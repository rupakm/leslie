import Leslie_LTS.Examples.BCA

/-! # Double BCA v2 — Pure Parallel Composition

    Same protocol as `DoubleBCA`, but structured as a pure nested
    `parallel` composition (no hand-written wrapper step function):

        doubleBCA = parallel innerSys outputCtrl output_sync

    where:
    - `innerSys` wraps `parallel bca₁ bca₂ sync_bca` with stutter
      observation labels (`readyToOutput`) that carry output-readiness
      data in the label
    - `outputCtrl` manages the `final` state
    - `output_sync` ties `readyToOutput i v` to `doOutput i v`

    This structure enables `parallel_forward_sim` to lift per-round
    BCA simulations automatically.
-/

open LTS

namespace DoubleBCA2

variable (T : Type) [DecidableEq T] (n f : Nat)

/-! ## Shared Types -/

inductive FinalVal (T : Type)
  | bot
  | valA (v : T)
  | valB (v : T)

/-! ## Inner System -/

def bca_sync : BCA_LTS.Label T n → BCA_LTS.Label (BCA_LTS.Val T) n → Prop
  | .corrupt i₁, .corrupt i₂ => i₁ = i₂
  | .output i₁ mv, .input i₂ v => i₁ = i₂ ∧ mv = v
  | _, _ => False

def par_bca :=
  parallel (BCA_LTS.bca T n f) (BCA_LTS.bca (BCA_LTS.Val T) n f) (bca_sync T n)

/-- Labels for the inner system: raw parallel labels + output observation. -/
inductive InnerLabel (T : Type) (n : Nat) where
  | par (cl : CompLabel (BCA_LTS.Label T n) (BCA_LTS.Label (BCA_LTS.Val T) n))
  | readyToOutput (i : Fin n) (v : FinalVal T)

/-- The inner system: raw parallel composition + stutter observations. -/
def innerSys : System
    (BCA_LTS.State T n × BCA_LTS.State (BCA_LTS.Val T) n)
    (InnerLabel T n) where
  init := (par_bca T n f).init
  step := fun s l s' =>
    match l with
    | .par cl => (par_bca T n f).step s cl s'
    | .readyToOutput i v =>
        BCA_LTS.isCorrect T n s.1 i ∧
        (match (s.2.local_ i).decided with
         | some (some (some w)) => v = FinalVal.valA w
         | some (some none)     => v = FinalVal.bot
         | some none            =>
             ∃ w : T, (s.2.local_ i).approved (some w) = true ∧ v = FinalVal.valB w
         | none => False) ∧
        s' = s

def innerLabelling [Inhabited T] [Inhabited (Fin n)] :
    Labelling (InnerLabel T n) where
  is_internal := fun l =>
    match l with
    | .readyToOutput _ _ => false
    | .par (.left (.input _ _)) => false
    | .par (.sync (.corrupt _) (.corrupt _)) => false
    | .par _ => true
  tau := .par (.left (.send default default .init default))
  tau_internal := rfl

/-! ## Output Controller -/

inductive OutputLabel (T : Type) (n : Nat) where
  | doOutput (i : Fin n) (v : FinalVal T)
  | idle

def outputCtrl : System (Fin n → Option (FinalVal T)) (OutputLabel T n) where
  init := fun s => ∀ p, s p = none
  step := fun s l s' =>
    match l with
    | .doOutput i v =>
        s i = none ∧
        s' = fun p => if p = i then some v else s p
    | .idle => s' = s

def outputLabelling [Inhabited T] [Inhabited (Fin n)] :
    Labelling (OutputLabel T n) where
  is_internal := fun l =>
    match l with
    | .doOutput _ _ => false
    | .idle => true
  tau := .idle
  tau_internal := rfl

/-! ## Composition -/

def output_sync : InnerLabel T n → OutputLabel T n → Prop
  | .readyToOutput i v, .doOutput i' v' => i = i' ∧ v = v'
  | _, _ => False

/-- The double BCA system: pure `parallel` composition. -/
def doubleBCA :=
  parallel (innerSys T n f) (outputCtrl T n) (output_sync T n)

/-! ## Labelling -/

def labelling [Inhabited T] [Inhabited (Fin n)] :
    Labelling (CompLabel (InnerLabel T n) (OutputLabel T n)) :=
  parallel_labelling (innerLabelling T n) (outputLabelling T n)

/-! ## State Accessors -/

/-- Access round 1 state. -/
abbrev r1 (s : (BCA_LTS.State T n × BCA_LTS.State (BCA_LTS.Val T) n) ×
    (Fin n → Option (FinalVal T))) : BCA_LTS.State T n := s.1.1

/-- Access round 2 state. -/
abbrev r2 (s : (BCA_LTS.State T n × BCA_LTS.State (BCA_LTS.Val T) n) ×
    (Fin n → Option (FinalVal T))) : BCA_LTS.State (BCA_LTS.Val T) n := s.1.2

/-- Access final output. -/
abbrev final (s : (BCA_LTS.State T n × BCA_LTS.State (BCA_LTS.Val T) n) ×
    (Fin n → Option (FinalVal T))) : Fin n → Option (FinalVal T) := s.2

/-! ## Properties -/

def feed_inv (s : (BCA_LTS.State T n × BCA_LTS.State (BCA_LTS.Val T) n) ×
    (Fin n → Option (FinalVal T))) : Prop :=
  ∀ q mv, (r2 T n s |>.local_ q).input = some mv →
    (r1 T n s |>.local_ q).decided = some mv

def output_consistent (s : (BCA_LTS.State T n × BCA_LTS.State (BCA_LTS.Val T) n) ×
    (Fin n → Option (FinalVal T))) : Prop :=
  ∀ p, match final T n s p with
    | none => True
    | some (FinalVal.valA w) => (r2 T n s |>.local_ p).decided = some (some (some w))
    | some FinalVal.bot => (r2 T n s |>.local_ p).decided = some (some none)
    | some (FinalVal.valB w) => (r2 T n s |>.local_ p).decided = some none ∧
        (r2 T n s |>.local_ p).approved (some w) = true

def double_validity (v : T)
    (s : (BCA_LTS.State T n × BCA_LTS.State (BCA_LTS.Val T) n) ×
      (Fin n → Option (FinalVal T))) : Prop :=
  (∀ p, ¬BCA_LTS.isCorrect T n (r1 T n s) p ∨
        (r1 T n s |>.local_ p).input = none ∨
        (r1 T n s |>.local_ p).input = some v) →
  ∀ p, BCA_LTS.isCorrect T n (r1 T n s) p →
    final T n s p = none ∨ final T n s p = some (FinalVal.valA v)

def graded_agreement
    (s : (BCA_LTS.State T n × BCA_LTS.State (BCA_LTS.Val T) n) ×
      (Fin n → Option (FinalVal T))) : Prop :=
  (∀ p q v w,
    BCA_LTS.isCorrect T n (r1 T n s) p → BCA_LTS.isCorrect T n (r1 T n s) q →
    (final T n s p = some (FinalVal.valA v) ∨ final T n s p = some (FinalVal.valB v)) →
    (final T n s q = some (FinalVal.valA w) ∨ final T n s q = some (FinalVal.valB w)) →
    v = w) ∧
  (∀ p q v,
    BCA_LTS.isCorrect T n (r1 T n s) p → BCA_LTS.isCorrect T n (r1 T n s) q →
    final T n s p = some (FinalVal.valA v) → final T n s q ≠ some FinalVal.bot) ∧
  (∀ p q v,
    BCA_LTS.isCorrect T n (r1 T n s) p → BCA_LTS.isCorrect T n (r1 T n s) q →
    final T n s p = some FinalVal.bot → final T n s q ≠ some (FinalVal.valA v))

def double_binding : Prop :=
  ∀ s, Reachable (doubleBCA T n f) s →
    (∃ p fv, BCA_LTS.isCorrect T n (r1 T n s) p ∧ final T n s p = some fv) →
    ∃ v : T, ∀ s', Star (doubleBCA T n f) s s' →
      ∀ q fv, BCA_LTS.isCorrect T n (r1 T n s') q → final T n s' q = some fv →
        fv = FinalVal.bot ∨ fv = FinalVal.valA v ∨ fv = FinalVal.valB v

end DoubleBCA2
