import Leslie_LTS.Examples.BCA

/-! # Double BCA — Sequential Composition via LTS Parallel Composition

    A protocol that runs BCA twice in sequence, built using the `parallel`
    composition from `Leslie.LTS.Composition`:

    1. Round 1: `bca T n f` — processes use their original input of type `T`
    2. Round 2: `bca (Val T) n f` — processes use round 1's decision as input

    **Synchronization**: the two BCA instances synchronize on two kinds of actions:
    - `corrupt i` — both sides corrupt the same process simultaneously,
      keeping their `corrupted` lists in lock-step
    - `output i mv` (round 1) with `input i mv` (round 2) — round 1's
      decision feeds directly as round 2's input

    A composite `output` transition is added on top of the parallel composition:
    - Round 2 decides `some (some v)` → final output `valA v`
    - Round 2 decides `some none`     → final output `bot`
    - Round 2 decides `none`          → final output `valB v` where
      `v` is a non-⊥ value approved by the process in round 2
-/

open LTS

namespace DoubleBCA_LTS

variable (T : Type) [DecidableEq T] (n f : Nat)

/-! ## Final Output Type -/

/-- The enriched output type for the double BCA. -/
inductive FinalVal (T : Type)
  | bot            -- ⊥
  | valA (v : T)   -- decided v (strong confidence)
  | valB (v : T)   -- decided v (weak confidence: round 2 saw conflict)

/-! ## Synchronization Predicate -/

/-- Two labels must synchronize when:
    1. Both are `corrupt i` for the same process `i`
    2. Round 1 `output i mv` pairs with round 2 `input i mv` -/
def sync_pred : BCA_LTS.Label T n → BCA_LTS.Label (BCA_LTS.Val T) n → Prop
  | .corrupt i₁, .corrupt i₂ => i₁ = i₂
  | .output i₁ mv, .input i₂ v => i₁ = i₂ ∧ mv = v
  | _, _ => False

/-! ## State -/

/-- State of the double BCA: the parallel product plus per-process
    composite output tracking. -/
structure State (T : Type) (n : Nat) where
  /-- Round 1 state. -/
  r1 : BCA_LTS.State T n
  /-- Round 2 state. -/
  r2 : BCA_LTS.State (BCA_LTS.Val T) n
  /-- Per-process composite output. -/
  final : Fin n → Option (FinalVal T)

/-! ## Labels -/

/-- Labels for the double BCA: parallel composition steps or
    the composite output. -/
inductive Label (T : Type) (n : Nat)
  /-- A step from the parallel composition. -/
  | par : CompLabel (BCA_LTS.Label T n) (BCA_LTS.Label (BCA_LTS.Val T) n) → Label T n
  /-- Composite output for process `i`. -/
  | output (i : Fin n) (v : FinalVal T) : Label T n

/-! ## The Composed System -/

/-- The underlying parallel composition. -/
def par_system :=
  parallel (BCA_LTS.bca T n f) (BCA_LTS.bca (BCA_LTS.Val T) n f) (sync_pred T n)

/-- The double BCA system. -/
def doubleBCA : System (State T n) (Label T n) where
  init := fun s =>
    (par_system T n f).init (s.r1, s.r2) ∧
    (∀ p, s.final p = none)
  step := fun s lbl s' =>
    match lbl with
    | .par cl =>
        (par_system T n f).step (s.r1, s.r2) cl (s'.r1, s'.r2) ∧
        s'.final = s.final
    | .output i v =>
        -- Process i is correct
        BCA_LTS.isCorrect T n s.r1 i ∧
        -- Hasn't done composite output yet
        s.final i = none ∧
        -- Round 2 has decided for process i
        (match (s.r2.local_ i).decided with
         | some (some (some w)) => v = .valA w
         | some (some none)     => v = .bot
         | some none            =>
             -- Round 2 saw conflict; pick a non-⊥ approved value from round 2
             ∃ w : T, (s.r2.local_ i).approved (some w) = true ∧ v = .valB w
         | none => False) ∧
        -- Only the final output changes
        s'.r1 = s.r1 ∧ s'.r2 = s.r2 ∧
        s'.final = fun p => if p = i then some v else s.final p

/-! ## Labelling -/

/-- Internal/external labelling for the double BCA.
    Only round 1 `input` and the final `output` are external;
    everything else is internal. -/
def labelling [Inhabited T] [Inhabited (Fin n)] :
    Labelling (Label T n) where
  is_internal := fun l =>
    match l with
    | .par (.left (.input _ _)) => false
    | .par (.sync (.corrupt _) (.corrupt _)) => false
    | .par _ => true
    | .output _ _ => false
  tau := .par (.left (.send default default .init default))
  tau_internal := rfl

/-! ## Properties -/

/-- Round 2 input for process q tracks round 1 decision. -/
def feed_inv (s : State T n) : Prop :=
  ∀ q mv, (s.r2.local_ q).input = some mv → (s.r1.local_ q).decided = some mv

/-- The final output is consistent with round 2's decision and round 2's
    approved values. -/
def output_consistent (s : State T n) : Prop :=
  ∀ p, match s.final p with
    | none => True
    | some (.valA w) => (s.r2.local_ p).decided = some (some (some w))
    | some .bot => (s.r2.local_ p).decided = some (some none)
    | some (.valB w) => (s.r2.local_ p).decided = some none ∧
        (s.r2.local_ p).approved (some w) = true

/-- Validity for the double BCA: if all correct processes have input `v`
    in round 1, then every correct process's final output is `none` or `valA v`. -/
def double_validity (v : T) (s : State T n) : Prop :=
  (∀ p, ¬BCA_LTS.isCorrect T n s.r1 p ∨
        (s.r1.local_ p).input = none ∨ (s.r1.local_ p).input = some v) →
  ∀ p, BCA_LTS.isCorrect T n s.r1 p →
    s.final p = none ∨ s.final p = some (.valA v)

/-- Graded agreement for the double BCA:
    1. If two correct processes output non-⊥ values, they agree on the
       underlying value.
    2. If a correct process outputs `valA v`, no correct process outputs `bot`
       (and conversely). -/
def graded_agreement (s : State T n) : Prop :=
  (∀ p q v w, BCA_LTS.isCorrect T n s.r1 p → BCA_LTS.isCorrect T n s.r1 q →
    (s.final p = some (.valA v) ∨ s.final p = some (.valB v)) →
    (s.final q = some (.valA w) ∨ s.final q = some (.valB w)) →
    v = w) ∧
  (∀ p q v, BCA_LTS.isCorrect T n s.r1 p → BCA_LTS.isCorrect T n s.r1 q →
    s.final p = some (.valA v) → s.final q ≠ some .bot) ∧
  (∀ p q v, BCA_LTS.isCorrect T n s.r1 p → BCA_LTS.isCorrect T n s.r1 q →
    s.final p = some .bot → s.final q ≠ some (.valA v))

/-- Binding for the double BCA: once a correct process outputs,
    there exists a value `v` such that in all continuations, every correct
    process's final output is `bot`, `valA v`, or `valB v`. -/
def double_binding : Prop :=
  ∀ s, Reachable (doubleBCA T n f) s →
    (∃ p fv, BCA_LTS.isCorrect T n s.r1 p ∧ s.final p = some fv) →
    ∃ v : T, ∀ s', Star (doubleBCA T n f) s s' →
      ∀ q fv, BCA_LTS.isCorrect T n s'.r1 q → s'.final q = some fv →
        fv = .bot ∨ fv = .valA v ∨ fv = .valB v


end DoubleBCA_LTS
