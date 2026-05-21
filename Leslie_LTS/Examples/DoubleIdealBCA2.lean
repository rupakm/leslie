import Leslie_LTS.Examples.IdealBCA

/-! # Double Ideal BCA v2 — Pure Parallel Composition

    Same protocol as `DoubleIdealBCA`, restructured as a pure nested
    `parallel` composition matching `DoubleBCA2`:

        doubleIdealBCA = parallel innerSys outputCtrl output_sync
-/

open LTS

namespace DoubleIdealBCA2

variable (T : Type) [DecidableEq T] (n f : Nat)

/-! ## Shared Types -/

inductive FinalVal (T : Type)
  | bot
  | valA (v : T)
  | valB (v : T)

/-! ## Inner System -/

def ideal_sync : IdealBCA.Label T n → IdealBCA.Label (IdealBCA.Val T) n → Prop
  | .corrupt i₁, .corrupt i₂ => i₁ = i₂
  | .output i₁ mv, .input i₂ v => i₁ = i₂ ∧ mv = v
  | _, _ => False

def par_ideal :=
  parallel (IdealBCA.ideal_bca T n f) (IdealBCA.ideal_bca (IdealBCA.Val T) n f)
    (ideal_sync T n)

/-- Labels for the inner system: raw parallel labels + output observation. -/
inductive InnerLabel (T : Type) (n : Nat) where
  | par (cl : CompLabel (IdealBCA.Label T n) (IdealBCA.Label (IdealBCA.Val T) n))
  | readyToOutput (i : Fin n) (v : FinalVal T)

/-- The inner system: raw parallel composition + stutter observations. -/
def innerSys : System
    (IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n)
    (InnerLabel T n) where
  init := (par_ideal T n f).init
  step := fun s l s' =>
    match l with
    | .par cl => (par_ideal T n f).step s cl s'
    | .readyToOutput i v =>
        IdealBCA.isCorrect T n s.1 i ∧
        (match s.2.decided i with
         | some (some (some w)) => v = FinalVal.valA w
         | some (some none)     => v = FinalVal.bot
         | some none            =>
             ∃ w, s.1.bound_value = some w ∧ v = FinalVal.valB w
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
  tau := .par (.left (.bind default))
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

/-- The double ideal BCA system: pure `parallel` composition. -/
def doubleIdealBCA :=
  parallel (innerSys T n f) (outputCtrl T n) (output_sync T n)

/-! ## Labelling -/

def labelling [Inhabited T] [Inhabited (Fin n)] :
    Labelling (CompLabel (InnerLabel T n) (OutputLabel T n)) :=
  parallel_labelling (innerLabelling T n) (outputLabelling T n)

/-! ## State Accessors -/

abbrev r1 (s : (IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n) ×
    (Fin n → Option (FinalVal T))) : IdealBCA.State T n := s.1.1

abbrev r2 (s : (IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n) ×
    (Fin n → Option (FinalVal T))) : IdealBCA.State (IdealBCA.Val T) n := s.1.2

abbrev final (s : (IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n) ×
    (Fin n → Option (FinalVal T))) : Fin n → Option (FinalVal T) := s.2

/-! ## Invariants -/

def feed_inv (s : (IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n) ×
    (Fin n → Option (FinalVal T))) : Prop :=
  ∀ q mv, (r2 T n s).input_ q = some mv → (r1 T n s).decided q = some mv

def output_consistent (s : (IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n) ×
    (Fin n → Option (FinalVal T))) : Prop :=
  ∀ p, match final T n s p with
    | none => True
    | some (FinalVal.valA w) => (r2 T n s).decided p = some (some (some w))
    | some FinalVal.bot => (r2 T n s).decided p = some (some none)
    | some (FinalVal.valB w) => (r2 T n s).decided p = some none ∧
        (r1 T n s).bound_value = some w

def binding_inv (s : (IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n) ×
    (Fin n → Option (FinalVal T))) : Prop :=
  output_consistent T n s ∧
  IdealBCA.inv T n f (r1 T n s) ∧
  IdealBCA.inv (IdealBCA.Val T) n f (r2 T n s) ∧
  feed_inv T n s

/-! ## Protocol Properties -/

def double_validity (v : T)
    (s : (IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n) ×
      (Fin n → Option (FinalVal T))) : Prop :=
  (∀ p, ¬IdealBCA.isCorrect T n (r1 T n s) p ∨
        (r1 T n s).input_ p = none ∨
        (r1 T n s).input_ p = some v) →
  ∀ p, IdealBCA.isCorrect T n (r1 T n s) p →
    final T n s p = none ∨ final T n s p = some (FinalVal.valA v)

def graded_agreement
    (s : (IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n) ×
      (Fin n → Option (FinalVal T))) : Prop :=
  (∀ p q v w,
    IdealBCA.isCorrect T n (r1 T n s) p → IdealBCA.isCorrect T n (r1 T n s) q →
    (final T n s p = some (FinalVal.valA v) ∨ final T n s p = some (FinalVal.valB v)) →
    (final T n s q = some (FinalVal.valA w) ∨ final T n s q = some (FinalVal.valB w)) →
    v = w) ∧
  (∀ p q v,
    IdealBCA.isCorrect T n (r1 T n s) p → IdealBCA.isCorrect T n (r1 T n s) q →
    final T n s p = some (FinalVal.valA v) → final T n s q ≠ some FinalVal.bot) ∧
  (∀ p q v,
    IdealBCA.isCorrect T n (r1 T n s) p → IdealBCA.isCorrect T n (r1 T n s) q →
    final T n s p = some FinalVal.bot → final T n s q ≠ some (FinalVal.valA v))

def double_binding : Prop :=
  ∀ s, Reachable (doubleIdealBCA T n f) s →
    (∃ p fv, IdealBCA.isCorrect T n (r1 T n s) p ∧ final T n s p = some fv) →
    ∃ v : T, ∀ s', Star (doubleIdealBCA T n f) s s' →
      ∀ q fv, IdealBCA.isCorrect T n (r1 T n s') q → final T n s' q = some fv →
        fv = FinalVal.bot ∨ fv = FinalVal.valA v ∨ fv = FinalVal.valB v

/-! ## Invariant Preservation -/

theorem binding_inv_init :
    ∀ s, (doubleIdealBCA T n f).init s → binding_inv T n f s := by
  intro s hinit
  have hinner := hinit.1
  have hout := hinit.2
  simp only [doubleIdealBCA, innerSys, par_ideal, parallel] at hinit
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p; simp [hout p]
  · exact IdealBCA.inv_init T n f s.1.1 hinner.1
  · exact IdealBCA.inv_init _ n f s.1.2 hinner.2
  · intro q mv hinp
    have h := hinner.2
    simp only [IdealBCA.ideal_bca, Order.add_one_le_iff, ne_eq, ge_iff_le] at h
    rw [h.2.1 q] at hinp; simp at hinp

private theorem par_inner_feed_inv_step :
    ∀ (s : IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n)
      (cl : CompLabel (IdealBCA.Label T n) (IdealBCA.Label (IdealBCA.Val T) n))
      (s' : IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n),
    feed_inv T n (s, default) → (par_ideal T n f).step s cl s' →
    feed_inv T n (s', default) := by
  intro s cl s' hf hstep
  simp only [par_ideal, parallel] at hstep
  intro q mv hinp
  match cl with
  | .left la =>
    obtain ⟨hnosync, hs₁, heq2⟩ := hstep
    have h2eq : s'.2.input_ q = s.2.input_ q := by rw [heq2]
    match la with
    | .input _ _ =>
      obtain ⟨_, heq1⟩ := hs₁
      have h1eq : s'.1.decided q = s.1.decided q := by simp [heq1]
      rw [h1eq]; exact hf q mv (h2eq ▸ hinp)
    | .bind _ =>
      obtain ⟨_, _, heq1⟩ := hs₁
      have h1eq : s'.1.decided q = s.1.decided q := by simp [heq1]
      rw [h1eq]; exact hf q mv (h2eq ▸ hinp)
    | .corrupt _ => exfalso; exact hnosync (.corrupt _) rfl
    | .output _ _ => exfalso; exact hnosync (.input _ _) ⟨rfl, rfl⟩
  | .right lb =>
    obtain ⟨hnosync, hs₂, heq1⟩ := hstep
    have h1eq : s'.1.decided q = s.1.decided q := by rw [heq1]
    rw [h1eq]
    match lb with
    | .output _ _ =>
      obtain ⟨_, _, _, heq2⟩ := hs₂
      have h2eq : s'.2.input_ q = s.2.input_ q := by simp [heq2]
      exact hf q mv (h2eq ▸ hinp)
    | .bind _ =>
      obtain ⟨_, _, heq2⟩ := hs₂
      have h2eq : s'.2.input_ q = s.2.input_ q := by simp [heq2]
      exact hf q mv (h2eq ▸ hinp)
    | .input _ _ => exfalso; exact hnosync (.output _ _) ⟨rfl, rfl⟩
    | .corrupt _ => exfalso; exact hnosync (.corrupt _) rfl
  | .sync la lb =>
    obtain ⟨hsync, hs₁, hs₂⟩ := hstep
    match la, lb with
    | .corrupt _, .corrupt _ =>
      obtain ⟨_, _, heq1⟩ := hs₁
      obtain ⟨_, _, heq2⟩ := hs₂
      have h1eq : s'.1.decided q = s.1.decided q := by simp [heq1]
      have h2eq : s'.2.input_ q = s.2.input_ q := by simp [heq2]
      rw [h1eq]; exact hf q mv (h2eq ▸ hinp)
    | .output i₁ mv', .input _ _ =>
      obtain ⟨rfl, rfl⟩ := hsync
      obtain ⟨_, _, _, heq1⟩ := hs₁
      obtain ⟨_, heq2⟩ := hs₂
      have h1 : s'.1.decided q = (if q = i₁ then some mv' else s.1.decided q) := by simp [heq1]
      have h2 : s'.2.input_ q = (if q = i₁ then some mv' else s.2.input_ q) := by simp [heq2]
      by_cases hq : q = i₁
      · rw [if_pos hq] at h1 h2; rw [h1]; exact h2 ▸ hinp
      · rw [if_neg hq] at h1 h2; rw [h1]; exact hf q mv (h2 ▸ hinp)
    | .corrupt _, .input .. | .corrupt _, .output ..
    | .corrupt _, .bind ..
    | .input .., _ | .bind .., _
    | .output _ _, .corrupt .. | .output _ _, .output ..
    | .output _ _, .bind .. => simp [ideal_sync] at hsync

private theorem par_inner_oc_step :
    ∀ (s : IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n)
      (cl : CompLabel (IdealBCA.Label T n) (IdealBCA.Label (IdealBCA.Val T) n))
      (s' : IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n)
      (out : Fin n → Option (FinalVal T)),
    output_consistent T n (s, out) → (par_ideal T n f).step s cl s' →
    output_consistent T n (s', out) := by
  intro s cl s' out hoc hstep p
  simp only [par_ideal, parallel] at hstep
  -- final T n (s', out) p = out p = final T n (s, out) p
  change match out p with
    | none => True
    | some (.valA w) => s'.2.decided p = some (some (some w))
    | some .bot => s'.2.decided p = some (some none)
    | some (.valB w) => s'.2.decided p = some none ∧ s'.1.bound_value = some w
  have hold : match out p with
    | none => True
    | some (.valA w) => s.2.decided p = some (some (some w))
    | some .bot => s.2.decided p = some (some none)
    | some (.valB w) => s.2.decided p = some none ∧ s.1.bound_value = some w := hoc p
  match hfp : out p with
  | none => trivial
  | some (.valA w) =>
    simp only [hfp] at hold
    match cl with
    | .left la =>
      obtain ⟨_, _, heq2⟩ := hstep; simp only [heq2]; exact hold
    | .right lb =>
      obtain ⟨hnosync, hs₂, _⟩ := hstep
      match lb with
      | .output i _ =>
        obtain ⟨_, hdec_none, _, heq2⟩ := hs₂
        by_cases hp : p = i
        · subst hp; rw [hdec_none] at hold; simp at hold
        · simp only [heq2, hp, ↓reduceIte]; exact hold
      | .bind _ =>
        obtain ⟨_, _, heq2⟩ := hs₂; simp only [heq2]; exact hold
      | .input _ _ => exfalso; exact hnosync (.output _ _) ⟨rfl, rfl⟩
      | .corrupt _ => exfalso; exact hnosync (.corrupt _) rfl
    | .sync la lb =>
      obtain ⟨hsync, _, hs₂⟩ := hstep
      match la, lb with
      | .corrupt _, .corrupt _ =>
        obtain ⟨_, _, heq2⟩ := hs₂; simp only [heq2]; exact hold
      | .output _ _, .input _ _ =>
        obtain ⟨_, heq2⟩ := hs₂; simp only [heq2]; exact hold
      | .corrupt _, .input .. | .corrupt _, .output ..
      | .corrupt _, .bind ..
      | .input .., _ | .bind .., _
      | .output _ _, .corrupt .. | .output _ _, .output ..
      | .output _ _, .bind .. => simp [ideal_sync] at hsync
  | some .bot =>
    simp only [hfp] at hold
    match cl with
    | .left la =>
      obtain ⟨_, _, heq2⟩ := hstep; simp only [heq2]; exact hold
    | .right lb =>
      obtain ⟨hnosync, hs₂, _⟩ := hstep
      match lb with
      | .output i _ =>
        obtain ⟨_, hdec_none, _, heq2⟩ := hs₂
        by_cases hp : p = i
        · subst hp; rw [hdec_none] at hold; simp at hold
        · simp only [heq2, hp, ↓reduceIte]; exact hold
      | .bind _ =>
        obtain ⟨_, _, heq2⟩ := hs₂; simp only [heq2]; exact hold
      | .input _ _ => exfalso; exact hnosync (.output _ _) ⟨rfl, rfl⟩
      | .corrupt _ => exfalso; exact hnosync (.corrupt _) rfl
    | .sync la lb =>
      obtain ⟨hsync, _, hs₂⟩ := hstep
      match la, lb with
      | .corrupt _, .corrupt _ =>
        obtain ⟨_, _, heq2⟩ := hs₂; simp only [heq2]; exact hold
      | .output _ _, .input _ _ =>
        obtain ⟨_, heq2⟩ := hs₂; simp only [heq2]; exact hold
      | .corrupt _, .input .. | .corrupt _, .output ..
      | .corrupt _, .bind ..
      | .input .., _ | .bind .., _
      | .output _ _, .corrupt .. | .output _ _, .output ..
      | .output _ _, .bind .. => simp [ideal_sync] at hsync
  | some (.valB w) =>
    simp only [hfp] at hold
    match cl with
    | .left la =>
      obtain ⟨hnosync, hs₁, heq2⟩ := hstep
      match la with
      | .input _ _ =>
        obtain ⟨_, heq1⟩ := hs₁
        exact ⟨by simp only [heq2]; exact hold.1, by simp only [heq1]; exact hold.2⟩
      | .bind _ =>
        obtain ⟨hbv_none, _, _⟩ := hs₁
        rw [hbv_none] at hold; simp at hold
      | .corrupt _ => exfalso; exact hnosync (.corrupt _) rfl
      | .output _ _ => exfalso; exact hnosync (.input _ _) ⟨rfl, rfl⟩
    | .right lb =>
      obtain ⟨hnosync, hs₂, heq1⟩ := hstep
      match lb with
      | .output i _ =>
        obtain ⟨_, hdec_none, _, heq2⟩ := hs₂
        by_cases hp : p = i
        · subst hp; rw [hdec_none] at hold; simp at hold
        · exact ⟨by simp only [heq2, hp]; exact hold.1, by simp only [heq1]; exact hold.2⟩
      | .bind _ =>
        obtain ⟨_, _, heq2⟩ := hs₂
        exact ⟨by simp only [heq2]; exact hold.1, by simp only [heq1]; exact hold.2⟩
      | .input _ _ => exfalso; exact hnosync (.output _ _) ⟨rfl, rfl⟩
      | .corrupt _ => exfalso; exact hnosync (.corrupt _) rfl
    | .sync la lb =>
      obtain ⟨hsync, hs₁, hs₂⟩ := hstep
      match la, lb with
      | .corrupt _, .corrupt _ =>
        obtain ⟨_, _, heq1⟩ := hs₁
        obtain ⟨_, _, heq2⟩ := hs₂
        exact ⟨by simp only [heq2]; exact hold.1, by simp only [heq1]; exact hold.2⟩
      | .output _ _, .input _ _ =>
        obtain ⟨_, _, _, heq1⟩ := hs₁
        obtain ⟨_, heq2⟩ := hs₂
        exact ⟨by simp only [heq2]; exact hold.1, by simp only [heq1]; exact hold.2⟩
      | .corrupt _, .input .. | .corrupt _, .output ..
      | .corrupt _, .bind ..
      | .input .., _ | .bind .., _
      | .output _ _, .corrupt .. | .output _ _, .output ..
      | .output _ _, .bind .. => simp [ideal_sync] at hsync

theorem binding_inv_step :
    ∀ s l s', binding_inv T n f s → (doubleIdealBCA T n f).step s l s' →
    binding_inv T n f s' := by
  intro s l s' ⟨hoc, h1, h2, hf⟩ hstep
  simp only [doubleIdealBCA, parallel] at hstep
  match l with
  | .left il =>
    obtain ⟨hnosync, hinner, heq_out⟩ := hstep
    match il with
    | .readyToOutput _ _ =>
      simp only [innerSys] at hinner
      have : s' = s := Prod.ext (hinner.2.2) heq_out
      rw [this]; exact ⟨hoc, h1, h2, hf⟩
    | .par cl =>
      simp only [innerSys] at hinner
      have hpar := hinner
      simp only [par_ideal, parallel] at hpar
      have hout_eq : s'.2 = s.2 := heq_out
      have hs'eq : s' = (s'.1, s.2) := Prod.ext rfl hout_eq
      constructor
      · rw [hs'eq]; exact par_inner_oc_step T n f s.1 cl s'.1 s.2 hoc hinner
      constructor
      · change IdealBCA.inv T n f s'.1.1
        match cl with
        | .left la =>
          obtain ⟨_, hs₁, _⟩ := hpar
          exact IdealBCA.inv_step T n f _ la _ h1 hs₁
        | .right _ =>
          obtain ⟨_, _, heq⟩ := hpar; rw [heq]; exact h1
        | .sync la _ =>
          obtain ⟨_, hs₁, _⟩ := hpar
          exact IdealBCA.inv_step T n f _ la _ h1 hs₁
      constructor
      · change IdealBCA.inv (IdealBCA.Val T) n f s'.1.2
        match cl with
        | .left _ =>
          obtain ⟨_, _, heq⟩ := hpar; rw [heq]; exact h2
        | .right lb =>
          obtain ⟨_, hs₂, _⟩ := hpar
          exact IdealBCA.inv_step _ n f _ lb _ h2 hs₂
        | .sync _ lb =>
          obtain ⟨_, _, hs₂⟩ := hpar
          exact IdealBCA.inv_step _ n f _ lb _ h2 hs₂
      · rw [hs'eq]; exact par_inner_feed_inv_step T n f s.1 cl s'.1 (by exact hf) hinner
  | .right ol =>
    obtain ⟨hnosync, hout, heq_inner⟩ := hstep
    match ol with
    | .idle =>
      simp only [outputCtrl] at hout
      have : s' = s := Prod.ext heq_inner hout
      rw [this]; exact ⟨hoc, h1, h2, hf⟩
    | .doOutput i v =>
      exfalso; exact hnosync (.readyToOutput i v) ⟨rfl, rfl⟩
  | .sync il ol =>
    obtain ⟨hsync, hinner, hout⟩ := hstep
    match il, ol, hsync with
    | .readyToOutput i v, .doOutput i' v', ⟨hi, hv⟩ =>
      subst hi; subst hv
      simp only [innerSys] at hinner
      have hieq : s'.1 = s.1 := hinner.2.2
      simp only [outputCtrl] at hout
      obtain ⟨hnone, heq_out⟩ := hout
      constructor
      · -- output_consistent
        show output_consistent T n s'
        intro p
        change match s'.2 p with
          | none => True
          | some (.valA w) => s'.1.2.decided p = some (some (some w))
          | some .bot => s'.1.2.decided p = some (some none)
          | some (.valB w) => s'.1.2.decided p = some none ∧ s'.1.1.bound_value = some w
        rw [hieq]
        by_cases hp : p = i
        · subst hp
          simp only [heq_out, ↓reduceIte]
          have hguard := hinner.2.1
          match hd : (s.1.2).decided p with
          | some (some (some w)) =>
            simp only [hd] at hguard; rw [hguard]
          | some (some none) =>
            simp only [hd] at hguard; rw [hguard]
          | some none =>
            simp only [hd] at hguard
            obtain ⟨w, hbv, hfv⟩ := hguard
            rw [hfv]; exact ⟨rfl, hbv⟩
          | none => simp only [hd] at hguard
        · simp only [heq_out, hp]; exact hoc p
      · exact ⟨by change IdealBCA.inv T n f s'.1.1; rw [hieq]; exact h1,
               by change IdealBCA.inv _ n f s'.1.2; rw [hieq]; exact h2,
               by show feed_inv T n s'; rw [show s' = (s.1, s'.2) from Prod.ext hieq rfl]; exact hf⟩

theorem binding_inv_reachable :
    ∀ s, Reachable (doubleIdealBCA T n f) s → binding_inv T n f s := by
  intro s hreach
  induction hreach with
  | init h => exact binding_inv_init T n f _ h
  | step _ hs ih => exact binding_inv_step T n f _ _ _ ih hs

/-! ## Property Proofs -/

private theorem valA_implies_r1_bound (s : (IdealBCA.State T n ×
    IdealBCA.State (IdealBCA.Val T) n) × (Fin n → Option (FinalVal T)))
    (hcons : output_consistent T n s)
    (hinv1 : IdealBCA.inv T n f s.1.1)
    (hinv2 : IdealBCA.inv (IdealBCA.Val T) n f s.1.2)
    (hfeed : feed_inv T n s)
    (p : Fin n) (v : T) (hfp : s.2 p = some (.valA v)) :
    s.1.1.bound_value = some v := by
  have hoc : s.1.2.decided p = some (some (some v)) := by
    have := hcons p; simp only [hfp] at this; exact this
  have hbv2 := hinv2.1 p (some v) hoc
  have hsup := hinv2.2.2.1 (some v) hbv2
  have hpos : IdealBCA.inputSupport (IdealBCA.Val T) n s.1.2 (some v) > 0 := by
    have := hinv2.2.2.2.1; omega
  simp only [IdealBCA.inputSupport] at hpos
  obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos hpos
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hr
  exact hinv1.1 r v (hfeed r (some v) hr.2.2)

private theorem output_implies_r1_bound_set (s : (IdealBCA.State T n ×
    IdealBCA.State (IdealBCA.Val T) n) × (Fin n → Option (FinalVal T)))
    (hcons : output_consistent T n s)
    (hinv1 : IdealBCA.inv T n f s.1.1)
    (hinv2 : IdealBCA.inv (IdealBCA.Val T) n f s.1.2)
    (hfeed : feed_inv T n s)
    (p : Fin n) (fv : FinalVal T) (hfp : s.2 p = some fv) :
    ∃ w, s.1.1.bound_value = some w := by
  match fv with
  | .valA v => exact ⟨v, valA_implies_r1_bound T n f s hcons hinv1 hinv2 hfeed p v hfp⟩
  | .valB w =>
    have hoc := hcons p; simp only [hfp] at hoc; exact ⟨w, hoc.2⟩
  | .bot =>
    have hoc : s.1.2.decided p = some (some none) := by
      have := hcons p; simp only [hfp] at this; exact this
    have hbv2 := hinv2.1 p none hoc
    have hsup := hinv2.2.2.1 none hbv2
    have hpos : IdealBCA.inputSupport (IdealBCA.Val T) n s.1.2 none > 0 := by
      have := hinv2.2.2.2.1; omega
    simp only [IdealBCA.inputSupport] at hpos
    obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos hpos
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hdec := hfeed r none hr.2.2
    have hbv_ne : s.1.1.bound_value ≠ none := by
      intro hbv; have := hinv1.2.2.2.2 hbv r; rw [this] at hdec; simp at hdec
    exact Option.ne_none_iff_exists'.mp hbv_ne

private theorem r1_bound_value_mono :
    ∀ s l s', (doubleIdealBCA T n f).step s l s' →
    ∀ w, s.1.1.bound_value = some w → s'.1.1.bound_value = some w := by
  intro s l s' hstep w hbv
  simp only [doubleIdealBCA, parallel] at hstep
  match l with
  | .left il =>
    obtain ⟨_, hinner, _⟩ := hstep
    match il with
    | .readyToOutput _ _ =>
      simp only [innerSys] at hinner; rw [hinner.2.2]; exact hbv
    | .par cl =>
      simp only [innerSys, par_ideal, parallel] at hinner
      match cl with
      | .left la =>
        obtain ⟨_, hs₁, _⟩ := hinner
        match la with
        | .input _ _ => obtain ⟨_, heq1⟩ := hs₁; simp only [heq1]; exact hbv
        | .bind _ =>
          obtain ⟨hbv_none, _, _⟩ := hs₁; rw [hbv] at hbv_none; simp at hbv_none
        | .output _ _ =>
          obtain ⟨_, _, _, heq1⟩ := hs₁; simp only [heq1]; exact hbv
        | .corrupt _ =>
          obtain ⟨_, _, heq1⟩ := hs₁; simp only [heq1]; exact hbv
      | .right _ =>
        obtain ⟨_, _, heq1⟩ := hinner; rw [heq1]; exact hbv
      | .sync la _ =>
        obtain ⟨hsync, hs₁, _⟩ := hinner
        match la with
        | .corrupt _ => obtain ⟨_, _, heq1⟩ := hs₁; simp only [heq1]; exact hbv
        | .output _ _ => obtain ⟨_, _, _, heq1⟩ := hs₁; simp only [heq1]; exact hbv
        | .input _ _ | .bind _ => simp [ideal_sync] at hsync
  | .right ol =>
    obtain ⟨_, _, heq_inner⟩ := hstep; rw [heq_inner]; exact hbv
  | .sync il ol =>
    obtain ⟨hsync, hinner, _⟩ := hstep
    match il, ol, hsync with
    | .readyToOutput _ _, .doOutput _ _, ⟨_, _⟩ =>
      simp only [innerSys] at hinner; rw [hinner.2.2]; exact hbv

private theorem r1_bound_star :
    ∀ s s', Star (doubleIdealBCA T n f) s s' →
    ∀ w, s.1.1.bound_value = some w → s'.1.1.bound_value = some w := by
  intro s s' hstar w hbv
  induction hstar with
  | refl => exact hbv
  | step hs _ ih => exact ih (r1_bound_value_mono T n f _ _ _ hs w hbv)

theorem double_binding_holds : double_binding T n f := by
  intro s hreach ⟨p, fv, hcorr, hfp⟩
  have hinv_s := binding_inv_reachable T n f s hreach
  obtain ⟨hcons_s, hinv1_s, hinv2_s, hfeed_s⟩ := hinv_s
  obtain ⟨v, hbv⟩ := output_implies_r1_bound_set T n f s hcons_s hinv1_s hinv2_s hfeed_s p fv hfp
  exact ⟨v, fun s' hstar q fv' hcq hfq => by
    have hinv' := Star.preserve_inv (binding_inv_step T n f) hstar
      ⟨hcons_s, hinv1_s, hinv2_s, hfeed_s⟩
    obtain ⟨hcons', hinv1', hinv2', hfeed'⟩ := hinv'
    have hbv' := r1_bound_star T n f s s' hstar v hbv
    match fv' with
    | .bot => left; rfl
    | .valA w =>
      right; left; congr 1
      have h := valA_implies_r1_bound T n f s' hcons' hinv1' hinv2' hfeed' q w hfq
      rw [hbv'] at h; exact (Option.some.inj h).symm
    | .valB w =>
      right; right; congr 1
      have hoc := hcons' q; simp only [hfq] at hoc
      rw [hbv'] at hoc; exact (Option.some.inj hoc.2).symm⟩

theorem double_validity_from_inv (v : T) (s) (hcons : output_consistent T n s)
    (hinv1 : IdealBCA.inv T n f s.1.1) (hinv2 : IdealBCA.inv (IdealBCA.Val T) n f s.1.2)
    (hfeed : feed_inv T n s) : double_validity T n v s := by
  intro hpre p hcorr
  have hval1 := IdealBCA.inv_implies_validity T n f v s.1.1 hinv1
  have hval2 := IdealBCA.inv_implies_validity (IdealBCA.Val T) n f (some v) s.1.2 hinv2
  have hr2_pre : ∀ q, ¬IdealBCA.isCorrect (IdealBCA.Val T) n s.1.2 q ∨
      s.1.2.input_ q = none ∨ s.1.2.input_ q = some (some v) := by
    intro q
    match hinq : s.1.2.input_ q with
    | none => right; left; rfl
    | some mv =>
      have hdec := hfeed q mv hinq
      rcases hval1 hpre q with h | h
      · rw [h] at hdec; simp at hdec
      · right; right; rw [← hdec]; exact h
  rcases hval2 hr2_pre p with h | h
  · have hoc := hcons p
    match hfp : s.2 p with
    | none => left; exact hfp
    | some (.valA w) => simp only [hfp] at hoc; rw [h] at hoc; simp at hoc
    | some .bot => simp only [hfp] at hoc; rw [h] at hoc; simp at hoc
    | some (.valB w) => simp only [hfp] at hoc; rw [h] at hoc; simp at hoc
  · have hoc := hcons p
    match hfp : s.2 p with
    | none => left; exact hfp
    | some (.valA w) =>
      simp only [hfp] at hoc; rw [h] at hoc; simp only [Option.some.injEq] at hoc
      right; rw [← hoc] at hfp; exact hfp
    | some .bot => simp only [hfp] at hoc; rw [h] at hoc; simp at hoc
    | some (.valB w) => simp only [hfp] at hoc; rw [h] at hoc; simp at hoc

theorem double_validity_holds (v : T) :
    ∀ s, Reachable (doubleIdealBCA T n f) s → double_validity T n v s := by
  intro s hreach
  obtain ⟨hcons, hinv1, hinv2, hfeed⟩ := binding_inv_reachable T n f s hreach
  exact double_validity_from_inv T n f v s hcons hinv1 hinv2 hfeed

theorem graded_agreement_from_inv (s) (hcons : output_consistent T n s)
    (hinv1 : IdealBCA.inv T n f s.1.1) (hinv2 : IdealBCA.inv (IdealBCA.Val T) n f s.1.2)
    (hfeed : feed_inv T n s) : graded_agreement T n s := by
  have valA_dec : ∀ p v, s.2 p = some (.valA v) →
      s.1.2.decided p = some (some (some v)) := by
    intro p v hfp; have hoc := hcons p; simp only [hfp] at hoc; exact hoc
  have bot_dec : ∀ p, s.2 p = some .bot →
      s.1.2.decided p = some (some none) := by
    intro p hfp; have hoc := hcons p; simp only [hfp] at hoc; exact hoc
  have valB_dec : ∀ p w, s.2 p = some (.valB w) →
      s.1.2.decided p = some none ∧ s.1.1.bound_value = some w := by
    intro p w hfp; have hoc := hcons p; simp only [hfp] at hoc; exact hoc
  have valA_bound : ∀ p v, s.2 p = some (.valA v) →
      s.1.2.bound_value = some (some v) := by
    intro p v hfp; exact hinv2.1 p (some v) (valA_dec p v hfp)
  have bot_bound : ∀ p, s.2 p = some .bot →
      s.1.2.bound_value = some none := by
    intro p hfp; exact hinv2.1 p none (bot_dec p hfp)
  have valA_valB_agree : ∀ p q v w,
      s.2 p = some (.valA v) → s.2 q = some (.valB w) → v = w := by
    intro p q v w hfp hfq
    have hbv2 := valA_bound p v hfp
    have hsup := hinv2.2.2.1 (some v) hbv2
    have hcorr_le := hinv2.2.2.2.1
    have hpos : IdealBCA.inputSupport (IdealBCA.Val T) n s.1.2 (some v) > 0 := by omega
    simp only [IdealBCA.inputSupport] at hpos
    obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos hpos
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hbv1 := hinv1.1 r v (hfeed r (some v) hr.2.2)
    have hbv1' := (valB_dec q w hfq).2
    rw [hbv1] at hbv1'; exact Option.some.inj hbv1'
  refine ⟨?_, ?_, ?_⟩
  · intro p q v w _ _ hfpv hfqw
    rcases hfpv with hfp | hfp <;> rcases hfqw with hfq | hfq
    · have hbv := valA_bound p v hfp; have hbw := valA_bound q w hfq
      rw [hbv] at hbw; simp only [Option.some.injEq] at hbw; exact hbw
    · exact valA_valB_agree p q v w hfp hfq
    · exact (valA_valB_agree q p w v hfq hfp).symm
    · have h1 := (valB_dec p v hfp).2; have h2 := (valB_dec q w hfq).2
      rw [h1] at h2; simp only [Option.some.injEq] at h2; exact h2
  · intro p q v _ _ hfp hfq
    have hbv := valA_bound p v hfp; have hbot := bot_bound q hfq
    rw [hbv] at hbot; simp at hbot
  · intro p q v _ _ hfp hfq
    have hbot := bot_bound p hfp; have hbv := valA_bound q v hfq
    rw [hbot] at hbv; simp at hbv

theorem graded_agreement_holds :
    ∀ s, Reachable (doubleIdealBCA T n f) s → graded_agreement T n s := by
  intro s hreach
  obtain ⟨hcons, hinv1, hinv2, hfeed⟩ := binding_inv_reachable T n f s hreach
  exact graded_agreement_from_inv T n f s hcons hinv1 hinv2 hfeed

end DoubleIdealBCA2
