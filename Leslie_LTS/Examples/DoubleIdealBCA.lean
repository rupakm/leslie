import Leslie_LTS.Examples.IdealBCA

/-! # Double Ideal BCA — LTS Formulation

    Two ideal BCA instances composed via `parallel`:
    1. Round 1: `ideal_bca T n f`
    2. Round 2: `ideal_bca (Val T) n f`

    Synchronized on `corrupt` and `output/input` (same pattern as `DoubleBCA`).
    Round 2 inputs come exclusively from round 1 outputs.

    A composite `output` transition is added on top of the parallel composition:
    - Round 2 decides `some (some v)` → final output `valA v`
    - Round 2 decides `some none`     → final output `bot`
    - Round 2 decides `none`          → final output `valB v` where
      `v` comes from round 1's `bound_value`
-/

open LTS

namespace DoubleIdealBCA

variable (T : Type) [DecidableEq T] (n f : Nat)

/-! ## Final Output Type -/

/-- The enriched output type for the double BCA. -/
inductive FinalVal (T : Type)
  | bot            -- ⊥
  | valA (v : T)   -- decided v (strong confidence)
  | valB (v : T)   -- decided v (weak confidence: round 2 saw conflict)

/-! ## Synchronization Predicate -/

/-- Two ideal BCA labels synchronize when:
    1. Both are `corrupt i` for the same process
    2. Round 1 `output i mv` pairs with round 2 `input i mv` -/
def sync_pred :
    IdealBCA.Label T n → IdealBCA.Label (IdealBCA.Val T) n → Prop
  | .corrupt i₁, .corrupt i₂ => i₁ = i₂
  | .output i₁ mv, .input i₂ v => i₁ = i₂ ∧ mv = v
  | _, _ => False

/-! ## State -/

/-- State of the double ideal BCA: the parallel product plus per-process
    composite output tracking. -/
structure State (T : Type) (n : Nat) where
  /-- Round 1 state. -/
  r1 : IdealBCA.State T n
  /-- Round 2 state. -/
  r2 : IdealBCA.State (IdealBCA.Val T) n
  /-- Per-process composite output. -/
  final : Fin n → Option (FinalVal T)

/-! ## Labels -/

/-- Labels for the double ideal BCA: parallel composition steps or
    the composite output. -/
inductive Label (T : Type) (n : Nat)
  /-- A step from the parallel composition. -/
  | par : CompLabel (IdealBCA.Label T n) (IdealBCA.Label (IdealBCA.Val T) n) → Label T n
  /-- Composite output for process `i`. -/
  | output (i : Fin n) (v : FinalVal T) : Label T n

/-! ## The Composed System -/

/-- The underlying parallel composition. -/
def par_system :=
  parallel (IdealBCA.ideal_bca T n f) (IdealBCA.ideal_bca (IdealBCA.Val T) n f)
    (sync_pred T n)

/-- The double ideal BCA system. -/
def doubleIdealBCA : System (State T n) (Label T n) where
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
        IdealBCA.isCorrect T n s.r1 i ∧
        -- Hasn't done composite output yet
        s.final i = none ∧
        -- Round 2 has decided for process i
        (match s.r2.decided i with
         | some (some (some w)) => v = .valA w
         | some (some none)     => v = .bot
         | some none            =>
             -- Round 2 saw conflict; take v from round 1's bound_value
             ∃ w, s.r1.bound_value = some w ∧ v = .valB w
         | none => False) ∧
        -- Only the final output changes
        s'.r1 = s.r1 ∧ s'.r2 = s.r2 ∧
        s'.final = fun p => if p = i then some v else s.final p

/-! ## Labelling -/

/-- Internal/external labelling for the double ideal BCA.
    Only round 1 `input` and the final `output` are external;
    everything else (bind, corrupt, send/recv between rounds, round 2
    input/output, sync) is internal. -/
def labelling [Inhabited T] [Inhabited (Fin n)] :
    Labelling (Label T n) where
  is_internal := fun l =>
    match l with
    | .par (.left (.input _ _)) => false
    | .par (.sync (.corrupt _) (.corrupt _)) => false
    | .par _ => true
    | .output _ _ => false
  tau := .par (.left (.bind default))
  tau_internal := rfl

/-! ## Invariant Lifting -/

/-- Lift a round 1 inductive invariant to the double ideal BCA. -/
theorem lift_r1_invariant (P : IdealBCA.State T n → Prop)
    (hinit : ∀ s, (IdealBCA.ideal_bca T n f).init s → P s)
    (hstep : ∀ s l s', P s → (IdealBCA.ideal_bca T n f).step s l s' → P s') :
    (doubleIdealBCA T n f).satisfies [ltl| □ ⌜ fun s => P s.r1 ⌝] := by
  apply System.state_invariant
  · intro s ⟨hpar, _⟩
    exact hinit s.r1 hpar.1
  · intro s l s' hP hstep_d
    match l with
    | .par cl =>
      have ⟨hpar_step, _⟩ := hstep_d
      -- The parallel step moves r1 according to sys₁
      simp only [par_system, parallel] at hpar_step
      match cl with
      | .left l₁ =>
        have ⟨_, hs₁, _⟩ := hpar_step
        exact hstep _ l₁ _ hP hs₁
      | .right _ =>
        have ⟨_, _, heq⟩ := hpar_step
        rw [heq]; exact hP
      | .sync l₁ _ =>
        have ⟨_, hs₁, _⟩ := hpar_step
        exact hstep _ l₁ _ hP hs₁
    | .output _ _ =>
      have ⟨_, _, _, heq, _, _⟩ := hstep_d
      rw [heq]; exact hP

/-- Lift a round 2 inductive invariant to the double ideal BCA. -/
theorem lift_r2_invariant (P : IdealBCA.State (IdealBCA.Val T) n → Prop)
    (hinit : ∀ s, (IdealBCA.ideal_bca (IdealBCA.Val T) n f).init s → P s)
    (hstep : ∀ s l s', P s →
      (IdealBCA.ideal_bca (IdealBCA.Val T) n f).step s l s' → P s') :
    (doubleIdealBCA T n f).satisfies [ltl| □ ⌜ fun s => P s.r2 ⌝] := by
  apply System.state_invariant
  · intro s ⟨hpar, _⟩
    exact hinit s.r2 hpar.2
  · intro s l s' hP hstep_d
    match l with
    | .par cl =>
      have ⟨hpar_step, _⟩ := hstep_d
      simp only [par_system, parallel] at hpar_step
      match cl with
      | .left _ =>
        have ⟨_, _, heq⟩ := hpar_step
        rw [heq]; exact hP
      | .right l₂ =>
        have ⟨_, hs₂, _⟩ := hpar_step
        exact hstep _ l₂ _ hP hs₂
      | .sync _ l₂ =>
        have ⟨_, _, hs₂⟩ := hpar_step
        exact hstep _ l₂ _ hP hs₂
    | .output _ _ =>
      have ⟨_, _, _, _, heq, _⟩ := hstep_d
      rw [heq]; exact hP

/-! ## Lifted Properties -/

/-- Round 1's strengthened invariant holds in the double system. -/
theorem r1_inv :
    (doubleIdealBCA T n f).satisfies [ltl| □ ⌜ fun s => IdealBCA.inv T n f s.r1 ⌝] :=
  lift_r1_invariant T n f _ (IdealBCA.inv_init T n f) (IdealBCA.inv_step T n f)

/-- Round 2's strengthened invariant holds in the double system. -/
theorem r2_inv :
    (doubleIdealBCA T n f).satisfies
      [ltl| □ ⌜ fun s => IdealBCA.inv (IdealBCA.Val T) n f s.r2 ⌝] :=
  lift_r2_invariant T n f _ (IdealBCA.inv_init _ n f) (IdealBCA.inv_step _ n f)

/-- Round 1 agreement lifts to the double system. -/
theorem r1_agreement :
    (doubleIdealBCA T n f).satisfies
      [ltl| □ ⌜ fun s => IdealBCA.agreement T n s.r1 ⌝] := by
  intro e hv k
  have hinv := r1_inv T n f e hv k
  intro p q v w hcp hcq hpv hqw
  have hv' := hinv.1 p v hpv
  have hw := hinv.1 q w hqw
  rw [hv'] at hw; exact Option.some.inj hw

/-- Round 2 agreement lifts to the double system. -/
theorem r2_agreement :
    (doubleIdealBCA T n f).satisfies
      [ltl| □ ⌜ fun s => IdealBCA.agreement (IdealBCA.Val T) n s.r2 ⌝] := by
  intro e hv k
  have hinv := r2_inv T n f e hv k
  intro p q v w hcp hcq hpv hqw
  have hv' := hinv.1 p v hpv
  have hw := hinv.1 q w hqw
  rw [hv'] at hw; exact Option.some.inj hw

/-- Round 1 validity lifts to the double system. -/
theorem r1_validity (v : T) :
    (doubleIdealBCA T n f).satisfies
      [ltl| □ ⌜ fun s => IdealBCA.validity T n v s.r1 ⌝] := by
  intro e hv k
  exact IdealBCA.inv_implies_validity T n f v _ (r1_inv T n f e hv k)

/-- Round 2 validity lifts to the double system. -/
theorem r2_validity (v : IdealBCA.Val T) :
    (doubleIdealBCA T n f).satisfies
      [ltl| □ ⌜ fun s => IdealBCA.validity (IdealBCA.Val T) n v s.r2 ⌝] := by
  intro e hv k
  exact IdealBCA.inv_implies_validity _ n f v _ (r2_inv T n f e hv k)

/-! ## Feed Invariant -/

/-- Round 2 input for process q tracks round 1 decision. -/
def feed_inv (s : State T n) : Prop :=
  ∀ q mv, s.r2.input_ q = some mv → s.r1.decided q = some mv

private theorem feed_inv_step :
    ∀ (s : State T n) l (s' : State T n),
    feed_inv T n s → (doubleIdealBCA T n f).step s l s' → feed_inv T n s' := by
  intro s l s' hP hstep q mv hinp
  match l with
  | .par cl =>
    have ⟨hpar_step, _⟩ := hstep
    simp only [par_system, parallel] at hpar_step
    match cl with
    | .left (.corrupt _) =>
      exfalso; exact hpar_step.1 (.corrupt _) rfl
    | .left (.output _ _) =>
      exfalso; exact hpar_step.1 (.input _ _) ⟨rfl, rfl⟩
    | .left (.input _ _) =>
      obtain ⟨_, hs₁, heq2⟩ := hpar_step
      obtain ⟨_, heq1⟩ := hs₁
      have h2 : s'.r2.input_ q = s.r2.input_ q := by simp only [heq2]
      have h1 : s'.r1.decided q = s.r1.decided q := by simp only [heq1]
      rw [h1]; exact hP q mv (h2 ▸ hinp)
    | .left (.bind _) =>
      obtain ⟨_, hs₁, heq2⟩ := hpar_step
      obtain ⟨_, _, heq1⟩ := hs₁
      have h2 : s'.r2.input_ q = s.r2.input_ q := by simp only [heq2]
      have h1 : s'.r1.decided q = s.r1.decided q := by simp only [heq1]
      rw [h1]; exact hP q mv (h2 ▸ hinp)
    | .right (.input _ _) =>
      exfalso; exact hpar_step.1 (.output _ _) ⟨rfl, rfl⟩
    | .right (.corrupt _) =>
      exfalso; exact hpar_step.1 (.corrupt _) rfl
    | .right (.output _ _) =>
      obtain ⟨_, hs₂, heq1⟩ := hpar_step
      obtain ⟨_, _, _, heq2⟩ := hs₂
      have h2 : s'.r2.input_ q = s.r2.input_ q := by simp only [heq2]
      have h1 : s'.r1.decided q = s.r1.decided q := by simp only [heq1]
      rw [h1]; exact hP q mv (h2 ▸ hinp)
    | .right (.bind _) =>
      obtain ⟨_, hs₂, heq1⟩ := hpar_step
      obtain ⟨_, _, heq2⟩ := hs₂
      have h2 : s'.r2.input_ q = s.r2.input_ q := by simp only [heq2]
      have h1 : s'.r1.decided q = s.r1.decided q := by simp only [heq1]
      rw [h1]; exact hP q mv (h2 ▸ hinp)
    | .sync (.corrupt _) (.corrupt _) =>
      obtain ⟨_, hs₁, hs₂⟩ := hpar_step
      obtain ⟨_, _, heq1⟩ := hs₁
      obtain ⟨_, _, heq2⟩ := hs₂
      have h2 : s'.r2.input_ q = s.r2.input_ q := by simp only [heq2]
      have h1 : s'.r1.decided q = s.r1.decided q := by simp only [heq1]
      rw [h1]; exact hP q mv (h2 ▸ hinp)
    | .sync (.output i₁ mv') (.input _ _) =>
      obtain ⟨⟨rfl, rfl⟩, hs₁, hs₂⟩ := hpar_step
      obtain ⟨_, _, _, heq1⟩ := hs₁
      obtain ⟨_, heq2⟩ := hs₂
      have h2 : s'.r2.input_ q =
          (if q = i₁ then some mv' else s.r2.input_ q) := by simp only [heq2]
      have h1 : s'.r1.decided q =
          (if q = i₁ then some mv' else s.r1.decided q) := by simp only [heq1]
      by_cases hq : q = i₁
      · rw [if_pos hq] at h1 h2; rw [h1]; exact h2 ▸ hinp
      · rw [if_neg hq] at h1 h2; rw [h1]; exact hP q mv (h2 ▸ hinp)
    -- Impossible sync combinations
    | .sync (.corrupt _) (.input ..) | .sync (.corrupt _) (.output ..)
    | .sync (.corrupt _) (.bind ..)
    | .sync (.input ..) _ | .sync (.bind ..) _
    | .sync (.output _ _) (.corrupt ..) | .sync (.output _ _) (.output ..)
    | .sync (.output _ _) (.bind ..) =>
      simp [sync_pred] at hpar_step
  | .output _ _ =>
    have ⟨_, _, _, heq1, heq2, _⟩ := hstep
    have h2 : s'.r2.input_ q = s.r2.input_ q := by rw [heq2]
    have h1 : s'.r1.decided q = s.r1.decided q := by rw [heq1]
    rw [h1]; exact hP q mv (h2 ▸ hinp)

theorem feed_inv_invariant :
    (doubleIdealBCA T n f).satisfies [ltl| □ ⌜ feed_inv T n ⌝] := by
  apply System.state_invariant
  · intro s ⟨hpar, _⟩ q mv hinp
    simp only [par_system, parallel, IdealBCA.ideal_bca] at hpar
    rw [hpar.2.2.1 q] at hinp; simp at hinp
  · exact feed_inv_step T n f

/-! ## Composite Validity -/

/-- Validity for the double ideal BCA: if all correct processes have input `v`
    in round 1, then every correct process's final output is `none` or `valA v`. -/
def double_validity (v : T) (s : State T n) : Prop :=
  (∀ p, ¬IdealBCA.isCorrect T n s.r1 p ∨
        s.r1.input_ p = none ∨ s.r1.input_ p = some v) →
  ∀ p, IdealBCA.isCorrect T n s.r1 p →
    s.final p = none ∨ s.final p = some (.valA v)

/-- The final output is consistent with round 2's decision and round 1's bound. -/
def output_consistent (s : State T n) : Prop :=
  ∀ p, match s.final p with
    | none => True
    | some (.valA w) => s.r2.decided p = some (some (some w))
    | some .bot => s.r2.decided p = some (some none)
    | some (.valB w) => s.r2.decided p = some none ∧ s.r1.bound_value = some w

private theorem output_consistent_step :
    ∀ (s : State T n) l (s' : State T n),
    output_consistent T n s → (doubleIdealBCA T n f).step s l s' →
    output_consistent T n s' := by
  intro s l s' hP hstep p
  match l with
  | .par cl =>
    have ⟨hpar_step, hfeq⟩ := hstep
    simp only [par_system, parallel] at hpar_step
    have hfinal_eq : s'.final p = s.final p := by rw [hfeq]
    have hold := hP p
    rw [hfinal_eq]
    match hfp : s.final p with
    | none => trivial
    | some (.valA w) =>
      simp only [hfp] at hold ⊢
      -- Need: s'.r2.decided p = s.r2.decided p (decided monotone)
      match cl with
      | .left (.corrupt _) => exfalso; exact hpar_step.1 (.corrupt _) rfl
      | .left (.output _ _) => exfalso; exact hpar_step.1 (.input _ _) ⟨rfl, rfl⟩
      | .left (.input _ _) =>
        obtain ⟨_, _, heq2⟩ := hpar_step; rw [heq2]; exact hold
      | .left (.bind _) =>
        obtain ⟨_, _, heq2⟩ := hpar_step; rw [heq2]; exact hold
      | .right (.input _ _) => exfalso; exact hpar_step.1 (.output _ _) ⟨rfl, rfl⟩
      | .right (.corrupt _) => exfalso; exact hpar_step.1 (.corrupt _) rfl
      | .right (.output i _) =>
        obtain ⟨_, hs₂, _⟩ := hpar_step
        obtain ⟨_, hdec_none, _, heq2⟩ := hs₂
        by_cases hp : p = i
        · subst hp; rw [hdec_none] at hold; simp at hold
        · simp only [heq2, hp]; exact hold
      | .right (.bind _) =>
        obtain ⟨_, hs₂, _⟩ := hpar_step
        obtain ⟨_, _, heq2⟩ := hs₂; simp only [heq2]; exact hold
      | .sync (.corrupt _) (.corrupt _) =>
        obtain ⟨_, _, hs₂⟩ := hpar_step
        obtain ⟨_, _, heq2⟩ := hs₂; simp only [heq2]; exact hold
      | .sync (.output _ _) (.input _ _) =>
        obtain ⟨_, _, hs₂⟩ := hpar_step
        obtain ⟨_, heq2⟩ := hs₂; simp only [heq2]; exact hold
      | .sync (.corrupt _) (.input ..) | .sync (.corrupt _) (.output ..)
      | .sync (.corrupt _) (.bind ..)
      | .sync (.input ..) _ | .sync (.bind ..) _
      | .sync (.output _ _) (.corrupt ..) | .sync (.output _ _) (.output ..)
      | .sync (.output _ _) (.bind ..) => simp [sync_pred] at hpar_step
    | some .bot =>
      simp only [hfp] at hold ⊢
      match cl with
      | .left (.corrupt _) => exfalso; exact hpar_step.1 (.corrupt _) rfl
      | .left (.output _ _) => exfalso; exact hpar_step.1 (.input _ _) ⟨rfl, rfl⟩
      | .left (.input _ _) =>
        obtain ⟨_, _, heq2⟩ := hpar_step; rw [heq2]; exact hold
      | .left (.bind _) =>
        obtain ⟨_, _, heq2⟩ := hpar_step; rw [heq2]; exact hold
      | .right (.input _ _) => exfalso; exact hpar_step.1 (.output _ _) ⟨rfl, rfl⟩
      | .right (.corrupt _) => exfalso; exact hpar_step.1 (.corrupt _) rfl
      | .right (.output i _) =>
        obtain ⟨_, hs₂, _⟩ := hpar_step
        obtain ⟨_, hdec_none, _, heq2⟩ := hs₂
        by_cases hp : p = i
        · subst hp; rw [hdec_none] at hold; simp at hold
        · simp only [heq2, hp]; exact hold
      | .right (.bind _) =>
        obtain ⟨_, hs₂, _⟩ := hpar_step
        obtain ⟨_, _, heq2⟩ := hs₂; simp only [heq2]; exact hold
      | .sync (.corrupt _) (.corrupt _) =>
        obtain ⟨_, _, hs₂⟩ := hpar_step
        obtain ⟨_, _, heq2⟩ := hs₂; simp only [heq2]; exact hold
      | .sync (.output _ _) (.input _ _) =>
        obtain ⟨_, _, hs₂⟩ := hpar_step
        obtain ⟨_, heq2⟩ := hs₂; simp only [heq2]; exact hold
      | .sync (.corrupt _) (.input ..) | .sync (.corrupt _) (.output ..)
      | .sync (.corrupt _) (.bind ..)
      | .sync (.input ..) _ | .sync (.bind ..) _
      | .sync (.output _ _) (.corrupt ..) | .sync (.output _ _) (.output ..)
      | .sync (.output _ _) (.bind ..) => simp only [sync_pred, false_and] at hpar_step
    | some (.valB w) =>
      simp only [hfp] at hold ⊢
      match cl with
      | .left (.corrupt _) => exfalso; exact hpar_step.1 (.corrupt _) rfl
      | .left (.output _ _) => exfalso; exact hpar_step.1 (.input _ _) ⟨rfl, rfl⟩
      | .left (.input _ _) =>
        obtain ⟨_, hs₁, heq2⟩ := hpar_step
        obtain ⟨_, heq1⟩ := hs₁
        exact ⟨by rw [heq2]; exact hold.1, by simp only [heq1]; exact hold.2⟩
      | .left (.bind _) =>
        obtain ⟨_, hs₁, heq2⟩ := hpar_step
        obtain ⟨hbv_none, _, _⟩ := hs₁
        rw [hbv_none] at hold; simp at hold
      | .right (.input _ _) => exfalso; exact hpar_step.1 (.output _ _) ⟨rfl, rfl⟩
      | .right (.corrupt _) => exfalso; exact hpar_step.1 (.corrupt _) rfl
      | .right (.output i _) =>
        obtain ⟨_, hs₂, heq1⟩ := hpar_step
        obtain ⟨_, hdec_none, _, heq2⟩ := hs₂
        by_cases hp : p = i
        · subst hp; rw [hdec_none] at hold; simp at hold
        · exact ⟨by simp only [heq2, hp]; exact hold.1, by rw [heq1]; exact hold.2⟩
      | .right (.bind _) =>
        obtain ⟨_, hs₂, heq1⟩ := hpar_step
        obtain ⟨_, _, heq2⟩ := hs₂
        exact ⟨by simp only [heq2]; exact hold.1, by rw [heq1]; exact hold.2⟩
      | .sync (.corrupt _) (.corrupt _) =>
        obtain ⟨_, hs₁, hs₂⟩ := hpar_step
        obtain ⟨_, _, heq1⟩ := hs₁
        obtain ⟨_, _, heq2⟩ := hs₂
        exact ⟨by simp only [heq2]; exact hold.1, by simp only [heq1]; exact hold.2⟩
      | .sync (.output _ _) (.input _ _) =>
        obtain ⟨_, hs₁, hs₂⟩ := hpar_step
        obtain ⟨_, _, _, heq1⟩ := hs₁
        obtain ⟨_, heq2⟩ := hs₂
        exact ⟨by simp only [heq2]; exact hold.1, by simp only [heq1]; exact hold.2⟩
      | .sync (.corrupt _) (.input ..) | .sync (.corrupt _) (.output ..)
      | .sync (.corrupt _) (.bind ..)
      | .sync (.input ..) _ | .sync (.bind ..) _
      | .sync (.output _ _) (.corrupt ..) | .sync (.output _ _) (.output ..)
      | .sync (.output _ _) (.bind ..) => simp [sync_pred] at hpar_step
  | .output i v' =>
    have ⟨_, _, hguard, heq1, heq2, hfeq⟩ := hstep
    by_cases hp : p = i
    · subst hp
      have hfinal : s'.final p = some v' := by simp [hfeq]
      rw [hfinal, heq2, heq1]
      match hd : s.r2.decided p with
      | some (some (some w)) =>
        simp only [hd] at hguard; subst hguard; simp
      | some (some none) =>
        simp only [hd] at hguard; subst hguard; simp
      | some none =>
        obtain ⟨w, hbv, hfv⟩ := by simpa [hd] using hguard
        subst hfv; exact ⟨rfl, hbv⟩
      | none => simp only [hd] at hguard
    · have hfinal : s'.final p = s.final p := by simp [hfeq, hp]
      rw [hfinal, heq2, heq1]
      exact hP p

theorem output_consistent_invariant :
    (doubleIdealBCA T n f).satisfies [ltl| □ ⌜ output_consistent T n ⌝] := by
  apply System.state_invariant
  · intro s ⟨_, hfin⟩ p; simp only [hfin p]
  · exact output_consistent_step T n f

/-- Composite validity is an invariant of the double ideal BCA. -/
theorem double_validity_invariant (v : T) :
    (doubleIdealBCA T n f).satisfies [ltl| □ ⌜ double_validity T n v ⌝] := by
  intro e hv k
  have hfeed := feed_inv_invariant T n f e hv k
  have hval1 := r1_validity T n f v e hv k
  have hval2 := r2_validity T n f (some v) e hv k
  have hcons := output_consistent_invariant T n f e hv k
  -- Normalize 0+k to k in all hypotheses
  simp only [Nat.zero_add, state_prop] at hfeed hval1 hval2 hcons ⊢
  intro hpre p hcorr
  -- Derive round 2's validity precondition
  have hr2_pre : ∀ q, ¬IdealBCA.isCorrect (IdealBCA.Val T) n (e.states k).r2 q ∨
      (e.states k).r2.input_ q = none ∨
      (e.states k).r2.input_ q = some (some v) := by
    intro q
    match hinq : (e.states k).r2.input_ q with
    | none => right; left; rfl
    | some mv =>
      have hdec := hfeed q mv hinq
      rcases hval1 hpre q with h | h
      · rw [h] at hdec; simp at hdec
      · right; right; rw [← hdec]; exact h
  -- Round 2 validity with value (some v)
  rcases hval2 hr2_pre p with h | h
  · -- r2.decided p = none
    have hoc := hcons p
    match hfp : (e.states k).final p with
    | none => left; rfl
    | some (.valA w) => simp only [hfp] at hoc; rw [h] at hoc; simp at hoc
    | some .bot => simp only [hfp] at hoc; rw [h] at hoc; simp at hoc
    | some (.valB w) => simp only [hfp] at hoc; rw [h] at hoc; simp at hoc
  · -- r2.decided p = some (some (some v))
    have hoc := hcons p
    match hfp : (e.states k).final p with
    | none => left; rfl
    | some (.valA w) =>
      right
      simp only [hfp] at hoc; rw [h] at hoc; simp at hoc
      congr 1; congr 1; exact hoc.symm
    | some .bot => simp only [hfp] at hoc; rw [h] at hoc; simp at hoc
    | some (.valB w) => simp only [hfp] at hoc; rw [h] at hoc; simp at hoc

/-! ## Graded Agreement -/

/-- Graded agreement for the double ideal BCA:
    1. If two correct processes output non-⊥ values, they agree on the underlying value.
    2. If a correct process outputs `valA v`, no correct process outputs `bot`
       (and conversely). -/
def graded_agreement (s : State T n) : Prop :=
  -- Part 1: value agreement
  (∀ p q v w, IdealBCA.isCorrect T n s.r1 p → IdealBCA.isCorrect T n s.r1 q →
    (s.final p = some (.valA v) ∨ s.final p = some (.valB v)) →
    (s.final q = some (.valA w) ∨ s.final q = some (.valB w)) →
    v = w) ∧
  -- Part 2: grade compatibility (valA and bot are incompatible)
  (∀ p q v, IdealBCA.isCorrect T n s.r1 p → IdealBCA.isCorrect T n s.r1 q →
    s.final p = some (.valA v) → s.final q ≠ some .bot) ∧
  (∀ p q v, IdealBCA.isCorrect T n s.r1 p → IdealBCA.isCorrect T n s.r1 q →
    s.final p = some .bot → s.final q ≠ some (.valA v))

/-- Graded agreement is an invariant of the double ideal BCA. -/
theorem graded_agreement_invariant :
    (doubleIdealBCA T n f).satisfies [ltl| □ ⌜ graded_agreement T n ⌝] := by
  intro e hv k
  have hinv1 := r1_inv T n f e hv k
  have hinv2 := r2_inv T n f e hv k
  have hcons := output_consistent_invariant T n f e hv k
  have hfeed := feed_inv_invariant T n f e hv k
  simp only [Nat.zero_add, state_prop] at hinv1 hinv2 hcons hfeed ⊢
  change graded_agreement T n (e.states k)
  unfold graded_agreement
  -- Helper: valA v implies r2.decided p = some (some (some v))
  have valA_dec : ∀ p v, (e.states k).final p = some (.valA v) →
      (e.states k).r2.decided p = some (some (some v)) := by
    intro p v hfp; have hoc := hcons p; simp only [hfp] at hoc; exact hoc
  -- Helper: bot implies r2.decided p = some (some none)
  have bot_dec : ∀ p, (e.states k).final p = some .bot →
      (e.states k).r2.decided p = some (some none) := by
    intro p hfp; have hoc := hcons p; simp only [hfp] at hoc; exact hoc
  -- Helper: valB w implies r2.decided p = some none ∧ r1.bound_value = some w
  have valB_dec : ∀ p w, (e.states k).final p = some (.valB w) →
      (e.states k).r2.decided p = some none ∧ (e.states k).r1.bound_value = some w := by
    intro p w hfp; have hoc := hcons p; simp only [hfp] at hoc; exact hoc
  -- Helper: valA v implies r2.bound_value = some (some v)
  have valA_bound : ∀ p v, (e.states k).final p = some (.valA v) →
      (e.states k).r2.bound_value = some (some v) := by
    intro p v hfp; exact hinv2.1 p (some v) (valA_dec p v hfp)
  -- Helper: bot implies r2.bound_value = some none
  have bot_bound : ∀ p, (e.states k).final p = some .bot →
      (e.states k).r2.bound_value = some none := by
    intro p hfp; exact hinv2.1 p none (bot_dec p hfp)
  -- Helper: valA v and valB w implies v = w
  have valA_valB_agree : ∀ p q v w,
      (e.states k).final p = some (.valA v) →
      (e.states k).final q = some (.valB w) → v = w := by
    intro p q v w hfp hfq
    have hbv2 := valA_bound p v hfp
    have hsup := hinv2.2.2.1 (some v) hbv2
    have hcorr_le := hinv2.2.2.2.1
    have hpos : IdealBCA.inputSupport (IdealBCA.Val T) n (e.states k).r2 (some v) > 0 := by
      omega
    simp only [IdealBCA.inputSupport] at hpos
    obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos hpos
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hr
    obtain ⟨_, _, hrinp⟩ := hr
    have hdec := hfeed r (some v) hrinp
    have hbv1 := hinv1.1 r v hdec
    have hbv1' := (valB_dec q w hfq).2
    rw [hbv1] at hbv1'; exact Option.some.inj hbv1'
  refine ⟨?_, ?_, ?_⟩
  -- Part 1: value agreement
  · intro p q v w _ _ hfpv hfqw
    rcases hfpv with hfp | hfp <;> rcases hfqw with hfq | hfq
    · -- valA v, valA w: r2 bound_value uniqueness
      have hbv := valA_bound p v hfp
      have hbw := valA_bound q w hfq
      rw [hbv] at hbw; simp only [Option.some.injEq] at hbw; exact hbw
    · -- valA v, valB w
      exact valA_valB_agree p q v w hfp hfq
    · -- valB v, valA w: symmetric
      exact (valA_valB_agree q p w v hfq hfp).symm
    · -- valB v, valB w: both give r1.bound_value
      have h1 := (valB_dec p v hfp).2
      have h2 := (valB_dec q w hfq).2
      rw [h1] at h2; simp only [Option.some.injEq] at h2; exact h2
  -- Part 2a: valA v → no bot
  · intro p q v _ _ hfp hfq
    have hbv := valA_bound p v hfp
    have hbot := bot_bound q hfq
    rw [hbv] at hbot; simp at hbot
  -- Part 2b: bot → no valA
  · intro p q v _ _ hfp hfq
    have hbot := bot_bound p hfp
    have hbv := valA_bound q v hfq
    rw [hbot] at hbv; simp at hbv

/-! ## Binding -/

/-- Binding for the double ideal BCA: once a correct process outputs,
    there exists a value `v` such that in all continuations, every correct
    process's final output is `bot`, `valA v`, or `valB v`. -/
def double_binding : Prop :=
  ∀ s, Reachable (doubleIdealBCA T n f) s →
    (∃ p fv, IdealBCA.isCorrect T n s.r1 p ∧ s.final p = some fv) →
    ∃ v : T, ∀ s', Star (doubleIdealBCA T n f) s s' →
      ∀ q fv, IdealBCA.isCorrect T n s'.r1 q → s'.final q = some fv →
        fv = .bot ∨ fv = .valA v ∨ fv = .valB v

/-- Once set, a process's final output never changes. -/
private theorem final_monotone :
    ∀ (s : State T n) l (s' : State T n),
    (doubleIdealBCA T n f).step s l s' →
    ∀ p fv, s.final p = some fv → s'.final p = some fv := by
  intro s l s' hstep p fv hfp
  match l with
  | .par _ => exact hstep.2 ▸ hfp
  | .output i _ =>
    have ⟨_, _, _, _, _, hfeq⟩ := hstep
    by_cases hp : p = i
    · subst hp
      have := hstep.2.1; rw [hfp] at this; simp at this
    · simp only [hfeq, hp]; exact hfp

/-- final_monotone across Star. -/
private theorem final_star_monotone :
    ∀ (s s' : State T n), Star (doubleIdealBCA T n f) s s' →
    ∀ p fv, s.final p = some fv → s'.final p = some fv := by
  intro s s' hstar p fv hfp
  induction hstar with
  | refl => exact hfp
  | step hs _ ih => exact ih (final_monotone T n f _ _ _ hs p fv hfp)

/-- Step-level preservation of r1 invariant. -/
private theorem r1_inv_step :
    ∀ (s : State T n) l (s' : State T n),
    IdealBCA.inv T n f s.r1 → (doubleIdealBCA T n f).step s l s' →
    IdealBCA.inv T n f s'.r1 := by
  intro s l s' hP hstep
  match l with
  | .par cl =>
    have ⟨hpar_step, _⟩ := hstep
    simp only [par_system, parallel] at hpar_step
    match cl with
    | .left l₁ =>
      obtain ⟨_, hs₁, _⟩ := hpar_step
      exact IdealBCA.inv_step T n f _ l₁ _ hP hs₁
    | .right _ =>
      obtain ⟨_, _, heq⟩ := hpar_step; rw [heq]; exact hP
    | .sync l₁ _ =>
      obtain ⟨_, hs₁, _⟩ := hpar_step
      exact IdealBCA.inv_step T n f _ l₁ _ hP hs₁
  | .output _ _ =>
    have ⟨_, _, _, heq, _, _⟩ := hstep; rw [heq]; exact hP

/-- Step-level preservation of r2 invariant. -/
private theorem r2_inv_step :
    ∀ (s : State T n) l (s' : State T n),
    IdealBCA.inv (IdealBCA.Val T) n f s.r2 → (doubleIdealBCA T n f).step s l s' →
    IdealBCA.inv (IdealBCA.Val T) n f s'.r2 := by
  intro s l s' hP hstep
  match l with
  | .par cl =>
    have ⟨hpar_step, _⟩ := hstep
    simp only [par_system, parallel] at hpar_step
    match cl with
    | .left _ =>
      obtain ⟨_, _, heq⟩ := hpar_step; rw [heq]; exact hP
    | .right l₂ =>
      obtain ⟨_, hs₂, _⟩ := hpar_step
      exact IdealBCA.inv_step _ n f _ l₂ _ hP hs₂
    | .sync _ l₂ =>
      obtain ⟨_, _, hs₂⟩ := hpar_step
      exact IdealBCA.inv_step _ n f _ l₂ _ hP hs₂
  | .output _ _ =>
    have ⟨_, _, _, _, heq, _⟩ := hstep; rw [heq]; exact hP

/-- The combined invariant needed for binding. -/
def binding_inv (s : State T n) : Prop :=
  output_consistent T n s ∧
  IdealBCA.inv T n f s.r1 ∧
  IdealBCA.inv (IdealBCA.Val T) n f s.r2 ∧
  feed_inv T n s

theorem binding_inv_init :
    ∀ s, (doubleIdealBCA T n f).init s → binding_inv T n f s := by
  intro s hinit
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p; simp only [hinit.2 p]
  · exact IdealBCA.inv_init T n f s.r1 hinit.1.1
  · exact IdealBCA.inv_init _ n f s.r2 hinit.1.2
  · intro q mv hinp
    have h := hinit.1
    simp only [par_system, parallel, IdealBCA.ideal_bca] at h
    rw [h.2.2.1 q] at hinp; simp at hinp

theorem binding_inv_step :
    ∀ (s : State T n) l (s' : State T n),
    binding_inv T n f s → (doubleIdealBCA T n f).step s l s' →
    binding_inv T n f s' := by
  intro s l s' ⟨hoc, h1, h2, hf⟩ hstep
  exact ⟨output_consistent_step T n f s l s' hoc hstep,
         r1_inv_step T n f s l s' h1 hstep,
         r2_inv_step T n f s l s' h2 hstep,
         feed_inv_step T n f s l s' hf hstep⟩

/-- Helper: from output_consistent + invariants, valA v implies r1.bound_value = some v. -/
private theorem valA_implies_r1_bound (s : State T n)
    (hcons : output_consistent T n s)
    (hinv1 : IdealBCA.inv T n f s.r1)
    (hinv2 : IdealBCA.inv (IdealBCA.Val T) n f s.r2)
    (hfeed : feed_inv T n s)
    (p : Fin n) (v : T) (hfp : s.final p = some (.valA v)) :
    s.r1.bound_value = some v := by
  have hoc := hcons p; simp only [hfp] at hoc
  -- r2.decided p = some (some (some v)), so r2.bound_value = some (some v)
  have hbv2 := hinv2.1 p (some v) hoc
  -- inputSupport(some v) ≥ 1 in r2
  have hsup := hinv2.2.2.1 (some v) hbv2
  have hpos : IdealBCA.inputSupport (IdealBCA.Val T) n s.r2 (some v) > 0 := by
    have := hinv2.2.2.2.1; omega
  simp only [IdealBCA.inputSupport] at hpos
  obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos hpos
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hr
  exact hinv1.1 r v (hfeed r (some v) hr.2.2)

/-- Helper: if a correct process has output anything, r1.bound_value is set. -/
private theorem output_implies_r1_bound_set (s : State T n)
    (hcons : output_consistent T n s)
    (hinv1 : IdealBCA.inv T n f s.r1)
    (hinv2 : IdealBCA.inv (IdealBCA.Val T) n f s.r2)
    (hfeed : feed_inv T n s)
    (p : Fin n) (fv : FinalVal T) (hfp : s.final p = some fv) :
    ∃ w, s.r1.bound_value = some w := by
  match fv with
  | .valA v => exact ⟨v, valA_implies_r1_bound T n f s hcons hinv1 hinv2 hfeed p v hfp⟩
  | .valB w =>
    have hoc := hcons p; simp only [hfp] at hoc
    exact ⟨w, hoc.2⟩
  | .bot =>
    have hoc := hcons p; simp only [hfp] at hoc
    -- r2.decided p = some (some none), r2.bound_value = some none
    have hbv2 := hinv2.1 p none hoc
    -- inputSupport(none) ≥ 1 in r2
    have hsup := hinv2.2.2.1 none hbv2
    have hpos : IdealBCA.inputSupport (IdealBCA.Val T) n s.r2 none > 0 := by
      have := hinv2.2.2.2.1; omega
    simp only [IdealBCA.inputSupport] at hpos
    obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos hpos
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hr
    -- r2.input_ r = some none, so r1.decided r = some none by feed
    have hdec := hfeed r none hr.2.2
    -- r1.decided r = some none, so by inv.5 contrapositive, bound_value ≠ none
    have hbv_ne : s.r1.bound_value ≠ none := by
      intro hbv; have := hinv1.2.2.2.2 hbv r; rw [this] at hdec; simp at hdec
    exact Option.ne_none_iff_exists'.mp hbv_ne

/-- r1.bound_value is monotone across steps. -/
private theorem r1_bound_value_mono :
    ∀ (s : State T n) l (s' : State T n),
    (doubleIdealBCA T n f).step s l s' →
    ∀ w, s.r1.bound_value = some w → s'.r1.bound_value = some w := by
  intro s l s' hstep w hbv
  match l with
  | .par cl =>
    have ⟨hpar_step, _⟩ := hstep
    simp only [par_system, parallel] at hpar_step
    match cl with
    | .left (.corrupt _) => exfalso; exact hpar_step.1 (.corrupt _) rfl
    | .left (.output _ _) => exfalso; exact hpar_step.1 (.input _ _) ⟨rfl, rfl⟩
    | .left (.input _ _) =>
      obtain ⟨_, hs₁, _⟩ := hpar_step
      obtain ⟨_, heq1⟩ := hs₁; simp only [heq1]; exact hbv
    | .left (.bind _) =>
      obtain ⟨_, hs₁, _⟩ := hpar_step
      obtain ⟨hbv_none, _, _⟩ := hs₁; rw [hbv] at hbv_none; simp at hbv_none
    | .right (.input _ _) => exfalso; exact hpar_step.1 (.output _ _) ⟨rfl, rfl⟩
    | .right (.corrupt _) => exfalso; exact hpar_step.1 (.corrupt _) rfl
    | .right (.output _ _) =>
      obtain ⟨_, _, heq1⟩ := hpar_step; rw [heq1]; exact hbv
    | .right (.bind _) =>
      obtain ⟨_, _, heq1⟩ := hpar_step; rw [heq1]; exact hbv
    | .sync (.corrupt _) (.corrupt _) =>
      obtain ⟨_, hs₁, _⟩ := hpar_step
      obtain ⟨_, _, heq1⟩ := hs₁; simp only [heq1]; exact hbv
    | .sync (.output _ _) (.input _ _) =>
      obtain ⟨_, hs₁, _⟩ := hpar_step
      obtain ⟨_, _, _, heq1⟩ := hs₁; simp only [heq1]; exact hbv
    | .sync (.corrupt _) (.input ..) | .sync (.corrupt _) (.output ..)
    | .sync (.corrupt _) (.bind ..)
    | .sync (.input ..) _ | .sync (.bind ..) _
    | .sync (.output _ _) (.corrupt ..) | .sync (.output _ _) (.output ..)
    | .sync (.output _ _) (.bind ..) => simp [sync_pred] at hpar_step
  | .output _ _ =>
    have ⟨_, _, _, heq1, _, _⟩ := hstep; rw [heq1]; exact hbv

/-- r1.bound_value is preserved by Star. -/
private theorem r1_bound_star :
    ∀ (s s' : State T n), Star (doubleIdealBCA T n f) s s' →
    ∀ w, s.r1.bound_value = some w → s'.r1.bound_value = some w := by
  intro s s' hstar w hbv
  induction hstar with
  | refl => exact hbv
  | step hs _ ih => exact ih (r1_bound_value_mono T n f _ _ _ hs w hbv)

/-- binding_inv holds at all reachable states. -/
private theorem binding_inv_reachable :
    ∀ s, Reachable (doubleIdealBCA T n f) s → binding_inv T n f s := by
  intro s hreach
  induction hreach with
  | init h => exact binding_inv_init T n f _ h
  | step _ hs ih => exact binding_inv_step T n f _ _ _ ih hs

theorem double_binding_holds : double_binding T n f := by
  intro s hreach ⟨p, fv, hcorr, hfp⟩
  have hinv_s := binding_inv_reachable T n f s hreach
  obtain ⟨hcons_s, hinv1_s, hinv2_s, hfeed_s⟩ := hinv_s
  -- The witness is r1.bound_value
  obtain ⟨v, hbv⟩ := output_implies_r1_bound_set T n f s hcons_s hinv1_s hinv2_s hfeed_s
    p fv hfp
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

end DoubleIdealBCA
