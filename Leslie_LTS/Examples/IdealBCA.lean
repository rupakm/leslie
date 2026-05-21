import Leslie_LTS.Framework
import Leslie_LTS.Examples.UtilityByzantine

/-! # Ideal Binding Crusader Agreement — LTS Formulation

  An abstract BCA specification that hides message-passing complexity.
  External labels (`corrupt`, `input`, `output`) match the real BCA;
  `bind` is the sole internal label committing to a binary value.
-/

open LTS

namespace IdealBCA

variable (T : Type) [DecidableEq T]

/-- Values in the protocol: binary or ⊥. -/
abbrev Val (T : Type) := Option T

variable (n f : Nat)

/-! ### State -/

/-- The ideal BCA state. -/
structure State (T : Type) (n : Nat) where
  /-- Corrupted process list. -/
  corrupted : List (Fin n)
  /-- Per-process input. -/
  input_ : Fin n → Option T
  /-- Committed binary value, `none` if unbound. -/
  bound_value : Option T
  /-- Per-process decision. -/
  decided : Fin n → Option (Val T)

/-- Whether a process is correct. -/
def isCorrect (s : State T n) (p : Fin n) : Prop := p ∉ s.corrupted

/-- Count of correct processes with input `b`. -/
def inputSupport (s : State T n) (b : T) : Nat :=
  ((List.finRange n).filter (fun p =>
    decide (p ∉ s.corrupted) && decide (s.input_ p = some b))).length

/-! ### Labels -/

/-- Labels of the ideal BCA. -/
inductive Label (T : Type) (n : Nat) where
  /-- Corrupt a process. -/
  | corrupt (i : Fin n)
  /-- Provide input to a process. -/
  | input (i : Fin n) (v : T)
  /-- A correct process outputs a value. -/
  | output (i : Fin n) (v : Val T)
  /-- Commit to a binary bound value (internal). -/
  | bind (b : T)

/-! ### The Ideal BCA System -/

/-- The ideal BCA as a labelled transition system. -/
def ideal_bca : System (State T n) (Label T n) where
  init := fun s =>
    s.corrupted = [] ∧
    (∀ p, s.input_ p = none) ∧
    s.bound_value = none ∧
    (∀ p, s.decided p = none)
  step := fun s lbl s' =>
    match lbl with
    | .corrupt i =>
        isCorrect T n s i ∧
        s.corrupted.length + 1 ≤ f ∧
        s' = { s with corrupted := i :: s.corrupted }
    | .input i v =>
        s.input_ i = none ∧
        s' = { s with
          input_ := fun p => if p = i then some v else s.input_ p }
    | .output i v =>
        isCorrect T n s i ∧
        s.decided i = none ∧
        (match v with
         | some b => s.bound_value = some b
         | none => ∃ b b', b ≠ b' ∧ s.bound_value = some b ∧
                     s.corrupted.length + inputSupport T n s b' ≥ f + 1) ∧
        s' = { s with
          decided := fun p => if p = i then some v else s.decided p }
    | .bind b =>
        s.bound_value = none ∧
        s.corrupted.length + inputSupport T n s b ≥ f + 1 ∧
        s' = { s with bound_value := some b }

/-! ### Internal / External Labelling -/

/-- Internal/external labelling for the ideal BCA. -/
def ideal_labelling [Inhabited T] : Labelling (Label T n) where
  is_internal := fun l =>
    match l with
    | .corrupt _ => false
    | .input _ _ => false
    | .output _ _ => false
    | .bind _ => true
  tau := .bind default
  tau_internal := rfl

/-! ### Safety Properties -/

/-- Agreement: no two correct processes decide different binary values. -/
def agreement (s : State T n) : Prop :=
  ∀ p q v w,
    isCorrect T n s p → isCorrect T n s q →
    s.decided p = some (some v) →
    s.decided q = some (some w) →
    v = w

/-- Validity: unanimous correct input `v` implies decisions are `none` or `some v`. -/
def validity (v : T) (s : State T n) : Prop :=
  (∀ p, ¬isCorrect T n s p ∨ s.input_ p = none ∨ s.input_ p = some v) →
  ∀ p, s.decided p = none ∨ s.decided p = some (some v)

/-- Binding: once a correct process decides, all future correct binary decisions agree. -/
def binding (sys : System (State T n) (Label T n)) : Prop :=
  ∀ s, Reachable sys s →
    (∃ p v, isCorrect T n s p ∧ s.decided p = some v) →
    ∃ b : T, ∀ s', Star sys s s' →
      ∀ q w, isCorrect T n s' q →
        s'.decided q = some (some w) → w = b

/-! ### Monotonicity Helpers -/

/-- `inputSupport b` decreases by at most 1 when a process is corrupted. -/
private theorem inputSupport_le_succ_corrupt
    (s : State T n) (i : Fin n) (b : T) :
    inputSupport T n s b ≤
      inputSupport T n { s with corrupted := i :: s.corrupted } b + 1 := by
  simp only [inputSupport]
  suffices h : ((List.finRange n).filter (fun p =>
      decide (p ∉ s.corrupted) && decide (s.input_ p = some b))).length ≤
    ((List.finRange n).filter (fun p =>
      decide (p ∉ i :: s.corrupted) && decide (s.input_ p = some b))).length + 1 from h
  have hsplit := filter_split
    (fun p : Fin n => decide (p ∉ s.corrupted) && decide (s.input_ p = some b))
    (fun p : Fin n => !decide (p = i))
    (List.finRange n)
  have hone : ((List.finRange n).filter (fun x =>
      decide (x ∉ s.corrupted) && decide (s.input_ x = some b) &&
      !!decide (x = i))).length ≤ 1 := by
    apply Nat.le_trans (filter_and_le _ _ _)
    simp only [Bool.not_not]
    have : ∀ x : Fin n, decide (x = i) = decide (x ∈ ([i] : List (Fin n))) := by
      intro x; simp
    simp only [this]
    exact Nat.le_trans (filter_mem_le [i]) (by simp)
  have hmono : ((List.finRange n).filter (fun x =>
      decide (x ∉ s.corrupted) && decide (s.input_ x = some b) &&
      !decide (x = i))).length ≤
    ((List.finRange n).filter (fun p =>
      decide (p ∉ i :: s.corrupted) && decide (s.input_ p = some b))).length := by
    apply filter_length_mono; intro p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
               decide_eq_false_iff_not, List.mem_cons, not_or] at hp ⊢
    exact ⟨⟨hp.2, hp.1.1⟩, hp.1.2⟩
  omega

/-- `inputSupport b` is non-decreasing when a process input is set. -/
private theorem inputSupport_mono_input
    (s : State T n) (j : Fin n) (v : T) (hjnone : s.input_ j = none) (b : T) :
    inputSupport T n s b ≤
      inputSupport T n { s with
        input_ := fun p => if p = j then some v else s.input_ p } b := by
  simp only [inputSupport]; apply filter_length_mono; intro p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp ⊢
  refine ⟨hp.1, ?_⟩
  by_cases hpj : p = j
  · subst hpj; simp [hjnone] at hp
  · rw [if_neg hpj]; exact hp.2

/-! ### Strengthened Invariant -/

/-- Strengthened invariant for the ideal BCA. -/
def inv (s : State T n) : Prop :=
  (∀ p b, s.decided p = some (some b) → s.bound_value = some b) ∧
  (∀ p, s.decided p = some none →
    ∃ b₁ b₂, b₁ ≠ b₂ ∧
      s.corrupted.length + inputSupport T n s b₁ ≥ f + 1 ∧
      s.corrupted.length + inputSupport T n s b₂ ≥ f + 1) ∧
  (∀ b, s.bound_value = some b →
    s.corrupted.length + inputSupport T n s b ≥ f + 1) ∧
  s.corrupted.length ≤ f ∧
  (s.bound_value = none → ∀ p, s.decided p = none)

/-- The invariant holds at initial states. -/
theorem inv_init :
    ∀ s, (ideal_bca T n f).init s → inv T n f s := by
  intro s ⟨hcorr, hinput, hbound, hdec⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p _ hp; rw [hdec] at hp; simp at hp
  · intro p hp; rw [hdec] at hp; simp at hp
  · intro b hb; rw [hbound] at hb; simp at hb
  · rw [hcorr]; simp
  · intro _ p; exact hdec p

/-- The invariant is preserved by every step. -/
theorem inv_step :
    ∀ s l s', inv T n f s → (ideal_bca T n f).step s l s' →
      inv T n f s' := by
  intro s l s' ⟨h1, h2, h3, h4, h5⟩ hstep
  match l with
  | .corrupt i =>
    obtain ⟨_, hbudget, rfl⟩ := hstep
    have mono : ∀ b, s.corrupted.length + inputSupport T n s b ≤
        (i :: s.corrupted).length +
          inputSupport T n { s with corrupted := i :: s.corrupted } b := by
      intro b
      have := inputSupport_le_succ_corrupt T n s i b
      simp only [List.length_cons]; omega
    refine ⟨h1, ?_, ?_, by simp only [List.length_cons]; omega, h5⟩
    · intro p hp
      obtain ⟨b₁, b₂, hne, hs1, hs2⟩ := h2 p hp
      exact ⟨b₁, b₂, hne,
        Nat.le_trans hs1 (mono b₁),
        Nat.le_trans hs2 (mono b₂)⟩
    · intro b hb
      exact Nat.le_trans (h3 b hb) (mono b)
  | .input i v =>
    obtain ⟨hinp_none, rfl⟩ := hstep
    have mono := inputSupport_mono_input T n s i v hinp_none
    refine ⟨h1, ?_, ?_, h4, h5⟩
    · intro p hp
      obtain ⟨b₁, b₂, hne, hs1, hs2⟩ := h2 p hp
      exact ⟨b₁, b₂, hne, by simp; have := mono b₁; omega, by simp; have := mono b₂; omega⟩
    · intro b hb; have := mono b; have := h3 b hb; simp; omega
  | .output i v =>
    obtain ⟨_, hdec_none, hguard, rfl⟩ := hstep
    cases v with
    | some b =>
      refine ⟨?_, ?_, h3, h4, ?_⟩
      · intro p w hp
        by_cases heq : p = i
        · subst heq; simp only [↓reduceIte, Option.some.injEq] at hp; exact hp ▸ hguard
        · simp only [if_neg heq] at hp; exact h1 p w hp
      · intro p hp
        by_cases heq : p = i
        · subst heq; simp at hp
        · simp only [if_neg heq] at hp; exact h2 p hp
      · intro hbv p
        by_cases heq : p = i
        · subst heq; simp; rw [hbv] at hguard; simp at hguard
        · simp only [if_neg heq]; exact h5 hbv p
    | none =>
      obtain ⟨bv, b', hne, hbv, hsupp⟩ := hguard
      refine ⟨?_, ?_, h3, h4, ?_⟩
      · intro p w hp
        by_cases heq : p = i
        · subst heq; simp at hp
        · simp only [if_neg heq] at hp; exact h1 p w hp
      · intro p hp
        by_cases heq : p = i
        · subst heq; exact ⟨bv, b', hne, h3 bv hbv, hsupp⟩
        · simp only [if_neg heq] at hp; exact h2 p hp
      · intro hbv' _; rw [hbv'] at hbv; simp at hbv
  | .bind b =>
    obtain ⟨hbound_none, hsupp, rfl⟩ := hstep
    have h5' : ∀ p, s.decided p = none := h5 hbound_none
    refine ⟨?_, ?_, ?_, h4, ?_⟩
    · intro p w hp; have := h5' p; simp [this] at hp
    · intro p hp; have := h5' p; simp [this] at hp
    · intro w hw; simp only [Option.some.injEq] at hw; subst hw; exact hsupp
    · intro hbv; simp at hbv

/-! ### Safety Theorems -/

/-- The strengthened invariant holds for the ideal BCA. -/
theorem ideal_inv :
    (ideal_bca T n f).satisfies [ltl| □ ⌜ inv T n f ⌝] :=
  System.state_invariant _ _ (inv_init T n f) (inv_step T n f)

/-- Agreement is an invariant of the ideal BCA. -/
theorem ideal_agreement :
    (ideal_bca T n f).satisfies [ltl| □ ⌜ agreement T n ⌝] := by
  apply System.state_invariant_via (I := inv T n f)
  · exact inv_init T n f
  · exact inv_step T n f
  · intro s ⟨h1, _, _, _, _⟩ p q v w _ _ hpv hqw
    have hv := h1 p v hpv
    have hw := h1 q w hqw
    rw [hv] at hw; exact (Option.some.inj hw)

/-- The strengthened invariant implies validity. -/
theorem inv_implies_validity (v : T) (s : State T n)
    (hinv : inv T n f s) : validity T n v s := by
  obtain ⟨h1, h2, h3, h4, _⟩ := hinv
  simp only [validity]
  intro hpre p
  have no_support : ∀ w, w ≠ v → inputSupport T n s w > 0 → False := by
    intro w hwv hpos
    simp only [inputSupport] at hpos
    obtain ⟨q, hq⟩ := List.exists_mem_of_length_pos hpos
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hq
    obtain ⟨_, hqcorr, hqinp⟩ := hq
    rcases hpre q with hnc | hno | hyes
    · exact absurd hqcorr hnc
    · simp [hno] at hqinp
    · simp [hyes] at hqinp; exact hwv hqinp.symm
  match hd : s.decided p with
  | none => left; rfl
  | some (some w) =>
    by_cases hwv : w = v
    · right; rw [hwv]
    · exfalso; exact no_support w hwv (by have := h3 w (h1 p w hd); omega)
  | some none =>
    exfalso
    obtain ⟨b₁, b₂, hne, hs1, hs2⟩ := h2 p hd
    by_cases hb1v : b₁ = v
    · exact no_support b₂ (fun h => hne (hb1v.trans h.symm)) (by omega)
    · exact no_support b₁ hb1v (by omega)

/-- Validity is an invariant of the ideal BCA. -/
theorem ideal_validity (v : T) :
    (ideal_bca T n f).satisfies [ltl| □ ⌜ validity T n v ⌝] :=
  System.state_invariant_via _ _ _
    (inv_init T n f) (inv_step T n f) (inv_implies_validity T n f v)

/-- `bound_value` is monotone: once set to `some b`, it stays `some b`. -/
private theorem bound_value_mono
    (s s' : State T n) (l : Label T n)
    (hstep : (ideal_bca T n f).step s l s')
    (b : T) (hbv : s.bound_value = some b) :
    s'.bound_value = some b := by
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := hstep; exact hbv
  | .input _ _ => obtain ⟨_, rfl⟩ := hstep; exact hbv
  | .output _ _ => obtain ⟨_, _, _, rfl⟩ := hstep; exact hbv
  | .bind _ => obtain ⟨hbn, _, _⟩ := hstep; rw [hbv] at hbn; simp at hbn

/-- `bound_value` stays set along any `Star` path. -/
private theorem bound_value_star
    (s s' : State T n)
    (hstar : Star (ideal_bca T n f) s s')
    (v : T) (hbv : s.bound_value = some v) :
    s'.bound_value = some v := by
  induction hstar with
  | refl => exact hbv
  | step hs _ ih => exact ih (bound_value_mono T n f _ _ _ hs v hbv)

/-- The invariant holds at all reachable states. -/
theorem inv_reachable :
    ∀ s, Reachable (ideal_bca T n f) s → inv T n f s := by
  intro s hr
  induction hr with
  | init hinit => exact inv_init T n f _ hinit
  | step _ hstep ih => exact inv_step T n f _ _ _ ih hstep

/-- Binding: once a correct process decides, all future correct binary decisions agree. -/
theorem ideal_binding :
    binding T n (ideal_bca T n f) := by
  intro s hreach ⟨p, v, _, hdec⟩
  have hinv := inv_reachable T n f s hreach
  obtain ⟨h1, h2, h3, h4, h5⟩ := hinv
  -- Extract bound_value witness
  have hbv_ne : s.bound_value ≠ none := by
    intro hbv; have := h5 hbv p; rw [this] at hdec; simp at hdec
  obtain ⟨b, hbv⟩ := Option.ne_none_iff_exists'.mp hbv_ne
  have hinv₀ : inv T n f s := ⟨h1, h2, h3, h4, h5⟩
  exact ⟨b, fun s' hstar q w _ hdecq => by
    have hinv' := Star.preserve_inv
      (fun a l a' h hs => inv_step T n f a l a' h hs) hstar hinv₀
    have hbv' := bound_value_star T n f s s' hstar b hbv
    have hbw := hinv'.1 q w hdecq
    rw [hbv'] at hbw; exact (Option.some.inj hbw).symm⟩

/-! ### Lifting Binding via Forward Simulation

  The `binding` property has the shape required by `ForwardSim.preserves_branching`:
  ```
  ∀ s, Reachable sys s → Guard(s) → ∃ w, ∀ s', Star sys s s' → Concl(w, s')
  ```

  To lift it to a concrete system via a `ForwardSim sim`:
  1. Define `Q_guard s₁` and `Q_concl w s₁` on concrete states
  2. Show `sim.R s₁ s₂ → Q_guard s₁ → P_guard s₂` (guard transfers up)
  3. Show `sim.R s₁ s₂ → P_concl w s₂ → Q_concl w s₁` (conclusion transfers down)
  4. Apply `ForwardSim.preserves_branching`

  For BCA, with `sim_rel` relating concrete/ideal states:
  - `Q_guard s₁ = ∃ p v, isCorrect s₁ p ∧ s₁.decided p = some v`
  - `Q_concl b s₁ = ∀ q w, isCorrect s₁ q → s₁.decided q = some (some w) → w = b`
  - Guard transfer: `sim_rel` preserves `corrupted` and `decided`, so the guard lifts
  - Conclusion transfer: `sim_rel` preserves `decided` and `corrupted`, so
    a binary decision in the concrete state corresponds to one in the ideal state
-/

end IdealBCA
