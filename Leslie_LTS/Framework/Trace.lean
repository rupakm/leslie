import Leslie_LTS.Framework.Basic

/-! # Traces for Labelled Transition Systems

    Defines both infinite executions and finite traces,
    along with validity predicates linking them to an LTS.
-/

namespace LTS

variable {State : Type u} {Label : Type v}

/-! ## Infinite Executions -/

/-- An infinite labelled execution: an alternating sequence of states
    and labels. `states n` is the state at time `n`, and `labels n`
    is the label of the transition from time `n` to `n+1`. -/
structure Execution (State : Type u) (Label : Type v) where
  states : Nat → State
  labels : Nat → Label

/-- Two executions are equal when their state and label sequences agree. -/
@[ext] theorem Execution.ext {e₁ e₂ : Execution State Label}
    (hs : e₁.states = e₂.states) (hl : e₁.labels = e₂.labels) : e₁ = e₂ := by
  cases e₁; cases e₂; simp at *; exact ⟨hs, hl⟩

/-- Drop the first `k` steps of an execution. -/
def Execution.drop (k : Nat) (e : Execution State Label) : Execution State Label where
  states := fun n => e.states (n + k)
  labels := fun n => e.labels (n + k)

/-- Prepend a single (state, label) pair to an execution. The new execution
    starts at `s`, takes label `l` to reach `e.states 0`, then continues as `e`. -/
def Execution.cons (s : State) (l : Label) (e : Execution State Label) :
    Execution State Label where
  states := fun n => match n with | 0 => s | n+1 => e.states n
  labels := fun n => match n with | 0 => l | n+1 => e.labels n

@[simp] theorem Execution.cons_states_zero (s : State) (l : Label) (e : Execution State Label) :
    (Execution.cons s l e).states 0 = s := rfl

@[simp] theorem Execution.cons_states_succ (s : State) (l : Label) (e : Execution State Label)
    (n : Nat) : (Execution.cons s l e).states (n + 1) = e.states n := rfl

@[simp] theorem Execution.cons_labels_zero (s : State) (l : Label) (e : Execution State Label) :
    (Execution.cons s l e).labels 0 = l := rfl

@[simp] theorem Execution.cons_labels_succ (s : State) (l : Label) (e : Execution State Label)
    (n : Nat) : (Execution.cons s l e).labels (n + 1) = e.labels n := rfl

/-- The state component of a dropped execution at index `n`. -/
@[simp] theorem Execution.drop_states (e : Execution State Label) (k n : Nat) :
    (e.drop k).states n = e.states (n + k) := rfl

/-- The label component of a dropped execution at index `n`. -/
@[simp] theorem Execution.drop_labels (e : Execution State Label) (k n : Nat) :
    (e.drop k).labels n = e.labels (n + k) := rfl

/-- Dropping zero steps is the identity. -/
theorem Execution.drop_zero (e : Execution State Label) : e.drop 0 = e := by
  apply Execution.ext <;> funext n <;> simp [drop]

/-- Dropping is additive: dropping `k` then `l` equals dropping `k + l`. -/
theorem Execution.drop_drop (e : Execution State Label) (k l : Nat) :
    (e.drop k).drop l = e.drop (k + l) := by
  apply Execution.ext
  · funext n; simp [drop]; congr 1; omega
  · funext n; simp [drop]; congr 1; omega

/-- Map the states of an execution through a function. -/
def Execution.map_states {State' : Type w}
    (f : State → State') (e : Execution State Label) : Execution State' Label where
  states := f ∘ e.states
  labels := e.labels

/-- Map the labels of an execution through a function. -/
def Execution.map_labels {Label' : Type w}
    (f : Label → Label') (e : Execution State Label) : Execution State Label' where
  states := e.states
  labels := f ∘ e.labels

/-- Map both states and labels of an execution. -/
def Execution.map {State' : Type w} {Label' : Type x}
    (fs : State → State') (fl : Label → Label')
    (e : Execution State Label) : Execution State' Label' where
  states := fs ∘ e.states
  labels := fl ∘ e.labels

/-- Mapping commutes with dropping. -/
theorem Execution.map_drop {State' : Type w} {Label' : Type x}
    (fs : State → State') (fl : Label → Label')
    (e : Execution State Label) (k : Nat) :
    (e.map fs fl).drop k = (e.drop k).map fs fl := by
  apply Execution.ext <;> funext n <;> simp [map, drop, Function.comp]

/-! ## Finite Traces -/

/-- A finite labelled trace: a nonempty sequence of states connected
    by labelled transitions. -/
inductive FinTrace (State : Type u) (Label : Type v) where
  | single : State → FinTrace State Label
  | cons   : State → Label → FinTrace State Label → FinTrace State Label

/-- The first state of a finite trace. -/
def FinTrace.head : FinTrace State Label → State
  | .single s => s
  | .cons s _ _ => s

/-- The last state of a finite trace. -/
def FinTrace.last : FinTrace State Label → State
  | .single s => s
  | .cons _ _ t => t.last

/-- The number of transitions in a finite trace. -/
def FinTrace.length : FinTrace State Label → Nat
  | .single _ => 0
  | .cons _ _ t => t.length + 1

/-- A finite trace is valid: every consecutive pair is a valid step. -/
def FinTrace.valid (sys : System State Label) : FinTrace State Label → Prop
  | .single _ => True
  | .cons s l t => sys.step s l t.head ∧ FinTrace.valid sys t

/-- A finite trace is a valid run: starts from an initial state
    and all steps are valid. -/
def FinTrace.valid_run (sys : System State Label) (t : FinTrace State Label) : Prop :=
  sys.init t.head ∧ t.valid sys

/-! ## Infinite Execution Validity -/

/-- An infinite execution is valid for a system: the initial state
    satisfies `init`, and every transition satisfies `step`. -/
def System.valid_exec (sys : System State Label) (e : Execution State Label) : Prop :=
  sys.init (e.states 0) ∧ ∀ k, sys.step (e.states k) (e.labels k) (e.states (k + 1))

/-- Stuttering validity: the initial state satisfies `init`, and each step
    is either a real transition or a stutter (state unchanged, τ label). -/
def System.valid_exec_stutter (sys : System State Label)
    (lab : Labelling Label)
    (e : Execution State Label) : Prop :=
  sys.init (e.states 0) ∧ ∀ k,
    sys.step (e.states k) (e.labels k) (e.states (k + 1)) ∨
    (e.states k = e.states (k + 1) ∧ e.labels k = lab.tau)

/-- Extract step `k` from a valid execution. -/
theorem System.valid_exec_step {sys : System State Label} {e : Execution State Label}
    (hv : sys.valid_exec e) (k : Nat) :
    sys.step (e.states k) (e.labels k) (e.states (k + 1)) :=
  hv.2 k

/-- Dropping preserves step validity. -/
theorem System.valid_exec_drop {sys : System State Label} {e : Execution State Label}
    (hv : sys.valid_exec e) (k : Nat) :
    ∀ n, sys.step ((e.drop k).states n) ((e.drop k).labels n) ((e.drop k).states (n + 1)) := by
  intro n; simp [Execution.drop]
  have h : n + 1 + k = n + k + 1 := by omega
  rw [h]; exact hv.2 (n + k)

/-- Every state in a valid execution is reachable. -/
theorem System.valid_exec_reachable {sys : System State Label} {e : Execution State Label}
    (hv : sys.valid_exec e) : ∀ k, Reachable sys (e.states k) := by
  intro k; induction k with
  | zero => exact .init hv.1
  | succ k ih => exact .step ih (hv.2 k)

/-! ## Data-Level Labelled Paths

    `LPath step a b` is a finite sequence of labelled steps from `a` to `b`,
    living in `Type` so we can extract length, states, and labels.
    This is the LTS counterpart of TLA's `Path`. -/

/-- A data-level labelled path: zero or more steps from `a` to `b`. -/
inductive LPath {S : Type u} {L : Type v} (step : S → L → S → Prop)
    : S → S → Type (max u v) where
  | refl : LPath step s s
  | cons (l : L) : step s l s' → LPath step s' s'' → LPath step s s''

/-- The number of steps in a labelled path. -/
def LPath.length {S : Type u} {L : Type v} {step : S → L → S → Prop} {a b : S} : LPath step a b → Nat
  | .refl => 0
  | .cons _ _ rest => rest.length + 1

/-- The `i`-th state along a labelled path (0-indexed, 0 = source, length = target). -/
def LPath.get_state {step : S → L → S → Prop} {a b : S} :
    LPath step a b → Nat → S
  | p, 0 => match p with
    | .refl => a
    | .cons _ _ _ => a
  | p, n + 1 => match p with
    | .refl => a
    | .cons _ _ rest => rest.get_state n

/-- The `i`-th label along a labelled path (0-indexed, valid for 0 ≤ i < length). -/
def LPath.get_label {step : S → L → S → Prop} {a b : S} [Inhabited L] :
    LPath step a b → Nat → L
  | .refl, _ => default
  | .cons l _ _, 0 => l
  | .cons _ _ rest, n + 1 => rest.get_label n

/-- State 0 of any labelled path is the source `a`. -/
@[simp] theorem LPath.get_state_zero {S : Type u} {L : Type v} {step : S → L → S → Prop} {a b : S} (p : LPath step a b) : p.get_state 0 = a := by
  cases p <;> rfl

/-- State `length` of a labelled path is the target `b`. -/
theorem LPath.get_state_length {S : Type u} {L : Type v} {step : S → L → S → Prop} {a b : S} (p : LPath step a b) : p.get_state p.length = b := by
  induction p with
  | refl => rfl
  | cons _ _ _ ih => exact ih

/-- Consecutive states in a labelled path are related by `step` with the
    corresponding label. -/
theorem LPath.get_step {step : S → L → S → Prop} {a b : S} [Inhabited L]
    (p : LPath step a b) :
    ∀ (i : Nat), i < p.length →
      step (p.get_state i) (p.get_label (L := L) i) (p.get_state (i + 1)) := by
  induction p with
  | refl => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | cons l hstep rest ih =>
    intro i hi
    cases i with
    | zero =>
      simp only [get_state, get_label]
      have h0 := rest.get_state_zero
      simp only at h0 ⊢
      rw [h0]; exact hstep
    | succ i =>
      simp only [get_state, get_label]
      exact ih i (by simp only [length] at hi; omega)

/-- A labelled path of length 0 has equal endpoints. -/
theorem LPath.eq_of_length_zero {S : Type u} {L : Type v} {step : S → L → S → Prop} {a b : S} (p : LPath step a b) (h : p.length = 0) : a = b := by
  cases p with
  | refl => rfl
  | cons _ _ rest => simp [length] at h

/-- `InternalStar` implies the existence of an `LPath`. -/
theorem InternalStar.nonempty_lpath {sys : System S L} {lab : Labelling L}
    (h : InternalStar sys lab a b) : Nonempty (LPath sys.step a b) := by
  induction h with
  | refl => exact ⟨.refl⟩
  | step _ hstep _ ih => obtain ⟨p⟩ := ih; exact ⟨.cons _ hstep p⟩

/-- `InternalStar` implies the existence of an `LPath` with all internal labels. -/
theorem InternalStar.exists_internal_lpath {sys : System S L} {lab : Labelling L}
    [Inhabited L]
    (h : InternalStar sys lab a b) :
    ∃ p : LPath sys.step a b,
      ∀ i, i < p.length → lab.is_internal (p.get_label i) = true := by
  induction h with
  | refl => exact ⟨.refl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | step hint hstep _ ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨.cons _ hstep p, fun i hi => by
      cases i with
      | zero => simp [LPath.get_label]; exact hint
      | succ j => simp [LPath.get_label, LPath.length] at hi ⊢; exact hp j (by omega)⟩

/-- Convert `InternalStar` to an `LPath` with all internal labels. -/
def InternalStar.toInternalLPath {sys : System S L} {lab : Labelling L}
    [Inhabited L]
    (h : InternalStar sys lab a b) :
    { p : LPath sys.step a b //
      ∀ i, i < p.length → lab.is_internal (p.get_label i) = true } :=
  match h with
  | .refl => ⟨.refl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | .step hint hstep rest =>
    let ⟨p, hp⟩ := rest.toInternalLPath
    ⟨.cons _ hstep p, fun i hi => by
      cases i with
      | zero => simp [LPath.get_label]; exact hint
      | succ j => simp [LPath.get_label, LPath.length] at hi ⊢; exact hp j (by omega)⟩

/-- The first label of a non-empty `AllFair` `InternalStar` (via
    `toInternalLPath.val.get_label 0`) is fair at its source state.
    Used to discharge fair-cofinality in the `WeakDivPreserving`
    soundness proof. -/
theorem InternalStar.fair_first_of_nonempty_allFair
    {sys : System S L} {lab : Labelling L} [Inhabited L]
    {fair_labels : S → L → Prop}
    {a b : S} (h : InternalStar sys lab a b)
    (hne : ¬ h.IsEmpty) (haf : h.AllFair fair_labels) :
    fair_labels a (h.toInternalLPath.val.get_label 0) := by
  cases h with
  | refl => exact absurd True.intro hne
  | step hint hstep rest =>
    simp [InternalStar.toInternalLPath, LPath.get_label]
    exact haf.1

/-- `Star` implies the existence of an `LPath`. -/
theorem Star.nonempty_lpath {sys : System S L}
    (h : Star sys a b) : Nonempty (LPath sys.step a b) := by
  induction h with
  | refl => exact ⟨.refl⟩
  | step hstep _ ih => obtain ⟨p⟩ := ih; exact ⟨.cons _ hstep p⟩

/-- Convert `Star` to an `LPath` (via `Classical.choice`). -/
noncomputable def Star.toLPath' {sys : System S L}
    (h : Star sys a b) : LPath sys.step a b :=
  Classical.choice h.nonempty_lpath

/-- Append two labelled paths. -/
def LPath.append {S : Type u} {L : Type v} {step : S → L → S → Prop} {a b c : S} : LPath step a b → LPath step b c → LPath step a c
  | .refl, q => q
  | .cons l h rest, q => .cons l h (rest.append q)

/-- A single-step labelled path. -/
def LPath.single {S : Type u} {L : Type v} {step : S → L → S → Prop} {a b : S} {l : L} (h : step a l b) : LPath step a b :=
  .cons l h .refl

theorem LPath.length_append {S : Type u} {L : Type v}
    {step : S → L → S → Prop} {a b c : S}
    (p : LPath step a b) (q : LPath step b c) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | refl => simp [append, length]
  | cons l h rest ih => simp [append, length, ih]; omega

theorem LPath.length_single {S : Type u} {L : Type v}
    {step : S → L → S → Prop} {a b : S} {l : L}
    (h : step a l b) : (LPath.single h).length = 1 := by
  simp [single, length]

theorem LPath.get_label_append_left {S : Type u} {L : Type v}
    {step : S → L → S → Prop} {a b c : S} [Inhabited L]
    (p : LPath step a b) (q : LPath step b c)
    (i : Nat) (hi : i < p.length) :
    (p.append q).get_label i = p.get_label i := by
  induction p generalizing i with
  | refl => exact absurd hi (Nat.not_lt_zero _)
  | cons l h rest ih =>
    cases i with
    | zero => simp [append, get_label]
    | succ j =>
      simp only [append, get_label]
      exact ih q j (by simp [length] at hi; omega)

theorem LPath.get_label_append_right {S : Type u} {L : Type v}
    {step : S → L → S → Prop} {a b c : S} [Inhabited L]
    (p : LPath step a b) (q : LPath step b c)
    (i : Nat) (hi : i < q.length) :
    (p.append q).get_label (p.length + i) = q.get_label i := by
  induction p with
  | refl => simp [append, length]
  | cons l h rest ih =>
    simp only [append, length]
    have : rest.length + 1 + i = (rest.length + i) + 1 := by omega
    rw [this, get_label]
    exact ih q hi

theorem LPath.get_label_single {S : Type u} {L : Type v}
    {step : S → L → S → Prop} {a b : S} {l : L} [Inhabited L]
    (h : step a l b) : (LPath.single h).get_label 0 = l := by
  simp [single, get_label]

/-! ## External Label Subsequence

    Given a labelling (internal/external classification), we extract the
    subsequence of external labels from an execution. This allows expressing
    safety properties purely in terms of observable (external) labels,
    independent of internal protocol steps and state. -/

/-- Count of external labels in positions `0 ..< k`. -/
def externalCount (lab : Labelling Label) (labels : Nat → Label) (k : Nat) : Nat :=
  (List.range k).filter (fun i => lab.is_external (labels i)) |>.length

/-- Find the position of the `k`-th external label (0-indexed) by
    searching from position `start`. Returns `start` as a fallback
    if no external label is found (shouldn't happen in well-formed traces). -/
def nthExternalPosFrom (lab : Labelling Label) (labels : Nat → Label)
    (k : Nat) (start : Nat) (fuel : Nat) : Nat :=
  match fuel with
  | 0 => start
  | fuel + 1 =>
    if lab.is_external (labels start) then
      match k with
      | 0 => start
      | k + 1 => nthExternalPosFrom lab labels k (start + 1) fuel
    else
      nthExternalPosFrom lab labels k (start + 1) fuel

/-- The position of the `k`-th external label.
    Uses a fuel parameter large enough for any reasonable trace. -/
def nthExternalPos (lab : Labelling Label) (labels : Nat → Label)
    (k : Nat) : Nat :=
  nthExternalPosFrom lab labels k 0 (k + 1)  -- fuel is a placeholder; see noncomputable version

/-- The external label subsequence as a function `Nat → Label`.
    Returns the k-th external label if it exists, `default` otherwise. -/
noncomputable def externalSubseq
    (lab : Labelling Label) (labels : Nat → Label) : Nat → Label :=
  fun k =>
    have := Classical.propDecidable
    if h : ∃ n, externalCount lab labels n = k ∧ lab.is_external (labels n) = true
    then labels (Classical.choose h)
    else lab.tau

/-! ### Properties of externalCount and externalSubseq -/

theorem externalCount_zero (lab : Labelling Label) (labels : Nat → Label) :
    externalCount lab labels 0 = 0 := by
  simp [externalCount]

theorem externalCount_succ (lab : Labelling Label) (labels : Nat → Label) (n : Nat) :
    externalCount lab labels (n + 1) =
      externalCount lab labels n +
        if lab.is_external (labels n) = true then 1 else 0 := by
  simp only [externalCount, List.range_succ, List.filter_append, List.length_append]
  simp only [List.filter_cons, List.filter_nil]
  split <;> simp

theorem externalCount_mono (lab : Labelling Label) (labels : Nat → Label)
    {n m : Nat} (h : n ≤ m) :
    externalCount lab labels n ≤ externalCount lab labels m := by
  induction m with
  | zero => simp [Nat.le_zero.mp h]
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact Nat.le_refl _
    · have := ih (Nat.lt_succ_iff.mp hlt)
      rw [externalCount_succ]; split <;> omega

theorem externalCount_succ_external (lab : Labelling Label) (labels : Nat → Label)
    (n : Nat) (hext : lab.is_external (labels n) = true) :
    externalCount lab labels (n + 1) = externalCount lab labels n + 1 := by
  rw [externalCount_succ]; simp [hext]

/-- Strict monotonicity: if n₁ < n₂ and both are external positions,
    then externalCount at n₁ < externalCount at n₂. -/
theorem externalCount_strict_mono_external (lab : Labelling Label) (labels : Nat → Label)
    {n₁ n₂ : Nat} (hlt : n₁ < n₂)
    (h₁ : lab.is_external (labels n₁) = true) :
    externalCount lab labels n₁ < externalCount lab labels n₂ := by
  have h_succ : externalCount lab labels n₁ + 1 =
      externalCount lab labels (n₁ + 1) := by
    rw [externalCount_succ_external lab labels n₁ h₁]
  have h_mono : externalCount lab labels (n₁ + 1) ≤
      externalCount lab labels n₂ :=
    externalCount_mono lab labels hlt
  omega

/-- Uniqueness: at most one external position has a given externalCount value. -/
theorem externalCount_external_unique (lab : Labelling Label) (labels : Nat → Label)
    {n₁ n₂ : Nat}
    (heq : externalCount lab labels n₁ = externalCount lab labels n₂)
    (h₁ : lab.is_external (labels n₁) = true)
    (h₂ : lab.is_external (labels n₂) = true) :
    n₁ = n₂ := by
  rcases Nat.lt_or_ge n₁ n₂ with hlt | hge
  · exact absurd heq (Nat.ne_of_lt
      (externalCount_strict_mono_external lab labels hlt h₁))
  · rcases Nat.eq_or_lt_of_le hge with rfl | hlt
    · rfl
    · exact absurd heq.symm (Nat.ne_of_lt
        (externalCount_strict_mono_external lab labels hlt h₂))

/-- If position `n` is the `k`-th external label, then `externalSubseq` at `k`
    returns `labels n`. -/
theorem externalSubseq_eq
    (lab : Labelling Label) (labels : Nat → Label)
    {n k : Nat} (hcount : externalCount lab labels n = k)
    (hext : lab.is_external (labels n) = true) :
    externalSubseq lab labels k = labels n := by
  unfold externalSubseq
  have hex : ∃ m, externalCount lab labels m = k ∧ lab.is_external (labels m) = true :=
    ⟨n, hcount, hext⟩
  rw [dif_pos hex]
  have h_spec := Classical.choose_spec hex
  exact congrArg labels (externalCount_external_unique lab labels
    (h_spec.1.trans hcount.symm) h_spec.2 hext)

/-- When there is no k-th external label, `externalSubseq` returns `τ`. -/
theorem externalSubseq_default
    (lab : Labelling Label) (labels : Nat → Label) (k : Nat)
    (h : ¬∃ n, externalCount lab labels n = k ∧ lab.is_external (labels n) = true) :
    externalSubseq lab labels k = lab.tau := by
  unfold externalSubseq; exact dif_neg h

/-- If an external label appears at position `n`, it appears in the external
    subsequence. Converse: the external subsequence value at the right index. -/
theorem external_label_in_subseq
    (lab : Labelling Label) (labels : Nat → Label)
    {n : Nat} (hext : lab.is_external (labels n) = true) :
    externalSubseq lab labels (externalCount lab labels n) = labels n :=
  externalSubseq_eq lab labels rfl hext

/-- Every value in the external subsequence comes from some position in the
    execution. If the value is external, the source position is identified. -/
theorem externalSubseq_source
    (lab : Labelling Label) (labels : Nat → Label) (k : Nat)
    (hext : lab.is_external (externalSubseq lab labels k) = true) :
    ∃ n, labels n = externalSubseq lab labels k ∧
      lab.is_external (labels n) = true ∧
      externalCount lab labels n = k := by
  unfold externalSubseq at hext ⊢
  have := Classical.propDecidable
  by_cases h : ∃ n, externalCount lab labels n = k ∧ lab.is_external (labels n) = true
  · rw [dif_pos h] at hext ⊢
    have hspec := Classical.choose_spec h
    exact ⟨Classical.choose h, rfl, hspec.2, hspec.1⟩
  · rw [dif_neg h] at hext
    simp [Labelling.is_external, lab.tau_internal] at hext

end LTS
