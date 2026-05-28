import Leslie_LTS.Framework.Basic
import Leslie_LTS.Framework.Trace

/-! # Divergence Predicates for LTS

    Definitions used by the weak-divergence-preserving simulation
    (Gaspard CONCUR 2026, §6.2 + §6.4):

    * `Diverges` — an infinite τ-execution from a state.
    * `WeaklyDiverges` — diverges, or reaches a deadlock via internal steps.
    * `FairDiverges` / `FairlyWeaklyDiverges` — fairness-aware variants
      parameterised by a state-dependent label predicate `fair_labels`.
-/

namespace LTS

variable {S : Type u} {L : Type v}

/-- Internal divergence: an infinite execution of internal steps from `s`. -/
def Diverges (sys : System S L) (lab : Labelling L) (s : S) : Prop :=
  ∃ e : Execution S L,
    e.states 0 = s ∧
    ∀ k, sys.step (e.states k) (e.labels k) (e.states (k + 1)) ∧
         lab.is_internal (e.labels k) = true

/-- Some τ-path leads to a state with no outgoing transitions. -/
def DeadlocksAfterTau (sys : System S L) (lab : Labelling L) (s : S) : Prop :=
  ∃ s', Nonempty (InternalStar sys lab s s') ∧ ¬ ∃ l s'', sys.step s' l s''

/-- Weak divergence: either diverges or reaches a deadlock via internal steps. -/
def WeaklyDiverges (sys : System S L) (lab : Labelling L) (s : S) : Prop :=
  Diverges sys lab s ∨ DeadlocksAfterTau sys lab s

/-- Fair divergence: an internal-only infinite execution with infinitely many
    (state, label) pairs satisfying `fair_labels`. -/
def FairDiverges
    (sys : System S L) (lab : Labelling L)
    (fair_labels : S → L → Prop) (s : S) : Prop :=
  ∃ e : Execution S L,
    e.states 0 = s ∧
    (∀ k, sys.step (e.states k) (e.labels k) (e.states (k + 1)) ∧
          lab.is_internal (e.labels k) = true) ∧
    (∀ N, ∃ k, N ≤ k ∧ fair_labels (e.states k) (e.labels k))

/-- Fair deadlock: no fair transition is enabled at `s`. -/
def FairDeadlock (sys : System S L) (fair_labels : S → L → Prop) (s : S) : Prop :=
  ∀ l s', sys.step s l s' → ¬ fair_labels s l

/-- Fairly weakly diverges: either fair-diverges, or reaches a fair deadlock
    via some τ-path. Per Gaspard CONCUR 2026 §6.4: "exists an execution …
    whose trace is τ and which is either a fair divergence or reaches a fair
    deadlock". The τ-path to the fair deadlock can use *any* internal labels
    — it is the *destination* that must be a fair deadlock. -/
def FairlyWeaklyDiverges
    (sys : System S L) (lab : Labelling L)
    (fair_labels : S → L → Prop) (s : S) : Prop :=
  FairDiverges sys lab fair_labels s ∨
  (∃ s', Nonempty (InternalStar sys lab s s') ∧
         FairDeadlock sys fair_labels s')

/-! ## Lift lemma: prepending an `InternalStar` preserves fair-weak-divergence

    Used in the soundness proof of `preserves_fair_weak_divergence` to lift
    abstract divergence at a later state back to abstract divergence at the
    starting state. Proven by induction on the `InternalStar` via the
    single-step prepend lemma `FairlyWeaklyDiverges.cons_step`. -/
/-- **Single-step prepend lemma**: a single internal step preserves
    `FairlyWeaklyDiverges`. Building block for the full `lift` lemma. -/
theorem FairlyWeaklyDiverges.cons_step
    {sys : System S L} {lab : Labelling L} {fair_labels : S → L → Prop}
    {s s' : S} {l : L}
    (hint : lab.is_internal l = true)
    (hstep : sys.step s l s')
    (h : FairlyWeaklyDiverges sys lab fair_labels s') :
    FairlyWeaklyDiverges sys lab fair_labels s := by
  rcases h with ⟨e', he'0, he'step, he'fair⟩ | ⟨s_dead, ⟨hpath⟩, hfd⟩
  · -- Fair divergence at s' lifts via Execution.cons.
    refine Or.inl ⟨Execution.cons s l e', ?_, ?_, ?_⟩
    · -- states 0 = s
      rfl
    · -- Each step is a valid internal step.
      intro k
      cases k with
      | zero =>
        refine ⟨?_, hint⟩
        simp [Execution.cons_states_zero, Execution.cons_labels_zero,
              Execution.cons_states_succ, he'0]
        exact hstep
      | succ k =>
        simp [Execution.cons_states_succ, Execution.cons_labels_succ]
        exact he'step k
    · -- Infinitely many fair labels: shift indices by 1.
      intro N
      obtain ⟨k, hkN, hfair_k⟩ := he'fair N
      refine ⟨k + 1, by omega, ?_⟩
      simp [Execution.cons_states_succ, Execution.cons_labels_succ]
      exact hfair_k
  · -- Deadlock case: prepend one step to the InternalStar.
    exact Or.inr ⟨s_dead, ⟨.step hint hstep hpath⟩, hfd⟩

/-- **Lift lemma**: prepending an `InternalStar` preserves
    `FairlyWeaklyDiverges`. Proven by induction on the `InternalStar` using
    `FairlyWeaklyDiverges.cons_step`. -/
theorem FairlyWeaklyDiverges.lift
    {sys : System S L} {lab : Labelling L} {fair_labels : S → L → Prop}
    {s s' : S}
    (hstar : InternalStar sys lab s s')
    (h : FairlyWeaklyDiverges sys lab fair_labels s') :
    FairlyWeaklyDiverges sys lab fair_labels s := by
  induction hstar with
  | refl => exact h
  | step hint hstep _ ih => exact FairlyWeaklyDiverges.cons_step hint hstep (ih h)

/-- A fair-deadlock trivially gives fair-weak-divergence via the reflexive
    internal-star path (zero steps). -/
theorem FairDeadlock.fairlyWeaklyDiverges
    {sys : System S L} {lab : Labelling L} {fair_labels : S → L → Prop}
    {s : S} (h : FairDeadlock sys fair_labels s) :
    FairlyWeaklyDiverges sys lab fair_labels s :=
  Or.inr ⟨s, ⟨.refl⟩, h⟩

end LTS
