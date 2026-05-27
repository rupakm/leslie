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

/-- Reflexive-transitive closure of fair internal steps. -/
inductive FairInternalStar
    (sys : System S L) (lab : Labelling L) (fair_labels : S → L → Prop) :
    S → S → Prop where
  | refl : FairInternalStar sys lab fair_labels s s
  | step : ∀ {s l s' s''}, sys.step s l s' →
      lab.is_internal l = true → fair_labels s l →
      FairInternalStar sys lab fair_labels s' s'' →
      FairInternalStar sys lab fair_labels s s''

/-- Fairly weakly diverges: either fair-diverges, or fair-internal-stars to a
    fair deadlock. The fairness-aware analog of `WeaklyDiverges`, as used in
    Gaspard CONCUR 2026 §6.4. -/
def FairlyWeaklyDiverges
    (sys : System S L) (lab : Labelling L)
    (fair_labels : S → L → Prop) (s : S) : Prop :=
  FairDiverges sys lab fair_labels s ∨
  (∃ s', FairInternalStar sys lab fair_labels s s' ∧
         FairDeadlock sys fair_labels s')

end LTS
