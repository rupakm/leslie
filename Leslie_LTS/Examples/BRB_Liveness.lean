import Leslie_LTS.Framework
import Leslie_LTS.Examples.BrachaBRB
import Leslie_LTS.Examples.IdealBRB
import Leslie_LTS.Examples.BRB_Simulation

/-! # BRB Liveness: Fair-Weak-Divergence Witness and Lifted Totality

  This file instantiates `ForwardSim.WeakDivPreserving` for the existing
  `BRB_Simulation.brb_forward_sim` and uses the transfer theorem to lift
  a fair-scheduling totality property from `IdealBRB` to the concrete
  Bracha BRB.

  All declarations here are statements only (Phase 1.5 of the plan). Proofs
  are deferred to Phase 3.
-/

open LTS

namespace BRB_Liveness

variable (n f : Nat) (Value : Type) [DecidableEq Value]
variable [Inhabited Value] [Inhabited (Fin n)]
variable (sender : Fin n)

/-! ## Label-level fairness -/

/-- A concrete BRB label is fair at state `s` iff every process it involves
    is correct (uncorrupted) at `s`. Following the Leslie/TLA-style BRB
    fairness convention (`Leslie/Examples/ByzantineReliableBroadcast.lean`'s
    `brb_fairness`), the environment-controlled `input` and adversary-
    controlled `corrupt` are *not* fair — only protocol-internal progress
    (send/recv) and externalisation (output) by correct processes is fair. -/
def brb_fair_labels
    (s : BRB_LTS.State n Value) (l : BRB_LTS.Label n Value) : Prop :=
  match l with
  | .corrupt _          => False
  | .input _ _          => False           -- environment-controlled
  | .output p _         => p ∉ s.corrupted
  | .send src dst _ _   => src ∉ s.corrupted ∧ dst ∉ s.corrupted
  | .recv src dst _ _   => src ∉ s.corrupted ∧ dst ∉ s.corrupted

/-- Matching fair-label predicate on the ideal side: `output` is fair for
    correct processes; the internal `commit` is fair (it must fire when
    enabled for the spec to be live); `corrupt` and `input` are unfair. -/
def ideal_brb_fair_labels
    (s : IdealBRB.State n Value) (l : IdealBRB.Label n Value) : Prop :=
  match l with
  | .corrupt _   => False
  | .input _ _   => False
  | .output p _  => p ∉ s.corrupted
  | .commit _    => True

/-! ## Well-founded rank on concrete states (definitions deferred to Phase 3.2) -/

/-- A `Nat`-valued progress measure on concrete BRB states. Decreases on
    every fair correct-process step. Definition deferred to Phase 3.2. -/
def brb_progress_measure (_s : BRB_LTS.State n Value) : Nat := by sorry

/-- The well-founded rank: `s' < s` iff the measure strictly drops. -/
def brb_rank (s s' : BRB_LTS.State n Value) : Prop :=
  brb_progress_measure n Value s' < brb_progress_measure n Value s

theorem brb_rank_wf :
    WellFounded (brb_rank n Value) := by sorry

/-! ## No fair deadlock under `n > 3f` -/

/-- Under `n > 3f`, no reachable concrete state is a fair deadlock — some
    correct process always has a fair action enabled. -/
theorem brb_no_fair_deadlock_reachable (hn : n > 3 * f) :
    ∀ s, Reachable (BRB_LTS.brb n f Value sender) s →
      ¬ FairDeadlock (BRB_LTS.brb n f Value sender)
        (brb_fair_labels n Value) s := by
  sorry

/-! ## The headline witness -/

/-- `brb_forward_sim` is weak-divergence-preserving under the fair-label
    classification above. The headline witness lifting all the per-field
    obligations together. -/
noncomputable def brb_weak_div_witness (hn : n > 3 * f) :
    (BRB_Simulation.brb_forward_sim n f Value sender hn).WeakDivPreserving
      (brb_fair_labels n Value)
      (ideal_brb_fair_labels n Value) where
  rank := brb_rank n Value
  rank_wf := brb_rank_wf n Value
  rank_non_increasing := by
    -- Sorried: BRB-protocol-specific obligation that unfair (Byzantine)
    -- internal steps do not grow the rank. Should follow from the
    -- definition of brb_progress_measure (Phase 3.2 sorried).
    sorry
  rank_decreases_on_fair_elision := by
    -- Sorried: BRB-protocol-specific obligation that a fair internal
    -- concrete step elided by IdealBRB decreases brb_rank. This is the
    -- "helpful directions" condition: every correct-process action that
    -- the ideal abstracts away must record progress in the measure.
    sorry
  rank_decreases_on_unfair_abstract := by
    -- For BRB: vacuously satisfied. IdealBRB's only internal label is
    -- `commit`, which is always fair (ideal_brb_fair_labels: .commit _ =>
    -- True). So the abstract InternalStar is always AllFair, hence the
    -- hypothesis `¬ AllFair` cannot hold. The proof would `exfalso` on
    -- the hypothesis. Sorried as part of the Phase-3 BRB scaffolding.
    sorry
  fair_deadlock_diverges := by
    intro s₁ s₂ hreach _hR hfd
    exact absurd hfd
      (brb_no_fair_deadlock_reachable n f Value sender hn s₁ hreach)

/-! ## Liveness statements

    The ideal-level liveness, plus the concrete-level liveness obtained by
    transferring it through `brb_weak_div_witness`. Both sorried in Phase 1;
    proofs in Phase 3.6 and 3.7. -/

/-- Totality / delivery property on the IDEAL: under fair scheduling, every
    correct process eventually has `returned` populated. -/
theorem ideal_brb_totality :
    (IdealBRB.ideal_brb n f Value sender).satisfies
      (assumes_fair_wf
        (IdealBRB.ideal_brb n f Value sender)
        (ideal_brb_fair_labels n Value)
        (eventually (state_prop (fun s : IdealBRB.State n Value =>
          ∀ p, p ∉ s.corrupted → s.returned p ≠ none)))) := by
  sorry

/-- The concrete-side totality, lifted from `ideal_brb_totality` via the
    transfer theorem applied to `brb_weak_div_witness`. -/
theorem brb_totality (hn : n > 3 * f) :
    (BRB_LTS.brb n f Value sender).satisfies
      (assumes_fair_wf
        (BRB_LTS.brb n f Value sender)
        (brb_fair_labels n Value)
        (eventually (state_prop (fun s : BRB_LTS.State n Value =>
          ∀ p, p ∉ s.corrupted → (s.local_ p).returned ≠ none)))) := by
  sorry

end BRB_Liveness
