import Leslie_LTS.Framework
import Leslie_LTS.Examples.BCA
import Leslie_LTS.Examples.IdealBCA
import Leslie_LTS.Examples.BCA_Simulation

/-! # BCA Liveness: Fair-Weak-Divergence Witness and Lifted Decision

  This file instantiates `ForwardSim.WeakDivPreserving` for the existing
  `BCA_Simulation.bca_forward_sim` and uses the transfer theorem to lift
  a fair-scheduling decision property from `IdealBCA` to the concrete BCA.

  Structurally mirrors `BRB_Liveness.lean`. All declarations here are
  statements only (the Phase-3-equivalent scaffolding for the BCA family).
  The vacuous-`AllFair` clause of the witness is fully proven; the
  protocol-specific obligations (progress measure, rank well-foundedness,
  no-fair-deadlock, and the lifted decision theorems) are sorried as
  Phase-3 protocol design work.
-/

open LTS

namespace BCA_Liveness

variable (T : Type) [DecidableEq T] [Inhabited T]
variable (n f : Nat) [Inhabited (Fin n)]

/-! ## Label-level fairness -/

/-- A concrete BCA label is fair at state `s` iff every process it
    involves is correct (uncorrupted) at `s`. Mirrors `brb_fair_labels`:
    environment-controlled `input` and adversary-controlled `corrupt`
    are *not* fair — only protocol-internal progress (send/recv) and
    externalisation (output) by correct processes are fair. -/
def bca_fair_labels
    (s : BCA_LTS.State T n) (l : BCA_LTS.Label T n) : Prop :=
  match l with
  | .corrupt _          => False
  | .input _ _          => False
  | .output p _         => p ∉ s.corrupted
  | .send src dst _ _   => src ∉ s.corrupted ∧ dst ∉ s.corrupted
  | .recv src dst _ _   => src ∉ s.corrupted ∧ dst ∉ s.corrupted

/-- Matching fair-label predicate on the ideal side: `output` is fair for
    correct processes; the internal `bind` is fair (it must fire when
    enabled for the spec to be live, analogous to `commit` for BRB);
    `corrupt` and `input` are unfair. -/
def ideal_bca_fair_labels
    (s : IdealBCA.State T n) (l : IdealBCA.Label T n) : Prop :=
  match l with
  | .corrupt _   => False
  | .input _ _   => False
  | .output p _  => p ∉ s.corrupted
  | .bind _      => True

/-! ## Structural fact: every IdealBCA internal label is fair

    `ideal_labelling.is_internal = true` only for `.bind _`, which
    `ideal_bca_fair_labels` always classifies as fair (`True`). Hence
    every `InternalStar` on the ideal side is `AllFair` w.r.t.
    `ideal_bca_fair_labels`, by the framework-level helper
    `InternalStar.allFair_of_all_internal_fair`. This is the fact that
    discharges `rank_decreases_on_unfair_abstract` by `exfalso` below. -/
theorem ideal_bca_internal_label_fair (s : IdealBCA.State T n)
    (l : IdealBCA.Label T n)
    (hint : (IdealBCA.ideal_labelling T n).is_internal l = true) :
    ideal_bca_fair_labels T n s l := by
  cases l <;> simp_all [IdealBCA.ideal_labelling, ideal_bca_fair_labels]

theorem ideal_bca_internalStar_allFair
    {a b : IdealBCA.State T n}
    (star : InternalStar (IdealBCA.ideal_bca T n f)
                          (IdealBCA.ideal_labelling T n) a b) :
    star.AllFair (ideal_bca_fair_labels T n) :=
  star.allFair_of_all_internal_fair (ideal_bca_internal_label_fair T n)

/-! ## Well-founded rank on concrete states (definitions deferred) -/

/-- A `Nat`-valued progress measure on concrete BCA states. Should decrease
    on every fair correct-process step. Designing this measure is itself a
    significant protocol-specific undertaking — a natural lexicographic
    candidate is

      (round/phase, undelivered honest messages, undecided correct procs)

    following `Leslie/Examples/BindingCrusaderAgreementLiveness.lean`'s
    structure. Deferred to a follow-up that mirrors `brb_progress_measure`. -/
def bca_progress_measure (_s : BCA_LTS.State T n) : Nat := by sorry

/-- The well-founded rank: `s' < s` iff the measure strictly drops. -/
def bca_rank (s s' : BCA_LTS.State T n) : Prop :=
  bca_progress_measure T n s' < bca_progress_measure T n s

theorem bca_rank_wf :
    WellFounded (bca_rank T n) := by sorry

/-! ## No fair deadlock under `n > 3f` -/

/-- Under `n > 3f`, no reachable concrete BCA state is a fair deadlock —
    some correct process always has a fair action enabled. Mirrors the
    BRB version. -/
theorem bca_no_fair_deadlock_reachable (hn : n > 3 * f) :
    ∀ s, Reachable (BCA_LTS.bca T n f) s →
      ¬ FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s := by
  sorry

/-! ## The headline witness -/

/-- `bca_forward_sim` is weak-divergence-preserving under the fair-label
    classification above. Mirrors `brb_weak_div_witness`. -/
noncomputable def bca_weak_div_witness (hn : n > 3 * f) :
    (BCA_Simulation.bca_forward_sim T n f hn).WeakDivPreserving
      (bca_fair_labels T n)
      (ideal_bca_fair_labels T n) where
  rank := bca_rank T n
  rank_wf := bca_rank_wf T n
  rank_non_increasing := by
    -- Protocol-specific: unfair (Byzantine) internal BCA steps do not
    -- grow the rank. Tied to the definition of `bca_progress_measure`.
    sorry
  rank_decreases_on_fair_elision := by
    -- Protocol-specific: a fair internal concrete step elided by
    -- IdealBCA decreases `bca_rank` — the "helpful directions"
    -- condition. Tied to the definition of `bca_progress_measure`.
    sorry
  rank_decreases_on_unfair_abstract := by
    -- Vacuous: IdealBCA's only internal label is `.bind _`, which
    -- `ideal_bca_fair_labels` always classifies as fair (`True`).
    -- Hence every abstract `InternalStar` produced by `step_internal`
    -- is `AllFair`, contradicting the `¬ AllFair` hypothesis. `exfalso`.
    intro s₁ _l₁ _s₁' _s₂ _hreach _hR _hint _hfair _hstep _hne hnaf
    exact absurd
      (ideal_bca_internalStar_allFair T n f _) hnaf
  fair_deadlock_diverges := by
    intro s₁ s₂ hreach _hR hfd
    exact absurd hfd
      (bca_no_fair_deadlock_reachable T n f hn s₁ hreach)

/-! ## Liveness statements

    The ideal-level decision liveness, plus the concrete-level decision
    obtained by transferring it through `bca_weak_div_witness`. -/

/-- Decision property on the IDEAL: under fair scheduling, every correct
    process eventually decides. -/
theorem ideal_bca_decision :
    (IdealBCA.ideal_bca T n f).satisfies
      (assumes_fair_wf
        (IdealBCA.ideal_bca T n f)
        (ideal_bca_fair_labels T n)
        (eventually (state_prop (fun s : IdealBCA.State T n =>
          ∀ p, p ∉ s.corrupted → s.decided p ≠ none)))) := by
  sorry

/-- The concrete-side decision property, lifted from `ideal_bca_decision`
    via the transfer theorem applied to `bca_weak_div_witness`. -/
theorem bca_decision (hn : n > 3 * f) :
    (BCA_LTS.bca T n f).satisfies
      (assumes_fair_wf
        (BCA_LTS.bca T n f)
        (bca_fair_labels T n)
        (eventually (state_prop (fun s : BCA_LTS.State T n =>
          ∀ p, p ∉ s.corrupted → (s.local_ p).decided ≠ none)))) := by
  sorry

end BCA_Liveness
