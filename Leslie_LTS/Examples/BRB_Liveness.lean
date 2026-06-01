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

/-- A `Nat`-valued progress measure on concrete BRB states.

    **Placeholder** (currently returns 0 for all states).  The intended
    lex measure over protocol phases is:

      Dim 1: #correct procs with `returned = none`
      Dim 2: total pending fair messages in buffer (between correct procs)
      Dim 3: #correct (src, dst, t, v) tuples eligible to send but unsent

    Encoded as `D1 * K² + D2 * K + D3` with `K ≥ n² · 3` (bounded per
    value `v` — the protocol commits to at most one value per `sender`).

    The real definition replaces this when the rank obligations (D.3)
    are discharged.  Until then, `brb_rank = False` everywhere (since
    `0 < 0` is false), and `brb_rank_wf` is trivially well-founded. -/
def brb_progress_measure (_s : BRB_LTS.State n Value) : Nat := 0

/-- The well-founded rank: `s' < s` iff the measure strictly drops. -/
def brb_rank (s s' : BRB_LTS.State n Value) : Prop :=
  brb_progress_measure n Value s' < brb_progress_measure n Value s

/-- With the placeholder measure (= 0 for all states), `brb_rank` is
    `False` everywhere (0 < 0 is false), so well-foundedness is trivial
    — no infinite descending chain exists because no pair is related.
    This will need re-proof when the real measure is plugged in. -/
theorem brb_rank_wf :
    WellFounded (brb_rank n Value) :=
  ⟨fun a => ⟨a, fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

/-! ## Reachable fair-deadlocks are terminated

    The original `brb_no_fair_deadlock_reachable` (no reachable BRB
    state is a fair deadlock) is **false as stated**: a terminated
    reachable state — where every correct process has `returned ≠
    none` and no pending fair messages remain — is vacuously a
    fair-deadlock under `FairDeadlock`'s definition (every enabled
    label is unfair, since only `corrupt` / `input` adversary moves
    remain). After Phase C.2's discharge rewrite via
    `ForwardSim.fair_deadlock_lifts`, the framework no longer needs
    that false claim.

    What IS true and useful: every reachable fair-deadlock is
    terminated.  This is the right invariant for the protocol-level
    `h_fair_reverse` discharge — if `s₁` is a reachable BRB
    fair-deadlock, every correct proc has returned, and the matched
    ideal state is also "done" (no commit/output enabled), so no fair
    abstract step is enabled either. -/
theorem brb_fair_deadlock_implies_terminated (hn : n > 3 * f) :
    ∀ s, Reachable (BRB_LTS.brb n f Value sender) s →
      FairDeadlock (BRB_LTS.brb n f Value sender)
        (brb_fair_labels n Value) s →
      ∀ p, p ∉ s.corrupted → (s.local_ p).returned ≠ none := by
  -- Protocol-specific: at a fair-deadlock no fair send/recv/output is
  -- enabled.  Under n > 3f, the only way no fair output(p, _) is
  -- enabled for a correct p is `(s.local_ p).returned ≠ none` already.
  -- Proof sketched in plan §D.4; sorried for now.
  sorry

/-! ## Fair-label compatibility through the simulation

    Concrete fair labels map to abstract fair labels via `label_map`.
    Used as the `h_fair_compat` hypothesis in `transfers_satisfaction`. -/
theorem brb_fair_compat (hn : n > 3 * f) :
    ∀ s₁ l₁ s₂,
      (BRB_Simulation.brb_forward_sim n f Value sender hn).R s₁ s₂ →
      brb_fair_labels n Value s₁ l₁ →
      ideal_brb_fair_labels n Value s₂
        ((BRB_Simulation.brb_forward_sim n f Value sender hn).label_map l₁) := by
  intro s₁ l₁ s₂ hR hfair
  -- R = sim_rel → s₂.corrupted = s₁.corrupted.
  have hcorr : s₂.corrupted = s₁.corrupted := hR.1
  match l₁ with
  | .corrupt _ => exact absurd hfair (by simp [brb_fair_labels])
  | .input _ _ => exact absurd hfair (by simp [brb_fair_labels])
  | .output p v =>
    -- label_map (.output p v) = .output p v.
    -- fair_labels₁ = p ∉ s₁.corrupted; fair_labels₂ = p ∉ s₂.corrupted.
    simp only [BRB_Simulation.brb_forward_sim, BRB_Simulation.label_map,
               brb_fair_labels, ideal_brb_fair_labels] at hfair ⊢
    rw [hcorr]; exact hfair
  | .send _ _ _ v =>
    -- label_map (.send ..) = .commit v; fair_labels₂ (.commit _) = True.
    simp [BRB_Simulation.brb_forward_sim, BRB_Simulation.label_map,
          ideal_brb_fair_labels]
  | .recv _ _ _ v =>
    -- label_map (.recv ..) = .commit v; fair_labels₂ (.commit _) = True.
    simp [BRB_Simulation.brb_forward_sim, BRB_Simulation.label_map,
          ideal_brb_fair_labels]

/-! ## Structural fact: every IdealBRB internal label is fair

    `ideal_labelling.is_internal = true` only for `.commit _`, which
    `ideal_brb_fair_labels` always classifies as fair (`True`). Hence
    every `InternalStar` on the ideal side is `AllFair` w.r.t.
    `ideal_brb_fair_labels`, by the framework-level helper
    `InternalStar.allFair_of_all_internal_fair`. This is the fact that
    discharges `rank_decreases_on_unfair_abstract` by `exfalso` below. -/
theorem ideal_brb_internal_label_fair (s : IdealBRB.State n Value)
    (l : IdealBRB.Label n Value)
    (hint : (IdealBRB.ideal_labelling n Value).is_internal l = true) :
    ideal_brb_fair_labels n Value s l := by
  cases l <;> simp_all [IdealBRB.ideal_labelling, ideal_brb_fair_labels]

theorem ideal_brb_internalStar_allFair
    {a b : IdealBRB.State n Value}
    (star : InternalStar (IdealBRB.ideal_brb n f Value sender)
                          (IdealBRB.ideal_labelling n Value) a b) :
    star.AllFair (ideal_brb_fair_labels n Value) :=
  star.allFair_of_all_internal_fair (ideal_brb_internal_label_fair n Value)

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
    -- Vacuous: IdealBRB's only internal label is `.commit _`, which
    -- `ideal_brb_fair_labels` always classifies as fair (`True`). Hence
    -- every abstract `InternalStar` produced by `step_internal` is
    -- `AllFair`, contradicting the `¬ AllFair` hypothesis. `exfalso`.
    intro s₁ _l₁ _s₁' _s₂ _hreach _hR _hint _hfair _hstep _hne hnaf
    exact absurd
      (ideal_brb_internalStar_allFair n f Value sender _) hnaf
  rank_non_increasing_on_fair_progress := by
    -- Protocol-specific: at a fair correct-process internal BRB step
    -- whose IdealBRB response is non-empty AllFair (i.e. `.commit v` is
    -- the abstract response), `brb_progress_measure` does not increase.
    -- Tied to the deferred `brb_progress_measure` design (Phase 3.2 /
    -- D.1 in plans/close-framework-gaps-and-brb.md).
    sorry
  fair_deadlock_diverges := by
    -- Honest discharge via the deadlock disjunct of FairlyWeaklyDiverges.
    -- Uses the framework helper `ForwardSim.fair_deadlock_lifts` plus a
    -- protocol-specific "reverse fair-step correspondence" hypothesis.
    --
    -- The reverse correspondence: at any reachable BRB state s₁ related
    -- to IdealBRB state s₂, every fair-enabled abstract step at s₂
    -- (fair commit or fair output) has SOME fair-enabled concrete step
    -- at s₁ (the concrete output 1:1 for fair output, or a concrete
    -- recv that crosses the relevant threshold for fair commit).
    -- Protocol-specific; sorried here pending the BRB invariant work.
    intro s₁ s₂ hreach hR hfd
    apply FairDeadlock.fairlyWeaklyDiverges
    apply (BRB_Simulation.brb_forward_sim n f Value sender hn).fair_deadlock_lifts
      (brb_fair_labels n Value) (ideal_brb_fair_labels n Value) ?_ hreach hR hfd
    -- h_fair_reverse: at any reachable s₁ related to s₂, every fair
    -- abstract step has a fair concrete preimage.  Protocol-specific.
    sorry

/-! ## Liveness statements

    The ideal-level liveness, plus the concrete-level liveness obtained by
    transferring it through `brb_weak_div_witness`.

    Status (per plans/close-framework-gaps-and-brb.md):
    * `ideal_brb_totality`: pure LTL leads-to chaining on the ideal
      (commit eventually fires → output enabled → output fires →
      every correct proc has `returned`).  Phase D.5.
    * `brb_totality`: lift of `ideal_brb_totality` via
      `transfers_satisfaction` (signature relaxed and skeleton in
      place in Phase B.2; two inner sorries remain — boundary R
      witness and the fair-WF antecedent lift).  Phase D.6.

    Note: when transfers_satisfaction is consumed here, `ideal_brb_
    totality` may need to be expressed as
    `IdealBRB.ideal_brb.satisfies_stutter (IdealBRB.ideal_labelling
    n Value) (...)` to match the relaxed `h_abs` signature.  For
    state-based `eventually` properties (which both totality goals
    are), `satisfies → satisfies_stutter` is straightforward (τ-
    stutters preserve state, so the eventually fires at the same
    real-step position). -/

/-- Totality / delivery property on the IDEAL: under fair scheduling,
    once the sender has broadcast (or has been corrupted), every correct
    process eventually has `returned` populated.

    **Statement guard:** the earlier version lacked a precondition
    and was false when `input` never fires (since `input` is unfair,
    fair scheduling doesn't force it; without broadcastVal, `commit`
    never enables and no progress occurs).  The `leads_to` from
    "broadcastVal set or sender corrupt" to "all correct returned"
    is the honest conditional formulation, matching the TLA-side
    `totality` from `ByzantineReliableBroadcast.lean`. -/
theorem ideal_brb_totality :
    (IdealBRB.ideal_brb n f Value sender).satisfies
      (assumes_fair_wf
        (IdealBRB.ideal_brb n f Value sender)
        (ideal_brb_fair_labels n Value)
        (leads_to
          (state_prop (fun s : IdealBRB.State n Value =>
            s.broadcastVal ≠ none ∨ ¬ IdealBRB.isCorrect n Value s sender))
          (state_prop (fun s : IdealBRB.State n Value =>
            ∀ p, p ∉ s.corrupted → s.returned p ≠ none)))) := by
  -- Unfold: valid exec e + fair-WF antecedent → leads_to at 0.
  intro e hv h_ante
  -- leads_to at 0: ∀ k, A(e.states k) → ∃ k' ≥ k, B(e.states k').
  -- Show via the intermediate "set_up ≠ none":
  --   Step A: A → eventually (set_up ≠ none)
  --   Step B: set_up ≠ none → eventually B
  intro k hA
  -- Step A: show eventually set_up ≠ none from position k.
  have hStepA : ∃ k' ≥ k, (e.states k').set_up ≠ none := by
    -- Until-or-forever: either set_up becomes ≠ none, or stays none
    -- forever (giving permanently enabled commit → antecedent fires →
    -- set_up set → contradiction).
    by_contra h_never
    -- h_never : ¬ ∃ k' ≥ k, set_up ≠ none.  Derive: set_up = none
    -- at every k' ≥ k.
    have h_none_forever : ∀ k', k' ≥ k → (e.states k').set_up = none := by
      intro k' hk'; by_contra hne; exact h_never ⟨k', hk', hne⟩
    -- Extract a value v for which commit(v) is enabled at position k.
    -- The commit step requires:
    --   set_up = none ∧ ((isCorrect sender ∧ broadcastVal = some v) ∨ ¬ isCorrect sender)
    -- From hA (broadcastVal ≠ none ∨ ¬ isCorrect sender), we can find
    -- such a v. Full extraction is protocol reasoning; sorried here.
    -- Once we have v AND "commit(v) stays enabled" (via h_none_forever +
    -- broadcastVal_persist), the antecedent h_ante at (.commit v) k
    -- forces commit to fire, contradicting h_none_forever.
    -- commit(v) is always enabled from k onwards (since set_up = none
    -- forever and broadcastVal/corruption are monotone). Use h_ante
    -- for l = .commit v at position k.
    --
    -- h_ante at (.commit v) k gives:
    --   (∀ j, enabled (.commit v) (e.states (k+j)) ∧ fair (.commit v) (e.states (k+j)))
    --   → ∃ j, .commit v = e.labels (k+j)
    --
    -- The inner ∀ j holds because:
    --   * enabled: set_up = none (by h_none_forever) ∧ hv_or persists (by broadcastVal_persist / corruption monotone).
    --   * fair: ideal_brb_fair_labels (.commit _) = True.
    --
    -- Inner argument: pick commit(v) from hA
    -- (broadcastVal = some v if sender correct; any v if corrupt),
    -- show it's always enabled (h_none_forever + broadcastVal_persist_
    -- along + corruption monotone), use h_ante to fire it, derive
    -- contradiction with h_none_forever.
    --
    -- Building blocks in place: broadcastVal_persist_along,
    -- set_up_persist_along, ideal_brb_fair_labels (.commit) = True.
    -- The LTL unfolding (0+k index normalization, System.enabled
    -- unfolding, step-relation extraction from hv.2) needs careful
    -- Lean annotation.  Sorried.
    exact sorry
  -- Step B: from set_up ≠ none, show eventually all correct returned.
  obtain ⟨k₁, hk₁_ge, hk₁_setup⟩ := hStepA
  -- Now need: ∃ k' ≥ k₁, B(e.states k').
  -- For each correct p with returned p = none at k₁, fair scheduling
  -- of output(p, _) fires it. Finite induction.
  sorry

/-- The concrete-side totality, lifted from `ideal_brb_totality` via the
    transfer theorem applied to `brb_weak_div_witness`.

    **Statement guard** (matching `ideal_brb_totality`): the `leads_to`
    precondition on the concrete side is "sender has broadcast or been
    corrupted" — translated via `sim_rel` to the ideal's
    `broadcastVal ≠ none ∨ ¬ isCorrect sender`. -/
theorem brb_totality (hn : n > 3 * f) :
    (BRB_LTS.brb n f Value sender).satisfies
      (assumes_fair_wf
        (BRB_LTS.brb n f Value sender)
        (brb_fair_labels n Value)
        (leads_to
          (state_prop (fun s : BRB_LTS.State n Value =>
            (s.local_ sender).broadcastVal ≠ none ∨
            ¬ BRB_LTS.isCorrect n Value s sender))
          (state_prop (fun s : BRB_LTS.State n Value =>
            ∀ p, p ∉ s.corrupted → (s.local_ p).returned ≠ none)))) := by
  sorry

end BRB_Liveness
