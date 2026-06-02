import Leslie_LTS.Framework
import Leslie_LTS.Examples.BrachaBRB
import Leslie_LTS.Examples.IdealBRB
import Leslie_LTS.Examples.BRB_Simulation

/-! # BRB Liveness: Fair-Weak-Divergence Witness and Lifted Totality

  This file instantiates `ForwardSim.WeakDivPreserving` for the existing
  `BRB_Simulation.brb_forward_sim` and uses `transfers_satisfaction` to
  lift a fair-scheduling totality property from `IdealBRB` to the
  concrete Bracha BRB.

  ## Current state (see also `plans/close-framework-gaps-and-brb.md`)

  Framework (`Leslie_LTS/Framework/Simulation.lean`) is sorry-free.
  This file has the remaining protocol-specific sorries:

  ### Dependency graph of remaining sorries

  ```
  brb_progress_measure (D.1: currently placeholder 0)
      │
      ├─→ brb_rank_wf (D.2: proven trivially for placeholder; re-prove for real measure)
      ├─→ rank_non_increasing (D.3: sorry — unfair steps don't grow measure)
      ├─→ rank_decreases_on_fair_elision (D.3: sorry — helpful fair steps decrease measure)
      ├─→ rank_non_increasing_on_fair_progress (D.3: sorry — lockstep AllFair steps ≤ measure)
      │
      └─→ [none of these block ideal_brb_totality or brb_totality — with
           the placeholder measure, brb_rank = False everywhere, so all
           rank clauses are vacuously satisfied.  The measure only matters
           if you want the composed `preserves_fair_weak_divergence` to
           produce the right witnesses at non-trivial BRB states.]

  brb_fair_deadlock_implies_terminated (D.4: sorry)
      │
      └─→ h_fair_reverse inside brb_weak_div_witness.fair_deadlock_diverges
           (line ~219: sorry — reverse fair-step correspondence)

  ideal_brb_totality (D.5: partially proven)
      │  Step A: broadcastVal → set_up ≠ none.
      │    — until-or-forever structure in place, 1 inner sorry at line ~330
      │      (OR condition: needs broadcastVal_persist_along + isCorrect case split)
      │  Step B: set_up ≠ none → all correct returned (line ~355: sorry)
      │    — finite induction: for each correct p, fair output(p, _) fires.
      │
      └─→ brb_totality (D.6: sorry — apply transfers_satisfaction with
           brb_weak_div_witness + ideal_brb_totality + brb_fair_compat)
  ```

  ### Attack order for a fresh session

  1. ~~ideal_brb_totality~~ — ✅ FULLY PROVEN (zero sorries).
  2. ~~brb_totality skeleton~~ — wired through transfers_satisfaction.
     Three inner sorries remain: ideal_brb_totality_stutter (generic
     satisfies → satisfies_stutter lift), h_prop_transfer (leads_to
     translation through sim_rel), h_ante_transfer (fair-WF antecedent
     lift from concrete to abstract).
  4. **Design brb_progress_measure** — replace placeholder 0 with a
     real lex measure. This is independent of Steps 1–3 but required for
     the simulation to produce meaningful abstract witnesses at BRB
     states (without it, `brb_rank = False` everywhere and the rank
     obligations are all vacuous).
  5. **Prove the rank obligations** (rank_non_increasing, rank_decreases_
     on_fair_elision, rank_non_increasing_on_fair_progress) against the
     real measure.
  6. **Prove brb_fair_deadlock_implies_terminated** and use it to close
     the `h_fair_reverse` sorry.
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
    -- h_ante at (.commit (default : Value)) k gives: if commit is always
    -- enabled + fair from position k, then commit fires at some k + j.
    -- NB: h_ante's inner index is `0 + k` (from `always ... e 0`),
    -- which we normalize via `show` / omega.
    --
    -- Pick v: any value works for the corrupt sender; broadcastVal's
    -- value for the correct sender. We use `default` for simplicity
    -- (the OR-condition covers both cases).
    -- Extract a concrete value v to commit.  Case-split on hA:
    --   * broadcastVal ≠ none → extract v from broadcastVal = some v.
    --   * ¬ isCorrect sender → any value works (corrupt branch of OR).
    -- In both cases, derive `h_or_at : ∀ k', k ≤ k' → OR condition at k'`.
    have h_or_at : ∃ v : Value, ∀ k', k ≤ k' →
        (IdealBRB.isCorrect n Value (e.states k') sender ∧
         (e.states k').broadcastVal = some v) ∨
        ¬ IdealBRB.isCorrect n Value (e.states k') sender := by
      rcases hA with hbv | hcorrupt
      · -- broadcastVal ≠ none at k.
        obtain ⟨v, hv_eq⟩ := Option.ne_none_iff_exists'.mp hbv
        refine ⟨v, fun k' hk' => ?_⟩
        by_cases hcorr : IdealBRB.isCorrect n Value (e.states k') sender
        · have hv_eq' : (e.states k).broadcastVal = some v := by
            have h0k : 0 + k = k := by omega
            rwa [h0k] at hv_eq
          have hbv_k' := IdealBRB.broadcastVal_persist_along hv hv_eq' k' (by omega)
          exact Or.inl ⟨hcorr, hbv_k'⟩
        · exact Or.inr hcorr
      · -- sender corrupt at k.  Corruption only grows (corrupt step
        -- adds to the list; no step removes from it).  So ¬ isCorrect
        -- persists.
        refine ⟨default, fun k' hk' => ?_⟩
        right
        -- ¬ isCorrect at k → sender ∈ corrupted at k → persists to k'.
        simp only [IdealBRB.isCorrect] at hcorrupt ⊢
        push_neg at hcorrupt ⊢
        have hcorrupt' : sender ∈ (e.states (0 + k)).corrupted := hcorrupt
        exact IdealBRB.corrupted_mem_persist_along hv hcorrupt' k' (by omega)
    obtain ⟨v, h_or_persist⟩ := h_or_at
    have h_commit_always := h_ante (IdealBRB.Label.commit v) k
    have h_inner : ∀ j',
        (IdealBRB.ideal_brb n f Value sender).enabled
          (.commit v) (e.states (0 + k + j')) ∧
        ideal_brb_fair_labels n Value
          (e.states (0 + k + j')) (.commit v) := by
      intro j'
      have hpos : 0 + k + j' = k + j' := by omega
      rw [hpos]
      constructor
      · refine ⟨{ (e.states (k + j')) with set_up := some v }, ?_⟩
        show (IdealBRB.ideal_brb n f Value sender).step _ (.commit v) _
        simp only [IdealBRB.ideal_brb]
        refine ⟨h_none_forever (k + j') (by omega),
               h_or_persist (k + j') (by omega), ?_⟩
        simp
      · simp [ideal_brb_fair_labels]
    obtain ⟨j, hj⟩ := h_commit_always h_inner
    have hpos : 0 + k + j = k + j := by omega
    rw [hpos] at hj
    have h_step_kj := hv.2 (k + j)
    rw [← hj] at h_step_kj
    simp only [IdealBRB.ideal_brb] at h_step_kj
    obtain ⟨_, _, heq_s'⟩ := h_step_kj
    have h_set : (e.states (k + j + 1)).set_up = some v := by rw [heq_s']
    have h_none := h_none_forever (k + j + 1) (by omega)
    rw [h_set] at h_none
    exact absurd h_none (by simp)
  -- Step B: from set_up ≠ none, show eventually all correct returned.
  obtain ⟨k₁, hk₁_ge, hk₁_setup⟩ := hStepA
  -- Step B: from set_up ≠ none at k₁, show all correct procs eventually return.
  -- Extract the value v from set_up.
  obtain ⟨v, hv_setup⟩ := Option.ne_none_iff_exists'.mp hk₁_setup
  -- set_up persists from k₁ onwards.
  have h_setup_persist : ∀ k', k₁ ≤ k' → (e.states k').set_up = some v :=
    IdealBRB.set_up_persist_along hv hv_setup
  -- For each correct p, if returned p = none at some k' ≥ k₁, then
  -- output(p, v) is permanently enabled + fair from k' until it fires.
  -- Use h_ante to fire it; after it fires, returned p = some v ≠ none.
  --
  -- We show: ∀ p, p ∉ (e.states k₁).corrupted →
  --   ∃ k' ≥ k₁, (e.states k').returned p ≠ none.
  -- Then combine with returned_persist_along to get the goal at some
  -- final k' ≥ k₁ ≥ k.
  -- The goal is: ∃ k' ≥ k, ∀ p, p ∉ (e.states k').corrupted → returned p ≠ none.
  -- Strategy: for each p : Fin n, if p is correct at the final position,
  -- then either p was already returned at k₁ (persistence), or p stayed
  -- correct long enough for output to fire (fair scheduling).
  --
  -- Key: the ∀ p quantifier's antecedent is "p ∉ corrupted at k'" (not
  -- at k₁). So if p gets corrupted between k₁ and k', the antecedent is
  -- false and we're done vacuously. We only need to handle p that stays
  -- correct throughout.
  --
  -- For each correct-at-k₁ proc p, case-split:
  --   (a) p stays correct forever: output(p, v) is permanently enabled +
  --       fair from k₁. h_ante fires it. returned p = some v persists.
  --   (b) p gets corrupted at some k₂ > k₁: at any k' ≥ k₂, p ∈
  --       corrupted, so "p ∉ corrupted → returned p ≠ none" is vacuous.
  --
  -- In case (a), we get k'_p with returned p ≠ none at k'_p; by
  -- returned_persist_along, returned p ≠ none at all k' ≥ k'_p. Take
  -- the max of all k'_p across the (finitely many) case-(a) procs.
  --
  -- Mechanically: prove the per-proc claim for procs that stay correct,
  -- take the max, then verify the universal ∀ p statement at that max.
  -- The finite-max argument uses `Finset.sup` over `Fin n`.
  --
  -- Per-proc claim: if p stays correct forever from k₁, then
  -- returned p ≠ none eventually.
  have h_per_proc : ∀ p,
      (∀ k', k₁ ≤ k' → p ∉ (e.states k').corrupted) →
      ∃ k', k₁ ≤ k' ∧ (e.states k').returned p ≠ none := by
    intro p h_stays_correct
    by_contra h_never_ret
    have h_ret_none : ∀ k', k₁ ≤ k' → (e.states k').returned p = none := by
      intro k' hk'; by_contra hne
      exact h_never_ret ⟨k', hk', hne⟩
    -- output(p, v) permanently enabled + fair from k₁.
    have h_output_always := h_ante (IdealBRB.Label.output p v) k₁
    have h_output_inner : ∀ j',
        (IdealBRB.ideal_brb n f Value sender).enabled
          (.output p v) (e.states (0 + k₁ + j')) ∧
        ideal_brb_fair_labels n Value
          (e.states (0 + k₁ + j')) (.output p v) := by
      intro j'
      have hpos : 0 + k₁ + j' = k₁ + j' := by omega
      rw [hpos]
      constructor
      · refine ⟨{ (e.states (k₁ + j')) with
                  returned := fun q => if q = p then some v
                    else (e.states (k₁ + j')).returned q }, ?_⟩
        show (IdealBRB.ideal_brb n f Value sender).step _ (.output p v) _
        simp only [IdealBRB.ideal_brb]
        exact ⟨h_stays_correct (k₁ + j') (by omega),
               h_ret_none (k₁ + j') (by omega),
               h_setup_persist (k₁ + j') (by omega), by simp⟩
      · -- fair: p ∉ corrupted at k₁ + j'
        simp only [ideal_brb_fair_labels]
        exact h_stays_correct (k₁ + j') (by omega)
    obtain ⟨j, hj⟩ := h_output_always h_output_inner
    have hpos : 0 + k₁ + j = k₁ + j := by omega
    rw [hpos] at hj
    have h_step_out := hv.2 (k₁ + j)
    rw [← hj] at h_step_out
    simp only [IdealBRB.ideal_brb] at h_step_out
    obtain ⟨_, _, _, heq_s'⟩ := h_step_out
    have h_ret_set : (e.states (k₁ + j + 1)).returned p = some v := by
      rw [heq_s']; simp
    exact absurd (h_ret_none (k₁ + j + 1) (by omega)) (by rw [h_ret_set]; simp)
  -- Combine per-proc results into the goal.
  -- For each p : Fin n, get a k'_p ≥ k₁ where the per-proc implication
  -- holds at all k' ≥ k'_p (by persistence of returned + corruption).
  have h_per_proc_persist : ∀ p : Fin n, ∃ k'_p, k₁ ≤ k'_p ∧
      ∀ k', k'_p ≤ k' →
        (p ∉ (e.states k').corrupted → (e.states k').returned p ≠ none) := by
    intro p
    by_cases h_correct : ∀ k', k₁ ≤ k' → p ∉ (e.states k').corrupted
    · -- p stays correct forever → h_per_proc gives k'_p with returned ≠ none.
      obtain ⟨k'_p, hk'_p, hret⟩ := h_per_proc p h_correct
      -- returned persists from k'_p onwards.
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hret
      refine ⟨k'_p, hk'_p, fun k' hk' _ => ?_⟩
      have := IdealBRB.returned_persist_along hv hw k' hk'
      simp [this]
    · -- p gets corrupted at some point. Get the earliest corruption time.
      push_neg at h_correct
      obtain ⟨k₂, hk₂, hc⟩ := h_correct
      -- At any k' ≥ k₂, p ∈ corrupted (persistence), so the implication
      -- p ∉ corrupted → ... is vacuously true.
      refine ⟨k₂, by omega, fun k' hk' hcorr => ?_⟩
      exact absurd (IdealBRB.corrupted_mem_persist_along hv hc k' hk') hcorr
  -- Take k_max = max over all per-proc k'_p values.
  -- Use Finset.univ.sup' to compute the max.
  -- Finite-max wrapper.
  classical
  let k'_fn : Fin n → Nat := fun p => (h_per_proc_persist p).choose
  have hk'_spec : ∀ p, k₁ ≤ k'_fn p ∧
      ∀ k', k'_fn p ≤ k' →
        (p ∉ (e.states k').corrupted → (e.states k').returned p ≠ none) :=
    fun p => (h_per_proc_persist p).choose_spec
  -- Goal: eventually (state_prop (∀ p ∉ corrupted, returned p ≠ none)) e (0 + k)
  -- = ∃ j, (∀ p ∉ (e.states (0+k+j)).corrupted, (e.states (0+k+j)).returned p ≠ none)
  simp only [eventually, state_prop]
  by_cases hn0 : n = 0
  · subst hn0
    exact ⟨k₁ - k, by intro p; exact Fin.elim0 p⟩
  · haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    let k_max := Finset.univ.sup k'_fn
    have hk_max_ge : ∀ p, k'_fn p ≤ k_max :=
      fun p => Finset.le_sup (Finset.mem_univ p)
    have hk_max_ge_k₁ : k₁ ≤ k_max := by
      have := (hk'_spec ⟨0, by omega⟩).1
      have := hk_max_ge ⟨0, by omega⟩
      omega
    refine ⟨k_max - k, ?_⟩
    have hkmax_eq : 0 + k + (k_max - k) = k_max := by omega
    rw [hkmax_eq]
    intro p hp
    exact (hk'_spec p).2 k_max (hk_max_ge p) hp

/-- Lift `ideal_brb_totality` to `satisfies_stutter`.  Every `valid_exec`
    is also a `valid_exec_stutter` (with no stutters), so `satisfies`
    implies `satisfies_stutter` for any property. -/
theorem ideal_brb_totality_stutter :
    (IdealBRB.ideal_brb n f Value sender).satisfies_stutter
      (IdealBRB.ideal_labelling n Value)
      (assumes_fair_wf
        (IdealBRB.ideal_brb n f Value sender)
        (ideal_brb_fair_labels n Value)
        (leads_to
          (state_prop (fun s : IdealBRB.State n Value =>
            s.broadcastVal ≠ none ∨ ¬ IdealBRB.isCorrect n Value s sender))
          (state_prop (fun s : IdealBRB.State n Value =>
            ∀ p, p ∉ s.corrupted → s.returned p ≠ none)))) := by
  intro e hv_stutter h_ante
  -- hv_stutter : valid_exec_stutter. We need to apply ideal_brb_totality
  -- which requires valid_exec. But e may contain stutters, so this doesn't
  -- directly work. Instead, use the fact that assumes_fair_wf's antecedent
  -- (weak fairness for each label) implies the property φ, and stutter
  -- steps don't affect state-based properties.
  --
  -- For now, sorry — this is a generic lifting issue (satisfies →
  -- satisfies_stutter for state-based properties). The right fix is
  -- either a stutter-removal helper or a generic `satisfies_le_
  -- satisfies_stutter` lemma for state-based TraceProp.
  sorry

/-- The concrete-side totality, lifted from `ideal_brb_totality` via
    `transfers_satisfaction` applied to `brb_weak_div_witness`. -/
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
  -- Apply transfers_satisfaction with the BRB witness.
  apply ForwardSim.WeakDivPreserving.transfers_satisfaction
    (brb_weak_div_witness n f Value sender hn)
    (brb_fair_compat n f Value sender hn)
    (by intro l₁ hl₁; cases l₁ <;>
        simp [BRB_LTS.brb_labelling, Labelling.is_external,
              BRB_Simulation.label_map, IdealBRB.ideal_labelling,
              BRB_Simulation.brb_forward_sim] at *)
    (by rfl)  -- h_map_tau: label_map tau = tau
  · -- h_prop_transfer: given concrete e₁, abstract e₂ with sim.R at
    -- idx-corresponding positions, and φ_abs e₂ 0 (= leads_to P_abs
    -- Q_abs e₂ 0), produce φ_con e₁ 0 (= leads_to P_con Q_con e₁ 0).
    --
    -- Strategy: unfold both leads_to; for each concrete position k with
    -- P_con, translate to P_abs at idx k via sim_rel, apply the abstract
    -- leads_to to get Q_abs at some abstract position idx k + j', then
    -- translate Q_abs back to Q_con at the concrete position k + j'
    -- (needs: idx (k + j') ≥ idx k + j' from monotonicity, plus sim.R
    -- at k + j' to transfer the state predicates).
    --
    -- The translation of B (∀ p ∉ corrupted, returned ≠ none) through
    -- sim_rel requires: corrupted agrees (sim_rel.1) and returned agrees
    -- for correct procs (sim_rel.3). Both sides are at corresponding
    -- idx-linked positions. The main subtlety: the abstract j' offset
    -- needs to be mapped back to a concrete offset, which requires the
    -- index map to be "sufficiently surjective" — every abstract position
    -- that matters is reached by some idx k'. This is protocol-specific.
    sorry
  · -- h_abs: ideal_brb_totality lifted to satisfies_stutter.
    exact ideal_brb_totality_stutter n f Value sender
  · -- h_ante_transfer: lift concrete fair-WF antecedent to abstract.
    sorry

end BRB_Liveness
