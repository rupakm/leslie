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

/-! ## BCA Protocol Reasoning Cheatsheet

    For the full TLA-level proof, see
    `Leslie/Examples/BindingCrusaderAgreementLiveness.lean` (4513 lines).

    ### Protocol structure (Graded BCA under n > 3f, binary values T)

    The concrete BCA has 5 label types: `corrupt`, `input`, `send`,
    `recv`, `output` (called `decide` in the TLA version). Fair labels
    are `send`/`recv`/`output` where all involved processes are correct.

    BCA operates over a binary value type `T` with at most 2 input
    values (`b₀`, `b₁`). The `Val T` type adds `none` (⊥ = "no binary
    decision") to `some b : T`.

    ### Thresholds (from `BCA.lean`)

    * `amplifyThreshold f = f + 1`  (for init amplification)
    * `approveThreshold n f = n - f` (for approval → echo)
    * `echoThreshold n f = n - f`    (for echo quorum → vote binary)
    * `returnThreshold n f = n - f`  (for decision)

    ### The delivery chain (from TLA-side proof, lines 3062–3470)

    Much more complex than BRB — 4 message phases instead of BRB's 2:

    1. **Init delivery** (`init_delivery_correct_sender`, line 3068):
       Correct sender p with `input = some b` → `init(some b)` delivered
       to every receiver q. Uses `wf_send` + `wf_recv`.

    2. **Init amplification** (`amplify_init_delivery`, line 3156):
       If `countInitRecv ≥ f+1` for value `b`, re-broadcast `init(b)`
       to all. Under n > 3f with binary inputs, enough correct procs
       have the same input → amplification threshold crossed.

    3. **Echo delivery** (`echo_delivery_from_approved`, line 3195):
       If correct p has `approved b` (got enough init receipts), p
       echoes. Once `countEchoRecv ≥ n-f` for some b, p can vote
       binary (some b). If two distinct values approved, p votes ⊥.

    4. **Vote delivery** (`vote_delivery_from_ready`, line 3307):
       Given echo quorum OR both-approved, p sends vote. Each vote is
       delivered to every receiver via `wf_chain_type` (handles the
       "vote-once" constraint — once voted, the value is fixed).

    5. **Decision delivery**:
       * `decide_delivery_binary` (line 3419): ≥ n-f binary votes
         for some b → decide (some b).
       * `decide_delivery_none` (line 3456): two distinct approved
         values + ≥ n-f total votes → decide none (⊥).

    ### Key difference from BRB

    BRB has a single "commit" phase on the ideal side. BCA has a
    multi-phase delivery chain (init → echo → vote → decide) where
    each phase depends on the previous one's quorum being reached.
    The ideal BCA has a single "bind" internal step (analogous to
    BRB's "commit") that sets the `bound_value`.

    ### Fairness (TLA-side, line 60)

    ```
    bca_fairness = WF(correct send) ∧ WF(recv) ∧ WF(decide)
    ```

    Three weak-fairness obligations. In the LTS framework, these map
    to `assumes_fair_wf` with `bca_fair_labels` selecting the fair
    labels.

    ### WF applications (TLA-side, lines 2516–2660)

    * `wf_send`: if send gate is open (unfired correct send with
      preconditions met), the send eventually fires.
    * `wf_send_type`: type-level send — fires for SOME value in a set
      of values with open gates. Handles the echo/vote "commitment"
      (once echoed/voted, the value is fixed).
    * `wf_recv`: message in buffer → eventually received.
    * `wf_decide`: if decide gate is open (threshold crossed, not yet
      decided), the decide eventually fires.
    * `wf_chain`: composed delivery: gate open → send → buffer →
      recv → delivered. The workhorse lemma.
    * `wf_chain_type`: type-level chain — delivers SOME value from a
      set of values with open gates.

    ### Persistence lemmas (TLA-side, lines 86–920)

    ~20 persistence lemmas covering all local-state fields:
    `input_persist`, `sent_persist`, `isCorrect_persist`,
    `initRecv_persist`, `echoRecv_persist`, `echoed_persist`,
    `approved_persist`, `voteRecv_persist`, `decided_persist`,
    `voted_persist`, `countEchoRecv_persist`, `countVoteRecv_persist`,
    `countAnyVoteRecv_persist`, `countInitRecv_persist`.

    ### How this applies to the BCA sorries

    **ideal_bca_decision:**
    Same until-or-forever structure as ideal_brb_totality:
    Step A: input ready → bound_value eventually set (via fair bind,
      which requires inputSupport ≥ f+1 — guaranteed by binary input
      assumption + n > 3f pigeonhole).
    Step B: bound_value set → all correct procs eventually decide (via
      fair output, since set_up = bound_value persists and output
      requires isCorrect + decided = none + bound_value = some v).

    **bca_decision:**
    Same `transfers_leads_to` pattern as `brb_totality`.

    **bca_fair_deadlock_implies_terminated:**
    Same argument as BRB: at a fair-deadlock, no fair step is enabled.
    If correct p has `decided = none`, show some fair step is enabled
    (output if enough votes, or fair recv/send upstream).

    **Rank obligations:**
    Same placeholder pattern as BRB. Design a lex measure over
    (decided_count, vote_pending, echo_pending, init_pending).
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

/-! ## Reachable fair-deadlocks are terminated (mirrors BRB)

    The original `bca_no_fair_deadlock_reachable` was false at
    terminated reachable states (vacuously fair-deadlocks); replaced
    after Phase C.2 by the honest claim that any reachable
    fair-deadlock is terminated. -/
theorem bca_fair_deadlock_implies_terminated (hn : n > 3 * f) :
    ∀ s, Reachable (BCA_LTS.bca T n f) s →
      FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s →
      ∀ p, p ∉ s.corrupted → (s.local_ p).decided ≠ none := by
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
  rank_non_increasing_on_fair_progress := by
    -- Protocol-specific: at a fair correct-process internal BCA step
    -- whose IdealBCA response is non-empty AllFair (i.e. `.bind b` is
    -- the abstract response), `bca_progress_measure` does not increase.
    -- Tied to the deferred `bca_progress_measure` design (out of scope
    -- for plans/close-framework-gaps-and-brb.md).
    sorry
  fair_deadlock_diverges := by
    -- Same shape as BRB: honest discharge via ForwardSim.fair_deadlock_
    -- lifts + a protocol-specific reverse fair-step correspondence.
    intro s₁ s₂ hreach hR hfd
    apply FairDeadlock.fairlyWeaklyDiverges
    apply (BCA_Simulation.bca_forward_sim T n f hn).fair_deadlock_lifts
      (bca_fair_labels T n) (ideal_bca_fair_labels T n) ?_ hreach hR hfd
    sorry

/-! ## Liveness statements

    The ideal-level decision liveness, plus the concrete-level decision
    obtained by transferring it through `bca_weak_div_witness`.

    Status: BCA full closure is out of scope for
    plans/close-framework-gaps-and-brb.md (BRB is the prioritised
    end-to-end target).  The statements below remain `sorry`'d.  When
    `transfers_satisfaction` is used here, `ideal_bca_decision` may need
    to be expressed as `IdealBCA.ideal_bca.satisfies_stutter
    (IdealBCA.ideal_labelling T n) (...)` to match the relaxed `h_abs`
    signature — see the analogous note in BRB_Liveness.lean. -/

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
