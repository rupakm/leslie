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
def bca_progress_measure (_s : BCA_LTS.State T n) : Nat := 0

/-- The well-founded rank: `s' < s` iff the measure strictly drops. -/
def bca_rank (s s' : BCA_LTS.State T n) : Prop :=
  bca_progress_measure T n s' < bca_progress_measure T n s

theorem bca_rank_wf :
    WellFounded (bca_rank T n) :=
  ⟨fun a => ⟨a, fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

/-! ## Fair-deadlock helpers (mirrors BRB_Liveness) -/

/-- At a fair deadlock, no fair send between correct processes is enabled. -/
theorem fair_deadlock_no_fair_send
    (s : BCA_LTS.State T n) (hfd : FairDeadlock (BCA_LTS.bca T n f)
      (bca_fair_labels T n) s)
    {src dst : Fin n} (hsrc : src ∉ s.corrupted) (hdst : dst ∉ s.corrupted)
    (t : BCA_LTS.MsgType) (v : BCA_LTS.Val T) :
    ¬ ∃ s', (BCA_LTS.bca T n f).step s (.send src dst t v) s' := by
  intro ⟨s', hstep⟩
  exact hfd (.send src dst t v) s' hstep ⟨hsrc, hdst⟩

/-- At a fair deadlock, no fair recv between correct processes is enabled. -/
theorem fair_deadlock_no_fair_recv
    (s : BCA_LTS.State T n) (hfd : FairDeadlock (BCA_LTS.bca T n f)
      (bca_fair_labels T n) s)
    {src dst : Fin n} (hsrc : src ∉ s.corrupted) (hdst : dst ∉ s.corrupted)
    (t : BCA_LTS.MsgType) (v : BCA_LTS.Val T) :
    ¬ ∃ s', (BCA_LTS.bca T n f).step s (.recv src dst t v) s' := by
  intro ⟨s', hstep⟩
  exact hfd (.recv src dst t v) s' hstep ⟨hsrc, hdst⟩

/-- At a fair deadlock, no fair output is enabled. -/
theorem fair_deadlock_no_fair_output
    (s : BCA_LTS.State T n) (hfd : FairDeadlock (BCA_LTS.bca T n f)
      (bca_fair_labels T n) s)
    {p : Fin n} (hp : p ∉ s.corrupted) (v : BCA_LTS.Val T) :
    ¬ ∃ s', (BCA_LTS.bca T n f).step s (.output p v) s' := by
  intro ⟨s', hstep⟩
  exact hfd (.output p v) s' hstep hp

/-- At a fair deadlock, a correct-to-correct message is NOT in the buffer. -/
theorem fair_deadlock_no_fair_buffer
    (s : BCA_LTS.State T n) (hfd : FairDeadlock (BCA_LTS.bca T n f)
      (bca_fair_labels T n) s)
    {src dst : Fin n} (hsrc : src ∉ s.corrupted) (hdst : dst ∉ s.corrupted)
    (t : BCA_LTS.MsgType) (v : BCA_LTS.Val T) :
    s.buffer ⟨src, dst, t, v⟩ = false := by
  by_contra hbuf
  simp only [Bool.not_eq_false] at hbuf
  -- recv(src, dst, t, v) is enabled (buffer has the message).
  -- The BCA recv step requires only that the buffer has the message.
  -- We use the step definition to construct the successor.
  have henabled : (BCA_LTS.bca T n f).enabled (.recv src dst t v) s := by
    simp only [System.enabled, BCA_LTS.bca]
    exact ⟨_, hbuf, rfl⟩
  obtain ⟨s', hstep⟩ := henabled
  exact hfd (.recv src dst t v) s' hstep ⟨hsrc, hdst⟩

/-! ## Reachable fair-deadlocks are terminated (mirrors BRB)

    The original `bca_no_fair_deadlock_reachable` was false at
    terminated reachable states (vacuously fair-deadlocks); replaced
    after Phase C.2 by the honest claim that any reachable
    fair-deadlock is terminated. -/
/-- At a reachable fair-deadlock where ALL correct processes have input,
    every correct process has decided.

    **Precondition:** `∀ q, q ∉ s.corrupted → (s.local_ q).input ≠ none`.
    The weaker precondition `∃ q correct with input` is FALSE: with n=7,
    f=2, 2 corrupt procs, and only 1 correct input, the delivery chain
    stalls (countInitRecv = 1 < amplifyThreshold = 3) and all decided
    remain none. The stronger "all correct have input" ensures pigeonhole
    over binary values: some b has ≥ ⌈(n-f)/2⌉ > f correct inputs,
    guaranteeing amplification and the full delivery chain.

    **Proof outline** (under all-correct-input + n > 3f):
    1. Pigeonhole: some value b has ≥ f+1 correct inputs.
    2. Those procs send init(b) to all correct → received (fair deadlock).
    3. countInitRecv(b) ≥ f+1 = amplifyThreshold → all correct amplify.
    4. After amplification: countInitRecv(b) ≥ n-f = approveThreshold
       → approved(b) = true for all correct.
    5. All correct echo(some b) or already echoed → sent and received.
    6. countEchoRecv(b) ≥ n-f = echoThreshold → all correct vote.
    7. All correct vote → sent and received → countVoteRecv ≥ n-f.
    8. output enabled for undecided correct → contradiction with deadlock. -/
theorem bca_fair_deadlock_implies_terminated (hn : n > 3 * f) :
    ∀ s, Reachable (BCA_LTS.bca T n f) s →
      FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s →
      (∀ q, q ∉ s.corrupted → (s.local_ q).input ≠ none) →
      ∀ p, p ∉ s.corrupted → (s.local_ p).decided ≠ none := by
  -- Deep protocol reasoning requiring the full BCA delivery chain.
  -- Steps 1-8 above formalize as: at a fair deadlock, every fair
  -- send/recv is blocked (already sent, already received, or not
  -- enabled). By backward induction from output through the chain,
  -- the only consistent configuration has all correct decided.
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
    -- Directly construct a FairDeadlock on the ideal side (or FairDiverges).
    -- Case analysis on ideal labels:
    --   * corrupt/input: not fair → trivial.
    --   * bind b: fair (= True). Need: bind not enabled.
    --     bind requires: bound_value = none ∧ inputSupport ≥ f+1.
    --     BLOCKED: sim_rel with bound_value = none gives echoSupport < echoThreshold
    --     for all b, but does NOT constrain inputSupport. Counter-example:
    --     n=7, f=2, 2 corrupt, 1 correct input b → corrupted.length + inputSupport
    --     = 2+1 = 3 = f+1, so bind IS enabled. Yet the concrete IS a valid fair
    --     deadlock (only 1 correct init source, amplifyThreshold = 3, no progress).
    --     The ideal is NOT a fair deadlock in this case, and there's no infinite
    --     internal divergence (bind fires once). So FairlyWeaklyDiverges genuinely
    --     fails here. This is a design gap in the sim_rel — it doesn't track enough
    --     structure about corrupt-to-correct init delivery. See issues.md §3.
    --   * output p v: fair iff p correct. Need: output not enabled for correct p.
    --     output requires: isCorrect, decided = none, bound_value conditions.
    --     If bound_value = none: output impossible (guard needs bound_value = some _).
    --     If bound_value ≠ none: need all correct decided ≠ none (delivery chain).
    intro s₁ s₂ hreach hR hfd
    apply FairDeadlock.fairlyWeaklyDiverges
    intro l₂ s₂' hstep hfair
    match l₂ with
    | .corrupt _ => exact absurd hfair (by simp [ideal_bca_fair_labels])
    | .input _ _ => exact absurd hfair (by simp [ideal_bca_fair_labels])
    | .bind b =>
      -- bind step requires bound_value = none ∧ inputSupport ≥ f+1.
      -- Blocked: inputSupport ≥ f+1 CAN hold at a concrete fair deadlock
      -- when corrupted.length + correct_inputs ≥ f+1, even if echoSupport is
      -- below threshold (init chain incomplete due to missing corrupt help).
      simp only [IdealBCA.ideal_bca] at hstep
      obtain ⟨_, _, _⟩ := hstep
      sorry
    | .output p v =>
      -- output requires isCorrect p, decided = none, value guard.
      -- Value guard requires bound_value ≠ none (both some/none branches).
      simp only [IdealBCA.ideal_bca] at hstep
      obtain ⟨_, hdec_none, hguard, _⟩ := hstep
      -- If bound_value = none, neither output branch is satisfiable.
      -- If bound_value ≠ none, need decided p ≠ none for all correct p
      -- (the delivery chain argument: echoSupport ≥ threshold or
      -- voteContention → vote/output chain completed at fair deadlock).
      sorry

/-! ## Liveness statements

    The ideal-level decision liveness, plus the concrete-level decision
    obtained by transferring it through `bca_weak_div_witness`.

    ### Proof structure (mirrors BRB_Liveness.lean)

    `ideal_bca_decision`: two steps through `bound_value ≠ none`:
      Step A: input_ready precondition → bound_value eventually set
        (until-or-forever: bind(b) permanently enabled + fair → fires).
      Step B: bound_value set → all correct decided
        (per-proc: output(p, v) enabled + fair → fires;
         finite-max wrapper via Finset.sup).

    `ideal_bca_decision_stutter`: same proof, step-aware h_ante.
    `bca_decision`: via `transfers_leads_to` + `bca_fair_compat`. -/

/-- Decision property on the IDEAL: under fair scheduling, once enough
    correct processes have input (the `input_ready` precondition:
    `∃ b, corrupted.length + inputSupport b ≥ f + 1`, which holds under
    binary inputs + n > 3f), every correct process eventually decides.

    The precondition is necessary: without it, `bind` is never enabled
    (no value has enough support), so no progress occurs.

    Compare BRB's `ideal_brb_totality` which has
    `broadcastVal ≠ none ∨ ¬ isCorrect sender` as precondition. -/
theorem ideal_bca_decision :
    (IdealBCA.ideal_bca T n f).satisfies
      (assumes_fair_wf
        (IdealBCA.ideal_bca T n f)
        (ideal_bca_fair_labels T n)
        (leads_to
          (state_prop (fun s : IdealBCA.State T n =>
            (∃ b, s.corrupted.length + IdealBCA.inputSupport T n s b ≥ f + 1) ∨
            s.bound_value ≠ none))
          (state_prop (fun s : IdealBCA.State T n =>
            ∀ p, p ∉ s.corrupted → s.decided p ≠ none)))) := by
  /-
  PROOF SKETCH (follow this structure — it mirrors ideal_brb_totality exactly):

  ```
  intro e hv h_ante
  intro k hA

  -- Step A: show ∃ k' ≥ k, bound_value ≠ none.
  have hStepA : ∃ k' ≥ k, (e.states k').bound_value ≠ none := by
    by_contra h_never
    have h_none_forever : ∀ k', k' ≥ k → (e.states k').bound_value = none := by
      intro k' hk'; by_contra hne; exact h_never ⟨k', hk', hne⟩
    -- From hA, extract value b with inputSupport ≥ f+1 (or bound_value ≠ none,
    -- which contradicts h_none_forever).
    -- KEY LEMMA NEEDED: show the inputSupport condition persists:
    --   corrupted.length + inputSupport b ≥ f+1 at k → same at all k' ≥ k.
    --   Proof: input_ persists (input_persist_along), corrupted only grows
    --   (so corrupted.length increases or stays), inputSupport counts
    --   correct procs with input (input stays, but proc may get corrupted →
    --   inputSupport might decrease by 1 BUT corrupted.length increases by 1
    --   → the SUM is non-decreasing).
    -- bind(b) is permanently enabled: bound_value = none ∧ condition persists.
    -- bind(b) is fair: ideal_bca_fair_labels (.bind _) = True.
    -- h_ante fires it: obtain ⟨j, hlbl, h_step⟩ := h_ante (.bind b) k h_inner
    -- Extract: (e.states (k+j+1)).bound_value = some b (from step relation).
    -- Contradiction: h_none_forever (k+j+1) vs bound_value = some b.

  -- Step B: from bound_value ≠ none, all correct decided.
  obtain ⟨k₁, hk₁_ge, hk₁_bv⟩ := hStepA
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hk₁_bv
  have h_bv_persist : ∀ k', k₁ ≤ k' → (e.states k').bound_value = some b :=
    IdealBCA.bound_value_persist_along hv hb
  -- Per-proc: for each p that stays correct, output(p, some b) is enabled + fair.
  --   enabled: isCorrect p, decided p = none, bound_value = some b. All hold.
  --   fair: p ∉ corrupted.
  --   h_ante fires it → decided p := some (some b) ≠ none.
  --   Pattern: by_contra → h_ret_none → h_output_inner → obtain ⟨j, hlbl, h_step⟩
  --   → extract decided change → contradiction.
  -- Per-proc-persist + Finset.sup finite-max wrapper (same as BRB).
  -- Use decided_persist_along, corrupted_mem_persist_along.
  ```

  The proof is ~100 LOC. Copy the structure from ideal_brb_totality
  (in BRB_Liveness.lean) and adapt:
    - broadcastVal → bound_value (renamed field)
    - returned → decided (renamed field)
    - .commit v → .bind b (renamed label)
    - .output p v → .output p (some b) (output takes Val T not Value)
    - ideal_brb_fair_labels → ideal_bca_fair_labels
    - IdealBRB.* persistence → IdealBCA.* persistence
  -/
  intro e hv h_ante
  intro k hA
  -- Step A: show ∃ k' ≥ k, bound_value ≠ none.
  have hStepA : ∃ k' ≥ k, (e.states k').bound_value ≠ none := by
    by_contra h_never
    have h_none_forever : ∀ k', k' ≥ k → (e.states k').bound_value = none := by
      intro k' hk'; by_contra hne; exact h_never ⟨k', hk', hne⟩
    -- From hA, either ∃ b with inputSupport condition, or bound_value ≠ none.
    -- The right disjunct contradicts h_none_forever directly.
    rcases hA with ⟨b, hsupp⟩ | hbv
    · -- Left: inputSupport condition at k.  The condition persists along valid execs.
      -- bind(b) is permanently enabled + fair from k.
      have hsupp_k : (e.states k).corrupted.length + IdealBCA.inputSupport T n (e.states k) b ≥ f + 1 := by
        have h0k : (0 : Nat) + k = k := Nat.zero_add k
        rw [h0k] at hsupp; exact hsupp
      have h_supp_persist : ∀ k', k ≤ k' →
          (e.states k').corrupted.length + IdealBCA.inputSupport T n (e.states k') b ≥ f + 1 :=
        fun k' hk' =>
          IdealBCA.inputSupport_condition_persist_along hv hsupp_k k' hk'
      have h_bind := h_ante (IdealBCA.Label.bind b) k
      have h_inner : ∀ j',
          (IdealBCA.ideal_bca T n f).enabled
            (.bind b) (e.states (0 + k + j')) ∧
          ideal_bca_fair_labels T n
            (e.states (0 + k + j')) (.bind b) := by
        intro j'
        have hpos : 0 + k + j' = k + j' := by omega
        rw [hpos]
        constructor
        · refine ⟨{ (e.states (k + j')) with bound_value := some b }, ?_⟩
          show (IdealBCA.ideal_bca T n f).step _ (.bind b) _
          simp only [IdealBCA.ideal_bca]
          exact ⟨h_none_forever (k + j') (by omega),
                 h_supp_persist (k + j') (by omega), by simp⟩
        · simp [ideal_bca_fair_labels]
      obtain ⟨j, hj, h_step_kj⟩ := h_bind h_inner
      have hpos : 0 + k + j = k + j := by omega
      rw [hpos] at hj h_step_kj
      rw [← hj] at h_step_kj
      simp only [IdealBCA.ideal_bca] at h_step_kj
      obtain ⟨_, _, heq_s'⟩ := h_step_kj
      have h_set : (e.states (k + j + 1)).bound_value = some b := by rw [heq_s']
      exact absurd (h_none_forever (k + j + 1) (by omega)) (by rw [h_set]; simp)
    · -- Right: bound_value ≠ none at k.  Contradicts h_none_forever directly.
      exact absurd (h_none_forever k (by omega)) (by simp only [Nat.zero_add] at hbv; exact hbv)
  -- Step B: from bound_value ≠ none, all correct decided.
  obtain ⟨k₁, hk₁_ge, hk₁_bv⟩ := hStepA
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hk₁_bv
  have h_bv_persist : ∀ k', k₁ ≤ k' → (e.states k').bound_value = some b :=
    IdealBCA.bound_value_persist_along hv hb
  -- Per-proc: if p stays correct forever, output fires and decided persists.
  have h_per_proc : ∀ p : Fin n,
      (∀ k', k₁ ≤ k' → p ∉ (e.states k').corrupted) →
      ∃ k', k₁ ≤ k' ∧ (e.states k').decided p ≠ none := by
    intro p h_stays_correct
    by_contra h_never_ret
    have h_ret_none : ∀ k', k₁ ≤ k' → (e.states k').decided p = none := by
      intro k' hk'; by_contra hne; exact h_never_ret ⟨k', hk', hne⟩
    -- output(p, some b) permanently enabled + fair from k₁.
    have h_output := h_ante (IdealBCA.Label.output p (some b)) k₁
    have h_output_inner : ∀ j',
        (IdealBCA.ideal_bca T n f).enabled
          (.output p (some b)) (e.states (0 + k₁ + j')) ∧
        ideal_bca_fair_labels T n
          (e.states (0 + k₁ + j')) (.output p (some b)) := by
      intro j'
      have hpos : 0 + k₁ + j' = k₁ + j' := by omega
      rw [hpos]
      constructor
      · refine ⟨{ (e.states (k₁ + j')) with
                  decided := fun q => if q = p then some (some b)
                    else (e.states (k₁ + j')).decided q }, ?_⟩
        show (IdealBCA.ideal_bca T n f).step _ (.output p (some b)) _
        simp only [IdealBCA.ideal_bca]
        exact ⟨by simp only [IdealBCA.isCorrect]; exact h_stays_correct (k₁ + j') (by omega),
               h_ret_none (k₁ + j') (by omega),
               h_bv_persist (k₁ + j') (by omega), by simp⟩
      · -- fair: p ∉ corrupted at k₁ + j'
        simp only [ideal_bca_fair_labels]
        exact h_stays_correct (k₁ + j') (by omega)
    obtain ⟨j, hj, h_step_out⟩ := h_output h_output_inner
    have hpos : 0 + k₁ + j = k₁ + j := by omega
    rw [hpos] at hj h_step_out
    rw [← hj] at h_step_out
    simp only [IdealBCA.ideal_bca] at h_step_out
    obtain ⟨_, _, _, heq_s'⟩ := h_step_out
    have h_dec_set : (e.states (k₁ + j + 1)).decided p = some (some b) := by
      rw [heq_s']; simp
    exact absurd (h_ret_none (k₁ + j + 1) (by omega)) (by rw [h_dec_set]; simp)
  -- Per-proc-persist + finite-max wrapper.
  have h_per_proc_persist : ∀ p : Fin n, ∃ k'_p, k₁ ≤ k'_p ∧
      ∀ k', k'_p ≤ k' →
        (p ∉ (e.states k').corrupted → (e.states k').decided p ≠ none) := by
    intro p
    by_cases h_correct : ∀ k', k₁ ≤ k' → p ∉ (e.states k').corrupted
    · obtain ⟨k'_p, hk'_p, hret⟩ := h_per_proc p h_correct
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hret
      refine ⟨k'_p, hk'_p, fun k' hk' _ => ?_⟩
      have := IdealBCA.decided_persist_along hv hw k' hk'
      simp [this]
    · push_neg at h_correct
      obtain ⟨k₂, hk₂, hc⟩ := h_correct
      refine ⟨k₂, by omega, fun k' hk' hcorr => ?_⟩
      exact absurd (IdealBCA.corrupted_mem_persist_along hv hc k' hk') hcorr
  classical
  let k'_fn : Fin n → Nat := fun p => (h_per_proc_persist p).choose
  have hk'_spec : ∀ p, k₁ ≤ k'_fn p ∧
      ∀ k', k'_fn p ≤ k' →
        (p ∉ (e.states k').corrupted → (e.states k').decided p ≠ none) :=
    fun p => (h_per_proc_persist p).choose_spec
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

/-- Stutter variant of `ideal_bca_decision` for use as `h_abs` in
    `transfers_satisfaction`. Uses unified `assumes_fair_wf` (step-aware
    "fires"). Same proof structure — at extraction points, h_ante gives
    real steps via the step conjunct. -/
theorem ideal_bca_decision_stutter :
    (IdealBCA.ideal_bca T n f).satisfies_stutter
      (IdealBCA.ideal_labelling T n)
      (assumes_fair_wf
        (IdealBCA.ideal_bca T n f)
        (ideal_bca_fair_labels T n)
        (leads_to
          (state_prop (fun s : IdealBCA.State T n =>
            (∃ b, s.corrupted.length + IdealBCA.inputSupport T n s b ≥ f + 1) ∨
            s.bound_value ≠ none))
          (state_prop (fun s : IdealBCA.State T n =>
            ∀ p, p ∉ s.corrupted → s.decided p ≠ none)))) := by
  intro e hv_stutter h_ante
  intro k hA
  -- Step A: show ∃ k' ≥ k, bound_value ≠ none.
  have hStepA : ∃ k' ≥ k, (e.states k').bound_value ≠ none := by
    by_contra h_never
    have h_none_forever : ∀ k', k' ≥ k → (e.states k').bound_value = none := by
      intro k' hk'; by_contra hne; exact h_never ⟨k', hk', hne⟩
    rcases hA with ⟨b, hsupp⟩ | hbv
    · have hsupp_k : (e.states k).corrupted.length + IdealBCA.inputSupport T n (e.states k) b ≥ f + 1 := by
        have h0k : (0 : Nat) + k = k := Nat.zero_add k
        rw [h0k] at hsupp; exact hsupp
      have h_supp_persist : ∀ k', k ≤ k' →
          (e.states k').corrupted.length + IdealBCA.inputSupport T n (e.states k') b ≥ f + 1 :=
        fun k' hk' =>
          IdealBCA.inputSupport_condition_persist_along_stutter hv_stutter hsupp_k k' hk'
      have h_bind := h_ante (IdealBCA.Label.bind b) k
      have h_inner : ∀ j',
          (IdealBCA.ideal_bca T n f).enabled
            (.bind b) (e.states (0 + k + j')) ∧
          ideal_bca_fair_labels T n
            (e.states (0 + k + j')) (.bind b) := by
        intro j'
        have hpos : 0 + k + j' = k + j' := by omega
        rw [hpos]
        constructor
        · refine ⟨{ (e.states (k + j')) with bound_value := some b }, ?_⟩
          show (IdealBCA.ideal_bca T n f).step _ (.bind b) _
          simp only [IdealBCA.ideal_bca]
          exact ⟨h_none_forever (k + j') (by omega),
                 h_supp_persist (k + j') (by omega), by simp⟩
        · simp [ideal_bca_fair_labels]
      obtain ⟨j, hlbl, h_real_step⟩ := h_bind h_inner
      have hpos : 0 + k + j = k + j := by omega
      rw [hpos] at hlbl h_real_step
      rw [← hlbl] at h_real_step
      simp only [IdealBCA.ideal_bca] at h_real_step
      obtain ⟨_, _, heq_s'⟩ := h_real_step
      have h_set : (e.states (k + j + 1)).bound_value = some b := by rw [heq_s']
      exact absurd (h_none_forever (k + j + 1) (by omega)) (by rw [h_set]; simp)
    · exact absurd (h_none_forever k (by omega)) (by simp only [Nat.zero_add] at hbv; exact hbv)
  -- Step B: from bound_value ≠ none, all correct decided.
  obtain ⟨k₁, hk₁_ge, hk₁_bv⟩ := hStepA
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hk₁_bv
  have h_bv_persist : ∀ k', k₁ ≤ k' → (e.states k').bound_value = some b :=
    IdealBCA.bound_value_persist_along_stutter hv_stutter hb
  have h_per_proc : ∀ p : Fin n,
      (∀ k', k₁ ≤ k' → p ∉ (e.states k').corrupted) →
      ∃ k', k₁ ≤ k' ∧ (e.states k').decided p ≠ none := by
    intro p h_stays_correct
    by_contra h_never_ret
    have h_ret_none : ∀ k', k₁ ≤ k' → (e.states k').decided p = none := by
      intro k' hk'; by_contra hne; exact h_never_ret ⟨k', hk', hne⟩
    have h_output := h_ante (IdealBCA.Label.output p (some b)) k₁
    have h_output_inner : ∀ j',
        (IdealBCA.ideal_bca T n f).enabled
          (.output p (some b)) (e.states (0 + k₁ + j')) ∧
        ideal_bca_fair_labels T n
          (e.states (0 + k₁ + j')) (.output p (some b)) := by
      intro j'
      have hpos : 0 + k₁ + j' = k₁ + j' := by omega
      rw [hpos]
      constructor
      · refine ⟨{ (e.states (k₁ + j')) with
                  decided := fun q => if q = p then some (some b)
                    else (e.states (k₁ + j')).decided q }, ?_⟩
        show (IdealBCA.ideal_bca T n f).step _ (.output p (some b)) _
        simp only [IdealBCA.ideal_bca]
        exact ⟨by simp only [IdealBCA.isCorrect]; exact h_stays_correct (k₁ + j') (by omega),
               h_ret_none (k₁ + j') (by omega),
               h_bv_persist (k₁ + j') (by omega), by simp⟩
      · simp only [ideal_bca_fair_labels]
        exact h_stays_correct (k₁ + j') (by omega)
    obtain ⟨j, hlbl, h_real_step⟩ := h_output h_output_inner
    have hpos : 0 + k₁ + j = k₁ + j := by omega
    rw [hpos] at hlbl h_real_step
    rw [← hlbl] at h_real_step
    simp only [IdealBCA.ideal_bca] at h_real_step
    obtain ⟨_, _, _, heq_s'⟩ := h_real_step
    have h_dec_set : (e.states (k₁ + j + 1)).decided p = some (some b) := by
      rw [heq_s']; simp
    exact absurd (h_ret_none (k₁ + j + 1) (by omega)) (by rw [h_dec_set]; simp)
  -- Per-proc-persist + finite-max wrapper.
  have h_per_proc_persist : ∀ p : Fin n, ∃ k'_p, k₁ ≤ k'_p ∧
      ∀ k', k'_p ≤ k' →
        (p ∉ (e.states k').corrupted → (e.states k').decided p ≠ none) := by
    intro p
    by_cases h_correct : ∀ k', k₁ ≤ k' → p ∉ (e.states k').corrupted
    · obtain ⟨k'_p, hk'_p, hret⟩ := h_per_proc p h_correct
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hret
      refine ⟨k'_p, hk'_p, fun k' hk' _ => ?_⟩
      have := IdealBCA.decided_persist_along_stutter hv_stutter hw k' hk'
      simp [this]
    · push_neg at h_correct
      obtain ⟨k₂, hk₂, hc⟩ := h_correct
      refine ⟨k₂, by omega, fun k' hk' hcorr => ?_⟩
      exact absurd (IdealBCA.corrupted_mem_persist_along_stutter hv_stutter hc k' hk') hcorr
  classical
  let k'_fn : Fin n → Nat := fun p => (h_per_proc_persist p).choose
  have hk'_spec : ∀ p, k₁ ≤ k'_fn p ∧
      ∀ k', k'_fn p ≤ k' →
        (p ∉ (e.states k').corrupted → (e.states k').decided p ≠ none) :=
    fun p => (h_per_proc_persist p).choose_spec
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

/-! ## Fair-label compatibility -/

/-- Concrete fair labels map to abstract fair labels via `label_map`.
    Used as `h_fair_compat` in `transfers_satisfaction`. -/
theorem bca_fair_compat (hn : n > 3 * f) :
    ∀ s₁ l₁ s₂,
      (BCA_Simulation.bca_forward_sim T n f hn).R s₁ s₂ →
      bca_fair_labels T n s₁ l₁ →
      ideal_bca_fair_labels T n s₂
        ((BCA_Simulation.bca_forward_sim T n f hn).label_map l₁) := by
  intro s₁ l₁ s₂ hR hfair
  have hcorr : s₂.corrupted = s₁.corrupted := hR.1
  match l₁ with
  | .corrupt _ => exact absurd hfair (by simp [bca_fair_labels])
  | .input _ _ => exact absurd hfair (by simp [bca_fair_labels])
  | .output p v =>
    simp only [BCA_Simulation.bca_forward_sim, BCA_Simulation.label_map,
               bca_fair_labels, ideal_bca_fair_labels] at hfair ⊢
    rw [hcorr]; exact hfair
  | .send _ _ _ _ =>
    simp [BCA_Simulation.bca_forward_sim, BCA_Simulation.label_map,
          ideal_bca_fair_labels]
  | .recv _ _ _ _ =>
    simp [BCA_Simulation.bca_forward_sim, BCA_Simulation.label_map,
          ideal_bca_fair_labels]

/-- The concrete-side decision property, lifted from
    `ideal_bca_decision_stutter` via `transfers_leads_to` applied to
    `bca_weak_div_witness`.

    **Precondition:** the concrete analog of `input_ready` — either
    some value has enough concrete-side support to cross the echo
    threshold (which maps to abstract inputSupport via sim_rel), or
    the abstract bound_value is already set. -/
theorem bca_decision (hn : n > 3 * f) :
    (BCA_LTS.bca T n f).satisfies
      (assumes_fair_wf
        (BCA_LTS.bca T n f)
        (bca_fair_labels T n)
        (leads_to
          (state_prop (fun s : BCA_LTS.State T n =>
            ∃ b, BCA_Simulation.echoSupport T n s b ≥ BCA_LTS.echoThreshold n f))
          (state_prop (fun s : BCA_LTS.State T n =>
            ∀ p, p ∉ s.corrupted → (s.local_ p).decided ≠ none)))) := by
  exact (bca_weak_div_witness T n f hn).transfers_leads_to
    -- h_label_ext: external labels preserved
    (fun l₁ hl₁ => by
      cases l₁ <;> simp_all [BCA_LTS.bca_labelling, Labelling.is_external,
        BCA_Simulation.label_map, IdealBCA.ideal_labelling,
        BCA_Simulation.bca_forward_sim])
    -- h_map_tau: tau maps to tau
    (by simp [BCA_Simulation.bca_forward_sim, BCA_Simulation.label_map,
        BCA_LTS.bca_labelling, IdealBCA.ideal_labelling])
    -- P_abs, Q_abs, P_con, Q_con
    (fun s => (∃ b, s.corrupted.length + IdealBCA.inputSupport T n s b ≥ f + 1) ∨
              s.bound_value ≠ none)
    (fun s => ∀ p, p ∉ s.corrupted → s.decided p ≠ none)
    (fun s => ∃ b, BCA_Simulation.echoSupport T n s b ≥ BCA_LTS.echoThreshold n f)
    (fun s => ∀ p, p ∉ s.corrupted → (s.local_ p).decided ≠ none)
    -- h_P: P_con → P_abs via sim_rel
    (fun s₁ s₂ hR hP => by
      obtain ⟨b, hsupp⟩ := hP
      -- echoSupport ≥ echoThreshold → sim_rel gives bound_value or voteContention
      -- Either way, bound_value ≠ none.
      right
      rcases hR.2.2.2.1 b hsupp with hbv | hvote
      · rw [hbv]; simp
      · exact hR.2.2.2.2.1 hvote)
    -- h_Q: Q_abs → Q_con via sim_rel
    (fun s₁ s₂ hR hQ p hp => by
      have hcorr : s₂.corrupted = s₁.corrupted := hR.1
      have hp' : p ∉ s₂.corrupted := hcorr ▸ hp
      have hdec := hR.2.2.1 p
      rw [← hdec]; exact hQ p hp')
    -- h_Q_step: Q_abs preserved by IdealBCA steps
    (fun s l s' hQ hstep => by
      intro p hp
      simp only [IdealBCA.ideal_bca] at hstep
      cases l with
      | corrupt i =>
        obtain ⟨_, _, heq⟩ := hstep
        subst heq; simp at hp; exact hQ p hp.2
      | input i v =>
        obtain ⟨_, heq⟩ := hstep; subst heq; exact hQ p hp
      | bind b =>
        obtain ⟨_, _, heq⟩ := hstep; subst heq; exact hQ p hp
      | output q v =>
        obtain ⟨_, _, _, heq⟩ := hstep; subst heq
        show (if p = q then some v else s.decided p) ≠ none
        split
        · simp
        · exact hQ p hp)
    -- h_abs: ideal_bca_decision_stutter
    (ideal_bca_decision_stutter T n f)
    -- h_ante_transfer: sorry (same structural issue as BRB)
    (fun e₁ e₂ idx hv₁ hv₂ idx_mono idx_zero h_idx_R h_fair_e1 => by
      intro l₂ k₂ h_always
      cases l₂ with
      | corrupt i =>
        exact absurd (h_always 0).2 (by simp [ideal_bca_fair_labels])
      | input i v =>
        exact absurd (h_always 0).2 (by simp [ideal_bca_fair_labels])
      | bind b =>
        sorry
      | output p v =>
        sorry)

end BCA_Liveness
