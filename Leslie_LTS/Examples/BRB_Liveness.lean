import Leslie_LTS.Framework
import Leslie_LTS.Examples.BrachaBRB
import Leslie_LTS.Examples.IdealBRB
import Leslie_LTS.Examples.BRB_Simulation

/-! # BRB Liveness: Fair-Weak-Divergence Witness and Lifted Totality

  This file instantiates `ForwardSim.WeakDivPreserving` for the existing
  `BRB_Simulation.brb_forward_sim` and uses `transfers_leads_to` to
  lift a fair-scheduling totality property from `IdealBRB` to the
  concrete Bracha BRB.

  ## Current state (2026-06-04)

  Framework (`Leslie_LTS/Framework/Simulation.lean`) is sorry-free.

  **Fully proven (zero sorries):**
  - `ideal_brb_totality` (Step A + Step B)
  - `ideal_brb_totality_stutter` (stutter-tolerant version)
  - `brb_fair_compat`
  - `brb_rank_wf` (trivially for placeholder measure)
  - `rank_decreases_on_unfair_abstract` (vacuous — all InternalStars AllFair)
  - `ideal_brb_internal_label_fair`, `ideal_brb_internalStar_allFair`
  - `brb_fair_deadlock_implies_terminated` FULLY proven
    (6-step chain: init→echo→vote→output, by contradiction)
  - `concrete_init_delivery`, `concrete_echo_delivery`,
    `concrete_vote_delivery`, `concrete_output_delivery`
    (temporal delivery chain building blocks)
  - `brb_totality_correct_sender` — the main concrete-level totality
    theorem, bypassing transfers_leads_to. Under fair scheduling with
    a correct sender, every correct process eventually returns.

  **Remaining sorries (6 in BRB_Liveness, 0 in BrachaBRB):**

  ```
  WeakDivPreserving witness (NOT used by transfers_leads_to — _wd unused):
    rank_non_increasing (sorry — placeholder measure; needs real measure)
    rank_decreases_on_fair_elision (sorry — same)
    rank_non_increasing_on_fair_progress (sorry — same)
    h_fair_reverse (sorry — see issues.md §3, corrupt-sender mismatch)

  brb_totality (via transfers_leads_to):
    h_ante_transfer / commit case (sorry — see issues.md §4-5)
    h_ante_transfer / output case (sorry — same root cause)
  ```

  **Note**: The 4 WeakDivPreserving sorries do NOT block `brb_totality`
  because `transfers_leads_to` takes `_wd` as an unused parameter (it only
  uses `h_abs`, `h_ante_transfer`, and the property callbacks). The only
  BLOCKING sorries are h_ante_transfer commit/output, which require the
  sender to be correct — a structural limitation of the simulation-based
  approach (see issues.md §4-5 for analysis and recommended fixes).

  **BrachaBRB.lean** is now sorry-free: all reachability invariants
  (init/echo/vote delivery, buffer-init-broadcastVal, sendRecv-value,
  echoed-value) are fully proven, along with auxiliary invariants
  sendRecv_none_of_broadcastVal_none and echoed_none_of_broadcastVal_none.

  ### Design issues (see `Leslie_LTS/issues.md` §3-5)

  - **h_fair_reverse** and **h_ante_transfer (commit)** are fundamentally
    blocked by the corrupt-sender fairness mismatch: in IdealBRB, commit
    is always fair, but the corresponding concrete init delivery from a
    corrupt sender involves only unfair steps. See issues.md §3-4.

  - **h_ante_transfer (output)** is ALSO blocked by the corrupt-sender
    issue: when sender is corrupt, initSupport ≥ echoThreshold does NOT
    guarantee enough correct sendRecvs for the echo chain to complete.
    With corrupted.length = f: |{correct with sendRecv}| ≥ n-2f, but
    echoThreshold = n-f > n-2f. See issues.md §5.

  - **brb_totality** antecedent narrowed to `broadcastVal ≠ none` only
    (dropped `¬ isCorrect sender`). The corrupt-sender case is unprovable
    at the concrete level.

  - **brb_fair_deadlock_implies_terminated** strengthened with a
    `sender ∉ corrupted` precondition (needed; statement is false when
    sender is corrupt and broadcastVal was set before corruption).
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

/-! ## BRB Protocol Reasoning Cheatsheet

    This section documents the BRB protocol's quorum structure and the
    delivery chain needed for the remaining protocol-specific sorries.
    For the full TLA-level proof, see
    `Leslie/Examples/ByzantineReliableBroadcast.lean` (lines 2333–3080).

    ### Protocol structure (Bracha BRB under n > 3f)

    The concrete BRB has 5 label types: `corrupt`, `input`, `send`,
    `recv`, `output`. Fair labels are `send`/`recv`/`output` where all
    involved processes are correct (not corrupted). `corrupt` and `input`
    are unfair (adversary/environment-controlled).

    ### Thresholds (from `BrachaBRB.lean`)

    * `echoThreshold n f = n - f`  (for echoing after receiving SEND)
    * `voteThreshold f = f + 1`    (for vote amplification)
    * `returnThreshold n f = n - f` (for returning/outputting)

    ### The delivery chain (from TLA-side `totality` proof)

    The TLA proof of totality (`ByzantineReliableBroadcast.lean:3008`)
    chains through these steps:

    1. **Vote backing:** if some process returned `v`, then ≥ `n-f`
       processes have `voted v = true` (invariant from safety proof).

    2. **Vote delivery to all receivers:** for each receiver `r`, each
       voting process `q` eventually sends `vote(v)` to `r` (WF on
       correct send), and the message is eventually delivered (WF on
       recv). After delivery, `r` has `voteRecv q v = true`.
       Combined: every receiver gets ≥ `f+1` vote receipts or the
       source gets corrupted.
       See `combine_vote_delivery_all_receivers` (line 2900).

    3. **Vote threshold delivery:** once `r` has `f+1` vote receipts,
       `r` itself votes and sends `vote(v)` to all (WF on send), then
       delivers to target (WF on recv). See
       `combine_vote_threshold_delivery` (line 2806).

    4. **Counting under n > 3f:** at most `f` processes are corrupt.
       Since ≥ `n-f` processes voted (step 1) and at most `f` got
       corrupted, ≥ `n-2f ≥ f+1` delivered votes reach `r`. After
       threshold delivery (step 3), `r` has ≥ `n-f` vote receipts.
       This is ≥ `returnThreshold`.

    5. **Return:** once `countVoteRecv ≥ returnThreshold`, `output(r,v)`
       is enabled. WF on output fires it. `returned r = some v`.
       See `wf_return` (line 2527).

    ### Fair WF applications (from TLA-side, lines 2333–2630)

    The TLA proof uses 4 core weak-fairness applications:

    * `wf_vote_send`: voted → send vote (WF on correct send action)
    * `wf_vote_threshold_send`: f+1 votes → send vote
    * `wf_return`: n-f votes → return (WF on doReturn action)
    * `wf_deliver`: message in buffer → received (WF on recv action)

    Each uses `wf1` (the TLA WF1 rule): show the action is enabled,
    fair, and that firing it makes progress (or some other action
    achieves the goal). In the LTS framework, these translate to
    applications of `h_ante` (the `assumes_fair_wf` antecedent) with
    the appropriate label.

    ### Key persistence lemmas (already proven for IdealBRB)

    For the concrete BRB, the same persistence facts hold but are NOT
    yet proven in `BrachaBRB.lean`. The TLA-side proofs are at:
    * `corrupt_persistent` (line 2027)
    * `voteRecv_persist` (line 2285)
    * `isCorrect_persist` (line 2298)
    * `countVoteRecv_persist` (line 2310)
    * `voted_persist` (line 2322)

    ### How this applies to the remaining sorries

    **brb_fair_deadlock_implies_terminated (line 164):**
    At a fair-deadlock, no fair step is enabled. For correct `p` with
    `returned = none`:
    * If `countVoteRecv p v ≥ returnThreshold`: then `output(p, v)` is
      enabled (preconditions: isCorrect p, returned = none,
      countVoteRecv ≥ threshold) and fair (p correct). Contradiction
      with FairDeadlock.
    * If `countVoteRecv p v < returnThreshold` for all v: then by the
      delivery chain (steps 1–4 above), some fair `recv` must be
      enabled somewhere (pending vote messages from correct senders).
      Or, if no fair recv is enabled, all vote messages have been
      delivered — but then countVoteRecv ≥ returnThreshold by counting
      (n > 3f ensures enough correct voters). Contradiction.

    The argument requires BRB invariants (vote backing, message
    integrity) which are proven in `BRB_Simulation.lean` as part of the
    safety proof. The key invariant: `initSupport` crossing the echo
    threshold implies enough correct processes have `sendRecv = some v`,
    which triggers the echo/vote chain.

    **h_fair_reverse (line 272):**
    Once `brb_fair_deadlock_implies_terminated` is proven, `h_fair_reverse`
    follows: at a terminated state, `sim_rel` gives us that the ideal
    state also has all `returned` set. In IdealBRB, `output(p, v)`
    requires `returned p = none` — so no output is enabled. And
    `commit(v)` requires `set_up = none` — but if everyone returned,
    `set_up` was already set (by the commit that happened earlier in the
    execution). So no fair ideal step is enabled → abstract fair-deadlock.
-/

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

    What IS true and useful: every reachable fair-deadlock where the
    sender has broadcast is terminated (all correct procs returned).
    The theorem is FALSE without the `broadcastVal ≠ none` precondition:
    the initial state (or any state after `corrupt(sender)` before input)
    is a fair-deadlock with `returned = none` for all procs.

    **Why broadcastVal ≠ none is sufficient:** if broadcastVal is set at a
    fair-deadlock, the init-send chain must have completed (otherwise some
    fair `send(sender, dst, init, v)` or `recv(sender, dst, init, v)`
    would be enabled for correct sender/dst). With all init recvs done,
    the echo chain must have completed (otherwise some fair echo
    send/recv would be enabled). Same for the vote chain. Finally,
    countVoteRecv ≥ returnThreshold for all correct procs with
    returned = none, making output enabled+fair — contradicting
    FairDeadlock.

    See `Leslie_LTS/issues.md` §3 for a detailed analysis of why the
    original (unconditional) statement was false. -/
/-- At a fair deadlock, no fair send between correct processes is enabled.
    That is, for correct src and correct dst, no send(src, dst, t, v) step
    exists with a successor state. -/
theorem fair_deadlock_no_fair_send
    (s : BRB_LTS.State n Value) (hfd : FairDeadlock (BRB_LTS.brb n f Value sender)
      (brb_fair_labels n Value) s)
    {src dst : Fin n} (hsrc : src ∉ s.corrupted) (hdst : dst ∉ s.corrupted)
    (t : BRB_LTS.MsgType) (v : Value) :
    ¬ ∃ s', (BRB_LTS.brb n f Value sender).step s (.send src dst t v) s' := by
  intro ⟨s', hstep⟩
  exact hfd (.send src dst t v) s' hstep ⟨hsrc, hdst⟩

/-- At a fair deadlock, no fair recv between correct processes is enabled. -/
theorem fair_deadlock_no_fair_recv
    (s : BRB_LTS.State n Value) (hfd : FairDeadlock (BRB_LTS.brb n f Value sender)
      (brb_fair_labels n Value) s)
    {src dst : Fin n} (hsrc : src ∉ s.corrupted) (hdst : dst ∉ s.corrupted)
    (t : BRB_LTS.MsgType) (v : Value) :
    ¬ ∃ s', (BRB_LTS.brb n f Value sender).step s (.recv src dst t v) s' := by
  intro ⟨s', hstep⟩
  exact hfd (.recv src dst t v) s' hstep ⟨hsrc, hdst⟩

/-- At a fair deadlock, no fair output is enabled. -/
theorem fair_deadlock_no_fair_output
    (s : BRB_LTS.State n Value) (hfd : FairDeadlock (BRB_LTS.brb n f Value sender)
      (brb_fair_labels n Value) s)
    {p : Fin n} (hp : p ∉ s.corrupted) (v : Value) :
    ¬ ∃ s', (BRB_LTS.brb n f Value sender).step s (.output p v) s' := by
  intro ⟨s', hstep⟩
  exact hfd (.output p v) s' hstep hp

/-- At a fair deadlock, a correct-to-correct message is NOT in the buffer.
    (If it were, recv would be enabled+fair, contradicting FairDeadlock.) -/
theorem fair_deadlock_no_fair_buffer
    (s : BRB_LTS.State n Value) (hfd : FairDeadlock (BRB_LTS.brb n f Value sender)
      (brb_fair_labels n Value) s)
    {src dst : Fin n} (hsrc : src ∉ s.corrupted) (hdst : dst ∉ s.corrupted)
    (t : BRB_LTS.MsgType) (v : Value) :
    s.buffer ⟨src, dst, t, v⟩ = false := by
  by_contra hbuf
  simp only [Bool.not_eq_false] at hbuf
  -- recv(src, dst, t, v) is enabled (buffer has the message).
  -- Construct the successor state explicitly from the recv definition.
  have : ∃ s', (BRB_LTS.brb n f Value sender).step s (.recv src dst t v) s' := by
    let ls := s.local_ dst
    let msg : BRB_LTS.Message n Value := ⟨src, dst, t, v⟩
    let ls' := match t with
      | .init => if src = sender ∧ ls.sendRecv = none
                 then { ls with sendRecv := some v } else ls
      | .echo => if ls.echoRecv src v = false
                 then { ls with echoRecv := fun q w =>
                   if q = src ∧ w = v then true else ls.echoRecv q w }
                 else ls
      | .vote => if ls.voteRecv src v = false
                 then { ls with voteRecv := fun q w =>
                   if q = src ∧ w = v then true else ls.voteRecv q w }
                 else ls
    exact ⟨{ s with
              buffer := fun m => if m = msg then false else s.buffer m
              local_ := fun p => if p = dst then ls' else s.local_ p },
           hbuf, rfl⟩
  obtain ⟨s', hstep⟩ := this
  exact hfd (.recv src dst t v) s' hstep ⟨hsrc, hdst⟩

theorem brb_fair_deadlock_implies_terminated (hn : n > 3 * f) :
    ∀ s, Reachable (BRB_LTS.brb n f Value sender) s →
      FairDeadlock (BRB_LTS.brb n f Value sender)
        (brb_fair_labels n Value) s →
      (s.local_ sender).broadcastVal ≠ none →
      sender ∉ s.corrupted →
      ∀ p, p ∉ s.corrupted → (s.local_ p).returned ≠ none := by
  -- Chain argument: at a fair deadlock with correct sender and broadcastVal set,
  -- the init→echo→vote→output delivery chain must have completed.
  -- Each unfinished link would provide a fair+enabled step, contradicting FairDeadlock.
  intro s hreach hfd hbv hcorr_sender p hp_corr
  -- Proof by contradiction: assume returned = none, derive output enabled+fair,
  -- contradicting FairDeadlock.
  by_contra h_ret_eq
  -- h_ret_eq : ¬ ((s.local_ p).returned ≠ none) i.e. returned = none
  have h_ret : (s.local_ p).returned = none := by tauto
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hbv
  -- Step 1: All correct dst have sendRecv = some v.
  -- For each correct dst: send(sender, dst, init, v) would be fair+enabled if not sent.
  -- So sent = true. Buffer = false (no fair buffer). By init_delivery_inv: sendRecv ≠ none.
  -- By sendRecv_value_inv: sendRecv = some v.
  have h_sendRecv : ∀ dst, dst ∉ s.corrupted → (s.local_ dst).sendRecv = some v := by
    intro dst hdst
    -- send(sender, dst, init, v) must have been sent
    by_contra h_not_v
    -- First show sent = true
    have h_sent : (s.local_ sender).sent dst .init v = true := by
      by_contra h_not_sent
      simp only [Bool.not_eq_true] at h_not_sent
      -- send(sender, dst, init, v) is enabled: correct sender, broadcastVal = some v, sent = false
      have h_enabled : ∃ s', (BRB_LTS.brb n f Value sender).step s (.send sender dst .init v) s' := by
        refine ⟨{ s with
          buffer := fun m => if m = ⟨sender, dst, .init, v⟩ then true else s.buffer m
          local_ := fun q => if q = sender then
            { s.local_ sender with
              sent := fun d t w => if d = dst ∧ t = .init ∧ w = v then true
                else (s.local_ sender).sent d t w }
            else s.local_ q }, ?_⟩
        simp only [BRB_LTS.brb]
        exact ⟨Or.inr ⟨hcorr_sender, h_not_sent, trivial, hv⟩, trivial⟩
      obtain ⟨s', hstep⟩ := h_enabled
      exact hfd (.send sender dst .init v) s' hstep ⟨hcorr_sender, hdst⟩
    -- Buffer = false for correct-to-correct
    have h_buf := fair_deadlock_no_fair_buffer n f Value sender s hfd hcorr_sender hdst .init v
    -- By init_delivery_inv: sendRecv ≠ none
    rcases BRB_LTS.init_delivery_inv s hreach dst v h_sent with hbuf | hsr
    · rw [hbuf] at h_buf; exact absurd h_buf (by simp)
    · -- sendRecv ≠ none → sendRecv = some w for some w → w = v
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hsr
      have := BRB_LTS.sendRecv_value_inv s hreach hcorr_sender hv dst w hw
      subst this; exact h_not_v hw
  -- Step 2: All correct q have sent echo(v) to all correct r, and echoRecv delivered.
  -- Each correct q has sendRecv = some v → echo condition met.
  -- send(q, r, echo, v) would be fair+enabled if not sent → contradiction. So sent = true.
  -- Buffer = false → by echo_delivery_inv: echoRecv r q v = true.
  have h_echoRecv : ∀ q r, q ∉ s.corrupted → r ∉ s.corrupted →
      (s.local_ r).echoRecv q v = true := by
    intro q r hq hr
    have h_sent : (s.local_ q).sent r .echo v = true := by
      by_contra h_not_sent
      simp only [Bool.not_eq_true] at h_not_sent
      -- Echo condition met: sendRecv = some v
      have hsrv := h_sendRecv q hq
      -- send(q, r, echo, v) is enabled: q correct, sent = false, echo condition met
      -- The echo condition: echoed = some v OR (echoed = none ∧ sendRecv = some v)
      -- If echoed = some v already, first disjunct. If echoed = none, second (sendRecv = some v).
      -- Either way, the send is enabled. Constructing the exact successor is mechanical.
      have h_enabled : ∃ s', (BRB_LTS.brb n f Value sender).step s (.send q r .echo v) s' := by
        let msg : BRB_LTS.Message n Value := ⟨q, r, .echo, v⟩
        refine ⟨{ s with
          buffer := fun m => if m = msg then true else s.buffer m
          local_ := fun p' => if p' = q then
            { s.local_ q with
              sent := fun d t w => if d = r ∧ t = .echo ∧ w = v then true
                else (s.local_ q).sent d t w
              echoed := if q ∉ s.corrupted then some v else (s.local_ q).echoed }
            else s.local_ p' }, ?_⟩
        simp only [BRB_LTS.brb]
        refine ⟨Or.inr ⟨hq, h_not_sent, ?_⟩, rfl⟩
        -- Echo condition: echoed = some v OR (echoed = none ∧ sendRecv = some v)
        rcases h_echoed : (s.local_ q).echoed with _ | w
        · exact Or.inr ⟨rfl, hsrv⟩
        · -- echoed = some w: need w = v. With correct sender, echoed can only be
          -- set to v (from sendRecv = some v). This requires an echoed-value invariant.
          have : w = v := BRB_LTS.echoed_value_inv s hreach hcorr_sender hv q hq w h_echoed
          exact Or.inl (this ▸ rfl)
      obtain ⟨s', hstep⟩ := h_enabled
      exact hfd (.send q r .echo v) s' hstep ⟨hq, hr⟩
    have h_buf := fair_deadlock_no_fair_buffer n f Value sender s hfd hq hr .echo v
    rcases BRB_LTS.echo_delivery_inv s hreach q r v h_sent with hbuf | hrecv
    · rw [hbuf] at h_buf; exact absurd h_buf (by simp)
    · exact hrecv
  -- Step 3: countEchoRecv ≥ echoThreshold for each correct r.
  -- echoRecv from all correct q ≥ n - |corrupted| ≥ n - f = echoThreshold.
  have h_echoCount : ∀ r, r ∉ s.corrupted →
      BRB_LTS.countEchoRecv n Value (s.local_ r) v ≥ BRB_LTS.echoThreshold n f := by
    intro r hr
    -- countEchoRecv ≥ n - |corrupted| ≥ n - f because echoRecv from all correct q.
    unfold BRB_LTS.countEchoRecv BRB_LTS.echoThreshold
    -- filter(echoRecv · v) includes all q ∉ corrupted
    have h1 : ((List.finRange n).filter (fun q => decide (q ∉ s.corrupted))).length ≤
        ((List.finRange n).filter ((s.local_ r).echoRecv · v)).length :=
      filter_length_mono _ _ _ (fun q hq => by
        simp only [decide_eq_true_eq] at hq; exact h_echoRecv q r hq hr)
    -- complement: |not-in-corrupted| + |in-corrupted| = n
    have h2 : ((List.finRange n).filter (fun q => decide (q ∉ s.corrupted))).length +
        ((List.finRange n).filter (fun q => decide (q ∈ s.corrupted))).length = n := by
      have key := (List.finRange n).length_eq_length_filter_add (fun q => decide (q ∈ s.corrupted))
      simp only [List.length_finRange] at key
      have : (List.filter (fun x => !decide (x ∈ s.corrupted)) (List.finRange n)) =
             (List.filter (fun x => decide (x ∉ s.corrupted)) (List.finRange n)) := by
        apply List.filter_congr; intro x _; simp
      rw [← this]; omega
    have h3 := filter_mem_le s.corrupted
    have h4 := BRB_Simulation.corrupted_budget hreach
    omega
  -- Step 4: All correct r have sent vote(v) to all correct r', and voteRecv delivered.
  have h_voteRecv : ∀ q r, q ∉ s.corrupted → r ∉ s.corrupted →
      (s.local_ r).voteRecv q v = true := by
    intro q r hq hr
    -- q has echoRecv count ≥ echoThreshold → vote condition met
    have hecho := h_echoCount q hq
    -- send(q, r, vote, v) must have completed (same pattern as echo)
    have h_sent : (s.local_ q).sent r .vote v = true := by
      by_contra h_not_sent
      simp only [Bool.not_eq_true] at h_not_sent
      -- vote send is enabled: echoRecv ≥ echoThreshold satisfies the vote condition
      have h_enabled : ∃ s', (BRB_LTS.brb n f Value sender).step s (.send q r .vote v) s' := by
        let msg : BRB_LTS.Message n Value := ⟨q, r, .vote, v⟩
        refine ⟨{ s with
          buffer := fun m => if m = msg then true else s.buffer m
          local_ := fun p' => if p' = q then
            { s.local_ q with
              sent := fun d t w => if d = r ∧ t = .vote ∧ w = v then true
                else (s.local_ q).sent d t w
              voted := if q ∉ s.corrupted
                then fun w => if w = v then true else (s.local_ q).voted w
                else (s.local_ q).voted }
            else s.local_ p' }, ?_⟩
        simp only [BRB_LTS.brb]
        refine ⟨Or.inr ⟨hq, h_not_sent, ?_⟩, rfl⟩
        -- Vote condition: voted ∨ echoRecv ≥ echoThreshold ∨ voteRecv ≥ voteThreshold
        exact Or.inr (Or.inl hecho)
      obtain ⟨s', hstep⟩ := h_enabled
      exact hfd (.send q r .vote v) s' hstep ⟨hq, hr⟩
    have h_buf := fair_deadlock_no_fair_buffer n f Value sender s hfd hq hr .vote v
    rcases BRB_LTS.vote_delivery_inv s hreach q r v h_sent with hbuf | hrecv
    · rw [hbuf] at h_buf; exact absurd h_buf (by simp)
    · exact hrecv
  -- Step 5: countVoteRecv p v ≥ returnThreshold.
  have h_voteCount :
      BRB_LTS.countVoteRecv n Value (s.local_ p) v ≥ BRB_LTS.returnThreshold n f := by
    -- Same counting argument as echoCount.
    unfold BRB_LTS.countVoteRecv BRB_LTS.returnThreshold
    have h1 : ((List.finRange n).filter (fun q => decide (q ∉ s.corrupted))).length ≤
        ((List.finRange n).filter ((s.local_ p).voteRecv · v)).length :=
      filter_length_mono _ _ _ (fun q hq => by
        simp only [decide_eq_true_eq] at hq; exact h_voteRecv q p hq hp_corr)
    have h2 : ((List.finRange n).filter (fun q => decide (q ∉ s.corrupted))).length +
        ((List.finRange n).filter (fun q => decide (q ∈ s.corrupted))).length = n := by
      have key := (List.finRange n).length_eq_length_filter_add (fun q => decide (q ∈ s.corrupted))
      simp only [List.length_finRange] at key
      have : (List.filter (fun x => !decide (x ∈ s.corrupted)) (List.finRange n)) =
             (List.filter (fun x => decide (x ∉ s.corrupted)) (List.finRange n)) := by
        apply List.filter_congr; intro x _; simp
      rw [← this]; omega
    have h3 := filter_mem_le s.corrupted
    have h4 := BRB_Simulation.corrupted_budget hreach
    omega
  -- Step 6: output(p, v) enabled + fair → contradiction.
  have h_output_enabled : ∃ s', (BRB_LTS.brb n f Value sender).step s (.output p v) s' := by
    refine ⟨{ s with local_ := fun q => if q = p then
        { s.local_ p with returned := some v } else s.local_ q }, ?_⟩
    simp only [BRB_LTS.brb]
    exact ⟨hp_corr, h_ret, h_voteCount, trivial⟩
  -- output(p, v) is fair: p ∉ corrupted
  obtain ⟨s', hstep⟩ := h_output_enabled
  exact hfd (.output p v) s' hstep hp_corr

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
    -- D.1 in plans/liveness-closure.md).
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

    Status (per plans/liveness-closure.md):
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
    obtain ⟨j, hj, h_step_kj⟩ := h_commit_always h_inner
    have hpos : 0 + k + j = k + j := by omega
    rw [hpos] at hj h_step_kj
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
    obtain ⟨j, hj, h_step_out⟩ := h_output_always h_output_inner
    have hpos : 0 + k₁ + j = k₁ + j := by omega
    rw [hpos] at hj h_step_out
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
  -- With assumes_fair_wf, h_ante gives "fires" = label match + real
  -- step. So the proof mirrors ideal_brb_totality exactly: wherever the
  -- non-stutter version uses `hv.2 k` to extract step structure, we use
  -- `h_ante`'s step component instead.
  --
  -- The proof is identical to ideal_brb_totality except we replace every
  -- `hv.2 (k+j)` with the step component from `h_ante`'s conclusion.
  -- Since `h_ante` gives `∃ j, l = e.labels (k+j) ∧ step at (k+j)`,
  -- the step is guaranteed at exactly the positions where we need it.
  --
  -- Rather than duplicating 200 LOC, we inline the key argument:
  intro k hA
  -- Step A: show eventually set_up ≠ none.
  have hStepA : ∃ k' ≥ k, (e.states k').set_up ≠ none := by
    by_contra h_never
    have h_none_forever : ∀ k', k' ≥ k → (e.states k').set_up = none := by
      intro k' hk'; by_contra hne; exact h_never ⟨k', hk', hne⟩
    -- Extract value and apply h_ante for commit.
    rcases hA with hbv | hcorrupt
    · -- Correct sender: broadcastVal ≠ none at 0 + k.
      obtain ⟨v₀, hv₀⟩ := Option.ne_none_iff_exists'.mp hbv
      have h_commit := h_ante (IdealBRB.Label.commit v₀) k
      have h_inner : ∀ j',
          (IdealBRB.ideal_brb n f Value sender).enabled
            (.commit v₀) (e.states (0 + k + j')) ∧
          ideal_brb_fair_labels n Value
            (e.states (0 + k + j')) (.commit v₀) := by
        intro j'
        constructor
        · refine ⟨{ (e.states (0 + k + j')) with set_up := some v₀ }, ?_⟩
          simp only [IdealBRB.ideal_brb]
          refine ⟨h_none_forever (0 + k + j') (by omega), ?_, by simp⟩
          -- OR condition: case-split on sender correctness at 0 + k + j'.
          by_cases hcorr_s : IdealBRB.isCorrect n Value (e.states (0 + k + j')) sender
          · -- Correct sender: broadcastVal persists from 0 + k.
            exact Or.inl ⟨hcorr_s,
              IdealBRB.broadcastVal_persist_along_stutter hv_stutter hv₀
                (0 + k + j') (by omega)⟩
          · exact Or.inr hcorr_s
        · simp [ideal_brb_fair_labels]
      obtain ⟨j, hlbl, h_real_step⟩ := h_commit h_inner
      -- h_real_step: real step at 0 + k + j. Extract set_up change.
      rw [← hlbl] at h_real_step
      simp only [IdealBRB.ideal_brb] at h_real_step
      obtain ⟨_, _, heq_s'⟩ := h_real_step
      have : (e.states (0 + k + j + 1)).set_up = some v₀ := by rw [heq_s']
      exact absurd (h_none_forever (0 + k + j + 1) (by omega)) (by rw [this]; simp)
    · -- Corrupt sender: same argument with default value.
      have h_commit := h_ante (IdealBRB.Label.commit (default : Value)) k
      have h_inner : ∀ j',
          (IdealBRB.ideal_brb n f Value sender).enabled
            (.commit default) (e.states (0 + k + j')) ∧
          ideal_brb_fair_labels n Value
            (e.states (0 + k + j')) (.commit default) := by
        intro j'
        constructor
        · refine ⟨{ (e.states (0 + k + j')) with set_up := some default }, ?_⟩
          simp only [IdealBRB.ideal_brb]
          refine ⟨h_none_forever (0 + k + j') (by omega), ?_, by simp⟩
          right
          simp only [IdealBRB.isCorrect] at hcorrupt ⊢
          push_neg at hcorrupt ⊢
          exact IdealBRB.corrupted_mem_persist_along_stutter hv_stutter
            hcorrupt (0 + k + j') (by omega)
        · simp [ideal_brb_fair_labels]
      obtain ⟨j, hlbl, h_real_step⟩ := h_commit h_inner
      rw [← hlbl] at h_real_step
      simp only [IdealBRB.ideal_brb] at h_real_step
      obtain ⟨_, _, heq_s'⟩ := h_real_step
      have : (e.states (0 + k + j + 1)).set_up = some default := by rw [heq_s']
      exact absurd (h_none_forever (0 + k + j + 1) (by omega)) (by rw [this]; simp)
  -- Step B: from set_up ≠ none, all correct procs eventually return.
  obtain ⟨k₁, hk₁_ge, hk₁_setup⟩ := hStepA
  obtain ⟨v, hv_setup⟩ := Option.ne_none_iff_exists'.mp hk₁_setup
  have h_setup_persist : ∀ k', k₁ ≤ k' → (e.states k').set_up = some v :=
    IdealBRB.set_up_persist_along_stutter hv_stutter hv_setup
  -- Per-proc: if p stays correct forever, output fires and returned persists.
  have h_per_proc : ∀ p : Fin n,
      (∀ k', k₁ ≤ k' → p ∉ (e.states k').corrupted) →
      ∃ k', k₁ ≤ k' ∧ (e.states k').returned p ≠ none := by
    intro p h_stays_correct
    by_contra h_never_ret
    have h_ret_none : ∀ k', k₁ ≤ k' → (e.states k').returned p = none := by
      intro k' hk'; by_contra hne; exact h_never_ret ⟨k', hk', hne⟩
    have h_output := h_ante (IdealBRB.Label.output p v) k₁
    have h_output_inner : ∀ j',
        (IdealBRB.ideal_brb n f Value sender).enabled
          (.output p v) (e.states (0 + k₁ + j')) ∧
        ideal_brb_fair_labels n Value
          (e.states (0 + k₁ + j')) (.output p v) := by
      intro j'
      constructor
      · refine ⟨{ (e.states (0 + k₁ + j')) with
                  returned := fun q => if q = p then some v
                    else (e.states (0 + k₁ + j')).returned q }, ?_⟩
        show (IdealBRB.ideal_brb n f Value sender).step _ (.output p v) _
        simp only [IdealBRB.ideal_brb]
        exact ⟨h_stays_correct (0 + k₁ + j') (by omega),
               h_ret_none (0 + k₁ + j') (by omega),
               h_setup_persist (0 + k₁ + j') (by omega), by simp⟩
      · simp only [ideal_brb_fair_labels]
        exact h_stays_correct (0 + k₁ + j') (by omega)
    obtain ⟨j, hlbl, h_real_step⟩ := h_output h_output_inner
    rw [← hlbl] at h_real_step
    simp only [IdealBRB.ideal_brb] at h_real_step
    obtain ⟨_, _, _, heq_s'⟩ := h_real_step
    have h_ret_set : (e.states (0 + k₁ + j + 1)).returned p = some v := by
      rw [heq_s']; simp
    exact absurd (h_ret_none (0 + k₁ + j + 1) (by omega))
      (by rw [h_ret_set]; simp)
  -- Per-proc-persist + finite-max wrapper (same as ideal_brb_totality).
  have h_per_proc_persist : ∀ p : Fin n, ∃ k'_p, k₁ ≤ k'_p ∧
      ∀ k', k'_p ≤ k' →
        (p ∉ (e.states k').corrupted → (e.states k').returned p ≠ none) := by
    intro p
    by_cases h_correct : ∀ k', k₁ ≤ k' → p ∉ (e.states k').corrupted
    · obtain ⟨k'_p, hk'_p, hret⟩ := h_per_proc p h_correct
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hret
      refine ⟨k'_p, hk'_p, fun k' hk' _ => ?_⟩
      have := IdealBRB.returned_persist_along_stutter hv_stutter hw k' hk'
      simp [this]
    · push_neg at h_correct
      obtain ⟨k₂, hk₂, hc⟩ := h_correct
      refine ⟨k₂, by omega, fun k' hk' hcorr => ?_⟩
      exact absurd (IdealBRB.corrupted_mem_persist_along_stutter hv_stutter hc k' hk') hcorr
  classical
  let k'_fn : Fin n → Nat := fun p => (h_per_proc_persist p).choose
  have hk'_spec : ∀ p, k₁ ≤ k'_fn p ∧
      ∀ k', k'_fn p ≤ k' →
        (p ∉ (e.states k').corrupted → (e.states k').returned p ≠ none) :=
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

/-- The concrete-side totality: under fair scheduling, once the sender
    has broadcast, every correct process eventually returns.

    **Antecedent**: `broadcastVal ≠ none` only (not the stronger
    `broadcastVal ≠ none ∨ ¬ isCorrect sender`).  The corrupt-sender
    case is NOT provable at the concrete level: when the sender is
    corrupt, all init sends/recvs involving the corrupt sender are
    unfair, so the concrete fair-WF provides no delivery guarantee.
    This matches the standard BRB specification: totality is only
    guaranteed for correct senders.

    **Proof approach**: uses `transfers_leads_to` with the ideal
    `ideal_brb_totality_stutter` as `h_abs`.  The `h_ante_transfer`
    obligation (lifting concrete fair-WF to abstract fair-WF) requires
    showing that every perpetually-enabled-and-fair abstract label
    eventually fires; see `Leslie_LTS/issues.md` §4 for the proof
    strategy and known difficulties. -/
theorem brb_totality (hn : n > 3 * f) :
    (BRB_LTS.brb n f Value sender).satisfies
      (assumes_fair_wf
        (BRB_LTS.brb n f Value sender)
        (brb_fair_labels n Value)
        (leads_to
          (state_prop (fun s : BRB_LTS.State n Value =>
            (s.local_ sender).broadcastVal ≠ none))
          (state_prop (fun s : BRB_LTS.State n Value =>
            ∀ p, p ∉ s.corrupted → (s.local_ p).returned ≠ none)))) := by
  -- Apply transfers_leads_to with brb_weak_div_witness + ideal_brb_totality_stutter.
  -- The ideal-side antecedent (broadcastVal ≠ none ∨ ¬ isCorrect sender) is
  -- STRONGER than the concrete-side antecedent (broadcastVal ≠ none), so the
  -- h_P transfer is straightforward.
  let sim := BRB_Simulation.brb_forward_sim n f Value sender hn
  exact (brb_weak_div_witness n f Value sender hn).transfers_leads_to
    -- h_label_ext: external labels preserved
    (fun l₁ hl₁ => by
      cases l₁ <;> simp_all [BRB_LTS.brb_labelling, Labelling.is_external,
        BRB_Simulation.label_map, IdealBRB.ideal_labelling,
        BRB_Simulation.brb_forward_sim])
    -- h_map_tau: tau maps to tau
    (by simp [BRB_Simulation.brb_forward_sim, BRB_Simulation.label_map,
        BRB_LTS.brb_labelling, IdealBRB.ideal_labelling])
    -- P_abs, Q_abs, P_con, Q_con
    (fun s => s.broadcastVal ≠ none ∨ ¬ IdealBRB.isCorrect n Value s sender)
    (fun s => ∀ p, p ∉ s.corrupted → s.returned p ≠ none)
    (fun s => (s.local_ sender).broadcastVal ≠ none)
    (fun s => ∀ p, p ∉ s.corrupted → (s.local_ p).returned ≠ none)
    -- h_P: P_con → P_abs via sim_rel (broadcastVal ≠ none → left disjunct)
    (fun s₁ s₂ hR hP => by
      have hbv : s₂.broadcastVal = (s₁.local_ sender).broadcastVal := hR.2.1
      exact Or.inl (hbv ▸ hP))
    -- h_Q: Q_abs → Q_con via sim_rel
    (fun s₁ s₂ hR hQ p hp => by
      have hcorr : s₂.corrupted = s₁.corrupted := hR.1
      have hp' : p ∉ s₂.corrupted := hcorr ▸ hp
      have hret := hR.2.2.1 p (by simp [BRB_LTS.isCorrect]; exact hp)
      rw [← hret]; exact hQ p hp')
    -- h_Q_step: Q_abs preserved by IdealBRB steps
    (fun s l s' hQ hstep => by
      intro p hp
      simp only [IdealBRB.ideal_brb] at hstep
      cases l with
      | corrupt i =>
        obtain ⟨_, _, heq⟩ := hstep
        subst heq; simp at hp; exact hQ p hp.2
      | input i v =>
        obtain ⟨_, _, heq⟩ := hstep; subst heq; exact hQ p hp
      | commit v =>
        obtain ⟨_, _, heq⟩ := hstep; subst heq; exact hQ p hp
      | output q v =>
        obtain ⟨_, _, _, heq⟩ := hstep; subst heq
        show (if p = q then some v else s.returned p) ≠ none
        split
        · simp
        · exact hQ p hp)
    -- h_abs: ideal_brb_totality_stutter
    (ideal_brb_totality_stutter n f Value sender)
    -- h_ante_transfer: lift concrete fair-WF to abstract step-aware fair-WF
    -- See Leslie_LTS/issues.md §4 for analysis. The commit case is the
    -- main difficulty: with a corrupt sender, abstract commit is always
    -- enabled+fair but can't fire (no concrete fair step causes the
    -- threshold crossing). The output case requires the BRB delivery chain.
    (fun e₁ e₂ idx hv₁ hv₂ idx_mono idx_zero h_idx_R h_fair_e1 => by
      -- Case-split on abstract label l₂.
      -- corrupt/input: fair_labels = False, so antecedent is impossible.
      -- commit/output: protocol-specific; sorried pending delivery chain.
      intro l₂ k₂ h_always
      cases l₂ with
      | corrupt i =>
        -- ideal_brb_fair_labels (.corrupt i) = False
        exact absurd (h_always 0).2 (by simp [ideal_brb_fair_labels])
      | input i v =>
        -- ideal_brb_fair_labels (.input i v) = False
        exact absurd (h_always 0).2 (by simp [ideal_brb_fair_labels])
      | commit v =>
        -- commit is always fair (True). Enabled means set_up = none ∧
        -- OR condition. If sender is correct with broadcastVal ≠ none,
        -- the concrete fair-WF drives init delivery → initSupport crosses
        -- echoThreshold → commit fires in e₂ → contradiction with
        -- "always enabled". If sender is corrupt, this is unprovable
        -- (see issues.md §4).
        sorry
      | output p v =>
        -- output p v is fair when p ∉ corrupted. Enabled means
        -- set_up = some v ∧ returned p = none ∧ p ∉ corrupted.
        -- The BRB delivery chain (echo → vote → output) under fair
        -- scheduling eventually makes countVoteRecv ≥ returnThreshold,
        -- at which point concrete output fires → abstract output fires
        -- → contradiction with "always enabled" (returned p becomes
        -- some v ≠ none).
        sorry)

/-! ## Concrete-level delivery chain building blocks

    These lemmas support a direct proof of BRB totality without
    `transfers_leads_to`. Each lemma chains one step of the BRB delivery
    (init → echo → vote → output) using the concrete fair-WF.

    Convention: each lemma takes a valid execution, fair-WF antecedent
    (`h_ante`), and position `k` where the precondition holds. It produces
    a position `k' ≥ k` where the postcondition holds.

    The fair-WF antecedent is:
    ```
    h_ante : ∀ l, ∀ k, (∀ j, enabled l (e.states (k + j)) ∧ fair l (e.states (k + j))) →
               ∃ j, l = e.labels (k + j) ∧ step (e.states (k + j)) l (e.states (k + j + 1))
    ```
    This is exactly the `assumes_fair_wf` antecedent from the framework. -/

/-- **Init delivery**: if broadcastVal = some v and sender always correct,
    then eventually sendRecv(dst) = some v (or dst gets corrupted).

    Uses fair-WF antecedent to fire send then recv. -/
theorem concrete_init_delivery
    {e : Execution (BRB_LTS.State n Value) (BRB_LTS.Label n Value)}
    (hv : (BRB_LTS.brb n f Value sender).valid_exec e)
    (h_ante : ∀ (l : BRB_LTS.Label n Value) (k : Nat),
        (∀ j, (BRB_LTS.brb n f Value sender).enabled l (e.states (k + j)) ∧
          brb_fair_labels n Value (e.states (k + j)) l) →
        ∃ j, l = e.labels (k + j) ∧
          (BRB_LTS.brb n f Value sender).step
            (e.states (k + j)) (e.labels (k + j)) (e.states (k + j + 1)))
    (k : Nat)
    (dst : Fin n)
    (hbv : ((e.states k).local_ sender).broadcastVal = some v)
    (hcorr_s : ∀ k', k ≤ k' → sender ∉ (e.states k').corrupted)
    (hcorr_d : dst ∉ (e.states k).corrupted) :
    ∃ k', k ≤ k' ∧ (((e.states k').local_ dst).sendRecv = some v ∨
      dst ∈ (e.states k').corrupted) := by
  by_contra h_never
  push_neg at h_never
  -- h_never : ∀ k' ≥ k, sendRecv ≠ some v ∧ dst ∉ corrupted
  -- By sendRecv_value_inv, sendRecv can only be some v, so sendRecv = none forever.
  have h_sr_none : ∀ k', k ≤ k' → ((e.states k').local_ dst).sendRecv = none := by
    intro k' hk'
    have ⟨hne, _⟩ := h_never k' hk'
    by_contra h_nn
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp h_nn
    have := BRB_LTS.sendRecv_value_inv (e.states k') (System.valid_exec_reachable hv k')
      (hcorr_s k' hk') (BRB_LTS.broadcastVal_persist_along hv hbv k' hk') dst w hw
    exact hne (this ▸ hw)
  -- Phase 1: sent(sender, dst, init, v) = true eventually.
  have h_sent : ∃ k₁, k ≤ k₁ ∧
      ((e.states k₁).local_ sender).sent dst .init v = true := by
    by_contra h_not
    push_neg at h_not
    -- sent ≠ true at all k' ≥ k
    have hsf : ∀ k', k ≤ k' →
        ((e.states k').local_ sender).sent dst .init v = false := by
      intro k' hk'
      have := h_not k' hk'
      simpa using this
    -- send(sender, dst, init, v) always enabled+fair from k
    have h_inner : ∀ j, (BRB_LTS.brb n f Value sender).enabled
        (.send sender dst .init v) (e.states (k + j)) ∧
        brb_fair_labels n Value (e.states (k + j)) (.send sender dst .init v) := by
      intro j
      constructor
      · refine ⟨{ (e.states (k + j)) with
          buffer := fun m => if m = ⟨sender, dst, .init, v⟩ then true
            else (e.states (k + j)).buffer m
          local_ := fun p => if p = sender then
            { (e.states (k + j)).local_ sender with
              sent := fun d t w => if d = dst ∧ t = .init ∧ w = v then true
                else ((e.states (k + j)).local_ sender).sent d t w }
            else (e.states (k + j)).local_ p }, ?_⟩
        simp only [BRB_LTS.brb]
        exact ⟨Or.inr ⟨hcorr_s (k + j) (by omega), hsf (k + j) (by omega),
          trivial, BRB_LTS.broadcastVal_persist_along hv hbv (k + j) (by omega)⟩, trivial⟩
      · exact ⟨hcorr_s (k + j) (by omega), (h_never (k + j) (by omega)).2⟩
    obtain ⟨j, hlbl, hstep⟩ := h_ante _ k h_inner
    rw [← hlbl] at hstep
    simp only [BRB_LTS.brb] at hstep
    obtain ⟨_, h_eq⟩ := hstep
    have : ((e.states (k + j + 1)).local_ sender).sent dst .init v = true := by
      rw [h_eq]; simp
    exact h_not (k + j + 1) (by omega) this
  obtain ⟨k₁, hk₁, h_sent_true⟩ := h_sent
  -- Phase 2: buffer(sender,dst,init,v) = true at all k' ≥ k₁ (via init_delivery_inv + sendRecv = none).
  have h_buf : ∀ k', k₁ ≤ k' →
      (e.states k').buffer ⟨sender, dst, .init, v⟩ = true := by
    intro k' hk'
    have h_sent' := BRB_LTS.sent_persist_along hv h_sent_true k' hk'
    rcases BRB_LTS.init_delivery_inv (e.states k') (System.valid_exec_reachable hv k')
      dst v h_sent' with hbuf | hsr
    · exact hbuf
    · exact absurd (h_sr_none k' (by omega)) hsr
  -- recv(sender, dst, init, v) always enabled+fair from k₁
  have h_recv_inner : ∀ j, (BRB_LTS.brb n f Value sender).enabled
      (.recv sender dst .init v) (e.states (k₁ + j)) ∧
      brb_fair_labels n Value (e.states (k₁ + j)) (.recv sender dst .init v) := by
    intro j
    constructor
    · exact ⟨_, h_buf (k₁ + j) (by omega), rfl⟩
    · exact ⟨hcorr_s (k₁ + j) (by omega), (h_never (k₁ + j) (by omega)).2⟩
  obtain ⟨j, hlbl, hstep⟩ := h_ante _ k₁ h_recv_inner
  rw [← hlbl] at hstep
  simp only [BRB_LTS.brb] at hstep
  obtain ⟨_, h_eq⟩ := hstep
  -- At k₁+j+1: sendRecv was none → recv sets it to some v → contradiction.
  have h_sr := h_sr_none (k₁ + j) (by omega)
  have : ((e.states (k₁ + j + 1)).local_ dst).sendRecv = some v := by
    rw [h_eq]; simp [h_sr]
  exact (h_never (k₁ + j + 1) (by omega)).1 this

/-- **Echo delivery**: if src has sendRecv = some v (echo condition met),
    src stays correct, then eventually echoRecv(dst, src, v) = true or dst corrupted. -/
theorem concrete_echo_delivery
    {e : Execution (BRB_LTS.State n Value) (BRB_LTS.Label n Value)}
    (hv : (BRB_LTS.brb n f Value sender).valid_exec e)
    (h_ante : ∀ (l : BRB_LTS.Label n Value) (k : Nat),
        (∀ j, (BRB_LTS.brb n f Value sender).enabled l (e.states (k + j)) ∧
          brb_fair_labels n Value (e.states (k + j)) l) →
        ∃ j, l = e.labels (k + j) ∧
          (BRB_LTS.brb n f Value sender).step
            (e.states (k + j)) (e.labels (k + j)) (e.states (k + j + 1)))
    (k : Nat)
    (src dst : Fin n)
    (hsr : ((e.states k).local_ src).sendRecv = some v)
    (hcorr_sender : ∀ k', k ≤ k' → sender ∉ (e.states k').corrupted)
    (hbv : ((e.states k).local_ sender).broadcastVal = some v)
    (hcorr_src : ∀ k', k ≤ k' → src ∉ (e.states k').corrupted)
    (hcorr_dst : dst ∉ (e.states k).corrupted) :
    ∃ k', k ≤ k' ∧ (((e.states k').local_ dst).echoRecv src v = true ∨
      dst ∈ (e.states k').corrupted) := by
  by_contra h_never
  push_neg at h_never
  have h_er_false : ∀ k', k ≤ k' →
      ((e.states k').local_ dst).echoRecv src v = false := by
    intro k' hk'; simpa using (h_never k' hk').1
  -- Phase 1: sent(src, dst, echo, v) = true eventually.
  have h_sent : ∃ k₁, k ≤ k₁ ∧
      ((e.states k₁).local_ src).sent dst .echo v = true := by
    by_contra h_not
    push_neg at h_not
    have hsf : ∀ k', k ≤ k' →
        ((e.states k').local_ src).sent dst .echo v = false := by
      intro k' hk'; simpa using h_not k' hk'
    have h_inner : ∀ j, (BRB_LTS.brb n f Value sender).enabled
        (.send src dst .echo v) (e.states (k + j)) ∧
        brb_fair_labels n Value (e.states (k + j)) (.send src dst .echo v) := by
      intro j
      constructor
      · -- enabled: echo condition met via sendRecv = some v
        have hsr' := BRB_LTS.sendRecv_persist_along hv hsr (k + j) (by omega)
        -- echoed: either some v (first disjunct) or none (second disjunct with sendRecv)
        have h_echo_cond : ((e.states (k + j)).local_ src).echoed = some v ∨
            (((e.states (k + j)).local_ src).echoed = none ∧
             ((e.states (k + j)).local_ src).sendRecv = some v) := by
          rcases h_echoed : ((e.states (k + j)).local_ src).echoed with _ | w
          · exact Or.inr ⟨rfl, hsr'⟩
          · have hval := BRB_LTS.echoed_value_inv (e.states (k + j))
              (System.valid_exec_reachable hv (k + j))
              (hcorr_sender (k + j) (by omega))
              (BRB_LTS.broadcastVal_persist_along hv hbv (k + j) (by omega))
              src (hcorr_src (k + j) (by omega)) w h_echoed
            exact Or.inl (congrArg some hval)
        refine ⟨{ (e.states (k + j)) with
          buffer := fun m => if m = ⟨src, dst, .echo, v⟩ then true
            else (e.states (k + j)).buffer m
          local_ := fun p => if p = src then
            { (e.states (k + j)).local_ src with
              sent := fun d t w => if d = dst ∧ t = .echo ∧ w = v then true
                else ((e.states (k + j)).local_ src).sent d t w
              echoed := if src ∉ (e.states (k + j)).corrupted then some v
                        else ((e.states (k + j)).local_ src).echoed }
            else (e.states (k + j)).local_ p }, ?_⟩
        simp only [BRB_LTS.brb]
        exact ⟨Or.inr ⟨hcorr_src (k + j) (by omega), hsf (k + j) (by omega),
          h_echo_cond⟩, trivial⟩
      · exact ⟨hcorr_src (k + j) (by omega), (h_never (k + j) (by omega)).2⟩
    obtain ⟨j, hlbl, hstep⟩ := h_ante _ k h_inner
    rw [← hlbl] at hstep; simp only [BRB_LTS.brb] at hstep
    obtain ⟨_, h_eq⟩ := hstep
    have : ((e.states (k + j + 1)).local_ src).sent dst .echo v = true := by
      rw [h_eq]; simp
    exact h_not (k + j + 1) (by omega) this
  obtain ⟨k₁, hk₁, h_sent_true⟩ := h_sent
  -- Phase 2: buffer stays true → recv fires.
  have h_buf : ∀ k', k₁ ≤ k' →
      (e.states k').buffer ⟨src, dst, .echo, v⟩ = true := by
    intro k' hk'
    have h_sent' := BRB_LTS.sent_persist_along hv h_sent_true k' hk'
    rcases BRB_LTS.echo_delivery_inv (e.states k') (System.valid_exec_reachable hv k')
      src dst v h_sent' with hbuf | hrecv
    · exact hbuf
    · exact absurd hrecv (by simp [h_er_false k' (by omega)])
  have h_recv_inner : ∀ j, (BRB_LTS.brb n f Value sender).enabled
      (.recv src dst .echo v) (e.states (k₁ + j)) ∧
      brb_fair_labels n Value (e.states (k₁ + j)) (.recv src dst .echo v) := by
    intro j
    constructor
    · exact ⟨_, h_buf (k₁ + j) (by omega), rfl⟩
    · exact ⟨hcorr_src (k₁ + j) (by omega), (h_never (k₁ + j) (by omega)).2⟩
  obtain ⟨j, hlbl, hstep⟩ := h_ante _ k₁ h_recv_inner
  rw [← hlbl] at hstep; simp only [BRB_LTS.brb] at hstep
  obtain ⟨_, h_eq⟩ := hstep
  have h_false := h_er_false (k₁ + j) (by omega)
  have : ((e.states (k₁ + j + 1)).local_ dst).echoRecv src v = true := by
    rw [h_eq]; simp [h_false]
  exact (h_never (k₁ + j + 1) (by omega)).1 (by simpa using this)

/-- **Vote delivery**: if src has the vote condition (countEchoRecv ≥ echoThreshold),
    src stays correct, then eventually voteRecv(dst, src, v) = true or dst corrupted. -/
theorem concrete_vote_delivery
    {e : Execution (BRB_LTS.State n Value) (BRB_LTS.Label n Value)}
    (hv : (BRB_LTS.brb n f Value sender).valid_exec e)
    (h_ante : ∀ (l : BRB_LTS.Label n Value) (k : Nat),
        (∀ j, (BRB_LTS.brb n f Value sender).enabled l (e.states (k + j)) ∧
          brb_fair_labels n Value (e.states (k + j)) l) →
        ∃ j, l = e.labels (k + j) ∧
          (BRB_LTS.brb n f Value sender).step
            (e.states (k + j)) (e.labels (k + j)) (e.states (k + j + 1)))
    (k : Nat)
    (src dst : Fin n)
    (hecho : BRB_LTS.countEchoRecv n Value ((e.states k).local_ src) v ≥
             BRB_LTS.echoThreshold n f)
    (hcorr_src : ∀ k', k ≤ k' → src ∉ (e.states k').corrupted)
    (hcorr_dst : dst ∉ (e.states k).corrupted) :
    ∃ k', k ≤ k' ∧ (((e.states k').local_ dst).voteRecv src v = true ∨
      dst ∈ (e.states k').corrupted) := by
  by_contra h_never
  push_neg at h_never
  have h_vr_false : ∀ k', k ≤ k' →
      ((e.states k').local_ dst).voteRecv src v = false := by
    intro k' hk'; simpa using (h_never k' hk').1
  -- Phase 1: sent(src, dst, vote, v) = true eventually.
  have h_sent : ∃ k₁, k ≤ k₁ ∧
      ((e.states k₁).local_ src).sent dst .vote v = true := by
    by_contra h_not
    push_neg at h_not
    have hsf : ∀ k', k ≤ k' →
        ((e.states k').local_ src).sent dst .vote v = false := by
      intro k' hk'; simpa using h_not k' hk'
    have h_inner : ∀ j, (BRB_LTS.brb n f Value sender).enabled
        (.send src dst .vote v) (e.states (k + j)) ∧
        brb_fair_labels n Value (e.states (k + j)) (.send src dst .vote v) := by
      intro j
      constructor
      · -- enabled: vote condition met via countEchoRecv ≥ echoThreshold (monotone)
        have h_echo' : BRB_LTS.countEchoRecv n Value
            ((e.states (k + j)).local_ src) v ≥ BRB_LTS.echoThreshold n f := by
          exact Nat.le_trans hecho (by
            induction j with
            | zero => exact Nat.le_refl _
            | succ j ih =>
              exact Nat.le_trans ih (BRB_LTS.step_countEchoRecv_mono (hv.2 (k + j)) src v))
        refine ⟨{ (e.states (k + j)) with
          buffer := fun m => if m = ⟨src, dst, .vote, v⟩ then true
            else (e.states (k + j)).buffer m
          local_ := fun p => if p = src then
            { (e.states (k + j)).local_ src with
              sent := fun d t w => if d = dst ∧ t = .vote ∧ w = v then true
                else ((e.states (k + j)).local_ src).sent d t w
              voted := if src ∉ (e.states (k + j)).corrupted
                then fun w => if w = v then true
                  else ((e.states (k + j)).local_ src).voted w
                else ((e.states (k + j)).local_ src).voted }
            else (e.states (k + j)).local_ p }, ?_⟩
        simp only [BRB_LTS.brb]
        exact ⟨Or.inr ⟨hcorr_src (k + j) (by omega), hsf (k + j) (by omega),
          Or.inr (Or.inl h_echo')⟩, trivial⟩
      · exact ⟨hcorr_src (k + j) (by omega), (h_never (k + j) (by omega)).2⟩
    obtain ⟨j, hlbl, hstep⟩ := h_ante _ k h_inner
    rw [← hlbl] at hstep; simp only [BRB_LTS.brb] at hstep
    obtain ⟨_, h_eq⟩ := hstep
    have : ((e.states (k + j + 1)).local_ src).sent dst .vote v = true := by
      rw [h_eq]; simp
    exact h_not (k + j + 1) (by omega) this
  obtain ⟨k₁, hk₁, h_sent_true⟩ := h_sent
  -- Phase 2: buffer stays true → recv fires.
  have h_buf : ∀ k', k₁ ≤ k' →
      (e.states k').buffer ⟨src, dst, .vote, v⟩ = true := by
    intro k' hk'
    have h_sent' := BRB_LTS.sent_persist_along hv h_sent_true k' hk'
    rcases BRB_LTS.vote_delivery_inv (e.states k') (System.valid_exec_reachable hv k')
      src dst v h_sent' with hbuf | hrecv
    · exact hbuf
    · exact absurd hrecv (by simp [h_vr_false k' (by omega)])
  have h_recv_inner : ∀ j, (BRB_LTS.brb n f Value sender).enabled
      (.recv src dst .vote v) (e.states (k₁ + j)) ∧
      brb_fair_labels n Value (e.states (k₁ + j)) (.recv src dst .vote v) := by
    intro j
    constructor
    · exact ⟨_, h_buf (k₁ + j) (by omega), rfl⟩
    · exact ⟨hcorr_src (k₁ + j) (by omega), (h_never (k₁ + j) (by omega)).2⟩
  obtain ⟨j, hlbl, hstep⟩ := h_ante _ k₁ h_recv_inner
  rw [← hlbl] at hstep; simp only [BRB_LTS.brb] at hstep
  obtain ⟨_, h_eq⟩ := hstep
  have h_false := h_vr_false (k₁ + j) (by omega)
  have : ((e.states (k₁ + j + 1)).local_ dst).voteRecv src v = true := by
    rw [h_eq]; simp [h_false]
  exact (h_never (k₁ + j + 1) (by omega)).1 (by simpa using this)

/-- **Output delivery**: if p has countVoteRecv ≥ returnThreshold and returned = none,
    p correct, then eventually returned(p) ≠ none or p corrupted. -/
theorem concrete_output_delivery
    {e : Execution (BRB_LTS.State n Value) (BRB_LTS.Label n Value)}
    (hv : (BRB_LTS.brb n f Value sender).valid_exec e)
    (h_ante : ∀ (l : BRB_LTS.Label n Value) (k : Nat),
        (∀ j, (BRB_LTS.brb n f Value sender).enabled l (e.states (k + j)) ∧
          brb_fair_labels n Value (e.states (k + j)) l) →
        ∃ j, l = e.labels (k + j) ∧
          (BRB_LTS.brb n f Value sender).step
            (e.states (k + j)) (e.labels (k + j)) (e.states (k + j + 1)))
    (k : Nat) (p : Fin n)
    (hvote : BRB_LTS.countVoteRecv n Value ((e.states k).local_ p) v ≥
             BRB_LTS.returnThreshold n f)
    (hcorr_p : ∀ k', k ≤ k' → p ∉ (e.states k').corrupted) :
    ∃ k', k ≤ k' ∧ ((e.states k').local_ p).returned ≠ none := by
  by_contra h_never
  push_neg at h_never
  -- h_never : ∀ k', k ≤ k' → returned = none
  -- output(p, v) is always enabled+fair from k.
  have h_inner : ∀ j, (BRB_LTS.brb n f Value sender).enabled
      (.output p v) (e.states (k + j)) ∧
      brb_fair_labels n Value (e.states (k + j)) (.output p v) := by
    intro j
    constructor
    · -- enabled: p correct, returned = none, countVoteRecv ≥ returnThreshold (monotone)
      have h_vote' : BRB_LTS.countVoteRecv n Value
          ((e.states (k + j)).local_ p) v ≥ BRB_LTS.returnThreshold n f :=
        Nat.le_trans hvote (BRB_LTS.countVoteRecv_mono_along hv p v k (k + j) (by omega))
      refine ⟨{ (e.states (k + j)) with
        local_ := fun q => if q = p then
          { (e.states (k + j)).local_ p with returned := some v }
          else (e.states (k + j)).local_ q }, ?_⟩
      simp only [BRB_LTS.brb]
      exact ⟨hcorr_p (k + j) (by omega), h_never (k + j) (by omega), h_vote', trivial⟩
    · exact hcorr_p (k + j) (by omega)
  obtain ⟨j, hlbl, hstep⟩ := h_ante _ k h_inner
  rw [← hlbl] at hstep; simp only [BRB_LTS.brb] at hstep
  obtain ⟨_, _, _, h_eq⟩ := hstep
  have : ((e.states (k + j + 1)).local_ p).returned = some v := by
    rw [h_eq]; simp
  exact absurd (h_never (k + j + 1) (by omega)) (by rw [this]; simp)

/-- Variant of `brb_totality` with an explicit sender-correctness assumption.
    This version IS provable (unlike the unrestricted version which is blocked
    by the corrupt-sender fairness mismatch — see issues.md §4-5).

    **Statement**: For every valid execution where sender is never corrupted,
    under fair scheduling, once broadcastVal is set, every correct process
    eventually returns.

    **Status**: Work in progress. The h_ante_transfer commit and output cases
    become provable with sender-correctness because:
    - Commit: correct sender → all correct dst eventually get sendRecv = some v
      via fair init send/recv → initSupport crosses echoThreshold → commit fires
    - Output: correct sender → echo/vote delivery chain completes under fair
      scheduling → countVoteRecv ≥ returnThreshold → output fires -/
theorem brb_totality_correct_sender (hn : n > 3 * f) :
    ∀ (e : Execution (BRB_LTS.State n Value) (BRB_LTS.Label n Value)),
      (BRB_LTS.brb n f Value sender).valid_exec e →
      (∀ j, sender ∉ (e.states j).corrupted) →
      assumes_fair_wf
        (BRB_LTS.brb n f Value sender)
        (brb_fair_labels n Value)
        (leads_to
          (state_prop (fun s : BRB_LTS.State n Value =>
            (s.local_ sender).broadcastVal ≠ none))
          (state_prop (fun s : BRB_LTS.State n Value =>
            ∀ p, p ∉ s.corrupted → (s.local_ p).returned ≠ none))) e 0 := by
  intro e hv hcorr h_ante k hA
  simp only [state_prop] at hA
  obtain ⟨v, hbv⟩ := Option.ne_none_iff_exists'.mp hA
  have hbv' : ((e.states k).local_ sender).broadcastVal = some v := by
    have h0k : 0 + k = k := by omega
    rw [h0k] at hbv; exact hbv
  simp only [eventually, state_prop]
  -- Convert h_ante to the raw form expected by the delivery lemmas.
  have h_ante' : ∀ (l : BRB_LTS.Label n Value) (k₀ : Nat),
      (∀ j, (BRB_LTS.brb n f Value sender).enabled l (e.states (k₀ + j)) ∧
        brb_fair_labels n Value (e.states (k₀ + j)) l) →
      ∃ j, l = e.labels (k₀ + j) ∧
        (BRB_LTS.brb n f Value sender).step
          (e.states (k₀ + j)) (e.labels (k₀ + j)) (e.states (k₀ + j + 1)) := by
    intro l k₀ hinner
    have h := h_ante l k₀ (fun j => by
      simp only [state_prop]; rw [show 0 + k₀ + j = k₀ + j from by omega]; exact hinner j)
    simp only [eventually, Nat.zero_add] at h; exact h

  -- Per-proc claim: if p stays correct forever, returned(p) ≠ none eventually.
  have h_per_proc : ∀ p : Fin n,
      (∀ k', k ≤ k' → p ∉ (e.states k').corrupted) →
      ∃ k', k ≤ k' ∧ ((e.states k').local_ p).returned ≠ none := by
    intro p hp_corr
    -- === Stage 1: Init delivery for ALL processes ===
    have h_init : ∀ q : Fin n, ∃ kq, k ≤ kq ∧
        (((e.states kq).local_ q).sendRecv = some v ∨
         q ∈ (e.states kq).corrupted) := by
      intro q
      by_cases hq : q ∈ (e.states k).corrupted
      · exact ⟨k, le_refl k, Or.inr hq⟩
      · exact concrete_init_delivery n f Value sender hv h_ante' k q hbv'
          (fun k' _ => hcorr k') hq
    classical
    -- Take max KA over all init delivery positions.
    haveI : Nonempty (Fin n) := ⟨p⟩
    let kA_fn : Fin n → Nat := fun q => (h_init q).choose
    have hkA_spec : ∀ q, k ≤ kA_fn q ∧
        (((e.states (kA_fn q)).local_ q).sendRecv = some v ∨
         q ∈ (e.states (kA_fn q)).corrupted) :=
      fun q => (h_init q).choose_spec
    let KA := Finset.univ.sup kA_fn
    have hKA_ge : ∀ q, kA_fn q ≤ KA := fun q => Finset.le_sup (Finset.mem_univ q)
    have hKA_ge_k : k ≤ KA := Nat.le_trans (hkA_spec p).1 (hKA_ge p)
    -- At KA: correct-at-KA → sendRecv = some v (by persistence).
    have h_sr_KA : ∀ q, q ∉ (e.states KA).corrupted →
        ((e.states KA).local_ q).sendRecv = some v := by
      intro q hq
      rcases (hkA_spec q).2 with hsr | hc
      · exact BRB_LTS.sendRecv_persist_along hv hsr KA (hKA_ge q)
      · exact absurd (BRB_LTS.corrupted_mem_persist_along hv hc KA (hKA_ge q)) hq
    -- === Stage 2: Global echo delivery ===
    -- For each pair (q, r) where q stays correct forever from k:
    -- echo delivery from q to r. For non-forever-correct q: skip (set position to KA).
    let h_echo_pair : ∀ q r : Fin n,
        (∀ k', k ≤ k' → q ∉ (e.states k').corrupted) →
        ∃ kr, KA ≤ kr ∧ (((e.states kr).local_ r).echoRecv q v = true ∨
          r ∈ (e.states kr).corrupted) := by
      intro q r hq_corr
      by_cases hr : r ∈ (e.states KA).corrupted
      · exact ⟨KA, le_refl KA, Or.inr hr⟩
      · exact concrete_echo_delivery n f Value sender hv h_ante' KA q r
          (h_sr_KA q (hq_corr KA hKA_ge_k))
          (fun k' _ => hcorr k')
          (BRB_LTS.broadcastVal_persist_along hv hbv' KA hKA_ge_k)
          (fun k' hk' => hq_corr k' (Nat.le_trans hKA_ge_k hk')) hr
    -- Build echo position function for all pairs, defaulting to KA for non-forever-correct src.
    let kB_fn : Fin n × Fin n → Nat := fun ⟨q, r⟩ =>
      if hq : ∀ k', k ≤ k' → q ∉ (e.states k').corrupted
      then (h_echo_pair q r hq).choose
      else KA
    let KB := Finset.univ.sup kB_fn
    have hKB_ge_KA : KA ≤ KB := by
      suffices KA ≤ kB_fn (p, p) from
        Nat.le_trans this (Finset.le_sup (Finset.mem_univ (p, p)))
      by_cases hpc : ∀ k', k ≤ k' → p ∉ (e.states k').corrupted
      · have : kB_fn (p, p) = (h_echo_pair p p hpc).choose := dif_pos hpc
        rw [this]; exact (h_echo_pair p p hpc).choose_spec.1
      · have : kB_fn (p, p) = KA := dif_neg hpc
        rw [this]
    have hKB_ge_k : k ≤ KB := Nat.le_trans hKA_ge_k hKB_ge_KA
    -- At KB: for each forever-correct q and any r:
    -- echoRecv(r, q, v) = true ∨ r ∈ corrupted (by persistence from delivery position).
    have h_echo_KB : ∀ q r : Fin n,
        (∀ k', k ≤ k' → q ∉ (e.states k').corrupted) →
        ((e.states KB).local_ r).echoRecv q v = true ∨ r ∈ (e.states KB).corrupted := by
      intro q r hq
      have hqr_le : kB_fn (q, r) ≤ KB := Finset.le_sup (Finset.mem_univ (q, r))
      have hspec : KA ≤ kB_fn (q, r) ∧ (((e.states (kB_fn (q, r))).local_ r).echoRecv q v = true ∨
          r ∈ (e.states (kB_fn (q, r))).corrupted) := by
        simp only [kB_fn, dif_pos hq]
        exact (h_echo_pair q r hq).choose_spec
      rcases hspec.2 with hecho | hcorr'
      · exact Or.inl (BRB_LTS.echoRecv_persist_along hv hecho KB hqr_le)
      · exact Or.inr (BRB_LTS.corrupted_mem_persist_along hv hcorr' KB hqr_le)
    -- === Stage 3: Echo counting ===
    -- At KB: for all forever-correct r: countEchoRecv(r, v) ≥ echoThreshold.
    -- The count includes echoRecv from all forever-correct q. Need |forever-correct| ≥ n-f.
    -- We use: {forever-correct} ⊆ {correct at KB}. And echoRecv from forever-correct q = true.
    -- Filter includes at least {q ∉ corrupted(KB)} ∩ {forever-correct} = {forever-correct}.
    -- And |{q ∉ corrupted(KB)}| ≥ n - f (standard counting), plus echoRecv = true for all
    -- q ∉ corrupted(KB) that are forever-correct ⊇ all we need for the count.
    --
    -- Counting argument: |filter(echoRecv)| ≥ n - f.
    -- echoRecv from all forever-correct q. |complement of echoRecv filter| ≤ f because
    -- every q with echoRecv = false is not-forever-correct, and |ever-corrupted| ≤ f.
    have h_echo_count : ∀ r : Fin n,
        (∀ k', k ≤ k' → r ∉ (e.states k').corrupted) →
        BRB_LTS.countEchoRecv n Value ((e.states KB).local_ r) v ≥
          BRB_LTS.echoThreshold n f := by
      intro r hr
      unfold BRB_LTS.countEchoRecv BRB_LTS.echoThreshold
      -- echoRecv(r, q, v) = true for all forever-correct q.
      have h_fc_sub : ∀ q : Fin n, (∀ k', k ≤ k' → q ∉ (e.states k').corrupted) →
          ((e.states KB).local_ r).echoRecv q v = true := by
        intro q hq
        exact (h_echo_KB q r hq).resolve_right (fun hc => absurd hc (hr KB hKB_ge_k))
      -- Complement: echoRecv = false → not-forever-correct → ever-corrupted.
      -- |complement| ≤ f by pigeonhole on corrupted budget.
      have h_compl_le :
          ((List.finRange n).filter (fun q => !((e.states KB).local_ r).echoRecv q v)).length ≤ f := by
        by_contra hgt; push_neg at hgt
        -- > f processes have echoRecv = false. Each is not-forever-correct → has corruption time.
        let badQ := (List.finRange n).filter (fun q => !((e.states KB).local_ r).echoRecv q v)
        have h_bad_not_fc : ∀ q, q ∈ badQ → ∃ k', k ≤ k' ∧ q ∈ (e.states k').corrupted := by
          intro q hq
          simp only [badQ, List.mem_filter, Bool.not_eq_true] at hq
          by_contra h_fc; push_neg at h_fc
          rw [h_fc_sub q h_fc] at hq; simp at hq
        -- Take max corruption time. All bad q's in corrupted(K_max).
        have h_nodup : badQ.Nodup := (List.nodup_finRange n).sublist List.filter_sublist
        -- Pick corruption times and use Finset.sup for max.
        let ct : Fin n → Nat := fun q =>
          if hq : q ∈ badQ then (h_bad_not_fc q hq).choose else 0
        let K_m := Finset.univ.sup ct
        have hK_m_ge : ∀ q : Fin n, ct q ≤ K_m :=
          fun q => Finset.le_sup (Finset.mem_univ q)
        have h_all_in : ∀ q, q ∈ badQ → q ∈ (e.states K_m).corrupted := by
          intro q hq
          have hspec := (h_bad_not_fc q hq).choose_spec
          have : ct q = (h_bad_not_fc q hq).choose := dif_pos hq
          exact BRB_LTS.corrupted_mem_persist_along hv hspec.2 K_m (this ▸ hK_m_ge q)
        have hsub : badQ.length ≤ (e.states K_m).corrupted.length :=
          nodup_sub_length h_nodup h_all_in
        have hbud := BRB_Simulation.corrupted_budget (System.valid_exec_reachable hv K_m)
        exact absurd (Nat.lt_of_lt_of_le hgt (Nat.le_trans hsub hbud)) (Nat.lt_irrefl f)
      -- filter(echoRecv = true) + filter(echoRecv = false) = n
      have h_sum := (List.finRange n).length_eq_length_filter_add
        (fun q => ((e.states KB).local_ r).echoRecv q v)
      simp only [List.length_finRange] at h_sum
      omega
    -- === Stage 4: Global vote delivery ===
    -- For each forever-correct pair (q, r): vote delivery from q to r.
    -- q needs countEchoRecv ≥ echoThreshold at KB (proved in Stage 3 for forever-correct q).
    let h_vote_pair : ∀ q r : Fin n,
        (∀ k', k ≤ k' → q ∉ (e.states k').corrupted) →
        ∃ kr, KB ≤ kr ∧ (((e.states kr).local_ r).voteRecv q v = true ∨
          r ∈ (e.states kr).corrupted) := by
      intro q r hq_corr
      by_cases hr : r ∈ (e.states KB).corrupted
      · exact ⟨KB, le_refl KB, Or.inr hr⟩
      · exact concrete_vote_delivery n f Value sender hv h_ante' KB q r
          (h_echo_count q hq_corr)
          (fun k' hk' => hq_corr k' (Nat.le_trans hKB_ge_k hk')) hr
    -- Build vote position function + max KC.
    let kC_fn : Fin n × Fin n → Nat := fun ⟨q, r⟩ =>
      if hq : ∀ k', k ≤ k' → q ∉ (e.states k').corrupted
      then (h_vote_pair q r hq).choose
      else KB
    let KC := Finset.univ.sup kC_fn
    have hKC_ge_KB : KB ≤ KC := by
      suffices KB ≤ kC_fn (p, p) from
        Nat.le_trans this (Finset.le_sup (Finset.mem_univ (p, p)))
      by_cases hpc : ∀ k', k ≤ k' → p ∉ (e.states k').corrupted
      · have : kC_fn (p, p) = (h_vote_pair p p hpc).choose := dif_pos hpc
        rw [this]; exact (h_vote_pair p p hpc).choose_spec.1
      · have : kC_fn (p, p) = KB := dif_neg hpc
        rw [this]
    have hKC_ge_k : k ≤ KC := Nat.le_trans hKB_ge_k hKC_ge_KB
    -- At KC: voteRecv from all forever-correct q (by persistence).
    have h_vote_KC : ∀ q r : Fin n,
        (∀ k', k ≤ k' → q ∉ (e.states k').corrupted) →
        ((e.states KC).local_ r).voteRecv q v = true ∨ r ∈ (e.states KC).corrupted := by
      intro q r hq
      have hqr_le : kC_fn (q, r) ≤ KC := Finset.le_sup (Finset.mem_univ (q, r))
      have hspec : KB ≤ kC_fn (q, r) ∧ (((e.states (kC_fn (q, r))).local_ r).voteRecv q v = true ∨
          r ∈ (e.states (kC_fn (q, r))).corrupted) := by
        simp only [kC_fn, dif_pos hq]
        exact (h_vote_pair q r hq).choose_spec
      rcases hspec.2 with hvote | hcorr'
      · exact Or.inl (BRB_LTS.voteRecv_persist_along hv hvote KC hqr_le)
      · exact Or.inr (BRB_LTS.corrupted_mem_persist_along hv hcorr' KC hqr_le)
    -- === Stage 5: Vote counting (same structure as echo counting) ===
    have h_vote_count :
        BRB_LTS.countVoteRecv n Value ((e.states KC).local_ p) v ≥
          BRB_LTS.returnThreshold n f := by
      unfold BRB_LTS.countVoteRecv BRB_LTS.returnThreshold
      have h_fc_sub : ∀ q : Fin n, (∀ k', k ≤ k' → q ∉ (e.states k').corrupted) →
          ((e.states KC).local_ p).voteRecv q v = true := by
        intro q hq
        exact (h_vote_KC q p hq).resolve_right (fun hc => absurd hc (hp_corr KC hKC_ge_k))
      have h_compl_le :
          ((List.finRange n).filter (fun q => !((e.states KC).local_ p).voteRecv q v)).length ≤ f := by
        by_contra hgt; push_neg at hgt
        let badQ := (List.finRange n).filter (fun q => !((e.states KC).local_ p).voteRecv q v)
        have h_bad_not_fc : ∀ q, q ∈ badQ → ∃ k', k ≤ k' ∧ q ∈ (e.states k').corrupted := by
          intro q hq
          simp only [badQ, List.mem_filter, Bool.not_eq_true] at hq
          by_contra h_fc; push_neg at h_fc
          rw [h_fc_sub q h_fc] at hq; simp at hq
        have h_nodup : badQ.Nodup := (List.nodup_finRange n).sublist List.filter_sublist
        let ct : Fin n → Nat := fun q =>
          if hq : q ∈ badQ then (h_bad_not_fc q hq).choose else 0
        let K_m := Finset.univ.sup ct
        have hK_m_ge : ∀ q : Fin n, ct q ≤ K_m :=
          fun q => Finset.le_sup (Finset.mem_univ q)
        have h_all_in : ∀ q, q ∈ badQ → q ∈ (e.states K_m).corrupted := by
          intro q hq
          have hspec := (h_bad_not_fc q hq).choose_spec
          have : ct q = (h_bad_not_fc q hq).choose := dif_pos hq
          exact BRB_LTS.corrupted_mem_persist_along hv hspec.2 K_m (this ▸ hK_m_ge q)
        have hsub : badQ.length ≤ (e.states K_m).corrupted.length :=
          nodup_sub_length h_nodup h_all_in
        have hbud := BRB_Simulation.corrupted_budget (System.valid_exec_reachable hv K_m)
        exact absurd (Nat.lt_of_lt_of_le hgt (Nat.le_trans hsub hbud)) (Nat.lt_irrefl f)
      have h_sum := (List.finRange n).length_eq_length_filter_add
        (fun q => ((e.states KC).local_ p).voteRecv q v)
      simp only [List.length_finRange] at h_sum
      omega
    -- === Stage 6: Output delivery ===
    obtain ⟨k', hk', hret⟩ := concrete_output_delivery n f Value sender hv h_ante' KC p
      h_vote_count (fun k' hk' => hp_corr k' (Nat.le_trans hKC_ge_k hk'))
    exact ⟨k', Nat.le_trans hKC_ge_k hk', hret⟩
  -- === Combine per-proc results (same pattern as ideal_brb_totality Step B) ===
  have h_per_proc_persist : ∀ p : Fin n, ∃ k'_p, k ≤ k'_p ∧
      ∀ k', k'_p ≤ k' →
        (p ∉ (e.states k').corrupted → ((e.states k').local_ p).returned ≠ none) := by
    intro p
    by_cases h_correct : ∀ k', k ≤ k' → p ∉ (e.states k').corrupted
    · obtain ⟨k'_p, hk'_p, hret⟩ := h_per_proc p h_correct
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hret
      refine ⟨k'_p, hk'_p, fun k' hk' _ => ?_⟩
      have := BRB_LTS.returned_persist_along hv hw k' hk'
      simp [this]
    · push_neg at h_correct
      obtain ⟨k₂, hk₂, hc⟩ := h_correct
      refine ⟨k₂, by omega, fun k' hk' hcorr => ?_⟩
      exact absurd (BRB_LTS.corrupted_mem_persist_along hv hc k' hk') hcorr
  classical
  let k'_fn : Fin n → Nat := fun p => (h_per_proc_persist p).choose
  have hk'_spec : ∀ p, k ≤ k'_fn p ∧
      ∀ k', k'_fn p ≤ k' →
        (p ∉ (e.states k').corrupted → ((e.states k').local_ p).returned ≠ none) :=
    fun p => (h_per_proc_persist p).choose_spec
  by_cases hn0 : n = 0
  · subst hn0; exact ⟨0, fun p => Fin.elim0 p⟩
  · haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    let k_max := Finset.univ.sup k'_fn
    have hk_max_ge : ∀ p, k'_fn p ≤ k_max :=
      fun p => Finset.le_sup (Finset.mem_univ p)
    have hk_max_ge_k : k ≤ k_max := by
      have := (hk'_spec ⟨0, by omega⟩).1
      have := hk_max_ge ⟨0, by omega⟩
      omega
    refine ⟨k_max - k, ?_⟩
    have hkmax_eq : 0 + k + (k_max - k) = k_max := by omega
    rw [hkmax_eq]
    intro p hp
    exact (hk'_spec p).2 k_max (hk_max_ge p) hp

end BRB_Liveness
