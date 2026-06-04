import Leslie_LTS.Framework
import Leslie_LTS.Examples.BCA
import Leslie_LTS.Examples.IdealBCA

/-! # BCA Liveness: Fair-Deadlock Analysis and Ideal Decision

  This file provides:
  1. Fair-label classification (`bca_fair_labels`, `ideal_bca_fair_labels`).
  2. Fair-deadlock analysis: at a reachable fair-deadlock with enough input
     support, the delivery chain forces all correct processes to have decided
     (`bca_fair_deadlock_implies_terminated` — 3 sorries remaining in
     `fair_deadlock_approved_spreads` and `bca_fair_deadlock_implies_terminated`).
  3. Ideal-level decision theorems (`ideal_bca_decision`,
     `ideal_bca_decision_stutter`) — sorry-free.

  The `WeakDivPreserving` witness and simulation-based `bca_decision` via
  `transfers_leads_to` were removed (same reason as BRB — see the
  "Why bca_totality via transfers_leads_to was removed" section below).
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

    ### Theorem overview

    **ideal_bca_decision / ideal_bca_decision_stutter:**
    Same until-or-forever structure as ideal_brb_totality:
    Step A: input ready → bound_value eventually set (via fair bind).
    Step B: bound_value set → all correct procs eventually decide (via
      fair output).

    **bca_fair_deadlock_implies_terminated:**
    At a fair-deadlock with inputSupport ≥ amplifyThreshold, no fair
    step is enabled, but every correct process has already decided.
    3 sorries remain: approval spreading and case-split completion.
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

/-! ## Fair-deadlock delivery: sent → received for correct-to-correct -/

/-- At a reachable fair-deadlock, if correct src sent init(some b) to
    correct dst, then dst has received it (initRecv = true). -/
theorem fair_deadlock_init_delivered
    (s : BCA_LTS.State T n)
    (hreach : Reachable (BCA_LTS.bca T n f) s)
    (hfd : FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s)
    {src dst : Fin n} (hsrc : src ∉ s.corrupted) (hdst : dst ∉ s.corrupted)
    {b : T} (hsent : (s.local_ src).sent dst .init (some b) = true) :
    (s.local_ dst).initRecv src b = true := by
  rcases BCA_LTS.init_delivery_inv hreach src dst b hsent with hbuf | hrecv
  · exact absurd hbuf (by rw [fair_deadlock_no_fair_buffer T n f s hfd hsrc hdst]; simp)
  · exact hrecv

/-- At a reachable fair-deadlock, if correct src sent echo(some b) to
    correct dst, then dst has received it (echoRecv = true). -/
theorem fair_deadlock_echo_delivered
    (s : BCA_LTS.State T n)
    (hreach : Reachable (BCA_LTS.bca T n f) s)
    (hfd : FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s)
    {src dst : Fin n} (hsrc : src ∉ s.corrupted) (hdst : dst ∉ s.corrupted)
    {b : T} (hsent : (s.local_ src).sent dst .echo (some b) = true) :
    (s.local_ dst).echoRecv src b = true := by
  rcases BCA_LTS.echo_delivery_inv hreach src dst b hsent with hbuf | hrecv
  · exact absurd hbuf (by rw [fair_deadlock_no_fair_buffer T n f s hfd hsrc hdst]; simp)
  · exact hrecv

/-- At a reachable fair-deadlock, if correct src sent vote(v) to
    correct dst, then dst has received it (voteRecv = true). -/
theorem fair_deadlock_vote_delivered
    (s : BCA_LTS.State T n)
    (hreach : Reachable (BCA_LTS.bca T n f) s)
    (hfd : FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s)
    {src dst : Fin n} (hsrc : src ∉ s.corrupted) (hdst : dst ∉ s.corrupted)
    {v : BCA_LTS.Val T} (hsent : (s.local_ src).sent dst .vote v = true) :
    (s.local_ dst).voteRecv src v = true := by
  rcases BCA_LTS.vote_delivery_inv hreach src dst v hsent with hbuf | hrecv
  · exact absurd hbuf (by rw [fair_deadlock_no_fair_buffer T n f s hfd hsrc hdst]; simp)
  · exact hrecv

/-- At a reachable fair-deadlock, a correct-to-correct init send has
    been done (otherwise the send step would be enabled). -/
theorem fair_deadlock_init_sent
    (s : BCA_LTS.State T n) (hn : n > 3 * f)
    (hreach : Reachable (BCA_LTS.bca T n f) s)
    (hfd : FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s)
    {src dst : Fin n} (hsrc : src ∉ s.corrupted) (hdst : dst ∉ s.corrupted)
    {b : T} (hgate : (s.local_ src).input = some b ∨
                      BCA_LTS.countInitRecv T n (s.local_ src) b ≥ BCA_LTS.amplifyThreshold f) :
    (s.local_ src).sent dst .init (some b) = true := by
  by_contra h
  simp only [Bool.not_eq_true] at h
  have henabled := BCA_LTS.send_init_enabled (f := f) hsrc h hgate
  obtain ⟨s', hstep⟩ := henabled
  exact hfd (.send src dst .init (some b)) s' hstep ⟨hsrc, hdst⟩

/-- At a reachable fair-deadlock, a correct proc with approved(b) and
    compatible echoed has sent echo(some b) to every correct proc. -/
theorem fair_deadlock_echo_sent
    (s : BCA_LTS.State T n)
    (hreach : Reachable (BCA_LTS.bca T n f) s)
    (hfd : FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s)
    {src dst : Fin n} (hsrc : src ∉ s.corrupted) (hdst : dst ∉ s.corrupted)
    {b : T} (happroved : (s.local_ src).approved b = true)
    (hechoed : (s.local_ src).echoed = none ∨ (s.local_ src).echoed = some b) :
    (s.local_ src).sent dst .echo (some b) = true := by
  by_contra h
  simp only [Bool.not_eq_true] at h
  have henabled := BCA_LTS.send_echo_enabled (f := f) hsrc h happroved hechoed
  obtain ⟨s', hstep⟩ := henabled
  exact hfd (.send src dst .echo (some b)) s' hstep ⟨hsrc, hdst⟩

/-- At a fair-deadlock, a correct proc with approved(b) has echoed ≠ none.
    Proof: if echoed = none and approved(b), then echo(some b) send to any
    correct dst is enabled (fair), contradicting fair deadlock. -/
theorem fair_deadlock_echoed_ne_none
    (s : BCA_LTS.State T n)
    (hreach : Reachable (BCA_LTS.bca T n f) s)
    (hfd : FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s)
    {p : Fin n} (hp : p ∉ s.corrupted)
    {b : T} (happroved : (s.local_ p).approved b = true)
    [Inhabited (Fin n)] (hn : 0 < n) :
    (s.local_ p).echoed ≠ none := by
  intro hechoed
  have hcompat : (s.local_ p).echoed = none ∨ (s.local_ p).echoed = some b :=
    Or.inl hechoed
  have hsent_false : (s.local_ p).sent p .echo (some b) = false := by
    by_contra hsent
    simp only [Bool.not_eq_false] at hsent
    have := BCA_LTS.sent_echo_implies_echoed hreach b hp hsent
    rw [this] at hechoed; simp at hechoed
  have henabled := BCA_LTS.send_echo_enabled (f := f) hp hsent_false happroved hcompat
  obtain ⟨s', hstep⟩ := henabled
  exact hfd (.send p p .echo (some b)) s' hstep ⟨hp, hp⟩

/-- At a reachable fair-deadlock, a correct proc with enough echo quorum
    and consistent voting has sent vote(some b) to every correct proc. -/
theorem fair_deadlock_vote_sent
    (s : BCA_LTS.State T n)
    (hreach : Reachable (BCA_LTS.bca T n f) s)
    (hfd : FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s)
    {src dst : Fin n} (hsrc : src ∉ s.corrupted) (hdst : dst ∉ s.corrupted)
    {b : T} (huniq : ∀ w, (s.local_ src).voted w = true → w = some b)
    (hquorum : BCA_LTS.countEchoRecv T n (s.local_ src) b ≥ BCA_LTS.echoThreshold n f) :
    (s.local_ src).sent dst .vote (some b) = true := by
  by_contra h
  simp only [Bool.not_eq_true] at h
  have henabled := BCA_LTS.send_vote_binary_enabled (f := f) hsrc h huniq hquorum
  obtain ⟨s', hstep⟩ := henabled
  exact hfd (.send src dst .vote (some b)) s' hstep ⟨hsrc, hdst⟩

/-- At a reachable fair-deadlock, a correct proc that is undecided
    with enough binary votes has decided (contradiction). -/
theorem fair_deadlock_output_contradiction
    (s : BCA_LTS.State T n)
    (hfd : FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s)
    {p : Fin n} (hp : p ∉ s.corrupted)
    {b : T} (hdec : (s.local_ p).decided = none)
    (hvotes : BCA_LTS.countVoteRecv T n (s.local_ p) (some b) ≥ BCA_LTS.returnThreshold n f) :
    False := by
  have henabled := BCA_LTS.output_binary_enabled hp hdec hvotes
  obtain ⟨s', hstep⟩ := henabled
  exact hfd (.output p (some b)) s' hstep hp

/-! ## Delivery chain helpers for fair-deadlock termination -/

/-- At a fair deadlock, if correct src has input = some b, every correct
    dst has initRecv(src, b) = true (init delivered). -/
theorem fair_deadlock_initRecv_from_input
    (s : BCA_LTS.State T n) (hn : n > 3 * f)
    (hreach : Reachable (BCA_LTS.bca T n f) s)
    (hfd : FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s)
    {src : Fin n} (hsrc : src ∉ s.corrupted)
    {b : T} (hinput : (s.local_ src).input = some b)
    {dst : Fin n} (hdst : dst ∉ s.corrupted) :
    (s.local_ dst).initRecv src b = true := by
  have hsent := fair_deadlock_init_sent T n f s hn hreach hfd hsrc hdst (Or.inl hinput)
  exact fair_deadlock_init_delivered T n f s hreach hfd hsrc hdst hsent

/-- At a fair deadlock, countInitRecv(q, b) ≥ inputSupport(b) for every correct q.
    Proof: every correct proc p with input=b sent init(b) to q and it was received. -/
theorem fair_deadlock_countInitRecv_ge_inputSupport
    (s : BCA_LTS.State T n) (hn : n > 3 * f)
    (hreach : Reachable (BCA_LTS.bca T n f) s)
    (hfd : FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s)
    {q : Fin n} (hq : q ∉ s.corrupted) (b : T) :
    BCA_LTS.countInitRecv T n (s.local_ q) b ≥ BCA_LTS.inputSupport T n s b := by
  simp only [BCA_LTS.countInitRecv, BCA_LTS.inputSupport]
  apply filter_length_mono
  intro p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨hcorr, hinput⟩ := hp
  exact fair_deadlock_initRecv_from_input T n f s hn hreach hfd hcorr hinput hq

/-- At a fair deadlock with inputSupport(b) ≥ amplifyThreshold,
    countInitRecv(q, b) ≥ approveThreshold for every correct q.
    Chain: input procs → init(b) → received → amplify → all correct send init(b)
    → received → count ≥ n-f = approveThreshold. -/
theorem fair_deadlock_countInitRecv_ge_approveThreshold
    (s : BCA_LTS.State T n) (hn : n > 3 * f)
    (hreach : Reachable (BCA_LTS.bca T n f) s)
    (hfd : FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s)
    {b : T} (hsupp : BCA_LTS.inputSupport T n s b ≥ BCA_LTS.amplifyThreshold f)
    {q : Fin n} (hq : q ∉ s.corrupted) :
    BCA_LTS.countInitRecv T n (s.local_ q) b ≥ BCA_LTS.approveThreshold n f := by
  -- Step 1: inputSupport ≥ amplifyThreshold → countInitRecv ≥ amplifyThreshold
  have hstep1 : ∀ r, r ∉ s.corrupted →
      BCA_LTS.countInitRecv T n (s.local_ r) b ≥ BCA_LTS.amplifyThreshold f :=
    fun r hr => Nat.le_trans hsupp
      (fair_deadlock_countInitRecv_ge_inputSupport T n f s hn hreach hfd hr b)
  -- Step 2: With amplifyThreshold met, ALL correct procs send init(b)
  -- to all correct procs (amplification gate opens).
  -- So ∀ correct src, ∀ correct dst, initRecv(dst, src, b) = true.
  have hstep2 : ∀ src dst, src ∉ s.corrupted → dst ∉ s.corrupted →
      (s.local_ dst).initRecv src b = true := by
    intro src dst hsrc hdst
    have hsent := fair_deadlock_init_sent T n f s hn hreach hfd hsrc hdst
      (Or.inr (hstep1 src hsrc))
    exact fair_deadlock_init_delivered T n f s hreach hfd hsrc hdst hsent
  -- Step 3: countInitRecv(q, b) counts at least all correct procs ≥ n - f
  have hbudget := BCA_LTS.corrupted_budget_reachable hreach
  exact count_correct_ge s.corrupted hbudget
    (fun p => (s.local_ q).initRecv p b) (fun p hp => hstep2 p q hp hq)

/-- At a fair deadlock with inputSupport(b) ≥ amplifyThreshold,
    approved(b) = true for every correct process. -/
theorem fair_deadlock_all_approved
    (s : BCA_LTS.State T n) (hn : n > 3 * f)
    (hreach : Reachable (BCA_LTS.bca T n f) s)
    (hfd : FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s)
    {b : T} (hsupp : BCA_LTS.inputSupport T n s b ≥ BCA_LTS.amplifyThreshold f)
    {q : Fin n} (hq : q ∉ s.corrupted) :
    (s.local_ q).approved b = true := by
  have hpos : BCA_LTS.approveThreshold n f > 0 := by
    simp only [BCA_LTS.approveThreshold]; omega
  exact BCA_LTS.countInitRecv_ge_implies_approved hreach q b hpos
    (fair_deadlock_countInitRecv_ge_approveThreshold T n f s hn hreach hfd hsupp hq)

/-- At a fair deadlock with inputSupport(b) ≥ amplifyThreshold, every
    correct proc src has sent echo(some (echoed_value src)) to all correct.
    The echoed value is echoed(src) = some b' for some b', and this echo
    was sent because approved(b') and echoed compatible. -/
theorem fair_deadlock_echo_sent_echoed
    (s : BCA_LTS.State T n) (hn : n > 3 * f)
    (hreach : Reachable (BCA_LTS.bca T n f) s)
    (hfd : FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s)
    {b : T} (hsupp : BCA_LTS.inputSupport T n s b ≥ BCA_LTS.amplifyThreshold f)
    {src : Fin n} (hsrc : src ∉ s.corrupted)
    {dst : Fin n} (hdst : dst ∉ s.corrupted) :
    ∃ b', (s.local_ src).echoed = some b' ∧
      (s.local_ src).sent dst .echo (some b') = true := by
  have happroved := fair_deadlock_all_approved T n f s hn hreach hfd hsupp hsrc
  have hechoed_ne := fair_deadlock_echoed_ne_none T n f s hreach hfd hsrc happroved
    (by omega)
  obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.mp hechoed_ne
  refine ⟨b', hb', ?_⟩
  -- echoed = some b' → approved(b') by echoed_implies_approved
  have happroved' := BCA_LTS.echoed_implies_approved hreach src b' hsrc hb'
  -- echo(some b') sent because approved(b') and echoed = some b' (compatible)
  exact fair_deadlock_echo_sent T n f s hreach hfd hsrc hdst happroved' (Or.inr hb')

/-- At a fair deadlock with inputSupport(b) ≥ amplifyThreshold, every
    correct proc src has sent echo(some b') to all correct dst, and
    dst received it: echoRecv(dst, src, b') = true. -/
theorem fair_deadlock_echoRecv_from_echoed
    (s : BCA_LTS.State T n) (hn : n > 3 * f)
    (hreach : Reachable (BCA_LTS.bca T n f) s)
    (hfd : FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s)
    {b : T} (hsupp : BCA_LTS.inputSupport T n s b ≥ BCA_LTS.amplifyThreshold f)
    {src : Fin n} (hsrc : src ∉ s.corrupted)
    {dst : Fin n} (hdst : dst ∉ s.corrupted) :
    ∃ b', (s.local_ src).echoed = some b' ∧
      (s.local_ dst).echoRecv src b' = true := by
  obtain ⟨b', hechoed, hsent⟩ := fair_deadlock_echo_sent_echoed T n f s hn hreach hfd hsupp hsrc hdst
  exact ⟨b', hechoed, fair_deadlock_echo_delivered T n f s hreach hfd hsrc hdst hsent⟩

/-- At a fair deadlock with inputSupport(b) ≥ amplifyThreshold,
    countEchoRecv(q, b') ≥ |{correct r : echoed(r) = some b'}| for every correct q.
    The echo chain ensures all correct procs' echoes are received. -/
theorem fair_deadlock_countEchoRecv_ge_echo_support
    (s : BCA_LTS.State T n) (hn : n > 3 * f)
    (hreach : Reachable (BCA_LTS.bca T n f) s)
    (hfd : FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s)
    {b : T} (hsupp : BCA_LTS.inputSupport T n s b ≥ BCA_LTS.amplifyThreshold f)
    {q : Fin n} (hq : q ∉ s.corrupted) (b' : T) :
    BCA_LTS.countEchoRecv T n (s.local_ q) b' ≥
      ((List.finRange n).filter (fun r =>
        decide (r ∉ s.corrupted) && decide ((s.local_ r).echoed = some b'))).length := by
  simp only [BCA_LTS.countEchoRecv]
  apply filter_length_mono; intro r hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨hcorr, hechoed⟩ := hr
  obtain ⟨v, hv, hrecv⟩ := fair_deadlock_echoRecv_from_echoed T n f s hn hreach hfd hsupp hcorr hq
  rw [hechoed] at hv; exact Option.some.inj hv ▸ hrecv

/-- At a fair deadlock, if correct src has two approved values and hasn't
    voted, then vote(none) send is enabled — contradicting fair deadlock.
    So src MUST have voted. -/
theorem fair_deadlock_vote_none_sent
    (s : BCA_LTS.State T n)
    (hfd : FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s)
    {src dst : Fin n} (hsrc : src ∉ s.corrupted) (hdst : dst ∉ s.corrupted)
    {b₁ b₂ : T} (hne : b₁ ≠ b₂)
    (happr1 : (s.local_ src).approved b₁ = true)
    (happr2 : (s.local_ src).approved b₂ = true)
    (huniq : ∀ w, (s.local_ src).voted w = true → w = none) :
    (s.local_ src).sent dst .vote none = true := by
  by_contra h
  simp only [Bool.not_eq_true] at h
  have henabled := BCA_LTS.send_vote_none_enabled (f := f) hsrc h huniq b₁ b₂ hne happr1 happr2
  obtain ⟨s', hstep⟩ := henabled
  exact hfd (.send src dst .vote none) s' hstep ⟨hsrc, hdst⟩

/-- At a fair deadlock, if any correct proc has approved(b'), then ALL
    correct procs have approved(b').
    Key insight: approved(b') requires countInitRecv(b') ≥ n-f. At least
    n-2f of those senders are correct. At the fair deadlock, those correct
    senders sent init(b') to ALL correct procs. Since n-2f ≥ f+1 = amplifyThreshold
    (from n > 3f), the amplification chain gives all correct approved(b'). -/
theorem fair_deadlock_approved_spreads
    (s : BCA_LTS.State T n) (hn : n > 3 * f)
    (hreach : Reachable (BCA_LTS.bca T n f) s)
    (hfd : FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s)
    {b' : T} {q₀ : Fin n} (hq₀ : q₀ ∉ s.corrupted)
    (happroved₀ : (s.local_ q₀).approved b' = true)
    {q : Fin n} (hq : q ∉ s.corrupted) :
    (s.local_ q).approved b' = true := by
  have hbudget := BCA_LTS.corrupted_budget_reachable hreach
  have hpos : BCA_LTS.approveThreshold n f > 0 := by
    simp only [BCA_LTS.approveThreshold]; omega
  -- Step 1: q₀ has countInitRecv(q₀, b') ≥ approveThreshold = n-f
  have hcount₀ := BCA_LTS.approved_implies_countInitRecv_ge hreach q₀ b' happroved₀
  -- Step 2: Every correct src that delivered init(b') to q₀ also delivers to ALL correct.
  -- Chain: initRecv(q₀, src, b') → sent(src, q₀, init, some b') → gate open → sent to all → delivered.
  have h_correct_src_delivers_all : ∀ src, src ∉ s.corrupted →
      (s.local_ q₀).initRecv src b' = true →
      ∀ r, r ∉ s.corrupted → (s.local_ r).initRecv src b' = true := by
    intro src hsrc hinitRecv r hr
    have hsent := BCA_LTS.initRecv_implies_sent hreach hinitRecv
    have hgate := BCA_LTS.sent_init_implies_gate hreach hsrc b' hsent
    have hsent_r := fair_deadlock_init_sent T n f s hn hreach hfd hsrc hr hgate
    exact fair_deadlock_init_delivered T n f s hreach hfd hsrc hr hsent_r
  -- Step 3: Every correct r has countInitRecv(b') ≥ f+1 = amplifyThreshold.
  -- Among q₀'s n-f initRecv sources, at least n-2f are correct (budget).
  -- Those n-2f correct sources also delivered to r. And n-2f ≥ f+1 since n > 3f.
  have h_amplify : ∀ r, r ∉ s.corrupted →
      BCA_LTS.countInitRecv T n (s.local_ r) b' ≥ BCA_LTS.amplifyThreshold f := by
    intro r hr
    -- Count correct sources from q₀'s initRecv that also delivered to r.
    have hsub := intersect_correct_ge s.corrupted
      (fun p => (s.local_ q₀).initRecv p b') hbudget hcount₀
    have hmono := filter_length_mono
      (fun p => (s.local_ q₀).initRecv p b' && decide (p ∉ s.corrupted))
      ((s.local_ r).initRecv · b') (List.finRange n)
      (fun src hsrc_filt => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hsrc_filt
        exact h_correct_src_delivers_all src hsrc_filt.2 hsrc_filt.1 r hr)
    simp only [BCA_LTS.countInitRecv, BCA_LTS.amplifyThreshold, BCA_LTS.approveThreshold] at *
    omega
  -- Step 4: With amplifyThreshold met, all correct send init(b') to q → delivered.
  have h_all_delivered : ∀ src, src ∉ s.corrupted →
      (s.local_ q).initRecv src b' = true := by
    intro src hsrc
    have hgate : (s.local_ src).input = some b' ∨
        BCA_LTS.countInitRecv T n (s.local_ src) b' ≥ BCA_LTS.amplifyThreshold f :=
      Or.inr (h_amplify src hsrc)
    have hsent := fair_deadlock_init_sent T n f s hn hreach hfd hsrc hq hgate
    exact fair_deadlock_init_delivered T n f s hreach hfd hsrc hq hsent
  -- Step 5: countInitRecv(q, b') ≥ n-f = approveThreshold → approved(q, b')
  have hcount_q := count_correct_ge s.corrupted hbudget
    (fun p => (s.local_ q).initRecv p b') (fun p hp => h_all_delivered p hp)
  exact BCA_LTS.countInitRecv_ge_implies_approved hreach q b' hpos hcount_q

/-- At a fair deadlock, output(none) contradicts if p is correct, undecided,
    has two approved values, and enough total votes. -/
theorem fair_deadlock_output_none_contradiction
    (s : BCA_LTS.State T n)
    (hfd : FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s)
    {p : Fin n} (hp : p ∉ s.corrupted) (hdec : (s.local_ p).decided = none)
    {b₁ b₂ : T} (hne : b₁ ≠ b₂)
    (happr1 : (s.local_ p).approved b₁ = true)
    (happr2 : (s.local_ p).approved b₂ = true)
    {vals : List (BCA_LTS.Val T)}
    (hvotes : BCA_LTS.countAnyVoteRecv T n (s.local_ p) vals ≥ BCA_LTS.returnThreshold n f) :
    False := by
  have henabled := BCA_LTS.output_none_enabled (f := f) hp hdec b₁ b₂ hne happr1 happr2 vals hvotes
  obtain ⟨s', hstep⟩ := henabled
  exact hfd (.output p none) s' hstep hp

/-! ## Reachable fair-deadlocks are terminated

    The original `bca_no_fair_deadlock_reachable` was false at
    terminated reachable states (vacuously fair-deadlocks); replaced
    after Phase C.2 by the honest claim that any reachable
    fair-deadlock is terminated. -/
/-- At a reachable fair-deadlock with inputSupport(b) ≥ amplifyThreshold
    for some value b, every correct process has decided.

    **Precondition:** `∃ b, inputSupport(b) ≥ amplifyThreshold f`.
    The caller provides this from binary T + all-correct-input + n > 3f
    (via pigeonhole), or directly when the sim_rel guarantees enough support.

    **Proof outline:**
    1. Amplification chain → approved(b) for all correct (helpers proved).
    2. Echo delivery → vote chain → output (requires case analysis). -/
theorem bca_fair_deadlock_implies_terminated (hn : n > 3 * f) :
    ∀ s, Reachable (BCA_LTS.bca T n f) s →
      FairDeadlock (BCA_LTS.bca T n f) (bca_fair_labels T n) s →
      (∃ b, BCA_LTS.inputSupport T n s b ≥ BCA_LTS.amplifyThreshold f) →
      ∀ p, p ∉ s.corrupted → (s.local_ p).decided ≠ none := by
  intro s hreach hfd ⟨b, hsupp_b⟩ p hp hdec
  have hbudget := BCA_LTS.corrupted_budget_reachable hreach
  -- Steps 1-3 (proved by helpers): all correct approved(b)
  have hall_approved : ∀ q, q ∉ s.corrupted → (s.local_ q).approved b = true :=
    fun q hq => fair_deadlock_all_approved T n f s hn hreach hfd hsupp_b hq
  -- Step 4: Each correct proc echoed some value
  have hall_echoed : ∀ q, q ∉ s.corrupted → (s.local_ q).echoed ≠ none :=
    fun q hq => fair_deadlock_echoed_ne_none T n f s hreach hfd hq (hall_approved q hq) (by omega)
  -- Unified case analysis: does any correct proc have a second approved value?
  by_cases hextra : ∃ b', b' ≠ b ∧ ∃ q₁, q₁ ∉ s.corrupted ∧ (s.local_ q₁).approved b' = true
  · -- Path A: Second approved value exists → ALL correct have two approved → output(none)
    obtain ⟨b', hne, q₁, hq₁, happr'⟩ := hextra
    -- By approved_spreads: ALL correct have approved(b')
    have hall_approved' : ∀ q, q ∉ s.corrupted → (s.local_ q).approved b' = true :=
      fun q hq => fair_deadlock_approved_spreads T n f s hn hreach hfd hq₁ happr' hq
    -- p has two approved values → output(none) with countAnyVoteRecv ≥ n-f
    -- At the fair deadlock, every correct proc voted something (if it hadn't,
    -- vote send would be enabled → contradiction). All votes delivered.
    -- countAnyVoteRecv(p, list_of_voted_values) ≥ n-f.
    -- This sorry requires: showing every correct proc voted + all votes delivered
    -- + constructing the appropriate vote-values list for countAnyVoteRecv.
    sorry
  · -- Path B: No second approved value → all echoed b → echo quorum → vote(some b) → output(some b)
    push_neg at hextra
    -- Since no correct proc has approved b' for b' ≠ b, and echoed(q) implies
    -- approved(echoed_val) by echoed_implies_approved, all correct must have echoed = some b.
    have hall_echo_b : ∀ q, q ∉ s.corrupted → (s.local_ q).echoed = some b := by
      intro q hq
      obtain ⟨bq, hbq⟩ := Option.ne_none_iff_exists'.mp (hall_echoed q hq)
      by_contra hne
      have hbq_ne : bq ≠ b := fun h => hne (h ▸ hbq)
      have := BCA_LTS.echoed_implies_approved hreach q bq hq hbq
      exact hextra bq hbq_ne q hq this
    -- Echo quorum for b: countEchoRecv(p, b) ≥ n-f
    have hecho_count : BCA_LTS.countEchoRecv T n (s.local_ p) b ≥ BCA_LTS.echoThreshold n f := by
      have hge := fair_deadlock_countEchoRecv_ge_echo_support T n f s hn hreach hfd hsupp_b hp b
      simp only [BCA_LTS.echoThreshold]
      apply Nat.le_trans _ hge
      exact count_correct_ge s.corrupted hbudget
        (fun r => decide (r ∉ s.corrupted) && decide ((s.local_ r).echoed = some b))
        (fun r hr => by simp [hr, hall_echo_b r hr])
    -- No second approved → all correct voted(some b) (the only option).
    -- Echo quorum met → vote(some b) send enabled if not already voted.
    -- Can't vote(none) (requires two approved, but only one exists).
    -- Can't vote(some b') for b' ≠ b (requires echo quorum for b', impossible
    --   since countEchoRecv(b') < echoThreshold when all echoed b).
    -- So voted(some b) or not yet voted. At fair deadlock, if not voted,
    -- vote(some b) is enabled → contradiction. So voted(some b).
    -- All correct sent vote(some b) → received → countVoteRecv(p, some b) ≥ n-f
    -- → output(some b) enabled → contradiction
    sorry

/-! ### Why `bca_totality` via `transfers_leads_to` was removed

    The simulation-based `bca_totality` (via `transfers_leads_to` +
    `WeakDivPreserving`) was removed because both `h_ante_transfer`
    cases and the `fair_deadlock_diverges` clause are fundamentally
    unprovable due to the corrupt-sender fairness mismatch (same issue
    as BRB — see BRB_Liveness.lean §"Why brb_totality was removed"):

    * **Bind case**: abstract bind is always fair (`True`), but the
      corresponding concrete init delivery from corrupt senders involves
      only unfair steps. At a concrete fair deadlock with
      `corrupted.length + inputSupport ≥ f+1`, bind IS enabled on the
      ideal side, so `FairlyWeaklyDiverges` genuinely fails.
    * **Rank obligations**: the progress measure approach requires a
      real `bca_progress_measure` where every fair concrete step strictly
      decreases the rank. Designing such a measure is non-trivial and
      orthogonal to the core liveness argument.
    * **h_ante_transfer**: same structural issue as BRB — transferring
      the fair-WF antecedent across the simulation boundary fails when
      abstract labels are fair but corresponding concrete steps are unfair.

    The correct approach (matching BRB) is to prove concrete-level
    liveness directly via the delivery chain. The ideal-level decision
    theorems (`ideal_bca_decision`, `ideal_bca_decision_stutter`) remain
    as standalone results. -/

/-! ## Liveness statements

    The ideal-level decision liveness.

    ### Proof structure

    `ideal_bca_decision`: two steps through `bound_value ≠ none`:
      Step A: input_ready precondition → bound_value eventually set
        (until-or-forever: bind(b) permanently enabled + fair → fires).
      Step B: bound_value set → all correct decided
        (per-proc: output(p, v) enabled + fair → fires;
         finite-max wrapper via Finset.sup).

    `ideal_bca_decision_stutter`: same proof, step-aware h_ante. -/

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

end BCA_Liveness
