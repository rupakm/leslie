import Leslie.PhaseRound

/-! ## LastVoting via PhaseRoundAlg

    Reimplementation of the LastVoting (Paxos / HO model) protocol using
    the `PhaseRoundAlg` multi-phase round framework from `PhaseRound.lean`.

    ### Protocol overview

    LastVoting is the Heard-Of model formulation of Paxos, due to
    Charron-Bost & Schiper (2009). Each **ballot** (logical round)
    consists of 4 **phases**:

    | Phase | Name      | Paxos equivalent | What happens                              |
    |-------|-----------|------------------|-------------------------------------------|
    | 0     | Prepare   | 1a               | Coordinator broadcasts prepare            |
    | 1     | Promise   | 1b               | Processes send lastVote; coordinator      |
    |       |           |                  | collects and picks proposal               |
    | 2     | Accept    | 2a               | Coordinator broadcasts proposal           |
    | 3     | Decide    | 2b               | Processes check majority acceptance       |

    ### Mapping to PhaseRoundAlg

    `PhaseRoundAlg` expects uniform `send` / `update` functions per phase
    that apply to every process. The coordinator asymmetry is handled by
    branching on `round mod n` inside the send/update functions:

    - **Phase 0 (Prepare):**
      - `send`: coordinator sends `PrepareMsg.prepare`, others send
        `PrepareMsg.skip`.
      - `update`: process records `prepared := true` if it received a
        prepare from the coordinator. Resets `accepted := false`.

    - **Phase 1 (Promise):**
      - `send`: every process sends its `lastVote`.
      - `update`: *coordinator* counts promises; if majority (≥ 2 of 3),
        computes proposal via `highestVote` and stores it in local state
        (`proposal` field). Non-coordinator: no change.

    - **Phase 2 (Accept):**
      - `send`: coordinator sends `AcceptMsg.propose v` (from stored
        proposal). Non-coordinator sends `AcceptMsg.skip`.
      - `update`: if process received a `propose v` from the coordinator,
        it accepts: sets `lastVote := (v, round)` and `accepted := true`.

    - **Phase 3 (Decide):**
      - `send`: process sends `DecideMsg.accepted` or `.notAccepted`.
      - `update`: if majority sent `.accepted`, process decides the value
        from its `lastVote` (which matches the proposal).

    ### Coordinator identity

    The coordinator of a ballot is `round mod 3`, where `round` is the
    PhaseRoundAlg round counter. This counter increments once per complete
    4-phase ballot, so it serves as the ballot number.

    ### Design note: proposal in local state

    The coordinator must remember its proposal between Phase 1 (where it
    computes the proposal) and Phase 2 (where it broadcasts it). We store
    the proposal in the local state's `proposal` field. Only the
    coordinator writes this field (in Phase 1's update). Phase 2's send
    reads it back.
-/

open TLA

namespace LastVotingPhased

/-! ### Types -/

/-- 3 processes, as in the original LastVoting. -/
abbrev Proc := Fin 3

/-- Values are natural numbers. -/
abbrev Value := Nat

/-! ### Message types (one per phase) -/

/-- Phase 0: Coordinator broadcasts prepare, others skip. -/
inductive PrepareMsg where
  | prepare
  | skip
  deriving DecidableEq, Repr

/-- Phase 1: Each process sends its lastVote to the coordinator. -/
structure PromiseMsg where
  lastVote : Option (Value × Nat)
  deriving DecidableEq, Repr

/-- Phase 2: Coordinator broadcasts its proposal, others skip. -/
inductive AcceptMsg where
  | propose (v : Value)
  | skip
  deriving DecidableEq, Repr

/-- Phase 3: Each process broadcasts its accept status. -/
inductive DecideMsg where
  | accepted (v : Value)
  | notAccepted
  deriving DecidableEq, Repr

/-- Uniform message type: a sum of all phase messages.
    Using a uniform type avoids dependent-type casts in phase
    definitions and proofs. Each phase sends/receives specific
    constructors and ignores the others. -/
inductive LVMsg where
  | prepare
  | skip
  | promise (lastVote : Option (Value × Nat))
  | propose (v : Value)
  | accepted (v : Value)
  | notAccepted
  deriving DecidableEq, Repr

/-- Uniform message type for all 4 phases. -/
def LVMsgs : PhaseMessages 4 := fun _ => LVMsg

/-! ### Local state -/

/-- Per-process local state.  Extends the original with a `proposal` field
    so the coordinator can store its computed proposal between phases. -/
structure LState where
  /-- Value and ballot of the most recent accept, or `none`. -/
  lastVote : Option (Value × Nat)
  /-- Decided value, once set stays forever. -/
  decided : Option Value
  /-- Whether this process received a prepare for the current ballot. -/
  prepared : Bool
  /-- Whether this process accepted in the current ballot. -/
  accepted : Bool
  /-- Coordinator's proposal (only meaningful for the coordinator process). -/
  proposal : Option Value
  deriving DecidableEq, Repr

/-! ### Helpers -/

/-- The coordinator of a ballot/round `r` is `r % 3`. -/
def coordinator (r : Nat) : Proc := ⟨r % 3, Nat.mod_lt r (by omega)⟩

/-- Majority predicate for 3 processes: at least 2 satisfy the predicate. -/
def hasMaj3 (p : Proc → Bool) : Bool :=
  let cnt := (List.finRange 3).filter (fun r => p r) |>.length
  decide (cnt ≥ 2)

/-- Extract the highest-ballot lastVote from a collection of promises.
    Returns the value from the promise with the highest ballot number,
    or `none` if all promises are empty. -/
def highestVote (promises : Proc → Option PromiseMsg) : Option Value :=
  let collected := (List.finRange 3).filterMap fun p =>
    match promises p with
    | some ⟨some (v, b)⟩ => some (v, b)
    | _ => none
  match collected with
  | [] => none
  | (v, b) :: rest =>
    some (rest.foldl (fun (best : Value × Nat) (cur : Value × Nat) =>
      if cur.2 > best.2 then cur else best) (v, b)).1

/-! ### Phase definitions -/

/-- **Phase 0 — Prepare**
    - Send: coordinator sends `prepare`, others send `skip`.
    - Update: record whether we heard the coordinator's prepare.
      Reset `accepted` for the new ballot. -/
def phase0Send (round : Nat) (p : Proc) (_s : LState) : PrepareMsg :=
  if p = coordinator round then PrepareMsg.prepare else PrepareMsg.skip

def phase0Update (round : Nat) (p : Proc) (s : LState)
    (msgs : Proc → Option PrepareMsg) : LState :=
  let c := coordinator round
  let heardPrepare := match msgs c with
    | some PrepareMsg.prepare => true
    | _ => false
  { s with
    prepared := heardPrepare
    accepted := false
    -- Reset proposal at start of new ballot (for coordinator)
    proposal := if p = c then none else s.proposal }

/-- **Phase 1 — Promise**
    - Send: every process sends its `lastVote`.
    - Update (coordinator): collect promises; if majority, compute proposal
      and store in local state. Non-coordinator: no change. -/
def phase1Send (_round : Nat) (_p : Proc) (s : LState) : PromiseMsg :=
  ⟨s.lastVote⟩

/-- Free value for the coordinator to propose when no previous vote exists.
    We use a fixed default (0). In a real system this would be the
    coordinator's input value. -/
def defaultValue : Value := 0

def phase1Update (round : Nat) (p : Proc) (s : LState)
    (msgs : Proc → Option PromiseMsg) : LState :=
  if p = coordinator round then
    -- Coordinator collects promises
    let promiseCount := (List.finRange 3).filter (fun q =>
      match msgs q with | some _ => true | none => false) |>.length
    if promiseCount ≥ 2 then
      let prop := match highestVote msgs with
        | some v => v
        | none   => defaultValue
      { s with proposal := some prop }
    else
      { s with proposal := none }
  else s

/-- **Phase 2 — Accept**
    - Send: coordinator sends its proposal, others send `skip`.
    - Update: if we heard a proposal from the coordinator, accept it. -/
def phase2Send (round : Nat) (p : Proc) (s : LState) : AcceptMsg :=
  if p = coordinator round then
    match s.proposal with
    | some v => AcceptMsg.propose v
    | none   => AcceptMsg.skip
  else AcceptMsg.skip

def phase2Update (round : Nat) (_p : Proc) (s : LState)
    (msgs : Proc → Option AcceptMsg) : LState :=
  let c := coordinator round
  match msgs c with
  | some (AcceptMsg.propose v) =>
    { s with lastVote := some (v, round), accepted := true }
  | _ => s

/-- **Phase 3 — Decide**
    - Send: process sends whether it accepted.
    - Update: if a majority accepted, decide the proposal value. -/
def phase3Send (_round : Nat) (_p : Proc) (s : LState) : DecideMsg :=
  if s.accepted then
    match s.lastVote with
    | some (v, _) => DecideMsg.accepted v
    | none        => DecideMsg.notAccepted  -- shouldn't happen
  else DecideMsg.notAccepted

def phase3Update (_round : Nat) (_p : Proc) (s : LState)
    (msgs : Proc → Option DecideMsg) : LState :=
  let acceptors : Proc → Bool := fun q =>
    match msgs q with
    | some (DecideMsg.accepted _) => true
    | _ => false
  if hasMaj3 acceptors then
    -- Decide: pick the value from any accepted message we received
    let decidedVal := (List.finRange 3).filterMap (fun q =>
      match msgs q with
      | some (DecideMsg.accepted v) => some v
      | _ => none) |>.head?
    match decidedVal with
    | some v => { s with decided := some v, prepared := false, accepted := false }
    | none   => { s with prepared := false, accepted := false }
  else
    { s with prepared := false, accepted := false }

/-! ### PhaseRoundAlg assembly

    We need to package the 4 phases into a `PhaseRoundAlg`.
    The challenge is that our send/update functions depend on the
    `round` number (for coordinator computation), but the `Phase` type
    only receives `P` and `S`.

    Solution: we thread the round number through the local state.  We
    add a `roundNum` field to local state that tracks the current round.
    Alternatively, we can define the algorithm as a function of round
    number and use the `PhaseRoundState.round` field.

    Actually, `PhaseRoundAlg.phases` gives us `Phase P S (Msgs i)` which
    does NOT have access to the round number. But `phase_step` applies
    the phase to `PhaseRoundState` which has the round number.

    We work around this by storing the round number in the local state.
    Phase 3's update increments it (to stay in sync with the global
    round counter). -/

/-- Extended local state that includes the round number. -/
structure LVState where
  /-- The current round/ballot number, mirrored from global state. -/
  roundNum : Nat
  /-- Core protocol state. -/
  core : LState
  deriving DecidableEq, Repr

/-- Build the 4 phases using the uniform LVMsg type. -/

def lvPhase0 : Phase Proc LVState LVMsg where
  send := fun p s =>
    if p = coordinator s.roundNum then .prepare else .skip
  update := fun p s msgs =>
    let c := coordinator s.roundNum
    let heardPrepare := match msgs c with | some .prepare => true | _ => false
    { s with core := { s.core with
        prepared := heardPrepare
        accepted := false
        proposal := if p = c then none else s.core.proposal } }

def lvPhase1 : Phase Proc LVState LVMsg where
  send := fun _p s => .promise s.core.lastVote
  update := fun p s msgs =>
    if p = coordinator s.roundNum then
      let promiseCount := (List.finRange 3).filter (fun q =>
        match msgs q with | some (.promise _) => true | _ => false) |>.length
      if promiseCount ≥ 2 then
        let collected := (List.finRange 3).filterMap fun q =>
          match msgs q with
          | some (.promise (some vb)) => some vb
          | _ => none
        let prop := match collected with
          | [] => defaultValue
          | (v, b) :: rest =>
            (rest.foldl (fun best cur => if cur.2 > best.2 then cur else best) (v, b)).1
        { s with core := { s.core with proposal := some prop } }
      else { s with core := { s.core with proposal := none } }
    else s

def lvPhase2 : Phase Proc LVState LVMsg where
  send := fun p s =>
    if p = coordinator s.roundNum then
      match s.core.proposal with | some v => .propose v | none => .skip
    else .skip
  update := fun _p s msgs =>
    let c := coordinator s.roundNum
    match msgs c with
    | some (.propose v) =>
      { s with core := { s.core with lastVote := some (v, s.roundNum), accepted := true } }
    | _ => s

def lvPhase3 : Phase Proc LVState LVMsg where
  send := fun _p s =>
    if s.core.accepted then
      match s.core.lastVote with
      | some (v, _) => .accepted v
      | none => .notAccepted
    else .notAccepted
  update := fun _p s msgs =>
    let acceptors : Proc → Bool := fun q =>
      match msgs q with | some (.accepted _) => true | _ => false
    let core' :=
      if hasMaj3 acceptors then
        let decidedVal := (List.finRange 3).filterMap (fun q =>
          match msgs q with | some (.accepted v) => some v | _ => none) |>.head?
        match decidedVal with
        | some v => { s.core with decided := some v, prepared := false, accepted := false }
        | none => { s.core with prepared := false, accepted := false }
      else { s.core with prepared := false, accepted := false }
    { roundNum := s.roundNum + 1, core := core' }

/-- The LastVoting algorithm as a `PhaseRoundAlg`. -/
def lvAlg : PhaseRoundAlg Proc LVState 4 LVMsgs where
  init := fun _p s =>
    s.roundNum = 0 ∧
    s.core = { lastVote := none, decided := none,
               prepared := false, accepted := false,
               proposal := none }
  phases := fun i =>
    if i.val = 0 then lvPhase0
    else if i.val = 1 then lvPhase1
    else if i.val = 2 then lvPhase2
    else lvPhase3

/-! ### Communication predicate

    LastVoting works under lossy communication — the safety proof does
    not require any communication predicate. Liveness would need
    coordinator-specific delivery guarantees, but we only prove safety. -/

def lvComm : PhaseCommPred Proc 4 := fun _ _ _ => True

/-- The complete PhaseRoundSpec for LastVoting. -/
def lvSpec : PhaseRoundSpec Proc LVState 4 LVMsgs where
  alg := lvAlg
  comm := lvComm

/-- Convert to a Leslie `Spec`. -/
def lvLeslieSpec : Spec (PhaseRoundState Proc LVState 4) :=
  lvSpec.toSpec (by omega)

/-! ### Safety property -/

/-- Agreement: if two processes have decided, they decided the same value. -/
def agreement (s : PhaseRoundState Proc LVState 4) : Prop :=
  ∀ (p q : Proc) (v w : Value),
    (s.locals p).core.decided = some v →
    (s.locals q).core.decided = some w →
    v = w

/-! ### Invariant

    The inductive invariant combines several properties:

    (A) **Agreement**: all existing decisions agree.

    (B) **Accepted consistency**: if a process has `accepted = true`,
        its `lastVote` matches the current ballot's proposal.

    (C) **Phase 3 consistency**: in phase 3, acceptors' lastVotes match
        the proposal.

    (D) **Decision-proposal consistency**: any existing decision agrees
        with the current proposal (if a majority accepted).

    (E) **Round synchronization**: `roundNum` in local state matches the
        global round counter. -/

def lv_inv (s : PhaseRoundState Proc LVState 4) : Prop :=
  -- (A) Agreement on all decisions made so far
  agreement s ∧
  -- (B) If a process accepted in this ballot, its lastVote matches a proposal
  (∀ p : Proc, (s.locals p).core.accepted = true →
    ∃ v b, (s.locals p).core.lastVote = some (v, b) ∧
      b = s.round) ∧
  -- (C) Phase 3 consistency
  (s.phase = ⟨3, by omega⟩ →
    ∀ p : Proc, (s.locals p).core.accepted = true →
    ∃ v, (s.locals p).core.lastVote = some (v, s.round)) ∧
  -- (D) Decision-proposal consistency: existing decisions agree with any
  --     new majority accept in phase 3
  (∀ p : Proc, ∀ v, (s.locals p).core.decided = some v →
    s.phase = ⟨3, by omega⟩ →
    hasMaj3 (fun q => (s.locals q).core.accepted) = true →
    -- All acceptors have the same value
    ∀ q : Proc, (s.locals q).core.accepted = true →
    ∃ w, (s.locals q).core.lastVote = some (w, s.round) ∧ w = v) ∧
  -- (E) Round synchronization
  (∀ p : Proc, (s.locals p).roundNum = s.round) ∧
  -- (F') Acceptance only at phase 3: if accepted, we must be in phase 3
  (∀ p : Proc, (s.locals p).core.accepted = true → s.phase = ⟨3, by omega⟩) ∧
  -- (F) Uniform value: at phase 3, all accepted processes agree on lastVote value
  (s.phase = ⟨3, by omega⟩ →
    ∀ (p q : Proc) (vp vq : Value),
    (s.locals p).core.accepted = true →
    (s.locals q).core.accepted = true →
    (s.locals p).core.lastVote = some (vp, s.round) →
    (s.locals q).core.lastVote = some (vq, s.round) →
    vp = vq)

/-! ### Invariant proofs -/

theorem lv_inv_init :
    ∀ s, lvLeslieSpec.init s → lv_inv s := by
  intro s ⟨hround, hphase, hinit⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Agreement: vacuously true, no decisions
    intro p q v w hv hw
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hv ; simp at hv
  · -- Accepted consistency: vacuously true, no accepts
    intro p hacc
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hacc ; simp at hacc
  · -- Phase 3 consistency: phase = 0 ≠ 3
    intro hph ; simp [hphase] at hph
  · -- Decision-proposal consistency: vacuously true
    intro p v hv
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hv ; simp at hv
  · -- Round synchronization
    intro p
    have hp := (hinit p).1
    simp at hp ; rw [hround, hp]
  · -- (F') Acceptance only at phase 3: vacuous, no accepts at init
    intro p hacc
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hacc ; simp at hacc
  · -- (F) Uniform value: phase = 0 ≠ 3
    intro hph ; simp [hphase] at hph

/-- The main invariant preservation theorem.
    Each of the 4 phase transitions preserves `lv_inv`. -/
theorem lv_inv_step :
    ∀ s ho, lv_inv s → lvComm s.round s.phase ho →
    ∀ s', phase_step lvAlg ho s s' → lv_inv s' := by
  intro s ho ⟨h_agree, h_acc, h_ph3, h_dec_prop, h_rsync, h_acc_ph3, h_uniform⟩ _ s' ⟨hadvance, hlocals⟩
  -- Determine which phase we're in
  have hph : s.phase.val = 0 ∨ s.phase.val = 1 ∨ s.phase.val = 2 ∨ s.phase.val = 3 := by
    have := s.phase.isLt ; omega
  rcases hph with hph0 | hph1 | hph2 | hph3
  · ---- Phase 0 → Phase 1 (Prepare → Promise) ----
    -- Phase 0 resets `accepted := false`, sets `prepared`, resets coordinator's proposal.
    -- No new decisions, no new accepts. Invariant mostly trivially preserved.
    have hph_eq : s.phase = ⟨0, by omega⟩ := Fin.ext hph0
    have h_phase : lvAlg.phases s.phase = lvPhase0 := by simp [lvAlg, hph_eq]
    -- s' has phase = 1, same round
    have hs'_phase : s'.phase = ⟨1, by omega⟩ := by
      simp [hph0] at hadvance ; exact hadvance.2
    have hs'_round : s'.round = s.round := by
      simp [hph0] at hadvance ; exact hadvance.1
    -- What hlocals says for each process after unfolding
    have hlocals' : ∀ p, s'.locals p = lvPhase0.update p (s.locals p)
        (phase_delivered lvPhase0 s.locals ho p) := by
      intro p ; have := hlocals p ; rwa [h_phase] at this
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (A) Agreement: no new decisions (phase0Update doesn't touch `decided`)
      intro p q v w hv hw
      rw [hlocals' p] at hv ; rw [hlocals' q] at hw
      simp [lvPhase0, phase0Update, phase_delivered] at hv hw
      exact h_agree p q v w hv hw
    · -- (B) Accepted consistency: accepted is reset to false
      intro p hacc
      rw [hlocals' p] at hacc
      simp [lvPhase0, phase0Update, phase_delivered] at hacc
    · -- (C) Phase 3 consistency: s'.phase = 1 ≠ 3, vacuous
      intro hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (D) Decision-proposal: s'.phase = 1 ≠ 3, vacuous
      intro p v _ hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (E) Round sync: round unchanged, roundNum unchanged by phase0Update
      intro p ; rw [hlocals' p]
      simp [lvPhase0, phase0Update, phase_delivered, hs'_round]
      exact h_rsync p
    · -- (F') Phase 0 resets accepted to false
      intro p hacc ; rw [hlocals' p] at hacc
      simp [lvPhase0, phase_delivered] at hacc
    · -- (F) s'.phase = 1 ≠ 3, vacuous
      intro hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
  · ---- Phase 1 → Phase 2 (Promise → Accept) ----
    -- Coordinator collects promises and stores proposal. Others unchanged.
    -- No new decisions, no new accepts.
    have hph_eq : s.phase = ⟨1, by omega⟩ := Fin.ext hph1
    have h_phase : lvAlg.phases s.phase = lvPhase1 := by simp [lvAlg, hph_eq]
    have hs'_phase : s'.phase = ⟨2, by omega⟩ := by
      simp [hph1] at hadvance ; exact hadvance.2
    have hs'_round : s'.round = s.round := by
      simp [hph1] at hadvance ; exact hadvance.1
    have hlocals' : ∀ p, s'.locals p = lvPhase1.update p (s.locals p)
        (phase_delivered lvPhase1 s.locals ho p) := by
      intro p ; have := hlocals p ; rwa [h_phase] at this
    -- Helper: lvPhase1 preserves accepted
    have h_acc_pres : ∀ r, (s'.locals r).core.accepted = (s.locals r).core.accepted := by
      intro r ; rw [hlocals' r] ; simp only [lvPhase1, phase_delivered]
      split <;> (try split) <;> simp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (A) Agreement: lvPhase1.update only changes `proposal`, not `decided`
      intro p q v w hv hw
      have h_dec : ∀ r, (s'.locals r).core.decided = (s.locals r).core.decided := by
        intro r ; rw [hlocals' r]
        simp only [lvPhase1, phase_delivered]
        split <;> (try split) <;> simp
      rw [h_dec p] at hv ; rw [h_dec q] at hw
      exact h_agree p q v w hv hw
    · -- (B) Accepted consistency: lvPhase1.update doesn't change `accepted` or `lastVote`
      intro p hacc
      rw [h_acc_pres p] at hacc
      obtain ⟨v, b, hvb, hb⟩ := h_acc p hacc
      have h_lv_pres : (s'.locals p).core.lastVote = (s.locals p).core.lastVote := by
        rw [hlocals' p] ; simp only [lvPhase1, phase_delivered]
        split <;> (try split) <;> simp
      exact ⟨v, b, by rw [h_lv_pres, hvb], by rw [hs'_round, hb]⟩
    · -- (C) Phase 3: s'.phase = 2 ≠ 3, vacuous
      intro hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (D) Decision-proposal: s'.phase = 2 ≠ 3, vacuous
      intro p v _ hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (E) Round sync: lvPhase1.update doesn't change roundNum
      intro p ; rw [hlocals' p, hs'_round]
      simp only [lvPhase1, phase_delivered]
      split <;> (try split) <;> simp [h_rsync p]
    · -- (F') accepted preserved → use h_acc_ph3 on pre-state
      intro p hacc' ; rw [h_acc_pres p] at hacc'
      have := h_acc_ph3 p hacc'
      rw [this] at hph1 ; simp at hph1
    · -- (F) s'.phase = 2 ≠ 3, vacuous
      intro hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
  · ---- Phase 2 → Phase 3 (Accept → Decide) ----
    -- Some processes accept the coordinator's proposal.
    -- No new decisions yet (decisions happen in Phase 3).
    -- The hard part: establishing conjunct (D) for Phase 3.
    have hph_eq : s.phase = ⟨2, by omega⟩ := Fin.ext hph2
    have h_phase : lvAlg.phases s.phase = lvPhase2 := by simp [lvAlg, hph_eq]
    have hs'_phase : s'.phase = ⟨3, by omega⟩ := by
      simp [hph2] at hadvance ; exact hadvance.2
    have hs'_round : s'.round = s.round := by
      simp [hph2] at hadvance ; exact hadvance.1
    have hlocals' : ∀ p, s'.locals p = lvPhase2.update p (s.locals p)
        (phase_delivered lvPhase2 s.locals ho p) := by
      intro p ; have := hlocals p ; rwa [h_phase] at this
    -- Helper: by (F'), no process is accepted at phase 2
    have h_no_acc : ∀ r, (s.locals r).core.accepted = false := by
      intro r ; by_contra h
      have := h_acc_ph3 r (by revert h ; cases (s.locals r).core.accepted <;> simp)
      rw [this] at hph2 ; simp at hph2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (A) Agreement: lvPhase2.update doesn't change `decided`
      intro p q v w hv hw
      have h_dec : ∀ r, (s'.locals r).core.decided = (s.locals r).core.decided := by
        intro r ; rw [hlocals' r]
        simp only [lvPhase2, phase_delivered]
        split <;> simp
      rw [h_dec p] at hv ; rw [h_dec q] at hw
      exact h_agree p q v w hv hw
    · -- (B) Accepted: if accepted in s', lastVote matches current round
      intro p hacc
      rw [hlocals' p] at hacc
      simp only [lvPhase2, phase_delivered] at hacc
      rw [hlocals' p]
      simp only [lvPhase2, phase_delivered]
      split
      · case _ v' _ =>
        exact ⟨v', (s.locals p).roundNum,
               by simp [lvPhase2, phase_delivered],
               by rw [hs'_round, h_rsync p]⟩
      · case _ _ =>
        simp at hacc
        obtain ⟨v, b, hvb, hb⟩ := h_acc p hacc
        exact ⟨v, b, hvb, by rw [hs'_round] ; exact hb⟩
    · -- (C) Phase 3 consistency
      intro _ p hacc
      rw [hlocals' p] at hacc ⊢
      simp only [lvPhase2, phase_delivered] at hacc ⊢
      split
      · case _ v' _ =>
        exact ⟨v', by simp ; rw [h_rsync p, hs'_round]⟩
      · case _ _ =>
        simp at hacc
        obtain ⟨v, b, hvb, hb⟩ := h_acc p hacc
        exact ⟨v, by rw [hvb, hb, hs'_round]⟩
    · -- (D) Decision-proposal consistency: cross-ballot Paxos invariant.
      -- This requires that the coordinator's proposal agrees with prior
      -- decisions. The argument uses quorum intersection at the Promise
      -- phase and ballot induction on `highestVote`. We leave this as
      -- sorry, noting the mathematical argument in `proposals_respect_votes`.
      sorry
    · -- (E) Round sync: lvPhase2.update doesn't change roundNum
      intro p ; rw [hlocals' p, hs'_round]
      simp only [lvPhase2, phase_delivered]
      split <;> simp [h_rsync p]
    · -- (F') accepted → phase = 3. s'.phase = 3, so just need True.
      intro _ _ ; exact hs'_phase
    · -- (F) Uniform value: all accepted in s' got the same proposal from coordinator.
      -- By h_no_acc, no process was accepted in s. So any accepted in s' must be
      -- newly accepted via lvPhase2.update receiving .propose from the coordinator.
      -- The coordinator sends the same message to all, so the value is uniform.
      intro _ p q vp vq hacc_p hacc_q hlv_p hlv_q
      -- Show: (s'.locals p).core.lastVote = (s'.locals q).core.lastVote
      -- Then from hlv_p and hlv_q we get vp = vq.
      suffices h_eq : (s'.locals p).core.lastVote = (s'.locals q).core.lastVote by
        rw [hlv_p, hlv_q] at h_eq
        simp only [Option.some.injEq, Prod.mk.injEq] at h_eq
        exact h_eq.1
      -- Prove both lastVotes are the same by showing both come from the same function
      -- applied to the same coordinator state.
      -- lvPhase2.update r s msgs = match msgs c with | some (.propose v) => {lastVote := (v,round),...} | _ => s
      -- For accepted in s', must be in .propose branch (since h_no_acc gives acc=false in else branch)
      -- The coordinator's message to both p and q is lvPhase2.send c (s.locals c), same for both.
      rw [hlocals' p, hlocals' q]
      simp only [lvPhase2, phase_delivered, h_rsync p, h_rsync q]
      -- Now both sides match on the coordinator's message, potentially different HO.
      -- But if both sides result in accepted=true, both took the .propose branch.
      -- Use hacc_p/hacc_q to know which branch was taken.
      rw [hlocals' p] at hacc_p ; rw [hlocals' q] at hacc_q
      simp only [lvPhase2, phase_delivered, h_rsync p, h_rsync q] at hacc_p hacc_q
      -- Now case-split on the coordinator's proposal
      cases h_prop : (s.locals (coordinator s.round)).core.proposal with
      | none =>
        -- Coordinator has no proposal, sends .skip. No one gets accepted.
        exfalso
        simp only [lvPhase2, h_rsync (coordinator s.round), h_prop] at hacc_p
        -- After simp, the coordinator sends .skip.
        -- If ho p c: match (some .skip) → not .propose → state unchanged → accepted = false
        -- If not ho: match none → state unchanged → accepted = false
        by_cases hho : ho p (coordinator s.round) = true
        · simp [hho, h_no_acc p] at hacc_p
        · have hf : ho p (coordinator s.round) = false := by
            revert hho ; cases ho p (coordinator s.round) <;> simp
          simp [hf, h_no_acc p] at hacc_p
      | some v₀ =>
        -- Coordinator sends .propose v₀
        -- Both p and q (if accepted) received .propose v₀ and set lastVote = (v₀, round)
        -- Their lastVote is the same.
        simp only [lvPhase2, h_rsync (coordinator s.round), h_prop, h_rsync p, h_rsync q]
        -- After simp, both sides should be:
        -- match (if ho r c then some (.propose v₀) else none) with | some (.propose v) => ... | _ => ...
        -- For the goal (lastVote equality), both sides have the same structure
        -- but with different ho. However, the .propose value v₀ is the same.
        -- Split on ho p c and ho q c
        by_cases hp_ho : ho p (coordinator s.round) = true <;>
          by_cases hq_ho : ho q (coordinator s.round) = true
        · -- Both heard: lastVote = (v₀, round) for both. Equal.
          simp [hp_ho, hq_ho]
        · -- p heard, q didn't: q's accepted = false. Contradiction.
          simp [hq_ho, h_no_acc q] at hacc_q
        · -- p didn't hear: p's accepted = false. Contradiction.
          simp [hp_ho, h_no_acc p] at hacc_p
        · -- Neither heard: both accepted = false. Contradiction.
          simp [hp_ho, h_no_acc p] at hacc_p
  · ---- Phase 3 → Phase 0 (Decide → Prepare of next round) ----
    -- Majority decision happens here. Hardest case for agreement.
    have hph_eq : s.phase = ⟨3, by omega⟩ := Fin.ext hph3
    have h_phase : lvAlg.phases s.phase = lvPhase3 := by
      show (if s.phase.val = 0 then lvPhase0
            else if s.phase.val = 1 then lvPhase1
            else if s.phase.val = 2 then lvPhase2
            else lvPhase3) = lvPhase3
      simp [show s.phase.val ≠ 0 by omega,
            show s.phase.val ≠ 1 by omega, show s.phase.val ≠ 2 by omega]
    have hs'_round : s'.round = s.round + 1 := by
      simp [hph3] at hadvance ; exact hadvance.1
    have hlocals' : ∀ p, s'.locals p = lvPhase3.update p (s.locals p)
        (phase_delivered lvPhase3 s.locals ho p) := by
      intro p ; have := hlocals p ; rwa [h_phase] at this
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (A) Agreement: new decisions must agree with old
      intro p q v w hv hw
      -- Helper: extract decided from post-state.
      -- lvPhase3.update either sets decided := some v (majority + head?) or keeps old.
      -- A process's decided in s' is either:
      --   (i) a new value from head? of accepted messages (if hasMaj3 in HO set)
      --   (ii) the old value from s (unchanged)
      -- Helper: characterize each process's decided in s'.
      -- Either old (from s) or new (from head? of accepted messages).
      -- For new decisions, also extract that hasMaj3 held on received.
      have h_dec_or : ∀ r val, (s'.locals r).core.decided = some val →
          (s.locals r).core.decided = some val ∨
          (∃ msgs_accepted,
            msgs_accepted = (List.finRange 3).filterMap (fun q' =>
              match (phase_delivered lvPhase3 s.locals ho r q') with
              | some (.accepted v') => some v'
              | _ => none) ∧
            msgs_accepted.head? = some val ∧
            -- hasMaj3 held on the received messages
            hasMaj3 (fun q' => match (phase_delivered lvPhase3 s.locals ho r q') with
              | some (.accepted _) => true | _ => false) = true) := by
        intro r val hr
        rw [hlocals' r] at hr
        simp only [lvPhase3, phase_delivered] at hr
        split at hr
        · -- hasMaj3 branch
          case _ hmaj =>
          split at hr
          · -- decidedVal = some val: new decision
            case _ v' hhead =>
            right ; simp at hr ; exact ⟨_, rfl, by rw [← hr] ; exact hhead, hmaj⟩
          · -- decidedVal = none: old decision preserved
            left ; simp at hr ; exact hr
        · -- no majority: old decision preserved
          left ; simp at hr ; exact hr
      -- Now case-split on whether p's and q's decisions are old or new
      rcases h_dec_or p v hv with hp_old | ⟨mp, hmp_eq, hp_new, hp_maj⟩
      · -- p's decision is old (from pre-state)
        rcases h_dec_or q w hw with hq_old | ⟨mq, hmq_eq, hq_new, hq_maj⟩
        · -- Both old: use pre-state agreement
          exact h_agree p q v w hp_old hq_old
        · -- p old, q new: h_dec_prop gives all acceptors have value v
          -- q's new decision from head? of accepted values in q's HO set.
          -- Step 1: q's majority implies global majority accepted
          -- q decided via head? of mq. mq is the filterMap of accepted values
          -- from q's HO set. For mq to be nonempty, ≥ 1 sender sent .accepted.
          -- Actually, the full structure: q decided because hasMaj3 on received,
          -- meaning ≥ 2 in q's HO have accepted = true. These are globally accepted.
          -- So hasMaj3 of global accepted holds.
          -- h_dec_prop + global majority → all acceptors have value v
          -- → q's received accepted values are all v → head? = v = w
          -- Step 1: HO-filtered majority → global majority
          -- h_impl: HO-filtered accepted implies globally accepted
          have h_impl : ∀ r : Fin 3,
              (match phase_delivered lvPhase3 s.locals ho q r with
                | some (.accepted _) => true | _ => false) = true →
              (s.locals r).core.accepted = true := by
            intro r hr_filt
            simp only [phase_delivered, lvPhase3] at hr_filt
            by_cases hho : ho q r = true
            · simp only [hho, ite_true] at hr_filt
              by_cases hacc : (s.locals r).core.accepted = true
              · exact hacc
              · have hf : (s.locals r).core.accepted = false := by
                  revert hacc ; cases (s.locals r).core.accepted <;> simp
                simp [hf] at hr_filt
            · have hf : ho q r = false := by revert hho ; cases ho q r <;> simp
              simp [hf] at hr_filt
          have h_mono := filter_length_mono (List.finRange 3) _ _ h_impl
          have h_global_maj : hasMaj3 (fun r => (s.locals r).core.accepted) = true := by
            unfold hasMaj3 at hq_maj ⊢
            simp only [decide_eq_true_eq] at hq_maj ⊢
            exact Nat.le_trans hq_maj h_mono
          -- Step 2: all globally accepted have value v
          have h_all_v := h_dec_prop p v hp_old hph_eq h_global_maj
          -- Step 3: every value in mq is v (each came from an accepted sender)
          have h_mq_all_v : ∀ x ∈ mq, x = v := by
            intro x hx ; rw [hmq_eq] at hx
            simp only [List.mem_filterMap, List.mem_finRange, true_and] at hx
            obtain ⟨r, hr⟩ := hx
            simp only [phase_delivered, lvPhase3] at hr
            by_cases hho : ho q r = true
            · simp only [hho, ite_true] at hr
              by_cases hacc_r : (s.locals r).core.accepted = true
              · obtain ⟨w', hw', hv'⟩ := h_all_v r hacc_r
                simp only [hacc_r, ite_true] at hr
                revert hr ; rw [hw'] ; simp ; intro hr ; rw [← hr] ; exact hv'
              · have hf : (s.locals r).core.accepted = false := by
                  revert hacc_r ; cases (s.locals r).core.accepted <;> simp
                simp [hf] at hr
            · have hf : ho q r = false := by revert hho ; cases ho q r <;> simp
              simp [hf] at hr
          -- Step 4: head? mq = some w, so w = v
          have hw_in : w ∈ mq := by
            cases mq with
            | nil => simp at hq_new
            | cons a as =>
              simp [List.head?] at hq_new
              subst hq_new ; exact List.Mem.head _
          exact (h_mq_all_v w hw_in).symm
      · -- p's decision is new
        rcases h_dec_or q w hw with hq_old | ⟨mq, hmq_eq, hq_new, hq_maj⟩
        · -- p new, q old: symmetric to old-new
          -- h_impl: HO-filtered accepted implies globally accepted
          have h_impl : ∀ r : Fin 3,
              (match phase_delivered lvPhase3 s.locals ho p r with
                | some (.accepted _) => true | _ => false) = true →
              (s.locals r).core.accepted = true := by
            intro r hr_filt
            simp only [phase_delivered, lvPhase3] at hr_filt
            by_cases hho : ho p r = true
            · simp only [hho, ite_true] at hr_filt
              by_cases hacc : (s.locals r).core.accepted = true
              · exact hacc
              · have hf : (s.locals r).core.accepted = false := by
                  revert hacc ; cases (s.locals r).core.accepted <;> simp
                simp [hf] at hr_filt
            · have hf : ho p r = false := by revert hho ; cases ho p r <;> simp
              simp [hf] at hr_filt
          have h_mono := filter_length_mono (List.finRange 3) _ _ h_impl
          have h_global_maj : hasMaj3 (fun r => (s.locals r).core.accepted) = true := by
            unfold hasMaj3 at hp_maj ⊢
            simp only [decide_eq_true_eq] at hp_maj ⊢
            exact Nat.le_trans hp_maj h_mono
          have h_all_w := h_dec_prop q w hq_old hph_eq h_global_maj
          -- All values in mp are w (each came from an accepted sender)
          have h_mp_all_w : ∀ x ∈ mp, x = w := by
            intro x hx ; rw [hmp_eq] at hx
            simp only [List.mem_filterMap, List.mem_finRange, true_and] at hx
            obtain ⟨r, hr⟩ := hx
            simp only [phase_delivered, lvPhase3] at hr
            by_cases hho : ho p r = true
            · simp only [hho, ite_true] at hr
              by_cases hacc_r : (s.locals r).core.accepted = true
              · obtain ⟨w', hw', hv'⟩ := h_all_w r hacc_r
                simp only [hacc_r, ite_true] at hr
                revert hr ; rw [hw'] ; simp ; intro hr ; rw [← hr] ; exact hv'
              · have hf : (s.locals r).core.accepted = false := by
                  revert hacc_r ; cases (s.locals r).core.accepted <;> simp
                simp [hf] at hr
            · have hf : ho p r = false := by revert hho ; cases ho p r <;> simp
              simp [hf] at hr
          -- v is in mp (it's head?)
          have hv_in : v ∈ mp := by
            cases mp with
            | nil => simp at hp_new
            | cons a as =>
              simp [List.head?] at hp_new
              subst hp_new ; exact List.Mem.head _
          exact h_mp_all_w v hv_in
        · -- Both new: use (F) — all accepted have same value
          -- Both mp and mq contain values from accepted processes.
          -- By (F), any two accepted processes have the same lastVote value.
          -- So all elements of mp and mq are the same value.
          -- Therefore head? mp = head? mq, giving v = w.
          -- Step 1: extract an accepted process from mp
          have hv_in : v ∈ mp := by
            cases mp with
            | nil => simp at hp_new
            | cons a as =>
              simp [List.head?] at hp_new ; subst hp_new ; exact List.Mem.head _
          have hw_in : w ∈ mq := by
            cases mq with
            | nil => simp at hq_new
            | cons a as =>
              simp [List.head?] at hq_new ; subst hq_new ; exact List.Mem.head _
          -- Step 2: v came from an accepted process r₁, w from r₂
          rw [hmp_eq] at hv_in
          simp only [List.mem_filterMap, List.mem_finRange, true_and] at hv_in
          obtain ⟨r₁, hr₁⟩ := hv_in
          rw [hmq_eq] at hw_in
          simp only [List.mem_filterMap, List.mem_finRange, true_and] at hw_in
          obtain ⟨r₂, hr₂⟩ := hw_in
          -- Step 3: extract that r₁ and r₂ are accepted with specific lastVote values
          -- r₁ sent .accepted v, meaning r₁ has accepted = true and lastVote = some (v, _)
          simp only [phase_delivered, lvPhase3] at hr₁ hr₂
          -- For r₁:
          have h_r₁_acc : (s.locals r₁).core.accepted = true := by
            by_cases hho : ho p r₁ = true
            · simp only [hho, ite_true] at hr₁
              by_cases hacc : (s.locals r₁).core.accepted = true
              · exact hacc
              · have hf : (s.locals r₁).core.accepted = false := by
                  revert hacc ; cases (s.locals r₁).core.accepted <;> simp
                simp [hf] at hr₁
            · have hf : ho p r₁ = false := by revert hho ; cases ho p r₁ <;> simp
              simp [hf] at hr₁
          have h_r₂_acc : (s.locals r₂).core.accepted = true := by
            by_cases hho : ho q r₂ = true
            · simp only [hho, ite_true] at hr₂
              by_cases hacc : (s.locals r₂).core.accepted = true
              · exact hacc
              · have hf : (s.locals r₂).core.accepted = false := by
                  revert hacc ; cases (s.locals r₂).core.accepted <;> simp
                simp [hf] at hr₂
            · have hf : ho q r₂ = false := by revert hho ; cases ho q r₂ <;> simp
              simp [hf] at hr₂
          -- Step 4: by (C), r₁ and r₂ have lastVote = some (v₁, round) and some (v₂, round)
          obtain ⟨v₁, hv₁⟩ := h_ph3 hph_eq r₁ h_r₁_acc
          obtain ⟨v₂, hv₂⟩ := h_ph3 hph_eq r₂ h_r₂_acc
          -- Step 5: by (F), v₁ = v₂
          have hv_eq := h_uniform hph_eq r₁ r₂ v₁ v₂ h_r₁_acc h_r₂_acc hv₁ hv₂
          -- Step 6: trace v back to v₁ and w back to v₂
          have hv_val : v = v₁ := by
            by_cases hho : ho p r₁ = true
            · simp [hho, h_r₁_acc, hv₁] at hr₁ ; exact hr₁.symm
            · have hf : ho p r₁ = false := by revert hho ; cases ho p r₁ <;> simp
              simp [hf] at hr₁
          have hw_val : w = v₂ := by
            by_cases hho : ho q r₂ = true
            · simp [hho, h_r₂_acc, hv₂] at hr₂ ; exact hr₂.symm
            · have hf : ho q r₂ = false := by revert hho ; cases ho q r₂ <;> simp
              simp [hf] at hr₂
          rw [hv_val, hw_val, hv_eq]
    · -- (B) Accepted: lvPhase3.update always sets accepted := false
      intro p hacc
      have h_false : (s'.locals p).core.accepted = false := by
        rw [hlocals' p]
        simp [lvPhase3, hasMaj3, phase_delivered]
        split <;> (try split) <;> simp
      simp [h_false] at hacc
    · -- (C) s'.phase = 0 ≠ 3 (after phase 3 wraps to 0), vacuous
      intro hph3'
      have : s'.phase = ⟨0, by omega⟩ := by simp [hph3] at hadvance ; exact hadvance.2
      rw [this] at hph3' ; simp at hph3'
    · -- (D) s'.phase = 0 ≠ 3, vacuous
      intro p v _ hph3'
      have : s'.phase = ⟨0, by omega⟩ := by simp [hph3] at hadvance ; exact hadvance.2
      rw [this] at hph3' ; simp at hph3'
    · -- (E) Round sync: roundNum incremented by lvPhase3.update
      intro p ; rw [hlocals' p, hs'_round]
      simp only [lvPhase3, phase_delivered, h_rsync p]
    · -- (F') Phase 3 resets accepted to false; s'.phase = 0 ≠ 3
      intro p hacc
      have h_false : (s'.locals p).core.accepted = false := by
        rw [hlocals' p]
        simp [lvPhase3, hasMaj3, phase_delivered]
        split <;> (try split) <;> simp
      simp [h_false] at hacc
    · -- (F) s'.phase = 0 ≠ 3, vacuous
      intro hph3'
      have : s'.phase = ⟨0, by omega⟩ := by simp [hph3] at hadvance ; exact hadvance.2
      rw [this] at hph3' ; simp at hph3'

/-! ### Agreement theorem -/

/-- Agreement is an invariant of the phased LastVoting protocol. -/
theorem lv_agreement :
    pred_implies lvLeslieSpec.safety [tlafml| □ ⌜agreement⌝] := by
  -- Prove the stronger combined invariant, then project
  suffices h : pred_implies lvLeslieSpec.safety [tlafml| □ ⌜lv_inv⌝] by
    intro e he n
    exact (h e he n).1
  apply phase_round_invariant lvSpec (by omega)
  · exact lv_inv_init
  · exact lv_inv_step

/-! ### Quorum intersection (reused from the framework)

    The `cross_phase_quorum_intersection` theorem from `PhaseRound.lean`
    provides the key quorum argument: any two majority HO sets among
    `Fin 3` must share a process. This is essential for Paxos safety:
    the promise quorum (Phase 1) and accept quorum (Phase 3) overlap.

    We instantiate it here for `n = 3` for documentation purposes. -/

/-- Two majorities of 3 processes must intersect. -/
theorem maj3_intersect (p₁ p₂ : Proc → Bool)
    (h₁ : ((List.finRange 3).filter fun r => p₁ r).length ≥ 2)
    (h₂ : ((List.finRange 3).filter fun r => p₂ r).length ≥ 2) :
    ∃ r : Proc, p₁ r = true ∧ p₂ r = true := by
  by_contra h
  have h' : ∀ r, ¬(p₁ r = true ∧ p₂ r = true) := fun r hr => h ⟨r, hr⟩
  have h_sum := filter_disjoint_length_le
    (fun r => p₁ r) (fun r => p₂ r) (List.finRange 3) h'
  have h_len : (List.finRange 3).length = 3 := List.length_finRange
  omega

/-! ### Full cross-ballot invariant (stated, proof deferred)

    The key Paxos safety argument: if value `v` was accepted by a majority
    in ballot `b`, then any proposal in ballot `b' > b` must also propose `v`.

    The argument uses quorum intersection at the Promise phase: the
    coordinator of `b'` collects promises from a majority; by
    `maj3_intersect`, this majority overlaps with the majority that
    accepted `v` in ballot `b`. The `highestVote` selection ensures the
    coordinator picks `v` (or a value from an even higher ballot, which
    by induction is also `v`).

    This requires a history-tracking strengthening of the invariant,
    which we leave as sorry. -/

def proposals_respect_votes (s : PhaseRoundState Proc LVState 4) : Prop :=
  ∀ v b,
    ((List.finRange 3).filter fun p =>
      decide ((s.locals p).core.lastVote = some (v, b))).length ≥ 2 →
    -- For any process that is the coordinator with a proposal
    ∀ p : Proc, (s.locals p).core.proposal ≠ none →
    (s.locals p).core.proposal = some v

theorem proposals_respect_votes_invariant :
    pred_implies lvLeslieSpec.safety
      [tlafml| □ ⌜proposals_respect_votes⌝] := by
  sorry

end LastVotingPhased
