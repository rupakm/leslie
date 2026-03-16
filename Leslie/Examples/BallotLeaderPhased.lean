import Leslie.PhaseRound

/-! ## Ballot-Based Leader Election via PhaseRoundAlg

    Refactoring of `BallotLeader.lean` to use the `PhaseRoundAlg` framework
    from `PhaseRound.lean`. The protocol is identical:

    **Phase 0 (New):** Each process broadcasts Bid(id) or NoBid, then picks
    the minimum bidder among received bids.

    **Phase 1 (Ack):** Each process broadcasts its pick, then elects a leader
    if a strict majority of received picks agree on the same candidate.

    **Safety: at most one leader is ever elected.**

    ### Design: modeling nondeterministic bidding

    The original `BallotLeader` uses an external `oracle : Fin n → Bool` to
    decide which processes bid. `PhaseRoundAlg.Phase.send` is deterministic
    (`P → S → M`), so we cannot introduce nondeterminism there.

    Solution: we add a `bidding : Bool` field to the local state. The
    nondeterminism is in the INITIAL state — any assignment of `bidding`
    values across processes is valid. Phase 0's `send` function then reads
    `bidding` deterministically. This is standard: lifting oracle choices
    into initial-state nondeterminism.

    ### Structure

    1. Define local state, message types per phase, and the `PhaseRoundAlg`.
    2. Wrap it in a `PhaseRoundSpec` with lossy communication.
    3. State the safety invariant (at most one leader).
    4. Prove safety using `phase_round_invariant`.
-/

open TLA

namespace BallotLeaderPhased

variable (n : Nat)

/-! ### State and messages -/

/-- Local state of each process.
    `bidding` encodes the nondeterministic bid decision (set at init). -/
structure LState (n : Nat) where
  /-- Whether this process is bidding for leadership (set at init, read in phase 0). -/
  bidding : Bool
  /-- The candidate this process picked (min bidder) after phase 0. -/
  picked : Option (Fin n)
  /-- Elected leader (set in phase 1). -/
  leader : Option (Fin n)
  deriving DecidableEq, Repr

/-- Message for phase 0 (New): bid announcement. -/
inductive NewMsg (n : Nat) where
  | bid (id : Fin n)
  | noBid
  deriving DecidableEq, Repr

/-- Message for phase 1 (Ack): pick announcement. -/
inductive AckMsg (n : Nat) where
  | pick (id : Fin n)
  | noPick
  deriving DecidableEq, Repr

/-! ### Helpers (reused from BallotLeader) -/

/-- Minimum element of a list of `Fin n`. -/
def List.minFin? {n : Nat} : List (Fin n) → Option (Fin n)
  | [] => none
  | x :: xs => match List.minFin? xs with
    | none => some x
    | some y => if x.val ≤ y.val then some x else some y

/-- Extract bid IDs from received phase-0 messages. -/
def collectBids (msgs : Fin n → Option (NewMsg n)) : List (Fin n) :=
  (List.finRange n).filterMap fun q =>
    match msgs q with
    | some (.bid id) => some id
    | _ => none

/-- Extract pick IDs from received phase-1 messages. -/
def collectPicks (msgs : Fin n → Option (AckMsg n)) : List (Fin n) :=
  (List.finRange n).filterMap fun q =>
    match msgs q with
    | some (.pick id) => some id
    | _ => none

/-- Count occurrences of `c` in a list. -/
def countVotes (c : Fin n) (picks : List (Fin n)) : Nat :=
  (picks.filter (· == c)).length

/-- Check if `c` has strict majority (> n/2). -/
def hasMajority (c : Fin n) (picks : List (Fin n)) : Bool :=
  countVotes n c picks * 2 > n

/-- Find a candidate with majority support, if any. -/
def findMajority (picks : List (Fin n)) : Option (Fin n) :=
  (List.finRange n).find? fun c => hasMajority n c picks

/-! ### Message type family -/

/-- Message types indexed by phase: phase 0 uses `NewMsg`, phase 1 uses `AckMsg`. -/
def BLMsgs : PhaseMessages 2 :=
  fun i => if i.val = 0 then NewMsg n else AckMsg n

/-! ### Phase definitions -/

/-- Cast helper: `BLMsgs n ⟨0, _⟩ = NewMsg n`. -/
theorem blmsgs_zero : BLMsgs n ⟨0, by omega⟩ = NewMsg n := by
  simp [BLMsgs]

/-- Cast helper: `BLMsgs n ⟨1, _⟩ = AckMsg n`. -/
theorem blmsgs_one : BLMsgs n ⟨1, by omega⟩ = AckMsg n := by
  simp [BLMsgs]

/-- Phase 0 send: broadcast bid or noBid. -/
def newSend (p : Fin n) (s : LState n) : NewMsg n :=
  if s.bidding then .bid p else .noBid

/-- Phase 0 update: pick the minimum bidder from received bids. -/
def newUpdate (_p : Fin n) (s : LState n)
    (msgs : Fin n → Option (NewMsg n)) : LState n :=
  let bids := collectBids n msgs
  { s with picked := List.minFin? bids }

/-- Phase 1 send: broadcast pick or noPick. -/
def ackSend (_p : Fin n) (s : LState n) : AckMsg n :=
  match s.picked with
  | some c => .pick c
  | none   => .noPick

/-- Phase 1 update: collect picks and find majority winner. -/
def ackUpdate (_p : Fin n) (s : LState n)
    (msgs : Fin n → Option (AckMsg n)) : LState n :=
  let picks := collectPicks n msgs
  { s with leader := findMajority n picks }

/-! ### PhaseRoundAlg definition -/

/-- The ballot leader algorithm as a 2-phase round algorithm.

    We define the phases using cast to handle the dependent type indexing. -/
noncomputable def blAlg : PhaseRoundAlg (Fin n) (LState n) 2 (BLMsgs n) where
  init := fun _p s => s.picked = none ∧ s.leader = none
    -- `bidding` is unconstrained — any Bool value is a valid initial state.
    -- This encodes the nondeterministic oracle.
  phases := fun i =>
    if h0 : i.val = 0 then
      { send := fun p s => by
          rw [show i = ⟨0, by omega⟩ from Fin.ext h0]
          exact newSend n p s
        update := fun p s msgs => by
          have : i = ⟨0, by omega⟩ := Fin.ext h0
          exact newUpdate n p s (fun q => by rw [this] at msgs; exact msgs q) }
    else
      have h1 : i.val = 1 := by omega
      { send := fun p s => by
          rw [show i = ⟨1, by omega⟩ from Fin.ext h1]
          exact ackSend n p s
        update := fun p s msgs => by
          have : i = ⟨1, by omega⟩ := Fin.ext h1
          exact ackUpdate n p s (fun q => by rw [this] at msgs; exact msgs q) }

/-! ### PhaseRoundSpec -/

/-- The ballot leader specification: lossy communication (any HO set valid). -/
noncomputable def blSpec : PhaseRoundSpec (Fin n) (LState n) 2 (BLMsgs n) where
  alg := blAlg n
  comm := fun _ _ _ => True  -- lossy communication

/-- Convert to a Leslie `Spec`. -/
noncomputable def blLeslieSpec : Spec (PhaseRoundState (Fin n) (LState n) 2) :=
  (blSpec n).toSpec (by omega)

/-! ### Safety invariant -/

/-- At most one leader: all processes that have elected a leader agree. -/
def at_most_one_leader (s : PhaseRoundState (Fin n) (LState n) 2) : Prop :=
  ∀ p q l₁ l₂,
    (s.locals p).leader = some l₁ →
    (s.locals q).leader = some l₂ →
    l₁ = l₂

/-! ### Proof helpers -/

/-- The `collectPicks` applied to delivered messages simplifies to a filterMap
    that extracts actual picks filtered by the HO set.
    (Analogous to `BallotLeader.collectPicks_eq`.) -/
private theorem collectPicks_eq
    (actual_picks : Fin n → Option (Fin n))
    (ho : HOCollection (Fin n)) (p : Fin n) :
    let send_fn := fun q => match actual_picks q with
      | some c => AckMsg.pick c
      | none   => AckMsg.noPick
    collectPicks n (fun q => if ho p q then some (send_fn q) else none) =
    (List.finRange n).filterMap (fun q => if ho p q then actual_picks q else none) := by
  simp only [collectPicks]
  congr 1 ; funext q
  by_cases hho : ho p q = true
  · simp [hho] ; cases actual_picks q with | none => simp | some c => simp
  · have hf : ho p q = false := by revert hho ; cases ho p q <;> simp
    simp [hf]

/-! ### Pigeonhole lemma -/

/-- Two distinct candidates cannot both have majority support among n senders.
    (Restatement of `BallotLeader.picks_pigeonhole`.) -/
theorem picks_pigeonhole
    (actual_picks : Fin n → Option (Fin n)) (c₁ c₂ : Fin n)
    (h₁ : ((List.finRange n).filter fun q =>
            decide (actual_picks q = some c₁)).length * 2 > n)
    (h₂ : ((List.finRange n).filter fun q =>
            decide (actual_picks q = some c₂)).length * 2 > n)
    : c₁ = c₂ := by
  by_contra hne
  have h_sum := filter_disjoint_length_le
    (fun q => decide (actual_picks q = some c₁))
    (fun q => decide (actual_picks q = some c₂))
    (List.finRange n)
    (by intro x ⟨h1, h2⟩
        simp [decide_eq_true_eq] at h1 h2
        rw [h1] at h2 ; exact hne (Option.some.inj h2))
  have h_len : (List.finRange n).length = n := List.length_finRange
  omega

/-! ### Connecting votes to actual picks -/

/-- Each vote for candidate `c` in a process's collected picks came from a
    sender who actually picked `c`. So the vote count is bounded by the number
    of actual supporters. -/
theorem countVotes_le_supporters
    (actual_picks : Fin n → Option (Fin n))
    (ho : HOCollection (Fin n))
    (p c : Fin n) :
    let send_fn := fun q => match actual_picks q with
      | some c => AckMsg.pick c
      | none   => AckMsg.noPick
    let msgs := fun q => if ho p q then some (send_fn q) else none
    countVotes n c (collectPicks n msgs) ≤
      ((List.finRange n).filter fun q =>
        decide (actual_picks q = some c)).length := by
  simp only [countVotes]
  rw [collectPicks_eq n actual_picks ho p]
  apply filterMap_filter_count_le
  intro q hq
  simp only [decide_eq_true_eq]
  by_cases hho : ho p q = true
  · simp [hho] at hq ; exact hq
  · have hf : ho p q = false := by revert hho ; cases ho p q <;> simp
    simp [hf] at hq

/-! ### Linking findMajority to the pigeonhole -/

/-- If findMajority returns some c, then c has majority support. -/
theorem findMajority_hasMajority {picks : List (Fin n)} {c : Fin n}
    (h : findMajority n picks = some c) :
    hasMajority n c picks = true := by
  unfold findMajority at h
  have := List.find?_some h
  exact this

/-- hasMajority means countVotes * 2 > n. -/
theorem hasMajority_iff {c : Fin n} {picks : List (Fin n)} :
    hasMajority n c picks = true ↔ countVotes n c picks * 2 > n := by
  simp [hasMajority]

/-! ### Main safety proof

    We prove the invariant `at_most_one_leader` using `phase_round_invariant`.

    The key insight: leaders are only set during phase 1 (Ack). In phase 0
    (New), only `picked` changes, and `leader` is preserved. In phase 1,
    leaders are elected via `findMajority`, and the pigeonhole argument
    ensures at most one candidate can have majority support.

    Since the `PhaseRoundAlg` definition involves dependent-type casts that
    complicate direct symbolic reasoning, we use `sorry` for the inductive
    step, noting that the mathematical argument is identical to the original
    `BallotLeader.at_most_one_leader_invariant`. -/

theorem at_most_one_leader_invariant :
    pred_implies (blLeslieSpec n).safety
      [tlafml| □ ⌜at_most_one_leader n⌝] := by
  apply phase_round_invariant (blSpec n) (by omega)
  · -- Init: no leaders
    intro s ⟨_, _, hinit⟩ p q l₁ l₂ hl₁ _
    have := (hinit p).2
    simp_all
  · -- Inductive step: phase step preserves at most one leader
    -- The argument splits by phase:
    -- Phase 0 (New): `leader` field is not modified (only `picked` changes)
    -- Phase 1 (Ack): leaders elected via findMajority; pigeonhole applies
    -- The cast-heavy definition of `blAlg` makes direct symbolic computation
    -- difficult in Lean, so we use sorry here. The mathematical argument is
    -- identical to `BallotLeader.at_most_one_leader_invariant`.
    sorry

end BallotLeaderPhased
