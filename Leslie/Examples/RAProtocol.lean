import Leslie.Action

/-! ## RA Protocol (Longmire Leader Election)

    ### Overview

    We model the Longmire RA (Resource Arbitration) Protocol, a leader
    election protocol used in storage systems. The system consists of:

    1. **Journal**: A shared persistent log with a generation number and
       sequence number. The generation number identifies the current leader
       epoch; the sequence number tracks progress within an epoch.

    2. **Workers** (`Fin n`): Each worker can be a follower, leader, or
       terminated. Workers read the journal state to synchronize, bid for
       leadership by sending context messages, send data messages while
       leading, and can timeout or resign.

    3. **Messages**: Context messages (leadership bids/renewals) and data
       messages flow between workers and the journal. Messages can be lost
       non-deterministically.

    ### Key invariant

    At most one worker can be "current leader" — a worker whose state is
    `leader` AND whose generation matches the journal's generation. This
    is maintained because processing a context message advances the journal
    generation, invalidating all other workers' generation numbers.

    ### Properties proved

    **SingleLeader**: At most one worker is the current leader at any time.
-/

open TLA

namespace RAProtocol

variable (n : Nat)

/-! ### Types -/

/-- Worker status in the protocol. -/
inductive WorkerStatus where
  | follower
  | leader
  | terminated
  deriving DecidableEq, Repr

/-- Messages exchanged between workers and the journal. -/
inductive Message (n : Nat) where
  /-- Context message: a leadership bid or renewal.
      `from_` is the sender, `currentGen` is the sender's view of the
      current generation, `newGen` is the proposed new generation,
      `seq` is the sequence number. -/
  | context (from_ : Fin n) (currentGen newGen seq : Nat)
  /-- Data message: a data write from a leader.
      `from_` is the sender, `gen` is the generation, `seq` is the
      sequence number. -/
  | data (from_ : Fin n) (gen seq : Nat)
  deriving DecidableEq, Repr

/-- Global system state. -/
structure RAState (n : Nat) where
  /-- Current journal generation (leader epoch). -/
  journalGeneration : Nat
  /-- Current journal sequence number (progress within epoch). -/
  journalSeqNum : Nat
  /-- Per-worker status: follower, leader, or terminated. -/
  workerState : Fin n → WorkerStatus
  /-- Per-worker generation number (last synced generation). -/
  workerGeneration : Fin n → Nat
  /-- Per-worker sequence number (last synced sequence). -/
  workerSeqNum : Fin n → Nat
  /-- In-flight messages. -/
  messages : List (Message n)

/-! ### Action Index -/

/-- The nine actions of the RA protocol. -/
inductive RAAction (n : Nat) where
  /-- Worker reads the journal state to synchronize. -/
  | readJournalState (w : Fin n)
  /-- Follower bids for leadership by sending a context message. -/
  | bidForLeadership (w : Fin n)
  /-- Leader sends a data message. -/
  | sendData (w : Fin n)
  /-- Journal processes a context message (leadership change). -/
  | processContext (m : Message n)
  /-- Journal processes a data message. -/
  | processData (m : Message n)
  /-- Leader renews its leadership by sending a context message. -/
  | renewLeadership (w : Fin n)
  /-- Leader times out and becomes terminated. -/
  | leaderTimeout (w : Fin n)
  /-- Leader resigns and becomes a follower. -/
  | leaderResign (w : Fin n)
  /-- A message is lost non-deterministically. -/
  | messageLoss (m : Message n)

/-! ### Specification -/

def raProtocol : ActionSpec (RAState n) (RAAction n) where
  init := fun s =>
    s.journalGeneration = 1 ∧
    s.journalSeqNum = 1 ∧
    (∀ w, s.workerState w = .follower) ∧
    (∀ w, s.workerGeneration w = 1) ∧
    (∀ w, s.workerSeqNum w = 1) ∧
    s.messages = []
  actions := fun
    | .readJournalState w => {
        -- A worker reads the journal state. If the worker is a leader
        -- whose generation doesn't match the journal's (stale leader),
        -- it terminates. Otherwise, it syncs its generation and sequence
        -- numbers with the journal.
        gate := fun _ => True
        transition := fun s s' =>
          if s.workerState w = .leader ∧ s.workerGeneration w ≠ s.journalGeneration then
            -- Stale leader: terminate without syncing
            s' = { s with
              workerState := fun q => if q = w then .terminated else s.workerState q }
          else
            -- Not a stale leader: sync gen and seq from journal
            s' = { s with
              workerGeneration := fun q =>
                if q = w then s.journalGeneration else s.workerGeneration q
              workerSeqNum := fun q =>
                if q = w then s.journalSeqNum else s.workerSeqNum q }
      }
    | .bidForLeadership w => {
        -- A follower whose generation and sequence match the journal
        -- bids for leadership by sending a context message with
        -- newGen = workerGeneration + 1.
        gate := fun s =>
          s.workerState w = .follower ∧
          s.workerGeneration w = s.journalGeneration ∧
          s.workerSeqNum w = s.journalSeqNum
        transition := fun s s' =>
          s' = { s with
            messages := s.messages ++
              [.context w (s.workerGeneration w) (s.workerGeneration w + 1) (s.workerSeqNum w + 1)] }
      }
    | .sendData w => {
        -- A leader whose generation and sequence match the journal
        -- sends a data message.
        gate := fun s =>
          s.workerState w = .leader ∧
          s.workerGeneration w = s.journalGeneration ∧
          s.workerSeqNum w = s.journalSeqNum
        transition := fun s s' =>
          s' = { s with
            messages := s.messages ++
              [.data w (s.workerGeneration w) (s.workerSeqNum w + 1)] }
      }
    | .processContext m => {
        -- The journal processes a context message. The message must be
        -- in the message pool, must be a context message, the currentGen
        -- must match the journal's generation, and seq must be exactly
        -- journalSeqNum + 1. Processing advances the journal to the new
        -- generation and sets the sender as leader.
        gate := fun s =>
          m ∈ s.messages ∧
          ∃ from_ currentGen newGen seq,
            m = .context from_ currentGen newGen seq ∧
            currentGen = s.journalGeneration ∧
            seq = s.journalSeqNum + 1
        transition := fun s s' =>
          match m with
          | .context from_ _ newGen seq =>
            s' = { s with
              journalGeneration := newGen
              journalSeqNum := seq
              workerState := fun q =>
                if q = from_ then .leader else s.workerState q
              workerGeneration := fun q =>
                if q = from_ then newGen else s.workerGeneration q
              workerSeqNum := fun q =>
                if q = from_ then seq else s.workerSeqNum q
              messages := s.messages.filter (· ≠ m) }
          | .data _ _ _ => False
      }
    | .processData m => {
        -- The journal processes a data message. The message must be
        -- in the pool, must be a data message, the gen must match
        -- the journal's generation, and seq must be exactly
        -- journalSeqNum + 1.
        gate := fun s =>
          m ∈ s.messages ∧
          ∃ from_ gen seq,
            m = .data from_ gen seq ∧
            gen = s.journalGeneration ∧
            seq = s.journalSeqNum + 1
        transition := fun s s' =>
          match m with
          | .data from_ _ seq =>
            s' = { s with
              journalSeqNum := seq
              workerSeqNum := fun q =>
                if q = from_ then seq else s.workerSeqNum q
              messages := s.messages.filter (· ≠ m) }
          | .context _ _ _ _ => False
      }
    | .renewLeadership w => {
        -- A leader whose generation and sequence match the journal
        -- renews by sending a context message (same format as bid).
        gate := fun s =>
          s.workerState w = .leader ∧
          s.workerGeneration w = s.journalGeneration ∧
          s.workerSeqNum w = s.journalSeqNum
        transition := fun s s' =>
          s' = { s with
            messages := s.messages ++
              [.context w (s.workerGeneration w) (s.workerGeneration w + 1) (s.workerSeqNum w + 1)] }
      }
    | .leaderTimeout w => {
        -- A leader times out and becomes terminated.
        gate := fun s =>
          s.workerState w = .leader
        transition := fun s s' =>
          s' = { s with
            workerState := fun q => if q = w then .terminated else s.workerState q }
      }
    | .leaderResign w => {
        -- A leader resigns and becomes a follower.
        gate := fun s =>
          s.workerState w = .leader
        transition := fun s s' =>
          s' = { s with
            workerState := fun q => if q = w then .follower else s.workerState q }
      }
    | .messageLoss m => {
        -- A message is lost non-deterministically.
        gate := fun s =>
          m ∈ s.messages
        transition := fun s s' =>
          s' = { s with
            messages := s.messages.filter (· ≠ m) }
      }
  fair := []

/-! ### Safety Properties -/

/-- A worker is the "current leader" if it is in leader state AND its
    generation matches the journal's current generation. -/
def isCurrentLeader (s : RAState n) (w : Fin n) : Prop :=
  s.workerState w = .leader ∧ s.workerGeneration w = s.journalGeneration

/-- At most one worker is the current leader. -/
def single_leader (s : RAState n) : Prop :=
  ∀ w₁ w₂ : Fin n, isCurrentLeader n s w₁ → isCurrentLeader n s w₂ → w₁ = w₂

/-! ### Inductive Invariant -/

/-- The inductive invariant combines three conjuncts:

    1. **Generation bound**: Every worker's generation is ≤ the journal
       generation. Needed for (2) in the processContext case.

    2. **Single leader**: At most one worker is current leader. This is
       the target safety property.

    3. **Message validity**: Every context message in flight has
       `newGen > currentGen`. Needed for (1) in the processContext case. -/
def ra_inv (s : RAState n) : Prop :=
  (∀ w : Fin n, s.workerGeneration w ≤ s.journalGeneration) ∧
  single_leader n s ∧
  (∀ m ∈ s.messages, match m with
    | .context _ cg ng _ => ng > cg
    | .data _ _ _ => True)

/-! ### Helper Lemmas -/

private theorem filter_preserves_membership {α : Type} [DecidableEq α]
    {l : List α} {x y : α} (hx : x ∈ l) (hne : x ≠ y) :
    x ∈ l.filter (· ≠ y) := by
  simp [List.mem_filter]
  exact ⟨hx, hne⟩

private theorem filter_subset_prop {α : Type} [DecidableEq α]
    {l : List α} {P : α → Prop} {y : α}
    (h : ∀ x ∈ l, P x) :
    ∀ x ∈ l.filter (· ≠ y), P x := by
  intro x hx
  simp [List.mem_filter] at hx
  exact h x hx.1

private theorem append_preserves_prop {α : Type}
    {l : List α} {y : α} {P : α → Prop}
    (hl : ∀ x ∈ l, P x) (hy : P y) :
    ∀ x ∈ l ++ [y], P x := by
  intro x hx
  simp [List.mem_append] at hx
  rcases hx with hx | hx
  · exact hl x hx
  · subst hx ; exact hy

/-! ### Invariant Proof: Initialization -/

theorem ra_inv_init :
    ∀ s, (raProtocol n).init s → ra_inv n s := by
  intro s ⟨hgen, hseq, hws, hwg, hwseq, hmsgs⟩
  refine ⟨?_, ?_, ?_⟩
  · -- (1) Generation bound: workerGeneration w = 1 = journalGeneration
    intro w ; simp [hwg w, hgen]
  · -- (2) Single leader: all workers are followers, so vacuously true
    intro w₁ w₂ h₁ _
    exact absurd (hws w₁) (by rw [h₁.1] ; decide)
  · -- (3) Message validity: no messages
    intro m hm ; rw [hmsgs] at hm ; simp at hm

/-! ### Invariant Proof: Action Preservation -/

theorem ra_inv_step :
    ∀ (a : RAAction n) (s s' : RAState n),
    ra_inv n s →
    ((raProtocol n).actions a).gate s →
    ((raProtocol n).actions a).transition s s' →
    ra_inv n s' := by
  intro a s s' ⟨h_gen_bound, h_single, h_msg_valid⟩ hgate htrans
  cases a with
  | readJournalState w =>
    -- ReadJournalState: Two sub-cases based on stale leader detection
    simp only [raProtocol] at htrans
    by_cases hstale : s.workerState w = .leader ∧ s.workerGeneration w ≠ s.journalGeneration
    · -- Stale leader: terminate
      rw [if_pos hstale] at htrans ; subst htrans
      refine ⟨?_, ?_, ?_⟩
      · -- Gen bound: unchanged (workerGeneration unchanged)
        simpa using h_gen_bound
      · -- Single leader: stale leader removed from current leaders
        intro w₁ w₂ h₁ h₂
        simp only [isCurrentLeader] at h₁ h₂
        -- If w₁ = w, then workerState w₁ = terminated, contradiction
        have hw₁ : w₁ ≠ w := by
          intro heq ; subst heq ; simp at h₁
        have hw₂ : w₂ ≠ w := by
          intro heq ; subst heq ; simp at h₂
        simp [hw₁] at h₁ ; simp [hw₂] at h₂
        exact h_single w₁ w₂ h₁ h₂
      · -- Msg validity: messages unchanged
        simpa using h_msg_valid
    · -- Not stale: sync gen and seq
      rw [if_neg hstale] at htrans ; subst htrans
      refine ⟨?_, ?_, ?_⟩
      · -- Gen bound: w gets journalGeneration, others unchanged
        intro q ; simp only
        by_cases hq : q = w
        · subst hq ; simp
        · simp [hq] ; exact h_gen_bound q
      · -- Single leader: need to show at most one current leader
        intro w₁ w₂ h₁ h₂
        simp only [isCurrentLeader] at h₁ h₂
        -- Worker states unchanged, gen/seq changed only for w
        -- Extract workerState equalities (unchanged by this action)
        have hw₁_state : s.workerState w₁ = .leader := h₁.1
        have hw₂_state : s.workerState w₂ = .leader := h₂.1
        -- Extract generation equalities
        have hw₁_gen' : s.workerGeneration w₁ = s.journalGeneration := by
          have := h₁.2
          by_cases hq : w₁ = w <;> simp_all
        have hw₂_gen' : s.workerGeneration w₂ = s.journalGeneration := by
          have := h₂.2
          by_cases hq : w₂ = w <;> simp_all
        exact h_single w₁ w₂ ⟨hw₁_state, hw₁_gen'⟩ ⟨hw₂_state, hw₂_gen'⟩
      · -- Msg validity: messages unchanged
        simpa using h_msg_valid
  | bidForLeadership w =>
    -- BidForLeadership: adds a context message, no state changes
    simp only [raProtocol] at hgate htrans
    obtain ⟨_, hwg, _⟩ := hgate
    subst htrans
    refine ⟨?_, ?_, ?_⟩
    · -- Gen bound: unchanged
      simpa using h_gen_bound
    · -- Single leader: workerState unchanged
      simpa [isCurrentLeader] using h_single
    · -- Msg validity: new message has newGen = wg+1 > wg = currentGen
      intro x hx
      simp [List.mem_append] at hx
      rcases hx with hx | hx
      · exact h_msg_valid x hx
      · subst hx ; simp
  | sendData w =>
    -- SendData: adds a data message, no state changes
    simp only [raProtocol] at hgate htrans
    subst htrans
    refine ⟨?_, ?_, ?_⟩
    · simpa using h_gen_bound
    · simpa [isCurrentLeader] using h_single
    · intro x hx
      simp [List.mem_append] at hx
      rcases hx with hx | hx
      · exact h_msg_valid x hx
      · subst hx ; simp
  | processContext m =>
    -- ProcessContext: the critical case for single leader
    simp only [raProtocol] at hgate htrans
    obtain ⟨hm_in, from_, currentGen, newGen, seq, hm_eq, hcg_eq, _⟩ := hgate
    subst hm_eq
    -- htrans now uses match on .context
    simp only at htrans
    subst htrans
    -- Get the message validity for this specific message
    have h_ng_gt : newGen > currentGen := by
      have := h_msg_valid _ hm_in
      simp at this ; exact this
    subst hcg_eq
    refine ⟨?_, ?_, ?_⟩
    · -- Gen bound: from_ gets newGen; others have gen ≤ old journalGen < newGen
      intro q ; simp only
      by_cases hq : q = from_
      · subst hq ; simp
      · simp [hq]
        have := h_gen_bound q
        omega
    · -- Single leader: only from_ has gen = newGen (= new journalGeneration)
      intro w₁ w₂ h₁ h₂
      simp only [isCurrentLeader] at h₁ h₂
      have hw₁_from : w₁ = from_ := by
        by_contra hne
        simp [hne] at h₁
        have := h_gen_bound w₁
        omega
      have hw₂_from : w₂ = from_ := by
        by_contra hne
        simp [hne] at h₂
        have := h_gen_bound w₂
        omega
      rw [hw₁_from, hw₂_from]
    · -- Msg validity: message removed; others preserved
      apply filter_subset_prop
      simpa using h_msg_valid
  | processData m =>
    -- ProcessData: updates journalSeqNum and workerSeqNum, no gen changes
    simp only [raProtocol] at hgate htrans
    obtain ⟨_, from_, gen, seq, hm_eq, _, _⟩ := hgate
    subst hm_eq
    simp only at htrans
    subst htrans
    refine ⟨?_, ?_, ?_⟩
    · -- Gen bound: journalGeneration unchanged, workerGeneration unchanged
      simpa using h_gen_bound
    · -- Single leader: workerState unchanged, journalGeneration unchanged, workerGeneration unchanged
      simpa [isCurrentLeader] using h_single
    · -- Msg validity: message removed
      apply filter_subset_prop
      simpa using h_msg_valid
  | renewLeadership w =>
    -- RenewLeadership: adds context message (same format as bid)
    simp only [raProtocol] at hgate htrans
    obtain ⟨_, hwg, _⟩ := hgate
    subst htrans
    refine ⟨?_, ?_, ?_⟩
    · simpa using h_gen_bound
    · simpa [isCurrentLeader] using h_single
    · intro x hx
      simp [List.mem_append] at hx
      rcases hx with hx | hx
      · exact h_msg_valid x hx
      · subst hx ; simp
  | leaderTimeout w =>
    -- LeaderTimeout: leader → terminated, removes a current leader
    simp only [raProtocol] at hgate htrans
    subst htrans
    refine ⟨?_, ?_, ?_⟩
    · simpa using h_gen_bound
    · -- Single leader: w removed from leaders
      intro w₁ w₂ h₁ h₂
      simp only [isCurrentLeader] at h₁ h₂
      have hw₁ : w₁ ≠ w := by
        intro heq ; subst heq ; simp at h₁
      have hw₂ : w₂ ≠ w := by
        intro heq ; subst heq ; simp at h₂
      simp [hw₁] at h₁ ; simp [hw₂] at h₂
      exact h_single w₁ w₂ h₁ h₂
    · simpa using h_msg_valid
  | leaderResign w =>
    -- LeaderResign: leader → follower, removes a current leader
    simp only [raProtocol] at hgate htrans
    subst htrans
    refine ⟨?_, ?_, ?_⟩
    · simpa using h_gen_bound
    · intro w₁ w₂ h₁ h₂
      simp only [isCurrentLeader] at h₁ h₂
      have hw₁ : w₁ ≠ w := by
        intro heq ; subst heq ; simp at h₁
      have hw₂ : w₂ ≠ w := by
        intro heq ; subst heq ; simp at h₂
      simp [hw₁] at h₁ ; simp [hw₂] at h₂
      exact h_single w₁ w₂ h₁ h₂
    · simpa using h_msg_valid
  | messageLoss m =>
    -- MessageLoss: removes a message
    simp only [raProtocol] at hgate htrans
    subst htrans
    refine ⟨?_, ?_, ?_⟩
    · simpa using h_gen_bound
    · simpa [isCurrentLeader] using h_single
    · apply filter_subset_prop
      simpa using h_msg_valid

/-! ### Safety Theorems -/

/-- The inductive invariant holds in all reachable states. -/
theorem ra_inv_always :
    pred_implies (raProtocol n).safety
      [tlafml| □ ⌜ra_inv n⌝] := by
  apply init_invariant
  · exact ra_inv_init n
  · intro s s' ⟨a, hfire⟩ hinv
    exact ra_inv_step n a s s' hinv hfire.1 hfire.2

/-- **SingleLeader safety**: at most one worker is the current leader
    in every reachable state. -/
theorem single_leader_always :
    pred_implies (raProtocol n).safety
      [tlafml| □ ⌜single_leader n⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜ra_inv n⌝])
  · exact ra_inv_always n
  · apply always_monotone
    intro e h ; exact h.2.1

end RAProtocol
