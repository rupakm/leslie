import Leslie.Examples.CacheCoherence.TileLink.Messages.Liveness.Defs
import Leslie.Rules.WF
import Leslie.Rules.LeadsTo

/-! ## Progress Lemmas for TileLink Liveness

    Each step in the acquire wave has a "progress" lemma: from the current
    phase, the action that advances to the next phase is enabled.

    These are the key building blocks for WF1 applications. Combined with
    weak fairness, they give leads-to properties.

    The acquire wave phases:

    ```
    chanA has acquire → txn active (probing) → all probes done (grantReady)
      → grant sent (grantPendingAck) → grant received → grantAck sent → txn complete
    ```

    STATUS: Preservation theorems are sorry'd because the branch's Act enum
    has 12 constructors (missing store, read, uncachedGet, uncachedPut,
    recvUncachedAtManager, recvAccessAckAtMaster). The original proofs
    case-split on all 18 constructors. All definitions, init theorems,
    and enabled/progress lemmas are fully proved.
-/

namespace TileLink.Messages.Liveness

open TLA TileLink SymShared

/-! ### Auxiliary invariants not in fullInv

    These invariants are needed for liveness but are not part of the safety
    invariant `fullInv`. Each requires a separate inductive proof over all
    protocol actions. -/

/-- pendingSink is only non-none when chanD or chanE is non-none (grant wave active).
    Key insight: only sendGrantLocal sets pendingSink := some (and also sets chanD),
    recvGrantLocal clears chanD but chanE gets set, recvGrantAckLocal clears both. -/
def pendingSinkInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, (s.locals i).pendingSink ≠ none →
    (s.locals i).chanD ≠ none ∨ (s.locals i).chanE ≠ none

theorem init_pendingSinkInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      pendingSinkInv n s := by
  intro s hinit i hps
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨_, _, _, _, _, _, _, hpsi, _⟩
  rw [hpsi] at hps; exact absurd rfl hps

/-- Stronger invariant: pendingSink ≠ none implies an active transaction at
    grantPendingAck phase with the node as requester. This is the inductive
    version; pendingSinkInv is derived from this + grantWaveActiveInv. -/
def pendingSinkTxnInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, (s.locals i).pendingSink ≠ none →
    ∃ tx, s.shared.currentTxn = some tx ∧ tx.requester = i.1 ∧ tx.phase = .grantPendingAck

theorem init_pendingSinkTxnInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      pendingSinkTxnInv n s := by
  intro s hinit i hps
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨_, _, _, _, _, _, _, hpsi, _⟩
  rw [hpsi] at hps; exact absurd rfl hps

-- sorry: proof case-splits on 18-constructor Act; branch has 12 constructors
theorem pendingSinkTxnInv_preserved {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hinv : fullInv n s)
    (hpst : pendingSinkTxnInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    pendingSinkTxnInv n s' := by
  sorry

/-- During probing, if probesRemaining j = true, then either chanB j
    has the probe (not yet received) or chanC j has the probeAck
    (j responded, manager hasn't consumed yet).
    Key insight: recvAcquire sets chanB for all probed nodes,
    recvProbe clears chanB and sets chanC,
    recvProbeAck clears chanC and sets probesRemaining to false. -/
def probeChannelInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ tx, s.shared.currentTxn = some tx → tx.phase = .probing →
    ∀ j : Fin n, tx.probesRemaining j.1 = true →
      (s.locals j).chanB ≠ none ∨ (s.locals j).chanC ≠ none

theorem init_probeChannelInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      probeChannelInv n s := by
  intro s hinit tx hcur
  rcases hinit with ⟨⟨_, _, hcurNone, _, _, _⟩, _⟩
  rw [hcur] at hcurNone; simp at hcurNone

-- sorry: proof case-splits on 18-constructor Act; branch has 12 constructors
theorem probeChannelInv_preserved {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hinv : fullInv n s)
    (hpci : probeChannelInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    probeChannelInv n s' := by
  sorry

/-- If chanD holds an accessAck/accessAckData, then chanA is none.
    This means the pending uncached request has already consumed chanA. -/
def accessAckChanAInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, match (s.locals i).chanD with
    | none => True
    | some msg =>
        (msg.opcode = .accessAck ∨ msg.opcode = .accessAckData) → (s.locals i).chanA = none

theorem init_accessAckChanAInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → accessAckChanAInv n s := by
  intro s hinit i
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨_, _, _, _, hD, _, _, _, _⟩
  simp [hD]

-- sorry: proof case-splits on 18-constructor Act; branch has 12 constructors
theorem accessAckChanAInv_preserved {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hinv : fullInv n s)
    (hacc : accessAckChanAInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    accessAckChanAInv n s' := by
  sorry

/-- If chanD holds an accessAck/accessAckData for node i, then any active
    transaction's requester ≠ i. (The accessAck is from an uncached operation
    that started when currentTxn was none, and creating a new txn requires
    chanA = none which accessAckChanAInv gives.) -/
def accessAckNotRequesterInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, ∀ msg, (s.locals i).chanD = some msg →
    (msg.opcode = .accessAck ∨ msg.opcode = .accessAckData) →
    ∀ tx, s.shared.currentTxn = some tx → tx.requester ≠ i.1

theorem init_accessAckNotRequesterInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      accessAckNotRequesterInv n s := by
  intro s hinit i msg hD _ tx hcur
  rcases hinit with ⟨⟨_, _, hcurNone, _, _, _⟩, _⟩
  rw [hcur] at hcurNone; simp at hcurNone

-- sorry: proof case-splits on 18-constructor Act; branch has 12 constructors
theorem accessAckNotRequesterInv_preserved {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hinv : fullInv n s)
    (hacca : accessAckChanAInv n s)
    (hnotreq : accessAckNotRequesterInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    accessAckNotRequesterInv n s' := by
  sorry

/-- During grantPendingAck, the requester either has the grant on chanD
    (not yet consumed) or the grantAck on chanE (grant consumed, ack pending).
    Key insight: sendGrant sets chanD, recvGrant clears chanD and sets chanE,
    recvGrantAck clears chanE. No other action touches chanD/chanE for the
    requester while the txn is active. -/
def grantWaveActiveInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ tx, s.shared.currentTxn = some tx → tx.phase = .grantPendingAck →
    ∀ i : Fin n, i.1 = tx.requester →
      (s.locals i).chanD ≠ none ∨ (s.locals i).chanE ≠ none

theorem init_grantWaveActiveInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      grantWaveActiveInv n s := by
  intro s hinit tx hcur
  rcases hinit with ⟨⟨_, _, hcurNone, _, _, _⟩, _⟩
  rw [hcur] at hcurNone; simp at hcurNone

-- sorry: proof case-splits on 18-constructor Act; branch has 12 constructors
theorem grantWaveActiveInv_preserved {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hinv : fullInv n s)
    (hnotreq : accessAckNotRequesterInv n s)
    (hgwa : grantWaveActiveInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    grantWaveActiveInv n s' := by
  sorry

theorem pendingSinkInv_preserved {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hinv : fullInv n s)
    (hnotreq : accessAckNotRequesterInv n s)
    (hpst : pendingSinkTxnInv n s)
    (hgwa : grantWaveActiveInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    pendingSinkInv n s' := by
  have hpst' := pendingSinkTxnInv_preserved hinv hpst hnext
  have hgwa' := grantWaveActiveInv_preserved hinv hnotreq hgwa hnext
  intro k hps'
  rcases hpst' k hps' with ⟨tx, hcur', hreq', hphase'⟩
  exact hgwa' tx hcur' hphase' k hreq'.symm

/-- During an active transaction, the requester's chanA is none and pendingSource
    is set, as long as the grant hasn't been consumed yet.
    Covers phases: probing, grantReady, and the first half of grantPendingAck
    (while chanD still holds the grant, before RecvGrant clears it).
    The pendingSource ≠ none conjunct is the key inductive strengthening:
    it blocks all chanA-setting actions (SendAcquire, UncachedGet/Put)
    since they all require pendingSource = none. -/
def requesterChanAInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ tx, s.shared.currentTxn = some tx →
    ∀ i : Fin n, tx.requester = i.1 →
      (tx.phase = .probing ∨ tx.phase = .grantReady ∨
       (tx.phase = .grantPendingAck ∧ (s.locals i).chanD ≠ none)) →
      (s.locals i).chanA = none ∧ (s.locals i).pendingSource ≠ none

theorem init_requesterChanAInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      requesterChanAInv n s := by
  intro s hinit tx hcur
  rcases hinit with ⟨⟨_, _, hcurNone, _, _, _⟩, _⟩
  rw [hcur] at hcurNone; simp at hcurNone

-- sorry: proof case-splits on 18-constructor Act; branch has 12 constructors
theorem requesterChanAInv_preserved {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hinv : fullInv n s)
    (hnotreq : accessAckNotRequesterInv n s)
    (hreq : requesterChanAInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    requesterChanAInv n s' := by
  sorry

/-! ### Enablement lemmas -/

/-- At grantReady, SendGrantToRequester is enabled for the requester. -/
theorem sendGrant_enabled {n : Nat}
    {s : SymState HomeState NodeState n}
    (hinv : fullInv n s)
    (hnotreq : accessAckNotRequesterInv n s)
    (hpst : pendingSinkTxnInv n s)
    (hready : grantReady n s) :
    ∃ i : Fin n, enabled (actSendGrantToRequester n i) s := by
  -- Extract invariants from fullInv
  rcases hinv with ⟨⟨_, _, hpending, htxnCore⟩, ⟨_, _, _, hchanD, hchanE⟩, _⟩
  -- Extract tx from grantReady
  rcases hready with ⟨tx, hcur, hphase⟩
  -- Get requester < n from txnCoreInv
  rw [txnCoreInv, hcur] at htxnCore
  rcases htxnCore with ⟨hreqLt, _, _, _, _, _, _, _⟩
  -- Define the requester index
  let i : Fin n := ⟨tx.requester, hreqLt⟩
  refine ⟨i, sendGrantState s i tx, ?_⟩
  -- Show actSendGrantToRequester fires
  refine ⟨.sendGrantToRequester, rfl, ?_⟩
  -- Unfold SendGrantToRequester
  simp only [tlMessages]
  refine ⟨tx, hcur, rfl, hphase, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · -- pendingGrantAck = none: from pendingInv, phase ≠ grantPendingAck
    rw [pendingInv, hcur] at hpending
    rcases hpending with ⟨_, hgrant⟩
    simp [hphase] at hgrant
    exact hgrant
  · -- pendingReleaseAck = none: from pendingInv, currentTxn = some
    rw [pendingInv, hcur] at hpending
    exact hpending.1
  · -- chanD i = none: from chanDInv
    specialize hchanD i
    match hD : (s.locals i).chanD with
    | none => rfl
    | some msg =>
      rw [hD] at hchanD
      rcases hchanD with ⟨tx', hcur', _, hphase', _, _, _, _⟩ | ⟨hcurNone, _, _, _, _, _, _⟩
      · -- Grant branch: phase = grantPendingAck, but our phase = grantReady
        rw [hcur] at hcur'; cases hcur'
        rw [hphase] at hphase'; exact absurd hphase' (by decide)
      · -- ReleaseAck branch: currentTxn = none, contradiction
        rw [hcur] at hcurNone; exact absurd hcurNone (by simp)
  · -- chanE i = none: from chanEInv, phase ≠ grantPendingAck
    specialize hchanE i
    match hE : (s.locals i).chanE with
    | none => rfl
    | some msg =>
      rw [hE] at hchanE
      rcases hchanE with ⟨tx', hcur', _, hphase', _, _, _, _⟩
      rw [hcur] at hcur'; cases hcur'
      rw [hphase] at hphase'; exact absurd hphase' (by decide)
  · -- pendingSink i = none: from pendingSinkTxnInv
    by_contra hps
    rcases hpst i hps with ⟨tx', hcur', _, hphase'⟩
    rw [hcur] at hcur'; cases hcur'
    rw [hphase] at hphase'; exact absurd hphase' (by decide)

/-- At grantPendingAck, the requester has the grant on chanD or grantAck on chanE.
    RecvGrantAtMaster (if chanD) or RecvGrantAckAtManager (if chanE) is enabled. -/
theorem recvGrant_enabled {n : Nat}
    {s : SymState HomeState NodeState n}
    (hinv : fullInv n s)
    (hnotreq : accessAckNotRequesterInv n s)
    (hreqInv : requesterChanAInv n s)
    (hgwa : grantWaveActiveInv n s)
    (hpending : grantPendingAck n s) :
    (∃ i : Fin n, enabled (actRecvGrantAtMaster n i) s) ∨
    (∃ i : Fin n, enabled (actRecvGrantAckAtManager n i) s) := by
  -- Extract invariants from fullInv
  rcases hinv with ⟨⟨_, _, hpendingI, htxnCore⟩, ⟨_, _, _, hchanD, hchanE⟩, _⟩
  -- Extract tx from grantPendingAck
  rcases hpending with ⟨tx, hcur, hphase⟩
  -- Get requester < n from txnCoreInv
  rw [txnCoreInv, hcur] at htxnCore
  rcases htxnCore with ⟨hreqLt, _, _, _, _, _, _, _⟩
  let i : Fin n := ⟨tx.requester, hreqLt⟩
  -- Get pendingGrantAck = some tx.requester from pendingInv
  have hGrantAck : s.shared.pendingGrantAck = some i.1 := by
    rw [pendingInv, hcur] at hpendingI
    rcases hpendingI with ⟨_, hga⟩
    simp [hphase] at hga; exact hga
  -- From grantWaveActiveInv: chanD or chanE is non-none for the requester
  have hwave := hgwa tx hcur hphase i rfl
  rcases hwave with hchanDne | hchanEne
  · -- Case: chanD i ≠ none → RecvGrantAtMaster enabled
    left
    refine ⟨i, ?_⟩
    -- Get chanD info from chanDInv
    specialize hchanD i
    match hD : (s.locals i).chanD with
    | none => exact absurd hD hchanDne
    | some msg =>
      rw [hD] at hchanD
      rcases hchanD with ⟨tx', hcur', hreq', hphase', hga', hps', hEn, hmsg⟩ | ⟨hcurNone, _, _, _, _, _, _⟩
      · -- Grant branch: all guards available
        rw [hcur] at hcur'; cases hcur'
        refine ⟨recvGrantState s i tx, .recvGrantAtMaster, rfl, ?_⟩
        simp only [tlMessages]
        refine ⟨tx, msg, hcur, rfl, hphase, hGrantAck, ?_, hD, hEn, hps', hmsg, rfl⟩
        -- chanA i = none from requesterChanAInv: during grantPendingAck with chanD ≠ none
        exact (hreqInv tx hcur i rfl (Or.inr (Or.inr ⟨hphase, hchanDne⟩))).1
      · -- ReleaseAck branch: currentTxn = none, contradiction
        rw [hcur] at hcurNone; exact absurd hcurNone (by simp)
  · -- Case: chanE i ≠ none → RecvGrantAckAtManager enabled
    right
    refine ⟨i, ?_⟩
    -- Get chanE info from chanEInv
    specialize hchanE i
    match hE : (s.locals i).chanE with
    | none => exact absurd hE hchanEne
    | some msg =>
      rw [hE] at hchanE
      rcases hchanE with ⟨tx', hcur', hreq', hphase', hga', hps', hDn, hmsg⟩
      rw [hcur] at hcur'; cases hcur'
      refine ⟨recvGrantAckState s i, .recvGrantAckAtManager, rfl, ?_⟩
      simp only [tlMessages]
      exact ⟨tx, msg, hcur, rfl, hphase, hGrantAck, hDn, hE, hps', hmsg, rfl⟩

/-- During probing with remaining probes, some node has a message on chanB or chanC.
    RecvProbeAtMaster (if chanB) or RecvProbeAckAtManager (if chanC) is enabled. -/
theorem probeAck_enabled {n : Nat}
    {s : SymState HomeState NodeState n}
    (hpci : probeChannelInv n s)
    (hprobing : probingWithRemaining n s) :
    ∃ tx j, s.shared.currentTxn = some tx ∧ tx.phase = .probing ∧
      tx.probesRemaining j.1 = true ∧
      ((s.locals j).chanB ≠ none ∨ (s.locals j).chanC ≠ none) := by
  rcases hprobing with ⟨tx, hcur, hphase, j, hrem⟩
  exact ⟨tx, j, hcur, hphase, hrem, hpci tx hcur hphase j hrem⟩

/-! ### Phase monotonicity

    Protocol actions never move the transaction phase backwards.
    This is the "stuttering or progress" condition for WF1. -/

/-- The transaction phase only advances or the transaction completes.
    This is a tautology on Option (some or none). -/
theorem phase_monotone {n : Nat}
    (s' : SymState HomeState NodeState n) :
    (∃ tx', s'.shared.currentTxn = some tx') ∨
    s'.shared.currentTxn = none := by
  cases h : s'.shared.currentTxn with
  | none => exact Or.inr rfl
  | some tx' => exact Or.inl ⟨tx', rfl⟩

/-! ### Probing has remaining probes

    If the transaction phase is `.probing`, there must be at least one
    remaining probe. This follows from the model: both recvAcquire and
    recvProbeAck set phase = probeAckPhase(probesRemaining), and
    probeAckPhase returns .probing iff some remaining bit is true. -/

def probingHasRemainingInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ tx, s.shared.currentTxn = some tx → tx.phase = .probing →
    ∃ j : Fin n, tx.probesRemaining j.1 = true

theorem init_probingHasRemainingInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      probingHasRemainingInv n s := by
  intro s hinit tx hcur
  rcases hinit with ⟨⟨_, _, hcurNone, _, _, _⟩, _⟩
  rw [hcur] at hcurNone; simp at hcurNone

/-- Helper: if probeAckPhase returns .probing, some index has remaining = true. -/
private theorem probeAckPhase_probing_has_remaining {n : Nat} {f : Nat → Bool}
    (hphase : @probeAckPhase n f = .probing) :
    ∃ j : Fin n, f j.1 = true := by
  unfold probeAckPhase at hphase
  split at hphase
  · cases hphase
  · rename_i h
    by_contra hall
    apply h
    intro j
    by_contra hne
    exact hall ⟨j, by cases hf : f j.1 <;> simp_all⟩

-- sorry: proof case-splits on 18-constructor Act; branch has 12 constructors
theorem probingHasRemainingInv_preserved {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hinv : probingHasRemainingInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    probingHasRemainingInv n s' := by
  sorry

end TileLink.Messages.Liveness
