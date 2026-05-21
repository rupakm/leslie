import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.Invariants

/-! ## Preservation of preLinesWFInv and txnTransferMemInv

    These are newer invariants added to support the txnDataInv Part 3 proof
    (transferVal = mem at grantReady after dirty probeAck processing).
    Extracted from the main Preservation.lean for context manageability.

    STATUS: These theorems depend on invariants (dataCoherenceInv,
    dirtyReleaseExclusiveInv, dirtyOwnerExistsInv, releaseDataInv,
    releaseDataChanCInv, txnNoReleaseInv, usedDirtySourceInv,
    preLinesWFInv, txnTransferMemInv) that are not yet defined on the
    Leslie_LTS branch. The branch's Act enum also has 12 constructors
    (missing store, read, uncachedGet, uncachedPut, recvUncachedAtManager,
    recvAccessAckAtMaster). All proofs are sorry'd pending model alignment. -/

namespace TileLink.Messages

open TLA TileLink SymShared Classical

-- The following invariant definitions are placeholders for invariants that
-- were defined on main but are not yet present on this branch.

/-- Placeholder: pre-transaction lines are well-formed. -/
def preLinesWFInv (_n : Nat) (_s : SymState HomeState NodeState _n) : Prop :=
  match _s.shared.currentTxn with
  | none => True
  | some tx => ∀ k : Nat, k < _n → (tx.preLines k).WellFormed

/-- Placeholder: transferVal tracks memory through dirty probeAck processing. -/
def txnTransferMemInv (_n : Nat) (_s : SymState HomeState NodeState _n) : Prop :=
  match _s.shared.currentTxn with
  | none => True
  | some tx =>
      tx.usedDirtySource = true →
      (∀ k : Nat, k < _n → (tx.preLines k).dirty = true → tx.probesRemaining k = false) →
      tx.transferVal = tx.transferVal  -- trivially true placeholder

/-- Placeholder: data coherence between local lines and shared memory. -/
def dataCoherenceInv (_n : Nat) (_s : SymState HomeState NodeState _n) : Prop :=
  _s.shared.currentTxn = none →
  ∀ i : Fin _n, (_s.locals i).releaseInFlight = false →
    (_s.locals i).line.valid = true →
    (_s.locals i).line.dirty = false →
    (_s.locals i).line.data = _s.shared.mem

/-- Placeholder: release data in chanC matches line data. -/
def releaseDataInv (_n : Nat) (_s : SymState HomeState NodeState _n) : Prop :=
  _s.shared.currentTxn = none →
  ∀ j : Fin _n, (_s.locals j).releaseInFlight = true →
    (∀ msg : CMsg, (_s.locals j).chanC = some msg → msg.data = none) →
    (_s.locals j).line.perm ≠ .N →
    (_s.locals j).line.dirty = false →
    (_s.locals j).line.data = _s.shared.mem

/-- Placeholder: release data on chanC equals line data for dirty releases. -/
def releaseDataChanCInv (_n : Nat) (_s : SymState HomeState NodeState _n) : Prop :=
  ∀ i : Fin _n, (_s.locals i).releaseInFlight = true →
    ∀ msg : CMsg, (_s.locals i).chanC = some msg → msg.data ≠ none →
      msg.data = some (_s.locals i).line.data

/-- Placeholder: no release in flight during active transaction. -/
def txnNoReleaseInv (_n : Nat) (_s : SymState HomeState NodeState _n) : Prop :=
  _s.shared.currentTxn ≠ none →
  ∀ j : Fin _n, (_s.locals j).releaseInFlight = false

/-- Placeholder: dirty owner exists when usedDirtySource is true. -/
def dirtyOwnerExistsInv (_n : Nat) (_s : SymState HomeState NodeState _n) : Prop :=
  ∀ tx : ManagerTxn, _s.shared.currentTxn = some tx → tx.usedDirtySource = true →
    ∃ k : Nat, k < _n ∧ tx.probesRemaining k = false ∧
      (tx.preLines k).dirty = true ∧ tx.transferVal = (tx.preLines k).data

/-- Placeholder: usedDirtySource consistency. -/
def usedDirtySourceInv (_n : Nat) (_s : SymState HomeState NodeState _n) : Prop :=
  True  -- simplified placeholder

/-- Placeholder: dirty release excludes other cached nodes. -/
def dirtyReleaseExclusiveInv (_n : Nat) (_s : SymState HomeState NodeState _n) : Prop :=
  _s.shared.currentTxn = none →
  ∀ i : Fin _n, (_s.locals i).releaseInFlight = true →
    (∃ msg : CMsg, (_s.locals i).chanC = some msg ∧ msg.data ≠ none) →
    ∀ j : Fin _n, j ≠ i → (_s.locals j).line.perm = .N

theorem preLinesWFInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hpreWF : preLinesWFInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    preLinesWFInv n s' := by
  sorry

theorem txnTransferMemInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (htxnData : txnDataInv n s)
    (hpreNoDirty : preLinesNoDirtyInv n s) (husedDirty : usedDirtySourceInv n s)
    (hdirtyOwner : dirtyOwnerExistsInv n s) (hpreWF : preLinesWFInv n s)
    (htxnTM : txnTransferMemInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    txnTransferMemInv n s' := by
  sorry

theorem releaseDataInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hdata : dataCoherenceInv n s)
    (hrelData : releaseDataInv n s)
    (hrelDCC : releaseDataChanCInv n s)
    (htxnNoRel : txnNoReleaseInv n s)
    (hdirtyRelEx : dirtyReleaseExclusiveInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    releaseDataInv n s' := by
  sorry

theorem releaseDataChanCInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hrelDCC : releaseDataChanCInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    releaseDataChanCInv n s' := by
  sorry

theorem txnNoReleaseInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (htxnNoRel : txnNoReleaseInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    txnNoReleaseInv n s' := by
  sorry

end TileLink.Messages
