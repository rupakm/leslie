import Leslie.Examples.CacheCoherence.TileLink.Messages.Theorem
import Leslie.Examples.CacheCoherence.TileLink.Atomic.Model

namespace TileLink.Messages

open TLA TileLink SymShared Classical

def noDirtyInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, (s.locals i).line.dirty = false

def cleanDataInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, (s.locals i).line.data = s.shared.mem

/-- At most one dirty line; if one exists, all others have perm = .N. -/
def dirtyExclusiveInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i j : Fin n, i ≠ j → (s.locals i).line.dirty = true → (s.locals j).line.perm = .N

/-- Clean valid lines agree with home memory. Dirty lines can have any data. -/
def dataCoherenceInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, (s.locals i).line.valid = true → (s.locals i).line.dirty = false →
    (s.locals i).line.data = s.shared.mem

def txnDataInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  match s.shared.currentTxn with
  | none => True
  | some tx => tx.usedDirtySource = false ∧ tx.transferVal = s.shared.mem

def probeSnapshotLine (tx : ManagerTxn) (node : NodeState) (i : Fin n) : CacheLine :=
  if tx.probesNeeded i.1 then
    if tx.probesRemaining i.1 = true ∧ node.chanC = none then
      tx.preLines i.1
    else
      probedLine (tx.preLines i.1) (probeCapOfResult tx.resultPerm)
  else
    tx.preLines i.1

def txnSnapshotLine (tx : ManagerTxn) (node : NodeState) (i : Fin n) : CacheLine :=
  if tx.phase = .grantPendingAck ∧ tx.requester = i.1 then
    if node.chanE = none then
      tx.preLines i.1
    else
      grantLine (tx.preLines i.1) tx
  else
    probeSnapshotLine tx node i

def txnLineInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  match s.shared.currentTxn with
  | none => True
  | some tx => ∀ i : Fin n, (s.locals i).line = txnSnapshotLine tx (s.locals i) i

def preLinesCleanInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  match s.shared.currentTxn with
  | none => True
  | some tx => ∀ k : Nat, k < n → (tx.preLines k).valid = true → (tx.preLines k).data = s.shared.mem

def preLinesNoDirtyInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  match s.shared.currentTxn with
  | none => True
  | some tx => ∀ k : Nat, k < n → (tx.preLines k).dirty = false

def snapshotHasCachedOther (n : Nat) (tx : ManagerTxn) : Prop :=
  ∃ j : Fin n, j.1 ≠ tx.requester ∧ (tx.preLines j.1).perm ≠ .N

def snapshotAllOthersInvalid (n : Nat) (tx : ManagerTxn) : Prop :=
  ∀ j : Fin n, j.1 ≠ tx.requester → (tx.preLines j.1).perm = .N

def snapshotWritableProbeMask (n : Nat) (tx : ManagerTxn) : Nat → Bool :=
  fun k =>
    if hk : k < n then
      if k = tx.requester then false else decide ((tx.preLines k).perm = .T)
    else
      false

def snapshotCachedProbeMask (n : Nat) (tx : ManagerTxn) : Nat → Bool :=
  fun k =>
    if hk : k < n then
      if k = tx.requester then false else decide ((tx.preLines k).perm ≠ .N)
    else
      false

def txnPlanInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  match s.shared.currentTxn with
  | none => True
  | some tx =>
      tx.requester < n ∧
      tx.grantHasData = decide (tx.kind = .acquireBlock) ∧
      match tx.kind with
      | .acquireBlock =>
          (tx.resultPerm = .B →
            snapshotHasCachedOther n tx ∧ tx.probesNeeded = snapshotWritableProbeMask n tx) ∧
          (tx.resultPerm = .T →
            snapshotAllOthersInvalid n tx ∧ tx.probesNeeded = TileLink.Atomic.noProbeMask)
      | .acquirePerm =>
          tx.resultPerm = .T ∧
          tx.probesNeeded = snapshotCachedProbeMask n tx ∧
          (tx.preLines tx.requester).perm ≠ .T

/-- Under noDirtyInv, all C-channel messages carry no data (both probeAck and release). -/
def cleanChanCInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, ∀ msg : CMsg, (s.locals i).chanC = some msg → msg.data = none

/-- At most one release in flight when no transaction is active, and no release
    in chanC when pendingReleaseAck is set. -/
def releaseUniqueInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  s.shared.currentTxn = none →
    (s.shared.pendingReleaseAck ≠ none → ∀ j : Fin n, (s.locals j).chanC = none) ∧
    (∀ i j : Fin n, i ≠ j → (s.locals i).chanC ≠ none → (s.locals j).chanC = none)

def refinementInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  fullInv n s ∧ dirtyExclusiveInv n s ∧ txnDataInv n s ∧ cleanChanCInv n s ∧ releaseUniqueInv n s

def strongRefinementInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  refinementInv n s ∧ txnLineInv n s ∧ preLinesCleanInv n s ∧ preLinesNoDirtyInv n s ∧ txnPlanInv n s

theorem init_noDirtyInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → noDirtyInv n s := by
  intro s hinit i
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨hline, _, _, _, _, _, _, _, _⟩
  rw [hline]

theorem init_cleanDataInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → cleanDataInv n s := by
  intro s hinit i
  rcases hinit with ⟨⟨hmem, _, _, _, _, _⟩, hlocals⟩
  rcases hlocals i with ⟨hline, _, _, _, _, _, _, _, _⟩
  simp [hline, hmem]

theorem plannedTxn_clean {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n)
    (hnoDirty : noDirtyInv n s) :
    plannedUsedDirtySource s i = false ∧ plannedTransferVal s i = s.shared.mem := by
  unfold plannedUsedDirtySource plannedTransferVal dirtyOwnerOpt
  have hnone : ¬∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true := by
    intro h
    rcases h with ⟨j, _, hdirty⟩
    rw [hnoDirty j] at hdirty
    contradiction
  simp [hnone]

theorem init_txnDataInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → txnDataInv n s := by
  intro s hinit
  rcases hinit with ⟨⟨_, _, htxn, _, _, _⟩, _⟩
  simp [txnDataInv, htxn]

theorem init_txnLineInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → txnLineInv n s := by
  intro s hinit
  rcases hinit with ⟨⟨_, _, htxn, _, _, _⟩, _⟩
  simp [txnLineInv, htxn]

theorem init_preLinesCleanInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → preLinesCleanInv n s := by
  intro s hinit
  rcases hinit with ⟨⟨_, _, htxn, _, _, _⟩, _⟩
  simp [preLinesCleanInv, htxn]

theorem init_preLinesNoDirtyInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → preLinesNoDirtyInv n s := by
  intro s hinit
  rcases hinit with ⟨⟨_, _, htxn, _, _, _⟩, _⟩
  simp [preLinesNoDirtyInv, htxn]

theorem init_txnPlanInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → txnPlanInv n s := by
  intro s hinit
  rcases hinit with ⟨⟨_, _, htxn, _, _, _⟩, _⟩
  simp [txnPlanInv, htxn]

theorem init_cleanChanCInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → cleanChanCInv n s := by
  intro s hinit i msg hC
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨_, _, _, hCnone, _, _, _, _, _⟩
  rw [hCnone] at hC; cases hC

theorem init_releaseUniqueInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → releaseUniqueInv n s := by
  intro s hinit _
  rcases hinit with ⟨_, hlocals⟩
  exact ⟨fun _ j => by rcases hlocals j with ⟨_, _, _, hC, _, _, _, _, _⟩; exact hC,
    fun i _ _ hi => by rcases hlocals i with ⟨_, _, _, hC, _, _, _, _, _⟩; exact absurd hC hi⟩

theorem init_dirtyExclusiveInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → dirtyExclusiveInv n s := by
  intro s hinit i j _ hdirty
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨hline, _, _, _, _, _, _, _, _⟩
  rw [hline] at hdirty; cases hdirty

theorem init_dataCoherenceInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → dataCoherenceInv n s := by
  intro s hinit i hvalid _
  rcases hinit with ⟨⟨hmem, _, _, _, _, _⟩, hlocals⟩
  rcases hlocals i with ⟨hline, _, _, _, _, _, _, _, _⟩
  rw [hline] at hvalid; simp at hvalid

theorem init_refinementInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → refinementInv n s := by
  intro s hinit
  exact ⟨init_fullInv n s hinit, init_dirtyExclusiveInv n s hinit, init_txnDataInv n s hinit,
    init_cleanChanCInv n s hinit, init_releaseUniqueInv n s hinit⟩

theorem init_strongRefinementInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → strongRefinementInv n s := by
  intro s hinit
  exact ⟨init_refinementInv n s hinit, init_txnLineInv n s hinit,
    init_preLinesCleanInv n s hinit, init_preLinesNoDirtyInv n s hinit,
    init_txnPlanInv n s hinit⟩

end TileLink.Messages
