import Leslie.Refinement
import Leslie.Examples.CacheCoherence.TileLink.Messages.Theorem
import Leslie.Examples.CacheCoherence.TileLink.Atomic.Model

namespace TileLink.Messages

open TLA TileLink SymShared Classical

def noDirtyInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, (s.locals i).line.dirty = false

def cleanDataInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, (s.locals i).line.valid = true → (s.locals i).line.data = s.shared.mem

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

def refinementInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  fullInv n s ∧ noDirtyInv n s ∧ txnDataInv n s

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
  intro s hinit i hvalid
  rcases hinit with ⟨⟨hmem, _, _, _, _, _⟩, hlocals⟩
  rcases hlocals i with ⟨hline, _, _, _, _, _, _, _, _⟩
  rw [hline] at hvalid
  simp at hvalid

private theorem plannedTxn_clean {n : Nat}
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

theorem init_refinementInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → refinementInv n s := by
  intro s hinit
  exact ⟨init_fullInv n s hinit, init_noDirtyInv n s hinit, init_txnDataInv n s hinit⟩

theorem init_strongRefinementInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → strongRefinementInv n s := by
  intro s hinit
  exact ⟨init_refinementInv n s hinit, init_txnLineInv n s hinit,
    init_preLinesCleanInv n s hinit, init_preLinesNoDirtyInv n s hinit,
    init_txnPlanInv n s hinit⟩

theorem noDirtyInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hnoDirty : noDirtyInv n s) (hnext : (tlMessages.toSpec n).next s s') :
    noDirtyInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock grow source =>
      intro j
      rw [sendAcquireBlock_line hstep]
      exact hnoDirty j
  | .sendAcquirePerm grow source =>
      intro j
      rw [sendAcquirePerm_line hstep]
      exact hnoDirty j
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, _, hs'⟩
        rcases hs' with ⟨_, hs'⟩
        intro j
        rw [hs']
        simpa [recvAcquireState, recvAcquireLocals_line] using hnoDirty j
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, _, hs'⟩
        rcases hs' with ⟨_, hs'⟩
        intro j
        rw [hs']
        simpa [recvAcquireState, recvAcquireLocals_line] using hnoDirty j
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩
      rcases hs' with ⟨_, hs'⟩
      intro j
      rw [hs']
      by_cases hji : j = i
      · subst j
        cases hparam : msg.param <;>
          simp [recvProbeState, recvProbeLocals, recvProbeLocal, setFn, probedLine,
            hparam, invalidatedLine, branchAfterProbe, tipAfterProbe]
      · simpa [recvProbeState, recvProbeLocals, setFn, hji] using hnoDirty j
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, hs'⟩
      intro j
      rw [hs']
      by_cases hji : j = i
      · subst j
        simpa [recvProbeAckState, recvProbeAckLocals, setFn]
          using hnoDirty i
      · simpa [recvProbeAckState, recvProbeAckLocals, setFn, hji]
          using hnoDirty j
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, _, _, _, _, _, _, _, _, hs'⟩
      intro j
      rw [hs']
      by_cases hji : j = i
      · subst j
        simpa [sendGrantState, sendGrantLocals, setFn] using hnoDirty i
      · simpa [sendGrantState, sendGrantLocals, setFn, hji] using hnoDirty j
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, _, hs'⟩
      intro j
      rw [hs']
      by_cases hji : j = i
      · subst j
        by_cases hdata : tx.grantHasData
        · cases hperm : tx.resultPerm <;> simp [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, grantLine, hdata, hperm, invalidatedLine, branchAfterProbe, tipAfterProbe]
        · simp [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, grantLine, hdata]
      · simpa [recvGrantState, recvGrantLocals, setFn, hji] using hnoDirty j
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩
      intro j
      rw [hs']
      simpa [recvGrantAckState_line] using hnoDirty j
  | .sendRelease param =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      intro j
      rw [hs']
      by_cases hji : j = i
      · subst j
        cases hres : param.result <;> simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, releasedLine, hres, invalidatedLine, branchAfterProbe, tipAfterProbe]
      · simpa [sendReleaseState, sendReleaseLocals, setFn, hji] using hnoDirty j
  | .sendReleaseData param =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hdirty, _hs'⟩
      exfalso
      rw [hnoDirty i] at hdirty
      contradiction
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, _, _, _, _, _, _, _, _, _, _, hs'⟩
      intro j
      rw [hs']
      simpa [recvReleaseState_line] using hnoDirty j
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, _, _, _, _, _, _, hs'⟩
      intro j
      rw [hs']
      simpa [recvReleaseAckState_line] using hnoDirty j

theorem txnDataInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hnoDirty : noDirtyInv n s) (htxnData : txnDataInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    txnDataInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [txnDataInv]
  | .sendAcquirePerm grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [txnDataInv]
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, _, hs'⟩
        rcases hs' with ⟨_, hs'⟩
        rcases plannedTxn_clean s i hnoDirty with ⟨hdirtySrc, htransfer⟩
        rw [hs']
        simp [txnDataInv, recvAcquireState, recvAcquireShared, plannedTxn, hdirtySrc, htransfer]
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, _, hs'⟩
        rcases hs' with ⟨_, hs'⟩
        rcases plannedTxn_clean s i hnoDirty with ⟨hdirtySrc, htransfer⟩
        rw [hs']
        simp [txnDataInv, recvAcquireState, recvAcquireShared, plannedTxn, hdirtySrc, htransfer]
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, hs'⟩
      rcases hs' with ⟨_, hs'⟩
      rw [hs']
      simpa [txnDataInv, hcur, recvProbeState] using htxnData
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [txnDataInv, hcur, recvProbeAckState, recvProbeAckShared] using htxnData
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [txnDataInv, hcur, sendGrantState, sendGrantShared] using htxnData
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [txnDataInv, hcur, recvGrantState, recvGrantShared] using htxnData
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnDataInv, recvGrantAckState, recvGrantAckShared]
  | .sendRelease param =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnDataInv, hcur, sendReleaseState]
  | .sendReleaseData param =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hdirty, _hs'⟩
      exfalso
      rw [hnoDirty i] at hdirty
      contradiction
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnDataInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnDataInv, hcur, recvReleaseAckState, recvReleaseAckShared]

theorem preLinesNoDirtyInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hnoDirty : noDirtyInv n s) (hpre : preLinesNoDirtyInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    preLinesNoDirtyInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesNoDirtyInv]
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesNoDirtyInv]
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, _, hrest⟩
        rcases hrest with ⟨_, hs'⟩
        rw [hs']
        intro k hk
        simp [preLinesNoDirtyInv, recvAcquireState, recvAcquireShared, plannedTxn, hk, hnoDirty ⟨k, hk⟩]
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, _, hrest⟩
        rcases hrest with ⟨_, hs'⟩
        rw [hs']
        intro k hk
        simp [preLinesNoDirtyInv, recvAcquireState, recvAcquireShared, plannedTxn, hk, hnoDirty ⟨k, hk⟩]
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesNoDirtyInv, hcur, recvProbeState]
        using hpre
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesNoDirtyInv, hcur, recvProbeAckState, recvProbeAckShared]
        using hpre
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesNoDirtyInv, hcur, sendGrantState, sendGrantShared]
        using hpre
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesNoDirtyInv, hcur, recvGrantState, recvGrantShared]
        using hpre
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesNoDirtyInv, recvGrantAckState, recvGrantAckShared]
  | .sendRelease _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesNoDirtyInv, hcur, sendReleaseState]
  | .sendReleaseData _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hdirty, _⟩
      exfalso
      rw [hnoDirty i] at hdirty
      contradiction
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesNoDirtyInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesNoDirtyInv, hcur, recvReleaseAckState, recvReleaseAckShared]

theorem preLinesCleanInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hclean : cleanDataInv n s) (hpre : preLinesCleanInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    preLinesCleanInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesCleanInv]
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesCleanInv]
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, _, hrest⟩
        rcases hrest with ⟨_, hs'⟩
        rw [hs']
        intro k hk hvalid
        have hvalid' : (s.locals ⟨k, hk⟩).line.valid = true := by
          simpa [plannedTxn, hk] using hvalid
        have hdata : (s.locals ⟨k, hk⟩).line.data = s.shared.mem := hclean ⟨k, hk⟩ hvalid'
        simpa [plannedTxn, hk] using hdata
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, _, hrest⟩
        rcases hrest with ⟨_, hs'⟩
        rw [hs']
        intro k hk hvalid
        have hvalid' : (s.locals ⟨k, hk⟩).line.valid = true := by
          simpa [plannedTxn, hk] using hvalid
        have hdata : (s.locals ⟨k, hk⟩).line.data = s.shared.mem := hclean ⟨k, hk⟩ hvalid'
        simpa [plannedTxn, hk] using hdata
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesCleanInv, hcur, recvProbeState]
        using hpre
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesCleanInv, hcur, recvProbeAckState, recvProbeAckShared]
        using hpre
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesCleanInv, hcur, sendGrantState, sendGrantShared]
        using hpre
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesCleanInv, hcur, recvGrantState, recvGrantShared]
        using hpre
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesCleanInv, recvGrantAckState, recvGrantAckShared]
  | .sendRelease _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesCleanInv, hcur, sendReleaseState]
  | .sendReleaseData _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesCleanInv, hcur, sendReleaseState]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesCleanInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesCleanInv, hcur, recvReleaseAckState, recvReleaseAckShared]


theorem refinementInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hinv : refinementInv n s) (hnext : (tlMessages.toSpec n).next s s') :
    refinementInv n s' := by
  rcases hinv with ⟨hfull, hnoDirty, htxnData⟩
  exact ⟨fullInv_preserved_with_release n s s' hfull hnext,
    noDirtyInv_preserved n s s' hnoDirty hnext,
    txnDataInv_preserved n s s' hnoDirty htxnData hnext⟩

/-- Map a message-level request kind to the atomic pending-grant kind. -/
def absGrantKind : ReqKind → TileLink.Atomic.GrantKind
  | .acquireBlock => .block
  | .acquirePerm => .perm

/-- Abstraction of a live message-level manager transaction to the atomic
    pending-grant summary. -/
def absPendingGrantMeta (tx : ManagerTxn) : TileLink.Atomic.PendingGrantMeta :=
  { requester := tx.requester
  , kind := absGrantKind tx.kind
  , requesterPerm := tx.resultPerm
  , usedDirtySource := tx.usedDirtySource
  , transferVal := tx.transferVal
  , probesNeeded := tx.probesNeeded
  , probesRemaining :=
      if tx.phase = .grantPendingAck then
        TileLink.Atomic.noProbeMask
      else
        tx.probesNeeded }

/-- Directory view before an acquire wave takes effect. -/
def preTxnDir (n : Nat) (tx : ManagerTxn) (dir : Nat → TLPerm) : Nat → TLPerm :=
  fun k =>
    if _hk : k < n then
      (tx.preLines k).perm
    else
      dir k

/-- Pick the unique queued release wave, if any. Reachable states in the
    current single-line model never have more than one. -/
noncomputable def queuedReleaseIdx (n : Nat) (s : SymState HomeState NodeState n) : Option Nat :=
  if h : ∃ i : Fin n, (s.locals i).releaseInFlight = true ∧ (s.locals i).chanC ≠ none then
    some (Classical.choose h).1
  else
    none

/-- Atomic-style directory view during `grantPendingAck`: requester permission
    is visible even if the concrete requester has not yet consumed D. -/
def grantPendingDir (n : Nat) (tx : ManagerTxn) (dir : Nat → TLPerm) : Nat → TLPerm :=
  if hk : tx.requester < n then
    updateDirAt dir ⟨tx.requester, hk⟩ tx.resultPerm
  else
    dir

/-- Message-level shared state mapped to the atomic wave-level summary state. -/
noncomputable def refMapShared (n : Nat) (s : SymState HomeState NodeState n) :
    TileLink.Atomic.HomeState :=
  let dir :=
    match s.shared.currentTxn with
    | none => TileLink.Atomic.syncDir s.shared.dir (fun i => (s.locals i).line)
    | some tx =>
        if tx.phase = .grantPendingAck then
          grantPendingDir n tx s.shared.dir
        else
          preTxnDir n tx s.shared.dir
  let pendingReleaseAck :=
    match s.shared.pendingReleaseAck with
    | some i => some i
    | none =>
        match s.shared.currentTxn with
        | some _ => none
        | none => queuedReleaseIdx n s
  { mem := s.shared.mem
  , dir := dir
  , pendingGrantMeta := s.shared.currentTxn.map absPendingGrantMeta
  , pendingGrantAck := s.shared.pendingGrantAck
  , pendingReleaseAck := pendingReleaseAck }

/-- Local-line abstraction during an active acquire wave. Before grant delivery,
    lines are hidden behind the transaction snapshot; after grant delivery, the
    requester is synthesized from the grant metadata even if the concrete D
    message is still pending. -/
def refMapLine (s : SymState HomeState NodeState n) (i : Fin n) : CacheLine :=
  match s.shared.currentTxn with
  | none => (s.locals i).line
  | some tx =>
      if tx.phase = .grantPendingAck then
        if _hreq : tx.requester = i.1 then
          grantLine (tx.preLines i.1) tx
        else
          (s.locals i).line
      else
        tx.preLines i.1

/-- Refinement map from the explicit message model to the atomic model. -/
noncomputable def refMap (n : Nat) (s : SymState HomeState NodeState n) :
    SymState TileLink.Atomic.HomeState CacheLine n :=
  { shared := refMapShared n s
  , locals := refMapLine s }

private theorem syncDir_lines_eq {n : Nat} (dir : Nat → TLPerm)
    (ls ls' : Fin n → NodeState)
    (hline : ∀ i : Fin n, (ls' i).line = (ls i).line) :
    TileLink.Atomic.syncDir dir (fun i => (ls' i).line) =
      TileLink.Atomic.syncDir dir (fun i => (ls i).line) := by
  funext k
  by_cases hk : k < n
  · let i : Fin n := ⟨k, hk⟩
    simp [TileLink.Atomic.syncDir, hk]
    exact congrArg CacheLine.perm (hline i)
  · simp [TileLink.Atomic.syncDir, hk]

private theorem refMapLine_eq_preLines_of_not_grantPendingAck {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hcur : s.shared.currentTxn = some tx) (hphase : tx.phase ≠ .grantPendingAck)
    (i : Fin n) :
    refMapLine s i = tx.preLines i.1 := by
  simp [refMapLine, hcur, hphase]

private theorem queuedReleaseIdx_eq_of_chanC_releaseEq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hC : ∀ j : Fin n, (s'.locals j).chanC = (s.locals j).chanC)
    (hflight : ∀ j : Fin n, (s'.locals j).releaseInFlight = (s.locals j).releaseInFlight) :
    queuedReleaseIdx n s' = queuedReleaseIdx n s := by
  simp [queuedReleaseIdx, hC, hflight]

private theorem queuedReleaseIdx_eq_none_of_all_chanC_none {n : Nat}
    (s : SymState HomeState NodeState n)
    (hallC : ∀ j : Fin n, (s.locals j).chanC = none) :
    queuedReleaseIdx n s = none := by
  unfold queuedReleaseIdx
  have hnone : ¬∃ i : Fin n, (s.locals i).releaseInFlight = true ∧ (s.locals i).chanC ≠ none := by
    intro h
    rcases h with ⟨i, _, hC⟩
    rw [hallC i] at hC
    contradiction
  simp [hnone]

private theorem preTxnDir_updateDirAt_eq {n : Nat} (tx : ManagerTxn)
    (dir : Nat → TLPerm) (i : Fin n) (perm : TLPerm) :
    preTxnDir n tx (updateDirAt dir i perm) = preTxnDir n tx dir := by
  funext k
  by_cases hk : k < n
  · simp [preTxnDir, hk]
  · have hne : k ≠ i.1 := by
      intro h
      exact hk (h ▸ i.is_lt)
    simp [preTxnDir, hk, updateDirAt, hne]

private theorem preTxnDir_tx_update_eq {n : Nat} (tx : ManagerTxn)
    (dir : Nat → TLPerm) (phase : TxnPhase) (probesRemaining : Nat → Bool) :
    preTxnDir n { tx with phase := phase, probesRemaining := probesRemaining } dir =
      preTxnDir n tx dir := by
  funext k
  by_cases hk : k < n <;> simp [preTxnDir, hk]

private theorem preTxnDir_plannedTxn_eq_syncDir {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (kind : ReqKind) (grow : GrowParam) (source : SourceId) :
    preTxnDir n (plannedTxn s i kind grow source) s.shared.dir =
      TileLink.Atomic.syncDir s.shared.dir (fun j => (s.locals j).line) := by
  funext k
  by_cases hk : k < n
  · simp [preTxnDir, plannedTxn, TileLink.Atomic.syncDir, hk]
  · simp [preTxnDir, plannedTxn, TileLink.Atomic.syncDir, hk]

private theorem grantPendingDir_updateDirAt_eq {n : Nat} (tx : ManagerTxn)
    (dir : Nat → TLPerm) (i : Fin n) (perm : TLPerm)
    (hreq : tx.requester = i.1) :
    grantPendingDir n tx (updateDirAt dir i perm) = grantPendingDir n tx dir := by
  funext k
  by_cases hk : tx.requester < n
  · by_cases hki : k = i.1
    · subst k
      simp [grantPendingDir, hk, updateDirAt, hreq]
    · simp [grantPendingDir, hk, updateDirAt, hreq, hki]
  · exfalso
    exact hk (hreq ▸ i.is_lt)

private theorem txnDataInv_currentTxn {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (htxnData : txnDataInv n s) (hcur : s.shared.currentTxn = some tx) :
    tx.usedDirtySource = false ∧ tx.transferVal = s.shared.mem := by
  simpa [txnDataInv, hcur] using htxnData

private theorem txnCoreInv_grantReady_allFalse {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hfull : fullInv n s) (hcur : s.shared.currentTxn = some tx) (hphase : tx.phase = .grantReady) :
    ∀ j : Fin n, tx.probesRemaining j.1 = false := by
  rcases hfull with ⟨⟨_, _, _, htxnCore⟩, _, _⟩
  rcases (by simpa [txnCoreInv, hcur] using htxnCore :
      tx.requester < n ∧
      (tx.phase = .probing ∨ tx.phase = .grantReady ∨ tx.phase = .grantPendingAck) ∧
      tx.resultPerm = tx.grow.result ∧
      (tx.grantHasData = false → tx.resultPerm = .T) ∧
      tx.probesNeeded tx.requester = false ∧
      (∀ k : Nat, tx.probesRemaining k = true → tx.probesNeeded k = true) ∧
      (tx.phase = .grantReady → ∀ j : Fin n, tx.probesRemaining j.1 = false) ∧
      (tx.phase = .grantPendingAck → ∀ j : Fin n, tx.probesRemaining j.1 = false))
    with ⟨_, _, _, _, _, _, hready, _⟩
  exact hready hphase

private theorem chanC_none_of_phase_ne_probing {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hfull : fullInv n s) (hcur : s.shared.currentTxn = some tx)
    (hphase : tx.phase ≠ .probing) :
    ∀ j : Fin n, (s.locals j).chanC = none := by
  rcases hfull with ⟨_, hchan, _⟩
  rcases hchan with ⟨_, _, hchanC, _, _⟩
  intro j
  specialize hchanC j
  cases hC : (s.locals j).chanC with
  | none => rfl
  | some msg =>
      rw [hC] at hchanC
      rcases hchanC with ⟨tx', hcur', hprobe, _, _, _, _⟩ | ⟨_, htxnNone, _, _, _, _, _⟩
      · rw [hcur] at hcur'
        cases hcur'
        exact False.elim (hphase hprobe)
      · rw [hcur] at htxnNone
        cases htxnNone

private theorem txnPlanInv_acquireBlock_branch {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hplan : txnPlanInv n s) (hcur : s.shared.currentTxn = some tx)
    (hkind : tx.kind = .acquireBlock) (hperm : tx.resultPerm = .B) :
    snapshotHasCachedOther n tx ∧ tx.probesNeeded = snapshotWritableProbeMask n tx := by
  rcases (by simpa [txnPlanInv, hcur, hkind] using hplan :
      tx.requester < n ∧
      tx.grantHasData = decide (tx.kind = .acquireBlock) ∧
      ((tx.resultPerm = .B →
          snapshotHasCachedOther n tx ∧ tx.probesNeeded = snapshotWritableProbeMask n tx) ∧
        (tx.resultPerm = .T →
          snapshotAllOthersInvalid n tx ∧ tx.probesNeeded = TileLink.Atomic.noProbeMask)))
    with ⟨_, _, hbranch, _⟩
  exact hbranch hperm

private theorem txnPlanInv_grantHasData {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hplan : txnPlanInv n s) (hcur : s.shared.currentTxn = some tx) :
    tx.grantHasData = decide (tx.kind = .acquireBlock) := by
  rcases (by simpa [txnPlanInv, hcur] using hplan :
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
          (tx.preLines tx.requester).perm ≠ .T) with ⟨_, hgrant, _⟩
  exact hgrant

private theorem txnPlanInv_acquireBlock_tip {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hplan : txnPlanInv n s) (hcur : s.shared.currentTxn = some tx)
    (hkind : tx.kind = .acquireBlock) (hperm : tx.resultPerm = .T) :
    snapshotAllOthersInvalid n tx ∧ tx.probesNeeded = TileLink.Atomic.noProbeMask := by
  rcases (by simpa [txnPlanInv, hcur, hkind] using hplan :
      tx.requester < n ∧
      tx.grantHasData = decide (tx.kind = .acquireBlock) ∧
      ((tx.resultPerm = .B →
          snapshotHasCachedOther n tx ∧ tx.probesNeeded = snapshotWritableProbeMask n tx) ∧
        (tx.resultPerm = .T →
          snapshotAllOthersInvalid n tx ∧ tx.probesNeeded = TileLink.Atomic.noProbeMask)))
    with ⟨_, _, _, htip⟩
  exact htip hperm

private theorem txnPlanInv_acquirePerm {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hplan : txnPlanInv n s) (hcur : s.shared.currentTxn = some tx)
    (hkind : tx.kind = .acquirePerm) :
    tx.resultPerm = .T ∧
      tx.probesNeeded = snapshotCachedProbeMask n tx ∧
      (tx.preLines tx.requester).perm ≠ .T := by
  rcases (by simpa [txnPlanInv, hcur, hkind] using hplan :
      tx.requester < n ∧
        tx.grantHasData = false ∧
        tx.resultPerm = .T ∧
        tx.probesNeeded = snapshotCachedProbeMask n tx ∧
        (tx.preLines tx.requester).perm ≠ .T)
    with ⟨_, _, hperm, hmask, hnotT⟩
  exact ⟨hperm, hmask, hnotT⟩

private theorem txnSnapshotLine_eq_of_grantReady {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (hcur : s.shared.currentTxn = some tx) (hphase : tx.phase = .grantReady) :
    ∀ j : Fin n,
      (s.locals j).line =
        (if tx.probesNeeded j.1 then
          probedLine (tx.preLines j.1) (probeCapOfResult tx.resultPerm)
        else
          tx.preLines j.1) := by
  intro j
  have hallFalse := txnCoreInv_grantReady_allFalse hfull hcur hphase j
  have hlines : ∀ i : Fin n, (s.locals i).line = txnSnapshotLine tx (s.locals i) i := by
    simpa [txnLineInv, hcur] using htxnLine
  specialize hlines j
  simpa [txnSnapshotLine, probeSnapshotLine, hphase, hallFalse] using hlines

private theorem txnSnapshotLine_eq_of_grantPendingAck_nonrequester {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (hcur : s.shared.currentTxn = some tx) (hphase : tx.phase = .grantPendingAck)
    {j : Fin n} (hreqj : tx.requester ≠ j.1) :
    (s.locals j).line =
      (if tx.probesNeeded j.1 then
        probedLine (tx.preLines j.1) (probeCapOfResult tx.resultPerm)
      else
        tx.preLines j.1) := by
  have hallFalse := by
    rcases hfull with ⟨⟨_, _, _, htxnCore⟩, _, _⟩
    rcases (by simpa [txnCoreInv, hcur] using htxnCore :
        tx.requester < n ∧
        (tx.phase = .probing ∨ tx.phase = .grantReady ∨ tx.phase = .grantPendingAck) ∧
        tx.resultPerm = tx.grow.result ∧
        (tx.grantHasData = false → tx.resultPerm = .T) ∧
        tx.probesNeeded tx.requester = false ∧
        (∀ k : Nat, tx.probesRemaining k = true → tx.probesNeeded k = true) ∧
        (tx.phase = .grantReady → ∀ j : Fin n, tx.probesRemaining j.1 = false) ∧
        (tx.phase = .grantPendingAck → ∀ j : Fin n, tx.probesRemaining j.1 = false))
      with ⟨_, _, _, _, _, _, _, hgp⟩
    exact hgp hphase j
  have hlines : ∀ i : Fin n, (s.locals i).line = txnSnapshotLine tx (s.locals i) i := by
    simpa [txnLineInv, hcur] using htxnLine
  specialize hlines j
  have hreqj' : tx.requester = j.1 ∧ (s.locals j).chanE = none → False := by
    intro h
    exact hreqj h.1
  simpa [txnSnapshotLine, probeSnapshotLine, hphase, hreqj, hallFalse, hreqj'] using hlines

theorem write_grant_nonrequester_invalid_of_strongRefinementInv {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hinv : strongRefinementInv n s)
    (hcur : s.shared.currentTxn = some tx)
    (hphase : tx.phase = .grantReady ∨ tx.phase = .grantPendingAck)
    (hperm : tx.resultPerm = .T) :
    ∀ j : Fin n, j.1 ≠ tx.requester → (s.locals j).line.perm = .N := by
  rcases hinv with ⟨⟨hfull, _, _⟩, htxnLine, _, _, hplan⟩
  intro j hreqj
  cases hkind : tx.kind with
  | acquireBlock =>
      have hallInvalid : snapshotAllOthersInvalid n tx :=
        (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).1
      have hpreN : (tx.preLines j.1).perm = .N := hallInvalid j hreqj
      cases hphase with
      | inl hready =>
          have hlinej := txnSnapshotLine_eq_of_grantReady hfull htxnLine hcur hready j
          have hmask : tx.probesNeeded = TileLink.Atomic.noProbeMask :=
            (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).2
          have hprobe : tx.probesNeeded j.1 = false := by
            rw [hmask]
            simp [TileLink.Atomic.noProbeMask]
          rw [hlinej, hprobe]
          simpa [hpreN]
      | inr hgp =>
          have hlinej :=
            txnSnapshotLine_eq_of_grantPendingAck_nonrequester hfull htxnLine hcur hgp
              (fun h => hreqj h.symm)
          have hmask : tx.probesNeeded = TileLink.Atomic.noProbeMask :=
            (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).2
          have hprobe : tx.probesNeeded j.1 = false := by
            rw [hmask]
            simp [TileLink.Atomic.noProbeMask]
          rw [hlinej, hprobe]
          simpa [hpreN]
  | acquirePerm =>
      have hmask : tx.probesNeeded = snapshotCachedProbeMask n tx :=
        (txnPlanInv_acquirePerm hplan hcur hkind).2.1
      cases hphase with
      | inl hready =>
          have hlinej := txnSnapshotLine_eq_of_grantReady hfull htxnLine hcur hready j
          by_cases hN : (tx.preLines j.1).perm = .N
          · have hprobe : tx.probesNeeded j.1 = false := by
              rw [hmask]
              simp [snapshotCachedProbeMask, j.is_lt, hN]
            rw [hlinej, hprobe]
            simpa [hN]
          · have hprobe : tx.probesNeeded j.1 = true := by
              rw [hmask]
              simp [snapshotCachedProbeMask, j.is_lt, hN]
              exact fun h => hreqj h
            rw [hlinej, hprobe]
            simpa [hperm, probedLine, probeCapOfResult]
      | inr hgp =>
          have hlinej :=
            txnSnapshotLine_eq_of_grantPendingAck_nonrequester hfull htxnLine hcur hgp
              (fun h => hreqj h.symm)
          by_cases hN : (tx.preLines j.1).perm = .N
          · have hprobe : tx.probesNeeded j.1 = false := by
              rw [hmask]
              simp [snapshotCachedProbeMask, j.is_lt, hN]
            rw [hlinej, hprobe]
            simpa [hN]
          · have hprobe : tx.probesNeeded j.1 = true := by
              rw [hmask]
              simp [snapshotCachedProbeMask, j.is_lt, hN]
              exact fun h => hreqj h
            rw [hlinej, hprobe]
            simpa [hperm, probedLine, probeCapOfResult]

private theorem preLine_data_eq_mem_of_grantReady_T {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {j : Fin n}
    (hfull : fullInv n s) (hclean : cleanDataInv n s) (htxnLine : txnLineInv n s)
    (hcur : s.shared.currentTxn = some tx) (hphase : tx.phase = .grantReady)
    (hres : tx.resultPerm = .B)
    (hpermT : (tx.preLines j.1).perm = .T)
    (hmask : tx.probesNeeded = snapshotWritableProbeMask n tx)
    (hreqj : tx.requester ≠ j.1) :
    (tx.preLines j.1).data = s.shared.mem := by
  have hprobe : tx.probesNeeded j.1 = true := by
    rw [hmask]
    simp [snapshotWritableProbeMask, j.is_lt, hpermT]
    exact fun h => hreqj h.symm
  have hlinej := txnSnapshotLine_eq_of_grantReady hfull htxnLine hcur hphase j
  have hactual : (s.locals j).line = branchAfterProbe (tx.preLines j.1) := by
    rw [hlinej, hprobe]
    simp [hres, hpermT, probeCapOfResult, probedLine]
  have hvalid : (s.locals j).line.valid = true := by
    simpa [hactual, branchAfterProbe]
  have hdata : (s.locals j).line.data = s.shared.mem := hclean j hvalid
  simpa [hactual, branchAfterProbe] using hdata

private theorem refMapLine_sendGrant_requester_block_branch_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase = .grantReady) (hkind : tx.kind = .acquireBlock)
    (hperm : tx.resultPerm = .B) :
    refMapLine (sendGrantState s i tx) i =
      TileLink.Atomic.branchLine (refMap n s).shared.mem := by
  have hgrantData : tx.grantHasData = true := by
    rw [txnPlanInv_grantHasData hplan hcur, hkind]
    simp
  have htransfer : tx.transferVal = s.shared.mem := (txnDataInv_currentTxn htxnData hcur).2
  simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals, hreq,
    grantLine, TileLink.Atomic.branchLine, refMap, refMapShared]
  rw [hgrantData, hperm, htransfer]
  rfl

private theorem refMapLine_sendGrant_requester_block_tip_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase = .grantReady) (hkind : tx.kind = .acquireBlock)
    (hperm : tx.resultPerm = .T) :
    refMapLine (sendGrantState s i tx) i =
      TileLink.Atomic.tipLine (refMap n s).shared.mem := by
  have hgrantData : tx.grantHasData = true := by
    rw [txnPlanInv_grantHasData hplan hcur, hkind]
    simp
  have htransfer : tx.transferVal = s.shared.mem := (txnDataInv_currentTxn htxnData hcur).2
  simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals, hreq,
    grantLine, TileLink.Atomic.tipLine, refMap, refMapShared]
  rw [hgrantData, hperm, htransfer]
  rfl

private theorem refMapLine_sendGrant_requester_acquirePerm_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase = .grantReady) (hkind : tx.kind = .acquirePerm) :
    refMapLine (sendGrantState s i tx) i =
      TileLink.Atomic.grantPermLine ((refMap n s).locals i) := by
  have hgrantData : tx.grantHasData = false := by
    rw [txnPlanInv_grantHasData hplan hcur, hkind]
    simp
  simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals, hreq,
    grantLine, TileLink.Atomic.grantPermLine, refMap, refMapShared, hcur, hphase]
  simp [hgrantData]

private theorem refMapLine_sendGrant_nonrequester_block_branch_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i j : Fin n}
    (hfull : fullInv n s) (hclean : cleanDataInv n s) (htxnLine : txnLineInv n s)
    (hplan : txnPlanInv n s) (hcur : s.shared.currentTxn = some tx)
    (hreq : tx.requester = i.1) (hphase : tx.phase = .grantReady)
    (hkind : tx.kind = .acquireBlock) (hperm : tx.resultPerm = .B)
    (hji : j ≠ i) :
    refMapLine (sendGrantState s i tx) j =
      TileLink.Atomic.acquireBlockSharedLocals (refMap n s) i j := by
  have hmask : tx.probesNeeded = snapshotWritableProbeMask n tx :=
    (txnPlanInv_acquireBlock_branch hplan hcur hkind hperm).2
  have hreqj : tx.requester ≠ j.1 := by
    intro h
    apply hji
    exact Fin.ext (h.symm.trans hreq)
  have hlinej := txnSnapshotLine_eq_of_grantReady hfull htxnLine hcur hphase j
  by_cases hT : (tx.preLines j.1).perm = .T
  · have hdata : (tx.preLines j.1).data = s.shared.mem :=
      preLine_data_eq_mem_of_grantReady_T hfull hclean htxnLine hcur hphase hperm hT hmask hreqj
    have hprobe : tx.probesNeeded j.1 = true := by
      rw [hmask]
      by_cases hreqeq : tx.requester = j.1
      · exact False.elim (hreqj hreqeq)
      · simp [snapshotWritableProbeMask, j.is_lt, hT]
        exact fun h => hreqeq h.symm
    have hactual : (s.locals j).line = branchAfterProbe (tx.preLines j.1) := by
      rw [hlinej, hprobe]
      simp [hperm, probedLine, probeCapOfResult]
    calc
      refMapLine (sendGrantState s i tx) j = (s.locals j).line := by
        simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals, hji, hreqj]
      _ = branchAfterProbe (tx.preLines j.1) := hactual
      _ = TileLink.Atomic.branchLine s.shared.mem := by
        simp [branchAfterProbe, TileLink.Atomic.branchLine, hdata]
      _ = TileLink.Atomic.acquireBlockSharedLocals (refMap n s) i j := by
        have href : (refMap n s).locals j = tx.preLines j.1 := by
          simp [refMap, refMapLine, hcur, hphase]
        rw [TileLink.Atomic.acquireBlockSharedLocals, href]
        simp [hji, hT, TileLink.Atomic.branchLine, refMap, refMapShared]
  · have hprobe : tx.probesNeeded j.1 = false := by
      rw [hmask]
      by_cases hreqeq : tx.requester = j.1
      · exact False.elim (hreqj hreqeq)
      · simp [snapshotWritableProbeMask, j.is_lt, hT]
    calc
      refMapLine (sendGrantState s i tx) j = (s.locals j).line := by
        simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals, hji, hreqj]
      _ = tx.preLines j.1 := by
        rw [hlinej, hprobe]
        simp
      _ = TileLink.Atomic.acquireBlockSharedLocals (refMap n s) i j := by
        have href : (refMap n s).locals j = tx.preLines j.1 := by
          simp [refMap, refMapLine, hcur, hphase]
        rw [TileLink.Atomic.acquireBlockSharedLocals, href]
        simp [hji, hT]

private theorem invalidatedLine_eq_self_of_perm_N_wf {line : CacheLine}
    (hwf : line.WellFormed) (hperm : line.perm = .N) :
    invalidatedLine line = line := by
  rcases hwf.2.2 hperm with ⟨hvalid, hdirty⟩
  cases line
  simp at hperm
  subst hperm
  simp [invalidatedLine]
  exact ⟨hvalid, hdirty⟩

private theorem refMapLine_sendGrant_nonrequester_block_tip_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i j : Fin n}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (hplan : txnPlanInv n s) (hcur : s.shared.currentTxn = some tx)
    (hreq : tx.requester = i.1) (hphase : tx.phase = .grantReady)
    (hkind : tx.kind = .acquireBlock) (hperm : tx.resultPerm = .T)
    (hji : j ≠ i) :
    refMapLine (sendGrantState s i tx) j =
      TileLink.setFn (refMap n s).locals i (TileLink.Atomic.tipLine (refMap n s).shared.mem) j := by
  have hallInvalid : snapshotAllOthersInvalid n tx :=
    (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).1
  have hreqj : tx.requester ≠ j.1 := by
    intro h
    apply hji
    exact Fin.ext (h.symm.trans hreq)
  have hpermN : (tx.preLines j.1).perm = .N := hallInvalid j hreqj.symm
  have hprobe : tx.probesNeeded j.1 = false := by
    rw [(txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).2]
    simp [TileLink.Atomic.noProbeMask]
  have hlinej := txnSnapshotLine_eq_of_grantReady hfull htxnLine hcur hphase j
  calc
    refMapLine (sendGrantState s i tx) j = (s.locals j).line := by
      simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals, hji, hreqj]
    _ = tx.preLines j.1 := by
      rw [hlinej, hprobe]
      simp
    _ = (refMap n s).locals j := by
      simp [refMap, refMapLine, hcur, hphase]
    _ = TileLink.setFn (refMap n s).locals i (TileLink.Atomic.tipLine (refMap n s).shared.mem) j := by
      simp [TileLink.setFn, hji]

private theorem refMapLine_sendGrant_nonrequester_acquirePerm_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i j : Fin n}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (hplan : txnPlanInv n s) (hcur : s.shared.currentTxn = some tx)
    (hreq : tx.requester = i.1) (hphase : tx.phase = .grantReady)
    (hkind : tx.kind = .acquirePerm) (hji : j ≠ i) :
    refMapLine (sendGrantState s i tx) j =
      TileLink.Atomic.acquirePermLocals (refMap n s) i j := by
  have hfull0 := hfull
  rcases hfull with ⟨⟨hlineWF, _, _, _⟩, _, _⟩
  have hmask : tx.probesNeeded = snapshotCachedProbeMask n tx :=
    (txnPlanInv_acquirePerm hplan hcur hkind).2.1
  have hpermT : tx.resultPerm = .T :=
    (txnPlanInv_acquirePerm hplan hcur hkind).1
  have hreqj : tx.requester ≠ j.1 := by
    intro h
    apply hji
    exact Fin.ext (h.symm.trans hreq)
  have hlinej := txnSnapshotLine_eq_of_grantReady hfull0 htxnLine hcur hphase j
  by_cases hN : (tx.preLines j.1).perm = .N
  · have hprobe : tx.probesNeeded j.1 = false := by
      rw [hmask]
      by_cases hreqeq : tx.requester = j.1
      · exact False.elim (hreqj hreqeq)
      · simp [snapshotCachedProbeMask, j.is_lt, hN]
    have hcurLine : (s.locals j).line = tx.preLines j.1 := by
      rw [hlinej, hprobe]
      simp
    have hwfPre : (tx.preLines j.1).WellFormed := by
      rw [← hcurLine]
      exact hlineWF j
    calc
      refMapLine (sendGrantState s i tx) j = (s.locals j).line := by
        simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals, hji, hreqj]
      _ = tx.preLines j.1 := hcurLine
      _ = invalidatedLine (tx.preLines j.1) := by
        symm
        exact invalidatedLine_eq_self_of_perm_N_wf hwfPre hN
      _ = TileLink.Atomic.invalidateLine (tx.preLines j.1) := by
        rfl
      _ = TileLink.Atomic.acquirePermLocals (refMap n s) i j := by
        have href : (refMap n s).locals j = tx.preLines j.1 := by
          simp [refMap, refMapLine, hcur, hphase]
        rw [TileLink.Atomic.acquirePermLocals, href]
        simp [hji]
  · have hprobe : tx.probesNeeded j.1 = true := by
      rw [hmask]
      by_cases hreqeq : tx.requester = j.1
      · exact False.elim (hreqj hreqeq)
      · simp [snapshotCachedProbeMask, j.is_lt, hN]
        exact fun h => hreqeq h.symm
    have hcurLine : (s.locals j).line = invalidatedLine (tx.preLines j.1) := by
      rw [hlinej, hprobe]
      simp [hpermT, probedLine, probeCapOfResult]
    calc
      refMapLine (sendGrantState s i tx) j = (s.locals j).line := by
        simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals, hji, hreqj]
      _ = invalidatedLine (tx.preLines j.1) := hcurLine
      _ = TileLink.Atomic.invalidateLine (tx.preLines j.1) := by
        rfl
      _ = TileLink.Atomic.acquirePermLocals (refMap n s) i j := by
        have href : (refMap n s).locals j = tx.preLines j.1 := by
          simp [refMap, refMapLine, hcur, hphase]
        rw [TileLink.Atomic.acquirePermLocals, href]
        simp [hji]

private theorem refMap_sendGrant_block_branch_locals_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hfull : fullInv n s) (hclean : cleanDataInv n s) (htxnLine : txnLineInv n s)
    (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase = .grantReady) (hkind : tx.kind = .acquireBlock)
    (hperm : tx.resultPerm = .B) :
    (refMap n (sendGrantState s i tx)).locals =
      TileLink.Atomic.acquireBlockSharedLocals (refMap n s) i := by
  funext j
  by_cases hji : j = i
  · subst hji
    simpa [refMap, TileLink.Atomic.acquireBlockSharedLocals] using
      refMapLine_sendGrant_requester_block_branch_eq htxnData hplan hcur hreq hphase hkind hperm
  · simpa [refMap] using
      refMapLine_sendGrant_nonrequester_block_branch_eq hfull hclean htxnLine hplan hcur hreq hphase
        hkind hperm hji

private theorem refMap_sendGrant_block_tip_locals_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase = .grantReady) (hkind : tx.kind = .acquireBlock)
    (hperm : tx.resultPerm = .T) :
    (refMap n (sendGrantState s i tx)).locals =
      TileLink.setFn (refMap n s).locals i (TileLink.Atomic.tipLine (refMap n s).shared.mem) := by
  funext j
  by_cases hji : j = i
  · subst hji
    simpa [refMap, TileLink.setFn] using
      refMapLine_sendGrant_requester_block_tip_eq htxnData hplan hcur hreq hphase hkind hperm
  · simpa [refMap, TileLink.setFn, hji] using
      refMapLine_sendGrant_nonrequester_block_tip_eq hfull htxnLine hplan hcur hreq hphase hkind
        hperm hji

private theorem refMap_sendGrant_acquirePerm_locals_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase = .grantReady) (hkind : tx.kind = .acquirePerm) :
    (refMap n (sendGrantState s i tx)).locals =
      TileLink.Atomic.acquirePermLocals (refMap n s) i := by
  funext j
  by_cases hji : j = i
  · subst hji
    simpa [refMap, TileLink.Atomic.acquirePermLocals] using
      refMapLine_sendGrant_requester_acquirePerm_eq hplan hcur hreq hphase hkind
  · simpa [refMap] using
      refMapLine_sendGrant_nonrequester_acquirePerm_eq hfull htxnLine hplan hcur hreq hphase hkind hji

private theorem refMapShared_sendGrant_block_branch_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hfull : fullInv n s) (hclean : cleanDataInv n s) (htxnLine : txnLineInv n s)
    (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase = .grantReady) (hrel : s.shared.pendingReleaseAck = none)
    (hkind : tx.kind = .acquireBlock)
    (hperm : tx.resultPerm = .B) :
    refMapShared n (sendGrantState s i tx) =
      { mem := (refMap n s).shared.mem
      , dir := TileLink.Atomic.syncDir (refMap n s).shared.dir
          (TileLink.Atomic.acquireBlockSharedLocals (refMap n s) i)
      , pendingGrantMeta := some (TileLink.Atomic.deliveredGrantMeta (absPendingGrantMeta tx))
      , pendingGrantAck := some i.1
      , pendingReleaseAck := none } := by
  have hfull0 := hfull
  rcases hfull with ⟨⟨_, hdir, _, _⟩, _, _⟩
  rw [TileLink.Atomic.HomeState.mk.injEq]
  constructor
  · simp [refMap, refMapShared, sendGrantState, sendGrantShared, hcur]
  constructor
  · funext k
    by_cases hk : k < n
    · let j : Fin n := ⟨k, hk⟩
      by_cases hji : j = i
      · subst hji
        have hreqk : tx.requester = k := by
          simpa [j] using hreq
        calc
          grantPendingDir n { tx with phase := .grantPendingAck } s.shared.dir k = tx.resultPerm := by
            simp [grantPendingDir, updateDirAt, hk, hreqk]
          _ = TLPerm.B := hperm
          _ = TileLink.Atomic.syncDir (refMap n s).shared.dir
                (TileLink.Atomic.acquireBlockSharedLocals (refMap n s) j) k := by
              simp [TileLink.Atomic.syncDir, TileLink.Atomic.acquireBlockSharedLocals, refMap, hk, j]
      · have hreqj : tx.requester ≠ j.1 := by
          intro h
          apply hji
          exact Fin.ext (h.symm.trans hreq)
        have hCnone : (s.locals j).chanC = none :=
          chanC_none_of_phase_ne_probing hfull0 hcur (by simp [hphase]) j
        have hdirj : s.shared.dir j.1 = (s.locals j).line.perm := hdir j hCnone
        have hlocalPerm :
            (TileLink.Atomic.acquireBlockSharedLocals (refMap n s) i j).perm =
              (s.locals j).line.perm := by
          have hlocals :=
            refMap_sendGrant_block_branch_locals_eq hfull0 hclean htxnLine htxnData hplan hcur
              hreq hphase hkind hperm
          have hlineEq :
              refMapLine (sendGrantState s i tx) j = (s.locals j).line := by
            simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals, hji, hreqj]
          have hpermEq :=
            congrArg CacheLine.perm (congrFun hlocals j)
          have hpermEq' :
              (s.locals j).line.perm =
                (TileLink.Atomic.acquireBlockSharedLocals (refMap n s) i j).perm := by
            simpa [refMap, hlineEq] using hpermEq
          simpa using hpermEq'.symm
        have hktx : k ≠ tx.requester := by
          exact fun h => hreqj h.symm
        have hki : k ≠ i.1 := by
          intro h
          apply hji
          exact Fin.ext h
        calc
          grantPendingDir n { tx with phase := .grantPendingAck } s.shared.dir k = s.shared.dir k := by
            simp [grantPendingDir, updateDirAt, hk, hreq, hki]
          _ = (s.locals j).line.perm := hdirj
          _ = (TileLink.Atomic.acquireBlockSharedLocals (refMap n s) i j).perm := hlocalPerm.symm
          _ = TileLink.Atomic.syncDir (refMap n s).shared.dir
                (TileLink.Atomic.acquireBlockSharedLocals (refMap n s) i) k := by
              simpa [TileLink.Atomic.syncDir, hk, j]
    · have hki : k ≠ i.1 := by
        intro hkiEq
        apply hk
        simpa [hkiEq] using i.is_lt
      simp [refMap, refMapShared, sendGrantState, sendGrantShared, grantPendingDir,
        TileLink.Atomic.syncDir, preTxnDir, updateDirAt, hcur, hreq, hphase, hk, hki]
  constructor
  · simp [refMapShared, sendGrantState, sendGrantShared, absPendingGrantMeta,
      TileLink.Atomic.deliveredGrantMeta, hcur, hphase]
  constructor
  · simp [refMapShared, sendGrantState, sendGrantShared, hcur, hreq]
  · simp [refMapShared, sendGrantState, sendGrantShared, hcur, hrel]

private theorem refMapShared_sendGrant_block_tip_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase = .grantReady) (hrel : s.shared.pendingReleaseAck = none)
    (hkind : tx.kind = .acquireBlock)
    (hperm : tx.resultPerm = .T) :
    refMapShared n (sendGrantState s i tx) =
      { mem := (refMap n s).shared.mem
      , dir := TileLink.Atomic.syncDir (refMap n s).shared.dir
          (TileLink.setFn (refMap n s).locals i (TileLink.Atomic.tipLine (refMap n s).shared.mem))
      , pendingGrantMeta := some (TileLink.Atomic.deliveredGrantMeta (absPendingGrantMeta tx))
      , pendingGrantAck := some i.1
      , pendingReleaseAck := none } := by
  have hfull0 := hfull
  rcases hfull with ⟨⟨_, hdir, _, _⟩, _, _⟩
  have hallInvalid : snapshotAllOthersInvalid n tx :=
    (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).1
  have hmask : tx.probesNeeded = TileLink.Atomic.noProbeMask :=
    (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).2
  rw [TileLink.Atomic.HomeState.mk.injEq]
  constructor
  · simp [refMap, refMapShared, sendGrantState, sendGrantShared, hcur]
  constructor
  · funext k
    by_cases hk : k < n
    · let j : Fin n := ⟨k, hk⟩
      by_cases hji : j = i
      · subst hji
        have hreqk : tx.requester = k := by
          simpa [j] using hreq
        calc
          grantPendingDir n { tx with phase := .grantPendingAck } s.shared.dir k = tx.resultPerm := by
            simp [grantPendingDir, updateDirAt, hk, hreqk]
          _ = TLPerm.T := hperm
          _ = TileLink.Atomic.syncDir (refMap n s).shared.dir
                (TileLink.setFn (refMap n s).locals j (TileLink.Atomic.tipLine (refMap n s).shared.mem)) k := by
              simp [TileLink.Atomic.syncDir, TileLink.setFn, hk, j]
      · have hreqj : tx.requester ≠ j.1 := by
          intro h
          apply hji
          exact Fin.ext (h.symm.trans hreq)
        have hCnone : (s.locals j).chanC = none :=
          chanC_none_of_phase_ne_probing hfull0 hcur (by simp [hphase]) j
        have hdirj : s.shared.dir j.1 = (s.locals j).line.perm := hdir j hCnone
        have hpreN : (tx.preLines j.1).perm = .N := hallInvalid j hreqj.symm
        have hprobe : tx.probesNeeded j.1 = false := by
          rw [hmask]
          simp [TileLink.Atomic.noProbeMask]
        have hlinej : (s.locals j).line = tx.preLines j.1 := by
          have hsnap := txnSnapshotLine_eq_of_grantReady hfull0 htxnLine hcur hphase j
          rw [hsnap, hprobe]
          simp
        have hrefj : (refMap n s).locals j = tx.preLines j.1 := by
          simp [refMap, refMapLine, hcur, hphase]
        have hki : k ≠ i.1 := by
          intro h
          apply hji
          exact Fin.ext h
        calc
          grantPendingDir n { tx with phase := .grantPendingAck } s.shared.dir k = s.shared.dir k := by
            simp [grantPendingDir, updateDirAt, hk, hreq, hki]
          _ = (s.locals j).line.perm := hdirj
          _ = .N := by simpa [hlinej] using hpreN
          _ = (TileLink.setFn (refMap n s).locals i (TileLink.Atomic.tipLine (refMap n s).shared.mem) j).perm := by
            simp [TileLink.setFn, hji, hrefj, hpreN]
          _ = TileLink.Atomic.syncDir (refMap n s).shared.dir
                (TileLink.setFn (refMap n s).locals i (TileLink.Atomic.tipLine (refMap n s).shared.mem)) k := by
              simpa [TileLink.Atomic.syncDir, hk, j]
    · have hki : k ≠ i.1 := by
        intro hkiEq
        apply hk
        simpa [hkiEq] using i.is_lt
      simp [refMap, refMapShared, sendGrantState, sendGrantShared, grantPendingDir,
        TileLink.Atomic.syncDir, preTxnDir, updateDirAt, hcur, hreq, hphase, hk, hki]
  constructor
  · simp [refMapShared, sendGrantState, sendGrantShared, absPendingGrantMeta,
      TileLink.Atomic.deliveredGrantMeta, hcur, hphase]
  constructor
  · simp [refMapShared, sendGrantState, sendGrantShared, hcur, hreq]
  · simp [refMapShared, sendGrantState, sendGrantShared, hcur, hrel]

private theorem refMapShared_sendGrant_acquirePerm_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase = .grantReady) (hrel : s.shared.pendingReleaseAck = none)
    (hkind : tx.kind = .acquirePerm) :
    refMapShared n (sendGrantState s i tx) =
      { mem := (refMap n s).shared.mem
      , dir := TileLink.Atomic.syncDir (refMap n s).shared.dir
          (TileLink.Atomic.acquirePermLocals (refMap n s) i)
      , pendingGrantMeta := some (TileLink.Atomic.deliveredGrantMeta (absPendingGrantMeta tx))
      , pendingGrantAck := some i.1
      , pendingReleaseAck := none } := by
  have hfull0 := hfull
  rcases hfull with ⟨⟨_, hdir, _, _⟩, _, _⟩
  rw [TileLink.Atomic.HomeState.mk.injEq]
  constructor
  · simp [refMap, refMapShared, sendGrantState, sendGrantShared, hcur]
  constructor
  · funext k
    by_cases hk : k < n
    · let j : Fin n := ⟨k, hk⟩
      by_cases hji : j = i
      · subst hji
        have hreqk : tx.requester = k := by
          simpa [j] using hreq
        calc
          grantPendingDir n { tx with phase := .grantPendingAck } s.shared.dir k = tx.resultPerm := by
            simp [grantPendingDir, updateDirAt, hk, hreqk]
          _ = TLPerm.T := (txnPlanInv_acquirePerm hplan hcur hkind).1
          _ = TileLink.Atomic.syncDir (refMap n s).shared.dir
                (TileLink.Atomic.acquirePermLocals (refMap n s) j) k := by
              simp [TileLink.Atomic.syncDir, TileLink.Atomic.acquirePermLocals, refMap, hk, j]
      · have hreqj : tx.requester ≠ j.1 := by
          intro h
          apply hji
          exact Fin.ext (h.symm.trans hreq)
        have hCnone : (s.locals j).chanC = none :=
          chanC_none_of_phase_ne_probing hfull0 hcur (by simp [hphase]) j
        have hdirj : s.shared.dir j.1 = (s.locals j).line.perm := hdir j hCnone
        have hlocalPerm :
            (TileLink.Atomic.acquirePermLocals (refMap n s) i j).perm =
              (s.locals j).line.perm := by
          have hlocals :=
            refMap_sendGrant_acquirePerm_locals_eq hfull0 htxnLine hplan hcur hreq hphase hkind
          have hlineEq :
              refMapLine (sendGrantState s i tx) j = (s.locals j).line := by
            simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals, hji, hreqj]
          have hpermEq := congrArg CacheLine.perm (congrFun hlocals j)
          have hpermEq' :
              (s.locals j).line.perm =
                (TileLink.Atomic.acquirePermLocals (refMap n s) i j).perm := by
            simpa [refMap, hlineEq] using hpermEq
          simpa using hpermEq'.symm
        have hki : k ≠ i.1 := by
          intro h
          apply hji
          exact Fin.ext h
        calc
          grantPendingDir n { tx with phase := .grantPendingAck } s.shared.dir k = s.shared.dir k := by
            simp [grantPendingDir, updateDirAt, hk, hreq, hki]
          _ = (s.locals j).line.perm := hdirj
          _ = (TileLink.Atomic.acquirePermLocals (refMap n s) i j).perm := hlocalPerm.symm
          _ = TileLink.Atomic.syncDir (refMap n s).shared.dir
                (TileLink.Atomic.acquirePermLocals (refMap n s) i) k := by
              simpa [TileLink.Atomic.syncDir, hk, j]
    · have hki : k ≠ i.1 := by
        intro hkiEq
        apply hk
        simpa [hkiEq] using i.is_lt
      simp [refMap, refMapShared, sendGrantState, sendGrantShared, grantPendingDir,
        TileLink.Atomic.syncDir, preTxnDir, updateDirAt, hcur, hreq, hphase, hk, hki]
  constructor
  · simp [refMapShared, sendGrantState, sendGrantShared, absPendingGrantMeta,
      TileLink.Atomic.deliveredGrantMeta, hcur, hphase]
  constructor
  · simp [refMapShared, sendGrantState, sendGrantShared, hcur, hreq]
  · simp [refMapShared, sendGrantState, sendGrantShared, hcur, hrel]

theorem refMap_init (n : Nat) (s : SymState HomeState NodeState n)
    (hs : (tlMessages.toSpec n).init s) :
    (TileLink.Atomic.tlAtomic.toSpec n).init (refMap n s) := by
  rcases hs with ⟨⟨hmem, hdir, htxn, hgrant, hrel, _⟩, hlocals⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hmem, ?_, ?_, hgrant, ?_⟩
    · intro k
      unfold refMap refMapShared
      simp [htxn, hrel, TileLink.Atomic.syncDir]
      by_cases hk : k < n
      · let i : Fin n := ⟨k, hk⟩
        rcases hlocals i with ⟨hline, _, _, _, _, _, _, _, _⟩
        simpa [i, hk, hline] using hdir k
      · simpa [hk] using hdir k
    · simp [refMap, refMapShared, htxn]
    · have hnoQueued :
          ¬∃ x : Fin n, (s.locals x).releaseInFlight = true ∧ (s.locals x).chanC ≠ none := by
        intro h
        rcases h with ⟨x, hflight, hCsome⟩
        rcases hlocals x with ⟨_, _, _, hC, _, _, _, _, hflight0⟩
        rw [hflight0] at hflight
        contradiction
      simp [refMap, refMapShared, htxn, hrel, queuedReleaseIdx, hnoQueued]
  · intro i
    rcases hlocals i with ⟨hline, _, _, _, _, _, _, _, _⟩
    simpa [refMap, refMapLine, TileLink.Atomic.tlAtomic, htxn, hline]

theorem refMap_sendAcquireBlock_eq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hstep : SendAcquireBlock s s' i grow source) :
    refMap n s' = refMap n s := by
  have hline : ∀ j : Fin n, (s'.locals j).line = (s.locals j).line := by
    intro j; simpa using sendAcquireBlock_line (j := j) hstep
  have hC : ∀ j : Fin n, (s'.locals j).chanC = (s.locals j).chanC := by
    intro j; simpa using sendAcquireBlock_chanC (j := j) hstep
  have hflight : ∀ j : Fin n, (s'.locals j).releaseInFlight = (s.locals j).releaseInFlight := by
    intro j; simpa using sendAcquireBlock_releaseInFlight (j := j) hstep
  apply SymState.ext
  · have hshared : s'.shared = s.shared := by simpa using sendAcquireBlock_shared hstep
    cases htx : s.shared.currentTxn with
    | none =>
        change refMapShared n s' = refMapShared n s
        simp [refMapShared, hshared, htx]
        rw [syncDir_lines_eq s.shared.dir s.locals s'.locals hline]
        rw [queuedReleaseIdx_eq_of_chanC_releaseEq hC hflight]
        simp
    | some tx =>
        change refMapShared n s' = refMapShared n s
        simp [refMapShared, hshared, htx]
  · funext j
    have hshared : s'.shared = s.shared := by simpa using sendAcquireBlock_shared hstep
    have hcur : s'.shared.currentTxn = s.shared.currentTxn := by simpa [hshared]
    cases htx : s.shared.currentTxn with
    | none =>
        have htx' : s'.shared.currentTxn = none := by simpa [htx] using hcur
        simp [refMap, refMapLine, htx, htx', hline j]
    | some tx =>
        have htx' : s'.shared.currentTxn = some tx := by simpa [htx] using hcur
        by_cases hgp : tx.phase = .grantPendingAck
        · by_cases hreq : tx.requester = j.1
          · simp [refMap, refMapLine, htx, htx', hgp, hreq]
          · simp [refMap, refMapLine, htx, htx', hgp, hreq, hline j]
        · simp [refMap, refMapLine, htx, htx', hgp]

theorem refMap_sendAcquirePerm_eq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hstep : SendAcquirePerm s s' i grow source) :
    refMap n s' = refMap n s := by
  have hline : ∀ j : Fin n, (s'.locals j).line = (s.locals j).line := by
    intro j; simpa using sendAcquirePerm_line (j := j) hstep
  have hC : ∀ j : Fin n, (s'.locals j).chanC = (s.locals j).chanC := by
    intro j; simpa using sendAcquirePerm_chanC (j := j) hstep
  have hflight : ∀ j : Fin n, (s'.locals j).releaseInFlight = (s.locals j).releaseInFlight := by
    intro j; simpa using sendAcquirePerm_releaseInFlight (j := j) hstep
  apply SymState.ext
  · have hshared : s'.shared = s.shared := by simpa using sendAcquirePerm_shared hstep
    cases htx : s.shared.currentTxn with
    | none =>
        change refMapShared n s' = refMapShared n s
        simp [refMapShared, hshared, htx]
        rw [syncDir_lines_eq s.shared.dir s.locals s'.locals hline]
        rw [queuedReleaseIdx_eq_of_chanC_releaseEq hC hflight]
        simp
    | some tx =>
        change refMapShared n s' = refMapShared n s
        simp [refMapShared, hshared, htx]
  · funext j
    have hshared : s'.shared = s.shared := by simpa using sendAcquirePerm_shared hstep
    have hcur : s'.shared.currentTxn = s.shared.currentTxn := by simpa [hshared]
    cases htx : s.shared.currentTxn with
    | none =>
        have htx' : s'.shared.currentTxn = none := by simpa [htx] using hcur
        simp [refMap, refMapLine, htx, htx', hline j]
    | some tx =>
        have htx' : s'.shared.currentTxn = some tx := by simpa [htx] using hcur
        by_cases hgp : tx.phase = .grantPendingAck
        · by_cases hreq : tx.requester = j.1
          · simp [refMap, refMapLine, htx, htx', hgp, hreq]
          · simp [refMap, refMapLine, htx, htx', hgp, hreq, hline j]
        · simp [refMap, refMapLine, htx, htx', hgp]

private theorem atomic_writableProbeMask_refMap_eq {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n)
    (htxn : s.shared.currentTxn = none) :
    TileLink.Atomic.writableProbeMask (refMap n s) i = writableProbeMask s i := by
  funext k
  by_cases hk : k < n
  · let j : Fin n := ⟨k, hk⟩
    unfold TileLink.Atomic.writableProbeMask writableProbeMask
    simp [hk, refMap, refMapLine, htxn]
  · simp [TileLink.Atomic.writableProbeMask, writableProbeMask, hk]

private theorem atomic_cachedProbeMask_refMap_eq {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n)
    (htxn : s.shared.currentTxn = none) :
    TileLink.Atomic.cachedProbeMask (refMap n s) i = cachedProbeMask s i := by
  funext k
  by_cases hk : k < n
  · let j : Fin n := ⟨k, hk⟩
    unfold TileLink.Atomic.cachedProbeMask cachedProbeMask
    simp [hk, refMap, refMapLine, htxn]
  · simp [TileLink.Atomic.cachedProbeMask, cachedProbeMask, hk]

private theorem atomic_not_hasDirtyOther_of_noDirty {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (hnoDirty : noDirtyInv n s)
    (htxn : s.shared.currentTxn = none) :
    ¬ TileLink.Atomic.hasDirtyOther n i (refMap n s) := by
  intro h
  rcases h with ⟨j, hji, hdirty⟩
  have hdirty' : (s.locals j).line.dirty = true := by
    simpa [TileLink.Atomic.hasDirtyOther, refMap, refMapLine, htxn] using hdirty
  rw [hnoDirty j] at hdirty'
  contradiction

private theorem atomic_hasCachedOther_refMap_iff {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (htxn : s.shared.currentTxn = none) :
    TileLink.Atomic.hasCachedOther n i (refMap n s) ↔ hasCachedOther s i := by
  simp [TileLink.Atomic.hasCachedOther, hasCachedOther, refMap, refMapLine, htxn]

private theorem atomic_allOthersInvalid_refMap_iff {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (htxn : s.shared.currentTxn = none) :
    TileLink.Atomic.allOthersInvalid n i (refMap n s) ↔ allOthersInvalid s i := by
  simp [TileLink.Atomic.allOthersInvalid, allOthersInvalid, refMap, refMapLine, htxn]

private theorem atomic_not_hasDirtyOther_of_preNoDirty {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hpre : preLinesNoDirtyInv n s)
    (hcur : s.shared.currentTxn = some tx) (hphase : tx.phase ≠ .grantPendingAck) :
    ¬ TileLink.Atomic.hasDirtyOther n i (refMap n s) := by
  intro hdirty
  rcases hdirty with ⟨j, _, hdirtyj⟩
  have hpre' : ∀ k : Nat, k < n → (tx.preLines k).dirty = false := by
    simpa [preLinesNoDirtyInv, hcur] using hpre
  have hdirtyPre : (tx.preLines j.1).dirty = true := by
    simpa [TileLink.Atomic.hasDirtyOther, refMap, refMapLine, hcur, hphase] using hdirtyj
  have hnoDirtyPre : (tx.preLines j.1).dirty = false := by
    exact hpre' j.1 j.is_lt
  rw [hnoDirtyPre] at hdirtyPre
  contradiction

private theorem atomic_hasCachedOther_refMap_snapshot_iff {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase ≠ .grantPendingAck) :
    TileLink.Atomic.hasCachedOther n i (refMap n s) ↔ snapshotHasCachedOther n tx := by
  constructor
  · intro h
    rcases h with ⟨j, hji, hperm⟩
    refine ⟨j, ?_, ?_⟩
    · exact fun h => hji (Fin.ext (h.trans hreq))
    · simpa [refMap, refMapLine, hcur, hphase] using hperm
  · intro h
    rcases h with ⟨j, hji, hperm⟩
    refine ⟨j, ?_, ?_⟩
    · intro h
      apply hji
      exact (congrArg Fin.val h).trans hreq.symm
    · simpa [TileLink.Atomic.hasCachedOther, refMap, refMapLine, hcur, hphase]
        using hperm

private theorem atomic_allOthersInvalid_refMap_snapshot_iff {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase ≠ .grantPendingAck) :
    TileLink.Atomic.allOthersInvalid n i (refMap n s) ↔ snapshotAllOthersInvalid n tx := by
  constructor
  · intro h j hji
    have hji' : j ≠ i := by
      intro hEq
      apply hji
      exact (congrArg Fin.val hEq).trans hreq.symm
    have hN := h j hji'
    simpa [refMap, refMapLine, hcur, hphase] using hN
  · intro h j hji
    have hji' : j.1 ≠ tx.requester := by
      exact fun hEq => hji (Fin.ext (hEq.trans hreq))
    have hN := h j hji'
    simpa [TileLink.Atomic.allOthersInvalid, refMap, refMapLine, hcur, hphase] using hN

private theorem atomic_writableProbeMask_refMap_snapshot_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase ≠ .grantPendingAck) :
    TileLink.Atomic.writableProbeMask (refMap n s) i = snapshotWritableProbeMask n tx := by
  funext k
  by_cases hk : k < n
  · let j : Fin n := ⟨k, hk⟩
    by_cases hki : k = i.1
    · have hji : j = i := Fin.ext hki
      simp [TileLink.Atomic.writableProbeMask, snapshotWritableProbeMask, refMap, refMapLine,
        hcur, hphase, hreq, hk, hki, hji, j]
    · have hji : j ≠ i := by
        intro h
        apply hki
        simpa [j] using congrArg Fin.val h
      simp [TileLink.Atomic.writableProbeMask, snapshotWritableProbeMask, refMap, refMapLine,
        hcur, hphase, hreq, hk, hki, hji, j]
  · simp [TileLink.Atomic.writableProbeMask, snapshotWritableProbeMask, hk]

private theorem atomic_cachedProbeMask_refMap_snapshot_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase ≠ .grantPendingAck) :
    TileLink.Atomic.cachedProbeMask (refMap n s) i = snapshotCachedProbeMask n tx := by
  funext k
  by_cases hk : k < n
  · let j : Fin n := ⟨k, hk⟩
    by_cases hki : k = i.1
    · have hji : j = i := Fin.ext hki
      simp [TileLink.Atomic.cachedProbeMask, snapshotCachedProbeMask, refMap, refMapLine,
        hcur, hphase, hreq, hk, hki, hji, j]
    · have hji : j ≠ i := by
        intro h
        apply hki
        simpa [j] using congrArg Fin.val h
      simp [TileLink.Atomic.cachedProbeMask, snapshotCachedProbeMask, refMap, refMapLine,
        hcur, hphase, hreq, hk, hki, hji, j]
  · simp [TileLink.Atomic.cachedProbeMask, snapshotCachedProbeMask, hk]

private theorem refMap_sendGrant_block_branch_next {n : Nat}
    {s s' : SymState HomeState NodeState n} {i : Fin n}
    (hfull : fullInv n s) (hclean : cleanDataInv n s) (htxnLine : txnLineInv n s)
    (hpre : preLinesNoDirtyInv n s) (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hstep : SendGrantToRequester s s' i) :
    ∀ {tx : ManagerTxn}, s.shared.currentTxn = some tx → tx.kind = .acquireBlock →
      tx.resultPerm = .B →
      (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  intro tx hcur hkind hperm
  rcases hstep with ⟨_, hcur', hreq, hphase, hgrant, hrel, _, _, _, hs'⟩
  rw [hcur] at hcur'
  cases hcur'
  rw [hs']
  simp only [SymSharedSpec.toSpec, TileLink.Atomic.tlAtomic]
  refine ⟨i, .finishGrant, ?_⟩
  refine ⟨absPendingGrantMeta tx, ?_, ?_, ?_, ?_, ?_⟩
  · simp [refMap, refMapShared, hcur, hphase]
  · simp [refMap, refMapShared, hcur, hphase, hgrant]
  · simp [refMap, refMapShared, hcur, hphase, hrel]
  · simp [absPendingGrantMeta, hreq]
  · right
    left
    refine ⟨atomic_not_hasDirtyOther_of_preNoDirty hpre hcur (by simp [hphase]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hsnapshotCached :=
        (txnPlanInv_acquireBlock_branch hplan hcur hkind hperm).1
      exact (atomic_hasCachedOther_refMap_snapshot_iff hcur hreq (by simp [hphase])).2 hsnapshotCached
    · simp [absPendingGrantMeta, absGrantKind, hkind]
    · simp [absPendingGrantMeta, hperm]
    · exact (txnDataInv_currentTxn htxnData hcur).1
    · exact (txnDataInv_currentTxn htxnData hcur).2
    · have hmask := (txnPlanInv_acquireBlock_branch hplan hcur hkind hperm).2
      simp [absPendingGrantMeta, hmask, atomic_writableProbeMask_refMap_snapshot_eq hcur hreq
        (by simp [hphase])]
    · constructor
      · have hmask := (txnPlanInv_acquireBlock_branch hplan hcur hkind hperm).2
        simp [absPendingGrantMeta, hphase, hmask, atomic_writableProbeMask_refMap_snapshot_eq hcur
          hreq (by simp [hphase])]
      · apply SymState.ext
        · exact refMapShared_sendGrant_block_branch_eq hfull hclean htxnLine htxnData hplan
            hcur hreq hphase hrel hkind hperm
        · simpa [refMap] using
            refMap_sendGrant_block_branch_locals_eq hfull hclean htxnLine htxnData hplan hcur
              hreq hphase hkind hperm

private theorem refMap_sendGrant_block_tip_next {n : Nat}
    {s s' : SymState HomeState NodeState n} {i : Fin n}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hstep : SendGrantToRequester s s' i) :
    ∀ {tx : ManagerTxn}, s.shared.currentTxn = some tx → tx.kind = .acquireBlock →
      tx.resultPerm = .T →
      (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  intro tx hcur hkind hperm
  rcases hstep with ⟨_, hcur', hreq, hphase, hgrant, hrel, _, _, _, hs'⟩
  rw [hcur] at hcur'
  cases hcur'
  rw [hs']
  simp only [SymSharedSpec.toSpec, TileLink.Atomic.tlAtomic]
  refine ⟨i, .finishGrant, ?_⟩
  refine ⟨absPendingGrantMeta tx, ?_, ?_, ?_, ?_, ?_⟩
  · simp [refMap, refMapShared, hcur, hphase]
  · simp [refMap, refMapShared, hcur, hphase, hgrant]
  · simp [refMap, refMapShared, hcur, hphase, hrel]
  · simp [absPendingGrantMeta, hreq]
  · right
    right
    left
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hallInvalid := (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).1
      exact (atomic_allOthersInvalid_refMap_snapshot_iff hcur hreq (by simp [hphase])).2 hallInvalid
    · simp [absPendingGrantMeta, absGrantKind, hkind]
    · simp [absPendingGrantMeta, hperm]
    · exact (txnDataInv_currentTxn htxnData hcur).1
    · exact (txnDataInv_currentTxn htxnData hcur).2
    · have hmask := (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).2
      simp [absPendingGrantMeta, hmask, TileLink.Atomic.noProbeMask]
    · constructor
      · have hmask := (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).2
        simp [absPendingGrantMeta, hphase, hmask, TileLink.Atomic.noProbeMask]
      · apply SymState.ext
        · exact refMapShared_sendGrant_block_tip_eq hfull htxnLine htxnData hplan
            hcur hreq hphase hrel hkind hperm
        · simpa [refMap] using
            refMap_sendGrant_block_tip_locals_eq hfull htxnLine htxnData hplan hcur
              hreq hphase hkind hperm

private theorem refMap_sendGrant_acquirePerm_next {n : Nat}
    {s s' : SymState HomeState NodeState n} {i : Fin n}
    (hfull : fullInv n s) (hpre : preLinesNoDirtyInv n s)
    (htxnLine : txnLineInv n s) (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hstep : SendGrantToRequester s s' i) :
    ∀ {tx : ManagerTxn}, s.shared.currentTxn = some tx → tx.kind = .acquirePerm →
      (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  intro tx hcur hkind
  rcases hstep with ⟨_, hcur', hreq, hphase, hgrant, hrel, _, _, _, hs'⟩
  rw [hcur] at hcur'
  cases hcur'
  rw [hs']
  simp only [SymSharedSpec.toSpec, TileLink.Atomic.tlAtomic]
  refine ⟨i, .finishGrant, ?_⟩
  refine ⟨absPendingGrantMeta tx, ?_, ?_, ?_, ?_, ?_⟩
  · simp [refMap, refMapShared, hcur, hphase]
  · simp [refMap, refMapShared, hcur, hphase, hgrant]
  · simp [refMap, refMapShared, hcur, hphase, hrel]
  · simp [absPendingGrantMeta, hreq]
  · right
    right
    right
    right
    refine ⟨atomic_not_hasDirtyOther_of_preNoDirty hpre hcur (by simp [hphase]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [absPendingGrantMeta, absGrantKind, hkind]
    · simp [absPendingGrantMeta, (txnPlanInv_acquirePerm hplan hcur hkind).1]
    · exact (txnDataInv_currentTxn htxnData hcur).1
    · exact (txnDataInv_currentTxn htxnData hcur).2
    · have hmask := (txnPlanInv_acquirePerm hplan hcur hkind).2.1
      simp [absPendingGrantMeta, hmask, atomic_cachedProbeMask_refMap_snapshot_eq hcur hreq
        (by simp [hphase])]
    · have hmask := (txnPlanInv_acquirePerm hplan hcur hkind).2.1
      simp [absPendingGrantMeta, hphase, hmask, atomic_cachedProbeMask_refMap_snapshot_eq hcur
        hreq (by simp [hphase])]
    · apply SymState.ext
      · exact refMapShared_sendGrant_acquirePerm_eq hfull htxnLine htxnData hplan
          hcur hreq hphase hrel hkind
      · simpa [refMap] using
          refMap_sendGrant_acquirePerm_locals_eq hfull htxnLine hplan hcur hreq hphase hkind

private theorem cachedProbeMask_eq_noProbeMask_of_allOthersInvalid {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (hallInvalid : allOthersInvalid s i) :
    cachedProbeMask s i = noProbeMask := by
  funext k
  by_cases hk : k < n
  · by_cases hki : (⟨k, hk⟩ : Fin n) = i
    · simp [cachedProbeMask, noProbeMask, hk, hki]
    · have hpermN : (s.locals ⟨k, hk⟩).line.perm = .N := hallInvalid ⟨k, hk⟩ hki
      simp [cachedProbeMask, noProbeMask, hk, hki, hpermN]
  · simp [cachedProbeMask, noProbeMask, hk]

private theorem refMap_recvAcquireState_locals_eq {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (kind : ReqKind) (grow : GrowParam) (source : SourceId)
    (htxn : s.shared.currentTxn = none) :
    (refMap n (recvAcquireState s i kind grow source)).locals = (refMap n s).locals := by
  funext j
  simp [refMap, refMapLine, recvAcquireState, recvAcquireShared, plannedTxn, htxn]

private theorem absPendingGrantMeta_tx_update_eq
    (tx : ManagerTxn) (phase : TxnPhase) (probesRemaining : Nat → Bool)
    (htx : tx.phase ≠ .grantPendingAck)
    (hphase : phase ≠ .grantPendingAck) :
    absPendingGrantMeta { tx with phase := phase, probesRemaining := probesRemaining } =
      absPendingGrantMeta tx := by
  simp [absPendingGrantMeta, htx, hphase]

private theorem refMapShared_recvAcquireState_eq_absPending {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (kind : ReqKind) (grow : GrowParam) (source : SourceId)
    (hnoDirty : noDirtyInv n s)
    (htxn : s.shared.currentTxn = none)
    (hrel : s.shared.pendingReleaseAck = none)
    (hallC : ∀ j : Fin n, (s.locals j).chanC = none) :
    refMapShared n (recvAcquireState s i kind grow source) =
      { mem := (refMap n s).shared.mem
      , dir := (refMap n s).shared.dir
      , pendingGrantMeta := some (absPendingGrantMeta (plannedTxn s i kind grow source))
      , pendingGrantAck := none
      , pendingReleaseAck := none } := by
  rcases plannedTxn_clean s i hnoDirty with ⟨hdirtySrc, htransfer⟩
  rw [TileLink.Atomic.HomeState.mk.injEq]
  constructor
  · simp [refMap, refMapShared, recvAcquireState, recvAcquireShared, htxn, hrel,
      queuedReleaseIdx_eq_none_of_all_chanC_none s hallC]
  constructor
  · simpa [refMap, refMapShared, htxn, hrel,
      queuedReleaseIdx_eq_none_of_all_chanC_none s hallC]
      using preTxnDir_plannedTxn_eq_syncDir s i kind grow source
  · simp [refMapShared, recvAcquireState, recvAcquireShared, absPendingGrantMeta,
      plannedTxn, hdirtySrc, htransfer, htxn, hrel]

private theorem absPendingGrantMeta_planned_acquireBlock_branch_eq {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId)
    (hnoDirty : noDirtyInv n s)
    (htxn : s.shared.currentTxn = none)
    (hresult : grow.result = .B) :
    absPendingGrantMeta (plannedTxn s i .acquireBlock grow source) =
      { requester := i.1
      , kind := .block
      , requesterPerm := .B
      , usedDirtySource := false
      , transferVal := s.shared.mem
      , probesNeeded := TileLink.Atomic.writableProbeMask (refMap n s) i
      , probesRemaining := TileLink.Atomic.writableProbeMask (refMap n s) i } := by
  rcases plannedTxn_clean s i hnoDirty with ⟨hdirtySrc, htransfer⟩
  simp [absPendingGrantMeta, plannedTxn, hdirtySrc, htransfer, hresult, probeMaskForResult]
  rw [atomic_writableProbeMask_refMap_eq s i htxn]
  simp [absGrantKind]

private theorem absPendingGrantMeta_planned_acquireBlock_tip_eq {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId)
    (hnoDirty : noDirtyInv n s)
    (hallInvalid : allOthersInvalid s i)
    (hresult : grow.result = .T) :
    absPendingGrantMeta (plannedTxn s i .acquireBlock grow source) =
      { requester := i.1
      , kind := .block
      , requesterPerm := .T
      , usedDirtySource := false
      , transferVal := s.shared.mem
      , probesNeeded := TileLink.Atomic.noProbeMask
      , probesRemaining := TileLink.Atomic.noProbeMask } := by
  rcases plannedTxn_clean s i hnoDirty with ⟨hdirtySrc, htransfer⟩
  simp [absPendingGrantMeta, plannedTxn, hdirtySrc, htransfer, hresult, probeMaskForResult,
    cachedProbeMask_eq_noProbeMask_of_allOthersInvalid hallInvalid]
  have hmask : noProbeMask = TileLink.Atomic.noProbeMask := rfl
  rw [hmask]
  simp [absGrantKind, TileLink.Atomic.noProbeMask, noProbeMask]

private theorem absPendingGrantMeta_planned_acquirePerm_eq {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId)
    (hnoDirty : noDirtyInv n s)
    (htxn : s.shared.currentTxn = none)
    (hresult : grow.result = .T) :
    absPendingGrantMeta (plannedTxn s i .acquirePerm grow source) =
      { requester := i.1
      , kind := .perm
      , requesterPerm := .T
      , usedDirtySource := false
      , transferVal := s.shared.mem
      , probesNeeded := TileLink.Atomic.cachedProbeMask (refMap n s) i
      , probesRemaining := TileLink.Atomic.cachedProbeMask (refMap n s) i } := by
  rcases plannedTxn_clean s i hnoDirty with ⟨hdirtySrc, htransfer⟩
  simp [absPendingGrantMeta, plannedTxn, hdirtySrc, htransfer, hresult, probeMaskForResult]
  rw [atomic_cachedProbeMask_refMap_eq s i htxn]
  simp [absGrantKind]

private theorem acquirePerm_requester_not_T {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam)
    (hlegal : grow.legalFrom (s.locals i).line.perm)
    (htxn : s.shared.currentTxn = none)
    (hresult : grow.result = .T) :
    ((refMap n s).locals i).perm ≠ .T := by
  have hperm : (s.locals i).line.perm ≠ .T := by
    cases grow
    · simp [GrowParam.result] at hresult
    · simp [GrowParam.legalFrom, GrowParam.source] at hlegal
      simpa [hlegal]
    · simp [GrowParam.legalFrom, GrowParam.source] at hlegal
      simpa [hlegal]
  simpa [refMap, refMapLine, htxn] using hperm

private theorem refMap_recvAcquireBlock_branch_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hinv : refinementInv n s)
    (hstep : RecvAcquireBlockAtManager s s' i grow source)
    (hbranch : hasCachedOther s i ∧ grow.result = .B) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hinv with ⟨_, hnoDirty, _⟩
  rcases hstep with ⟨htxn, hgrant, hrel, hallC, _hA, hpermN, _hlegal, _hnoDirtyOther, _hshape, _hBs, hs'⟩
  rcases hbranch with ⟨hcached, hresult⟩
  rw [hs']
  simp only [SymSharedSpec.toSpec, TileLink.Atomic.tlAtomic]
  refine ⟨i, .acquireBlock, ?_⟩
  constructor
  · simp [refMap, refMapShared, htxn, hrel, queuedReleaseIdx_eq_none_of_all_chanC_none s hallC]
  constructor
  · simp [refMap, refMapShared, htxn, hrel, queuedReleaseIdx_eq_none_of_all_chanC_none s hallC, hgrant]
  constructor
  · simp [refMap, refMapShared, htxn, hrel, queuedReleaseIdx_eq_none_of_all_chanC_none s hallC]
  constructor
  · simpa [refMap, refMapLine, htxn] using hpermN
  · right
    left
    refine ⟨atomic_not_hasDirtyOther_of_noDirty hnoDirty htxn, (atomic_hasCachedOther_refMap_iff htxn).2 hcached, ?_⟩
    apply SymState.ext
    · calc
        refMapShared n (recvAcquireState s i .acquireBlock grow source)
            = { (refMap n s).shared with
                  pendingGrantMeta := some (absPendingGrantMeta (plannedTxn s i .acquireBlock grow source))
                , pendingGrantAck := none
                , pendingReleaseAck := none } := by
                  simpa [refMap] using
                    refMapShared_recvAcquireState_eq_absPending s i .acquireBlock grow source
                      hnoDirty htxn hrel hallC
        _ = { (refMap n s).shared with
                pendingGrantMeta := some {
                  requester := i.1
                  kind := .block
                  requesterPerm := .B
                  usedDirtySource := false
                  transferVal := s.shared.mem
                  probesNeeded := TileLink.Atomic.writableProbeMask (refMap n s) i
                  probesRemaining := TileLink.Atomic.writableProbeMask (refMap n s) i }
              , pendingGrantAck := none
              , pendingReleaseAck := none } := by
                rw [absPendingGrantMeta_planned_acquireBlock_branch_eq s i grow source hnoDirty htxn hresult]
    · simpa [refMap] using refMap_recvAcquireState_locals_eq s i .acquireBlock grow source htxn

private theorem refMap_recvAcquireBlock_tip_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hinv : refinementInv n s)
    (hstep : RecvAcquireBlockAtManager s s' i grow source)
    (htip : allOthersInvalid s i ∧ grow.result = .T) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hinv with ⟨_, hnoDirty, _⟩
  rcases hstep with ⟨htxn, hgrant, hrel, hallC, _hA, hpermN, _hlegal, _hnoDirtyOther, _hshape, _hBs, hs'⟩
  rcases htip with ⟨hallInvalid, hresult⟩
  rw [hs']
  simp only [SymSharedSpec.toSpec, TileLink.Atomic.tlAtomic]
  refine ⟨i, .acquireBlock, ?_⟩
  constructor
  · simp [refMap, refMapShared, htxn, hrel, queuedReleaseIdx_eq_none_of_all_chanC_none s hallC]
  constructor
  · simp [refMap, refMapShared, htxn, hrel, queuedReleaseIdx_eq_none_of_all_chanC_none s hallC, hgrant]
  constructor
  · simp [refMap, refMapShared, htxn, hrel, queuedReleaseIdx_eq_none_of_all_chanC_none s hallC]
  constructor
  · simpa [refMap, refMapLine, htxn] using hpermN
  · right
    right
    refine ⟨(atomic_allOthersInvalid_refMap_iff htxn).2 hallInvalid, ?_⟩
    apply SymState.ext
    · calc
        refMapShared n (recvAcquireState s i .acquireBlock grow source)
            = { (refMap n s).shared with
                  pendingGrantMeta := some (absPendingGrantMeta (plannedTxn s i .acquireBlock grow source))
                , pendingGrantAck := none
                , pendingReleaseAck := none } := by
                  simpa [refMap] using
                    refMapShared_recvAcquireState_eq_absPending s i .acquireBlock grow source
                      hnoDirty htxn hrel hallC
        _ = { (refMap n s).shared with
                pendingGrantMeta := some {
                  requester := i.1
                  kind := .block
                  requesterPerm := .T
                  usedDirtySource := false
                  transferVal := s.shared.mem
                  probesNeeded := TileLink.Atomic.noProbeMask
                  probesRemaining := TileLink.Atomic.noProbeMask }
              , pendingGrantAck := none
              , pendingReleaseAck := none } := by
                rw [absPendingGrantMeta_planned_acquireBlock_tip_eq s i grow source hnoDirty hallInvalid hresult]
    · simpa [refMap] using refMap_recvAcquireState_locals_eq s i .acquireBlock grow source htxn

private theorem refMap_recvAcquirePerm_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hinv : refinementInv n s)
    (hstep : RecvAcquirePermAtManager s s' i grow source) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hinv with ⟨_, hnoDirty, _⟩
  rcases hstep with ⟨htxn, hgrant, hrel, hallC, _hA, hlegal, hresult, _hnoDirtyOther, _hBs, hs'⟩
  rw [hs']
  simp only [SymSharedSpec.toSpec, TileLink.Atomic.tlAtomic]
  refine ⟨i, .acquirePerm, ?_⟩
  constructor
  · simp [refMap, refMapShared, htxn, hrel, queuedReleaseIdx_eq_none_of_all_chanC_none s hallC]
  constructor
  · simp [refMap, refMapShared, htxn, hrel, queuedReleaseIdx_eq_none_of_all_chanC_none s hallC, hgrant]
  constructor
  · simp [refMap, refMapShared, htxn, hrel, queuedReleaseIdx_eq_none_of_all_chanC_none s hallC]
  constructor
  · exact acquirePerm_requester_not_T s i grow hlegal htxn hresult
  · right
    refine ⟨atomic_not_hasDirtyOther_of_noDirty hnoDirty htxn, ?_⟩
    apply SymState.ext
    · calc
        refMapShared n (recvAcquireState s i .acquirePerm grow source)
            = { (refMap n s).shared with
                  pendingGrantMeta := some (absPendingGrantMeta (plannedTxn s i .acquirePerm grow source))
                , pendingGrantAck := none
                , pendingReleaseAck := none } := by
                  simpa [refMap] using
                    refMapShared_recvAcquireState_eq_absPending s i .acquirePerm grow source
                      hnoDirty htxn hrel hallC
        _ = { (refMap n s).shared with
                pendingGrantMeta := some {
                  requester := i.1
                  kind := .perm
                  requesterPerm := .T
                  usedDirtySource := false
                  transferVal := s.shared.mem
                  probesNeeded := TileLink.Atomic.cachedProbeMask (refMap n s) i
                  probesRemaining := TileLink.Atomic.cachedProbeMask (refMap n s) i }
              , pendingGrantAck := none
              , pendingReleaseAck := none } := by
                rw [absPendingGrantMeta_planned_acquirePerm_eq s i grow source hnoDirty htxn hresult]
    · simpa [refMap] using refMap_recvAcquireState_locals_eq s i .acquirePerm grow source htxn

theorem refMap_recvAcquireAtManager_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hinv : refinementInv n s)
    (hstep : RecvAcquireAtManager s s' i) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hstep with ⟨grow, source, hblk⟩ | ⟨grow, source, hperm⟩
  · have hshape : (hasCachedOther s i ∧ grow.result = .B) ∨
        (allOthersInvalid s i ∧ grow.result = .T) := by
        rcases hblk with ⟨_, _, _, _, _, _, _, _, hshape, _, _⟩
        exact hshape
    rcases hshape with hbranch | htip
    · exact refMap_recvAcquireBlock_branch_next hinv hblk hbranch
    · exact refMap_recvAcquireBlock_tip_next hinv hblk htip
  · exact refMap_recvAcquirePerm_next hinv hperm

theorem refMap_recvProbeAtMaster_eq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hstep : RecvProbeAtMaster s s' i) :
    refMap n s' = refMap n s := by
  rcases hstep with ⟨tx, msg, hcur, hphase, _, _, _, _, _, _, _, hs'⟩
  rw [hs']
  apply SymState.ext
  · simp [refMap, refMapShared, recvProbeState, hcur, hphase]
  · funext j
    have hcur' : (recvProbeState s i msg).shared.currentTxn = some tx := by
      simp [recvProbeState, hcur]
    simp [refMap, refMapLine, recvProbeState, hcur, hcur', hphase]

theorem refMap_recvProbeAckAtManager_eq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hstep : RecvProbeAckAtManager s s' i) :
    refMap n s' = refMap n s := by
  rcases hstep with ⟨tx, msg, hcur, hphase, _, _, _, _, _, hs'⟩
  rw [hs']
  have hphase' : probeAckPhase (n := n) (clearProbeIdx tx.probesRemaining i.1) ≠ .grantPendingAck := by
    intro hbad
    unfold probeAckPhase at hbad
    split at hbad <;> cases hbad
  apply SymState.ext
  · change refMapShared n (recvProbeAckState s i tx) = refMapShared n s
    simp [refMapShared, recvProbeAckState, recvProbeAckShared, hcur, hphase, hphase']
    constructor
    · rw [preTxnDir_tx_update_eq tx
        (updateDirAt s.shared.dir i (s.locals i).line.perm)
        (probeAckPhase (n := n) (clearProbeIdx tx.probesRemaining i.1))
        (clearProbeIdx tx.probesRemaining i.1)]
      rw [preTxnDir_updateDirAt_eq (n := n) tx s.shared.dir i (s.locals i).line.perm]
    · exact absPendingGrantMeta_tx_update_eq tx
        (probeAckPhase (n := n) (clearProbeIdx tx.probesRemaining i.1))
        (clearProbeIdx tx.probesRemaining i.1) (by simpa [hphase]) hphase'
  · funext j
    simp [refMap, refMapLine, recvProbeAckState, recvProbeAckShared, hcur, hphase, hphase']

theorem refMap_recvGrantAtMaster_eq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hstep : RecvGrantAtMaster s s' i) :
    refMap n s' = refMap n s := by
  rcases hstep with ⟨tx, msg, hcur, hreq, hphase, hgrant, _, _, _, _, hrest⟩
  rcases hrest with ⟨_, hs'⟩
  rw [hs']
  apply SymState.ext
  · change refMapShared n (recvGrantState s i tx) = refMapShared n s
    simp [refMapShared, recvGrantState, recvGrantShared, hcur, hphase, hgrant]
    rw [grantPendingDir_updateDirAt_eq tx s.shared.dir i tx.resultPerm hreq]
  · funext j
    by_cases hji : j = i
    · subst j
      simp [refMap, refMapLine, recvGrantState, recvGrantShared, hcur, hphase, hreq]
    · have hreqj : tx.requester ≠ j.1 := by
        intro hreq'
        apply hji
        exact Fin.ext ((hreq.symm.trans hreq').symm)
      simpa [refMap, refMapLine, recvGrantState, recvGrantShared, recvGrantLocals,
        recvGrantLocal, setFn, hcur, hphase, hreqj, hji]

theorem refinement_inv_invariant (n : Nat) :
    pred_implies (tlMessages.toSpec n).safety [tlafml| □ ⌜ refinementInv n ⌝] := by
  apply init_invariant
  · intro s hinit
    exact init_refinementInv n s hinit
  · intro s s' hnext hinv
    exact refinementInv_preserved n s s' hinv hnext

end TileLink.Messages
