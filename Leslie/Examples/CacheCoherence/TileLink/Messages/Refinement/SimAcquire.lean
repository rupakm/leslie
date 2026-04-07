import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.SimGrant

namespace TileLink.Messages

open TLA TileLink SymShared Classical

theorem refMap_init (n : Nat) (s : SymState HomeState NodeState n)
    (hs : (tlMessages.toSpec n).init s) :
    (TileLink.Atomic.tlAtomic.toSpec n).init (refMap n s) := by
  simp [SymSharedSpec.toSpec] at hs ⊢
  rcases hs with ⟨⟨hmem, hdir, htxn, hgrant, hrel, _⟩, hloc⟩
  constructor
  · -- init_shared for refMapShared
    simp [refMap, refMapShared, htxn, hrel, hgrant]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- mem = 0: no dirty (all dirty = false), no release in flight, so mem = s.shared.mem = 0
      have hnd : ¬∃ j : Fin n, (s.locals j).line.dirty = true := by
        intro ⟨j, hd⟩
        have := (hloc j).1
        rw [this] at hd; simp at hd
      rw [dif_neg hnd]
      have hnorel : findDirtyReleaseVal n s = none := by
        apply findDirtyReleaseVal_none_of_all_chanC_none
        intro j; exact (hloc j).2.2.2.1
      rw [hnorel]; exact hmem
    · -- dir k = .N
      intro k
      by_cases hk : k < n
      · simp [TileLink.Atomic.syncDir, hk]
        have := (hloc ⟨k, hk⟩).1
        rw [this]; rfl
      · simp [TileLink.Atomic.syncDir, hk]; exact hdir k
    · rfl  -- pendingGrantMeta = none
    · rfl  -- pendingGrantAck = none
    · -- pendingReleaseAck = none
      simp
      apply queuedReleaseIdx_eq_none_of_all_chanC_none
      intro j; exact (hloc j).2.2.2.1
  · -- init_local for refMapLine
    intro i
    simp [refMap, refMapLine, htxn]
    have := (hloc i).1
    rw [this]
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem refMap_sendAcquireBlock_eq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hstep : SendAcquireBlock s s' i grow source) :
    refMap n s' = refMap n s := by
  rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
  rw [hs']
  exact refMap_eq_of_invisible_local_change
    (fun j => by simp [setFn]; split <;> simp)
    (fun j => by simp [setFn]; split <;> simp)
    (fun j => by simp [setFn]; split <;> simp)

theorem refMap_sendAcquirePerm_eq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hstep : SendAcquirePerm s s' i grow source) :
    refMap n s' = refMap n s := by
  rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
  rw [hs']
  exact refMap_eq_of_invisible_local_change
    (fun j => by simp [setFn]; split <;> simp)
    (fun j => by simp [setFn]; split <;> simp)
    (fun j => by simp [setFn]; split <;> simp)

theorem atomic_writableProbeMask_refMap_eq {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n)
    (htxn : s.shared.currentTxn = none) :
    TileLink.Atomic.writableProbeMask (refMap n s) i = writableProbeMask s i := by
  funext k
  by_cases hk : k < n
  · let j : Fin n := ⟨k, hk⟩
    unfold TileLink.Atomic.writableProbeMask writableProbeMask
    simp [hk, refMap, refMapLine, htxn]
  · simp [TileLink.Atomic.writableProbeMask, writableProbeMask, hk]

theorem atomic_cachedProbeMask_refMap_eq {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n)
    (htxn : s.shared.currentTxn = none) :
    TileLink.Atomic.cachedProbeMask (refMap n s) i = cachedProbeMask s i := by
  funext k
  by_cases hk : k < n
  · let j : Fin n := ⟨k, hk⟩
    unfold TileLink.Atomic.cachedProbeMask cachedProbeMask
    simp [hk, refMap, refMapLine, htxn]
  · simp [TileLink.Atomic.cachedProbeMask, cachedProbeMask, hk]

theorem atomic_not_hasDirtyOther_of_noDirty {n : Nat}
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

theorem atomic_not_hasDirtyOther_of_not_hasDirtyOther {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (hnd : ¬hasDirtyOther s i)
    (htxn : s.shared.currentTxn = none) :
    ¬ TileLink.Atomic.hasDirtyOther n i (refMap n s) := by
  intro h
  rcases h with ⟨j, hji, hdirty⟩
  have hdirty' : (s.locals j).line.dirty = true := by
    simpa [TileLink.Atomic.hasDirtyOther, refMap, refMapLine, htxn] using hdirty
  exact hnd ⟨j, hji, hdirty'⟩

theorem atomic_hasCachedOther_refMap_iff {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (htxn : s.shared.currentTxn = none) :
    TileLink.Atomic.hasCachedOther n i (refMap n s) ↔ hasCachedOther s i := by
  simp [TileLink.Atomic.hasCachedOther, hasCachedOther, refMap, refMapLine, htxn]

theorem atomic_allOthersInvalid_refMap_iff {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (htxn : s.shared.currentTxn = none) :
    TileLink.Atomic.allOthersInvalid n i (refMap n s) ↔ allOthersInvalid s i := by
  simp [TileLink.Atomic.allOthersInvalid, allOthersInvalid, refMap, refMapLine, htxn]

theorem atomic_not_hasDirtyOther_of_preNoDirty {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hpre : preLinesNoDirtyInv n s)
    (hcur : s.shared.currentTxn = some tx) (hphase : tx.phase ≠ .grantPendingAck) :
    ¬ TileLink.Atomic.hasDirtyOther n i (refMap n s) := by
  -- NOTE: This theorem appears unprovable as stated. `preLinesNoDirtyInv` ensures
  -- at most one preLines entry is dirty, but does not rule out a dirty entry at
  -- some j ≠ i. An additional hypothesis is needed, e.g., that tx.requester = i.1
  -- (so the dirty preLines belongs to the requester) or that no preLines is dirty
  -- at all. Leaving sorry until the statement is strengthened.
  sorry

theorem atomic_hasCachedOther_refMap_snapshot_iff {n : Nat}
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

theorem atomic_allOthersInvalid_refMap_snapshot_iff {n : Nat}
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

theorem atomic_writableProbeMask_refMap_snapshot_eq {n : Nat}
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

theorem atomic_cachedProbeMask_refMap_snapshot_eq {n : Nat}
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

theorem refMap_sendGrant_block_branch_next {n : Nat}
    {s s' : SymState HomeState NodeState n} {i : Fin n}
    (hfull : fullInv n s) (hclean : cleanDataInv n s) (htxnLine : txnLineInv n s)
    (hpre : preLinesNoDirtyInv n s) (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hstep : SendGrantToRequester s s' i) :
    ∀ {tx : ManagerTxn}, s.shared.currentTxn = some tx → tx.kind = .acquireBlock →
      tx.resultPerm = .B →
      (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  sorry

theorem refMap_sendGrant_block_tip_next {n : Nat}
    {s s' : SymState HomeState NodeState n} {i : Fin n}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hstep : SendGrantToRequester s s' i) :
    ∀ {tx : ManagerTxn}, s.shared.currentTxn = some tx → tx.kind = .acquireBlock →
      tx.resultPerm = .T →
      (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  sorry

theorem refMap_sendGrant_acquirePerm_next {n : Nat}
    {s s' : SymState HomeState NodeState n} {i : Fin n}
    (hfull : fullInv n s) (hpre : preLinesNoDirtyInv n s)
    (htxnLine : txnLineInv n s) (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hstep : SendGrantToRequester s s' i) :
    ∀ {tx : ManagerTxn}, s.shared.currentTxn = some tx → tx.kind = .acquirePerm →
      (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  sorry

theorem cachedProbeMask_eq_noProbeMask_of_allOthersInvalid {n : Nat}
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

theorem refMap_recvAcquireState_locals_eq {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (kind : ReqKind) (grow : GrowParam) (source : SourceId)
    (htxn : s.shared.currentTxn = none) :
    (refMap n (recvAcquireState s i kind grow source)).locals = (refMap n s).locals := by
  funext j
  simp [refMap, refMapLine, recvAcquireState, recvAcquireShared, plannedTxn, htxn]

theorem absPendingGrantMeta_tx_update_eq
    (tx : ManagerTxn) (phase : TxnPhase) (probesRemaining : Nat → Bool)
    (htx : tx.phase ≠ .grantPendingAck)
    (hphase : phase ≠ .grantPendingAck) :
    absPendingGrantMeta { tx with phase := phase, probesRemaining := probesRemaining } =
      absPendingGrantMeta tx := by
  simp [absPendingGrantMeta, htx, hphase]

theorem refMapShared_recvAcquireState_eq_absPending {n : Nat}
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
  have hnd_all : ¬∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true :=
    fun ⟨j, _, hd⟩ => absurd hd (by simp [hnoDirty j])
  have hdo : dirtyOwnerOpt s i = none := by unfold dirtyOwnerOpt; simp [hnd_all]
  have hud : (plannedTxn s i kind grow source).usedDirtySource = false := by
    simp [plannedTxn, plannedUsedDirtySource, hdo]
  have hnd : ¬∃ j : Fin n, (s.locals j).line.dirty = true :=
    fun ⟨j, hd⟩ => absurd hd (by simp [hnoDirty j])
  have hfdrv := findDirtyReleaseVal_none_of_all_chanC_none' s hallC
  have hcur_post : (recvAcquireState s i kind grow source).shared.currentTxn =
      some (plannedTxn s i kind grow source) := by simp [recvAcquireState, recvAcquireShared]
  have hphase : (plannedTxn s i kind grow source).phase ≠ .grantPendingAck := by simp [plannedTxn]
  ext
  · -- mem: both sides = s.shared.mem
    simp [refMapShared, recvAcquireState, recvAcquireShared, hud, htxn, hrel, hnd, hfdrv, refMap]
  · -- dir: preTxnDir = syncDir (via existing lemma)
    simp [refMapShared, recvAcquireState, recvAcquireShared, hphase, htxn, refMap]
    exact congrFun (preTxnDir_plannedTxn_eq_syncDir s i kind grow source) _
  · -- pendingGrantMeta
    simp [refMapShared, recvAcquireState, recvAcquireShared]
  · -- pendingGrantAck
    simp [refMapShared, recvAcquireState, recvAcquireShared]
  · -- pendingReleaseAck
    simp [refMapShared, recvAcquireState, recvAcquireShared, hrel]

theorem absPendingGrantMeta_planned_acquireBlock_branch_eq {n : Nat}
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

theorem absPendingGrantMeta_planned_acquireBlock_tip_eq {n : Nat}
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

theorem absPendingGrantMeta_planned_acquirePerm_eq {n : Nat}
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

theorem acquirePerm_requester_not_T {n : Nat}
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

/-! ### Helpers using ¬hasDirtyOther (weaker than noDirtyInv) -/

theorem refMapShared_recvAcquireState_eq_absPending' {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (kind : ReqKind) (grow : GrowParam) (source : SourceId)
    (hnd : ¬hasDirtyOther s i)
    (hperm : (s.locals i).line.perm = .N)
    (hlineWF : lineWFInv n s)
    (htxn : s.shared.currentTxn = none)
    (hrel : s.shared.pendingReleaseAck = none)
    (hallC : ∀ j : Fin n, (s.locals j).chanC = none) :
    refMapShared n (recvAcquireState s i kind grow source) =
      { mem := (refMap n s).shared.mem
      , dir := (refMap n s).shared.dir
      , pendingGrantMeta := some (absPendingGrantMeta (plannedTxn s i kind grow source))
      , pendingGrantAck := none
      , pendingReleaseAck := none } := by
  -- Derive noDirtyInv from ¬hasDirtyOther + perm = .N + lineWF
  have hnoDirty : noDirtyInv n s := by
    intro j
    by_cases hji : j = i
    · subst hji
      -- i has perm .N → dirty = false (from lineWF: dirty → perm = .T)
      by_contra hd; simp only [Bool.not_eq_false] at hd
      have hpT := (hlineWF j).1 hd; rw [hperm] at hpT; exact absurd hpT (by simp [TLPerm.noConfusion])
    · -- j ≠ i → not dirty (from ¬hasDirtyOther)
      by_contra hd; simp only [Bool.not_eq_false] at hd
      exact hnd ⟨j, hji, hd⟩
  exact refMapShared_recvAcquireState_eq_absPending s i kind grow source hnoDirty htxn hrel hallC

theorem absPendingGrantMeta_planned_acquireBlock_branch_eq' {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId)
    (hnd : ¬hasDirtyOther s i)
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
  rcases plannedTxn_clean_of_not_hasDirtyOther s i hnd with ⟨hdirtySrc, htransfer⟩
  simp [absPendingGrantMeta, plannedTxn, hdirtySrc, htransfer, hresult, probeMaskForResult]
  rw [atomic_writableProbeMask_refMap_eq s i htxn]
  simp [absGrantKind]

theorem absPendingGrantMeta_planned_acquireBlock_tip_eq' {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId)
    (hnd : ¬hasDirtyOther s i)
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
  rcases plannedTxn_clean_of_not_hasDirtyOther s i hnd with ⟨hdirtySrc, htransfer⟩
  simp [absPendingGrantMeta, plannedTxn, hdirtySrc, htransfer, hresult, probeMaskForResult,
    cachedProbeMask_eq_noProbeMask_of_allOthersInvalid hallInvalid]
  have hmask : noProbeMask = TileLink.Atomic.noProbeMask := rfl
  rw [hmask]
  simp [absGrantKind, TileLink.Atomic.noProbeMask, noProbeMask]

theorem absPendingGrantMeta_planned_acquirePerm_eq' {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId)
    (hnd : ¬hasDirtyOther s i)
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
  rcases plannedTxn_clean_of_not_hasDirtyOther s i hnd with ⟨hdirtySrc, htransfer⟩
  simp [absPendingGrantMeta, plannedTxn, hdirtySrc, htransfer, hresult, probeMaskForResult]
  rw [atomic_cachedProbeMask_refMap_eq s i htxn]
  simp [absGrantKind]

/-! ### Dirty-source acquire helpers -/

/-- Under dirtyExclusiveInv + lineWFInv, the dirty owner has perm = .T. -/
private theorem dirty_owner_perm_T {n : Nat}
    {s : SymState HomeState NodeState n} {i j : Fin n}
    (hlineWF : lineWFInv n s)
    (hji : j ≠ i)
    (hdirty : (s.locals j).line.dirty = true) :
    (s.locals j).line.perm = .T :=
  ((hlineWF j).1 hdirty).1

/-- Under permSwmrInv + lineWFInv, if j is dirty then writableProbeMask s i = singleProbeMask j.1.
    Since j is the unique .T node, only j.1 appears in the writable mask. -/
private theorem writableProbeMask_eq_singleProbeMask_of_dirty {n : Nat}
    {s : SymState HomeState NodeState n} {i j : Fin n}
    (hlineWF : lineWFInv n s)
    (hSwmr : permSwmrInv n s)
    (hji : j ≠ i)
    (hdirty : (s.locals j).line.dirty = true) :
    writableProbeMask s i = TileLink.Atomic.singleProbeMask j.1 := by
  have hpermT : (s.locals j).line.perm = .T := dirty_owner_perm_T hlineWF hji hdirty
  funext k
  unfold writableProbeMask TileLink.Atomic.singleProbeMask
  by_cases hk : k < n
  · simp only [hk, ↓reduceDIte]
    by_cases hpj : k = j.1
    · -- k = j.1: writable because perm = .T, and j ≠ i
      subst hpj
      have hpi : (⟨j.1, hk⟩ : Fin n) = j := Fin.ext rfl
      rw [hpi]
      simp [hji, hpermT]
    · -- k ≠ j.1: perm = .N from SWMR, so not writable
      have hpne : (⟨k, hk⟩ : Fin n) ≠ j := fun h => hpj (congrArg Fin.val h)
      have hpermN : (s.locals ⟨k, hk⟩).line.perm = .N :=
        hSwmr j ⟨k, hk⟩ (Ne.symm hpne) hpermT
      simp [hpj, hpermN]
  · simp [hk, show ¬(k = j.1) from fun h => hk (h ▸ j.isLt)]

theorem refMap_recvAcquireBlock_branch_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hinv : refinementInv n s)
    (hstep : RecvAcquireBlockAtManager s s' i grow source)
    (hNoDirty : ¬hasDirtyOther s i)
    (hbranch : hasCachedOther s i ∧ grow.result = .B) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  sorry

theorem refMap_recvAcquireBlock_tip_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hinv : refinementInv n s)
    (hstep : RecvAcquireBlockAtManager s s' i grow source)
    (htip : allOthersInvalid s i ∧ grow.result = .T) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  sorry

theorem refMap_recvAcquirePerm_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hinv : refinementInv n s)
    (hstep : RecvAcquirePermAtManager s s' i grow source) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  sorry

theorem refMap_recvAcquireAtManager_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hinv : refinementInv n s)
    (hstep : RecvAcquireAtManager s s' i) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  sorry

end TileLink.Messages
