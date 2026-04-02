import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.SimGrant

namespace TileLink.Messages

open TLA TileLink SymShared Classical

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

theorem refMap_sendGrant_block_tip_next {n : Nat}
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

theorem refMap_sendGrant_acquirePerm_next {n : Nat}
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
    (htxn : s.shared.currentTxn = none)
    (hrel : s.shared.pendingReleaseAck = none)
    (hallC : ∀ j : Fin n, (s.locals j).chanC = none) :
    refMapShared n (recvAcquireState s i kind grow source) =
      { mem := (refMap n s).shared.mem
      , dir := (refMap n s).shared.dir
      , pendingGrantMeta := some (absPendingGrantMeta (plannedTxn s i kind grow source))
      , pendingGrantAck := none
      , pendingReleaseAck := none } := by
  rcases plannedTxn_clean_of_not_hasDirtyOther s i hnd with ⟨hdirtySrc, htransfer⟩
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

theorem refMap_recvAcquireBlock_branch_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hinv : refinementInv n s)
    (hstep : RecvAcquireBlockAtManager s s' i grow source)
    (hNoDirty : ¬hasDirtyOther s i)
    (hbranch : hasCachedOther s i ∧ grow.result = .B) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hstep with ⟨htxn, hgrant, hrel, hallC, _hA, hpermN, _hlegal, _, _hBs, hs'⟩
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
    refine ⟨atomic_not_hasDirtyOther_of_not_hasDirtyOther hNoDirty htxn,
            (atomic_hasCachedOther_refMap_iff htxn).2 hcached, ?_⟩
    apply SymState.ext
    · calc
        refMapShared n (recvAcquireState s i .acquireBlock grow source)
            = { (refMap n s).shared with
                  pendingGrantMeta := some (absPendingGrantMeta (plannedTxn s i .acquireBlock grow source))
                , pendingGrantAck := none
                , pendingReleaseAck := none } := by
                  simpa [refMap] using
                    refMapShared_recvAcquireState_eq_absPending' s i .acquireBlock grow source
                      hNoDirty htxn hrel hallC
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
                rw [absPendingGrantMeta_planned_acquireBlock_branch_eq' s i grow source hNoDirty htxn hresult]
    · simpa [refMap] using refMap_recvAcquireState_locals_eq s i .acquireBlock grow source htxn

theorem refMap_recvAcquireBlock_tip_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hinv : refinementInv n s)
    (hstep : RecvAcquireBlockAtManager s s' i grow source)
    (htip : allOthersInvalid s i ∧ grow.result = .T) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hinv with ⟨⟨⟨hwf, _, _, _⟩, _, _⟩, _, _, _, _, _⟩
  rcases hstep with ⟨htxn, hgrant, hrel, hallC, _hA, hpermN, _hlegal, _, _hBs, hs'⟩
  rcases htip with ⟨hallInvalid, hresult⟩
  have hNoDirty : ¬hasDirtyOther s i := not_hasDirtyOther_of_allOthersInvalid hwf hallInvalid
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
                    refMapShared_recvAcquireState_eq_absPending' s i .acquireBlock grow source
                      hNoDirty htxn hrel hallC
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
                rw [absPendingGrantMeta_planned_acquireBlock_tip_eq' s i grow source hNoDirty hallInvalid hresult]
    · simpa [refMap] using refMap_recvAcquireState_locals_eq s i .acquireBlock grow source htxn

theorem refMap_recvAcquirePerm_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hinv : refinementInv n s)
    (hstep : RecvAcquirePermAtManager s s' i grow source) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  -- SORRY: RecvAcquirePermAtManager may have hasDirtyOther. The non-dirty case is proved
  -- by refMap_recvAcquireBlock_branch_next (used for the block case). For the dirty case,
  -- the concrete plannedTxn uses usedDirtySource=true with transferVal = dirtyOwner.data and
  -- probesNeeded = cachedProbeMask. The atomic model expects probesNeeded = cachedProbeMask
  -- with usedDirtySource=true and transferVal = (s.locals j).data for the dirty owner j.
  -- Needs: (1) identifying the dirty owner j from dirtyOwnerOpt, (2) proving transferVal matches,
  -- (3) proving cachedProbeMask agrees between concrete and abstract. Under permSwmrInv,
  -- the dirty node has perm=T so cachedProbeMask includes it, matching the atomic model.
  sorry

theorem refMap_recvAcquireAtManager_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hinv : refinementInv n s)
    (hstep : RecvAcquireAtManager s s' i) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hstep with ⟨grow, source, hblk⟩ | ⟨grow, source, hperm⟩
  · -- RecvAcquireBlockAtManager: 3-way disjunction
    have hshape := hblk.2.2.2.2.2.2.2.1
    rcases hshape with ⟨hDirtyOther, hresultB⟩ | ⟨hNoDirty, hcached, hresultB⟩ | ⟨hallInvalid, hresultT⟩
    · -- Case 1: hasDirtyOther ∧ .B — dirty-source acquire
      -- SORRY: The concrete plannedTxn with hasDirtyOther creates usedDirtySource=true,
      -- transferVal = dirtyOwner.data, probesNeeded = writableProbeMask. The atomic model
      -- expects singleProbeMask j.1 for the dirty owner j. Under permSwmrInv (at most one T),
      -- the dirty node is the unique T-perm node, so writableProbeMask = singleProbeMask j.1.
      -- Proving this equivalence requires connecting dirtyExclusiveInv + permSwmrInv to
      -- the concrete/atomic probe mask agreement. Left as sorry pending probe mask lemmas.
      sorry
    · -- Case 2: ¬hasDirtyOther ∧ hasCachedOther ∧ .B
      exact refMap_recvAcquireBlock_branch_next hinv hblk hNoDirty ⟨hcached, hresultB⟩
    · -- Case 3: allOthersInvalid ∧ .T
      exact refMap_recvAcquireBlock_tip_next hinv hblk ⟨hallInvalid, hresultT⟩
  · exact refMap_recvAcquirePerm_next hinv hperm

end TileLink.Messages
