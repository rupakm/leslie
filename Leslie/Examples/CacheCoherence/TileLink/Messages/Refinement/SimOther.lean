import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.SimAcquire

namespace TileLink.Messages

open TLA TileLink SymShared Classical

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
  rcases hstep with ⟨tx, msg, hcur, hphase, _, _, hC, _, _, hs'⟩
  rw [hs']
  have hphase' : probeAckPhase (n := n) (clearProbeIdx tx.probesRemaining i.1) ≠ .grantPendingAck := by
    intro hbad
    unfold probeAckPhase at hbad
    split at hbad <;> cases hbad
  apply SymState.ext
  · change refMapShared n (recvProbeAckState s i tx msg) = refMapShared n s
    simp [refMapShared, recvProbeAckState, recvProbeAckShared, hcur, hphase, hphase']
    constructor
    · -- mem: refMap uses tx.transferVal or s.shared.mem depending on usedDirtySource.
      -- tx fields unchanged by probeAck (only probesRemaining/phase change).
      -- If usedDirtySource=true: mem = tx.transferVal (unchanged) ✓
      -- If usedDirtySource=false: mem = s.shared.mem. After probeAck, concrete mem becomes
      --   match msg.data with some v => v | none => s.shared.mem.
      --   Proving msg.data = none requires connecting ¬usedDirtySource to the probed node
      --   being clean (via preLinesNoDirtyInv + txnLineInv). Needs txnDataInv generalization.
      sorry
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

theorem refMap_recvGrantAckAtManager_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (hstep : RecvGrantAckAtManager s s' i) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hfull with ⟨hcore, hchan, _⟩
  rcases hcore with ⟨_, hdir, hpending, htxnCore⟩
  rcases hchan with ⟨_, _, hchanC, _, _⟩
  rcases hstep with ⟨tx, msg, hcur, hreq, hphase, hpendingGrant, hD, hE, hSink, hmsg, hs'⟩
  have hpendPair : s.shared.pendingReleaseAck = none ∧ s.shared.pendingGrantAck = some tx.requester := by
    simpa [pendingInv, hcur, hphase] using hpending
  have hpendRel : s.shared.pendingReleaseAck = none := hpendPair.1
  have hCnone : ∀ j : Fin n, (s.locals j).chanC = none := by
    intro j
    specialize hchanC j
    cases hC : (s.locals j).chanC with
    | none => exact rfl
    | some _ =>
        rw [hC] at hchanC
        rcases hchanC with hprobe | hrel
        · rcases hprobe with ⟨tx0, hcur0, hprobing, _, _, _, _, _⟩
          rw [hcur] at hcur0
          injection hcur0 with htx
          subst htx
          rw [hphase] at hprobing
          cases hprobing
        · rcases hrel with ⟨_, htxnNone, _, _, _, _, _, _⟩
          rw [hcur] at htxnNone
          simp at htxnNone
  have hCnone' : ∀ j : Fin n, ((recvGrantAckState s i).locals j).chanC = none := by
    intro j
    by_cases hji : j = i
    · simpa [recvGrantAckState, recvGrantAckLocals, setFn, hji] using hCnone j
    · simpa [recvGrantAckState, recvGrantAckLocals, setFn, hji] using hCnone j
  have hqueuedNone : queuedReleaseIdx n (recvGrantAckState s i) = none :=
    queuedReleaseIdx_eq_none_of_all_chanC_none (recvGrantAckState s i) hCnone'
  rw [hs']
  simp only [SymSharedSpec.toSpec, TileLink.Atomic.tlAtomic]
  refine ⟨i, .grantAck, ?_⟩
  constructor
  · simpa [refMap, refMapShared, hcur, hphase, hpendingGrant, hreq]
  · apply SymState.ext
    · change refMapShared n (recvGrantAckState s i) =
          { (refMap n s).shared with pendingGrantMeta := none, pendingGrantAck := none }
      rw [TileLink.Atomic.HomeState.mk.injEq]
      constructor
      · simp [refMap, refMapShared, recvGrantAckState, recvGrantAckShared, hcur]
      constructor
      · funext k
        by_cases hk : k < n
        · let j : Fin n := ⟨k, hk⟩
          by_cases hji : j = i
          · have hreqj : tx.requester = j.1 := by simpa [hji] using hreq
            have hEj : (s.locals j).chanE = some msg := by simpa [hji] using hE
            have hlinej : (s.locals j).line = grantLine (tx.preLines j.1) tx := by
              have hlines : ∀ u : Fin n, (s.locals u).line = txnSnapshotLine tx (s.locals u) u := by
                simpa [txnLineInv, hcur] using htxnLine
              specialize hlines j
              simpa [txnSnapshotLine, probeSnapshotLine, hphase, hreqj, hEj] using hlines
            have hgrantPerm : (grantLine (tx.preLines j.1) tx).perm = tx.resultPerm := by
              unfold grantLine
              by_cases hdata : tx.grantHasData
              · rw [if_pos hdata]
                cases hperm : tx.resultPerm <;> simp
              · rw [if_neg hdata]
                have hdataFalse : tx.grantHasData = false := by
                  cases hgd : tx.grantHasData with
                  | false => rfl
                  | true => exact False.elim (hdata hgd)
                have hresT : tx.resultPerm = .T := by
                  rcases (by simpa [txnCoreInv, hcur] using htxnCore) with
                    ⟨_, _, _, hnoData, _, _, _, _⟩
                  exact hnoData hdataFalse
                simp [hresT]
            have hdirj : s.shared.dir j.1 = (s.locals j).line.perm := hdir j (hCnone j)
            have hpermEq : (s.locals j).line.perm = tx.resultPerm := by
              rw [hlinej]
              exact hgrantPerm
            calc
              TileLink.Atomic.syncDir s.shared.dir
                  (fun u => ((recvGrantAckState s i).locals u).line) k =
                    ((recvGrantAckState s i).locals j).line.perm := by
                      simp [j, TileLink.Atomic.syncDir, hk]
              _ = (s.locals j).line.perm := by
                    simp [recvGrantAckState, recvGrantAckLocals, setFn, hji]
              _ = s.shared.dir k := by simpa [j] using hdirj.symm
              _ = tx.resultPerm := by simpa [j] using hdirj.trans hpermEq
              _ = (refMap n s).shared.dir k := by
                    have hkreq : tx.requester < n := by simpa [j, hreqj] using j.is_lt
                    have hkeq : k = tx.requester := by simpa [j] using hreqj.symm
                    simp [refMap, refMapShared, hcur, hphase, grantPendingDir, hkreq, updateDirAt, hkeq]
          · have hki : k ≠ i.1 := by
              intro h
              apply hji
              exact Fin.ext h
            have hdirj : s.shared.dir j.1 = (s.locals j).line.perm := hdir j (hCnone j)
            calc
              TileLink.Atomic.syncDir s.shared.dir
                  (fun u => ((recvGrantAckState s i).locals u).line) k
                  = ((recvGrantAckState s i).locals j).line.perm := by
                      simp [j, TileLink.Atomic.syncDir, hk]
              _ = (s.locals j).line.perm := by
                    simp [recvGrantAckState, recvGrantAckLocals, setFn, hji]
              _ = s.shared.dir k := by simpa [j] using hdirj.symm
              _ = (refMap n s).shared.dir k := by
                    simp [j, refMap, refMapShared, hcur, hphase, grantPendingDir, updateDirAt, hreq, hki]
        · have hki : k ≠ i.1 := by
            intro h
            apply hk
            simpa [h] using i.is_lt
          have hkreq : tx.requester < n := by simpa [hreq] using i.is_lt
          have hkreq' : k ≠ tx.requester := by
            intro h
            apply hk
            rw [h]
            exact hkreq
          simp [refMap, refMapShared, recvGrantAckState, recvGrantAckShared,
            TileLink.Atomic.syncDir, grantPendingDir, updateDirAt, hcur, hphase, hk, hkreq, hkreq']
      constructor
      · simp [refMap, refMapShared, recvGrantAckState, recvGrantAckShared, hcur]
      constructor
      · simp [refMap, refMapShared, recvGrantAckState, recvGrantAckShared, hcur, hphase]
      · simpa [refMap, refMapShared, recvGrantAckState, recvGrantAckShared, hcur, hphase, hpendRel]
          using hqueuedNone
    · change (refMap n (recvGrantAckState s i)).locals = (refMap n s).locals
      funext j
      by_cases hji : j = i
      · have hreqj : tx.requester = j.1 := by simpa [hji] using hreq
        have hEj : (s.locals j).chanE = some msg := by simpa [hji] using hE
        have hlinej : (s.locals j).line = grantLine (tx.preLines j.1) tx := by
          have hlines : ∀ u : Fin n, (s.locals u).line = txnSnapshotLine tx (s.locals u) u := by
            simpa [txnLineInv, hcur] using htxnLine
          specialize hlines j
          simpa [txnSnapshotLine, probeSnapshotLine, hphase, hreqj, hEj] using hlines
        calc
          refMapLine (recvGrantAckState s i) j = (s.locals j).line := by
            simp [refMapLine, recvGrantAckState, recvGrantAckShared, recvGrantAckLocals, setFn, hji]
          _ = grantLine (tx.preLines j.1) tx := hlinej
          _ = refMapLine s j := by
            simp [refMapLine, hcur, hphase, hreqj]
      · have hreqj : tx.requester ≠ j.1 := by
          intro h
          apply hji
          exact Fin.ext (h.symm.trans hreq)
        simpa [refMap, refMapLine, recvGrantAckState, recvGrantAckShared, recvGrantAckLocals,
          setFn, hcur, hphase, hreqj, hji]

theorem releasedLine_eq (line : CacheLine) (perm : TLPerm) :
    TileLink.Messages.releasedLine line perm = TileLink.Atomic.releasedLine line perm := by
  cases perm <;> simp [TileLink.Messages.releasedLine, TileLink.Atomic.releasedLine,
    invalidatedLine, TileLink.Atomic.invalidateLine,
    branchAfterProbe, TileLink.Atomic.branchLine,
    tipAfterProbe, TileLink.Atomic.tipLine]

private theorem queuedReleaseIdx_sendRelease {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n)
    (param : PruneReportParam)
    (hCi : (s.locals i).chanC = none)
    (hflighti : (s.locals i).releaseInFlight = false)
    (hCother : ∀ j : Fin n, j ≠ i → (s.locals j).chanC = none) :
    queuedReleaseIdx n (sendReleaseState s i param false) = some i.1 := by
  unfold queuedReleaseIdx
  have hexists : ∃ j : Fin n, ((sendReleaseState s i param false).locals j).releaseInFlight = true ∧
      ((sendReleaseState s i param false).locals j).chanC ≠ none := by
    refine ⟨i, ?_, ?_⟩
    · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn]
    · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn]
  rw [dif_pos hexists]
  have huniq : ∀ j : Fin n, ((sendReleaseState s i param false).locals j).releaseInFlight = true ∧
      ((sendReleaseState s i param false).locals j).chanC ≠ none → j = i := by
    intro j ⟨_, hcj⟩
    by_contra hne
    simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hne] at hcj
    exact hcj (hCother j hne)
  have heqi := huniq _ (Classical.choose_spec hexists)
  exact congrArg (fun x => some (x : Fin n).1) heqi

theorem refMap_sendRelease_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {param : PruneReportParam}
    (hfull : fullInv n s)
    (hstep : SendRelease s s' i param) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hfull with ⟨hcore, hchan, _⟩
  rcases hcore with ⟨_, hdir, hpending, _⟩
  rcases hstep with ⟨htxn, hgrant, hrel, hCother, hA, hB, hCi, hD, hE, hps, hpk, hflight,
    hlegal, hnotdirty, hvalid, hs'⟩
  rw [hs']
  simp only [SymSharedSpec.toSpec, TileLink.Atomic.tlAtomic]
  refine ⟨i, .release param, ?_⟩
  have hpendingGrant : s.shared.pendingGrantAck = none := by
    have h := hpending
    simp only [pendingInv, htxn] at h
    exact h.1
  have hqueuedNone : queuedReleaseIdx n s = none := by
    apply queuedReleaseIdx_eq_none_of_all_chanC_none
    intro j
    by_cases hji : j = i
    · subst j; exact hCi
    · exact hCother j hji
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- pendingGrantMeta = none
    show (refMap n s).shared.pendingGrantMeta = none
    simp [refMap, refMapShared, htxn]
  · -- pendingGrantAck = none
    show (refMap n s).shared.pendingGrantAck = none
    simp [refMap, refMapShared, htxn, hrel, hqueuedNone, hpendingGrant]
  · -- pendingReleaseAck = none
    show (refMap n s).shared.pendingReleaseAck = none
    simp [refMap, refMapShared, htxn, hrel, hqueuedNone]
  · -- param.legalFrom
    show param.legalFrom ((refMap n s).locals i).perm
    simp [refMap, refMapLine, htxn]
    exact hlegal
  · -- dirty = false
    show ((refMap n s).locals i).dirty = false
    simp [refMap, refMapLine, htxn]
    exact hnotdirty
  · -- valid ∨ result = N
    show ((refMap n s).locals i).valid = true ∨ param.result = TLPerm.N
    simp [refMap, refMapLine, htxn]
    exact hvalid
  · -- postcondition: s' = expected state
    apply SymState.ext
    · -- shared
      rw [TileLink.Atomic.HomeState.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- mem
        simp [refMap, refMapShared, sendReleaseState, htxn]
      · -- dir
        funext k
        simp only [refMap, refMapShared, sendReleaseState, htxn, hrel, hqueuedNone]
        by_cases hk : k < n
        · simp only [TileLink.Atomic.syncDir, hk, dite_true]
          simp only [sendReleaseLocals, sendReleaseLocal, setFn, refMapLine, htxn]
          split
          · simp [releasedLine_eq]
          · rfl
        · simp only [TileLink.Atomic.syncDir, hk, dite_false]
      · -- pendingGrantMeta
        simp [refMap, refMapShared, sendReleaseState, htxn]
      · -- pendingGrantAck
        simp [refMap, refMapShared, sendReleaseState, htxn, hpendingGrant]
      · -- pendingReleaseAck
        simp only [refMap, refMapShared, sendReleaseState, htxn, hrel]
        exact queuedReleaseIdx_sendRelease s i param hCi hflight hCother
    · -- locals
      funext j
      simp only [refMap, refMapLine, sendReleaseState, htxn]
      by_cases hji : j = i
      · subst j
        simp [sendReleaseLocals, sendReleaseLocal, setFn, releasedLine_eq]
      · simp [sendReleaseLocals, sendReleaseLocal, setFn, hji, refMapLine, htxn]

theorem refMap_sendReleaseData_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {param : PruneReportParam}
    (hfull : fullInv n s)
    (hstep : SendReleaseData s s' i param) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  -- sendReleaseData maps to atomic releaseData.
  -- The atomic releaseData changes mem := data, but concrete sendReleaseData does not change
  -- s.shared.mem (only recvReleaseAtManager does). The refMap would need to account for
  -- in-flight dirty release data (findDirtyReleaseVal from the plan). This requires extending
  -- refMapShared.mem for the no-txn case to use findDirtyReleaseVal.
  sorry

theorem refMap_recvReleaseAtManager_eq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hfull : fullInv n s) (hcleanRel : cleanChanCInv n s)
    (hCother : ∀ j : Fin n, j ≠ i → (s.locals j).chanC = none)
    (hstep : RecvReleaseAtManager s s' i) :
    refMap n s' = refMap n s := by
  rcases hfull with ⟨hcore, hchan, _⟩
  rcases hcore with ⟨_, _, _, _⟩
  rcases hchan with ⟨_, _, hchanC, _, _⟩
  rcases hstep with ⟨msg, param, htxn, hgrant, hrel, hflight, hC, hsource, hwf, hparam, hperm, hD, hs'⟩
  have hmsgData : msg.data = none := hcleanRel i msg hC
  have hqueuedPre : queuedReleaseIdx n s = some i.1 := by
    unfold queuedReleaseIdx
    have hexists : ∃ j : Fin n, (s.locals j).releaseInFlight = true ∧ (s.locals j).chanC ≠ none :=
      ⟨i, hflight, by rw [hC]; simp⟩
    rw [dif_pos hexists]
    have huniq : Classical.choose hexists = i := by
      have ⟨_, hcC⟩ := Classical.choose_spec hexists
      by_contra hne
      exact hcC (hCother _ hne)
    exact congrArg (fun x => some (x : Fin n).1) huniq
  rw [hs']
  apply SymState.ext
  · -- shared
    change refMapShared n (recvReleaseState s i msg param) = refMapShared n s
    rw [TileLink.Atomic.HomeState.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- mem
      simp only [refMapShared, recvReleaseState, recvReleaseShared, htxn, releaseWriteback, hmsgData]
    · -- dir
      funext k
      simp only [refMapShared, recvReleaseState, recvReleaseShared, htxn, hrel, hqueuedPre]
      by_cases hk : k < n
      · simp only [TileLink.Atomic.syncDir, hk, dite_true,
          recvReleaseLocals, recvReleaseLocal, setFn]
        split <;> simp_all
      · simp only [TileLink.Atomic.syncDir, hk, dite_false, updateDirAt]
        split <;> simp_all
    · -- pendingGrantMeta
      simp only [refMapShared, recvReleaseState, recvReleaseShared, htxn]
    · -- pendingGrantAck
      simp only [refMapShared, recvReleaseState, recvReleaseShared, htxn, hgrant]
    · -- pendingReleaseAck
      simp only [refMapShared, recvReleaseState, recvReleaseShared, htxn, hrel, hqueuedPre]
  · -- locals
    funext j
    simp only [refMap, refMapLine, recvReleaseState, recvReleaseShared, htxn,
      recvReleaseLocals, recvReleaseLocal, setFn]
    split <;> simp_all

theorem refMap_recvReleaseAckAtMaster_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hfull : fullInv n s)
    (hCnone : ∀ j : Fin n, (s.locals j).chanC = none)
    (hstep : RecvReleaseAckAtMaster s s' i) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hfull with ⟨hcore, hchan, _⟩
  rcases hcore with ⟨_, hdir, hpending, _⟩
  rcases hchan with ⟨_, _, hchanC, _, _⟩
  rcases hstep with ⟨msg, htxn, hgrant, hrel, hflight, hD, hmsg, hs'⟩
  rw [hs']
  simp only [SymSharedSpec.toSpec, TileLink.Atomic.tlAtomic]
  refine ⟨i, .releaseAck, ?_⟩
  have hqueuedPre : queuedReleaseIdx n s = none :=
    queuedReleaseIdx_eq_none_of_all_chanC_none s hCnone
  have hCnone' : ∀ j : Fin n, ((recvReleaseAckState s i).locals j).chanC = none := by
    intro j; rw [recvReleaseAckState_chanC]; exact hCnone j
  have hqueuedPost : queuedReleaseIdx n (recvReleaseAckState s i) = none :=
    queuedReleaseIdx_eq_none_of_all_chanC_none _ hCnone'
  constructor
  · -- precondition: pendingReleaseAck = some i.1
    show (refMapShared n s).pendingReleaseAck = some i.1
    simp only [refMapShared, htxn, hrel, hqueuedPre]
  · -- postcondition
    apply SymState.ext
    · -- shared
      show refMapShared n (recvReleaseAckState s i) =
        { (refMapShared n s) with pendingReleaseAck := none }
      rw [TileLink.Atomic.HomeState.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- mem
        simp only [refMapShared, recvReleaseAckState, recvReleaseAckShared, htxn]
      · -- dir
        funext k
        simp only [refMapShared, recvReleaseAckState, recvReleaseAckShared, htxn, hrel, hqueuedPre]
        by_cases hk : k < n
        · simp only [TileLink.Atomic.syncDir, hk, dite_true,
            recvReleaseAckLocals, recvReleaseAckLocal, setFn]
          split <;> simp_all
        · simp only [TileLink.Atomic.syncDir, hk, dite_false]
      · -- pendingGrantMeta
        simp only [refMapShared, recvReleaseAckState, recvReleaseAckShared, htxn]
      · -- pendingGrantAck
        simp only [refMapShared, recvReleaseAckState, recvReleaseAckShared, htxn, hgrant]
      · -- pendingReleaseAck
        simp only [refMapShared, recvReleaseAckState, recvReleaseAckShared, htxn, hrel]
        exact hqueuedPost
    · -- locals unchanged
      funext j
      simp only [refMap, refMapLine, recvReleaseAckState, recvReleaseAckShared, htxn,
        recvReleaseAckLocals, recvReleaseAckLocal, setFn]
      split <;> simp_all

end TileLink.Messages
