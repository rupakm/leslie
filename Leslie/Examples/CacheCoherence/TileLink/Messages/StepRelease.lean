import Leslie.Examples.CacheCoherence.TileLink.Messages.StepGrant

namespace TileLink.Messages

open TLA TileLink SymShared

private theorem fin_val_ne_of_ne {n : Nat} {i j : Fin n} (h : j ≠ i) : j.1 ≠ i.1 := by
  intro hval
  apply h
  exact Fin.ext hval

private theorem chanB_none_of_currentTxn_none (n : Nat)
    (s : SymState HomeState NodeState n) (hchanB : chanBInv n s)
    (hcur : s.shared.currentTxn = none) :
    ∀ j : Fin n, (s.locals j).chanB = none := by
  intro j
  specialize hchanB j
  cases hB : (s.locals j).chanB with
  | none => exact rfl
  | some _ =>
      rw [hB] at hchanB
      rcases hchanB with ⟨tx, hcurTx, _, _, _, _, _⟩
      rw [hcur] at hcurTx
      simp at hcurTx

private theorem chanD_none_of_no_pending (n : Nat)
    (s : SymState HomeState NodeState n) (hchanD : chanDInv n s)
    (hcur : s.shared.currentTxn = none)
    (_hgrant : s.shared.pendingGrantAck = none)
    (hrel : s.shared.pendingReleaseAck = none) :
    ∀ j : Fin n, (s.locals j).chanD = none := by
  intro j
  specialize hchanD j
  cases hD : (s.locals j).chanD with
  | none => exact rfl
  | some _ =>
      rw [hD] at hchanD
      rcases hchanD with hgrantBranch | hrelBranch
      · rcases hgrantBranch with ⟨tx, hcurTx, _, _, hpending, _, _, _⟩
        rw [hcur] at hcurTx
        simp at hcurTx
      · rcases hrelBranch with ⟨hcurNone, hpendingGrant, hpendingRel, _, _, _, _⟩
        rw [hrel] at hpendingRel
        simp at hpendingRel

private theorem chanE_none_of_pendingGrant_none (n : Nat)
    (s : SymState HomeState NodeState n) (hchanE : chanEInv n s)
    (hgrant : s.shared.pendingGrantAck = none) :
    ∀ j : Fin n, (s.locals j).chanE = none := by
  intro j
  specialize hchanE j
  cases hE : (s.locals j).chanE with
  | none => exact rfl
  | some _ =>
      rw [hE] at hchanE
      rcases hchanE with ⟨tx, _, _, _, hpending, _, _, _⟩
      rw [hgrant] at hpending
      simp at hpending

private theorem chanD_none_of_other_pendingRelease (n : Nat)
    (s : SymState HomeState NodeState n) (hchanD : chanDInv n s)
    (hcur : s.shared.currentTxn = none)
    (_hgrant : s.shared.pendingGrantAck = none)
    {i : Fin n} (hrel : s.shared.pendingReleaseAck = some i.1) :
    ∀ j : Fin n, j ≠ i → (s.locals j).chanD = none := by
  intro j hji
  specialize hchanD j
  cases hD : (s.locals j).chanD with
  | none => exact rfl
  | some _ =>
      rw [hD] at hchanD
      rcases hchanD with hgrantBranch | hrelBranch
      · rcases hgrantBranch with ⟨tx, hcurTx, _, _, _, _, _, _⟩
        rw [hcur] at hcurTx
        simp at hcurTx
      · rcases hrelBranch with ⟨hcurNone, _, hpendingRel, _, _, _, _⟩
        rw [hrel] at hpendingRel
        injection hpendingRel with hEq
        exfalso
        apply hji
        exact Fin.ext hEq.symm

theorem coreInv_preserved_sendRelease (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} {param : PruneReportParam} (hstep : SendRelease s s' i param) :
    coreInv n s' := by
  rcases hinv with ⟨hlineWF, hdir, hpending, htxn⟩
  rcases hstep with ⟨hcur, hgrant, hrel, _, hA, hB, hC, hD, hE, _, _, _, _, _, _, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal] using
        (releasedLine_wf (s.locals i).line param.result)
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hlineWF j
  · intro j hCnone
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal] at hCnone
    · have hCnone_old : (s.locals j).chanC = none := by
        simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hCnone
      simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hdir j hCnone_old
  · simpa [pendingInv, sendReleaseState, hcur, hgrant, hrel] using hpending
  · simpa [txnCoreInv, sendReleaseState, hcur] using htxn

theorem coreInv_preserved_sendReleaseData (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} {param : PruneReportParam} (hstep : SendReleaseData s s' i param) :
    coreInv n s' := by
  rcases hinv with ⟨hlineWF, hdir, hpending, htxn⟩
  rcases hstep with ⟨hcur, hgrant, hrel, _, hA, hB, hC, hD, hE, _, _, _, _, _, _, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal] using
        (releasedLine_wf (s.locals i).line param.result)
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hlineWF j
  · intro j hCnone
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal] at hCnone
    · have hCnone_old : (s.locals j).chanC = none := by
        simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hCnone
      simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hdir j hCnone_old
  · simpa [pendingInv, sendReleaseState, hcur, hgrant, hrel] using hpending
  · simpa [txnCoreInv, sendReleaseState, hcur] using htxn

theorem channelInv_preserved_sendRelease (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    {i : Fin n} {param : PruneReportParam} (hstep : SendRelease s s' i param) :
    channelInv n s' := by
  rcases hinv with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  rcases hstep with ⟨hcur, hgrant, hrel, _, hA, hB, hC, hD, hE, _, _, _, _, _, _, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, hA]
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hchanA j
  · intro j
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, hB]
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hchanB j
  · intro j
    by_cases hji : j = i
    · subst j
      have hmsg :
          ((sendReleaseState s i param false).locals i).chanC =
            some (releaseMsg i.1 param false (s.locals i).line) := by
        simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal]
      rw [hmsg]
      right
      refine ⟨param, ?_⟩
      refine ⟨hcur, ?_, ?_, ?_, ?_, ?_, ?_, releaseMsg_of_clean i.1 param (s.locals i).line⟩
      · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal]
      · simpa [sendReleaseState_chanA] using hA
      · simpa [sendReleaseState_chanB] using hB
      · simp [releaseMsg]
      · simp [releaseMsg]
      · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, releasedLine_perm]
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hchanC j
  · intro j
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, hD]
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hchanD j
  · intro j
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, hE]
    · simpa [sendReleaseState_chanE, setFn, hji] using hchanE j

theorem channelInv_preserved_sendReleaseData (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    {i : Fin n} {param : PruneReportParam} (hstep : SendReleaseData s s' i param) :
    channelInv n s' := by
  rcases hinv with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  rcases hstep with ⟨hcur, hgrant, hrel, _, hA, hB, hC, hD, hE, _, _, _, _, _, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, hA]
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hchanA j
  · intro j
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, hB]
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hchanB j
  · intro j
    by_cases hji : j = i
    · subst j
      have hmsg :
          ((sendReleaseState s i param true).locals i).chanC =
            some (releaseMsg i.1 param true (s.locals i).line) := by
        simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal]
      rw [hmsg]
      right
      refine ⟨param, ?_⟩
      refine ⟨hcur, ?_, ?_, ?_, ?_, ?_, ?_, releaseMsg_of_dirty i.1 param (s.locals i).line⟩
      · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal]
      · simpa [sendReleaseState_chanA] using hA
      · simpa [sendReleaseState_chanB] using hB
      · simp [releaseMsg]
      · simp [releaseMsg]
      · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, releasedLine_perm]
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hchanC j
  · intro j
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, hD]
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hchanD j
  · intro j
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, hE]
    · simpa [sendReleaseState_chanE, setFn, hji] using hchanE j

theorem coreInv_preserved_recvReleaseAtManager (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} (hstep : RecvReleaseAtManager s s' i) :
    coreInv n s' := by
  rcases hinv with ⟨hlineWF, hdir, hpending, htxn⟩
  rcases hstep with ⟨msg, param, hcur, hgrant, hrel, hflight, hC, hsrc, hwf, hparam, hperm, hD, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    simpa [recvReleaseState_line] using hlineWF j
  · intro j hCnone
    by_cases hji : j = i
    · subst j
      simpa [recvReleaseState, recvReleaseShared, recvReleaseLocals, recvReleaseLocal, updateDirAt, hperm]
    · have hCnone_old : (s.locals j).chanC = none := by
        simpa [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji] using hCnone
      have hdirj := hdir j hCnone_old
      simpa [recvReleaseState, recvReleaseShared, recvReleaseLocals, recvReleaseLocal, setFn, hji,
        updateDirAt, fin_val_ne_of_ne hji] using hdirj
  · simp [pendingInv, recvReleaseState, recvReleaseShared, hcur, hgrant]
    refine ⟨i, rfl, ?_⟩
    simpa [recvReleaseState, recvReleaseLocals, recvReleaseLocal] using hflight
  · simpa [txnCoreInv, recvReleaseState, recvReleaseShared, hcur] using htxn

theorem channelInv_preserved_recvReleaseAtManager (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    {i : Fin n} (hstep : RecvReleaseAtManager s s' i) :
    channelInv n s' := by
  rcases hinv with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  rcases hstep with ⟨msg, param, hcur, hgrant, hrel, hflight, hC, hsrc, hwf, hparam, hperm, hD, rfl⟩
  have hDnoneAll := chanD_none_of_no_pending n s hchanD hcur hgrant hrel
  have hEnoneAll := chanE_none_of_pendingGrant_none n s hchanE hgrant
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa [recvReleaseState_chanA] using hchanA j
  · intro j
    simpa [recvReleaseState_chanB] using hchanB j
  · intro j
    by_cases hji : j = i
    · subst j
      simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal]
    · simpa [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji] using hchanC j
  · intro j
    by_cases hji : j = i
    · subst j
      have hmsg :
          ((recvReleaseState s i msg param).locals i).chanD = some (releaseAckMsg i.1) := by
        simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal]
      rw [hmsg]
      right
      refine ⟨hcur, hgrant, ?_, ?_, ?_, ?_, rfl⟩
      · simp [recvReleaseState, recvReleaseShared]
      · simpa [recvReleaseState_releaseInFlight] using hflight
      · simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal]
      · simpa [recvReleaseState_chanE] using hEnoneAll i
    · have hnone : ((recvReleaseState s i msg param).locals j).chanD = none := by
        simpa [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji] using hDnoneAll j
      rw [hnone]
      trivial
  · intro j
    have hnone : ((recvReleaseState s i msg param).locals j).chanE = none := by
      simpa [recvReleaseState_chanE] using hEnoneAll j
    rw [hnone]
    trivial

theorem coreInv_preserved_recvReleaseAckAtMaster (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} (hstep : RecvReleaseAckAtMaster s s' i) :
    coreInv n s' := by
  rcases hinv with ⟨hlineWF, hdir, hpending, htxn⟩
  rcases hstep with ⟨msg, hcur, hgrant, hrel, hflight, hD, hmsg, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    simpa [recvReleaseAckState_line] using hlineWF j
  · intro j hCnone
    have hCnone_old : (s.locals j).chanC = none := by
      simpa [recvReleaseAckState_chanC] using hCnone
    have hline : ((recvReleaseAckState s i).locals j).line = (s.locals j).line := by
      simpa [recvReleaseAckState_line]
    rw [hline]
    exact hdir j hCnone_old
  · simp [pendingInv, recvReleaseAckState, recvReleaseAckShared, hcur, hgrant]
  · simpa [txnCoreInv, recvReleaseAckState, recvReleaseAckShared, hcur] using htxn

theorem channelInv_preserved_recvReleaseAckAtMaster (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    {i : Fin n} (hstep : RecvReleaseAckAtMaster s s' i) :
    channelInv n s' := by
  rcases hinv with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  rcases hstep with ⟨msg, hcur, hgrant, hrel, hflight, hD, hmsg, rfl⟩
  have hBnone := chanB_none_of_currentTxn_none n s hchanB hcur
  have hDotherNone := chanD_none_of_other_pendingRelease n s hchanD hcur hgrant hrel
  have hEnone := chanE_none_of_pendingGrant_none n s hchanE hgrant
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa [recvReleaseAckState_chanA] using hchanA j
  · intro j
    have hnone : ((recvReleaseAckState s i).locals j).chanB = none := by
      simpa [recvReleaseAckState_chanB] using hBnone j
    rw [hnone]
    trivial
  · intro j
    by_cases hji : j = i
    · subst j
      have hCi : (s.locals i).chanC = none := by
        specialize hchanD i
        rw [hD] at hchanD
        rcases hchanD with hgrantBranch | hrelBranch
        · rcases hgrantBranch with ⟨tx, hcurTx, _, _, _, _, _, _⟩
          rw [hcur] at hcurTx
          simp at hcurTx
        · rcases hrelBranch with ⟨_, _, _, _, hCnone, _, _⟩
          exact hCnone
      simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, hCi]
    · simpa [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji] using hchanC j
  · intro j
    by_cases hji : j = i
    · subst j
      simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal]
    · have hnone : ((recvReleaseAckState s i).locals j).chanD = none := by
        simpa [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji] using hDotherNone j hji
      rw [hnone]
      trivial
  · intro j
    have hnone : ((recvReleaseAckState s i).locals j).chanE = none := by
      simpa [recvReleaseAckState_chanE] using hEnone j
    rw [hnone]
    trivial

theorem fullInv_preserved_with_release (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hinv : fullInv n s) (hnext : (tlMessages.toSpec n).next s s') :
    fullInv n s' := by
  rcases hinv with ⟨hcore, hchan, _hser⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock grow source =>
      have hcore' := coreInv_preserved_sendAcquireBlock n s s' hcore hstep
      have hchan' := channelInv_preserved_sendAcquireBlock n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .sendAcquirePerm grow source =>
      have hcore' := coreInv_preserved_sendAcquirePerm n s s' hcore hstep
      have hchan' := channelInv_preserved_sendAcquirePerm n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, hrecv⟩
        have hcore' := coreInv_preserved_recvAcquireBlock n s s' hcore hrecv
        have hchan' := channelInv_preserved_recvAcquireBlock n s s' hcore hchan hrecv
        exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
      · rcases hperm with ⟨grow, source, hrecv⟩
        have hcore' := coreInv_preserved_recvAcquirePerm n s s' hcore hrecv
        have hchan' := channelInv_preserved_recvAcquirePerm n s s' hcore hchan hrecv
        exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .recvProbeAtMaster =>
      have hcore' := coreInv_preserved_recvProbeAtMaster n s s' hcore hstep
      have hchan' := channelInv_preserved_recvProbeAtMaster n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .recvProbeAckAtManager =>
      have hcore' := coreInv_preserved_recvProbeAckAtManager n s s' hcore hstep
      have hchan' := channelInv_preserved_recvProbeAckAtManager n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .sendGrantToRequester =>
      have hcore' := coreInv_preserved_sendGrantToRequester n s s' hcore hstep
      have hchan' := channelInv_preserved_sendGrantToRequester n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .recvGrantAtMaster =>
      have hcore' := coreInv_preserved_recvGrantAtMaster n s s' hcore hstep
      have hchan' := channelInv_preserved_recvGrantAtMaster n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .recvGrantAckAtManager =>
      have hcore' := coreInv_preserved_recvGrantAckAtManager n s s' hcore hstep
      have hchan' := channelInv_preserved_recvGrantAckAtManager n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .sendRelease param =>
      have hcore' := coreInv_preserved_sendRelease n s s' hcore hstep
      have hchan' := channelInv_preserved_sendRelease n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .sendReleaseData param =>
      have hcore' := coreInv_preserved_sendReleaseData n s s' hcore hstep
      have hchan' := channelInv_preserved_sendReleaseData n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .recvReleaseAtManager =>
      have hcore' := coreInv_preserved_recvReleaseAtManager n s s' hcore hstep
      have hchan' := channelInv_preserved_recvReleaseAtManager n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .recvReleaseAckAtMaster =>
      have hcore' := coreInv_preserved_recvReleaseAckAtMaster n s s' hcore hstep
      have hchan' := channelInv_preserved_recvReleaseAckAtMaster n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .store v =>
      rcases hstep with ⟨hcur, hgrant, hrel, hperm, hA, hB, hC, hD, hE, hSrc, hFlight, hs'⟩
      subst hs'
      rcases hcore with ⟨hlineWF, hdir, hpending, htxn⟩
      rcases hchan with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
      have hcore' : coreInv n { shared := s.shared, locals := setFn s.locals i (storeLocal (s.locals i) v) } := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · -- lineWFInv
          intro j
          by_cases hji : j = i
          · subst j; simp [setFn, storeLocal, CacheLine.WellFormed]
          · simpa [setFn, hji] using hlineWF j
        · -- dirInv
          intro j hCnone
          by_cases hji : j = i
          · subst j
            simp [setFn, storeLocal] at hCnone ⊢
            rw [hdir i hC, hperm]
          · have hCnone_old : (s.locals j).chanC = none := by
              simpa [setFn, hji] using hCnone
            simpa [setFn, hji] using hdir j hCnone_old
        · -- pendingInv
          simpa [pendingInv, hcur, hgrant, hrel] using hpending
        · -- txnCoreInv
          simpa [txnCoreInv, hcur] using htxn
      have hchan' : channelInv n { shared := s.shared, locals := setFn s.locals i (storeLocal (s.locals i) v) } := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro j
          by_cases hji : j = i
          · subst j; simp [setFn, storeLocal, hA]
          · simpa [setFn, hji] using hchanA j
        · intro j
          by_cases hji : j = i
          · subst j; simp [setFn, storeLocal, hB]
          · simpa [setFn, hji] using hchanB j
        · intro j
          by_cases hji : j = i
          · subst j; simp [setFn, storeLocal, hC]
          · simpa [setFn, hji] using hchanC j
        · intro j
          by_cases hji : j = i
          · subst j; simp [setFn, storeLocal, hD]
          · simpa [setFn, hji] using hchanD j
        · intro j
          by_cases hji : j = i
          · subst j; simp [setFn, storeLocal, hE]
          · simpa [setFn, hji] using hchanE j
      exact ⟨hcore', hchan', serializationInv_of_core_channel _ _ hcore' hchan'⟩

end TileLink.Messages
