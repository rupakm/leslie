import Leslie.Examples.CacheCoherence.TileLink.Messages.InitProof

namespace TileLink.Messages

open TLA TileLink SymShared

theorem probeMaskForResult_requester_false {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) (perm : TLPerm) :
    probeMaskForResult s i perm i.1 = false := by
  cases perm <;> simp [probeMaskForResult, noProbeMask, writableProbeMask, cachedProbeMask, i.is_lt]

private theorem chanD_noneOrAccessAck_of_pendingGrant_none (n : Nat)
    (s : SymState HomeState NodeState n) (hchanD : chanDInv n s)
    (hgrant : s.shared.pendingGrantAck = none)
    (hrel : s.shared.pendingReleaseAck = none) :
    ∀ j : Fin n, (s.locals j).chanD = none ∨
      (∃ msg, (s.locals j).chanD = some msg ∧
        (msg.opcode = .accessAck ∨ msg.opcode = .accessAckData) ∧
        (s.locals j).pendingSource ≠ none ∧
        (s.locals j).chanA = none) := by
  intro j
  specialize hchanD j
  cases hD : (s.locals j).chanD with
  | none => exact Or.inl rfl
  | some msg =>
      rw [hD] at hchanD
      rcases hchanD with hgrantBranch | hrelBranch | ⟨hacc, hps, hchanAnone⟩
      · rcases hgrantBranch with ⟨_, _, _, _, hpending, _, _, _⟩
        rw [hgrant] at hpending; simp at hpending
      · rcases hrelBranch with ⟨_, _, hpendingRel, _, _, _, _⟩
        rw [hrel] at hpendingRel; simp at hpendingRel
      · exact Or.inr ⟨msg, rfl, hacc, hps, hchanAnone⟩

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
      rcases hchanE with ⟨_, _, _, _, hpending, _, _, _⟩
      rw [hgrant] at hpending
      simp at hpending

theorem coreInv_preserved_sendAcquireBlock (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hstep : SendAcquireBlock s s' i grow source) :
    coreInv n s' := by
  rcases hinv with ⟨hlineWF, hdir, hpending, htxn⟩
  rcases hstep with ⟨hA, hB, hC, hPendingSource, hFlightFalse, _, hlegal, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simpa [setFn] using hlineWF i
    · simpa [setFn, hji] using hlineWF j
  · intro j hCnone
    by_cases hji : j = i
    · subst j
      have hCnone_old : (s.locals i).chanC = none := by
        simpa [setFn] using hCnone
      simpa [setFn] using hdir i hCnone_old
    · have hCnone_old : (s.locals j).chanC = none := by
        simpa [setFn, hji] using hCnone
      simpa [setFn, hji] using hdir j hCnone_old
  · cases hcur : s.shared.currentTxn with
    | none =>
        cases hrel : s.shared.pendingReleaseAck with
        | none =>
            simpa [pendingInv, hcur, hrel] using hpending
        | some ridx =>
            simp [pendingInv, hcur, hrel] at hpending ⊢
            rcases hpending with ⟨hgrant, hlt, fi, hfi, hflight⟩
            refine ⟨hgrant, hlt, fi, hfi, ?_⟩
            by_cases hfix : fi = i
            · subst hfix
              rw [hFlightFalse] at hflight
              contradiction
            · simp [setFn, hfix, hflight]
    | some tx =>
        simp [pendingInv, hcur] at hpending ⊢
        exact hpending
  · simpa [txnCoreInv, setFn] using htxn

theorem coreInv_preserved_sendAcquirePerm (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hstep : SendAcquirePerm s s' i grow source) :
    coreInv n s' := by
  rcases hinv with ⟨hlineWF, hdir, hpending, htxn⟩
  rcases hstep with ⟨hA, hB, hC, hPendingSource, hFlightFalse, hlegal, hresT, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simpa [setFn] using hlineWF i
    · simpa [setFn, hji] using hlineWF j
  · intro j hCnone
    by_cases hji : j = i
    · subst j
      have hCnone_old : (s.locals i).chanC = none := by
        simpa [setFn] using hCnone
      simpa [setFn] using hdir i hCnone_old
    · have hCnone_old : (s.locals j).chanC = none := by
        simpa [setFn, hji] using hCnone
      simpa [setFn, hji] using hdir j hCnone_old
  · cases hcur : s.shared.currentTxn with
    | none =>
        cases hrel : s.shared.pendingReleaseAck with
        | none =>
            simpa [pendingInv, hcur, hrel] using hpending
        | some ridx =>
            simp [pendingInv, hcur, hrel] at hpending ⊢
            rcases hpending with ⟨hgrant, hlt, fi, hfi, hflight⟩
            refine ⟨hgrant, hlt, fi, hfi, ?_⟩
            by_cases hfix : fi = i
            · subst hfix
              rw [hFlightFalse] at hflight
              contradiction
            · simp [setFn, hfix, hflight]
    | some tx =>
        simp [pendingInv, hcur] at hpending ⊢
        exact hpending
  · simpa [txnCoreInv, setFn] using htxn

theorem coreInv_preserved_recvAcquireBlock (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hstep : RecvAcquireBlockAtManager s s' i grow source) :
    coreInv n s' := by
  rcases hinv with ⟨hlineWF, hdir, _, _⟩
  rcases hstep with ⟨_, _, _, _, _, _, _, _, _, ⟨_, rfl⟩⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    simpa [recvAcquireState, recvAcquireLocals_line] using hlineWF j
  · intro j hCnone
    have hCnone_old : (s.locals j).chanC = none := by
      simpa [recvAcquireState, recvAcquireLocals, scheduleProbeLocals_chanC] using hCnone
    simpa [recvAcquireState, recvAcquireShared_dir, recvAcquireLocals_line]
      using hdir j hCnone_old
  · simp [pendingInv, recvAcquireState, recvAcquireShared, plannedTxn]
  · refine ⟨i.is_lt, Or.inl rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro hnodata
      simp [plannedTxn] at hnodata
    · exact probeMaskForResult_requester_false s i grow.result
    · intro k hk
      simpa [plannedTxn] using hk
    · refine ⟨?_, ?_⟩
      · intro hready j
        cases hready
      · intro hgrant j
        cases hgrant

theorem coreInv_preserved_recvAcquirePerm (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hstep : RecvAcquirePermAtManager s s' i grow source) :
    coreInv n s' := by
  rcases hinv with ⟨hlineWF, hdir, _, _⟩
  rcases hstep with ⟨_, _, _, _, _, _, _, hresT, _, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    simpa [recvAcquireState, recvAcquireLocals_line] using hlineWF j
  · intro j hCnone
    have hCnone_old : (s.locals j).chanC = none := by
      simpa [recvAcquireState, recvAcquireLocals, scheduleProbeLocals_chanC] using hCnone
    simpa [recvAcquireState, recvAcquireShared_dir, recvAcquireLocals_line]
      using hdir j hCnone_old
  · simp [pendingInv, recvAcquireState, recvAcquireShared, plannedTxn]
  · refine ⟨i.is_lt, Or.inl rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro _
      simpa [plannedTxn] using hresT
    · exact probeMaskForResult_requester_false s i grow.result
    · intro k hk
      simpa [plannedTxn] using hk
    · refine ⟨?_, ?_⟩
      · intro hready j
        cases hready
      · intro hgrant j
        cases hgrant

theorem channelInv_preserved_sendAcquireBlock (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hstep : SendAcquireBlock s s' i grow source) :
    channelInv n s' := by
  rcases hinv with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      rcases hstep with ⟨_, _, _, _, _, hpermN, hlegal, rfl⟩
      simp [setFn]
      exact ⟨rfl, Or.inl ⟨rfl, hlegal⟩⟩
    · rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      simpa [chanAInv, setFn, hji] using hchanA j
  · intro j
    simpa [sendAcquireBlock_shared hstep, sendAcquireBlock_chanB hstep] using hchanB j
  · intro j
    rcases hstep with ⟨_, _, hCpre, _, _, _, _, rfl⟩
    by_cases hji : j = i
    · subst j
      cases hC : (s.locals i).chanC with
      | none =>
          simp [setFn, hC]
      | some msg =>
          rw [hC] at hCpre
          contradiction
    · simpa [setFn, hji] using hchanC j
  · intro j
    rcases hstep with ⟨_, _, _, hPSrc, _, _, _, rfl⟩
    by_cases hji : j = i
    · subst j
      specialize hchanD i
      cases hDi : (s.locals i).chanD with
      | none => simp [setFn, hDi]
      | some msg =>
          simp only [hDi] at hchanD
          simp only [setFn, ite_true, hDi]
          rcases hchanD with hgrant | hrel | ⟨hacc, hps, _⟩
          · exact Or.inl hgrant
          · exact Or.inr (Or.inl hrel)
          · exact absurd hPSrc hps
    · simpa [setFn, hji] using hchanD j
  · intro j
    simpa [sendAcquireBlock_shared hstep, sendAcquireBlock_chanE hstep,
      sendAcquireBlock_pendingSink hstep, sendAcquireBlock_chanD hstep] using hchanE j

theorem channelInv_preserved_sendAcquirePerm (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hstep : SendAcquirePerm s s' i grow source) :
    channelInv n s' := by
  rcases hinv with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      rcases hstep with ⟨_, _, _, _, _, hlegal, hresT, rfl⟩
      simp [setFn]
      exact ⟨rfl, Or.inr (Or.inl ⟨rfl, hlegal, hresT⟩)⟩
    · rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      simpa [chanAInv, setFn, hji] using hchanA j
  · intro j
    simpa [sendAcquirePerm_shared hstep, sendAcquirePerm_chanB hstep] using hchanB j
  · intro j
    rcases hstep with ⟨_, _, hCpre, _, _, _, _, rfl⟩
    by_cases hji : j = i
    · subst j
      cases hC : (s.locals i).chanC with
      | none =>
          simp [setFn, hC]
      | some msg =>
          rw [hC] at hCpre
          contradiction
    · simpa [setFn, hji] using hchanC j
  · intro j
    rcases hstep with ⟨_, _, _, hPSrc, _, _, _, rfl⟩
    by_cases hji : j = i
    · subst j
      specialize hchanD i
      cases hDi : (s.locals i).chanD with
      | none => simp [setFn, hDi]
      | some msg =>
          simp only [hDi] at hchanD
          simp only [setFn, ite_true, hDi]
          rcases hchanD with hgrant | hrel | ⟨hacc, hps, _⟩
          · exact Or.inl hgrant
          · exact Or.inr (Or.inl hrel)
          · exact absurd hPSrc hps
    · simpa [setFn, hji] using hchanD j
  · intro j
    simpa [sendAcquirePerm_shared hstep, sendAcquirePerm_chanE hstep,
      sendAcquirePerm_pendingSink hstep, sendAcquirePerm_chanD hstep] using hchanE j

theorem chanB_none_of_no_txn (n : Nat)
    (s : SymState HomeState NodeState n) (hchanB : chanBInv n s)
    (hcur : s.shared.currentTxn = none) :
    ∀ j : Fin n, (s.locals j).chanB = none := by
  intro j
  specialize hchanB j
  cases hB : (s.locals j).chanB with
  | none => exact rfl
  | some _ =>
      simp [hB] at hchanB
      rcases hchanB with ⟨_, hcurSome, _, _, _, _⟩
      rw [hcur] at hcurSome
      simp at hcurSome

theorem channelInv_preserved_recvAcquireBlock (n : Nat)
    (s s' : SymState HomeState NodeState n) (_hcore : coreInv n s) (hinv : channelInv n s)
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hstep : RecvAcquireBlockAtManager s s' i grow source) :
    channelInv n s' := by
  rcases hinv with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  rcases hstep with ⟨hcur, hgrant, hrel, hCnoneAll, _, _, _, _, _, _, rfl⟩
  have hBnone := chanB_none_of_no_txn n s hchanB hcur
  have hDdisj := chanD_noneOrAccessAck_of_pendingGrant_none n s hchanD hgrant hrel
  have hEnone := chanE_none_of_pendingGrant_none n s hchanE hgrant
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      have hAself :
          ((recvAcquireState s i .acquireBlock grow source).locals i).chanA = none := by
        simp [recvAcquireState, recvAcquireLocals]
      simp [hAself]
    · simpa [recvAcquireLocals, recvAcquireState, scheduleProbeLocals_chanA_other, hji,
        scheduleProbeLocals_pendingSource, scheduleProbeLocals_line] using hchanA j
  · intro j
    by_cases hmask : probeMaskForResult s i grow.result j.1 = true
    · have hmsg :
        ((recvAcquireState s i .acquireBlock grow source).locals j).chanB =
          some { opcode := probeOpcodeOfKind .acquireBlock
               , param := probeCapOfResult grow.result
               , source := source } := by
        simpa [recvAcquireState, recvAcquireLocals] using
          (scheduleProbeLocals_chanB_true s i j (probeMaskForResult s i grow.result)
            .acquireBlock grow.result source hmask)
      rw [hmsg]
      refine ⟨plannedTxn s i .acquireBlock grow source, ?_⟩
      refine ⟨by simp [recvAcquireState, recvAcquireShared, plannedTxn], ?_⟩
      refine ⟨by simp [plannedTxn], ?_⟩
      refine ⟨by simpa [plannedTxn] using hmask, ?_⟩
      refine ⟨by simp [plannedTxn], by simp [plannedTxn]⟩
    · have hnone :
        ((recvAcquireState s i .acquireBlock grow source).locals j).chanB = none := by
        have hfalse : probeMaskForResult s i grow.result j.1 = false := by
          cases hprobe : probeMaskForResult s i grow.result j.1 <;> simp_all
        by_cases hji : j = i
        · subst j
          simp [recvAcquireState, recvAcquireLocals, scheduleProbeLocals, hfalse, hBnone i]
        · simp [recvAcquireState, recvAcquireLocals, scheduleProbeLocals, hji, hfalse, hBnone j]
      rw [hnone]
      trivial
  · intro j
    have hnone : ((recvAcquireState s i .acquireBlock grow source).locals j).chanC = none := by
      simpa [recvAcquireState, recvAcquireLocals, scheduleProbeLocals_chanC] using hCnoneAll j
    rw [hnone]
    trivial
  · intro j
    rcases hDdisj j with hDnone | ⟨msg, hD, hacc, hps, hchanAnone⟩
    · have : ((recvAcquireState s i .acquireBlock grow source).locals j).chanD = none := by
        simpa [recvAcquireState, recvAcquireLocals, recvAcquireLocals_chanD] using hDnone
      rw [this]; trivial
    · have hD' : ((recvAcquireState s i .acquireBlock grow source).locals j).chanD = some msg := by
        simpa [recvAcquireState, recvAcquireLocals, recvAcquireLocals_chanD] using hD
      have hps' : ((recvAcquireState s i .acquireBlock grow source).locals j).pendingSource ≠ none := by
        simpa [recvAcquireState, recvAcquireLocals, scheduleProbeLocals_pendingSource] using hps
      have hchanAnone' : ((recvAcquireState s i .acquireBlock grow source).locals j).chanA = none := by
        by_cases hji : j = i
        · subst j; simp [recvAcquireState, recvAcquireLocals]
        · simpa [recvAcquireState, recvAcquireLocals, scheduleProbeLocals_chanA_other, hji] using hchanAnone
      rw [hD']; exact Or.inr (Or.inr ⟨hacc, hps', hchanAnone'⟩)
  · intro j
    have hnone : ((recvAcquireState s i .acquireBlock grow source).locals j).chanE = none := by
      simpa [recvAcquireState, recvAcquireLocals, recvAcquireLocals_chanE] using hEnone j
    rw [hnone]
    trivial

theorem channelInv_preserved_recvAcquirePerm (n : Nat)
    (s s' : SymState HomeState NodeState n) (_hcore : coreInv n s) (hinv : channelInv n s)
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hstep : RecvAcquirePermAtManager s s' i grow source) :
    channelInv n s' := by
  rcases hinv with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  rcases hstep with ⟨hcur, hgrant, hrel, hCnoneAll, _, _, _, _, _, _, rfl⟩
  have hBnone := chanB_none_of_no_txn n s hchanB hcur
  have hDdisj := chanD_noneOrAccessAck_of_pendingGrant_none n s hchanD hgrant hrel
  have hEnone := chanE_none_of_pendingGrant_none n s hchanE hgrant
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      have hAself :
          ((recvAcquireState s i .acquirePerm grow source).locals i).chanA = none := by
        simp [recvAcquireState, recvAcquireLocals]
      simp [hAself]
    · simpa [recvAcquireLocals, recvAcquireState, scheduleProbeLocals_chanA_other, hji,
        scheduleProbeLocals_pendingSource, scheduleProbeLocals_line] using hchanA j
  · intro j
    by_cases hmask : probeMaskForResult s i grow.result j.1 = true
    · have hmsg :
        ((recvAcquireState s i .acquirePerm grow source).locals j).chanB =
          some { opcode := probeOpcodeOfKind .acquirePerm
               , param := probeCapOfResult grow.result
               , source := source } := by
        simpa [recvAcquireState, recvAcquireLocals] using
          (scheduleProbeLocals_chanB_true s i j (probeMaskForResult s i grow.result)
            .acquirePerm grow.result source hmask)
      rw [hmsg]
      refine ⟨plannedTxn s i .acquirePerm grow source, ?_⟩
      refine ⟨by simp [recvAcquireState, recvAcquireShared, plannedTxn], ?_⟩
      refine ⟨by simp [plannedTxn], ?_⟩
      refine ⟨by simpa [plannedTxn] using hmask, ?_⟩
      refine ⟨by simp [plannedTxn], by simp [plannedTxn]⟩
    · have hnone :
        ((recvAcquireState s i .acquirePerm grow source).locals j).chanB = none := by
        have hfalse : probeMaskForResult s i grow.result j.1 = false := by
          cases hprobe : probeMaskForResult s i grow.result j.1 <;> simp_all
        by_cases hji : j = i
        · subst j
          simp [recvAcquireState, recvAcquireLocals, scheduleProbeLocals, hfalse, hBnone i]
        · simp [recvAcquireState, recvAcquireLocals, scheduleProbeLocals, hji, hfalse, hBnone j]
      rw [hnone]
      trivial
  · intro j
    have hnone : ((recvAcquireState s i .acquirePerm grow source).locals j).chanC = none := by
      simpa [recvAcquireState, recvAcquireLocals, scheduleProbeLocals_chanC] using hCnoneAll j
    rw [hnone]
    trivial
  · intro j
    rcases hDdisj j with hDnone | ⟨msg, hD, hacc, hps, hchanAnone⟩
    · have : ((recvAcquireState s i .acquirePerm grow source).locals j).chanD = none := by
        simpa [recvAcquireState, recvAcquireLocals, recvAcquireLocals_chanD] using hDnone
      rw [this]; trivial
    · have hD' : ((recvAcquireState s i .acquirePerm grow source).locals j).chanD = some msg := by
        simpa [recvAcquireState, recvAcquireLocals, recvAcquireLocals_chanD] using hD
      have hps' : ((recvAcquireState s i .acquirePerm grow source).locals j).pendingSource ≠ none := by
        simpa [recvAcquireState, recvAcquireLocals, scheduleProbeLocals_pendingSource] using hps
      have hchanAnone' : ((recvAcquireState s i .acquirePerm grow source).locals j).chanA = none := by
        by_cases hji : j = i
        · subst j; simp [recvAcquireState, recvAcquireLocals]
        · simpa [recvAcquireState, recvAcquireLocals, scheduleProbeLocals_chanA_other, hji] using hchanAnone
      rw [hD']; exact Or.inr (Or.inr ⟨hacc, hps', hchanAnone'⟩)
  · intro j
    have hnone : ((recvAcquireState s i .acquirePerm grow source).locals j).chanE = none := by
      simpa [recvAcquireState, recvAcquireLocals, recvAcquireLocals_chanE] using hEnone j
    rw [hnone]
    trivial

end TileLink.Messages
