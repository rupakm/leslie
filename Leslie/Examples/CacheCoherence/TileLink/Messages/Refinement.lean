import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.SimOther

namespace TileLink.Messages

open TLA TileLink SymShared Classical

/-! ### Forward-Simulation Invariant

    The forward-simulation theorem requires a stronger invariant than `refinementInv`
    to handle the sendGrant and recvGrantAck actions. We define `forwardSimInv` as the
    conjunction of all needed components. -/

/-- Combined invariant for the forward-simulation theorem. Includes:
    - `refinementInv` (fullInv + noDirtyInv + txnDataInv + cleanReleaseInv)
    - `cleanDataInv` (valid lines hold shared memory value)
    - `txnLineInv` (local lines match transaction snapshot)
    - `preLinesCleanInv` (pre-wave lines are clean)
    - `preLinesNoDirtyInv` (pre-wave lines not dirty)
    - `txnPlanInv` (transaction plan consistency) -/
def forwardSimInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  refinementInv n s ∧ dataCoherenceInv n s ∧ txnLineInv n s ∧
  preLinesCleanInv n s ∧ preLinesNoDirtyInv n s ∧ txnPlanInv n s

theorem init_forwardSimInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → forwardSimInv n s := by
  intro s hinit
  exact ⟨init_refinementInv n s hinit, init_dataCoherenceInv n s hinit,
    init_txnLineInv n s hinit, init_preLinesCleanInv n s hinit,
    init_preLinesNoDirtyInv n s hinit, init_txnPlanInv n s hinit⟩

-- The following preservation proofs are needed to close `forwardSimInv_preserved`.
-- `refinementInv_preserved`, `preLinesNoDirtyInv_preserved`, and `preLinesCleanInv_preserved`
-- are already proved in Preservation.lean. The remaining three are mechanical case analyses
-- over the 12 actions; their structure mirrors the existing preservation proofs.

theorem dataCoherenceInv_preserved (n : Nat) (s s' : SymState HomeState NodeState n)
    (hinv : forwardSimInv n s) (hnext : (tlMessages.toSpec n).next s s') :
    dataCoherenceInv n s' := by
  rcases hinv with ⟨⟨hfull, hdirtyEx, hSwmr, htxnData, hcleanC, _⟩, hdata, _, _, _, _⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  intro j hvalidJ hdirtyJ
  match a with
  | .sendAcquireBlock grow source =>
      -- lines/mem unchanged
      have hline := sendAcquireBlock_line (j := j) hstep
      rw [hline] at hvalidJ hdirtyJ
      have hmem : s'.shared.mem = s.shared.mem := by
        rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩; rw [hs']
      rw [hline, hmem]; exact hdata j hvalidJ hdirtyJ
  | .sendAcquirePerm grow source =>
      have hline := sendAcquirePerm_line (j := j) hstep
      rw [hline] at hvalidJ hdirtyJ
      have hmem : s'.shared.mem = s.shared.mem := by
        rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩; rw [hs']
      rw [hline, hmem]; exact hdata j hvalidJ hdirtyJ
  | .recvAcquireAtManager =>
      -- lines/mem unchanged
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, hs'⟩
        rcases hs' with ⟨_, hs'⟩
        rw [hs'] at hvalidJ hdirtyJ ⊢
        simp [recvAcquireState, recvAcquireLocals_line] at hvalidJ hdirtyJ ⊢
        exact hdata j hvalidJ hdirtyJ
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, hs'⟩
        rcases hs' with ⟨_, hs'⟩
        rw [hs'] at hvalidJ hdirtyJ ⊢
        simp [recvAcquireState, recvAcquireLocals_line] at hvalidJ hdirtyJ ⊢
        exact hdata j hvalidJ hdirtyJ
  | .recvProbeAtMaster =>
      -- recvProbe requires currentTxn = some tx. Post-state also has currentTxn = some.
      -- dataCoherenceInv has guard currentTxn = none, so it's vacuously true.
      rcases hstep with ⟨tx, _, hcur, _, _, _, _, _, _, _, _, hs'⟩
      intro htxn'
      rw [hs'] at htxn'; simp [recvProbeState] at htxn'; exact absurd hcur htxn'
  | .recvProbeAckAtManager =>
      -- recvProbeAck: node i clears chanC, lines unchanged for j≠i, line i unchanged.
      -- mem may change (if msg.data = some v). Under cleanChanCInv, msg.data = none → mem unchanged.
      rcases hstep with ⟨tx, msg, hcur, _, _, _, hC, _, _, hs'⟩
      have hmsgNone : msg.data = none := hcleanC i msg hC
      rw [hs'] at hvalidJ hdirtyJ ⊢
      by_cases hji : j = i
      · subst hji
        simp [recvProbeAckState, recvProbeAckLocals, recvProbeAckLocal, setFn] at hvalidJ hdirtyJ ⊢
        simp [recvProbeAckShared, hmsgNone]
        exact hdata j hvalidJ hdirtyJ
      · simp [recvProbeAckState, recvProbeAckLocals, setFn, hji] at hvalidJ hdirtyJ ⊢
        simp [recvProbeAckShared, hmsgNone]
        exact hdata j hvalidJ hdirtyJ
  | .sendGrantToRequester =>
      -- lines/mem unchanged
      rcases hstep with ⟨tx, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hvalidJ hdirtyJ ⊢
      simp [sendGrantState_line, sendGrantShared] at hvalidJ hdirtyJ ⊢
      exact hdata j hvalidJ hdirtyJ
  | .recvGrantAtMaster =>
      -- recvGrant requires currentTxn = some tx. Post-state has currentTxn = some.
      -- dataCoherenceInv has guard currentTxn = none, so it's vacuously true.
      rcases hstep with ⟨tx, _, hcur, _, _, _, _, _, _, _, _, hs'⟩
      intro htxn'
      rw [hs'] at htxn'; simp [recvGrantState, recvGrantShared] at htxn'; exact absurd hcur htxn'
  | .recvGrantAckAtManager =>
      -- lines/mem unchanged (only chanE cleared, currentTxn/pendingGrantAck cleared)
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hvalidJ hdirtyJ ⊢
      simp [recvGrantAckState_line, recvGrantAckShared] at hvalidJ hdirtyJ ⊢
      exact hdata j hvalidJ hdirtyJ
  | .sendRelease param =>
      -- releasedLine for j=i: dirty=false always. Need data = mem.
      -- If was dirty before, data = old dirty data ≠ mem. But sendRelease guard has dirty=false.
      -- So was NOT dirty. data was = mem (from dataCoherence pre). releasedLine preserves data.
      -- Mem unchanged. So preserved.
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hnotDirty, hvOrN, hs'⟩
      rw [hs'] at hvalidJ hdirtyJ ⊢
      by_cases hji : j = i
      · subst hji
        simp only [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, ite_true] at hvalidJ hdirtyJ ⊢
        -- Guard: dirty=false AND (valid=true ∨ result=.N)
        -- If result=.N → releasedLine=invalidatedLine → valid=false → contradiction
        -- If result≠.N → valid=true → dataCoherence gives data=mem → preserved
        -- sendReleaseShared = s.shared (mem unchanged)
        have hmem : (sendReleaseState s j param false).shared.mem = s.shared.mem := by
          simp [sendReleaseState]
        -- releasedLine preserves data; after simp, goal is about releasedLine
        cases hres : param.result with
        | N => -- releasedLine = invalidatedLine → valid = false → contradiction
          simp [releasedLine, invalidatedLine, hres] at hvalidJ
        | B => -- valid must be true (from guard: valid ∨ result=.N, and result=.B)
          have hvalid : (s.locals j).line.valid = true := by
            rcases hvOrN with h | h
            · exact h
            · rw [hres] at h; exact absurd h (by decide)
          unfold releasedLine at hvalidJ ⊢; simp [branchAfterProbe] at hvalidJ ⊢
          exact hdata j hvalid hnotDirty
        | T => -- valid must be true (from guard: valid ∨ result=.N, and result=.T)
          have hvalid : (s.locals j).line.valid = true := by
            rcases hvOrN with h | h
            · exact h
            · rw [hres] at h; exact absurd h (by decide)
          unfold releasedLine at hvalidJ ⊢; simp [tipAfterProbe] at hvalidJ ⊢
          exact hdata j hvalid hnotDirty
      · simp [sendReleaseState, sendReleaseLocals, setFn, hji] at hvalidJ hdirtyJ ⊢
        exact hdata j hvalidJ hdirtyJ
  | .sendReleaseData param =>
      -- After sendReleaseData, node i has releaseInFlight=true → excluded by dataCoherenceInv.
      -- For j≠i, lines/mem unchanged, releaseInFlight unchanged.
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      intro htxn' j hflight hvalidJ hdirtyJ
      rw [hs'] at htxn' hflight hvalidJ hdirtyJ ⊢
      simp only [sendReleaseState] at htxn' hflight hvalidJ hdirtyJ ⊢
      by_cases hji : j = i
      · subst j
        simp [sendReleaseLocals, sendReleaseLocal, setFn] at hflight
      · simp [sendReleaseLocals, sendReleaseLocal, setFn, hji] at hflight hvalidJ hdirtyJ ⊢
        exact hdata htxn j hflight hvalidJ hdirtyJ
  | .recvReleaseAtManager =>
      -- Lines unchanged for all nodes (only chanC/chanD changed).
      -- Mem may change (releaseWriteback). Under cleanChanCInv, msg.data = none → mem unchanged.
      rcases hstep with ⟨msg, param, _, _, _, _, hC, _, _, _, _, _, hs'⟩
      have hmsgNone := hcleanC i msg hC
      rw [hs'] at hvalidJ hdirtyJ ⊢
      by_cases hji : j = i
      · subst hji
        simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn] at hvalidJ hdirtyJ ⊢
        simp [recvReleaseShared, releaseWriteback, hmsgNone]
        exact hdata j hvalidJ hdirtyJ
      · simp [recvReleaseState, recvReleaseLocals, setFn, hji] at hvalidJ hdirtyJ ⊢
        simp [recvReleaseShared, releaseWriteback, hmsgNone]
        exact hdata j hvalidJ hdirtyJ
  | .recvReleaseAckAtMaster =>
      -- lines/mem unchanged
      rcases hstep with ⟨msg, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hvalidJ hdirtyJ ⊢
      by_cases hji : j = i
      · subst hji
        simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn,
              recvReleaseAckShared] at hvalidJ hdirtyJ ⊢
        exact hdata j hvalidJ hdirtyJ
      · simp [recvReleaseAckState, recvReleaseAckLocals, setFn, hji,
              recvReleaseAckShared] at hvalidJ hdirtyJ ⊢
        exact hdata j hvalidJ hdirtyJ
  | .store v =>
      -- Store: node i gets dirty=true, others unchanged. Mem unchanged.
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hvalidJ hdirtyJ ⊢
      by_cases hji : j = i
      · subst hji; simp [setFn, storeLocal] at hdirtyJ
      · simp [setFn, hji] at hvalidJ hdirtyJ ⊢
        exact hdata j hvalidJ hdirtyJ

theorem txnLineInv_preserved (n : Nat) (s s' : SymState HomeState NodeState n)
    (hinv : forwardSimInv n s) (hnext : (tlMessages.toSpec n).next s s') :
    txnLineInv n s' := by
  rcases hinv with ⟨⟨hfull, hnoDirty, _, _, _⟩, _, htxnLine, _, _, _⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp only [txnLineInv]
      match hcur : s.shared.currentTxn with
      | none => trivial
      | some tx =>
          rw [txnLineInv, hcur] at htxnLine
          intro j
          have hpre := htxnLine j
          by_cases hji : j = i
          · subst j; simp only [setFn, ite_true] at hpre ⊢
            simp only [txnSnapshotLine, probeSnapshotLine] at hpre ⊢; exact hpre
          · simp only [setFn, show (j = i) = False from propext ⟨hji, False.elim⟩, ite_false] at hpre ⊢
            exact hpre
  | .sendAcquirePerm grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp only [txnLineInv]
      match hcur : s.shared.currentTxn with
      | none => trivial
      | some tx =>
          rw [txnLineInv, hcur] at htxnLine
          intro j
          have hpre := htxnLine j
          by_cases hji : j = i
          · subst j; simp only [setFn, ite_true] at hpre ⊢
            simp only [txnSnapshotLine, probeSnapshotLine] at hpre ⊢; exact hpre
          · simp only [setFn, show (j = i) = False from propext ⟨hji, False.elim⟩, ite_false] at hpre ⊢
            exact hpre
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, htxnNone, _, _, hCnone, _, _, _, _, hrest⟩
        rcases hrest with ⟨_, hs'⟩
        rw [hs']
        simp only [txnLineInv, recvAcquireState, recvAcquireShared, recvAcquireLocals_line]
        intro j
        unfold txnSnapshotLine probeSnapshotLine plannedTxn
        have hCj := hCnone j
        have hlt := j.2
        by_cases hmask : probeMaskForResult s i grow.result j.1 = true
        · simp [hmask, hCj, hlt]
        · have hmaskF : probeMaskForResult s i grow.result j.1 = false := by
            cases h : probeMaskForResult s i grow.result j.1 <;> simp_all
          simp [hmaskF, hlt]
      · rcases hperm with ⟨grow, source, htxnNone, _, _, hCnone, _, _, _, hrest⟩
        rcases hrest with ⟨_, hs'⟩
        rw [hs']
        simp only [txnLineInv, recvAcquireState, recvAcquireShared, recvAcquireLocals_line]
        intro j
        unfold txnSnapshotLine probeSnapshotLine plannedTxn
        have hCj := hCnone j
        have hlt := j.2
        by_cases hmask : probeMaskForResult s i grow.result j.1 = true
        · simp [hmask, hCj, hlt]
        · have hmaskF : probeMaskForResult s i grow.result j.1 = false := by
            cases h : probeMaskForResult s i grow.result j.1 <;> simp_all
          simp [hmaskF, hlt]
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, hphase, hrem, _hA, _hB, _hsrc, _hop, hparam, hCnone, hs'⟩
      rw [hs']
      rw [txnLineInv, hcur] at htxnLine
      simp only [txnLineInv, recvProbeState, hcur]
      intro j
      by_cases hji : j = i
      · subst j
        simp only [recvProbeLocals, recvProbeLocal, setFn, ite_true]
        have hpre_i := htxnLine i
        have hnotGPA : ¬(tx.phase = .grantPendingAck ∧ tx.requester = i.1) := by
          intro ⟨h, _⟩; rw [hphase] at h; cases h
        simp only [txnSnapshotLine, hnotGPA, ite_false] at hpre_i ⊢
        rcases hfull with ⟨⟨_, _, _, htxnCore⟩, _, _⟩
        rcases (by simpa [txnCoreInv, hcur] using htxnCore :
            tx.requester < n ∧ _ ∧ _ ∧ _ ∧
            tx.probesNeeded tx.requester = false ∧
            (∀ k : Nat, tx.probesRemaining k = true → tx.probesNeeded k = true) ∧ _ ∧ _)
          with ⟨_, _, _, _, _, hsubset, _, _⟩
        have hneeded : tx.probesNeeded i.1 = true := hsubset i.1 hrem
        simp only [probeSnapshotLine, hneeded, ite_true, hrem, hCnone, and_self] at hpre_i
        simp only [probeSnapshotLine, hneeded, ite_true, hrem]
        simp only [show (some (probeAckMsg i (s.locals i).line) = none) = False from by simp, and_false, ite_false]
        rw [hpre_i, hparam]
      · simp only [recvProbeLocals, setFn, show (j = i) = False from propext ⟨hji, False.elim⟩, ite_false]
        exact htxnLine j
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, hphase, hrem, _hA, hC, _hsrc, _hwf, hs'⟩
      rw [hs']
      rw [txnLineInv, hcur] at htxnLine
      simp only [txnLineInv, recvProbeAckState, recvProbeAckShared, hcur]
      intro j
      by_cases hji : j = i
      · subst j
        simp only [recvProbeAckLocals, recvProbeAckLocal, setFn, ite_true]
        have hpre_i := htxnLine i
        have hnotGPA : ¬(tx.phase = .grantPendingAck ∧ tx.requester = i.1) := by
          intro ⟨h, _⟩; rw [hphase] at h; cases h
        simp only [txnSnapshotLine, hnotGPA, ite_false] at hpre_i ⊢
        rcases hfull with ⟨⟨_, _, _, htxnCore⟩, _, _⟩
        rcases (by simpa [txnCoreInv, hcur] using htxnCore :
            tx.requester < n ∧ _ ∧ _ ∧ _ ∧
            tx.probesNeeded tx.requester = false ∧
            (∀ k : Nat, tx.probesRemaining k = true → tx.probesNeeded k = true) ∧ _ ∧ _)
          with ⟨_, _, _, _, _, hsubset, _, _⟩
        have hneeded : tx.probesNeeded i.1 = true := hsubset i.1 hrem
        have hnotGPA' : ¬((probeAckPhase (n := n) (clearProbeIdx tx.probesRemaining i.1)) = .grantPendingAck ∧
            tx.requester = i.1) := by
          intro ⟨h, _⟩; simp [probeAckPhase] at h; split at h <;> cases h
        simp only [hnotGPA', ite_false]
        simp only [probeSnapshotLine, hneeded, ite_true] at hpre_i ⊢
        simp only [hC, hrem, show (some msg = none) = False from by simp, and_false, ite_false] at hpre_i
        simp only [clearProbeIdx, show i.1 = i.1 from rfl, ite_true, show (false = true) = False from by simp,
          false_and, ite_false]
        exact hpre_i
      · simp only [recvProbeAckLocals, setFn, show (j = i) = False from propext ⟨hji, False.elim⟩, ite_false]
        have hpre_j := htxnLine j
        have hnotGPA : ¬(tx.phase = .grantPendingAck ∧ tx.requester = j.1) := by
          intro ⟨h, _⟩; rw [hphase] at h; cases h
        have hnotGPA' : ¬((probeAckPhase (n := n) (clearProbeIdx tx.probesRemaining i.1)) = .grantPendingAck ∧
            tx.requester = j.1) := by
          intro ⟨h, _⟩; simp [probeAckPhase] at h; split at h <;> cases h
        simp only [txnSnapshotLine, hnotGPA, hnotGPA', ite_false] at hpre_j ⊢
        simp only [probeSnapshotLine] at hpre_j ⊢
        have hne : i.1 ≠ j.1 := by intro h; exact hji (Fin.ext_iff.mpr h.symm)
        simp only [clearProbeIdx, show (j.1 = i.1) = False from propext ⟨fun h => hne h.symm, False.elim⟩, ite_false]
        exact hpre_j
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, hreq, hphase, _, _, _hD, hE, _hSink, hs'⟩
      rw [hs']
      rw [txnLineInv, hcur] at htxnLine
      simp only [txnLineInv, sendGrantState, sendGrantShared, hcur]
      intro j
      have hpre_j := htxnLine j
      by_cases hji : j = i
      · subst j
        simp only [sendGrantLocals, setFn, ite_true, sendGrantLocal]
        simp only [txnSnapshotLine, show TxnPhase.grantPendingAck = TxnPhase.grantPendingAck from rfl,
          true_and, hreq, ite_true, hE]
        have hnotGPA : ¬(tx.phase = .grantPendingAck ∧ tx.requester = i.1) := by
          intro ⟨h, _⟩; rw [hphase] at h; cases h
        simp only [txnSnapshotLine, hnotGPA, ite_false] at hpre_j
        rcases hfull with ⟨⟨_, _, _, htxnCore⟩, _, _⟩
        rcases (by simpa [txnCoreInv, hcur] using htxnCore :
            tx.requester < n ∧ _ ∧ _ ∧ _ ∧
            tx.probesNeeded tx.requester = false ∧ _ ∧ _ ∧ _)
          with ⟨_, _, _, _, hnoProbeReq, _, _, _⟩
        rw [hreq] at hnoProbeReq
        simp only [probeSnapshotLine, hnoProbeReq, ite_false] at hpre_j
        exact hpre_j
      · simp only [sendGrantLocals, setFn, show (j = i) = False from propext ⟨hji, False.elim⟩, ite_false]
        have hreq_ne : ¬(tx.requester = j.1) := by
          intro h; apply hji; exact Fin.ext_iff.mpr (by rw [← hreq]; exact h.symm)
        -- Post txn has phase = grantPendingAck, but requester ≠ j → probeSnapshotLine
        simp only [txnSnapshotLine]
        simp only [show TxnPhase.grantPendingAck = TxnPhase.grantPendingAck from rfl, true_and,
          hreq_ne, ite_false]
        -- Pre: phase = grantReady → also probeSnapshotLine (with original tx)
        have hnotGPA : ¬(tx.phase = .grantPendingAck ∧ tx.requester = j.1) := by
          intro ⟨h, _⟩; rw [hphase] at h; cases h
        simp only [txnSnapshotLine, hnotGPA, ite_false] at hpre_j
        -- probeSnapshotLine doesn't use phase, so both are equal
        simp only [probeSnapshotLine] at hpre_j ⊢
        exact hpre_j
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, hreq, hphase, _, _hA, _hD, hE, _hSink, _hmsg, hs'⟩
      rw [hs']
      rw [txnLineInv, hcur] at htxnLine
      simp only [txnLineInv, recvGrantState, recvGrantShared, hcur]
      intro j
      have hpre_j := htxnLine j
      by_cases hji : j = i
      · subst j
        simp only [recvGrantLocals, recvGrantLocal, setFn, ite_true]
        simp only [txnSnapshotLine, show TxnPhase.grantPendingAck = TxnPhase.grantPendingAck from rfl,
          true_and, hreq, ite_true, hphase]
        simp only [show (some ({ sink := tx.sink } : EMsg) = none) = False from by simp, ite_false]
        simp only [txnSnapshotLine, show TxnPhase.grantPendingAck = TxnPhase.grantPendingAck from rfl,
          true_and, hreq, ite_true, hphase, hE, ite_true] at hpre_j
        rw [hpre_j]
      · simp only [recvGrantLocals, setFn, show (j = i) = False from propext ⟨hji, False.elim⟩, ite_false]
        have hreq_ne : ¬(tx.requester = j.1) := by
          intro h; apply hji; exact Fin.ext_iff.mpr (by rw [← hreq]; exact h.symm)
        simp only [txnSnapshotLine, show ¬(TxnPhase.grantPendingAck = TxnPhase.grantPendingAck ∧ tx.requester = j.1) from
          fun ⟨_, h⟩ => hreq_ne h, ite_false] at hpre_j ⊢
        exact hpre_j
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, recvGrantAckState, recvGrantAckShared]
  | .sendRelease param =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur, sendReleaseState]
  | .sendReleaseData param =>
      -- currentTxn = none → txnLineInv trivially True
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur, sendReleaseState]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur, recvReleaseAckState, recvReleaseAckShared]
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur]

private theorem writableProbeMask_eq_snapshotWritableProbeMask {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) (kind : ReqKind)
    (grow : GrowParam) (source : SourceId) :
    writableProbeMask s i =
      snapshotWritableProbeMask n (plannedTxn s i kind grow source) := by
  funext k
  by_cases hk : k < n
  · simp [writableProbeMask, snapshotWritableProbeMask, plannedTxn, hk, Fin.ext_iff]
  · simp [writableProbeMask, snapshotWritableProbeMask, hk]

private theorem cachedProbeMask_eq_snapshotCachedProbeMask {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) (kind : ReqKind)
    (grow : GrowParam) (source : SourceId) :
    cachedProbeMask s i =
      snapshotCachedProbeMask n (plannedTxn s i kind grow source) := by
  funext k
  by_cases hk : k < n
  · simp [cachedProbeMask, snapshotCachedProbeMask, plannedTxn, hk, Fin.ext_iff]
  · simp [cachedProbeMask, snapshotCachedProbeMask, hk]

private theorem hasCachedOther_iff_snapshotHasCachedOther {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) (kind : ReqKind)
    (grow : GrowParam) (source : SourceId) :
    hasCachedOther s i ↔
      snapshotHasCachedOther n (plannedTxn s i kind grow source) := by
  constructor
  · rintro ⟨j, hne, hperm⟩
    have hne' : j.1 ≠ i.1 := Fin.val_ne_of_ne hne
    exact ⟨j, hne', by simp [plannedTxn, j.is_lt, hperm]⟩
  · rintro ⟨j, hne, hperm⟩
    have hne' : j ≠ i := fun h => hne (congrArg Fin.val h)
    exact ⟨j, hne', by simpa [plannedTxn, j.is_lt] using hperm⟩

private theorem allOthersInvalid_iff_snapshotAllOthersInvalid {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) (kind : ReqKind)
    (grow : GrowParam) (source : SourceId) :
    allOthersInvalid s i ↔
      snapshotAllOthersInvalid n (plannedTxn s i kind grow source) := by
  constructor
  · intro h j hne
    have hne' : j ≠ i := fun heq => hne (congrArg Fin.val heq)
    simp [plannedTxn, j.is_lt, h j hne']
  · intro h j hne
    have hne' : j.1 ≠ i.1 := Fin.val_ne_of_ne hne
    simpa [plannedTxn, j.is_lt] using h j hne'

theorem txnPlanInv_preserved (n : Nat) (s s' : SymState HomeState NodeState n)
    (hinv : forwardSimInv n s) (hnext : (tlMessages.toSpec n).next s s') :
    txnPlanInv n s' := by
  rcases hinv with ⟨⟨hfull, hnoDirty, _, _, _⟩, _, _, _, _, hplan⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [txnPlanInv] using hplan
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [txnPlanInv] using hplan
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · -- RecvAcquireBlockAtManager
        rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, hcases, hrest⟩
        rcases hrest with ⟨_, hs'⟩
        rw [hs']
        simp only [txnPlanInv, recvAcquireState, recvAcquireShared, plannedTxn]
        refine ⟨i.is_lt, trivial, ?_, ?_⟩
        · -- resultPerm = .B → snapshotHasCachedOther ∧ probesNeeded = snapshotWritableProbeMask
          intro hresB
          rcases hcases with ⟨hdirtyOther, hresult⟩ | ⟨_, hcached, hresult⟩ | ⟨_, hresult⟩
          · -- dirty case: hasDirtyOther → hasCachedOther (via lineWF: dirty→perm=.T→perm≠.N)
            rw [hresult] at hresB ⊢
            rcases hdirtyOther with ⟨j, hne, hdirty⟩
            rcases hfull with ⟨⟨hlineWF, _⟩, _, _⟩
            have hpermT := (hlineWF j).1 hdirty
            have hcached : hasCachedOther s i :=
              ⟨j, hne, by rw [hpermT.1]; exact TLPerm.noConfusion⟩
            exact ⟨(hasCachedOther_iff_snapshotHasCachedOther s i .acquireBlock grow source).mp hcached,
              by simp [probeMaskForResult];
                 exact writableProbeMask_eq_snapshotWritableProbeMask s i .acquireBlock grow source⟩
          · rw [hresult] at hresB ⊢
            exact ⟨(hasCachedOther_iff_snapshotHasCachedOther s i .acquireBlock grow source).mp hcached,
              by simp [probeMaskForResult];
                 exact writableProbeMask_eq_snapshotWritableProbeMask s i .acquireBlock grow source⟩
          · rw [hresult] at hresB; cases hresB
        · -- resultPerm = .T → snapshotAllOthersInvalid ∧ probesNeeded = noProbeMask
          intro hresT
          rcases hcases with ⟨_, hresult⟩ | ⟨_, _, hresult⟩ | ⟨hallInv, hresult⟩
          · rw [hresult] at hresT; cases hresT
          · rw [hresult] at hresT; cases hresT
          · rw [hresult] at hresT ⊢
            constructor
            · exact (allOthersInvalid_iff_snapshotAllOthersInvalid s i .acquireBlock grow source).mp hallInv
            · simp [probeMaskForResult]
              rw [cachedProbeMask_eq_noProbeMask_of_allOthersInvalid hallInv]
              rfl
      · -- RecvAcquirePermAtManager
        rcases hperm with ⟨grow, source, _, _, _, _, _, hgrowLegal, hresT, hrest⟩
        rcases hrest with ⟨_, hs'⟩
        rw [hs']
        simp only [txnPlanInv, recvAcquireState, recvAcquireShared, plannedTxn]
        refine ⟨i.is_lt, trivial, hresT, ?_, ?_⟩
        · -- probesNeeded = snapshotCachedProbeMask
          rw [hresT]; simp [probeMaskForResult]
          exact cachedProbeMask_eq_snapshotCachedProbeMask s i .acquirePerm grow source
        · -- (preLines requester).perm ≠ .T
          simp [i.is_lt]
          rw [GrowParam.legalFrom] at hgrowLegal
          rw [hgrowLegal]
          cases grow <;> simp [GrowParam.source, GrowParam.result] at hresT ⊢
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, hs'⟩
      rcases hs' with ⟨_, hs'⟩
      rw [hs']
      simpa [txnPlanInv, hcur, recvProbeState] using hplan
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp only [txnPlanInv, recvProbeAckState, recvProbeAckShared]
      simp only [txnPlanInv, hcur] at hplan
      exact hplan
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp only [txnPlanInv, sendGrantState, sendGrantShared]
      simp only [txnPlanInv, hcur] at hplan
      exact hplan
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp only [txnPlanInv, recvGrantState, recvGrantShared, hcur]
      simp only [txnPlanInv, hcur] at hplan
      exact hplan
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnPlanInv, recvGrantAckState, recvGrantAckShared]
  | .sendRelease param =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      rw [hs']
      simp [txnPlanInv, hcur, sendReleaseState]
  | .sendReleaseData param =>
      -- currentTxn = none → txnPlanInv trivially True
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnPlanInv, hcur, sendReleaseState]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnPlanInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnPlanInv, hcur, recvReleaseAckState, recvReleaseAckShared]
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnPlanInv, hcur]

theorem forwardSimInv_preserved (n : Nat) (s s' : SymState HomeState NodeState n)
    (hinv : forwardSimInv n s) (hnext : (tlMessages.toSpec n).next s s') :
    forwardSimInv n s' := by
  rcases hinv with ⟨hrefInv, hdata, htxnLine, hpreClean, hpreNoDirty, hplan⟩
  rcases hrefInv with ⟨hfull, hdirtyEx, hSwmr, htxnData, hcleanRel, hrelUniq⟩
  refine ⟨refinementInv_preserved n s s' ⟨⟨hfull, hdirtyEx, hSwmr, htxnData, hcleanRel, hrelUniq⟩, htxnLine, hpreClean, hpreNoDirty, hplan⟩ hnext,
    dataCoherenceInv_preserved n s s' ⟨⟨hfull, hdirtyEx, hSwmr, htxnData, hcleanRel, hrelUniq⟩, hdata, htxnLine, hpreClean, hpreNoDirty, hplan⟩ hnext,
    txnLineInv_preserved n s s' ⟨⟨hfull, hdirtyEx, hSwmr, htxnData, hcleanRel, hrelUniq⟩, hdata, htxnLine, hpreClean, hpreNoDirty, hplan⟩ hnext,
    ?_, ?_, ?_⟩
  · exact preLinesCleanInv_preserved n s s' hfull hdata hpreClean hcleanRel hpreNoDirty hnext
  · exact preLinesNoDirtyInv_preserved n s s' hdirtyEx hpreNoDirty hnext
  · exact txnPlanInv_preserved n s s'
      ⟨⟨hfull, hdirtyEx, hSwmr, htxnData, hcleanRel, hrelUniq⟩, hdata, htxnLine, hpreClean, hpreNoDirty, hplan⟩
      hnext

theorem refinement_inv_invariant (n : Nat) :
    pred_implies (tlMessages.toSpec n).safety [tlafml| □ ⌜ refinementInv n ⌝] := by
  have h : pred_implies (tlMessages.toSpec n).safety [tlafml| □ ⌜ forwardSimInv n ⌝] := by
    apply init_invariant
    · intro s hinit; exact init_forwardSimInv n s hinit
    · intro s s' hnext hinv; exact forwardSimInv_preserved n s s' hinv hnext
  intro σ hsafe k
  exact (h σ hsafe k).1

/-! ### Forward-Simulation Dispatch

    For each message-level action, we prove that either:
    - the refMap is unchanged (stuttering), or
    - there exists an atomic-level action that transforms refMap(s) to refMap(s')

    Actions that require additional hypotheses (like `hCother` for recvReleaseAtManager
    and `hCnone` for recvReleaseAckAtMaster) derive them from the forwardSimInv. -/

-- Helper: when pendingReleaseAck = some i.1 and currentTxn = none,
-- all chanC are none (the release has already been consumed by the manager).
-- This follows from chanDInv (releaseAck on D implies chanC = none for that node)
-- and the single-release-in-flight constraint.
private theorem chanC_none_of_releaseAck_pending {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (hrelUniq : releaseUniqueInv n s) (htxn : s.shared.currentTxn = none)
    (hrel : s.shared.pendingReleaseAck = some i.1) :
    ∀ j : Fin n, (s.locals j).chanC = none :=
  (hrelUniq htxn).1 (by rw [hrel]; simp)

theorem forwardSim_step (n : Nat) (s s' : SymState HomeState NodeState n)
    (hinv : forwardSimInv n s) (hnext : (tlMessages.toSpec n).next s s') :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') ∨
    refMap n s = refMap n s' := by
  rcases hinv with ⟨⟨hfull, hnoDirty, hSwmr, htxnData, hcleanRel, hrelUniq⟩, hclean, htxnLine, _, hpreNoDirty, hplan⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock grow source =>
      right; exact (refMap_sendAcquireBlock_eq hstep).symm
  | .sendAcquirePerm grow source =>
      right; exact (refMap_sendAcquirePerm_eq hstep).symm
  | .recvAcquireAtManager =>
      left; exact refMap_recvAcquireAtManager_next ⟨hfull, hnoDirty, hSwmr, htxnData, hcleanRel, hrelUniq⟩ hstep
  | .recvProbeAtMaster =>
      right; exact (refMap_recvProbeAtMaster_eq hstep).symm
  | .recvProbeAckAtManager =>
      right; exact (refMap_recvProbeAckAtManager_eq hfull htxnData hpreNoDirty hstep).symm
  | .sendGrantToRequester =>
      left
      rcases hstep with ⟨tx, hcur, hreq, hphase, hgrant, hrel, hD, hE, hSink, hs'⟩
      have hstep' : SendGrantToRequester s s' i := ⟨tx, hcur, hreq, hphase, hgrant, hrel, hD, hE, hSink, hs'⟩
      cases htx : tx.kind with
      | acquireBlock =>
          cases hperm : tx.resultPerm with
          | N => -- acquireBlock can't produce N; resultPerm = grow.result ≠ N
              have ⟨⟨_, _, _, htxnCore⟩, _, _⟩ := hfull
              unfold txnCoreInv at htxnCore; rw [hcur] at htxnCore
              rcases htxnCore with ⟨_, _, hresultEq, _⟩
              rw [hperm] at hresultEq; revert hresultEq
              cases tx.grow <;> simp [GrowParam.result]
          | B => -- SORRY: refMap_sendGrant_block_branch_next requires cleanDataInv
                 -- (∀ i, data = mem), which is stronger than the available dataCoherenceInv.
                 -- At grant-ready time with all probes done and preLinesNoDirtyInv, the
                 -- argument is: (1) all preLines are clean, so usedDirtySource=false and
                 -- mem is unchanged since plan time, (2) preLinesCleanInv gives valid clean
                 -- preLines data = mem, (3) probedLine preserves data. But cleanDataInv also
                 -- covers INVALID nodes, whose data = preLines data may not equal mem if the
                 -- node was invalid at plan time with stale data. Closing this requires either
                 -- strengthening the init/store invariant to track all node data = mem, or
                 -- weakening the atomic model's finishGrant postcondition for invalid nodes.
                 sorry
          | T => exact refMap_sendGrant_block_tip_next hfull htxnLine htxnData hplan hstep' hcur htx hperm
      | acquirePerm =>
          exact refMap_sendGrant_acquirePerm_next hfull hpreNoDirty htxnLine htxnData hplan hstep' hcur htx
  | .recvGrantAtMaster =>
      right; exact (refMap_recvGrantAtMaster_eq hstep).symm
  | .recvGrantAckAtManager =>
      left; exact refMap_recvGrantAckAtManager_next hfull htxnLine hstep
  | .sendRelease param =>
      left; exact refMap_sendRelease_next hfull hstep
  | .sendReleaseData param =>
      left; exact refMap_sendReleaseData_next hfull hstep
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, htxn, hgrant, hrel, hflight, hC, hsource, hwf, hparam, hperm, hD, hs'⟩
      have hstep' : RecvReleaseAtManager s s' i := ⟨msg, param, htxn, hgrant, hrel, hflight, hC, hsource, hwf, hparam, hperm, hD, hs'⟩
      -- Derive hCother: with currentTxn = none, other nodes' chanC must be none
      -- (probe case needs currentTxn = some; release case is the only option but
      -- the single-line model has at most one release in flight)
      have hCother : ∀ j : Fin n, j ≠ i → (s.locals j).chanC = none := by
        intro j hne
        exact (hrelUniq htxn).2 i j (Ne.symm hne) (by rw [hC]; simp)
      right; exact (refMap_recvReleaseAtManager_eq hfull hcleanRel hCother hstep').symm
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, htxn, hgrant, hrel, hflight, hD, hmsg, hs'⟩
      have hstep' : RecvReleaseAckAtMaster s s' i := ⟨msg, htxn, hgrant, hrel, hflight, hD, hmsg, hs'⟩
      have hCnone : ∀ j : Fin n, (s.locals j).chanC = none :=
        chanC_none_of_releaseAck_pending hrelUniq htxn hrel
      left; exact refMap_recvReleaseAckAtMaster_next hfull hCnone hstep'
  | .store v =>
      rcases hstep with ⟨hcur, hgrant, hrel, hallC, hperm, hA, hB, hCi, hD, hE, hSrc, hFlight, hs'⟩
      rw [hs']
      left
      simp only [SymSharedSpec.toSpec, TileLink.Atomic.tlAtomic]
      refine ⟨i, .store v, ?_⟩
      have hqueuedNone : queuedReleaseIdx n s = none :=
        queuedReleaseIdx_eq_none_of_all_chanC_none s hallC
      let s'store : SymState HomeState NodeState n :=
        { shared := s.shared, locals := setFn s.locals i (storeLocal (s.locals i) v) }
      have hqueuedPost : queuedReleaseIdx n s'store = none := by
        apply queuedReleaseIdx_eq_none_of_all_chanC_none
        intro j
        show (s'store.locals j).chanC = none
        by_cases hji : j = i
        · subst j; simp [s'store, setFn, storeLocal, hCi]
        · simp [s'store, setFn, hji]; exact hallC j
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- pendingGrantMeta = none
        simp [refMap, refMapShared, hcur]
      · -- pendingGrantAck = none
        simp [refMap, refMapShared, hcur, hrel, hqueuedNone, hgrant]
      · -- pendingReleaseAck = none
        simp [refMap, refMapShared, hcur, hrel, hqueuedNone]
      · -- perm = .T
        simpa [refMap, refMapLine, hcur] using hperm
      · -- postcondition
        apply SymState.ext
        · -- shared: refMapShared unchanged (store preserves perm = .T so syncDir same)
          show refMapShared n s'store = (refMap n s).shared
          simp only [refMapShared, hcur, refMap, hrel, s'store]
          rw [TileLink.Atomic.HomeState.mk.injEq]
          refine ⟨rfl, ?_, rfl, ?_, ?_⟩
          · -- dir: syncDir unchanged because perm .T → .T at i, others unchanged
            funext k
            by_cases hk : k < n
            · simp only [TileLink.Atomic.syncDir, hk, dite_true]
              by_cases hki : (⟨k, hk⟩ : Fin n) = i
              · subst hki; simp [setFn, storeLocal, hperm]
              · simp [setFn, hki]
            · simp [TileLink.Atomic.syncDir, hk]
          · -- pendingGrantAck
            simp [hgrant, hqueuedNone, hqueuedPost]
          · -- pendingReleaseAck: queuedReleaseIdx unchanged
            rw [hqueuedNone]; exact hqueuedPost
        · -- locals: refMapLine at each index
          funext j
          simp only [refMap, refMapLine, hcur, setFn]
          by_cases hji : j = i
          · subst j; simp [storeLocal, TileLink.Atomic.dirtyTipLine]
          · simp [hji]

/-! ### Main Forward-Simulation Theorem -/

/-- The explicit message-level TileLink model refines the atomic wave-level model
    (with stuttering). Every behavior of the message model, mapped through `refMap`,
    is a behavior of the atomic model. -/
theorem messages_refines_atomic (n : Nat) :
    refines_via (refMap n) (tlMessages.toSpec n).safety
      (TileLink.Atomic.tlAtomic.toSpec n).safety_stutter := by
  apply refinement_mapping_stutter_with_invariant
  · intro s hinit; exact init_forwardSimInv n s hinit
  · intro s s' hinv hnext; exact forwardSimInv_preserved n s s' hinv hnext
  · intro s hinit; exact refMap_init n s hinit
  · intro s s' hinv hnext
    rcases forwardSim_step n s s' hinv hnext with hstep | heq
    · exact Or.inl hstep
    · exact Or.inr heq

end TileLink.Messages
