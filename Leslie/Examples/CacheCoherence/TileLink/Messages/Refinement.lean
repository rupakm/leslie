import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.SimOther

namespace TileLink.Messages

open TLA TileLink SymShared Classical

theorem refinement_inv_invariant (n : Nat) :
    pred_implies (tlMessages.toSpec n).safety [tlafml| □ ⌜ refinementInv n ⌝] := by
  apply init_invariant
  · intro s hinit
    exact init_refinementInv n s hinit
  · intro s s' hnext hinv
    exact refinementInv_preserved n s s' hinv hnext

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
  refinementInv n s ∧ cleanDataInv n s ∧ txnLineInv n s ∧
  preLinesCleanInv n s ∧ preLinesNoDirtyInv n s ∧ txnPlanInv n s

theorem init_forwardSimInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → forwardSimInv n s := by
  intro s hinit
  exact ⟨init_refinementInv n s hinit, init_cleanDataInv n s hinit,
    init_txnLineInv n s hinit, init_preLinesCleanInv n s hinit,
    init_preLinesNoDirtyInv n s hinit, init_txnPlanInv n s hinit⟩

-- The following preservation proofs are needed to close `forwardSimInv_preserved`.
-- `refinementInv_preserved`, `preLinesNoDirtyInv_preserved`, and `preLinesCleanInv_preserved`
-- are already proved in Preservation.lean. The remaining three are mechanical case analyses
-- over the 12 actions; their structure mirrors the existing preservation proofs.

theorem cleanDataInv_preserved (n : Nat) (s s' : SymState HomeState NodeState n)
    (hinv : forwardSimInv n s) (hnext : (tlMessages.toSpec n).next s s') :
    cleanDataInv n s' := by
  rcases hinv with ⟨⟨_, hnoDirty, htxnData, hcleanRel, _⟩, hclean, _, _, _, _⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock grow source =>
      intro j
      rw [sendAcquireBlock_line hstep, sendAcquireBlock_shared hstep]
      exact hclean j
  | .sendAcquirePerm grow source =>
      intro j
      rw [sendAcquirePerm_line hstep, sendAcquirePerm_shared hstep]
      exact hclean j
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, _, hs'⟩
        rcases hs' with ⟨_, hs'⟩
        intro j
        rw [hs']
        simp only [recvAcquireState, recvAcquireLocals_line, recvAcquireShared_mem]
        exact hclean j
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, _, hs'⟩
        rcases hs' with ⟨_, hs'⟩
        intro j
        rw [hs']
        simp only [recvAcquireState, recvAcquireLocals_line, recvAcquireShared_mem]
        exact hclean j
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩
      rcases hs' with ⟨_, hs'⟩
      intro j
      rw [hs']
      simp only [recvProbeState]
      by_cases hji : j = i
      · subst j
        simp only [recvProbeLocals, setFn, ite_true, recvProbeLocal]
        -- line = probedLine (s.locals i).line msg.param
        -- probedLine preserves data for all caps
        cases msg.param <;>
          simp [probedLine, invalidatedLine, branchAfterProbe, tipAfterProbe]
        all_goals exact hclean i
      · simp only [recvProbeLocals, setFn, show (j = i) = False from propext ⟨hji, False.elim⟩,
            ite_false]
        exact hclean j
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, hs'⟩
      intro j
      rw [hs']
      by_cases hji : j = i
      · subst j
        simpa [recvProbeAckState, recvProbeAckLocals, recvProbeAckShared, setFn]
          using hclean i
      · simpa [recvProbeAckState, recvProbeAckLocals, recvProbeAckShared, setFn, hji]
          using hclean j
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, _, _, _, _, _, _, _, _, hs'⟩
      intro j
      rw [hs']
      by_cases hji : j = i
      · subst j
        simpa [sendGrantState, sendGrantLocals, sendGrantShared, setFn]
          using hclean i
      · simpa [sendGrantState, sendGrantLocals, sendGrantShared, setFn, hji]
          using hclean j
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩
      intro j
      rw [hs']
      by_cases hji : j = i
      · subst j
        simp only [recvGrantState, recvGrantLocals, recvGrantLocal, recvGrantShared, setFn,
            ite_true]
        by_cases hdata : tx.grantHasData
        · -- grantHasData = true: line.data = tx.transferVal or preserved
          have htransfer := (txnDataInv_currentTxn htxnData hcur).2
          cases hperm : tx.resultPerm <;>
            simp [grantLine, hdata, hperm, invalidatedLine]
          -- N: invalidatedLine preserves data
          · exact hclean i
          -- B: data = tx.transferVal = mem
          · exact htransfer
          -- T: data = tx.transferVal = mem
          · exact htransfer
        · -- grantHasData = false: data preserved from pre-state
          simp [grantLine, hdata]
          exact hclean i
      · simpa [recvGrantState, recvGrantLocals, recvGrantShared, setFn, hji]
          using hclean j
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩
      intro j
      rw [hs']
      rw [show ((recvGrantAckState s i).locals j).line = (s.locals j).line from
        recvGrantAckState_line s i j]
      rw [show (recvGrantAckState s i).shared.mem = s.shared.mem from by
        simp [recvGrantAckState, recvGrantAckShared]]
      exact hclean j
  | .sendRelease param =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      intro j
      rw [hs']
      simp only [sendReleaseState]
      by_cases hji : j = i
      · subst j
        simp only [sendReleaseLocals, sendReleaseLocal, setFn, ite_true]
        -- releasedLine preserves data
        cases param.result <;>
          simp [releasedLine, invalidatedLine, branchAfterProbe, tipAfterProbe]
        all_goals exact hclean i
      · simp only [sendReleaseLocals, setFn, show (j = i) = False from propext ⟨hji, False.elim⟩,
            ite_false]
        exact hclean j
  | .sendReleaseData param =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hdirty, _hs'⟩
      exfalso
      rw [hnoDirty i] at hdirty
      contradiction
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, _, _, _, _, hC, _, hwf, _, _, _, hs'⟩
      intro j
      rw [hs']
      have hmsgClean : msg.data = none := hcleanRel i msg hC hwf
      rw [show ((recvReleaseState s i msg param).locals j).line = (s.locals j).line from
        recvReleaseState_line s i j msg param]
      rw [show (recvReleaseState s i msg param).shared.mem = s.shared.mem from by
        simp [recvReleaseState, recvReleaseShared, releaseWriteback, hmsgClean]]
      exact hclean j
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, _, _, _, _, _, _, hs'⟩
      intro j
      rw [hs']
      rw [show ((recvReleaseAckState s i).locals j).line = (s.locals j).line from
        recvReleaseAckState_line s i j]
      rw [show (recvReleaseAckState s i).shared.mem = s.shared.mem from by
        simp [recvReleaseAckState, recvReleaseAckShared]]
      exact hclean j

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
      · rcases hblk with ⟨grow, source, htxnNone, _, _, hCnone, _, _, _, _, _, hrest⟩
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
      · rcases hperm with ⟨grow, source, htxnNone, _, _, hCnone, _, _, _, _, hrest⟩
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
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hdirty, _⟩
      exfalso; rw [hnoDirty i] at hdirty; contradiction
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur, recvReleaseAckState, recvReleaseAckShared]

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
        rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, hndirty, hcases, hrest⟩
        rcases hrest with ⟨_, hs'⟩
        rw [hs']
        simp only [txnPlanInv, recvAcquireState, recvAcquireShared, plannedTxn]
        refine ⟨i.is_lt, trivial, ?_, ?_⟩
        · -- resultPerm = .B → snapshotHasCachedOther ∧ probesNeeded = snapshotWritableProbeMask
          intro hresB
          rcases hcases with ⟨hcached, hresult⟩ | ⟨_, hresult⟩
          · rw [hresult] at hresB ⊢
            exact ⟨(hasCachedOther_iff_snapshotHasCachedOther s i .acquireBlock grow source).mp hcached,
              by simp [probeMaskForResult];
                 exact writableProbeMask_eq_snapshotWritableProbeMask s i .acquireBlock grow source⟩
          · rw [hresult] at hresB; cases hresB
        · -- resultPerm = .T → snapshotAllOthersInvalid ∧ probesNeeded = noProbeMask
          intro hresT
          rcases hcases with ⟨_, hresult⟩ | ⟨hallInv, hresult⟩
          · rw [hresult] at hresT; cases hresT
          · rw [hresult] at hresT ⊢
            constructor
            · exact (allOthersInvalid_iff_snapshotAllOthersInvalid s i .acquireBlock grow source).mp hallInv
            · simp [probeMaskForResult]
              rw [cachedProbeMask_eq_noProbeMask_of_allOthersInvalid hallInv]
              rfl
      · -- RecvAcquirePermAtManager
        rcases hperm with ⟨grow, source, _, _, _, _, _, hgrowLegal, hresT, hrest⟩
        rcases hrest with ⟨hndirty, _, hs'⟩
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
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hdirty, _⟩
      exfalso
      rw [hnoDirty i] at hdirty
      contradiction
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnPlanInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnPlanInv, hcur, recvReleaseAckState, recvReleaseAckShared]

theorem forwardSimInv_preserved (n : Nat) (s s' : SymState HomeState NodeState n)
    (hinv : forwardSimInv n s) (hnext : (tlMessages.toSpec n).next s s') :
    forwardSimInv n s' := by
  rcases hinv with ⟨hrefInv, hclean, htxnLine, hpreClean, hpreNoDirty, hplan⟩
  rcases hrefInv with ⟨hfull, hnoDirty, htxnData, hcleanRel, hrelUniq⟩
  exact ⟨refinementInv_preserved n s s' ⟨hfull, hnoDirty, htxnData, hcleanRel, hrelUniq⟩ hnext,
    cleanDataInv_preserved n s s' ⟨⟨hfull, hnoDirty, htxnData, hcleanRel, hrelUniq⟩, hclean, htxnLine, hpreClean, hpreNoDirty, hplan⟩ hnext,
    txnLineInv_preserved n s s' ⟨⟨hfull, hnoDirty, htxnData, hcleanRel, hrelUniq⟩, hclean, htxnLine, hpreClean, hpreNoDirty, hplan⟩ hnext,
    preLinesCleanInv_preserved n s s' hclean hpreClean hnext,
    preLinesNoDirtyInv_preserved n s s' hnoDirty hpreNoDirty hnext,
    txnPlanInv_preserved n s s' ⟨⟨hfull, hnoDirty, htxnData, hcleanRel, hrelUniq⟩, hclean, htxnLine, hpreClean, hpreNoDirty, hplan⟩ hnext⟩

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
  rcases hinv with ⟨⟨hfull, hnoDirty, htxnData, hcleanRel, hrelUniq⟩, hclean, htxnLine, _, hpreNoDirty, hplan⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock grow source =>
      right; exact (refMap_sendAcquireBlock_eq hstep).symm
  | .sendAcquirePerm grow source =>
      right; exact (refMap_sendAcquirePerm_eq hstep).symm
  | .recvAcquireAtManager =>
      left; exact refMap_recvAcquireAtManager_next ⟨hfull, hnoDirty, htxnData, hcleanRel, hrelUniq⟩ hstep
  | .recvProbeAtMaster =>
      right; exact (refMap_recvProbeAtMaster_eq hstep).symm
  | .recvProbeAckAtManager =>
      right; exact (refMap_recvProbeAckAtManager_eq hstep).symm
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
          | B => exact refMap_sendGrant_block_branch_next hfull hclean htxnLine hpreNoDirty htxnData hplan hstep' hcur htx hperm
          | T => exact refMap_sendGrant_block_tip_next hfull htxnLine htxnData hplan hstep' hcur htx hperm
      | acquirePerm =>
          exact refMap_sendGrant_acquirePerm_next hfull hpreNoDirty htxnLine htxnData hplan hstep' hcur htx
  | .recvGrantAtMaster =>
      right; exact (refMap_recvGrantAtMaster_eq hstep).symm
  | .recvGrantAckAtManager =>
      left; exact refMap_recvGrantAckAtManager_next hfull htxnLine hstep
  | .sendRelease param =>
      left; exact refMap_sendRelease_next hnoDirty hfull hstep
  | .sendReleaseData param =>
      exact (refMap_sendReleaseData_absurd hnoDirty hstep).elim
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
