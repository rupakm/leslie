import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.Invariants

namespace TileLink.Messages

open TLA TileLink SymShared Classical

/-- Helper: if all lines are unchanged between s and s', dirtyExclusiveInv transfers. -/
private theorem probedLine_dirty (line : CacheLine) (cap : CapParam) :
    (probedLine line cap).dirty = false := by
  cases cap <;> simp [probedLine, invalidatedLine, branchAfterProbe, tipAfterProbe]

private theorem releasedLine_dirty (line : CacheLine) (perm : TLPerm) :
    (releasedLine line perm).dirty = false := by
  cases perm <;> simp [releasedLine, invalidatedLine, branchAfterProbe, tipAfterProbe]

private theorem grantLine_dirty (line : CacheLine) (tx : ManagerTxn) :
    (grantLine line tx).dirty = false := by
  unfold grantLine
  cases tx.grantHasData <;> cases tx.resultPerm <;> simp [invalidatedLine]


/-- Helper: if all lines are unchanged between s and s', dirtyExclusiveInv transfers. -/
private theorem dirtyExclusiveInv_of_same_lines (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hdirtyEx : dirtyExclusiveInv n s)
    (hlines : ∀ j : Fin n, (s'.locals j).line = (s.locals j).line) :
    dirtyExclusiveInv n s' := by
  intro p q hpq hdirtyP
  rw [hlines p] at hdirtyP; rw [hlines q]
  exact hdirtyEx p q hpq hdirtyP

theorem dirtyExclusiveInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hdirtyEx : dirtyExclusiveInv n s) (hSwmr : permSwmrInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    dirtyExclusiveInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock grow source =>
      exact dirtyExclusiveInv_of_same_lines n s s' hdirtyEx
        (fun j => sendAcquireBlock_line hstep)
  | .sendAcquirePerm grow source =>
      exact dirtyExclusiveInv_of_same_lines n s s' hdirtyEx
        (fun j => sendAcquirePerm_line hstep)
  | .recvAcquireAtManager =>
      -- recvAcquire doesn't change lines
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, hs'⟩
        rcases hs' with ⟨_, hs'⟩
        exact dirtyExclusiveInv_of_same_lines n s s' hdirtyEx
          (fun j => by rw [hs']; simp [recvAcquireState, recvAcquireLocals_line])
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, hs'⟩
        rcases hs' with ⟨_, hs'⟩
        exact dirtyExclusiveInv_of_same_lines n s s' hdirtyEx
          (fun j => by rw [hs']; simp [recvAcquireState, recvAcquireLocals_line])
  | .recvProbeAtMaster =>
      -- probedLine always sets dirty=false
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, _, hs'⟩
      intro p q hpq hdirtyP
      rw [hs'] at hdirtyP ⊢
      by_cases hpi : p = i
      · subst hpi
        simp only [recvProbeState, recvProbeLocals, recvProbeLocal, setFn, ite_true] at hdirtyP
        rw [probedLine_dirty] at hdirtyP; cases hdirtyP
      · simp [recvProbeState, recvProbeLocals, setFn, hpi] at hdirtyP
        by_cases hqi : q = i
        · subst hqi
          simp only [recvProbeState, recvProbeLocals, recvProbeLocal, setFn, ite_true]
          -- hdirtyEx gives perm i = .N in pre. probedLine of a .N perm line
          -- needs protocol reasoning (probes only sent to cached nodes).
          sorry
        · simp [recvProbeState, recvProbeLocals, setFn, hqi]
          exact hdirtyEx p q hpq hdirtyP
  | .recvProbeAckAtManager =>
      -- recvProbeAck clears chanC, doesn't change lines
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, hs'⟩
      exact dirtyExclusiveInv_of_same_lines n s s' hdirtyEx (fun j => by
        rw [hs']
        by_cases hji : j = i
        · subst hji; simp [recvProbeAckState, recvProbeAckLocals, recvProbeAckLocal, setFn]
        · simp [recvProbeAckState, recvProbeAckLocals, setFn, hji])
  | .sendGrantToRequester =>
      -- sendGrant doesn't change lines
      rcases hstep with ⟨tx, _, _, _, _, _, _, _, _, hs'⟩
      exact dirtyExclusiveInv_of_same_lines n s s' hdirtyEx
        (fun j => by rw [hs']; exact sendGrantState_line s i j tx)
  | .recvGrantAtMaster =>
      -- grantLine always sets dirty=false
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      intro p q hpq hdirtyP
      by_cases hpi : p = i
      · subst hpi
        simp only [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, ite_true] at hdirtyP
        rw [grantLine_dirty] at hdirtyP; cases hdirtyP
      · simp [recvGrantState, recvGrantLocals, setFn, hpi] at hdirtyP
        by_cases hqi : q = i
        · subst hqi
          -- dirty p → perm i = .N in pre. grantLine of a .N-perm line needs fullInv reasoning.
          sorry
        · simp [recvGrantState, recvGrantLocals, setFn, hqi]
          exact hdirtyEx p q hpq hdirtyP
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, hs'⟩
      exact dirtyExclusiveInv_of_same_lines n s s' hdirtyEx
        (fun j => by rw [hs']; exact recvGrantAckState_line s i j)
  | .sendRelease param =>
      -- releasedLine always sets dirty=false
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      rw [hs']
      intro p q hpq hdirtyP
      by_cases hpi : p = i
      · subst hpi
        simp only [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, ite_true] at hdirtyP
        rw [releasedLine_dirty] at hdirtyP; cases hdirtyP
      · simp [sendReleaseState, sendReleaseLocals, setFn, hpi] at hdirtyP
        by_cases hqi : q = i
        · subst hqi
          simp only [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, ite_true]
          -- hdirtyEx gives perm i = .N from dirty p. releasedLine.perm = param.result.
          -- From guard: param.legalFrom (perm i). Since perm i = .N, param.source = .N.
          -- All PruneReportParam with source .N: only NtoN. result = .N.
          have hpermN : (s.locals i).line.perm = .N := hdirtyEx p i (Ne.symm hpq) hdirtyP
          rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlegal, _, _, _⟩
          rw [hpermN] at hlegal
          cases param <;> simp [PruneReportParam.legalFrom, PruneReportParam.source] at hlegal
          simp [releasedLine, invalidatedLine]
        · simp [sendReleaseState, sendReleaseLocals, setFn, hqi]
          exact hdirtyEx p q hpq hdirtyP
  | .sendReleaseData param =>
      -- releasedLine always sets dirty=false; SendReleaseData guard has dirty=true
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hdirtyI, hs'⟩
      rw [hs']
      intro p q hpq hdirtyP
      by_cases hpi : p = i
      · subst hpi
        simp only [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, ite_true] at hdirtyP
        rw [releasedLine_dirty] at hdirtyP; cases hdirtyP
      · simp [sendReleaseState, sendReleaseLocals, setFn, hpi] at hdirtyP
        by_cases hqi : q = i
        · -- dirty i = true in pre, dirty p = true in pre (p ≠ i)
          -- dirtyExclusiveInv i p: dirty i → perm p = .N
          -- dirty p = true → perm p = .T (from lineWF in fullInv) → contradiction
          rw [hqi]
          simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn]
          have hpermPN := hdirtyEx i p (Ne.symm hpi) hdirtyI
          rcases hfull with ⟨⟨hlineWF, _, _, _⟩, _, _⟩
          exact absurd ((hlineWF p).1 hdirtyP).1 (by rw [hpermPN]; simp)
        · simp [sendReleaseState, sendReleaseLocals, setFn, hqi]
          exact hdirtyEx p q hpq hdirtyP
  | .recvReleaseAtManager =>
      -- recvRelease doesn't change lines (only chanC/chanD)
      rcases hstep with ⟨msg, param, _, _, _, _, _, _, _, _, _, _, hs'⟩
      exact dirtyExclusiveInv_of_same_lines n s s' hdirtyEx (fun j => by
        rw [hs']
        by_cases hji : j = i
        · subst hji; simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn]
        · simp [recvReleaseState, recvReleaseLocals, setFn, hji])
  | .recvReleaseAckAtMaster =>
      -- doesn't change lines
      rcases hstep with ⟨msg, _, _, _, _, _, _, hs'⟩
      exact dirtyExclusiveInv_of_same_lines n s s' hdirtyEx (fun j => by
        rw [hs']
        by_cases hji : j = i
        · subst hji; simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn]
        · simp [recvReleaseAckState, recvReleaseAckLocals, setFn, hji])
  | .store v =>
      -- Store sets dirty=true at node i (perm=.T guard), others unchanged
      rcases hstep with ⟨hcur, _, _, _, hperm, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      intro p q hpq hdirtyP
      by_cases hpi : p = i
      · subst hpi
        -- p = i, perm i = .T (store guard). By SWMR: perm q = .N for q ≠ i.
        -- Post-state: q ≠ i so line unchanged via setFn.
        simp [setFn, Ne.symm hpq]
        exact hSwmr i q hpq hperm
      · -- p ≠ i: dirty p unchanged. q = i → store guard perm i = .T but
        -- dirtyExclusiveInv says perm i = .N, contradiction.
        simp [setFn, hpi] at hdirtyP
        by_cases hqi : q = i
        · rw [hqi]; simp [setFn, storeLocal]
          have hpermIN := hdirtyEx p i hpi hdirtyP
          rw [hperm] at hpermIN; cases hpermIN
        · simp [setFn, hqi]
          exact hdirtyEx p q hpq hdirtyP

theorem txnDataInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hdirtyEx : dirtyExclusiveInv n s) (htxnData : txnDataInv n s) (hcleanC : cleanChanCInv n s)
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
      -- plannedTxn_clean needs noDirtyInv; with dirtyExclusiveInv, dirty sources possible
      sorry
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, hs'⟩
      rcases hs' with ⟨_, hs'⟩
      rw [hs']
      simpa [txnDataInv, hcur, recvProbeState] using htxnData
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, hC, _, _, hs'⟩
      have hmsgNone : msg.data = none := hcleanC i msg hC
      rw [hs']
      simpa [txnDataInv, recvProbeAckState, recvProbeAckShared, hmsgNone, hcur] using htxnData
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
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      rw [hs']
      simp [txnDataInv, hcur, sendReleaseState]
  | .sendReleaseData param =>
      -- currentTxn = none in guard, stays none → txnDataInv trivially True
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnDataInv, hcur, sendReleaseState]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnDataInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnDataInv, hcur, recvReleaseAckState, recvReleaseAckShared]
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnDataInv, hcur]

theorem preLinesNoDirtyInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hdirtyEx : dirtyExclusiveInv n s) (hpre : preLinesNoDirtyInv n s)
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
      -- preLines snapshot current lines; need dirty k = false for all k
      -- With dirtyExclusiveInv, at most one dirty line exists, but that's not enough
      sorry
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
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      rw [hs']
      simp [preLinesNoDirtyInv, hcur, sendReleaseState]
  | .sendReleaseData _ =>
      -- currentTxn = none → preLinesNoDirtyInv trivially True
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesNoDirtyInv, hcur, sendReleaseState]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesNoDirtyInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesNoDirtyInv, hcur, recvReleaseAckState, recvReleaseAckShared]
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesNoDirtyInv, hcur]

theorem preLinesCleanInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hclean : cleanDataInv n s) (hpre : preLinesCleanInv n s) (hcleanC : cleanChanCInv n s)
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
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, hrest⟩
        rcases hrest with ⟨_, hs'⟩
        rw [hs']
        intro k hk hvalid
        have hdata : (s.locals ⟨k, hk⟩).line.data = s.shared.mem := hclean ⟨k, hk⟩
        simpa [plannedTxn, hk] using hdata
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, hrest⟩
        rcases hrest with ⟨_, hs'⟩
        rw [hs']
        intro k hk hvalid
        have hdata : (s.locals ⟨k, hk⟩).line.data = s.shared.mem := hclean ⟨k, hk⟩
        simpa [plannedTxn, hk] using hdata
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesCleanInv, hcur, recvProbeState]
        using hpre
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, hC, _, _, hs'⟩
      have hmsgNone : msg.data = none := hcleanC i msg hC
      rw [hs']
      simpa [preLinesCleanInv, hcur, recvProbeAckState, recvProbeAckShared, hmsgNone]
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
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
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
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesCleanInv, hcur]


theorem cleanChanCInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hdirtyEx : dirtyExclusiveInv n s) (hclean : cleanChanCInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    cleanChanCInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  intro j msg hCj
  match a with
  | .sendAcquireBlock grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hCj
      by_cases hji : j = i
      · subst j; simp [setFn] at hCj; exact hclean i msg hCj
      · simp [setFn, hji] at hCj; exact hclean j msg hCj
  | .sendAcquirePerm grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hCj
      by_cases hji : j = i
      · subst j; simp [setFn] at hCj; exact hclean i msg hCj
      · simp [setFn, hji] at hCj; exact hclean j msg hCj
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨_, _, _, _, _, _, _, _, _, _, hs'⟩
        rcases hs' with ⟨_, hs'⟩
        rw [hs'] at hCj
        simp [recvAcquireState, recvAcquireLocals, scheduleProbeLocals_chanC] at hCj
        exact hclean j msg hCj
      · rcases hperm with ⟨_, _, _, _, _, _, _, _, _, hs'⟩
        rcases hs' with ⟨_, hs'⟩
        rw [hs'] at hCj
        simp [recvAcquireState, recvAcquireLocals, scheduleProbeLocals_chanC] at hCj
        exact hclean j msg hCj
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, bmsg, _, _, _, _, _, _, _, _, hs'⟩
      rcases hs' with ⟨_, hs'⟩
      rw [hs'] at hCj
      by_cases hji : j = i
      · subst j
        simp [recvProbeState, recvProbeLocals, recvProbeLocal, setFn] at hCj
        subst hCj
        -- probeAckMsg data depends on dirty. With dirtyExclusiveInv, node might be dirty.
        -- This needs fullInv reasoning to show probed node can't be dirty during a probe.
        sorry
      · simp [recvProbeState, recvProbeLocals, setFn, hji] at hCj
        exact hclean j msg hCj
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hCj
      by_cases hji : j = i
      · subst j
        simp [recvProbeAckState, recvProbeAckLocals, recvProbeAckLocal, setFn] at hCj
      · simp [recvProbeAckState, recvProbeAckLocals, recvProbeAckLocal, setFn, hji] at hCj
        exact hclean j msg hCj
  | .sendGrantToRequester =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hCj
      by_cases hji : j = i
      · subst j; simp [sendGrantState, sendGrantLocals, sendGrantLocal, setFn] at hCj
        exact hclean i msg hCj
      · simp [sendGrantState, sendGrantLocals, sendGrantLocal, setFn, hji] at hCj
        exact hclean j msg hCj
  | .recvGrantAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hCj
      by_cases hji : j = i
      · subst j; simp [recvGrantState, recvGrantLocals, recvGrantLocal, setFn] at hCj
        exact hclean i msg hCj
      · simp [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, hji] at hCj
        exact hclean j msg hCj
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hCj
      by_cases hji : j = i
      · subst j; simp [recvGrantAckState, recvGrantAckLocals, recvGrantAckLocal, setFn] at hCj
        exact hclean i msg hCj
      · simp [recvGrantAckState, recvGrantAckLocals, recvGrantAckLocal, setFn, hji] at hCj
        exact hclean j msg hCj
  | .sendRelease param =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      rw [hs'] at hCj
      by_cases hji : j = i
      · subst j
        simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn] at hCj
        subst hCj
        simp [releaseMsg, releaseDataPayload]
      · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] at hCj
        exact hclean j msg hCj
  | .sendReleaseData param =>
      -- SendReleaseData: release message carries data, violating cleanChanCInv
      -- This needs protocol reasoning to show it doesn't happen under refinementInv
      sorry
  | .recvReleaseAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hCj
      by_cases hji : j = i
      · subst j; simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn] at hCj
      · simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji] at hCj
        exact hclean j msg hCj
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hCj
      by_cases hji : j = i
      · subst j; simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn] at hCj
        exact hclean i msg hCj
      · simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji] at hCj
        exact hclean j msg hCj
  | .store v =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hCi, _, _, _, _, hs'⟩
      rw [hs'] at hCj
      by_cases hji : j = i
      · subst j; simp [setFn] at hCj; rw [hCi] at hCj; simp at hCj
      · simp [setFn, hji] at hCj; exact hclean j msg hCj

theorem releaseUniqueInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hdirtyEx : dirtyExclusiveInv n s) (hrelUniq : releaseUniqueInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    releaseUniqueInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  intro htxn'
  match a with
  | .sendAcquireBlock grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn' ⊢; simp at htxn'
      have h := hrelUniq htxn'
      exact ⟨fun hrel j => by
          have := h.1 hrel j
          by_cases hji : j = i <;> simp_all [setFn],
        fun p q hpq hp => by
          have hp' : (s.locals p).chanC ≠ none := by
            by_cases hpi : p = i <;> simp_all [setFn]
          have := h.2 p q hpq hp'
          by_cases hqi : q = i <;> simp_all [setFn]⟩
  | .sendAcquirePerm grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn' ⊢; simp at htxn'
      have h := hrelUniq htxn'
      exact ⟨fun hrel j => by
          have := h.1 hrel j
          by_cases hji : j = i <;> simp_all [setFn],
        fun p q hpq hp => by
          have hp' : (s.locals p).chanC ≠ none := by
            by_cases hpi : p = i <;> simp_all [setFn]
          have := h.2 p q hpq hp'
          by_cases hqi : q = i <;> simp_all [setFn]⟩
  | .recvAcquireAtManager =>
      -- Post: currentTxn = some, so the invariant is vacuously true
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨_, _, _, _, _, _, _, _, _, _, ⟨_, hs'⟩⟩
        rw [hs'] at htxn'; simp [recvAcquireState, recvAcquireShared] at htxn'
      · rcases hperm with ⟨_, _, _, _, _, _, _, _, _, ⟨_, hs'⟩⟩
        rw [hs'] at htxn'; simp [recvAcquireState, recvAcquireShared] at htxn'
  | .recvProbeAtMaster =>
      -- currentTxn stays some (guard requires some)
      rcases hstep with ⟨_, _, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn'; simp [recvProbeState] at htxn'; rw [htxn'] at hcur; cases hcur
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨_, _, hcur, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn'; simp [recvProbeAckState, recvProbeAckShared] at htxn'
  | .sendGrantToRequester =>
      rcases hstep with ⟨_, hcur, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn'; simp [sendGrantState, sendGrantShared] at htxn'
  | .recvGrantAtMaster =>
      rcases hstep with ⟨_, _, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn'; simp [recvGrantState, recvGrantShared] at htxn'; rw [htxn'] at hcur; cases hcur
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, hreq, hphase, hpendGrant, hD, hE, hSink, hmsg, hs'⟩
      rw [hs']
      rcases hfull with ⟨_, ⟨_, _, hchanC, _, _⟩, _⟩
      have hAllCNone : ∀ j : Fin n, (s.locals j).chanC = none := by
        intro j; specialize hchanC j
        cases hCj : (s.locals j).chanC with
        | none => rfl
        | some cmsg =>
            rw [hCj] at hchanC
            rcases hchanC with ⟨tx0, hcur0, hprobing, _, _, _, _, _⟩ | ⟨_, hcur0, _, _, _, _, _, _⟩
            · rw [hcur] at hcur0; injection hcur0 with htx; subst htx; rw [hphase] at hprobing; cases hprobing
            · rw [hcur] at hcur0; cases hcur0
      constructor
      · intro _ j
        by_cases hji : j = i
        · subst j; simp [recvGrantAckState, recvGrantAckLocals, recvGrantAckLocal, setFn, hAllCNone i]
        · simp [recvGrantAckState, recvGrantAckLocals, recvGrantAckLocal, setFn, hji, hAllCNone j]
      · intro p q _ hp
        by_cases hpi : p = i
        · subst p; simp [recvGrantAckState, recvGrantAckLocals, recvGrantAckLocal, setFn] at hp
          exact absurd (hAllCNone i) hp
        · simp [recvGrantAckState, recvGrantAckLocals, recvGrantAckLocal, setFn, hpi] at hp
          exact absurd (hAllCNone p) hp
  | .sendRelease param =>
      rcases hstep with ⟨htxn, hgrant, hrel, hCother, _, _, hCi, _, _, _, _, hflight, _, _, _, hs'⟩
      rw [hs']
      constructor
      · intro hrel'
        simp [sendReleaseState] at hrel'
        exact absurd hrel' (by simp [hrel])
      · intro p q hpq hp
        by_cases hpi : p = i
        · subst p
          by_cases hqi : q = i
          · exact absurd hqi (Ne.symm hpq)
          · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hqi]
            exact hCother q hqi
        · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hpi] at hp
          exact absurd (hCother p hpi) hp
  | .sendReleaseData param =>
      -- SendReleaseData: guard has currentTxn = none, dirty = true
      -- Post: chanC[i] set with data, others unchanged, currentTxn still none
      rcases hstep with ⟨htxn, hgrant, hrel, hCother, _, _, hCi, _, _, _, _, hflight, _, _, hs'⟩
      rw [hs']
      constructor
      · intro hrel'
        simp [sendReleaseState] at hrel'
        exact absurd hrel' (by simp [hrel])
      · intro p q hpq hp
        by_cases hpi : p = i
        · subst p
          by_cases hqi : q = i
          · exact absurd hqi (Ne.symm hpq)
          · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hqi]
            exact hCother q hqi
        · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hpi] at hp
          exact absurd (hCother p hpi) hp
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, htxn, hgrant, hrel, hflight, hC, _, _, _, _, _, hs'⟩
      rw [hs']
      have hpre := hrelUniq htxn
      constructor
      · intro _ j
        by_cases hji : j = i
        · subst j; simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn]
        · simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji]
          have : (s.locals i).chanC ≠ none := by rw [hC]; simp
          exact hpre.2 i j (Ne.symm hji) this
      · intro p q hpq hp
        by_cases hpi : p = i
        · subst p; simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn] at hp
        · simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hpi] at hp
          have : (s.locals i).chanC ≠ none := by rw [hC]; simp
          exact absurd (hpre.2 i p (Ne.symm hpi) this) hp
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, htxn, hgrant, hrel, hflight, hD, hmsg, hs'⟩
      rw [hs']
      have hpre := hrelUniq htxn
      have hAllCNone := hpre.1 (by rw [hrel]; simp)
      constructor
      · intro hrel' j
        simp [recvReleaseAckState, recvReleaseAckShared] at hrel'
      · intro p q hpq hp
        by_cases hpi : p = i
        · subst p; simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn] at hp
          exact absurd (hAllCNone i) hp
        · simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hpi] at hp
          exact absurd (hAllCNone p) hp
  | .store v =>
      rcases hstep with ⟨hcur, _, hrel, _, _, _, _, hCi, _, _, _, _, hs'⟩
      have hpre := hrelUniq hcur
      rw [hs']
      constructor
      · intro hrel'
        rw [hrel] at hrel'
        simp at hrel'
      · intro p q hpq hp
        by_cases hpi : p = i
        · subst p; simp [setFn, storeLocal] at hp; rw [hCi] at hp; simp at hp
        · have hp' : (s.locals p).chanC ≠ none := by
            simp [setFn, hpi] at hp; exact hp
          have := hpre.2 p q hpq hp'
          by_cases hqi : q = i
          · subst q; simp [setFn, storeLocal, hCi]
          · simp [setFn, hqi]; exact this

/-- Helper: if all lines are unchanged between s and s', permSwmrInv transfers. -/
private theorem permSwmrInv_of_same_lines (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hSwmr : permSwmrInv n s)
    (hlines : ∀ j : Fin n, (s'.locals j).line = (s.locals j).line) :
    permSwmrInv n s' := by
  intro p q hpq hpermP
  rw [hlines p] at hpermP; rw [hlines q]
  exact hSwmr p q hpq hpermP

/-- probedLine with probeCapOfResult never produces perm .T -/
private theorem probedLine_probeCapOfResult_perm_ne_T (line : CacheLine) (resultPerm : TLPerm) :
    (probedLine line (probeCapOfResult resultPerm)).perm ≠ .T := by
  cases resultPerm <;> simp [probeCapOfResult, probedLine, invalidatedLine, branchAfterProbe]

theorem permSwmrInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hSwmr : permSwmrInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    permSwmrInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock grow source =>
      exact permSwmrInv_of_same_lines n s s' hSwmr
        (fun j => sendAcquireBlock_line hstep)
  | .sendAcquirePerm grow source =>
      exact permSwmrInv_of_same_lines n s s' hSwmr
        (fun j => sendAcquirePerm_line hstep)
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, hs'⟩
        rcases hs' with ⟨_, hs'⟩
        exact permSwmrInv_of_same_lines n s s' hSwmr
          (fun j => by rw [hs']; simp [recvAcquireState, recvAcquireLocals_line])
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, hs'⟩
        rcases hs' with ⟨_, hs'⟩
        exact permSwmrInv_of_same_lines n s s' hSwmr
          (fun j => by rw [hs']; simp [recvAcquireState, recvAcquireLocals_line])
  | .recvProbeAtMaster =>
      -- probedLine with probeCapOfResult never gives perm .T
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, hparam, _, hs'⟩
      rw [hs']
      intro p q hpq hpermP
      by_cases hpi : p = i
      · -- p = i (probed node): post perm is probedLine ≠ .T
        rw [hpi] at hpermP
        simp only [recvProbeState, recvProbeLocals, recvProbeLocal, setFn, ite_true] at hpermP
        exact absurd hpermP (by rw [hparam]; exact probedLine_probeCapOfResult_perm_ne_T _ _)
      · -- p ≠ i: line p unchanged
        simp [recvProbeState, recvProbeLocals, setFn, hpi] at hpermP
        by_cases hqi : q = i
        · -- q = i: needs protocol reasoning (probed node has pre perm .N from SWMR)
          rw [hqi]
          simp only [recvProbeState, recvProbeLocals, recvProbeLocal, setFn, ite_true]
          sorry -- needs txnPlanInv reasoning: probed node i has pre perm .N, shouldn't be probed
        · -- q ≠ i: line q unchanged
          simp [recvProbeState, recvProbeLocals, setFn, hqi]
          exact hSwmr p q hpq hpermP
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, hs'⟩
      exact permSwmrInv_of_same_lines n s s' hSwmr (fun j => by
        rw [hs']
        by_cases hji : j = i
        · subst hji; simp [recvProbeAckState, recvProbeAckLocals, recvProbeAckLocal, setFn]
        · simp [recvProbeAckState, recvProbeAckLocals, setFn, hji])
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, _, _, _, _, _, _, _, _, hs'⟩
      exact permSwmrInv_of_same_lines n s s' hSwmr
        (fun j => by rw [hs']; exact sendGrantState_line s i j tx)
  | .recvGrantAtMaster =>
      -- grantLine changes perm at node i. Needs protocol reasoning.
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      intro p q hpq hpermP
      by_cases hpi : p = i
      · -- p = i: grantLine gives some perm. If .T, need all others .N.
        rw [hpi] at hpermP
        sorry -- needs deep protocol reasoning about grant correctness
      · -- p ≠ i: line p unchanged
        simp [recvGrantState, recvGrantLocals, setFn, hpi] at hpermP
        by_cases hqi : q = i
        · rw [hqi]
          simp only [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, ite_true]
          sorry -- needs protocol reasoning: can't grant while another node has .T
        · simp [recvGrantState, recvGrantLocals, setFn, hqi]
          exact hSwmr p q hpq hpermP
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, hs'⟩
      exact permSwmrInv_of_same_lines n s s' hSwmr
        (fun j => by rw [hs']; exact recvGrantAckState_line s i j)
  | .sendRelease param =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlegal, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      rw [hs']
      intro p q hpq hpermP
      by_cases hpi : p = i
      · -- p = i: post perm = param.result. If .T → param.source = .T → pre perm = .T.
        rw [hpi] at hpermP hpq
        simp only [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, ite_true] at hpermP
        rw [releasedLine_perm] at hpermP
        have hpermIT : (s.locals i).line.perm = .T := by
          rw [PruneReportParam.legalFrom] at hlegal; rw [hlegal]
          cases param <;> simp [PruneReportParam.result] at hpermP <;>
            simp [PruneReportParam.source]
        have hqi : q ≠ i := fun h => hpq (h.symm)
        simp [sendReleaseState, sendReleaseLocals, setFn, hqi]
        exact hSwmr i q hqi.symm hpermIT
      · -- p ≠ i: line p unchanged
        simp [sendReleaseState, sendReleaseLocals, setFn, hpi] at hpermP
        by_cases hqi : q = i
        · rw [hqi]
          simp only [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, ite_true]
          rw [releasedLine_perm]
          have hpermIN : (s.locals i).line.perm = .N := hSwmr p i hpi hpermP
          rw [PruneReportParam.legalFrom] at hlegal; rw [hpermIN] at hlegal
          cases param <;> simp [PruneReportParam.source] at hlegal
          simp [PruneReportParam.result]
        · simp [sendReleaseState, sendReleaseLocals, setFn, hqi]
          exact hSwmr p q hpq hpermP
  | .sendReleaseData param =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlegal, _, hs'⟩
      rw [hs']
      intro p q hpq hpermP
      by_cases hpi : p = i
      · rw [hpi] at hpermP hpq
        simp only [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, ite_true] at hpermP
        rw [releasedLine_perm] at hpermP
        have hpermIT : (s.locals i).line.perm = .T := by
          rw [PruneReportParam.legalFrom] at hlegal; rw [hlegal]
          cases param <;> simp [PruneReportParam.result] at hpermP <;>
            simp [PruneReportParam.source]
        have hqi : q ≠ i := fun h => hpq (h.symm)
        simp [sendReleaseState, sendReleaseLocals, setFn, hqi]
        exact hSwmr i q hqi.symm hpermIT
      · simp [sendReleaseState, sendReleaseLocals, setFn, hpi] at hpermP
        by_cases hqi : q = i
        · rw [hqi]
          simp only [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, ite_true]
          rw [releasedLine_perm]
          have hpermIN : (s.locals i).line.perm = .N := hSwmr p i hpi hpermP
          rw [PruneReportParam.legalFrom] at hlegal; rw [hpermIN] at hlegal
          cases param <;> simp [PruneReportParam.source] at hlegal
          simp [PruneReportParam.result]
        · simp [sendReleaseState, sendReleaseLocals, setFn, hqi]
          exact hSwmr p q hpq hpermP
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, _, _, _, _, _, _, _, _, _, _, hs'⟩
      exact permSwmrInv_of_same_lines n s s' hSwmr (fun j => by
        rw [hs']
        by_cases hji : j = i
        · subst hji; simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn]
        · simp [recvReleaseState, recvReleaseLocals, setFn, hji])
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, _, _, _, _, _, _, hs'⟩
      exact permSwmrInv_of_same_lines n s s' hSwmr (fun j => by
        rw [hs']
        by_cases hji : j = i
        · subst hji; simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn]
        · simp [recvReleaseAckState, recvReleaseAckLocals, setFn, hji])
  | .store v =>
      rcases hstep with ⟨_, _, _, _, hperm, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      intro p q hpq hpermP
      by_cases hpi : p = i
      · -- p = i: pre perm i = .T. By SWMR, all q ≠ i have .N. Post: q ≠ i unchanged.
        rw [hpi] at hpermP hpq
        have hqi : q ≠ i := fun h => hpq (h.symm)
        simp [setFn, hqi]
        exact hSwmr i q hqi.symm hperm
      · -- p ≠ i: line p unchanged
        simp [setFn, hpi] at hpermP
        by_cases hqi : q = i
        · -- q = i: pre perm p = .T and perm i = .T (guard). SWMR says perm i = .N. Contradiction.
          rw [hqi]; simp [setFn, storeLocal]
          have hpermIN := hSwmr p i hpi hpermP
          rw [hperm] at hpermIN; cases hpermIN
        · simp [setFn, hqi]
          exact hSwmr p q hpq hpermP

theorem refinementInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hinv : refinementInv n s) (hnext : (tlMessages.toSpec n).next s s') :
    refinementInv n s' := by
  rcases hinv with ⟨hfull, hdirtyEx, hSwmr, htxnData, hcleanRel, hrelUniq⟩
  exact ⟨fullInv_preserved_with_release n s s' hfull hnext,
    dirtyExclusiveInv_preserved n s s' hfull hdirtyEx hSwmr hnext,
    permSwmrInv_preserved n s s' hfull hSwmr hnext,
    txnDataInv_preserved n s s' hdirtyEx htxnData hcleanRel hnext,
    cleanChanCInv_preserved n s s' hdirtyEx hcleanRel hnext,
    releaseUniqueInv_preserved n s s' hfull hdirtyEx hrelUniq hnext⟩

end TileLink.Messages
