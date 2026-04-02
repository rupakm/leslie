import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.Invariants

namespace TileLink.Messages

open TLA TileLink SymShared Classical

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
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, hs'⟩
        rcases hs' with ⟨_, hs'⟩
        intro j
        rw [hs']
        simpa [recvAcquireState, recvAcquireLocals_line] using hnoDirty j
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, hs'⟩
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
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
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
  | .store v =>
      -- Store sets dirty = true on node i, violating noDirtyInv
      sorry

theorem txnDataInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hnoDirty : noDirtyInv n s) (htxnData : txnDataInv n s) (hcleanC : cleanChanCInv n s)
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
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, hs'⟩
        rcases hs' with ⟨_, hs'⟩
        rcases plannedTxn_clean s i hnoDirty with ⟨hdirtySrc, htransfer⟩
        rw [hs']
        simp [txnDataInv, recvAcquireState, recvAcquireShared, plannedTxn, hdirtySrc, htransfer]
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, hs'⟩
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
      rcases hstep with ⟨tx, msg, hcur, _, _, _, hC, _, _, hs'⟩
      have hmsgNone : msg.data = none := hcleanC i msg hC
      rw [hs']
      simp [txnDataInv, hcur, recvProbeAckState, recvProbeAckShared, hmsgNone]
      exact htxnData
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
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnDataInv, hcur]

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
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, hrest⟩
        rcases hrest with ⟨_, hs'⟩
        rw [hs']
        intro k hk
        simp [preLinesNoDirtyInv, recvAcquireState, recvAcquireShared, plannedTxn, hk, hnoDirty ⟨k, hk⟩]
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, hrest⟩
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
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
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
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, hs'⟩
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
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesCleanInv, hcur]


theorem cleanChanCInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hnoDirty : noDirtyInv n s) (hclean : cleanChanCInv n s)
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
        -- probeAckMsg data = probeAckDataOfLine line. Under noDirtyInv, dirty = false → data = none
        simp [probeAckMsg, probeAckDataOfLine, hnoDirty i]
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
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hdirty, _⟩
      exact absurd hdirty (by simp [hnoDirty i])
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
      rcases hstep with ⟨_, _, _, _, _, _, hCi, _, _, _, _, hs'⟩
      rw [hs'] at hCj
      by_cases hji : j = i
      · subst j; simp [setFn] at hCj; rw [hCi] at hCj; simp at hCj
      · simp [setFn, hji] at hCj; exact hclean j msg hCj

theorem releaseUniqueInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hnoDirty : noDirtyInv n s) (hrelUniq : releaseUniqueInv n s)
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
      -- Post: currentTxn = none. Pre: currentTxn = some with grantPendingAck.
      -- All chanC were none (chanCInv probe requires probing phase, release requires currentTxn = none)
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
      -- Post: currentTxn = none, chanC[i] set, others unchanged
      rcases hstep with ⟨htxn, hgrant, hrel, hCother, _, _, hCi, _, _, _, _, hflight, _, _, _, hs'⟩
      rw [hs']
      constructor
      · -- pendingReleaseAck ≠ none → all chanC = none
        intro hrel'
        simp [sendReleaseState] at hrel'
        exact absurd hrel' (by simp [hrel])
      · -- at most one chanC non-none
        intro p q hpq hp
        by_cases hpi : p = i
        · subst p
          by_cases hqi : q = i
          · exact absurd hqi (Ne.symm hpq)
          · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hqi]
            exact hCother q hqi
        · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hpi] at hp
          exact absurd (hCother p hpi) hp
  | .sendReleaseData param =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hdirty, _⟩
      exact absurd hdirty (by simp [hnoDirty i])
  | .recvReleaseAtManager =>
      -- Post: chanC[i] cleared, pendingReleaseAck set, others unchanged
      rcases hstep with ⟨msg, param, htxn, hgrant, hrel, hflight, hC, _, _, _, _, _, hs'⟩
      rw [hs']
      have hpre := hrelUniq htxn
      constructor
      · -- pendingReleaseAck = some i ≠ none → all chanC = none
        intro _ j
        by_cases hji : j = i
        · subst j; simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn]
        · simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji]
          have : (s.locals i).chanC ≠ none := by rw [hC]; simp
          exact hpre.2 i j (Ne.symm hji) this
      · -- at most one chanC non-none
        intro p q hpq hp
        by_cases hpi : p = i
        · subst p; simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn] at hp
        · simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hpi] at hp
          -- p ≠ i and chanC[p] ≠ none, but pre-state had chanC[i] ≠ none, contradicting uniqueness
          have : (s.locals i).chanC ≠ none := by rw [hC]; simp
          exact absurd (hpre.2 i p (Ne.symm hpi) this) hp
  | .recvReleaseAckAtMaster =>
      -- Post: pendingReleaseAck cleared, chanC unchanged
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
      rcases hstep with ⟨hcur, _, hrel, _, _, _, hCi, _, _, _, _, hs'⟩
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

theorem refinementInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hinv : refinementInv n s) (hnext : (tlMessages.toSpec n).next s s') :
    refinementInv n s' := by
  rcases hinv with ⟨hfull, hnoDirty, htxnData, hcleanRel, hrelUniq⟩
  exact ⟨fullInv_preserved_with_release n s s' hfull hnext,
    noDirtyInv_preserved n s s' hnoDirty hnext,
    txnDataInv_preserved n s s' hnoDirty htxnData hcleanRel hnext,
    cleanChanCInv_preserved n s s' hnoDirty hcleanRel hnext,
    releaseUniqueInv_preserved n s s' hfull hnoDirty hrelUniq hnext⟩

end TileLink.Messages
