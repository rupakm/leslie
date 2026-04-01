import Leslie.Examples.CacheCoherence.TileLink.Messages.StepGrant

namespace TileLink.Messages

open TLA TileLink SymShared

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
    (hgrant : s.shared.pendingGrantAck = none)
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
      · rcases hrelBranch with ⟨hcurNone, hpendingGrant, hpendingRel, _, _, _⟩
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
  sorry

theorem coreInv_preserved_sendRelease (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} {param : PruneReportParam} (hstep : SendRelease s s' i param) :
    coreInv n s' := by
  sorry

theorem coreInv_preserved_sendReleaseData (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} {param : PruneReportParam} (hstep : SendReleaseData s s' i param) :
    coreInv n s' := by
  sorry

theorem channelInv_preserved_sendRelease (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    {i : Fin n} {param : PruneReportParam} (hstep : SendRelease s s' i param) :
    channelInv n s' := by
  sorry

theorem channelInv_preserved_sendReleaseData (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    {i : Fin n} {param : PruneReportParam} (hstep : SendReleaseData s s' i param) :
    channelInv n s' := by
  sorry

theorem coreInv_preserved_recvReleaseAtManager (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} (hstep : RecvReleaseAtManager s s' i) :
    coreInv n s' := by
  sorry

theorem channelInv_preserved_recvReleaseAtManager (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    {i : Fin n} (hstep : RecvReleaseAtManager s s' i) :
    channelInv n s' := by
  sorry

theorem coreInv_preserved_recvReleaseAckAtMaster (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} (hstep : RecvReleaseAckAtMaster s s' i) :
    coreInv n s' := by
  sorry

theorem channelInv_preserved_recvReleaseAckAtMaster (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    {i : Fin n} (hstep : RecvReleaseAckAtMaster s s' i) :
    channelInv n s' := by
  sorry

theorem fullInv_preserved_with_release (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hinv : fullInv n s) (hnext : (tlMessages.toSpec n).next s s') :
    fullInv n s' := by
  sorry

end TileLink.Messages
