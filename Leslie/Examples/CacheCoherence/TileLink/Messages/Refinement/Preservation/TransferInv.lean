import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.Invariants
import Leslie.Gadgets.ActionCases

/-! ## Preservation of preLinesWFInv and txnTransferMemInv

    These are newer invariants added to support the txnDataInv Part 3 proof
    (transferVal = mem at grantReady after dirty probeAck processing).
    Extracted from the main Preservation.lean for context manageability. -/

namespace TileLink.Messages

open TLA TileLink SymShared Classical

theorem preLinesWFInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hpreWF : preLinesWFInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    preLinesWFInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩; rw [hs']; exact hpreWF
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩; rw [hs']; exact hpreWF
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs']
        simp only [preLinesWFInv, recvAcquireState, recvAcquireShared]
        intro k hk
        rcases hfull with ⟨⟨hlineWF, _, _, _⟩, _, _⟩
        simp [plannedTxn, hk]
        exact hlineWF ⟨k, hk⟩
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs']
        simp only [preLinesWFInv, recvAcquireState, recvAcquireShared]
        intro k hk
        rcases hfull with ⟨⟨hlineWF, _, _, _⟩, _, _⟩
        simp [plannedTxn, hk]
        exact hlineWF ⟨k, hk⟩
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, hs'⟩
      rcases hs' with ⟨_, hs'⟩; rw [hs']
      simpa [preLinesWFInv, hcur, recvProbeState] using hpreWF
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, hs'⟩; rw [hs']
      simpa [preLinesWFInv, hcur, recvProbeAckState, recvProbeAckShared] using hpreWF
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, _, _, _, _, _, _, _, hs'⟩; rw [hs']
      simpa [preLinesWFInv, hcur, sendGrantState, sendGrantShared] using hpreWF
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩; rw [hs']
      simpa [preLinesWFInv, hcur, recvGrantState, recvGrantShared] using hpreWF
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩; rw [hs']
      simp [preLinesWFInv, recvGrantAckState, recvGrantAckShared]
  | .sendRelease _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'; simp [preLinesWFInv, hcur, sendReleaseState]
  | .sendReleaseData _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'; simp [preLinesWFInv, hcur, sendReleaseState]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'; simp [preLinesWFInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩; rw [hs']
      simp [preLinesWFInv, hcur, recvReleaseAckState, recvReleaseAckShared]
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [preLinesWFInv, hcur]
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩; exact hpreWF
  | .uncachedGet source =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [preLinesWFInv, hcur]
  | .uncachedPut source v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [preLinesWFInv, hcur]
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcur, _, _, _, _, _, rfl⟩
      simp [preLinesWFInv, hcur]
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩; exact hpreWF

theorem txnTransferMemInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (htxnData : txnDataInv n s)
    (hpreNoDirty : preLinesNoDirtyInv n s) (husedDirty : usedDirtySourceInv n s)
    (hdirtyOwner : dirtyOwnerExistsInv n s) (hpreWF : preLinesWFInv n s)
    (htxnTM : txnTransferMemInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    txnTransferMemInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩; rw [hs']; exact htxnTM
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩; rw [hs']; exact htxnTM
  | .recvAcquireAtManager =>
      -- New transaction: at init probesRemaining = probesNeeded.
      -- Dirty nodes have probesNeeded = true (from lineWFInv → perm .T → in mask).
      -- So the "all dirty processed" premise (remaining = false) is contradicted.
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, htxn, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs']
        simp only [txnTransferMemInv, recvAcquireState, recvAcquireShared]
        intro huds hall
        sorry -- At init: usedDirtySource = true → dirty node k with remaining = needed = true → contradiction
      · rcases hperm with ⟨grow, source, htxn, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs']
        sorry -- Same as acquireBlock case
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, hs'⟩
      rcases hs' with ⟨_, hs'⟩; rw [hs']
      simpa [txnTransferMemInv, hcur, recvProbeState] using htxnTM
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, hphase, hrem, _, hC, _, _, hs'⟩
      rw [hs']
      -- From chanCInv: msg.data = probeAckDataOfLine (tx.preLines i.1)
      rcases hfull with ⟨⟨_, _, _, _⟩, ⟨_, _, hchanC, _, _⟩, _⟩
      specialize hchanC i; rw [hC] at hchanC
      rcases hchanC with ⟨tx', hcur', _, _, _, _, _, _, hdata⟩ | ⟨_, hcurNone, _⟩
      · rw [hcur] at hcur'; cases hcur'
        cases hdirtyI : (tx.preLines i.1).dirty
        · -- Clean probeAck: msg.data = none → transferVal and mem unchanged
          have hmsg : msg.data = none := by simp [hdata, probeAckDataOfLine, hdirtyI]
          simp only [txnTransferMemInv, recvProbeAckState, recvProbeAckShared, hmsg,
            Option.isSome, Bool.or_false]
          simp only [txnTransferMemInv, hcur] at htxnTM
          intro huds hall
          apply htxnTM huds
          intro k hk hdirty
          have hki : k ≠ i.1 := by
            intro heq; rw [heq] at hdirty; rw [hdirtyI] at hdirty; cases hdirty
          have := hall k hk hdirty
          simp [clearProbeIdx, hki] at this
          exact this
        · -- Dirty probeAck: msg.data = some data → both transferVal and mem set to same value
          have hmsg : msg.data = some (tx.preLines i.1).data := by
            simp [hdata, probeAckDataOfLine, hdirtyI]
          simp only [txnTransferMemInv, recvProbeAckState, recvProbeAckShared, hmsg,
            Option.isSome, Bool.or_true]
          intro huds _
          obtain ⟨k, hk, _, hk_dirty, htv⟩ := hdirtyOwner tx hcur huds
          have hpreWF' : ∀ k : Nat, k < n → (tx.preLines k).WellFormed := by
            simpa [preLinesWFInv, hcur] using hpreWF
          have hpreNoDirty' : ∀ k1 k2 : Nat, k1 < n → k2 < n → k1 ≠ k2 →
              (tx.preLines k1).dirty = true → (tx.preLines k2).perm = .N := by
            simpa [preLinesNoDirtyInv, hcur] using hpreNoDirty
          by_cases hki : k = i.1
          · rw [hki] at htv; exact htv
          · exfalso
            have hwf_k := hpreWF' k hk
            have hpermT_k := hwf_k.1 hk_dirty |>.1
            have hpermN_k := hpreNoDirty' i.1 k i.is_lt hk (Ne.symm hki) hdirtyI
            rw [hpermT_k] at hpermN_k; cases hpermN_k
      · rw [hcur] at hcurNone; simp at hcurNone
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, _, _, _, _, _, _, _, hs'⟩; rw [hs']
      simpa [txnTransferMemInv, hcur, sendGrantState, sendGrantShared] using htxnTM
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩; rw [hs']
      simpa [txnTransferMemInv, hcur, recvGrantState, recvGrantShared] using htxnTM
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩; rw [hs']
      simp [txnTransferMemInv, recvGrantAckState, recvGrantAckShared]
  | .sendRelease _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'; simp [txnTransferMemInv, hcur, sendReleaseState]
  | .sendReleaseData _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'; simp [txnTransferMemInv, hcur, sendReleaseState]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'; simp [txnTransferMemInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩; rw [hs']
      simp [txnTransferMemInv, hcur, recvReleaseAckState, recvReleaseAckShared]
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [txnTransferMemInv, hcur]
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩; exact htxnTM
  | .uncachedGet source =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [txnTransferMemInv, hcur]
  | .uncachedPut source v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [txnTransferMemInv, hcur]
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcur, _, _, _, _, _, rfl⟩
      simp [txnTransferMemInv, hcur]
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩; exact htxnTM

end TileLink.Messages
