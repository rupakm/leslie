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
      · rcases hblk with ⟨grow, source, htxn, _, _, _, _, _, _, _, hresult, _, hs'⟩
        rw [hs']
        simp only [txnTransferMemInv, recvAcquireState, recvAcquireShared]
        intro huds hall
        exfalso
        by_cases hex : ∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true
        · have hk := Classical.choose_spec hex
          let k := Classical.choose hex
          rcases hfull with ⟨⟨hlineWF, _, _, _⟩, _, _⟩
          have hpermT := (hlineWF k).1 hk.2 |>.1
          have hk_dirty_pre : ((plannedTxn s i .acquireBlock grow source).preLines k.1).dirty = true := by
            simp [plannedTxn, k.is_lt]; exact hk.2
          have hrem := hall k.1 k.is_lt hk_dirty_pre
          -- grow.result ∈ {.B, .T} from action precondition
          have hresultBT : grow.result = .B ∨ grow.result = .T := by
            rcases hresult with ⟨_, hr⟩ | ⟨_, _, hr⟩ | ⟨_, hr⟩
            · exact Or.inl hr
            · exact Or.inl hr
            · exact Or.inr hr
          -- At init, probesRemaining = probeMask; show mask(k) = true → contradiction
          have hmask : ∀ hr : grow.result = .B ∨ grow.result = .T,
              (probeMaskForResult s i grow.result) k.1 = true := by
            intro hr
            rcases hr with hr | hr <;> simp [probeMaskForResult, hr, writableProbeMask,
              cachedProbeMask, k.is_lt, dite_true, show (⟨k.1, k.is_lt⟩ : Fin n) = k from rfl,
              show k ≠ i from hk.1, hpermT]
          have hrem_eq : (plannedTxn s i .acquireBlock grow source).probesRemaining k.1 =
              (probeMaskForResult s i grow.result) k.1 := by
            simp [plannedTxn]
          rw [hrem_eq, hmask hresultBT] at hrem
          exact absurd hrem (by decide)
        · -- No dirty owner → usedDirtySource should be false → contradiction
          -- hex : ¬∃ j, j ≠ i ∧ dirty j → dirtyOwnerOpt = none → usedDirtySource = false
          exfalso; revert huds; simp [plannedTxn, plannedUsedDirtySource, dirtyOwnerOpt, dif_neg hex]
      · rcases hperm with ⟨grow, source, htxn, _, _, _, _, _, _, hresultT, _, hs'⟩
        rw [hs']
        simp only [txnTransferMemInv, recvAcquireState, recvAcquireShared]
        intro huds hall
        exfalso
        by_cases hex : ∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true
        · have hk := Classical.choose_spec hex
          let k := Classical.choose hex
          rcases hfull with ⟨⟨hlineWF, _, _, _⟩, _, _⟩
          have hpermT := (hlineWF k).1 hk.2 |>.1
          have hk_dirty_pre : ((plannedTxn s i .acquirePerm grow source).preLines k.1).dirty = true := by
            simp [plannedTxn, k.is_lt]; exact hk.2
          have hrem := hall k.1 k.is_lt hk_dirty_pre
          -- grow.result = .T → cachedProbeMask includes k (perm .T ≠ .N) → true = false
          have hmask : (probeMaskForResult s i grow.result) k.1 = true := by
            simp [probeMaskForResult, hresultT, cachedProbeMask, k.is_lt, dite_true,
              show (⟨k.1, k.is_lt⟩ : Fin n) = k from rfl, show k ≠ i from hk.1, hpermT]
          have hrem_eq : (plannedTxn s i .acquirePerm grow source).probesRemaining k.1 =
              (probeMaskForResult s i grow.result) k.1 := by
            simp [plannedTxn]
          rw [hrem_eq, hmask] at hrem
          exact absurd hrem (by decide)
        · exfalso; revert huds; simp [plannedTxn, plannedUsedDirtySource, dirtyOwnerOpt, dif_neg hex]
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

theorem releaseDataInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hdata : dataCoherenceInv n s)
    (hrelData : releaseDataInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    releaseDataInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, rfl⟩
      intro htxn' j hflight hperm hdirty
      simp only [setFn] at *
      by_cases hji : j = i <;> simp_all [releaseDataInv]
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, rfl⟩
      intro htxn' j hflight hperm hdirty
      simp only [setFn] at *
      by_cases hji : j = i <;> simp_all [releaseDataInv]
  | .recvAcquireAtManager =>
      -- currentTxn → some → guard false
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
        intro htxn'; simp [recvAcquireState, recvAcquireShared] at htxn'
      · rcases hperm with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
        intro htxn'; simp [recvAcquireState, recvAcquireShared] at htxn'
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, _, hcur, _, _, _, _, _, _, _, ⟨_, rfl⟩⟩
      intro htxn'; simp [recvProbeState, hcur] at htxn'
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, _, hcur, _, _, _, _, _, _, rfl⟩
      intro htxn'; simp [recvProbeAckState, recvProbeAckShared, hcur] at htxn'
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, _, _, _, _, _, _, _, rfl⟩
      intro htxn'; simp [sendGrantState, sendGrantShared, hcur] at htxn'
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, _, hcur, _, _, _, _, _, _, _, _, rfl⟩
      intro htxn'; simp [recvGrantState, recvGrantShared, hcur] at htxn'
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, _, hcur, _, _, _, _, _, _, _, rfl⟩
      sorry -- currentTxn some→none; needs: all releaseInFlight = false during txn
  | .sendRelease param =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, _, hflight_pre, _, hdirty_pre, _, hs'⟩
      subst hs'
      intro htxn' j hflight hperm hdirty
      by_cases hji : j = i
      · subst hji
        sorry -- KEY INIT: use dataCoherenceInv pre-state; releasedLine preserves data for TtoB
      · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] at hflight hperm hdirty ⊢
        exact hrelData htxn j hflight hperm hdirty
  | .sendReleaseData param =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'
      intro htxn' j hflight hperm hdirty
      by_cases hji : j = i
      · subst hji; sorry -- dirty release: releasedLine TtoN → perm .N vacuous; TtoB → need data=mem
      · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] at hflight hperm hdirty ⊢
        exact hrelData htxn j hflight hperm hdirty
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, htxn, _, _, hflight_i, _, _, _, _, _, _, hs'⟩
      subst hs'
      intro htxn' j hflight hperm hdirty
      simp [recvReleaseState, recvReleaseShared] at htxn'
      by_cases hji : j = i
      · subst hji
        simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn] at hflight hperm hdirty ⊢
        sorry -- needs: mem changes via releaseWriteback; for clean release mem unchanged; for dirty release use channel invariant
      · simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji] at hflight hperm hdirty ⊢
        sorry -- needs: no other node j≠i has releaseInFlight=true at recvRelease (single-release constraint)
  | .recvReleaseAckAtMaster =>
      -- Node i: releaseInFlight cleared → guard false. Others: unchanged.
      rcases hstep with ⟨msg, htxn, _, _, hflight_i, _, _, hs'⟩
      subst hs'
      intro htxn' j hflight hperm hdirty
      simp [recvReleaseAckState, recvReleaseAckShared] at htxn'
      by_cases hji : j = i
      · subst hji
        simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn] at hflight
      · simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji] at hflight hperm hdirty ⊢
        exact hrelData htxn j hflight hperm hdirty
  | .store v =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      intro htxn' j hflight hperm hdirty
      simp only [setFn] at *
      by_cases hji : j = i <;> simp_all [releaseDataInv, storeLocal]
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩; exact hrelData
  | .uncachedGet source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
      sorry -- uncached ops: check if currentTxn changes or releaseInFlight affected
  | .uncachedPut source v =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
      sorry
  | .recvUncachedAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      sorry
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩; sorry -- should be trivial: no release state changes

end TileLink.Messages
