import Leslie.Examples.CacheCoherence.TileLink.Messages.Liveness.Defs
import Leslie.Rules.WF
import Leslie.Rules.LeadsTo

/-! ## Per-Step Leads-To Lemmas for TileLink Liveness

    Each step in the acquire wave is proved to eventually complete using
    the WF1 rule. These are composed into the full liveness theorem in
    `Theorem.lean`.
-/

namespace TileLink.Messages.Liveness

open TLA TileLink SymShared

/-! ### Step: grantReady ↝ grantPendingAck

    When the transaction is at grantReady and the sendGrant action is
    weakly fair, the grant is eventually sent. -/

/-- At grantReady, the sendGrant action for the requester is enabled. -/
theorem sendGrant_enabled_at_grantReady {n : Nat}
    {s : SymState HomeState NodeState n}
    (hfull : fullInv n s)
    (hready : Liveness.grantReady n s) :
    enabled (actSendGrantToRequester n ⟨(hready.choose).requester,
      by rcases hfull with ⟨⟨_, _, _, htxnCore⟩, _, _⟩
         rcases hready with ⟨tx, hcur, _⟩
         simpa [txnCoreInv, hcur] using htxnCore⟩) s := by
  sorry

/-- Once at grantReady, under fairness of sendGrant, we reach grantPendingAck. -/
theorem grantReady_leads_to_grantPendingAck (n : Nat) :
    (□ ⟨(tlMessages.toSpec n).next⟩ ∧
     ⋀ i ∈ (List.finRange n).map fun j => actSendGrantToRequester n j, 𝒲ℱ i)
    |-tla- (state_pred (Liveness.grantReady n) ↝
            state_pred (Liveness.grantPendingAck n)) := by
  sorry

end TileLink.Messages.Liveness
