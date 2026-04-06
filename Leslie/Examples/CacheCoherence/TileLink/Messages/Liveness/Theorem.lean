import Leslie.Examples.CacheCoherence.TileLink.Messages.Liveness.Steps

/-! ## Liveness Composition: Acquire Eventually Completes

    The main liveness theorem: under weak fairness of all protocol actions,
    every acquire request eventually completes.

    The proof composes per-step leads-to lemmas via `leads_to_trans`.
    Each per-step lemma is proved via WF1 in Steps.lean.

    The acquire wave phase chain:

    ```
    acquirePending
      ↝ txnActive (recvAcquire consumes chanA, creates txn)
      ↝ grantReady (probing terminates: well-founded induction on remaining probes)
      ↝ grantPendingAck (sendGrant fires)
      ↝ txnComplete (recvGrant + recvGrantAck)
    ```
-/

namespace TileLink.Messages.Liveness

open TLA TileLink SymShared

/-! ### State predicates lifted to TLA predicates -/

def txnActiveForI (n : Nat) (i : Fin n) : pred (SymState HomeState NodeState n) :=
  state_pred (fun s => ∃ tx, s.shared.currentTxn = some tx ∧ tx.requester = i.1)

def chanAPending (n : Nat) (i : Fin n) : pred (SymState HomeState NodeState n) :=
  state_pred (fun s => (s.locals i).chanA ≠ none)

def tlGrantReady (n : Nat) : pred (SymState HomeState NodeState n) :=
  state_pred (grantReady n)

def tlGrantPendingAck (n : Nat) : pred (SymState HomeState NodeState n) :=
  state_pred (grantPendingAck n)

def probingOrReady (n : Nat) : pred (SymState HomeState NodeState n) :=
  state_pred (fun s => ∃ tx, s.shared.currentTxn = some tx ∧
    (tx.phase = .probing ∨ tx.phase = .grantReady))

def grantAckOnChanE (n : Nat) : pred (SymState HomeState NodeState n) :=
  state_pred (fun s => ∃ i : Fin n, (s.locals i).chanE ≠ none)

def txnDone (n : Nat) : pred (SymState HomeState NodeState n) :=
  state_pred (fun s => s.shared.currentTxn = none)

def tlAcquirePending (n : Nat) (i : Fin n) : pred (SymState HomeState NodeState n) :=
  state_pred (acquirePending n i)

def tlAcquireComplete (n : Nat) (i : Fin n) : pred (SymState HomeState NodeState n) :=
  state_pred (acquireComplete n i)

/-! ### Helper: chain leads-to under a hypothesis -/

private theorem chain2 {Γ p q r : pred σ}
    (h1 : pred_implies Γ (leads_to p q))
    (h2 : pred_implies Γ (leads_to q r)) :
    pred_implies Γ (leads_to p r) :=
  fun e hΓ => leads_to_trans p q r e (h1 e hΓ) (h2 e hΓ)


/-! ### Per-step leads-to lemmas

    Each is proved by applying WF1 with the appropriate fair action.
    The WF1 premises are:
    1. Safety: p ∧ next ⇒ ◯p ∨ ◯q (stuttering or progress)
    2. Progress: p ∧ next ∧ a ⇒ ◯q (the fair action advances)
    3. Enablement: p ⇒ Enabled(a) ∨ q
    4. Fairness: □⟨next⟩ ∧ WF(a) -/

/-- Step 1: An acquire on chanA is eventually consumed by the manager.
    Fair action: recvAcquireAtManager for i. -/
theorem chanA_leads_to_txnActive (n : Nat) (i : Fin n) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (chanAPending n i) (txnActiveForI n i)) := by
  sorry

/-- Step 2: During probing, probes are eventually consumed.
    Uses well-founded induction on |{j | probesRemaining j = true}|.
    Each iteration uses WF1 on recvProbeAtMaster or recvProbeAckAtManager. -/
theorem probing_leads_to_grantReady (n : Nat) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (probingOrReady n) (tlGrantReady n)) := by
  sorry

/-- Step 3: At grantReady, the grant is sent to the requester.
    Fair action: sendGrantToRequester.
    Relies on sendGrant_enabled from Steps.lean. -/
theorem grantReady_leads_to_grantPendingAck (n : Nat) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (tlGrantReady n) (tlGrantPendingAck n)) := by
  sorry

/-- Step 4a: At grantPendingAck, the requester receives the grant.
    Fair action: recvGrantAtMaster for the requester.
    Relies on recvGrant_enabled from Steps.lean. -/
theorem grantPendingAck_leads_to_grantAckSent (n : Nat) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (tlGrantPendingAck n) (grantAckOnChanE n)) := by
  sorry

/-- Step 4b: The grantAck is received by the manager, completing the transaction.
    Fair action: recvGrantAckAtManager. -/
theorem grantAckSent_leads_to_txnComplete (n : Nat) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (grantAckOnChanE n) (txnDone n)) := by
  sorry

/-! ### Composed chains -/

/-- The grant wave completes: grantReady ↝ txnDone.
    Chains steps 3, 4a, 4b via leads_to_trans. -/
theorem grantReady_leads_to_txnDone (n : Nat) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (tlGrantReady n) (txnDone n)) :=
  chain2 (grantReady_leads_to_grantPendingAck n)
    (chain2 (grantPendingAck_leads_to_grantAckSent n)
      (grantAckSent_leads_to_txnComplete n))

/-- From probing/grantReady to txnDone.
    Chains steps 2, 3, 4a, 4b. -/
theorem probingOrReady_leads_to_txnDone (n : Nat) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (probingOrReady n) (txnDone n)) :=
  chain2 (probing_leads_to_grantReady n) (grantReady_leads_to_txnDone n)

/-! ### Main composition -/

/-- txnActiveForI implies probingOrReady ∨ grantPendingAck.
    From txnCoreInv: phase ∈ {probing, grantReady, grantPendingAck}. -/
theorem txnActive_leads_to_txnDone (n : Nat) (i : Fin n) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (txnActiveForI n i) (txnDone n)) := by
  sorry
  -- Sketch: txnActiveForI → probingOrReady ∨ grantPendingAck (from txnCoreInv)
  -- Case probing/ready: use probingOrReady_leads_to_txnDone
  -- Case grantPendingAck: use chain2 grantPendingAck_leads_to_grantAckSent + txnComplete

/-- The full acquire wave completes under weak fairness.
    Every acquire request eventually leads to a completed transaction. -/
theorem acquire_leads_to_txnDone (n : Nat) (i : Fin n) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (tlAcquirePending n i) (txnDone n)) := by
  sorry
  -- Sketch: acquirePending = chanAPending ∨ txnActiveForI
  -- chanAPending ↝ txnActiveForI (step 1)
  -- txnActiveForI ↝ txnDone (above)
  -- Chain via leads_to_trans

end TileLink.Messages.Liveness
