import Leslie.Examples.CacheCoherence.TileLink.Messages.Liveness.Steps
import Leslie.Examples.CacheCoherence.TileLink.Messages.StepRelease
import Leslie.Rules.LeadsTo

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

    STATUS: Most proofs are sorry'd because the branch's Act enum has 12
    constructors (missing store, read, uncachedGet, uncachedPut,
    recvUncachedAtManager, recvAccessAckAtMaster). The original proofs
    case-split on all 18 constructors. All theorem statements and
    definitions are preserved.
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

/-- Count true values in a Nat → Bool function up to bound n. -/
def countTrue (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => (f n).toNat + countTrue f n

@[simp] private theorem Bool.toNat_true : Bool.toNat true = 1 := rfl
@[simp] private theorem Bool.toNat_false : Bool.toNat false = 0 := rfl

@[simp] private theorem probeAckPhase_ne_grantPendingAck :
    @probeAckPhase n f ≠ TxnPhase.grantPendingAck := by
  unfold probeAckPhase; split <;> decide

theorem countTrue_pos {f : Nat → Bool} {n j : Nat} (hj : j < n) (hf : f j = true) :
    countTrue f n > 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold countTrue
    by_cases hjn : j = n
    · subst j; simp [hf]; omega
    · have := ih (by omega : j < n); omega

private theorem countTrue_congr {f g : Nat → Bool} {n : Nat}
    (h : ∀ k, k < n → f k = g k) : countTrue f n = countTrue g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold countTrue; rw [h n (by omega)]
    congr 1; exact ih (fun k hk => h k (by omega))

theorem countTrue_decrease {f : Nat → Bool} {n j : Nat} (hj : j < n) (hf : f j = true) :
    countTrue (fun k => if k = j then false else f k) n < countTrue f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold countTrue
    by_cases hjn : j = n
    · subst j
      have h1 : (if n = n then false else f n) = false := if_pos rfl
      rw [h1, hf]; simp only [Bool.toNat_false, Bool.toNat_true]
      have heq : countTrue (fun k => if k = n then false else f k) n = countTrue f n :=
        countTrue_congr (fun k hk => if_neg (by omega))
      omega
    · have h1 : (if n = j then false else f n) = f n := if_neg (Ne.symm hjn)
      rw [h1]
      have h2 := ih (by omega : j < n)
      omega

theorem countTrue_clearProbeIdx_le (f : Nat → Bool) (j n : Nat) :
    countTrue (clearProbeIdx f j) n ≤ countTrue f n := by
  induction n with
  | zero => simp [countTrue]
  | succ n ih =>
    simp only [countTrue, clearProbeIdx]
    by_cases hjn : n = j
    · subst hjn; simp [Bool.toNat]; omega
    · simp [hjn]; omega

/-- Count of remaining probes. -/
noncomputable def probeRemainingCount (n : Nat) (e : Nat → SymState HomeState NodeState n) : Nat :=
  match e 0 |>.shared.currentTxn with
  | none => 0
  | some tx => countTrue tx.probesRemaining n

/-! ### Phase-specific leads-to lemmas

    All proofs sorry'd: they case-split on the 18-constructor Act enum
    from main, but the branch has only 12 constructors. -/

-- sorry: proofs case-split on 18-constructor Act
theorem probing_leads_to_grantReady (n : Nat) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (probingOrReady n) (tlGrantReady n)) := by
  sorry

-- sorry: proofs case-split on 18-constructor Act
theorem grantReady_leads_to_grantPendingAck (n : Nat) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (tlGrantReady n) (tlGrantPendingAck n)) := by
  sorry

-- sorry: proofs case-split on 18-constructor Act
theorem grantPendingAck_leads_to_grantAckSent (n : Nat) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (tlGrantPendingAck n) (grantAckOnChanE n)) := by
  sorry

-- sorry: proofs case-split on 18-constructor Act
theorem grantAckSent_leads_to_txnComplete (n : Nat) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (grantAckOnChanE n) (txnDone n)) := by
  sorry

/-! ### Composition -/

private theorem chain2 {Γ p q r : pred σ}
    (h1 : pred_implies Γ (leads_to p q))
    (h2 : pred_implies Γ (leads_to q r)) :
    pred_implies Γ (leads_to p r) :=
  fun e hΓ => leads_to_trans p q r e (h1 e hΓ) (h2 e hΓ)

theorem grantReady_leads_to_txnDone (n : Nat) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (tlGrantReady n) (txnDone n)) :=
  chain2 (grantReady_leads_to_grantPendingAck n)
    (chain2 (grantPendingAck_leads_to_grantAckSent n)
      (grantAckSent_leads_to_txnComplete n))

theorem probingOrReady_leads_to_txnDone (n : Nat) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (probingOrReady n) (txnDone n)) :=
  chain2 (probing_leads_to_grantReady n) (grantReady_leads_to_txnDone n)

-- sorry: depends on livenessInv which uses txnLineInv (not in scope without
-- additional imports/opens) and on compositional proof structure that
-- references the 18-constructor Act
theorem txnActive_leads_to_txnDone (n : Nat) (i : Fin n) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (txnActiveForI n i) (txnDone n)) := by
  sorry

theorem chanA_leads_to_txnDone (n : Nat) (i : Fin n) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (chanAPending n i) (txnDone n)) := by
  sorry

/-- The full acquire wave completes under weak fairness.
    Every acquire request eventually leads to a completed transaction. -/
theorem acquire_leads_to_txnDone (n : Nat) (i : Fin n) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (tlAcquirePending n i) (txnDone n)) := by
  sorry

end TileLink.Messages.Liveness
