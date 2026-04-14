import Leslie.Examples.Combinators.LockInvariant
import Leslie.Round

/-! ## Threshold Consensus via Combinator Pattern

    A round-based consensus protocol demonstrating the combinator pattern from
    `QuorumSystem.lean` and `LockInvariant.lean`. This is essentially the
    OneThirdRule algorithm, but the safety proof factors through reusable
    abstractions:

    - `thresholdQuorum` provides the quorum intersection property
    - `LockProperty` + `lock_unique` provide the pigeonhole argument

    The key payoff: the pigeonhole argument ("two super-majorities can't
    coexist for different values") comes FOR FREE from `lock_unique` composed
    with `thresholdQuorum.intersection`, rather than being proved from scratch.

    ### Protocol

    Each process holds a value (0 or 1) and optionally a decision. In each
    round:
    1. Broadcast current value
    2. Receive values from HO set (≥ 2n/3 + 1 messages guaranteed)
    3. If > 2n/3 received values agree on v: adopt v, decide v
    4. Otherwise: keep current value

    ### Safety: Agreement

    If two processes decided, they decided the same value.

    Proof: decision implies a super-majority lock. By `lock_unique` (from
    `LockInvariant.lean`), at most one value can be locked. QED.
-/

open TLA TLA.Combinator

namespace ThresholdConsensus

variable (n : Nat)

/-! ### Value type -/

/-- Two-element value type for consensus. -/
inductive Value where
  | zero
  | one
  deriving DecidableEq, Repr

/-! ### Local state -/

/-- Each process holds a value and optionally a decision. -/
structure LocalState where
  val : Value
  decided : Option Value
  deriving DecidableEq, Repr

/-! ### Counting helpers -/

/-- Count occurrences of value `v` in a list. -/
def countVal (v : Value) (l : List Value) : Nat :=
  (l.filter (· == v)).length

/-- Does value `v` have a super-majority (> 2n/3) in the list? -/
def hasSuperMaj (v : Value) (l : List Value) : Bool :=
  countVal v l * 3 > 2 * n

/-- Find a value with super-majority, if one exists. -/
def findSuperMaj (l : List Value) : Option Value :=
  l.find? (fun v => hasSuperMaj n v l)

/-! ### Algorithm definition -/

/-- The threshold consensus algorithm as a `RoundAlg`. -/
def tcAlg : RoundAlg (Fin n) LocalState Value where
  init := fun _p s => s.decided = none
  send := fun _p s => s.val
  update := fun _p s msgs =>
    let received := (List.finRange n).filterMap msgs
    match findSuperMaj n received with
    | some v => { val := v, decided := some v }
    | none => s

/-! ### Communication predicate: > 2n/3 delivery -/

/-- Every process hears from more than 2n/3 senders in every round. -/
def commTwoThirds : CommPred (Fin n) :=
  fun _r ho => ∀ p : Fin n,
    ((List.finRange n).filter fun q => ho p q).length * 3 > 2 * n

/-- The complete round specification. -/
def tcSpec : RoundSpec (Fin n) LocalState Value where
  alg := tcAlg n
  comm := commTwoThirds n

/-! ### Safety property -/

/-- Agreement: all decided processes agree. -/
def agreement (s : RoundState (Fin n) LocalState) : Prop :=
  ∀ p q v w,
    (s.locals p).decided = some v →
    (s.locals q).decided = some w →
    v = w

/-! ### Lock property via combinators -/

/-- Count how many processes hold value `v`. -/
def countHolding (v : Value) (s : RoundState (Fin n) LocalState) : Nat :=
  ((List.finRange n).filter fun p =>
    decide ((s.locals p).val = v)).length

/-- The lock property instance: a value is "locked" when > 2n/3 processes
    hold it. Uses `thresholdQuorum` from `QuorumSystem.lean`. -/
def tcLock : LockProperty n LocalState Value where
  qs := thresholdQuorum n 2 3 (by omega) (by omega)
  holders := fun v locals i => decide ((locals i).val = v)

/-- `tcLock.isLocked v locals` iff `countHolding v` forms a 2/3 quorum. -/
theorem tcLock_isLocked_iff (v : Value) (locals : Fin n → LocalState) :
    (tcLock n).isLocked v locals ↔
    countTrue (fun i => decide ((locals i).val = v)) * 3 > 2 * n := by
  simp [tcLock, LockProperty.isLocked, thresholdQuorum]

/-- Holders are disjoint for distinct values: no process can hold two
    different values simultaneously. -/
theorem holders_disjoint :
    ∀ v w : Value, ∀ locals : Fin n → LocalState, ∀ i : Fin n,
    v ≠ w → ¬((tcLock n).holders v locals i = true ∧
               (tcLock n).holders w locals i = true) := by
  intro v w locals i hne ⟨hv, hw⟩
  simp [tcLock, decide_eq_true_eq] at hv hw
  rw [hv] at hw; exact hne hw

/-! ### Agreement from lock_unique — THE KEY PAYOFF -/

/-- **Agreement from lock uniqueness**: if two values are both locked
    (have > 2n/3 support), they must be the same value.

    This is the pigeonhole argument, obtained FOR FREE from `lock_unique`. -/
theorem locked_values_agree (v w : Value)
    (locals : Fin n → LocalState)
    (hv : (tcLock n).isLocked v locals)
    (hw : (tcLock n).isLocked w locals) : v = w :=
  lock_unique (tcLock n) (holders_disjoint n) v w locals hv hw

/-! ### The lock invariant -/

/-- If any process has decided `v`, then `v` is locked (> 2n/3 hold it). -/
def lockInv (s : RoundState (Fin n) LocalState) : Prop :=
  ∀ v, (∃ p : Fin n, (s.locals p).decided = some v) →
    (tcLock n).isLocked v (s.locals)

/-- Lock invariant implies agreement, using `locked_values_agree`. -/
theorem lockInv_implies_agreement (s : RoundState (Fin n) LocalState)
    (h : lockInv n s) : agreement n s := by
  intro p q v w hv hw
  exact locked_values_agree n v w s.locals (h v ⟨p, hv⟩) (h w ⟨q, hw⟩)

/-! ### Helper lemmas for induction -/

/-- `findSuperMaj` returning `some v` implies `v` has a super-majority. -/
theorem findSuperMaj_spec {l : List Value} {v : Value}
    (h : findSuperMaj n l = some v) :
    hasSuperMaj n v l = true := by
  simp only [findSuperMaj] at h
  exact List.find?_some (p := fun v => hasSuperMaj n v l) h

/-- Votes for `w` in received messages ≤ total `w`-holders globally.
    Each received vote came from a distinct sender holding `w`. -/
theorem countVal_le_countTrue
    (s : RoundState (Fin n) LocalState) (ho : HOCollection (Fin n))
    (p : Fin n) (w : Value) :
    countVal w ((List.finRange n).filterMap
      (fun r => if ho p r then some (s.locals r).val else none)) ≤
    countTrue (fun i : Fin n => decide ((s.locals i).val = w)) := by
  simp only [countVal, countTrue]
  apply filterMap_filter_count_le
  intro r hr
  simp only [decide_eq_true_eq]
  by_cases hho : ho p r = true
  · simp [hho] at hr; exact hr
  · have hf : ho p r = false := by revert hho; cases ho p r <;> simp
    simp [hf] at hr

/-- No competing super-majority: if `v` is locked, no `w ≠ v` can have
    a super-majority in any process's received messages. -/
theorem no_competing_supermaj
    (s : RoundState (Fin n) LocalState) (ho : HOCollection (Fin n))
    (p : Fin n) (v w : Value) (hne : w ≠ v)
    (hlock : (tcLock n).isLocked v (s.locals)) :
    ¬ (hasSuperMaj n w
        ((List.finRange n).filterMap
          (fun r => if ho p r then some (s.locals r).val else none)) = true) := by
  intro hsm
  simp only [hasSuperMaj, decide_eq_true_eq] at hsm
  have hle_w := countVal_le_countTrue n s ho p w
  -- Both v and w would be locked — contradiction via lock_unique
  have hw_locked : (tcLock n).isLocked w (s.locals) := by
    simp [tcLock, LockProperty.isLocked, thresholdQuorum]
    calc 2 * n < countVal w _ * 3 := by omega
      _ ≤ countTrue (fun i => decide ((s.locals i).val = w)) * 3 :=
        Nat.mul_le_mul_right 3 hle_w
  exact hne (locked_values_agree n w v s.locals hw_locked hlock)

/-! ### The lock is inductive -/

/-- Initially no process has decided, so the lock holds vacuously. -/
theorem lockInv_init :
    ∀ s, (tcSpec n).toSpec.init s → lockInv n s := by
  intro s ⟨_, hinit⟩ v ⟨p, hp⟩
  have := hinit p
  simp only at this
  rw [this] at hp; simp at hp

/-- **The lock is preserved across rounds.**

    Step (a): Establish the lock in s (from new decision or IH).
    Step (b): Every v-holder in s still holds v in s'.
    Step (c): Count doesn't decrease. -/
theorem lockInv_step :
    ∀ s ho, lockInv n s → (tcSpec n).comm s.round ho →
    ∀ s', round_step (tcAlg n) ho s s' → lockInv n s' := by
  intro s ho hinv _hcomm s' ⟨_, hlocals⟩
  intro v ⟨p, hp⟩
  -- Simplify delivered messages
  have delivered_eq : ∀ q r, delivered (tcAlg n) s ho q r =
      (if ho q r then some (s.locals r).val else none) := by
    intro q r; simp only [delivered, tcAlg]
  have hlocals_expanded : ∀ q, s'.locals q =
      match findSuperMaj n ((List.finRange n).filterMap
        (fun r => if ho q r then some (s.locals r).val else none)) with
      | some w => { val := w, decided := some w }
      | none => s.locals q := by
    intro q
    have := hlocals q
    simp only [tcAlg] at this
    rw [this]; congr 2
  -- ── Step (a): Establish the lock in s ──
  have lock_in_s : (tcLock n).isLocked v (s.locals) := by
    have hp' := hlocals_expanded p
    rw [hp'] at hp
    split at hp
    · -- p newly decided v' in this round
      case h_1 v' hfind =>
      simp only at hp
      have hv' : v' = v := Option.some.inj hp
      rw [← hv']
      -- v' had super-majority in p's received messages
      have hsm := findSuperMaj_spec n hfind
      simp only [hasSuperMaj, decide_eq_true_eq] at hsm
      -- Lift to global lock
      simp [tcLock, LockProperty.isLocked, thresholdQuorum]
      calc 2 * n < countVal v' _ * 3 := by omega
        _ ≤ countTrue (fun i => decide ((s.locals i).val = v')) * 3 :=
          Nat.mul_le_mul_right 3 (countVal_le_countTrue n s ho p v')
    · -- p already had decided = some v from state s
      case h_2 hfind =>
      exact hinv v ⟨p, hp⟩
  -- ── Step (b): Every v-holder in s still holds v in s' ──
  have h_preserved : ∀ q : Fin n,
      (s.locals q).val = v → (s'.locals q).val = v := by
    intro q hq_val
    rw [hlocals_expanded q]
    split
    · -- findSuperMaj returned some w for q — show w = v
      case h_1 w hfind_q =>
      simp only
      by_contra hne
      exact no_competing_supermaj n s ho q v w hne lock_in_s
        (findSuperMaj_spec n hfind_q)
    · -- findSuperMaj returned none — q keeps its value v
      case h_2 hfind_q =>
      exact hq_val
  -- ── Step (c): Count doesn't decrease → lock preserved in s' ──
  simp [tcLock, LockProperty.isLocked, thresholdQuorum]
  simp [tcLock, LockProperty.isLocked, thresholdQuorum] at lock_in_s
  have h_mono := filter_length_mono (List.finRange n)
    (fun q => decide ((s.locals q).val = v))
    (fun q => decide ((s'.locals q).val = v))
    (by intro q hq
        simp [decide_eq_true_eq] at hq ⊢
        exact h_preserved q hq)
  simp only [countTrue] at lock_in_s ⊢
  omega

/-! ### Main safety theorem -/

/-- **Threshold consensus satisfies agreement.**

    Proof structure:
    1. `lockInv` is inductive (via `round_invariant`)
    2. `lockInv` implies agreement (via `lockInv_implies_agreement`)
    3. The agreement proof uses `lock_unique` from the combinator library

    Compare with `OneThirdRule.otr_agreement`: the pigeonhole argument
    (`super_majority_unique`) is replaced by `lock_unique` + `thresholdQuorum`. -/
theorem tc_agreement :
    pred_implies (tcSpec n).toSpec.safety
      [tlafml| □ ⌜agreement n⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜lockInv n⌝])
  · apply round_invariant
    · exact lockInv_init n
    · exact lockInv_step n
  · apply always_monotone
    intro e h
    exact lockInv_implies_agreement n (e 0) h

end ThresholdConsensus
