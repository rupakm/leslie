import Leslie.Examples.Combinators.QuorumSystem

/-! ## Lock Invariant Combinator

    The lock invariant pattern: if a value has quorum support (its "holders"
    form a quorum), then that value is unique. This captures the core safety
    argument shared by OneThirdRule, Paxos, and many voting-based protocols.
-/

namespace TLA.Combinator

/-! ### Lock Property -/

/-- A lock property parameterized by a quorum system: a value `v` is "locked"
    when its holders form a quorum. The `holders` function extracts, for each
    value, which processes currently "hold" that value (e.g., voted for it,
    store it, etc.). -/
structure LockProperty (n : Nat) (S V : Type) where
  /-- The underlying quorum system. -/
  qs : QuorumSystem n
  /-- Which processes hold value `v` given the array of local states. -/
  holders : V → (Fin n → S) → Fin n → Bool

/-- Value `v` is locked when its holders form a quorum. -/
def LockProperty.isLocked (lp : LockProperty n S V) (v : V) (locals : Fin n → S) : Prop :=
  lp.qs.isQuorum (lp.holders v locals)

/-! ### Lock Uniqueness -/

/-- **Two different values cannot both be locked**, provided holders are
    disjoint for distinct values (i.e., no process holds two different values
    simultaneously). This is the core pigeonhole/quorum-intersection argument.

    Proof: if `v` and `w` are both locked, their holder sets are both quorums.
    By `QuorumSystem.intersection`, some process `i` is in both. But the
    disjointness hypothesis says no process can hold both `v` and `w`. -/
theorem lock_unique {n : Nat} {S V : Type}
    (lp : LockProperty n S V)
    (h_disj : ∀ v w locals i, v ≠ w →
      ¬(lp.holders v locals i = true ∧ lp.holders w locals i = true))
    (v w : V) (locals : Fin n → S)
    (hv : lp.isLocked v locals) (hw : lp.isLocked w locals) : v = w := by
  by_contra hne
  obtain ⟨i, hi_v, hi_w⟩ := lp.qs.intersection _ _ hv hw
  exact h_disj v w locals i hne ⟨hi_v, hi_w⟩

/-- Variant with `DecidableEq V`: the disjointness condition is stated
    more concretely as "each process holds at most one value". -/
theorem lock_unique' {n : Nat} {S V : Type} [DecidableEq V]
    (lp : LockProperty n S V)
    (h_func : ∀ v w locals (i : Fin n),
      lp.holders v locals i = true → lp.holders w locals i = true → v = w)
    (v w : V) (locals : Fin n → S)
    (hv : lp.isLocked v locals) (hw : lp.isLocked w locals) : v = w := by
  by_contra hne
  obtain ⟨i, hi_v, hi_w⟩ := lp.qs.intersection _ _ hv hw
  exact hne (h_func v w locals i hi_v hi_w)

end TLA.Combinator
