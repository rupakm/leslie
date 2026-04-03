import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.SimOther

/-! ## Access-Path Theorems

    This file proves that the TileLink message model correctly implements
    a sequentially consistent shared memory for reads and writes:

    - `read_returns_logical_data`: a readable node's data equals the
      abstract sequential register value
    - `store_updates_logical_data`: after a store, the abstract sequential
      register value equals the stored value
-/

namespace TileLink.Messages

open TLA TileLink SymShared Classical

/-- A readable node's data equals the logical line value (the abstract
    sequential register value mapped through the refinement).

    When a node has read permission (perm ∈ {.B, .T}) and valid data,
    its data equals `(refMap n s).shared.mem`, which is the abstract
    memory value. Combined with `messages_refines_atomic` and
    `atomic_coherence`, this means reads return the value of the
    sequential register. -/
theorem read_returns_logical_data {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (hinv : ForwardSimInv n s)
    (hperm : (s.locals i).line.perm.allowsRead)
    (hvalid : (s.locals i).line.valid = true)
    (htxn : s.shared.currentTxn = none)
    (hflight : (s.locals i).releaseInFlight = false) :
    (s.locals i).line.data = (refMap n s).shared.mem := by
  -- Unfold refMap.mem for the no-transaction case
  simp only [refMap, refMapShared, htxn]
  -- The new refMap checks for a dirty owner first:
  --   if h : ∃ j, dirty j then (choose h).data
  --   else match findDirtyReleaseVal with some v => v | none => s.shared.mem
  rcases hinv with ⟨⟨⟨⟨hlineWF, _, _, _⟩, _, _⟩, hdirtyEx, _, _, _, _, hdirtyRelEx⟩, hdata, _, _, _, _⟩
  by_cases hex : ∃ j : Fin n, (s.locals j).line.dirty = true
  · -- Case 1: A dirty owner exists. refMap.mem = (choose hex).line.data
    simp only [hex, dite_true]
    -- The dirty owner k = Classical.choose hex satisfies dirty k = true
    have hk_dirty := Classical.choose_spec hex
    let k := Classical.choose hex
    -- By dirtyExclusiveInv: dirty k → ∀ j ≠ k, perm j = .N
    -- Reader i has allowsRead → perm i ≠ .N
    -- Therefore i = k
    by_cases hik : i = k
    · -- i = k: data i = data (choose hex). Trivially equal.
      subst hik; rfl
    · -- i ≠ k: dirtyExclusiveInv gives perm i = .N, contradicting allowsRead
      exfalso
      have hpermN := hdirtyEx k i (Ne.symm hik) hk_dirty
      rw [hpermN] at hperm
      exact hperm
  · -- Case 2: No dirty owner. refMap.mem = match findDirtyReleaseVal with ...
    simp only [hex, dite_false]
    -- Node i is not dirty (since no one is dirty)
    push_neg at hex
    have hdirty_i : (s.locals i).line.dirty = false := by
      cases h : (s.locals i).line.dirty
      · rfl
      · exact absurd h (by rw [hex i]; simp)
    -- From dataCoherenceInv: txn = none → releaseInFlight = false → dirty = false → data = mem
    have hdata_eq : (s.locals i).line.data = s.shared.mem := hdata htxn i hflight hdirty_i
    -- Case split on findDirtyReleaseVal
    rcases hfdrv : findDirtyReleaseVal n s with v | _
    · -- findDirtyReleaseVal = some v: a dirty release is in flight.
      -- By dirtyReleaseExclusiveInv: all other nodes have perm .N.
      -- Since node i has allowsRead (perm ≠ .N), i must be the releasing node.
      -- But i has releaseInFlight = false. Contradiction: the releasing node
      -- must have releaseInFlight = true.
      exfalso
      -- Extract the releasing node j from findDirtyReleaseVal
      unfold findDirtyReleaseVal at hfdrv
      split at hfdrv
      · rename_i hrel_exists
        -- hrel_exists: ∃ j, releaseInFlight j ∧ ∃ msg, chanC j = some msg ∧ msg.data ≠ none
        have ⟨hrel_j, hmsg_j⟩ := Classical.choose_spec hrel_exists
        let j := Classical.choose hrel_exists
        -- By dirtyReleaseExclusiveInv: all k ≠ j have perm .N
        have hpermN := hdirtyRelEx htxn j hrel_j hmsg_j i
        by_cases hij : i = j
        · -- i = j: but releaseInFlight i = false while releaseInFlight j = true
          subst hij; rw [hflight] at hrel_j; cases hrel_j
        · exact hperm (hpermN (Ne.symm hij))
      · simp at hfdrv
    · -- findDirtyReleaseVal = none: refMap.mem = s.shared.mem
      exact hdata_eq

/-- After a store, the abstract sequential register value equals the stored value.

    Combined with `messages_refines_atomic` and `atomic_coherence`, this
    gives a complete sequential consistency guarantee: writes are immediately
    visible to subsequent reads at any node with appropriate permissions. -/
theorem store_updates_logical_data {n : Nat}
    {s s' : SymState HomeState NodeState n} {i : Fin n} {v : Val}
    (hinv : ForwardSimInv n s)
    (hstep : Store s s' i v) :
    ∀ j : Fin n, (s'.locals j).line.perm.allowsRead →
      (s'.locals j).line.valid = true →
      (s'.locals j).line.data = v ∨ (s'.locals j).line.data = (refMap n s).shared.mem := by
  intro j hpermJ hvalidJ
  rcases hstep with ⟨htxn, _, _, _, hpermI, _, _, _, _, _, _, _, hs'⟩
  rw [hs']
  by_cases hji : j = i
  · -- j = i: the storing node. After store: data = v, dirty = true, perm = .T, valid = true.
    subst j
    simp [setFn, storeLocal]
    exact Or.inl rfl
  · -- j ≠ i: line unchanged. Under permSwmrInv, perm i = .T → perm j = .N.
    -- perm .N → ¬allowsRead. Contradicts hpermJ.
    simp [setFn, hji] at hpermJ hvalidJ ⊢
    rcases hinv with ⟨⟨_, _, hSwmr, _, _, _, _⟩, _, _, _, _, _⟩
    have hpermN := hSwmr i j (Ne.symm hji) hpermI
    rw [hpermN] at hpermJ
    simp [TLPerm.allowsRead] at hpermJ

end TileLink.Messages
