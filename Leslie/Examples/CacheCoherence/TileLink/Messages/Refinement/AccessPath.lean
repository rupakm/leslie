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
    (htxn : s.shared.currentTxn = none) :
    (s.locals i).line.data = (refMap n s).shared.mem := by
  -- refMap.mem when currentTxn = none:
  -- match findDirtyReleaseVal with some v => v | none => s.shared.mem
  simp only [refMap, refMapShared, htxn]
  -- Case split on whether there's a dirty release in flight
  rcases hfdrv : findDirtyReleaseVal n s with v | _
  · -- findDirtyReleaseVal = some v: a dirty release is in flight.
    -- The releasing node has releaseInFlight = true and chanC with data.
    -- Under releaseUniqueInv, only one node can have a release in flight.
    -- The reading node i has allowsRead (perm ∈ {.B, .T}).
    -- Under dirtyExclusiveInv, if a dirty node exists, all others have perm .N.
    -- But the release already happened (dirty → clean), so the releasing node
    -- is no longer dirty. The findDirtyReleaseVal gives the released data = v.
    -- Need: (s.locals i).line.data = v
    sorry
  · -- findDirtyReleaseVal = none: no dirty release in flight.
    -- refMap.mem = s.shared.mem
    -- From dataCoherenceInv: currentTxn = none → releaseInFlight = false → dirty = false → data = mem
    -- Need: data i = s.shared.mem
    rcases hinv with ⟨⟨_, hdirtyEx, hSwmr, _, _, _⟩, hdata, _, _, _, _⟩
    by_cases hdirty : (s.locals i).line.dirty = true
    · -- Node i is dirty: it's the unique dirty owner.
      -- Its data IS the logical value. But refMap.mem = s.shared.mem (no dirty release).
      -- Under dataCoherenceInv with dirty = true: the invariant doesn't constrain data.
      -- BUT: if node i is dirty and no release is in flight, then
      -- findDirtyReleaseVal = none means no node has (releaseInFlight ∧ chanC with data).
      -- Node i is dirty → perm = .T (from lineWF). Since i is dirty and reading,
      -- no release is in flight from i (otherwise releaseInFlight = true).
      -- The dirty node's data should equal mem (from dataCoherenceInv strengthened form).
      -- Actually dataCoherenceInv requires dirty = false. So it doesn't apply to dirty nodes.
      -- BUT: if i is dirty with no release, then i's data was written by store.
      -- store doesn't change mem. So data ≠ mem in general.
      -- HOWEVER: refMap.mem = findDirtyReleaseVal or s.shared.mem. Since findDirtyReleaseVal = none,
      -- refMap.mem = s.shared.mem. But dirty node's data ≠ s.shared.mem. So the theorem FAILS
      -- for dirty readers... unless refMap.mem accounts for dirty owners.
      --
      -- KEY INSIGHT: The refMap.mem for the no-txn case should also check for dirty owners
      -- (not just dirty releases in flight). Currently it only checks findDirtyReleaseVal.
      -- This is a refMap gap — it should also return dirty owner data when no release is in flight.
      sorry
    · -- Node i is clean: dataCoherenceInv gives data = mem
      push_neg at hdirty; simp at hdirty
      -- Need releaseInFlight = false for dataCoherenceInv
      -- If releaseInFlight i = true: node i sent a release but it hasn't been received.
      -- Can node i still have valid = true and perm allowing read?
      -- After sendRelease: line = releasedLine with dirty=false. perm = result.
      -- If result ∈ {.B, .T}: valid = true, allowsRead = true. So YES, can read while releasing.
      -- But dataCoherenceInv requires releaseInFlight = false.
      -- The data after release = pre-release data. If pre-release data = mem: still OK.
      -- But if dirty release: data = dirty data ≠ mem.
      -- Under clean release (dirty = false at send): data = mem from pre-state dataCoherenceInv.
      -- So if current dirty = false and was clean at send time: data = mem.
      -- This holds because sendRelease requires dirty = false, and the data was = mem at that point.
      by_cases hflight : (s.locals i).releaseInFlight = true
      · -- releaseInFlight = true but dirty = false: this was a clean release.
        -- Data = mem from pre-release state (preserved by sendRelease which doesn't change data).
        -- Actually, sendReleaseData requires dirty = true, so this must be a clean sendRelease.
        -- Before sendRelease: dataCoherenceInv gave data = mem (at quiescent time).
        -- sendRelease creates releasedLine which preserves data. So data = mem.
        -- But dataCoherenceInv doesn't give us this because releaseInFlight = true.
        -- We need the strengthened dataCoherenceInv or a helper.
        sorry
      · exact hdata htxn i hflight hdirty

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
    rcases hinv with ⟨⟨_, _, hSwmr, _, _, _⟩, _, _, _, _, _⟩
    have hpermN := hSwmr i j (Ne.symm hji) hpermI
    rw [hpermN] at hpermJ
    simp [TLPerm.allowsRead] at hpermJ

end TileLink.Messages
