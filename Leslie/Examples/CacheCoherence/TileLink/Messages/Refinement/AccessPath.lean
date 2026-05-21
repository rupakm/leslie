import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.SimOther
import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement

/-! ## Access-Path Theorems

    This file proves that the TileLink message model correctly implements
    a sequentially consistent shared memory for reads and writes:

    - `read_returns_logical_data`: a readable node's data equals the
      abstract sequential register value
    - `store_updates_logical_data`: after a store, the abstract sequential
      register value equals the stored value

    STATUS: These theorems depend on `ForwardSimInv` (a structured invariant
    bundling dirtyExclusiveInv, dirtyReleaseExclusiveInv, dataCoherenceInv,
    etc.) which is not yet defined on the Leslie_LTS branch. The branch's
    Act enum also lacks `store`/`read` constructors. Proof bodies are
    sorry'd pending alignment of the model with the extended action set.
-/

namespace TileLink.Messages

open TLA TileLink SymShared Classical

/-- A readable node's data equals the logical line value (the abstract
    sequential register value mapped through the refinement).

    When a node has read permission (perm in {.B, .T}) and valid data,
    its data equals `(refMap n s).shared.mem`, which is the abstract
    memory value. Combined with `messages_refines_atomic` and
    `atomic_coherence`, this means reads return the value of the
    sequential register.

    TODO: Requires ForwardSimInv (dirtyExclusiveInv, dirtyReleaseExclusiveInv,
    dataCoherenceInv, findDirtyReleaseVal) which are not yet on this branch. -/
theorem read_returns_logical_data {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (hinv : forwardSimInv n s)
    (hperm : (s.locals i).line.perm.allowsRead)
    (hvalid : (s.locals i).line.valid = true)
    (htxn : s.shared.currentTxn = none)
    (hflight : (s.locals i).releaseInFlight = false) :
    (s.locals i).line.data = (refMap n s).shared.mem := by
  sorry

-- store_updates_logical_data: commented out because the `Store` action predicate
-- is not part of the Act enum on this branch (the branch uses a 12-constructor
-- Act without store/read/uncached actions).

end TileLink.Messages
