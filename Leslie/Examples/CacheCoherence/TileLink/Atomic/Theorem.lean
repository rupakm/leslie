import Leslie.Examples.CacheCoherence.TileLink.Atomic.StepProof

namespace TileLink.Atomic

open TLA SymShared

theorem atomic_inv_invariant (n : Nat) :
    pred_implies (tlAtomic.toSpec n).safety [tlafml| □ ⌜ atomicInv n ⌝] := by
  apply init_invariant
  · intro s hinit
    exact init_atomicInv n s hinit
  · intro s s' hnext hinv
    exact atomicInv_preserved n s s' hinv hnext

theorem atomic_dirty_exclusive_invariant (n : Nat) :
    pred_implies (tlAtomic.toSpec n).safety [tlafml| □ ⌜ dirtyExclusive n ⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜ atomicInv n ⌝])
  · exact atomic_inv_invariant n
  · apply always_monotone
    intro e he
    exact atomicInv_implies_dirtyExclusive n _ he

theorem atomic_dir_invariant (n : Nat) :
    pred_implies (tlAtomic.toSpec n).safety [tlafml| □ ⌜ dirInv n ⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜ atomicInv n ⌝])
  · exact atomic_inv_invariant n
  · apply always_monotone
    intro e he
    rcases he with ⟨_, _, hdir, _, _⟩
    exact hdir

theorem atomic_clean_data_invariant (n : Nat) :
    pred_implies (tlAtomic.toSpec n).safety [tlafml| □ ⌜ cleanDataInv n ⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜ atomicInv n ⌝])
  · exact atomic_inv_invariant n
  · apply always_monotone
    intro e he
    rcases he with ⟨_, _, _, _, hcleanData⟩
    exact hcleanData

theorem atomic_dirty_owner_data_invariant (n : Nat) :
    pred_implies (tlAtomic.toSpec n).safety [tlafml| □ ⌜ dirtyOwnerDataInv n ⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜ atomicInv n ⌝])
  · exact atomic_inv_invariant n
  · apply always_monotone
    intro e he
    exact atomicInv_implies_dirtyOwnerDataInv n _ he

end TileLink.Atomic
