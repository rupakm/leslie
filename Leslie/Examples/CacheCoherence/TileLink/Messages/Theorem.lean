import Leslie.Examples.CacheCoherence.TileLink.Messages.StepRelease

namespace TileLink.Messages

open TLA SymShared

theorem messages_acquire_inv_invariant (n : Nat) :
    pred_implies (tlMessages.toSpec n).safety [tlafml| □ ⌜ fullInv n ⌝] := by
  apply init_invariant
  · intro s hinit
    exact init_fullInv n s hinit
  · intro s s' hnext hinv
    exact fullInv_preserved_with_release n s s' hinv hnext

end TileLink.Messages
