import Leslie.Refinement
import Leslie.Examples.CacheCoherence.TileLink.Messages.Theorem
import Leslie.Examples.CacheCoherence.TileLink.Atomic.Model

namespace TileLink.Messages

open TLA TileLink SymShared Classical

def noDirtyInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, (s.locals i).line.dirty = false

def txnDataInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  match s.shared.currentTxn with
  | none => True
  | some tx => tx.usedDirtySource = false ∧ tx.transferVal = s.shared.mem

def refinementInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  fullInv n s ∧ noDirtyInv n s ∧ txnDataInv n s

theorem init_noDirtyInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → noDirtyInv n s := by
  intro s hinit i
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨hline, _, _, _, _, _, _, _, _⟩
  rw [hline]

private theorem plannedTxn_clean {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n)
    (hnoDirty : noDirtyInv n s) :
    plannedUsedDirtySource s i = false ∧ plannedTransferVal s i = s.shared.mem := by
  unfold plannedUsedDirtySource plannedTransferVal dirtyOwnerOpt
  have hnone : ¬∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true := by
    intro h
    rcases h with ⟨j, _, hdirty⟩
    rw [hnoDirty j] at hdirty
    contradiction
  simp [hnone]

theorem init_txnDataInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → txnDataInv n s := by
  intro s hinit
  rcases hinit with ⟨⟨_, _, htxn, _, _, _⟩, _⟩
  simp [txnDataInv, htxn]

theorem init_refinementInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → refinementInv n s := by
  intro s hinit
  exact ⟨init_fullInv n s hinit, init_noDirtyInv n s hinit, init_txnDataInv n s hinit⟩

end TileLink.Messages
