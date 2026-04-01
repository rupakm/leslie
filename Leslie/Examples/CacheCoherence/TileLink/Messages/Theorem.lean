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

theorem grantPendingAck_other_channels_none_of_fullInv {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hinv : fullInv n s)
    (hcur : s.shared.currentTxn = some tx)
    (hphase : tx.phase = .grantPendingAck) :
    ∀ j : Fin n, j.1 ≠ tx.requester →
      (s.locals j).chanB = none ∧
      (s.locals j).chanC = none ∧
      (s.locals j).chanD = none ∧
      (s.locals j).chanE = none := by
  rcases hinv with ⟨_, hchan, _⟩
  rcases hchan with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  intro j hreqj
  refine ⟨?_, ?_, ?_, ?_⟩
  · specialize hchanB j
    cases hB : (s.locals j).chanB with
    | none => exact rfl
    | some _ =>
        rw [hB] at hchanB
        rcases hchanB with ⟨tx0, hcur0, hprobing, _, _, _, _⟩
        rw [hcur] at hcur0
        injection hcur0 with htx
        subst htx
        rw [hphase] at hprobing
        cases hprobing
  · specialize hchanC j
    cases hC : (s.locals j).chanC with
    | none => exact rfl
    | some _ =>
        rw [hC] at hchanC
        rcases hchanC with hprobe | hrel
        · rcases hprobe with ⟨tx0, hcur0, hprobing, _, _, _, _, _⟩
          rw [hcur] at hcur0
          injection hcur0 with htx
          subst htx
          rw [hphase] at hprobing
          cases hprobing
        · rcases hrel with ⟨_, htxnNone, _, _, _, _, _, _⟩
          rw [hcur] at htxnNone
          simp at htxnNone
  · specialize hchanD j
    cases hD : (s.locals j).chanD with
    | none => exact rfl
    | some _ =>
        rw [hD] at hchanD
        rcases hchanD with hgrant | hrel
        · rcases hgrant with ⟨tx0, hcur0, hreq0, hphase0, _, _, _, _⟩
          rw [hcur] at hcur0
          injection hcur0 with htx
          subst htx
          exact False.elim (hreqj hreq0.symm)
        · rcases hrel with ⟨htxnNone, _, _, _, _, _, _⟩
          rw [hcur] at htxnNone
          simp at htxnNone
  · specialize hchanE j
    cases hE : (s.locals j).chanE with
    | none => exact rfl
    | some _ =>
        rw [hE] at hchanE
        rcases hchanE with ⟨tx0, hcur0, hreq0, hphase0, _, _, _, _⟩
        rw [hcur] at hcur0
        injection hcur0 with htx
        subst htx
        exact False.elim (hreqj hreq0.symm)

end TileLink.Messages
