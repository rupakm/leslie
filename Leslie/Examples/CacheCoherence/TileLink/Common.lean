import Leslie.Examples.CacheCoherence.TileLink.Permissions

/-! ## TileLink Shared Helpers

    Generic helpers reused by the atomic and message-level TileLink models.
-/

namespace TileLink

def setFn {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) (x : α) : Fin n → α :=
  fun j => if j = i then x else f j

@[simp] theorem setFn_same {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) (x : α) :
    setFn f i x i = x := by
  simp [setFn]

@[simp] theorem setFn_ne {α : Type} {n : Nat} (f : Fin n → α) {i j : Fin n} (x : α)
    (h : j ≠ i) : setFn f i x j = f j := by
  simp [setFn, h]

/-- Minimal per-master line state shared by early TileLink models. -/
structure CacheLine where
  perm : TLPerm := .N
  valid : Bool := false
  dirty : Bool := false
  data : Val := 0
  deriving DecidableEq, Repr

/-- Dirty data requires a valid Tip; Branches are always valid; N is always invalid. -/
def CacheLine.WellFormed (line : CacheLine) : Prop :=
  (line.dirty = true → line.perm = .T ∧ line.valid = true) ∧
  (line.perm = .B → line.valid = true) ∧
  (line.perm = .N → line.valid = false ∧ line.dirty = false)

theorem CacheLine.dirty_implies_writable {line : CacheLine} :
    line.WellFormed → line.dirty = true → line.perm.allowsWrite := by
  intro hwf hdirty
  rw [TLPerm.allowsWrite_iff_eq_T]
  exact (hwf.1 hdirty).1

theorem CacheLine.dirty_implies_readable {line : CacheLine} :
    line.WellFormed → line.dirty = true → line.perm.allowsRead := by
  intro hwf hdirty
  exact TLPerm.allowsWrite_implies_allowsRead (CacheLine.dirty_implies_writable hwf hdirty)

theorem CacheLine.dirty_implies_valid {line : CacheLine} :
    line.WellFormed → line.dirty = true → line.valid = true := by
  intro hwf hdirty
  exact (hwf.1 hdirty).2

theorem CacheLine.valid_of_perm_eq_B {line : CacheLine}
    (hwf : line.WellFormed) (hperm : line.perm = .B) :
    line.valid = true := by
  exact hwf.2.1 hperm

theorem CacheLine.invalid_of_perm_eq_N {line : CacheLine}
    (hwf : line.WellFormed) (hperm : line.perm = .N) :
    line.valid = false := by
  exact (hwf.2.2 hperm).1

theorem CacheLine.not_dirty_of_perm_ne_T {line : CacheLine}
    (hwf : line.WellFormed) (hperm : line.perm ≠ .T) :
    line.dirty = false := by
  cases hdirty : line.dirty with
  | false => rfl
  | true =>
      exfalso
      exact hperm ((hwf.1 hdirty).1)

@[simp] theorem CacheLine.default_wf :
    ({ perm := TLPerm.N, valid := false, dirty := false, data := 0 } : CacheLine).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro hdirty
    simp at hdirty
  · intro hperm
    simp at hperm
  · intro hperm
    simp

end TileLink
