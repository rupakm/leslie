import Lean
import Leslie.Rules.Basic
import Leslie.Gadgets.TheoremDeriving

/-! Theorems about the leads-to operator. -/

open Classical

namespace TLA

section leads_to

variable {σ : Type u}

-- FIXME: any chance to make the following two lemmas more general
theorem leads_to_exists (Γ q : pred σ) (p : α → pred σ) :
  (∀ (x : α), (Γ) |-tla- ((p x) ↝ q)) ↔ (Γ) |-tla- ((tla_exists p) ↝ q) := by
  tla_unfold_simp ; aesop

theorem leads_to_pure_pred_and (Γ p q : pred σ) (φ : Prop) :
  (φ → (Γ) |-tla- (p ↝ q)) ↔ (Γ) |-tla- (⌞ φ ⌟ ∧ p ↝ q) := by
  tla_unfold_simp ; aesop

@[tla_derive]
theorem leads_to_conseq (p p' q q': pred σ) :
  |-tla- ((p' ⇒ p) → (q ⇒ q') → (p ↝ q) ⇒ (p' ↝ q')) := by
  tla_unfold_simp ; intro e h1 h2 k h k' hh'
  specialize h _ (h1 _ hh') ; rcases h with ⟨k1, h⟩ ; aesop

@[tla_derive]
theorem leads_to_trans (p q r : pred σ) :
  |-tla- ((p ↝ q) → (q ↝ r) → (p ↝ r)) := by
  tla_unfold_simp ; intro e h1 h2 k hh
  specialize h1 _ hh ; rcases h1 with ⟨k1, h1⟩
  specialize h2 _ h1 ; rcases h2 with ⟨k2, h2⟩
  exists (k1 + k2) ; rw [← Nat.add_assoc] ; assumption

theorem leads_to_combine (Γ Γ' p1 q1 p2 q2 : pred σ)
  (h1 : (□ Γ ∧ Γ') |-tla- (p1 ↝ q1))
  (h2 : (□ Γ ∧ Γ') |-tla- (p2 ↝ q2))
  (h1' : (q1 ∧ □ Γ) |-tla- □ q1) (h2' : (q2 ∧ □ Γ) |-tla- □ q2) :
  (□ Γ ∧ Γ') |-tla- (p1 ∧ p2 ↝ q1 ∧ q2) := by
  -- a semantic proof
  tla_unfold_simp ; intro e hΓ hΓ' k hp1 hp2
  specialize h1 _ hΓ hΓ' k hp1 ; rcases h1 with ⟨k1, h1⟩
  specialize h2 _ hΓ hΓ' k hp2 ; rcases h2 with ⟨k2, h2⟩
  exists k1 + k2
  specialize h1' _ h1 (by intro q ; rw [exec.drop_drop] ; apply hΓ) k2
  specialize h2' _ h2 (by intro q ; rw [exec.drop_drop] ; apply hΓ) k1
  simp [exec.drop_drop] at h1' h2'
  constructor ; rw [← Nat.add_assoc] ; assumption ; rw [Nat.add_comm k1 k2, ← Nat.add_assoc] ; assumption

@[tla_derive]
theorem leads_to_strengthen_lhs (p q inv : pred σ) :
  |-tla- (□ inv → (p ∧ inv ↝ q) → (p ↝ q)) := by
  tla_unfold_simp ; aesop

/-! ### Composition under a common hypothesis -/

/-- Chain two leads-to properties under a common hypothesis Γ.
    `(Γ ⊢ p ↝ q) ∧ (Γ ⊢ q ↝ r) → (Γ ⊢ p ↝ r)` -/
theorem leads_to_chain {Γ p q r : pred σ}
    (h1 : pred_implies Γ (leads_to p q))
    (h2 : pred_implies Γ (leads_to q r)) :
    pred_implies Γ (leads_to p r) :=
  fun e hΓ => leads_to_trans p q r e (h1 e hΓ) (h2 e hΓ)

/-- Chain three leads-to properties under a common hypothesis Γ. -/
theorem leads_to_chain3 {Γ p q r s : pred σ}
    (h1 : pred_implies Γ (leads_to p q))
    (h2 : pred_implies Γ (leads_to q r))
    (h3 : pred_implies Γ (leads_to r s)) :
    pred_implies Γ (leads_to p s) :=
  leads_to_chain h1 (leads_to_chain h2 h3)

/-- Disjunction elimination for leads-to under a common hypothesis. -/
theorem leads_to_or {Γ p1 p2 q : pred σ}
    (h1 : pred_implies Γ (leads_to p1 q))
    (h2 : pred_implies Γ (leads_to p2 q)) :
    pred_implies Γ (leads_to (tla_or p1 p2) q) :=
  fun e hΓ k hp => hp.elim (h1 e hΓ k) (h2 e hΓ k)

/-- Trivial leads-to: p ↝ p. -/
theorem leads_to_refl (Γ p : pred σ) :
    pred_implies Γ (leads_to p p) :=
  fun _ _ k hp => ⟨0, (exec.drop_zero _).symm ▸ hp⟩

end leads_to

end TLA
