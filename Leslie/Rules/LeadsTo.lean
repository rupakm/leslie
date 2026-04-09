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

/-! ### Well-founded induction for leads-to

    These rules allow proving p ↝ q by providing a Nat-valued measure μ
    that decreases with each step. This is the TLA analogue of
    "proof by well-founded ordering" (Lamport). -/

/-- Well-founded induction for leads-to using a Nat-valued measure.
    If for every k > 0, p ∧ (μ = k) leads to q ∨ (p ∧ μ < k),
    and p ∧ (μ = 0) leads to q, then p leads to q.

    This is the standard TLA lattice rule: each step either achieves q
    or makes progress toward it by decreasing the measure. -/
theorem leads_to_via_nat {Γ : pred σ} {p q : pred σ}
    (μ : (Nat → σ) → Nat)
    (hstep : ∀ k : Nat, k > 0 →
      ∀ e, Γ e → ∀ i, p (e.drop i) → μ (e.drop i) = k →
        ∃ j, q (e.drop (i + j)) ∨ (p (e.drop (i + j)) ∧ μ (e.drop (i + j)) < k))
    (hbase : ∀ e, Γ e → ∀ i, p (e.drop i) → μ (e.drop i) = 0 →
        ∃ j, q (e.drop (i + j))) :
    pred_implies Γ (leads_to p q) := by
  intro e hΓ
  simp only [leads_to, always, eventually] at *
  -- Suffices: induct on μ using absolute positions in e
  suffices h : ∀ m k, μ (e.drop k) ≤ m → p (e.drop k) →
      ∃ j, q ((e.drop k).drop j) by
    intro k hp; exact h (μ (e.drop k)) k (Nat.le_refl _) hp
  intro m
  induction m with
  | zero =>
    intro k hle hp'
    obtain ⟨j, hj⟩ := hbase e hΓ k hp' (Nat.le_zero.mp hle)
    exact ⟨j, show q ((e.drop k).drop j) by rw [exec.drop_drop]; exact hj⟩
  | succ m ih =>
    intro k hle hp'
    by_cases hm : μ (e.drop k) = 0
    · obtain ⟨j, hj⟩ := hbase e hΓ k hp' hm
      exact ⟨j, show q ((e.drop k).drop j) by rw [exec.drop_drop]; exact hj⟩
    · obtain ⟨j, hj⟩ := hstep (μ (e.drop k)) (Nat.pos_of_ne_zero hm) e hΓ k hp' rfl
      rcases hj with hq | ⟨hp'', hlt⟩
      · exact ⟨j, show q ((e.drop k).drop j) by rw [exec.drop_drop]; exact hq⟩
      · have hle' : μ (e.drop (k + j)) ≤ m := by omega
        obtain ⟨j', hj'⟩ := ih (k + j) hle' hp''
        refine ⟨j + j', ?_⟩
        show q ((e.drop k).drop (j + j'))
        -- All exec.drop_drop collapses to e.drop (n) for some n
        simp only [exec.drop_drop] at hj' ⊢
        -- hj' : q (e (k + j + j')), goal: q (e (k + (j + j')))
        -- These are equal by Nat.add_assoc
        rwa [show k + j + j' = k + (j + j') from by omega] at hj'

end leads_to

end TLA
