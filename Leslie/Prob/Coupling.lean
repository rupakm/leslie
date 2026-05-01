/-
M1 W2 — pRHL-style coupling judgment for `PMF`.

A *coupling* of two PMFs `μ : PMF α` and `ν : PMF β` is a joint
distribution on `α × β` whose marginals are `μ` and `ν`. Couplings
that support a relation `R : α → β → Prop` lift relational reasoning
from sample-pairs to distributions — the foundation of probabilistic
relational Hoare logic (pRHL).

This module provides the structure plus the most-used constructors:

  * `PMF.Coupling μ ν` — the structure (joint + marginal proofs)
  * `PMF.Coupling.supports c R` — `R` holds on the joint's support
  * `PMF.eq_of_coupling_id` — an `Eq`-supporting coupling proves
    `μ = ν`
  * `PMF.Coupling.pure_id` — Dirac on the diagonal
  * `PMF.Coupling.bijection` — bijection-induced coupling
  * `PMF.Coupling.self` — `μ` coupled with itself

More combinators (`bind`, `swap`, `up_to_bad`) and tactics that wrap
them land later. Mathlib does not have a direct `PMF.Coupling`
structure (it has measure-theoretic couplings elsewhere); we define
our own in the `PMF` namespace.
-/

import Leslie.Prob.PMF

namespace PMF

variable {α β : Type*}

/-! ## The Coupling structure -/

/-- A coupling of `μ : PMF α` and `ν : PMF β`: a joint distribution
on `α × β` whose marginals are `μ` and `ν`. -/
structure Coupling (μ : PMF α) (ν : PMF β) where
  joint      : PMF (α × β)
  marg_left  : joint.map Prod.fst = μ
  marg_right : joint.map Prod.snd = ν

namespace Coupling

variable {μ : PMF α} {ν : PMF β}

/-- A coupling *supports* a relation `R : α → β → Prop` if every pair
in the joint's support is `R`-related. -/
def supports (c : Coupling μ ν) (R : α → β → Prop) : Prop :=
  ∀ p ∈ c.joint.support, R p.1 p.2

end Coupling

/-! ## Constructors -/

/-- The diagonal coupling: `μ` coupled with itself by sampling once
and pairing with the same value. -/
noncomputable def Coupling.self (μ : PMF α) : Coupling μ μ where
  joint      := μ.bind fun a => PMF.pure (a, a)
  marg_left  := by
    show (μ.bind fun a => PMF.pure (a, a)).map Prod.fst = μ
    rw [PMF.map_bind]
    show (μ.bind fun a => (PMF.pure (a, a)).map Prod.fst) = μ
    have : ∀ a : α, (PMF.pure (a, a)).map Prod.fst = PMF.pure a := by
      intro a; rw [PMF.pure_map]
    simp_rw [this]
    exact PMF.bind_pure μ
  marg_right := by
    show (μ.bind fun a => PMF.pure (a, a)).map Prod.snd = μ
    rw [PMF.map_bind]
    have : ∀ a : α, (PMF.pure (a, a)).map Prod.snd = PMF.pure a := by
      intro a; rw [PMF.pure_map]
    simp_rw [this]
    exact PMF.bind_pure μ

/-- The diagonal coupling supports equality. -/
theorem Coupling.self_supports_eq (μ : PMF α) :
    (Coupling.self μ).supports (· = ·) := by
  intro p hp
  -- joint = μ.bind (fun a => pure (a, a)); support is {(a, a) | a ∈ μ.support}
  simp [Coupling.self, PMF.support_bind, PMF.support_pure] at hp
  obtain ⟨a, _, rfl⟩ := hp
  rfl

/-- Dirac on the diagonal: `pure a` is coupled with itself. -/
noncomputable def Coupling.pure_id (a : α) : Coupling (PMF.pure a) (PMF.pure a) :=
  Coupling.self (PMF.pure a)

/-- Bijection-induced coupling: from `f : α → β`, `μ` is coupled with
`μ.map f` via the joint `μ.bind (fun a => pure (a, f a))`, supporting
`fun a b => b = f a`. -/
noncomputable def Coupling.bijection (μ : PMF α) (f : α → β) :
    Coupling μ (μ.map f) where
  joint      := μ.bind fun a => PMF.pure (a, f a)
  marg_left  := by
    rw [PMF.map_bind]
    have : ∀ a : α, (PMF.pure (a, f a)).map Prod.fst = PMF.pure a := by
      intro a; rw [PMF.pure_map]
    simp_rw [this]
    exact PMF.bind_pure μ
  marg_right := by
    rw [PMF.map_bind]
    have : ∀ a : α, (PMF.pure (a, f a)).map Prod.snd = PMF.pure (f a) := by
      intro a; rw [PMF.pure_map]
    simp_rw [this]
    -- Goal: (μ.bind fun a => pure (f a)) = μ.map f
    -- Mathlib's `bind_pure_comp f p : p.bind (pure ∘ f) = map f p`
    -- and `pure ∘ f = fun a => pure (f a)` definitionally.
    show μ.bind (PMF.pure ∘ f) = μ.map f
    exact PMF.bind_pure_comp f μ

/-- The bijection coupling supports `b = f a`. -/
theorem Coupling.bijection_supports (μ : PMF α) (f : α → β) :
    (Coupling.bijection μ f).supports (fun a b => b = f a) := by
  intro p hp
  -- joint = μ.bind (fun a => pure (a, f a))
  simp [Coupling.bijection, PMF.support_bind, PMF.support_pure] at hp
  obtain ⟨a, _, rfl⟩ := hp
  rfl

/-! ## eq_of_coupling_id

Cornerstone of "rewrite by coupling": equality of marginals follows
from a coupling supporting `(· = ·)`. -/

/-- A coupling that supports `(· = ·)` proves `μ = ν`. -/
theorem eq_of_coupling_id {μ ν : PMF α} (c : Coupling μ ν)
    (h : c.supports (· = ·)) : μ = ν := by
  apply PMF.ext
  intro a
  -- Reduce μ a and ν a to coordinate-projected forms.
  have hL : μ a = (c.joint.map Prod.fst) a := by rw [c.marg_left]
  have hR : ν a = (c.joint.map Prod.snd) a := by rw [c.marg_right]
  rw [hL, hR, PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro p
  by_cases hp : p ∈ c.joint.support
  · -- supports (·=·) gives p.1 = p.2 on support
    have heq : p.1 = p.2 := h p hp
    by_cases ha : a = p.1
    · simp [ha, heq]
    · have ha2 : a ≠ p.2 := heq ▸ ha
      simp [ha, ha2]
  · -- off support, joint p = 0 (use apply_eq_zero_iff)
    have hzero : c.joint p = 0 := (PMF.apply_eq_zero_iff c.joint p).mpr hp
    rw [hzero]
    simp

end PMF
