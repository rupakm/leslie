/-
M1 W1 — Project-local PMF utilities.

Mathlib already provides `PMF.pure`, `PMF.bind`, `PMF.map`,
`PMF.support`, `PMF.uniformOfFintype`, `PMF.filter`, plus the
expected algebraic lemmas. This module adds vocabulary aliases that
match the design plan:

  * `PMF.uniform` ⇐ `PMF.uniformOfFintype` (shorter)
  * `PMF.product`  — independent joint via `bind` + `map`
  * `PMF.condition` ⇐ `PMF.filter` (design plan vocabulary)
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

open scoped ENNReal

namespace PMF

variable {α β : Type*}

/-- Uniform distribution on a finite, nonempty type. -/
noncomputable abbrev uniform (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  uniformOfFintype α

@[simp] theorem uniform_apply [Fintype α] [Nonempty α] (a : α) :
    uniform α a = (Fintype.card α : ℝ≥0∞)⁻¹ :=
  uniformOfFintype_apply a

/-- Independent joint distribution: sample `μ`, then independently
`ν`, return the pair. -/
noncomputable def product (μ : PMF α) (ν : PMF β) : PMF (α × β) :=
  μ.bind fun a => ν.map (a, ·)

/-- Conditional distribution restricted to a positive-measure set
(alias for `PMF.filter`). -/
noncomputable abbrev condition (μ : PMF α) (s : Set α)
    (h : ∃ a ∈ s, a ∈ μ.support) : PMF α :=
  μ.filter s h

/-! ## Translation-invariance of uniform

For a finite, nonempty type, pushing the uniform PMF along any
bijection yields the uniform PMF. This is the canonical
"bijection preserves uniform" fact, used by the one-time pad and
the universal-hash arguments in `Examples/Prob/`. Lives here
because both `Coupling.lean` and clients want it. -/

/-- For a bijection `f : α → α` on a finite nonempty type, pushing
the uniform distribution along `f` is again uniform. -/
theorem uniform_map_of_bijective [Fintype α] [Nonempty α]
    {f : α → α} (hf : Function.Bijective f) :
    (PMF.uniform α).map f = PMF.uniform α := by
  apply PMF.ext
  intro b
  rw [PMF.map_apply, PMF.uniform_apply]
  obtain ⟨a₀, ha₀⟩ := hf.surjective b
  rw [tsum_eq_single a₀]
  · rw [if_pos ha₀.symm, PMF.uniform_apply]
  · intro a hane
    rw [if_neg]
    intro hb_eq
    apply hane
    apply hf.injective
    rw [← hb_eq, ha₀]

end PMF
