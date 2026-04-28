/-
M1 W1 — Project-local PMF utilities.

A thin layer atop Mathlib's `PMF` that fixes vocabulary for the
randomized-leslie modules. Mathlib already provides `PMF.pure`,
`PMF.bind`, `PMF.map`, `PMF.support`, `PMF.uniformOfFintype`,
`PMF.filter`, plus all the expected algebraic lemmas; we only add
what's missing or worth aliasing.

Additions:
  * `PMF.uniform` — alias for `PMF.uniformOfFintype` (shorter name).
  * `PMF.product` — independent joint `α × β` from marginals.
  * `PMF.condition` — alias for `PMF.filter` (vocabulary alignment
    with the design plan).

The simp set used by Action.lean / Embed.lean is Mathlib's plus the
two helpers below.
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform

open scoped ENNReal

namespace PMF

variable {α β : Type*}

/-! ## Uniform distribution -/

/-- Uniform distribution on a finite, nonempty type. Alias for
`PMF.uniformOfFintype`. -/
@[reducible]
noncomputable def uniform (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  uniformOfFintype α

@[simp] theorem uniform_apply [Fintype α] [Nonempty α] (a : α) :
    uniform α a = (Fintype.card α : ℝ≥0∞)⁻¹ :=
  uniformOfFintype_apply a

/-! ## Independent joint distribution -/

/-- Independent joint distribution over `α × β`: sample `μ` then
independently `ν`, return the pair. -/
noncomputable def product (μ : PMF α) (ν : PMF β) : PMF (α × β) :=
  μ.bind (fun a => ν.map (fun b => (a, b)))

/-! ## Conditional / filtered distribution

`condition` is Mathlib's `PMF.filter` — restrict support to a set
with positive measure and renormalize. The new name aligns with the
design plan's "conditional" vocabulary. -/

/-- Conditional distribution restricted to a positive-measure set. -/
noncomputable def condition (μ : PMF α) (s : Set α)
    (h : ∃ a ∈ s, a ∈ μ.support) : PMF α :=
  μ.filter s h

end PMF
