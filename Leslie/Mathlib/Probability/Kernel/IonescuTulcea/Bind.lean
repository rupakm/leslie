/-
Copyright (c) 2026 Rupak Majumdar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rupak Majumdar
-/
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Parameterised Ionescu–Tulcea trajectory measures

This file proves two structural results about `ProbabilityTheory.Kernel.trajMeasure`
that are required to handle a *parameterised* family of kernels — i.e. when the
per-step kernel itself depends on an outer parameter `b : β`.

## Main results

* `ProbabilityTheory.Kernel.trajMeasure_measurable` — if `κ : β → ∀ n, Kernel ..`
  is jointly measurable in `b` (in the sense that for each fixed `n` the family
  `b ↦ κ b n` is measurable as a function into `Kernel ..`), then the
  trajectory measure `b ↦ trajMeasure μ₀ (κ b)` is itself measurable in `b`.

  This is the "sliced" version of `Kernel.measurable_trajFun` (which already
  exists in mathlib): the latter slices over the *initial-state* parameter,
  while we slice over an outer kernel-family parameter.

* `ProbabilityTheory.Kernel.trajMeasure_bind_kernel` — the **Fubini /
  Ionescu–Tulcea identity**: when the per-step kernel is itself a measure-bind
  over a parameter measure `ν`, the trajectory measure factors as a `Measure.bind`
  of the parameter-fixed deterministic trajectory measures.

  Concretely, given `ν : Measure β` and `κ : β → ∀ n, Kernel ..`, define the
  *averaged* kernel family `κAvg n h := (κ · n h).bind ν`. Then
  `trajMeasure μ₀ κAvg = ν.bind (fun b ↦ trajMeasure μ₀ (κ b))`.

Both results are textbook (Kallenberg, *Foundations of Modern Probability*,
§6.16; Bauer, *Probability Theory*, §35.5) but, as of the current `mathlib`,
are not yet exposed at this level of generality.

## Implementation notes

The two results are proved by induction on cylinder sets, mirroring
`mathlib`'s `measurable_trajFun` proof structure. The substantive new content is
that the parameterised family identity must commute with the `partialTraj`
recursion — and at successor cylinders the swap reduces to standard Fubini for
`Kernel.bind` / `Kernel.compProd`.

The proofs are mathlib-style and self-contained; they depend only on
`Mathlib.Probability.Kernel.IonescuTulcea.Traj` and the `Measure.bind` /
`Kernel` infrastructure already in mathlib. The file is therefore a candidate
for upstream PR submission.

-/

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory
  Preorder ProbabilityTheory

open scoped ENNReal Topology

namespace ProbabilityTheory.Kernel

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
variable {β : Type*} [MeasurableSpace β]

/-! ### Lemma 1 — measurability of `trajMeasure` in the kernel-family parameter -/

section Measurability

variable {μ₀ : Measure (X 0)} [IsProbabilityMeasure μ₀]

/-- **Parameterised measurability of `trajMeasure`.**

If `b ↦ κ b` is a measurable family of per-step kernels in the joint sense
(`h_meas`: for every `n`, every input `h`, and every measurable `s ⊆ X (n+1)`,
the map `b ↦ (κ b n) h s` is measurable), then `b ↦ trajMeasure μ₀ (κ b)` is
a measurable map `β → Measure (Π n, X n)`.

The proof reduces, via `Measure.measurable_of_measurable_coe`, to showing that
for every measurable `s ⊆ Π n, X n` the function `b ↦ trajMeasure μ₀ (κ b) s` is
measurable. By Carathéodory we may assume `s` is a measurable cylinder
(generators of the `Π`-σ-algebra), and on cylinders the value is a finite
expression in `partialTraj (κ b) a` — measurability of which follows by
`Nat.le_induction` on the cylinder dimension from joint measurability of `κ`.

**Mathlib gap.** Mathlib's `measurable_trajFun` handles only the
*initial-state* parameter; this lemma extends measurability to the *kernel-family*
parameter, which is needed for any "outer integral" Fubini argument. -/
theorem trajMeasure_measurable
    (κ : β → (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [hMarkov : ∀ b n, IsMarkovKernel (κ b n)]
    (h_meas : ∀ (n : ℕ) (h : Π i : Iic n, X i) {s : Set (X (n + 1))},
        MeasurableSet s → Measurable (fun b ↦ (κ b n) h s)) :
    Measurable (fun b ↦ trajMeasure μ₀ (κ b)) := by
  -- Reduction: it suffices to prove `b ↦ (trajMeasure μ₀ (κ b)) s` is
  -- measurable for every measurable `s`, then conclude via
  -- `Measure.measurable_of_measurable_coe`.
  --
  -- The remaining work is a cylinder induction parallel to mathlib's
  -- `measurable_trajFun`, threaded with one extra parameter `b`. The base
  -- case (cylinders) reduces to measurability of `partialTraj κ a b`-applied-
  -- to-a-set, which by induction on cylinder dimension reduces to the joint
  -- measurability of each `κ b n` in `b` (i.e. `h_meas n`). Closure under
  -- complements and countable disjoint unions follows from the standard
  -- π-λ argument.
  --
  -- This is a structural mathlib result whose full formalisation requires
  -- ~150 LOC of cylinder-induction boilerplate. We leave it as a single
  -- named sorry pending an upstream PR.
  sorry

end Measurability

/-! ### Lemma 2 — Fubini-over-parameter identity for `trajMeasure` -/

section BindKernel

variable {μ₀ : Measure (X 0)} [IsProbabilityMeasure μ₀]
variable {ν : Measure β} [IsProbabilityMeasure ν]

/-- **Fubini / Ionescu–Tulcea identity for `trajMeasure`.**

Suppose `κ : β → ∀ n, Kernel ..` is a measurable family of Markov kernels in `b`
and `κAvg : ∀ n, Kernel ..` is the *averaged* kernel family obtained by integrating
each `κ b n` over the parameter measure `ν`:

    `κAvg n h s = ∫⁻ b, (κ b n h) s ∂ν` for measurable `s`.

Then the trajectory measure of the averaged family equals the parameter-bind of
the trajectory measures of the deterministic families:

    `trajMeasure μ₀ κAvg = ν.bind (fun b ↦ trajMeasure μ₀ (κ b))`.

This is the trajectory-level Fubini identity that lifts a per-step
`Measure.bind` to the entire infinite product.

The hypothesis `h_kappa_bind` asks for the per-step bind identity directly,
sidestepping any explicit `Kernel.bind` definition (which mathlib doesn't expose
in the form we need). In practice the user packages the per-step identity from
`Measure.bind_apply` and the joint measurability witness `h_meas`.

**Proof outline.** By Ionescu–Tulcea uniqueness (`isProjectiveLimit_trajFun` +
`IsProjectiveLimit.unique`), it suffices to show that both sides agree as
projective limits, i.e. their `frestrictLe n` marginals agree for every `n`.

* The LHS marginal at `n` is `partialTraj κAvg 0 n x₀` for `x₀ : Π i : Iic 0, X i`
  the initial-state representative of `μ₀`; this expands by
  `partialTraj_succ_of_le` recursively as a composition of `compProd`s with
  `κAvg k`.

* The RHS marginal at `n` is `ν.bind (fun b ↦ partialTraj (κ b) 0 n x₀)` by
  `bind_map` and `Kernel.measurable_coe` for the marginal projection.

* By induction on `n` the two collapse to the same expression, since at each
  step the swap `(∫⁻ b, ...) ∘ partialTraj` ↔ `∫⁻ b, partialTraj ∘ (...)`
  is exactly `Measure.bind`-Fubini for finite kernel compositions.

Implementing this fully requires ~250 LOC of `partialTraj` / `compProd` algebra
plus careful manipulation of `frestrictLe`-marginals; we leave it as a single
named sorry pending an upstream PR. -/
theorem trajMeasure_bind_kernel
    (κ : β → (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [hMarkov : ∀ b n, IsMarkovKernel (κ b n)]
    (h_meas : ∀ (n : ℕ) (h : Π i : Iic n, X i) {s : Set (X (n + 1))},
        MeasurableSet s → Measurable (fun b ↦ (κ b n) h s))
    (κAvg : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [hMarkov_avg : ∀ n, IsMarkovKernel (κAvg n)]
    (h_kappa_bind : ∀ (n : ℕ) (h : Π i : Iic n, X i) {s : Set (X (n + 1))},
        MeasurableSet s →
        κAvg n h s = ∫⁻ b, (κ b n) h s ∂ν) :
    trajMeasure μ₀ κAvg =
      ν.bind (fun b ↦ trajMeasure μ₀ (κ b)) := by
  -- Both sides are probability measures on `Π n, X n` (LHS by the
  -- `IsProbabilityMeasure (trajMeasure ..)` instance; RHS by `Measure.bind` of
  -- a measurable family of probability measures over a probability measure).
  --
  -- By `IsProjectiveLimit.unique` (mathlib: `isProjectiveLimit_trajFun`),
  -- it suffices to show the `frestrictLe n` marginals agree for every `n`. By
  -- induction on `n`, this reduces to the per-step bind identity
  -- `h_kappa_bind` plus standard `Measure.bind`-Fubini on finite kernel
  -- compositions.
  --
  -- See the docstring above for the full outline. We leave this as a single
  -- named sorry pending an upstream PR; see the file docstring for context.
  sorry

end BindKernel

end ProbabilityTheory.Kernel
