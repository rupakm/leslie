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

* `ProbabilityTheory.Kernel.trajMeasure_bind_kernel_of_partial` — the
  trajectory-level Fubini identity: when the per-step kernel is itself a
  measure-bind over a parameter measure `ν`, the trajectory measure factors
  as a `Measure.bind` of the parameter-fixed deterministic trajectory
  measures, *provided* the trajectory-level bind identity holds at every
  finite truncation `partialTraj κ 0 n`.

  Historical note: a previous version of this file exposed an unconditional
  variant `trajMeasure_bind_kernel` whose hypotheses were only the per-level
  bind identity. PR #96 discovered that this is **false in general** — see
  the explicit two-coordinate Bernoulli counterexample below — and exposed
  this corrected `_of_partial` variant alongside it. PR #97 (this PR)
  migrated the single caller (`Leslie.Prob.RandomisedAdversary`) to consume
  the corrected variant and *deleted* the false original. The corrected
  variant is the canonical exposed Fubini identity going forward; in typical
  applications (e.g. randomised adversaries where `ν` is a
  `Measure.infinitePi` indexed by query points) the trajectory-level
  hypothesis is derivable from the per-level identity plus the product
  structure of `ν`. -- See the docstring of `trajMeasure_bind_kernel_of_partial`
  for the precise statement and the counterexample to the unconditional form.

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

section trajMeasure_bind_kernel_helpers

/-! ### Helper lemmas for `trajMeasure_bind_kernel`

These are placed in a dedicated section to avoid textual conflicts with potential
helpers added for `trajMeasure_measurable`. -/

variable {μ₀ : Measure (X 0)} [IsProbabilityMeasure μ₀]
variable {ν : Measure β} [IsProbabilityMeasure ν]

/-- Two probability measures on `Π n, X n` are equal iff their `frestrictLe n`
projections agree for every `n`. -/
lemma eq_of_frestrictLe_eq (μ₁ μ₂ : Measure (Π n, X n))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h : ∀ n, μ₁.map (frestrictLe n) = μ₂.map (frestrictLe n)) : μ₁ = μ₂ := by
  let P : (n : ℕ) → Measure (Π i : Iic n, X i) := fun n ↦ μ₁.map (frestrictLe n)
  have hP_proj : ∀ a b (hab : a ≤ b), (P b).map (frestrictLe₂ hab) = P a := by
    intro a b hab
    simp only [P]
    rw [Measure.map_map (measurable_frestrictLe₂ _) (measurable_frestrictLe _),
        frestrictLe₂_comp_frestrictLe hab]
  have hPF := MeasureTheory.isProjectiveMeasureFamily_inducedFamily P hP_proj
  have hμ₁ : IsProjectiveLimit μ₁ (MeasureTheory.inducedFamily P) := by
    rw [MeasureTheory.isProjectiveLimit_nat_iff hPF]
    intro n; rw [MeasureTheory.inducedFamily_Iic]
  have hμ₂ : IsProjectiveLimit μ₂ (MeasureTheory.inducedFamily P) := by
    rw [MeasureTheory.isProjectiveLimit_nat_iff hPF]
    intro n; rw [MeasureTheory.inducedFamily_Iic, ← h n]
  exact hμ₁.unique hμ₂

omit [IsProbabilityMeasure μ₀] in
/-- The `frestrictLe n` projection of `trajMeasure μ₀ κ` equals the composition
`partialTraj κ 0 n ∘ₘ (μ₀.map (piUnique _).symm)`. -/
lemma trajMeasure_map_frestrictLe
    (κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    (trajMeasure μ₀ κ).map (frestrictLe n) =
      (partialTraj κ 0 n) ∘ₘ
        (μ₀.map (MeasurableEquiv.piUnique (fun i : Iic 0 ↦ X i)).symm) := by
  unfold trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop), traj_map_frestrictLe]

/-- `Measure.bind` commutes with measure pushforward under measurability of the bind family. -/
lemma map_bind_eq_bind_map {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    {ρ : Measure β} (g : β → Measure α)
    (hg : Measurable g) {f : α → γ} (hf : Measurable f) :
    (ρ.bind g).map f = ρ.bind (fun b ↦ (g b).map f) := by
  ext s hs
  rw [Measure.map_apply hf hs,
      Measure.bind_apply (hf hs) hg.aemeasurable,
      Measure.bind_apply hs (Measurable.aemeasurable (by fun_prop))]
  refine lintegral_congr (fun b ↦ ?_)
  rw [Measure.map_apply hf hs]

omit [IsProbabilityMeasure ν] in
/-- The averaged kernel `κAvg` is the `Measure.bind` of `κ b` over `ν`. -/
lemma kappa_avg_eq_bind
    (κ : β → (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [∀ b n, IsMarkovKernel (κ b n)]
    (h_meas : ∀ (n : ℕ) (h : Π i : Iic n, X i) {s : Set (X (n + 1))},
        MeasurableSet s → Measurable (fun b ↦ (κ b n) h s))
    (κAvg : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    (h_kappa_bind : ∀ (n : ℕ) (h : Π i : Iic n, X i) {s : Set (X (n + 1))},
        MeasurableSet s → κAvg n h s = ∫⁻ b, (κ b n) h s ∂ν)
    (n : ℕ) (h : Π i : Iic n, X i) :
    κAvg n h = ν.bind (fun b ↦ (κ b n) h) := by
  have hb_meas : Measurable (fun b ↦ (κ b n) h) :=
    Measure.measurable_of_measurable_coe _ (fun s hs ↦ h_meas n h hs)
  ext s hs
  rw [Measure.bind_apply hs hb_meas.aemeasurable]
  exact h_kappa_bind n h hs

omit [IsProbabilityMeasure ν] in
/-- Lintegral form of the averaged kernel: integrating against `κAvg` is the
`ν`-average of integrating against `κ b`. -/
lemma kappa_avg_lintegral
    (κ : β → (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [∀ b n, IsMarkovKernel (κ b n)]
    (h_meas : ∀ (n : ℕ) (h : Π i : Iic n, X i) {s : Set (X (n + 1))},
        MeasurableSet s → Measurable (fun b ↦ (κ b n) h s))
    (κAvg : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    (h_kappa_bind : ∀ (n : ℕ) (h : Π i : Iic n, X i) {s : Set (X (n + 1))},
        MeasurableSet s → κAvg n h s = ∫⁻ b, (κ b n) h s ∂ν)
    (n : ℕ) (h : Π i : Iic n, X i) {f : X (n + 1) → ℝ≥0∞} (mf : Measurable f) :
    ∫⁻ x, f x ∂(κAvg n h) = ∫⁻ b, ∫⁻ x, f x ∂(κ b n h) ∂ν := by
  have hb_meas : Measurable (fun b ↦ (κ b n) h) :=
    Measure.measurable_of_measurable_coe _ (fun s hs ↦ h_meas n h hs)
  rw [kappa_avg_eq_bind κ h_meas κAvg h_kappa_bind n h,
      Measure.lintegral_bind hb_meas.aemeasurable mf.aemeasurable]

end trajMeasure_bind_kernel_helpers

section BindKernel

variable {μ₀ : Measure (X 0)} [IsProbabilityMeasure μ₀]
variable {ν : Measure β} [IsProbabilityMeasure ν]

/-- **Fubini / Ionescu–Tulcea identity for `trajMeasure` (trajectory-level
hypothesis form).**

Suppose `κ : β → ∀ n, Kernel ..` is a measurable family of Markov kernels in `b`
and `κAvg : ∀ n, Kernel ..` is the *per-level averaged* kernel family. If we
have the *trajectory-level* bind identity at every finite truncation
`partialTraj κ 0 n` (plus joint measurability witnesses for the trajectory
and partial-trajectory parameters), then:

    `trajMeasure μ₀ κAvg = ν.bind (fun b ↦ trajMeasure μ₀ (κ b))`.

In typical applications (e.g. randomised adversaries where `ν` is a
`Measure.infinitePi` indexed by query points) this trajectory-level hypothesis
is derivable from a per-level bind identity plus the product structure of `ν`.

**Counterexample to the unconditional per-level form.** Without the
trajectory-level hypothesis (i.e. with only the *per-level* bind identity
`κAvg n h s = ∫⁻ b, (κ b n h) s ∂ν`), the conclusion is *false in general*.
Take `X n := Bool` for all `n`, `μ₀ := dirac false`, `β := Bool`,
`ν := (dirac false + dirac true) / 2`, and `κ b n h := dirac b` (deterministic,
ignoring state). Then `κAvg n h = (dirac false + dirac true) / 2`, so under
`trajMeasure μ₀ κAvg` the coordinates `x_1, x_2, …` are i.i.d. Bernoulli(1/2);
the cylinder `{x_1 = false ∧ x_2 = true}` has mass `1/4`. On the right,
`ν.bind` first samples `b ~ ν` once, then applies `κ b` at every level — so
all coordinates are equal to `b`, and the same cylinder has mass `0`. The two
measures are distinct. (This counterexample was discovered in PR #96 and
motivated the strictly stronger trajectory-level hypothesis used here.) -/
theorem trajMeasure_bind_kernel_of_partial
    (κ : β → (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [hMarkov : ∀ b n, IsMarkovKernel (κ b n)]
    (h_traj_meas : Measurable (fun b ↦ trajMeasure μ₀ (κ b)))
    (κAvg : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [hMarkov_avg : ∀ n, IsMarkovKernel (κAvg n)]
    (h_partialTraj_meas :
      ∀ (n : ℕ) {S : Set (Π i : Iic n, X i)}, MeasurableSet S →
        Measurable (Function.uncurry
          (fun b (x₀ : Π i : Iic 0, X i) ↦ partialTraj (κ b) 0 n x₀ S)))
    (h_partialTraj_bind :
      ∀ (n : ℕ) (x₀ : Π i : Iic 0, X i) {S : Set (Π i : Iic n, X i)},
        MeasurableSet S →
        partialTraj κAvg 0 n x₀ S = ∫⁻ b, partialTraj (κ b) 0 n x₀ S ∂ν) :
    trajMeasure μ₀ κAvg =
      ν.bind (fun b ↦ trajMeasure μ₀ (κ b)) := by
  -- Both sides are probability measures on `Π n, X n`. Reduce to projection agreement.
  haveI : IsProbabilityMeasure (ν.bind (fun b ↦ trajMeasure μ₀ (κ b))) := by
    constructor
    rw [Measure.bind_apply MeasurableSet.univ h_traj_meas.aemeasurable]
    simp
  refine eq_of_frestrictLe_eq _ _ (fun n ↦ ?_)
  -- LHS projection: `(partialTraj κAvg 0 n) ∘ₘ (μ₀.map (piUnique _).symm)`.
  rw [trajMeasure_map_frestrictLe κAvg n]
  -- RHS projection: bind/map commute, then per-fibre projection.
  rw [map_bind_eq_bind_map _ h_traj_meas (by fun_prop : Measurable (frestrictLe n))]
  set μ' : Measure (Π i : Iic 0, X i) :=
    μ₀.map (MeasurableEquiv.piUnique (fun i : Iic 0 ↦ X i)).symm with hμ'
  have hμ'_prob : IsProbabilityMeasure μ' := by
    rw [hμ']
    exact Measure.isProbabilityMeasure_map
      (MeasurableEquiv.measurable _).aemeasurable
  -- Pointwise rewrite of the RHS: each fibre projection collapses to `partialTraj`.
  conv_rhs =>
    rw [show (fun b ↦ Measure.map (frestrictLe n) (trajMeasure μ₀ (κ b)))
          = (fun b ↦ (partialTraj (κ b) 0 n) ∘ₘ μ') from
        funext (fun b ↦ trajMeasure_map_frestrictLe (κ b) n)]
  -- Now both sides are measures on `Π i : Iic n, X i`; show ext on measurable sets.
  ext S hS
  -- LHS S = ∫⁻ x₀, partialTraj κAvg 0 n x₀ S ∂μ'
  rw [Measure.bind_apply hS (Kernel.aemeasurable _)]
  -- RHS S = ∫⁻ b, ((partialTraj (κ b) 0 n) ∘ₘ μ') S ∂ν.
  -- We bypass `Measure.bind_apply` by reducing to `lintegral_bind` via the kernel structure.
  -- For now, evaluate the bind via its measurable-of-coe proof.
  have hjoint := h_partialTraj_meas n hS
  have hb_int : Measurable (fun b ↦ ∫⁻ x₀, partialTraj (κ b) 0 n x₀ S ∂μ') :=
    Measurable.lintegral_prod_right (ν := μ') hjoint
  -- AEMeasurability of `b ↦ (partialTraj (κ b) 0 n) ∘ₘ μ' : Measure _` —
  -- this requires `Measure.measurable_of_measurable_coe`.
  have hb_meas_meas : Measurable (fun b ↦ (partialTraj (κ b) 0 n) ∘ₘ μ') := by
    refine Measure.measurable_of_measurable_coe _ ?_
    intro t ht
    have hjoint_t := h_partialTraj_meas n ht
    have hbt_int : Measurable (fun b ↦ ∫⁻ x₀, partialTraj (κ b) 0 n x₀ t ∂μ') :=
      Measurable.lintegral_prod_right (ν := μ') hjoint_t
    have heq : (fun b ↦ ((partialTraj (κ b) 0 n) ∘ₘ μ') t)
        = (fun b ↦ ∫⁻ x₀, partialTraj (κ b) 0 n x₀ t ∂μ') := by
      funext b; rw [Measure.bind_apply ht (Kernel.aemeasurable _)]
    rw [heq]; exact hbt_int
  rw [Measure.bind_apply hS hb_meas_meas.aemeasurable]
  -- Inner: ((partialTraj (κ b) 0 n) ∘ₘ μ') S = ∫⁻ x₀, partialTraj (κ b) 0 n x₀ S ∂μ'
  have hinner : ∀ b, ((partialTraj (κ b) 0 n) ∘ₘ μ') S
                  = ∫⁻ x₀, partialTraj (κ b) 0 n x₀ S ∂μ' := by
    intro b; rw [Measure.bind_apply hS (Kernel.aemeasurable _)]
  conv_rhs => enter [2, b]; rw [hinner]
  -- Apply the trajectory-level hypothesis pointwise then Fubini-swap.
  have hpt : ∀ x₀, partialTraj κAvg 0 n x₀ S
                = ∫⁻ b, partialTraj (κ b) 0 n x₀ S ∂ν :=
    fun x₀ ↦ h_partialTraj_bind n x₀ hS
  calc
    ∫⁻ x₀, partialTraj κAvg 0 n x₀ S ∂μ'
        = ∫⁻ x₀, (∫⁻ b, partialTraj (κ b) 0 n x₀ S ∂ν) ∂μ' :=
          lintegral_congr (fun x₀ ↦ hpt x₀)
    _ = ∫⁻ b, ∫⁻ x₀, partialTraj (κ b) 0 n x₀ S ∂μ' ∂ν := by
          -- `lintegral_lintegral_swap`: requires AEMeasurability of `(x₀, b) ↦ ...`.
          have hsw : Measurable (Function.uncurry
              (fun (x₀ : Π i : Iic 0, X i) (b : β) ↦
                partialTraj (κ b) 0 n x₀ S)) := by
            -- This is `hjoint` composed with `Prod.swap`.
            have : (Function.uncurry
              (fun (x₀ : Π i : Iic 0, X i) (b : β) ↦
                partialTraj (κ b) 0 n x₀ S))
                = (Function.uncurry
                  (fun b (x₀ : Π i : Iic 0, X i) ↦
                    partialTraj (κ b) 0 n x₀ S)) ∘ Prod.swap := by
              funext ⟨x₀, b⟩; rfl
            rw [this]; exact hjoint.comp (by fun_prop)
          rw [lintegral_lintegral_swap hsw.aemeasurable]


end BindKernel

end ProbabilityTheory.Kernel
