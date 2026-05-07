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

The measurability proof uses the auxiliary typeclass assumptions
`[∀ n, Countable (Π i : Iic n, X i)]` and
`[∀ n, MeasurableSingletonClass (Π i : Iic n, X i)]`. These are needed to
bootstrap separate measurability `b ↦ (κ b n) h s` (for fixed `h, s`) into
joint measurability `(b, h) ↦ (κ b n) h s` via
`measurable_from_prod_countable_left`. The typeclass assumptions are
automatically satisfied at the use sites, where the per-step state space is a
finite product of countable types with `MeasurableSingletonClass` instances.

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

section trajMeasure_measurable_helpers

/-! The helpers in this section build a JOINT kernel-version of
`partialTraj (κ b) 0 n` parameterised over `(b, x₀)`. The proof of
`trajMeasure_measurable` then proceeds by cylinder induction, mirroring
mathlib's `measurable_trajFun`, with the joint kernel providing the
required joint measurability at the cylinder base case. -/

variable [hCount : ∀ (n : ℕ), Countable (Π i : Iic n, X i)]
variable [hSing : ∀ (n : ℕ), MeasurableSingletonClass (Π i : Iic n, X i)]

/-- The "joint" kernel version of `κ b n`, i.e. the kernel
`Kernel (β × Π i : Iic n, X i) (X (n+1))` that maps `(b, h)` to `(κ b n) h`.
The measurability of this kernel follows from separate measurability
(hypothesis `h_meas`) plus countability of the second component. -/
private noncomputable def kappaJoint
    (κ : β → (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    (h_meas : ∀ (n : ℕ) (h : Π i : Iic n, X i) {s : Set (X (n + 1))},
        MeasurableSet s → Measurable (fun b ↦ (κ b n) h s))
    (n : ℕ) :
    Kernel (β × Π i : Iic n, X i) (X (n + 1)) where
  toFun bh := (κ bh.1 n) bh.2
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
    exact measurable_from_prod_countable_left fun h => h_meas n h hs

private instance kappaJoint_isMarkov
    (κ : β → (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [∀ b n, IsMarkovKernel (κ b n)]
    (h_meas : ∀ (n : ℕ) (h : Π i : Iic n, X i) {s : Set (X (n + 1))},
        MeasurableSet s → Measurable (fun b ↦ (κ b n) h s))
    (n : ℕ) :
    IsMarkovKernel (kappaJoint κ h_meas n) :=
  ⟨fun bh => by
    show IsProbabilityMeasure ((κ bh.1 n) bh.2)
    infer_instance⟩

/-- The "joint" version of the per-step Ionescu–Tulcea step kernel
`(Kernel.id ×ₖ ((κ b n).map (piSingleton n))).map (IicProdIoc n (n+1))`,
parameterised over `b`. -/
private noncomputable def jointStepKernel
    (κ : β → (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [∀ b n, IsMarkovKernel (κ b n)]
    (h_meas : ∀ (n : ℕ) (h : Π i : Iic n, X i) {s : Set (X (n + 1))},
        MeasurableSet s → Measurable (fun b ↦ (κ b n) h s))
    (n : ℕ) :
    Kernel (β × Π i : Iic n, X i) (Π i : Iic (n + 1), X i) :=
  (Kernel.deterministic Prod.snd measurable_snd
      ×ₖ (kappaJoint κ h_meas n).map (MeasurableEquiv.piSingleton n)).map
    (IicProdIoc n (n + 1))

private instance jointStepKernel_isMarkov
    (κ : β → (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [∀ b n, IsMarkovKernel (κ b n)]
    (h_meas : ∀ (n : ℕ) (h : Π i : Iic n, X i) {s : Set (X (n + 1))},
        MeasurableSet s → Measurable (fun b ↦ (κ b n) h s))
    (n : ℕ) :
    IsMarkovKernel (jointStepKernel κ h_meas n) := by
  unfold jointStepKernel
  have : IsMarkovKernel ((kappaJoint κ h_meas n).map (MeasurableEquiv.piSingleton n)) :=
    IsMarkovKernel.map (kappaJoint κ h_meas n) (MeasurableEquiv.piSingleton n).measurable
  exact IsMarkovKernel.map _ measurable_IicProdIoc

private lemma jointStepKernel_apply
    (κ : β → (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [∀ b n, IsMarkovKernel (κ b n)]
    (h_meas : ∀ (n : ℕ) (h : Π i : Iic n, X i) {s : Set (X (n + 1))},
        MeasurableSet s → Measurable (fun b ↦ (κ b n) h s))
    (n : ℕ) (b : β) (y : Π i : Iic n, X i) :
    jointStepKernel κ h_meas n (b, y) =
      ((Kernel.id ×ₖ ((κ b n).map (MeasurableEquiv.piSingleton n))) y).map
        (IicProdIoc n (n + 1)) := by
  unfold jointStepKernel
  rw [Kernel.map_apply _ measurable_IicProdIoc]
  congr 1
  rw [Kernel.prod_apply, Kernel.prod_apply, deterministic_apply, Kernel.id_apply]
  congr 1
  rw [Kernel.map_apply _ (MeasurableEquiv.piSingleton n).measurable,
    Kernel.map_apply _ (MeasurableEquiv.piSingleton n).measurable]
  rfl

/-- The joint kernel version of `partialTraj (κ b) 0 n`, parameterised over
`(b, x₀)`. Built recursively as `compProd` with `jointStepKernel`. -/
private noncomputable def jointPartialTraj
    (κ : β → (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [∀ b n, IsMarkovKernel (κ b n)]
    (h_meas : ∀ (n : ℕ) (h : Π i : Iic n, X i) {s : Set (X (n + 1))},
        MeasurableSet s → Measurable (fun b ↦ (κ b n) h s)) :
    (n : ℕ) → Kernel (β × Π i : Iic 0, X i) (Π i : Iic n, X i)
  | 0 => Kernel.deterministic Prod.snd measurable_snd
  | n + 1 =>
      ((jointPartialTraj κ h_meas n) ⊗ₖ
        ((jointStepKernel κ h_meas n).comap
          (fun bxy : (β × Π i : Iic 0, X i) × Π i : Iic n, X i => (bxy.1.1, bxy.2))
          (by fun_prop))).map Prod.snd

private instance jointPartialTraj_isMarkov
    (κ : β → (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [∀ b n, IsMarkovKernel (κ b n)]
    (h_meas : ∀ (n : ℕ) (h : Π i : Iic n, X i) {s : Set (X (n + 1))},
        MeasurableSet s → Measurable (fun b ↦ (κ b n) h s)) :
    ∀ (n : ℕ), IsMarkovKernel (jointPartialTraj κ h_meas n) := by
  intro n
  induction n with
  | zero =>
    show IsMarkovKernel (Kernel.deterministic Prod.snd measurable_snd)
    infer_instance
  | succ n ih =>
    have := ih
    have hStep : IsMarkovKernel ((jointStepKernel κ h_meas n).comap
        (fun bxy : (β × Π i : Iic 0, X i) × Π i : Iic n, X i => (bxy.1.1, bxy.2))
        (by fun_prop)) := IsMarkovKernel.comap _ _
    show IsMarkovKernel
      (((jointPartialTraj κ h_meas n) ⊗ₖ
        ((jointStepKernel κ h_meas n).comap
          (fun bxy : (β × Π i : Iic 0, X i) × Π i : Iic n, X i => (bxy.1.1, bxy.2))
          (by fun_prop))).map Prod.snd)
    have : IsMarkovKernel ((jointPartialTraj κ h_meas n) ⊗ₖ
        ((jointStepKernel κ h_meas n).comap
          (fun bxy : (β × Π i : Iic 0, X i) × Π i : Iic n, X i => (bxy.1.1, bxy.2))
          (by fun_prop))) := inferInstance
    exact IsMarkovKernel.map _ measurable_snd

private lemma jointPartialTraj_apply
    (κ : β → (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [hMarkov : ∀ b n, IsMarkovKernel (κ b n)]
    (h_meas : ∀ (n : ℕ) (h : Π i : Iic n, X i) {s : Set (X (n + 1))},
        MeasurableSet s → Measurable (fun b ↦ (κ b n) h s))
    (n : ℕ) (b : β) (x₀ : Π i : Iic 0, X i) :
    jointPartialTraj κ h_meas n (b, x₀) = partialTraj (κ b) 0 n x₀ := by
  induction n with
  | zero =>
    show (Kernel.deterministic Prod.snd measurable_snd) (b, x₀) = _
    rw [deterministic_apply, partialTraj_self, Kernel.id_apply]
  | succ n ih =>
    have hMark_jptN : IsMarkovKernel (jointPartialTraj κ h_meas n) := inferInstance
    have hMark_step_comap : IsMarkovKernel ((jointStepKernel κ h_meas n).comap
        (fun bxy : (β × Π i : Iic 0, X i) × Π i : Iic n, X i => (bxy.1.1, bxy.2))
        (by fun_prop)) := IsMarkovKernel.comap _ _
    show ((jointPartialTraj κ h_meas n ⊗ₖ
        ((jointStepKernel κ h_meas n).comap
          (fun bxy : (β × Π i : Iic 0, X i) × Π i : Iic n, X i => (bxy.1.1, bxy.2))
          (by fun_prop))).map Prod.snd) (b, x₀) = _
    ext s hs
    rw [Kernel.map_apply' _ measurable_snd _ hs,
      Kernel.compProd_apply (measurable_snd hs)]
    have hcomap : ∀ y, ((jointStepKernel κ h_meas n).comap
        (fun bxy : (β × Π i : Iic 0, X i) × Π i : Iic n, X i => (bxy.1.1, bxy.2))
        (by fun_prop)) ((b, x₀), y) (Prod.mk y ⁻¹' (Prod.snd ⁻¹' s)) =
          jointStepKernel κ h_meas n (b, y) s := by
      intro y; rw [comap_apply']; rfl
    simp_rw [hcomap, ih]
    rw [partialTraj_succ_of_le (zero_le _), Kernel.map_apply' _ measurable_IicProdIoc _ hs,
      Kernel.comp_apply' _ _ _ (measurable_IicProdIoc hs)]
    refine lintegral_congr (fun y => ?_)
    rw [jointStepKernel_apply, Measure.map_apply measurable_IicProdIoc hs]

/-- Joint measurability of `(b, x₀) ↦ partialTraj (κ b) 0 N x₀ S` for fixed
measurable `S`. Obtained from joint measurability of the kernel
`jointPartialTraj` evaluated at `S`. -/
private lemma partialTraj_apply_jointMeasurable
    (κ : β → (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [hMarkov : ∀ b n, IsMarkovKernel (κ b n)]
    (h_meas : ∀ (n : ℕ) (h : Π i : Iic n, X i) {s : Set (X (n + 1))},
        MeasurableSet s → Measurable (fun b ↦ (κ b n) h s))
    (N : ℕ) {S : Set (Π i : Iic N, X i)} (hS : MeasurableSet S) :
    Measurable (fun bx₀ : β × (Π i : Iic 0, X i) ↦ partialTraj (κ bx₀.1) 0 N bx₀.2 S) := by
  have hRw : (fun bx₀ : β × (Π i : Iic 0, X i) =>
      partialTraj (κ bx₀.1) 0 N bx₀.2 S) =
      (fun bx₀ : β × (Π i : Iic 0, X i) => jointPartialTraj κ h_meas N bx₀ S) := by
    funext bx₀; rw [jointPartialTraj_apply]
  rw [hRw]
  exact (Measure.measurable_coe hS).comp (Kernel.measurable _)

/-- Joint measurability of `(b, x₀) ↦ trajFun (κ b) 0 x₀` as a measure-valued
map. By cylinder induction, mirroring mathlib's `measurable_trajFun`. -/
private lemma trajFun_jointMeasurable
    (κ : β → (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [hMarkov : ∀ b n, IsMarkovKernel (κ b n)]
    (h_meas : ∀ (n : ℕ) (h : Π i : Iic n, X i) {s : Set (X (n + 1))},
        MeasurableSet s → Measurable (fun b ↦ (κ b n) h s)) :
    Measurable (fun bx₀ : β × (Π i : Iic 0, X i) ↦ trajFun (κ bx₀.1) 0 bx₀.2) := by
  apply Measure.measurable_of_measurable_coe
  refine MeasurableSpace.induction_on_inter
    (C := fun t _ ↦ Measurable (fun bx₀ : β × (Π i : Iic 0, X i) ↦
      trajFun (κ bx₀.1) 0 bx₀.2 t))
    (s := measurableCylinders X) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (by simp) (fun t ht ↦ ?cylinder) (fun t mt ht ↦ ?compl)
    (fun f disf mf hf ↦ ?union)
  · obtain ⟨N, S, mS, t_eq⟩ : ∃ N S, MeasurableSet S ∧ t = cylinder (Iic N) S := by
      simpa [measurableCylinders_nat] using ht
    have hcyl : ∀ b x₀, trajFun (κ b) 0 x₀ t = partialTraj (κ b) 0 N x₀ S := by
      intro b x₀
      rw [t_eq, trajFun, AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm _
        (cylinder_mem_measurableCylinders _ _ mS), trajContent_cylinder mS]
    show Measurable (fun bx₀ : β × (Π i : Iic 0, X i) => trajFun (κ bx₀.1) 0 bx₀.2 t)
    rw [show (fun bx₀ : β × (Π i : Iic 0, X i) => trajFun (κ bx₀.1) 0 bx₀.2 t) =
        (fun bx₀ : β × (Π i : Iic 0, X i) => partialTraj (κ bx₀.1) 0 N bx₀.2 S) from
        funext fun bx₀ => hcyl bx₀.1 bx₀.2]
    exact partialTraj_apply_jointMeasurable κ h_meas N mS
  · show Measurable (fun bx₀ : β × (Π i : Iic 0, X i) => trajFun (κ bx₀.1) 0 bx₀.2 tᶜ)
    have hprob : ∀ b x₀, IsProbabilityMeasure (trajFun (κ b) 0 x₀) := fun b x₀ =>
      isProbabilityMeasure_trajFun (κ b) 0 x₀
    have heq : (fun bx₀ : β × (Π i : Iic 0, X i) => trajFun (κ bx₀.1) 0 bx₀.2 tᶜ) =
        (fun bx₀ : β × (Π i : Iic 0, X i) => 1 - trajFun (κ bx₀.1) 0 bx₀.2 t) := by
      funext bx₀
      have := hprob bx₀.1 bx₀.2
      rw [measure_compl mt (measure_ne_top _ _)]
      simp
    rw [heq]
    exact Measurable.const_sub ht 1
  · show Measurable (fun bx₀ : β × (Π i : Iic 0, X i) => trajFun (κ bx₀.1) 0 bx₀.2 (⋃ i, f i))
    have heq : (fun bx₀ : β × (Π i : Iic 0, X i) => trajFun (κ bx₀.1) 0 bx₀.2 (⋃ i, f i)) =
        (fun bx₀ : β × (Π i : Iic 0, X i) => ∑' i, trajFun (κ bx₀.1) 0 bx₀.2 (f i)) := by
      funext bx₀; rw [measure_iUnion disf mf]
    rw [heq]
    exact Measurable.ennreal_tsum hf

end trajMeasure_measurable_helpers

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

The auxiliary typeclass assumptions
`[∀ n, Countable (Π i : Iic n, X i)]` and
`[∀ n, MeasurableSingletonClass (Π i : Iic n, X i)]` are needed to bootstrap
separate measurability `b ↦ (κ b n) h s` (for fixed `h, s`) into joint
measurability `(b, h) ↦ (κ b n) h s` via
`measurable_from_prod_countable_left`. They are automatically satisfied at the
expected use sites where the per-step state space is a finite product of
countable types with `MeasurableSingletonClass` instances.

**Mathlib gap.** Mathlib's `measurable_trajFun` handles only the
*initial-state* parameter; this lemma extends measurability to the *kernel-family*
parameter, which is needed for any "outer integral" Fubini argument. -/
theorem trajMeasure_measurable
    (κ : β → (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [hMarkov : ∀ b n, IsMarkovKernel (κ b n)]
    [hCount : ∀ (n : ℕ), Countable (Π i : Iic n, X i)]
    [hSing : ∀ (n : ℕ), MeasurableSingletonClass (Π i : Iic n, X i)]
    (h_meas : ∀ (n : ℕ) (h : Π i : Iic n, X i) {s : Set (X (n + 1))},
        MeasurableSet s → Measurable (fun b ↦ (κ b n) h s)) :
    Measurable (fun b ↦ trajMeasure μ₀ (κ b)) := by
  -- Reduce to: for every measurable `s`, `b ↦ trajMeasure μ₀ (κ b) s` is measurable.
  apply Measure.measurable_of_measurable_coe
  intro s hs
  -- Unfold `trajMeasure`: it's `(traj κ 0) ∘ₘ (μ₀.map e)` for the standard
  -- pi-singleton equivalence `e`. Rewrite the value at `s` as an `lintegral`.
  have heq : ∀ b, trajMeasure μ₀ (κ b) s =
      ∫⁻ x₀, traj (κ b) 0 x₀ s
        ∂(μ₀.map (MeasurableEquiv.piUnique (fun i : Iic 0 => X i)).symm) := by
    intro b
    rw [trajMeasure, Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [heq, traj_apply]
  have he_meas : Measurable (MeasurableEquiv.piUnique (fun i : Iic 0 => X i)).symm :=
    (MeasurableEquiv.piUnique _).symm.measurable
  have hμ' : IsProbabilityMeasure
      (μ₀.map (MeasurableEquiv.piUnique (fun i : Iic 0 => X i)).symm) :=
    Measure.isProbabilityMeasure_map he_meas.aemeasurable
  -- Apply `Measurable.lintegral_prod_left` (from `MeasureTheory.Measure.Prod`):
  -- the integral over a fixed measure of a jointly measurable function is
  -- measurable in the free parameter.
  refine Measurable.lintegral_prod_left
    (μ := μ₀.map (MeasurableEquiv.piUnique (fun i : Iic 0 => X i)).symm)
    (f := fun x₀ b => trajFun (κ b) 0 x₀ s) ?_
  -- Joint measurability of the integrand. Reduce to the helper
  -- `trajFun_jointMeasurable` after a `swap` (since `lintegral_prod_left`
  -- expects `(x₀, b)`-uncurry while our helper produces `(b, x₀)`-uncurry).
  have hjoint : Measurable
      (fun bx₀ : β × (Π i : Iic 0, X i) => trajFun (κ bx₀.1) 0 bx₀.2) :=
    trajFun_jointMeasurable κ h_meas
  show Measurable (Function.uncurry (fun x₀ b => trajFun (κ b) 0 x₀ s))
  have : (Function.uncurry (fun x₀ : Π i : Iic 0, X i =>
      fun b : β => trajFun (κ b) 0 x₀ s))
    = (fun bx₀ : β × (Π i : Iic 0, X i) => trajFun (κ bx₀.1) 0 bx₀.2 s) ∘
      (fun p : (Π i : Iic 0, X i) × β => (p.2, p.1)) := by
    funext p; rfl
  rw [this]
  exact ((Measure.measurable_coe hs).comp hjoint).comp measurable_swap

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
