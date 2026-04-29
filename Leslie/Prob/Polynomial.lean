/-
M1 W3 — Polynomial uniformity library (foundations).

`uniformWithFixedZero d s` is the uniform distribution over polynomials
of degree ≤ d with constant term `s`. The headline theorem
`evals_uniform` says: for `pts ⊂ F` with `|pts| ≤ d`, `0 ∉ pts`, and
`d + 1 ≤ Fintype.card F`, the joint distribution of evaluations
`(f(p))_{p∈pts}` is uniform on `pts → F`. This is the algebraic core
of Shamir secrecy (M1 W4).

The proof of `evals_uniform` reduces to a direct injectivity argument:
for `pts.card = d`, the eval map `(Fin d → F) → (pts → F)` is
injective (any two coefficient vectors agreeing on `pts ∪ {0}` —
which has size `d + 1` — produce a polynomial of degree ≤ d with
`d + 1` zeros, hence is zero), and bijectivity follows from card
equality. For `pts.card < d`, extend `pts` to `pts'` of size `d` in
`F \ ({0} ∪ pts)` (requiring `d + 1 ≤ Fintype.card F`), apply the
equal-card case to `pts'`, then project — using a constant-fiber
surjection helper.

Status (M1 W3 polish):
  * Helper `PMF.uniform_map_of_bijective` proved.
  * Helper `PMF.uniform_map_of_surjective_constFiber` proved
    (pushforward under constant-fiber surjection is uniform).
  * `uniformWithFixedZero`, `uniformBivariateWithFixedZero` defined.
  * `evals_uniform` proved (with extra hypothesis `d + 1 ≤ Fintype.card F`).
  * `bivariate_evals_uniform` deferred to M2 per plan v2.2.

Per implementation plan v2.2 §M1 W3.
-/

import Leslie.Prob.PMF
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Fintype.EquivFin

namespace Leslie.Prob.Polynomial

open scoped ENNReal

/-! ## Pushforward of uniform under a bijection

Mathlib doesn't expose this directly; it is the workhorse for every
"uniform-stays-uniform-under-bijection" lemma below. Proof: the
forward marginal at each codomain point is exactly the source's
mass at the unique preimage, which is `1/|α| = 1/|β|`. -/

theorem _root_.PMF.uniform_map_of_bijective
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    {f : α → β} (hf : Function.Bijective f) :
    (PMF.uniform α).map f = PMF.uniform β := by
  apply PMF.ext
  intro b
  rw [PMF.map_apply, PMF.uniform_apply]
  obtain ⟨a, ha⟩ := hf.surjective b
  have hcard : (Fintype.card α : ℝ≥0∞) = Fintype.card β :=
    congrArg Nat.cast (Fintype.card_of_bijective hf)
  rw [tsum_eq_single a]
  · simp [ha, hcard]
  · intro a' ha'
    have : f a' ≠ b := fun h_eq =>
      ha' (hf.injective (h_eq.trans ha.symm))
    simp [Ne.symm this]

/-! ## Pushforward of uniform under a constant-fiber surjection

If every fiber of `g : α → β` has the same size `k > 0`, then the
pushforward of `uniform α` under `g` is `uniform β`. Generalizes
`uniform_map_of_bijective` (where `k = 1`). -/

theorem _root_.PMF.uniform_map_of_surjective_constFiber
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [DecidableEq α] [DecidableEq β]
    (g : α → β) (k : ℕ) (hk : 0 < k)
    (h_fib : ∀ b : β, (Finset.univ.filter (fun a => g a = b)).card = k) :
    (PMF.uniform α).map g = PMF.uniform β := by
  apply PMF.ext
  intro b
  rw [PMF.map_apply]
  simp only [PMF.uniform_apply]
  have h_α_eq : Fintype.card α = Fintype.card β * k := by
    have hsumeq : (Finset.univ : Finset α).card =
        ∑ b : β, (Finset.univ.filter (fun a => g a = b)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext a
        simp
      · intro x _ y _ hxy
        simp only [Function.onFun]
        rw [Finset.disjoint_filter]
        intro a _ ha
        exact fun ha' => hxy (ha.symm.trans ha')
    have h2 : (Finset.univ : Finset α).card = Fintype.card α := rfl
    rw [h2] at hsumeq
    rw [hsumeq, Finset.sum_congr rfl (fun b _ => h_fib b), Finset.sum_const,
        Finset.card_univ, smul_eq_mul]
  rw [tsum_eq_sum (s := Finset.univ.filter (fun a => g a = b))
      (fun a ha => by simp at ha; simp [Ne.symm ha])]
  have hsum : ∀ a ∈ (Finset.univ.filter (fun a => g a = b)),
      (if b = g a then ((Fintype.card α : ℝ≥0∞)⁻¹) else 0) =
        ((Fintype.card α : ℝ≥0∞)⁻¹) := by
    intro a ha
    simp at ha
    simp [ha]
  rw [Finset.sum_congr rfl hsum, Finset.sum_const, h_fib b, h_α_eq]
  rw [nsmul_eq_mul]
  push_cast
  rw [ENNReal.mul_inv]
  · rw [← mul_assoc, mul_comm (k : ℝ≥0∞), mul_assoc, ENNReal.mul_inv_cancel]
    · simp
    · exact_mod_cast hk.ne'
    · simp
  · left; exact_mod_cast (Fintype.card_pos).ne'
  · left; simp

/-! ## Pi-lift of a uniform pushforward

If `h : α → β` pushes forward `uniform α` to `uniform β`, then for any
finite nonempty index `ι`, the per-coordinate map `f ↦ (i ↦ h (f i))`
pushes forward `uniform (ι → α)` to `uniform (ι → β)`.

Proof sketch: from `(uniform α).map h = uniform β`, every fiber of `h`
has the same size `k = |α|/|β|`. For the per-coordinate map
`Φ : (ι → α) → (ι → β)`, the fiber over `g` is the product over `i` of
the per-coordinate fibers `{a | h a = g i}`, hence has size `k^|ι|`,
constant in `g`. Conclude via `uniform_map_of_surjective_constFiber`. -/

theorem _root_.PMF.uniform_pi_map_of_uniform_map
    {ι α β : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [DecidableEq α] [DecidableEq β]
    {h : α → β} (h_uniform : (PMF.uniform α).map h = PMF.uniform β) :
    (PMF.uniform (ι → α)).map (fun f i => h (f i)) = PMF.uniform (ι → β) := by
  -- Extract the constant fiber size of `h` from the PMF equation.
  -- For any b : β, the fiber {a | h a = b} has size |α|/|β|.
  have h_card_β_pos : 0 < Fintype.card β := Fintype.card_pos
  have h_card_α_pos : 0 < Fintype.card α := Fintype.card_pos
  -- The fiber size for h.
  have h_fib_h : ∀ b : β,
      (Finset.univ.filter (fun a : α => h a = b)).card * Fintype.card β
        = Fintype.card α := by
    intro b
    have h_pmf : ((PMF.uniform α).map h) b = (PMF.uniform β) b := by rw [h_uniform]
    simp only [PMF.map_apply, PMF.uniform_apply] at h_pmf
    -- Reduce the tsum to a sum over the fiber.
    have h_sum : (∑' (a : α), if b = h a then ((Fintype.card α : ℝ≥0∞))⁻¹ else 0)
        = (Finset.univ.filter (fun a : α => h a = b)).card *
            ((Fintype.card α : ℝ≥0∞))⁻¹ := by
      rw [tsum_eq_sum (s := Finset.univ.filter (fun a => h a = b))
          (fun a ha => by simp at ha; simp [Ne.symm ha])]
      have hsum_eq : ∀ a ∈ (Finset.univ.filter (fun a : α => h a = b)),
          (if b = h a then ((Fintype.card α : ℝ≥0∞))⁻¹ else 0)
            = ((Fintype.card α : ℝ≥0∞))⁻¹ := by
        intro a ha; simp at ha; simp [ha]
      rw [Finset.sum_congr rfl hsum_eq, Finset.sum_const, nsmul_eq_mul]
    rw [h_sum] at h_pmf
    -- h_pmf : (filter.card : ℝ≥0∞) * |α|⁻¹ = |β|⁻¹.
    have hα_ne : (Fintype.card α : ℝ≥0∞) ≠ 0 := by exact_mod_cast h_card_α_pos.ne'
    have hα_ne_top : (Fintype.card α : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hβ_ne : (Fintype.card β : ℝ≥0∞) ≠ 0 := by exact_mod_cast h_card_β_pos.ne'
    have hβ_ne_top : (Fintype.card β : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    -- Multiply both sides by |α| to get filter.card = |α|/|β|, then by |β| to clear.
    have h_pmf2 :
        ((Finset.univ.filter (fun a : α => h a = b)).card : ℝ≥0∞) * Fintype.card β
          = Fintype.card α := by
      -- From h_pmf : k * |α|⁻¹ = |β|⁻¹.
      -- Multiply both sides by |α|: k = |α| * |β|⁻¹.
      have h_pmf' : ((Finset.univ.filter (fun a : α => h a = b)).card : ℝ≥0∞)
          = (Fintype.card β : ℝ≥0∞)⁻¹ * Fintype.card α := by
        have := congrArg (· * (Fintype.card α : ℝ≥0∞)) h_pmf
        simp only at this
        rw [mul_assoc, ENNReal.inv_mul_cancel hα_ne hα_ne_top, mul_one] at this
        exact this
      -- Multiply by |β|.
      rw [h_pmf']
      rw [mul_comm ((Fintype.card β : ℝ≥0∞)⁻¹), mul_assoc,
          ENNReal.inv_mul_cancel hβ_ne hβ_ne_top, mul_one]
    -- Cast back to ℕ.
    have h_pmf3 :
        (((Finset.univ.filter (fun a : α => h a = b)).card * Fintype.card β : ℕ) : ℝ≥0∞)
          = ((Fintype.card α : ℕ) : ℝ≥0∞) := by
      push_cast; exact h_pmf2
    exact_mod_cast h_pmf3
  -- Conclude |β| ∣ |α| and the per-fiber size k.
  have h_β_dvd_α : Fintype.card β ∣ Fintype.card α := by
    obtain ⟨b⟩ := (inferInstance : Nonempty β)
    exact ⟨_, (h_fib_h b).symm.trans (by ring)⟩
  set k : ℕ := Fintype.card α / Fintype.card β with hk_def
  have hk_card : Fintype.card α = Fintype.card β * k := by
    rw [hk_def, Nat.mul_div_cancel' h_β_dvd_α]
  have hk_fib : ∀ b : β,
      (Finset.univ.filter (fun a : α => h a = b)).card = k := by
    intro b
    have := h_fib_h b
    rw [hk_card] at this
    have h_eq : (Finset.univ.filter (fun a : α => h a = b)).card * Fintype.card β
        = k * Fintype.card β := by rw [this]; ring
    exact Nat.eq_of_mul_eq_mul_right h_card_β_pos h_eq
  have hk_pos : 0 < k := by
    by_contra hk0
    push_neg at hk0
    interval_cases k
    rw [Nat.mul_zero] at hk_card
    exact absurd hk_card h_card_α_pos.ne'
  -- Now the Pi map: each fiber over g : ι → β has size k^|ι|.
  have h_pow_pos : 0 < k ^ Fintype.card ι := pow_pos hk_pos _
  apply PMF.uniform_map_of_surjective_constFiber (fun (f : ι → α) i => h (f i))
      (k ^ Fintype.card ι) h_pow_pos
  intro g
  -- Fiber: {f : ι → α | (fun i => h (f i)) = g} = {f | ∀ i, h (f i) = g i}.
  -- This corresponds to Fintype.piFinset (fun i => univ.filter (h · = g i)).
  have h_fib_eq :
      Finset.univ.filter (fun f : ι → α => (fun i => h (f i)) = g)
        = Fintype.piFinset (fun i => Finset.univ.filter (fun a : α => h a = g i)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
               Fintype.mem_piFinset]
    constructor
    · intro hf i
      have := congrFun hf i
      simp [this]
    · intro hf
      funext i
      exact (hf i)
  rw [h_fib_eq, Fintype.card_piFinset]
  rw [Finset.prod_congr rfl (fun i _ => hk_fib (g i))]
  rw [Finset.prod_const, Finset.card_univ]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Uniform polynomial with fixed constant term -/

/-- A uniform random polynomial of degree ≤ d with constant term `s`,
realized by sampling the coefficients of `X, X², …, X^d` uniformly
from `F`. -/
noncomputable def uniformWithFixedZero (d : ℕ) (s : F) :
    PMF (_root_.Polynomial F) :=
  (PMF.uniform (Fin d → F)).map fun coefs =>
    Polynomial.C s + ∑ i : Fin d,
      Polynomial.C (coefs i) * Polynomial.X ^ (i.val + 1)

/-- A uniform random bivariate polynomial of bidegree ≤ (dx, dy)
with constant term `s`. Built as `Polynomial (Polynomial F)` —
the inner ring is `Polynomial F` and its constants are coefficients
in the outer `X` variable. -/
noncomputable def uniformBivariateWithFixedZero (dx dy : ℕ) (s : F) :
    PMF (_root_.Polynomial (_root_.Polynomial F)) :=
  (PMF.uniform (Fin dx → Fin dy → F)).map fun coefs =>
    Polynomial.C (Polynomial.C s) + ∑ i : Fin dx, ∑ j : Fin dy,
      Polynomial.C (Polynomial.C (coefs i j)) *
        Polynomial.X ^ (i.val + 1) *
        (Polynomial.C Polynomial.X) ^ (j.val + 1)

/-! ## Headline theorems (proofs deferred)

Both `evals_uniform` and `bivariate_evals_uniform` reduce to
Lagrange-interpolation bijections via `Lagrange.funEquivDegreeLT`
(in `Mathlib.LinearAlgebra.Lagrange`):

```
def funEquivDegreeLT (hvs : Set.InjOn v s) : degreeLT F #s ≃ₗ[F] s → F
```

This linear equivalence between polynomials of degree `< #s` and
functions on `s` is exactly the bijection we need. Restricting to
the affine subspace `{f : f(0) = s}` — i.e., adding `0` to the point
set — pushes the parametrization down by one dimension, leaving a
bijection between sample-space coefficients (`Fin d → F`) and
evaluations on the points (`pts → F`). Pushforward of uniform under
a linear bijection is uniform (`PMF.uniform_map_of_bijective`).

The full proof is M1 W3 polish work; the structural deliverables
(definitions and statements) are above. -/

/-! ## Injectivity of the evaluation map (equal-cardinality case)

For `pts.card = d` with `0 ∉ pts`, the map sending coefficients
`(c_0, …, c_{d-1})` to the evaluation tuple
`p ↦ s + ∑ i, c_i * p^(i+1)` is injective. Proof: if two coefficient
vectors agree on `pts`, then `Δ(X) := ∑ (c1 i - c2 i) * X^(i+1)` has
degree ≤ d and vanishes on `pts ∪ {0}` (size `d + 1`), hence is zero,
hence all its coefficients agree. -/

omit [Fintype F] in
theorem eval_map_injective (d : ℕ) (s : F)
    (pts : Finset F) (h_card : pts.card = d) (h_nz : (0 : F) ∉ pts) :
    Function.Injective fun (coefs : Fin d → F) =>
        fun (p : pts) =>
          (Polynomial.C s + ∑ i : Fin d,
            Polynomial.C (coefs i) * Polynomial.X ^ (i.val + 1)).eval p.val := by
  intro c1 c2 h_eq
  set Δ : Polynomial F :=
      ∑ i : Fin d, Polynomial.C (c1 i - c2 i) * Polynomial.X ^ (i.val + 1) with hΔ
  -- Δ vanishes at every p ∈ pts (subtract the eval-equality at p).
  have h_eval_pts : ∀ p ∈ pts, Δ.eval p = 0 := by
    intro p hp
    have hh := congrFun h_eq ⟨p, hp⟩
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_finset_sum,
               Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at hh
    have hh' : ∑ x, c1 x * p ^ (x.val + 1) = ∑ x, c2 x * p ^ (x.val + 1) :=
      add_left_cancel hh
    rw [hΔ, Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
               Polynomial.eval_X, sub_mul]
    rw [Finset.sum_sub_distrib, hh']
    ring
  -- Δ has zero constant term, so it vanishes at 0.
  have h_eval_0 : Δ.eval 0 = 0 := by
    rw [hΔ, Polynomial.eval_finset_sum]
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  -- Δ has degree ≤ d.
  have h_deg : Δ.degree ≤ (d : WithBot ℕ) := by
    rw [hΔ]
    apply le_trans (Polynomial.degree_sum_le _ _)
    rw [Finset.sup_le_iff]
    intro i _
    apply le_trans (Polynomial.degree_C_mul_X_pow_le _ _)
    exact_mod_cast Nat.succ_le_iff.mpr i.is_lt
  -- pts ∪ {0} has size d + 1, so Δ.degree < (d+1) = card (pts ∪ {0}).
  set pts0 : Finset F := insert (0 : F) pts with hpts0
  have h_pts0_card : pts0.card = d + 1 := by
    rw [hpts0, Finset.card_insert_of_notMem h_nz, h_card]
  have h_eval_pts0 : ∀ x ∈ pts0, Δ.eval x = 0 := by
    intro x hx
    rw [hpts0, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact h_eval_0
    · exact h_eval_pts x hx
  have h_deg_lt : Δ.degree < (pts0.card : WithBot ℕ) := by
    rw [h_pts0_card]
    calc Δ.degree ≤ (d : WithBot ℕ) := h_deg
      _ < ((d + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self d
  have hΔ_zero : Δ = 0 :=
    Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero pts0 h_deg_lt h_eval_pts0
  -- Read off coefficients: each coefficient of Δ at degree (i+1) equals c1 i - c2 i.
  funext i
  have h_coef : Δ.coeff (i.val + 1) = 0 := by rw [hΔ_zero]; simp
  rw [hΔ, Polynomial.finset_sum_coeff] at h_coef
  have h_unique : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      (Polynomial.C (c1 j - c2 j) * Polynomial.X ^ (j.val + 1)).coeff (i.val + 1)
        = if j = i then c1 i - c2 i else 0 := by
    intro j _
    rw [Polynomial.coeff_C_mul_X_pow]
    by_cases h : j = i
    · subst h; simp
    · simp only [if_neg h]
      have hne : i.val + 1 ≠ j.val + 1 := by
        intro heq; apply h; apply Fin.ext; omega
      rw [if_neg hne]
  rw [Finset.sum_congr rfl h_unique, Finset.sum_ite_eq' Finset.univ i] at h_coef
  simp at h_coef
  exact sub_eq_zero.mp h_coef

/-! ## Equal-cardinality case of `evals_uniform`

When `pts.card = d`, the eval map is a bijection between
`Fin d → F` and `pts → F` (both of size `(card F)^d`). Apply
`PMF.uniform_map_of_bijective`. -/

theorem evals_uniform_eq_card (d : ℕ) (s : F)
    (pts : Finset F) (h_card : pts.card = d) (h_nz : (0 : F) ∉ pts) :
    (uniformWithFixedZero d s).map
        (fun f => fun (p : pts) => f.eval p.val)
      = PMF.uniform (pts → F) := by
  unfold uniformWithFixedZero
  rw [PMF.map_comp]
  -- Card equality: (card F)^d = (card F)^pts.card.
  have h_card_eq : Fintype.card (Fin d → F) = Fintype.card (pts → F) := by
    rw [Fintype.card_fun, Fintype.card_fun]
    simp [Fintype.card_coe, h_card]
  -- Injectivity from eval_map_injective.
  have h_inj : Function.Injective fun (coefs : Fin d → F) =>
      fun (p : pts) =>
        Polynomial.eval p.val (Polynomial.C s + ∑ i : Fin d,
          Polynomial.C (coefs i) * Polynomial.X ^ (i.val + 1)) :=
    eval_map_injective d s pts h_card h_nz
  -- Bijectivity from inj + card equality.
  have h_bij : Function.Bijective fun (coefs : Fin d → F) =>
      fun (p : pts) =>
        Polynomial.eval p.val (Polynomial.C s + ∑ i : Fin d,
          Polynomial.C (coefs i) * Polynomial.X ^ (i.val + 1)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨h_inj, h_card_eq⟩
  exact PMF.uniform_map_of_bijective h_bij

/-- Joint of evaluations at `pts` is uniform on `pts → F` whenever
`|pts| ≤ d`, `0 ∉ pts`, and the field is large enough
(`d + 1 ≤ Fintype.card F`). The latter is needed so that we can
extend `pts` to size `d` within `F \ {0}` for the marginalization
argument when `pts.card < d`.

For `pts.card = d`, the eval map is a bijection (via injectivity
+ cardinality, see `evals_uniform_eq_card`).

For `pts.card < d`, extend `pts` to a `pts'` of size `d` in
`F \ ({0} ∪ pts)`, apply the equal-card case to `pts'`, then project
the uniform on `pts' → F` down to `pts → F` via restriction (which
is a constant-fiber surjection of fiber size
`(Fintype.card F) ^ (d - pts.card)`).

For `d = 0` (so also `pts.card = 0`): both sides are `pure (·)` on
the empty function — handled directly. -/
theorem evals_uniform (d : ℕ) (s : F)
    (pts : Finset F) (h_card : pts.card ≤ d) (h_nz : (0 : F) ∉ pts)
    (h_F : d + 1 ≤ Fintype.card F) :
    (uniformWithFixedZero d s).map
        (fun f => fun (p : pts) => f.eval p.val)
      = PMF.uniform (pts → F) := by
  -- Extend pts to pts' of size d within F \ ({0} ∪ pts).
  -- The set F \ ({0} ∪ pts) has at least `d - pts.card` elements
  -- (using `d + 1 ≤ Fintype.card F`).
  have h_avail : d - pts.card ≤ (Finset.univ \ (insert (0 : F) pts)).card := by
    have h_eq : (Finset.univ \ (insert (0 : F) pts)).card =
        Fintype.card F - (pts.card + 1) := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
          Finset.card_univ, Finset.card_insert_of_notMem h_nz]
    rw [h_eq]; omega
  obtain ⟨extras, h_extras_sub, h_extras_card⟩ :=
    Finset.exists_subset_card_eq h_avail
  -- extras is disjoint from {0} ∪ pts.
  have h_extras_disj_excluded : Disjoint extras (insert (0 : F) pts) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb heq
    have ha' : a ∈ Finset.univ \ (insert (0 : F) pts) := h_extras_sub ha
    rw [Finset.mem_sdiff] at ha'
    apply ha'.2
    rw [heq]; exact hb
  have h_extras_disj_pts : Disjoint extras pts :=
    Disjoint.mono_right (Finset.subset_insert _ _) h_extras_disj_excluded
  have h_extras_no_zero : (0 : F) ∉ extras := by
    intro h0
    have : (0 : F) ∈ Finset.univ \ (insert (0 : F) pts) := h_extras_sub h0
    rw [Finset.mem_sdiff, Finset.mem_insert] at this
    exact this.2 (Or.inl rfl)
  set pts' : Finset F := pts ∪ extras with hpts'_def
  -- Properties of pts'.
  have hpts'_card : pts'.card = d := by
    rw [hpts'_def, Finset.card_union_of_disjoint h_extras_disj_pts.symm,
        h_extras_card]
    omega
  have hpts'_nz : (0 : F) ∉ pts' := by
    rw [hpts'_def, Finset.mem_union]
    rintro (h | h)
    · exact h_nz h
    · exact h_extras_no_zero h
  have h_pts_sub_pts' : pts ⊆ pts' := by
    rw [hpts'_def]; exact Finset.subset_union_left
  -- Restriction map (pts' → F) → (pts → F) given by composition with inclusion.
  let restr : (pts' → F) → (pts → F) := fun g p => g ⟨p.val, h_pts_sub_pts' p.property⟩
  -- Factor: eval at pts = restr ∘ (eval at pts').
  have h_factor :
      (fun (f : Polynomial F) (p : pts) => f.eval p.val) =
        restr ∘ (fun (f : Polynomial F) (p' : pts') => f.eval p'.val) := by
    funext f p
    rfl
  rw [h_factor, ← PMF.map_comp]
  -- Apply equal-card case to pts'.
  rw [evals_uniform_eq_card d s pts' hpts'_card hpts'_nz]
  -- Now need: (PMF.uniform (pts' → F)).map restr = PMF.uniform (pts → F).
  -- Apply uniform_map_of_surjective_constFiber.
  -- Fiber of restr at any r : pts → F has size (Fintype.card F)^(extras.card)
  -- (extensions of r to extras).
  have h_card_F_pos : 0 < Fintype.card F := by linarith
  have h_extras_pow_pos : 0 < (Fintype.card F) ^ extras.card := pow_pos h_card_F_pos _
  haveI : Nonempty (pts' → F) := by
    have hF : Nonempty F := ⟨0⟩
    exact ⟨fun _ => 0⟩
  haveI : Nonempty (pts → F) := ⟨fun _ => 0⟩
  -- The fiber computation: fix r : pts → F, count g : pts' → F with restr g = r.
  -- Such g is determined by r and (g restricted to extras), giving (card F)^extras.card.
  apply PMF.uniform_map_of_surjective_constFiber restr
      ((Fintype.card F) ^ extras.card) h_extras_pow_pos
  intro r
  -- We need: |{g : pts' → F | restr g = r}| = (card F)^extras.card.
  -- Build a bijection between this fiber and (extras → F).
  -- Define the equivalence: g ↦ (extras ↦ g (i with hi : i ∈ pts')).
  -- For p ∈ pts', either p ∈ pts (and g p = r ⟨p, _⟩) or p ∈ extras.
  -- The free degrees of freedom are exactly g restricted to extras.
  classical
  -- Counting: cardinality of fiber = (Fintype.card F)^extras.card.
  -- Use Finset.card_eq via an explicit bijection with extras → F.
  have h_fib_card :
      (Finset.univ.filter (fun (g : pts' → F) => restr g = r)).card =
        (Fintype.card F) ^ extras.card := by
    -- Use an explicit equivalence between fiber and (extras → F).
    have h_pow : (Fintype.card F) ^ extras.card = Fintype.card (extras → F) := by
      rw [Fintype.card_fun, Fintype.card_coe]
    -- Reduce the goal to Fintype.card on the subtype.
    have h_filter_card_eq :
        (Finset.univ.filter (fun (g : pts' → F) => restr g = r)).card =
        Fintype.card { g : pts' → F // restr g = r } := by
      rw [Fintype.card_subtype]
    rw [h_filter_card_eq, h_pow]
    -- Now: card { g // restr g = r } = card (extras → F).
    -- Build a bijection φ.
    let φ : { g : pts' → F // restr g = r } → (extras → F) :=
      fun ⟨g, _⟩ e =>
        g ⟨e.val, by rw [hpts'_def]; exact Finset.mem_union_right _ e.property⟩
    have hφ_bij : Function.Bijective φ := by
      refine ⟨?_, ?_⟩
      · intro ⟨g1, hg1⟩ ⟨g2, hg2⟩ h_eq_φ
        simp only [Subtype.mk_eq_mk]
        funext ⟨p, hp⟩
        rw [hpts'_def, Finset.mem_union] at hp
        rcases hp with hp | hp
        · -- p ∈ pts.
          have hg1_at :
              g1 ⟨p, by rw [hpts'_def]; exact Finset.mem_union_left _ hp⟩ =
              r ⟨p, hp⟩ := by
            have := congrFun hg1 ⟨p, hp⟩
            simpa [restr] using this
          have hg2_at :
              g2 ⟨p, by rw [hpts'_def]; exact Finset.mem_union_left _ hp⟩ =
              r ⟨p, hp⟩ := by
            have := congrFun hg2 ⟨p, hp⟩
            simpa [restr] using this
          rw [hg1_at, hg2_at]
        · -- p ∈ extras.
          exact congrFun h_eq_φ ⟨p, hp⟩
      · intro t
        let g : pts' → F := fun ⟨p, hp⟩ =>
          if h : p ∈ pts then r ⟨p, h⟩
            else t ⟨p, by
              have : p ∈ pts ∪ extras := by rw [← hpts'_def]; exact hp
              rw [Finset.mem_union] at this
              exact this.resolve_left h⟩
        refine ⟨⟨g, ?_⟩, ?_⟩
        · funext ⟨p, hp⟩
          show g ⟨p, h_pts_sub_pts' hp⟩ = r ⟨p, hp⟩
          simp only [g, hp, dif_pos]
        · funext ⟨e, he⟩
          have h_e_not_pts : e ∉ pts := fun h_e_pts =>
            (Finset.disjoint_iff_ne.mp h_extras_disj_pts) e he e h_e_pts rfl
          show g ⟨e, by rw [hpts'_def]; exact Finset.mem_union_right _ he⟩ = t ⟨e, he⟩
          simp only [g, h_e_not_pts, dif_neg, not_false_eq_true]
    exact Fintype.card_of_bijective hφ_bij
  exact h_fib_card

/-- Bivariate evaluation uniformity. Proof reduces to univariate
`evals_uniform` applied in each direction via the row-then-column
factoring `f(p,q) = s + ∑_i (∑_j coefs(i,j) * q^(j+1)) * p^(i+1)`. -/
theorem bivariate_evals_uniform (dx dy : ℕ) (s : F)
    (pts_x : Finset F) (pts_y : Finset F)
    (h_cx : pts_x.card ≤ dx) (h_cy : pts_y.card ≤ dy)
    (h_nx : (0 : F) ∉ pts_x) (h_ny : (0 : F) ∉ pts_y)
    (h_Fx : dx + 1 ≤ Fintype.card F) (h_Fy : dy + 1 ≤ Fintype.card F) :
    (uniformBivariateWithFixedZero dx dy s).map
        (fun f => fun (p : pts_x) (q : pts_y) =>
          (f.eval (Polynomial.C p.val)).eval q.val)
      = PMF.uniform (pts_x → pts_y → F) := by
  -- Edge cases first: if either pts_x or pts_y is empty, the codomain
  -- `pts_x → pts_y → F` is a subsingleton, and any two PMFs on a
  -- subsingleton type are equal.
  by_cases h_xy_subsing : pts_x.card = 0 ∨ pts_y.card = 0
  · -- Subsingleton case.
    have h_subsing : Subsingleton (pts_x → pts_y → F) := by
      rcases h_xy_subsing with hx | hy
      · haveI : IsEmpty pts_x := by
          rw [Finset.card_eq_zero] at hx
          subst hx
          exact ⟨fun ⟨_, h⟩ => Finset.notMem_empty _ h⟩
        infer_instance
      · haveI : IsEmpty pts_y := by
          rw [Finset.card_eq_zero] at hy
          subst hy
          exact ⟨fun ⟨_, h⟩ => Finset.notMem_empty _ h⟩
        haveI : Subsingleton (pts_y → F) := inferInstance
        infer_instance
    apply PMF.ext
    intro g
    have h_default : ∀ a, a = g := fun a => Subsingleton.elim a g
    have hμ := PMF.tsum_coe ((uniformBivariateWithFixedZero dx dy s).map
        (fun f => fun (p : pts_x) (q : pts_y) =>
          (f.eval (Polynomial.C p.val)).eval q.val))
    have hν := PMF.tsum_coe (PMF.uniform (pts_x → pts_y → F))
    rw [tsum_eq_single g (fun b hb => absurd (h_default b) hb)] at hμ
    rw [tsum_eq_single g (fun b hb => absurd (h_default b) hb)] at hν
    rw [hμ, hν]
  -- Non-degenerate case: both pts are nonempty.
  push_neg at h_xy_subsing
  obtain ⟨h_px_pos, h_py_pos⟩ := h_xy_subsing
  have h_dx_pos : 0 < dx := lt_of_lt_of_le (Nat.pos_of_ne_zero h_px_pos) h_cx
  have h_dy_pos : 0 < dy := lt_of_lt_of_le (Nat.pos_of_ne_zero h_py_pos) h_cy
  haveI : Nonempty (Fin dx) := ⟨⟨0, h_dx_pos⟩⟩
  haveI : Nonempty (Fin dy) := ⟨⟨0, h_dy_pos⟩⟩
  haveI h_pts_x_ne : Nonempty pts_x := by
    have h := Finset.card_pos.mp (Nat.pos_of_ne_zero h_px_pos)
    exact ⟨⟨h.choose, h.choose_spec⟩⟩
  haveI h_pts_y_ne : Nonempty pts_y := by
    have h := Finset.card_pos.mp (Nat.pos_of_ne_zero h_py_pos)
    exact ⟨⟨h.choose, h.choose_spec⟩⟩
  -- Define per-row Y-eval and per-q X-eval.
  set step1 : (Fin dx → Fin dy → F) → (Fin dx → pts_y → F) :=
    fun coefs i q => ∑ j : Fin dy, coefs i j * (q.val : F) ^ (j.val + 1) with hstep1
  set step2 : (Fin dx → pts_y → F) → (pts_x → pts_y → F) :=
    fun b p q => s + ∑ i : Fin dx, b i q * (p.val : F) ^ (i.val + 1) with hstep2
  -- Algebraic identity: bivariate eval = step2 ∘ step1.
  have h_factor : ∀ (coefs : Fin dx → Fin dy → F) (p : pts_x) (q : pts_y),
        Polynomial.eval (q.val : F)
          (Polynomial.eval (Polynomial.C (p.val : F))
            (Polynomial.C (Polynomial.C s) +
              ∑ i : Fin dx, ∑ j : Fin dy,
                Polynomial.C (Polynomial.C (coefs i j)) *
                  Polynomial.X ^ (i.val + 1) *
                  (Polynomial.C Polynomial.X) ^ (j.val + 1)))
      = step2 (step1 coefs) p q := by
    intro coefs p q
    simp only [hstep1, hstep2]
    -- Both inner and outer eval simplifications (one simp call handles both).
    simp only [Polynomial.eval_add, Polynomial.eval_C,
               Polynomial.eval_finset_sum, Polynomial.eval_mul,
               Polynomial.eval_pow, Polynomial.eval_X]
    -- Algebraic massaging: ∑ i ∑ j, coefs i j * p^(i+1) * q^(j+1) = ∑ i, (∑ j, coefs i j * q^(j+1)) * p^(i+1).
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- Push h_factor as a function-equality.
  have h_factor_fun :
      (fun (coefs : Fin dx → Fin dy → F) (p : pts_x) (q : pts_y) =>
        Polynomial.eval (q.val : F)
          (Polynomial.eval (Polynomial.C (p.val : F))
            (Polynomial.C (Polynomial.C s) +
              ∑ i : Fin dx, ∑ j : Fin dy,
                Polynomial.C (Polynomial.C (coefs i j)) *
                  Polynomial.X ^ (i.val + 1) *
                  (Polynomial.C Polynomial.X) ^ (j.val + 1))))
        = step2 ∘ step1 := by
    funext coefs p q; exact h_factor coefs p q
  -- Step 1: per-row Y-eval pushes uniform to uniform.
  have h_step1 :
      (PMF.uniform (Fin dx → Fin dy → F)).map step1
        = PMF.uniform (Fin dx → pts_y → F) := by
    -- The per-row map: row ↦ (q ↦ ∑ j, row j * q.val^(j+1)).
    -- This equals evals_uniform dy 0 pts_y h_cy h_ny h_Fy after simplification.
    have h_y_uni : (PMF.uniform (Fin dy → F)).map
        (fun (row : Fin dy → F) (q : pts_y) =>
          ∑ j : Fin dy, row j * (q.val : F) ^ (j.val + 1))
        = PMF.uniform (pts_y → F) := by
      have h_evals := evals_uniform dy (0 : F) pts_y h_cy h_ny h_Fy
      unfold uniformWithFixedZero at h_evals
      rw [PMF.map_comp] at h_evals
      have h_eq : (fun (row : Fin dy → F) (q : pts_y) =>
            ∑ j : Fin dy, row j * (q.val : F) ^ (j.val + 1))
          = (fun f (p : pts_y) => Polynomial.eval p.val f) ∘
              (fun coefs : Fin dy → F =>
                Polynomial.C (0 : F) + ∑ i : Fin dy,
                  Polynomial.C (coefs i) * Polynomial.X ^ (i.val + 1)) := by
        funext row q
        simp only [Function.comp, Polynomial.eval_add, Polynomial.eval_C,
                   Polynomial.eval_finset_sum, Polynomial.eval_mul,
                   Polynomial.eval_pow, Polynomial.eval_X, zero_add]
      rw [h_eq]; exact h_evals
    -- Now lift via Pi-uniform helper.
    have h_pi := PMF.uniform_pi_map_of_uniform_map (ι := Fin dx) h_y_uni
    -- Rewrite step1 = fun coefs i => h (coefs i) where h is the per-row map.
    have h_step1_eq : step1 = fun (coefs : Fin dx → Fin dy → F) (i : Fin dx) =>
        (fun (row : Fin dy → F) (q : pts_y) =>
          ∑ j : Fin dy, row j * (q.val : F) ^ (j.val + 1)) (coefs i) := by
      funext coefs i q; rfl
    rw [h_step1_eq]; exact h_pi
  -- Step 2: pushforward via per-q X-eval. Decompose step2 via swaps.
  have h_step2 :
      (PMF.uniform (Fin dx → pts_y → F)).map step2
        = PMF.uniform (pts_x → pts_y → F) := by
    -- Decompose step2 = swap2 ∘ pi_x ∘ swap1.
    set swap1 : (Fin dx → pts_y → F) → (pts_y → Fin dx → F) :=
      fun b q i => b i q with hswap1
    set pi_x : (pts_y → Fin dx → F) → (pts_y → pts_x → F) :=
      fun M q p => s + ∑ i : Fin dx, M q i * (p.val : F) ^ (i.val + 1) with hpi_x
    set swap2 : (pts_y → pts_x → F) → (pts_x → pts_y → F) :=
      fun M p q => M q p with hswap2
    have h_decomp : step2 = swap2 ∘ pi_x ∘ swap1 := by
      funext b p q
      simp only [hstep2, Function.comp, hswap1, hpi_x, hswap2]
    rw [h_decomp]
    -- swap1 is bijective.
    have h_swap1_bij : Function.Bijective swap1 := by
      refine ⟨?_, ?_⟩
      · intro b1 b2 h_eq
        funext i q
        exact congrFun (congrFun h_eq q) i
      · intro M
        exact ⟨fun i q => M q i, rfl⟩
    have h_swap1 : (PMF.uniform (Fin dx → pts_y → F)).map swap1
        = PMF.uniform (pts_y → Fin dx → F) :=
      PMF.uniform_map_of_bijective h_swap1_bij
    -- swap2 is bijective.
    have h_swap2_bij : Function.Bijective swap2 := by
      refine ⟨?_, ?_⟩
      · intro M1 M2 h_eq
        funext q p
        exact congrFun (congrFun h_eq p) q
      · intro N
        exact ⟨fun q p => N p q, rfl⟩
    have h_swap2 : (PMF.uniform (pts_y → pts_x → F)).map swap2
        = PMF.uniform (pts_x → pts_y → F) :=
      PMF.uniform_map_of_bijective h_swap2_bij
    -- Per-q X-eval via Pi-uniform helper.
    have h_x_uni : (PMF.uniform (Fin dx → F)).map
        (fun (col : Fin dx → F) (p : pts_x) =>
          s + ∑ i : Fin dx, col i * (p.val : F) ^ (i.val + 1))
        = PMF.uniform (pts_x → F) := by
      have h_evals := evals_uniform dx s pts_x h_cx h_nx h_Fx
      unfold uniformWithFixedZero at h_evals
      rw [PMF.map_comp] at h_evals
      have h_eq : (fun (col : Fin dx → F) (p : pts_x) =>
            s + ∑ i : Fin dx, col i * (p.val : F) ^ (i.val + 1))
          = (fun f (p : pts_x) => Polynomial.eval p.val f) ∘
              (fun coefs : Fin dx → F =>
                Polynomial.C s + ∑ i : Fin dx,
                  Polynomial.C (coefs i) * Polynomial.X ^ (i.val + 1)) := by
        funext col p
        simp only [Function.comp, Polynomial.eval_add, Polynomial.eval_C,
                   Polynomial.eval_finset_sum, Polynomial.eval_mul,
                   Polynomial.eval_pow, Polynomial.eval_X]
      rw [h_eq]; exact h_evals
    have h_pi_x : (PMF.uniform (pts_y → Fin dx → F)).map pi_x
        = PMF.uniform (pts_y → pts_x → F) := by
      have h_pi := PMF.uniform_pi_map_of_uniform_map (ι := pts_y) h_x_uni
      have h_pi_x_eq : pi_x = fun (M : pts_y → Fin dx → F) (q : pts_y) =>
          (fun (col : Fin dx → F) (p : pts_x) =>
            s + ∑ i : Fin dx, col i * (p.val : F) ^ (i.val + 1)) (M q) := by
        funext M q p; rfl
      rw [h_pi_x_eq]; exact h_pi
    -- Compose: ((uniform).map swap1).map pi_x.map swap2.
    rw [show (swap2 ∘ pi_x ∘ swap1) = swap2 ∘ (pi_x ∘ swap1) from rfl]
    rw [← PMF.map_comp]
    rw [← PMF.map_comp]
    rw [h_swap1, h_pi_x, h_swap2]
  -- Compose step1 and step2.
  unfold uniformBivariateWithFixedZero
  rw [PMF.map_comp]
  -- The composed map equals step2 ∘ step1.
  rw [show ((fun f (p : pts_x) (q : pts_y) =>
              Polynomial.eval (q.val : F) (Polynomial.eval (Polynomial.C (p.val : F)) f))
            ∘ (fun coefs : Fin dx → Fin dy → F =>
                Polynomial.C (Polynomial.C s) + ∑ i : Fin dx, ∑ j : Fin dy,
                  Polynomial.C (Polynomial.C (coefs i j)) *
                    Polynomial.X ^ (i.val + 1) *
                    (Polynomial.C Polynomial.X) ^ (j.val + 1)))
          = step2 ∘ step1 from h_factor_fun]
  rw [← PMF.map_comp, h_step1, h_step2]

end Leslie.Prob.Polynomial
