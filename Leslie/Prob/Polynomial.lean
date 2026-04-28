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
`evals_uniform` applied row-wise. Deferred to M2 per plan v2.2. -/
theorem bivariate_evals_uniform (dx dy : ℕ) (s : F)
    (pts_x : Finset F) (pts_y : Finset F)
    (h_cx : pts_x.card ≤ dx) (h_cy : pts_y.card ≤ dy)
    (h_nx : (0 : F) ∉ pts_x) (h_ny : (0 : F) ∉ pts_y) :
    (uniformBivariateWithFixedZero dx dy s).map
        (fun f => fun (p : pts_x) (q : pts_y) =>
          (f.eval (Polynomial.C p.val)).eval q.val)
      = PMF.uniform (pts_x → pts_y → F) := by
  sorry

end Leslie.Prob.Polynomial
