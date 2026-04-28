/-
M1 W3 — Polynomial uniformity library (foundations).

`uniformWithFixedZero d s` is the uniform distribution over polynomials
of degree ≤ d with constant term `s`. The headline theorem
`evals_uniform` says: for `pts ⊂ F` with `|pts| ≤ d` and `0 ∉ pts`,
the joint distribution of evaluations `(f(p))_{p∈pts}` is uniform on
`pts → F`. This is the algebraic core of Shamir secrecy (M1 W4).

The proof of `evals_uniform` reduces (via `Lagrange.funEquivDegreeLT`)
to a Vandermonde linear-algebra fact: distinct nonzero points give a
nonsingular Vandermonde matrix, so polynomial coefficients ↔
evaluations is a linear bijection.

Status (M1 W3 first pass):
  * Helper `PMF.uniform_map_of_bijective` proved (pushforward of
    uniform under a bijection is uniform).
  * `uniformWithFixedZero`, `uniformBivariateWithFixedZero` defined.
  * `evals_uniform`, `bivariate_evals_uniform` stated; proofs are
    `sorry` with reduction sketches in the doc-comments. The
    Lagrange-via-`funEquivDegreeLT` proof is M1 W3 polish work
    (likely 100–150 more lines once the right lemma chain is found).

Per implementation plan v2.2 §M1 W3.
-/

import Leslie.Prob.PMF
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Lagrange

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

/-- Joint of evaluations at `pts` is uniform on `pts → F` whenever
`|pts| ≤ d` and `0 ∉ pts`. -/
theorem evals_uniform (d : ℕ) (s : F)
    (pts : Finset F) (h_card : pts.card ≤ d) (h_nz : (0 : F) ∉ pts) :
    (uniformWithFixedZero d s).map
        (fun f => fun (p : pts) => f.eval p.val)
      = PMF.uniform (pts → F) := by
  sorry

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
