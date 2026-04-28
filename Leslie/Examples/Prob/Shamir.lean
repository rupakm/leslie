/-
M1 W4 — Shamir secret sharing: secrecy proof.

Defines the Shamir-share spec as a `ProbActionSpec` and proves the
secrecy theorem: for any coalition of size ≤ t, the distribution
of shares is the same regardless of the secret. Mathematical core
is two applications of `Polynomial.evals_uniform` plus transitivity:

```
(uniformWithFixedZero t s).map share_view
  = uniform                                     by evals_uniform
  = (uniformWithFixedZero t s').map share_view  by evals_uniform.symm
```

The proof is two rewrite steps once the eval-points are set up.
Modulo the deferred `evals_uniform` body (M1 W3 sorry; planned),
Shamir secrecy is *fully proved* — no extra sorries here.

Per implementation plan v2.2 §M1 W4. Coalition-with-`Coalition`-
shape and `Embed.lean` Level-2 conservativity are deferred to a
separate pass once `traceDist` measure-level infrastructure lands
(M2 W1 per plan).
-/

import Leslie.Prob.Action
import Leslie.Prob.PMF
import Leslie.Prob.Polynomial

namespace Leslie.Examples.Prob.Shamir

open Leslie.Prob

/-! ## Algebraic core

The mathematical content of secrecy: the joint distribution of
evaluations at a coalition's points is the *same uniform* regardless
of the secret. -/

/-- Algebraic core of Shamir secrecy: for any coalition `pts ⊂ F`
with `|pts| ≤ t` and `0 ∉ pts`, the distribution of evaluations is
independent of the secret `s`.

Both sides reduce to `PMF.uniform (pts → F)` via `evals_uniform`. -/
theorem shamir_secrecy_pts {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (t : ℕ) (s s' : F)
    (pts : Finset F) (h_card : pts.card ≤ t) (h_nz : (0 : F) ∉ pts) :
    (Leslie.Prob.Polynomial.uniformWithFixedZero t s).map
        (fun f => fun (p : pts) => f.eval p.val)
      =
    (Leslie.Prob.Polynomial.uniformWithFixedZero t s').map
        (fun f => fun (p : pts) => f.eval p.val) := by
  rw [Leslie.Prob.Polynomial.evals_uniform t s pts h_card h_nz,
      Leslie.Prob.Polynomial.evals_uniform t s' pts h_card h_nz]

/-! ## Shamir spec as a `ProbActionSpec`

State: per-party shares (and an "is-shared" flag tracking whether
the deal has happened).

Action: `deal s` — sample a uniform degree-`t` polynomial with
`f(0) = s`, set every party's share to `f(partyPoint i)`.

`partyPoint : Fin n → F` is an injection avoiding 0 — for
`F = ZMod p` with `p > n`, the canonical embedding `i ↦ i + 1`
works. We parameterize over the injection so the spec is
field-agnostic. -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ}

/-- Shamir per-party state: each of the `n` parties has either
received its share (`some s_i`) or not (`none`). -/
structure ShamirState (F : Type*) (n : ℕ) where
  shares : Fin n → Option F

/-- The dealer's only action: deal secret `s` using a degree-`t`
polynomial with constant term `s`. The action label is the secret
itself (so the scheduler determines the secret along with the
action). -/
inductive ShamirAction (F : Type*) where
  | deal (s : F)

/-- The Shamir-share spec.

  * Initial state: every party's share is `none`.
  * Action `.deal s`: gate is "no share dealt yet"; effect samples
    a uniform polynomial with constant term `s` and writes
    `some (f(partyPoint i))` to every party. -/
noncomputable def shamirShare (t : ℕ) (partyPoint : Fin n → F) :
    ProbActionSpec (ShamirState F n) (ShamirAction F) where
  init    := fun st => ∀ i, st.shares i = none
  actions := fun
    | .deal s =>
      { gate   := fun st => ∀ i, st.shares i = none
        effect := fun _ _ =>
          (Leslie.Prob.Polynomial.uniformWithFixedZero t s).map fun f =>
            { shares := fun i => some (f.eval (partyPoint i)) } }

/-! ## Coalition view -/

/-- A `t`-coalition: a subset of parties of size ≤ t. -/
def Coalition (n t : ℕ) := { S : Finset (Fin n) // S.card ≤ t }

/-- The view of a coalition: the (some-)shares of its members. The
`Option`-stripping is justified because in any reachable state the
shares are either all-`none` or all-`some`. -/
noncomputable def coalitionView (C : Coalition n t) (st : ShamirState F n) :
    C.val → Option F :=
  fun i => st.shares i.val

/-! ## Secrecy theorem at the coalition level

The coalition view's distribution after dealing is independent of
the secret. Reduces to `shamir_secrecy_pts` after translating
coalition indices into field elements via `partyPoint`.

Concretely, the post-deal coalition view distribution is
`(uniformWithFixedZero t s).map (fun f => fun i : C.val => some (f.eval (partyPoint i.val)))`.

The `some` wrapper and the `partyPoint` translation are bijective
in the coordinate sense, so secrecy at the polynomial-evaluation
level lifts directly to secrecy at the share level. -/

/-- Secrecy at the post-deal coalition-share level.

Given a coalition `C` of size ≤ t and an injective `partyPoint`
avoiding 0, the distribution of `C`'s shares after dealing depends
only on the coalition (not on the secret). Reduces to
`shamir_secrecy_pts` by transporting along `partyPoint` and
stripping the `Option.some` wrapper. -/
theorem shamir_secrecy {t : ℕ}
    (partyPoint : Fin n → F)
    (_h_inj : Function.Injective partyPoint)  -- documentation; not used
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (C : Coalition n t) (s s' : F) :
    (Leslie.Prob.Polynomial.uniformWithFixedZero t s).map
        (fun f => fun (i : C.val) => some (f.eval (partyPoint i.val)))
      =
    (Leslie.Prob.Polynomial.uniformWithFixedZero t s').map
        (fun f => fun (i : C.val) => some (f.eval (partyPoint i.val))) := by
  -- The coalition's evaluation points, as a Finset F.
  set pts : Finset F := C.val.image partyPoint with hpts
  have h_card : pts.card ≤ t :=
    le_trans Finset.card_image_le C.property
  have h_nz : (0 : F) ∉ pts := by
    intro h_in
    rw [hpts, Finset.mem_image] at h_in
    obtain ⟨i, _, h_eq⟩ := h_in
    exact h_nz_pp i h_eq
  -- Membership witness: every `partyPoint i.val` for `i : C.val` is in `pts`.
  have h_mem : ∀ (i : C.val), partyPoint i.val ∈ pts := fun i => by
    simp only [pts, Finset.mem_image]
    exact ⟨i.val, i.property, rfl⟩
  -- Both LHS and RHS factor as `(... .map evals_at_pts).map view_translate`,
  -- where `view_translate g i = some (g ⟨partyPoint i.val, h_mem i⟩)`.
  have h_factor : ∀ (s_sec : F),
      (Leslie.Prob.Polynomial.uniformWithFixedZero t s_sec).map
          (fun f => fun (i : C.val) => some (f.eval (partyPoint i.val)))
        =
      ((Leslie.Prob.Polynomial.uniformWithFixedZero t s_sec).map
          (fun f => fun (p : pts) => f.eval p.val)).map
          (fun g i => some (g ⟨partyPoint i.val, h_mem i⟩)) := by
    intro s_sec
    rw [PMF.map_comp]
    rfl
  rw [h_factor s, h_factor s']
  -- Inner equality is exactly `shamir_secrecy_pts`.
  rw [shamir_secrecy_pts t s s' pts h_card h_nz]

end Leslie.Examples.Prob.Shamir
