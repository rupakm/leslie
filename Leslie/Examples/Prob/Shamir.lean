/-
M1 W4 — Shamir secret sharing: secrecy proof.

Defines the Shamir-share spec as a `ProbActionSpec` and proves
secrecy at three levels of abstraction:

  * `shamir_secrecy_pts` — algebraic core: for any
    `pts ⊂ F` with `|pts| ≤ t` and `0 ∉ pts`, the distribution
    of polynomial evaluations at `pts` is independent of the
    secret. Two applications of `Polynomial.evals_uniform`.
  * `shamir_secrecy` — coalition-level lift: for any coalition
    `C : Coalition n t`, the post-deal coalition view (as a
    polynomial-eval pushforward) is independent of the secret.
  * `shamir_secrecy_via_step` — operational/state-level: the
    `step`-of-`shamirShare` post-deal coalition view distribution
    is independent of the secret. This is the corollary that
    actually uses the spec, the step semantics, and `coalitionView`
    together.

Modulo the deferred `evals_uniform` body (M1 W3 sorry), Shamir
secrecy is fully proved at all three levels — zero sorries in this
file.

## Model assumptions

  * **Synchronous broadcast deal.** The `.deal` action atomically
    writes shares to all parties. Real Shamir distributes shares
    over a network; modeling per-party delivery is M2/M3 work.
  * **Single-shot dealer.** Once the deal has occurred, `gate`
    becomes `False` and no further `.deal` actions fire. No
    re-deal, no proactive refresh, no multiple dealers.
  * **Scheduler-supplied secret.** `ShamirAction := .deal (s : F)`
    parameterizes the action by the secret, so the scheduler picks
    both "fire deal" and "with this secret". An alternative model
    keeps the secret in the dealer's local state, separating
    setup from the protocol step. Either is fine for secrecy
    (we quantify ∀ s, s'); for richer fault models the latter is
    preferable.
  * **`partyPoint` is a parameter.** The party→field-element map
    is provided by the caller. For `F = ZMod p` with `p > n`, the
    canonical embedding `i ↦ ((i.val + 1 : ℕ) : F)` works.
    Injectivity is *not* needed for secrecy (it's enforced
    operationally for distinguishability of parties).

## Per implementation plan v2.2 §M1 W4

Note: the plan's Embed.lean Level-2 conservativity and
Invariant.lean (almost-sure invariants) are deferred — both
require trace-measure infrastructure (M2 W1 per design plan).
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
    (pts : Finset F) (h_card : pts.card ≤ t) (h_nz : (0 : F) ∉ pts)
    (h_F : t + 1 ≤ Fintype.card F) :
    (Leslie.Prob.Polynomial.uniformWithFixedZero t s).map
        (fun f => fun (p : pts) => f.eval p.val)
      =
    (Leslie.Prob.Polynomial.uniformWithFixedZero t s').map
        (fun f => fun (p : pts) => f.eval p.val) := by
  rw [Leslie.Prob.Polynomial.evals_uniform t s pts h_card h_nz h_F,
      Leslie.Prob.Polynomial.evals_uniform t s' pts h_card h_nz h_F]

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

/-- The view of a coalition: the (`Option`-wrapped) shares of its
members. Pure data projection — no probabilistic dependencies. -/
def coalitionView (C : Coalition n t) (st : ShamirState F n) :
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

Given a coalition `C` of size ≤ t and a `partyPoint` avoiding 0,
the distribution of `C`'s shares after dealing depends only on the
coalition (not on the secret). Reduces to `shamir_secrecy_pts` by
transporting along `partyPoint` and stripping the `Option.some`
wrapper.

Note: injectivity of `partyPoint` is *not* required — the proof
goes through `Finset.card_image_le`, which gives the size bound
regardless. So this theorem also holds when multiple parties
share an evaluation point (in which case they jointly observe
fewer distinct shares — still `≤ t` of them). For standard
Shamir, callers will supply an injective `partyPoint` anyway. -/
theorem shamir_secrecy {t : ℕ}
    (partyPoint : Fin n → F)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
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
  rw [shamir_secrecy_pts t s s' pts h_card h_nz h_F]

/-! ## State-level secrecy

Connecting `shamir_secrecy` to the spec: the post-deal coalition
view, computed via `step` ∘ `coalitionView`, is independent of the
secret. -/

/-- State-level secrecy: when the dealer's gate holds (no shares
dealt), the post-deal coalition-view distribution depends only on
the coalition, not on the secret.

This is the corollary that makes `shamirShare` the *operational
witness* for the secrecy claim: the spec, the step semantics, and
the coalition view all participate. -/
theorem shamir_secrecy_via_step {t : ℕ}
    (partyPoint : Fin n → F)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (C : Coalition n t) (s s' : F)
    (initial : ShamirState F n)
    (h_init : ∀ i, initial.shares i = none) :
    Option.map (PMF.map (coalitionView C))
        ((shamirShare t partyPoint).step (.deal s) initial)
      =
    Option.map (PMF.map (coalitionView C))
        ((shamirShare t partyPoint).step (.deal s') initial) := by
  -- Both `step` calls succeed (gate = `h_init`).
  have h_gate : ∀ (sec : F),
      ((shamirShare t partyPoint).actions (.deal sec)).gate initial :=
    fun _ => h_init
  rw [ProbActionSpec.step_eq_some (h_gate s),
      ProbActionSpec.step_eq_some (h_gate s')]
  -- After `step_eq_some` the goal is `some _ = some _`; strip the
  -- `Option.map`/`some` wrapper and reduce to `effect_s.map view =
  -- effect_s'.map view`. The two `effect` calls reduce definitionally
  -- to `(uniformWithFixedZero t _).map poly→state`; combine the two
  -- maps via `PMF.map_comp` and reduce to `shamir_secrecy`.
  simp only [Option.map_some, Option.some_inj]
  rw [show ((shamirShare t partyPoint).actions (.deal s)).effect initial (h_gate s)
      = (Leslie.Prob.Polynomial.uniformWithFixedZero t s).map fun f =>
          ({ shares := fun i => some (f.eval (partyPoint i)) } : ShamirState F n)
      from rfl,
      show ((shamirShare t partyPoint).actions (.deal s')).effect initial (h_gate s')
      = (Leslie.Prob.Polynomial.uniformWithFixedZero t s').map fun f =>
          ({ shares := fun i => some (f.eval (partyPoint i)) } : ShamirState F n)
      from rfl,
      PMF.map_comp, PMF.map_comp]
  exact shamir_secrecy partyPoint h_nz_pp h_F C s s'

end Leslie.Examples.Prob.Shamir
