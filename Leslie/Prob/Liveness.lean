/-
M3 entry gate — `ASTCertificate` and `FairASTCertificate`.

This module defines the certificate structures for almost-sure
termination (AST) under, respectively, demonic and weakly-fair
adversaries. The structures encode the proof rules from:

  * **POPL 2025** Majumdar–Sathiyanarayana, Rule 3.2 — likelihood
    supermartingale `V` plus distance variant `U` with sublevel-set
    compatibility (`ASTCertificate`).
  * **POPL 2026** ibid., fair extension — same shape but with
    supermartingale / variant conditions required only under fair
    adversaries (`FairASTCertificate`).

## Status (M3 W0 — entry gate)

Both structures are declared with **field types pinned down**. The
`*.sound` theorems and helper lemmas carry `sorry`s; the goal of
the entry gate is to verify that the *shape* compiles cleanly
against the AVSS termination certificate (`Examples/Prob/AVSSStub.lean`).
The actual soundness proofs land in M3 W1–W2.

## Why two certificates

The demonic AST rule alone is insufficient for AVSS termination:
the AVSS protocol terminates only under fair scheduling (the
adversary cannot indefinitely starve honest delivery). The fair
extension restricts the supermartingale / variant conditions to
fair adversaries, matching the temporal-logic side condition
`□◇⟨honestDeliver⟩` (etc.) baked into `FairnessAssumptions`.

Per implementation plan v2.2 §M3 entry-gate + design plan v2.2
§"AST rule".
-/

import Leslie.Prob.Action
import Leslie.Prob.Adversary
import Leslie.Prob.Refinement
import Leslie.Prob.Trace

namespace Leslie.Prob

open MeasureTheory NNReal

variable {σ ι : Type*}

/-! ## ASTCertificate (POPL 2025 Rule 3.2)

Demonic AST rule. The certificate package:

  * `Inv` — an inductive invariant that holds along every execution
    (modulo the initial-state predicate).
  * `V` — a non-negative likelihood supermartingale, zero on
    terminated states. Witnesses that the protocol "doesn't drift
    away" from termination indefinitely.
  * `U` — a non-negative integer-valued distance variant, zero on
    terminated states, decreasing with positive probability on
    every step within the sublevel set `{V ≤ k}` for every `k`.

Both `V` and `U` are needed: `V` alone gives "termination has
positive probability", `U` upgrades that to "almost-sure
termination" via the strong-Markov-style pumping argument in the
POPL 2025 proof. -/

/-- Demonic almost-sure-termination certificate (POPL 2025 Rule 3.2).

The fields encode the proof obligations the POPL 2025 demonic AST
rule requires.

**No `sound` theorem is exported for this structure.** The demonic
rule is provably false under our `Adversary` model because of the
stuttering schedule (`A.schedule _ = none` everywhere). Concrete
protocols in this development use `FairASTCertificate` (POPL 2026
fair extension) instead — fairness rules out indefinite stuttering
on fair-required actions, restoring soundness. See
`docs/randomized-leslie-spike/10-stuttering-adversary-finding.md`.
The structure is retained so calibration tests
(e.g., `Examples/Prob/RandomWalker1D.lean`) can validate the
certificate field shape; lifting helpers `liftV` / `liftU` are kept
for any future demonic-AST development. -/
structure ASTCertificate
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (spec : ProbActionSpec σ ι) (terminated : σ → Prop) where
  /-- Inductive invariant. -/
  Inv : σ → Prop
  /-- Likelihood supermartingale (non-negative, zero on terminated). -/
  V : σ → ℝ≥0
  /-- Distance variant (non-negative integer, zero on terminated). -/
  U : σ → ℕ
  /-- Initial-state implication: `spec.init s → Inv s`. -/
  inv_init : ∀ s, spec.init s → Inv s
  /-- Step preservation: for any gated action, `Inv` is preserved. -/
  inv_step : ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
    Inv s → ∀ s' ∈ ((spec.actions i).effect s h).support, Inv s'
  /-- `V` is zero exactly when terminated (within the invariant). -/
  V_term : ∀ s, Inv s → terminated s → V s = 0
  /-- `V` is positive at non-terminated states (within the invariant). -/
  V_pos : ∀ s, Inv s → ¬ terminated s → 0 < V s
  /-- Supermartingale condition: under any gated action, the expected
  `V`-value at the next state is at most the current `V`. Stated as
  a tsum over the per-action PMF support. -/
  V_super : ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
    Inv s → ¬ terminated s →
    ∑' s' : σ, ((spec.actions i).effect s h) s' * V s' ≤ V s
  /-- `U` is zero on terminated states (within the invariant). -/
  U_term : ∀ s, Inv s → terminated s → U s = 0
  /-- `U` is bounded on every sublevel set of `V`. -/
  U_bdd_subl : ∀ k : ℝ≥0, ∃ M : ℕ, ∀ s, Inv s → V s ≤ k → U s ≤ M
  /-- `U` decreases with positive probability under any action that
  fires from a non-terminated state. The minimum decrease probability
  on any sublevel set is uniformly bounded below. -/
  U_dec_prob : ∀ k : ℝ≥0, ∃ p : ℝ≥0, 0 < p ∧
    ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
      Inv s → ¬ terminated s → V s ≤ k →
      p ≤ ∑' s' : σ,
        ((spec.actions i).effect s h) s' *
          (if U s' < U s then 1 else 0)
  /-- `V` is uniformly bounded on the invariant set.

  **Why this field is needed.** Without a uniform bound, the
  `pi_infty_zero` step of soundness would invoke Doob's L¹-bounded
  martingale convergence — but a non-negative supermartingale's L¹
  norm is bounded by its initial expectation, which can be infinite
  if `V` is unbounded on `μ₀`'s support. Adding this field makes
  the trajectory `liftV cert n ω = V (ω n).1` uniformly bounded
  by `K` for every `ω` in the AE-set where `Inv` holds, which
  collapses `pi_infty_zero` to the trivial case (the bad set is
  empty) and reduces soundness to `pi_n_AST K`.

  Concrete protocols typically satisfy this: AVSS / Bracha / random
  walker all have state-bounded `V` since the protocol's reachable
  state space is bounded by the initial parameters. The field is
  also what POPL 2025 §3.2's actual statement requires (the paper
  uses an L¹-bounded supermartingale; we strengthen to a uniform
  bound on the invariant for cleaner Lean statement). -/
  V_init_bdd : ∃ K : ℝ≥0, ∀ s, Inv s → V s ≤ K

namespace ASTCertificate

variable [Countable σ] [Countable ι]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {spec : ProbActionSpec σ ι} {terminated : σ → Prop}

/-! ### Soundness — NOT provided for the demonic version

The POPL 2025 §3 Lemma 3.2 demonic AST rule is **provably false**
under our `Adversary` model, which permits stuttering schedules
(`A.schedule _ = none` everywhere). On such a stuttering trace the
state is constant, so any `cert.V (ω n).1 ≤ N` hypothesis is
trivially satisfied while termination need not hold. The standard
POPL 2025 statement implicitly assumes a non-stuttering adversary;
our weaker `Adversary` model makes the rule unsound as-stated.

We therefore **do not export** `ASTCertificate.sound`. Concrete
protocols use `FairASTCertificate.sound` (the POPL 2026 fair
extension) instead — fairness rules out indefinite stuttering on
fair-required actions, restoring soundness. The fair version's
`sound` is closed (modulo trajectory-form witnesses on the caller's
side); see `FairASTCertificate.sound_traj_det` for the
deterministic-protocol consumer-friendly form.

Possible future work: refine `ASTCertificate` with a non-stuttering
field on the adversary (a `progress`-style hypothesis ruling out
indefinite stuttering at non-terminated states), restoring the
demonic rule to soundness. Documented in
`docs/randomized-leslie-spike/10-stuttering-adversary-finding.md`.
For now, only the structure `ASTCertificate` itself is exported,
without a soundness theorem; calibration tests
(e.g., `Examples/Prob/RandomWalker1D.lean`) construct certificate
instances to validate the structure's API but don't invoke
soundness.

The coordinate-lift helpers `liftV` and `liftU` below are kept as
useful primitives for any future demonic-AST development. -/

/-- Coordinate-`n` lift of the certificate's likelihood
supermartingale `cert.V` to the trace measure: `Vₙ ω = cert.V (ω n).1`. -/
noncomputable def liftV (cert : ASTCertificate spec terminated)
    (n : ℕ) (ω : Trace σ ι) : ℝ≥0 :=
  cert.V ((ω n).1)

/-- Coordinate-`n` lift of the certificate's distance variant
`cert.U` to the trace measure: `Uₙ ω = cert.U (ω n).1`. -/
def liftU (cert : ASTCertificate spec terminated) (n : ℕ)
    (ω : Trace σ ι) : ℕ :=
  cert.U ((ω n).1)

end ASTCertificate

/-! ## FairASTCertificate (POPL 2026 fair extension)

Same shape as `ASTCertificate`, but the supermartingale and
variant decrease conditions are required only under *weakly fair*
adversaries — i.e., adversaries that don't indefinitely starve
actions in `fair_actions`.

This rule is what AVSS termination needs: a corrupt-and-faulty
adversary can refuse to schedule honest delivery for arbitrarily
long, but cannot do so *forever* (that's the fairness assumption).
Under that constraint, the supermartingale eventually pays out. -/

/-- Fair almost-sure-termination certificate (POPL 2026).

Carries the same field shape as `ASTCertificate` plus a
`FairnessAssumptions` witness; the supermartingale and variant
conditions hold against `FairAdversary _ F`. -/
structure FairASTCertificate
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (spec : ProbActionSpec σ ι) (F : FairnessAssumptions σ ι)
    (terminated : σ → Prop) where
  /-- Inductive invariant. -/
  Inv : σ → Prop
  /-- Likelihood supermartingale. -/
  V : σ → ℝ≥0
  /-- Distance variant. -/
  U : σ → ℕ
  /-- Initial-state implication. -/
  inv_init : ∀ s, spec.init s → Inv s
  /-- Step preservation under fair adversary. -/
  inv_step : ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
    Inv s → ∀ s' ∈ ((spec.actions i).effect s h).support, Inv s'
  /-- `V` zero on terminated. -/
  V_term : ∀ s, Inv s → terminated s → V s = 0
  /-- `V` positive on non-terminated. -/
  V_pos : ∀ s, Inv s → ¬ terminated s → 0 < V s
  /-- Supermartingale condition (unconditional: every gated step is
  weakly non-increasing in `V` regardless of fairness; fairness
  only matters for variant decrease, not for the supermartingale
  bound). -/
  V_super : ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
    Inv s → ¬ terminated s →
    ∑' s' : σ, ((spec.actions i).effect s h) s' * V s' ≤ V s
  /-- Strict supermartingale on fair-actions: when a fair-required
  action fires, `V` strictly decreases in expectation. This is the
  fairness payoff that the demonic rule lacks. -/
  V_super_fair : ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
    i ∈ F.fair_actions → Inv s → ¬ terminated s →
    ∑' s' : σ, ((spec.actions i).effect s h) s' * V s' < V s
  /-- `U` zero on terminated. -/
  U_term : ∀ s, Inv s → terminated s → U s = 0
  /-- Deterministic-decrease pattern: when a fair-required action
  fires, `U` either decreases or the run reaches a state where
  another fair-required action becomes enabled. -/
  U_dec_det : ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
    i ∈ F.fair_actions → Inv s → ¬ terminated s →
    ∀ s' ∈ ((spec.actions i).effect s h).support,
      U s' < U s ∨ ∃ j ∈ F.fair_actions, (spec.actions j).gate s'
  /-- `U` bounded on every sublevel set of `V`. -/
  U_bdd_subl : ∀ k : ℝ≥0, ∃ M : ℕ, ∀ s, Inv s → V s ≤ k → U s ≤ M
  /-- Probabilistic decrease under fair scheduling: with positive
  probability, `U` decreases in finitely many steps. -/
  U_dec_prob : ∀ k : ℝ≥0, ∃ p : ℝ≥0, 0 < p ∧
    ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
      i ∈ F.fair_actions → Inv s → ¬ terminated s → V s ≤ k →
      p ≤ ∑' s' : σ,
        ((spec.actions i).effect s h) s' *
          (if U s' < U s then 1 else 0)
  /-- `V` is uniformly bounded on the invariant set. Same role as
  `ASTCertificate.V_init_bdd`: makes the trajectory `liftV` uniformly
  bounded, so the soundness proof skips Doob's convergence theorem
  entirely and reduces to the finite-variant sublevel rule. -/
  V_init_bdd : ∃ K : ℝ≥0, ∀ s, Inv s → V s ≤ K

namespace FairASTCertificate

variable [Countable σ] [Countable ι]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {spec : ProbActionSpec σ ι} {F : FairnessAssumptions σ ι}
  {terminated : σ → Prop}

/-! ### Soundness — proof skeleton

The fair soundness proof decomposes along the same `pi_n_AST` /
`pi_infty_zero` / `partition_almostDiamond` skeleton as the demonic
case. The sound rule implemented here is the monotone fair variant:
in addition to trajectory fair progress, callers provide AE witnesses
that `U` is non-increasing on all steps and strictly decreases on fair
firings in each `V` sublevel.

The three pieces are:

  * `pi_infty_zero_fair` — closed via `AlmostBox_of_inductive`
    + `V_init_bdd`, exactly as in the demonic case.
  * `partition_almostDiamond_fair` — closed by the partition
    argument once `pi_n_AST_fair` is provided.
  * `pi_n_AST_fair` — closed by the deterministic monotone
    specialization `pi_n_AST_fair_with_progress_det`.

The older probabilistic chain witness remains below as a placeholder
for the more general conditional Borel-Cantelli development; it is no
longer on the `sound` path. -/

/-- Coordinate-`n` lift of the certificate's likelihood
supermartingale `cert.V` to the trace measure. -/
noncomputable def liftV (cert : FairASTCertificate spec F terminated)
    (n : ℕ) (ω : Trace σ ι) : ℝ≥0 :=
  cert.V ((ω n).1)

/-- Coordinate-`n` lift of the certificate's distance variant
`cert.U` to the trace measure. -/
def liftU (cert : FairASTCertificate spec F terminated) (n : ℕ)
    (ω : Trace σ ι) : ℕ :=
  cert.U ((ω n).1)

/- **Historical general fair sublevel rule sketch.** On the
sublevel set `{ω | ∀ k, cert.V (ω k).1 ≤ N}`, almost-sure
termination follows from `U_bdd_subl` plus the fair finite-variant
rule.

Unlike the (now-removed) demonic counterpart, this fair version
does **not** suffer the stuttering-adversary issue:
`A : FairAdversary σ ι F` carries the weakly-fair witness
`A.fair : F.isWeaklyFair A.toAdversary`, which forces every
fair-required action to fire eventually whenever continuously
enabled. So the `always-stutter` adversary that breaks the
demonic AST rule is excluded by the type signature.

**Status:** this sketch is not used for `FairASTCertificate.sound`.
The implemented rule is the monotone specialization below. The more
general positive-probability rule is tracked in
`docs/randomized-leslie-spike/13-fair-ast-borel-cantelli-plan.md`.

The proof sketch (assuming the assembly):
  1. From `A.fair`, every fair action is fired infinitely often AE.
  2. From `cert.U_dec_det` + `cert.U_dec_prob`, on every fair
     firing, `U` decreases (deterministically or with probability
     `p > 0` on the sublevel set `{V ≤ N}`).
  3. From `cert.U_bdd_subl N = M`, `U ≤ M` along the sublevel
     trajectory.
  4. Geometric tail bound: after at most `M / p` fair firings AE,
     `U` reaches `0`, which forces termination via
     `terminated`-equivalence on `U = 0` (from `cert.V_pos` +
     `cert.U_term`).

Tracked under M3 W3+. The general (non-monotone) Mathlib gap is
the conditional Borel-Cantelli filtration plumbing; see
`docs/randomized-leslie-spike/14-stopping-time-and-borel-cantelli.md`.

**Two stacked gaps** (see `docs/randomized-leslie-spike/11-fair-progress-blocker.md`):

  1. *Trajectory-progress witness gap*: `F.isWeaklyFair` has type
     `Adversary σ ι → Prop`, an opaque predicate. The proof needs
     "fair actions fire AE i.o. on the trajectory" — a trajectory-
     level statement. Concrete instances of `FairnessAssumptions`
     in our codebase (`brbFair`, `boFair`, `avssFair`) all use
     `isWeaklyFair := True` (placeholder), so the witness isn't
     extractable. The fix is to either (a) refine
     `FairnessAssumptions` with a trajectory-form fairness witness,
     or (b) take a `TrajectoryFairProgress` hypothesis (see
     `pi_n_AST_fair_with_progress` below).
  2. *Mathlib Borel–Cantelli + filtration plumbing*: even with the
     progress witness, assembling the geometric-tail argument
     requires the natural filtration on `Trace σ ι` and a
     conditional Borel–Cantelli specialization. ~250 LOC. -/
/-! ### Trajectory progress witness — gap 1 made explicit

This is the proof obligation the abstract `FairnessAssumptions.isWeaklyFair`
fails to deliver. `TrajectoryFairProgress` says: **AE on the trace
measure, every fair-required action fires infinitely often.**

POPL 2026 takes a similar trajectory-level fairness condition as
primitive in its rule statement; our `FairnessAssumptions` keeps
`isWeaklyFair` opaque to allow per-protocol concrete witnesses.

A future refactor of `FairnessAssumptions` to require a witness of
this shape would let `pi_n_AST_fair` be proved without an extra
hypothesis. Meanwhile, `pi_n_AST_fair_with_progress` takes the
witness explicitly. -/

/-- AE-fairness predicate on the trajectory: every fair-required
action fires infinitely often. -/
def TrajectoryFairProgress (spec : ProbActionSpec σ ι)
    (F : FairnessAssumptions σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (A : FairAdversary σ ι F) : Prop :=
  ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
    ∀ N : ℕ, ∃ n ≥ N, ∃ i ∈ F.fair_actions, (ω (n + 1)).2 = some i

/-- A fair-required action fires between trace positions `n` and
`n + 1`. -/
def FairFiresAt (F : FairnessAssumptions σ ι) (ω : Trace σ ι) (n : ℕ) : Prop :=
  ∃ i ∈ F.fair_actions, (ω (n + 1)).2 = some i

omit [Countable σ] [MeasurableSingletonClass σ] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] in
/-- Fixed-time fair-firing events are measurable. -/
theorem measurableSet_fairFiresAt
    (F : FairnessAssumptions σ ι) (n : ℕ) :
    MeasurableSet {ω : Trace σ ι | FairFiresAt F ω n} := by
  unfold FairFiresAt
  let fairSome : Set (Option ι) := {oi | ∃ i ∈ F.fair_actions, oi = some i}
  have hfairSome : MeasurableSet fairSome := by
    exact (Set.to_countable fairSome).measurableSet
  exact hfairSome.preimage
    (measurable_snd.comp (measurable_pi_apply (n + 1)))

/-- A `Nat`-valued trace functional is measurable when all singleton
fibers are measurable. This local helper avoids relying on a packaged
countable-codomain theorem. -/
theorem measurable_nat_of_measurableSet_fiber
    {α : Type*} [MeasurableSpace α]
    (f : α → ℕ) (h : ∀ n : ℕ, MeasurableSet {x : α | f x = n}) :
    Measurable f := by
  intro s _hs
  have hpre : f ⁻¹' s =
      Set.iUnion (α := α) (fun n : {n : ℕ // n ∈ s} =>
        {x : α | f x = n.1}) := by
    ext x
    rw [Set.mem_iUnion]
    constructor
    · intro hx
      exact ⟨⟨f x, hx⟩, rfl⟩
    · intro hx
      rcases hx with ⟨n, hn⟩
      change f x ∈ s
      rw [hn]
      exact n.2
  rw [hpre]
  exact MeasurableSet.iUnion fun n => h n.1

/-- First fair firing time at or after `N`, defaulting to `N` when no
such time exists. The default branch is never used under
`TrajectoryFairProgress`. -/
noncomputable def firstFairAfter
    (F : FairnessAssumptions σ ι) (ω : Trace σ ι) (N : ℕ) : ℕ :=
  by
    classical
    exact if h : ∃ n : ℕ, n ≥ N ∧ FairFiresAt F ω n then Nat.find h else N

omit [Countable σ] [Countable ι] [MeasurableSpace σ] [MeasurableSingletonClass σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Correctness of `firstFairAfter` when a fair firing exists after
the lower bound. -/
theorem firstFairAfter_spec
    (F : FairnessAssumptions σ ι) (ω : Trace σ ι) (N : ℕ)
    (h : ∃ n : ℕ, n ≥ N ∧ FairFiresAt F ω n) :
    firstFairAfter F ω N ≥ N ∧ FairFiresAt F ω (firstFairAfter F ω N) := by
  classical
  unfold firstFairAfter
  rw [dif_pos h]
  exact Nat.find_spec h

/-- Fiber decomposition for `firstFairAfter`. Either there is no fair
firing after `N` and the default branch returns `N`, or `m` is the
least fair firing time at/after `N`. -/
def firstFairAfterFiberSet
    (F : FairnessAssumptions σ ι) (N m : ℕ) : Set (Trace σ ι) :=
  {ω | (¬ (∃ n : ℕ, n ≥ N ∧ FairFiresAt F ω n) ∧ N = m) ∨
    ((m ≥ N ∧ FairFiresAt F ω m) ∧
      ∀ n : ℕ, n < m → ¬ (n ≥ N ∧ FairFiresAt F ω n))}

omit [Countable σ] [Countable ι] [MeasurableSpace σ] [MeasurableSingletonClass σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Exact fiber characterization for `firstFairAfter`. -/
theorem firstFairAfter_fiber_eq
    (F : FairnessAssumptions σ ι) (N m : ℕ) :
    {ω : Trace σ ι | firstFairAfter F ω N = m} =
      firstFairAfterFiberSet F N m := by
  classical
  ext ω
  unfold firstFairAfterFiberSet
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hfirst
    unfold firstFairAfter at hfirst
    by_cases h : ∃ n : ℕ, n ≥ N ∧ FairFiresAt F ω n
    · rw [dif_pos h] at hfirst
      right
      exact (Nat.find_eq_iff h).mp hfirst
    · rw [dif_neg h] at hfirst
      left
      exact ⟨h, hfirst⟩
  · intro hright
    unfold firstFairAfter
    rcases hright with ⟨hno, hNm⟩ | hmin
    · rw [dif_neg hno]
      exact hNm
    · have hex : ∃ n : ℕ, n ≥ N ∧ FairFiresAt F ω n :=
        ⟨m, hmin.1.1, hmin.1.2⟩
      rw [dif_pos hex]
      exact (Nat.find_eq_iff hex).mpr hmin

omit [Countable σ] [MeasurableSingletonClass σ] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] in
/-- The explicit fiber set for `firstFairAfter` is measurable. -/
theorem measurableSet_firstFairAfterFiberSet
    (F : FairnessAssumptions σ ι) (N m : ℕ) :
    MeasurableSet (firstFairAfterFiberSet F N m) := by
  classical
  have hExists : MeasurableSet
      {ω : Trace σ ι | ∃ n : ℕ, n ≥ N ∧ FairFiresAt F ω n} := by
    have hrepr :
        {ω : Trace σ ι | ∃ n : ℕ, n ≥ N ∧ FairFiresAt F ω n} =
          ⋃ n : ℕ, {ω : Trace σ ι | n ≥ N ∧ FairFiresAt F ω n} := by
      ext ω
      simp
    rw [hrepr]
    exact MeasurableSet.iUnion fun n => by
      by_cases hn : n ≥ N
      · simpa [hn] using measurableSet_fairFiresAt F n
      · have hempty :
            {ω : Trace σ ι | n ≥ N ∧ FairFiresAt F ω n} = ∅ := by
          ext ω
          simp [hn]
        rw [hempty]
        exact MeasurableSet.empty
  have hNo : MeasurableSet
      {ω : Trace σ ι | ¬ (∃ n : ℕ, n ≥ N ∧ FairFiresAt F ω n)} :=
    hExists.compl
  have hLeft : MeasurableSet
      {ω : Trace σ ι |
        ¬ (∃ n : ℕ, n ≥ N ∧ FairFiresAt F ω n) ∧ N = m} := by
    by_cases hNm : N = m
    · simpa [hNm] using hNo
    · have hempty :
          {ω : Trace σ ι |
            ¬ (∃ n : ℕ, n ≥ N ∧ FairFiresAt F ω n) ∧ N = m} = ∅ := by
        ext ω
        simp [hNm]
      rw [hempty]
      exact MeasurableSet.empty
  have hBefore : MeasurableSet
      {ω : Trace σ ι |
        ∀ n : ℕ, n < m → ¬ (n ≥ N ∧ FairFiresAt F ω n)} := by
    have hrepr :
        {ω : Trace σ ι |
          ∀ n : ℕ, n < m → ¬ (n ≥ N ∧ FairFiresAt F ω n)} =
          ⋂ n : ℕ,
            {ω : Trace σ ι |
              n < m → ¬ (n ≥ N ∧ FairFiresAt F ω n)} := by
      ext ω
      simp
    rw [hrepr]
    exact MeasurableSet.iInter fun n => by
      by_cases hlt : n < m
      · by_cases hn : n ≥ N
        · have heq :
              {ω : Trace σ ι |
                n < m → ¬ (n ≥ N ∧ FairFiresAt F ω n)} =
                {ω : Trace σ ι | ¬ FairFiresAt F ω n} := by
            ext ω
            simp [hlt, hn]
          rw [heq]
          exact (measurableSet_fairFiresAt F n).compl
        · have heq :
              {ω : Trace σ ι |
                n < m → ¬ (n ≥ N ∧ FairFiresAt F ω n)} = Set.univ := by
            ext ω
            simp [hn]
          rw [heq]
          exact MeasurableSet.univ
      · have heq :
            {ω : Trace σ ι |
              n < m → ¬ (n ≥ N ∧ FairFiresAt F ω n)} = Set.univ := by
          ext ω
          simp [hlt]
        rw [heq]
        exact MeasurableSet.univ
  have hRight : MeasurableSet
      {ω : Trace σ ι |
        (m ≥ N ∧ FairFiresAt F ω m) ∧
          ∀ n : ℕ, n < m → ¬ (n ≥ N ∧ FairFiresAt F ω n)} := by
    by_cases hmN : m ≥ N
    · have heq :
          {ω : Trace σ ι |
            (m ≥ N ∧ FairFiresAt F ω m) ∧
              ∀ n : ℕ, n < m → ¬ (n ≥ N ∧ FairFiresAt F ω n)} =
            {ω : Trace σ ι | FairFiresAt F ω m} ∩
              {ω : Trace σ ι |
                ∀ n : ℕ, n < m → ¬ (n ≥ N ∧ FairFiresAt F ω n)} := by
        ext ω
        simp [hmN]
      rw [heq]
      exact (measurableSet_fairFiresAt F m).inter hBefore
    · have hempty :
          {ω : Trace σ ι |
            (m ≥ N ∧ FairFiresAt F ω m) ∧
              ∀ n : ℕ, n < m → ¬ (n ≥ N ∧ FairFiresAt F ω n)} = ∅ := by
        ext ω
        simp [hmN]
      rw [hempty]
      exact MeasurableSet.empty
  unfold firstFairAfterFiberSet
  exact hLeft.union hRight

omit [Countable σ] [MeasurableSingletonClass σ] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] in
/-- Fixed-lower-bound `firstFairAfter` fibers are measurable. -/
theorem measurableSet_firstFairAfter_eq
    (F : FairnessAssumptions σ ι) (N m : ℕ) :
    MeasurableSet {ω : Trace σ ι | firstFairAfter F ω N = m} := by
  rw [firstFairAfter_fiber_eq F N m]
  exact measurableSet_firstFairAfterFiberSet F N m

omit [Countable σ] [MeasurableSingletonClass σ] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] in
/-- For a fixed lower bound, `firstFairAfter` is measurable. -/
theorem measurable_firstFairAfter
    (F : FairnessAssumptions σ ι) (N : ℕ) :
    Measurable (fun ω : Trace σ ι => firstFairAfter F ω N) :=
  measurable_nat_of_measurableSet_fiber _ fun m =>
    measurableSet_firstFairAfter_eq F N m

/-- Iterated fair-firing times. The successor asks for a fair firing at
least two indices after the previous one, so the resulting sequence is
strictly separated and its successor state is already past the prior
firing step. -/
noncomputable def fairFiringTime
    (F : FairnessAssumptions σ ι) (ω : Trace σ ι) : ℕ → ℕ
  | 0 => firstFairAfter F ω 0
  | k + 1 => firstFairAfter F ω (fairFiringTime F ω k + 2)

omit [Countable σ] [MeasurableSingletonClass σ] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] in
/-- Iterated fair-firing time fibers are measurable. -/
theorem measurableSet_fairFiringTime_eq
    (F : FairnessAssumptions σ ι) :
    ∀ k m : ℕ, MeasurableSet
      {ω : Trace σ ι | fairFiringTime F ω k = m} := by
  intro k
  induction k with
  | zero =>
    intro m
    simpa [fairFiringTime] using measurableSet_firstFairAfter_eq F 0 m
  | succ k ih =>
    intro m
    have hrepr :
        {ω : Trace σ ι | fairFiringTime F ω (k + 1) = m} =
          Set.iUnion (α := Trace σ ι) (fun N : ℕ =>
            ({ω : Trace σ ι | fairFiringTime F ω k + 2 = N} ∩
              {ω : Trace σ ι | firstFairAfter F ω N = m})) := by
      ext ω
      constructor
      · intro hω
        rw [Set.mem_iUnion]
        refine ⟨fairFiringTime F ω k + 2, ?_⟩
        exact ⟨by rfl, by simpa [fairFiringTime] using hω⟩
      · intro hω
        rw [Set.mem_iUnion] at hω
        rcases hω with ⟨N, hN, hfirst⟩
        have hN' : N = fairFiringTime F ω k + 2 := hN.symm
        simpa [fairFiringTime, hN'] using hfirst
    rw [hrepr]
    exact MeasurableSet.iUnion fun N => by
      have hprev :
          MeasurableSet {ω : Trace σ ι | fairFiringTime F ω k + 2 = N} := by
        by_cases hN : ∃ r : ℕ, r + 2 = N
        · rcases hN with ⟨r, hr⟩
          have heq :
              {ω : Trace σ ι | fairFiringTime F ω k + 2 = N} =
                {ω : Trace σ ι | fairFiringTime F ω k = r} := by
            ext ω
            constructor
            · intro hω
              change fairFiringTime F ω k + 2 = N at hω
              rw [← hr] at hω
              exact Nat.add_right_cancel hω
            · intro hω
              change fairFiringTime F ω k + 2 = N
              change fairFiringTime F ω k = r at hω
              rw [hω, hr]
          rw [heq]
          exact ih r
        · have hempty :
              {ω : Trace σ ι | fairFiringTime F ω k + 2 = N} = ∅ := by
            ext ω
            constructor
            · intro hω
              exact False.elim (hN ⟨fairFiringTime F ω k, hω⟩)
            · intro hω
              simp at hω
          rw [hempty]
          exact MeasurableSet.empty
      exact hprev.inter (measurableSet_firstFairAfter_eq F N m)

omit [Countable σ] [MeasurableSingletonClass σ] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] in
/-- Iterated fair-firing times are measurable stopping-time selectors. -/
theorem measurable_fairFiringTime
    (F : FairnessAssumptions σ ι) (k : ℕ) :
    Measurable (fun ω : Trace σ ι => fairFiringTime F ω k) :=
  measurable_nat_of_measurableSet_fiber _ fun m =>
    measurableSet_fairFiringTime_eq F k m

omit [Countable σ] [Countable ι] [MeasurableSpace σ] [MeasurableSingletonClass σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Every iterated fair-firing time is a fair firing under trajectory
progress. -/
theorem fairFiringTime_fair
    (F : FairnessAssumptions σ ι) (ω : Trace σ ι)
    (hprog : ∀ N : ℕ, ∃ n ≥ N, FairFiresAt F ω n) :
    ∀ k : ℕ, FairFiresAt F ω (fairFiringTime F ω k) := by
  intro k
  cases k with
  | zero =>
    exact (firstFairAfter_spec F ω 0 (by
      rcases hprog 0 with ⟨n, hn, hfair⟩
      exact ⟨n, hn, hfair⟩)).2
  | succ k =>
    exact (firstFairAfter_spec F ω (fairFiringTime F ω k + 2) (by
      rcases hprog (fairFiringTime F ω k + 2) with ⟨n, hn, hfair⟩
      exact ⟨n, hn, hfair⟩)).2

omit [Countable σ] [Countable ι] [MeasurableSpace σ] [MeasurableSingletonClass σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Iterated fair-firing times are separated by at least two steps. -/
theorem fairFiringTime_step
    (F : FairnessAssumptions σ ι) (ω : Trace σ ι)
    (hprog : ∀ N : ℕ, ∃ n ≥ N, FairFiresAt F ω n) :
    ∀ k : ℕ, fairFiringTime F ω (k + 1) ≥ fairFiringTime F ω k + 2 := by
  intro k
  exact (firstFairAfter_spec F ω (fairFiringTime F ω k + 2) (by
    rcases hprog (fairFiringTime F ω k + 2) with ⟨n, hn, hfair⟩
    exact ⟨n, hn, hfair⟩)).1

/-- Stronger "pointwise fair-at-next-step" hypothesis.
This is strictly stronger than `TrajectoryFairProgress`: it provides
a fair-action witness at every deterministic step index. -/
def PointwiseFairStep (spec : ProbActionSpec σ ι)
    (F : FairnessAssumptions σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (A : FairAdversary σ ι F) : Prop :=
  ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
    ∀ n : ℕ, ∃ i ∈ F.fair_actions, (ω (n + 1)).2 = some i

/-- `PointwiseFairStep` implies `TrajectoryFairProgress` by taking
the witness `n = N` at each lower bound `N`. -/
theorem PointwiseFairStep.toTrajectoryFairProgress
    (spec : ProbActionSpec σ ι)
    (F : FairnessAssumptions σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (A : FairAdversary σ ι F) :
    PointwiseFairStep spec F μ₀ A →
      TrajectoryFairProgress spec F μ₀ A := by
  intro h_pointwise
  filter_upwards [h_pointwise] with ω hω
  intro N
  rcases hω N with ⟨i, hiF, hstep⟩
  exact ⟨N, le_rfl, i, hiF, hstep⟩

/-! ### General-case proof — Lévy / conditional Borel-Cantelli sketch

The general `pi_n_AST_fair_with_progress` differs from the closed
deterministic specialisation in one place: at a fair firing, `U`
decreases *with probability ≥ p > 0* (from `U_dec_prob N = p`), not
deterministically. The certificate's `U_dec_det` allows the
disjunction "decrease at this step OR a new fair action becomes
enabled at the successor" — that disjunction is what blocks the
finite-descent argument used in the deterministic case.

The standard textbook proof (POPL 2026 Rule fair-AST, Lévy's
extension of Borel-Cantelli) decomposes as:

  1. **Filtration.** Take the natural filtration `ℱ` on `Trace σ ι`
     generated by coordinate projections `ω ↦ ω k` for `k ≤ n`.
     Mathlib provides `MeasureTheory.Filtration.natural`, but to
     instantiate it we need each coordinate (`σ × Option ι`) to be
     `MetrizableSpace + BorelSpace` — derivable from the discrete
     topology on `Countable + MeasurableSingletonClass` types but
     not in scope here.

  2. **Decrease events.** Let `D_n := {ω | cert.U (ω (n+1)).1 < cert.U (ω n).1}`.
     These are `ℱ (n+1)`-measurable under the discrete σ-algebra.

  3. **Conditional bound.** From `U_dec_prob N = p`, on the event
     "fair action `i ∈ F.fair_actions` fires at step `n+1` from a
     non-terminated state in the V-sublevel", the kernel structure
     of `traceDist` (specifically the marginal-recurrence equality
     in `Refinement.AlmostBox_of_inductive`) yields
     `μ[D_n | ℱ n] ≥ p · 1_{good_n}`.

  4. **Sum diverges AE.** From `_h_progress`, fair firings happen
     i.o. AE on the trajectory; combined with (3) the conditional
     probabilities `μ[D_n | ℱ n]` sum to ∞ AE on the sublevel.

  5. **Lévy extension of Borel-Cantelli.** Mathlib's
     `MeasureTheory.ae_mem_limsup_atTop_iff` gives `D_n` occurs
     i.o. AE on traces where the conditional sum diverges, *with the
     additional strength that the events are filtration-progressive*.

  6. **Bounded variant + i.o. drop-to-new-min ⇒ termination.** The
     conditional Borel-Cantelli output gives more than i.o. step-drop:
     it gives that the sequence of `U`-minima `U_∗_n := min_{k ≤ n} U (ω k).1`
     strictly decreases i.o. (because each `D_n` event occurring while
     `U_n = U_∗_n` lowers the minimum). Combined with `U_∗_n ∈ ℕ ∩ [0, M]`,
     the minimum can decrease at most `M+1` times, contradicting the
     supposed i.o. condition unless termination is reached.

**Specific Mathlib gaps:**

  * **Gap A** (filtration plumbing): `Filtration.natural` requires
    per-coordinate `MetrizableSpace + BorelSpace` instances, not derivable
    automatically from `Countable + MeasurableSingletonClass`. Either
    refine `traceDist`'s typeclass list with discrete-topology instances
    or add a `Filtration.natural_of_countable` Mathlib lemma. ~50 LOC.

  * **Gap B** (kernel-form conditional probability): the conditional
    expectation `μ[D_n.indicator 1 | ℱ n]` w.r.t. the natural filtration
    of `Kernel.trajMeasure` equals (up to AE-equivalence) the per-step
    kernel evaluation. Mathlib has
    `Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`
    (the disintegration identity, used in `AlmostBox_of_inductive`) but
    the conditional-expectation glue is not packaged. ~150 LOC.

  * **Gap C** (descent assembly for non-monotone `U`): even given
    i.o. step-drop, the descent contradiction needs the i.o.-drop-to-new-min
    strengthening (or an unconditional U-monotonicity field on the
    certificate). The conditional Borel-Cantelli of step (5) provides this
    naturally for "the decrease event happens AT a new minimum" — but
    extracting that requires coupling the i.o.-step result with the
    running-minimum tracking. ~50 LOC of trajectory bookkeeping.

The whole load is the single sorry below. The deterministic
specialisation `pi_n_AST_fair_with_progress_det` below sidesteps gaps
A-B-C by taking U-monotonicity as a trajectory-form hypothesis and
running a pure finite descent. -/

/-! **Retired chain-witness route.** The auxiliary
`pi_n_AST_fair_chain_witness` and its consumer
`pi_n_AST_fair_with_progress_of_chain` previously packaged the
conditional Borel-Cantelli content as a single chain-existence lemma.
That route has been retired in favor of the cleaner
`TrajectoryBCDescent` / `TrajectoryFairRunningMinDropIO` bridge (see
`pi_n_AST_fair_with_progress_bc` and
`pi_n_AST_fair_with_progress_bc_of_running_min_drops` below).

`pi_n_AST_fair_with_progress` is now a thin wrapper around
`pi_n_AST_fair_with_progress_bc_of_running_min_drops`, taking the
post-Borel-Cantelli running-minimum-drop-IO event as an explicit
hypothesis. The remaining analytic bridge — deriving
`TrajectoryFairRunningMinDropIO` from `cert.U_dec_prob` and
`TrajectoryFairProgress` via conditional Borel-Cantelli — is now an
isolated obligation discharged at the call site (see
`docs/randomized-leslie-spike/13-fair-ast-borel-cantelli-plan.md`,
items 1–3 of the Remaining section). -/

/-! `pi_n_AST_fair_with_progress` is now defined further down (after
`pi_n_AST_fair_with_progress_bc_of_running_min_drops`), as a thin
wrapper around the running-minimum-drop bridge. -/

/-! ### Deterministic specialisation — `pi_n_AST_fair_with_progress_det`

For protocols whose distance variant `U` is monotone non-increasing
along every trajectory step and *strictly* decreases on every fair
firing (the deterministic special case of `U_dec_det`), the proof of
`pi_n_AST_fair_with_progress` closes without Borel-Cantelli: a finite
descent argument suffices. We expose this as a sister lemma, taking the
two strengthening conditions as **trajectory-form** hypotheses.

The hypotheses are stated AE on the trace measure:

  * `TrajectoryUMono` — `U` is monotone non-increasing at every step.
  * `TrajectoryFairStrictDecrease` — at every step where a fair-required
    action fires from a non-terminated state below the V-sublevel, `U`
    strictly drops.

Concrete protocols can derive these from `U_dec_det` (specialised to
the deterministic-decrease branch) plus the step-kernel support analysis
already used in `Refinement.AlmostBox_of_inductive`. That derivation is
~100-150 LOC of trajectory plumbing; we leave it to per-protocol work
since it depends on protocol-specific structure (e.g., which non-fair
actions can fire and how they affect `U`).

The general `pi_n_AST_fair_with_progress` (whose `U_dec_det` allows the
disjunction "decrease *or* a new fair action becomes enabled") plus the
probabilistic `U_dec_prob` path requires the natural filtration on
`Trace σ ι` and conditional Borel-Cantelli — gap 2 of M3 W3, deferred. -/

/-- AE-monotonicity: along every trajectory step, the certificate's
distance variant `U` is non-increasing. -/
def TrajectoryUMono (spec : ProbActionSpec σ ι)
    (F : FairnessAssumptions σ ι)
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (A : FairAdversary σ ι F) : Prop :=
  ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
    ∀ n : ℕ, cert.U (ω (n + 1)).1 ≤ cert.U (ω n).1

/-- AE-strict-decrease: at every trajectory step where a fair-required
action fires from a non-terminated state below the V-sublevel, `U`
strictly drops. -/
def TrajectoryFairStrictDecrease (spec : ProbActionSpec σ ι)
    (F : FairnessAssumptions σ ι)
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (A : FairAdversary σ ι F) (N : ℕ) : Prop :=
  ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
    ∀ n : ℕ, (∃ i ∈ F.fair_actions, (ω (n + 1)).2 = some i) →
      ¬ terminated (ω n).1 → cert.V (ω n).1 ≤ (N : ℝ≥0) →
      cert.U (ω (n + 1)).1 < cert.U (ω n).1

/-- **Deterministic specialisation** of `pi_n_AST_fair_with_progress`.

Closes the sublevel-set finite-variant rule under the stronger
deterministic-decrease conditions: `U` monotone non-increasing and
strictly decreasing on every fair firing (in trajectory form). The
proof is a finite-descent argument — no Borel-Cantelli, no filtration
plumbing.

Uses:
  * `cert.U_bdd_subl N` for the uniform `M`-bound on `U` along the
    sublevel.
  * `Refinement.AlmostBox_of_inductive` to lift `cert.Inv` along the
    trajectory.
  * `Nat.find`-style finite descent: pick `M + 2` strictly-increasing
    fair-firing times via iterated `h_progress`, observe
    `U` strictly decreases from one fair-firing time to the next
    (combining strict-decrease at the firing with mono between firings),
    contradicting `U ≤ M`. -/
theorem pi_n_AST_fair_with_progress_det
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : FairAdversary σ ι F)
    (h_progress : TrajectoryFairProgress spec F μ₀ A)
    (N : ℕ)
    (h_U_mono : TrajectoryUMono spec F cert μ₀ A)
    (h_U_strict : TrajectoryFairStrictDecrease spec F cert μ₀ A N) :
    ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
      (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) → ∃ n, terminated (ω n).1 := by
  -- Extract the uniform `M`-bound on `U` along the sublevel.
  obtain ⟨M, hM⟩ := cert.U_bdd_subl (N : ℝ≥0)
  -- Lift `cert.Inv` along trajectories via `AlmostBox_of_inductive`.
  have hbox_inv : AlmostBox spec A.toAdversary μ₀ cert.Inv :=
    AlmostBox_of_inductive cert.Inv
      (fun i s h hInv s' hs' => cert.inv_step i s h hInv s' hs')
      μ₀ h_init_inv A.toAdversary
  unfold AlmostBox at hbox_inv
  unfold TrajectoryFairProgress at h_progress
  unfold TrajectoryUMono at h_U_mono
  unfold TrajectoryFairStrictDecrease at h_U_strict
  -- Filter upwards through all four AE hypotheses.
  filter_upwards [hbox_inv, h_progress, h_U_mono, h_U_strict] with
    ω hInv_all hProg hMono hStrict hVbnd
  -- Goal at this point: ∃ n, terminated (ω n).1.
  -- Strategy: by contradiction, assume `∀ n, ¬ terminated (ω n).1`,
  -- then construct M+2 strictly-increasing fair-firing times whose
  -- U-values form a strictly descending ℕ-sequence below M+1, impossible.
  by_contra hne
  push_neg at hne
  -- hne : ∀ n, ¬ terminated (ω n).1
  -- Bound U by M along the trajectory.
  have hU_bdd : ∀ n, cert.U (ω n).1 ≤ M :=
    fun n => hM _ (hInv_all n) (hVbnd n)
  -- Define `pickFair n` : a fair-firing time `≥ n`.
  -- From `hProg n`, we get such a time.
  -- Use `Classical.choose` to extract.
  let pickFair : ℕ → ℕ := fun n => Classical.choose (hProg n)
  have hpickFair_ge : ∀ n, pickFair n ≥ n := fun n =>
    (Classical.choose_spec (hProg n)).1
  have hpickFair_fair : ∀ n, ∃ i ∈ F.fair_actions,
      (ω (pickFair n + 1)).2 = some i := fun n =>
    (Classical.choose_spec (hProg n)).2
  -- Build the sequence of fair-firing times: `t 0 = pickFair 0`,
  -- `t (k+1) = pickFair (t k + 2)`.
  let t : ℕ → ℕ := fun k => Nat.rec (pickFair 0)
    (fun _ prev => pickFair (prev + 2)) k
  -- Concrete recursion for `t`.
  have ht_zero : t 0 = pickFair 0 := rfl
  have ht_succ : ∀ k, t (k + 1) = pickFair (t k + 2) := fun _ => rfl
  -- Each `t k` is a fair-firing time.
  have ht_fair : ∀ k, ∃ i ∈ F.fair_actions, (ω (t k + 1)).2 = some i := by
    intro k
    cases k with
    | zero => simpa [ht_zero] using hpickFair_fair 0
    | succ k => simpa [ht_succ k] using hpickFair_fair (t k + 2)
  -- Each `t k` separates from the previous: `t (k+1) ≥ t k + 2`.
  have ht_inc : ∀ k, t (k + 1) ≥ t k + 2 := fun k => by
    rw [ht_succ k]; exact hpickFair_ge _
  -- At each `t k`, U strictly decreases at the next step.
  have hU_drop : ∀ k, cert.U (ω (t k + 1)).1 < cert.U (ω (t k)).1 := by
    intro k
    refine hStrict (t k) (ht_fair k) (hne _) (hVbnd _)
  -- Monotonicity iterated: `U (ω (a + j)).1 ≤ U (ω a).1` for all `j`.
  have hU_mono_iter : ∀ a j, cert.U (ω (a + j)).1 ≤ cert.U (ω a).1 := by
    intro a j
    induction j with
    | zero => simp
    | succ j ih =>
      have hstep := hMono (a + j)
      calc cert.U (ω (a + (j + 1))).1
          = cert.U (ω (a + j + 1)).1 := by rw [Nat.add_succ]
        _ ≤ cert.U (ω (a + j)).1 := hstep
        _ ≤ cert.U (ω a).1 := ih
  -- Monotonicity gives `U (ω b).1 ≤ U (ω a).1` whenever `a ≤ b`.
  have hU_mono_le : ∀ a b, a ≤ b → cert.U (ω b).1 ≤ cert.U (ω a).1 := by
    intro a b hab
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hab
    exact hU_mono_iter a j
  -- Combining: U at `t (k+1)` ≤ U at `t k + 1` (since `t (k+1) ≥ t k + 2 ≥ t k + 1`).
  have hU_step : ∀ k, cert.U (ω (t (k + 1))).1 ≤ cert.U (ω (t k + 1)).1 := by
    intro k
    have h1 : t k + 1 ≤ t (k + 1) := by have := ht_inc k; omega
    exact hU_mono_le (t k + 1) (t (k + 1)) h1
  -- Combining strict drop + monotonicity: U strictly decreases between fair-firing times.
  have hU_strict_step : ∀ k, cert.U (ω (t (k + 1))).1 < cert.U (ω (t k)).1 :=
    fun k => (hU_step k).trans_lt (hU_drop k)
  -- By induction: `U (ω (t k)).1 + k ≤ U (ω (t 0)).1` for all `k`.
  have hU_decay : ∀ k, cert.U (ω (t k)).1 + k ≤ cert.U (ω (t 0)).1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hlt := hU_strict_step k
      omega
  -- But `U (ω (t (M+1))).1 + (M+1) ≤ U (ω (t 0)).1 ≤ M`, hence `M + 1 ≤ M`. Contradiction.
  have h_t0_bdd : cert.U (ω (t 0)).1 ≤ M := hU_bdd _
  have h_decay_M1 := hU_decay (M + 1)
  omega

/-! ### General fair AST via a Borel-Cantelli descent witness

The conditional Borel-Cantelli development should prove the witness
below from the kernel lower bound `U_dec_prob` plus trajectory fair
progress. We keep that analytic step explicit and prove the
certificate-level consequence here.
-/

/-- Running minimum of the certificate's distance variant along a
trace prefix. This is the non-resetting quantity used by the general
Borel-Cantelli argument: non-fair steps may increase `U`, but they
cannot increase the running minimum. -/
def runningMinU (cert : FairASTCertificate spec F terminated)
    (ω : Trace σ ι) : ℕ → ℕ
  | 0 => cert.U (ω 0).1
  | n + 1 => min (runningMinU cert ω n) (cert.U (ω (n + 1)).1)

@[simp] theorem runningMinU_zero
    (cert : FairASTCertificate spec F terminated) (ω : Trace σ ι) :
    runningMinU cert ω 0 = cert.U (ω 0).1 := rfl

@[simp] theorem runningMinU_succ
    (cert : FairASTCertificate spec F terminated) (ω : Trace σ ι) (n : ℕ) :
    runningMinU cert ω (n + 1) =
      min (runningMinU cert ω n) (cert.U (ω (n + 1)).1) := rfl

/-- The running minimum is monotone non-increasing in time. -/
theorem runningMinU_mono
    (cert : FairASTCertificate spec F terminated) (ω : Trace σ ι) :
    ∀ {m n : ℕ}, m ≤ n → runningMinU cert ω n ≤ runningMinU cert ω m := by
  intro m n hmn
  induction hmn with
  | refl => rfl
  | @step n _ ih =>
    calc runningMinU cert ω (n + 1)
        ≤ runningMinU cert ω n := by
          rw [runningMinU_succ]
          exact min_le_left _ _
      _ ≤ runningMinU cert ω m := ih

/-- The running minimum at time `n` is attained by some prefix state. -/
theorem runningMinU_prefix_witness
    (cert : FairASTCertificate spec F terminated) (ω : Trace σ ι) :
    ∀ n : ℕ, ∃ m ≤ n, cert.U (ω m).1 = runningMinU cert ω n := by
  intro n
  induction n with
  | zero =>
    exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
    by_cases hle : runningMinU cert ω n ≤ cert.U (ω (n + 1)).1
    · rcases ih with ⟨m, hm, hm_eq⟩
      refine ⟨m, Nat.le_succ_of_le hm, ?_⟩
      rw [runningMinU_succ, Nat.min_eq_left hle]
      exact hm_eq
    · refine ⟨n + 1, le_rfl, ?_⟩
      have hlt : cert.U (ω (n + 1)).1 < runningMinU cert ω n :=
        Nat.lt_of_not_ge hle
      rw [runningMinU_succ, Nat.min_eq_right (le_of_lt hlt)]

/-- The running minimum at a fixed time is a measurable trace
coordinate functional. -/
theorem measurable_runningMinU
    (cert : FairASTCertificate spec F terminated) (n : ℕ) :
    Measurable (fun ω : Trace σ ι => runningMinU cert ω n) := by
  induction n with
  | zero =>
    exact (measurable_of_countable cert.U).comp
      (measurable_fst.comp (measurable_pi_apply 0))
  | succ n ih =>
    simpa [runningMinU_succ] using ih.min
      ((measurable_of_countable cert.U).comp
        (measurable_fst.comp (measurable_pi_apply (n + 1))))

/-- A step lowers the running minimum. This is the event selected by
the Borel-Cantelli argument, rather than merely lowering the current
`U` value. -/
def RunningMinDropAt (cert : FairASTCertificate spec F terminated)
    (ω : Trace σ ι) (n : ℕ) : Prop :=
  cert.U (ω (n + 1)).1 < runningMinU cert ω n

/-- A fair firing lowers the running minimum. -/
def FairRunningMinDropAt (F : FairnessAssumptions σ ι)
    (cert : FairASTCertificate spec F terminated) (ω : Trace σ ι) (n : ℕ) :
    Prop :=
  FairFiresAt F ω n ∧ RunningMinDropAt cert ω n

/-- Fixed-time running-minimum drop events are measurable. -/
theorem measurableSet_runningMinDropAt
    (cert : FairASTCertificate spec F terminated) (n : ℕ) :
    MeasurableSet {ω : Trace σ ι | RunningMinDropAt cert ω n} := by
  unfold RunningMinDropAt
  exact measurableSet_lt
    ((measurable_of_countable cert.U).comp
      (measurable_fst.comp (measurable_pi_apply (n + 1))))
    (measurable_runningMinU cert n)

/-- Fixed-time fair running-minimum drop events are measurable. -/
theorem measurableSet_fairRunningMinDropAt
    (cert : FairASTCertificate spec F terminated) (n : ℕ) :
    MeasurableSet {ω : Trace σ ι | FairRunningMinDropAt F cert ω n} := by
  unfold FairRunningMinDropAt
  exact (measurableSet_fairFiresAt F n).inter
    (measurableSet_runningMinDropAt cert n)

/-- The event "fair running-minimum drops happen infinitely often" is
measurable. This is the limsup-style event targeted by the
conditional Borel-Cantelli bridge. -/
theorem measurableSet_fairRunningMinDropIO
    (cert : FairASTCertificate spec F terminated) :
    MeasurableSet
      {ω : Trace σ ι | ∀ K : ℕ, ∃ n ≥ K, FairRunningMinDropAt F cert ω n} := by
  classical
  let E : ℕ → Set (Trace σ ι) := fun n =>
    {ω | FairRunningMinDropAt F cert ω n}
  have hE : ∀ n, MeasurableSet (E n) := fun n =>
    measurableSet_fairRunningMinDropAt (F := F) cert n
  have hrepr :
      {ω : Trace σ ι | ∀ K : ℕ, ∃ n ≥ K, FairRunningMinDropAt F cert ω n} =
        ⋂ K : ℕ, ⋃ n : ℕ, {ω : Trace σ ι | K ≤ n ∧ ω ∈ E n} := by
    ext ω
    simp [E]
  rw [hrepr]
  exact MeasurableSet.iInter fun K =>
    MeasurableSet.iUnion fun n =>
      if hKn : K ≤ n then by
        simpa [hKn, E] using hE n
      else by
        have hempty : {ω : Trace σ ι | K ≤ n ∧ ω ∈ E n} = ∅ := by
          ext ω
          simp [hKn]
        rw [hempty]
        exact MeasurableSet.empty

/-- The stopping-time-indexed running-minimum drop event at the
`k`-th fair-firing selector is measurable. -/
def StoppingTimeRunningMinDropAt (F : FairnessAssumptions σ ι)
    (cert : FairASTCertificate spec F terminated) (ω : Trace σ ι) (k : ℕ) :
    Prop :=
  RunningMinDropAt cert ω (fairFiringTime F ω k)

/-- The stopping-time-indexed *fair* running-minimum drop event at the
`k`-th fair-firing selector is measurable. -/
def StoppingTimeFairRunningMinDropAt (F : FairnessAssumptions σ ι)
    (cert : FairASTCertificate spec F terminated) (ω : Trace σ ι) (k : ℕ) :
    Prop :=
  FairRunningMinDropAt F cert ω (fairFiringTime F ω k)

/-- The stopping-time-indexed running-minimum drop event is measurable. -/
theorem measurableSet_stoppingTimeRunningMinDropAt
    (cert : FairASTCertificate spec F terminated) (k : ℕ) :
    MeasurableSet {ω : Trace σ ι | StoppingTimeRunningMinDropAt F cert ω k} := by
  classical
  have hrepr :
      {ω : Trace σ ι | StoppingTimeRunningMinDropAt F cert ω k} =
        ⋃ m : ℕ, {ω : Trace σ ι |
          fairFiringTime F ω k = m ∧ RunningMinDropAt cert ω m} := by
    ext ω
    simp [StoppingTimeRunningMinDropAt]
  rw [hrepr]
  exact MeasurableSet.iUnion fun m =>
    (measurableSet_fairFiringTime_eq F k m).inter
      (measurableSet_runningMinDropAt cert m)

/-- The stopping-time-indexed fair running-minimum drop event is
measurable. -/
theorem measurableSet_stoppingTimeFairRunningMinDropAt
    (cert : FairASTCertificate spec F terminated) (k : ℕ) :
    MeasurableSet {ω : Trace σ ι | StoppingTimeFairRunningMinDropAt F cert ω k} := by
  classical
  have hrepr :
      {ω : Trace σ ι | StoppingTimeFairRunningMinDropAt F cert ω k} =
        ⋃ m : ℕ, {ω : Trace σ ι |
          fairFiringTime F ω k = m ∧ FairRunningMinDropAt F cert ω m} := by
    ext ω
    simp [StoppingTimeFairRunningMinDropAt]
  rw [hrepr]
  exact MeasurableSet.iUnion fun m =>
    (measurableSet_fairFiringTime_eq F k m).inter
      (measurableSet_fairRunningMinDropAt (F := F) cert m)

/-- The stopping-time-indexed fair running-minimum drop event happens
infinitely often as a measurable limsup-style set. -/
theorem measurableSet_stoppingTimeFairRunningMinDropIO
    (cert : FairASTCertificate spec F terminated) :
    MeasurableSet
      {ω : Trace σ ι |
        ∀ K : ℕ, ∃ n ≥ K, StoppingTimeFairRunningMinDropAt F cert ω n} := by
  classical
  let E : ℕ → Set (Trace σ ι) := fun n =>
    {ω | StoppingTimeFairRunningMinDropAt F cert ω n}
  have hE : ∀ n, MeasurableSet (E n) := fun n =>
    measurableSet_stoppingTimeFairRunningMinDropAt (F := F) cert n
  have hrepr :
      {ω : Trace σ ι | ∀ K : ℕ, ∃ n ≥ K, StoppingTimeFairRunningMinDropAt F cert ω n} =
        ⋂ K : ℕ, ⋃ n : ℕ, {ω : Trace σ ι | K ≤ n ∧ ω ∈ E n} := by
    ext ω
    simp [E]
  rw [hrepr]
  exact MeasurableSet.iInter fun K =>
    MeasurableSet.iUnion fun n =>
      if hKn : K ≤ n then by
        simpa [hKn, E] using hE n
      else by
        have hempty : {ω : Trace σ ι | K ≤ n ∧ ω ∈ E n} = ∅ := by
          ext ω
          simp [hKn]
        rw [hempty]
        exact MeasurableSet.empty

/-- Generic countable-fiber lower bound for a measurable selector.

If each fiber `{x | T x = m}` has at least `p`-fraction of its mass
inside the fiberwise event `E m`, then the union over all fibers has at
least `p`-fraction of total mass. This is the measure-theoretic
reduction used by the stopping-time kernel theorem. -/
theorem measure_selector_fiber_lower_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (T : α → ℕ) (hT : Measurable T)
    (E : ℕ → Set α) (hE : ∀ m, MeasurableSet (E m))
    (p : ENNReal)
    (h_step : ∀ m, p * μ {x : α | T x = m} ≤ μ ({x : α | T x = m} ∩ E m)) :
    p * μ Set.univ ≤ μ {x : α | ∃ m : ℕ, T x = m ∧ x ∈ E m} := by
  have hfib_meas : ∀ m : ℕ, MeasurableSet {x : α | T x = m} := by
    intro m
    have hsing : MeasurableSet ({m} : Set ℕ) := measurableSet_singleton m
    exact MeasurableSet.preimage hsing hT
  have hfib_disj : Pairwise (Function.onFun Disjoint fun m : ℕ => {x : α | T x = m}) := by
    intro m1 m2 hneq
    change Disjoint {x : α | T x = m1} {x : α | T x = m2}
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact hneq (hx1.symm.trans hx2)
  have h_union : (⋃ m : ℕ, {x : α | T x = m}) = Set.univ := by
    ext x
    simp
  have hsum_fib : μ Set.univ = ∑' m : ℕ, μ {x : α | T x = m} := by
    rw [← h_union]
    exact measure_iUnion hfib_disj hfib_meas
  have hfibE_meas : ∀ m : ℕ, MeasurableSet ({x : α | T x = m} ∩ E m) := by
    intro m
    exact (hfib_meas m).inter (hE m)
  have hfibE_disj : Pairwise (Function.onFun Disjoint fun m : ℕ => ({x : α | T x = m} ∩ E m)) := by
    intro m1 m2 hneq
    change Disjoint ({x : α | T x = m1} ∩ E m1) ({x : α | T x = m2} ∩ E m2)
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact hneq (hx1.1.symm.trans hx2.1)
  have h_unionE : μ {x : α | ∃ m : ℕ, T x = m ∧ x ∈ E m} =
      ∑' m : ℕ, μ ({x : α | T x = m} ∩ E m) := by
    have hset : {x : α | ∃ m : ℕ, T x = m ∧ x ∈ E m} = ⋃ m : ℕ, ({x : α | T x = m} ∩ E m) := by
      ext x
      simp
    rw [hset]
    exact measure_iUnion hfibE_disj hfibE_meas
  calc
    p * μ Set.univ = p * ∑' m : ℕ, μ {x : α | T x = m} := by rw [hsum_fib]
    _ = ∑' m : ℕ, p * μ {x : α | T x = m} := by rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' m : ℕ, μ ({x : α | T x = m} ∩ E m) := by exact ENNReal.tsum_le_tsum h_step
    _ = μ {x : α | ∃ m : ℕ, T x = m ∧ x ∈ E m} := by rw [h_unionE]

/-- Trace-specialized fiber lower bound.

This is the theorem shape the stopping-time kernel proof will
instantiate once the per-selector fiber bound is available. It simply
packages `measure_selector_fiber_lower_bound` for the trace measure. -/
theorem traceDist_selector_fiber_lower_bound
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {spec : ProbActionSpec σ ι}
    (A : Adversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (T : Trace σ ι → ℕ) (hT : Measurable T)
    (E : ℕ → Set (Trace σ ι)) (hE : ∀ m, MeasurableSet (E m))
    (p : ENNReal)
    (h_step : ∀ m, p * (traceDist spec A μ₀) {ω : Trace σ ι | T ω = m} ≤
        (traceDist spec A μ₀) ({ω : Trace σ ι | T ω = m} ∩ E m)) :
    p * (traceDist spec A μ₀) Set.univ ≤
      (traceDist spec A μ₀) {ω : Trace σ ι | ∃ m : ℕ, T ω = m ∧ ω ∈ E m} := by
  simpa using
    measure_selector_fiber_lower_bound (μ := traceDist spec A μ₀) T hT E hE p h_step

/-- A `RunningMinDropAt` event strictly decreases the running minimum
at the successor time. -/
theorem runningMinU_succ_lt_of_drop
    (cert : FairASTCertificate spec F terminated) (ω : Trace σ ι) (n : ℕ)
    (hdrop : RunningMinDropAt cert ω n) :
    runningMinU cert ω (n + 1) < runningMinU cert ω n := by
  unfold RunningMinDropAt at hdrop
  rw [runningMinU_succ, Nat.min_eq_right (le_of_lt hdrop)]
  exact hdrop

/-- Infinitely many running-minimum drops imply arbitrarily large
finite descents below the initial running minimum. -/
theorem runningMinU_descent_of_drop_io
    (cert : FairASTCertificate spec F terminated) (ω : Trace σ ι)
    (hio : ∀ K : ℕ, ∃ n ≥ K, RunningMinDropAt cert ω n) :
    ∀ k : ℕ, ∃ n : ℕ,
      runningMinU cert ω n + k ≤ cert.U (ω 0).1 := by
  classical
  let pick : ℕ → ℕ := fun K => Classical.choose (hio K)
  have hpick_ge : ∀ K, K ≤ pick K := fun K =>
    (Classical.choose_spec (hio K)).1
  have hpick_drop : ∀ K, RunningMinDropAt cert ω (pick K) := fun K =>
    (Classical.choose_spec (hio K)).2
  let t : ℕ → ℕ := Nat.rec 0 (fun _ prev => pick prev + 1)
  have ht_succ : ∀ k, t (k + 1) = pick (t k) + 1 := fun _ => rfl
  have hdecay : ∀ k : ℕ,
      runningMinU cert ω (t k) + k ≤ runningMinU cert ω 0 := by
    intro k
    induction k with
    | zero =>
      simp [t]
    | succ k ih =>
      have hmono : runningMinU cert ω (pick (t k)) ≤ runningMinU cert ω (t k) :=
        runningMinU_mono cert ω (hpick_ge (t k))
      have hdrop : runningMinU cert ω (pick (t k) + 1) <
          runningMinU cert ω (pick (t k)) :=
        runningMinU_succ_lt_of_drop cert ω (pick (t k)) (hpick_drop (t k))
      rw [ht_succ k]
      omega
  intro k
  refine ⟨t k, ?_⟩
  simpa using hdecay k

/-- Post-Borel-Cantelli running-minimum descent witness for a fixed
`V` sublevel. This is the direct output expected from a conditional
Borel-Cantelli theorem applied to new-minimum drop events. -/
def TrajectoryRunningMinDescent (spec : ProbActionSpec σ ι)
    (F : FairnessAssumptions σ ι)
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (A : FairAdversary σ ι F) (N : ℕ) : Prop :=
  ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
    (∀ n : ℕ, cert.V (ω n).1 ≤ (N : ℝ≥0)) →
      (∀ n : ℕ, ¬ terminated (ω n).1) →
        ∀ k : ℕ, ∃ n : ℕ,
          runningMinU cert ω n + k ≤ cert.U (ω 0).1

/-- Conditional-Borel-Cantelli target event: fair firings lower the
running minimum infinitely often on bad traces in a fixed sublevel. -/
def TrajectoryFairRunningMinDropIO (spec : ProbActionSpec σ ι)
    (F : FairnessAssumptions σ ι)
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (A : FairAdversary σ ι F) (N : ℕ) : Prop :=
  ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
    (∀ n : ℕ, cert.V (ω n).1 ≤ (N : ℝ≥0)) →
      (∀ n : ℕ, ¬ terminated (ω n).1) →
        ∀ K : ℕ, ∃ n ≥ K, FairRunningMinDropAt F cert ω n

/-- Infinitely many fair running-minimum drops give the
running-minimum descent witness. This is the purely trajectory-level
tail of the Borel-Cantelli proof. -/
theorem TrajectoryFairRunningMinDropIO.toRunningMinDescent
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (A : FairAdversary σ ι F) (N : ℕ) :
    TrajectoryFairRunningMinDropIO spec F cert μ₀ A N →
      TrajectoryRunningMinDescent spec F cert μ₀ A N := by
  intro hio
  unfold TrajectoryFairRunningMinDropIO at hio
  unfold TrajectoryRunningMinDescent
  filter_upwards [hio] with ω hω hV hne k
  exact runningMinU_descent_of_drop_io cert ω (fun K => by
    rcases hω hV hne K with ⟨n, hn_ge, _hfair, hdrop⟩
    exact ⟨n, hn_ge, hdrop⟩) k

/-- Post-Borel-Cantelli descent witness for a fixed `V` sublevel.

On any trace that remains in the `V ≤ N` sublevel and never
terminates, arbitrarily large finite descents below the initial
`U`-value occur. This is the natural-number contradiction yielded by
the running-minimum form of conditional Borel-Cantelli. -/
def TrajectoryBCDescent (spec : ProbActionSpec σ ι)
    (F : FairnessAssumptions σ ι)
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (A : FairAdversary σ ι F) (N : ℕ) : Prop :=
  ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
    (∀ n : ℕ, cert.V (ω n).1 ≤ (N : ℝ≥0)) →
      (∀ n : ℕ, ¬ terminated (ω n).1) →
        ∀ k : ℕ, ∃ n : ℕ, cert.U (ω n).1 + k ≤ cert.U (ω 0).1

/-- A running-minimum descent witness implies the simpler
`TrajectoryBCDescent` witness by choosing a prefix state attaining
the running minimum. -/
theorem TrajectoryRunningMinDescent.toBCDescent
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (A : FairAdversary σ ι F) (N : ℕ) :
    TrajectoryRunningMinDescent spec F cert μ₀ A N →
      TrajectoryBCDescent spec F cert μ₀ A N := by
  intro hmin
  unfold TrajectoryRunningMinDescent at hmin
  unfold TrajectoryBCDescent
  filter_upwards [hmin] with ω hω hV hne k
  rcases hω hV hne k with ⟨n, hn⟩
  rcases runningMinU_prefix_witness cert ω n with ⟨m, _hm_le, hm_eq⟩
  refine ⟨m, ?_⟩
  simpa [hm_eq] using hn

/-- Infinitely many fair running-minimum drops imply the
`TrajectoryBCDescent` witness consumed by the fair sublevel rule. -/
theorem TrajectoryFairRunningMinDropIO.toBCDescent
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (A : FairAdversary σ ι F) (N : ℕ) :
    TrajectoryFairRunningMinDropIO spec F cert μ₀ A N →
      TrajectoryBCDescent spec F cert μ₀ A N := by
  intro hio
  exact TrajectoryRunningMinDescent.toBCDescent cert μ₀ A N
    (TrajectoryFairRunningMinDropIO.toRunningMinDescent cert μ₀ A N hio)

/-- General fair sublevel rule from a post-Borel-Cantelli descent
witness.

The missing analytic theorem should establish `TrajectoryBCDescent`
from the stochastic lower-bound obligations. Once that witness is
available, termination follows by the same bounded-variant
contradiction used in the monotone specialization. -/
theorem pi_n_AST_fair_with_progress_bc
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : FairAdversary σ ι F)
    (N : ℕ)
    (h_bc : TrajectoryBCDescent spec F cert μ₀ A N) :
    ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
      (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) → ∃ n, terminated (ω n).1 := by
  obtain ⟨M, hM⟩ := cert.U_bdd_subl (N : ℝ≥0)
  have hbox_inv : AlmostBox spec A.toAdversary μ₀ cert.Inv :=
    AlmostBox_of_inductive cert.Inv
      (fun i s h hInv s' hs' => cert.inv_step i s h hInv s' hs')
      μ₀ h_init_inv A.toAdversary
  unfold AlmostBox at hbox_inv
  unfold TrajectoryBCDescent at h_bc
  filter_upwards [hbox_inv, h_bc] with ω hInv_all hDescent hVbnd
  by_contra hne
  push_neg at hne
  have hU0_bdd : cert.U (ω 0).1 ≤ M := hM _ (hInv_all 0) (hVbnd 0)
  obtain ⟨n, hn⟩ := hDescent hVbnd hne (M + 1)
  have hn' : M + 1 ≤ cert.U (ω 0).1 := by omega
  omega

/-- General fair sublevel rule from the Borel-Cantelli target event:
fair firings lower the running minimum infinitely often on bad traces
in the fixed `V` sublevel. -/
theorem pi_n_AST_fair_with_progress_bc_of_running_min_drops
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : FairAdversary σ ι F)
    (N : ℕ)
    (h_drop_io : TrajectoryFairRunningMinDropIO spec F cert μ₀ A N) :
    ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
      (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) → ∃ n, terminated (ω n).1 :=
  pi_n_AST_fair_with_progress_bc cert μ₀ h_init_inv A N
    (TrajectoryFairRunningMinDropIO.toBCDescent cert μ₀ A N h_drop_io)

/-- **Fair sublevel finite-variant rule with explicit trajectory
progress witness — Borel-Cantelli form.**

Same shape as `pi_n_AST_fair` but takes a `TrajectoryFairProgress`
hypothesis explicitly *plus* a `TrajectoryFairRunningMinDropIO`
witness packaging the conditional Borel-Cantelli output (fair
running-minimum drops happen i.o. on bad traces).

This is the **post-Borel-Cantelli** form of the fair sublevel rule:
the analytic content (deriving the running-minimum-drop-IO event
from `cert.U_dec_prob` plus trajectory fair progress via
conditional Borel-Cantelli) is delegated to the call site. The
deterministic specialisation `pi_n_AST_fair_with_progress_det` covers
all concrete protocols (Bracha, AVSS, common-coin) that satisfy
`U`-monotonicity along trajectories; this general form is a strict
generalisation needed when the per-step decrease is genuinely
probabilistic (e.g., common-coin protocols where the local
randomness can resample `U` on fair firings).

**Internal note:** the previous `pi_n_AST_fair_with_progress` used a
chain-witness packaging (`pi_n_AST_fair_chain_witness`) that has
been retired in favor of this clearer running-minimum-drop bridge
(see `docs/randomized-leslie-spike/13-fair-ast-borel-cantelli-plan.md`).
The remaining analytic obligation — to derive
`TrajectoryFairRunningMinDropIO` from the certificate fields and the
trajectory fair-progress witness — is documented as items 1–3 of the
plan's Remaining section. Concrete protocols can either close that
obligation per-protocol or use the deterministic specialisation. -/
theorem pi_n_AST_fair_with_progress
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : FairAdversary σ ι F)
    (_h_progress : TrajectoryFairProgress spec F μ₀ A)
    (N : ℕ)
    (h_drop_io : TrajectoryFairRunningMinDropIO spec F cert μ₀ A N) :
    ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
      (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) → ∃ n, terminated (ω n).1 :=
  pi_n_AST_fair_with_progress_bc_of_running_min_drops cert μ₀
    h_init_inv A N h_drop_io

/-- Fair sublevel finite-variant rule with explicit trajectory
progress and monotone-variant witnesses.

This is the sound monotone specialization of the fair rule: `U` is
non-increasing along all trajectory steps, and strictly decreases on
fair-required firings while non-terminated in the current `V` sublevel. -/
theorem pi_n_AST_fair (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : FairAdversary σ ι F)
    (h_progress : TrajectoryFairProgress spec F μ₀ A)
    (N : ℕ)
    (h_U_mono : TrajectoryUMono spec F cert μ₀ A)
    (h_U_strict : TrajectoryFairStrictDecrease spec F cert μ₀ A N) :
    ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
      (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) → ∃ n, terminated (ω n).1 :=
  pi_n_AST_fair_with_progress_det cert μ₀ h_init_inv A h_progress N
    h_U_mono h_U_strict

/-- **Step 2 — exceptional set `Π_∞` is null (fair version).**
With `V_init_bdd` giving a uniform bound `K` on the invariant set
and the inductive preservation of `Inv` along trajectories, every
trajectory in the support of `traceDist` satisfies `V (ω n).1 ≤ K`
for all `n`.

Proof: lift `Inv` via `AlmostBox_of_inductive`, then bound `V`
trajectorywise by `⌈K⌉₊`. -/
theorem pi_infty_zero_fair (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : FairAdversary σ ι F) :
    (traceDist spec A.toAdversary μ₀)
      {ω | ∀ N : ℕ, ¬ (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0))} = 0 := by
  -- Extract the uniform `V`-bound `K` on the invariant set.
  obtain ⟨K, hK⟩ := cert.V_init_bdd
  -- Lift `cert.Inv` along trajectories via `AlmostBox_of_inductive`.
  have hbox_inv : AlmostBox spec A.toAdversary μ₀ cert.Inv :=
    AlmostBox_of_inductive cert.Inv
      (fun i s h hInv s' hs' => cert.inv_step i s h hInv s' hs')
      μ₀ h_init_inv A.toAdversary
  -- Convert AE-Inv to AE-bound on V using the uniform K.
  have : ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
      ¬ (∀ N : ℕ, ¬ (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0))) := by
    unfold AlmostBox at hbox_inv
    filter_upwards [hbox_inv] with ω hInv_all
    push_neg
    refine ⟨⌈(K : ℝ≥0)⌉₊, fun n => ?_⟩
    have h1 : cert.V (ω n).1 ≤ K := hK _ (hInv_all n)
    have h2 : (K : ℝ≥0) ≤ ((⌈(K : ℝ≥0)⌉₊ : ℕ) : ℝ≥0) := by
      have : (K : ℝ) ≤ (⌈(K : ℝ≥0)⌉₊ : ℝ) := Nat.le_ceil (K : ℝ≥0)
      exact_mod_cast this
    exact h1.trans h2
  -- Convert AE to measure-zero.
  rw [MeasureTheory.ae_iff] at this
  -- The set under `this` simplifies via `not_not` to the target set.
  have hset : {a : Trace σ ι | ¬ ¬ ∀ N : ℕ, ¬ ∀ n, cert.V (a n).1 ≤ (N : ℝ≥0)} =
      {ω : Trace σ ι | ∀ N : ℕ, ¬ ∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)} := by
    ext ω; simp
  rw [hset] at this
  exact this

/-- **Step 3 — partition argument (fair version).** Combine
`pi_n_AST_fair` (AST on each sublevel) with `pi_infty_zero_fair`
(unbounded set is null) to conclude AST overall.

Proof: countable-union AE swap (`MeasureTheory.ae_iUnion_iff`)
plus the bounded-vs-unbounded partition. -/
theorem partition_almostDiamond_fair
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : FairAdversary σ ι F)
    (h_progress : TrajectoryFairProgress spec F μ₀ A)
    (h_U_mono : TrajectoryUMono spec F cert μ₀ A)
    (h_U_strict : ∀ N : ℕ,
      TrajectoryFairStrictDecrease spec F cert μ₀ A N) :
    AlmostDiamond spec A.toAdversary μ₀ terminated := by
  unfold AlmostDiamond
  have hbounded_or_unbounded :
      ∀ ω : Trace σ ι,
        (∃ N : ℕ, ∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) ∨
        (∀ N : ℕ, ¬ (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0))) := by
    intro ω
    by_cases h : ∃ N : ℕ, ∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)
    · exact .inl h
    · refine .inr ?_
      intro N hbnd
      exact h ⟨N, hbnd⟩
  have h_inf_null : ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
      ¬ (∀ N : ℕ, ¬ (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0))) := by
    rw [ae_iff]
    have heq : {a : Trace σ ι | ¬ ¬ ∀ N : ℕ, ¬ (∀ n, cert.V (a n).1 ≤ (N : ℝ≥0))} =
        {ω : Trace σ ι | ∀ N : ℕ, ¬ (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0))} := by
      ext ω
      simp
    rw [heq]
    exact pi_infty_zero_fair cert μ₀ h_init_inv A
  have h_each_N : ∀ N : ℕ, ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
      (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) → ∃ n, terminated (ω n).1 :=
    fun N => pi_n_AST_fair cert μ₀ h_init_inv A h_progress N
      h_U_mono (h_U_strict N)
  rw [← MeasureTheory.ae_all_iff] at h_each_N
  filter_upwards [h_each_N, h_inf_null] with ω hN h_inf
  rcases hbounded_or_unbounded ω with ⟨N, hbnd⟩ | hunb
  · exact hN N hbnd
  · exact absurd hunb h_inf

/-- Fair AST certificate soundness under trajectory-fair progress and
monotone variant witnesses. This theorem is axiom-clean: it uses the
closed deterministic finite-descent specialization rather than the
open conditional Borel-Cantelli chain witness. -/
theorem sound (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : FairAdversary σ ι F)
    (h_progress : TrajectoryFairProgress spec F μ₀ A)
    (h_U_mono : TrajectoryUMono spec F cert μ₀ A)
    (h_U_strict : ∀ N : ℕ,
      TrajectoryFairStrictDecrease spec F cert μ₀ A N) :
    AlmostDiamond spec A.toAdversary μ₀ terminated :=
  partition_almostDiamond_fair cert μ₀ h_init_inv A h_progress
    h_U_mono h_U_strict

end FairASTCertificate

/-! ### `TrajectoryFairAdversary` — bundle progress witness with the adversary

Resolution path **1c** of the gap-1 finding (see
`docs/randomized-leslie-spike/11-fair-progress-blocker.md`):
`FairnessAssumptions.isWeaklyFair : Adversary → Prop` is opaque, so
the trajectory-form fairness witness cannot be derived from
`A.fair`. Instead of refactoring `FairnessAssumptions` (option 1a)
or threading a progress hypothesis through every caller (option
1b), we bundle the witness with the adversary in a subtype.

Concrete protocols construct a `TrajectoryFairAdversary` by
providing both the fair adversary AND a `TrajectoryFairProgress`
witness. The witness is parametric in the initial measure `μ₀` —
fairness on a specific run, not for all measures uniformly.

The corollary `pi_n_AST_fair_traj_det` shows the soundness path
for protocols satisfying the deterministic specialisation:
`TrajectoryFairAdversary` + `TrajectoryUMono` +
`TrajectoryFairStrictDecrease` ⟹ AS termination. -/

/-- A fair adversary bundled with a trajectory-progress witness for
a specific initial measure `μ₀`.

`progress` is the AE-trajectory statement that fair-required
actions fire i.o. — exactly the trajectory-form predicate the
soundness proof needs but `FairAdversary.fair` doesn't provide. -/
structure TrajectoryFairAdversary
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (spec : ProbActionSpec σ ι) (F : FairnessAssumptions σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] where
  /-- The underlying fair adversary. -/
  toFair : FairAdversary σ ι F
  /-- AE-trajectory progress: every fair-required action fires
  infinitely often along almost every trace. -/
  progress : FairASTCertificate.TrajectoryFairProgress spec F μ₀ toFair

namespace TrajectoryFairAdversary

variable [Countable σ] [Countable ι]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {spec : ProbActionSpec σ ι} {F : FairnessAssumptions σ ι}
  {μ₀ : Measure σ} [IsProbabilityMeasure μ₀]

/-- Project a `TrajectoryFairAdversary` to its underlying
plain `Adversary`. -/
def toAdversary (A : TrajectoryFairAdversary spec F μ₀) :
    Adversary σ ι :=
  A.toFair.toAdversary

end TrajectoryFairAdversary

/-! ### `sound_traj_det` deferred

A consumer-friendly `FairASTCertificate.sound_traj_det` corollary
that takes a `TrajectoryFairAdversary` and discharges termination
via `pi_n_AST_fair_with_progress_det` is the natural next step. It
encountered a `whnf` heartbeat-blowup during elaboration of its
signature (specifically the `A.toFair` projection composing with
`TrajectoryUMono` / `TrajectoryFairStrictDecrease`'s implicit args).
The proof body is straightforward (mirrors
`partition_almostDiamond_fair`); deferred to the next polish pass
once the elaboration cost is identified.

Concrete protocols can already use `pi_n_AST_fair_with_progress_det`
directly with `A.toFair` and `A.progress` — the structure provides
the bundle, the corollary just packages the call. -/

end Leslie.Prob
