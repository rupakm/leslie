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

The certificate's correctness is captured by `ASTCertificate.sound`:
a `traceDist`-AE statement asserting that `terminated` eventually
holds. The fields encode the proof obligations the rule requires.

**Status (entry gate):** field types pinned; proofs of internal
lemmas and `sound` are sorry'd. The shape is verified to compile
against `Examples/Prob/AVSSStub.lean`. -/
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

/-! ### Soundness — proof skeleton

The POPL 2025 §3 Lemma 3.2 soundness proof decomposes into four
named steps. We expose each step as its own intermediate result
(`pi_n_AST`, `pi_infty_zero`, `partition_almostDiamond`); each
carries one clearly-scoped Mathlib-side gap that landing closes
`sound` mechanically via `partition_almostDiamond`. -/

/-- Coordinate-`n` lift of the certificate's likelihood
supermartingale `cert.V` to the trace measure: `Vₙ ω = cert.V (ω n).1`.

This is the per-coordinate process that the supermartingale
machinery (`MeasureTheory.Supermartingale`) acts on. The
supermartingale property under `traceDist spec A μ₀` follows from
`cert.V_super` plus the joint-marginal recurrence already used in
`Refinement.AlmostBox_of_pure_inductive`. -/
noncomputable def liftV (cert : ASTCertificate spec terminated)
    (n : ℕ) (ω : Trace σ ι) : ℝ≥0 :=
  cert.V ((ω n).1)

/-- Coordinate-`n` lift of the certificate's distance variant
`cert.U` to the trace measure: `Uₙ ω = cert.U (ω n).1`. -/
def liftU (cert : ASTCertificate spec terminated) (n : ℕ)
    (ω : Trace σ ι) : ℕ :=
  cert.U ((ω n).1)

/-- **Step 1 — sublevel set `Π_n`.** On the sublevel set
`{ω | ∀ k, cert.V (ω k).1 ≤ N}`, almost-sure termination follows
from `U_bdd_subl` plus the standard probabilistic finite-variant
rule (POPL 2025 §3 Rule 3.1).

Formally: with `U_bdd_subl N = M`, the variant `liftU` is
uniformly bounded by `M` along the prefix; with `U_dec_prob N = p`,
each step decreases `U` with probability ≥ `p`. The variant
strictly decreases at most `M` times before forcing termination,
so the geometric tail bound gives AST.

**Status:** `sorry`. Two gaps stand between this and a closed proof:

1. **Statement-level**: as written, the theorem is technically *false*
   under the demonic adversary that always stutters
   (`A.schedule _ = none` everywhere). On such a trace the state is
   constant, so `V (ω n).1 = V (ω 0).1` for all `n`, making the
   hypothesis `∀ n, V (ω n).1 ≤ N` vacuously true for any
   `N ≥ V (ω 0).1`, while termination need not hold. The fix is a
   `cert`-level "non-stuttering" / progress field (e.g., a fairness
   constraint on the adversary, or a `Inv s → ¬terminated s →
   ∃ i, (spec.actions i).gate s` field) — but adding it requires
   amending `ASTCertificate`, which is outside the M3 W2 budget and
   needs design discussion.

2. **Mathlib-level**: even with the missing field, the assembly is
   the standard finite-variant rule (positive-probability decrease
   + bounded variant ⇒ AS termination). Mathlib provides the
   geometric-tail / Borel–Cantelli ingredients
   (`MeasureTheory.measure_eq_zero_of_summable_indicator`,
   `ENNReal.tsum_geometric_lt_top`, etc.) but the assembly into a
   positive-probability-decrease + bounded-variant AST conclusion
   is not packaged. ~250 LOC of filtration plumbing.

Tracked under M3 W3. Concrete protocols satisfy a deterministic-
decrease specialisation that closes via the simpler step-counting
argument; this can be added as a separate lemma `pi_n_AST_det` once
the statement-level field is added. -/
theorem pi_n_AST (cert : ASTCertificate spec terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : Adversary σ ι) (N : ℕ) :
    ∀ᵐ ω ∂(traceDist spec A μ₀),
      (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) → ∃ n, terminated (ω n).1 := by
  sorry

/-- **Step 2 — exceptional set `Π_∞` is null.** With `V_init_bdd`
giving a uniform bound `K` on the invariant set, plus the inductive
preservation of `Inv` along trajectories (from `inv_step`), every
trajectory in the support of `traceDist` satisfies `V (ω n).1 ≤ K`
for all `n`. So the "unbounded" set `{ω | ∀ N, ¬ (∀ n, V ≤ N)}` is
contained in the negation of "∃ N, ∀ n, V ≤ N", which the bound
makes empty modulo the AE-`Inv` hypothesis.

The proof reduces `Π_∞` to a `traceDist`-measure-zero set via the
inductive invariant lift (an `AlmostBox`-style argument that's
exactly the calling pattern of `Refinement.AlmostBox_of_pure_inductive`,
modulo specializing `P` to `Inv s ∧ V s ≤ K`).

**Status:** closed (M3 W2). Uses
`Refinement.AlmostBox_of_inductive` (non-pure-effect generalisation
of `AlmostBox_of_pure_inductive`) to lift `cert.Inv` along
trajectories, then combines with `cert.V_init_bdd` to bound `V`
trajectorywise by `⌈K⌉₊` for the witness `K`. The Doob-convergence
path is no longer needed thanks to `V_init_bdd`. -/
theorem pi_infty_zero (cert : ASTCertificate spec terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : Adversary σ ι) :
    (traceDist spec A μ₀)
      {ω | ∀ N : ℕ, ¬ (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0))} = 0 := by
  -- Extract the uniform `V`-bound `K` on the invariant set.
  obtain ⟨K, hK⟩ := cert.V_init_bdd
  -- Lift `cert.Inv` along trajectories via `AlmostBox_of_inductive`.
  have hbox_inv : AlmostBox spec A μ₀ cert.Inv :=
    AlmostBox_of_inductive cert.Inv
      (fun i s h hInv s' hs' => cert.inv_step i s h hInv s' hs')
      μ₀ h_init_inv A
  -- Goal: `traceDist .. {ω | ∀ N, ¬ (∀ n, V (ω n).1 ≤ N)} = 0`.
  -- Equivalent to: `∀ᵐ ω, ¬ (∀ N, ¬ (∀ n, V ≤ N))`.
  have : ∀ᵐ ω ∂(traceDist spec A μ₀),
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
  -- Now `this : traceDist .. {ω | ¬ ¬ (∀ N, ¬ ..)} = 0`.
  -- The set under `this` simplifies via `not_not` to the target set.
  have hset : {a : Trace σ ι | ¬ ¬ ∀ N : ℕ, ¬ ∀ n, cert.V (a n).1 ≤ (N : ℝ≥0)} =
      {ω : Trace σ ι | ∀ N : ℕ, ¬ ∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)} := by
    ext ω; simp
  rw [hset] at this
  exact this

/-- **Step 3 — partition argument.** Combine `pi_n_AST` (AST on
each sublevel `Π_n`) with `pi_infty_zero` (the unbounded set is
null) to conclude AST overall.

This is the assembly step: the trajectory space partitions as
`(⋃ N, {ω | ∀ n, V (ω n).1 ≤ N}) ∪ Π_∞`, and AST holds on each
`{ω | ∀ n, V ≤ N}` (by `pi_n_AST`) and on the null set `Π_∞`
trivially. Hence AST holds AE.

The proof is countable-union AE swap (`MeasureTheory.ae_iUnion_iff`)
plus the partitioning identity. -/
theorem partition_almostDiamond (cert : ASTCertificate spec terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : Adversary σ ι) :
    AlmostDiamond spec A μ₀ terminated := by
  -- Combine the partition: every ω is either bounded by some N or in Π_∞.
  -- On bounded ω (sublevel `Π_N`), `pi_n_AST` gives AST.
  -- On unbounded ω (`Π_∞`), the measure is zero by `pi_infty_zero`.
  -- The union of countably many AE-events is still AE.
  unfold AlmostDiamond
  -- Use the trichotomy: either ∃ N, ∀ n, V (ω n).1 ≤ N, or ∀ N, ¬(...).
  -- Filter upwards through `pi_infty_zero` to discard the unbounded set,
  -- then through `pi_n_AST` over each `N : ℕ` to handle bounded ω.
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
  -- The unbounded set has measure zero.
  have h_inf_null : ∀ᵐ ω ∂(traceDist spec A μ₀),
      ¬ (∀ N : ℕ, ¬ (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0))) := by
    rw [ae_iff]
    have heq : {a : Trace σ ι | ¬ ¬ ∀ N : ℕ, ¬ (∀ n, cert.V (a n).1 ≤ (N : ℝ≥0))} =
        {ω : Trace σ ι | ∀ N : ℕ, ¬ (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0))} := by
      ext ω
      simp
    rw [heq]
    exact pi_infty_zero cert μ₀ h_init_inv A
  -- For each N, AST holds on the sublevel.
  have h_each_N : ∀ N : ℕ, ∀ᵐ ω ∂(traceDist spec A μ₀),
      (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) → ∃ n, terminated (ω n).1 :=
    fun N => pi_n_AST cert μ₀ h_init_inv A N
  -- Combine via countable AE swap.
  rw [← MeasureTheory.ae_all_iff] at h_each_N
  filter_upwards [h_each_N, h_inf_null] with ω hN h_inf
  rcases hbounded_or_unbounded ω with ⟨N, hbnd⟩ | hunb
  · exact hN N hbnd
  · exact absurd hunb h_inf

/-- AST certificate soundness: under a demonic adversary, every
execution AE terminates.

**Status (M3 W2):** reduced to a single sorry'd lemma —
`pi_n_AST` (sublevel-set finite-variant rule). The companion
`pi_infty_zero` is now closed, using the non-pure-effect
generalisation `Refinement.AlmostBox_of_inductive` to lift
`cert.Inv` along trajectories and combining with `cert.V_init_bdd`
to bound `V` trajectorywise (Doob convergence is no longer needed).
The top-level partition argument (`partition_almostDiamond`) closes
without sorry once `pi_n_AST` lands. See `pi_n_AST`'s docstring for
the two outstanding gaps (statement-level non-stuttering field +
Mathlib-level filtration plumbing). -/
theorem sound (cert : ASTCertificate spec terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : Adversary σ ι) :
    AlmostDiamond spec A μ₀ terminated :=
  partition_almostDiamond cert μ₀ h_init_inv A

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

The fair POPL 2026 soundness proof decomposes along the same
`pi_n_AST` / `pi_infty_zero` / `partition_almostDiamond` skeleton
as the demonic case. The key structural improvement: the
fair-side `pi_n_AST_fair` does **not** suffer the stuttering-
adversary issue that blocks demonic `pi_n_AST`. The
`isWeaklyFair` predicate on `FairAdversary _ F` rules out the
"always-stutter" trace (which would starve every fair-required
action), so the sublevel-set finite-variant rule applies cleanly
on AE traces.

Two of the three pieces close from existing infrastructure:

  * `pi_infty_zero_fair` — closed via `AlmostBox_of_inductive`
    + `V_init_bdd`, exactly as in the demonic case.
  * `partition_almostDiamond_fair` — closed by the partition
    argument once `pi_n_AST_fair` is provided.
  * `pi_n_AST_fair` — *blocks on Mathlib filtration plumbing*
    (Borel–Cantelli + positive-probability-decrease assembly).
    Sorry'd with documented gap. -/

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

/-- **Step 1 — sublevel set `Π_n` (fair version).** On the
sublevel set `{ω | ∀ k, cert.V (ω k).1 ≤ N}`, almost-sure
termination follows from `U_bdd_subl` plus the fair finite-variant
rule.

Unlike the demonic counterpart `ASTCertificate.pi_n_AST`, this
fair version does **not** suffer the stuttering-adversary issue:
`A : FairAdversary σ ι F` carries the weakly-fair witness
`A.fair : F.isWeaklyFair A.toAdversary`, which forces every
fair-required action to fire eventually whenever continuously
enabled. So the `always-stutter` adversary that breaks
demonic `pi_n_AST` is excluded by the type signature.

**Status:** `sorry`. The sole remaining gap is the Mathlib-level
assembly of "positive-probability decrease + bounded variant ⇒
AS termination" — same gap as `ASTCertificate.pi_n_AST`.

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

Tracked under M3 W3+. The Mathlib gap is shared with
`ASTCertificate.pi_n_AST`; closing one closes the other modulo the
fair-action filtering.

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
theorem pi_n_AST_fair (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : FairAdversary σ ι F) (N : ℕ) :
    ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
      (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) → ∃ n, terminated (ω n).1 := by
  sorry

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
    (_cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (A : FairAdversary σ ι F) : Prop :=
  ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
    ∀ N : ℕ, ∃ n ≥ N, ∃ i ∈ F.fair_actions, (ω (n + 1)).2 = some i

/-- **Step 1 — sublevel set `Π_n` (fair version), with explicit
trajectory progress.**

Same shape as `pi_n_AST_fair` but takes a `TrajectoryFairProgress`
hypothesis explicitly. This isolates gap 1 (trajectory-level
fairness witness, opaque from `isWeaklyFair`) from gap 2 (Mathlib
Borel-Cantelli + filtration plumbing).

**Status:** still `sorry` — gap 2 (Mathlib) remains. But this
parameterized form is the right shape for downstream callers once
gap 2 closes: any concrete protocol that supplies a
`TrajectoryFairProgress` witness gets termination via this lemma. -/
theorem pi_n_AST_fair_with_progress
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : FairAdversary σ ι F)
    (_h_progress : TrajectoryFairProgress spec F cert μ₀ A)
    (N : ℕ) :
    ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
      (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) → ∃ n, terminated (ω n).1 := by
  sorry

/-- **Step 2 — exceptional set `Π_∞` is null (fair version).**
With `V_init_bdd` giving a uniform bound `K` on the invariant set
and the inductive preservation of `Inv` along trajectories, every
trajectory in the support of `traceDist` satisfies `V (ω n).1 ≤ K`
for all `n`.

Proof is identical to `ASTCertificate.pi_infty_zero`: lift `Inv`
via `AlmostBox_of_inductive`, then bound `V` trajectorywise by
`⌈K⌉₊`. -/
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

Proof structure mirrors `ASTCertificate.partition_almostDiamond`. -/
theorem partition_almostDiamond_fair
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : FairAdversary σ ι F) :
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
    fun N => pi_n_AST_fair cert μ₀ h_init_inv A N
  rw [← MeasureTheory.ae_all_iff] at h_each_N
  filter_upwards [h_each_N, h_inf_null] with ω hN h_inf
  rcases hbounded_or_unbounded ω with ⟨N, hbnd⟩ | hunb
  · exact hN N hbnd
  · exact absurd hunb h_inf

/-- Fair AST certificate soundness: under a weakly-fair adversary,
every execution AE terminates.

**Status (M3 W3):** reduced to a single sorry'd lemma —
`pi_n_AST_fair` (sublevel-set fair-finite-variant rule). The
companion `pi_infty_zero_fair` is closed via
`Refinement.AlmostBox_of_inductive` + `cert.V_init_bdd`; the
partition argument `partition_almostDiamond_fair` closes without
sorry once `pi_n_AST_fair` lands.

Unlike the demonic counterpart `ASTCertificate.sound` (whose
`pi_n_AST` is blocked on a *statement-level* stuttering-adversary
issue), the fair version's `pi_n_AST_fair` is only blocked on the
*Mathlib-level* filtration plumbing. The fair adversary's
`isWeaklyFair` predicate rules out the stuttering counterexample. -/
theorem sound (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : FairAdversary σ ι F) :
    AlmostDiamond spec A.toAdversary μ₀ terminated :=
  partition_almostDiamond_fair cert μ₀ h_init_inv A

end FairASTCertificate

end Leslie.Prob
