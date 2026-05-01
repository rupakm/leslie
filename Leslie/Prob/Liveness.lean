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

namespace ASTCertificate

variable [Countable σ] [Countable ι]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {spec : ProbActionSpec σ ι} {terminated : σ → Prop}

/-- AST certificate soundness: under a demonic adversary, every
execution AE terminates.

**Status (entry gate):** `sorry`. Proof structure mirrors POPL 2025
§3 proof of Lemma 3.2:
  1. Partition runs into `Π_n = {sup V ≤ n}` and `Π_∞`.
  2. On each `Π_n`, apply finite-variant rule using `U_bdd_subl` +
     `U_dec_prob`; conclude AST on `Π_n`.
  3. On `Π_∞`, apply Doob's martingale convergence on `V` (via
     `MeasureTheory.Martingale`) to derive `P(Π_∞) = 0`.
  4. Conclude AST overall. -/
theorem sound (cert : ASTCertificate spec terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : Adversary σ ι) :
    AlmostDiamond spec A μ₀ terminated := by
  sorry

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

namespace FairASTCertificate

variable [Countable σ] [Countable ι]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {spec : ProbActionSpec σ ι} {F : FairnessAssumptions σ ι}
  {terminated : σ → Prop}

/-- Fair AST certificate soundness: under a weakly-fair adversary,
every execution AE terminates.

**Status (entry gate):** `sorry`. Proof structure: same as the
demonic case but the supermartingale convergence argument is
restricted to fair sub-traces (Doob applied conditional on
`isWeaklyFair`). -/
theorem sound (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : FairAdversary σ ι F) :
    AlmostDiamond spec A.toAdversary μ₀ terminated := by
  sorry

end FairASTCertificate

end Leslie.Prob
