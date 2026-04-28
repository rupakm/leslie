/-
M0.1 spike — verify Option A (Measure + Ionescu-Tulcea) compiles and
gives a usable trace measure on a trivial example.

This file is part of the M0 spike for the randomized-leslie extension.
It is *not* production code; it lives under `Leslie/Prob/Spike/` to
emphasize that. After the spike closes, this file is either:
  - promoted into `Leslie/Prob/` proper (if the design holds), or
  - deleted and replaced (if a different design is chosen).

Goal of this file:

  1. Construct a coin-flip Markov chain on `Bool` using a constant
     `Kernel` family.
  2. Lift to a `Measure (Π n, Bool)` via `ProbabilityTheory.Kernel.trajMeasure`.
  3. Witness the `IsProbabilityMeasure` instance.
  4. State (and ideally prove) that the marginal at step `n+1` is
     uniform on `Bool`, by reducing to `map_traj_succ_self`.
  5. Stub `ASTCertificate.sound` against this trace-measure type
     (statement-only; body is `sorry` per M0 sorry budget).

If this file builds end-to-end with `(0)` `sorry` on items 1–3 and the
standard sorry budget on items 4–5, M0.1 prototype phase passes.

See `docs/randomized-leslie-spike/01-trace-measure.md` for the
decision rationale and the API references this file relies on.
-/

import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Distributions.Uniform

namespace Leslie.Prob.Spike

open MeasureTheory ProbabilityTheory

/-! ## Coin-flip kernel family

`X : ℕ → Type` is the constant family `fun _ => Bool`. The kernel
`κ n : Kernel (Π i : Iic n, Bool) Bool` is history-independent uniform.
-/

/-- The constant state family — every "coordinate" is `Bool`. -/
abbrev X : ℕ → Type := fun _ => Bool

/-- Uniform distribution on `Bool`, as a `Measure`. -/
noncomputable def uniformBool : Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure uniformBool := by
  unfold uniformBool
  infer_instance

/-- The history-independent uniform-coin kernel family. -/
noncomputable def coinKernel :
    (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)) :=
  fun _ => Kernel.const _ uniformBool

instance (n : ℕ) : IsMarkovKernel (coinKernel n) := by
  unfold coinKernel
  infer_instance

/-! ## Trace measure

`coinTrace μ₀ : Measure (Π n, Bool)` is the distribution over infinite
coin-flip trajectories starting from initial distribution `μ₀`.
-/

/-- Trace measure over `Π n, Bool` from initial distribution `μ₀`. -/
noncomputable def coinTrace (μ₀ : Measure Bool) [IsProbabilityMeasure μ₀] :
    Measure (Π n, X n) :=
  Kernel.trajMeasure μ₀ coinKernel

instance (μ₀ : Measure Bool) [IsProbabilityMeasure μ₀] :
    IsProbabilityMeasure (coinTrace μ₀) := by
  unfold coinTrace
  infer_instance

/-! ## Marginal at step `n + 1` is uniform on Bool

This is the headline correctness fact for the prototype. We use
`map_traj_succ_self` from Mathlib: the (a+1)-th marginal of
`traj κ a` equals `κ a` itself. Since our kernel is constant uniform,
the marginal is uniform.

Statement is given; the proof is left as `sorry` for M0.1 prototype
phase — closing it is M0.3's stuck-soundness sanity check. The
*shape* compiling is what matters here.
-/

/-- For any step `n + 1`, the marginal of the trace measure is uniform
on `Bool`, regardless of the initial distribution. -/
theorem coinTrace_marginal_succ_uniform
    (μ₀ : Measure Bool) [IsProbabilityMeasure μ₀] (n : ℕ) :
    (coinTrace μ₀).map (fun (x : Π n, X n) => x (n + 1)) = uniformBool := by
  sorry

/-! ## AST certificate stub

Statement-only stub of `ASTCertificate` and its soundness, with the
trace type being `Measure (Π n, X n)` instead of v2's invalid
`PMF (Trace σ ι)`. Compiles → M0.3 exit gate's "shape compiles"
condition is met for this trivial example.

The full structure is just enough to type-check the soundness lemma's
quantification; non-trivial fields are placeholders.
-/

/-- Stub almost-sure box: probability-1 set under a measure. -/
def AlmostBox {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (P : α → Prop) : Prop :=
  ∀ᵐ x ∂μ, P x

/-- Stub almost-sure diamond: probability-1 set under a measure.
For the prototype this is the same as `AlmostBox` — what matters is
that the *type* is expressible against `Measure (Π n, X n)`, not the
exact temporal-logic semantics, which lands in M3 W1. -/
def AlmostDiamond {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (P : α → Prop) : Prop :=
  ∀ᵐ x ∂μ, P x

/-- Stub `ASTCertificate` for a trace measure on coin flips. The full
shape (V, U, Inv, sublevel-set compatibility) is deferred to M3 W1;
this stub just confirms the type *shape* is expressible against the
trace-measure type. -/
structure CoinASTCertificate
    (μ₀ : Measure Bool) [IsProbabilityMeasure μ₀]
    (term : (Π n, X n) → Prop) where
  /-- The (V, U, Inv) triple is elided for the prototype. We just
  record the shape: a measurable set of "terminating" trajectories. -/
  measurable_term : Measurable (fun (x : Π n, X n) => term x)

/-- Stub soundness: a `CoinASTCertificate` implies almost-sure
termination under the trace measure. Body is `sorry` per the M0
sorry budget. -/
theorem CoinASTCertificate.sound
    (μ₀ : Measure Bool) [IsProbabilityMeasure μ₀]
    (term : (Π n, X n) → Prop)
    (_ : CoinASTCertificate μ₀ term) :
    AlmostDiamond (coinTrace μ₀) term := by
  sorry

end Leslie.Prob.Spike
