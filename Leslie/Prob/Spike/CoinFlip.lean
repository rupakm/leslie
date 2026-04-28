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

If this file builds with `(0)` `sorry` on items 1–3 and one planned
`sorry` on item 4 (the marginal lemma; closing it is downstream M3
work), M0.1 prototype phase passes. The AST-certificate scaffolding
lives in `Leslie/Prob/Spike/ASTSanity.lean` (M0.3); this file is
focused purely on the trace-measure construction.

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

/-! ## Scope

The AST-certificate shape was previously stubbed in this file as a
placeholder; it has moved to `Leslie/Prob/Spike/ASTSanity.lean` in its
full POPL 2025 (V, U) form. This file's responsibility is purely the
*trace-measure construction* — `coinKernel`, `coinTrace`, and the
marginal lemma. AST stuff lives next door.
-/

end Leslie.Prob.Spike
