/-
M2 W1 — `Trace`: types + signatures for the Ionescu-Tulcea trace
measure. Actual measure construction deferred to M2 W1 polish.

Per design plan v2.2 §"`ProbActionSpec` and trace distributions":
trace distributions are `Measure (Π n : ℕ, σ × Option ι)` via
`ProbabilityTheory.Kernel.trajMeasure` (Ionescu-Tulcea kernel
trajectory). Validated by the M0.1 spike (`Spike/CoinFlip.lean`).

This file:

  * Defines the trace type `Trace σ ι := Π n : ℕ, σ × Option ι`.
  * Defines a finite-prefix type alias used as the input to the
    per-step kernel.
  * Sketches `stepKernel` and `traceDist` signatures.

What's deferred to a focused M2 W1 polish session:

  * **Measurability witness for `stepKernel`** — requires
    `MeasurableSpace (Option ι)` (not in Mathlib for general `ι`;
    can be added locally as `⊤` for discrete action labels) and
    careful threading through gate-conditional / schedule branches.
  * **`IsMarkovKernel` instance** for `stepKernel` — depends on the
    measurability witness.
  * **Concrete `traceDist`** body (currently `sorry`) — composes
    `Kernel.trajMeasure` with the initial-distribution lift.
  * **`AlmostBox` / `AlmostDiamond` modal predicates** — defined
    against `traceDist`, so depend on its body.

Per implementation plan v2.2 §M2 W1. The signature surface here is
sufficient for M2 W2 (`Refinement.lean`) and M2 W3 (`BrachaRBC.lean`)
to *state* their theorems; they'll discharge `traceDist`-dependent
claims via the deferred body once that lands.
-/

import Leslie.Prob.Action
import Leslie.Prob.Adversary
import Leslie.Prob.PMF
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

namespace Leslie.Prob

open MeasureTheory ProbabilityTheory

/-! ## Local `MeasurableSpace` instance for `Option`

Mathlib does not (as of v4.27.0) provide a `MeasurableSpace (Option α)`
instance. Action labels are typically discrete; we equip `Option ι`
with the maximal σ-algebra (every set is measurable). For continuous
action spaces this would need refinement, but that's not in scope for
M1–M5 (action labels are inductive types throughout). -/

instance instMeasurableSpaceOption {α : Type*} : MeasurableSpace (Option α) := ⊤

/-! ## Trace types

Infinite traces are functions `ℕ → σ × Option ι`. Termination is
encoded as eventual stuttering at a terminal state. -/

/-- An infinite trace: at each step `n`, a pair of (state at step n,
optional action label that fired between step n-1 and n). The 0-th
entry's action component is conventionally `none`. -/
abbrev Trace (σ : Type*) (ι : Type*) := Π _ : ℕ, σ × Option ι

/-- A finite trace prefix of length `n + 1`: the input shape to the
per-step Markov kernel in the Ionescu-Tulcea construction. -/
abbrev FinPrefix (σ : Type*) (ι : Type*) (n : ℕ) :=
  Π _ : Finset.Iic n, σ × Option ι

namespace FinPrefix

variable {σ ι : Type*}

/-- Convert a finite trace prefix to a `List`, in increasing index
order, for feeding to `Adversary.schedule`. -/
def toList {n : ℕ} (h : FinPrefix σ ι n) : List (σ × Option ι) :=
  (List.finRange (n + 1)).map fun k =>
    h ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩

/-- The current state in a finite trace prefix is the last entry's
state component. -/
def currentState {n : ℕ} (h : FinPrefix σ ι n) : σ :=
  (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1

end FinPrefix

/-! ## Trace measure (signature only)

`traceDist` produces the probability measure on infinite traces
under a `ProbActionSpec` and an `Adversary`, starting from an
initial-state distribution. Body is `sorry` for the M2 W1 first
cut — see file header for the deferred-work breakdown. -/

/-- The trace measure under spec, adversary, and initial
distribution. **Signature delivered; body deferred to M2 W1
polish.**

Construction sketch (per M0.1 spike):
```
let stepKernel n : Kernel (FinPrefix σ ι n) (σ × Option ι) :=
  -- branches on adversary's choice and gate
  ...
let μ₀_full : Measure (σ × Option ι) := μ₀.map (·, none)
Kernel.trajMeasure μ₀_full stepKernel
```

The full body requires `MeasurableSpace (Option ι)` (e.g., the
discrete σ-algebra ⊤) and measurability of the conditional kernel,
which is the focused-polish-session work. -/
noncomputable def traceDist {σ ι : Type*}
    [MeasurableSpace σ] [MeasurableSpace ι]
    (_spec : ProbActionSpec σ ι) (_A : Adversary σ ι)
    (_μ₀ : Measure σ) :
    Measure (Trace σ ι) :=
  sorry

end Leslie.Prob
