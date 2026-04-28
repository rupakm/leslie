/-
M1 W2 — `Trace` (single-step skeleton).

Just enough trace machinery for M1's downstream use cases (Shamir
secrecy at M1 W4, where the dealer's share-phase is a single round
from the initial state). The full infinite-trace measure
construction via `Kernel.trajMeasure` (Ionescu-Tulcea) is M2 W1
work; for M1 we only need:

  * The finite-trace type alias.
  * `singleStep` — distribution over one-step traces given an
    initial state and a chosen action.

Per implementation plan v2.2 §M1 W2.
-/

import Leslie.Prob.Action
import Leslie.Prob.Adversary

namespace Leslie.Prob

/-- A finite trace: a list of `(state, optional-action-label)` pairs.
For an infinite trace, see M2 W1's measure-theoretic construction. -/
abbrev Trace (σ ι : Type*) := List (σ × Option ι)

namespace Trace

variable {σ ι : Type*}

/-- Single-step trace distribution: given pre-state `s₀` and an
action label `i`, the distribution over `(post-state, action label)`
pairs after one step. Returns `none` if the action's gate fails. -/
noncomputable def singleStep (spec : ProbActionSpec σ ι) (i : ι) (s₀ : σ) :
    Option (PMF (σ × Option ι)) :=
  match spec.step i s₀ with
  | some μ => some (μ.map fun s' => (s', some i))
  | none   => none

end Trace

end Leslie.Prob
