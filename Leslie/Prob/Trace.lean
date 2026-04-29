/-
M2 W1 — `Trace`: types + Ionescu-Tulcea trace measure.

Per design plan v2.2 §"`ProbActionSpec` and trace distributions":
trace distributions are `Measure (Π n : ℕ, σ × Option ι)` via
`ProbabilityTheory.Kernel.trajMeasure` (Ionescu-Tulcea kernel
trajectory). Validated by the M0.1 spike (`Spike/CoinFlip.lean`).

This file:

  * Defines the trace type `Trace σ ι := Π n : ℕ, σ × Option ι`.
  * Defines a finite-prefix type alias used as the input to the
    per-step kernel.
  * Defines the per-step Markov kernel `stepKernel` and the
    trace measure `traceDist`, both **sorry-free**.

**M2 W1 polish status.** The per-step kernel currently realises
the *stutter branch* of the conceptual definition (`Dirac` at
`(currentState, none)` regardless of schedule/gate). This is a
deliberate, mathematically valid simplification: it delivers the
correct *type* (a Markov kernel and hence a probability measure
on `Trace σ ι` via `Kernel.trajMeasure`), so downstream M2 W2
(`Refinement.lean`) and M2 W3 (`BrachaRBC.lean`) can be stated
and typechecked against it.

The schedule-conditional and PMF-effect branches of the kernel
are deferred to a follow-up session. The technical blocker is
that `MeasurableSpace (Option ι) := ⊤` (declared locally below)
makes every *set* in `Option ι` measurable but does *not*
automatically make every *function into* `Option ι` measurable.
Closing that gap requires either an explicit measurability
hypothesis on `A.schedule`, a typeclass refinement on `ι`/`σ`
that forces it, or a custom σ-algebra on the adversary history
type. See the long comment above `stepKernel` for the full
checklist. The M0.1 design document (§"Outstanding questions"
item 5) anticipated this might be automatic; it isn't.

Per implementation plan v2.2 §M2 W1.
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

/-! ## Per-step kernel (`stepKernel`)

`stepKernel spec A n` is the per-step Markov kernel from the
finite trace prefix at time `n` to the next `(σ × Option ι)` pair.

Conceptually we want it to branch on `A.schedule h.toList`:

```
match A.schedule h.toList with
| none   => Dirac (currentState h, none)
| some i =>
    if (spec.actions i).gate (currentState h)
    then ((spec.actions i).effect ...).toMeasure.map (·, some i)
    else Dirac (currentState h, none)
```

Discharging measurability of this match expression in full
generality requires a *measurability hypothesis* on
`A.schedule` of the form
`Measurable (fun h : FinPrefix σ ι n ↦ A.schedule h.toList)`,
which is **not** automatic from the standalone instances on
`σ`, `ι`, and `Option ι` alone — codomain ⊤ on `Option ι`
makes every preimage trivially `MeasurableSet`, but the
preimage in `FinPrefix σ ι n` (Pi-product σ-algebra) is *not*
automatically measurable for an arbitrary `A.schedule`. The
M0.1 design document anticipated this might be automatic
(§"Outstanding questions for the prototype" item 5); it is
not, in fact.

For the M2 W1 *polish* milestone the goal is to deliver a
sorry-free, well-typed, measure-theoretically valid `traceDist`
that downstream `Refinement.lean` and `BrachaRBC.lean` can be
stated against. We adopt the simplest realisation that meets
that bar: **stutter at every step**. This is the `none`-branch
of the conceptual definition above, applied unconditionally.

Concretely:

```
stepKernel spec A n := Kernel.deterministic
    (fun h ↦ (h.currentState, none))
    (by measurability)
```

The resulting `traceDist spec A μ₀` is the law of the
stuttering trajectory `(s₀, none), (s₀, none), …` where
`s₀ ∼ μ₀`. It is a probability measure (so `Refinement` and
liveness statements typecheck), but it does *not* yet reflect
the adversary or the spec's effect distributions.

Closing the schedule branch (and hence delivering the
"interesting" `traceDist`) is an M2 W2 follow-up. The required
ingredients are:

  * Either an extra `Measurable`-hypothesis on the schedule
    threaded through `traceDist`'s signature, or
  * A typeclass refinement (e.g. `MeasurableSpace ι := ⊤`
    plus `MeasurableSingletonClass σ` plus `Countable ι`)
    that makes `fun h ↦ A.schedule h.toList` automatically
    measurable, or
  * A bespoke `MeasurableSpace` instance on the adversary's
    history list-domain that's compatible with `toList`.

The choice is a small design call to be made when the
downstream lemmas (`Refines.refl`, `BrachaRBC` totality) need
the *non-stuttering* trace measure; documented at length here
so the next session has a concrete checklist. -/

/-- The current state of a finite-prefix history is a measurable
function of the history (a coordinate projection composed with
`Prod.fst`). -/
@[fun_prop]
theorem FinPrefix.measurable_currentState {σ ι : Type*}
    [MeasurableSpace σ] [MeasurableSpace ι] {n : ℕ} :
    Measurable (FinPrefix.currentState (σ := σ) (ι := ι) (n := n)) := by
  unfold FinPrefix.currentState
  fun_prop

/-- The per-step Markov kernel of a `ProbActionSpec`/`Adversary`
pair. **M2 W1 polish realisation: stutter at every step.** See
the file's "Per-step kernel" section above for why this falls
short of the conceptual definition and what's required to
close the gap. -/
noncomputable def stepKernel {σ ι : Type*}
    [MeasurableSpace σ] [MeasurableSpace ι]
    (_spec : ProbActionSpec σ ι) (_A : Adversary σ ι) (n : ℕ) :
    Kernel (FinPrefix σ ι n) (σ × Option ι) :=
  Kernel.deterministic
    (fun h ↦ (h.currentState, (none : Option ι)))
    (by
      refine Measurable.prod ?_ ?_
      · exact FinPrefix.measurable_currentState
      · exact measurable_const)

/-- The per-step kernel is a Markov kernel (Dirac measures are
probability measures). -/
instance instIsMarkovKernel_stepKernel {σ ι : Type*}
    [MeasurableSpace σ] [MeasurableSpace ι]
    (spec : ProbActionSpec σ ι) (A : Adversary σ ι) (n : ℕ) :
    IsMarkovKernel (stepKernel spec A n) := by
  unfold stepKernel; infer_instance

/-! ## Trace measure (`traceDist`)

`traceDist spec A μ₀` is the measure on infinite traces
obtained by lifting `μ₀` to `σ × Option ι` (pairing with `none`)
and feeding the result, together with `stepKernel spec A`, to
`Kernel.trajMeasure`. We deliberately do *not* require
`[IsProbabilityMeasure μ₀]` here: the construction makes sense
for any initial measure, and the `IsProbabilityMeasure` instance
below recovers the probability-measure status when `μ₀` is one.

This signature is invariant under the M2 W2 callers in
`Refinement.lean`: `Refines` quantifies over `μ₀` with an
`IsProbabilityMeasure μ₀` proposition (not an instance), then
uses `traceDist` directly. -/

/-- The trace measure under `spec`, `A`, and initial state
distribution `μ₀`.

**M2 W1 polish realisation.** Per the file's "Per-step kernel"
section: the per-step kernel is stutter-only, so this measure
is the law of `(s₀, none), (s₀, none), …` for `s₀ ∼ μ₀`. The
shape is correct (probability measure on `Trace σ ι` when
`μ₀` is, ready for `Refinement.lean` to be stated against);
the schedule and effect branches of the kernel are M2 W2
follow-up. -/
noncomputable def traceDist {σ ι : Type*}
    [MeasurableSpace σ] [MeasurableSpace ι]
    (spec : ProbActionSpec σ ι) (A : Adversary σ ι)
    (μ₀ : Measure σ) :
    Measure (Trace σ ι) :=
  let μ₀_full : Measure (σ × Option ι) :=
    μ₀.map (fun s ↦ (s, (none : Option ι)))
  Kernel.trajMeasure μ₀_full (stepKernel spec A)

/-- The trace measure is a probability measure when `μ₀` is. -/
instance instIsProbabilityMeasure_traceDist {σ ι : Type*}
    [MeasurableSpace σ] [MeasurableSpace ι]
    (spec : ProbActionSpec σ ι) (A : Adversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] :
    IsProbabilityMeasure (traceDist spec A μ₀) := by
  unfold traceDist
  -- The lift `μ₀.map (·, none)` is a probability measure since the
  -- pairing function is measurable; `Kernel.trajMeasure` then
  -- yields a probability measure since each `stepKernel` is Markov.
  have : IsProbabilityMeasure
      (μ₀.map (fun s : σ ↦ (s, (none : Option ι)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  infer_instance

end Leslie.Prob
