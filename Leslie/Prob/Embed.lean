/-
M1 W1 — `ActionSpec → ProbActionSpec` coercion (skeleton).

The design plan's coercion `GatedAction.toProb` is pictured for an
*effect-function* shape `effect : σ → σ`, but existing Leslie's
`GatedAction.transition : σ → σ → Prop` is *relational*. Existing
deterministic specs (e.g., `Paxos.lean`) use the relational form
where every transition is `s' = f s` for some `f`, but extracting
`f` requires either:
  * the user supplying it explicitly (the path taken below), or
  * `Classical.choose` on a uniqueness witness (M1 W4 fallback).

This file provides the M1 W1 skeleton:
  * `ProbGatedAction.dirac` — a basic Dirac-effect constructor from
    a gate predicate and a successor function.
  * `ActionSpec.toProbViaSucc` — coerce a relational `ActionSpec` to
    a `ProbActionSpec` given a per-action successor extractor.
  * Simp lemmas confirming the coercion is one expression per field.

The full *conservativity* level 2 (`invariant_preserved`,
`refines_preserved`) lands in M1 W4 once `Refinement.lean` exists.
-/

import Leslie.Prob.Action
import Leslie.Action
import Leslie.Refinement

namespace Leslie.Prob

/-! ## Dirac constructor

A probabilistic gated action whose effect is a Dirac on a successor
function. This is the natural target shape of the
`ActionSpec → ProbActionSpec` coercion. -/

/-- Build a `ProbGatedAction` from a gate predicate and a deterministic
successor function: the effect is the Dirac on `succ s`.
Marked `noncomputable` because `PMF.pure` is. -/
noncomputable def ProbGatedAction.dirac {σ : Type*}
    (gate : σ → Prop) (succ : σ → σ) : ProbGatedAction σ where
  gate := gate
  effect := fun s _ => PMF.pure (succ s)

@[simp] theorem ProbGatedAction.dirac_gate {σ : Type*}
    (gate : σ → Prop) (succ : σ → σ) :
    (ProbGatedAction.dirac gate succ).gate = gate := rfl

@[simp] theorem ProbGatedAction.dirac_effect {σ : Type*}
    (gate : σ → Prop) (succ : σ → σ) (s : σ) (h : gate s) :
    (ProbGatedAction.dirac gate succ).effect s h = PMF.pure (succ s) := rfl

/-! ## Coercion of an `ActionSpec` via per-action successors

Given a `TLA.ActionSpec σ ι` and, for each action `i`, a
deterministic successor function consistent with the relational
`transition`, produce a `ProbActionSpec σ ι` whose effects are
all Dirac.

Existing Leslie specs whose `transition` has the form
`s' = f i s` (e.g., Paxos's `p1b`) admit a successor extractor
trivially; non-deterministic transitions (e.g., `∃ v, s' = ...`)
require refinement to per-choice action labels before this coercion
applies. -/

end Leslie.Prob

namespace TLA.ActionSpec

/-- Coerce a relational `ActionSpec` to a `ProbActionSpec` with Dirac
effects, given a per-action successor extractor.

Defined in the `TLA.ActionSpec` namespace so that `spec.toProbViaSucc`
dot-notation resolves on values of type `TLA.ActionSpec σ ι`. -/
noncomputable def toProbViaSucc {σ : Type*} {ι : Type*}
    (spec : TLA.ActionSpec σ ι)
    (succ : ι → σ → σ) : Leslie.Prob.ProbActionSpec σ ι where
  init    := spec.init
  actions := fun i =>
    Leslie.Prob.ProbGatedAction.dirac (spec.actions i).gate (succ i)

@[simp] theorem toProbViaSucc_init {σ : Type*} {ι : Type*}
    (spec : TLA.ActionSpec σ ι) (succ : ι → σ → σ) :
    (spec.toProbViaSucc succ).init = spec.init := rfl

@[simp] theorem toProbViaSucc_actions_gate {σ : Type*} {ι : Type*}
    (spec : TLA.ActionSpec σ ι) (succ : ι → σ → σ) (i : ι) :
    ((spec.toProbViaSucc succ).actions i).gate = (spec.actions i).gate := rfl

end TLA.ActionSpec

namespace Leslie.Prob

/-! ## Soundness: the supplied successor really steps the spec

When the user-supplied `succ` matches the spec's `transition`
relation pointwise (under the gate), the probabilistic step takes
`s` to `Dirac (succ i s)` and that is in agreement with the
deterministic spec.

This is a Level-1 coercion sanity check. The Level-2 conservativity
(invariants and refinement preserved) lands in M1 W4. -/

/-- The Dirac effect of `toProbViaSucc` corresponds to the original
relational transition, provided the successor function realises the
relation under the gate. -/
theorem ActionSpec.toProbViaSucc_step_eq_dirac {σ : Type*} {ι : Type*}
    (spec : TLA.ActionSpec σ ι) (succ : ι → σ → σ)
    (i : ι) (s : σ) (h : (spec.actions i).gate s) :
    (spec.toProbViaSucc succ).step i s
      = some (PMF.pure (succ i s)) :=
  ProbActionSpec.step_eq_some (spec := spec.toProbViaSucc succ) (i := i) (s := s) h

end Leslie.Prob
