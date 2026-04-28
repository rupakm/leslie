/-
M1 W1 — `ProbActionSpec`: probabilistic counterpart of `ActionSpec`.

The shape mirrors `Leslie.Action.ActionSpec σ ι` exactly: function-
indexed by `ι`, no per-action parameter. This is the core abstraction
on top of which `Refinement.lean`, `Liveness.lean`, `Coupling.lean`
land in M2–M3.

Vocabulary note: the design plan called the predicate field `guard`;
this file uses `gate` to match existing Leslie's `GatedAction.gate`.
The names are interchangeable in the literature; `gate` keeps the
project consistent.

Design decisions reflected here:

  * `effect` is a *function* `(s : σ) → gate s → PMF σ` — the action
    chosen + the pre-state determines a single distribution over
    next states. Non-determinism in action-choice is handled by the
    `Adversary` (M2 W1); pre-state non-determinism in relations
    (e.g., `∃ v, s' = ...` in deterministic Paxos) requires
    refinement to per-value action labels in the probabilistic
    setting. See M0.1 trace-measure decision document.

  * Single-step semantics in `step` returns `Option (PMF σ)`; `none`
    when the gate fails.

  * `parallel` (basic disjoint-state product) is included for the
    simple case where two `ProbActionSpec`s share no state.
    Distributed protocols with shared networks use the
    `parallelWithNet` shape sketched in M0.2 — that variant lands
    in M2 W1.
-/

import Leslie.Prob.PMF

namespace Leslie.Prob

/-! ## ProbGatedAction -/

/-- A gated probabilistic action over state `σ`.

  * `gate` — the precondition for firing.
  * `effect` — given a pre-state and a proof that the gate holds,
    the distribution over post-states.

Mirror of `Leslie.GatedAction` with the deterministic relation
replaced by a PMF. -/
structure ProbGatedAction (σ : Type*) where
  gate   : σ → Prop
  effect : (s : σ) → gate s → PMF σ

namespace ProbGatedAction

variable {σ : Type*}

/-- The action is enabled at state `s` iff its gate holds (and there
is a — vacuously existing — distribution to step into). -/
def is_enabled (a : ProbGatedAction σ) (s : σ) : Prop := a.gate s

/-- A gated probabilistic action with no precondition (gate trivially
true) and a pre-supplied effect function. -/
def unguarded (e : σ → PMF σ) : ProbGatedAction σ where
  gate := fun _ => True
  effect := fun s _ => e s

end ProbGatedAction

/-! ## ProbActionSpec -/

/-- A probabilistic specification: an initial-state predicate and a
family of gated probabilistic actions indexed by `ι`. -/
structure ProbActionSpec (σ : Type*) (ι : Type*) where
  init    : σ → Prop
  actions : ι → ProbGatedAction σ

namespace ProbActionSpec

variable {σ ι : Type*}

/-! ### Single-step semantics -/

open Classical in
/-- Single-step transition: given the action label `i` chosen by the
scheduler, return the PMF over next states (`none` if the gate
fails). Uses classical case analysis since `gate` is `σ → Prop`
without a decidability witness. -/
noncomputable def step (spec : ProbActionSpec σ ι) (i : ι) (s : σ) : Option (PMF σ) :=
  if h : (spec.actions i).gate s
  then some ((spec.actions i).effect s h)
  else none

@[simp] theorem step_eq_some {spec : ProbActionSpec σ ι} {i : ι} {s : σ}
    (h : (spec.actions i).gate s) :
    spec.step i s = some ((spec.actions i).effect s h) := by
  classical
  unfold step
  rw [dif_pos h]

@[simp] theorem step_eq_none {spec : ProbActionSpec σ ι} {i : ι} {s : σ}
    (h : ¬ (spec.actions i).gate s) :
    spec.step i s = none := by
  classical
  unfold step
  rw [dif_neg h]

/-- The action `i` is enabled at `s` iff its gate holds. -/
def is_enabled (spec : ProbActionSpec σ ι) (i : ι) (s : σ) : Prop :=
  (spec.actions i).gate s

/-! ### Parallel composition (disjoint state — basic case)

The shared-state product (`parallelWithNet`) for distributed protocols
lands in M2 W1; see `Leslie/Prob/Spike/ParallelShape.lean` for the
shape sketch and `docs/randomized-leslie-spike/03-parallel-state.md`
for the design rationale. The version below is the *disjoint-state*
case — two specs that genuinely share nothing. It is mostly
illustrative; real distributed examples use `parallelWithNet`. -/

/-- Disjoint-state parallel composition of two probabilistic specs.
Each step fires exactly one side's action; the other side's local
state stays put (Dirac).

This shape is *not* what distributed protocols use — they share a
network and need `parallelWithNet`. Kept here as the trivial baseline
that demonstrates the structural pattern. -/
noncomputable def parallel
    {σ₁ σ₂ ι₁ ι₂ : Type*}
    (spec₁ : ProbActionSpec σ₁ ι₁) (spec₂ : ProbActionSpec σ₂ ι₂) :
    ProbActionSpec (σ₁ × σ₂) (ι₁ ⊕ ι₂) where
  init := fun s => spec₁.init s.1 ∧ spec₂.init s.2
  actions := fun
    | .inl i₁ =>
      { gate   := fun s => (spec₁.actions i₁).gate s.1
        effect := fun s h =>
          ((spec₁.actions i₁).effect s.1 h).map (fun s₁' => (s₁', s.2)) }
    | .inr i₂ =>
      { gate   := fun s => (spec₂.actions i₂).gate s.2
        effect := fun s h =>
          ((spec₂.actions i₂).effect s.2 h).map (fun s₂' => (s.1, s₂')) }

end ProbActionSpec

end Leslie.Prob
