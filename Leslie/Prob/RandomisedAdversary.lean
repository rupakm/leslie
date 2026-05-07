/-
M3 Phase 9.1 — `RandomisedAdversary`: type + mixture trace measure.

Closes the foundation half of caveat **C5** (MODEL_NOTES §11.5):
existing theorems universally quantify over deterministic
`Adversary σ ι`, but the literature-standard threat model is a
randomised (coin-flipping) adversary. This file introduces the
randomised type and the corresponding mixture trace measure; the
lifting meta-theorems that translate deterministic-adversary
theorems to randomised-adversary theorems land in PR 9.2.

Design choices:

  * **Per-step PMF schedule.** A randomised adversary is a function
    `History → PMF (Option ι)` rather than `History → Option ι`. The
    PMF form is the same shape used everywhere else in the framework
    (see `Leslie.Prob.PMF`, `Leslie.Prob.Action`); it sidesteps the
    need to thread a `Kernel`-with-measurability witness around.

  * **Mixture trace measure via the existing per-step kernel.** The
    new per-step PMF `randomisedStepPMF` reuses the same gate-and-
    stutter dispatch as `stepKernel`'s match-body: sample an action
    label `α : Option ι` from `R.strategy h.toList`, then dispatch
    on `α` exactly as the deterministic kernel does. The trace
    measure then plugs into `Kernel.trajMeasure` identically to
    `traceDist`. This means `randomisedTraceDist spec A.toRandomised
    μ₀ = traceDist spec A μ₀` reduces to a `PMF.pure_bind` rewrite
    plus `PMF.toMeasure_pure` / `PMF.toMeasure_map`.

Per implementation plan v2.2 §M3 + MODEL_NOTES §13.1 (PR 9.1).
-/

import Leslie.Prob.Action
import Leslie.Prob.Adversary
import Leslie.Prob.PMF
import Leslie.Prob.Trace

namespace Leslie.Prob

open MeasureTheory ProbabilityTheory

/-! ## `RandomisedAdversary`

A randomised, history-deterministic, demonic scheduler with a
static corruption set. The schedule is a function from the visible
history to a `PMF` over the next action label; concretely the
strategy can flip coins to decide its move.

Mathematically this is equivalent to "pick a random tape `r` from a
distribution and run a deterministic `Adversary` parameterised by
`r`" by Fubini composition; the per-step PMF form is more uniform
with the rest of the `Leslie.Prob` framework. -/
structure RandomisedAdversary (σ : Type*) (ι : Type*) where
  /-- Randomised schedule: given the visible history, produce a
  distribution over the next action label (or `none` to stutter). -/
  strategy : List (σ × Option ι) → PMF (Option ι)
  /-- Static corruption set, identically to a plain `Adversary`. -/
  corrupt  : Set PartyId

namespace Adversary

variable {σ ι : Type*}

/-- Lift a deterministic `Adversary` to a `RandomisedAdversary` via
a Dirac PMF on each schedule decision. The mixture trace measure of
the lifted adversary equals the deterministic trace measure of the
original (`randomisedTraceDist_toRandomised` below). -/
noncomputable def toRandomised (A : Adversary σ ι) : RandomisedAdversary σ ι where
  strategy := fun h => PMF.pure (A.schedule h)
  corrupt  := A.corrupt

@[simp]
theorem toRandomised_strategy (A : Adversary σ ι)
    (h : List (σ × Option ι)) :
    A.toRandomised.strategy h = PMF.pure (A.schedule h) := rfl

@[simp]
theorem toRandomised_corrupt (A : Adversary σ ι) :
    A.toRandomised.corrupt = A.corrupt := rfl

end Adversary

/-! ## Per-step randomised PMF and kernel -/

section RandomisedStep

variable {σ ι : Type*}

open Classical

/-- Per-step distribution on `(σ × Option ι)` for a randomised
adversary. Sample the next action label `α : Option ι` from
`R.strategy h.toList`; then dispatch on `α` as in `stepKernel`:

  * `none` → stutter at the current state.
  * `some i` with gate-met → push the effect distribution forward
    along `(·, some i)`.
  * `some i` with gate-unmet → stutter. -/
noncomputable def randomisedStepPMF
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    {n : ℕ} (h : FinPrefix σ ι n) : PMF (σ × Option ι) :=
  (R.strategy h.toList).bind fun α =>
    match α with
    | none => PMF.pure (h.currentState, (none : Option ι))
    | some i =>
      if hgate : (spec.actions i).gate h.currentState then
        ((spec.actions i).effect h.currentState hgate).map fun s => (s, some i)
      else PMF.pure (h.currentState, (none : Option ι))

end RandomisedStep

section RandomisedKernel

open Classical

variable {σ ι : Type*}
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Per-step Markov kernel of a `ProbActionSpec` / `RandomisedAdversary`
pair. Lift `randomisedStepPMF` pointwise via `PMF.toMeasure` and
`Kernel.ofFunOfCountable`. -/
noncomputable def randomisedStepKernel
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι) (n : ℕ) :
    Kernel (FinPrefix σ ι n) (σ × Option ι) :=
  Kernel.ofFunOfCountable fun h => (randomisedStepPMF spec R h).toMeasure

instance instIsMarkovKernel_randomisedStepKernel
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι) (n : ℕ) :
    IsMarkovKernel (randomisedStepKernel spec R n) := by
  refine ⟨fun h => ?_⟩
  show IsProbabilityMeasure (randomisedStepPMF spec R h).toMeasure
  infer_instance

/-! ## Mixture trace measure -/

/-- The mixture trace measure of a `ProbActionSpec`,
`RandomisedAdversary`, and initial state distribution `μ₀`.

Defined identically to `traceDist` but with `randomisedStepKernel` in
place of `stepKernel`. Concretely this is the Fubini composition
"sample the strategy at each step, then deterministically dispatch
on the gate" iterated by `Kernel.trajMeasure`. -/
noncomputable def randomisedTraceDist
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (μ₀ : Measure σ) :
    Measure (Trace σ ι) :=
  Kernel.trajMeasure (μ₀.map (fun s ↦ (s, (none : Option ι))))
    (randomisedStepKernel spec R)

instance instIsProbabilityMeasure_randomisedTraceDist
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] :
    IsProbabilityMeasure (randomisedTraceDist spec R μ₀) := by
  unfold randomisedTraceDist
  have : IsProbabilityMeasure
      (μ₀.map (fun s : σ ↦ (s, (none : Option ι)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  infer_instance

/-! ## Sanity: deterministic lift agrees with `traceDist`

For a `RandomisedAdversary` arising from `Adversary.toRandomised`,
each per-step PMF is a `PMF.pure` over the deterministic schedule
choice; the corresponding `toMeasure` collapses to the same Dirac /
pushforward shapes used by `stepKernel`. Hence the per-step kernels
agree, and by `Kernel.trajMeasure` extensionality the mixture trace
measure equals the deterministic trace measure. -/

set_option linter.unusedSectionVars false in
/-- Per-history measure equality for the deterministic lift: each
randomised step PMF on `A.toRandomised` collapses (via
`PMF.pure_bind`) to the same per-history measure that `stepKernel`
produces. The proof case-splits on `A.schedule h.toList` and uses
`PMF.toMeasure_pure` and `PMF.toMeasure_map`.

Most of the surrounding section's typeclass requirements (`Countable`,
`MeasurableSingletonClass`, `MeasurableSpace ι`) are unused at the
PMF-on-`σ` level — only `MeasurableSpace σ` is needed. We silence
the unused-section-vars linter rather than restructure the file. -/
private lemma randomisedStepPMF_toMeasure_toRandomised
    (spec : ProbActionSpec σ ι) (A : Adversary σ ι)
    {n : ℕ} (h : FinPrefix σ ι n) :
    (randomisedStepPMF spec A.toRandomised h).toMeasure =
      (match A.schedule h.toList with
      | none => Measure.dirac (h.currentState, (none : Option ι))
      | some i =>
        if hgate : (spec.actions i).gate h.currentState then
          ((spec.actions i).effect h.currentState hgate).toMeasure.map
            (fun s => (s, some i))
        else Measure.dirac (h.currentState, (none : Option ι))) := by
  unfold randomisedStepPMF
  rw [Adversary.toRandomised_strategy, PMF.pure_bind]
  -- Substitute the schedule choice on both sides via `cases ... with`.
  -- `dsimp only` forces iota-reduction of the resulting `match … with`.
  cases hα : A.schedule h.toList with
  | none =>
    dsimp only
    exact PMF.toMeasure_pure _
  | some i =>
    dsimp only
    -- Split on the gate; both `if`s collapse to the same branch.
    by_cases hgate : (spec.actions i).gate h.currentState
    · rw [dif_pos hgate, dif_pos hgate]
      have hfun : Measurable (fun s : σ => (s, some i)) := by fun_prop
      exact (PMF.toMeasure_map _ _ hfun).symm
    · rw [dif_neg hgate, dif_neg hgate]
      exact PMF.toMeasure_pure _

theorem randomisedStepKernel_toRandomised
    (spec : ProbActionSpec σ ι) (A : Adversary σ ι) (n : ℕ) :
    randomisedStepKernel spec A.toRandomised n = stepKernel spec A n := by
  refine DFunLike.ext _ _ fun h => ?_
  exact randomisedStepPMF_toMeasure_toRandomised spec A h

/-- For an `Adversary` lifted to a `RandomisedAdversary` via
`Adversary.toRandomised`, the mixture trace measure equals the
deterministic trace distribution. -/
theorem randomisedTraceDist_toRandomised
    (spec : ProbActionSpec σ ι) (A : Adversary σ ι) (μ₀ : Measure σ) :
    randomisedTraceDist spec A.toRandomised μ₀ = traceDist spec A μ₀ := by
  -- Both sides reduce to `Kernel.trajMeasure μ₀_full κ` with the same
  -- `μ₀_full`; only the per-step kernel family differs. The two
  -- families agree pointwise (`randomisedStepKernel_toRandomised`),
  -- so by `funext` the families are equal as functions, and the
  -- trajectory measures coincide.
  unfold randomisedTraceDist traceDist
  have hk : randomisedStepKernel spec A.toRandomised = stepKernel spec A :=
    funext (randomisedStepKernel_toRandomised spec A)
  simp only [hk]

end RandomisedKernel

end Leslie.Prob
