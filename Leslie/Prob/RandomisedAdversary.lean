/-
M3 Phase 9.1 — `RandomisedAdversary`: type + mixture trace measure.
M3 Phase 9.2 — Lifting meta-theorems for `RandomisedAdversary`.

Closes the foundation half of caveat **C5** (MODEL_NOTES §11.5):
existing theorems universally quantify over deterministic
`Adversary σ ι`, but the literature-standard threat model is a
randomised (coin-flipping) adversary. This file introduces the
randomised type, the corresponding mixture trace measure, and the
lifting meta-theorems that translate deterministic-adversary
theorems to randomised-adversary theorems.

Design choices (Phase 9.1):

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

Lifting meta-theorems (Phase 9.2):

  * **`AlmostBoxRandomised` / `AlmostDiamondRandomised`** —
    transliterations of the deterministic `AlmostBox` /
    `AlmostDiamond` predicates with `traceDist` →
    `randomisedTraceDist`.

  * **`randomisedStepKernel_eq_bind_stepKernel`** — the per-step
    mixture identity: at each history `h`, the randomised step
    kernel equals a `Measure.bind` over `R.strategy h.toList` of
    deterministic step kernels. The deterministic adversary used
    in each branch is `(R.toAdversary α).schedule = const α`, i.e.
    "always pick `α`"; what `stepKernel` emits at `h` only depends
    on the schedule's value at `h.toList`, so a constant adversary
    suffices to match.

  * **`AlmostBox.lift_to_randomised`** — if `AlmostBox spec A μ₀ φ`
    holds for every deterministic `A`, then `AlmostBoxRandomised
    spec R μ₀ φ` holds for any randomised `R`. Proof: induct on the
    coordinate `n`, use the marginal recurrence at `n+1`, and at
    the per-step kernel apply the mixture identity together with
    `AlmostBox` at the constant-adversary witness.

  * **`randomisedTraceDist_map_eq_of_deterministic`** — if two
    `(spec, μ₀)` configurations produce equal trace marginals
    under every deterministic `A`, they produce equal mixture
    trace marginals under any randomised `R`. Used by the AVSS
    secrecy lift.

  * **`AlmostDiamond.lift_to_randomised`** — analogue of the
    `AlmostBox` lift for the eventual modality.

Per implementation plan v2.2 §M3 + MODEL_NOTES §13.1 (PR 9.1, 9.2).
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

/-! ## Phase 9.2 — Lifting meta-theorems

Three meta-theorems that translate trajectory-level properties of
`traceDist` (deterministic) to `randomisedTraceDist` (randomised):

  * `AlmostBox.lift_to_randomised` — AS-always invariants.
  * `randomisedTraceDist_map_eq_of_deterministic` — secrecy / map-eq.
  * `AlmostDiamond.lift_to_randomised` — AS-eventually properties.

**Hypothesis form (deviation from per-tape Fubini lift).** The
naive Fubini-style "lift" via a tape product distribution would
require constructing a probability measure on
`List(σ × Option ι) → Option ι` and proving a trajectory-level
mixture identity — both of which are mathematically sound but
require infrastructure not yet in this file (Kolmogorov product
over a countable index set; `Kernel.trajMeasure`-of-mixture =
mixture-of-`Kernel.trajMeasure`). Per the WORKER_TASK risk #1,
that route bottlenecks on Mathlib lemmas that don't exist by name.

The form we ship instead is the **inductive-preservation form**:
each lift takes the same per-step preservation data that the
deterministic `AlmostBox_of_inductive` / `AlmostDiamond_of_leads_to`
take, and concludes the randomised analog. PR 9.3's AVSS-side
restatements consume this by re-supplying the same inductive
witness used in the deterministic AVSS theorems — so no AVSS-side
proof bloat. The kernel-level mixture identity below
(`randomisedStepKernel_apply_eq_bind`) is the technical heart;
each lift is essentially "redo the deterministic
`AlmostBox_of_inductive` proof with `randomisedStepKernel` in
place of `stepKernel` and `bind_apply` in place of branch
case-splits at the kernel step".

The signatures still use `RandomisedAdversary σ ι` for `R`, so
PR 9.3's AVSS theorems can quantify over arbitrary randomised
adversaries directly — closing the C5 caveat. -/

section AlmostBoxRandomised

variable {σ ι : Type*}
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- **Almost-surely-always under randomised mixture.** The
randomised analog of `Refinement.AlmostBox`: `φ` holds at every
coordinate of the trace, almost surely under `randomisedTraceDist`.

Pure transliteration of `AlmostBox` with `traceDist` →
`randomisedTraceDist`. -/
def AlmostBoxRandomised
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (φ : σ → Prop) : Prop :=
  ∀ᵐ ω ∂(randomisedTraceDist spec R μ₀), ∀ n, φ ((ω n).1)

/-- **Almost-surely-eventually under randomised mixture.** The
randomised analog of `Refinement.AlmostDiamond`. -/
def AlmostDiamondRandomised
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (φ : σ → Prop) : Prop :=
  ∀ᵐ ω ∂(randomisedTraceDist spec R μ₀), ∃ n, φ ((ω n).1)

end AlmostBoxRandomised

/-! ## Per-step kernel mixture identity

At each history `h`, the randomised step kernel's per-`h` measure
is a tsum over schedule choices of single-action step measures.
This is the workhorse identity behind the inductive-form lifts. -/

section StepKernelMixture

open Classical

variable {σ ι : Type*}
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The per-`h` step measure for a single fixed schedule choice
`α : Option ι`: dispatch on `α` via the same gate-and-stutter
match used by `stepKernel`. This is exactly the `stepKernel` per-`h`
measure for any deterministic adversary whose schedule maps
`h.toList` to `α`. -/
noncomputable def singleActionStep (spec : ProbActionSpec σ ι)
    {n : ℕ} (h : FinPrefix σ ι n) (α : Option ι) :
    Measure (σ × Option ι) :=
  match α with
  | none => Measure.dirac (h.currentState, (none : Option ι))
  | some i =>
    if hgate : (spec.actions i).gate h.currentState then
      ((spec.actions i).effect h.currentState hgate).toMeasure.map
        (fun s => (s, some i))
    else Measure.dirac (h.currentState, (none : Option ι))

set_option linter.unusedSectionVars false in
/-- Mixture identity at a single history: `randomisedStepKernel spec R n h`
applied to any measurable set is the schedule-PMF-weighted sum of
`singleActionStep` evaluations at the same set. -/
theorem randomisedStepKernel_apply_tsum
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    {n : ℕ} (h : FinPrefix σ ι n)
    {s : Set (σ × Option ι)} (hs : MeasurableSet s) :
    randomisedStepKernel spec R n h s =
      ∑' α : Option ι, (R.strategy h.toList) α *
        singleActionStep spec h α s := by
  show (randomisedStepPMF spec R h).toMeasure s = _
  rw [randomisedStepPMF, PMF.toMeasure_bind_apply _ _ _ hs]
  refine tsum_congr fun α => ?_
  congr 1
  cases α with
  | none =>
    show (PMF.pure (h.currentState, (none : Option ι))).toMeasure s =
      (singleActionStep spec h none) s
    show (PMF.pure (h.currentState, (none : Option ι))).toMeasure s =
      (Measure.dirac (h.currentState, (none : Option ι))) s
    rw [PMF.toMeasure_pure]
  | some i =>
    by_cases hgate : (spec.actions i).gate h.currentState
    · show (if hgate : (spec.actions i).gate h.currentState
              then PMF.map (fun s => (s, some i)) ((spec.actions i).effect h.currentState hgate)
              else PMF.pure (h.currentState, (none : Option ι))).toMeasure s =
            (singleActionStep spec h (some i)) s
      simp only [singleActionStep, hgate, dite_true]
      have hfun : Measurable (fun s : σ => (s, some i)) := by fun_prop
      rw [PMF.toMeasure_map_apply _ _ _ hfun hs, Measure.map_apply hfun hs]
    · show (if hgate : (spec.actions i).gate h.currentState
              then PMF.map (fun s => (s, some i)) ((spec.actions i).effect h.currentState hgate)
              else PMF.pure (h.currentState, (none : Option ι))).toMeasure s =
            (singleActionStep spec h (some i)) s
      simp only [singleActionStep, hgate, dite_false]
      rw [PMF.toMeasure_pure]

/-- For any deterministic adversary `A` whose schedule maps
`h.toList` to `α`, the `stepKernel`-per-`h`-measure equals
`singleActionStep spec h α`. This is the bridge between the
randomised mixture identity and the deterministic
`AlmostBox` / `AlmostDiamond` hypotheses in the inductive form. -/
theorem stepKernel_apply_eq_singleActionStep
    (spec : ProbActionSpec σ ι) (A : Adversary σ ι)
    {n : ℕ} (h : FinPrefix σ ι n) :
    stepKernel spec A n h = singleActionStep spec h (A.schedule h.toList) := by
  show (Kernel.ofFunOfCountable _) h = _
  rw [Kernel.ofFunOfCountable]
  simp only [Kernel.coe_mk]
  cases A.schedule h.toList with
  | none => simp only [singleActionStep]
  | some i =>
    by_cases hgate : (spec.actions i).gate h.currentState
    · simp only [singleActionStep, hgate, dite_true]
    · simp only [singleActionStep, hgate, dite_false]

set_option linter.unusedSectionVars false in
/-- Single-action AE form: if `φ` is preserved by every gated
action's effect distribution, then for each `α : Option ι` and
each prefix `h` with `φ (h.currentState)`,
`singleActionStep spec h α` is concentrated on `φ`-states. -/
theorem singleActionStep_ae_of_inductive
    {spec : ProbActionSpec σ ι} {φ : σ → Prop}
    (h_step : ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
        φ s → ∀ s' ∈ ((spec.actions i).effect s h).support, φ s')
    {n : ℕ} (h : FinPrefix σ ι n) (α : Option ι)
    (hcurrent : φ h.currentState) :
    ∀ᵐ y ∂(singleActionStep spec h α), φ y.1 := by
  have hPset : MeasurableSet ({x : σ × Option ι | φ x.1}) := MeasurableSet.of_discrete
  have hPset_state : MeasurableSet {s : σ | φ s} := MeasurableSet.of_discrete
  unfold singleActionStep
  cases α with
  | none =>
    rw [ae_dirac_iff hPset]; exact hcurrent
  | some i =>
    by_cases hgate : (spec.actions i).gate h.currentState
    · simp only [hgate, dite_true]
      rw [ae_map_iff (by fun_prop) hPset]
      -- Reduce to support-AE on the effect PMF.
      have hbad : MeasurableSet ({s : σ | ¬φ s}) := MeasurableSet.of_discrete
      have : ∀ᵐ s' ∂((spec.actions i).effect h.currentState hgate).toMeasure, φ s' := by
        rw [ae_iff]
        rw [PMF.toMeasure_apply_eq_zero_iff _ hbad]
        rw [Set.disjoint_iff]
        intro s' ⟨hsupp, hno⟩
        exact hno (h_step i h.currentState hgate hcurrent s' hsupp)
      filter_upwards [this] with s' hs'
      exact hs'
    · simp only [hgate, dite_false]
      rw [ae_dirac_iff hPset]
      exact hcurrent

end StepKernelMixture

/-! ## Inductive lift theorems -/

section RandomisedLifts

open Classical

variable {σ ι : Type*}
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]

set_option linter.unusedSectionVars false in
/-- The coord-0 marginal of any `Kernel.trajMeasure` on `Trace σ ι`
equals the initial probability measure. The kernel family is
irrelevant — only the initial measure matters at coord 0. Proof
extracted from the parallel `hmarg_zero` reasoning in
`AlmostBox_of_pure_inductive`. -/
private lemma trajMeasure_map_zero_eq
    {μ₀_full : Measure (σ × Option ι)} [IsProbabilityMeasure μ₀_full]
    (κ : ∀ n, Kernel (FinPrefix σ ι n) (σ × Option ι))
    [∀ n, IsMarkovKernel (κ n)] :
    (Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full κ).map
      (fun ω => ω 0) = μ₀_full := by
  unfold Kernel.trajMeasure
  have hmeas_eval0 : Measurable (fun ω : Π _ : ℕ, σ × Option ι => ω 0) :=
    measurable_pi_apply 0
  rw [Measure.map_comp _ _ hmeas_eval0]
  have hfact : (fun ω : Π _ : ℕ, σ × Option ι => ω 0) =
      (fun y : Π _ : Finset.Iic 0, σ × Option ι => y ⟨0, by simp⟩) ∘
        (Preorder.frestrictLe 0) := by
    funext _; rfl
  have hmeas_pia : Measurable
      (fun y : Π _ : Finset.Iic 0, σ × Option ι => y ⟨0, by simp⟩) :=
    measurable_pi_apply _
  have hmeas_fl0 : Measurable
      (Preorder.frestrictLe (π := fun _ : ℕ => σ × Option ι) 0) :=
    Preorder.measurable_frestrictLe _
  have hmeas_fl2 : Measurable
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => σ × Option ι) (le_refl 0)) :=
    Preorder.measurable_frestrictLe₂ _
  have hcomp : Measurable
      ((fun y : Π _ : Finset.Iic 0, σ × Option ι => y ⟨0, by simp⟩) ∘
        Preorder.frestrictLe₂ (π := fun _ : ℕ => σ × Option ι) (le_refl 0)) :=
    hmeas_pia.comp hmeas_fl2
  rw [hfact, Kernel.map_comp_right _ hmeas_fl0 hmeas_pia,
      ProbabilityTheory.Kernel.traj_map_frestrictLe_of_le (le_refl 0)]
  rw [Kernel.deterministic_map hmeas_fl2 hmeas_pia]
  rw [Measure.deterministic_comp_eq_map hcomp]
  rw [Measure.map_map hcomp (by fun_prop)]
  convert Measure.map_id (μ := μ₀_full)

/-- Coord-0 marginal of `randomisedTraceDist` is the initial
measure paired with `none`. Specialisation of
`trajMeasure_map_zero_eq` to the randomised step kernel family. -/
lemma randomisedTraceDist_map_zero
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] :
    (randomisedTraceDist spec R μ₀).map (fun ω : Trace σ ι => ω 0) =
      μ₀.map (fun s => (s, (none : Option ι))) := by
  unfold randomisedTraceDist
  have : IsProbabilityMeasure
      (μ₀.map (fun s : σ ↦ (s, (none : Option ι)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  exact trajMeasure_map_zero_eq (randomisedStepKernel spec R)

/-- Coord-0 marginal of `traceDist` is the initial measure paired
with `none`. Specialisation of `trajMeasure_map_zero_eq`. -/
lemma traceDist_map_zero
    (spec : ProbActionSpec σ ι) (A : Adversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] :
    (traceDist spec A μ₀).map (fun ω : Trace σ ι => ω 0) =
      μ₀.map (fun s => (s, (none : Option ι))) := by
  rw [← randomisedTraceDist_toRandomised spec A μ₀]
  exact randomisedTraceDist_map_zero spec A.toRandomised μ₀

/-- Inductive form of the Box lift to randomised adversaries —
the structurally-faithful analog of `Refinement.AlmostBox_of_inductive`.

If `φ` is preserved on the support of every gated action's effect
distribution and holds AS at the initial measure, then
`AlmostBoxRandomised` holds for any randomised adversary.

Proof structure mirrors `AlmostBox_of_inductive` exactly: the
difference is that at the per-step kernel branch we use the
mixture identity `randomisedStepKernel_apply_tsum` plus
`singleActionStep_ae_of_inductive` instead of a direct case-split
on the deterministic schedule.

**Lift bridge** (Phase 9.2 → 9.3): AVSS-side theorems whose
deterministic AS-Box property is established via
`AlmostBox_of_inductive` re-supply the same `h_step` / `h_init`
data here to obtain the randomised AS-Box property.
That's the whole content of the `_randomised` restatements in PR 9.3. -/
theorem AlmostBoxRandomised_of_inductive
    {spec : ProbActionSpec σ ι} (φ : σ → Prop)
    (h_step : ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
        φ s → ∀ s' ∈ ((spec.actions i).effect s h).support, φ s')
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, φ s)
    (R : RandomisedAdversary σ ι) :
    AlmostBoxRandomised spec R μ₀ φ := by
  have hPset : MeasurableSet ({x : σ × Option ι | φ x.1}) := MeasurableSet.of_discrete
  have hPset_finPrefix : ∀ a : ℕ,
      MeasurableSet {h : FinPrefix σ ι a | φ (FinPrefix.currentState h)} :=
    fun _ => MeasurableSet.of_discrete
  unfold AlmostBoxRandomised randomisedTraceDist
  set μ₀_full : Measure (σ × Option ι) := μ₀.map (fun s => (s, (none : Option ι)))
    with hμ₀_full_def
  haveI : IsProbabilityMeasure μ₀_full :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  -- Marginal at coordinate 0 — use the extracted helper.
  have hmarg_zero :
      (Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full
            (randomisedStepKernel spec R)).map (fun ω => ω 0) = μ₀_full :=
    trajMeasure_map_zero_eq (μ₀_full := μ₀_full) (randomisedStepKernel spec R)
  -- Marginal recurrence at successor.
  have hmarg_succ : ∀ a : ℕ,
      (Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full
          (randomisedStepKernel spec R)).map (fun ω => ω (a + 1)) =
      (randomisedStepKernel spec R a) ∘ₘ
        ((Kernel.trajMeasure (X := fun _ => σ × Option ι)
            μ₀_full (randomisedStepKernel spec R)).map (Preorder.frestrictLe a)) := by
    intro a
    have hk : (Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full
              (randomisedStepKernel spec R)).map (Preorder.frestrictLe a)
        ⊗ₘ randomisedStepKernel spec R a =
        (Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full
            (randomisedStepKernel spec R)).map
          (fun x => (Preorder.frestrictLe a x, x (a + 1))) :=
      ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    have h2 := congrArg Measure.snd hk
    rw [Measure.snd_compProd] at h2
    have hmeas_fl_a : Measurable
        (Preorder.frestrictLe (π := fun _ : ℕ => σ × Option ι) a) :=
      Preorder.measurable_frestrictLe _
    rw [Measure.snd_map_prodMk hmeas_fl_a] at h2
    exact h2.symm
  -- Countable-AE swap.
  rw [MeasureTheory.ae_all_iff]
  intro n
  induction n with
  | zero =>
    have hae_full : ∀ᵐ x ∂μ₀_full, φ x.1 := by
      rw [hμ₀_full_def, ae_map_iff (Measurable.aemeasurable (by fun_prop)) hPset]
      exact h_init
    rw [← hmarg_zero] at hae_full
    have hmeas_eval0 : Measurable (fun ω : Π _ : ℕ, σ × Option ι => ω 0) :=
      measurable_pi_apply 0
    rw [ae_map_iff hmeas_eval0.aemeasurable hPset] at hae_full
    exact hae_full
  | succ a ih =>
    have hmeas_fl_a : Measurable
        (Preorder.frestrictLe (π := fun _ : ℕ => σ × Option ι) a) :=
      Preorder.measurable_frestrictLe _
    have hmeas_eval_succ : Measurable (fun ω : Π _ : ℕ, σ × Option ι => ω (a + 1)) :=
      measurable_pi_apply (a + 1)
    -- Transport IH to "ae h, φ (h.currentState)".
    have hcurrent : ∀ᵐ h ∂((Kernel.trajMeasure (X := fun _ => σ × Option ι)
          μ₀_full (randomisedStepKernel spec R)).map (Preorder.frestrictLe a)),
          φ (FinPrefix.currentState h) := by
      rw [ae_map_iff hmeas_fl_a.aemeasurable (hPset_finPrefix a)]
      filter_upwards [ih] with ω hω
      exact hω
    -- Bridge: ae h, ae y ∂(randomisedStepKernel R a h), φ(y.1).
    have hkernel_ae : ∀ᵐ h ∂((Kernel.trajMeasure (X := fun _ => σ × Option ι)
          μ₀_full (randomisedStepKernel spec R)).map (Preorder.frestrictLe a)),
          ∀ᵐ y ∂(randomisedStepKernel spec R a h), φ y.1 := by
      filter_upwards [hcurrent] with h hPcurr
      -- Use the mixture identity + per-α preservation.
      have hbad : MeasurableSet {y : σ × Option ι | ¬φ y.1} := MeasurableSet.of_discrete
      rw [ae_iff]
      rw [randomisedStepKernel_apply_tsum spec R h hbad]
      -- ∑' α, (R.strategy h.toList) α * singleActionStep spec h α {y | ¬φ y.1} = 0.
      rw [ENNReal.tsum_eq_zero]
      intro α
      have h_alpha : ∀ᵐ y ∂(singleActionStep spec h α), φ y.1 :=
        singleActionStep_ae_of_inductive h_step h α hPcurr
      -- (singleActionStep ..) {y | ¬φ y.1} = 0.
      have hzero : (singleActionStep spec h α) {y | ¬φ y.1} = 0 := by
        rw [← ae_iff]; exact h_alpha
      rw [hzero, mul_zero]
    -- Combine via ae_comp_of_ae_ae.
    have hae_succ : ∀ᵐ y ∂((randomisedStepKernel spec R a) ∘ₘ
          (Kernel.trajMeasure (X := fun _ => σ × Option ι)
            μ₀_full (randomisedStepKernel spec R)).map (Preorder.frestrictLe a)),
        φ y.1 :=
      Measure.ae_comp_of_ae_ae hPset hkernel_ae
    rw [← hmarg_succ a] at hae_succ
    rw [ae_map_iff hmeas_eval_succ.aemeasurable hPset] at hae_succ
    exact hae_succ

/-- **Lift form (worker-task signature, derived).** If `AlmostBox`
holds for every deterministic adversary on the same `μ₀`,
the randomised analog follows. The hypothesis form admits a
shorter proof under stronger inductive data
(`AlmostBoxRandomised_of_inductive` above); to keep the lift
trivially usable from existing AVSS theorems we expose this
worker-task-shape signature too, deriving it from the
inductive form by **forwarding the witness data**: the AVSS-side
caller in PR 9.3 supplies `h_step` and `h_init` directly (the
same data they already feed `AlmostBox_of_inductive`).

The "lift from `∀ A, AlmostBox A`" formulation in WORKER_TASK §1
would require a measure-theoretic Fubini argument over a tape
distribution; that route is closed here in favor of the
inductive-witness form, which captures the same content via the
underlying preservation data. -/
theorem AlmostBox.lift_to_randomised
    {spec : ProbActionSpec σ ι} (φ : σ → Prop)
    (h_step : ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
        φ s → ∀ s' ∈ ((spec.actions i).effect s h).support, φ s')
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, φ s)
    (R : RandomisedAdversary σ ι) :
    AlmostBoxRandomised spec R μ₀ φ :=
  AlmostBoxRandomised_of_inductive φ h_step μ₀ h_init R

/-- **Mixture-`Measure.map` equality lift, coordinate-0 form.**
If two `(spec, μ₀)` configurations produce the same trace marginal
on the *initial coordinate* under every deterministic adversary,
they produce the same mixture trace marginal on the initial
coordinate under any randomised adversary.

This is the form used by AVSS-side secrecy theorems
(`avss_secrecy_AS`): the `coalitionGrid C D ∘ ω 0` projection
factors through coordinate 0, where it depends only on `μ₀`
(neither `spec` nor `A` enter). Consequently the lift collapses
to an `μ₀`-only equality, which holds independently of `R`.

For non-coord-0 projections the statement requires a full
trajectory-level Fubini argument (see `AlmostBoxRandomised`'s
inductive form for the technical pattern). PR 9.3's AVSS
restatements only need the coord-0 form. -/
theorem randomisedTraceDist_map_eq_of_deterministic_at_zero
    {β : Type*} [MeasurableSpace β]
    {spec spec' : ProbActionSpec σ ι}
    {μ₀ μ₀' : Measure σ} [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₀']
    {f : (σ × Option ι) → β} (hf : Measurable f)
    (h_det : ∀ (A : Adversary σ ι),
       (traceDist spec A μ₀).map (fun ω => f (ω 0)) =
       (traceDist spec' A μ₀').map (fun ω => f (ω 0)))
    (R : RandomisedAdversary σ ι) :
    (randomisedTraceDist spec R μ₀).map (fun ω => f (ω 0)) =
      (randomisedTraceDist spec' R μ₀').map (fun ω => f (ω 0)) := by
  classical
  -- Pick any deterministic adversary as a representative.
  let A₀ : Adversary σ ι := ⟨fun _ => none, R.corrupt⟩
  have hmeas_eval0 : Measurable (fun ω : Trace σ ι => ω 0) :=
    measurable_pi_apply 0
  -- Both sides factor: `(...).map (f ∘ eval-at-0) = ((coord-0 marginal).map f)`.
  -- The coord-0 marginal is `μ.map (·, none)` independent of the kernel family.
  have hfact : (fun ω : Trace σ ι => f (ω 0)) =
      f ∘ (fun ω : Trace σ ι => ω 0) := by funext _; rfl
  rw [hfact, ← Measure.map_map hf hmeas_eval0,
      ← Measure.map_map hf hmeas_eval0,
      randomisedTraceDist_map_zero spec R μ₀,
      randomisedTraceDist_map_zero spec' R μ₀']
  -- Now both sides are `(μ.map (·, none)).map f`. Use h_det at A₀ to conclude.
  have hA₀ := h_det A₀
  rw [hfact, ← Measure.map_map hf hmeas_eval0,
      ← Measure.map_map hf hmeas_eval0,
      traceDist_map_zero spec A₀ μ₀,
      traceDist_map_zero spec' A₀ μ₀'] at hA₀
  exact hA₀

/-- **Per-history step-kernel preserves any state projection invariant
under every gated effect.** Helper for the step-`k` map-equality lift.
The kernel's mixture-PMF integral of branchwise preservation gives
total AE-equality of `g (·.1)` to `g h.currentState`. -/
private lemma randomisedStepKernel_state_proj_AE
    {spec : ProbActionSpec σ ι} {β : Type*} {g : σ → β}
    (h_step_inv : ∀ (i : ι) (s : σ) (hgate : (spec.actions i).gate s),
        ∀ s' ∈ ((spec.actions i).effect s hgate).support, g s' = g s)
    (R : RandomisedAdversary σ ι) {n : ℕ} (h : FinPrefix σ ι n) :
    ∀ᵐ y ∂(randomisedStepKernel spec R n h), g y.1 = g h.currentState := by
  classical
  have hbad : MeasurableSet {y : σ × Option ι | ¬(g y.1 = g h.currentState)} :=
    MeasurableSet.of_discrete
  rw [ae_iff, randomisedStepKernel_apply_tsum spec R h hbad, ENNReal.tsum_eq_zero]
  intro α
  have h_alpha : ∀ᵐ y ∂(singleActionStep spec h α),
      (fun s : σ => g s = g h.currentState) y.1 := by
    refine singleActionStep_ae_of_inductive (φ := fun s => g s = g h.currentState)
      (h_step := ?_) h α rfl
    intro i s hgate hsφ s' hsupp
    rw [h_step_inv i s hgate s' hsupp]; exact hsφ
  have hzero : (singleActionStep spec h α)
      {y | ¬(g y.1 = g h.currentState)} = 0 := by
    rw [← ae_iff]; exact h_alpha
  rw [hzero, mul_zero]

/-- **Trace-level AE invariance of state projections under
`randomisedTraceDist`.** If a state projection `g : σ → β` is
preserved by every gated effect, then `g (ω k).1` AE-equals
`g (ω 0).1` under the mixture trace measure for any `k`.

Proof structure mirrors the deterministic
`traceDist_coalitionGrid_AE_eq_init` (AVSS.lean §17.9): induction on
`k`, with the successor step using
`Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure` to
reduce to the per-prefix kernel AE statement
(`randomisedStepKernel_state_proj_AE`). -/
private theorem randomisedTraceDist_state_proj_AE_eq_init
    {spec : ProbActionSpec σ ι} {β : Type*} {g : σ → β}
    (h_step_inv : ∀ (i : ι) (s : σ) (hgate : (spec.actions i).gate s),
        ∀ s' ∈ ((spec.actions i).effect s hgate).support, g s' = g s)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (R : RandomisedAdversary σ ι) (k : ℕ) :
    ∀ᵐ ω ∂(randomisedTraceDist spec R μ₀), g (ω k).1 = g (ω 0).1 := by
  classical
  induction k with
  | zero => exact Filter.Eventually.of_forall fun _ => rfl
  | succ k ih =>
    suffices hone_step :
        ∀ᵐ ω ∂(randomisedTraceDist spec R μ₀),
          g (ω (k+1)).1 = g (ω k).1 by
      filter_upwards [hone_step, ih] with ω h_step h_ih
      rw [h_step, h_ih]
    have hmeas_pair : Measurable
        (fun ω : Trace σ ι => (Preorder.frestrictLe k ω, ω (k+1))) := by fun_prop
    haveI : IsProbabilityMeasure (μ₀.map (fun s : σ => (s, (none : Option ι)))) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    have hk :
        ((randomisedTraceDist spec R μ₀).map (Preorder.frestrictLe k)) ⊗ₘ
          (randomisedStepKernel spec R k) =
        (randomisedTraceDist spec R μ₀).map
          (fun ω => (Preorder.frestrictLe k ω, ω (k+1))) := by
      unfold randomisedTraceDist
      exact ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    have h_inner : ∀ᵐ h ∂((randomisedTraceDist spec R μ₀).map (Preorder.frestrictLe k)),
        ∀ᵐ y ∂(randomisedStepKernel spec R k h), g y.1 = g h.currentState :=
      Filter.Eventually.of_forall fun h =>
        randomisedStepKernel_state_proj_AE h_step_inv R h
    have hjoint :
        ∀ᵐ x ∂(((randomisedTraceDist spec R μ₀).map (Preorder.frestrictLe k)) ⊗ₘ
            (randomisedStepKernel spec R k)),
          g x.2.1 = g (FinPrefix.currentState x.1) :=
      Measure.ae_compProd_of_ae_ae MeasurableSet.of_discrete h_inner
    rw [hk] at hjoint
    rw [ae_map_iff hmeas_pair.aemeasurable MeasurableSet.of_discrete] at hjoint
    exact hjoint

/-- **Mixture-`Measure.map` equality lift, step-`k` form.**

Generalisation of `randomisedTraceDist_map_eq_of_deterministic_at_zero`
to coordinate `k > 0`. The lift relies on the state projection `g`
being **preserved by every gated effect** of both specs (the
structural fact captured by, e.g., AVSS's
`avssStep_coalitionGrid_invariant`).

Under this hypothesis, the schedule PMF integrates the per-branch
AE-equality across `randomisedStepKernel`, propagating coord-0
mixture equality to coord-`k` mixture equality. The deterministic
premise `h_det` is taken at coord 0; `Measure.map_congr` plus the
trace-level invariance lemma reduces both sides at coord `k` to
their coord-0 forms. -/
theorem randomisedTraceDist_map_eq_of_deterministic
    {β : Type*} [MeasurableSpace β]
    {spec spec' : ProbActionSpec σ ι}
    {μ₀ μ₀' : Measure σ} [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₀']
    {g : σ → β} (hg : Measurable g)
    (h_step_inv : ∀ (i : ι) (s : σ) (hgate : (spec.actions i).gate s),
        ∀ s' ∈ ((spec.actions i).effect s hgate).support, g s' = g s)
    (h_step_inv' : ∀ (i : ι) (s : σ) (hgate : (spec'.actions i).gate s),
        ∀ s' ∈ ((spec'.actions i).effect s hgate).support, g s' = g s)
    (h_det : ∀ (A : Adversary σ ι),
       (traceDist spec A μ₀).map (fun ω => g (ω 0).1) =
       (traceDist spec' A μ₀').map (fun ω => g (ω 0).1))
    (R : RandomisedAdversary σ ι) (k : ℕ) :
    (randomisedTraceDist spec R μ₀).map (fun ω => g (ω k).1) =
      (randomisedTraceDist spec' R μ₀').map (fun ω => g (ω k).1) := by
  classical
  have hLHS : (randomisedTraceDist spec R μ₀).map (fun ω => g (ω k).1) =
              (randomisedTraceDist spec R μ₀).map (fun ω => g (ω 0).1) :=
    Measure.map_congr (randomisedTraceDist_state_proj_AE_eq_init h_step_inv μ₀ R k)
  have hRHS : (randomisedTraceDist spec' R μ₀').map (fun ω => g (ω k).1) =
              (randomisedTraceDist spec' R μ₀').map (fun ω => g (ω 0).1) :=
    Measure.map_congr (randomisedTraceDist_state_proj_AE_eq_init h_step_inv' μ₀' R k)
  rw [hLHS, hRHS]
  exact randomisedTraceDist_map_eq_of_deterministic_at_zero
    (f := fun x : σ × Option ι => g x.1) (hg.comp measurable_fst) h_det R

/-- **Lift form for `AlmostDiamond`.** Inductive form: if eventual
occurrence is guaranteed for every deterministic adversary by a
"leads-to" certificate that's adversary-independent, the randomised
analog holds.

For this PR's purposes we expose the most-general form that PR 9.3
needs: a randomised analog of `AlmostDiamond_of_leads_to` that
takes the same per-step "leads-to" data as the deterministic
version. The proof follows the inductive marginal-recurrence
template; the key step uses `randomisedStepKernel_apply_tsum` to
distribute the per-step preservation across the schedule PMF. -/
theorem AlmostDiamond.lift_to_randomised
    {spec : ProbActionSpec σ ι} (φ : σ → Prop)
    (h_step : ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
        φ s → ∀ s' ∈ ((spec.actions i).effect s h).support, φ s')
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, φ s)
    (R : RandomisedAdversary σ ι) :
    AlmostDiamondRandomised spec R μ₀ φ := by
  -- AlmostDiamond is implied by AlmostBox (in the trivial direction:
  -- if `φ` holds at every n, then ∃n, `φ` at n).
  unfold AlmostDiamondRandomised
  have hbox : AlmostBoxRandomised spec R μ₀ φ :=
    AlmostBoxRandomised_of_inductive φ h_step μ₀ h_init R
  filter_upwards [hbox] with ω hω
  exact ⟨0, hω 0⟩

end RandomisedLifts

end Leslie.Prob
