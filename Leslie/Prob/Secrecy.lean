/-
M3 W4 (Phase 11-α + 11-β) — Secrecy framework abstraction.

Phase 11-α (PR #71) introduced two predicates over deterministic
adversaries:

  * `Secrecy spec μ₀ proj` — under any deterministic adversary, the
    projected trace distribution doesn't depend on the secret. The
    protocol-independent notion of operational view-secrecy.
  * `SecrecyRushing` — view-restricted variant: the adversary's
    schedule depends only on a `ProtocolView` projection. Mirrors
    Canetti–Rabin '93 / Goldwasser–Lindell '02.

Phase 11-β (this PR) adds the **randomised** counterparts, mirroring
the deterministic stack against `RandomisedAdversary` and
`RushingRandomisedAdversary`:

  * `SecrecyRandomised spec μ₀ proj` — universal over randomised
    schedules, on the mixture trace measure (`randomisedTraceDist`).
  * `SecrecyRushingRandomised` — view-restricted randomised variant.

The "easy" direction `SecrecyRandomised → Secrecy` (specialise
through `Adversary.toRandomised`) is proven inline.  The converse
`Secrecy → SecrecyRandomised` requires a Fubini-over-deterministic-
schedules argument (the randomised mixture trace measure decomposes
into an integral over deterministic schedules induced by `R`).
That direction is queued for a future PR (likely Phase 12-prereq);
its absence is not a soundness gap — protocols generally prove
either the deterministic or the randomised form directly without
relying on the cross-implication.

Each example protocol (AVSS, BivariateShamir, ...) instantiates
`Secrecy` / `SecrecyRushing` / `SecrecyRandomised` /
`SecrecyRushingRandomised` with its specific projection. This file
is purely abstract; protocol-specific theorems live in
`Leslie/Examples/Prob/`.

Per implementation plan v2.2 §M3 W4 + design plan v2.2
§"Secrecy framework abstraction", Phase 11-α (PR #71) + Phase 11-β
(this PR).
-/

import Leslie.Prob.Trace
import Leslie.Prob.Adversary
import Leslie.Prob.RandomisedAdversary
import Mathlib.Probability.ProductMeasure

namespace Leslie.Prob

open MeasureTheory

/-! ## Definitions -/

variable {σ ι : Type*}
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- A protocol satisfies **operational secrecy** with respect to a
secret-indexed initial-measure family `μ₀ : Sec → Measure σ` and a
coalition projection `proj : Trace σ ι → V` if every two secrets
produce the same projected trace distribution under any
deterministic adversary.

The secret is encoded in the initial state (via `μ₀`); the
adversary's view of the trace through `proj` (typically the
corrupt-coalition view + schedule prefix) is the only operational
quantity that matters for secrecy. The claim says: this view is
distributed identically across secrets. -/
def Secrecy
    (spec : ProbActionSpec σ ι)
    {Sec : Type*}
    {V : Type*} [MeasurableSpace V]
    (μ₀ : Sec → Measure σ) [∀ s, IsProbabilityMeasure (μ₀ s)]
    (proj : Trace σ ι → V) : Prop :=
  ∀ (sec sec' : Sec) (A : Adversary σ ι),
    (traceDist spec A (μ₀ sec)).map proj =
    (traceDist spec A (μ₀ sec')).map proj

/-- View-restricted (rushing) secrecy: the rushing adversary's
schedule depends only on the `ProtocolView W` projection of the
state-history. Quantifies over `RushingAdversary σ ι W` whose
attached `ProtocolView` matches `view`.

This is strictly weaker than `Secrecy spec μ₀ proj` (the universal
adversary class is a strict superset of the rushing-adversary
image), so plain secrecy implies rushing-secrecy
(`Secrecy.toRushing`). The converse requires a separate factorisation
argument and is protocol-specific. -/
def SecrecyRushing
    (spec : ProbActionSpec σ ι)
    {Sec : Type*}
    {V W : Type*} [MeasurableSpace V]
    (μ₀ : Sec → Measure σ) [∀ s, IsProbabilityMeasure (μ₀ s)]
    (view : ProtocolView σ W)
    (proj : Trace σ ι → V) : Prop :=
  ∀ (sec sec' : Sec) (R : RushingAdversary σ ι W),
    R.toProtocolView = view →
    (traceDist spec R.toAdversary (μ₀ sec)).map proj =
    (traceDist spec R.toAdversary (μ₀ sec')).map proj

/-! ## Structural lemmas -/

/-- Secrecy is **monotone in the projection**: applying a
measurable map `f` after `proj₁` yields a coarser projection
that still preserves secrecy. Proof is by `Measure.map_map`
followed by the original equality.

For the more general factorisation form (`proj₂ = f ∘ proj₁`),
`rw` against the factorisation and then apply this lemma. -/
theorem Secrecy.mono_proj
    {spec : ProbActionSpec σ ι}
    {Sec V₁ V₂ : Type*}
    [MeasurableSpace V₁] [MeasurableSpace V₂]
    {μ₀ : Sec → Measure σ} [∀ s, IsProbabilityMeasure (μ₀ s)]
    {proj₁ : Trace σ ι → V₁} (hproj₁ : Measurable proj₁)
    (f : V₁ → V₂) (hf : Measurable f)
    (h : Secrecy spec μ₀ proj₁) :
    Secrecy spec μ₀ (f ∘ proj₁) := by
  intro sec sec' A
  rw [← Measure.map_map hf hproj₁, ← Measure.map_map hf hproj₁, h sec sec' A]

/-- Rushing-secrecy is monotone in the projection, mirroring
`Secrecy.mono_proj`. -/
theorem SecrecyRushing.mono_proj
    {spec : ProbActionSpec σ ι}
    {Sec V₁ V₂ W : Type*}
    [MeasurableSpace V₁] [MeasurableSpace V₂]
    {μ₀ : Sec → Measure σ} [∀ s, IsProbabilityMeasure (μ₀ s)]
    {view : ProtocolView σ W}
    {proj₁ : Trace σ ι → V₁} (hproj₁ : Measurable proj₁)
    (f : V₁ → V₂) (hf : Measurable f)
    (h : SecrecyRushing spec μ₀ view proj₁) :
    SecrecyRushing spec μ₀ view (f ∘ proj₁) := by
  intro sec sec' R hR
  rw [← Measure.map_map hf hproj₁, ← Measure.map_map hf hproj₁, h sec sec' R hR]

/-- Plain secrecy implies rushing-secrecy (for any view). The
universal claim over all deterministic adversaries specialises to
the image of `RushingAdversary.toAdversary`, so any
`R : RushingAdversary σ ι W` can be plugged in directly.

The hypothesis `R.toProtocolView = view` is irrelevant on this
side: `Secrecy` doesn't constrain the view at all, so the
rushing-secrecy conclusion holds for the requested view (or any
other) trivially. -/
theorem Secrecy.toRushing
    {spec : ProbActionSpec σ ι}
    {Sec V W : Type*} [MeasurableSpace V]
    {μ₀ : Sec → Measure σ} [∀ s, IsProbabilityMeasure (μ₀ s)]
    {proj : Trace σ ι → V}
    (view : ProtocolView σ W)
    (h : Secrecy spec μ₀ proj) :
    SecrecyRushing spec μ₀ view proj := by
  intro sec sec' R _hR
  exact h sec sec' R.toAdversary

/-! ## Phase 11-β — Randomised counterparts -/

/-- **Randomised operational secrecy.**  Under any *randomised*
adversary `R : RandomisedAdversary σ ι` (kernel-mixture schedule),
the projected mixture trace distribution doesn't depend on the
secret.

This is the literature-standard threat model for AVSS-style
secrecy claims (Canetti–Rabin '93, Backes-Pfitzmann-Waidner): the
adversary may flip coins to choose the schedule, but the corrupt
coalition's view distribution is identical across secrets.

Defined identically to `Secrecy` but with `randomisedTraceDist` in
place of `traceDist`. -/
def SecrecyRandomised
    (spec : ProbActionSpec σ ι)
    {Sec : Type*}
    {V : Type*} [MeasurableSpace V]
    (μ₀ : Sec → Measure σ) [∀ s, IsProbabilityMeasure (μ₀ s)]
    (proj : Trace σ ι → V) : Prop :=
  ∀ (sec sec' : Sec) (R : RandomisedAdversary σ ι),
    (randomisedTraceDist spec R (μ₀ sec)).map proj =
    (randomisedTraceDist spec R (μ₀ sec')).map proj

/-- **Randomised rushing operational secrecy.**  View-restricted
randomised analog of `SecrecyRushing`: quantifies over
`RushingRandomisedAdversary σ ι W` (PMF-valued schedules on view-
histories).  The adversary's randomised schedule sees only the
`ProtocolView W` projection of the state-history.

This is the most literature-faithful threat model in the framework:
randomised + rushing combines the two literature-standard adversarial
powers.  It is strictly weaker than `SecrecyRandomised`, which
quantifies over the full universal class of randomised schedulers
(state-history visible). -/
def SecrecyRushingRandomised
    (spec : ProbActionSpec σ ι)
    {Sec : Type*}
    {V W : Type*} [MeasurableSpace V]
    (μ₀ : Sec → Measure σ) [∀ s, IsProbabilityMeasure (μ₀ s)]
    (view : ProtocolView σ W)
    (proj : Trace σ ι → V) : Prop :=
  ∀ (sec sec' : Sec) (R : RushingRandomisedAdversary σ ι W),
    R.toProtocolView = view →
    (randomisedTraceDist spec R.toRandomisedAdversary (μ₀ sec)).map proj =
    (randomisedTraceDist spec R.toRandomisedAdversary (μ₀ sec')).map proj

/-- `SecrecyRandomised` is monotone in the projection, mirroring
`Secrecy.mono_proj`. -/
theorem SecrecyRandomised.mono_proj
    {spec : ProbActionSpec σ ι}
    {Sec V₁ V₂ : Type*}
    [MeasurableSpace V₁] [MeasurableSpace V₂]
    {μ₀ : Sec → Measure σ} [∀ s, IsProbabilityMeasure (μ₀ s)]
    {proj₁ : Trace σ ι → V₁} (hproj₁ : Measurable proj₁)
    (f : V₁ → V₂) (hf : Measurable f)
    (h : SecrecyRandomised spec μ₀ proj₁) :
    SecrecyRandomised spec μ₀ (f ∘ proj₁) := by
  intro sec sec' R
  rw [← Measure.map_map hf hproj₁, ← Measure.map_map hf hproj₁, h sec sec' R]

/-- `SecrecyRushingRandomised` is monotone in the projection,
mirroring `SecrecyRushing.mono_proj`. -/
theorem SecrecyRushingRandomised.mono_proj
    {spec : ProbActionSpec σ ι}
    {Sec V₁ V₂ W : Type*}
    [MeasurableSpace V₁] [MeasurableSpace V₂]
    {μ₀ : Sec → Measure σ} [∀ s, IsProbabilityMeasure (μ₀ s)]
    {view : ProtocolView σ W}
    {proj₁ : Trace σ ι → V₁} (hproj₁ : Measurable proj₁)
    (f : V₁ → V₂) (hf : Measurable f)
    (h : SecrecyRushingRandomised spec μ₀ view proj₁) :
    SecrecyRushingRandomised spec μ₀ view (f ∘ proj₁) := by
  intro sec sec' R hR
  rw [← Measure.map_map hf hproj₁, ← Measure.map_map hf hproj₁, h sec sec' R hR]

/-- Randomised secrecy implies plain (deterministic) secrecy: the
universal claim over `RandomisedAdversary` specialises to the image
of `Adversary.toRandomised`, and `randomisedTraceDist_toRandomised`
shows the mixture trace at a deterministic-lift adversary equals
the deterministic trace.

This is the **easy direction** of the
`Secrecy ↔ SecrecyRandomised` correspondence; the converse requires
Fubini over deterministic schedules and is queued for a follow-up
PR (see file docstring). -/
theorem SecrecyRandomised.toSecrecy
    {spec : ProbActionSpec σ ι}
    {Sec V : Type*} [MeasurableSpace V]
    {μ₀ : Sec → Measure σ} [∀ s, IsProbabilityMeasure (μ₀ s)]
    {proj : Trace σ ι → V}
    (h : SecrecyRandomised spec μ₀ proj) :
    Secrecy spec μ₀ proj := by
  intro sec sec' A
  have hsec  := h sec sec' A.toRandomised
  rw [randomisedTraceDist_toRandomised, randomisedTraceDist_toRandomised] at hsec
  exact hsec

/-- Randomised secrecy implies rushing-randomised secrecy (for any
view).  The universal claim over `RandomisedAdversary` specialises
to the image of `RushingRandomisedAdversary.toRandomisedAdversary`,
so any `R : RushingRandomisedAdversary σ ι W` plugs in directly.

The view hypothesis is irrelevant on this side, mirroring
`Secrecy.toRushing`. -/
theorem SecrecyRandomised.toRushingRandomised
    {spec : ProbActionSpec σ ι}
    {Sec V W : Type*} [MeasurableSpace V]
    {μ₀ : Sec → Measure σ} [∀ s, IsProbabilityMeasure (μ₀ s)]
    {proj : Trace σ ι → V}
    (view : ProtocolView σ W)
    (h : SecrecyRandomised spec μ₀ proj) :
    SecrecyRushingRandomised spec μ₀ view proj := by
  intro sec sec' R _hR
  exact h sec sec' R.toRandomisedAdversary

/-! ## Phase 11-β-followup — `Secrecy → SecrecyRandomised`

The **hard direction** of the `Secrecy ↔ SecrecyRandomised`
correspondence: deterministic secrecy implies randomised secrecy.

**Mathematical content.**  Given a randomised adversary
`R : RandomisedAdversary σ ι`, the mixture trace measure
`randomisedTraceDist spec R μ` decomposes as a Fubini integral of
deterministic trace measures over a probability measure on
deterministic schedules.  Concretely, R's per-history PMFs
`R.strategy : List (σ × Option ι) → PMF (Option ι)` induce a
probability measure on the function space
`List (σ × Option ι) → Option ι` of "schedule assignments" via the
Kolmogorov / Ionescu-Tulcea construction over the (countable) index
set of histories.  Each such assignment defines a deterministic
`Adversary σ ι`; the mixture trace measure is then the integral of
deterministic trace measures over this schedule-assignment measure.

Once the factorisation is established, the deterministic `Secrecy`
hypothesis applies pointwise under the integral, swapping the secret
and yielding the randomised conclusion via congruence of integrals.

**Proof strategy chosen for this PR — Strategy B (schedule-space
measure).**  We expose a single named factorisation lemma
`randomisedTraceDist_eq_integral_traceDist` as a sorry-bearing
helper *inside this file* — Phase 11-β-followup-2 will promote it
to `RandomisedAdversary.lean` once mathematically settled.  The
main theorem `Secrecy.toRandomised` then becomes a short
consequence: factor both sides through the schedule-space measure,
apply `Secrecy` under the integral, conclude by `Measure.map`
congruence.

This proof structure is **load-bearing for the sorry-handoff
chain**: each named sorry is a self-contained measure-theoretic
sub-claim that a subsequent worker can attack independently.

**Sorry inventory** (after Phase 11-β-followup-3, Worker 3):

  * `Phase 11-β-followup-2` — ✅ closed (Worker 2). `scheduleSpaceMeasure`
    + its `IsProbabilityMeasure` instance now use mathlib's
    `MeasureTheory.Measure.infinitePi` over the (arbitrary) history
    index set with per-fiber `PMF.toMeasure`.  Note that mathlib's
    `infinitePi` does not require a `Countable` index, so the file-
    level `[Countable σ] [Countable ι]` are not threaded into the
    definition itself (they remain useful for the rest of the
    development, e.g. measurability of discrete projections).
  * `Phase 11-β-followup-3` — ✅ closed (Worker 3, this PR).
    `randomisedTraceDist_eq_integral_traceDist` is now a one-line
    forwarding to a single named sub-claim `_traj` (the substantive
    trajectory-level Fubini), and the two supporting facts (per-step
    factorisation, schedule-space marginal) are fully proved.
  * `Phase 11-β-followup-3a` — ⏳ open (queued for follow-up).
    `randomisedTraceDist_eq_integral_traceDist_traj`: the cylinder-
    set Ionescu-Tulcea induction that lifts the per-step
    factorisation to the trajectory measure. ~150 lines of mechanical
    measure-theoretic plumbing; proof outline + inputs are documented
    in the helper's docstring.
  * `Phase 11-β-followup-4` — ⏳ open. `Secrecy.toRandomised` itself:
    assemble the factorisation + apply `h` under the integral +
    conclude.

Each of these is a clean handoff target; subsequent PRs in the chain
can address them independently. -/

/-! ### Schedule-space machinery

A "deterministic schedule assignment" is a function
`List (σ × Option ι) → Option ι`, identical in shape to
`Adversary.schedule` (just without the corruption set, which is
inherited from R).  We package it as a private abbrev to keep
the rest of this section terse. -/

/-- A *schedule assignment*: the deterministic content of a
randomised adversary's choice — for each history, which action
label to fire.  Bundling this with `R.corrupt` produces an
`Adversary σ ι`. -/
private abbrev ScheduleAssignment (σ ι : Type*) :=
  List (σ × Option ι) → Option ι

/-- Convert a schedule assignment + corruption set into a
deterministic `Adversary σ ι`. -/
private def ScheduleAssignment.toAdversary
    (sched : ScheduleAssignment σ ι) (corrupt : Set PartyId) :
    Adversary σ ι where
  schedule := sched
  corrupt  := corrupt

/-- The `MeasurableSpace` on schedule assignments: the Pi-σ-algebra
on the function space, with each fiber `Option ι` carrying the
discrete σ-algebra (already supplied by `instMeasurableSpaceOption`).
This is sufficient because histories are countable (lists over a
countable type).

NOTE: The `[Countable σ] [Countable ι]` typeclasses (combined with
the file-level variable section) imply
`Countable (List (σ × Option ι))`, which is needed for the
Ionescu-Tulcea / Kolmogorov product construction in
`Phase 11-β-followup-2`. -/
private instance instMeasurableSpaceScheduleAssignment :
    MeasurableSpace (ScheduleAssignment σ ι) := by
  unfold ScheduleAssignment
  infer_instance

/-- The schedule-space measure induced by a randomised adversary.

For each history `h`, R's strategy produces a PMF on `Option ι`.
The schedule-space measure is the Kolmogorov product of these
per-history marginals over the (arbitrary, countable in our typical
use, but mathlib's `Measure.infinitePi` works on any index type) set
of all histories `List (σ × Option ι)`.

Closed in Phase 11-β-followup-2 (Worker 2): the Kolmogorov product of
`(R.strategy h).toMeasure` indexed over `h : List (σ × Option ι)`
via `MeasureTheory.Measure.infinitePi`. Each fiber is a probability
measure (`PMF.toMeasure.isProbabilityMeasure`), and `infinitePi`
extends across arbitrary index types (Carathéodory + projective
limit), so no `Countable` constraint on the index set is required —
the file-level `[Countable σ] [Countable ι]` typeclasses suffice for
the rest of the development. -/
private noncomputable def scheduleSpaceMeasure
    (R : RandomisedAdversary σ ι) :
    Measure (ScheduleAssignment σ ι) :=
  Measure.infinitePi
    (fun h : List (σ × Option ι) => (R.strategy h).toMeasure)

/-- The schedule-space measure is a probability measure: the
Kolmogorov product of probability measures (`PMF.toMeasure` is
always a probability measure) is itself a probability measure, by
mathlib's `infinitePi` instance. -/
private instance instIsProbabilityMeasure_scheduleSpaceMeasure
    (R : RandomisedAdversary σ ι) :
    IsProbabilityMeasure (scheduleSpaceMeasure R) := by
  unfold scheduleSpaceMeasure
  infer_instance

/-! ### Per-step factorisation building blocks

The Fubini factorisation `randomisedTraceDist_eq_integral_traceDist`
decomposes naturally into three layers of decreasing tractability:

  * **3a (closed here)** — per-history per-step factorisation: the
    randomised step kernel at history `h` equals the PMF-bind of
    `singleActionStep` over the schedule choice. Direct from the
    existing tsum identity `randomisedStepKernel_apply_tsum`.
  * **3b (closed here)** — schedule-space marginal: the marginal of
    `scheduleSpaceMeasure R` at any single history coordinate is
    `(R.strategy h).toMeasure`. Direct from mathlib's
    `infinitePi_map_eval`.
  * **3c (open, queued for follow-up)** — trajectory-level Fubini:
    lifting the per-step factorisation to the trajectory measure via
    Ionescu-Tulcea. This is the substantive measure-theoretic
    content; see the sub-sorry comment below for a structured
    breakdown.

Phase 11-β-followup-3 (this PR) closes 3a and 3b and reduces the main
factorisation to a single, clearly-stated trajectory-level sub-claim
`randomisedTraceDist_eq_integral_traceDist_traj`. The main lemma is
proved structurally: it exposes the bind-of-trajectories form and
hands off the Ionescu-Tulcea-cylinder argument to the next worker.
-/

set_option linter.unusedSectionVars false in
/-- **3a (closed).** Per-history factorisation of the randomised
step kernel: at any history `h`, the kernel measure equals the
`Measure.bind` of `singleActionStep spec h` over the schedule PMF
viewed as a measure.

Direct from the tsum identity `randomisedStepKernel_apply_tsum`,
unfolding `Measure.bind` via `bind_apply` and reducing the integral
on the discrete `Option ι` PMF to a tsum via `lintegral_countable'`. -/
private lemma randomisedStepKernel_eq_bind_singleActionStep
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    {n : ℕ} (h : FinPrefix σ ι n) :
    (randomisedStepKernel spec R n) h =
      Measure.bind (R.strategy h.toList).toMeasure
        (fun α => singleActionStep spec h α) := by
  -- Reduce to set-equality and use `bind_apply` + `tsum`.
  ext s hs
  -- LHS: the existing tsum identity.
  rw [randomisedStepKernel_apply_tsum spec R h hs]
  -- RHS: `bind_apply` reduces to `lintegral`, then `lintegral_countable'`
  -- (Option ι is countable + discrete) reduces to `tsum`.
  rw [Measure.bind_apply hs
        ((Measurable.of_discrete (f := singleActionStep spec h)).aemeasurable)]
  -- ∫⁻ α, singleActionStep spec h α s ∂(R.strategy ...).toMeasure
  --   = ∑' α, singleActionStep spec h α s * (R.strategy ...).toMeasure {α}
  --   = ∑' α, (R.strategy h.toList) α * singleActionStep spec h α s.
  rw [MeasureTheory.lintegral_countable' (μ := (R.strategy h.toList).toMeasure)
        (fun α => singleActionStep spec h α s)]
  refine tsum_congr fun α => ?_
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete, mul_comm]

set_option linter.unusedSectionVars false in
/-- **3b (closed).** Schedule-space marginal at a single history:
the projection of `scheduleSpaceMeasure R` onto the `h`-coordinate
recovers `(R.strategy h).toMeasure`.

Direct application of mathlib's `Measure.infinitePi_map_eval`. -/
private lemma scheduleSpaceMeasure_map_eval
    (R : RandomisedAdversary σ ι) (h : List (σ × Option ι)) :
    (scheduleSpaceMeasure R).map (fun sched => sched h) =
      (R.strategy h).toMeasure := by
  unfold scheduleSpaceMeasure
  exact Measure.infinitePi_map_eval _ h

/-- **3c (queued sub-sorry, Phase 11-β-followup-3a).**

Trajectory-level Fubini for the mixture trace measure. This is the
substantive measure-theoretic content of `Secrecy.toRandomised`.

**Statement intuition.** A randomised adversary `R` with per-history
PMFs samples a fresh schedule choice at each step; equivalently, by
Kolmogorov / Ionescu-Tulcea, we can sample *all* schedule choices in
advance (one per history) and run the deterministic step kernel
against the sampled schedule. Both yield the same trace distribution
because the per-step independence of schedule samples in the
randomised kernel matches the per-history independence in the
Kolmogorov product.

**Proof obligation.** Apply Ionescu-Tulcea cylinder uniqueness:
two probability measures on `Trace σ ι = ∀ n, σ × Option ι` are
equal iff their cylinder-set values agree. Both sides agree on
cylinders by induction on the cylinder length, using:
  * `randomisedStepKernel_eq_bind_singleActionStep` (3a) at each step
    on the LHS, and
  * `stepKernel_apply_eq_singleActionStep` for each fixed `sched` on
    the RHS,
followed by Fubini on `scheduleSpaceMeasure R` to swap the
schedule-space integral past the trajectory integral. The
schedule-space marginal `scheduleSpaceMeasure_map_eval` (3b) bridges
the per-step kernel form on the LHS with the per-history-marginal
form needed on the RHS.

**Mathlib gap.** Mathlib's `Kernel.trajMeasure` does not expose a
"`trajMeasure` of a `Kernel.bind`-mixture equals `Measure.bind` of
trajectory measures" lemma; the proof must be done by hand on
cylinder sets. ~150 lines of mechanical induction; isolated here as
a single named sorry to be discharged in a follow-up PR. -/
private theorem randomisedTraceDist_eq_integral_traceDist_traj
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (μ : Measure σ) [IsProbabilityMeasure μ] :
    randomisedTraceDist spec R μ =
      Measure.bind (scheduleSpaceMeasure R) fun sched =>
        traceDist spec (sched.toAdversary R.corrupt) μ := by
  sorry  -- TODO Phase 11-β-followup-3a: Ionescu-Tulcea cylinder
         -- factorisation. See docstring above for the proof outline.
         -- Inputs: 3a (`randomisedStepKernel_eq_bind_singleActionStep`)
         --       + 3b (`scheduleSpaceMeasure_map_eval`)
         --       + Ionescu-Tulcea cylinder uniqueness.

/-- **Fubini factorisation of the mixture trace measure** (the heart
of `Secrecy.toRandomised`).

The randomised mixture trace measure equals the *integral* of
deterministic trace measures over the schedule-space measure.

For any measurable test function `g : Trace σ ι → ℝ≥0∞`,
```
∫ ω, g ω ∂(randomisedTraceDist spec R μ) =
∫ sched, ∫ ω, g ω ∂(traceDist spec (sched.toAdversary R.corrupt) μ)
       ∂(scheduleSpaceMeasure R)
```

For our `Secrecy` use-case, `g` is the indicator of a
`Measure.map proj`-measurable set — Fubini moves the projection
outside the integral and leaves the deterministic equality to
discharge.

**Phase 11-β-followup-3 status.** This PR closes the main lemma
modulo the trajectory-level Fubini sub-claim
`randomisedTraceDist_eq_integral_traceDist_traj` (sorry-bookmark
`Phase 11-β-followup-3a`), which is the substantive
measure-theoretic content. The two supporting facts are closed:

  * Per-step factorisation 3a:
    `randomisedStepKernel_eq_bind_singleActionStep` (closed).
  * Schedule-space marginal 3b:
    `scheduleSpaceMeasure_map_eval` (closed via mathlib's
    `infinitePi_map_eval`).

The main lemma is now a single-line forwarding to 3c. -/
private theorem randomisedTraceDist_eq_integral_traceDist
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (μ : Measure σ) [IsProbabilityMeasure μ] :
    randomisedTraceDist spec R μ =
      Measure.bind (scheduleSpaceMeasure R) fun sched =>
        traceDist spec (sched.toAdversary R.corrupt) μ :=
  randomisedTraceDist_eq_integral_traceDist_traj spec R μ

/-- **Hard direction** of the `Secrecy ↔ SecrecyRandomised`
correspondence: deterministic secrecy implies randomised secrecy.

Proof outline (Fubini over deterministic schedules).  Given
`R : RandomisedAdversary σ ι`, the randomised mixture trace measure
`randomisedTraceDist spec R μ` equals the integral, over the
schedule-space measure, of the deterministic trace measure for the
schedule sampled.  Applying `Secrecy` under the integral yields the
conclusion.

Concretely:
  * factor both sides via `randomisedTraceDist_eq_integral_traceDist`,
  * push `Measure.map proj` inside the bind via `Measure.map_bind`,
  * apply the deterministic hypothesis `h sec sec' (sched.toAdversary R.corrupt)`
    pointwise inside the bind,
  * conclude by `Measure.bind_congr`.

NOTE: this is the substantive measure-theoretic content.  The
proof is in progress (sorry-handoff chain). -/
theorem Secrecy.toRandomised
    {spec : ProbActionSpec σ ι}
    {Sec V : Type*} [MeasurableSpace V]
    {μ₀ : Sec → Measure σ} [∀ s, IsProbabilityMeasure (μ₀ s)]
    {proj : Trace σ ι → V}
    (h : Secrecy spec μ₀ proj) :
    SecrecyRandomised spec μ₀ proj := by
  intro sec sec' R
  -- Strategy: factor both sides through the schedule-space measure
  -- (`randomisedTraceDist_eq_integral_traceDist`), push `Measure.map proj`
  -- through `Measure.bind`, then apply `h sec sec' (sched.toAdversary R.corrupt)`
  -- pointwise under the integral.
  --
  -- Pushing `Measure.map proj` through `Measure.bind` requires
  -- `AEMeasurable proj` w.r.t. the inner measure.  In the framework
  -- `proj` is typically discrete-valued (e.g., a coalition view); the
  -- standard lift is `Measurable.aemeasurable` after a
  -- `[MeasurableSingletonClass V]` upgrade or a discrete σ-algebra on
  -- `V`.  Because the current `Secrecy` signature does not carry a
  -- `Measurable proj` hypothesis, the cleanest fix in the chain is
  -- either (a) add such a hypothesis here (mirroring `mono_proj`),
  -- or (b) prove that `proj`'s measurability is automatic in all
  -- caller contexts.  This is left for Phase 11-β-followup-4.
  sorry  -- TODO Phase 11-β-followup-4: assemble the factorisation
         -- (lemma -3) + push `proj` through `Measure.bind` (needs
         -- `AEMeasurable proj`; either add hypothesis or derive from
         -- caller context) + apply `h` pointwise + close by
         -- `Measure.bind_congr`.  See proof-strategy comment in the
         -- file docstring above.

end Leslie.Prob
