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

**Sorry inventory** (Phase 11-β-followup-1, this PR):

  * `Phase 11-β-followup-2` — `ScheduleSpace` & its measure: the
    Kolmogorov/Ionescu-Tulcea construction of a probability measure
    on the function space of schedule-assignments from R's per-history
    PMFs.
  * `Phase 11-β-followup-3` — `randomisedTraceDist_eq_integral_traceDist`:
    the Fubini factorisation that the mixture trace measure equals
    the integral of deterministic trace measures over the schedule-
    space measure.
  * `Phase 11-β-followup-4` — `Secrecy.toRandomised` itself: assemble
    the factorisation + apply `h` under the integral + conclude.

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
per-history marginals over the countable index set of all histories
`List (σ × Option ι)`.

TODO Phase 11-β-followup-2: construct this measure rigorously via
`MeasureTheory.Measure.pi` over the countable history index set.
The construction is standard but requires threading `PMF.toMeasure`
+ `Measure.pi` + the existing typeclass `Countable (List (σ × Option ι))`
(derivable from `Countable σ` and `Countable ι` via
`List.instCountable`). -/
private noncomputable def scheduleSpaceMeasure
    (R : RandomisedAdversary σ ι) :
    Measure (ScheduleAssignment σ ι) :=
  -- The Kolmogorov product of `(R.strategy h).toMeasure` indexed
  -- over `h : List (σ × Option ι)`.  Mathlib's `Measure.pi` requires
  -- a `Fintype` index set; for the countable index set used here we
  -- need `MeasureTheory.Measure.infinitePi` or an equivalent.
  -- Phase 11-β-followup-2 supplies the construction.
  sorry  -- TODO Phase 11-β-followup-2: Kolmogorov product over countable history index

/-- The schedule-space measure is a probability measure (the
countable product of probability measures is a probability
measure).

TODO Phase 11-β-followup-2 (companion): once `scheduleSpaceMeasure`
is constructed via `MeasureTheory.Measure.infinitePi`, this
instance follows from `Measure.pi.instIsProbabilityMeasure` (or
the `infinitePi` analog). -/
private instance instIsProbabilityMeasure_scheduleSpaceMeasure
    (R : RandomisedAdversary σ ι) :
    IsProbabilityMeasure (scheduleSpaceMeasure R) := by
  -- Will follow from the underlying `Measure.pi` / `infinitePi` once
  -- Phase 11-β-followup-2 closes.
  sorry  -- TODO Phase 11-β-followup-2 (companion): probability measure status

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

TODO Phase 11-β-followup-3: prove the factorisation.  The standard
route is induction on the trajectory length:

  1. Coordinate-0 marginal: both sides agree (both reduce to
     `μ₀.map (·, none)`, and the schedule-space measure is a
     probability measure so it integrates to 1).
  2. Successor step: use the marginal recurrence
     `Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`
     and the per-step kernel mixture identity
     `randomisedStepKernel_apply_tsum`, plus the schedule-space
     marginal projection.
  3. Pass to the trajectory measure via Ionescu-Tulcea uniqueness
     (a probability measure on `Trace σ ι` is determined by its
     finite-dim marginals).

The induction is mechanical but voluminous (~150 lines).  An
alternative route — direct `Kernel.trajMeasure` extensionality on
`Kernel.bind` — would be cleaner but requires a Mathlib lemma about
`trajMeasure` of `Kernel.bind` that does not exist by name. -/
private theorem randomisedTraceDist_eq_integral_traceDist
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (μ : Measure σ) [IsProbabilityMeasure μ] :
    randomisedTraceDist spec R μ =
      Measure.bind (scheduleSpaceMeasure R) fun sched =>
        traceDist spec (sched.toAdversary R.corrupt) μ := by
  sorry  -- TODO Phase 11-β-followup-3: Fubini factorisation of mixture trace measure

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
