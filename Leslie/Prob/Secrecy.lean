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

end Leslie.Prob
