/-
M3 W4 (Phase 11-α) — Secrecy framework abstraction.

`Secrecy spec μ₀ proj` says: under any deterministic adversary, the
projected trace distribution doesn't depend on the secret. This is
the protocol-independent notion of operational view-secrecy.

`SecrecyRushing` is the view-restricted (rushing) variant: the
adversary's schedule depends only on a `ProtocolView` projection
of the state, not on the full state-history. Mirrors the standard
cryptography-literature notion (Canetti–Rabin '93, Goldwasser–
Lindell '02).

Each example protocol (AVSS, BivariateShamir, ...) instantiates
`Secrecy` or `SecrecyRushing` with its specific projection. This
file is purely abstract; protocol-specific theorems live in
`Leslie/Examples/Prob/`.

The two definitions intentionally mirror the existing AVSS-side
shape `(traceDist ... A μ₀ sec).map proj = (traceDist ... A μ₀ sec').map proj`
so that AVSS's headline `avss_secrecy_AS_view_rushing` can be
restated as a one-line `instance : SecrecyRushing avssSpec ... ...`
in Phase 11-γ.

Per implementation plan v2.2 §M3 W4 + design plan v2.2
§"Secrecy framework abstraction", Phase 11-α (PR #71's §14 plan).
-/

import Leslie.Prob.Trace
import Leslie.Prob.Adversary

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

end Leslie.Prob
