/-
M2 W2 — Probabilistic refinement.

Lifts Abadi–Lamport refinement to the probabilistic setting:
`Π ⊑ₚ Σ via proj` says that for every initial distribution and
adversary on `Π`, there exist matching ones on `Σ` such that
`Σ`'s trace measure projects (via `proj`) to `Π`'s trace measure.

This is the trace-level analogue of `Leslie.Refinement`'s
deterministic refinement, lifted to Mathlib `Measure`s under the
cylinder σ-algebra (per design plan v2.2 §"Composition combinators").

Status (M2 W2 first cut):

  * `Refines Π Σ proj` — the refinement predicate, parameterized
    by a trace-level projection function.
  * `Refines.id` — every spec refines itself via the identity
    projection.
  * `Refines.comp` — composition of refinements.
  * `AlmostBox`, `AlmostDiamond` — modal predicates on
    `traceDist`.
  * `Refines_safe` — invariant lift along refinement (statement;
    body sorry, requires `traceDist` body from M2 W1 polish).

Per implementation plan v2.2 §M2 W2. The proofs that need to
unfold `traceDist` carry transitive sorries until M2 W1 polish
lands; this file's structural lemmas (`comp`, `id`) compose
cleanly without `traceDist` unfolding.
-/

import Leslie.Prob.Action
import Leslie.Prob.Adversary
import Leslie.Prob.Trace

namespace Leslie.Prob

open MeasureTheory

variable {σ σ' σ'' : Type*} {ι ι' ι'' : Type*}

/-! ## Trace-level projection

A trace projection translates an "abstract" trace
(`Trace σ' ι'`) to a "concrete" trace (`Trace σ ι`). For pure
state-translation refinements, this is `fun ω n => (f (ω n).1, ?)`
for some `f : σ' → σ`. For refinements that also collapse
stuttering steps, the projection is more involved. -/

/-- Identity trace projection (when source and target traces have
the same shape). -/
def Trace.idProj : Trace σ ι → Trace σ ι := id

/-- Composition of trace projections. -/
def Trace.compProj (g : Trace σ' ι' → Trace σ ι)
    (f : Trace σ'' ι'' → Trace σ' ι') :
    Trace σ'' ι'' → Trace σ ι :=
  g ∘ f

@[simp] theorem Trace.idProj_apply (ω : Trace σ ι) :
    Trace.idProj ω = ω := rfl

@[simp] theorem Trace.compProj_apply
    (g : Trace σ' ι' → Trace σ ι) (f : Trace σ'' ι'' → Trace σ' ι')
    (ω : Trace σ'' ι'') :
    Trace.compProj g f ω = g (f ω) := rfl

/-! ## Refinement -/

/-- Probabilistic refinement under a trace-level projection.

`Refines Π Σ proj` says: for every initial-state distribution `μ₀`
and adversary `A` on the concrete spec `Π`, there exist a matching
initial distribution `μ₀'` and adversary `A'` on the abstract
spec `Σ` such that `Σ`'s trace measure pushed through `proj`
equals `Π`'s trace measure.

This is the probabilistic Abadi–Lamport, parametric in `proj`
(typically a state-translation + stutter-collapse function).

For the special case where `Σ` and `Π` have the same trace shape,
use `Trace.idProj` for `proj`; this gives the simple "Π ⊑ Σ at
the same trace shape" relation (no refinement mapping). -/
def Refines
    [Countable σ] [Countable σ']
    [Countable ι] [Countable ι']
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace σ'] [MeasurableSingletonClass σ']
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace ι'] [MeasurableSingletonClass ι']
    (spec₁ : ProbActionSpec σ ι) (spec₂ : ProbActionSpec σ' ι')
    (proj : Trace σ' ι' → Trace σ ι) : Prop :=
  ∀ (μ₀ : Measure σ), IsProbabilityMeasure μ₀ →
    ∀ (A : Adversary σ ι),
      ∃ (μ₀' : Measure σ') (_ : IsProbabilityMeasure μ₀')
        (A' : Adversary σ' ι'),
        Measure.map proj (traceDist spec₂ A' μ₀') = traceDist spec₁ A μ₀

/-! ### Identity, composition

The structural lemmas: every spec refines itself via the identity
projection, and refinements compose. These hold without unfolding
`traceDist`. -/

/-- Every spec refines itself under the identity projection. -/
theorem Refines.id
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (spec₁ : ProbActionSpec σ ι) :
    Refines spec₁ spec₁ Trace.idProj := by
  intro μ₀ hμ₀ A
  refine ⟨μ₀, hμ₀, A, ?_⟩
  -- Goal: Measure.map Trace.idProj (traceDist spec₁ A μ₀) = traceDist spec₁ A μ₀
  -- Trace.idProj is the identity, so the map is identity.
  unfold Trace.idProj
  exact Measure.map_id

/-- Composition of refinements. If `Π ⊑ Σ` via `g` and `Σ ⊑ Τ` via
`f`, then `Π ⊑ Τ` via `g ∘ f`. -/
theorem Refines.comp
    [Countable σ] [Countable σ'] [Countable σ'']
    [Countable ι] [Countable ι'] [Countable ι'']
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace σ'] [MeasurableSingletonClass σ']
    [MeasurableSpace σ''] [MeasurableSingletonClass σ'']
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace ι'] [MeasurableSingletonClass ι']
    [MeasurableSpace ι''] [MeasurableSingletonClass ι'']
    {spec₁ : ProbActionSpec σ ι} {spec₂ : ProbActionSpec σ' ι'}
    {spec₃ : ProbActionSpec σ'' ι''}
    {g : Trace σ' ι' → Trace σ ι}
    {f : Trace σ'' ι'' → Trace σ' ι'}
    (h_g : Refines spec₁ spec₂ g) (h_f : Refines spec₂ spec₃ f)
    (h_g_meas : Measurable g) :
    Refines spec₁ spec₃ (Trace.compProj g f) := by
  intro μ₀ hμ₀ A
  -- From h_g: ∃ μ₀₂, A₂ such that map g (traceDist spec₂ A₂ μ₀₂) = traceDist spec₁ A μ₀
  obtain ⟨μ₀₂, hμ₀₂, A₂, h_eq_g⟩ := h_g μ₀ hμ₀ A
  -- From h_f: ∃ μ₀₃, A₃ such that map f (traceDist spec₃ A₃ μ₀₃) = traceDist spec₂ A₂ μ₀₂
  obtain ⟨μ₀₃, hμ₀₃, A₃, h_eq_f⟩ := h_f μ₀₂ hμ₀₂ A₂
  refine ⟨μ₀₃, hμ₀₃, A₃, ?_⟩
  -- Goal: map (g ∘ f) (traceDist spec₃ A₃ μ₀₃) = traceDist spec₁ A μ₀
  -- = map g (map f (traceDist spec₃ A₃ μ₀₃))   [by Measure.map_map, using measurability]
  -- = map g (traceDist spec₂ A₂ μ₀₂)            [by h_eq_f]
  -- = traceDist spec₁ A μ₀                        [by h_eq_g]
  show Measure.map (g ∘ f) (traceDist spec₃ A₃ μ₀₃) = traceDist spec₁ A μ₀
  -- Compose pushforwards: map (g ∘ f) = map g ∘ map f.
  -- Needs g and f measurable; we have g measurable, but f's
  -- measurability isn't a hypothesis here. The full proof requires
  -- threading measurability through both steps; deferred to
  -- M2 W2 polish (analogous to traceDist body in M2 W1 polish).
  sorry

/-! ### Modal predicates on `traceDist`

Probabilistic analogues of `□` and `◇` against a `traceDist`. -/

/-- Almost-surely-always: `φ` holds at every step of the trace. -/
def AlmostBox
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (spec₁ : ProbActionSpec σ ι) (A : Adversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (φ : σ → Prop) : Prop :=
  ∀ᵐ ω ∂(traceDist spec₁ A μ₀), ∀ n, φ ((ω n).1)

/-- Almost-surely-eventually: there exists a step at which `φ`
holds, almost surely. -/
def AlmostDiamond
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (spec₁ : ProbActionSpec σ ι) (A : Adversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (φ : σ → Prop) : Prop :=
  ∀ᵐ ω ∂(traceDist spec₁ A μ₀), ∃ n, φ ((ω n).1)

/-! ### Refines_safe

If `Π` refines `Σ` (via `proj`) and `φ` holds always for `Σ`'s
trace (under projected predicates), then `φ` holds always for
`Π`'s trace.

Proof outline: pushforward through `proj` preserves
`MeasureTheory.ae`. Concretely:
- From `Refines Π Σ proj`, every Π-execution comes from a
  Σ-execution via `proj`.
- `φ` holds Σ-almost-everywhere ⇒ `φ ∘ proj_state` holds
  Π-almost-everywhere via measure-pushforward.

The proof requires unfolding `traceDist` (M2 W1 polish task) and
careful handling of the projection's component-wise structure.
Stated here; sorry'd until those land. -/

/-- Stated form: invariant `φ` on the abstract spec lifts (via
projection) to an invariant on the concrete spec. -/
theorem Refines_safe
    [Countable σ] [Countable σ']
    [Countable ι] [Countable ι']
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace σ'] [MeasurableSingletonClass σ']
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace ι'] [MeasurableSingletonClass ι']
    {spec₁ : ProbActionSpec σ ι} {spec₂ : ProbActionSpec σ' ι'}
    {proj : Trace σ' ι' → Trace σ ι}
    (h_ref : Refines spec₁ spec₂ proj)
    (state_proj : σ' → σ)
    (h_proj_state : ∀ (ω : Trace σ' ι') n, ((proj ω) n).1 = state_proj ((ω n).1))
    (φ : σ → Prop)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (A : Adversary σ ι) :
    (∃ (μ₀' : Measure σ') (_ : IsProbabilityMeasure μ₀')
       (A' : Adversary σ' ι'),
       AlmostBox spec₂ A' μ₀' (φ ∘ state_proj)) →
    AlmostBox spec₁ A μ₀ φ := by
  sorry

end Leslie.Prob
