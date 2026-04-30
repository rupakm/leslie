/-
M2 W2 — Probabilistic refinement.

Lifts Abadi–Lamport refinement to the probabilistic setting:
`Π ⊑ₚ Σ via proj` says that for every initial distribution and
adversary on `Π`, there exist matching ones on `Σ` such that
`Σ`'s trace measure projects (via `proj`) to `Π`'s trace measure.

This is the trace-level analogue of `Leslie.Refinement`'s
deterministic refinement, lifted to Mathlib `Measure`s under the
cylinder σ-algebra (per design plan v2.2 §"Composition combinators").

Status (M2 W2 polish — sorry-free):

  * `Refines Π Σ proj` — the refinement predicate, parameterized
    by a trace-level projection function.
  * `Refines.id` — every spec refines itself via the identity
    projection.
  * `Refines.comp` — composition of refinements (requires
    measurability of both projections to compose pushforwards
    via `Measure.map_map`).
  * `AlmostBox`, `AlmostDiamond` — modal predicates on
    `traceDist`.
  * `Refines_safe` — invariant lift along refinement: a safety
    property `φ` that holds Σ-AE under any abstract execution
    lifts to a Π-AE invariant via `ae_map_iff` on the pushforward.
    Requires measurability of `proj` and of `{s | φ s}`; both
    are satisfied for our discrete protocol settings.

Per implementation plan v2.2 §M2 W2. The real `traceDist` body
(M2 W1 polish + M2 W2 polish) is now a real schedule-and-gate-
conditional Markov-kernel measure; both `Refines.comp` and
`Refines_safe` are proved by composing it with Mathlib's measure
pushforward / AE machinery.
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
    (h_g_meas : Measurable g) (h_f_meas : Measurable f) :
    Refines spec₁ spec₃ (Trace.compProj g f) := by
  intro μ₀ hμ₀ A
  -- From h_g: ∃ μ₀₂, A₂ such that map g (traceDist spec₂ A₂ μ₀₂) = traceDist spec₁ A μ₀
  obtain ⟨μ₀₂, hμ₀₂, A₂, h_eq_g⟩ := h_g μ₀ hμ₀ A
  -- From h_f: ∃ μ₀₃, A₃ such that map f (traceDist spec₃ A₃ μ₀₃) = traceDist spec₂ A₂ μ₀₂
  obtain ⟨μ₀₃, hμ₀₃, A₃, h_eq_f⟩ := h_f μ₀₂ hμ₀₂ A₂
  refine ⟨μ₀₃, hμ₀₃, A₃, ?_⟩
  -- Goal: map (g ∘ f) (traceDist spec₃ A₃ μ₀₃) = traceDist spec₁ A μ₀
  -- = map g (map f (traceDist spec₃ A₃ μ₀₃))   [by Measure.map_map]
  -- = map g (traceDist spec₂ A₂ μ₀₂)            [by h_eq_f]
  -- = traceDist spec₁ A μ₀                        [by h_eq_g]
  show Measure.map (Trace.compProj g f) (traceDist spec₃ A₃ μ₀₃) = traceDist spec₁ A μ₀
  rw [show Trace.compProj g f = g ∘ f from rfl,
      ← Measure.map_map h_g_meas h_f_meas, h_eq_f, h_eq_g]

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

/-! ### `AlmostBox_of_pure_inductive` — deterministic-step bridge

When every action's effect is a Dirac (`PMF.pure (det_step i s)`), the
`stepKernel` collapses to a deterministic kernel: in the `none`-schedule
branch and the gate-fail branch it is already a Dirac (stutter), and in
the gate-pass branch the PMF.pure measure is also a Dirac. With a
deterministic-everywhere kernel, an inductive predicate `P` that is
preserved by the deterministic step transfers from the initial measure
to every coordinate of the trace, hence `AlmostBox` holds.

**M2 W3 polish status.** The helper is structural (signature pinned
down by the four BrachaRBC-AS theorems below). The proof body needs
the n-step marginal extraction lemma for `Kernel.trajMeasure`, which
is not yet exposed in Mathlib v4.27.0 in a directly usable form (only
joint marginals via `map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`).
Closing this rigorously is M3-W1-adjacent work — see the documentation
of the gap below the theorem.

For now we leave the body as `sorry` so the BrachaRBC closures (which
reduce to one-line applications of this helper) demonstrate the API
is correctly shaped.

Mathlib lemmas used / needed:
  * `MeasureTheory.ae_all_iff` — countable-AE swap (already available).
  * `PMF.toMeasure_pure` — Dirac form of `PMF.pure` (already available).
  * `Kernel.trajMeasure_marginal_succ` (NOT in Mathlib): would say
    `(trajMeasure μ₀ κ).map (fun ω => ω (n+1))` equals the kernel-
    pushed marginal at coordinate `n`. This is derivable from the
    existing `map_traj_succ_self` plus
    `map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`, but the
    derivation is ~80 lines of measure-theoretic plumbing. -/

/-- When all effects are Dirac on a deterministic step function and
the deterministic step preserves an inductive predicate `P`, the
predicate holds AE-always on the trace measure.

**Body status: documented `sorry`** — see file-section header. The
BrachaRBC-AS callers (§5–§7 in `Examples/Prob/BrachaRBC.lean`) reduce
to one-line applications of this helper; the helper signature is
pinned down by those callers.

Closing the body needs an n-step marginal lemma for
`Kernel.trajMeasure` that is currently missing from Mathlib v4.27.0
(see the section header for the precise gap). -/
theorem AlmostBox_of_pure_inductive
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {spec : ProbActionSpec σ ι}
    (P : σ → Prop)
    (det_step : ι → σ → σ)
    (h_pure : ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
        (spec.actions i).effect s h = PMF.pure (det_step i s))
    (h_step : ∀ (i : ι) (s : σ),
        (spec.actions i).gate s → P s → P (det_step i s))
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, P s)
    (A : Adversary σ ι) :
    AlmostBox spec A μ₀ P := by
  -- Mark the hypotheses as "intentionally unused" until the body lands
  -- (M3 polish). Keeping them in the signature so callers can already
  -- apply this lemma cleanly (see `BrachaRBC.brbProb_budget_AS`).
  let _ := h_pure
  let _ := h_step
  let _ := h_init
  -- AlmostBox unfolds to `∀ᵐ ω ∂traceDist, ∀ n, P (ω n).1`.
  -- By `MeasureTheory.ae_all_iff` this is `∀ n, ∀ᵐ ω, P (ω n).1`.
  -- For each `n`, the marginal of `traceDist` at coordinate `n` is the
  -- pushforward of `μ₀.map (·, none)` through `n` deterministic-Dirac
  -- kernel steps; the inductive `h_step`/`h_init` finish.
  --
  -- Body deferred — see section header for the missing Mathlib lemma.
  -- Concretely: we need `(trajMeasure μ₀_full (stepKernel ..)).map (eval n)`
  -- in a form usable by `filter_upwards`. With `_h_pure` plus the
  -- countable-AE swap, this reduces to a finite induction step that
  -- transports `P` along the deterministic kernel.
  sorry

/-! ### Refines_safe

If `Π` refines `Σ` (via `proj`) and `φ` holds always for `Σ`'s
trace (under projected predicates), then `φ` holds always for
`Π`'s trace.

Proof: extract the `Refines` witness `(μ₀', A')`, instantiate the
`AlmostBox`-on-Σ hypothesis there, then use `ae_map_iff` to push
the AE-event back through `Measure.map proj`. The state-component
identity `h_proj_state` lets us turn `φ ((proj ω) n).1` into
`(φ ∘ state_proj) ((ω n).1)`, which is exactly the Σ-side
hypothesis at index `n`.

The hypothesis is universally quantified over `(μ₀', A')` (with
`[IsProbabilityMeasure μ₀']` carried as an instance). This is
strictly stronger than the existential form but matches the
"safety holds for *every* abstract execution" reading and lets
us instantiate at the witness produced by `Refines`. -/

/-- Invariant `φ` on the abstract spec lifts (via projection) to
an invariant on the concrete spec. Requires measurability of
`proj` and of the predicate set; both are satisfied for our
discrete protocol settings. -/
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
    (h_proj_meas : Measurable proj)
    (state_proj : σ' → σ)
    (h_proj_state : ∀ (ω : Trace σ' ι') n, ((proj ω) n).1 = state_proj ((ω n).1))
    (φ : σ → Prop) (h_phi_meas : MeasurableSet {s : σ | φ s})
    (μ₀ : Measure σ) [hμ₀ : IsProbabilityMeasure μ₀]
    (A : Adversary σ ι)
    (h_box : ∀ (μ₀' : Measure σ') [IsProbabilityMeasure μ₀']
        (A' : Adversary σ' ι'),
        AlmostBox spec₂ A' μ₀' (φ ∘ state_proj)) :
    AlmostBox spec₁ A μ₀ φ := by
  obtain ⟨μ₀', hμ₀', A', h_eq⟩ := h_ref μ₀ hμ₀ A
  haveI : IsProbabilityMeasure μ₀' := hμ₀'
  have hbox' := h_box μ₀' A'
  -- Reduce to AE on the pushforward `Measure.map proj _`.
  unfold AlmostBox at hbox' ⊢
  rw [← h_eq]
  -- The predicate set `{ω | ∀ n, φ (ω n).1}` is measurable as a
  -- countable intersection of preimages of `{s | φ s}`.
  have h_pred : MeasurableSet {ω : Trace σ ι | ∀ n, φ (ω n).1} := by
    have heq : {ω : Trace σ ι | ∀ n, φ (ω n).1} = ⋂ n, {ω | φ (ω n).1} := by
      ext ω; simp
    rw [heq]
    exact MeasurableSet.iInter fun n =>
      (measurable_fst.comp (measurable_pi_apply n)) h_phi_meas
  rw [ae_map_iff h_proj_meas.aemeasurable h_pred]
  filter_upwards [hbox'] with ω' h_ae n
  rw [h_proj_state ω' n]
  exact h_ae n

end Leslie.Prob
