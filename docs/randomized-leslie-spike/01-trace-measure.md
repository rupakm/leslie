# M0.1 — Trace measure decision document

**Status.** In progress. Initial findings + recommendation; prototype
deferred to follow-up.
**Owner.** TBD.
**Budget.** ~5 days (per implementation plan v2.1 §M0).
**Blocks.** All M1 work; M0.3.

---

## The question

What is the type of `traceDist Π A` — the distribution over infinite
traces of `Π : ProbActionSpec σ ι` under adversary `A`?

Design plan v2 said `PMF (Trace σ ι)` where
`Trace σ ι := Stream' (σ × Option ι)`. Round-2 review claimed this is
not a real type.

## What Mathlib actually provides

After consulting Mathlib4 docs (April 2026), the situation is more
nuanced than v2's "PMF won't work" / round-2's "PMF can't host trace
distributions":

### `PMF α` (compiles, but operationally weak for traces)

`Mathlib.Probability.ProbabilityMassFunction.Basic`:

- `PMF α` is a subtype of `α → ℝ≥0∞` summing to 1. **`α` need not be
  countable.**
- However: `PMF.support_countable` is a `simp` lemma — for *any*
  `μ : PMF α`, `μ.support` is countable.

So `PMF (Stream' (σ × Option ι))` *type-checks*, but every inhabitant
has countable support. This means we cannot represent the distribution
over traces induced by even a single coin flip per step (which has
support of cardinality continuum). **Round-2 finding 1 is correct in
substance**: PMF on streams compiles, but only represents
operationally-trivial distributions.

### `ProbabilityTheory.Kernel α β` (the right primitive)

`Mathlib.Probability.Kernel.Basic`:

- `Kernel α β` = measurable function `α → Measure β` (plus
  measurability witness).
- Constructors: `deterministic`, `const`, `id`, `comapRight`,
  `piecewise`, `ofFunOfCountable`.
- `IsMarkovKernel κ` ⇔ each `κ a` is a probability measure.

Per-step transitions of `ProbActionSpec` (action choice composed with
effect PMF) are naturally a `Kernel σ σ`. PMF effects compose with the
adversary's history-deterministic schedule to give a measurable map
`History → Measure σ` per step.

### `Mathlib.Probability.Kernel.IonescuTulcea.Traj` (the trace-measure construction)

This is the headline finding: the construction we need is **already
in Mathlib**, formalized in 2025 (arXiv 2506.18616).

```lean
noncomputable def traj {X : ℕ → Type u₁}
  [∀(n : ℕ), MeasurableSpace (X n)]
  (κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
  [∀(n : ℕ), IsMarkovKernel (κ n)]
  (a : ℕ) :
  Kernel (Π i : Iic a, X i) (Π n, X n)
```

Given a family of one-step Markov kernels indexed by ℕ, `traj` produces
a kernel from finite-prefix initial conditions to measures on the
infinite product space. The projective-limit property
`(traj κ a).map (frestrictLe2 h_b) = partialTraj κ a b` characterizes
it as the unique extension.

For our setting `X n := σ × Option ι` is constant in `n`; we instantiate
`κ n` to the per-step transition kernel induced by the adversary
schedule + `ProbGatedAction.effect`. The output `Π n, X n` is
isomorphic to `Stream' (σ × Option ι) = Trace σ ι` (modulo a
`Stream'`-vs-`Pi` translation).

### `MeasureTheory.Martingale.Convergence` (Doob)

Doob's martingale convergence theorem is formalized in Mathlib (arXiv
2212.05578). Specifically the form we need —
"non-negative supermartingale converges almost surely to an
integrable limit" — is available. AST soundness is therefore *not*
gated on a Mathlib gap.

## Three options, re-evaluated

### Option A — `Measure (Trace σ ι)` via Ionescu-Tulcea (RECOMMENDED)

Define `traceDist Π A : Measure (Stream' (σ × Option ι))` by:
1. Constructing per-step kernel `κ_step Π A : Kernel (History σ ι) σ`
   from the adversary schedule + action effect.
2. Currying through the projective-limit: `κ_step` becomes a kernel
   `(Π i : Iic n, σ × Option ι) → σ × Option ι` family.
3. Applying `Kernel.traj` at index 0 with the initial state.
4. Pulling back along the `Stream'` ↔ `Π n` isomorphism.

**Pros.**
- Construction already in Mathlib; no shim needed.
- Proper measure-theoretic semantics; `□̃` (almost-sure box) and
  `◇̃` (almost-sure diamond) lift cleanly to events on the cylinder
  σ-algebra.
- Doob (and hence `ASTCertificate.sound`) applies directly.
- Unifies with UC composition (Hirt-Maurer adversaries naturally
  live as kernels).

**Cons.**
- `Π n, X n` ≠ `Stream'` syntactically; need a `Pi.streamEquiv`-style
  lemma. Should be ~30 lines.
- `noncomputable`, like all of Mathlib's measure theory. Tactic story
  for `Tactics/Prob.lean` must be measure-theoretic, not
  PMF-symbolic — this is a real consequence; see *Implications*
  below.
- Per-step kernel needs measurability witnesses. For a finite-state
  `ProbActionSpec` this is trivial; for general `σ` the user must
  prove `Measurable` for the transition.

### Option B — Truncated PMF + tail measure (REJECTED)

Define `traceDist^≤n : PMF (List (σ × Option ι))` for each `n` plus
a separate `tailMeasure` for liveness reasoning.

**Pros.** Keeps PMF in the type for finite-prefix reasoning.

**Cons.**
- Two parallel objects users must keep consistent.
- Liveness properties (◇̃, AST) cannot be stated against PMF; they
  end up against `tailMeasure` anyway, so PMF buys nothing.
- Coupling rules need duplicate statements (PMF version + measure
  version).

Reject. The supposed PMF benefit is illusory because every interesting
property is a tail/limit property.

### Option C — `MeasureTheory.ProbabilityMeasure` throughout (CANDIDATE)

Use `Measure` everywhere; PMF is just a convenient way to construct
finitely-supported measures.

**Pros.** Single object, no PMF/measure boundary.

**Cons.** Loses the discrete-symbolic ergonomics that pRHL / coupling
proofs benefit from. `coupling_bijection` over a finite Shamir
polynomial is much cleaner with PMF + `PMF.bind` than with measures
and Lebesgue integration.

**Synthesis.** Option A's form already gives us C's benefits at the
trace level (`traceDist` is a `Measure`) while preserving PMF for
single-step effects. So C is subsumed by A.

## Recommendation

**Option A.** Per-step effects stay `PMF` (good ergonomics for
single-step coupling proofs); trace distributions are `Measure` via
`Kernel.traj`. The PMF/Measure boundary is at "one step vs. many
steps" — semantically natural.

Concretely, the type signature changes from v2 are:

```lean
-- v2 (broken):
def traceDist (Π : ProbActionSpec σ ι) (A : Adversary σ ι) :
              PMF (Trace σ ι)

-- v2.1 / Option A:
def traceDist (Π : ProbActionSpec σ ι) (A : Adversary σ ι)
              [MeasurableSpace σ] [MeasurableSpace ι]
              (s₀ : σ) :
              Measure (Stream' (σ × Option ι))
```

Note the added `[MeasurableSpace σ]`, `[MeasurableSpace ι]`, and the
explicit initial state `s₀` (since `Kernel.traj` is parameterized on
the initial trajectory, not the initial distribution; for an initial
distribution `Π.init`, we additionally bind through it).

## Implications for the rest of the plan

If Option A is adopted, propagate:

1. **§"Discrete probability first" (design plan).** Soften: "Discrete
   probability for single-step effects; measure theory at the trace
   level. We do not need the *general* measure-theoretic stack
   (Lebesgue, Bochner integration), but we do need the
   product-measure / kernel-trajectory / martingale-convergence parts."

2. **`Refines` (§Composition combinators).** Change from
   `traceDist Π A = (traceDist Σ A').map projectStuttering` (PMF
   equality) to `Measure.map projectStuttering (traceDist Σ A') = traceDist Π A`
   — same idea, measure-level.

3. **`RelatedTraces` and coupling rules at trace level.** A coupling
   between two trace measures is a measure on the product space with
   the right marginals. Mathlib has `Measure.prod` and projection
   marginals; the coupling rules port over but with
   `MeasureTheory.Measure` instead of `PMF`. The coupling rules at
   the *step* level stay PMF-flavored.

4. **`ASTCertificate.sound` (§AST rule).** The supermartingale `V`
   becomes a measurable function `σ → ℝ≥0∞` (not just `σ → ℝ≥0`); the
   integration is against `traceDist Π A`. Doob's theorem in Mathlib
   covers this case.

5. **`Tactics/Prob.lean`.** Single-step tactics (`coupling_identity`,
   `coupling_bijection`, `coupling_swap`) operate on PMF. Trace-level
   tactics (`by_coupling` on full-trace claims) need to bridge from
   step-PMF reasoning to trace-Measure reasoning. The bridge is
   `Kernel.traj`'s functoriality: a step-level PMF coupling lifts to a
   trace-level Measure coupling.

6. **`MeasurableSpace` instances become a real ergonomic burden.** We
   will need standard instances on `σ × Option ι`,
   `Stream' (σ × Option ι)`, `History σ ι`. Most are already in
   Mathlib (`Prod.instMeasurableSpace`, `Option.instMeasurableSpace`,
   `Pi.measurableSpace`); the `Stream'` one may not be — verify in the
   prototype.

## Doob availability check

Per the Mathlib4 search:

- `Mathlib.MeasureTheory.Martingale.Convergence` formalizes Doob's
  martingale convergence theorem (arXiv 2212.05578).
- The non-negative supermartingale form: a non-negative supermartingale
  `M : ℕ → Ω → ℝ≥0∞` converges a.s. to a measurable limit.
- Filtration handling: `MeasureTheory.Filtration` is the standard
  setup; we will need to expose the natural filtration on
  `Stream' (σ × Option ι)` (the σ-algebra generated by the first `n`
  coordinates), which is straightforward — every cylinder σ-algebra
  has a canonical filtration.

**No shim needed.** This is a meaningful win: the Mathlib martingale
infrastructure is more developed than v2's "small shim … worst case
~200 lines" implied.

## Outstanding questions for the prototype

The decision is made; the prototype's job is to *verify* by building
the core construction end-to-end on a trivial example. Specifically:

1. **Does `Kernel.traj` instantiate cleanly when `X n` is constant in
   `n`?** Needs a wrapper or fresh definition; estimate ~30 lines.

2. **What does `Stream'` ↔ `Π n` look like in Mathlib?** Verify
   `Stream'` has `MeasurableSpace`; if not, define one via the
   coordinate projections (likely 50 lines).

3. **Coin-flip Markov chain** on `Bool` driven by a single action that
   flips with probability `1/2`: prove the marginal at step `n` is
   uniform on `Bool`. Target: ≤150 lines including the kernel
   construction. If it exceeds 250 lines, Option A is more painful
   than expected and we re-evaluate.

4. **AST soundness toy.** Statement-only stub of
   `ASTCertificate.sound` with `sorry` body; every obligation typed
   correctly under the new trace-measure type. Builds → exit gate
   passes.

5. **MeasurableSpace on `Adversary`.** The schedule
   `History σ ι → Option ι` must be measurable to compose with kernels.
   For history-deterministic adversaries this is automatic given
   measurable spaces on `σ` and `ι`; verify.

## Implications for M0 timeline

If Option A is adopted (and assuming the prototype goes through):

- M0.1 budget reduces from "decide between three options" to "verify
  Option A on a toy". Likely ~3 days of actual prototype work, not 5.
- M0.3 (AST soundness scaffolding) becomes near-trivial because Doob is
  available — likely 1 day, not 2.
- **M0.1 brings forward what was M1 W1 Day 1** (add Mathlib
  dependency). The prototype requires Mathlib; we can either
  - (a) add Mathlib in the spike branch and discard if the spike
    fails; or
  - (b) write the prototype as a standalone scratch file outside the
    project tree and copy results into the eventual M1 commit.
  Recommendation: (a). The spike is exactly the place to validate
  Mathlib pinning, cache behavior, and build times, and the cost of
  discarding is bounded.

## Decision

**Option A** (Measure + Ionescu-Tulcea kernel trajectory) is adopted
pending prototype verification.

If the prototype completes within budget, the design plan v2.1 should
be patched to:
- Replace `PMF (Trace σ ι)` with `Measure (Stream' (σ × Option ι))`
  in all trace-level signatures (§"`ProbActionSpec` and trace
  distributions" and downstream).
- Soften §"Design principles" item 2 ("Discrete probability first")
  to acknowledge measure theory at the trace level.
- Add `MeasurableSpace σ` / `MeasurableSpace ι` typeclass
  requirements where they were elided in v2.
- Cross-reference `Mathlib.Probability.Kernel.IonescuTulcea.Traj` and
  `Mathlib.MeasureTheory.Martingale.Convergence` in the §References.

If the prototype reveals a friction not anticipated here, this
document is the place to record the finding and revise.

## References

- [Mathlib.Probability.ProbabilityMassFunction.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ProbabilityMassFunction/Basic.html)
- [Mathlib.Probability.Kernel.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Basic.html)
- [Mathlib.Probability.Kernel.IonescuTulcea.Traj](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/IonescuTulcea/Traj.html)
- [Cauchy et al. — A Formalization of the Ionescu-Tulcea Theorem in Mathlib (arXiv:2506.18616)](https://arxiv.org/abs/2506.18616)
- [Degenne et al. — Markov kernels in Mathlib's probability library (arXiv:2510.04070)](https://arxiv.org/abs/2510.04070)
- [Pflanzer & Bentkamp — A Formalization of Doob's Martingale Convergence Theorems in mathlib (arXiv:2212.05578)](https://arxiv.org/abs/2212.05578)
