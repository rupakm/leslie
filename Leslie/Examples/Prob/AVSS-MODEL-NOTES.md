# AVSS model notes — relationship to Canetti–Rabin '93

`Leslie/Examples/Prob/AVSS.lean` formalises a **threshold-faithful abstraction** of Canetti–Rabin asynchronous verifiable secret sharing. The four classical theorems
(termination, correctness, commitment, secrecy) plus reconstruction (Option C)
are all proved axiom-clean. This document records the **structural assumptions
under which those theorems hold**, the **implicit adversary model**, and the
specific **literature gaps** that any reader should be aware of when
interpreting the formalised statements.

The aim is honest disclosure: nothing here weakens the formalised theorems'
internal validity, but several distinctions matter when comparing to the AVSS
literature or when AVSS is used as a primitive for downstream protocols.

## Quick summary of the gap

| Aspect | Canetti–Rabin literature | This formalisation |
|---|---|---|
| Adversary information | Rushing — sees corrupt-coalition view + in-flight messages | **Two adversary types coexist**: plain `Adversary` (full-state access; legacy) and `RushingAdversary` (view-restricted; Phase 7.1, generic in `Adversary.lean`). The classical AVSS theorems are restated against both (Phase 7.3) |
| Adversary *power* (what corrupt parties can do/observe) | Rushing adversary controls all corrupt-party messages and observes every honest broadcast on corrupt receivers; corrupt dealer can selectively short-share honest parties; adversary may flip coins | ⚠ **Strictly weaker.** Corrupt parties cannot send echoes/readys/amplify (C1); they never receive honest echoes/readys (C2); selective non-broadcast not modelled — `dealerShare` always sends to all honest parties (C4); all theorems quantify only over deterministic adversaries (C5). C3 (dealer-share fairness) **resolved by Phase B**. See **§11**, plans in **§12 (Phase 8)** and **§13 (Phase 9)** |
| Static vs. adaptive corruption | Both treated; usually adaptive | Static (`corrupted` fixed at `μ₀` time) |
| Dealer-to-party communication | Per-party row + column polys, possibly inconsistent under corrupt dealer | Single global `s.coeffs` field; consistent by construction |
| Dealer's distribution choice | Honest = uniform of bidegree ≤ (t,t) with `f(0,0) = sec`; corrupt = adversarial | **`Polynomial.uniformBivariateWithFixedZero` is degenerate** — fixes all axis coefficients to 0, not just `f(0,0)`. Honest output equals `sec` directly (every share is `sec`), and corrupt-party row poly's constant term is `sec`. See §10 below |
| Secrecy granularity | Trace-level on corrupt parties' actual observable view | Trace-level on the **algebraic ideal grid** `bivEval coeffs ...` at non-axis points (axis points are degenerate by point above). Operational view secrecy is **vacuously true** under the degenerate distribution — see §9–§10 |
| Network model | Asynchronous with arbitrary delays, point-to-point messages | `Finset`-based in-flight queues; eventual delivery via fairness |
| Cryptographic strength | Information-theoretic | Information-theoretic (aligned in design) |

The formalisation is sound and useful as a stepping stone, but the gap between
its statements and the literature's statements is non-trivial.  Consumers of
this module should consult the relevant section below before relying on a
particular property.

✅ **Distribution refactor landed (Phase 7.7).** As of the polynomial
refactor PR (Phase 7.7), `avssInitMeasure` no longer couples to the
degenerate `Polynomial.uniformBivariateWithFixedZero`.  Instead it
uses `Polynomial.uniformBivariateFullWithFixedZero` — a true
uniform bivariate of bidegree ≤ (t, t) with **only** the `(0, 0)`
constant pinned to `sec`.  Under the new distribution
`f(α_p, 0) = sec + ∑_{i ≥ 1} coeffs(i, 0) · α_p^i` is a genuine
degree-`t` Shamir polynomial in `α_p`, so the per-party operational
content of `avss_correctness_AS`, `avss_commitment_AS`, and
`avss_reconstruction` is no longer trivially-`sec`.  The
conditional operational-secrecy theorems
(`avss_secrecy_AS_view_conditional`,
`avss_secrecy_AS_view_rushing_via_aux`)' `h_aux` becomes provable in
principle (Phase 7.4 inductive AE-bridge remains the substantive
~300–500 LOC follow-on work).  See §10 below for the per-theorem
"after refactor" semantics; §9's audit is preserved for historical
context.

## 1. Adversary model

### Literature

Canetti–Rabin and the broader AVSS literature analyse the protocol against a
**rushing adversary**.  Concretely: each round, the adversary sees

- all corrupt parties' local states,
- all messages currently in transit (including those sent this round),
- the schedule history,

and chooses, in arbitrary order:

- which messages to deliver next (asynchrony),
- what each corrupt party does this round (since the adversary controls them),
- when to corrupt new parties (in adaptive variants).

Crucially the adversary does **not** see honest parties' internal state —
only what's in messages they emit.  Secrecy claims hold against this strongest
admissible adversary.

### This formalisation

Two adversary types are now formalised side-by-side in
`Leslie/Prob/Adversary.lean`:

  * `Adversary σ ι` (legacy): a strategy
    `List (σ × Option ι) → Option ι` whose decision is conditioned on the
    full state-history.  This is the type the original M2/M3 theorems and
    PRs #25–#33 are written against, and it persists for backwards
    compatibility.

  * `RushingAdversary σ ι V` (**Phase 7.1**, generic): bundles a
    `ProtocolView σ V` (i.e. a projection `view : σ → V`) with a
    *view-restricted* schedule `List (V × Option ι) → Option ι` and a
    static corruption set.  An adapter `RushingAdversary.toAdversary`
    lifts every rushing adversary back to a plain `Adversary σ ι`,
    consulting `view` on the state-component of each history entry
    before invoking the rushing schedule.  Equivalently:
    `R.toAdversary.schedule h = R.schedule (h.map (R.view × id))`
    (rfl-simp lemma `toAdversary_schedule` in `Adversary.lean`).

The AVSS instantiation (`avssCoalitionView corr`, **Phase 7.2**, in
`AVSS.lean §19`) takes `V := corr → AVSSLocalState n t F` — the corrupt
coalition's per-party local-state projection, generalising the existing
`coalitionView` (Phase 5/6) from a size-`t` `BivariateShamir.Coalition`
to an arbitrary `Finset (Fin n)`.

Two practical consequences for downstream reasoning:

1. **Plain `Adversary` still has read access to the full state.**  This
   was already true before Phase 7 and is unchanged: the adversary's
   strategy can, in principle, branch on `s.coeffs` and on honest
   parties' `local_` fields.  Operational secrecy in the
   plain-adversary world is therefore caveated — see Phase 6's
   `avss_secrecy_AS_view` (PR #33) and its joint marginalisation with
   the schedule.

2. **`RushingAdversary` strictly restricts adversary information,
   but is also message-restricted and reception-restricted relative
   to CR.**  Under a `RushingAdversary R`, the adversary's strategy
   is — by construction — a function only of the view-history
   `(R.view of state, action)`-pairs.  It *cannot* branch on
   `s.coeffs`, on honest parties' internal state outside the view, or
   on anything else outside `corr → AVSSLocalState`.  This is the
   information half of the literature-standard rushing adversary.

   ⚠ The *capability* half is **strictly weaker than CR's**: in this
   model corrupt parties cannot send echoes/readys/amplify (C1) and
   never receive honest echoes/readys (C2).  See **§11** below for
   the full statement of these restrictions and their operational
   implication for the secrecy claim.

3. **The classical AVSS theorems re-prove against `RushingAdversary`.**
   `avss_termination_AS_fair_rushing`, `avss_correctness_AS_rushing`,
   `avss_commitment_AS_rushing` (**Phase 7.3**) are thin wrappers that
   invoke their plain-`Adversary` counterparts on `R.toAdversary`.
   Termination requires a `TrajectoryFairAdversary` witness for
   `R.toAdversary`, threaded explicitly; correctness and commitment are
   universal in the adversary so the wrapping is purely mechanical.

4. **Static corruption only.**  Unchanged from before Phase 7:
   `corr : Finset (Fin n)` is part of the initial state and never
   changes.  The standard literature reduction "static ⇒ adaptive"
   applies, so adaptive variants follow but require additional model
   machinery (corruption events).

### Implication for the formalised secrecy theorem

`avss_secrecy_AS` says: under any `Adversary`, the trace marginal of the
algebraic grid `coalitionGrid C D (ω k).1` is invariant in the secret.

This is sound because `coalitionGrid` is a function of `s.coeffs` and
`s.partyPoint` only (not of the adversary's strategy), and `s.coeffs` and
`s.partyPoint` are immutable across actions.  So the theorem doesn't actually
exercise the adversary's strategy at all — it's effectively the polynomial-
level secrecy `bivariate_shamir_secrecy` lifted through `μ₀`.

A literature-faithful operational secrecy theorem (Phases 6–7, see
"Future directions" below) requires four pieces:

- ✅ A new `RushingAdversary` type whose strategy is a function of *only* the
  corrupt-coalition view (Phase 7.1, **landed**).
- ✅ AVSS instantiation `avssCoalitionView` projecting onto corrupt
  parties' `local_` (Phase 7.2, **landed**).
- ✅ Re-proving termination / correctness / commitment against the new
  adversary type (Phase 7.3, **landed** — `*_rushing` variants of the
  classical theorems).
- ✅ A *cryptographic-core* lemma "schedule prefix factors through the
  coalition's algebraic view" (Phase 7.4, **landed**) and the
  composition `avss_secrecy_AS_view_rushing` (Phase 7.5, **landed** —
  fully unconditional in §19.4.5; intermediates
  `avss_secrecy_AS_view_rushing_via_aux` and
  `avss_secrecy_AS_view_rushing_via_init_invariant` retained)
  that closes the schedule-leakage caveat from Phase 6 by discharging
  the `h_aux` hypothesis of `avss_secrecy_AS_view_conditional`.  The
  proof is an inductive argument on `k` showing that, under the rushing
  adversary, the schedule at step `k+1` is a deterministic function of
  the corrupt-coalition view at steps `0..k`.  See **§9. Phase 7.4–7.5
  deferral** below for the precise statement and architectural
  rationale.
- ⏳ Replacing `s.coeffs` with per-party dealer messages (separate
  refactor; cf. §2 below) so the dealer's inputs are
  scheduling-time data, not background state (Phase 8 territory).

## 2. Dealer-to-party communication

### Literature

The dealer in Canetti–Rabin sends each party `i`:

- the row polynomial `f_i(y) = f(α_i, y)` (degree-`t` univariate in `y`),
- the column polynomial `g_i(x) = f(x, α_i)` (degree-`t` univariate in `x`).

Parties verify *consistency* via echoes: party `i` sends to each `j` the
single value `f_i(α_j)`, and `j` checks `f_i(α_j) = g_j(α_i)`.  The Bracha
echo/ready amplification is precisely how this consistency check is
distributed.  Echoes carry **payloads** (the field elements) — they're not
just control messages.

### This formalisation

`AVSSState.coeffs : Fin (t+1) → Fin (t+1) → F` is a single global field.
`partyDeliver q` writes `rowPolyOfDealer s.partyPoint s.coeffs q` (the row
polynomial) into `(s.local_ q).rowPoly`.  No column polynomial is modeled.

`partyEchoSend q` and `partyEchoReceive p q` carry **no payload** — they're
control messages that just record "q has echoed" / "p has received q's echo".
Bracha amplification fires based on counts (≥ n−t echoes received → ready
phase), not on agreement of echoed values.

### Implication

The model **trivially makes the dealer consistent**: a corrupt dealer in our
model still distributes a single coherent bivariate polynomial because there
*is* only one polynomial in the state.  Real-world AVSS verifies dealer
consistency precisely because a corrupt dealer might send different `f_i`'s
that don't fit a single bivariate polynomial — and the protocol detects this.

`avss_commitment_AS` proves "every honest output is a value of `bivEval
s.coeffs ...`".  Under our abstraction this is true by construction; the
literature's commitment theorem says something genuinely harder ("the
adversary can't fool honest parties into outputting values inconsistent with
*any* single bivariate polynomial").  See **Future directions** below for
what a faithful commitment story would require.

## 3. Honest dealer's distribution

### Literature

Honest dealer = chooses `f` uniformly at random from bidegree-`≤ (t,t)`
bivariate polynomials with `f(0,0) = sec`.  Corrupt dealer = chooses `f`
adversarially (subject only to the protocol's verifiability checks).

### This formalisation

Both the honest and corrupt dealer cases use the same `μ₀` distribution on
`s.coeffs`.  Phase 5 Layer B (`avssInitMeasure`) couples to
`uniformBivariateWithFixedZero t t sec` for both honest and corrupt cases.
The `s.dealerHonest` flag distinguishes them but doesn't change the
distribution.

### Implication

Our `avss_correctness_AS` (honest dealer ⇒ honest output = `bivEval coeffs
(partyPoint p) 0`) reads as expected.

`avss_commitment_AS` is correctly stated for any (honest or corrupt)
dealer's `coeffs` — but since `μ₀` samples uniformly in both cases, we don't
quite capture "the adversary's choice of `coeffs` was constrained by what the
protocol's verifiability allows".  The literature commitment is a *forall
adversary* statement quantifying over the dealer's input distribution; ours
is *for the fixed `μ₀` we chose*.

In a faithful refactor, the dealer's polynomial would be part of the
adversary's input (in the corrupt-dealer case), and `μ₀` would be replaced
by an adversary-chosen distribution subject to verifiability.

## 4. Secrecy granularity

### Literature

"`t`-coalition view secrecy" means: the *joint distribution* of everything
the corrupt parties observe — their local state, every message they've
received, every protocol decision they've made — is invariant in the
secret.

### This formalisation

Two distinct secrecy theorems are formalised:

- `avss_secrecy` (PR #31): polynomial-level grid form.  Distribution of the
  coalition's grid evaluations of `f` is invariant in `sec`.  Pure algebra,
  no protocol semantics.

- `avss_secrecy_AS` (PR #32, with Phase 5 Layer E step-`k` extension):
  trace-level grid form at any step `k`.  Marginal of `coalitionGrid C D (ω
  k).1` under `traceDist` is invariant in `sec`.  Crucially,
  `coalitionGrid` is the **algebraic ideal** — it's a function of `s.coeffs`
  and `s.partyPoint` only, not of corrupt parties' actual `local_`.  Since
  `s.coeffs` and `s.partyPoint` are immutable, the step-`k` and step-0
  versions agree pointwise, and both reduce to the polynomial-level theorem.

- Operational view secrecy at the corrupt-coalition's actual observable
  state (`coalitionView` projecting onto `local_` fields) is formalised
  in conditional form: `avss_secrecy_AS_view_conditional` (PR #33) and
  `avss_secrecy_AS_view_rushing_via_aux` (PR #35) both take an auxiliary
  hypothesis `h_aux` about joint marginal invariance of
  `(coalitionAlgebraicView, schedulePrefix)`.  ⚠ Under the current
  polynomial distribution this hypothesis is **provably false**; see
  §9 and §10.  The conditional theorems hold vacuously and do not
  carry useful operational content until §10's distribution refactor
  lands.

### Implication

`avss_secrecy_AS` is well-named only with the qualifier *"of the algebraic
grid view at non-axis points"*.  It's a meaningful step (it lifts the
polynomial-level secrecy through the `traceDist` infrastructure) but it
doesn't say anything about what corrupt parties *operationally* observe.
The conditional theorems that target the operational view (`coalitionView`
projecting `local_` including `rowPoly`) are vacuously true because of
§10 — the constant term of every honest party's row poly is exactly
`sec` under the current degenerate distribution, observable to any
corrupt party that runs `partyCorruptDeliver`.

The upshot: until §10 lands, **the only meaningful trace-level secrecy
statement we have is at the algebraic grid view, not the operational
local-state view**.

(Phase 7.7 has now landed §10's distribution refactor, so the
operational view-secrecy theorem `avss_secrecy_AS_view_rushing` does
hold.  But its rushing adversary is the *view-restricted, message-
restricted, reception-restricted* one of §11 — see **§11** for what
that means concretely and why a literature-faithful version is still
Phase 8 territory.)

## 5. Network model

### Literature

Asynchronous = arbitrary message delays, but every message eventually
delivers.  Adversary controls delivery scheduling.  Echoes and readys are
point-to-point messages with adversary-controlled order.

### This formalisation

`AVSSState.inflightEchoes : Finset (Fin n × Fin n)` and `inflightReady :
Finset (Fin n)` are abstracted as **sets** of pending messages.  Schedule
fairness (`avssFair`) models eventual-delivery: under fair scheduling, every
in-transit message is eventually delivered.

### Implication

Two minor abstractions:

- **Set, not multiset.**  Real networks allow message duplication.  For AVSS
  this doesn't matter (semantics are idempotent — `partyEchoReceive p q`
  is no-op if `q ∈ (s.local_ p).echoesReceived`), but it's a quiet
  simplification.

- **Order.**  Sets are unordered; real networks have arbitrary delivery
  order, which the schedule abstracts.  Our model captures this via the
  adversary's free choice of which `partyEchoReceive p q` action to fire
  next — equivalent in the limit.

Network model is the most faithful aspect of the abstraction.

## 6. Cryptographic setting

### Literature

Two branches:

- **Information-theoretic AVSS** (Canetti–Rabin '93): unconditional
  guarantees, no cryptographic assumptions.
- **Computational AVSS** (Pedersen, AVSS-via-commitments, etc.):
  game-based proofs against polynomial-time adversaries.

### This formalisation

Information-theoretic (aligned with Canetti–Rabin).  All theorems are
unconditional.

### Implication

Aligned with the Canetti–Rabin branch.  Computational AVSS would require a
different machinery (game-based reductions, polynomial-time adversary
restrictions) that our framework doesn't provide.

## 7. Reconstruction agency

### Literature

Reconstruction is performed by parties cooperating: they exchange shares,
run Lagrange interpolation, detect cheating during reconstruction.

### This formalisation

`avss_reconstruction` (Option C) is a math-level theorem: given `t+1`
honest shares with distinct `partyPoint`s, Lagrange returns `s.coeffs 0 0`.
There's no operational reconstruction phase modeled.

### Implication

Standard abstraction (similar to many other formalisations).  A faithful
reconstruction phase would add new actions to `AVSSAction` (e.g.,
`partyShareSend`, `partyReconstruct`).  Probably ~100 LOC; the cryptographic
content is already in the algebra so the operational lift is mostly
plumbing.

## What's *correctly* captured

Lest the above read as a litany of caveats, here's what the formalisation
*does* nail down rigorously:

- **Termination under fairness**: `avss_termination_AS_fair`, reduced to
  the structural sublevel-finite-variant rule, axiom-clean.  This holds
  against *any* adversary in our model — the strongest admissible since
  termination is a liveness property unaffected by adversary information.

- **Per-party share computation**: `avss_correctness_AS` rigorously proves
  that for an honest dealer, every honest output is `bivEval s.coeffs
  (s.partyPoint p) 0`.  This is the actual Canetti–Rabin specification (vs.
  the simpler `coeffs 0 0` rule used in `AVSSAbstract.lean`).

- **Output-determined-by-coeffs**: `avss_commitment_AS` proves that *given
  our model*, every honest output is determined by `s.coeffs` regardless of
  dealer honesty.  Useful for downstream reasoning that consumes AVSS
  abstractly (without caring about dealer-side malice).

- **Reconstruction algebra**: `avss_reconstruction` is a clean Lagrange
  interpolation theorem.  Stands as a mathematical fact independent of the
  protocol model.

- **Polynomial-level secrecy**: `avss_secrecy` (and the trace-lifted
  `avss_secrecy_AS`) cleanly reduces to `BivariateShamir.bivariate_shamir_-
  secrecy` — the cryptographic core is preserved.

- **Operational μ₀ coupling** (Phase 5 Layer B): `avssInitMeasure` couples
  the protocol's initial state distribution to
  `uniformBivariateWithFixedZero t t sec`.  This is the structural anchor
  for any future stronger secrecy theorem.

- **Algebraic-grid invariance under all actions** (Phase 5):
  `avssStep_coalitionGrid_invariant`.  This is the key structural fact that
  enables the step-`k` lift.

## 9. Phase 7.4–7.5 partial closure — schedule-leakage closing theorem

### What Phases 7.4–7.5 deliver

Phase 7 closes the rushing-adversary *type machinery* and classical-
theorem wrappers (Phases 7.1–7.3, **landed**) plus the schedule-leakage
half of the headline (this section, **landed**):

  * **Phase 7.4 simulate machinery (landed).** AVSS.lean §19.2
    introduces `avssSimulateRev`, `avssSimulateTrace`, and
    `avssSimulateNext`: a deterministic per-step simulation of the
    AVSS trace under a `RushingAdversary` whose effects are
    `PMF.pure` and whose schedule is a deterministic function of the
    view-history.  Plus structural lemmas: list length, head, succ
    recurrence, `avssSimulateRev_reverse_eq_ofFn` (index-form
    characterisation matching `FinPrefix.toList`).
  * **Phase 7.4 inductive AE-bridge (landed).** AVSS.lean §19.2.4
    proves `traceDist_AE_eq_avssSimulateTrace`: under `R.toAdversary`,
    every step's trace AE-equals `avssSimulateTrace R (ω 0).1` at
    that step.  Threads the marginal recurrence
    `Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`
    through the per-step Dirac kernel (each branch is Dirac by
    `PMF.pure` on the effect side and by Dirac on stutter branches),
    using a strong induction-form
    `traceDist_AE_eq_avssSimulateTrace_strong` over the entire
    prefix.  Per-prefix Dirac-identification lemma
    `avssSpec_R_stepKernel_AE_simulate` factors the kernel through
    the simulate's `avssSimulateNext` under prefix-matching
    hypothesis.
  * **Phase 7.4 joint factoring (landed).** AVSS.lean §19.2.5 defines
    `simAlgebraicView` and `simSchedulePrefix` as deterministic
    functions of `s_0`, then proves
    `coalitionAlgebraicView_schedulePrefix_AE_eq_sim` (AE form) and
    `traceDist_algebraicView_schedulePrefix_factors_AE` (pushforward
    form).  Combined with the step-0 state marginal
    (`traceDist_step_zero_state_marginal`, PR #32), expresses the
    trace-level joint marginal as a pushforward of the initial
    measure through `(simAlgebraicView, simSchedulePrefix)` —
    `traceDist_jointMarginal_eq_init` (§19.4).
  * **Phase 7.5 (thin composition, landed).** AVSS.lean §19.3
    introduces `avss_secrecy_AS_view_rushing_via_aux`, a thin wrapper
    around PR #33's `avss_secrecy_AS_view_conditional` that plugs in
    `R.toAdversary` for the underlying adversary.  Hypothesis
    `h_aux` (trace-level joint marginal invariance) is reduced to
    `h_init_invariant` (initial-measure pushforward invariance) via
    `traceDist_algebraicView_schedulePrefix_invariant` (§19.4).
  * **Phase 7.4 headline (landed).** AVSS.lean §19.4 introduces
    `avss_secrecy_AS_view_rushing_via_init_invariant`, taking
    `h_init_invariant` (a polynomial-level initial-measure
    invariance) as a hypothesis instead of the abstract trace-level
    `h_aux`.  Composed with the row-poly secrecy lemma, §19.4.5
    discharges `h_init_invariant` and yields the canonical
    fully-unconditional headline `avss_secrecy_AS_view_rushing`.

### What's still deferred (algebraic-core row-poly secrecy)

The single piece remaining for a fully unconditional headline:

  * **Algebraic-core row-poly secrecy (~+200 LOC).**  The
    polynomial-manipulation strengthening of
    `BivariateShamir.bivariate_shamir_secrecy_full` that lifts the
    grid-pointwise theorem (sec-invariant for `|C| × |D|`
    bivariate-evaluations with `|C|, |D| ≤ t`) to a *row-poly*
    form (sec-invariant for `|S|` row polynomials at corrupt
    coalition `S` with `|S| ≤ t`, each row poly a `Fin (t+1) → F`
    vector of coefficients).  This is what's needed for
    `(simAlgebraicView, simSchedulePrefix)`'s initial-measure
    pushforward to be sec-invariant.

    Concretely: under `uniformBivariateFullWithFixedZero t t sec`
    (PR #36), for any `S : Finset (Fin n)` with `S.card ≤ t` and
    `partyPoint` avoiding zero, the joint distribution of
    `(rowPolyOfDealer partyPoint (polyToCoeffs f) q)_{q ∈ S}` is
    uniform on `S → Fin (t+1) → F` — and hence sec-invariant.
    Sketch: decompose `uniformBivariateFullWithFixedZero` into
    independent column polynomials `g_l(x)` for `l ∈ Fin (t+1)`;
    `g_0` has Shamir-secret structure with secret `sec` (uniform
    by `evals_uniform`), `g_l` for `l ≥ 1` is fully uniform.
    Combine via product-of-uniforms.

    Modular composition: when this lemma lands as a separate PR,
    `h_init_invariant` becomes provable via
    `traceDist_jointMarginal_eq_init` plus the row-poly secrecy
    plus the structural fact that `(simAlgebraicView,
    simSchedulePrefix)` factors through `(rowPolyOfDealer at corr)`
    (provable via simulate's view-history-only dependence).

This piece has landed (`bivariate_shamir_secrecy_rowPoly_full`),
discharging `h_init_invariant` and yielding the canonical
literature-faithful operational secrecy theorem
`avss_secrecy_AS_view_rushing` under the AVSS state model —
completing Phase 7.

### Why "row-poly secrecy" is *structurally false* under the current distribution (audit, 2026-05-04)

A direct attempt to discharge `h_aux` under the current AVSS
distribution **cannot succeed**, and the obstruction is at the
distribution-design level, not the proof-engineering level.  Recording
the audit here so a future attempt does not repeat it.

**Observation.**
`Polynomial.uniformBivariateWithFixedZero t t sec` (the distribution
that `avssInitMeasure` couples to) is **not** the standard "uniform
polynomial of bidegree ≤ (t, t) with `f(0, 0) = sec`".  Its def at
`Leslie/Prob/Polynomial.lean:247–253` is:

```
(PMF.uniform (Fin dx → Fin dy → F)).map fun coefs =>
    Polynomial.C (Polynomial.C s) +
      ∑ i : Fin dx, ∑ j : Fin dy,
        Polynomial.C (Polynomial.C (coefs i j)) *
          Polynomial.X ^ (i.val + 1) *
          (Polynomial.C Polynomial.X) ^ (j.val + 1)
```

Every monomial in the sum has both `X`-degree `≥ 1` *and* `Y`-degree
`≥ 1`.  So all "axis" coefficients are forced to zero except the
constant `(0, 0)` — which is `sec`.  Concretely:

  * `coeffs(0, 0) = sec`
  * `coeffs(k, 0) = 0` for every `k ≥ 1`
  * `coeffs(0, l) = 0` for every `l ≥ 1`
  * `coeffs(k, l)` for `k, l ≥ 1` is uniform random

Equivalently, `f(x, 0) = sec` for **all** `x`, and symmetrically
`f(0, y) = sec`.  This is why `Polynomial.bivariate_evals_uniform`
carries the `0 ∉ pts_x ∪ pts_y` precondition: the axes are constants
of `sec`, not uniformly distributed, and the proof's
`step1 ∘ step2` factoring relies on the off-axis-only structure.

**Consequence for `coalitionAlgebraicView.1`.**
`rowPolyOfDealer pp coeffs p l = ∑_k coeffs(k, l) · pp(p)^k`.  At
`l = 0` this evaluates to

```
rowPolyOfDealer pp coeffs p 0 = coeffs(0, 0) + ∑_{k ≥ 1} coeffs(k, 0) · pp(p)^k = sec
```

— **identically `sec` for every party `p`**.  Hence the `l = 0` row of
`(coalitionAlgebraicView C ω k).1` is `Dirac (sec, sec, …, sec)` and

```
(traceDist sec).map (fun ω => coalitionAlgebraicView C ω k)
≠
(traceDist sec').map (fun ω => coalitionAlgebraicView C ω k)
   for sec ≠ sec'
```

so `h_aux` of `avss_secrecy_AS_view_conditional` is **false** under
the current distribution whenever `sec ≠ sec'`.  The conclusion of
the conditional is also false (since the operational `coalitionView`
stores the full `rowPoly`, including the leaked `sec` constant).
The conditional theorem holds vacuously (its hypothesis is false),
not as a discharge target.

**The fix is in the distribution, not the proof.**
A literature-faithful row-poly secrecy needs:

  1. A **true** uniform bivariate `f` of bidegree ≤ (t, t) with the
     single constraint `f(0, 0) = sec` — i.e., all `(t + 1)² − 1`
     other coefficients independently uniform in `F`.  Under that
     distribution `f(x, 0)` is a Shamir polynomial in `x` with secret
     `sec`, so by univariate Shamir secrecy `(f(x_p, 0))_{p ∈ corr}`
     for `corr.card ≤ t` and distinct nonzero `partyPoint`s has
     sec-invariant marginal — the row poly's constant is no longer
     constant-`sec`.
  2. Re-prove `bivariate_evals_uniform` under that distribution.  The
     existing factoring (`step1 ∘ step2`) does not apply; a
     Vandermonde + Lagrange argument does.
  3. Re-prove `BivariateShamir.bivariate_shamir_secrecy_pts` against
     the new distribution (it currently calls
     `bivariate_evals_uniform` directly).
  4. Migrate `avssInitState ∘ polyToCoeffs` to the new distribution
     so `s.coeffs` carries the random axis coefficients (which then
     propagate into `rowPolyOfDealer p 0`).

**Scope.**
Step 1 lives in `Leslie/Prob/Polynomial.lean` (owned).
Step 2 lives in `Leslie/Prob/Polynomial.lean` (owned).
Step 3 lives in `Leslie/Examples/Prob/BivariateShamir.lean`
(**read-only** per the worker brief), so completing the chain in a
single PR violates the constraint.  An additive path that adds
`uniformBivariateFullWithFixedZero` and a parallel proof family
without modifying `BivariateShamir.lean` is feasible (≈ 250–400 LOC)
but lives in parallel to the existing infrastructure and requires a
separate `avssInitMeasureFull` plus an alternate conditional /
headline; it has not been pursued in this PR-set.

**Bottom line.**
The "+200 LOC algebraic-core" deferral cannot be discharged purely
inside `BivariateShamir.bivariate_shamir_secrecy`'s grid form: the
row-poly form is provably false under the current distribution, and
the fix requires a distribution change that crosses an off-limits
file.  Either the worker brief's read-only constraint on
`BivariateShamir.lean` needs to be lifted, or the additive
parallel-distribution path described above needs to be sanctioned,
before this work item can be closed.

### Original deferral (kept for context)

The original deferral note from before this PR-set is preserved in
the project's git history; the precise statement of what was deferred
and the proof outline below still apply to the remaining work.

### Precise statement of the gap

PR #33's `avss_secrecy_AS_view_conditional` (Phase 6.3) discharges the
operational view-secrecy theorem *given* a hypothesis

```
h_aux :
  (traceDist sec).map (fun ω => (coalitionAlgebraicView C ω k, schedulePrefix ω k)) =
  (traceDist sec').map (fun ω => (coalitionAlgebraicView C ω k, schedulePrefix ω k))
```

i.e. the joint marginal of (algebraic-coalition view, schedule prefix)
at step `k` is invariant in the secret.  Under a plain `Adversary`,
`h_aux` is **not unconditionally true** — the adversary's strategy may
branch on `s.coeffs` and thereby leak `sec`-bits via its scheduling
decisions, so the joint marginal can differ between `sec` and `sec'`.

Under a `RushingAdversary R` with `R.toAdversary` plugged into
`traceDist`, the schedule is by construction a deterministic function
of the corrupt-coalition view-history.  Combined with Phase 6.2's
bridge (corrupt local states factor through `algebraicView`) and
Phase 5 step-`k` algebraic-view secrecy, this forces `h_aux` to hold.
The theorem `avss_secrecy_AS_view_rushing_via_aux` then follows by
`apply avss_secrecy_AS_view_conditional`; composition with the
initial-measure invariance (§19.4) and the row-poly secrecy lemma
(§19.4.5) yields the canonical fully-unconditional
`avss_secrecy_AS_view_rushing`.

### Why the proof is non-trivial

The composition outlined above looks short, but the underlying
factoring lemma "the schedule prefix at step `k` AE-equals a
deterministic function of the algebraic-coalition view at step `k`"
(Phase 7.4's substantive form) is a genuine inductive argument on `k`
threaded through the Ionescu–Tulcea trace-measure construction.
Concretely:

  * At each step `i < k` the action that fires is
    `R.toAdversary.schedule (history)` gated by
    `(spec.actions ·).gate (state at step i)`.
  * The rushing-restricted schedule depends only on view = corrupt
    local states (Phase 7.1's structural lemma).
  * Phase 6.2's bridge (`coalitionView_corrupt_factors_AE`) shows
    corrupt local states are determined by the algebraic view AE.
  * AVSS gates (after inspection) do *not* depend on `s.coeffs` —
    they read state-flags (`delivered`, `echoSent`, `dealerSent`,
    etc.) plus `partyPoint` / `dealerHonest` / `corrupted`, all
    invariant under sec.  Thus gate evaluation factors through the
    non-secret state evolution, which itself factors through schedule
    history.

Putting these together via the Phase 5 inductive template (the
`Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`
recurrence used in `traceDist_coalitionGrid_AE_eq_init`) yields the
desired AE-factoring.  Conservatively this is ~300–500 LOC of
inductive proof plus auxiliary measurability and state-evolution
plumbing.

### Path forward

The deferred work is well-defined: the proof outline above identifies
all the structural ingredients, every one of which is already
formalised in the current branch.  The remaining work is *only*
inductive-proof engineering, with no new cryptographic content to
discover.  A follow-up PR should:

  1. Define `nonSecretState` (the state projection excluding
     `s.coeffs`) and an induction-friendly evolution lemma.
  2. State `RushingAdversary.schedulePrefix_factors_through_view_AE`
     in `AVSS.lean` (or a new `Leslie/Prob/RushingAdversary.lean`
     file) using the algebraic-view type.
  3. Prove by induction on `k` using the Phase 5 template.
  4. Compose with PR #33's `avss_secrecy_AS_view_conditional` to
     deliver `avss_secrecy_AS_view_rushing` — the literature-faithful
     operational secrecy theorem.

This unblocks the headline operational-secrecy theorem; once landed,
the only remaining gap (relative to a literature-faithful AVSS) is
per-party dealer messages (§2 above) — the classical "row + column
secrecy" formulation which `BivariateShamir`'s deferred +200 LOC
polynomial-manipulation work will eventually supply.

## 10. Distribution refactor (✅ landed Phase 7.7)

§9's audit identified that `Polynomial.uniformBivariateWithFixedZero`
is degenerate — every random monomial has both `X`-degree ≥ 1 and
`Y`-degree ≥ 1, forcing all axis coefficients to zero and making
`f(x, 0) = sec` for all `x`.  This blocked the operational-view
secrecy story at the polynomial level.

This section records the **distribution refactor** that
unblocked the chain (now landed as Phase 7.7).

### Target distribution

```lean
noncomputable def uniformBivariateFullWithFixedZero (dx dy : ℕ) (s : F) :
    PMF (Polynomial (Polynomial F)) :=
  -- (PMF.uniform (Fin (dx+1) → Fin (dy+1) → F)).map fun coefs =>
  --   ∑ i, ∑ j,
  --     Polynomial.C (Polynomial.C (if (i, j) = (0, 0) then s else coefs i j))
  --       * X^i.val * (C X)^j.val
  ...
```

i.e., a true uniform bidegree-`(dx, dy)` bivariate polynomial with
**only the `(0, 0)` coefficient pinned to `s`** and all other
`(dx + 1) * (dy + 1) - 1` coefficients independently uniform.

Under this distribution, `f(α_p, 0) = ∑_k coeffs(k, 0) · α_p^k` is a
genuine degree-`dx` Shamir polynomial in `α_p` with constant term
`coeffs(0, 0) = s`.  For any `t` distinct nonzero evaluation points
`(α_p)_{p ∈ corr}` with `corr.card ≤ t`, univariate Shamir secrecy
gives that the marginal `(f(α_p, 0))_{p ∈ corr}` is sec-invariant.

### Refactor plan (~360 LOC, 4 commits — ✅ all landed)

| Step | File | LOC | Status |
|---|---|---|---|
| 1. Added `uniformBivariateFullWithFixedZero` (3-product source: interior matrix + axisX vector + axisY vector) | `Leslie/Prob/Polynomial.lean` | ~40 | ✅ |
| 2. Proved `bivariate_evals_uniform_full` (joint eval at off-axis grid uniform on `pts_x → pts_y → F`).  Reduces to existing `bivariate_evals_uniform dx dy 0` plus translation invariance: the new polynomial decomposes as `s + α(axisX)(p) + β(axisY)(q) + γ(coefs)(p, q)`, with γ exactly the eval of the axis-zero distribution at constant 0 | `Leslie/Prob/Polynomial.lean` | ~290 | ✅ |
| 3. Added `bivariate_shamir_secrecy_pts_full` and `bivariate_shamir_secrecy_full` against the new distribution | `Leslie/Examples/Prob/BivariateShamir.lean` | ~90 | ✅ |
| 4. Migrated `avssInitPMF` to use `uniformBivariateFullWithFixedZero`; added `bivEval_polyToCoeffs_eq_eval_of_support_full` bridge; updated `avss_secrecy_initPMF` and `avss_secrecy` to consume `bivariate_shamir_secrecy_full` | `Leslie/Examples/Prob/AVSS.lean` | ~280 | ✅ |

### What changed after the refactor

| Theorem | Before refactor (axis-zero distribution) | After refactor (full distribution) |
|---|---|---|
| `avss_correctness_AS` | honest output = `bivEval coeffs (pp p) 0`, collapsed to `sec` for all `p` (degenerate) | honest output = `bivEval coeffs (pp p) 0`, the *per-party Shamir share* — different `p` get different shares |
| `avss_commitment_AS` | every honest output = `coeffs 0 0` (collapsed) | every honest output = `bivEval coeffs (pp p) 0` (per-party share) |
| `avss_reconstruction` | trivial since all shares = `sec` | genuine Lagrange interpolation: `t + 1` distinct shares recover `coeffs 0 0` (and reconstruction across fewer shares is information-theoretically impossible by Shamir secrecy) |
| `avss_secrecy` | grid form at non-axis points; meaningful but doesn't say anything about axis row-poly contents | unchanged shape (still the polynomial-level grid form), now reads as the foundational ingredient for operational secrecy.  Statement migrated to `uniformBivariateFullWithFixedZero` |
| `avss_secrecy_AS_view_conditional` / `_rushing` | vacuously true (`h_aux` provably false) | **conditional theorem unchanged**, but `h_aux` now becomes provable in principle.  Discharging it remains Phase 7.4 inductive AE-bridge (~300–500 LOC follow-on) |

### Phase 7.4 inductive AE-bridge (still required)

Even after the distribution refactor, the inductive AE-bridge proof
sketched in §9's "Path forward" remains: the proof that under a
`RushingAdversary`, the schedule prefix at step `k` AE-equals a
deterministic function of the algebraic-coalition view at step `k`.
This proof was Phase 7.4's substantive form; it consumes the
simulate machinery (PR #35 commit `39b24d0`).  Estimated ~300–500
additional LOC of inductive trace plumbing.

### History (now superseded by the landed refactor)

The original Phase 7 worker brief made `BivariateShamir.lean`
read-only.  The worker correctly stopped at the boundary and
recorded the finding (commit `2de1f2b`) rather than violate the
constraint.  Phase 7.7's worker received explicit authorisation
to modify `BivariateShamir.lean` for the duration of the
distribution refactor; the parallel-additive path was chosen
(both `uniformBivariateWithFixedZero` and
`uniformBivariateFullWithFixedZero` coexist) so that `SyncVSS.lean`
and `AVSSAbstract.lean` (off-limits) continue to consume the
axis-zero variant unchanged.

## 11. Adversary-power restrictions (relative to CR '93)

§1 documents the *information* the rushing adversary may use (a
projection of the state).  This section documents three orthogonal
restrictions on what the adversary can *do* and *observe* in this
state model.  They are not bugs in the formalisation — every theorem
is sound about the model it speaks of — but they weaken the implicit
adversary relative to Canetti–Rabin '93, and a reader who cites the
formalised secrecy / commitment / termination theorems without
consulting them risks overclaiming.

The shorthand C1, C2, C3 is used in theorem docstrings
(`avss_secrecy_AS_view_rushing`, `avss_correctness_AS`,
`avss_commitment_AS`, `avss_termination_AS_fair`) when pointing at
this section.

### 11.1. C1 — Corrupt parties cannot send echoes/readys/amplify

✅ **Resolved by the Phase 8.5b chain** (PRs #57 / #59 / #60 / #61 /
#62 / #63 / #64 / #65 / #66).  The honest gates on
`partyEchoSend` / `partyReady` / `partyAmplify` were dropped, the
`partyEchoSend` broadcast filter was widened to all parties, and
`corruptLocalInv` was weakened to its sustainable two-clause form
(`output = none`, `(delivered = false → rowPoly = none)`).  The
`avssCert` `V_super` / `V_super_fair` / `U_dec_det` disjuncts now
dispatch via `Or.inr` for corrupt-fired actions through the new
liveness lemma `avssFairActionEnabled_at_non_terminated`, and the
soundness route of `avss_termination_AS_fair` was switched from
`pi_n_AST_fair_with_progress_det` (requires `TrajectoryUMono`,
false under C1+C2) to the BC running-min route
`pi_n_AST_fair_with_progress_bc_of_running_min_drops`.

**Resolution status (citation).**

| PR | Role |
|---|---|
| **#57** (8.5a) | `s.dealerSent = true` gate strengthening on send actions (variant prep). |
| **#59** (8.5b-framework) | `V_super` disjunct in `FairASTCertificate`. |
| **#60** (8.5b-α) | C1+C2 model surgery + `corruptLocalInv` weakening + cert sorries. |
| **#61** (8.5b-β) | `avssFairActionEnabled_at_non_terminated` cert dispatch. |
| **#62** (8.5b-γ) | `avssFreshInv` + `actionGate_iff` + `simSyncInv` re-derivation. |
| **#63** (8.5b-γ-followup) | C5/C7 stuck-cases via `avssFlowInv` joint invariant + `(h_corr : corr.card ≤ t)`. |
| **#64** (8.5b-γ-followup-2) | F4 ready-flow preservation via per-pair `inflightReady : Finset (Fin n × Fin n)`. |
| **#65** (8.5b-δ) | BC running-min termination route switch. |
| **#66** (8.5c) | `coalitionView_corrupt_factors_AE` weakening (drop schedule-dependent clauses). |

**(Pre-resolution history kept below for context.)**

Every send-action's gate has `p ∉ s.corrupted` (see
`Leslie/Examples/Prob/AVSS.lean`):

  * `partyEchoSend p` (gate, line ~401–403): `p ∉ s.corrupted`.
  * `partyReady p` (gate, line ~407–410): `p ∉ s.corrupted`.
  * `partyAmplify p` (gate, line ~411–414): `p ∉ s.corrupted`.

Consequence: in this model, corrupt parties' only protocol-relevant
action is `partyCorruptDeliver` (passively receive their row poly
from the dealer).  They cannot inject echoes, fake readys, equivocate,
or amplify — every protocol message they would emit is gate-blocked.

In CR '93 the rushing adversary controls *what* corrupt parties send,
including malformed and adversarially-timed messages designed to
manipulate honest threshold counts (e.g., racing an echo so that an
honest party's `echoesReceived` reaches `n − t` from a corrupt-only
quorum).

**Implication.**

  * For *termination/correctness/commitment*, this makes the
    formalised theorems strictly stronger than the literature: the
    adversary has fewer disruption options, so any property proved
    holds against a (proper) restriction of the CR adversary.
  * For *secrecy*, the implication runs the other way: a proof of
    secrecy in this model is against a *strictly weaker* adversary
    than CR's, so it does **not** directly imply CR-rushing secrecy.

**Bridge to literature.**  Phase 8 (per-party dealer messages and
adversary-controlled corrupt-party send schedule) replaces these
gates with adversary-chosen send actions subject to message-format
verifiability.

**Phase 8.4 status (2026-05-05).**  C1 closure was originally scoped
into Phase 8.4 but deferred during implementation: dropping the honest
gates on `partyEchoSend` / `partyReady` / `partyAmplify` invalidates
the K-weighted variant's strict-decrease story (corrupt-fired sends do
not consume honest-only `unsentEchoSet` slots), and would also force
weakening `corruptLocalInv` (whose `echoesReceived = ∅ ∧ readyReceived = ∅`
clauses underpin the Phase 6/7 secrecy proofs).  Both are
interdependent state-machine refactors and warrant their own PR.
Phase 8.4 instead delivered the **cryptographic content** (Vandermonde-
uniqueness witness for `joinedConsistencyInv`'s preservation, see §12.1
row 8.4); C1 is queued for Phase 8.5+ alongside the variant rework
and the secrecy chain re-verification.

**Phase 8.5 subdivision (2026-05-05).**  An attempt to land C1 (along
with C2 + C4) in a single Phase 8.5 PR confirmed the original
~400 LOC estimate but surfaced cascade depth that makes a single PR
practically infeasible; the work has been subdivided into
8.5a/b/c/d (see §12.1).  C1 closure proper is **PR 8.5b** (combined
with C2), preceded by **PR 8.5a** (variant analysis preparation:
`s.dealerSent = true` gate strengthening + `unsentEchoSet`/
`notReadySentSet` extension to corrupt parties).

**Phase 8.5b PROPER attempt (2026-05-06).**  A worker attempt to
land 8.5b (C1 + C2 model surgery, `corruptLocalInv` weakening,
`avssCert` `Or.inr` dispatch for corrupt fires, and BC running-min
termination route switch) in a single PR validated the original
plan's correctness but found the empirical scope to be ~600–1000 LOC
— 3–5× the ~200 LOC estimate.  The cascade has three distinct
stages that **must land together** to remain build-green at the
cert level (stages i + ii) and through the secrecy theorem
statements (stage iii):

  1. **Model surgery** (gate drops, broadcast-filter broadening,
     `corruptLocalInv` weakening, per-action `_lt` lemma adaptations,
     dispatcher rename) — ~250 LOC.  Saved as a captured WIP diff at
     `/tmp/AVSS-phase8-5b-WIP.patch` (worker session 2026-05-06).
  2. **Cert `Or.inr` dispatch** in `avssCert.V_super`/
     `V_super_fair`/`U_dec_det` for corrupt-fired actions, requiring
     a new ~150 LOC AVSS-side liveness lemma:
     `avssFairActionEnabled_at_non_terminated` (at any state with
     `avssTermInv ∧ ¬ terminated`, some fair action is enabled —
     this is the AVSS progress witness that the V_super disjunct
     framework expects).  Bundled with stage 1 to keep the build
     green at the cert level.
  3. **`coalitionView_corrupt_factors_AE` statement weakening** —
     drop the four schedule-dependent clauses, retain only the
     `coeffs`-content conclusion.  Cascades through ~6+ secrecy-chain
     consumers that destructure the old 6-tuple.  This is a smaller
     prerequisite carved out of 8.5c's original scope.

The BC running-min termination route switch (originally bundled
into 8.5b) and the deeper secrecy-chain re-proof through
`coalitionTrivialView` (originally 8.5c) are *not* required for
the build-green minimum — they're orthogonal and can land
independently.  See §12.1 rows 8.5b-i/ii/iii for the refined
subdivision.

C1 closure properly lands when 8.5b-i + 8.5b-ii are bundled.

### 11.2. C2 — Honest echoes/readys are addressed only to honest receivers

✅ **Resolved by the Phase 8.5b chain** (PRs #60 / #62 / #66).  The
`partyEchoReceive` and `partyReceiveReady` honest-receiver gates were
dropped jointly with the C1 surgery (PR #60), and the
`coalitionView_corrupt_factors_AE` statement was weakened (PR #66) to
drop the four schedule-dependent clauses (`echoSent`,
`echoesReceived`, `readySent`, `readyReceived`), retaining only the
`coeffs`-content clauses (`output = none`,
`delivered = false → rowPoly = none`,
`delivered = true → rowPoly = some (rowPolyOfDealer …)`).  The
`coalitionTraceView_eq_reconstruct_AE` consumer chain (PRs #62, #66)
was rebuilt under the wider corrupt-local view; the cTV bridge now
fires uniformly via `coalitionRowPolyAlignedInv` (a structural,
honest-dealer-INDEPENDENT alignment invariant introduced in
8.5d-β-followup-7).

**Resolution status (citation).**

| PR | Role |
|---|---|
| **#60** (8.5b-α) | Drop `partyEchoReceive` / `partyReceiveReady` honest-receiver gates; widen `partyEchoSend` broadcast filter to all parties. |
| **#62** (8.5b-γ) | `simSyncInv` re-derivation under wider broadcast image. |
| **#66** (8.5c) | `coalitionView_corrupt_factors_AE` weakening; secrecy-chain consumer cascade. |

**(Pre-resolution history kept below for context.)**

`partyEchoSend p`'s effect (around line 348 of `AVSS.lean`) populates
`inflightEchoes` only with `(p, q)` for `q ∉ s.corrupted` (the
`Finset.filter` excludes corrupt receivers).  The receive gates
`partyEchoReceive p q` and `partyReceiveReady p q` additionally
require `p ∉ s.corrupted`.  Symmetrically for `partyReady`.

Consequence: no honest-to-corrupt echo or ready is ever in transit,
and corrupt parties never receive any echo or ready from honest
parties.  Their `(s.local_ p).echoesReceived` and `readyReceived`
fields remain empty throughout every reachable trace.

In CR '93, honest broadcasts are point-to-point messages that go to
*every* party including corrupt ones.  The corrupt-coalition view in
CR therefore includes "I have received an echo from honest p" /
"honest q has readied" — which is a real information channel that
the adversary can use both to learn about honest progress and to
correlate scheduling decisions.

**Implication.**  Combined with C1, the corrupt-coalition view in
this model essentially reduces to:

> for each corrupt `p`, has `partyCorruptDeliver` fired? if so, here
> is `rowPolyOfDealer s.partyPoint s.coeffs p`.

That is a much smaller view than CR's.  This is why
`avss_secrecy_AS_view_rushing`'s rushing adversary, while
view-restricted in the §1 sense, still carries the qualifier "under
the AVSS state model" — the model has carved out the operational
channels through which a CR-rushing adversary would observe honest
broadcasts on corrupt receivers.

**Bridge to literature.**  Same as C1: Phase 8's per-party messages
refactor closes both C1 and C2 simultaneously by giving the adversary
full delivery scheduling on every honest message including those
addressed to corrupt receivers.

**Phase 8.4 status (2026-05-05).**  C2 closure was scoped into Phase
8.4 but deferred for the same reason as C1: dropping the
`partyEchoReceive` honest-receiver gate (and widening the
`partyEchoSend` broadcast filter to all parties) would create
`(honest, corrupt)` entries in `inflightEchoes` whose drainage feeds
into `(s.local_ p).echoesReceived` for corrupt `p` — directly
invalidating `corruptLocalInv`'s `echoesReceived = ∅` clause and
breaking Phase 6/7's coalition-view structural theorem.  Resolving
this requires re-engineering the corrupt-local invariant (or
introducing a separate "corrupt receiver buffer" that doesn't feed
into the secrecy view), which is a substantial state-machine
refactor.  C2 is queued for Phase 8.5+ alongside C1.

**Phase 8.5 subdivision (2026-05-05).**  C2 closure is **PR 8.5b**
(combined with C1).  The technical resolution route surfaced during
the Phase 8.5 attempt is the **`coalitionTrivialView` factoring**:
treat the schedule-dependent `(echoSent, echoesReceived, readySent,
readyReceived)` fields of corrupt parties as a separate per-step
projection of the trace (independent of `coeffs`), and update
`buildCorruptLocalState`/`reconstructCoalitionTraceView` to take it
as a parameter alongside the algebraic view.  This cascades through
`coalitionTraceView_eq_reconstruct_AE` and the headline
secrecy-conditional theorem `avss_secrecy_AS_view_conditional`, which
takes a richer `h_aux` covering the joint marginal of
`(coalitionAlgebraicView, coalitionTrivialView, schedulePrefix)`.
The `simAlgebraicView`/`simSchedulePrefix` factoring chain (§19.4)
gains a parallel `simTrivialView` deterministic-in-`(s_0, schedule)`
companion, and the headline `avss_secrecy_AS_view_rushing` reroutes
through it.  Mechanical once 8.5b lands; **PR 8.5c** delivers the
secrecy chain re-proof.

**Phase 8.5b PROPER attempt (2026-05-06).**  Same status as C1: see
§11.1's 2026-05-06 follow-up note.  C2 closure lands together with
C1 in 8.5b-i + 8.5b-ii (the model-surgery + cert-`Or.inr`-dispatch
bundle); the secrecy-chain consumer statements (which currently
destructure `corruptLocalInv`'s `echoesReceived = ∅ ∧ readyReceived
= ∅` clauses) are weakened in 8.5b-iii.  The `coalitionTrivialView`
introduction and full secrecy re-proof remain in 8.5c per the
original 2026-05-05 plan.

### 11.3. C3 — `dealerShare` is not in `avssFairActions`

`avssFairActions` (definition at `AVSS.lean` line ~568) explicitly
lists only honest-party receive/send/output actions:

```
def avssFairActions : Set (AVSSAction n F) :=
  { a | match a with
        | .partyDeliver _ | .partyEchoSend _ | .partyEchoReceive _ _
        | .partyReady _ | .partyAmplify _ | .partyReceiveReady _ _
        | .partyOutput _ => True
        | _ => False }
```

**(Pre-Phase-B history, kept for context.)** Pre-Phase-B,
`dealerShare` and `partyCorruptDeliver` both fell into the catch-all
`_ => False` and were not fair-required.

Consequence (pre-Phase-B): a "fair adversary" was *not required* to
ever fire `dealerShare`.  A stalling adversary that never fired it
kept `s.dealerSent = false` forever; every fair action's gate then
failed (`partyDeliver` requires `s.dealerSent = true`); no honest
party output; `terminated` was unreachable.

The termination theorem (`avss_termination_AS_fair`) was still
logically sound — for such a stalling adversary, the user-supplied
`h_U_mono` / `h_U_strict` certificate witnesses *could not be
discharged*, so the theorem held vacuously for that input.  But the
theorem carried no operational content in that case.  A naive reader
might have inferred "the formalised model implies an honest dealer's
protocol always terminates"; the precise statement was "the protocol
terminates *if the adversary eventually fires `dealerShare` and the
fair-progress certificate is dischargeable*".

In CR '93 an honest dealer broadcasts by definition (the dealer's
share-out step is part of the protocol script, not the adversary's
schedule).

#### Phase B fix landed

✅ **Resolved (pre-Phase-8 historical fix).** Phase B folded
`dealerShare` into `avssFairActions` (Option B2 from the original
plan).  Phase 8.5d-α subsequently replaced `dealerShare` with the
per-party `dealerShareTo`, retaining the same fairness assumption
for `(honest dealer ∧ honest p)` pairs (see §11.4).  The new
strict-decrease witness `avssU_step_dealerShare_lt` requires
`(honestSet s).card ≥ 1`; the helper
`honestSet_pos_of_not_terminated_pre_share` derives this from
`¬ terminated s ∧ avssTermInv s ∧ s.dealerSent = false`.  When
`honestSet.card = 0`, every honest-party conjunct of `terminated`
is vacuous and the queue conjuncts follow from inv clause 1, so
`terminated s` already holds — the strict-decrease witness is only
needed off-terminated, exactly the context of `avssCert.U_dec_det`.

`avssU_step_lt_of_fair` was extended with a `(hnt : ¬ terminated s)`
premise to thread the helper into the dealerShare case; the three
call sites in `avssCert` (`V_super_fair`, `U_dec_det`,
`U_dec_prob`) all already had the `_hnt` parameter unused, so the
threading was mechanical.

For corrupt-dealer scenarios, folding `dealerShare` into the fair
set is conservative: under fair scheduling, even a corrupt dealer
is forced to broadcast.  Real-CR allows a corrupt dealer to refuse
to broadcast, in which case CR's termination is conditional on the
dealer's behaviour.  A future Phase 8 with per-party dealer
messages would distinguish honest- vs. corrupt-dealer fairness
more precisely.

**Bridge to literature.**  Two clean fixes were considered:

  1. **Phase B (small):** add the hypothesis "honest dealer ⇒
     `dealerShare` eventually fires" at the call site of
     `avss_termination_AS_fair` (a stutter-free trace condition or a
     fairness side-condition outside `avssFair`).
  2. **Phase B alt:** fold `dealerShare` into `avssFairActions` (so
     fair scheduling guarantees it fires).  Slightly tighter: the
     resulting `avssFair` then enforces "dealer eventually shares"
     for every adversary, so honest-dealer termination is genuinely
     unconditional.

Either fix is local; neither requires changes to the cryptographic
content.  Phase A's docs commit flagged the issue; this PR's
Phase B commit chose Option B2 (fold `dealerShare` into
`avssFairActions`).

### 11.4. C4 — Selective non-broadcast and the load-bearing role of Bracha amplification

✅ **Resolved by the Phase 8.5d chain** (PRs #68 / #69 / #70).  The
per-party `dealerShareTo` action surgery (Phase 8.5d-α, PR #68) plus
`s.coeffs` migration to μ₀ (Phase 8.5d-β, PR #69) plus termination
re-scoping to take `h_consistent_quorum` (Phase 8.5d-γ, PR #70)
jointly formalise CR's conditional-termination semantics.  See
`AVSS.consistent_quorum_AE` for the runtime hypothesis form, and
`AVSS.consistent_quorum_AE_of_all_honest_delivered` for a sanity
check confirming honest-dealer schedules satisfy it trivially.

**Resolution status (citation).**

| PR | Role |
|---|---|
| **#68** (8.5d-α) | `dealerShare` → `dealerShareTo (p : Fin n)`; `s.dealerSent : Fin n → Bool`; per-party `actionGate`/`avssStep`/variant updates. |
| **#69** (8.5d-β) | `s.coeffs` removed from `AVSSState`; `coeffs` parameter threaded through `initPred`, `avssSpec`, `avssCert`, all theorem statements; `dealerCommit : Fin n → DealerPayload t F` field carries per-party commitments. |
| **#70** (8.5d-γ) | Termination re-scoped: `avss_termination_AS_fair` (and `_traj`/`_rushing`) take `h_consistent_quorum : consistent_quorum_AE sec corr coeffs μ₀ A`; sanity-check `consistent_quorum_AE_of_all_honest_delivered`. |

**New theorem statement (post-Phase-8.5d-γ).**

```lean
theorem avss_termination_AS_fair
    (sec : F) (corr : Finset (Fin n)) (h_corr : corr.card ≤ t)
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (A : Adversary _ _) (h_fair : avssFair A)
    (h_consistent_quorum :
      consistent_quorum_AE sec corr coeffs avssInitMeasure A)
    (h_drop_io : ...) :
    AlmostDiamond
      (traceDist (avssSpec sec corr coeffs) A avssInitMeasure)
      terminated
```

The `consistent_quorum_AE` hypothesis encodes CR '93's structural
runtime requirement (≥ n − t honest parties have both
`dealerSent p = true` and `dealerMessages p ≠ none` along the
trace, AE-eventually) — the conditional-CR statement that was
previously bypassed by Phase B's unconditional-fairness route.

⚠ **Closely related to §2 (Dealer-to-party communication) but worth
spelling out separately**: in CR '93, a corrupt dealer's adversarial
power includes choosing *which subset of parties* to send shares to,
not just whether to broadcast at all.

#### What CR '93 actually models

The CR adversary controlling the dealer can:

  1. Refuse to broadcast entirely (handled by C3's fix in our model
     by forcing `dealerShare` via fairness).
  2. **Send shares to only some honest parties** (selective non-
     broadcast — what we call C4).
  3. Send *inconsistent* shares to different parties (handled by §2's
     deferred per-party messages).

For (2), CR distinguishes two regimes:

  * **At least `n − t` honest parties receive consistent shares**:
    Bracha amplification fires.  The honest parties who received
    shares broadcast echoes; those who didn't receive shares but
    observe `≥ n − t` echoes amplify via the `readyReceived ≥ t + 1`
    rule (`partyAmplify` in our model).  All honest parties output
    values jointly consistent with some bivariate polynomial.
  * **Fewer than `n − t` honest parties receive shares**: no echo
    cascade, no amplification, no termination.  The protocol simply
    doesn't decide.  CR's termination theorem is conditional on the
    first regime.

The protocol **is correct in both regimes** — there are no
incorrect outputs in the no-termination case (output is `none`,
not "wrong"), and in the termination case Bracha amplification's
joint-consistency property holds.  What's *not* unconditional is
termination.

#### What our model captures and what it doesn't

`dealerShare`'s effect (post-Phase-B) at `AVSS.lean:319–323`
populates `s.inflightDeliveries` with **all** honest parties:

```
| .dealerShare =>
    { s with
      dealerSent := true
      inflightDeliveries :=
        (Finset.univ : Finset (Fin n)).filter (fun p => p ∉ s.corrupted) }
```

So in our model every honest party always receives a share, and
selective non-broadcast is impossible — the adversary cannot choose
which parties to short.  Consequence:

  * The `partyAmplify` action exists in the state machine and the
    variant analysis treats it as fair-required, but in practice
    every honest party can take the direct path
    `partyDeliver → partyEchoSend → partyReady → partyOutput`
    since they all receive shares.  `partyAmplify` is never
    operationally load-bearing in our reachable traces.
  * Bracha amplification's role — letting parties *without* a direct
    share output via echo cascade — is not exercised.
  * Termination becomes unconditional under fair scheduling
    (post-Phase-B), where in CR it would be conditional on the
    `≥ n − t` consistent-share regime.

#### Implication for the formalised theorems

  * **Termination**: stronger than CR — our model forces the dealer
    to broadcast to all honest parties, so the "fewer than `n − t`"
    regime is unreachable.  CR's conditional termination is bypassed
    rather than proved.
  * **Correctness/commitment**: weaker threat model — selective
    non-broadcast and inconsistent-broadcast attacks are not
    considered.
  * **Secrecy**: orthogonal — selective non-broadcast doesn't change
    what corrupt parties learn about `sec`, only whether honest
    parties terminate.  The secrecy theorems remain meaningful.

#### Phase 8 closes C4

The per-party dealer messages refactor (Phase 8, scoped separately)
addresses C4 directly:

  * `dealerMessages : Fin n → Option DealerPayload` — the dealer's
    output to each party, possibly `none` (corrupt dealer chose to
    skip this party) or `some payload`.
  * `partyDeliver p` reads from `dealerMessages p` rather than a
    global `coeffs`.
  * Honest parties without a direct share rely on `partyAmplify`.
  * Termination becomes conditional on "≥ `n − t` honest parties got
    consistent shares" — the genuine CR statement.

Phase 8 also addresses §2 (per-party messages), C1 (corrupt-party
sends), and C2 (honest broadcasts to corrupt receivers) — all four
gaps are entangled and a single refactor closes them together.

**Phase 8.5 subdivision (2026-05-05).**  C4 closure (`dealerShareTo`
+ `coeffs` migration + termination re-scope) is **PR 8.5d**.
Sequenced last because it depends on the gate surgery (8.5b) and
secrecy chain re-proof (8.5c) being in place.  Crucially, 8.5d also
migrates `s.coeffs` out of state into `μ₀` (the witness sample);
this completes the migration-stability story from PRs #43, #45, #48,
#49 (existential-witness theorem forms) by retiring the
state-level `s.coeffs` field entirely.

##### Phase 8.1 (this PR) — A-lite refactor: data carrier in place

Phase 8.1 introduces the `DealerPayload` structure and the
`dealerMessages : Fin n → Option (DealerPayload t F)` field on
`AVSSState` without changing any theorem semantics.  The `s.coeffs`
field is retained as the dealer's *intended* polynomial; `dealerShare`
populates `dealerMessages` deterministically from `s.coeffs` and
`s.partyPoint` for every party (honest and corrupt).  The per-party
`partyDeliver` and `partyCorruptDeliver` actions are migrated to read
from `dealerMessages` (with a new `(dealerMessages p).isSome` gate)
rather than recomputing `rowPolyOfDealer` directly.

The refactor is supported by a new sibling invariant
`dealerMessagesInv s` ensuring every populated `dealerMessages p`
agrees with `rowPolyOfDealer s.partyPoint s.coeffs p` on its `rowPoly`
field.  `colPoly` is currently a `0` placeholder; PR 8.4 will start
populating it for cross-check verification.  All existing classical
theorems re-prove unchanged, lifting the joint
`outputDeterminedInv ∧ dealerMessagesInv` (or `honestDealerInv ∧
dealerMessagesInv`) and projecting back to the surface invariant.

What Phase 8.1 sets up for later PRs:

  * **PR 8.4** (corrupt-party sends, payload-carrying echoes): drop
    the `p ∉ s.corrupted` gates from `partyEchoSend` / `partyReady` /
    `partyAmplify`; carry payload values via the echo actions.
  * **PR 8.5** (selective non-broadcast): let `dealerShare` populate
    only a subset of parties; let a corrupt dealer choose
    `dealerMessages p` independently of `s.coeffs`.
  * **PR 8.6** (full secrecy): re-prove operational secrecy in the
    row+column form.

What Phase 8.1 does *not* do:

  * Move `s.coeffs` out of state into `μ₀` (PR 8.5).
  * Drop the `p ∉ s.corrupted` honest-action gates (PR 8.4).
  * Allow corrupt-dealer freedom in `dealerMessages` (PR 8.5).

### 11.5. C5 — Deterministic-adversary quantification only

✅ **Resolved by Phase 9** (PRs #41, #46, #47, #49, #53, #54, #55,
and the integration PR — see §13.1).  Each AVSS classical theorem
now has a randomised analog quantified over `RandomisedAdversary`
(PR #41) or the literature-standard `AVSSRushingRandomisedAdversary`
(PR #55); together they cover correctness, commitment, secrecy
(step-`k` full form via 9.6/PR #53; coord-0 grid form via 9.3/PR #47;
step-`k` rushing wrapper `avss_secrecy_AS_view_rushing_randomised`
via the integration PR), and termination (via 9.4/PR #54 and the
rushing wrapper in PR #55).  The original deterministic theorems
remain as the structural backbone — the randomised analogs route
through the Phase 9.2 lifting meta-theorems
(`AlmostBoxRandomised_of_inductive`,
`randomisedTraceDist_map_eq_of_deterministic_at_zero`) plus the
randomised `FairASTCertificate.sound` core, and the rushing
wrappers are one-liners through `R.toRandomisedAdversary`.

**⚠ Cross-branch reconciliation caveat (post-Phase-8.5d).**  Phase
9's `avss_termination_AS_fair_randomised` (PR #54) and
`_rushing_randomised` (PR #55) are typed against the **pre-Phase-8.5b
deterministic-descent route** (via `RandomisedFairASTCertificate.sound`,
which requires `RandomisedTrajectoryUMono` — AE-monotone `U` along
the randomised mixture trace).  Two issues compound under the
post-Phase-8.5b/d AVSS model:

1. **Soundness route mismatch.** The deterministic version
   `avss_termination_AS_fair` switched in Phase 8.5d-γ from the
   deterministic-descent route to the BC running-min route
   (`pi_n_AST_fair_with_progress_bc_of_running_min_drops`), taking
   `consistent_quorum_AE` and `TrajectoryFairRunningMinDropIO`
   hypotheses.  The randomised analogs still call the
   deterministic-descent route under the hood.

2. **`RandomisedTrajectoryUMono` is unsatisfiable for AVSS.**  The
   reason for the deterministic switch — corrupt-fired actions
   bump `avssU` post-Phase-8.5b — applies equally at the randomised
   level.  AE-monotonicity is false under any `RandomisedAdversary`
   that schedules corrupt-fired sends.  So the existing
   `avss_termination_AS_fair_randomised` is **vacuously callable
   but not usefully callable** for any post-Phase-8.5b AVSS
   instance: the `RandomisedTrajectoryUMono` hypothesis cannot be
   discharged.

This is **not a small mechanical thread-through fix.**  Closing
the gap requires:

  * **Framework PR** — add
    `pi_n_AST_fair_with_progress_bc_of_running_min_drops_randomised`
    in `Leslie/Prob/Liveness.lean` plus
    `RandomisedTrajectoryFairRunningMinDropIO` in
    `Leslie/Prob/RandomisedAdversary.lean`.  Real measure-theoretic
    work (~150–200 LOC) — the BC running-min argument needs to be
    re-derived for the kernel-mixture trace, paralleling the
    deterministic version's structure.

  * **AVSS-side PR** — define
    `consistent_quorum_AE_randomised` (analog of `consistent_quorum_AE`
    on the randomised mixture trace), switch
    `avss_termination_AS_fair_randomised` and `_rushing_randomised`
    to call the new framework theorem, drop the now-unsatisfiable
    `RandomisedTrajectoryUMono` hypothesis.  ~80 LOC.

Total: ~230–280 LOC across 2 stacked PRs.  Tracked as a Phase
11-β-followup or a new Phase 12-prerequisite (depending on whether
the framework lift is composed before or after Phase 11-β
extracts `Secrecy.lift_to_randomised`).

The other Phase 9 randomised forms — `avss_correctness_AS_*` /
`avss_commitment_AS_*` / `avss_secrecy_AS_*` (PRs #47, #49, #53,
#55, #56, #74) — are aligned with their deterministic counterparts
and do not need rebase work; only termination is affected.

The historical context below is retained for completeness; readers
of new code should reach for the `_randomised` and
`_rushing_randomised` variants.

⚠ Historical: **All theorems in this formalisation universally quantify over
*deterministic* adversaries** — both the legacy `Adversary σ ι` and
the rushing `RushingAdversary σ ι V` are pure functions
(`History → Option Action` and `view-history → Option Action`
respectively) rather than measurable kernels.  Nothing in the
current artefact says "AVSS is secure against any adversary that
flips coins."

#### Why the cryptographic content is preserved

The standard information-theoretic argument is a Fubini /
mixture argument over the adversary's random tape.  A randomised
adversary `A_rand : (History × R) → PMF (Option Action)` is
mathematically equivalent to "pick `r ∈ R` from some distribution
`ρ`, then run the deterministic adversary `A(r)` parameterised by
`r`."  By Fubini composition with the random tape:

```
traceDist[A_rand] sec  =  ∫_R  traceDist[A(r)] sec   dρ(r)
```

Each of the four headline theorem forms lifts under this mixture
by an elementary measure-theoretic argument:

| Theorem form | Lifting argument |
|---|---|
| **Secrecy** (pushforward equality `(traceDist sec).map f = (traceDist sec').map f`) | Pushforward and mixture commute: `∫ (traceDist[A(r)] sec).map f dρ = (traceDist[A_rand] sec).map f`.  Equation holds pointwise in `r`, so it holds after integration. |
| **Correctness / Commitment** (`AlmostBox`: `∀ᵐ ω ∂traceDist, P(ω)`) | If `traceDist[A(r)]{¬P} = 0` for every `r`, then `traceDist[A_rand]{¬P} = ∫ traceDist[A(r)]{¬P} dρ = 0`.  Fubini, plus `P` measurable. |
| **Termination** (`AlmostDiamond`: `∀ᵐ ω, ∃ k, terminated (ω k).1`) | Same Fubini argument as correctness; the fairness hypothesis lifts cleanly because `TrajectoryFairAdversary`'s progress witness is itself an AE statement on the trace measure. |

So mathematically the lift is automatic and AVSS genuinely is
secure against randomised adversaries.  The gap is purely
formal — the surface theorem statements name the deterministic
type.

#### Why the `simSimulate` AE-bridge specifically would break under randomised adversaries

The Phase 7.4 inductive AE-bridge
(`traceDist_AE_eq_avssSimulateTrace`) crucially assumes:

  1. Each effect is `PMF.pure` (Dirac).
  2. The schedule is a function, not a kernel.

A randomised adversary breaks (2): the kernel branch in the
trace-construction recurrence no longer collapses to a single
Dirac point, instead becoming a mixture of Diracs which is not
itself a Dirac.

The clean fix is **not** to lift the bridge to kernel form
(that's option (c) in §12.4-style risk analysis — strictly more
work and only needed if a downstream consumer wants a kernel-form
simulate).  Instead, lift the **headline** theorems via a one-shot
meta-theorem that operates above the bridge — the bridge stays in
its current deterministic form as a structural fact about
deterministic-strategy AVSS.

#### Phase 9 fix (planned — see §13)

A **single one-shot meta-theorem** in `Leslie/Prob/` covers every
property in the library uniformly: define `RandomisedAdversary` as
a measurable kernel, prove
`AlmostBox.lift_to_randomised`, the matching forms for
`Measure.map`-equality (secrecy) and `AlmostDiamond` (termination),
and every theorem in `AVSS.lean` (and any other protocol module)
immediately re-states against randomised adversaries by
composition.  No protocol-specific work; ≈150–250 LOC total.

The simulate AE-bridge stays deterministic; the lifting argument
operates above it.

### 11.6. Correctness/commitment subtlety (per-party share, not the secret)

This is not strictly an *adversary-power* restriction — it's a
restatement subtlety that affects how readers should interpret the
correctness and commitment theorems.

`avss_correctness_AS` concludes

```
v = bivEval s.coeffs (s.partyPoint p) 0
```

for every honest party `p` with output `v` — i.e., each honest party
outputs its **per-party share** `f_p(0)`, **not the secret**
`s.coeffs 0 0`.  This is consistent with CR-style AVSS where outputs
are *shares* and reconstruction is a separate phase, but readers who
expect the colloquial "honest dealer ⇒ honest outputs equal `sec`"
will be surprised: that holds only after `avss_reconstruction`'s
Lagrange step (any `t + 1` distinct honest shares interpolate at `0`
to recover `s.coeffs 0 0`).

`avss_commitment_AS` is similarly "every honest output is
`bivEval coeffs (partyPoint p) 0`" — strong enough (combined with
`avss_reconstruction`) to imply the literature's "any `t + 1` honest
outputs Lagrange-interpolate to one secret", but the model's
commitment is structurally trivial because there is only one
`s.coeffs` field in the state (already disclosed in §2).

**Bridge to literature.**  The Lagrange step is already formalised
(`avss_reconstruction`); composing it with `avss_correctness_AS`
gives the user-facing "honest dealer ⇒ recovered secret = `sec`"
property at any committee of `t + 1` honest parties.  The
*genuinely-harder* commitment property — "the corrupt dealer cannot
fool honest parties into outputting values inconsistent with any
single bivariate polynomial" — is structural in this model (one
global `s.coeffs`) and recovered properly only under Phase 8's
per-party dealer messages.

## Future directions

The honest path to a literature-faithful AVSS — what we'd call a "Phase B+"
trajectory — has four components, each shippable as a separate PR:

1. ✅ **Phase 6: Operational view secrecy in the current adversary model.**
   Replace `coalitionGrid` with `coalitionView` (corrupt parties' actual
   `local_`).  Prove `coalitionView` factors through `coalitionGrid +
   schedule + invariants`.  Result: a theorem that says the corrupt
   parties' state distribution is invariant in `sec`, *under the existing
   strong adversary, jointly with the schedule prefix*.  Caveat: still
   doesn't address adversary information leakage via scheduling
   decisions (handled by Phase 7).  **Landed in PR #33.**

2. ✅ **Phase 7.1: Define `RushingAdversary`.**  New generic adversary
   type in `Leslie/Prob/Adversary.lean` whose strategy is a function of
   the view-history (via a `ProtocolView σ V` projection).  Adapter
   `toAdversary` lifts back to plain `Adversary σ ι`.  Sanity lemma:
   `R.toAdversary.schedule h = R.schedule (R.viewHistory h)` (rfl).
   **Landed in this PR.**

3. ✅ **Phase 7.2: AVSS instantiation.**  `avssCoalitionView corr` —
   the corrupt coalition's local-state projection, packaged as a
   generic `ProtocolView`.  `AVSSRushingAdversary corr` abbreviation
   for the canonical rushing-adversary type for AVSS.  **Landed in
   this PR.**

4. ✅ **Phase 7.3: Re-prove existing classical theorems against
   `RushingAdversary`.**  `avss_termination_AS_fair_rushing`,
   `avss_correctness_AS_rushing`, `avss_commitment_AS_rushing` — thin
   wrappers around the classical theorems via `R.toAdversary`.
   `avss_reconstruction` is purely algebraic, no rushing version
   needed.  **Landed in this PR.**

5. ✅ **Phase 7.4 + 7.5: schedule-leakage-closing theorem.**  See
   §9 above — the cryptographic-core composition that produces the
   unconditional `avss_secrecy_AS_view_rushing` (canonical name).
   Intermediate variants `avss_secrecy_AS_view_rushing_via_aux` and
   `avss_secrecy_AS_view_rushing_via_init_invariant` are retained
   as the conditional building blocks.  **Landed.**

6. ⏳ **Phase 8: Per-party dealer messages — full literature-faithful AVSS.**
   Closes the four entangled gaps **§2 (dealer-to-party communication),
   C1 (corrupt-party sends), C2 (honest broadcasts to corrupt
   receivers), C4 (selective non-broadcast)** in a single coherent
   refactor.  After Phase 8, AVSS matches Canetti–Rabin '93's model:
   per-party dealer messages, corrupt-party send actions, honest
   broadcasts to corrupt receivers, and selective non-broadcast as an
   adversary capability.  Termination becomes conditional on Bracha
   amplification, as in the literature.

   This is **the load-bearing remaining gap**.  Estimated 1500–2200 LOC
   across 6–8 PRs.  See **§12** below for the detailed plan and
   status tracker.

Estimated cost: Phase 6 ≈ 600 LOC (landed); Phase 7.1 ≈ 130 LOC
(landed); Phase 7.2 ≈ 90 LOC (landed); Phase 7.3 ≈ 70 LOC (landed);
Phase 7.4+7.5 ≈ 800 LOC (landed); Phase 7.7 (distribution refactor)
≈ 780 LOC (landed); Phase A (docs) ≈ 150 LOC (landed); Phase B
(C3 fix) ≈ 200 LOC (landed); Phase 8 ≈ 1500–2200 LOC (in progress).

## 12. Phase 8 — per-party dealer messages: detailed plan + status tracker

This section tracks the multi-PR Phase 8 initiative as it lands.
Each row corresponds to one PR; statuses move from ⏳ pending to 🚧
in-flight to ✅ landed.

### 12.1. Status tracker

The Phase 8 chain landed non-linearly: planning rows from 2026-05-05
(8.5b-i / ii / iii) and 2026-05-06 (8.5b-i / ii / iii + 8.5c
serialization) were superseded by the actual α/β/γ chain that
landed in PRs #57–#70.  This table reflects what **actually
landed**.  Earlier planning rows are preserved in §12.1.x below
for archaeological context.

| PR | Title | Scope | Status |
|---|---|---|---|
| **8.1** (PR #39) | DealerPayload + state surgery (A-lite) | Foundational refactor: introduce `DealerPayload` type and `dealerMessages : Fin n → Option (DealerPayload t F)` field; keep `coeffs` alongside; migrate `dealerShare`/`partyDeliver`/`partyCorruptDeliver` to read from `dealerMessages`; add consistency invariant. **No theorem semantics change.** | ✅ landed |
| **8.2** (PR #43) | Honest-dealer consistency invariant + correctness re-verification | Define `honestDealerConsistencyInv`; add `coeffsSecretInv` and `avss_correctness_AS_existential` (+ `_rushing` variant). | ✅ landed |
| **8.3** (PR #45) | Corrupt-dealer commitment (existential statement) | `joinedConsistencyInv`, `consistentPayload`, `honestOutputCount`, `avss_commitment_AS_existential` (+ `_rushing` variant). | ✅ landed |
| **8.4** (PR #48) | Corrupt-dealer commitment via Vandermonde witness (cryptographic content) | Re-prove `avssStep_preserves_joinedConsistencyInv` via `Lagrange.eq_interpolate_of_eval_eq`; add `partyPointInjInv`. | ✅ landed |
| **8.5a** (PR #57) | `s.dealerSent = true` gate strengthening (8.5b precursor; variant prep). | ✅ landed |
| **8.5b-framework** (PR #59) | `V_super` disjunct in `FairASTCertificate` (framework-level prereq for corrupt-fire `Or.inr` dispatch). | ✅ landed |
| **8.5b-α** (PR #60) | C1+C2 model surgery: drop honest gates on `partyEchoSend`/`partyReady`/`partyAmplify`/`partyEchoReceive`/`partyReceiveReady`; widen broadcast filter; weaken `corruptLocalInv` to two clauses; add `isHonestFire`; rename dispatcher; cert sorries. | ✅ landed |
| **8.5b-β** (PR #61) | `avssCert` `Or.inr` dispatch via new liveness lemma `avssFairActionEnabled_at_non_terminated` (corrupt-fire post enables some fair action). | ✅ landed |
| **8.5b-γ** (PR #62) | `avssFreshInv` + `actionGate_iff` corrupt-q branches + `simSyncInv` re-derivation; closes 9 of 13 sorries from 8.5b-α. | ✅ landed |
| **8.5b-γ-followup** (PR #63) | Closes C5/C7 stuck cases of `avssFairActionEnabled_at_non_terminated` via new `avssFlowInv` (threshold + delivery completeness + echo + ready flow) and `(h_corr : corr.card ≤ t)` parameter on `avssCert`. | ✅ landed |
| **8.5b-γ-followup-2** (PR #64) | F4 ready-flow preservation: upgrade `inflightReady : Finset (Fin n)` → `Finset (Fin n × Fin n)` (per-pair tokens). | ✅ landed |
| **8.5b-δ** (PR #65) | BC running-min termination route: switch `avss_termination_AS_fair` from `pi_n_AST_fair_with_progress_det` (TrajectoryUMono — false under C1+C2) to `pi_n_AST_fair_with_progress_bc_of_running_min_drops`. | ✅ landed |
| **8.5c** (PR #66) | `coalitionView_corrupt_factors_AE` statement weakening + secrecy-chain `rcases` cascade (formerly the "8.5b-iii + 8.5c" plan, landed as a single PR). | ✅ landed |
| **8.5b-ε** (PR #67) | Remove vestigial `U_dec_prob` (BC running-min route doesn't consume it). | ✅ landed |
| **8.5d-α** (PR #68) | `dealerShare` → `dealerShareTo (p : Fin n)` per-party action surgery; `s.dealerSent : Fin n → Bool`; per-party `actionGate`/`avssStep`/variant updates. | ✅ landed |
| **8.5d-β** (PR #69) | `s.coeffs` migration to μ₀; `coeffs` parameter through `initPred` / `avssSpec` / `avssCert` / theorem statements; `dealerCommit : Fin n → DealerPayload t F` field; cTV-bridge dealerHonest-INDEPENDENT closure (8.5d-β-followup-7 via `coalitionRowPolyAlignedInv`). | ✅ landed |
| **8.5d-γ** (PR #70) | `avss_termination_AS_fair` (and `_traj`/`_rushing`) re-scoped to take `h_consistent_quorum`; new `consistent_quorum_AE` def + `_of_all_honest_delivered` sanity check; 0 sorries. | ✅ landed |
| **8.5d-δ** (this PR) | MODEL_NOTES finalisation: §11 caveat-closure citations, §12.1 status reconciliation, §12.3 canonical post-Phase-8 state freeze, §12.4 risks update, Phase 11 stub. Docs-only. | 🚧 in-flight (this PR) |
| **8.6** | Operational secrecy under full adversary (post-8.5d-α/β/γ) | Re-prove `avss_secrecy_AS_view_rushing` against the post-8.5d adversary.  Consists of (a) the +200 LOC row + column secrecy form (deferred since `SyncVSS.lean §10` — full polynomial-manipulation step in two directions), and (b) wiring the row+col form into a strengthened headline conclusion. | ✅ **landed**. **(a)** Phase 11-δ (PR #75): `Leslie.Prob.Polynomial.bivariate_evals_uniform_row_col` (statement + full proof via `bivariate_evals_uniform_full` + constant-fiber projection) and the AVSS-side wrappers `avss_bivariate_corrGrid_uniform` / `avss_bivariate_corrGrid_sec_invariant`.  **(b)** Phase 11-δ-followup (this PR): sibling theorem `avss_secrecy_AS_view_rushing_bivariate` in §19.7 of `AVSS.lean` — bundles the existing operational headline and the bivariate corrupt-grid sec-invariance into a single citation-ready conjunction.  The original `avss_secrecy_AS_view_rushing` is unchanged (backward-compat).  All five load-bearing AVSS theorems remain `[propext, Classical.choice, Quot.sound]`-axiom-clean; zero sorries. |
| **8.7** | Adapter retirement / cleanup | **Likely empty.** The 8.5b/c/d chain edited the model in place; there is no parallel pre-Phase-8 form to retire (no compatibility shim was kept).  Documented here as a finding — if a deprecation-shim layer is needed for downstream consumers, that work would be added back; otherwise this row is closeable as a no-op. | 🟡 likely no-op |
| **8.8 (Fix 1, post-PR `#77`)** | **Rename** misleadingly-named commitment headline from `avss_commitment_AS_corrupt_dealer` to `avss_commitment_AS_existential` (mirroring sibling `avss_correctness_AS_existential` pattern). | The old name claimed "corrupt-dealer commitment" but the conclusion has been honest-dealer-conditional since Phase 8.5d-β migrated `s.coeffs → μ₀` (the Vandermonde extraction route requires `outputDeterminedInv coeffs s`, which is honest-dealer-conditional). All four variants (`*`, `*_rushing`, `*_randomised`, `*_rushing_randomised`) renamed. Theorem statements unchanged — pure rename + docstring refresh. Queues §16 (Phase 8.6 Bracha amplification) as the proper corrupt-dealer fix. | ✅ landed |
| **8.6 (renumbered)** | Genuine corrupt-dealer commitment via Bracha echo+ready amplification | Strengthen `joinedConsistencyInv` to be **dealerHonest-INDEPENDENT**: prove that the AVSS echo+ready threshold dynamics force all honest outputs to lie on a single bivariate polynomial of degree ≤ t, even under corrupt dealer.  Proof outline: (a) define `bivariateAlignedInv` — state-level invariant saying "there exists a bivariate `B` such that every honest party with `delivered = true` has `rowPoly = some (B(·, partyPoint p))`"; (b) prove `bivariateAlignedInv` is preserved by `partyEcho`/`partyReady` actions via threshold counting (any t+1 honest parties echoing on the same row+col vote-pair fix `B` uniquely by Vandermonde, dealerHonest-INDEPENDENT); (c) drop the `s.dealerHonest = true →` guards on `avss_commitment_AS_existential` and the 3 wrapper variants.  ~200–400 LOC of new cryptographic content. **Note**: This is the row originally numbered 8.6 in pre-Fix-1 versions, but that row got merged into 8.5d as the row+column secrecy work; the genuine corrupt-dealer commitment was effectively never landed.  Renumbered here as the new 8.6 / queued. | ⏳ queued |
| **8.8** | MODEL_NOTES rewrite | Subsumed by **8.5d-δ** (this PR).  The original "comprehensive rewrite" scope is replaced by the targeted §11 / §12 / §13 reconciliation here. | 🟢 subsumed by 8.5d-δ |

### 12.2. Sequencing — actual landed order

The actual landed sequence (PR-by-PR), which differs from the
2026-05-05 / 2026-05-06 planning subdivisions:

```
8.1 (#39) → 8.2 (#43) → 8.3 (#45) → 8.4 (#48) →
8.5a (#57) → 8.5b-framework (#59) →
8.5b-α (#60) → 8.5b-β (#61) → 8.5b-γ (#62) →
8.5b-γ-followup (#63) → 8.5b-γ-followup-2 (#64) →
8.5b-δ (#65) → 8.5c (#66) → 8.5b-ε (#67) →
8.5d-α (#68) → 8.5d-β (#69) → 8.5d-γ (#70) →
8.5d-δ (this PR)
```

**Pending after this PR.**

  * **8.6** depends on 8.5d-γ's adversary model (selective
    non-broadcast + per-party messages + `s.coeffs` in μ₀).
  * **8.7** likely no-op (model edited in place; no parallel
    form to retire).
  * **8.8** subsumed by 8.5d-δ.
  * **Phase 11** (§14) — secrecy framework abstraction; **closed
    (✅ 11-α / 11-γ / 11-δ / 11-δ-followup / 11-ε landed)**; 11-β
    (randomised lift) remains ⏸ deferred until Phase 9
    (`RandomisedAdversary`) merges — its scope is then a one-shot
    Fubini lift independent of any further AVSS work.

### 12.3. Post-Phase-8 state — **canonical reference (frozen 2026-05-07)**

After the 8.1 → 8.5d chain landed (PRs #39 / #43 / #45 / #48 / #57 –
#70), AVSS matches Canetti–Rabin '93's threat model up to row + column
secrecy (deferred to 8.6).  This table is the **canonical citation
target** for downstream work.

| Theorem | Pre-Phase-8 (historical) | **Post-Phase-8 (this state)** |
|---|---|---|
| **Termination** | Unconditional under fair scheduling | Conditional on `consistent_quorum_AE` (≥ n − t honest parties have received consistent shares, AE on traces) — `avss_termination_AS_fair` |
| **Correctness** | Honest dealer ⇒ outputs consistent with `s.coeffs` (state field) | Honest dealer ⇒ ∃ witness s.t. outputs consistent with `bivEval witness ...` — `avss_correctness_AS_existential` |
| **Commitment** | Trivially true (single global `coeffs`) | Honest-dealer-conditional existential commitment (via `joinedConsistencyInv_via_vandermonde`) — `avss_commitment_AS_existential`; full corrupt-dealer strengthening is queued in Phase 8.6 |
| **Reconstruction** | Lagrange theorem | Unchanged — `avss_reconstruction` |
| **Secrecy** | Row-poly secrecy under restricted adversary | Operational view-secrecy under rushing adversary, dealerHonest-INDEPENDENT cTV bridge — `avss_secrecy_AS_view_rushing` (existing) **and** the bivariate row+column sibling `avss_secrecy_AS_view_rushing_bivariate` (Phase 11-δ-followup) which additionally bundles the polynomial-level corrupt-grid sec-invariance from `avss_bivariate_corrGrid_sec_invariant`. |

**Adversary model.**

  * Corrupt parties freely fire `partyEchoSend` / `partyReady` /
    `partyAmplify` (C1 closed).
  * Honest broadcasts go to corrupt receivers (C2 closed).
  * `dealerShareTo p` is per-party; corrupt dealer can selectively
    short-share (C4 closed).
  * `s.coeffs` lives in μ₀ (initial measure), not state — the witness
    is sampled at protocol start, not stored in `AVSSState`.

**Remaining gaps (for downstream callers to be aware of).**

  * **C5** (deterministic adversary quantification): closed by Phase 9
    on a parallel branch.  Cross-branch reconciliation deferred to
    merge time (see §11.5).
  * **Row + column secrecy** (the +200 LOC polynomial step deferred
    since `SyncVSS.lean §10`): ✅ **closed** by Phase 11-δ (PR #75)
    + Phase 11-δ-followup (this PR).  See §12.1 row 8.6 and §12.4
    risk 4 for the citation-level pointers.

Freeze this table as the citation reference.  Downstream protocol
work (e.g., AVSS-using-RBC composition) should cite the Post-Phase-8
column.

### 12.4. Risks

1. ✅ **Commitment proof's cryptographic content** — resolved across
   PRs 8.3 (#45) + 8.4 (#48).  PR #45 landed the existential statement
   of `joinedConsistencyInv` with a thin `s.coeffs`-witness preservation
   proof; PR #48 replaced it with the genuine Lagrange-interpolation /
   Vandermonde-uniqueness construction (`joinedConsistencyInv_via_vandermonde`)
   using `Lagrange.eq_interpolate_of_eval_eq`.  New invariant
   `partyPointInjInv` (distinct evaluation points) added as the
   standard Shamir/Vandermonde precondition.

2. ✅ **Variant analysis re-verification** — resolved by the 8.5b chain
   (PRs #57 / #60 / #65).  PR #57 (8.5a) added the `s.dealerSent = true`
   gate strengthening to preserve pre-share quiescence under C1+C2.
   PR #60 (8.5b-α) re-proved the per-action `_lt` lemmas under the new
   gates with `(hph : p ∉ s.corrupted)` premises, added the
   `isHonestFire` predicate, and renamed the dispatcher.  PR #65
   (8.5b-δ) handled the deeper issue that corrupt-fired sends bump
   `avssU` by switching the soundness route from
   `pi_n_AST_fair_with_progress_det` (TrajectoryUMono — false under
   C1+C2) to `pi_n_AST_fair_with_progress_bc_of_running_min_drops`
   (BC running-min, handles non-monotone variants by tracking the
   running minimum).

3. ✅ **`corruptLocalInv` weakening cascade** — resolved by the 8.5b
   chain (PRs #60 / #62 / #66) and finalised by 8.5d-β-followup-7.
   PR #60 weakened `corruptLocalInv` to its sustainable two-clause form.
   PR #62 (8.5b-γ) re-derived `simSyncInv` under the wider broadcast
   image.  PR #66 (8.5c) cascaded through ~6+ secrecy-chain consumers
   (`coalitionView_corrupt_factors_AE` weakening + `rcases` updates
   throughout `coalitionTraceView_eq_reconstruct_AE`,
   `simAlgebraicView`'s inductive bridge, etc.).  The final cTV bridge
   was made dealerHonest-INDEPENDENT in 8.5d-β-followup-7 via a new
   `coalitionRowPolyAlignedInv` structural alignment invariant —
   eliminating the need for the originally-planned `coalitionTrivialView`
   factoring layer.

4. ✅ **Row + column secrecy** (PR 8.6 / Phase 11-δ) — **landed
   2026-05-07, axiom-clean.**  The polynomial-level row+column
   uniformity theorem
   `Leslie.Prob.Polynomial.bivariate_evals_uniform_row_col` is landed:
   for any `R ⊆ F` with `|R| ≤ t` and `0 ∉ R`, and any subset
   `S ⊆ R ×ˢ R`, the joint evaluation distribution at `S` of the
   uniformly sampled bidegree-`(t, t)` polynomial with `f(0, 0) = sec`
   is uniform on `↑S → F` — generalising the rectangular-only
   `bivariate_evals_uniform_full` (Phase 7.7) to arbitrary subsets.
   Proof reduces to the rectangular form plus a constant-fiber
   projection along `↑S ↪ ↑R × ↑R`, captured by the auxiliary
   `PMF.uniform_pi_restrict`.  AVSS-side wrappers
   `avss_bivariate_corrGrid_uniform` (uniformity) and
   `avss_bivariate_corrGrid_sec_invariant` (sec-invariance corollary)
   are landed in §19.6.  All four declarations are
   `[propext, Classical.choice, Quot.sound]`-axiom-clean (zero
   sorries; the headline cryptographic reasoning — Vandermonde+
   Lagrange in two directions — is fully captured by
   `bivariate_evals_uniform_full`'s existing proof).
   **Phase 11-δ-followup (this PR).** The row+col form is now wired
   into a *sibling* of the headline secrecy theorem,
   `avss_secrecy_AS_view_rushing_bivariate` (`AVSS.lean` §19.7).  The
   sibling bundles two sec-invariances into a single citation:
   (a) the existing operational headline's
   `(coalitionTraceView, schedulePrefix)` marginal sec-invariance
   (Phase 8.5d), and (b) the polynomial-level
   `avss_bivariate_corrGrid_sec_invariant` (this PR's parent).  Both
   axes of secrecy are now available to downstream consumers
   (e.g. column cross-check protocols à la CR'93 §10) from a single
   theorem — without any changes to the existing
   `avss_secrecy_AS_view_rushing` (backward-compat).
   **Out of scope:** axis-zero handling (`0 ∈ R` case, where the
   sec-axis is exposed and the conclusion is conditional on `sec`)
   is documented but **not** included; the current statement requires
   `0 ∉ R`.  A deeper joint-pushforward variant (extracting the
   dealer's polynomial through the trace's initial state to give a
   single trace-level joint sec-invariance) is also queued for a
   later phase — see §14 Phase 11-ε notes.

### 12.5. Maintenance protocol

This tracker is the source of truth for Phase 8 status.  As each PR lands:

  1. The PR's own commit message updates the corresponding row of §12.1 (statuses ⏳ → 🚧 → ✅).
  2. New caveats discovered during implementation are added to §11 (or to a new sub-section here if scope-specific).
  3. After Phase 8 completes, §11.1–§11.4 caveats should be marked "✅ resolved by Phase 8 (PR #N)" and the post-Phase-8 state table (§12.3) frozen as the citation reference.

If the plan changes in the middle (e.g., a worker discovers a structural issue that re-scopes a PR), the affected row's status reverts to 🚧 with a footnote describing the change.

## 13. Phase 9 — Randomised adversary support (independent of Phase 8)

Closes caveat **C5** (deterministic-adversary quantification only,
§11.5).  This phase is **independent of Phase 8** — it can land in
parallel, since the Phase 8 refactor work happens at the
protocol-state level while Phase 9 happens at the
adversary-type level.  Either can be done first.

### 13.1. Status tracker

| PR | Title | Scope | LOC | Status |
|---|---|---|---|---|
| **9.1** | `RandomisedAdversary` type + mixture trace measure | Define `RandomisedAdversary σ ι` as `History → PMF (Option ι)` in `Leslie/Prob/RandomisedAdversary.lean` (new file).  Define the mixture trace measure `randomisedTraceDist` via the same `Kernel.trajMeasure` plumbing as `traceDist` but with the per-step kernel sampling the strategy's PMF.  Adapter `Adversary.toRandomised : Adversary σ ι → RandomisedAdversary σ ι` lifts deterministic strategies (Dirac PMF on `Option ι`).  Sanity theorem `randomisedTraceDist_toRandomised` shows the lift agrees with `traceDist`.  Plus `@[simp]` lemmas `toRandomised_strategy` / `toRandomised_corrupt`. | ~230 | ✅ landed (PR #41) |
| **9.2** | Three lifting meta-theorems | `AlmostBoxRandomised_of_inductive` / `AlmostBox.lift_to_randomised`: per-step inductive preservation lifts to randomised AS-Box.  `randomisedTraceDist_map_eq_of_deterministic_at_zero`: secrecy form for coord-0 projections (the AVSS use case).  `AlmostDiamond.lift_to_randomised`: AS-Diamond from inductive data.  Heart of the proofs is the per-step kernel mixture identity `randomisedStepKernel_apply_tsum`.  Inductive-form hypothesis selected over the abstract Fubini-tape form (worker-task §1) since the latter would require Mathlib infrastructure on infinite product measures over countable index sets — see comments in `RandomisedAdversary.lean`'s Phase 9.2 header. | ~310 | ✅ landed (PR #46) |
| **9.3** | AVSS-side restatements (partial coverage) | `avss_correctness_AS_randomised` and `avss_commitment_AS_randomised` via `AlmostBoxRandomised_of_inductive` (re-feeding the same per-step preservation data used by the deterministic versions); `avss_secrecy_AS_step_zero_grid_randomised` via `randomisedTraceDist_map_eq_of_deterministic_at_zero` (coord-0 form). `avss_termination_AS_fair_randomised` is **NOT** lifted in this PR because PR #46's `AlmostDiamond.lift_to_randomised` is degenerate (`exact ⟨0, hω 0⟩` only); termination is deferred to Phase 9.4. Closes C5 for correctness, commitment, and coord-0 secrecy. | ~150 | ✅ landed (PR #47) |
| **9.3-existential** | Existential-witness `_randomised` analogs | `avss_correctness_AS_existential_randomised` (joint inv: `honestDealerInv` ∧ static `coeffs 0 0 = secret`) and `avss_commitment_AS_existential_randomised` (with `honestOutputCount`-precondition gate, witness from `s.coeffs`). Migration-stable: when a future PR moves `s.coeffs` out of state into `μ₀`, the existential-witness forms continue to hold (witness sourced from initial-state sample); the `s.coeffs`-direct forms from PR #47 will become stale. Closes the literature-faithful `_randomised` gap that PR #47 missed. | ~50 | ✅ landed (PR #49) |
| **9.4** | Termination lifting | Randomised analog of `avss_termination_AS_fair`: introduce `RandomisedTrajectoryFairAdversary`, refactor `Liveness.lean`'s `FairASTCertificate.sound` to share its supermartingale + finite-descent core between deterministic and randomised, expose `RandomisedFairASTCertificate.sound` and `avss_termination_AS_fair_randomised`. The shared core takes the form of three measure-generic `_on` theorems (`pi_n_AST_fair_with_progress_det_on`, `pi_infty_zero_fair_on`, `partition_almostDiamond_fair_on`) that take an arbitrary trace measure plus an AE-trajectory invariant lift; deterministic and randomised specialise via `AlmostBox_of_inductive` and `AlmostBoxRandomised_of_inductive` respectively. Path **(c)** of §13.4 (specialised: generic over the trace measure rather than over the effect kernel — equivalent in content, simpler to implement). The `_rushing_randomised` wrapper is deferred to Phase 9.5 (which introduces `AVSSRushingRandomisedAdversary`). | ~280 | ✅ landed (PR #TBD) |
| **9.5** | Rushing-randomised adversary + 4 rushing wrappers | `AVSSRushingRandomisedAdversary` — randomised analog of `AVSSRushingAdversary` with PMF-valued schedule on the rushing-view σ-algebra (via `instCountableAVSSRushingView`); `R.toRandomisedAdversary` adapter; plus thin `_rushing_randomised` wrappers for correctness (existential-witness form), commitment (corrupt-dealer existential-witness form), coord-0 grid secrecy, and termination (the last depends on 9.4). Adds the measurability infrastructure on the rushing view that 9.3 deferred. See §13.5 for the full plan. | ~140 | ✅ landed (PR #55) |
| **9.6** | Step-`k` general secrecy | `avss_secrecy_AS_randomised` at coord `k > 0` — generalise PR #47's coord-0 form using `avssStep_coalitionGrid_invariant` lifted branchwise across `randomisedStepKernel`. The schedule PMF integrates the AE-equality. Independent of 9.4 / 9.5. See §13.6 for the full plan. | ~50 | ✅ landed (PR #53) |
| **9-integration** | Step-`k` rushing-randomised secrecy + Phase 9 stack merge | Merges PRs #53 (9.6) and #55 (9.5) into PR #54's stack. Exposes the literature-faithful `avss_secrecy_AS_view_rushing_randomised` (step-`k` rushing-randomised secrecy form) — a one-line wrapper around PR #53's `avss_secrecy_AS_randomised` via `R.toRandomisedAdversary`. Resolves the docs-conflict on §13 closure notes between the 9.4-followup and 9.5 stacks. Updates §11.5 C5 closure citation to its final form. | ~30 (incl. merge) | ✅ landed (PR #TBD) |

**Total**: ~980 LOC, 7 PRs.  Estimated worker time: 24–32 hours.

### 13.2. Sequencing

  * **PR 9.1** depends on nothing else — can be dispatched immediately.
  * **PR 9.2** depends on 9.1 (needs the type + mixture trace measure).
  * **PR 9.3** depends on 9.2 (needs the lifting meta-theorems to compose).
  * **PR 9.3-existential** depends on 9.3 (re-uses the lift pattern
    and per-step preservation lemmas from PR #47); ships the
    literature-faithful existential-witness analogs missing from PR #47.
  * **PR 9.4** depends on 9.3-existential (needs the partial-coverage
    AVSS lifts in place so the termination machinery slots into the
    same restatement pattern); independent of 9.5 and 9.6.
  * **PR 9.5** depends on 9.3-existential (needs the four classical
    `_randomised` analogs to wrap); the termination wrapper additionally
    depends on 9.4.  Independent of 9.6.
  * **PR 9.6** depends on 9.3 alone (the coord-0 form's
    `randomisedTraceDist_map_eq_of_deterministic_at_zero` extends
    branchwise to coord-`k` via `avssStep_coalitionGrid_invariant`).
    Independent of 9.4 and 9.5.

Phase 9 is **independent of Phase 8**: PRs 9.1–9.6 can ship in
parallel with Phases 8.1–8.8.  Once both phases land, AVSS will
quantify over arbitrary randomised rushing adversaries — the
literature-standard threat model.

### 13.3. Why this approach (Option 1) over kernel-form simulate (Option 3)

The Phase 7.4 AE-bridge `traceDist_AE_eq_avssSimulateTrace` assumes
deterministic schedules.  Two ways to lift it to randomised:

  * **Option 1 (Phase 9, this plan)**: keep the bridge deterministic;
    lift the *headline* theorems via the one-shot meta-theorem.  The
    bridge becomes a structural fact about deterministic-strategy
    AVSS, and the lifting argument operates above it.
  * **Option 3 (deferred)**: lift the bridge itself to kernel form,
    re-prove the inductive AE-bridge with a kernel-valued simulate
    `avssSimulateKernel : RandomisedRushingAdversary → ... → PMF (...)`.
    Strictly more work and only needed if a downstream consumer wants
    a kernel-form simulate.

Option 1 is the right choice because:

  1. **Amortises across the library**: every theorem in the library
     that universally quantifies over `Adversary` or
     `RushingAdversary` immediately becomes a randomised-adversary
     theorem, not just AVSS.
  2. **Smaller**: ~250 LOC total vs. ~400+ for option 3 (which would
     need to re-do every Phase 7.4–7.5 inductive proof in kernel form).
  3. **The cryptographic content lives in the deterministic case**:
     the Fubini argument is structural, not protocol-specific, so
     once the meta-theorem lands the cryptographic story is automatic.

✅ **Validated by Phase 9.5 (PR #55).**  The literature-standard
threat model — *randomised rushing* — is captured by
`AVSSRushingRandomisedAdversary` and the four
`_rushing_randomised` wrappers; each is a one-liner through
`R.toRandomisedAdversary`, confirming Option 1's amortisation
claim above (no protocol-specific work, the lifting argument lives
entirely above the deterministic bridge).

### 13.4. Phase 9.4 — Termination lifting

PR #46's `AlmostDiamond.lift_to_randomised` only derives "eventually"
from "always" trivially (`exact ⟨0, hω 0⟩`).  It cannot lift true
diamond claims like `avss_termination_AS_fair`, whose proof goes
through `FairASTCertificate.sound` (supermartingale +
Borel-Cantelli on a strictly-decreasing rank function under
trajectory fairness).  Phase 9.3 (PR #47) therefore deferred the
termination restatement; PR 9.3-existential (PR #49) closed the
literature-faithful existential-witness gap for the AS-Box theorems
but did not address termination.  Phase 9.4 closes that gap.

Like the existential `_randomised` analogs in PR #49, Phase 9.4
targets the **existential-witness form** of termination (quorum-of-
honest-outputs phrased as `honestOutputCount ≥ t + 1` rather than
`s.coeffs`-direct), keeping it migration-stable across the future
`s.coeffs → μ₀` transition.

#### Liveness.lean policy for 9.4

**`Leslie/Prob/Liveness.lean` is on-limits for this PR.**  The
deterministic `FairASTCertificate.sound` and the randomised
`RandomisedFairASTCertificate.sound` share the same supermartingale +
finite-descent core.  Three implementation paths were considered:

| Path | Work | Cleanliness |
|---|---|---|
| **(a)** Modify `Liveness.lean` to parameterise the supermartingale proof | ~150 LOC, reuses deterministic core | clean abstraction |
| **(b)** Re-derive supermartingale + finite-descent locally in `RandomisedAdversary.lean` | ~250-300 LOC, full re-proof | quarantined but heavy and duplicative |
| **(c)** Generalize `FairASTCertificate.sound` to take a parameterised effect kernel | ~100 LOC in `Liveness.lean`, both versions specialise | cleanest mathematically |

**Path taken (PR #TBD): a specialisation of (c).**  Rather than
parameterise over the effect kernel, the implemented refactor
parameterises over the *trace measure*: three measure-generic
helper theorems (`pi_n_AST_fair_with_progress_det_on`,
`pi_infty_zero_fair_on`, `partition_almostDiamond_fair_on`) take
an arbitrary `μtrace : Measure (Trace σ ι)` plus an AE-trajectory
invariant lift (`∀ᵐ ω ∂μtrace, ∀ n, cert.Inv (ω n).1`).  The
deterministic and randomised soundness theorems both specialise
to these by supplying their respective trace measure and lifting
the invariant via `AlmostBox_of_inductive` /
`AlmostBoxRandomised_of_inductive`.  This is equivalent in content
to (c) — the spec-specific dependency factored out is precisely
the inductive `cert.Inv` lift, the only place the original proof
mentioned the effect kernel — and produces ~50 LOC less plumbing
than (c) by skipping a kernel-form intermediate.

The deterministic surface API (`FairASTCertificate.sound`'s
signature and conclusion, plus `pi_n_AST_fair_with_progress_det`,
`pi_infty_zero_fair`, `partition_almostDiamond_fair`) is **unchanged**;
each existing theorem becomes a thin wrapper that lifts the
invariant via `AlmostBox_of_inductive` and forwards to its `_on`
counterpart.

#### Phase 9.4 introduces

  * Three measure-generic helpers in `Liveness.lean`:
    `FairASTCertificate.pi_n_AST_fair_with_progress_det_on`,
    `pi_infty_zero_fair_on`, `partition_almostDiamond_fair_on`.
    The existing deterministic theorems become thin forwarding
    wrappers (surface API unchanged).
  * `RandomisedTrajectoryFairAdversary spec F μ₀` in
    `RandomisedAdversary.lean` — randomised analog of
    `TrajectoryFairAdversary` parameterised by the same fairness
    predicate, with the trajectory progress witness AE on the
    mixture trace measure.
  * `FairASTCertificate.RandomisedTrajectoryFairProgress`,
    `RandomisedTrajectoryUMono`,
    `RandomisedTrajectoryFairStrictDecrease` — analogs of the
    deterministic predicates, restated on `randomisedTraceDist`.
  * `RandomisedFairASTCertificate.sound` — randomised specialisation,
    a thin wrapper around `partition_almostDiamond_fair_on` plus
    `AlmostBoxRandomised_of_inductive`.
  * `avss_termination_AS_fair_randomised` — the AVSS-side restatement,
    a thin wrapper.

##### Note on the fairness predicate

The trajectory-form AE-progress witness used here is the same shape
as the deterministic side (`TrajectoryFairProgress`); both
deterministic and randomised soundness consume the *trajectory*
witness as input.  In the randomised setting this witness can be
derived from a structural uniform-`ε` lower bound on the schedule
PMF for gated fair actions via Borel-Cantelli ("schedule PMF assigns
total weight `≥ ε > 0` to gated fair actions infinitely often, for
some uniform `ε`"), but the soundness machinery itself does not
need that derivation: the deterministic-decrease finite-descent
route closes from the trajectory witness alone.  A constructor
lemma deriving the trajectory witness from the uniform-`ε` bound
is left as an optional follow-up (no termination soundness theorem
depends on it).

**Follow-up landed (PR #54 update):**
`RandomisedTrajectoryFairAdversary.of_uniform_epsilon_bound` in
`Leslie/Prob/RandomisedAdversary.lean` derives the trajectory
witness from the uniform-`ε` schedule-PMF lower bound on gated
fair actions.  The proof is an iterative kernel-level argument
(the analog of Borel-Cantelli II for history-conditioned Bernoulli
trials with a uniform positive lower bound):

  1. Per-step bound: at every history `h`, the kernel mass on
     "next coordinate is non-fair-firing" is at most `1 - ε`
     (from the schedule-PMF hypothesis plus a per-action
     decomposition of `randomisedStepKernel_apply_tsum`).
  2. Inductive bound: `ν({ω | ∀ k < m, ω(N+k+1).2 ∉ fairFireSet F})
     ≤ (1 - ε)^m` for all `N`, `m`, by induction on `m` using the
     `Kernel.trajMeasure` marginal recurrence
     (`map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`).
  3. Continuity-of-measure limit: for fixed `N`, the tail event
     `{ω | ∀ n ≥ N, ω(n+1).2 ∉ fairFireSet F}` has measure
     `≤ (1-ε)^m` for every `m`, hence `0` (since `(1-ε)^m → 0`).
  4. Countable AE swap: union over `N` has measure `0`, and the
     complement gives the AE-trajectory progress witness.

This bypasses the conditional Borel-Cantelli machinery in
`MeasureTheory.Martingale.BorelCantelli`, whose connection to
`Kernel.trajMeasure` would require non-trivial infrastructure for
converting kernel mass at a history-prefix into a conditional
expectation w.r.t. the natural filtration on `Trace σ ι`.

The hypothesis is phrased on `FinPrefix σ ι n` rather than raw
`List` prefixes so that `currentState` is well-defined and the
gate predicate is meaningful.  The bound is on
`∑' i, [i ∈ F.fair_actions ∧ (spec.actions i).gate h.currentState]
R.strategy h.toList (some i)` — i.e., the schedule mass on **gated**
fair actions, since "ungated" fair-action samples stutter and do
not register as a fair firing in the trace.

The `_rushing_randomised` wrapper for termination
(`avss_termination_AS_fair_rushing_randomised`) is **closed by
Phase 9.5** (PR #55 — see §13.5), which introduces
`AVSSRushingRandomisedAdversary` and the measurability
infrastructure on the rushing-view σ-algebra; the wrapper itself
is a one-liner through `R.toRandomisedAdversary` plus a
`RandomisedTrajectoryFairAdversary` bundle.

#### Files OWNED

  * `Leslie/Prob/Liveness.lean` — `FairASTCertificate.sound` refactor.
    Off-limits for **all other phases**; on-limits for 9.4.
  * `Leslie/Prob/RandomisedAdversary.lean` — `RandomisedFairASTCertificate`
    and its `.sound`.
  * `Leslie/Examples/Prob/AVSS.lean` — `avss_termination_AS_fair_randomised`
    wrapper.
  * `Leslie/Examples/Prob/AVSS-MODEL-NOTES.md` — §13.1 status row 9.4 +
    §11.5 caveat status if all of 9.4–9.6 close it.

#### Estimated LOC

~280: 100 (Liveness refactor) + 30 (`RandomisedTrajectoryFairAdversary`)
+ 120 (`RandomisedFairASTCertificate.sound` specialisation) + 30
(AVSS-side wrapper).

#### Sequencing

Depends on PR #49 (9.3-existential).  Independent of Phase 8 and
Phase 10.  Independent of 9.5 and 9.6 (they don't touch
`Liveness.lean` or fair-AST machinery).

### 13.5. Phase 9.5 — Rushing-randomised adversary + 4 rushing wrappers

✅ **Landed (PR #55).** PR 9.3 deferred the `_rushing_randomised`
wrappers because `AVSSRushingRandomisedAdversary` doesn't exist yet
— defining it requires additional measurability infrastructure on
the rushing-view σ-algebra that's separate from PR 9.3's scope.
Phase 9.5 fills that gap.

#### Phase 9.5 introduces

  * `AVSSRushingRandomisedAdversary` — randomised analog of
    `AVSSRushingAdversary` (the rushing-view-restricted adversary).
    Schedule is a PMF on the rushing view, with the same
    `instCountableAVSSRushingView` measurability backbone as the
    deterministic case.
  * `R.toRandomisedAdversary` adapter — projects the rushing-view PMF
    schedule to a `History → PMF (Option ι)` schedule on the full
    state.
  * Four thin `_rushing_randomised` wrappers (one-liners around the
    corresponding `_randomised` theorems from PRs #47, #49, and 9.4):
    - `avss_correctness_AS_rushing_randomised`
    - `avss_commitment_AS_existential_rushing_randomised`
    - `avss_secrecy_AS_view_rushing_randomised`
    - `avss_termination_AS_fair_rushing_randomised` (depends on 9.4)

#### Files OWNED

  * `Leslie/Prob/Adversary.lean` (or `RandomisedAdversary.lean`) —
    `AVSSRushingRandomisedAdversary` + adapter.  Existing rushing
    adversary infrastructure lives in `Adversary.lean`; the randomised
    analog should live alongside it for consistency.  This is a small
    measurability extension, not a refactor.
  * `Leslie/Examples/Prob/AVSS.lean` — the four wrappers.
  * `Leslie/Examples/Prob/AVSS-MODEL-NOTES.md` — §13.1 status row 9.5.

#### Estimated LOC

~100: 50 (`AVSSRushingRandomisedAdversary` + adapter + measurability
glue) + 40 (four wrappers, ~10 LOC each).

#### Sequencing

Depends on PR #49 (9.3-existential).  The termination wrapper
additionally depends on 9.4.  Independent of 9.6.

### 13.6. Phase 9.6 — Step-`k` general secrecy

PR #47 lifted secrecy only at coord 0 (`avss_secrecy_AS_step_zero_grid_randomised`)
because PR #46's `randomisedTraceDist_map_eq_of_deterministic_at_zero`
only handles coord-0 projections.  Phase 9.6 generalises to all
`k : ℕ`.  Phase 9.5 (PR #55) added the *rushing* wrapper for the
coord-0 form (`avss_secrecy_AS_step_zero_grid_rushing_randomised`);
once 9.6 lands its step-`k` form, a parallel
`avss_secrecy_AS_view_rushing_randomised` rushing wrapper follows
from `R.toRandomisedAdversary` by the same one-liner pattern.

#### Why this is independent of 9.4

The step-`k` lift uses the deterministic-side fact
`avssStep_coalitionGrid_invariant` (every gated action preserves
`coalitionGrid`) and integrates that AE-equality branchwise across
`randomisedStepKernel`.  No supermartingale or Borel-Cantelli
machinery is involved.  9.6 has no fair-AST machinery interaction.

#### Phase 9.6 introduces

  * `randomisedTraceDist_map_eq_of_deterministic` — step-`k`
    generalisation of PR #46's coord-0 form.  Argument: each gated
    step's effect preserves the `coalitionGrid` projection (this is
    a structural fact, not adversary-dependent), so the schedule PMF
    integration of branchwise AE-equality gives total AE-equality.
  * `avss_secrecy_AS_randomised` — the headline step-`k` form, applied
    to the AVSS-specific `coalitionGrid C D` projection.

#### Files OWNED

  * `Leslie/Prob/RandomisedAdversary.lean` — generic step-`k` lift.
  * `Leslie/Examples/Prob/AVSS.lean` — AVSS-specific instantiation.
  * `Leslie/Examples/Prob/AVSS-MODEL-NOTES.md` — §13.1 status row 9.6.

#### Estimated LOC

~50: 30 (generic step-`k` lift) + 20 (AVSS instantiation).

#### Sequencing

Depends on PR #47 only.  Independent of 9.4 and 9.5.  Can ship at
any time after PR #47.

### 13.7. Risks

  1. **Mathlib Fubini availability**: the lifting argument uses
     `MeasureTheory.Integral.Fubini` for kernel composition.  This is
     well-established mathlib infrastructure; no new measure-theoretic
     content to develop.
  2. **Measurability hypotheses**: the meta-theorem needs the
     property `P` to be measurable.  All of our existing properties
     (terminated, output-determined, coalition-view marginals) are
     measurable, but each AVSS-side restatement needs to check this.
  3. **PR 9.4 supermartingale refactor**: parameterising
     `FairASTCertificate.sound` over the effect kernel may surface
     hidden assumptions in the existing deterministic proof.  If the
     refactor proves invasive (e.g., requires API changes that ripple
     to other `Liveness.lean` callers), fall back to path (b) — local
     re-derivation in `RandomisedAdversary.lean`.  Cost: ~150 LOC
     extra.
  4. **PR 9.4 fairness predicate sharpness**: the randomised
     `TrajectoryFairProgress` analog requires a uniform `ε > 0` lower
     bound on the schedule PMF's weight on gated fair actions.
     Mathlib's `MeasureTheory.Martingale.BorelCantelli` supports the
     countable-index integrated form, but the proof that the AVSS
     schedule PMF satisfies the `ε`-bound is a concrete obligation
     for AVSS callers (likely discharged via the rushing adversary's
     measurability witness).
  5. **PR 9.5 rushing-view σ-algebra**: defining
     `AVSSRushingRandomisedAdversary` requires a measurable structure
     on the rushing view that's compatible with PMF measurability.
     The deterministic case uses `instCountableAVSSRushingView`;
     the randomised case may need a `Decidable`-witnessed extension
     or a coercion to/from `Subtype` measurability.  Estimated minor.

### 13.8. Maintenance protocol

Same as §12.5 but for Phase 9: each PR's commit message updates the
corresponding row of §13.1 (statuses ⏳ → 🚧 → ✅).  After Phase 9
completes (PRs 9.1–9.6 all ✅), §11.5 (C5) should be marked
"✅ resolved by Phase 9 (PRs #41, #46, #47, #49, plus 9.4–9.6 PR
numbers)".

If 9.4 / 9.5 / 9.6 land out of order with respect to 9.4 → 9.5 (the
termination wrapper in 9.5 depends on 9.4), the affected row's
status reverts to 🚧 with a footnote describing the dependency
realisation.

### 13.9. Post-Phase-8.5d randomised termination follow-up (queued)

**Status: ⏳ pending framework PR.**

The `_randomised` and `_rushing_randomised` corollaries for
**termination** (PRs #54, #55) are typed against the
deterministic-descent route (`RandomisedFairASTCertificate.sound`).
Under the post-Phase-8.5b AVSS model, that route's
`RandomisedTrajectoryUMono` hypothesis is **unsatisfiable** because
corrupt-fired actions bump `avssU` (same reason the deterministic
version switched to BC running-min in Phase 8.5d-γ).  The randomised
termination theorems compile but are **vacuously-callable**.

To close: a two-PR stack lifting the BC running-min soundness
theorem to the randomised level.

| PR | Scope | LOC |
|---|---|---|
| **9.7-α (framework)** | `pi_n_AST_fair_with_progress_bc_of_running_min_drops_randomised` in `Leslie/Prob/Liveness.lean` + `RandomisedTrajectoryFairRunningMinDropIO` in `Leslie/Prob/RandomisedAdversary.lean`.  Real measure-theoretic content: the BC running-min argument re-derived for the kernel-mixture trace measure, paralleling the deterministic version's structure | ~150–200 |
| **9.7-β (AVSS-side)** | Define `consistent_quorum_AE_randomised` (analog of `consistent_quorum_AE` on the randomised mixture trace), switch `avss_termination_AS_fair_randomised` and `_rushing_randomised` to the new framework theorem, drop the now-unsatisfiable `RandomisedTrajectoryUMono` hypothesis, add `consistent_quorum_AE_randomised` and `RandomisedTrajectoryFairRunningMinDropIO` hypotheses | ~80 |

**Total**: ~230–280 LOC, 2 stacked PRs.

This work may be folded into Phase 11-β (which lifts `Secrecy` to
randomised at the framework level — same shape of work) or into
a Phase 12 prerequisite (UC composability requires usable
randomised termination).  Cross-reference: §11.5 cross-branch
caveat.

The other Phase 9 randomised forms — `avss_correctness_AS_*` /
`avss_commitment_AS_*` / `avss_secrecy_AS_*` (PRs #47, #49, #53,
#55, #56, #74) — are aligned with their deterministic counterparts
and do not need follow-up; only termination is affected.

### 13.10. Operational randomised secrecy follow-up (queued)

**Status: ⏳ pending Fubini plumbing.**

Phase 11-γ-randomised (PR #83) added the AVSS-side instance form
`avss_secrecy_AS_view_rushing_randomised_instance : SecrecyRushingRandomised
... view proj`, mirroring the deterministic Phase 11-γ instance
(`avss_secrecy_AS_view_rushing_instance`, PR #74).  The two
instances differ in **projection strength**:

| Variant | Projection wrapped | Underlying theorem |
|---|---|---|
| Deterministic (PR #74) | `(coalitionTraceView, schedulePrefix)` — operational, full literature shape | `avss_secrecy_AS_view_rushing` (PR #43, plus 8.5d-β-followup-7 dealerHonest-INDEPENDENT chain) |
| Randomised (PR #83) | `coalitionGrid C D (ω k).1` — **algebraic grid only** | `avss_secrecy_AS_view_rushing_randomised` (Phase 9.6, PR #53) |

The randomised instance is therefore for a **strictly weaker
projection**: it captures bivariate-grid secrecy but not the full
operational coalition-view + schedule-prefix joint distribution
that the deterministic instance proves.

To close the gap, an **operational randomised secrecy theorem**
parallel to `avss_secrecy_AS_view_rushing` is needed.  Required
content:

  * **Randomised AE-bridge**: lift the Phase 7.4 deterministic AE-
    bridge `traceDist_AE_eq_avssSimulateTrace` (which expresses
    the rushing trace as a deterministic pushforward of μ₀) to the
    randomised mixture trace.  This requires Fubini over the
    per-step adversary PMFs.
  * **Randomised algebraic-view factoring**: lift `avssSimulateTrace`
    to a randomised analog that integrates over R's coin flips at
    each step.
  * **Headline randomised theorem**: `avss_secrecy_AS_view_rushing_randomised_operational`,
    with conclusion `(randomisedTraceDist ...).map (coalitionTraceView, schedulePrefix) =
    same on the other secret`.

Estimated scope: ~150–250 LOC, single substantive PR, mostly in
`Leslie/Examples/Prob/AVSS.lean`.  May be combined with Phase 11-β-
followup (the framework-level `Secrecy → SecrecyRandomised` Fubini
direction) since both rely on similar measure-theoretic plumbing.

**Why not blocking**: the algebraic-grid randomised secrecy is
already enough for downstream Phase 12 composability arguments
that work at the polynomial level (e.g., random-secret-draw via
sum-of-uniforms).  Operational randomised secrecy is needed only
when downstream protocols want to reason about randomised
coalition-trace views directly, which is a less common pattern
in the AVSS literature.

## 14. Phase 10 — Generic deterministic-simulate meta-theorem

The Phase 7.4 inductive AE-bridge `traceDist_AE_eq_avssSimulateTrace`
currently lives in `AVSS.lean` §19.2.  Reviewing the proof: nothing
in it depends on AVSS-specific semantics.  The bridge is a fact about
**deterministic state-machine specs** (every effect is `PMF.pure`) and
**deterministic adversary strategies** — the AVSS instantiation is
the consumer, not the source of any structural reasoning.

Promoting the bridge to a meta-theorem in `Leslie/Prob/`
(a) shrinks `AVSS.lean` §19.2 to a one-page instantiation,
(b) makes the same machinery reusable by `BrachaRBC`, `SyncVSS`,
`AVSSAbstract`, and any future deterministic-spec protocol, and
(c) cleanly demarcates "protocol determinism" (structural,
generic) from "cryptographic security" (substantive, AVSS-specific).

Closely related to Phase 9 (randomised-adversary lifting): both
phases promote framework-level reasoning out of `AVSS.lean` and into
`Leslie/Prob/`.  Phase 10's meta-bridge holds for any
`(DeterministicProbActionSpec, Adversary)` pair; Phase 9's meta-lift
takes any such ∀-deterministic theorem to randomised.  Stacked
together: deterministic protocols get both for free.

### 14.1. Status tracker

| PR | Title | Scope | LOC | Status |
|---|---|---|---|---|
| **10.1** | `DeterministicProbActionSpec` + simulate machinery (data) | Define `DeterministicProbActionSpec σ ι := { init, gate, step }` in new file `Leslie/Prob/DeterministicSimulate.lean`; provide `toProbActionSpec` adapter; define generic `simulateNext` / `simulateRev` / `simulateTrace` reading only `gate`, `step`, and `Adversary.schedule`.  Plus structural `_length`, `_ne_nil`, `_succ_eq`, `_head_eq`, `_zero` simp lemmas. | ~150 | ✅ landed (PR #42) |
| **10.2** | The meta-bridge `traceDist_AE_eq_simulateTrace` | The substantive proof: for any `D : DeterministicProbActionSpec` and `A : Adversary` and any step `k`, `∀ᵐ ω ∂(traceDist D.toProbActionSpec A μ₀), ω k = simulateTrace D A (ω 0).1 k`.  Pure transcription of the existing AVSS-specific proof, with all references to `avssStep`, `avssSpec`, `actionGate` replaced by `D.step`, `D.toProbActionSpec`, `D.gate`. | ~300 | ✅ landed (PR #44) |
| **10.3** | AVSS instantiation: shrink §19.2 | Define `avssDeterministic := { gate := actionGate, step := avssStep }`. Prove `avssSpec sec corr = (avssDeterministic sec corr).toProbActionSpec` (rfl).  `avssSimulate{Next,Rev,Trace}` definitions kept verbatim (signatures unchanged); bridge lemmas `avssSimulate*_eq_simulate*` prove their propositional equality with the generic forms (the kernel's `defEq` on `noncomputable def`s with structure projections does not see through; the bridge is a small structural induction).  Replace `traceDist_AE_eq_avssSimulateTrace`'s 300-LOC inductive proof with a one-line application of `Leslie.Prob.traceDist_AE_eq_simulateTrace` plus `rw [avssDeterministic_toProbActionSpec, avssSimulateTrace_eq_simulateTrace]`.  Delete the dead helper chain (`avssSpec_R_stepKernel_AE_simulate`, `traceDist_step_zero_pair_marginal`, `traceDist_step_zero_snd_AE`, `avssSimulateRev_reverse_eq_ofFn`, old strong form). | net −185 LOC (353 deleted, 168 added) | ✅ landed (PR #51) |

**Total**: ~400 LOC across 3 PRs.  Net effect on AVSS.lean: shrinks by ~370 LOC.  Net effect on the codebase: +400 framework, -370 example = +30 LOC, but vastly more reusable.

### 14.2. Sequencing

  * **PR 10.1** depends on nothing else — can be dispatched immediately.
  * **PR 10.2** depends on 10.1 (needs the data definitions).
  * **PR 10.3** depends on 10.2 (needs the meta-theorem to apply).

Phase 10 is **independent of Phase 8 and Phase 9**: PRs 10.1–10.3 can ship in parallel with both, since:
  - Phase 8 modifies `AVSSState` and AVSS actions; Phase 10 is generic over the state/action types.
  - Phase 9 lifts deterministic theorems to randomised; Phase 10 *produces* a deterministic theorem (the AE-bridge) that 9's lifter can then handle.

When all three phases land, the AVSS chain reads:

```
(deterministic spec, det. adversary)              [Phase 10 meta-bridge]
  → trace AE-equals simulateTrace
  → (per-property pointwise reasoning, via rushing-adversary projection)
  → (deterministic theorem)                        [Phase 9 meta-lift]
  → (randomised theorem)
```

Each link is a one-shot meta-theorem; AVSS-specific content is only the
projection-and-composition step in the middle.

### 14.3. Why this is worth doing concretely

1. **Reuse**.  At least three other state-machine protocols in the library have `PMF.pure` effects:
   - `BrachaRBC` — no protocol-internal randomness; reliable broadcast.
   - `SyncVSS` — synchronous VSS, deterministic transitions.
   - `AVSSAbstract` — the simpler abstraction that predates the threshold-faithful AVSS.
   Each of these currently re-derives or hand-writes any trace-determinism reasoning it needs.  Once the meta-bridge lands, those proofs collapse to one-line instantiations.

2. **Composability with Phase 9**.  The two abstractions stack cleanly: any `(DeterministicProbActionSpec, Adversary)` pair gets the AE-bridge from Phase 10; any `∀ Adversary, P` theorem lifts to `∀ RandomisedAdversary, P` via Phase 9.  Each protocol gets both for free without further engineering.

3. **Sharper statement of what AVSS contributes cryptographically**.  Once the bridge is generic, the AVSS section is left holding only the cryptographic content: Shamir/bivariate row-poly secrecy + the polynomial-pushforward composition.  That's the right separation: protocol determinism is structural; cryptographic security is the substance.

4. **Demarcation of where randomness becomes load-bearing**.  As soon as a future protocol introduces a non-pure effect (a common-coin step, a random oracle), it stops fitting the `DeterministicProbActionSpec` abstraction — and that's the right place for the type system to register the obstruction, rather than the failure cropping up deep inside a protocol-specific lemma.

### 14.4. Subtlety — fallback parameter

The current `avssSimulateNext` takes a `fallback : AVSSState` argument used in the unreachable `prev = []` case (Lean totality).  In the meta-version this becomes `fallback : σ`.  If we want to remove it cleanly, the alternative is to define `simulateRev 0 := [(s_0, none)]` (already the base case) and take `head` as well-defined by the structural fact that the list is non-empty (`avssSimulateRev_ne_nil` already proves this).  Generalising it lets the meta-version state `simulateTrace` without a fallback.  Worth doing for cleanliness; not load-bearing.  Decide during PR 10.1.

### 14.5. Maintenance protocol

Same as §12.5 / §13.5 but for Phase 10: each PR's commit message updates the corresponding row of §14.1 (statuses ⏳ → 🚧 → ✅).  After Phase 10 completes, AVSS.lean §19.2 should be marked "✅ generalised — see `Leslie/Prob/DeterministicSimulate.lean`".

### 14.6. AVSS-side projections that stay AVSS-specific

The simulate machinery is generic; the projections downstream of it are not.  These remain in `AVSS.lean` even after Phase 10:

  * `simAlgebraicView R C k s_0 := (rowPolyOfDealer s_0.partyPoint s_0.coeffs ·, fun i p => (sim ... .local_).delivered)` — references `partyPoint`, `coeffs`, `local_.delivered`, `rowPolyOfDealer`.  AVSS-specific.
  * `simSchedulePrefix` — generic in shape, but its consumers in AVSS-side proofs reference AVSS-specific structure.
  * `coalitionTraceView`, `coalitionAlgebraicView`, `coalitionGrid` — all reference AVSS-specific types.

Phase 10 generalises the structural bridge between trace and simulate; the cryptographic projection of simulate onto the corrupt-coalition view remains AVSS-specific (and rightly so).

### 14.7. Closing note — Phase 10 complete

Phase 10 closed in PR 10.3 (#PENDING).  AVSS.lean §19.2's
`avss_traceDist_AE_eq_avssSimulateTrace` is now a one-line
instantiation of the generic meta-theorem
`Leslie.Prob.traceDist_AE_eq_simulateTrace` (PR #44) at
`avssDeterministic sec corr`.  The 300-LOC inductive proof chain in
§19.2.4 has been replaced by:

  * `avssDeterministic sec corr := { init := initPred sec corr, gate
    := actionGate, step := avssStep }` (~6 LOC).
  * Three `@[simp]` rfl-bridges
    (`avssDeterministic_{toProbActionSpec,init,gate,step}`).
  * Three structural-induction bridges
    (`avssSimulate{Next,Rev,Trace}_eq_simulate{Next,Rev,Trace}`)
    proving propositional equality with the generic forms — these
    work around a Lean kernel `defEq` quirk where structure
    projections on `noncomputable def` calls (`(avssDeterministic sec
    corr).gate`) do not unfold automatically through `rfl` in the
    presence of the surrounding `Filter.Eventually`/`Measure` machinery.
  * One-line proof of the headline theorem.

Net AVSS.lean impact: −185 LOC (353 deletions, 168 insertions).  The
`avssSimulate{Next,Rev,Trace}` definitions and structural lemmas
(`_length`, `_ne_nil`, `_succ_eq`, `_zero{,_fst,_snd}`,
`_head_eq`) are kept verbatim — they are referenced by the
downstream `avssSimulateTrace_simSyncInv` (§19.4.4) and by simp.  See
§19.2.4 in `AVSS.lean` for the new one-line proof and the deletion
manifest.

After this PR: `AVSS.lean §19.2` is marked **✅ generalised — see
`Leslie/Prob/DeterministicSimulate.lean`**.  All future protocols
that fit the deterministic-spec abstraction (BrachaRBC, SyncVSS,
AVSSAbstract) can apply the meta-theorem in one line; no further
trace-determinism plumbing needed.

## 14. Phase 11 — Secrecy framework abstraction

**Status: ✅ closed (modulo the post-Phase-9-merge deliverable 11-β).**
Phase 11-α ✅ + 11-γ ✅ + 11-δ ✅ + 11-ε ✅ landed; 11-β remains ⏸
deferred until Phase 9 (`RandomisedAdversary` integration) merges,
at which point its scope (a one-shot Fubini lift) is well-defined
and independent.

Extract `Secrecy` and `SecrecyRushing` as framework-level definitions
in `Leslie/Prob/Secrecy.lean` (Phase 11-α, ✅).  Each protocol's
headline secrecy theorem becomes an instance of the framework
abstraction (Phase 11-γ).  Phase 11-β adds the framework lift to
randomised adversaries (`Secrecy.lift_to_randomised`,
`SecrecyRushing.of_secrecy`).

**Why now (not earlier).**  Phase 8 has stabilised the AVSS-side
shape of "operational secrecy under a rushing adversary"
(`avss_secrecy_AS_view_rushing`'s dealerHonest-INDEPENDENT closure
via the cTV bridge).  Other protocols in the library (SyncVSS,
BenOrAsync, ...) will follow the same shape; abstracting now means
their secrecy theorems can be one-line corollaries instead of
re-deriving the chain.

**Sub-PR sequencing.**

| Sub-PR | Scope | LOC | Status |
|---|---|---|---|
| 11-α | `Leslie/Prob/Secrecy.lean` — `Secrecy` (deterministic-adversary form) and `SecrecyRushing` (rushing form); structural lemmas (`Secrecy.mono_proj`, `SecrecyRushing.mono_proj`, `Secrecy.toRushing`) | ~140 | ✅ |
| 11-β | `Secrecy.lift_to_randomised`, `SecrecyRushing.of_secrecy` (framework lifts to randomised adversaries) | ~80 | ⏳ (deferred until Phase 9 `RandomisedAdversary` integration) |
| 11-γ | AVSS instance: `avss_secrecy_AS_view_rushing` re-stated as `SecrecyRushing avssSpec ... := ...` | ~50 | ✅ |
| 11-δ | Apply to 8.6's row + column secrecy form (composes with the abstraction directly so 8.6 doesn't need its own framework boilerplate) | ~280 | ✅ (PR #75) — headline `Leslie.Prob.Polynomial.bivariate_evals_uniform_row_col` (statement + full proof via constant-fiber projection along `↑S ↪ ↑R × ↑R`); AVSS-side wrappers `avss_bivariate_corrGrid_uniform` / `_sec_invariant` (§19.6); auxiliary `PMF.uniform_pi_restrict`.  All axiom-clean (`[propext, Classical.choice, Quot.sound]`); zero sorries. |
| 11-δ-followup | Wire the row+col form into a *sibling* of the headline secrecy theorem.  `avss_secrecy_AS_view_rushing_bivariate` (`AVSS.lean` §19.7) bundles the existing trace-level `(coalitionTraceView, schedulePrefix)` sec-invariance and the polynomial-level `avss_bivariate_corrGrid_sec_invariant` into a single conjunction.  The original `avss_secrecy_AS_view_rushing` is unchanged (backward-compat). | ~80 | ✅ (this PR) |
| 11-ε | Cleanup, MODEL_NOTES finalisation: §12.1 row 8.6 → ✅, §12.3 post-Phase-8 secrecy row updated to cite the new sibling, §12.4 risk 4 closed, §14 marked ✅ closed. Final axiom hygiene check on the five load-bearing AVSS theorems (`avss_termination_AS_fair`, `avss_correctness_AS_existential`, `avss_commitment_AS_existential`, `avss_reconstruction`, `avss_secrecy_AS_view_rushing` + new sibling). | ~50 | ✅ (this PR) |

**Sequence.**  Phase 11-α landed after 8.5d-δ (this PR's parent).
Subsequent sub-PRs land before Phase 8.6, so 8.6's operational-secrecy
theorem instantiates the abstraction directly rather than re-deriving
the chain bottom-up.

**Phase 11-α deliverables (this sub-PR).**

The new file `Leslie/Prob/Secrecy.lean` adds two protocol-independent
predicates plus three structural lemmas, all axiom-clean
(`[propext, Classical.choice, Quot.sound]`):

  * `Secrecy spec μ₀ proj` — operational secrecy: under any
    deterministic adversary `A : Adversary σ ι`, the projected trace
    distribution `(traceDist spec A (μ₀ sec)).map proj` is invariant
    in the secret `sec`.
  * `SecrecyRushing spec μ₀ view proj` — view-restricted variant: the
    same equality but quantified over `RushingAdversary σ ι W` whose
    `toProtocolView = view`.
  * `Secrecy.mono_proj` / `SecrecyRushing.mono_proj` — coarsening the
    projection by a measurable map preserves secrecy (via
    `Measure.map_map`).
  * `Secrecy.toRushing` — plain secrecy implies rushing-secrecy for
    any view (the universal adversary class subsumes the
    rushing-adversary image).

The two main definitions intentionally mirror the existing AVSS-side
shape so that Phase 11-γ's instantiation is a one-liner.

**Phase 11-γ deliverables (this sub-PR).**

The AVSS instance `avss_secrecy_AS_view_rushing_instance` lives in
`Leslie/Examples/Prob/AVSS.lean` (§19.5) and is axiom-clean
(`[propext, Classical.choice, Quot.sound]`).  Diagnosing
`avssSpec`'s `sec` parameter showed it was vestigial — `sec` only
enters `avssSpec.init`, which `traceDist` does not consume (only
`spec.actions` is read by `stepKernel`).  Rather than refactor the
~230 in-file `avssSpec sec corr coeffs` call sites, we proved the
helper lemma `traceDist_avssSpec_sec_irrelevant` (defeq via `rfl`)
and used `avssSpec 0 corr coeffs` as the canonical sec-agnostic spec
for the instance:

  * `traceDist_avssSpec_sec_irrelevant` — `traceDist` is invariant
    under the `sec` parameter; closed by `rfl` since `stepKernel`
    only references `spec.actions`.
  * `avss_secrecy_AS_view_rushing_instance` — full
    `SecrecyRushing (avssSpec 0 corr coeffs) (μ₀ := …
    avssInitMeasure …) (avssCoalitionView corr) (proj := …)` with
    body `intro sec sec' R hR; rw [sec_irrelevant, sec_irrelevant];
    exact avss_secrecy_AS_view_rushing …`.

The instance closes the AVSS deliverable for 11-γ; downstream
protocols (SyncVSS, BenOrAsync) can mirror this pattern.

(See `PHASE-8-5d-CHECKPOINT.md` for the worker-side note if a fuller
plan is recorded there.)

**Phase 11-δ deliverables (this sub-PR).**

This is the +200 LOC row+column bivariate Shamir secrecy upgrade
**deferred since SyncVSS §10**.  It generalises Phase 7.7's
`bivariate_evals_uniform_full` (rectangular `pts_x × pts_y`) to the
literature-standard form on arbitrary subsets `S ⊆ R × R`:

  * `Leslie.Prob.Polynomial.bivariate_evals_uniform_row_col` — for
    `R ⊆ F` with `|R| ≤ t` and `0 ∉ R` and any subset
    `S ⊆ R ×ˢ R`, the joint evaluation distribution at `S` of the
    uniformly-sampled bidegree-`(t, t)` polynomial with
    `f(0, 0) = sec` is uniform on `↑S → F`.  Proof: corollary of
    `bivariate_evals_uniform_full` plus a constant-fiber projection
    along `↑S ↪ ↑R × ↑R`.

  * `PMF.uniform_pi_restrict` (auxiliary) — pushforward of
    `PMF.uniform (κ → α)` along precomposition with an injection
    `proj : ι → κ` is `PMF.uniform (ι → α)`.  This is the per-coord
    constant-fiber restriction lemma; proved via
    `PMF.uniform_map_of_surjective_constFiber` plus an explicit
    bijection between the fiber `{g | g ∘ proj = h}` and
    `(κ \ image proj) → α` (size `|α|^(|κ| − |ι|)`, constant in `h`).

  * AVSS-side instantiations (`Leslie/Examples/Prob/AVSS.lean` §19.6):
    `avss_bivariate_corrGrid_uniform` (uniformity of corrupt-coalition
    bivariate evaluations on any subset of `corrPts × corrPts`) and
    `avss_bivariate_corrGrid_sec_invariant` (sec-invariance corollary,
    by uniformity-on-both-sides).  Both are thin specialisations of
    the polynomial-level theorem via the standard `partyPoint`
    injection bridge.

**Axiom-cleanliness.** All four new declarations
(`bivariate_evals_uniform_row_col`, `PMF.uniform_pi_restrict`,
`avss_bivariate_corrGrid_uniform`, `avss_bivariate_corrGrid_sec_invariant`)
depend on `[propext, Classical.choice, Quot.sound]` only — zero
sorries, zero custom axioms.  The existing chain through
`bivariate_shamir_secrecy_rowPoly_full` and
`avss_secrecy_AS_view_rushing` is unchanged.

**Out of scope for the parent (PR #75 / Phase 11-δ).** Axis-zero
handling (the `0 ∈ R` case where the sec-axis is exposed and the
conclusion becomes conditional on the sec value) is documented in
§12.4 risk 4 but not formalised; the current statement requires
`0 ∉ R`.  Wiring the row+col form into a strengthened headline was
deferred to Phase 11-δ-followup — see below.

**Phase 11-δ-followup deliverables (this PR).**

The Phase 11-δ-followup sub-PR closes part (b) of §12.1 row 8.6 — the
"wire row+col into headline secrecy" deliverable — by adding a
*sibling* theorem to `avss_secrecy_AS_view_rushing`:

  * `avss_secrecy_AS_view_rushing_bivariate` (`AVSS.lean` §19.7).
    Bundles two sec-invariances into a single citation:
    **(a)** the existing trace-level
    `(coalitionTraceView, schedulePrefix)`-marginal sec-invariance
    (Phase 8.5d), and
    **(b)** the polynomial-level row+column sec-invariance from
    `avss_bivariate_corrGrid_sec_invariant` (Phase 11-δ / PR #75).
    The conjunction form is the right abstraction for downstream
    consumers because each clause matches their natural query —
    "is my operational view sec-invariant?" and "is my bivariate
    evaluation grid sec-invariant?" — and the two equalities concern
    *distinct measures* (the trace distribution vs. the
    bivariate-polynomial measure that `avssInitMeasure` is pulled
    back from).  A deeper joint pushforward that extracts the
    dealer's polynomial through the trace's initial state is
    queued for a later phase; it would add substantive measurability
    work without changing the cryptographic content.

The original `avss_secrecy_AS_view_rushing` is unchanged
(backward-compat); the sibling is *additive*.  Axiom hygiene is
preserved on all five load-bearing AVSS theorems
(`[propext, Classical.choice, Quot.sound]` only); zero sorries.

**Phase 11-ε deliverables (this PR).**

Phase 11-ε is the MODEL_NOTES finalisation that closes Phase 11.
Specifically:

  * §12.1 row 8.6 → ✅ landed (cites PR #75 for part (a) and this
    PR's `avss_secrecy_AS_view_rushing_bivariate` for part (b)).
  * §12.3 post-Phase-8 state table's "Secrecy" row updated to cite
    the new sibling theorem alongside the existing headline.
  * §12.4 risk 4 closed — both the polynomial-level row+col upgrade
    and the headline wiring are landed.
  * §14 Phase 11 marked ✅ closed (with 11-β still ⏸ deferred for
    post-Phase-9-merge).
  * Axiom hygiene check on the five load-bearing AVSS theorems
    (`avss_termination_AS_fair`, `avss_correctness_AS_existential`,
    `avss_commitment_AS_existential`, `avss_reconstruction`,
    `avss_secrecy_AS_view_rushing` + new sibling
    `avss_secrecy_AS_view_rushing_bivariate`) — all
    `[propext, Classical.choice, Quot.sound]`-axiom-clean.

## How to read the formalised theorems

If you're using AVSS as a black box for downstream protocol verification:

- Use `avss_termination_AS_fair`, `avss_correctness_AS`,
  `avss_reconstruction`, and `avss_secrecy` (polynomial-level) directly.
  These have the literature-expected meaning.

- For consumers wanting the rushing-adversary (literature-standard)
  formulation of termination / correctness / commitment, use the
  `*_rushing` variants (`avss_termination_AS_fair_rushing`,
  `avss_correctness_AS_rushing`, `avss_commitment_AS_rushing`) that
  quantify over `R : AVSSRushingAdversary corr` — the
  view-restricted adversary defined in `Leslie/Prob/Adversary.lean`.

- For `avss_commitment_AS` (and `_rushing`), internalize that "in our
  model" means under the abstraction in §2 above; the theorem is a
  useful abstraction for downstream work but doesn't capture
  corrupt-dealer adversarial choice (Phase 8 territory).

- For `avss_secrecy_AS` (trace-level grid form), read as: "the
  algebraic ideal grid view distribution is invariant in `sec` along
  any trace".  Phase 6 (PR #33) extended this to the operational view
  jointly with the schedule prefix (`avss_secrecy_AS_view`), and
  Phase 6.3 added the conditional theorem
  `avss_secrecy_AS_view_conditional` whose `h_aux` hypothesis
  Phase 7.4–7.5 will discharge against `RushingAdversary` (deferred —
  see §9 above).  An *unconditional* operational secrecy theorem
  ("corrupt parties learn nothing about `sec` along any trace") is
  therefore *not yet* a single named theorem in this branch; consult
  §1, §4, §9 above.

## Citing this formalisation

When citing the formalisation in a paper or report, the precise claim is:

> Leslie's AVSS module proves the four classical Canetti–Rabin properties
> — termination, correctness, commitment, secrecy — plus reconstruction,
> all axiom-clean, against two coexisting adversary models: a legacy
> `Adversary` with read-access to the full protocol state (a strict
> over-approximation of the literature's rushing adversary), and a
> `RushingAdversary` whose strategy is restricted to a measurable
> projection of the state to the corrupt coalition's view.  The classical
> theorems re-prove mechanically against the rushing adversary
> (`avss_termination_AS_fair_rushing`, `avss_correctness_AS_rushing`,
> `avss_commitment_AS_rushing`).  The polynomial-level secrecy is
> unconditional and matches the literature; the trace-level secrecy is
> at the algebraic grid view, with Phase 6 lifting it to the
> corrupt parties' operational view jointly with the schedule prefix and
> Phase 6.3 producing a conditional headline theorem
> `avss_secrecy_AS_view_conditional` whose schedule-leakage hypothesis a
> follow-up Phase 7.4–7.5 PR will discharge against the rushing
> adversary, completing the literature-faithful operational secrecy
> theorem.  The dealer's bivariate polynomial is modeled as a single
> global field rather than per-party messages, so the formalised
> commitment theorem is in an abstracted form.  ⚠ The formalised
> rushing adversary is **strictly weaker than CR '93's rushing
> adversary**: corrupt parties cannot send echoes/readys/amplify (C1),
> never receive honest echoes/readys (C2), and `dealerShare` is not
> fair-required (C3) — see §11.  Citers of `avss_secrecy_AS_view_rushing`
> in particular should note that secrecy *here* does not directly imply
> secrecy against a CR rushing adversary that controls corrupt-party
> messages; closing that gap is Phase 8 territory.  See
> `Leslie/Examples/Prob/AVSS-MODEL-NOTES.md` for the full abstraction
> inventory and pointers to the remaining literature-faithful refactor.


## 15. Phase 12 — UC-style composability layer (queued)

Phase 11's `Secrecy` and `SecrecyRushing` abstractions are *whole-protocol*
predicates — they say nothing about how secrecy composes across
subprotocol boundaries. Many cryptographic protocols (random secret
draw, MPC, byzantine agreement with sub-rounds, ...) build on AVSS or
similar primitives as black-box subroutines. We want compositional
reasoning: "the bigger protocol inherits secrecy from the subprotocol
+ a secrecy-respecting composer", without re-opening the subprotocol's
internal proof.

This is the operational form of **Universal Composability** (Canetti
UC, Backes-Pfitzmann-Waidner reactive simulatability). The Leslie
framework needs a new abstraction layer to express it.

### 15.1. Goal

Enable reasoning of the form:

> Q is a protocol that uses P as a subprotocol (P being a
> `SubprotocolFunctionality` with secrecy on its inputs).
> Q's combiner is "secrecy-respecting" (e.g., deterministic in P's
> outputs + non-secret state, or a sum-of-uniforms form).
> Then Q inherits secrecy on those inputs.

The motivating instance: random secret draw on top of `n` AVSS
instances + a sum combiner. The honest-uniform input plus AVSS's
per-instance secrecy plus sum-of-uniforms gives Q's secrecy.

### 15.2. Sub-PR sequence

| Sub-PR | Scope | LOC |
|---|---|---|
| **12-α** | `SubprotocolFunctionality` definition + structural foundations in `Leslie/Prob/Subprotocol.lean` (new file) | ~150 |
| **12-β** | Parallel composition operator on `ProbActionSpec`s (interleaving traces; per-instance μ₀) | ~200 |
| **12-γ** | Conditional-independence theorem under parallel composition (the load-bearing measure-theoretic content) | ~250 |
| **12-δ** | Sum-of-uniforms / convolution at the trace-distribution level (one-honest-uniform-addend ⇒ uniform sum) | ~100 |
| **12-ε** | Main composability theorem: subprotocol secrecy + secrecy-respecting composer ⇒ composite secrecy | ~150 |
| **12-ζ** | AVSS as `SubprotocolFunctionality` instance (bridging to existing `SecrecyRushing` from Phase 11-γ) | ~80 |
| **12-η** | RandomSecretDraw protocol definition + secrecy proof via composability | ~200 |
| **12-θ** | Cleanup + MODEL_NOTES rewrite reflecting Phase 12 state | ~50 |

**Total**: ~1180 LOC, 8 sub-PRs.

### 15.3. Key definitions (preliminary)

```lean
-- in Leslie/Prob/Subprotocol.lean (new file, Phase 12-α):
structure SubprotocolFunctionality (α β V : Type*)
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace V] where
  spec        : ProbActionSpec σ ι
  μ₀          : α → Measure σ            -- input → initial measure
  outputProj  : Trace σ ι → β            -- trace → output
  viewProj    : Trace σ ι → V            -- trace → corrupt-coalition view
  -- Operational guarantees:
  output_AE   : ∀ a A, ∀ᵐ ω ∂(traceDist spec A (μ₀ a)), outputProj ω = ...
  secrecy     : ∀ a a' A, (traceDist spec A (μ₀ a)).map viewProj
                       = (traceDist spec A (μ₀ a')).map viewProj

-- in Leslie/Prob/Composition.lean (Phase 12-β):
def parallelCompose
    (subs : Fin n → SubprotocolFunctionality α β V)
    (combiner : (Fin n → β) → γ)
    (Q_spec : ProbActionSpec _ _) : ProbActionSpec _ _
  := ...

-- Phase 12-ε (the load-bearing theorem):
theorem secrecy_of_parallel_composition
    (subs : Fin n → SubprotocolFunctionality α β V)
    (combiner : (Fin n → β) → γ)
    (h_each_secrecy : ∀ i, (subs i).secrecy)
    (h_combiner_respects : SecrecyRespectingCombiner combiner ...)
    : Secrecy (parallelCompose subs combiner ...) ...
```

### 15.4. Key risks

1. **Conditional-independence formalisation** (12-γ): the theorem "AVSS
   instances are independent given the bigger protocol's schedule" is
   measure-theoretically subtle.  Mathlib has independence lemmas for
   product measures; we need to lift to trace distributions over
   kernel-composed protocols.  If it doesn't fit cleanly in mathlib's
   existing infrastructure, may need a substantial helper.

2. **Adversary-class subtleties**: the bigger protocol's adversary
   has joint access to all subprotocol instances' corrupt views.
   Reducing to per-instance secrecy requires care: the per-instance
   adversaries derived from a Q-adversary depend on the schedule;
   formalising this dependency is a real obligation.

3. **Subroutine vs parallel composition**: this plan covers parallel
   composition (multiple P-instances + a combiner).  Subroutine
   composition (Q invokes P, awaits output, continues) is harder —
   the Q-trace contains nested P-traces with explicit
   call/return points.  Defer to Phase 12-followup or Phase 13.

4. **Schedule semantics**: if Q's adversary can adaptively schedule
   per-instance actions (e.g., delay AVSS_2 until learning AVSS_1's
   view), the conditional-independence argument needs care.  The
   right model is probably: the adversary controls Q's schedule and
   per-step picks one subprotocol-instance to advance.

### 15.5. Sequence in the master plan

```
Today's queue (post-Phase-11):
  Phase 11-α (PR #72)     — Secrecy framework abstraction ✅ landed
  Phase 11-γ (in flight)  — AVSS instance of SecrecyRushing
  Phase 11-δ (= Phase 8.6) — operational secrecy + row+col
  Phase 11-ε              — cleanup + docs
  ↓
  Phase 11 closure point — operational secrecy at the protocol level
  ↓
  Phase 12-α              — SubprotocolFunctionality abstraction      ← queued here
  Phase 12-β / γ / δ      — parallel composition + independence + sum
  Phase 12-ε              — main composability theorem
  Phase 12-ζ              — AVSS as SubprotocolFunctionality
  Phase 12-η              — RandomSecretDraw (the motivating instance)
  Phase 12-θ              — cleanup
```

### 15.6. Alternative: shortcut path

If random secret draw is the *only* compositional protocol we need,
the principled Phase 12 layer is overkill.  The shortcut is:

  * Formalise random secret draw directly as a `ProbActionSpec`.
  * Prove its secrecy *inline*, treating AVSS's per-instance secrecy
    as a library lemma (call site of `avss_secrecy_AS_view_rushing_instance`
    from Phase 11-γ).
  * No `SubprotocolFunctionality` abstraction, no composition operator.

Estimated cost: ~500 LOC for the random secret draw protocol +
specific secrecy proof.

The principled Phase 12 path costs ~1180 LOC but amortises across
future protocols (each new compositional protocol becomes ~150-200
LOC instead of ~500 LOC).

**Decision criterion**: if 3+ compositional protocols are planned,
go principled.  If random secret draw is one-off, shortcut.

### 15.7. Maintenance protocol

Same as §13.8: each Phase 12 sub-PR's commit message updates
§15.2's table from ⏳ pending to ✅ landed.  After Phase 12
completes, this section freezes as the canonical reference for
the composability layer.

## 16. CR '93 threshold and fairness audit

A reader who picks up the formalised theorems may reasonably ask:
"under what assumptions on `n` and `t` are these claims meaningful?"
The headline theorems all carry only `corr.card ≤ t` as their
threshold hypothesis (no explicit `n ≥ 3t + 1` or `n ≥ 4t + 1`).
The preamble of `AVSS.lean` does claim "`n ≥ 3t + 1`" as the model's
intended setting, but **no theorem in the codebase enforces this
bound as a hypothesis**.  This section audits where the actual bounds
sit and how the formalisation relates to Canetti–Rabin '93's stated
threat model.

### 16.1. Threshold bounds — what's enforced vs claimed

| Bound | Status in code | Where it appears |
|---|---|---|
| `corr.card ≤ t` | ✅ enforced as theorem hypothesis | All headline theorems take `h_corr : corr.card ≤ t` |
| `n ≥ 2t + 1` (so `n - t ≥ t + 1`) | ⚠️ implicit | Used silently when `n - t` is required to dominate `t + 1` (e.g., honest-output quorum existence in `consistent_quorum_AE_of_all_honest_delivered` cardinality argument) |
| `n ≥ 3t + 1` (Bracha echo-quorum intersection) | ❌ **claimed but not enforced** | Stated in `AVSS.lean` preamble (line 6); `quorum_intersection_card` lemma (§16 of `AVSS.lean`) carries the bound information but is **defined-but-never-used** — no headline theorem consumes it |
| `n ≥ 4t + 1` (Bracha-quality intersection: `≥ t+1` honest in any two output-quorums) | ❌ not enforced | Quorum-intersection lemma's docstring mentions it as a stronger setting; not actually used |

**Interpretation.**  The headline theorems are mathematically valid
under the weakest standing hypothesis (`corr.card ≤ t`), but their
*cryptographic content* is non-vacuous only under `n ≥ 3t + 1` —
because under weaker bounds, the runtime hypothesis `consistent_quorum_AE`
(see §16.3) becomes unsatisfiable in the actual Bracha-amplified
protocol semantics.

This is **not a soundness bug**: the theorems are honestly stated as
"if these runtime hypotheses are satisfied, then …".  But the
**discharge** of those runtime hypotheses (in particular
`consistent_quorum_AE`) is what requires `n ≥ 3t + 1`, and we don't
formalise the discharge — see §16.4.

### 16.2. Fairness predicate — `avssFair` vs CR '93 weak fairness

`avssFair : FairnessAssumptions` (AVSS.lean §11) defines the fair
action set as every action **except** corrupt-fired sends:

```
avssFairActions = { dealerShareTo p, partyDeliver p, partyEchoSend p,
                    partyEchoReceive p q, partyReady p, partyAmplify p,
                    partyReceiveReady p q, partyOutput p }
                  -- corrupt-fired sends NOT fair
```

with `isWeaklyFair := fun _ => True` (every fair action is weakly
fair-required to fire).

This matches CR '93's standard async fairness assumption: every
honest-party-initiated action eventually fires, every sent message
is eventually delivered.  Corrupt-fired sends are NOT fair because
the adversary chooses their schedule.

**Verdict**: `avssFair` is faithful to CR '93's weak fairness.

### 16.3. The `consistent_quorum_AE` runtime hypothesis

Phase 8.5d-γ (PR #70) re-scoped `avss_termination_AS_fair` to take
an extra runtime hypothesis:

```
def consistent_quorum_AE ... (A : Adversary ...) : Prop :=
  ∀ᵐ ω ∂(traceDist (avssSpec ...) A μ₀),
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      |{p ∉ corr ∧ ω k.dealerSent p ∧ ω k.dealerMessages p ≠ none}| ≥ n - t
```

In words: AE on traces, eventually at least `n - t` honest parties
have received their dealer share.

**Why we add this.**  Phase 8.5d-α split the dealer's broadcast into
per-party `dealerShareTo p` actions (closing caveat C4 — selective
non-broadcast).  Under that model, a corrupt dealer can selectively
refuse to send to some honest parties, blocking their output and
breaking termination unconditionally.

**CR '93's contrast.**  The original CR '93 protocol assumes the
dealer broadcasts a single message to all parties (atomic
broadcast).  Under that assumption, `consistent_quorum_AE` is
**derivable** from broadcast atomicity + `avssFair`'s weak-
delivery — no extra hypothesis needed.

**Verdict**: `consistent_quorum_AE` is **strictly extra** relative
to CR '93's stated threat model.  It's a runtime hypothesis our
formalisation needs because we model the more permissive selective-
non-broadcast adversary.  Under CR '93's atomic-broadcast model,
it would be a theorem, not a hypothesis.

The sanity-check lemma `consistent_quorum_AE_of_all_honest_delivered`
shows the form is satisfiable: under any schedule that AE delivers
to every honest party, the consistent-quorum hypothesis holds.

### 16.4. Bracha amplification gap

CR '93's protocol uses Bracha-style echo+ready amplification to
guarantee that **if any honest party outputs, then all honest
parties eventually output** (the "any-or-all" property).  The
amplification argument is:

  1. Output requires `readyReceived.card ≥ n - t`.
  2. Among `n - t` ready-senders, at least `n - t - t = n - 2t` are
     honest (since at most `t` are corrupt).
  3. Each of those honest ready-senders satisfies the `partyAmplify`
     gate (`readyReceived ≥ t + 1`), which forces every other honest
     party with `readyReceived ≥ t + 1` to also send ready.
  4. Cascade: once one honest party outputs, every honest party
     eventually has `readyReceived.card ≥ n - t` and outputs.

This argument requires `n ≥ 3t + 1` for the intersection step (so
that any two ready-quorums of size `n - t` share at least one honest
party).  **We do not formalise this argument.**  Instead, the
termination certificate `avssCert` (§12 of AVSS.lean) takes
`consistent_quorum_AE` as a hypothesis and produces termination from
there.

**Status**: this is a known formalisation simplification.  CR '93's
core "any-or-all" property is the missing piece.  Closing it would
require a substantive PR (~150–250 LOC) proving:

  ```
  theorem avss_any_or_all
      (h_corr : corr.card ≤ t) (h_n_geq : 3 * t + 1 ≤ n)
      ... :
    AlmostBox ... (fun s =>
      (∃ p ∉ s.corrupted, (s.local_ p).output.isSome) →
      ∀ᵐ ω ..., ∃ k₀, ∀ k ≥ k₀, ∀ p ∉ corr,
        (ω k).1.local_ p .output.isSome)
  ```

Once proven, `consistent_quorum_AE` could be discharged from
`avss_any_or_all` + dealer-broadcast + `avssFair`, recovering CR
'93's unconditional fair-AST claim.

### 16.5. Net assessment relative to CR '93

| CR '93 claim | Our formalisation |
|---|---|
| **Threat model**: `n ≥ 3t + 1`, byzantine static corruption ≤ `t` | Static corruption ✅; threshold bound **claimed but not enforced** |
| **Fairness**: weak fairness (every fair action eventually fires) | ✅ via `avssFair` |
| **Termination**: every honest party eventually outputs | ✅ conditional on `consistent_quorum_AE` (which CR '93 derives from broadcast + fairness; we leave as runtime hypothesis) |
| **Correctness** (honest dealer): every honest output equals `bivEval coeffs (partyPoint p) 0` | ✅ existential-witness form |
| **Commitment** (corrupt dealer): all honest outputs jointly determined | ⚠️ honest-dealer-conditional after Phase 8.5d-β; queued Phase 8.6 (Bracha amplification) drops the guard |
| **Secrecy**: `t`-coalition view independent of secret | ✅ operational view, dealerHonest-INDEPENDENT |
| **Reconstruction**: `t + 1` honest shares recover the secret | ✅ as Lagrange lemma (not a protocol phase) |
| **Bracha "any-or-all"** amplification | ❌ not formalised; replaced by `consistent_quorum_AE` runtime hypothesis |
| **Adaptive corruption** | ❌ static only; gap |
| **Dealer broadcast** (atomic) | ⚠️ permissive: per-party `dealerShareTo p` actions; closes caveat C4 but introduces `consistent_quorum_AE` hypothesis |

**Verdict**: **CR '93 property parity**, with two structural gaps:

  1. **Bracha "any-or-all" amplification** (§16.4) — replaced by
     `consistent_quorum_AE` runtime hypothesis.  Closing this would
     also let us drop the `consistent_quorum_AE` hypothesis on
     `avss_termination_AS_fair`, recovering CR '93's unconditional
     fair-AST.

  2. **Adaptive corruption** — our model is static; CR '93 is
     adaptive.  Closing this requires substantial state surgery
     (~600–1000 LOC) and is a known modern-formalisation
     simplification.

The threshold bound `n ≥ 3t + 1` is **not enforced** in our
theorems but is the bound under which the runtime hypotheses are
satisfiable in the actual protocol.  Adding `n ≥ 3t + 1` as an
explicit hypothesis to the headline theorems would make them
**self-documenting** but would not change their content (since the
bound is needed for the hypotheses' satisfiability, not for the
theorems themselves).  Recommended as a **light-touch follow-up**:
add `(h_n_geq : 3 * t + 1 ≤ n)` to the four headline theorems'
signatures, drop unused but document-aligned, ~20 LOC.

### 16.6. Recommended follow-ups (queued)

| # | Follow-up | Scope | LOC |
|---|---|---|---|
| **16-α** | Add `n ≥ 3 * t + 1` hypothesis to headline theorems for self-documentation | Light-touch, signature surgery | ~20 |
| **16-β** | Formalise Bracha "any-or-all" amplification → discharge `consistent_quorum_AE` from `avssFair` + broadcast | Substantive | ~150–250 |
| **16-γ** | Adaptive corruption support | Substantial state surgery | ~600–1000 |

