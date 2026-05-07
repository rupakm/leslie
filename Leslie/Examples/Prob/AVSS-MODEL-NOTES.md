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

### 11.2. C2 — Honest echoes/readys are addressed only to honest receivers

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

✅ **Resolved.** Phase B (this PR) folds `dealerShare` into
`avssFairActions` (Option B2 from the original plan).  The new
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

⚠ **All theorems in this formalisation universally quantify over
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

| PR | Title | Scope | LOC | Status |
|---|---|---|---|---|
| **8.1** | DealerPayload + state surgery (A-lite) | Foundational refactor: introduce `DealerPayload` type and `dealerMessages : Fin n → Option (DealerPayload t F)` field; keep `coeffs` alongside; migrate `dealerShare`/`partyDeliver`/`partyCorruptDeliver` to read from `dealerMessages`; add consistency invariant. **No theorem semantics change.** | ~200 (actual: 442/-82) | ✅ landed (PR #39) |
| **8.2** | Honest-dealer consistency invariant + correctness re-verification | Define `honestDealerConsistencyInv`: for honest dealer, ∃ witness coeffs such that every honest party's payload matches `rowPolyOfDealer`/`colPolyOfDealer`. Re-prove `avss_correctness_AS` against the new model with existential witness. Also adds bookkeeping `coeffsSecretInv` and `avss_correctness_AS_existential` (+ `_rushing` variant). Witness in current projection := `s.coeffs`; PR 8.5 will route the witness through μ₀'s sample. | ~250 (actual: 201/-0) | ✅ landed (PR #43) |
| **8.3** | Corrupt-dealer commitment (the genuine theorem) | The headline literature-faithful theorem `joinedConsistencyInv`: ≥ t+1 honest outputs ⇒ ∃ coeffs witnessing all of them.  Adds `consistentPayload` (per-payload consistency predicate, reusable by 8.4), `honestOutputCount`, `joinedConsistencyInv`, and the `AlmostBox` form `avss_commitment_AS_corrupt_dealer` (+ `_rushing` variant).  In the Phase 8.3 model the witness is supplied by `s.coeffs` and the cryptographic content (Bracha quorum + Vandermonde uniqueness) becomes load-bearing only after PRs 8.4 and 8.5 let the adversary deviate from `s.coeffs`; the *statement* — Canetti–Rabin's existential-witness commitment form — is unchanged across the migration. | ~300 (actual: 198/-0) | ✅ landed (PR #45) |
| **8.4** | Corrupt-party send actions (C1) + reception (C2) | Drop `p ∉ s.corrupted` from `partyEchoSend`/`partyReady`/`partyAmplify` gates. Update `partyEchoReceive` to populate corrupt receivers. Echoes carry payload values; consistency check predicate added; only consistent echoes count toward thresholds. Termination becomes conditional on "≥ n−t honest parties have consistent shares". | ~250 | ⏳ pending |
| **8.5** | Selective non-broadcast (C4) | Replace `dealerShare` with `dealerShareTo (p : Fin n)`; adversary chooses recipients and payloads. Move `coeffs` out of state into `μ₀` (or honest-dealer witness). Refactor variant analysis to handle the new fair-action structure. Most subtle PR; budget extra time. | ~150 | ⏳ pending |
| **8.6** | Operational secrecy under the full adversary | Re-prove `avss_secrecy_AS_view_rushing` against the post-8.4+8.5 adversary, which now has corrupt-party messages and honest-broadcast reception. Requires the **+200 LOC row + column secrecy** form (deferred since `SyncVSS.lean §10`) — the full polynomial-manipulation step. | ~250 | ⏳ pending |
| **8.7** | Adapter retirement / cleanup | Decide whether to keep pre-Phase-8 model alongside or retire it. Recommend a thin compatibility shim with deprecation warnings for downstream migration. | ~100 | ⏳ pending |
| **8.8** | MODEL_NOTES rewrite | Comprehensive rewrite to reflect post-Phase-8 state. Most §-level caveats become "✅ resolved by Phase 8". Preserve historical context. | ~150 | ⏳ pending |

### 12.2. Sequencing constraints

- **PRs 8.1–8.3** can be a tight unit (state surgery → honest-dealer correctness → commitment).
- **PR 8.4** depends on 8.1's `dealerMessages` infrastructure.
- **PR 8.5** depends on 8.4's consistency-check infrastructure.
- **PR 8.6** depends on PRs 8.4 + 8.5 (full adversary model + selective broadcast).
- **PRs 8.7, 8.8** are cleanup, can be deferred.

### 12.3. Post-Phase-8 state

After Phase 8 lands, AVSS will be **literature-faithful** for Canetti–Rabin '93:

| Theorem | Pre-Phase-8 (current) | Post-Phase-8 |
|---|---|---|
| Termination | Unconditional under fair scheduling (model forces dealer to all-broadcast) | Conditional on ≥ n−t honest parties receiving consistent shares (CR statement) |
| Correctness | Honest dealer ⇒ outputs consistent with `s.coeffs` (state field) | Honest dealer ⇒ outputs consistent with *some* bivariate polynomial (existential witness) |
| Commitment | Trivially true (single global `coeffs`) | Genuine joint-consistency theorem under corrupt dealer (Bracha amplification load-bearing) |
| Reconstruction | Lagrange theorem, unchanged | Lagrange theorem, unchanged |
| Secrecy | Row-poly secrecy under restricted adversary | Full row + column secrecy under CR rushing adversary |

### 12.4. Risks

1. **PR 8.3's commitment proof** is the hardest cryptographic content. It requires showing Bracha amplification's "all accepted shares are consistent with some polynomial" property — threading the consistency-check predicate added in 8.4 through quorum intersection. Some risk this becomes a multi-PR effort itself.

2. **Variant analysis re-verification** (PRs 8.4, 8.5): adding corrupt-party send actions to the fair set changes the variant's strict-decrease story. Each fair action must still strictly decrease U; the per-action `_lt` lemmas need rework. Risk: the K-weighting may need reshuffling.

3. **Row + column secrecy** (PR 8.6): the +200 LOC polynomial-manipulation step has been deferred since `SyncVSS.lean §10`. Doing it now is real cryptographic content (Vandermonde + Lagrange in two directions, with axis-zero handling). Could be its own multi-PR effort if we hit complications.

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
| **9.3** | AVSS-side restatements + MODEL_NOTES | One-line corollaries: `avss_secrecy_AS_view_rushing_randomised`, `avss_correctness_AS_randomised`, etc., each obtained by composing the Phase 9.2 meta-theorem with the existing deterministic-quantified theorem.  Update MODEL_NOTES §11.5 to mark C5 resolved. | ~50 | ⏳ pending |

**Total**: ~250 LOC, 3 PRs.  Estimated worker time: 6–10 hours.

### 13.2. Sequencing

  * **PR 9.1** depends on nothing else — can be dispatched immediately.
  * **PR 9.2** depends on 9.1 (needs the type + mixture trace measure).
  * **PR 9.3** depends on 9.2 (needs the lifting meta-theorems to compose).

Phase 9 is **independent of Phase 8**: PRs 9.1–9.3 can ship in
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

### 13.4. Risks

  1. **Mathlib Fubini availability**: the lifting argument uses
     `MeasureTheory.Integral.Fubini` for kernel composition.  This is
     well-established mathlib infrastructure; no new measure-theoretic
     content to develop.
  2. **Measurability hypotheses**: the meta-theorem needs the
     property `P` to be measurable.  All of our existing properties
     (terminated, output-determined, coalition-view marginals) are
     measurable, but each AVSS-side restatement (PR 9.3) needs to
     check this.

### 13.5. Maintenance protocol

Same as §12.5 but for Phase 9: each PR's commit message updates the
corresponding row of §13.1 (statuses ⏳ → 🚧 → ✅).  After Phase 9
completes, §11.5 (C5) should be marked "✅ resolved by Phase 9 (PR
#N)".

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
