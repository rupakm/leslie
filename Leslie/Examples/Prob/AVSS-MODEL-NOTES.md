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
| Static vs. adaptive corruption | Both treated; usually adaptive | Static (`corrupted` fixed at `μ₀` time) |
| Dealer-to-party communication | Per-party row + column polys, possibly inconsistent under corrupt dealer | Single global `s.coeffs` field; consistent by construction |
| Dealer's distribution choice | Honest = uniform with `f(0,0) = sec`; corrupt = adversarial | Both honest and corrupt dealer get uniform `coeffs` from `μ₀` |
| Secrecy granularity | Trace-level on corrupt parties' actual observable view | Trace-level on the algebraic ideal grid `bivEval coeffs ...` |
| Network model | Asynchronous with arbitrary delays, point-to-point messages | `Finset`-based in-flight queues; eventual delivery via fairness |
| Cryptographic strength | Information-theoretic | Information-theoretic (aligned) |

The formalisation is sound and useful as a stepping stone, but the gap between
its statements and the literature's statements is non-trivial.  Consumers of
this module should consult the relevant section below before relying on a
particular property.

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

2. **`RushingAdversary` strictly restricts adversary information.**
   Under a `RushingAdversary R`, the adversary's strategy is — by
   construction — a function only of the view-history
   `(R.view of state, action)`-pairs.  It *cannot* branch on
   `s.coeffs`, on honest parties' internal state outside the view, or
   on anything else outside `corr → AVSSLocalState`.  This is the
   literature-standard rushing adversary.

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
- ⏳ A *cryptographic-core* lemma "schedule prefix factors through the
  coalition's algebraic view" (Phase 7.4, **deferred**) and the
  composition `avss_secrecy_AS_view_rushing` (Phase 7.5, **deferred**)
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
  state (`coalitionView` projecting onto `local_` fields) is **not yet
  formalised**.  See **Future directions**.

### Implication

`avss_secrecy_AS` is well-named only with the qualifier *"of the algebraic
grid view"*.  It's a meaningful step (in particular, it lifts the polynomial-
level secrecy through the `traceDist` infrastructure) but it doesn't say
anything about what corrupt parties *operationally* observe.  In particular
it's silent on what `(s.local_ p).rowPoly` distribution looks like for
corrupt `p` after `partyCorruptDeliver` fires.

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

## 9. Phase 7.4–7.5 deferral — schedule-leakage closing theorem

### What's deferred

Phase 7 (this PR-set) delivers the rushing-adversary *type machinery* and
the classical-theorem wrappers (Phases 7.1–7.3, **landed**), plus the
docs update (Phase 7.6, this section).  The two cryptographic-core
deliverables originally scoped for Phase 7 — Phase 7.4 (a generic
`RushingAdversary.schedule_factors_through_view` lemma) and Phase 7.5
(the headline `avss_secrecy_AS_view_rushing` that composes 7.4 with
PR #33's conditional theorem) — are **deferred to a follow-up PR**.

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
The theorem `avss_secrecy_AS_view_rushing` should then follow by
`apply avss_secrecy_AS_view_conditional`.

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

5. ⏳ **Phase 7.4 + 7.5: schedule-leakage-closing theorem.**  See
   §9 above — the cryptographic-core composition that produces the
   unconditional `avss_secrecy_AS_view_rushing`.  Deferred to a
   follow-up PR.

6. ⏳ **Phase 8: Per-party dealer messages.**  Replace `s.coeffs` with
   per-party messages `dealerMessages : Fin n → (RowPoly × ColPoly)`.
   Honest dealer = consistent assignment; corrupt dealer = adversarial
   choice subject to verifiability.  Re-prove commitment as the
   genuine "joint consistency" theorem.  This is the
   literature-faithful AVSS modulo cryptographic content already in
   `BivariateShamir`'s deferred row-poly secrecy.

Estimated cost: Phase 6 ≈ 600 LOC (landed); Phase 7.1 ≈ 130 LOC
(landed); Phase 7.2 ≈ 90 LOC (landed); Phase 7.3 ≈ 70 LOC (landed);
Phase 7.4+7.5 ≈ 300–500 LOC (deferred); Phase 8 ≈ 600–1000 LOC.  The
bulk of the cryptographic content is already in the formalisation;
what remains is largely *adversary-information plumbing*, which is
real engineering work but conceptually well-understood.

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
> commitment theorem is in an abstracted form.  See
> `Leslie/Examples/Prob/AVSS-MODEL-NOTES.md` for the full abstraction
> inventory and pointers to the remaining literature-faithful refactor.
