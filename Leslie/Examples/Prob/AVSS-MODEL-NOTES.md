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
| Adversary information | Rushing — sees corrupt-coalition view + in-flight messages | Has read access to the full global state including `s.coeffs` |
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

`Adversary σ ι` (`Leslie/Prob/Adversary.lean`) is a strategy that picks the
next action conditioned on the current full global state `s : σ`.  Two
practical consequences:

1. **The adversary type has read access to the full state.**  This means the
   adversary's strategy can, in principle, branch on `s.coeffs` and on
   honest parties' `local_` fields (e.g., `(s.local_ p).rowPoly` for honest
   `p`).  Operational secrecy is not falsified by this only because the
   adversary's *output* (the chosen action) doesn't directly leak `s.coeffs`
   to the trace projection — but it can encode information about `s.coeffs`
   via *which actions it chooses to fire and in what order*.

   The salvage: our `coalitionView` and `coalitionGrid` projections only see
   corrupt parties' local states (or, for `coalitionGrid`, a derived
   algebraic content of `s.coeffs`).  So the adversary's free access to
   honest state is masked away by the projection, *provided that the
   projection itself doesn't leak the adversary's choices*.  In our
   formulation it doesn't: the projection is `fun ω => coalitionView (ω k).1`
   — only the state, not the action history.

   But: a downstream consumer that wants to reason about *what corrupt
   parties learn* must include the schedule (the action history) in the
   projection — and then they have to re-prove that the adversary's schedule
   choices don't leak information about `sec`.  In our model, since the
   adversary's strategy is allowed to branch on `s.coeffs`, this *fails*.

2. **Static corruption only.**  `corr : Finset (Fin n)` is part of the initial
   state and never changes.  The standard literature reduction "static ⇒
   adaptive" applies, so adaptive variants follow but require additional
   model machinery (corruption events).

### Implication for the formalised secrecy theorem

`avss_secrecy_AS` says: under any `Adversary`, the trace marginal of the
algebraic grid `coalitionGrid C D (ω k).1` is invariant in the secret.

This is sound because `coalitionGrid` is a function of `s.coeffs` and
`s.partyPoint` only (not of the adversary's strategy), and `s.coeffs` and
`s.partyPoint` are immutable across actions.  So the theorem doesn't actually
exercise the adversary's strategy at all — it's effectively the polynomial-
level secrecy `bivariate_shamir_secrecy` lifted through `μ₀`.

A literature-faithful operational secrecy theorem (Phase 6 + Phase 7, see
"Future directions" below) would require:

- A new `RushingAdversary` type whose strategy is a function of *only* the
  corrupt-coalition view + in-flight messages (not the full state).
- Replacing `s.coeffs` with per-party dealer messages so the dealer's
  inputs are scheduling-time data, not background state.
- Re-proving termination/correctness/commitment/reconstruction against the
  new adversary type (mostly mechanical).
- Then proving secrecy against the new adversary type — that's the genuine
  cryptographic statement.

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

## Future directions

The honest path to a literature-faithful AVSS — what we'd call a "Phase B+"
trajectory — has four components, each shippable as a separate PR:

1. **Phase 6: Operational view secrecy in the current adversary model.**
   Replace `coalitionGrid` with `coalitionView` (corrupt parties' actual
   `local_`).  Prove `coalitionView` factors through `coalitionGrid +
   schedule + invariants`.  Result: a theorem that says the corrupt
   parties' state distribution is invariant in `sec`, *under the existing
   strong adversary*.  Caveat: still doesn't address adversary information
   leakage via scheduling decisions.

2. **Phase 7a: Define `RushingAdversary`.**  New adversary type whose
   strategy is a function of (corrupt-coalition view + in-flight messages
   seen so far).  Show every `Adversary` implementing the rushing-adversary
   structure exists; provide adapter to the existing `Adversary`.

3. **Phase 7b: Re-prove existing classical theorems against `RushingAdversary`.**
   Most should be mechanical (termination/correctness/commitment hold
   against any admissible adversary).  Re-export with the stronger
   adversary type.

4. **Phase 7c: Per-party dealer messages.**  Replace `s.coeffs` with
   per-party messages `dealerMessages : Fin n → (RowPoly × ColPoly)`.
   Honest dealer = consistent assignment; corrupt dealer = adversarial
   choice subject to verifiability.  Re-prove commitment as the genuine
   "joint consistency" theorem.  Re-prove secrecy at `coalitionView`
   against `RushingAdversary` — *this* is the literature-faithful AVSS
   secrecy.

Estimated cost: Phase 6 ≈ 600 LOC; Phase 7a ≈ 200 LOC; Phase 7b ≈ 300 LOC;
Phase 7c ≈ 600–1000 LOC.  The bulk of the cryptographic content is already
in the formalisation; what's missing is largely *adversary-information
plumbing*, which is real engineering work but conceptually well-understood.

## How to read the formalised theorems

If you're using AVSS as a black box for downstream protocol verification:

- Use `avss_termination_AS_fair`, `avss_correctness_AS`, `avss_reconstruction`,
  and `avss_secrecy` (polynomial-level) directly.  These have the literature-
  expected meaning.

- For `avss_commitment_AS`, internalize that "in our model" means under the
  abstraction in §2 above; the theorem is a useful abstraction for
  downstream work but doesn't capture corrupt-dealer adversarial choice.

- For `avss_secrecy_AS` (trace-level grid form), read as: "the algebraic
  ideal grid view distribution is invariant in `sec` along any trace".  The
  *operational* meaning ("corrupt parties learn nothing about `sec`") is not
  yet proved against the rushing adversary; consult §1, §4 above.

## Citing this formalisation

When citing the formalisation in a paper or report, the precise claim is:

> Leslie's AVSS module proves the four classical Canetti–Rabin properties —
> termination, correctness, commitment, secrecy — plus reconstruction, all
> axiom-clean, against an adversary model that has read-access to the full
> protocol state (a strict over-approximation of the literature's rushing
> adversary).  The polynomial-level secrecy is unconditional and matches
> the literature; the trace-level secrecy is at the algebraic grid view
> rather than the corrupt parties' operational view.  The dealer's
> bivariate polynomial is modeled as a single global field rather than per-
> party messages, so the formalised commitment theorem is in an abstracted
> form.  See `Leslie/Examples/Prob/AVSS-MODEL-NOTES.md` for the full
> abstraction inventory and pointers to a literature-faithful refactor.
