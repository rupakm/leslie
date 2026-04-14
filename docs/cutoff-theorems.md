# Cutoff Theorems in Leslie

A reference for Leslie's cutoff infrastructure: what's already proved, how the
combinator framework interacts with cutoffs, and a detailed design for the
next target — cutoffs on the **number of rounds** explored in a round-based
algorithm.

This document is intended as durable reference. It does not track current
sorries or in-flight proofs.

---

## 1. Background and motivation

Distributed protocol verification in Leslie is parameterized by `n`, the
number of processes. A safety theorem has the shape

> For every `n : ℕ` and every reachable state of the `n`-process instance,
> the invariant holds.

This is a universal statement over an infinite family of transition systems,
and the proof obligation is correspondingly universal. Inductive invariants
discharge it when they are strong enough, but they still have to be
*discovered* and *proven* for every `n` uniformly.

A **cutoff theorem** reduces a universally-quantified correctness statement
to a finite collection of small instances:

> For every `n`, the `n`-process instance satisfies the invariant
>     iff
> every instance with `n ≤ K` satisfies a corresponding finite invariant.

The finite instances can be discharged by `decide` / `native_decide`, a model
checker, or by explicit case analysis. The target of cutoff reasoning is to
replace the universally-quantified inductive step with a decidable problem,
or at least a structurally bounded one.

Leslie has two cutoff results in place today (described in §2 and §3) and one
under active design (§4). This document unifies the picture.

---

## 2. Existing cutoff: symmetric threshold protocols

**Location:** `Leslie/Cutoff.lean`, `Leslie/Examples/OneThirdRuleCutoff.lean`.

### 2.1 The target protocol class

A **symmetric threshold protocol** in the HO model satisfies:

1. **Finite state domain.** Each process holds one of `k` values
   (`Fin k`). There is no other per-process state.
2. **Communication closure.** Messages sent in round `r` are either
   delivered in round `r` or lost forever — no stale messages from previous
   rounds interfere with current counts.
3. **Role symmetry.** All processes run the same deterministic update
   function; there is no "leader" role distinguished from "follower".
4. **Threshold decision.** A process updates its value based purely on the
   *count* of each value among received messages. The decision depends only
   on whether each count is above (or below) a fixed fraction `α_num / α_den`
   of `n`.

Formally in `Leslie/Cutoff.lean`, this is the `SymThreshAlg k α_num α_den`
structure. The step function maps `(current_counts, received_counts)` to
`new_counts` without consulting individual process identities.

### 2.2 The threshold view abstraction

The key abstraction: a `Config k n` — a tuple of `k` counts summing to `n` —
is abstracted to its `ThreshView`, which records, for each value, one of
three tags:

- `below` — strictly less than `α_num / α_den` of `n`
- `exactly` — exactly `α_num / α_den` of `n`
- `above` — strictly greater than `α_num / α_den` of `n`

Two configurations with the same `ThreshView` are behaviorally
indistinguishable to a symmetric threshold protocol: they trigger the same
per-value decisions in the same order. This is the "collapse" that makes the
cutoff work.

### 2.3 The cutoff bound

```lean
def cutoffBound (k α_num α_den : ℕ) : ℕ :=
  if α_den > α_num then
    k * α_den / (α_den - α_num) + 1
  else
    1
```

**Intuition.** For each value in `Fin k`, the count can sit in one of three
`ThreshView` tags. Changes in counts during a step are constrained: a value
can gain or lose support in bounded increments. The bound is the smallest `n`
such that every reachable `ThreshView` is already realized — adding more
processes cannot create a new threshold view.

For the one-third rule (k=2, α=1/3), the bound is `K = 7`. For any `n ≥ 7`,
if the invariant holds at `n = 7`, it holds at `n`.

### 2.4 The main theorem

```lean
theorem cutoff_reliable
    (alg : SymThreshAlg k α_num α_den)
    (inv : ConfigInv k)
    (h_det : inv.threshDetermined α_num α_den) :
    (∀ n (c : Config k n), inv n c) ↔
    (∀ n ≤ cutoffBound k α_num α_den, ∀ c : Config k n, inv n c)
```

**Direction (→):** trivial, restrict the universal.

**Direction (←):** the substance. Given `n > K`, find a smaller `n' ≤ K` with
the same `ThreshView`, apply the small-instance result, lift back via
`threshDetermined`.

### 2.5 Scope

- **Applies:** One-third rule, majority rule, absorbing threshold protocols,
  ThresholdConsensus combinator instance.
- **Does not apply:** Paxos (role asymmetry: proposers vs acceptors),
  Ben-Or (finite but the stepwise behavior is non-deterministic via the coin
  oracle and the invariant is not purely threshold-determined), HotStuff
  (ballot-indexed state beyond `k` values), any protocol with per-process
  unbounded state (ballots, logs, histories).

---

## 3. Combinators and cutoffs

**Location:** `Leslie/Examples/Combinators/CutoffIntegration.lean`,
`Leslie/Examples/Combinators/TerminationCutoff.lean`.

The protocol combinator framework (`Leslie/Examples/Combinators/`) introduces
reusable building blocks: `QuorumSystem`, `LockProperty`, `CPhase`,
`seq_compose`, and friends. The question is: **do these combinators
compose with cutoffs?**

### 3.1 Structural cutoff via combinators

`CutoffIntegration.lean` provides `SymCPhase` — a symmetric version of
`CPhase` where transitions are threshold-determined — and a composition
theorem:

> If each phase of a composed protocol is `SymCPhase` with bound `Kᵢ`, the
> composed protocol has bound `max(K₁, K₂, …, K_m)` under sequential
> composition.

This is a **structural cutoff**: the cutoff bound is derived from the
combinator structure, not proved separately for each protocol. The
combinator's `autoCutoff` lemma delivers concrete bounds for the six
demo protocols:

| Protocol                | Structure                          | K  |
|-------------------------|-------------------------------------|----|
| Raft                    | single phase, majority lock          |  9 |
| Multi-Paxos (per slot)  | 2-phase, majority                    |  7 |
| ThresholdConsensus      | 2-phase, 2/3 threshold               | 13 |
| VR                      | single phase, majority               |  9 |
| PBFT                    | 3-phase, 2/3                         | 13 |
| HotStuff                | 3-phase, 2/3 with chaining           | 16 |
| Fast Paxos              | 2-phase, mixed 1/2 + 3/4             | 17 |

These are bounds derived from the combinator. They do NOT mean these
protocols are fully verified via cutoff — the ballot-indexed invariants of
Paxos-family protocols still require the universal inductive proof, and the
combinator-style proofs decompose into quorum-intersection lemmas that are
uniform in `n`. The cutoff bound would apply if/when the invariant is
recast into a threshold-determined form.

### 3.2 Termination cutoff for TV-deterministic protocols

`TerminationCutoff.lean` proves a different kind of cutoff: not on the
*number of processes*, but on the *number of rounds* for **termination**.

> **Theorem (TerminationCutoff).** If a round-based protocol is
> *TV-deterministic* (the view-to-value function depends only on the
> threshold view, not on `n`), then the protocol terminates within
> `T` rounds at any `n` iff it terminates within `T` rounds at `n ≤ K`
> where `K` is the symmetric cutoff bound.

**Why TV-determinism matters.** For safety, the invariant only needs to
collapse across `n`. For termination, the *number of rounds* to decide
must also collapse. TV-determinism ensures that if the protocol terminates
at `n = K` after `t` rounds, it terminates at any `n ≥ K` after the same
`t` rounds, because the state trajectories project identically onto
threshold views.

**Instances:**
- OTR (1/3 rule): TV-deterministic.
- Majority rule: TV-deterministic.
- Absorbing-at-threshold protocols: TV-deterministic.
- BenOr: **NOT** TV-deterministic (coin oracle depends on nondeterminism, not
  threshold view).
- Paxos family: **NOT** in scope (role asymmetric, not SymThreshAlg).

### 3.3 Limits of the current combinator cutoff

1. **Fixed value domain.** All combinator cutoffs assume `Fin k` for a
   fixed `k`. Ballots (unbounded), logs (unbounded), and histories break this.
2. **Threshold-determined invariants only.** The invariant must be expressible
   as a predicate on threshold views, not on absolute counts.
3. **Sequential composition only.** Parallel or nested phases need additional
   work; the combinator framework handles sequential but not yet concurrent
   compositions.
4. **Safety OR termination, separately.** Combined cutoffs (e.g., safety
   bound + termination bound) are not yet composed into a single "full
   verification cutoff".

---

## 4. Round-based cutoffs: a design proposal (on hold)

This section describes a cutoff result on the **number of rounds** to be
explored in a round-based algorithm. **Status: the design is preserved
for future use but the theorem is not being formalized at this time.**
Three feasibility studies (BenOr, OTR, Paxos) failed to find a target
protocol in Leslie's current corpus where the theorem does nontrivial
work. See §4.12 for the combined finding.

### 4.1 The question

A round-based algorithm in the HO model runs for arbitrarily many rounds. In
principle, verifying safety requires reasoning about executions of arbitrary
length. The existing node-cutoff (§2) bounds `n`, but the number of rounds
per execution is still unbounded — the inductive invariant must be maintained
forever.

**Target theorem (informal):**

> If a round-based algorithm satisfies certain "round locality" conditions,
> then its safety invariant holds in all executions iff it holds in all
> executions of length at most `K` starting from a finite set of *canonical
> round configurations*.

This would reduce safety verification to a finite model-checking problem
(bounded `n` via §2, bounded rounds via this new result).

### 4.2 The core insight: round-shift invariance

A round-based algorithm typically does not care about the *absolute* values
of round numbers — only about relative orderings. Formally, if we add a
constant `k` to every round number in the state (every process's current
round, every round-indexed piece of history), the algorithm's behavior is
indistinguishable.

This is analogous to *α-renaming* in programming languages or *data
independence* in model checking: the algorithm is a function of the
*shape* of the round distribution, not of specific round labels.

If this holds, the state space quotiented by the shift action becomes
finite (up to additional observer constraints), and verification reduces
to exploring the quotient.

### 4.3 Formal state-level operations

Three typeclass-level operations are needed, provided per protocol:

```lean
class RoundShift (S : Type) where
  /-- Add k to every round-valued field in the state. -/
  shift   : ℤ → S → S
  shift_zero (s : S)          : shift 0 s = s
  shift_add  (j k : ℤ) (s : S) : shift (j + k) s = shift j (shift k s)

class RoundObserver (S : Type) [RoundShift S] where
  /-- The largest round present in the state. -/
  maxRound : S → ℤ
  /-- The smallest round present in the state. -/
  minRound : S → ℤ
  /-- Observers are equivariant under shift. -/
  maxRound_shift (k : ℤ) (s : S) : maxRound (shift k s) = maxRound s + k
  minRound_shift (k : ℤ) (s : S) : minRound (shift k s) = minRound s + k
```

**Why ℤ, not ℕ.** Shifting by `-k` must be a total operation for the
quotient argument to work. Reachable states always have nonneg rounds
in practice, but the shift action requires a full group.

**Why both max and min.** The cutoff normalizes to `minRound = 0` (WLOG
the earliest process is at round zero), and the window condition is
stated relative to `maxRound` (the "frontier" of active rounds).

### 4.4 Round-shift invariance of the algorithm

```lean
structure RoundShiftInvariant (A : ActionSpec S Act) [RoundShift S] : Prop where
  /-- The set of initial states is closed under shift. -/
  init_closed : ∀ k s, A.init s → A.init (RoundShift.shift k s)
  /-- The transition relation is shift-equivariant. -/
  next_equiv  : ∀ k s s' act,
                A.next s s' act ↔
                A.next (RoundShift.shift k s) (RoundShift.shift k s') act
```

**Subtlety about `init_closed`.** Leslie's typical init predicate says "every
process is at round 0". That is *one orbit* of the shift action, not
shift-closed: applying `shift 1` gives "every process at round 1", which is
not literally the original init. Two ways to handle this:

1. **Redefine init.** Restate init as "every process is at the same round,
   value unspecified". This is the shift-orbit of the original, and the
   semantics are preserved because in any reachable trace the absolute
   initial round is irrelevant.
2. **Introduce a quotient spec.** Define a new algorithm `A^†` whose states
   are shift-orbits of `A`'s states. The new transition is `A`'s transition
   lifted to orbits. Prove safety on `A^†`, then transfer back to `A` via
   "every reachable `A`-state is in some reachable `A^†`-orbit".

Option 1 is easier to formalize; option 2 is cleaner mathematically. For a
first feasibility study, option 1 is the recommended path.

### 4.5 Bounded round advance

```lean
structure BoundedAdvance (A : ActionSpec S Act)
    [RoundShift S] [RoundObserver S] (D : ℕ) : Prop where
  max_advance  : ∀ s s' act, A.next s s' act →
                 RoundObserver.maxRound s' ≤ RoundObserver.maxRound s + D
  min_monotone : ∀ s s' act, A.next s s' act →
                 RoundObserver.minRound s ≤ RoundObserver.minRound s'
```

For almost every Leslie round-based algorithm, `D = 1` — a single step
advances at most one process's round by at most one. `min_monotone` says
slow processes may catch up but never regress, which is standard for
pure HO-model protocols.

### 4.6 Round-window locality (the hard condition)

```lean
class RoundWindow (S : Type) [RoundShift S] [RoundObserver S] where
  /-- `agreeAbove r s₁ s₂` means s₁ and s₂ agree on all round-indexed
      content whose round is ≥ r. Below r is unconstrained. -/
  agreeAbove : ℤ → S → S → Prop

  -- Equivalence axioms:
  agree_refl  : ∀ r s,       agreeAbove r s s
  agree_sym   : ∀ r s₁ s₂,   agreeAbove r s₁ s₂ → agreeAbove r s₂ s₁
  agree_trans : ∀ r s₁ s₂ s₃, agreeAbove r s₁ s₂ → agreeAbove r s₂ s₃ →
                              agreeAbove r s₁ s₃

  -- Weaker as r increases (more freedom = weaker constraint):
  agree_mono  : ∀ r₁ r₂ s₁ s₂, r₁ ≤ r₂ →
                agreeAbove r₁ s₁ s₂ → agreeAbove r₂ s₁ s₂

  -- Agreement all the way down = equality:
  agree_eq    : ∀ s₁ s₂, agreeAbove (RoundObserver.minRound s₁ - 1) s₁ s₂ ↔
                s₁ = s₂

  -- Shift respects window equivalence:
  agree_shift : ∀ k r s₁ s₂,
                agreeAbove r s₁ s₂ ↔
                agreeAbove (r + k) (RoundShift.shift k s₁) (RoundShift.shift k s₂)

structure RoundLocal (A : ActionSpec S Act)
    [RoundShift S] [RoundObserver S] [RoundWindow S] (W : ℕ) : Prop where
  /-- If two pre-states agree above (maxRound - W), transitions
      produce window-equivalent successors. -/
  next_respects : ∀ s₁ s₂ s₁' act,
    RoundWindow.agreeAbove (RoundObserver.maxRound s₁ - W) s₁ s₂ →
    A.next s₁ s₁' act →
    ∃ s₂', A.next s₂ s₂' act ∧
           RoundWindow.agreeAbove (RoundObserver.maxRound s₁' - W) s₁' s₂'
```

**Informal reading.** A step never reads or writes state below
`maxRound - W`. Data more than `W` rounds in the past is garbage from the
algorithm's perspective and can be discarded (or re-initialized
arbitrarily) without affecting future behavior.

### 4.7 Invariant conditions

```lean
structure RoundInvariant (I : S → Prop)
    [RoundShift S] [RoundObserver S] [RoundWindow S] (W : ℕ) : Prop where
  /-- The invariant only looks at the top W rounds. -/
  window_local : ∀ s₁ s₂, RoundWindow.agreeAbove
                 (RoundObserver.maxRound s₁ - W) s₁ s₂ →
                 (I s₁ ↔ I s₂)
  /-- The invariant is shift-invariant. -/
  shift_inv    : ∀ k s, I s ↔ I (RoundShift.shift k s)
```

### 4.8 The target cutoff theorem

```lean
theorem round_cutoff (A : ActionSpec S Act) (I : S → Prop)
    [RoundShift S] [RoundObserver S] [RoundWindow S]
    (hAlg : RoundShiftInvariant A)
    (hAdv : BoundedAdvance A D)
    (hLoc : RoundLocal A W)
    (hInv : RoundInvariant I W)
    (n : ℕ) :
    (∀ s, Reachable A s → I s) ↔
    (∀ cfg ∈ canonicalConfigs n W,
     ∀ k ≤ n * D + W,
     ∀ s, ReachableFromIn A cfg k s → I s)
```

**Canonical configurations** are all assignments `Fin n → Fin (W+1)`,
quotiented by symmetric permutations of processes and by shift
normalization. For reasonable `n, W`, this is a small finite set
(upper bound `(W+1)^n / n!`).

**Proof sketch (not yet formalized).**

1. **(←) direction (target).** Assume the right-hand side. Given an
   arbitrary reachable state `s` with `¬ I s`, we must reach a
   contradiction.
   - Shift `s` so `minRound s = 0`. This is WLOG by `RoundShiftInvariant`
     of `A`, `init_closed`, and `shift_inv` of `I`.
   - Let `M = maxRound s`. By `BoundedAdvance`, the trace to `s` has
     length `≥ M` (since max advances by ≤ D per step and starts at 0 for
     a canonical init, where min = max = some base round).
   - If `M ≤ W`, then `s` is already a "small-window" state, handled by the
     RHS directly.
   - If `M > W`, use `RoundLocal` to construct a state `s̃` agreeing with `s`
     above `M - W` but with everything below zeroed out. `s̃` has
     `maxRound = M` and `minRound ≥ M - W`. Shift by `-(M-W)` to get
     `maxRound = W, minRound = 0`. By `window_local` of `I`, `¬ I s̃`.
     `s̃` is reachable from a canonical config within `W` steps via the
     truncation argument. Contradiction.

2. **(→) direction.** Trivial restriction of the universal.

The missing piece: formalizing "truncation" as a concrete operation on
states and showing that the truncated-then-shifted state is reachable from
a canonical config. This is where the `RoundWindow.agreeAbove` equivalence
is used.

### 4.9 Scope: where this will and won't apply

**Important revision from initial scoping.** Feasibility studies on BenOr
and OTR (`docs/benor-round-cutoff-feasibility.md`,
`docs/otr-round-cutoff-feasibility.md`) revealed that **Leslie's
`RoundAlg`-based round protocols are all structurally degenerate for this
theorem.** The reason is architectural: `RoundAlg.update` has signature
`P → S → (P → Option M) → S` — it has no access to round history or to
any round-indexed data. Every `RoundAlg`-based protocol (OTR, BenOr,
LastVoting, FloodMin, LeaderBroadcast, BallotLeader, …) therefore has
`W = 0` trivially, and the round cutoff theorem collapses to vacuity.

The real target class is **ballot-indexed protocols** — those built on
the base `Spec` abstraction with per-process state types that include
explicit round/ballot-valued fields.

**Real candidates (protocols with genuine round-indexed state):**
- Paxos (`rep q i`, `acc i` store ballot-tagged values; `hSafe`
  quantifies over ballot orderings) — the primary target
- Multi-Paxos (per-slot ballot-indexed state)
- Raft, HotStuff, PBFT (view-indexed quorum certificates)
- VRViewChange (view-indexed view-change messages)

**Out of scope:**
- All `RoundAlg`-based protocols (BenOr, OTR, etc.) — no round-indexed
  state to compress, so `W = 0` trivially and the theorem is vacuous.
- Gossip protocols with unbounded history accumulation
- Algorithms with absolute round numbers baked in (e.g., "round 0 is
  bootstrap mode")
- Rotating-coordinator protocols where coordinator identity depends on
  the absolute round modulo n

**The key feasibility question** for ballot-indexed protocols is whether
invariants that currently quantify over *all* lower ballots (like Paxos's
`hSafe : ∀ c < ballot q, ∃ Q, …`) can be reformulated to reference only
a bounded window of ballots (`current`, `current - 1`, etc.) without
losing the proof. If yes, ballot-indexed protocols enter the scope of
the round cutoff and admit a finite-unrolling verification. If no, the
theorem does not apply and cutoff effort should focus elsewhere.

### 4.10 Interaction with node cutoffs

The eventual target is a **dual cutoff**: bound `n` via §2, bound rounds
via §4, and conclude that the full safety problem reduces to finite
verification at `(n ≤ K_nodes, rounds ≤ K_rounds)`. The two cutoffs are
independent in form but may compose tightly: the same `threshView`
abstraction that collapses across `n` may also collapse across round
histories in a favorable way. Exploring that composition is a follow-up
after the round-cutoff theorem is established in isolation.

### 4.12 Combined feasibility finding

Three feasibility studies were performed:

1. **BenOr** (`docs/benor-round-cutoff-feasibility.md`) — degenerate.
   BenOr's state has no round-indexed fields beyond the global counter.
   All round cutoff instances hold trivially with `W = 0` and the theorem
   delivers no verification value.

2. **One-Third Rule** (`docs/otr-round-cutoff-feasibility.md`) — same
   degeneracy, traced to a deeper architectural cause: **every protocol
   built on Leslie's `RoundAlg` framework is structurally round-history-free
   because `RoundAlg.update` has no access to round-indexed data**. This
   excludes all `RoundAlg`-based protocols from ever providing a meaningful
   round-cutoff target.

3. **Single-Decree Paxos** (`docs/paxos-round-cutoff-feasibility.md`) —
   a different degeneracy. Paxos has ballot-indexed state (`rep`, `acc`)
   and is shift-invariant, but its "ballot dimension" is already finite
   at the model level: bounded by `m`, the fixed number of proposers.
   There is no unbounded round dimension in single-decree Paxos to cut
   off. Multi-decree variants (Multi-Paxos, Raft) are the only plausible
   targets, and they require multi-dimensional cutoff reasoning that
   doesn't fit the current single-round design.

**Combined finding:** no protocol in Leslie's current corpus satisfies
the round cutoff theorem's non-triviality conditions. The theorem is
consistent and its instances mechanize cleanly, but it has no current
user.

**Decision:** suspend formalization of the round cutoff theorem. Keep
this design section as reference. Revisit if and when Leslie gains a
multi-decree protocol with explicit slot × ballot state.

### 4.11 Risks and open questions

1. **`agreeAbove` mechanization.** For ad-hoc state types, there's no
   generic derivation of `RoundWindow`. Each protocol needs a user-written
   instance, and getting it wrong breaks soundness. An attribute-driven
   approach (`@[round_valued]` marking round-typed fields) would help but
   requires Lean elaborator support.
2. **Implicit rounds.** Round values embedded inside records (e.g., "the
   round at which I voted") are easy to miss. Users must identify every
   round-valued field; missing one corrupts the shift action.
3. **Init reformulation.** Every protocol's existing init predicate
   typically names a concrete round (usually 0). Cutoff applicability
   requires rewriting each to "all processes at the same round,
   unspecified". This is a semantic change — mild, but real.
4. **Bounded-window coverage.** Algorithms that use "previous round's
   data" (e.g., Paxos 1b reports, OneThirdRule's majority-of-last-round)
   have `W = 2`, so the bound is tight. Algorithms with deeper history
   (k-round histories for some `k > 2`) have larger `W`, inflating the
   cutoff constant but preserving applicability.
5. **Paxos reformulation.** The most interesting research question: can
   Paxos's `hSafe` be restated in a window-local form without losing the
   proof? If yes, Paxos enters the scope of the round cutoff, and the
   dual node+round cutoff applies to Paxos. This would be novel.

---

## 5. Bounded-unrolling cutoff for stateless verification

This section describes a different kind of cutoff — one that reduces
verification to straight-line simulation of bounded-length traces from
a finite set of symbolic initial configurations. Unlike the round
cutoff in §4 (on hold), this one has a concrete target: OTR at the
existing node cutoff `K = 7`. The motivation and the sketch below are
the design basis for a planned implementation.

### 5.1 The problem with existing cutoffs in practice

The node cutoff (§2) reduces "safety for all n" to "safety for n ≤ K",
and the combinator cutoff (§3) gives structural bounds on K. Both are
*logical* iffs — they reduce the verification problem but do not
execute it. To actually check safety at n ≤ K, two paths exist:

1. **Prove an inductive invariant.** Find `I` with `Init → I`,
   `I ∧ next → I'`, `I → P`. This is what Leslie currently does.
   Cost: finding `I` (hard, requires insight) + proving it (routine
   but laborious). No runtime cost.

2. **Model-check the finite instance.** Explore the reachable state
   space at `n ≤ K` until fixpoint. Cost: stateful MC with cycle
   detection. Must hash visited states. Memory proportional to state
   space size.

Neither is ideal: (1) requires human insight; (2) requires a stateful
model checker and is not trivially parallelizable.

**Target: stateless bounded model checking.** Enumerate a finite set of
symbolic initial configurations, and from each one run straight-line
traces up to a computable depth bound. Check the safety property at
every state along each trace. No cycle detection, no visited-state
hashing, no induction. Parallelism is trivial: each (config, trace_id)
is an independent task.

This mode of verification requires **an analytically-derived depth
bound**. Classical BMC uses heuristic or k-induction bounds; the target
here is a bound proved from the protocol structure.

### 5.2 The safety diameter

For a finite transition system `T` with safety property `I`, define:

> **Safety diameter `D_I(T)`:** the smallest `d` such that if `I` holds
> on all prefixes of length `≤ d` from every reachable state, then
> `I` holds everywhere.

Equivalently, the smallest `d` such that every invariant violation has
a witness trace of length `≤ d` from some reachable state.

This is weaker than the full diameter of `T` — longer traces can't
introduce new violations if shorter ones didn't. Bounded-unrolling
verification needs the safety diameter, not the full diameter.

### 5.3 OTR: phase structure and dynamics

OTR with `n` processes, two values, communication predicate
`|HO_p| > 2n/3`. Safety target: `lock_inv` — "if any process has
decided `v`, then `h_v(s) > 2n/3`" (where `h_v(s)` is the number of
processes holding `v` in `s`).

**Observation 1 (adoption requires super-majority).** The OTR update
adopts `v` only when the local view has `> 2n/3` votes for `v`. Each
vote in the local view comes from a distinct sender holding `v`. So
for any process `p` to adopt `v`, we need `|HO_p ∩ H_v| > 2n/3`, which
(by pigeonhole with `|HO_p| > 2n/3`) forces `h_v > 2n/3`.

In other words: **a process can only adopt a value that already has
global super-majority.**

**Observation 2 (phase 1 is absorbing).** If no value has
super-majority at `s`, then any successor `s'` of `s` satisfies
`s' = s`. *Proof:* by Observation 1, no process can adopt any value.
The OTR update leaves state unchanged.

**Observation 3 (phase 2 is absorbing and monotone).** If some value
`v` has super-majority at `s`, then for any successor `s'`:
- The unique super-majority value in `s'` is still `v` (by
  `super_majority_unique`, at most one value has super-majority at
  once, and adoptions only increase holder counts).
- `h_v(s') ≥ h_v(s) > 2n/3`.

**Corollary (phase transitions are impossible).** The phase of a state
is preserved by all transitions. OTR runs either entirely in phase 1
(no super-majority, state frozen, no decisions ever, safety vacuous)
or entirely in phase 2 (super-majority on some `v`, decisions only for
`v`, `lock_inv` holds by construction).

### 5.4 Safety diameter bound for OTR

In phase 1, the state never changes. Zero state-changing transitions.

In phase 2, `h_v(s)` is monotone non-decreasing. Every state-changing
transition adopts at least one process from `w ≠ v` to `v`, so
strictly increases `h_v` by at least 1. Starting at
`h_v ≥ ⌊2n/3⌋ + 1` (minimum super-majority), the maximum number of
state-changing transitions before reaching `h_v = n` is:

> `n - (⌊2n/3⌋ + 1) = ⌈n/3⌉ - 1`

After this many transitions, the state is fully locked (all processes
hold `v`) and no further state-changing transitions are possible.

**Safety diameter:** `D_safety(OTR at n) ≤ ⌈n/3⌉ - 1`.

**Tightness:** a trace can achieve this bound. Starting at `h_v =
⌊2n/3⌋ + 1`, the environment can schedule one adoption per step,
realizing the full `⌈n/3⌉ - 1` bound.

**At the existing node cutoff `n = K = 7`:** `D ≤ 2`.

### 5.5 Canonical initial configurations

For OTR at `n = 7, k = 2`, the set of distinct initial configurations
(modulo round counter and decision state) is parameterized by the
holder split:

```
Γ_raw = { (h_v0, h_v1) : h_v0 + h_v1 = 7 } = 8 configurations
```

Up to the `v0 ↔ v1` symmetry, there are 4 distinct equivalence classes:
`(0,7)`, `(1,6)`, `(2,5)`, `(3,4)`.

**Per-class phase and diameter:**

| Configuration | Super-majority? | Phase | Max state changes |
|---|---|---|---|
| `(0,7)` | `v1` (h=7) | 2 (locked) | 0 |
| `(1,6)` | `v1` (h=6 > 14/3) | 2 | 1 |
| `(2,5)` | `v1` (h=5 > 14/3) | 2 | 2 |
| `(3,4)` | neither (4 ≤ 14/3) | 1 | 0 |

So at `n = 7`, the worst case is `(2,5)`-equivalent with 2 state changes.
`D = 2` is tight and all three non-degenerate configurations require
≤ 2 steps to reach fixpoint.

### 5.6 Stateless verification procedure

```
verify_otr_safety(n = 7):
  for γ in { (0,7), (1,6), (2,5), (3,4) }:      -- 4 canonical configs
    for π in enumerate_traces(γ, depth = 2):     -- bounded depth
      for s in π:
        assert lock_inv(s)                       -- pointwise check
```

The per-trace check is straight-line simulation: no state hashing, no
cycle detection. Each trace explores one specific sequence of
environment choices (HO collections) from a symbolic start.

**Trace count.** At each step, the environment picks an HO collection
`ho : Fin 7 → Fin 7 → Bool` subject to `|HO_p| > 4`. Naively there are
`2^49` HO collections; most are equivalent for OTR's behavior. The
effective choice is "which subset of processes adopts in this step",
which is bounded above by `2^7 = 128` per step. With symmetry
reduction and the phase-2 structural constraint, the per-step choice
further collapses.

**Upper bound:** `4 configs × 128^2 steps × 3 states per trace
≈ 200,000 state checks`. Lower bound after symmetry: `< 100`. Either
way, feasible via `native_decide` or a custom trace enumerator.

### 5.7 The theorem statement

```lean
theorem otr_bounded_unrolling_cutoff :
    (∀ n s, Reachable (otr_spec n) s → lock_inv n s) ↔
    (∀ γ ∈ canonicalConfigs 7,
     ∀ π : Trace (otr_spec 7) γ,
     π.length ≤ 2 →
     ∀ s ∈ π, lock_inv 7 s)
```

**Proof ingredients:**

1. The existing node cutoff (`cutoff_reliable` in `Leslie/Cutoff.lean`):
   reduces LHS to "safety at `n ≤ 7`".
2. The phase-structure lemmas (Observations 1–3): prove that OTR at
   `n ≤ 7` has `D_safety ≤ 2`.
3. Every reachable state of OTR at `n ≤ 7` is in the trace-closure of
   some canonical `γ` within `D` steps.
4. Compose: safety at `n ≤ 7` reduces to bounded-depth trace
   verification from canonical configs.

### 5.8 Comparison with existing cutoffs

| Method | Needs inductive invariant? | Needs state hashing? | Needs cycle detection? |
|---|---|---|---|
| Existing cutoff + inductive proof | Yes | No | No |
| Existing cutoff + stateful BFS | No | Yes | Yes |
| **Bounded unrolling (§5)** | **No** | **No** | **No** |

The bounded-unrolling approach is strictly weaker than stateful BFS
(no state hashing), and is a different tradeoff against inductive
proof — no need to guess `I`; run the simulation and check the safety
property directly at each state.

### 5.9 Generalization to other threshold protocols

The argument for OTR generalizes to any threshold protocol with:

1. **A monotone progress measure.** "Count of the locked value" (or
   equivalent) is monotone non-decreasing and strictly increases per
   state-changing transition.
2. **Single-value lock.** Once one value has the threshold, no other
   value can (proved by a `super_majority_unique`-style lemma).
3. **Bounded maximum.** Progress measure is bounded by `n`.

**Instances:**
- **Majority rule.** `D ≤ ⌈n/2⌉ - 1`.
- **Absorbing-at-threshold protocols.** `D ≤ n - K_threshold`.
- **Per-view/per-slot BFT protocols (PBFT, HotStuff).** `D_per_view =
  O(n)`; multi-view bounds require additional view-change counting.
- **Paxos (single-decree).** Phase-structure argument over proposer
  rounds; `D = O(mn)`. See Appendix C for ballot-counting details.

### 5.10 Implementation roadmap

Work breakdown for OTR bounded-unrolling cutoff in Leslie:

1. **Formalize the progress measure** (`holder_count_max`,
   `super_majority_value`) as definitions. ~50 lines.
2. **Prove the phase structure lemmas** (Observations 1–3) at the
   `RoundState` level. ~100 lines.
3. **Prove the safety diameter bound** as a lemma: from any reachable
   state at `n ≤ 7`, at most 2 state-changing transitions reach a
   fixpoint. ~50 lines.
4. **State the `otr_bounded_unrolling_cutoff` theorem** and prove it,
   using the existing `cutoff_reliable` as one ingredient. ~80 lines.
5. **Demonstrate via `#eval` or `decide`** at `n = 7`, enumerating
   the canonical configs and verifying safety along each depth-2
   trace. ~30 lines.

Total: ~300 lines, one focused session. The work sits in a new file
`Leslie/Examples/OneThirdRuleBoundedUnrolling.lean` (or similar),
importing `Leslie/Cutoff.lean` and `Leslie/Examples/OneThirdRule.lean`.

### 5.11 Dependencies and obstacles

**Depends on:**
- The existing `cutoff_reliable` theorem (for the `n ≤ K` reduction).
- The `Config.succ` deterministic abstraction (as a tool for reasoning
  about successor states symbolically).

**Obstacles:**
- **HO enumeration cost.** Naively, per-step HO choices are `2^49` at
  `n = 7`. Symmetry reduction and the phase-2 structural constraint
  collapse this, but realizing the collapse inside Lean is nontrivial.
  May need a custom symmetry-aware trace enumerator rather than a
  brute-force `decide`.
- **Bridging `Config.succ` and the actual transition.** The existing
  cutoff works at the `Config` (ThreshView) level; the bounded-unrolling
  theorem should ideally work at the real-state level. An intermediate
  lemma relating `Config.succ` diameter to real-state diameter is
  needed.
- **Trace enumeration inside Lean.** To make this a verified result
  (not just `#eval`-checked), the trace enumerator must live inside
  the kernel or use `native_decide`. Small-instance feasibility is
  clear; scaling is not.

### 5.12 Status of concrete instances

As of this writing:

| Protocol | Threshold | Config level | RoundState via bridge | Demo |
|---|---|---|---|---|
| One-third rule | 2/3 | ✓ `otr_bounded_unrolling_cutoff` | ✓ via `binaryOtrRsta` | ✓ `verifyCanonical7 = true` |
| Majority rule | 1/2 | ✓ `majority_bounded_unrolling_cutoff` | ✓ via `majorityRsta` | ✓ `verifyCanonical5 = true` |
| Absorbing-at-threshold | varies | Planned | — | — |
| PBFT / HotStuff (per view) | 2/3 | Planned | — | — |
| Single-decree Paxos | majority (proposer+majority quorum) | Not yet attempted | **Does not fit the current bridge** | — |

Both OTR and majority-rule implementations share the exact same
proof structure (phase 1 absorbing, phase 2 absorbing-and-monotone,
single-step lock, depth-2 bounded trace), with only the threshold
constants changing. This strongly suggests that an abstract
`PhaseAbsorbingThreshold` theorem could be factored out and
instantiated for both — a future refactor candidate, not a blocker.

### 5.13 Single-decree Paxos via bounded-unrolling: what would be required

Paxos is structurally incompatible with the `RoundSymThreshAlg`
bridge from Commit 2 of the bounded-unrolling work. Three specific
obstacles, each requiring a different framework extension:

#### 5.13.1 Role asymmetry

`RoundSymThreshAlg` assumes every process runs the same update
function over a uniform local state. Paxos has two roles:

- **Proposers** maintain `(prop : Option Value, got1b : Fin n → Bool,
  rep : Fin n → Option (Nat × Value))` and run three actions
  (phase 1a implicit via ballot ownership, phase 2a, a passive role
  in phase 2b).
- **Acceptors** maintain `(prom : Nat, acc : Option (Nat × Value),
  did2b : Fin m → Bool)` and run two actions (phase 1b, phase 2b).

A bridge for Paxos would need a **role-parameterized
`RoundAlg`** where local state and update depend on a role
discriminator. This is a nontrivial extension of `Leslie/Round.lean`.

#### 5.13.2 Non-threshold state

`cutoff_reliable` assumes the safety invariant factors through
`ConfigInv k` — a predicate on threshold counts. Paxos's safety
invariant `hSafe` (and the 9 auxiliary invariants `hA`–`hJ`,
`hRepBound`/`hF`) reference *specific values* in `rep` and `acc`,
not just "how many are above a threshold". Specifically:

- `hC` : `rep q i = some (b, v) → ∃ p, ballot p = b ∧ prop p = some v`
- `hG` : given `did2b p i ∧ got1b q i ∧ ballot q > ballot p`, there
  *exists* a report in `rep q i` with the right ballot

These are not threshold properties. They reference the actual
ballot value in each acceptor's recorded state. Collapsing them to
a `ThreshView` loses essential information.

A bridge for Paxos would need to abandon `ThreshView` abstraction
and work directly with per-process state, which defeats the purpose
of the node cutoff.

#### 5.13.3 The phase-counting diameter argument

Despite the above, **single-decree Paxos does admit a safety
diameter bound**, via a completely different argument than the
phase-absorbing threshold protocols:

> **Claim (§5.9).** Single-decree Paxos has safety diameter
> `O(mn)`, where `m` is the number of proposers and `n` is the
> number of acceptors.

**Phase counting proof sketch.** Every action fires at most once
per structural slot:
- Phase 1a (implicit): `m` slots (one per proposer)
- Phase 1b: `m · n` slots (one per (proposer, acceptor) pair)
- Phase 2a: `m` slots (one per proposer)
- Phase 2b: `m · n` slots (one per (proposer, acceptor) pair)

Total slots: `2m + 2mn = O(mn)`. Every state-changing action fills
exactly one slot and cannot fire twice (the action's guard becomes
`false` after firing). Hence the diameter is bounded by `O(mn)`.

**What this proof requires:**
1. A per-action "slot consumed" counter defined on `PaxosState`
2. A lemma that each action strictly increases the counter by 1
3. A bound that the counter is ≤ `O(mn)` at all reachable states
4. A finite-instance check at small `(m, n)` — `m = 2, n = 3` gives
   a bounded trace length of `O(6) = O(10)` actions

This is a different shape than the phase-absorbing argument used
for OTR and majority. It's a **monotone counter** argument rather
than a **fixpoint** argument. The bounded-unrolling framework
would need a second specialization for this class.

#### 5.13.4 Tractable subproblems

Rather than attempting the full abstraction, these intermediate
targets are more actionable:

1. **Single-proposer Paxos** (`m = 1`). With one proposer, there's
   no role asymmetry in the sense that matters — the proposer runs
   deterministically and all acceptors are symmetric. Safety
   diameter reduces to `O(n)` (just the phase-1b and phase-2b
   acceptor loops). This is essentially "one-shot voting with an
   elected leader" and could use a variant of the majority-rule
   framework.

2. **Two-proposer Paxos**. The minimum case where ballot ordering
   matters. Still small enough that a custom diameter argument
   might fit in a single file without abstracting over roles.
   This tests whether the phase-counting argument can be
   formalized directly without a reusable framework.

3. **Single-decree Paxos with bounded ballots**. Fix a concrete
   `m, n` (say `m = 3, n = 5`) and prove safety via
   `native_decide` on a bounded-depth trace. No general theorem;
   just a demonstration that the phase-counting argument gives
   a finite verification procedure for specific instances. Could
   be a first concrete result before abstracting.

#### 5.13.5 Recommendation

Single-decree Paxos via bounded-unrolling is **research-grade
work**, estimated at 1000+ lines across a role-parameterized
framework and a Paxos instantiation. Before committing:

1. Implement subproblem (1) above (single-proposer Paxos) to
   validate that the phase-counting argument is mechanizable.
2. If that succeeds, extend to (2) (two-proposer Paxos) to test
   the ballot-ordering argument.
3. Only then consider the general abstract framework.

The OTR and majority-rule demonstrations in commits 1 and 3 of
PR #15 provide the foundation: they show the Config-level
bounded-unrolling machinery works and lifts via the bridge. The
next frontier — ballot-indexed protocols with per-phase counters
— is a separate research track that should build on this
foundation but not yet be conflated with it.

---

## 6. Relationship summary

| Cutoff kind           | Bounds                  | Class of protocols                | Where proved                              |
|-----------------------|-------------------------|-----------------------------------|--------------------------------------------|
| Node cutoff (§2)      | `n ≤ K_nodes`           | Symmetric threshold, role-symmetric | `Leslie/Cutoff.lean`                       |
| Combinator cutoff (§3)| Bounds derived structurally | Protocols built from SymCPhase      | `Combinators/CutoffIntegration.lean`       |
| Termination cutoff (§3.2) | `rounds ≤ T`, transfers across n | TV-deterministic round protocols    | `Combinators/TerminationCutoff.lean`       |
| Round cutoff (§4)     | `rounds ≤ n·D + W`      | Shift-invariant, window-local       | Design on hold (see Appendix D)            |
| Bounded-unrolling (§5)| `trace length ≤ D_safety` | Phase-structured deterministic protocols | **Planned** (OTR target)                 |

The five together form a planned verification suite: decompose a protocol
via combinators, derive a node cutoff from §2/§3, derive a termination
cutoff from §3.2 if applicable, and verify the resulting finite problem
via §5 stateless bounded-unrolling. Whether all can be made to compose
on a single nontrivial example is the medium-term target.

---

## 7. References

- Leslie/Cutoff.lean — node cutoff for SymThreshAlg
- Leslie/Examples/OneThirdRuleCutoff.lean — applied to 1/3 rule
- Leslie/Examples/Combinators/CutoffIntegration.lean — structural cutoff
  via combinators
- Leslie/Examples/Combinators/TerminationCutoff.lean — termination cutoff
  for TV-deterministic protocols
- Leslie/Examples/BenOr.lean — first planned instance of round cutoff
- docs/round-based-tutorial.md — Leslie's round-based modeling intro
- Konnov, Lazić, Veith: "Para² : Parametric Parallel model-checking with
  Threshold Automata" (structural inspiration for SymThreshAlg)
- Drăgoi, Henzinger, Veith: PSync (round-based symbolic execution; influenced
  the Tier-1 round-cutoff design)
- Abdulla et al.: "View Abstraction" (view-based parameterized cutoffs)

---

## Appendix A. BenOr round-cutoff feasibility study

This appendix records the first of three feasibility studies performed
while designing the round cutoff in §4. Study target: Ben-Or's binary
consensus (`Leslie/Examples/BenOr.lean`).

### A.1 BenOr's state in a nutshell

```lean
structure LState where
  val       : Fin 2
  witnessed : Option (Fin 2)     -- this-round witness, reset each round
  decided   : Option (Fin 2)     -- permanent decision

structure GState (n : Nat) where
  round  : Nat                    -- global round counter (lockstep model)
  phase  : Fin 2                  -- 0 = Report, 1 = Propose
  locals : Fin n → LState
```

Crucial observation: **BenOr is a lockstep model.** There is a single
global `round : Nat` at the top level of `GState`, not a per-process
round. All processes always agree on the current round number.

The individual `LState` fields are all round-*independent* data:
`val` is current value (overwritten each round), `witnessed` is computed
fresh in phase 1 (reset via `stepReport`), `decided` is a permanent
decision with no round tag.

**None of the local state fields carry an explicit round label.** The
only round-valued field in `GState` is `GState.round` itself. BenOr has
**no round-indexed history**.

### A.2 Instance sketches

With only `GState.round` as the round-valued field, all six instances
are trivial:

- **`RoundShift`:** `shift k s = { s with round := s.round + k }`
- **`RoundObserver`:** `maxRound = minRound = s.round` (lockstep)
- **`RoundWindow`:** `agreeAbove r s₁ s₂ := (r ≤ s₁.round → s₁.round = s₂.round) ∧ s₁.phase = s₂.phase ∧ s₁.locals = s₂.locals`
- **`BoundedAdvance`:** `D = 1` (stepReport keeps round, stepPropose does `+1`)
- **`RoundLocal`:** `W = 0` — no history, steps depend only on current locals
- **`RoundShiftInvariant`:** holds after reformulating init to drop `s.round = 0`
- **`RoundInvariant` for `lock_inv`:** trivially window-local and shift-invariant (the invariant mentions no round)

**Caveat:** BenOr uses `round : Nat`, so shifting by `-k` requires either
changing the model to `ℤ` or using a wrapper. Minor friction.

### A.3 Lessons from BenOr

1. **The conditions are internally consistent and mechanizable.** Each
   structure admits a clean BenOr instance. No circularity, no missing
   axioms. Positive sanity check on the design.
2. **`ℕ` vs `ℤ` for rounds is real friction.** Requires editing the
   existing model or adding a wrapper type.
3. **Init reformulation is unavoidable but localized.** Dropping
   `s.round = 0` from init is a semantic-preserving change every
   protocol must make.
4. **BenOr is a degenerate test case.** The theorem collapses on BenOr
   because BenOr has no round-indexed state. `W = 0` trivially.
   Verification delivers no new information beyond what existing
   induction-on-n gives.
5. **The truncation/compression step in the cutoff proof never fires
   on BenOr.** There is no history to truncate.

### A.4 Outcome

BenOr fails as a stress test of the round cutoff theorem. It validates
the design's internal consistency but does not exercise its substantive
proof obligations. Recommended (at the time): try One-Third Rule next.

---

## Appendix B. One-Third Rule round-cutoff feasibility study

Second feasibility study. Target: the One-Third Rule
(`Leslie/Examples/OneThirdRule.lean`). The goal was to find a protocol
where the round cutoff does nontrivial work after BenOr was found
degenerate.

**Headline finding:** OTR is equally degenerate, and for a deeper,
architectural reason.

### B.1 OTR's state

```lean
structure LState where
  val     : Nat
  decided : Option Nat

def otr_alg : RoundAlg (Fin n) LState Nat where
  init   := fun _p s => s.decided = none
  send   := fun _p s => s.val
  update := fun _p s msgs =>
    let received := (List.finRange n).filterMap msgs
    match findSuperMajority n received with
    | some v => { val := v, decided := some v }
    | none => s
```

And the global `RoundState` comes from `Leslie/Round.lean`:

```lean
structure RoundState (P : Type) (S : Type) where
  round  : Nat
  locals : P → S
```

### B.2 Instance sketches

Mechanically identical to BenOr's:
- `RoundShift`, `RoundObserver`, `RoundWindow`, etc. all trivially
  satisfied with `W = 0`.
- `lock_inv` doesn't mention round, so `RoundInvariant` holds trivially.
- Same `init` reformulation friction as BenOr.

### B.3 The architectural root cause

Writing out the type of `RoundAlg.update`:

```lean
update : P → S → (P → Option M) → S
```

The update function takes the process id, the current local state `S`,
and the messages delivered this round — and returns the next local
state.

**Crucially, `update` has no access to any round number, nor to any
history from previous rounds.** The local state type `S` is chosen by
the protocol, but the `RoundAlg` contract explicitly forbids peeking at
past rounds' state. The only persistent state across rounds is whatever
the protocol stores in `S`, and whatever is stored in `S` is
round-independent *by construction* — because `S` has no round labels.

The global `round : Nat` in `RoundState` is purely bookkeeping. It is
observed by the `CommPred` (to constrain HO collections round by round)
and incremented by `round_step`, but the algorithm never reads it.

**Corollary:** **every protocol built on Leslie's `RoundAlg` framework
is structurally round-history-free.** Its behavior at round `r` depends
only on the locals at round `r` and the HO collection for round `r`.

For such a protocol:
- `W = 0` is always sufficient — there is no past state to look back at.
- The round cutoff theorem applies trivially but delivers no information.
- The core proof step — compressing history via `agreeAbove` — never
  fires.

This applies to every `RoundAlg`-based protocol in Leslie: OTR, BenOr,
LastVoting (despite its name — the "last vote" is stored in `S`, not
round-indexed), FloodMin, LeaderBroadcast, BallotLeader, etc.

### B.4 Meta-observation: `RoundAlg` is already a kind of cutoff

Leslie's `RoundAlg` framework *already* achieves a form of round
compression by construction. Because `update` has no access to history,
every `RoundAlg`-based protocol is tautologically "Markov" — each
round's behavior depends only on the current state.

This is why node cutoffs (`Leslie/Cutoff.lean`) were the natural first
direction: `RoundAlg` already handles the round dimension by
*restricting expressivity*. A round cutoff would add value only for
protocols that step *outside* `RoundAlg`'s restrictions — i.e., those
that explicitly store round-indexed state in `S`.

### B.5 Outcome

OTR fails as a round-cutoff stress test for the same reason BenOr does,
and more fundamentally: the framework it's built on structurally
forbids round-indexed state. This redirected the feasibility effort
toward **ballot-indexed protocols** (Paxos family), which live outside
`RoundAlg`.

---

## Appendix C. Paxos round-cutoff feasibility study

Third and final feasibility study. Target: single-decree Paxos
(`Leslie/Examples/Paxos.lean`). This was the real test after the
architectural retargeting in Appendix B.

### C.1 Paxos state recap

```lean
structure PaxosState (n m : Nat) where
  prom   : Fin n → Nat                      -- highest ballot promised per acceptor
  acc    : Fin n → Option (Nat × Value)     -- accepted (ballot, value) per acceptor
  got1b  : Fin m → Fin n → Bool             -- proposer got 1b reply from acceptor
  rep    : Fin m → Fin n → Option (Nat × Value)  -- i's 1b-reply to p
  prop   : Fin m → Option Value             -- proposer's chosen value
  did2b  : Fin m → Fin n → Bool             -- acceptor accepted p's ballot
```

Ballots are `Nat`-valued, assigned to proposers via `ballot : Fin m → Nat`.

### C.2 Shift invariance: yes

**Claim:** adding constant `k` to every ballot value in the state *and*
to the `ballot` function preserves behavior.

**Why:** Paxos transitions reference ballots only through comparisons
(`<`, `≤`, `>`, `≥`), equality tests, and assignments. No arithmetic
(`+1`) is ever performed on ballot values — all ballot assignments are
*copies* (`prom := ballot p`, `rep := acc`, etc.). Adding a constant
preserves order and equality, hence all behavior.

**`init_closed`:** the initial state has `prom = 0`, `acc = none`, etc.
Shift maps this to `prom = k`, `acc = none`, etc. This is still an init-
like state. The init predicate must be relaxed from "prom = 0" to
"prom = some base value". Minor edit to `paxos.init`.

**Shift invariance holds.** ✓

### C.3 Consecutive-window locality: no

The `RoundLocal W` condition requires that transitions only depend on
state within `W` ballots of the current maximum. **This fails for Paxos.**

Consider a reachable state where:
- Proposer 1 has ballot 1 and has reached phase 2b majority: `prop 1 = some v₁`
- Proposer 2 has ballot 1000 and is doing phase 2a.

Proposer 2's phase 2a checks `rep 2 i` for every acceptor in its 1b-quorum.
An acceptor that has been promising since ballot 1 may have `rep 2 i =
some (1, v₁)` — a report from 999 ballots below. By the `hconstr`
condition, proposer 2 must pick the value of the highest-ballot report;
if ballot 1 is the only reported ballot, proposer 2 must use `v₁`.

**Proposer 2's transition depends on ballot values arbitrarily far
below its own.** No finite `W` suffices. `hSafe`'s `∀ c < b` quantifier
cannot be truncated to `[b - W, b - 1]`.

**Window locality fails.** ✗

### C.4 Bounded ballot support: a promising alternative

**Observation:** while the quantifier in `hSafe` ranges over unbounded
ballots, the *set of ballot values actually mentioned in the state* is
bounded. Define:

```
ballotsIn s :=
  {prom i | i}                              ∪   -- ≤ n
  {b | ∃ i v, acc i = some (b, v)}          ∪   -- ≤ n
  {b | ∃ q i v, rep q i = some (b, v)}      ∪   -- ≤ n·m
  {ballot p | p, prop p ≠ none ∨ ∃ i, did2b p i}  -- ≤ m
```

**Bound:** `|ballotsIn s| ≤ n·(m+2) + m`.

The number of distinct ballot values in any single state is bounded.
The state is "ballot-sparse" — it mentions a small number of ballots,
but those values may be far apart on the number line.

### C.5 The deeper observation that kills the attempt

When we trace *where ballot values come from*, a stronger fact emerges:
**Paxos never mints new ballot values at runtime.**

All ballot values in any reachable state are drawn from the fixed
`range ballot` of the initial ballot function. This range has exactly
`m` elements (one per proposer), and `m` is a fixed protocol parameter.

- `prom i` is initialized to `0`, and only ever updated to `ballot p`
  for some proposer `p`.
- `acc i` stores `(ballot p, v)` from some `p2b p i` step.
- `rep q i` is set to the current `acc i` by `p1b q i`, transitively
  from some proposer's ballot.
- The `ballot` function itself never changes.

**The total set of distinct ballot values appearing in any reachable
Paxos execution is bounded by `m`.** Not `n·(m+2) + m`, just `m`.

### C.6 Implication: single-decree Paxos has a finite round dimension

**Single-decree Paxos has at most `m` distinct ballot values across
its entire execution.** The "ballot dimension" of Paxos is already
finite at the model level, bounded by `m` — the number of proposers.

Since `m` is a fixed parameter already handled by any reasonable node
cutoff, **there is no unbounded round dimension in single-decree Paxos
to cut off**. The apparent unboundedness of ballots (the `Nat` type)
is a red herring; the real parameter is `m`, and `m` is already
bounded.

### C.7 Ballot renaming quotient (side observation, still useful)

Even though single-decree Paxos doesn't need a round cutoff, the
analysis surfaced a genuine symmetry: **Paxos is invariant under
strict-monotone ballot renaming.** Applying any order-preserving
injection `φ : ℕ → ℕ` to all ballot values and to the `ballot`
function preserves all behavior.

No transition performs ballot arithmetic, so renaming preserves all
transitions. This is a true symmetry that could support:

- **Symbolic ballot execution** — reason about ballot orderings
  abstractly, not about specific values
- **Test-case generation** — any test using ballots `{0, 5, 17}` is
  equivalent to one using `{0, 1, 2}`
- **Symmetry reductions for model checking**

The ballot renaming quotient is not a cutoff theorem, but it is a
valid and potentially useful structural observation. Worth revisiting
as a standalone tool.

### C.8 Outcome

The round cutoff as designed does not apply to single-decree Paxos,
but for a surprising reason: **Paxos's "round" dimension is already
finite at the model level**, bounded by the fixed parameter `m`. There
is no unbounded round dimension to compress.

Multi-decree variants (Multi-Paxos, Raft) have per-slot ballots and
do have an unbounded dimension (the slot index × ballot pair). A
cutoff targeting multi-decree protocols would be multi-dimensional and
requires a separate theorem — not the single-round cutoff in §4.

---

## Appendix D. Combined conclusion of the three feasibility studies

The three studies (BenOr, OTR, Paxos) yielded a uniform negative
result: **no protocol in Leslie's current corpus satisfies the round
cutoff theorem's non-triviality conditions.** The theorem is
internally consistent and its typeclass instances mechanize cleanly
(verified across all three studies), but it has no current user in
the repo.

The three failure modes are distinct and worth distinguishing:

| Protocol | Class | Why the theorem is vacuous/inapplicable |
|---|---|---|
| BenOr | `RoundAlg` | Global `round` counter only; no round-indexed local state |
| OTR | `RoundAlg` | Same as BenOr — the `RoundAlg` framework structurally forbids round history |
| Paxos | ballot-indexed | Ballot dimension is already finite at the model level (`m` proposers, no new ballots at runtime) |

**Useful findings that survive the negative result:**

1. **`RoundAlg` performs round compression by type.** Its restricted
   signature makes all HO-model protocols round-Markov by construction.
   This is a hidden virtue that explains why node cutoffs compose so
   well with `RoundAlg` protocols.
2. **Paxos's rounds are structurally finite.** Single-decree Paxos has
   exactly `m` ballots across any execution. The apparent unboundedness
   of `Nat`-valued ballots is a concurrency concern the model abstracts
   away via `Fin m`.
3. **Ballot renaming is a valid symmetry.** Paxos's invariance under
   strict-monotone ballot renumbering could support other tools
   (symbolic execution, symmetry reductions) even without a cutoff
   theorem.
4. **The round dimension / ballot structure distinction matters.**
   HO-model round protocols (lockstep, advancing) and ballot-indexed
   consensus (sparse, arbitrary-spaced) are fundamentally different
   and need different cutoff frameworks.

**Decision** (as of this writing): the round cutoff theorem's design
is preserved in §4 as reference, but the theorem is not being
formalized. Revisit if Leslie gains a multi-decree protocol
(Multi-Paxos, Raft) where a meaningful unbounded round dimension
exists.
