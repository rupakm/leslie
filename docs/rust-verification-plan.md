# Implementation Plan: Verifying Rust Round-Based Protocols

This document breaks the design in `rust-verification.md` into
concrete implementation steps with dependencies, deliverables, and
estimated scope.

## Prerequisites

- Leslie project with round-based framework and proved examples
  (OneThirdRule, BallotLeader, etc.) — **done**
- Rust `Communication`/`InboxExt` API — **done** (provided by user)
- Verus installation for Rust verification annotations

## Phase 1: Typestate API for Phase Discipline

**Goal**: Make phase violations a compile error. No verification
tooling needed — pure Rust type system.

### Step 1.1: Define the typestate round API

Create `rust-lib/src/typestate.rs`:

```rust
pub struct Ready;
pub struct Sent;
pub struct Received;

pub struct RoundCtx<P, R, T, Phase> { ... }
```

Transitions:
- `RoundCtx<..., Ready>` → `.send(msg)` → `RoundCtx<..., Sent>`
- `RoundCtx<..., Sent>` → `.inbox(pred, done)` → `(RoundCtx<..., Received>, BTreeMap<P, M>)`
- `RoundCtx<..., Received>` → `.tick()` → `RoundCtx<..., Ready>`

**Deliverable**: A Rust crate `leslie-rounds` wrapping the
`Communication`/`InboxExt` API with typestate enforcement.

**Dependency**: None.

### Step 1.2: Multi-phase typestate variant

For protocols with k phases per round (Paxos: 4, VR: 2):

```rust
pub struct PhaseCtx<P, R, T, const PHASE: usize> { ... }
```

Transitions advance `PHASE` from 0 to k-1, then tick to next round.

**Deliverable**: Extension of `leslie-rounds` for multi-phase protocols.

**Dependency**: Step 1.1.

### Step 1.3: Port OneThirdRule to typestate API

Implement OneThirdRule using `RoundCtx`, verifying that the typestate
prevents phase violations at compile time.

```rust
fn otr_round(ctx: RoundCtx<PeerId, Nat, T, Ready>, state: &OTRState)
    -> (RoundCtx<PeerId, Nat, T, Ready>, OTRState)
{
    let ctx = ctx.send(NatMsg(state.val))?;
    let (ctx, inbox) = ctx.inbox(same_round, quorum_done)?;
    let new_state = otr_update(state, &inbox);
    let ctx = ctx.tick();
    (ctx, new_state)
}
```

**Deliverable**: `rust-examples/otr/src/main.rs`.

**Dependency**: Step 1.1.

## Phase 2: Ghost State and Encoding Functions

**Goal**: Define the correspondence between Rust state and Leslie
state as ghost functions (erased at runtime, checked at verify time).

### Step 2.1: Define the RoundProtocol trait

Create `rust-lib/src/protocol.rs`:

```rust
pub trait RoundProtocol {
    type State: Clone;
    type Msg: Clone;
    type Oracle;

    /// The message to send, given current state.
    fn send(state: &Self::State) -> Self::Msg;

    /// The new state, given current state, inbox, and oracle.
    fn update(
        state: &Self::State,
        inbox: &BTreeMap<PeerId, Self::Msg>,
        oracle: Self::Oracle,
    ) -> Self::State;

    /// All possible oracle values (for nondeterministic protocols).
    fn oracle_values() -> Vec<Self::Oracle>;
}
```

**Deliverable**: Trait definition in `leslie-rounds`.

**Dependency**: None (can be done in parallel with Phase 1).

### Step 2.2: Define ghost encoding for OneThirdRule

```rust
mod ghost {
    /// Maps Rust OTRState to Leslie LState.
    /// Erased at runtime; used only in Verus annotations.
    pub fn encode(s: &OTRState) -> LeslieLState {
        LeslieLState { val: s.val, decided: s.decided }
    }

    /// Maps Rust BTreeMap inbox to Leslie (Peer → Option Msg).
    pub fn encode_inbox(inbox: &BTreeMap<PeerId, u64>) -> LeslieInbox {
        LeslieInbox(move |p| inbox.get(&p).copied())
    }
}
```

**Deliverable**: Ghost module in `rust-examples/otr/src/ghost.rs`.

**Dependency**: Step 2.1.

### Step 2.3: Define ghost encoding for Ben-Or

Same structure as 2.2, but with `Oracle = bool` (coin flip):

```rust
impl RoundProtocol for BenOr {
    type Oracle = bool;
    fn oracle_values() -> Vec<bool> { vec![false, true] }
    fn update(state: &State, inbox: &Inbox, coin: bool) -> State { ... }
}
```

**Deliverable**: Ghost module in `rust-examples/benor/src/ghost.rs`.

**Dependency**: Step 2.1.

## Phase 3: Verus Annotations

**Goal**: Express the verification conditions as Verus pre/post
conditions on the Rust protocol functions.

### Step 3.1: Annotate OneThirdRule send

```rust
#[ensures(encode_msg(&result) == leslie::otr_send(encode(state)))]
fn send(state: &OTRState) -> u64 {
    state.val
}
```

**Verification condition**: The message equals the encoded state's val.
Trivial for OTR (send = identity on val).

**Deliverable**: Annotated `send` in OTR example.

**Dependency**: Step 2.2.

### Step 3.2: Annotate OneThirdRule update

```rust
#[ensures(encode(&result) == leslie::otr_update(encode(state), encode_inbox(inbox)))]
fn update(state: &OTRState, inbox: &BTreeMap<PeerId, u64>) -> OTRState {
    let counts = count_values(inbox);
    if let Some(v) = find_super_majority(&counts, N) {
        OTRState { val: v, decided: Some(v) }
    } else {
        state.clone()
    }
}
```

**Verification condition**: The Rust `find_super_majority` matches
Leslie's `findSuperMajority`. This requires showing the counting
logic is equivalent.

**Deliverable**: Annotated `update` in OTR example.

**Dependency**: Step 2.2.

### Step 3.3: Annotate Ben-Or update with oracle enumeration

```rust
#[ensures(forall(|coin: bool|
    exists(|leslie_oracle: LeslieOracle|
        encode(&Self::update(state, inbox, coin))
        == leslie::benor_update(encode(state), encode_inbox(inbox), leslie_oracle)
    ))
)]
```

**Verification condition**: For each coin value (true/false), the
Rust update corresponds to some valid Leslie transition.

**Deliverable**: Annotated `update` in Ben-Or example.

**Dependency**: Step 2.3.

### Step 3.4: Annotate communication closure

```rust
#[requires(forall(|local: &R, remote: &R|
    round_pred(local, remote) ==> *local == *remote
))]
fn inbox<RP, DONE>(&mut self, round_pred: RP, done: DONE) -> Result<...>
```

**Verification condition**: The inbox predicate only accepts
same-round messages.

**Deliverable**: Annotated `inbox` in `leslie-rounds` crate.

**Dependency**: Step 1.1.

## Phase 4: Leslie Correspondence Theorem

**Goal**: Prove in Lean that if the Verus VCs hold, the Rust system
inherits the Leslie safety proof.

### Step 4.1: Define RustCorrespondence.lean

```lean
structure RustCorrespondence (RS LS M : Type) where
  encode : RS → LS
  encode_msg : RustMsg → M
  encode_inbox : (PeerId → Option RustMsg) → (PeerId → Option M)
```

**Deliverable**: `Leslie/RustCorrespondence.lean`.

**Dependency**: None (can be done in parallel with Phases 1-3).

### Step 4.2: State the correspondence conditions

```lean
structure CorrespondenceProof (rc : RustCorrespondence RS LS M)
    (alg : RoundAlg P LS M) where
  init_corr : ∀ rs, rust_init rs → alg.init (rc.encode rs)
  send_corr : ∀ rs, rc.encode_msg (rust_send rs) = alg.send (rc.encode rs)
  update_corr : ∀ rs inbox oracle,
    rc.encode (rust_update rs inbox oracle) =
    alg.update (rc.encode rs) (rc.encode_inbox inbox)
```

**Deliverable**: Conditions in `RustCorrespondence.lean`.

**Dependency**: Step 4.1.

### Step 4.3: Prove the transfer theorem

```lean
theorem rust_inherits_safety
    (rc : RustCorrespondence RS LS M)
    (alg : RoundAlg P LS M)
    (proof : CorrespondenceProof rc alg)
    (leslie_safety : pred_implies (RoundSpec.toSpec ...).safety [tlafml| □ ⌜inv⌝])
    : -- The Rust system satisfies inv ∘ encode
    ...
```

This is the key metatheorem: Verus VCs + Leslie proof → Rust safety.

**Deliverable**: Proved theorem in `RustCorrespondence.lean`.

**Dependency**: Steps 4.1, 4.2.

## Phase 5: Concurrent Test Harness

**Goal**: A systematic test that explores the state space of N
processes running the Rust protocol, checking the Leslie invariant.

### Step 5.1: Simulated transport

```rust
struct SimulatedTransport {
    // For each (sender, receiver, round): Option<Msg>
    // Nondeterministic: can drop any subset of messages
    buffers: HashMap<(PeerId, PeerId, Round), Option<Msg>>,
}
```

The transport enumerates delivery subsets (all 2^(N²) HO collections
per round, or a sampled subset for large N).

**Deliverable**: `rust-lib/src/simulated_transport.rs`.

**Dependency**: None.

### Step 5.2: State-space explorer

```rust
fn explore<P: RoundProtocol>(
    n_processes: usize,
    n_rounds: usize,
    invariant: impl Fn(&[P::State]) -> bool,
) -> Result<(), Counterexample>
```

For each round:
1. Each process sends (deterministic, from state).
2. Enumerate HO collections (which messages delivered).
3. For each HO: each process collects inbox, enumerates oracle
   values, updates state.
4. Check invariant on the global state.

With cutoff: only explore N ≤ K (from Leslie cutoff theorem).

**Deliverable**: `rust-lib/src/explorer.rs`.

**Dependency**: Steps 2.1, 5.1.

### Step 5.3: OneThirdRule exploration

Instantiate the explorer for OneThirdRule with N=3 processes,
binary values, and the agreement invariant.

Expected: no counterexample found for N ≤ 7.

**Deliverable**: `rust-examples/otr/tests/explore.rs`.

**Dependency**: Steps 1.3, 5.2.

### Step 5.4: Ben-Or exploration

Instantiate for Ben-Or with N=3, reliable communication (all
messages delivered), and agreement invariant. Also test with
unreliable communication to find the known counterexample.

**Deliverable**: `rust-examples/benor/tests/explore.rs`.

**Dependency**: Steps 2.3, 5.2.

## Phase 6: End-to-End Case Study

**Goal**: Complete pipeline from Leslie proof to verified Rust code
for OneThirdRule.

### Step 6.1: Assemble the full OTR pipeline

1. Leslie proof: `OneThirdRule.lean` (agreement + validity) — **done**
2. Rust implementation: `rust-examples/otr/` with typestate API
3. Ghost encoding: `encode`, `encode_inbox`
4. Verus VCs: `send_corr`, `update_corr`, `closure`
5. Leslie metatheorem: `rust_inherits_safety` instantiated for OTR
6. Concurrent test: explorer with N ≤ 7, agreement invariant

**Deliverable**: End-to-end demo in `rust-examples/otr/`.

**Dependency**: All of Phase 1-5.

### Step 6.2: Write up the case study

Document the complete pipeline: what was proved where, what was
checked how, what the trust assumptions are.

**Deliverable**: `docs/otr-case-study.md`.

**Dependency**: Step 6.1.

## Dependency Graph

```
Phase 1 (Typestate)          Phase 2 (Ghost)           Phase 4 (Leslie)
  1.1 ─── 1.2                 2.1                       4.1
   │       │                  / \                         │
   │       │               2.2   2.3                     4.2
   │       │                │     │                       │
  1.3      │                │     │                      4.3
   │       │                │     │                       │
   ├───────┴────────────────┴─────┘                       │
   │                                                      │
Phase 3 (Verus)             Phase 5 (Testing)             │
  3.1, 3.2, 3.3, 3.4         5.1                         │
   │                           │                          │
   │                          5.2                         │
   │                         / \                          │
   │                       5.3   5.4                      │
   │                        │                             │
   └────────────────────────┴─────────────────────────────┘
                            │
                        Phase 6 (E2E)
                          6.1
                           │
                          6.2
```

## Parallelism

The following can proceed in parallel:

- **Phase 1** (typestate API) and **Phase 4** (Leslie metatheorem):
  no dependencies between them.

- **Phase 2** (ghost encoding) and **Phase 5.1** (simulated transport):
  independent.

- **Steps 3.1-3.3** (Verus annotations for different protocols):
  independent of each other.

- **Steps 5.3 and 5.4** (OTR and Ben-Or exploration): independent.

## Estimated Scope

| Phase | Steps | New code | Difficulty |
|-------|-------|----------|------------|
| 1. Typestate | 3 | ~300 lines Rust | Low |
| 2. Ghost | 3 | ~200 lines Rust | Low |
| 3. Verus | 4 | ~200 lines annotations | Medium |
| 4. Leslie | 3 | ~200 lines Lean | Medium |
| 5. Testing | 4 | ~500 lines Rust | Medium |
| 6. E2E | 2 | ~100 lines + docs | Low |
| **Total** | **19** | **~1500 lines** | |

## Open Questions

1. **Verus discharge**: How do we actually verify the Verus annotations?
   Options: Verus solver (SMT-based), manual proof, testing against
   the Leslie model. The annotations are the specification; the
   discharge method is orthogonal.

2. **Inbox completeness**: The `done` predicate in `inbox` controls
   when to stop collecting messages. If `done` returns true too early
   (before a quorum is reached), the protocol might not make progress.
   This is a liveness concern, not safety — but it affects testing.

3. **Transport model fidelity**: The simulated transport must faithfully
   model the real transport's nondeterminism. For model checking, we
   enumerate all delivery subsets. For testing, we sample. The gap
   between the simulated and real transport is a trust assumption.

4. **Multi-phase round_pred**: For Paxos-style protocols, the
   communication closure predicate is more complex (same ballot AND
   same phase). The dataflow check for `round_pred` needs to handle
   these structured rounds.

5. **State-space explosion**: For N processes and R rounds, the
   explorer enumerates 2^(N²) HO collections per round. With the
   cutoff (N ≤ 7 for OTR), this is ~2^49 per round — too large for
   exhaustive search. Optimizations: symmetry reduction (permuting
   processes), threshold-view pruning (only distinct threshold views
   matter), random sampling.
