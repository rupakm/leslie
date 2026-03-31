# TileLink TL-C Implementation Plan

This plan turns the earlier protocol summary into a concrete development path
for Leslie. It is written to keep files short, proof obligations local, and
later extensions compatible with earlier work.

## Guiding constraints

- Model one cache line first.
- Separate protocol layers:
  atomic transfer semantics, explicit message semantics, parameterized scaling.
- Keep each proof file centered on one action family or one invariant cluster.
- Prefer refinement between models over proving everything directly in the most
  detailed state space.
- Use environment abstraction only after the small-system message model is
  stable.

## Concrete target structure

```text
Leslie/Examples/CacheCoherence/TileLink/
  README.md
  IMPLEMENTATION_PLAN.md
  Types.lean
  Permissions.lean
  Common.lean
  Atomic/
    Model.lean
    Invariant.lean
    StepProof.lean
    Theorem.lean
    Refinement.lean
  Messages/
    Model.lean
    FrameLemmas.lean
    InvariantCore.lean
    InvariantChannels.lean
    InvariantSerialization.lean
    InitProof.lean
    StepAcquire.lean
    StepProbe.lean
    StepRelease.lean
    StepAccess.lean
    Theorem.lean
  Parameterized/
    Model.lean
    FocusModel.lean
    EnvSummary.lean
    EnvProof.lean
    Safety.lean
    Refinement.lean
```

## Core modeling choices

### State space

Use a single-line state space with:

- a managing slave / home node
- `n` symmetric masters
- per-master permission/data state
- explicit in-flight protocol obligations

The key split is:

- shared state:
  manager directory, backing value, global transaction metadata
- local state:
  cache-line permission/data and per-link message endpoints for one master

### Permission abstraction

Use TileLink's coherence permissions, not MESI names, in the concrete model:

- `N`: no cached copy
- `B`: branch, read-only copy
- `T_dirty`: tip with writable/dirty authority
- `T_clean`: tip with writable authority but clean data
- optionally `TrunkOnly` later if an intermediate inclusive cache is modeled

For the first pass with one manager and leaf masters, `TrunkOnly` can stay out
of the master-local state and live only in comments or future extensions. The
important concrete distinction is between:

- no copy
- read-only copy
- sole writer / serialization owner

That lets us prove coherence with a compact local state while still keeping the
message labels and proof statements TileLink-shaped.

### Message scope for the first pass

Include only the TL-C transfer messages needed for invalidation-based
coherence:

- A: `AcquireBlock`, `AcquirePerm`
- B: `ProbeBlock`, `ProbePerm`
- C: `ProbeAck`, `ProbeAckData`, `Release`, `ReleaseData`
- D: `Grant`, `GrantData`, `ReleaseAck`
- E: `GrantAck`

Defer:

- forwarded TL-UH/TL-UL access traffic on B/C
- multibeat bursts
- `denied`
- `corrupt`
- hierarchical caches above the manager

## Stage plan

## Stage 0: Shared vocabulary and helper lemmas

### Deliverables

- `Types.lean`
- `Permissions.lean`
- `Common.lean`

### Content

- enums for:
  `TLPerm`, `GrowParam`, `CapParam`, `PruneReportParam`
- message opcodes grouped by channel
- transaction-key record for `(address, source, sink)` style tracking
- helper predicates translating TileLink parameters into permission updates

### Proof goals

- small algebraic lemmas:
  grow/cap/prune legality, read/write permission predicates, dirty-owner facts
- no protocol theorem yet

### Purpose

This isolates spec vocabulary from the first executable model. It also avoids
repeating permission-case analysis across later files.

## Stage 1: Atomic transfer model

### Objective

Build the simplest TL-C-flavored model that still reflects:

- permission growth by `Acquire*`
- forced downgrades by `Probe*`
- voluntary downgrades by `Release*`
- serialization completion by `GrantAck` and `ReleaseAck`

### Current status

The checked-in files under `Atomic/` currently implement an early Stage 1b
checkpoint:

- `AcquirePerm` grants write authority without valid data
- `Release` and `ReleaseData` are already split and carry abstract
  prune/report parameters
- local state distinguishes permission, validity, dirtiness, and data
- shared state includes home memory, a directory summary, pending grant
  metadata, and pending `GrantAck`/`ReleaseAck` obligations
- the proved invariant currently covers writer exclusivity, pending-ack
  discipline, directory agreement, local well-formedness, and clean valid data
  agreement with memory
- a derived theorem identifies the dirty owner as the source of the atomic
  model's logical line value

The remaining Stage 1 work is to strengthen the shared state and the proof to
cover:

- explicit outstanding probe obligations / pending serialized transfer metadata
- sequential one-line refinement

### Files

- `Atomic/Model.lean`
- `Atomic/Invariant.lean`
- `Atomic/StepProof.lean`
- `Atomic/Theorem.lean`
- `Atomic/Refinement.lean`

### Modeling style

Use `SymSharedSpec`, mirroring `GermanSimple` and `MESIParam`.

Shared state should contain:

- `mem : Val`
- directory summary over masters
- optional pending transaction
- probe obligations outstanding for the current transaction
- whether a post-grant `GrantAck` is still required
- whether a post-release `ReleaseAck` is still required

Local state should contain:

- local permission/data
- optional abstract mailbox markers only if needed

Keep the first version largely atomic:

- one step can represent "manager processes acquire and schedules probes"
- one step can represent "all required probe responses consumed"
- one step can represent "grant delivered and locally consumed"

The current Stage 1b checkpoint intentionally implements only:

- `mem`
- directory summary
- pending grant metadata
- pending `GrantAck`
- pending `ReleaseAck`

That is enough to validate the TL-C permission shape, prove a first memory
agreement invariant, and keep the next extensions focused on serialized
transfer metadata rather than basic permission bookkeeping.

### Proof goals

Prove an inductive invariant combining:

- unique writer / tip owner
- readers exclude dirty ownership
- directory agrees with local permissions
- if a line is clean in a master, its value agrees with memory
- if a line is dirty in one master, all others are non-writers and the logical
  line value equals that master's data
- a pending `GrantAck` blocks conflicting new serialization points
- a pending `ReleaseAck` blocks re-use of the same line by the releasing master

Then prove refinement to a sequential one-line memory abstraction, in the same
style as `MESIParam`.

The current checked-in proof stops short of this point. It proves the
structural safety core first, and Stage 1b should add the data and refinement
theorems above without collapsing the file structure.

### Success criterion

An end-to-end theorem for the atomic model:

- coherence safety
- data coherence
- simple sequential-line refinement

## Stage 2: Explicit message-level model

### Objective

Replace atomic waves with explicit channels and in-flight messages, following
the organization pattern of `GermanMessages/`.

### Files

- `Messages/Model.lean`
- `Messages/FrameLemmas.lean`
- `Messages/InvariantCore.lean`
- `Messages/InvariantChannels.lean`
- `Messages/InvariantSerialization.lean`
- `Messages/InitProof.lean`
- `Messages/StepAcquire.lean`
- `Messages/StepProbe.lean`
- `Messages/StepRelease.lean`
- `Messages/StepAccess.lean`
- `Messages/Theorem.lean`

### State design

Shared state:

- manager memory value
- directory / sharer metadata
- current serialized operation state
- outstanding probe targets and probe-ack counter
- map or option structure for live `d_sink` obligations

Local state per master:

- permission/data
- channel endpoint state for A/B/C/D/E
- local transaction bookkeeping:
  request source tags, remembered `d_sink`, release-in-flight marker

### Action families

- `sendAcquire*`
- `recvAcquireAtManager`
- `sendProbe*`
- `recvProbeAtMaster`
- `sendProbeAck*`
- `recvProbeAckAtManager`
- `sendGrant*`
- `recvGrantAtMaster`
- `sendGrantAck`
- `recvGrantAckAtManager`
- `sendRelease*`
- `recvReleaseAtManager`
- `sendReleaseAck`
- `recvReleaseAckAtMaster`

### Invariant split

#### Core safety

- permission exclusivity
- data coherence
- directory/local consistency

#### Channel well-formedness

- each non-empty channel carries a legal opcode/parameter pair
- IDs copied across request/response pairs correctly
- message payload legality:
  `ProbeAckData` and `ReleaseData` only when dirty data is permitted

#### Serialization

- pending `GrantAck` prevents conflicting new grants/probes
- pending `ReleaseAck` prevents conflicting new local actions by releaser
- manager only grants after required probes are fully collected
- if a grant is in flight, the manager's chosen post-state is stable

#### Manager bookkeeping

- outstanding probe target set matches actual expected responses
- directory updates happen in the right phase
- the unique dirty owner, if any, is reflected either in a master local state
  or in a returning data message

### Proof method

Use the `GermanMessages` style directly:

- public safety predicates in one file
- stronger internal invariants in separate files
- frame lemmas for actions with small write footprints
- one preservation file per action family
- final theorem as reachable-state induction

### Success criterion

A fully explicit single-line TL-C message model proving the same safety theorem
as Stage 1.

## Stage 3: Refinement from messages to atomic waves

### Objective

Show the explicit message model refines the atomic model instead of reproving
all high-level properties from scratch.

### Files

- `Messages/Theorem.lean`
- `Atomic/Refinement.lean`

### Mapping idea

Map an explicit channel state to:

- effective manager transaction phase
- effective per-master permission/data state
- abstract pending obligations such as "probe outstanding" or
  "grant awaiting ack"

### Proof goals

- explicit model refines atomic model with stuttering
- atomic model refines sequential line abstraction
- therefore explicit model inherits sequential coherence theorem

### Benefit

This keeps later extensions focused on preserving the refinement mapping rather
than duplicating every high-level proof.

## Stage 4: Parameterized many-master model

### Objective

Lift the explicit or semi-atomic model to arbitrary `n` using symmetry.

### Files

- `Parameterized/Model.lean`
- `Parameterized/Safety.lean`

### Approach

Use `SymSharedSpec` with:

- shared manager state
- `Fin n -> LocalState`
- action type indexed by a master and protocol operation

Reuse the same invariant vocabulary, but state it pointwise over all
`i : Fin n`.

### Proof goals

- symmetry theorem
- focus-to-all lifting for local obligations
- direct proof of core coherence for arbitrary `n`

### Expected difficulty

Direct global proofs are still reasonable for coarse safety, but the full
message model will likely become too large here. That is when environment
abstraction should be introduced.

## Stage 5: Focus/environment abstraction

### Objective

Summarize the `n-1` non-focus masters into a compact environment state so that
most reasoning happens in a 1+env model.

### Files

- `Parameterized/FocusModel.lean`
- `Parameterized/EnvSummary.lean`
- `Parameterized/EnvProof.lean`

### Proposed environment summary

Track only the facts the focus proofs actually need:

- whether some other master has `B`
- whether some other master has writable / dirty authority
- whether some other master is currently the target of a probe
- whether dirty data from the environment is in flight
- whether a manager-side `GrantAck` or `ReleaseAck` dependency exists
- whether the environment contributes any outstanding response needed before a
  grant may issue

Do not try to encode the exact set of all other masters unless a proof forces
it.

### Proof style

Use `EnvAbsInvProof` from `Leslie/EnvAbstraction.lean`, because abstraction
soundness will almost certainly depend on previously proved concrete safety
facts.

### Proof goals

- define abstraction map from many masters to focus + environment summary
- prove focus-step and environment-step soundness under the concrete invariant
- lift focus safety to all masters using symmetry

## Stage 6: Access-path extension

### Objective

Add ordinary reads/writes/atomics once the transfer protocol is stable.

### Scope

Initially only model:

- local cache hits
- misses that force an `Acquire*`
- writes that use `AcquirePerm` when data need not be fetched

Defer forwarded B/C access traffic again if possible. The first access theorem
should sit on top of the already-proved transfer machinery.

### Proof goals

- reads return the logical line value
- writes update the logical line value
- local access preconditions match current permissions

## Stage 7: Optional forwarded-access extension

### Objective

Support Section 9.5 style use of B/C for forwarded TL-UH/TL-UL accesses.

### Why optional

This is a different policy dimension. The invalidation-based transfer proof is
already substantial and should stand on its own. Add this only after the base
development is complete.

### Expected impact

- more message types on B/C
- more response matching invariants
- stronger serialization statements around forwarded dirty data

## Stage 8: Liveness and deadlock-related progress

### Objective

After safety is stable, add fairness assumptions for local progress.

### Suggested first liveness target

- if an acquire request remains enabled and required responses eventually
  arrive, then the requester eventually receives a `Grant` or `GrantData`

### Do not attempt first

- full mechanization of the spec's global deadlock-freedom proof over channel
  priorities and agent graphs

That is a separate project and should only begin after the local transfer
protocol is executable and proved safe.

## Simplified models and what they buy us

### Simplification A: one line only

Removes address-space interference. Coherence is per-line, so this is the right
safety abstraction.

### Simplification B: one manager and leaf masters only

Avoids intermediate inclusive caches and trunk-only states in the first model.

### Simplification C: single-beat transfers

Avoids burst bookkeeping while preserving transfer serialization structure.

### Simplification D: no denied/corrupt

Lets the first proof focus on coherence, not fault handling.

### Simplification E: invalidation-based policy only

Defers forwarded-access variants and update-style policies.

## Main proof obligations by layer

## Atomic layer

- unique writable owner
- readers consistent with manager memory or unique dirty owner
- manager chooses legal permission transitions
- pending transfer metadata is consistent

## Message layer

- every in-flight message is legal for its channel
- request/response fields match correctly
- manager waits for the right acknowledgments
- masters obey same-block local blocking conditions
- data in `GrantData`, `ProbeAckData`, and `ReleaseData` reflects the logical
  line value

## Parameterized layer

- symmetry
- focus theorem
- abstraction soundness

## Refinement layer

- message model to atomic wave model
- atomic wave model to sequential line abstraction

## Recommended work sequence

1. Implement `Types.lean` and `Permissions.lean`.
2. Build `Atomic/Model.lean`.
3. Prove the first atomic safety theorem.
4. Add message-level `Model.lean` and frame lemmas.
5. Prove channel/core invariants for message level.
6. Prove message-to-atomic refinement.
7. Generalize to arbitrary `n`.
8. Add environment abstraction if direct parameterized message proofs become
   unwieldy.
9. Add accesses.
10. Add optional forwarded-access and liveness extensions.

## Minimal first milestone

The first milestone worth merging is:

- shared TileLink permission vocabulary
- atomic TL-C transfer model for one line
- theorem: coherence safety + data coherence
- refinement to a sequential line abstraction

This milestone is small enough to finish and strong enough to validate the
overall approach.

## Second milestone

- explicit A/B/C/D/E message model for one line
- layered invariants
- preservation proofs split by action family
- refinement to the atomic model

## Third milestone

- arbitrary `n` masters
- symmetry theorem
- environment abstraction and focus proof
- lifted parameterized safety theorem

## Review checklist for each stage

- Is the state carrying protocol facts or implementation noise?
- Are invariants split by footprint and responsibility?
- Can the next stage reuse this stage by refinement instead of reproving it?
- Are files still short enough to edit and load without blowing up context?
- Is every new protocol field justified by a theorem, not just by realism?
