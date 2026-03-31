# TileLink TL-C in Leslie

This directory is the planned home for a Leslie model and proof development for
the TileLink cached protocol (TL-C), with emphasis on coherent cache-block
transfers for a single cache line.

## Goal

Build a staged, modular verification effort for TileLink coherence that:

- starts from small, atomic models that are easy to prove
- refines toward explicit message-level models with A/B/C/D/E channels
- keeps invariants split across small files instead of one monolithic proof
- scales to symmetric many-master systems using Leslie's shared-memory
  symmetry and environment-abstraction machinery

## Why this needs its own structure

TileLink TL-C is more than a MESI state machine. The concrete protocol also
tracks:

- explicit transfer messages (`Acquire*`, `Probe*`, `Grant*`, `Release*`)
- transaction identifiers (`source`, `sink`)
- same-block serialization obligations (`GrantAck`, `ReleaseAck`)
- in-flight protocol waves that may overlap without point-to-point ordering

Because of that, the development should not jump directly to a fully explicit
model. The intended approach is:

1. prove an atomic transfer-level model first
2. refine it to an explicit message-level model
3. lift per-process proofs to parameterized systems

## Planned contents

- `README.md`
  This overview and directory roadmap.
- `IMPLEMENTATION_PLAN.md`
  Detailed staged implementation and proof plan.
- `Types.lean`
  Shared enums and basic records.
- `Permissions.lean`
  Permission lattice and transition classification.
- `Atomic/`
  Small wave-level models and safety proofs.
- `Messages/`
  Explicit channel-level models and invariants.
- `Refinement/`
  Refinement mappings between atomic and message-level models.
- `Parameterized/`
  Symmetric shared-memory model, environment abstraction, and scaling proofs.

## Intended first proof scope

The first end-to-end theorem should target:

- one cache line
- one managing slave
- many symmetric masters
- invalidation-based coherence only
- single-beat transfers
- no `denied` or `corrupt`
- safety only

That first scope should prove:

- permission exclusivity / SWMR-style coherence
- data coherence for clean and dirty ownership
- same-block serialization obligations for the simplified transfer set
- refinement to a simple sequential line abstraction

## Existing Leslie patterns to copy

- `GermanSimple.lean`
  Atomic controller-level coherence model.
- `GermanMessages/`
  Explicit message-level model with layered invariants and split proof files.
- `MESIParam.lean`
  Symmetric parameterized cache-coherence development using `SymSharedSpec`.
- `EnvAbstraction.lean`
  Focus/environment abstraction for scaling local proofs to arbitrary `n`.

## Immediate next step

Implement Stage 0 and Stage 1 from `IMPLEMENTATION_PLAN.md`: define the shared
types and the first atomic TL-C transfer model for one line.
