# Lentil: TLA in Lean 4

> TLA+ is considered to be exhaustively-testable pseudocode, and its use likened
> to drawing blueprints for software systems; _TLA_ is an acronym for Temporal
> Logic of Actions.
>
> (from [TLA+ - Wikipedia](https://en.wikipedia.org/wiki/TLA%2B))

Lentil is a shallow embedding of the Temporal Logic of Actions (TLA) in Lean 4,
ported from the [`coq-tla`](https://github.com/tchajed/coq-tla) library. It
provides a framework for specifying and verifying concurrent and distributed
systems with machine-checked proofs.

The library includes refinement mappings (Abadi-Lamport), structured
multi-action specifications, CIVL-style layered refinement with mover types,
and the core Lipton reduction theorem.

## Building

Requires [elan](https://github.com/leanprover/elan) with Lean 4 v4.27.0.

```
lake build
```

## Usage

Add this project into your `lakefile.lean` and then:

```lean
import Lentil
```

See [MANUAL.md](MANUAL.md) for a complete user guide covering how to write
specifications, prove invariants, and establish refinement.

## Project Structure

```
Lentil/
├── Basic.lean              Core TLA definitions, syntax, and operators
├── Refinement.lean         Spec structure and refinement mapping theorems
├── Action.lean             GatedAction, ActionSpec (multi-action specs)
├── Layers.lean             CIVL-style layers, mover types, Lipton reduction
├── Rules/
│   ├── Basic.lean          Core TLA rules (always, eventually, until, etc.)
│   ├── StatePred.lean      State predicate rules, init_invariant
│   ├── LeadsTo.lean        Leads-to reasoning (transitivity, consequence)
│   ├── BigOp.lean          Big conjunction/disjunction operators
│   └── WF.lean             Weak fairness (WF1 rule)
├── Tactics/
│   ├── Basic.lean          tla_unfold, tla_merge_always, etc.
│   ├── Modality.lean       Modal operator tactics
│   ├── Structural.lean     tla_intros
│   └── StateFinite.lean    simp_finite_exec_goal
├── Gadgets/
│   ├── TheoremLifting.lean #tla_lift command
│   └── TheoremDeriving.lean @[tla_derive] attribute
└── Examples/
    ├── CounterRefinement.lean   Simple refinement example
    ├── TwoPhaseCommit.lean      2PC with refinement proof
    ├── TicketLock.lean          Layered refinement + mover proofs
    └── Paxos.lean               Single-decree Paxos
```

## Examples at a Glance

| Example | What it demonstrates | Lines | Status |
|---------|---------------------|-------|--------|
| CounterRefinement | Basic refinement with stuttering | ~100 | Complete |
| TwoPhaseCommit | Refinement with invariant (10 actions) | ~280 | Complete, no sorry |
| TicketLock | Layered refinement, mover types | ~395 | Complete, no sorry |
| Paxos | Quorum intersection, 14 actions | ~340 | Spec complete, proofs WIP |
