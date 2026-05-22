# Leslie

Leslie is a Lean 4 library for specifying and verifying concurrent and
distributed systems with machine-checked proofs. It provides two independent
frameworks under one roof:

| Framework | Import | Description |
|-----------|--------|-------------|
| **Leslie** (TLA) | `import Leslie` | Shallow embedding of the Temporal Logic of Actions. Interleaving and round-based protocols, refinement mappings, CIVL-style layers, cutoff theorems. |
| **Leslie_LTS** | `import Leslie_LTS` | Labelled Transition Systems with simulation, composition, adversaries, probabilistic reasoning, and secrecy. Byzantine fault-tolerance examples. |

Each framework has its own README with full details:

- [Leslie/README.md](Leslie/README.md) — TLA framework
- [Leslie_LTS/README.md](Leslie_LTS/README.md) — LTS framework

## Building

Requires [elan](https://github.com/leanprover/elan) with Lean 4.

The project provides a `Makefile` with convenient build shortcuts:

| Target | Command | Description |
|--------|---------|-------------|
| `make` / `make all` | `lake build` | Build both frameworks |
| `make LTS` | `lake build Leslie_LTS` | Build only the LTS framework |
| `make TLA` | `lake build Leslie` | Build only the TLA framework |
| `make clean` | `lake clean` | Clean all build artifacts |

> **Warning:** `make clean` deletes the Mathlib build cache, making the next
> build extremely slow as Mathlib must be rebuilt from scratch. Avoid it unless
> absolutely necessary.

## Repository Layout

```
Leslie/                TLA framework (source + docs)
Leslie.lean            TLA umbrella import
Leslie_LTS/            LTS framework (source + docs)
Leslie_LTS.lean        LTS umbrella import
lakefile.lean          Lake build configuration
Makefile               Build shortcuts
```

## License

Apache 2.0 — see [LICENSE](LICENSE).
