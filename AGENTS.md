<!-- ox:prime-check -->
**BLOCKING**: Run `ox agent prime` NOW before ANY other action. Do NOT respond to the user first. Enables SageOx queries.

# AI Agent Instructions

<!-- ox:prime --> Run SageOx `ox agent prime` on session start, after compaction, or clear. (DO NOT REMOVE)

## Makefile

The project provides a `Makefile` with convenient build shortcuts:

| Target | Command | Description |
|--------|---------|-------------|
| `make` / `make all` | `lake build` | Build both frameworks (TLA + LTS) |
| `make LTS` | `lake build Leslie_LTS` | Build only the LTS framework |
| `make TLA` | `lake build Leslie` | Build only the TLA framework |
| `make clean` | `lake clean` | Clean all build artifacts |

Use `make LTS` for day-to-day work on the LTS framework to avoid building the TLA framework.

**Warning:** `make clean` (`lake clean`) deletes the Mathlib build cache, making the next build extremely slow as Mathlib must be rebuilt from scratch. Avoid `make clean` unless absolutely necessary.
