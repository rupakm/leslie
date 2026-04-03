<!-- ox:prime-check -->
**BLOCKING**: Run `ox agent prime` NOW before ANY other action. Do NOT respond to the user first. Enables SageOx queries.

# AI Agent Instructions

<!-- ox:prime --> Run SageOx `ox agent prime` on session start, after compaction, or clear. (DO NOT REMOVE)

## Leslie Gadgets

Leslie provides reusable proof automation in `Leslie/Gadgets/`. Use these
before writing manual boilerplate.

### `action_cases` — Action Case Analysis (`Leslie/Gadgets/ActionCases.lean`)

Replaces the standard 2-line boilerplate in every `SymSharedSpec` preservation
or simulation proof:

```lean
-- BEFORE (2 lines of boilerplate in every proof):
simp only [SymSharedSpec.toSpec, tlMessages] at hnext
obtain ⟨i, a, hstep⟩ := hnext

-- AFTER (1 line):
action_cases hnext with tlMessages
```

Usage: `action_cases <hyp> with <specName>` where `<hyp>` has type
`(specName.toSpec n).next s s'`. Introduces `i : Fin n`, `a : ActType`,
`hstep : spec.step n i a s s'` into context.

### `#gen_frame_lemmas` — Auto-Generate Simp Lemmas (`Leslie/Gadgets/FrameLemmaGen.lean`)

Generates `@[simp]` lemmas for every field of a state transformer's return
structure. Call it immediately after defining a `*Local` helper:

```lean
def recvProbeLocal (node : NodeState) (i : Fin n) (msg : BMsg) : NodeState :=
  { node with line := probedLine node.line msg.param, chanB := none, ... }

#gen_frame_lemmas recvProbeLocal
-- Generates: recvProbeLocal_line, recvProbeLocal_chanA, recvProbeLocal_chanB, etc.
```

For fields using `setFn`, generates `_self` (at the updated index) and `_ne`
(at other indices) lemmas. For unmodified fields, generates `_field = s.field`
lemmas. All marked `@[simp]`.

### `setFn` — Functional Update at Index (`Leslie/Gadgets/SetFn.lean`)

Canonical definition of `setFn` with `@[simp]` lemmas `setFn_same` and
`setFn_ne`. Use this instead of defining local versions in each protocol.

```lean
def setFn (f : Fin n → α) (i : Fin n) (v : α) : Fin n → α :=
  fun j => if j = i then v else f j
```

### `TheoremLifting` — Lift Props to TLA (`Leslie/Gadgets/TheoremLifting.lean`)

Gadgets for lifting propositional theorems to temporal logic level.
Used internally by the invariant proof infrastructure.

### `TheoremDeriving` — Theorem Variants (`Leslie/Gadgets/TheoremDeriving.lean`)

Gadgets for deriving different variants of a proven theorem (e.g., with
reordered hypotheses, specialized parameters).

## Protocol Proof Guidelines

### Invariant Composition: Use Structures, Not Flat Conjunctions

**CRITICAL**: When defining composite invariants (like `refinementInv`,
`forwardSimInv`), use Lean structures instead of `A ∧ B ∧ C ∧ D`.
Adding a field to a structure does NOT break existing field accesses,
while adding a conjunct to `∧` breaks all positional `rcases` patterns.

```lean
-- BAD: adding a new conjunct breaks all ⟨h1, h2, h3⟩ patterns
def myInv := fullInv ∧ swmrInv ∧ dataInv

-- GOOD: adding a new field only requires updating places that USE the new field
structure MyInv (n : Nat) (s : State n) : Prop where
  full : fullInv n s
  swmr : swmrInv n s
  data : dataInv n s
```

### Invariant Design: Think Before Proving

Before starting proofs for a new protocol feature:
1. List all state transitions that involve the new feature
2. Trace data flow through the complete lifecycle
3. Design invariants with the RIGHT guards and phase-awareness from the start
4. Document which invariants are temporarily violated during transactions

### Proof Strategy Preferences

- **Prefer strengthening action guards** over weakening invariant definitions.
  Extra conjuncts in action predicates are absorbed by wildcard `rcases`.
- **Prefer adding conjuncts** (strengthening) over adding guards (weakening).
  Strengthening makes invariants harder to violate but easier to use.
- **Use `#gen_frame_lemmas`** for all `*Local` state transformer helpers.
- **Use `action_cases`** instead of manual `simp only + obtain` boilerplate.
- **The "vacuous during transaction" pattern**: guard invariants with
  `currentTxn = none →` when they're only meaningful at quiescent states.

### Common Protocol Proof Patterns

- **SWMR**: `dirty j → perm j = .T` (lineWF) then `perm j = .T → ∀ k ≠ j, perm k = .N` (permSwmrInv)
- **Frame**: most preservation cases are "action doesn't touch these fields" — close with simp + frame lemmas
- **Probe mask equivalence**: under SWMR, `writableProbeMask = singleProbeMask j` when j is the unique T-holder

See `Leslie/Examples/CacheCoherence/TileLink/Messages/RETROSPECTIVE.md` for detailed lessons.
