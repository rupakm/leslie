---
name: lean4-ic3
description: IC3/PDR-style inductive invariant inference — find CTIs, dispatch generalizer, grow a structure-based invariant until inductive
user_invocable: true
---

# Lean4 IC3

Property-directed reachability for Lean4 invariant proofs. Drives a CEGAR loop over
a structure-based invariant: probe each action, extract counterexamples-to-induction
(CTIs) from residual goals, dispatch a generalizer subagent to propose new conjuncts,
insert them as non-breaking structure fields, and iterate until inductive.

**Prerequisite:** The invariant MUST be a `structure`, not a flat `∧`. Adding fields
is the whole point — it must be non-breaking for existing field accessors.

## Usage

```
/lean4-ic3 File.lean::InvName --spec=specName --safety=safetyLemma
/lean4-ic3 ... --max-iters=8
/lean4-ic3 ... --decide-cti=auto --check-n=3
/lean4-ic3 ... --generalizer=manual        # default on first run
/lean4-ic3 ... --generalizer=agent         # dispatch ic3-generalizer
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| target | Yes | — | `File.lean::StructureName` |
| --spec | Yes | — | Spec value used with `action_cases` (e.g. `tlMessages`) |
| --safety | Yes | — | Safety lemma the invariant must imply |
| --init-lemma | No | `init_preserves_inv` | Base-case lemma name |
| --step-lemma | No | `step_preserves_inv` | Inductive-step lemma name |
| --max-iters | No | 8 | Max new conjuncts added before giving up |
| --generalizer | No | manual | `manual` (prompt user) or `agent` (`ic3-generalizer`) |
| --decide-cti | No | auto | `auto` / `off` / `always` — concretize CTI via decide at small n |
| --check-n | No | 3 | n for decide-based CTI concretization |

Refuse to start if the target invariant is not a `structure` declaration — flat
conjunctions make non-breaking insertion impossible. Tell the user to refactor
first. (See CLAUDE.md "Invariant Composition: Use Structures, Not Flat Conjunctions".)

## Actions

### Phase 0 — Baseline snapshot

1. `lean_diagnostic_messages(file)` → record sorry count + diagnostic baseline.
2. `lean_file_outline(file)` → discover invariant structure fields and action names.
3. Verify `init-lemma` and `step-lemma` exist (may contain `sorry`; that is fine).
4. Snapshot the invariant structure declaration verbatim. This is the rollback point.

On any regression (later phase increases sorry count beyond baseline or adds new
diagnostics), revert to this snapshot and abort with a report.

### Phase 1 — Base case

Dispatch the base-case cascade at `init-lemma`:

```
intro s h_init
constructor
<;> first | rfl | simp [init_defs] | decide | grind
```

via `lean_multi_attempt`. For any field that fails:

1. `lean_goal` at the failing subgoal → the **Init CTI**.
2. Package hypotheses + negated goal and hand to Phase 3 (Generalize) with
   `cti_kind = init`.

If all fields close: move to Phase 2.

### Phase 2 — Inductive step (per action)

The core of IC3 in Lean. This phase runs a **mandatory reduction cascade**
before any CTI is extracted, and applies a **strict dispatch gate** before
invoking the generalizer. The cascade plays the role that symbolic simulation
plays in hardware IC3: it turns a monolithic preservation obligation into
localized leaf goals that can actually be generalized.

**Why the cascade matters.** In hardware PDR, SAT gives you a concrete
counterexample cube — a specific assignment to pre-state variables that
witnesses the failure. In Lean, there is no built-in symbolic executor: a
bare `sorry` at a preservation lemma leaves you with the *whole* property as
a residual goal, which contains no instantiation, no pre-state witness, no
localizable facts. The generalizer cannot do anything with that. The cascade
below is Lean's substitute for SAT: it unfolds, case-splits, and normalizes
until either the goal closes or the remaining residuals are small leaves
about specific pre-state projections.

#### Phase 2a — Reduction cascade (mandatory, per action)

1. Open `step-lemma`, run `action_cases h with <spec>` (Leslie gadget).
2. For each action case `a`, run the cascade in order. Stop at the first
   level that yields a closed goal (move to next field). If ALL levels fail,
   collect residuals for the dispatch gate.
   - **L0 — Unfold & introduce.** `intro`s on quantifiers, `refine
     ⟨?_, …, ?_⟩` to push inside the target structure, `obtain ⟨…⟩ := …`
     to destructure witnesses in hypotheses.
   - **L1 — Normalize.** `simp only [action_simp, setFn_same, setFn_ne,
     <frame lemmas for a>]`. Project the post-state delta to its minimal
     form so frame facts become syntactic.
   - **L2 — Frame close.** For each invariant field `C` whose footprint is
     disjoint from action `a`'s write set (from `#gen_frame_lemmas`-derived
     metadata), try `exact hinv.C`. If the field is partially disjoint
     (e.g., `setFn f i v` updates only at `i`), `by_cases` on the witness
     index and close the `≠ i` side with `hinv.C`.
   - **L3 — Existential witness.** For goals of the form `∃ b w, P`, try
     `obtain ⟨b, w, hP⟩ := hinv.<candidate field>; exact ⟨b, w, hP⟩` for
     each existing field whose conclusion is of similar shape. Use
     `lean_multi_attempt` to probe candidates.
   - **L4 — Closure automation.** `lean_multi_attempt` with
     `["omega", "grind", "decide", "simp [hinv]"]` — the standard tail.
     Budget: ≤5 seconds per goal.
   - **L5 — State-search.** `lean_state_search` on the residual goal. If
     one of the returned lemmas closes the goal via `lean_multi_attempt`,
     accept it.
3. Any leaf goal surviving L0–L5 becomes a **candidate CTI**. Record the
   `lean_goal` output verbatim, the action, and the cascade path taken.

#### Phase 2b — Dispatch gate (strict)

For each candidate CTI, check ALL of the following. If ANY check fails, do
NOT call the generalizer — instead, route per the "non-dispatchable"
actions below.

| Gate | Check | Failure route |
|------|-------|---------------|
| **G1 Localized** | Goal references ≤5 distinct hypothesis identifiers AND is a scalar predicate (≤ , ≥, =, ∃ with concrete body) — NOT `∀` over fresh vars, NOT `safeAt`-style nested quantifiers. | → structural gap (see below) |
| **G2 Action-scoped** | Failing case is tagged with exactly one action; hypothesis footprint lies in that action's write set ∪ its read set. | → skill bug, report and stop |
| **G3 Automation-clean** | L4 cascade was tried and exhausted. No `lean_multi_attempt` candidate closed the goal. | → close with automation (not a CTI) |
| **G4 Field-miss** | `exact hinv.<name>` fails for every field in the current invariant (L2 tried). | → close with existing field (not a CTI) |
| **G5 Hypothesis shape** | Pre-state hypotheses are projections of `s.*` (state variables), not abstract predicates. The generalizer's job is to find a universal closure over state projections — it cannot generalize over opaque function symbols. | → structural gap |

**All gates pass → dispatchable CTI.** Proceed to Phase 3 with the
pre-collected context packet.

**Any gate fails → non-dispatchable.** Route as follows:

- **Structural gap (G1, G5):** the residual is too large or too abstract for
  a single-conjunct generalization. This typically means the proof skeleton
  is missing a *structural* step (a case-split, a witness construction, an
  auxiliary lemma), not a missing invariant. Record under
  `structural_gaps[]` in the report. Options:
  - Escalate to human with "skeleton gap — propose structural reasoning
    for {goal}".
  - Optionally dispatch `sorry-filler-deep` from `/lean4:prove` with the
    residual goal as input — that agent can propose *proof-level* help
    (structural case splits), while IC3's generalizer only proposes
    *invariant-level* help (new conjuncts). These are complementary.
  - Never loop the IC3 generalizer on a structural gap — it will either
    propose ¬CTI or propose a too-strong conjunct that fails base case.
- **Closable without CTI (G3, G4):** the cascade just needs to accept the
  closure and move on. Record as `closed_without_cti[]`. No generalizer
  call.
- **Skill bug (G2):** the action labeling or footprint analysis is wrong.
  Log and stop the phase — human triage required.

#### Phase 2c — CTI prioritization

From the dispatchable CTIs, prioritize for Phase 3:

1. `init` CTIs first (smaller, trivial base cases).
2. Step CTIs by ascending hypothesis-identifier count (simpler generalizes
   cleaner — matches our empirical finding that unguarded universal closures
   are the best targets).
3. Step CTIs tagged with actions that have smaller write sets (frame-heavy
   actions → cleaner CTIs).
4. Tie-break by CTI first discovered.

#### Phase 2d — Optional decide witness

If `--decide-cti=auto` and the spec is decidable at `n ≤ check-n`, for each
dispatchable CTI emit a scratch `example` that instantiates the CTI at
`n = check-n` and run `lean_run_code` with `decide` / `native_decide`. If a
concrete witness is produced (counterexample at finite n), attach it to the
CTI packet — it drastically narrows the generalizer's hypothesis space.

If the worklist of dispatchable CTIs is empty AND the worklist of
non-dispatchable routes is also empty: proof is complete for this iteration,
go to Phase 5. If the dispatchable worklist is empty but the non-dispatchable
worklist is non-empty, report the structural gaps and stop (do not call the
generalizer on empty).

### Phase 3 — Generalize

Take one CTI from the worklist (prefer `init` CTIs, then `step` CTIs with the
smallest residual hypothesis set — simpler CTIs generalize more cleanly).

Build a **pre-collected context packet**:
- File path + invariant structure snippet.
- Existing invariant field names and types (one-liners).
- Spec definition + offending action definition.
- Pretty-printed CTI hypotheses + failing goal (from `lean_goal`).
- Optional decide witness.
- A premise index snapshot: names/types from `Leslie/Examples/Combinators/` and
  `Leslie/Gadgets/` likely to be relevant (grep for `lock_unique`,
  `majorityQuorum`, `cross_phase`, `setFn_*`, `*_frame`, etc.).

If `--generalizer=manual`:

> **CTI found.** Action `{a}`, field `{C}`. Pre-state: `{hypotheses}`. Failing
> goal: `{goal}`. {decide witness if any}. Propose a new conjunct `hC' : …`
> such that (a) Init → C', (b) Inv ∧ C' ∧ step_a preserves both C' and C, and
> (c) C' is as weak as possible — do NOT just conjoin ¬CTI. Reply with:
> ```
> name: hC'
> type: ∀ …, …
> rationale: <one line>
> ```

Wait for user response.

If `--generalizer=agent`:

Dispatch the `ic3-generalizer` subagent with the pre-collected context packet.
Agent returns a proposal in the same strict format above.

### Phase 4 — Insert & re-check

1. **Type-check probe** (mandatory): before editing the file, run
   `lean_multi_attempt` with a throwaway `example : {proposed C'} := by sorry`
   at an appropriate position. If elaboration fails, bounce back to Phase 3
   with the elaboration error (max 2 bounces per CTI; then skip CTI and report).
2. Edit the invariant structure by **appending** the new field at the END of
   the structure, and append a matching `·` bullet at the END of every
   `apply <Struct>.mk` block in existing proofs.
   - **CRITICAL:** never insert mid-structure. Positional `·` bullet lists in
     existing `apply Struct.mk` proofs rely on field order; mid-insertion
     shifts every subsequent bullet to the wrong field. Append is safe;
     mid-insert is a regression.
   - **Existential unification gotcha:** `∃ b w, P ∧ Q` and
     `∃ b, (∃ w, P) ∧ Q` are semantically identical but not syntactically
     unified. When synthesizing the trivial init-case body or a frame-case
     bullet, prefer `obtain ⟨…⟩ := …; exact ⟨…⟩` patterns over bare anonymous
     constructor tuples.
3. `lean_diagnostic_messages(file)` → compare against baseline:
   - **Base lemma now fails on `hC'`:** `C'` isn't initiation-valid. Treat
     as a fresh Init CTI for `hC'`, append to worklist, loop Phase 3 with
     `bounce_count + 1`. Bounce budget per original CTI = 2.
   - **Step lemma regresses somewhere else:** rollback the field insertion,
     append failure to CTI report, continue worklist.
   - **Old CTI now closes:** mark CTI resolved, increment conjunct counter.
     If conjunct counter ≥ `--max-iters`, stop and report.
4. Re-run Phase 2 over all actions — adding `hC'` may create NEW step CTIs for
   `hC'` itself (the "recursive CTI" case). Append any new CTIs to the worklist.

### Phase 5 — Fixpoint check

When the worklist empties:

1. Full `lean_diagnostic_messages(file)`: expect zero sorries in `init-lemma`
   and `step-lemma`.
2. Try to discharge `safety` lemma using the grown invariant: attempt
   `exact h_inv.hSafety` first, then `lean_multi_attempt` with a short cascade.
3. If safety closes: success. Invoke `/lean4:checkpoint`-equivalent (stage +
   commit touched files). If safety does NOT close, that is a signal the
   invariant is inductive but still too weak for safety — report and stop.
   Do NOT loop (safety failures are not CTIs in the same sense).

### Phase 6 — Report

```
## IC3 Report

Target: {file}::{Inv}
Spec: {spec}
Iterations: {k}/{max-iters}
Conjuncts added: {list of hC' names with one-line rationales}
CTIs resolved: {n}
CTIs skipped (elaboration failure or rollback): {n}
Remaining sorries: {init-lemma / step-lemma / safety}
Build status: {green / red}
```

On `red` build status at any phase, rollback to the Phase 0 snapshot.

## Stuck conditions

Abort with stuck report if:
- Same CTI returns from Phase 4 twice with the same generalizer proposal.
- `--max-iters` reached with a non-empty worklist.
- Generalizer subagent returns "I cannot propose a conjunct" twice in a row.
- `lean_diagnostic_messages` shows new, unrelated diagnostics after an insert
  (regression gate).

In all stuck cases, write the CTI worklist and last generalizer proposal to a
report and leave the file in the most-recent-good state (rollback any pending
insert).

## Safety

- Never modify `init-lemma` or `step-lemma` bodies except to add field cases.
- Never delete fields from the invariant structure.
- Never modify declaration headers (header fence from cycle-engine.md).
- Never broaden `git add`; stage only the target file.
- On any kernel error in diagnostics, immediate rollback.

## Reuses

- `lean_goal`, `lean_diagnostic_messages`, `lean_multi_attempt`,
  `lean_file_outline`, `lean_run_code`, `lean_local_search`, `lean_leansearch`,
  `lean_loogle` — no new MCP tools.
- Leslie gadgets: `action_cases`, `#gen_frame_lemmas`, `setFn` simp lemmas.
- `ic3-generalizer` subagent for Phase 3 when `--generalizer=agent`.

## See Also

- `/lean4:prove` — general cycle-by-cycle proving (use when the invariant is
  already known and you only need to fill sorries).
- `ic3-generalizer` — the narrow Phase-3 subagent.
- `CLAUDE.md` "Invariant Composition: Use Structures" — prerequisite.
