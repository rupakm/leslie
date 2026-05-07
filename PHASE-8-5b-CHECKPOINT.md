# Phase 8.5b Checkpoint — 8.5b-α landed

**Branch**: `feat/randomized-leslie-m3-avss-phase8-5b-proper`
**Base**: PR #59 (V_super disjunct framework)
**Build state**: green at 2699 jobs.
**Sorry count**: 11 (all named with `-- TODO Phase 8.5b-X` comments).

## What 8.5b-α delivered

1. **C1 closure**: dropped `p ∉ s.corrupted` from gates of `partyEchoSend`/`partyReady`/`partyAmplify`.
2. **C2 closure**: dropped `p ∉ s.corrupted` from `partyEchoReceive` and `partyReceiveReady` gates.
3. **Broadcast filter broadening**: `partyEchoSend`'s effect now uses `Finset.univ` (covers all receivers).
4. **`corruptLocalInv` weakening**: from 6 clauses to 2 (`output = none ∧ delivered = false → rowPoly = none`).
5. **`isHonestFire` predicate**: new helper for the case-split dispatch.
6. **Per-action `_lt` variant lemmas**: added `(hph : p ∉ s.corrupted)` premise to `avssU_step_partyEchoSend_lt` / `_partyReady_lt` / `_partyAmplify_lt`; updated gate tuple destructuring.
7. **`avssU_step_le` and `avssU_step_lt_of_fair`**: added `(hph : isHonestFire a s)` premise.
8. **`avssTermInv_step` preservation cases**: re-derived contradictions for new gate tuples.
9. **`avssStep_preserves_corruptLocalInv`** + **`corruptLocalInv_local_trivial`**: rewritten for the weakened invariant.

## Sorry inventory (11 total)

### To be closed by 8.5b-β (4 sorries)

`avssCert` field-level sorries — replace with `isHonestFire` case-split:

| Line | Field | What's needed |
|---|---|---|
| 2572 | `V_super` | Honest case → `Or.inl` via `avssU_step_le` (with `hph`). Corrupt case → `Or.inr` via new lemma `avssFairActionEnabled_at_non_terminated`. |
| 2573 | `V_super_fair` | Honest fair-fire → `Or.inl` via `avssU_step_lt_of_fair`. Corrupt → unreachable (corrupt actions aren't in `avssFairActions` if we keep the existing definition; verify). |
| 2575 | `U_dec_det` | Same case-split pattern. |
| 2578 | `U_dec_prob` | Same case-split pattern. |

**New lemma 8.5b-β must define**:

```lean
theorem avssFairActionEnabled_at_non_terminated
    (s : AVSSState n t F) (hinv : avssTermInv s)
    (hcorrupt : corruptLocalInv s) (hnt : ¬ terminated s) :
    ∃ j ∈ avssFairActions, actionGate j s
```

Argument: case-split on `s.dealerSent`. If `false`, `dealerShare` is fair and gated. If `true`, some honest party is non-terminated; case-split on its protocol position to find an enabled fair action (`partyDeliver`, `partyEchoSend`, `partyReady`, etc. — whichever step is next for that party).

### To be closed by 8.5b-γ (7 sorries)

§15 / §16 secrecy-chain cascade:

| Line | Theorem | What's needed |
|---|---|---|
| 5669 | `coalitionView_corrupt_factors_AE` | **Theorem statement needs weakening**: drop the 4 schedule-dependent clauses (`echoSent = false`, `echoesReceived = ∅`, `readySent = false`, `readyReceived = ∅`). Re-prove the remaining clauses (`output = none`, `delivered → rowPoly = ...`). Cascade through ~6+ secrecy-chain consumers. |
| 7214 | `actionGate_iff` partyEchoSend branch | Corrupt-q gate-equivalence under `simSyncInv`. `simSyncInv` likely needs strengthening to preserve corrupt locals' (delivered, echoSent) fields. |
| 7217 | `actionGate_iff` partyEchoReceive branch | Same as above for partyEchoReceive (C2). |
| 7220 | `actionGate_iff` partyReady branch | Same as above for partyReady. |
| 7223 | `actionGate_iff` partyAmplify branch | Same as above for partyAmplify. |
| 7226 | `actionGate_iff` partyReceiveReady branch | Same as above for partyReceiveReady (C2). |
| 7267 | `avssStep_preserves_simSyncInv` (entire body) | Re-prove under C1+C2 model. The full original proof was ~600 LOC; the corresponding case-split was deleted in this checkpoint to keep the file build-green. **Recommended**: strengthen `simSyncInv` to preserve corrupt locals' (delivered, echoSent, echoesReceived, readySent, readyReceived) fields too, then re-derive. |

## Path forward

```
8.5b-α [✅ this checkpoint, 11 sorries]
  ↓
8.5b-β  — close 4 cert sorries (~200 LOC, defines avssFairActionEnabled_at_non_terminated)
  ↓
8.5b-γ  — close 7 secrecy-chain sorries (~300-400 LOC; the deepest one)
  ↓
8.5b-δ  — switch AVSS termination to `pi_n_AST_fair_with_progress_bc_of_running_min_drops`
  ↓
8.5b-ε  — verify all axiom-clean, finalize MODEL_NOTES (§11.1, §11.2, §12.1)
```

## How to pick up

1. Read this file + `PHASE-8-5b-PLAN.md` (in this worktree).
2. `lake build Leslie.Prob.Index` — confirm 2699 green.
3. Pick a sorry to close based on which sub-PR you're on.
4. After closing one or more sorries, push and update this checkpoint file.
