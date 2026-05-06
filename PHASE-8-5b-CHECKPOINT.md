# Phase 8.5b Checkpoint — 8.5b-γ landed (partial)

**Branch**: `feat/randomized-leslie-m3-avss-phase8-5b-gamma`
**Base**: PR #61 (8.5b-β: cert dispatch + avssFairActionEnabled_at_non_terminated)
**Build state**: green.
**Sorry count**: 4 (was 13 at end of 8.5b-β; net −9).

## What 8.5b-γ delivered

1. **Freshness invariant `avssFreshInv`**: new bundle of four
   freshness/source-sent clauses (Q6 echo freshness, Q7 ready
   freshness, Q8 echo source-sent, Q9 ready source-sent) wired into
   the cert's joint invariant.  Closes the **3 queue WF freshness
   sorries** (`partyEchoSend` / `partyReady` / `partyAmplify` cases
   of `avssStep_preserves_avssQueueWfInv`).
2. **`actionGate_iff` 5 corrupt-q branches closed**: existing
   `simSyncInv.local_corrupt_eq` was already strong enough — no
   simSyncInv structural change needed for the gate-equivalence
   proofs.  All 5 corrupt-q branches (partyEchoSend, partyEchoReceive,
   partyReady, partyAmplify, partyReceiveReady) use
   `local_corrupt_eq` plus `simSyncInv`'s honest-side fields.
3. **`avssStep_preserves_simSyncInv` re-derived**: the ~600-LOC body
   was re-written under the C1+C2 model.  For the five C1+C2-affected
   actions, the proof case-splits on `q ∈ corr` (rather than relying
   on the dropped `q ∉ corrupted` gate clause) and uses
   `local_corrupt_eq` + `setLocal` congruence to discharge the corrupt
   side.  Honest-side arguments mirror the original.

## Sorry inventory (4 total)

### Out of scope for 8.5b-γ

| Line | Theorem | Resolution route |
|---|---|---|
| ~4096 | `avssCert.U_dec_prob` corrupt-fire branch | 8.5b-δ termination route switch (running-min). |

### Deferred to 8.5b-γ-followup (deeper structural changes needed)

| Line | Theorem | What's still needed |
|---|---|---|
| ~3879 | `avssFairActionEnabled_at_non_terminated` C5 case | (a) `s.corrupted.card ≤ t` invariant (threshold); (b) echo-flow invariant; (c) delivery-completeness invariant.  Sub-case dispatch via "lex-most-significant Cᵢ" reformulation. |
| ~3893 | Same lemma C7 case | Analogous to C5, plus a ready-flow invariant. |

### Deferred to 8.5c scope

| Line | Theorem | What's still needed |
|---|---|---|
| ~7067 | `coalitionView_corrupt_factors_AE` | Statement weakening + cascade through `corrupt_local_state_uniqueness` (which needs `coalitionTrivialView` infrastructure to recover the 4 schedule-dependent fields).  Per `AVSS-MODEL-NOTES.md` §12.1 row 8.5c. |

## Path forward

```
8.5b-α [✅ 11 sorries]
  ↓
8.5b-β [✅ 13 sorries; cert dispatch + lemma + queue WF]
  ↓
8.5b-γ [✅ this checkpoint, 4 sorries; -9 net]
        Closed: 3 freshness, 5 actionGate_iff, 1 simSyncInv preservation.
        Deferred: 2 lemma stuck cases (γ-followup), 1 coalitionView (8.5c),
                  1 U_dec_prob (8.5b-δ).
  ↓
8.5b-γ-followup — close C5/C7 stuck cases via flow invariants + threshold.
  ↓
8.5b-δ — switch AVSS termination to BC running-min route to absorb
         U_dec_prob corrupt-fire bump.
  ↓
8.5c — `coalitionView_corrupt_factors_AE` weakening + `coalitionTrivialView`
       cascade through secrecy chain (~6 callers).
  ↓
8.5b-ε — verify all axiom-clean, finalize MODEL_NOTES.
```

## Axiom hygiene status

`avssCert` still depends transitively on `sorryAx` (via the lemma's
deep dispatches and the U_dec_prob corrupt branch).  Will become
axiom-clean after 8.5b-γ-followup + 8.5b-δ + 8.5c close the
remaining sorries.

## How to pick up

1. Read this file + `PHASE-8-5b-PLAN.md` (in this worktree).
2. `lake build Leslie.Prob.Index` — confirm green.
3. For 8.5b-γ-followup:
     * Add `s.corrupted.card ≤ t` clause to `cert.Inv` (threshold).
     * Add `avssFlowInv` (echo + ready completeness) and
       `avssDeliveryInv` (Q10).
     * Restructure `avssU_pos_disjunct` to "lex-most-significant
       positive component", then close C5/C7 dispatch.
4. For 8.5b-δ: switch `avss_termination_AS_fair`'s soundness route
   to `pi_n_AST_fair_with_progress_bc_of_running_min_drops`.
5. For 8.5c: introduce `coalitionTrivialView`, weaken
   `coalitionView_corrupt_factors_AE` statement, cascade through
   ~6 secrecy-chain consumers.
