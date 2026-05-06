# Phase 8.5b Checkpoint — 8.5b-γ-followup-2 landed

**Branch**: `feat/randomized-leslie-m3-avss-phase8-5b-gamma-followup-2`
**Base**: PR #63 (8.5b-γ-followup: F4 flow + threshold invariant + C5/C7 dispatch).
**Build state**: green at 2699 jobs.
**Sorry count**: 2 (was 3 at end of 8.5b-γ-followup; net −1: F4 preservation closed via per-pair tokens).

## What 8.5b-γ-followup-2 delivered

**Route (a) chosen** (per the WORKER_TASK brief).  Per-pair `inflightReady`
tokens `(q, p)` mirror the existing `inflightEchoes : Finset (Fin n × Fin n)`
shape.

1. **Field type**: `AVSSState.inflightReady : Finset (Fin n × Fin n)`.
2. **Action effects**:
   * `partyReady p` / `partyAmplify p`: insert `(p, r)` for every receiver
     `r` via `Finset.univ.image (fun r => (p, r))` (same pattern as
     `partyEchoSend`).
   * `partyReceiveReady r q`: erase just the consumed token `(q, r)`.
3. **Gate**: `partyReceiveReady r q` requires `(q, r) ∈ inflightReady`.
4. **`inflightReady_card_le`**: bound widened from `≤ n` to `≤ (n+1)²`
   (= `K`).
5. **`avssU` bound**: the `inflightReady.card * K` term now contributes
   `≤ K²` instead of `≤ n·K`; total bound widened from `6·n·K⁶ + K⁶` to
   `5·n·K⁶ + 2·K⁶`, both within the `(7·n + 7)·K⁶` constant.
6. **Variant strict-decrease**:
   * `avssU_step_partyReceiveReady_lt`: erase `(q, p)` instead of `q`;
     same K-drop argument.
   * `avssU_step_partyReady_lt` / `_partyAmplify_lt`: increase ≤ n
     instead of ≤ 1; net K² − n·K = K(K−n) ≥ K ≥ 1 (using K ≥ n + 1).
7. **Invariants updated**:
   * `avssQueueWfInv` Q3: `(q, p) ∈ ifr → q ∉ p.readyReceived`.
   * `avssFreshInv` Q9: `(q.readySent = false) → ∀ p, (q, p) ∉ ifr`.
   * `avssFlowInv` F4: `q ∈ p.readyReceived ∨ (q, p) ∈ ifr`.
   * `simSyncInv.inflightReady_eq`: type changes; `congrArg` updated to
     thread the per-pair image / erase shape.
8. **F4 preservation** under `partyReceiveReady r q` is now mechanical:
   the action only erases `(q, r)`; for `(q', p) ≠ (q, r)` the pre token
   survives, and the consumed token `(q, r)` is replaced by
   `q ∈ r.readyReceived`.
9. **C5 / C7 stuck-case dispatches**: pick `(q, r) ∈ ifr` (instead of
   `q ∈ ifr`) and dispatch `partyReceiveReady r q`.
10. **`corrupt_fire_post_not_terminated`**: token witness updated to
    `(p, p) ∈ ifr_post` (uses the diagonal pair).

## Sorry inventory (2 total)

### Out of scope for 8.5b-γ-followup-2

| Line | Theorem | Resolution route |
|---|---|---|
| ~5045 | `avssCert.U_dec_prob` corrupt-fire branch | 8.5b-δ termination route switch (running-min). |
| ~8016 | `coalitionView_corrupt_factors_AE` | 8.5c — statement weakening + cascade through `corrupt_local_state_uniqueness` (needs `coalitionTrivialView` infrastructure). |

## Path forward

```
8.5b-α [✅ 11 sorries]
  ↓
8.5b-β [✅ 13 sorries; cert dispatch + lemma + queue WF]
  ↓
8.5b-γ [✅ 4 sorries; -9 net; freshness, actionGate_iff, simSyncInv]
  ↓
8.5b-γ-followup [✅ 3 sorries; -1 net]
        Closed: C5 / C7 stuck cases via flow + threshold cascade.
        New helper sorry: F4 ready-flow preservation under partyReceiveReady.
  ↓
8.5b-γ-followup-2 [✅ this checkpoint, 2 sorries; -1 net]
        Closed: F4 ready-flow preservation via per-pair `inflightReady`
                tokens (Route (a)).
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

`avssCert` still depends transitively on `sorryAx` (via U_dec_prob corrupt
branch and coalitionView).  After 8.5b-γ-followup-2, the cert's
`avssFlowInv` clause and `avssFairActionEnabled_at_non_terminated` are
fully axiom-clean.  The cert becomes axiom-clean after 8.5b-δ + 8.5c
close the remaining two sorries.

## How to pick up

1. Read this file + `PHASE-8-5b-PLAN.md` (in this worktree).
2. `lake build Leslie.Prob.Index` — confirm green at 2699 jobs.
3. For 8.5b-δ: switch `avss_termination_AS_fair`'s soundness route
   to `pi_n_AST_fair_with_progress_bc_of_running_min_drops`.
4. For 8.5c: introduce `coalitionTrivialView`, weaken
   `coalitionView_corrupt_factors_AE` statement, cascade through
   ~6 secrecy-chain consumers.
