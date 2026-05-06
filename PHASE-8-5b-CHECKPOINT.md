# Phase 8.5b Checkpoint — 8.5b-γ-followup landed (partial)

**Branch**: `feat/randomized-leslie-m3-avss-phase8-5b-gamma-followup`
**Base**: PR #62 (8.5b-γ: queue WF freshness + actionGate_iff + simSyncInv preservation)
**Build state**: green at 2699 jobs.
**Sorry count**: 3 (was 4 at end of 8.5b-γ; net −1: closed two stuck cases at the
cost of one new helper sorry in F4 ready-flow preservation).

## What 8.5b-γ-followup delivered

1. **Flow + threshold invariant `avssFlowInv`**: new bundle of four clauses
   (F1 threshold `s.corrupted.card ≤ t`; F2 delivery completeness; F3 echo flow;
   F4 ready flow), wired into the cert's joint invariant.
2. **`avssCert` signature**: now takes `(h_corr : corr.card ≤ t)` to seed F1
   from `initPred`.  Threaded through `avss_termination_AS_fair`,
   `avss_termination_AS_fair_traj`, and `avss_termination_AS_fair_rushing`.
3. **C5 / C7 stuck-case dispatches**: `avssFairActionEnabled_at_non_terminated`
   now closes both branches via lex-most-significant cascades through the
   higher progress components (ifd / uss / ife / nrs / ifr); when all of those
   are zero the C5 branch dispatches to `partyReady p` via F2 + F3 + threshold,
   and the C7 branch dispatches to `partyOutput p` via F2 + F4 + threshold.

## Sorry inventory (3 total)

### Helper sorry (introduced this PR)

| Line | Theorem | Resolution route |
|---|---|---|
| ~4250 | `avssStep_preserves_avssFlowInv` F4 `partyReceiveReady` branch | **8.5b-γ-followup-2** (or model fix).  The model's `partyReceiveReady r q` globally erases `q` from `inflightReady`, but only `r.readyReceived` gains `q`; F4's "every honest receiver" claim isn't preserved without a stronger broadcast semantics (per-pair tokens like `inflightEchoes`).  Two routes: (a) split `inflightReady` into `Finset (Fin n × Fin n)`; (b) weaken F4 to existential and re-derive C7 dispatch via the lucky-receiver chain.  Tracked by the in-line TODO. |

### Out of scope for 8.5b-γ-followup

| Line | Theorem | Resolution route |
|---|---|---|
| ~4932 | `avssCert.U_dec_prob` corrupt-fire branch | 8.5b-δ termination route switch (running-min). |
| ~7903 | `coalitionView_corrupt_factors_AE` | 8.5c — statement weakening + cascade through `corrupt_local_state_uniqueness` (needs `coalitionTrivialView` infrastructure). |

## Path forward

```
8.5b-α [✅ 11 sorries]
  ↓
8.5b-β [✅ 13 sorries; cert dispatch + lemma + queue WF]
  ↓
8.5b-γ [✅ 4 sorries; -9 net; freshness, actionGate_iff, simSyncInv]
  ↓
8.5b-γ-followup [✅ this checkpoint, 3 sorries; -1 net]
        Closed: C5 / C7 stuck cases via flow + threshold cascade.
        New helper sorry: F4 ready-flow preservation under partyReceiveReady
                          (model-defect sub-followup).
  ↓
8.5b-γ-followup-2 — close F4 ready-flow preservation via model fix
                    (per-pair inflightReady) or invariant weakening.
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

`avssCert` still depends transitively on `sorryAx` (via F4 ready-flow
preservation, U_dec_prob corrupt branch, and coalitionView).  Will
become axiom-clean after 8.5b-γ-followup-2 + 8.5b-δ + 8.5c close the
remaining three sorries.

## How to pick up

1. Read this file + `PHASE-8-5b-PLAN.md` (in this worktree).
2. `lake build Leslie.Prob.Index` — confirm green at 2699 jobs.
3. For 8.5b-γ-followup-2:
     * Decide between (a) splitting `inflightReady` into per-pair
       `Finset (Fin n × Fin n)` (clean but 200+ LOC of cascades) or
       (b) weakening F4 to existential and re-deriving C7 stuck-case
       dispatch via lucky-receiver chain.
4. For 8.5b-δ: switch `avss_termination_AS_fair`'s soundness route
   to `pi_n_AST_fair_with_progress_bc_of_running_min_drops`.
5. For 8.5c: introduce `coalitionTrivialView`, weaken
   `coalitionView_corrupt_factors_AE` statement, cascade through
   ~6 secrecy-chain consumers.
