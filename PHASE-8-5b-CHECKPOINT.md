# Phase 8.5b Checkpoint — 8.5b-β landed (partial)

**Branch**: `feat/randomized-leslie-m3-avss-phase8-5b-beta`
**Base**: PR #60 (8.5b-α: model surgery + variant honest-firing premise + cert sorries)
**Build state**: green at 2699 jobs.
**Sorry count**: 13 (was 11 at end of 8.5b-α; net +2).

## What 8.5b-β delivered

1. **Cert dispatch landed**: `avssCert.V_super` / `V_super_fair` / `U_dec_det` no
   longer have direct `sorry`; each is closed via case-split on `isHonestFire`
   with `Or.inl` (variant decreases via `avssU_step_*_lt`) for honest-fired
   actions and `Or.inr` (fair action enabled at post-state) via the new lemma
   `avssFairActionEnabled_at_non_terminated`.
2. **`U_dec_prob`**: honest-fire branch closed; corrupt-fire branch remains
   `sorry` (TODO 8.5b-γ — see "Why U_dec_prob is stuck" below).
3. **Cert `Inv` strengthened**: from `avssTermInv` to
   `avssTermInv ∧ corruptLocalInv ∧ avssQueueWfInv`.
4. **`corruptLocalInv` block relocated**: moved before `avssCert` so the cert
   can reference it in `Inv`.  Definition + `initPred_corruptLocalInv` +
   `avssStep_preserves_corruptLocalInv` are unchanged from PR #60.
5. **New invariant `avssQueueWfInv`**: bundles four protocol-level queue
   invariants:
     * `inflightDeliveries → honest ∧ ¬delivered ∧ dealerMessages.isSome`,
     * `(q, p) ∈ inflightEchoes → q ∉ p.echoesReceived`,
     * `q ∈ inflightReady → q ∉ p.readyReceived` (∀ p),
     * `dealerSent → ∀ p, dealerMessages.isSome`.
   Plus `initPred_avssQueueWfInv` (init: vacuous via empty queues) and
   `avssStep_preserves_avssQueueWfInv` (mechanical preservation modulo three
   `sorry` placeholders for the "echo/ready freshness" invariants — see below).
6. **New lemma `avssFairActionEnabled_at_non_terminated`**: load-bearing
   liveness lemma for the cert's `Or.inr` dispatch.  Cases on `s.dealerSent`:
     * `false` → `dealerShare`'s gate holds; `dealerShare ∈ avssFairActions`.
     * `true` → uses an internal helper `avssU_pos_disjunct` to find a
       positive lex-component, dispatches each to a fair action via queue WF.
7. **New helper `corrupt_fire_post_not_terminated`**: corrupt-fired actions
   (one of `partyEchoSend p` / `partyReady p` / `partyAmplify p` with
   `p ∈ s.corrupted`) populate either `inflightEchoes` or `inflightReady`,
   so the post-state is provably not `terminated`.

## Sorry inventory (13 total)

### New from 8.5b-β (6 sorries — all TODO 8.5b-γ)

| Line | What's needed |
|---|---|
| ~2878 | `q.echoSent = false → q ∉ p.echoesReceived` ("echo freshness"); needed by `avssQueueWfInv` preservation under `partyEchoSend`. |
| ~2987 | `q.readySent = false → q ∉ p.readyReceived` ("ready freshness"); needed by `avssQueueWfInv` preservation under `partyReady`. |
| ~3032 | Same as above for `partyAmplify`. |
| ~3332 | `avssFairActionEnabled_at_non_terminated` C5 case (`notReadySentSet ≠ ∅` + dealerSent=T): the deep "stuck honest party" sub-case (delivered=T ∧ echoSent=T ∧ readyReceived < t+1 ∧ echoesReceived < n-t).  Needs simSyncInv-level "echoes received from honest senders" invariant. |
| ~3343 | Same for C7 case (`unfinishedSet ≠ ∅`). |
| ~3540 | `avssCert.U_dec_prob` corrupt-fire branch.  See "Why U_dec_prob is stuck". |

### Why U_dec_prob is stuck

`FairASTCertificate.U_dec_prob`'s signature requires a uniform `0 < p` such
that *every* gated fair-fire from a non-terminated state contributes ≥ p to
the strict-decrease event.  Under Phase 8.5b's C1+C2 model, corrupt-party
fair-fires of `partyEchoSend` / `partyReady` / `partyAmplify` are in
`avssFairActions` but do **not** strictly decrease `avssU` (since
`unsentEchoSet` / `notReadySentSet` are honest-only).  No uniform `p > 0`
satisfies the field — the strict-decrease event has probability `0` on
corrupt fires.

**Resolution scope**: 8.5b-δ (termination AE-trajectory route switch).  The
fix is to switch `avss_termination_AS_fair`'s soundness route from
`pi_n_AST_fair_with_progress_det` (which consumes `U_dec_prob` directly) to
`pi_n_AST_fair_with_progress_bc_of_running_min_drops` (the BC running-min
route), which absorbs the corrupt-fire bump via the disjunct.

### Inherited from 8.5b-α (7 sorries — all TODO 8.5b-γ)

§15 / §16 secrecy-chain cascade, unchanged from 8.5b-α:

| Line | Theorem | What's needed |
|---|---|---|
| ~6511 | `coalitionView_corrupt_factors_AE` | Theorem statement weakening (drop 4 schedule-dependent clauses). |
| ~8056 | `actionGate_iff` partyEchoSend branch | Corrupt-q gate equivalence under `simSyncInv`. |
| ~8059 | `actionGate_iff` partyEchoReceive branch | Same (C2). |
| ~8062 | `actionGate_iff` partyReady branch | Same (C1). |
| ~8065 | `actionGate_iff` partyAmplify branch | Same (C1). |
| ~8068 | `actionGate_iff` partyReceiveReady branch | Same (C2). |
| ~8109 | `avssStep_preserves_simSyncInv` (entire body) | Re-prove under C1+C2 model. |

## Path forward

```
8.5b-α [✅ 11 sorries, cert sorries pending]
  ↓
8.5b-β [✅ this checkpoint, 13 sorries; cert dispatch landed; lemma + queue WF
        scaffolding in place; 3 freshness sorries in queue WF preservation,
        2 deep dispatches in lemma, 1 U_dec_prob corrupt branch]
  ↓
8.5b-γ — close the 6 new TODOs from 8.5b-β + the 7 §15+ secrecy cascade
        sorries.  Specifically:
          * Add Q6/Q7 (echo/ready freshness) + Q8/Q9 (queue→sent) invariants
            to close the 3 freshness sorries in queue WF preservation.
          * Strengthen lemma's stuck-case dispatch using simSyncInv-level
            "honest echoes/readies received" invariants to close C5/C7.
          * §15 secrecy chain cascade (7 inherited sorries).
  ↓
8.5b-δ — switch AVSS termination to
        `pi_n_AST_fair_with_progress_bc_of_running_min_drops` (BC running-min
        route).  Closes the U_dec_prob corrupt-fire branch by changing the
        soundness route.
  ↓
8.5b-ε — verify all axiom-clean, finalize MODEL_NOTES (§11.1, §11.2, §12.1)
```

## Axiom hygiene status

`avssCert` still depends transitively on `sorryAx` (via the lemma's deep
dispatches and the U_dec_prob corrupt branch).  Will become axiom-clean after
8.5b-γ + 8.5b-δ close the remaining sorries.

## How to pick up

1. Read this file + `PHASE-8-5b-PLAN.md` (in this worktree).
2. `lake build Leslie.Prob.Index` — confirm 2699 green.
3. For 8.5b-γ: focus on
     * Adding `avssQueueWfFreshnessInv` (Q6-Q9) to close lines ~2878, ~2987,
       ~3032 in `avssStep_preserves_avssQueueWfInv`.
     * Adding `avssQueueProgressInv` (simSyncInv-flavored) to close lines
       ~3332, ~3343 in `avssFairActionEnabled_at_non_terminated`.
     * Then close the 7 §15+ secrecy cascade sorries (lines ~6511, ~8056-68,
       ~8109).
4. After closing one or more sorries, push and update this checkpoint file.
