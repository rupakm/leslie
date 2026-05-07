# Phase 8.5b Checkpoint — 8.5b-δ landed (BC running-min route switch)

**Branch**: `feat/randomized-leslie-m3-avss-phase8-5b-delta`
**Base**: PR #64 (8.5b-γ-followup-2: per-pair `inflightReady` tokens).
**Build state**: green at 2699 jobs.
**Sorry count**: 2 (unchanged; U_dec_prob reclassified as **vestigial** —
see "Why U_dec_prob remains" below).

## What 8.5b-δ delivered

**Soundness route switch** in the AVSS termination theorems
(`Leslie/Examples/Prob/AVSS.lean`):

- `avss_termination_AS_fair` / `_traj` / `_rushing` were previously
  parameterised on `TrajectoryUMono` (`avssU` non-increasing along
  every trajectory step) and `TrajectoryFairStrictDecrease` (strict
  drop on each fair firing in the `V` sublevel), and discharged via
  `FairASTCertificate.sound` / `pi_n_AST_fair_with_progress_det`.
- Under the C1+C2 model (Phase 8.5b), corrupt parties may fire
  `partyEchoSend` / `partyReady` / `partyAmplify` /
  `partyEchoReceive` / `partyReceiveReady`, all of which are in
  `avssFairActions`.  A corrupt-fired send *increases* `avssU`
  (the honest-only `unsentEcho`/`notReadySent` components don't
  shrink while `inflightEchoes`/`inflightReady` grows by ≤ n).
  `TrajectoryUMono` is therefore **false**.
- Phase 8.5b-δ replaces both witnesses with a single per-sublevel
  `TrajectoryFairRunningMinDropIO` hypothesis and dispatches
  termination via
  `pi_n_AST_fair_with_progress_bc_of_running_min_drops`.  The BC
  running-min route handles non-monotone variants by tracking the
  running minimum of `avssU` along trajectories: every fair firing
  strictly drops the running minimum, even though intermediate
  corrupt firings may temporarily raise the pointwise value.

The body of `avss_termination_AS_fair_traj` retains the explicit
`pi_infty_zero_fair` + per-sublevel partition argument (the
`partition_almostDiamond_fair` skeleton); only the inner
sublevel-rule dispatch changed (det → BC running-min).

## Why `U_dec_prob` remains as a vestigial sorry

The `FairASTCertificate.U_dec_prob` field has the strict-form
signature

```lean
∀ k : ℝ≥0, ∃ p : ℝ≥0, 0 < p ∧
  ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
    i ∈ F.fair_actions → Inv s → ¬ terminated s → V s ≤ k →
    p ≤ ∑' s' : σ,
      ((spec.actions i).effect s h) s' *
        (if U s' < U s then 1 else 0)
```

Under the C1+C2 model + the Dirac kernel, this requires a uniform
`p > 0` such that **every** fair-fired step from a non-terminated
invariant state strictly decreases `avssU`.  Corrupt-fired actions
(`partyEchoSend p` for `p ∈ s.corrupted` etc.) are gated and in
`avssFairActions` whenever the local-state preconditions hold
(`s.dealerSent = true` and `(s.local_ p).delivered = true ∧
echoSent = false`), and they bump `avssU`.  The strict-decrease
indicator sums to 0 in those cases, forcing `p ≤ 0`, contradicting
`0 < p`.  No clause of `Inv` (`avssTermInv ∧ corruptLocalInv ∧
avssQueueWfInv ∧ avssFreshInv ∧ avssFlowInv`) excludes such
corrupt-fire premised states; `Inv` is consistently preserved by
`partyCorruptDeliver` (the action that creates the
`delivered = true ∧ echoSent = false` window for corrupt parties).

**Why this is OK on the live soundness path.** The BC running-min
route consumes `cert.U_bdd_subl`, `cert.Inv`, `cert.inv_step`, and
the caller-supplied `TrajectoryFairRunningMinDropIO` witness only.
`cert.U_dec_prob` is **not consumed** by
`pi_n_AST_fair_with_progress_bc_of_running_min_drops` or
`pi_n_AST_fair_with_progress_bc`, so the sorry is dead weight on
the active soundness chain.  The remaining references to
`cert.U_dec_prob` in `Liveness.lean` (lines 365, 871, 1522) are
all in *comments* tracking the gap-2 conditional Borel-Cantelli
plan, not in active proof bodies.

**To eliminate the sorry** (future work, deferred to 8.5b-δ-followup
or a framework PR), pick one of:

  (a) Open `Liveness.lean` and weaken `U_dec_prob` to a disjunct
      form mirroring `U_dec_det` and `V_super_fair`:

      ```lean
      U_dec_prob : ∀ k : ℝ≥0, ∃ p : ℝ≥0, 0 < p ∧
        ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
          i ∈ F.fair_actions → Inv s → ¬ terminated s → V s ≤ k →
          (p ≤ ∑' s' : σ, ... (if U s' < U s then 1 else 0)) ∨
          (∀ s' ∈ ((spec.actions i).effect s h).support,
            ∃ j ∈ F.fair_actions, (spec.actions j).gate s')
      ```

      AVSS would then dispatch via `Or.inr` on the corrupt-fire
      branch using `avssFairActionEnabled_at_non_terminated`,
      mirroring the existing `V_super_fair` / `U_dec_det` cert
      dispatch.

  (b) Split `FairASTCertificate` into a smaller "BC cert" that
      omits `U_dec_prob` (the BC running-min route doesn't need
      it).  AVSS would target the smaller structure, eliminating
      the field entirely.

Either is a `Liveness.lean` framework adaptation outside this PR's
scope (the worker brief held `Leslie/Prob/Liveness.lean` off-limits
for this δ phase).

## Sorry inventory (2 total, unchanged)

| Line | Theorem | Status |
|---|---|---|
| ~4877 (avssCert U_dec_prob) | structural blocker | **vestigial** under BC route — see above |
| ~7996 | `coalitionView_corrupt_factors_AE` | 8.5c — statement weakening + `coalitionTrivialView` cascade |

## Path forward

```
8.5b-α [✅ 11 sorries]
  ↓
8.5b-β [✅ 13 sorries; cert dispatch + lemma + queue WF]
  ↓
8.5b-γ [✅ 4 sorries; -9 net; freshness, actionGate_iff, simSyncInv]
  ↓
8.5b-γ-followup [✅ 3 sorries; -1 net; C5/C7 stuck-case dispatch]
  ↓
8.5b-γ-followup-2 [✅ 2 sorries; -1 net; F4 via per-pair tokens]
  ↓
8.5b-δ [✅ this checkpoint, 2 sorries; 0 net but route switched]
        Switched termination route to BC running-min.
        U_dec_prob sorry now vestigial (BC route doesn't consume).
  ↓
8.5b-δ-followup (NEW): close U_dec_prob via Liveness.lean disjunct
        weakening (route-A above).  ~80-120 LOC framework PR.
  ↓
8.5c — `coalitionView_corrupt_factors_AE` weakening +
       `coalitionTrivialView` cascade through secrecy chain.
  ↓
8.5b-ε — verify all axiom-clean, finalize MODEL_NOTES.
```

## Axiom hygiene status

`avssCert` still depends transitively on `sorryAx` via the vestigial
`U_dec_prob` sorry.  The cert's `avssTermInv`, `corruptLocalInv`,
`avssQueueWfInv`, `avssFreshInv`, `avssFlowInv` clauses, the
`V_super` / `V_super_fair` / `U_dec_det` cert dispatches, and the
`avssFairActionEnabled_at_non_terminated` lemma are all axiom-clean.
After 8.5b-δ-followup (close the vestigial sorry) + 8.5c
(`coalitionView_corrupt_factors_AE`), the cert and downstream
termination theorems become axiom-clean.

The **soundness path** for `avss_termination_AS_fair` /
`avss_termination_AS_fair_traj` /
`avss_termination_AS_fair_rushing` flows through
`pi_n_AST_fair_with_progress_bc_of_running_min_drops` and
`pi_infty_zero_fair`, neither of which consumes `cert.U_dec_prob`.

## How to pick up

1. Read this file + `PHASE-8-5b-PLAN.md` (in this worktree).
2. `lake build Leslie.Prob.Index` — confirm green at 2699 jobs.
3. For 8.5b-δ-followup: open `Leslie/Prob/Liveness.lean` and weaken
   `FairASTCertificate.U_dec_prob` to a disjunct form (Or.inr
   "another fair action enabled at post").  Update `avssCert` to
   dispatch via `Or.inr` on the corrupt-fire branch.
4. For 8.5c: introduce `coalitionTrivialView`, weaken
   `coalitionView_corrupt_factors_AE` statement, cascade through
   ~6 secrecy-chain consumers.
