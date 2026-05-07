# Phase 8.6 Step 2 — Handoff (STEP2-HANDOFF.md)

This file is the explicit handoff from Worker 1 (Steps 1a/1b/1c, PR #88)
to Worker 2 (Step 2 — echo validation predicate).  Worker 1's PR is
*intentionally not closed* at the build-green / 0-sorries bar: the 4
residual errors are structural symptoms that Step 2 was always scoped
to address.  Worker 2 should pick up this branch (`feature/phase8-6`)
and continue.

## TL;DR for Worker 2

* **Branch:** `feature/phase8-6` (commits `c398d1e` → `7675e53` → `b3eb7a7`).
* **PR:** #88 (cumulative; analysis + Step 1b/1c surgery).
* **State:** ~1100 LOC of value-augmented AVSS surgery in
  `Leslie/Examples/Prob/AVSS.lean`.  4 residual errors, all in §17/§19
  secrecy abstractions.  No sorries from Worker 1; the `'declaration
  uses sorry'` warnings are Lean's auto-fill on compile failures —
  closing the 4 errors closes them too.
* **Your job:** introduce an `echoValid` predicate (§A below), thread
  it through the inflight-echoes invariant (§B), restate the 4 broken
  theorems against the new invariant (§C).  Closes PR #88, lets
  Worker 3 start on `bivariateAlignedInv`.
* **Estimated size:** 400-700 LOC.  Single self-consistent commit.

## What's compiling cleanly (don't touch)

The bulk of Step 1's surgery is already in place and proves through:

* Type expansion: `AVSSLocalState.echoesReceived : Finset (Fin n × F)`,
  `AVSSState.inflightEchoes : Finset (Fin n × Fin n × F)`.
* `AVSSAction.partyEchoReceive (p q : Fin n) (v : F)` + Fintype
  instance + `avssFair`.
* `avssStep` for `partyEchoSend` / `partyEchoReceive` with canonical
  CR'93 echo content.
* `actionGate` updates (`(q, p, v) ∈ inflightEchoes`, `q ∉ image
  Prod.fst`, `((s.local_ p).echoesReceived.image Prod.fst).card ≥ n - t`).
* `avssU_le_bound` rescaled by `Fintype.card F`.
* `avssU_step_partyEchoReceive_lt` re-proved.
* `avssQueueWfInv.Q2`, `avssFreshInv.Q6/Q8`, `avssFlowInv.F3` restated
  and preserved through all 9 actions.  `partyEchoReceive` Q2 case
  uses the new `avssInflightEchoesValueDeterminate` invariant for
  uniqueness.
* `avssInflightEchoesValueDeterminate` (Phase 8.6 step-1 added
  invariant): every `(q, p, v) ∈ inflightEchoes` has `v` pinned to
  `evalRowPoly ((s.local_ q).rowPoly.getD (fun _ => 0)) (s.partyPoint p)`.
  Preservation theorem (`avssStep_preserves_avssInflightEchoesValueDeterminate`)
  threads through all 9 actions.
* `corruptLocalInv` extended with `(echoSent = true → delivered = true)`
  for corrupt parties; preservation re-proved.
* `avssCert.Inv` grown to a 6-conjunct (`avssInflightEchoesValueDeterminate`
  appended); `inv_init` / `inv_step` / `V_super` / `V_super_fair` /
  `U_dec_det` re-coupled.
* `corrupt_fire_post_not_terminated`: partyEchoSend witness re-derived
  with the canonical-value entry.
* `avssFairActionEnabled_at_non_terminated` C4/C5/C7 dispatches now
  destructure the (sender, receiver, value) triple.
* §17 / §19 honest-side projections (`coalitionTrivialView`,
  `simTrivialView`, `coalitionTrivialView_AE_eq_traceProj`,
  §19.6 partyEchoSend `simSyncInv` — for corrupt q only): all
  use `.image Prod.fst` against the new echoesReceived type.

## What's NOT compiling (your job)

Four errors, all in §17/§19, all share the same root cause: with echo
values introduced, the secrecy proof's existing
`TrivialView`/`buildCorruptLocalState` reconstruction is
information-lossy unless the values are pinned to a canonical form.

### 1. `simSyncInv.inflightEchoes_eq` preservation under
       `partyEchoSend` (line 12452 — `avssStep_preserves_simSyncInv`,
       `partyEchoSend q` case, `refine_1` placeholder)

```
⊢ s'.inflightEchoes ∪
    Finset.image (fun q_1 ↦ (q, q_1,
      evalRowPoly ((s.local_ q).rowPoly.getD fun x ↦ 0) (s.partyPoint q_1)))
      Finset.univ =
  s'.inflightEchoes ∪
    Finset.image (fun q_1 ↦ (q, q_1,
      evalRowPoly ((s'.local_ q).rowPoly.getD fun x ↦ 0) (s'.partyPoint q_1)))
      Finset.univ
```

For corrupt `q`, `local_corrupt_eq q` makes the rowPolys equal and
the goal closes via `simp + h.partyPoint_eq + h.local_corrupt_eq`.
For honest `q`, `(s.local_ q).rowPoly` and `(s'.local_ q).rowPoly`
are *not* pinned to be equal in `simSyncInv` — they encode different
secrets in the secrecy proof's canonical use.

**Step 2's resolution.**  Define `echoValid` and add it as a
`simSyncInv` field for honest `q`:

```lean
def echoValid (s : AVSSState n t F) (q p : Fin n) (v : F) : Prop :=
  ∃ rp, (s.local_ q).rowPoly = some rp ∧
        v = evalRowPoly rp (s.partyPoint p)
```

Then strengthen `simSyncInv` with `local_honest_rowPoly_eq` *only on
delivered honest parties*: when `(s.local_ q).delivered = true`, both
sides have the same rowPoly content (because `dealerCommit` agrees on
the corrupt-coalition-visible structure under
`coalitionRowPolyAlignedInv`).  Discharge the partyEchoSend case from
the gate's `(s.local_ q).delivered = true`.

### 2. `coalitionTraceView_eq_reconstruct` family (lines 9878 / 9939
       / 9994; theorems
       `coalitionTraceView_eq_reconstruct_AE`,
       `coalitionTraceView_eq_reconstruct_AE_ex`,
       `coalitionTraceView_eq_reconstruct_AE_indep`)

The shared shape:

```
goal:  (ω i.val).1.local_ p.val =
       reconstructCoalitionTraceView (...) i p
```

`reconstructCoalitionTraceView` calls `buildCorruptLocalState` which
produces `echoesReceived = (sender_ids).image (fun q => (q, 0))`.
Real corrupt `p`'s `echoesReceived` carries CR'93 values, not zeros.
So the equality is *false* in the current form.

**Step 2's resolution.**  Replace the `(q, 0 : F)` placeholder in
`buildCorruptLocalState` with the canonical reconstruction, threading
`coeffs` through:

```lean
def buildCorruptLocalState (coeffs : Fin (t+1) → Fin (t+1) → F)
    (partyPoint : Fin n → F) (rp : Fin (t+1) → F) (tv : TrivialView n)
    (delivered : Bool) (corrupt_p : Fin n) : AVSSLocalState n t F := {
  ...
  echoesReceived := tv.2.1.image
    (fun q => (q, bivEval coeffs (partyPoint q) (partyPoint corrupt_p)))
  ...
}
```

The reconstruction is now exact for honest senders (since their
echoes carry `bivEval coeffs ...` per `avssInflightEchoesValueDeterminate`
+ honest-rowPoly canonicality).  For corrupt senders the value is
schedule-determined; treat as a separate refinement (or pin via
adversary's choice in the `Adversary` view — Worker 3's territory).

Then `corrupt_local_state_uniqueness` returns to the original full
equality (revert Worker 1c's 7-conjunct weakening).  The three
`coalitionTraceView_eq_reconstruct_*` theorems should compile back
through after threading `coeffs` and `partyPoint` into
`reconstructCoalitionTraceView`.

## Concrete sequence (recommended)

### Step 2.1 — `echoValid` predicate + value-determinacy upgrade

1. Define `echoValid` in §1 (next to `evalRowPoly`).
2. Strengthen `avssInflightEchoesValueDeterminate` (already added by
   Worker 1) to also assert `q.delivered = true` for every
   `(q, p, v) ∈ inflightEchoes` (currently it derives this implicitly
   via `getD (fun _ => 0)` semantics; making it explicit saves
   downstream branching).
3. Verify preservation through all 9 actions (most cases are
   already mechanical given Worker 1's framework).

### Step 2.2 — `simSyncInv` honest-rowPoly extension

1. Add field `local_honest_rowPoly_eq : ∀ p, p ∉ corr → (s.local_ p).delivered = true →
                                          (s.local_ p).rowPoly = (s'.local_ p).rowPoly`.
   (Constraint scoped to delivered honest parties — undelivered
   honest parties have `rowPoly = none` on both sides by
   `corruptLocalInv`-analog or `outputDeterminedInv`.)
2. Discharge in `simSyncInv_avssInitState` (vacuous: no honest
   delivered at init).
3. Discharge in every preservation case (mostly frame).  The
   `partyDeliver q` case is the one that lights up the new
   constraint: both sides set `rowPoly := some
   (dealerMessages q .rowPoly)`, and `dealerMessages_corrupt_eq`
   already gives this for corrupt q; for honest q, derive from a
   new `dealerMessages_honest_isSome_eq` field or directly from
   `coalitionRowPolyAlignedInv` if that's threaded.

### Step 2.3 — `buildCorruptLocalState` value reconstruction

1. Thread `coeffs : Fin (t+1) → Fin (t+1) → F` and `partyPoint :
   Fin n → F` (both already in scope at consumer sites) into
   `buildCorruptLocalState`.
2. Replace the `(q, 0 : F)` placeholder with `(q, bivEval coeffs
   (partyPoint q) (partyPoint corrupt_p))`.
3. Restore `corrupt_local_state_uniqueness` to its original full
   equality (revert Worker 1c's 7-conjunct weakening).  The proof
   uses `avssInflightEchoesValueDeterminate` plus the canonical
   `evalRowPoly = bivEval` identity (`evalRowPoly_rowPolyOfDealer`
   in §2).
4. Re-thread `coeffs` / `partyPoint` through `reconstructCoalitionTraceView`
   and the three `coalitionTraceView_eq_reconstruct_*` theorems.

### Step 2.4 — close PR #88

1. Build green: `lake build Leslie.Examples.Prob.AVSS`.
2. 0 sorries (`grep -nE 'sorry' Leslie/Examples/Prob/AVSS.lean`).
3. Axiom-clean: `[propext, Classical.choice, Quot.sound]` (verify via
   `#print axioms` on a few headline theorems).
4. Push and request review.  PR title can change to
   `feat(M3 AVSS Phase 8.6 step-1 + step-2): echo type expansion +
   echo validation predicate`.

## Files

* `Leslie/Examples/Prob/AVSS.lean` — single file you'll modify.
* `Leslie/Examples/Prob/AVSS-MODEL-NOTES.md` — read-only; update §12.1
  row 8.6 status only after you close.
* `BLOCKER.md` — Worker 1's analysis + 1b/1c progress log.  Read for
  context.

## Files NOT to touch

* `Leslie/Prob/*` (framework).
* `Leslie/Examples/Prob/AVSSAbstract.lean` (read-only).
* `Leslie/Examples/Prob/BivariateShamir.lean` (read-only — but the
  algebraic identities you'll cite live there).

## Constraints

* DO NOT pipe `lake build` output (the build hangs when piped).  Use
  foreground or `run_in_background: true` without `2>&1 | tail`.
* 0 sorries at end.  No new axioms / postulates / framework defs.
* Maintain axiom hygiene: `[propext, Classical.choice, Quot.sound]`.

## Headline theorems still take `s.dealerHonest = true →`

Worker 4 will drop these guards.  Do *not* attempt that in Step 2.

## When done

Same shipping protocol as Worker 1 (see WORKER_TASK.md):

```
LEAN4_GUARDRAILS_BYPASS=1 git push origin feature/phase8-6
```

PR title update:

```
feat(M3 AVSS Phase 8.6 step-1+2): echo type expansion + echo validation predicate
```

Then append:

```
phase8-6|<PR URL>|<diff size>|step1+2 done|<date>
```

to `~/.claude/active-sessions.log`.  Worker 3 picks up `bivariateAlignedInv`.
