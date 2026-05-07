# Phase 8.6 Step 1 — STOPPED & REPORTING (`STEP1-BLOCKED.md`)

Worker 1 of the redesigned Phase 8.6 chain (post-PR #98 / §12.6 of
`AVSS-MODEL-NOTES.md`). This file documents a structural blocker that
prevents Step 1 from landing as scoped: **Path X (reconstruction-side
threading of `schedulePrefix` through `buildCorruptLocalState`) closes
errors 1–3 but does NOT close error 4**. Error 4 lives in
`simSyncInv.inflightEchoes_eq` preservation under the
`partyEchoSend` action — outside the bridge that Path X targets — and
its discharge requires Path Y (action-label refactor) or an equivalent
weakening of `simSyncInv`. The original Step-1 plan in
`WORKER_TASK.md` only scoped Path X.

The conclusion mirrors `STEP2-BLOCKED.md` from PR #95 (Worker 2 of the
prior chain), but is reached freshly here against the post-#98 main.
The cherry-pick experiment (3 commits from `origin/feature/phase8-6`
onto `feature/8.6` forked from current main) was performed locally and
verified to reproduce **exactly the same 4 compile errors** (lines
9782 / 9843 / 9898 / 12346) Worker 1's original PR #88 left and that
Worker 2's rebase (PR #95) reproduced. The cherry-picked working
branch is preserved locally as `feature/8.6-with-experiment` for
forensics; this branch (`feature/8.6-blocked`) is reset to
`origin/main` so the docs-only finding lands cleanly.

## TL;DR

  * **Errors 1–3** (lines 9782 / 9843 / 9898): consumers of
    `corrupt_local_state_uniqueness` need full state equality, but
    Worker 1c's intentional weakening (the lemma now returns a
    7-conjunct projected equality with `echoesReceived.image Prod.fst`)
    breaks the consumers' `Measure.map_congr` glue. **Closable via
    Path X** as scoped in `WORKER_TASK.md`.
  * **Error 4** (line 12346): `simSyncInv.inflightEchoes_eq`
    preservation under `partyEchoSend q`. After Step 1's expansion,
    `partyEchoSend q` adds
    `Finset.image (fun q1 ↦ (q, q1, evalRowPoly ((s.local_ q).rowPoly.getD ...) (s.partyPoint q1))) Finset.univ`.
    For honest `q`, `(s.local_ q).rowPoly` legitimately differs across
    the two simulating traces (different secrets `c, c'`), so the
    images differ value-wise; `inflightEchoes_eq` as full set equality
    cannot be preserved. Pinning honest `rowPoly` would force
    `c = c'` and trivialise secrecy (the structural unsoundness §12.6
    documents). **NOT closable via Path X.**

Path X is genuinely necessary for errors 1–3 and genuinely insufficient
for error 4. Closing all four requires Path X **and** a complementary
intervention for error 4 (Path Y as described in §12.6 / Worker 2's
`STEP2-BLOCKED.md`).

## Cherry-pick experiment performed

```bash
cd /Users/rupak/.worktrees/leslie/8.6
ln -sf /Users/rupak/Code/tla/leslie/.lake .lake
git fetch origin feature/phase8-6
git cherry-pick c398d1e 7675e53 b3eb7a7
```

Single conflict at the `partyEchoReceive q r v` simSyncInv preservation
case (HEAD's post-#98 `partyEchoReceive q r` vs the cherry-picked
`partyEchoReceive q r v` plus the deprecated `rowPoly_corrupt_eq`
field). Resolved by keeping the value-augmented action label and
dropping the deprecated field (matching Worker 2's resolution in PR
#95, since `rowPoly_corrupt_eq` was removed by post-#98 `simSyncInv`
slimming and never reintroduced).

Build state after cherry-pick (`lake build Leslie.Examples.Prob.AVSS`):

```
error: Leslie/Examples/Prob/AVSS.lean:9782:2:  Type mismatch (corrupt_local_state_uniqueness consumer #1)
error: Leslie/Examples/Prob/AVSS.lean:9843:2:  Type mismatch (corrupt_local_state_uniqueness consumer #2)
error: Leslie/Examples/Prob/AVSS.lean:9898:2:  Type mismatch (corrupt_local_state_uniqueness consumer #3)
error: Leslie/Examples/Prob/AVSS.lean:12346:4: unsolved goals (simSyncInv.inflightEchoes_eq under partyEchoSend)
```

Identical lines and identical residual-goal shapes to PR #88's
handoff and PR #95's rebase. No drift since #98 merged.

## Why Path X closes errors 1–3 but not error 4

### Errors 1–3 — `corrupt_local_state_uniqueness` consumers

The three consumer theorems
(`coalitionTraceView_eq_reconstruct_AE{,_ex,_indep}`, lines 9716 /
9799 / 9855) have the same shape:

```
goal:  (ω i.val).1.local_ p.val =
       reconstructCoalitionTraceView (...) i p
```

Currently `corrupt_local_state_uniqueness` returns a 7-conjunct
projected equality (Worker 1c's weakening because full equality is
false post-Step 1: `echoesReceived` carries values that the trivial
view's `(q, 0)` placeholder cannot reconstruct). The consumers want
full equality.

**Path X discharge.** Thread `schedulePrefix` through
`buildCorruptLocalState` and `reconstructCoalitionTraceView`; for each
echo cell `(q, p, v) ∈ (s.local_ p).echoesReceived`, recover `v`
deterministically:

  * **Corrupt sender `q`**: `v` agrees across simulating traces by
    `simSyncInv.local_corrupt_eq` (`(s.local_ q) = (s'.local_ q)`)
    plus `avssInflightEchoesValueDeterminate` value-pinning.
  * **Honest sender `q`**: `v = evalRowPoly ((s.local_ q).rowPoly.getD ...) (s.partyPoint p)`,
    deterministically computable from the schedule prefix
    (`partyEchoReceive q p v` action labels carry `v` directly, so
    the schedule prefix encodes the value at the moment of receipt).

After threading, `corrupt_local_state_uniqueness` returns the original
full state equality and the three consumers compose cleanly with
`Measure.map_congr`. Estimated cost (per §12.6 / Worker 2's
`STEP2-BLOCKED.md` Path X line item): **~600–900 LOC**.

### Error 4 — `simSyncInv.inflightEchoes_eq` under `partyEchoSend`

Goal at `partyEchoSend q.refine_1` (line 12346, after the existing
`simp only [avssStep, h.inflightEchoes_eq, h.corrupted_eq]`):

```
s'.inflightEchoes ∪
    Finset.image (fun q1 ↦ (q, q1,
      evalRowPoly ((s.local_ q).rowPoly.getD ...) (s.partyPoint q1)))
      Finset.univ
  =
s'.inflightEchoes ∪
    Finset.image (fun q1 ↦ (q, q1,
      evalRowPoly ((s'.local_ q).rowPoly.getD ...) (s'.partyPoint q1)))
      Finset.univ
```

`s.partyPoint = s'.partyPoint` by `simSyncInv.partyPoint_eq`. The
remaining gap is `(s.local_ q).rowPoly = (s'.local_ q).rowPoly` for
*honest* `q`. The `actionGate` of `partyEchoSend q` requires only
`delivered = true ∧ echoSent = false ∧ dealerSent q = true` — not
`q ∈ corrupted` — so honest `q` legitimately fires `partyEchoSend`,
and at that moment `(s.local_ q).rowPoly = some (s.dealerMessages q .rowPoly)`
encodes the secret-dependent row poly. Across the two simulating
traces (instantiated by `simSyncInv_avssInitState` with
`h_rp : ∀ p ∈ corr, ...` — only corrupt rowPoly equality), honest
`q`'s rowPoly differs by design.

**Path X is structurally orthogonal to this preservation goal.** Path
X reshapes `buildCorruptLocalState` / `reconstructCoalitionTraceView`
(consumed downstream of `simSyncInv`); it does not touch
`avssStep_preserves_simSyncInv`. The preservation goal is between two
arbitrary `simSyncInv`-related states `s, s'` independent of any
simulation chain.

**What the discharge requires.** Either:

  1. **Path Y** (per §12.6 redesign options table — “action-label
     refactor”). Drop `(v : F)` from `AVSSAction.partyEchoReceive`'s
     label; weaken `simSyncInv.inflightEchoes_eq` to project on
     `(sender, receiver)` pairs (`Finset (Fin n × Fin n)`); make
     `avssStep`'s `partyEchoReceive p q s` look up the unique `v'`
     from `inflightEchoes` via
     `avssInflightEchoesValueDeterminate`. The image of
     `partyEchoSend q` projects to
     `Finset.image (fun q1 ↦ (q, q1)) Finset.univ` — independent of
     `rowPoly`, hence preserved across honest `q`'s simulation
     pairing. Cost: **~250–400 LOC**.

  2. **Restructure the cross-trace bridging layer.** Replace
     `simSyncInv` (which currently must hold *pointwise* across two
     simulating traces) with a weaker view-equivalence that does not
     require pinning `inflightEchoes`. The current secrecy chain
     consumes `simSyncInv` via
     `simAlgebraicView_simSchedulePrefix_eq_of_simSyncInv` (line
     12790) and `avssSimulateTrace_simSyncInv` (line 12713); both
     would need re-architecting. Significantly more invasive than
     Path Y; falls outside the Step 1 budget and likely outside the
     entire Phase 8.6 chain.

  3. **Strengthen `partyEchoSend`'s `actionGate` to require
     `q ∈ corrupted`.** Operationally invalid — honest parties must
     echo for the protocol to make progress.

Of these, **only Path Y is in budget**. Worker 2's analysis (PR #95
`STEP2-BLOCKED.md`) reached the same conclusion independently: errors
1–3 want Path X, error 4 wants Path Y, and the §12.6 recommendation is
**Path X+Y combined** (~850–1300 LOC for sub-deliverable B alone).

## Estimated cost of X+Y combined sub-deliverable B

Per §12.6 / Worker 2's `STEP2-BLOCKED.md`:

  * Path X: ~600–900 LOC (reconstruction-side threading).
  * Path Y: ~250–400 LOC (action-label refactor + `simSyncInv`
    weakening).

**Combined: ~850–1300 LOC.** Sub-deliverable A (echo type expansion,
the cherry-pick) is ~1086 LOC. **Total Step 1 (sub-A + sub-B
combined): ~1936–2386 LOC**, slightly above `WORKER_TASK.md`'s
1700–2000 LOC budget envelope (~1700–2400 LOC if we stretch the upper
bound).

This is feasible in one PR if we accept the ceiling; it's also a
reasonable subdivision into Worker 1a (sub-A only, ~1086 LOC) +
Worker 1b (sub-B = X+Y, ~850–1300 LOC), per the `WORKER_TASK.md`
fallback explicitly anticipating this split.

## Recommendation

Per `WORKER_TASK.md` fallback:

> If the chain plan turns out to be unsound at Step 1 (e.g., Path X
> also runs into structural issues), STOP and write a finding to a
> `STEP1-BLOCKED.md` in the worktree.  Don't churn.  Don't introduce
> sorries.

**Stopping at the rebase-clean baseline.** No code is shipped to
`feature/8.6` (the cherry-pick experiment is preserved on
`feature/8.6-with-experiment` for forensics; this branch
`feature/8.6-blocked` is the docs-only finding off `origin/main`). No
sorries introduced. No regression to current main.

### Suggested next steps

  1. **Worker 1' (re-scoped, recommended)**. Combine sub-A
     (cherry-pick + rebase-conflict resolution) with **Path X+Y**
     for sub-B. Single PR, ~1936–2386 LOC. Title: `feat(M3 AVSS Phase
     8.6 step-1): echo type expansion + Path X reconstruction +
     Path Y action-label refactor`.

  2. **Workers 1a + 1b (split)**. Worker 1a ships sub-A only (the
     cherry-pick, ~1086 LOC, leaving the 4 errors as documented).
     Worker 1b ships sub-B = X+Y (~850–1300 LOC, closing the 4
     errors). The `WORKER_TASK.md` fallback explicitly authorises
     this split.

  3. **Re-scope Step 1 to Path Y only, defer Path X to Step 2/3**.
     Path Y closes error 4 cheaply (~250–400 LOC) and reduces the
     `corrupt_local_state_uniqueness` weakening's blast radius
     (since `inflightEchoes` and `echoesReceived` no longer carry
     value-dependent shape across `simSyncInv`). The 3
     `corrupt_local_state_uniqueness` consumers still need
     reshaping; Step 2's `echoValid` or Step 3's `bivariateAlignedInv`
     could subsume that work. **Risk**: relocating Path X to Step 2/3
     may push complexity into the `bivariateAlignedInv` design, which
     §12.6 has not yet detailed.

Worker 1' (option 1) is the cleanest because it lands the full
echo-type-expansion infrastructure with all 4 errors closed in one
self-consistent PR, leaving Step 2's `echoValid` predicate and
Step 3's `bivariateAlignedInv` as forward-looking cryptographic
content rather than residual Step 1 cleanup.

## Files

  * `STEP1-BLOCKED.md` (this file).

No code changes to `Leslie/Examples/Prob/AVSS.lean` on this branch.
The cherry-pick experiment (with the 4 reproduced errors) is on the
local branch `feature/8.6-with-experiment`; cherry-pick sources are
on `origin/feature/phase8-6` (PR #88, preserved per §12.6).

## Verification

  * `git log --oneline origin/main..HEAD` shows 1 commit (this docs
    finding).
  * `lake build Leslie.Examples.Prob.AVSS` exits 0 on this branch
    (no regression from `origin/main`).
  * No sorries introduced (`grep -nE 'sorry'
    Leslie/Examples/Prob/AVSS.lean` returns only doc-comment
    matches, identical to `origin/main`).

## Bibliographic pointer

  * §12.6 of `Leslie/Examples/Prob/AVSS-MODEL-NOTES.md` — Phase 8.6
    redesign findings (post-PR #95). Documents Paths X / Y / Z and
    the X+Y recommendation.
  * `STEP2-BLOCKED.md` on `origin/feature/phase8-6-step2` — Worker 2's
    structural analysis (PR #95). Reaches the same X+Y recommendation
    independently from a fresh investigation against the prior main.
  * `STEP2-HANDOFF.md` on `origin/feature/phase8-6` — Worker 1's
    handoff (PR #88). Predates §12.6's structural diagnosis; its
    proposed `local_honest_rowPoly_eq` field on `simSyncInv` is the
    cause of the trivialisation pitfall §12.6 corrects.
