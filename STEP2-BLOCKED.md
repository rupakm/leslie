# Phase 8.6 Step 2 — STOPPED & REPORTING (STEP2-BLOCKED.md)

Worker 2 of the Phase 8.6 chain.  This file documents why Step 2 as
described in `STEP2-HANDOFF.md` cannot land in a single ~700-LOC commit:
its central recommendation (adding `local_honest_rowPoly_eq` to
`simSyncInv`) is incompatible with the bivariate-Shamir secrecy
pairing that `simSyncInv_avssInitState` is constructed against.

The build currently has the same 4 errors Worker 1 left in `feature/phase8-6`:
3 in `corrupt_local_state_uniqueness` consumers (§17.6 / §17.7) and 1
in `simSyncInv` preservation under `partyEchoSend` (§19.x).

## What Worker 2 actually did

1. **Rebased** `feature/phase8-6-step2` onto current `origin/main`
   (post-#81 / #82 / #89).
   * Single conflict in `Leslie/Examples/Prob/AVSS.lean` at the
     `partyEchoReceive q r` case of `simSyncInv.symm`-adjacent code:
     resolved by dropping `rowPoly_corrupt_eq` (removed by #81 Fix 5) and
     keeping the 3-arg `partyEchoReceive q r v` (Worker 1's echo-value
     expansion).
   * No `s.coeffs` / `avssStep_coeffs_invariant` / `avssSpec_stepKernel_coeffs_AE` /
     `traceDist_coeffs_AE_eq_init` references survived in code (verified
     by `grep` — all matches are inside `--` doc comments).

2. **Verified post-rebase build state**: 4 errors at lines 9782, 9843,
   9898, 12346 — exactly the same structural footprint Worker 1 left
   pre-rebase.

3. **Investigated each error's true scope** before attempting surgery
   (this file).

## Why Step 2's recommended surgery doesn't work

### Error 4 (line 12346 — `simSyncInv.inflightEchoes_eq` preservation under `partyEchoSend q`)

The goal at `refine_1`:

```
s'.inflightEchoes ∪
    Finset.image (fun q_1 ↦ (q, q_1,
      evalRowPoly ((s.local_ q).rowPoly.getD fun x ↦ 0) (s.partyPoint q_1)))
      Finset.univ
  =
s'.inflightEchoes ∪
    Finset.image (fun q_1 ↦ (q, q_1,
      evalRowPoly ((s'.local_ q).rowPoly.getD fun x ↦ 0) (s'.partyPoint q_1)))
      Finset.univ
```

* For corrupt `q`, `local_corrupt_eq` pins `(s.local_ q) = (s'.local_ q)`,
  so the images agree (`partyPoint_eq` handles the partyPoint
  factor) — closes.

* For honest `q`, `(s.local_ q).rowPoly` and `(s'.local_ q).rowPoly`
  are **NOT** pinned to be equal in `simSyncInv` and **CANNOT** be
  pinned without breaking the secrecy proof.

#### Why honest `rowPoly` agreement breaks secrecy

The simulation pairing is constructed via `simSyncInv_avssInitState`
with hypothesis:

```
h_rp : ∀ p ∈ corr,
    rowPolyOfDealer partyPoint c p = rowPolyOfDealer partyPoint c' p
```

That is, the simulation pairs traces where **only corrupt parties' row
polys agree**.  Honest parties' row polys derive from
`(s.dealerCommit p).rowPoly` (set at init from the `c` /  `c'`
witnesses), which differ between the two traces (encoding different
secrets).

Adding the handoff-recommended field

```
local_honest_rowPoly_eq : ∀ p, p ∉ corr →
    (s.local_ p).delivered = true →
    (s.local_ p).rowPoly = (s'.local_ p).rowPoly
```

cascades into needing:

1. `dealerMessages_honest_rowPoly_eq` (since `partyDeliver q` reads
   `(s.dealerMessages q).rowPoly`).
2. `dealerCommit_honest_rowPoly_eq` (since `dealerShareTo q` writes
   `s.dealerCommit q` to `dealerMessages q`).
3. Strengthening `simSyncInv_avssInitState`'s hypothesis to **all**
   parties (not just corrupt), i.e., `∀ p, rowPolyOfDealer partyPoint c p
   = rowPolyOfDealer partyPoint c' p`.

But that hypothesis forces `c = c'` (modulo the polynomial-equality
direction of bivariate Shamir), which means `sec = sec'`, **trivialising
the secrecy claim**.

The handoff's sketch of "discharge from `coalitionRowPolyAlignedInv` if
that's threaded" doesn't survive scrutiny: `coalitionRowPolyAlignedInv`
is a **unary** invariant about a single state, and it only pins
**corrupt** parties' `local_.rowPoly` to `dealerCommit`.  It cannot
relate two states' honest-party row polys.

### Errors 1–3 (lines 9782 / 9843 / 9898 — `corrupt_local_state_uniqueness` type mismatch)

`corrupt_local_state_uniqueness`'s current shape returns a 7-conjunct
projected equality (Worker 1c's intentional weakening — full state
equality fails post-Step 1 because echoesReceived's values are
secret-dependent).  Its three consumers (`coalitionTraceView_eq_reconstruct_AE`,
`_AE_ex`, `_AE_indep`) need the *full* state equality
`(ω i.val).1.local_ p.val = reconstructCoalitionTraceView ...` to compose
with `Measure.map_congr` for the operational-secrecy headline.

The handoff's Path A — refactor `buildCorruptLocalState` to use
`bivEval coeffs (partyPoint q) (partyPoint corrupt_p)` for echo values
— closes the honest-sender case but **leaves corrupt-sender values
unmatched**: corrupt senders' `partyEchoSend` emits `evalRowPoly
((s.local_ q).rowPoly.getD ...)` where the rowPoly is whatever the
adversary installed (NOT canonical bivEval), while the reconstruction
would substitute bivEval.  The handoff acknowledges this in passing
("for corrupt senders the value is schedule-determined; treat as a
separate refinement (or pin via adversary's choice in the `Adversary`
view — Worker 3's territory)") but does not provide a concrete
discharge mechanism.

For *delivered* corrupt senders under
`coalitionRowPolyAlignedInv`, their `rowPoly = some (dealerCommit q
.rowPoly)`, which under honest dealer equals `rowPolyOfDealer
partyPoint coeffs q` — at which point bivEval matches.  But the
**`AE_indep`** variant of the bridge theorem **drops** the honest-dealer
guard.  In the dishonest-dealer regime, `dealerCommit q .rowPoly` is
adversarial and ≠ canonical bivEval.

So Path A:
* works for `_AE` (honest dealer guard present) ✓
* works for `_AE_ex` (honest dealer guard present) ✓
* **fails** for `_AE_indep` (no guard; corrupt dealer + corrupt sender
  values are non-canonical) ✗

The dishonest-dealer secrecy bridge needs a different reconstruction —
likely Worker 3's `bivariateAlignedInv` providing a full canonical
pinning, or a refactor of the bridge to use `dealerCommit`-derived
values rather than `coeffs`-derived values.

## Two viable paths forward (both larger than Step 2's 700-LOC budget)

### Path X (reconstruction-side refactor — recommended)

Refactor `buildCorruptLocalState` and `reconstructCoalitionTraceView` to
take **`schedulePrefix`** (or equivalently the per-step `partyEchoReceive
p q v` history) as an additional input, and reconstruct each
`echoesReceived` cell from the schedule directly.  This keeps full
state equality in `corrupt_local_state_uniqueness` (echoesReceived
matches by definition: the schedule's `partyEchoReceive p q v` actions
are exactly what's in the local state's `echoesReceived` field).

* Eliminates the corrupt-vs-honest sender asymmetry — values come from
  the schedule, not from algebra.
* Honest-dealer guard stays optional for the bridge (works either
  way).
* Cost: thread `schedulePrefix` through ~8 secrecy theorems, refactor
  `buildCorruptLocalState`'s signature, update 3 bridge proofs +
  3 consumers (`avss_secrecy_AS_view_conditional{,_ex,_indep}`).
* Estimated ~600–900 LOC, single file.

### Path Y (action-label refactor — Step 1 partial revert)

Drop `(v : F)` from `AVSSAction.partyEchoReceive`'s label.  Make
`avssStep`'s `partyEchoReceive p q` look up the unique `v'` such that
`(q, p, v') ∈ s.inflightEchoes` (uniqueness from
`avssInflightEchoesValueDeterminate`) and use that.  The `simSyncInv`
gate equivalence is then existential and provable from
`inflightEchoes_eq` projected to sender-receiver pairs.

* Fixes error 4 cleanly.
* Doesn't fix errors 1–3 (those still need Path X for echoesReceived
  reconstruction).
* Cost: change `AVSSAction` definition + Fintype instance + ~30
  case-match sites.
* Estimated ~250–400 LOC, single file.

**Both paths together** would close the 4 errors and deliver the
"echoValid + secrecy bridge value-canonicality" surgery the handoff
described.  Combined estimate: 850–1300 LOC, well above the 700-LOC
budget Worker 2's session was scoped against.

## Recommendation

Per `WORKER_TASK.md` fallback:

> If the 4 compile errors require infrastructure you can't reach (e.g.,
> a structural change that would also touch framework files), STOP and
> report.  Don't introduce sorries.

I am stopping at the rebase-resolved baseline (no Step 2 surgery
attempted; build remains red with the same 4 errors as Worker 1's
final commit, modulo cosmetic differences from the rebase).  I am
**not** introducing sorries.

Suggested next steps:

1. **Worker 2a** (split): Path Y (action-label revert).  ~250–400
   LOC, closes error 4, build still has errors 1–3 but the simSyncInv
   layer is healthy.

2. **Worker 2b**: Path X (reconstruction-side refactor) on top of
   2a.  ~600–900 LOC, closes errors 1–3.

3. **Worker 3** (unchanged): `bivariateAlignedInv`.

4. **Worker 4** (unchanged): drop honest-dealer guards.

OR, alternatively:

1. **Worker 2** (re-scoped to ~1000–1400 LOC): Paths X+Y combined,
   single PR.  Treat as 2× the original Step 2 budget.

## What this PR contains

* `STEP2-BLOCKED.md` (this file).
* The rebase resolution (1 file conflict) on `feature/phase8-6-step2`.

No code changes to `Leslie/Examples/Prob/AVSS.lean` beyond the conflict
resolution that the rebase forced.

## Verification

* `git log --oneline origin/main..HEAD` shows 4 commits: 1 analysis,
  3 step-1 work + 1 docs from Worker 1, all rebased cleanly onto
  current main.
* `lake build Leslie.Examples.Prob.AVSS` exits 1 with the same 4
  errors as before (no regression introduced; no progress made).
* No sorries introduced (`grep -nE 'sorry' Leslie/Examples/Prob/AVSS.lean`
  produces only doc-comment matches, same as `feature/phase8-6`).
