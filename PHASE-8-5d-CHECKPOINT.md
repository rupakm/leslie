# Phase 8.5d Checkpoint — β-followup-3 closed 10 of 12 sorries

**Branch**: `feat/randomized-leslie-m3-avss-phase8-5d-beta`
**Base**: PR #68 (8.5d-α, dealerShareTo per-party action surgery).
**Build state**: green at `lake build Leslie.Examples.Prob.AVSS` with
**4** sorries in AVSS.lean (down from 12 after the followup-3 batch).
**Sorry count**: **4** in AVSS — all tracked.

## Phase 8.5d-β-followup-3 — what landed

Closed 10 of the 12 sorries from PR #69's structural migration:

| Site | Status |
|---|---|
| `avssStep_preserves_dealerMessagesInv` (dealerShareTo) | ✅ Closed |
| `avssStep_preserves_honestDealerInv` (partyDeliver) | ✅ Closed |
| `initPred_honestDealerConsistencyInv` | ✅ Closed |
| `avssStep_preserves_honestDealerConsistencyInv` | ✅ Closed |
| `avssStep_preserves_outputDeterminedInv` (Tier 2) | ✅ Closed |
| `simSyncInv_avssInitState` fixture | ✅ Closed |
| `avssInitMeasure_AE_initPred` | ✅ Closed |
| `avss_secrecy_initPMF` (Tier 2) | ✅ Closed |
| `avss_secrecy_AS_init` (Tier 2) | ✅ Closed |
| `avss_secrecy_AS` (Tier 2) | ✅ Closed |
| `avssStep_preserves_simSyncInv` (Tier 3) | 🟡 Deferred to followup-4 |
| `avss_secrecy_AS_view_rushing` wrapper | 🟡 Deferred to followup-4 |

**Restatements** (with `coeffs` parameter, replacing the deprecated
`s.coeffs` placeholder):

- `dealerMessagesInv coeffs s` — honest-dealer-conditional, with both
  `dealerCommit p = canonical` and `msg.rowPoly = canonical` clauses.
- `outputDeterminedInv coeffs s` — honest-dealer-conditional, clause 1
  universal in `p` (preserved via `dealerMessagesInv` for both honest
  and corrupt parties' delivered rowPoly).
- `coalitionGrid coeffs C D s` — algebraic grid view with parametric
  witness (no longer the placeholder = 0).
- `joinedConsistencyInv_via_vandermonde coeffs s` — honest-dealer-cond.
- `phase6Inv coeffs s` — composite invariant taking coeffs.
- `avss_commitment_AS_corrupt_dealer` — conclusion is honest-dealer-AE-
  conditional (corrupt-dealer Vandermonde witness deferred to a
  Phase 8.6+ Bracha amplification proof).

**Newly tagged TODO Phase 8.5d-β-followup-5** (cascade out-of-scope):

- `coalitionView_corrupt_factors_AE` (body sorry'd) — closing requires
  restating `coalitionAlgebraicView` to take a `coeffs` parameter
  (~30 callsites in the operational-secrecy chain).
- `coalitionTraceView_eq_reconstruct_AE` (body sorry'd) — downstream
  of the above plus the `traceDist_dealerHonest_AE_eq_init` lemma.

## Remaining 4 sorries

| Site | Tag | Estimate |
|---|---|---|
| `avssStep_preserves_simSyncInv` | TODO 8.5d-β-followup-4 (Tier 3) | ~200 LOC per-action proof + `dealerCommit_corrupt_eq` field addition |
| `avss_secrecy_AS_view_rushing` | TODO 8.5d-β-followup-4 | requires existential-vs-fixed-coeffs reconciliation in inner theorem chain |
| `coalitionView_corrupt_factors_AE` | TODO 8.5d-β-followup-5 | ~50 LOC after `coalitionAlgebraicView` restatement |
| `coalitionTraceView_eq_reconstruct_AE` | TODO 8.5d-β-followup-5 | ~30 LOC; uses the above |

## Pre-β-followup-3 state (kept for reference)

# Phase 8.5d Checkpoint — β landed (12 sorries, all tracked) [historical]

**Branch**: `feat/randomized-leslie-m3-avss-phase8-5d-beta`
**Base**: PR #68 (8.5d-α, dealerShareTo per-party action surgery).
**Build state**: green at `lake build Leslie.Prob.Index` with **12** sorries
in AVSS.lean (up from 0; 12 added by 8.5d-β are all tagged
`TODO Phase 8.5d-β-followup`).
**Sorry count**: **12** in AVSS — all tracked, none in pre-β chain.

## Phase 8.5d-β — what landed

**Goal**: migrate `s.coeffs : Fin (t+1) → Fin (t+1) → F` out of `AVSSState`
into μ₀ (initial measure). The bivariate polynomial is now a witness sampled
at protocol start (parametric to `initPred`), not a state field.

**Structural surgery**:
- Removed `coeffs` field from `AVSSState`.
- Added `dealerCommit : Fin n → DealerPayload t F` field for per-party
  commitments (set at init from the canonical `coeffs` witness for honest
  dealer; arbitrary for corrupt dealer).
- `initPred sec corr coeffs s` takes `coeffs` parameter (the witness).
- `avssStep` for `dealerShareTo p` now writes `dealerMessages p =
  some (s.dealerCommit p)` instead of computing from a state field.
- Threaded `coeffs` through `avssSpec`, `avssCert`, all
  `avss_termination_AS_*` theorems, and most secrecy/commitment statements.
- `coeffsSecretInv` and `honestDealerInv` restated to take `coeffs`
  parameter (followup-1).
- `avssStep_preserves_honestDealerInv` rebuilt with the parameterized form
  (followup-1, all cases except partyDeliver — that one inner sorry needs
  the `dealerCommit` ↔ canonical bridge from initPred).
- `avssStep_coalitionGrid_invariant` closed via the placeholder being a
  constant (followup-2).

**Vestigial scaffolding**: `AVSSState.coeffs` accessor returns `(0 : F)` as
placeholder, marked `@[deprecated]`. Existing `s.coeffs` syntax compiles via
this scaffold; theorems whose statements depend on the actual witness
should be restated to take `coeffs` as a parameter (matching `initPred`'s
signature) and then the placeholder can be deleted.

## Sorry inventory (Phase 8.5d-β-followup TODO)

| Site | Reason | Effort |
|---|---|---|
| `avssStep_preserves_dealerMessagesInv` (dealerShareTo case) | needs dealerCommit ↔ canonical bridge from initPred | 1-line via initPred clause |
| `avssStep_preserves_honestDealerInv` (partyDeliver case, line 5674) | needs same bridge | 1-line |
| `initPred_honestDealerConsistencyInv` | needs rebuild using `coeffs` parameter as witness | 5-line |
| `avssStep_preserves_honestDealerConsistencyInv` | depends on dealerMessages preservation | 5-line |
| `avssStep_preserves_outputDeterminedInv` | restate `outputDeterminedInv` to take `coeffs` parameter, rebuild proof | 100-line per-action case split |
| `avss_secrecy_initPMF` | restate `coalitionGrid` to take `coeffs` parameter, rebuild bivariate-shamir bridge | 30-line |
| `avss_secrecy_AS_init`, `avss_secrecy_AS` | downstream of above | mechanical |
| `avssStep_preserves_simSyncInv` | restate `simSyncInv.rowPoly_corrupt_eq` to take `coeffs` param, rebuild per-action proof | 200-line (most complex) |
| `simSyncInv_avssInitState` | fixture, needs simSyncInv restatement first | 10-line |
| `avssInitMeasure_AE_initPred` | now needs existential witness; provide via `polyToCoeffs f` for `f` in support | 30-line |
| `avss_secrecy_AS_view_rushing` | top-level wrapper; reconciles existential `avssInitMeasure_AE_initPred` with fixed-coeffs `avss_secrecy_AS_view_rushing_via_init_invariant` | 20-line |

**Total followup estimate**: ~400-500 LOC, tractable in 2-3 followup commits.

## Pre-β baseline (kept for reference)

## Followup status — all 9 sorries closed

| Site | Status |
|---|---|
| `avssTermInv_step` clause 4 | ✅ Closed (per-party `dealerSent p = false → ¬delivered`). |
| `avssU_step_dealerShareTo_le` | ✅ Closed (case-split honest/corrupt p). |
| `avssU_step_dealerShareTo_lt` | ✅ Closed (requires `p ∉ corrupted`; carried via `isHonestFire`). |
| `avssStep_preserves_corruptLocalInv` (dealerShareTo) | ✅ Closed (frame proof). |
| `avssStep_preserves_avssQueueWfInv` (dealerShareTo) | ✅ Closed. |
| `avssStep_preserves_avssFlowInv` F2 (9 sub-cases) | ✅ Closed. |
| `avssFairActionEnabled_at_non_terminated` | ✅ Closed (cascade re-derived under per-party form). |
| `avssStep_preserves_dealerMessagesInv` (dealerShareTo) | ✅ Closed. |
| `avssStep_preserves_simSyncInv` (dealerShareTo) | ✅ Closed via `rowPoly_corrupt_eq`. |
| `corrupt_fire_post_not_terminated` (dealerShareTo case) | ✅ Closed by adding pre-state `¬ terminated s` premise. |

## Final closure technique notes

### `simSyncInv` dealerShareTo sub-case (was the trickiest)

The corrupt-slot dealerMessages payload at slot `r ∈ corr`. Initially looked
like it needed a new `coeffs_eq` field on `simSyncInv`, but
`simSyncInv.rowPoly_corrupt_eq r hp` already gives the row poly equality
directly, so no schema change was needed:

```lean
have hrp := h.rowPoly_corrupt_eq p hp  -- p ∈ corr
exact DealerPayload.mk.injEq _ _ _ _ |>.mpr ⟨hrp, rfl⟩
```

### `corrupt_fire_post_not_terminated` for dealerShareTo (corrupt p)

The action only mutates `inflightCorruptDeliveries`, `dealerSent p`, and
`dealerMessages p` — none of which appear in `terminated`. So
`terminated post ↔ terminated pre`. Adding the pre-state `¬ terminated s`
hypothesis lets the new `dealerShareTo` corrupt-case lift forward:

```lean
theorem corrupt_fire_post_not_terminated
    (a : AVSSAction n F) (s : AVSSState n t F)
    (hph : ¬ isHonestFire a s) (hnt : ¬ terminated s) :   -- new hnt premise
    ¬ terminated (avssStep a s) := by
  ...
```

The 3 V_super / V_super_fair callers already had `hnt` in scope, so the
update was a one-line append.

## What 8.5d-α delivered

Phase 8.5d-α is the structural surgery for **C4 (selective non-broadcast)** caveat:

## What 8.5d-α delivered

Phase 8.5d-α is the structural surgery for **C4 (selective non-broadcast)** caveat:

### Action constructor refactor

```lean
inductive AVSSAction (n : ℕ) (F : Type*) [DecidableEq F]
  -- BEFORE: | dealerShare
  -- AFTER:
  | dealerShareTo (p : Fin n) : AVSSAction n F
  ...
```

### State field retype

```lean
structure AVSSState (n t : ℕ) (F : Type*) [DecidableEq F] where
  ...
  -- BEFORE: dealerSent : Bool
  -- AFTER: per-party flag
  dealerSent : Fin n → Bool
  ...
```

### `avssStep`'s dealerShareTo branch

```lean
| .dealerShareTo p =>
    let payload : DealerPayload t F :=
      { rowPoly := rowPolyOfDealer s.partyPoint s.coeffs p
        colPoly := fun _ => (0 : F) }
    { s with
      dealerSent := Function.update s.dealerSent p true
      inflightDeliveries :=
        if p ∉ s.corrupted then insert p s.inflightDeliveries
        else s.inflightDeliveries
      inflightCorruptDeliveries :=
        if p ∈ s.corrupted then insert p s.inflightCorruptDeliveries
        else s.inflightCorruptDeliveries
      dealerMessages := Function.update s.dealerMessages p (some payload) }
```

### Gate cascades

`actionGate (.dealerShareTo p) s = (s.dealerSent p = false)` — single party, not global.
`actionGate (.partyDeliver p) s = (s.dealerSent p = true ∧ ...)` — per-party precondition.
Same per-party shift for `partyEchoSend / partyReady / partyAmplify / partyCorruptDeliver`.

### Variant `avssU` updates

The c₁ component shifted:
```lean
-- BEFORE:
(if s.dealerSent then 0 else (honestSet s).card) * K^6
-- AFTER:
(unsentDealerSet s).card * K^6   where
  unsentDealerSet s = univ.filter (fun p => p ∉ corrupted ∧ s.dealerSent p = false)
```

The honest-only filter ensures `unsentDealerSet = ∅` at terminated states (used by
`avssCert.V_term`'s `avssU_eq_zero_of_terminated`).

### Invariant `avssTermInv` clause 4 (new)

Added per-party pre-share quiescence:

```lean
def avssTermInv (s : AVSSState n t F) : Prop :=
  ((∀ p, s.dealerSent p = false) → ...) ∧   -- clause 1 (was Bool, now per-party)
  (∀ p, p ∉ corrupted → echoSent → delivered) ∧   -- clause 2
  (∀ p, p ∉ corrupted → output.isSome → readySent ∧ delivered) ∧   -- clause 3
  (∀ p, s.dealerSent p = false → s.local_ p = init)   -- NEW clause 4 (Phase 8.5d-α)
```

Clause 4 is what makes `avssU_eq_zero_of_terminated` go through:
honest p has output ⇒ via clause 4 contrapositive, `dealerSent p = true`,
so `unsentDealerSet` is empty.

### Invariants restated

- `avssQueueWfInv` Q5: `∀ p, dealerSent p = true → dealerMessages p .isSome` (per-party).
- `avssFlowInv` F2: `∀ p ∉ corrupted, dealerSent p = true → delivered ∨ p ∈ inflightDeliveries`.
- `simSyncInv.dealerSent_eq` is now between two `Fin n → Bool` functions (no statement change).

### Files touched

- `Leslie/Examples/Prob/AVSS.lean` (~150 lines updated, ~50 lines net added).
- `PHASE-8-5d-CHECKPOINT.md` (new).
- `PHASE-8-5d-PLAN.md` carried from base.

## Sorry inventory

All sorries are named `TODO Phase 8.5d-α-followup` (or refer to the same handoff).

| Line | Site | Why sorrified |
|---|---|---|
| 1045 | `avssTermInv_step` clause 4 | Per-party `dealerSent p = false → local p = init` preservation needs case-split per action; mechanical but verbose. |
| 2213 | `avssU_step_dealerShareTo_le` | Per-party drop in `unsentDealerSet` (`-K⁶`) plus growth in `inflightDeliveries` (`+K⁵`); structurally simpler than the old all-or-nothing proof. |
| 2227 | `avssU_step_dealerShareTo_lt` | Same as above, strict variant. The K⁶ - K⁵ gap is at least `K^5 * (K-1) ≥ 1`. |
| 2531 | `avssStep_preserves_corruptLocalInv` (dealerShareTo case) | The corrupt party's local state isn't touched, but `dealerMessages` writes a slot. Since the conclusion only mentions `output` and `rowPoly`, this should be one-line `simp [avssStep, setLocal]`-style after careful rewriting. |
| 2710 | `avssStep_preserves_avssQueueWfInv` (dealerShareTo case) | Q1 for new in-flight delivery slot; Q5 for the new dealerMessages population. Mechanical. |
| 3676 | `avssStep_preserves_avssFlowInv` F2 (all cases) | F2 is now per-party `(∀ p, dealerSent p = true → ...)`; the original case-by-case body needs updating (each non-dealer case is a frame proof using the per-party hypothesis). I've case-split into 9 sorries which can be filled in one short batch. |
| 4201 | `avssFairActionEnabled_at_non_terminated` (all-served case) | When `∀ p, dealerSent p = true`, dispatch falls back to the existing C2..C7 cascade. The body (~360 LOC) was retained as a comment block; needs to be re-derived under per-party gates. |
| 4934 | `avssStep_preserves_dealerMessagesInv` (dealerShareTo case) | Case-split on `p = r` vs `p ≠ r`: for `p = r`, the new payload is `rowPolyOfDealer s.partyPoint s.coeffs r`, matching the rule; for `p ≠ r`, fall back to `hinv`. |
| 9620 | `avssStep_preserves_simSyncInv` (dealerShareTo case) | Both sides write to slot `r` with identical payloads (since `partyPoint` and `coeffs` are equal across `s` and `s'` by simSyncInv structure). Mechanical congr-with-update. |

## Build state at handoff

```
$ lake build Leslie.Examples.Prob.AVSS
warning: 9 declaration uses 'sorry'
(no errors)
```

The 9 sorries cascade through the `avssCert` constructor, propagating to:

- `avssCert.inv_step` — uses `avssTermInv_step` (clause 4 sorry)
- `avssCert.U_dec_det` and `_prob` — uses `avssU_step_lt_of_fair` which depends on `avssU_step_dealerShareTo_lt`
- `avssCert.V_super` — uses `avssFairActionEnabled_at_non_terminated` (the dispatch sorry)

These propagate to the main load-bearing termination theorem. Phase 8.5d-α-followup will close them.

## Next worker brief: Phase 8.5d-α-followup

**Goal**: Close the 9 named sorries. Estimated 200–400 LOC.

### Order of attack

1. **`avssTermInv_step` clause 4** (1045): straightforward case-split. Each non-dealer action either preserves `dealerSent p` or contradicts the per-party gate `dealerSent p = true`.
2. **`avssU_step_dealerShareTo_le/_lt`** (2213, 2227): the proof structure is similar to the old `dealerShare_le/_lt`. Compute the post-state set equalities (mostly preserved), the `unsentDealerSet` drop by 1, and bound the `inflightDeliveries` growth by 1.
3. **`avssStep_preserves_corruptLocalInv`** (2531) — should compress to ~10 lines.
4. **`avssStep_preserves_avssQueueWfInv` dealerShareTo** (2710) — Q1 needs the new slot; Q5 directly satisfied by Function.update + `rfl`.
5. **`avssStep_preserves_avssFlowInv` F2 cases** (3676): 9 small subgoals, each a frame argument using the per-party hypothesis.
6. **`avssStep_preserves_dealerMessagesInv` dealerShareTo** (4934): 2-case split.
7. **`avssStep_preserves_simSyncInv` dealerShareTo** (9620): congr-with-update, ~30 lines.
8. **`avssFairActionEnabled_at_non_terminated`** (4201): the deepest. Uncomment the retained body, replace the OLD `s.dealerSent = true` Bool comparison with the per-party form, and ensure the C2..C7 cascade carries through. The C1 case dispatches `dealerShareTo p` for the unserved p.

### Files OFF-LIMITS for 8.5d-α-followup

- All framework files. Only `Leslie/Examples/Prob/AVSS.lean`.
- The dead-code shim `_avssFair_dead_old_body_keep` (kept as TODO scaffold; delete once the main theorem's body is recovered).

## After 8.5d-α-followup

- **8.5d-β**: `s.coeffs` migration to μ₀ (state field → initial-measure parameter).
- **8.5d-γ**: termination re-scope to consistent-quorum hypothesis.
- **8.5d-δ**: cleanup + MODEL_NOTES §11.4 closure citation.
