# Phase 8.5d Checkpoint — α + α-followup landed

**Branch**: `feat/randomized-leslie-m3-avss-phase8-5d-alpha`
**Base**: PR #67 (8.5b-ε, end of 8.5b chain — 0 sorries baseline).
**Build state**: green at `lake build Leslie.Prob.Index` with **2** sorries in AVSS.lean (down from 9 in 8.5d-α handoff).
**Sorry count**: **2** (both deferred to 8.5d-γ termination re-scope; documented below).

## Followup status (2 PRs squashed)

The original Phase 8.5d-α PR opened with 9 sorries; this branch's later commits closed 7 of them as part of α-followup work. Closures:

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
| `avssStep_preserves_simSyncInv` (dealerShareTo) | ⚠ Closed except for one sub-sorry (see below). |
| `corrupt_fire_post_not_terminated` (dealerShareTo case) | ⚠ Deferred to 8.5d-γ. |

## Remaining sorries (2 total, both deferred to 8.5d-γ)

### 1. `corrupt_fire_post_not_terminated` — dealerShareTo p with p corrupt

When the adversary fires `dealerShareTo p` for a corrupt p, only `inflightCorruptDeliveries` grows — neither `inflightDeliveries`/`inflightEchoes`/`inflightReady` nor any local field changes. So `terminated` could hold post-step (if it held pre-step), and we cannot derive contradiction.

The proper resolution is **Phase 8.5d-γ**: re-scope termination to a consistent-quorum hypothesis, which obviates this branch.

### 2. `avssStep_preserves_simSyncInv` — dealerMessages_corrupt_eq at slot r

`dealerShareTo r` writes `dealerMessages r` with payload computed from `s.partyPoint` and `s.coeffs`. The `simSyncInv` couples `s.partyPoint = s'.partyPoint` (via `partyPoint_eq`) but does NOT track `s.coeffs = s'.coeffs`. The corrupt-side `dealerMessages_corrupt_eq` field needs the new payload at slot `r` to agree on both simulators when `r ∈ corr`, which requires the bivariate coefficients to agree.

Resolution path:
- Extend `simSyncInv` with a `coeffs_eq` field (8.5d-α-followup-2), or
- Refactor `rowPolyOfDealer` to use a witness coefficient grid that's coupled in `simSyncInv` (8.5d-β when `s.coeffs` migrates to μ₀).

For now, the sorry is named `TODO Phase 8.5d-α-followup-2` (or 8.5d-β depending on closure approach).

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
