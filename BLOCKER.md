# Phase 8.6 step-1 — structural blocker (BLOCKER.md)

This worktree was provisioned for "Phase 8.6 step-1: model surgery on the
echo type to carry sender + value" (Worker 1 of a 4-step chain).  This file
documents a structural blocker that surfaced during the attempt and
recommends a subdivision so Worker 1b can finish the surgery.

The current commit on this branch reverts `Leslie/Examples/Prob/AVSS.lean`
to its main-branch state.  The build is green at the start of the
follow-up worker's session.  No sorries, no axiom additions, no broken
proofs are introduced by this PR.

## Summary

* **Attempted change.**  Migrate `AVSSLocalState.echoesReceived` from
  `Finset (Fin n)` to `Finset (Fin n × F)`, and `AVSSState.inflightEchoes`
  from `Finset (Fin n × Fin n)` to `Finset (Fin n × Fin n × F)`, threading
  the echoed value through `partyEchoSend` (broadcast value
  `evalRowPoly rp (s.partyPoint q)` for each receiver `q`) and
  `partyEchoReceive p q v` (gate `(q, p, v) ∈ inflightEchoes`).
* **Outcome of attempted patch.**  ~440 LOC of changes compile syntactically
  but fail ~62 proof obligations downstream.  The remaining failures
  cluster around three preservation invariants
  (`avssQueueWfInv`, `avssFreshInv`, `avssFlowInv`) that were stated in
  terms of `(q, p) ∈ inflightEchoes` and need rephrasing.
* **Fundamental blocker.**  The `avssQueueWfInv.Q2` clause as restated
  (`∀ q p v, (q, p, v) ∈ inflightEchoes → q ∉ echoesReceived.image Prod.fst`)
  is not preserved by `partyEchoReceive p q v` without an *additional*
  uniqueness invariant `inflightEchoesUnique`.  Without uniqueness, the
  case `p = q ∧ qq = r` admits a counterexample where another `(r, q, v')`
  with `v' ≠ v` survives the erase, and after the insertion of `(r, v)` into
  `echoesReceived`, the freshly-inserted `r` is in
  `echoesReceived.image Prod.fst` — so Q2 fails.
* **Recommended subdivision.**  Split Step 1 into Step 1a (this PR — analysis
  only, no code change) and Step 1b (the surgery proper, with the additional
  uniqueness invariant).  Step 1b is well-scoped (≈700 LOC, single file)
  but should not be conflated with the original Step 1 estimate.

## What was attempted (preserved here as guidance for Worker 1b)

The attempt followed the WORKER_TASK.md plan literally:

1. `AVSSLocalState.echoesReceived : Finset (Fin n) → Finset (Fin n × F)` —
   straightforward, all 9 fields of `AVSSLocalState.init` plus the
   `Fintype` instance updated.
2. `AVSSState.inflightEchoes : Finset (Fin n × Fin n) → Finset (Fin n × Fin n × F)` —
   straightforward, plus `Fintype` instance, plus `inflightEchoes_card_le`
   bound rescaled by `Fintype.card F`.
3. `AVSSAction.partyEchoReceive (p q : Fin n)` →
   `(p q : Fin n) (v : F)`.  Required `(v : F)` argument adds a third
   summand `Fin n × Fin n × F` to the `Fintype` equiv (was
   `Fin n × Fin n`).  `avssFair` gets `partyEchoReceive _ _ _ => True`.
4. `avssStep` cases:
   * `partyEchoSend p`: emit
     `(p, q, evalRowPoly rp (s.partyPoint q))` for every `q ∈ Finset.univ`,
     where `rp = (s.local_ p).rowPoly.getD (fun _ => 0)`.
   * `partyEchoReceive p q v`: insert `(q, v)` into
     `(s.local_ p).echoesReceived`; erase `(q, p, v)` from
     `inflightEchoes`.
5. `actionGate`:
   * `partyEchoReceive p q v`: gate becomes
     `(q, p, v) ∈ s.inflightEchoes ∧ q ∉ (s.local_ p).echoesReceived.image Prod.fst`.
   * `partyReady p`: threshold becomes
     `((s.local_ p).echoesReceived.image Prod.fst).card ≥ n - t`.
6. `avssU_le_bound`: constant rescales from
   `(7 * n + 7) * K^6` to `(7 * n + 7 + Fintype.card F) * K^6` to
   accommodate `inflightEchoes.card ≤ Fintype.card F * K`.
7. Most of the `cases a with | partyEchoReceive p q => ...` proof bodies
   were updated to `| partyEchoReceive p q v => ...` via `replace_all`
   on the case patterns, plus `(.partyEchoReceive p q)` →
   `(.partyEchoReceive p q v)` for inner expressions.
8. `avssU_step_partyEchoReceive_lt` was rewritten with the `(v : F)`
   parameter; its proof closes after threading `v` through the
   `Finset.card_erase_of_mem` argument.

Remaining work (estimated ~150-300 LOC) clusters around:

* `avssStep_preserves_avssQueueWfInv` (Q2 case): see structural blocker
  below.
* `avssStep_preserves_avssFreshInv` (Q6 image, Q8 quantifies over `v`):
  rephrase the four clauses; preservation cases need the value
  threaded through.
* `avssStep_preserves_avssFlowInv` (F3): rephrase
  `q ∈ p.echoesReceived ∨ (q, p) ∈ inflightEchoes`
  to `q ∈ p.echoesReceived.image Prod.fst ∨ ∃ v, (q, p, v) ∈ inflightEchoes`.
* `avssFairActionEnabled_at_non_terminated`: lines 5197 / 5217 / 5299
  pattern-match `⟨⟨q, p⟩, hqp_in⟩`; needs `⟨⟨q, p, v⟩, hqp_in⟩` and the
  partyEchoReceive enables-witness `hwf.2.1 q p v hqp_in`.  The
  partyReady-stuck case at line 5255-5273 needs `hh_sub` and
  `h_echoes_ge` rephrased to use `.image Prod.fst`.
* `simSyncInv` preservation cases for `partyEchoReceive`: bound `v`
  in the case match; the `(q, p) ∈ inflightEchoes` membership equality
  via `h.inflightEchoes_eq` is unchanged at the field-equality level
  but the membership predicate needs the triple form.
* §17.x consumers (Phase 6.3 `corruptViewFactorsThroughGrid`,
  §17.6 / §17.7, §19.x rushing simulation): these touch `echoesReceived`
  and `inflightEchoes` only via `simSyncInv` field-equalities and the
  `R.view` projection, both of which carry over with no semantic change
  once the `simSyncInv` proof is repaired.
* `avssCert`'s `V_init_bdd` constant rescales; the existing call site
  takes `(7 * n + 7) * (lexBase n) ^ 6` and just becomes
  `(7 * n + 7 + Fintype.card F) * (lexBase n) ^ 6`.

The attempt produced a `git diff --stat` of ≈270 insertions / ≈170 deletions
— well below the 500-LOC fallback threshold for Step 1, so the
substantively-correct portion of the work is recoverable from this
session's transcript by Worker 1b.

## The structural blocker — `avssQueueWfInv.Q2` preservation

The intended new Q2 clause:
```
(∀ q p v, (q, p, v) ∈ s.inflightEchoes →
    q ∉ (s.local_ p).echoesReceived.image Prod.fst) ∧
```
fails to be preserved by `avssStep (.partyEchoReceive q r v) s` in the
sub-case `p = q ∧ qq = r`:

* Pre-state has the gate witness `(r, q, v) ∈ s.inflightEchoes` and
  `r ∉ (s.local_ q).echoesReceived.image Prod.fst` (the gate's freshness
  conjunct).
* Post-state: `inflightEchoes = pre.ife.erase (r, q, v)`,
  `(s.local_ q).echoesReceived = insert (r, v) pre.echoesReceived`, so
  `post.echoesReceived.image Prod.fst = insert r pre.image`.
* Suppose another `(r, q, v')` with `v' ≠ v` is in `pre.ife` (this
  preimage admits such a configuration unless an additional invariant
  rules it out).  Then `(r, q, v')` survives `erase` and is in
  `post.ife`.  For `qq = r, p = q, vv = v'`:
  `(qq, p, vv) ∈ post.ife` but `qq = r ∈ post.image` — so Q2 fails.

In the current model the protocol's `partyEchoSend r` is single-shot
(gated by `r.echoSent = false`, which flips `true` after firing), so
**operationally** there can be at most one `(r, q, *)` triple in flight
at a time.  But that is an **invariant-level** fact, not a type-level
guarantee.  Q2 as restated is therefore preserved *only* in conjunction
with an additional uniqueness clause:
```
(∀ q p v v', (q, p, v) ∈ s.inflightEchoes →
    (q, p, v') ∈ s.inflightEchoes → v = v')
```
or, equivalently, the value-determinacy clause
```
(∀ q p v, (q, p, v) ∈ s.inflightEchoes →
    v = evalRowPoly ((s.local_ q).rowPoly.getD (fun _ => 0))
                    (s.partyPoint p))
```

Adding either clause to `avssQueueWfInv` (or splitting it into a fresh
`avssInflightEchoesUniqueInv`) re-enables the Q2 proof.  Preservation of
the new clause is mechanical for every action (only `partyEchoSend r`
extends `inflightEchoes`, and pre's `r.echoSent = false` together with
`avssFreshInv.Q8` rules out any pre-existing `(r, *, *)` token, so the
post-state's `(r, q, v_rq)` triples are unique by construction).

## Recommended Step 1 subdivision

* **Step 1b (next worker / next session).**  Land the type surgery in a
  single PR.  Concretely:
  1. Carry over the type/structure changes documented above.
  2. Add an `avssInflightEchoesUniqueInv` (or extend `avssQueueWfInv` by
     a 5th clause) capturing
     `(∀ q p v v', (q, p, v) ∈ ife → (q, p, v') ∈ ife → v = v')`.
  3. Discharge preservation of the new uniqueness clause for every
     action (mostly by `rfl` / `Finset.mem_erase`-style frame; only
     `partyEchoSend` needs the `Function.injective` argument over the
     image).
  4. Discharge `avssQueueWfInv.Q2` for `partyEchoReceive` using the
     new uniqueness clause.
  5. Repair the eight `cases`-rewrite proofs that thread the value
     through (`partyDeliver`, `partyCorruptDeliver`, `partyEchoSend`,
     `partyReady`, `partyAmplify`, `partyReceiveReady`, `partyOutput`
     of `avssStep_preserves_avssQueueWfInv`).
  6. Repair the consumer at `avssFairActionEnabled_at_non_terminated`
     (lines 5197 / 5217 / 5299) and the partyReady-stuck case at
     5255–5273.
  7. Repair `simSyncInv`'s `partyEchoReceive` case (a single
     case-arm in `actionGate_iff` and `avssStep_preserves_simSyncInv`).

  Estimated single-file effort: 700–900 LOC, single self-consistent
  commit.  The fallback threshold for Step 1 was 500 LOC, but Step 1b
  is in the 700-900 LOC range because of the uniqueness invariant and
  the proof-cascade through six preservation theorems.  The
  subdivision into Step 1a (this analysis) + Step 1b (the surgery
  with the uniqueness fix) keeps each PR's blast radius reviewable.

* **Step 2 (Worker 2, unchanged).**  Echo validation predicate at
  `partyEchoReceive`.  No surgery needed beyond what Step 1b already
  threads.

* **Step 3 (Worker 3, unchanged).**  `bivariateAlignedInv` state invariant.

* **Step 4 (Worker 4, unchanged).**  Rewire commitment headlines, drop
  the honest-dealer guards on
  `avss_commitment_AS_existential{,_rushing,_randomised,_rushing_randomised}`.

## What this PR contains

* **No code changes to `Leslie/Examples/Prob/AVSS.lean`.**  The file
  is byte-for-byte identical to its `main` state.
* **`BLOCKER.md`** (this file) with the analysis above.

The build remains green at the start of Worker 1b's session.  Build:

```
lake build Leslie.Examples.Prob.AVSS
```

returns exit 0 with 0 sorries and unchanged axiom hygiene.

## Handoff

**Worker 1b: pick up Step 1 with the uniqueness-invariant approach
described above.**  The structural diagnosis is in this file; Worker 1b
should not need to re-derive the issue.  The recommended approach:

1. Add `avssInflightEchoesUniqueInv` (or 5th clause of `avssQueueWfInv`).
2. Carry over the type surgery in one self-consistent commit.
3. Rebuild and resolve the cascade with the uniqueness clause in
   hand for the `partyEchoReceive` Q2 case.
4. Open a single PR titled
   `feat(M3 AVSS Phase 8.6 step-1b): echo type expansion + uniqueness invariant`.

Phases 2 / 3 / 4 of the chain (Workers 2, 3, 4) remain unchanged.
