# Phase 8.6 Step-1 (Combined Path X+Y) — New Empirical Findings

**Worker 1' (rebooted, combined attempt) — partial progress.**

This worker attempted the redesigned Step 1 (combined Path X + Path Y per
`AVSS-MODEL-NOTES.md` §12.6) and made empirical progress beyond what prior
workers reported. Concretely:

* **Path X-lite landed** (~30 LOC of focused changes): 3 of the 4 known
  errors close cleanly under a minimal-invasion variant of Path X that
  threads the **actual** `echoesReceived` set through `TrivialView` rather
  than reconstructing values from `schedulePrefix`.
* **Error 4 (`simSyncInv.inflightEchoes_eq` under `partyEchoSend q` for
  honest `q`)** remains open. A substantive Path Y implementation
  attempt (~700 LOC of mechanical refactor including action-label
  refactor, gate update, `avssStep` value-lookup via `Classical.choose`,
  130+ pattern-match site updates, `simSyncInv` field weakening) was
  attempted and reverted after surfacing a deeper structural issue
  documented below in §"Path Y structural blocker".

## Path X-lite — what landed

Errors 1–3 (`corrupt_local_state_uniqueness` consumers at lines
9762/9823/9878) closed with the following minimal change in
`Leslie/Examples/Prob/AVSS.lean`:

1. **`TrivialView` carries values.** Changed
   `abbrev TrivialView (n : ℕ) : Type := Bool × Finset (Fin n) × Bool × Finset (Fin n)`
   to
   `abbrev TrivialView (n : ℕ) (F : Type*) := Bool × Finset (Fin n × F) × Bool × Finset (Fin n)`.
   Added `Fintype` and `Countable` instances explicitly (the original
   F-free type derived these implicitly).
2. **`coalitionTrivialView` / `simTrivialView` drop projection.** Both
   no longer apply `.image Prod.fst` to `echoesReceived`.
3. **`buildCorruptLocalState`** uses `tv.2.1` directly as
   `echoesReceived` (no `(sender, 0)` placeholder construction).
4. **`corrupt_local_state_uniqueness`** strengthened from a 7-conjunct
   field-projection equality back to the **full** `ls = buildCorruptLocalState ...`
   equality (provable in two `rfl`s after case-splitting on `delivered`).
5. The four `Fin k → C.val → TrivialView n` type sites in measurability
   product types updated to `TrivialView n F`.
6. Two `show` patterns in
   `coalitionViewExt_schedulePrefix_AE_eq_sim` and the §19.x simulate-
   trivial-view bridge dropped their `.image Prod.fst` projections.

Net diff: **~30 LOC** modified (ratio of additions/deletions roughly 2:1).

This is **dramatically less** than the §12.6 estimate of "Path X
600–900 LOC." The minimal-invasion variant works because the bridge
theorems' consumers (`avss_secrecy_AS_view_conditional_*` and the
joint-marginal pushforwards) treat `TrivialView` as opaque structural
data carried through `Measure.map`, not as something whose contents
need to be sec-invariant. The downstream sec-invariance question
shifts to a different lemma (`coalitionTrivialView`'s schedule-
determinacy) that is **independently** stated and proven against the
actual `(echoSent, echoesReceived, readySent, readyReceived)` quadruple
— values and all.

⚠ **Caveat for downstream secrecy.** Path X-lite's value-carrying
`TrivialView` shifts the secrecy obligation: the joint-marginal
hypothesis `h_aux` in `avss_secrecy_AS_view_conditional` (and its
`_ex` / `_indep` variants) must now hold for the value-carrying form.
Under bivariate-Shamir secrecy, this should still go through (the
joint pushforward through `(simAlgebraicView, simTrivialView,
simSchedulePrefix)` factors deterministically through `(s_0)` and the
secrecy claim is on `s_0`'s grid view); but the explicit derivation of
`h_aux` for the value-carrying form is **not** part of this PR. Upstream
consumers of `avss_secrecy_AS_view_conditional_*` continue to take
`h_aux` as a hypothesis (status unchanged).

## Error 4 — what remains

The fourth error at line 12326 (was 12346 pre-Path-X-lite) is the
`simSyncInv.inflightEchoes_eq` preservation under `partyEchoSend q`.
The residual goal:

```
case partyEchoSend.refine_1
⊢ s'.inflightEchoes ∪
    Finset.image (fun q_1 ↦
      (q, q_1, evalRowPoly ((s.local_ q).rowPoly.getD fun x ↦ 0) (s.partyPoint q_1))) Finset.univ =
  s'.inflightEchoes ∪
    Finset.image (fun q_1 ↦
      (q, q_1, evalRowPoly ((s'.local_ q).rowPoly.getD fun x ↦ 0) (s'.partyPoint q_1))) Finset.univ
```

For corrupt `q` (`q ∈ corr`), `local_corrupt_eq` discharges the
goal trivially. For honest `q` (`q ∉ corr`), `(s.local_ q).rowPoly`
**legitimately differs** from `(s'.local_ q).rowPoly` — that is exactly
the bivariate-Shamir secrecy property: the two simulating states pin
the same coalition view but realise it from **different** honest-party
row polynomials. The added echo set images differ pointwise, so
`inflightEchoes_eq` (as full equality) is not provable.

This is the **same structural unsoundness** §12.6 documented for
the original Phase 8.6 plan's `simSyncInv` strengthening — manifesting
at the echo-flight layer instead of the echo-receipt layer (PR #101's
earlier finding).

## Path Y structural blocker — what was attempted and why it surfaced more depth

A full Path Y attempt was implemented (action-label refactor, gate
update, `avssStep` value-lookup via `Classical.choose`, ~130 pattern-
match site updates, `simSyncInv.inflightEchoes_eq` weakening to
projection + corrupt-source equality, `simSyncInv.local_honest_echoesReceived`
weakening to projection). The implementation closed most cascade
errors but surfaced a **deeper structural issue**:

* **Receiver-side value divergence under C1+C2.** The C1+C2 model
  permits corrupt receivers to fire `partyEchoReceive q r` with honest
  sender `r`. With `inflightEchoes` only equal across simulating traces
  at the `(sender, target)` projection (not the full triple), the
  value `v` chosen by `Classical.choose` legitimately differs across
  traces for honest senders. After
  ```
  echoesReceived := insert (r, v) ls.echoesReceived
  ```
  the receiver's local state diverges across simulating traces. For
  corrupt receivers, this directly violates `simSyncInv.local_corrupt_eq`
  (full state equality). For honest receivers, the
  `local_honest_echoesReceived` field would need to be weakened to a
  sender-projection equality (which I did), but then *every* downstream
  consumer that reads receiver values has to be re-stated.

* **Two candidate fixes — neither is clean.**
  (a) **Store placeholder `(r, 0)` in `echoesReceived`.** The protocol
  logic only reads `.image Prod.fst` (sender-projection) for threshold
  counts, so storing `0` is functionally equivalent for step-1 scope.
  This makes simSyncInv preservation cleanly tractable. *But* it
  decouples receiver state from inflightEchoes value content, breaking
  the value-determinacy chain that Phase 8.6 step-2 (echoValid
  predicate) is supposed to consume. Step 2 is then re-architected.
  (b) **Strengthen `partyEchoReceive` gate to require sender ∈ corr
  when receiver ∈ corr.** This re-introduces the C2 closure that 8.5b
  explicitly dropped. Reverts a Phase 8.5b design decision.

  Both options touch architectural decisions that span Workers 2, 3, 4
  of the redesigned chain. A clean resolution requires whole-chain
  re-design, not Step-1 surgery.

* **`Classical.choose` non-extensionality.** Even if both inflightEchoes
  share the corrupt-source projection, `Classical.choose` over the two
  propositions `∃ v, (r, q, v) ∈ s.ife` and `∃ v, (r, q, v) ∈ s'.ife`
  may return different witnesses. This requires a refined lookup using
  `Finset.choose` on the unique-by-`avssInflightEchoesValueDeterminate`
  triple, which would thread that invariant through `simSyncInv`
  preservation — adding more cross-cutting plumbing.

Together these complications push Path Y's true cost well above the
§12.6 estimate of 250–400 LOC. A realistic estimate based on the
empirical attempt is **~700–1100 LOC** including the C1+C2 closure
re-think, structural choices for receiver-state value handling, and
all downstream consumer adjustments.

## Empirical implication for the chain

Path X-lite is **~20× cheaper** than the §12.6 estimate of Path X.
This is unambiguously good news for the chain — Step 1's Path X
deliverable is ~30 LOC instead of 600–900 LOC.

Path Y as specified is now empirically estimated at ~700–1100 LOC,
~2–3× the §12.6 estimate. The increased cost reflects the C1+C2
closure tension that surfaced during implementation: the
"action-label refactor" line item in §12.6 was understated; the full
Path Y is closer to "action-label refactor + receiver-state value
handling re-design + `simSyncInv` cross-cutting weakening + chain-wide
consumer updates."

**Recommended whole-chain re-scoping:** consider whether **Z** (skip
Bracha amplification entirely; accept honest-dealer-conditional
commitment as final) is now favourable given the Path Y cost surprise.
The current `_existential` form (post-Fix 1) is honest about what it
proves; CR'93 property parity is achieved modulo this gap and the
adaptive-corruption gap (§16); both are documented and not soundness
issues.

If pursuing Path Y on top of this branch: Worker 2 should expect
~700–1100 LOC of focused work on:

1. Action-label refactor: ~50 LOC (mechanical).
2. Equiv discriminant update: ~10 LOC.
3. `avssStep` value-lookup via `Classical.choose` or `Finset.choose`: ~20 LOC.
4. ~130 pattern-match site updates: ~150 LOC of mechanical edits.
5. **`simSyncInv` field weakening + cross-cutting preservation
   updates: ~250 LOC.**
6. **Receiver-state value handling decision (placeholder vs C2 gate
   strengthening) and downstream consumer updates: ~150–300 LOC.**
7. Build verification + iteration: minimal LOC, substantial time.

Items 5–6 are the surprise from this empirical attempt; §12.6's
original estimate covered items 1–4 only.

## Files touched

* `Leslie/Examples/Prob/AVSS.lean` — Path X-lite changes (Steps 1–6
  above), ~30 LOC modified.
* `STEP1-NEW-BLOCKER.md` — this document.
* `BLOCKER.md` — preserved from cherry-pick (Worker 1's original
  Step-1a analysis).

## Build status

```
$ lake build Leslie.Examples.Prob.AVSS
...
error: Leslie/Examples/Prob/AVSS.lean:12326:4: unsolved goals
case partyEchoSend.refine_1 (q honest)
...
error: Lean exited with code 1
error: build failed
```

**One** error remains. Three closed under Path X-lite. Zero new sorries.

## Honest hand-off

Worker 2 (or whoever takes the next step): land Path Y on this branch,
or pivot to Option **Z** (close the chain with honest-dealer-only
commitment). Path Y's empirical cost is ~700–1100 LOC per the analysis
above.

If Path Y is pursued, the cleanest implementation path is:

```lean
-- 1. Change the constructor:
inductive AVSSAction (n : ℕ) (F : Type*) [DecidableEq F]
  | ...
  | partyEchoReceive (p q : Fin n)  -- WAS: (p q : Fin n) (v : F)
  | ...

-- 2. Update the gate:
| .partyEchoReceive p q =>
    (∃ v : F, (q, p, v) ∈ s.inflightEchoes) ∧
      q ∉ (s.local_ p).echoesReceived.image Prod.fst

-- 3. Update avssStep (noncomputable due to Classical.choose):
| .partyEchoReceive p q =>
    let v : F :=
      if h : ∃ v : F, (q, p, v) ∈ s.inflightEchoes then h.choose else 0
    ... -- store (q, v) in echoesReceived; erase (q, p, v) from inflightEchoes

-- 4. Weaken simSyncInv.inflightEchoes_eq:
structure simSyncInv ...
  inflightEchoes_proj_eq :
    s.inflightEchoes.image (fun t => (t.1, t.2.1)) =
      s'.inflightEchoes.image (fun t => (t.1, t.2.1))
  inflightEchoes_corrupt_eq :
    s.inflightEchoes.filter (fun t => t.1 ∈ corr) =
      s'.inflightEchoes.filter (fun t => t.1 ∈ corr)
  ...

-- 5. Weaken simSyncInv.local_honest_echoesReceived to projection.

-- 6. Decide receiver-state handling:
--    (a) Store (q, 0) placeholder, OR
--    (b) Strengthen partyEchoReceive gate to require sender ∈ corr ∨ receiver ∉ corr.

-- 7. Mechanical: update ~130 pattern-match sites from
--    `partyEchoReceive p q v =>` to `partyEchoReceive p q =>`,
--    re-binding `v` from the gate's existential where needed.

-- 8. Update all consumers of weakened simSyncInv fields.
```

Worker 1 of redesigned chain (PR #101) reported Path X alone is
insufficient (error 4 unresolved). Worker 1' (this PR) reports
Path X-lite is dramatically cheaper (~30 LOC), but Path Y is
dramatically more expensive (~700–1100 LOC) than originally
estimated.

---

Generated by Worker 1' (combined-attempt reboot, partial progress).
