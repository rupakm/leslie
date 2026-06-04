# Leslie_LTS — Known Issues and Design Decisions

## 1. `assumes_fair_wf` — step-aware "fires" semantics

**Status:** Resolved (2026-06-03). The definition uses step-aware
"fires" (label match + real step). There is only one variant.

**The problem (historical):** An earlier version of `assumes_fair_wf`
defined "label l eventually fires" as just `l = e.labels k` — only
checking that the label appears at some position. On a
`valid_exec_stutter` execution (used by `transfers_satisfaction` for
the abstract execution), a τ-stutter position has `e.labels k = τ` and
`e.states k = e.states (k+1)` (no state change). If `τ = .commit
default` (as in IdealBRB), then `.commit default` "fires" at every
stutter position — but no state change occurs.

This broke the `ideal_brb_totality` proof's contradiction argument on
stutter executions: the argument assumes that when commit fires,
`set_up` changes from `none` to `some v`. On a stutter exec, commit
"fires" (label matches) but `set_up` stays `none` (state unchanged).
The contradiction with `h_none_forever` doesn't work because commit
firing didn't actually change anything.

**The fix:** `assumes_fair_wf` (in `Leslie_LTS/Framework/Liveness.lean`)
now defines "fires" as BOTH `l = e.labels k` AND
`sys.step (e.states k) (e.labels k) (e.states (k+1))` — a real step
occurred. The old label-only variant was deleted (commit `b761bfe`).

On `valid_exec` (non-stutter), the step conjunct is free from `hv.2 k`.
On `valid_exec_stutter`, it prevents τ-stutters from counting as
"fired", which was the root cause of the issue.

All callers use the unified definition:
- `ideal_brb_totality`: destructures `⟨j, hj, h_step⟩` from the
  antecedent (the step used to come from `hv.2 (k+j)` separately).
- `ideal_brb_totality_stutter`: same — the step comes from the
  antecedent, not from `hv_stutter.2 k` (which only gives step ∨ stutter).
- `transfers_satisfaction`: `h_abs` and `h_ante_transfer` both use
  the unified `assumes_fair_wf`.

**Files:**
- `Leslie_LTS/Framework/Liveness.lean` — single `assumes_fair_wf` definition
- `Leslie_LTS/Framework/Simulation.lean` — `transfers_satisfaction`
- `Leslie_LTS/Examples/BRB_Liveness.lean` — `ideal_brb_totality`, `ideal_brb_totality_stutter`, `brb_totality`

## 2. Remaining BRB_Liveness sorries (as of 2026-06-03)

**6 sorries**, all protocol-specific (framework is sorry-free):

| Line | What | Category | Status |
|------|------|----------|--------|
| 164 | `brb_fair_deadlock_implies_terminated` | Protocol invariant | FALSE as stated — see §3 |
| 233 | `rank_non_increasing` | Progress measure | Needs real measure |
| 239 | `rank_decreases_on_fair_elision` | Progress measure | Needs real measure |
| 254 | `rank_non_increasing_on_fair_progress` | Progress measure | Needs real measure |
| 272 | `h_fair_reverse` in `fair_deadlock_diverges` | Fair deadlock | FALSE as stated — see §3 |
| 785 | `h_ante_transfer` in `brb_totality` | Transfer | FALSE as stated — see §4 |

Lines 233/239/254 are tied to the placeholder `brb_progress_measure := 0`.
With the placeholder, `brb_rank = False` everywhere — so the rank clauses
are vacuously satisfied and don't block any theorem. They only matter for
producing meaningful abstract witnesses.

## 3. Fair-deadlock chain: soundness issues (2026-06-03)

### `brb_fair_deadlock_implies_terminated` (line 164) is FALSE

**Counterexample**: the initial BRB state (or after `corrupt(sender)`).
At these states `FairDeadlock` holds (only unfair steps like `corrupt` and
`input` are enabled) but all correct procs have `returned = none`.

**Fix**: add a precondition, e.g., `(s.local_ sender).broadcastVal ≠ none`.
At a fair-deadlock where broadcastVal is set, the protocol must have
completed (otherwise some fair send/recv/output would be enabled).

### `h_fair_reverse` (line 272) is FALSE

**Counterexample**: concrete state after `corrupt(sender)`.  Concrete is a
fair-deadlock (only `input` and `corrupt` remain; both unfair).  The
matched abstract state via `sim_rel` has `set_up = none` and `sender ∈
corrupted`, so abstract `commit v` is enabled (OR condition: `¬ isCorrect
sender`) AND fair (`ideal_brb_fair_labels (.commit _) = True`).  But the
concrete has NO fair step → `h_fair_reverse` must produce one and cannot.

**Consequence**: `fair_deadlock_diverges` is unprovable with the current
approach of using `fair_deadlock_lifts`.  At a state where the abstract
has fair-enabled commit but the concrete has no fair steps, `FairlyWeakly-
Diverges abstract s₂` is also false (only one commit possible via
InternalStar, and the resulting state is not a FairDeadlock because output
becomes enabled+fair).

**Impact**: `fair_deadlock_diverges` is a field of `WeakDivPreserving` but
is NOT exercised by `brb_totality` (the `_wd` parameter in
`transfers_leads_to` is unused).  So this sorry does not affect the
concrete totality theorem's soundness.  It DOES affect
`preserves_fair_weak_divergence` if that theorem were applied to BRB.

**Root cause**: mismatch between ideal and concrete fairness for `commit`.
In the ideal, commit is always fair.  In the concrete, the corresponding
init delivery from a corrupt sender involves only unfair steps.

**Possible fixes** (not yet implemented):
1. Make `ideal_brb_fair_labels (.commit _)` conditional on `sender ∉
   s.corrupted`.  This fixes h_fair_reverse but cascades: breaks
   `ideal_brb_internalStar_allFair`, `rank_decreases_on_unfair_abstract`,
   and the Step A argument in `ideal_brb_totality` for corrupt senders.
2. Restructure `fair_deadlock_diverges` to not use `fair_deadlock_lifts`.
   The honest argument: at any reachable BRB fair-deadlock, the abstract
   is also a fair-deadlock OR can reach one via InternalStar.  This needs
   a case-split on whether sender is corrupt / broadcastVal is set / the
   protocol has completed.  Substantial but feasible.

## 4. `h_ante_transfer` in `brb_totality` (line 785) is FALSE

The `h_ante_transfer` hypothesis in `transfers_leads_to` requires:
for every abstract label `l₂`, if `l₂` is always enabled+fair on the
abstract execution `e₂` from position `k₂`, then `l₂` fires.

**Counterexample for `.commit v`**: with a corrupt sender, abstract commit
v is always enabled (`set_up = none`, `¬ isCorrect sender` → OR satisfied)
and always fair (`True`).  But in the concrete execution, no fair step
causes initSupport to cross echoThreshold (init sends/recvs involving the
corrupt sender are unfair), so commit v never fires in `e₂`.

**Counterexample for `.output p v`**: requires showing the full BRB
delivery chain (init→echo→vote→output) completes under fair scheduling.
While this IS true under weak fairness with a correct sender, the proof
is essentially the concrete-level BRB liveness argument — hundreds of
lines of protocol reasoning that defeats the purpose of the simulation
transfer.

**Proposed decomposition** (not yet implemented):

Split `brb_totality` into two steps:

  *Step A (concrete-level)*: under the concrete fair-WF, if the sender is
  correct and has broadcast, then eventually initSupport crosses
  echoThreshold.  Argument: fair init sends from correct sender fire,
  fair recvs of those messages fire, enough procs get sendRecv set.

  *Step B (transfer from ideal)*: if initSupport ≥ echoThreshold (i.e.,
  set_up ≠ none in abstract), then eventually all correct procs return.
  Uses `ideal_brb_totality`'s Step B via `transfers_leads_to` with a
  weaker `h_ante_transfer` that only handles the output case (commit is
  not enabled when set_up ≠ none).

  The output case of `h_ante_transfer` was THOUGHT to be provable, but
  is actually ALSO blocked by the corrupt-sender issue — see §5 below.

See `plans/liveness-closure.md` for context.

## 5. `h_ante_transfer` output case ALSO blocked (2026-06-04)

**The output case has the same corrupt-sender issue as the commit case.**

When abstract `output(p, v)` is always enabled from some position, we have
`set_up = some v` (i.e., `initSupport v ≥ echoThreshold = n-f`). This means
`|corrupted| + |{correct with sendRecv = some v}| ≥ n-f`.

With `|corrupted| = c ≤ f`: `|{correct with sendRecv}| ≥ n-f-c`.

For the echo chain to complete, each correct receiver needs echoRecv from
ALL correct echoing processes. Only processes with `sendRecv = some v` can
echo (the LTS has no echo amplification based on received echoes). So each
receiver gets at most `n-f-c` echoes from correct sources.

`echoThreshold = n-f`. We need `n-f-c ≥ n-f`, which requires `c ≤ 0`.
So the echo threshold is reached ONLY when `c = 0` (no corruption).

**With corrupt sender** (`c ≥ 1`): `n-f-c < n-f = echoThreshold`. The echo
chain stalls. No process votes. No process returns. Concrete output never
fires. But abstract output remains "always enabled".

**Exception**: if the sender is correct, more init sends fire (fair-WF),
eventually giving ALL correct processes `sendRecv = some v`. Then
`|correct with sendRecv| = n-c ≥ n-f`, and echoRecv ≥ n-f = echoThreshold.

**Conclusion**: both `h_ante_transfer` cases (commit AND output) require
the sender to be correct. This is a fundamental limitation of the
`transfers_leads_to` approach for BRB. The abstract IdealBRB can be live
with a corrupt sender (commit is always fair), but the concrete BRB cannot
(init sends from corrupt sender are unfair).

**Recommended fix**: either
1. Prove `brb_totality` directly at the concrete level (without
   `transfers_leads_to`) with a `sender stays correct` precondition, OR
2. Split `brb_totality` into two concrete-level lemmas:
   - Step A: `broadcastVal ≠ none ∧ sender correct → initSupport ≥ echoThreshold`
   - Step B: `initSupport ≥ echoThreshold ∧ sender correct → all correct returned`
   Both provable via concrete fair-WF.
