# Leslie_LTS — Known Issues and Design Decisions

## 1. `assumes_fair_wf` vs `assumes_fair_wf_step` on stutter executions

**Status:** Resolved (2026-06-03). The step-aware version is now the
ONLY `assumes_fair_wf` — the old label-only variant was deleted.

**The problem:** `assumes_fair_wf` defines "label l eventually fires" as
`eventually (step_prop (fun _ l' _ => l = l'))`, which only checks that
`l = e.labels k` at some position k. On a `valid_exec_stutter` execution,
a τ-stutter position has `e.labels k = τ` and `e.states k = e.states (k+1)`
(no state change). If `τ = .commit default` (as in IdealBRB), then
`.commit default` "fires" at every stutter position — but no state change
occurs.

This breaks the `ideal_brb_totality` proof's contradiction argument on
stutter executions: the argument assumes that when commit fires, `set_up`
changes from `none` to `some v`. On a stutter exec, commit "fires" (label
matches) but `set_up` stays `none` (state unchanged). The contradiction
with `h_none_forever` (set_up = none at all future positions) doesn't work
because commit firing didn't actually change anything.

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
