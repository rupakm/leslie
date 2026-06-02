# Leslie_LTS — Known Issues and Design Decisions

## 1. `assumes_fair_wf` vs `assumes_fair_wf_step` on stutter executions

**Status:** Resolved via `assumes_fair_wf_step` (2026-06-02).

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

**The fix:** `assumes_fair_wf_step` (in `Leslie_LTS/Framework/Liveness.lean`)
strengthens "fires" to require BOTH `l = e.labels k` AND
`sys.step (e.states k) (e.labels k) (e.states (k+1))` — a real step
occurred. On `valid_exec` (non-stutter), this is equivalent to
`assumes_fair_wf` (proven via `assumes_fair_wf_step_eq_on_valid_exec`).
On `valid_exec_stutter`, it's strictly weaker (harder antecedent, easier
to prove the implication).

`transfers_satisfaction`'s `h_abs` hypothesis is typed as
`abstract.satisfies_stutter lab₂ (assumes_fair_wf_step ...)`, and its
`h_ante_transfer` output also uses the step-aware variant. This means
callers (like `ideal_brb_totality_stutter`) can extract real steps at
label-fire positions, making the state-change contradiction work.

**Impact:** `ideal_brb_totality` (non-stutter version) is unaffected — it
uses `assumes_fair_wf` directly and is fully proven. Only the stutter
variant and the transfer chain use `assumes_fair_wf_step`.

**Files:**
- `Leslie_LTS/Framework/Liveness.lean` — definition + equivalence theorem
- `Leslie_LTS/Framework/Simulation.lean` — `transfers_satisfaction` h_abs/h_ante_transfer re-typed
- `Leslie_LTS/Examples/BRB_Liveness.lean` — `ideal_brb_totality_stutter` re-typed
