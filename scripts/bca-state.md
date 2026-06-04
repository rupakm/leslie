# BCA Agent State
**Last commit:** dbc7435 — fix bca_fair_deadlock_implies_terminated precondition + delivery invariants
**Sorry count:** 8 in BCA_Liveness.lean. BCA.lean/IdealBCA.lean/BCA_Simulation.lean: 0.

## What was done this session:
- Fixed FALSE precondition on bca_fair_deadlock_implies_terminated (∃ → ∀ correct input)
- Restructured fair_deadlock_diverges with explicit case analysis + design gap documentation
- Fixed BRB agent's broken delivery invariants in BCA.lean (added 5 helpers, rewrote 3 proofs)

## Remaining 8 sorries (all structurally blocked):
1. bca_fair_deadlock_implies_terminated — needs full delivery chain proof
2-4. rank_{non_increasing,decreases_on_fair_elision,non_increasing_on_fair_progress} — need real measure
5-6. fair_deadlock_diverges bind/output — DESIGN GAP: sim_rel insufficient (see comment)
7-8. h_ante_transfer bind/output — structurally blocked (same as BRB)

## What's next:
- Progress measure design (closes 3 sorries if T is Fintype)
- Delivery chain proof for bca_fair_deadlock_implies_terminated
- Fair_deadlock_diverges needs sim_rel redesign (research-level)
