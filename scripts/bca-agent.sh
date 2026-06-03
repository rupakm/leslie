#!/bin/bash
# ============================================================================
# BCA overnight agent — runs in parallel with the BRB agent.
#
# IMPORTANT: This agent ONLY edits BCA files:
#   - Leslie_LTS/Examples/BCA_Liveness.lean
#   - Leslie_LTS/Examples/IdealBCA.lean
#   - Leslie_LTS/Examples/BCA_Simulation.lean (read-only preferred)
# It must NOT edit BRB files or Framework files (the BRB agent may be
# editing those concurrently).
#
# Start:  ./scripts/bca-agent.sh &
# Stop:   kill %1
# Logs:   scripts/bca-output.log, scripts/bca-state.md
# ============================================================================

set -o pipefail
export PATH="/Users/mbk-23-0041/.local/bin:/Users/mbk-23-0041/.elan/bin:/usr/local/bin:/opt/homebrew/bin:/usr/bin:/bin"

cd /Users/mbk-23-0041/code/leslie
LOG="scripts/bca-output.log"
echo "=== $(date) === BCA agent starting ===" > "$LOG"

# Write PID file so the watchdog can track THIS specific agent
echo $$ > scripts/bca-agent.pid

/Users/mbk-23-0041/.local/bin/claude \
  --print \
  --verbose \
  --output-format stream-json \
  --dangerously-skip-permissions \
  "+10000k

# HARD RULES
1. **DO NOT push.** Commits local only.
2. **No artificial stopping.** Keep working until all BCA sorries are closed or context runs out.
3. **Build verification.** After every commit: \`make LTS 2>&1 | grep 'Build completed successfully'\`.
4. **No decide / admit / axiom / extra sorries.**
5. **Commit messages.** Include Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>.
6. **State file.** After EVERY commit, overwrite \`scripts/bca-state.md\` with: what you did, what's next, what's blocked, sorry count. MAX 10 lines.
7. **FILE RESTRICTION.** You are running in parallel with a BRB agent. You may edit:
   - \`Leslie_LTS/Examples/BCA_Liveness.lean\`
   - \`Leslie_LTS/Examples/IdealBCA.lean\`
   - \`Leslie_LTS/Examples/BCA.lean\` (concrete BCA definitions)
   - \`Leslie_LTS/Examples/BCA_Simulation.lean\` (simulation, sim_rel)
   Do NOT edit any Framework files (\`Leslie_LTS/Framework/\`) or BRB files (\`BRB_Liveness.lean\`, \`BrachaBRB.lean\`, \`IdealBRB.lean\`, \`BRB_Simulation.lean\`). The BRB agent may be editing those concurrently.

# Project overview
Lean 4 formal verification project at /Users/mbk-23-0041/code/leslie, branch Leslie_LTS. Build: \`make LTS\`.

# Key files (READ ONLY)
- \`Leslie_LTS/Framework/Simulation.lean\` — framework (sorry-free, DO NOT EDIT)
- \`Leslie_LTS/Framework/Liveness.lean\` — assumes_fair_wf (step-aware), leads_to
- \`Leslie_LTS/Framework/LTL.lean\` — TraceProp, satisfies, satisfies_stutter
- \`Leslie_LTS/issues.md\` — design decisions (assumes_fair_wf, corrupt-sender fix)
- \`plans/liveness-closure.md\` — multi-session plan

# Files you EDIT
- \`Leslie_LTS/Examples/BCA_Liveness.lean\` — the main target
- \`Leslie_LTS/Examples/IdealBCA.lean\` — persistence lemmas (12 already proven)
- \`Leslie_LTS/Examples/BCA.lean\` — concrete BCA definitions (add persistence lemmas here if needed)
- \`Leslie_LTS/Examples/BCA_Simulation.lean\` — simulation, sim_rel, label_map (reference for bca_fair_compat)

# Current state
Run \`grep -n sorry Leslie_LTS/Examples/BCA_Liveness.lean\` for BCA sorries (~9).
The BCA Protocol Reasoning Cheatsheet is in the BCA_Liveness.lean header — read it.

**Already proven (do NOT redo):**
- bca_fair_labels / ideal_bca_fair_labels (definitions)
- ideal_bca_internal_label_fair + ideal_bca_internalStar_allFair
- rank_decreases_on_unfair_abstract (vacuous — all IdealBCA InternalStars AllFair)
- 12 IdealBCA persistence lemmas (bound_value, decided, corrupted, input — single-step + along + stutter)

# Priorities — in order

## (1) ideal_bca_decision (the main prize)

Proof structure: two steps through \`bound_value ≠ none\`.

**Step A: precondition → bound_value eventually set**
Until-or-forever: assume bound_value = none forever from position k.
- Precondition gives ∃ b, corrupted.length + inputSupport b ≥ f+1.
- This condition is MONOTONE along valid execs: corrupted.length only
  grows (corruption monotone) and inputSupport counts correct procs
  with input (input persists, and corrupted.length growing helps the
  sum). So the condition persists.
- bind(b) is permanently enabled: bound_value = none (assumption) AND
  the support condition (monotone from above).
- bind(b) is fair: ideal_bca_fair_labels (.bind _) = True.
- Apply h_ante: bind fires as a real step → bound_value := some b →
  contradiction with bound_value = none forever.

Key lemma needed: \`inputSupport_condition_persist_along\` — show that
\`s.corrupted.length + inputSupport s b ≥ f + 1\` persists along valid
execs. Can be proven by showing each step either preserves or increases
both summands. Add this to IdealBCA.lean.

**Step B: bound_value set → all correct decided**
Per-proc finite induction (same as BRB Step B):
- For each correct p that stays correct forever:
  * output(p, some b) is enabled: isCorrect p, decided p = none,
    bound_value = some b (persists via bound_value_persist_along).
  * output(p, some b) is fair: p ∉ corrupted.
  * h_ante fires it → decided p := some (some b).
  * If output(p, some b) is NOT enabled for some reason (e.g.,
    bound_value = some b but the output step also allows output(p, none)
    under different conditions), show output(p, none) is enabled instead.
    For pure liveness, either suffices — decided ≠ none is the goal.
- Finite-max wrapper: Finset.sup over Fin n + decided_persist_along.

## (2) ideal_bca_decision_stutter
Same proof as (1) but with step-aware h_ante. At extraction points,
h_ante gives ⟨j, hlbl, h_step⟩. The step replaces hv.2 (k+j).

## (3) bca_fair_compat
Case-split on concrete label, use sim_rel.1 (corrupted agrees).
Check what label_map does for each BCA label — look at
BCA_Simulation.bca_forward_sim.label_map.

## (4) bca_decision
Apply transfers_leads_to with bca_weak_div_witness +
ideal_bca_decision_stutter + bca_fair_compat.

## (5) Lower priority — witness obligations
bca_progress_measure, bca_rank_wf, rank obligations,
bca_fair_deadlock_implies_terminated, h_fair_reverse.
Same placeholder pattern as BRB — don't block theorems.

# TLA-side proof reference (Leslie/Examples/BindingCrusaderAgreementLiveness.lean)

The TLA-side BCA liveness proof (4513 lines) contains the complete
argument. Here are the KEY theorems to mirror:

**Fairness + persistence (lines 60–920):**
- \`bca_fairness\` (line 60): WF(correct send) ∧ WF(recv) ∧ WF(decide)
- \`persist_mono\` (line 95): generic persistence pattern
- 20+ field-specific persistence lemmas (already mirrored in IdealBCA.lean)

**WF applications (lines 2516–2660):**
- \`wf_send\` (line 2563): gate open → send fires (uses \`wf_gate_always_open_contra\`)
- \`wf_send_type\` (line 2610): type-level send (for echo/vote commitment)
- \`wf_recv\` (referenced throughout): message in buffer → received
- \`wf_decide\` (referenced at line 3430): decide gate open → fires
- \`wf_chain\` (line 2668): composed: gate → send → buffer → recv → delivered
- \`wf_chain_type\` (line 2737): type-level chain

**The delivery chain (lines 3062–3470) — mirror these for ideal_bca_decision:**
1. \`init_delivery_correct_sender\` (3068): correct sender with input b →
   init(b) delivered to every q. Pattern: wf_chain with trivial init gate.
2. \`init_delivery_from_initRecv\` (3110): if p has initRecv s b, then
   init(b) delivered to every r. Wraps wf_chain.
3. \`amplify_init_delivery\` (3156): countInitRecv ≥ f+1 → init(b)
   delivered to all. Uses amplify gate.
4. \`echo_delivery_from_approved\` (3195): approved b → echo delivered
   to every q. Uses wf_chain_type (echo commitment).
5. \`vote_delivery_from_ready\` (3307): echo quorum OR both approved →
   vote delivered to every q. Uses wf_chain_type (vote commitment).
6. \`decide_delivery_binary\` (3419): n-f binary votes → decide (some b).
7. \`decide_delivery_none\` (3456): two approved + n-f total votes →
   decide none.

**For ideal_bca_decision, you DON'T need the full chain.** The ideal
BCA is much simpler — just bind + output. The delivery chain is for
the CONCRETE BCA. For the ideal:
- Step A: bind(b) fires when inputSupport ≥ f+1 (same pattern as
  BRB's commit).
- Step B: output(p, v) fires when bound_value = some b and decided =
  none (same pattern as BRB's output).

The TLA delivery chain is useful for bca_fair_deadlock_implies_
terminated and h_ante_transfer (concrete-side arguments), not for
ideal_bca_decision (ideal-side argument)." \
  >> "$LOG" 2>&1

BCA_RC=$?
echo "--- $(date) === BCA agent exited rc=$BCA_RC ===" >> "$LOG"
rm -f scripts/bca-agent.pid
