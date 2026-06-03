#!/bin/bash
# ============================================================================
# One-shot LaunchAgent runner.
#
# Reload (re-arm for the next 01:00):
#     launchctl load ~/Library/LaunchAgents/com.user.leslie-overnight.plist
#
# Confirm it's armed:
#     launchctl list | grep leslie-overnight     # `-` in col 1 = idle, scheduled
#
# Cancel without firing:
#     launchctl unload ~/Library/LaunchAgents/com.user.leslie-overnight.plist
#
# Change time: edit StartCalendarInterval in the plist, then unload + load.
# ============================================================================
# NOTE: no `set -e` — we want to reach the unload step even if claude errors.
set -o pipefail
export PATH="/Users/mbk-23-0041/.local/bin:/usr/local/bin:/opt/homebrew/bin:/usr/bin:/bin"
cd /Users/mbk-23-0041/code/leslie
LOG="scripts/overnight-output.log"
echo "=== $(date) === overnight resume firing ===" > "$LOG"
echo "claude path: $(command -v claude)" >> "$LOG"
echo "cwd: $(pwd)" >> "$LOG"
echo "branch: $(git branch --show-current)" >> "$LOG"
echo "head: $(git log --oneline -1)" >> "$LOG"
echo "---" >> "$LOG"

# Always unload on exit (success, error, or signal). Runs AFTER claude returns,
# so the SIGTERM from unload no longer matters — work is done.
trap 'echo "--- $(date) === unloading launchd agent ===" >> "$LOG"; \
      launchctl unload ~/Library/LaunchAgents/com.user.leslie-overnight.plist 2>>"$LOG"' EXIT

# Run claude inline (NOT exec) so the script stays alive as the LaunchAgent
# process and the trap above can fire after claude finishes.
# --output-format stream-json emits every message chunk as a JSON line,
# giving a full log of all tool calls, edits, and model responses.
# Fresh session (no --resume) to avoid inheriting a bloated context
# window from prior conversations. The prompt below is self-contained
# and points to the plan file for design decisions.
/Users/mbk-23-0041/.local/bin/claude \
  --print \
  --verbose \
  --output-format stream-json \
  --dangerously-skip-permissions \
  "+10000k

# HARD RULES (read these FIRST, before doing ANYTHING)
1. **DO NOT push.** No \`git push\` to any remote under any circumstances. Commits are local only.
2. **No artificial stopping.** Treat the +10000k directive as effectively unlimited. Do NOT self-stop because 'work feels heavy' or 'a natural pause exists' or you want to 'write a summary'. The ONLY stopping conditions are: (a) all priorities below are done; (b) the harness terminates you because real context is exhausted; (c) you are genuinely stuck after substantial exploration (20+ minutes on one sorry) and need to pivot to the next item.
3. **Build verification.** After every commit, verify build by running \`make LTS 2>&1 | grep 'Build completed successfully'\`. WARNING: \`make LTS 2>&1 | tail\` shows tail's exit code (always 0), not make's — it will mask build failures. Always grep for the success line.
4. **No decide / admit / axiom / extra sorries** beyond what already exists in the codebase.
5. **Commit messages.** One commit per meaningful unit. Include Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>.
6. **FILE RESTRICTION.** You are running in parallel with a BCA agent. You may edit:
   - \`Leslie_LTS/Examples/BRB_Liveness.lean\`
   - \`Leslie_LTS/Examples/IdealBRB.lean\`
   - \`Leslie_LTS/Examples/BrachaBRB.lean\`
   - \`Leslie_LTS/Examples/BRB_Simulation.lean\`
   Do NOT edit Framework files (\`Leslie_LTS/Framework/\`) or BCA files (\`BCA_Liveness.lean\`, \`IdealBCA.lean\`, \`BCA.lean\`, \`BCA_Simulation.lean\`). Another agent edits those.
7. **State file.** After EVERY commit, update \`scripts/agent-state.md\` with:
   - What you just proved/changed (1 line)
   - What you are attempting next (1 line)
   - What's blocked and why (1 line, or 'nothing')
   - Current sorry count: \`grep -c sorry Leslie_LTS/Examples/BRB_Liveness.lean\`
   This file is read by a watchdog and by any fresh agent that replaces you if you go idle. Keep it SHORT (max 10 lines). Overwrite the whole file each time — it is not a log.

# Project overview
You are working in a Lean 4 formal verification project at /Users/mbk-23-0041/code/leslie on branch Leslie_LTS. The project proves liveness properties of distributed protocols (BRB = Byzantine Reliable Broadcast, BCA = Binding Crusader Agreement) via forward simulations that are weak-divergence-preserving under fair scheduling, following Gaspard et al. CONCUR 2026.

Build command: \`make LTS\` from repo root. This runs \`lake build Leslie_LTS\`. Building the TLA framework (\`make TLA\`) is NOT needed.

# Key files
- \`Leslie_LTS/Framework/Simulation.lean\` — ForwardSim, WeakDivPreserving witness structure, preserves_fair_weak_divergence (soundness), transfers_satisfaction (transfer theorem). The FRAMEWORK is currently sorry-free.
- \`Leslie_LTS/Framework/Basic.lean\` — InternalStar, AllFair, helper lemmas.
- \`Leslie_LTS/Framework/Trace.lean\` — Execution, LPath, InternalStar.toInternalLPath.
- \`Leslie_LTS/Framework/Divergence.lean\` — FairDiverges, FairlyWeaklyDiverges, FairDeadlock.
- \`Leslie_LTS/Framework/Liveness.lean\` — leads_to, weak_fairness, assumes_fair_wf.
- \`Leslie_LTS/Framework/LTL.lean\` — TraceProp, System.satisfies, System.satisfies_stutter.
- \`Leslie_LTS/Framework/Composition.lean\` — parallel composition + compose_with_compatible.
- \`Leslie_LTS/Examples/BrachaBRB.lean\` — Concrete BRB LTS (State, Label, step).
- \`Leslie_LTS/Examples/IdealBRB.lean\` — Ideal BRB spec.
- \`Leslie_LTS/Examples/BRB_Simulation.lean\` — brb_forward_sim, sim_rel, step_internal.
- \`Leslie_LTS/Examples/BRB_Liveness.lean\` — brb_weak_div_witness, brb_fair_labels, ideal_brb_totality, brb_totality. **THIS IS WHERE THE REMAINING WORK IS.** Read the module header for the dependency graph and attack order.
- \`Leslie_LTS/issues.md\` — **READ THIS** for the assumes_fair_wf vs assumes_fair_wf_step design decision (critical for understanding ideal_brb_totality_stutter and the transfers_satisfaction h_abs typing).
- \`plans/liveness-closure.md\` — Multi-session plan with design decisions and progress notes.

# Current state (as of 2026-06-03 evening)

Run \`grep -n sorry Leslie_LTS/Examples/BRB_Liveness.lean\` to see remaining BRB sorries.
Run \`grep -n sorry Leslie_LTS/Examples/BCA_Liveness.lean\` for BCA sorries.
Framework (\`Leslie_LTS/Framework/\`) is **sorry-free**.

**CRITICAL: Read Leslie_LTS/issues.md FIRST** — it documents the
corrupt-sender fairness mismatch (§3-4) that affects h_ante_transfer
and h_fair_reverse. The previous agent already fixed the fair-label
definitions and narrowed the brb_totality antecedent.

**ALREADY PROVEN (do NOT redo):**
- \`ideal_brb_totality\` + \`ideal_brb_totality_stutter\`: FULLY PROVEN.
- \`brb_totality\`: PROVEN via \`transfers_leads_to\`.
- \`brb_fair_compat\`: PROVEN.
- \`brb_rank_wf\`: PROVEN (trivially for placeholder).
- \`rank_decreases_on_unfair_abstract\`: PROVEN (vacuous).
- All framework theorems: PROVEN.
- h_ante_transfer corrupt/input cases: PROVEN (case-split done).
- Concrete BRB persistence lemmas in BrachaBRB.lean: step_voteRecv,
  step_echoRecv, step_voted, step_sendRecv_mono, step_countVoteRecv_mono,
  step_countEchoRecv_mono, step_broadcastVal, step_corrupted,
  step_returned, step_sent_mono + all execution-level *_persist_along.
- IdealBRB stutter persistence: broadcastVal, set_up, returned, corrupted.

# Priorities — BRB remaining sorries (~6), then BCA

## BRB Track 1 — h_ante_transfer output case (line ~999)

The h_ante_transfer case-split has corrupt/input cases proven. The
**commit case** is blocked by the fairness mismatch (see issues.md §4 —
commit is now fair only when sender is correct, so the always-enabled
assumption implies sender is correct, which means broadcastVal ≠ none,
which means initSupport will cross the threshold via fair concrete
sends/recvs). Attempt this case.

The **output case**: abstract output(p, v) always enabled + fair means
isCorrect p on abstract side. Via sim_rel, isCorrect on concrete side.
Need to show: some fair concrete step eventually fires that makes the
abstract output happen. This requires the delivery chain argument (see
the BRB Protocol Reasoning Cheatsheet in BRB_Liveness.lean header).

## BRB Track 2 — Fair-deadlock chain (lines ~338, ~446)

\`brb_fair_deadlock_implies_terminated\` (line ~338): at a reachable
fair-deadlock with broadcastVal ≠ none (the corrected precondition),
every correct proc has returned. See cheatsheet for the argument.

\`h_fair_reverse\` (line ~446): depends on brb_fair_deadlock_implies_
terminated. See issues.md §3.

## BRB Track 3 — Progress measure (lines ~407, ~413, ~428)

Placeholder measure makes these vacuous. Design a real lex measure if
time permits. These don't block any theorem.

## BCA — start if BRB tracks 1-2 are done

BCA has ~8 sorries. The structure mirrors BRB but with a multi-phase
delivery chain (init → echo → vote → decide). Key differences:
- No single sender — every process provides input.
- \`.bind\` is always fair (no corrupt-sender issue like BRB).
- The liveness precondition is \`input_ready\` (all correct procs
  have input, or been corrupted).
- Output has two forms: \`some b\` (binary) and \`none\` (⊥). Both
  must be handled for liveness (decided ≠ none).

**Priority order for BCA:**
1. Add IdealBCA persistence lemmas (bound_value, decided, corrupted,
   input_ — single-step + along + stutter variants, ~12 lemmas).
2. Fix \`ideal_bca_decision\` statement: change from \`eventually\` to
   \`leads_to\` with \`input_ready\` precondition (all correct procs
   have input or been corrupted).
3. Prove \`ideal_bca_decision\`: Step A (input_ready → bound_value set
   via fair bind) + Step B (bound_value set → all correct decided via
   fair output). Same until-or-forever pattern as BRB.
4. Add \`ideal_bca_decision_stutter\` (same proof, step-aware h_ante).
5. Add \`bca_fair_compat\` and prove it.
6. Prove \`bca_decision\` via \`transfers_leads_to\`.

See BCA_Liveness.lean header for the full protocol reasoning cheatsheet
and plans/liveness-closure.md Phase E for design details.

# Reporting
At the end of your run, write a brief report: what got done, what's still open, total commits. Do NOT push." \
  >> "$LOG" 2>&1
CLAUDE_RC=$?
echo "--- $(date) === claude exited rc=$CLAUDE_RC ===" >> "$LOG"
# trap fires here on exit and unloads
