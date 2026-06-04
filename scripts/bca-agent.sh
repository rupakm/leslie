#!/bin/bash
set -o pipefail
export PATH="/Users/mbk-23-0041/.local/bin:/Users/mbk-23-0041/.elan/bin:/usr/local/bin:/opt/homebrew/bin:/usr/bin:/bin"

cd /Users/mbk-23-0041/code/leslie
LOG="scripts/bca-output.log"

echo "=== $(date) === BCA agent starting ===" >> "$LOG"
echo $$ > scripts/bca-agent.pid

# Snapshot current state for the prompt
SORRY_LINES=$(grep -n 'sorry' Leslie_LTS/Examples/BCA_Liveness.lean 2>/dev/null | grep -v "^[0-9]*:.*--" | head -20)
BCA_STATE=$(cat scripts/bca-state.md 2>/dev/null || echo "(no state file)")
RECENT=$(git log --oneline -5 2>/dev/null)

/Users/mbk-23-0041/.local/bin/claude \
  --print \
  --verbose \
  --output-format stream-json \
  --dangerously-skip-permissions \
  "+10000k

# HARD RULES
1. DO NOT push. Commits local only.
2. Keep working until all BCA sorries are closed or context runs out.
3. Build: \`make LTS 2>&1 | grep 'Build completed successfully'\`.
4. No decide / admit / axiom / extra sorries.
5. Commits: Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>.
6. After EVERY commit, overwrite \`scripts/bca-state.md\` (max 10 lines).
7. ONLY edit: BCA_Liveness.lean, IdealBCA.lean, BCA.lean, BCA_Simulation.lean.

# CRITICAL: DO NOT WASTE CONTEXT
You are restarted frequently when context fills. Do NOT re-read the
entire codebase. The state below tells you what to work on.
Read ONLY the specific sorry location, then IMMEDIATELY start editing.
Commit early and often — even partial progress with new sorries is
better than running out of context with nothing committed.
Do NOT read Framework files or BRB files. Do NOT grep for patterns.
The BRB liveness is already sorry-free — do not look at it.

# Previous agent state
${BCA_STATE}

# Current sorry lines in BCA_Liveness.lean
${SORRY_LINES}

# Recent commits
${RECENT}

# Project: Lean 4 at /Users/mbk-23-0041/code/leslie, branch Leslie_LTS
# Build: make LTS" \
  >> "$LOG" 2>&1

BCA_RC=$?
echo "--- $(date) === BCA agent exited rc=$BCA_RC ===" >> "$LOG"
rm -f scripts/bca-agent.pid
