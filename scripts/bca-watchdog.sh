#!/bin/bash
# ============================================================================
# BCA watchdog: monitors the BCA agent, restarts on process death.
# Same structure as overnight-watchdog.sh but for the BCA agent.
# ============================================================================

set -o pipefail
export PATH="/Users/mbk-23-0041/.local/bin:/Users/mbk-23-0041/.elan/bin:/usr/local/bin:/opt/homebrew/bin:/usr/bin:/bin"

cd /Users/mbk-23-0041/code/leslie

LOG="scripts/bca-watchdog.log"
BCA_LOG="scripts/bca-output.log"
STATE_FILE="scripts/bca-state.md"

POLL_INTERVAL=60
TOTAL_RUNTIME=28800
MAX_RESTARTS=25

echo "=== $(date) === BCA watchdog started ===" > "$LOG"

restarts=0
start_time=$(date +%s)

PID_FILE="scripts/bca-agent.pid"

bca_alive() {
    [ -f "$PID_FILE" ] && kill -0 "$(cat "$PID_FILE")" 2>/dev/null
}

# Wait for BCA agent to appear
echo "$(date): waiting for BCA agent..." >> "$LOG"
for i in $(seq 1 30); do
    if bca_alive; then
        echo "$(date): BCA agent detected (pid $(cat "$PID_FILE"))" >> "$LOG"
        break
    fi
    sleep 10
done

if ! bca_alive; then
    echo "$(date): no BCA agent found. Starting one." >> "$LOG"
    restarts=1
    nohup scripts/bca-agent.sh > /dev/null 2>&1 &
    echo "$(date): started bca-agent.sh (pid $!)" >> "$LOG"
fi

while true; do
    now=$(date +%s)
    elapsed=$((now - start_time))
    if [ $elapsed -ge $TOTAL_RUNTIME ]; then
        echo "$(date): runtime exceeded. Done." >> "$LOG"
        break
    fi
    sleep $POLL_INTERVAL
    if bca_alive; then
        continue
    fi
    echo "$(date): BCA agent died." >> "$LOG"
    if [ $restarts -ge $MAX_RESTARTS ]; then
        echo "$(date): max restarts reached." >> "$LOG"
        break
    fi
    restarts=$((restarts + 1))
    echo "$(date): restarting BCA (#$restarts)..." >> "$LOG"
    nohup scripts/bca-agent.sh > /dev/null 2>&1 &
    echo "$(date): started bca-agent.sh (pid $!)" >> "$LOG"
done

echo "=== $(date) === BCA watchdog done ===" >> "$LOG"
