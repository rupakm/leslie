#!/bin/bash
# ============================================================================
# BCA watchdog: monitors the BCA agent's OUTPUT FILE for growth.
# If output stalls for STALL_THRESHOLD seconds, kills + restarts.
# ============================================================================

set -o pipefail
export PATH="/Users/mbk-23-0041/.local/bin:/Users/mbk-23-0041/.elan/bin:/usr/local/bin:/opt/homebrew/bin:/usr/bin:/bin"

cd /Users/mbk-23-0041/code/leslie

LOG="scripts/bca-watchdog.log"
BCA_LOG="scripts/bca-output.log"
STATE_FILE="scripts/bca-state.md"
PID_FILE="scripts/bca-agent.pid"

POLL_INTERVAL=120
STALL_THRESHOLD=900    # 15 min without output = hung
TOTAL_RUNTIME=36000
MAX_RESTARTS=25

echo "=== $(date) === BCA watchdog started ===" >> "$LOG"

restarts=0
start_time=$(date +%s)
last_size=$(wc -c < "$BCA_LOG" 2>/dev/null || echo 0)
last_growth=$(date +%s)

# Wait up to 2 minutes for BCA agent output
for i in $(seq 1 12); do
    cur_size=$(wc -c < "$BCA_LOG" 2>/dev/null || echo 0)
    if [ "$cur_size" -gt "$last_size" ]; then
        echo "$(date): BCA agent producing output ($cur_size bytes)" >> "$LOG"
        last_size=$cur_size
        last_growth=$(date +%s)
        break
    fi
    sleep 10
done

while true; do
    now=$(date +%s)
    elapsed=$((now - start_time))

    if [ $elapsed -ge $TOTAL_RUNTIME ]; then
        echo "$(date): total runtime exceeded. Done." >> "$LOG"
        break
    fi

    sleep $POLL_INTERVAL

    cur_size=$(wc -c < "$BCA_LOG" 2>/dev/null || echo 0)
    if [ "$cur_size" -gt "$last_size" ]; then
        last_size=$cur_size
        last_growth=$(date +%s)
        continue
    fi

    stall_time=$((now - last_growth))
    if [ $stall_time -lt $STALL_THRESHOLD ]; then
        continue
    fi

    echo "$(date): BCA agent stalled (no output for ${stall_time}s). Killing." >> "$LOG"

    # Kill via PID file
    if [ -f "$PID_FILE" ]; then
        kill "$(cat "$PID_FILE")" 2>/dev/null
        rm -f "$PID_FILE"
    fi
    sleep 5

    if [ $restarts -ge $MAX_RESTARTS ]; then
        echo "$(date): max restarts ($MAX_RESTARTS) reached. Done." >> "$LOG"
        break
    fi

    restarts=$((restarts + 1))
    echo "$(date): restarting BCA (#$restarts)..." >> "$LOG"
    nohup scripts/bca-agent.sh > /dev/null 2>&1 &
    echo "$(date): started bca-agent.sh (pid $!)" >> "$LOG"
    last_size=$(wc -c < "$BCA_LOG" 2>/dev/null || echo 0)
    last_growth=$(date +%s)
done

echo "=== $(date) === BCA watchdog done ===" >> "$LOG"
