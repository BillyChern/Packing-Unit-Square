#!/bin/bash
# Monitor inode and disk usage every 60s. Print warnings if approaching limits.
while true; do
    INODE_USED=$(df -i /workspace 2>/dev/null | awk 'NR==2 {print $3}')
    INODE_FREE=$(df -i /workspace 2>/dev/null | awk 'NR==2 {print $4}')
    DISK_PCT=$(df -h /workspace 2>/dev/null | awk 'NR==2 {gsub("%","",$5); print $5}')
    TS=$(date +%H:%M:%S)
    echo "$TS  used=${INODE_USED}  free=${INODE_FREE}  disk=${DISK_PCT}%"
    # Auto-action only on ABSOLUTE free inodes < 10000 (i.e. real exhaustion).
    if [ "${INODE_FREE:-1000000}" -lt 10000 ]; then
        echo "$TS  CRITICAL: inode free < 10k, killing newest tracker"
        PID=$(ps -eo pid,etime,cmd | grep -E "track_inv_fast|verify_alpha" | grep -v grep | sort -k2 | head -1 | awk '{print $1}')
        if [ -n "$PID" ]; then
            kill $PID 2>/dev/null
            echo "$TS  killed PID $PID"
        fi
    fi
    if [ "${INODE_FREE:-1000000}" -lt 1000 ]; then
        echo "$TS  EMERGENCY: inode free < 1k, killing all"
        pkill -f track_inv 2>/dev/null
        pkill -f full_run 2>/dev/null
        pkill -f verify_alpha 2>/dev/null
    fi
    sleep 60
done
