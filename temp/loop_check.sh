#!/bin/bash
# Periodic self-check: snapshot tracker + inode + cert status.
# Designed to be called from loop wakeup.
set -e
out=/workspace/Packing/results/loop_status.log
ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")

{
echo "============================================"
echo "LOOP CHECK at $ts"
echo "============================================"

echo "--- Inode/disk ---"
df -i /workspace 2>/dev/null | tail -1
df -h /workspace 2>/dev/null | tail -1

echo "--- Active processes ---"
ps aux | grep -E "track_inv|full_run|inode_monitor" | grep -v grep | wc -l
echo " python procs"

echo "--- Latest tracker values (v1 — pre-restart) ---"
for h in BSSF BAF CONTACT BLSF; do
    f=/workspace/Packing/results/inv_fast_${h}.log
    last=$(tail -1 $f 2>/dev/null)
    echo "  [$h] $last"
done
echo "--- Latest tracker values (v2 — post-restart) ---"
for h in BSSF BAF CONTACT BLSF; do
    f=/workspace/Packing/results/inv_fast_${h}_v2.log
    if [ -f "$f" ]; then
        last=$(tail -1 $f 2>/dev/null)
        echo "  [$h v2] $last"
    fi
done
echo "  [BSSF 1M]"
tail -1 /workspace/Packing/results/inv_fast_BSSF_1M.log 2>/dev/null

echo "--- Cert pushes ---"
for f in /workspace/Packing/results/v6_*.log; do
    h=$(basename $f .log)
    last=$(tail -1 $f 2>/dev/null)
    echo "  [$h] $last"
done

echo "--- New certificates? ---"
ls /workspace/Packing/results/full_*N5*.json /workspace/Packing/results/full_*N1*.json 2>/dev/null

echo "--- FAIL events? ---"
grep -l "FAIL" /workspace/Packing/results/inv_fast_*.log 2>/dev/null

echo ""
} >> $out
echo "Wrote snapshot to $out"
