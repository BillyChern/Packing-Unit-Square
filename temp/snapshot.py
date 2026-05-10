"""Snapshot of empirical invariant data so far."""
import sys
import os
import json
import re

# Parse logs
data = {}
for h in ["BSSF", "BAF", "CONTACT", "BLSF", "BL"]:
    data[h] = []
    for fname in os.listdir("/workspace/Packing/results"):
        if not fname.startswith("inv_") or fname.endswith(".pkl") or "_chk" in fname:
            continue
        if not fname.endswith(".log"):
            continue
        # match heuristic
        if f"_{h}_" not in fname and not fname.endswith(f"_{h}.log"):
            continue
        path = f"/workspace/Packing/results/{fname}"
        with open(path) as f:
            for line in f:
                m = re.search(r"k=\s*(\d+)\s+mss=([\d.eE+-]+)\s+ratio=([\d.eE+-]+)", line)
                if m:
                    data[h].append({"k": int(m.group(1)),
                                    "mss": float(m.group(2)),
                                    "ratio": float(m.group(3)),
                                    "src": fname})

# Summarize per heuristic
print("Summary (across all logs)")
print(f"{'Heur':<10}{'samples':<10}{'min ratio':<14}{'min ratio @ k':<14}{'max k':<10}{'max ratio':<10}")
for h, rows in data.items():
    if not rows:
        continue
    rows.sort(key=lambda r: r["k"])
    k_max = rows[-1]["k"]
    ratios = [r["ratio"] for r in rows]
    min_r = min(ratios)
    min_r_k = rows[ratios.index(min_r)]["k"]
    max_r = max(ratios)
    print(f"{h:<10}{len(rows):<10}{min_r:<14.3f}{min_r_k:<14}{k_max:<10}{max_r:<10.3f}")

# Save JSON
out_path = "/workspace/Packing/results/inv_snapshot.json"
with open(out_path, "w") as f:
    json.dump(data, f)
print(f"\nSaved {out_path}")
