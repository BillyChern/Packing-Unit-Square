"""Plot all heuristics' invariant trajectories together."""
import json, os, math

# Load all tracker logs
data = {}
import re
for fname in os.listdir("/workspace/Packing/results"):
    if not (fname.startswith("inv_fast_") or fname.startswith("inv_BSSF_") or fname.startswith("inv_BAF_")
            or fname.startswith("inv_CONTACT_") or fname.startswith("inv_BLSF_") or fname.startswith("inv_stream_")):
        continue
    if not fname.endswith(".log"):
        continue
    path = f"/workspace/Packing/results/{fname}"
    h = None
    for cand in ["BSSF", "BAF", "CONTACT", "BLSF", "BL"]:
        if f"_{cand}" in fname.upper() or f"_{cand}_" in fname.upper():
            h = cand
            break
    if not h:
        continue
    if h not in data:
        data[h] = []
    with open(path) as f:
        for line in f:
            m = re.search(r"k=\s*(\d+)\s+mss=([\d.eE+-]+)\s+ratio=([\d.eE+-]+)", line)
            if m:
                data[h].append((int(m.group(1)), float(m.group(3))))

# Dedupe & sort
for h in data:
    seen = set()
    rows = []
    for k, r in sorted(data[h], key=lambda x: x[0]):
        if k not in seen:
            seen.add(k)
            rows.append((k, r))
    data[h] = rows

# Plot log-log
W, H = 1000, 500
M = 70

# Find global ranges
all_ks = []
all_rs = []
for h, rows in data.items():
    for k, r in rows:
        if k > 1 and r > 0:
            all_ks.append(k)
            all_rs.append(r)

if not all_ks:
    print("No data!")
    exit(1)

logk_min = math.log10(max(min(all_ks), 1))
logk_max = math.log10(max(all_ks))
logr_min = math.log10(min(all_rs))
logr_max = math.log10(max(all_rs))

def mapx(k):
    return M + (math.log10(k) - logk_min) * (W - 2*M) / (logk_max - logk_min + 1e-9)

def mapy(r):
    return H - M - (math.log10(r) - logr_min) * (H - 2*M) / (logr_max - logr_min + 1e-9)

colors = {
    "BSSF": "steelblue",
    "BAF":  "green",
    "CONTACT": "orange",
    "BLSF": "purple",
    "BL":   "red",
}

parts = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}">']
parts.append(f'<rect x="0" y="0" width="{W}" height="{H}" fill="white" stroke="#333"/>')
parts.append(f'<text x="{W/2}" y="20" text-anchor="middle" font-family="serif" font-size="16">'
             f'Health ratio ρ(k) = mss(k)·(k+1) — log-log, all 5 heuristics</text>')

# axis lines
parts.append(f'<line x1="{M}" y1="{H-M}" x2="{W-M}" y2="{H-M}" stroke="#333"/>')
parts.append(f'<line x1="{M}" y1="{M}" x2="{M}" y2="{H-M}" stroke="#333"/>')

# y=1 reference
y1 = mapy(1)
parts.append(f'<line x1="{M}" y1="{y1}" x2="{W-M}" y2="{y1}" stroke="red" stroke-dasharray="6,3" stroke-width="1.2"/>')
parts.append(f'<text x="{W-M-150}" y="{y1-5}" font-family="serif" font-size="11" fill="red">ρ=1 (failure threshold)</text>')

# Plot each heuristic's trajectory
legend_y = M + 20
for h, rows in data.items():
    color = colors.get(h, "black")
    pts = [(mapx(k), mapy(r)) for k, r in rows if k > 0 and r > 0]
    poly = " ".join(f"{x:.1f},{y:.1f}" for x, y in pts)
    parts.append(f'<polyline points="{poly}" fill="none" stroke="{color}" stroke-width="1.5" opacity="0.7"/>')
    parts.append(f'<rect x="{W-180}" y="{legend_y-10}" width="14" height="3" fill="{color}"/>')
    parts.append(f'<text x="{W-160}" y="{legend_y-5}" font-family="serif" font-size="11" fill="{color}">'
                 f'{h} ({len(rows)} pts, max k={max(k for k,_ in rows) if rows else 0})</text>')
    legend_y += 18

# Tick labels
for log_k in range(int(logk_min), int(logk_max) + 1):
    k = 10**log_k
    x = mapx(k)
    parts.append(f'<line x1="{x}" y1="{H-M}" x2="{x}" y2="{H-M+5}" stroke="#333"/>')
    parts.append(f'<text x="{x}" y="{H-M+18}" text-anchor="middle" font-family="serif" font-size="10">10^{log_k}</text>')

for log_r in range(int(math.floor(logr_min)), int(math.ceil(logr_max)) + 1):
    r = 10**log_r
    y = mapy(r)
    parts.append(f'<line x1="{M-5}" y1="{y}" x2="{M}" y2="{y}" stroke="#333"/>')
    parts.append(f'<text x="{M-8}" y="{y+4}" text-anchor="end" font-family="serif" font-size="10">10^{log_r}</text>')

parts.append(f'<text x="{W/2}" y="{H-M+38}" text-anchor="middle" font-family="serif" font-size="11">k (number of placements)</text>')
parts.append(f'<text x="{M-50}" y="{H/2}" text-anchor="middle" font-family="serif" font-size="11" transform="rotate(-90 {M-50} {H/2})">ρ(k) = mss(k)·(k+1)</text>')

parts.append('</svg>')

with open("/workspace/Packing/figures/invariant_all_heuristics.svg", "w") as f:
    f.write(''.join(parts))
print("Saved /workspace/Packing/figures/invariant_all_heuristics.svg")
print(f"Heuristics plotted: {list(data.keys())}")
print(f"Max k per heuristic: {dict((h, max(k for k,_ in rows)) for h, rows in data.items())}")
print(f"Min ρ per heuristic: {dict((h, min(r for _,r in rows)) for h, rows in data.items())}")
print(f"Max ρ per heuristic: {dict((h, max(r for _,r in rows)) for h, rows in data.items())}")
