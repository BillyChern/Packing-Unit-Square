"""Plot the invariant trajectory ρ(k) = mss(k) × (k+1)."""
import json
import math
import os

with open("/workspace/Packing/results/inv_traj_BAF_N20000.json") as f:
    rows = json.load(f)

# log-log plot of ρ vs k
import math
W, H = 800, 400
M = 60
ks = [r["k"] for r in rows]
ratios = [r["max_min_side_x_kp1"] for r in rows]

logk_min = math.log10(max(min(ks), 1))
logk_max = math.log10(max(ks))
r_min = min(ratios)
r_max = max(ratios)

def mapx(k):
    return M + (math.log10(k) - logk_min) * (W - 2*M) / (logk_max - logk_min)

def mapy(r):
    return H - M - (r - r_min) * (H - 2*M) / (r_max - r_min)

parts = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}">']
parts.append(f'<rect x="0" y="0" width="{W}" height="{H}" fill="white" stroke="#333"/>')
parts.append(f'<text x="{W/2}" y="20" text-anchor="middle" font-family="serif" font-size="14">'
             f'Health ratio ρ(k) = mss(k)·(k+1) for BAF on Moser sequence (k=2..19911)</text>')

# axes
parts.append(f'<line x1="{M}" y1="{H-M}" x2="{W-M}" y2="{H-M}" stroke="#333"/>')
parts.append(f'<line x1="{M}" y1="{M}" x2="{M}" y2="{H-M}" stroke="#333"/>')
# y=1 reference (failure threshold)
y1 = mapy(1)
parts.append(f'<line x1="{M}" y1="{y1}" x2="{W-M}" y2="{y1}" stroke="red" stroke-dasharray="4,2" stroke-width="1"/>')
parts.append(f'<text x="{W-M-100}" y="{y1-3}" font-family="serif" font-size="10" fill="red">ρ=1 (algorithm failure threshold)</text>')

# data line
points = []
for k, r in zip(ks, ratios):
    points.append(f'{mapx(k):.1f},{mapy(r):.1f}')
parts.append(f'<polyline points="{" ".join(points)}" fill="none" stroke="steelblue" stroke-width="0.7"/>')

# axis ticks
for log_k in range(int(logk_min), int(logk_max) + 1):
    k = 10**log_k
    x = mapx(k)
    parts.append(f'<line x1="{x}" y1="{H-M}" x2="{x}" y2="{H-M+5}" stroke="#333"/>')
    parts.append(f'<text x="{x}" y="{H-M+18}" text-anchor="middle" font-family="serif" font-size="10">10^{log_k}</text>')

for r_val in range(int(r_min), int(r_max) + 1, 2):
    y = mapy(r_val)
    parts.append(f'<line x1="{M-5}" y1="{y}" x2="{M}" y2="{y}" stroke="#333"/>')
    parts.append(f'<text x="{M-8}" y="{y+4}" text-anchor="end" font-family="serif" font-size="10">{r_val}</text>')

# mean line
mean_r = sum(ratios) / len(ratios)
ym = mapy(mean_r)
parts.append(f'<line x1="{M}" y1="{ym}" x2="{W-M}" y2="{ym}" stroke="green" stroke-dasharray="6,3" stroke-width="0.7"/>')
parts.append(f'<text x="{W-M-100}" y="{ym-3}" font-family="serif" font-size="10" fill="green">mean = {mean_r:.2f}</text>')

parts.append('</svg>')
out = '/workspace/Packing/figures/invariant_trajectory_BAF.svg'
os.makedirs("/workspace/Packing/figures", exist_ok=True)
with open(out, 'w') as f:
    f.write(''.join(parts))
print(f"Saved {out}")
print(f"Stats: min={min(ratios):.2f} max={max(ratios):.2f} mean={mean_r:.2f}")
