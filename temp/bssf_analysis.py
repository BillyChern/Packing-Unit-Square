"""Analyze BSSF trajectory: power-law fit, extrapolation, sanity."""
import json, os, math, re

# Load all BSSF logs
data = []
for fname in os.listdir("/workspace/Packing/results"):
    if "BSSF" not in fname or not fname.endswith(".log"):
        continue
    with open(f"/workspace/Packing/results/{fname}") as f:
        for line in f:
            m = re.search(r"k=\s*(\d+)\s+mss=([\d.eE+-]+)\s+ratio=([\d.eE+-]+)", line)
            if m:
                k = int(m.group(1))
                ratio = float(m.group(3))
                if k > 100 and ratio > 0:
                    data.append((k, ratio))

# Dedupe
seen = set()
uniq = []
for k, r in sorted(data):
    if k not in seen:
        seen.add(k)
        uniq.append((k, r))

print(f"BSSF trajectory: {len(uniq)} samples, k ∈ [{min(k for k,_ in uniq)}, {max(k for k,_ in uniq)}]")

# Power-law fit ρ = c · k^α
# log ρ = log c + α log k
import statistics
xs = [math.log(k) for k, _ in uniq]
ys = [math.log(r) for _, r in uniq]
n = len(xs)
mx = sum(xs) / n
my = sum(ys) / n
slope = sum((x-mx)*(y-my) for x,y in zip(xs, ys)) / sum((x-mx)**2 for x in xs)
intercept = my - slope * mx
c = math.exp(intercept)
alpha = slope

print(f"Power-law fit: ρ ≈ {c:.4f} · k^{alpha:.4f}")
print(f"Predictions:")
for k_test in [10**4, 10**5, 10**6, 10**8, 10**12]:
    rho_pred = c * k_test ** alpha
    print(f"  k = 10^{int(math.log10(k_test))}: ρ ≈ {rho_pred:.1f}")

print()
print(f"Min ρ observed: {min(r for _,r in uniq):.3f}")
print(f"Max ρ observed: {max(r for _,r in uniq):.3f}")

# Save for plotting
out_path = "/workspace/Packing/results/bssf_traj_analysis.json"
with open(out_path, "w") as f:
    json.dump({"data": uniq, "fit": {"c": c, "alpha": alpha}}, f)
print(f"Saved {out_path}")
