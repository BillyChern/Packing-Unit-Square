"""Push N as large as possible using FastMaxRectsPacker."""
import sys, time, json, os
sys.path.insert(0, "/workspace/Packing")

from fractions import Fraction as F
from src.fast_packer import FastMaxRectsPacker
from src.geometry import Placement, verify_packing

def push(heuristic, N_max, log_every=200):
    p = FastMaxRectsPacker(W=F(1), H=F(1))
    p.place_explicit(1, F(0), F(0), rotated=False)
    t0 = time.time()
    last_n = 1
    last_t = t0
    for k in range(2, N_max + 1):
        placement = p.place(k, allow_rotate=True, heuristic=heuristic)
        if placement is None:
            print(f"  [{heuristic}] FAIL at k={k}, free_rects={len(p.free)}, elapsed={time.time()-t0:.1f}s", flush=True)
            return last_n, p.placed
        last_n = k
        if k % log_every == 0:
            now = time.time()
            print(f"  [{heuristic}] k={k}/{N_max}  free={len(p.free)}  total={now-t0:.1f}s  Δ={now-last_t:.1f}s", flush=True)
            last_t = now
    return last_n, p.placed


def serialize(placements):
    rows = []
    for p in placements:
        rows.append({
            "k": p.k,
            "x": [p.x.numerator, p.x.denominator],
            "y": [p.y.numerator, p.y.denominator],
            "rotated": p.rotated,
        })
    return rows


if __name__ == "__main__":
    h = sys.argv[1] if len(sys.argv) > 1 else "BSSF"
    N_max = int(sys.argv[2]) if len(sys.argv) > 2 else 5000
    n, pl = push(h, N_max)
    sigma = (n + 2, n + 1)
    print(f"\n[{h}] FINAL max_N = {n}, sigma <= {sigma[0]}/{sigma[1]} = {sigma[0]/sigma[1]:.10f}")
    print("Verifying with exact arithmetic...")
    t0 = time.time()
    ok, errs = verify_packing(pl, F(1), F(1))
    print(f"verify_ok={ok} errors_sample={errs[:3]} verify_time={time.time()-t0:.1f}s")
    out = {"heuristic": h, "max_N": n, "sigma": f"{sigma[0]}/{sigma[1]}",
           "sigma_float": sigma[0]/sigma[1], "verify_ok": ok,
           "placements": serialize(pl)}
    os.makedirs("/workspace/Packing/results", exist_ok=True)
    with open(f"/workspace/Packing/results/fast_push_{h}.json", "w") as f:
        json.dump(out, f)
