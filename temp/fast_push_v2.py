"""Push N as large as possible using FastMaxRectsPacker.

Saves a JSON snapshot every CHECKPOINT_EVERY placements so a kill mid-run
loses at most CHECKPOINT_EVERY placements. The final JSON includes full
placement coordinates for downstream certification.
"""
import sys, time, json, os
sys.path.insert(0, "/workspace/Packing")

from fractions import Fraction as F
from src.fast_packer import FastMaxRectsPacker
from src.geometry import Placement, verify_packing

CHECKPOINT_EVERY = 500


def serialize(placements):
    return [
        {
            "k": p.k,
            "x": [p.x.numerator, p.x.denominator],
            "y": [p.y.numerator, p.y.denominator],
            "rotated": p.rotated,
        }
        for p in placements
    ]


def push(heuristic, N_max, log_every=200, ckpt_path: str = ""):
    p = FastMaxRectsPacker(W=F(1), H=F(1))
    p.place_explicit(1, F(0), F(0), rotated=False)
    t0 = time.time()
    last_ok = 1
    last_t = t0
    for k in range(2, N_max + 1):
        placement = p.place(k, allow_rotate=True, heuristic=heuristic)
        if placement is None:
            print(
                f"  [{heuristic}] FAIL at k={k}, free={len(p.free)}, "
                f"elapsed={time.time()-t0:.1f}s",
                flush=True,
            )
            return last_ok, p.placed
        last_ok = k
        if k % log_every == 0:
            now = time.time()
            print(
                f"  [{heuristic}] k={k}/{N_max}  free={len(p.free)}  "
                f"total={now-t0:.1f}s  Δ={now-last_t:.1f}s",
                flush=True,
            )
            last_t = now
        if ckpt_path and k % CHECKPOINT_EVERY == 0:
            with open(ckpt_path, "w") as f:
                json.dump(
                    {
                        "heuristic": heuristic,
                        "max_N": last_ok,
                        "placements": serialize(p.placed),
                    },
                    f,
                )
    return last_ok, p.placed


if __name__ == "__main__":
    h = sys.argv[1] if len(sys.argv) > 1 else "BSSF"
    N_max = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    ckpt = f"/workspace/Packing/results/fast_push_{h}.json"
    n, pl = push(h, N_max, ckpt_path=ckpt)
    sigma = (n + 2, n + 1)
    print(
        f"\n[{h}] FINAL max_N = {n}, sigma <= {sigma[0]}/{sigma[1]} = "
        f"{sigma[0]/sigma[1]:.10f}"
    )
    out = {
        "heuristic": h,
        "max_N": n,
        "sigma": f"{sigma[0]}/{sigma[1]}",
        "sigma_float": sigma[0] / sigma[1],
        "placements": serialize(pl),
    }
    os.makedirs("/workspace/Packing/results", exist_ok=True)
    with open(ckpt, "w") as f:
        json.dump(out, f)
    print(f"saved to {ckpt}")
