"""Streaming trajectory: print every X placements so we see live progress."""
import sys, time, json, os
sys.set_int_max_str_digits(0)
sys.path.insert(0, "/workspace/Packing")
from fractions import Fraction as F
from src.fast_packer import FastMaxRectsPacker


def main(heuristic="BAF", N_max=50000):
    p = FastMaxRectsPacker(W=F(1), H=F(1))
    p.place_explicit(1, F(0), F(0), rotated=False)
    rows = []
    t0 = time.time()
    min_ratio = float('inf')
    min_ratio_k = 0
    last_print_k = 0
    PRINT_GAP = 1000  # log roughly every 1000
    for k in range(2, N_max + 1):
        if p.place(k, allow_rotate=True, heuristic=heuristic) is None:
            print(f'FAIL at k={k}', flush=True)
            break
        # check ratio every step but log sparsely; CRITICAL: detect any drop below 1.0 immediately
        # mss = max over F of min(W, H)
        # The TRUE next-fit feasibility: ∃ F with min(W,H) ≥ 1/(k+2) AND max(W,H) ≥ 1/(k+1).
        # We track both:
        mss = F(0)  # max min-side
        feasibility = 0  # max over F of min(min·(k+2), max·(k+1))
        for fr in p.free:
            mn, mx = (fr.w, fr.h) if fr.w <= fr.h else (fr.h, fr.w)
            if mn > mss:
                mss = mn
            f = min(mn * (k + 2), mx * (k + 1))
            if f > feasibility:
                feasibility = f
        ratio = float(mss * (k + 1))
        feas_f = float(feasibility)
        if ratio < min_ratio:
            min_ratio = ratio
            min_ratio_k = k
            if ratio < 2.0:  # noteworthy drop
                rows.append({"k": k, "mss": float(mss), "ratio": ratio, "feasibility": feas_f, "tag": "min_so_far"})
                print(f'  ! k={k:>6} mss={float(mss):.4e} ratio={ratio:.3f} feas={feas_f:.3f} (NEW MIN)', flush=True)
        if k - last_print_k >= PRINT_GAP:
            elapsed = time.time() - t0
            print(f'  k={k:>6} mss={float(mss):.4e} ratio={ratio:.3f} feas={feas_f:.3f}  min={min_ratio:.3f}@k={min_ratio_k}  t={elapsed:.0f}s', flush=True)
            rows.append({"k": k, "mss": float(mss), "ratio": ratio, "feasibility": feas_f})
            last_print_k = k
            # checkpoint
            if k % 5000 == 0:
                tmp = f"/workspace/Packing/results/inv_stream_{heuristic}_N{N_max}_chk.json"
                with open(tmp, "w") as f:
                    json.dump({"heuristic": heuristic, "N_max": N_max, "rows": rows,
                               "min_ratio": min_ratio, "min_ratio_k": min_ratio_k,
                               "last_k": k}, f)
    out = f"/workspace/Packing/results/inv_stream_{heuristic}_N{N_max}.json"
    with open(out, "w") as f:
        json.dump({"heuristic": heuristic, "N_max": N_max, "rows": rows,
                   "min_ratio": min_ratio, "min_ratio_k": min_ratio_k}, f)
    print(f'Saved {out}; min_ratio={min_ratio:.3f}@k={min_ratio_k}')


if __name__ == "__main__":
    h = sys.argv[1] if len(sys.argv) > 1 else "BAF"
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 50000
    main(h, N)
