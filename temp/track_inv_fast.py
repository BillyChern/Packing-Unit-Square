"""Faster invariant tracker — uses float-only for the mss/feas computation
(safe because the algorithm itself uses Fraction; we just measure)."""
import sys, time, json
sys.set_int_max_str_digits(0)
sys.path.insert(0, "/workspace/Packing")
from fractions import Fraction as F
from src.fast_packer import FastMaxRectsPacker


def main(heuristic="BSSF", N_max=200000):
    p = FastMaxRectsPacker(W=F(1), H=F(1))
    p.place_explicit(1, F(0), F(0), rotated=False)
    rows = []
    t0 = time.time()
    min_ratio = float('inf')
    min_ratio_k = 0
    last_print_k = 0
    for k in range(2, N_max + 1):
        if p.place(k, allow_rotate=True, heuristic=heuristic) is None:
            print(f'FAIL at k={k}', flush=True)
            break
        # Fast float-only computation (cached float fields)
        mss_f = 0.0
        feas_f = 0.0
        for fr in p.free:
            mn = fr.wf if fr.wf < fr.hf else fr.hf
            mx = fr.wf if fr.wf > fr.hf else fr.hf
            if mn > mss_f:
                mss_f = mn
            f = mn * (k + 2) if mn * (k + 2) < mx * (k + 1) else mx * (k + 1)
            if f > feas_f:
                feas_f = f
        ratio = mss_f * (k + 1)
        if ratio < min_ratio:
            min_ratio = ratio
            min_ratio_k = k
            if ratio < 2.0:
                rows.append({"k": k, "mss": mss_f, "ratio": ratio, "feasibility": feas_f, "tag": "min_so_far"})
                print(f'  ! k={k:>7} mss={mss_f:.4e} ratio={ratio:.3f} feas={feas_f:.3f} (NEW MIN)', flush=True)
        if k - last_print_k >= 1000:
            elapsed = time.time() - t0
            print(f'  k={k:>7} mss={mss_f:.4e} ratio={ratio:.3f} feas={feas_f:.3f}  min={min_ratio:.3f}@k={min_ratio_k}  t={elapsed:.0f}s', flush=True)
            rows.append({"k": k, "mss": mss_f, "ratio": ratio, "feasibility": feas_f})
            last_print_k = k
            if k % 10000 == 0:
                with open(f"/workspace/Packing/results/inv_fast_{heuristic}_chk.json", "w") as f:
                    json.dump({"heuristic": heuristic, "rows": rows,
                               "min_ratio": min_ratio, "min_ratio_k": min_ratio_k,
                               "last_k": k}, f)
    out = f"/workspace/Packing/results/inv_fast_{heuristic}_N{N_max}.json"
    with open(out, "w") as f:
        json.dump({"heuristic": heuristic, "rows": rows,
                   "min_ratio": min_ratio, "min_ratio_k": min_ratio_k}, f)
    print(f'Saved {out}; min_ratio={min_ratio:.3f}@k={min_ratio_k}')


if __name__ == "__main__":
    h = sys.argv[1] if len(sys.argv) > 1 else "BSSF"
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
    main(h, N)
