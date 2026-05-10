"""Track the invariant max_min_side(k) * (k+1) over k, looking for trends."""
import sys
sys.set_int_max_str_digits(0)
sys.path.insert(0, "/workspace/Packing")
import json
from fractions import Fraction as F
from src.fast_packer import FastMaxRectsPacker


def trajectory(heuristic, N_max):
    p = FastMaxRectsPacker(W=F(1), H=F(1))
    p.place_explicit(1, F(0), F(0), rotated=False)
    rows = []
    last_log_k = 1
    for k in range(2, N_max + 1):
        ok = p.place(k, allow_rotate=True, heuristic=heuristic)
        if ok is None:
            print(f"  FAIL at k={k}")
            break
        # cheap stat per step
        if k - last_log_k >= max(1, k // 100):
            mss = max((min(fr.w, fr.h) for fr in p.free), default=F(0))
            mss_other = max((max(fr.w, fr.h) for fr in p.free if min(fr.w, fr.h) == mss), default=F(0))
            ratio = float(mss * (k + 1))
            rows.append({
                "k": k,
                "max_min_side": float(mss),
                "max_min_side_x_kp1": ratio,
                "n_free": len(p.free),
            })
            last_log_k = k
    return rows, p


if __name__ == "__main__":
    h = sys.argv[1] if len(sys.argv) > 1 else "BAF"
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 5000
    rows, p = trajectory(h, N)
    out_path = f"/workspace/Packing/results/inv_traj_{h}_N{N}.json"
    with open(out_path, "w") as f:
        json.dump(rows, f)
    if rows:
        ratios = [r["max_min_side_x_kp1"] for r in rows]
        print(f"  k_max with ratio<2 : {min(r['k'] for r in rows if r['max_min_side_x_kp1']<2) if any(r['max_min_side_x_kp1']<2 for r in rows) else 'never'}")
        print(f"  Min ratio: {min(ratios):.4f}")
        print(f"  Max ratio: {max(ratios):.4f}")
        print(f"  Mean ratio: {sum(ratios)/len(ratios):.4f}")
        print(f"  Last sample: k={rows[-1]['k']}, ratio={rows[-1]['max_min_side_x_kp1']:.4f}")
    print(f"  Saved {len(rows)} samples to {out_path}")
