"""Look for inductive patterns in MaxRects packings.

The goal: find a reusable structure that might extend to all N — i.e.,
data on whether free regions retain "good" properties as N grows.
"""
import json
import sys
sys.path.insert(0, "/workspace/Packing")
from fractions import Fraction as F
from src.fast_packer import FastMaxRectsPacker, FastFreeRect
from src.geometry import Placement


def free_rect_stats(packer: FastMaxRectsPacker, k: int):
    """At step k, summarise the free rect distribution."""
    if not packer.free:
        return None
    sizes = [(min(fr.wf, fr.hf), max(fr.wf, fr.hf), fr.wf * fr.hf) for fr in packer.free]
    sizes.sort(reverse=True, key=lambda t: t[2])  # by area desc
    largest = sizes[0]
    smallest = sizes[-1]
    # min-side that can hold next R_{k+1}
    next_min_side = 1 / (k + 2)
    n_can_hold = sum(1 for s in sizes if s[1] >= next_min_side and s[0] >= 1/(k+2))
    return {
        "k": k,
        "n_free": len(sizes),
        "largest_min_side": largest[0],
        "largest_max_side": largest[1],
        "largest_area": largest[2],
        "smallest_min_side": smallest[0],
        "smallest_area": smallest[2],
        "n_can_hold_next": n_can_hold,
        "max_min_side": max(s[0] for s in sizes),
        "total_free_area": sum(s[2] for s in sizes),
    }


def trajectory_analysis(heuristic="BSSF", N_max=2000, sample_every=100):
    """Track free-region statistics over time."""
    p = FastMaxRectsPacker(W=F(1), H=F(1))
    p.place_explicit(1, F(0), F(0), rotated=False)
    rows = []
    for k in range(2, N_max + 1):
        placement = p.place(k, allow_rotate=True, heuristic=heuristic)
        if placement is None:
            print(f"  FAIL at k={k}")
            break
        if k % sample_every == 0:
            stats = free_rect_stats(p, k)
            print(f"  k={k:>5} free={stats['n_free']:>5} "
                  f"max_min_side={stats['max_min_side']:.4e} "
                  f"can_hold_next={stats['n_can_hold_next']:>4} "
                  f"largest_area={stats['largest_area']:.4e}")
            rows.append(stats)
    return rows


if __name__ == "__main__":
    h = sys.argv[1] if len(sys.argv) > 1 else "BSSF"
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    rows = trajectory_analysis(h, N)
    out_path = f"/workspace/Packing/results/trajectory_{h}_N{N}.json"
    with open(out_path, "w") as f:
        json.dump(rows, f, indent=2)
    print(f"Saved {out_path}")
