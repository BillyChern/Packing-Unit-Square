"""Experiment driver for Moser packing.

Reports σ = side of smallest [0, σ]² that contains the packing of R_1..R_N
under various heuristics, with rigorous exact-arithmetic verification.

Outputs JSON to results/, SVG to figures/.
"""

from __future__ import annotations
import json
import os
import time
from fractions import Fraction
from typing import Dict, List, Optional, Tuple

from .geometry import (
    F,
    Placement,
    bounding_extent,
    moser_dims,
    moser_prefix_area,
    total_area,
    verify_packing,
)
from .algorithms import (
    MaxRectsPacker,
    pack_moser_prefix_maxrects,
)
from .visualize import save_svg


HEURISTICS = ("BSSF", "BAF", "BLSF", "BL")


def fit_into_unit_square(
    N: int, heuristic: str = "BSSF", side: F = F(1)
) -> Tuple[List[Placement], List[int], F, F]:
    """Try to pack R_1..R_N into [0, side]². Returns
    (placements, failed_ks, used_X, used_Y)."""
    placed, packer, failed = pack_moser_prefix_maxrects(
        N, side=side, heuristic=heuristic, place_R1_first=True
    )
    used_X, used_Y = bounding_extent(placed)
    return placed, failed, used_X, used_Y


def smallest_side_containing(
    N: int, heuristic: str = "BSSF",
    side_hi: F = F(2), side_lo: F = F(1),
    tol: F = F(1, 10**6),
) -> Tuple[F, List[Placement]]:
    """Binary-search the smallest σ such that MaxRects packs R_1..R_N into
    [0, σ]². Heuristic-dependent — does not give a true minimum, only an
    algorithmic minimum.

    σ_lo: known infeasible lower bound (we test if it succeeds; if so, we
    pull it lower). σ_hi: known feasible upper.
    """
    # Try increasing side until success, then binary-search.
    placed = []
    while True:
        placed, failed, _, _ = fit_into_unit_square(N, heuristic, side_hi)
        if not failed:
            break
        side_hi *= F(2)
    # Now have feasible side_hi. Try to shrink.
    while side_hi - side_lo > tol:
        mid = (side_hi + side_lo) / 2
        try_placed, failed, _, _ = fit_into_unit_square(N, heuristic, mid)
        if not failed:
            side_hi = mid
            placed = try_placed
        else:
            side_lo = mid
    return side_hi, placed


def sweep_baseline(
    Ns: List[int],
    out_dir: str = "results",
    fig_dir: str = "figures",
) -> Dict:
    """For each N, try all heuristics at side=1 and report success/failure
    and bounding box."""
    os.makedirs(out_dir, exist_ok=True)
    os.makedirs(fig_dir, exist_ok=True)
    rows = []
    for N in Ns:
        for h in HEURISTICS:
            t0 = time.time()
            placed, failed, X, Y = fit_into_unit_square(N, heuristic=h, side=F(1))
            elapsed = time.time() - t0
            ok, errs = verify_packing(placed, F(1), F(1))
            row = {
                "N": N,
                "heuristic": h,
                "success_in_unit_square": (len(failed) == 0),
                "n_failed": len(failed),
                "first_failed_k": failed[0] if failed else None,
                "bbox_W": str(X),
                "bbox_H": str(Y),
                "bbox_W_float": float(X),
                "bbox_H_float": float(Y),
                "verify_ok": ok,
                "verify_errors": errs[:5],
                "n_placed": len(placed),
                "elapsed_sec": round(elapsed, 3),
                "area_placed": float(total_area(placed)),
                "area_target": float(moser_prefix_area(N)),
            }
            rows.append(row)
            print(
                f"N={N:>5} h={h} success={row['success_in_unit_square']!s:>5} "
                f"failed={len(failed):>4} bbox={float(X):.6f}x{float(Y):.6f} "
                f"placed={len(placed):>5} t={elapsed:.1f}s"
            )
            # Save SVG for manageable sizes
            if N <= 2000 and not failed:
                fname = f"{fig_dir}/pack_N{N}_{h}_unit.svg"
                save_svg(
                    fname, placed, F(1), F(1),
                    title=f"N={N} {h} σ=1.0  (placed={len(placed)})",
                )
    out = {"rows": rows}
    with open(f"{out_dir}/baseline_sweep.json", "w") as f:
        json.dump(out, f, indent=2)
    return out


def find_max_N_in_unit_square(
    heuristic: str = "BSSF",
    N_start: int = 1,
    N_max: int = 5000,
) -> Tuple[int, List[Placement]]:
    """Find the largest N such that R_1..R_N can be packed into [0,1]²
    by `heuristic`. Returns (N_max_found, placements)."""
    p = MaxRectsPacker(W=F(1), H=F(1))
    p.place_explicit(1, F(0), F(0), rotated=False)
    last_ok_N = 1
    placed_at_last_ok = list(p.placed)
    for k in range(2, N_max + 1):
        if p.place(k, allow_rotate=True, heuristic=heuristic) is None:
            return last_ok_N, placed_at_last_ok
        last_ok_N = k
        if k % 50 == 0 or k <= 10:
            placed_at_last_ok = list(p.placed)
    return last_ok_N, list(p.placed)


def report_max_N(
    heuristics=HEURISTICS, N_max: int = 2000, out_path: str = "results/max_N.json"
) -> Dict:
    rows = []
    best = {"max_N": 0}
    for h in heuristics:
        t0 = time.time()
        n_ok, placed = find_max_N_in_unit_square(h, N_max=N_max)
        elapsed = time.time() - t0
        ok, errs = verify_packing(placed, F(1), F(1))
        row = {
            "heuristic": h,
            "max_N_in_unit_square": n_ok,
            "verify_ok": ok,
            "errors_sample": errs[:5],
            "elapsed_sec": round(elapsed, 2),
        }
        print(
            f"h={h} max_N={n_ok} (sigma_bound={1 + 1/(n_ok+1):.6f}={n_ok+2}/{n_ok+1}) "
            f"elapsed={elapsed:.1f}s"
        )
        rows.append(row)
        if n_ok > best["max_N"]:
            best = {**row, "max_N": n_ok, "placed": placed}
    out = {"rows": rows, "best_heuristic": best["heuristic"], "best_max_N": best["max_N"]}
    if "placed" in best:
        save_svg(
            "figures/best_unit_square.svg",
            best["placed"],
            F(1),
            F(1),
            title=f"best heuristic: {best['heuristic']} max_N={best['max_N']}, σ_bound={best['max_N']+2}/{best['max_N']+1}",
        )
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, "w") as f:
        json.dump({k: v for k, v in out.items() if k != "best_heuristic" or True} | {
            "best_heuristic": best["heuristic"]
        }, f, indent=2, default=str)
    return out


if __name__ == "__main__":
    # Smoke test
    placed, failed, X, Y = fit_into_unit_square(20, "BSSF")
    print(f"N=20: placed={len(placed)} failed={failed} bbox=({X},{Y})")
    ok, errs = verify_packing(placed, F(1), F(1))
    print(f"verify_ok={ok}")
