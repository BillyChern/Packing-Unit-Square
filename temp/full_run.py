"""Full run: push N for one heuristic + L-strip extension + certify + visualize.

Single-process to avoid stale-state issues.
"""
import sys, os, time, json
sys.set_int_max_str_digits(0)  # allow arbitrarily large rationals in JSON
sys.path.insert(0, "/workspace/Packing")

from fractions import Fraction as F
from src.fast_packer import FastMaxRectsPacker
from src.geometry import F as Frac, Placement, verify_packing
from src.lstrip import lstrip_inequalities_certify, Lstrip_extend_tight
from src.visualize import save_svg


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


def main(heuristic="BSSF", N_max=2000, max_k_for_verify=None, J_total=4):
    if max_k_for_verify is None:
        # Materialize a few more rows of tail for verification
        max_k_for_verify = N_max * 4 + 1000
    print(f"=== Full run: heuristic={heuristic} N_max={N_max} ===", flush=True)
    os.makedirs("/workspace/Packing/results", exist_ok=True)
    os.makedirs("/workspace/Packing/figures", exist_ok=True)

    p = FastMaxRectsPacker(W=Frac(1), H=Frac(1))
    p.place_explicit(1, Frac(0), Frac(0), rotated=False)

    t0 = time.time()
    last_ok = 1
    for k in range(2, N_max + 1):
        if p.place(k, allow_rotate=True, heuristic=heuristic) is None:
            print(
                f"  [{heuristic}] FAIL at k={k}, free={len(p.free)}, t={time.time()-t0:.1f}s",
                flush=True,
            )
            break
        last_ok = k
        if k % 200 == 0:
            print(f"  k={k}/{N_max} free={len(p.free)} t={time.time()-t0:.1f}s", flush=True)

    print(f"\n  --> Successfully placed first {last_ok} into [0,1]²")
    sigma_finite = (last_ok + 2, last_ok + 1)
    print(f"  σ-bound (finite N): {sigma_finite[0]}/{sigma_finite[1]} = {sigma_finite[0]/sigma_finite[1]:.10f}")
    if sigma_finite[0] / sigma_finite[1] < 501 / 500:
        print(f"  ★ BEATS Bálint's 501/500 = {501/500:.10f}")

    # Verify the prefix
    t0 = time.time()
    ok, errs = verify_packing(p.placed, Frac(1), Frac(1))
    print(f"  Prefix verify_ok={ok} time={time.time()-t0:.1f}s")
    assert ok, f"Prefix verification failed: {errs[:3]}"

    # Now extend via L-strip
    n = last_ok + 1
    print(f"\nL-strip extension with n={n}, J={J_total}, max_k={max_k_for_verify}")
    ineq = lstrip_inequalities_certify(n, J=J_total)
    if not ineq["all_ok"]:
        print(f"  L-strip inequalities FAIL: {ineq}", flush=True)
        return
    print(f"  inequalities all OK; sigma = {ineq['sigma']}")

    t0 = time.time()
    full, sigma, total_area = Lstrip_extend_tight(
        p.placed, n, J_total=J_total, max_k=max_k_for_verify
    )
    print(f"  Materialized {len(full)} placements in {time.time()-t0:.1f}s")

    t0 = time.time()
    full_ok, full_errs = verify_packing(full, sigma, sigma)
    print(f"  Full verify_ok={full_ok} time={time.time()-t0:.1f}s")
    if not full_ok:
        print(f"  errors: {full_errs[:5]}")

    # Save
    summary = {
        "heuristic": heuristic,
        "max_N_in_unit_square": last_ok,
        "n_for_lstrip": n,
        "sigma": f"{sigma.numerator}/{sigma.denominator}",
        "sigma_float": float(sigma),
        "Bálint_501_500": 501/500,
        "improvement": 501/500 - float(sigma),
        "verified_finite_prefix_to_k": max(p.k for p in full),
        "construction_proves_for_all_k": ineq["all_ok"],
        "verify_full_ok": full_ok,
        "lstrip_inequalities": ineq,
        "k_count_materialized": len(full),
    }
    summary_path = f"/workspace/Packing/results/full_{heuristic}_N{last_ok}.json"
    with open(summary_path, "w") as f:
        json.dump(summary, f, indent=2, default=str)

    # Skip dumping full placements (huge file). Only save summary.
    placements_path = None

    # Skip SVG too (large file).
    fig_path = None
    print(f"\nSaved: {summary_path}")


if __name__ == "__main__":
    h = sys.argv[1] if len(sys.argv) > 1 else "BSSF"
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    main(heuristic=h, N_max=N)
