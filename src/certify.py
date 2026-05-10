"""Generate a verified packing certificate.

Given a packing of R_1..R_N in [0, 1]², this module:
  1. Verifies it (exact arithmetic).
  2. Extends it via Lstrip_extend_tight to ALL R_k in [0, 1+1/(N+1)]².
  3. Writes a JSON certificate + SVG figure.

The certificate has enough information for a third party to reproduce and
re-verify (every placement listed as numerator/denominator pairs).
"""

from __future__ import annotations
import json
import os
from fractions import Fraction
from typing import Iterable, List

from .geometry import F, Placement, verify_packing, total_area
from .lstrip import Lstrip_extend_tight, Lstrip_extend, lstrip_inequalities_certify
from .visualize import save_svg


def serialize_placements(placements: Iterable[Placement]) -> list:
    rows = []
    for p in placements:
        rows.append({
            "k": p.k,
            "x": [p.x.numerator, p.x.denominator],
            "y": [p.y.numerator, p.y.denominator],
            "w": [p.w.numerator, p.w.denominator],
            "h": [p.h.numerator, p.h.denominator],
            "rotated": p.rotated,
        })
    return rows


def deserialize_placements(rows) -> List[Placement]:
    out = []
    for r in rows:
        x = F(r["x"][0], r["x"][1])
        y = F(r["y"][0], r["y"][1])
        out.append(Placement(k=r["k"], x=x, y=y, rotated=r["rotated"]))
    return out


def certify(
    prefix_placements: List[Placement],
    N: int,
    out_dir: str = "results/certificate",
    fig_dir: str = "figures",
    J_total: int = 30,
    max_k: int = 50000,
    use_tight: bool = True,
) -> dict:
    """N is the largest k packed in the unit square (so prefix has k=1..N).

    The L-strip construction is proved correct for ALL k by computing the
    inequalities. We materialise rectangles up to k = max_k for verification
    and visualization.
    """
    os.makedirs(out_dir, exist_ok=True)
    os.makedirs(fig_dir, exist_ok=True)

    n = N + 1
    # Prove construction soundness via exact inequalities
    inequalities = lstrip_inequalities_certify(n, J_total)
    if not inequalities["all_ok"]:
        raise RuntimeError(
            f"L-strip inequalities fail for n={n}: {inequalities}"
        )
    # Extend, materializing up to max_k for verification
    if use_tight:
        full, sigma, total = Lstrip_extend_tight(
            prefix_placements, n, J_total=J_total, max_k=max_k
        )
        scheme = "tight"
    else:
        full, sigma, total = Lstrip_extend(prefix_placements, n, J_total=J_total)
        scheme = "loose"

    ok, errs = verify_packing(full, sigma, sigma)
    last_k = max(p.k for p in full)
    sigma_str = f"{sigma.numerator}/{sigma.denominator}"

    cert = {
        "problem": "Moser rectangle packing",
        "claim": f"R_1..R_∞ pack into [0, σ]² with σ = {sigma_str} ({float(sigma):.10f})",
        "verified_finite_prefix_to_k": last_k,
        "construction_proves_for_all_k": inequalities["all_ok"],
        "N_prefix_in_unit_square": N,
        "n_for_lstrip": n,
        "max_k_materialized": max_k,
        "J_total_rows_used": J_total,
        "scheme": scheme,
        "sigma_numer": sigma.numerator,
        "sigma_denom": sigma.denominator,
        "sigma_float": float(sigma),
        "k_count_materialized": len(full),
        "total_area_materialized": [total.numerator, total.denominator],
        "verify_ok_finite": ok,
        "errors_sample": errs[:5],
        "n_prefix_placements": len(prefix_placements),
        "lstrip_inequalities": inequalities,
        "comparison": {
            "Bálint_501_500": float(F(501, 500)),
            "Jennings_133_132": float(F(133, 132)),
            "our_sigma": float(sigma),
            "improvement_vs_Bálint": float(F(501, 500) - sigma),
        },
    }
    with open(os.path.join(out_dir, "summary.json"), "w") as f:
        json.dump(cert, f, indent=2, default=str)

    # Save full placements (compact form)
    with open(os.path.join(out_dir, "placements.json"), "w") as f:
        json.dump({
            "sigma": sigma_str,
            "placements": serialize_placements(full),
        }, f)

    # Visualize
    svg_path = os.path.join(fig_dir, f"certified_N{N}_sigma_{sigma.numerator}_{sigma.denominator}.svg")
    save_svg(
        svg_path, full, sigma, sigma,
        title=f"Moser packing: R_1..R_{last_k} in σ²={sigma_str}² ({len(full)} rects)",
        label_max_k=20,
    )

    print(f"=== Certificate generated ===")
    print(f"  N (prefix in unit square): {N}")
    print(f"  σ = {sigma_str} = {float(sigma):.10f}")
    print(f"  k packed: 1..{last_k}  (total {len(full)})")
    print(f"  verify_ok = {ok}")
    print(f"  vs Bálint 501/500 = {501/500}: {'BETTER' if sigma < F(501, 500) else 'NOT BETTER'}")
    print(f"  files: {out_dir}/summary.json, {svg_path}")
    return cert
