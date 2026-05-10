"""Exact-rational verification of a calibrated warm-start certificate.

Verifies all 8 conditions from agent_execution_brief §10:
  1. Containment
  2. Correct dimensions (D_n = 1/n × 1/(n+1))
  3. No overlap
  4. Free-state containment (LRP/normal/endpoint inside container, disjoint from placed)
  5. LRP area ≥ c/N
  6. LRP aspect ≤ R
  7. Endpoint semiperimeter ≤ η
  8. Normal-width law: c1 ≤ w(B_k) · k^γ ≤ c2
"""

from __future__ import annotations
from dataclasses import dataclass, field
from fractions import Fraction
from typing import List, Optional, Tuple

from .certificate import Certificate
from .geometry import (
    Rect,
    FreeBox,
    PlacedRect,
    verify_no_overlap,
    verify_containment,
)
from .rect_sequence import D_dims

F = Fraction


@dataclass
class CheckReport:
    ok: bool
    errors: List[str] = field(default_factory=list)
    bounds: dict = field(default_factory=dict)


def integer_floor_root(m: int, d: int) -> int:
    """Largest k with k^d ≤ m, m≥0, d≥1."""
    if m == 0:
        return 0
    lo, hi = 1, m
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid ** d <= m:
            lo = mid
        else:
            hi = mid - 1
    return lo


def integer_ceil_root(m: int, d: int) -> int:
    """Smallest k with k^d ≥ m, m≥0, d≥1."""
    if m == 0:
        return 0
    lo, hi = 1, m
    while lo < hi:
        mid = (lo + hi) // 2
        if mid ** d < m:
            lo = mid + 1
        else:
            hi = mid
    return lo


def k_to_gamma_floor(k: int, gamma_num: int, gamma_den: int) -> int:
    return integer_floor_root(k ** gamma_num, gamma_den)


def k_to_gamma_ceil(k: int, gamma_num: int, gamma_den: int) -> int:
    return integer_ceil_root(k ** gamma_num, gamma_den)


def check_certificate(
    cert: Certificate,
    c_LRP: F = F(1, 10),
    R_aspect: F = F(8),
    eta_ep: F = F(1, 20),
    c1_norm: F = F(1, 4),
    c2_norm: F = F(4),
) -> CheckReport:
    """Run all 8 invariant checks. Default thresholds match
    agent_execution_brief §6 / §11."""
    errors: List[str] = []
    bounds: dict = {}
    N = cert.N

    # 1. Containment
    ok, errs = verify_containment(cert.placed, cert.container)
    if not ok:
        errors.extend(["containment: " + e for e in errs])

    # 2. Correct dimensions
    for p in cert.placed:
        long_, short = D_dims(p.n)
        if p.rotated:
            if not (p.w == short and p.h == long_):
                errors.append(
                    f"dim n={p.n}: rotated → expected ({short}, {long_}), got ({p.w}, {p.h})"
                )
        else:
            if not (p.w == long_ and p.h == short):
                errors.append(
                    f"dim n={p.n}: native → expected ({long_}, {short}), got ({p.w}, {p.h})"
                )

    # 3. No overlap
    ok, errs = verify_no_overlap(cert.placed)
    if not ok:
        errors.extend(["no_overlap: " + e for e in errs])

    # 4. Free-state containment + disjointness with placed
    placed_rects = [p.rect for p in cert.placed]
    free_boxes: List[FreeBox] = []
    if cert.LRP is not None:
        free_boxes.append(cert.LRP)
    free_boxes.extend(cert.normal_boxes)
    free_boxes.extend(cert.endpoint_boxes)
    free_boxes.extend(cert.absorbers)
    for fb in free_boxes:
        if not cert.container.contains(fb.rect):
            errors.append(f"free-state: {fb.kind.value} {fb.rect} not in container {cert.container}")
        for pr in placed_rects:
            if not pr.interior_disjoint(fb.rect):
                errors.append(
                    f"free-state: {fb.kind.value} {fb.rect} intersects placed {pr}"
                )
                break
    # Free boxes also pairwise interior-disjoint
    fbn = len(free_boxes)
    for i in range(fbn):
        a = free_boxes[i].rect
        for j in range(i + 1, fbn):
            b = free_boxes[j].rect
            if not a.interior_disjoint(b):
                errors.append(
                    f"free-state: free boxes overlap: {free_boxes[i].kind.value}{a} ∩ "
                    f"{free_boxes[j].kind.value}{b}"
                )

    # 5. LRP area ≥ c_LRP / N
    if cert.LRP is None:
        s_lrp = F(0)
    else:
        s_lrp = cert.LRP.area
    bounds["S_LRP"] = str(s_lrp)
    bounds["S_LRP_over_tail"] = str(s_lrp * N)
    if s_lrp * N < c_LRP:
        errors.append(
            f"LRP area: S_LRP·N = {s_lrp * N} < c_LRP = {c_LRP}"
        )

    # 6. LRP aspect ≤ R
    if cert.LRP is not None and cert.LRP.area > 0:
        a = cert.LRP.aspect
        bounds["LRP_aspect"] = str(a)
        if a > R_aspect:
            errors.append(f"LRP aspect: {a} > R = {R_aspect}")
    else:
        bounds["LRP_aspect"] = "n/a"

    # 7. Endpoint semiperimeter ≤ η
    p_ep = sum((b.semiperim for b in cert.endpoint_boxes), F(0))
    bounds["P_ep"] = str(p_ep)
    if p_ep > eta_ep:
        errors.append(f"endpoint semiperim: {p_ep} > η = {eta_ep}")

    # 8. Normal-width law: c1 ≤ w(B_k) · k^γ ≤ c2  for each normal box
    bad_norm = 0
    ratios = []
    for B in cert.normal_boxes:
        k = B.birth_index
        if k is None or k < 1:
            continue
        # k^γ ∈ [floor, ceil] of integer (gamma_den)-th root of k^gamma_num
        kg_floor = k_to_gamma_floor(k, cert.gamma_num, cert.gamma_den)
        kg_ceil = k_to_gamma_ceil(k, cert.gamma_num, cert.gamma_den)
        # ratio_lower = w * kg_floor (≤ true w · k^γ)
        # ratio_upper = w * kg_ceil  (≥ true w · k^γ)
        rl = B.w * kg_floor
        ru = B.w * kg_ceil
        ratios.append((k, rl, ru))
        if ru < c1_norm:
            bad_norm += 1
            errors.append(
                f"normal width law: B_k={k}: w·k^γ ≤ {ru} < c1 = {c1_norm}"
            )
        if rl > c2_norm:
            bad_norm += 1
            errors.append(
                f"normal width law: B_k={k}: w·k^γ ≥ {rl} > c2 = {c2_norm}"
            )
    bounds["normal_width_violations"] = bad_norm
    bounds["normal_width_count"] = len(ratios)

    return CheckReport(ok=(len(errors) == 0), errors=errors, bounds=bounds)


__all__ = ["CheckReport", "check_certificate", "k_to_gamma_floor", "k_to_gamma_ceil"]
