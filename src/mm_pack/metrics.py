"""Metrics for the calibrated state: S_LRP, S_norm, S_ep, P_ep, aspect, width-ratios."""

from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from typing import List, Optional, Tuple

from .geometry import FreeBox, FreeBoxKind

F = Fraction


@dataclass(frozen=True)
class Metrics:
    t: int
    S_LRP: F                     # area of LRP (or 0 if none)
    S_norm: F                    # total area of normal boxes
    S_ep: F                      # total area of endpoint boxes
    P_ep: F                      # total semiperimeter of endpoint boxes
    LRP_aspect: F                # aspect of LRP (1 if no LRP)
    normal_width_ratio_min: Optional[F] = None
    normal_width_ratio_max: Optional[F] = None
    n_normal: int = 0
    n_endpoint: int = 0


def compute_metrics(
    t: int,
    LRP: Optional[FreeBox],
    normal_boxes: List[FreeBox],
    endpoint_boxes: List[FreeBox],
    gamma_num: int = 4,
    gamma_den: int = 3,
) -> Metrics:
    s_lrp = LRP.area if LRP else F(0)
    aspect = LRP.aspect if (LRP and LRP.area > 0) else F(1)
    s_norm = sum((b.area for b in normal_boxes), F(0))
    s_ep = sum((b.area for b in endpoint_boxes), F(0))
    p_ep = sum((b.semiperim for b in endpoint_boxes), F(0))

    # Normal-width ratio: w(B_k) * k^γ should be Θ(1).
    # We compute (w(B_k) * k^gamma_num)^gamma_den and compare to 1, but for
    # diagnostic purposes we just compute the rational ratio
    #   r_k = w(B_k) * k^γ ≈ w(B_k) * (k^gamma_num)^(1/gamma_den)
    # using the integer ⌊k^γ⌋ ≈ ⌊(k^gamma_num)^(1/gamma_den)⌋ from rect_sequence.
    ratios: List[F] = []
    if normal_boxes:
        for B in normal_boxes:
            k = B.birth_index
            if k is None or k < 1:
                continue
            # k^γ ≈ floor of integer (gamma_den)-th root of k^gamma_num
            m = k ** gamma_num
            lo, hi = 1, m
            while lo < hi:
                mid = (lo + hi + 1) // 2
                if mid ** gamma_den <= m:
                    lo = mid
                else:
                    hi = mid - 1
            k_gamma_floor = lo  # integer ≤ k^γ
            # ratio = w(B_k) * k^γ ≥ w(B_k) * k_gamma_floor
            ratios.append(B.w * k_gamma_floor)
    rmin = min(ratios) if ratios else None
    rmax = max(ratios) if ratios else None

    return Metrics(
        t=t,
        S_LRP=s_lrp,
        S_norm=s_norm,
        S_ep=s_ep,
        P_ep=p_ep,
        LRP_aspect=aspect,
        normal_width_ratio_min=rmin,
        normal_width_ratio_max=rmax,
        n_normal=len(normal_boxes),
        n_endpoint=len(endpoint_boxes),
    )


__all__ = ["Metrics", "compute_metrics"]
