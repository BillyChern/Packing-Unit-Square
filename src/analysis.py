"""Pattern detection and analysis on Moser packings."""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction
from typing import Dict, Iterable, List, Tuple

from .geometry import F, Placement


def by_k(placements: Iterable[Placement]) -> Dict[int, Placement]:
    return {p.k: p for p in placements}


def trajectory(placements: Iterable[Placement]) -> List[Tuple[int, float, float, float, float, bool]]:
    """For each k, return (k, x, y, w, h, rotated) sorted by k."""
    out = []
    for p in sorted(placements, key=lambda q: q.k):
        out.append((p.k, float(p.x), float(p.y), float(p.w), float(p.h), p.rotated))
    return out


def grid_zone(placements: Iterable[Placement], n_zones: int = 10
              ) -> Dict[Tuple[int, int], List[int]]:
    """Bin placements by (zone_x, zone_y) to see which zones contain which k's."""
    zones: Dict[Tuple[int, int], List[int]] = defaultdict(list)
    for p in placements:
        cx = float(p.x + p.w / 2)
        cy = float(p.y + p.h / 2)
        zx = min(int(cx * n_zones), n_zones - 1)
        zy = min(int(cy * n_zones), n_zones - 1)
        zones[(zx, zy)].append(p.k)
    return zones


def k_range_per_zone(placements, n_zones=8):
    """For each grid zone, return min/max k of placements centred there."""
    zones = grid_zone(placements, n_zones)
    rows = []
    for (zx, zy), ks in zones.items():
        rows.append({
            "zone": (zx, zy),
            "n_k": len(ks),
            "min_k": min(ks),
            "max_k": max(ks),
            "median_k": sorted(ks)[len(ks) // 2],
        })
    return rows


def rotation_stats(placements):
    rot = sum(1 for p in placements if p.rotated)
    nat = sum(1 for p in placements if not p.rotated)
    return {"rotated": rot, "native": nat, "ratio_rotated": rot / max(rot + nat, 1)}


def x_distribution(placements):
    """For each k, x position. Compare to candidate analytic formulas."""
    rows = []
    for p in sorted(placements, key=lambda q: q.k):
        rows.append({
            "k": p.k,
            "x": float(p.x),
            "y": float(p.y),
            "w": float(p.w),
            "h": float(p.h),
        })
    return rows


def detect_horizontal_layers(placements, eps=1e-9) -> List[float]:
    """Return distinct y-coordinates (top-of-rect) used. Many duplicates →
    a 'shelf' structure."""
    ys = sorted({float(p.y) for p in placements})
    layers = []
    for y in ys:
        if not layers or y - layers[-1] > eps:
            layers.append(y)
    return layers


def empty_corners(placements, side: Fraction = F(1)
                  ) -> List[Tuple[Fraction, Fraction, Fraction, Fraction]]:
    """Approximate the unfilled L-shape regions (concave corners). Returns
    list of bounding rectangles of remaining free space."""
    # Build a grid of occupancy
    # quick heuristic: scan x-monotone events
    return []  # placeholder
