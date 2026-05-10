"""Compute a disjoint rectangular partition of `container \\ placed_rects`.

Strategy: x-slab decomposition.

  1. Collect all distinct x-coordinates from container + placed rect edges.
  2. For each slab [x_i, x_{i+1}], find the y-intervals NOT covered by any placed
     rect whose x-extent contains the slab.
  3. Output one rectangle per (slab, y-gap).

The output rectangles tile the empty region exactly (disjoint interiors, union
equals empty region). The number of output pieces is O(n²) in the worst case
(n = #placed) but typically much less.
"""

from __future__ import annotations
from fractions import Fraction
from typing import List, Tuple

from .geometry import Rect, PlacedRect

F = Fraction


def rectangulate_complement(
    container: Rect, placed: List[PlacedRect]
) -> List[Rect]:
    """Return a list of disjoint Rects that tile `container \\ ⋃ placed`.

    The placed rects are assumed pairwise interior-disjoint and inside container.
    """
    if not placed:
        return [container] if container.area > 0 else []

    xs: List[F] = sorted({container.x0, container.x1, *(p.x0 for p in placed), *(p.x1 for p in placed)})
    out: List[Rect] = []
    for i in range(len(xs) - 1):
        x_lo = xs[i]
        x_hi = xs[i + 1]
        if x_lo >= x_hi:
            continue
        # Slab [x_lo, x_hi]. Find placed rects whose x-range covers the slab.
        # (We sliced at every placed-rect x-edge, so a placed rect either
        # fully covers the slab in x or does not touch it.)
        intervals: List[Tuple[F, F]] = []
        for p in placed:
            if p.x0 <= x_lo and p.x1 >= x_hi:
                intervals.append((p.y0, p.y1))
        # Compute y-gaps within [container.y0, container.y1].
        intervals.sort()
        merged: List[Tuple[F, F]] = []
        for y0, y1 in intervals:
            if merged and y0 <= merged[-1][1]:
                merged[-1] = (merged[-1][0], max(merged[-1][1], y1))
            else:
                merged.append((y0, y1))
        # Gaps
        cursor = container.y0
        for y0, y1 in merged:
            if y0 > cursor:
                out.append(Rect(x_lo, cursor, x_hi, y0))
            cursor = max(cursor, y1)
        if cursor < container.y1:
            out.append(Rect(x_lo, cursor, x_hi, container.y1))
    return out


def merge_horizontal(rects: List[Rect]) -> List[Rect]:
    """Merge horizontally-adjacent rects with identical [y0, y1] into one."""
    if not rects:
        return rects
    # Group by (y0, y1)
    from collections import defaultdict
    groups = defaultdict(list)
    for r in rects:
        groups[(r.y0, r.y1)].append(r)
    out: List[Rect] = []
    for (y0, y1), group in groups.items():
        group.sort(key=lambda r: r.x0)
        cur_x0 = group[0].x0
        cur_x1 = group[0].x1
        for r in group[1:]:
            if r.x0 == cur_x1:
                cur_x1 = r.x1
            else:
                out.append(Rect(cur_x0, y0, cur_x1, y1))
                cur_x0 = r.x0
                cur_x1 = r.x1
        out.append(Rect(cur_x0, y0, cur_x1, y1))
    return out


def merge_vertical(rects: List[Rect]) -> List[Rect]:
    """Merge vertically-adjacent rects with identical [x0, x1] into one."""
    if not rects:
        return rects
    from collections import defaultdict
    groups = defaultdict(list)
    for r in rects:
        groups[(r.x0, r.x1)].append(r)
    out: List[Rect] = []
    for (x0, x1), group in groups.items():
        group.sort(key=lambda r: r.y0)
        cur_y0 = group[0].y0
        cur_y1 = group[0].y1
        for r in group[1:]:
            if r.y0 == cur_y1:
                cur_y1 = r.y1
            else:
                out.append(Rect(x0, cur_y0, x1, cur_y1))
                cur_y0 = r.y0
                cur_y1 = r.y1
        out.append(Rect(x0, cur_y0, x1, cur_y1))
    return out


def rectangulate_simplified(
    container: Rect, placed: List[PlacedRect], merge_passes: int = 4
) -> List[Rect]:
    """Compute disjoint rectangulation, then run a few merge passes to
    consolidate adjacent rects (reduces the count from O(n²) toward O(n)).
    """
    rects = rectangulate_complement(container, placed)
    for _ in range(merge_passes):
        n0 = len(rects)
        rects = merge_horizontal(rects)
        rects = merge_vertical(rects)
        if len(rects) == n0:
            break
    return rects


__all__ = [
    "rectangulate_complement",
    "rectangulate_simplified",
    "merge_horizontal",
    "merge_vertical",
]
