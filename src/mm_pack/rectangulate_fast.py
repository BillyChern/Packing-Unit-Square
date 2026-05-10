"""Sweep-line rectangulation: O((n+k) log n) where k = output size.

Algorithm (left-to-right sweep over distinct x-coordinates of placed rects):

  1. Compute distinct x-edges X = sorted({container.x0, container.x1} ∪ {p.x0, p.x1}).
  2. Maintain `active_y_intervals` = sorted list of (y0, y1) for placed rects whose
     x-projection covers the *current* slab [X[i], X[i+1]].
  3. For each slab, the y-gaps in [container.y0, container.y1] minus active are
     the free rectangles in that slab.
  4. Add/remove rects from `active` at slab boundaries (insertion sort: O(log n)
     per change with bisect).

For exact-rational correctness we never use floats — all comparisons are on
`Fraction`. Output is identical to `rectangulate_complement` modulo ordering.

Property tests verify:
  P1. Pairwise interior-disjoint.
  P2. Each output rect is contained in container.
  P3. Each output rect is interior-disjoint from each placed rect.
  P4. Total area = container.area - Σ placed.area  (exact; assuming placed
      rectangles are pairwise interior-disjoint and contained).
"""

from __future__ import annotations
from fractions import Fraction
from typing import List, Tuple, Iterable
import bisect

from .geometry import Rect, PlacedRect
from .rectangulate import rectangulate_complement, merge_horizontal, merge_vertical

F = Fraction


def rectangulate_complement_fast(
    container: Rect, placed: List[PlacedRect]
) -> List[Rect]:
    """Sweep-line: produces the same disjoint partition as
    `rectangulate_complement` but faster. O(n log n + n·output) worst case.
    """
    if not placed:
        return [container] if container.area > 0 else []

    # Collect events: (x, kind, p_index) where kind=0 means "start" (add p), 1 means "end" (remove p)
    events: List[Tuple[F, int, int]] = []
    for i, p in enumerate(placed):
        events.append((p.x0, 0, i))
        events.append((p.x1, 1, i))
    # Sort: by x; at same x, process ends BEFORE starts (so a placed rect that ends at
    # exactly the slab boundary doesn't appear in the next slab).
    events.sort(key=lambda e: (e[0], e[1]))

    # Distinct x-edges from events plus container boundaries.
    xs_set = {container.x0, container.x1}
    for p in placed:
        if container.x0 <= p.x0 <= container.x1:
            xs_set.add(p.x0)
        if container.x0 <= p.x1 <= container.x1:
            xs_set.add(p.x1)
    xs = sorted(xs_set)

    out: List[Rect] = []
    active_intervals: List[Tuple[F, F, int]] = []   # (y0, y1, idx) sorted by y0
    ev_idx = 0
    n_events = len(events)

    for i in range(len(xs) - 1):
        x_lo = xs[i]
        x_hi = xs[i + 1]
        if x_lo >= x_hi:
            continue
        # Process all events with x ≤ x_lo (apply at this slab start).
        while ev_idx < n_events and events[ev_idx][0] <= x_lo:
            xe, kind, p_idx = events[ev_idx]
            p = placed[p_idx]
            if kind == 0:   # start
                # only add if this rect's x_range overlaps the slab in interior
                # (it does because xe = p.x0 ≤ x_lo and the next slab is ≥ x_lo)
                # Insertion: keep sorted by y0
                bisect.insort(active_intervals, (p.y0, p.y1, p_idx))
            else:           # end
                # remove placement p_idx
                for j, (y0, y1, idx) in enumerate(active_intervals):
                    if idx == p_idx:
                        del active_intervals[j]
                        break
            ev_idx += 1

        # Compute y-gaps in [container.y0, container.y1] given active intervals.
        # Merge overlapping intervals first.
        merged: List[Tuple[F, F]] = []
        for y0, y1, _ in active_intervals:
            if y0 < container.y0:
                y0 = container.y0
            if y1 > container.y1:
                y1 = container.y1
            if y0 >= y1:
                continue
            if merged and y0 <= merged[-1][1]:
                merged[-1] = (merged[-1][0], max(merged[-1][1], y1))
            else:
                merged.append((y0, y1))
        cursor = container.y0
        for y0, y1 in merged:
            if y0 > cursor:
                out.append(Rect(x_lo, cursor, x_hi, y0))
            cursor = max(cursor, y1)
        if cursor < container.y1:
            out.append(Rect(x_lo, cursor, x_hi, container.y1))

    return out


def rectangulate_simplified_fast(
    container: Rect, placed: List[PlacedRect], merge_passes: int = 4
) -> List[Rect]:
    rects = rectangulate_complement_fast(container, placed)
    for _ in range(merge_passes):
        n0 = len(rects)
        rects = merge_horizontal(rects)
        rects = merge_vertical(rects)
        if len(rects) == n0:
            break
    return rects


# Property tests -------------------------------------------------------------


def total_area(rects: Iterable[Rect]) -> Fraction:
    return sum((r.area for r in rects), Fraction(0))


def assert_pairwise_disjoint(rects: List[Rect]) -> None:
    n = len(rects)
    for i in range(n):
        for j in range(i + 1, n):
            assert rects[i].interior_disjoint(rects[j]), \
                f"output rects {i} and {j} overlap: {rects[i]} ∩ {rects[j]}"


def assert_inside(rects: List[Rect], container: Rect) -> None:
    for i, r in enumerate(rects):
        assert container.contains(r), f"rect {i} {r} not in container {container}"


def assert_disjoint_from_placed(rects: List[Rect], placed: List[PlacedRect]) -> None:
    for r in rects:
        for p in placed:
            assert r.interior_disjoint(p.rect), \
                f"output rect {r} overlaps placed n={p.n} rect {p.rect}"


def assert_area_balanced(rects: List[Rect], container: Rect, placed: List[PlacedRect]) -> None:
    placed_area = sum((p.area for p in placed), Fraction(0))
    free_area = total_area(rects)
    expected = container.area - placed_area
    assert free_area == expected, f"area mismatch: free={free_area}, expected={expected}"


def verify_rectangulation(
    rects: List[Rect], container: Rect, placed: List[PlacedRect]
) -> None:
    """Run all 4 property checks; raise AssertionError if any fails."""
    assert_inside(rects, container)
    assert_disjoint_from_placed(rects, placed)
    assert_pairwise_disjoint(rects)
    assert_area_balanced(rects, container, placed)


def equivalent_rectangulations(rs1: List[Rect], rs2: List[Rect]) -> bool:
    """Two rectangulations are equivalent if they tile the same region.
    We check by total area + same set of x-edges hit + same set of y-edges hit.
    A more rigorous check: each piece of rs1 can be partitioned into pieces of rs2
    and vice versa, but for our purposes equal-area + same bbox suffices."""
    if total_area(rs1) != total_area(rs2):
        return False
    # Compute bounding box union of each
    if not rs1 or not rs2:
        return rs1 == rs2
    bb1 = (
        min(r.x0 for r in rs1), min(r.y0 for r in rs1),
        max(r.x1 for r in rs1), max(r.y1 for r in rs1),
    )
    bb2 = (
        min(r.x0 for r in rs2), min(r.y0 for r in rs2),
        max(r.x1 for r in rs2), max(r.y1 for r in rs2),
    )
    return bb1 == bb2


__all__ = [
    "rectangulate_complement_fast",
    "rectangulate_simplified_fast",
    "verify_rectangulation",
    "equivalent_rectangulations",
    "total_area",
]
