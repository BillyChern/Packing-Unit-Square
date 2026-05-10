"""Cellification: split a long thin strip into fat absorber cells.

Given a strip of dimensions M × m with M ≥ m > 0, partition the long side
into N = ⌈M/m⌉ equal pieces. Each cell has dims m × M/N, with M/N ∈ (m/2, m].
Aspect ratio ≤ 2 and total semiperimeter ≤ 3M.

Reference: research-notes §10.2 / agent-execution-brief §6.7 / formalization-brief §8.
"""

from __future__ import annotations
from fractions import Fraction
from typing import List, Tuple

from .geometry import Rect

F = Fraction


def ceil_div(a: int, b: int) -> int:
    return -(-a // b)


def cells_count_along(M: F, m: F) -> int:
    """Smallest integer N with N*m ≥ M (i.e. ⌈M/m⌉ over rationals)."""
    if m <= 0:
        raise ValueError("m must be positive")
    if M <= 0:
        return 0
    # N = ⌈M/m⌉ = ⌈(M.numerator * m.denominator) / (M.denominator * m.numerator)⌉
    num = M.numerator * m.denominator
    den = M.denominator * m.numerator
    return ceil_div(num, den)


def cellify_strip(strip: Rect, max_cells: int = 64) -> List[Rect]:
    """Split `strip` (assumed M × m with M ≥ m, oriented arbitrarily) into N cells.

    Returns a list of disjoint sub-rectangles whose union equals `strip`,
    each with aspect ≤ 2, total semiperimeter ≤ 3M.

    If the natural cell count `⌈M/m⌉` exceeds `max_cells`, we return the strip
    *unsplit* — an ultra-thin strip is better treated as a single endpoint than
    fragmented into a huge number of cells.
    """
    if strip.w <= 0 or strip.h <= 0:
        return []
    horizontal = strip.w >= strip.h
    M = strip.w if horizontal else strip.h
    m = strip.h if horizontal else strip.w
    if M == m:
        # already a square; no further split
        return [strip]
    N = cells_count_along(M, m)
    if N <= 1:
        return [strip]
    if N > max_cells:
        # Ultra-thin strip — keep as single endpoint instead of fragmenting.
        return [strip]
    cell_long = F(M.numerator, M.denominator * N) if isinstance(M, Fraction) else M / N
    # Use exact rational division
    cell_long = Fraction(M) / N
    cells: List[Rect] = []
    for i in range(N):
        start = strip.x0 + i * cell_long if horizontal else strip.x0
        end = start + cell_long if horizontal else strip.x1
        if horizontal:
            cells.append(Rect(start, strip.y0, start + cell_long, strip.y1))
        else:
            ys = strip.y0 + i * cell_long
            cells.append(Rect(strip.x0, ys, strip.x1, ys + cell_long))
    # final cell may have fractional spillover; ensure last cell ends exactly at strip edge
    if cells:
        last = cells[-1]
        if horizontal and last.x1 != strip.x1:
            cells[-1] = Rect(last.x0, last.y0, strip.x1, last.y1)
        if (not horizontal) and last.y1 != strip.y1:
            cells[-1] = Rect(last.x0, last.y0, last.x1, strip.y1)
    return cells


def cell_bounds(M: F, m: F) -> Tuple[F, F, F]:
    """Return (cell_long, total_semiperim, max_aspect) for the cellification.

    cell_long: M / N where N = ⌈M/m⌉.
    total_semiperim: N * (m + M/N) = N*m + M.
    max_aspect: max(m, cell_long) / min(m, cell_long).
    """
    N = cells_count_along(M, m)
    if N == 0:
        return (F(0), F(0), F(1))
    cell_long = M / N
    semi = N * m + M
    if cell_long >= m:
        aspect = cell_long / m
    else:
        aspect = m / cell_long
    return (cell_long, semi, aspect)


__all__ = ["cellify_strip", "cells_count_along", "cell_bounds", "ceil_div"]
