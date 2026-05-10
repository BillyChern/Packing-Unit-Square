"""Exact-rational geometry primitives for Calibrated Slack-Pack.

Builds on `src.geometry.Placement` with a typed `FreeBox` decomposition:
each free rectangle carries its `kind` (LRP / normal / endpoint / absorber /
generic) and optional birth index for the calibrated normal-width law.
"""

from __future__ import annotations
from dataclasses import dataclass, field, replace
from enum import Enum
from fractions import Fraction
from typing import Iterable, List, Optional, Tuple

F = Fraction


@dataclass(frozen=True)
class Rect:
    """Closed axis-aligned rectangle [x0, x1] × [y0, y1] over Fractions."""

    x0: F
    y0: F
    x1: F
    y1: F

    def __post_init__(self) -> None:
        if self.x0 > self.x1 or self.y0 > self.y1:
            raise ValueError(f"degenerate Rect: {self}")

    @property
    def w(self) -> F:
        return self.x1 - self.x0

    @property
    def h(self) -> F:
        return self.y1 - self.y0

    @property
    def area(self) -> F:
        return self.w * self.h

    @property
    def semiperim(self) -> F:
        return self.w + self.h

    @property
    def min_side(self) -> F:
        return min(self.w, self.h)

    @property
    def max_side(self) -> F:
        return max(self.w, self.h)

    @property
    def aspect(self) -> F:
        m = self.min_side
        if m == 0:
            return F(0)
        return self.max_side / m

    def contains(self, other: "Rect") -> bool:
        return (
            self.x0 <= other.x0
            and other.x1 <= self.x1
            and self.y0 <= other.y0
            and other.y1 <= self.y1
        )

    def interior_disjoint(self, other: "Rect") -> bool:
        return (
            self.x1 <= other.x0
            or other.x1 <= self.x0
            or self.y1 <= other.y0
            or other.y1 <= self.y0
        )

    def fits(self, w: F, h: F) -> bool:
        """Whether a w×h or h×w rectangle fits in self."""
        return (w <= self.w and h <= self.h) or (h <= self.w and w <= self.h)


class FreeBoxKind(str, Enum):
    LRP = "LRP"
    NORMAL = "normal"
    ENDPOINT = "endpoint"
    ABSORBER = "absorber"
    GENERIC = "generic"


@dataclass(frozen=True)
class FreeBox:
    """A free rectangle with type tag + optional birth index for normal-box width law."""

    rect: Rect
    kind: FreeBoxKind = FreeBoxKind.GENERIC
    birth_index: Optional[int] = None

    @property
    def w(self) -> F:
        return self.rect.w

    @property
    def h(self) -> F:
        return self.rect.h

    @property
    def area(self) -> F:
        return self.rect.area

    @property
    def semiperim(self) -> F:
        return self.rect.semiperim

    @property
    def aspect(self) -> F:
        return self.rect.aspect

    @property
    def min_side(self) -> F:
        return self.rect.min_side

    @property
    def max_side(self) -> F:
        return self.rect.max_side


@dataclass(frozen=True)
class PlacedRect:
    """A Moser rectangle placed at a position."""

    n: int
    x0: F
    y0: F
    rotated: bool

    @property
    def w(self) -> F:
        if self.rotated:
            return F(1, self.n + 1)
        return F(1, self.n)

    @property
    def h(self) -> F:
        if self.rotated:
            return F(1, self.n)
        return F(1, self.n + 1)

    @property
    def x1(self) -> F:
        return self.x0 + self.w

    @property
    def y1(self) -> F:
        return self.y0 + self.h

    @property
    def rect(self) -> Rect:
        return Rect(self.x0, self.y0, self.x1, self.y1)

    @property
    def area(self) -> F:
        return F(1, self.n * (self.n + 1))


def split_free_after_place(free: Rect, placed: Rect) -> List[Rect]:
    """MaxRects-style guillotine split: given a placed rect inside free,
    return the list of new (non-overlapping) free sub-rectangles.

    Standard MaxRects produces 4 candidate maximal rects (left, right, bottom,
    top of placed). Here we produce a 2-cut guillotine split instead — fewer
    boxes, simpler accounting for the calibrated framework.
    """
    if not free.contains(placed):
        raise ValueError("placed rectangle not contained in free rectangle")
    out: List[Rect] = []
    # Right strip: [placed.x1, free.x1] × [free.y0, free.y1]
    if placed.x1 < free.x1:
        out.append(Rect(placed.x1, free.y0, free.x1, free.y1))
    # Top strip above placed within [free.x0, placed.x1] × [placed.y1, free.y1]
    if placed.y1 < free.y1:
        out.append(Rect(free.x0, placed.y1, placed.x1, free.y1))
    return out


def maxrects_split(free: Rect, placed: Rect) -> List[Rect]:
    """4-piece MaxRects split: returns L/R/B/T strips of `free` minus `placed`."""
    if not free.contains(placed):
        return [free]
    out: List[Rect] = []
    if placed.x0 > free.x0:
        out.append(Rect(free.x0, free.y0, placed.x0, free.y1))
    if placed.x1 < free.x1:
        out.append(Rect(placed.x1, free.y0, free.x1, free.y1))
    if placed.y0 > free.y0:
        out.append(Rect(free.x0, free.y0, free.x1, placed.y0))
    if placed.y1 < free.y1:
        out.append(Rect(free.x0, placed.y1, free.x1, free.y1))
    return out


def is_contained_in_any(rect: Rect, others: Iterable[Rect]) -> bool:
    for o in others:
        if o is rect:
            continue
        if o.contains(rect) and (o.w > rect.w or o.h > rect.h or o is not rect):
            if o.w * o.h > rect.w * rect.h:
                return True
            if o.w * o.h == rect.w * rect.h and o is not rect:
                return True
    return False


def prune_contained(rects: List[Rect]) -> List[Rect]:
    """Remove rects strictly contained in another rect of the list."""
    n = len(rects)
    keep = [True] * n
    for i in range(n):
        if not keep[i]:
            continue
        for j in range(n):
            if i == j or not keep[j]:
                continue
            if rects[j].contains(rects[i]) and (
                rects[j].w > rects[i].w or rects[j].h > rects[i].h
            ):
                keep[i] = False
                break
    return [r for r, k in zip(rects, keep) if k]


def verify_no_overlap(placed: List[PlacedRect]) -> Tuple[bool, List[str]]:
    """Sweep-line + exact check that no two placed rectangles have positive-area overlap."""
    errors: List[str] = []
    items = sorted(placed, key=lambda p: p.x0)
    n = len(items)
    for i in range(n):
        a = items[i]
        for j in range(i + 1, n):
            b = items[j]
            if b.x0 >= a.x1:
                break
            ar = a.rect
            br = b.rect
            if not ar.interior_disjoint(br):
                errors.append(f"overlap n={a.n} and n={b.n}")
    return (len(errors) == 0, errors)


def verify_containment(placed: List[PlacedRect], container: Rect) -> Tuple[bool, List[str]]:
    errors: List[str] = []
    for p in placed:
        if not container.contains(p.rect):
            errors.append(f"n={p.n} not in container: {p.rect} vs {container}")
    return (len(errors) == 0, errors)


__all__ = [
    "Rect",
    "FreeBox",
    "FreeBoxKind",
    "PlacedRect",
    "split_free_after_place",
    "maxrects_split",
    "prune_contained",
    "verify_no_overlap",
    "verify_containment",
]
