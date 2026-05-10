"""Packing algorithms for the Moser rectangle problem.

All algorithms operate in exact rational arithmetic (`fractions.Fraction`).

We provide:

* `shelf_pack`        — pure shelf packing with rotation.
* `meir_moser_strip`  — pack a list of (w, h) rectangles into a strip of
                         given width using the classical Meir–Moser shelf
                         decomposition; returns the resulting height.
* `MaxRectsPacker`    — Jylänki–Wäänänen "Maximal Rectangles" algorithm
                         adapted to exact arithmetic. The standard tool for
                         offline 2D rectangle packing.
* `pack_moser_prefix` — high-level driver that places R_1 at the bottom of
                         the unit square then runs MaxRects on the rest.
* `tail_strip_height` — Meir–Moser height bound for a tail R_{N+1}, R_{N+2}, …
                         packed into a strip of width W.
"""

from __future__ import annotations
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Iterable, List, Optional, Tuple

from .geometry import F, Placement, moser_dims

# ----------------------------------------------------------------------------
# Free-rectangle representation
# ----------------------------------------------------------------------------


@dataclass
class FreeRect:
    """An axis-aligned free rectangle [x, x+w] × [y, y+h]."""

    x: F
    y: F
    w: F
    h: F

    @property
    def x2(self) -> F:
        return self.x + self.w

    @property
    def y2(self) -> F:
        return self.y + self.h

    @property
    def area(self) -> F:
        return self.w * self.h

    def contains(self, other: "FreeRect") -> bool:
        return (
            self.x <= other.x
            and self.y <= other.y
            and self.x2 >= other.x2
            and self.y2 >= other.y2
        )


# ----------------------------------------------------------------------------
# Maximal Rectangles algorithm (Jylänki–Wäänänen)
# ----------------------------------------------------------------------------


class MaxRectsPacker:
    """Maximal-Rectangles 2D packer with rotation, exact arithmetic.

    Heuristics for placement:
        - 'BAF'  : Best Area Fit — minimize leftover area in the chosen rect.
        - 'BSSF' : Best Short Side Fit — minimize the shorter leftover edge.
        - 'BLSF' : Best Long Side Fit  — minimize the longer leftover edge.
        - 'BL'   : Bottom-Left — pick lowest y, then lowest x.
    """

    def __init__(self, W: F, H: F) -> None:
        self.W = W
        self.H = H
        self.free: List[FreeRect] = [FreeRect(F(0), F(0), W, H)]
        self.placed: List[Placement] = []

    # ------------------------------------------------------------
    # Placement scoring
    # ------------------------------------------------------------

    def _score(
        self, fr: FreeRect, w: F, h: F, heuristic: str
    ) -> Tuple[F, F]:
        """Return (primary, secondary) score; lower is better."""
        leftover_w = fr.w - w
        leftover_h = fr.h - h
        short = min(leftover_w, leftover_h)
        long_ = max(leftover_w, leftover_h)
        if heuristic == "BAF":
            return (fr.area - w * h, short)
        if heuristic == "BSSF":
            return (short, long_)
        if heuristic == "BLSF":
            return (long_, short)
        if heuristic == "BL":
            return (fr.y + h, fr.x)
        raise ValueError(f"unknown heuristic {heuristic}")

    def _find_position(
        self, w: F, h: F, allow_rotate: bool, heuristic: str
    ) -> Optional[Tuple[FreeRect, F, F, bool]]:
        """Best free rect & dimensions; None if no fit."""
        best = None
        best_score: Tuple[F, F] = (F(10**12), F(10**12))
        for fr in self.free:
            for ww, hh, rot in (
                (w, h, False),
                *(((h, w, True),) if allow_rotate and h != w else ()),
            ):
                if ww <= fr.w and hh <= fr.h:
                    s = self._score(fr, ww, hh, heuristic)
                    if s < best_score:
                        best_score = s
                        best = (fr, ww, hh, rot)
        return best

    # ------------------------------------------------------------
    # Splitting and pruning
    # ------------------------------------------------------------

    @staticmethod
    def _split(fr: FreeRect, used: FreeRect) -> List[FreeRect]:
        """Split fr by removing the used sub-rectangle.
        Returns up to four maximal pieces (some may be degenerate)."""
        out: List[FreeRect] = []
        # No overlap
        if (
            used.x >= fr.x2 or used.x2 <= fr.x
            or used.y >= fr.y2 or used.y2 <= fr.y
        ):
            return [fr]
        # Top
        if used.y2 < fr.y2:
            out.append(FreeRect(fr.x, used.y2, fr.w, fr.y2 - used.y2))
        # Bottom
        if used.y > fr.y:
            out.append(FreeRect(fr.x, fr.y, fr.w, used.y - fr.y))
        # Left
        if used.x > fr.x:
            out.append(FreeRect(fr.x, fr.y, used.x - fr.x, fr.h))
        # Right
        if used.x2 < fr.x2:
            out.append(FreeRect(used.x2, fr.y, fr.x2 - used.x2, fr.h))
        return [r for r in out if r.w > 0 and r.h > 0]

    def _prune(self) -> None:
        """Remove non-maximal free rectangles. O(n²)."""
        i = 0
        free = self.free
        while i < len(free):
            j = i + 1
            removed_i = False
            while j < len(free):
                if free[j].contains(free[i]):
                    free.pop(i)
                    removed_i = True
                    break
                if free[i].contains(free[j]):
                    free.pop(j)
                else:
                    j += 1
            if not removed_i:
                i += 1

    # ------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------

    def place(
        self,
        k: int,
        allow_rotate: bool = True,
        heuristic: str = "BSSF",
    ) -> Optional[Placement]:
        """Place rectangle R_k. Returns the placement, or None if no fit."""
        w, h = moser_dims(k)
        cand = self._find_position(w, h, allow_rotate, heuristic)
        if cand is None:
            return None
        fr, ww, hh, rotated = cand
        used = FreeRect(fr.x, fr.y, ww, hh)
        new_free: List[FreeRect] = []
        for f in self.free:
            new_free.extend(self._split(f, used))
        self.free = new_free
        self._prune()
        p = Placement(k=k, x=fr.x, y=fr.y, rotated=rotated)
        self.placed.append(p)
        return p

    def place_explicit(self, k: int, x: F, y: F, rotated: bool = False) -> Placement:
        """Force-place rectangle k; consume free space accordingly."""
        w, h = moser_dims(k)
        if rotated:
            w, h = h, w
        used = FreeRect(x, y, w, h)
        new_free: List[FreeRect] = []
        for f in self.free:
            new_free.extend(self._split(f, used))
        self.free = new_free
        self._prune()
        p = Placement(k=k, x=x, y=y, rotated=rotated)
        self.placed.append(p)
        return p

    def reserve(self, x: F, y: F, w: F, h: F) -> None:
        """Mark a region as occupied (e.g., a residual tail strip)."""
        used = FreeRect(x, y, w, h)
        new_free: List[FreeRect] = []
        for f in self.free:
            new_free.extend(self._split(f, used))
        self.free = new_free
        self._prune()


# ----------------------------------------------------------------------------
# Meir–Moser shelf packing
# ----------------------------------------------------------------------------


def meir_moser_strip(
    items: Iterable[Tuple[int, F, F]],
    W: F,
    allow_rotate: bool = True,
) -> Tuple[List[Placement], F]:
    """Pack `items=(k, w, h)` into strip of width W using shelves of height
    equal to the first item's height in each shelf. Returns placements and
    total height used. Items are processed in given order (caller sorts).
    """
    placed: List[Placement] = []
    cursor_y = F(0)
    cursor_x = F(0)
    shelf_h = F(0)
    for k, w, h in items:
        if allow_rotate and h > w:
            # We prefer the longer side horizontal for tighter shelves
            # but this is a *shelf* packer so we keep the input orientation.
            pass
        if cursor_x + w > W:
            cursor_y += shelf_h
            cursor_x = F(0)
            shelf_h = h
        if shelf_h == 0:
            shelf_h = h
        if w > W:
            raise ValueError(
                f"item k={k} width {w} exceeds strip width {W}"
            )
        rotated = False
        # Determine which orientation matches (k's native dims)
        nat_w, nat_h = moser_dims(k)
        if (w, h) == (nat_w, nat_h):
            rotated = False
        elif (w, h) == (nat_h, nat_w):
            rotated = True
        else:  # arbitrary item; treat as rotated relative to native
            rotated = (w == nat_h and h == nat_w)
        placed.append(Placement(k=k, x=cursor_x, y=cursor_y, rotated=rotated))
        cursor_x += w
        if h > shelf_h:
            shelf_h = h
    cursor_y += shelf_h
    return placed, cursor_y


def tail_strip_height(N: int, W: F) -> F:
    """Meir–Moser height bound for packing R_{N+1}, R_{N+2}, … into a strip
    of width W ≥ 1/(N+1).  Height ≥ 1/(N+2) + (1/(N+1)) / W.
    """
    if W < F(1, N + 1):
        raise ValueError(
            f"tail strip width {W} too small for R_{N+1} of width 1/{N+1}"
        )
    return F(1, N + 2) + F(1, N + 1) / W


# ----------------------------------------------------------------------------
# Algorithms tailored to the Moser sequence
# ----------------------------------------------------------------------------


def shelf_pack(
    N: int,
    X: F = F(1),
    rotate: bool = True,
) -> Tuple[List[Placement], F]:
    """Pack R_1..R_N into a strip of width X, returning final height."""
    items: List[Tuple[int, F, F]] = []
    for k in range(1, N + 1):
        w, h = moser_dims(k)
        # Place with longer side horizontal (since X is large)
        if rotate and h > w:
            w, h = h, w
        items.append((k, w, h))
    return meir_moser_strip(items, X, allow_rotate=False)


def pack_moser_prefix_maxrects(
    N: int,
    side: F = F(1),
    heuristic: str = "BSSF",
    place_R1_first: bool = True,
) -> Tuple[List[Placement], MaxRectsPacker, List[int]]:
    """Pack R_1..R_N into [0, side]² via MaxRects (with rotation).

    R_1 always has width 1; we place it explicitly at the bottom-left.
    Returns (placements, packer state, list of unplaced k's).
    """
    p = MaxRectsPacker(W=side, H=side)
    failed: List[int] = []
    if place_R1_first:
        p.place_explicit(1, F(0), F(0), rotated=False)
        start = 2
    else:
        start = 1
    for k in range(start, N + 1):
        if p.place(k, allow_rotate=True, heuristic=heuristic) is None:
            failed.append(k)
    return p.placed, p, failed


def pack_with_tail_reservation(
    N: int,
    side: F,
    tail_strip_W: F,
    place_at: str = "top",
    heuristic: str = "BSSF",
) -> Tuple[List[Placement], MaxRectsPacker, List[int], FreeRect]:
    """Reserve a strip for the tail R_{N+1}, … and pack the prefix R_1..R_N.

    `place_at` is one of 'top' (full-width strip at top) or
    'right' (full-height strip on the right).

    Returns placements, packer, unplaced prefix indices, and the reserved
    tail-strip FreeRect (for downstream packing of the tail).
    """
    p = MaxRectsPacker(W=side, H=side)
    # Reserve the tail region
    if place_at == "top":
        h_tail = tail_strip_height(N, tail_strip_W)
        # tail strip is [side - tail_strip_W ... side] × [side - h_tail ... side]?
        # Use full width: pick W = side, but caller may pass smaller tail_strip_W.
        tail = FreeRect(F(0), side - h_tail, tail_strip_W, h_tail)
        p.reserve(tail.x, tail.y, tail.w, tail.h)
    elif place_at == "right":
        h_strip = side  # full height
        tail = FreeRect(side - tail_strip_W, F(0), tail_strip_W, h_strip)
        p.reserve(tail.x, tail.y, tail.w, tail.h)
    else:
        raise ValueError(f"unknown place_at={place_at}")
    # Place R_1 explicitly at bottom (so it doesn't conflict with the tail).
    if place_at == "right":
        # R_1 is 1×1/2, but available width is side - tail_strip_W ≤ 1.
        # Try rotated: 1/2×1, fits if side ≥ 1.
        if side - tail_strip_W >= F(1):
            p.place_explicit(1, F(0), F(0), rotated=False)
        else:
            p.place_explicit(1, F(0), F(0), rotated=True)
    else:
        p.place_explicit(1, F(0), F(0), rotated=False)
    failed: List[int] = []
    for k in range(2, N + 1):
        if p.place(k, allow_rotate=True, heuristic=heuristic) is None:
            failed.append(k)
    return p.placed, p, failed, tail
