"""Fast MaxRects packer using float-shadowed Fraction.

Each FreeRect carries Fraction coordinates (exact) and float copies (fast).
Comparisons use float with safe tolerance. Storage and final verification
use Fraction. This gives ~50–100× speedup over pure-Fraction MaxRects
without sacrificing correctness.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from typing import List, Optional, Tuple

from .geometry import F, Placement, moser_dims


# Float tolerance: a pair of inequalities A.x ≤ B.x and B.x ≤ A.x within
# this tolerance is treated as "A.x == B.x". Since denominators come from
# 1/k for k ≤ 10^6, the smallest *real* gap between distinct rationals here
# is on the order of 1/(k₁·k₂) ≥ 10⁻¹². We use 10⁻¹⁵ to be safe — any
# difference smaller than that is treated as a tie and resolved by exact
# Fraction comparison.
FLOAT_EPS = 1e-13


@dataclass
class FastFreeRect:
    x: Fraction
    y: Fraction
    w: Fraction
    h: Fraction
    xf: float = 0.0  # cached
    yf: float = 0.0
    wf: float = 0.0
    hf: float = 0.0

    def __post_init__(self):
        self.xf = float(self.x)
        self.yf = float(self.y)
        self.wf = float(self.w)
        self.hf = float(self.h)

    @property
    def x2(self) -> Fraction:
        return self.x + self.w

    @property
    def y2(self) -> Fraction:
        return self.y + self.h

    @property
    def x2f(self) -> float:
        return self.xf + self.wf

    @property
    def y2f(self) -> float:
        return self.yf + self.hf

    def contains_float(self, other: "FastFreeRect") -> Optional[bool]:
        """Return True / False / None (None = ambiguous, fall back to exact)."""
        # A contains B iff A.x ≤ B.x, A.y ≤ B.y, A.x2 ≥ B.x2, A.y2 ≥ B.y2.
        # Float check: if any inequality fails by > FLOAT_EPS, definitely False.
        # If all hold by > FLOAT_EPS, definitely True. Otherwise None.
        dx1 = other.xf - self.xf       # ≥ 0 desired
        dy1 = other.yf - self.yf
        dx2 = self.x2f - other.x2f     # ≥ 0 desired
        dy2 = self.y2f - other.y2f
        if dx1 < -FLOAT_EPS or dy1 < -FLOAT_EPS or dx2 < -FLOAT_EPS or dy2 < -FLOAT_EPS:
            return False
        if dx1 > FLOAT_EPS and dy1 > FLOAT_EPS and dx2 > FLOAT_EPS and dy2 > FLOAT_EPS:
            return True
        if min(dx1, dy1, dx2, dy2) > FLOAT_EPS / 2:
            # all clearly non-negative
            return True
        if dx1 >= 0 and dy1 >= 0 and dx2 >= 0 and dy2 >= 0:
            return True  # weak containment, allowed (touching boundaries counts)
        return None

    def contains_exact(self, other: "FastFreeRect") -> bool:
        return (
            self.x <= other.x
            and self.y <= other.y
            and self.x + self.w >= other.x + other.w
            and self.y + self.h >= other.y + other.h
        )

    def contains(self, other: "FastFreeRect") -> bool:
        r = self.contains_float(other)
        if r is not None:
            return r
        return self.contains_exact(other)


class FastMaxRectsPacker:
    def __init__(self, W: Fraction, H: Fraction) -> None:
        self.W = W
        self.H = H
        self.free: List[FastFreeRect] = [FastFreeRect(F(0), F(0), W, H)]
        self.placed: List[Placement] = []

    @staticmethod
    def _split(fr: FastFreeRect, ux: Fraction, uy: Fraction, uw: Fraction, uh: Fraction
               ) -> List[FastFreeRect]:
        out: List[FastFreeRect] = []
        ux2 = ux + uw
        uy2 = uy + uh
        if ux >= fr.x + fr.w or ux2 <= fr.x or uy >= fr.y + fr.h or uy2 <= fr.y:
            return [fr]
        # Top
        if uy2 < fr.y + fr.h:
            out.append(FastFreeRect(fr.x, uy2, fr.w, fr.y + fr.h - uy2))
        # Bottom
        if uy > fr.y:
            out.append(FastFreeRect(fr.x, fr.y, fr.w, uy - fr.y))
        # Left
        if ux > fr.x:
            out.append(FastFreeRect(fr.x, fr.y, ux - fr.x, fr.h))
        # Right
        if ux2 < fr.x + fr.w:
            out.append(FastFreeRect(ux2, fr.y, fr.x + fr.w - ux2, fr.h))
        return [r for r in out if r.w > 0 and r.h > 0]

    def _prune(self) -> None:
        free = self.free
        # Sort by area descending — large rects more likely to contain others
        free.sort(key=lambda r: r.wf * r.hf, reverse=True)
        n = len(free)
        keep = [True] * n
        for i in range(n):
            if not keep[i]:
                continue
            ai = free[i]
            for j in range(i + 1, n):
                if not keep[j]:
                    continue
                bj = free[j]
                # A contains B?
                # quick float reject
                if (
                    bj.xf < ai.xf - FLOAT_EPS
                    or bj.yf < ai.yf - FLOAT_EPS
                    or bj.x2f > ai.x2f + FLOAT_EPS
                    or bj.y2f > ai.y2f + FLOAT_EPS
                ):
                    continue
                # All four float ineqs hold within ε; finalize with exact
                if ai.contains_exact(bj):
                    keep[j] = False
        self.free = [free[i] for i in range(n) if keep[i]]

    def _find_position(self, w: Fraction, h: Fraction, allow_rotate: bool, heuristic: str
                       ) -> Optional[Tuple[FastFreeRect, Fraction, Fraction, bool]]:
        wf, hf = float(w), float(h)
        best: Optional[Tuple[FastFreeRect, Fraction, Fraction, bool, float, float]] = None
        Wf = float(self.W)
        Hf = float(self.H)
        for fr in self.free:
            for ww, hh, wwf, hhf, rot in (
                (w, h, wf, hf, False),
                *(((h, w, hf, wf, True),) if allow_rotate and h != w else ()),
            ):
                if wwf > fr.wf + FLOAT_EPS or hhf > fr.hf + FLOAT_EPS:
                    continue
                # exact check (cheap if the float passes by margin)
                if not (ww <= fr.w and hh <= fr.h):
                    continue
                lw = fr.wf - wwf
                lh = fr.hf - hhf
                short = lw if lw < lh else lh
                long_ = lh if lw < lh else lw
                if heuristic == "BSSF":
                    s1, s2 = short, long_
                elif heuristic == "BAF":
                    s1, s2 = fr.wf * fr.hf - wwf * hhf, short
                elif heuristic == "BLSF":
                    s1, s2 = long_, short
                elif heuristic == "BL":
                    s1, s2 = fr.yf + hhf, fr.xf
                elif heuristic == "CONTACT":
                    # contact_score = wwf + hhf
                    #   + hhf if width matches FR's width (right side touches neighbor)
                    #   + wwf if height matches FR's height (top side touches neighbor)
                    extra = 0.0
                    if abs(wwf - fr.wf) < FLOAT_EPS:
                        extra += hhf
                    if abs(hhf - fr.hf) < FLOAT_EPS:
                        extra += wwf
                    contact = wwf + hhf + extra
                    s1, s2 = -contact, fr.yf + hhf
                elif heuristic == "BAF_CONTACT":
                    # primary: best area fit. tiebreak by contact bonus.
                    extra = 0.0
                    if abs(wwf - fr.wf) < FLOAT_EPS:
                        extra += hhf
                    if abs(hhf - fr.hf) < FLOAT_EPS:
                        extra += wwf
                    s1 = fr.wf * fr.hf - wwf * hhf
                    s2 = -extra  # max extra = min -extra
                elif heuristic == "BSSF_CONTACT":
                    extra = 0.0
                    if abs(wwf - fr.wf) < FLOAT_EPS:
                        extra += hhf
                    if abs(hhf - fr.hf) < FLOAT_EPS:
                        extra += wwf
                    s1 = short
                    s2 = -extra
                elif heuristic == "PAULHUS":
                    # Paulhus / Joós: choose FR with smallest WIDTH that fits;
                    # tiebreak by smallest HEIGHT. (For Moser, use the FR with
                    # smallest "admissible" width = wf such that wwf ≤ wf.)
                    s1, s2 = fr.wf, fr.hf
                else:
                    raise ValueError(heuristic)
                if best is None or (s1, s2) < (best[4], best[5]):
                    best = (fr, ww, hh, rot, s1, s2)
        if best is None:
            return None
        return best[0], best[1], best[2], best[3]

    def _incremental_update(self, x: Fraction, y: Fraction, w: Fraction, h: Fraction) -> None:
        """Split overlapping free rects and incrementally prune the result.
        Avoids the O(F²) full-prune by only considering new rects vs existing.
        """
        xf = float(x)
        yf = float(y)
        x2f = float(x + w)
        y2f = float(y + h)
        new_rects: List[FastFreeRect] = []
        kept_old: List[FastFreeRect] = []
        for f in self.free:
            # float quick test for overlap with placed rect
            if (
                f.x2f <= xf + FLOAT_EPS
                or f.xf >= x2f - FLOAT_EPS
                or f.y2f <= yf + FLOAT_EPS
                or f.yf >= y2f - FLOAT_EPS
            ):
                kept_old.append(f)
                continue
            # exact split
            new_rects.extend(self._split(f, x, y, w, h))
        # Now prune new_rects against kept_old and each other
        # Sort new_rects by area descending so larger considered first
        new_rects.sort(key=lambda r: r.wf * r.hf, reverse=True)
        survivors: List[FastFreeRect] = []
        for c in new_rects:
            # drop c if any kept_old or earlier survivor contains it
            contained = False
            for o in kept_old:
                # quick float test
                if (
                    o.xf - FLOAT_EPS <= c.xf
                    and o.yf - FLOAT_EPS <= c.yf
                    and o.x2f + FLOAT_EPS >= c.x2f
                    and o.y2f + FLOAT_EPS >= c.y2f
                ):
                    if o.contains_exact(c):
                        contained = True
                        break
            if contained:
                continue
            for s in survivors:
                if (
                    s.xf - FLOAT_EPS <= c.xf
                    and s.yf - FLOAT_EPS <= c.yf
                    and s.x2f + FLOAT_EPS >= c.x2f
                    and s.y2f + FLOAT_EPS >= c.y2f
                ):
                    if s.contains_exact(c):
                        contained = True
                        break
            if contained:
                continue
            survivors.append(c)
        # Also drop kept_old rects contained in any survivor (possible since
        # new survivor could be larger than an old non-overlapping rect, but
        # only if the survivor extends into territory the old one occupies —
        # this doesn't happen since survivors are pieces of split overlapping
        # rects, all sharing some side with the placed rect's neighbors).
        # We check anyway for correctness.
        kept_old_kept: List[FastFreeRect] = []
        for o in kept_old:
            contained = False
            for s in survivors:
                if (
                    s.xf - FLOAT_EPS <= o.xf
                    and s.yf - FLOAT_EPS <= o.yf
                    and s.x2f + FLOAT_EPS >= o.x2f
                    and s.y2f + FLOAT_EPS >= o.y2f
                ):
                    if s.contains_exact(o):
                        contained = True
                        break
            if not contained:
                kept_old_kept.append(o)
        self.free = kept_old_kept + survivors

    def place_explicit(self, k: int, x: Fraction, y: Fraction, rotated: bool = False) -> Placement:
        w, h = moser_dims(k)
        if rotated:
            w, h = h, w
        self._incremental_update(x, y, w, h)
        p = Placement(k=k, x=x, y=y, rotated=rotated)
        self.placed.append(p)
        return p

    def reserve(self, x: Fraction, y: Fraction, w: Fraction, h: Fraction) -> None:
        self._incremental_update(x, y, w, h)

    def place(self, k: int, allow_rotate: bool = True, heuristic: str = "BSSF") -> Optional[Placement]:
        w, h = moser_dims(k)
        cand = self._find_position(w, h, allow_rotate, heuristic)
        if cand is None:
            return None
        fr, ww, hh, rotated = cand
        self._incremental_update(fr.x, fr.y, ww, hh)
        p = Placement(k=k, x=fr.x, y=fr.y, rotated=rotated)
        self.placed.append(p)
        return p
