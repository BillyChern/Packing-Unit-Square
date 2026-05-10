"""Exact-arithmetic geometry for rectangle packings.

All coordinates use `fractions.Fraction` to avoid floating-point error.
A `Placement` is an axis-aligned rectangle with a label `k` (which Moser
rectangle 1/k × 1/(k+1) it represents) and a rotation flag.
"""

from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable, List, Tuple

F = Fraction


def moser_dims(k: int) -> Tuple[F, F]:
    """Native (width, height) of the k-th Moser rectangle: 1/k × 1/(k+1)."""
    return F(1, k), F(1, k + 1)


@dataclass(frozen=True)
class Placement:
    """Axis-aligned placement of Moser rectangle k.

    The rectangle occupies [x, x+w] × [y, y+h] in the ambient square.
    `rotated=True` means the rectangle is placed with its short side horizontal,
    i.e. (w, h) = (1/(k+1), 1/k).
    """

    k: int
    x: F
    y: F
    rotated: bool = False

    @property
    def w(self) -> F:
        a, b = moser_dims(self.k)
        return b if self.rotated else a

    @property
    def h(self) -> F:
        a, b = moser_dims(self.k)
        return a if self.rotated else b

    @property
    def x2(self) -> F:
        return self.x + self.w

    @property
    def y2(self) -> F:
        return self.y + self.h

    @property
    def area(self) -> F:
        return F(1, self.k * (self.k + 1))

    def overlaps(self, other: "Placement") -> bool:
        """Strict positive-area overlap (touching boundaries is OK)."""
        if self.x2 <= other.x or other.x2 <= self.x:
            return False
        if self.y2 <= other.y or other.y2 <= self.y:
            return False
        return True

    def inside(self, X: F, Y: F) -> bool:
        """Whether placement lies within [0, X] × [0, Y]."""
        return self.x >= 0 and self.y >= 0 and self.x2 <= X and self.y2 <= Y


def verify_packing(
    placements: Iterable[Placement], X: F = F(1), Y: F = F(1)
) -> Tuple[bool, List[str]]:
    """Verify a list of Placements: containment, non-overlap, distinct labels.

    Returns (ok, errors). Uses exact arithmetic for the final check, with a
    fast float pre-pass to skip clearly-non-overlapping pairs.
    """
    EPS = 1e-13
    errors: List[str] = []
    plist: List[Placement] = list(placements)

    Xf = float(X)
    Yf = float(Y)

    seen: set[int] = set()
    bounds_ok = True
    for p in plist:
        if p.k in seen:
            errors.append(f"duplicate rectangle k={p.k}")
        seen.add(p.k)
        # Fast float bound check first
        xf, yf = float(p.x), float(p.y)
        wf, hf = float(p.w), float(p.h)
        if (xf < -EPS or yf < -EPS or xf + wf > Xf + EPS or yf + hf > Yf + EPS):
            # confirm with exact
            if not p.inside(X, Y):
                errors.append(
                    f"k={p.k} out of bounds: "
                    f"[{p.x},{p.x2}]×[{p.y},{p.y2}] vs box {X}×{Y}"
                )
                bounds_ok = False

    # Sweep-line non-overlap check: sort by x, scan, prune by x_right < x_left
    n = len(plist)
    # Precompute floats for fast pre-test
    fx = [(float(p.x), float(p.x + p.w), float(p.y), float(p.y + p.h), p) for p in plist]
    fx.sort(key=lambda t: t[0])
    for i in range(n):
        ai_x, ai_x2, ai_y, ai_y2, ap = fx[i]
        for j in range(i + 1, n):
            bj_x, bj_x2, bj_y, bj_y2, bp = fx[j]
            if bj_x >= ai_x2 - EPS:
                break
            # quick float reject
            if bj_x2 <= ai_x + EPS or ai_x2 <= bj_x + EPS:
                continue
            if bj_y2 <= ai_y + EPS or ai_y2 <= bj_y + EPS:
                continue
            # overlap likely; verify exact
            if ap.overlaps(bp):
                errors.append(
                    f"overlap k={ap.k} and k={bp.k}: "
                    f"[{ap.x},{ap.x2}]×[{ap.y},{ap.y2}] vs "
                    f"[{bp.x},{bp.x2}]×[{bp.y},{bp.y2}]"
                )
    return (len(errors) == 0, errors)


def total_area(placements: Iterable[Placement]) -> F:
    return sum((p.area for p in placements), F(0))


def bounding_extent(placements: Iterable[Placement]) -> Tuple[F, F]:
    """Smallest axis-aligned bounding box [0, X] × [0, Y] containing all placements."""
    X = F(0)
    Y = F(0)
    for p in placements:
        if p.x2 > X:
            X = p.x2
        if p.y2 > Y:
            Y = p.y2
    return X, Y


def moser_tail_area(N: int) -> F:
    """Area of R_{N+1} ∪ R_{N+2} ∪ … = 1/(N+1)."""
    return F(1, N + 1)


def moser_prefix_area(N: int) -> F:
    """Area of R_1 ∪ … ∪ R_N = N/(N+1)."""
    return F(N, N + 1)
