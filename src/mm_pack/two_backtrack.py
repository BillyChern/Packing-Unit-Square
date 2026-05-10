"""Two-backtrack anti-sliver rule.

When a row of placements ends with a too-thin endpoint (residual width < λ/t),
undo at most 2 of the trailing placements until the residual thickness lies in
[λ/t, (λ+C)/t]. This guarantees endpoint *fatness* at scale 1/t.

Reference: research-notes §9.2 / agent-execution-brief §6.1.
"""

from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from typing import List, Tuple

from .geometry import PlacedRect

F = Fraction


@dataclass(frozen=True)
class BacktrackResult:
    placements: Tuple[PlacedRect, ...]   # surviving placements in the row
    removed: Tuple[PlacedRect, ...]      # placements undone
    residual_width: F                    # endpoint thickness after backtrack
    accepted: bool                       # residual now ≥ λ/t (i.e., not a sliver)


def two_backtrack(
    row: List[PlacedRect],
    row_extent: F,
    t: int,
    lam: F = F(11, 10),
    C: F = F(3),
) -> BacktrackResult:
    """Apply two-backtrack to `row`: undo up to 2 trailing placements until
    the residual width (= row_extent − Σ widths) is at least λ/t. If a row
    was filled greedily, this also gives an upper bound (λ+C)/t.

    `row_extent` is the available width; `t` is the current scheduling time.
    `accepted` means the residual passes the *lower* bound (no longer a sliver).
    """
    target_lo = F(lam.numerator, lam.denominator * t)
    used = sum((p.w for p in row), F(0))
    residual = row_extent - used

    # If residual already at-or-above target_lo, accept without removing.
    if residual >= target_lo:
        return BacktrackResult(
            tuple(row), tuple(), residual, True
        )

    removed: List[PlacedRect] = []
    survivors = list(row)
    for _ in range(2):
        if not survivors:
            break
        last = survivors.pop()
        removed.append(last)
        residual = residual + last.w
        if residual >= target_lo:
            break

    accepted = residual >= target_lo
    return BacktrackResult(
        tuple(survivors), tuple(removed), residual, accepted
    )


__all__ = ["BacktrackResult", "two_backtrack"]
