"""Tests for mm_pack.two_backtrack."""
from fractions import Fraction as F

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.mm_pack.geometry import PlacedRect
from src.mm_pack.two_backtrack import two_backtrack


def test_no_change_when_residual_in_band():
    # row of total width 0.6, extent 1.0, residual 0.4. λ/t = 0.011 << 0.4
    plc = [PlacedRect(n=10, x0=F(0), y0=F(0), rotated=False)]   # width 1/10 = 0.1
    res = two_backtrack(plc, F(1), t=100)
    assert len(res.removed) == 0
    assert res.accepted


def test_undo_one_when_too_thin():
    # extent 1, three placements of width 1/2 + 1/3 + 1/15 = 0.9 (residual 0.1)
    # at t=10000, target_lo = 1.1/10000 = 1.1e-4. Residual 0.1 already > target_lo.
    # Force undersized residual: extent 1, used = 0.9999, residual 0.0001 < 1.1/100 = 0.011.
    plc = [
        PlacedRect(n=2, x0=F(0), y0=F(0), rotated=False),     # 1/2
        PlacedRect(n=2, x0=F(1, 2), y0=F(0), rotated=False),  # 1/2
    ]
    # extent 1, used 1, residual 0. Force undo.
    res = two_backtrack(plc, F(1), t=100)
    assert len(res.removed) >= 1   # at least one undone
    assert res.residual_width >= F(1, 2)  # huge residual after undo


def test_at_most_two_undo():
    plc = [PlacedRect(n=10+i, x0=F(0), y0=F(0), rotated=False) for i in range(5)]
    res = two_backtrack(plc, F(1, 1000), t=10**6)   # extent 1/1000, much less than placements
    assert len(res.removed) <= 2
