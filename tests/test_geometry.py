"""Tests for mm_pack.geometry."""
from fractions import Fraction as F

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.mm_pack.geometry import (
    Rect, FreeBox, FreeBoxKind, PlacedRect,
    split_free_after_place, maxrects_split,
    verify_no_overlap, verify_containment,
)


def test_rect_basic():
    r = Rect(F(0), F(0), F(1), F(2))
    assert r.w == 1
    assert r.h == 2
    assert r.area == 2
    assert r.semiperim == 3
    assert r.min_side == 1
    assert r.max_side == 2
    assert r.aspect == 2


def test_rect_contains():
    big = Rect(F(0), F(0), F(1), F(1))
    small = Rect(F(0, 1), F(0, 1), F(1, 2), F(1, 2))
    assert big.contains(small)
    assert not small.contains(big)


def test_rect_interior_disjoint():
    a = Rect(F(0), F(0), F(1, 2), F(1, 2))
    b = Rect(F(1, 2), F(0), F(1), F(1, 2))         # touches edge
    c = Rect(F(1, 4), F(0), F(3, 4), F(1, 2))      # overlaps
    assert a.interior_disjoint(b)
    assert b.interior_disjoint(a)
    assert not a.interior_disjoint(c)


def test_rect_fits():
    box = Rect(F(0), F(0), F(1, 2), F(1, 3))
    assert box.fits(F(1, 4), F(1, 4))                  # both fit
    assert box.fits(F(1, 3), F(1, 2))                  # rotated fits
    assert not box.fits(F(1), F(1, 100))               # too wide


def test_split_free_after_place():
    free = Rect(F(0), F(0), F(1), F(1))
    placed = Rect(F(0), F(0), F(1, 2), F(1, 3))
    out = split_free_after_place(free, placed)
    assert len(out) == 2
    # Right strip
    right = next(r for r in out if r.x0 == F(1, 2))
    assert right == Rect(F(1, 2), F(0), F(1), F(1))
    # Top strip (only over placed.x range)
    top = next(r for r in out if r.y0 == F(1, 3))
    assert top == Rect(F(0), F(1, 3), F(1, 2), F(1))
    # Total area = free.area - placed.area
    total = sum((r.area for r in out), F(0))
    assert total == free.area - placed.area


def test_maxrects_split():
    free = Rect(F(0), F(0), F(1), F(1))
    placed = Rect(F(1, 4), F(1, 4), F(3, 4), F(3, 4))
    out = maxrects_split(free, placed)
    assert len(out) == 4   # L, R, B, T


def test_placed_rect_dims():
    p = PlacedRect(n=5, x0=F(0), y0=F(0), rotated=False)
    assert p.w == F(1, 5) and p.h == F(1, 6)
    pr = PlacedRect(n=5, x0=F(0), y0=F(0), rotated=True)
    assert pr.w == F(1, 6) and pr.h == F(1, 5)


def test_freebox_kind_enum():
    assert FreeBoxKind.LRP.value == "LRP"
    fb = FreeBox(rect=Rect(F(0), F(0), F(1), F(1)), kind=FreeBoxKind.LRP)
    assert fb.area == 1


def test_verify_no_overlap_pos():
    p1 = PlacedRect(n=2, x0=F(0), y0=F(0), rotated=False)   # 1/2 × 1/3
    p2 = PlacedRect(n=2, x0=F(1, 2), y0=F(0), rotated=False)
    p2 = PlacedRect(n=3, x0=F(1, 2), y0=F(0), rotated=False)  # 1/3 × 1/4
    ok, errs = verify_no_overlap([p1, p2])
    assert ok and len(errs) == 0


def test_verify_no_overlap_neg():
    p1 = PlacedRect(n=2, x0=F(0), y0=F(0), rotated=False)
    p2 = PlacedRect(n=3, x0=F(1, 4), y0=F(0), rotated=False)   # overlap with p1
    ok, errs = verify_no_overlap([p1, p2])
    assert not ok
