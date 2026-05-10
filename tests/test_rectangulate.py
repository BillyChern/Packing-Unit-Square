"""Tests for mm_pack.rectangulate and rectangulate_fast: equivalence + correctness."""
from fractions import Fraction as F

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.mm_pack.geometry import Rect, PlacedRect
from src.mm_pack.rectangulate import rectangulate_complement
from src.mm_pack.rectangulate_fast import (
    rectangulate_complement_fast, verify_rectangulation, total_area
)
from src.algorithms import MaxRectsPacker


def make_packing(N: int) -> tuple[Rect, list[PlacedRect]]:
    container = Rect(F(0), F(0), F(1), F(1))
    packer = MaxRectsPacker(F(1), F(1))
    for n in range(1, N+1):
        packer.place(n, allow_rotate=True, heuristic='BSSF')
    placed = [PlacedRect(n=p.k, x0=p.x, y0=p.y, rotated=p.rotated) for p in packer.placed]
    return container, placed


def test_empty():
    container = Rect(F(0), F(0), F(1), F(1))
    out = rectangulate_complement_fast(container, [])
    assert len(out) == 1 and out[0] == container


def test_single_corner():
    container = Rect(F(0), F(0), F(1), F(1))
    placed = [PlacedRect(n=2, x0=F(0), y0=F(0), rotated=False)]   # 1/2 × 1/3 at corner
    out = rectangulate_complement_fast(container, placed)
    verify_rectangulation(out, container, placed)
    assert total_area(out) == container.area - placed[0].area


def test_n_50_equivalence():
    container, placed = make_packing(50)
    slow = rectangulate_complement(container, placed)
    fast = rectangulate_complement_fast(container, placed)
    verify_rectangulation(slow, container, placed)
    verify_rectangulation(fast, container, placed)
    assert total_area(slow) == total_area(fast)


def test_n_100_correctness():
    container, placed = make_packing(100)
    fast = rectangulate_complement_fast(container, placed)
    verify_rectangulation(fast, container, placed)


def test_n_200_correctness():
    container, placed = make_packing(200)
    fast = rectangulate_complement_fast(container, placed)
    verify_rectangulation(fast, container, placed)
