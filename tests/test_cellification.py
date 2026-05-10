"""Tests for mm_pack.cellification."""
from fractions import Fraction as F

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.mm_pack.cellification import cellify_strip, cells_count_along, cell_bounds, ceil_div
from src.mm_pack.geometry import Rect


def test_ceil_div():
    assert ceil_div(10, 3) == 4
    assert ceil_div(9, 3) == 3
    assert ceil_div(0, 5) == 0


def test_cells_count_simple():
    assert cells_count_along(F(1), F(1, 3)) == 3
    assert cells_count_along(F(57, 10), F(1)) == 6
    assert cells_count_along(F(1), F(1)) == 1


def test_cellify_horizontal():
    strip = Rect(F(0), F(0), F(1), F(1, 3))
    cells = cellify_strip(strip)
    assert len(cells) == 3
    total = sum((c.area for c in cells), F(0))
    assert total == strip.area
    for c in cells:
        assert c.aspect <= 2


def test_cellify_total_semiperim_bounded_by_3M():
    strip = Rect(F(0), F(0), F(57, 10), F(1))
    cl, semi, asp = cell_bounds(F(57, 10), F(1))
    assert semi <= 3 * F(57, 10)
    assert asp <= 2


def test_cellify_square_strip():
    sq = Rect(F(0), F(0), F(1), F(1))
    cells = cellify_strip(sq)
    assert len(cells) == 1
    assert cells[0] == sq


def test_cellify_vertical():
    strip = Rect(F(0), F(0), F(1, 3), F(1))
    cells = cellify_strip(strip)
    assert len(cells) == 3
    total = sum((c.area for c in cells), F(0))
    assert total == strip.area


def test_cellify_property_aspect_le_2():
    """For any strip, all cells have aspect ≤ 2."""
    for w_num, w_den, h_num, h_den in [
        (5, 2, 1, 1), (7, 1, 3, 4), (1, 1, 5, 7), (10, 3, 1, 1)
    ]:
        strip = Rect(F(0), F(0), F(w_num, w_den), F(h_num, h_den))
        cells = cellify_strip(strip)
        for c in cells:
            assert c.aspect <= 2, f"aspect {c.aspect} > 2 in cell {c} of strip {strip}"
