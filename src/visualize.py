"""SVG visualization of Moser packings."""

from __future__ import annotations
from fractions import Fraction
from typing import Iterable, Optional, Tuple

from .geometry import Placement


def _f(x: Fraction) -> float:
    return float(x)


def render_svg(
    placements: Iterable[Placement],
    box_w: Fraction,
    box_h: Fraction,
    pixel: int = 800,
    title: Optional[str] = None,
    label_max_k: int = 60,
) -> str:
    """Render placements into a self-contained SVG string."""
    px_w = pixel
    px_h = int(pixel * float(box_h / box_w))
    sx = px_w / float(box_w)
    sy = px_h / float(box_h)

    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" '
        f'viewBox="0 0 {px_w} {px_h}" width="{px_w}" height="{px_h}">'
        f'<rect x="0" y="0" width="{px_w}" height="{px_h}" fill="white" stroke="black" stroke-width="2"/>'
    ]
    if title:
        parts.append(
            f'<text x="10" y="20" font-family="monospace" font-size="14" fill="#333">{title}</text>'
        )
    plist = list(placements)
    for p in plist:
        x = _f(p.x) * sx
        y = px_h - _f(p.y2) * sy  # flip vertical for SVG (y axis down)
        w = _f(p.w) * sx
        h = _f(p.h) * sy
        # Color by log2(k): warmer = larger k
        import math
        hue = (math.log2(p.k + 1) * 35) % 360
        fill = f"hsl({hue:.0f},70%,82%)"
        parts.append(
            f'<rect x="{x:.2f}" y="{y:.2f}" width="{w:.2f}" height="{h:.2f}" '
            f'fill="{fill}" stroke="#444" stroke-width="0.5"/>'
        )
        if p.k <= label_max_k and w > 12 and h > 12:
            parts.append(
                f'<text x="{x + w/2:.2f}" y="{y + h/2 + 4:.2f}" '
                f'font-family="monospace" font-size="10" '
                f'text-anchor="middle" fill="#222">{p.k}</text>'
            )
    parts.append("</svg>")
    return "".join(parts)


def save_svg(path: str, *args, **kwargs) -> None:
    with open(path, "w") as f:
        f.write(render_svg(*args, **kwargs))
