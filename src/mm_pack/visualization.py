"""Minimal SVG renderer for calibrated state visualization."""

from __future__ import annotations
from fractions import Fraction
from pathlib import Path
from typing import Optional

from .certificate import Certificate
from .geometry import FreeBox, FreeBoxKind, PlacedRect, Rect

F = Fraction

KIND_COLOR = {
    FreeBoxKind.LRP: "#a8d5ff",
    FreeBoxKind.NORMAL: "#d6f5d6",
    FreeBoxKind.ENDPOINT: "#fff5cc",
    FreeBoxKind.ABSORBER: "#f0e0ff",
    FreeBoxKind.GENERIC: "#eeeeee",
}


def render_svg(cert: Certificate, path: str, side_pixels: int = 1000) -> None:
    cont = cert.container
    W = float(cont.x1 - cont.x0)
    H = float(cont.y1 - cont.y0)
    sx = side_pixels / W
    sy = side_pixels / H

    def emit_rect(r: Rect, fill: str, opacity: float = 0.6, stroke: str = "#888") -> str:
        x = (float(r.x0) - float(cont.x0)) * sx
        y = side_pixels - (float(r.y1) - float(cont.y0)) * sy   # flip y
        w = (float(r.x1) - float(r.x0)) * sx
        h = (float(r.y1) - float(r.y0)) * sy
        return (
            f'<rect x="{x:.2f}" y="{y:.2f}" width="{w:.2f}" height="{h:.2f}" '
            f'fill="{fill}" fill-opacity="{opacity}" stroke="{stroke}" stroke-width="0.5"/>'
        )

    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{side_pixels}" '
        f'height="{side_pixels}" viewBox="0 0 {side_pixels} {side_pixels}">'
    ]
    parts.append(f'<rect x="0" y="0" width="{side_pixels}" height="{side_pixels}" fill="white"/>')

    # Free boxes underneath, placed on top
    if cert.LRP is not None:
        parts.append(emit_rect(cert.LRP.rect, KIND_COLOR[FreeBoxKind.LRP]))
    for b in cert.normal_boxes:
        parts.append(emit_rect(b.rect, KIND_COLOR[FreeBoxKind.NORMAL]))
    for b in cert.endpoint_boxes:
        parts.append(emit_rect(b.rect, KIND_COLOR[FreeBoxKind.ENDPOINT]))
    for b in cert.absorbers:
        parts.append(emit_rect(b.rect, KIND_COLOR[FreeBoxKind.ABSORBER], opacity=0.5))

    for p in cert.placed:
        parts.append(emit_rect(p.rect, "#666666", opacity=0.7, stroke="#222"))

    parts.append("</svg>")
    Path(path).write_text("\n".join(parts))


__all__ = ["render_svg"]
