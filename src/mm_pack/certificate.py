"""Certificate JSON schema (per agent_execution_brief §9) + Lean exporter."""

from __future__ import annotations
from dataclasses import dataclass, asdict, field
from fractions import Fraction
import json
from pathlib import Path
from typing import Any, Dict, List, Optional

from .geometry import FreeBox, FreeBoxKind, PlacedRect, Rect

F = Fraction


def frac_to_str(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def parse_frac(s: str) -> Fraction:
    return Fraction(s)


def rect_to_dict(r: Rect) -> Dict[str, str]:
    return {
        "x0": frac_to_str(Fraction(r.x0)),
        "y0": frac_to_str(Fraction(r.y0)),
        "x1": frac_to_str(Fraction(r.x1)),
        "y1": frac_to_str(Fraction(r.y1)),
    }


def rect_from_dict(d: Dict[str, str]) -> Rect:
    return Rect(
        x0=Fraction(d["x0"]),
        y0=Fraction(d["y0"]),
        x1=Fraction(d["x1"]),
        y1=Fraction(d["y1"]),
    )


def placed_to_dict(p: PlacedRect) -> Dict[str, Any]:
    return {
        "n": p.n,
        "x0": frac_to_str(p.x0),
        "y0": frac_to_str(p.y0),
        "rotated": p.rotated,
    }


def placed_from_dict(d: Dict[str, Any]) -> PlacedRect:
    return PlacedRect(
        n=int(d["n"]),
        x0=Fraction(d["x0"]),
        y0=Fraction(d["y0"]),
        rotated=bool(d["rotated"]),
    )


def freebox_to_dict(b: FreeBox) -> Dict[str, Any]:
    return {
        "kind": b.kind.value,
        "rect": rect_to_dict(b.rect),
        "birth_index": b.birth_index,
    }


def freebox_from_dict(d: Dict[str, Any]) -> FreeBox:
    return FreeBox(
        rect=rect_from_dict(d["rect"]),
        kind=FreeBoxKind(d["kind"]),
        birth_index=d.get("birth_index"),
    )


@dataclass
class Certificate:
    """Warm-start certificate for the calibrated tail theorem."""

    N: int                                        # next index to place
    gamma_num: int                                # γ = gamma_num / gamma_den
    gamma_den: int
    container: Rect                               # ambient container [0,W]×[0,H]
    placed: List[PlacedRect] = field(default_factory=list)
    LRP: Optional[FreeBox] = None
    normal_boxes: List[FreeBox] = field(default_factory=list)
    endpoint_boxes: List[FreeBox] = field(default_factory=list)
    absorbers: List[FreeBox] = field(default_factory=list)
    claimed_bounds: Dict[str, str] = field(default_factory=dict)


def write_certificate(c: Certificate, path: str) -> None:
    out = {
        "problem": "Meir-Moser Concrete Mathematics 2.37",
        "schema_version": 1,
        "N": c.N,
        "gamma_num": c.gamma_num,
        "gamma_den": c.gamma_den,
        "container": rect_to_dict(c.container),
        "placed_rectangles": [placed_to_dict(p) for p in c.placed],
        "free_state": {
            "LRP": freebox_to_dict(c.LRP) if c.LRP else None,
            "normal_boxes": [freebox_to_dict(b) for b in c.normal_boxes],
            "endpoint_boxes": [freebox_to_dict(b) for b in c.endpoint_boxes],
            "absorbers": [freebox_to_dict(b) for b in c.absorbers],
        },
        "claimed_bounds": c.claimed_bounds,
    }
    Path(path).write_text(json.dumps(out, indent=2))


def read_certificate(path: str) -> Certificate:
    raw = json.loads(Path(path).read_text())
    fs = raw["free_state"]
    return Certificate(
        N=int(raw["N"]),
        gamma_num=int(raw["gamma_num"]),
        gamma_den=int(raw["gamma_den"]),
        container=rect_from_dict(raw["container"]),
        placed=[placed_from_dict(p) for p in raw["placed_rectangles"]],
        LRP=freebox_from_dict(fs["LRP"]) if fs.get("LRP") else None,
        normal_boxes=[freebox_from_dict(b) for b in fs.get("normal_boxes", [])],
        endpoint_boxes=[freebox_from_dict(b) for b in fs.get("endpoint_boxes", [])],
        absorbers=[freebox_from_dict(b) for b in fs.get("absorbers", [])],
        claimed_bounds=raw.get("claimed_bounds", {}),
    )


def write_lean_certificate(c: Certificate, path: str, namespace_suffix: Optional[str] = None) -> None:
    """Emit a Lean file defining all data + theorem proved by `native_decide`."""
    ns = namespace_suffix or f"N{c.N}Gamma{c.gamma_num}_{c.gamma_den}"

    def fr(x: Fraction) -> str:
        return f"({x.numerator} : ℚ) / ({x.denominator} : ℚ)"

    def rect_lit(r: Rect) -> str:
        return (
            "{ "
            f"x0 := {fr(r.x0)}, y0 := {fr(r.y0)}, "
            f"x1 := {fr(r.x1)}, y1 := {fr(r.y1)}, "
            "hx := by norm_num, hy := by norm_num }"
        )

    def placed_lit(p: PlacedRect) -> str:
        return (
            "{ "
            f"n := {p.n}, x0 := {fr(p.x0)}, y0 := {fr(p.y0)}, "
            f"rotated := {'true' if p.rotated else 'false'} "
            "}"
        )

    placed_list = ",\n  ".join(placed_lit(p) for p in c.placed)
    lrp_str = rect_lit(c.LRP.rect) if c.LRP else "default"
    normal_list = ",\n    ".join(rect_lit(b.rect) for b in c.normal_boxes)
    ep_list = ",\n    ".join(rect_lit(b.rect) for b in c.endpoint_boxes)

    text = f"""import MeirMoser.Certificate
import MeirMoser.CalibratedScheduler

namespace MeirMoser.Certificates.{ns}

open MeirMoser

def container : Rect := {rect_lit(c.container)}

def placed : List PlacedRect := [
  {placed_list}
]

def lrp : Rect := {lrp_str}

def normalBoxes : List Rect := [
  {normal_list}
]

def endpointBoxes : List Rect := [
  {ep_list}
]

def gammaNum : Nat := {c.gamma_num}
def gammaDen : Nat := {c.gamma_den}

theorem finite_packing_valid : FinitePacking container placed := by
  native_decide

end MeirMoser.Certificates.{ns}
"""
    Path(path).write_text(text)


__all__ = [
    "Certificate",
    "write_certificate",
    "read_certificate",
    "write_lean_certificate",
    "frac_to_str",
    "parse_frac",
]
