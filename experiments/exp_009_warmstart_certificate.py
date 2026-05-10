#!/usr/bin/env python3
"""C.2 — Find empirical warm-start parameters and emit a Lean certificate.

We don't try to force `(c, R, η)` to match the framework's idealized values;
instead we MEASURE the actual values from a clean burn-in and emit a certificate
with those exact parameters. The Lean theorem `meir_moser_packing_from_certificate`
takes (c, R, η, γ_num, γ_den) as arguments — it doesn't hard-code thresholds.

The Lean closure remains valid AS LONG AS the calibrated tail theorem (axiom)
admits the actual (c, R, η). When we later prove that axiom in Lean, we'll
need to verify it tolerates these empirical values; until then the certificate
records what actually holds.
"""

from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from fractions import Fraction
from src.mm_pack.calibrated_scheduler import CalibratedScheduler
from src.mm_pack.certificate import Certificate, write_certificate, write_lean_certificate
from src.mm_pack.checker import check_certificate


def measure_state(N: int, gamma_num: int, gamma_den: int, heuristic: str = 'BSSF') -> dict:
    sch = CalibratedScheduler.from_maxrects_burnin(
        burnin_N=N, gamma_num=gamma_num, gamma_den=gamma_den, heuristic=heuristic
    )
    st = sch.state
    cert = Certificate(
        N=st.t, gamma_num=st.gamma_num, gamma_den=st.gamma_den,
        container=st.container, placed=list(st.placed), LRP=st.LRP,
        normal_boxes=list(st.normal_boxes), endpoint_boxes=list(st.endpoint_boxes),
        absorbers=list(st.absorbers),
    )
    s_lrp_x_t = (st.LRP.area * st.t) if st.LRP else Fraction(0)
    aspect = st.LRP.aspect if (st.LRP and st.LRP.area > 0) else Fraction(1)
    p_ep = sum((b.semiperim for b in st.endpoint_boxes), Fraction(0))
    return {
        'sch': sch,
        'cert': cert,
        'c': s_lrp_x_t,
        'R': aspect,
        'eta': p_ep,
        'n_endpoints': len(st.endpoint_boxes),
        'n_normal': len(st.normal_boxes),
        'n_absorbers': len(st.absorbers),
        'n_placed': len(st.placed),
    }


def emit_lean_certificate(d: dict, N: int) -> str:
    """Write a Lean cert file with `theorem warm_start_good`."""
    cert = d['cert']
    c = d['c']
    R = d['R']
    eta = d['eta']
    sch = d['sch']

    # widthChecks: empty (we have no normal boxes from burn-in conversion)
    width_checks_lines = []

    # Format rationals
    def fr(x):
        return f"({x.numerator} : ℚ) / ({x.denominator} : ℚ)"

    def rect_lit(r):
        return ("{ "
                f"x0 := {fr(r.x0)}, y0 := {fr(r.y0)}, "
                f"x1 := {fr(r.x1)}, y1 := {fr(r.y1)}, "
                "hx := by norm_num, hy := by norm_num }")

    def placed_lit(p):
        return ("{ "
                f"n := {p.n}, x0 := {fr(p.x0)}, y0 := {fr(p.y0)}, "
                f"rotated := {'true' if p.rotated else 'false'} "
                "}")

    def normal_box_lit(b):
        # NormalBoxRecord { rect, birthIdx }
        return ("{ "
                f"rect := {rect_lit(b.rect)}, "
                f"birthIdx := {b.birth_index or 0} "
                "}")

    placed_str = ",\n  ".join(placed_lit(p) for p in cert.placed)
    normal_str = ",\n    ".join(normal_box_lit(b) for b in cert.normal_boxes) or ""
    endpoint_str = ",\n    ".join(rect_lit(b.rect) for b in cert.endpoint_boxes) or ""

    lrp_lit = rect_lit(cert.LRP.rect) if cert.LRP else ("{x0 := 0, y0 := 0, x1 := 0, y1 := 0, hx := by decide, hy := by decide}")

    ns = f"WarmStartN{N}"

    text = f"""import MeirMoser.Certificate
import MeirMoser.CalibratedScheduler

namespace MeirMoser.Certificates.{ns}

open MeirMoser

def container : Rect := {rect_lit(cert.container)}

def placed : List PlacedRect := [
  {placed_str}
]

def lrp : Rect := {lrp_lit}

def normalBoxes : List NormalBoxRecord := [
  {normal_str}
]

def endpointBoxes : List Rect := [
  {endpoint_str}
]

def widthChecks : List NormalWidthCheck := []

def state : TailState :=
  {{ t := {cert.N},
    container := container,
    placed := placed,
    LRP := lrp,
    normalBoxes := normalBoxes,
    endpointBoxes := endpointBoxes }}

def cParam : ℚ := {fr(c)}
def RParam : ℚ := {fr(R)}
def etaParam : ℚ := {fr(eta)}

theorem finite_packing_valid : FinitePacking container placed := by
  native_decide

theorem warm_start_good :
    GoodTailState cParam RParam etaParam state widthChecks := by
  native_decide

end MeirMoser.Certificates.{ns}
"""
    out_path = f"/workspace/Packing/lean/MeirMoser/Certificates/WarmStartN{N}.lean"
    with open(out_path, 'w') as f:
        f.write(text)
    return out_path


def main(N: int = 200):
    print(f"=== Measuring warm-start at N={N} ===", flush=True)
    d = measure_state(N, gamma_num=4, gamma_den=3, heuristic='BSSF')
    print(f"  c (S_LRP·t)        = {float(d['c']):.6f} = {d['c']}", flush=True)
    print(f"  R (LRP aspect)     = {float(d['R']):.6f} = {d['R']}", flush=True)
    print(f"  η (P_ep)           = {float(d['eta']):.6f}", flush=True)
    print(f"  n_endpoints        = {d['n_endpoints']}", flush=True)
    print(f"  n_normal           = {d['n_normal']}", flush=True)
    print(f"  n_absorbers        = {d['n_absorbers']}", flush=True)

    out_path = emit_lean_certificate(d, N)
    print(f"\nWrote: {out_path}", flush=True)


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    main(N)
