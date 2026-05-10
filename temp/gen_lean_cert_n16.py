"""Generate a Lean cert for N=16 BSSF (the doc's exact T_0=16 target)
with parameters (c=1/2, R=8/3, η=0).

This satisfies all Lean conditions and the doc's T1, T3, T4. T2 fails
slightly: (t+1)²/t = 19.06 < 4R/c = 21.33.

Smaller cert, faster to instantiate, illustrates the tightest
warm-start using BSSF burnin.
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from fractions import Fraction
from src.algorithms import MaxRectsPacker
from src.mm_pack.geometry import Rect, FreeBox, FreeBoxKind, PlacedRect
from src.mm_pack.rectangulate_fast import rectangulate_simplified_fast
from src.mm_pack.cellification import cellify_strip
from src.mm_pack.certificate import Certificate, write_certificate

F = Fraction


def build_cert(N: int):
    side = F(1)
    cont = Rect(F(0), F(0), side, side)
    packer = MaxRectsPacker(side, side)
    for n in range(1, N + 1):
        packer.place(n, allow_rotate=True, heuristic="BSSF")
    placed = [
        PlacedRect(n=p.k, x0=p.x, y0=p.y, rotated=p.rotated)
        for p in packer.placed
    ]
    free_rects = rectangulate_simplified_fast(cont, placed)
    lrp_rect = max(free_rects, key=lambda r: (r.min_side, r.area))
    absorbers = []
    dropped = []
    for r in free_rects:
        if r is lrp_rect:
            continue
        if r.aspect > F(64):
            dropped.append(r)
        elif r.aspect > F(2):
            for c in cellify_strip(r):
                absorbers.append(FreeBox(rect=c, kind=FreeBoxKind.ABSORBER))
        else:
            absorbers.append(FreeBox(rect=r, kind=FreeBoxKind.ABSORBER))
    LRP = FreeBox(rect=lrp_rect, kind=FreeBoxKind.LRP)
    return Certificate(
        N=N+1, gamma_num=4, gamma_den=3,
        container=cont, placed=placed, LRP=LRP,
        normal_boxes=[], endpoint_boxes=[], absorbers=absorbers,
    )


def fr(x):
    return f"({x.numerator} : ℚ) / ({x.denominator} : ℚ)"


def rect_lit(x0, y0, x1, y1):
    return ("{ "
        f"x0 := {fr(F(x0))}, y0 := {fr(F(y0))}, "
        f"x1 := {fr(F(x1))}, y1 := {fr(F(y1))}, "
        "hx := by norm_num, hy := by norm_num }"
    )


def placed_lit(p):
    return ("  { "
        f"n := {p.n}, x0 := {fr(F(p.x0))}, y0 := {fr(F(p.y0))}, "
        f"rotated := {'true' if p.rotated else 'false'} "
        "}"
    )


def emit(cert: Certificate, out_path: str, ns: str, c: F, R: F, eta: F):
    placed_str = ",\n".join(placed_lit(p) for p in cert.placed)
    lrp_str = rect_lit(cert.LRP.rect.x0, cert.LRP.rect.y0,
                        cert.LRP.rect.x1, cert.LRP.rect.y1)

    text = f'''import MeirMoser.Certificate
import MeirMoser.CalibratedScheduler
import MeirMoser.MainTheorem

namespace MeirMoser.Certificates.{ns}

open MeirMoser

def container : Rect := {rect_lit(0, 0, 1, 1)}

def placed : List PlacedRect := [
{placed_str}
]

def lrp : Rect := {lrp_str}

def normalBoxes : List NormalBoxRecord := []
def endpointBoxes : List Rect := []
def widthChecks : List NormalWidthCheck := []

def state : TailState :=
  {{ t := {cert.N},
    container := container,
    placed := placed,
    LRP := lrp,
    normalBoxes := normalBoxes,
    endpointBoxes := endpointBoxes }}

/-- N=16 BSSF cert. The smallest balanced warm-start (in terms of t) that
    closes Lean's chain.

    Parameters: c = {c}, R = {R}, η = {eta}.

  This satisfies:
  * Lean conditions (R ≥ 1, (R-1)² ≥ R, R ≤ c·t, etc.) ✓
  * Doc T1 (LRP scale): t = {cert.N} ≥ R/(c·(1-1/R)²) ≈ 13.65 ✓
  * Doc T3 (nbfStep):   t ≥ R/c = 16/3 ≈ 5.33 ✓
  * Doc T4 (c_* margin): c/R = 3/16 ≥ 1/16 ✓

  T2 (freshness): (t+1)²/t = 324/17 ≈ 19.06 < 4R/c = 64/3 ≈ 21.33.
  T2 is a *doc-level* analysis condition; the Lean closure does not
  require it directly. BalancedCertN22 satisfies T2 strictly. -/
def cParam : ℚ := {fr(c)}
def RParam : ℚ := {fr(R)}
def etaParam : ℚ := {fr(eta)}

theorem finite_packing_valid : FinitePacking container placed := by
  native_decide

theorem warm_start_good :
    GoodTailState cParam RParam etaParam state widthChecks := by
  native_decide

theorem state_container_unit : state.container = unitSquare := by
  unfold state container unitSquare
  native_decide

theorem state_prefix_covers :
    ∀ n, 1 ≤ n → n < state.t → ∃ P ∈ state.placed, P.n = n := by
  native_decide

theorem gamma_in_range : 1 * 3 < 4 ∧ 4 * 2 < 3 * 3 := by decide

theorem state_t_pos : 1 ≤ state.t := by native_decide

theorem state_LRP_in_container : state.container.contains state.LRP := by
  native_decide

theorem state_LRP_disj :
    ∀ P ∈ state.placed, Rect.interiorDisjoint state.LRP P.toRect := by
  native_decide

theorem state_c_pos : 0 < cParam := by
  unfold cParam; native_decide

theorem state_R_pos : 0 < RParam := by
  unfold RParam; native_decide

theorem state_R_ge_one : (1 : ℚ) ≤ RParam := by
  unfold RParam; native_decide

theorem state_R_squared : RParam ≤ (RParam - 1) * (RParam - 1) := by
  unfold RParam; native_decide

theorem state_t_large : (RParam : ℚ) ≤ cParam * (state.t : ℕ) := by
  unfold RParam cParam state; native_decide

theorem meir_moser_packs_unit_square :
    MoserPacksFrom 1 unitSquare :=
  meir_moser_packing_from_certificate
    4 3 cParam RParam etaParam gamma_in_range
    state widthChecks warm_start_good
    state_container_unit
    state_prefix_covers
    state_c_pos
    state_R_pos
    state_R_ge_one
    state_R_squared
    state_t_large
    state_t_pos
    state_LRP_in_container
    state_LRP_disj

end MeirMoser.Certificates.{ns}
'''
    with open(out_path, 'w') as f:
        f.write(text)
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    cert = build_cert(16)
    write_certificate(cert, "/workspace/Packing/results/balanced_cert_N16.json")
    emit(cert, "/workspace/Packing/lean/MeirMoser/Certificates/BalancedCertN16.lean",
          "BalancedCertN16", c=F(1, 2), R=F(8, 3), eta=F(0))
