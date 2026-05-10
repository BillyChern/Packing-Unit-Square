"""Generate Lean cert file for N=22 balanced cert,
following the WarmStartN100 format closely.
"""
from __future__ import annotations
import sys, os, json
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from fractions import Fraction
from src.mm_pack.certificate import read_certificate

F = Fraction


def fr(x: Fraction) -> str:
    return f"({x.numerator} : ℚ) / ({x.denominator} : ℚ)"


def rect_lit(x0, y0, x1, y1) -> str:
    return (
        "{ "
        f"x0 := {fr(F(x0))}, y0 := {fr(F(y0))}, "
        f"x1 := {fr(F(x1))}, y1 := {fr(F(y1))}, "
        "hx := by norm_num, hy := by norm_num }"
    )


def placed_lit(p) -> str:
    return (
        "  { "
        f"n := {p.n}, x0 := {fr(F(p.x0))}, y0 := {fr(F(p.y0))}, "
        f"rotated := {'true' if p.rotated else 'false'} "
        "}"
    )


def main(in_path, out_path, namespace_suffix, c_val, R_val, eta_val):
    cert = read_certificate(in_path)

    placed_str = ",\n".join(placed_lit(p) for p in cert.placed)

    lrp_str = rect_lit(cert.LRP.rect.x0, cert.LRP.rect.y0,
                        cert.LRP.rect.x1, cert.LRP.rect.y1)

    text = f'''import MeirMoser.Certificate
import MeirMoser.CalibratedScheduler
import MeirMoser.MainTheorem

namespace MeirMoser.Certificates.{namespace_suffix}

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

/-- Cert parameters: c = {c_val}, R = {R_val}, η = {eta_val}.

  We choose:
    R = 8/3 (≥ φ² ≈ 2.618, the smallest "nice" R satisfying (R-1)² ≥ R).
    c = 9/20 (≤ S_LRP · t = 1150/2527 ≈ 0.4551).
    η = 0 (no endpoints — ultra-thin slivers were dropped).

  These satisfy ALL doc-24 T_0 thresholds:
    T1: t = {cert.N} ≥ 16 ✓
    T2: (t+1)²/t ≥ 4R/c ✓
    T3: t ≥ R/c ✓
    T4: c/R = 27/160 ≥ 1/16 ✓
  AND the Lean closure conditions:
    R ≥ 1 ✓
    (R-1)² ≥ R ⟺ R ≥ φ² ✓
    R ≤ c · t ✓
-/
def cParam : ℚ := {fr(c_val)}
def RParam : ℚ := {fr(R_val)}
def etaParam : ℚ := {fr(eta_val)}

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

/-- The R-parameter satisfies `R ≤ (R - 1)²`, equivalently `R ≥ φ²`.
    With R = 8/3: (R-1)² = (5/3)² = 25/9 ≈ 2.778 ≥ R = 8/3 ≈ 2.667. -/
theorem state_R_squared : RParam ≤ (RParam - 1) * (RParam - 1) := by
  unfold RParam; native_decide

/-- The certificate satisfies `R ≤ c · t`.
    With c = 9/20, R = 8/3, t = {cert.N}: c · t = 9·{cert.N}/20 = {9*cert.N}/20.
    R = 8/3 = 160/60. Since 9·{cert.N}/20 = {9*cert.N*3}/{20*3} = {9*cert.N*3}/60 ≥ 160/60 = R, true. -/
theorem state_t_large : (RParam : ℚ) ≤ cParam * (state.t : ℕ) := by
  unfold RParam cParam state; native_decide

/-- THE MAIN INSTANTIATED THEOREM: the Moser sequence packs into the
    unit square (modulo the single remaining project axiom
    `balanced_c_share_positive_axiom` in `MeirMoser.AllStepsSucceedProof`). -/
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

end MeirMoser.Certificates.{namespace_suffix}
'''
    with open(out_path, 'w') as f:
        f.write(text)
    print(f"Wrote Lean cert to {out_path}")
    print(f"  state.t = {cert.N}")
    print(f"  |placed| = {len(cert.placed)}")
    print(f"  c = {c_val}, R = {R_val}, η = {eta_val}")


if __name__ == "__main__":
    main(
        in_path="/workspace/Packing/results/balanced_cert_N22.json",
        out_path="/workspace/Packing/lean/MeirMoser/Certificates/BalancedCertN22.lean",
        namespace_suffix="BalancedCertN22",
        c_val=F(9, 20),
        R_val=F(8, 3),
        eta_val=F(0),
    )
