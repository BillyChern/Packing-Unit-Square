import MeirMoser.Certificate
import MeirMoser.CalibratedScheduler
import MeirMoser.MainTheorem

namespace MeirMoser.Certificates.BalancedCertN22

open MeirMoser

def container : Rect := { x0 := (0 : ℚ) / (1 : ℚ), y0 := (0 : ℚ) / (1 : ℚ), x1 := (1 : ℚ) / (1 : ℚ), y1 := (1 : ℚ) / (1 : ℚ), hx := by norm_num, hy := by norm_num }

def placed : List PlacedRect := [
  { n := 1, x0 := (0 : ℚ) / (1 : ℚ), y0 := (0 : ℚ) / (1 : ℚ), rotated := false },
  { n := 2, x0 := (0 : ℚ) / (1 : ℚ), y0 := (1 : ℚ) / (2 : ℚ), rotated := true },
  { n := 3, x0 := (1 : ℚ) / (3 : ℚ), y0 := (1 : ℚ) / (2 : ℚ), rotated := true },
  { n := 4, x0 := (7 : ℚ) / (12 : ℚ), y0 := (1 : ℚ) / (2 : ℚ), rotated := false },
  { n := 5, x0 := (5 : ℚ) / (6 : ℚ), y0 := (1 : ℚ) / (2 : ℚ), rotated := true },
  { n := 6, x0 := (1 : ℚ) / (3 : ℚ), y0 := (5 : ℚ) / (6 : ℚ), rotated := true },
  { n := 7, x0 := (10 : ℚ) / (21 : ℚ), y0 := (5 : ℚ) / (6 : ℚ), rotated := true },
  { n := 8, x0 := (7 : ℚ) / (12 : ℚ), y0 := (7 : ℚ) / (10 : ℚ), rotated := true },
  { n := 9, x0 := (101 : ℚ) / (168 : ℚ), y0 := (33 : ℚ) / (40 : ℚ), rotated := true },
  { n := 10, x0 := (25 : ℚ) / (36 : ℚ), y0 := (7 : ℚ) / (10 : ℚ), rotated := true },
  { n := 11, x0 := (589 : ℚ) / (840 : ℚ), y0 := (4 : ℚ) / (5 : ℚ), rotated := true },
  { n := 12, x0 := (589 : ℚ) / (840 : ℚ), y0 := (49 : ℚ) / (55 : ℚ), rotated := true },
  { n := 13, x0 := (8497 : ℚ) / (10920 : ℚ), y0 := (49 : ℚ) / (55 : ℚ), rotated := true },
  { n := 14, x0 := (659 : ℚ) / (840 : ℚ), y0 := (4 : ℚ) / (5 : ℚ), rotated := true },
  { n := 15, x0 := (101 : ℚ) / (168 : ℚ), y0 := (337 : ℚ) / (360 : ℚ), rotated := false },
  { n := 16, x0 := (311 : ℚ) / (396 : ℚ), y0 := (7 : ℚ) / (10 : ℚ), rotated := true },
  { n := 17, x0 := (5683 : ℚ) / (6732 : ℚ), y0 := (7 : ℚ) / (10 : ℚ), rotated := true },
  { n := 18, x0 := (673 : ℚ) / (748 : ℚ), y0 := (7 : ℚ) / (10 : ℚ), rotated := false },
  { n := 19, x0 := (673 : ℚ) / (748 : ℚ), y0 := (143 : ℚ) / (190 : ℚ), rotated := false },
  { n := 20, x0 := (13535 : ℚ) / (14212 : ℚ), y0 := (143 : ℚ) / (190 : ℚ), rotated := true },
  { n := 21, x0 := (143 : ℚ) / (168 : ℚ), y0 := (129 : ℚ) / (170 : ℚ), rotated := false },
  { n := 22, x0 := (6431 : ℚ) / (6732 : ℚ), y0 := (7 : ℚ) / (10 : ℚ), rotated := true }
]

def lrp : Rect := { x0 := (673 : ℚ) / (748 : ℚ), y0 := (61 : ℚ) / (76 : ℚ), x1 := (298447 : ℚ) / (298452 : ℚ), y1 := (1 : ℚ) / (1 : ℚ), hx := by norm_num, hy := by norm_num }

def normalBoxes : List NormalBoxRecord := []

def endpointBoxes : List Rect := []

def widthChecks : List NormalWidthCheck := []

def state : TailState :=
  { t := 23,
    container := container,
    placed := placed,
    LRP := lrp,
    normalBoxes := normalBoxes,
    endpointBoxes := endpointBoxes }

/-- Cert parameters: c = 9/20, R = 8/3, η = 0.

  We choose:
    R = 8/3 (≥ φ² ≈ 2.618, the smallest "nice" R satisfying (R-1)² ≥ R).
    c = 9/20 (≤ S_LRP · t = 1150/2527 ≈ 0.4551).
    η = 0 (no endpoints — ultra-thin slivers were dropped).

  These satisfy ALL doc-24 T_0 thresholds:
    T1: t = 23 ≥ 16 ✓
    T2: (t+1)²/t ≥ 4R/c ✓
    T3: t ≥ R/c ✓
    T4: c/R = 27/160 ≥ 1/16 ✓
  AND the Lean closure conditions:
    R ≥ 1 ✓
    (R-1)² ≥ R ⟺ R ≥ φ² ✓
    R ≤ c · t ✓
-/
def cParam : ℚ := (9 : ℚ) / (20 : ℚ)
def RParam : ℚ := (8 : ℚ) / (3 : ℚ)
def etaParam : ℚ := (0 : ℚ) / (1 : ℚ)

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
    With c = 9/20, R = 8/3, t = 23: c · t = 9·23/20 = 207/20.
    R = 8/3 = 160/60. Since 9·23/20 = 621/60 = 621/60 ≥ 160/60 = R, true. -/
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

end MeirMoser.Certificates.BalancedCertN22
