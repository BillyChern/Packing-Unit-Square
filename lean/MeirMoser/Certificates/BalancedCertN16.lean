import MeirMoser.Certificate
import MeirMoser.CalibratedScheduler
import MeirMoser.MainTheorem

namespace MeirMoser.Certificates.BalancedCertN16

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
  { n := 16, x0 := (311 : ℚ) / (396 : ℚ), y0 := (7 : ℚ) / (10 : ℚ), rotated := true }
]

def lrp : Rect := { x0 := (143 : ℚ) / (168 : ℚ), y0 := (7 : ℚ) / (10 : ℚ), x1 := (1 : ℚ) / (1 : ℚ), y1 := (1 : ℚ) / (1 : ℚ), hx := by norm_num, hy := by norm_num }

def normalBoxes : List NormalBoxRecord := []
def endpointBoxes : List Rect := []
def widthChecks : List NormalWidthCheck := []

def state : TailState :=
  { t := 17,
    container := container,
    placed := placed,
    LRP := lrp,
    normalBoxes := normalBoxes,
    endpointBoxes := endpointBoxes }

/-- N=16 BSSF cert. The smallest balanced warm-start (in terms of t) that
    closes Lean's chain.

    Parameters: c = 1/2, R = 8/3, η = 0.

  This satisfies:
  * Lean conditions (R ≥ 1, (R-1)² ≥ R, R ≤ c·t, etc.) ✓
  * Doc T1 (LRP scale): t = 17 ≥ R/(c·(1-1/R)²) ≈ 13.65 ✓
  * Doc T3 (nbfStep):   t ≥ R/c = 16/3 ≈ 5.33 ✓
  * Doc T4 (c_* margin): c/R = 3/16 ≥ 1/16 ✓

  T2 (freshness): (t+1)²/t = 324/17 ≈ 19.06 < 4R/c = 64/3 ≈ 21.33.
  T2 is a *doc-level* analysis condition; the Lean closure does not
  require it directly. BalancedCertN22 satisfies T2 strictly. -/
def cParam : ℚ := (1 : ℚ) / (2 : ℚ)
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

end MeirMoser.Certificates.BalancedCertN16
