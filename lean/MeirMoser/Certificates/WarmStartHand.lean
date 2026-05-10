/-
  Hand-built N=1 warm-start certificate.

  After placing D_1 = 1 × 1/2 at the bottom of the unit square, the empty
  region is exactly the top half: a clean 1 × 1/2 rectangle, which we
  designate as the LRP. No endpoints, no normal boxes.

  Empirical parameters (tight):
    c = 1/2  (S_LRP · t = (1/2) · 1)
    R = 2    (LRP aspect = 1 / (1/2))
    η = 0    (no endpoints)

  These are well below the framework's idealized thresholds, so the
  warm-start certificate satisfies `GoodTailState` strictly.
-/
import MeirMoser.Certificate
import MeirMoser.CalibratedScheduler
import MeirMoser.MainTheorem

namespace MeirMoser.Certificates.WarmStartHand

open MeirMoser

def container : Rect :=
  { x0 := 0, y0 := 0, x1 := 1, y1 := 1
    hx := by decide, hy := by decide }

/-- Place D_1 = 1 × 1/2 native at the corner. -/
def placed : List PlacedRect := [
  { n := 1, x0 := 0, y0 := 0, rotated := false }
]

/-- LRP = top half of unit square: [0, 1] × [1/2, 1]. -/
def lrp : Rect :=
  { x0 := 0, y0 := 1/2, x1 := 1, y1 := 1
    hx := by norm_num, hy := by norm_num }

def normalBoxes : List NormalBoxRecord := []
def endpointBoxes : List Rect := []
def widthChecks : List NormalWidthCheck := []

def state : TailState :=
  { t := 2,    -- next index to place is D_2; D_1 is already in `placed`
    container := container,
    placed := placed,
    LRP := lrp,
    normalBoxes := normalBoxes,
    endpointBoxes := endpointBoxes }

/-- Tight parameters: c = 1/2, R = 2, η = 0. -/
def cParam : ℚ := 1/2
def RParam : ℚ := 2
def etaParam : ℚ := 0

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

/-- The hand-built state has S.t = 2. -/
theorem state_t_pos : 1 ≤ state.t := by native_decide

/-- The LRP is contained in the container (top half ⊆ unit square). -/
theorem state_LRP_in_container : state.container.contains state.LRP := by
  native_decide

/-- The LRP (top half) is interior-disjoint from D_1 (bottom half). -/
theorem state_LRP_disj :
    ∀ P ∈ state.placed, Rect.interiorDisjoint state.LRP P.toRect := by
  native_decide

/-
  NOTE (Route A R-A.8):

  Following the upgrade from `good_state_implies_all_steps_succeed`
  (single monolithic axiom) to `c_decay_balanced` (a smaller, focused
  analytic claim), `meir_moser_packing_from_certificate` now requires
  three additional hypotheses on its certificate:

      h_c_pos    : 0 < c
      h_R_pos    : 0 < R
      h_t_large  : (R : ℚ) ≤ c * (S.t : ℕ)

  The hand-built N=1 certificate uses tight parameters `c = 1/2`,
  `R = 2`, with `state.t = 2`, so `R/c = 4` but `state.t = 2 < 4`.
  The hypothesis `h_t_large` therefore FAILS for this minimal
  hand-built certificate, and the closure can no longer be
  instantiated here.

  For a fully closed instantiation use `MeirMoser.Certificates.WarmStartN100`,
  whose `state.t = 101` and `R/c ≈ 70` satisfy `state.t ≥ R/c`.

  The structural verification artefacts (finite_packing_valid,
  warm_start_good, state_container_unit, state_prefix_covers,
  state_LRP_in_container, state_LRP_disj) are retained as a clean
  small-state demo of the calibrated invariants under
  `native_decide`. -/

/-- The hand-built certificate's parameters do NOT satisfy `R ≤ c · t`
    (since `c = 1/2`, `R = 2`, `state.t = 2`, so `R/c = 4 > 2 = t`).
    This is documented as a propositional negation so it cannot be
    accidentally treated as the missing closure hypothesis. -/
theorem state_t_large_fails : ¬ ((RParam : ℚ) ≤ cParam * (state.t : ℕ)) := by
  unfold RParam cParam state; native_decide

end MeirMoser.Certificates.WarmStartHand
