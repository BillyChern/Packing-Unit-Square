/-
  CalibratedStripe.lean (Route A.5 Task 1): the genuinely calibrated step.

  Stripe width `a_t = 1/(t+1) + t^{-γ}` (for γ ∈ (1, 3/2)). The extra `t^{-γ}`
  term is what makes `Σ a_t · shorter_t` convergent, restoring soundness.

  We use a CONCRETE RATIONAL LOWER BOUND for `t^{-γ}`:
    `calibratedExtraSlackRat γ_num γ_den t = 1 / (t * t)`  (for `t ≥ 1`)
  which is `≤ t^{-γ}` for any `γ ≤ 2` and `t ≥ 1`. The Real-valued bound
  is bridged in `CalibratedStripeRpowBound.lean` (Task 7 of Route A.5).

  This file:
    1. Defines `calibratedExtraSlackRat`, `calibratedStripeWidthRat`.
    2. Defines `calibratedBalancedStep` (mirrors `balancedStep` with
       `a_t` in place of `1/(t+1)` along the longer direction).
    3. Defines `iteratedCalibrated` and proves the basic structural
       passthroughs (container, t-advance).
-/
import MeirMoser.CalibratedScheduler
import MeirMoser.SchedulerInductionBalanced  -- for cutFromX
import Mathlib.Tactic

namespace MeirMoser

/-- Concrete rational lower bound for `t^{-γ}` (with `γ = γ_num/γ_den`).

    We use the simple bound `1/(t*t)` which is `≤ t^{-γ}` for `γ ≤ 2`
    and `t ≥ 1`. The arguments `γ_num`, `γ_den` are kept in the
    signature for downstream consistency; they do not appear in the
    definition itself (they enter via the bridge lemma in
    `CalibratedStripeRpowBound.lean`).

    For `t = 0` we return `0` (sentinel; we never iterate from `t = 0`). -/
def calibratedExtraSlackRat (γ_num γ_den t : ℕ) : ℚ :=
  if t = 0 then 0 else 1 / (((t : ℕ) * (t : ℕ) : ℕ) : ℕ)

/-- Total stripe width `a_t = 1/(t+1) + extraSlack`. -/
def calibratedStripeWidthRat (γ_num γ_den t : ℕ) : ℚ :=
  1 / ((t + 1 : ℕ) : ℕ) + calibratedExtraSlackRat γ_num γ_den t

/-- The extra slack is non-negative. -/
theorem calibratedExtraSlackRat_nonneg (γ_num γ_den t : ℕ) :
    (0 : ℚ) ≤ calibratedExtraSlackRat γ_num γ_den t := by
  unfold calibratedExtraSlackRat
  split_ifs <;> positivity

/-- The total stripe width is non-negative. -/
theorem calibratedStripeWidthRat_nonneg (γ_num γ_den t : ℕ) :
    (0 : ℚ) ≤ calibratedStripeWidthRat γ_num γ_den t := by
  unfold calibratedStripeWidthRat
  have h1 : (0 : ℚ) ≤ 1 / ((t + 1 : ℕ) : ℕ) := by positivity
  have h2 := calibratedExtraSlackRat_nonneg γ_num γ_den t
  linarith

/-- The width-fragment lower bound: `1/(t+1) ≤ a_t`. -/
theorem one_div_succ_le_calibratedStripeWidthRat (γ_num γ_den t : ℕ) :
    (1 : ℚ) / ((t + 1 : ℕ) : ℕ) ≤ calibratedStripeWidthRat γ_num γ_den t := by
  unfold calibratedStripeWidthRat
  have := calibratedExtraSlackRat_nonneg γ_num γ_den t
  linarith

/-- For `t ≥ 1`: `1/t ≤ a_t`. The algebra is
    `1/(t+1) + 1/t² ≥ 1/t ⇔ t² + (t+1) ≥ t(t+1) ⇔ 1 ≥ 0`. -/
theorem one_div_le_calibratedStripeWidthRat
    (γ_num γ_den t : ℕ) (h_t : 0 < t) :
    (1 : ℚ) / ((t : ℕ) : ℕ) ≤ calibratedStripeWidthRat γ_num γ_den t := by
  unfold calibratedStripeWidthRat calibratedExtraSlackRat
  have h_t_ne : t ≠ 0 := Nat.pos_iff_ne_zero.mp h_t
  rw [if_neg h_t_ne]
  -- Goal: 1/t ≤ 1/(t+1) + 1/(t*t)
  have h_t_pos_q : (0 : ℚ) < (t : ℕ) := by exact_mod_cast h_t
  have h_tt_pos : (0 : ℚ) < ((t : ℕ) * (t : ℕ) : ℕ) := by
    have : (0 : ℕ) < t * t := Nat.mul_pos h_t h_t
    exact_mod_cast this
  have h_t1_pos : (0 : ℚ) < ((t + 1 : ℕ) : ℕ) := by
    have : (0 : ℕ) < t + 1 := Nat.succ_pos _
    exact_mod_cast this
  -- Cross-multiply: equivalent to t*(t+1) ≤ t*t + (t+1)
  rw [div_add_div _ _ (ne_of_gt h_t1_pos) (ne_of_gt h_tt_pos),
      div_le_div_iff₀ h_t_pos_q (by positivity)]
  push_cast
  ring_nf
  nlinarith [sq_nonneg ((t : ℚ) - 1), h_t_pos_q]

/-- One calibrated balanced step.

    Always rotates D_t (placed dim `1/(t+1)` wide × `1/t` tall). Cuts a stripe of
    length `a_t = 1/(t+1) + 1/t²` from the longer side of the LRP.

    Fit hypothesis: `a_t ≤ x1 - x0 ∧ 1/t ≤ y1 - y0`. In the y-cut branch
    we additionally use `cutFromX S = false` to conclude `x1 - x0 < y1 - y0`,
    which combined with `a_t ≤ x1 - x0` gives `a_t < y1 - y0` so the
    horizontal stripe of height `a_t` fits.

    Returns `S` unchanged if rotated D_t doesn't fit. -/
def calibratedBalancedStep (γ_num γ_den : ℕ) (S : TailState) : TailState :=
  let n := S.t
  let a_t : ℚ := calibratedStripeWidthRat γ_num γ_den n
  let h_d : ℚ := 1 / ((n : ℕ) : ℕ)            -- rotated D_n height = 1/n
  let w_d : ℚ := 1 / ((n + 1 : ℕ) : ℕ)        -- rotated D_n width  = 1/(n+1)
  if hcanFit : a_t ≤ S.LRP.x1 - S.LRP.x0 ∧ h_d ≤ S.LRP.y1 - S.LRP.y0 then
    if hcut : cutFromX S = true then
      -- x-cut: vertical stripe of width a_t on the left of LRP.
      { t := n + 1
        container := S.container
        placed := S.placed ++ [
          { n := n, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true }]
        LRP :=
          { x0 := S.LRP.x0 + a_t
            y0 := S.LRP.y0
            x1 := S.LRP.x1
            y1 := S.LRP.y1
            hx := by have := hcanFit.1; linarith
            hy := S.LRP.hy }
        normalBoxes := S.normalBoxes ++ [{
          rect :=
            { x0 := S.LRP.x0
              y0 := S.LRP.y0 + h_d
              x1 := S.LRP.x0 + a_t
              y1 := S.LRP.y1
              hx := by
                have h_a_nn : (0 : ℚ) ≤ a_t :=
                  calibratedStripeWidthRat_nonneg γ_num γ_den n
                linarith
              hy := by have := hcanFit.2; linarith }
          birthIdx := n }]
        endpointBoxes := S.endpointBoxes }
    else
      -- y-cut: horizontal stripe of height a_t on the bottom of LRP.
      -- We need a_t ≤ y1 - y0. Using cutFromX = false: x1-x0 < y1-y0, and
      -- hcanFit.1 gives a_t ≤ x1-x0, so a_t ≤ x1-x0 < y1-y0.
      { t := n + 1
        container := S.container
        placed := S.placed ++ [
          { n := n, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true }]
        LRP :=
          { x0 := S.LRP.x0
            y0 := S.LRP.y0 + a_t
            x1 := S.LRP.x1
            y1 := S.LRP.y1
            hx := S.LRP.hx
            hy := by
              -- Extract S.LRP.x1-x0 < S.LRP.y1-y0 from `cutFromX S = false`.
              have hcut_eq : cutFromX S = false := by
                cases hcase : cutFromX S
                · rfl
                · exact absurd hcase hcut
              unfold cutFromX at hcut_eq
              have h_lt : S.LRP.x1 - S.LRP.x0 < S.LRP.y1 - S.LRP.y0 := by
                by_contra hge
                push_neg at hge
                simp [decide_eq_false_iff_not, hge] at hcut_eq
              have := hcanFit.1
              linarith }
        normalBoxes := S.normalBoxes ++ [{
          rect :=
            { x0 := S.LRP.x0 + w_d
              y0 := S.LRP.y0
              x1 := S.LRP.x1
              y1 := S.LRP.y0 + a_t
              hx := by
                -- 1/(n+1) ≤ a_t ≤ x1 - x0
                have h_w_le_a : w_d ≤ a_t :=
                  one_div_succ_le_calibratedStripeWidthRat γ_num γ_den n
                have := hcanFit.1
                linarith
              hy := by
                have h_a_nn : (0 : ℚ) ≤ a_t :=
                  calibratedStripeWidthRat_nonneg γ_num γ_den n
                linarith }
          birthIdx := n }]
        endpointBoxes := S.endpointBoxes }
  else
    S

/-- Iterate the calibrated balanced step k times. -/
def iteratedCalibrated (γ_num γ_den : ℕ) : ℕ → TailState → TailState
  | 0, S => S
  | (k+1), S => calibratedBalancedStep γ_num γ_den (iteratedCalibrated γ_num γ_den k S)

@[simp] theorem iteratedCalibrated_zero (γ_num γ_den : ℕ) (S : TailState) :
    iteratedCalibrated γ_num γ_den 0 S = S := rfl

@[simp] theorem iteratedCalibrated_succ (γ_num γ_den : ℕ) (k : ℕ) (S : TailState) :
    iteratedCalibrated γ_num γ_den (k+1) S =
      calibratedBalancedStep γ_num γ_den (iteratedCalibrated γ_num γ_den k S) := rfl

/-- The calibrated balanced step preserves the container. -/
theorem calibratedBalancedStep_container (γ_num γ_den : ℕ) (S : TailState) :
    (calibratedBalancedStep γ_num γ_den S).container = S.container := by
  unfold calibratedBalancedStep
  by_cases h : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0
  · rw [dif_pos h]
    by_cases hcut : cutFromX S = true
    · rw [dif_pos hcut]
    · rw [dif_neg hcut]
  · rw [dif_neg h]

/-- Step's `t` advances by 1 when rotated D_t fits in the LRP. -/
theorem calibratedBalancedStep_t_advances {γ_num γ_den : ℕ} {S : TailState}
    (h_fit : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
             (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    (calibratedBalancedStep γ_num γ_den S).t = S.t + 1 := by
  unfold calibratedBalancedStep
  rw [dif_pos h_fit]
  by_cases hcut : cutFromX S = true
  · rw [dif_pos hcut]
  · rw [dif_neg hcut]

end MeirMoser
