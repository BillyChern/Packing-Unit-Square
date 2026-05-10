/-
  CalibratedStripeArea.lean (Route A.5 Task 2)

  Per-step LRP area-share preservation lemma for `calibratedBalancedStep`.

  When `calibratedBalancedStep` succeeds, the rotated D_t (width 1/(t+1),
  height 1/t) is placed and the LRP is shrunk on the chosen cut side by
  the calibrated stripe width `a_t = 1/(t+1) + 1/t²`:
    - x-cut branch (`cutFromX S = true`): LRP loses width `a_t`.
        new_area = (W - a_t) · H = W·H - a_t·H.
    - y-cut branch (`cutFromX S = false`): LRP loses height `a_t`.
        new_area = W · (H - a_t) = W·H - a_t·W.

  In both branches `new_t = old_t + 1` and the area loss is at most
  `a_t · maxSide` (the orthogonal side, bounded by maxSide). Hence
    new_area ≥ old_area - a_t · maxSide.
  Multiplying by `t+1`:
    new_area · (t+1) ≥ (old_area - a_t · maxSide) · (t+1)
                     = old_area · t + old_area - a_t · maxSide · (t+1)
                     ≥ old_area · t - a_t · maxSide · (t+1).
  This gives the per-step area-share bound

    new_LRP.area · (t+1) ≥ old_LRP.area · t - a_t · LRP.maxSide · (t+1).

  The form `(t+1)` (rather than `(1 + 1/t) = (t+1)/t`) is the natural
  analogue of the simplified `balancedStep` bound: in the simplified
  step, the loss factor along the longer side is `1/t` and the bound is
  `maxSide · (1 + 1/t) = maxSide · (1/t) · (t+1)`. With the calibrated
  step, the loss factor along either side is `a_t`, so the natural bound
  is `a_t · maxSide · (t+1)` (substituting `a_t` for `1/t`).
-/
import MeirMoser.CalibratedStripe
import MeirMoser.SchedulerInductionBalanced
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace MeirMoser

/-- (Route A.5 Task 2) Per-step LRP area-share preservation for
    `calibratedBalancedStep`.

    On the success branch, the new `(LRP.area · t)` decreases by at most
    `a_t · LRP.maxSide · (t+1)` compared to the old `(LRP.area · t)`,
    where `a_t = calibratedStripeWidthRat γ_num γ_den t`. -/
theorem calibratedBalancedStep_LRP_area_lower
    (γ_num γ_den : ℕ) (S : TailState)
    (h_fit : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
             (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0)
    (h_t_pos : 0 < S.t)
    : (calibratedBalancedStep γ_num γ_den S).LRP.area *
        ((calibratedBalancedStep γ_num γ_den S).t : ℚ) ≥
      S.LRP.area * (S.t : ℚ) -
        calibratedStripeWidthRat γ_num γ_den S.t * S.LRP.maxSide *
          (((S.t + 1 : ℕ) : ℚ)) := by
  -- Unfold the success branch.
  unfold calibratedBalancedStep
  rw [dif_pos h_fit]
  -- Abbreviations.
  set t : ℚ := (S.t : ℚ) with ht_def
  set H : ℚ := S.LRP.y1 - S.LRP.y0 with hH_def
  set W : ℚ := S.LRP.x1 - S.LRP.x0 with hW_def
  set a : ℚ := calibratedStripeWidthRat γ_num γ_den S.t with ha_def
  -- Non-negativity facts.
  have hH_nn : 0 ≤ H := by
    have := S.LRP.hy
    simp [hH_def]; linarith
  have hW_nn : 0 ≤ W := by
    have := S.LRP.hx
    simp [hW_def]; linarith
  have ha_nn : 0 ≤ a := calibratedStripeWidthRat_nonneg γ_num γ_den S.t
  -- 0 < S.t as a rational.
  have ht_pos : (0 : ℚ) < t := by
    have : (0 : ℚ) < (S.t : ℚ) := by exact_mod_cast h_t_pos
    simpa [ht_def] using this
  -- Cast facts.
  have hcast_t : ((S.t : ℕ) : ℚ) = t := by simp [ht_def]
  have hcast_tp1 : (((S.t + 1 : ℕ) : ℕ) : ℚ) = t + 1 := by
    push_cast
    simp [ht_def]
  -- t + 1 > 0.
  have htp1_pos : (0 : ℚ) < t + 1 := by linarith
  -- Bounds a ≤ W and 1/t ≤ H from h_fit.
  have hWmin : a ≤ W := by
    have h := h_fit.1
    simpa [ha_def, hW_def] using h
  have hHmin : (1 : ℚ) / t ≤ H := by
    have h := h_fit.2
    simpa [hcast_t, hH_def] using h
  -- maxSide bounds: maxSide ≥ W and maxSide ≥ H.
  have hMax_ge_W : W ≤ S.LRP.maxSide := by
    unfold Rect.maxSide
    have : Rect.width S.LRP = W := by simp [Rect.width, hW_def]
    rw [show Rect.width S.LRP = W from this]
    exact le_max_left _ _
  have hMax_ge_H : H ≤ S.LRP.maxSide := by
    unfold Rect.maxSide
    have hwid : Rect.width S.LRP = W := by simp [Rect.width, hW_def]
    have hhgt : Rect.height S.LRP = H := by simp [Rect.height, hH_def]
    rw [show Rect.width S.LRP = W from hwid,
        show Rect.height S.LRP = H from hhgt]
    exact le_max_right _ _
  -- maxSide is also ≥ 0.
  have hMax_nn : 0 ≤ S.LRP.maxSide :=
    le_trans hW_nn hMax_ge_W
  -- a * H ≤ a * maxSide and a * W ≤ a * maxSide.
  have h_aH_le : a * H ≤ a * S.LRP.maxSide := by
    exact mul_le_mul_of_nonneg_left hMax_ge_H ha_nn
  have h_aW_le : a * W ≤ a * S.LRP.maxSide := by
    exact mul_le_mul_of_nonneg_left hMax_ge_W ha_nn
  -- Case-split on the cut direction.
  by_cases hcut : cutFromX S = true
  · -- x-cut branch.
    rw [dif_pos hcut]
    -- Expose `area`, `width`, `height` for the new LRP.
    simp only [Rect.area, Rect.width, Rect.height]
    -- Show the goal in a normalized form.
    show (S.LRP.x1 - (S.LRP.x0 + calibratedStripeWidthRat γ_num γ_den S.t)) *
          (S.LRP.y1 - S.LRP.y0) * ((S.t + 1 : ℕ) : ℚ) ≥
         (S.LRP.x1 - S.LRP.x0) * (S.LRP.y1 - S.LRP.y0) * ((S.t : ℕ) : ℚ) -
          calibratedStripeWidthRat γ_num γ_den S.t * S.LRP.maxSide *
            ((S.t + 1 : ℕ) : ℚ)
    -- Rewrite using W, H, t, a.
    rw [show S.LRP.x1 - (S.LRP.x0 + calibratedStripeWidthRat γ_num γ_den S.t)
            = W - a by simp [hW_def, ha_def]; ring,
        show S.LRP.y1 - S.LRP.y0 = H from rfl,
        show S.LRP.x1 - S.LRP.x0 = W from rfl,
        show calibratedStripeWidthRat γ_num γ_den S.t = a from rfl,
        show ((S.t + 1 : ℕ) : ℚ) = t + 1 from hcast_tp1,
        show ((S.t : ℕ) : ℚ) = t from hcast_t]
    -- Goal:
    --   (W - a) * H * (t+1) ≥ W * H * t - a * maxSide * (t+1).
    -- Expand: LHS = W*H*(t+1) - a*H*(t+1) ≥ W*H*(t+1) - a*maxSide*(t+1)
    --              = W*H*t + W*H - a*maxSide*(t+1).
    -- Hence LHS ≥ W*H*t - a*maxSide*(t+1) + W*H ≥ RHS (since W*H ≥ 0).
    have hWH_nn : 0 ≤ W * H := mul_nonneg hW_nn hH_nn
    nlinarith [hWH_nn, hH_nn, hW_nn, ha_nn, hMax_nn, hMax_ge_H, hMax_ge_W,
               h_aH_le, h_aW_le, ht_pos, htp1_pos, hWmin]
  · -- y-cut branch.
    rw [dif_neg hcut]
    -- Expose `area`, `width`, `height`.
    simp only [Rect.area, Rect.width, Rect.height]
    show (S.LRP.x1 - S.LRP.x0) *
          (S.LRP.y1 - (S.LRP.y0 + calibratedStripeWidthRat γ_num γ_den S.t)) *
          ((S.t + 1 : ℕ) : ℚ) ≥
         (S.LRP.x1 - S.LRP.x0) * (S.LRP.y1 - S.LRP.y0) * ((S.t : ℕ) : ℚ) -
          calibratedStripeWidthRat γ_num γ_den S.t * S.LRP.maxSide *
            ((S.t + 1 : ℕ) : ℚ)
    -- Rewrite using W, H, t, a.
    rw [show S.LRP.y1 - (S.LRP.y0 + calibratedStripeWidthRat γ_num γ_den S.t)
            = H - a by simp [hH_def, ha_def]; ring,
        show S.LRP.y1 - S.LRP.y0 = H from rfl,
        show S.LRP.x1 - S.LRP.x0 = W from rfl,
        show calibratedStripeWidthRat γ_num γ_den S.t = a from rfl,
        show ((S.t + 1 : ℕ) : ℚ) = t + 1 from hcast_tp1,
        show ((S.t : ℕ) : ℚ) = t from hcast_t]
    -- Goal:
    --   W * (H - a) * (t+1) ≥ W * H * t - a * maxSide * (t+1).
    -- Expand: LHS = W*H*(t+1) - a*W*(t+1) ≥ W*H*(t+1) - a*maxSide*(t+1)
    --              = W*H*t + W*H - a*maxSide*(t+1) ≥ W*H*t - a*maxSide*(t+1).
    have hWH_nn : 0 ≤ W * H := mul_nonneg hW_nn hH_nn
    nlinarith [hWH_nn, hH_nn, hW_nn, ha_nn, hMax_nn, hMax_ge_H, hMax_ge_W,
               h_aH_le, h_aW_le, ht_pos, htp1_pos, hWmin]

end MeirMoser
