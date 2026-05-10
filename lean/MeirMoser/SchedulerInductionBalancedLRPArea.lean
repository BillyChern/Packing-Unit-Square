/-
  SchedulerInductionBalancedLRPArea.lean

  Per-step LRP area-share preservation lemma (Route A R-A.2) for the BALANCED
  calibrated step.

  When `balancedStep` succeeds, the rotated D_t (width 1/(t+1), height 1/t)
  is placed and the LRP is shrunk on the LONGER side:
    - x-cut branch (LRP.width ≥ LRP.height):
        LRP loses width 1/(t+1).
        new_area = (W - 1/(t+1)) · H = W·H - H/(t+1).
    - y-cut branch (LRP.width < LRP.height):
        LRP loses height 1/t.
        new_area = W · (H - 1/t) = W·H - W/t.

  In both branches `new_t = old_t + 1`. We prove the lower bound

    new_LRP.area · (t+1) ≥ old_LRP.area · t - LRP.maxSide · (1 + 1/t)

  which mirrors the simplified-step lemma `calibratedStep_LRP_area_lower`
  (with `LRP.height` replaced by `LRP.maxSide`, since the cut may be from
  either side).
-/
import MeirMoser.SchedulerInductionBalanced
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace MeirMoser

/-- (Route A R-A.2) Per-step LRP area-share preservation for `balancedStep`.

    On the success branch, the new `(LRP.area · t)` decreases by at most
    `LRP.maxSide · (1 + 1/t)` compared to the old `(LRP.area · t)`. -/
theorem balancedStep_LRP_area_lower
    (S : TailState)
    (h_fit :
      (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
      (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0)
    (h_t_pos : 0 < S.t)
    : (balancedStep S).LRP.area * ((balancedStep S).t : ℚ) ≥
        S.LRP.area * (S.t : ℚ) -
        S.LRP.maxSide * (1 + 1 / (S.t : ℕ)) := by
  -- Unfold the success branch.
  unfold balancedStep
  rw [dif_pos h_fit]
  -- Abbreviations.
  set t : ℚ := (S.t : ℚ) with ht_def
  set H : ℚ := S.LRP.y1 - S.LRP.y0 with hH_def
  set W : ℚ := S.LRP.x1 - S.LRP.x0 with hW_def
  -- Non-negativity facts.
  have hH_nn : 0 ≤ H := by
    have := S.LRP.hy
    simp [hH_def]; linarith
  have hW_nn : 0 ≤ W := by
    have := S.LRP.hx
    simp [hW_def]; linarith
  -- 0 < S.t as a rational.
  have ht_pos : (0 : ℚ) < t := by
    have : (0 : ℚ) < (S.t : ℚ) := by exact_mod_cast h_t_pos
    simpa [ht_def] using this
  have ht_ne : (t : ℚ) ≠ 0 := ne_of_gt ht_pos
  -- Cast facts.
  have hcast_t : ((S.t : ℕ) : ℚ) = t := by simp [ht_def]
  have hcast_tp1 : (((S.t + 1 : ℕ) : ℕ) : ℚ) = t + 1 := by
    push_cast
    simp [ht_def]
  -- t + 1 > 0.
  have htp1_pos : (0 : ℚ) < t + 1 := by linarith
  have htp1_ne : (t + 1 : ℚ) ≠ 0 := ne_of_gt htp1_pos
  -- Bounds 1/(t+1) ≤ W and 1/t ≤ H from h_fit, expressed in t.
  -- After `set`, `h_fit.2` is already `1 / t ≤ H`.
  -- For `h_fit.1`, the cast `↑(S.t + 1)` still needs to be rewritten to `t + 1`.
  have hWmin : (1 : ℚ) / (t + 1) ≤ W := by
    have h := h_fit.1
    rw [hcast_tp1] at h
    exact h
  have hHmin : (1 : ℚ) / t ≤ H := h_fit.2
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
  -- Auxiliary: 1/t > 0 and (1 + 1/t) > 0.
  have hu_def : (1 : ℚ) / t * t = 1 := by field_simp
  have hu_nn : 0 ≤ (1 : ℚ) / t := one_div_nonneg.mpr (le_of_lt ht_pos)
  -- Case-split on the cut direction.
  by_cases hcut : cutFromX S
  · -- x-cut branch.
    rw [if_pos hcut]
    -- Expose `area`, `width`, `height` for the new LRP.
    simp only [Rect.area, Rect.width, Rect.height]
    -- Unfold `maxSide` on the right-hand side.
    -- After simp, the goal is about
    --   (S.LRP.x1 - (S.LRP.x0 + 1/((S.t+1:ℕ):ℕ))) * (S.LRP.y1 - S.LRP.y0)
    --     * ((S.t : ℚ) + 1)
    --   ≥ (S.LRP.x1 - S.LRP.x0) * (S.LRP.y1 - S.LRP.y0) * (S.t : ℚ)
    --     - S.LRP.maxSide * (1 + 1 / ((S.t : ℕ) : ℚ)).
    -- Match the goal form precisely. Both `↑(S.t+1)` instances stay as
    -- `((S.t + 1 : ℕ) : ℚ)` (unpushed) and `↑S.t` stays as `((S.t : ℕ) : ℚ)`.
    show (S.LRP.x1 - (S.LRP.x0 + 1 / ((S.t + 1 : ℕ) : ℚ))) *
          (S.LRP.y1 - S.LRP.y0) * ((S.t + 1 : ℕ) : ℚ) ≥
         (S.LRP.x1 - S.LRP.x0) * (S.LRP.y1 - S.LRP.y0) * ((S.t : ℕ) : ℚ) -
          S.LRP.maxSide * (1 + 1 / ((S.t : ℕ) : ℚ))
    -- Rewrite using W, H, t.
    rw [show S.LRP.x1 - (S.LRP.x0 + 1 / ((S.t + 1 : ℕ) : ℚ))
            = W - 1 / (t + 1) by
          rw [show (((S.t + 1 : ℕ)) : ℚ) = t + 1 from hcast_tp1]
          simp [hW_def]; ring,
        show ((S.t + 1 : ℕ) : ℚ) = t + 1 from hcast_tp1,
        show ((S.t : ℕ) : ℚ) = t from hcast_t]
    -- Goal:
    --   (W - 1/(t+1)) * H * (t+1) ≥ W * H * t - maxSide * (1 + 1/t).
    -- Expand: LHS = W*H*(t+1) - H = W*H*t + W*H - H.
    --         RHS = W*H*t - maxSide*(1+1/t).
    --   LHS - RHS = W*H + maxSide*(1+1/t) - H.
    -- This is ≥ 0 since maxSide ≥ H, hence maxSide*(1+1/t) ≥ H (as 1+1/t ≥ 1),
    -- and W*H ≥ 0.
    have hW1tp1 : (1 : ℚ) / (t + 1) * (t + 1) = 1 := by field_simp
    -- maxSide * (1 + 1/t) ≥ H.
    have h_ms_ge_H : H ≤ S.LRP.maxSide * (1 + 1 / t) := by
      have h1 : S.LRP.maxSide ≤ S.LRP.maxSide * (1 + 1 / t) := by
        have h_one_le : (1 : ℚ) ≤ 1 + 1 / t := by linarith
        have := mul_le_mul_of_nonneg_left h_one_le hMax_nn
        simpa using this
      linarith [hMax_ge_H]
    have key1 : 0 ≤ W * H := mul_nonneg hW_nn hH_nn
    -- Use nlinarith with helper facts.
    nlinarith [key1, hH_nn, hW_nn, ht_pos, htp1_pos, hu_nn, hu_def,
               hW1tp1, hMax_nn, h_ms_ge_H, hMax_ge_W, hMax_ge_H]
  · -- y-cut branch.
    rw [if_neg hcut]
    -- Expose `area`, `width`, `height`.
    simp only [Rect.area, Rect.width, Rect.height]
    -- After simp, the goal is about
    --   (S.LRP.x1 - S.LRP.x0) * (S.LRP.y1 - (S.LRP.y0 + 1/((S.t:ℕ):ℕ)))
    --     * ((S.t : ℚ) + 1)
    --   ≥ (S.LRP.x1 - S.LRP.x0) * (S.LRP.y1 - S.LRP.y0) * (S.t : ℚ)
    --     - S.LRP.maxSide * (1 + 1 / ((S.t : ℕ) : ℚ)).
    show (S.LRP.x1 - S.LRP.x0) *
          (S.LRP.y1 - (S.LRP.y0 + 1 / ((S.t : ℕ) : ℚ))) *
          ((S.t + 1 : ℕ) : ℚ) ≥
         (S.LRP.x1 - S.LRP.x0) * (S.LRP.y1 - S.LRP.y0) * ((S.t : ℕ) : ℚ) -
          S.LRP.maxSide * (1 + 1 / ((S.t : ℕ) : ℚ))
    -- Rewrite using W, H, t.
    rw [show S.LRP.y1 - (S.LRP.y0 + 1 / ((S.t : ℕ) : ℚ)) = H - 1 / t by
          rw [show (((S.t : ℕ)) : ℚ) = t from hcast_t]
          simp [hH_def]; ring,
        show S.LRP.x1 - S.LRP.x0 = W from rfl,
        show ((S.t + 1 : ℕ) : ℚ) = t + 1 from hcast_tp1,
        show ((S.t : ℕ) : ℚ) = t from hcast_t]
    -- Goal:
    --   W * (H - 1/t) * (t+1) ≥ W * H * t - maxSide * (1 + 1/t).
    -- Expand: LHS = W*H*(t+1) - W*(t+1)/t = W*H*t + W*H - W*(1 + 1/t).
    --         RHS = W*H*t - maxSide*(1+1/t).
    -- LHS - RHS = W*H + (maxSide - W)*(1+1/t) ≥ 0.
    have h_one_plus_inv_pos : (0 : ℚ) < 1 + 1 / t := by
      have : (0 : ℚ) ≤ 1 / t := hu_nn
      linarith
    have h_diff_nn : 0 ≤ S.LRP.maxSide - W := by linarith [hMax_ge_W]
    have h_prod_nn : 0 ≤ (S.LRP.maxSide - W) * (1 + 1 / t) :=
      mul_nonneg h_diff_nn (le_of_lt h_one_plus_inv_pos)
    have key1 : 0 ≤ W * H := mul_nonneg hW_nn hH_nn
    nlinarith [key1, hH_nn, hW_nn, ht_pos, htp1_pos, hu_nn, hu_def,
               hMax_nn, hMax_ge_W, hMax_ge_H, h_diff_nn, h_prod_nn,
               h_one_plus_inv_pos]

end MeirMoser
