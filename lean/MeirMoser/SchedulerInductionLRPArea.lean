/-
  SchedulerInductionLRPArea.lean

  Per-step LRP area-share preservation lemma (A.3.b) for the simplified
  calibrated step.

  When `calibratedStep` succeeds:
    - the LRP loses a stripe of width `1/t` from its left side,
    - so `new_LRP.area = old_LRP.area - (1/t) * old_LRP.height`,
    - `new_t = old_t + 1`.
  Hence
    new_LRP.area * (t+1)
      = (old_LRP.area - height/t) * (t+1)
      = old_LRP.area * (t+1) - height * (t+1)/t.
  And
    new_LRP.area * (t+1) - old_LRP.area * t
      = old_LRP.area - height * (t+1)/t.
  Since `old_LRP.area ≥ 0`, we obtain the lower bound
    new_LRP.area * (t+1) ≥ old_LRP.area * t - height * (1 + 1/t).
-/
import MeirMoser.SchedulerInduction
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace MeirMoser

/-- (A.3.b) Per-step LRP area-share preservation.

    On the success branch, the new `(LRP.area · t)` decreases by at most
    `LRP.height · (1 + 1/t)` compared to the old `(LRP.area · t)`. -/
theorem calibratedStep_LRP_area_lower
    (S : TailState)
    (h_step_succeeds :
      (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
      (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0)
    (h_t_pos : 0 < S.t)
    : (calibratedStep S).LRP.area * ((calibratedStep S).t : ℚ) ≥
        S.LRP.area * (S.t : ℚ) -
        S.LRP.height * (1 + 1 / (S.t : ℕ)) := by
  -- Unfold the success branch.
  unfold calibratedStep
  rw [dif_pos h_step_succeeds]
  -- Abbreviations.
  set t : ℚ := (S.t : ℚ) with ht_def
  -- After `dif_pos`, the goal is concrete in terms of S.LRP fields.
  -- Expose `area = width * height` and `height = y1 - y0`.
  simp only [Rect.area, Rect.width, Rect.height, Nat.cast_add, Nat.cast_one]
  -- New LRP width = (x1 - (x0 + 1/t)) = (x1 - x0) - 1/t.
  -- New LRP height = (y1 - y0) (unchanged).
  -- New t = S.t + 1.
  -- Old area = (x1 - x0) * (y1 - y0); old height = (y1 - y0).
  -- We want:
  --   ((x1 - x0 - 1/t_nat) * (y1 - y0)) * (t + 1)
  --    ≥ ((x1 - x0) * (y1 - y0)) * t - (y1 - y0) * (1 + 1/t_nat).
  -- Note: in the goal, the `1 / S.t` literally appears as `1 / (S.t : ℕ)`,
  -- which is `(S.t : ℚ)⁻¹` after coercion.
  -- Strategy: introduce h := y1 - y0, w := x1 - x0, positivity facts;
  --   rearrange the inequality to `(t + 1) * (...)  ≥ 0`-style form;
  --   conclude from non-negativity of `h`, `w - 1/t_nat`, and `t > 0`.
  -- Set up the algebraic substitutions.
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
  -- The LHS factor `W - 1/t` is ≥ 0 (from hcanFit.1).
  have hWmin : (1 : ℚ) / (S.t : ℕ) ≤ W := by
    have := h_step_succeeds.1
    simpa [hW_def] using this
  -- Rewrite Nat.cast (S.t : ℕ) to t.
  have hcast_t : ((S.t : ℕ) : ℚ) = t := by simp [ht_def]
  -- Now prove the goal directly via algebra.
  -- The unfolded goal currently has `((S.t : ℕ) : ℚ)` and `((S.t + 1 : ℕ) : ℕ : ℚ)`.
  -- After `simp` above, casts have been pushed; restore the W,H names.
  -- Rather than fighting with simp, just do `show` to a clean form and
  -- finish with `nlinarith` on the key facts.
  show (S.LRP.x1 - (S.LRP.x0 + 1 / ((S.t : ℕ) : ℚ))) *
        (S.LRP.y1 - S.LRP.y0) * ((S.t : ℚ) + 1) ≥
       (S.LRP.x1 - S.LRP.x0) * (S.LRP.y1 - S.LRP.y0) * (S.t : ℚ) -
        (S.LRP.y1 - S.LRP.y0) * (1 + 1 / ((S.t : ℕ) : ℚ))
  -- Rewrite using W, H, t.
  rw [show S.LRP.x1 - (S.LRP.x0 + 1 / ((S.t : ℕ) : ℚ)) = W - 1 / t by
        simp [hW_def, hcast_t]; ring,
      show S.LRP.y1 - S.LRP.y0 = H from rfl,
      show S.LRP.x1 - S.LRP.x0 = W from rfl]
  rw [hcast_t]
  -- Reduce to: (W - 1/t) * H * (t+1) ≥ W * H * t - H * (1 + 1/t).
  -- Multiply through by t > 0 to clear denominators:
  --   (W*t - 1) * H * (t+1) ≥ W * H * t^2 - H * (t + 1).
  -- LHS = W*H*t*(t+1) - H*(t+1).
  -- LHS - RHS = W*H*t*(t+1) - H*(t+1) - W*H*t^2 + H*(t+1)
  --           = W*H*t*(t+1) - W*H*t^2
  --           = W*H*t.
  -- So the inequality becomes `W*H*t ≥ 0` after multiplying by t > 0.
  -- We use `nlinarith` with the right hint terms.
  have hWmin' : 1 / t ≤ W := by rw [← hcast_t]; exact hWmin
  -- Provide nlinarith with enough algebraic facts.
  have key1 : 0 ≤ W * H := mul_nonneg hW_nn hH_nn
  have key2 : 0 ≤ W * H * t := mul_nonneg key1 (le_of_lt ht_pos)
  have ht_inv : (1 : ℚ) / t * t = 1 := by field_simp
  -- Replace 1/t by a name to help nlinarith.
  set u : ℚ := 1 / t with hu_def
  have hu_nn : 0 ≤ u := by
    rw [hu_def]; exact one_div_nonneg.mpr (le_of_lt ht_pos)
  have hu_t : u * t = 1 := by rw [hu_def]; field_simp
  -- Goal after substitution: (W - u) * H * (t + 1) ≥ W * H * t - H * (1 + u).
  -- Expand:
  --   LHS = W*H*t + W*H - u*H*t - u*H
  --       = W*H*t + W*H - H - u*H        (since u*t = 1)
  --   RHS = W*H*t - H - u*H.
  --   LHS - RHS = W*H ≥ 0.
  nlinarith [key1, key2, hu_nn, hu_t, hH_nn, hW_nn, hWmin', ht_pos, mul_nonneg hH_nn hu_nn,
             mul_nonneg hW_nn (le_of_lt ht_pos)]

end MeirMoser
