/-
  CalibratedStripeAspect.lean (Route A.5 Task A5.3): per-step LRP aspect
  preservation for the genuinely CALIBRATED balanced step.

  This is the calibrated analog of `balancedStep_LRP_aspect_preserved`. The
  calibrated step always cuts the LONGER side of the LRP by exactly
  `a_t = calibratedStripeWidthRat γ_num γ_den t` (in BOTH branches, x-cut and
  y-cut). Unlike the simplified balanced step, here there is no asymmetry
  between the two cuts: both are of magnitude `a_t`.

  We prove that under a "room" hypothesis on `a_t`, the calibrated balanced
  step preserves the LRP aspect bound `maxSide ≤ R · minSide`.

  Approach (per orientation):
    Let M = old.maxSide (longer side), m = old.minSide (shorter side).
    The cut is `a_t` on the longer side. After the cut:
      Case A:  M − a_t ≥ m.   Then maxSide' = M − a_t ≤ M ≤ R · m.
      Case B:  M − a_t < m.   Then maxSide' = m, minSide' = M − a_t.
                From `h_room`: M − a_t ≥ m / R, so m ≤ R · (M − a_t).
-/
import MeirMoser.CalibratedStripe
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace MeirMoser

/-- (Route A.5 Task A5.3) Per-step LRP aspect preservation for the calibrated
    balanced step.

    The "room" hypothesis says the longer-side cut `a_t` leaves enough on the
    longer side: what remains is at least `minSide / R`. The conclusion is
    that the new LRP still satisfies `maxSide ≤ R · minSide`. -/
theorem calibratedBalancedStep_LRP_aspect_preserved
    (γ_num γ_den : ℕ) (S : TailState) (R : ℚ) (h_R : 1 ≤ R)
    (h_aspect : S.LRP.maxSide ≤ R * S.LRP.minSide)
    (h_fit : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
             (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0)
    (h_t_pos : 0 < S.t)
    (h_room : S.LRP.maxSide - calibratedStripeWidthRat γ_num γ_den S.t ≥
              S.LRP.minSide / R)
    : (calibratedBalancedStep γ_num γ_den S).LRP.maxSide ≤
        R * (calibratedBalancedStep γ_num γ_den S).LRP.minSide := by
  -- Unfold to the success branch of `calibratedBalancedStep`.
  unfold calibratedBalancedStep
  rw [dif_pos h_fit]
  -- Abbreviations.
  set W : ℚ := S.LRP.x1 - S.LRP.x0 with hW_def
  set H : ℚ := S.LRP.y1 - S.LRP.y0 with hH_def
  set a_t : ℚ := calibratedStripeWidthRat γ_num γ_den S.t with ha_t_def
  -- Positivity facts.
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one h_R
  have ha_t_nn : 0 ≤ a_t := by
    unfold_let a_t; exact calibratedStripeWidthRat_nonneg γ_num γ_den S.t
  have hW_pos : (0 : ℚ) ≤ W := by
    have := h_fit.1
    have : a_t ≤ W := this
    linarith
  have hH_pos : (0 : ℚ) ≤ H := by
    have h_h_d_nn : (0 : ℚ) ≤ (1 : ℚ) / (S.t : ℕ) := by positivity
    have := h_fit.2
    linarith
  -- Old aspect facts in terms of W, H.
  have h_old_aspect : max W H ≤ R * min W H := by
    have := h_aspect
    show max W H ≤ R * min W H
    convert this using 2 <;> rfl
  -- Rewrite h_room in terms of W, H, a_t.
  have h_room' : max W H - a_t ≥ min W H / R := by
    have := h_room
    show max W H - a_t ≥ min W H / R
    convert this using 2 <;> rfl
  -- Case split on cutFromX S.
  by_cases hcut_branch : cutFromX S = true
  · -- x-cut branch: new LRP has width W − a_t, height H.
    rw [dif_pos hcut_branch]
    -- cutFromX = decide (H ≤ W), so we know H ≤ W.
    have hHW : H ≤ W := by
      unfold cutFromX at hcut_branch
      simpa [hW_def, hH_def] using
        (decide_eq_true_iff (p := S.LRP.y1 - S.LRP.y0 ≤ S.LRP.x1 - S.LRP.x0)).mp
          hcut_branch
    -- Old max = W, old min = H.
    have h_max_W : max W H = W := max_eq_left hHW
    have h_min_H : min W H = H := min_eq_right hHW
    have h_old_aspect_W : W ≤ R * H := by
      have := h_old_aspect; rw [h_max_W, h_min_H] at this; exact this
    have h_room_W : W - a_t ≥ H / R := by
      have := h_room'; rw [h_max_W, h_min_H] at this; exact this
    -- Goal: max ((x1) − (x0+a_t)) (y1 − y0) ≤ R * min ...
    show max (S.LRP.x1 - (S.LRP.x0 + a_t)) (S.LRP.y1 - S.LRP.y0)
         ≤ R * min (S.LRP.x1 - (S.LRP.x0 + a_t)) (S.LRP.y1 - S.LRP.y0)
    have h_eq_w : S.LRP.x1 - (S.LRP.x0 + a_t) = W - a_t := by
      show S.LRP.x1 - (S.LRP.x0 + a_t) = (S.LRP.x1 - S.LRP.x0) - a_t
      ring
    have h_eq_h : S.LRP.y1 - S.LRP.y0 = H := rfl
    rw [h_eq_w, h_eq_h]
    show max (W - a_t) H ≤ R * min (W - a_t) H
    -- Sub-case: is W − a_t ≥ H or W − a_t < H?
    rcases le_or_lt H (W - a_t) with hcase | hcase
    · -- W − a_t ≥ H: new max = W − a_t, new min = H.
      have h_max : max (W - a_t) H = W - a_t := max_eq_left hcase
      have h_min : min (W - a_t) H = H := min_eq_right hcase
      rw [h_max, h_min]
      -- Need W − a_t ≤ R · H. From W ≤ R · H and a_t ≥ 0.
      linarith
    · -- W − a_t < H: new max = H, new min = W − a_t.
      have hcase' : W - a_t ≤ H := le_of_lt hcase
      have h_max : max (W - a_t) H = H := max_eq_right hcase'
      have h_min : min (W - a_t) H = W - a_t := min_eq_left hcase'
      rw [h_max, h_min]
      -- Need H ≤ R · (W − a_t). From h_room_W: W − a_t ≥ H/R.
      have h1 : H / R * R ≤ (W - a_t) * R :=
        mul_le_mul_of_nonneg_right h_room_W hR_pos.le
      have h2 : H / R * R = H := by
        rw [div_mul_cancel₀]; exact ne_of_gt hR_pos
      rw [h2] at h1
      linarith
  · -- y-cut branch: new LRP has width W, height H − a_t.
    rw [dif_neg hcut_branch]
    -- Not (cutFromX S = true), so cutFromX S = false, hence H > W (strictly).
    have hWH : W < H := by
      have hcut_eq : cutFromX S = false := by
        cases hcase : cutFromX S
        · rfl
        · exact absurd hcase hcut_branch
      unfold cutFromX at hcut_eq
      have h_dec :
          ¬ (S.LRP.y1 - S.LRP.y0 ≤ S.LRP.x1 - S.LRP.x0) := by
        intro hle
        have : decide (S.LRP.y1 - S.LRP.y0 ≤ S.LRP.x1 - S.LRP.x0) = true :=
          decide_eq_true hle
        rw [this] at hcut_eq
        exact Bool.noConfusion hcut_eq
      have : S.LRP.x1 - S.LRP.x0 < S.LRP.y1 - S.LRP.y0 := lt_of_not_ge h_dec
      simpa [hW_def, hH_def] using this
    have hWH_le : W ≤ H := le_of_lt hWH
    -- Old max = H, old min = W.
    have h_max_H : max W H = H := max_eq_right hWH_le
    have h_min_W : min W H = W := min_eq_left hWH_le
    have h_old_aspect_H : H ≤ R * W := by
      have := h_old_aspect; rw [h_max_H, h_min_W] at this; exact this
    have h_room_H : H - a_t ≥ W / R := by
      have := h_room'; rw [h_max_H, h_min_W] at this; exact this
    -- Goal: max (x1 − x0) ((y1) − (y0+a_t)) ≤ R * min ...
    show max (S.LRP.x1 - S.LRP.x0) (S.LRP.y1 - (S.LRP.y0 + a_t))
         ≤ R * min (S.LRP.x1 - S.LRP.x0) (S.LRP.y1 - (S.LRP.y0 + a_t))
    have h_eq_w : S.LRP.x1 - S.LRP.x0 = W := rfl
    have h_eq_h : S.LRP.y1 - (S.LRP.y0 + a_t) = H - a_t := by
      show S.LRP.y1 - (S.LRP.y0 + a_t) = (S.LRP.y1 - S.LRP.y0) - a_t
      ring
    rw [h_eq_w, h_eq_h]
    show max W (H - a_t) ≤ R * min W (H - a_t)
    -- Sub-case: is H − a_t ≥ W or H − a_t < W?
    rcases le_or_lt W (H - a_t) with hcase | hcase
    · -- H − a_t ≥ W: new max = H − a_t, new min = W.
      have h_max : max W (H - a_t) = H - a_t := max_eq_right hcase
      have h_min : min W (H - a_t) = W := min_eq_left hcase
      rw [h_max, h_min]
      -- Need H − a_t ≤ R · W. From H ≤ R · W and a_t ≥ 0.
      linarith
    · -- H − a_t < W: new max = W, new min = H − a_t.
      have hcase' : H - a_t ≤ W := le_of_lt hcase
      have h_max : max W (H - a_t) = W := max_eq_left hcase'
      have h_min : min W (H - a_t) = H - a_t := min_eq_right hcase'
      rw [h_max, h_min]
      -- Need W ≤ R · (H − a_t). From h_room_H: H − a_t ≥ W/R.
      have h1 : W / R * R ≤ (H - a_t) * R :=
        mul_le_mul_of_nonneg_right h_room_H hR_pos.le
      have h2 : W / R * R = W := by
        rw [div_mul_cancel₀]; exact ne_of_gt hR_pos
      rw [h2] at h1
      linarith

end MeirMoser
