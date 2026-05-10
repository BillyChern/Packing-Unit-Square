/-
  SchedulerInductionLRPAspect.lean: per-step LRP aspect preservation (A.3.c).

  We prove that the simplified `calibratedStep` (defined in
  `SchedulerInduction.lean`) preserves the aspect bound of the LRP, given a
  "room" hypothesis on the cut. This is the calibrated framework's invariant
  (ii):  `LRP.maxSide ≤ R · LRP.minSide`.

  The simplified step cuts a stripe of width `1/t` from the LRP's left side, so
  the new LRP has the same `y`-extent and a width reduced by `1/t`.

  Approach:
    Let w' = old.width − 1/t  and  h' = old.height.
    Case A:  h' ≤ w'.    Then maxSide' = w', minSide' = h'.  Use w' ≤ old.width
              and old.maxSide = max ≥ old.width together with `h_aspect`.
    Case B:  w' < h'.    Then maxSide' = h', minSide' = w'.  Use the `h_room`
              hypothesis directly: `R · w' ≥ h'`.
-/
import MeirMoser.SchedulerInduction
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace MeirMoser

/-- (A.3.c) Per-step LRP aspect preservation under the simplified calibrated
    step.  The "room" hypothesis says the cut leaves enough width: after
    removing `1/t`, the new width is at least `height / R`.  The conclusion is
    that the new LRP still satisfies `maxSide ≤ R · minSide`. -/
theorem calibratedStep_LRP_aspect_preserved
    (S : TailState) (R : ℚ) (hR : 1 ≤ R)
    (h_aspect : S.LRP.maxSide ≤ R * S.LRP.minSide)
    (h_step_succeeds :
      (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
      (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0)
    (h_t_pos : 0 < S.t)
    (h_room : S.LRP.x1 - S.LRP.x0 - (1 : ℚ) / (S.t : ℕ)
              ≥ (S.LRP.y1 - S.LRP.y0) / R)
    : (calibratedStep S).LRP.maxSide ≤ R * (calibratedStep S).LRP.minSide := by
  -- Unfold to the success branch.
  unfold calibratedStep
  rw [dif_pos h_step_succeeds]
  -- Abbreviations.
  set w_old : ℚ := S.LRP.x1 - S.LRP.x0 with hw_old
  set h_old : ℚ := S.LRP.y1 - S.LRP.y0 with hh_old
  set s : ℚ := (1 : ℚ) / (S.t : ℕ) with hs
  set w_new : ℚ := w_old - s with hw_new
  -- Extract step success components.
  have hw_room_step : s ≤ w_old := h_step_succeeds.1
  have hh_pos : 0 ≤ h_old := by
    have h := h_step_succeeds.2
    have hpos : (0 : ℚ) ≤ 1 / ((S.t + 1 : ℕ) : ℕ) := by positivity
    linarith
  -- Step width nonneg.
  have hs_nonneg : 0 ≤ s := by unfold_let s; positivity
  have hw_new_nonneg : 0 ≤ w_new := by unfold_let w_new; linarith
  -- Show R is positive (since 1 ≤ R).
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  -- Compute the new LRP's width and height.
  -- New LRP: x0 := S.LRP.x0 + s, y0 := S.LRP.y0, x1 := S.LRP.x1, y1 := S.LRP.y1.
  -- So new.width = (S.LRP.x1) - (S.LRP.x0 + s) = w_old - s = w_new.
  -- And new.height = h_old.
  show max ((S.LRP.x1) - (S.LRP.x0 + s)) (S.LRP.y1 - S.LRP.y0)
       ≤ R * min ((S.LRP.x1) - (S.LRP.x0 + s)) (S.LRP.y1 - S.LRP.y0)
  -- Rewrite the new width as w_new.
  have h_eq_w : S.LRP.x1 - (S.LRP.x0 + s) = w_new := by
    unfold_let w_new w_old; ring
  rw [h_eq_w]
  -- The y-extent is literally h_old by definition.
  show max w_new h_old ≤ R * min w_new h_old
  -- Old aspect ⇒ old width and height bounded by R · min(width, height).
  -- From h_aspect: max(w_old, h_old) ≤ R · min(w_old, h_old).
  have h_old_aspect : max w_old h_old ≤ R * min w_old h_old := by
    have := h_aspect
    -- maxSide = max width height; width = x1-x0; height = y1-y0.
    show max w_old h_old ≤ R * min w_old h_old
    convert this using 2 <;> rfl
  have h_old_w_le : w_old ≤ R * min w_old h_old :=
    le_trans (le_max_left _ _) h_old_aspect
  have h_old_h_le : h_old ≤ R * min w_old h_old :=
    le_trans (le_max_right _ _) h_old_aspect
  have h_old_h_le_Rw : h_old ≤ R * w_old :=
    le_trans h_old_h_le (mul_le_mul_of_nonneg_left (min_le_left _ _) hR_pos.le)
  have h_old_w_le_Rh : w_old ≤ R * h_old :=
    le_trans h_old_w_le (mul_le_mul_of_nonneg_left (min_le_right _ _) hR_pos.le)
  -- The room hypothesis gives R · w_new ≥ h_old.
  -- h_room : w_old - s ≥ h_old / R, i.e. w_new ≥ h_old / R.
  have h_room' : w_new ≥ h_old / R := by
    unfold_let w_new w_old s
    -- Direct from hypothesis.
    have := h_room; unfold_let s at this; exact this
  have h_R_w_new : R * w_new ≥ h_old := by
    have h1 : h_old / R * R ≤ w_new * R := by
      exact (mul_le_mul_of_nonneg_right h_room' hR_pos.le)
    have h2 : h_old / R * R = h_old := by
      rw [div_mul_cancel₀]; exact ne_of_gt hR_pos
    rw [h2] at h1
    linarith [h1]
  -- Case split: is w_new ≥ h_old or w_new < h_old?
  rcases le_or_lt h_old w_new with hcase | hcase
  · -- Case A: h_old ≤ w_new. Max = w_new, Min = h_old.
    have h_max : max w_new h_old = w_new := max_eq_left hcase
    have h_min : min w_new h_old = h_old := min_eq_right hcase
    rw [h_max, h_min]
    -- Need: w_new ≤ R · h_old.
    -- Since w_new ≤ w_old and w_old ≤ R · h_old.
    have h_w_new_le_w_old : w_new ≤ w_old := by unfold_let w_new; linarith
    exact le_trans h_w_new_le_w_old h_old_w_le_Rh
  · -- Case B: w_new < h_old. Max = h_old, Min = w_new.
    have hcase' : w_new ≤ h_old := le_of_lt hcase
    have h_max : max w_new h_old = h_old := max_eq_right hcase'
    have h_min : min w_new h_old = w_new := min_eq_left hcase'
    rw [h_max, h_min]
    -- Need: h_old ≤ R · w_new.  Direct from h_R_w_new.
    exact h_R_w_new

end MeirMoser
