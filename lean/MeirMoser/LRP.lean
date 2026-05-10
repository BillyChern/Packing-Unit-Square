/-
  Balanced LRP aspect-control lemma:

    Let X ≥ Y > 0 with X·Y ≥ c/t  and  X/Y ≤ R.
    Cut a stripe of thickness s ≤ α/t from the longer side.
    If t ≥ α² R / (c · (1 - 1/R)²), then the new aspect ratio is still ≤ R.

  Stated over ℝ. Proof: from the area+aspect bounds, Y² ≥ c/(R·t). Combined with
  s² ≤ α²/t² and the hypothesis on t, we get s² ≤ ((1-1/R)·Y)², hence s ≤ (1-1/R)·Y
  (both sides nonneg). Then s ≤ (1-1/R)·X (Y ≤ X), and finally Y/R ≤ X − s.
-/
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace MeirMoser.LRP

/-- From XY ≥ c/t and X ≤ R·Y we get Y² ≥ c/(R·t). -/
theorem Y_squared_lower_bound
    {X Y c t R : ℝ}
    (hY : 0 < Y) (hAspect : X ≤ R * Y)
    (hArea : c / t ≤ X * Y)
    (hRpos : 0 < R) (ht : 0 < t)
    : c / (R * t) ≤ Y * Y := by
  have h1 : X * Y ≤ R * Y * Y := by
    have := mul_le_mul_of_nonneg_right hAspect (le_of_lt hY)
    linarith
  have h2 : c / t ≤ R * Y * Y := le_trans hArea h1
  have h3 : c / t / R ≤ Y * Y := by
    rw [div_le_iff₀ hRpos]; linarith
  have heq : c / (R * t) = c / t / R := by
    rw [div_div]; ring_nf
  rw [heq]; exact h3

/-- Balanced LRP aspect control. -/
theorem balanced_lrp_aspect_control
    {X Y c t R α s : ℝ}
    (hY : 0 < Y) (hYX : Y ≤ X)
    (hArea : c / t ≤ X * Y)
    (hc : 0 < c) (ht : 0 < t)
    (hR : 1 < R)
    (hAspect : X ≤ R * Y)
    (hα : 0 < α) (hs : 0 ≤ s) (hsBound : s ≤ α / t)
    (hT : α^2 * R / (c * (1 - 1/R)^2) ≤ t)
    : 0 < X - s ∧ Y ≤ R * (X - s) := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hX_pos : 0 < X := lt_of_lt_of_le hY hYX
  have h_one_minus : 0 < 1 - 1/R := by
    have h_recip : 1/R < 1 := by
      rw [div_lt_iff₀ hRpos]; linarith
    linarith
  have hY2 : c / (R * t) ≤ Y * Y :=
    Y_squared_lower_bound hY hAspect hArea hRpos ht
  have h_denom_pos : 0 < c * (1 - 1/R)^2 := by positivity
  have hT' : α^2 * R ≤ c * (1 - 1/R)^2 * t := by
    have := (div_le_iff₀ h_denom_pos).mp hT
    linarith
  have hRt_pos : 0 < R * t := mul_pos hRpos ht
  -- Step A: s² ≤ α²/t²
  have ht_pos : 0 < t := ht
  have hsBound_nn : 0 ≤ α / t := le_trans hs hsBound
  have hs2_bound : s^2 ≤ α^2 / t^2 := by
    have h_sq_mono : s^2 ≤ (α/t)^2 := by
      have : s ≤ α/t := hsBound
      nlinarith [sq_nonneg s, sq_nonneg (α/t)]
    have eq_sq : (α/t)^2 = α^2 / t^2 := by
      rw [div_pow]
    linarith
  -- Step B: α²/t² ≤ (1-1/R)² · Y²
  have h_target : α^2 / t^2 ≤ (1 - 1/R)^2 * (Y * Y) := by
    have ht2 : (0 : ℝ) < t^2 := by positivity
    -- Step B.1: α²·R·t ≤ c·(1-1/R)²·t²  (multiply hT' by t)
    have step1 : α^2 * R * t ≤ c * (1 - 1/R)^2 * t * t := by
      exact mul_le_mul_of_nonneg_right hT' (le_of_lt ht_pos)
    -- Step B.2: divide both sides by R·t² (positive)
    have hRt2 : (0 : ℝ) < R * t^2 := by positivity
    have h_div : α^2 / t^2 ≤ (1 - 1/R)^2 * c / (R * t) := by
      rw [div_le_div_iff₀ ht2 hRt_pos]
      have lhs_eq : α^2 * (R * t) = α^2 * R * t := by ring
      have rhs_eq : (1 - 1/R)^2 * c * t^2 = c * (1 - 1/R)^2 * t * t := by ring
      rw [lhs_eq, rhs_eq]
      exact step1
    -- Step B.3: (1-1/R)²·c/(R·t) ≤ (1-1/R)²·(Y·Y)  via hY2
    have step3 : (1 - 1/R)^2 * c / (R * t) ≤ (1 - 1/R)^2 * (Y * Y) := by
      have eq1 : (1 - 1/R)^2 * c / (R * t) = (1 - 1/R)^2 * (c / (R * t)) := by
        field_simp
      rw [eq1]
      exact mul_le_mul_of_nonneg_left hY2 (sq_nonneg _)
    linarith
  -- Step C: s ≤ (1-1/R)·Y from squared comparison + nonnegativity.
  have h_1mR_Y_nn : 0 ≤ (1 - 1/R) * Y :=
    mul_nonneg (le_of_lt h_one_minus) (le_of_lt hY)
  have hs_le_1mY : s ≤ (1 - 1/R) * Y := by
    have h_sq : s^2 ≤ ((1 - 1/R) * Y)^2 := by
      have rewrite : ((1 - 1/R) * Y)^2 = (1 - 1/R)^2 * (Y * Y) := by ring
      rw [rewrite]; linarith
    -- a² ≤ b², a ≥ 0, b ≥ 0 ⇒ a ≤ b.
    -- (b - a)(b + a) = b² - a² ≥ 0. With b + a ≥ 0 and Y > 0 ⇒ (1-1/R)·Y + s > 0.
    have hY_pos_strict : 0 < (1 - 1/R) * Y :=
      mul_pos h_one_minus hY
    have hsum_pos : 0 < (1 - 1/R) * Y + s := by linarith
    have hdiff_prod : 0 ≤ ((1 - 1/R) * Y - s) * ((1 - 1/R) * Y + s) := by
      have eq : ((1 - 1/R) * Y - s) * ((1 - 1/R) * Y + s) = ((1 - 1/R) * Y)^2 - s^2 := by
        ring
      rw [eq]; linarith
    -- product is nonneg, second factor positive ⇒ first factor nonneg.
    have hdiff : 0 ≤ (1 - 1/R) * Y - s := by
      by_contra h_neg
      push_neg at h_neg
      have : ((1 - 1/R) * Y - s) * ((1 - 1/R) * Y + s) < 0 :=
        mul_neg_of_neg_of_pos h_neg hsum_pos
      linarith
    linarith
  -- Step D: combine to finish.
  have hsX : s ≤ (1 - 1/R) * X := by
    have h_mul : (1 - 1/R) * Y ≤ (1 - 1/R) * X :=
      mul_le_mul_of_nonneg_left hYX (le_of_lt h_one_minus)
    linarith
  have h_1mR_lt_one : (1 - 1/R) < 1 := by
    have : 0 < 1/R := by positivity
    linarith
  have hs_lt_X : s < X := by
    have h_step : (1 - 1/R) * X < 1 * X :=
      mul_lt_mul_of_pos_right h_1mR_lt_one hX_pos
    linarith
  refine ⟨by linarith, ?_⟩
  -- Goal: Y ≤ R·(X-s).
  -- s ≤ (1-1/R)·X = X - X/R, so X/R ≤ X - s. Y ≤ X gives Y/R ≤ X/R ≤ X - s.
  have h_eq : (1 - 1/R) * X = X - X / R := by field_simp; ring
  rw [h_eq] at hsX
  have h_X_R_le : X / R ≤ X - s := by linarith
  have h_Y_R_le_X_R : Y / R ≤ X / R := by
    have : Y / R ≤ X / R ↔ Y ≤ X := by
      rw [div_le_div_iff₀ hRpos hRpos]; constructor <;> intro h <;> nlinarith
    exact this.mpr hYX
  have h_Y_R_le : Y / R ≤ X - s := le_trans h_Y_R_le_X_R h_X_R_le
  rw [div_le_iff₀ hRpos] at h_Y_R_le
  linarith

end MeirMoser.LRP
