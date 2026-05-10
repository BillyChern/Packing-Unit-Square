/-
  CalibratedStripeRpowBound.lean (Route A.5 Task 7).

  Bridge between the rational lower bound `calibratedExtraSlackRat γ_num γ_den t
  = 1/(t·t)` (for t ≥ 1) and the Real-valued power `t^{-γ}` where
  `γ = γ_num/γ_den`. For γ ∈ (1, 3/2) ⊂ [0, 2] and t ≥ 1 we have:

      1/(t·t) = t^{-2} ≤ t^{-γ}

  since `(t : ℝ) ≥ 1` and `-2 ≤ -γ` (because `γ ≤ 2` follows from
  `γ_num ≤ 2 · γ_den`).

  Key Mathlib lemmas used:
    * `Real.rpow_neg`                       :  x ^ (-y) = (x ^ y)⁻¹  (for 0 ≤ x)
    * `Real.rpow_two`                       :  x ^ (2 : ℝ) = x ^ 2
    * `Real.rpow_le_rpow_of_exponent_le`    :  1 ≤ x ∧ y ≤ z → x ^ y ≤ x ^ z
-/
import MeirMoser.CalibratedStripe
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace MeirMoser

/-- For γ ≤ 2 and t ≥ 1: `1/(t·t) ≤ t^{-γ}` as Reals.
    Equivalently: `t^{-2} ≤ t^{-γ}` for t ≥ 1, since -2 ≤ -γ when γ ≤ 2,
    and `x ↦ t^x` is monotone increasing for t ≥ 1. -/
theorem calibratedExtraSlackRat_le_rpow
    (γ_num γ_den : ℕ) (h_γ_pos : 0 < γ_den) (h_γ_lt_two : γ_num ≤ 2 * γ_den)
    (t : ℕ) (h_t : 0 < t) :
    ((calibratedExtraSlackRat γ_num γ_den t : ℚ) : ℝ) ≤
      (t : ℝ) ^ (-((γ_num : ℝ) / (γ_den : ℝ))) := by
  -- Reduce the LHS to `1 / ((t : ℝ) * (t : ℝ))`.
  have h_t_ne : t ≠ 0 := Nat.pos_iff_ne_zero.mp h_t
  have h_t_R_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast h_t
  have h_t_R_ne : (t : ℝ) ≠ 0 := ne_of_gt h_t_R_pos
  have h_one_le_t_R : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast h_t
  have h_t_R_nonneg : (0 : ℝ) ≤ (t : ℝ) := le_of_lt h_t_R_pos
  -- LHS reduction.
  have h_lhs_eq :
      ((calibratedExtraSlackRat γ_num γ_den t : ℚ) : ℝ) =
        1 / ((t : ℝ) * (t : ℝ)) := by
    unfold calibratedExtraSlackRat
    rw [if_neg h_t_ne]
    push_cast
    ring
  -- Express `1 / (t * t)` as `(t : ℝ) ^ (-2 : ℝ)`.
  have h_pow_two : (t : ℝ) ^ (2 : ℝ) = (t : ℝ) * (t : ℝ) := by
    rw [Real.rpow_two]
    ring
  have h_pow_neg_two : (t : ℝ) ^ (-(2 : ℝ)) = 1 / ((t : ℝ) * (t : ℝ)) := by
    rw [Real.rpow_neg h_t_R_nonneg, h_pow_two, one_div]
  -- Show -2 ≤ -(γ_num/γ_den), i.e., γ_num/γ_den ≤ 2.
  have h_γ_den_R_pos : (0 : ℝ) < (γ_den : ℝ) := by exact_mod_cast h_γ_pos
  have h_ratio_le_two : (γ_num : ℝ) / (γ_den : ℝ) ≤ 2 := by
    rw [div_le_iff₀ h_γ_den_R_pos]
    have : (γ_num : ℝ) ≤ 2 * (γ_den : ℝ) := by exact_mod_cast h_γ_lt_two
    linarith
  have h_exp_le : -(2 : ℝ) ≤ -((γ_num : ℝ) / (γ_den : ℝ)) := by linarith
  -- Apply monotonicity: t^(-2) ≤ t^(-γ_num/γ_den).
  have h_mono :
      (t : ℝ) ^ (-(2 : ℝ)) ≤ (t : ℝ) ^ (-((γ_num : ℝ) / (γ_den : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le h_one_le_t_R h_exp_le
  calc
    ((calibratedExtraSlackRat γ_num γ_den t : ℚ) : ℝ)
        = 1 / ((t : ℝ) * (t : ℝ)) := h_lhs_eq
    _ = (t : ℝ) ^ (-(2 : ℝ)) := h_pow_neg_two.symm
    _ ≤ (t : ℝ) ^ (-((γ_num : ℝ) / (γ_den : ℝ))) := h_mono

/-- Total stripe width as Real bound: `a_t ≤ 1/(t+1) + t^{-γ}`. -/
theorem calibratedStripeWidthRat_le_rpow_sum
    (γ_num γ_den : ℕ) (h_γ_pos : 0 < γ_den) (h_γ_lt_two : γ_num ≤ 2 * γ_den)
    (t : ℕ) (h_t : 0 < t) :
    ((calibratedStripeWidthRat γ_num γ_den t : ℚ) : ℝ) ≤
      1 / ((t : ℝ) + 1) + (t : ℝ) ^ (-((γ_num : ℝ) / (γ_den : ℝ))) := by
  unfold calibratedStripeWidthRat
  -- The Rat-valued sum casts to a Real-valued sum.
  have h_cast :
      (((1 : ℚ) / ((t + 1 : ℕ) : ℕ) +
            calibratedExtraSlackRat γ_num γ_den t : ℚ) : ℝ) =
        (((1 : ℚ) / ((t + 1 : ℕ) : ℕ) : ℚ) : ℝ) +
          ((calibratedExtraSlackRat γ_num γ_den t : ℚ) : ℝ) := by
    push_cast
    ring
  rw [h_cast]
  -- The fraction `1/(t+1)` on the left side casts cleanly.
  have h_frac_eq :
      (((1 : ℚ) / ((t + 1 : ℕ) : ℕ) : ℚ) : ℝ) = 1 / ((t : ℝ) + 1) := by
    push_cast
    ring
  rw [h_frac_eq]
  -- Now apply the slack bound to the second summand.
  have h_slack :=
    calibratedExtraSlackRat_le_rpow γ_num γ_den h_γ_pos h_γ_lt_two t h_t
  linarith

end MeirMoser
