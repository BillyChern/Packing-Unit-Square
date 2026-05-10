/-
  CalibratedStripeCombine.lean (R-A.5 Task A5.6): combines the four per-step
  preservation lemmas for `calibratedBalancedStep` into
  `step_preserves_GoodTailState_calibrated`.

  Mirrors `SchedulerInductionBalancedCombine.lean`, adapted for the
  calibrated balanced step which uses `calibratedStripeWidthRat γ_num γ_den t`
  in place of `1/(t+1)` for the x-cut width, so the area-share bound carries
  the additional factor `a_t · LRP.maxSide · (t+1)` rather than
  `LRP.maxSide · (1 + 1/t)`.
-/
import MeirMoser.CalibratedStripeArea
import MeirMoser.CalibratedStripeAspect
import MeirMoser.CalibratedStripeAux
import MeirMoser.WarmStart

namespace MeirMoser

/-- One calibrated balanced step preserves a (relaxed) GoodTailState.

    Output parameters: the new `c'` is shifted from `c` by exactly the
    calibrated area-share decrement
    `a_t · LRP.maxSide · (t+1)`, where `a_t = calibratedStripeWidthRat γ_num γ_den t`.
    `R` and `η` are unchanged. The new `widthChecks` list extends the old
    one by exactly one entry, namely `newWidthCheckCalibrated γ_num γ_den S`. -/
theorem step_preserves_GoodTailState_calibrated
    (γ_num γ_den : ℕ) (S : TailState) (widthChecks : List NormalWidthCheck)
    (c R η : ℚ) (h_R : 1 ≤ R)
    (h_state : GoodTailState c R η S widthChecks)
    (h_fit :
      calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
      (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0)
    (h_t_pos : 0 < S.t)
    (h_room : S.LRP.maxSide - calibratedStripeWidthRat γ_num γ_den S.t ≥
              S.LRP.minSide / R)
    (h_FP : FinitePacking
              (calibratedBalancedStep γ_num γ_den S).container
              (calibratedBalancedStep γ_num γ_den S).placed)
    : ∃ c', GoodTailState c' R η (calibratedBalancedStep γ_num γ_den S)
              (widthChecks ++ [newWidthCheckCalibrated γ_num γ_den S]) := by
  rcases h_state with ⟨h_LRP_area, h_LRP_aspect, h_P_ep, h_widths, _h_finite⟩
  -- New `c'` from the calibrated area-share bound.
  refine ⟨c - calibratedStripeWidthRat γ_num γ_den S.t * S.LRP.maxSide *
            (((S.t + 1 : ℕ) : ℚ)), ?_, ?_, ?_, ?_, ?_⟩
  · -- (i) c' ≤ (calibratedBalancedStep ..).LRP.area · (calibratedBalancedStep ..).t.
    have h_area_bound :=
      calibratedBalancedStep_LRP_area_lower γ_num γ_den S h_fit h_t_pos
    -- We have: (cBS S).LRP.area * (cBS S).t ≥ S.LRP.area · S.t − a_t · maxSide · (t+1).
    -- And c ≤ S.LRP.area · S.t.
    -- So c − a_t · maxSide · (t+1) ≤ (cBS S).LRP.area · (cBS S).t.
    linarith
  · -- (ii) (calibratedBalancedStep ..).LRP.maxSide ≤ R · (calibratedBalancedStep ..).LRP.minSide.
    exact calibratedBalancedStep_LRP_aspect_preserved γ_num γ_den S R h_R
            h_LRP_aspect h_fit h_t_pos h_room
  · -- (iii) Σ semiperim ((calibratedBalancedStep ..).endpointBoxes) ≤ η.
    rw [calibratedBalancedStep_preserves_endpoint_perim]
    exact h_P_ep
  · -- (iv) all width-checks (extended list) hold.
    exact calibratedBalancedStep_widthChecks_extend γ_num γ_den S widthChecks h_widths
  · -- (v) FinitePacking on the new container/placed prefix.
    exact h_FP

end MeirMoser
