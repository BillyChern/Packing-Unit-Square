/-
  SchedulerInductionCombine.lean (A.3.f): combines the four per-step
  preservation lemmas into `step_preserves_GoodTailState`.
-/
import MeirMoser.SchedulerInduction
import MeirMoser.SchedulerInductionLRPArea
import MeirMoser.SchedulerInductionLRPAspect
import MeirMoser.SchedulerInductionNormalWidth
import MeirMoser.WarmStart

namespace MeirMoser

/-- One calibrated step preserves a (relaxed) GoodTailState.

    Output parameters: c' = c − height·(1+1/t), R unchanged, η unchanged.
    The new widthChecks list extends the old by one entry. -/
theorem step_preserves_GoodTailState
    (S : TailState) (widthChecks : List NormalWidthCheck)
    (c R η : ℚ) (h_R : 1 ≤ R)
    (h_state : GoodTailState c R η S widthChecks)
    (h_step_succeeds :
      (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
      (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0)
    (h_t_pos : 0 < S.t)
    (h_room : S.LRP.x1 - S.LRP.x0 - (1 : ℚ) / (S.t : ℕ) ≥ (S.LRP.y1 - S.LRP.y0) / R)
    (h_FP : FinitePacking (calibratedStep S).container (calibratedStep S).placed)
    : ∃ c', GoodTailState c' R η (calibratedStep S) (widthChecks ++ [newWidthCheck S]) := by
  rcases h_state with ⟨h_LRP_area, h_LRP_aspect, h_P_ep, h_widths, _h_finite⟩
  -- New c' from A.3.b's bound.
  refine ⟨c - S.LRP.height * (1 + 1 / (S.t : ℕ)), ?_, ?_, ?_, ?_, ?_⟩
  · -- (i) c' ≤ (calibratedStep S).LRP.area · (calibratedStep S).t.
    have h_area_bound :=
      calibratedStep_LRP_area_lower S h_step_succeeds h_t_pos
    -- We have: (cS S).LRP.area * (cS S).t ≥ S.LRP.area · S.t − height·(1+1/t).
    -- And c ≤ S.LRP.area · S.t.
    -- So c − height·(1+1/t) ≤ (cS S).LRP.area · (cS S).t.
    linarith
  · -- (ii) (calibratedStep S).LRP.maxSide ≤ R · (calibratedStep S).LRP.minSide.
    exact calibratedStep_LRP_aspect_preserved S R h_R h_LRP_aspect
            h_step_succeeds h_t_pos h_room
  · -- (iii) Σ semiperim ((calibratedStep S).endpointBoxes) ≤ η.
    rw [calibratedStep_preserves_endpoint_perim]
    exact h_P_ep
  · -- (iv) all width-checks (extended list) hold.
    exact calibratedStep_widthChecks_extend S widthChecks h_widths h_t_pos
  · -- (v) FinitePacking (calibratedStep S).container (calibratedStep S).placed.
    exact h_FP

end MeirMoser
