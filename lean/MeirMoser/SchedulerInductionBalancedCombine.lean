/-
  SchedulerInductionBalancedCombine.lean (R-A.5): combines the four per-step
  balanced-step preservation lemmas into `step_preserves_GoodTailState_balanced`.
-/
import MeirMoser.SchedulerInductionBalanced
import MeirMoser.SchedulerInductionBalancedLRPArea
import MeirMoser.SchedulerInductionBalancedLRPAspect
import MeirMoser.SchedulerInductionBalancedAux
import MeirMoser.WarmStart

namespace MeirMoser

/-- One balanced calibrated step preserves a (relaxed) GoodTailState.

    Output parameters: c' = c − maxSide·(1+1/t), R unchanged, η unchanged.
    The new widthChecks list extends the old by one entry. -/
theorem step_preserves_GoodTailState_balanced
    (S : TailState) (widthChecks : List NormalWidthCheck)
    (c R η : ℚ) (h_R : 1 ≤ R)
    (h_state : GoodTailState c R η S widthChecks)
    (h_fit :
      (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
      (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0)
    (h_t_pos : 0 < S.t)
    (h_room : S.LRP.maxSide - (1 : ℚ) / (S.t : ℕ) ≥ S.LRP.minSide / R)
    (h_FP : FinitePacking (balancedStep S).container (balancedStep S).placed)
    : ∃ c', GoodTailState c' R η (balancedStep S) (widthChecks ++ [newWidthCheckBalanced S]) := by
  rcases h_state with ⟨h_LRP_area, h_LRP_aspect, h_P_ep, h_widths, _h_finite⟩
  -- New c' from the area-share bound.
  refine ⟨c - S.LRP.maxSide * (1 + 1 / (S.t : ℕ)), ?_, ?_, ?_, ?_, ?_⟩
  · -- (i) c' ≤ (balancedStep S).LRP.area · (balancedStep S).t.
    have h_area_bound :=
      balancedStep_LRP_area_lower S h_fit h_t_pos
    -- We have: (bS S).LRP.area * (bS S).t ≥ S.LRP.area · S.t − maxSide·(1+1/t).
    -- And c ≤ S.LRP.area · S.t.
    -- So c − maxSide·(1+1/t) ≤ (bS S).LRP.area · (bS S).t.
    linarith
  · -- (ii) (balancedStep S).LRP.maxSide ≤ R · (balancedStep S).LRP.minSide.
    exact balancedStep_LRP_aspect_preserved S R h_R h_LRP_aspect
            h_fit h_t_pos h_room
  · -- (iii) Σ semiperim ((balancedStep S).endpointBoxes) ≤ η.
    rw [balancedStep_preserves_endpoint_perim]
    exact h_P_ep
  · -- (iv) all width-checks (extended list) hold.
    exact balancedStep_widthChecks_extend S widthChecks h_widths
  · -- (v) FinitePacking (balancedStep S).container (balancedStep S).placed.
    exact h_FP

end MeirMoser
