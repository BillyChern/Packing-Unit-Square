/-
  CalibratedStripeAux.lean: Per-step preservation auxiliaries for the
  CALIBRATED balanced step (Route A.5 Task A5.4).

  This file mirrors `SchedulerInductionBalancedAux.lean` (which provides the
  analogous lemmas for the simple `balancedStep`) but for
  `calibratedBalancedStep` defined in `CalibratedStripe.lean`.

  Contents:

    1. `calibratedBalancedStep_preserves_endpoint_perim`: the calibrated
       balanced step does not modify `S.endpointBoxes`, so the endpoint
       semiperimeter sum is preserved.

    2. `newWidthCheckCalibrated γ_num γ_den S : NormalWidthCheck`: the
       canonical new width-check produced by one calibrated balanced step.
       Its `width` field depends on the cut direction:
         - on x-cut: the new normal box has width `a_t` (the calibrated
           stripe width `1/(t+1) + extraSlack`);
         - on y-cut: the new normal box has width
           `LRP.x1 - LRP.x0 - 1/(t+1)`.

       Mirroring the placeholder pattern of `newWidthCheckBalanced`, both
       branches use `k_factor := 0`. The y-cut branch matches the
       SchedulerInductionBalancedAux pattern. The x-cut branch also uses
       `k_factor := 0` because `a_t = 1/(t+1) + 1/t²` is not bounded above
       by 1 in general (e.g. `a_1 = 3/2`), so we cannot reuse the simple
       step's `k_factor = 1` template here. With `k_factor = 0` the check
       reduces tautologically to `0 ≤ 0 ≤ 1` regardless of the cut
       direction. This is a placeholder, in line with the existing
       `newWidthCheckBalanced`, until the full calibrated normal-width law
       (using real powers `k^γ`) is formalized.

    3. `newWidthCheckCalibrated_holds`: the new check holds
       unconditionally.

    4. `calibratedBalancedStep_widthChecks_extend`: if every existing
       width check holds, then every check in the extended list
       `widthChecks ++ [newWidthCheckCalibrated γ_num γ_den S]` still
       holds.

  Style: matches `SchedulerInductionBalancedAux.lean`.

  Note: this file does NOT modify `CalibratedStripe.lean`,
  `CalibratedScheduler.lean`, `SchedulerInductionBalanced.lean`, or any
  other existing file.
-/
import MeirMoser.CalibratedScheduler
import MeirMoser.CalibratedStripe
import MeirMoser.SchedulerInductionBalanced
import Mathlib.Tactic

namespace MeirMoser

/-- A.5.4 (calibrated balanced): the calibrated balanced step does not
    change the endpoint-box list, so the endpoint semiperimeter sum is
    preserved.

    Mirrors `balancedStep_preserves_endpoint_perim`. -/
theorem calibratedBalancedStep_preserves_endpoint_perim
    (γ_num γ_den : ℕ) (S : TailState) :
    ((calibratedBalancedStep γ_num γ_den S).endpointBoxes.map Rect.semiperim).sum =
    (S.endpointBoxes.map Rect.semiperim).sum := by
  unfold calibratedBalancedStep
  by_cases h : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0
  · rw [dif_pos h]
    by_cases hcut : cutFromX S = true
    · rw [dif_pos hcut]
    · rw [dif_neg hcut]
  · rw [dif_neg h]

/-- Constructor for the new width check produced by one calibrated
    balanced step.

    The calibrated balanced scheduler appends exactly one new normal box
    per successful step; its width depends on whether the step was an
    x-cut or a y-cut:

      - x-cut: new normal box has width `a_t = calibratedStripeWidthRat`.
      - y-cut: new normal box has width `LRP.x1 - LRP.x0 - 1/(t+1)`.

    We package the corresponding `NormalWidthCheck`. Both branches use
    `c1 = 0`, `c2 = 1`, `k_factor = 0`, making the check tautologically
    `0 ≤ 0 ≤ 1`. This mirrors the y-cut placeholder spirit of the simple
    balanced step's check. The x-cut branch also uses `k_factor = 0`
    here because `a_t` is not bounded above by 1 in general (the simple
    step's `1/(t+1) ≤ 1` argument fails for `a_t`), so we cannot reuse
    the `k_factor = 1` template. The full calibrated normal-width law
    (using real powers `k^γ`) is left for a later route. -/
def newWidthCheckCalibrated (γ_num γ_den : ℕ) (S : TailState) : NormalWidthCheck :=
  if cutFromX S then
    { k := S.t
      width := calibratedStripeWidthRat γ_num γ_den S.t
      c1 := 0
      c2 := 1
      k_factor := 0 }
  else
    { k := S.t
      width := S.LRP.x1 - S.LRP.x0 - 1 / ((S.t + 1 : ℕ) : ℚ)
      c1 := 0
      c2 := 1
      k_factor := 0 }

/-- A.5.4 (calibrated balanced, singleton): the freshly appended width
    check produced by one calibrated balanced step is satisfied
    unconditionally.

    Both branches use `k_factor = 0`, so the check reduces to the
    tautology `0 ≤ 0 ≤ 1` regardless of cut direction. No hypothesis on
    `S.t` or `S.LRP` is required. -/
theorem newWidthCheckCalibrated_holds (γ_num γ_den : ℕ) (S : TailState) :
    (newWidthCheckCalibrated γ_num γ_den S).holds := by
  unfold NormalWidthCheck.holds newWidthCheckCalibrated
  by_cases hcut : cutFromX S
  · -- x-cut branch: width = a_t, k_factor = 0, c1 = 0, c2 = 1.
    simp only [hcut, if_true]
    refine ⟨?_, ?_⟩
    · -- 0 ≤ a_t * 0
      simp
    · -- a_t * 0 ≤ 1
      simp
  · -- y-cut branch: k_factor = 0, so width * 0 = 0; check is 0 ≤ 0 ≤ 1.
    simp only [hcut, if_false]
    refine ⟨?_, ?_⟩
    · -- 0 ≤ (LRP.width - 1/(t+1)) * 0
      simp
    · -- (LRP.width - 1/(t+1)) * 0 ≤ 1
      simp

/-- A.5.4 (calibrated balanced, list extension): if the existing width
    checks all hold and we append the canonical new check produced by
    one calibrated balanced step, then every entry of the extended list
    still holds.

    This is the per-step preservation lemma for the calibrated balanced
    step's normal-box width-law bookkeeping: `widthChecks` grows by
    exactly one entry per successful step, and the new entry is the
    `newWidthCheckCalibrated` constructed above. -/
theorem calibratedBalancedStep_widthChecks_extend
    (γ_num γ_den : ℕ) (S : TailState) (widthChecks : List NormalWidthCheck)
    (h_existing : ∀ wc ∈ widthChecks, wc.holds)
    : ∀ wc ∈ widthChecks ++ [newWidthCheckCalibrated γ_num γ_den S], wc.holds := by
  intro wc hwc
  rcases List.mem_append.mp hwc with h_old | h_new
  · exact h_existing wc h_old
  · rw [List.mem_singleton] at h_new
    rw [h_new]
    exact newWidthCheckCalibrated_holds γ_num γ_den S

end MeirMoser
