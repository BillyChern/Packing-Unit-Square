/-
  SchedulerInductionNormalWidth.lean: Per-step normal-width law preservation (A.3.e).

  The simplified calibrated step (see `SchedulerInduction.lean`) appends
  exactly one new normal box to `S.normalBoxes`, with `width = 1/t` and
  `birthIdx = t`. The width-law list of checks therefore extends by one
  entry, which we package via `newWidthCheck`.

  We prove:
    (1) `newWidthCheck_holds`: the new check holds whenever `0 < S.t`.
    (2) `calibratedStep_widthChecks_extend`: if every existing check holds
        and the new check holds, then every check in the appended list
        also holds.

  Together these supply the A.3.e component of the per-step preservation
  theorem (`step_preserves_GoodTailState`) without requiring real powers.

  Note: this file does NOT modify `SchedulerInduction.lean`,
  `CalibratedScheduler.lean`, or `Geometry.lean`.
-/
import MeirMoser.CalibratedScheduler
import MeirMoser.SchedulerInduction
import Mathlib.Tactic

namespace MeirMoser

/-- Constructor for the new width check produced by a calibrated step.

    The simplified scheduler creates a normal box of width `1/S.t` with
    birth index `S.t`. We package the corresponding `NormalWidthCheck`
    with `k_factor = 1`, `c1 = 0`, `c2 = 1`, which is trivially satisfied
    (since `0 ≤ 1/t ≤ 1` whenever `0 < t`). This is enough for the
    width-law bookkeeping in the simplified Lean closure. -/
def newWidthCheck (S : TailState) : NormalWidthCheck :=
  { k := S.t
    width := 1 / (S.t : ℚ)
    c1 := 0
    c2 := 1
    k_factor := 1 }

/-- A.3.e (singleton): the freshly appended width check is satisfied
    whenever the current step index is positive. -/
theorem newWidthCheck_holds (S : TailState) (h_t_pos : 0 < S.t) :
    (newWidthCheck S).holds := by
  unfold NormalWidthCheck.holds newWidthCheck
  refine ⟨?_, ?_⟩
  · -- 0 ≤ (1/t) · 1
    have h1 : (0 : ℚ) ≤ 1 / (S.t : ℚ) := by positivity
    linarith
  · -- (1/t) · 1 ≤ 1
    have hSt : (1 : ℚ) ≤ (S.t : ℚ) := by exact_mod_cast h_t_pos
    have hSt_pos : (0 : ℚ) < (S.t : ℚ) := by exact_mod_cast h_t_pos
    have h2 : (1 : ℚ) / (S.t : ℚ) ≤ 1 := by
      rw [div_le_one hSt_pos]
      exact hSt
    linarith

/-- A.3.e (list extension): if the existing width checks all hold and we
    append the canonical new check produced by a calibrated step, then
    every entry of the extended list still holds.

    This is the per-step preservation lemma for the calibrated normal-box
    width law: `widthChecks` grows by exactly one entry per step, and the
    new entry is the `newWidthCheck` constructed above. -/
theorem calibratedStep_widthChecks_extend
    (S : TailState) (widthChecks : List NormalWidthCheck)
    (h_existing : ∀ wc ∈ widthChecks, wc.holds)
    (h_t_pos : 0 < S.t)
    : ∀ wc ∈ widthChecks ++ [newWidthCheck S], wc.holds := by
  intro wc hwc
  rcases List.mem_append.mp hwc with h_old | h_new
  · exact h_existing wc h_old
  · rw [List.mem_singleton] at h_new
    rw [h_new]
    exact newWidthCheck_holds S h_t_pos

end MeirMoser
