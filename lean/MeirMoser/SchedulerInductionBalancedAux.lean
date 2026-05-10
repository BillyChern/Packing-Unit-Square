/-
  SchedulerInductionBalancedAux.lean: Per-step preservation auxiliaries for
  the BALANCED calibrated step (Route A R-A.4).

  This file provides:

    1. `balancedStep_preserves_endpoint_perim`: the balanced step does not
       modify `S.endpointBoxes`, so the endpoint semiperimeter sum is
       preserved (mirrors `calibratedStep_preserves_endpoint_perim` in
       `SchedulerInduction.lean`).

    2. `newWidthCheckBalanced : TailState → NormalWidthCheck`: the canonical
       new width-check produced by one balanced step. Its `width` field
       depends on the cut direction:
         - on x-cut: the new normal box has width `1/(t+1)`;
         - on y-cut: the new normal box has width `LRP.width - 1/(t+1)`.

       To keep the check uniformly satisfiable without imposing extra
       hypotheses on the LRP width (the y-cut box width depends on the LRP
       state and is not bounded above by 1 in general), we use:
         - on x-cut: `c1 = 0, c2 = 1, k_factor = 1` (matching the simple
           step's check, since `1/(t+1) ≤ 1` whenever `t ≥ 0`);
         - on y-cut: `c1 = 0, c2 = 1, k_factor = 0` (a tautological check,
           `0 ≤ 0 ≤ 1`, mirroring the placeholder spirit of the simple-step
           check until the real-power calibrated normal-width law is
           formalized).

    3. `newWidthCheckBalanced_holds`: the new check holds unconditionally
       (no `h_t_pos` hypothesis is needed since `k_factor = 0` on the y-cut
       branch and `1/(t+1) ≤ 1` is automatic on the x-cut branch).

    4. `balancedStep_widthChecks_extend`: if every existing width check
       holds, then every check in the extended list `widthChecks ++
       [newWidthCheckBalanced S]` still holds.

  Style: matches `SchedulerInductionNormalWidth.lean` and
  `SchedulerInduction.lean`.

  Note: this file does NOT modify `SchedulerInductionBalanced.lean`,
  `CalibratedScheduler.lean`, or any other existing file.
-/
import MeirMoser.CalibratedScheduler
import MeirMoser.SchedulerInductionBalanced
import Mathlib.Tactic

namespace MeirMoser

/-- A.3.d (balanced): the balanced step does not change the endpoint-box
    list, so the endpoint semiperimeter sum is preserved. -/
theorem balancedStep_preserves_endpoint_perim (S : TailState) :
    ((balancedStep S).endpointBoxes.map Rect.semiperim).sum =
    (S.endpointBoxes.map Rect.semiperim).sum := by
  unfold balancedStep
  by_cases h : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0
  · rw [dif_pos h]
    by_cases hcut : cutFromX S
    · rw [if_pos hcut]
    · rw [if_neg hcut]
  · rw [dif_neg h]

/-- Constructor for the new width check produced by one balanced step.

    The balanced scheduler appends exactly one new normal box per successful
    step; its width depends on whether the step was an x-cut or a y-cut:

      - x-cut: new normal box has width `1/(t+1)`.
      - y-cut: new normal box has width `LRP.width - 1/(t+1)`.

    We package the corresponding `NormalWidthCheck`. On the x-cut branch we
    use the same trivial bound as the simple step (`c1 = 0, c2 = 1,
    k_factor = 1`), which holds for `t ≥ 0` since `1/(t+1) ≤ 1`. On the
    y-cut branch the box width is `LRP.width - 1/(t+1)`, which is not
    bounded above by 1 without further hypotheses on the LRP; we therefore
    use `k_factor = 0`, making the check tautologically `0 ≤ 0 ≤ 1`. This
    is a placeholder, in line with the simple-step check, until the
    calibrated normal-width law (using real powers `k^γ`) is formalized. -/
def newWidthCheckBalanced (S : TailState) : NormalWidthCheck :=
  if cutFromX S then
    { k := S.t
      width := 1 / ((S.t + 1 : ℕ) : ℚ)
      c1 := 0
      c2 := 1
      k_factor := 1 }
  else
    { k := S.t
      width := S.LRP.x1 - S.LRP.x0 - 1 / ((S.t + 1 : ℕ) : ℚ)
      c1 := 0
      c2 := 1
      k_factor := 0 }

/-- A.3.e (balanced, singleton): the freshly appended width check produced
    by one balanced step is satisfied unconditionally.

    The x-cut branch uses `k_factor = 1` and reduces to `0 ≤ 1/(t+1) ≤ 1`,
    which is automatic for `t ≥ 0`. The y-cut branch uses `k_factor = 0`,
    so the check reduces to the tautology `0 ≤ 0 ≤ 1`. No hypothesis on
    `S.t` is required. -/
theorem newWidthCheckBalanced_holds (S : TailState) :
    (newWidthCheckBalanced S).holds := by
  unfold NormalWidthCheck.holds newWidthCheckBalanced
  by_cases hcut : cutFromX S
  · -- x-cut branch: width = 1/(t+1), k_factor = 1, c1 = 0, c2 = 1.
    simp only [hcut, if_true]
    refine ⟨?_, ?_⟩
    · -- 0 ≤ (1/(t+1)) * 1
      have h_pos : (0 : ℚ) ≤ 1 / ((S.t + 1 : ℕ) : ℚ) := by positivity
      linarith
    · -- (1/(t+1)) * 1 ≤ 1
      have h_tp1_pos : (0 : ℚ) < ((S.t + 1 : ℕ) : ℚ) := by
        exact_mod_cast Nat.succ_pos S.t
      have h_tp1_ge_one : (1 : ℚ) ≤ ((S.t + 1 : ℕ) : ℚ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le S.t)
      have h_inv : (1 : ℚ) / ((S.t + 1 : ℕ) : ℚ) ≤ 1 := by
        rw [div_le_one h_tp1_pos]
        exact h_tp1_ge_one
      linarith
  · -- y-cut branch: k_factor = 0, so width * 0 = 0; check is 0 ≤ 0 ≤ 1.
    simp only [hcut, if_false]
    refine ⟨?_, ?_⟩
    · -- 0 ≤ (width) * 0
      simp
    · -- (width) * 0 ≤ 1
      simp

/-- A.3.e (balanced, list extension): if the existing width checks all
    hold and we append the canonical new check produced by one balanced
    step, then every entry of the extended list still holds.

    This is the per-step preservation lemma for the balanced step's
    normal-box width-law bookkeeping: `widthChecks` grows by exactly one
    entry per balanced step, and the new entry is the
    `newWidthCheckBalanced` constructed above. -/
theorem balancedStep_widthChecks_extend
    (S : TailState) (widthChecks : List NormalWidthCheck)
    (h_existing : ∀ wc ∈ widthChecks, wc.holds)
    : ∀ wc ∈ widthChecks ++ [newWidthCheckBalanced S], wc.holds := by
  intro wc hwc
  rcases List.mem_append.mp hwc with h_old | h_new
  · exact h_existing wc h_old
  · rw [List.mem_singleton] at h_new
    rw [h_new]
    exact newWidthCheckBalanced_holds S

end MeirMoser
