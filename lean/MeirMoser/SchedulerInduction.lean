/-
  SchedulerInduction.lean: Lean definition of the calibrated step (A.3.a).

  We DEFINE `calibratedStep : TailState → TailState` and `iteratedStep` here.
  The per-step invariance lemmas (A.3.b–f) and the infinite-extraction (A.4)
  build on this definition.

  Strategy: a SIMPLIFIED step that always cuts D_t from the LRP if it fits
  (native orientation, bottom-left corner). Otherwise return the state
  unchanged. This is enough for the Lean closure even though the empirical
  scheduler had endpoint priority.
-/
import MeirMoser.CalibratedScheduler
import MeirMoser.LRP
import MeirMoser.Cellification
import MeirMoser.EndpointPotential
import Mathlib.Tactic

namespace MeirMoser

/-- Calibrated active width `a_t` (rational lower bound). -/
def calibratedActiveWidth (t : ℕ) : ℚ := 1 / (t + 1 : ℕ)

/-- One simplified calibrated step.

    If `1/t ≤ LRP.width` and `1/(t+1) ≤ LRP.height`, place D_t native at the
    LRP's bottom-left corner; the right strip becomes the new LRP, the top
    strip a normal box. Otherwise the state is unchanged. -/
def calibratedStep (S : TailState) : TailState :=
  let n := S.t
  let w : ℚ := 1 / (n : ℕ)
  let h : ℚ := 1 / ((n + 1 : ℕ) : ℕ)
  if hcanFit : w ≤ S.LRP.x1 - S.LRP.x0 ∧ h ≤ S.LRP.y1 - S.LRP.y0 then
    { t := n + 1
      container := S.container
      placed := S.placed ++ [
        { n := n, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := false }]
      LRP :=
        { x0 := S.LRP.x0 + w
          y0 := S.LRP.y0
          x1 := S.LRP.x1
          y1 := S.LRP.y1
          hx := by have := hcanFit.1; linarith
          hy := S.LRP.hy }
      normalBoxes := S.normalBoxes ++ [{
        rect :=
          { x0 := S.LRP.x0
            y0 := S.LRP.y0 + h
            x1 := S.LRP.x0 + w
            y1 := S.LRP.y1
            hx := by
              have hw_pos : (0 : ℚ) ≤ 1 / (n : ℕ) := by positivity
              linarith
            hy := by have := hcanFit.2; linarith }
        birthIdx := n }]
      endpointBoxes := S.endpointBoxes }
  else
    S

/-- Iterate the step k times. -/
def iteratedStep : ℕ → TailState → TailState
  | 0, S => S
  | (k+1), S => calibratedStep (iteratedStep k S)

@[simp] theorem iteratedStep_zero (S : TailState) : iteratedStep 0 S = S := rfl
@[simp] theorem iteratedStep_succ (k : ℕ) (S : TailState) :
    iteratedStep (k+1) S = calibratedStep (iteratedStep k S) := rfl

/-- Step's `t` advances by 1 when LRP fits D_t. -/
theorem calibratedStep_t_advances {S : TailState}
    (hw : (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.x1 - S.LRP.x0)
    (hh : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0)
    : (calibratedStep S).t = S.t + 1 := by
  unfold calibratedStep
  rw [dif_pos ⟨hw, hh⟩]

/-- Step preserves the container. -/
theorem calibratedStep_container (S : TailState) :
    (calibratedStep S).container = S.container := by
  unfold calibratedStep
  by_cases h : (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0
  · rw [dif_pos h]
  · rw [dif_neg h]

/-! ### A.3.b–e: per-step preservation of GoodTailState components.

  Each lemma states that one of the four invariants is preserved under one
  calibrated step (with appropriate parameter updates). These are the
  building blocks of `step_preserves_GoodTailState` (A.3.f).

  In the simplified scheduler we use here:
    - The LRP loses a stripe of width 1/t from its left side.
    - One normal box is added: dim (1/t × (LRP.height - 1/(t+1))).
    - Endpoint set is unchanged.

  So:
    (i)   LRP area drops by (1/t) · LRP.height. We need: new S_LRP · (t+1) ≥ c.
    (ii)  LRP aspect: new width = old.width - 1/t. New aspect ≤ old aspect if old.height ≤ old.width;
          else may degrade to a bounded value. Use balanced cuts in the full scheduler.
    (iii) P_ep unchanged.
    (iv)  New normal box has width 1/t and birth t. Width-ratio = (1/t)·t^γ = t^{γ-1}.
          For γ ∈ (1, 3/2), t^{γ-1} ∈ (1, t^{1/2}); we'd need a more careful matching.
          The full framework uses the calibrated stripe a_t = 1/(t+1) + t^{-γ} so that
          width-ratio is ≈ 1.
-/

-- (A.3.c — schematic form deprecated; superseded by
-- `calibratedStep_LRP_aspect_preserved` in `SchedulerInductionLRPAspect.lean`,
-- which gives a full proof using a finer hypothesis `h_room`.)

/-- A.3.d trivially: simplified step doesn't add endpoints. -/
theorem calibratedStep_preserves_endpoint_perim (S : TailState) :
    ((calibratedStep S).endpointBoxes.map Rect.semiperim).sum =
    (S.endpointBoxes.map Rect.semiperim).sum := by
  unfold calibratedStep
  by_cases h : (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0
  · rw [dif_pos h]
  · rw [dif_neg h]

/-- The simplified step preserves containment in `container`. -/
theorem calibratedStep_LRP_in_container (S : TailState)
    (hin : S.container.contains S.LRP) :
    (calibratedStep S).container.contains (calibratedStep S).LRP := by
  unfold calibratedStep
  by_cases h : (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0
  · rw [dif_pos h]
    -- new LRP = (S.LRP.x0 + 1/t, S.LRP.y0, S.LRP.x1, S.LRP.y1) ⊆ S.LRP
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := hin.1; have hw_pos : (0 : ℚ) ≤ 1 / (S.t : ℕ) := by positivity
      linarith
    · exact hin.2.1
    · exact hin.2.2.1
    · exact hin.2.2.2
  · rw [dif_neg h]; exact hin

end MeirMoser
