/-
  SchedulerInductionBalanced.lean: Lean definition of the BALANCED step (Route A R-A.1).

  We DEFINE `balancedStep : TailState → TailState` and `iteratedBalanced` here.
  Unlike `calibratedStep` (native orientation, x-cut), this step ALWAYS rotates
  the Moser rectangle D_t and cuts from the LONGER side of the LRP. This is
  intended to keep the LRP aspect ratio bounded.

  Convention (rotated D_t has width 1/(t+1), height 1/t):
    - `cutFromX S` is true iff `LRP.width ≥ LRP.height`.
    - On x-cut: shave a vertical strip of width 1/(t+1) from the left of LRP.
                Place rotated D_t at the bottom-left of this strip.
                Normal box = strip leftover above D_t (height LRP.height - 1/t).
    - On y-cut: shave a horizontal strip of height 1/t from the bottom of LRP.
                Place rotated D_t at the bottom-left of this strip.
                Normal box = strip leftover right of D_t (width LRP.width - 1/(t+1)).
    - In both branches the rotated D_t has the SAME shape (1/(t+1) × 1/t),
      so the fit condition is uniformly `1/(t+1) ≤ LRP.width ∧ 1/t ≤ LRP.height`.
-/
import MeirMoser.CalibratedScheduler
import MeirMoser.LRP
import MeirMoser.Cellification
import MeirMoser.EndpointPotential
import Mathlib.Tactic

namespace MeirMoser

/-- Decide whether the balanced step should cut from the x-axis side
    (i.e. the LRP is at least as wide as it is tall). -/
def cutFromX (S : TailState) : Bool :=
  decide (S.LRP.y1 - S.LRP.y0 ≤ S.LRP.x1 - S.LRP.x0)

/-- One balanced calibrated step.

    Always rotates D_t (placed dimensions 1/(t+1) wide × 1/t tall) and cuts a
    slice off the LONGER side of the LRP. Returns S unchanged if rotated D_t
    cannot fit in the LRP. -/
def balancedStep (S : TailState) : TailState :=
  let n := S.t
  let w : ℚ := 1 / ((n + 1 : ℕ) : ℕ)   -- rotated D_t width
  let h : ℚ := 1 / (n : ℕ)             -- rotated D_t height
  if hcanFit : w ≤ S.LRP.x1 - S.LRP.x0 ∧ h ≤ S.LRP.y1 - S.LRP.y0 then
    if cutFromX S then
      -- x-cut: vertical strip of width w on the left of LRP.
      { t := n + 1
        container := S.container
        placed := S.placed ++ [
          { n := n, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true }]
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
                have hw_pos : (0 : ℚ) ≤ 1 / ((n + 1 : ℕ) : ℕ) := by positivity
                linarith
              hy := by have := hcanFit.2; linarith }
          birthIdx := n }]
        endpointBoxes := S.endpointBoxes }
    else
      -- y-cut: horizontal strip of height h on the bottom of LRP.
      { t := n + 1
        container := S.container
        placed := S.placed ++ [
          { n := n, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true }]
        LRP :=
          { x0 := S.LRP.x0
            y0 := S.LRP.y0 + h
            x1 := S.LRP.x1
            y1 := S.LRP.y1
            hx := S.LRP.hx
            hy := by have := hcanFit.2; linarith }
        normalBoxes := S.normalBoxes ++ [{
          rect :=
            { x0 := S.LRP.x0 + w
              y0 := S.LRP.y0
              x1 := S.LRP.x1
              y1 := S.LRP.y0 + h
              hx := by have := hcanFit.1; linarith
              hy := by
                have hh_pos : (0 : ℚ) ≤ 1 / (n : ℕ) := by positivity
                linarith }
          birthIdx := n }]
        endpointBoxes := S.endpointBoxes }
  else
    S

/-- Iterate the balanced step k times. -/
def iteratedBalanced : ℕ → TailState → TailState
  | 0, S => S
  | (k+1), S => balancedStep (iteratedBalanced k S)

@[simp] theorem iteratedBalanced_zero (S : TailState) : iteratedBalanced 0 S = S := rfl
@[simp] theorem iteratedBalanced_succ (k : ℕ) (S : TailState) :
    iteratedBalanced (k+1) S = balancedStep (iteratedBalanced k S) := rfl

/-- The balanced step preserves the container. -/
theorem balancedStep_container (S : TailState) :
    (balancedStep S).container = S.container := by
  unfold balancedStep
  by_cases h : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0
  · rw [dif_pos h]
    by_cases hcut : cutFromX S
    · rw [if_pos hcut]
    · rw [if_neg hcut]
  · rw [dif_neg h]

/-- Step's `t` advances by 1 when rotated D_t fits in the LRP. -/
theorem balancedStep_t_advances {S : TailState}
    (hw : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0)
    (hh : (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0)
    : (balancedStep S).t = S.t + 1 := by
  unfold balancedStep
  rw [dif_pos ⟨hw, hh⟩]
  by_cases hcut : cutFromX S
  · rw [if_pos hcut]
  · rw [if_neg hcut]

end MeirMoser
