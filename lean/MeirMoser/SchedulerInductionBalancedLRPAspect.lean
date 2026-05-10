/-
  SchedulerInductionBalancedLRPAspect.lean: per-step LRP aspect preservation for
  the BALANCED step (Route A R-A.3).

  We prove that `balancedStep` preserves the aspect bound of the LRP, given a
  "room" hypothesis on the cut.  This is the calibrated framework's invariant
  (ii):  `LRP.maxSide ≤ R · LRP.minSide`.

  The balanced step always cuts from the LONGER side of the LRP:
    - if `cutFromX S` (W ≥ H):  new W = W − 1/(t+1), new H = H.
    - else (H > W):              new W = W,         new H = H − 1/t.
  In both cases the longer side shrinks by at most `1/t` (since
  `1/(t+1) ≤ 1/t`).

  The "room" hypothesis is the conservative bound:
    `LRP.maxSide − 1/t ≥ LRP.minSide / R`,
  which guarantees that even after the larger cut `1/t`, the formerly-longer
  side stays at least `minSide / R`.  This in turn keeps the new aspect ratio
  bounded by `R`.

  Approach (per orientation):
    Let M = old.maxSide (longer side), m = old.minSide (shorter side).
    Let δ ∈ {1/(t+1), 1/t} be the actual cut.  We have δ ≤ 1/t.
    After the cut: longer side becomes M − δ, shorter side stays m.
    Case A:  M − δ ≥ m.   Then maxSide' = M − δ ≤ M ≤ R · m = R · minSide'.
    Case B:  M − δ < m.   Then maxSide' = m, minSide' = M − δ.
              From `h_room`: M − 1/t ≥ m / R, so M − δ ≥ M − 1/t ≥ m / R,
              hence m ≤ R · (M − δ) = R · minSide'.
-/
import MeirMoser.SchedulerInductionBalanced
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace MeirMoser

/-- (R-A.3) Per-step LRP aspect preservation under the balanced step.  The
    "room" hypothesis says the cut leaves enough on the longer side: after
    removing `1/t` (the worst-case cut), what remains is at least `minSide / R`.
    The conclusion is that the new LRP still satisfies
    `maxSide ≤ R · minSide`. -/
theorem balancedStep_LRP_aspect_preserved
    (S : TailState) (R : ℚ) (h_R : 1 ≤ R)
    (h_aspect : S.LRP.maxSide ≤ R * S.LRP.minSide)
    (h_fit : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
             (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0)
    (h_t_pos : 0 < S.t)
    (h_room : S.LRP.maxSide - (1 : ℚ) / (S.t : ℕ) ≥ S.LRP.minSide / R)
    : (balancedStep S).LRP.maxSide ≤ R * (balancedStep S).LRP.minSide := by
  -- Unfold to the success branch of `balancedStep`.
  unfold balancedStep
  rw [dif_pos h_fit]
  -- Abbreviations.
  set W : ℚ := S.LRP.x1 - S.LRP.x0 with hW_def
  set H : ℚ := S.LRP.y1 - S.LRP.y0 with hH_def
  set wcut : ℚ := (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) with hwcut_def
  set hcut : ℚ := (1 : ℚ) / (S.t : ℕ) with hhcut_def
  -- Positivity facts.
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one h_R
  have hwcut_nn : 0 ≤ wcut := by unfold_let wcut; positivity
  have hhcut_nn : 0 ≤ hcut := by unfold_let hcut; positivity
  -- 1/(t+1) ≤ 1/t : the wcut is at most the hcut.
  have hwcut_le_hcut : wcut ≤ hcut := by
    unfold_let wcut hcut
    have ht_pos_q : (0 : ℚ) < (S.t : ℕ) := by exact_mod_cast h_t_pos
    have ht1_pos_q : (0 : ℚ) < ((S.t + 1 : ℕ) : ℕ) := by
      have : (0 : ℕ) < S.t + 1 := Nat.succ_pos _
      exact_mod_cast this
    have h_le : ((S.t : ℕ) : ℚ) ≤ ((S.t + 1 : ℕ) : ℕ) := by
      have : (S.t : ℕ) ≤ (S.t + 1 : ℕ) := Nat.le_succ _
      exact_mod_cast this
    exact one_div_le_one_div_of_le ht_pos_q h_le
  have hW_pos : (0 : ℚ) ≤ W := by
    have := h_fit.1
    have : wcut ≤ W := this
    linarith
  have hH_pos : (0 : ℚ) ≤ H := by
    have := h_fit.2
    have : hcut ≤ H := this
    linarith
  -- Old aspect facts in terms of W, H.
  have h_old_aspect : max W H ≤ R * min W H := by
    have := h_aspect
    show max W H ≤ R * min W H
    convert this using 2 <;> rfl
  -- Rewrite h_room in terms of W, H, hcut.
  have h_room' : max W H - hcut ≥ min W H / R := by
    have := h_room
    show max W H - hcut ≥ min W H / R
    convert this using 2 <;> rfl
  -- Case split on cutFromX S.
  by_cases hcut_branch : cutFromX S
  · -- x-cut branch: new LRP has width W − wcut, height H.
    rw [if_pos hcut_branch]
    -- cutFromX = decide (H ≤ W), so we know H ≤ W.
    have hHW : H ≤ W := by
      unfold cutFromX at hcut_branch
      simpa [hW_def, hH_def] using
        (decide_eq_true_iff (p := S.LRP.y1 - S.LRP.y0 ≤ S.LRP.x1 - S.LRP.x0)).mp
          hcut_branch
    -- Old max = W, old min = H.
    have h_max_W : max W H = W := max_eq_left hHW
    have h_min_H : min W H = H := min_eq_right hHW
    have h_old_aspect_W : W ≤ R * H := by
      have := h_old_aspect; rw [h_max_W, h_min_H] at this; exact this
    have h_room_W : W - hcut ≥ H / R := by
      have := h_room'; rw [h_max_W, h_min_H] at this; exact this
    have h_room_W' : W - wcut ≥ H / R := by
      have h1 : W - hcut ≤ W - wcut := by linarith
      linarith
    -- Goal: max ((x1) − (x0+wcut)) (y1 − y0) ≤ R * min ...
    show max (S.LRP.x1 - (S.LRP.x0 + wcut)) (S.LRP.y1 - S.LRP.y0)
         ≤ R * min (S.LRP.x1 - (S.LRP.x0 + wcut)) (S.LRP.y1 - S.LRP.y0)
    have h_eq_w : S.LRP.x1 - (S.LRP.x0 + wcut) = W - wcut := by
      show S.LRP.x1 - (S.LRP.x0 + wcut) = (S.LRP.x1 - S.LRP.x0) - wcut
      ring
    have h_eq_h : S.LRP.y1 - S.LRP.y0 = H := rfl
    rw [h_eq_w, h_eq_h]
    show max (W - wcut) H ≤ R * min (W - wcut) H
    -- Sub-case: is W − wcut ≥ H or W − wcut < H?
    rcases le_or_lt H (W - wcut) with hcase | hcase
    · -- W − wcut ≥ H: new max = W − wcut, new min = H.
      have h_max : max (W - wcut) H = W - wcut := max_eq_left hcase
      have h_min : min (W - wcut) H = H := min_eq_right hcase
      rw [h_max, h_min]
      -- Need W − wcut ≤ R · H. From W ≤ R · H and wcut ≥ 0.
      linarith
    · -- W − wcut < H: new max = H, new min = W − wcut.
      have hcase' : W - wcut ≤ H := le_of_lt hcase
      have h_max : max (W - wcut) H = H := max_eq_right hcase'
      have h_min : min (W - wcut) H = W - wcut := min_eq_left hcase'
      rw [h_max, h_min]
      -- Need H ≤ R · (W − wcut). From h_room_W': W − wcut ≥ H/R.
      have h1 : H / R * R ≤ (W - wcut) * R :=
        mul_le_mul_of_nonneg_right h_room_W' hR_pos.le
      have h2 : H / R * R = H := by
        rw [div_mul_cancel₀]; exact ne_of_gt hR_pos
      rw [h2] at h1
      linarith
  · -- y-cut branch: new LRP has width W, height H − hcut.
    rw [if_neg hcut_branch]
    -- Not cutFromX = decide (H ≤ W), so H > W (strictly).
    have hWH : W < H := by
      unfold cutFromX at hcut_branch
      have h_dec :
          ¬ (S.LRP.y1 - S.LRP.y0 ≤ S.LRP.x1 - S.LRP.x0) := by
        intro hle
        apply hcut_branch
        exact (decide_eq_true_iff
          (p := S.LRP.y1 - S.LRP.y0 ≤ S.LRP.x1 - S.LRP.x0)).mpr hle
      have : S.LRP.x1 - S.LRP.x0 < S.LRP.y1 - S.LRP.y0 := lt_of_not_ge h_dec
      simpa [hW_def, hH_def] using this
    have hWH_le : W ≤ H := le_of_lt hWH
    -- Old max = H, old min = W.
    have h_max_H : max W H = H := max_eq_right hWH_le
    have h_min_W : min W H = W := min_eq_left hWH_le
    have h_old_aspect_H : H ≤ R * W := by
      have := h_old_aspect; rw [h_max_H, h_min_W] at this; exact this
    have h_room_H : H - hcut ≥ W / R := by
      have := h_room'; rw [h_max_H, h_min_W] at this; exact this
    -- Goal: max (x1 − x0) ((y1) − (y0+hcut)) ≤ R * min ...
    show max (S.LRP.x1 - S.LRP.x0) (S.LRP.y1 - (S.LRP.y0 + hcut))
         ≤ R * min (S.LRP.x1 - S.LRP.x0) (S.LRP.y1 - (S.LRP.y0 + hcut))
    have h_eq_w : S.LRP.x1 - S.LRP.x0 = W := rfl
    have h_eq_h : S.LRP.y1 - (S.LRP.y0 + hcut) = H - hcut := by
      show S.LRP.y1 - (S.LRP.y0 + hcut) = (S.LRP.y1 - S.LRP.y0) - hcut
      ring
    rw [h_eq_w, h_eq_h]
    show max W (H - hcut) ≤ R * min W (H - hcut)
    -- Sub-case: is H − hcut ≥ W or H − hcut < W?
    rcases le_or_lt W (H - hcut) with hcase | hcase
    · -- H − hcut ≥ W: new max = H − hcut, new min = W.
      have h_max : max W (H - hcut) = H - hcut := max_eq_right hcase
      have h_min : min W (H - hcut) = W := min_eq_left hcase
      rw [h_max, h_min]
      -- Need H − hcut ≤ R · W. From H ≤ R · W and hcut ≥ 0.
      linarith
    · -- H − hcut < W: new max = W, new min = H − hcut.
      have hcase' : H - hcut ≤ W := le_of_lt hcase
      have h_max : max W (H - hcut) = W := max_eq_left hcase'
      have h_min : min W (H - hcut) = H - hcut := min_eq_right hcase'
      rw [h_max, h_min]
      -- Need W ≤ R · (H − hcut). From h_room_H: H − hcut ≥ W/R.
      have h1 : W / R * R ≤ (H - hcut) * R :=
        mul_le_mul_of_nonneg_right h_room_H hR_pos.le
      have h2 : W / R * R = W := by
        rw [div_mul_cancel₀]; exact ne_of_gt hR_pos
      rw [h2] at h1
      linarith

end MeirMoser
