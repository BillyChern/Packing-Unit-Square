/-
  CalibratedStripeTailProof.lean (Route A.5 Task A5.10):
  the proof of the calibrated tail packing under the CALIBRATED step,
  composing per-step preservation (`CalibratedStripe` +
  `CalibratedStripeContainment` + helpers in `CalibratedStripeExtraction`)
  into the full infinite packing.

  Mirrors `CalibratedTailProofBalanced.lean` (the simplified-balanced version)
  but adapted for the CALIBRATED step:
    - rotated D_t with width 1/(t+1), height 1/t (same as balanced),
    - LRP shifts by `a_t = calibratedStripeWidthRat γ_num γ_den t` instead of
      `1/(t+1)` (x-cut) or `1/t` (y-cut). The bridge inequalities
      `1/(t+1) ≤ a_t` and `1/t ≤ a_t` (for t ≥ 1) make the disjointness proof
      go through unchanged.

  Output: `calibrated_tail_from_calibrated_steps_success`, conditional on
  `AllStepsSucceed_calibrated γ_num γ_den S` plus three explicit geometric
  preconditions (`S.t ≥ 1`, `S.LRP ⊆ S.container`, `S.LRP` interior-disjoint
  from every placement in `S.placed`).
-/
import MeirMoser.CalibratedStripe
import MeirMoser.CalibratedStripeContainment
import MeirMoser.CalibratedStripeExtraction
import MeirMoser.WarmStart

namespace MeirMoser.CalibratedStripeTailProof

open MeirMoser

/-- Hypothesis: the CALIBRATED scheduler succeeds at every iteration starting
    from S.

    The fit condition is `a_t ≤ width ∧ 1/t ≤ height` because the rotated D_t
    has dimensions `1/(t+1) × 1/t`, but on the cut axis we need to peel off a
    full `a_t = 1/(t+1) + 1/t²` slab. -/
def AllStepsSucceed_calibrated (γ_num γ_den : ℕ) (S : TailState) : Prop :=
  ∀ k : ℕ,
    calibratedStripeWidthRat γ_num γ_den (iteratedCalibrated γ_num γ_den k S).t ≤
        (iteratedCalibrated γ_num γ_den k S).LRP.x1 -
        (iteratedCalibrated γ_num γ_den k S).LRP.x0 ∧
    (1 : ℚ) / ((iteratedCalibrated γ_num γ_den k S).t : ℕ) ≤
        (iteratedCalibrated γ_num γ_den k S).LRP.y1 -
        (iteratedCalibrated γ_num γ_den k S).LRP.y0

/-- Calibrated tail theorem (calibrated-step version).

    Assuming `AllStepsSucceed_calibrated γ_num γ_den S`, plus `S.t ≥ 1`,
    `S.LRP ⊆ S.container`, and `S.LRP` interior-disjoint from every placement
    in `S.placed`, we get the full packing. -/
theorem calibrated_tail_from_calibrated_steps_success
    (γ_num γ_den : ℕ) (S : TailState)
    (h_steps : AllStepsSucceed_calibrated γ_num γ_den S)
    (h_t_pos : 1 ≤ S.t)
    (h_LRP_in_container : S.container.contains S.LRP)
    (h_LRP_disj : ∀ P ∈ S.placed, Rect.interiorDisjoint S.LRP P.toRect)
    : MoserPacksFromAvoid S.t S.container S.placed := by
  -- Local abbreviation for the success predicate restricted to first (k+1) steps.
  have h_succ : ∀ k, ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j :=
    fun k j _ => h_steps j
  -- Reusable helper: for n ≥ S.t,
  --   extractedPackingCalibrated γ_num γ_den S n
  --     = stepPlacementCalibrated γ_num γ_den S (n - S.t).
  have h_extr : ∀ n, S.t ≤ n →
      extractedPackingCalibrated γ_num γ_den S n =
      stepPlacementCalibrated γ_num γ_den S (n - S.t) := by
    intro n hn
    unfold extractedPackingCalibrated
    rw [dif_neg (by omega : ¬ n < S.t)]
  -- Helper: t at step k is positive when S.t ≥ 1.
  have h_tk_pos : ∀ k, 0 < (iteratedCalibrated γ_num γ_den k S).t := by
    intro k
    induction k with
    | zero => exact h_t_pos
    | succ k ih =>
        rw [iteratedCalibrated_succ]
        exact calibratedBalancedStep_t_pos γ_num γ_den _ ih
  -- Use extractedPackingCalibrated γ_num γ_den S as the witness.
  refine ⟨extractedPackingCalibrated γ_num γ_den S, ?dims, ?inside, ?disj, ?avoid⟩
  case dims =>
    -- dims: for n ≥ S.t, (extractedPackingCalibrated γ_num γ_den S n).n = n
    --       and validDims (rotated branch).
    intro n hn
    set k := n - S.t with hk_def
    have hk_eq : n = S.t + k := by omega
    have hn_pos : 1 ≤ n := by omega
    have hn_ne : (n : ℕ) ≠ 0 := by omega
    have h_extr' : extractedPackingCalibrated γ_num γ_den S n =
        stepPlacementCalibrated γ_num γ_den S k := h_extr n hn
    have h_n : (stepPlacementCalibrated γ_num γ_den S k).n = n := by
      rw [stepPlacementCalibrated_n γ_num γ_den S k (h_succ k), ← hk_eq]
    have h_rot : (stepPlacementCalibrated γ_num γ_den S k).rotated = true :=
      stepPlacementCalibrated_rotated γ_num γ_den S k (h_succ k)
    refine ⟨?_, ?_⟩
    · -- (extractedPackingCalibrated γ_num γ_den S n).n = n
      rw [h_extr', h_n]
    · -- (extractedPackingCalibrated γ_num γ_den S n).validDims
      unfold PlacedRect.validDims
      rw [h_extr']
      refine ⟨?_, ?_⟩
      · rw [h_n]; exact hn_pos
      · rw [h_rot]
        simp only [↓reduceIte]
        refine ⟨?_, ?_⟩
        · -- width = 1 / (n + 1)
          unfold PlacedRect.width
          rw [h_n, h_rot]
          simp [hn_ne]
        · -- height = 1 / n
          unfold PlacedRect.height
          rw [h_n, h_rot]
          simp [hn_ne]
  case inside =>
    -- inside: containment in S.container.
    intro n hn
    set k := n - S.t with hk_def
    have hk_eq : n = S.t + k := by omega
    have hn_pos : 1 ≤ n := by omega
    have hn_ne : (n : ℕ) ≠ 0 := by omega
    have h_extr' : extractedPackingCalibrated γ_num γ_den S n =
        stepPlacementCalibrated γ_num γ_den S k := h_extr n hn
    have h_x0 : (stepPlacementCalibrated γ_num γ_den S k).x0 =
        (iteratedCalibrated γ_num γ_den k S).LRP.x0 :=
      stepPlacementCalibrated_x0 γ_num γ_den S k (h_succ k)
    have h_y0 : (stepPlacementCalibrated γ_num γ_den S k).y0 =
        (iteratedCalibrated γ_num γ_den k S).LRP.y0 :=
      stepPlacementCalibrated_y0 γ_num γ_den S k (h_succ k)
    have h_n : (stepPlacementCalibrated γ_num γ_den S k).n = n := by
      rw [stepPlacementCalibrated_n γ_num γ_den S k (h_succ k), ← hk_eq]
    have h_rot : (stepPlacementCalibrated γ_num γ_den S k).rotated = true :=
      stepPlacementCalibrated_rotated γ_num γ_den S k (h_succ k)
    have h_t : (iteratedCalibrated γ_num γ_den k S).t = n := by
      rw [iteratedCalibrated_t γ_num γ_den S k (h_succ k), ← hk_eq]
    -- LRP iteration invariants.
    have h_lrp_x1 : (iteratedCalibrated γ_num γ_den k S).LRP.x1 = S.LRP.x1 :=
      iteratedCalibrated_LRP_x1 γ_num γ_den S k (h_succ k)
    have h_lrp_y1 : (iteratedCalibrated γ_num γ_den k S).LRP.y1 = S.LRP.y1 :=
      iteratedCalibrated_LRP_y1 γ_num γ_den S k (h_succ k)
    have h_lrp_x0_mono : S.LRP.x0 ≤ (iteratedCalibrated γ_num γ_den k S).LRP.x0 :=
      iteratedCalibrated_LRP_x0_mono γ_num γ_den S k (h_succ k)
    have h_lrp_y0_mono : S.LRP.y0 ≤ (iteratedCalibrated γ_num γ_den k S).LRP.y0 :=
      iteratedCalibrated_LRP_y0_mono γ_num γ_den S k (h_succ k)
    have h_step_k := h_steps k
    -- Cast helper for (n+1).
    have h_cast : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by push_cast; ring
    -- 1/(n+1) ≤ a_t ≤ S.LRP.x1 - (iteratedCalibrated k S).LRP.x0
    have h_xfit : (stepPlacementCalibrated γ_num γ_den S k).x0 + 1 / ((n : ℕ) + 1) ≤
        S.LRP.x1 := by
      rw [h_x0]
      have hx := h_step_k.1
      rw [h_t] at hx
      have h_w_le_a : (1 : ℚ) / ((n + 1 : ℕ) : ℕ) ≤
          calibratedStripeWidthRat γ_num γ_den n :=
        one_div_succ_le_calibratedStripeWidthRat γ_num γ_den n
      rw [h_lrp_x1] at hx
      have hx' : (1 : ℚ) / ((n : ℕ) + 1) ≤
          S.LRP.x1 - (iteratedCalibrated γ_num γ_den k S).LRP.x0 := by
        have h_eq : (1 : ℚ) / ((n : ℕ) + 1) = (1 : ℚ) / ((n + 1 : ℕ) : ℕ) := by
          push_cast; ring
        rw [h_eq]
        linarith
      linarith
    -- 1/n ≤ S.LRP.y1 - (iteratedCalibrated k S).LRP.y0
    have h_yfit : (stepPlacementCalibrated γ_num γ_den S k).y0 + 1 / (n : ℕ) ≤
        S.LRP.y1 := by
      rw [h_y0]
      have hy := h_step_k.2
      rw [h_t] at hy
      rw [h_lrp_y1] at hy
      linarith
    rw [h_extr']
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- container.x0 ≤ placement.x0
      have hc : S.container.x0 ≤ S.LRP.x0 := h_LRP_in_container.1
      show S.container.x0 ≤ (stepPlacementCalibrated γ_num γ_den S k).x0
      rw [h_x0]; linarith
    · -- placement.x1 ≤ container.x1
      have hc : S.LRP.x1 ≤ S.container.x1 := h_LRP_in_container.2.1
      show (stepPlacementCalibrated γ_num γ_den S k).x1 ≤ S.container.x1
      unfold PlacedRect.x1
      unfold PlacedRect.width
      rw [h_n, h_rot]
      simp only [hn_ne, ↓reduceIte]
      rw [h_cast]
      linarith
    · -- container.y0 ≤ placement.y0
      have hc : S.container.y0 ≤ S.LRP.y0 := h_LRP_in_container.2.2.1
      show S.container.y0 ≤ (stepPlacementCalibrated γ_num γ_den S k).y0
      rw [h_y0]; linarith
    · -- placement.y1 ≤ container.y1
      have hc : S.LRP.y1 ≤ S.container.y1 := h_LRP_in_container.2.2.2
      show (stepPlacementCalibrated γ_num γ_den S k).y1 ≤ S.container.y1
      unfold PlacedRect.y1
      unfold PlacedRect.height
      rw [h_n, h_rot]
      simp only [hn_ne, ↓reduceIte]
      linarith
  case disj =>
    -- pairwise disjoint within tail.
    intro m n hm hn hmn
    have hmn' : m < n ∨ n < m := lt_or_gt_of_ne hmn
    -- Asymmetric case: a < b, both ≥ S.t.
    have aux : ∀ {a b : ℕ}, S.t ≤ a → S.t ≤ b → a < b →
        Rect.interiorDisjoint
          (extractedPackingCalibrated γ_num γ_den S a).toRect
          (extractedPackingCalibrated γ_num γ_den S b).toRect := by
      intro a b ha hb hab
      have ha_extr : extractedPackingCalibrated γ_num γ_den S a =
          stepPlacementCalibrated γ_num γ_den S (a - S.t) := h_extr a ha
      have hb_extr : extractedPackingCalibrated γ_num γ_den S b =
          stepPlacementCalibrated γ_num γ_den S (b - S.t) := h_extr b hb
      set j := a - S.t with hj_def
      set k := b - S.t with hk_def
      have hjk : j < k := by omega
      have hjk1 : j + 1 ≤ k := hjk
      have ha_eq : a = S.t + j := by omega
      have hb_eq : b = S.t + k := by omega
      have ha_pos : 1 ≤ a := by omega
      have ha_ne : (a : ℕ) ≠ 0 := by omega
      -- placement j: corner (LRP_j.x0, LRP_j.y0), rotated
      have h_x0_j : (stepPlacementCalibrated γ_num γ_den S j).x0 =
          (iteratedCalibrated γ_num γ_den j S).LRP.x0 :=
        stepPlacementCalibrated_x0 γ_num γ_den S j (h_succ j)
      have h_y0_j : (stepPlacementCalibrated γ_num γ_den S j).y0 =
          (iteratedCalibrated γ_num γ_den j S).LRP.y0 :=
        stepPlacementCalibrated_y0 γ_num γ_den S j (h_succ j)
      have h_n_j : (stepPlacementCalibrated γ_num γ_den S j).n = a := by
        rw [stepPlacementCalibrated_n γ_num γ_den S j (h_succ j), ← ha_eq]
      have h_rot_j : (stepPlacementCalibrated γ_num γ_den S j).rotated = true :=
        stepPlacementCalibrated_rotated γ_num γ_den S j (h_succ j)
      have h_t_j : (iteratedCalibrated γ_num γ_den j S).t = a := by
        rw [iteratedCalibrated_t γ_num γ_den S j (h_succ j), ← ha_eq]
      have h_t_j_pos : 0 < (iteratedCalibrated γ_num γ_den j S).t := h_tk_pos j
      -- placement k:
      have h_x0_k : (stepPlacementCalibrated γ_num γ_den S k).x0 =
          (iteratedCalibrated γ_num γ_den k S).LRP.x0 :=
        stepPlacementCalibrated_x0 γ_num γ_den S k (h_succ k)
      have h_y0_k : (stepPlacementCalibrated γ_num γ_den S k).y0 =
          (iteratedCalibrated γ_num γ_den k S).LRP.y0 :=
        stepPlacementCalibrated_y0 γ_num γ_den S k (h_succ k)
      -- Monotonicity at step k (relative to step (j+1)).
      have h_mono_x : (iteratedCalibrated γ_num γ_den (j+1) S).LRP.x0 ≤
          (iteratedCalibrated γ_num γ_den k S).LRP.x0 :=
        iteratedCalibrated_LRP_x0_ge_step_j γ_num γ_den S k (h_succ k) (j+1) hjk1
      have h_mono_y : (iteratedCalibrated γ_num γ_den (j+1) S).LRP.y0 ≤
          (iteratedCalibrated γ_num γ_den k S).LRP.y0 :=
        iteratedCalibrated_LRP_y0_ge_step_j γ_num γ_den S k (h_succ k) (j+1) hjk1
      -- Case split on which axis advanced at step (j+1).
      have h_axis := iteratedCalibrated_step_advances_one_axis γ_num γ_den S j (h_succ j)
      rw [ha_extr, hb_extr]
      unfold Rect.interiorDisjoint
      have h_cast_a : ((a + 1 : ℕ) : ℚ) = (a : ℚ) + 1 := by push_cast; ring
      rcases h_axis with ⟨hxd, _⟩ | ⟨_, hyd⟩
      · -- x-cut at step (j+1):
        --   (iteratedCalibrated (j+1) S).LRP.x0
        --     = (iteratedCalibrated j S).LRP.x0
        --       + a_{t_j}.
        -- Placement j has width 1/(t_j+1) = 1/(a+1), so its x1
        --   = LRP_j.x0 + 1/(a+1) ≤ LRP_j.x0 + a_{t_j}
        --   = (iteratedCalibrated (j+1) S).LRP.x0 ≤ LRP_k.x0 = placement k.x0.
        left
        show (stepPlacementCalibrated γ_num γ_den S j).toRect.x1 ≤
             (stepPlacementCalibrated γ_num γ_den S k).toRect.x0
        have h_x1_j_eq : (stepPlacementCalibrated γ_num γ_den S j).toRect.x1 =
            (stepPlacementCalibrated γ_num γ_den S j).x1 := rfl
        have h_x0_k_eq : (stepPlacementCalibrated γ_num γ_den S k).toRect.x0 =
            (stepPlacementCalibrated γ_num γ_den S k).x0 := rfl
        rw [h_x1_j_eq, h_x0_k_eq, h_x0_k]
        unfold PlacedRect.x1
        unfold PlacedRect.width
        rw [h_n_j, h_rot_j]
        simp only [ha_ne, ↓reduceIte]
        rw [h_x0_j]
        -- Goal: LRP_j.x0 + 1/(a+1) ≤ LRP_k.x0
        -- Step 1: LRP_j.x0 + 1/(a+1) ≤ LRP_j.x0 + a_{t_j}
        --   by `one_div_succ_le_calibratedStripeWidthRat`.
        -- Step 2: LRP_j.x0 + a_{t_j} = (iteratedCalibrated (j+1) S).LRP.x0
        --   by `hxd` after rewriting `t_j = a`.
        -- Step 3: (iteratedCalibrated (j+1) S).LRP.x0 ≤ LRP_k.x0  by h_mono_x.
        have hxd' : (iteratedCalibrated γ_num γ_den (j+1) S).LRP.x0 =
            (iteratedCalibrated γ_num γ_den j S).LRP.x0 +
              calibratedStripeWidthRat γ_num γ_den a := by
          rw [hxd, h_t_j]
        have h_w_le_a : (1 : ℚ) / ((a + 1 : ℕ) : ℕ) ≤
            calibratedStripeWidthRat γ_num γ_den a :=
          one_div_succ_le_calibratedStripeWidthRat γ_num γ_den a
        have h_eq : (1 : ℚ) / ((a + 1 : ℕ) : ℕ) = (1 : ℚ) / ((a : ℕ) + 1) := by
          push_cast; ring
        rw [h_eq] at h_w_le_a
        rw [h_cast_a]
        linarith [h_mono_x, hxd', h_w_le_a]
      · -- y-cut at step (j+1):
        --   (iteratedCalibrated (j+1) S).LRP.y0
        --     = (iteratedCalibrated j S).LRP.y0 + a_{t_j}.
        -- Placement j has height 1/t_j = 1/a, so its y1 = LRP_j.y0 + 1/a
        --   ≤ LRP_j.y0 + a_{t_j}
        --   = (iteratedCalibrated (j+1) S).LRP.y0 ≤ LRP_k.y0 = placement k.y0.
        right; right; left
        show (stepPlacementCalibrated γ_num γ_den S j).toRect.y1 ≤
             (stepPlacementCalibrated γ_num γ_den S k).toRect.y0
        have h_y1_j_eq : (stepPlacementCalibrated γ_num γ_den S j).toRect.y1 =
            (stepPlacementCalibrated γ_num γ_den S j).y1 := rfl
        have h_y0_k_eq : (stepPlacementCalibrated γ_num γ_den S k).toRect.y0 =
            (stepPlacementCalibrated γ_num γ_den S k).y0 := rfl
        rw [h_y1_j_eq, h_y0_k_eq, h_y0_k]
        unfold PlacedRect.y1
        unfold PlacedRect.height
        rw [h_n_j, h_rot_j]
        simp only [ha_ne, ↓reduceIte]
        rw [h_y0_j]
        -- Goal: LRP_j.y0 + 1/a ≤ LRP_k.y0
        -- Use hyd to rewrite (iteratedCalibrated (j+1) S).LRP.y0
        --   = LRP_j.y0 + a_{t_j} (with t_j = a).
        -- Then 1/a ≤ a_{t_j} by `one_div_le_calibratedStripeWidthRat`.
        have hyd' : (iteratedCalibrated γ_num γ_den (j+1) S).LRP.y0 =
            (iteratedCalibrated γ_num γ_den j S).LRP.y0 +
              calibratedStripeWidthRat γ_num γ_den a := by
          rw [hyd, h_t_j]
        have h_a_pos : 0 < a := by omega
        have h_h_le_a : (1 : ℚ) / ((a : ℕ) : ℕ) ≤
            calibratedStripeWidthRat γ_num γ_den a :=
          one_div_le_calibratedStripeWidthRat γ_num γ_den a h_a_pos
        linarith [h_mono_y, hyd', h_h_le_a]
    rcases hmn' with hmn'' | hmn''
    · exact aux hm hn hmn''
    · exact Rect.interiorDisjoint_symm _ _ (aux hn hm hmn'')
  case avoid =>
    -- avoid: tail packings disjoint from S.placed.
    intro n hn P hP
    set k := n - S.t with hk_def
    have hk_eq : n = S.t + k := by omega
    have hn_pos : 1 ≤ n := by omega
    have hn_ne : (n : ℕ) ≠ 0 := by omega
    have h_extr' : extractedPackingCalibrated γ_num γ_den S n =
        stepPlacementCalibrated γ_num γ_den S k := h_extr n hn
    have h_x0 : (stepPlacementCalibrated γ_num γ_den S k).x0 =
        (iteratedCalibrated γ_num γ_den k S).LRP.x0 :=
      stepPlacementCalibrated_x0 γ_num γ_den S k (h_succ k)
    have h_y0 : (stepPlacementCalibrated γ_num γ_den S k).y0 =
        (iteratedCalibrated γ_num γ_den k S).LRP.y0 :=
      stepPlacementCalibrated_y0 γ_num γ_den S k (h_succ k)
    have h_n : (stepPlacementCalibrated γ_num γ_den S k).n = n := by
      rw [stepPlacementCalibrated_n γ_num γ_den S k (h_succ k), ← hk_eq]
    have h_rot : (stepPlacementCalibrated γ_num γ_den S k).rotated = true :=
      stepPlacementCalibrated_rotated γ_num γ_den S k (h_succ k)
    have h_t : (iteratedCalibrated γ_num γ_den k S).t = n := by
      rw [iteratedCalibrated_t γ_num γ_den S k (h_succ k), ← hk_eq]
    have h_lrp_x1 : (iteratedCalibrated γ_num γ_den k S).LRP.x1 = S.LRP.x1 :=
      iteratedCalibrated_LRP_x1 γ_num γ_den S k (h_succ k)
    have h_lrp_y1 : (iteratedCalibrated γ_num γ_den k S).LRP.y1 = S.LRP.y1 :=
      iteratedCalibrated_LRP_y1 γ_num γ_den S k (h_succ k)
    have h_lrp_x0_mono : S.LRP.x0 ≤ (iteratedCalibrated γ_num γ_den k S).LRP.x0 :=
      iteratedCalibrated_LRP_x0_mono γ_num γ_den S k (h_succ k)
    have h_lrp_y0_mono : S.LRP.y0 ≤ (iteratedCalibrated γ_num γ_den k S).LRP.y0 :=
      iteratedCalibrated_LRP_y0_mono γ_num γ_den S k (h_succ k)
    -- placement is contained inside S.LRP.
    have h_step_k := h_steps k
    have h_cast : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by push_cast; ring
    have h_xfit : (stepPlacementCalibrated γ_num γ_den S k).x0 + 1 / ((n : ℕ) + 1) ≤
        S.LRP.x1 := by
      rw [h_x0]
      have hx := h_step_k.1
      rw [h_t] at hx
      have h_w_le_a : (1 : ℚ) / ((n + 1 : ℕ) : ℕ) ≤
          calibratedStripeWidthRat γ_num γ_den n :=
        one_div_succ_le_calibratedStripeWidthRat γ_num γ_den n
      rw [h_lrp_x1] at hx
      have hx' : (1 : ℚ) / ((n : ℕ) + 1) ≤
          S.LRP.x1 - (iteratedCalibrated γ_num γ_den k S).LRP.x0 := by
        have h_eq : (1 : ℚ) / ((n : ℕ) + 1) = (1 : ℚ) / ((n + 1 : ℕ) : ℕ) := by
          push_cast; ring
        rw [h_eq]
        linarith
      linarith
    have h_yfit : (stepPlacementCalibrated γ_num γ_den S k).y0 + 1 / (n : ℕ) ≤
        S.LRP.y1 := by
      rw [h_y0]
      have hy := h_step_k.2
      rw [h_t] at hy
      rw [h_lrp_y1] at hy
      linarith
    have hcontain_x0 : S.LRP.x0 ≤ (stepPlacementCalibrated γ_num γ_den S k).x0 := by
      rw [h_x0]; exact h_lrp_x0_mono
    have hcontain_y0 : S.LRP.y0 ≤ (stepPlacementCalibrated γ_num γ_den S k).y0 := by
      rw [h_y0]; exact h_lrp_y0_mono
    -- placement geometry.
    have h_p_x1 : (stepPlacementCalibrated γ_num γ_den S k).toRect.x1 =
        (stepPlacementCalibrated γ_num γ_den S k).x0 + 1 / ((n : ℕ) + 1) := by
      show (stepPlacementCalibrated γ_num γ_den S k).x1 = _
      unfold PlacedRect.x1 PlacedRect.width
      rw [h_n, h_rot]
      simp [hn_ne, h_cast]
    have h_p_y1 : (stepPlacementCalibrated γ_num γ_den S k).toRect.y1 =
        (stepPlacementCalibrated γ_num γ_den S k).y0 + 1 / (n : ℕ) := by
      show (stepPlacementCalibrated γ_num γ_den S k).y1 = _
      unfold PlacedRect.y1 PlacedRect.height
      rw [h_n, h_rot]
      simp [hn_ne]
    have h_p_x0 : (stepPlacementCalibrated γ_num γ_den S k).toRect.x0 =
        (stepPlacementCalibrated γ_num γ_den S k).x0 := rfl
    have h_p_y0 : (stepPlacementCalibrated γ_num γ_den S k).toRect.y0 =
        (stepPlacementCalibrated γ_num γ_den S k).y0 := rfl
    have h_disj_LRP_P : Rect.interiorDisjoint S.LRP P.toRect := h_LRP_disj P hP
    rw [h_extr']
    unfold Rect.interiorDisjoint
    rcases h_disj_LRP_P with h | h | h | h
    · -- S.LRP.x1 ≤ P.x0 ⇒ placement.x1 ≤ S.LRP.x1 ≤ P.x0
      left
      rw [h_p_x1]
      linarith
    · -- P.x1 ≤ S.LRP.x0 ⇒ P.x1 ≤ S.LRP.x0 ≤ placement.x0
      right; left
      rw [h_p_x0]
      linarith
    · -- S.LRP.y1 ≤ P.y0 ⇒ placement.y1 ≤ S.LRP.y1 ≤ P.y0
      right; right; left
      rw [h_p_y1]
      linarith
    · -- P.y1 ≤ S.LRP.y0 ≤ placement.y0
      right; right; right
      rw [h_p_y0]
      linarith

end MeirMoser.CalibratedStripeTailProof
