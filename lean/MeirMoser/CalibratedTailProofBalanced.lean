/-
  CalibratedTailProofBalanced.lean (Route A R-A.7): the proof of the calibrated
  tail packing under the BALANCED step, composing per-step preservation
  (`SchedulerInductionBalanced` + helpers in `DiagonalExtractionBalanced`) into
  the full infinite packing.

  Mirrors `CalibratedTailProof.lean` (the simplified-step version) but adapted
  for the balanced step:
    - rotated D_t with width 1/(t+1), height 1/t,
    - case split on `cutFromX S` for which axis advances each step.

  Output: `calibrated_tail_from_balanced_steps_success`, conditional on
  `AllStepsSucceed_balanced S` plus three explicit geometric preconditions
  (`S.t ≥ 1`, `S.LRP ⊆ S.container`, `S.LRP` interior-disjoint from every
  placement in `S.placed`).
-/
import MeirMoser.SchedulerInductionBalanced
import MeirMoser.DiagonalExtractionBalanced
import MeirMoser.WarmStart

namespace MeirMoser.CalibratedTailProofBalanced

open MeirMoser

/-- Hypothesis: the BALANCED scheduler succeeds at every iteration starting from S.
    The fit condition is `1/(t+1) ≤ width ∧ 1/t ≤ height` because rotated D_t
    has dimensions 1/(t+1) × 1/t. -/
def AllStepsSucceed_balanced (S : TailState) : Prop :=
  ∀ k : ℕ,
    (1 : ℚ) / (((iteratedBalanced k S).t + 1 : ℕ) : ℕ) ≤
        (iteratedBalanced k S).LRP.x1 - (iteratedBalanced k S).LRP.x0 ∧
    (1 : ℚ) / ((iteratedBalanced k S).t : ℕ) ≤
        (iteratedBalanced k S).LRP.y1 - (iteratedBalanced k S).LRP.y0

/-- Calibrated tail theorem (balanced version, proof shell).

    Assuming `AllStepsSucceed_balanced S`, plus `S.t ≥ 1`,
    `S.LRP ⊆ S.container`, and `S.LRP` interior-disjoint from every placement
    in `S.placed`, we get the full packing. -/
theorem calibrated_tail_from_balanced_steps_success
    (S : TailState) (h_steps : AllStepsSucceed_balanced S)
    (h_t_pos : 1 ≤ S.t)
    (h_LRP_in_container : S.container.contains S.LRP)
    (h_LRP_disj : ∀ P ∈ S.placed, Rect.interiorDisjoint S.LRP P.toRect)
    : MoserPacksFromAvoid S.t S.container S.placed := by
  -- Local abbreviation for the success predicate restricted to first (k+1) steps.
  have h_succ : ∀ k, ∀ j ≤ k, BalancedStepFitsAt S j :=
    fun k j _ => h_steps j
  -- Reusable helper: for n ≥ S.t, extractedPackingBalanced S n = stepPlacementBalanced S (n - S.t).
  have h_extr : ∀ n, S.t ≤ n →
      extractedPackingBalanced S n = stepPlacementBalanced S (n - S.t) := by
    intro n hn
    unfold extractedPackingBalanced
    rw [dif_neg (by omega : ¬ n < S.t)]
  -- Use extractedPackingBalanced S as the witness.
  refine ⟨extractedPackingBalanced S, ?dims, ?inside, ?disj, ?avoid⟩
  case dims =>
    -- dims: for n ≥ S.t, (extractedPackingBalanced S n).n = n and validDims (rotated branch).
    intro n hn
    set k := n - S.t with hk_def
    have hk_eq : n = S.t + k := by omega
    have hn_pos : 1 ≤ n := by omega
    have hn_ne : (n : ℕ) ≠ 0 := by omega
    have h_extr' : extractedPackingBalanced S n = stepPlacementBalanced S k := h_extr n hn
    have h_n : (stepPlacementBalanced S k).n = n := by
      rw [stepPlacementBalanced_n S k (h_succ k), ← hk_eq]
    have h_rot : (stepPlacementBalanced S k).rotated = true :=
      stepPlacementBalanced_rotated S k (h_succ k)
    refine ⟨?_, ?_⟩
    · -- (extractedPackingBalanced S n).n = n
      rw [h_extr', h_n]
    · -- (extractedPackingBalanced S n).validDims
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
    have h_extr' : extractedPackingBalanced S n = stepPlacementBalanced S k := h_extr n hn
    have h_x0 : (stepPlacementBalanced S k).x0 = (iteratedBalanced k S).LRP.x0 :=
      stepPlacementBalanced_x0 S k (h_succ k)
    have h_y0 : (stepPlacementBalanced S k).y0 = (iteratedBalanced k S).LRP.y0 :=
      stepPlacementBalanced_y0 S k (h_succ k)
    have h_n : (stepPlacementBalanced S k).n = n := by
      rw [stepPlacementBalanced_n S k (h_succ k), ← hk_eq]
    have h_rot : (stepPlacementBalanced S k).rotated = true :=
      stepPlacementBalanced_rotated S k (h_succ k)
    have h_t : (iteratedBalanced k S).t = n := by
      rw [iteratedBalanced_t S k (h_succ k), ← hk_eq]
    -- LRP iteration invariants.
    have h_lrp_x1 : (iteratedBalanced k S).LRP.x1 = S.LRP.x1 :=
      iteratedBalanced_LRP_x1 S k (h_succ k)
    have h_lrp_y1 : (iteratedBalanced k S).LRP.y1 = S.LRP.y1 :=
      iteratedBalanced_LRP_y1 S k (h_succ k)
    have h_lrp_x0_mono : S.LRP.x0 ≤ (iteratedBalanced k S).LRP.x0 :=
      iteratedBalanced_LRP_x0_mono S k (h_succ k)
    have h_lrp_y0_mono : S.LRP.y0 ≤ (iteratedBalanced k S).LRP.y0 :=
      iteratedBalanced_LRP_y0_mono S k (h_succ k)
    have h_step_k := h_steps k
    -- Cast helper for (n+1).
    have h_cast : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by push_cast; ring
    -- 1/(n+1) ≤ S.LRP.x1 - (iteratedBalanced k S).LRP.x0
    have h_xfit : (stepPlacementBalanced S k).x0 + 1 / ((n : ℕ) + 1) ≤ S.LRP.x1 := by
      rw [h_x0]
      have hx := h_step_k.1
      rw [h_t] at hx
      have hx' : (1 : ℚ) / ((n : ℕ) + 1) ≤
          (iteratedBalanced k S).LRP.x1 - (iteratedBalanced k S).LRP.x0 := by
        convert hx using 2
        push_cast
        ring
      rw [h_lrp_x1] at hx'
      linarith
    -- 1/n ≤ S.LRP.y1 - (iteratedBalanced k S).LRP.y0
    have h_yfit : (stepPlacementBalanced S k).y0 + 1 / (n : ℕ) ≤ S.LRP.y1 := by
      rw [h_y0]
      have hy := h_step_k.2
      rw [h_t] at hy
      rw [h_lrp_y1] at hy
      linarith
    rw [h_extr']
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- container.x0 ≤ placement.x0
      have hc : S.container.x0 ≤ S.LRP.x0 := h_LRP_in_container.1
      show S.container.x0 ≤ (stepPlacementBalanced S k).x0
      rw [h_x0]; linarith
    · -- placement.x1 ≤ container.x1
      have hc : S.LRP.x1 ≤ S.container.x1 := h_LRP_in_container.2.1
      show (stepPlacementBalanced S k).x1 ≤ S.container.x1
      unfold PlacedRect.x1
      unfold PlacedRect.width
      rw [h_n, h_rot]
      simp only [hn_ne, ↓reduceIte]
      rw [h_cast]
      linarith
    · -- container.y0 ≤ placement.y0
      have hc : S.container.y0 ≤ S.LRP.y0 := h_LRP_in_container.2.2.1
      show S.container.y0 ≤ (stepPlacementBalanced S k).y0
      rw [h_y0]; linarith
    · -- placement.y1 ≤ container.y1
      have hc : S.LRP.y1 ≤ S.container.y1 := h_LRP_in_container.2.2.2
      show (stepPlacementBalanced S k).y1 ≤ S.container.y1
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
          (extractedPackingBalanced S a).toRect
          (extractedPackingBalanced S b).toRect := by
      intro a b ha hb hab
      have ha_extr : extractedPackingBalanced S a = stepPlacementBalanced S (a - S.t) := h_extr a ha
      have hb_extr : extractedPackingBalanced S b = stepPlacementBalanced S (b - S.t) := h_extr b hb
      set j := a - S.t with hj_def
      set k := b - S.t with hk_def
      have hjk : j < k := by omega
      have hjk1 : j + 1 ≤ k := hjk
      have ha_eq : a = S.t + j := by omega
      have hb_eq : b = S.t + k := by omega
      have ha_pos : 1 ≤ a := by omega
      have ha_ne : (a : ℕ) ≠ 0 := by omega
      -- placement j: corner (LRP_j.x0, LRP_j.y0), rotated
      have h_x0_j : (stepPlacementBalanced S j).x0 = (iteratedBalanced j S).LRP.x0 :=
        stepPlacementBalanced_x0 S j (h_succ j)
      have h_y0_j : (stepPlacementBalanced S j).y0 = (iteratedBalanced j S).LRP.y0 :=
        stepPlacementBalanced_y0 S j (h_succ j)
      have h_n_j : (stepPlacementBalanced S j).n = a := by
        rw [stepPlacementBalanced_n S j (h_succ j), ← ha_eq]
      have h_rot_j : (stepPlacementBalanced S j).rotated = true :=
        stepPlacementBalanced_rotated S j (h_succ j)
      have h_t_j : (iteratedBalanced j S).t = a := by
        rw [iteratedBalanced_t S j (h_succ j), ← ha_eq]
      -- placement k:
      have h_x0_k : (stepPlacementBalanced S k).x0 = (iteratedBalanced k S).LRP.x0 :=
        stepPlacementBalanced_x0 S k (h_succ k)
      have h_y0_k : (stepPlacementBalanced S k).y0 = (iteratedBalanced k S).LRP.y0 :=
        stepPlacementBalanced_y0 S k (h_succ k)
      -- Monotonicity at step k (relative to step (j+1)).
      have h_mono_x : (iteratedBalanced (j+1) S).LRP.x0 ≤ (iteratedBalanced k S).LRP.x0 :=
        iteratedBalanced_LRP_x0_ge_step_j S k (h_succ k) (j+1) hjk1
      have h_mono_y : (iteratedBalanced (j+1) S).LRP.y0 ≤ (iteratedBalanced k S).LRP.y0 :=
        iteratedBalanced_LRP_y0_ge_step_j S k (h_succ k) (j+1) hjk1
      -- Case split on which axis advanced at step (j+1).
      have h_axis := iteratedBalanced_step_advances_one_axis S j (h_succ j)
      rw [ha_extr, hb_extr]
      unfold Rect.interiorDisjoint
      have h_cast_a : ((a + 1 : ℕ) : ℚ) = (a : ℚ) + 1 := by push_cast; ring
      rcases h_axis with ⟨hxd, _⟩ | ⟨_, hyd⟩
      · -- x-cut at step (j+1): (iteratedBalanced (j+1) S).LRP.x0
        --   = (iteratedBalanced j S).LRP.x0 + 1/(t_j+1).
        -- placement j has width 1/(t_j+1) = 1/(a+1), so its x1 = LRP_j.x0 + 1/(a+1)
        -- = (iteratedBalanced (j+1) S).LRP.x0 ≤ LRP_k.x0 = placement k.x0.
        left
        show (stepPlacementBalanced S j).toRect.x1 ≤ (stepPlacementBalanced S k).toRect.x0
        have h_x1_j_eq : (stepPlacementBalanced S j).toRect.x1 = (stepPlacementBalanced S j).x1 := rfl
        have h_x0_k_eq : (stepPlacementBalanced S k).toRect.x0 = (stepPlacementBalanced S k).x0 := rfl
        rw [h_x1_j_eq, h_x0_k_eq, h_x0_k]
        unfold PlacedRect.x1
        unfold PlacedRect.width
        rw [h_n_j, h_rot_j]
        simp only [ha_ne, ↓reduceIte]
        rw [h_x0_j]
        -- Need: (iteratedBalanced j S).LRP.x0 + 1/(a+1) ≤ (iteratedBalanced k S).LRP.x0
        -- Use hxd:
        --   (iteratedBalanced (j+1) S).LRP.x0
        --     = (iteratedBalanced j S).LRP.x0 + 1/((iteratedBalanced j S).t + 1)
        -- and h_t_j to rewrite to a.
        have hxd' : (iteratedBalanced (j+1) S).LRP.x0 =
            (iteratedBalanced j S).LRP.x0 + 1 / ((a : ℕ) + 1) := by
          rw [hxd]
          congr 2
          rw [h_t_j]
          push_cast
          ring
        rw [h_cast_a]
        linarith [h_mono_x, hxd']
      · -- y-cut at step (j+1): (iteratedBalanced (j+1) S).LRP.y0
        --   = (iteratedBalanced j S).LRP.y0 + 1/t_j.
        -- placement j has height 1/t_j = 1/a, so its y1 = LRP_j.y0 + 1/a
        -- = (iteratedBalanced (j+1) S).LRP.y0 ≤ LRP_k.y0 = placement k.y0.
        right; right; left
        show (stepPlacementBalanced S j).toRect.y1 ≤ (stepPlacementBalanced S k).toRect.y0
        have h_y1_j_eq : (stepPlacementBalanced S j).toRect.y1 = (stepPlacementBalanced S j).y1 := rfl
        have h_y0_k_eq : (stepPlacementBalanced S k).toRect.y0 = (stepPlacementBalanced S k).y0 := rfl
        rw [h_y1_j_eq, h_y0_k_eq, h_y0_k]
        unfold PlacedRect.y1
        unfold PlacedRect.height
        rw [h_n_j, h_rot_j]
        simp only [ha_ne, ↓reduceIte]
        rw [h_y0_j]
        -- Need: (iteratedBalanced j S).LRP.y0 + 1/a ≤ (iteratedBalanced k S).LRP.y0
        have hyd' : (iteratedBalanced (j+1) S).LRP.y0 =
            (iteratedBalanced j S).LRP.y0 + 1 / (a : ℕ) := by
          rw [hyd]
          congr 2
          rw [h_t_j]
        linarith [h_mono_y, hyd']
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
    have h_extr' : extractedPackingBalanced S n = stepPlacementBalanced S k := h_extr n hn
    have h_x0 : (stepPlacementBalanced S k).x0 = (iteratedBalanced k S).LRP.x0 :=
      stepPlacementBalanced_x0 S k (h_succ k)
    have h_y0 : (stepPlacementBalanced S k).y0 = (iteratedBalanced k S).LRP.y0 :=
      stepPlacementBalanced_y0 S k (h_succ k)
    have h_n : (stepPlacementBalanced S k).n = n := by
      rw [stepPlacementBalanced_n S k (h_succ k), ← hk_eq]
    have h_rot : (stepPlacementBalanced S k).rotated = true :=
      stepPlacementBalanced_rotated S k (h_succ k)
    have h_t : (iteratedBalanced k S).t = n := by
      rw [iteratedBalanced_t S k (h_succ k), ← hk_eq]
    have h_lrp_x1 : (iteratedBalanced k S).LRP.x1 = S.LRP.x1 :=
      iteratedBalanced_LRP_x1 S k (h_succ k)
    have h_lrp_y1 : (iteratedBalanced k S).LRP.y1 = S.LRP.y1 :=
      iteratedBalanced_LRP_y1 S k (h_succ k)
    have h_lrp_x0_mono : S.LRP.x0 ≤ (iteratedBalanced k S).LRP.x0 :=
      iteratedBalanced_LRP_x0_mono S k (h_succ k)
    have h_lrp_y0_mono : S.LRP.y0 ≤ (iteratedBalanced k S).LRP.y0 :=
      iteratedBalanced_LRP_y0_mono S k (h_succ k)
    -- placement is contained inside S.LRP.
    have h_step_k := h_steps k
    have h_cast : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by push_cast; ring
    have h_xfit : (stepPlacementBalanced S k).x0 + 1 / ((n : ℕ) + 1) ≤ S.LRP.x1 := by
      rw [h_x0]
      have hx := h_step_k.1
      rw [h_t] at hx
      have hx' : (1 : ℚ) / ((n : ℕ) + 1) ≤
          (iteratedBalanced k S).LRP.x1 - (iteratedBalanced k S).LRP.x0 := by
        convert hx using 2
        push_cast
        ring
      rw [h_lrp_x1] at hx'
      linarith
    have h_yfit : (stepPlacementBalanced S k).y0 + 1 / (n : ℕ) ≤ S.LRP.y1 := by
      rw [h_y0]
      have hy := h_step_k.2
      rw [h_t] at hy
      rw [h_lrp_y1] at hy
      linarith
    have hcontain_x0 : S.LRP.x0 ≤ (stepPlacementBalanced S k).x0 := by
      rw [h_x0]; exact h_lrp_x0_mono
    have hcontain_y0 : S.LRP.y0 ≤ (stepPlacementBalanced S k).y0 := by
      rw [h_y0]; exact h_lrp_y0_mono
    -- placement geometry.
    have h_p_x1 : (stepPlacementBalanced S k).toRect.x1 =
        (stepPlacementBalanced S k).x0 + 1 / ((n : ℕ) + 1) := by
      show (stepPlacementBalanced S k).x1 = _
      unfold PlacedRect.x1 PlacedRect.width
      rw [h_n, h_rot]
      simp [hn_ne, h_cast]
    have h_p_y1 : (stepPlacementBalanced S k).toRect.y1 =
        (stepPlacementBalanced S k).y0 + 1 / (n : ℕ) := by
      show (stepPlacementBalanced S k).y1 = _
      unfold PlacedRect.y1 PlacedRect.height
      rw [h_n, h_rot]
      simp [hn_ne]
    have h_p_x0 : (stepPlacementBalanced S k).toRect.x0 = (stepPlacementBalanced S k).x0 := rfl
    have h_p_y0 : (stepPlacementBalanced S k).toRect.y0 = (stepPlacementBalanced S k).y0 := rfl
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

end MeirMoser.CalibratedTailProofBalanced
