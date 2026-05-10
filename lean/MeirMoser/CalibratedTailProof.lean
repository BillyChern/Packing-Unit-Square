/-
  CalibratedTailProof.lean (A.5): the proof of `calibrated_tail_theorem`,
  composing per-step preservation (A.3) + diagonal extraction (A.4).

  This file gives a complete sorry-free proof of the calibrated tail packing
  under the assumption `AllStepsSucceed S` plus three explicit geometric
  preconditions (S.t ≥ 1, S.LRP ⊆ S.container, and S.LRP interior-disjoint
  from every placement in S.placed). Together with
  `good_state_implies_all_steps_succeed` (in CalibratedTailReduction.lean,
  currently an axiom that bundles the per-step preservation), this discharges
  the original `calibrated_tail_theorem` axiom.

  The theorem we want to prove (currently in WarmStart.lean as an axiom):
    GoodTailState ⇒ MoserPacksFromAvoid S.t S.container S.placed
-/
import MeirMoser.SchedulerInduction
import MeirMoser.DiagonalExtraction
import MeirMoser.WarmStart

namespace MeirMoser.CalibratedTailProof

open MeirMoser

/-- Hypothesis: the calibrated scheduler succeeds at every iteration starting from S. -/
def AllStepsSucceed (S : TailState) : Prop :=
  ∀ k : ℕ,
    (1 : ℚ) / ((iteratedStep k S).t : ℕ) ≤ (iteratedStep k S).LRP.x1 - (iteratedStep k S).LRP.x0 ∧
    (1 : ℚ) / (((iteratedStep k S).t + 1 : ℕ) : ℕ) ≤ (iteratedStep k S).LRP.y1 - (iteratedStep k S).LRP.y0

/-- Calibrated tail theorem (proof shell).

    Assuming `AllStepsSucceed S`, plus three basic geometric preconditions
    (`S.t ≥ 1`, `S.LRP ⊆ S.container`, `S.LRP` interior-disjoint from every
    placement in `S.placed`), we get the full packing. -/
theorem calibrated_tail_from_steps_success
    (S : TailState) (h_steps : AllStepsSucceed S)
    (h_t_pos : 1 ≤ S.t)
    (h_LRP_in_container : S.container.contains S.LRP)
    (h_LRP_disj : ∀ P ∈ S.placed, Rect.interiorDisjoint S.LRP P.toRect)
    : MoserPacksFromAvoid S.t S.container S.placed := by
  -- Local abbreviation for the success predicate restricted to first (k+1) steps.
  have h_succ : ∀ k, ∀ j ≤ k,
      (1 : ℚ) / ((iteratedStep j S).t : ℕ) ≤ (iteratedStep j S).LRP.x1 - (iteratedStep j S).LRP.x0 ∧
      (1 : ℚ) / (((iteratedStep j S).t + 1 : ℕ) : ℕ) ≤ (iteratedStep j S).LRP.y1 - (iteratedStep j S).LRP.y0 :=
    fun k j _ => h_steps j
  -- Extract a placement n ↦ stepPlacement S (n - S.t) for n ≥ S.t.
  -- Reusable helper: for n ≥ S.t, extractedPacking S n = stepPlacement S (n - S.t).
  have h_extr : ∀ n, S.t ≤ n →
      extractedPacking S n = stepPlacement S (n - S.t) := by
    intro n hn
    unfold extractedPacking
    rw [dif_neg (by omega : ¬ n < S.t)]
  -- Use extractedPacking S as the witness.
  refine ⟨extractedPacking S, ?dims, ?inside, ?disj, ?avoid⟩
  case dims =>
    -- dims: for n ≥ S.t, (extractedPacking S n).n = n and validDims.
    intro n hn
    set k := n - S.t with hk_def
    have hk_eq : n = S.t + k := by omega
    have hn_pos : 1 ≤ n := by omega
    have hn_ne : (n : ℕ) ≠ 0 := by omega
    have h_extr' : extractedPacking S n = stepPlacement S k := h_extr n hn
    have h_n : (stepPlacement S k).n = n := by
      rw [stepPlacement_n S k (h_succ k), ← hk_eq]
    have h_rot : (stepPlacement S k).rotated = false :=
      stepPlacement_rotated S k (h_succ k)
    refine ⟨?_, ?_⟩
    · -- (extractedPacking S n).n = n
      rw [h_extr', h_n]
    · -- (extractedPacking S n).validDims
      unfold PlacedRect.validDims
      rw [h_extr']
      refine ⟨?_, ?_⟩
      · rw [h_n]; exact hn_pos
      · rw [h_rot]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, ?_⟩
        · -- width = 1 / n
          unfold PlacedRect.width
          rw [h_n, h_rot]
          simp [hn_ne]
        · -- height = 1 / (n + 1)
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
    have h_extr' : extractedPacking S n = stepPlacement S k := h_extr n hn
    -- Geometric properties of stepPlacement S k.
    have h_x0 : (stepPlacement S k).x0 = (iteratedStep k S).LRP.x0 :=
      stepPlacement_x0 S k (h_succ k)
    have h_y0 : (stepPlacement S k).y0 = (iteratedStep k S).LRP.y0 :=
      stepPlacement_y0 S k (h_succ k)
    have h_n : (stepPlacement S k).n = n := by
      rw [stepPlacement_n S k (h_succ k), ← hk_eq]
    have h_rot : (stepPlacement S k).rotated = false :=
      stepPlacement_rotated S k (h_succ k)
    -- (iteratedStep k S).t = n.
    have h_t : (iteratedStep k S).t = n := by
      rw [iteratedStep_t S k (h_succ k), ← hk_eq]
    -- LRP iteration invariants.
    have h_lrp_y0 : (iteratedStep k S).LRP.y0 = S.LRP.y0 :=
      iteratedStep_LRP_y0 S k (h_succ k)
    have h_lrp_x1 : (iteratedStep k S).LRP.x1 = S.LRP.x1 :=
      iteratedStep_LRP_x1 S k (h_succ k)
    have h_lrp_y1 : (iteratedStep k S).LRP.y1 = S.LRP.y1 :=
      iteratedStep_LRP_y1 S k (h_succ k)
    have h_lrp_x0_mono : S.LRP.x0 ≤ (iteratedStep k S).LRP.x0 :=
      iteratedStep_LRP_x0_mono S k (h_succ k)
    -- Step success at j = k.
    have h_step_k := h_steps k
    -- 1/n ≤ S.LRP.x1 - (iteratedStep k S).LRP.x0
    have h_xfit : (stepPlacement S k).x0 + 1 / (n : ℕ) ≤ S.LRP.x1 := by
      rw [h_x0]
      have := h_step_k.1
      rw [h_t] at this
      linarith [h_lrp_x1]
    -- 1/(n+1) ≤ S.LRP.y1 - S.LRP.y0
    have h_yfit : (stepPlacement S k).y0 + 1 / ((n : ℕ) + 1) ≤ S.LRP.y1 := by
      rw [h_y0, h_lrp_y0]
      have := h_step_k.2
      rw [h_t] at this
      have : (1 : ℚ) / ((n : ℕ) + 1) ≤ (iteratedStep k S).LRP.y1 - (iteratedStep k S).LRP.y0 := by
        convert this using 2
        push_cast
        ring
      rw [h_lrp_y0, h_lrp_y1] at this
      linarith
    rw [h_extr']
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- container.x0 ≤ placement.x0
      have hc : S.container.x0 ≤ S.LRP.x0 := h_LRP_in_container.1
      show S.container.x0 ≤ (stepPlacement S k).x0
      rw [h_x0]; linarith
    · -- placement.x1 ≤ container.x1
      have hc : S.LRP.x1 ≤ S.container.x1 := h_LRP_in_container.2.1
      show (stepPlacement S k).x1 ≤ S.container.x1
      unfold PlacedRect.x1
      unfold PlacedRect.width
      rw [h_n, h_rot]
      simp only [hn_ne, ↓reduceIte, Bool.false_eq_true]
      linarith
    · -- container.y0 ≤ placement.y0
      have hc : S.container.y0 ≤ S.LRP.y0 := h_LRP_in_container.2.2.1
      show S.container.y0 ≤ (stepPlacement S k).y0
      rw [h_y0, h_lrp_y0]; linarith
    · -- placement.y1 ≤ container.y1
      have hc : S.LRP.y1 ≤ S.container.y1 := h_LRP_in_container.2.2.2
      show (stepPlacement S k).y1 ≤ S.container.y1
      unfold PlacedRect.y1
      unfold PlacedRect.height
      rw [h_n, h_rot]
      simp only [hn_ne, ↓reduceIte, Bool.false_eq_true]
      have h_cast : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by push_cast; ring
      rw [h_cast]
      linarith
  case disj =>
    -- pairwise disjoint within tail.
    intro m n hm hn hmn
    -- WLOG m < n; reduce to the asymmetric case
    have hmn' : m < n ∨ n < m := lt_or_gt_of_ne hmn
    -- We prove the "j < k" case where j = min - S.t, k = max - S.t.
    -- It suffices to show: for any j < k with both successful, the placements
    -- at iteration j and k are interior-disjoint via the right-strip argument.
    have aux : ∀ {a b : ℕ}, S.t ≤ a → S.t ≤ b → a < b →
        Rect.interiorDisjoint (extractedPacking S a).toRect (extractedPacking S b).toRect := by
      intro a b ha hb hab
      have ha_extr : extractedPacking S a = stepPlacement S (a - S.t) := h_extr a ha
      have hb_extr : extractedPacking S b = stepPlacement S (b - S.t) := h_extr b hb
      set j := a - S.t with hj_def
      set k := b - S.t with hk_def
      have hjk : j < k := by omega
      have ha_eq : a = S.t + j := by omega
      have hb_eq : b = S.t + k := by omega
      have ha_pos : 1 ≤ a := by omega
      have ha_ne : (a : ℕ) ≠ 0 := by omega
      -- placement j: x0 = (iteratedStep j S).LRP.x0, x1 = x0 + 1/a
      have h_x0_j : (stepPlacement S j).x0 = (iteratedStep j S).LRP.x0 :=
        stepPlacement_x0 S j (h_succ j)
      have h_n_j : (stepPlacement S j).n = a := by
        rw [stepPlacement_n S j (h_succ j), ← ha_eq]
      have h_rot_j : (stepPlacement S j).rotated = false :=
        stepPlacement_rotated S j (h_succ j)
      have h_t_j : (iteratedStep j S).t = a := by
        rw [iteratedStep_t S j (h_succ j), ← ha_eq]
      -- placement k: x0 = (iteratedStep k S).LRP.x0
      have h_x0_k : (stepPlacement S k).x0 = (iteratedStep k S).LRP.x0 :=
        stepPlacement_x0 S k (h_succ k)
      -- (iteratedStep (j+1) S).LRP.x0 = (iteratedStep j S).LRP.x0 + 1/a
      have h_lrp_step : (iteratedStep (j+1) S).LRP.x0 = (iteratedStep j S).LRP.x0 + 1 / ((a : ℕ) : ℕ) := by
        have := iteratedStep_LRP_x0_succ S j (h_succ j)
        rw [this, ← ha_eq]
      -- (iteratedStep (j+1) S).LRP.x0 ≤ (iteratedStep k S).LRP.x0
      have h_mono : (iteratedStep (j+1) S).LRP.x0 ≤ (iteratedStep k S).LRP.x0 := by
        have hjk1 : j + 1 ≤ k := hjk
        exact iteratedStep_LRP_x0_ge_step_j S k (h_succ k) (j+1) hjk1
      -- placement_j.x1 = (iteratedStep j S).LRP.x0 + 1/a = (iteratedStep (j+1) S).LRP.x0 ≤ placement_k.x0
      rw [ha_extr, hb_extr]
      unfold Rect.interiorDisjoint
      -- Goal: placement_j.x1 ≤ placement_k.x0 ∨ ...
      left
      show (stepPlacement S j).toRect.x1 ≤ (stepPlacement S k).toRect.x0
      have h_x1_j : (stepPlacement S j).toRect.x1 = (stepPlacement S j).x1 := rfl
      have h_x0_k_eq : (stepPlacement S k).toRect.x0 = (stepPlacement S k).x0 := rfl
      rw [h_x1_j, h_x0_k_eq, h_x0_k]
      -- Need: (stepPlacement S j).x1 ≤ (iteratedStep k S).LRP.x0
      unfold PlacedRect.x1
      unfold PlacedRect.width
      rw [h_n_j, h_rot_j]
      simp only [ha_ne, ↓reduceIte, Bool.false_eq_true]
      rw [h_x0_j]
      -- Now: (iteratedStep j S).LRP.x0 + 1 / a ≤ (iteratedStep k S).LRP.x0
      linarith [h_lrp_step, h_mono]
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
    have h_extr' : extractedPacking S n = stepPlacement S k := h_extr n hn
    -- Geometric properties of stepPlacement S k.
    have h_x0 : (stepPlacement S k).x0 = (iteratedStep k S).LRP.x0 :=
      stepPlacement_x0 S k (h_succ k)
    have h_y0 : (stepPlacement S k).y0 = (iteratedStep k S).LRP.y0 :=
      stepPlacement_y0 S k (h_succ k)
    have h_n : (stepPlacement S k).n = n := by
      rw [stepPlacement_n S k (h_succ k), ← hk_eq]
    have h_rot : (stepPlacement S k).rotated = false :=
      stepPlacement_rotated S k (h_succ k)
    have h_t : (iteratedStep k S).t = n := by
      rw [iteratedStep_t S k (h_succ k), ← hk_eq]
    have h_lrp_y0 : (iteratedStep k S).LRP.y0 = S.LRP.y0 :=
      iteratedStep_LRP_y0 S k (h_succ k)
    have h_lrp_x1 : (iteratedStep k S).LRP.x1 = S.LRP.x1 :=
      iteratedStep_LRP_x1 S k (h_succ k)
    have h_lrp_y1 : (iteratedStep k S).LRP.y1 = S.LRP.y1 :=
      iteratedStep_LRP_y1 S k (h_succ k)
    have h_lrp_x0_mono : S.LRP.x0 ≤ (iteratedStep k S).LRP.x0 :=
      iteratedStep_LRP_x0_mono S k (h_succ k)
    -- placement is contained inside S.LRP (in particular).
    have h_step_k := h_steps k
    have h_xfit : (stepPlacement S k).x0 + 1 / (n : ℕ) ≤ S.LRP.x1 := by
      rw [h_x0]
      have := h_step_k.1
      rw [h_t] at this
      linarith [h_lrp_x1]
    have h_yfit : (stepPlacement S k).y0 + 1 / ((n : ℕ) + 1) ≤ S.LRP.y1 := by
      rw [h_y0]
      have := h_step_k.2
      rw [h_t] at this
      have h_cast : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by push_cast; ring
      rw [← h_cast] at *
      rw [h_lrp_y1] at this
      linarith [iteratedStep_LRP_y0 S k (h_succ k)]
    have hcontain_x0 : S.LRP.x0 ≤ (stepPlacement S k).x0 := by rw [h_x0]; exact h_lrp_x0_mono
    have hcontain_y0 : S.LRP.y0 ≤ (stepPlacement S k).y0 := by
      rw [h_y0, h_lrp_y0]
    have hcontain_y0_eq : (stepPlacement S k).y0 = S.LRP.y0 := by rw [h_y0, h_lrp_y0]
    -- placement x1, y1 in terms of placement.x0 + width and y0 + height.
    have h_p_x1 : (stepPlacement S k).toRect.x1 = (stepPlacement S k).x0 + 1 / (n : ℕ) := by
      show (stepPlacement S k).x1 = _
      unfold PlacedRect.x1 PlacedRect.width
      rw [h_n, h_rot]
      simp [hn_ne]
    have h_p_y1 : (stepPlacement S k).toRect.y1 = (stepPlacement S k).y0 + 1 / ((n : ℕ) + 1) := by
      show (stepPlacement S k).y1 = _
      unfold PlacedRect.y1 PlacedRect.height
      rw [h_n, h_rot]
      have h_cast : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by push_cast; ring
      simp [hn_ne, h_cast]
    have h_p_x0 : (stepPlacement S k).toRect.x0 = (stepPlacement S k).x0 := rfl
    have h_p_y0 : (stepPlacement S k).toRect.y0 = (stepPlacement S k).y0 := rfl
    -- placement.x1 ≤ S.LRP.x1, placement.y1 ≤ S.LRP.y1, placement.x0 ≥ S.LRP.x0, placement.y0 = S.LRP.y0.
    have h_disj_LRP_P : Rect.interiorDisjoint S.LRP P.toRect := h_LRP_disj P hP
    rw [h_extr']
    unfold Rect.interiorDisjoint
    rcases h_disj_LRP_P with h | h | h | h
    · -- S.LRP.x1 ≤ P.x0 ⇒ placement.x1 ≤ S.LRP.x1 ≤ P.x0
      left
      rw [h_p_x1]
      linarith
    · -- P.x1 ≤ S.LRP.x0 ⇒ P.x1 ≤ S.LRP.x0 ≤ placement.x0 = placement.toRect.x0
      right; left
      rw [h_p_x0]
      linarith
    · -- S.LRP.y1 ≤ P.y0 ⇒ placement.y1 ≤ S.LRP.y1 ≤ P.y0
      right; right; left
      rw [h_p_y1]
      linarith
    · -- P.y1 ≤ S.LRP.y0 = placement.y0 = placement.toRect.y0
      right; right; right
      rw [h_p_y0, hcontain_y0_eq]
      linarith

end MeirMoser.CalibratedTailProof
