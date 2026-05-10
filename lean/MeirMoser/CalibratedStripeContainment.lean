/-
  CalibratedStripeContainment.lean (Route A.5 Task A5.5):
  Geometric containment / disjointness lemmas for the CALIBRATED step.

  Mirrors `SchedulerInductionBalancedContainment.lean` for the calibrated
  balanced step (`calibratedBalancedStep`), where the stripe length on the
  longer side of the LRP is `a_t = 1/(t+1) + extraSlack ≥ 1/(t+1)` instead of
  the simpler `1/(t+1)`. Placement geometry of the rotated D_t (width
  `1/(t+1)`, height `1/t`) is identical, so the placement-disjointness
  arguments mirror exactly; the LRP-shrink uses the larger `a_t` cut.

  Lemmas:
    1. `calibratedBalancedStep_t_pos`             : positivity of t propagates.
    2. `iteratedCalibrated_t_pos`                 : iterated version.
    3. `calibratedBalancedStep_LRP_in_container`  : new LRP ⊆ container.
    4. `iteratedCalibrated_LRP_in_container`      : iterated version.
    5. `calibratedBalancedStep_LRP_in_old_LRP`    : new LRP ⊆ old LRP.
    6. `calibratedBalancedStep_LRP_disj_new_placement`
                                                  : new LRP ⟂ new placement.
    7. `calibratedBalancedStep_LRP_disj_old_placed`
                                                  : new LRP ⟂ old placements.
    8. `calibratedBalancedStep_LRP_disj_from_placed`
                                                  : new LRP ⟂ all new placements.
    9. `iteratedCalibrated_LRP_disj_from_placed`  : iterated version.
   10. `calibratedBalancedStep_FP`                : FinitePacking propagation.
   11. `iteratedCalibrated_FP`                    : iterated version.
   12. `iteratedCalibrated_FP_next`               : "next-step" form.

  Helpers `interiorDisjoint_of_contains_left`, `PairwiseDisjoint_singleton`,
  and `PairwiseDisjoint_append_singleton` are reused from
  `SchedulerInductionBalancedContainment.lean`.

  All lemmas are sorry-free.
-/
import MeirMoser.CalibratedStripe
import MeirMoser.SchedulerInductionBalancedContainment
import MeirMoser.FinitePacking
import Mathlib.Tactic

namespace MeirMoser

open List

/-- The calibrated balanced step preserves positivity of `t`.

    Since the step either advances `t` by 1 (when D_t fits) or leaves
    `t` unchanged, `0 < S.t` always implies `0 < (calibratedBalancedStep S).t`. -/
theorem calibratedBalancedStep_t_pos (γ_num γ_den : ℕ) (S : TailState)
    (h_t_pos : 0 < S.t)
    : 0 < (calibratedBalancedStep γ_num γ_den S).t := by
  unfold calibratedBalancedStep
  by_cases h : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0
  · rw [dif_pos h]
    by_cases hcut : cutFromX S = true
    · rw [dif_pos hcut]
      show 0 < S.t + 1
      omega
    · rw [dif_neg hcut]
      show 0 < S.t + 1
      omega
  · rw [dif_neg h]
    exact h_t_pos

/-- Iteration-level: `0 < S.t → ∀ k, 0 < (iteratedCalibrated k S).t`. -/
theorem iteratedCalibrated_t_pos (γ_num γ_den : ℕ) (S : TailState)
    (h_t_pos : 0 < S.t) (k : ℕ)
    : 0 < (iteratedCalibrated γ_num γ_den k S).t := by
  induction k with
  | zero => exact h_t_pos
  | succ k ih =>
    rw [iteratedCalibrated_succ]
    exact calibratedBalancedStep_t_pos γ_num γ_den _ ih

/-- The calibrated balanced step preserves containment of the LRP in the
    container. The new LRP is a sub-rectangle of the old LRP: we shrink either
    `x0 → x0 + a_t` (x-cut) or `y0 → y0 + a_t` (y-cut), and the container is
    unchanged. -/
theorem calibratedBalancedStep_LRP_in_container (γ_num γ_den : ℕ)
    (S : TailState) (hin : S.container.contains S.LRP) :
    (calibratedBalancedStep γ_num γ_den S).container.contains
      (calibratedBalancedStep γ_num γ_den S).LRP := by
  unfold calibratedBalancedStep
  by_cases h : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0
  · rw [dif_pos h]
    by_cases hcut : cutFromX S = true
    · rw [dif_pos hcut]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hwx : (0 : ℚ) ≤ calibratedStripeWidthRat γ_num γ_den S.t :=
          calibratedStripeWidthRat_nonneg γ_num γ_den S.t
        show S.container.x0 ≤ S.LRP.x0 + calibratedStripeWidthRat γ_num γ_den S.t
        linarith [hin.1]
      · exact hin.2.1
      · exact hin.2.2.1
      · exact hin.2.2.2
    · rw [dif_neg hcut]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hin.1
      · exact hin.2.1
      · have hwy : (0 : ℚ) ≤ calibratedStripeWidthRat γ_num γ_den S.t :=
          calibratedStripeWidthRat_nonneg γ_num γ_den S.t
        show S.container.y0 ≤ S.LRP.y0 + calibratedStripeWidthRat γ_num γ_den S.t
        linarith [hin.2.2.1]
      · exact hin.2.2.2
  · rw [dif_neg h]
    exact hin

/-- The new LRP after a successful calibrated balanced step is contained in
    the OLD LRP. -/
theorem calibratedBalancedStep_LRP_in_old_LRP (γ_num γ_den : ℕ) (S : TailState)
    (hcanFit : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    S.LRP.contains (calibratedBalancedStep γ_num γ_den S).LRP := by
  unfold calibratedBalancedStep
  rw [dif_pos hcanFit]
  by_cases hcut : cutFromX S = true
  · rw [dif_pos hcut]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : (0 : ℚ) ≤ calibratedStripeWidthRat γ_num γ_den S.t :=
        calibratedStripeWidthRat_nonneg γ_num γ_den S.t
      show S.LRP.x0 ≤ S.LRP.x0 + calibratedStripeWidthRat γ_num γ_den S.t
      linarith
    · exact le_refl _
    · exact le_refl _
    · exact le_refl _
  · rw [dif_neg hcut]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact le_refl _
    · exact le_refl _
    · have : (0 : ℚ) ≤ calibratedStripeWidthRat γ_num γ_den S.t :=
        calibratedStripeWidthRat_nonneg γ_num γ_den S.t
      show S.LRP.y0 ≤ S.LRP.y0 + calibratedStripeWidthRat γ_num γ_den S.t
      linarith
    · exact le_refl _

/-- The new LRP after a successful calibrated balanced step is interior-disjoint
    from the freshly placed rotated D_t.

    On the x-cut branch the new LRP starts at `S.LRP.x0 + a_t`, while the
    placement has width `1/(t+1) ≤ a_t` and starts at `S.LRP.x0`, so its x1 is
    at most the new LRP's x0 — interiors disjoint.

    On the y-cut branch the analogous identity holds on the y axis: placement
    height is `1/t ≤ a_t`. -/
theorem calibratedBalancedStep_LRP_disj_new_placement (γ_num γ_den : ℕ)
    (S : TailState)
    (hcanFit : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0)
    (h_t_pos : 0 < S.t) :
    Rect.interiorDisjoint (calibratedBalancedStep γ_num γ_den S).LRP
      ({ n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true } :
        PlacedRect).toRect := by
  unfold calibratedBalancedStep
  rw [dif_pos hcanFit]
  have h_n_ne : (S.t : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp h_t_pos
  by_cases hcut : cutFromX S = true
  · -- x-cut: new LRP.x0 = S.LRP.x0 + a_t, placement.x1 = S.LRP.x0 + 1/(t+1) ≤ new LRP.x0.
    rw [dif_pos hcut]
    -- pick `placement.x1 ≤ new_LRP.x0` (i.e. second disjunct).
    right; left
    -- placement.toRect.x1 = placement.x0 + placement.width
    show ({n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true} :
            PlacedRect).x1 ≤ S.LRP.x0 + calibratedStripeWidthRat γ_num γ_den S.t
    unfold PlacedRect.x1 PlacedRect.width
    simp only [h_n_ne, ↓reduceIte]
    -- Goal becomes: S.LRP.x0 + 1/(S.t + 1) ≤ S.LRP.x0 + a_t.
    have h_w_le_a : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤
        calibratedStripeWidthRat γ_num γ_den S.t :=
      one_div_succ_le_calibratedStripeWidthRat γ_num γ_den S.t
    linarith
  · -- y-cut: new LRP.y0 = S.LRP.y0 + a_t, placement.y1 = S.LRP.y0 + 1/t ≤ new LRP.y0.
    rw [dif_neg hcut]
    right; right; right
    -- placement.toRect.y1 ≤ new_LRP.y0
    show ({n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true} :
            PlacedRect).y1 ≤ S.LRP.y0 + calibratedStripeWidthRat γ_num γ_den S.t
    unfold PlacedRect.y1 PlacedRect.height
    simp only [h_n_ne, ↓reduceIte]
    -- Goal becomes: S.LRP.y0 + 1/S.t ≤ S.LRP.y0 + a_t.
    have h_h_le_a : (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤
        calibratedStripeWidthRat γ_num γ_den S.t :=
      one_div_le_calibratedStripeWidthRat γ_num γ_den S.t h_t_pos
    linarith

/-- The new LRP is interior-disjoint from every placement in `S.placed`,
    given that the OLD LRP is interior-disjoint from each. -/
theorem calibratedBalancedStep_LRP_disj_old_placed
    (γ_num γ_den : ℕ) (S : TailState)
    (hcanFit : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0)
    (h_disj : ∀ P ∈ S.placed, Rect.interiorDisjoint S.LRP P.toRect) :
    ∀ P ∈ S.placed, Rect.interiorDisjoint
      (calibratedBalancedStep γ_num γ_den S).LRP P.toRect := by
  intro P hP
  have h_LRP_in : S.LRP.contains (calibratedBalancedStep γ_num γ_den S).LRP :=
    calibratedBalancedStep_LRP_in_old_LRP γ_num γ_den S hcanFit
  exact interiorDisjoint_of_contains_left h_LRP_in (h_disj P hP)

/-- After a successful calibrated balanced step the `placed` list gains the
    new rotated placement at the LRP corner. -/
theorem calibratedBalancedStep_placed_eq {γ_num γ_den : ℕ} {S : TailState}
    (h_step : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
              (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    (calibratedBalancedStep γ_num γ_den S).placed = S.placed ++
      [{ n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true }] := by
  unfold calibratedBalancedStep
  rw [dif_pos h_step]
  by_cases hcut : cutFromX S = true
  · rw [dif_pos hcut]
  · rw [dif_neg hcut]

/-- The new LRP is interior-disjoint from every placement in
    `(calibratedBalancedStep S).placed`. The new placed list is
    `S.placed ++ [new]`. -/
theorem calibratedBalancedStep_LRP_disj_from_placed
    (γ_num γ_den : ℕ) (S : TailState)
    (h_t_pos : 0 < S.t)
    (h_disj : ∀ P ∈ S.placed, Rect.interiorDisjoint S.LRP P.toRect) :
    ∀ P ∈ (calibratedBalancedStep γ_num γ_den S).placed,
      Rect.interiorDisjoint (calibratedBalancedStep γ_num γ_den S).LRP P.toRect := by
  intro P hP
  -- Case split on whether the step succeeded.
  by_cases h : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0
  · -- success branch: (calibratedBalancedStep S).placed = S.placed ++ [new].
    have h_eq := calibratedBalancedStep_placed_eq h
    rw [h_eq] at hP
    rcases List.mem_append.mp hP with hP_old | hP_new
    · -- P was already in S.placed → use the shrink lemma.
      exact calibratedBalancedStep_LRP_disj_old_placed γ_num γ_den S h h_disj P hP_old
    · -- P is the new placement → use the new-placement disjointness lemma.
      rw [List.mem_singleton] at hP_new
      rw [hP_new]
      exact calibratedBalancedStep_LRP_disj_new_placement γ_num γ_den S h h_t_pos
  · -- failure branch: calibratedBalancedStep S = S; LRP unchanged.
    have h_step_eq : calibratedBalancedStep γ_num γ_den S = S := by
      unfold calibratedBalancedStep
      rw [dif_neg h]
    rw [h_step_eq]
    rw [h_step_eq] at hP
    exact h_disj P hP

/-! ## FinitePacking propagation

    Given the new disjointness lemma above, we can lift `FinitePacking` from
    `S.placed` to `(calibratedBalancedStep S).placed`. -/

/-- One calibrated balanced step preserves `FinitePacking`, given the standard
    "LRP interior-disjoint from existing placed" hypothesis. -/
theorem calibratedBalancedStep_FP
    (γ_num γ_den : ℕ) (S : TailState)
    (h_t_pos : 0 < S.t)
    (h_FP : FinitePacking S.container S.placed)
    (h_LRP_in : S.container.contains S.LRP)
    (h_disj : ∀ P ∈ S.placed, Rect.interiorDisjoint S.LRP P.toRect) :
    FinitePacking (calibratedBalancedStep γ_num γ_den S).container
      (calibratedBalancedStep γ_num γ_den S).placed := by
  rcases h_FP with ⟨h_in, h_dims, h_pair⟩
  -- Case split on whether the step succeeded.
  by_cases h : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0
  · have h_eq := calibratedBalancedStep_placed_eq h
    have h_cont_eq := calibratedBalancedStep_container γ_num γ_den S
    -- new placed = old placed ++ [new placement]
    set P_new : PlacedRect :=
      { n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true }
    refine ⟨?_, ?_, ?_⟩
    · -- AllInside (calibratedBalancedStep S).container (calibratedBalancedStep S).placed.
      rw [h_eq, h_cont_eq]
      intro P hP
      rcases List.mem_append.mp hP with hP_old | hP_new
      · exact h_in P hP_old
      · rw [List.mem_singleton] at hP_new
        rw [hP_new]
        -- New placement ⊆ S.LRP ⊆ S.container.
        unfold Rect.contains
        have h_n_ne : (S.t : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp h_t_pos
        rcases h_LRP_in with ⟨h_cx0, h_cx1, h_cy0, h_cy1⟩
        have h_pxw : (P_new).toRect.x0 = S.LRP.x0 := rfl
        have h_pyw : (P_new).toRect.y0 = S.LRP.y0 := rfl
        have h_px1 : (P_new).toRect.x1 = S.LRP.x0 + 1 / ((S.t : ℕ) + 1 : ℕ) := by
          unfold PlacedRect.toRect PlacedRect.x1 PlacedRect.width
          simp only [h_n_ne, ↓reduceIte]
        have h_py1 : (P_new).toRect.y1 = S.LRP.y0 + 1 / (S.t : ℕ) := by
          unfold PlacedRect.toRect PlacedRect.y1 PlacedRect.height
          simp only [h_n_ne, ↓reduceIte]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [h_pxw]; exact h_cx0
        · rw [h_px1]
          -- need: S.LRP.x0 + 1/(t+1) ≤ S.container.x1.
          have h_fit_x : calibratedStripeWidthRat γ_num γ_den S.t ≤
              S.LRP.x1 - S.LRP.x0 := h.1
          have h_w_le_a : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤
              calibratedStripeWidthRat γ_num γ_den S.t :=
            one_div_succ_le_calibratedStripeWidthRat γ_num γ_den S.t
          have h_cast : ((S.t + 1 : ℕ) : ℚ) = ((S.t : ℕ) + 1 : ℕ) := by push_cast; ring
          rw [h_cast] at h_w_le_a
          linarith
        · rw [h_pyw]; exact h_cy0
        · rw [h_py1]
          -- need: S.LRP.y0 + 1/t ≤ S.container.y1.
          have h_fit_y : (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0 := h.2
          linarith
    · -- AllValidDims (calibratedBalancedStep S).placed.
      rw [h_eq]
      intro P hP
      rcases List.mem_append.mp hP with hP_old | hP_new
      · exact h_dims P hP_old
      · rw [List.mem_singleton] at hP_new
        rw [hP_new]
        unfold PlacedRect.validDims
        refine ⟨h_t_pos, ?_⟩
        have h_rot : (P_new).rotated = true := rfl
        rw [h_rot]
        simp only [↓reduceIte]
        have h_n_ne : (S.t : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp h_t_pos
        have h_n_eq : (P_new).n = S.t := rfl
        refine ⟨?_, ?_⟩
        · unfold PlacedRect.width
          rw [h_rot]
          rw [h_n_eq]
          simp [h_n_ne]
        · unfold PlacedRect.height
          rw [h_rot]
          rw [h_n_eq]
          simp [h_n_ne]
    · -- PairwiseDisjoint (calibratedBalancedStep S).placed.
      rw [h_eq]
      apply PairwiseDisjoint_append_singleton
      · exact h_pair
      · intro P hP
        -- We need: P interior-disjoint from new placement.
        have h_disjLRP : Rect.interiorDisjoint S.LRP P.toRect := h_disj P hP
        -- new placement.toRect ⊆ S.LRP.
        have h_new_in : S.LRP.contains (P_new).toRect := by
          unfold Rect.contains
          have h_n_ne : (S.t : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp h_t_pos
          have h_px0 : (P_new).toRect.x0 = S.LRP.x0 := rfl
          have h_py0 : (P_new).toRect.y0 = S.LRP.y0 := rfl
          have h_px1 : (P_new).toRect.x1 = S.LRP.x0 + 1 / ((S.t : ℕ) + 1 : ℕ) := by
            unfold PlacedRect.toRect PlacedRect.x1 PlacedRect.width
            simp only [h_n_ne, ↓reduceIte]
          have h_py1 : (P_new).toRect.y1 = S.LRP.y0 + 1 / (S.t : ℕ) := by
            unfold PlacedRect.toRect PlacedRect.y1 PlacedRect.height
            simp only [h_n_ne, ↓reduceIte]
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [h_px0]
          · rw [h_px1]
            have h_fit_x : calibratedStripeWidthRat γ_num γ_den S.t ≤
                S.LRP.x1 - S.LRP.x0 := h.1
            have h_w_le_a : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤
                calibratedStripeWidthRat γ_num γ_den S.t :=
              one_div_succ_le_calibratedStripeWidthRat γ_num γ_den S.t
            have h_cast : ((S.t + 1 : ℕ) : ℚ) = ((S.t : ℕ) + 1 : ℕ) := by
              push_cast; ring
            rw [h_cast] at h_w_le_a
            linarith
          · rw [h_py0]
          · rw [h_py1]
            have h_fit_y : (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0 := h.2
            linarith
        -- Apply interiorDisjoint_of_contains_left (with A = S.LRP, B = new).
        have h_disj_new : Rect.interiorDisjoint (P_new).toRect P.toRect :=
          interiorDisjoint_of_contains_left h_new_in h_disjLRP
        exact Rect.interiorDisjoint_symm _ _ h_disj_new
  · -- Failure branch: calibratedBalancedStep S = S, so FP holds vacuously.
    have h_step_eq : calibratedBalancedStep γ_num γ_den S = S := by
      unfold calibratedBalancedStep
      rw [dif_neg h]
    rw [h_step_eq]
    exact ⟨h_in, h_dims, h_pair⟩

/-! ## Iteration-level propagation -/

/-- Iterated containment: after k calibrated steps the LRP stays inside container. -/
theorem iteratedCalibrated_LRP_in_container
    (γ_num γ_den : ℕ) (S : TailState)
    (h_LRP_in : S.container.contains S.LRP)
    (k : ℕ) :
    (iteratedCalibrated γ_num γ_den k S).container.contains
      (iteratedCalibrated γ_num γ_den k S).LRP := by
  induction k with
  | zero => exact h_LRP_in
  | succ k ih =>
    rw [iteratedCalibrated_succ]
    exact calibratedBalancedStep_LRP_in_container γ_num γ_den _ ih

/-- Iterated disjointness: after k calibrated steps the LRP stays
    interior-disjoint from every placement. -/
theorem iteratedCalibrated_LRP_disj_from_placed
    (γ_num γ_den : ℕ) (S : TailState)
    (h_t_pos : 0 < S.t)
    (h_disj : ∀ P ∈ S.placed, Rect.interiorDisjoint S.LRP P.toRect)
    (k : ℕ) :
    ∀ P ∈ (iteratedCalibrated γ_num γ_den k S).placed,
      Rect.interiorDisjoint (iteratedCalibrated γ_num γ_den k S).LRP P.toRect := by
  induction k with
  | zero => exact h_disj
  | succ k ih =>
    have h_tk_pos : 0 < (iteratedCalibrated γ_num γ_den k S).t :=
      iteratedCalibrated_t_pos γ_num γ_den S h_t_pos k
    rw [iteratedCalibrated_succ]
    exact calibratedBalancedStep_LRP_disj_from_placed γ_num γ_den _ h_tk_pos ih

/-- Iterated FinitePacking: after k calibrated steps `placed` is still a
    valid finite packing.

    Hypotheses: `0 < S.t`, `S.LRP ⊆ S.container`, `S.LRP` interior-disjoint
    from each placement in `S.placed`, and `FinitePacking S.container S.placed`. -/
theorem iteratedCalibrated_FP
    (γ_num γ_den : ℕ) (S : TailState)
    (h_t_pos : 0 < S.t)
    (h_LRP_in : S.container.contains S.LRP)
    (h_disj : ∀ P ∈ S.placed, Rect.interiorDisjoint S.LRP P.toRect)
    (h_FP : FinitePacking S.container S.placed)
    (k : ℕ) :
    FinitePacking (iteratedCalibrated γ_num γ_den k S).container
      (iteratedCalibrated γ_num γ_den k S).placed := by
  induction k with
  | zero => exact h_FP
  | succ k ih =>
    have h_tk_pos : 0 < (iteratedCalibrated γ_num γ_den k S).t :=
      iteratedCalibrated_t_pos γ_num γ_den S h_t_pos k
    have h_LRP_in_k : (iteratedCalibrated γ_num γ_den k S).container.contains
        (iteratedCalibrated γ_num γ_den k S).LRP :=
      iteratedCalibrated_LRP_in_container γ_num γ_den S h_LRP_in k
    have h_disj_k : ∀ P ∈ (iteratedCalibrated γ_num γ_den k S).placed,
        Rect.interiorDisjoint (iteratedCalibrated γ_num γ_den k S).LRP P.toRect :=
      iteratedCalibrated_LRP_disj_from_placed γ_num γ_den S h_t_pos h_disj k
    rw [iteratedCalibrated_succ]
    exact calibratedBalancedStep_FP γ_num γ_den _ h_tk_pos ih h_LRP_in_k h_disj_k

/-- "Next-step" FinitePacking: the FinitePacking on
    `(iteratedCalibrated (k+1) S).placed`, which is
    `(calibratedBalancedStep (iteratedCalibrated k S)).placed`. -/
theorem iteratedCalibrated_FP_next
    (γ_num γ_den : ℕ) (S : TailState)
    (h_t_pos : 0 < S.t)
    (h_LRP_in : S.container.contains S.LRP)
    (h_disj : ∀ P ∈ S.placed, Rect.interiorDisjoint S.LRP P.toRect)
    (h_FP : FinitePacking S.container S.placed)
    (k : ℕ) :
    FinitePacking
      (calibratedBalancedStep γ_num γ_den (iteratedCalibrated γ_num γ_den k S)).container
      (calibratedBalancedStep γ_num γ_den (iteratedCalibrated γ_num γ_den k S)).placed := by
  have := iteratedCalibrated_FP γ_num γ_den S h_t_pos h_LRP_in h_disj h_FP (k+1)
  rw [iteratedCalibrated_succ] at this
  exact this

end MeirMoser
