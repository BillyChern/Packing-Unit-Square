/-
  CalibratedStripeExtraction.lean (Route A.5 Task A5.10):
  Diagonal extraction helpers for the CALIBRATED step.

  Mirrors `DiagonalExtractionBalanced.lean` for the calibrated step.

  Key differences from the simplified balanced step:
    - On x-cut: LRP.x0 increases by `calibratedStripeWidthRat γ_num γ_den t`
      (which is `≥ 1/(t+1)`), LRP.y0 unchanged.
    - On y-cut: LRP.x0 unchanged, LRP.y0 increases by
      `calibratedStripeWidthRat γ_num γ_den t` (which is `≥ 1/t` for `t ≥ 1`).

  In both branches LRP.x1 and LRP.y1 are unchanged, and the placement is added
  at the corner `(S.LRP.x0, S.LRP.y0)` with `rotated := true`.

  The monotonicity lemmas track BOTH coordinates, since either may increase on
  a given step. The disjointness argument in `CalibratedStripeTailProof.lean`
  uses the bridge inequalities `1/(t+1) ≤ a_t` and `1/t ≤ a_t` (proved in
  `CalibratedStripe.lean`) to convert the `1/(t+1)` width / `1/t` height of
  the placement into the `a_t` LRP shift.
-/
import MeirMoser.CalibratedStripe
import MeirMoser.CalibratedStripeContainment
import MeirMoser.WarmStart

namespace MeirMoser

/-- The list of placements added by `iteratedCalibrated k S`. -/
noncomputable def iteratedCalibrated_placed (γ_num γ_den : ℕ) (S : TailState) :
    ℕ → List PlacedRect
  | 0 => S.placed
  | (k+1) => (iteratedCalibrated γ_num γ_den (k+1) S).placed

/-- The placement added at step `k+1` of the calibrated scheduler. -/
noncomputable def stepPlacementCalibrated (γ_num γ_den : ℕ) (S : TailState)
    (k : ℕ) : PlacedRect :=
  (iteratedCalibrated γ_num γ_den (k+1) S).placed.getLastD ⟨0, 0, 0, false⟩

/-- The infinite extracted packing for the calibrated scheduler.

    For `n < S.t`, returns a default placement (the prefix is handled separately).
    For `n ≥ S.t`, returns the placement made at step `(n - S.t + 1)`.

    NB: relies on every calibrated step succeeding (precondition of the
    `calibrated_tail_from_calibrated_steps_success` theorem). -/
noncomputable def extractedPackingCalibrated (γ_num γ_den : ℕ) (S : TailState) :
    ℕ → PlacedRect := fun n =>
  if _ : n < S.t then
    ⟨n, 0, 0, false⟩
  else
    stepPlacementCalibrated γ_num γ_den S (n - S.t)

/-- Per-step success predicate for the calibrated step at iteration `j`. -/
abbrev CalibratedStepFitsAt (γ_num γ_den : ℕ) (S : TailState) (j : ℕ) : Prop :=
  calibratedStripeWidthRat γ_num γ_den (iteratedCalibrated γ_num γ_den j S).t ≤
      (iteratedCalibrated γ_num γ_den j S).LRP.x1 -
      (iteratedCalibrated γ_num γ_den j S).LRP.x0 ∧
  (1 : ℚ) / ((iteratedCalibrated γ_num γ_den j S).t : ℕ) ≤
      (iteratedCalibrated γ_num γ_den j S).LRP.y1 -
      (iteratedCalibrated γ_num γ_den j S).LRP.y0

/-- After a successful calibrated step the `t` index advances by 1. -/
theorem calibratedBalancedStep_t_succ {γ_num γ_den : ℕ} {S : TailState}
    (h_step : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
              (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    (calibratedBalancedStep γ_num γ_den S).t = S.t + 1 := by
  unfold calibratedBalancedStep
  rw [dif_pos h_step]
  by_cases hcut : cutFromX S = true
  · rw [dif_pos hcut]
  · rw [dif_neg hcut]

/-- After a successful calibrated step LRP.x0 either gains `a_t` (x-cut) or is
    unchanged (y-cut). In both cases it is at least the original LRP.x0. -/
theorem calibratedBalancedStep_LRP_x0_ge {γ_num γ_den : ℕ} {S : TailState}
    (h_step : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
              (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    S.LRP.x0 ≤ (calibratedBalancedStep γ_num γ_den S).LRP.x0 := by
  unfold calibratedBalancedStep
  rw [dif_pos h_step]
  by_cases hcut : cutFromX S = true
  · rw [dif_pos hcut]
    have hpos : (0 : ℚ) ≤ calibratedStripeWidthRat γ_num γ_den S.t :=
      calibratedStripeWidthRat_nonneg γ_num γ_den S.t
    show S.LRP.x0 ≤ S.LRP.x0 + calibratedStripeWidthRat γ_num γ_den S.t
    linarith
  · rw [dif_neg hcut]

/-- After a successful calibrated step LRP.y0 either is unchanged (x-cut) or
    gains `a_t` (y-cut). In both cases it is at least the original LRP.y0. -/
theorem calibratedBalancedStep_LRP_y0_ge {γ_num γ_den : ℕ} {S : TailState}
    (h_step : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
              (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    S.LRP.y0 ≤ (calibratedBalancedStep γ_num γ_den S).LRP.y0 := by
  unfold calibratedBalancedStep
  rw [dif_pos h_step]
  by_cases hcut : cutFromX S = true
  · rw [dif_pos hcut]
  · rw [dif_neg hcut]
    have hpos : (0 : ℚ) ≤ calibratedStripeWidthRat γ_num γ_den S.t :=
      calibratedStripeWidthRat_nonneg γ_num γ_den S.t
    show S.LRP.y0 ≤ S.LRP.y0 + calibratedStripeWidthRat γ_num γ_den S.t
    linarith

/-- After a successful calibrated step LRP.x1 is unchanged. -/
theorem calibratedBalancedStep_LRP_x1 {γ_num γ_den : ℕ} {S : TailState}
    (h_step : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
              (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    (calibratedBalancedStep γ_num γ_den S).LRP.x1 = S.LRP.x1 := by
  unfold calibratedBalancedStep
  rw [dif_pos h_step]
  by_cases hcut : cutFromX S = true
  · rw [dif_pos hcut]
  · rw [dif_neg hcut]

/-- After a successful calibrated step LRP.y1 is unchanged. -/
theorem calibratedBalancedStep_LRP_y1 {γ_num γ_den : ℕ} {S : TailState}
    (h_step : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
              (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    (calibratedBalancedStep γ_num γ_den S).LRP.y1 = S.LRP.y1 := by
  unfold calibratedBalancedStep
  rw [dif_pos h_step]
  by_cases hcut : cutFromX S = true
  · rw [dif_pos hcut]
  · rw [dif_neg hcut]

/-- The container is preserved across all calibrated iterations. -/
theorem iteratedCalibrated_container (γ_num γ_den : ℕ) (S : TailState) (k : ℕ) :
    (iteratedCalibrated γ_num γ_den k S).container = S.container := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [iteratedCalibrated_succ]
      rw [calibratedBalancedStep_container]
      exact ih

/-- The prefix size of `iteratedCalibrated k S` is `S.placed.length + k`. -/
theorem iteratedCalibrated_placed_length (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j) :
    (iteratedCalibrated γ_num γ_den k S).placed.length = S.placed.length + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have ih' := ih (fun j hj => h_succeeds j (Nat.le_succ_of_le hj))
      show (calibratedBalancedStep γ_num γ_den (iteratedCalibrated γ_num γ_den k S)).placed.length
        = S.placed.length + (k + 1)
      rw [calibratedBalancedStep_placed_eq h_step_k]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- `t` after `k` successful calibrated steps is `S.t + k`. -/
theorem iteratedCalibrated_t (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j) :
    (iteratedCalibrated γ_num γ_den k S).t = S.t + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have ih' := ih (fun j hj => h_succeeds j (Nat.le_succ_of_le hj))
      rw [iteratedCalibrated_succ, calibratedBalancedStep_t_succ h_step_k, ih']
      omega

/-- After `k` successful calibrated steps LRP.x1 is unchanged. -/
theorem iteratedCalibrated_LRP_x1 (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j) :
    (iteratedCalibrated γ_num γ_den k S).LRP.x1 = S.LRP.x1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have ih' := ih (fun j hj => h_succeeds j (Nat.le_succ_of_le hj))
      rw [iteratedCalibrated_succ, calibratedBalancedStep_LRP_x1 h_step_k, ih']

/-- After `k` successful calibrated steps LRP.y1 is unchanged. -/
theorem iteratedCalibrated_LRP_y1 (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j) :
    (iteratedCalibrated γ_num γ_den k S).LRP.y1 = S.LRP.y1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have ih' := ih (fun j hj => h_succeeds j (Nat.le_succ_of_le hj))
      rw [iteratedCalibrated_succ, calibratedBalancedStep_LRP_y1 h_step_k, ih']

/-- The LRP.x0 grows monotonically across calibrated steps (x-cut may bump it,
    y-cut leaves it unchanged). -/
theorem iteratedCalibrated_LRP_x0_mono (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j) :
    S.LRP.x0 ≤ (iteratedCalibrated γ_num γ_den k S).LRP.x0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have ih' := ih (fun j hj => h_succeeds j (Nat.le_succ_of_le hj))
      rw [iteratedCalibrated_succ]
      have h_mono : (iteratedCalibrated γ_num γ_den k S).LRP.x0 ≤
          (calibratedBalancedStep γ_num γ_den (iteratedCalibrated γ_num γ_den k S)).LRP.x0 :=
        calibratedBalancedStep_LRP_x0_ge h_step_k
      linarith

/-- The LRP.y0 grows monotonically across calibrated steps. -/
theorem iteratedCalibrated_LRP_y0_mono (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j) :
    S.LRP.y0 ≤ (iteratedCalibrated γ_num γ_den k S).LRP.y0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have ih' := ih (fun j hj => h_succeeds j (Nat.le_succ_of_le hj))
      rw [iteratedCalibrated_succ]
      have h_mono : (iteratedCalibrated γ_num γ_den k S).LRP.y0 ≤
          (calibratedBalancedStep γ_num γ_den (iteratedCalibrated γ_num γ_den k S)).LRP.y0 :=
        calibratedBalancedStep_LRP_y0_ge h_step_k
      linarith

/-- After successful calibrated step (k+1), LRP.x0 is at least LRP.x0 at step k. -/
theorem iteratedCalibrated_LRP_x0_succ_ge (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j) :
    (iteratedCalibrated γ_num γ_den k S).LRP.x0 ≤
      (iteratedCalibrated γ_num γ_den (k+1) S).LRP.x0 := by
  have h_step_k := h_succeeds k (le_refl k)
  rw [iteratedCalibrated_succ]
  exact calibratedBalancedStep_LRP_x0_ge h_step_k

/-- After successful calibrated step (k+1), LRP.y0 is at least LRP.y0 at step k. -/
theorem iteratedCalibrated_LRP_y0_succ_ge (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j) :
    (iteratedCalibrated γ_num γ_den k S).LRP.y0 ≤
      (iteratedCalibrated γ_num γ_den (k+1) S).LRP.y0 := by
  have h_step_k := h_succeeds k (le_refl k)
  rw [iteratedCalibrated_succ]
  exact calibratedBalancedStep_LRP_y0_ge h_step_k

/-- For `j ≤ k`, the LRP.x0 at step k is at least the LRP.x0 at step j. -/
theorem iteratedCalibrated_LRP_x0_ge_step_j (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j)
    (j : ℕ) (hjk : j ≤ k) :
    (iteratedCalibrated γ_num γ_den j S).LRP.x0 ≤
      (iteratedCalibrated γ_num γ_den k S).LRP.x0 := by
  induction k with
  | zero =>
    interval_cases j
    rfl
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have h_succeeds_k : ∀ j' ≤ k, CalibratedStepFitsAt γ_num γ_den S j' :=
        fun j' hj' => h_succeeds j' (Nat.le_succ_of_le hj')
      by_cases hjk' : j ≤ k
      · have ih' := ih h_succeeds_k hjk'
        have h_mono : (iteratedCalibrated γ_num γ_den k S).LRP.x0 ≤
            (calibratedBalancedStep γ_num γ_den (iteratedCalibrated γ_num γ_den k S)).LRP.x0 :=
          calibratedBalancedStep_LRP_x0_ge h_step_k
        rw [iteratedCalibrated_succ]
        linarith
      · push_neg at hjk'
        have hj_eq : j = k + 1 := by omega
        rw [hj_eq]

/-- For `j ≤ k`, the LRP.y0 at step k is at least the LRP.y0 at step j. -/
theorem iteratedCalibrated_LRP_y0_ge_step_j (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j)
    (j : ℕ) (hjk : j ≤ k) :
    (iteratedCalibrated γ_num γ_den j S).LRP.y0 ≤
      (iteratedCalibrated γ_num γ_den k S).LRP.y0 := by
  induction k with
  | zero =>
    interval_cases j
    rfl
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have h_succeeds_k : ∀ j' ≤ k, CalibratedStepFitsAt γ_num γ_den S j' :=
        fun j' hj' => h_succeeds j' (Nat.le_succ_of_le hj')
      by_cases hjk' : j ≤ k
      · have ih' := ih h_succeeds_k hjk'
        have h_mono : (iteratedCalibrated γ_num γ_den k S).LRP.y0 ≤
            (calibratedBalancedStep γ_num γ_den (iteratedCalibrated γ_num γ_den k S)).LRP.y0 :=
          calibratedBalancedStep_LRP_y0_ge h_step_k
        rw [iteratedCalibrated_succ]
        linarith
      · push_neg at hjk'
        have hj_eq : j = k + 1 := by omega
        rw [hj_eq]

/-- The placement at iteration `k` has its `n`-index equal to
    `(iteratedCalibrated k S).t`. -/
theorem stepPlacementCalibrated_idx (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j) :
    (stepPlacementCalibrated γ_num γ_den S k).n = (iteratedCalibrated γ_num γ_den k S).t := by
  have h_kk := h_succeeds k (le_refl k)
  unfold stepPlacementCalibrated
  rw [iteratedCalibrated_succ, calibratedBalancedStep_placed_eq h_kk]
  simp only [List.getLastD_concat]

/-- The placement at iteration `k` has `x0 = (iteratedCalibrated k S).LRP.x0`. -/
theorem stepPlacementCalibrated_x0 (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j) :
    (stepPlacementCalibrated γ_num γ_den S k).x0 =
      (iteratedCalibrated γ_num γ_den k S).LRP.x0 := by
  have h_kk := h_succeeds k (le_refl k)
  unfold stepPlacementCalibrated
  rw [iteratedCalibrated_succ, calibratedBalancedStep_placed_eq h_kk]
  simp only [List.getLastD_concat]

/-- The placement at iteration `k` has `y0 = (iteratedCalibrated k S).LRP.y0`. -/
theorem stepPlacementCalibrated_y0 (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j) :
    (stepPlacementCalibrated γ_num γ_den S k).y0 =
      (iteratedCalibrated γ_num γ_den k S).LRP.y0 := by
  have h_kk := h_succeeds k (le_refl k)
  unfold stepPlacementCalibrated
  rw [iteratedCalibrated_succ, calibratedBalancedStep_placed_eq h_kk]
  simp only [List.getLastD_concat]

/-- The placement added by the calibrated step is rotated. -/
theorem stepPlacementCalibrated_rotated (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j) :
    (stepPlacementCalibrated γ_num γ_den S k).rotated = true := by
  have h_kk := h_succeeds k (le_refl k)
  unfold stepPlacementCalibrated
  rw [iteratedCalibrated_succ, calibratedBalancedStep_placed_eq h_kk]
  simp only [List.getLastD_concat]

/-- The `n` index of the calibrated placement at iteration `k`. -/
theorem stepPlacementCalibrated_n (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j) :
    (stepPlacementCalibrated γ_num γ_den S k).n = S.t + k := by
  rw [stepPlacementCalibrated_idx γ_num γ_den S k h_succeeds,
      iteratedCalibrated_t γ_num γ_den S k h_succeeds]

/-- Width of the calibrated placement (rotated): width = 1/(n+1). -/
theorem stepPlacementCalibrated_width (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_t_pos : 1 ≤ S.t)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j) :
    (stepPlacementCalibrated γ_num γ_den S k).width = 1 / ((S.t + k + 1 : ℕ) : ℕ) := by
  unfold PlacedRect.width
  rw [stepPlacementCalibrated_n γ_num γ_den S k h_succeeds,
      stepPlacementCalibrated_rotated γ_num γ_den S k h_succeeds]
  have hpos : S.t + k ≠ 0 := by omega
  simp [hpos]

/-- Height of the calibrated placement (rotated): height = 1/n. -/
theorem stepPlacementCalibrated_height (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_t_pos : 1 ≤ S.t)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j) :
    (stepPlacementCalibrated γ_num γ_den S k).height = 1 / ((S.t + k : ℕ) : ℕ) := by
  unfold PlacedRect.height
  rw [stepPlacementCalibrated_n γ_num γ_den S k h_succeeds,
      stepPlacementCalibrated_rotated γ_num γ_den S k h_succeeds]
  have hpos : S.t + k ≠ 0 := by omega
  simp [hpos]

/-- After step (k+1), LRP.x0 either gains `a_t` or is unchanged. -/
theorem iteratedCalibrated_LRP_x0_succ (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j) :
    (iteratedCalibrated γ_num γ_den (k+1) S).LRP.x0 =
        (iteratedCalibrated γ_num γ_den k S).LRP.x0 ∨
      (iteratedCalibrated γ_num γ_den (k+1) S).LRP.x0 =
        (iteratedCalibrated γ_num γ_den k S).LRP.x0 +
        calibratedStripeWidthRat γ_num γ_den (iteratedCalibrated γ_num γ_den k S).t := by
  have h_step_k := h_succeeds k (le_refl k)
  rw [iteratedCalibrated_succ]
  unfold calibratedBalancedStep
  rw [dif_pos h_step_k]
  by_cases hcut : cutFromX (iteratedCalibrated γ_num γ_den k S) = true
  · rw [dif_pos hcut]
    right
    rfl
  · rw [dif_neg hcut]
    left
    rfl

/-- After step (k+1), LRP.y0 either is unchanged or gains `a_t`. -/
theorem iteratedCalibrated_LRP_y0_succ (γ_num γ_den : ℕ) (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j) :
    (iteratedCalibrated γ_num γ_den (k+1) S).LRP.y0 =
        (iteratedCalibrated γ_num γ_den k S).LRP.y0 ∨
      (iteratedCalibrated γ_num γ_den (k+1) S).LRP.y0 =
        (iteratedCalibrated γ_num γ_den k S).LRP.y0 +
        calibratedStripeWidthRat γ_num γ_den (iteratedCalibrated γ_num γ_den k S).t := by
  have h_step_k := h_succeeds k (le_refl k)
  rw [iteratedCalibrated_succ]
  unfold calibratedBalancedStep
  rw [dif_pos h_step_k]
  by_cases hcut : cutFromX (iteratedCalibrated γ_num γ_den k S) = true
  · rw [dif_pos hcut]
    left
    rfl
  · rw [dif_neg hcut]
    right
    rfl

/-- At every successful step EITHER LRP.x0 grew by `a_t`, OR LRP.y0 grew by `a_t`.
    Used in the disjointness proof: the placement's bounding box on at least
    one axis ends right at (or before) the new LRP corner. -/
theorem iteratedCalibrated_step_advances_one_axis (γ_num γ_den : ℕ) (S : TailState)
    (k : ℕ) (h_succeeds : ∀ j ≤ k, CalibratedStepFitsAt γ_num γ_den S j) :
    ((iteratedCalibrated γ_num γ_den (k+1) S).LRP.x0 =
        (iteratedCalibrated γ_num γ_den k S).LRP.x0 +
        calibratedStripeWidthRat γ_num γ_den (iteratedCalibrated γ_num γ_den k S).t
       ∧ (iteratedCalibrated γ_num γ_den (k+1) S).LRP.y0 =
           (iteratedCalibrated γ_num γ_den k S).LRP.y0) ∨
      ((iteratedCalibrated γ_num γ_den (k+1) S).LRP.x0 =
           (iteratedCalibrated γ_num γ_den k S).LRP.x0
       ∧ (iteratedCalibrated γ_num γ_den (k+1) S).LRP.y0 =
           (iteratedCalibrated γ_num γ_den k S).LRP.y0 +
           calibratedStripeWidthRat γ_num γ_den (iteratedCalibrated γ_num γ_den k S).t) := by
  have h_step_k := h_succeeds k (le_refl k)
  rw [iteratedCalibrated_succ]
  unfold calibratedBalancedStep
  rw [dif_pos h_step_k]
  by_cases hcut : cutFromX (iteratedCalibrated γ_num γ_den k S) = true
  · rw [dif_pos hcut]
    left
    exact ⟨rfl, rfl⟩
  · rw [dif_neg hcut]
    right
    exact ⟨rfl, rfl⟩

end MeirMoser
