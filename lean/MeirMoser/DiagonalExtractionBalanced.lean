/-
  DiagonalExtractionBalanced.lean (Route A R-A.7): from `iteratedBalanced` extract
  a function ℕ → PlacedRect that packs all D_n for n ≥ S.t into S.container.

  This file mirrors `DiagonalExtraction.lean` but adapted for the BALANCED step
  defined in `SchedulerInductionBalanced.lean`. The key difference from the
  simplified step is the case split on `cutFromX`:

    - On x-cut: LRP.x0 increases by 1/(t+1), LRP.y0 unchanged.
    - On y-cut: LRP.x0 unchanged,           LRP.y0 increases by 1/t.

  In both branches LRP.x1 and LRP.y1 are unchanged, and the placement is added
  at the corner (S.LRP.x0, S.LRP.y0) with rotated := true.

  The monotonicity lemmas track BOTH coordinates (x0 and y0) since either may
  increase on a given step.
-/
import MeirMoser.SchedulerInductionBalanced
import MeirMoser.WarmStart

namespace MeirMoser

/-- The list of placements added by `iteratedBalanced k S`. -/
noncomputable def iteratedBalanced_placed (S : TailState) : ℕ → List PlacedRect
  | 0 => S.placed
  | (k+1) => (iteratedBalanced (k+1) S).placed

/-- The placement added at step `k+1` of the balanced scheduler. -/
noncomputable def stepPlacementBalanced (S : TailState) (k : ℕ) : PlacedRect :=
  (iteratedBalanced (k+1) S).placed.getLastD ⟨0, 0, 0, false⟩

/-- The infinite extracted packing for the balanced scheduler.

    For n < S.t, returns a default placement (the prefix is handled separately).
    For n ≥ S.t, returns the placement made at step (n - S.t + 1).

    NB: relies on every balanced step succeeding (precondition of the
    `calibrated_tail_from_balanced_steps_success` theorem). -/
noncomputable def extractedPackingBalanced (S : TailState) : ℕ → PlacedRect := fun n =>
  if _ : n < S.t then
    ⟨n, 0, 0, false⟩
  else
    stepPlacementBalanced S (n - S.t)

/-- Per-step success predicate for the balanced step at iteration `j`. -/
abbrev BalancedStepFitsAt (S : TailState) (j : ℕ) : Prop :=
  (1 : ℚ) / (((iteratedBalanced j S).t + 1 : ℕ) : ℕ) ≤
      (iteratedBalanced j S).LRP.x1 - (iteratedBalanced j S).LRP.x0 ∧
  (1 : ℚ) / ((iteratedBalanced j S).t : ℕ) ≤
      (iteratedBalanced j S).LRP.y1 - (iteratedBalanced j S).LRP.y0

/-- After a successful balanced step the `t` index advances by 1. -/
theorem balancedStep_t_succ {S : TailState}
    (h_step : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
              (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    (balancedStep S).t = S.t + 1 := by
  unfold balancedStep
  rw [dif_pos h_step]
  by_cases hcut : cutFromX S
  · rw [if_pos hcut]
  · rw [if_neg hcut]

/-- After a successful balanced step the `placed` list gains the new rotated
    placement at the LRP corner. -/
theorem balancedStep_placed_eq {S : TailState}
    (h_step : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
              (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    (balancedStep S).placed = S.placed ++
      [{ n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true }] := by
  unfold balancedStep
  rw [dif_pos h_step]
  by_cases hcut : cutFromX S
  · rw [if_pos hcut]
  · rw [if_neg hcut]

/-- After a successful balanced step LRP.x0 either gains 1/(t+1) (x-cut) or is
    unchanged (y-cut). In both cases it is at least the original LRP.x0. -/
theorem balancedStep_LRP_x0_ge {S : TailState}
    (h_step : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
              (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    S.LRP.x0 ≤ (balancedStep S).LRP.x0 := by
  unfold balancedStep
  rw [dif_pos h_step]
  by_cases hcut : cutFromX S
  · rw [if_pos hcut]
    have hpos : (0 : ℚ) ≤ 1 / ((S.t + 1 : ℕ) : ℕ) := by positivity
    show S.LRP.x0 ≤ S.LRP.x0 + 1 / ((S.t + 1 : ℕ) : ℕ)
    linarith
  · rw [if_neg hcut]

/-- After a successful balanced step LRP.y0 either is unchanged (x-cut) or
    gains 1/t (y-cut). In both cases it is at least the original LRP.y0. -/
theorem balancedStep_LRP_y0_ge {S : TailState}
    (h_step : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
              (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    S.LRP.y0 ≤ (balancedStep S).LRP.y0 := by
  unfold balancedStep
  rw [dif_pos h_step]
  by_cases hcut : cutFromX S
  · rw [if_pos hcut]
  · rw [if_neg hcut]
    have hpos : (0 : ℚ) ≤ 1 / (S.t : ℕ) := by positivity
    show S.LRP.y0 ≤ S.LRP.y0 + 1 / (S.t : ℕ)
    linarith

/-- After a successful balanced step LRP.x1 is unchanged. -/
theorem balancedStep_LRP_x1 {S : TailState}
    (h_step : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
              (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    (balancedStep S).LRP.x1 = S.LRP.x1 := by
  unfold balancedStep
  rw [dif_pos h_step]
  by_cases hcut : cutFromX S
  · rw [if_pos hcut]
  · rw [if_neg hcut]

/-- After a successful balanced step LRP.y1 is unchanged. -/
theorem balancedStep_LRP_y1 {S : TailState}
    (h_step : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
              (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    (balancedStep S).LRP.y1 = S.LRP.y1 := by
  unfold balancedStep
  rw [dif_pos h_step]
  by_cases hcut : cutFromX S
  · rw [if_pos hcut]
  · rw [if_neg hcut]

/-- The container is preserved across all balanced iterations. -/
theorem iteratedBalanced_container (S : TailState) (k : ℕ) :
    (iteratedBalanced k S).container = S.container := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [iteratedBalanced_succ]
      rw [balancedStep_container]
      exact ih

/-- The prefix size of `iteratedBalanced k S` is `S.placed.length + k`. -/
theorem iteratedBalanced_placed_length (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    : (iteratedBalanced k S).placed.length = S.placed.length + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have ih' := ih (fun j hj => h_succeeds j (Nat.le_succ_of_le hj))
      show (balancedStep (iteratedBalanced k S)).placed.length = S.placed.length + (k + 1)
      rw [balancedStep_placed_eq h_step_k]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- `t` after `k` successful balanced steps is `S.t + k`. -/
theorem iteratedBalanced_t (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    : (iteratedBalanced k S).t = S.t + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have ih' := ih (fun j hj => h_succeeds j (Nat.le_succ_of_le hj))
      rw [iteratedBalanced_succ, balancedStep_t_succ h_step_k, ih']
      omega

/-- After `k` successful balanced steps LRP.x1 is unchanged. -/
theorem iteratedBalanced_LRP_x1 (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    : (iteratedBalanced k S).LRP.x1 = S.LRP.x1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have ih' := ih (fun j hj => h_succeeds j (Nat.le_succ_of_le hj))
      rw [iteratedBalanced_succ, balancedStep_LRP_x1 h_step_k, ih']

/-- After `k` successful balanced steps LRP.y1 is unchanged. -/
theorem iteratedBalanced_LRP_y1 (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    : (iteratedBalanced k S).LRP.y1 = S.LRP.y1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have ih' := ih (fun j hj => h_succeeds j (Nat.le_succ_of_le hj))
      rw [iteratedBalanced_succ, balancedStep_LRP_y1 h_step_k, ih']

/-- The LRP.x0 grows monotonically across balanced steps (x-cut may bump it,
    y-cut leaves it unchanged). -/
theorem iteratedBalanced_LRP_x0_mono (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    : S.LRP.x0 ≤ (iteratedBalanced k S).LRP.x0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have ih' := ih (fun j hj => h_succeeds j (Nat.le_succ_of_le hj))
      rw [iteratedBalanced_succ]
      have h_mono : (iteratedBalanced k S).LRP.x0 ≤ (balancedStep (iteratedBalanced k S)).LRP.x0 :=
        balancedStep_LRP_x0_ge h_step_k
      linarith

/-- The LRP.y0 grows monotonically across balanced steps. -/
theorem iteratedBalanced_LRP_y0_mono (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    : S.LRP.y0 ≤ (iteratedBalanced k S).LRP.y0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have ih' := ih (fun j hj => h_succeeds j (Nat.le_succ_of_le hj))
      rw [iteratedBalanced_succ]
      have h_mono : (iteratedBalanced k S).LRP.y0 ≤ (balancedStep (iteratedBalanced k S)).LRP.y0 :=
        balancedStep_LRP_y0_ge h_step_k
      linarith

/-- After successful balanced step (k+1), LRP.x0 is at least LRP.x0 at step k. -/
theorem iteratedBalanced_LRP_x0_succ_ge (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    : (iteratedBalanced k S).LRP.x0 ≤ (iteratedBalanced (k+1) S).LRP.x0 := by
  have h_step_k := h_succeeds k (le_refl k)
  rw [iteratedBalanced_succ]
  exact balancedStep_LRP_x0_ge h_step_k

/-- After successful balanced step (k+1), LRP.y0 is at least LRP.y0 at step k. -/
theorem iteratedBalanced_LRP_y0_succ_ge (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    : (iteratedBalanced k S).LRP.y0 ≤ (iteratedBalanced (k+1) S).LRP.y0 := by
  have h_step_k := h_succeeds k (le_refl k)
  rw [iteratedBalanced_succ]
  exact balancedStep_LRP_y0_ge h_step_k

/-- For `j ≤ k`, the LRP.x0 at step k is at least the LRP.x0 at step j. -/
theorem iteratedBalanced_LRP_x0_ge_step_j (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    (j : ℕ) (hjk : j ≤ k)
    : (iteratedBalanced j S).LRP.x0 ≤ (iteratedBalanced k S).LRP.x0 := by
  induction k with
  | zero =>
    interval_cases j
    rfl
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have h_succeeds_k : ∀ j' ≤ k, BalancedStepFitsAt S j' :=
        fun j' hj' => h_succeeds j' (Nat.le_succ_of_le hj')
      by_cases hjk' : j ≤ k
      · have ih' := ih h_succeeds_k hjk'
        have h_mono : (iteratedBalanced k S).LRP.x0 ≤
            (balancedStep (iteratedBalanced k S)).LRP.x0 :=
          balancedStep_LRP_x0_ge h_step_k
        rw [iteratedBalanced_succ]
        linarith
      · push_neg at hjk'
        have hj_eq : j = k + 1 := by omega
        rw [hj_eq]

/-- For `j ≤ k`, the LRP.y0 at step k is at least the LRP.y0 at step j. -/
theorem iteratedBalanced_LRP_y0_ge_step_j (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    (j : ℕ) (hjk : j ≤ k)
    : (iteratedBalanced j S).LRP.y0 ≤ (iteratedBalanced k S).LRP.y0 := by
  induction k with
  | zero =>
    interval_cases j
    rfl
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have h_succeeds_k : ∀ j' ≤ k, BalancedStepFitsAt S j' :=
        fun j' hj' => h_succeeds j' (Nat.le_succ_of_le hj')
      by_cases hjk' : j ≤ k
      · have ih' := ih h_succeeds_k hjk'
        have h_mono : (iteratedBalanced k S).LRP.y0 ≤
            (balancedStep (iteratedBalanced k S)).LRP.y0 :=
          balancedStep_LRP_y0_ge h_step_k
        rw [iteratedBalanced_succ]
        linarith
      · push_neg at hjk'
        have hj_eq : j = k + 1 := by omega
        rw [hj_eq]

/-- The placement at iteration `k` has its `n`-index equal to
    `(iteratedBalanced k S).t`. -/
theorem stepPlacementBalanced_idx (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    : (stepPlacementBalanced S k).n = (iteratedBalanced k S).t := by
  have h_kk := h_succeeds k (le_refl k)
  unfold stepPlacementBalanced
  rw [iteratedBalanced_succ, balancedStep_placed_eq h_kk]
  simp only [List.getLastD_concat]

/-- The placement at iteration `k` has `x0 = (iteratedBalanced k S).LRP.x0`. -/
theorem stepPlacementBalanced_x0 (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    : (stepPlacementBalanced S k).x0 = (iteratedBalanced k S).LRP.x0 := by
  have h_kk := h_succeeds k (le_refl k)
  unfold stepPlacementBalanced
  rw [iteratedBalanced_succ, balancedStep_placed_eq h_kk]
  simp only [List.getLastD_concat]

/-- The placement at iteration `k` has `y0 = (iteratedBalanced k S).LRP.y0`. -/
theorem stepPlacementBalanced_y0 (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    : (stepPlacementBalanced S k).y0 = (iteratedBalanced k S).LRP.y0 := by
  have h_kk := h_succeeds k (le_refl k)
  unfold stepPlacementBalanced
  rw [iteratedBalanced_succ, balancedStep_placed_eq h_kk]
  simp only [List.getLastD_concat]

/-- The placement added by the balanced step is rotated. -/
theorem stepPlacementBalanced_rotated (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    : (stepPlacementBalanced S k).rotated = true := by
  have h_kk := h_succeeds k (le_refl k)
  unfold stepPlacementBalanced
  rw [iteratedBalanced_succ, balancedStep_placed_eq h_kk]
  simp only [List.getLastD_concat]

/-- The `n` index of the balanced placement at iteration `k`. -/
theorem stepPlacementBalanced_n (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    : (stepPlacementBalanced S k).n = S.t + k := by
  rw [stepPlacementBalanced_idx S k h_succeeds, iteratedBalanced_t S k h_succeeds]

/-- Width of the balanced placement (rotated): width = 1/(n+1). -/
theorem stepPlacementBalanced_width (S : TailState) (k : ℕ) (h_t_pos : 1 ≤ S.t)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    : (stepPlacementBalanced S k).width = 1 / ((S.t + k + 1 : ℕ) : ℕ) := by
  unfold PlacedRect.width
  rw [stepPlacementBalanced_n S k h_succeeds, stepPlacementBalanced_rotated S k h_succeeds]
  have hpos : S.t + k ≠ 0 := by omega
  simp [hpos]

/-- Height of the balanced placement (rotated): height = 1/n. -/
theorem stepPlacementBalanced_height (S : TailState) (k : ℕ) (h_t_pos : 1 ≤ S.t)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    : (stepPlacementBalanced S k).height = 1 / ((S.t + k : ℕ) : ℕ) := by
  unfold PlacedRect.height
  rw [stepPlacementBalanced_n S k h_succeeds, stepPlacementBalanced_rotated S k h_succeeds]
  have hpos : S.t + k ≠ 0 := by omega
  simp [hpos]

/-- After step (k+1), LRP.x0 either gains 1/(t+1) or is unchanged. We package
    this as a non-decreasing inequality (use `iteratedBalanced_LRP_x0_succ_ge`
    plus the per-step shift bound when needed). -/
theorem iteratedBalanced_LRP_x0_succ (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    : (iteratedBalanced (k+1) S).LRP.x0 = (iteratedBalanced k S).LRP.x0 ∨
      (iteratedBalanced (k+1) S).LRP.x0 =
        (iteratedBalanced k S).LRP.x0 + 1 / (((iteratedBalanced k S).t + 1 : ℕ) : ℕ) := by
  have h_step_k := h_succeeds k (le_refl k)
  rw [iteratedBalanced_succ]
  unfold balancedStep
  rw [dif_pos h_step_k]
  by_cases hcut : cutFromX (iteratedBalanced k S)
  · rw [if_pos hcut]
    right
    rfl
  · rw [if_neg hcut]
    left
    rfl

/-- After step (k+1), LRP.y0 either is unchanged or gains 1/t. -/
theorem iteratedBalanced_LRP_y0_succ (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    : (iteratedBalanced (k+1) S).LRP.y0 = (iteratedBalanced k S).LRP.y0 ∨
      (iteratedBalanced (k+1) S).LRP.y0 =
        (iteratedBalanced k S).LRP.y0 + 1 / ((iteratedBalanced k S).t : ℕ) := by
  have h_step_k := h_succeeds k (le_refl k)
  rw [iteratedBalanced_succ]
  unfold balancedStep
  rw [dif_pos h_step_k]
  by_cases hcut : cutFromX (iteratedBalanced k S)
  · rw [if_pos hcut]
    left
    rfl
  · rw [if_neg hcut]
    right
    rfl

/-- Convenience: at every successful step, the cut amount on the chosen side is
    at least the rotated D_t's footprint on that side. Specifically:
    after step (k+1), EITHER LRP.x0 grew by ≥ 1/(t+1), OR LRP.y0 grew by ≥ 1/t.
    This is the key step used in the disjointness proof: the placement's
    bounding box on at least one axis ends right at the new LRP corner. -/
theorem iteratedBalanced_step_advances_one_axis (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k, BalancedStepFitsAt S j)
    : ((iteratedBalanced (k+1) S).LRP.x0 =
         (iteratedBalanced k S).LRP.x0 + 1 / (((iteratedBalanced k S).t + 1 : ℕ) : ℕ)
       ∧ (iteratedBalanced (k+1) S).LRP.y0 = (iteratedBalanced k S).LRP.y0) ∨
      ((iteratedBalanced (k+1) S).LRP.x0 = (iteratedBalanced k S).LRP.x0
       ∧ (iteratedBalanced (k+1) S).LRP.y0 =
         (iteratedBalanced k S).LRP.y0 + 1 / ((iteratedBalanced k S).t : ℕ)) := by
  have h_step_k := h_succeeds k (le_refl k)
  rw [iteratedBalanced_succ]
  unfold balancedStep
  rw [dif_pos h_step_k]
  by_cases hcut : cutFromX (iteratedBalanced k S)
  · rw [if_pos hcut]
    left
    exact ⟨rfl, rfl⟩
  · rw [if_neg hcut]
    right
    exact ⟨rfl, rfl⟩

end MeirMoser
