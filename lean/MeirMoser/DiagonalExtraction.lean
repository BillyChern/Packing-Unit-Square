/-
  DiagonalExtraction.lean (A.4): from `iteratedStep` extract a function
  ℕ → PlacedRect that packs all D_n for n ≥ S.t into S.container.

  The construction:
    extractedPacking S n :=
      if n < S.t then
        — placeholder; the prefix indices come from S.placed (handled by
        moser_packs_combine in MainTheorem).
        ⟨n, 0, 0, false⟩
      else
        — at iterated step (n - S.t), the placement added is exactly D_n.
        — we use `(iteratedStep (n - S.t + 1) S).placed.getLast`.
        ⟨n, 0, 0, false⟩  -- (placeholder — needs definition by induction on k)

  Pairwise disjointness follows because each step preserves disjointness of
  the "placed" list, and the new placement (LRP-corner cut) is disjoint from
  all earlier placements (it's strictly inside the LRP, which is the leftover).
-/
import MeirMoser.SchedulerInduction
import MeirMoser.WarmStart

namespace MeirMoser

/-- The list of placements added by `iteratedStep k S`. -/
noncomputable def iteratedStep_placed (S : TailState) : ℕ → List PlacedRect
  | 0 => S.placed
  | (k+1) => (iteratedStep (k+1) S).placed

/-- The placement added at step `k+1`: the difference between the placed lists. -/
noncomputable def stepPlacement (S : TailState) (k : ℕ) : PlacedRect :=
  (iteratedStep (k+1) S).placed.getLastD ⟨0, 0, 0, false⟩

/-- The infinite extracted packing as a function ℕ → PlacedRect.

    For n < S.t, returns a default placement (the prefix is handled separately).
    For n ≥ S.t, returns the placement made at step (n - S.t + 1).

    NB: this function depends on the assumption that the calibrated scheduler
    succeeds at every step, which is the contract of `calibrated_tail_theorem`.
    The current definition is structural; the proof of correctness (validDims,
    containment, disjointness) requires the per-step preservation lemmas. -/
noncomputable def extractedPacking (S : TailState) : ℕ → PlacedRect := fun n =>
  if h : n < S.t then
    -- Default for prefix indices; not used by `MoserPacksFrom S.t`.
    ⟨n, 0, 0, false⟩
  else
    stepPlacement S (n - S.t)

/-- Helper: at step k+1 of the simplified `calibratedStep`, the new placement
    has index `(iteratedStep k S).t`. This connects scheduler iterations to
    Moser indices. -/
theorem stepPlacement_idx (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k,
      (1 : ℚ) / ((iteratedStep j S).t : ℕ) ≤ (iteratedStep j S).LRP.x1 - (iteratedStep j S).LRP.x0 ∧
      (1 : ℚ) / (((iteratedStep j S).t + 1 : ℕ) : ℕ) ≤ (iteratedStep j S).LRP.y1 - (iteratedStep j S).LRP.y0)
    : (stepPlacement S k).n = (iteratedStep k S).t := by
  -- Unfold one step from `iteratedStep (k+1) S`, use the success branch of
  -- calibratedStep, then read off the last placement.
  have h_kk := h_succeeds k (le_refl k)
  unfold stepPlacement
  rw [iteratedStep_succ]
  unfold calibratedStep
  rw [dif_pos h_kk]
  -- After rewriting, the placed list is (iteratedStep k S).placed ++ [⟨(iteratedStep k S).t, ...⟩]
  simp only [List.getLastD_concat]

/-- The prefix size of `iteratedStep k S` is `S.placed.length + k` (when each step succeeds).

    This says the scheduler's `placed` list grows by exactly one element per
    successful step. -/
theorem iteratedStep_placed_length (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k,
      (1 : ℚ) / ((iteratedStep j S).t : ℕ) ≤ (iteratedStep j S).LRP.x1 - (iteratedStep j S).LRP.x0 ∧
      (1 : ℚ) / (((iteratedStep j S).t + 1 : ℕ) : ℕ) ≤ (iteratedStep j S).LRP.y1 - (iteratedStep j S).LRP.y0)
    : (iteratedStep k S).placed.length = S.placed.length + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have ih' := ih (fun j hj => h_succeeds j (Nat.le_succ_of_le hj))
      -- (iteratedStep (k+1) S).placed = (calibratedStep (iteratedStep k S)).placed
      -- = (iteratedStep k S).placed ++ [_]
      show (calibratedStep (iteratedStep k S)).placed.length = S.placed.length + (k + 1)
      unfold calibratedStep
      rw [dif_pos h_step_k]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- The container is preserved across all iterations. -/
theorem iteratedStep_container (S : TailState) (k : ℕ) :
    (iteratedStep k S).container = S.container := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [iteratedStep_succ]
      rw [calibratedStep_container]
      exact ih

/-- After a successful step the `t` index advances by 1. -/
theorem calibratedStep_t_succ {S : TailState}
    (h_step : (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
              (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    (calibratedStep S).t = S.t + 1 := by
  unfold calibratedStep
  rw [dif_pos h_step]

/-- After a successful step the `placed` list gains the new placement at the LRP corner. -/
theorem calibratedStep_placed_eq {S : TailState}
    (h_step : (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
              (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    (calibratedStep S).placed = S.placed ++
      [{ n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := false }] := by
  unfold calibratedStep
  rw [dif_pos h_step]

/-- After a successful step the LRP shifts right by `1/S.t`. -/
theorem calibratedStep_LRP_x0 {S : TailState}
    (h_step : (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
              (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    (calibratedStep S).LRP.x0 = S.LRP.x0 + 1 / (S.t : ℕ) := by
  unfold calibratedStep
  rw [dif_pos h_step]

/-- After a successful step LRP keeps its y0. -/
theorem calibratedStep_LRP_y0 {S : TailState}
    (h_step : (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
              (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    (calibratedStep S).LRP.y0 = S.LRP.y0 := by
  unfold calibratedStep
  rw [dif_pos h_step]

/-- After a successful step LRP keeps its x1. -/
theorem calibratedStep_LRP_x1 {S : TailState}
    (h_step : (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
              (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    (calibratedStep S).LRP.x1 = S.LRP.x1 := by
  unfold calibratedStep
  rw [dif_pos h_step]

/-- After a successful step LRP keeps its y1. -/
theorem calibratedStep_LRP_y1 {S : TailState}
    (h_step : (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
              (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    (calibratedStep S).LRP.y1 = S.LRP.y1 := by
  unfold calibratedStep
  rw [dif_pos h_step]

/-- `t` after k successful steps is `S.t + k`. -/
theorem iteratedStep_t (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k,
      (1 : ℚ) / ((iteratedStep j S).t : ℕ) ≤ (iteratedStep j S).LRP.x1 - (iteratedStep j S).LRP.x0 ∧
      (1 : ℚ) / (((iteratedStep j S).t + 1 : ℕ) : ℕ) ≤ (iteratedStep j S).LRP.y1 - (iteratedStep j S).LRP.y0)
    : (iteratedStep k S).t = S.t + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have ih' := ih (fun j hj => h_succeeds j (Nat.le_succ_of_le hj))
      rw [iteratedStep_succ, calibratedStep_t_succ h_step_k, ih']
      omega

/-- After k successful steps the LRP.y0 is unchanged. -/
theorem iteratedStep_LRP_y0 (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k,
      (1 : ℚ) / ((iteratedStep j S).t : ℕ) ≤ (iteratedStep j S).LRP.x1 - (iteratedStep j S).LRP.x0 ∧
      (1 : ℚ) / (((iteratedStep j S).t + 1 : ℕ) : ℕ) ≤ (iteratedStep j S).LRP.y1 - (iteratedStep j S).LRP.y0)
    : (iteratedStep k S).LRP.y0 = S.LRP.y0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have ih' := ih (fun j hj => h_succeeds j (Nat.le_succ_of_le hj))
      rw [iteratedStep_succ, calibratedStep_LRP_y0 h_step_k, ih']

/-- After k successful steps the LRP.x1 is unchanged. -/
theorem iteratedStep_LRP_x1 (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k,
      (1 : ℚ) / ((iteratedStep j S).t : ℕ) ≤ (iteratedStep j S).LRP.x1 - (iteratedStep j S).LRP.x0 ∧
      (1 : ℚ) / (((iteratedStep j S).t + 1 : ℕ) : ℕ) ≤ (iteratedStep j S).LRP.y1 - (iteratedStep j S).LRP.y0)
    : (iteratedStep k S).LRP.x1 = S.LRP.x1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have ih' := ih (fun j hj => h_succeeds j (Nat.le_succ_of_le hj))
      rw [iteratedStep_succ, calibratedStep_LRP_x1 h_step_k, ih']

/-- After k successful steps the LRP.y1 is unchanged. -/
theorem iteratedStep_LRP_y1 (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k,
      (1 : ℚ) / ((iteratedStep j S).t : ℕ) ≤ (iteratedStep j S).LRP.x1 - (iteratedStep j S).LRP.x0 ∧
      (1 : ℚ) / (((iteratedStep j S).t + 1 : ℕ) : ℕ) ≤ (iteratedStep j S).LRP.y1 - (iteratedStep j S).LRP.y0)
    : (iteratedStep k S).LRP.y1 = S.LRP.y1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have ih' := ih (fun j hj => h_succeeds j (Nat.le_succ_of_le hj))
      rw [iteratedStep_succ, calibratedStep_LRP_y1 h_step_k, ih']

/-- The LRP.x0 grows monotonically across steps (it only shifts right). -/
theorem iteratedStep_LRP_x0_mono (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k,
      (1 : ℚ) / ((iteratedStep j S).t : ℕ) ≤ (iteratedStep j S).LRP.x1 - (iteratedStep j S).LRP.x0 ∧
      (1 : ℚ) / (((iteratedStep j S).t + 1 : ℕ) : ℕ) ≤ (iteratedStep j S).LRP.y1 - (iteratedStep j S).LRP.y0)
    : S.LRP.x0 ≤ (iteratedStep k S).LRP.x0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have ih' := ih (fun j hj => h_succeeds j (Nat.le_succ_of_le hj))
      rw [iteratedStep_succ, calibratedStep_LRP_x0 h_step_k]
      have h_t_pos : (1 : ℚ) / ((iteratedStep k S).t : ℕ) ≥ 0 := by positivity
      linarith

/-- The stepPlacement at step k has its `x0` equal to (iteratedStep k S).LRP.x0. -/
theorem stepPlacement_x0 (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k,
      (1 : ℚ) / ((iteratedStep j S).t : ℕ) ≤ (iteratedStep j S).LRP.x1 - (iteratedStep j S).LRP.x0 ∧
      (1 : ℚ) / (((iteratedStep j S).t + 1 : ℕ) : ℕ) ≤ (iteratedStep j S).LRP.y1 - (iteratedStep j S).LRP.y0)
    : (stepPlacement S k).x0 = (iteratedStep k S).LRP.x0 := by
  have h_kk := h_succeeds k (le_refl k)
  unfold stepPlacement
  rw [iteratedStep_succ]
  unfold calibratedStep
  rw [dif_pos h_kk]
  simp only [List.getLastD_concat]

theorem stepPlacement_y0 (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k,
      (1 : ℚ) / ((iteratedStep j S).t : ℕ) ≤ (iteratedStep j S).LRP.x1 - (iteratedStep j S).LRP.x0 ∧
      (1 : ℚ) / (((iteratedStep j S).t + 1 : ℕ) : ℕ) ≤ (iteratedStep j S).LRP.y1 - (iteratedStep j S).LRP.y0)
    : (stepPlacement S k).y0 = (iteratedStep k S).LRP.y0 := by
  have h_kk := h_succeeds k (le_refl k)
  unfold stepPlacement
  rw [iteratedStep_succ]
  unfold calibratedStep
  rw [dif_pos h_kk]
  simp only [List.getLastD_concat]

theorem stepPlacement_rotated (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k,
      (1 : ℚ) / ((iteratedStep j S).t : ℕ) ≤ (iteratedStep j S).LRP.x1 - (iteratedStep j S).LRP.x0 ∧
      (1 : ℚ) / (((iteratedStep j S).t + 1 : ℕ) : ℕ) ≤ (iteratedStep j S).LRP.y1 - (iteratedStep j S).LRP.y0)
    : (stepPlacement S k).rotated = false := by
  have h_kk := h_succeeds k (le_refl k)
  unfold stepPlacement
  rw [iteratedStep_succ]
  unfold calibratedStep
  rw [dif_pos h_kk]
  simp only [List.getLastD_concat]

/-- The `t` index of stepPlacement S k. -/
theorem stepPlacement_n (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k,
      (1 : ℚ) / ((iteratedStep j S).t : ℕ) ≤ (iteratedStep j S).LRP.x1 - (iteratedStep j S).LRP.x0 ∧
      (1 : ℚ) / (((iteratedStep j S).t + 1 : ℕ) : ℕ) ≤ (iteratedStep j S).LRP.y1 - (iteratedStep j S).LRP.y0)
    : (stepPlacement S k).n = S.t + k := by
  rw [stepPlacement_idx S k h_succeeds, iteratedStep_t S k h_succeeds]

/-- The width of stepPlacement S k as a placed rect equals 1/(S.t + k). -/
theorem stepPlacement_width (S : TailState) (k : ℕ) (h_t_pos : 1 ≤ S.t)
    (h_succeeds : ∀ j ≤ k,
      (1 : ℚ) / ((iteratedStep j S).t : ℕ) ≤ (iteratedStep j S).LRP.x1 - (iteratedStep j S).LRP.x0 ∧
      (1 : ℚ) / (((iteratedStep j S).t + 1 : ℕ) : ℕ) ≤ (iteratedStep j S).LRP.y1 - (iteratedStep j S).LRP.y0)
    : (stepPlacement S k).width = 1 / ((S.t + k : ℕ) : ℕ) := by
  unfold PlacedRect.width
  rw [stepPlacement_n S k h_succeeds, stepPlacement_rotated S k h_succeeds]
  have hpos : S.t + k ≠ 0 := by omega
  simp [hpos]

/-- The height of stepPlacement S k as a placed rect equals 1/(S.t + k + 1). -/
theorem stepPlacement_height (S : TailState) (k : ℕ) (h_t_pos : 1 ≤ S.t)
    (h_succeeds : ∀ j ≤ k,
      (1 : ℚ) / ((iteratedStep j S).t : ℕ) ≤ (iteratedStep j S).LRP.x1 - (iteratedStep j S).LRP.x0 ∧
      (1 : ℚ) / (((iteratedStep j S).t + 1 : ℕ) : ℕ) ≤ (iteratedStep j S).LRP.y1 - (iteratedStep j S).LRP.y0)
    : (stepPlacement S k).height = 1 / ((S.t + k + 1 : ℕ) : ℕ) := by
  unfold PlacedRect.height
  rw [stepPlacement_n S k h_succeeds, stepPlacement_rotated S k h_succeeds]
  have hpos : S.t + k ≠ 0 := by omega
  simp [hpos]

/-- After the (k+1)-th step, LRP.x0 increases by 1/(S.t+k). -/
theorem iteratedStep_LRP_x0_succ (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k,
      (1 : ℚ) / ((iteratedStep j S).t : ℕ) ≤ (iteratedStep j S).LRP.x1 - (iteratedStep j S).LRP.x0 ∧
      (1 : ℚ) / (((iteratedStep j S).t + 1 : ℕ) : ℕ) ≤ (iteratedStep j S).LRP.y1 - (iteratedStep j S).LRP.y0)
    : (iteratedStep (k+1) S).LRP.x0 =
        (iteratedStep k S).LRP.x0 + 1 / ((S.t + k : ℕ) : ℕ) := by
  have h_step_k := h_succeeds k (le_refl k)
  rw [iteratedStep_succ, calibratedStep_LRP_x0 h_step_k]
  rw [iteratedStep_t S k (fun j hj => h_succeeds j hj)]

/-- For `j ≤ k`, the LRP.x0 at step k is at least LRP.x0 at step j (plus any number of cuts). -/
theorem iteratedStep_LRP_x0_ge_step_j (S : TailState) (k : ℕ)
    (h_succeeds : ∀ j ≤ k,
      (1 : ℚ) / ((iteratedStep j S).t : ℕ) ≤ (iteratedStep j S).LRP.x1 - (iteratedStep j S).LRP.x0 ∧
      (1 : ℚ) / (((iteratedStep j S).t + 1 : ℕ) : ℕ) ≤ (iteratedStep j S).LRP.y1 - (iteratedStep j S).LRP.y0)
    (j : ℕ) (hjk : j ≤ k)
    : (iteratedStep j S).LRP.x0 ≤ (iteratedStep k S).LRP.x0 := by
  induction k with
  | zero =>
    interval_cases j
    rfl
  | succ k ih =>
      have h_step_k := h_succeeds k (Nat.le_succ k)
      have h_succeeds_k : ∀ j' ≤ k,
          (1 : ℚ) / ((iteratedStep j' S).t : ℕ) ≤ (iteratedStep j' S).LRP.x1 - (iteratedStep j' S).LRP.x0 ∧
          (1 : ℚ) / (((iteratedStep j' S).t + 1 : ℕ) : ℕ) ≤ (iteratedStep j' S).LRP.y1 - (iteratedStep j' S).LRP.y0 :=
        fun j' hj' => h_succeeds j' (Nat.le_succ_of_le hj')
      by_cases hjk' : j ≤ k
      · have ih' := ih h_succeeds_k hjk'
        have h_step_pos : (0 : ℚ) ≤ 1 / ((iteratedStep k S).t : ℕ) := by positivity
        rw [iteratedStep_succ, calibratedStep_LRP_x0 h_step_k]
        linarith
      · push_neg at hjk'
        have hj_eq : j = k + 1 := by omega
        rw [hj_eq]

end MeirMoser
