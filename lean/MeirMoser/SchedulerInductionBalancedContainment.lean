/-
  SchedulerInductionBalancedContainment.lean (R-A.10):
  Geometric containment / disjointness lemmas for the BALANCED step.

  This file proves three structural propagation results that previously were
  bundled inside `balanced_geometric_invariants_axiom`:

    1. `balancedStep_t_pos`           : `0 < S.t → 0 < (balancedStep S).t`.
    2. `balancedStep_LRP_in_container`: containment is preserved (mirrors
                                        `calibratedStep_LRP_in_container`).
    3. `balancedStep_LRP_disj_from_placed`: the new LRP stays interior-disjoint
                                            from every placement in the new
                                            `placed` list (which extends the
                                            old by one rotated D_t in the
                                            corner of the OLD LRP).
    4. `balancedStep_FP_propagates`   : a FinitePacking on the OLD `S.placed`
                                        + the standard "LRP disjoint from
                                        placed" hypothesis lifts to a
                                        FinitePacking on `(balancedStep S).placed`.

  All lemmas are sorry-free.
-/
import MeirMoser.SchedulerInductionBalanced
import MeirMoser.DiagonalExtractionBalanced
import MeirMoser.FinitePacking
import Mathlib.Tactic

namespace MeirMoser

open List

/-- The balanced step preserves positivity of `t`.

    Since the step either advances `t` by 1 (when D_t fits) or leaves
    `t` unchanged, `0 < S.t` always implies `0 < (balancedStep S).t`. -/
theorem balancedStep_t_pos (S : TailState) (h_t_pos : 0 < S.t)
    : 0 < (balancedStep S).t := by
  unfold balancedStep
  by_cases h : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0
  · rw [dif_pos h]
    by_cases hcut : cutFromX S
    · rw [if_pos hcut]
      -- the new t = S.t + 1
      show 0 < S.t + 1
      omega
    · rw [if_neg hcut]
      show 0 < S.t + 1
      omega
  · rw [dif_neg h]
    exact h_t_pos

/-- Iteration-level: `0 < S.t → ∀ k, 0 < (iteratedBalanced k S).t`. -/
theorem iteratedBalanced_t_pos (S : TailState) (h_t_pos : 0 < S.t) (k : ℕ)
    : 0 < (iteratedBalanced k S).t := by
  induction k with
  | zero => exact h_t_pos
  | succ k ih =>
    rw [iteratedBalanced_succ]
    exact balancedStep_t_pos _ ih

/-- The balanced step preserves containment of the LRP in the container.

    Mirrors `calibratedStep_LRP_in_container`. The new LRP is a sub-rectangle
    of the old LRP (we shrink either x0 → x0 + 1/(t+1) on x-cut or
    y0 → y0 + 1/t on y-cut), and the container is unchanged. -/
theorem balancedStep_LRP_in_container (S : TailState)
    (hin : S.container.contains S.LRP) :
    (balancedStep S).container.contains (balancedStep S).LRP := by
  unfold balancedStep
  by_cases h : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0
  · rw [dif_pos h]
    by_cases hcut : cutFromX S
    · rw [if_pos hcut]
      -- new LRP = (S.LRP.x0 + 1/(t+1), S.LRP.y0, S.LRP.x1, S.LRP.y1)
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hwx : (0 : ℚ) ≤ 1 / ((S.t + 1 : ℕ) : ℕ) := by positivity
        show S.container.x0 ≤ S.LRP.x0 + 1 / ((S.t + 1 : ℕ) : ℕ)
        linarith [hin.1]
      · exact hin.2.1
      · exact hin.2.2.1
      · exact hin.2.2.2
    · rw [if_neg hcut]
      -- new LRP = (S.LRP.x0, S.LRP.y0 + 1/t, S.LRP.x1, S.LRP.y1)
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hin.1
      · exact hin.2.1
      · have hwy : (0 : ℚ) ≤ 1 / ((S.t : ℕ) : ℕ) := by positivity
        show S.container.y0 ≤ S.LRP.y0 + 1 / (S.t : ℕ)
        linarith [hin.2.2.1]
      · exact hin.2.2.2
  · rw [dif_neg h]
    exact hin

/-- The new LRP after a successful balanced step is interior-disjoint from
    the freshly placed rotated D_t.

    On the x-cut branch the new LRP starts at `S.LRP.x0 + 1/(t+1)`, while the
    placement has width `1/(t+1)` and starts at `S.LRP.x0`, so its x1 is
    exactly the new LRP's x0 — these touch on a vertical edge but their
    interiors are disjoint.

    On the y-cut branch the analogous identity holds on the y axis. -/
theorem balancedStep_LRP_disj_new_placement (S : TailState)
    (hcanFit : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0)
    (h_t_pos : 0 < S.t) :
    Rect.interiorDisjoint (balancedStep S).LRP
      ({ n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true } : PlacedRect).toRect := by
  -- Compute placement.toRect: x1 = x0 + width, y1 = y0 + height.
  -- For rotated D_t (n = S.t, rotated = true, n ≠ 0 since 0 < S.t):
  --   width = 1/(n+1), height = 1/n.
  unfold balancedStep
  rw [dif_pos hcanFit]
  have h_n_ne : (S.t : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp h_t_pos
  by_cases hcut : cutFromX S
  · -- x-cut: new LRP.x0 = S.LRP.x0 + 1/(t+1), placement.x1 = S.LRP.x0 + 1/(t+1).
    rw [if_pos hcut]
    -- pick first disjunct (placement.x1 ≤ new LRP.x0).
    -- but `Rect.interiorDisjoint A B := A.x1 ≤ B.x0 ∨ B.x1 ≤ A.x0 ∨ ...`
    -- so we want `placement.x1 ≤ new_LRP.x0`. Since the first arg is
    -- newLRP, that's `B.x1 ≤ A.x0`.
    show ({x0 := S.LRP.x0 + 1 / ((S.t + 1 : ℕ) : ℕ), y0 := S.LRP.y0,
            x1 := S.LRP.x1, y1 := S.LRP.y1, hx := _, hy := _} : Rect).x1 ≤
              ({n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true} :
                PlacedRect).toRect.x0
          ∨ ({n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true} :
                PlacedRect).toRect.x1 ≤
            ({x0 := S.LRP.x0 + 1 / ((S.t + 1 : ℕ) : ℕ), y0 := S.LRP.y0,
              x1 := S.LRP.x1, y1 := S.LRP.y1, hx := _, hy := _} : Rect).x0
          ∨ ({x0 := S.LRP.x0 + 1 / ((S.t + 1 : ℕ) : ℕ), y0 := S.LRP.y0,
              x1 := S.LRP.x1, y1 := S.LRP.y1, hx := _, hy := _} : Rect).y1 ≤
            ({n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true} :
                PlacedRect).toRect.y0
          ∨ ({n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true} :
                PlacedRect).toRect.y1 ≤
            ({x0 := S.LRP.x0 + 1 / ((S.t + 1 : ℕ) : ℕ), y0 := S.LRP.y0,
              x1 := S.LRP.x1, y1 := S.LRP.y1, hx := _, hy := _} : Rect).y0
    right; left
    -- placement.toRect.x1 = placement.x0 + placement.width
    show ({n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true} :
            PlacedRect).x1 ≤ S.LRP.x0 + 1 / ((S.t + 1 : ℕ) : ℕ)
    unfold PlacedRect.x1 PlacedRect.width
    simp only [h_n_ne, ↓reduceIte]
    -- After unfolding, goal is `S.LRP.x0 + 1/(S.t + 1) ≤ S.LRP.x0 + 1/(S.t + 1)`.
    rfl
  · -- y-cut: new LRP.y0 = S.LRP.y0 + 1/t, placement.y1 = S.LRP.y0 + 1/t.
    rw [if_neg hcut]
    show ({x0 := S.LRP.x0, y0 := S.LRP.y0 + 1 / ((S.t : ℕ) : ℕ),
            x1 := S.LRP.x1, y1 := S.LRP.y1, hx := _, hy := _} : Rect).x1 ≤
              ({n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true} :
                PlacedRect).toRect.x0
          ∨ ({n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true} :
                PlacedRect).toRect.x1 ≤
            ({x0 := S.LRP.x0, y0 := S.LRP.y0 + 1 / ((S.t : ℕ) : ℕ),
              x1 := S.LRP.x1, y1 := S.LRP.y1, hx := _, hy := _} : Rect).x0
          ∨ ({x0 := S.LRP.x0, y0 := S.LRP.y0 + 1 / ((S.t : ℕ) : ℕ),
              x1 := S.LRP.x1, y1 := S.LRP.y1, hx := _, hy := _} : Rect).y1 ≤
            ({n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true} :
                PlacedRect).toRect.y0
          ∨ ({n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true} :
                PlacedRect).toRect.y1 ≤
            ({x0 := S.LRP.x0, y0 := S.LRP.y0 + 1 / ((S.t : ℕ) : ℕ),
              x1 := S.LRP.x1, y1 := S.LRP.y1, hx := _, hy := _} : Rect).y0
    right; right; right
    -- placement.toRect.y1 ≤ new_LRP.y0
    show ({n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true} :
            PlacedRect).y1 ≤ S.LRP.y0 + 1 / ((S.t : ℕ) : ℕ)
    unfold PlacedRect.y1 PlacedRect.height
    simp only [h_n_ne, ↓reduceIte]
    -- After unfolding, goal is `S.LRP.y0 + 1/S.t ≤ S.LRP.y0 + 1/S.t`.
    rfl

/-- The new LRP after a successful balanced step is contained in the OLD LRP.

    On x-cut: new LRP = [x0+1/(t+1), x1] × [y0, y1] ⊆ old LRP.
    On y-cut: new LRP = [x0, x1] × [y0+1/t, y1] ⊆ old LRP. -/
theorem balancedStep_LRP_in_old_LRP (S : TailState)
    (hcanFit : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    S.LRP.contains (balancedStep S).LRP := by
  unfold balancedStep
  rw [dif_pos hcanFit]
  by_cases hcut : cutFromX S
  · rw [if_pos hcut]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : (0 : ℚ) ≤ 1 / ((S.t + 1 : ℕ) : ℕ) := by positivity
      show S.LRP.x0 ≤ S.LRP.x0 + 1 / ((S.t + 1 : ℕ) : ℕ)
      linarith
    · exact le_refl _
    · exact le_refl _
    · exact le_refl _
  · rw [if_neg hcut]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact le_refl _
    · exact le_refl _
    · have : (0 : ℚ) ≤ 1 / ((S.t : ℕ) : ℕ) := by positivity
      show S.LRP.y0 ≤ S.LRP.y0 + 1 / (S.t : ℕ)
      linarith
    · exact le_refl _

/-- If two rectangles A,B satisfy `A ⊇ B` (i.e., `A.contains B`), and A is
    interior-disjoint from C, then B is interior-disjoint from C.

    This is a useful "shrink" lemma. -/
theorem interiorDisjoint_of_contains_left
    {A B C : Rect} (h_in : A.contains B) (h_disj : Rect.interiorDisjoint A C) :
    Rect.interiorDisjoint B C := by
  unfold Rect.interiorDisjoint at h_disj ⊢
  rcases h_disj with h | h | h | h
  · -- A.x1 ≤ C.x0; since B.x1 ≤ A.x1 (h_in.2.1), B.x1 ≤ C.x0.
    left; linarith [h_in.2.1]
  · -- C.x1 ≤ A.x0 ≤ B.x0.
    right; left; linarith [h_in.1]
  · -- A.y1 ≤ C.y0; since B.y1 ≤ A.y1 (h_in.2.2.2), B.y1 ≤ C.y0.
    right; right; left; linarith [h_in.2.2.2]
  · -- C.y1 ≤ A.y0 ≤ B.y0.
    right; right; right; linarith [h_in.2.2.1]

/-- The new LRP is interior-disjoint from every placement in `S.placed`,
    given that the OLD LRP is interior-disjoint from each. -/
theorem balancedStep_LRP_disj_old_placed
    (S : TailState)
    (hcanFit : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0)
    (h_disj : ∀ P ∈ S.placed, Rect.interiorDisjoint S.LRP P.toRect) :
    ∀ P ∈ S.placed, Rect.interiorDisjoint (balancedStep S).LRP P.toRect := by
  intro P hP
  have h_LRP_in : S.LRP.contains (balancedStep S).LRP :=
    balancedStep_LRP_in_old_LRP S hcanFit
  exact interiorDisjoint_of_contains_left h_LRP_in (h_disj P hP)

/-- The new LRP is interior-disjoint from every placement in
    `(balancedStep S).placed`. The new placed list is `S.placed ++ [new]`. -/
theorem balancedStep_LRP_disj_from_placed
    (S : TailState)
    (h_t_pos : 0 < S.t)
    (h_disj : ∀ P ∈ S.placed, Rect.interiorDisjoint S.LRP P.toRect) :
    ∀ P ∈ (balancedStep S).placed,
      Rect.interiorDisjoint (balancedStep S).LRP P.toRect := by
  intro P hP
  -- Case split on whether the step succeeded.
  by_cases h : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0
  · -- success branch: (balancedStep S).placed = S.placed ++ [new].
    have h_eq := balancedStep_placed_eq h
    rw [h_eq] at hP
    rcases List.mem_append.mp hP with hP_old | hP_new
    · -- P was already in S.placed → use the shrink lemma.
      exact balancedStep_LRP_disj_old_placed S h h_disj P hP_old
    · -- P is the new placement → use the new-placement disjointness lemma.
      rw [List.mem_singleton] at hP_new
      rw [hP_new]
      exact balancedStep_LRP_disj_new_placement S h h_t_pos
  · -- failure branch: (balancedStep S).placed = S.placed; LRP unchanged.
    have h_step_eq : balancedStep S = S := by
      unfold balancedStep
      rw [dif_neg h]
    rw [h_step_eq]
    rw [h_step_eq] at hP
    exact h_disj P hP

/-! ## FinitePacking propagation

    Given the new disjointness lemma above, we can lift `FinitePacking` from
    `S.placed` to `(balancedStep S).placed`. -/

/-- Lemma: a singleton list `[P]` is `PairwiseDisjoint`. -/
theorem PairwiseDisjoint_singleton (P : PlacedRect) :
    PairwiseDisjoint [P] := by
  unfold PairwiseDisjoint
  exact List.pairwise_singleton _ P

/-- Lemma: `PairwiseDisjoint (xs ++ [y])` iff `PairwiseDisjoint xs` and
    `y` is interior-disjoint from every element of `xs`. -/
theorem PairwiseDisjoint_append_singleton (xs : List PlacedRect) (y : PlacedRect)
    (h_xs : PairwiseDisjoint xs)
    (h_y : ∀ x ∈ xs, Rect.interiorDisjoint x.toRect y.toRect) :
    PairwiseDisjoint (xs ++ [y]) := by
  unfold PairwiseDisjoint
  rw [List.pairwise_append]
  refine ⟨h_xs, ?_, ?_⟩
  · -- PairwiseDisjoint [y]
    exact List.pairwise_singleton _ y
  · -- ∀ a ∈ xs, ∀ b ∈ [y], interiorDisjoint a.toRect b.toRect
    intro a ha b hb
    rw [List.mem_singleton] at hb
    rw [hb]
    exact h_y a ha

/-- One balanced step preserves `FinitePacking`, given the standard "LRP
    interior-disjoint from existing placed" hypothesis. -/
theorem balancedStep_FP
    (S : TailState)
    (h_t_pos : 0 < S.t)
    (h_FP : FinitePacking S.container S.placed)
    (h_LRP_in : S.container.contains S.LRP)
    (h_disj : ∀ P ∈ S.placed, Rect.interiorDisjoint S.LRP P.toRect) :
    FinitePacking (balancedStep S).container (balancedStep S).placed := by
  rcases h_FP with ⟨h_in, h_dims, h_pair⟩
  -- Case split on whether the step succeeded.
  by_cases h : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0
  · have h_eq := balancedStep_placed_eq h
    have h_cont_eq := balancedStep_container S
    -- new placed = old placed ++ [new placement]
    set P_new : PlacedRect :=
      { n := S.t, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true }
    -- (a) AllInside: each old placement was inside container; new one inside S.LRP ⊆ container.
    refine ⟨?_, ?_, ?_⟩
    · -- AllInside (balancedStep S).container (balancedStep S).placed.
      rw [h_eq, h_cont_eq]
      intro P hP
      rcases List.mem_append.mp hP with hP_old | hP_new
      · exact h_in P hP_old
      · rw [List.mem_singleton] at hP_new
        rw [hP_new]
        -- New placement ⊆ S.LRP ⊆ S.container.
        -- toRect for P_new: x0 = S.LRP.x0, y0 = S.LRP.y0,
        --                    x1 = S.LRP.x0 + 1/(t+1), y1 = S.LRP.y0 + 1/t.
        unfold Rect.contains
        have h_n_ne : (S.t : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp h_t_pos
        -- Container box bounds.
        rcases h_LRP_in with ⟨h_cx0, h_cx1, h_cy0, h_cy1⟩
        -- new placement.toRect.x0 = S.LRP.x0
        have h_pxw : (P_new).toRect.x0 = S.LRP.x0 := rfl
        have h_pyw : (P_new).toRect.y0 = S.LRP.y0 := rfl
        -- new placement.toRect.x1 = S.LRP.x0 + 1/(t+1)
        have h_px1 : (P_new).toRect.x1 = S.LRP.x0 + 1 / ((S.t : ℕ) + 1 : ℕ) := by
          unfold PlacedRect.toRect PlacedRect.x1 PlacedRect.width
          simp only [h_n_ne, ↓reduceIte]
        -- new placement.toRect.y1 = S.LRP.y0 + 1/t
        have h_py1 : (P_new).toRect.y1 = S.LRP.y0 + 1 / (S.t : ℕ) := by
          unfold PlacedRect.toRect PlacedRect.y1 PlacedRect.height
          simp only [h_n_ne, ↓reduceIte]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [h_pxw]; exact h_cx0
        · rw [h_px1]
          -- need: S.LRP.x0 + 1/(t+1) ≤ S.container.x1.
          have h_fit_x : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 := h.1
          have h_cast : ((S.t + 1 : ℕ) : ℚ) = ((S.t : ℕ) + 1 : ℕ) := by push_cast; ring
          rw [h_cast] at h_fit_x
          linarith
        · rw [h_pyw]; exact h_cy0
        · rw [h_py1]
          -- need: S.LRP.y0 + 1/t ≤ S.container.y1.
          have h_fit_y : (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0 := h.2
          linarith
    · -- AllValidDims (balancedStep S).placed.
      rw [h_eq]
      intro P hP
      rcases List.mem_append.mp hP with hP_old | hP_new
      · exact h_dims P hP_old
      · rw [List.mem_singleton] at hP_new
        rw [hP_new]
        unfold PlacedRect.validDims
        refine ⟨h_t_pos, ?_⟩
        -- P_new.rotated = true, so we need P_new.width = 1/(n+1) ∧ P_new.height = 1/n.
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
    · -- PairwiseDisjoint (balancedStep S).placed.
      rw [h_eq]
      apply PairwiseDisjoint_append_singleton
      · exact h_pair
      · intro P hP
        -- We need: P interior-disjoint from new placement.
        have h_disjLRP : Rect.interiorDisjoint S.LRP P.toRect := h_disj P hP
        -- new placement.toRect ⊆ S.LRP, so by interiorDisjoint_of_contains_left
        -- (with A = S.LRP, B = new placement.toRect, C = P.toRect):
        -- new placement.toRect interior-disjoint from P.toRect.
        -- Need to show new placement.toRect ⊆ S.LRP first.
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
            have h_fit_x : (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ S.LRP.x1 - S.LRP.x0 := h.1
            have h_cast : ((S.t + 1 : ℕ) : ℚ) = ((S.t : ℕ) + 1 : ℕ) := by push_cast; ring
            rw [h_cast] at h_fit_x
            linarith
          · rw [h_py0]
          · rw [h_py1]
            have h_fit_y : (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0 := h.2
            linarith
        -- Now apply interiorDisjoint_of_contains_left (with A = S.LRP, B = new).
        have h_disj_new : Rect.interiorDisjoint (P_new).toRect P.toRect :=
          interiorDisjoint_of_contains_left h_new_in h_disjLRP
        -- We need P.toRect interior-disjoint from new placement.
        -- (Note: PairwiseDisjoint_append_singleton wants
        --   ∀ a ∈ xs, interiorDisjoint a.toRect y.toRect; here a = P, y = P_new.)
        exact Rect.interiorDisjoint_symm _ _ h_disj_new
  · -- Failure branch: balancedStep S = S, so FP holds vacuously.
    have h_step_eq : balancedStep S = S := by
      unfold balancedStep
      rw [dif_neg h]
    rw [h_step_eq]
    exact ⟨h_in, h_dims, h_pair⟩

/-! ## Iteration-level propagation -/

/-- Iterated containment: after k balanced steps the LRP stays inside container. -/
theorem iteratedBalanced_LRP_in_container
    (S : TailState)
    (h_LRP_in : S.container.contains S.LRP)
    (k : ℕ) :
    (iteratedBalanced k S).container.contains (iteratedBalanced k S).LRP := by
  induction k with
  | zero => exact h_LRP_in
  | succ k ih =>
    rw [iteratedBalanced_succ]
    exact balancedStep_LRP_in_container _ ih

/-- Iterated disjointness: after k balanced steps the LRP stays
    interior-disjoint from every placement.

    This is the iteration-level version of
    `balancedStep_LRP_disj_from_placed`. It needs `0 < S.t` to apply at every
    intermediate step. -/
theorem iteratedBalanced_LRP_disj_from_placed
    (S : TailState)
    (h_t_pos : 0 < S.t)
    (h_disj : ∀ P ∈ S.placed, Rect.interiorDisjoint S.LRP P.toRect)
    (k : ℕ) :
    ∀ P ∈ (iteratedBalanced k S).placed,
      Rect.interiorDisjoint (iteratedBalanced k S).LRP P.toRect := by
  induction k with
  | zero => exact h_disj
  | succ k ih =>
    have h_tk_pos : 0 < (iteratedBalanced k S).t :=
      iteratedBalanced_t_pos S h_t_pos k
    rw [iteratedBalanced_succ]
    exact balancedStep_LRP_disj_from_placed _ h_tk_pos ih

/-- Iterated FinitePacking: after k balanced steps `placed` is still a
    valid finite packing.

    Hypotheses: `0 < S.t`, `S.LRP ⊆ S.container`, `S.LRP` interior-disjoint
    from each placement in `S.placed`, and `FinitePacking S.container S.placed`. -/
theorem iteratedBalanced_FP
    (S : TailState)
    (h_t_pos : 0 < S.t)
    (h_LRP_in : S.container.contains S.LRP)
    (h_disj : ∀ P ∈ S.placed, Rect.interiorDisjoint S.LRP P.toRect)
    (h_FP : FinitePacking S.container S.placed)
    (k : ℕ) :
    FinitePacking (iteratedBalanced k S).container (iteratedBalanced k S).placed := by
  induction k with
  | zero => exact h_FP
  | succ k ih =>
    have h_tk_pos : 0 < (iteratedBalanced k S).t :=
      iteratedBalanced_t_pos S h_t_pos k
    have h_LRP_in_k : (iteratedBalanced k S).container.contains
        (iteratedBalanced k S).LRP :=
      iteratedBalanced_LRP_in_container S h_LRP_in k
    have h_disj_k : ∀ P ∈ (iteratedBalanced k S).placed,
        Rect.interiorDisjoint (iteratedBalanced k S).LRP P.toRect :=
      iteratedBalanced_LRP_disj_from_placed S h_t_pos h_disj k
    rw [iteratedBalanced_succ]
    exact balancedStep_FP _ h_tk_pos ih h_LRP_in_k h_disj_k

/-- The "next-step" FinitePacking: the FinitePacking on `(iteratedBalanced (k+1) S).placed`,
    which is `(balancedStep (iteratedBalanced k S)).placed`. This is the form
    that the original `balanced_geometric_invariants_axiom` quantified over. -/
theorem iteratedBalanced_FP_next
    (S : TailState)
    (h_t_pos : 0 < S.t)
    (h_LRP_in : S.container.contains S.LRP)
    (h_disj : ∀ P ∈ S.placed, Rect.interiorDisjoint S.LRP P.toRect)
    (h_FP : FinitePacking S.container S.placed)
    (k : ℕ) :
    FinitePacking (balancedStep (iteratedBalanced k S)).container
      (balancedStep (iteratedBalanced k S)).placed := by
  have := iteratedBalanced_FP S h_t_pos h_LRP_in h_disj h_FP (k+1)
  rw [iteratedBalanced_succ] at this
  exact this

end MeirMoser
