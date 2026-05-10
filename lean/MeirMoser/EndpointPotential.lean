/-
  Endpoint-perimeter potential lemma:

    if every endpoint E has width(E) ≤ C/t, then
       Σ area(E) ≤ (C/t) · Σ semiperim(E).

  This converts an *area* control problem into a *perimeter* control problem,
  letting us bound endpoint area by maintaining a perimeter potential P_ep.
-/
import Mathlib.Tactic
import MeirMoser.Geometry

namespace MeirMoser

open BigOperators

/-- The endpoint-area-by-width-and-perimeter bound, over a List of Rect.

    Crucial setup: width E ≤ C  forces  area E = width · height ≤ C · height
    ≤ C · semiperim. Sum and you get Σ area ≤ C · Σ semiperim. -/
theorem endpoint_area_bound_by_width_and_perimeter
    (eps : List Rect)
    {C : ℚ}
    (hC : 0 ≤ C)
    (hwidth : ∀ E ∈ eps, E.width ≤ C)
    : (eps.map Rect.area).sum ≤ C * (eps.map Rect.semiperim).sum := by
  induction eps with
  | nil => simp
  | cons E rest ih =>
      have hE : E.width ≤ C := hwidth E (by simp)
      have hrest : ∀ F ∈ rest, F.width ≤ C := fun F hF => hwidth F (by simp [hF])
      have ih' := ih hrest
      have hE_h : 0 ≤ E.height := E.height_nonneg
      have hE_w : 0 ≤ E.width := E.width_nonneg
      have hE_area : E.area ≤ C * E.semiperim := by
        unfold Rect.area Rect.semiperim
        -- area = w·h ≤ C·h ≤ C·(w+h) since C, w ≥ 0.
        calc E.width * E.height
            ≤ C * E.height := by exact mul_le_mul_of_nonneg_right hE hE_h
          _ ≤ C * (E.width + E.height) := by
              have : 0 ≤ C * E.width := mul_nonneg hC hE_w
              linarith
      simp only [List.map_cons, List.sum_cons]
      have : E.area + (rest.map Rect.area).sum
           ≤ C * E.semiperim + C * (rest.map Rect.semiperim).sum := by
        linarith
      have rhs_eq : C * E.semiperim + C * (rest.map Rect.semiperim).sum
                  = C * (E.semiperim + (rest.map Rect.semiperim).sum) := by ring
      linarith [rhs_eq]

end MeirMoser
