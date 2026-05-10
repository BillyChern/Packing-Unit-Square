/-
  FinitePacking: predicate for "all rectangles in `placed` are inside `container`,
  have correct dimensions, and pairwise interior-disjoint."

  Decidability gives us machine-checking by `decide` for small N.
-/
import MeirMoser.Geometry
import MeirMoser.Basic
import Mathlib.Data.List.Pairwise

namespace MeirMoser

open List

/-- A placed rectangle has the correct Moser dimensions. -/
def PlacedRect.validDims (P : PlacedRect) : Prop :=
  P.n ≥ 1 ∧
  if P.rotated then
    P.width = 1 / (P.n + 1 : ℕ) ∧ P.height = 1 / (P.n : ℕ)
  else
    P.width = 1 / (P.n : ℕ) ∧ P.height = 1 / (P.n + 1 : ℕ)

instance (P : PlacedRect) : Decidable (PlacedRect.validDims P) := by
  unfold PlacedRect.validDims; exact inferInstance

/-- All `placed` are inside `container`. -/
def AllInside (container : Rect) (placed : List PlacedRect) : Prop :=
  ∀ P ∈ placed, container.contains P.toRect

instance (C : Rect) (placed : List PlacedRect) : Decidable (AllInside C placed) := by
  unfold AllInside; exact List.decidableBAll _ _

/-- All placed rectangles have valid Moser dimensions. -/
def AllValidDims (placed : List PlacedRect) : Prop :=
  ∀ P ∈ placed, P.validDims

instance (placed : List PlacedRect) : Decidable (AllValidDims placed) := by
  unfold AllValidDims; exact List.decidableBAll _ _

/-- Pairwise interior-disjoint. Uses List.Pairwise for an O(n²) decidable check. -/
def PairwiseDisjoint (placed : List PlacedRect) : Prop :=
  placed.Pairwise (fun P Q => Rect.interiorDisjoint P.toRect Q.toRect)

instance (placed : List PlacedRect) : Decidable (PairwiseDisjoint placed) := by
  unfold PairwiseDisjoint; exact inferInstance

/-- A FinitePacking is: correct dims, all inside container, pairwise disjoint. -/
def FinitePacking (container : Rect) (placed : List PlacedRect) : Prop :=
  AllInside container placed ∧
  AllValidDims placed ∧
  PairwiseDisjoint placed

instance (C : Rect) (placed : List PlacedRect) : Decidable (FinitePacking C placed) := by
  unfold FinitePacking; exact inferInstance

end MeirMoser
