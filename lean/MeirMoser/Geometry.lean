/-
  Axis-aligned rectangles over ℚ, with width/height/area/semiperim,
  containment, and interior disjointness.

  Decidability instances are provided so finite checks (FinitePacking,
  certificate verification) reduce to `decide` / `native_decide`.
-/
import Mathlib.Tactic
import MeirMoser.Basic

namespace MeirMoser

/-- A closed axis-aligned rectangle [x0, x1] × [y0, y1] over ℚ. -/
structure Rect where
  x0 : ℚ
  y0 : ℚ
  x1 : ℚ
  y1 : ℚ
  hx : x0 ≤ x1 := by decide
  hy : y0 ≤ y1 := by decide
deriving Repr, DecidableEq

namespace Rect

def width (R : Rect) : ℚ := R.x1 - R.x0
def height (R : Rect) : ℚ := R.y1 - R.y0
def area (R : Rect) : ℚ := R.width * R.height
def semiperim (R : Rect) : ℚ := R.width + R.height
def minSide (R : Rect) : ℚ := min R.width R.height
def maxSide (R : Rect) : ℚ := max R.width R.height

theorem width_nonneg (R : Rect) : 0 ≤ R.width := by
  unfold width
  linarith [R.hx]

theorem height_nonneg (R : Rect) : 0 ≤ R.height := by
  unfold height
  linarith [R.hy]

theorem area_nonneg (R : Rect) : 0 ≤ R.area := by
  unfold area
  exact mul_nonneg (width_nonneg R) (height_nonneg R)

theorem semiperim_nonneg (R : Rect) : 0 ≤ R.semiperim := by
  unfold semiperim
  linarith [width_nonneg R, height_nonneg R]

/-- Closed containment: A.contains B ↔ B's corners lie in A. -/
def contains (A B : Rect) : Prop :=
  A.x0 ≤ B.x0 ∧ B.x1 ≤ A.x1 ∧ A.y0 ≤ B.y0 ∧ B.y1 ≤ A.y1

instance (A B : Rect) : Decidable (Rect.contains A B) := by
  unfold contains; exact inferInstance

/-- Interior disjointness: their interiors don't overlap (boundaries may touch). -/
def interiorDisjoint (A B : Rect) : Prop :=
  A.x1 ≤ B.x0 ∨ B.x1 ≤ A.x0 ∨ A.y1 ≤ B.y0 ∨ B.y1 ≤ A.y0

instance (A B : Rect) : Decidable (Rect.interiorDisjoint A B) := by
  unfold interiorDisjoint; exact inferInstance

theorem interiorDisjoint_symm (A B : Rect) :
    interiorDisjoint A B → interiorDisjoint B A := by
  unfold interiorDisjoint
  intro h
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

end Rect

/-- A placed Moser rectangle: index `n ≥ 1`, position (x0,y0), and rotation. -/
structure PlacedRect where
  n : ℕ
  x0 : ℚ
  y0 : ℚ
  rotated : Bool
deriving Repr, DecidableEq

namespace PlacedRect

/-- Width of the placed Moser rectangle: 1/n if not rotated, 1/(n+1) if rotated.
    For n=0 we return 0 (sentinel; we never use D_0). -/
def width (P : PlacedRect) : ℚ :=
  if P.n = 0 then 0
  else if P.rotated then 1 / (P.n + 1 : ℕ)
  else 1 / (P.n : ℕ)

def height (P : PlacedRect) : ℚ :=
  if P.n = 0 then 0
  else if P.rotated then 1 / (P.n : ℕ)
  else 1 / (P.n + 1 : ℕ)

def x1 (P : PlacedRect) : ℚ := P.x0 + P.width
def y1 (P : PlacedRect) : ℚ := P.y0 + P.height

/-- The geometric Rect occupied by this placement. Uses `min`/`max` to ensure
    the corner ordering invariant; in practice `width`/`height ≥ 0`. -/
def toRect (P : PlacedRect) : Rect :=
  { x0 := P.x0, y0 := P.y0, x1 := P.x1, y1 := P.y1
    hx := by
      unfold x1
      have : 0 ≤ P.width := by
        unfold width
        split_ifs <;> norm_num <;> positivity
      linarith
    hy := by
      unfold y1
      have : 0 ≤ P.height := by
        unfold height
        split_ifs <;> norm_num <;> positivity
      linarith }

/-- Area = 1/(n(n+1)). Returns 0 for n = 0 (sentinel). -/
def area (P : PlacedRect) : ℚ :=
  if P.n = 0 then 0 else 1 / ((P.n : ℕ) * (P.n + 1 : ℕ))

end PlacedRect

end MeirMoser
