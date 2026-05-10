/-
  Basic shared definitions for the Meir-Moser project.
-/
import Mathlib.Tactic

namespace MeirMoser

/-- The (closed) area-1 unit square. -/
def unitSquareArea : ℚ := 1

/-- The next index of the Moser sequence is `n+1`. -/
abbrev NextIdx (n : ℕ) : ℕ := n + 1

end MeirMoser
