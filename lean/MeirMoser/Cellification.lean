/-
  Cellification lemma: a strip M × m with M ≥ m > 0 splits into N = ⌈M/m⌉ cells
  of dims m × (M/N), with each cell having aspect ≤ 2 and total semiperimeter ≤ 3M.

  We avoid formalizing `Nat.ceil` over ℚ by parametrizing over an explicit `N`
  satisfying  M ≤ N·m  and  N·m < M + m  (i.e. N = ⌈M/m⌉).
-/
import Mathlib.Tactic
import MeirMoser.Basic

namespace MeirMoser.Cellification

/-- Bound on the cell long side and total semiperimeter for a cellification. -/
theorem cellification_bounds
    {M m : ℚ} {N : ℕ}
    (hm : 0 < m) (hM : m ≤ M)
    (hN1 : M ≤ (N : ℚ) * m)
    (hN2 : (N : ℚ) * m < M + m) :
    let cellLong : ℚ := M / N
    m / 2 < cellLong ∧
    cellLong ≤ m ∧
    (N : ℚ) * (m + cellLong) ≤ 3 * M := by
  -- N ≥ 1 because M ≥ m > 0 forces (N : ℚ) ≥ 1.
  have hNpos : 0 < (N : ℚ) := by
    rcases lt_or_eq_of_le (by linarith : (0 : ℚ) ≤ M) with hM0 | hM0
    · -- M > 0; (N : ℚ) ≥ M/m > 0
      have : (0 : ℚ) < (N : ℚ) * m := by linarith
      have : 0 < (N : ℚ) := by
        by_contra hne
        push_neg at hne
        have : (N : ℚ) * m ≤ 0 := by nlinarith
        linarith
      exact this
    · -- M = 0 contradicts m ≤ M and m > 0
      exfalso; linarith
  -- cellLong = M / N
  let cellLong : ℚ := M / N
  refine ⟨?_, ?_, ?_⟩
  · -- m/2 < M/N. From hN2: N·m < M + m ≤ 2M, so N·m < 2M, hence m/2 < M/N.
    have h1 : (N : ℚ) * m < 2 * M := by linarith
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℚ) < 2) hNpos]
    nlinarith
  · -- M/N ≤ m  follows from N·m ≥ M (i.e. hN1).
    rw [div_le_iff₀ hNpos]
    nlinarith
  · -- N·(m + M/N) = N·m + M ≤ 3M  follows from N·m ≤ 2M.
    have h1 : (N : ℚ) * m < 2 * M := by linarith
    have heq : (N : ℚ) * (m + M / N) = (N : ℚ) * m + M := by
      have hNne : (N : ℚ) ≠ 0 := ne_of_gt hNpos
      field_simp; ring
    rw [heq]
    linarith

end MeirMoser.Cellification
