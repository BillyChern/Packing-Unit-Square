/-
  Telescoping sum:  Σ_{n=N}^{M-1} 1/(n(n+1)) = 1/N - 1/M  for 1 ≤ N ≤ M.

  This is the area-bookkeeping identity that makes the Meir-Moser problem
  exactly fit-the-area: at the start of step N, the remaining tail area is 1/N.
-/
import Mathlib.Tactic
import MeirMoser.Basic

namespace MeirMoser

open BigOperators

/-- Per-rectangle area as a rational: 1/(n(n+1)). For n=0 we return 0. -/
noncomputable def DArea (n : ℕ) : ℚ :=
  if n = 0 then 0 else 1 / (n * (n + 1) : ℕ)

/-- Telescoping identity over the rationals. Stated for `1 ≤ N ≤ M`. -/
theorem finite_tail_telescopes
    (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    (Finset.Ico N M).sum (fun n => DArea n) = (1 : ℚ) / N - 1 / M := by
  induction M, hNM using Nat.le_induction with
  | base =>
      simp [Finset.Ico_self]
  | succ M hMN ih =>
      rw [Finset.sum_Ico_succ_top (by linarith) (fun n => DArea n)]
      rw [ih]
      have hMpos : 0 < (M : ℚ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_trans hN hMN))
      have hM1pos : 0 < ((M + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos _
      have hMne : (M : ℚ) ≠ 0 := ne_of_gt hMpos
      have hM1ne : ((M + 1 : ℕ) : ℚ) ≠ 0 := ne_of_gt hM1pos
      have hMprod : (M : ℚ) * ((M + 1 : ℕ) : ℚ) ≠ 0 := mul_ne_zero hMne hM1ne
      have : DArea M = (1 : ℚ) / M - 1 / (M + 1 : ℕ) := by
        unfold DArea
        have hM_ne : M ≠ 0 := by linarith
        rw [if_neg hM_ne]
        push_cast
        field_simp
      linarith [this]

end MeirMoser
