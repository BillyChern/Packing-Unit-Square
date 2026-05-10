/-
  TwoBacktrack.lean: formal anti-sliver lemma (A.2).

  Setup: a "row" is a sequence of placements at time `t` with each placement of
  width 1/k for k near t, sharing an extent W. The residual width is W − Σ wᵢ.

  Two-backtrack rule: if the residual is below `λ/t` (a sliver), undo the last
  placement; if still below, undo one more. After at most 2 undos the residual is
  in `[λ/t, (λ+C)/t]`.

  We prove this purely combinatorially. The key observation: each undone
  placement adds back its width ≥ `1/(t+R)` for some bounded R (R = #placements
  in the row, typically O(t)). For the bound we'd need careful counting; we
  state the simplest version.

  HISTORICAL NOTE (2026-05): The lemma statements here were originally written
  with `widths.sum ≤ W` and an *upper* bound `x ≤ w` on each width. That
  combination is not provable: dropping placements with small widths cannot
  raise the residual. The intended physical content is a *lower* bound on the
  dropped widths (each undone placement adds back at least `w`). The
  reformulated statements below are honest about this requirement and are
  proved without sorrys.
-/
import Mathlib.Tactic

namespace MeirMoser.TwoBacktrack

/-!
### Auxiliary lemmas about `List.dropLast` and sums.
-/

/-- Sum of `dropLast` plus the (default-padded) last element equals total sum. -/
private lemma sum_dropLast_add_getLastD (xs : List ℚ) :
    xs.dropLast.sum + xs.getLastD 0 = xs.sum := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    cases rest with
    | nil => simp
    | cons y ys =>
      -- `(x :: y :: ys).dropLast = x :: (y :: ys).dropLast`
      -- `(x :: y :: ys).getLastD 0 = (y :: ys).getLastD 0 = ys.getLastD y`
      simp only [List.dropLast_cons₂, List.sum_cons, List.getLastD_cons]
      -- Rewrite `ih` in the same normalized form, also unfolding (y :: ys).sum.
      simp only [List.getLastD_cons, List.sum_cons] at ih
      linarith [ih]

/-- After dropping the last element, residual increases by `getLastD`. -/
private lemma residual_drop_one (W : ℚ) (xs : List ℚ) :
    W - xs.dropLast.sum = (W - xs.sum) + xs.getLastD 0 := by
  have h := sum_dropLast_add_getLastD xs
  linarith

/-- After dropping the last two elements, residual increases by the sum of the
last two (using `getLastD` for safety on short lists). -/
private lemma residual_drop_two (W : ℚ) (xs : List ℚ) :
    W - xs.dropLast.dropLast.sum =
      (W - xs.sum) + xs.getLastD 0 + xs.dropLast.getLastD 0 := by
  have h1 := sum_dropLast_add_getLastD xs
  have h2 := sum_dropLast_add_getLastD xs.dropLast
  linarith

/-!
### Main lemmas.

The original statements (with upper bound `x ≤ w` on each placement) are not
provable. We restate with lower bounds on the dropped widths, which is the
intended physical content of the two-backtrack rule.
-/

/-- **Two-backtrack residual bound** (basic form, corrected).

    Given a list of widths `widths : List ℚ`, an extent `W : ℚ`, and a target
    lower bound `lo : ℚ`, suppose:
      - `0 ≤ lo`
      - `widths.sum ≤ W` (placements fit in the row)
      - the last and second-to-last widths are each ≥ `w` (positive lower bound
        on the widths that may be undone)
      - `lo ≤ 2·w` (so two undos cover lo)

    Then there exists `k ≤ 2` such that
       lo ≤ W - (List.dropLast^[k] widths).sum.

    The hypotheses `hw_last_lb` and `hw_secondlast_lb` use `getLastD 0`, which
    is defined for empty lists to be 0. So in the degenerate case where the
    list has fewer than 2 elements, the lower bound `w` must be ≤ 0, which
    forces `lo ≤ 0`, and then `k = 0` suffices (since the original residual
    `W - widths.sum ≥ 0 ≥ lo`).
-/
theorem two_backtrack_residual_bound
    (widths : List ℚ) (W lo w : ℚ)
    (_hlo_nn : 0 ≤ lo)
    (hsum : widths.sum ≤ W)
    (hw_last_lb : w ≤ widths.getLastD 0)
    (hw_secondlast_lb : w ≤ widths.dropLast.getLastD 0)
    (hw_doubled : lo ≤ 2 * w)
    : ∃ k ≤ 2, lo ≤ W - (List.dropLast^[k] widths).sum := by
  -- Trivial case: residual already ≥ lo with k = 0.
  by_cases h0 : lo ≤ W - widths.sum
  · refine ⟨0, by decide, ?_⟩
    simpa [Function.iterate_zero, id] using h0
  -- Try k = 1: residual = (W - sum) + last.
  by_cases h1 : lo ≤ W - widths.sum + widths.getLastD 0
  · refine ⟨1, by decide, ?_⟩
    have heq : W - (List.dropLast^[1] widths).sum
             = (W - widths.sum) + widths.getLastD 0 := by
      simpa [Function.iterate_one] using residual_drop_one W widths
    rw [heq]; exact h1
  -- k = 2: residual = (W - sum) + last + second-to-last.
  refine ⟨2, by decide, ?_⟩
  have heq2 : W - (List.dropLast^[2] widths).sum
            = (W - widths.sum) + widths.getLastD 0 + widths.dropLast.getLastD 0 := by
    have hi : (List.dropLast^[2] widths) = widths.dropLast.dropLast := by
      change List.dropLast (List.dropLast widths) = widths.dropLast.dropLast
      rfl
    rw [hi]
    exact residual_drop_two W widths
  rw [heq2]
  -- W - sum ≥ 0, last ≥ w, second-to-last ≥ w, lo ≤ 2w.
  have hWs : 0 ≤ W - widths.sum := by linarith [hsum]
  linarith [hw_last_lb, hw_secondlast_lb, hw_doubled, hWs]

/-- **Two-backtrack uniform variant** (corrected).

    A specialized version for the canonical Moser scenario where all placements
    have width `1/(n+1)`. We assume the row started fully packed with `n` such
    placements totalling `n/(n+1) ≤ W`, and we are now considering the state
    after exactly `k = 2` placements have been undone (so `n - 2` remain).

    Then the residual after the two undos is at least `2/(n+1)` (the freed
    width), so any `lo ≤ 2/(n+1)` is covered.

    Note: The earlier formulation allowed `k ∈ {0, 1, 2}` but for `lo` as large
    as `2/(n+1)` only `k = 2` works; we therefore fix `k = 2` here for honesty.
    A version with weaker `lo` (e.g., `lo ≤ 1/(n+1)`) would admit `k = 1`.
    Additionally we require `2 ≤ n` so the subtraction `n - 2` and the chain
    `n/(n+1) ≥ (n-2)/(n+1) + 2/(n+1)` are well-formed.
-/
theorem two_backtrack_uniform
    (n : ℕ) (W : ℚ)
    (hn : 2 ≤ n)
    (hW_packed : (n : ℚ) / (n + 1 : ℕ) ≤ W)
    (lo : ℚ) (_h_lo_nn : 0 ≤ lo) (h_lo : lo ≤ 2 / (n + 1 : ℕ))
    : lo ≤ W - (List.replicate (n - 2) (1 / (n + 1 : ℕ) : ℚ)).sum := by
  -- Sum of `replicate m c` = m·c.
  have hsum : (List.replicate (n - 2) (1 / (n + 1 : ℕ) : ℚ)).sum
            = ((n - 2 : ℕ) : ℚ) * (1 / (n + 1 : ℕ) : ℚ) := by
    rw [List.sum_replicate]; ring
  rw [hsum]
  -- We have W ≥ n/(n+1). Show W - (n-2)/(n+1) ≥ 2/(n+1).
  have hsub : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by
    have h2n : (2 : ℕ) ≤ n := hn
    rw [Nat.cast_sub h2n]
    norm_num
  rw [hsub]
  have hnn : (0 : ℚ) < ((n + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos n
  -- W ≥ n/(n+1), so W - (n-2)/(n+1) ≥ n/(n+1) - (n-2)/(n+1) = 2/(n+1).
  have hresid_lb : (2 : ℚ) / ((n + 1 : ℕ) : ℚ)
                 ≤ W - ((n : ℚ) - 2) * (1 / ((n + 1 : ℕ) : ℚ)) := by
    have hkey : (n : ℚ) / ((n + 1 : ℕ) : ℚ)
              - ((n : ℚ) - 2) * (1 / ((n + 1 : ℕ) : ℚ))
              = 2 / ((n + 1 : ℕ) : ℚ) := by
      field_simp
    linarith [hW_packed, hkey]
  -- Cast h_lo's denominator: `2 / (n+1 : ℕ)` is interpreted as ℚ-division.
  have h_lo_cast : lo ≤ (2 : ℚ) / ((n + 1 : ℕ) : ℚ) := h_lo
  linarith [h_lo_cast, hresid_lb]

end MeirMoser.TwoBacktrack
