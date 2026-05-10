/-
  NormalBoxScheduler.lean: scheduler-invariant cumulative-width bound.

  This file integrates the proved `MeirMoser.NormalBoxes.calibrated_normal_sum`
  into a scheduler-facing lemma that bounds the *total width* of normal boxes
  appended by the calibrated scheduler over a range of iterations.

  The bookkeeping picture is:

    * The calibrated scheduler runs at iterations `t_0, t_0 + 1, …, t_0 + N`.
    * At each iteration `j`, it (optionally) appends one normal box of width
      `w_j` with birth index `b_j ∈ ℕ`, satisfying the calibrated
      normal-width law
          0 ≤ w_j  ∧  w_j ≤ c_2 · b_j^{-(γ+1)}.
    * All birth indices satisfy `t ≤ b_j ≤ N` and are pairwise distinct
      (each iteration `j` births at most one normal box with index `j`).

  Under these hypotheses we conclude
      Σ_j w_j ≤ c_2 · (2 / t),
  which is the cumulative-width bound used by the framework.

  Key ingredient: `MeirMoser.NormalBoxes.calibrated_normal_sum` from
  `NormalBoxes.lean`, which gives the analytic tail-sum bound
      Σ_{k = K}^{N} k^{-(γ+1)} ≤ 2 / t      whenever (K-1) ≥ t^{1/γ}.

  This file proves only DEFINITIONS + the cumulative-width bookkeeping
  lemmas; it does not modify any other file.
-/
import MeirMoser.NormalBoxes
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace MeirMoser.NormalBoxScheduler

open Real
open MeirMoser.NormalBoxes

/-! ### Finset-form scheduler invariant

The most natural formulation: we have a finset `S ⊆ Finset.Icc K N` of birth
indices, and a width assignment `w : ℕ → ℝ`. If the calibrated normal-width
law holds pointwise on `S`, then `Σ_{k ∈ S} w k ≤ c_2 · 2 / t`. -/

/-- Cumulative-width bound over a finset of birth indices.

    Given:
      * `γ ∈ (1, 3/2)` (the calibrated exponent),
      * `t ≥ 1`, `K ≥ 2`, `N ≥ K`, with `(K - 1 : ℝ) ≥ t^{1/γ}`,
      * a finset `S ⊆ Finset.Icc K N` of birth indices,
      * `c_2 ≥ 0`,
      * a width function `w : ℕ → ℝ` satisfying
          `0 ≤ w k ≤ c_2 · k^{-(γ+1)}` for every `k ∈ S`,

    we conclude `Σ_{k ∈ S} w k ≤ c_2 · 2 / t`.

    This is the scheduler-invariant form of `calibrated_normal_sum`. -/
theorem normal_widths_finset_bound
    {γ : ℝ} (hγ1 : 1 < γ) (hγ2 : γ < 3/2)
    {K N : ℕ} (hK2 : 2 ≤ K) (hKN : K ≤ N)
    {t : ℝ} (ht : 1 ≤ t)
    (hKt : ((K - 1 : ℕ) : ℝ) ≥ t^(1/γ))
    {c2 : ℝ} (hc2 : 0 ≤ c2)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc K N)
    (w : ℕ → ℝ)
    (h_law : ∀ k ∈ S, 0 ≤ w k ∧ w k ≤ c2 * ((k : ℝ))^(-(γ + 1)))
    : (S.sum w) ≤ c2 * 2 / t := by
  -- Step 1: pointwise bound, S.sum w ≤ S.sum (c2·k^{-(γ+1)}).
  have hpt : ∀ k ∈ S, w k ≤ c2 * ((k : ℝ))^(-(γ + 1)) := fun k hk => (h_law k hk).2
  have hstep1 : (S.sum w) ≤ S.sum (fun k => c2 * ((k : ℝ))^(-(γ + 1))) :=
    Finset.sum_le_sum hpt
  -- Step 2: factor out c2.
  have hfactor : S.sum (fun k => c2 * ((k : ℝ))^(-(γ + 1)))
                  = c2 * S.sum (fun k => ((k : ℝ))^(-(γ + 1))) := by
    rw [← Finset.mul_sum]
  -- Step 3: extend to Icc K N (each term is nonneg).
  have hnn_term : ∀ k ∈ Finset.Icc K N, 0 ≤ ((k : ℝ))^(-(γ + 1)) := by
    intro k _
    exact Real.rpow_nonneg (Nat.cast_nonneg k) _
  have hext : S.sum (fun k => ((k : ℝ))^(-(γ + 1)))
              ≤ (Finset.Icc K N).sum (fun k => ((k : ℝ))^(-(γ + 1))) :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun k hk _ => hnn_term k hk)
  -- Step 4: invoke the analytic bound.
  have hcal : (Finset.Icc K N).sum (fun k => ((k : ℝ))^(-(γ + 1))) ≤ 2 / t :=
    calibrated_normal_sum hγ1 hγ2 hK2 ht hKt hKN
  -- Step 5: monotonicity in c2.
  have hmul1 : c2 * S.sum (fun k => ((k : ℝ))^(-(γ + 1)))
                ≤ c2 * (Finset.Icc K N).sum (fun k => ((k : ℝ))^(-(γ + 1))) :=
    mul_le_mul_of_nonneg_left hext hc2
  have hmul2 : c2 * (Finset.Icc K N).sum (fun k => ((k : ℝ))^(-(γ + 1)))
                ≤ c2 * (2 / t) :=
    mul_le_mul_of_nonneg_left hcal hc2
  -- Combine and rewrite c2 * (2/t) = c2 * 2 / t.
  have h_total : S.sum w ≤ c2 * (2 / t) := by
    calc S.sum w
        ≤ S.sum (fun k => c2 * ((k : ℝ))^(-(γ + 1))) := hstep1
      _ = c2 * S.sum (fun k => ((k : ℝ))^(-(γ + 1))) := hfactor
      _ ≤ c2 * (Finset.Icc K N).sum (fun k => ((k : ℝ))^(-(γ + 1))) := hmul1
      _ ≤ c2 * (2 / t) := hmul2
  have hassoc : c2 * (2 / t) = c2 * 2 / t := by rw [mul_div_assoc]
  linarith

/-! ### List-form scheduler invariant

The form preferred by the scheduler bookkeeping uses a `List (ℕ × ℝ)` of
`(birthIdx, width)` pairs. The list version follows from the finset version
by mapping the list to a finset of birth indices and showing the list-sum
equals the finset-sum (assuming distinct birth indices). -/

/-- Cumulative-width bound over a list of `(birthIdx, width)` pairs.

    The list represents the normal boxes added by the scheduler at iterations
    `K, K+1, …, N`. Each pair `(k, w_k)` has a *distinct* birth index `k` in
    `Icc K N`, and satisfies the calibrated normal-width law
        `0 ≤ w_k ≤ c_2 · k^{-(γ+1)}`.

    Conclusion: the total width is bounded by `c_2 · 2 / t`. -/
theorem normal_widths_telescope_bound
    {γ : ℝ} (hγ1 : 1 < γ) (hγ2 : γ < 3/2)
    {K N : ℕ} (hK2 : 2 ≤ K) (hKN : K ≤ N)
    {t : ℝ} (ht : 1 ≤ t)
    (hKt : ((K - 1 : ℕ) : ℝ) ≥ t^(1/γ))
    {c2 : ℝ} (hc2 : 0 ≤ c2)
    (boxes : List (ℕ × ℝ))
    (h_birthRange : ∀ p ∈ boxes, K ≤ p.1 ∧ p.1 ≤ N)
    (h_distinct : (boxes.map Prod.fst).Nodup)
    (h_widthLaw : ∀ p ∈ boxes, 0 ≤ p.2 ∧ p.2 ≤ c2 * ((p.1 : ℝ))^(-(γ + 1)))
    : (boxes.map Prod.snd).sum ≤ c2 * 2 / t := by
  -- We build the Finset S = (boxes.map Prod.fst).toFinset of all birth indices.
  -- Since birth indices are distinct, the List-sum of widths equals the
  -- finset-sum of (one of the matching widths). Then apply the finset bound.
  set Sl : List ℕ := boxes.map Prod.fst with hSl_def
  set S : Finset ℕ := Sl.toFinset with hS_def
  -- (1) Subset condition.
  have hS_subset : S ⊆ Finset.Icc K N := by
    intro k hk
    simp only [hS_def, hSl_def, List.mem_toFinset, List.mem_map] at hk
    obtain ⟨p, hp_mem, hp_eq⟩ := hk
    have ⟨hKp, hpN⟩ := h_birthRange p hp_mem
    rw [Finset.mem_Icc]
    exact ⟨hp_eq ▸ hKp, hp_eq ▸ hpN⟩
  -- (2) Pointwise bound on the second coordinate.
  have hwlaw_pt : ∀ p ∈ boxes, p.2 ≤ c2 * ((p.1 : ℝ))^(-(γ + 1)) :=
    fun p hp => (h_widthLaw p hp).2
  -- (3) List-sum step: bound the list of widths by the list of c2·b^{-(γ+1)}.
  have hlist_le : (boxes.map Prod.snd).sum
                  ≤ (boxes.map (fun p => c2 * ((p.1 : ℝ))^(-(γ + 1)))).sum :=
    List.sum_le_sum hwlaw_pt
  -- Define the bound function explicitly with type ℕ → ℝ.
  let f : ℕ → ℝ := fun k => c2 * ((k : ℝ))^(-(γ + 1))
  -- (4) The list (boxes.map (fun p => f p.1)) is the same as
  --     ((boxes.map Prod.fst).map f), via List.map_map.
  have hmap_eq : (boxes.map (fun p : ℕ × ℝ => f p.1)).sum
                = (Sl.map f).sum := by
    congr 1
    rw [hSl_def, List.map_map]
  -- (5) Convert the list-sum of `Sl.map f` into finset-sum on `S = Sl.toFinset`,
  -- using `List.prod_toFinset`'s additive twin.
  have hSl_nodup : Sl.Nodup := hSl_def ▸ h_distinct
  have hlist_to_finset :
      (Sl.map f).sum = S.sum f := by
    rw [hS_def, ← List.sum_toFinset f hSl_nodup]
  -- (6) Apply the finset bound, expanding f.
  have hsum_finset_bound : S.sum f ≤ c2 * 2 / t := by
    have : S.sum f = S.sum (fun k => c2 * ((k : ℝ))^(-(γ + 1))) := rfl
    rw [this]
    apply normal_widths_finset_bound hγ1 hγ2 hK2 hKN ht hKt hc2 S hS_subset
    intro k _hk
    refine ⟨?_, le_refl _⟩
    -- 0 ≤ c2 · k^{-(γ+1)}
    have hpos : 0 ≤ ((k : ℝ))^(-(γ + 1)) :=
      Real.rpow_nonneg (Nat.cast_nonneg k) _
    exact mul_nonneg hc2 hpos
  -- Combine.
  have hbox_eq : (boxes.map (fun p => c2 * ((p.1 : ℝ))^(-(γ + 1)))).sum
              = (boxes.map (fun p : ℕ × ℝ => f p.1)).sum := rfl
  calc (boxes.map Prod.snd).sum
      ≤ (boxes.map (fun p => c2 * ((p.1 : ℝ))^(-(γ + 1)))).sum := hlist_le
    _ = (boxes.map (fun p : ℕ × ℝ => f p.1)).sum := hbox_eq
    _ = (Sl.map f).sum := hmap_eq
    _ = S.sum f := hlist_to_finset
    _ ≤ c2 * 2 / t := hsum_finset_bound

end MeirMoser.NormalBoxScheduler
