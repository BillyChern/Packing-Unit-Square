/-
  NormalBoxes.lean: tail-sum bound for normal-box widths.

  The integral comparison route uses Mathlib's `tsum_le_integral_Ici`-style
  lemmas. To keep this self-contained and ELEMENTARY, we instead prove the
  bound by **telescoping**.

  Lemma (telescoping): for γ > 0 and integer K ≥ 1,
       Σ_{k=K+1}^∞ k^{-γ-1} ≤ K^{-γ} / γ.

  Proof: from k^{-γ} - (k+1)^{-γ} ≥ γ · (k+1)^{-γ-1} (mean-value bound,
  which simplifies via (k+1)^{γ+1} - k·(k+1)^γ ≥ γ algebra).
  Telescoping the LHS gives K^{-γ}.

  We avoid Mathlib's integral library by using only `Real.rpow` algebra.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace MeirMoser.NormalBoxes

open Real

/-- Mean-value-type bound: for x > 0 and 0 < γ ≤ 1,  x^{-γ} - (x+1)^{-γ} ≥ γ · (x+1)^{-γ-1}.

    Proof sketch: f(x) = x^{-γ} has derivative f'(x) = -γ · x^{-γ-1}, which is
    increasing in x for γ > 0. By the mean value theorem applied to [x, x+1],
    f(x) - f(x+1) = -f'(c)·1 = γ·c^{-γ-1} for some c ∈ (x, x+1). Since c < x+1,
    c^{-γ-1} > (x+1)^{-γ-1}, giving the inequality.

    For our purposes we only need this for integer x ≥ 1, but state generally. -/
theorem mvt_bound_rpow_neg
    {γ : ℝ} (hγ : 0 < γ) {x : ℝ} (hx : 0 < x)
    : x^(-γ) - (x+1)^(-γ) ≥ γ * (x+1)^(-(γ+1)) := by
  -- Mean value theorem on f(t) = t^{-γ}, [x, x+1].
  -- ∃ c ∈ (x, x+1) with f'(c) = (f(x+1) - f(x))/1.
  -- f'(c) = -γ · c^{-γ-1}, so x^{-γ} - (x+1)^{-γ} = γ · c^{-γ-1}.
  -- Since c < x+1 and -(γ+1) < 0: c^{-(γ+1)} ≥ (x+1)^{-(γ+1)}.
  set f : ℝ → ℝ := fun t => t^(-γ) with hf_def
  set f' : ℝ → ℝ := fun t => -γ * t^(-γ - 1) with hf'_def
  -- f is differentiable at every t ≠ 0 with derivative -γ * t^(-γ-1).
  have hxlt : x < x + 1 := by linarith
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  -- HasDerivAt for t ↦ t^(-γ) at every point t ≠ 0.
  have hderiv : ∀ t ∈ Set.Ioo x (x + 1), HasDerivAt f (f' t) t := by
    intro t ht
    have ht_pos : 0 < t := lt_trans hx ht.1
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    have h1 : HasDerivAt (fun s : ℝ => s ^ (-γ)) ((-γ) * t ^ (-γ - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl ht_ne)
    exact h1
  -- f is continuous on [x, x+1].
  have hcont : ContinuousOn f (Set.Icc x (x + 1)) := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le hx ht.1
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    exact (Real.continuousAt_rpow_const t (-γ) (Or.inl ht_ne)).continuousWithinAt
  -- Apply Lagrange's MVT.
  obtain ⟨c, hc_mem, hc_eq⟩ :=
    exists_hasDerivAt_eq_slope f f' hxlt hcont hderiv
  -- hc_eq : f' c = (f (x+1) - f x) / ((x+1) - x)
  have hc_pos : 0 < c := lt_trans hx hc_mem.1
  have hc_lt : c < x + 1 := hc_mem.2
  -- Simplify: (x+1) - x = 1.
  have hsub : (x + 1) - x = 1 := by ring
  rw [hsub, div_one] at hc_eq
  -- hc_eq: -γ * c^(-γ-1) = (x+1)^(-γ) - x^(-γ).
  -- So x^(-γ) - (x+1)^(-γ) = γ * c^(-γ-1).
  have hgoal_eq : x^(-γ) - (x + 1)^(-γ) = γ * c^(-γ - 1) := by
    have : f' c = (x + 1)^(-γ) - x^(-γ) := hc_eq
    simp only [hf'_def] at this
    -- this : -γ * c^(-γ-1) = (x+1)^(-γ) - x^(-γ)
    linarith
  rw [hgoal_eq]
  -- Now show: γ * c^(-γ-1) ≥ γ * (x+1)^(-(γ+1)).
  -- This reduces to c^(-(γ+1)) ≥ (x+1)^(-(γ+1)) since γ > 0.
  have h_neg : -(γ + 1) < 0 := by linarith
  have h_eq : -γ - 1 = -(γ + 1) := by ring
  rw [h_eq]
  -- We need: γ * c^(-(γ+1)) ≥ γ * (x+1)^(-(γ+1)).
  apply mul_le_mul_of_nonneg_left _ hγ.le
  -- Show: (x+1)^(-(γ+1)) ≤ c^(-(γ+1)).
  -- Since 0 < c < x+1 and exponent is negative.
  exact (Real.rpow_lt_rpow_of_exponent_neg hc_pos hc_lt h_neg).le

/-- Stronger telescoping bound: Σ_{k=K}^N k^{-γ-1} ≤ ((K-1)^{-γ} - N^{-γ})/γ for K ≥ 2.

    By induction on N. -/
theorem finite_tail_sum_bound_strong
    {γ : ℝ} (hγ : 0 < γ) {K N : ℕ} (hK : 2 ≤ K) (hKN : K ≤ N)
    : (Finset.Icc K N).sum (fun k => ((k : ℝ))^(-(γ+1)))
      ≤ (((K - 1 : ℕ) : ℝ)^(-γ) - (N : ℝ)^(-γ)) / γ := by
  induction N, hKN using Nat.le_induction with
  | base =>
      -- Sum is just K^(-(γ+1)). Need K^(-(γ+1)) ≤ ((K-1)^(-γ) - K^(-γ))/γ.
      rw [Finset.Icc_self, Finset.sum_singleton]
      have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by linarith : 0 < K)
      have hK1pos : (0 : ℝ) < ((K - 1 : ℕ) : ℝ) := by
        have : 0 < K - 1 := by omega
        exact_mod_cast this
      have hKsub : ((K - 1 : ℕ) : ℝ) + 1 = (K : ℝ) := by
        have hK1 : (K - 1 : ℕ) + 1 = K := by omega
        have := congrArg (fun n : ℕ => (n : ℝ)) hK1
        simp only [Nat.cast_add, Nat.cast_one] at this
        exact this
      -- Apply mvt_bound_rpow_neg with x = K-1.
      have hmvt := mvt_bound_rpow_neg hγ hK1pos
      -- hmvt : (K-1)^(-γ) - ((K-1)+1)^(-γ) ≥ γ * ((K-1)+1)^(-(γ+1))
      rw [hKsub] at hmvt
      -- hmvt : γ * K^(-(γ+1)) ≤ (K-1)^(-γ) - K^(-γ)
      rw [le_div_iff₀ hγ]
      linarith
  | succ N hKNind ih =>
      -- Sum over Icc K (N+1) = sum over Icc K N + (N+1)^(-(γ+1)).
      rw [Finset.sum_Icc_succ_top (by linarith : K ≤ N + 1)]
      -- Goal: (sum over Icc K N) + (N+1)^(-(γ+1)) ≤ ((K-1)^(-γ) - (N+1)^(-γ))/γ.
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by linarith : 0 < N)
      have hmvt := mvt_bound_rpow_neg hγ hNpos
      -- hmvt : N^(-γ) - (N+1)^(-γ) ≥ γ * (N+1)^(-(γ+1))
      have hNeq : ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hNeq] at hmvt
      have hineq : ((N + 1 : ℕ) : ℝ)^(-(γ+1)) ≤ ((N : ℝ)^(-γ) - ((N + 1 : ℕ) : ℝ)^(-γ)) / γ := by
        rw [le_div_iff₀ hγ]
        linarith
      calc (Finset.Icc K N).sum (fun k => ((k : ℝ))^(-(γ+1))) + ((N + 1 : ℕ) : ℝ)^(-(γ+1))
          ≤ (((K - 1 : ℕ) : ℝ)^(-γ) - (N : ℝ)^(-γ)) / γ + ((N + 1 : ℕ) : ℝ)^(-(γ+1)) := by
            linarith [ih]
        _ ≤ (((K - 1 : ℕ) : ℝ)^(-γ) - (N : ℝ)^(-γ)) / γ
              + ((N : ℝ)^(-γ) - ((N + 1 : ℕ) : ℝ)^(-γ)) / γ := by linarith [hineq]
        _ = (((K - 1 : ℕ) : ℝ)^(-γ) - ((N + 1 : ℕ) : ℝ)^(-γ)) / γ := by ring

/-- Telescoping bound: Σ_{k=K}^N k^{-γ-1} ≤ (K-1)^{-γ}/γ for K ≥ 2.

    Follows from the stronger bound by dropping the negative term. -/
theorem finite_tail_sum_bound
    {γ : ℝ} (hγ : 0 < γ) {K N : ℕ} (hK : 2 ≤ K) (hKN : K ≤ N)
    : (Finset.Icc K N).sum (fun k => ((k : ℝ))^(-(γ+1)))
      ≤ ((K - 1 : ℕ) : ℝ)^(-γ) / γ := by
  have h := finite_tail_sum_bound_strong hγ hK hKN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by linarith : 0 < N)
  have hNnn : 0 ≤ (N : ℝ)^(-γ) := Real.rpow_nonneg hNpos.le (-γ)
  have hmono : (((K - 1 : ℕ) : ℝ)^(-γ) - (N : ℝ)^(-γ)) / γ
                  ≤ ((K - 1 : ℕ) : ℝ)^(-γ) / γ := by
    apply div_le_div_of_nonneg_right _ hγ.le
    linarith
  linarith

/-- Calibrated bound: for `K ≥ ⌈t^{1/γ}⌉ + 1` and γ ∈ (1, 3/2),
    `Σ_{k=K}^N k^{-γ-1} ≤ 2/t`.

    The `+1` shift accounts for the offset in `finite_tail_sum_bound`. -/
theorem calibrated_normal_sum
    {γ : ℝ} (hγ1 : 1 < γ) (hγ2 : γ < 3/2)
    {K N : ℕ} (hK2 : 2 ≤ K)
    {t : ℝ} (ht : 1 ≤ t)
    (hKt : ((K - 1 : ℕ) : ℝ) ≥ t^(1/γ))
    (hKN : K ≤ N)
    : (Finset.Icc K N).sum (fun k => ((k : ℝ))^(-(γ+1)))
      ≤ 2 / t := by
  have hγ : 0 < γ := by linarith
  have htpos : 0 < t := by linarith
  -- Step 1: from finite_tail_sum_bound: sum ≤ (K-1)^{-γ}/γ.
  have hsum := finite_tail_sum_bound hγ hK2 hKN
  -- Step 2: (K-1)^{-γ} ≤ (t^{1/γ})^{-γ} via rpow_le_rpow_of_nonpos.
  have htpow_pos : 0 < t^(1/γ) := Real.rpow_pos_of_pos htpos _
  have hneg : -γ ≤ 0 := by linarith
  have hbound : ((K - 1 : ℕ) : ℝ)^(-γ) ≤ (t^(1/γ))^(-γ) :=
    Real.rpow_le_rpow_of_nonpos htpow_pos hKt hneg
  -- Step 3: (t^{1/γ})^{-γ} = t^{-1}.
  have hrpow_eq : (t^(1/γ))^(-γ) = t^(-1 : ℝ) := by
    rw [← Real.rpow_mul htpos.le]
    congr 1
    field_simp
  -- Step 4: t^{-1} = 1/t.
  have htinv : t^(-1 : ℝ) = 1 / t := by
    rw [Real.rpow_neg_one]; ring
  -- Combine: (K-1)^{-γ} ≤ 1/t.
  have hKbound : ((K - 1 : ℕ) : ℝ)^(-γ) ≤ 1 / t := by
    rw [hrpow_eq, htinv] at hbound
    exact hbound
  -- Step 5: 1/γ ≤ 1 since γ ≥ 1.
  have hγinv_le_one : 1 / γ ≤ 1 := by
    rw [div_le_one hγ]; linarith
  -- Step 6: (K-1)^{-γ}/γ ≤ (1/t)/γ ≤ (1/t) ≤ 2/t.
  have hKbound_nn : 0 ≤ ((K - 1 : ℕ) : ℝ)^(-γ) := by
    apply Real.rpow_nonneg
    have : 0 < K - 1 := by omega
    exact_mod_cast Nat.zero_le _
  have hstep1 : ((K - 1 : ℕ) : ℝ)^(-γ) / γ ≤ (1 / t) / γ := by
    apply div_le_div_of_nonneg_right hKbound hγ.le
  have hstep2 : (1 / t) / γ ≤ 1 / t := by
    rw [div_le_iff₀ hγ]
    have h1t_nn : 0 ≤ 1 / t := by positivity
    nlinarith
  have hstep3 : (1 : ℝ) / t ≤ 2 / t := by
    rw [div_le_div_iff₀ htpos htpos]
    linarith
  linarith

end MeirMoser.NormalBoxes
