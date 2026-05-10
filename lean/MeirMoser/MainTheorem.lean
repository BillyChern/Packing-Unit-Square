/-
  MainTheorem: combine the warm-start certificate with the (sharpened)
  calibrated tail theorem to conclude that the Moser sequence packs into [0,1]².

  Conditional on a SINGLE axiom: `c_decay_balanced`
  (in `AllStepsSucceedProof.lean`). The original `calibrated_tail_theorem`
  axiom and the intermediate `good_state_implies_all_steps_succeed` axiom
  have been reduced to this even smaller analytic claim plus the
  proved `calibrated_tail_from_balanced_steps_success` (in
  `CalibratedTailProofBalanced.lean`) and the proved
  `good_state_implies_all_steps_succeed_balanced` (in
  `AllStepsSucceedProof.lean`, modulo `c_decay_balanced`).

  By tracking the slack budget exactly inside the calibrated framework
  (S_LRP(t) ≥ c/t with bounded cumulative LRP cuts), the tail theorem
  produces a packing into S.container directly, removing the need
  for Martin compactness entirely.
-/
import MeirMoser.WarmStart
import MeirMoser.Certificate
import MeirMoser.CalibratedTailReduction

namespace MeirMoser

/-- The unit square. -/
def unitSquare : Rect :=
  { x0 := 0, y0 := 0, x1 := 1, y1 := 1
    hx := by decide, hy := by decide }

/-- Combine a placed prefix with a tail packing into a single ℕ→PlacedRect.

    The math: the prefix `S.placed` covers indices `1, …, S.t-1` (by
    `h_indices`). The tail provides indices `n ≥ S.t`. The combined packing
    is built piecewise; pairwise disjointness comes from three sources:
      - both indices in the prefix: `h_disjoint_prefix`,
      - both indices in the tail: the inner disjointness of `h_tail`,
      - one each: the avoid clause of `h_tail`.
-/
theorem moser_packs_combine
    (S : TailState) (h_C : S.container = unitSquare)
    (h_prefix : ∀ P ∈ S.placed, P.validDims ∧ unitSquare.contains P.toRect)
    (h_disjoint_prefix : S.placed.Pairwise
      (fun P Q => Rect.interiorDisjoint P.toRect Q.toRect))
    (h_indices : ∀ n, 1 ≤ n → n < S.t →
       ∃ P ∈ S.placed, P.n = n)
    (h_tail : MoserPacksFromAvoid S.t unitSquare S.placed)
    : MoserPacksFrom 1 unitSquare := by
  rcases h_tail with ⟨tailPacking, h_tail_dims, h_tail_inside, h_tail_disj, h_tail_avoid⟩
  -- Choice function for prefix indices: for each n ∈ [1, S.t), pick a
  -- representative placed rectangle with .n = n.
  classical
  -- Build the combined packing.
  let combinedPacking : ℕ → PlacedRect := fun n =>
    if h : 1 ≤ n ∧ n < S.t then
      Classical.choose (h_indices n h.1 h.2)
    else
      tailPacking n
  -- Property of the chosen prefix representative.
  have h_choose : ∀ n (h1 : 1 ≤ n) (h2 : n < S.t),
      (Classical.choose (h_indices n h1 h2)) ∈ S.placed ∧
      (Classical.choose (h_indices n h1 h2)).n = n := by
    intro n h1 h2
    have h := h_indices n h1 h2
    have hspec := Classical.choose_spec h
    exact hspec
  -- Useful shape: combinedPacking n for n in the prefix range.
  have hC_pref : ∀ n (h1 : 1 ≤ n) (h2 : n < S.t),
      combinedPacking n = Classical.choose (h_indices n h1 h2) := by
    intro n h1 h2
    simp [combinedPacking, h1, h2]
  -- Useful shape: combinedPacking n for n outside the prefix range.
  have hC_tail : ∀ n, ¬ (1 ≤ n ∧ n < S.t) → combinedPacking n = tailPacking n := by
    intro n h
    simp [combinedPacking, h]
  -- Membership lemma for the prefix branch.
  have h_pref_mem : ∀ n (h1 : 1 ≤ n) (h2 : n < S.t),
      combinedPacking n ∈ S.placed := by
    intro n h1 h2
    rw [hC_pref n h1 h2]
    exact (h_choose n h1 h2).1
  refine ⟨combinedPacking, ?dims, ?inside, ?disj⟩
  · -- dims
    intro n hn
    by_cases h_lt : n < S.t
    · -- prefix
      have h1 : 1 ≤ n := hn
      rw [hC_pref n h1 h_lt]
      have hmem := (h_choose n h1 h_lt).1
      have hn_eq := (h_choose n h1 h_lt).2
      have hvd := (h_prefix _ hmem).1
      exact ⟨hn_eq, hvd⟩
    · -- tail (n ≥ S.t)
      push_neg at h_lt
      have h_not_pref : ¬ (1 ≤ n ∧ n < S.t) := by
        intro h; exact (Nat.lt_irrefl n) (lt_of_lt_of_le h.2 h_lt)
      rw [hC_tail n h_not_pref]
      exact h_tail_dims n h_lt
  · -- inside
    intro n hn
    by_cases h_lt : n < S.t
    · have h1 : 1 ≤ n := hn
      rw [hC_pref n h1 h_lt]
      have hmem := (h_choose n h1 h_lt).1
      have := (h_prefix _ hmem).2
      exact this
    · push_neg at h_lt
      have h_not_pref : ¬ (1 ≤ n ∧ n < S.t) := by
        intro h; exact (Nat.lt_irrefl n) (lt_of_lt_of_le h.2 h_lt)
      rw [hC_tail n h_not_pref]
      exact h_tail_inside n h_lt
  · -- pairwise disjoint
    intro m n hm hn hmn
    -- Cases on whether m, n are in prefix range.
    by_cases hm_lt : m < S.t
    · by_cases hn_lt : n < S.t
      · -- both in prefix
        have hm1 : 1 ≤ m := hm
        have hn1 : 1 ≤ n := hn
        rw [hC_pref m hm1 hm_lt, hC_pref n hn1 hn_lt]
        -- Use h_disjoint_prefix on the two chosen reps. They could be the
        -- same element in `S.placed` only if their indices m and n are equal,
        -- but we know m ≠ n and the chosen rep has its index = m or n
        -- respectively, hence the two reps are different list entries.
        -- However List.Pairwise gives disjointness between distinct list entries
        -- by their pairwise-relation; we use that any two distinct entries are
        -- interior-disjoint, and our chosen reps have distinct .n fields.
        set P := Classical.choose (h_indices m hm1 hm_lt) with hP
        set Q := Classical.choose (h_indices n hn1 hn_lt) with hQ
        have hPmem : P ∈ S.placed := (h_choose m hm1 hm_lt).1
        have hQmem : Q ∈ S.placed := (h_choose n hn1 hn_lt).1
        have hPn : P.n = m := (h_choose m hm1 hm_lt).2
        have hQn : Q.n = n := (h_choose n hn1 hn_lt).2
        have hPQ_ne : P ≠ Q := by
          intro h_eq
          have : P.n = Q.n := by rw [h_eq]
          rw [hPn, hQn] at this
          exact hmn this
        -- Use Pairwise relation between distinct elements.
        exact h_disjoint_prefix.forall (fun a b h => Rect.interiorDisjoint_symm _ _ h)
          hPmem hQmem hPQ_ne
      · -- m in prefix, n in tail
        push_neg at hn_lt
        have hm1 : 1 ≤ m := hm
        have hn_not_pref : ¬ (1 ≤ n ∧ n < S.t) := by
          intro h; exact (Nat.lt_irrefl n) (lt_of_lt_of_le h.2 hn_lt)
        rw [hC_pref m hm1 hm_lt, hC_tail n hn_not_pref]
        -- We need: (Classical.choose ...) and (tailPacking n) disjoint.
        -- Use h_tail_avoid n (for n ≥ S.t) on the chosen prefix rep.
        set P := Classical.choose (h_indices m hm1 hm_lt) with hP
        have hPmem : P ∈ S.placed := (h_choose m hm1 hm_lt).1
        have h_av := h_tail_avoid n hn_lt P hPmem
        exact Rect.interiorDisjoint_symm _ _ h_av
    · -- m in tail
      push_neg at hm_lt
      have hm_not_pref : ¬ (1 ≤ m ∧ m < S.t) := by
        intro h; exact (Nat.lt_irrefl m) (lt_of_lt_of_le h.2 hm_lt)
      by_cases hn_lt : n < S.t
      · -- m in tail, n in prefix
        have hn1 : 1 ≤ n := hn
        rw [hC_tail m hm_not_pref, hC_pref n hn1 hn_lt]
        set Q := Classical.choose (h_indices n hn1 hn_lt) with hQ
        have hQmem : Q ∈ S.placed := (h_choose n hn1 hn_lt).1
        have h_av := h_tail_avoid m hm_lt Q hQmem
        exact h_av
      · -- both in tail
        push_neg at hn_lt
        have hn_not_pref : ¬ (1 ≤ n ∧ n < S.t) := by
          intro h; exact (Nat.lt_irrefl n) (lt_of_lt_of_le h.2 hn_lt)
        rw [hC_tail m hm_not_pref, hC_tail n hn_not_pref]
        exact h_tail_disj m n hm_lt hn_lt hmn

/-- The MAIN THEOREM (conditional on a warm-start certificate satisfying
    `GoodTailState`): the Moser sequence packs into `[0, 1]²`.

    This version uses `calibrated_tail_theorem_from_balanced`, depending
    only on the *much smaller* axiom `c_decay_balanced` (in
    `AllStepsSucceedProof.lean`).

    Three NEW hypotheses (relative to the previous version):
      - `h_c_pos : 0 < c`,
      - `h_R_pos : 0 < R`,
      - `h_t_large : (R : ℚ) ≤ c * (S.t : ℕ)` — the certificate's `S.t`
        must already satisfy `R ≤ c · t` so that `base_LRP_fits` applies
        at the warm-start state. -/
theorem meir_moser_packing_from_certificate
    (γ_num γ_den : ℕ) (c R η : ℚ)
    (h_γ_in : 1 * γ_den < γ_num ∧ γ_num * 2 < γ_den * 3)
    (S : TailState) (widthChecks : List NormalWidthCheck)
    (h_state : GoodTailState c R η S widthChecks)
    (h_cont_unit : S.container = unitSquare)
    (h_prefix_indices : ∀ n, 1 ≤ n → n < S.t →
       ∃ P ∈ S.placed, P.n = n)
    (h_c_pos : 0 < c)
    (h_R_pos : 0 < R)
    (h_R_ge_one : (1 : ℚ) ≤ R)
    (h_R_squared : R ≤ (R - 1) * (R - 1))
    (h_t_large : (R : ℚ) ≤ c * (S.t : ℕ))
    (h_t_pos : 1 ≤ S.t)
    (h_LRP_in_container : S.container.contains S.LRP)
    (h_LRP_disj : ∀ P ∈ S.placed, Rect.interiorDisjoint S.LRP P.toRect)
    : MoserPacksFrom 1 unitSquare := by
  apply moser_packs_combine S h_cont_unit
  · -- prefix dims + containment
    intro P hP
    rcases h_state with ⟨_, _, _, _, h_fp⟩
    refine ⟨h_fp.2.1 P hP, ?_⟩
    have := h_fp.1 P hP
    rwa [← h_cont_unit]
  · rcases h_state with ⟨_, _, _, _, h_fp⟩
    exact h_fp.2.2
  · exact h_prefix_indices
  · -- tail: use the proved balanced path (modulo balanced_c_share_positive_axiom)
    have h_tail :=
      calibrated_tail_theorem_from_balanced γ_num γ_den c R η h_γ_in
        S widthChecks h_state h_c_pos h_R_pos h_R_ge_one h_R_squared h_t_large
        h_t_pos h_LRP_in_container h_LRP_disj
    rwa [h_cont_unit] at h_tail

end MeirMoser
