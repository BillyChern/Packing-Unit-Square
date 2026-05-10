/-
  CalibratedTailReduction.lean (Route A R-A.8): top-level reduction of the
  calibrated tail packing theorem to the much smaller axiom `c_decay_balanced`
  (in `AllStepsSucceedProof.lean`), via the balanced step proof in
  `CalibratedTailProofBalanced.lean`.

  This file replaces the original `axiom good_state_implies_all_steps_succeed`
  + `theorem calibrated_tail_theorem_from_smaller_axiom` pair with a balanced
  version that depends only on `c_decay_balanced` (a strictly smaller and
  more focused analytic claim).

  The new top-level theorem is `calibrated_tail_theorem_from_balanced`.
  Downstream callers (`MainTheorem.lean`, `Certificates/WarmStart*.lean`)
  must supply three additional hypotheses (`h_c_pos`, `h_R_pos`,
  `h_t_large : R ≤ c · t`) that connect the certificate parameters to the
  base-case hypotheses needed by `base_LRP_fits`.
-/
import MeirMoser.SchedulerInduction
import MeirMoser.SchedulerInductionCombine
import MeirMoser.CalibratedTailProof
import MeirMoser.CalibratedTailProofBalanced
import MeirMoser.AllStepsSucceedProof
import MeirMoser.WarmStart

namespace MeirMoser

/-- Top-level calibrated tail theorem (BALANCED step, R-A.8 wiring).

    Assumes:
      - `GoodTailState c R η S widthChecks` (the calibrated invariant);
      - `0 < c`, `0 < R`, and `R ≤ c · S.t` (so `base_LRP_fits` applies at S);
      - `1 ≤ S.t`, `S.LRP ⊆ S.container`, and `S.LRP` is interior-disjoint
        from every prefix placement.

    Derives `MoserPacksFromAvoid S.t S.container S.placed`.

    The proof composes:
      - `good_state_implies_all_steps_succeed_balanced` (proves
        `AllStepsSucceed_balanced S` modulo the smaller analytic axiom
        `c_decay_balanced`), and
      - `calibrated_tail_from_balanced_steps_success` (sorry-free, proves
        the packing from `AllStepsSucceed_balanced` plus the geometric
        preconditions). -/
theorem calibrated_tail_theorem_from_balanced
    (γ_num γ_den : ℕ) (c R η : ℚ)
    (h_γ_in : 1 * γ_den < γ_num ∧ γ_num * 2 < γ_den * 3)
    (S : TailState) (widthChecks : List NormalWidthCheck)
    (h_state : GoodTailState c R η S widthChecks)
    (h_c_pos : 0 < c) (h_R_pos : 0 < R)
    (h_R_ge_one : (1 : ℚ) ≤ R)
    (h_R_squared : R ≤ (R - 1) * (R - 1))
    (h_t_large : (R : ℚ) ≤ c * (S.t : ℕ))
    (h_t_pos : 1 ≤ S.t)
    (h_LRP_in_container : S.container.contains S.LRP)
    (h_LRP_disj : ∀ P ∈ S.placed, Rect.interiorDisjoint S.LRP P.toRect)
    : MoserPacksFromAvoid S.t S.container S.placed :=
  MeirMoser.CalibratedTailProofBalanced.calibrated_tail_from_balanced_steps_success S
    (MeirMoser.AllStepsSucceedProof.good_state_implies_all_steps_succeed_balanced
      S c R η widthChecks h_c_pos h_R_pos h_R_ge_one h_R_squared h_state h_t_large
      (Nat.lt_of_lt_of_le Nat.zero_lt_one h_t_pos)
      h_LRP_in_container h_LRP_disj)
    h_t_pos h_LRP_in_container h_LRP_disj

end MeirMoser
