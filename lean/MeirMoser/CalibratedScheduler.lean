/-
  CalibratedScheduler: the abstract state and the GoodTailState predicate.

  TailState (S):
    t      : current Moser index to place
    LRP    : the large rectangular piece
    normalBoxes : list of (rect, birth_index)
    endpointBoxes : list of rects

  GoodTailState γ c R η (S) means the four calibrated invariants hold:
    (i)   area(LRP) ≥ c / S.t                         (LRP area share)
    (ii)  aspect(LRP) ≤ R                              (LRP aspect bound)
    (iii) Σ semiperim(endpointBoxes) ≤ η               (endpoint potential)
    (iv)  for each (rect, k) in normalBoxes:           (calibrated normal-box width law)
            c1 ≤ rect.width · k^γ ≤ c2

  At the warm-start step t = N, condition (iv) is encoded as a list of
  (k, w_k, c1, c2) checkable triples; we don't build a real-power library here.

  This file gives DEFINITIONS + DECIDABILITY only. The CONDITIONAL theorem
  `good_tail_state_admits_continuation` is stated as a hypothesis to the
  main theorem in `MainTheorem.lean`; its proof is a separate research goal
  (the calibrated tail theorem; see WarmStart.lean for the formal statement).
-/
import MeirMoser.Geometry
import MeirMoser.FinitePacking
import Mathlib.Tactic

namespace MeirMoser

/-- A normal box with its birth index `k`, used to verify the width law. -/
structure NormalBoxRecord where
  rect : Rect
  birthIdx : ℕ
deriving Repr, DecidableEq

/-- A calibrated tail-state at index `t`. -/
structure TailState where
  t : ℕ
  container : Rect
  placed : List PlacedRect
  LRP : Rect
  normalBoxes : List NormalBoxRecord
  endpointBoxes : List Rect
deriving Repr

/-- A pre-computed `(k, w, c1, c2)` constraint for the calibrated normal-box width law:
    we require `c1 ≤ w · k^γ ≤ c2`, but to avoid real-power Lean we instead supply
    integer bounds `c1_bound`, `c2_bound` such that
      c1_bound · k^γ_den_pow ≤ w^γ_den_pow_pre  ≤ c2_bound · k^γ_den_pow
    where γ_den_pow_pre handles the rational exponent γ = γ_num / γ_den.
    For now we keep this lemma operational (decidable) but not formally tied to
    real-power γ; the empirical certificate provides the integer bounds. -/
structure NormalWidthCheck where
  k : ℕ                  -- birth index
  width : ℚ              -- box width
  c1 : ℚ                 -- lower
  c2 : ℚ                 -- upper
  -- We require c1 ≤ width · k_factor ≤ c2 where k_factor approximates k^γ.
  k_factor : ℚ
deriving Repr, DecidableEq

def NormalWidthCheck.holds (n : NormalWidthCheck) : Prop :=
  n.c1 ≤ n.width * n.k_factor ∧ n.width * n.k_factor ≤ n.c2

instance (n : NormalWidthCheck) : Decidable (NormalWidthCheck.holds n) := by
  unfold NormalWidthCheck.holds; exact inferInstance

/-- The four calibrated invariants. -/
def GoodTailState
    (c R η : ℚ) (S : TailState) (widthChecks : List NormalWidthCheck) : Prop :=
  -- (i)  area(LRP) · t ≥ c
  c ≤ S.LRP.area * (S.t : ℚ) ∧
  -- (ii) aspect(LRP) ≤ R, encoded as maxSide ≤ R · minSide
  S.LRP.maxSide ≤ R * S.LRP.minSide ∧
  -- (iii) Σ semiperim(endpoints) ≤ η
  (S.endpointBoxes.map Rect.semiperim).sum ≤ η ∧
  -- (iv) every width check holds
  (∀ wc ∈ widthChecks, wc.holds) ∧
  -- (v) the placed prefix is a valid finite packing
  FinitePacking S.container S.placed

instance (c R η : ℚ) (S : TailState) (wc : List NormalWidthCheck) :
    Decidable (GoodTailState c R η S wc) := by
  unfold GoodTailState; exact inferInstance

end MeirMoser
