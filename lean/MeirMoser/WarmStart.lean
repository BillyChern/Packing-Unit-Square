/-
  WarmStart: the calibrated tail theorem (statement only).

  We bundle the diagonal extraction into the theorem statement, so the axiom
  produces a full infinite packing into (1+ε)·container directly. This matches
  the research-mathematical statement (the "tail theorem" in the Concrete
  Mathematics 2.37 attack).

  When this axiom is replaced by a Lean proof, that proof must assemble:
    - LRP.lean       (balanced LRP aspect control)
    - Cellification.lean
    - EndpointPotential.lean
    - NormalBoxes.lean (the irrational sum bound for normal-box widths)
    - SchedulerInduction.lean (a scheduler-induction lemma + diagonal extraction)
-/
import MeirMoser.CalibratedScheduler
import MeirMoser.LRP
import MeirMoser.Cellification
import MeirMoser.EndpointPotential

namespace MeirMoser

/-- The Moser sequence dimensions: D_n has size 1/n × 1/(n+1). -/
def MoserDim (n : ℕ) : ℚ × ℚ :=
  if n = 0 then (0, 0) else (1 / (n : ℕ), 1 / ((n + 1 : ℕ) : ℕ))

/-- A `(1+ε)`-expanded container. Uses `max 0 ε` internally; called with ε > 0. -/
def expandedContainer (ε : ℚ) (C : Rect) : Rect :=
  let ε' := max 0 ε
  { x0 := C.x0, y0 := C.y0,
    x1 := C.x1 + ε' * (C.x1 - C.x0),
    y1 := C.y1 + ε' * (C.y1 - C.y0),
    hx := by
      have h := C.hx
      have hε' : 0 ≤ max 0 ε := le_max_left 0 ε
      have hxpos : 0 ≤ C.x1 - C.x0 := by linarith
      have : 0 ≤ max 0 ε * (C.x1 - C.x0) := mul_nonneg hε' hxpos
      linarith
    hy := by
      have h := C.hy
      have hε' : 0 ≤ max 0 ε := le_max_left 0 ε
      have hypos : 0 ≤ C.y1 - C.y0 := by linarith
      have : 0 ≤ max 0 ε * (C.y1 - C.y0) := mul_nonneg hε' hypos
      linarith }

/-- An infinite "Moser packing" of `D_n` for `n ≥ start` into `container`. -/
def MoserPacksFrom (start : ℕ) (container : Rect) : Prop :=
  ∃ packing : ℕ → PlacedRect,
    -- For every n ≥ start: packing n is a validly-dimensioned D_n
    (∀ n ≥ start, (packing n).n = n ∧ (packing n).validDims) ∧
    -- All placed inside container
    (∀ n ≥ start, container.contains (packing n).toRect) ∧
    -- Pairwise disjoint
    (∀ m n, start ≤ m → start ≤ n → m ≠ n →
      Rect.interiorDisjoint (packing m).toRect (packing n).toRect)

/-- An infinite "Moser packing" of `D_n` for `n ≥ start` into `container` that
    additionally avoids (interior-disjoint from) every rectangle in the
    external `avoid` list. This is the form produced by the calibrated
    scheduler: the tail packing is constructed to dodge the already-placed
    prefix. -/
def MoserPacksFromAvoid (start : ℕ) (container : Rect) (avoid : List PlacedRect) : Prop :=
  ∃ packing : ℕ → PlacedRect,
    (∀ n ≥ start, (packing n).n = n ∧ (packing n).validDims) ∧
    (∀ n ≥ start, container.contains (packing n).toRect) ∧
    (∀ m n, start ≤ m → start ≤ n → m ≠ n →
      Rect.interiorDisjoint (packing m).toRect (packing n).toRect) ∧
    (∀ n ≥ start, ∀ P ∈ avoid,
      Rect.interiorDisjoint (packing n).toRect P.toRect)

/-- The "Avoid" version weakens to the plain `MoserPacksFrom` by forgetting
    the avoid clause. -/
theorem MoserPacksFromAvoid.toMoserPacksFrom
    {start : ℕ} {container : Rect} {avoid : List PlacedRect}
    (h : MoserPacksFromAvoid start container avoid) :
    MoserPacksFrom start container := by
  rcases h with ⟨packing, h_dims, h_inside, h_disj, _⟩
  exact ⟨packing, h_dims, h_inside, h_disj⟩

/-
  Calibrated tail theorem (formerly axiomatized here).

  The original wholesale axiom `calibrated_tail_theorem` has been removed
  and replaced by the proved theorem
  `calibrated_tail_theorem_from_smaller_axiom` in
  `CalibratedTailReduction.lean`, which depends only on the smaller axiom
  `good_state_implies_all_steps_succeed` plus the proved lemmas in
  `CalibratedTailProof.lean`.
-/

end MeirMoser
