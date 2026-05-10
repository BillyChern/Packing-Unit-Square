/-
  Certificate scaffolding: predicates and decidable checks for warm-start
  certificates exported by the Python pipeline.

  At this level we just expose `FinitePacking` and helper functions.
-/
import MeirMoser.Geometry
import MeirMoser.FinitePacking

namespace MeirMoser

/-- Convenience wrapper for a candidate "warm-start" certificate state.
    Free regions are omitted at this layer; certificates check only the placed
    rectangles' validity. The four GoodTailState invariants (LRP, normal,
    endpoint, normal-width) are formalized in `CalibratedScheduler.lean`. -/
structure FiniteCertificate where
  container : Rect
  placed : List PlacedRect
deriving Repr

/-- Decidable validity of a `FiniteCertificate`. -/
def FiniteCertificate.valid (c : FiniteCertificate) : Prop :=
  FinitePacking c.container c.placed

instance (c : FiniteCertificate) : Decidable (FiniteCertificate.valid c) := by
  unfold FiniteCertificate.valid; exact inferInstance

end MeirMoser
