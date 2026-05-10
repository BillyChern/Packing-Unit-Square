/-
  NormalBoxFirstStep.lean: skeleton for the **normal-box-first** scheduler.

  Why this file exists
  --------------------
  The full Meir–Moser tail framework relies on a key structural mechanism that
  the existing `calibratedBalancedStep` does NOT yet implement: when placing
  the next Moser rectangle `D_t` (rotated, with dimensions `1/(t+1) × 1/t`),
  the scheduler should FIRST try to drop `D_t` into one of the EXISTING normal
  boxes accumulated from previous steps, and only fall back to cutting a stripe
  off the LRP if no such box has room.

  Why this matters mathematically
  -------------------------------
  In the simplified `calibratedBalancedStep` every iteration takes a fresh
  stripe of width `a_t = 1/(t+1) + 1/t²` from the LRP. Hence the cumulative
  amount of width "spent" on LRP cuts is

      Σ_{t=N}^{∞} a_t  =  Θ(log)  +  Σ_{t} 1/t²,

  i.e. linear-in-`log(t)` blow-up of LRP cuts, which destroys the area share
  invariant for the LRP and prevents `GoodTailState` from being preserved
  inductively. This is the proximate reason the simplified scheduler cannot
  pack infinitely many tail rectangles in the current Lean development.

  In the FULL Meir–Moser argument the cumulative LRP cuts are only
  `O(t^{1−γ})` (sub-linear in `t`), because MOST `D_t` go into pre-existing
  normal boxes, which are "free" (they were paid for at their birth step).
  Concretely:

    • Each normal box has a calibrated width law `c1 ≤ w · k^γ ≤ c2`,
      so its width is `≈ k^{−γ}` for some birth index `k ≤ t`.
    • The number of `D_t` that can fit horizontally in a normal box of
      width `w_k ≈ k^{−γ}` is roughly `w_k · (t+1) ≈ (t/k)^{1−γ} · k`,
      which is `≫ 1` for `k ≪ t`.
    • Aggregated over all existing normal boxes, the number of `D_t` that
      reuse a normal box swamps the number that have to cut from the LRP,
      and a counting / pigeon-hole argument bounds the cumulative LRP
      cuts by `O(t^{1−γ})`.

  THIS is the missing mechanism that closes the cumulative bound and
  ultimately allows the proof of `GoodTailState` preservation, the absence
  of the `good_state_implies_all_steps_succeed` axiom, and the calibrated
  tail theorem for Moser's rectangle packing problem.

  What this file provides
  -----------------------
  This file defines a SKELETON scheduler `nbfStep : TailState → TailState`
  that:

    (1) Scans `S.normalBoxes` for the first record whose `rect` has both
        width `≥ 1/(t+1)` and height `≥ 1/t` (so rotated `D_t` fits).
    (2) If found, place rotated `D_t` in that normal box at its bottom-left
        corner. The chosen normal box is REMOVED from the list (it has been
        "used up" by `D_t`'s footprint), and the LEFTOVER region inside the
        box (after subtracting `D_t`'s `1/(t+1) × 1/t` footprint) becomes
        one or two NEW normal boxes appended to `S.normalBoxes`.
    (3) If no normal box fits, fall back to `calibratedBalancedStep`, which
        cuts a stripe off the LRP.

  What is intentionally left as `sorry`
  -------------------------------------
  The `some i` branch — actually building the new `TailState` after placing
  `D_t` inside the chosen normal box — is left as `sorry`. The implementation
  is mechanical but non-trivial because:

    • One must build a `PlacedRect` for `D_n` whose corner is the chosen
      normal box's `(x0, y0)`, NOT the LRP's `(x0, y0)`.
    • One must produce a NEW `NormalBoxRecord` for the leftover region
      (typically the strip above `D_n` inside the box, plus possibly the
      strip to the right of `D_n` if the box is wider than `1/(t+1)`),
      and assign each leftover record an appropriate `birthIdx`. The
      birth index for the leftover is a DESIGN DECISION:
        - Option A: keep the original `birthIdx = k` (the leftover is a
          "child" of the same box and inherits its calibration).
        - Option B: use `birthIdx = n` (the leftover was "born" at step
          `n` from the cut).
      The FULL Meir–Moser proof requires Option A so that the calibrated
      width law `c1 ≤ w · k^γ ≤ c2` continues to hold for the leftover
      with the same `k`.
    • One must thread `Rect` proof obligations (`hx`, `hy`) through, which
      requires knowing the box's geometry meets the placement constraints
      (this follows from the `findNormalBoxForRotated` predicate).
    • One must reconstruct a valid `FinitePacking` extension. The new
      `D_n` is interior-disjoint from existing placements because the
      normal box was disjoint from prior placed rectangles by the
      packing invariant on `S`.

  All of this is straightforward case work but requires roughly the same
  amount of Lean as `calibratedBalancedStep`. That implementation is a
  follow-up task; the skeleton here is enough to plumb `nbfStep` into
  the rest of the calibrated framework and to state preservation lemmas.

  Relationship to the existing code
  ---------------------------------
    • `calibratedBalancedStep γ_num γ_den S` — used as the fallback in
      the `none` branch, exactly the existing LRP-cut step.
    • `TailState`, `NormalBoxRecord`, `Rect` — shared structures from
      `MeirMoser.CalibratedScheduler` and `MeirMoser.Geometry`.
-/
import MeirMoser.CalibratedStripe
import MeirMoser.CalibratedScheduler
import Mathlib.Tactic

namespace MeirMoser

/-- Find the FIRST normal box in `S.normalBoxes` whose rectangle has both
    width `≥ 1/(t+1)` and height `≥ 1/t`, i.e. is large enough to host
    a rotated copy of `D_t` (dimensions `1/(t+1) × 1/t`).

    Returns the list-index of the first such box, or `none` if no normal
    box has room. Uses `List.findIdx?` over a `Bool`-valued predicate so
    that the lookup is fully decidable / computable. -/
def findNormalBoxForRotated (S : TailState) (t : ℕ) : Option ℕ :=
  let w_d : ℚ := 1 / ((t + 1 : ℕ) : ℕ)   -- rotated D_t width
  let h_d : ℚ := 1 / ((t : ℕ) : ℕ)       -- rotated D_t height
  S.normalBoxes.findIdx? (fun nb =>
    decide (w_d ≤ nb.rect.x1 - nb.rect.x0 ∧ h_d ≤ nb.rect.y1 - nb.rect.y0))

/-- The normal-box-first calibrated step.

    Behavior:
      • If some existing normal box has room for rotated `D_t`, place
        `D_t` inside that box (this is the "free" branch, no LRP cut).
      • Otherwise, fall back to the LRP-cut step
        `calibratedBalancedStep γ_num γ_den S`.

    The `some i` branch is currently a `sorry` placeholder; see the
    top-of-file documentation for the math obligations and the design
    decision (birth-index inheritance) that the full implementation
    must respect. -/
def nbfStep (γ_num γ_den : ℕ) (S : TailState) : TailState :=
  let n := S.t
  match findNormalBoxForRotated S n with
  | some _i =>
      -- TODO (follow-up task): build the new TailState here.
      --   1. Pop normal box at index `_i` from `S.normalBoxes`.
      --   2. Append `PlacedRect { n := n, x0 := box.rect.x0,
      --                            y0 := box.rect.y0, rotated := true }`
      --      to `S.placed`.
      --   3. Append leftover strip(s) inside the popped box as new
      --      `NormalBoxRecord`s. The leftover above `D_n` is the rect
      --      `[box.x0, box.x0 + 1/(n+1)] × [box.y0 + 1/n, box.y1]`
      --      (or `[box.x0, box.x1] × [box.y0 + 1/n, box.y1]` plus a
      --      side strip, depending on the cut convention chosen).
      --   4. The leftover's `birthIdx` should be the ORIGINAL box's
      --      `birthIdx` so the calibrated width law
      --      `c1 ≤ w · k^γ ≤ c2` carries over.
      --   5. Advance `t` by 1; container, LRP, endpointBoxes unchanged.
      sorry
  | none =>
      -- No normal box has room: fall back to the LRP-cut step.
      calibratedBalancedStep γ_num γ_den S

end MeirMoser
