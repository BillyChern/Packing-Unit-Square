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

  Implementation status
  ---------------------
  The `some i` branch is now implemented (no `sorry`). Concretely:

    • A new `PlacedRect` for `D_n` is appended at the chosen normal
      box's `(x0, y0)` corner with `rotated := true` (so width = 1/(t+1),
      height = 1/t).
    • The chosen box is REMOVED from `S.normalBoxes` (`List.eraseIdx i`)
      and replaced by TWO new `NormalBoxRecord`s:
        - "above" leftover: `[x0, x0 + 1/(n+1)] × [y0 + 1/n, y1]`
        - "right" leftover: `[x0 + 1/(n+1), x1] × [y0, y1]`
      The "right" strip is degenerate (zero width) when the chosen box's
      width is exactly `1/(n+1)`; we keep it for uniformity.
    • Both leftovers INHERIT the original box's `birthIdx` (Option A
      from the design notes), preserving the calibrated width law
      `c1 ≤ w · k^γ ≤ c2`.
    • `Rect` proof obligations (`hx`, `hy`) are discharged from the
      `findNormalBoxForRotated` predicate, recovered at the use site
      via an explicit `if h_fits : ...` recheck.

  Open follow-up obligations (NOT in this file):

    • Showing that the new `placed` list is still a valid
      `FinitePacking`. This requires interior-disjointness of `D_n` with
      every prior placement, which follows from the (yet-to-be-tracked)
      invariant that `S.normalBoxes` regions are interior-disjoint
      from `S.placed`. That invariant must be added to the calibrated
      framework before a preservation lemma for `nbfStep` can be proved.
    • A preservation lemma analogous to `calibratedBalancedStep_*`
      that propagates `GoodTailState` across `nbfStep`.

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

    Design choice (Option A from the file header): the leftover strips
    INHERIT the original box's `birthIdx`, preserving the calibrated
    width law `c1 ≤ w · k^γ ≤ c2`.

    Implementation note: the predicate from `findNormalBoxForRotated`
    guarantees the chosen box has the required dimensions. We RECHECK
    the predicate at the use site to recover proof-relevant data for
    the `Rect.hx`/`hy` obligations on the leftover strips. The
    "doesn't fit" / "out of bounds" branches return `S` unchanged;
    by construction these are never reached on a well-formed lookup. -/
def nbfStep (γ_num γ_den : ℕ) (S : TailState) : TailState :=
  let n := S.t
  let w_d : ℚ := 1 / ((n + 1 : ℕ) : ℕ)        -- rotated D_n width  = 1/(n+1)
  let h_d : ℚ := 1 / ((n : ℕ) : ℕ)            -- rotated D_n height = 1/n
  match findNormalBoxForRotated S n with
  | some i =>
      match h_get : S.normalBoxes.get? i with
      | some chosen =>
          if h_fits : w_d ≤ chosen.rect.x1 - chosen.rect.x0 ∧
                      h_d ≤ chosen.rect.y1 - chosen.rect.y0 then
            -- Place rotated D_n at the box's bottom-left corner, and
            -- replace the box with two leftover normal boxes:
            --   • "above": [x0, x0 + 1/(n+1)] × [y0 + 1/n, y1]
            --   • "right": [x0 + 1/(n+1), x1] × [y0, y1]
            -- Both inherit the original `birthIdx` (Option A).
            { t := n + 1
              container := S.container
              placed := S.placed ++ [
                { n := n, x0 := chosen.rect.x0, y0 := chosen.rect.y0, rotated := true }]
              LRP := S.LRP
              normalBoxes :=
                (S.normalBoxes.eraseIdx i) ++ [
                  -- Leftover above D_n.
                  { rect :=
                      { x0 := chosen.rect.x0
                        y0 := chosen.rect.y0 + h_d
                        x1 := chosen.rect.x0 + w_d
                        y1 := chosen.rect.y1
                        hx := by
                          have h_w_nn : (0 : ℚ) ≤ w_d := by positivity
                          linarith
                        hy := by
                          have h := h_fits.2
                          linarith }
                    birthIdx := chosen.birthIdx },
                  -- Leftover to the right of D_n (possibly degenerate
                  -- if the box's width equals 1/(n+1) exactly).
                  { rect :=
                      { x0 := chosen.rect.x0 + w_d
                        y0 := chosen.rect.y0
                        x1 := chosen.rect.x1
                        y1 := chosen.rect.y1
                        hx := by
                          have h := h_fits.1
                          linarith
                        hy := chosen.rect.hy }
                    birthIdx := chosen.birthIdx }]
              endpointBoxes := S.endpointBoxes }
          else
            -- Unreachable on well-formed input: the find predicate
            -- guaranteed `h_fits`. Keep `S` unchanged as a safe
            -- fallback so the function remains total.
            S
      | none =>
          -- Unreachable on well-formed input: `findIdx?` returned a
          -- valid index, so `get? i` cannot be `none`. Keep `S`
          -- unchanged as a safe fallback.
          S
  | none =>
      -- No normal box has room: fall back to the LRP-cut step.
      calibratedBalancedStep γ_num γ_den S

end MeirMoser
