/-
  StrengthenedAbsorberStep.lean: strengthened absorber semantics
  layered on top of the rate-limited normal-box-first scheduler.

  Why this file exists
  --------------------
  The rate-limited absorber of `RateLimitedNbfStep.lean` consumes the
  chosen endpoint *whole* and discards everything except the placed
  rotated `D_t`. That is a structurally simple choice — it makes the
  endpoint semiperimeter potential strictly decrease — but it is also
  wasteful: whatever clean strip is left over after carving `D_t` out
  of the endpoint is silently dropped.

  The "strengthened absorber" specified in
  `docs/22-strengthened-absorber.md` partitions the L-shaped residual
  region of the consumed endpoint into two clean rectangular strips
  `H` (horizontal) and `V` (vertical), and applies a sliver test
  to each strip:

    • If the strip's aspect ratio is bounded (≤ ρ_*), the strip is
      "fat enough" to be promoted into a fresh normal box — it can
      host future `D_s` events for `s ≥ t`, so it is added to the
      `normalBoxes` queue.
    • Otherwise the strip is a sliver: too thin and long to ever
      accept another rotated detail. It is *discarded*, and its
      area is added to a global accumulator `discardTotal`.

  This file gives a Lean-level realisation of that rule. Since
  `TailState` does not have a `discardTotal` field, we thread it
  alongside as a `ℚ` value, mirroring the existing convention of
  threading the rate-limit counter `m : ℕ` alongside `S`.

  External shape of the function
  ------------------------------
  `strengthenedRateLimitedStep` takes a triple
    `(S : TailState, m : ℕ, w : ℚ)`
  and returns the same shape:
    `(S', m', w')`
  where:
    • `S'` is the new tail state,
    • `m'` is the new rate-limit counter (same convention as
      `rateLimitedNbfStep`: advances by 1 inside the cycle, resets
      to 0 at the cycle boundary),
    • `w' = w + (sum of areas of any strips that failed the sliver
      test in this step). In particular `w' ≥ w` always, i.e. the
      discard total is monotone non-decreasing.

  Sliver threshold
  ----------------
  We use the simple integer aspect threshold `ρ_* := 4`, encoded as
  `maxSide ≤ 4 · minSide`. This is decidable on `ℚ`, avoids any
  real-power reasoning, and matches the spirit of the paper-side
  threshold `ρ_* = R = 2`: with margin to spare, since R = 2 is the
  LRP aspect bound from N7 and 4 is comfortably looser.

  The exact threshold value is not load-bearing for the structural
  lemmas of this file; only `discardTotal` monotonicity, the
  endpoint-count bound, and `t`-advance in the absorber branch
  matter for the cumulative-LRP-cut framework that motivates this
  file. A finer bound on the per-step discard area is left to a
  follow-up file.

  Status
  ------
  Sorry-free. Three structural lemmas are proved:
    • `strengthenedRateLimitedStep_t_advances_absorber`: in the
      absorber-success branch, `t` advances by 1 and the rate-limit
      counter resets to 0.
    • `strengthenedRateLimitedStep_discard_monotone`: the discard
      total is non-decreasing across any single step, in any branch.
    • `strengthenedRateLimitedStep_endpoint_count_bound`: after one
      step, `endpointBoxes.length ≤ pre.endpointBoxes.length` (the
      strengthened absorber never grows the endpoint queue, since
      promoted strips go to `normalBoxes`; the non-absorber
      branches delegate to `nbfStep`/`calibratedBalancedStep`,
      both of which preserve `endpointBoxes` exactly).

  Relationship to the rest of the framework
  -----------------------------------------
    • Builds on `rateLimitedNbfStep` and re-uses
      `findEndpointForRotated`, `kTarget` from `RateLimitedNbfStep.lean`.
    • The non-absorber branches delegate to `rateLimitedNbfStep`
      directly — the strengthening only changes the absorber-success
      branch.
    • The promoted strips inherit the freshly-fired `t` as their
      `birthIdx`; this matches the §10.3 N3 "promoted-strip" rule
      from the paper-side notes (with the caveat (R2) flagged in
      doc 22 §6.2 that a virtual birth index may eventually be
      preferred for cleaner amortisation).
-/
import MeirMoser.RateLimitedNbfStep
import MeirMoser.NormalBoxFirstStep
import MeirMoser.CalibratedScheduler
import MeirMoser.CalibratedStripe
import Mathlib.Tactic

namespace MeirMoser

/-- Aspect-ratio sliver threshold used by the strengthened absorber.

    A rectangle `R` passes the sliver test iff `maxSide ≤ ρ_* · minSide`
    where we take `ρ_* := 4`. Strips that fail are discarded; strips
    that pass are promoted to fresh normal boxes.

    The threshold is conservative (the paper's calibrated value is
    `ρ_* = R = 2`); a looser threshold here only means *more* strips
    are promoted (none are needlessly discarded), which is harmless
    for the structural correctness of the step. -/
def sliverThreshold : ℚ := 4

/-- Whether a rectangle is "fat enough" to be promoted to a normal
    box: equivalent to `aspect(R) ≤ sliverThreshold`. Decidable. -/
def Rect.isFat (R : Rect) : Bool :=
  decide (R.maxSide ≤ sliverThreshold * R.minSide)

/-- An empty rectangle has zero area, so even if it's classified as
    a "sliver" the accounting cost is zero. The two strips below can
    legitimately be empty when the absorbed endpoint exactly fits the
    rotated `D_t`. -/
def Rect.isEmpty (R : Rect) : Bool :=
  decide (R.x0 = R.x1 ∨ R.y0 = R.y1)

/-- The horizontal strip `H` of the L-shaped residual after placing
    rotated `D_t` (with width `1/(t+1)`, height `1/t`) at the
    bottom-left corner of `chosen`.

    Geometry:
      H = [chosen.x0,  chosen.x0 + 1/(t+1)] × [chosen.y0 + 1/t, chosen.y1]
      (region directly above `D_t`).

    The strip is well-formed (i.e. the `Rect` invariants `hx`, `hy`
    hold) provided the absorber predicate `h_fits` is satisfied. -/
def hStrip (chosen : Rect) (t : ℕ) (h_fits :
      (1 : ℚ) / ((t + 1 : ℕ) : ℕ) ≤ chosen.x1 - chosen.x0 ∧
      (1 : ℚ) / ((t : ℕ) : ℕ)     ≤ chosen.y1 - chosen.y0) : Rect :=
  let w_d : ℚ := 1 / ((t + 1 : ℕ) : ℕ)
  let h_d : ℚ := 1 / ((t : ℕ) : ℕ)
  { x0 := chosen.x0
    y0 := chosen.y0 + h_d
    x1 := chosen.x0 + w_d
    y1 := chosen.y1
    hx := by
      have h_w_nn : (0 : ℚ) ≤ w_d := by positivity
      linarith
    hy := by
      have h := h_fits.2
      linarith }

/-- The vertical strip `V` of the L-shaped residual after placing
    rotated `D_t` at the bottom-left corner of `chosen`.

    Geometry:
      V = [chosen.x0 + 1/(t+1), chosen.x1] × [chosen.y0, chosen.y1]
      (region to the right of `D_t`, but spanning the full original
      height; this slightly over-covers the L-shape but matches the
      §10.3 simple two-strip dissection used in `nbfStep`). -/
def vStrip (chosen : Rect) (t : ℕ) (h_fits :
      (1 : ℚ) / ((t + 1 : ℕ) : ℕ) ≤ chosen.x1 - chosen.x0 ∧
      (1 : ℚ) / ((t : ℕ) : ℕ)     ≤ chosen.y1 - chosen.y0) : Rect :=
  let w_d : ℚ := 1 / ((t + 1 : ℕ) : ℕ)
  { x0 := chosen.x0 + w_d
    y0 := chosen.y0
    x1 := chosen.x1
    y1 := chosen.y1
    hx := by
      have h := h_fits.1
      linarith
    hy := chosen.hy }

/-- Local helper: classify a strip and return its contribution to
    `(promotedNormalBoxes, addedDiscardArea)`. A fat strip becomes a
    `NormalBoxRecord` with `birthIdx := t` and contributes 0 area to
    the discard total; a sliver contributes its area and no normal
    box. The strip is also dropped if its area is zero, regardless
    of its aspect (this prevents us from registering degenerate
    boxes when the absorbed endpoint exactly fits `D_t`). -/
def classifyStrip (R : Rect) (t : ℕ) : List NormalBoxRecord × ℚ :=
  if R.isEmpty then
    ([], 0)
  else if R.isFat then
    ([{ rect := R, birthIdx := t }], 0)
  else
    ([], R.area)

/-- Classification preserves area-non-negativity in the discard
    accumulator: `R.area ≥ 0` always, so the second component of
    `classifyStrip` is non-negative. -/
theorem classifyStrip_discard_nonneg (R : Rect) (t : ℕ) :
    0 ≤ (classifyStrip R t).2 := by
  unfold classifyStrip
  split_ifs with h_empty h_fat
  · exact le_refl _
  · exact le_refl _
  · exact R.area_nonneg

/-- One strengthened rate-limited step.

    Triple shape: `(S, m, w) → (S', m', w')` where `w` is the
    cumulative discarded area so far.

    Branching rule (with `n := S.t`, `k := kTarget γ_num γ_den n`):
      • `m + 1 < k`: rate-limit (delegate to `rateLimitedNbfStep`).
        The discard total is unchanged.
      • `m + 1 ≥ k`: absorber slot.
          * If some endpoint fits a rotated `D_n`:
              - place `D_n` at its bottom-left corner;
              - cellify the L-residual into the two strips `H`, `V`;
              - sliver-test each strip: fat strips become new
                normal boxes (added to `S.normalBoxes`); slivers
                contribute their area to the discard accumulator;
              - remove the absorbed endpoint from `S.endpointBoxes`;
              - reset the rate-limit counter to 0.
          * Otherwise, fall back to `rateLimitedNbfStep` (which
            itself falls back to `nbfStep` in this branch).

    The discard total `w'` always satisfies `w' ≥ w` (monotonicity
    is direct from `classifyStrip_discard_nonneg`). -/
def strengthenedRateLimitedStep (γ_num γ_den : ℕ)
    (S : TailState) (m : ℕ) (w : ℚ) : TailState × ℕ × ℚ :=
  let n := S.t
  let k := kTarget γ_num γ_den n
  if m + 1 < k then
    -- Rate-limit branch: delegate, discard total unchanged.
    let p := rateLimitedNbfStep γ_num γ_den S m
    (p.1, p.2, w)
  else
    -- Cycle boundary: absorber slot.
    let w_d : ℚ := 1 / ((n + 1 : ℕ) : ℕ)
    let h_d : ℚ := 1 / ((n : ℕ) : ℕ)
    match findEndpointForRotated S n with
    | some i =>
        match S.endpointBoxes.get? i with
        | some chosen =>
            if h_fits : w_d ≤ chosen.x1 - chosen.x0 ∧
                        h_d ≤ chosen.y1 - chosen.y0 then
              let H := hStrip chosen n h_fits
              let V := vStrip chosen n h_fits
              let (newH, dropH) := classifyStrip H n
              let (newV, dropV) := classifyStrip V n
              ({ t := n + 1
                 container := S.container
                 placed := S.placed ++ [
                   { n := n, x0 := chosen.x0, y0 := chosen.y0,
                     rotated := true }]
                 LRP := S.LRP
                 normalBoxes := S.normalBoxes ++ newH ++ newV
                 endpointBoxes := S.endpointBoxes.eraseIdx i },
                0,
                w + dropH + dropV)
            else
              -- Unreachable on well-formed input.
              let p := rateLimitedNbfStep γ_num γ_den S m
              (p.1, p.2, w)
        | none =>
            -- Unreachable on well-formed input.
            let p := rateLimitedNbfStep γ_num γ_den S m
            (p.1, p.2, w)
    | none =>
        -- No fitting endpoint: fall back, discard total unchanged.
        let p := rateLimitedNbfStep γ_num γ_den S m
        (p.1, p.2, w)

/-- Iterate the strengthened step. -/
def iteratedStrengthened (γ_num γ_den : ℕ) :
    ℕ → TailState × ℕ × ℚ → TailState × ℕ × ℚ
  | 0, p => p
  | (k+1), p =>
      let prev := iteratedStrengthened γ_num γ_den k p
      strengthenedRateLimitedStep γ_num γ_den prev.1 prev.2.1 prev.2.2

@[simp] theorem iteratedStrengthened_zero (γ_num γ_den : ℕ)
    (p : TailState × ℕ × ℚ) :
    iteratedStrengthened γ_num γ_den 0 p = p := rfl

@[simp] theorem iteratedStrengthened_succ
    (γ_num γ_den : ℕ) (k : ℕ) (p : TailState × ℕ × ℚ) :
    iteratedStrengthened γ_num γ_den (k+1) p =
      strengthenedRateLimitedStep γ_num γ_den
        (iteratedStrengthened γ_num γ_den k p).1
        (iteratedStrengthened γ_num γ_den k p).2.1
        (iteratedStrengthened γ_num γ_den k p).2.2 := rfl

/-! ## Helper lemmas about the delegated steps

    These show that `nbfStep`, `calibratedBalancedStep`, and hence
    `rateLimitedNbfStep` all *preserve* the endpoint-box list — they
    are exactly equal to `S.endpointBoxes` (up to `eraseIdx` in the
    absorber sub-branch of `rateLimitedNbfStep`). This is the core
    structural fact that drives the endpoint-count bound below. -/

/-- `calibratedBalancedStep` keeps `endpointBoxes` literally
    unchanged in every sub-branch. Mirrors `calibratedBalancedStep_container`. -/
theorem calibratedBalancedStep_endpointBoxes
    (γ_num γ_den : ℕ) (S : TailState) :
    (calibratedBalancedStep γ_num γ_den S).endpointBoxes =
      S.endpointBoxes := by
  unfold calibratedBalancedStep
  by_cases h : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤ S.LRP.y1 - S.LRP.y0
  · rw [dif_pos h]
    by_cases hcut : cutFromX S = true
    · rw [dif_pos hcut]
    · rw [dif_neg hcut]
  · rw [dif_neg h]

/-- `nbfStep` keeps `endpointBoxes` literally unchanged.

    The proof rewrites the goal using the def of `nbfStep` and a
    case analysis on `findNormalBoxForRotated S n`, then on
    `S.normalBoxes.get? j`, then on the fits predicate. In every
    sub-branch the result either equals `S` or is built with
    `endpointBoxes := S.endpointBoxes`. -/
theorem nbfStep_endpointBoxes (γ_num γ_den : ℕ) (S : TailState) :
    (nbfStep γ_num γ_den S).endpointBoxes = S.endpointBoxes := by
  -- Case-split on the find/get/fits triple via if's behaviour.
  unfold nbfStep
  -- Outer match on findNormalBoxForRotated.
  cases h_find : findNormalBoxForRotated S S.t with
  | none =>
      simp only [h_find]
      exact calibratedBalancedStep_endpointBoxes γ_num γ_den S
  | some j =>
      simp only [h_find]
      cases h_get : S.normalBoxes.get? j with
      | none =>
          simp only [h_get]
      | some chosen =>
          simp only [h_get]
          by_cases h_fits :
              (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ chosen.rect.x1 - chosen.rect.x0 ∧
              (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤ chosen.rect.y1 - chosen.rect.y0
          · simp only [dif_pos h_fits]
          · simp only [dif_neg h_fits]

/-- `rateLimitedNbfStep` length-bound on `endpointBoxes`.

    All non-absorber-success branches reduce to `nbfStep` applied
    to `S`, which preserves `endpointBoxes`. The absorber-success
    branch erases one element, which strictly decreases the
    length. -/
theorem rateLimitedNbfStep_endpointBoxes_length_le
    (γ_num γ_den : ℕ) (S : TailState) (m : ℕ) :
    (rateLimitedNbfStep γ_num γ_den S m).1.endpointBoxes.length
      ≤ S.endpointBoxes.length := by
  by_cases h_cyc : m + 1 < kTarget γ_num γ_den S.t
  · -- Rate-limit branch: equals `nbfStep S`.
    rw [rateLimitedNbfStep_inside_cycle h_cyc]
    show (nbfStep γ_num γ_den S).endpointBoxes.length ≤ _
    rw [nbfStep_endpointBoxes]
  · cases h_find : findEndpointForRotated S S.t with
    | none =>
        rw [rateLimitedNbfStep_absorber_no_fit h_cyc h_find]
        show (nbfStep γ_num γ_den S).endpointBoxes.length ≤ _
        rw [nbfStep_endpointBoxes]
    | some i =>
        cases h_get : S.endpointBoxes.get? i with
        | none =>
            -- Get-none branch.
            simp only [rateLimitedNbfStep, if_neg h_cyc, h_find, h_get]
            show (nbfStep γ_num γ_den S).endpointBoxes.length ≤ _
            rw [nbfStep_endpointBoxes]
        | some chosen =>
            by_cases h_fits :
                (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ chosen.x1 - chosen.x0 ∧
                (1 : ℚ) / ((S.t : ℕ) : ℕ)     ≤ chosen.y1 - chosen.y0
            · -- Absorber-success: count strictly decreases by 1.
              simp only [rateLimitedNbfStep, if_neg h_cyc, h_find, h_get,
                         dif_pos h_fits]
              exact List.length_eraseIdx_le _ _
            · -- Unreachable: delegates to nbfStep.
              simp only [rateLimitedNbfStep, if_neg h_cyc, h_find, h_get,
                         dif_neg h_fits]
              show (nbfStep γ_num γ_den S).endpointBoxes.length ≤ _
              rw [nbfStep_endpointBoxes]

/-! ## Structural lemmas about `strengthenedRateLimitedStep` -/

/-- In the absorber-success branch, `t` advances by 1 and the
    counter resets to 0.

    More precisely: if the cycle boundary is reached
    (`¬ m + 1 < k`), the find-step returns `some i`, the lookup
    `S.endpointBoxes.get? i` returns the endpoint, and the fitting
    predicate `h_fits` is satisfied, then the new state's `t` is
    `S.t + 1` and the new counter is `0`. -/
theorem strengthenedRateLimitedStep_t_advances_absorber
    {γ_num γ_den : ℕ} {S : TailState} {m : ℕ} {w : ℚ}
    (h_cycle : ¬ m + 1 < kTarget γ_num γ_den S.t)
    {i : ℕ} (h_find : findEndpointForRotated S S.t = some i)
    {chosen : Rect} (h_get : S.endpointBoxes.get? i = some chosen)
    (h_fits :
      (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ chosen.x1 - chosen.x0 ∧
      (1 : ℚ) / ((S.t : ℕ) : ℕ)     ≤ chosen.y1 - chosen.y0) :
    (strengthenedRateLimitedStep γ_num γ_den S m w).1.t = S.t + 1 ∧
    (strengthenedRateLimitedStep γ_num γ_den S m w).2.1 = 0 := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [strengthenedRateLimitedStep, if_neg h_cycle, h_find, h_get,
               dif_pos h_fits]

/-- In the rate-limit (non-cycle) branch, the step delegates to
    `rateLimitedNbfStep` and the discard total is unchanged. -/
theorem strengthenedRateLimitedStep_inside_cycle
    {γ_num γ_den : ℕ} {S : TailState} {m : ℕ} {w : ℚ}
    (h_cycle : m + 1 < kTarget γ_num γ_den S.t) :
    strengthenedRateLimitedStep γ_num γ_den S m w =
      ((rateLimitedNbfStep γ_num γ_den S m).1,
       (rateLimitedNbfStep γ_num γ_den S m).2,
       w) := by
  unfold strengthenedRateLimitedStep
  rw [if_pos h_cycle]

/-- In the absorber branch with no fitting endpoint, the step
    falls back to `rateLimitedNbfStep` and the discard total is
    unchanged. -/
theorem strengthenedRateLimitedStep_absorber_no_fit
    {γ_num γ_den : ℕ} {S : TailState} {m : ℕ} {w : ℚ}
    (h_cycle : ¬ m + 1 < kTarget γ_num γ_den S.t)
    (h_find : findEndpointForRotated S S.t = none) :
    strengthenedRateLimitedStep γ_num γ_den S m w =
      ((rateLimitedNbfStep γ_num γ_den S m).1,
       (rateLimitedNbfStep γ_num γ_den S m).2,
       w) := by
  unfold strengthenedRateLimitedStep
  rw [if_neg h_cycle]
  simp [h_find]

/-- The discard total is non-decreasing across any single
    strengthened step.

    In the rate-limit and no-fit branches the discard total is
    literally unchanged. In the absorber-success branch it
    increases by `dropH + dropV`, both of which are non-negative
    by `classifyStrip_discard_nonneg`. -/
theorem strengthenedRateLimitedStep_discard_monotone
    (γ_num γ_den : ℕ) (S : TailState) (m : ℕ) (w : ℚ) :
    w ≤ (strengthenedRateLimitedStep γ_num γ_den S m w).2.2 := by
  by_cases h_cycle : m + 1 < kTarget γ_num γ_den S.t
  · -- Rate-limit branch: discard total unchanged.
    rw [strengthenedRateLimitedStep_inside_cycle h_cycle]
  · -- Cycle boundary: examine each sub-branch.
    cases h_find : findEndpointForRotated S S.t with
    | none =>
        rw [strengthenedRateLimitedStep_absorber_no_fit h_cycle h_find]
    | some i =>
        cases h_get : S.endpointBoxes.get? i with
        | none =>
            -- Get returned none; falls back, discard unchanged.
            simp only [strengthenedRateLimitedStep, if_neg h_cycle, h_find, h_get]
            exact le_refl w
        | some chosen =>
            by_cases h_fits :
                (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ chosen.x1 - chosen.x0 ∧
                (1 : ℚ) / ((S.t : ℕ) : ℕ)     ≤ chosen.y1 - chosen.y0
            · -- Absorber-success branch.
              have hH := classifyStrip_discard_nonneg
                  (hStrip chosen S.t h_fits) S.t
              have hV := classifyStrip_discard_nonneg
                  (vStrip chosen S.t h_fits) S.t
              simp only [strengthenedRateLimitedStep, if_neg h_cycle, h_find,
                         h_get, dif_pos h_fits]
              -- Goal reduces to: w ≤ w + dropH + dropV.
              linarith
            · -- Unreachable; discard unchanged.
              simp only [strengthenedRateLimitedStep, if_neg h_cycle, h_find,
                         h_get, dif_neg h_fits]
              exact le_refl w

/-- The number of endpoint boxes never grows across a single
    strengthened step.

    In the rate-limit and no-fit branches this reduces to
    `rateLimitedNbfStep_endpointBoxes_length_le`. In the
    absorber-success branch the count strictly decreases by 1
    (the chosen endpoint is removed; promoted strips go to
    `normalBoxes`, not `endpointBoxes`).

    The bound is stated as `≤ S.endpointBoxes.length`. -/
theorem strengthenedRateLimitedStep_endpoint_count_bound
    (γ_num γ_den : ℕ) (S : TailState) (m : ℕ) (w : ℚ) :
    (strengthenedRateLimitedStep γ_num γ_den S m w).1.endpointBoxes.length
      ≤ S.endpointBoxes.length := by
  by_cases h_cycle : m + 1 < kTarget γ_num γ_den S.t
  · -- Rate-limit branch.
    rw [strengthenedRateLimitedStep_inside_cycle h_cycle]
    exact rateLimitedNbfStep_endpointBoxes_length_le γ_num γ_den S m
  · -- Cycle boundary.
    cases h_find : findEndpointForRotated S S.t with
    | none =>
        rw [strengthenedRateLimitedStep_absorber_no_fit h_cycle h_find]
        exact rateLimitedNbfStep_endpointBoxes_length_le γ_num γ_den S m
    | some i =>
        cases h_get : S.endpointBoxes.get? i with
        | none =>
            -- Get returned none; falls back.
            simp only [strengthenedRateLimitedStep, if_neg h_cycle, h_find, h_get]
            exact rateLimitedNbfStep_endpointBoxes_length_le γ_num γ_den S m
        | some chosen =>
            by_cases h_fits :
                (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ chosen.x1 - chosen.x0 ∧
                (1 : ℚ) / ((S.t : ℕ) : ℕ)     ≤ chosen.y1 - chosen.y0
            · -- Absorber-success: endpoint count strictly decreases by 1.
              simp only [strengthenedRateLimitedStep, if_neg h_cycle, h_find,
                         h_get, dif_pos h_fits]
              exact List.length_eraseIdx_le _ _
            · -- Unreachable; delegate.
              simp only [strengthenedRateLimitedStep, if_neg h_cycle, h_find,
                         h_get, dif_neg h_fits]
              exact rateLimitedNbfStep_endpointBoxes_length_le γ_num γ_den S m

end MeirMoser
