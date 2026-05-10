# Route A.5: Calibrated Stripe Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Discharge the residual `MeirMoser.AllStepsSucceedProof.balanced_c_share_positive_axiom` (currently provably-false for the simplified balanced step) by introducing a fully-calibrated step `calibratedBalancedStep` whose stripe width `a_t = 1/(t+1) + t^{-γ}` with γ ∈ (1, 3/2) makes the cumulative LRP-area decay convergent, restoring soundness and yielding a fully axiom-free Lean proof of `meir_moser_packs_unit_square`.

**Architecture:** Add a parallel `calibratedBalancedStep` next to the existing `balancedStep`, prove its four per-step preservations (area, aspect, width-law, FP/containment), then prove a *cumulative* tail-sum bound `Σ a_t · LRP.height_t ≤ c/2` using Mathlib's `Real.summable_one_div_nat_rpow`. The cumulative bound discharges the c-share-positivity invariant inductively, eliminating the residual axiom. Bridge ℝ↔ℚ via concrete rational lower bounds for `t^{-γ}` (e.g. `t^{-4/3} ≥ 1/(t·γceiledCubeRoot(t))`).

**Tech Stack:** Lean 4 v4.15.0, Mathlib v4.15.0 (specifically: `Real.rpow`, `Real.summable_one_div_nat_rpow`, `Mathlib.Analysis.SpecialFunctions.Pow.Real`, `Mathlib.Topology.Algebra.InfiniteSum.Basic`).

---

## Mathematical foundation (read this first)

### Why the simplified step's axiom is false

Per-step LRP area-share decay: `≤ maxSide · (1 + 1/t)`. With `maxSide = Θ(1)` for many iterations, the cumulative sum is `Θ(k)`. This makes `c_share_witness c S k = c − Θ(k) → −∞`, falsifying the axiom.

### Why the calibrated stripe fixes this

Per-step LRP area-share decay with stripe width `a_t = 1/(t+1) + t^{-γ}`:
- The slice removed is `a_t × LRP.shorter_side`.
- Area lost = `a_t · shorter`.

With `area_t · t ≥ c` (the GoodTailState invariant) and aspect ≤ R: `shorter ≤ √(area_t/R)·R = √(R · area_t/1) ≤ √(R · 1) = √R` (loose), but tighter: `shorter ≤ √(area_t)` since `area = shorter · longer ≤ shorter² · R`, so `shorter ≥ √(area/R)`, and `shorter ≤ longer ≤ R · shorter`, so `area ≤ R · shorter²`, hence `shorter ≥ √(area/R)`, and `shorter² ≤ R · area`, and `shorter ≤ √(R · area)`.

So per-step decay: `a_t · √(R · area_t)`. With `area_t ≤ 1`: bounded by `a_t · √R`. Cumulative: `√R · Σ a_t = √R · (Σ 1/(t+1) + Σ t^{-γ})`.

Wait — `Σ 1/(t+1)` still diverges. The trick: use the *tighter* bound `area_t ≤ c/t` (NO — area can be larger). Actually, the framework's tighter bound is that `LRP.height` shrinks: from balanced cuts and `aspect ≤ R`, after k steps the height is bounded by some specific expression. The TRUE deep math:

After step k starting from area_0, the LRP area is bounded by `area_0 - Σ_{j<k} a_{t_j} · shorter_j`. If we want to show `area_k · t_k ≥ c'` for `c' = c/2`, we need cumulative decay ≤ c/2:

`Σ a_{t_j} · shorter_j ≤ c/2`

With `shorter_j ≤ √(R · area_j)` and `area_j ≤ area_0 ≤ c'/t_0 + cumulative_decay ≤ c/t_0 + c/2 ≤ 3c/2` (assuming bounded), we get a self-referential bound. The cleanest closure: prove

`Σ a_{t_j} · shorter_j ≤ √R · area_max · Σ_{j} a_{t_j}` (where `area_max = sup_j √(area_j)`)

But `Σ a_{t_j}` for the simplified piece (`1/(t_j+1)`) diverges. So we need a **separate argument** for the `1/(t_j+1)` part using the area-shrinking effect.

Actually, the research framework's argument: per-step decay = `a_t · shorter` ≤ `(1/(t+1) + t^{-γ}) · √R · √(area)`. Now `area · t ≥ c` so `area ≥ c/t`, and with `area_max ≤ c'/t_min + ...`, the `√area` term is `O(1/√t)`. So:

`a_t · √(R·area) ≈ (1/(t+1) + t^{-γ}) · √(R · c/t)` when area ≈ c/t (the lower bound is tight when GoodTailState is saturated).

`(1/(t+1)) · √(R·c)/√t = √(R·c) / ((t+1)·√t) = O(t^{-3/2})` — summable.
`t^{-γ} · √(R·c)/√t = √(R·c) · t^{-γ-1/2} = O(t^{-11/6})` for γ=4/3 — summable.

Total cumulative decay: `√(R·c) · (Σ t^{-3/2} + Σ t^{-11/6})` — bounded by some `K(R, c, t_0) · √(R·c)`. For sufficiently large `t_0`, `K · √(R·c) ≤ c/2`, allowing the inductive c-share-positive argument to close.

### Key Mathlib facts we'll use

```
Real.rpow : ℝ → ℝ → ℝ                                         -- t^{-γ}
Real.summable_one_div_nat_rpow : 1 < p → Summable (n => 1/n^p)  -- Σ 1/n^p < ∞ for p > 1
Real.tsum_le_of_sum_range_le                                    -- bound by partial sum + tail
Real.rpow_le_rpow_of_exponent_le                                -- monotonicity
```

For the bridge to ℚ, use `Real.rpow ≥ rational_lower_bound` lemmas or work in ℝ throughout the cumulative-bound proof.

---

## File structure

| Path | Est. LoC | Responsibility |
|------|---------|---------------|
| `MeirMoser/CalibratedStripe.lean` | ~250 | Define `calibratedBalancedStep`, basic structural lemmas (container, t-advance, x0/y0/x1/y1) |
| `MeirMoser/CalibratedStripeArea.lean` | ~200 | Per-step area-share lower bound for the calibrated stripe |
| `MeirMoser/CalibratedStripeAspect.lean` | ~200 | Aspect ≤ R preserved under calibrated stripe |
| `MeirMoser/CalibratedStripeAux.lean` | ~150 | Endpoint + width-check preservation + new normal box width |
| `MeirMoser/CalibratedStripeContainment.lean` | ~250 | t > 0, FP, container, LRP-disjointness propagation (mirrors `SchedulerInductionBalancedContainment.lean`) |
| `MeirMoser/CalibratedStripeCombine.lean` | ~80 | `step_preserves_GoodTailState_calibrated` |
| `MeirMoser/CalibratedStripeRpowBound.lean` | ~300 | Bridge: `Real.rpow`-based bounds, rational lower bounds for `t^{-γ}` |
| `MeirMoser/CalibratedStripeCumulative.lean` | ~400 | THE KEY FILE: cumulative tail-sum bound `Σ a_t · shorter_t ≤ c/2` |
| `MeirMoser/CalibratedStripeAllSucceed.lean` | ~250 | Replace `balanced_c_share_positive_axiom` with proved theorem |
| `MeirMoser/CalibratedStripeExtraction.lean` | ~400 | Diagonal extraction adapter (mirrors `DiagonalExtractionBalanced.lean`) |
| `MeirMoser/CalibratedStripeTailProof.lean` | ~350 | Adapt `CalibratedTailProofBalanced.lean` to the calibrated stripe |
| `MeirMoser/AllStepsSucceedProof.lean` | edits | Wire the new calibrated path; remove `balanced_c_share_positive_axiom` |
| `MeirMoser/CalibratedTailReduction.lean` | edits | Use `calibrated_tail_theorem_from_calibrated_stripe` |
| `MeirMoser/MainTheorem.lean` | edits | Pass γ_num, γ_den, possibly stronger `t_0` lower bound |
| `MeirMoser/Certificates/WarmStartN100.lean` | edits | Verify `t_0 ≥ T_0(γ, R, c)` |

Total: ~3000 LoC of new code, ~50 LoC of edits to existing files.

---

## Task 1: Define `calibratedBalancedStep` (geometry + structural lemmas)

**Files:**
- Create: `lean/MeirMoser/CalibratedStripe.lean`

- [ ] **Step 1.1: Write file skeleton with imports**

```lean
/-
  CalibratedStripe.lean (Route A.5 Task 1): the genuinely calibrated step.

  Stripe width a_t = 1/(t+1) + t^{-γ} for γ ∈ (1, 3/2). The extra t^{-γ}
  term is what makes Σ a_t · shorter_t convergent, restoring soundness.

  We use a CONCRETE RATIONAL LOWER BOUND for t^{-γ} via
  `calibratedExtraSlackRat γ_num γ_den t : ℚ` so the step itself is in ℚ.
  The Real-valued bound is bridged in CalibratedStripeRpowBound.lean.
-/
import MeirMoser.CalibratedScheduler
import MeirMoser.SchedulerInductionBalanced  -- for cutFromX

namespace MeirMoser

/-- Concrete rational lower bound for `t^{-γ}` with γ = γ_num/γ_den.

    For γ = 4/3 (γ_num=4, γ_den=3): `t^{-4/3} ≥ 1/(t · ⌈t^{1/3}⌉ + 1)`.
    We use a simpler still: `t^{-4/3} ≥ 1/(t² + 1)` (works for all t ≥ 1
    since t² ≥ t^{γ} = t^{4/3} for γ = 4/3 means t^{2−4/3} = t^{2/3} ≥ 1
    iff t ≥ 1, i.e. `t² ≥ t^{4/3}` so `1/t² ≤ 1/t^{4/3}`). -/
def calibratedExtraSlackRat (γ_num γ_den t : ℕ) : ℚ :=
  if t = 0 then 0 else 1 / (((t * t : ℕ) + 1 : ℕ) : ℕ)

/-- Total stripe width a_t (rational). -/
def calibratedStripeWidthRat (γ_num γ_den t : ℕ) : ℚ :=
  1 / ((t + 1 : ℕ) : ℕ) + calibratedExtraSlackRat γ_num γ_den t
```

- [ ] **Step 1.2: Define `calibratedBalancedStep`**

```lean
/-- One calibrated balanced step.

    Always rotates D_t (placed dim 1/(t+1) × 1/t). Cuts a stripe of width
    `a_t = 1/(t+1) + (rational lower bound on t^{-γ})` from the longer
    side of the LRP. Returns S unchanged if rotated D_t doesn't fit. -/
def calibratedBalancedStep (γ_num γ_den : ℕ) (S : TailState) : TailState :=
  let n := S.t
  let a_t : ℚ := calibratedStripeWidthRat γ_num γ_den n
  let h_d : ℚ := 1 / (n : ℕ)            -- rotated D_n height
  if hcanFit : a_t ≤ S.LRP.x1 - S.LRP.x0 ∧ h_d ≤ S.LRP.y1 - S.LRP.y0 then
    if cutFromX S then
      -- x-cut: vertical stripe of width a_t
      { t := n + 1
        container := S.container
        placed := S.placed ++ [
          { n := n, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true }]
        LRP :=
          { x0 := S.LRP.x0 + a_t
            y0 := S.LRP.y0
            x1 := S.LRP.x1
            y1 := S.LRP.y1
            hx := by have := hcanFit.1; linarith
            hy := S.LRP.hy }
        normalBoxes := S.normalBoxes ++ [{
          rect :=
            { x0 := S.LRP.x0
              y0 := S.LRP.y0 + h_d
              x1 := S.LRP.x0 + a_t
              y1 := S.LRP.y1
              hx := by
                have h_pos : (0 : ℚ) ≤ a_t := by
                  unfold_let a_t calibratedStripeWidthRat calibratedExtraSlackRat
                  split_ifs <;> positivity
                linarith
              hy := by have := hcanFit.2; linarith }
          birthIdx := n }]
        endpointBoxes := S.endpointBoxes }
    else
      -- y-cut: horizontal stripe of height h_d
      { t := n + 1
        container := S.container
        placed := S.placed ++ [
          { n := n, x0 := S.LRP.x0, y0 := S.LRP.y0, rotated := true }]
        LRP :=
          { x0 := S.LRP.x0
            y0 := S.LRP.y0 + h_d
            x1 := S.LRP.x1
            y1 := S.LRP.y1
            hx := S.LRP.hx
            hy := by have := hcanFit.2; linarith }
        normalBoxes := S.normalBoxes ++ [{
          rect :=
            { x0 := S.LRP.x0 + 1 / ((n + 1 : ℕ) : ℕ)
              y0 := S.LRP.y0
              x1 := S.LRP.x1
              y1 := S.LRP.y0 + h_d
              hx := by
                have hw_pos : (0 : ℚ) ≤ 1 / ((n + 1 : ℕ) : ℕ) := by positivity
                linarith [hcanFit.1, calibratedStripeWidthRat]
              hy := by
                have h_pos : (0 : ℚ) ≤ h_d := by positivity
                linarith }
          birthIdx := n }]
        endpointBoxes := S.endpointBoxes }
  else
    S

def iteratedCalibrated (γ_num γ_den : ℕ) : ℕ → TailState → TailState
  | 0, S => S
  | (k+1), S => calibratedBalancedStep γ_num γ_den (iteratedCalibrated γ_num γ_den k S)

@[simp] theorem iteratedCalibrated_zero (γ_num γ_den : ℕ) (S : TailState) :
    iteratedCalibrated γ_num γ_den 0 S = S := rfl
@[simp] theorem iteratedCalibrated_succ (γ_num γ_den : ℕ) (k : ℕ) (S : TailState) :
    iteratedCalibrated γ_num γ_den (k+1) S =
      calibratedBalancedStep γ_num γ_den (iteratedCalibrated γ_num γ_den k S) := rfl

end MeirMoser
```

- [ ] **Step 1.3: Build, verify compiles**

Run: `cd /workspace/Packing/lean && lake build 2>&1 | tail -10`
Expected: `Build completed successfully` (warnings OK).

- [ ] **Step 1.4: Add structural pass-through lemmas**

```lean
/-- Container preserved. -/
theorem calibratedBalancedStep_container (γ_num γ_den : ℕ) (S : TailState) :
    (calibratedBalancedStep γ_num γ_den S).container = S.container := by
  unfold calibratedBalancedStep
  by_cases h : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
               (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0
  · rw [dif_pos h]; by_cases hcut : cutFromX S
    · rw [if_pos hcut]
    · rw [if_neg hcut]
  · rw [dif_neg h]

/-- t advances by 1 when fit succeeds. -/
theorem calibratedBalancedStep_t_advances {γ_num γ_den : ℕ} {S : TailState}
    (h_fit : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
             (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0) :
    (calibratedBalancedStep γ_num γ_den S).t = S.t + 1 := by
  unfold calibratedBalancedStep
  rw [dif_pos h_fit]
  by_cases hcut : cutFromX S
  · rw [if_pos hcut]
  · rw [if_neg hcut]
```

- [ ] **Step 1.5: Build, commit**

```bash
cd /workspace/Packing/lean && lake build 2>&1 | tail -5
```

```bash
cd /workspace/Packing && git add lean/MeirMoser/CalibratedStripe.lean
git commit -m "feat: define calibratedBalancedStep with rational stripe a_t = 1/(t+1) + 1/(t²+1)

Route A.5 Task 1: define the calibrated balanced step using a concrete
rational lower bound for t^{-γ}: 1/(t² + 1) (valid for γ ≤ 2). Container
preserved; t-advance proved.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 2: Per-step area-share bound

**Files:**
- Create: `lean/MeirMoser/CalibratedStripeArea.lean`

- [ ] **Step 2.1: State the area-share lemma**

```lean
/-
  CalibratedStripeArea.lean: per-step area-share bound for the calibrated step.

  Per-step LRP area loss = a_t · shorter_side.
  We get: new_area · new_t ≥ old_area · t − a_t · maxSide · (1 + 1/t).
-/
import MeirMoser.CalibratedStripe
import MeirMoser.SchedulerInductionBalanced  -- for cutFromX
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace MeirMoser

theorem calibratedBalancedStep_LRP_area_lower
    (γ_num γ_den : ℕ) (S : TailState)
    (h_fit : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
             (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0)
    (h_t_pos : 0 < S.t)
    : (calibratedBalancedStep γ_num γ_den S).LRP.area *
        ((calibratedBalancedStep γ_num γ_den S).t : ℚ) ≥
      S.LRP.area * (S.t : ℚ) -
        calibratedStripeWidthRat γ_num γ_den S.t * S.LRP.maxSide *
          (1 + 1 / (S.t : ℕ)) := by
  sorry  -- mirror balancedStep_LRP_area_lower with a_t in place of 1/(t+1) or 1/t

end MeirMoser
```

- [ ] **Step 2.2: Fill the proof**

The proof structure mirrors `balancedStep_LRP_area_lower` (in `SchedulerInductionBalancedLRPArea.lean`). Two cases on `cutFromX S`:
- x-cut: new area = `(W - a_t) · H`. Per-step loss = `a_t · H`. Adjust algebra.
- y-cut: new area = `W · (H - 1/t)`. Per-step loss = `W/t`. (Note: y-cut still uses `1/t` for height since the rotated D_t height is `1/t`, but the stripe in y-cut direction is just `1/t`, NOT `a_t`. WAIT — if we want the calibrated slack on BOTH cuts, both cuts should use width `a_t`. Let me reconsider.)

Actually, re-examining: the calibrated stripe has width `a_t` ALONG ONE direction. In x-cut, we cut a vertical stripe of WIDTH `a_t`. In y-cut, we cut a horizontal stripe of HEIGHT — what?

For symmetry, the y-cut should also cut a stripe of length `a_t` (in the y-direction). So y-cut: stripe of height `a_t`, with rotated D_t (1/(t+1) × 1/t) at corner; this requires `a_t ≥ 1/t` (the rotated D_t's height). Since `a_t = 1/(t+1) + t^{-γ}` and γ < 3/2, `t^{-γ} > 1/t² > 0`, but is `a_t ≥ 1/t`? We need `1/(t+1) + 1/(t²+1) ≥ 1/t`. For t = 1: 1/2 + 1/2 = 1 ≥ 1 ✓. For t = 100: 0.0099 + 0.0001 = 0.01 ≥ 0.01 ✓. For t large: `1/(t+1) ≈ 1/t - 1/t²` so the bound is tight. Use `1/(t² + 1)` as the rational lower bound is borderline. Use `1/t²` instead: `1/(t+1) + 1/t² ≥ 1/t` iff `t² + (t+1) ≥ t(t+1) = t² + t` iff `t+1 ≥ t` ✓. So `a_t ≥ 1/t` ALWAYS using the simpler `1/t²` bound.

REVISE Task 1 step 1.1: use `calibratedExtraSlackRat γ_num γ_den t = 1/(t * t)` for `t ≥ 1` (defined as `0` for `t = 0`).

```lean
def calibratedExtraSlackRat (γ_num γ_den t : ℕ) : ℚ :=
  if t = 0 then 0 else 1 / ((t : ℕ) * (t : ℕ) : ℕ)
```

So `a_t ≥ 1/t`, and the y-cut stripe of height `a_t` works (since `a_t ≥ 1/t ≥ 1/t = D_t.height_rotated`).

Now revise the step:

```lean
-- y-cut branch:
LRP := { x0 := S.LRP.x0, y0 := S.LRP.y0 + a_t, x1 := S.LRP.x1, y1 := S.LRP.y1, ... }
```

And the proof of `calibratedBalancedStep_LRP_area_lower` uses `a_t` in BOTH branches. Per-step loss = `a_t · shorter_side`.

- [ ] **Step 2.3: Test the proof, build, commit**

```bash
cd /workspace/Packing/lean && lake build 2>&1 | tail -5
```

```bash
cd /workspace/Packing && git add lean/MeirMoser/CalibratedStripe*.lean
git commit -m "feat: calibratedBalancedStep area-share bound (R-A.5 Task 2)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 3: Aspect preservation

**Files:**
- Create: `lean/MeirMoser/CalibratedStripeAspect.lean`

- [ ] **Step 3.1: State and prove**

The aspect proof uses the key insight: cut from longer side, longer shrinks by `a_t`, shorter unchanged. New aspect = max(longer-a_t, shorter)/min(longer-a_t, shorter). Need ≤ R.

Mirror `balancedStep_LRP_aspect_preserved` with `a_t` in place of `1/(t+1)` or `1/t`. The room hypothesis becomes:

```lean
(h_room : S.LRP.maxSide - calibratedStripeWidthRat γ_num γ_den S.t ≥ S.LRP.minSide / R)
```

This is a TIGHTER room hypothesis than the simplified version (since `a_t > 1/t`). Conditions when this can be discharged inside the inductive proof: needs analysis. Initial guess: `R ≥ φ²` plus some additional condition involving `a_t`. Defer the discharge to Task 9.

```lean
theorem calibratedBalancedStep_LRP_aspect_preserved
    (γ_num γ_den : ℕ) (S : TailState) (R : ℚ) (h_R : 1 ≤ R)
    (h_aspect : S.LRP.maxSide ≤ R * S.LRP.minSide)
    (h_fit : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
             (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0)
    (h_t_pos : 0 < S.t)
    (h_room : S.LRP.maxSide - calibratedStripeWidthRat γ_num γ_den S.t ≥
              S.LRP.minSide / R)
    : (calibratedBalancedStep γ_num γ_den S).LRP.maxSide ≤
        R * (calibratedBalancedStep γ_num γ_den S).LRP.minSide := by
  sorry  -- mirror balancedStep_LRP_aspect_preserved
```

- [ ] **Step 3.2: Build, commit**

---

## Task 4: Endpoint + width-check + new normal box

**Files:**
- Create: `lean/MeirMoser/CalibratedStripeAux.lean`

- [ ] **Step 4.1**: State and prove
```lean
theorem calibratedBalancedStep_preserves_endpoint_perim
    (γ_num γ_den : ℕ) (S : TailState) :
    ((calibratedBalancedStep γ_num γ_den S).endpointBoxes.map Rect.semiperim).sum =
    (S.endpointBoxes.map Rect.semiperim).sum
```

- [ ] **Step 4.2**: Define `newWidthCheckCalibrated` and prove `calibratedBalancedStep_widthChecks_extend`. Mirror `balancedStep_widthChecks_extend`.

- [ ] **Step 4.3**: Build, commit.

---

## Task 5: Containment + FP propagation

**Files:**
- Create: `lean/MeirMoser/CalibratedStripeContainment.lean`

- [ ] **Step 5.1**: Mirror `SchedulerInductionBalancedContainment.lean` for the calibrated step. Lemmas needed:
  - `calibratedBalancedStep_t_pos`
  - `calibratedBalancedStep_LRP_in_container`
  - `calibratedBalancedStep_LRP_in_old_LRP` (the new LRP is contained in the old LRP)
  - `calibratedBalancedStep_LRP_disj_from_placed`
  - `calibratedBalancedStep_FP`
  - `iteratedCalibrated_t_pos`
  - `iteratedCalibrated_FP`
  - `iteratedCalibrated_LRP_in_container`
  - `iteratedCalibrated_LRP_disj_from_placed`

- [ ] **Step 5.2**: Build, commit.

---

## Task 6: Combine into preservation theorem

**Files:**
- Create: `lean/MeirMoser/CalibratedStripeCombine.lean`

- [ ] **Step 6.1**: 

```lean
theorem step_preserves_GoodTailState_calibrated
    (γ_num γ_den : ℕ) (S : TailState) (widthChecks : List NormalWidthCheck)
    (c R η : ℚ) (h_R : 1 ≤ R)
    (h_state : GoodTailState c R η S widthChecks)
    (h_fit : calibratedStripeWidthRat γ_num γ_den S.t ≤ S.LRP.x1 - S.LRP.x0 ∧
             (1 : ℚ) / (S.t : ℕ) ≤ S.LRP.y1 - S.LRP.y0)
    (h_t_pos : 0 < S.t)
    (h_room : S.LRP.maxSide - calibratedStripeWidthRat γ_num γ_den S.t ≥
              S.LRP.minSide / R)
    (h_FP : FinitePacking
              (calibratedBalancedStep γ_num γ_den S).container
              (calibratedBalancedStep γ_num γ_den S).placed)
    : ∃ c', GoodTailState c' R η (calibratedBalancedStep γ_num γ_den S)
              (widthChecks ++ [newWidthCheckCalibrated γ_num γ_den S]) := by
  sorry  -- mirror step_preserves_GoodTailState_balanced
```

- [ ] **Step 6.2**: Build, commit.

---

## Task 7: Bridge ℝ↔ℚ for `t^{-γ}`

**Files:**
- Create: `lean/MeirMoser/CalibratedStripeRpowBound.lean`

- [ ] **Step 7.1**: Prove the rational lower bound is below the actual `Real.rpow`:

```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace MeirMoser

/-- The rational lower bound `1/t²` is below `t^{-γ}` for γ ≤ 2 and t ≥ 1. -/
theorem calibratedExtraSlackRat_le_rpow
    (γ_num γ_den : ℕ) (h_γ_lt_two : γ_num < 2 * γ_den)
    (t : ℕ) (h_t : 0 < t) :
    (calibratedExtraSlackRat γ_num γ_den t : ℝ) ≤
      (t : ℝ) ^ (-(γ_num / γ_den : ℝ)) := by
  sorry  -- 1/t² ≤ t^{-γ} for γ ≤ 2 and t ≥ 1
```

- [ ] **Step 7.2**: Total stripe width bound:

```lean
theorem calibratedStripeWidthRat_le_rpow_sum
    (γ_num γ_den : ℕ) (h_γ_lt_two : γ_num < 2 * γ_den)
    (t : ℕ) (h_t : 0 < t) :
    (calibratedStripeWidthRat γ_num γ_den t : ℝ) ≤
      1 / ((t : ℝ) + 1) + (t : ℝ) ^ (-(γ_num / γ_den : ℝ)) := by
  sorry
```

- [ ] **Step 7.3**: Build, commit.

---

## Task 8: Cumulative tail-sum bound (THE KEY)

**Files:**
- Create: `lean/MeirMoser/CalibratedStripeCumulative.lean`

- [ ] **Step 8.1**: State the cumulative bound

```lean
import MeirMoser.CalibratedStripeRpowBound
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace MeirMoser

/-- Cumulative LRP-area decay across all balanced calibrated steps is bounded.

    Specifically: `Σ_{j=0}^∞ a_{t_0 + j} · LRP.height_j ≤ K(γ, R, c) / √t_0`
    for some explicit constant K. The proof uses:
      1. `LRP.height_j ≤ √(R · area_j)` (aspect ≤ R).
      2. `area_j ≤ 2c/(t_0 + j)` (from GoodTailState propagation, c stays
         within [c/2, 3c/2]).
      3. Hence `LRP.height_j ≤ √(R · 2c/(t_0 + j)) = √(2Rc) · (t_0+j)^{-1/2}`.
      4. Per-step decay ≤ `a_t · √(2Rc) · t^{-1/2}` =
         `√(2Rc) · (1/((t+1)·√t) + t^{-γ - 1/2})`.
      5. Cumulative ≤ `√(2Rc) · (Σ t^{-3/2} + Σ t^{-γ - 1/2})`. Both converge
         (γ > 1/2). Total ≤ `√(2Rc) · K(γ) · 1/√t_0`. -/
theorem calibrated_cumulative_decay_bound
    (γ_num γ_den : ℕ) (h_γ_in : 1 * γ_den < γ_num ∧ γ_num * 2 < γ_den * 3)
    (c R : ℚ) (h_c_pos : 0 < c) (h_R_ge_one : 1 ≤ R)
    (t_0 : ℕ) (h_t_0_large : True)  -- TODO: explicit lower bound on t_0
    : ∃ K : ℝ, ∀ k, (
        ∑ j in Finset.range k,
          (calibratedStripeWidthRat γ_num γ_den (t_0 + j) : ℝ) *
          (1 : ℝ)  -- placeholder for LRP.height — needs precise statement
      ) ≤ K := by
  sorry  -- the deep tail-sum bound
```

The exact statement requires careful threading; may take iteration. The proof uses:
- `Real.summable_one_div_nat_rpow` for `Σ t^{-p}` (p > 1).
- Telescoping for `Σ 1/((t+1)·√t)`.

**This is the hardest task** — estimated 3–5 days of focused Lean work.

- [ ] **Step 8.2**: Iterate on the statement until provable.

- [ ] **Step 8.3**: Prove. Build. Commit.

---

## Task 9: Discharge `c_share_positive_axiom`

**Files:**
- Modify: `lean/MeirMoser/AllStepsSucceedProof.lean` (or create `CalibratedStripeAllSucceed.lean`)

- [ ] **Step 9.1**: Replace `axiom balanced_c_share_positive_axiom` with a proved theorem using `calibrated_cumulative_decay_bound` + `step_preserves_GoodTailState_calibrated`.

- [ ] **Step 9.2**: Update `c_decay_balanced` (or define new `c_decay_calibrated`) to use the calibrated step.

- [ ] **Step 9.3**: Build, commit.

---

## Task 10: Adapt extraction + tail proof

**Files:**
- Create: `lean/MeirMoser/CalibratedStripeExtraction.lean`
- Create: `lean/MeirMoser/CalibratedStripeTailProof.lean`

- [ ] **Step 10.1**: Mirror `DiagonalExtractionBalanced.lean` for the calibrated step.

- [ ] **Step 10.2**: Mirror `CalibratedTailProofBalanced.lean` for the calibrated step.

- [ ] **Step 10.3**: Build, commit.

---

## Task 11: Wire main theorem

**Files:**
- Modify: `lean/MeirMoser/CalibratedTailReduction.lean`
- Modify: `lean/MeirMoser/MainTheorem.lean`
- Modify: `lean/MeirMoser/Certificates/WarmStartN100.lean`

- [ ] **Step 11.1**: Add `theorem calibrated_tail_theorem_from_calibrated` using the calibrated path.

- [ ] **Step 11.2**: Update `meir_moser_packing_from_certificate` to use the calibrated path. Add hypothesis `h_t_0_large : t_0 ≥ T_0(γ, R, c)`.

- [ ] **Step 11.3**: Add `state_t_0_large` theorem to WarmStartN100.lean. Verify via `native_decide`.

- [ ] **Step 11.4**: Verify `#print axioms` shows ONLY Lean core (4 axioms): `propext`, `Classical.choice`, `Lean.ofReduceBool`, `Quot.sound`. No project-specific axioms.

- [ ] **Step 11.5**: Build, final commit.

---

## Self-Review

- **Spec coverage**: tasks 1-11 cover the geometry, four preservations, propagation, the cumulative bound (key), and the wiring. ✓
- **Placeholders**: Task 8 has `True` as a placeholder for `h_t_0_large`; this needs concretization (e.g. `t_0 ≥ R³/c²` or whatever the constant tracking gives). FIX: add to Task 8 step "iterate on statement" — first attempt a vague bound, then refine.
- **Type consistency**: `calibratedBalancedStep`, `iteratedCalibrated`, `calibratedStripeWidthRat`, `calibratedExtraSlackRat`, `step_preserves_GoodTailState_calibrated` are used consistently across tasks.

## Risk

- **Task 8** is genuinely hard. Estimated 3–5 days for the cumulative bound. If it gets stuck, the fallback is to prove the bound for sufficiently large `t_0` (e.g., `t_0 ≥ 10^6`) which simplifies constants.
- **Real ↔ Rational**: bridging may require ad-hoc lemmas; budget extra time for Task 7.
- **Total estimate**: 10–14 days of focused Lean engineering. Multi-session work; not closeable in a single session.

## Plan complete

Plan saved to `docs/superpowers/plans/2026-05-10-route-a5-calibrated-stripe.md`. Two execution options:

1. **Subagent-Driven (recommended)** — dispatch a fresh subagent per task, review between tasks, fast iteration. Tasks 1–7 are independent (after Task 1 lands) and can run in parallel.

2. **Inline Execution** — execute tasks in this session using executing-plans.

Which approach?
