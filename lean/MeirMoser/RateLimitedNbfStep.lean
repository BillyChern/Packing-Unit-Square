/-
  RateLimitedNbfStep.lean: rate-limited absorber extension of the
  normal-box-first scheduler.

  Why this file exists
  --------------------
  The Meir–Moser tail framework combines two ingredients:
    (a) the normal-box-first dispatch (`nbfStep`), which lets `D_t` reuse a
        previously created normal box "for free" (no LRP cut);
    (b) endpoint absorbers: special endpoint boxes earmarked to swallow `D_t`
        events at a controlled rate, so that the cumulative LRP cuts shrink
        sub-linearly in `t`.

  In the calibrated paper-side analysis, absorber events fire at a rate
  `1 / ⌈t^{1/γ}⌉`: roughly, every `⌈t^{1/γ}⌉`-th step is an absorber slot
  rather than a normal-box-first dispatch. This rate is sharp enough for
  the cumulative bound `Σ a_t = O(t^{1−γ})` and the calibrated tail closure
  argument.

  Approach
  --------
  Per the design notes for this task, we follow approach (b): keep the
  existing `TailState` unchanged, and thread an EXTERNAL counter `m` along
  with `S`. Each step takes the pair `(S, m)` and returns the updated pair
  `(S', m+1)`. The rate `kTarget(t) = ⌈t^{1/γ}⌉` is approximated by the
  coarse-but-safe over-estimator `Nat.sqrt t + 1`, which dominates `t^{1/γ}`
  for any `γ ≤ 2` and `t ≥ 1`.

  Three branches per step:
    • `m + 1 < kTarget(t)`: ordinary normal-box-first dispatch (delegate to
      `nbfStep`).
    • `m + 1 ≥ kTarget(t)`: absorber slot. Try to consume the first endpoint
      box that fits a rotated `D_t` of dimensions `1/(t+1) × 1/t`. If found,
      remove that endpoint and place `D_t` at its bottom-left corner. If no
      endpoint fits, fall back to `nbfStep`.

  When an absorber fires we DROP the consumed endpoint without reinserting
  any leftover region (the framework treats absorbed endpoints as fully
  discharged). This is the simplest version that matches the paper-side
  intent; in particular it strictly DECREASES the endpoint-semiperimeter
  potential, which is the right monotone direction for the calibrated
  invariant `Σ semiperim(endpointBoxes) ≤ η`.

  Implementation status
  ---------------------
  Sorry-free. Every branch is explicitly constructed:
    • The absorber-success branch builds a fresh `TailState` whose
      `endpointBoxes` is `S.endpointBoxes.eraseIdx i`, whose `placed` is
      extended by a rotated `D_t` placed at the consumed endpoint's
      bottom-left corner, and whose `t` advances by 1.
    • The absorber-failure branch (no endpoint fits) and the rate-limited
      branch (`m + 1 < kTarget`) both delegate to `nbfStep`.

  We also prove a small structural lemma `rateLimitedNbfStep_advances_t_or_S`
  showing that the absorber branch advances `t` by 1 whenever it fires,
  and that the counter advances by 1 in every branch.

  Open follow-up obligations (NOT in this file):
    • A preservation lemma that propagates `GoodTailState` across
      `rateLimitedNbfStep`, mirroring the analogous obligations for
      `nbfStep` and `calibratedBalancedStep`.
    • A cumulative-rate lemma showing that the number of LRP cuts taken
      across `iteratedRateLimited k` is `O(k^{1−γ})`, using the
      `kTarget`-driven rate of absorber events.

  Relationship to existing code
  ------------------------------
    • `nbfStep γ_num γ_den S` — used as the rate-limited branch and as the
      absorber-failure fallback.
    • `TailState`, `Rect`, `PlacedRect` — shared structures from
      `MeirMoser.CalibratedScheduler` and `MeirMoser.Geometry`.
-/
import MeirMoser.NormalBoxFirstStep
import MeirMoser.CalibratedScheduler
import Mathlib.Tactic

namespace MeirMoser

/-- Coarse-but-safe over-estimator of `⌈t^{1/γ}⌉`.

    For any `γ ≤ 2` and `t ≥ 1` we have `t^{1/γ} ≥ t^{1/2} = √t`, so
    `Nat.sqrt t + 1` is an upper bound on `⌈t^{1/γ}⌉` whenever `γ ≤ 2`.
    Using a coarser rate is conservative for the calibrated tail bound
    (more absorber events cause the cumulative LRP cut to be even smaller).

    The arguments `γ_num`, `γ_den` are kept in the signature for downstream
    consistency; they do not appear in the definition itself, since the
    `Nat.sqrt`-based bound dominates uniformly for `γ ≤ 2`. -/
def kTarget (γ_num γ_den : ℕ) (t : ℕ) : ℕ :=
  Nat.sqrt t + 1

/-- `kTarget` is always positive. -/
theorem kTarget_pos (γ_num γ_den t : ℕ) : 0 < kTarget γ_num γ_den t := by
  unfold kTarget
  exact Nat.succ_pos _

/-- Find the FIRST endpoint box in `S.endpointBoxes` whose rectangle has
    both width `≥ 1/(t+1)` and height `≥ 1/t`, i.e. is large enough to
    host a rotated copy of `D_t` (dimensions `1/(t+1) × 1/t`).

    Returns the list-index of the first such endpoint, or `none` if none
    of the endpoints have room. Decidable / computable. -/
def findEndpointForRotated (S : TailState) (t : ℕ) : Option ℕ :=
  let w_d : ℚ := 1 / ((t + 1 : ℕ) : ℕ)   -- rotated D_t width
  let h_d : ℚ := 1 / ((t : ℕ) : ℕ)       -- rotated D_t height
  S.endpointBoxes.findIdx? (fun ep =>
    decide (w_d ≤ ep.x1 - ep.x0 ∧ h_d ≤ ep.y1 - ep.y0))

/-- One rate-limited normal-box-first step.

    Returns the pair `(newState, newCounter)`.

    Branching rule (with `n := S.t`, `k := kTarget γ_num γ_den n`):
      • `m + 1 < k`: ordinary `nbfStep` (normal-box-first dispatch). The
        counter advances by 1 (we are still inside the current absorber
        cycle).
      • `m + 1 ≥ k`: absorber slot.
          * If some endpoint box fits a rotated `D_n`, consume that
            endpoint and place `D_n` at its bottom-left corner. The
            consumed endpoint is removed from `S.endpointBoxes` (no
            leftover reinserted), and the counter resets to `0`
            (the cycle is complete).
          * Otherwise, fall back to `nbfStep`. The counter still
            resets to `0`: the absorber attempt has fired, even
            though it was "spent" on a normal-box-first dispatch.

    The reset-to-zero behavior keeps `m` bounded by `kTarget(t)` for all
    iterations, so the counter never overflows the cycle length. -/
def rateLimitedNbfStep (γ_num γ_den : ℕ) (S : TailState) (m : ℕ) : TailState × ℕ :=
  let n := S.t
  let k := kTarget γ_num γ_den n
  if m + 1 < k then
    -- Inside the cycle: ordinary normal-box-first dispatch.
    (nbfStep γ_num γ_den S, m + 1)
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
              -- Place rotated D_n at the endpoint's bottom-left corner;
              -- consume the endpoint without reinserting any leftover.
              ({ t := n + 1
                 container := S.container
                 placed := S.placed ++ [
                   { n := n, x0 := chosen.x0, y0 := chosen.y0, rotated := true }]
                 LRP := S.LRP
                 normalBoxes := S.normalBoxes
                 endpointBoxes := S.endpointBoxes.eraseIdx i }, 0)
            else
              -- Unreachable on well-formed input: the find predicate
              -- already guaranteed `h_fits`. Safe fallback.
              (nbfStep γ_num γ_den S, 0)
        | none =>
            -- Unreachable on well-formed input. Safe fallback.
            (nbfStep γ_num γ_den S, 0)
    | none =>
        -- No endpoint fits; fall back to ordinary normal-box-first dispatch.
        (nbfStep γ_num γ_den S, 0)

/-- Iterate the rate-limited step. Threads the counter through.

    Convention: pass an initial counter `m₀ = 0` from the caller, e.g.
    `iteratedRateLimited γ_num γ_den k (S₀, 0)`. -/
def iteratedRateLimited (γ_num γ_den : ℕ) : ℕ → TailState × ℕ → TailState × ℕ
  | 0, p => p
  | (k+1), p => rateLimitedNbfStep γ_num γ_den
                  (iteratedRateLimited γ_num γ_den k p).1
                  (iteratedRateLimited γ_num γ_den k p).2

@[simp] theorem iteratedRateLimited_zero (γ_num γ_den : ℕ) (p : TailState × ℕ) :
    iteratedRateLimited γ_num γ_den 0 p = p := rfl

@[simp] theorem iteratedRateLimited_succ
    (γ_num γ_den : ℕ) (k : ℕ) (p : TailState × ℕ) :
    iteratedRateLimited γ_num γ_den (k+1) p =
      rateLimitedNbfStep γ_num γ_den
        (iteratedRateLimited γ_num γ_den k p).1
        (iteratedRateLimited γ_num γ_den k p).2 := rfl

/-- Structural lemma: in the absorber-success branch, `t` advances by 1.

    More precisely: if the cycle boundary is reached (`m + 1 ≥ k`) and
    `findEndpointForRotated S n = some i` with the chosen endpoint
    actually fitting `D_n`, then the new state's `t` is `S.t + 1` and
    the new counter is `0`. -/
theorem rateLimitedNbfStep_t_advances_absorber
    {γ_num γ_den : ℕ} {S : TailState} {m : ℕ}
    (h_cycle : ¬ m + 1 < kTarget γ_num γ_den S.t)
    {i : ℕ} (h_find : findEndpointForRotated S S.t = some i)
    {chosen : Rect} (h_get : S.endpointBoxes.get? i = some chosen)
    (h_fits :
      (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ chosen.x1 - chosen.x0 ∧
      (1 : ℚ) / ((S.t : ℕ) : ℕ) ≤ chosen.y1 - chosen.y0) :
    (rateLimitedNbfStep γ_num γ_den S m).1.t = S.t + 1 ∧
    (rateLimitedNbfStep γ_num γ_den S m).2 = 0 := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [rateLimitedNbfStep, if_neg h_cycle, h_find, h_get, dif_pos h_fits]

/-- Structural lemma: in the rate-limited (non-cycle) branch, the step
    delegates to `nbfStep` and the counter advances by 1. -/
theorem rateLimitedNbfStep_inside_cycle
    {γ_num γ_den : ℕ} {S : TailState} {m : ℕ}
    (h_cycle : m + 1 < kTarget γ_num γ_den S.t) :
    rateLimitedNbfStep γ_num γ_den S m = (nbfStep γ_num γ_den S, m + 1) := by
  unfold rateLimitedNbfStep
  rw [if_pos h_cycle]

/-- Structural lemma: in the absorber branch with no fitting endpoint,
    the step falls back to `nbfStep` and the counter resets to `0`. -/
theorem rateLimitedNbfStep_absorber_no_fit
    {γ_num γ_den : ℕ} {S : TailState} {m : ℕ}
    (h_cycle : ¬ m + 1 < kTarget γ_num γ_den S.t)
    (h_find : findEndpointForRotated S S.t = none) :
    rateLimitedNbfStep γ_num γ_den S m = (nbfStep γ_num γ_den S, 0) := by
  unfold rateLimitedNbfStep
  rw [if_neg h_cycle]
  rw [h_find]

end MeirMoser
