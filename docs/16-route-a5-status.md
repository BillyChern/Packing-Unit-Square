# Route A.5 status — partial progress + deeper gap revealed

Date: 2026-05-10

## What was achieved

Route A.5 ("calibrated stripe with t^{-γ} extra slack") was executed in parallel
through A5.1–A5.7 + A5.6. All structural components built sorry-free:

- `CalibratedStripe.lean` (A5.1, 211 LoC): defines `calibratedBalancedStep`
  with stripe `a_t = 1/(t+1) + 1/t²` (rational lower bound on `1/(t+1) + t^{-γ}`).
- `CalibratedStripeArea.lean` (A5.2, 165 LoC): per-step area-share lower bound.
- `CalibratedStripeAspect.lean` (A5.3, 175 LoC): aspect ≤ R preserved.
- `CalibratedStripeAux.lean` (A5.4, 151 LoC): endpoint + width-check preservation.
- `CalibratedStripeContainment.lean` (A5.5, 451 LoC): t > 0, FP, container,
  LRP-disjointness propagation.
- `CalibratedStripeCombine.lean` (A5.6, 63 LoC): combines all four into
  `step_preserves_GoodTailState_calibrated`.
- `CalibratedStripeRpowBound.lean` (A5.7, 95 LoC): bridge `1/t² ≤ t^{-γ}` for
  γ ≤ 2 in ℝ.
- `CalibratedStripeExtraction.lean` and `CalibratedStripeTailProof.lean`
  (A5.10): adaptation of diagonal extraction (in progress).

Total new code: ~1300 LoC, sorry-free, building cleanly under `lake build`.

## The deeper gap (revealed by simulation)

Simulation (`temp/sim_calibrated.py`) on both the synthetic strong cert
(c=40, R=2, t=100, area=0.4) and the N=100-like cert showed that even with
the calibrated stripe, the per-step c-share decay
`a_t · maxSide · (t+1)` diverges:

- Synthetic strong: c-share flips negative at k=50, t=150.
- N=100-like: c-share flips negative at k=1, t=102.

### Why

The proven per-step bound is `a_t · maxSide · (t+1)`. Algebraically:
`a_t · (t+1) ≈ 1 + 1/t` for large t (the `t+1` factor cancels the `1/(t+1)` in
`a_t`). Per-step decay ≈ `(1+1/t) · maxSide ≈ maxSide`.

With `maxSide ≤ √(R · area)`, cumulative ≈ Σ √(R · area_j) which doesn't
converge to anything small unless area shrinks fast.

### Tighter bound `a_t · maxSide · (1 + 1/t)` would close

If the per-step bound were `a_t · maxSide · (1 + 1/t)` (instead of `(t+1)`):
- a_t · (1 + 1/t) ≈ (1/(t+1)) · 1 + t^{-γ-1} ≈ 1/t + 1/t^{γ+1}.
- Cumulative `Σ a_t · maxSide · (1 + 1/t)` for `area_t ≥ c/t`, `maxSide ≤ √(Rc/t)`:
  ≈ √(Rc) · Σ (1/t + t^{-γ-1}) / √t = √(Rc) · (Σ t^{-3/2} + Σ t^{-γ-3/2})
  Both convergent for γ > -1/2. For γ = 4/3: bounded. ✓

But the tighter bound is not unconditionally provable — it requires using
`old_area · t ≥ c` (the GoodTailState invariant) as a hypothesis. Even with
that, the algebra doesn't cleanly close: we'd need `c ≥ a · W · (t²−1)`
which is generically false for our certs (e.g., for N=100: c=0.077,
a·W·(t²−1) ≈ 6.5).

### What's actually needed

The full Meir-Moser framework uses MORE than just the LRP area-share invariant:
- **Normal-box width law** (`Σ width_k ≤ K/t^{γ−1}` via calibrated_normal_sum):
  bounds the total length of normal-box widths, providing the missing decay.
- **Endpoint potential** `P_ep ≤ η`: bounds endpoint perimeter accumulation.
- **Cellification of finished strips**: recovers area lost to thin strips.
- **Two-backtrack**: prevents endpoint slivers.

These four together provide the bookkeeping that makes the cumulative bound
work. Our simplified setting (LRP + one normal box per step, no endpoints, no
cellification) doesn't have enough machinery.

## Status of axioms

The closure path now depends on a single project-specific axiom
`MeirMoser.AllStepsSucceedProof.balanced_c_share_positive_axiom`. Proving
this axiom rigorously requires implementing the FULL calibrated framework
(cellification, endpoints, normal-box width law all integrated into the
scheduler). This is a research-level project, not an engineering one — the
framework's quantitative claims need careful verification before they can be
formalized.

## Decision

The Lean artifact is structurally complete: 33 files, ~4000 LoC, single
focused analytic axiom. The artifact serves as a **framework demonstration**
and **proof skeleton**, not a complete formal proof. Closing the residual
axiom requires either:

(a) Implementing the full calibrated framework (cellification, endpoints, etc.) —
    a multi-week to multi-month research project.

(b) Restating the axiom at a higher level of abstraction (revert to the
    wholesale `calibrated_tail_theorem` form, sound but undecomposed). This
    is a 5-minute change and produces a sound (axiom-supported) proof.

(c) Pursuing a fundamentally different proof technique (e.g., extending
    Zhu-Joós's computational approach, or BSSF ρ→∞ invariant).

The Meir-Moser problem (Concrete Mathematics 2.37) remains open in
mathematics. The user's calibrated framework is one promising approach, but
the simplified versions we've Lean-formalized are too weak to discharge the
deep claim. The empirical contribution (σ ≤ 20002/20001) stands as a
significant computational result independent of the Lean closure.

## Next steps

- Wait for A5.10 (extraction adapter) to complete; this is mechanical.
- Mark A5.8 (deep cumulative bound) as **blocked by research-level math gap**.
- Mark A5.9 and A5.11 as blocked.
- The artifact's value is in the framework's structural verification, not
  in producing a closed formal proof of an open math problem.
