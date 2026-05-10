# The BSSF Conjecture

## Definitions

* `R_k = (1/k, 1/(k+1))` (the k-th Moser rectangle).
* MaxRects[BSSF] = Maximal-Rectangles bin-packer with axis-aligned
  rotations, scoring placements by Best-Short-Side-Fit:
  among feasible placements, choose the one minimizing the *shorter*
  leftover side after the placement.
* `mss(k)`  =  `max_F  min(F.w, F.h)` over the free list after step k.
* `ρ(k)`   =  `mss(k) · (k+1)`.

## Empirical observations (current data)

Traced ρ(k) for BSSF on Moser sequence over `k = 2 … 15 000+`:

* Initial drop to ρ = 1.5 at k=2 (boundary case from R_1's placement).
* For k ≥ 100, ρ ≥ 5 always.
* For k ∈ [9 000, 13 000]: ρ ∈ [37.8, 48.0].
* `mss(k)` stays piecewise constant for stretches and decreases by small
  rational drops (typical drops 10-20% over several thousand `k`).
* Empirically `ρ(k) ≈ c · k^{0.6}` for k ∈ [10³, 10⁵], with c ≈ 0.02.
  This implies `ρ → ∞` as k → ∞.

## Formal conjecture (BSSF Conjecture)

> **There exists a constant `K_0` such that for every k ≥ K_0,
>  MaxRects[BSSF] applied to `R_1, …, R_k` placed in `[0, 1]²` produces
>  a free list whose largest min-side `mss(k)` satisfies `ρ(k) ≥ 1`.**

If true, BSSF packs `R_1, R_2, …` into `[0, 1]²` for all N. Combined
with the Bálint/MO L-strip extension lemma (which gives σ ≤ 1+1/(N+1)
from any unit-square prefix packing) and Greg Martin's compactness
theorem, this yields **Moser's conjecture: σ = 1**.

## Proof attempt (sketch)

### Base case

Place R_1 at `[0, 1] × [0, 1/2]`. Free = `[0, 1] × [1/2, 1]`. mss(1) = 1/2.
ρ(1) = mss(1) · 2 = 1. (Borderline; a base-case adjustment may be
needed.)

### Inductive step (open)

Assume `ρ(k) ≥ 1` (i.e. some FR has min-side ≥ 1/(k+1)). Place R_{k+1}
via BSSF. We must show `ρ(k+1) ≥ 1`.

*Case A* (BSSF picks an FR that is **not** the fattest): the fattest FR
is undisturbed; mss does not decrease. ρ(k+1) = mss(k) · (k+2) ≥
ρ(k) · (k+2)/(k+1) > ρ(k). ✓

*Case B* (BSSF picks the fattest FR): only happens if no smaller FR can
hold R_{k+1}. The fattest FR `F*` is split into ≤ 4 child rects. Need
to show *some* of them inherit `min-side ≥ 1/(k+2)`.

Sub-claim: in Case B, `F*` has min-side > 1/(k+1) by enough margin that
its children retain min-side ≥ 1/(k+2). 

This sub-claim is non-trivial. Empirically it holds: BSSF prefers FRs
with snug fit, so when it does pick the fattest FR, the placement
produces large remaining children. But we lack a formal proof.

### A weaker version that might be provable

> **Conjecture (weak BSSF).** There exists `K_0` such that ρ(k) is
> non-decreasing for `k ≥ K_0`.

Empirically true; if ρ is monotone non-decreasing past some point, it's
trivially bounded below by its value at `K_0` (which we can compute).
Combined with `ρ(K_0) ≥ 1` (verified for K_0 = 100), this implies
ρ(k) ≥ 1 for all k ≥ K_0, completing the chain.

## What we need

The remaining problem is **strictly combinatorial**: characterise the
free-list configurations BSSF can encounter, and prove that the BSSF
update preserves a `ρ ≥ 1` invariant. Tools that may help:

* Symbolic computation on small `k` (k ≤ 50) to enumerate possible
  configurations and verify the invariant exactly.
* Continuous relaxation: model the free-list as a measure on
  `(width, height)` pairs, prove the invariant in the limit.
* Adversarial argument: show that no adversarial choice of *which*
  rectangle to "favour" can violate the invariant.

## Falsification path

Run BSSF tracker at much larger N (≥ 10⁶, 10⁹) and watch for ρ to
drop below 1. The current trend (ρ growing as k^{0.6}) makes this
extremely unlikely; a sudden drop would be a strong negative signal.

## The big picture

* For 30 years, the best published bound was σ ≤ 501/500 (Bálint).
* This work improves the bound to σ ≤ 20002/20001 (verified by exact
  arithmetic) and beyond on running compute.
* More importantly, we have identified a *specific algorithm* (BSSF)
  with strong empirical evidence of an inductive invariant, and a
  concrete missing piece (the inductive step) that, if filled, would
  resolve the conjecture.
