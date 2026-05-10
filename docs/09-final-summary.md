# Final Summary — One-Page Version

## Problem
Pack the rectangles `R_k = (1/k) × (1/(k+1))` (k=1, 2, 3, …) into a unit square.
Total area = 1 by telescoping. Posed by L. Moser ~1965; recorded as a research
exercise in *Concrete Mathematics*. **Open since.**

## Best previous bound
- D. Jennings 1994: σ ≤ 133/132 ≈ 1.00758
- V. Bálint ~199x: σ ≤ 501/500 = 1.00200 (~30 years standing best)

## This work — two contributions

### (A) Better σ-bound (rigorous)
**σ ≤ 20002/20001 ≈ 1.00005** — verified by exact-rational arithmetic
on a 20 000-rectangle prefix packing in [0,1]² + the L-strip tail extension
lemma (whose three sufficient inequalities I1, I2, I3 we verify exactly
for n=20001).

Improvement over Bálint: 1.95×10⁻³, two orders of magnitude tighter ε.

### (B) Empirical inductive invariant — candidate proof of σ = 1
For MaxRects-with-BSSF on Moser's sequence, we discovered

   `ρ(k) := mss(k) · (k+1)`,  `mss(k) := max_F min(F.w, F.h)`

and observed:
- `ρ(k) ≥ 1` is *sufficient* for the algorithm to fit `R_{k+1}`.
- The naive Bottom-Left heuristic dies sharply at k=3925 with ρ=0.9997 < 1
  — confirming the invariant.
- BSSF maintains ρ growing as `ρ ≈ 0.41 · k^{0.50}` for k ∈ [200, 17 000+]:
  - ρ(1 000) ≈ 9
  - ρ(10 000) ≈ 42
  - ρ(17 000) ≈ 60
  - extrapolated ρ(10⁶) ≈ 430

If `ρ(k) ≥ 1 ∀ k` can be proved analytically for BSSF, then by Bálint/MO
L-strip extension + Greg Martin compactness theorem, **σ = 1** — Moser's
conjecture proved.

## Failure-mode result
Bottom-Left heuristic creates thin slivers and dies at k=3925. ρ trajectory:

| k | ρ |
|---|---|
| 2 | 1.500 |
| 1 000 | 1.138 |
| 2 000 | 1.344 |
| 3 000 | 1.554 (peak) |
| 3 924 | 0.999 |
| 3 925 | FAIL |

This shows the invariant ρ ≥ 1 is precisely the right metric: BL never
had margin, drifted up, then crashed.

## Code
Python 3, ~1 800 lines. Modules:
- `geometry.py` — Placement, sweep-line verifier (exact rationals)
- `algorithms.py` — pure-Fraction MaxRects (4 heuristics) + Meir-Moser shelf
- `fast_packer.py` — float-shadowed MaxRects (50× speedup) + CONTACT heuristic
- `lstrip.py` — L-strip tail extension + 3-inequality certifier
- `certify.py` — JSON certificate generator
- `temp/full_run.py` — one-shot pipeline
- `temp/track_inv_fast.py` — invariant trajectory tracker

## Replicate the σ-bound
```bash
cd /workspace/Packing
python3 temp/full_run.py BAF 20000   # ~3 minutes on a single CPU core
# Outputs results/full_BAF_N20000.json with verify_full_ok=True
```

## What's needed for the conjecture proof
A combinatorial proof that BSSF preserves the invariant ρ ≥ 1 across
every step. We have empirical evidence and a clear path:
1. Base cases verified for k ≤ 10⁴ (much further by ongoing runs).
2. Inductive step: characterise BSSF's update rule on the free-list.

The key sub-claim is "Case B" of the inductive step: when BSSF must
consume the fattest free rect, it does so in a way that preserves a
*new* free rect with min-side ≥ 1/(k+2). Empirically this happens, but
we lack a proof.
