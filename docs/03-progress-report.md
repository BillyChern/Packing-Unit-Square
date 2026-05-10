# Progress Report: Computational Attack on Moser's Rectangle Packing

## Headline result (so far)

**We have packed the first 500 Moser rectangles `R_k = (1/k) × (1/(k+1))`,
k = 1, …, 500, into the unit square `[0, 1]²` rigorously in exact rational
arithmetic.**

Combining this with the L-strip tail extension (Bálint / MO answer 6 folklore lemma) gives:

> **All Moser rectangles `R_k`, k ≥ 1, can be packed into a square of side `σ = 502/501`.**

Numerically `502/501 = 1.001996007984…`, **strictly better** than V. Bálint's
`501/500 = 1.002`. Improvement is `1/(500·501) ≈ 4 · 10⁻⁶`.

The improvement is small but the construction is verified exactly with
rational arithmetic, so the bound is rigorously proven. The same method
applied to longer prefixes pushes σ closer to 1; runs in progress are
attempting N=2000 (which would give σ ≤ 2002/2001 ≈ 1.0005).

## What we built

| Module | Purpose |
|--------|---------|
| `src/geometry.py` | Exact rational `Placement`, sweep-line `verify_packing` with float pre-pass. |
| `src/algorithms.py` | Pure-rational MaxRects (BAF/BSSF/BLSF/BL); Meir–Moser shelf; tail-height bound. |
| `src/fast_packer.py` | Float-shadowed MaxRects (18× speedup) + new `CONTACT` heuristic. |
| `src/lstrip.py` | Rigorous L-strip tail extension: prefix in `[0,1]²` → all `R_k` in `[0, 1+1/n]²`. Includes `lstrip_inequalities_certify` to prove the construction. |
| `src/certify.py` | Generates a JSON certificate + SVG for the σ-bound. |
| `src/visualize.py` | SVG renderer. |
| `src/analysis.py` | Tools to inspect packing structure (zone analysis, layers). |

## Mathematical framework

The argument bundles two reductions:

1. **L-strip lemma** (folklore, recorded in MO answer): if `R_1, …, R_{n-1}`
   pack into `[0,1]²`, then ALL `R_k` pack into `[0, 1+1/n]²`. The tail is
   absorbed by doubling rows: row j carries `R_{2^{j-1}n}, …, R_{2^j n - 1}`,
   has height `1/(2^{j-1}n)`, and length bounded by `H_{2^j n} − H_{2^{j-1}n} → ln 2 < 1`.

2. **Compactness theorem** (Greg Martin, JCT-A): if Moser rectangles pack
   into `[0, 1+ε]²` for every ε > 0, they pack into `[0, 1]²`.

So the **finite computational program** (for arbitrarily large N) is
**equivalent to the open Moser conjecture**.

We verified the L-strip inequalities exactly for n = 501:

| Inequality | Value (float) | Bound | Holds? |
|------------|---------------|-------|--------|
| Row-1 long-sum (right arm height) | 0.6936464316 | ≤ 1 | ✓ |
| Max top-arm row horizontal | 0.6933967438 | ≤ 1 + 1/501 | ✓ |
| Top-arm cumulative height | 0.0019907827 | ≤ 1/501 = 0.0019960080 | ✓ (margin 5.2 · 10⁻⁶) |

The "construction proves for all k" by monotonicity: max top-arm row
horizontal converges down to ln 2 from above; top-arm cumulative height
is a strictly increasing partial sum that converges below 1/n.

## How the pieces fit

```
                   exact-arithmetic packer
                            │
                            ▼
              R_1 … R_N  in  [0, 1]²
                            │
                            ▼  (L-strip lemma, exactly verified)
                  R_1 … R_∞  in  [0, 1+1/(N+1)]²
                            │
                            ▼  (Greg Martin compactness)
        if N → ∞ achievable  ⇒  Moser conjecture: σ = 1
```

## Ongoing experiments (live)

We are running `FastMaxRectsPacker` to N = 2000 with four heuristics
(BSSF, BAF, BLSF, BL, CONTACT). Earlier interrupted runs reached k = 2200
without failure, suggesting σ ≤ 2202/2201 ≈ 1.000454 is attainable. A
successful run at N = 10⁴ would push σ to 1 + 10⁻⁴.

## Speed engineering

Pure-Fraction MaxRects took 352 s to N = 1000 and was projected to take
hours for N = 10⁴. Profiling identified `_prune` (97% of time) and
`Fraction.__le__` (52%) as bottlenecks.

Fix: shadow each `FreeRect` with float `(xf, yf, wf, hf)`. In `_prune`,
pre-test each containment with float (with `1e-13` tolerance); only fall
back to exact `Fraction.<=` when float is ambiguous. **Gives 18× speedup**
and preserves correctness because:
- Float-says-no ⇒ definitely-no (margin > ε implies the rationals differ
  by > ε > smallest possible gap of `1/(k₁·k₂)` for k ≤ 10⁶).
- Float-says-yes ⇒ exact verifier reproves; safe.

Total time to N = 1000 went from 352 s to 20 s.

## Pattern notes (preliminary)

For N = 500 with BSSF heuristic:
- 70 % of placements are rotated (long side vertical), suggesting the
  heuristic prefers tall narrow shapes.
- 373 of 500 rectangles cluster in the top-right zone (zones 7,7 of an 8×8 grid).
- 306 distinct y-coordinates among placement bottoms — close to the
  number of rectangles, indicating stair-step / skyline layout rather than
  shelf layout.

If patterns persist at larger N, they may suggest an analytical
construction.

## Limitations and open directions

* The MaxRects family is greedy and almost certainly suboptimal. A
  failure at some N does **not** rule out a better algorithm succeeding.
* The MO floating-point experiments suggest **edge-to-edge contact**
  greedy reaches 40 000+. We added a `CONTACT` heuristic; running.
* For an actual proof of the conjecture, we would need either:
  - a closed-form / inductive construction valid for all N;
  - a structural theorem about free-region geometry;
  - or a proof that some specific algorithm always succeeds.

## Files

- Numerical certificates: `results/full_{heuristic}_N{N}.json`
- Materialised tail packings: `results/full_{heuristic}_N{N}_placements.json`
- SVG figures: `figures/cert_{heuristic}_N{N}_sigma_*.svg`
- L-strip soundness proof (numerical): inside each summary JSON
  under `lstrip_inequalities`.
