# Moser's Rectangle Packing — Research Plan

## Problem Statement

Pack the rectangles `R_k = (1/k) × (1/(k+1))`, k = 1, 2, 3, …, exactly into a 1×1 square (rotations allowed).

- Total area: Σ 1/(k(k+1)) = 1  (telescoping)
- Open since Moser (1966); a Concrete Mathematics research exercise (Graham–Knuth–Patashnik, exercise 7.46 area).
- Best known: Bálint 501/500, Jennings 133/132 (square side).
- Computational packings exist for first 10⁴ rectangles.

## Realistic Goals (this session)

| Tier | Goal |
|------|------|
| T1 (must) | Build rigorous exact-arithmetic packer + visual verifier. |
| T2 (should) | Reproduce a packing into 1+ε for small ε (Meir–Moser style). |
| T3 (stretch) | Improve over 501/500 for finite N (computational evidence). |
| T4 (moonshot) | New theoretical insight — explicit infinite construction or impossibility argument. |

## Approach

1. **Foundation**: exact-rational geometry library (Python `Fraction`).
2. **Algorithms**:
   - Greedy shelf
   - Recursive Meir–Moser
   - "Pocket" residual: fit prefix optimally, fit tail by Meir–Moser bound
   - Heuristic: first-fit-decreasing-height with rotation
3. **Verification**: pairwise non-overlap + containment, all in `Fraction`.
4. **Visualization**: matplotlib SVG.
5. **Analysis**: track ε(N) = side of bounding square as a function of N.

## Key Identities (will use repeatedly)

- Σ_{k≥N+1} 1/(k(k+1)) = 1/(N+1).
- R_1 = 1×1/2. R_1 forces a full row (its width is 1).
- Subproblem: pack {R_k : k ≥ 2} into a 1×1/2 strip (total area 1/2).
- Tail bound (Meir–Moser): set of widths ≤ w, heights ≤ h, area ≤ A
  fits in a w × (h + A/w) rectangle (shelf algorithm).

## Strategy for an Infinite Packing

Place R_1 at the bottom (forced). The top strip [0,1]×[1/2,1] must absorb
the rest. After placing some prefix, the residual region must absorb the
tail (area 1/(N+1)). The tail has widths ≤ 1/(N+1), heights ≤ 1/(N+2),
so by Meir–Moser it fits any rectangle of width w ≥ 1/(N+1) with height
≥ 1/(N+2) + (1/(N+1))/w.

Take residual = strip of width c·1/(N+1) and height ~ 1/c for a tunable c:
height ≥ 1/(N+2) + 1/c. As N → ∞ height → 1/c. So if c ≥ 1, this fits in
a unit-height column iff c ≥ 1 (asymptotically). With c = 1, residual
strip of width 1/(N+1), height = 1/(N+2)+1, exceeds the unit square —
naive Meir–Moser alone is not tight. Need a multi-level / adaptive
residual.

## File Layout

- `src/geometry.py` — Rect, placement, exact predicates, verification.
- `src/algorithms.py` — packing algorithms.
- `src/visualize.py` — SVG rendering.
- `src/experiments.py` — driver scripts.
- `results/` — JSON logs of packings, gaps, statistics.
- `figures/` — SVG renders.
- `docs/` — write-up of findings.
