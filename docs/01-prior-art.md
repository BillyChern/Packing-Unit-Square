# Prior Art on Moser's Rectangle Packing Problem

## The problem (Moser, ~1966)

Pack the rectangles `R_k = (1/k) × (1/(k+1))` for k = 1, 2, 3, … into a unit square. Total area = 1 by telescoping.

Recorded as a research exercise in *Concrete Mathematics* (Graham–Knuth–Patashnik, 1988, ch. 1). Surveyed in Brass–Moser–Pach, *Research Problems in Discrete Geometry*, ch. 3 (2005, still listed as open).

## Best known explicit bounds (square side σ)

| Year | Author        | Bound σ      | Method                                           |
|------|---------------|--------------|--------------------------------------------------|
| 1994 | D. Jennings   | 133/132      | JCT-A 1994, doi:10.1016/0097-3165(94)90116-3     |
| ~199x| V. Bálint     | **501/500**  | "A Packing Problem and Geometrical Series" (Disc. Math. proc.), and "Two Packing Problems"; packs first 499 rectangles into a unit square then absorbs the tail in a 1/500-wide strip |
| 2003 | G. Martin     | (compactness)| JCT-A; if σ ≤ 1+ε for every ε>0, then σ=1        |
| 200x | M. Paulhus    | claim of 10⁹| algorithmic, unverified rigorously               |

## Two crucial reductions

### (A) Compactness (Greg Martin)

If `A` packs into a square of side `1+ε` for every ε > 0, then `A` packs into the unit square. (Proof via compact subsets of the space of positionings.)

### (B) L-strip lemma (folklore, see MO answer 6)

If R_1, …, R_{n-1} pack into [0, 1]², then all rectangles pack into [0, 1+1/n]².

Proof: Pack R_1..R_{n-1} in [0, 1]². The complement in [0, 1+1/n]² is an L-strip of width 1/n. Group the tail into rows of widths 1/n, 1/(2n), 1/(4n), …; row j contains R_{2^{j-1} n} … R_{2^j n - 1}. Row j's total length is

  H_{2^j n} − H_{2^{j-1} n} = ln 2 + O(1/n) < 1.

The total of row heights is 1/n + 1/(2n) + … = 2/n; split this into two strips of width 1/n and place along the two arms of the L.

### Combined consequence

For every N such that R_1..R_{N-1} fits in the unit square, σ ≤ 1 + 1/N.

Since σ → 1 (by Martin's compactness) iff finite-prefix packings exist for every N, **the Moser conjecture is equivalent to: the first N rectangles fit in [0, 1]² for every N**.

## Computational results in the literature

- Bálint: 499 rectangles, manual / "with patience".
- Anonymous MO answerer: 40 000 rectangles via floating-point greedy with edge-to-edge contact heuristic. "Crunch point" near N=17 000.
- Mathematica MO answerer: 10 000 rectangles, no backtracking, scoring by (a−b)² of next 2–3 rectangles' fitting dimensions.
- Paulhus: claim of 10⁹ rectangles (origin unclear; possibly different problem variant).

## Algorithmic approaches reported

1. **Backtracking with vertex-sharing**: dies near N ≈ 255 (factorial blowup).
2. **Edge-to-edge greedy**: place each rectangle so that it shares maximum boundary with already-placed rectangles. Reaches 40 000+ in practice.
3. **Look-ahead minimization**: choose placement that minimizes (a−b)² for the next few rectangles' fits.
4. **MaxRects / Skyline**: standard 2D bin-packing offline heuristics.

## Numerical pitfalls

Exact contact tests get hard: nearly-zero quantities like `1/3912 + 1/4124 - 1/4050 - 1/3981 = 1/3612702562200` arise; floating-point precision <10⁻¹⁹ insufficient. Need rational arithmetic. Denominator growth: ≤ 10¹³⁸ for N=4 800 (related to OEIS A003418).

## Implications for our work

- We use exact `Fraction` arithmetic throughout — no precision concerns.
- Each N for which we fit R_1..R_{N-1} in [0,1]² gives σ ≤ 1+1/N. **N ≥ 501 beats Bálint.**
- The hard cases are around the empirical "crunch" (~17k); that's far beyond Bálint and would already be remarkable progress.
- A complete inductive argument that R_1..R_N always fit would solve Moser.

## Cited papers

1. D. Jennings, "On the packing of squares into a square", JCT-A 67 (1994). doi:10.1016/0097-3165(94)90116-3
2. V. Bálint, "A Packing Problem and Geometrical Series", Discrete Math (proc), doi:10.1016/S0167-5060(08)70600-9
3. V. Bálint, "Two Packing Problems", Discrete Math, doi:10.1016/S0012-365X(97)81831-6
4. P. Brass, W. O. J. Moser, J. Pach, "Research Problems in Discrete Geometry", ch. 3 (2005)
5. G. Martin, JCT-A, "Compactness theorems for geometric packings". sciencedirect.com/science/article/pii/S0097316501932091
6. M. Paulhus, "An algorithm for packing squares" (and follow-ups; squares-not-rectangles variant).
7. A. Joós, "On packing of rectangles in a rectangle".
8. arXiv:1705.02443 — packing-efficiency / continuity framework.
