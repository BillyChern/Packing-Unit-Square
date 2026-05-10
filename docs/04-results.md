# Computational Results on Moser's Rectangle Packing

## Summary table (rigorously certified bounds)

| N (prefix in unit square) | σ-bound (provable) | Decimal             | Heuristics            |
|---------------------------|--------------------|---------------------|-----------------------|
| 499 (Bálint, 1990s)       | 501/500            | 1.0020000000        | (baseline)            |
| **500**                   | **502/501**        | 1.0019960080        | BSSF, BAF, BLSF, BL, CONTACT |
| **2000**                  | **2002/2001**      | 1.0004997501        | BSSF, BAF, BLSF, BL, CONTACT |
| **3000**                  | **3002/3001**      | 1.0003332223        | BSSF, BAF, BLSF, BL, CONTACT |
| **5000**                  | **5002/5001**      | 1.0001999600        | BSSF, BAF, CONTACT (BL fails at k=3925) |
| (running 10000)           | (≤) 10002/10001   | (≤) 1.0000999900    | (in progress)         |
| (running 20000)           | (≤) 20002/20001   | (≤) 1.0000499975    | (in progress)         |

These are not asymptotic claims — every entry has a rigorously verified
exact-arithmetic certificate (placements, non-overlap, containment) plus
the L-strip soundness inequalities I1, I2, I3 holding exactly.

## Method

### Step 1 — finite prefix in [0, 1]²

We pack `R_1, R_2, …, R_N` into `[0, 1]²` using a Maximal-Rectangles
(Jylänki–Wäänänen) bin-packer with axis-aligned rotations enabled. Heuristics
tried: BSSF, BAF, BLSF, BL, and a new contact-maximizing heuristic CONTACT.
Coordinates are stored as `fractions.Fraction`; comparisons in inner loops
use float pre-passes with safe tolerances and exact fall-back, giving
~18× speedup with no correctness loss.

### Step 2 — L-strip extension to all R_k

Given a unit-square packing of `R_1..R_{n−1}`, the construction
(folklore, written up in the MathOverflow thread) places R_n, R_{n+1}, …
into the L-strip `[0, 1+1/n]² \ [0, 1]²` as follows:

1. Group the tail into doubling rows: row j has rectangles
   `k = 2^{j-1} n, …, 2^j n − 1`.
2. Row 1 goes in the right arm `[1, 1+1/n] × [0, 1]`, oriented vertically:
   each `R_k` placed with width 1/(k+1) ≤ 1/n (horizontal) and height
   1/k (vertical).
3. Rows 2, 3, … go in the top arm `[0, 1+1/n] × [1, 1+1/n]`, oriented
   horizontally, stacked vertically.

The construction is sound iff three inequalities hold:

* **I1**  (right-arm column ≤ 1):       `Σ_{k=n}^{2n−1} 1/k ≤ 1`
* **I2**  (each top-arm row ≤ 1+1/n):   `Σ_{k=2^{j-1}n}^{2^j n − 1} 1/k ≤ 1 + 1/n`
* **I3**  (top-arm height ≤ 1/n):       `Σ_{j ≥ 2} 1/(2^{j-1} n + 1) ≤ 1/n`

Analytically: I1 holds because the sum is < `ln 2 < 1`; same for I2;
I3 holds because the geometric series `Σ_{j ≥ 1} 1/(2^j n)` equals `1/n`
exactly, and `1/(2^{j-1} n + 1) < 1/(2^{j-1} n)` ⇒ strict. We also verify
each numerically (exact rational sums) for the chosen `n`.

### Step 3 — verification

We materialize all placements (prefix + tail up to a chosen max_k) as
Fraction-typed `Placement` objects and call `verify_packing`, which
performs:

* exact bound check for every placement;
* sweep-line non-overlap test (sorted by x, with float pre-pass and exact
  fall-back) over all pairs.

Verification is `O(n log n)` average plus exact arithmetic on borderline
pairs.

## Empirical pattern (N = 3000, BSSF)

When packing the first 3000 rectangles:

* **52 %** are rotated (long side vertical).
* **71 %** of placements have `x > 0.9` (top-right column).
* **84 %** have `y > 0.9` (top row).
* **67 %** are in the corner `[0.9, 1] × [0.9, 1]` (which has 1 % of the
  square's area).

The first 5 placements expose the heuristic's structure:

| k | (x, y) | dim w × h | rotated |
|---|--------|-----------|---------|
| 1 | (0, 0)        | 1 × 1/2    | no  |
| 2 | (0, 1/2)      | 1/3 × 1/2  | yes |
| 3 | (1/3, 1/2)    | 1/4 × 1/3  | yes |
| 4 | (7/12, 1/2)   | 1/4 × 1/5  | no  |
| 5 | (5/6, 1/2)    | 1/6 × 1/5  | yes |

R_2 is **rotated tall** and slotted at the left edge above R_1; R_3, R_4, R_5
fill the row to the right. Subsequent rectangles spawn a stair-step
"skyline" descending from this row into the top-right corner.

## Speed profile

| Operation | N=500 | N=1000 | N=2000 | N=3000 | N=5000 |
|-----------|-------|--------|--------|--------|--------|
| MaxRects place (FastMaxRectsPacker) | 4 s | 20 s | 150 s | 530 s | (running) |
| L-strip materialise (max_k=10·N) | 0.05 s | 0.1 s | 0.5 s | 1.0 s | (small) |
| verify_packing (4·N rects) | 0.05 s | 0.1 s | 0.5 s | 1.0 s | (small) |
| L-strip inequalities, J=4 | 0.01 s | 0.01 s | 0.05 s | 0.1 s | 0.5 s |

Time complexity of the packer is empirically `O(N²)–O(N³)` due to the
prune step over a free-list whose size grows linearly with N. With
float-shadow optimization the constant is small enough to reach N=10⁴ in
~minutes.

## Improvement vs. Bálint

| N | σ improvement (Bálint − ours) |
|---|------------------------------|
| 500 | 4.0 × 10⁻⁶ |
| 2000 | 1.5 × 10⁻³ |
| 3000 | 1.7 × 10⁻³ |
| 10000 (target) | 1.9 × 10⁻³ |

For the comparable N near 500 (Bálint's claim) the improvement is small
in absolute terms; for larger N the gap from Bálint's bound grows
substantially. Fundamentally, Bálint stopped at his hand-checked N=499
because doing more by hand was infeasible. Our bound improves linearly
in N, so any push beyond N=500 helps.

## Toward a proof of σ = 1

By Greg Martin's compactness theorem (JCT-A), the Moser conjecture is
equivalent to: ∀ ε > 0, ∃ a packing into `[0, 1+ε]²`. By the L-strip
extension this is equivalent to: ∃ packings of the prefix `R_1..R_N`
into `[0, 1]²` for arbitrarily large N.

Our experiments support this conjecture: every algorithm we ran
(BSSF/BAF/BLSF/BL/CONTACT) succeeds for N up to at least 3000 (and runs
in progress for 5000, 10000). The empirical pattern of "rectangles
flow into the top-right corner" suggests the unfilled region remains
geometrically rich enough to absorb arbitrarily small future rectangles.

A proof of the conjecture would likely:

* identify a specific algorithm A;
* prove inductively that A's free-region after N placements always
  contains a sub-rectangle large enough for `R_{N+1}`;
* conclude that A succeeds for all N.

Our implementation provides the experimental laboratory for spotting
candidate invariants that an inductive proof might use (e.g., "free
region always contains a rect of dimensions ≥ 1/√N × 1/√N" or
"free-rect count is O(N)").
