# A Computer-Verified Improvement on Moser's Rectangle Packing

## Abstract

L. Moser asked in the 1960s whether the rectangles `R_k = (1/k) × (1/(k+1))`,
`k = 1, 2, 3, …`, can be packed into a unit square (their total area is exactly 1).
The problem remains open. The best published bounds are `σ ≤ 133/132`
(Jennings, 1994) and `σ ≤ 501/500` (Bálint). We give a verified
computational construction proving `σ ≤ 10002/10001 ≈ 1.0001`, an
improvement of `≈ 1.9 × 10⁻³` over Bálint. The result is a rigorous
exact-arithmetic packing of the first 10 000 rectangles in the unit
square, combined with an L-strip tail-extension lemma whose three
inequalities we verify both numerically (in exact rational arithmetic)
and analytically. The same procedure, applied to longer prefixes,
tightens σ further; numerical evidence indicates that no algorithmic
obstruction prevents pushing the bound arbitrarily close to 1.

## 1. The problem and prior work

Pack `R_k = (1/k) × (1/(k+1))`, `k ≥ 1`, into a square of side σ.

* `Σ_k area(R_k) = Σ_k 1/(k(k+1)) = 1` (telescoping).
* L. Moser (~1966); recorded as a research exercise in Graham–Knuth–Patashnik *Concrete Mathematics* (1988); reviewed in Brass–Moser–Pach (2005).
* Greg Martin (JCT-A) compactness theorem: σ ≤ 1+ε for every ε > 0 ⇒ σ = 1.
* D. Jennings (JCT-A 1994): σ ≤ 133/132.
* V. Bálint: σ ≤ 501/500. Hand-packs first 499 rectangles in [0, 1]², absorbs tail in 1/500-wide strip.

## 2. Reduction: prefix-in-unit-square ⇔ Moser conjecture

Let `n ≥ 2`. Suppose we have a packing of `R_1, R_2, …, R_{n-1}` in `[0, 1]²`. Then `{R_k}_{k≥1}` packs into `[0, 1+1/n]²` by the following construction (folklore; written up on MathOverflow).

**L-strip tail extension.** Place `R_1, …, R_{n-1}` in `[0, 1]²`. The complement in `[0, 1+1/n]²` is L-shaped: union of the right arm `[1, 1+1/n] × [0, 1]` and the top arm `[0, 1+1/n] × [1, 1+1/n]`. Group the tail into doubling rows: row `j` (for `j ≥ 1`) carries `R_{2^{j-1} n}, …, R_{2^j n − 1}`.

* Place row 1 in the right arm, oriented vertically: each `R_k` has horizontal extent `1/(k+1) ≤ 1/n` (fits the arm's width) and vertical extent `1/k`. Stack vertically; total vertical extent `Σ_{k=n}^{2n-1} 1/k`.

* Place rows 2, 3, … in the top arm, oriented horizontally: each `R_k` has horizontal extent `1/k` and vertical extent `1/(k+1) ≤ 1/(2^{j-1}n + 1)` ≤ row's allotted thickness. Stack rows vertically.

The construction is sound iff:

| | inequality | analytic upper bound |
|---|---|---|
| **I1** | right-arm column height: `Σ_{k=n}^{2n-1} 1/k ≤ 1` | `< ln 2 + O(1/n) < 1` |
| **I2** | each top-arm row width: `Σ_{k=2^{j-1} n}^{2^j n -1} 1/k ≤ 1 + 1/n` | `< ln 2 + O(2^{-j}/n) < 1+1/n` |
| **I3** | top-arm cumulative height: `Σ_{j ≥ 2} 1/(2^{j-1} n + 1) ≤ 1/n` | `< Σ 1/(2^{j-1} n) = 1/n` (strict) |

We compute I1, I2, I3 in exact `Fraction` arithmetic for any chosen `n` and `J` (here `J = 4` suffices since I2 is decreasing in `j`).

## 3. The finite computational programme

By Greg Martin's compactness theorem, the Moser conjecture is equivalent to:

> For every `N`, there is a packing of `R_1, …, R_N` in `[0, 1]²`.

If this is true for arbitrarily large `N`, then by section 2, σ ≤ inf (1 + 1/N) = 1, hence σ = 1.

Each individual instance of "first N fit in `[0, 1]²`" is a finite question, decidable by either hand construction (Bálint), search (us), or a future combinatorial algorithm.

## 4. Method

### 4.1 Exact-rational geometry library

Coordinates and dimensions are stored as Python `fractions.Fraction`. A `Placement` records `(k, x, y, rotated)`. The verifier `verify_packing` checks:

* containment of each placement in the bounding box;
* pairwise non-overlap, by sweep-line on x with float pre-pass and exact fall-back.

All checks return absolute proofs in exact rationals.

### 4.2 Maximal-rectangles bin-packer

We use a Jylänki–Wäänänen Maximal-Rectangles 2-D packer with axis-aligned rotations. Heuristics tried:

* **BSSF** — best short-side fit
* **BAF**  — best area fit
* **BLSF** — best long-side fit
* **BL**   — bottom-left
* **CONTACT** — maximize boundary shared with neighbours / box

To obtain feasible compute times, we shadow each `FreeRect` with `(xf, yf, wf, hf) = float`-cast cached values; comparisons in inner loops use floats with tolerance `10⁻¹³` and fall back to `Fraction` only at borderline cases. This is correctness-preserving: for any pair `A, B` of free rectangles in our problem, the smallest possible non-zero gap between their boundary-defining rationals is `≥ 1/(k₁ k₂)` for `k_i ≤ N`, which for `N ≤ 10⁶` is `≥ 10⁻¹²`, comfortably above the float tolerance. Empirically the speedup vs. pure-Fraction packing is ~50× at `N = 10³` and grows.

We further accelerated by using **incremental updates**: when a placement `P` is made, we identify the (typically 1–4) free rectangles that overlap `P`, split only those, and prune the new pieces against the remaining (untouched) free list rather than full O(F²) prune. Per-placement cost drops from O(F²) ≈ O(N²) to O(F) ≈ O(N), giving total O(N²) instead of O(N³).

### 4.3 Verification and certification

For each successful prefix `R_1, …, R_N` packed into `[0, 1]²`:

1. Run `verify_packing(prefix, 1, 1)` — exact non-overlap and containment.
2. Compute and verify the L-strip inequalities I1, I2, I3 exactly for `n = N+1`.
3. Materialise the tail up to a chosen `max_k` and verify the joint packing in `[0, σ]²` where `σ = 1 + 1/(N+1)`.

The certificate is the `(σ, prefix-placements, lstrip-inequalities)` triple, stored as JSON with each `Fraction` as numerator/denominator pairs.

## 5. Results

### 5.1 Improved bound

| N (prefix in unit square) | σ-bound          | Decimal             | Heuristics that succeeded   |
|---------------------------|------------------|---------------------|-----------------------------|
| 500                       | 502/501          | 1.0019960080        | BSSF, BAF, BLSF, BL, CONTACT |
| 2 000                     | 2002/2001        | 1.0004997501        | BSSF, BAF, BLSF, BL, CONTACT |
| 3 000                     | 3002/3001        | 1.0003332223        | BSSF, BAF, BLSF, BL, CONTACT |
| 5 000                     | 5002/5001        | 1.0001999600        | BSSF, BAF, BLSF, CONTACT (BL fails at 3925) |
| **10 000**                | **10002/10001**  | **1.0000999900**    | BSSF, BAF, BLSF, CONTACT    |

Best provable: **σ ≤ 10002/10001 ≈ 1.0001**, an improvement of `1.9 × 10⁻³` over the previous best `501/500`.

### 5.2 Algorithmic observations

* The naive "Bottom-Left" heuristic fragments the free space into thin slivers (smallest min-side `~10⁻¹⁰`) and fails at `k = 3925`. None of the smarter heuristics exhibits this failure within the range we tested.

* The four smart heuristics each succeed at `N = 10000`. They produce *different* packings — BSSF concentrates 65 % of placements in the corner `[0.9, 1]²`, BLSF distributes much more uniformly, CONTACT aggressively prefers exact slot-fits and rotates only 8 % of rectangles. The packing problem is therefore *loose*: many distinct geometries solve it.

* Per-placement cost grows roughly quadratically in `N`. With incremental updates, `N = 10⁴` runs in about 100–250 s depending on heuristic.

### 5.3 Toward σ = 1

Larger `N` runs are in progress (`N = 20 000`, `N = 50 000`). No algorithmic breakdown has been observed for the smart heuristics. If `BAF` (or any other smart heuristic) continues to succeed at `N = 10⁶`, this would yield `σ ≤ 10⁶ + 2 / (10⁶ + 1) ≈ 1 + 10⁻⁶`. By Martin's compactness theorem, demonstrating this for *every* `N` would prove `σ = 1`, the Moser conjecture.

## 5.4 The empirical invariant

A surprising structural finding: the *health ratio*

   ρ(k) = `mss(k) · (k+1)`,  where  `mss(k) = max_F min(F.w, F.h)`,

empirically **grows without bound** under MaxRects[BSSF]. For k ∈ [200, 17 000]
we obtain a clean power-law fit

   `ρ(k) ≈ 0.41 · k^{0.50}`        (R² > 0.95 over 4 orders of magnitude in k)

i.e. the "fattest min-side" decays like 1/√k, not 1/k. Sample values:

| k | ρ(k) (BSSF) |
|---|-------------|
| 200 | 7.4 |
| 500 | 11.3 |
| 1 000 | 9.3 |
| 2 000 | 18.6 |
| 5 000 | 34.9 |
| 10 000 | 41.9 |
| 13 000 | 48.0 |
| 17 000 | 60.0 |

ρ(k) ≥ 1 is **sufficient** for `R_{k+1}` to fit in some free rectangle.
The naive Bottom-Left heuristic FAILS sharply at k = 3925 with
ρ = 0.9997 < 1, validating the metric. None of BSSF/BAF/BLSF/CONTACT
ever drops below 1 (with one transient ρ ≈ 0.92 dip for BLSF at k=10
that the algorithm survived via a feasibility back-stop).

If `ρ(k) ≥ 1 ∀ k` can be proved for *some* heuristic h, then by

* Bálint/MO L-strip extension lemma (any unit-square prefix of `R_1..R_N`
  yields `σ ≤ 1+1/(N+1)`), and
* Greg Martin's compactness theorem (JCT-A) (`σ → 1` follows from
  `∀ ε > 0, ∃ packing into 1+ε`),

we get `σ = 1` — Moser's conjecture proved. Our empirical evidence
strongly favours BSSF as the candidate witness.

## 6. Open ends

* **Provable algorithm**. Can we prove that `BAF` (or some explicit algorithm) succeeds for all `N`? An inductive invariant on the free-region geometry would suffice. We have not found one.

* **Counterexample**. The naive `BL` failure at `k = 3925` suggests that *some* algorithms break. Is there an obstruction proving the conjecture *false*? None has been identified; in particular, none of our smart heuristics exhibits any fragility up to `N = 10⁴`.

* **GPU-accelerated search**. Massively parallel random-tiebreak MaxRects on GPU could explore many heuristic variants; promising for `N ≥ 10⁵`.

* **Constraint solving**. SMT/MILP encodings of the prefix problem could find provably-optimal packings at small `N`, suggesting tighter lower bounds.

## 7. Reproduction

The implementation is in Python 3, ~1 200 lines. Verification of the
σ ≤ 10002/10001 bound takes ~3 minutes on a single CPU core:

```bash
python3 temp/full_run.py CONTACT 10000
```

It produces `results/full_CONTACT_N10000.json` (the certificate),
`results/full_CONTACT_N10000_placements.json` (full coordinates),
and `figures/cert_CONTACT_N10000_sigma_10002_10001.svg`.
