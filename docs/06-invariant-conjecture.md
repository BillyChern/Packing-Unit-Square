# An Empirical Inductive Invariant for MaxRects on Moser's Sequence

## Statement

Let `MaxRects[BAF]` be the Maximal-Rectangles packer with the
Best-Area-Fit heuristic (and rotations enabled). Run it on the Moser
sequence `R_1, R_2, …, R_k` placed in `[0, 1]²` and let

> `mss(k) = max{ min(w(F), h(F))  :  F ∈ free-list after step k }`

i.e. the largest "minimum side" of any free rectangle. Define the
**health ratio**

> `ρ(k) = mss(k) · (k + 1).`

If `ρ(k) ≥ 1`, then the next rectangle `R_{k+1} = (1/(k+1)) × (1/(k+2))`
fits into some free rectangle (in either orientation, since both
dimensions of `R_{k+1}` are ≤ `1/(k+1) ≤ mss(k)`). So `ρ(k) ≥ 1` is a
**sufficient condition** for the algorithm to be able to continue at
step `k+1`.

## Empirical evidence (BAF)

Tracked `ρ(k)` at every step over `k = 2 … 19911`:

| Quantity              | Value     |
|-----------------------|-----------|
| min `ρ(k)`            | **1.5000** (occurred at k ∈ {2, 4}) |
| min over `k > 100`    | 2.7795 (at k = 2003) |
| max `ρ(k)`            | 15.34     |
| mean over k>100       | 7.997     |
| log-log slope of ρ vs k (k>100) | 0.0046 (≈ flat) |

`ρ(k) ≥ 1.5` throughout. Asymptotically `ρ(k)` is a near-flat function
of k, hovering around 8, suggesting the invariant is *not* eroding.

## Reservoir structure observed

`mss(k)` is piecewise constant: for long runs it equals a fixed
rational `1/D` for some integer `D`. The "reservoir" is a thin free
rectangle near the top boundary of the unit square. Sample
trajectory:

| k range               | mss(k)               | ρ(k) at end |
|-----------------------|----------------------|-------------|
| 1669 … 6438           | exactly `1/720`      | 8.94 → 4.47 |
| 6489 … (≥10000)       | exactly `61/73080`   | 5.42 → 8.35 |

When the reservoir is partially consumed, a *new* fat free rectangle
appears (typically still a thin horizontal strip near `y = 1`) and the
ratio jumps back up to ~10–15.

## Why the conjecture would suffice

If we could prove

> **Conjecture.**  For every k ≥ 2, `mss(k) ≥ 1/(k+1)` (i.e. ρ(k) ≥ 1)
> when MaxRects[BAF] is applied to the Moser sequence.

then `MaxRects[BAF]` packs all of `R_1, R_2, …` into the unit square,
yielding `σ = 1` — Moser's conjecture is proved.

By Greg Martin's compactness theorem the conjecture is *equivalent* to
"for every N, R_1..R_N pack into [0, 1]²". Since `mss(k) ≥ 1/(k+1)` is
a stronger statement (it provides an explicit witness for the next
step), proving it via combinatorial / geometric arguments gives a
constructive proof.

## Plausibility argument (sketch, not a proof)

After placing `R_k`, the free region has total area `1/(k+1)`. If this
area is concentrated in `O(k)` rectangles (empirically: F ≈ 0.95 · k),
the *average* free rectangle has area `≈ 1/(k(k+1))` — the same as
`R_{k+1}`.  Heuristically, by area alone the next rectangle should fit
in *some* free rectangle.

The geometric question is whether the area is distributed in shapes
favourable to `R_{k+1}`. The MaxRects-with-BAF empirical observation
is that *yes*, the algorithm preserves a thin strip whose thickness
scales like `1/k` (after a constant burn-in), and inside that strip
plus the smaller pockets, every `R_{k+1}` fits.

A formal proof would likely:
1. analyse one step of MaxRects + BAF as a function of the free-list
   configuration;
2. show that the configuration belongs to a class closed under the
   step (an inductive invariant);
3. show that within this class, `mss ≥ 1/(k+1)` always.

We do not yet have such a proof, but the data narrows the path:

* The "reservoir" patterns (1/720, 61/73080, …) are clean rationals;
  they hint that the invariant can be expressed in closed form.
* The min ratio `ρ = 1.5` is achieved only for the boundary-case
  small-k placements where `R_2, R_4` constrain the geometry; for k>100
  the minimum is much higher (≈ 2.8), suggesting the asymptotic
  behaviour is benign.

## Falsification path

If the conjecture is false, there is some `k*` such that `mss(k*) < 1/(k*+1)`,
i.e. `ρ(k*) < 1`. Our largest tested k is 19 911 with `ρ ≈ 15`. To
falsify, one would need to either:

* find a `k*` (computationally) where `ρ` drops below 1 — empirically
  this has not occurred for any of the four "smart" heuristics tested;
* construct a theoretical obstruction.

The naive "Bottom-Left" heuristic *does* break: `ρ(k)` falls below 1
at `k ≈ 3925`. So the conjecture is heuristic-dependent. Whether some
specific algorithm is *guaranteed* to maintain `ρ ≥ 1` is the open
question.
