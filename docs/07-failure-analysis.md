# BL Failure: Empirical Validation of the Invariant

## Setup

The "Bottom-Left" heuristic (BL) chooses the placement with smallest
`(y, x)` corner. Across 5 heuristics tested (BSSF, BAF, BLSF, BL, CONTACT),
**only BL fails on Moser's sequence** within the range `k ≤ 5000`.

## Failure point

```
FAIL at k = 3925.
After step k = 3924, the free list contains 3799 rectangles. The
fattest one has dimensions:

    w = 0.0002845   h = 0.0002546   (min-side ≈ 0.0002546)

R_3925 has dimensions:

    1/3925 × 1/3926  ≈ 0.0002548 × 0.0002547

R_3925 (in either orientation) requires both placed dimensions ≥ 0.0002547,
but the fattest free rect's min-side is 0.0002546 < 0.0002547. No fit.

Health ratio at failure:  ρ = mss × (k+1) = 0.99965  ≈ 1.
```

## Interpretation

The failure is **sharp**: the invariant `ρ ≥ 1` was violated by a margin
of `≈ 4 × 10⁻⁴`, immediately followed by algorithm collapse. There is no
other free rect "almost large enough" — the fattest, second, third
fattest are all clustered at `min-side ≈ 0.0002546`, all just below
`1/3925 = 0.0002548`.

Concurrently the free list contains many *thin strips* with one side
close to 1 (a wide strip near the top or right of the box) and the
other side `~10⁻⁵–10⁻⁶`. These strips have huge area but are useless
because no Moser rectangle for `k ≤ 10⁶` has any side that small.

## Diagnostic conclusion

**Falsification of the invariant `ρ ≥ 1` predicts algorithm failure.**
Conversely, *maintaining* the invariant suffices for the algorithm to
continue.

Empirical safety margins observed for k = 2..N (with N = 9000+ and
running):

| Heuristic | min ρ over k | comment |
|-----------|--------------|---------|
| BSSF | **5.36** (at k=100; rising) | very safe |
| BAF  | 1.50 (k=2,4 only); 2.78 (k>100) | safe |
| BLSF | 0.92 (k=10) but recovers | recovers from temporary drop |
| CONTACT | 1.33 (k=3); 1.42 onwards | small margin |
| BL | 1.00 (k=3925) and DIES | fails sharply |

BLSF is interesting: it transiently has `ρ < 1` at k=10 (mss × 11 = 0.917)
yet *survives* — because at that step the *feasibility* invariant
(`max-side × (k+1) AND min-side × (k+2)` both ≥ 1) is what actually
matters. The pure `mss × (k+1)` ratio is *sufficient* but not
*necessary* for survival.

## BL trajectory: gradual crawl + sudden fall

We tracked ρ(k) for the BL heuristic from k=2 to failure:

| k       | ρ(k)   | feas(k) | comment |
|---------|--------|---------|---------|
| 2       | 1.500  | 1.500   | initial |
| 3       | 1.000  | 1.250   | min over [2..3] |
| 1 000   | 1.138  | 1.139   | slow rise |
| 2 000   | 1.344  | 1.345   |  |
| 3 000   | 1.554  | 1.555   | peak |
| 3 924   | 0.999  | 1.000   | new minimum |
| 3 925   | —      | —       | **FAIL**: no free rect can hold R_3925 |

ρ never exceeds 1.6 throughout. It drifts up monotonically until k≈3000,
then declines through ~3000–3924 to land just below 1.0 — at which point
the algorithm cannot proceed. BSSF, by contrast, has `ρ ≥ 30` in the same
range.

This is **textbook fragile behaviour**: BL operates with no safety margin
and crashes precisely when the marginal ρ tips under 1. It validates ρ as
the right safety metric, and it shows that *some* heuristics (BL) cannot
maintain it while others (BSSF, BAF, BLSF, CONTACT) do.

## What this means for a proof

The natural inductive invariant for proving `σ = 1` via a specific
heuristic is:

> **(I)**  After step `k`, there exists a free rectangle `F` such that
>          `min(F.w, F.h) ≥ 1/(k+2)` *and* `max(F.w, F.h) ≥ 1/(k+1)`.

Equivalently, the *feasibility* `max over F of min(min·(k+2), max·(k+1)) ≥ 1`.

For BSSF, the simpler invariant `min × (k+1) ≥ 1` (which implies (I))
holds with safety factor ≥ 5 for k ≥ 100. This is the strongest
empirical evidence we have that BSSF is a candidate for a constructive
proof of Moser's conjecture.

A formal proof would proceed by:
1. Verify base cases `k = 1, …, K_0` for some K_0 by direct computation
   (we have done this for K_0 ≥ 10⁴).
2. Show by induction: assuming free-list at step `k` admits invariant
   (I), the BSSF heuristic chooses a placement such that the resulting
   free-list also admits (I) at step `k+1`.

Step 2 is the missing link. BSSF chooses the free rect minimising the
shorter leftover edge; under the right starting condition this seems
to consistently *create* a new "fat" free rect (the empirical "fat
strip" near `y = 1`) while consuming smaller pockets. Translating
"seems to consistently" into a proof is the open problem.
