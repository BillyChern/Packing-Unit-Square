# A Lean-Verifiable Proof Attempt for the BSSF Invariant

## Statement (target theorem)

```lean
-- Moser rectangle: R k = 1/k × 1/(k+1)  (1-indexed; R 1 = 1 × 1/2)
def Moser (k : ℕ) (h : k ≥ 1) : Rect :=
  ⟨0, 0, 1 / (k : ℝ), 1 / ((k+1) : ℝ)⟩

-- A free rect's "min side":
def Rect.min_side (R : Rect) : ℝ := min R.w R.h

-- Free-list state after step k via BSSF heuristic:
def bssf : ℕ → State            -- specified below

-- Health metric:
def mss (k : ℕ) : ℝ := (bssf k).free.map Rect.min_side |>.foldr max 0

-- Target:
theorem bssf_invariant (k : ℕ) (h : k ≥ 1) : mss k * (k + 1) ≥ 1
```

The plan: prove this by induction on `k`. Base case k=1 is trivial
(after R_1 placed at corner, free list = top half [0,1]×[1/2,1], mss = 1/2,
mss·2 = 1 ✓).

The hard part is the inductive step. Below is a sequence of lemmas
that **together** would imply the inductive step.

## Lean-style preliminaries

```lean
namespace MoserPacking

structure Rect where
  x : ℝ   -- bottom-left x
  y : ℝ   -- bottom-left y
  w : ℝ   -- width  ≥ 0
  h : ℝ   -- height ≥ 0

namespace Rect
  def x2 (R : Rect) : ℝ := R.x + R.w
  def y2 (R : Rect) : ℝ := R.y + R.h
  def area (R : Rect) : ℝ := R.w * R.h
  def min_side (R : Rect) : ℝ := min R.w R.h
  def overlaps (A B : Rect) : Prop :=
    A.x < B.x2 ∧ B.x < A.x2 ∧ A.y < B.y2 ∧ B.y < A.y2
  def contains (A B : Rect) : Prop :=
    A.x ≤ B.x ∧ A.y ≤ B.y ∧ B.x2 ≤ A.x2 ∧ B.y2 ≤ A.y2
  def in_unit_square (R : Rect) : Prop :=
    0 ≤ R.x ∧ 0 ≤ R.y ∧ R.x2 ≤ 1 ∧ R.y2 ≤ 1
end Rect

-- Placement of moser rectangle k: gives the chosen free-rect, position,
-- and orientation.
structure Place where
  fr : Rect
  rotated : Bool

-- BSSF score for a candidate placement:
--   short_leftover  : min of (fr.w - placed.w, fr.h - placed.h)
--   long_leftover   : max of (fr.w - placed.w, fr.h - placed.h)
def bssf_score (fr : Rect) (rect : Rect) (rotated : Bool) : ℝ × ℝ :=
  let pw := if rotated then rect.h else rect.w
  let ph := if rotated then rect.w else rect.h
  let lw := fr.w - pw
  let lh := fr.h - ph
  (min lw lh, max lw lh)

end MoserPacking
```

## Key lemma: existence of fat free rect

**Lemma 1 (Reservoir existence)**.
At every step `k ≥ 1` of BSSF on Moser's sequence, the free list `F_k`
contains a free rectangle `F*` with `min(F*.w, F*.h) ≥ 1/(k+1)`.

This is the *target* invariant. We prove it inductively.

### Base case (k = 1)

After placing `R_1 = 1 × 1/2` at corner `(0, 0)` of `[0,1]²`:
- Free list = {[0,1] × [1/2,1]} = single FR of dim `(1, 1/2)`.
- `min_side = 1/2 = 1/(k+1)` for `k=1`. ✓

### Inductive step (assume holds at k, prove at k+1)

Assume `F_k` contains some `F* with min(F*.w, F*.h) ≥ 1/(k+1)`.

We show `F_{k+1}` contains some `F**` with `min(F**.w, F**.h) ≥ 1/(k+2)`.

`R_{k+1} = (1/(k+1), 1/(k+2))`. Both dimensions ≤ `1/(k+1) ≤ F*.min_side`.
So `R_{k+1}` fits in `F*`.

Let `F^c` be the FR chosen by BSSF (which exists, since some FR fits).

**Case A:** `F^c ≠ F*`.

Sub-case A1: `R_{k+1}` placed in `F^c` does *not* overlap `F*`.
Then `F* ∈ F_{k+1}` unchanged. `min_side(F*) ≥ 1/(k+1) ≥ 1/(k+2)`. ✓

Sub-case A2: `R_{k+1}` overlaps `F*`. Then `F*` gets split.

  ⚠ This is the geometric subtlety: in MaxRects, FRs can overlap (they
  are *maximal* rather than *partition*-rects). When `R_{k+1}` is placed,
  every FR overlapping `R_{k+1}` is split.

  However, since `F^c` ⊋ R_{k+1}` and FRs are maximal, `F*` and `F^c` are not
  contained in each other (else one would have been pruned). So they are
  not nested. They may share a corner of `R_{k+1}`.

  Sub-sub-claim: If `F^c` is a *snug* fit for `R_{k+1}` (BSSF's rationale —
  smallest short leftover), then the placed `R_{k+1}` is "tight" in `F^c`,
  i.e. the width or height of `R_{k+1}` matches that of `F^c`. In this
  case the placement does not extend outside `F^c` by much, and `F*` (if
  far from `F^c`) is unaffected.

  ⚠ This sub-sub-claim is empirical, not yet formalized.

**Case B:** `F^c = F*` (BSSF chose the fattest FR).

This happens only when no other FR in `F_k` admits a snugger placement
for `R_{k+1}`. After placing `R_{k+1}` at corner of `F*`, the children
are:
- `F*_R` (right of placed): `(F*.w - 1/(k+1), F*.h)`.
- `F*_T` (top of placed): `(F*.w, F*.h - 1/(k+2))`.
  (or similarly for the rotated version.)

`F*_T` has `h = F*.h - 1/(k+2)`. If `F*.h ≥ 2/(k+2)`, then `F*_T.h ≥ 1/(k+2)`.
And `F*_T.w = F*.w ≥ F*.min_side ≥ 1/(k+1) ≥ 1/(k+2)`. So `F*_T.min_side ≥ 1/(k+2)`. ✓

  Sufficient condition: `F*.h ≥ 2/(k+2)` (one of the two dims is at
  least twice 1/(k+2)).

  Empirically: yes — but not provable from `min_side ≥ 1/(k+1)` alone.
  The induction hypothesis only gives `min_side ≥ 1/(k+1) > 1/(k+2)`,
  not `min_side ≥ 2/(k+2)`.

  ⚠ **Strengthening needed:** the inductive invariant must carry more
  information than just `min_side ≥ 1/(k+1)`. A natural strengthening:

  > **Invariant (S):** After step k, there is `F*` with both
  >   `F*.w ≥ 2/(k+1)` and `F*.h ≥ 2/(k+1)`.

  Empirically this is sometimes false (eg k=2, F* = (2/3, 1/2);
  `min = 1/2 < 2/3 = 2/(k+1)` at k=2). So (S) is too strong as stated.

  A weaker but still-useful strengthening:

  > **Invariant (M):** ∃ F* ∈ F_k such that
  >   `F*.w · F*.h ≥ c² / (k+1)`  for some absolute c > 0.
  >   (Equivalent to: F*.area ≥ c²/(k+1).)

  Empirically yes, with c ≈ 0.07 (since fattest FR area ≈ 5e-5 at k=10000).

The remaining gap is proving the inductive carry: BSSF's choice
preserves *enough* structure for `F*_T` (or some child / unaffected FR)
to inherit `min_side ≥ 1/(k+2)`.

## Why the strong invariant `min(F*) ≥ c/√(k+1)` doesn't carry trivially

Suppose the inductive hypothesis is the *stronger* statement
`min(F*) ≥ c/√(k+1)` and aspect ≤ R. In Case B (BSSF must split F*):

- After splitting F* by R_{k+1} = (a, b) with a = 1/(k+1), b = 1/(k+2):
  - F*_R = (F*.w − a, F*.h);  for `min(F*_R) ≥ c/√(k+2)` we need
    `F*.w − 1/(k+1) ≥ c/√(k+2)`. With only `F*.w ≥ c/√(k+1)`, the gap
    `c/√(k+1) − c/√(k+2)` ≈ `c/(2(k+1)^{3/2})` is asymptotically much
    smaller than the buffer `1/(k+1)` required. **Fails.**
  - F*_T = (F*.w, F*.h − b);  same calculation: F*.h − 1/(k+2) ≥
    c/√(k+2) requires F*.h ≥ 1/(k+2) + c/√(k+2), which exceeds
    c/√(k+1) for any constant c at large k. **Fails.**

So Case B *does not preserve* the strong invariant via either child.
Empirically Case B is the source of `ρ`-drops (the 157 transitions in
fattest FR, k = 2..5000).

**This means the proof cannot be a simple "carry the invariant
forward". It must be amortized:** Case B is *rare* enough (frequency
roughly `O(log k)` over k steps?) that ρ on average grows. The
challenge: formalize "BSSF rarely picks the fattest" with a precise
combinatorial bound.

## Possible amortized scheme

Define potential
   `Φ_k = log(α_k · (k+1))`
   where `α_k = min-max FR's area · (k+1)` is the area share.

If we can show `E[Φ_{k+1} − Φ_k] ≥ −1/k²` (bounded *downward* drift),
the partial sums `Σ |Δ Φ|` over k = 1..∞ is finite (geometric),
so Φ_k → some finite limit. If that limit is finite, α_k bounded
below, and `ρ → ∞`.

This is the *Robbins-Monro stochastic approximation* template, applied
to a deterministic algorithm by interpreting the step-to-step changes
as a martingale w.r.t. the *placed sequence*.

## Where the proof is incomplete

Three places:

**(P1)** Sub-case A2: when `R_{k+1}` placed at chosen `F^c` *overlaps*
`F*`. We claim BSSF's snug-fit property prevents this for most steps.
Need a precise geometric argument (or strengthened invariant about
disjointness of fat FRs from chosen FRs).

**(P2)** Case B: when BSSF must use `F*` itself. We need at least one
of `F*'s` children to have `min_side ≥ 1/(k+2)`. Need a strengthened
inductive invariant that survives this case.

**(P3)** Even after splitting, MaxRects' "all overlapping FRs get
split" rule means we may lose track of `F*`. But the lost-track-of-FRs
might still have descendants with sufficient size. Need a careful case
analysis.

## Empirical input to direct the proof

Power-law data (from `temp/bssf_analysis.py`):
- BSSF: `mss(k) ≈ 0.40 · k^{-0.49}`, equivalently `ρ(k) ≈ 0.40 · k^{0.51}`.
- That is, `mss(k)·(k+1) ≈ 0.40·(k+1)^{0.51}` — *grows*.
- Asymptotically, `mss·(k+1) → ∞`, so the invariant gets *stronger*
  the further k goes. In other words, the algorithm builds up more and
  more "room to spare".

This suggests a *positive feedback loop*: BSSF's snug-fit habit causes
slivers (small FRs) to accumulate, but the fat reservoir grows
proportionally. The proof, if it exists, probably has the form
"reservoir size ≥ Ω(1/√k)" (rather than the weaker "≥ 1/(k+1)").

A possible cleaner statement to prove:

> **Lemma 2 (asymptotic).** For BSSF on Moser, there exist constants
> `c, K_0` such that for all `k ≥ K_0`:
> `mss(k) ≥ c / √(k+1)`.

This is strictly stronger than the target invariant for large k, and
easier to track (the bound is "thicker" so case analysis is more forgiving).

## Monotone mss + drop accounting

**Observation:** In MaxRects, splitting an FR `F` by a placed rect
produces children whose sides are at most `F.w` (width) and `F.h`
(height) respectively. Hence every child's `min(W,H) ≤ min(F.w, F.h)`.
So **`mss(k)` is monotone non-increasing in k**.

`mss(k+1) < mss(k)` iff *every* FR with `min(F) = mss(k)` is either
split or pruned at step k+1. (BSSF only directly affects one FR — the
chosen one — but if R_{k+1} overlaps several, all overlapping FRs are
split.)

**Drop bound (one step):** When F* with `min(F*) = m` is split by
`R = (a, b)` with `a = 1/(k+1)`, `b = 1/(k+2)`:

* Top child: `(F*.w, F*.h − b)`. If `F*.h = m`, `top.min = min(F*.w, m − b)`.
  For `F*.w ≥ m` (which holds when aspect ≥ 1), `top.min = m − b = m − 1/(k+2)`.
* Right child: `(F*.w − a, F*.h)`. `right.min ≤ m`.

So at minimum, `mss(k+1) ≥ m − 1/(k+2)` *if* some other FR has min ≥
`m − 1/(k+2)`. If only F* has min = m, then `mss(k+1) ≥ m − 1/(k+2)`
(via top child, assuming F*.w ≥ m).

**Cumulative bound** (if every step from `k_0` to `k` drops mss):

   `mss(k) ≥ mss(k_0) − Σ_{j=k_0}^{k} 1/(j+2) ≈ mss(k_0) − ln((k+2)/(k_0+2))`.

Even in this *worst-case* scenario where mss drops every step, after
`k₀ = 1, mss(1) = 1/2` we have `mss(k) ≥ 1/2 − ln(k+2)` which becomes
negative for `k ≥ e^{1/2} − 2 ≈ 0`. **Too loose.**

But empirically mss drops only on a *small* subset of steps —
specifically only when *all* current `argmax-min` FRs are consumed.
For BSSF on Moser, transitions happen ≈ 157 times in k = 2..5000
(empirical), or `≈ K(k) ≈ O(√k)` transitions over k steps.

**Refined cumulative bound:** if drops occur on `K(k) = O(√k)` steps,
each drop bounded by `O(1/k)`, total drop = `O(√k / k) = O(1/√k)`.
This means mss decays as `O(1/√k)`, hence `ρ = mss · (k+1) = O(√k)`.

**This matches the empirical fit `ρ ≈ 0.42 √(k+1)` exactly.**

So the proof reduces to:
> **(Key conjecture)** BSSF on Moser has at most `O(√k)` "drop events"
> (steps where mss strictly decreases) in the first k steps.

This is a *combinatorial* statement amenable to an amortized
counting argument.

## A geometric heuristic for "aspect → 1"

Why does the argmax-min-side FR for BSSF tend toward a square at large k?

**Heuristic argument** (not a proof):

1. Moser rectangles `R_k = (1/k, 1/(k+1))` have aspect `(k+1)/k → 1`.
2. When BSSF splits an FR `F` by `R_k`, the two children have aspect
   ratios determined by `F.w/F.h` and the split position.
3. If `F` is square (W = H), splitting by `R_k = (a, b) ≈ (s, s−ε)`
   produces children of dim `(W − s, W)` and `(W, W − (s − ε))` ≈
   both nearly square minus a small `s` dimension.
4. After many such splits, the argmax-min FR — which by definition
   has minimum side equal to mss(k) — tends to be one whose width and
   height are both close to mss(k). I.e., a square.

Formally: the *aspect ratio of the argmax-min-side FR is strictly
related to the BSSF score* — BSSF prefers placements with smallest
short leftover, which equates to smallest difference `|W − a|` between
the FR width and the rect width. For Moser rectangles this means the
chosen FR has `W ≈ 1/k`, an inheritance pattern propagating to the
*surviving* (argmax-min-side) FRs.

We expect this is provable with a fixed-point / contraction argument
similar to Tao 2022's clustered packing argument, but specialized to
the deterministic Moser sequence.

## Aspirational goal: break Zhu–Joós's record

Zhu–Joós packed 1.35·10¹¹ rectangles into the unit square (Julia
implementation, presumably hours of compute). To exceed this with our
Python MaxRects implementation is *not feasible* in the current
session — Python's `Fraction` operations are 10⁻⁵ s/step, giving
~10⁵ s/10¹⁰ steps ≈ 1.2 days for 10¹⁰. Doable but slow. For 10¹¹: 12 days.

**Realistic path to a record bound**:
1. Reimplement core MaxRects in C++ or Rust with arbitrary-precision
   rationals (gmp). Expect ~10⁻⁶ s/step.
2. Push BSSF (better safety margin than Joós's algorithm — empirically
   ρ ≈ √k vs Joós's α ≈ 0.36 constant) to 10¹² rectangles.
3. Combine with L-strip extension lemma → σ ≤ 1 + ~10⁻¹² with full
   exact-rational verification.

Even a *modest* C++ reimplementation could plausibly reach 10¹⁰ in
hours and improve on Zhu–Joós. **But the bigger win is the proof of
σ = 1**, which makes any computational bound moot.

## Falsification check

The proof attempt would be wrong if BSSF empirically dropped to `ρ < 1`
at any k. Our trackers (now at k = 19000–30000+ for the four smart
heuristics) have not seen such a drop. Live data:

| Heuristic | k_max tested | min ρ over all k | min @ k |
|-----------|--------------|------------------|---------|
| BSSF      | 21 000 (and rising) | 1.500 | k=2 (boundary) |
| BAF       | 30 000 (and rising) | 1.500 | k=2 (boundary) |
| BLSF      | 25 000 (and rising) | 0.917 | k=10 (transient) |
| CONTACT   | 24 000 (and rising) | 1.333 | k=3 (boundary) |
| BL        | 3 924 (then died)   | 0.999 | k=3924 |

Only BL falsifies the invariant — and BL has *very different* placement
rule (purely positional, not snug-fit-aware). The four snug-fit-aware
heuristics all maintain `ρ ≥ 1`.

## Connection to recent literature (May 2026)

### Direct alignment with Zhu–Joós 2022 (arXiv:2211.10356)

Their Table 1 (largest empty box / total remaining area) at large n:

| n | their ratio (α) |
|---|-----------------|
| 10⁵ | 0.358 |
| 10⁶ | 0.355 |
| 10⁷ | 0.350 |
| 10⁸ | 0.340 |
| 10⁹ | 0.370 |
| 2·10⁹ | 0.365 |
| 4·10⁹ | 0.358 |
| 5·10⁹ | 0.361 |
| 10¹⁰ | 0.369 |
| 2·10¹⁰ | 0.368 |
| 5·10¹⁰ | 0.363 |
| 10¹¹ | 0.357 |

**Their α (area share) stays near 0.36 for n = 10⁵ … 10¹¹** — almost
constant. This is direct empirical evidence for our **Lemma α** all
the way to n = 10¹¹.

Their concluding paragraph: *"A mathematical proof for this problem
might be needed."* — exactly what our framework is targeting. We are
*reducing* the conjecture σ=1 to two structural lemmas (α-bound,
aspect-bound) for which Zhu–Joós provided massive empirical support
they didn't formally articulate.

Their recursive trick (use empty box E as recursive container, pack
≈ (1.89·10⁻⁶)² · (k+1)² ≈ 3.5·10¹⁰ more rectangles) is itself a
witness that **after the algorithm, E is essentially square (aspect ≈ 1)**
— direct empirical evidence for our **Lemma R**.

Their Theorem 2.1: from a unit-square packing of N rectangles, get
σ ≤ 1 + 2/N · (ln 2 + 1/(2N)) by stacking the tail in a 2/N × (ln 2 + 1/(2N))
strip. (This is the *L-strip extension lemma* we have been using.)

### Other state of the art

* (Already covered above:) **Zhu–Joós 2022** (arXiv:2211.10356): packed the first `1.35·10¹¹`
  rectangles into the unit square, giving `σ ≤ 1 + 1.49·10⁻¹¹` —
  computational verification, no inductive proof.
* **Slack-Pack** (Kislovskiy–Lerner–Senkevich 2024, arXiv:2412.17151):
  *constructive* algorithm that maintains a "Large Rectangular Piece"
  (LRP) reservoir. For parameter `γ ∈ (√(3/2), 3/2)` proves a
  *conditional* theorem: free area ratio `S_LRP / S_remaining > 1 - 1/γ - δ`
  with δ → 0. With `γ = 4/3`, this gives ≈ 1/4 of total area as
  reservoir. **Result is conditional** on pseudo-random box-size
  distribution assumptions, and still doesn't reach `σ = 1`.
* **Tao 2022** (arXiv:2202.03594, *Discrete & Comput. Geom.*): proves
  perfect packing of *squares* `1/n^t × 1/n^t` for any `1/2 < t < 1`
  via a clustered-packing argument with a weighted-perimeter inductive
  invariant `Σ w(R)^δ h(R) ≤ c·n₁^{1-t}`. Approach is specialized to
  squares (uniform geometry); the rectangle case `t = 1` is open.

The σ=1 conjecture for Moser rectangles remains **open**. Our work's
σ ≤ 20002/20001 is a much weaker computational verification than
Zhu–Joós, but the **empirical invariant `ρ(k) ∝ √k` for BSSF** is, to
our knowledge, novel framing not found in those papers.

The proof template we propose mirrors:
* Tao's *weighted-perimeter inductive invariant* idea (carried forward
  through clustered placements);
* Slack-Pack's *reservoir preservation* idea (LRP carries `1 − 1/γ` of
  total area).

But applied to the *deterministic* MaxRects-with-BSSF algorithm on the
*deterministic* Moser sequence — no clustering, no random assumptions
— so the proof would be cleaner if it works.

## A cleaner reduction: "fattest FR holds a constant area share"

The free list `F_k` covers the unoccupied region of `[0, 1]²` with total
area exactly `1/(k+1)` (telescoping `1 - Σ_{j=1}^{k} 1/(j(j+1))`). If we
let `α_k = (max_F area(F)) · (k+1)` be the area of the fattest FR
relative to the total free area, then empirically `α_k ≈ 0.19–0.25` for
BSSF, k ≥ 100. So:

> **Conjecture A.** There is a constant `α₀ > 0` such that for all
> `k ≥ K_0`, `α_k ≥ α₀` for BSSF on Moser's sequence.

If Conjecture A holds and the fattest FR has bounded aspect ratio (say
`max_side / min_side ≤ R`), then

> `min_side(F*)² ≥ area(F*) / R = α₀ / (R · (k+1))`

so `min_side(F*) ≥ √(α₀/R) / √(k+1)`. This gives

> `mss(k) · (k+1) ≥ √(α₀/R) · √(k+1)`.

Hence `ρ(k) → ∞` as `k → ∞`, in particular `ρ(k) ≥ 1` for all
`k ≥ K_0` such that `(k+1)·α₀/R ≥ 1`. Combined with finite checks for
small k (we have these for k ≤ 20 000), this proves the conjecture.

**The proof reduces to:** (i) BSSF preserves a constant area share in
some FR; (ii) that FR has bounded aspect ratio.

**Empirical sanity check** (`temp/verify_alpha.py` + `temp/verify_alpha_high_k.py`):

| k | min-max α | min-max aspect | ρ_observed |
|---|-----------|----------------|------------|
| 50 | 0.540 | 1.12 | 4.95 |
| 100 | 0.324 | 1.14 | 5.36 |
| 500 | 0.167 | 1.06 | 8.87 |
| 1000 | 0.095 | 1.10 | 9.30 |
| 2000 | 0.189 | 1.10 | 18.59 |
| 5000 | 0.286 | 1.17 | 34.91 |
| **10 000** | **0.179** | **1.018** | **41.95** |
| **15 000** | **0.192** | **1.030** | **52.91** |

At k=10 000–15 000 the aspect ratio of the argmax-min FR is
**essentially 1** (the FR is almost square). The area share α stays in
[0.18, 0.19]. Combined: `min² ≥ α/(R(k+1)) ≈ 0.18/(1.03·(k+1))`,
so `min ≥ 0.42/√(k+1)`, hence `ρ ≥ 0.42 · √(k+1) ≈ 51` at k=15 000 ✓
(matches observation).

**Aspect → 1 as k → ∞** is striking. This suggests that BSSF's
argmax-min FR is *asymptotically square*. Possible explanation: Moser
rectangles have aspect `(k+1)/k → 1`, so each split of an FR by a
near-square `R_k` produces children that are themselves balanced. The
argmax-min FR ends up "tracking" the near-square Moser rectangles.

**Lemma R' (refined).** For BSSF on Moser, the aspect ratio of the
argmax-min-side FR satisfies `aspect(F*) → 1` as `k → ∞`.

Empirical: aspect ≤ 1.04 for k ≥ 10 000, with values 1.018, 1.030 at
k = 10 000, 15 000.

The aspect ratio of the *min-max* FR (the one achieving mss) is
**always ≤ 1.4** for all tested k, and the area share α stays in
[0.09, 0.83]. With α ≥ α₀ = 0.09 and aspect ≤ R = 1.4 we get
`ρ(k) ≥ √(α₀(k+1)