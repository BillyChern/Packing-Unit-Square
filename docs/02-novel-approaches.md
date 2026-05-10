# Novel Algorithmic Approaches — Brainstorm

The classical literature uses backtracking, MaxRects, edge-to-edge greedy, and look-ahead heuristics. Below are *new* angles, scoring, and tools we might bring to bear.

## A. Exploiting structural identities

`R_k = (1/k) × (1/(k+1))` has special relations rarely used in generic 2D packing:

1. **Strip dissection identity**:
   `R_k = R_{k+1}^{(rotated)} ∪ slim_k` where slim_k has dimensions `(1/k − 1/(k+1)) × 1/(k+1) = 1/(k(k+1)) × 1/(k+1)`. So a `1/k × 1/(k+1)` rectangle is "an `R_{k+1}` rotated, plus a sliver". This recursion may inform a **fractal-like** placement.

2. **Doubling identity**: `R_k = R_{2k} ∪ R_{2k} ∪ (lots of slivers)` — the "row of double-width" trick already used by Bálint.

3. **Cassini-like / hyperbolic identity**: `1/k − 1/(2k) = 1/(2k)`, so `R_k` width minus half-width equals R_{2k}'s width. Useful for binary tree placement.

4. **Aspect-ratio limit**: `R_k`'s aspect → 1 as k → ∞. They're nearly squares for k large. Once aspect is close enough to 1, packing is essentially the **squares 1/k²** problem — much easier (Meir-Moser-Paulhus solved related variants).

## B. Hierarchical / fractal layout

**Decimation strategy** (new):

- Place `R_1` at bottom of unit square: [0,1]×[0,1/2].
- The top half [0,1]×[1/2,1] is a 1×1/2 rectangle. Re-scale by 2 (vertically) → unit square.
- In this scaled square, the rescaled rectangles have dimensions `1/k × 2/(k+1)`, taller than wide. Place R_2 (rescaled) at the bottom-left ([0, 1/2]×[0, 2/3]). The remaining region is again an L.
- Recurse.

This is a self-similar structure. Whether the recursion closes (i.e., always works) is non-trivial — may need a tighter inequality. *Potential research finding*.

## C. Constraint-based exact packing

**SAT/SMT with rational arithmetic**: encode each rectangle's `(x_k, y_k, rot_k)` as variables; non-overlap as disjunctions of half-planes; containment as bounds. Use Z3 with `LIRA` (linear integer-real arithmetic).

For small N, can find optimum or prove infeasibility. The bottleneck is variable explosion. We can:
- Fix orientations greedily, only solving placement.
- Use **incremental SAT**: extend a partial solution.
- Use **MILP** with big-M for non-overlap.

**Beam search with SMT pruning**: keep top-K partial solutions, extend each by 1 rectangle, prune by SMT-checking whether extension is feasible.

## D. Continuous optimization (GPU-friendly)

Encode positions as differentiable variables; non-overlap as a soft penalty (squared overlap area). Run gradient descent on H100 for many random initializations in parallel.

```
loss = Σ_k ReLU(out_of_box(k))² + λ Σ_{k<l} overlap_area(k, l)²
```

Use coordinate descent / projected gradient / ADMM.

For large N, this is the only tractable approach. After the optimizer converges to a near-feasible solution, **snap** to a rational solution by carefully chosen rounding, and verify with exact arithmetic.

## E. Reinforcement learning policy

Train a policy (e.g., PPO) to choose placements one rectangle at a time. State: free-region map (image-based or feature-based). Action: which free rect + which orientation. Reward: −1 per failed placement, large bonus on completing N.

H100 → many parallel rollouts. Curriculum: train on N=100, then N=500, … . Could discover non-obvious heuristics that beat hand-designed ones (the literature mentions edge-to-edge contact greedy works well — RL might rediscover or improve).

## F. Look-ahead with rollouts (UCT / MCTS)

Like AlphaZero for tile placement: each node = partial packing, each edge = next placement choice. Use UCT to balance exploration/exploitation. Rollouts evaluate by random play to depth d.

The MO comments suggest "exact-fit" placements are rare — so MCTS may quickly converge to "pad densely, leave residual" patterns.

## G. Randomized + symmetry breaking

- **Random** choice of next rectangle's placement among feasible bottom-left positions, weighted by score.
- 180° rotation symmetry: any packing's reflection is also a packing; can use to break symmetry in MCTS.
- Multi-start: 10⁴ independent random runs in parallel on GPU.

## H. Algebraic / geometric direct construction

**Wild idea — explicit closed-form positioning**:

If the rectangles can be packed exactly, there should be *some* rule for `(x_k, y_k)`. Conjecture: there exist sequences `(x_k, y_k)` of the form
  `x_k = polynomial(k) / harmonic-like(k)`
that work. Search for such patterns in computational solutions.

If we can spot a recurrence — e.g. `x_{2k} = x_k + 1/k(k+1)` — we'd have a closed form, hence proof.

## I. Reduction to known problems

- **Rectangle packing in rectangle = NP-hard** for finite instances. But our instance has very special structure (harmonic widths).
- **Bin packing** with fractional pieces: maybe related to known wavelet-decomposition packings.
- **Problem of packing 1/k² squares**: solved (Meir-Moser, Paulhus). Our problem reduces to this asymptotically since R_k → near-square.

## J. The "infinite-prefix" angle

Don't pack R_1, R_2, …, R_N. Instead pack R_{2^j}, R_{2^{j+1}}, …, R_{2^{j+1}−1} as **batches** — each batch has `2^j` rectangles of similar size. The batches can be packed in geometric-area squares.

If batch j fits in some sub-region, and the union of regions fits in the unit square, we're done. The total area used by batches matches by telescoping.

This is essentially the doubling-row idea but rotated: rather than absorb the tail in an L-strip, pack everything as a doubling sequence.

## K. Computational program for *this* session

Given an H100 and exact-arithmetic Python:

1. **Step 1** (rigor): MaxRects with all four heuristics, run for N=100, 500, 1000, 2000, 5000, 10 000. Report largest N where we fit in [0,1]² (rigorously).
2. **Step 2** (search): Random restarts with edge-to-edge greedy. Keep best.
3. **Step 3** (exotic): Recursive L-shape strategy from §B. Verify it pushes beyond MaxRects.
4. **Step 4** (proof attempt): Try to *prove* the recursive strategy works for all N. If yes — Moser solved.

The wild-card is Step 4. We won't likely solve Moser today, but we can:
- Identify exactly where MaxRects fails.
- Map out the "crunch" landscape.
- Find a smarter heuristic by inspecting failure cases.
