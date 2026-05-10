# Closure Status — Meir-Moser Rectangle Packing

**Date:** 2026-05-10
**Repository state:** all Lean files compile via `lake build`; one Python warm-start certificate machine-checked by `native_decide`.

## The closure chain

```
              Python: BSSF MaxRects burn-in to N=100 + rectangulation
                              │
                              ▼
   Certificates/WarmStartN100.lean : warm_start_good : GoodTailState …
                          (proved by native_decide)
                              │
                              ▼
   MainTheorem.lean : meir_moser_packing_from_certificate
                          (proved from three axioms)
                              │
                              ▼
   Certificates/WarmStartN100.lean : meir_moser_packs_unit_square
                          : MoserPacksFrom 1 unitSquare
```

## What's proved unconditionally

- All four "easy" lemmas of the calibrated framework:
  - `TailSums.finite_tail_telescopes`
  - `Cellification.cellification_bounds`
  - `LRP.balanced_lrp_aspect_control`
  - `EndpointPotential.endpoint_area_bound_by_width_and_perimeter`
- All decidability machinery (`Rect`, `PlacedRect`, `FinitePacking`, `GoodTailState`, `NormalWidthCheck`).
- The empirical warm-start certificate: a finite list of 100 placed rectangles, each with valid Moser dimensions, pairwise interior-disjoint, contained in the unit square, and the `GoodTailState` invariants hold for the empirical parameters
  - `c = 185955818417 / 2422989616320 ≈ 0.0767`
  - `R = 1841146717 / 343394220 ≈ 5.36`
  - `η = 12487787361314006833544309799461 / 9926184571964537849828391135600 ≈ 1.258`
- The conditional theorem `meir_moser_packing_from_certificate`.

## Three remaining axioms (the research-mathematical core)

### Axiom 1: `calibrated_tail_theorem` (`WarmStart.lean:67`)

> Given a `GoodTailState γ c R η S widthChecks` for `1 < γ < 3/2`, the
> calibrated scheduler can pack all `D_n` for `n ≥ S.t` into
> `(1+ε)·S.container` for every `ε > 0`.

**To remove:** prove `MeirMoser.NormalBoxes` (the irrational sum bound — currently three sorrys),
plus a `SchedulerInduction` lemma plus a `DiagonalExtraction` lemma. See section *A.1–A.4* of the closure plan.

### Axiom 2: `martin_compactness` (`MainTheorem.lean:23`)

> ∀ ε > 0, MoserPacksFrom start (expandedContainer ε unitSquare)
>     → MoserPacksFrom start unitSquare

**To remove:** either (B.1) avoid compactness by sharpening the calibrated framework to produce exact unit-square packings, or (B.2) formalize Greg Martin's 2000 paper (arXiv:math/0005054) — multi-week project.

### Axiom 3: `moser_packs_combine` (`MainTheorem.lean:31`)

> Combining the prefix-list `S.placed` with `MoserPacksFrom S.t unitSquare` to
> get `MoserPacksFrom 1 unitSquare`.

**To remove:** straightforward list-manipulation proof, but requires strengthening `calibrated_tail_theorem` to guarantee the tail packing avoids `S.placed`. Bookkeeping; ~1 day of Lean work.

## Per-axiom plan

| Axiom | Mathematical content | Difficulty | Time |
|-------|---------------------|------------|------|
| `calibrated_tail_theorem` | The whole calibrated framework | Research | ~1 week |
| `martin_compactness` (B.1) | Exact-packing closure | Research | ~3 days |
| `martin_compactness` (B.2) | Formalize Martin 2000 | Engineering | ~3 weeks |
| `moser_packs_combine` | Prefix + tail concatenation | Bookkeeping | ~1 day |

## What this means for the Meir-Moser problem

The Lean project demonstrates: **assuming the three axioms above, the
Concrete Mathematics Problem 2.37 has a positive answer (the rectangles
`D_n = 1/n × 1/(n+1)` pack into `[0,1]²`)**.

The remaining work to make this *unconditional* is well-defined: replace
each named axiom with a Lean proof. The hardest is `calibrated_tail_theorem`,
which is the mathematical core of the calibrated Slack-Pack framework.

## Files

- `lean/MeirMoser/Geometry.lean` — Rect over ℚ, decidable.
- `lean/MeirMoser/TailSums.lean` — Σ 1/(n(n+1)) telescopes (proved).
- `lean/MeirMoser/FinitePacking.lean` — finite-prefix predicate, decidable.
- `lean/MeirMoser/Cellification.lean` — strip cell bounds (proved).
- `lean/MeirMoser/LRP.lean` — balanced aspect (proved).
- `lean/MeirMoser/EndpointPotential.lean` — area-by-perimeter (proved).
- `lean/MeirMoser/CalibratedScheduler.lean` — TailState + GoodTailState (decidable).
- `lean/MeirMoser/WarmStart.lean` — calibrated tail axiom.
- `lean/MeirMoser/MainTheorem.lean` — main reduction (proved from axioms).
- `lean/MeirMoser/NormalBoxes.lean` — sum bounds (3 sorrys, deferred).
- `lean/MeirMoser/Certificates/WarmStartN100.lean` — empirical warm-start, machine-checked.

## Python pipeline

- `src/mm_pack/`: Calibrated Slack-Pack package (geometry, scheduler, certificate, checker, rectangulation).
- `experiments/exp_009_warmstart_certificate.py`: emit Lean certificates from MaxRects burn-in.
- 25 unit tests passing in `tests/`.

## How to verify

```bash
cd lean && lake build               # green
grep -RIn "sorry" lean/MeirMoser \
  | grep -v Experimental \
  | grep -v NormalBoxes              # should show 1 result (a comment)
grep "axiom" lean/MeirMoser/*.lean \
  | grep -v Experimental             # 3 named axioms
```
