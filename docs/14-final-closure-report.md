# Meir-Moser Closure: Final Session Report (2026-05-10)

## Lean theorem produced

```lean
theorem meir_moser_packs_unit_square : MoserPacksFrom 1 unitSquare
```
in `lean/MeirMoser/Certificates/WarmStartHand.lean`.

`#print axioms` shows it depends on:
- `propext, Classical.choice, Lean.ofReduceBool, Quot.sound` (core Lean axioms)
- `MeirMoser.calibrated_tail_theorem` (the only project-specific axiom)

## Closure architecture

```
Python pipeline:
  burn-in (BSSF MaxRects) → rectangulation → certificate JSON
                                                ↓
                                           Lean exporter
                                                ↓
        ┌────────────────────────────────────┐
        │ Certificates/WarmStartHand.lean    │
        │ - placed: List PlacedRect          │
        │ - state : TailState                │
        │ - cParam=1/2, RParam=2, etaParam=0 │
        │                                    │
        │ theorem warm_start_good            │
        │   : GoodTailState ... := by        │
        │     native_decide   ◀──────── machine-checked
        │                                    │
        │ theorem meir_moser_packs_unit_square│
        │   := meir_moser_packing_from_certificate ...│
        └────────────────────────────────────┘
                          ↓
        ┌────────────────────────────────────┐
        │ MainTheorem.lean                   │
        │                                    │
        │ theorem meir_moser_packing_from_certificate│
        │   uses moser_packs_combine (proved) │
        │   uses calibrated_tail_theorem (axiom)│
        └────────────────────────────────────┘
                          ↓
        ┌────────────────────────────────────┐
        │ WarmStart.lean                     │
        │                                    │
        │ axiom calibrated_tail_theorem      │
        │   : GoodTailState                  │
        │     → MoserPacksFromAvoid          │
        │   ←── (replaceable via             │
        │        CalibratedTailReduction.lean)│
        └────────────────────────────────────┘
```

## Lemmas proved (no sorrys, no extra axioms)

| Component | File | Description |
|-----------|------|-------------|
| Rect over ℚ + decidable predicates | `Geometry.lean`, `FinitePacking.lean` | Containment, interior-disjointness, valid Moser dims |
| Telescoping `Σ 1/(n(n+1))` | `TailSums.lean` | `1/N - 1/M` |
| Cellification: cell aspect ≤ 2, semiperim ≤ 3M | `Cellification.lean` | |
| Balanced LRP aspect-control | `LRP.lean` | `t ≥ α²R/(c(1-1/R)²) ⇒` aspect preserved |
| Endpoint area-by-perimeter | `EndpointPotential.lean` | `Σ area ≤ (C/t)·Σ semiperim` |
| MVT-based decay bound: `x⁻γ - (x+1)⁻γ ≥ γ(x+1)⁻γ⁻¹` | `NormalBoxes.lean` | |
| Telescoping tail sum: `Σ k⁻γ⁻¹ ≤ (K-1)⁻γ/γ` | `NormalBoxes.lean` | |
| Calibrated normal sum: `Σ k⁻γ⁻¹ ≤ 2/t` for K ≥ t^(1/γ) | `NormalBoxes.lean` | |
| `calibratedStep` definition + `iteratedStep` | `SchedulerInduction.lean` | |
| Step preserves LRP area share (A.3.b) | `SchedulerInductionLRPArea.lean` | |
| Step preserves LRP aspect (A.3.c) | `SchedulerInductionLRPAspect.lean` | |
| Step preserves endpoint perimeter (A.3.d) | `SchedulerInduction.lean` | trivial (no endpoint changes) |
| Step extends widthChecks (A.3.e) | `SchedulerInductionNormalWidth.lean` | |
| `step_preserves_GoodTailState` (A.3.f) | `SchedulerInductionCombine.lean` | combines all four |
| `iteratedStep_container`, `stepPlacement_idx`, `iteratedStep_placed_length` | `DiagonalExtraction.lean` | |
| `extractedPacking` definition | `DiagonalExtraction.lean` | |
| `moser_packs_combine` (was axiom) | `MainTheorem.lean` | prefix + tail concatenation |

## Empirical certificates (machine-checked)

| File | N | (c, R, η) | Status |
|------|---|-----------|--------|
| `Certificates/WarmStartHand.lean` | 1 | (1/2, 2, 0) | tight; native_decide |
| `Certificates/WarmStartN100.lean` | 100 | (~0.077, ~5.36, ~1.26) | empirical; native_decide |

## What's left to make the closure unconditional

The closure depends on a single project-specific axiom:

**`calibrated_tail_theorem`**: GoodTailState ⇒ packing of all D_n into S.container.

This reduces (modulo sub-sorrys in `CalibratedTailProof.lean`) to:

**`good_state_implies_all_steps_succeed`** (smaller axiom in `CalibratedTailReduction.lean`): GoodTailState ⇒ at every iteration of `calibratedStep`, LRP fits the next Moser rectangle.

The remaining work to fully close:

1. Fill 4 sub-sorrys in `calibrated_tail_from_steps_success`:
   - dims (uses proved `stepPlacement_idx`)
   - inside (uses proved `iteratedStep_container` + LRP containment)
   - disjointness within tail (induction over `iteratedStep` placements)
   - avoidance vs prefix (induction; new placement inside shrinking LRP)

2. Replace `good_state_implies_all_steps_succeed` axiom by a proof:
   - Base case: `GoodTailState γ c R η S` with t ≥ R/c implies `LRP.minSide ≥ 1/t` (since `LRP.minSide² ≥ c/(R·t)`).
   - Inductive step: use `step_preserves_GoodTailState` (A.3.f) to propagate.

3. Replace `calibrated_tail_theorem` axiom in `WarmStart.lean` with the derived `calibrated_tail_theorem_from_smaller_axiom`.

After (1)+(2)+(3) the project depends on no project-specific axioms — only Lean core. The Meir-Moser problem (Concrete Mathematics 2.37) is then formally proved.

## Honest summary

- The session reduced the closure from 3 axioms + 5 sorrys (start) to **1 axiom on the closure path** + a few alternative-path sorrys being filled.
- `#print axioms meir_moser_packs_unit_square` confirms only one project-specific axiom (`calibrated_tail_theorem`) plus Lean core.
- The proof architecture is laid out: every component has a defined role, signature, and a (mostly) complete proof.
- 21 Lean files / 2079+ lines total; framework lemmas (telescoping, cellification, balanced LRP, endpoint potential, MVT bound, calibrated normal sum, scheduler-step preservation in 4 components, diagonal extraction, prefix combine) all proved.
- Empirical: tight (c=1/2, R=2, η=0) hand-built warm-start + N=100 BSSF burn-in cert, both `native_decide`-checked.
- Remaining work to fully eliminate the axiom: fill the 4 sub-sorrys in `CalibratedTailProof.lean` (induction over `iteratedStep` placements), prove `good_state_implies_all_steps_succeed` (geometric/cumulative-area bookkeeping), and wire them via `CalibratedTailReduction.lean`.
- Estimate: 1–3 person-days of focused Lean engineering to complete the formal closure of the Meir-Moser problem.
