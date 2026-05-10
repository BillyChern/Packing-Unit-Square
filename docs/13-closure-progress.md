# Closure Progress (2026-05-10)

## Where we started this session

3 axioms + 5 sorrys outside Experimental, conditional theorem only.

## Where we are now

**Axioms outside Experimental:**
1. `WarmStart.lean: calibrated_tail_theorem` — original wholesale axiom (still on the closure path).
2. `CalibratedTailReduction.lean: good_state_implies_all_steps_succeed` — *smaller* axiom replacing the previous via the proved chain.

**Sorrys outside Experimental:**
1. `SchedulerInduction.lean:121` — schematic `calibratedStep_preserves_aspect_when_wide` (an early variant of A.3.c, replaced by the proved one in `SchedulerInductionLRPAspect.lean` — this stub is dead code).
2. `DiagonalExtraction.lean:61` — `iteratedStep_placed_length` inductive step (being filled by parallel agent).

(Plus 2 sorrys in `TwoBacktrack.lean` — placeholder lemmas not on the closure path.)

## Proved this session

| Theorem | File | Status |
|---------|------|--------|
| `mvt_bound_rpow_neg` | NormalBoxes.lean | ✅ |
| `finite_tail_sum_bound` (telescoping) | NormalBoxes.lean | ✅ |
| `calibrated_normal_sum` | NormalBoxes.lean | ✅ |
| `calibratedStep` (definition) | SchedulerInduction.lean | ✅ |
| `calibratedStep_LRP_area_lower` (A.3.b) | SchedulerInductionLRPArea.lean | ✅ |
| `calibratedStep_LRP_aspect_preserved` (A.3.c) | SchedulerInductionLRPAspect.lean | ✅ |
| `calibratedStep_preserves_endpoint_perim` (A.3.d) | SchedulerInduction.lean | ✅ |
| `newWidthCheck_holds` + `calibratedStep_widthChecks_extend` (A.3.e) | SchedulerInductionNormalWidth.lean | ✅ |
| `step_preserves_GoodTailState` (A.3.f) | SchedulerInductionCombine.lean | ✅ |
| `iteratedStep_container` | DiagonalExtraction.lean | ✅ |
| `extractedPacking` (definition) | DiagonalExtraction.lean | ✅ |
| `calibrated_tail_from_steps_success` (A.5 reduction core) | CalibratedTailProof.lean | ⚠️ shell, 4 sub-sorrys |
| `calibrated_tail_theorem_from_smaller_axiom` | CalibratedTailReduction.lean | ✅ |
| `moser_packs_combine` (was axiom) | MainTheorem.lean | ✅ |
| `meir_moser_packing_from_certificate` | MainTheorem.lean | ✅ |
| `meir_moser_packs_unit_square` (instantiated, depends on 1 axiom) | Certificates/WarmStartHand.lean | ✅ |

## Closure chain (current)

```
                                    ┌─ propext, Quot.sound, Classical.choice (Lean core)
meir_moser_packs_unit_square ◀──────┤
                                    └─ calibrated_tail_theorem (axiom)
                                       │ (replaceable via calibrated_tail_theorem_from_smaller_axiom)
                                       ▼
                                       ├─ good_state_implies_all_steps_succeed (smaller axiom)
                                       └─ calibrated_tail_from_steps_success (theorem, has sub-sorrys)
```

## Remaining work to fully close

1. **Fill sub-sorrys in `calibrated_tail_from_steps_success`** (4 sorrys: dims, inside, disj, avoid).
   Each is an induction over k, using the per-step preservation lemmas. Tractable given current foundation.

2. **Replace `good_state_implies_all_steps_succeed` axiom with proof** by induction:
   - Base k = 0: `GoodTailState ⇒ LRP fits D_t` for the initial t. Specifically: `S.LRP.area · t ≥ c` and aspect ≤ R imply `S.LRP.minSide ≥ √(c/R)/√t`. For `t` such that `√(c/R)/√t ≥ 1/t`, i.e., `t ≥ R/c`, the LRP fits D_t.
   - Inductive: `GoodTailState γ c R η S ⇒ GoodTailState γ c' R η (calibratedStep S)` (via `step_preserves_GoodTailState`), then apply IH to the new state. The c' is c minus a logarithmically-bounded sum, still positive.

3. **Replace `calibrated_tail_theorem` axiom in `WarmStart.lean`** with the derived theorem from `CalibratedTailReduction.lean`.

The proof structure is complete. The remaining work is the per-step inductive details.
