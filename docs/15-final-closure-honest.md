# Meir-Moser closure — final honest status

Date: 2026-05-10
Lean build: GREEN (`lake build` succeeds, no `sorry` outside `Experimental/` and `TwoBacktrack.lean`).

## Closure status

`#print axioms MeirMoser.Certificates.WarmStartHand.meir_moser_packs_unit_square`
returns:

```
[propext, Classical.choice, Lean.ofReduceBool,
 MeirMoser.good_state_implies_all_steps_succeed, Quot.sound]
```

i.e. the unit-square packing depends on Lean's core axioms plus exactly one
project-specific axiom: `good_state_implies_all_steps_succeed`.

## What's been done in this session

- Removed the original wholesale axiom `calibrated_tail_theorem` from
  `WarmStart.lean` and replaced it with the proved theorem
  `calibrated_tail_theorem_from_smaller_axiom` in
  `CalibratedTailReduction.lean`, which depends on the smaller axiom plus
  proved sub-lemmas.
- Filled all 4 sub-sorrys in `calibrated_tail_from_steps_success`
  (`CalibratedTailProof.lean`): dims, inside, disjointness, avoidance.
- Filled `DiagonalExtraction.lean` helper lemmas
  (`stepPlacement_idx`, `iteratedStep_t`, monotonicity, etc.) — sorry-free.
- Proved `step_preserves_GoodTailState` in `SchedulerInductionCombine.lean`
  by composing four per-step lemmas (`A.3.b/c/d/e`), each proved by a
  parallel subagent in `SchedulerInductionLRPArea.lean`,
  `SchedulerInductionLRPAspect.lean`, `SchedulerInduction.lean` (trivial),
  and `SchedulerInductionNormalWidth.lean`.
- Proved the base case of `good_state_implies_all_steps_succeed` in
  `AllStepsSucceedProof.lean`: when `t ≥ R/c`, the LRP minimum side ≥ 1/t,
  so D_t fits.
- `moser_packs_combine` and the prefix/tail combination in
  `MainTheorem.lean` are sorry-free, axiom-free.
- `Martin.lean` compactness was AVOIDED — the calibrated framework is
  sharpened to produce exact unit-square packings directly.
- Hand-built tight warm-start (N=1, c=1/2, R=2, η=0) and N=100 BSSF
  burn-in certificate verify `GoodTailState` via `native_decide`.

## The remaining axiom — honest math content

`good_state_implies_all_steps_succeed` claims:

> For any `(c, R, η, S)` with `GoodTailState c R η S`, the simplified
> scheduler `iteratedStep` succeeds at every iteration k ∈ ℕ.

In `CalibratedTailProof.lean`, "succeeds at iteration k" means: at
`iteratedStep k S`, the LRP's width and height are ≥ `1/(t)` and
`1/(t+1)` respectively, where `t = (iteratedStep k S).t`.

### The simplified-step soundness gap

The simplified `calibratedStep` always cuts a slice of width `1/t` from
the **left** of the LRP (no rotation, no balanced cut). Starting from the
hand-built cert (LRP = top half of unit square, width 1, height 1/2,
t = 2):

- After step 1 (place D_2): LRP width = 1 − 1/2 = 1/2.
- After step 2 (place D_3): LRP width = 1/2 − 1/3 = 1/6.
- Step 3 needs to place D_4 (width 1/4); but 1/4 > 1/6 ⇒ FAIL.

So `AllStepsSucceed` is false for the simplified step on this cert. This
means the smaller axiom — as written — is logically *unsound* for the
particular `iteratedStep` we have defined.

### What IS mathematically true

The deep mathematical content of the calibrated framework — and the
intended meaning of the bridging axiom — is:

> For any `GoodTailState`, *some* calibrated scheduler (with balanced
> cuts, rotation, cellification, endpoint management) succeeds at every
> iteration, and produces a tail packing of all D_n into S.container.

This requires:
- a **balanced step**: cut from the longer side of the LRP, optionally
  rotate D_t, to keep `LRP.aspect ≤ R` forever;
- **cellification** of finished strips so leftover area is reused;
- **endpoint management** so row leftovers don't grow (P_ep ≤ η).

For γ ∈ (1, 3/2), the sum Σ D_n.area = 1/t (telescoping) is bounded; with
balanced cuts and aspect ≤ R, the LRP minSide stays ≥ √(c/(R(t+k))),
which is ≥ 1/(t+k) iff (t+k)² · c/R ≥ 1, i.e. t ≥ R/c. So with the right
step function, AllStepsSucceed is genuinely true.

## To eliminate the axiom rigorously (remaining work)

Two routes, both substantial:

**Route A** — Rigorous balanced step:

1. Replace `calibratedStep` with a balanced version
   (`calibratedStepBalanced`) that:
   - cuts from the longer side, OR
   - rotates D_t when `D_t.height > D_t.width` and the LRP aspect demands.
2. Re-prove `step_preserves_GoodTailState` for the new step (the four
   A.3.b/c/d/e proofs need adaptation, but the LRP-area and aspect
   arguments still apply).
3. Re-prove the base case `base_step_succeeds` (already proved for the
   simplified step; geometry is essentially the same).
4. Prove `AllStepsSucceed` by induction: GoodTailState at iteration k
   implies LRP fits D_{t+k}, hence step k+1 succeeds and produces a new
   GoodTailState (with c' ≥ c · (1 − 1/(t+k)²) — explicit bookkeeping).
5. The cumulative bound: c_k ≥ c · ∏_{j=0}^{k-1} (1 − 1/(t+j)²) ≥
   c · (1 − Σ 1/(t+j)²) ≥ c · (1 − 1/t) ≥ c/2 for t ≥ 2. So c_k stays
   bounded below — the inductive invariant survives.

Estimated effort: 1–2 weeks of focused Lean engineering, with the
arithmetic of the balanced cuts being the main technical hurdle.

**Route B** — Higher-level abstraction:

1. Restate the axiom as a quantified statement over schedulers:
   ```lean
   axiom calibrated_scheduler_exists
       (c R η : ℚ) (S : TailState) (h : GoodTailState c R η S _)
       (h_t_pos : 1 ≤ S.t)
       (h_LRP_in_container : S.container.contains S.LRP)
       (h_LRP_disj : ∀ P ∈ S.placed, Rect.interiorDisjoint S.LRP P.toRect)
       : MoserPacksFromAvoid S.t S.container S.placed
   ```
   (i.e. the original `calibrated_tail_theorem` form.)
2. This is the standard "trust the framework" axiom — used in many
   formalization projects when the proof is in the paper but
   discharging it in Lean would balloon the project.

Effort: 5 minutes (revert to the original axiom).

## Honest summary

- The proof architecture is **complete and machine-checked** modulo
  one axiom.
- The single remaining axiom captures the deep-math claim that a
  calibrated scheduler exists for `GoodTailState` inputs — proved on
  paper (the Meir-Moser research notes, with γ ∈ (1, 3/2)), but the
  scheduler itself in `SchedulerInduction.lean` is a *simplified* form
  that does not actually implement balanced cuts.
- Therefore, while the build is green and `#print axioms` is clean
  except for the bridging axiom, **the bridging axiom as currently
  formalized is unsound for the simplified scheduler**.
- The closure of Concrete Math 2.37 is **conditional** on the deep
  research claim, with all surrounding scaffolding mechanically verified.
- Eliminating the residual axiom requires either implementing a balanced
  scheduler (Route A) or restating the axiom at a higher level
  (Route B).

The paper-side proof of the Meir-Moser theorem (in
`meir_moser_concrete_math_2_37_research_notes.md`) is the trusted
mathematical content; the Lean formalization captures the framework
structure but currently routes the deep claim through a simplified
step that is too weak to discharge it without further refinement.
