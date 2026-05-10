# N5 focused audit — global endpoint potential bound P_ep(t) ≤ η

**Date:** 2026-05-10
**Scope:** Single-claim assessment of N5 ("at every LRP-critical t, P_ep(t) := Σ_E (w(E)+h(E)) ≤ η"), based on `18-paper-audit.md` and `19-paper-N4.md`.

## Verdict: (c) coupled — controllable only under a scheduler that simultaneously breaks N4.

Per-step inequality S_ep(t) ≤ (C/t)·P_ep(t) is solid. The global η-bound is the load-bearing claim, and it survives only under an amortization scheme that conflicts with the oldest-first normal-box rule N4 needs.

## (a) Amortization sketch — the inequality one would have to prove

Decompose P_ep updates by event type:
- **Creation event (LRP cut, time t):** a fresh stripe spawns endpoints. Per cell, semiperimeter ≤ 3·a_t = 3·(1/(t+1) + t^{-γ}). Cellification produces N_t = ⌈M_t/m_t⌉ ≤ O(√(R·t/c)) cells, so
  ΔP_ep^{create}(t) ≤ C₁·N_t·a_t ≤ C₁·√(R/(c·t))·(1+o(1)).
- **Absorber event:** when D_t lands in endpoint E (priority rule), E is consumed and replaced by a residual of strictly smaller semiperimeter; per §10.3, w(E)+h(E) − [w(E')+h(E')] ≥ Δ·1/t for some Δ > 0 (the gain equals the placed item's perimeter contribution).
  ΔP_ep^{absorb}(t) ≤ −Δ/t.

A clean amortized bound would require, summed over [1, T]:
  Σ_{t ≤ T} ΔP_ep^{create}(t) ≤ Σ_{t ≤ T} (−ΔP_ep^{absorb}(t)) + η,
i.e.
  C₁·Σ_{LRP cuts at t} √(R/(c·t)) ≤ Δ·Σ_{absorber events at t} 1/t + η.   (*)

If LRP cuts occur at most #_{LRP}(T) ≤ O(T^{1−1/γ}) times (the dual of N4), the LHS of (*) is O(T^{1−1/γ}·T^{−1/2}) = O(T^{1/2 − 1/γ}). For γ < 2 this is unbounded as T → ∞. So even granting N4's sublinearity, raw cellification creates more endpoint perimeter than absorbers can drain; (*) **fails**.

The only way to rescue (*) is either (i) postpone cellification until enough absorber events have accumulated credit, or (ii) reduce per-cut cell count to N_t = O(1) by cutting only into balanced LRP slabs. Option (ii) is what N7 enables, and it would replace the √(R·t/c) factor by O(1), giving ΔP_ep^{create}(t) ≤ C₁/t. Then LHS of (*) is O(T^{1−1/γ}·T^{−1}) = O(T^{−1/γ}) → 0, comfortably absorbed by η.

So **N5 is plausibly true under (ii) + amortization**, modulo the still-open coupling below.

## (b) Counterexample — endpoint absorbers can't fire when N4's scheduler runs

Under the strict oldest-first normal-box rule N4 needs (§19), endpoints are *never* selected when a fittable normal box exists. Construct a cert with γ = 4/3 where, at every t ≥ 100, some B_k with k ≤ t^{3/4} survives and is fittable. Then the scheduler always routes D_t to B_k; absorber events on endpoints fire 0 times in [100, T]. Meanwhile every LRP cut spawns ≥ 1 new endpoint family, so
  P_ep(T) ≥ P_ep(100) + #_{LRP}(T)·c_{min}·a_{T} ≥ #_{LRP}(T)/T,
which is unbounded if #_{LRP}(T) ≫ T (or even if it's Θ(T^{1−1/γ}) and the growth dominates the per-event size). More concretely, even one create-event per ~T^{1/γ} LRP cycle without compensating drain pushes P_ep monotonically upward; lacking a sink, P_ep grows linearly in #_{LRP}(T).

This is the dual failure mode to N4's leak: there, endpoint priority starved normal-box consumption; here, normal-box priority starves endpoint absorption.

## (c) Coupled constraint — joint impossibility under fixed priority

Pin the issue precisely. Each LRP cut creates ≥ 1 new endpoint (in fact Θ(1) under N7's balanced regime). Each absorber event consumes 1 endpoint. So a stable system needs

  #_{absorbers}([1,T]) ≥ #_{LRP cuts}([1,T]) − O(η).        (†)

Both N4 (oldest-normal-first) and N5 (endpoint-first) want to be the *primary* placement target for D_t. Only one can: in any fixed-priority scheduler at most one queue is drained at the per-step rate. The other accumulates.

- **Endpoint-first:** drains endpoints (N5 OK) but starves normal boxes (N4 fails — old wide B_5 survives forever, S_norm > C/t).
- **Normal-first:** drains normal boxes (N4 OK) but starves endpoints (N5 fails — (†) violated).

A scheduler closing both must be **rate-limited interleaving**: spend exactly one absorber slot per O(t^{1/γ}) normal slot, matching (†) since LRP cuts arrive at rate t^{−1/γ} and normal placements at rate 1. Such a scheduler is **not** in §9.3 of the notes. Whether it preserves N3's normal-box width law (which assumed strict oldest-first) is an additional check the notes never perform.

**Bottom line:** N5 is not falsified outright — option (a) gives a viable amortization template — but the η-bound is only achievable under a scheduler that **redefines the priority hierarchy of N4 simultaneously**. Treating N4 and N5 as independent claims to discharge (as §§9.3–9.5 do) is the same Paulhus-style local-iterate-globally fallacy the audit flagged. The honest deliverable is a single coupled claim "N4∧N5" with a rate-limited scheduler, not two separable lemmas.
