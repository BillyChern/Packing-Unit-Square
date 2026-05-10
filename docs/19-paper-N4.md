# N4 focused audit — birth-index lower bound for unused normal boxes

**Date:** 2026-05-10
**Scope:** Single-claim assessment of N4 ("at LRP-critical time t, every unused normal box has birth index k ≳ t^{1/γ}"), based on `18-paper-audit.md` and `16-route-a5-status.md`.

## Verdict: (a) plausibly true under strict tie-breaking, but coupled to N5.

The summation algebra of N4 is fine: given N3 (w(B_k) ≍ k^{-γ}) and a floor K = c·t^{1/γ},
  Σ_{k ≥ K} k^{-(γ+1)} ≤ (1/γ)·K^{-γ} + O(K^{-γ-1}) = (1/γ + o(1))·(1/t).
The load-bearing claim is the floor K ≍ t^{1/γ} on *surviving* boxes.

## Why the floor is plausible

A normal box B_k has width ≍ k^{-γ}. D_t needs width 1/(t+1) (x-cut) or 1/t (y-cut). It fits iff
  k^{-γ} ≥ 1/t  ⇔  k ≤ t^{1/γ}.
If the scheduler always consumes a fittable normal box when one exists, then any unused B_k at time t must have k > t^{1/γ}. Done.

## The needed tie-breaking rule

For this contrapositive to bite, define:

> **Oldest-first normal-box rule.** If any unused B_k satisfies w(B_k) ≥ 1/(t+1) (or 1/t), place D_t into the *smallest such k*.

Under this rule, the consumption invariant holds by induction: a fittable B_k is always selected, so survivors are exactly those with c₁ k^{-γ} < 1/t, i.e. k > (c₁ t)^{1/γ} ≍ t^{1/γ}. With N3's two-sided width law and γ = 4/3, the floor is K ≍ t^{3/4}, giving S_norm(t) ≤ (3/4 + δ)/t — matching the audit's "1/γ + δ" coefficient.

## Why the actual scheduler may break this

The §9.3 scheduler does **not** strictly use oldest-first normal-box. Two leaks:

1. **Endpoint priority preempts normal-box selection.** §9.3 places D_t into a fitting endpoint *before* checking normal boxes (to keep P_ep bounded for N5). If endpoints of width 1/(t+1) are persistently available, D_t never touches normal boxes; an old wide B_5 (width ≈ 5^{-4/3} ≈ 0.135) survives indefinitely while endpoints absorb the stream. Counterexample candidate: any trajectory generating a steady supply of width-1/(t+1) endpoints starves old normal boxes. Concretely, if at every t there exists an endpoint with w ∈ [1/(t+1), 2/(t+1)], then B_5 with w ≈ 0.135 is bypassed forever, falsifying N4 with k = 5 ≪ t^{3/4}.

2. **Height/aspect ignored.** "Fittable" requires the box also be ≥ 1/(t+1) tall. The notes give no normal-box aspect invariant, so a wide-short box may be skipped for a newer fittable box, breaking oldest-first selection on width alone.

Leak (1) is the structural one. The audit's diagnosis of N5 (endpoint perimeter not provably bounded) compounds it: if endpoints can accumulate unboundedly, they can also absorb D_t indefinitely, indefinitely starving normal-box consumption. So **N4 and N5 fail or succeed together** under §9.3's priority rules.

## Bottom line

N4 is plausibly true under a *strictly* normal-box-first scheduler with explicit oldest-first tie-breaking, and the audit's diagnosis of "no-waste invariant missing" is precisely the missing scheduler axiom. Under the actual §9.3 endpoint-priority scheduler, N4 is **not** plausibly true without first closing N5 (or restructuring priority so endpoint absorption is budgeted, e.g., one endpoint placement per O(t^{1/γ}) normal-box placements). Closing N4 cleanly is therefore coupled to N5; treating it as independent is the gap the audit flags.
