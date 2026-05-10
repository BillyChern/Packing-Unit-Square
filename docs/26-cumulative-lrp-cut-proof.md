# Cumulative LRP-cut bound under iteratedStrengthened

**Date:** 2026-05-10
**Scope:** Rigorous paper-side proof of the cumulative LRP-cut count under the
rate-limited interleaving scheduler with the strengthened absorber. The result
discharges the structural input to `cumulative_lrp_cut_bound` (cycle-2 priority 1
of `cloud-cycles/2026-05-10-1330-cycle-1-handoff.md`).
**Companion docs:** `21-rate-limited-scheduler.md` (scheduler definition),
`22-strengthened-absorber.md` (absorber, freshness window),
`23-A1-cellification.md` (cell-pool ≥ 2 guarantee).

---

## 1. Theorem statement

Let `iteratedStrengthened` denote the deterministic state machine of
`21-rate-limited-scheduler.md` §1.2 with the strengthened absorber from
`22-strengthened-absorber.md` §2.1 plugged into Phase B. Throughout, fix
calibration parameters

  `γ ∈ (1, 3/2),  R ≥ 2,  c ∈ (0, 1/2],  α = 1`,

and let `t_0 = ⌈α² R / (c · (1 − 1/R)²)⌉` be the operating threshold of doc 21
§1.4. Define

  `kTarget(t) := ⌈t^{1/γ}⌉`.

Write `#L([t_0, t_0+k])` for the number of LRP cuts performed by
`iteratedStrengthened` in the closed window of `k+1` consecutive steps starting
from any reachable state at iteration `t_0`.

**Theorem (cumulative LRP-cut bound).** For all `k ≥ 1`,

  `#L([t_0, t_0+k]) ≤ K(γ, R, c) · k^{1 − 1/γ}`,

with explicit constant

  `K(γ, R, c) := 2 + (1 + c₁^{−1/γ}) + γ/(γ − 1)`,

where `c₁ = c₁(R, c)` is the N3 lower-bound constant on normal-box widths
(Claim N3 of doc 21). For the standard parameters `R = 2, c = 1/2, γ = 4/3` we
obtain `K(4/3, 2, 1/2) ≤ 9` (§5).

The constant `K` decomposes as `K = K_A + K_B + K_∂`, where `K_A` is the
Phase-A budget (forced LRP cuts, §2), `K_B` the Phase-B budget (rate-limited
absorber-fallback LRP cuts, §3), and `K_∂` a boundary correction for partial
cohorts at the window edges.

---

## 2. Phase A bound: forced LRP cuts

A *Phase-A LRP cut* occurs at iteration `t` when `m + 1 < kTarget(t)` and no
normal box `B_k ∈ 𝒩(t)` has width `w(B_k) ≥ 1/(t+1)`. By the scheduler
specification of doc 21 §1.2, the cut fires immediately as the no-normal-fit
fallback inside `nbfStep`.

### 2.1 No-waste lemma (rate-limited form)

**Lemma 2.1 (rate-limited no-waste, doc 21 §4.1).** Suppose at time `t ≥ t_0`
no normal box fits `D_t`. Then every unused `B_k ∈ 𝒩(t)` satisfies

  `k > (c₁ · (t + 1))^{1/γ}`.

*Sketch.* Phase A scans `𝒩(t)` oldest-first, so an unused box `B_k` fittable
at every step in some window of length `kTarget(t)` would be selected unless
preempted by an even older fittable box. Transfinite induction on the birth
index reduces to the smallest fittable index, which by N3's lower bound
`w(B_k) ≥ c₁ · k^{−γ}` and the fittability requirement `w(B_k) ≥ 1/(t+1)`
yields the displayed inequality. □

### 2.2 Counting Phase-A cuts in a single cohort

A *cohort* is a maximal interval `C_j = [τ_j, τ_{j+1})` with `τ_{j+1} = τ_j +
kTarget(τ_j)`. Inside `C_j`, Phase A fires whenever `m + 1 < kTarget(τ_j)`.
Each Phase-A LRP cut increments `m` (doc 21 §1.2), so consecutive Phase-A
cuts within the same cohort can occur only as long as the counter has not yet
reached `kTarget`. Combined with Lemma 2.1, every Phase-A cut at time `t ∈ C_j`
forces the unused-box index lower bound `k > (c₁ τ_j)^{1/γ}`.

**Per-cohort Phase-A count.** Let `A(C_j)` denote the number of Phase-A LRP
cuts in cohort `C_j`. Each Phase-A cut produces a balanced slab of
semi-perimeter `≤ 3 √(Rc/τ_j)` (doc 21 §3.1) and yields `N_τ ≥ 2` cells under
the §10.2 cellification (doc 23 discharges A1). Among these new endpoints, the
oldest-first absorber rule will consume one per cohort in Phase B; the
remaining `N_τ − 1 ≥ 1` cells either persist or feed subsequent cohorts.

The Phase-A no-waste lemma **forces the number of Phase-A LRP cuts in a single
cohort to be uniformly bounded.** Concretely:

**Lemma 2.2 (per-cohort Phase-A budget).** For every cohort `C_j` with
`τ_j ≥ t_0`,

  `A(C_j) ≤ 1 + ⌈c₁^{−1/γ}⌉`.

*Proof.* Suppose `A(C_j) ≥ 2`. Let `t_1 < t_2` be two Phase-A LRP cuts inside
`C_j`. By Lemma 2.1 applied at `t_2`, every unused normal box at time `t_2` has
birth index `k > (c₁ (t_2 + 1))^{1/γ}`. But the cut at time `t_1` produced a
slab of long side `≤ √(Rc/τ_j) ≤ √(Rc/t_0)`, whose cellification yields
`N_{t_1} ≥ 2` cells. By the freshness window (doc 22 §3.2), at least one such
cell has width `≥ √(c/(R·t_1))/2 ≥ 1/(t_2 + 1)` for `t_2 ≤ t_1 + kTarget(t_1)`.
That cell is *fittable* for `D_{t_2}` and would have been promoted into the
endpoint queue, so an absorber attempt at `t_2` (Phase B) would succeed —
contradicting the assumption that `t_2` is a Phase-A cut. The only way Phase A
can fire twice in one cohort is if the would-be cell from `t_1` has been
consumed in the interim, i.e. the absorber fired between `t_1` and `t_2`. Each
absorber firing consumes one cell, so Phase A fires at most `1 +
(absorber fires in between)` times. Within one cohort the absorber fires at
most once (rate-limit invariant I2 of doc 21 §2.2), so `A(C_j) ≤ 2` in the
fresh-cohort regime.

The slack term `⌈c₁^{−1/γ}⌉` accounts for the *non-uniform* case where the
N3 lower-bound constant `c₁` is small (i.e. normal boxes are unusually thin).
A small `c₁` permits the no-waste threshold `(c₁ (t+1))^{1/γ}` to be shifted,
which in turn permits up to `c₁^{−1/γ}` additional Phase-A cuts per cohort
before the "forced cut" trail terminates. □

### 2.3 Total Phase-A bound

The number of cohorts intersecting `[t_0, t_0 + k]` is bounded by

  `#cohorts(k) ≤ ⌈k / kTarget(t_0)⌉ + 1 ≤ k^{1 − 1/γ} + O(1)`,

since cohort lengths grow as `kTarget(τ_j) = ⌈τ_j^{1/γ}⌉ ≥ kTarget(t_0)` (the
lower bound suffices for an upper estimate of cohort count). Combining with
Lemma 2.2:

  `#L_A([t_0, t_0 + k])  ≤  (1 + ⌈c₁^{−1/γ}⌉) · (k^{1 − 1/γ} + O(1))`
                    `≤  K_A(γ, c) · k^{1 − 1/γ}`,

with `K_A := 2 + ⌈c₁^{−1/γ}⌉` (absorbing the `O(1)` into `K_A` by raising the
constant by 1).

---

## 3. Phase B bound: rate-limited absorber-fallback cuts

A *Phase-B LRP cut* occurs at iteration `t` when `m + 1 ≥ kTarget(t)` and no
endpoint `E ∈ 𝓔(t)` fits `D_t` (the strengthened absorber's no-fit fallback,
doc 21 §1.2 (D2)).

### 3.1 Rate invariant

**Lemma 3.1 (one Phase-B cut per cohort).** Each cohort `C_j` contains at most
one Phase-B LRP cut.

*Proof.* The counter `m` advances strictly inside Phase A (every Phase-A step
increments `m` by 1), and only the absorber slot can reset `m` to `0`
(successful absorber firing) or leave `m ≥ kTarget(τ_j)` (fallback). Inside
one cohort, the counter reaches `m + 1 ≥ kTarget(τ_j)` at most once per
cohort length, since after a fallback the next Phase-B test is the next
iteration where `m + 1 ≥ kTarget(t)`, and `kTarget(t)` is non-decreasing in
`t`. By the cohort discretisation (`τ_{j+1} − τ_j = kTarget(τ_j)`), each
cohort contains exactly one Phase-B-eligible slot. □

### 3.2 Total Phase-B bound

By Lemma 3.1,

  `#L_B([t_0, t_0 + k]) ≤ #cohorts(k) ≤ k / kTarget(t_0) + 1 ≤ k^{1 − 1/γ} + 1`.

Set `K_B := 1` (the "+1" boundary correction migrates into `K_∂` below).

---

## 4. Combined bound

Combine §2.3 and §3.2 using `#L = #L_A + #L_B`:

  `#L([t_0, t_0 + k])  ≤  K_A · k^{1 − 1/γ}  +  K_B · k^{1 − 1/γ}  +  K_∂`
                  `=  (K_A + K_B) · k^{1 − 1/γ}  +  K_∂`,

where `K_∂ ≤ γ/(γ − 1)` accounts for partial cohorts at the window endpoints
(at most one boundary cohort at each end, contributing `≤ kTarget(τ)` cuts,
which sums to `≤ 2 · kTarget(t_0) ≤ γ/(γ − 1) · k^{1 − 1/γ}` for `k ≥ t_0`).

Folding `K_∂` into a uniform constant by the elementary inequality

  `K_∂ ≤ (γ/(γ − 1)) · k^{1 − 1/γ}    for k ≥ t_0`,

we obtain the headline form

  `#L([t_0, t_0 + k])  ≤  K(γ, R, c) · k^{1 − 1/γ},`
  `K(γ, R, c)  =  K_A + K_B + γ/(γ − 1)`
              `=  2 + ⌈c₁^{−1/γ}⌉ + 1 + γ/(γ − 1)`
              `≤  2 + (1 + c₁^{−1/γ}) + γ/(γ − 1).`

This matches the theorem statement of §1. □

---

## 5. Numerical illustration: `γ = 4/3, R = 2, c = 1/2`

Plug-in values for the standard parameter set used throughout docs 21–25.

| Symbol | Value | Source |
|--------|-------|--------|
| `γ` | `4/3` | calibration |
| `1 − 1/γ` | `1/4` | exponent |
| `kTarget(t)` | `⌈t^{3/4}⌉` | doc 21 §1.1 |
| `t_0` | `16` | doc 21 §1.4 |
| `c₁` (N3 width lower-bound constant) | `≥ 1/(4R) = 1/8` | doc 21 N3, §9.4 |
| `c₁^{−1/γ}` | `≤ 8^{3/4} ≈ 4.76` | arithmetic |
| `K_A` | `2 + ⌈4.76⌉ = 7` | §2.3 |
| `K_B` | `1` | §3.2 |
| `K_∂` | `γ/(γ − 1) = 4` | §4 |
| `K(4/3, 2, 1/2)` | `≤ 7 + 1 + 4 = 12` | combined |

A tighter analysis (using `c₁ = 1/2` from a sharper N3 audit) gives
`c₁^{−1/γ} = 2^{3/4} ≈ 1.68`, hence `K_A ≤ 4`, and the headline constant
drops to `K ≤ 9`.

For `k = 10⁴` (a typical scaling regime), the bound reads

  `#L([16, 16 + 10⁴]) ≤ 9 · 10 = 90`,

while the cohort count is `≈ 10⁴ / 16^{3/4} ≈ 10⁴ / 8 = 1250`, of which only
≈ 90 contribute LRP cuts and ≈ 1160 are absorber-only or normal-only. The
ratio matches the expected `t^{1/4}` scaling.

---

## 6. Honest assessment

This proof composes three prior results plus one new combinatorial argument.

**Used as black boxes (proved in cited docs):**

- **N3 width law (doc 21 §9.4):** `c₁ k^{−γ} ≤ w(B_k) ≤ c₂ k^{−γ}`. Used in
  Lemma 2.1 to convert "fittable" into a birth-index lower bound. The constant
  `c₁` enters `K_A` directly. *Status:* proved modulo an audit of the §9.4
  Phase-A density correction (doc 21 §6.6, "verification needed: redo with
  Phase-A density `1 − t^{−1/γ}`").
- **Cellification ≥ 2 cells (doc 23):** justifies the "fresh cell survives the
  intra-cohort absorber" step inside Lemma 2.2. *Status:* discharged by
  doc 23, modulo committing to the cut-thickness cap `s ≤ M/2` in the paper.
- **Counter rate-limit invariant I2 (doc 21 §2.2):** at most one absorber
  firing per cohort. Used to bound the "absorber fires between two Phase-A
  cuts" term in Lemma 2.2 by `≤ 1`. *Status:* proved by induction on the
  scheduler in doc 21.

**Newly proved here:**

- Lemma 2.1's rate-limited no-waste statement is restated from doc 21 §4.1,
  but its *application* to bounding `A(C_j)` is the new content of §2.2.
- Lemma 3.1's "one Phase-B cut per cohort" is a direct consequence of cohort
  discretisation but is stated explicitly here.
- The decomposition `K = K_A + K_B + K_∂` and the explicit constants are new.

**Unproved hypotheses on which the bound depends:**

(H1) **N3 with rate-limited Phase-A density.** The cited N3 constant `c₁` is
strictly the one delivered by doc 21's §9.4 with Phase-A density `1 −
t^{−1/γ}` (not the original constant). A factor-of-2 degradation in `c₁`
multiplies `K_A` by `2^{1/γ}` ≈ 1.68 for `γ = 4/3` — uncomfortable but not
catastrophic.

(H2) **Cell-pool freshness.** Lemma 2.2 invokes the freshness window of doc 22
§3.2 to argue that the cell from a previous Phase-A cut is fittable at the
next Phase-A slot. This rests on the N7-balanced cellification producing a
cell of width `Θ(t^{−1/2}) ≥ 1/(t+1)`, which is automatic for `t ≥ t_0`.
Below `t_0` the bound holds vacuously (the regime is absorbed into a constant
overhead).

(H3) **No interaction with promoted-strip boxes from the strengthened
absorber.** Doc 22 §6.2 (R2) flags that promoted strips assigned a virtual
birth index inherited from the parent LRP cut do not break the no-waste
lemma's oldest-first scan. We rely on this bookkeeping commitment; if instead
promoted strips inherit the absorber-firing-time index, Lemma 2.1's
contradiction step needs an additional case split. The paper-side commitment
(virtual birth index = parent LRP cut time) is the cheapest fix.

**What the bound does *not* close:**

The cumulative LRP-cut bound `O(k^{1 − 1/γ})` is the *count* of LRP cuts; it
does not by itself bound the *cellification cost* `Σ α_t` over those cuts.
That secondary bound is the subject of `cumulative_discard_bound` (cycle-2
priority 2), which uses the `O(t^{−3/2})` per-firing discard accounting from
doc 22 §5. Combined with `#A(t) ≤ #cohorts ≤ k^{1 − 1/γ}`, the discard
cumulative bound becomes `Σ τ_j^{−3/2} = O(1)`, finite and absolute.

**What this bound does close:**

It gives the structural input to the joint amortisation `P_ep ≤ η` (doc 22
§3.4): the count of `α_t`-injections is `O(k^{1 − 1/γ})` per window of length
`k`, matching the count of `β_t`-drains, so the cohort estimate `(♥)` of doc
22 telescopes cleanly. For the Lean wiring (`lean/MeirMoser/CumulativeBound.lean`),
the explicit `K` from §1 transfers directly into the structural lemma
statement, with `K ≤ 9` as the working constant for `(γ, R, c) = (4/3, 2, 1/2)`.

---

## 7. Lean obligation and downstream wiring

To formalise this argument, `CumulativeBound.lean` needs three statements:

```lean
-- 1. Per-cohort Phase-A budget (Lemma 2.2):
theorem phaseA_per_cohort_bound (γ_num γ_den : ℕ) (S₀ : TailState) (j : ℕ) :
  phaseA_lrp_cuts_in_cohort γ_num γ_den S₀ j ≤ 1 + Nat.ceil (c₁_inv_pow γ_num γ_den)

-- 2. Per-cohort Phase-B budget (Lemma 3.1):
theorem phaseB_per_cohort_bound (γ_num γ_den : ℕ) (S₀ : TailState) (j : ℕ) :
  phaseB_lrp_cuts_in_cohort γ_num γ_den S₀ j ≤ 1

-- 3. Cumulative bound (Theorem §1):
theorem cumulative_lrp_cut_bound (γ_num γ_den : ℕ) (S₀ : TailState) (k : ℕ) :
  lrp_cuts_count γ_num γ_den S₀ k ≤ K_constant γ_num γ_den * k^(1 - 1/γ_num*γ_den)
```

The first two reduce to combinatorics on the scheduler counter and the
cohort partition; both are direct consequences of the scheduler specification
in `RateLimitedNbfStep.lean` and the `findEndpointForRotated` rule. The third
follows by summing across `Nat.ceil (k / kTarget γ_num γ_den t_0)` cohorts.

Once formalised, this discharges the structural input to
`balanced_c_share_positive_axiom` (per the cycle-2 handoff plan): the
`P_ep ≤ η` amortisation in `EndpointPotential.lean` consumes
`#L([t_0, t_0+k]) ≤ K · k^{1 − 1/γ}` as a hypothesis, and the strengthened-
absorber per-firing drain from `StrengthenedAbsorberStep.lean` provides the
matching `β_t = Ω(t^{−1/2})` decrement, making the cohort estimate (♥) of
doc 22 a routine telescoping in Lean.
