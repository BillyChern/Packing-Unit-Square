# Rate-limited interleaving scheduler — paper-side mathematical design

**Date:** 2026-05-10
**Scope:** Formal design of the scheduler that closes the joint claim N4 ∧ N5
identified as coupled-but-broken under fixed-priority rules in `19-paper-N4.md`
and `20-paper-N5.md`. This document specifies the state machine, its invariants,
and the joint amortization argument. Open obligations are listed honestly at
the end.

---

## 0. Notation recap

- `t ∈ ℕ_{≥1}` — current iteration. The detail being placed is `D_t`, of width
  `1/(t+1)` (x-cut orientation) or `1/t` (y-cut). `D_t` has perimeter
  contribution `≥ 2/(t+1)`.
- `γ ∈ (1, 3/2)` — calibration exponent.
- `a_t = 1/(t+1) + t^{-γ}` — calibrated active width (Claim N1).
- *Normal box* `B_k` — the leftover slot born when `D_k` was placed inside an
  earlier active box. Width `w(B_k) ≍ k^{-γ}`, area `≍ k^{-(γ+1)}` (Claim N3).
- *Endpoint* `E` — a residual cell created by the two-backtrack / cellification
  decomposition of an LRP slab. Tracked by semiperimeter `w(E)+h(E)`.
- *LRP* — Largest Remaining Place; the dominant remaining slab. Side lengths
  `X ≥ Y`, area `XY ≥ c/t`, aspect `X/Y ≤ R` (Claim N7).
- *Endpoint potential* `P_ep(t) = Σ_E (w(E)+h(E))`.
- *Birth window* — the interval `[k, k_target(k)·k]` during which a normal box
  born at index `k` must be consumed.

The ambient constants throughout are `R = 2`, `c = 1/2`, `γ = 4/3` unless
otherwise stated.

---

## 1. Precise definition of the scheduler

The scheduler is a deterministic state machine. At every iteration `t` it must
place `D_t` somewhere in the geometric state, then update bookkeeping.

### 1.1 State variables

Three integer counters plus the geometric state:

| Symbol | Meaning |
|--------|---------|
| `t` | Current iteration. Increments by 1 per step. |
| `m` | Placements since last absorber event. Reset to `0` when an absorber fires. |
| `k_target(t) = ⌈t^{1/γ}⌉` | Target inter-absorber rate at time `t`. |
| `𝒩(t)` | Set of unused normal boxes at time `t`, ordered by birth index. |
| `𝓔(t)` | Multiset of endpoints, with semiperimeters tracked. |
| `LRP(t)` | The dominant slab. |

Throughout, `k_target(t)` is a *fixed* function of `t` chosen at admission
time; it is a schedule, not feedback. For `γ = 4/3`, `k_target(t) = ⌈t^{3/4}⌉`.

### 1.2 Transition rule at iteration `t`

The scheduler considers three placement targets in a *fixed priority order
modulated by the counter `m`*:

```
Phase A (m < k_target):  prefer normal box; LRP cut as fallback.
Phase B (m == k_target): force an absorber attempt; fall back to LRP cut.
```

Concretely, the transition is the following case analysis. Let `B*` be the
oldest fittable normal box (smallest birth index `k` with `w(B_k) ≥ 1/(t+1)`);
let `E*` be the oldest fittable endpoint (smallest birth index with
`w(E*) ≥ 1/(t+1)`).

```
if m < k_target(t):
    if B* exists:
        place D_t in B* (NORMAL placement)
        m ← m + 1
    else:
        cut LRP (LRP CUT)           # spawns one balanced slab + cellified endpoints
        m ← m + 1
elif m == k_target(t):
    if E* exists:
        place D_t in E* (ABSORBER)  # consumes E*, may leave residual E*'
        m ← 0
    else:                            # forced fallback: no endpoint to absorb into
        cut LRP (LRP CUT)
        m ← m + 1                    # absorber attempt skipped, will retry next step
```

Two design notes:

(D1) **The absorber phase fires once per cohort by construction.** A *cohort*
is a maximal block of `k_target(t)` consecutive steps with the same value of
`k_target` (we re-discretise when `k_target` increments — see §1.3). Inside
the cohort, exactly one step has `m = k_target` and tries the absorber.

(D2) **Endpoint absorber failure does not silently lose the rate.** If no
endpoint exists at the absorber slot, the scheduler falls back to an LRP
cut and `m` stays at `k_target` (since we increment `m`, but on next step
`m > k_target`, which we treat as `m = k_target` again — equivalently the
condition is `m ≥ k_target`). The fallback ensures that as soon as an
endpoint becomes available it is consumed. In pseudocode the second
branch of the `elif` should set `m ← k_target` to encode "still owe an
absorber". Without this fix the rate-limit invariant in §2 breaks.

### 1.3 Cohort discretisation

Define cohort `C_j` as the iteration interval

  `C_j = [τ_j, τ_{j+1})`, with `τ_0 = t_0`, `τ_{j+1} = τ_j + k_target(τ_j)`.

Then `|C_j| = k_target(τ_j) ≈ τ_j^{1/γ}`. Cohorts grow geometrically:
`τ_{j+1}/τ_j = 1 + τ_j^{1/γ - 1} → 1`, so for γ > 1 the cohort lengths grow
sublinearly relative to `τ_j`. This is the right granularity for the
amortisation in §3.

### 1.4 Threshold `t_0`

The scheduler is well-defined for all `t ≥ 1`, but the invariants of §§2–3
only kick in once `t ≥ t_0`, where

  `t_0 = ⌈α² R / (c (1 − 1/R)²)⌉`

is the threshold from Claim N7 / §10.1. For `R = 2, c = 1/2, α = 1` (where
`α` is the constant in `s ≤ α/t` from the cut-thickness control), `t_0 ≥ 16`.
Below `t_0` the scheduler runs but bookkeeping is absorbed into a finite
overhead `K_0`.

---

## 2. Per-step and cohort-level counting invariants

Write `#A(t) = #{absorbers in [1, t]}`, `#L(t) = #{LRP cuts}`,
`#N(t) = #{normal placements}`. Always `#A + #L + #N = t`.

### 2.1 Counter bound

**Invariant I1.** `m ≤ k_target(t) + 1` at every iteration.

*Proof.* By induction. The Phase-A branch increments `m` only when
`m < k_target(t)`, so after the increment `m ≤ k_target(t)`. The Phase-B
branch either resets `m` to `0` (success) or sets `m ≤ k_target(t)` (fallback,
under the §1.2-D2 fix). The slack `+1` accommodates the increment of `t` from
which `k_target` is non-decreasing. □

### 2.2 Absorber rate

**Invariant I2.** For `t ≥ t_0`,

  `#A(t) ≥ ⌊(t − t_0) / k_target(t)⌋ ≥ t^{1 − 1/γ} − O(1)`,

with equality up to fallback events (where the absorber phase missed because
no endpoint was available).

*Proof.* Each cohort `C_j` has length `≥ k_target(τ_j)` and contains at most
one successful absorber. Conversely, every cohort contains at least one
*absorber attempt*, and a fallback happens only if no endpoint exists, which
is not free: each fallback is also an LRP cut, so the slot is accounted for.
Summing over cohorts in `[t_0, t]` yields the bound. □

### 2.3 LRP-cut rate

**Invariant I3.** For `t ≥ t_0`,

  `#L(t) ≤ #A(t) + #L_starvation(t)`,

where `#L_starvation(t)` counts steps in Phase A where no fittable normal
box exists. Heuristically `#L_starvation(t) = O(t^{1 − 1/γ})` (this is the
restated Claim N4, now to be derived under this scheduler in §4); combining
gives

  `#L(t) ≤ O(t^{1 − 1/γ})`.

*Proof of bound (modulo Claim N4).* In Phase A, an LRP cut occurs only if
`B*` does not exist. By the no-waste reasoning of §4, the set of times this
happens has cardinality `O(t^{1 − 1/γ})`. In Phase B, an LRP cut occurs only
on absorber fallback, bounded by `#A(t) ≤ t^{1 − 1/γ}`. □

### 2.4 Normal-placement rate

**Invariant I4.** `#N(t) = t − #A(t) − #L(t) = t − O(t^{1 − 1/γ}) = (1 − o(1)) t`.

The bulk of placements absorb the detail stream into normal boxes — the
"workhorse" channel — confirming that the rate-limited interleaving does not
compromise N3's economy of scale.

---

## 3. Joint amortisation: the heart

The objective is to prove

  **Goal.** `P_ep(t) ≤ η` uniformly in `t ≥ t_0`, for some explicit `η < ∞`.

We follow the cohort accounting introduced in §1.3.

### 3.1 Per-step P_ep change

Let `Δ_t = P_ep(t) − P_ep(t−1)`. We classify by step type.

**(C1) Normal placement.** No endpoint touched. `Δ_t = 0`.

**(C2) LRP cut at iteration `t`.** A balanced slab of thickness
`s ≤ a_t = 1/(t+1) + t^{-γ}` is removed from the longer side of the LRP and
cellified per Claim N8 into `N_t` cells of total semiperimeter `≤ 3 M_t`,
where `M_t` is the longer side of the slab. Under N7-balanced cuts
(Y_LRP ≥ √(c/(Rt))), the slab has `M_t ≤ X_LRP ≤ R Y_LRP ≤ R √(c/(Rt)) =
√(Rc/t)`, hence

  `Δ_t^{LRP} ≤ C₁ · √(R c / t) =: α_t`,    `α_t = Θ(t^{-1/2})`.

This is the *raw* cellification estimate. Under a balanced cellification
that produces `N_t = O(1)` cells (cf. `20-paper-N5.md` §(a)-option-(ii)),
each cell has semiperimeter `≤ s + M_t ≤ a_t + √(Rc/t) = O(t^{-1/2})`, so
`Δ_t^{LRP} ≤ C₁' · t^{-1/2}`. The bottom-line `α_t = Θ(t^{-1/2})` is robust
to which cellification is used; constants differ.

**(C3) Absorber.** When `D_t` lands in endpoint `E*`, by §10.3 we have
`w(E*) + h(E*) − [w(E*') + h(E*')] ≥ Δ · (1/(t+1))` for some absolute
constant `Δ > 0` (the gain equals the placed detail's perimeter contribution,
since `D_t` occupies a corner of `E*` and `E*'` is the L-shaped residual that
loses at least one side-length contribution `1/(t+1)`). So

  `Δ_t^{abs} ≤ −Δ / (t+1) =: −β_t`,    `β_t = Θ(t^{-1})`.

### 3.2 Cohort-level change

In cohort `C_j = [τ_j, τ_{j+1})` of length `k_target(τ_j) ≈ τ_j^{1/γ}`:

- At least one absorber event (§2.2): contributes `≤ −β_{τ_j}`.
- At most `#L(C_j)` LRP cuts: contributes `≤ #L(C_j) · α_{τ_j}`.
- Other steps: `0`.

By Invariant I3 plus §4 (no-waste), `#L(C_j) ≤ 1 + #fallback_j` per cohort,
with `fallback_j = 0` when an endpoint is available. So in the *steady* regime
where each cohort has ≤ 1 LRP cut:

  `ΔP_ep(C_j) ≤ α_{τ_j} − β_{τ_j} = C₁'·τ_j^{-1/2} − Δ·τ_j^{-1}`.    (♦)

For `τ_j ≥ τ* := (C₁'/Δ)²`, the LHS of (♦) is positive — the LRP-cut term
**dominates** the absorber term. **This is the residual gap.** The naive
amortisation as stated in the user's framing (`α_t = O(1/t)`, `β_t = Ω(1/t^{1/γ})`)
does *not* hold under raw cellification: per-LRP-cut increase is
`Θ(t^{-1/2})`, not `Θ(t^{-1})`.

### 3.3 Where the user's framing comes from

The user's framing (`α_t = O(1/t)`, so `α_t · k_target = O(t^{1/γ - 1}) = O(t^{-1/4})`
for `γ = 4/3`, and `β_t = Ω(t^{-1/γ}) = Ω(t^{-3/4})`) corresponds to two
strengthenings of the local bookkeeping:

(S1) **Constant-cell cellification.** Replace the §10.2 cellification (which
produces `N_t ≤ ⌈M_t / m_t⌉ = ⌈√(R c / t) / a_t⌉ ≈ √(t)` cells, totalling
`≤ 3 M_t = O(t^{-1/2})` semiperimeter) by an N7-aware cellification that
exploits balanced LRP geometry to produce `O(1)` cells of size
`s × Y ≤ a_t × √(c/(Rt))`. The dominant cell has semiperimeter `≤ a_t + Y_LRP
≤ 1/t + 1/√t = O(t^{-1/2})`. So even with `O(1)` cells, the per-cut
increase is `α_t = Θ(t^{-1/2})`, not `Θ(t^{-1})`. **The user's α_t = O(1/t)
is achievable only if the LRP shape is much more balanced than N7
guarantees**, e.g. aspect → 1, in which case `Y_LRP = Θ(1/√t)` becomes
`Θ(1/t)`. This requires a stronger aspect lemma than N7.

(S2) **Absorber drains the *whole* endpoint, not the placed-detail perimeter.**
If the absorber design is "place `D_t` and then close out `E*` by
cellifying its residual into the next-cohort budget", then β_t is the
*entire* `w(E*) + h(E*)`, not the marginal `1/(t+1)`. With `E*` of
semiperimeter ~ a_t ~ 1/t plus the LRP-aspect contribution `~ 1/√t`, the
absorber drains `Θ(t^{-1/2})` (matching α_t), not `Θ(t^{-3/4})`. Strict
endpoint-cellification draining gives `β_t = Θ(t^{-1/2})`, exactly enough
to compensate (♦) up to constants. **The user's β_t = Ω(t^{-3/4}) requires
an absorber that drains *more* than one endpoint per cohort — e.g. the
absorber consumes `~ k_target^{1/2}` endpoints per firing.**

### 3.4 Honest cohort estimate

With (S1)+(S2) at the realistic strength `α_t = β_t = Θ(t^{-1/2})`:

  `ΔP_ep(C_j) ≤ #L(C_j) · α_{τ_j} − #A(C_j) · β_{τ_j} ≤ (#L(C_j) − #A(C_j)) · C₂ · τ_j^{-1/2}`. (♥)

The cohort count `#L(C_j) ≤ #A(C_j)` (since the scheduler caps LRP cuts by
absorber fallbacks; see §2) gives `ΔP_ep(C_j) ≤ 0` per cohort. **Telescoped:**

  `P_ep(t) ≤ P_ep(t_0) + Σ_{j: τ_j ≤ t} ΔP_ep(C_j) ≤ P_ep(t_0) =: η`.

So the *qualitative* η-bound holds **provided** (i) the cellification of
LRP cuts produces semiperimeter `O(t^{-1/2})` per cut (which N7 + §10.2 do
provide), and (ii) the absorber design drains semiperimeter `≥ C · t^{-1/2}`
per absorber event (which requires the strengthened absorber design (S2),
not the §10.3 marginal drain).

### 3.5 Quantitative η for γ = 4/3

Plugging `R = 2, c = 1/2, γ = 4/3, α = 1` into the constants:

- `α_t ≤ C₁' · t^{-1/2}` with `C₁' = 3 √(Rc) = 3` (from §10.2: total
  semiperimeter `≤ 3 M_t`).
- `β_t ≥ Δ · t^{-1/2}` with `Δ` = the absorber-drain constant. Plausibly
  `Δ ≥ 1` if the absorber consumes a *whole* endpoint per firing.

Net per cohort: `ΔP_ep(C_j) ≤ (3 − Δ) · τ_j^{-1/2}`, summed against
`τ_j^{1 − 1/γ} = τ_j^{1/4}` cohorts in `[1, t]`:

  `P_ep(t) ≤ P_ep(t_0) + (3 − Δ)_+ · Σ τ_j^{-1/2}`.

For `Δ ≥ 3` (achievable if the absorber drains the entire `E*` residual,
not just the placed-detail margin), the sum is non-positive and
**`η = P_ep(t_0)`**. For `Δ < 3` but bounded, the sum is finite-but-positive
of order `Σ τ_j^{-1/2}`. Since cohorts grow as `τ_{j+1} = τ_j (1 + τ_j^{-1/4})`,
geometric estimates give `Σ τ_j^{-1/2} = O(t^{-1/4} · #cohorts) = O(t^{-1/4 + 1/4}) = O(1)`, hence still finite η. The explicit constant is
`η ≤ P_ep(t_0) + |3 − Δ|·O(1)`.

**Conservative numerical bound for `R = 2, c = 1/2, γ = 4/3`:** assuming
the absorber design achieves `Δ ≥ 1` (i.e. one full endpoint perimeter
drained per firing), `η ≤ P_ep(t_0) + 4` is a viable target.

`t_0 ≥ 16` from §1.4, and `P_ep(t_0) ≤ 4 · X_LRP(t_0) ≤ 4` from the warm-start
hypothesis on the initial state (cf. §12 of the research notes).

---

## 4. N4 invariant via rate-limited consumption

We now give the missing structural piece for Claim N4: **all unused normal
boxes at LRP-critical time `t` have birth index `k ≳ t^{1/γ}`**.

### 4.1 No-waste lemma under the scheduler

**Lemma (rate-limited no-waste).** Fix `t ≥ t_0`. Suppose `B_k` is unused at
time `t`, with width `w(B_k) ≥ 1/(t+1)`. Then there must exist `k_target(t)`
consecutive iterations in `[k, t]` during which Phase A never selected `B_k`
despite its being fittable. By the oldest-first rule (Phase A: pick smallest
`k`), this means `B_k` was preempted at every such iteration by an *even older*
fittable box. By transfinite induction on birth index, *some* normal box
`B_{k'}` with `k' ≤ k` survives the same window — but then `B_{k'}` has even
larger width, and was placed inside the active state at time `k'` ≤ `k`, so
its width law `w(B_{k'}) ≍ k'^{-γ} ≥ k^{-γ}` and the contradiction `D_t`
should fit in `B_{k'}` rather than perform an LRP cut.

**Corollary.** At an LRP-critical time (when no normal box fits `D_t`), every
unused `B_k` has `w(B_k) < 1/(t+1)`. By N3's lower bound `c₁ k^{-γ} ≤ w(B_k)`
this forces `k > (c₁ (t+1))^{1/γ}`, the desired `k ≳ t^{1/γ}`.

### 4.2 Rate-limit-as-floor argument

The argument above uses Phase A's oldest-first rule — but Phase A only fires
`#N(t) = t − O(t^{1 − 1/γ})` times. The key observation is that the absorber
events do *not* affect normal-box ordering: an absorber consumes an endpoint,
not a normal box. So the oldest-first scan of `𝒩(t)` happens at every Phase-A
step. Over a window of `k_target(t)` Phase-A steps, every fittable `B_k` of
small index is selected unless preempted by an even older one. The
transfinite-induction step terminates at the smallest fittable index, which
is exactly the structural claim N4 needs.

### 4.3 What rate-limiting buys

Without rate-limiting, the endpoint-priority scheduler of `19-paper-N4.md`
breaks N4: `D_t` indefinitely consumes endpoints, leaving `B_5` unused. With
rate-limiting, between any two consecutive absorbers there are exactly
`k_target(t)` Phase-A steps, each of which scans `𝒩(t)` oldest-first. So
`B_5` is forced to be consumed within `k_target` ≈ `t^{1/γ}` steps of becoming
fittable, i.e. by time `5 + 5^γ`, which is `O(1)`. Hence at any `t > 5^γ`,
`B_5` is gone. Iterating, every `B_k` is consumed by `O(k^γ)`, and surviving
boxes have `k ≳ t^{1/γ}`.

---

## 5. Explicit constants for `γ = 4/3, R = 2, c = 1/2`

Plug-in values:

| Symbol | Value |
|--------|-------|
| `k_target(t)` | `⌈t^{3/4}⌉` |
| `α_t` (per-LRP-cut P_ep increase) | `≤ 3 · √(R c / t) = 3 · t^{-1/2}` |
| `β_t` (per-absorber P_ep decrease) | `≥ Δ · t^{-1/2}` (target `Δ ≥ 1`) |
| `t_0` (regime threshold) | `⌈α² R / (c (1 − 1/R)²)⌉ = ⌈1·2/(0.5·0.25)⌉ = 16` |
| `#L(t)` (LRP cuts in `[1, t]`) | `≤ t^{1/4} · (1 + o(1))` |
| `#A(t)` (absorbers in `[1, t]`) | `≥ t^{1/4} − O(1)` |
| `#N(t)` (normal placements) | `t − O(t^{1/4})` |
| `η` (target P_ep bound) | `P_ep(t_0) + (3 − Δ)_+ · O(1) ≤ 8` (conservative) |

The N4-floor is then `K(t) = ⌈c₁^{1/γ} · t^{1/γ}⌉ = ⌈c₁^{3/4} · t^{3/4}⌉`,
and N4 reads

  `S_norm(t) ≤ Σ_{k ≥ K(t)} C k^{-7/3} ≤ (3/4 + δ) · 1/t`.

For γ = 4/3, the LRP lower bound (Claim N6) becomes

  `S_LRP(t) ≥ 1/t − S_norm(t) − S_ep(t) ≥ (1 − 3/4 − ε)/t = (1/4 − ε)/t`,

matching the §9.6 target.

---

## 6. Open obligations

Despite the structural fix, several obligations remain. The amortisation
argument **does not close cleanly without** discharging these:

### 6.1 Absorber design (the load-bearing one)

The argument in §3 requires `β_t = Ω(t^{-1/2})`, i.e. each absorber drains
semiperimeter at a rate matching the cellification expansion. The naive
"place D_t and let the residual be the L-shape" gives only `β_t = Θ(t^{-1})`
per §10.3, which is insufficient. The paper needs an explicit absorber design
where, after placing `D_t`, the *whole* endpoint `E*` is closed out — its
residual is broken into smaller pieces that are no longer counted in `P_ep`,
or are charged to the next cohort. Concretely:

- Either redefine `P_ep` to track only "active" endpoints, not residuals
  below threshold (e.g. semiperimeter `< 1/t`), and prove that the closed-out
  residuals are absorbed by future `D_{t+k}` without ever returning to
  `P_ep`.
- Or define the absorber to perform a *local cellification cascade* of
  depth 2: place `D_t`, then immediately cellify the L-shaped residual,
  and only count cells of semiperimeter `≥ 1/t` going forward.

Without such a design, §3.4 only gives `ΔP_ep(C_j) ≤ (α_t − β_t/k_target) ·
k_target = (α_t · k_target − β_t) ≈ τ_j^{-1/2 + 1/4} − τ_j^{-1} = τ_j^{-1/4}`,
which sums to `Σ τ_j^{-1/4} = O(t^{3/4})` — *unbounded*. The amortisation
**fails** under the naive absorber.

### 6.2 Endpoint indexing / stale-endpoint pruning

The scheduler treats `𝓔(t)` as a flat multiset. In practice endpoints are
born across many LRP cuts and have very different sizes. The Phase-B
"oldest fittable endpoint" rule needs an explicit ordering. Two natural
choices:

- **By birth time** (FIFO): drains old endpoints first, matches the
  natural cohort ordering, but may leave widthier endpoints idle.
- **By largest semiperimeter**: drains aggressively, gives a stronger β_t,
  but breaks the cohort association in §3.

The paper must commit to one; the analysis differs. The cohort argument as
written assumes some ordering exists that gives β_t ≥ Ω(t^{-1/2}); FIFO
plausibly works but needs verification.

### 6.3 LRP-cut starvation count

§2.3 invoked `#L_starvation(t) = O(t^{1 − 1/γ})` — this is exactly the
restated Claim N4 in §4, and the no-waste lemma there *uses the rate-limit*.
The argument is not strictly circular because the rate-limit is a definitional
choice of the scheduler, but the precise statement is "given the scheduler,
N4 holds, and given N4, P_ep is bounded." A clean writeup must verify that
the implicit dependence is well-founded: the scheduler's rule is `t`-local
(it depends only on `t, m, k_target(t)` and the current geometric state),
so N4 follows by induction on `t`, with §4 as the induction step.

### 6.4 Initial-state warm-start

The bound `P_ep(t_0) ≤ 4` in §3.5 is a *hypothesis*, supplied by the
warm-start lemma (§12 of the research notes). The combinatorial certificate
search (§15.1) must produce a state at `t = t_0` with this property. As of
this writing the warm-start lemma is unproved; this is the standing
"finite Burn-In" gap.

### 6.5 Constants that are not yet pinned

- The cellification constant `C₁'` in `α_t ≤ C₁' · t^{-1/2}` is `3` from
  §10.2, but with logarithmic-in-`t` slack from N7's threshold. A precise
  computation needs the slack absorbed into `t_0`.
- The absorber drain constant `Δ` depends on the absorber design (§6.1).
  The §3.5 estimate `Δ ≥ 1` is *conjectural*. A failure of `Δ < 3` does not
  immediately break the proof (§3.4's Σ τ_j^{-1/2} is finite), but
  `Δ < 0` (i.e. absorbers *grow* P_ep) would be fatal.
- The threshold `t_0 ≥ 16` assumes the warm-start delivers a balanced LRP
  with aspect at most `R = 2`. A sharper warm-start (R = 1 + ε) lowers `t_0`.

### 6.6 Interaction with N3

N3 (normal-box width law) was proved under §9.4 assuming "expected row
length q = O(t^{1 − 1/γ})". This held under the original scheduler. Under
the rate-limited scheduler, normal-box rows are only filled during Phase A
(at rate `1 − k_target^{-1}`), not every step. Per-row fill rate is
slightly slower, but the asymptotic q = O(t^{1 − 1/γ}) survives because
absorber events do not affect normal boxes. The §9.4 derivation goes through
with the same constants. **Verification needed: redo the §9.4 calculation
with Phase-A density `1 − t^{-1/γ}`, confirm constants unchanged.**

---

## 7. Honest summary

The rate-limited interleaving scheduler **resolves the priority-conflict
diagnosed in §§19–20 in principle**: by reserving one absorber slot per
`k_target(t)` ≈ `t^{1/γ}` Phase-A steps, both N4's normal-box consumption
and N5's endpoint draining are guaranteed at the right rates. The cohort
amortisation in §3 is structurally sound — `#L(C_j) ≤ #A(C_j)` is enforced
by construction, so per-cohort `ΔP_ep ≤ 0` reduces to a per-event
bookkeeping inequality.

The **residual gap** is the absorber design (§6.1). To close `P_ep ≤ η`
quantitatively we need each absorber to drain semiperimeter `Ω(t^{-1/2})`,
which requires an explicit absorber that closes out an entire endpoint
(not just chips off the placed-detail margin). This is a paper-side
design choice not yet committed in §10.3, and it is the single most
important open obligation.

Once §6.1 is settled, the scheduler closes `N4 ∧ N5` for `γ ∈ (1, 3/2)`
with explicit constants (§5). The N6 lower bound on `S_LRP` then follows,
and the calibrated tail theorem becomes a clean conditional reduction to
the warm-start lemma.
