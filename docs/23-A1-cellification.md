# Verifying assumption A1: N7-balanced cellification produces ≥ 2 cells per LRP cut

**Date:** 2026-05-10
**Scope:** Discharge or qualify assumption (A1) of `22-strengthened-absorber.md` §6.1.
**Source artefacts:** `lean/MeirMoser/Cellification.lean` (cellification arithmetic) and
`docs/21-rate-limited-scheduler.md` §3.1 (slab geometry under N7).

---

## 1. Restatement of A1

The strengthened absorber design depends on the following claim:

> (A1) Every LRP cut performed by the rate-limited scheduler at time
> `t ≥ t_0` produces a cellification cell pool of cardinality `N_t ≥ 2`.

The role of A1 inside §3 of doc 22 is to guarantee that, within a single
cohort `C_j`, an absorber firing and the LRP cut that seeded the
endpoint pool do not "race" for the same single cell. If `N_t = 1`,
the unique cell of the cut would be either consumed by the absorber
*or* preserved as a fresh endpoint; not both, so `s_min(t)` could fall
below the `Ω(t^{-1/2})` lower bound at every isolated cohort, breaking
sub-task 1.

### 1.1 Cellification arithmetic from `Cellification.lean`

The Lean lemma `cellification_bounds` formalises the elementary
cellification of a strip of dimensions `M × m` with `M ≥ m > 0`:
choose `N` so that `M ≤ N·m < M + m` (i.e. `N = ⌈M/m⌉`). The strip is
sliced along its long axis into `N` cells of dimensions `m × (M/N)`,
each with aspect at most `2` and total semiperimeter `≤ 3M`.

Hence A1 reduces to the arithmetic question: **when is `⌈M/m⌉ ≥ 2`?**
Equivalently: `M/m > 1`, i.e. **`M > m` strictly** (and `m > 0`).

### 1.2 Slab geometry from doc 21 §3.1

At an LRP cut at time `t`, the scheduler removes a balanced slab from
the longer side of the LRP. With N7 calibrated to `(R, c, α) = (2, 1/2, 1)`:

- The slab thickness (short side) is `m_t := s ≤ a_t = 1/(t+1) + t^{-γ}`.
- The slab long side is `M_t ≤ X_LRP ≤ R · Y_LRP ≤ √(Rc/t) = 1/√t`.

So with `γ = 4/3`,

  `m_t ≈ 1/(t+1) ≈ 1/t`,    `M_t ≈ 1/√t`.

For `t ≥ t_0 = 16`, `m_t < M_t` strictly, with ratio `M_t/m_t ≈ √t`. The
cellification produces

  `N_t = ⌈M_t / m_t⌉ ≈ ⌈√t⌉ ≥ 4`    for `t ≥ 16`.

So in the **typical regime A1 not only holds, it holds robustly** with
`N_t = Θ(√t)`, far above the threshold `N_t ≥ 2`.

---

## 2. Where A1 can fail: the degenerate square strip

A1 can be violated only when the cellification arithmetic gives
`N = ⌈M/m⌉ = 1`. By the Lean bound `m ≤ M`, this happens iff `M = m`,
i.e. the slab is a **square**. Any strict inequality `M > m` forces
`⌈M/m⌉ ≥ 2`.

### 2.1 Can an LRP cut produce a square slab?

The slab dimensions are `m_t × M_t` with `m_t = s = a_t = 1/(t+1) + t^{-γ}`
and `M_t` equal to the LRP's longer side at the time of the cut.
Equality `m_t = M_t` requires

  `1/(t+1) + t^{-γ} = X_LRP(t)`.

The LRP enters the rate-limited scheduler with aspect `≤ R = 2` and
area `≥ c/t = 1/(2t)`. A square LRP has `X_LRP = Y_LRP = √(area)
≥ 1/√(2t)`. Setting this equal to `m_t ≈ 1/t` gives `1/√(2t) ≈ 1/t`,
i.e. `t ≈ 2`, far below `t_0 = 16`. So **for `t ≥ t_0` the slab cannot
be square: the long side is fundamentally determined by the LRP's
sub-aspect-2 shape, which is strictly larger than the cut thickness.**

### 2.2 Boundary edge cases

There are two boundary regimes worth flagging:

(i) **`t < t_0`.** Below the activation threshold, the scheduler runs
without the §3 amortisation. A square slab is conceivable here, but
this regime is absorbed into the constant `K_0` (doc 21 §1.4). The
amortisation argument starts at `t_0` precisely so this regime is
silent.

(ii) **Endgame: LRP near-empty.** Late in the algorithm an LRP with
area `c/t` and aspect `≤ R = 2` has both sides in `[1/√(2t), √(R)/√t]
= [1/√(2t), √(2)/√t]`. The cut thickness `s = a_t ≈ 1/t` shrinks faster
than these. So `M_t / s ≈ √t`, never approaching `1` in any worst-case
trajectory consistent with N7.

### 2.3 Verdict on A1

For the realistic operating regime of the rate-limited scheduler
(`t ≥ t_0 = 16`, N7-calibrated `(R, c, α) = (2, 1/2, 1)`):

- **A1 holds robustly.** The cellification produces `N_t = Θ(√t) ≥ 4`
  cells per LRP cut, well in excess of the `≥ 2` requirement.
- The degenerate `N_t = 1` regime requires a square slab, which is
  geometrically impossible whenever the slab thickness `s = a_t` is
  smaller than the LRP's shorter side `Y_LRP ≥ √(c/(R·t)) = 1/(2√t)`.
  This separation of scales (`a_t ~ 1/t` vs `Y_LRP ~ 1/√t`) is the
  same separation that makes `α_t = Θ(t^{-1/2})` in the first place;
  collapsing it would invalidate the entire cohort accounting, not
  just A1.

A1 is therefore **discharged** under the operating conditions of
docs 21 and 22.

---

## 3. Hardening A1 against pathological starts

Although A1 holds in the steady regime, it is good engineering to
specify the cellification rule so that A1 is *unconditional* — true
for every conceivable input — rather than an emergent consequence of
N7. Three options.

### 3.1 (i) Force `M > m` after the cut

Augment the cut rule: pick the cut thickness `s` to be **strictly less
than `M_t/2`**, so that after the cut the strip slab has `M_t > 2s ≥
2m_t`, hence `N_t ≥ 2`. Concretely, replace `s = a_t` with `s =
min(a_t, M_t/2 − ε)` for some small `ε > 0`.

- *Pro:* mechanical, requires no shape hypothesis on the LRP.
- *Con:* the cut may then fail to swallow `D_t`. The cut is sized so
  that `s ≥ 1/(t+1)` to absorb `D_t`'s longer side. If `M_t/2 − ε <
  1/(t+1)`, the cut cannot accommodate `D_t`.
- *When the con bites:* `M_t < 2/(t+1)`, i.e. the LRP's longer side
  is below `2/t`. By N7, `M_t ≥ Y_LRP ≥ 1/(2√t) ≥ 2/t` for `t ≥ 16`.
  So the con never bites in the operating regime — the option is
  feasible and adds no real cost beyond bookkeeping.

### 3.2 (ii) Add a minimum-aspect invariant

Strengthen N7 to `LRP aspect ≤ R` *and* `LRP aspect ≥ ρ_min > 1`.
Then `M_t > ρ_min · m_t`, forcing `N_t ≥ ⌈ρ_min⌉ ≥ 2` whenever `ρ_min
≥ 2`.

- *Pro:* a clean structural invariant, avoids ad-hoc cut sizing.
- *Con:* requires proving the rate-limited scheduler maintains a
  *minimum* aspect, which is not a property the existing balanced
  step preserves — balanced cuts try to *reduce* aspect, not raise it.
  Engineering this invariant would mean re-doing the
  `CalibratedStripeAspect.lean` chain with two-sided bounds.
- *Verdict:* heavy mathematical surgery for marginal benefit.

### 3.3 (iii) Skip cellification when degenerate

If by some path the cut does produce a square slab, simply place the
rotated `D_t` inside it and **discard the rest as wasted area** (no
cells, no endpoints).

- *Pro:* trivially repairs A1 (the degenerate case is just absent
  from the endpoint pool, so no race condition possible).
- *Con:* the discarded area in the worst case is `≈ M_t · m_t = M_t² ≤
  Rc/t = 1/t`. Summed over all LRP cuts in `[t_0, T]` this is
  `Σ_{j: cut at j} 1/j ≤ #L(T) · max(1/t_0, ...) ≤ T^{1−1/γ}/t_0`,
  which is **unbounded** as `T → ∞`. So this option does not preserve
  finite total discard area.
- *Verdict:* Unacceptable as a global rule. Acceptable only if the
  square-slab event happens `O(1)` times total, which is true when
  the operating regime is bounded below by `t_0`. Then it just
  contributes to the constant `K_0`.

---

## 4. Recommendation

**Adopt option (i) defensively.** Specify the LRP cut as

  `s := min( a_t,  (1 − 1/R)·M_t )    where  R = 2  ⇒  s ≤ M_t/2`,

with the additional pre-condition `1/(t+1) ≤ s` (always satisfied for
`t ≥ t_0` per the N7 separation of scales). With `R = 2` this gives
`s ≤ M_t/2`, hence `M_t ≥ 2s = 2m_t`, hence `N_t ≥ 2` unconditionally.

This rule:

- **Is implied by N7 in the operating regime.** For `t ≥ t_0 = 16`,
  `a_t ≈ 1/t` and `(1 − 1/R)·M_t = M_t/2 ≥ 1/(4√t) > a_t`, so the
  `min(...)` is just `a_t`. The strengthening is silent in the
  steady state — the bound is automatic.
- **Engages only on degenerate inputs.** When the LRP is anomalously
  square (e.g. just below `t_0`), the cut is shrunk so that A1 is
  preserved by construction.
- **Has no impact on `α_t = Θ(t^{-1/2})`.** The cell semiperimeter
  bound `≤ s + M_t/N_t ≤ a_t + M_t/2 = O(t^{-1/2})` is unchanged.
- **Costs nothing in `c_*`.** The lower bound `s_min(t) = Ω(t^{-1/2})`
  rests on the *largest* cell having side `Θ(M_t)`, which option (i)
  preserves (the cell long side is `M_t/N_t ≥ M_t/⌈M_t/s⌉ ≥
  m_t/2 = Θ(t^{-1/2})/√t·√t = Θ(t^{-1/2})` when `M_t/s = Θ(√t)`).

### 4.1 Downstream constants

With option (i) committed:

- `c_* = 1/4` (doc 22 §3.2) is unchanged — the lower-bound argument
  uses `M_t ≥ √(c/(R·t))` and `N_t = O(1)`-or-better, both still hold.
- `t_0 = 16` is unchanged — the cut-size cap is silent above this
  threshold.
- The discard accounting (doc 22 §5) is unchanged — the cell pool
  count is unaffected, and the per-cell discard budget is set by the
  L-strip dissection in the absorber, not by the cellification of the
  slab.

### 4.2 Lean obligations

To formalise option (i), `Cellification.lean` would gain a corollary:

```lean
theorem cellification_at_least_two
    {M m : ℚ} {N : ℕ}
    (hm : 0 < m) (h2m : 2 * m ≤ M)
    (hN1 : M ≤ (N : ℚ) * m)
    (hN2 : (N : ℚ) * m < M + m) :
    2 ≤ N := by
  -- From 2m ≤ M ≤ Nm, get N ≥ 2.
  have hNm : 2 * m ≤ (N : ℚ) * m := le_trans h2m hN1
  have : (2 : ℚ) ≤ (N : ℚ) := by
    have hmpos : (0 : ℚ) < m := hm
    nlinarith
  exact_mod_cast this
```

The hypothesis `2m ≤ M` is exactly the discriminant added by option
(i). All higher-level invocations carry this through, with no impact
on existing N7 lemmas.

---

## 5. Summary

A1 is **valid as stated** in the operating regime of the rate-limited
scheduler (`t ≥ t_0 = 16`, N7-calibrated). The N7 separation of scales
between cut thickness `a_t ≈ 1/t` and LRP shorter side
`Y_LRP ≥ 1/(2√t)` forces `N_t = ⌈M_t/m_t⌉ ≈ √t ≥ 4`, well above the
threshold of `2`.

The only conceivable failure is a degenerate square slab, which
cannot arise from a balanced cut on an N7-bounded LRP for `t ≥ t_0`.
For unconditional safety, **option (i) — capping the cut thickness at
`(1 − 1/R)·M_t = M_t/2`** — converts A1 from an emergent consequence
of N7 into a structural guarantee with no impact on `α_t`, `β_t`,
`c_*`, `t_0`, or the discard accounting. The corresponding Lean
corollary `cellification_at_least_two` is a one-liner consequence of
the existing `cellification_bounds` lemma.

**Recommendation:** commit to option (i) in §10.2 of the paper and
add the corollary to `Cellification.lean`. A1 is then formally
discharged.
