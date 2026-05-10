# Independent algebra audit of the K and η constants

**Date:** 2026-05-10
**Scope:** Independent recomputation of every constant in the
`#L([t_0, t_0+k]) ≤ K · k^{1−1/γ}` derivation (doc 26) and the
`P_ep(t) ≤ η` derivation (doc 28, doc 29) for the standard parameters
`(γ, R, c) = (4/3, 2, 1/2)`. Cross-checked against doc 21 §5 and
doc 22 §3.2 sources for `c_1`, `C_1'`, and `c_*`.

For each constant I quote the formula as printed in the source doc,
re-derive the value from primitive inputs, and flag any discrepancy.

---

## 1. K_A — Phase-A budget

**Source formula (doc 26).** Lemma 2.2 (line 94):

  `A(C_j) ≤ 1 + ⌈c_1^{−1/γ}⌉`.

The cumulative aggregation (doc 26 line 131) lifts this to

  `K_A := 2 + ⌈c_1^{−1/γ}⌉`,

absorbing the `O(1)` cohort-count slack by raising the constant by 1.

**Inputs.** Doc 26 §5 (line 202): `c_1 ≥ 1/(4R) = 1/8` from N3 with
the rate-limited Phase-A density correction. Doc 21 §6.6 confirms the
1/(4R) figure as the conservative N3 lower-bound. (The user's prompt
guesses `c_1 = 0.4`; doc 26 actually pins `c_1 = 1/8` for the
worst-case audit and offers `c_1 = 1/2` only as a sharper alternative.)

**Independent calculation.** With `c_1 = 1/8` and `γ = 4/3`:

  `c_1^{−1/γ} = (1/8)^{−3/4} = 8^{3/4} = 2^{9/4} = 4 · 2^{1/4}
   ≈ 4 · 1.18921 ≈ 4.75683`.

So `⌈c_1^{−1/γ}⌉ = 5`. Lemma 2.2 gives `A(C_j) ≤ 1 + 5 = 6`. The
aggregated constant is `K_A = 2 + 5 = 7`. Doc 26 §5 (line 204) prints
`K_A = 2 + ⌈4.76⌉ = 7`. **Agrees.**

Under the sharper N3 audit `c_1 = 1/2`: `(1/2)^{−3/4} = 2^{3/4}
≈ 1.68179`, hence `⌈1.68⌉ = 2` and `K_A = 4`. Doc 26 line 210 quotes
`K_A ≤ 4`. **Agrees.**

---

## 2. K_B — Phase-B budget

**Source formula (doc 26 line 161).** `K_B := 1` from Lemma 3.1
("each cohort contains at most one Phase-B LRP cut").

**Re-derivation.** The scheduler counter `m` advances strictly inside
Phase A; only the absorber slot can reset it. Each cohort contains
exactly one slot at which `m+1 ≥ kTarget(τ_j)`, because cohort length
equals `kTarget(τ_j)` and `kTarget` is non-decreasing in `t`. So at
most one Phase-B fallback can fire per cohort. The cohort count is
`≤ k^{1−1/γ} + O(1)`; absorbing the +1 into the boundary correction
gives `K_B = 1`. **Agrees.**

---

## 3. K_∂ — boundary correction

**Source formula (doc 26 line 175).** `K_∂ ≤ γ/(γ − 1)`.

**Re-derivation.** For `γ = 4/3`: `γ/(γ−1) = (4/3) / (1/3) = 4`.
**Agrees.**

The provenance is the boundary-cohort overhead: at each window edge
at most one partial cohort contributes `≤ kTarget(t_0) ≤
t_0^{1/γ}` cuts; over both edges this sums to a constant ≤ 2 ·
kTarget(t_0). The factor `γ/(γ−1)` is the absorbed bound after
re-expressing `2 · kTarget(t_0) ≤ (γ/(γ−1)) · k^{1−1/γ}` for `k ≥ t_0`.
The arithmetic `(4/3)/(1/3) = 4` is exact.

---

## 4. K total

**Source formula (doc 26 line 184–186).**

  `K = K_A + K_B + γ/(γ−1) = 2 + ⌈c_1^{−1/γ}⌉ + 1 + γ/(γ−1)
     ≤ 2 + (1 + c_1^{−1/γ}) + γ/(γ−1)`.

Doc 26 §5 table (line 207): `K(4/3, 2, 1/2) ≤ 7 + 1 + 4 = 12` for the
conservative `c_1 = 1/8`; tightens to `K ≤ 9` under the sharper
`c_1 = 1/2`.

**Re-derivation.**

- Conservative (`c_1 = 1/8`): `K_A + K_B + K_∂ = 7 + 1 + 4 = 12`.
  **Agrees** with doc 26 line 207.
- Sharper (`c_1 = 1/2`): `K_A + K_B + K_∂ = 4 + 1 + 4 = 9`.
  **Agrees** with the headline `K ≤ 9`.

**User's claim.** The prompt asks "K total: 2 + (1 + K_A) + K_∂ =
2 + 1 + 1 + 1 + 4 = 9?". Re-parsed against doc 26: the formula
`2 + (1 + c_1^{−1/γ}) + γ/(γ−1)` corresponds to `2 + (1 + 1.68) + 4
≈ 8.68`, ceiling-equivalent to 9 only after replacing the bare
`c_1^{−1/γ}` with `⌈c_1^{−1/γ}⌉ = 2`, i.e., `2 + (1 + 2) + 4 = 9`.
The headline form **drops the ceiling**, giving `2 + (1 + 1.68) + 4
= 8.68`, which is then printed as "≤ 9" by re-applying ⌈·⌉ at the
end. This is honest as an upper bound but the formula at line 38
(`K(γ, R, c) := 2 + (1 + c_1^{−1/γ}) + γ/(γ−1)`, no ceiling) is
*looser* than `K_A + K_B + K_∂` *only when c_1^{−1/γ} is fractional
and ⌈c_1^{−1/γ}⌉ > c_1^{−1/γ}*. Concretely, the line-186 inequality
`K_A + K_B = 2 + ⌈c_1^{−1/γ}⌉ + 1 ≤ 2 + (1 + c_1^{−1/γ})` is
**inverted**: the LHS is `3 + ⌈c_1^{−1/γ}⌉` and the RHS is `3 +
c_1^{−1/γ}`, and `⌈x⌉ ≥ x` so the LHS is **at least** the RHS, not
at most. *This is a sign error in the line-186 chain.*

The error has no effect on the headline `K ≤ 9`, because §5 evaluates
`K_A + K_B + K_∂ = 4 + 1 + 4 = 9` directly from the un-headlined
form. The line-38 / line-186 "compact form" should be read as a
mnemonic, not a rigorous upper bound; the rigorous bound is
`K = (2 + ⌈c_1^{−1/γ}⌉) + 1 + γ/(γ−1)`.

**Verdict.** With `c_1 = 1/2`, `K = 9` exact (no rounding slack).
With `c_1 = 1/8`, `K = 12` exact. The headline `K ≤ 9` is
correct *under the c_1 = 1/2 audit*, which depends on H1 (doc 27).

---

## 5. α_t — per-LRP-cut P_ep injection

**Source formula (doc 28 line 72).** `α_t = C_1' · t^{−1/2}` with
`C_1' = 3 √(Rc)`.

**Re-derivation.** For `R = 2, c = 1/2`: `Rc = 1`, `√(Rc) = 1`,
`C_1' = 3`. **Agrees.**

The factor of 3 comes from the cellification semiperimeter bound
`Σ_{cells} (w + h) ≤ 3 · M_t` with `M_t ≤ √(Rc/t)` (doc 21 §3.1).

---

## 6. β_t — per-absorber P_ep drain

**Source formula (doc 22 line 134, doc 28 line 103).**
`β_t = c_* · t^{−1/2}` with `c_* := (1/2) · √(c/R)`.

**Re-derivation.** For `R = 2, c = 1/2`: `c/R = 1/4`,
`√(c/R) = 1/2`, `c_* = (1/2) · (1/2) = 1/4`. **Agrees.**

(Doc 28 line 267 writes the same value as `√(c/R)/2 = √(1/4)/2 =
(1/2)/2 = 1/4`, equivalent.)

The 1/2 factor comes from the freshness window argument: the
*largest* cell in an N7-balanced cellification inherits the longer
side modulo a factor of 2 (one of two halves).

---

## 7. η worst case (doc 28 §5)

**Source formulas.** From (★) (doc 28 line 239):

  `η ≤ P_ep(t_0) + (C_1' · K · ζ_∞ − c_* · ζ_A)_+ + K_0`.

Naive evaluation (line 275–277):

  `C_1' · K · ζ_∞ = 3 · 9 · 1.645 ≈ 44.4`,
  `c_* · ζ_A ≥ 0.25 · 1.6 = 0.4`,
  `Δ_glob ≈ 44`,
  `η ≤ P_ep(t_0) + 44 + K_0 ≈ 96` with `K_0 = 48`.

After sharpenings (T1: per-cohort instead of cumulative; T2:
`c_* = 1/2`):

  `5 · C_1' · ζ_∞ = 5 · 3 · 1.6449 ≈ 24.674`,
  `c_* · ζ_A ≥ 0.5 · 1.6 = 0.8`,
  `(24.674 − 0.8)_+ ≈ 23.87`,
  `η ≤ 4 + 23.87 + 6 ≈ 33.87`,

rounded up to **`η ≤ 34`**.

**Re-derivation.** I computed independently:

- `ζ_∞ = π²/6 = 1.64493...` (correct, line 269).
- `C_1' · K · ζ_∞ = 3 · 9 · 1.64493 = 44.4132` (line 275 says ≈ 44.4).
  **Agrees.**
- `(T1) 5 · 3 · 1.64493 = 24.674` (line 286 says ≈ 24.7). **Agrees.**
- `(T2) 0.5 · 1.6 = 0.8`. **Agrees.**
- Total `4 + (24.674 − 0.8) + 6 = 33.874 ≈ 34`. **Agrees.**

**Caveat.** The (T1) substitution `5` for `K = 9` claims that the
*per-cohort* count `#L_j ≤ 1 + ⌈c_1^{−1/γ}⌉ + 1 ≤ 5` (Lemma 2.2 + 3.1)
is the right upstream constant. With `c_1 = 1/2`, the per-cohort
budget is `1 + 2 + 1 = 4`, not 5. With `c_1 = 1/8`, it is `1 + 5 + 1 =
7`, not 5. The `5` in the doc 28 (T1) sharpening matches neither
audit. If we use `c_1 = 1/2` consistently, (T1) should read
`4 · C_1' · ζ_∞ ≈ 19.74`, giving `η ≤ 4 + (19.74 − 0.8) + 6 ≈ 28.94`,
i.e. `η ≤ 29`. If we use `c_1 = 1/8`, (T1) gives `7 · C_1' · ζ_∞ ≈
34.54`, i.e. `η ≤ 4 + (34.54 − 0.8) + 6 ≈ 43.74`, i.e. `η ≤ 44`.
**The `5` is intermediate and not consistent with either c_1 audit.**

**Verdict.** The headline `η ≤ 34` is *approximately* correct as an
intermediate value but the per-cohort upstream constant is mis-quoted
as 5; under the consistent c_1 = 1/2 audit, η ≤ 29 (tighter), and
under c_1 = 1/8 it is η ≤ 44 (looser). The "34" is a midpoint that
neither audit independently produces.

---

## 8. η under O1 (doc 29 §2)

**Source formula (doc 28 line 304–308, doc 29 §2).**

  `(C_1' − c_*) · (1 + ζ_∞) ≈ 2.75 · 2.65 ≈ 7.3`,

"rounded up to 6 after the absorber surplus is incorporated" — i.e.,

  `η ≤ P_ep(t_0) + 6  =  0 + 6  =  6` under O1.

**Re-derivation.** `(C_1' − c_*) · (1 + ζ_∞)` is *not* the standard
form of the global bound (★). The standard form is

  `η ≤ P_ep(t_0) + (C_1' · K_eff · ζ_∞ − c_* · ζ_A)_+ + K_0`

with `K_eff` being the per-cohort count. The line-308 expression
`(C_1' − c_*) · (1 + ζ_∞) = 2.75 · 2.65 = 7.286` corresponds to
treating *each* cohort as contributing `(α_τ − β_τ) = (C_1' − c_*) ·
τ^{−1/2}` exactly once, and summing:

  `Σ_j (C_1' − c_*) · T_j^{−1/2} ≤ (C_1' − c_*) · ζ_∞ ≈ 4.524`,

then adding the leading t_0 term `(C_1' − c_*) · t_0^{−1/2}` ≈
`2.75 · 0.25 = 0.6875` and the boundary `K_0 ≤ 1` to get ≈ 6. The
"`(1 + ζ_∞)`" factor in the doc-line-308 mnemonic is unclear — it
should read either `1 + ζ_∞` as "first cohort + asymptotic tail" or
just `ζ_∞`. **The arithmetic 2.75 · 2.65 = 7.286 ≈ 7.3 is correct,
but its interpretation as "rounded up to 6" is not arithmetically
sound: rounding 7.3 *up* gives 8, and rounding *down* gives 7.**

The genuine path to η ≤ 6 under O1 is:

- Each cohort contributes ≤ `(C_1' · #L_j − c_*) · τ_j^{−1/2}` per (♥).
- For cohorts where `#L_j = 1` and `#A_j = 1`, the contribution is
  `(3 − 0.25) · τ_j^{−1/2} = 2.75 · τ_j^{−1/2}`.
- Summed: `2.75 · Σ_j τ_j^{−1/2} = 2.75 · ζ_∞ ≈ 2.75 · 1.645 = 4.524`.
- Add the leading-cohort term `2.75 · t_0^{−1/2} ≈ 2.75 · 16^{−1/2}
  = 2.75/4 ≈ 0.6875`.
- Add fallback K_0 (doc 29 §3 says ≤ small constant): conservatively
  ≤ 1.
- Total ≈ `4.524 + 0.6875 + 1 ≈ 6.21`, rounded to **`η ≤ 7`**, not 6.

So the `η ≤ 6` claim is tight — it is achievable only by an
optimistic rounding (e.g. ignoring the boundary term, or assuming
`#L_j = 0` for some cohorts so the average contribution is below
2.75 · ζ_∞). **The claim "η ≤ 6" has approximately ±1 slack against
my independent recomputation; the rigorous worst-case is η ≤ 7.**

Doc 29 §2 line 58 prints `η ≤ P_ep(t_0) + 6 = 0 + 6 = 6`. This is
quoting doc 28 line 306 verbatim. The rigorous value with the
explicit per-cohort sum and a +1 boundary is closer to η ≤ 7.

---

## 9. Summary

| # | Quantity | Doc value | My re-derivation | Discrepancy |
|---|----------|-----------|------------------|-------------|
| 1 | K_A (c_1 = 1/8) | 7 | 7 | none |
| 1 | K_A (c_1 = 1/2) | 4 | 4 | none |
| 2 | K_B | 1 | 1 | none |
| 3 | K_∂ = γ/(γ−1) | 4 | 4 | none |
| 4 | K (c_1 = 1/8) | 12 | 12 | none |
| 4 | K (c_1 = 1/2) | 9 | 9 | none, **but** the line-186 inequality `2 + ⌈c_1^{−1/γ}⌉ + 1 ≤ 2 + (1 + c_1^{−1/γ})` is *backwards* (sign error in mnemonic; harmless to headline). |
| 5 | α_t coefficient C_1' | 3 | 3 | none |
| 6 | β_t coefficient c_* | 1/4 | 1/4 | none |
| 7 | η worst case | ≤ 34 | ≤ 29 (c_1=1/2) or ≤ 44 (c_1=1/8) | (T1) substitutes `5` for the per-cohort count, which matches neither c_1 audit; the consistent answers are 29 or 44, not 34 |
| 8 | η under O1 | ≤ 6 | ≈ 6.2, rounded to 7 | "rounded up to 6" wording is arithmetically inverted (7.3 rounds up to 8 or down to 7); rigorous value is η ≤ 7 |

### Are all constants correct?

**Constants 1–6 are exact.** No off-by-1, sign, or cancellation
errors in K_A, K_B, K_∂, the headline K, C_1', or c_*. The N3 audit
chain (Lemma 2.2 → K_A → K) is internally consistent, and the
arithmetic `(1/2)·√(c/R) = 1/4` and `3·√(Rc) = 3` checks out.

**Constants 7–8 are loose by O(1).** The worst-case `η ≤ 34` mixes
sharpenings (T1) and (T2) with an intermediate per-cohort constant
`5` that does not match either the conservative or the sharper
c_1 audit; it is presented as a numerical illustration, not as a
rigorous chain. The under-O1 `η ≤ 6` is one unit below my
independent recomputation `η ≤ 7`. Both look like favourable
roundings rather than rigorous tight bounds.

### Corrected K and η

- **K (rigorous):**
  - With c_1 = 1/8 (worst-case N3, conservative): `K = 12`.
  - With c_1 = 1/2 (sharper N3, doc 27 H1): `K = 9`.
- **η worst case (rigorous):**
  - With c_1 = 1/2: `η ≤ 29`.
  - With c_1 = 1/8: `η ≤ 44`.
- **η under O1 (rigorous, P_ep(t_0) = 0):**
  - With c_1 = 1/2: `η ≤ 7` (one above doc claim of 6).

### Bottom line

The framework's headline constants are *not wrong*, but they are
quoted as upper bounds derived through favourable rounding rather
than tight inequalities. The arithmetic from primitive inputs to K
is exact (no off-by-1 anywhere); the η chain has a "5 vs 4 vs 7"
inconsistency in the (T1) sharpening and a "round 7.3 to 6"
inconsistency in the under-O1 reading. Neither inconsistency
threatens the qualitative claim `η < ∞`; both should be cleaned up
in the camera-ready by either (a) committing to one c_1 audit and
recomputing 7–8 consistently, or (b) explicitly tagging the
intermediate values as illustrative rather than rigorous.

The framework's claim `K ≤ 9` (under H1) is correct; the framework's
claim `η ≤ 10` (under O1) requires the η ≤ 6 component, which is
loose by 1 and would be more honest as `η ≤ 11`.
