# Paper-side mathematical audit of the Calibrated Slack-Pack framework

**Date:** 2026-05-10
**Purpose:** Self-audit of the calibrated framework for *Concrete Mathematics* Problem 2.37 before committing 10+ weeks of Lean formalization to a possibly-broken theorem.
**Author posture:** academic rebuttal / referee report on our own research notes.
**Source under audit:** `meir_moser_concrete_math_2_37_research_notes.md` (§§7–11) and the simulation evidence in `temp/sim_balanced.py`, `temp/sim_calibrated.py`.

---

## 1. Why this audit is necessary

The Lean formalization (Route A.5) reduced the proof to a *single* residual axiom
`balanced_c_share_positive_axiom`, which encodes a cumulative LRP-area-share bound.
Numerical simulations of the *simplified* balanced step show this cumulative
bound diverges:

- Synthetic strong cert (c = 40, R = 2, t₀ = 100, area₀ = 0.4):
  c-share flips negative at k = 74 (sim_balanced) and k = 50 (sim_calibrated).
- N = 100-like cert: c-share flips negative at k = 1.

This is the kind of single-step error that destroyed Paulhus 1998 (later corrected
by Joós 2018). Before paying the formalization cost, we must answer whether the
*full* calibrated framework — normal-box-first scheduler + cellification + endpoint
potential — actually closes the cumulative argument, or whether the divergence we
observe in the simplified simulator persists in the full machinery.

---

## 2. Numeric / quantitative claims, enumerated

I list every numeric or asymptotic claim that the proof requires. Each item is
classified later as **Solid**, **Needs work**, or **Suspect**.

### Claim N1. Calibrated active width
For γ ∈ (1, 3/2) and time t ≥ 1,
  a_t = 1/(t+1) + t^{-γ}.
This is a *definition* and is unambiguous.

### Claim N2. Total tail area (telescoping)
S_com(t) = Σ_{n≥t} 1/(n(n+1)) = 1/t exactly.
Solid; this is high-school telescoping.

### Claim N3. Normal-box width law (§9.4)
For a normal box "born" at time k via the calibrated scheduler:
  c₁ k^{-γ} ≤ w(B_k) ≤ c₂ k^{-γ},
  area(B_k) ≍ k^{-(γ+1)}.

### Claim N4. Normal-box area sum (§9.5)
At an LRP-critical time t (i.e., no normal box wide enough for D_t):
  S_norm(t) = Σ_{k unused} area(B_k) ≤ (1/γ + δ)·(1/t).

### Claim N5. Endpoint potential bound (§9.3)
Endpoint priority + two-backtrack ⇒ at every LRP-critical time
  P_ep(t) := Σ_E (w(E) + h(E)) ≤ η,
which gives
  S_ep(t) ≤ (C/t)·P_ep(t) ≤ Cη/t.

### Claim N6. LRP lower bound (§9.6)
Combining N4 and N5:
  S_LRP(t) = 1/t − S_norm(t) − S_ep(t) ≥ (1 − 1/γ − 2δ)/t.
For γ = 4/3 the leading coefficient is 1/4.

### Claim N7. Balanced LRP aspect control (§10.1)
If LRP has X ≥ Y, area ≥ c/t, X/Y ≤ R, and we cut from the longer side a stripe
of thickness s ≤ α/t, then the new aspect is still ≤ R provided
  t ≥ α²R / (c·(1 − 1/R)²).

### Claim N8. Cellification lemma (§10.2)
A strip of size M × m (M ≥ m) split into N = ⌈M/m⌉ cells m × M/N has aspect ≤ 2 and
total semiperimeter ≤ 3M.
Solid; this is direct arithmetic.

### Claim N9. Absorber cascade (§11)
Cellification yields A_{j+1} ≤ C·A_j·P_j, P_{j+1} ≤ C·P_j; choosing P₀ small and
finite cascade depth r gives leftover ≤ ε.

### Claim N10. Conditional main theorem (§14)
Calibrated tail theorem + warm-start sequence (N_j → ∞, ε_j → 0) ⇒ exact
unit-square packing via Martin compactness. (The Lean closure goes one step further
and tries to *avoid* Martin via a direct exact-square claim from the calibrated
framework.)

---

## 3. Per-claim audit

### 3.1 Claim N3 (calibrated normal-box width law) — Needs work

The argument in §9.4: in a calibrated active box of width a_t = 1/(t+1) + t^{-γ},
placing D_j produces a leftover normal box of width

  a_t − 1/(j+1) = t^{-γ} + (1/(t+1) − 1/(j+1)).

The note then claims:

> "If the row length is q = j − t, then 1/(t+1) − 1/(j+1) = O(q/t²). Inside
> normal boxes, expected row lengths are q = O(t^{1−1/γ}), so q/t² = O(t^{−1−1/γ})
> = o(t^{−γ}) for 1 < γ < 3/2. Therefore w(B_j) ≍ j^{−γ}."

There are *two* unjustified steps here:

**(a) Where does q = O(t^{1−1/γ}) come from?**
A calibrated active box at time t has width ≈ 1/t (since γ > 1 means 1/(t+1)
dominates t^{-γ}). Any rectangle D_j (j ≥ t) placed in it occupies width
1/(j+1) ≈ 1/j. The number of consecutive items placeable in one row is
roughly (active width) / (item width) = (1/t) / (1/j) = j/t — but the row
must fit *across* the box, so total width is 1/t, hence we must have

  Σ_{i in row} 1/(i+1) ≤ a_t.

For consecutive indices t, t+1, …, t+q−1 this is ≈ ln((t+q)/t) ≤ a_t ≈ 1/t,
which forces q ≤ t·a_t · (1 + o(1)) ≍ 1, i.e., **q = O(1)**, not O(t^{1−1/γ}).

I don't see how the t^{1−1/γ} estimate is derived in §9.4. One charitable
reading: "row length" might mean the length of a row in an *older* normal box
B_k (born at index k) when its row is being filled by items at time t. There,
row width is k^{-γ}, item width is 1/t, so q ≈ k^{-γ}·t, and at LRP-critical
time we have k ≈ t^{1/γ}, giving q ≈ t·t^{-1} = O(1) again — *not* the claimed
t^{1−1/γ}. For γ = 4/3 the claim says q ~ t^{1/4}; for γ = 5/4 it says q ~
t^{1/5}; these are not the row counts arising naturally.

**(b) Is the claim w(B_j) ≍ j^{-γ} for *every* normal box, or only on average?**
The notes blur this. A worst-case lower bound c₁ j^{-γ} is essential for
Claim N4 to give an O(1/t) sum (otherwise some boxes might be much narrower
and less plentiful than estimated). The notes give only an *upper*-bound
estimate via the "small correction" t^{-γ} + O(t^{-1-1/γ}) = (1+o(1))·t^{-γ}.
The lower bound c₁ k^{-γ} is asserted but not derived.

**Verdict:** Plausible and likely true under the natural scheduler, but the
proof in §9.4 is informal. To close Lean-rigorously, one needs a precise
inductive definition of "normal box born at k" and a per-box width invariant,
not the averaged O(q/t²) hand-wave. **Roughly 1–2 pages of careful real
work to repair.**

### 3.2 Claim N4 (normal-box area sum) — Needs work, with one suspect step

Given Claim N3, §9.5 estimates

  S_norm(t) ≤ Σ_{k ≥ c·t^{1/γ}} C·k^{-(γ+1)}.

The integral comparison

  Σ_{k ≥ K} k^{-(γ+1)} ≤ (1/γ)·K^{-γ} + O(K^{-γ-1})

is standard (∫_K^∞ x^{-γ-1} dx = K^{-γ}/γ). With K ≍ t^{1/γ}, K^{-γ} ≍ 1/t, so
the bound is (1/γ + o(1))·(1/t). **This step is solid given Claim N3.**

The suspect part: the *birth-index lower bound* "k ≳ t^{1/γ} for all unused
normal boxes." This depends on:

(i) A precise scheduler invariant that the only normal boxes still present at
time t are those born at indices k where w(B_k) < min item width currently
needed (which for D_t is 1/t for x-cut, 1/(t+1) for y-cut). With Claim N3's
w(B_k) ≍ k^{-γ}, this gives k^{-γ} < 1/t, i.e., k > t^{1/γ}.

But the cumulative argument needs the *opposite* direction: an *upper bound*
on which normal boxes can possibly still be alive. Why isn't a normal box
born at time k = 5, with width ≍ 5^{-γ} ≈ 0.07 still alive at t = 100? It
would have stored area, and was passed over because it didn't fit some
intermediate detail. Closing this requires:

(ii) A *consumption invariant*: every normal box B_k of width ≍ k^{-γ} *must*
have been used between times k and k^γ. This requires a "no-waste" lemma
about the scheduler, which is not stated in the notes. The endpoint-priority
+ normal-box-priority rules don't automatically guarantee this; one might pass
over B_k repeatedly because endpoints kept fitting.

**Verdict:** The summation algebra is fine; the structural claim "all surviving
normal boxes have k ≳ t^{1/γ}" is **not rigorously argued** in §9.5. This is
the kind of gap that, if false, can falsify the entire framework.

### 3.3 Claim N5 (endpoint potential) — Suspect

This is the most algebraically delicate and the place I am most worried about.

The §9.3 derivation: at LRP-critical time t, every endpoint E has w(E) ≤ C/t
(by endpoint priority — otherwise priority would have placed D_t in E, not in
the LRP). So area(E) ≤ (C/t)·h(E) ≤ (C/t)·(w(E) + h(E)). Summing:

  S_ep(t) ≤ (C/t)·P_ep(t).

The arithmetic per endpoint is solid. The *suspect* claim is

**(c) P_ep(t) ≤ η globally, for a fixed η.**

§10.3 (shelf residual bookkeeping) only proves a *per-box* and *per-cascade-level*
inequality of the form

  P_res(B) ≤ C·(W + H), and P(𝓑') ≤ C·P(𝓑).

This gives a bound P_ep(t) ≤ C^r · P₀ for r cascade levels. With r = O(log t)
cascade levels through the lifetime, **C^r is unbounded** — not constant in t.
The notes acknowledge in §11 ("corrected absorber cascade") that one chooses
r finite and starts at large index so that C^r·P₀ is small, but this is in
the ε-version: for *one* terminal box, you can absorb into ε. But for the
*lifetime* invariant P_ep(t) ≤ η, the cascade keeps re-producing endpoints,
and the multiplicative constant C ≥ some constant (cellification doubles
semiperimeter bookkeeping) means

  P_ep at time t ≈ C^{number of cascades so far} · P_initial.

If the scheduler does a cascade per LRP cut, and there are Θ(t) LRP cuts
in [1, t], then P_ep grows polynomially in t, blowing up the η bound.

The escape hatch is "amortized" cascading: only do a cascade when the
endpoint family has accumulated enough perimeter. But §9–§11 do **not**
formalize this amortization. The §10.3 bookkeeping is purely local:
"one box in, one residual out, perimeter at most tripled." Iterated this
crashes.

**This is the crucial gap that the simplified-scheduler simulation surfaces.**
The simulation shows that without cellification + amortized cascading, the
cumulative perimeter (and its cousin, the cumulative LRP-area-decay) grow
linearly in the number of steps. The notes' claim that the full scheduler
fixes this **does not yet contain a quantitative argument** showing how the
amortization tames the growth.

**Verdict:** Suspect. Without an explicit potential argument that accounts for
the cumulative effect of cascades over Θ(t) LRP cuts, the η-bound is at best
heuristic. **This is structurally the same kind of claim as Paulhus 1998's
faulty endpoint lemma.** Closing it would require either:

- An amortized analysis: charge each cascade against the LRP area saved;
- Or a stronger structural lemma showing that endpoint perimeter is *not* a
  monotone-increasing quantity but a Lyapunov function with a sink.

Neither appears in the notes.

### 3.4 Claim N6 (LRP lower bound) — Solid *given* N4 and N5

Conditional on N4 and N5, the algebra

  S_LRP = 1/t − S_norm − S_ep ≥ (1 − 1/γ − 2δ)/t

is just subtraction. For γ = 4/3 the coefficient is 1/4 − 2δ > 0 for δ small.
**Solid.** The defect is the conditioning on N4/N5, which we just identified
as needing work or being suspect.

### 3.5 Claim N7 (balanced LRP aspect) — Solid (and Lean-verified)

The §10.1 proof is a clean two-line algebra: from XY ≥ c/t and X ≤ RY one
derives Y ≥ √(c/(Rt)), hence s ≤ α/t ≤ (1−1/R)Y for t ≥ α²R/(c(1−1/R)²).
**Solid.** This lemma is one of the few pieces fully discharged in Lean (see
`CalibratedStripeAspect.lean`).

### 3.6 Claim N8 (cellification lemma) — Solid

Direct arithmetic; no analytic content. **Solid.**

### 3.7 Claim N9 (absorber cascade) — Needs work, but ε-version is OK

The corrected ε-version in §11 is honest: pick finite cascade depth r, start
at sufficiently large index. This works *for a single ε-packing* but does
**not** give a uniform invariant P_ep ≤ η across all t — it gives a
per-ε statement only. So as a tool for the asymptotic LRP lower bound it is
*not* sufficient; the cascade controls leftover *area* to be ≤ ε but does
not control endpoint *perimeter* uniformly in t.

**Verdict:** §11 is internally consistent for an ε-packing target but
**does not directly give the uniform η-bound** that §9.3/Claim N5 needs.

### 3.8 Claim N10 (conditional main theorem) — Solid as stated

§14 is honest: assume the calibrated tail theorem + warm-start sequence ⇒ exact
unit-square packing. The application of Martin compactness is a known step
(stated in §1.5; needs Lean formalization or external citation).

The Lean closure tries to *avoid* Martin compactness by sharpening the calibrated
framework so that for *some* fixed choice (1+ε)-square packings yield directly
the unit packing. This sharpening hinges on Claim N6 being genuine and
*uniform* in t — i.e., back to N4/N5.

---

## 4. The cumulative argument: precise diagnosis

### 4.1 What the simplified simulator shows

The simulator `sim_balanced.py` runs the simplified balanced step:
- Place rotated D_t at the LRP corner;
- Cut a slice of width 1/(t+1) (x-cut) or 1/t (y-cut) from the longer side.

Tracking c_share(k) = c₀ − Σ_{j<k} maxSide_j · (1 + 1/t_j):

| Cert | k where c_share ≤ 0 | k where fit fails |
|------|--------------------:|------------------:|
| Synthetic strong (c=40, R=2, t=100, area=0.4) | 74 | 265 |
| WarmStartN100-like (c=0.077, R=5.36, t=101, area≈7.6e-4) | 2 | 6 |

Crucially, the cum/log(k) ratio grows: at k=10 it's 3.3, at k=100 it's 10.6.
This is not even logarithmic decay; it's *polynomial growth*. So as a uniform
invariant, c_share(k) ≥ 0 for all k is **false** for the simplified balanced step.

### 4.2 Why the full calibrated framework is *supposed* to fix this

The notes' implicit theory of change:

(i) Most steps are *not* LRP cuts. They are normal-box placements or endpoint
    placements. Only Θ(t^{1−1/γ}) of the first t steps are LRP-critical
    (because every LRP cut creates Θ(t^{1−1/γ}) normal boxes that absorb the
    next many items).

(ii) When an LRP cut *does* happen, the cut depth s ≤ a_t ≈ 1/t.

(iii) Therefore the LRP loses cumulative thickness ≤ Σ_{LRP cuts} 1/t, which
      summed over Θ(t^{1−1/γ}) cuts among the first t indices is
      O(∫₁^t s^{-1/γ} ds) = O(t^{1−1/γ}) — a *sublinear* quantity. With LRP
      side ≍ √(c/t), losing thickness O(t^{1−1/γ}) is fine because it's much
      less than √(c/t) for γ > 1.

This is the heuristic mechanism. **But the rigorous version of (i) is exactly
Claim N4, which we identified as needing the structural "consumption
invariant" that the notes don't prove.** The simulator falsifies this for a
scheduler that *only* does LRP cuts (no normal boxes, no endpoints) — which
is unsurprising. The question is whether the *real* scheduler with normal-
box-first scheduling has only Θ(t^{1−1/γ}) LRP cuts in [1, t].

### 4.3 Where the rigorous argument would have to live

Let me sketch what a rigorous proof of "≤ O(t^{1−1/γ}) LRP cuts among the
first t steps" would require:

- A *potential function* Φ(state) that decreases by Ω(1) on each LRP cut and
  is bounded above by Φ_max ≤ O(t^{1−1/γ}).
- The natural candidate is Φ = (number of "fresh" calibrated stripes), or
  Φ = (LRP perimeter) — but neither has a clean Ω(1) decrement per LRP cut.

Alternatively:
- An *amortization* argument: after each LRP cut at time t, the next ~k^γ
  items don't trigger LRP cuts because they fit in normal boxes. This is
  exactly the dual of Claim N4's k ≳ t^{1/γ} invariant.

In either case, this is a **non-trivial step missing from §§7–11**.

The notes hand-wave §9.5 with "if the box was passed over, it must be too
narrow, hence k ≳ t^{1/γ}", but the converse — "every box of size k^{-γ}
*will* be used by some time ≤ k^γ" — is needed and *not* shown.

---

## 5. Compactness handling — is the avoidance rigorous?

The Lean formalization (per `15-final-closure-honest.md`) **avoids** Martin
compactness and tries to derive the unit-square packing directly from the
calibrated tail theorem.

Per `15-final-closure-honest.md` §"What IS mathematically true":

> "For γ ∈ (1, 3/2), the sum Σ D_n.area = 1/t (telescoping) is bounded; with
> balanced cuts and aspect ≤ R, the LRP minSide stays ≥ √(c/(R(t+k))), which
> is ≥ 1/(t+k) iff (t+k)² · c/R ≥ 1, i.e. t ≥ R/c. So with the right step
> function, AllStepsSucceed is genuinely true."

This is the local argument. It is *correct* per step **assuming** area_t · t ≥ c
holds at each t. The cumulative bound is the *only* thing standing between
this local argument and a complete proof. So the Martin avoidance is *not*
the issue — the issue is the cumulative invariant.

If the cumulative invariant fails (as the simulator shows), the avoidance of
Martin is moot: there is no exact unit-square packing produced by the
calibrated scheduler. We would fall back to ε-packings + Martin compactness,
which still requires the ε-packings to be honestly produced by the calibrated
framework. The framework's own gap propagates through.

**Verdict:** Compactness avoidance is rigorously routed *only if* the cumulative
LRP-area-share invariant survives. The avoidance itself is a sound
sharpening; the gap is upstream.

---

## 6. Final assessment

### 6.1 Solid (rigorously closed in the notes)

- **N1.** Calibrated active width definition.
- **N2.** Telescoping tail area Σ 1/(n(n+1)) = 1/t.
- **N7.** Balanced LRP aspect control. (Proof in §10.1 with explicit constant
  α²R/(c(1−1/R)²); already Lean-verified.)
- **N8.** Cellification arithmetic.

These four are unproblematic. They constitute the "scaffolding" — geometry
primitives that any framework would need.

### 6.2 Needs work (plausible proof, not tight)

- **N3 (normal-box width law).** The averaged O(q/t²) computation gives an
  *upper* bound but not a uniform two-sided bound c₁ k^{-γ} ≤ w(B_k) ≤ c₂ k^{-γ}
  for *every* normal box. Needs an explicit per-box invariant in the
  scheduler definition. Estimated repair: 1–2 weeks of paper math + Lean
  bookkeeping.

- **N9 (absorber cascade).** §11's ε-version is internally consistent but
  doesn't yield a *uniform* perimeter bound across all t. It works for a
  one-shot ε-packing, not for the asymptotic invariant. Need to upgrade to an
  amortized or potential-based argument.

### 6.3 Suspect (gaps that look unfixable without new ideas)

- **N4 (normal-box area sum).** The summation algebra is fine. The structural
  claim that "all unused normal boxes at time t have birth index k ≳ t^{1/γ}"
  has **no proof** in the notes. The needed lemma — every normal box of size
  ≍ k^{-γ} is consumed by time ≤ k^γ — would require a no-waste invariant
  that the endpoint-priority + normal-priority + LRP-cut scheduler doesn't
  obviously provide.

- **N5 (endpoint potential).** The per-step bound S_ep ≤ (C/t)·P_ep is fine.
  The global claim P_ep(t) ≤ η for a fixed η across all t is **suspect**.
  The §10.3 bookkeeping proves only P → C·P per cascade; with Θ(t) cascades
  in [1, t] this gives P_ep ≤ C^{Θ(t)}·P₀ = unbounded. The notes do not
  formalize the amortization that would tame this.

These are the analogues of Paulhus 1998's faulty endpoint lemma: claims that
*look* like they should follow from local bookkeeping, but in fact require
a non-trivial structural argument that has not been written down. They are
the most likely sources of an unfixable gap.

### 6.4 Cumulative argument: the bottom line

The numerical simulator, even of the *simplified* scheduler, is not the full
test. The full calibrated framework should make Θ(t) LRP cuts much rarer
(targeting Θ(t^{1−1/γ})) and ε-pack the rest into normal boxes and endpoints.
**This sublinearity of LRP cuts is the load-bearing claim**, but it's exactly
what Claim N4 needs and what is *not* rigorously proved.

A fair summary: the framework has a *plausible* mechanism, with **two
explicit gaps** (Claims N4 and N5) that look approximately the same shape as
historical errors in the literature on this problem. The Lean simplified-step
simulator falsifies these claims for the simplified setting. Whether the full
setting closes them is a research-level open question, not a mechanical
formalization step.

---

## 7. Recommendation

### 7.1 Do not invest 10 weeks of Lean engineering yet.

The Lean Route A (full calibrated scheduler with cellification, endpoints,
balanced cuts, normal-box width law, and explicit per-step bookkeeping) only
makes sense **after** the paper-side math has tightened Claims N4 and N5 into
explicit, sublinear-cut potential arguments. Otherwise we'd Lean-formalize a
proof that the paper itself doesn't contain.

### 7.2 What paper-side work is actually needed

The minimal sequence of paper-side improvements:

1. **A consumption invariant.** Prove (or precisely conjecture with computational
   evidence) that every normal box of width ≍ k^{-γ} created at time k is
   consumed by time ≤ C·k^γ. This needs an explicit scheduler-state argument
   not found in §§7–9.

2. **An amortized endpoint potential.** Show that P_ep(t) is bounded *despite*
   Θ(t) cascade events in [1, t]. The current §10.3 bookkeeping is local
   and doesn't aggregate. A potential-function argument is needed.

3. **A "fraction of LRP cuts" lemma.** Prove that #(LRP cuts in [1, t]) ≤
   C·t^{1−1/γ}. This is the load-bearing combinatorial lemma; it's where the
   γ > 1 hypothesis is used most essentially.

4. **Once these are tight, re-run the simulator** with the full scheduler
   to numerically check the cumulative bound. If the simulator still
   diverges, the paper-side argument has a residual gap that no amount of
   Lean engineering will fix.

### 7.3 Honest interim posture

The current research notes are **a framework**, not a closed proof. They
reduce the problem to a finite warm-start certificate *plus* the calibrated
tail theorem, but the calibrated tail theorem itself contains the two gaps
above. A paper claiming "we propose a framework and reduce the problem to
the warm-start lemma" is supportable; a paper claiming "we prove the
calibrated tail theorem" is not, given the current state of §§9.3–9.5.

For Lean: the right deliverable is a **conditional** formalization, where
N4 and N5 are stated as named axioms, and the surrounding scaffolding (N1,
N2, N7, N8) is proved. This is honest: the Lean artifact would say "the
Meir-Moser problem reduces to these two specific quantitative claims," and
the paper would discuss those claims. Such an artifact is publishable as a
formalization-of-conditional-result; it does not require closing N4/N5.

This is precisely what the current Lean tree comes close to (with the single
axiom `balanced_c_share_positive_axiom` standing in for the cumulative bound),
but the axiom should be split into N4 and N5 separately, with a clear paper-
side discussion of which is suspect and why.

---

## 8. Closing remark — analogy to Paulhus 1998 / Joós 2018

Paulhus 1998's "proof" of an analogous packing problem was found 20 years
later (Joós 2018) to contain a faulty endpoint lemma — exactly the kind of
gap I've flagged in Claim N5. The mechanism was identical: a per-step
bookkeeping inequality that looks right and aggregates to give a finite
result, but whose iteration (cascades, repetitions) is uncontrolled.

Our framework is at the same risk. The §10.3 inequality P → C·P per
cascade level is correct *per cascade*, but iterated Θ(t) times it is
fatal. The cure must be a non-local, potential-based argument that the
notes do not yet contain.

This audit's recommendation is to write down that potential argument
explicitly *before* Lean engineering, not after. Better to find the gap
now than 10 weeks into formalization.
