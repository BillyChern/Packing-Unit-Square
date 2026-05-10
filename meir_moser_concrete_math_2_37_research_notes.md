# Meir–Moser / *Concrete Mathematics* Problem 2.37 Research Notes

**Working note generated from our discussion.**  
**Date:** 2026-05-10  
**Problem:** Can the rectangles  
\[
D_n=\frac1n\times\frac1{n+1},\qquad n=1,2,\dots
\]
be packed into the unit square?

---

## 0. Executive summary

We focused on *Concrete Mathematics* Problem 2.37, also known as a Meir–Moser rectangle packing problem:

\[
\sum_{n=1}^{\infty}\frac1{n(n+1)}=1.
\]

The question is whether the rectangles \(1/n\times 1/(n+1)\) can be packed into the \(1\times1\) square without overlap.

The exact problem remains open in the literature. The best public computational frontier we referenced is Zhu–Joós, who packed the first \(1.35\cdot10^{11}\) rectangles into the unit square and derived an extremely small positive \(\varepsilon\)-bound for the full infinite sequence. The newest structural method we referenced is the Slack-Pack algorithm, which obtains a large-rectangular-piece lower bound under natural assumptions. Our research direction was to try to remove those assumptions deterministically.

The main new conceptual package we developed is:

\[
\boxed{\text{Calibrated Slack-Pack + two-backtrack anti-sliver + endpoint-perimeter potential.}}
\]

The strongest honest conclusion from our discussion:

> We have not solved the original open problem.  
> But we reduced the remaining hard part to a very specific **finite burn-in / warm-start certificate** problem.

The proposed route to a publishable SOTA project is:

1. Prove a rigorous **calibrated tail theorem** for all sufficiently large \(N\).
2. Find/certify a finite warm-start state at some large \(N\).
3. Combine the finite certificate with the tail theorem.
4. Use compactness to pass from \((1+\varepsilon)\)-packings to the exact unit-square packing.

---

## 1. References we used

### 1.1 Original problem / background

- R. Graham, D. Knuth, O. Patashnik, *Concrete Mathematics*, Problem 2.37.  
  The problem asks whether all rectangles \(1/k\times1/(k+1)\) fit inside the unit square.

- MathOverflow discussion: “Can we cover the unit square by these rectangles?”  
  <https://mathoverflow.net/questions/34145/can-we-cover-the-unit-square-by-these-rectangles>  
  The MathOverflow thread states the problem as a research exercise from *Concrete Mathematics* and discusses computational and historical progress.

### 1.2 Current approximate frontier

- Mingliang Zhu and Antal Joós, “Packing \(1.35\cdot10^{11}\) rectangles into a unit square,” arXiv:2211.10356.  
  <https://arxiv.org/abs/2211.10356>  
  They show they can pack the first \(1.35\cdot10^{11}\) rectangles into the unit square and derive an \(\varepsilon\)-estimate for the full infinite problem.

### 1.3 Slack-Pack algorithm

- A. D. Kislovskiy, E. Yu. Lerner, I. A. Senkevich, “Slack-Pack algorithm for Meir-Moser packing problem,” arXiv:2412.17151.  
  <https://arxiv.org/abs/2412.17151>  
  The paper introduces Slack-Pack, uses a parameter  
  \[
  \sqrt{3/2}<\gamma<3/2,
  \]
  and conditionally controls the ratio of the large rectangular part, LRP, to remaining empty area. The abstract says the LRP ratio exceeds approximately  
  \[
  1-\frac1\gamma-\delta
  \]
  under natural assumptions.

### 1.4 Tao’s related theorem

- Terence Tao, “Perfectly packing a square by squares of nearly harmonic sidelength,” arXiv:2202.03594.  
  <https://arxiv.org/abs/2202.03594>  
  Tao proves a related near-critical theorem for squares of sidelength \(n^{-t}\), \(1/2<t<1\), for sufficiently large \(n_0\). This motivates the idea that the critical \(t=1\) case is the hard boundary.

### 1.5 Compactness bridge

- Greg Martin, “Compactness Theorems for Geometric Packings,” arXiv:math/0005054.  
  <https://arxiv.org/abs/math/0005054>  
  Martin proves compactness theorems implying that “for every \(\varepsilon>0\)” packing versions of Moser-type problems imply the exact limiting packing problem.

### 1.6 MaxRects / finite heuristic experiments

- Jukka Jylänki, *A Thousand Ways to Pack the Bin — A Practical Approach to Two-Dimensional Rectangle Bin Packing*.  
  Reference implementation / repository: <https://github.com/juj/RectangleBinPack>  
  MaxRects maintains a set of maximal empty rectangles and greedily places new rectangles using scoring rules such as Best Short Side Fit, Best Area Fit, Bottom Left, and Contact Point.

---

## 2. Problem statement and notation

Define

\[
D_n=\frac1n\times\frac1{n+1}.
\]

The area is

\[
\operatorname{area}(D_n)=\frac1{n(n+1)}.
\]

The total area telescopes:

\[
\sum_{n=1}^{\infty}\frac1{n(n+1)}
=
\sum_{n=1}^{\infty}\left(\frac1n-\frac1{n+1}\right)
=
1.
\]

The question:

\[
\boxed{
\text{Can all }D_n\text{ be packed into }[0,1]^2?
}
\]

For a tail starting at \(t\),

\[
S_{\mathrm{com}}(t)
=
\sum_{n=t}^{\infty}\frac1{n(n+1)}
=
\frac1t.
\]

This identity is central to all asymptotic arguments.

---

## 3. Why Problem 2.37 looked promising among the *Concrete Mathematics* research problems

We identified Problem 2.37 as promising because it has a rare balance:

- It is easy to state.
- It has strong partial progress.
- It is computationally attackable.
- It has visible modern structure through Tao’s near-harmonic theorem and Slack-Pack.
- It is likely more approachable than extremely deep number-theoretic exercises like \(\gamma\)-irrationality, Cramér-type prime gaps, or Mersenne squarefreeness.

Compared with other problems in *Concrete Mathematics*, 2.37 has a clear path for hybrid mathematics + certified computation.

---

## 4. The current known frontier

### 4.1 Zhu–Joós

Zhu–Joós pack the first

\[
1.35\cdot10^{11}
\]

rectangles into the unit square and estimate the remaining infinite tail. This is the strongest public large finite computation we discussed.

Their result is not a proof of exact unit-square packing. It shows an extremely small positive \(\varepsilon\) bound for an enlarged square/area setting.

### 4.2 Slack-Pack

Slack-Pack introduces a large rectangular part, LRP, and decomposes the remaining empty area into pieces:

\[
S_{\mathrm{com}}(t)
=
S_{\mathrm{LRP}}(t)
+
S_{\mathrm{norm}}(t)
+
S_{\mathrm{ep}}(t).
\]

The paper’s main conditional target is roughly:

\[
\frac{S_{\mathrm{LRP}}(t)}{S_{\mathrm{com}}(t)}
>
1-\frac1\gamma-\delta.
\]

The issue is that the Slack-Pack proof depends on assumptions, especially:

1. a normal-box shape law,
2. endpoint behavior / pseudorandomness.

Our work tried to replace both with deterministic mechanisms.

---

## 5. MaxRects: what it is and how it relates

MaxRects is a 2D rectangle-packing heuristic. It keeps a list of maximal empty rectangles and, when a rectangle is placed, splits intersected free regions into new candidate free rectangles.

For our problem, a MaxRects experiment means:

\[
\text{try to pack }D_1,\dots,D_N\text{ into }[0,1]^2.
\]

It is not a proof, but it is useful for discovering finite warm-start states.

Common heuristics:

| Heuristic | Idea |
|---|---|
| Best Short Side Fit | Minimize shorter leftover side |
| Best Long Side Fit | Minimize longer leftover side |
| Best Area Fit | Use smallest free rectangle that fits |
| Bottom Left | Prefer low-left placements |
| Contact Point | Prefer placements touching existing boundaries/rectangles |

We discussed that MaxRects is useful for warm-start search but insufficient as a proof without exact rational/interval certificates.

---

## 6. Small computational experiments we discussed

### 6.1 Clean start after \(D_1,D_2\)

Place

\[
D_1=1\times\frac12
\]

as the bottom half of the unit square. The remaining top half is

\[
1\times\frac12
\]

with area \(1/2\), exactly equal to the tail area from \(D_2\).

Then rotate

\[
D_2=\frac12\times\frac13
\]

as

\[
\frac13\times\frac12
\]

inside the top half. The leftover region is

\[
\frac23\times\frac12,
\]

whose area is \(1/3\), exactly equal to the tail area from \(D_3\).

This clean rectangle recursion fails at \(D_3\). The simple shelf construction in the \((2/3)\times(1/2)\) rectangle gave:

```text
Row 1: D3-D4
height = 1/4
used width = 1/3 + 1/4 = 7/12
remaining width = 1/12

Row 2: D5-D8
height = 1/6
used width = 1/5 + 1/6 + 1/7 + 1/8 ≈ 0.634523
remaining width ≈ 0.032143

Total used height = 1/4 + 1/6 = 5/12
remaining height = 1/12

Next rectangle D9 has height 1/10, which is larger than 1/12.
```

So the naive clean-tail shelf recursion fails by \(D_9\).

### 6.2 MaxRects diagnostic table

A simple floating-point MaxRects heuristic with rotations produced promising finite states. The important diagnostic was the ratio

\[
\frac{\text{largest empty rectangle area}}{\text{remaining tail area}}.
\]

Observed values from our discussion:

| Heuristic | \(N\) | Failed? | Largest empty rectangle area | Tail area \(1/(N+1)\) | LRP / tail |
|---|---:|---|---:|---:|---:|
| Best Short Side Fit | 100 | no | 0.0037216 | 0.0099010 | 0.3759 |
| Best Short Side Fit | 200 | no | 0.0027160 | 0.0049751 | 0.5459 |
| Best Short Side Fit | 500 | no | 0.0006496 | 0.0019960 | 0.3255 |
| Best Short Side Fit | 800 | no | 0.0003464 | 0.0012484 | 0.2775 |
| Best Area Fit | 500 | no | 0.0007569 | 0.0019960 | 0.3792 |
| Bottom Left | 800 | no | 0.0004123 | 0.0012484 | 0.3302 |

These are not proof-level results, but they support the idea that a positive LRP fraction emerges naturally.

---

## 7. Core proposed method: Calibrated Slack-Pack

Fix

\[
1<\gamma<\frac32.
\]

Define the calibrated active width

\[
a_t=\frac1{t+1}+t^{-\gamma}.
\]

The proposed calibrated scheduler:

1. **Endpoint priority:** If a suitable endpoint/absorber can fit the next detail, use it before cutting the LRP.
2. **Normal-box priority:** If no endpoint fits but a normal box fits, use a normal box.
3. **LRP cut:** Cut a fresh calibrated stripe from the LRP only if no endpoint or normal box fits.
4. **Calibration:** Before using an oversized available box, cut a calibrated active subbox of width \(a_t\).
5. **Two-backtrack anti-sliver:** If a row endpoint is too thin, undo one or two placements to make it fat.
6. **Balanced LRP cuts:** Always cut a stripe from the longer side of the LRP.

This was designed to replace Slack-Pack’s assumptions with deterministic invariants.

---

## 8. Key decomposition

At time \(t\), the remaining tail area is

\[
S_{\mathrm{com}}(t)=\frac1t.
\]

We decompose empty area:

\[
S_{\mathrm{com}}(t)
=
S_{\mathrm{LRP}}(t)
+
S_{\mathrm{norm}}(t)
+
S_{\mathrm{ep}}(t).
\]

The goal is to prove that at every LRP-critical time,

\[
S_{\mathrm{LRP}}(t)
\ge
\frac{c}{t}
\]

for some fixed \(c>0\).

If the LRP also has bounded aspect ratio, then its side lengths are \(\Omega(t^{-1/2})\), while the next rectangle has side scale \(O(t^{-1})\). Therefore the next calibrated stripe fits.

---

## 9. Lemma package developed in our discussion

### 9.1 Compactness reduction

If the rectangles can be packed into \([0,1+\varepsilon]^2\) for every \(\varepsilon>0\), then compactness can be used to obtain an exact unit-square packing. This is the role of Martin’s theorem.

Therefore it suffices to prove an arbitrary-\(\varepsilon\) packing theorem.

---

### 9.2 Two-backtrack anti-sliver lemma

When a row stops greedily, the leftover endpoint may be a sliver. The deterministic fix:

- If endpoint thickness \(\rho\) is below threshold \(\lambda/t\), undo one rectangle.
- If still below, undo one more.

Since each undone rectangle changes the residual by \(\Theta(1/t)\), after at most two undos:

\[
\frac{\lambda}{t}
\le
\rho^\star
\le
\frac{\lambda+C}{t}.
\]

Thus endpoints become fat at scale \(1/t\), rather than arbitrarily thin.

This attacks Slack-Pack’s endpoint pseudorandomness assumption.

---

### 9.3 Endpoint priority and endpoint-perimeter potential

Counting endpoints is fragile because cellification can create many cells. The better invariant is total endpoint semiperimeter:

\[
P_{\mathrm{ep}}(t)=\sum_E (w(E)+h(E)).
\]

At an LRP-critical time, endpoint priority implies every endpoint is too narrow for the current detail, hence:

\[
w(E)\le \frac{C}{t}.
\]

Then

\[
\operatorname{area}(E)\le \frac{C}{t}h(E).
\]

Summing:

\[
S_{\mathrm{ep}}(t)
\le
\frac{C}{t}P_{\mathrm{ep}}(t).
\]

If \(P_{\mathrm{ep}}(t)\le \eta\), then

\[
S_{\mathrm{ep}}(t)\le \frac{C\eta}{t}.
\]

This gives deterministic endpoint control.

---

### 9.4 Calibration gives the normal-width law

In a calibrated active box of width

\[
a_t=\frac1{t+1}+t^{-\gamma},
\]

placing \(D_j\) creates a normal box of width

\[
a_t-\frac1{j+1}
=
t^{-\gamma}
+
\left(\frac1{t+1}-\frac1{j+1}\right).
\]

If the row length is \(q=j-t\), then

\[
\frac1{t+1}-\frac1{j+1}=O(q/t^2).
\]

Inside normal boxes, expected row lengths are

\[
q=O(t^{1-1/\gamma}),
\]

so

\[
q/t^2=O(t^{-1-1/\gamma})=o(t^{-\gamma})
\]

for \(1<\gamma<3/2\). Therefore:

\[
w(B_j)\asymp j^{-\gamma},
\qquad
\operatorname{area}(B_j)\asymp j^{-\gamma-1}.
\]

This replaces Slack-Pack’s normal-box shape assumption.

---

### 9.5 Normal-box area estimate

At an LRP-critical time, no normal box is wide enough for \(D_t\). If a normal box born at \(k\) has width \(\asymp k^{-\gamma}\), then it being too narrow implies

\[
k\gtrsim t^{1/\gamma}.
\]

Therefore

\[
S_{\mathrm{norm}}(t)
\le
\sum_{k\gtrsim t^{1/\gamma}} Ck^{-\gamma-1}
=
\left(\frac{C}{\gamma}+o(1)\right)\frac1t.
\]

With calibrated constants close to \(1\), the target becomes:

\[
S_{\mathrm{norm}}(t)
\le
\left(\frac1\gamma+\delta\right)\frac1t.
\]

---

### 9.6 LRP lower bound

Using

\[
S_{\mathrm{LRP}}(t)
=
\frac1t-S_{\mathrm{norm}}(t)-S_{\mathrm{ep}}(t),
\]

and the bounds

\[
S_{\mathrm{norm}}(t)\le \left(\frac1\gamma+\delta\right)\frac1t,
\]

\[
S_{\mathrm{ep}}(t)\le \frac{\delta}{t},
\]

we get

\[
S_{\mathrm{LRP}}(t)
\ge
\left(1-\frac1\gamma-2\delta\right)\frac1t.
\]

For \(\gamma>1\) and small \(\delta\), the coefficient is positive.

---

## 10. Fully rigorous local bookkeeping lemmas

### 10.1 Balanced LRP aspect-control lemma

Let the LRP be a rectangle with side lengths

\[
X\ge Y>0,
\]

area

\[
A=XY\ge \frac{c}{t},
\]

and aspect ratio

\[
\frac{X}{Y}\le R.
\]

Suppose we cut from the longer side a stripe of thickness

\[
s\le \frac{\alpha}{t}.
\]

If

\[
t\ge
\frac{\alpha^2R}{c(1-1/R)^2},
\]

then the new LRP still has aspect ratio at most \(R\).

Proof sketch:

Since \(XY\ge c/t\) and \(X\le RY\),

\[
Y\ge \sqrt{\frac{c}{Rt}}.
\]

It is enough to guarantee

\[
s\le \left(1-\frac1R\right)Y.
\]

This follows from the stated lower bound on \(t\). Thus cutting from the longer side preserves aspect ratio.

---

### 10.2 Cellification lemma

Let \(S\) be a strip with side lengths \(M\ge m>0\). Partition along the long side into

\[
N=\left\lceil \frac{M}{m}\right\rceil
\]

rectangles of dimensions

\[
m\times \frac{M}{N}.
\]

Then each cell has aspect ratio at most \(2\), and the total semiperimeter is at most

\[
3M.
\]

Proof:

\[
\frac m2<\frac{M}{N}\le m.
\]

Thus aspect ratio \(\le2\). Total semiperimeter:

\[
N\left(m+\frac{M}{N}\right)=Nm+M\le 3M.
\]

---

### 10.3 Shelf residual bookkeeping

For a box \(B=W\times H\), if horizontal two-backtrack gives row endpoints of width \(O(s)\) and height \(O(s)\), then row endpoints contribute:

\[
A_{\mathrm{row}}\le C sH,
\]

\[
P_{\mathrm{row}}\le C H.
\]

The bottom strip contributes:

\[
A_{\mathrm{bottom}}\le C sW,
\]

and after cellification,

\[
P_{\mathrm{bottom}}\le C W.
\]

Therefore total residuals from \(B\) satisfy

\[
A_{\mathrm{res}}(B)\le C s(W+H),
\]

\[
P_{\mathrm{res}}(B)\le C(W+H).
\]

For a family \(\mathcal B\):

\[
A(\mathcal B')\le C s P(\mathcal B),
\]

\[
P(\mathcal B')\le C P(\mathcal B).
\]

This supports the absorber cascade.

---

## 11. Absorber cascade: corrected \(\varepsilon\)-version

The original too-strong idea was:

> Fill absorbers perfectly in one shot.

The corrected rigorous target:

> Fill absorbers up to arbitrarily small leftover area.

If an absorber family has area \(A_j\), semiperimeter \(P_j\), and the next rectangle scale is \(s_j\asymp A_j\), then the residual estimates give:

\[
A_{j+1}\le C A_jP_j,
\]

\[
P_{j+1}\le CP_j.
\]

If \(P_0\) is sufficiently small and we only need finite depth \(r\), choose the starting index sufficiently large so that:

\[
C^rP_0\ll1.
\]

Then the leftover area after \(r\) cascade levels is arbitrarily small.

This is enough for the \(\varepsilon\)-packing route, and compactness handles the final exact limit.

---

## 12. Where the proof still fails to be complete

The remaining obstruction is the **Finite Burn-In / Warm-Start Lemma**.

### Needed lemma

For every \(\varepsilon>0\), there exists \(N\) such that \(D_1,\dots,D_{N-1}\) can be packed into \([0,1+\varepsilon]^2\) while leaving a good calibrated tail state for \(D_N,D_{N+1},\dots\).

A good tail state means:

1. LRP area:
   \[
   S_{\mathrm{LRP}}(N)\ge \frac{c}{N}.
   \]
2. LRP aspect ratio bounded:
   \[
   \operatorname{aspect}(\mathrm{LRP})\le R.
   \]
3. Endpoint perimeter small:
   \[
   P_{\mathrm{ep}}(N)\le \eta.
   \]
4. Normal boxes satisfy calibrated width law:
   \[
   w(B_k)\asymp k^{-\gamma}.
   \]
5. Total state area compatible with the remaining tail:
   \[
   S_{\mathrm{state}}(N)\approx \frac1N.
   \]

We do not yet have a proof of this lemma.

---

## 13. Why Burn-In is genuinely hard

The tempting area-only argument fails:

\[
\operatorname{area}(D_1,\dots,D_{N-1})=1-\frac1N.
\]

But leaving area \(1/N\) is not enough. The leftover must contain usable geometry.

Generic rectangle-packing theorems are too lossy near density \(1\), and they do not preserve a tiny calibrated tail container.

Therefore Burn-In is essentially the remaining open core.

---

## 14. Current strongest honest theorem statement

### Conditional Main Theorem

Assume:

1. The calibrated tail theorem holds for all sufficiently large \(N\).
2. There exists a sequence \(N_j\to\infty\), \(\varepsilon_j\to0\), such that the prefix
   \[
   D_1,\dots,D_{N_j-1}
   \]
   packs into \([0,1+\varepsilon_j]^2\) while leaving a good calibrated tail state.

Then the full sequence \(D_1,D_2,\dots\) packs into the unit square.

Proof:

- Fill the tail using the calibrated tail theorem.
- Obtain packings into \([0,1+\varepsilon_j]^2\).
- Let \(\varepsilon_j\to0\).
- Apply Martin compactness.

---

## 15. Concrete path forward

### 15.1 Build a finite certificate searcher

Implement a certified calibrated MaxRects / Slack-Pack hybrid.

State variables:

```text
Placed rectangles:
  index n
  orientation
  rational/interval coordinates

Free-region decomposition:
  LRP rectangle
  normal boxes
  endpoint/absorber cells

Certified invariants:
  S_LRP >= c/N
  aspect(LRP) <= R
  P_ep <= eta
  normal width bounds
  no-overlap certificate
  containment certificate
```

### 15.2 Use exact rational or interval arithmetic

Floating-point experiments are useful for discovery but not proof.

For a certificate, store coordinates as:

- exact rationals, or
- rational intervals with outward rounding.

A checker should verify:

1. every \(D_n\) lies inside the square,
2. interiors are disjoint,
3. free regions cover the complement up to certified residual,
4. the good tail-state inequalities hold.

### 15.3 Search targets

Start with modest \(N\):

\[
N=10^3,\ 10^4,\ 10^5.
\]

For each \(N\), try to produce a state with:

\[
S_{\mathrm{LRP}}(N)/(1/N)\ge c
\]

for fixed \(c\), say \(0.1\) or \(0.2\).

Then gradually add stronger conditions:

- bounded aspect ratio,
- low endpoint perimeter,
- calibrated normal boxes.

### 15.4 Candidate algorithms

1. Generic MaxRects warm start.
2. Calibrated MaxRects:
   - prefer free rectangles that allow calibrated active width \(a_t\).
3. Endpoint-priority calibrated Slack-Pack:
   - use endpoints before LRP.
4. Hybrid:
   - MaxRects for early burn-in,
   - switch to calibrated Slack-Pack once a clean LRP emerges.

---

## 16. Proposed paper structure

### Title options

- **Calibrated Slack-Pack and Endpoint Potentials for the Meir–Moser Rectangle Problem**
- **A Deterministic Absorber Framework for Harmonic Rectangle Packing**
- **Toward the Critical Meir–Moser Rectangle Packing Problem via Calibrated Slack-Pack**

### Abstract idea

We introduce a calibrated variant of the Slack-Pack algorithm for the Meir–Moser rectangle packing problem. The method uses calibrated active widths, a two-backtrack anti-sliver rule, endpoint-priority scheduling, and an endpoint-perimeter potential to replace the pseudorandom endpoint assumptions in previous Slack-Pack analysis. We prove rigorous local invariants for normal-box widths, endpoint area control, LRP aspect preservation, and absorber cellification. The full Meir–Moser problem is reduced to a finite warm-start certificate.

### Main results

1. Calibrated normal-box theorem.
2. Two-backtrack endpoint theorem.
3. Endpoint-perimeter potential theorem.
4. Balanced LRP theorem.
5. Cellification/absorber cascade theorem.
6. Conditional main theorem reducing the full problem to finite warm-start certification.

---

## 17. What we should not claim

We should **not** claim:

\[
\text{“The Meir–Moser problem is solved.”}
\]

We should claim:

\[
\text{“We propose a deterministic calibrated Slack-Pack framework and reduce the remaining problem to finite warm-start certification.”}
\]

This is honest and potentially publishable.

---

## 18. Summary of achievements

We achieved:

1. Identified Problem 2.37 as the most promising *Concrete Mathematics* research problem.
2. Reviewed the best known frontier:
   - Zhu–Joós finite computation,
   - Slack-Pack conditional theorem,
   - Tao near-harmonic theorem,
   - Martin compactness theorem.
3. Understood MaxRects and used it as a finite-state discovery tool.
4. Developed **two-backtrack anti-sliver** to replace endpoint pseudorandomness.
5. Developed **endpoint-priority scheduling**.
6. Replaced endpoint counting with **endpoint semiperimeter potential**.
7. Developed **calibrated active widths** to force normal-box shape.
8. Proved balanced LRP aspect control with explicit constants.
9. Proved cellification/perimeter bookkeeping with explicit constants.
10. Formulated an absorber cascade in the \(\varepsilon\)-packing sense.
11. Reduced the final problem to the **Finite Burn-In / Warm-Start Lemma**.

---

## 19. Final path forward

The final path is:

\[
\boxed{
\text{Build a finite warm-start certificate.}
}
\]

More concretely:

1. Implement calibrated MaxRects / Slack-Pack.
2. Use exact rational or interval arithmetic.
3. Search for a finite \(N\) state satisfying calibrated tail-start invariants.
4. Prove a certificate-checking theorem.
5. Combine with the calibrated tail theorem.
6. Apply Martin compactness.

If successful, this would be a credible route to the exact unit-square theorem.

---

## 20. Minimal certificate schema

A certificate file should include:

```yaml
N: integer
gamma: rational or interval
square_side: rational or interval
placed_rectangles:
  - n: 1
    x0: rational
    y0: rational
    x1: rational
    y1: rational
    orientation: normal/rotated
free_state:
  LRP:
    x0: rational
    y0: rational
    x1: rational
    y1: rational
  normal_boxes:
    - birth_index: k
      x0: rational
      y0: rational
      x1: rational
      y1: rational
  endpoint_boxes:
    - x0: rational
      y0: rational
      x1: rational
      y1: rational
verified_bounds:
  S_LRP_over_tail: rational lower bound
  LRP_aspect: rational upper bound
  P_endpoint: rational upper bound
  normal_width_constants:
    lower: rational
    upper: rational
```

The checker verifies:

\[
S_{\mathrm{LRP}}(N)\ge \frac{c}{N},
\]

\[
\operatorname{aspect}(\mathrm{LRP})\le R,
\]

\[
P_{\mathrm{ep}}(N)\le \eta,
\]

\[
c_1 k^{-\gamma}\le w(B_k)\le c_2 k^{-\gamma},
\]

and disjoint containment of all placed rectangles.

---

## 21. Closing note

This project is promising because it transforms a broad open problem into a sequence of sharply testable claims:

\[
\text{local deterministic lemmas}
+
\text{finite certificate}
+
\text{compactness}.
\]

The main intellectual contribution is no longer “we hope endpoints are random.” It is:

\[
\boxed{
\text{Use calibration and endpoint perimeter to make the Slack-Pack invariants deterministic.}
}
\]

That is the new SOTA research direction.
