# Cleaner Proof Sketch — Drop Counting + Aspect

## The clean reduction

**Working invariant:** ∀k ≥ 1, ∃F* ∈ F_k with
  (i) `min(F*) ≥ c/√(k+1)`,
  (ii) `aspect(F*) ≥ 1 + 1/√(k+1)`.

If both hold for c ≥ 1: `ρ(k) = min(F*)·(k+1) ≥ c√(k+1) ≥ √(k+1) ≥ 1` for k ≥ 0. ✓

## Why (ii) helps Case B (BSSF must split F*)

WLOG F*.w = m (smaller), F*.h = M ≥ m, aspect = M/m. Place R = (a, b) (Moser, a > b) at corner. After split:
- Right child: (m−a, M). min = m − a = m − 1/(k+1).
- Top child: (m, M−b). min = min(m, M−1/(k+2)).
  - If `M − 1/(k+2) ≥ m`, then top.min = m **preserved**.
  - Equivalently: M ≥ m + 1/(k+2).

So **mss is preserved iff aspect = M/m ≥ 1 + 1/(m(k+2))**.

For m ≈ c/√(k+1), this needs aspect ≥ 1 + √(k+1)/(c(k+2)) ≈ 1 + 1/(c√(k+1)).

If invariant (ii) gives aspect ≥ 1 + 1/√(k+1), and c ≥ 1: condition holds, top child preserves mss.

Empirical (verify_alpha):
| k | aspect needed | aspect observed |
|---|---|---|
| 100 | 1.10 | 1.14 ✓ |
| 1000 | 1.032 | 1.10 ✓ |
| 10000 | 1.010 | 1.018 ✓ |
| 15000 | 1.008 | 1.030 ✓ |

Aspect always exceeds requirement. So Case B *as we defined it* preserves mss.

## What's still needed

* (P-i) Inductive carry of `min(F*) ≥ c/√(k+1)`. The new top child has min = m unchanged in Case B. New top child has aspect... `M' = M, m' = m` -- wait, in our case-B analysis, top child has dim (m, M−b). Its min is m (preserved), max is M (assuming M − b ≥ m which we showed). So its aspect is M/m, *unchanged*. So aspect propagates! ✓

But wait — in case B we picked F*. After case B, top child IS F* with reduced height. So m unchanged, M decreased by b. New aspect = (M−b)/m. Lower than before.

For aspect to remain ≥ 1 + 1/√(k+1+1) = 1 + 1/√(k+2):
  (M − b)/m ≥ 1 + 1/√(k+2),
  M ≥ m + m/√(k+2) + b = m + m/√(k+2) + 1/(k+2).

For m ≈ c/√(k+1): m/√(k+2) ≈ c/(k+1). And 1/(k+2) ≈ 1/k. So need M ≥ m + c/k + 1/k = m + (c+1)/k.

Original aspect M/m ≥ 1 + 1/√(k+1) means M ≥ m + m/√(k+1) ≈ m + c/(k+1).

We need M − b ≥ m + c/√(k+2), i.e., M ≥ m + b + c/√(k+2) = m + 1/(k+2) + c/√(k+2).

For m ≈ c/√(k+1) and large k: m/√(k+2) ≈ c/(k+1). So M ≥ m + (c + something) /(k+1).

Hmm. The "+1" is the difficulty. Aspect needs to grow by an additional 1/(k+1) per step to maintain the invariant. Where does this growth come from?

This is the **amortized** part: over many steps, aspect occasionally INCREASES (when neighboring FRs are pruned, F* gains room) and occasionally decreases (when F* is split).

* (P-ii) **Aspect-replenishment**: prove that the aspect ratio of F*
  GROWS *between* drop events, i.e. on Case A steps.

In Case A (BSSF picks some other FR, not F*), F* is unchanged. So aspect static. Hmm, then aspect can only decrease over time (in Case B). Eventually < 1 + 1/√k. Then preservation fails.

Unless: when an FR adjacent to F* is split, the NEW argmax-min FR could be a *fatter* one — including a child whose aspect is > previous F*'s.

Hmm subtle.

* (P-iii) **Resolve drift in m**: even if aspect is preserved, m
  may decrease over many drops. Need lower bound on m via the
  drop-count argument.

## The drop-count reduction (cleaner version)

Define a "drop event" at step k as: mss(k) < mss(k−1). Equivalently, all FRs achieving max-min at step k−1 were either split or pruned at step k.

**Claim (open):** the number of drop events in the first k steps is `D(k) = O(log k)` or `O(√k)`.

If `D(k) = O(√k)`, with drop magnitude `≤ 1/(k+2) ≈ 1/k`, total drop is `O(√k · 1/k) = O(1/√k)`.

Then `mss(k) ≥ mss(1) − O(1/√k) ≥ 1/2 − O(1/√k)`. For k large, `mss(k) ≥ 1/4` say.

But `mss(k) → 0` empirically (mss decays as 1/√k). So this analysis gives the WRONG direction. Reconsider.

Actually `mss(k) ≈ 0.4/√k` empirically. So mss does decay. But ρ = mss·(k+1) ≈ 0.4·√k → ∞.

For a *constant* lower bound on ρ (≥ 1 for all k), we need `mss(k) ≥ 1/(k+1)`. The drop-count bound `mss(k) ≥ mss(1) − D(k)/k` gives `mss ≥ 1/2 − const/k → 1/2`. So mss ≥ 1/2. But mss empirically → 0. **Contradiction with empirical fact.**

So the drop magnitude ISN'T bounded by 1/(k+2). Drops can be MUCH larger.

Specifically: if F* has min = m and is split, the children's min could be very small. mss(k+1) is the max over ALL remaining FRs, not just F*'s children.

So mss(k+1) = max(other_FRs.min, F*_R.min, F*_T.min). Other FRs may have min = m' for some m' < m.

Empirically `m' ≈ m − ε` for small ε. So drop is small. But not bounded by 1/(k+2).

Drop ≤ m' − m where m' is second-largest min. And m' depends on configuration.

OK let me also be precise: drop = mss(k) − mss(k+1). It's empirically O(1/√k) per drop (since both mss values are O(1/√k)).

For O(√k) drops each O(1/√k): total drop = O(√k / √k) = O(1). Bounded, so mss(k) ≥ mss(1) − const = 1/2 − const. If const < 1/2, mss(k) ≥ const' > 0. **Bounded below.**

But empirically mss → 0. So drops aren't all the same magnitude — they accumulate.

Hmm. Let me also re-examine.

Actually mss(k) ≈ 0.4/√k → 0. So mss DOES decay. The drop-count analysis must permit this.

If drops are O(1/√k) in magnitude on average, and there are O(√k) drops, total is O(√k · 1/√k) = O(1). Bounded.

But this would mean mss is bounded below. Contradicts mss → 0.

OK actually mss(k) = 0.4/√k → 0 is the "limit". Drops accumulate to 1/2 (initial mss) - 0 = 1/2 over all k.

So total accumulated drop = 1/2 (finite). Number of drops can be infinite.

For a lower bound mss(k) ≥ c/√(k+1):
   Σ drops up to k = mss(1) − mss(k) ≥ 1/2 − c/√(k+1).

If number of drops up to k is D(k), and each drop has magnitude bounded by Δ_max(k):
   Σ drops ≤ D(k) · Δ_max(k).

For mss decay c/√k, with D(k) drops and Δ_max(k) = O(1/√k):
   1/2 − c/√k ≤ D(k) · O(1/√k).
   D(k) ≥ (1/2 − c/√k) · √k / O(1) = O(√k).

So drops accumulate at rate O(√k).

For the proof via this route, we need:
   mss(k) ≥ c/√(k+1) for some c > 0.

This doesn't really need drop counting; it's just a statement about the asymptotic decay of mss.

Hmm, the drop-counting was a wrong direction.

Let me also think differently.

**The right framing:**

mss(k) is a non-increasing sequence. Sum of decrements = mss(0) - mss(∞) ≤ 1/2.

For the conjecture, we need mss(k) ≥ 1/(k+1). 
Equivalent: mss(k) - 1/(k+1) ≥ 0.

Rewrite as: mss(k) ≥ 1/(k+1).

Claim: at every drop event (step where mss decreases), the drop is bounded by some function f(k).

If Σ f(k) over drop events ≤ 1/2 - 1/(k+1), then mss(k) ≥ 1/(k+1).

Hmm, this is just restating.

OK enough proof attempts. Let me also accept this is hard and let things continue.
