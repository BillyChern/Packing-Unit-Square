"""Simulate the calibrated balanced step to see if c-share-positive holds."""
from fractions import Fraction

def simulate(c0, R, t0, area0, max_steps=10000):
    # Stripe width a_t = 1/(t+1) + 1/t²
    # Per-step c decrease: a_t · maxSide · (t+1)
    c, t, area = Fraction(c0), t0, Fraction(area0)
    # Assume the LRP is square at the worst case (aspect 1 or aspect R)
    # Use maxSide = sqrt(R * area), shorter = sqrt(area/R)
    cum_decay = Fraction(0)
    for k in range(max_steps):
        a_t = Fraction(1, t+1) + Fraction(1, t*t)
        # maxSide (worst case for decay)
        from math import sqrt
        maxSide_approx = sqrt(float(R) * float(area))  # approximate max
        shorter_approx = sqrt(float(area) / float(R))
        # Decay ≈ a_t · maxSide · (t+1)
        decay_step = float(a_t) * maxSide_approx * (t+1)
        # Per-step area loss = a_t · shorter
        loss = float(a_t) * shorter_approx
        cum_decay += Fraction(decay_step).limit_denominator(10**12)
        area -= Fraction(loss).limit_denominator(10**12)
        c_share = c - cum_decay
        if k in {0, 10, 100, 1000, 10000}:
            print(f"k={k:5d} | t={t:5d} | a_t={float(a_t):.6f} | "
                  f"maxSide≈{maxSide_approx:.4f} | area={float(area):.6f} | "
                  f"cum_decay={float(cum_decay):.4f} | "
                  f"c_share={float(c_share):.4f} | c·t={float(c_share)*t:.4f}")
        if c_share <= 0:
            print(f"!!! c_share went negative at k={k}, t={t}")
            break
        if area <= 0:
            print(f"!!! area went negative at k={k}, t={t}")
            break
        t += 1
    return c, t, area, cum_decay

print("=== Synthetic strong cert: c=40, R=2, t=100, area=0.4 ===")
simulate(40.0, 2.0, 100, 0.4, max_steps=5000)
print()
print("=== N=100-like: c=0.077, R=5.36, t=101, area=0.000762 ===")
simulate(0.077, 5.36, 101, 0.000762, max_steps=200)
