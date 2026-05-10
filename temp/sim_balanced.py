"""
Simulation of the balanced step from SchedulerInductionBalanced.lean.

Tests whether `balanced_c_share_positive_axiom` holds:
  c_share_witness(k) = c - sum_{j=0}^{k-1} maxSide_j * (1 + 1/t_j) > 0
  AND R <= c_share_witness(k) * (t_0 + k)

for the simplified balanced step (rotated D_t at LRP corner, cut from longer side,
slice width 1/(t+1) on x-cut or 1/t on y-cut).
"""

from fractions import Fraction


def balanced_step(LRP_w, LRP_h, t):
    """One balanced step.

    Args:
        LRP_w, LRP_h: current LRP width/height (Fraction)
        t: current step index (we place D_t)

    Returns:
        (new_w, new_h, fits, cut_x, slice_w_or_h, max_side)
        where max_side is max(LRP_w, LRP_h) BEFORE the step (used in axiom witness).
    """
    w_rot = Fraction(1, t + 1)  # rotated D_t width
    h_rot = Fraction(1, t)      # rotated D_t height

    # Fit check: rotated D_t must fit in LRP
    fits = (w_rot <= LRP_w) and (h_rot <= LRP_h)
    if not fits:
        return LRP_w, LRP_h, False, None, None, max(LRP_w, LRP_h)

    cut_x = (LRP_h <= LRP_w)  # cutFromX: width >= height
    if cut_x:
        # x-cut: shave vertical strip of width w_rot from left.
        new_w = LRP_w - w_rot
        new_h = LRP_h
    else:
        # y-cut: shave horizontal strip of height h_rot from bottom.
        new_w = LRP_w
        new_h = LRP_h - h_rot

    return new_w, new_h, True, cut_x, (w_rot if cut_x else h_rot), max(LRP_w, LRP_h)


def simulate(c0, R, LRP_w0, LRP_h0, t0, K_max, log_at=None):
    """Simulate K_max steps and track c_share_witness.

    c_share_witness(k) = c0 - sum_{j=0}^{k-1} maxSide_j * (1 + 1/t_j)

    Reports:
      - Whether fit holds at each step (LRP.minSide >= 1/t)
      - c_share_witness(k) > 0 ?
      - c_share_witness(k) * (t0 + k) >= R ?

    Returns log of (k, t_k, LRP_w, LRP_h, min_side, 1/t, fits, c_share, c_share*t, R)
    """
    if log_at is None:
        log_at = [0, 1, 10, 100, 1000, 10000, K_max]

    LRP_w = LRP_w0
    LRP_h = LRP_h0
    t = t0
    cum = Fraction(0)  # cumulative sum of maxSide_j * (1 + 1/t_j)
    log = []

    # Find the first k at which any failure happens
    fail_share_pos = None
    fail_share_R = None
    fail_fit = None

    for k in range(K_max + 1):
        c_share = c0 - cum
        c_share_t = c_share * t  # c_share_witness(k) * (t0 + k) where t = t0 + k
        min_side = min(LRP_w, LRP_h)
        one_over_t = Fraction(1, t)

        # Record when we cross thresholds
        if fail_share_pos is None and c_share <= 0:
            fail_share_pos = k
        if fail_share_R is None and c_share_t < R:
            fail_share_R = k
        if fail_fit is None and min_side < one_over_t:
            fail_fit = k

        if k in log_at:
            log.append({
                'k': k,
                't': t,
                'LRP_w': float(LRP_w),
                'LRP_h': float(LRP_h),
                'min_side': float(min_side),
                'one_over_t': float(one_over_t),
                'fits': min_side >= one_over_t,
                'aspect': float(max(LRP_w, LRP_h) / max(min_side, Fraction(1, 10**18))),
                'c_share': float(c_share),
                'c_share_t': float(c_share_t),
                'R': float(R),
                'c_share_t_minus_R': float(c_share_t - R),
                'cum': float(cum),
            })

        if k == K_max:
            break

        # Step
        new_w, new_h, fits, cut_x, slice_, max_side = balanced_step(LRP_w, LRP_h, t)
        if not fits:
            # Cannot place; record where it stops
            log.append({
                'k': k,
                't': t,
                'note': 'fit_failed',
                'LRP_w': float(LRP_w),
                'LRP_h': float(LRP_h),
                'min_side': float(min_side),
                'one_over_t': float(one_over_t),
            })
            break

        # Update cumulative
        increment = max_side * (Fraction(1) + Fraction(1, t))
        cum += increment

        LRP_w, LRP_h = new_w, new_h
        t += 1

    return log, fail_share_pos, fail_share_R, fail_fit


def test_synthetic():
    """Synthesized strong cert: LRP.area=0.4, aspect=2, t0=100, c0=R*c-room."""
    print("=" * 70)
    print("TEST 1: Synthesized strong cert")
    print("  LRP = some rect with area ~0.4, aspect ~2, t_0 = 100")
    print("  Choose LRP_w = sqrt(0.8), LRP_h = sqrt(0.2). aspect=2.")
    print("  c_0 = 40 (so c_0 * t_0 = 4000), R = 2.")
    print("=" * 70)
    # We need rationals; take LRP = 4/5 by 1/2 (area 0.4, aspect 1.6) - close enough
    # Actually use LRP_w = 4/5, LRP_h = 1/2: area = 2/5 = 0.4, aspect = 8/5 = 1.6
    LRP_w0 = Fraction(4, 5)
    LRP_h0 = Fraction(1, 2)
    t0 = 100
    R = Fraction(2)
    c0 = Fraction(40)
    print(f"  Initial: LRP=({float(LRP_w0)}, {float(LRP_h0)}), t0={t0}, R={float(R)}, c0={float(c0)}")
    print(f"  c0 * t0 = {float(c0 * t0)}, R={float(R)}, R<=c0*t0? {R <= c0 * t0}")
    print()

    log, fp, fR, fF = simulate(c0, R, LRP_w0, LRP_h0, t0, K_max=10000,
                                 log_at=[0, 1, 10, 100, 1000, 5000, 10000])
    print(f"{'k':>6} {'t':>6} {'min_side':>12} {'1/t':>12} {'fits':>5} "
          f"{'aspect':>8} {'c_share':>14} {'c_share*t':>14} {'R':>8} "
          f"{'c_share*t-R':>14}")
    for L in log:
        if 'note' in L:
            print(f"  fit failed at k={L['k']}, t={L['t']}, LRP=({L['LRP_w']:.6f},{L['LRP_h']:.6f})")
            continue
        print(f"{L['k']:>6} {L['t']:>6} {L['min_side']:>12.6e} {L['one_over_t']:>12.6e} "
              f"{str(L['fits']):>5} {L['aspect']:>8.2f} "
              f"{L['c_share']:>14.6e} {L['c_share_t']:>14.6e} "
              f"{L['R']:>8.4f} {L['c_share_t_minus_R']:>14.6e}")
    print()
    print(f"  First k where c_share <= 0: {fp}")
    print(f"  First k where c_share * t < R: {fR}")
    print(f"  First k where min_side < 1/t (fit fails): {fF}")
    print()
    return log, fp, fR, fF


def test_warmstart():
    """WarmStartN100 approximation: aspect=5.36, area=7.6e-4, c=0.077, R=5.36, t0=101."""
    print("=" * 70)
    print("TEST 2: WarmStartN100-like cert")
    print("  Initial LRP area ~ 7.6e-4, aspect ~ 5.36, t0=101.")
    print("  c=0.077, R=5.36. c*t0 = 7.777. R <= c*t0? Yes.")
    print("=" * 70)
    # area = w*h = 7.6e-4, h/w = 1/5.36 (so h is small if w is big and aspect is w/h=5.36).
    # Actually take LRP_w >> LRP_h. w*h = a, w/h = ar => w = sqrt(a*ar), h = sqrt(a/ar).
    # w = sqrt(7.6e-4 * 5.36) ~ 0.0638, h = sqrt(7.6e-4 / 5.36) ~ 0.01191.
    # Use rationals: w = 64/1000, h = 12/1000. area=768/1e6=7.68e-4, aspect=64/12=5.33.
    LRP_w0 = Fraction(64, 1000)
    LRP_h0 = Fraction(12, 1000)
    t0 = 101
    R = Fraction(536, 100)  # 5.36
    c0 = Fraction(77, 1000)  # 0.077
    print(f"  Initial: LRP=({float(LRP_w0)}, {float(LRP_h0)}), aspect={float(LRP_w0/LRP_h0)}")
    print(f"  area={float(LRP_w0*LRP_h0)}, t0={t0}, R={float(R)}, c0={float(c0)}")
    print(f"  c0 * t0 = {float(c0 * t0)}, R={float(R)}, R<=c0*t0? {R <= c0 * t0}")
    print(f"  Need 1/t0 = {1/t0:.6f} <= LRP_h={float(LRP_h0):.6f}? {Fraction(1,t0) <= LRP_h0}")
    print(f"  Need 1/(t0+1) = {1/(t0+1):.6f} <= LRP_w={float(LRP_w0):.6f}? {Fraction(1,t0+1) <= LRP_w0}")
    print()

    log, fp, fR, fF = simulate(c0, R, LRP_w0, LRP_h0, t0, K_max=10000,
                                 log_at=[0, 1, 10, 100, 1000, 5000, 10000])
    print(f"{'k':>6} {'t':>6} {'min_side':>12} {'1/t':>12} {'fits':>5} "
          f"{'aspect':>8} {'c_share':>14} {'c_share*t':>14} {'R':>8} "
          f"{'c_share*t-R':>14}")
    for L in log:
        if 'note' in L:
            print(f"  fit failed at k={L['k']}, t={L['t']}, LRP=({L['LRP_w']:.6f},{L['LRP_h']:.6f})")
            continue
        print(f"{L['k']:>6} {L['t']:>6} {L['min_side']:>12.6e} {L['one_over_t']:>12.6e} "
              f"{str(L['fits']):>5} {L['aspect']:>8.2f} "
              f"{L['c_share']:>14.6e} {L['c_share_t']:>14.6e} "
              f"{L['R']:>8.4f} {L['c_share_t_minus_R']:>14.6e}")
    print()
    print(f"  First k where c_share <= 0: {fp}")
    print(f"  First k where c_share * t < R: {fR}")
    print(f"  First k where min_side < 1/t (fit fails): {fF}")
    print()
    return log, fp, fR, fF


def analyze_decay(log_at_k, log_at_cum):
    """Analyze whether cumulative decay diverges as ~log(k) or stays bounded."""
    print("=" * 70)
    print("Cumulative decay growth rate:")
    print("=" * 70)
    print(f"{'k':>10} {'log(k)':>12} {'cum':>14} {'cum/log(k)':>14}")
    import math
    for k, c in zip(log_at_k, log_at_cum):
        if k <= 1:
            continue
        lk = math.log(k)
        print(f"{k:>10} {lk:>12.4f} {c:>14.6e} {c/lk:>14.6e}")


if __name__ == "__main__":
    log1, fp1, fR1, fF1 = test_synthetic()
    log2, fp2, fR2, fF2 = test_warmstart()

    # Analyze cumulative decay across the synthetic run
    print("\n--- Cumulative decay rates (synthetic) ---")
    ks = [L['k'] for L in log1 if 'note' not in L]
    cums = [L['cum'] for L in log1 if 'note' not in L]
    analyze_decay(ks, cums)

    print("\n--- Cumulative decay rates (warmstart) ---")
    ks = [L['k'] for L in log2 if 'note' not in L]
    cums = [L['cum'] for L in log2 if 'note' not in L]
    analyze_decay(ks, cums)

    # Diagnosis summary
    print("\n" + "=" * 70)
    print("DIAGNOSIS SUMMARY")
    print("=" * 70)
    for name, fp, fR, fF in [("synthetic", fp1, fR1, fF1),
                              ("warmstart", fp2, fR2, fF2)]:
        print(f"  [{name}]")
        print(f"    c_share <= 0 first at k = {fp}")
        print(f"    c_share*t < R first at k = {fR}")
        print(f"    fit fails first at k = {fF}")
