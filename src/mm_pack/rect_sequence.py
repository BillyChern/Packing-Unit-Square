"""The Moser sequence D_n = 1/n × 1/(n+1) and its tail / prefix areas."""

from __future__ import annotations
from fractions import Fraction
from typing import Tuple

F = Fraction


def D_dims(n: int) -> Tuple[F, F]:
    """Native dimensions (long, short) of D_n = 1/n × 1/(n+1)."""
    if n < 1:
        raise ValueError(f"n must be ≥ 1, got {n}")
    return F(1, n), F(1, n + 1)


def D_area(n: int) -> F:
    """Area 1/(n(n+1))."""
    return F(1, n * (n + 1))


def tail_area(t: int) -> F:
    """Σ_{n=t}^∞ 1/(n(n+1)) = 1/t."""
    return F(1, t)


def finite_tail_area(t: int, M: int) -> F:
    """Σ_{n=t}^{M-1} 1/(n(n+1)) = 1/t - 1/M (telescoping)."""
    if t < 1 or M < t:
        raise ValueError(f"need 1 ≤ t ≤ M, got t={t}, M={M}")
    return F(1, t) - F(1, M)


def prefix_area(N: int) -> F:
    """Σ_{n=1}^{N} 1/(n(n+1)) = N/(N+1)."""
    return F(N, N + 1)


def calibrated_active_width(t: int, gamma_num: int, gamma_den: int) -> Fraction:
    """a_t = 1/(t+1) + t^{-γ}, with γ = gamma_num / gamma_den.

    Computed exactly when γ is rational by raising to the gamma_num-th power
    and gamma_den-th root via integer arithmetic — but t^{-γ} is generally
    irrational for non-integer γ. We return a rational lower bound (one that
    is at most the true value) by replacing t^{-γ} with the nearest integer
    rational approximation derived from `t**gamma_num` and `t**gamma_den`.

    For the calibrated scheduler the *exact* width need only satisfy
    a_t ≥ 1/(t+1) + 1/t^γ; we compute a rational a_t ≤ true_a_t suitable for
    cutting (using a slightly *under*-estimated calibration thickness keeps the
    LRP at least as fat as the analysis demands).
    """
    if gamma_num <= 0 or gamma_den <= 0:
        raise ValueError("γ must be positive")
    # t^γ = t^(gamma_num/gamma_den)
    # We want the smallest rational ≤ 1/t^γ (so a_t under-estimates).
    # Using monotonicity: 1/t^γ ≥ 1/⌈t^γ⌉. Compute ⌈t^γ⌉ via integer arithmetic.
    # t^γ = (t^gamma_num)^(1/gamma_den). Compute m = t**gamma_num, then ceil m^(1/gamma_den).
    if gamma_num == gamma_den:
        # γ = 1 → t^γ = t exactly
        t_gamma_ceil = t
    else:
        m = t ** gamma_num
        # integer dᵗʰ root via binary search
        lo, hi = 1, m
        while lo < hi:
            mid = (lo + hi) // 2
            if mid ** gamma_den < m:
                lo = mid + 1
            else:
                hi = mid
        t_gamma_ceil = lo  # smallest integer with t_gamma_ceil^gamma_den ≥ m
    # 1/t^γ ≥ 1/t_gamma_ceil
    return Fraction(1, t + 1) + Fraction(1, t_gamma_ceil)


__all__ = [
    "D_dims",
    "D_area",
    "tail_area",
    "finite_tail_area",
    "prefix_area",
    "calibrated_active_width",
]
