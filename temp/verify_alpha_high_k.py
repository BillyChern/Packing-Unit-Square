"""Trace α (argmax-min-side area share) at high k for BSSF."""
import sys
sys.set_int_max_str_digits(0)
sys.path.insert(0, "/workspace/Packing")
from fractions import Fraction as F
from src.fast_packer import FastMaxRectsPacker
import time

p = FastMaxRectsPacker(W=F(1), H=F(1))
p.place_explicit(1, F(0), F(0), rotated=False)

t0 = time.time()
print(f"{'k':>6} {'α_argmin':>9} {'aspect':>8} {'ρ':>8}")
for k in range(2, 30001):
    p.place(k, allow_rotate=True, heuristic='BSSF')
    if k in (100, 500, 1000, 2000, 5000, 10000, 15000, 20000, 25000, 30000):
        # Two notions of fattest
        f_by_min = max(p.free, key=lambda fr: min(fr.w, fr.h))
        ms_m = float(min(f_by_min.w, f_by_min.h))
        asp_m = float(max(f_by_min.w, f_by_min.h)) / ms_m if ms_m > 0 else float('inf')
        area_m = float(f_by_min.w * f_by_min.h)
        alpha_m = area_m / (1/(k+1))
        rho = ms_m * (k+1)
        elapsed = time.time() - t0
        print(f"{k:>6} {alpha_m:>9.4f} {asp_m:>8.3f} {rho:>8.2f}  t={elapsed:.0f}s")
