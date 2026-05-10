"""Verify Conjecture A: at every step k, the fattest FR holds α(k) ≥ α₀ of total free area."""
import sys
sys.set_int_max_str_digits(0)
sys.path.insert(0, "/workspace/Packing")
from fractions import Fraction as F
from src.fast_packer import FastMaxRectsPacker

p = FastMaxRectsPacker(W=F(1), H=F(1))
p.place_explicit(1, F(0), F(0), rotated=False)

print(f"{'k':>6} {'|F|':>5} {'fattest_area':>14} {'total_free':>14} {'α=fa/tf*(k+1)':>15} {'aspect':>8} {'min_side·(k+1)':>16}")
for k in range(2, 5001):
    p.place(k, allow_rotate=True, heuristic='BSSF')
    if k in (2, 3, 4, 5, 10, 20, 50, 100, 200, 500, 1000, 2000, 5000):
        # Two candidate "fattest" FRs:
        f_by_area = max(p.free, key=lambda fr: fr.w * fr.h)
        f_by_min  = max(p.free, key=lambda fr: min(fr.w, fr.h))
        fa_a = float(f_by_area.w * f_by_area.h)
        fa_m = float(f_by_min.w * f_by_min.h)
        total_unocc = 1/(k+1)
        alpha_a = fa_a / total_unocc
        alpha_m = fa_m / total_unocc
        ms_a = float(min(f_by_area.w, f_by_area.h))
        ms_m = float(min(f_by_min.w, f_by_min.h))
        asp_a = float(max(f_by_area.w, f_by_area.h)) / ms_a if ms_a > 0 else float('inf')
        asp_m = float(max(f_by_min.w, f_by_min.h)) / ms_m if ms_m > 0 else float('inf')
        print(f"{k:>6} |F|={len(p.free):>4}  "
              f"area-max:α={alpha_a:.3f} asp={asp_a:.2f} ms·k={ms_a*(k+1):.2f}  | "
              f"min-max:α={alpha_m:.3f} asp={asp_m:.2f} ms·k={ms_m*(k+1):.2f}")
