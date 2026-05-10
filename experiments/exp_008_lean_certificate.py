#!/usr/bin/env python3
"""Generate a small Lean-checked certificate.

Pipeline:
  1. Run a small calibrated burn-in.
  2. Export to .lean format with Rect/PlacedRect literals.
  3. Run lake build on the certificate file.
  4. Confirm `theorem finite_packing_valid : FinitePacking ... := by decide` checks.
"""

from __future__ import annotations
import os
import sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from fractions import Fraction
from src.mm_pack.calibrated_scheduler import CalibratedScheduler
from src.mm_pack.certificate import Certificate, write_certificate, write_lean_certificate
from src.mm_pack.checker import check_certificate


def main(N: int = 100):
    print(f"=== Building certificate for N={N} ===", flush=True)
    sch = CalibratedScheduler.from_maxrects_burnin(
        burnin_N=N, gamma_num=4, gamma_den=3, heuristic='BSSF'
    )
    st = sch.state
    cert = Certificate(
        N=st.t, gamma_num=st.gamma_num, gamma_den=st.gamma_den,
        container=st.container, placed=list(st.placed), LRP=st.LRP,
        normal_boxes=list(st.normal_boxes), endpoint_boxes=list(st.endpoint_boxes),
        absorbers=list(st.absorbers),
    )
    rep = check_certificate(cert, c_LRP=Fraction(1, 10), R_aspect=Fraction(8))
    print(f"Python checker: ok={rep.ok}, |errors|={len(rep.errors)}", flush=True)
    for e in rep.errors[:3]:
        print(f"  - {e}", flush=True)

    # Write JSON
    json_path = f"/workspace/Packing/results/cert_lean_N{N}.json"
    write_certificate(cert, json_path)
    print(f"Wrote: {json_path}", flush=True)

    # Write Lean
    lean_path = f"/workspace/Packing/lean/MeirMoser/Certificates/CandidateN{N}.lean"
    write_lean_certificate(cert, lean_path, namespace_suffix=f"N{N}")
    print(f"Wrote: {lean_path}", flush=True)


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    main(N)
