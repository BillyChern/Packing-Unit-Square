#!/usr/bin/env python3
"""γ-sweep + burn-in N-sweep for the calibrated framework.

For each (N, γ) ∈ N_grid × γ_grid:
  1. Run MaxRects burn-in to N (BSSF heuristic).
  2. Convert to calibrated state (LRP = argmax-min-side rect; absorbers).
  3. Compute the 4 GoodTailState invariants.
  4. Write a JSON certificate.

Output: results/calibrated_sweep.json + per-(N,γ) certificate JSONs.
"""

from __future__ import annotations
import sys, os, time, json
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from fractions import Fraction
from src.mm_pack.calibrated_scheduler import CalibratedScheduler
from src.mm_pack.certificate import Certificate, write_certificate
from src.mm_pack.checker import check_certificate

GAMMA_LIST = [
    (6, 5),    # 1.20
    (5, 4),    # 1.25
    (4, 3),    # 4/3 ≈ 1.333
    (7, 5),    # 1.40
]

N_LIST = [200, 500, 1000, 2000]


def run_one(N: int, gamma_num: int, gamma_den: int) -> dict:
    print(f"  N={N}, γ={gamma_num}/{gamma_den}", flush=True)
    t0 = time.time()
    sch = CalibratedScheduler.from_maxrects_burnin(
        burnin_N=N, gamma_num=gamma_num, gamma_den=gamma_den, heuristic='BSSF'
    )
    elapsed = time.time() - t0
    st = sch.state
    cert = Certificate(
        N=st.t, gamma_num=st.gamma_num, gamma_den=st.gamma_den,
        container=st.container, placed=list(st.placed), LRP=st.LRP,
        normal_boxes=list(st.normal_boxes), endpoint_boxes=list(st.endpoint_boxes),
        absorbers=list(st.absorbers),
    )
    rep = check_certificate(cert, c_LRP=Fraction(1, 10), R_aspect=Fraction(8))
    out_path = f"/workspace/Packing/results/calibrated_N{N}_gamma_{gamma_num}_{gamma_den}.json"
    write_certificate(cert, out_path)
    s_lrp = float(st.LRP.area * N) if st.LRP else 0
    aspect = float(st.LRP.aspect) if (st.LRP and st.LRP.area > 0) else 0
    p_ep_str = rep.bounds.get('P_ep', '0')
    p_ep = float(Fraction(p_ep_str)) if isinstance(p_ep_str, str) else float(p_ep_str)
    return {
        "N": N,
        "gamma_num": gamma_num,
        "gamma_den": gamma_den,
        "elapsed_s": elapsed,
        "n_placed": len(st.placed),
        "S_LRP_over_tail": s_lrp,
        "LRP_aspect": aspect,
        "P_ep": p_ep,
        "n_normal": len(st.normal_boxes),
        "n_endpoint": len(st.endpoint_boxes),
        "n_absorber": len(st.absorbers),
        "ok": rep.ok,
        "errors": rep.errors[:5],
        "cert_path": out_path,
    }


def main():
    print(f"=== Calibrated γ-sweep: γ ∈ {GAMMA_LIST}, N ∈ {N_LIST} ===", flush=True)
    results = []
    for N in N_LIST:
        for gn, gd in GAMMA_LIST:
            res = run_one(N, gn, gd)
            results.append(res)
            print(f"    [{res['elapsed_s']:6.2f}s] S_LRP*N={res['S_LRP_over_tail']:.4f} "
                  f"asp={res['LRP_aspect']:.3f} P_ep={res['P_ep']:.4f} ok={res['ok']}", flush=True)
    os.makedirs("/workspace/Packing/results", exist_ok=True)
    with open("/workspace/Packing/results/calibrated_sweep.json", "w") as f:
        json.dump(results, f, indent=2)
    print("=== DONE ===", flush=True)
    # Summary
    print()
    print(f"{'N':>5} {'γ':>10} {'time':>6} {'S_LRP*N':>9} {'aspect':>7} {'P_ep':>9} ok")
    for r in results:
        gamma_str = f"{r['gamma_num']}/{r['gamma_den']}"
        print(f"{r['N']:>5} {gamma_str:>10} {r['elapsed_s']:>6.2f} {r['S_LRP_over_tail']:>9.4f} "
              f"{r['LRP_aspect']:>7.3f} {r['P_ep']:>9.4f} {r['ok']}")


if __name__ == "__main__":
    main()
