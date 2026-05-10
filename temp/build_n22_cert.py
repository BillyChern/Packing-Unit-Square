"""Build a balanced cert at N=22 BSSF, satisfying ALL T_0 thresholds.

At N=22 (t=23): aspect = 63/32 = 1.9688, S_LRP * t = 0.4551.

Choose:
  c = S_LRP * t exactly = some Fraction (or 9/20 = 0.45)
  R = 8/3 (≥ φ²)
  η = 0 (drop ultra-thin slivers)
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from fractions import Fraction
from src.algorithms import MaxRectsPacker
from src.mm_pack.geometry import Rect, FreeBox, FreeBoxKind, PlacedRect
from src.mm_pack.rectangulate_fast import rectangulate_simplified_fast
from src.mm_pack.cellification import cellify_strip
from src.mm_pack.certificate import Certificate, write_certificate
from src.mm_pack.checker import check_certificate

F = Fraction


def build_cert(N: int):
    side = F(1)
    cont = Rect(F(0), F(0), side, side)
    packer = MaxRectsPacker(side, side)
    for n in range(1, N + 1):
        p = packer.place(n, allow_rotate=True, heuristic="BSSF")
        if p is None:
            raise RuntimeError(f"BSSF failed at n={n}")
    placed = [
        PlacedRect(n=p.k, x0=p.x, y0=p.y, rotated=p.rotated)
        for p in packer.placed
    ]
    free_rects = rectangulate_simplified_fast(cont, placed)
    if not free_rects:
        raise RuntimeError("no free rects")
    lrp_rect = max(free_rects, key=lambda r: (r.min_side, r.area))
    absorbers = []
    dropped = []
    for r in free_rects:
        if r is lrp_rect:
            continue
        if r.aspect > F(64):
            dropped.append(r)
        elif r.aspect > F(2):
            for c in cellify_strip(r):
                absorbers.append(FreeBox(rect=c, kind=FreeBoxKind.ABSORBER))
        else:
            absorbers.append(FreeBox(rect=r, kind=FreeBoxKind.ABSORBER))
    LRP = FreeBox(rect=lrp_rect, kind=FreeBoxKind.LRP)
    cert = Certificate(
        N=N+1,
        gamma_num=4, gamma_den=3,
        container=cont,
        placed=placed,
        LRP=LRP,
        normal_boxes=[],
        endpoint_boxes=[],
        absorbers=absorbers,
    )
    return cert, dropped


def verify_full(cert: Certificate, c: F, R: F, eta: F):
    s_lrp = cert.LRP.area
    aspect = cert.LRP.aspect
    t = cert.N
    p_ep = sum((b.semiperim for b in cert.endpoint_boxes), F(0))

    print(f"=== Cert: t = {t}, |placed| = {len(cert.placed)} ===")
    print(f"  LRP: area = {s_lrp} ({float(s_lrp):.6f}), aspect = {aspect} ({float(aspect):.6f})")
    print(f"  S_LRP * t = {s_lrp * t} = {float(s_lrp * t):.6f}")
    print(f"  Parameters: c = {c} ({float(c):.6f}), R = {R} ({float(R):.6f}), η = {eta}")

    # Lean conditions
    print()
    print("--- Lean conditions ---")
    lean_ok = True
    for name, ok in [
        ("c > 0", c > 0),
        ("R > 0", R > 0),
        ("R ≥ 1", R >= 1),
        ("(R-1)² ≥ R", (R-1)*(R-1) >= R),
        ("R ≤ c · t", R <= c*t),
        ("S_LRP · t ≥ c", s_lrp * t >= c),
        ("aspect ≤ R", aspect <= R),
        ("P_ep ≤ η", p_ep <= eta),
    ]:
        print(f"  [{'OK' if ok else 'FAIL'}] {name}")
        lean_ok = lean_ok and ok

    # Doc T_0 conditions
    T1 = R / (c * (1 - F(1)/R)**2)
    T2_lhs = F(t+1)**2 / F(t)
    T2_thresh = 4*R/c
    T3 = R / c
    T4 = c/R

    print()
    print("--- Doc T_0 conditions ---")
    doc_ok = True
    for name, ok in [
        (f"T1: t={t} ≥ R/(c(1-1/R)²)={float(T1):.3f}", t >= T1),
        (f"T2: (t+1)²/t={float(T2_lhs):.3f} ≥ 4R/c={float(T2_thresh):.3f}", T2_lhs >= T2_thresh),
        (f"T3: t={t} ≥ R/c={float(T3):.3f}", t >= T3),
        (f"T4: c/R={float(T4):.4f} ≥ 1/16={1/16:.4f}", T4 >= F(1, 16)),
    ]:
        print(f"  [{'OK' if ok else 'FAIL'}] {name}")
        doc_ok = doc_ok and ok

    rep = check_certificate(cert, c_LRP=c, R_aspect=R, eta_ep=eta)
    print()
    print(f"--- Internal checker ---")
    print(f"  ok = {rep.ok}")
    if not rep.ok:
        for e in rep.errors[:3]:
            print(f"    err: {e}")

    return lean_ok, doc_ok, rep.ok


if __name__ == "__main__":
    print("=" * 70)
    print("Approach: N=22 BSSF, use the actual S_LRP*t as c")
    print("=" * 70)
    cert, dropped = build_cert(22)
    print(f"Built. Dropped {len(dropped)} ultra-thin slivers.")
    print()

    # The actual S_LRP * t at N=22:
    s_lrp_t = cert.LRP.area * cert.N
    print(f"Actual S_LRP * t = {s_lrp_t} = {float(s_lrp_t):.6f}")
    # We pick c = floor of this rational with manageable denom, or just use the
    # exact value. Alternative: c = 9/20 = 0.45 (a nicer rational).
    # 9/20 ≤ 1093/2401 = 0.4552?
    # 9/20 = 0.45 < 0.4551 ✓
    c = F(9, 20)
    R = F(8, 3)
    eta = F(0)
    print(f"Trying (c={c}, R={R}, η={eta})...")
    print()
    lean_ok, doc_ok, check_ok = verify_full(cert, c, R, eta)
    print()
    print(f"=== Summary: Lean={lean_ok}, Doc={doc_ok}, Checker={check_ok} ===")

    if lean_ok and doc_ok and check_ok:
        out_path = f"/workspace/Packing/results/balanced_cert_N22.json"
        cert.claimed_bounds = {
            "c": str(c),
            "R": str(R),
            "eta": str(eta),
            "t": str(cert.N),
            "S_LRP_times_t": str(cert.LRP.area * cert.N),
            "LRP_aspect": str(cert.LRP.aspect),
        }
        write_certificate(cert, out_path)
        print(f"Saved cert to {out_path}")
    else:
        print()
        print("Trying alternate parameters...")
        # If doc fails, try varying c
        for c_test in [F(2, 5), F(4, 9), F(11, 25), F(45, 100)]:
            print(f"  c={c_test} ({float(c_test):.4f})")
            cert2, _ = build_cert(22)
            lean_ok2, doc_ok2, ck2 = verify_full(cert2, c_test, R, eta)
            print(f"    Result: Lean={lean_ok2}, Doc={doc_ok2}, Check={ck2}")
            if lean_ok2 and doc_ok2 and ck2:
                break
