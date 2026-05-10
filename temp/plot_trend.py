"""Visualize σ vs N progression — show how each successful prefix tightens the bound."""
import sys, os
sys.path.insert(0, "/workspace/Packing")
import json

# Collect achieved Ns
ns_achieved = []  # (N, heuristic)

for fn in os.listdir('/workspace/Packing/results'):
    if fn.startswith('full_') and fn.endswith('.json') and 'placements' not in fn:
        with open(f'/workspace/Packing/results/{fn}') as f:
            d = json.load(f)
        N = d.get('max_N_in_unit_square')
        h = d.get('heuristic')
        if N and h and d.get('verify_full_ok'):
            ns_achieved.append((N, h))

# Add fast_push results
for fn in os.listdir('/workspace/Packing/results'):
    if fn.startswith('fast_push_') and fn.endswith('.json'):
        with open(f'/workspace/Packing/results/{fn}') as f:
            d = json.load(f)
        N = d.get('max_N')
        h = d.get('heuristic')
        if N and h:
            ns_achieved.append((N, h))

# Plot ASCII
ns_achieved.sort()
print('N achieved (heuristic) → σ-bound (1+1/(N+1)):')
print('=' * 60)
for N, h in ns_achieved:
    sigma = 1 + 1/(N+1)
    print(f'  N={N:>7}  ({h:8})  σ ≤ {N+2}/{N+1} = {sigma:.10f}')

# Compare to literature
print()
print('Literature:')
print(f'  Jennings 1994: 133/132 = {133/132:.10f}')
print(f'  Bálint:        501/500 = {501/500:.10f}')
print()
print('Our improvements over Bálint 501/500:')
balint = 501/500
for N, h in ns_achieved:
    sigma = 1 + 1/(N+1)
    if sigma < balint:
        print(f'  N={N:>7} ({h:8}): {balint - sigma:.6e}')

# SVG for the trend
svg_w = 800
svg_h = 400
margin = 60
inner_w = svg_w - 2*margin
inner_h = svg_h - 2*margin
import math

import os
import json as J

def svg_log_trend(records, outpath):
    """records: list of (N, heuristic). Plot σ vs N."""
    Ns = [r[0] for r in records]
    if not Ns:
        return
    Nmin, Nmax = min(Ns), max(Ns)
    epsmin = 1/(Nmax + 1)
    epsmax = 1/(Nmin + 1)
    log_Nmin = math.log10(max(Nmin, 1))
    log_Nmax = math.log10(Nmax)
    log_emin = math.log10(epsmin)
    log_emax = math.log10(epsmax)

    def mapx(N):
        return margin + (math.log10(N) - log_Nmin) * inner_w / (log_Nmax - log_Nmin + 1e-9)

    def mapy(eps):
        return svg_h - margin - (math.log10(eps) - log_emin) * inner_h / (log_emax - log_emin + 1e-9)

    parts = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{svg_w}" height="{svg_h}" viewBox="0 0 {svg_w} {svg_h}">']
    parts.append(f'<rect x="0" y="0" width="{svg_w}" height="{svg_h}" fill="white" stroke="#333" stroke-width="1"/>')
    parts.append(f'<text x="{svg_w/2}" y="20" text-anchor="middle" font-family="serif" font-size="14">σ − 1 vs N (log-log) for Moser packing</text>')
    # Axes
    parts.append(f'<line x1="{margin}" y1="{margin}" x2="{margin}" y2="{svg_h-margin}" stroke="#333"/>')
    parts.append(f'<line x1="{margin}" y1="{svg_h-margin}" x2="{svg_w-margin}" y2="{svg_h-margin}" stroke="#333"/>')
    parts.append(f'<text x="{margin}" y="{svg_h-margin+30}" text-anchor="middle" font-family="serif" font-size="11">N</text>')
    parts.append(f'<text x="20" y="{svg_h/2}" font-family="serif" font-size="11">ε = σ − 1</text>')
    # Bálint
    bx = mapx(499)
    by = mapy(1/500)
    parts.append(f'<circle cx="{bx}" cy="{by}" r="4" fill="red"/>')
    parts.append(f'<text x="{bx+8}" y="{by+4}" font-family="serif" font-size="11" fill="red">Bálint 501/500</text>')
    # Jennings
    jx = mapx(132)
    jy = mapy(1/132)
    parts.append(f'<circle cx="{jx}" cy="{jy}" r="4" fill="orange"/>')
    parts.append(f'<text x="{jx+8}" y="{jy+4}" font-family="serif" font-size="11" fill="orange">Jennings 133/132</text>')
    # Our points
    for N, h in records:
        eps = 1/(N+1)
        x = mapx(N)
        y = mapy(eps)
        parts.append(f'<circle cx="{x}" cy="{y}" r="3" fill="steelblue"/>')
    # Theoretical (this work) line: ε = 1/(N+1)
    line_x = []
    line_y = []
    for k in range(int(log_Nmin*10), int(log_Nmax*10)+1):
        N = 10**(k/10)
        line_x.append(mapx(N))
        line_y.append(mapy(1/(N+1)))
    points = ' '.join(f'{x},{y}' for x,y in zip(line_x, line_y))
    parts.append(f'<polyline points="{points}" fill="none" stroke="steelblue" stroke-width="1" stroke-dasharray="4,2"/>')
    # Tick labels
    for log_n in range(int(log_Nmin), int(log_Nmax)+1):
        N = 10**log_n
        x = mapx(N)
        parts.append(f'<line x1="{x}" y1="{svg_h-margin}" x2="{x}" y2="{svg_h-margin+5}" stroke="#333"/>')
        parts.append(f'<text x="{x}" y="{svg_h-margin+18}" text-anchor="middle" font-family="serif" font-size="10">10^{log_n}</text>')
    for log_e in range(int(log_emin), int(log_emax)+1):
        eps = 10**log_e
        y = mapy(eps)
        parts.append(f'<line x1="{margin-5}" y1="{y}" x2="{margin}" y2="{y}" stroke="#333"/>')
        parts.append(f'<text x="{margin-8}" y="{y+4}" text-anchor="end" font-family="serif" font-size="10">10^{log_e}</text>')
    parts.append('</svg>')
    with open(outpath, 'w') as f:
        f.write(''.join(parts))


svg_log_trend(ns_achieved + [(499, 'Bálint'), (132, 'Jennings')], '/workspace/Packing/figures/sigma_vs_N.svg')
print('\nSaved /workspace/Packing/figures/sigma_vs_N.svg')
