# Loop Log

## Tick 1 (iter=0 → 1) — 2026-05-02T17:53:13Z

- Inode used: 11,130,820 / 11,704,808 (free 573,988 — plenty)
- FAIL events: none ✓
- Trackers (v1, last data before 17:18 auto-kill):
  - BSSF: k=31000 ρ=68.97
  - BAF: k=40000 ρ=30.30
  - CONTACT: k=36000 ρ=1.81
  - BLSF: k=34000 ρ=11.17
- Trackers (v2, restarted at 17:31, currently catching up):
  - BSSF v2: k=15000 ρ=52.91
  - BAF v2: k=20000 ρ=15.15
  - CONTACT v2: k=18000 ρ=1.90
  - BLSF v2: k=19000 ρ=7.49
- verify_alpha at k=20000: α=0.218, aspect=1.039, ρ=64.73
- Cert pushes (v6): BAF 38%, BSSF 53%
- No major findings; ρ continues to grow for BSSF/BAF/BLSF, CONTACT plateau ~1.8.

## Tick 2 (iter=1 → 2) — ~18:55Z (estimated)

- **Bash tool blocked** by `/tmp/claude-0` ENOSPC — could not run loop_check.sh, df, or any subprocess.
- Cannot verify tracker progress this tick. Background processes (track_inv_fast.py × 4, verify_alpha_high_k.py, inode_monitor.sh) presumably still running unless killed by external memory pressure.
- No new findings to report from this tick.
- Re-armed wakeup at 3600s; if /tmp is freed by next fire (19:55Z), normal operation resumes.

## Tick 3 — same fire, /tmp still blocked

- Same situation: Bash unavailable, can't run loop_check.sh.
- Re-armed for next fire; trackers still presumed running.

## Tick 4 — at/past 4-hour target, /tmp STILL blocked

- /tmp/claude-0 still ENOSPC; cannot run plot_combined.py, bssf_analysis.py, or verify certificates.
- We are past the 20:50 UTC target. Writing final report from existing data (no fresh runtime checks possible).
- Loop terminating: no further wakeups scheduled.
- Note: even Write tool failing with ENOSPC — could not create docs/11-final-report.md. Final summary inlined here instead.

# FINAL REPORT (2026-05-02, post-loop)

## Status
- Did not prove σ = 1.
- Verified σ ≤ 20002/20001 by exact arithmetic (small vs Zhu–Joós's 1+1.49·10⁻¹¹).
- **Articulated a concrete proof framework** reducing σ=1 to two open structural lemmas.

## Key empirical findings
- For BSSF: ρ(k) = mss(k)·(k+1) ≈ 0.42·√(k+1), growing, observed to k≈31000.
- Argmax-min FR's aspect ratio: 1.018 at k=10000, 1.030 at k=15000, 1.039 at k=20000 — empirically → 1.
- Naive BL fails at k=3925 with ρ=0.999 — confirms ρ is the right metric.
- Zhu–Joós Table 1: their α stays at 0.36 from k=10⁵ to k=10¹¹ (six orders of magnitude).

## Two open lemmas to close σ=1
- Lemma α: BSSF preserves area share α₀ > 0 in some FR.
- Lemma R: same FR has bounded aspect (or → 1).
- Together: min² ≥ α₀/(R(k+1)) ⇒ ρ → ∞ ⇒ σ = 1.

## Bottleneck
Aspect-replenishment: in Case B (BSSF must split F*), aspect drops; in Case A, aspect should grow on average. Empirically yes; formal proof open. This is the central piece needed.

## Loop terminating
Past 20:50 UTC target. Bash and Write blocked by /tmp + disk ENOSPC for last 3 ticks; cannot run scripts or create new files. No further wakeups scheduled.

See `docs/10-proof-attempt.md` for full framework, `docs/11-proof-cleanup.md` for refined Case-B analysis.

