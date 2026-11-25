"""Interval version of the envelope (EMPIRICAL). For each N compute
  c_up(N) = max_{s<t} [G(t) - G(s) - (t-s)/2]   (integrated surplus on [s,t])
  c_dn(N) = max_{s<t} [G(s) - G(t) - (t-s)/2]   (integrated deficit on [s,t])
(A) is the case s = 0 of c_up <= 0; (C) is the case t = 1 of c_dn <= 0.
If c_dn <= c for all N then G(s) >= G(1) - (1-s)/2 - c >= -1 - c (a lower bound).
Usage: python3 experiments/interval_slack.py SEQ NMAX STRIDE_AFTER_3000
"""
import bisect
import sys

import numpy as np

idx = [int(l.split()[1]) for l in open(sys.argv[1])]
nmax, stride = int(sys.argv[2]), int(sys.argv[3])
pts, worst_up, worst_dn = [], (-9, 0), (-9, 0)
for n in range(1, nmax + 1):
    bisect.insort(pts, (2 * idx[n - 1] + 1) / (2 * n))
    if n > 3000 and n % stride:
        continue
    y = np.array(pts)
    j = np.arange(n + 1)
    t = np.unique(np.clip(np.concatenate([y, (j - .5) / n, j / n, (j + .5) / n, [0, 1]]), 0, 1))
    cs = np.concatenate([[0.0], np.cumsum(y)])
    c = np.searchsorted(y, t, side="right")
    g = c * t - cs[c] - n * t * t / 2
    u, v = g - t / 2, g + t / 2
    cup = (u - np.minimum.accumulate(u)).max()
    cdn = (np.maximum.accumulate(v) - v).max()
    if cup > worst_up[0]:
        worst_up = (cup, n)
    if cdn > worst_dn[0]:
        worst_dn = (cdn, n)
    if n in (10, 100, 1000, 3000, 10000, 30000):
        print(f"N={n}: c_up={cup:.4f} c_dn={cdn:.4f}  running worst up {worst_up[0]:.4f}@{worst_up[1]} dn {worst_dn[0]:.4f}@{worst_dn[1]}")
print(f"FINAL N<={nmax}: worst c_up {worst_up[0]:.4f} at N={worst_up[1]}, worst c_dn {worst_dn[0]:.4f} at N={worst_dn[1]}")
