"""Numerical statements of the second paper (EMPIRICAL; floating point).

For Kritzinger's sequence (data/kritzinger_30000.seq) and every N <= NMAX:
  1. the unnormalised star discrepancy D*_N = sup_t |#{k : x_k < t} - N t|,
     the maximum of D*_N / log N over 1000 <= N <= NMAX, and D*_NMAX exactly;
  2. the lower envelope G_N(t) >= -t + t^2/2 (checked at all breakpoints and
     grid points t = j/N, (j+1/2)/N; G_N is piecewise quadratic).
Usage: python3 experiments/paper2_numerics.py data/kritzinger_30000.seq 30000
"""
import bisect
import math
import sys
from fractions import Fraction as F

import numpy as np

rows = [tuple(map(int, l.split())) for l in open(sys.argv[1])]
nmax = int(sys.argv[2])
pts, best, env = [], (0.0, 0), np.inf
for n, (m, i) in enumerate(rows[:nmax], 1):
    bisect.insort(pts, (2 * i + 1) / (2 * m))
    y = np.array(pts)
    k = np.arange(1, n + 1)
    d = max((k - n * y).max(), (n * y - (k - 1)).max())
    if n >= 1000 and d / math.log(n) > best[0]:
        best = (d / math.log(n), n)
    j = np.arange(n + 1)
    t = np.unique(np.clip(np.concatenate([y, j / n, (j + 0.5) / n]), 0, 1))
    cs = np.concatenate([[0.0], np.cumsum(y)])
    c = np.searchsorted(y, t, side="right")
    g = c * t - cs[c] - n * t * t / 2
    env = min(env, (g + t - t * t / 2).min())
print(f"max D*_N/log N over 1000 <= N <= {nmax}: {best[0]:.4f} at N = {best[1]}")
ys = sorted(F(2 * i + 1, 2 * m) for m, i in rows[:nmax])
n = len(ys)
dex = max(max(F(k + 1) - n * y, n * y - k) for k, y in enumerate(ys))
print(f"D*_{n} = {dex} = {float(dex):.6f} = {float(dex) / math.log(n):.4f} log N")
print(f"min over N <= {nmax}, t of G_N(t) + t - t^2/2: {env:.6f} (>= 0: envelope holds)")
