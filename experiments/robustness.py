"""Greedy L2 steps from random initial sets: does G return to [-1/2, 1/2]?
(EMPIRICAL, floats; ties broken by least index.)
For each run: k uniform random initial points, then greedy steps to NMAX.
Reports max/min of G over N in [NMAX/10, NMAX] (after the transient) and the
last N at which |G| > 1/2.
Usage: nice -n 19 python3 experiments/robustness.py NMAX RUNS K1,K2,... SEED
"""
import sys

import numpy as np


def gext(y):
    n = len(y)
    cs = np.concatenate([[0.0], np.cumsum(y)])
    xs = np.concatenate([y, np.arange(n + 1) / n])
    c = np.searchsorted(y, xs, side="right")
    g = c * xs - cs[c] - n * xs * xs / 2
    return g.max(), g.min()


nmax, runs = int(sys.argv[1]), int(sys.argv[2])
ks = [int(k) for k in sys.argv[3].split(",")]
rng = np.random.default_rng(int(sys.argv[4]))
for k in ks:
    for r in range(runs):
        y = np.sort(rng.random(k))
        hi, lo, last_bad = -9.0, 9.0, 0
        g0 = gext(y)
        for n in range(k, nmax):
            m = n + 1
            p = np.concatenate([[0.0], np.cumsum(np.arange(1, n + 1) / m - y)])
            j = int(np.argmax(p))
            y = np.insert(y, j, (2 * j + 1) / (2 * m))
            if m % 5 == 0:
                a, b = gext(y)
                if max(a, -b) > 0.5:
                    last_bad = m
                if m >= nmax // 10:
                    hi, lo = max(hi, a), min(lo, b)
        print(f"k={k:3d} run={r} initial G in [{g0[1]:+.3f},{g0[0]:+.3f}]  "
              f"N in [{nmax//10},{nmax}]: max G {hi:+.4f}, min G {lo:+.4f}; last |G|>1/2 at N={last_bad}")
