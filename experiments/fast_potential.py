"""Fast resumable generator for Kritzinger's sequence via the potential rule.

Rule (equivalent to the greedy step; see the paper, Section 2): with old points sorted y_1 < ... < y_N, M = N + 1 and
P_j = sum_{k<=j} (k/M - y_k) (P_0 = 0), insert x = (2j+1)/(2M) at the least j
maximising P_j. EMPIRICAL: P is computed in floats; every index within TOL of
the maximum is compared exactly (Fractions over the index range between
candidates), so ties are decided exactly unless the float error exceeds TOL.

Also records Steinerberger's integrated discrepancy
G_N = max_x |int_0^x (#{x_k <= y} - N y) dy| every STRIDE steps.

Usage (resumes if OUT.seq exists):
  nice -n 19 python3 experiments/fast_potential.py NMAX OUT [STRIDE] [MAXSEC]
Stops cleanly after MAXSEC seconds (default 480) so every chunk stays < 10 min.
"""
import os
import sys
import time
from fractions import Fraction as F

import numpy as np

TOL = 1e-9


def gstats(y, n):
    cs = np.concatenate([[0.0], np.cumsum(y)])
    xs = np.concatenate([y, np.arange(n + 1) / n])
    cnt = np.searchsorted(y, xs, side="right")
    g = cnt * xs - cs[cnt] - n * xs * xs / 2
    return g.max(), g.min()


def main(nmax, out, stride=10, maxsec=480):
    t0 = time.time()
    seqp, stp = out + ".seq", out + ".gstats.csv"
    if os.path.exists(seqp):
        rows = [tuple(map(int, l.split())) for l in open(seqp)]
    else:
        rows = [(1, 0)]
        open(seqp, "w").write("1 0\n")
        open(stp, "w").write("N,maxG,minG,near_ties,exact_ties,max_tie_range\n")
    # exact values kept as (numerator, n) pairs: x = (2i+1)/(2n)
    order = sorted(rows, key=lambda r: (2 * r[1] + 1) / (2 * r[0]))
    y = np.array([(2 * i + 1) / (2 * n) for n, i in order])
    yex = [(n, i) for n, i in order]
    n = len(rows)
    near = exact = maxrange = 0
    seqf, stf = open(seqp, "a"), open(stp, "a")
    while n < nmax and time.time() - t0 < maxsec:
        m = n + 1
        p = np.concatenate([[0.0], np.cumsum(np.arange(1, n + 1) / m - y)])
        pmax = p.max()
        cand = np.where(p >= pmax - TOL)[0]
        if len(cand) == 1:
            j = int(cand[0])
        else:
            near += 1
            a0 = int(cand[0])
            vals, val, prev = [(F(0), a0)], F(0), a0
            for c in map(int, cand[1:]):
                maxrange = max(maxrange, c - a0)
                for k in range(prev + 1, c + 1):          # P_c - P_a0, exactly
                    nn, ii = yex[k - 1]
                    val += F(k, m) - F(2 * ii + 1, 2 * nn)
                prev = c
                vals.append((val, c))
            top = max(v for v, _ in vals)
            winners = [c for v, c in vals if v == top]
            j = min(winners)
            exact += len(winners) > 1
        x = (2 * j + 1) / (2 * m)
        y = np.insert(y, j, x)
        yex.insert(j, (m, j))
        seqf.write(f"{m} {j}\n")
        n = m
        if n % stride == 0 or n == nmax:
            hi, lo = gstats(y, n)
            stf.write(f"{n},{hi:.6f},{lo:.6f},{near},{exact},{maxrange}\n")
    seqf.close()
    stf.close()
    print(f"reached N={n} in {time.time() - t0:.1f}s; near_ties={near} maxrange={maxrange}")


if __name__ == "__main__":
    a = sys.argv
    main(int(a[1]), a[2], int(a[3]) if len(a) > 3 else 10, float(a[4]) if len(a) > 4 else 480)
