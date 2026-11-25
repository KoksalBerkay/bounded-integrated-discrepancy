"""Every-N statistics of the integrated discrepancy G_N (EMPIRICAL, floats).

Replays a .seq file (lines "N i": x_N = (2i+1)/(2N)) and, for every N in
[START, END), computes in O(N):
  maxG, minG and where they occur;  max H and mean H for H = G + t(1-t)/2;
  E = int_0^1 D_N(t)^2 dt (squared L2 discrepancy).
Local maxima of G lie at grid points k/N with y_k <= k/N < y_{k+1}; local
minima at the points y_j; plus t = 0 and t = 1. (D = G' decreases with slope
-N between points and jumps by +1 at each point.)

Writes rows with a new record of max G (record=1), of min G (record=2) or both (3),
and every 1000th N, to OUT. Values printed with 6 decimals (CSV) or 9 (summary).
Usage: nice -n 19 python3 experiments/records.py SEQ START END OUT [MAXSEC]
Stops after MAXSEC seconds (default 420) and prints the next START.
"""
import bisect
import sys
import time

import numpy as np


def stats(y, n):
    k = np.arange(1, n + 1)
    cs = np.cumsum(y)
    # local minima candidates: at the points y_j (count = j)
    gpts = k * y - cs - n * y * y / 2
    # local maxima candidates: t = k/N with y_k <= k/N < y_{k+1}
    t = k / n
    ynext = np.append(y[1:], 1.0)
    ok = (y <= t) & (t < ynext)
    ggrid = np.where(ok, k * k / (2 * n) - cs, -np.inf)
    g1 = n / 2 - cs[-1]
    gmax = max(0.0, g1, ggrid.max())
    gmin = min(0.0, g1, gpts.min())
    tmax = float(t[np.argmax(ggrid)]) if ggrid.max() >= max(0.0, g1) else (1.0 if g1 > 0 else 0.0)
    tmin = float(y[np.argmin(gpts)]) if gpts.min() <= min(0.0, g1) else (1.0 if g1 < 0 else 0.0)
    # H = G + psi; its maximum is at some c_j = (2j+1)/(2M); P_j = H(c_j) - 1/(8M)
    m = n + 1
    p = np.concatenate([[0.0], np.cumsum(k / m - y)])
    hmax = p.max() + 1 / (8 * m)
    # mean of G: int_0^1 G = sum_k (1-y_k)^2/2 - n/6 ; mean of psi = 1/12
    gmean = float(((1 - y) ** 2).sum() / 2 - n / 6)
    hmean = gmean + 1 / 12
    # E = int D^2: on [y_j, y_{j+1}] D = j - n t
    a = np.concatenate([[0.0], y])
    b = np.concatenate([y, [1.0]])
    j = np.arange(0, n + 1)
    e = float((((j - n * a) ** 3 - (j - n * b) ** 3) / (3 * n)).sum())
    return gmax, gmin, tmax, tmin, hmax, hmean, e


def main(seq, start, end, out, maxsec=420):
    t0 = time.time()
    idx = [int(l.split()[1]) for l in open(seq)]
    end = min(end, len(idx) + 1)
    pts = sorted((2 * idx[q] + 1) / (2 * (q + 1)) for q in range(start - 1))
    best_hi, best_lo = 0.0, 0.0     # separate records for max G and min G
    try:
        for line in open(out):
            if line[0].isdigit():
                best_hi = max(best_hi, float(line.split(",")[1]))
                best_lo = min(best_lo, float(line.split(",")[2]))
    except FileNotFoundError:
        open(out, "w").write("N,maxG,minG,tmax,tmin,maxH,meanH,E,record\n")
    f = open(out, "a")
    n = start - 1
    while n + 1 < end and time.time() - t0 < maxsec:
        n += 1
        bisect.insort(pts, (2 * idx[n - 1] + 1) / (2 * n))
        s = stats(np.array(pts), n)
        rec = 0
        if s[0] > best_hi:
            best_hi, rec = s[0], 1          # new record for max G
        if s[1] < best_lo:
            best_lo, rec = s[1], rec + 2    # new record for min G (2, or 3 if both)
        if rec or n % 1000 == 0:
            f.write(f"{n},{s[0]:.6f},{s[1]:.6f},{s[2]:.6f},{s[3]:.6f},"
                    f"{s[4]:.6f},{s[5]:.6f},{s[6]:.4f},{rec}\n")
    f.close()
    print(f"done through N={n}; next START={n + 1}; max G={best_hi:.9f}; min G={best_lo:.9f}; {time.time() - t0:.0f}s")


if __name__ == "__main__":
    a = sys.argv
    main(a[1], int(a[2]), int(a[3]), a[4], float(a[5]) if len(a) > 5 else 420)
