"""Generate Kritzinger's greedy sequence and record regularity statistics.

Exploration code (EMPIRICAL only, not a verifier). Candidates come from
Kritzinger's Theorem 2: x_{N+1} = (2i+1)/(2(N+1)). The objective is evaluated
in floating point; every candidate within TOL of the minimum is re-evaluated
in exact rational arithmetic, so ties and near-ties are decided exactly.

Usage: nice -n 19 python3 experiments/kritzinger.py NMAX [OUTPREFIX]
Writes OUTPREFIX.seq (one line per term: N i, meaning x_N = (2i+1)/(2N)) and
OUTPREFIX.stats.csv (N, N*D_N, N*maxgap, N*mingap, chosen-gap rank,
cumulative steps whose point did not enter a largest gap, ties).
"""
import bisect
import sys
from fractions import Fraction as F

import numpy as np

TOL = 1e-7


def f_exact(pts, x):
    n = len(pts)
    return -2 * sum(max(p, x) for p in pts) + (n + 1) * x * x - x


def run(nmax, out):
    pts = [F(1, 2)]
    srt = [0.5]
    near_ties = exact_ties = nonlargest = 0
    seq = open(out + ".seq", "w")
    st = open(out + ".stats.csv", "w")
    seq.write("1 0\n")
    st.write("N,ND,Nmaxgap,Nmingap,gap_rank,steps_not_largest_gap,near_ties,exact_ties\n")
    for n in range(1, nmax):
        m = n + 1
        a = np.array(srt)
        c = (2 * np.arange(m) + 1) / (2 * m)
        cs = np.concatenate([[0.0], np.cumsum(a)])
        k = np.searchsorted(a, c, side="right")
        val = -2 * ((cs[-1] - cs[k]) + c * k) + m * c * c - c
        cand = np.where(val <= val.min() + TOL)[0]
        if len(cand) > 1:
            near_ties += 1
            ex = [(f_exact(pts, F(2 * int(i) + 1, 2 * m)), int(i)) for i in cand]
            best = min(e[0] for e in ex)
            winners = [i for v, i in ex if v == best]
            exact_ties += len(winners) > 1
            i = min(winners)
        else:
            i = int(cand[0])
        x = F(2 * i + 1, 2 * m)
        # rank of the gap that receives x, among gaps before insertion (0 = largest)
        g = np.diff(np.concatenate([[0.0], a, [1.0]]))
        j = bisect.bisect_left(srt, float(x))
        rank = int((g > g[j] + 1e-15).sum())
        nonlargest += rank > 0
        pts.append(x)
        bisect.insort(srt, float(x))
        seq.write(f"{m} {i}\n")
        if m % 100 == 0 or m == nmax:
            b = np.array(srt)
            idx = np.arange(1, m + 1)
            d = max(np.max(idx - m * b), np.max(m * b - (idx - 1)))
            gaps = np.diff(np.concatenate([[0.0], b, [1.0]]))
            st.write(f"{m},{d:.6f},{gaps.max()*m:.6f},{gaps[1:-1].min()*m:.6f},"
                     f"{rank},{nonlargest},{near_ties},{exact_ties}\n")
    seq.close()
    st.close()


if __name__ == "__main__":
    run(int(sys.argv[1]), sys.argv[2] if len(sys.argv) > 2 else f"data/kritzinger_{sys.argv[1]}")
