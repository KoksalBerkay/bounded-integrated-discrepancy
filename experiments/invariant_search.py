"""Counterexample-guided search for inductive lower invariants (EMPIRICAL).

A candidate invariant I is *inductive* if every point set whose G satisfies
I (together with the proved upper envelope A, C) still satisfies I after one
greedy step. Real Kritzinger states satisfying I prove nothing; we search for
arbitrary point sets in [0,1] that satisfy the hypotheses but break I after
one step (simulated annealing on point positions).

Margins (>= 0 means satisfied), all exact up to float rounding because each
quantity is piecewise quadratic and we evaluate at all its critical points:
  A : t/2 - G(t)                         C : G(1) + (1-t)/2 - G(t)
  L1: G(t) - (-t + t^2/2)                L1m (mirror): G(t) - G(1) + (1-t^2)/2
  L2: G(t) + 1/2
Usage: python3 experiments/invariant_search.py CAND NMIN NMAX ITERS SEED
  CAND: comma list of lower candidates used as hypotheses AND conclusion,
        e.g. L1  or  L1,L1m  or  L2
Optional 6th/7th/8th args: DBOUND ('-' for none), GAPS (1 = min gap >= 1/(2N)), SLACK c for IU/ID
(interval family: |G(t)-G(s)| <= |t-s|/2 + c).
"""
import sys

import numpy as np


def gvals(y, t):
    n = len(y)
    cs = np.concatenate([[0.0], np.cumsum(y)])
    c = np.searchsorted(y, t, side="right")
    return c * t - cs[c] - n * t * t / 2


def crit(y):
    """Superset of critical points of all margins: points, endpoints, and
    t = (j + s)/N in each gap for s in {-1/2, 0, 1/2}."""
    n = len(y)
    j = np.arange(n + 1)
    extra = np.concatenate([(j - 0.5) / n, j / n, (j + 0.5) / n])
    t = np.concatenate([y, extra, [0.0, 1.0]])
    return np.clip(t, 0.0, 1.0)


def margins(y):
    t = crit(y)
    g = gvals(y, t)
    g1 = gvals(y, np.array([1.0]))[0]
    ts = np.argsort(t, kind="stable")
    tt, gg = t[ts], g[ts]
    u, v = gg - tt / 2, gg + tt / 2
    c_up = (u - np.minimum.accumulate(u)).max()
    c_dn = (np.maximum.accumulate(v) - v).max()
    return {
        "IU": SLACK - c_up,     # interval surplus  <= SLACK
        "ID": SLACK - c_dn,     # interval deficit  <= SLACK
        "A": (t / 2 - g).min(),
        "C": (g1 + (1 - t) / 2 - g).min(),
        "L1": (g - (-t + t * t / 2)).min(),
        "L1m": (g - g1 + (1 - t * t) / 2).min(),
        "L2": (g + 0.5).min(),
    }


def step(y):
    n = len(y)
    m = n + 1
    p = np.concatenate([[0.0], np.cumsum(np.arange(1, n + 1) / m - y)])
    j = int(np.argmax(p))
    return np.insert(y, j, (2 * j + 1) / (2 * m))


SLACK = 0.125      # constant c in the interval family IU/ID
DBOUND = None      # optional hypothesis |D_N| <= DBOUND
GAPS = False       # optional hypothesis: min gap >= 1/(2N) (Kritzinger Thm 3)


def local_ok(y):
    n = len(y)
    if DBOUND is not None:
        j = np.arange(1, n + 1)
        if (j - n * y).max() > DBOUND or ((j - 1) - n * y).min() < -DBOUND:
            return False
    if GAPS and n > 1 and np.diff(y).min() < 1 / (2 * n) - 1e-12:
        return False
    return True


def score(y, cands):
    """(feasible, post-step worst margin over cands)."""
    mg = margins(y)
    if mg["A"] < -1e-12 or mg["C"] < -1e-12 or any(mg[c] < -1e-12 for c in cands):
        return False, None
    if not local_ok(y):
        return False, None
    m2 = margins(step(y))
    return True, min(m2[c] for c in cands)


def search(cands, n, iters, rng):
    y = (2 * np.arange(n) + 1) / (2 * n)          # centred grid: feasible start
    ok, best = score(y, cands)
    cur = best
    temp = 0.05
    for it in range(iters):
        z = y.copy()
        k = rng.integers(n)
        z[k] = np.clip(z[k] + rng.normal(0, 0.3 / n + 0.1 * rng.random() / n * n ** 0.5), 0, 1)
        z.sort()
        ok, s = score(z, cands)
        if not ok:
            continue
        if s < cur or rng.random() < np.exp((cur - s) / temp):
            y, cur = z, s
            if s < best:
                best, by = s, z.copy()
        temp *= 0.9995
        if best < -1e-9:
            return best, by
    return best, (by if "by" in dir() else y)


if __name__ == "__main__":
    cands = sys.argv[1].split(",")
    nmin, nmax, iters, seed = map(int, sys.argv[2:6])
    if len(sys.argv) > 6 and sys.argv[6] != "-":
        DBOUND = float(sys.argv[6])
    if len(sys.argv) > 8:
        SLACK = float(sys.argv[8])
    if len(sys.argv) > 7:
        GAPS = sys.argv[7] == "1"
    rng = np.random.default_rng(seed)
    for n in range(nmin, nmax + 1):
        best, y = search(cands, n, iters, rng)
        flag = "COUNTEREXAMPLE" if best < -1e-9 else "ok"
        print(f"N={n:3d} worst post-step margin {best:+.5f} {flag}")
        if best < -1e-9:
            mg = margins(y)
            print("   points:", np.round(y, 5).tolist())
            print("   pre-step margins:", {k: round(v, 5) for k, v in mg.items()})
            x = np.setdiff1d(step(y), y)
            print("   greedy inserts x =", np.round(x, 5).tolist())
