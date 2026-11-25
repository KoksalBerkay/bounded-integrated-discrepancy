"""Quadrature errors E_f(N) = sum_{k<=N} f(x_k) - N * int_0^1 f for Kritzinger's
sequence vs van der Corput (base 2) and the golden-ratio Kronecker sequence.
EMPIRICAL (floats). Proved for Kritzinger (from the envelope theorem): for convex
f in C^2, E_f(N) <= min((f(1)-f(0))/2 + max(0,-f'(0)), max(0,f'(1)) - (f(1)-f(0))/2).
Usage: python3 experiments/quadrature.py SEQ NMAX
"""
import math
import sys

import numpy as np

idx = [int(l.split()[1]) for l in open(sys.argv[1])]
nmax = min(int(sys.argv[2]), len(idx))
kr = np.array([(2 * idx[q] + 1) / (2 * (q + 1)) for q in range(nmax)])


def vdc(n):
    x, d = 0.0, 0.5
    while n:
        x += d * (n & 1)
        n >>= 1
        d /= 2
    return x


vd = np.array([vdc(n) for n in range(nmax)])
gold = np.array([(n * (math.sqrt(5) - 1) / 2) % 1 for n in range(1, nmax + 1)])
fs = {
    "x":      (lambda x: x, 0.5, 1.0, 1.0, 1.0),          # f, integral, f(1)-f(0), f'(0), f'(1)
    "x^2":    (lambda x: x * x, 1 / 3, 1.0, 0.0, 2.0),
    "e^x":    (lambda x: np.exp(x), math.e - 1, math.e - 1, 1.0, math.e),
    "(x-.3)^2": (lambda x: (x - .3) ** 2, (0.7 ** 3 + 0.3 ** 3) / 3, 0.49 - 0.09, -0.6, 1.4),
}
n = np.arange(1, nmax + 1)
for name, (f, I, df, d0, d1) in fs.items():
    bound = min(df / 2 + max(0, -d0), max(0, d1) - df / 2)
    line = f"f={name:9s} proved upper bound {bound:+.3f} |"
    for lab, seq in (("Kritzinger", kr), ("vdCorput", vd), ("golden", gold)):
        e = np.cumsum(f(seq)) - n * I
        line += f" {lab}: max {e.max():+.3f} min {e.min():+.3f} |"
    print(line)
