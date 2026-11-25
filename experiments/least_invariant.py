"""Least inductive two-point family for the greedy step (EMPIRICAL, grid).

Hypotheses on G (for s < t):  G(t) - G(s) <= phi(s,t)   (surplus on [s,t])
                              G(s) - G(t) <= chi(s,t)   (deficit on [s,t])
Step: x maximises G + psi, psi(u) = u(1-u)/2;  G' = G + k_x,
k_x(u) = (u - x)_+ - u^2/2.  The step preserves the family if, for all
s < t and x (case analysis as in the remark in Section 4 of the paper):
  phi(s,t) >= phi(s,x) + psi(x) - psi(t) + (t-x) - (t^2-s^2)/2   (s <= x < t, when positive)
  phi(s,t) >= chi(x,s) + psi(x) - psi(t) + (t-s) - (t^2-s^2)/2   (x < s)
  chi(s,t) >= phi(t,x) + psi(x) - psi(s) + (t^2-s^2)/2           (x >= t)
  chi(s,t) >= chi(x,t) + psi(x) - psi(s) + (t^2-s^2)/2 - (t-x)   (s < x < t, when positive)
with phi(s,s) = chi(s,s) = 0 and phi, chi >= 0 (base case G_0 = 0).
These are monotone, so the least solution is found by value iteration from 0.
Divergence means no family of this form is inductive (for these sufficient
conditions).
Usage: python3 experiments/least_invariant.py NGRID MAXITER
"""
import sys

import numpy as np

n, maxit = int(sys.argv[1]), int(sys.argv[2])
u = np.linspace(0, 1, n)
psi = u * (1 - u) / 2
I, J, K = np.meshgrid(np.arange(n), np.arange(n), np.arange(n), indexing="ij")
s, t, x = u[I], u[J], u[K]
valid = I < J
dq = (t ** 2 - s ** 2) / 2

# masks and constants for each rule (arrays indexed [i, j, k])
m1 = valid & (I <= K) & (K < J)
c1 = psi[K] - psi[J] + (t - x) - dq
m1 &= (t - x) - dq > 0
m2 = valid & (K < I)
c2 = psi[K] - psi[J] + (t - s) - dq
m3 = valid & (K >= J)
c3 = psi[K] - psi[I] + dq
m4 = valid & (I < K) & (K < J)
c4 = psi[K] - psi[I] + dq - (t - x)
m4 &= dq - (t - x) > 0

phi = np.zeros((n, n))
chi = np.zeros((n, n))
for it in range(maxit):
    # rule 1: phi(s,x) with x index k (phi[i,k]; zero when k == i)
    r1 = np.where(m1, phi[I, K] + c1, -np.inf).max(axis=2)
    r2 = np.where(m2, chi[K, I] + c2, -np.inf).max(axis=2)
    r3 = np.where(m3, phi[J, K] + c3, -np.inf).max(axis=2)
    r4 = np.where(m4, chi[K, J] + c4, -np.inf).max(axis=2)
    new_phi = np.where(np.triu(np.ones((n, n)), 1) > 0, np.maximum(0, np.maximum(r1, r2)), 0)
    new_chi = np.where(np.triu(np.ones((n, n)), 1) > 0, np.maximum(0, np.maximum(r3, r4)), 0)
    new_phi, new_chi = np.maximum(phi, new_phi), np.maximum(chi, new_chi)
    delta = max(np.abs(new_phi - phi).max(), np.abs(new_chi - chi).max())
    phi, chi = new_phi, new_chi
    if delta < 1e-13:
        break
    if phi.max() > 50 or chi.max() > 50:
        break
print(f"grid {n}: iterations {it + 1}, last change {delta:.2e}")
print(f"max phi {phi.max():.4f}, max chi {chi.max():.4f}")
print(f"bound on G: max_t phi(0,t) = {phi[0].max():.4f}, max_t chi(0,t) = {chi[0].max():.4f}")
if delta < 1e-13:
    print("phi(0,t) samples:", np.round(phi[0, ::max(1, n // 10)], 4).tolist())
    print("chi(0,t) samples:", np.round(chi[0, ::max(1, n // 10)], 4).tolist())
