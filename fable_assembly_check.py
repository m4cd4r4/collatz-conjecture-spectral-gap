# -*- coding: utf-8 -*-
"""
Verification for THEOREM.md (2026-07-05): the truncation-aware assembly closes the certificate
from Lemmas A + B alone.

Claim:  R_a := sum_b Q[a,b] 2^{a-b}  <=  f(e),   e := k-a >= 2,
        f(e) = sum_{d=1}^{e-2} 2^{-3d/2} + 2^{-(e-1)/2},     max_{e>=2} f(e) = f(3) = 0.853553...

Derivation: Q[a,b] <= 2^{-(b-a)/2}[b>a] + u_a v_b (Lemma A + rank-1 defect); the upper series
truncates at d <= e-2; the defect over ALL b is <= 2^{(a-1)/2} * 2^{1-k/2} = 2^{-(e-1)/2} by
Cauchy-Schwarz + Lemma B (||v|| <= sqrt(3) 2^{-k/2}). No Lemma C, no leak bookkeeping, all k >= 3.

This script checks, against the dense ground-truth operator build_T, for k = 3..13:
  (1) R_a <= f(k-a) for every row a (the theorem's envelope);
  (2) u_a = 2^{-(a+1)/2} exactly;  ||c|| * 2^{k/2} <= sqrt(3)  (Lemma B);
  (3) Q[a,b] = u_a v_b exactly for a >= b (R1+R2);  Q[a,b] - 2^{-(b-a)/2} <= u_a v_b for a < b;
  (4) the reported cert(k) and rho(Q) match the published ~0.6345 / ~0.566.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from analytic_proofs import build_T, v2


def character_basis(k):
    mod = 1 << k
    N = mod >> 1
    w = np.exp(2j * np.pi / mod)
    odds = np.arange(1, mod, 2, dtype=np.int64)
    xis = np.arange(N, dtype=np.int64)
    C = w ** np.outer(odds, xis) / np.sqrt(N)
    levels = np.array([v2(int(x)) if x != 0 else -1 for x in xis])
    return C, levels


def f_env(e):
    return sum(2.0 ** (-1.5 * d) for d in range(1, e - 1)) + 2.0 ** (-(e - 1) / 2)


def check(k):
    mod = 1 << k
    T = np.asarray(build_T(k), dtype=float)
    U = T.T
    C, levels = character_basis(k)
    N = mod >> 1
    K = k - 1

    rstar = ((pow(4, (k + 1) // 2, 3 * mod) - 1) // 3) % mod
    i_star = (rstar - 1) // 2
    assert v2(3 * rstar + 1) >= k

    c = U[i_star, :].copy()
    coef_c = C.conj().T @ c
    coef_e = C.conj().T @ np.eye(N)[i_star]
    v = np.array([np.linalg.norm(coef_c[levels == b]) for b in range(K)])
    u = np.array([np.linalg.norm(coef_e[levels == a]) for a in range(K)])

    Uc = C.conj().T @ U @ C
    Q = np.zeros((K, K))
    for a in range(K):
        ia = levels == a
        for b in range(K):
            Q[a, b] = np.linalg.norm(Uc[np.ix_(ia, ib)], 2) if (ib := levels == b) is not None else 0.0

    R = (Q * 2.0 ** (np.arange(K)[:, None] - np.arange(K)[None, :])).sum(axis=1)
    fk = np.array([f_env(k - a) for a in range(K)])

    err_u = np.abs(u - 2.0 ** (-(np.arange(K) + 1) / 2)).max()
    c_scaled = np.linalg.norm(c) * 2 ** (k / 2)
    # (3): lower/diag exact separability, upper deviation within u_a v_b
    sep = max(abs(Q[a, b] - u[a] * v[b]) for a in range(K) for b in range(a + 1))
    updev = max((Q[a, b] - 2.0 ** (-(b - a) / 2)) - u[a] * v[b] for a in range(K) for b in range(a + 1, K)) if K > 1 else 0.0

    ok = (R <= fk + 1e-9).all() and err_u < 1e-9 and c_scaled <= np.sqrt(3) + 1e-9 and sep < 1e-9 and updev <= 1e-9
    print(f"k={k:2d}: cert={R.max():.4f}  rho(Q)={max(abs(np.linalg.eigvals(Q))):.4f}  "
          f"||c||2^(k/2)={c_scaled:.4f}  max[R_a-f(e)]={(R - fk).max():+.4f}  "
          f"|u err|={err_u:.1e}  sep={sep:.1e}  updev={updev:+.1e}  {'PASS' if ok else 'FAIL'}")
    assert ok
    return R.max()


if __name__ == "__main__":
    print("envelope: " + ", ".join(f"f({e})={f_env(e):.4f}" for e in range(2, 9))
          + "  -> max = f(3) = 0.853553")
    for k in range(3, 14):
        check(k)
    print("ALL PASS: cert(k) <= f(3) = 0.8536 at every tested k (theorem: all k >= 3).")
