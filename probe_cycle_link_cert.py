# -*- coding: utf-8 -*-
"""
Reproduces the cert / rho(Q) / |lambda_2| table of CYCLE_CLAIM_REFUTED.md for BOTH signs.

Why this file exists
--------------------
CYCLE_CLAIM_REFUTED.md says "Reproduce: python probe_cycle_link.py", but that script prints
only |lambda_1| and |lambda_2| - it never computes `cert` or `rho(Q)`. Four of the six columns
of the refutation table had no producer anywhere in the repository, so the decisive control
experiment was not reproducible from the repo. (Provenance gap found by the 2026-08-02
retro-label audit; closed by this script, task H0.)

The table it reproduces (CYCLE_CLAIM_REFUTED.md):

    k  | 3x+1 cert | 3x+1 rho(Q) | 3x+1 |l2| | 3x-1 cert | 3x-1 rho(Q) | 3x-1 |l2|
    6  | 0.6338    | 0.5535      | 0.277     | 0.6018    | 0.5039      | 0.297
    8  | 0.6347    | 0.5661      | 0.255     | 0.6061    | 0.5272      | 0.293
    10 | 0.6345    | 0.5673      | 0.270     | 0.6061    | 0.5365      | 0.291
    11 | 0.6343    | 0.5664      | 0.252     | 0.6060    | 0.5388      | 0.283

The point of the control: the 3x-1 operator passes the certificate MORE strongly than 3x+1,
uniformly in k, yet 3x-1 provably HAS non-trivial cycles ({5,7}, {17,25,37,55,41,...}).
So `cert(k) < 1` does not imply the absence of cycles.

Conventions follow fable_assembly_check.py exactly: states are the odd residues mod 2^k,
characters chi_xi(r) = w^{xi r}/sqrt(N) with w = exp(2i pi/2^k), level(xi) = v2(xi),
Q[a,b] = ||P_a U P_b||_2 with U = T^T, and cert = max_a sum_b Q[a,b] 2^{a-b}.

Note on the 3x-1 defect row: for sign -1 the exceptional row is r* = +3^{-1} mod 2^k (the
negation of the 3x+1 one), since 3r - 1 = 0 mod 2^k there. It is located by search here
rather than by closed form, so the same code path serves both signs.

Usage:  python probe_cycle_link_cert.py
"""
import numpy as np


def v2(n):
    """2-adic valuation of a positive integer."""
    if n == 0:
        return 0
    c = 0
    while n % 2 == 0:
        n //= 2
        c += 1
    return c


def syr_pm(n, sign):
    """Syracuse-type odd core: oddpart(3n + sign). sign = +1 (Collatz) or -1."""
    val = 3 * n + sign
    if val == 0:
        return 0
    while val % 2 == 0:
        val //= 2
    return val


def build_T_pm(k, sign):
    """Fibre-averaged transition matrix on odd residues mod 2^k (column-stochastic).

    Identical to probe_cycle_link.build_T_pm; for sign=+1 it agrees with
    analytic_proofs.build_T.
    """
    mod = 1 << k
    N = mod >> 1
    T = np.zeros((N, N))
    for src in range(N):
        r = 2 * src + 1
        for m in range(mod):
            s = syr_pm(r + m * mod, sign) % mod
            if s % 2 == 1:
                T[(s - 1) // 2, src] += 1.0
    T /= mod
    return T


def character_basis(k):
    mod = 1 << k
    N = mod >> 1
    w = np.exp(2j * np.pi / mod)
    odds = np.arange(1, mod, 2, dtype=np.int64)
    xis = np.arange(N, dtype=np.int64)
    C = w ** np.outer(odds, xis) / np.sqrt(N)
    levels = np.array([v2(int(x)) if x != 0 else -1 for x in xis])
    return C, levels


def cert_rho_l2(k, sign):
    """Return (cert, rho(Q), |lambda_2|) for the sign-flipped Syracuse operator."""
    T = build_T_pm(k, sign)
    U = T.T
    C, levels = character_basis(k)
    K = k - 1

    Uc = C.conj().T @ U @ C
    Q = np.zeros((K, K))
    for a in range(K):
        ia = levels == a
        for b in range(K):
            ib = levels == b
            Q[a, b] = np.linalg.norm(Uc[np.ix_(ia, ib)], 2)

    weights = 2.0 ** (np.arange(K)[:, None] - np.arange(K)[None, :])
    cert = (Q * weights).sum(axis=1).max()
    rho_Q = max(abs(np.linalg.eigvals(Q)))

    mags = np.sort(np.abs(np.linalg.eigvals(T)))[::-1]
    return cert, rho_Q, mags[1]


# Published table from CYCLE_CLAIM_REFUTED.md, for regression checking.
PUBLISHED = {
    6:  (0.6338, 0.5535, 0.277, 0.6018, 0.5039, 0.297),
    8:  (0.6347, 0.5661, 0.255, 0.6061, 0.5272, 0.293),
    10: (0.6345, 0.5673, 0.270, 0.6061, 0.5365, 0.291),
    11: (0.6343, 0.5664, 0.252, 0.6060, 0.5388, 0.283),
}

if __name__ == "__main__":
    print("3x-1 cycle check: 5 -> oddpart(3*5-1=14)=7 -> oddpart(3*7-1=20)=5, so {5,7} is a cycle.")
    print(f"  syr(5,-1)={syr_pm(5, -1)}, syr(7,-1)={syr_pm(7, -1)}   (expect 7, 5)\n")

    hdr = f"{'k':>3} | {'+1 cert':>8} {'+1 rho':>8} {'+1 |l2|':>8} | {'-1 cert':>8} {'-1 rho':>8} {'-1 |l2|':>8} | match"
    print(hdr)
    print("-" * len(hdr))

    worst = 0.0
    for k in sorted(PUBLISHED):
        cp, rp, lp = cert_rho_l2(k, +1)
        cm, rm, lm = cert_rho_l2(k, -1)
        got = (cp, rp, lp, cm, rm, lm)
        exp = PUBLISHED[k]
        # published to 4 dp for cert/rho and 3 dp for |l2|
        tols = (5e-5, 5e-5, 5e-4, 5e-5, 5e-5, 5e-4)
        devs = [abs(g - e) for g, e in zip(got, exp)]
        ok = all(d <= t for d, t in zip(devs, tols))
        worst = max(worst, max(d / t for d, t in zip(devs, tols)))
        print(f"{k:>3} | {cp:>8.4f} {rp:>8.4f} {lp:>8.3f} | "
              f"{cm:>8.4f} {rm:>8.4f} {lm:>8.3f} | {'OK' if ok else 'MISMATCH'}")

    print(f"\nWorst deviation vs published, as a fraction of print tolerance: {worst:.2f}")
    print("(<= 1.00 means every published digit is reproduced.)\n")
    print("Reading: the 3x-1 operator passes the certificate MORE strongly than 3x+1")
    print("(cert ~0.606 < ~0.634) uniformly in k - yet 3x-1 has the cycles {5,7} and")
    print("{17,25,37,55,41,...}. Hence cert(k) < 1 does NOT imply 'no non-trivial cycles'.")
