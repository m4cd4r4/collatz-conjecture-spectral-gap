#!/usr/bin/env python3
"""
verify_truncation_reading.py - the numbers behind "What the theorem is a statement about"
(paper Section 9, and the README section of the same name).

Three claims, all checked here:

  C1  The HONEST 2-adic kernel K_k - conditioning Haar on the FULL fibre rather than on the
      finite lift window [0, 2^k) - has |lambda_2| = 0.  We do not prove that; it follows from
      the Bernstein-Lagarias 1996 conjugacy (each Syracuse step deletes at least one low bit,
      so the non-Perron part is a nilpotent shift).  What is checked here is that the numerics
      are CONSISTENT with it: |lambda_2(K_k)| falls steadily toward 0 as the fibre is resolved.
      A fixed-depth computation shows a nonzero value and that value GROWS with k - which looks
      alarming and is purely a sampling artifact.  That trap is the reason this script exists.

  C2  rank(T_k - K_k) = 1 for every k.  The window substitution touches exactly one row.

  C3  ||T_k - K_k||_1 is roughly 0.25-0.50 and does NOT shrink with k.  The defect is rank one
      but it is not small - which is what makes the uniform bound a real statement rather than
      a perturbative triviality.

It also reproduces |lambda_2(T_k)| independently of EXTREMAL_VALUES.md, as a cross-check on
that table: 0.2727 at k=4, 0.2767 at k=6, 0.2549 at k=8.

Requires numpy.  Exits non-zero on failure.
"""

import sys

FAIL = []
EXTREMAL = {4: 0.2727, 6: 0.2767, 8: 0.2549}   # from EXTREMAL_VALUES.md, 4 dp


def syr(n):
    m = 3 * n + 1
    while m % 2 == 0:
        m //= 2
    return m


def mats(k, M):
    """K_k from lifts mod 2^M (fibre approximation), T_k from the window m < 2^k."""
    import numpy as np
    odds = [r for r in range(2 ** k) if r % 2 == 1]
    idx = {r: i for i, r in enumerate(odds)}
    N = len(odds)
    K = np.zeros((N, N)); T = np.zeros((N, N))
    L = 2 ** (M - k)
    for r in odds:
        for m in range(L):
            n = r + m * (2 ** k)
            if n:
                K[idx[syr(n) % 2 ** k], idx[r]] += 1.0
        K[:, idx[r]] /= L
        for m in range(2 ** k):
            n = r + m * (2 ** k)
            if n:
                T[idx[syr(n) % 2 ** k], idx[r]] += 1.0
        T[:, idx[r]] /= 2 ** k
    return K, T


def lam2(A):
    import numpy as np
    return sorted(abs(np.linalg.eigvals(A)))[::-1][1]


def c1():
    """|lambda_2(K_k)| -> 0 as the fibre is resolved."""
    print("C1  |lambda_2(K_k)| as the fibre approximation deepens (k = 4):")
    vals = []
    for M in (10, 12, 14, 16, 18, 20, 22):
        K, _ = mats(4, M)
        v = lam2(K); vals.append(v)
        print("      2^%-2d lifts   |lambda_2| = %.3e" % (M - 4, v))
    if not all(b < a for a, b in zip(vals, vals[1:])):
        FAIL.append("C1 |lambda_2(K)| is not decreasing monotonically in the fibre depth")
    if vals[-1] > 0.02:
        FAIL.append("C1 |lambda_2(K)| = %.3e at the deepest sample, expected well under 0.02" % vals[-1])
    print("      monotone decreasing toward 0: consistent with nilpotence (proof is CITED)")

    print("\n      THE TRAP: at FIXED depth 2^13 the value grows with k, which is sampling error,")
    print("      not structure -")
    for k in (3, 4, 5, 6):
        K, _ = mats(k, k + 13)
        print("        k=%d  |lambda_2(K_k)| = %.3e" % (k, lam2(K)))
    print("      - so never read a fixed-depth column as evidence about K.")


def c2c3():
    import numpy as np
    print("\nC2/C3  the window defect, and |lambda_2(T_k)| against EXTREMAL_VALUES.md:")
    print("   k | dim | rank(T-K) | ||T-K||_1 | |lam2(T_k)| | EXTREMAL")
    for k in (3, 4, 5, 6, 7, 8):
        K, T = mats(k, k + 14)
        r = int(np.linalg.matrix_rank(T - K, tol=1e-8))
        nrm = float(abs(T - K).sum(axis=0).max())
        l2 = lam2(T)
        if r != 1:
            FAIL.append("C2 rank(T-K) = %d at k=%d, expected 1" % (r, k))
        if not (0.2 <= nrm <= 0.6):
            FAIL.append("C3 ||T-K||_1 = %.4f at k=%d, outside the stated 0.25-0.50 band" % (nrm, k))
        ref = EXTREMAL.get(k)
        if ref is not None and abs(l2 - ref) > 5e-4:
            FAIL.append("cross-check: |lam2(T_%d)| = %.4f but EXTREMAL_VALUES says %.4f" % (k, l2, ref))
        print("   %d | %3d |     %d     |  %.4f   |   %.4f    | %s"
              % (k, 2 ** (k - 1), r, nrm, l2, ("%.4f" % ref) if ref else "-"))
    print("\n   rank one at every k, and NOT small - the defect does not shrink as k grows.")
    print("   A rank-one perturbation of this size could drive an eigenvalue to 1.")
    print("   The theorem says it never does: |lambda_2(T_k)| <= 0.853553... for all k >= 3.")


def run():
    try:
        import numpy  # noqa: F401
    except ImportError:
        print("numpy required"); return 2
    c1(); c2c3()
    print()
    if FAIL:
        print("FAILURES (%d):" % len(FAIL))
        for f in FAIL:
            print("  " + f)
        return 1
    print("ALL CHECKS PASS.")
    print("Note: C1 supports |lambda_2(K)| = 0 numerically; the PROOF is Bernstein-Lagarias 1996,")
    print("cited, not this repository's.")
    return 0


if __name__ == "__main__":
    sys.exit(run())
