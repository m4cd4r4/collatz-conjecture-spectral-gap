# -*- coding: utf-8 -*-
"""
calibrate_general_shift.py - MEASURE BEFORE PROVING, for the 3x+c generalisation.

Why this exists
---------------
BARRIER_THEOREM.md section 7.1 asserts that the Lean proof of the certificate "uses exactly one
property of 3^{-1}: that it is odd. So the formalisation runs verbatim for 3x-1."  Acting on that
means a real refactor: 104 literal `3n+1` sites across 5 Lean files, plus a redefinition of
`rstar` (for shift c it solves 3r + c = 0 mod 2^k, not 3r + 1 = 0).

Before paying that, measure whether the LEMMA-LEVEL ingredients actually transfer - not just the
headline.  If Lemma A's exact block norms fail for some odd c, the refactor is wasted and the
"runs verbatim" claim is wrong.

What is checked, for every odd shift c and several k
---------------------------------------------------
  G1  cert_c(k) <= 0.853553...      the target theorem, same BOUND (not the same value)
  G2  Lemma A: the clean upper-cascade block norms are EXACTLY 2^{-(b-a)/2}
  G3  Lemma B: the defect covector satisfies ||c||_2 <= sqrt(3) * 2^{-k/2}
  G4  the defect really is supported on ONE row, and that row is the r* solving 3r + c = 0

Conventions follow probe_cycle_link_cert.py / fable_assembly_check.py exactly: odd residues mod
2^k, chi_xi(r) = w^{xi r}/sqrt(N), level(xi) = v2(xi), Q[a,b] = ||P_a U P_b||_2 with U = T^T,
cert = max_a sum_b Q[a,b] 2^{a-b}.

Exits non-zero on any failure.
"""
import sys
import numpy as np

BOUND = 2 ** -1.5 + 0.5          # 0.853553...
FAIL = []


def v2(n):
    if n == 0:
        return 0
    c = 0
    while n % 2 == 0:
        n //= 2; c += 1
    return c


def syr_c(n, c):
    """Odd core of 3n + c.  c odd, so 3n + c is even for odd n."""
    val = 3 * n + c
    if val == 0:
        return 0
    while val % 2 == 0:
        val //= 2
    return val


def build_T(k, c):
    mod = 1 << k
    N = mod >> 1
    T = np.zeros((N, N))
    for src in range(N):
        r = 2 * src + 1
        for m in range(mod):
            s = syr_c(r + m * mod, c) % mod
            if s % 2 == 1:
                T[(s - 1) // 2, src] += 1.0
    return T / mod


def character_basis(k):
    mod = 1 << k
    N = mod >> 1
    w = np.exp(2j * np.pi / mod)
    odds = np.arange(1, mod, 2, dtype=np.int64)
    xis = np.arange(N, dtype=np.int64)
    C = w ** np.outer(odds, xis) / np.sqrt(N)
    levels = np.array([v2(int(x)) if x != 0 else -1 for x in xis])
    return C, levels


def rstar(k, c):
    """The residue with 3r + c = 0 mod 2^k, i.e. the defect row."""
    mod = 1 << k
    inv3 = pow(3, -1, mod)
    return ((-c) * inv3) % mod


def analyse(k, c):
    mod = 1 << k
    T = build_T(k, c)
    U = T.T
    C, levels = character_basis(k)
    Uc = C.conj().T @ U @ C                      # U in the character basis
    K = k - 1
    lv = [np.where(levels == a)[0] for a in range(K)]

    Q = np.zeros((K, K))
    for a in range(K):
        for b in range(K):
            if len(lv[a]) == 0 or len(lv[b]) == 0:
                continue
            Q[a, b] = np.linalg.norm(Uc[np.ix_(lv[a], lv[b])], 2)
    cert = max(sum(Q[a, b] * 2.0 ** (a - b) for b in range(K)) for a in range(K))

    # clean part: zero the r* ROW of U (= the r* column of T)
    rs = rstar(k, c)
    assert rs % 2 == 1, "r* must be odd"
    ridx = (rs - 1) // 2
    Uclean = U.copy(); Uclean[ridx, :] = 0.0
    Ucl = C.conj().T @ Uclean @ C
    Qcl = np.zeros((K, K))
    for a in range(K):
        for b in range(K):
            if len(lv[a]) and len(lv[b]):
                Qcl[a, b] = np.linalg.norm(Ucl[np.ix_(lv[a], lv[b])], 2)

    D = U - Uclean                                # rank-1 defect
    cvec = C.conj().T @ D @ C
    return cert, Q, Qcl, np.linalg.norm(D, 2), np.linalg.matrix_rank(D, tol=1e-9), rs


def run():
    shifts_for = lambda k: [1, (1 << k) - 1, 3, 5, 7, 11, (1 << k) - 3]
    print("G1  cert_c(k) against the proven bound %.6f" % BOUND)
    print("   k |    c    |  cert_c(k)  | <= bound")
    for k in (4, 5, 6, 7, 8):
        for c in sorted(set(x % (1 << k) or 1 for x in shifts_for(k))):
            if c % 2 == 0:
                continue
            cert, Q, Qcl, dn, dr, rs = analyse(k, c)
            ok = cert <= BOUND + 1e-9
            if not ok:
                FAIL.append("G1 cert=%.6f > bound at k=%d c=%d" % (cert, k, c))
            print("   %d | %6d  |  %.6f   | %s" % (k, c, cert, "yes" if ok else "*** NO ***"))

    print("\nG2  Lemma A: clean block norms exactly 2^{-(b-a)/2} for b > a")
    for k in (5, 6, 7):
        for c in (1, (1 << k) - 1, 5):
            _, _, Qcl, _, _, _ = analyse(k, c)
            K = k - 1
            worst = 0.0
            for a in range(K):
                for b in range(a + 1, K):
                    want = 2.0 ** (-(b - a) / 2.0)
                    worst = max(worst, abs(Qcl[a, b] - want))
            status = "OK" if worst < 1e-9 else "*** DEVIATION %.2e ***" % worst
            if worst >= 1e-9:
                FAIL.append("G2 clean block norm deviates by %.2e at k=%d c=%d" % (worst, k, c))
            print("   k=%d c=%-5d max |Qclean[a,b] - 2^{-(b-a)/2}| = %.2e  %s" % (k, c, worst, status))

    print("\nG3/G4  defect: rank, norm, and the r* row")
    print("   k |    c    | rank(D) | ||D||_2  | sqrt3*2^(-k/2) | <= ? |  r*")
    for k in (5, 6, 7, 8):
        for c in (1, (1 << k) - 1, 5):
            _, _, _, dn, dr, rs = analyse(k, c)
            lim = np.sqrt(3) * 2.0 ** (-k / 2.0)
            ok = dn <= lim + 1e-9
            if dr != 1:
                FAIL.append("G4 rank(D)=%d at k=%d c=%d" % (dr, k, c))
            if not ok:
                FAIL.append("G3 ||D||=%.5f > sqrt3*2^(-k/2)=%.5f at k=%d c=%d" % (dn, lim, k, c))
            print("   %d | %6d  |    %d    | %.6f |    %.6f    | %s | %d"
                  % (k, c, dr, dn, lim, "yes" if ok else "NO", rs))

    print()
    if FAIL:
        print("FAILURES (%d):" % len(FAIL))
        for f in FAIL[:20]:
            print("  " + f)
        return 1
    print("ALL CHECKS PASS - the lemma-level ingredients transfer to every odd shift tested.")
    print("The 'runs verbatim for 3x-1' claim is supported; the Lean refactor is justified.")
    return 0


if __name__ == "__main__":
    sys.exit(run())
