# -*- coding: utf-8 -*-
"""
calibrate_lemmaA_shift_structure.py - WHY Lemma A's clean block norms are shift-independent.

calibrate_general_shift.py gate G2 MEASURES that the clean upper-cascade block norms are exactly
2^{-(b-a)/2} for every odd shift c.  This script establishes the MECHANISM, because the mechanism
decides how big the Lean generalisation is.

GramIdentity's Gram argument consumes exactly two facts about the operator:

    Bent_eq_zero_of_not_owned   off the owner set the entry is 0          (SUPPORT)
    norm_Bent_of_owned          on it, the modulus is exactly (1/2)^(b-a) (MODULUS)

Neither mentions a phase.  Both come from

    upper_entry_eq :  cleanEntry = wz(xi*u) * Sodd(resJ(eta,xi,u,b-a), k-(b-a))

in which the first factor is used only through ||wz|| = 1, and the Sodd argument alphaJ(eta,xi,u,j)
does not mention the shift at all.  So IF the shift enters the clean operator only as a per-entry
phase, every step above the entry theorem transfers to general c unchanged, and the generalisation
is ONE new entry theorem rather than the "104 sites across 5 files" refactor estimated in
calibrate_general_shift.py's header.

Hypotheses tested here
----------------------
  H1  SUPPORT invariance:  {(xi,eta) : B_c[xi,eta] != 0} is the same set for every odd c   -> TRUE
  H2  MODULUS invariance:  |B_c[xi,eta]| = |B_1[xi,eta]| entrywise                         -> TRUE
  H3  the ratio is a COLUMN phase, B_c = B_1 * diag_xi(w^{xi*3inv*(c-1)})                  -> FALSE

H1+H2 are exactly what the Gram argument needs and are enough on their own: the off-diagonal
vanishes by disjoint support and the diagonal is a sum of squared moduli, so B*B - and hence every
block norm - is shift-independent.

H3 IS RECORDED BECAUSE IT IS THE ATTRACTIVE WRONG TURN.  A column-only phase would make the whole
thing a two-line diagonal-unitary conjugation.  It is false: the phase depends on both indices.
The norm invariance does not come from a factorisation, it comes from disjoint support.  Do not
spend a session trying to rescue H3.

H4, a free structural fact: 3x+c IS 3x+1 with source residues translated, but ONLY when 3 | c-1,
because 3(r+s)+1 = 3r+c needs s = (c-1)/3 as an identity over Z.  A modular s gives it only mod
2^k, and oddPart does not factor through the residue.  So the family splits by c mod 6, and for
c = 1 mod 6 the block norms are inherited trivially by a column permutation.

Exits non-zero on any failure.
"""
import sys
import numpy as np

TOL = 1e-9
FAIL = []


def v2(n):
    if n == 0:
        return 0
    c = 0
    while n % 2 == 0:
        n //= 2; c += 1
    return c


def syr_c(n, c):
    """Odd core of 3n + c, with c a genuine INTEGER (may be negative)."""
    val = 3 * n + c
    while val % 2 == 0:
        val //= 2
    return val


def clean_char(k, c):
    """The CLEAN operator (r* row of U zeroed) in the character basis, plus the level labels."""
    mod = 1 << k
    N = mod >> 1
    T = np.zeros((N, N))
    for src in range(N):
        r = 2 * src + 1
        for m in range(mod):
            T[(syr_c(r + m * mod, c) % mod - 1) // 2, src] += 1.0
    T /= mod
    U = T.T
    rs = ((-c) * pow(3, -1, mod)) % mod
    U[(rs - 1) // 2, :] = 0.0
    w = np.exp(2j * np.pi / mod)
    odds = np.arange(1, mod, 2, dtype=np.int64)
    xis = np.arange(N, dtype=np.int64)
    C = w ** np.outer(odds, xis) / np.sqrt(N)
    levels = np.array([v2(int(x)) if x != 0 else -1 for x in xis])
    return C.conj().T @ U @ C, levels


def shifts_for(k):
    return [3, 5, 7, 11, (1 << k) - 1, -1]


def label(c):
    return "-1 (TRUE 3x-1)" if c == -1 else str(c)


def run_h1_h2():
    print("H1/H2  support and modulus of the CLEAN operator, against c = 1, over all a<b blocks")
    print("   k | c              | support identical | max ||B_c| - |B_1||")
    for k in (4, 5, 6, 7):
        base, levels = clean_char(k, 1)
        K = k - 1
        lv = [np.where(levels == a)[0] for a in range(K)]
        for c in shifts_for(k):
            M, _ = clean_char(k, c)
            sup_ok = True
            worst = 0.0
            for a in range(K):
                for b in range(a + 1, K):
                    if not (len(lv[a]) and len(lv[b])):
                        continue
                    Bb = base[np.ix_(lv[a], lv[b])]
                    Bc = M[np.ix_(lv[a], lv[b])]
                    if not np.array_equal(np.abs(Bb) > TOL, np.abs(Bc) > TOL):
                        sup_ok = False
                    worst = max(worst, float(np.max(np.abs(np.abs(Bb) - np.abs(Bc)))))
            if not sup_ok:
                FAIL.append("H1 support differs at k=%d c=%d" % (k, c))
            if worst > 1e-12:
                FAIL.append("H2 modulus differs by %.2e at k=%d c=%d" % (worst, k, c))
            print("   %d | %-14s | %-17s | %.3e" % (k, label(c), str(sup_ok), worst))
        print()


def run_h3():
    print("H3  is the ratio a COLUMN phase?  EXPECTED FALSE - this is the attractive wrong turn.")
    print("   k | c              | ratio depends on xi alone")
    any_true = False
    for k in (4, 5, 6):
        B1, levels = clean_char(k, 1)
        K = k - 1
        lv = [np.where(levels == a)[0] for a in range(K)]
        for c in shifts_for(k):
            Bc, _ = clean_char(k, c)
            colphase = {}
            ok_col = True
            for a in range(K):
                for b in range(a + 1, K):
                    for i in lv[a]:
                        for j in lv[b]:
                            if abs(B1[i, j]) > TOL:
                                r = Bc[i, j] / B1[i, j]
                                if j in colphase:
                                    if abs(r - colphase[j]) > 1e-8:
                                        ok_col = False
                                else:
                                    colphase[j] = r
            if ok_col:
                any_true = True
            print("   %d | %-14s | %s" % (k, label(c), ok_col))
        print()
    if any_true:
        FAIL.append("H3 held somewhere - re-derive; the brief says it is false everywhere")


def run_h4():
    print("H4  3x+c is 3x+1 with sources translated  <=>  3 | c-1  (i.e. c = 1 mod 6)")
    print("   k | c    | 3|c-1 | column-permutation identity | r*_c + s == r*_1")
    for k in (3, 4, 5, 6):
        mod = 1 << k
        odds = list(range(1, mod, 2))
        pos = {r: i for i, r in enumerate(odds)}

        def T(c):
            M = np.zeros((len(odds), len(odds)), dtype=np.int64)
            for r in odds:
                for m in range(mod):
                    M[pos[syr_c(r + m * mod, c) % mod], pos[r]] += 1
            return M

        T1 = T(1)
        inv3 = pow(3, -1, mod)
        for c in range(3, min(mod, 16), 2):
            s = (inv3 * (c - 1)) % mod
            perm = [pos[(r + s) % mod] for r in odds]
            identity = np.array_equal(T(c), T1[:, perm])
            predicted = (c - 1) % 3 == 0
            rstar_ok = ((((-c) * inv3) % mod) + s) % mod == ((-1 * inv3) % mod)
            if identity != predicted:
                FAIL.append("H4 mismatch at k=%d c=%d (identity=%s predicted=%s)"
                            % (k, c, identity, predicted))
            if not rstar_ok:
                FAIL.append("H4 r* translation failed at k=%d c=%d" % (k, c))
            print("   %d | %-4d | %-5s | %-27s | %s"
                  % (k, c, predicted, identity, rstar_ok))
        print()


def run():
    run_h1_h2()
    run_h3()
    run_h4()
    if FAIL:
        print("FAILURES (%d):" % len(FAIL))
        for f in FAIL[:20]:
            print("  " + f)
        return 1
    print("ALL CHECKS PASS.")
    print("  H1+H2 hold  -> the shift enters the clean operator ONLY as a per-entry phase, so")
    print("                 every step above the entry theorem transfers to general c unchanged.")
    print("  H3 is FALSE -> the phase is NOT a column phase; there is no diagonal-unitary")
    print("                 shortcut.  The norm invariance comes from disjoint support.")
    print("  H4 holds    -> only the c = 1 mod 6 class is a translate of 3x+1.")
    print("See Collatz/BRIEF_LEMMA_A_GENERAL_SHIFT.md (private repo) for what to build.")
    return 0


if __name__ == "__main__":
    sys.exit(run())
