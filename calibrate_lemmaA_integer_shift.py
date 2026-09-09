# -*- coding: utf-8 -*-
"""
calibrate_lemmaA_integer_shift.py - does Lemma A's structure survive at a GENUINE INTEGER shift?

calibrate_lemmaA_shift_structure.py established the mechanism (H1+H2: the shift enters the clean
operator only as a per-entry phase; H3 FALSE: it is not a column phase), but it was written for
c : Nat and only reached c = -1 as a spot check.  This script asks the same questions at genuine
negative shifts -1, -5, -11 (and -7, -13 as controls), because that is what route (a') needs
before TkZ / upper_entry_eqZ / cleanBlockCLMZ can be written in Lean.

  L1  H1 (support) and H2 (modulus) at negative c - is the shift still a per-entry phase?
  L2  is the clean block norm still EXACTLY 2^{-(b-a)/2} at negative c?
  L3  does the shell / sbMap bijection survive at negative c?   <-- the one that can genuinely fail
  L4  is rank D = 1 and ||D|| <= sqrt3 * 2^{-k/2} off c = -1?

L3 IS THE GATE.  shellS / sbMapS are Nat-valued in Lean and use (3r + c)/2^j, which at negative c
goes negative before it goes anywhere.  If the bijection onto oddResidues(k-j) fails, a per-entry
phase argument that needs a bijection that does not exist is not a small fix, and Lemma A at an
integer shift must be re-scoped rather than mirrored.

SHIFTS DELIBERATELY EXCLUDED: c = -3t for odd t < 2^k.  There 3r + c = 0 has an odd solution in
range, the AP model degenerates and A_c <= 0.  That is recorded out of scope in
calibrate_integer_shift.py (I5) and DECISION_INTEGER_SHIFT.md, not overlooked here.

Exits non-zero on any failure.
"""
import sys
import numpy as np

TOL = 1e-9
FAIL = []

NEG_SHIFTS = [-1, -5, -7, -11, -13]


def v2(n):
    n = abs(int(n))
    if n == 0:
        raise ValueError("v2(0) - 3r + c vanished; c = -3t is out of scope")
    c = 0
    while n % 2 == 0:
        n //= 2
        c += 1
    return c


def syr_c(n, c):
    """Odd core of 3n + c, c a genuine INTEGER.  Sign-agnostic: oddPart(2^k X) = oddPart(X)."""
    val = 3 * n + c
    if val == 0:
        raise ValueError("3n + c = 0 at n=%d c=%d - out of scope" % (n, c))
    while val % 2 == 0:
        val //= 2
    return val


def clean_char(k, c):
    """CLEAN operator (r* row of U zeroed) in the character basis, plus level labels."""
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


def full_char(k, c):
    """FULL operator U in the character basis, plus the rank-1 defect D and level labels."""
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
    Ucl = U.copy()
    Ucl[(rs - 1) // 2, :] = 0.0
    D = U - Ucl
    w = np.exp(2j * np.pi / mod)
    odds = np.arange(1, mod, 2, dtype=np.int64)
    xis = np.arange(N, dtype=np.int64)
    C = w ** np.outer(odds, xis) / np.sqrt(N)
    levels = np.array([v2(int(x)) if x != 0 else -1 for x in xis])
    return C.conj().T @ U @ C, D, levels, rs


def levels_split(levels, K):
    return [np.where(levels == a)[0] for a in range(K)]


# --------------------------------------------------------------------------- L1

def run_l1():
    print("L1  support (H1) and modulus (H2) of the CLEAN operator at NEGATIVE c, vs c = 1")
    print("   k | c    | support identical | max ||B_c| - |B_1||")
    for k in (4, 5, 6, 7):
        base, levels = clean_char(k, 1)
        K = k - 1
        lv = levels_split(levels, K)
        for c in NEG_SHIFTS:
            M, _ = clean_char(k, c)
            sup_ok, worst = True, 0.0
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
                FAIL.append("L1 support differs at k=%d c=%d" % (k, c))
            if worst > 1e-12:
                FAIL.append("L1 modulus differs by %.2e at k=%d c=%d" % (worst, k, c))
            print("   %d | %-4d | %-17s | %.3e" % (k, c, str(sup_ok), worst))
        print()


# --------------------------------------------------------------------------- L2

def run_l2():
    print("L2  clean upper-cascade block norms EXACTLY 2^{-(b-a)/2} at negative c")
    print("   k | c    | max |norm - 2^{-(b-a)/2}| over a<b")
    for k in (4, 5, 6, 7, 8):
        for c in NEG_SHIFTS:
            M, levels = clean_char(k, c)
            K = k - 1
            lv = levels_split(levels, K)
            worst = 0.0
            for a in range(K):
                for b in range(a + 1, K):
                    if not (len(lv[a]) and len(lv[b])):
                        continue
                    nb = np.linalg.norm(M[np.ix_(lv[a], lv[b])], 2)
                    worst = max(worst, abs(nb - 2.0 ** (-(b - a) / 2.0)))
            if worst > 1e-10:
                FAIL.append("L2 clean block norm off by %.2e at k=%d c=%d" % (worst, k, c))
            print("   %d | %-4d | %.3e" % (k, c, worst))
        print()


# --------------------------------------------------------------------------- L3

def shell_int(k, c, j):
    """{ r in [0, 2^k) : v2(3r + c) = j }.  Nat r, INTEGER c, so 3r + c may be negative."""
    return [r for r in range(1 << k) if (3 * r + c) != 0 and v2(3 * r + c) == j]


def sbmap_int(k, c, j, r):
    """((3r + c) / 2^j) mod 2^(k-j), with Python floor-division = Lean Int.ediv on 2^j > 0."""
    q = (3 * r + c) // (1 << j)          # exact: 2^j | 3r + c by construction
    return q % (1 << (k - j))


def run_l3():
    print("L3  shell / sbMap bijection onto the odd residues mod 2^(k-j), at NEGATIVE c")
    print("   THIS IS THE GATE.  (3r+c)/2^j goes negative before it goes anywhere.")
    print("   k | c    | j | |shell| | 2^(k-1-j) | injective | image = odd residues")
    for k in (4, 5, 6, 7):
        for c in NEG_SHIFTS:
            for j in range(1, k):
                sh = shell_int(k, c, j)
                imgs = [sbmap_int(k, c, j, r) for r in sh]
                inj = len(set(imgs)) == len(imgs)
                target = set(range(1, 1 << (k - j), 2))
                onto = set(imgs) == target
                card_ok = len(sh) == (1 << (k - 1 - j))
                if not card_ok:
                    FAIL.append("L3 |shell| = %d != 2^(k-1-j) = %d at k=%d c=%d j=%d"
                                % (len(sh), 1 << (k - 1 - j), k, c, j))
                if not inj:
                    FAIL.append("L3 sbMap NOT injective at k=%d c=%d j=%d" % (k, c, j))
                if not onto:
                    FAIL.append("L3 sbMap image != odd residues at k=%d c=%d j=%d" % (k, c, j))
                print("   %d | %-4d | %d | %-7d | %-9d | %-9s | %s"
                      % (k, c, j, len(sh), 1 << (k - 1 - j), str(inj), str(onto)))
        print()


# --------------------------------------------------------------------------- L4

def run_l4():
    print("L4  defect rank and norm at negative c:  rank D = 1 and ||D|| <= sqrt3 * 2^{-k/2}")
    print("   k | c    | rank D | ||D||_2  | sqrt3*2^(-k/2) | <= ? | ||D||*2^(k/2)")
    for k in (4, 5, 6, 7, 8):
        for c in NEG_SHIFTS:
            _, D, _, _ = full_char(k, c)
            dn = float(np.linalg.norm(D, 2))
            dr = int(np.linalg.matrix_rank(D, tol=1e-9))
            lim = np.sqrt(3.0) * 2.0 ** (-k / 2.0)
            if dr != 1:
                FAIL.append("L4 rank(D) = %d at k=%d c=%d" % (dr, k, c))
            if dn > lim + 1e-12:
                FAIL.append("L4 ||D|| = %.6f > %.6f at k=%d c=%d" % (dn, lim, k, c))
            print("   %d | %-4d | %-6d | %.6f | %.6f       | %-4s | %.4f"
                  % (k, c, dr, dn, lim, str(dn <= lim + 1e-12), dn * 2.0 ** (k / 2.0)))
        print()


# --------------------------------------------------------------------------- L5

def T_full(k, c):
    mod = 1 << k
    N = mod >> 1
    T = np.zeros((N, N))
    for src in range(N):
        r = 2 * src + 1
        for m in range(mod):
            T[(syr_c(r + m * mod, c) % mod - 1) // 2, src] += 1.0
    return T


def run_l5():
    print("L5  THE TRAP, asserted FALSE:  T_c  !=  T_{c mod 2^k}  as matrices.")
    print("   rstarZ reduces through the residue because it is a CONGRUENCE.  The operator does")
    print("   NOT: it is built from oddPart, which does not factor through the residue mod 2^k.")
    print("   Witness at k=3, n=1:  oddPart(3*1 - 1) = %d  but  oddPart(3*1 + 8 - 1) = %d"
          % (syr_c(1, -1), syr_c(1, 7)))
    print("   k | c    | c mod 2^k | entrywise |T_c - T_res| (times 2^k) | identical?")
    for k in range(3, 9):
        mod = 1 << k
        c = -1
        diff = np.abs(T_full(k, c) - T_full(k, c % mod))
        total = int(round(float(diff.sum())))
        same = total == 0
        if same:
            FAIL.append("L5 T_c == T_{c mod 2^k} at k=%d - the trap would be SAFE, "
                        "which contradicts ShiftedOperator.lean section 4.  Re-derive." % k)
        print("   %d | %-4d | %-9d | %-33d | %s" % (k, c, c % mod, total, str(same)))
    print()


# --------------------------------------------------------------------------- L6

def run_l6():
    print("L6  WHERE EXACTLY THE RESIDUE REDUCTION IS LEGITIMATE - the boundary, both sides.")
    print("   The operator is NOT residue-reducible (L5).  The question this asks is whether")
    print("   the SHELL LAYER is, because that decides how big the Lean mirror of section 2b is.")
    print("   Reason to expect yes: the shell is cut out by v2(3r+c) = j with j <= k-1, which is")
    print("   determined by 3r+c mod 2^(j+1), and j+1 <= k; and (3r+c)/2^j taken mod 2^(k-j)")
    print("   moves by 2^(k-j)*t under c -> c + 2^k*t, i.e. not at all.  Both are CONGRUENCE")
    print("   data mod 2^k.  r ranges over [0,2^k) here - it is NOT the lift window, which is")
    print("   precisely what makes this different from L5.")
    print()
    print("   k | c    | shell identical | sbMap identical | syracuse identical (EXPECT False)")
    for k in (4, 5, 6, 7):
        mod = 1 << k
        for c in NEG_SHIFTS:
            cres = c % mod
            sh_ok = sb_ok = True
            syr_same = True
            saw_shell = False
            for j in range(1, k):
                sz = shell_int(k, c, j)
                sn = shell_int(k, cres, j)
                if sz != sn:
                    sh_ok = False
                    continue
                if sz:
                    saw_shell = True
                for r in sz:
                    if sbmap_int(k, c, j, r) != sbmap_int(k, cres, j, r):
                        sb_ok = False
                    # the FULL odd part, which is what syracuse returns
                    if syr_c(r, c) != syr_c(r, cres):
                        syr_same = False
            if not sh_ok:
                FAIL.append("L6 shell differs at k=%d c=%d" % (k, c))
            if not sb_ok:
                FAIL.append("L6 sbMap differs at k=%d c=%d" % (k, c))
            if saw_shell and syr_same:
                FAIL.append("L6 syracuse agreed through the residue at k=%d c=%d - the "
                            "boundary is not where this script says it is; re-derive." % (k, c))
            print("   %d | %-4d | %-15s | %-15s | %s"
                  % (k, c, str(sh_ok), str(sb_ok), str(syr_same)))
        print()


# --------------------------------------------------------------------------- L7-L9
#
# The three gates below calibrate the ENTRY THEOREM at an integer shift - the next Lean
# statements (`cu_syracuse_affineZ`, `gauss_collapseZ`, `upper_entry_eqZ`,
# `norm_upper_entryZ`).  Nothing above them measures the lift window at an integer shift;
# L5 only measured that the residue shortcut is false, not what the true object is.
#
# The MODEL BELOW IS LEAN'S, NOT THE MATHEMATICIAN'S.  `syr_c` above keeps the sign of the
# odd core, because sign-agnosticism was the right model for the shell layer.  `oddPartZ` in
# Lean is `m.toNat / 2 ^ v2 m.toNat`, which CLAMPS a non-positive argument to 0.  L7 exists
# to find where that clamp bites, so the Lean hypothesis is measured rather than assumed.

def oddpartZ_lean(m):
    """Lean's `IntegerShift.oddPartZ` exactly, clamp included: 0 at every m <= 0."""
    t = max(int(m), 0)
    if t == 0:
        return 0
    while t % 2 == 0:
        t //= 2
    return t


def syracuseZ_lean(c, n):
    """Lean's `IntegerShift.syracuseZ`."""
    return n if n % 2 == 0 else oddpartZ_lean(3 * n + c)


def v2Z(m):
    """Lean's `IntegerShift.v2Z` = v2 |m|."""
    return v2(m)


def tcountZ(c, k, u, r):
    """Lean's `IntegerShift.TcountZ`."""
    mod = 1 << k
    return sum(1 for m in range(mod) if syracuseZ_lean(c, r + m * mod) % mod == u)


def run_l7():
    print("L7  CU AT AN INTEGER SHIFT - is the Syracuse step still affine in the lift, and")
    print("    WHERE does Lean's toNat clamp break it?  This decides the hypothesis on")
    print("    `cu_syracuse_affineZ`, which is the only genuinely new mathematics in step 4b.")
    print("    Claim A: v2Z(3(x + m*2^K) + c) = v2Z(3x + c)          (valuation frozen)")
    print("    Claim B: syracuseZ(c, x + m*2^K) = q0 + 3m*2^(K-v)    (affine)")
    print()
    print("   k | c    | 0<3x+c cases | A holds | B holds | B on the 3x+c<0 cases")
    for k in (4, 5, 6):
        mod = 1 << k
        for c in NEG_SHIFTS + [1, 5]:
            pos_n = 0
            a_ok = b_ok = True
            b_neg_all_ok = True
            saw_neg = False
            for x in range(1, mod, 2):
                val = 3 * x + c
                if val == 0:
                    continue
                v = v2Z(val)
                if v >= k:
                    continue
                q0 = val // (1 << v)          # exact; keeps the sign
                positive = val > 0
                if positive:
                    pos_n += 1
                else:
                    saw_neg = True
                for m in range(mod):
                    lifted = 3 * (x + m * mod) + c
                    if lifted == 0 or v2Z(lifted) != v:
                        a_ok = False
                    rhs = q0 + 3 * m * (1 << (k - v))
                    lhs = syracuseZ_lean(c, x + m * mod)
                    if lhs != rhs:
                        if positive:
                            b_ok = False
                        else:
                            b_neg_all_ok = False
            if not a_ok:
                FAIL.append("L7 valuation NOT frozen at k=%d c=%d - CU is false, stop" % (k, c))
            if not b_ok:
                FAIL.append("L7 affine step fails on a POSITIVE 3x+c at k=%d c=%d - the "
                            "positivity hypothesis is not sufficient; re-scope" % (k, c))
            print("   %d | %-4d | %-12d | %-7s | %-7s | %s"
                  % (k, c, pos_n, str(a_ok), str(b_ok),
                     ("n/a" if not saw_neg else str(b_neg_all_ok))))
        print()
    print("   READ THE LAST COLUMN.  `False` there is the POINT, not a failure: it is the")
    print("   clamp biting, and it is why `cu_syracuse_affineZ` carries `0 < 3x + c`.")
    print("   A `True` there at every shift would mean the hypothesis is unnecessary.")
    print()


def run_l8():
    print("L8  THE GAUSS COLLAPSE AT AN INTEGER SHIFT (`gauss_collapseZ`).  For odd r with")
    print("    v = v2Z(3r + c) < k:   sum_u TcountZ(c,k,u,r) w^(eta u)")
    print("      = 2^k w^(eta * syracuseZ c r)   if 2^v | eta,   else 0.")
    print("   k | c    | rows tested | max |LHS - RHS|")
    for k in (4, 5):
        mod = 1 << k
        w = np.exp(2j * np.pi / mod)
        for c in (-1, 1, 5):
            worst = 0.0
            rows = 0
            for r in range(1, mod, 2):
                val = 3 * r + c
                if val <= 0:
                    continue                      # positivity hypothesis, per L7
                v = v2Z(val)
                if v >= k:
                    continue
                counts = [tcountZ(c, k, u, r) for u in range(mod)]
                for eta in range(mod):
                    lhs = sum(counts[u] * w ** (eta * u) for u in range(mod))
                    if eta % (1 << v) == 0:
                        rhs = mod * w ** (eta * syracuseZ_lean(c, r))
                    else:
                        rhs = 0.0
                    worst = max(worst, abs(lhs - rhs))
                rows += 1
            if worst > 1e-6:
                FAIL.append("L8 Gauss collapse fails at k=%d c=%d, dev %.3e" % (k, c, worst))
            print("   %d | %-4d | %-11d | %.3e" % (k, c, rows, worst))
        print()


def alphaJ(eta, xi, u, j):
    return eta - xi * (1 << j) * u


def resJ(k, eta, xi, u, j):
    return alphaJ(eta, xi, u, j) % (1 << k)


def Sodd(k, alpha, m):
    w = np.exp(2j * np.pi / (1 << k))
    return sum(w ** (alpha * q) for q in range(1, 1 << m, 2))


def clean_entryZ(k, c, eta, xi):
    """Lean's `cleanEntryZ`: the shell-indexed clean character entry, built from TcountZ."""
    mod = 1 << k
    w = np.exp(2j * np.pi / mod)
    total = 0.0 + 0.0j
    for j in range(1, k):
        for r in shell_int(k, c, j):
            col = sum(tcountZ(c, k, u, r) * w ** (eta * u) for u in range(mod))
            total += (col / mod) * w ** (-(xi * r))
    return total


def run_l9():
    print("L9  THE ENTRY THEOREM AT AN INTEGER SHIFT (`upper_entry_eqZ`, `norm_upper_entryZ`).")
    print("    eta = 2^b eta', xi = 2^a xi', eta'/xi' odd, a < b, b + 2 <= k, 2^k | 3u - 1:")
    print("      cleanEntryZ c k eta xi = w^(xi u c) * Sodd(resJ k eta xi u d, k - d),  d = b-a")
    print("    and on the sharp points ||cleanEntryZ|| = 2^(k-d-1).")
    print("   k | c    | (a,b) cases | max |LHS-RHS| | sharp pts | max ||.|| err")
    for k in (5, 6):
        mod = 1 << k
        u = pow(3, -1, mod)                       # odd, and 2^k | 3u - 1
        for c in (-1, 1, 5):
            worst = 0.0
            worst_norm = 0.0
            cases = 0
            sharp = 0
            for b in range(1, k - 1):
                for a in range(0, b):
                    for etap in (1, 3):
                        for xip in (1, 3):
                            eta = (1 << b) * etap
                            xi = (1 << a) * xip
                            if eta >= mod:
                                continue
                            d = b - a
                            lhs = clean_entryZ(k, c, eta, xi)
                            rhs = (np.exp(2j * np.pi / mod) ** (xi * u * c)
                                   * Sodd(k, resJ(k, eta, xi, u, d), k - d))
                            worst = max(worst, abs(lhs - rhs))
                            cases += 1
                            if alphaJ(eta, xi, u, d) % (1 << (k - 1)) == 0:
                                sharp += 1
                                worst_norm = max(worst_norm,
                                                 abs(abs(lhs) - 2.0 ** (k - d - 1)))
            if worst > 1e-6:
                FAIL.append("L9 entry theorem fails at k=%d c=%d, dev %.3e" % (k, c, worst))
            if sharp and worst_norm > 1e-6:
                FAIL.append("L9 sharp-point modulus fails at k=%d c=%d, dev %.3e"
                            % (k, c, worst_norm))
            print("   %d | %-4d | %-11d | %-13.3e | %-9d | %.3e"
                  % (k, c, cases, worst, sharp, worst_norm))
        print()
    print("   The Sodd factor carries NO c.  That is the claim `upper_entry_eqZ` will make,")
    print("   and it is the same claim `upper_entry_eqS` makes at c : Nat - measured here at")
    print("   c = -1, where syracuseZ is a genuinely different map (L5).")
    print()


def run():
    run_l1()
    run_l2()
    run_l3()
    run_l4()
    run_l5()
    run_l6()
    run_l7()
    run_l8()
    run_l9()
    if FAIL:
        print("FAILURES (%d):" % len(FAIL))
        for f in FAIL[:20]:
            print("  " + f)
        return 1
    print("ALL CHECKS PASS.")
    print("  L1  the shift is STILL only a per-entry phase at negative c - H1+H2 hold verbatim.")
    print("  L2  clean upper-cascade block norms are still EXACTLY 2^{-(b-a)/2}.")
    print("  L3  the shell/sbMap bijection SURVIVES at negative c.  Lemma A can be mirrored")
    print("      rather than re-scoped:  Nat r with an INTEGER 3r + c, floor-divided by 2^j,")
    print("      still lands on each odd residue mod 2^(k-j) exactly once.")
    print("  L4  the defect is still rank 1 and still under sqrt3 * 2^{-k/2}.")
    print("  L5  and the residue shortcut TkZ c k = TkS (c mod 2^k) k stays FALSE at every k")
    print("      tested - do not define the integer operator that way.")
    print("  L7  CU survives at an integer shift: the valuation is frozen under the lift at")
    print("      EVERY shift tested, and the affine step holds on every 3x + c > 0.  It")
    print("      FAILS on 3x + c < 0, where Lean's toNat clamps - so `cu_syracuse_affineZ`")
    print("      carries `0 < 3x + c`, which is a MEASURED hypothesis, not a defensive one.")
    print("  L8  the Gauss collapse holds at c = -1, so the column sum still reduces to one")
    print("      phase gated by 2^v | eta - `gauss_collapseZ` is the right statement.")
    print("  L9  the ENTRY THEOREM holds at c = -1: cleanEntryZ = (unimodular) * Sodd(...),")
    print("      the Sodd factor carrying NO c, and modulus exactly 2^(k-d-1) on the sharp")
    print("      points.  That is `upper_entry_eqZ` / `norm_upper_entryZ` before they exist.")
    print("CAVEAT: none of this is a proof, and none of it is a certificate for 3x - 1.  It is")
    print("the measurement that says the Lean mirror (TkZ / upper_entry_eqZ / cleanBlockCLMZ)")
    print("is the right shape before it is written.  c = -3t stays out of scope.")
    return 0


if __name__ == "__main__":
    sys.exit(run())
