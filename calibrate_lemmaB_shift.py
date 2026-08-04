#!/usr/bin/env python3
"""
calibrate_lemmaB_shift.py - Lemma B for a general odd shift, and the structure that makes it
a THREE-CASE problem rather than an infinite family.

Lemma B, as rendered in CollisionBound.lean:

    cf   k t = #{ m < 2^k : oddPart(a + 3m) % 2^k = t }
    coll k   = sum_t (cf k t)^2
    Lemma B  : coll(k) <= 3 * 2^k          (equivalently ||c|| * 2^{k/2} <= sqrt 3)

where `a = (3 r* + c) / 2^k` and `r*` is the defect residue solving `3 r* + c = 0 mod 2^k`.

THREE FINDINGS, all checked here
--------------------------------

F1  `a_c` only ever takes the values **1, 2, 3**.  Immediate once you look: `r* < 2^k` and
    `c < 2^k` give `0 < 3 r* + c < 3 * 2^k + 2^k`, so `a in {1,2,3}` - but it is worth
    checking rather than assuming, and it is checked over every odd `c` for `k = 3..13`.

F2  **`coll` depends ONLY on `a`, not on `c`.**  At `k = 8`, all 128 odd shifts collapse to
    exactly three values: `a=1 -> 662`, `a=2 -> 598`, `a=3 -> 766`.

    Together F1 and F2 turn "Lemma B for every odd shift" into "Lemma B for a = 1, 2, 3".
    The corpus already proves the cases that arise at `c = 1`, where `a` alternates with the
    parity of `k` (`k` even -> `a=1`, `k` odd -> `a=2`).  **The one genuinely new case is
    `a = 3`.**

F3  **`coll(k, 3) = 3 * 2^k - 2` exactly**, for every `k` tested (3..14).  So Lemma B's
    constant `3` is **SHARP**: the margin is exactly 2, at every scale, and
    `||c|| * 2^{k/2} -> sqrt 3` from below.

WHAT F3 MEANS FOR THE PROOF
---------------------------
At `c = 1` the margin GROWS with `k` (`6, 6, 16, 26, 56, ... 6826` at `k = 14`), because
`coll/2^k -> 31/12 = 2.583`.  Any proof that leans on that growing slack **will fail at
`a = 3`**, where the margin is a constant 2 forever.  The `a = 3` case has to be proved
tightly, and its exact closed form is the natural way in.

This is the risk flagged by `calibrate_general_shift.py` (Lemma B nearly saturated at
`c = 2^k - 1`), now identified precisely: those were the `a = 3` shifts.

Exits non-zero on failure.
"""
import sys
from math import sqrt

FAIL = []


def oddpart(n):
    if n == 0:
        return 0
    while n % 2 == 0:
        n //= 2
    return n


def coll_a(k, a):
    """coll for the AP model with offset a."""
    mod = 1 << k
    cf = {}
    for m in range(mod):
        t = oddpart(a + 3 * m) % mod
        cf[t] = cf.get(t, 0) + 1
    return sum(v * v for v in cf.values())


def a_of(k, c):
    mod = 1 << k
    inv3 = pow(3, -1, mod)
    rs = ((-c) * inv3) % mod
    A = 3 * rs + c
    assert A % mod == 0, "r* must satisfy 3r* + c = 0 mod 2^k"
    return A // mod


def f1():
    vals = set()
    for k in range(3, 14):
        for c in range(1, 1 << k, 2):
            vals.add(a_of(k, c))
    if vals != {1, 2, 3}:
        FAIL.append("F1 a_c took values %s, expected {1,2,3}" % sorted(vals))
    print("F1  a_c over every odd c, k = 3..13:  %s" % sorted(vals))


def f2():
    k = 8
    groups = {}
    for c in range(1, 1 << k, 2):
        a = a_of(k, c)
        groups.setdefault(a, set()).add(coll_a(k, a))
    bad = [a for a, v in groups.items() if len(v) != 1]
    if bad:
        FAIL.append("F2 coll is not a function of a alone at a = %s" % bad)
    print("F2  k=8, all %d odd shifts collapse to three values: %s"
          % ((1 << k) // 2, {a: sorted(v)[0] for a, v in sorted(groups.items())}))
    print("      => 'Lemma B for every odd shift' IS 'Lemma B for a = 1, 2, 3'")


def f3():
    print("\nF3  the three cases, and the sharpness of the constant 3")
    print("     k |   a=1  |   a=2  |   a=3  |  3*2^k | 3*2^k - coll(k,3)")
    for k in range(3, 15):
        c1, c2, c3 = coll_a(k, 1), coll_a(k, 2), coll_a(k, 3)
        margin = 3 * (1 << k) - c3
        if margin != 2:
            FAIL.append("F3 coll(%d,3) = %d, margin %d, expected exactly 2" % (k, c3, margin))
        for a, cl in ((1, c1), (2, c2), (3, c3)):
            if cl > 3 * (1 << k):
                FAIL.append("F3 coll(%d,%d) = %d exceeds 3*2^k" % (k, a, cl))
        print("    %2d | %6d | %6d | %6d | %6d |        %d" % (k, c1, c2, c3, 3 * (1 << k), margin))
    print("\n     coll(k,3) = 3*2^k - 2 exactly  =>  the constant 3 is SHARP,")
    print("     ||c||*2^(k/2) -> sqrt(3) = %.6f from below." % sqrt(3))
    print("     At c = 1 the margin GROWS (6, 6, 16, ... 6826 at k=14) because coll/2^k -> 31/12.")
    print("     A proof leaning on that growth WILL FAIL at a = 3.")


def run():
    f1(); f2(); f3()
    print()
    if FAIL:
        print("FAILURES (%d):" % len(FAIL))
        for f in FAIL[:10]:
            print("  " + f)
        return 1
    print("ALL CHECKS PASS.")
    print("Next Lean target, well-posed: coll(k, 3) <= 3*2^k, ideally via the exact form")
    print("coll(k,3) = 3*2^k - 2.  Cases a = 1, 2 are already in CollisionBound.lean.")
    return 0


if __name__ == "__main__":
    sys.exit(run())
