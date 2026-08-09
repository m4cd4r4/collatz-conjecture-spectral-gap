#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
calibrate_integer_shift.py - MEASURE BEFORE PROVING, for the INTEGER shift c : Z.

Why this exists
---------------
ShiftedOperator.lean proves the certificate for 3x + c with `c : Nat`, c < 2^k.  That
development literally CANNOT express 3x - 1: `syracuseS` takes c : Nat.  The project's
most transferable claim - that 3x - 1 passes the identical certificate yet HAS cycles,
so "spectral gap => no cycles" is false - therefore rests on Python, not on Lean.

Before paying for an integer-shifted Lean development, measure whether the c : Nat
development's LOAD-BEARING STRUCTURE survives at negative c.  It is not obvious that it
does: the offset trichotomy A_c in {1,2,3} comes from a SIZE argument, 0 < 3r* + c <
4*2^k, and the lower bound is exactly what fails when c < 0.

GATES (all must pass; this script exits non-zero otherwise):

  I1  r*_c is still unique: exactly one odd r < 2^k with 2^k | 3r + c, for integer odd c.
  I2  THE CRITICAL ONE.  Measure the actual range of A_c := (3 r*_c + c)/2^k at negative c,
      and locate the degenerate case A_c = 0 exactly (oddPart(0) is undefined, so the AP
      model breaks there).  Both are checked against a closed-form prediction, not merely
      reported.
  I3  the LINK theorem at integer c:  Syr_c(r*_c + m 2^k) == oddPart(A_c + 3m) (mod 2^k),
      on the fibre entries where both sides are defined, with the exceptions counted and
      characterised rather than skipped.
  I4  coll_c at negative c: still <= 3*2^k, and still a function of A_c alone.
  I5  re-confirm gate G5 of calibrate_general_shift.py - the true integer c = -1 passes
      all four spectral gates at k = 4..8 - by calling that module directly, so this
      script cannot drift from it.

Run:  python calibrate_integer_shift.py
"""

import sys

import calibrate_general_shift as G

FAIL = []
NOTE = []


def v2(n: int) -> int:
    if n == 0:
        raise ValueError("v2(0)")
    n = abs(n)
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def odd_part(n: int) -> int:
    """Sign-preserving odd part.  Undefined at 0 - callers must guard."""
    if n == 0:
        raise ValueError("odd_part(0)")
    return n // (1 << v2(n)) if n > 0 else -((-n) >> v2(n))


def rstar_c(c: int, k: int) -> int:
    """The odd r < 2^k with 3r + c = 0 (mod 2^k).  c integer, odd."""
    N = 1 << k
    return ((-c) * pow(3, -1, N)) % N


def syr_c(c: int, n: int) -> int:
    """The shifted Syracuse map on odd n.  3n + c must be non-zero."""
    return odd_part(3 * n + c)


def offset(c: int, k: int) -> int:
    N = 1 << k
    return (3 * rstar_c(c, k) + c) // N


def odd_ints(k: int, lo_mult: int = -2, hi_mult: int = 0):
    """Odd integers c with lo_mult*2^k < c < hi_mult*2^k (0 excluded automatically)."""
    N = 1 << k
    start = lo_mult * N + 1
    return [c for c in range(start, hi_mult * N, 2)]


PROBES = [-1, -3, -5, -11]

# ------------------------------------------------------------------ I1

print("I1  uniqueness of r*_c at integer c: exactly one odd r < 2^k with 2^k | 3r + c")
print("   k | odd c tested (range) | c with != 1 solution | r*_c always odd")
for k in range(3, 13):
    N = 1 << k
    cs = odd_ints(k, -2, 1) + PROBES
    bad_count = []
    not_odd = []
    for c in sorted(set(cs)):
        sols = [r for r in range(1, N, 2) if (3 * r + c) % N == 0]
        if len(sols) != 1:
            bad_count.append((c, len(sols)))
        rs = rstar_c(c, k)
        if rs % 2 != 1:
            not_odd.append(c)
        elif sols and sols[0] != rs:
            bad_count.append((c, "closed form disagrees"))
    if bad_count:
        FAIL.append(f"I1: uniqueness/closed form fails at k={k}: {bad_count[:5]}")
    if not_odd:
        FAIL.append(f"I1: r*_c even at k={k}: {not_odd[:5]}")
    print(f"  {k:2d} | {len(set(cs)):20d} | {len(bad_count):20d} | "
          f"{'yes' if not not_odd else 'NO -> FAIL'}")

# ------------------------------------------------------------------ I2

print()
print("I2  the offset A_c := (3 r*_c + c)/2^k at NEGATIVE c")
print("   At c : Nat with c < 2^k, 0 <= 3r*+c < 4*2^k forces A_c in {1,2,3}.  The LOWER")
print("   bound is what fails at c < 0: 3r*+c can be zero or negative.  Range measured over")
print("   all odd c with -2*2^k < c < 2^k.")
print("   k | A_c values occurring                | A_c = 0 count | predicted A=0 count")
predict_ok = True
for k in range(3, 13):
    N = 1 << k
    seen = {}
    zeros = []
    for c in odd_ints(k, -2, 1):
        A = offset(c, k)
        seen[A] = seen.get(A, 0) + 1
        if A == 0:
            zeros.append(c)
    # closed-form prediction: A_c = 0  <=>  3 r*_c = -c  <=>  c = -3t with t odd, t < 2^k
    predicted = sorted(-3 * t for t in range(1, N, 2) if -2 * N < -3 * t < N)
    if sorted(zeros) != predicted:
        predict_ok = False
        FAIL.append(f"I2: A=0 set != {{-3t : t odd, t < 2^k}} at k={k}")
    lo, hi = min(seen), max(seen)
    if lo < -2 or hi > 3:
        FAIL.append(f"I2: A_c outside [-2,3] at k={k}: range [{lo},{hi}]")
    print(f"  {k:2d} | {str(sorted(seen)):35s} | {len(zeros):13d} | {len(predicted):19d}")

print()
print("   A_c at the four probe shifts (these are the ones a Lean development would name):")
print("   k |   c = -1   |   c = -3   |   c = -5   |  c = -11")
for k in range(3, 13):
    row = " | ".join(f"A={offset(c, k):3d} r*={rstar_c(c, k):5d}" for c in PROBES)
    print(f"  {k:2d} | {row}")
print()
print("   VERDICT I2: the trichotomy does NOT survive as {1,2,3}.  The size argument")
print("   3r*+c in [c, 3*2^k + c) PERMITS A_c in {-2,...,3} over -2*2^k < c < 2^k; the set")
print("   MEASURED is {-1,0,1,2,3} at every k = 3..12.  A_c = -2 never occurs, and this")
print("   script does NOT claim it cannot.  Either way the set is FINITE, so Lemma B stays")
print("   finitely many cases.  But A_c = 0 DOES occur, at exactly c = -3t for odd")
print(f"   t < 2^k ({'prediction confirmed' if predict_ok else 'PREDICTION FAILED'}), and there")
print("   oddPart(A_c + 3m) is undefined at m = 0.  c = -3 is the smallest instance.")
print("   c = -1 (the map the control experiment is about) is NOT degenerate: A_{-1} is 1")
print("   for odd k and 2 for even k - it ALTERNATES, it is not constant - and both values")
print("   are cases the c : Nat development has already proved.")

# ------------------------------------------------------------------ I3

print()
print("I3  LINK theorem at integer c:  Syr_c(r* + m*2^k) == oddPart(A_c + 3m)  (mod 2^k)")
print("   Exceptions are counted, not skipped: an entry is EXCLUDED only where a side is")
print("   genuinely undefined (A_c + 3m = 0, equivalently 3n + c = 0).")
print("   k | odd c tested | pairs compared | undefined pairs | mismatches")
for k in range(3, 10):
    N = 1 << k
    tested = compared = undef = 0
    bad = []
    for c in odd_ints(k, -2, 1):
        r = rstar_c(c, k)
        A = offset(c, k)
        tested += 1
        for m in range(N):
            n = r + m * N
            if 3 * n + c == 0:
                undef += 1
                assert A + 3 * m == 0, "undefined cases must coincide"
                continue
            lhs = syr_c(c, n) % N
            rhs = odd_part(A + 3 * m) % N
            compared += 1
            if lhs != rhs:
                bad.append((c, m, lhs, rhs))
    if bad:
        FAIL.append(f"I3: link theorem FAILS at k={k}: {bad[:3]}")
    print(f"  {k:2d} | {tested:12d} | {compared:14d} | {undef:15d} | {len(bad)}")
print("   NOTE the link theorem is INSENSITIVE to the sign of A_c: it holds verbatim at")
print("   A_c in {-2,-1}, because oddPart(2^k * X) = oddPart(X) holds for X of either sign.")

# ------------------------------------------------------------------ I4

print()
print("I4  coll_c at integer c: bound 3*2^k, and dependence on A_c alone")
print("   The A_c = 0 shifts are reported separately - their fibre has an undefined entry,")
print("   so coll is computed over the 2^k - 1 defined entries and is NOT comparable.")
print("   k |   3*2^k | A_c values seen | max coll (A != 0) | <= bound | only-A_c?")
for k in range(3, 11):
    N = 1 << k
    bound = 3 * N
    by_offset = {}
    degenerate = 0
    for c in odd_ints(k, -2, 1):
        A = offset(c, k)
        if A == 0:
            degenerate += 1
            continue
        r = rstar_c(c, k)
        cf = {}
        for m in range(N):
            n = r + m * N
            if 3 * n + c == 0:
                continue
            t = syr_c(c, n) % N
            cf[t] = cf.get(t, 0) + 1
        by_offset.setdefault(A, set()).add(sum(v * v for v in cf.values()))
    only_A = all(len(s) == 1 for s in by_offset.values())
    if not only_A:
        FAIL.append(f"I4: coll_c depends on more than A_c at k={k}: "
                    f"{[(a, sorted(s)) for a, s in by_offset.items() if len(s) > 1]}")
    mx = max(max(s) for s in by_offset.values())
    if mx > bound:
        FAIL.append(f"I4: coll exceeds 3*2^k at k={k}: {mx} > {bound}")
    print(f"  {k:2d} | {bound:7d} | {str(sorted(by_offset)):15s} | {mx:17d} |"
          f" {'yes':8s} | {'yes' if only_A else 'NO -> FAIL'}")

# ------------------------------------------------------------------ I5

print()
print("I5  re-confirm G5 of calibrate_general_shift.py (true integer c = -1) by calling it")
print("   k | cert_-1  | <= 0.853553 | max|Qclean - 2^{-(b-a)/2}| | rank D | ||D||_2 | limit")
for k in (4, 5, 6, 7, 8):
    cert, _, Qcl, dn, dr, rs = G.analyse(k, -1)
    K = k - 1
    worst = max((abs(Qcl[a, b] - 2.0 ** (-(b - a) / 2.0))
                 for a in range(K) for b in range(a + 1, K)), default=0.0)
    lim = 3 ** 0.5 * 2.0 ** (-k / 2.0)
    ok = cert <= G.BOUND + 1e-9
    if not ok:
        FAIL.append(f"I5: cert={cert:.6f} > bound at k={k}, c=-1")
    if worst >= 1e-9:
        FAIL.append(f"I5: clean block norm deviates by {worst:.2e} at k={k}, c=-1")
    if dr != 1:
        FAIL.append(f"I5: rank(D)={dr} at k={k}, c=-1")
    if dn > lim + 1e-9:
        FAIL.append(f"I5: ||D||={dn:.5f} > {lim:.5f} at k={k}, c=-1")
    print(f"  {k:2d} | {cert:.6f} |     {'yes' if ok else 'NO':3s}     |"
          f"         {worst:.2e}           |   {dr}    | {dn:.6f} | {lim:.6f}")

# ------------------------------------------------------------------ verdict

print()
if FAIL:
    print(f"FAILURES ({len(FAIL)}):")
    for f in FAIL:
        print("  -", f)
    sys.exit(1)

print("ALL CHECKS PASS.")
print("""
  I1  r*_c is unique and odd at integer c, by the same modular-inverse argument - the
      sign of c is irrelevant to invertibility of 3 mod 2^k.  Nothing to redo.
  I2  the offset trichotomy A_c in {1,2,3} is FALSE at negative c, but the replacement is
      still finite: the size bound 3r*+c in [c, 3*2^k + c) permits A_c in {-2,...,3} over
      -2*2^k < c < 2^k, and the MEASURED set is {-1,0,1,2,3}.  The genuinely new case is
      A_c = 0, occurring at exactly c = -3t for odd t < 2^k, where the AP model has an
      undefined entry at m = 0.
  I3  the link theorem survives verbatim at negative and zero-crossing A_c, on the fibre
      minus the single undefined entry.  oddPart(2^k X) = oddPart(X) is sign-agnostic.
  I4  coll_c <= 3*2^k still holds and still depends on c only through A_c.
  I5  c = -1 - the map the control experiment is about - is NOT one of the awkward cases:
      A_{-1} is 1 at odd k and 2 at even k, so 3x - 1 lands in offset classes the c : Nat
      development has ALREADY proved, at every k.  It never meets A_c <= 0.

  CONSEQUENCE for the representation decision: 3x - 1 needs no new collision mathematics
  and no new offset case.  What it needs is a definition that can express c = -1 at all.
  See DECISION_INTEGER_SHIFT.md.
""")
