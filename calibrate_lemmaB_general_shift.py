#!/usr/bin/env python3
"""
Calibration for Lemma B at a general odd shift, run BEFORE any Lean is written.

Lemma B at c = 1 (CollisionBound.lean) rests on ONE structural accident:

    3 r*_1 + 1 = 2^{ek k}   exactly a power of two,

so that 3(r* + m 2^k) + 1 = 2^k (a + 3m) with a = 2^{ek k - k} in {1, 2}, and the
defect fibre becomes the arithmetic progression a + 3m.  `coll(k) <= 3 * 2^k` is then a
statement about that AP.

The question this script answers, and the reason it exists rather than a Lean file:

    what replaces `a in {1,2}` for a general odd shift c?

The answer is NOT obvious from the c = 1 proof, because 3r*_c + c is in general NOT a
power of two -- rstarS is defined by a modular inverse, not by a repunit closed form.

GATES (all must pass; this script exits non-zero otherwise):

  B1  2^k | 3 r*_c + c, and A_c := (3 r*_c + c) / 2^k lies in {1, 2, 3}, for every odd
      c < 2^k.  This is the general-c replacement for apA in {1,2}.
  B2  A_c = 3 really occurs -- the a = 3 case is not vacuous, and neither are 1 and 2.
  B3  THE MODEL IDENTITY: the true shifted Syracuse defect fibre equals the AP model,
          Syr_c(r*_c + m 2^k) mod 2^k  ==  oddPart(A_c + 3m) mod 2^k.
      This is the general-c analogue of CollisionBound.syracuse_defect_fibre, and it is
      exactly what BRIEF_LEMMA_A_GENERAL_SHIFT.md §5 records as missing.
  B4  coll_c(k) <= 3 * 2^k for every odd c < 2^k -- Lemma B's bound itself.
  B5  the three AP offsets give only three distinct collision counts, i.e. coll_c(k)
      depends on c ONLY through A_c.  If true, Lemma B for general c is three cases,
      not a family.
  B6  a = 3 is the extremal case, and coll_3(k) = 3*2^k - 2 (ShiftedOperator.coll3_closed),
      so the bound 3*2^k is SHARP to an additive 2 and cannot be improved to c * 2^k
      for any c < 3.

Run:  python calibrate_lemmaB_general_shift.py
"""

import sys

FAIL = []


def v2(n: int) -> int:
    if n == 0:
        raise ValueError("v2(0)")
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def odd_part(n: int) -> int:
    return n >> v2(n)


def rstar_c(c: int, k: int) -> int:
    """The unique odd r < 2^k with 3r + c = 0 (mod 2^k)."""
    N = 1 << k
    inv3 = pow(3, -1, N)
    return ((-c) * inv3) % N


def syr_c(c: int, n: int) -> int:
    """The shifted Syracuse map on odd n."""
    return odd_part(3 * n + c)


def coll_from_offset(a: int, k: int) -> int:
    """coll for the AP model  oddPart(a + 3m) mod 2^k,  m < 2^k."""
    N = 1 << k
    cf = {}
    for m in range(N):
        t = odd_part(a + 3 * m) % N
        cf[t] = cf.get(t, 0) + 1
    return sum(v * v for v in cf.values())


def coll_from_true_fibre(c: int, k: int) -> int:
    """coll computed from the genuine shifted Syracuse fibre over r*_c."""
    N = 1 << k
    r = rstar_c(c, k)
    cf = {}
    for m in range(N):
        t = syr_c(c, r + m * N) % N
        cf[t] = cf.get(t, 0) + 1
    return sum(v * v for v in cf.values())


# ---------------------------------------------------------------- B1, B2

print("B1/B2  A_c := (3 r*_c + c) / 2^k  for every odd c < 2^k")
print("   k | #odd c |  A_c = 1 |  A_c = 2 |  A_c = 3 | any A_c outside {1,2,3}")
seen_offsets = set()
for k in range(3, 13):
    N = 1 << k
    counts = {1: 0, 2: 0, 3: 0}
    outside = []
    for c in range(1, N, 2):
        r = rstar_c(c, k)
        t = 3 * r + c
        if t % N != 0:
            FAIL.append(f"B1: 2^{k} does not divide 3*r*+c at c={c}")
            continue
        A = t // N
        seen_offsets.add(A)
        if A in counts:
            counts[A] += 1
        else:
            outside.append((c, A))
    if outside:
        FAIL.append(f"B1: A_c outside {{1,2,3}} at k={k}: {outside[:5]}")
    print(f"  {k:2d} | {N // 2:6d} | {counts[1]:8d} | {counts[2]:8d} | {counts[3]:8d} |"
          f" {'YES -> FAIL' if outside else 'none'}")

if seen_offsets != {1, 2, 3}:
    FAIL.append(f"B2: offsets seen = {sorted(seen_offsets)}, expected exactly {{1,2,3}}")
print(f"\n  offsets actually occurring: {sorted(seen_offsets)}"
      f"  ({'all three, none vacuous' if seen_offsets == {1, 2, 3} else 'UNEXPECTED'})")

# ---------------------------------------------------------------- B3

print("\nB3  THE MODEL IDENTITY: true shifted fibre == AP model oddPart(A_c + 3m)")
print("   k | odd c tested | fibre values compared | mismatches")
for k in range(3, 11):
    N = 1 << k
    tested = 0
    compared = 0
    bad = []
    for c in range(1, N, 2):
        r = rstar_c(c, k)
        A = (3 * r + c) // N
        tested += 1
        for m in range(N):
            lhs = syr_c(c, r + m * N) % N
            rhs = odd_part(A + 3 * m) % N
            compared += 1
            if lhs != rhs:
                bad.append((c, m, lhs, rhs))
    if bad:
        FAIL.append(f"B3: model identity FAILS at k={k}: {bad[:3]}")
    print(f"  {k:2d} | {tested:12d} | {compared:21d} | {len(bad)}")

# ---------------------------------------------------------------- B4, B5

print("\nB4/B5  coll_c(k) <= 3*2^k, and coll_c depends on c only through A_c")
print("   k |    3*2^k |  coll(A=1) |  coll(A=2) |  coll(A=3) | max coll | margin | only-A_c?")
for k in range(3, 12):
    N = 1 << k
    bound = 3 * N
    by_offset = {}
    per_c = {}
    for c in range(1, N, 2):
        r = rstar_c(c, k)
        A = (3 * r + c) // N
        val = coll_from_true_fibre(c, k)
        per_c[c] = (A, val)
        by_offset.setdefault(A, set()).add(val)
    only_A = all(len(s) == 1 for s in by_offset.values())
    if not only_A:
        FAIL.append(f"B5: coll_c depends on more than A_c at k={k}: "
                    f"{[(a, sorted(s)) for a, s in by_offset.items() if len(s) > 1]}")
    vals = {a: sorted(s)[0] for a, s in by_offset.items()}
    mx = max(v for _, v in per_c.values())
    if mx > bound:
        FAIL.append(f"B4: coll exceeds 3*2^k at k={k}: {mx} > {bound}")
    print(f"  {k:2d} | {bound:8d} | {vals.get(1, -1):10d} | {vals.get(2, -1):10d} |"
          f" {vals.get(3, -1):10d} | {mx:8d} | {bound - mx:6d} |"
          f" {'yes' if only_A else 'NO -> FAIL'}")

# ---------------------------------------------------------------- B6

print("\nB6  a = 3 is extremal, and coll_3(k) = 3*2^k - 2  (ShiftedOperator.coll3_closed)")
print("   k |  coll_1 |  coll_2 |  coll_3 |   3*2^k | coll_3 = 3*2^k - 2 | argmax offset")
for k in range(3, 13):
    N = 1 << k
    bound = 3 * N
    c1 = coll_from_offset(1, k)
    c2 = coll_from_offset(2, k)
    c3 = coll_from_offset(3, k)
    closed = (c3 == bound - 2)
    if not closed:
        FAIL.append(f"B6: coll_3({k}) = {c3}, expected {bound - 2}")
    arg = max([(c1, 1), (c2, 2), (c3, 3)])[1]
    if arg != 3:
        FAIL.append(f"B6: a=3 is not extremal at k={k} (argmax = {arg})")
    print(f"  {k:2d} | {c1:7d} | {c2:7d} | {c3:7d} | {bound:7d} |"
          f" {'yes' if closed else 'NO -> FAIL':18s} | {arg}")

# ---------------------------------------------------------------- verdict

print()
if FAIL:
    print("FAILURES:")
    for f in FAIL:
        print("  -", f)
    sys.exit(1)

print("ALL CHECKS PASS.")
print("""
  B1  3 r*_c + c = 2^k * A_c with A_c in {1,2,3}, every odd c < 2^k.  This is the
      general-c replacement for CollisionBound.apA in {1,2}, and it needs NO valuation
      argument: it follows from 2^k | 3r*+c (rstarS_spec, already proved) plus the size
      bound r* < 2^k, which forces 3r*+c < 4*2^k.
  B3  the AP model IS the true shifted defect fibre.  This is the theorem
      BRIEF_LEMMA_A_GENERAL_SHIFT.md §5 records as missing, and it is provable from B1
      alone -- oddPart(2^k * X) = oddPart(X).
  B5  coll_c depends on c ONLY through A_c, so Lemma B for general c is THREE CASES,
      not an infinite family:  a = 1 and a = 2 are CollisionBound's existing cases
      (apA), and a = 3 is ShiftedOperator.coll3_closed, already proved.
  B6  a = 3 is extremal and coll_3(k) = 3*2^k - 2, so the bound 3*2^k is sharp to an
      additive 2 -- it cannot be lowered to any C*2^k with C < 3.

  CONSEQUENCE: Lemma B at a general odd shift needs no new collision mathematics.  What
  it needs is the LINK theorem (B3) and the offset trichotomy (B1).  Both are small.
""")
