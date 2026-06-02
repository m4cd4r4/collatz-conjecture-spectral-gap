# -*- coding: utf-8 -*-
"""
Adversarial referee checks of Lemma H proof. Integer-exact wherever possible.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction
import cmath, math
from adv_tril_sep_correct import rstar
from analytic_proofs import syr, v2


def oddcore(x):
    while x % 2 == 0:
        x //= 2
    return x


def a_k(k):
    rs = rstar(k)
    return (3 * rs + 1) // (1 << k)


print("=== CHECK 0: a_k matches the doc claim (a=1 k even, a=2 k odd) ===")
for k in range(2, 16):
    a = a_k(k)
    claim = 1 if k % 2 == 0 else 2
    print(f"  k={k}: a_k={a}  doc_claim={claim}  match={a==claim}")

# ---------------------------------------------------------------------------
# CHECK 1: the parity-split map identity, INTEGER EXACT.
# Claim: split m into 2m' (even) and 2m'+1 (odd).
#   - One parity makes 3m+a_k odd -> O_k = 3m+a_k linear (geometric).
#   - Other parity makes 3m+a_k even, and O_k = OddCore(3m'+a_{k-1}) (structural).
# Verify O_k(m) actually equals these claimed forms for EVERY m, integer-exact,
# and that a_{k-1} is exactly the swapped constant.
# ---------------------------------------------------------------------------
print("\n=== CHECK 1: parity-split map identities, integer-exact, all m ===")
for k in range(2, 15):
    mod = 1 << k
    a = a_k(k)
    am1 = a_k(k - 1) if k - 1 >= 1 else None
    half = 1 << (k - 1)
    geo_ok = True
    struct_ok = True
    which_parity_geo = None
    for mp in range(half):
        # even m = 2m'
        m_even = 2 * mp
        x_even = 3 * m_even + a            # = 6m'+a
        O_even = oddcore(x_even) % mod
        # odd m = 2m'+1
        m_odd = 2 * mp + 1
        x_odd = 3 * m_odd + a              # = 6m'+3+a
        O_odd = oddcore(x_odd) % mod

        # identify geometric parity: the x that is ODD
        if x_even % 2 == 1:
            which_parity_geo = 'even'
            # geometric: O should equal x_even itself mod mod (linear, no oddcore reduction beyond identity)
            if O_even != (x_even % mod):
                geo_ok = False
            # structural: O_odd should equal OddCore(3m'+a_{k-1}) mod mod
            if am1 is not None and O_odd != (oddcore(3 * mp + am1) % mod):
                struct_ok = False
        else:
            which_parity_geo = 'odd'
            if O_odd != (x_odd % mod):
                geo_ok = False
            if am1 is not None and O_even != (oddcore(3 * mp + am1) % mod):
                struct_ok = False
    print(f"  k={k}: geo_parity={which_parity_geo:4s} a_k={a} a_(k-1)={am1} "
          f"geo_linear_ok={geo_ok} struct_=OddCore(3m'+a_(k-1))_ok={struct_ok}")

# ---------------------------------------------------------------------------
# CHECK 2: the geometric-sum vanishing, EXACT via roots of unity arithmetic.
# Geometric part = w_k^{eta c} * sum_{m'=0}^{2^{k-1}-1} (w_k^{6 eta})^{m'}.
# Claim (a): r^{2^{k-1}} = 1 for all integer eta.  r = w_k^{6 eta}.
#   r^{2^{k-1}} = w_k^{6 eta 2^{k-1}} = exp(-2pi i * 6 eta 2^{k-1} / 2^k)
#               = exp(-2pi i * 3 eta) = 1. Check the exponent is integer multiple.
# Claim (b): geometric sum = 0 unless r = 1, i.e. 6 eta == 0 mod 2^k <=> eta == 0 mod 2^{k-1}.
# We check this by EXACT geometric-series logic: sum of N-th roots = N if r=1 else 0
#   (when r^N=1). Determine r=1 condition exactly with modular arithmetic.
# ---------------------------------------------------------------------------
print("\n=== CHECK 2: geometric vanishing, exact modular logic, eta=2*xi ===")
for k in range(2, 16):
    mod = 1 << k
    N = 1 << (k - 1)
    bad = []
    for xi in range(0, N + 1):   # include xi=0 and the boundary
        eta = 2 * xi
        # r = w_k^{6 eta}. r^N = w_k^{6 eta N}. exponent in units of 2pi i / 2^k:
        # check 6*eta*N is a multiple of 2^k (so r^N=1):
        rN_is_one = (6 * eta * N) % mod == 0
        # r==1 condition: 6*eta ==0 mod 2^k
        r_is_one = (6 * eta) % mod == 0
        # the doc reduces r_is_one to eta == 0 mod 2^{k-1} using gcd(3,2)=1:
        # 6 eta == 0 mod 2^k <=> 3*eta == 0 mod 2^{k-1} <=> eta == 0 mod 2^{k-1}
        r_is_one_doc = (eta % N == 0)
        if rN_is_one != True:
            bad.append(('rN!=1', xi))
        if r_is_one != r_is_one_doc:
            bad.append(('redux', xi, r_is_one, r_is_one_doc))
    # which xi in [1,N) have geometric nonzero (r==1)?
    nonzero_xi = [xi for xi in range(1, N) if (6 * (2 * xi)) % mod == 0]
    print(f"  k={k}: rN==1 always & reduction-correct: {len(bad)==0}  "
          f"geo-nonzero xi in [1,N): {nonzero_xi} (doc says only 2^(k-2)={1<<(k-2) if k>=2 else '-'})")
    if bad:
        print(f"        ANOMALIES: {bad[:5]}")

# ---------------------------------------------------------------------------
# CHECK 3: structural part equals S_{k-1}(xi). Done numerically in probe; here
# we check the ROOT-OF-UNITY collapse w_k^{2 xi X} = w_{k-1}^{xi X} exactly,
# and recompute S_{k-1} two independent ways (direct r* map vs the OddCore map).
# ---------------------------------------------------------------------------
print("\n=== CHECK 3: w_k^{2 xi X} = w_{k-1}^{xi X} depends only on X mod 2^{k-1} ===")
# This is exact: w_k^2 = exp(-2pi i *2/2^k) = exp(-2pi i/2^{k-1}) = w_{k-1}. trivially true.
# The real content: S_{k-1}(xi) over OddCore(3m'+a_{k-1}) mod 2^{k-1} matches the
# definition used in the recursion (i.e. the a_{k-1} map IS the scale-(k-1) defect map).
for k in range(3, 13):
    mod1 = 1 << (k - 1)
    a_struct = a_k(k - 1)
    rs1 = rstar(k - 1)
    # S_{k-1} via the OddCore(3m'+a_{k-1}) definition vs via syr(r*_{k-1}+m 2^{k-1}):
    mismatch = 0
    for m in range(mod1):
        viaoddcore = oddcore(3 * m + a_struct) % mod1
        viasyr = syr(rs1 + m * mod1) % mod1
        if viaoddcore != viasyr:
            mismatch += 1
    print(f"  k-1={k-1}: a_struct={a_struct}  OddCore(3m'+a) vs syr(r*+m2^p) mismatches={mismatch}")

# ---------------------------------------------------------------------------
# CHECK 4: Does Lemma H genuinely FAIL at xi = 2^{k-2}? Compute exactly.
# ---------------------------------------------------------------------------
print("\n=== CHECK 4: failure at xi = 2^{k-2} (the exceptional) ===")
import numpy as np
def Svec(k):
    mod = 1 << k
    rs = rstar(k)
    cnt = np.zeros(mod)
    for m in range(mod):
        cnt[syr(rs + m * mod) % mod] += 1.0
    return np.fft.fft(cnt)
for k in range(4, 13):
    Sk = Svec(k)
    Sk1 = Svec(k - 1)
    mod = 1 << k
    xi = 1 << (k - 2)
    lhs = Sk[(2 * xi) % mod]
    rhs = Sk1[xi % (1 << (k - 1))]
    print(f"  k={k}: xi=2^(k-2)={xi}  S_k(2xi)={lhs:.4f}  S_(k-1)(xi)={rhs:.4f}  "
          f"|diff|={abs(lhs-rhs):.4f}  (2xi=Nyquist={1<<(k-1)})")

# ---------------------------------------------------------------------------
# CHECK 5: iterated reduction. Level-b frequencies xi = 2^b m, m odd, 1<=m<2^{k-1-b}.
# Claim: S_k(2^b m) = S_{k-b}(m), each peel legitimate because intermediate arg
# equals step's Nyquist only if m = 2^{k-1-b} (excluded). Check EVERY peel exactly,
# including b=k-2 (m=1).
# ---------------------------------------------------------------------------
print("\n=== CHECK 5: iterated peel, every (k,b,m), check no Nyquist hit ===")
for k in range(4, 13):
    Svecs = {p: Svec(p) for p in range(1, k + 1)}
    worst = 0.0
    bad = []
    nyquist_hits = []
    for b in range(0, k - 1):           # 0 <= b <= k-2
        p_final = k - b
        lim = 1 << (k - 1 - b)          # m < 2^{k-1-b}
        for m in range(1, lim):
            if m % 2 == 0:
                continue
            # iterate the peel; track intermediate args hitting Nyquist of each step
            arg = (1 << b) * m
            hit = False
            for i in range(b):          # peel b factors of 2
                level = k - i
                nyq = 1 << (level - 1)
                if arg % nyq == 0 and arg != 0:
                    # arg == Nyquist (mod 2^level) means 2*(arg/2) hits Nyquist
                    pass
                # the peel S_level(arg) -> S_{level-1}(arg/2) needs arg even and
                # arg != Nyquist 2^{level-1}
                if arg == nyq:
                    hit = True
                arg //= 2
            lhs = Svecs[k][((1 << b) * m) % (1 << k)]
            rhs = Svecs[p_final][m % (1 << p_final)]
            d = abs(lhs - rhs)
            worst = max(worst, d)
            if d > 1e-6:
                bad.append((b, m, d))
            if hit:
                nyquist_hits.append((b, m))
    print(f"  k={k}: worst|S_k(2^b m)-S_(k-b)(m)|={worst:.2e}  failures={len(bad)}  "
          f"intermediate-Nyquist-hits={len(nyquist_hits)}")
    if bad:
        print(f"        BAD: {bad[:5]}")
    if nyquist_hits:
        print(f"        NYQUIST HITS (should be none if m<2^(k-1-b)): {nyquist_hits[:5]}")
