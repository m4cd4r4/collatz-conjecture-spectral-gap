# -*- coding: utf-8 -*-
"""
Reduce E_p (odd-frequency energy) to a half-shift autocorrelation -- an elementary
counting object in the same family as Lemma B's collision count.

Identity to confirm:
  E_p = sum_{xi odd} |S_p(xi)|^2 = 2^{p-1} ( coll(p) - A_p ),
  where coll(p) = sum_t count[t]^2,
        A_p     = sum_t count[t] * count[(t + 2^{p-1}) mod 2^p]   (lag-2^{p-1} autocorrelation).
Hence  g_b^2 = E_p/4^p = (coll(p) - A_p) / 2^{p+1},  p = k-b.

Lemma C  <=>  coll(p) - A_p <= (9/8) 2^p   for all p>=2.
We confirm the identity and tabulate coll(p), A_p, and the normalised
  c_p := coll(p)/2^p  and  a_p := A_p/2^p,  so g_b^2 = (c_p - a_p)/2.
count[t] = #{m in [0,2^p): syr(r*+m 2^p) == t mod 2^p}, supported on odd t.
"""
import numpy as np
from adv_tril_sep_correct import rstar
from analytic_proofs import syr


def count_vec(p):
    mod = 1 << p
    rs = rstar(p)
    cnt = np.zeros(mod, dtype=np.int64)
    for m in range(mod):
        cnt[syr(rs + m * mod) % mod] += 1
    return cnt


def stats(p):
    cnt = count_vec(p)
    mod = 1 << p
    coll = int(np.sum(cnt ** 2))
    half = mod >> 1
    shifted = np.roll(cnt, half)
    A = int(np.sum(cnt * shifted))
    # E_p directly
    S = np.fft.fft(cnt.astype(float))
    Ep = sum(abs(S[xi]) ** 2 for xi in range(mod) if xi % 2 == 1)
    return coll, A, Ep


if __name__ == "__main__":
    print(f"{'p':>3} {'coll(p)':>10} {'A_p':>10} {'E_p':>14} {'2^(p-1)(coll-A)':>16} "
          f"{'match':>6} {'c_p':>9} {'a_p':>9} {'(c_p-a_p)/2=g^2':>15}")
    for p in range(2, 17):
        coll, A, Ep = stats(p)
        pred = (1 << (p - 1)) * (coll - A)
        cp = coll / (1 << p)
        ap = A / (1 << p)
        print(f"{p:>3} {coll:>10} {A:>10} {Ep:>14.1f} {pred:>16} "
              f"{str(abs(Ep-pred)<1e-6):>6} {cp:>9.5f} {ap:>9.5f} {(cp-ap)/2:>15.6f}")
    print("\nLemma C  <=>  coll(p) - A_p <= (9/8) 2^p,  i.e.  c_p - a_p <= 9/8 = 1.125")
    print("(sup of g^2 is 9/16 => sup of c_p-a_p is 9/8, attained at p=4)")
    print("\nLimits: c_p -> 31/12 = 2.58333 (Lemma B sharp).  a_p -> ?")
    for p in [12, 14, 16]:
        coll, A, Ep = stats(p)
        print(f"  p={p}: a_p={A/(1<<p):.6f}  c_p-a_p={(coll-A)/(1<<p):.6f}  "
              f"31/12 - a_p = {31/12 - A/(1<<p):.6f}")
