# -*- coding: utf-8 -*-
"""
Lemma C reduced to:  Delta-energy  D_p := sum_t (count[t]-count[t+2^{p-1}])^2 <= (9/4) 2^p.
Equivalently coll(p)-A_p = D_p/2 <= (9/8)2^p.

Here we (1) verify D_p/2 = coll-A, (2) study count[t] and the half-shift difference
count[t]-count[t+half] to see what values they take (toward an elementary proof).

count[t] = #{m in [0,2^p): syr(r*+m 2^p) == t},  supported on odd t in [0,2^p).
The map is m -> OddCore(3m + 2^delta), delta = v2(3r*+1)-p in {0,1}.
"""
import numpy as np
from collections import Counter
from adv_tril_sep_correct import rstar
from analytic_proofs import syr


def count_vec(p):
    mod = 1 << p
    rs = rstar(p)
    cnt = np.zeros(mod, dtype=np.int64)
    for m in range(mod):
        cnt[syr(rs + m * mod) % mod] += 1
    return cnt


if __name__ == "__main__":
    print("Verify D_p/2 = coll-A, and the bound D_p <= (9/4)2^p:")
    print(f"{'p':>3} {'D_p=sum dif^2':>13} {'D_p/2':>10} {'coll-A':>10} {'(9/4)2^p':>10} "
          f"{'D_p/2^p':>9} {'<=9/4?':>7}")
    for p in range(2, 17):
        cnt = count_vec(p)
        mod = 1 << p
        half = mod >> 1
        dif = cnt - np.roll(cnt, half)
        D = int(np.sum(dif ** 2))
        coll = int(np.sum(cnt ** 2))
        A = int(np.sum(cnt * np.roll(cnt, half)))
        print(f"{p:>3} {D:>13} {D//2:>10} {coll-A:>10} {int(2.25*mod):>10} "
              f"{D/mod:>9.5f} {str(D/mod<=2.25+1e-9):>7}")

    print("\nValue distribution of count[t] (odd t) and of the half-shift difference:")
    for p in [8, 10, 12]:
        cnt = count_vec(p)
        mod = 1 << p
        odd = cnt[1::2]
        dif = (cnt - np.roll(cnt, mod >> 1))[1::2]   # differences on odd t
        print(f"  p={p}: count[odd] values -> {dict(sorted(Counter(odd.tolist()).items()))}")
        print(f"        (count[t]-count[t+half]) on odd t -> "
              f"{dict(sorted(Counter(dif.tolist()).items()))}")
        # how many nonzero differences, and their magnitudes
        nz = dif[dif != 0]
        print(f"        #nonzero dif = {len(nz)} of {len(dif)} odd t; "
              f"max|dif|={np.abs(dif).max()}; sum dif^2 (odd t)={int(np.sum(dif**2))}")
