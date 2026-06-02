# -*- coding: utf-8 -*-
"""
Shell decomposition of coll(p)-A_p = (1/2)D_p, toward proving <= (9/8)2^p.

From Lemma B: cf[t] = #{j: t in R_j}, R_j = {(x/2^j) mod 2^p : x in A_j}, A_j={a+3m: v2=j},
|A_j|=|R_j|=2^{p-1-j} (j=0..p-1) + top atom. FACT 1: cf is 0/1 per shell.

With h=2^{p-1}:
  coll - A = (1/2) sum_t (cf[t]-cf[t+h])^2
           = sum_j (|R_j| - s_j)  +  cross,
  s_j   = |R_j cap (R_j - h)|                          (t with both t,t+h in R_j)
  cross = sum_{j!=j'} ( |R_j cap R_j'| - |R_j cap (R_j' - h)| ) / ... (signed, computed directly)
We compute every piece exactly and look for a clean closed form / bound.
"""
import numpy as np
from adv_tril_sep_correct import rstar
from analytic_proofs import v2


def shells(p):
    """Return R_j as sets of residues mod 2^p, using the a+3m AP model."""
    mod = 1 << p
    rs = rstar(p)
    a = (3 * rs + 1) // mod          # in {1,2}
    Rs = {}
    for m in range(mod):
        x = a + 3 * m
        j = v2(x)
        if j >= p:                   # top atom -> oddpart 0 mod 2^p region; handle as j=p bucket
            j = p
        u = (x >> j) % mod
        Rs.setdefault(j, set()).add(u)
    return Rs, a


def decompose(p):
    mod = 1 << p
    h = mod >> 1
    Rs, a = shells(p)
    # rebuild cf to confirm
    cf = np.zeros(mod, dtype=np.int64)
    for j, R in Rs.items():
        for u in R:
            cf[u] += 1
    coll = int(np.sum(cf ** 2))
    A = int(np.sum(cf * np.roll(cf, h)))
    # diagonal pieces
    diag_term = 0
    Sj = {}
    for j, R in Rs.items():
        sj = len(R & {(u + h) % mod for u in R})
        Sj[j] = sj
        diag_term += len(R) - sj
    # cross (signed) computed as remainder
    cross = (coll - A) - diag_term
    return coll, A, coll - A, diag_term, cross, Sj, Rs, a


if __name__ == "__main__":
    print(f"{'p':>3} {'coll-A':>8} {'(9/8)2^p':>9} {'diag=Σ(|Rj|-sj)':>16} {'cross':>8} "
          f"{'Σ|Rj|':>7} {'Σsj':>6}")
    for p in range(2, 15):
        coll, A, cmA, diag, cross, Sj, Rs, a = decompose(p)
        sumR = sum(len(R) for R in Rs.values())
        sumS = sum(Sj.values())
        print(f"{p:>3} {cmA:>8} {int(1.125*(1<<p)):>9} {diag:>16} {cross:>8} {sumR:>7} {sumS:>6}")
    # detailed shell profile at one p
    print("\nShell profile at p=12 (a, |R_j|, s_j):  a=", end="")
    coll, A, cmA, diag, cross, Sj, Rs, a = decompose(12)
    print(a)
    for j in sorted(Rs):
        print(f"  j={j:2d}: |R_j|={len(Rs[j]):5d}  s_j={Sj[j]:5d}  |R_j|-s_j={len(Rs[j])-Sj[j]:5d}")
    print(f"  Σ(|R_j|-s_j)={diag}  cross={cross}  total coll-A={cmA}  target≤{int(1.125*4096)}")
