# -*- coding: utf-8 -*-
"""
Reduce g_b^2 to the Lemma-B collision count coll(p), p=k-b.

Recursion (verified in probe_selfsimilar.py):  |S_k(2 xi)| = |S_{k-1}(xi)|.
Consequence to pin down exactly here:
  - g_b^2 depends only on p = k-b   (single-index)
  - E_p := sum_{xi odd, 1<=xi<2^p} |S_p(xi)|^2   (odd-frequency energy at scale p)
  - identities to confirm:
        g_b^2 ?= E_p / 4^p
        sum_{all xi in [0,2^p)} |S_p(xi)|^2 ?= 2^p * coll(p)        (Parseval, count on odds)
        E_p ?= 2^p coll(p) - (even-frequency energy)
  and read off the closed form g_b^2 = F(coll(p), coll(p-1), ...).
"""
import numpy as np
from adv_tril_sep_correct import rstar, level_energies
from analytic_proofs import syr


def count_vec_full(p):
    """count over ALL residues mod 2^p (nonzero only on odds): count[t] = #{m: syr(r*+m2^p)=t}."""
    mod = 1 << p
    rs = rstar(p)
    cnt = np.zeros(mod)
    for m in range(mod):
        cnt[syr(rs + m * mod) % mod] += 1.0
    return cnt


def S_full(p):
    return np.fft.fft(count_vec_full(p))   # S_p(xi) = sum_t count[t] exp(-2pi i xi t/2^p)


def odd_energy(p):
    """E_p = sum_{xi odd} |S_p(xi)|^2."""
    S = S_full(p)
    mod = 1 << p
    return sum(abs(S[xi]) ** 2 for xi in range(mod) if xi % 2 == 1)


def coll(p):
    cnt = count_vec_full(p)
    return int(np.sum(cnt.astype(np.int64) ** 2))


if __name__ == "__main__":
    print(f"{'p':>3} {'coll(p)':>10} {'g_p=coll/2^p':>13} {'E_p':>14} {'E_p/4^p':>12} "
          f"{'2^p coll(p)':>13} {'sum|S|^2':>14}")
    for p in range(2, 16):
        cp = coll(p)
        S = S_full(p)
        totS = float(np.sum(np.abs(S) ** 2))
        Ep = odd_energy(p)
        print(f"{p:>3} {cp:>10} {cp/(1<<p):>13.6f} {Ep:>14.2f} {Ep/(4**p):>12.6f} "
              f"{(1<<p)*cp:>13} {totS:>14.2f}")

    print("\nCross-check g_b^2 (from level_energies at scale k) vs E_{k-b}/4^{k-b}:")
    for k in [10, 12, 14]:
        e, _, _ = level_energies(k)
        g2 = e * (1 << k) * (4.0 ** np.arange(len(e)))   # g_b^2 indexed by b
        print(f"  k={k}:")
        for b in range(max(0, k - 8), k - 1):
            p = k - b
            Ep = odd_energy(p)
            print(f"    b={b:2d} p={p:2d}: g_b^2={g2[b]:.6f}  E_p/4^p={Ep/(4**p):.6f}  "
                  f"match={abs(g2[b]-Ep/4**p)<1e-9}")

    # REJECTED HYPOTHESIS (kept as a record): the even-frequency energy is NOT
    # 2^{p-1} coll(p-1) -- the naive cross-scale recursion fails because S_p and S_{p-1}
    # use different parity-delta maps. The CORRECT reduction is the half-shift
    # autocorrelation E_p = 2^{p-1}(coll(p) - A_p); see probe_autocorr.py. match=False below
    # is expected and documents why this route was abandoned.
    print("\n[rejected] is E_p = 2^p coll(p) - 2^{p-1} coll(p-1)?  (expected match=False)")
    for p in range(3, 14):
        Ep = odd_energy(p)
        pred = (1 << p) * coll(p) - (1 << (p - 1)) * coll(p - 1)
        print(f"  p={p:2d}: E_p={Ep:.1f} pred={pred} match={abs(Ep-pred)<1e-6} (use probe_autocorr.py)")
