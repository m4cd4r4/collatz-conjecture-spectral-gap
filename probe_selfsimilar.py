# -*- coding: utf-8 -*-
"""
Hunt for the self-similar recursion behind Lemma C.

Established: c^{(k)} = pushforward of uniform m in [0,2^k) under m -> OddCore(3m+2^delta) mod 2^k,
delta = v2(3r*+1)-k in {0,1} (0 for k even, 1 for k odd).
Exponential sum:  S_k(xi) = sum_{m=0}^{2^k-1} w^{xi * OddCore(3m+2^delta)},  w=exp(-2pi i/2^k).
   |<chi_xi,c>| = |S_k(xi)| / (2^k sqrt(N)),  N=2^{k-1}.

Tests:
  (A) fold_{2^j}(c^{(k)}) vs c^{(k-j)} : is the folded distribution a smaller-scale covector?
  (B) exponential-sum recursion: relate S_k(xi) to a smaller sum.
  (C) closed form of |S_k(xi)| -- does it factor over the binary digits of xi?
"""
import numpy as np
from adv_tril_sep_correct import covector_state, rstar
from analytic_proofs import v2, syr


def oddcore(x):
    while x % 2 == 0:
        x //= 2
    return x


def expsum(k, xi):
    """S_k(xi) = sum_m w^{xi OddCore(3m+1 or +2)}, exact via the syr(r*+m2^k) identity."""
    mod = 1 << k
    rs = rstar(k)
    w = np.exp(-2j * np.pi / mod)
    acc = 0j
    for m in range(mod):
        t = syr(rs + m * mod) % mod
        acc += w ** (xi * t)
    return acc


def fold(c, twoj):
    N = len(c)
    return c.reshape(twoj, N // twoj).sum(axis=0)


if __name__ == "__main__":
    np.set_printoptions(linewidth=200, suppress=True, precision=8)

    # (A) fold vs smaller-scale covector
    print("=== (A) fold_{2^j}(c^{(k)}) vs c^{(k-j)} ===")
    for k in [10, 12]:
        c, _ = covector_state(k)
        for j in [1, 2]:
            fc = fold(c, 1 << j)            # on 2^{k-1-j} points
            csmall, _ = covector_state(k - j)  # on 2^{k-j-1} points (== same count)
            same = len(fc) == len(csmall) and np.allclose(fc, csmall, atol=1e-12)
            reldiff = np.max(np.abs(fc - csmall)) if len(fc) == len(csmall) else float('nan')
            print(f"  k={k} j={j}: len(fold)={len(fc)} len(c[k-j])={len(csmall)} "
                  f"equal={same} maxdiff={reldiff:.2e}")

    # (C) closed form of |S_k(xi)|: factor over binary structure of xi = 2^b * m_odd
    print("\n=== (C) |S_k(xi)| structure;  scaled = |S|/2^k, and *2^b (b=v2(xi)) ===")
    k = 12
    mod = 1 << k
    rs = rstar(k)
    w = np.exp(-2j * np.pi / mod)
    # full sum vector S[xi] via FFT of the count distribution
    cnt = np.zeros(mod)
    for m in range(mod):
        t = syr(rs + m * mod) % mod
        cnt[t] += 1.0          # counts indexed by odd residue t in [0,2^k)
    # S_k(xi) = sum_t cnt[t] w^{xi t} = (conj) FFT over Z/2^k
    S = np.fft.fft(cnt[::1], n=mod)   # sum_t cnt[t] exp(-2pi i xi t/2^k) = FFT(cnt)[xi]
    Smag = np.abs(S)
    print(f"  k={k}: |S(0)|={Smag[0]:.1f} (=2^k={mod})")
    for m in [1, 3, 5, 7]:
        vals = []
        for b in range(k):
            xi = (1 << b) * m
            if xi < mod:
                vals.append(Smag[xi] / mod * (2.0 ** b))   # |S|/2^k * 2^b
        print(f"  m={m}: |S(2^b m)|/2^k * 2^b across b = {np.array(vals)}")

    # (B) exponential-sum recursion S_k(2 xi) vs S_{k-1}(xi)
    print("\n=== (B) S_k(2 xi)/2 vs S_{k-1}(xi) (parity j=1 step) ===")
    for k in [8, 10]:
        modk = 1 << k
        rsk = rstar(k)
        cntk = np.zeros(modk)
        for m in range(modk):
            cntk[syr(rsk + m * modk) % modk] += 1.0
        Sk = np.fft.fft(cntk)
        modk1 = 1 << (k - 1)
        rsk1 = rstar(k - 1)
        cntk1 = np.zeros(modk1)
        for m in range(modk1):
            cntk1[syr(rsk1 + m * modk1) % modk1] += 1.0
        Sk1 = np.fft.fft(cntk1)
        # compare |S_k(2 xi)| vs |S_{k-1}(xi)| for xi in [0, 2^{k-1})
        ratios = []
        for xi in range(1, min(16, modk1)):
            a = abs(Sk[(2 * xi) % modk]); b = abs(Sk1[xi % modk1])
            ratios.append(a / b if b > 1e-9 else float('nan'))
        print(f"  k={k}: |S_k(2xi)|/|S_{{k-1}}(xi)| for xi=1..15 = {np.array(ratios)}")
