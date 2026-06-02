# -*- coding: utf-8 -*-
"""
Verify the elementary proof of the homometry  S_k(2 xi) = S_{k-1}(xi)  (exact, complex),
for all xi with 2 xi != 2^{k-1} (Nyquist) and xi != 0 (Perron).

Proof structure (split S_k by parity of m):
  S_k(xi) = sum_{m=0}^{2^k-1} w_k^{xi O_k(m)},  O_k(m) = OddCore(3m + a_k) mod 2^k,  w_k=exp(-2pi i/2^k),
  a_k = 1 (k even) or 2 (k odd).
Write m = 2m' (even) or 2m'+1 (odd), m' in [0, 2^{k-1}).

  k EVEN (a_k=1):
    even m: 3(2m')+1 = 6m'+1 ODD -> O = 6m'+1.   GEOMETRIC part.
    odd  m: 3(2m'+1)+1 = 6m'+4 = 2(3m'+2) -> O = OddCore(3m'+2) = the a=2 map.  <-- a_{k-1}=2 (k-1 odd)
  k ODD (a_k=2):
    even m: 6m'+2 = 2(3m'+1) -> O = OddCore(3m'+1) = the a=1 map.   <-- a_{k-1}=1 (k-1 even)
    odd  m: 6m'+5 ODD -> O = 6m'+5.   GEOMETRIC part.

The GEOMETRIC part (sum of w_k^{xi*(6m'+c)} over m'=0..2^{k-1}-1) has ratio w_k^{6 xi};
its closed form vanishes unless w_k^{6 xi}=1, i.e. 6 xi == 0 mod 2^k, i.e. xi == 0 mod 2^{k-1}
(since gcd(3,2)=1) -> xi in {0, 2^{k-1}}. For xi in [1, 2^{k-1}) the geometric part is 0
EXCEPT we are evaluating S_k at argument 2 xi; the geometric vanishes unless 2 xi in {0, 2^{k-1}}.
The NON-geometric part is exactly sum_{m'} w_k^{2 xi * O_{k-1}-map(m')}, and since
w_k^{2 xi *.} = w_{k-1}^{xi *.} depends only on the value mod 2^{k-1}, it equals S_{k-1}(xi).
"""
import numpy as np
from adv_tril_sep_correct import rstar
from analytic_proofs import syr, v2


def oddcore(x):
    while x % 2 == 0:
        x //= 2
    return x


def a_k(k):
    rs = rstar(k)
    return (3 * rs + 1) // (1 << k)        # in {1,2}


def S_full(k, xi):
    mod = 1 << k
    w = np.exp(-2j * np.pi / mod)
    a = a_k(k)
    return sum(w ** (xi * (oddcore(a + 3 * m) % mod)) for m in range(mod))


def geometric_and_odd_parts(k, eta):
    """Split S_k(eta) into geometric (vanishing) + structural parts. eta is the actual argument."""
    mod = 1 << k
    w = np.exp(-2j * np.pi / mod)
    a = a_k(k)
    geo = 0j
    nongeo = 0j
    half = 1 << (k - 1)
    for mp in range(half):
        # even m=2m'
        x_even = a + 3 * (2 * mp)
        Oe = oddcore(x_even) % mod
        # odd m=2m'+1
        x_odd = a + 3 * (2 * mp + 1)
        Oo = oddcore(x_odd) % mod
        # which is geometric? the one whose x is ODD (v2=0): O=x itself, linear in m'
        if x_even % 2 == 1:   # k even: even-m is geometric
            geo += w ** (eta * Oe); nongeo += w ** (eta * Oo)
        else:                 # k odd: odd-m is geometric
            geo += w ** (eta * Oo); nongeo += w ** (eta * Oe)
    return geo, nongeo


if __name__ == "__main__":
    print("Check parity split: for eta=2 xi, geometric part = 0 and nongeo = S_{k-1}(xi):")
    for k in [8, 9, 10]:
        modk1 = 1 << (k - 1)
        bad_geo = []
        bad_eq = []
        for xi in range(1, modk1):
            eta = 2 * xi
            geo, nongeo = geometric_and_odd_parts(k, eta)
            if abs(geo) > 1e-7:
                bad_geo.append(xi)
            Sk1 = S_full(k - 1, xi)
            if abs(nongeo - Sk1) > 1e-6:
                bad_eq.append(xi)
        print(f"  k={k}: xi in [1,2^(k-1)) with geometric!=0: {bad_geo}  "
              f"(expect only xi=2^(k-2)={1<<(k-2)} where 2xi=Nyquist)")
        print(f"         xi where nongeo != S_(k-1)(xi): {bad_eq}  (expect [] except the Nyquist xi)")
    # full identity confirmation, complex, big k via FFT
    print("\nFFT confirmation S_k(2xi)=S_{k-1}(xi) exact, k up to 14:")
    from probe_selfsimilar import fold
    for k in [12, 14]:
        modk = 1 << k
        rs = rstar(k); cnt = np.zeros(modk)
        for m in range(modk):
            cnt[syr(rs + m * modk) % modk] += 1
        Sk = np.fft.fft(cnt)
        modk1 = 1 << (k - 1)
        rs1 = rstar(k - 1); cnt1 = np.zeros(modk1)
        for m in range(modk1):
            cnt1[syr(rs1 + m * modk1) % modk1] += 1
        Sk1 = np.fft.fft(cnt1)
        err = max(abs(Sk[(2 * xi) % modk] - Sk1[xi]) for xi in range(1, modk1) if xi != (1 << (k - 2)))
        print(f"  k={k}: max|S_k(2xi)-S_(k-1)(xi)| over xi in [1,2^(k-1)), xi!=2^(k-2):  {err:.2e}")
