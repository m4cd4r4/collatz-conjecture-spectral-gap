"""
T6.3 verification script - fresh rebuild of T_k from the THEOREM.md Setup definition.

Gate first (reproduce known quantities), then the new constants.
Every constant is computed TWICE: once in float from the rebuilt operator / plain
arithmetic, once in exact symbolic form (sympy, powers of 2 and surds) evaluated to
30 digits. Disagreements are reported.

Run: python extremal_values_check.py
"""
import numpy as np
import sympy as sp
from math import sqrt, log10

np.set_printoptions(precision=6, suppress=True)

# ----------------------------------------------------------------- operators


def oddpart_vec(x):
    x = x.copy()
    while True:
        ev = (x % 2 == 0)
        if not ev.any():
            break
        x[ev] //= 2
    return x


def build_T(k, sign=+1):
    """Column-stochastic T_k on the N = 2^(k-1) odd residues mod 2^k.

    T[s',s] = P[ Syr(s + m 2^k) = s' mod 2^k ], m uniform on [0,2^k).
    Syr(n) = oddpart(3n + sign).
    """
    K = 1 << k
    N = K >> 1
    odds = np.arange(1, K, 2, dtype=np.int64)
    m = np.arange(K, dtype=np.int64)
    T = np.zeros((N, N))
    for i, r in enumerate(odds):
        n = int(r) + m * K
        t = oddpart_vec(3 * n + sign) % K
        j = (t - 1) // 2
        T[:, i] = np.bincount(j, minlength=N) / K
    return T, odds


def char_matrix(k, odds):
    K = 1 << k
    N = K >> 1
    xis = np.arange(N, dtype=np.int64)
    ph = (np.outer(odds, xis) % K).astype(np.float64)
    C = np.exp(2j * np.pi * ph / K) / sqrt(N)
    return C, xis


def v2(n):
    c = 0
    while n % 2 == 0:
        n //= 2
        c += 1
    return c


def analyse(k, sign=+1):
    K = 1 << k
    N = K >> 1
    T, odds = build_T(k, sign)
    # column-stochastic sanity
    colsum_err = float(np.max(np.abs(T.sum(axis=0) - 1.0)))

    C, xis = char_matrix(k, odds)
    U = T.T                                   # Koopman
    M = C.conj().T @ U @ C                    # U in the character basis

    levels = [[] for _ in range(k - 1)]       # b = 0..k-2
    for idx, xi in enumerate(xis):
        if xi == 0:
            continue
        levels[v2(int(xi))].append(idx)
    levels = [np.array(L, dtype=int) for L in levels]

    nb = k - 1
    Q = np.zeros((nb, nb))
    for a in range(nb):
        Ra = levels[a]
        for b in range(nb):
            Cb = levels[b]
            blk = M[np.ix_(Ra, Cb)]
            Q[a, b] = np.linalg.norm(blk, 2)

    wt = np.array([[2.0 ** (a - b) for b in range(nb)] for a in range(nb)])
    rowsums = (Q * wt).sum(axis=1)
    cert = float(rowsums.max())
    a_star = int(rowsums.argmax())
    e_star = k - a_star

    rhoQ = float(max(abs(np.linalg.eigvals(Q))))
    ev = np.sort(np.abs(np.linalg.eigvals(T)))[::-1]
    lam2 = float(ev[1])

    # defect covector c = fiber distribution of r* = -sign * 3^{-1} mod 2^k
    rstar = (-sign * pow(3, -1, K)) % K
    i_star = (rstar - 1) // 2
    c = T[:, i_star].copy()
    chat = C.conj().T @ c
    vb = np.array([float(np.linalg.norm(chat[levels[b]])) for b in range(nb)])
    gb = vb * (2.0 ** np.arange(nb)) * 2.0 ** (k / 2)
    cnorm = float(np.linalg.norm(c))

    ua = 2.0 ** (-(np.arange(nb) + 1) / 2.0)
    ua_meas = np.array([float(np.linalg.norm((C.conj().T @ np.eye(N)[:, i_star])[levels[b]]))
                        for b in range(nb)])

    return dict(k=k, sign=sign, cert=cert, rhoQ=rhoQ, lam2=lam2, a_star=a_star,
                e_star=e_star, Q=Q, rowsums=rowsums, vb=vb, gb=gb, cnorm=cnorm,
                ua=ua, ua_meas=ua_meas, colsum_err=colsum_err, rstar=rstar)


# ----------------------------------------------------------------- envelopes

def f_AB(e):                      # Lemmas A+B (Cauchy-Schwarz defect)
    return sum(2.0 ** (-1.5 * d) for d in range(1, e - 1)) + 2.0 ** (-(e - 1) / 2.0)


def f_C_proven(e):                # Lemma C at the PROVEN constant sqrt(3/4)
    return sum(2.0 ** (-1.5 * d) for d in range(1, e - 1)) + (2 / sqrt(3)) * 2.0 ** (-(e + 1) / 2.0)


def f_C_data(e):                  # Lemma C at the DATA sharp constant 3/4
    return sum(2.0 ** (-1.5 * d) for d in range(1, e - 1)) + 2.0 ** (-(e + 1) / 2.0)


def f_profile(e, S):              # measured profile: S = 2^{k/2} sum_b v_b 2^-b
    # defect term = u_a 2^a * sum_b v_b 2^-b = 2^{(a-1)/2} * S * 2^{-k/2} = S * 2^{-(e+1)/2}
    return sum(2.0 ** (-1.5 * d) for d in range(1, e - 1)) + S * 2.0 ** (-(e + 1) / 2.0)


# exact (sympy) counterparts
def F_AB(e):
    return sum(sp.Integer(2) ** sp.Rational(-3 * d, 2) for d in range(1, e - 1)) \
        + sp.Integer(2) ** sp.Rational(-(e - 1), 2)


def F_C_proven(e):
    return sum(sp.Integer(2) ** sp.Rational(-3 * d, 2) for d in range(1, e - 1)) \
        + (2 / sp.sqrt(3)) * sp.Integer(2) ** sp.Rational(-(e + 1), 2)


def F_C_data(e):
    return sum(sp.Integer(2) ** sp.Rational(-3 * d, 2) for d in range(1, e - 1)) \
        + sp.Integer(2) ** sp.Rational(-(e + 1), 2)


def show(label, flt, exact):
    ev = sp.N(exact, 30)
    d = abs(sp.N(exact, 30) - sp.Float(flt, 30))
    print(f"  {label:<52} float={flt:.10f}  exact={sp.nsimplify(exact)} = {str(ev)[:18]}  |diff|={float(d):.3e}")
    return float(d)


# ================================================================== MAIN
print("=" * 78)
print("PART 0 - REPRODUCTION GATE (must pass before any new number)")
print("=" * 78)

g8 = analyse(8, +1)
print(f"  T_8 column-stochastic max err        : {g8['colsum_err']:.2e}")
print(f"  cert(8)   rebuilt = {g8['cert']:.6f}   published 0.634659 (UFULL table) / 0.6347 (CCR)")
print(f"  rho(Q,8)  rebuilt = {g8['rhoQ']:.6f}   published 0.566061 / 0.5661")
print(f"  |lambda2| rebuilt = {g8['lam2']:.6f}   published 0.255")
fAB3 = f_AB(3)
print(f"  f(3) A+B envelope = {fAB3:.10f}  published 0.8535533906  (2^-3/2 + 2^-1)")

gate_ok = (abs(g8['cert'] - 0.634659) < 5e-5
           and abs(g8['rhoQ'] - 0.566061) < 5e-5
           and abs(fAB3 - 0.8535533906) < 1e-9)
print(f"\n  GATE: {'PASS' if gate_ok else 'FAIL'}")
if not gate_ok:
    raise SystemExit("gate failed - STOP")

print("\n" + "=" * 78)
print("PART 1 - measured table, 3x+1 and 3x-1")
print("=" * 78)
res_p, res_m = {}, {}
KS = list(range(3, 14))
for k in KS:
    res_p[k] = analyse(k, +1)
print("  3x+1:  k   cert       rho(Q)     |lam2|   a*  e*   max g_b^2   ||c||2^(k/2)")
for k in KS:
    r = res_p[k]
    print(f"        {k:2d}  {r['cert']:.6f}  {r['rhoQ']:.6f}  {r['lam2']:.4f}  {r['a_star']:2d}  {r['e_star']:2d}"
          f"   {max(r['gb'])**2:.6f}    {r['cnorm']*2**(k/2):.4f}")
for k in [6, 8, 10, 11]:
    res_m[k] = analyse(k, -1)
print("  3x-1:  k   cert       rho(Q)     |lam2|   a*  e*")
for k in [6, 8, 10, 11]:
    r = res_m[k]
    print(f"        {k:2d}  {r['cert']:.6f}  {r['rhoQ']:.6f}  {r['lam2']:.4f}  {r['a_star']:2d}  {r['e_star']:2d}")

print("\n  u_a exactness (max |measured - 2^-(a+1)/2|) over k=3..12:",
      f"{max(float(np.max(np.abs(res_p[k]['ua_meas'] - res_p[k]['ua']))) for k in KS):.2e}")

print("\n" + "=" * 78)
print("PART 2 - the three envelopes, argmax and value (float vs exact)")
print("=" * 78)
diffs = []
for name, ff, FF in [("A+B  (PROVEN, Cauchy-Schwarz)", f_AB, F_AB),
                     ("Lemma C at sqrt(3/4) (PROVEN)", f_C_proven, F_C_proven),
                     ("Lemma C at 3/4       (DATA)  ", f_C_data, F_C_data)]:
    vals = [(e, ff(e)) for e in range(2, 61)]
    e_max, v_max = max(vals, key=lambda t: t[1])
    print(f"\n  {name}:  argmax e = {e_max}")
    for e in range(2, 8):
        print(f"      e={e}: {ff(e):.10f}")
    diffs.append(show("    max value", v_max, sp.radsimp(sp.simplify(FF(e_max)))))
    # monotone decrease check after argmax
    mono = all(ff(e) > ff(e + 1) for e in range(e_max, 60))
    print(f"      monotone decreasing after e={e_max}: {mono}")

print("\n" + "=" * 78)
print("PART 3 - UFULL assembly constants")
print("=" * 78)
G_up_f = 1.0 / (2 ** 1.5 - 1)
G_up_e = 1 / (2 * sp.sqrt(2) - 1)
diffs.append(show("G_up = sum_{d>=1} 2^-3d/2", G_up_f, G_up_e))
diffs.append(show("UFULL PROVEN  G_up + (2/sqrt3) 2^-3/2", G_up_f + (2 / sqrt(3)) * 2 ** -1.5,
                  sp.radsimp(G_up_e + 2 / sp.sqrt(3) * sp.Integer(2) ** sp.Rational(-3, 2))))
diffs.append(show("UFULL DATA    G_up + 2^-3/2", G_up_f + 2 ** -1.5,
                  sp.radsimp(G_up_e + sp.Integer(2) ** sp.Rational(-3, 2))))

print("\n" + "=" * 78)
print("PART 4 - measured v_b profile pushed through the Part III row assembly")
print("=" * 78)
print("   k    S_k=2^(k/2) sum_b v_b 2^-b    cert_profile   argmax e   cert_measured")
for k in KS:
    r = res_p[k]
    S = float(np.sum(r['vb'] * 2.0 ** (-np.arange(k - 1))) * 2 ** (k / 2))
    vals = [(e, f_profile(e, S)) for e in range(2, k + 1)]
    e_max, v_max = max(vals, key=lambda t: t[1])
    print(f"  {k:2d}    {S:.8f}                  {v_max:.6f}      {e_max}          {r['cert']:.6f}")

print("\n  binding-row split at the measured binding row (clean analytic + defect):")
for k in [8, 10, 12]:
    r = res_p[k]
    e = r['e_star']
    clean = sum(2.0 ** (-1.5 * d) for d in range(1, e - 1))
    S = float(np.sum(r['vb'] * 2.0 ** (-np.arange(k - 1))) * 2 ** (k / 2))
    defect = S * 2.0 ** (-(e + 1) / 2.0)
    print(f"   k={k:2d}  e*={e}  clean={clean:.4f} + defect={defect:.4f} = {clean+defect:.6f}"
          f"   (cert measured {r['cert']:.6f})")

print("\n" + "=" * 78)
print("PART 5 - absurd-height instantiation at s = 6,586,818,670")
print("=" * 78)
s = 6586818670
for label, g in [("PROVEN 0.8535533906", 2 ** -1.5 + 0.5),
                 ("PROVEN-LemmaC 0.6826775", f_C_proven(4)),
                 ("DATA-LemmaC   0.6553301", f_C_data(4)),
                 ("STATUS.md's 0.29", 0.29),
                 ("measured |lam2| 0.27", 0.27)]:
    print(f"   4 * ({g:.7f})^(s/2)  ~  10^({log10(4) + (s/2)*log10(g):.4e})   [{label}]")

print("\n" + "=" * 78)
print("PART 6 - SECOND, INDEPENDENT METHOD for the measured constants")
print("  Method A: enumerate all 2^k lifts, build T, transform to characters.")
print("  Method B: build the character-basis operator from the CU masked-phase")
print("            formula (THEOREM.md Part II) + the single defect row - no lift")
print("            enumeration except for the r* fiber. Completely different code path.")
print("=" * 78)


def analyse_CU(k, sign=+1):
    K = 1 << k
    N = K >> 1
    odds = np.arange(1, K, 2, dtype=np.int64)
    etas = np.arange(N, dtype=np.int64)
    w = np.exp(2j * np.pi / K)
    rstar = (-sign * pow(3, -1, K)) % K

    v_eta = np.array([k if e == 0 else v2(int(e)) for e in etas])
    E = np.zeros((N, N), dtype=complex)
    for i, r in enumerate(odds):
        r = int(r)
        if r == rstar:
            continue
        x = 3 * r + sign
        vr = v2(x)
        assert vr < k, (r, vr)
        tgt = (x >> vr) % K
        mask = (vr <= v_eta)
        E[i, :] = mask * np.exp(2j * np.pi * ((etas * tgt) % K) / K)
    # the one exceptional row: its fiber distribution, computed directly
    m = np.arange(K, dtype=np.int64)
    n = rstar + m * K
    t = oddpart_vec(3 * n + sign) % K
    cf = np.bincount((t - 1) // 2, minlength=N) / K
    i_star = (rstar - 1) // 2
    E[i_star, :] = (cf[:, None] * np.exp(2j * np.pi * ((etas[None, :] * odds[:, None]) % K) / K)).sum(axis=0)

    W = np.exp(2j * np.pi * ((np.outer(odds, etas)) % K) / K)
    M = (W.conj().T @ E) / N          # = C^H U C

    levels = [[] for _ in range(k - 1)]
    for idx, xi in enumerate(etas):
        if xi == 0:
            continue
        levels[v2(int(xi))].append(idx)
    levels = [np.array(L, dtype=int) for L in levels]
    nb = k - 1
    Q = np.zeros((nb, nb))
    for a in range(nb):
        for b in range(nb):
            Q[a, b] = np.linalg.norm(M[np.ix_(levels[a], levels[b])], 2)
    wt = np.array([[2.0 ** (a - b) for b in range(nb)] for a in range(nb)])
    rs = (Q * wt).sum(axis=1)
    ev = np.sort(np.abs(np.linalg.eigvals(M)))[::-1]
    chat = (W.conj().T @ cf) / sqrt(N)
    vb = np.array([float(np.linalg.norm(chat[levels[b]])) for b in range(nb)])
    return dict(cert=float(rs.max()), rhoQ=float(max(abs(np.linalg.eigvals(Q)))),
                lam2=float(ev[1]), e_star=k - int(rs.argmax()), vb=vb)


print("        sign  k   cert(A)    cert(B)     |dA-B|     rho(A)     rho(B)"
      "     |l2|(A)   |l2|(B)   max|vb A-B|")
worst = 0.0
for sign, ks in [(+1, [6, 8, 10, 12]), (-1, [6, 8, 10, 11])]:
    for k in ks:
        A = res_p[k] if sign == +1 else (res_m[k] if k in res_m else analyse(k, sign))
        B = analyse_CU(k, sign)
        dv = float(np.max(np.abs(A['vb'] - B['vb'])))
        d = max(abs(A['cert'] - B['cert']), abs(A['rhoQ'] - B['rhoQ']),
                abs(A['lam2'] - B['lam2']), dv)
        worst = max(worst, d)
        print(f"        {sign:+d}   {k:2d}  {A['cert']:.7f}  {B['cert']:.7f}  {abs(A['cert']-B['cert']):.2e}"
              f"   {A['rhoQ']:.6f}   {B['rhoQ']:.6f}   {A['lam2']:.6f}  {B['lam2']:.6f}   {dv:.2e}")
print(f"\n  worst A-vs-B disagreement over all measured quantities: {worst:.3e}")

print("\n" + "=" * 78)
print(f"MAX float-vs-exact disagreement across all closed-form constants: {max(diffs):.3e}")
print("=" * 78)
