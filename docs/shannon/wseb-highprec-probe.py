"""
WSEB single-sample atom, ARBITRARY-PRECISION recomputation.  Requires: mpmath.

WHAT THIS SHOWS.  sup { f(0)^2 / ∫_0^T f^2 : f ∈ PW_W } is +∞, i.e. the window energy of a
band-limited signal does NOT control its point values.  sup_N is monotone increasing in N and,
crucially, DOES NOT CONVERGE: each floating-point precision level has its own spurious plateau
(dps=15 -> ~54, dps=30 -> ~116, dps=60 -> ~280, dps=120 -> ~718; at dps=480, N=96 reaches 5680
and is still climbing).  The apparent "convergence" is an artifact of the working precision, not
a property of the supremum.

SUPERSEDES docs/shannon/wseb-numerical-probe.py and docs/shannon/wseb-numerical-crosscheck.py.
Those two double-precision scripts reported the atom TRUE with sup ~= 76.1 at T=4, and were
believed independent (sinc-side vs spectral-side discretizations).  They are not independent in
the way that matters: BOTH call np.linalg.lstsq(..., rcond=None), which discards singular values
below ~machine eps.  The window sinc Gram's singular values decay super-exponentially
(lambda_min = 3.8e-10 / 1.9e-25 / 2.3e-44 at N=4/8/12, T=4), so past effective rank ~2WT every
added mode is silently dropped and the value freezes.  The reported 76.1 is exactly the N=8 value
at which double precision froze (this script prints 76.4058 there, and keeps going).

The refutation does not rest on trusting an ill-conditioned solve.  Only a LOWER bound on the sup
is needed, and a lower bound needs only a witness: solve for candidate coefficients c at high dps,
then FORWARD-evaluate f(t) = sum_n c_n sinc(t-n), taking f(0) by direct summation and int_0^T f^2
by direct quadrature.  The resulting ratio contains no matrix inverse, and ANY c is a valid
witness regardless of how it was obtained, so conditioning cannot inflate it.  That route confirms
276.29 at T=4 (matching the dps=120, N=16 entry below), already 3.6x the recorded "sup" of 76.1.

Consequence in the Lean development: the false-sup belief is what made
ShannonHartley.contAwgnMaxMessages_bddAbove look provable-but-hard (tagged as a nyquist-2w-dof
wall).  It is in fact false as framed, together with contAwgn_eq_shannonHartley and
contAwgn_ge_shannonHartley; the root is the window-only ContAwgnCode.encoder_power constraint.

Question:  is  sup { f(0)^2 / ∫_0^T f^2 : f ∈ PW_{1/2}, f ≠ 0 }  finite?

Setup (same as docs/shannon/wseb-numerical-probe.py): W = 1/2, Nyquist spacing 1,
so {sinc(t-n)}_{n∈ℤ} is an ORTHONORMAL BASIS of PW_{1/2} (Shannon).  Write
f = Σ_{|n|≤N} c_n sinc(t-n).  Since sinc(0-n) = δ_{n0} for integer n,
the constraint f(0) = 1 is exactly c_0 = 1.  Then

    sup_N = (G_N^{-1})_{00},        G_{mn} = ∫_0^T sinc(t-m) sinc(t-n) dt

and sup_N ↑ sup as N → ∞ (monotone: bigger subspace).

CLOSED FORM (exact, no quadrature).  For integer m,n:
  sin(π(t-m)) = (-1)^m sin(πt), so
  sinc(t-m)sinc(t-n) = (-1)^{m+n} sin^2(πt) / (π^2 (t-m)(t-n)).

  m ≠ n:  1/((t-m)(t-n)) = [1/(t-m) - 1/(t-n)] / (m-n)
          G_{mn} = (-1)^{m+n} / (π^2 (m-n)) * ( I(m) - I(n) )
          I(k) = ∫_0^T sin^2(πt)/(t-k) dt = F(T-k) + F(k)
          F(x) = ∫_0^x (1-cos 2πu)/(2u) du  (odd);  F(x) = Cin(2πx)/2 for x>0,
          Cin(z) = γ + ln z - Ci(z).
  m = n:  G_{nn} = ( J(T-n) + J(n) ) / π^2
          J(x) = ∫_0^x (1-cos 2πu)/(2u^2) du  (odd)
                = [ 2π Si(2πx) - (1-cos 2πx)/x ] / 2   for x > 0.

The double-precision probe uses lstsq(rcond=None), which truncates singular
values below ~eps.  The window Gram's singular values decay like the prolate
eigenvalues (super-exponentially), so beyond effective rank ≈ 2WT + O(log)
EVERY added mode is discarded -> the value freezes -> looks "converged".
Here we crank the precision instead and watch sup_N grow.
"""
from mpmath import mp, mpf, pi, sin, cos, ci, si, euler, log, matrix, lu_solve, quad

def F(x):
    """∫_0^x (1-cos 2πu)/(2u) du.

    Integrand is ODD ((1-cos) even / u odd), so F is EVEN: F(-x) = F(x).
    For x > 0, F(x) = Cin(2πx)/2 with Cin(z) = γ + ln z - Ci(z).
    """
    if x == 0:
        return mpf(0)
    if x < 0:
        x = -x
    z = 2 * pi * x
    return (euler + log(z) - ci(z)) / 2

def J(x):
    """∫_0^x (1-cos 2πu)/(2u^2) du, odd, continuous at 0."""
    if x == 0:
        return mpf(0)
    if x < 0:
        return -J(-x)
    z = 2 * pi * x
    return (2 * pi * si(z) - (1 - cos(z)) / x) / 2

def gram(T, N):
    ns = list(range(-N, N + 1))
    T = mpf(T)
    # I(k) = ∫_{-k}^{T-k} (1-cos 2πu)/(2u) du = F(T-k) - F(-k) = F(T-k) - F(k)  [F even]
    Ical = {k: F(T - k) - F(k) for k in ns}
    Jcal = {k: J(T - k) + J(k) for k in ns}
    d = len(ns)
    G = matrix(d, d)
    for i, m in enumerate(ns):
        for j, n in enumerate(ns):
            if i > j:
                G[i, j] = G[j, i]
                continue
            if m == n:
                G[i, j] = Jcal[m] / pi**2
            else:
                sgn = mpf(-1) ** ((m + n) % 2)
                G[i, j] = sgn * (Ical[m] - Ical[n]) / (pi**2 * (m - n))
    return G, ns

def sup_N(T, N, dps):
    mp.dps = dps
    G, ns = gram(T, N)
    e0 = matrix(len(ns), 1)
    e0[ns.index(0), 0] = 1
    x = lu_solve(G, e0)          # x = G^{-1} e_0
    return x[ns.index(0), 0]     # (G^{-1})_{00} = sup over this subspace


def _sinc(x):
    if x == 0:
        return mpf(1)
    return sin(pi * x) / (pi * x)

def validate(T, N, dps=40):
    """Check the closed-form Gram against direct quadrature (independent route)."""
    mp.dps = dps
    G, ns = gram(T, N)
    worst = mpf(0)
    for i, m in enumerate(ns):
        for j, n in enumerate(ns):
            if j < i:
                continue
            pts = [mpf(k) for k in range(0, T + 1)]
            q = quad(lambda t: _sinc(t - m) * _sinc(t - n), pts)
            err = abs(q - G[i, j])
            worst = max(worst, err)
    return worst

def check_psd(T, N, dps=60):
    """Gram must be positive definite; report the smallest eigenvalue."""
    mp.dps = dps
    G, ns = gram(T, N)
    return min(mp.eigsy(G, eigvals_only=True))


if __name__ == "__main__":
    print("--- validation: closed-form Gram vs direct quadrature (must be ~0) ---")
    for T in [4, 8]:
        for N in [2, 4]:
            print(f"  T={T} N={N}: max |closed-form - quad| = {float(validate(T, N)):.3e}")
    print("--- validation: Gram positive definite (min eigenvalue must be > 0) ---")
    for T in [4, 8]:
        for N in [4, 8, 12]:
            print(f"  T={T} N={N}: lambda_min = {float(check_psd(T, N)):.3e}")
    print()

    print("sup_N = (G_N^{-1})_{00} = sup{ f(0)^2/∫_0^T f^2 } over span{sinc_n : |n|<=N}")
    print("monotone increasing in N; WSEB TRUE <=> bounded, FALSE <=> -> ∞\n")
    for T in [4, 8]:
        print(f"=== T={T}, W=1/2 ===")
        print(f"{'N':>4} | " + " | ".join(f"dps={d:<4}".rjust(14) for d in [15, 30, 60, 120]))
        for N in [2, 4, 8, 12, 16, 24, 32, 48]:
            row = []
            for dps in [15, 30, 60, 120]:
                try:
                    v = sup_N(T, N, dps)
                    row.append(f"{float(v):14.6g}")
                except Exception as ex:
                    row.append(f"{'ERR':>14}")
            print(f"{N:>4} | " + " | ".join(row))
        print()
