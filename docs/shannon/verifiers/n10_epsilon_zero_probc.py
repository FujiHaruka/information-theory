#!/usr/bin/env python3
"""Leg N10: is the N7 tolerance `eps = 2.0786e-07` removable, i.e. is `Omega(t) = d*_t` exact?

Self-contained: this file NEVER imports or executes any other verifier under
`docs/shannon/verifiers/` (in particular not `shoulder_certificate_probc.py`,
`n7_audit_probc.py`, `n9_cone_probc.py`, `n9_audit_probc.py`).  Every constant,
channel matrix and identity below is rebuilt from the instance definition.

Instance [probc] (independently rebuilt):
    X = (X1,X2) in {0,1}^2,  p = 0.1,  e = h(p),  C = 1 - e = 1 - h(p),
    X1 -> Y1 = BEC(e),  X1 -> Z1 = BSC(p),
    X2 -> Y2 = BSC(p),  X2 -> Z2 = BEC(e).

Notation:
    f_t(s)   = H(Y)_s - t H(Z)_s
    psi_t(x) = t C h(x) - J(x),     J(x) = h(x*p) - h(p)
    d*_t     = max_x psi_t(x)
    delta(x) = psi_1(x) = C h(x) - J(x)          (>= 0: Mrs. Gerber / more capable)
    Omega(t) = max_s [ t I(X;Z)_s - I(X;Y)_s ]
    G_t(s)   = I(X1;Y1|Y2) - t I(X1;Z1|Z2)
    b = P(X2=1), a = P(X1=1), A_j = P(X1=1|X2=j), B_i = P(X2=1|X1=i),
    I2 = I(X1;X2),  S_A = e delta(a) + C E_{X2}[delta(A_X2)],
                    S_B = e delta(b) + C E_{X1}[delta(B_X1)].

Main chain proved here (tests D1-D6, E1-E4):
    T_t := G_t + d*_t - psi_t(b) = C(1-t)[h(a)+h(b)-C I2] + t S_A + d*_t - S_B  (identity)
    S_B <= d*_t + C(1-t)[h(b) - C I2]                                          (psi_t <= d*_t)
    ==> T_t >= C(1-t) h(a) + t S_A >= 0                                        (delta >= 0)
    ==> Omega(t) <= d*_t, and Omega(t) >= d*_t is achieved ==> Omega(t) = d*_t.

Run:  python3 docs/shannon/verifiers/n10_epsilon_zero_probc.py [--quick]
Exit code 0 iff every test passes.  Tests whose name contains `screen` are
searches: a non-violation there is not evidence (parent plan section 4.5).
"""
import argparse
import sys
import time

import numpy as np

LN2 = np.log(2.0)
RESULTS = []


def record(name, ok, detail):
    RESULTS.append((name, ok, detail))
    print(f"[{'PASS' if ok else 'FAIL'}] {name}: {detail}")
    sys.stdout.flush()


# ----------------------------------------------------------------- primitives


def ent(P):
    P = np.asarray(P, dtype=float).ravel()
    Q = P[P > 1e-300]
    return float(-(Q * np.log(Q)).sum() / LN2)


def h2(a):
    a = float(a)
    if a <= 0.0 or a >= 1.0:
        return 0.0
    return float(-a * np.log2(a) - (1 - a) * np.log2(1 - a))


def h2v(a):
    a = np.clip(np.asarray(a, dtype=float), 0.0, 1.0)
    with np.errstate(divide="ignore", invalid="ignore"):
        r = -a * np.log2(a) - (1 - a) * np.log2(1 - a)
    return np.where((a <= 0) | (a >= 1), 0.0, r)


def star(a, b):
    return a * (1 - b) + (1 - a) * b


P_CROSS = 0.1
E_ERAS = h2(P_CROSS)
CAP = 1.0 - E_ERAS
R2 = (1 - 2 * P_CROSS) ** 2

BEC = np.array([[1 - E_ERAS, 0.0, E_ERAS], [0.0, 1 - E_ERAS, E_ERAS]])
BSC = np.array([[1 - P_CROSS, P_CROSS], [P_CROSS, 1 - P_CROSS]])

# X index = 2*x1 + x2;  Y index = 2*y1 + y2 (y1 in {0,1,?});  Z index = 3*z1 + z2
MY = np.zeros((4, 6))
MZ = np.zeros((4, 6))
for _x1 in range(2):
    for _x2 in range(2):
        _x = 2 * _x1 + _x2
        for _y1 in range(3):
            for _y2 in range(2):
                MY[_x, 2 * _y1 + _y2] = BEC[_x1, _y1] * BSC[_x2, _y2]
        for _z1 in range(2):
            for _z2 in range(3):
                MZ[_x, 3 * _z1 + _z2] = BSC[_x1, _z1] * BEC[_x2, _z2]

H_Y_GIVEN_X = h2(E_ERAS) + h2(P_CROSS)
H_Z_GIVEN_X = h2(P_CROSS) + h2(E_ERAS)


def HY(s):
    return ent(np.asarray(s, dtype=float) @ MY)


def HZ(s):
    return ent(np.asarray(s, dtype=float) @ MZ)


def f_t(s, t):
    return HY(s) - t * HZ(s)


def Omega_at(s, t):
    return t * (HZ(s) - H_Z_GIVEN_X) - (HY(s) - H_Y_GIVEN_X)


# ------------------------------------------- psi / d* in a cancellation-free form


def h_small(b):
    b = float(b)
    if b <= 0.0 or b >= 1.0:
        return 0.0
    return -b * np.log2(b) - (1 - b) * np.log1p(-b) / LN2


def Jfun(x):
    """J(x) = h(x*p) - h(p), array-valued."""
    return h2v(star(x, P_CROSS)) - h2(P_CROSS)


def J_stable(b):
    """J(b) without the catastrophic cancellation of the naive form (scalar)."""
    d = float(b) * (1 - 2 * P_CROSS)
    if d == 0.0:
        return 0.0
    return (-P_CROSS * np.log1p(d / P_CROSS) / LN2
            - d * np.log2(P_CROSS + d)
            - (1 - P_CROSS) * np.log1p(-d / (1 - P_CROSS)) / LN2
            + d * np.log2(1 - P_CROSS - d))


def psi(t, b):
    return t * CAP * h_small(b) - J_stable(b)


def dpsi(t, b):
    x = P_CROSS + b * (1 - 2 * P_CROSS)
    return (t * CAP * (np.log2(1 - b) - np.log2(b))
            - (1 - 2 * P_CROSS) * (np.log2(1 - x) - np.log2(x)))


_DSTAR_CACHE = {}


def dstar(t):
    """(d*_t, beta*_t) by bisection on log beta.  psi_t is symmetric about 1/2 and
    has a local minimum at 1/2 (since t C <= C < (1-2p)^2), so the maximiser lies
    in (0, 1/2)."""
    t = float(t)
    hit = _DSTAR_CACHE.get(t)
    if hit is not None:
        return hit
    if t <= 0.0:
        out = (0.0, 0.0)
    elif dpsi(t, 0.5 - 1e-15) > 0:
        out = (psi(t, 0.5), 0.5)
    else:
        lo, hi = -740.0, float(np.log(0.5 - 1e-15))
        for _ in range(200):
            m = 0.5 * (lo + hi)
            if dpsi(t, np.exp(m)) > 0:
                lo = m
            else:
                hi = m
        b = float(np.exp(0.5 * (lo + hi)))
        out = (psi(t, b), b)
    _DSTAR_CACHE[t] = out
    return out


def delta(x):
    """delta = psi_1 = C h - J, array-valued."""
    return CAP * h2v(x) - Jfun(x)


# ------------------------------------------------ the fibre reformulation of Omega


def fibre_parts(b, A0, A1):
    """Return (a, I2, CH, Xi, EdA, EdB) on the fibre, all array-valued.

    A0 = P(X1=1|X2=0), A1 = P(X1=1|X2=1), b = P(X2=1).
    CH  = C H(X1|Y2)   = I(X1;Y1|Y2)      (exact for a BEC(e) side channel)
    Xi  = I(X1;Z1|Z2)  = e J(a) + C E_{X2}[J(A_X2)]
    EdA = E_{X2}[delta(A_X2)],  EdB = E_{X1}[delta(B_X1)]
    """
    b = np.asarray(b, float)
    A0 = np.asarray(A0, float)
    A1 = np.asarray(A1, float)
    a = (1 - b) * A0 + b * A1
    # H(X1|Y2) through Y2 = BSC(p)(X2)
    py1 = star(b, P_CROSS)
    py0 = 1 - py1
    j1 = (1 - b) * A0 * BSC[0, 1] + b * A1 * BSC[1, 1]
    j0 = (1 - b) * A0 * BSC[0, 0] + b * A1 * BSC[1, 0]
    al1 = np.where(py1 > 0, j1 / np.where(py1 > 0, py1, 1.0), 0.0)
    al0 = np.where(py0 > 0, j0 / np.where(py0 > 0, py0, 1.0), 0.0)
    CH = CAP * (py0 * h2v(al0) + py1 * h2v(al1))
    Xi = E_ERAS * Jfun(a) + CAP * ((1 - b) * Jfun(A0) + b * Jfun(A1))
    EdA = (1 - b) * delta(A0) + b * delta(A1)
    # B_i = P(X2=1|X1=i)
    B1 = np.where(a > 0, b * A1 / np.where(a > 0, a, 1.0), 0.0)
    B0 = np.where(a < 1, b * (1 - A1) / np.where(a < 1, 1 - a, 1.0), 0.0)
    EdB = (1 - a) * delta(B0) + a * delta(B1)
    HX2_X1 = (1 - a) * h2v(B0) + a * h2v(B1)
    I2 = h2v(b) - HX2_X1
    return a, I2, CH, Xi, EdA, EdB, B0, B1


def G_of(t, b, A0, A1):
    _, _, CH, Xi, _, _, _, _ = fibre_parts(b, A0, A1)
    return CH - t * Xi


def T_of(t, b, A0, A1):
    """T_t = G_t + d*_t - psi_t(b); >= 0 is the target."""
    g = G_of(t, b, A0, A1)
    bb = np.asarray(b, float)
    pv = np.vectorize(lambda x: psi(float(t), x))(bb)
    return g + dstar(t)[0] - pv


def s_from_fibre(b, A0, A1):
    """law on X = (X1,X2), index 2*x1+x2."""
    return np.array([(1 - b) * (1 - A0), b * (1 - A1), (1 - b) * A0, b * A1])


def fibre_from_s(s):
    s = np.asarray(s, float)
    b = s[1] + s[3]
    A0 = s[2] / (s[0] + s[2]) if s[0] + s[2] > 0 else 0.0
    A1 = s[3] / (s[1] + s[3]) if s[1] + s[3] > 0 else 0.0
    return b, A0, A1


# ------------------------------------------------------------------------ tests


def a1_constants():
    d = [f"p = {P_CROSS}", f"e = h(p) = {E_ERAS:.15f}", f"C = 1-h(p) = {CAP:.15f}"]
    ok = abs(E_ERAS + CAP - 1.0) < 1e-15
    d.append(f"e+C-1 = {abs(E_ERAS + CAP - 1.0):.3e}")
    cap_bec = 1.0 - E_ERAS
    cap_bsc = 1.0 - h2(P_CROSS)
    ok &= abs(cap_bec - cap_bsc) < 1e-15
    d.append(f"cap BEC(e) - cap BSC(p) = {abs(cap_bec - cap_bsc):.3e}")
    ok &= abs(R2 - 0.64) < 1e-15 and R2 > CAP
    d.append(f"(1-2p)^2 = {R2:.15f} > C")
    record("A1 constants (e+C=1, equal capacities)", ok, "; ".join(d))


def a2_channel():
    ok = True
    unif = np.ones(4) / 4
    hy = HY(unif)
    ok &= abs(hy - (CAP + h2(E_ERAS) + 1.0)) < 1e-12
    d = [f"H(Y)_unif = {hy:.15f} = C+h(e)+1 (residual {abs(hy - (CAP + h2(E_ERAS) + 1.0)):.3e})"]
    w = 0.0
    for x in range(4):
        w = max(w, abs(ent(MY[x]) - H_Y_GIVEN_X), abs(ent(MZ[x]) - H_Z_GIVEN_X))
    ok &= w < 1e-15
    d.append(f"H(Y|X=x) = H(Z|X=x) = h(e)+h(p) for all x (residual {w:.3e})")
    ok &= abs(MY.sum(1) - 1).max() < 1e-15 and abs(MZ.sum(1) - 1).max() < 1e-15
    record("A2 channel matrices", ok, "; ".join(d))


def a3_fibre_identity(n):
    """Omega_at(s,t) = psi_t(b) - G_t(s), pointwise, and G_t from the raw joint law."""
    rng = np.random.default_rng(20260808)
    w_fib = 0.0
    w_raw = 0.0
    for _ in range(n):
        s = rng.dirichlet(np.ones(4))
        t = float(rng.random())
        b, A0, A1 = fibre_from_s(s)
        g = float(G_of(t, np.array(b), np.array(A0), np.array(A1)))
        w_fib = max(w_fib, abs(Omega_at(s, t) - (psi(t, b) - g)))
        # brute force I(X1;Y1|Y2) - t I(X1;Z1|Z2) from the joint law
        w_raw = max(w_raw, abs(g - raw_G(s, t)))
    ok = w_fib < 1e-13 and w_raw < 1e-13
    record("A3 fibre identity Omega = psi_t(b) - G_t (+ raw-law cross-check)", ok,
           f"{n} random (s,t): identity residual {w_fib:.3e}, "
           f"closed-form vs raw-law G_t residual {w_raw:.3e}")


def raw_G(s, t):
    """I(X1;Y1|Y2) - t I(X1;Z1|Z2) computed from the joint law of (X1,X2) only."""
    s = np.asarray(s, float)
    # joint of (X1, Y1, Y2): Y1 from X1 via BEC, Y2 from X2 via BSC
    pj = np.zeros((2, 3, 2))
    for x1 in range(2):
        for x2 in range(2):
            for y1 in range(3):
                for y2 in range(2):
                    pj[x1, y1, y2] += s[2 * x1 + x2] * BEC[x1, y1] * BSC[x2, y2]
    # I(X1;Y1|Y2) = H(X1|Y2) - H(X1|Y1,Y2)
    p_x1y2 = pj.sum(1)
    p_y2 = p_x1y2.sum(0)
    HX1_Y2 = ent(p_x1y2) - ent(p_y2)
    HX1_Y1Y2 = ent(pj) - ent(pj.sum(0))
    IY = HX1_Y2 - HX1_Y1Y2
    pk = np.zeros((2, 2, 3))
    for x1 in range(2):
        for x2 in range(2):
            for z1 in range(2):
                for z2 in range(3):
                    pk[x1, z1, z2] += s[2 * x1 + x2] * BSC[x1, z1] * BEC[x2, z2]
    p_x1z2 = pk.sum(1)
    HX1_Z2 = ent(p_x1z2) - ent(p_x1z2.sum(0))
    HX1_Z1Z2 = ent(pk) - ent(pk.sum(0))
    IZ = HX1_Z2 - HX1_Z1Z2
    return IY - t * IZ


# ------------------------------------------------------ step 0 reproductions (H1-H3)


def c1_h1(n):
    """(H1): the t-elimination of facts N7-p is not an equivalence."""
    ts = np.linspace(0, 1, n)
    ds = np.array([dstar(float(t))[0] for t in ts])
    best, arg = -1.0, None
    for b in np.linspace(0, 1, n):
        phi = CAP * h_small(b) * ts - J_stable(b) - ds
        v = float(phi.max() - phi[-1])
        if v > best:
            best, arg = v, (b, float(ts[int(phi.argmax())]))
    d1, b1 = dstar(1.0)
    ok = best > 1e-3 and abs(best - d1) < 1e-9
    record("C1 (H1) t-elimination fails: max_b [max_t phi_b - phi_b(1)] > 0", ok,
           f"= {best:.10f} at (b,t) = ({arg[0]:.4f}, {arg[1]:.5f}); equals d*_1 = {d1:.10f} "
           f"(residual {abs(best - d1):.3e}) ==> N7-p's 3-variable form is necessary only")


def c1b_beta_star():
    d1, b1 = dstar(1.0)
    hb = h2(b1)
    ok = abs(d1 - 0.0387713704696416) < 1e-12
    record("C1b beta*_1 / d*_1 / h(beta*_1) re-derived", ok,
           f"beta*_1 = {b1:.14f}, d*_1 = {d1:.16f}, h(beta*_1) = {hb:.14f} "
           f"(the N10 brief quotes h(beta*_1) = 0.39331; own value differs by "
           f"{abs(hb - 0.39331):.2e} -- does not affect (H1))")


def c2_h2():
    """(H2): the extra equality point at t=1, A0=A1=1/2, b=beta*_1."""
    d1, b1 = dstar(1.0)
    v = float(T_of(1.0, np.array(b1), np.array(0.5), np.array(0.5)))
    g = float(G_of(1.0, np.array(b1), np.array(0.5), np.array(0.5)))
    # the N7-p family {X2 uniform, X1 = X2 xor Bern(q)} is NOT an equality family here
    qs = np.linspace(0.0, 1.0, 101)
    fam = np.array([float(T_of(1.0, np.array(0.5), np.array(q), np.array(1 - q))) for q in qs])
    ok = abs(v) < 1e-14 and abs(g) < 1e-14 and fam.min() > 1e-3
    record("C2 (H2) equality point at t=1, A0=A1=1/2, b=beta*_1", ok,
           f"T = {v:.3e}, G_1 = {g:.3e}; on the N7-p family G_1 == 0 the target keeps "
           f"margin >= {fam.min():.6f} ==> the two equality families are distinct")


def c2b_hessian():
    """(H2) second order: the Hessian decomposition (x+y)^2[(1-2p)^2 - C] + C[(1-2p)^2 S_in - S_out]."""
    d1, b1 = dstar(1.0)
    b = b1
    q1 = star(b, P_CROSS)
    q0 = 1 - q1

    def quad(u0, u1):
        x, y = (1 - b) * u0, b * u1
        c0 = (1 - P_CROSS) * x + P_CROSS * y
        c1 = P_CROSS * x + (1 - P_CROSS) * y
        S_in = x * x / (1 - b) + y * y / b - (x + y) ** 2
        S_out = c0 * c0 / q0 + c1 * c1 / q1 - (x + y) ** 2
        return (2 / LN2) * ((x + y) ** 2 * (R2 - CAP) + CAP * (R2 * S_in - S_out))

    worst_rel = 0.0
    for u0, u1 in [(1, 0), (0, 1), (1, 1), (1, -1), (2, -3), (-1, 4), (3, 1)]:
        for h in (1e-4, 1e-5):
            g = float(G_of(1.0, np.array(b), np.array(0.5 + h * u0), np.array(0.5 + h * u1)))
            pred = quad(h * u0, h * u1)
            worst_rel = max(worst_rel, abs(g - pred) / max(abs(pred), 1e-300))
    # positive definiteness of the quadratic form + the two structural facts
    eig_min = min(np.linalg.eigvalsh(np.array(
        [[quad(1, 0) * 2, quad(1, 1) - quad(1, 0) - quad(0, 1)],
         [quad(1, 1) - quad(1, 0) - quad(0, 1), quad(0, 1) * 2]])))
    sdpi = q0 * q1 - b * (1 - b)
    ok = worst_rel < 5e-3 and eig_min > 0 and R2 > CAP and sdpi > 0
    record("C2b (H2) Hessian = (x+y)^2[(1-2p)^2-C] + C[(1-2p)^2 S_in - S_out] is PD", ok,
           f"form matches G_1 to rel. {worst_rel:.2e} at |u|~1e-4/1e-5; min eigenvalue "
           f"{eig_min:.6f} > 0; (1-2p)^2 - C = {R2 - CAP:.6f} > 0; "
           f"chi2-SDPI slack (b*p)(1-b*p) - b(1-b) = {sdpi:.6f} > 0")


def c3_h3(n):
    """(H3): delta = C h - J >= 0, zeros exactly {0,1/2,1}; BEC(h(p)) is more capable."""
    xs = np.linspace(0, 1, n)
    dv = delta(xs)
    ok = dv.min() > -1e-15
    zeros = xs[dv < 1e-9]
    d = [f"min delta over {n} points = {dv.min():.3e}"]
    d.append(f"delta(0) = {float(delta(np.array(0.0))):.3e}, "
             f"delta(1/2) = {float(delta(np.array(0.5))):.3e}, "
             f"delta(1) = {float(delta(np.array(1.0))):.3e}")
    # the only near-zeros are the three known ones
    isolated = all(min(abs(z - 0.0), abs(z - 0.5), abs(z - 1.0)) < 2e-4 for z in zeros)
    ok &= isolated
    d.append(f"all near-zeros within 2e-4 of {{0,1/2,1}}: {isolated}")
    record("C3 (H3) delta >= 0 with zeros exactly {0,1/2,1} (more capable, boundary)", ok,
           "; ".join(d))


def c3b_delta_structure():
    """Elementary proof of delta >= 0: delta'' changes sign exactly once on (0,1/2).

    delta''(x) ln2 = (1-2p)^2 / [(x*p)(1-x*p)] - C / [x(1-x)], whose sign is that of
    N(x) := e (1-2p)^2 x(1-x) - C p(1-p) because (x*p)(1-x*p) = p(1-p) + (1-2p)^2 x(1-x).
    """
    r = 1 - 2 * P_CROSS
    x0 = 0.5 * (1 - np.sqrt(1 - 4 * CAP * P_CROSS * (1 - P_CROSS) / (E_ERAS * r * r)))
    xs = np.linspace(1e-3, 0.5 - 1e-9, 200001)
    q = star(xs, P_CROSS)
    d2_analytic = (r * r / (q * (1 - q)) - CAP / (xs * (1 - xs))) / LN2
    N = E_ERAS * r * r * xs * (1 - xs) - CAP * P_CROSS * (1 - P_CROSS)
    # the quadratic factorisation of (x*p)(1-x*p) that turns delta'' into N
    fact = np.abs(q * (1 - q) - (P_CROSS * (1 - P_CROSS) + r * r * xs * (1 - xs))).max()
    # analytic second derivative vs a central difference, away from the endpoints
    sub = np.linspace(0.05, 0.45, 41)          # away from the endpoint singularity
    hh = 1e-4
    d2_num = (delta(sub + hh) - 2 * delta(sub) + delta(sub - hh)) / hh ** 2
    qs = star(sub, P_CROSS)
    d2_an = (r * r / (qs * (1 - qs)) - CAP / (sub * (1 - sub))) / LN2
    rel = float(np.abs(d2_num - d2_an).max() / np.abs(d2_an).max())
    sign_ok = bool(np.all(np.sign(d2_analytic) == np.sign(N)))
    changes = int(np.sum(np.diff(np.sign(N)) != 0))
    dv = delta(xs)
    conc = xs < x0
    ok = (sign_ok and changes == 1 and fact < 1e-15 and rel < 1e-4
          and dv[conc].min() > -1e-15                      # concave arc, endpoints >= 0
          and float(delta(np.array(x0))) > 0
          and dv[~conc].min() > -1e-15)                    # convex arc, min at 1/2 (delta'=0)
    record("C3b delta'' has exactly one sign change on (0,1/2) (elementary proof of delta>=0)",
           ok,
           f"(x*p)(1-x*p) = p(1-p) + (1-2p)^2 x(1-x) (residual {fact:.3e}) ==> "
           f"sign(delta'') = sign(e (1-2p)^2 x(1-x) - C p(1-p)); sign changes on (0,1/2) = "
           f"{changes} at x0 = {x0:.9f}; analytic delta'' vs central difference rel. {rel:.2e}; "
           f"delta(x0) = {float(delta(np.array(x0))):.9f} > 0; concave arc [1e-3,x0] with "
           f"delta(0)=0, convex arc [x0,1/2] with delta(1/2)=delta'(1/2)=0 ==> delta >= 0")


# ------------------------------------------------------- the identities of the proof


def _sample_fibres(rng, m):
    b = rng.random(m)
    A0 = rng.random(m)
    A1 = rng.random(m)
    edge = rng.random(m) < 0.25
    A0 = np.where(edge, np.round(A0 * 2) / 2, A0)
    A1 = np.where(edge, np.round(A1 * 2) / 2, A1)
    return b, A0, A1


def d2_sdpi_identity(m):
    """I(X1;Y2) - C I(X1;X2) = E_{X1}[delta(B_X1)] - delta(b)."""
    rng = np.random.default_rng(11)
    b, A0, A1 = _sample_fibres(rng, m)
    a, I2, _, _, _, EdB, B0, B1 = fibre_parts(b, A0, A1)
    # I(X1;Y2) = h(b*p) - E_{X1}[h(B_X1 * p)]
    I = h2v(star(b, P_CROSS)) - ((1 - a) * h2v(star(B0, P_CROSS)) + a * h2v(star(B1, P_CROSS)))
    res = np.abs(I - CAP * I2 - (EdB - delta(b)))
    ok = res.max() < 1e-12
    record("D2 identity  I(X1;Y2) - C I(X1;X2) = E[delta(B)] - delta(b)", ok,
           f"{m} random fibres, max residual {res.max():.3e}")


def d3_T_identity(m):
    """T_t = C(1-t)[h(a)+h(b)-C I2] + t S_A + d*_t - S_B."""
    rng = np.random.default_rng(12)
    b, A0, A1 = _sample_fibres(rng, m)
    a, I2, CH, Xi, EdA, EdB, _, _ = fibre_parts(b, A0, A1)
    S_A = E_ERAS * delta(a) + CAP * EdA
    S_B = E_ERAS * delta(b) + CAP * EdB
    worst = 0.0
    for t in [0.0, 0.13, 0.37, 0.5, 0.618, 0.83, 1.0]:
        lhs = T_of(t, b, A0, A1)
        rhs = CAP * (1 - t) * (h2v(a) + h2v(b) - CAP * I2) + t * S_A + dstar(t)[0] - S_B
        worst = max(worst, float(np.abs(lhs - rhs).max()))
    ok = worst < 1e-12
    record("D3 identity  T_t = C(1-t)[h(a)+h(b)-C I2] + t S_A + d*_t - S_B", ok,
           f"{m} fibres x 7 values of t, max residual {worst:.3e}")


def d4_SB_bound(m):
    """S_B <= d*_t + C(1-t)[h(b) - C I2], from psi_t(x) <= d*_t applied at x = b and x = B_i."""
    rng = np.random.default_rng(13)
    b, A0, A1 = _sample_fibres(rng, m)
    a, I2, _, _, _, EdB, B0, B1 = fibre_parts(b, A0, A1)
    S_B = E_ERAS * delta(b) + CAP * EdB
    worst_gap = np.inf
    worst_id = 0.0
    for t in [0.0, 0.13, 0.37, 0.5, 0.618, 0.83, 1.0]:
        dt = dstar(t)[0]
        bound = dt + CAP * (1 - t) * (h2v(b) - CAP * I2)
        worst_gap = min(worst_gap, float((bound - S_B).min()))
        # the intermediate form e[d*+C(1-t)h(b)] + C E[d*+C(1-t)h(B)] equals the bound
        mid = (E_ERAS * (dt + CAP * (1 - t) * h2v(b))
               + CAP * ((1 - a) * (dt + CAP * (1 - t) * h2v(B0))
                        + a * (dt + CAP * (1 - t) * h2v(B1))))
        worst_id = max(worst_id, float(np.abs(mid - bound).max()))
    ok = worst_gap > -1e-12 and worst_id < 1e-12
    record("D4 bound  S_B <= d*_t + C(1-t)[h(b) - C I2]", ok,
           f"{m} fibres x 7 t: min slack {worst_gap:.3e} >= 0; regrouping residual "
           f"{worst_id:.3e} (uses e+C=1 and H(X2|X1) = h(b) - I2)")


def d5_main_bound(m, nt):
    """T_t >= C(1-t) h(a) + t S_A  (D3 minus D4), hence T_t >= 0."""
    rng = np.random.default_rng(14)
    b, A0, A1 = _sample_fibres(rng, m)
    a, I2, _, _, EdA, _, _, _ = fibre_parts(b, A0, A1)
    S_A = E_ERAS * delta(a) + CAP * EdA
    worst = np.inf
    worst_T = np.inf
    for t in np.linspace(0, 1, nt):
        lower = CAP * (1 - t) * h2v(a) + t * S_A
        Tt = T_of(float(t), b, A0, A1)
        worst = min(worst, float((Tt - lower).min()))
        worst_T = min(worst_T, float(Tt.min()))
    ok = worst > -1e-12 and worst_T > -1e-12 and float(S_A.min()) > -1e-15
    record("D5 main bound  T_t >= C(1-t) h(a) + t S_A >= 0", ok,
           f"{m} fibres x {nt} t: min (T_t - lower bound) = {worst:.3e} >= 0, "
           f"min T_t = {worst_T:.3e} >= 0, min S_A = {float(S_A.min()):.3e} >= 0")


def d6_grid_bound(n):
    """Deterministic grid sweep of the same bound (no randomness)."""
    grid = np.linspace(0, 1, n)
    gb, gA0, gA1 = np.meshgrid(grid, grid, grid, indexing="ij")
    a, I2, _, _, EdA, _, _, _ = fibre_parts(gb, gA0, gA1)
    S_A = E_ERAS * delta(a) + CAP * EdA
    worst = np.inf
    argw = None
    for t in np.linspace(0, 1, 21):
        lower = CAP * (1 - t) * h2v(a) + t * S_A
        Tt = T_of(float(t), gb, gA0, gA1)
        gap = Tt - lower
        i = np.unravel_index(np.argmin(gap), gap.shape)
        if gap[i] < worst:
            worst, argw = float(gap[i]), (float(t), float(gb[i]), float(gA0[i]), float(gA1[i]))
    ok = worst > -1e-12
    record("D6 grid sweep of the main bound", ok,
           f"{n}^3 fibres x 21 t: min (T_t - lower bound) = {worst:.3e} at "
           f"(t,b,A0,A1) = ({argw[0]:.2f}, {argw[1]:.4f}, {argw[2]:.4f}, {argw[3]:.4f})")


def d7_equality_set(ng):
    """The bound is tight: it reproduces both equality families exactly."""
    d1, b1 = dstar(1.0)
    rows = []
    ok = True
    for t in [0.0, 0.25, 0.5, 0.75, 1.0]:
        dt, bt = dstar(t)
        v = float(T_of(t, np.array(bt), np.array(0.0), np.array(0.0)))
        rows.append(f"t={t}: X1 const, b=beta*_t -> T = {v:.2e}")
        ok &= abs(v) < 1e-12
    v = float(T_of(1.0, np.array(b1), np.array(0.5), np.array(0.5)))
    rows.append(f"t=1: X1 uniform indep., b=beta*_1 -> T = {v:.2e}")
    ok &= abs(v) < 1e-14
    # strictness off the equality set
    off = float(T_of(0.5, np.array(b1), np.array(0.5), np.array(0.5)))
    ok &= off > 1e-3
    rows.append(f"t=1/2 same fibre -> T = {off:.6f} > 0 (strict)")
    # the derived characterisation is the whole zero set: every grid point with a small T
    # sits within O(sqrt(tau)) of the predicted finite point set (quadratic growth).
    g = np.linspace(0, 1, ng)
    gb, gA0, gA1 = np.meshgrid(g, g, g, indexing="ij")
    tau = 2e-4
    for t in (0.5, 1.0):
        dt, bt = dstar(t)
        aa = [(0.0, 0.0), (1.0, 1.0)] if t < 1 else [(0.0, 0.0), (0.5, 0.5), (1.0, 1.0)]
        pred = [(bb, u, v) for bb in (bt, 1 - bt) for (u, v) in aa]
        # all predicted points are exact zeros
        wz = max(abs(float(T_of(t, np.array(P[0]), np.array(P[1]), np.array(P[2]))))
                 for P in pred)
        dist = np.full(gb.shape, np.inf)
        for (bb, u, v) in pred:
            dist = np.minimum(dist, np.maximum(np.maximum(np.abs(gb - bb), np.abs(gA0 - u)),
                                               np.abs(gA1 - v)))
        Z = T_of(t, gb, gA0, gA1) < tau
        far = float(dist[Z].max()) if Z.any() else 0.0
        ok &= wz < 1e-12 and far < 0.09
        rows.append(f"t={t}: {len(pred)} predicted zeros all exact (max |T| = {wz:.1e}); "
                    f"{int(Z.sum())} of {gb.size} grid points with T < {tau:.0e}, all within L-inf "
                    f"{far:.3f} of them")
    record("D7 the bound is tight, and the derived equality set is the whole zero set", ok,
           "; ".join(rows))


def d8_n7p_counterexample():
    """The N7-p rational point s = (0, 3/8, 1/2, 1/8) has G_1 < 0 but T_1 > 0."""
    s = np.array([0.0, 3 / 8, 1 / 2, 1 / 8])
    b, A0, A1 = fibre_from_s(s)
    g1 = float(G_of(1.0, np.array(b), np.array(A0), np.array(A1)))
    T1 = float(T_of(1.0, np.array(b), np.array(A0), np.array(A1)))
    a, I2, _, _, EdA, _, _, _ = fibre_parts(np.array(b), np.array(A0), np.array(A1))
    S_A = float(E_ERAS * delta(a) + CAP * EdA)
    ok = g1 < 0 and T1 > 0 and T1 >= S_A - 1e-12
    record("D8 the N7-p rational counterexample to G_1 >= 0 is not one for the target", ok,
           f"s = (0,3/8,1/2,1/8): b = {b}, A0 = {A0}, A1 = {A1}; G_1 = {g1:.9f} < 0, "
           f"T_1 = {T1:.9f} > 0, lower bound t*S_A = {S_A:.9f}")


# ------------------------------------------------------------------- the conclusion


def e1_omega_lower(nt):
    """Omega(t) >= d*_t: the X1-deterministic laws achieve psi_t(beta)."""
    worst = 0.0
    for t in np.linspace(0, 1, nt):
        dt, bt = dstar(float(t))
        s = s_from_fibre(bt, 0.0, 0.0)
        worst = max(worst, abs(Omega_at(s, float(t)) - dt))
    ok = worst < 1e-12
    record("E1 Omega(t) >= d*_t attained by X1-deterministic laws (residual)", ok,
           f"{nt} values of t, max |Omega(s_det,t) - d*_t| = {worst:.3e}")


def e2_omega_equals(nt):
    """Omega(t) = d*_t exactly: upper bound from D5, lower from E1."""
    worst = 0.0
    for t in np.linspace(0, 1, nt):
        dt = dstar(float(t))[0]
        # exhaustive check of the upper bound over a fibre grid, via T >= 0
        grid = np.linspace(0, 1, 61)
        gb, gA0, gA1 = np.meshgrid(grid, grid, grid, indexing="ij")
        worst = min(worst, float(T_of(float(t), gb, gA0, gA1).min()))
    ok = worst > -1e-12
    record("E2 Omega(t) = d*_t, i.e. min_s f_t = F*(t) exactly (eps = 0)", ok,
           f"{nt} values of t x 61^3 fibres: min T_t = {worst:.3e} >= 0; "
           f"combined with D5 (proof) and E1 (attainment) ==> equality")


def e3_bridge(nt):
    """R1(beta) + t R2(beta) = 2C + psi_t(beta) pointwise (so the max is 2C + d*_t),
    and H(Y)_unif - F*(t) - t H(Z|X) = 2C + d*_t."""
    betas = np.linspace(0, 1, 4001)
    R1 = CAP + 1 - h2v(star(betas, P_CROSS))
    Rb2 = CAP * h2v(betas)
    psi_v = np.array([[psi(float(t), float(x)) for x in betas] for t in (0.0, 0.5, 1.0)])
    w0 = 0.0
    for k, t in enumerate((0.0, 0.5, 1.0)):
        w0 = max(w0, float(np.abs(R1 + t * Rb2 - (2 * CAP + psi_v[k])).max()))
    w2 = 0.0
    for t in np.linspace(0, 1, nt):
        dt = dstar(float(t))[0]
        Fstar = (1 - t) * H_Y_GIVEN_X - dt
        w2 = max(w2, abs((CAP + h2(E_ERAS) + 1.0) - Fstar - t * H_Z_GIVEN_X - (2 * CAP + dt)))
    w3 = abs(2 * CAP - (CAP + 1 - h2(P_CROSS)))
    ok = w0 < 1e-13 and w2 < 1e-13 and w3 < 1e-15
    record("E3 bridge  R1(b)+t R2(b) = 2C + psi_t(b)  and  H(Y)_unif - F*(t) - t H(Z|X) = 2C + d*_t",
           ok,
           f"pointwise bridge residual {w0:.3e} over 4001 beta x 3 t (so max_beta = 2C + d*_t "
           f"by definition of d*); the C+1-h(p) = 2C step residual {w3:.3e}; "
           f"{nt} values of t: closing identity residual {w2:.3e}")


def e4_screen_search(n):
    """SCREEN (not evidence): random + local search for a violation of T_t >= 0."""
    rng = np.random.default_rng(99)
    best = np.inf
    argb = None
    for _ in range(n):
        t = float(rng.random())
        b, A0, A1 = _sample_fibres(rng, 1)
        b, A0, A1 = float(b[0]), float(A0[0]), float(A1[0])
        v = float(T_of(t, np.array(b), np.array(A0), np.array(A1)))
        if v < best:
            best, argb = v, (t, b, A0, A1)
        # local descent
        step = 0.1
        cur = (t, b, A0, A1)
        for _ in range(60):
            improved = False
            for k in range(4):
                for sg in (+1, -1):
                    cand = list(cur)
                    cand[k] = min(max(cand[k] + sg * step, 0.0), 1.0)
                    vv = float(T_of(cand[0], np.array(cand[1]), np.array(cand[2]),
                                    np.array(cand[3])))
                    if vv < v - 1e-16:
                        v, cur, improved = vv, tuple(cand), True
            if not improved:
                step *= 0.5
                if step < 1e-9:
                    break
        if v < best:
            best, argb = v, cur
    ok = best > -1e-12
    record("E4 screen: search for a violation of T_t >= 0 (SCREEN, not evidence)", ok,
           f"{n} restarts with local descent: best (most negative) T = {best:.3e} at "
           f"(t,b,A0,A1) = ({argb[0]:.5f}, {argb[1]:.5f}, {argb[2]:.5f}, {argb[3]:.5f})")


# ----------------------------------------------------------- class, not instance


class Instance:
    """A detunable rebuild: X1 -> BEC(e)/BSC(p), X2 -> BSC(p)/BEC(e).  e = h(p) gives [probc].

    Everything is local, so nothing here perturbs the [probc] globals used above.
    """

    def __init__(self, p, e=None):
        self.p = p
        self.e = h2(p) if e is None else e
        self.Cb = 1.0 - self.e                 # BEC capacity: I(X1;Y1|W) = Cb H(X1|W)
        bec = np.array([[1 - self.e, 0.0, self.e], [0.0, 1 - self.e, self.e]])
        bsc = np.array([[1 - p, p], [p, 1 - p]])
        MYl = np.zeros((4, 6))
        MZl = np.zeros((4, 6))
        for x1 in range(2):
            for x2 in range(2):
                x = 2 * x1 + x2
                for y1 in range(3):
                    for y2 in range(2):
                        MYl[x, 2 * y1 + y2] = bec[x1, y1] * bsc[x2, y2]
                for z1 in range(2):
                    for z2 in range(3):
                        MZl[x, 3 * z1 + z2] = bsc[x1, z1] * bec[x2, z2]
        self.MY, self.MZ = MYl, MZl
        self.HYX = h2(self.e) + h2(p)
        self.HZX = h2(p) + h2(self.e)

    def J(self, x):
        return h2v(star(x, self.p)) - h2(self.p)

    def delta(self, x):
        return self.Cb * h2v(x) - self.J(x)

    def psi(self, t, x):
        return t * self.Cb * h2v(x) - self.J(x)

    def dstar(self, t):
        xs = np.concatenate([np.linspace(0, 0.5, 200001),
                             np.exp(np.linspace(np.log(1e-12), np.log(0.5), 20001))])
        return float(self.psi(t, xs).max())

    def Omega_grid(self, t, n):
        g = np.linspace(0, 1, n)
        gb, gA0, gA1 = np.meshgrid(g, g, g, indexing="ij")
        s = np.stack([(1 - gb) * (1 - gA0), gb * (1 - gA1),
                      (1 - gb) * gA0, gb * gA1], axis=-1).reshape(-1, 4)
        qy = s @ self.MY
        qz = s @ self.MZ
        with np.errstate(divide="ignore", invalid="ignore"):
            ly = np.where(qy > 0, -qy * np.log2(np.maximum(qy, 1e-300)), 0.0).sum(1)
            lz = np.where(qz > 0, -qz * np.log2(np.maximum(qz, 1e-300)), 0.0).sum(1)
        return float((t * (lz - self.HZX) - (ly - self.HYX)).max())

    def parts(self, b, A0, A1):
        a = (1 - b) * A0 + b * A1
        py1 = star(b, self.p)
        py0 = 1 - py1
        j1 = (1 - b) * A0 * self.p + b * A1 * (1 - self.p)
        j0 = (1 - b) * A0 * (1 - self.p) + b * A1 * self.p
        al1 = np.where(py1 > 0, j1 / np.where(py1 > 0, py1, 1.0), 0.0)
        al0 = np.where(py0 > 0, j0 / np.where(py0 > 0, py0, 1.0), 0.0)
        CH = self.Cb * (py0 * h2v(al0) + py1 * h2v(al1))
        Xi = self.e * self.J(a) + self.Cb * ((1 - b) * self.J(A0) + b * self.J(A1))
        EdA = (1 - b) * self.delta(A0) + b * self.delta(A1)
        return a, CH, Xi, EdA


def g1_other_p(ps, m):
    """The chain is p-generic: only e + Cb = 1 and delta >= 0 are used."""
    rows = []
    ok = True
    rng = np.random.default_rng(7)
    b, A0, A1 = _sample_fibres(rng, m)
    xs = np.linspace(0, 1, 20001)
    for p in ps:
        ins = Instance(p)
        dmin = float(ins.delta(xs).min())
        a, CH, Xi, EdA = ins.parts(b, A0, A1)
        S_A = ins.e * ins.delta(a) + ins.Cb * EdA
        w = np.inf
        for t in np.linspace(0, 1, 11):
            T = CH - t * Xi + ins.dstar(float(t)) - ins.psi(float(t), b)
            w = min(w, float((T - (ins.Cb * (1 - t) * h2v(a) + t * S_A)).min()))
        rows.append(f"p={p}: min delta = {dmin:+.2e}, min (T - bound) = {w:+.2e}")
        ok &= dmin > -1e-14 and w > -1e-8
    record("G1 class not instance: same chain for other p (e = h(p) kept)", ok, "; ".join(rows))


def g2_negative_control(n):
    """Two structurally different negative controls that e = h(p) is load-bearing.

    (i) e > h(p): delta = Cb h - J goes negative (BEC no longer more capable) and the
        target Omega(t) <= d*_t fails by about the same amount.
    (ii) e < h(p): delta stays >= 0 but is strictly positive at x = 1/2, and the target
        holds with slack -- the equality structure of [probc] is destroyed in the other
        direction, so e = h(p) is exactly the boundary, not an interior choice.
    """
    rows = []
    ok = True
    xs = np.linspace(0, 1, 20001)
    for shift in (-0.05, -0.02, +0.02, +0.05):
        ins = Instance(P_CROSS, e=h2(P_CROSS) + shift)
        dmin = float(ins.delta(xs).min())
        d_half = float(ins.delta(np.array(0.5)))
        worst = np.inf
        for t in np.linspace(0, 1, 21):
            worst = min(worst, ins.dstar(float(t)) - ins.Omega_grid(float(t), n))
        rows.append(f"e=h(p){shift:+.2f}: min delta = {dmin:+.5f}, delta(1/2) = {d_half:+.5f}, "
                    f"min_t [d*_t - Omega] = {worst:+.5f}")
        if shift > 0:
            ok &= dmin < -1e-3 and worst < -1e-3
        else:
            ok &= dmin > -1e-12 and d_half > 1e-3 and worst > -1e-9
    record("G2 negative control: e = h(p) is load-bearing (both directions)", ok, "; ".join(rows))


# ------------------------------------------------------------------------- driver


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    q = args.quick
    t0 = time.time()

    a1_constants()
    a2_channel()
    a3_fibre_identity(400 if q else 3000)
    c1_h1(201 if q else 801)
    c1b_beta_star()
    c2_h2()
    c2b_hessian()
    c3_h3(20001 if q else 200001)
    c3b_delta_structure()
    d2_sdpi_identity(20000 if q else 120000)
    d3_T_identity(20000 if q else 120000)
    d4_SB_bound(20000 if q else 120000)
    d5_main_bound(20000 if q else 120000, 11 if q else 31)
    d6_grid_bound(41 if q else 101)
    d7_equality_set(101 if q else 161)
    d8_n7p_counterexample()
    e1_omega_lower(101 if q else 501)
    e2_omega_equals(9 if q else 21)
    e3_bridge(101 if q else 401)
    e4_screen_search(20 if q else 100)
    g1_other_p([0.02, 0.05, 0.2, 0.35] if q else [0.01, 0.02, 0.05, 0.2, 0.35, 0.45],
               5000 if q else 20000)
    g2_negative_control(31 if q else 61)

    npass = sum(1 for _, ok, _ in RESULTS if ok)
    n = len(RESULTS)
    print(f"\n{npass}/{n} tests passed in {time.time() - t0:.1f} s"
          f"{' (--quick)' if q else ''}")
    sys.exit(0 if npass == n else 1)


if __name__ == "__main__":
    main()
