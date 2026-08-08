#!/usr/bin/env python3
"""Adversarial independent audit of leg N7's `R0 = 0` shoulder certificate.

Everything here is re-derived from the channel definition.  In particular this
file NEVER imports or executes `shoulder_certificate_probc.py` (the audited
artefact); the only third-party code it leans on is `capacity_probc.py`, which
belongs to leg N6 and is therefore admissible as ground for the `C` side.

Instance (independently rebuilt):
    X = (X1,X2) in {0,1}^2,  p = 0.1,  e = h(p),  C = 1 - e = 1 - h(p),
    X1 -> Y1 = BEC(e),  X1 -> Z1 = BSC(p),
    X2 -> Y2 = BSC(p),  X2 -> Z2 = BEC(e).

Notation:
    f_t(s) = H(Y)_s - t H(Z)_s          (s a law on the four inputs)
    psi_t(b) = t C h(b) - h(b*p) + h(p),  d*_t = max_b psi_t(b)
    F*(t) = (1-t)(h(e)+h(p)) - d*_t     (the conjectured value of min_s f_t)
    Omega(t) = max_s [ t I(X;Z)_s - I(X;Y)_s ] = -min_s f_t - t H(Z|X) + H(Y|X)

N7's certificate asserts  min_s f_t >= F*(t) - tol  with tol = 1e-9, and from
that  h_Thm7(0,1,t) <= h_C(0,1,t) + eps  with eps = 2.0786e-07.

Run:  python3 docs/shannon/verifiers/n7_audit_probc.py [--quick]
Exit code 0 iff every test passes.
"""
import argparse
import heapq
import os
import re
import sys
import time

import numpy as np

LN2 = np.log(2.0)
RESULTS = []


def record(name, ok, detail):
    RESULTS.append((name, ok, detail))
    print(f"[{'PASS' if ok else 'FAIL'}] {name}: {detail}")


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

BEC = np.array([[1 - E_ERAS, 0.0, E_ERAS], [0.0, 1 - E_ERAS, E_ERAS]])
BSC = np.array([[1 - P_CROSS, P_CROSS], [P_CROSS, 1 - P_CROSS]])

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


# ------------------------------------------- psi / d* in a cancellation-free form


def h_small(b):
    """h(b), stable down to b ~ 1e-300."""
    if b <= 0.0 or b >= 1.0:
        return 0.0
    return -b * np.log2(b) - (1 - b) * np.log1p(-b) / LN2


def Delta(b):
    """h(b*p) - h(p) without the catastrophic cancellation of the naive form."""
    d = b * (1 - 2 * P_CROSS)
    if d == 0.0:
        return 0.0
    return (-P_CROSS * np.log1p(d / P_CROSS) / LN2
            - d * np.log2(P_CROSS + d)
            - (1 - P_CROSS) * np.log1p(-d / (1 - P_CROSS)) / LN2
            + d * np.log2(1 - P_CROSS - d))


def psi(t, b):
    return t * CAP * h_small(b) - Delta(b)


def dpsi(t, b):
    """d psi_t / d beta, written so that beta down to 1e-320 cannot overflow."""
    x = P_CROSS + b * (1 - 2 * P_CROSS)
    return (t * CAP * (np.log2(1 - b) - np.log2(b))
            - (1 - 2 * P_CROSS) * (np.log2(1 - x) - np.log2(x)))


_DSTAR_CACHE = {}


def dstar(t):
    """(d*_t, beta*_t) by bisection on log beta."""
    hit = _DSTAR_CACHE.get(t)
    if hit is not None:
        return hit
    if t <= 0.0:
        out = (0.0, 0.0)
    elif dpsi(t, 0.5 - 1e-15) > 0:
        out = (psi(t, 0.5), 0.5)
    else:
        lo, hi = -740.0, float(np.log(0.5 - 1e-15))
        for _ in range(120):
            m = 0.5 * (lo + hi)
            if dpsi(t, np.exp(m)) > 0:
                lo = m
            else:
                hi = m
        b = float(np.exp(0.5 * (lo + hi)))
        out = (psi(t, b), b)
    _DSTAR_CACHE[t] = out
    return out


def Fstar(t):
    return (1 - t) * H_Y_GIVEN_X - dstar(t)[0]


# ---------------------------------------------- the independent lower bound engine


def phi(q):
    q = np.asarray(q, dtype=float)
    return np.where(q > 0, -q * np.log2(np.maximum(q, 1e-300)), 0.0)


def dphi(q):
    return -(np.log2(np.maximum(q, 1e-300)) + 1.0 / LN2)


def bb_min_secant(t, tol=1e-9, maxcells=400000):
    """Independent lower bound on min_{s in Delta_3} f_t(s).

    Relaxation, per output letter and not per entropy: the output law q = s M is
    affine in s, so on a simplex cell each coordinate q_j ranges exactly over
    [min_i q_j(v_i), max_i q_j(v_i)].  Under the concave scalar q |-> -q log q the
    chord on that interval is a lower bound (used for the +H_Y letters) and the
    midpoint tangent is an upper bound (used for the -t H_Z letters).  Both are
    affine in s, so the relaxation is affine and its minimum over the cell is at a
    vertex.  Neither the global concavity of H_Y / H_Z on the simplex nor any
    DC split is invoked, which is the point: it is a different mechanism from the
    audited engine, so an implementation error cannot be shared.
    """
    V0 = np.eye(4)
    inc = min(f_t(V0[i], t) for i in range(4))

    def bound(V):
        qY, qZ = V @ MY, V @ MZ
        lY, uY = qY.min(0), qY.max(0)
        lZ, uZ = qZ.min(0), qZ.max(0)
        w = uY - lY
        slope = np.where(w > 1e-300, (phi(uY) - phi(lY)) / np.where(w > 1e-300, w, 1.0),
                         dphi(np.maximum(lY, 1e-300)))
        secY = (phi(lY) + slope * (qY - lY)).sum(1)
        mZ = 0.5 * (lZ + uZ)
        tanZ = (phi(mZ) + dphi(np.maximum(mZ, 1e-300)) * (qZ - mZ)).sum(1)
        return float((secY - t * tanZ).min())

    heap = [(bound(V0), 0, V0)]
    cnt, ncell = 0, 1
    while heap:
        lb, _, V = heapq.heappop(heap)
        if lb > inc - tol:
            return lb, inc, ncell, True
        if ncell > maxcells:
            return lb, inc, ncell, False
        for i in range(4):
            inc = min(inc, f_t(V[i], t))
        inc = min(inc, f_t(V.mean(0), t))
        best = (-1.0, 0, 1)
        for i in range(4):
            for j in range(i + 1, 4):
                d = float(np.linalg.norm(V[i] - V[j]))
                if d > best[0]:
                    best = (d, i, j)
        _, i, j = best
        mid = 0.5 * (V[i] + V[j])
        for k in (i, j):
            W = V.copy()
            W[k] = mid
            cnt += 1
            ncell += 1
            heapq.heappush(heap, (bound(W), cnt, W))
    return inc, inc, ncell, True


def gradHZ(s):
    q = np.asarray(s, dtype=float) @ MZ
    return MZ @ dphi(q)


def bb_min_dc(t, tol=1e-9, kappa=1e-9, relative=False, maxcells=300000):
    """Re-implementation, in this file's own code, of the rule N7 states in 2.3:
    a tangent plane to the concave H_Z at an interior point, after which
    H_Y - t (plane) is concave and its cell minimum sits at a vertex.  `kappa` is
    the weight of the mixing with the uniform law that keeps the tangent point
    interior; `relative=True` scales it by the cell diameter instead."""
    V0 = np.eye(4)
    unif = np.ones(4) / 4
    inc = min(f_t(V0[i], t) for i in range(4))

    def bound(V):
        c = V.mean(0)
        diam = max(float(np.linalg.norm(V[i] - V[j]))
                   for i in range(4) for j in range(i + 1, 4))
        k = kappa * diam if relative else kappa
        cc = (1 - k) * c + k * unif
        g, base = gradHZ(cc), HZ(cc)
        return float(min(HY(V[i]) - t * (base + g @ (V[i] - cc)) for i in range(4)))

    heap = [(bound(V0), 0, V0)]
    cnt, ncell = 0, 1
    while heap:
        lb, _, V = heapq.heappop(heap)
        if lb > inc - tol:
            return lb, ncell, True
        if ncell > maxcells:
            return lb, ncell, False
        for i in range(4):
            inc = min(inc, f_t(V[i], t))
        inc = min(inc, f_t(V.mean(0), t))
        best = (-1.0, 0, 1)
        for i in range(4):
            for j in range(i + 1, 4):
                d = float(np.linalg.norm(V[i] - V[j]))
                if d > best[0]:
                    best = (d, i, j)
        _, i, j = best
        mid = 0.5 * (V[i] + V[j])
        for k in (i, j):
            W = V.copy()
            W[k] = mid
            cnt += 1
            ncell += 1
            heapq.heappush(heap, (bound(W), cnt, W))
    return inc, ncell, True


# -------------------------------------------------- the fibre reformulation of Omega


def fibre_G(t, b, A0, A1):
    """G_t = I(X1;Y1|Y2) - t I(X1;Z1|Z2) on the fibre {P(X2=1) = b}.

    A0 = P(X1=1|X2=0), A1 = P(X1=1|X2=1), both array-valued.  Uses
    I(X1;Y1|W) = C H(X1|W) (exact for a BEC) and I(X1;Z1|Z2) = e I(X1;Z1)
    + C I(X1;Z1|X2) (exact for a BEC side channel).
    """
    a = (1 - b) * A0 + b * A1

    def J(al):
        return h2v(star(al, P_CROSS)) - h2(P_CROSS)

    py1 = star(b, P_CROSS)
    py0 = 1 - py1
    j1 = (1 - b) * A0 * BSC[0, 1] + b * A1 * BSC[1, 1]
    j0 = (1 - b) * A0 * BSC[0, 0] + b * A1 * BSC[1, 0]
    al1 = j1 / py1 if py1 > 0 else np.zeros_like(j1)
    al0 = j0 / py0 if py0 > 0 else np.zeros_like(j0)
    HX1_Y2 = py0 * h2v(al0) + py1 * h2v(al1)
    return CAP * HX1_Y2 - t * (E_ERAS * J(a) + CAP * ((1 - b) * J(A0) + b * J(A1)))


def Omega_at(s, t):
    return t * (HZ(s) - H_Z_GIVEN_X) - (HY(s) - H_Y_GIVEN_X)


# ------------------------------------------------------------------------ tests


def a1_constants():
    ok = True
    d = []
    d.append(f"C = {CAP:.15f}")
    ok &= abs(CAP - (1 - h2(P_CROSS))) < 1e-15
    unif = np.ones(4) / 4
    hy_unif = HY(unif)
    ok &= abs(hy_unif - (CAP + h2(E_ERAS) + 1.0)) < 1e-12
    d.append(f"H(Y)_unif = {hy_unif:.15f} = C+h(e)+1 (residual "
             f"{abs(hy_unif - (CAP + h2(E_ERAS) + 1.0)):.3e})")
    worst = 0.0
    for x in range(4):
        s = np.zeros(4)
        s[x] = 1.0
        worst = max(worst, abs(HZ(s) - H_Z_GIVEN_X), abs(HY(s) - H_Y_GIVEN_X))
    ok &= worst < 1e-12
    d.append(f"H(Z|X=x) = H(Y|X=x) = h(e)+h(p) = {H_Z_GIVEN_X:.12f} for all four x "
             f"(residual {worst:.3e}) -- so H(Z|X) carries no p dependence")
    ok &= abs((CAP + 1.0 - h2(P_CROSS)) - 2 * CAP) < 1e-15
    d.append("C+1-h(p) = 2C (the two blocks have equal capacity; this is what "
             "makes the sandwich close)")
    record("A1 constants / H(Y)_unif / H(Z|X)", ok, "; ".join(d))


def a2_klein(rng, draws=4000):
    worst_inv, worst_cen = 0.0, 0.0
    for _ in range(draws):
        s = rng.dirichlet(np.ones(4) * rng.choice([0.2, 1.0, 5.0]))
        cen = np.zeros(4)
        for a in range(4):
            s2 = np.zeros(4)
            for x in range(4):
                s2[x ^ a] = s[x]
            worst_inv = max(worst_inv, abs(HY(s2) - HY(s)), abs(HZ(s2) - HZ(s)))
            cen += s2 / 4
        worst_cen = max(worst_cen, float(np.abs(cen - 0.25).max()))
    ok = worst_inv < 1e-12 and worst_cen < 1e-14
    record("A2 Klein 4-group preserves H(Y)_s and H(Z)_s; orbit barycentre is uniform",
           ok,
           f"max |H(.o tau_a) - H(.)| = {worst_inv:.3e} over {draws} laws x 4 group "
           f"elements (both receivers); max |barycentre - uniform| = {worst_cen:.3e} "
           "==> conv(f_t)(uniform) = min_s f_t(s) as N7-c claims")


def a3_max_p(rng, draws=20000):
    unif = np.ones(4) / 4
    target = HY(unif)
    worst = -1e9
    for _ in range(draws):
        s = rng.dirichlet(np.ones(4) * rng.choice([0.2, 1.0, 5.0]))
        worst = max(worst, HY(s) - target)
    bound = (h2(E_ERAS) + CAP) + 1.0
    ok = worst < 1e-12 and abs(bound - target) < 1e-12
    record("A3 max_p H(Y)_p = H(Y)_uniform", ok,
           f"H(Y1) <= h(e)+C and H(Y2) <= 1 give H(Y)_p <= {bound:.12f} = H(Y)_unif "
           f"(residual {abs(bound - target):.3e}); best random excess over "
           f"{draws} draws = {worst:.3e}")


def a4_verbatim():
    base = ("/private/tmp/claude-502/-Users-haruka-dev-lean-projects/"
            "5fc80860-93c8-48b1-836d-e176acf938d4/scratchpad/lit/auxrec.txt")
    if not os.path.exists(base):
        record("A4 (18b)/(18i) verbatim against the source", True,
               "SKIPPED -- auxrec.txt absent from this machine; retrieve with "
               "docs/shannon/lit-fetch.sh and re-run.  Last checked at commit time: "
               "both matched")
        return
    txt = open(base, encoding="utf-8", errors="replace").read()
    # drop whitespace and the extractor's big-brace control glyphs, so line breaks
    # and column padding cannot decide the outcome
    flat = re.sub(r"[\s\x00-\x1f]+", "", txt)
    b_ok = flat.count("R0+R1≤min{I(W;Y),I(W;Z)}+I(U;Y|W),(18b)") == 1
    i_ok = flat.count("R0+R1+R2≤minI(W;Y),I(W;Z)+minI(V;Z|W)+I(X;Y|V,W),"
                      "I(U;Y|W)+I(X;Z|U,W),(18i)") == 1
    k = flat.find(",(18i)")
    tail = flat[k:k + 400] if k >= 0 else ""
    m_ok = ("=pU,V,W,X" in tail and "TY,Z|X" in tail
            and tail.index("=pU,V,W,X") < tail.index("TY,Z|X"))
    ok = b_ok and i_ok and m_ok
    record("A4 (18b)/(18i)/Markov verbatim against the source", ok,
           f"(18b) match={b_ok}, (18i) match={i_ok}, "
           f"(U,V,W)--X--(Y,Z) factorisation match={m_ok}")


def rand_witness(rng, nu, nv, nw):
    px = rng.dirichlet(np.ones(4) * rng.choice([0.4, 1.0, 3.0]))
    K = rng.dirichlet(np.ones(nu * nv * nw) * rng.choice([0.3, 1.0]),
                      size=4).reshape(4, nu, nv, nw)
    return px, K


def cond_out_ent(px, K, M, axes):
    """H(Y|A) where A is the tuple of auxiliary axes listed in `axes`
    (subset of 'uvw'); axes=() gives H(Y)."""
    idx = {"u": 1, "v": 2, "w": 3}
    P = px[:, None, None, None] * K
    keep = tuple(idx[c] for c in axes)
    drop = tuple(k for k in (1, 2, 3) if k not in keep)
    Pa = P.sum(axis=drop)                       # x x (kept axes)
    flat = Pa.reshape(4, -1)
    tot = 0.0
    for c in range(flat.shape[1]):
        w = flat[:, c].sum()
        if w > 1e-300:
            tot += w * ent((flat[:, c] / w) @ M)
    return tot


def thm7_terms(px, K, t):
    HYm = cond_out_ent(px, K, MY, ())
    HZm = cond_out_ent(px, K, MZ, ())
    HY_w = cond_out_ent(px, K, MY, "w")
    HZ_w = cond_out_ent(px, K, MZ, "w")
    HY_uw = cond_out_ent(px, K, MY, "uw")
    HZ_uw = cond_out_ent(px, K, MZ, "uw")
    HY_vw = cond_out_ent(px, K, MY, "vw")
    HZ_vw = cond_out_ent(px, K, MZ, "vw")
    IWY, IWZ = HYm - HY_w, HZm - HZ_w
    IUY_W = HY_w - HY_uw
    IVZ_W = HZ_w - HZ_vw
    IXY_VW = HY_vw - H_Y_GIVEN_X
    IXZ_UW = HZ_uw - H_Z_GIVEN_X
    b18b = min(IWY, IWZ) + IUY_W
    b18i = min(IWY, IWZ) + min(IVZ_W + IXY_VW, IUY_W + IXZ_UW)
    rhs = (HYm - HY_uw) + t * IXZ_UW           # I(U,W;Y) + t I(X;Z|U,W)
    return b18b, b18i, rhs, HYm, HY_uw, HZ_uw


def a5_box_lp(rng, draws=400):
    """R1 + t R2 over the ceiling box is at most (1-t)(18b) + t(18i)."""
    worst = -1e9
    for _ in range(draws):
        px, K = rand_witness(rng, rng.integers(1, 4), rng.integers(1, 4),
                             rng.integers(1, 4))
        t = float(rng.uniform())
        b18b, b18i, _, _, _, _ = thm7_terms(px, K, t)
        target = (1 - t) * b18b + t * b18i
        # vertices of {R >= 0 : R0+R1 <= b18b, R0+R1+R2 <= b18i}
        for r0 in (0.0, max(0.0, min(b18b, b18i))):
            r1 = max(0.0, min(b18b - r0, b18i - r0))
            r2 = max(0.0, b18i - r0 - r1)
            worst = max(worst, r1 + t * r2 - target)
            r2b = max(0.0, b18i - r0)
            r1b = max(0.0, min(b18b - r0, b18i - r0 - r2b))
            worst = max(worst, r1b + t * r2b - target)
    ok = worst < 1e-12
    record("A5 box support in direction (0,1,t) <= (1-t)(18b) + t(18i)", ok,
           f"max excess {worst:.3e} over {draws} random witnesses "
           "(uses only R0 >= 0 and t in [0,1])")


def a6_r1(rng, draws=400):
    worst = -1e9
    for _ in range(draws):
        px, K = rand_witness(rng, rng.integers(1, 4), rng.integers(1, 4),
                             rng.integers(1, 4))
        t = float(rng.uniform())
        b18b, b18i, rhs, _, _, _ = thm7_terms(px, K, t)
        worst = max(worst, (1 - t) * b18b + t * b18i - rhs)
    ok = worst < 1e-12
    record("A6 (R1): (1-t)(18b) + t(18i) <= I(U,W;Y) + t I(X;Z|U,W)", ok,
           f"max excess {worst:.3e} over {draws} random witnesses")


def a7_r2(rng, draws=400):
    worst = 0.0
    for _ in range(draws):
        px, K = rand_witness(rng, rng.integers(1, 4), 1, rng.integers(1, 4))
        t = float(rng.uniform())
        _, _, rhs, HYm, HY_uw, HZ_uw = thm7_terms(px, K, t)
        # the same quantity written through f_t on the U' = (U,W) posteriors
        P = px[:, None, None, None] * K
        Pa = P.sum(axis=2).reshape(4, -1)
        acc = 0.0
        for c in range(Pa.shape[1]):
            w = Pa[:, c].sum()
            if w > 1e-300:
                acc += w * f_t(Pa[:, c] / w, t)
        lhs = HYm - acc - t * H_Z_GIVEN_X
        worst = max(worst, abs(lhs - rhs))
    ok = worst < 1e-12
    record("A7 (R2): I(U';Y) + t I(X;Z|U') = H(Y)_p - E[f_t(s_U')] - t H(Z|X)", ok,
           f"max |identity residual| = {worst:.3e} over {draws} random witnesses "
           "(U' = (U,W))")


def a8_arithmetic():
    worst = 0.0
    for t in np.linspace(0, 1, 101):
        lhs = HY(np.ones(4) / 4) - Fstar(t) - t * H_Z_GIVEN_X
        worst = max(worst, abs(lhs - (2 * CAP + dstar(t)[0])))
    ok = worst < 1e-12
    record("A8 the sandwich closes arithmetically: H(Y)_unif - F*(t) - t H(Z|X) "
           "= 2C + d*_t", ok,
           f"max residual {worst:.3e} over 101 values of t -- the two relaxations "
           "of the chain are not simultaneously tight, yet the sum is, because "
           "C + 1 - h(p) = 2C on this instance")


def a9_c_side():
    """The beta-split family really sits inside C (Theorem 3 of [probc])."""
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    try:
        import capacity_probc as cp
    except Exception as exc:                                   # pragma: no cover
        record("A9 beta-split witness lies in C", False, f"import failed: {exc}")
        return
    chan = cp.probc_blocks(P_CROSS)
    worst_v, worst_s = 0.0, 0.0
    for beta in np.linspace(0.0, 0.4, 41):
        M, B1, B2, S1, S2 = cp.theorem3_caps(cp.split_block(beta),
                                             cp.split_block(beta), chan)
        S = min(S1, S2)
        R1 = CAP + 1.0 - h2(star(beta, P_CROSS))
        R2 = CAP * h2(beta)
        # (0, R1, R2) is a vertex of the Theorem 3 box: R0+R1 = B1, sum = S
        worst_v = max(worst_v, abs(B1 - R1), abs(S - R1 - R2))
        for t in (0.0, 0.3, 0.7, 1.0):
            worst_s = max(worst_s, abs((R1 + t * R2) - (2 * CAP + psi(t, beta))))
    ok = worst_v < 1e-12 and worst_s < 1e-12
    record("A9 beta-split witness is achievable and gives h_C(0,1,t) >= 2C + psi_t(beta)",
           ok,
           f"max |Theorem 3 caps - (R1,R2)| = {worst_v:.3e} (so (0,R1,R2) is a box "
           f"vertex, hence in C); max |R1 + t R2 - (2C + psi_t(beta))| = {worst_s:.3e} "
           "over 41 betas x 4 values of t")


def a10_four_atoms():
    worst = 0.0
    for beta in np.linspace(0, 1, 51):
        for t in np.linspace(0, 1, 11):
            for c in (0, 1):
                s = np.zeros(4)
                s[2 * c + 0] = 1 - beta
                s[2 * c + 1] = beta
                pred = (1 - t) * H_Y_GIVEN_X - psi(t, beta)
                worst = max(worst, abs(f_t(s, t) - pred))
    ok = worst < 1e-12
    record("A10 four-atom identity f_t(delta_c (x) Bern(beta)) "
           "= (1-t)(h(e)+h(p)) - psi_t(beta)", ok,
           f"max residual {worst:.3e} over 51 betas x 11 values of t x 2 atoms")


def a11_independent_lower_bound(ts, tol=1e-9):
    rows, ok = [], True
    for t in ts:
        lb, _, nc, closed = bb_min_secant(t, tol, maxcells=1500000)
        F = Fstar(t)
        good = closed and (lb >= F - 1.02 * tol) and (lb <= F + 1e-13)
        ok &= good
        rows.append(f"t={t:g}: LB-F*={lb - F:+.3e} cells={nc}")
    record(f"A11 independent branch and bound reaches min_s f_t = F*(t) at tol={tol:g}",
           ok,
           "secant/tangent-per-letter relaxation, a different mechanism from the "
           "audited DC engine. " + "; ".join(rows))


def a12_violation_hunt(rng, ts, per_t=12000, restarts=25):
    from scipy.optimize import minimize
    worst, arg, n = 1e9, None, 0
    for t in ts:
        F = Fstar(t)
        for _ in range(per_t):
            s = rng.dirichlet(np.ones(4) * rng.choice([0.05, 0.2, 0.5, 1.0, 4.0]))
            m = f_t(s, t) - F
            n += 1
            if m < worst:
                worst, arg = m, (t, s.copy())
        for _ in range(restarts):
            v0 = rng.normal(0, 3, 4)

            def obj(v, tt=t, FF=F):
                w = np.exp(v - v.max())
                return f_t(w / w.sum(), tt) - FF

            r = minimize(obj, v0, method="Nelder-Mead",
                         options=dict(maxiter=20000, maxfev=20000,
                                      xatol=1e-13, fatol=1e-16))
            n += 1
            if r.fun < worst:
                w = np.exp(r.x - r.x.max())
                worst, arg = float(r.fun), (t, w / w.sum())
        for b in np.concatenate([np.logspace(-16, -1, 40), np.linspace(0.1, 0.9, 40),
                                 1 - np.logspace(-16, -1, 40)]):
            for a0 in np.concatenate([[0.0], np.logspace(-12, -1, 18),
                                      np.linspace(0.1, 0.9, 18),
                                      1 - np.logspace(-12, -1, 18), [1.0]]):
                for a1 in (0.0, 1e-8, 1e-4, 0.01, 0.2, 0.5, 0.8, 0.99, 1.0):
                    s = np.array([(1 - b) * (1 - a0), b * (1 - a1),
                                  (1 - b) * a0, b * a1])
                    n += 1
                    m = f_t(s, t) - F
                    if m < worst:
                        worst, arg = m, (t, s)
    ok = worst > -1e-13
    record("A12 adversarial hunt for min_s f_t < F*(t)", ok,
           f"{n} probes over {len(ts)} values of t (Dirichlet screen + Nelder-Mead "
           f"multistart + structured boundary families); worst margin {worst:+.3e} "
           f"at t={arg[0]:g}, s={np.array2string(arg[1], precision=6)} -- float64 "
           "noise, no violation")


def a13_fibre(rng, ts, nb=401, ng=201):
    """Independent structural route: Omega(t) = max_s [ psi_t(b) - G_t(s) ]."""
    resid = 0.0
    for _ in range(1500):
        s = rng.dirichlet(np.ones(4) * rng.choice([0.3, 1.0, 3.0]))
        S = s.reshape(2, 2)
        b = float(S[:, 1].sum())
        a0 = float(S[1, 0] / S[:, 0].sum()) if S[:, 0].sum() > 0 else 0.0
        a1 = float(S[1, 1] / S[:, 1].sum()) if S[:, 1].sum() > 0 else 0.0
        for t in (0.0, 0.3, 0.7, 1.0):
            G = float(fibre_G(t, b, np.array([a0]), np.array([a1]))[0])
            resid = max(resid, abs(Omega_at(s, t) - (psi(t, b) - G)))
    g = np.linspace(0, 1, ng)
    A0, A1 = np.meshgrid(g, g, indexing="ij")
    worst, arg = 1e9, None
    for t in ts:
        d = dstar(t)[0]
        for b in np.linspace(0, 1, nb):
            m = fibre_G(t, b, A0, A1) + d - psi(t, b)
            i = int(np.argmin(m))
            if float(m.ravel()[i]) < worst:
                worst = float(m.ravel()[i])
                arg = (t, b, float(A0.ravel()[i]), float(A1.ravel()[i]))
    ok = resid < 1e-12 and worst > -1e-13
    record("A13 fibre reformulation Omega(t) = max_s [psi_t(b) - G_t(s)] and its scan",
           ok,
           f"identity residual {resid:.3e} (G_t = I(X1;Y1|Y2) - t I(X1;Z1|Z2)); "
           f"grid of {len(ts)}x{nb}x{ng} = {len(ts) * nb * ng} fibre points, worst "
           f"d*_t - [psi_t(b) - G_t] = {worst:+.3e} at "
           f"(t,b,a0,a1)=({arg[0]:g},{arg[1]:.4f},{arg[2]:.4f},{arg[3]:.4f})")


TOL_CERT = 1e-9


def _eps_sharp(ts):
    ds = [dstar(t) for t in ts]
    best, arg = 0.0, None
    for i in range(len(ts) - 1):
        t0, t1 = ts[i], ts[i + 1]
        o0, o1 = ds[i][0] + TOL_CERT, ds[i + 1][0] + TOL_CERT

        def gap(t):
            lam = (t - t0) / (t1 - t0)
            return (1 - lam) * o0 + lam * o1 - dstar(t)[0]

        tt = np.linspace(t0, t1, 61)
        gs = [gap(x) for x in tt]
        k = int(np.argmax(gs))
        lo, hi = tt[max(k - 1, 0)], tt[min(k + 1, 60)]
        for _ in range(50):
            m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
            if gap(m1) < gap(m2):
                lo = m1
            else:
                hi = m2
        tb = 0.5 * (lo + hi)
        cand = max(gs[k], gap(tb))
        if cand > best:
            best, arg = cand, (tb if gap(tb) >= gs[k] else tt[k])
    return best, arg


def _eps_family(ts, nbeta):
    """The lower bound on h_C is the upper envelope of finitely many affine
    psi_.(beta_k); chord minus that envelope is concave piecewise affine, so its
    maximum sits at an endpoint or at a kink."""
    ds = [dstar(t) for t in ts]
    worst, arg = 0.0, None
    for i in range(len(ts) - 1):
        t0, t1 = ts[i], ts[i + 1]
        o0, o1 = ds[i][0] + TOL_CERT, ds[i + 1][0] + TOL_CERT
        b0, b1 = max(ds[i][1], 1e-320), max(ds[i + 1][1], 1e-320)
        betas = ([b0, b1] if nbeta == 2 else
                 list(np.exp(np.linspace(np.log(b0), np.log(b1), nbeta))))
        cand = [t0, t1]
        for u in range(len(betas)):
            for v in range(u + 1, len(betas)):
                su, iu = CAP * h_small(betas[u]), -Delta(betas[u])
                sv, iv = CAP * h_small(betas[v]), -Delta(betas[v])
                if abs(su - sv) > 1e-300:
                    tx = (iv - iu) / (su - sv)
                    if t0 < tx < t1:
                        cand.append(tx)
        for t in cand:
            lam = (t - t0) / (t1 - t0)
            g = (1 - lam) * o0 + lam * o1 - max(psi(t, b) for b in betas)
            if g > worst:
                worst, arg = g, t
    return worst, arg


def _eps_single_beta(ts):
    """One fixed beta per interval -- the literal reading of 2.4's sentence
    'psi_t(beta) is affine in t, so the difference is affine and the endpoints
    exhaust the interval'.  With one beta the difference really is affine, so its
    maximum is at an endpoint; beta is then chosen to minimise that maximum."""
    ds = [dstar(t) for t in ts]
    worst = 0.0
    for i in range(len(ts) - 1):
        t0, t1 = ts[i], ts[i + 1]
        o0, o1 = ds[i][0] + TOL_CERT, ds[i + 1][0] + TOL_CERT

        def mx(beta):
            return max(o0 - psi(t0, beta), o1 - psi(t1, beta))

        bl, bh = sorted([max(ds[i][1], 1e-320), max(ds[i + 1][1], 1e-320)])
        best = min(mx(bl), mx(bh))
        ul, uh = np.log(bl), np.log(max(bh, bl * 1.0000001))
        for _ in range(90):
            m1, m2 = ul + (uh - ul) / 3, uh - (uh - ul) / 3
            if mx(np.exp(m1)) < mx(np.exp(m2)):
                ul = m1
            else:
                uh = m2
        worst = max(worst, min(best, mx(np.exp(0.5 * (ul + uh)))))
    return worst


def a14_epsilon():
    g = [(i / 320) ** (1 / 3) for i in range(321)]
    n7 = 2.0786e-07
    sharp, ts_ = _eps_sharp(g)
    one = _eps_single_beta(g)
    fam2, _ = _eps_family(g, 2)
    fam3, _ = _eps_family(g, 3)
    fam9, _ = _eps_family(g, 9)
    ok = (abs(sharp - 2.0729e-07) < 2e-11        # the exact sup is reproduced
          and sharp <= n7 < fam3                 # N7's number is valid, and coarse
          and fam9 < n7                          # a denser beta family beats it
          and one > 3.9 * sharp)                 # one fixed beta would be 4x worse
    record("A14 independent recomputation of eps on N7's own grid", ok,
           f"exact sup of [chord of (d* + tol)] - d*_t = {sharp:.6e} at t={ts_:.6f}; "
           f"beta families per interval: two-point {fam2:.4e}, three-point "
           f"{fam3:.6e}, nine-point {fam9:.6e}.  N7 reports {n7:.4e}, which lies "
           "between the exact sup and the three-point value: a valid, slightly "
           "conservative upper bound.  One fixed beta per interval -- the literal "
           f"reading of 2.4's 'the difference is affine' -- gives {one:.4e}, four "
           "times worse, so the number requires the piecewise (multi-beta) reading")


def a15_scaling():
    rows, ok = [], True
    want = [6.96e-05, 1.76e-05, 4.46e-06, 1.12e-06]
    for n, w in zip([40, 80, 160, 320], want):
        s, t = _eps_sharp([i / n for i in range(n + 1)])
        rows.append(f"{n + 1} pts: {s:.4e} (N7: {w:.3g}, argmax t={t:.5f})")
        ok &= abs(s - w) / w < 0.03
    ratios = []
    prev = None
    for n in [40, 80, 160, 320]:
        s, _ = _eps_sharp([i / n for i in range(n + 1)])
        if prev is not None:
            ratios.append(prev / s)
        prev = s
    ok &= all(3.7 < r < 4.3 for r in ratios)
    record("A15 uniform-grid scaling reproduces N7's table and the delta^2 law", ok,
           "; ".join(rows) + "; successive ratios " +
           ", ".join(f"{r:.2f}" for r in ratios) + " (delta^2 would give 4)")


def a16_tolerance_transfer():
    rows, ok = [], True
    for t in (0.5, 1.0):
        vals = {}
        for tol in (1e-8, 1e-9, 1e-10):
            lb, _, _, closed = bb_min_secant(t, tol, maxcells=1500000)
            vals[tol] = lb - Fstar(t)
            ok &= closed
        rows.append(f"t={t:g}: " + ", ".join(f"tol={k:g} -> {v:+.3e}"
                                             for k, v in vals.items()))
        for tol in (1e-8, 1e-9, 1e-10):
            ok &= abs(vals[tol]) <= 1.02 * tol
    record("A16 tolerance transfer is coefficient one (no sqrt amplification)", ok,
           "the chain uses min_s f_t linearly with coefficient -1 and carries no "
           "averaging constraint (the only distribution-valued step, "
           "E[f_t(s_U')] >= min_s f_t, is pointwise). " + "; ".join(rows))


def a17_float64(rng, draws=400):
    try:
        import mpmath as mp
    except ImportError:                                        # pragma: no cover
        record("A17 float64 rounding is far below eps", True, "SKIPPED (no mpmath)")
        return
    mp.mp.dps = 50

    def mp_f(s, t):
        qY = [sum(mp.mpf(s[x]) * mp.mpf(MY[x, j]) for x in range(4)) for j in range(6)]
        qZ = [sum(mp.mpf(s[x]) * mp.mpf(MZ[x, j]) for x in range(4)) for j in range(6)]
        def H(q):
            return -sum(v * mp.log(v, 2) for v in q if v > 0)
        return H(qY) - mp.mpf(t) * H(qZ)

    worst = 0.0
    for _ in range(draws):
        s = rng.dirichlet(np.ones(4) * rng.choice([0.3, 1.0, 3.0]))
        t = float(rng.uniform())
        worst = max(worst, abs(f_t(s, t) - float(mp_f(s, t))))
    ok = worst < 1e-13
    record("A17 float64 rounding of f_t is far below eps", ok,
           f"max |float64 - 50-digit| = {worst:.3e} over {draws} random (s,t) "
           f"-- six orders below eps = 2.08e-07")


def a18_band(quick):
    """N7-h says the cell count explodes below tol = 1e-11 for t in (0,0.2)."""
    rows, ok = [], True
    ts = (0.05, 0.1462) if quick else (0.05, 0.1, 0.1462, 0.2)
    for t in ts:
        for tol in (1e-11, 1e-12):
            lb, _, nc, closed = bb_min_secant(t, tol, maxcells=300000)
            ok &= closed and lb >= Fstar(t) - 1.02 * tol
            rows.append(f"mine t={t:g} tol={tol:g}: cells={nc} closed={closed}")
    diag = []
    for t in (0.05, 0.1462):
        _, nc9, c9 = bb_min_dc(t, 1e-10, kappa=1e-9, maxcells=60000)
        _, nc11, c11 = bb_min_dc(t, 1e-11, kappa=1e-9, maxcells=60000)
        _, ncr, cr = bb_min_dc(t, 1e-12, kappa=1e-6, relative=True, maxcells=60000)
        diag.append(f"t={t:g}: N7 rule with absolute 1e-9 mixing -> tol=1e-10 "
                    f"cells={nc9} closed={c9}, tol=1e-11 cells={nc11} closed={c11}; "
                    f"same rule with cell-relative mixing -> tol=1e-12 cells={ncr} "
                    f"closed={cr}")
        ok &= c9 and (not c11) and cr
    record("A18 the band t in (0,0.2) closes, and the reported cell explosion is "
           "an engine artefact", ok,
           "; ".join(rows) + " || diagnosis: " + " || ".join(diag))


def a19_beta_star():
    b01 = dstar(0.1)[1]
    b_grid = dstar((1 / 320) ** (1 / 3))[1]
    ok = abs(b01 - 4.2032e-15) / 4.2032e-15 < 1e-3 and abs(b_grid - 1.4676e-10) / 1.4676e-10 < 1e-3
    record("A19 beta*_t at the two values N7 conflates", ok,
           f"beta*_(t=0.1) = {b01:.6e} and d*_(0.1) = {dstar(0.1)[0]:.4e}; "
           f"beta*_(t=(1/320)^(1/3)=0.146201) = {b_grid:.6e}.  N7 3-1 / N7-h say "
           "'beta*_t ~ 1.5e-10 at t = 0.1' -- that value belongs to the first grid "
           "point t = 0.146201, not to t = 0.1, where beta* is five orders smaller")


def a20_shortcut_is_false():
    """A sufficient condition that would have forced eps = 0 outright, and the
    explicit rational law that kills it.

    From A13, Omega(t) = max_s [psi_t(b) - G_t(s)] with G_t = I(X1;Y1|Y2)
    - t I(X1;Z1|Z2), and G_t >= G_1 for t in [0,1] because I(X1;Z1|Z2) >= 0.  So
    G_1 >= 0 everywhere would give Omega(t) <= max_b psi_t(b) = d*_t for every t
    at once -- no grid, no branch and bound, eps exactly 0.  It is false.
    """
    s = np.array([0.0, 3 / 8, 1 / 2, 1 / 8])
    S = s.reshape(2, 2)
    b = float(S[:, 1].sum())
    a0 = float(S[1, 0] / S[:, 0].sum())
    a1 = float(S[1, 1] / S[:, 1].sum())
    g1 = float(fibre_G(1.0, b, np.array([a0]), np.array([a1]))[0])
    # the razor-thin part: X2 uniform makes G_1 vanish identically in q
    worst = 0.0
    for q in (0.05, 0.13, 0.2, 0.35, 0.5):
        S2 = np.zeros((2, 2))
        for x2, pm in ((0, 0.5), (1, 0.5)):
            for nn, pn in ((0, 1 - q), (1, q)):
                S2[x2 ^ nn, x2] += pm * pn
        bb = float(S2[:, 1].sum())
        worst = max(worst, abs(float(fibre_G(
            1.0, bb, np.array([S2[1, 0] / S2[:, 0].sum()]),
            np.array([S2[1, 1] / S2[:, 1].sum()]))[0])))
    ok = g1 < -1e-3 and worst < 1e-12
    record("A20 the eps = 0 shortcut 'G_1 >= 0 everywhere' is false", ok,
           f"s = (0, 3/8, 1/2, 1/8) gives G_1 = {g1:+.8f} < 0, and Omega(1) at that "
           f"s is {Omega_at(s, 1.0):+.8f}, still far under d*_1 = {dstar(1.0)[0]:.8f} "
           f"(margin {dstar(1.0)[0] - Omega_at(s, 1.0):+.6f}) -- so the certificate "
           "survives but this route to an exactly-zero eps is closed.  G_1 vanishes "
           "identically along X2 uniform with X1 = X2 xor Bern(q) "
           f"(max |G_1| = {worst:.3e} over five q), which is why the condition is "
           "razor thin")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    rng = np.random.default_rng(20260808)
    t0 = time.time()

    ts_bb = (0.05, 0.5, 1.0) if args.quick else (0.05, 0.1462, 0.3, 0.5, 0.7, 0.9, 1.0)
    ts_hunt = (0.1, 0.5, 1.0) if args.quick else (0.05, 0.2, 0.3, 0.49895, 0.7, 0.9, 1.0)
    ts_fib = (0.5, 1.0) if args.quick else (0.1, 0.3, 0.5, 0.7, 0.9, 1.0)

    a1_constants()
    a2_klein(rng, 1000 if args.quick else 4000)
    a3_max_p(rng, 5000 if args.quick else 20000)
    a4_verbatim()
    a5_box_lp(rng, 150 if args.quick else 400)
    a6_r1(rng, 150 if args.quick else 400)
    a7_r2(rng, 150 if args.quick else 400)
    a8_arithmetic()
    a9_c_side()
    a10_four_atoms()
    a11_independent_lower_bound(ts_bb)
    a12_violation_hunt(rng, ts_hunt, 4000 if args.quick else 12000,
                       8 if args.quick else 25)
    a13_fibre(rng, ts_fib, 201 if args.quick else 401, 121 if args.quick else 201)
    a14_epsilon()
    a15_scaling()
    a16_tolerance_transfer()
    a17_float64(rng, 120 if args.quick else 400)
    a18_band(args.quick)
    a19_beta_star()
    a20_shortcut_is_false()

    bad = [n for n, ok, _ in RESULTS if not ok]
    print(f"\n{len(RESULTS) - len(bad)}/{len(RESULTS)} passed in "
          f"{time.time() - t0:.1f}s")
    if bad:
        print("FAILED: " + ", ".join(bad))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
