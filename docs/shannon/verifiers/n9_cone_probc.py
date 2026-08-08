#!/usr/bin/env python3
"""Leg N9: the cone 0 < lam0 < lam1+lam2 for the [probc] instance.

The question the cone was reduced to (N6-g / N6-n) is "D = C?", where

    K       := C|_{R0=0}                                   (the R0=0 slice)
    D       := { R >= 0 : R0 <= 2C, (R0+R1, R2) in K, (R1, R0+R2) in K }
    D'      := the same with K replaced by Thm7|_{R0=0}

and Thm7 subset D' is unconditional (box projection identity, N6-g/N6-n).

This file is a *fresh* implementation: it does not import, exec or otherwise
run capacity_probc.py / n6_audit_probc.py / shoulder_certificate_probc.py.
The mutual informations, the mirrored Theorem 3 caps and the beta-split family
are re-derived here and calibrated against the constants the ledger carries.

Orientation (checked, not assumed): [probc] Theorem 3 is stated for "Z1 more
capable than Y1, Y2 more capable than Z2"; the Lemma 8 instance has the
opposite orientation in both blocks, so Theorem 3 is applied after the receiver
swap Y <-> Z (which swaps R1 <-> R2).  The mirrored region carries the
auxiliaries V1 (block 1, receiver Z) and U2 (block 2, receiver Y).

Instance:  X = (X1,X2) in {0,1}^2,  X1 -> Y1 = BEC(e), X1 -> Z1 = BSC(p),
           X2 -> Y2 = BSC(p), X2 -> Z2 = BEC(e),  p = 0.1, e = h(p).

Run:  python3 docs/shannon/verifiers/n9_cone_probc.py
Exit code 0 iff every test passes.
"""
import argparse

import numpy as np
from scipy.optimize import brentq, linprog, minimize_scalar

LOG2 = np.log(2.0)
EPS_N7 = 2.0786e-07          # the N7 tolerance, quoted from ## N7 (T3c) N7-a


# --------------------------------------------------------------- information


def H(v):
    v = np.asarray(v, dtype=float).ravel()
    v = v[v > 1e-300]
    return float(-(v * np.log(v)).sum() / LOG2)


def h2(a):
    if a <= 0.0 or a >= 1.0:
        return 0.0
    return float(-a * np.log2(a) - (1.0 - a) * np.log2(1.0 - a))


def dh2(a):
    """h'(a) = log2((1-a)/a)."""
    return float(np.log2((1.0 - a) / a))


def bec(e):
    return np.array([[1.0 - e, 0.0, e], [0.0, 1.0 - e, e]])


def bsc(p):
    return np.array([[1.0 - p, p], [p, 1.0 - p]])


def block_infos(P, TY, TZ):
    """Every mutual information of one [probc] block.

    P[w, a, x] is a joint law of (W, A, X), A the block's auxiliary.
    Written by chain rules on plain entropies (deliberately a different code
    shape from the other verifiers in this directory).
    """
    P = np.asarray(P, dtype=float)
    P = P / P.sum()
    out = {}
    for tag, T in (("Y", TY), ("Z", TZ)):
        # joint of (w, a, x, b)
        Q = P[:, :, :, None] * T[None, None, :, :]
        Hb = H(Q.sum(axis=(0, 1, 2)))
        Hw = H(P.sum(axis=(1, 2)))
        Ha_w = H(P.sum(axis=2))
        Hx_w = H(P.sum(axis=1))
        Hxa_w = H(P)
        Hwb = H(Q.sum(axis=(1, 2)))
        Hawb = H(Q.sum(axis=2))
        Hxwb = H(Q.sum(axis=1))
        Hxawb = H(Q)
        out["IW" + tag] = Hw + Hb - Hwb
        out["IA" + tag + "_W"] = Ha_w + Hwb - Hawb - Hw
        out["IX" + tag + "_W"] = Hx_w + Hwb - Hxwb - Hw
        out["IX" + tag + "_AW"] = Hxa_w + Hawb - Hxawb - Ha_w
    return out


def theorem3_caps(P1, P2, ch):
    """(M, B1, B2, S1, S2) of [probc] Theorem 3 after the receiver swap.

    P1[w1, v1, x1] (block 1 auxiliary V1, receiver Z),
    P2[w2, u2, x2] (block 2 auxiliary U2, receiver Y).
    """
    a = block_infos(P1, ch["TY1"], ch["TZ1"])
    b = block_infos(P2, ch["TY2"], ch["TZ2"])
    M = min(a["IWY"] + b["IWY"], a["IWZ"] + b["IWZ"])
    B1 = M + a["IXY_W"] + b["IAY_W"]
    B2 = M + a["IAZ_W"] + b["IXZ_W"]
    S1 = M + b["IXZ_W"] + min(a["IAZ_W"] + a["IXY_AW"], a["IXY_W"])
    S2 = M + min(b["IXZ_W"], b["IAY_W"] + b["IXZ_AW"]) + a["IXY_W"]
    return M, B1, B2, S1, S2


def instance(p=0.1):
    e = h2(p)
    return {"p": p, "e": e, "TY1": bec(e), "TZ1": bsc(p),
            "TY2": bsc(p), "TZ2": bec(e)}


# ---------------------------------------------------------------- constants


def constants(p=0.1):
    e = h2(p)
    C = 1.0 - e

    def star(a):
        return a * (1.0 - p) + (1.0 - a) * p

    def psi(a):
        return C * h2(a) - (h2(star(a)) - h2(p))

    def dpsi(a):
        return C * dh2(a) - (1.0 - 2.0 * p) * dh2(star(a))

    astar = brentq(dpsi, 1e-9, 0.5 - 1e-12, xtol=1e-16, rtol=8.9e-16)
    dstar = psi(astar)
    return {"p": p, "e": e, "C": C, "star": star, "psi": psi, "dpsi": dpsi,
            "astar": astar, "dstar": dstar, "twoC": 2.0 * C,
            "SR": 2.0 * C + dstar,
            "ceiling": C + 1.0 - h2(star(astar)),
            "seg_lo": C * h2(astar)}


# ------------------------------------------------- the beta-split arc of K_b


def arc(K, beta):
    """(R1, R2, M, S) of the beta-split witness (V1 = U2 = const)."""
    p, C = K["p"], K["C"]
    R1 = C + 1.0 - h2(K["star"](beta))
    R2 = C * h2(beta)
    M = C * (1.0 - h2(beta)) + 1.0 - h2(K["star"](beta))
    S = R1 + R2
    return R1, R2, M, S


def split_witness(beta):
    """W = beta-split of a uniform X on one block, auxiliary = constant."""
    P = np.zeros((2, 1, 2))
    P[0, 0, 0] = 0.5 * (1.0 - beta)
    P[0, 0, 1] = 0.5 * beta
    P[1, 0, 0] = 0.5 * beta
    P[1, 0, 1] = 0.5 * (1.0 - beta)
    return P


def g_beta(K, a, b):
    """Support function of K_b = down-closed conv(arc u mirror-arc) at (a,b).

    K_b is the C-side lower bound the N7 certificate is stated against.
    """
    if a < 0 or b < 0:
        raise ValueError("K_b is only probed in the non-negative orthant")
    if b > a:
        a, b = b, a
    if a == 0.0:
        return 0.0
    # stationarity of a*R1(beta) + b*R2(beta):
    #     b*C*h'(beta) = a*(1-2p)*h'(beta*p)
    p, C = K["p"], K["C"]

    def deriv(beta):
        return b * C * dh2(beta) - a * (1.0 - 2.0 * p) * dh2(K["star"](beta))

    best = a * arc(K, 0.0)[0]                       # beta -> 0 endpoint = 2aC
    lo, hi = 1e-14, 0.5 - 1e-14
    if b > 0.0 and deriv(lo) > 0.0 > deriv(hi):
        bs = brentq(deriv, lo, hi, xtol=1e-16, rtol=8.9e-16)
        R1, R2, _, _ = arc(K, bs)
        best = max(best, a * R1 + b * R2)
    R1, R2, _, _ = arc(K, 0.5)
    return max(best, a * R1 + b * R2)


def beta_of_sigma(K, sigma):
    """The beta in [0, alpha*] with S(beta) = sigma (sigma in [2C, SR_C])."""
    f = lambda t: arc(K, t)[3] - sigma
    if sigma <= K["twoC"]:
        return 0.0
    if sigma >= K["SR"]:
        return K["astar"]
    return brentq(f, 0.0, K["astar"], xtol=1e-16, rtol=8.9e-16)


def r_beta(K, sigma):
    """max { x : (x, sigma - x) in K_b }."""
    if sigma <= K["twoC"]:
        return sigma
    return arc(K, beta_of_sigma(K, sigma))[0]


def r_L(K, sigma, eps):
    """max { x : (x, sigma - x) in K_b + [0,eps]^2 }, -inf if the level is empty.

    # corrected by N9audit (訂正 3): the first version took this boundary to be
    r_beta(sigma) + eps, which is BELOW the truth because r_beta decreases in
    sigma on [2C, SR_C] -- the shortfall reaches 8.151e-04 = 3921 eps near the
    sum-rate face, where dr_beta/dsigma blows up.  Writing a point of the level
    sigma as (a + u, b + v) with (a, b) in K_b and u, v in [0, eps] gives
    x <= min(eps, t) + r_beta(sigma - t) for t = u + v, and the maximum over
    t in [0, 2 eps] is taken here.  Its breakpoints are t = 0, eps, 2 eps and
    the two where sigma - t hits 2C / SR_C; a grid is added for safety.  The
    level is non-empty up to sigma = SR_C + 2 eps, not SR_C.
    """
    cands = [0.0, eps, 2.0 * eps, sigma - K["twoC"], sigma - K["SR"]]
    cands += list(np.linspace(0.0, 2.0 * eps, 17))
    best = -np.inf
    for t in cands:
        if t < 0.0 or t > 2.0 * eps:
            continue
        s = sigma - t
        if s < 0.0 or s > K["SR"]:
            continue
        best = max(best, min(eps, t) + r_beta(K, s))
    return best


# ---------------------------------------------------------- support of a box


def max1d(f, lo, hi, grid=2001):
    """Maximise a smooth 1-D function: coarse grid, then Brent refinement.

    Used to evaluate max_beta h_Box(beta) without going through the
    stationarity equation g_beta solves, so the two are independent.
    """
    xs = np.linspace(lo, hi, grid)
    vals = np.array([f(x) for x in xs])
    i = int(vals.argmax())
    a = xs[max(0, i - 1)]
    b = xs[min(grid - 1, i + 1)]
    res = minimize_scalar(lambda x: -f(x), bounds=(a, b), method="bounded",
                          options={"xatol": 1e-14})
    return max(float(vals[i]), float(-res.fun))


def level_vertices(sigma, rs):
    """Vertices of {R >= 0 : sum = sigma, R0+R1 <= rs, R0+R2 <= rs}."""
    if sigma <= 0.0:
        return [(0.0, 0.0, 0.0)]
    if rs >= sigma:
        return [(sigma, 0.0, 0.0), (0.0, sigma, 0.0), (0.0, 0.0, sigma)]
    if 2.0 * rs < sigma:
        return []
    return [(0.0, rs, sigma - rs), (0.0, sigma - rs, rs),
            (2.0 * rs - sigma, sigma - rs, sigma - rs)]


def level_vertices_capped(sigma, rs, cap0):
    """Vertices of {R >= 0 : sum = sigma, R0 <= cap0, R0+R1 <= rs, R0+R2 <= rs}.

    An exact 2-D vertex enumeration in (R0, R1) with R2 = sigma - R0 - R1, so a
    level can be swept at its extreme points rather than sampled.
    """
    cons = [(-1.0, 0.0, 0.0),           # R0 >= 0
            (0.0, -1.0, 0.0),           # R1 >= 0
            (1.0, 1.0, sigma),          # R2 >= 0
            (1.0, 0.0, cap0),           # R0 <= cap0
            (1.0, 1.0, rs),             # R0 + R1 <= rs
            (0.0, -1.0, rs - sigma)]    # R0 + R2 <= rs
    out = []
    for i in range(len(cons)):
        for j in range(i + 1, len(cons)):
            A = np.array([cons[i][:2], cons[j][:2]], dtype=float)
            if abs(float(np.linalg.det(A))) < 1e-13:
                continue
            x = np.linalg.solve(A, np.array([cons[i][2], cons[j][2]]))
            if all(c0 * x[0] + c1 * x[1] <= rhs + 1e-12 for c0, c1, rhs in cons):
                out.append((float(x[0]), float(x[1]),
                            float(sigma - x[0] - x[1])))
    return out


def box_support(caps, lam):
    """max <lam, R> over {R >= 0 : R0<=M, R0+R1<=B1, R0+R2<=B2, sum<=S}."""
    M, B1, B2, S1, S2 = caps
    S = min(S1, S2)
    A = np.array([[1.0, 0.0, 0.0], [1.0, 1.0, 0.0],
                  [1.0, 0.0, 1.0], [1.0, 1.0, 1.0]])
    res = linprog(-np.asarray(lam, dtype=float), A_ub=A,
                  b_ub=np.array([M, B1, B2, S]), bounds=(0.0, None),
                  method="highs")
    return float(-res.fun)


def box_support_closed(caps, lam):
    """(lam0 - lam_max)^+ M + (lam_max - lam_min) B_max + lam_min S."""
    M, B1, B2, S1, S2 = caps
    S = min(S1, S2)
    l0, l1, l2 = lam
    if l1 >= l2:
        lmax, lmin, Bmax = l1, l2, B1
    else:
        lmax, lmin, Bmax = l2, l1, B2
    return max(0.0, l0 - lmax) * M + (lmax - lmin) * Bmax + lmin * S


def in_box(caps, R, tol=1e-12):
    M, B1, B2, S1, S2 = caps
    S = min(S1, S2)
    R0, R1, R2 = R
    return (R0 <= M + tol and R0 + R1 <= B1 + tol and R0 + R2 <= B2 + tol
            and R0 + R1 + R2 <= S + tol and min(R) >= -tol)


# ---------------------------------------------------------------- D_b itself


def in_D(K, R, tol=1e-12, cap0=None, r=None, sig_max=None):
    """Membership in D_b = {R >= 0 : R0 <= 2C, both projections in K_b}.

    # corrected by N9audit (訂正 3): sig_max is now a parameter.  It was hard
    wired to SR_C, which silently discarded the band sigma in (SR_C, SR_C+2eps]
    whenever this was called on the eps-inflated set (see c15).
    """
    r = r or (lambda s: r_beta(K, s))
    cap0 = K["twoC"] if cap0 is None else cap0
    sig_max = K["SR"] if sig_max is None else sig_max
    R0, R1, R2 = R
    if min(R) < -tol or R0 > cap0 + tol:
        return False
    sigma = R0 + R1 + R2
    if sigma > sig_max + tol:
        return False
    rs = r(min(sigma, sig_max))
    return R0 + R1 <= rs + tol and R0 + R2 <= rs + tol


def D_violation(K, R):
    """How far R sits outside D_b (<= 0 means inside), in rate units."""
    R0, R1, R2 = R
    sigma = R0 + R1 + R2
    rs = r_beta(K, min(max(sigma, 0.0), K["SR"]))
    return max(-min(R), R0 - K["twoC"], sigma - K["SR"],
               R0 + R1 - rs, R0 + R2 - rs)


def D_support_numeric(K, lam, grid=1201):
    """max <lam, R> over D_b, computed by a sigma sweep + a small LP.

    Independent of the closed form the leg derives -- used only to cross-check
    it, never as the evidence.
    """
    A = np.array([[1.0, 1.0, 0.0], [1.0, 0.0, 1.0], [1.0, 0.0, 0.0]])

    def at_level(sigma):
        rs = r_beta(K, min(max(sigma, 0.0), K["SR"]))
        res = linprog(-np.asarray(lam, dtype=float), A_ub=A,
                      b_ub=np.array([rs, rs, K["twoC"]]),
                      A_eq=np.ones((1, 3)), b_eq=np.array([sigma]),
                      bounds=(0.0, None), method="highs")
        return float(-res.fun) if res.status == 0 else 0.0

    return max1d(at_level, 0.0, K["SR"], grid=grid)


def D_support_closed(K, lam):
    """g_beta(a, b) with a = max(lam), b = min(lam1, lam2, (l1+l2-l0)^+)."""
    l0, l1, l2 = lam
    a = max(l0, l1, l2)
    b = min(l1, l2, max(0.0, l1 + l2 - l0))
    return g_beta(K, a, b)


# ------------------------------------------------------------------- tests

RESULTS = []


def record(name, ok, detail):
    RESULTS.append((name, ok, detail))
    print(f"[{'ok ' if ok else 'FAIL'}] {name}: {detail}")


LEDGER = {"C": 0.5310044064, "astar": 0.0776696702, "dstar": 0.0387713705,
          "SR": 1.1007801833, "ceiling": 0.8916098871, "seg_lo": 0.2091702962}


def c1_constants(K):
    worst, where = 0.0, ""
    for k, v in LEDGER.items():
        d = abs(K[k] - v)
        if d > worst:
            worst, where = d, k
    record("C1 constants vs bc-facts ## N1/## N6", worst < 5e-10,
           f"max |ours - ledger| = {worst:.3e} at {where}; C={K['C']:.10f} "
           f"a*={K['astar']:.10f} d*={K['dstar']:.10f} SR_C={K['SR']:.10f} "
           f"ceiling={K['ceiling']:.10f} seg_lo={K['seg_lo']:.10f}")


def c2_orientation(K, ch):
    """The mirrored reading: psi >= 0 (screen) and the alpha*-split caps."""
    lo = min(K["psi"](a) for a in np.linspace(1e-6, 1 - 1e-6, 20001))
    P = split_witness(K["astar"])
    M, B1, B2, S1, S2 = theorem3_caps(P, P, ch)
    dev = max(abs(B1 - K["ceiling"]), abs(B2 - K["ceiling"]),
              abs(S1 - K["SR"]), abs(S2 - K["SR"]))
    record("C2 mirrored Theorem 3 orientation + alpha*-split caps",
           lo > -1e-12 and dev < 1e-12,
           f"min_a [I(X;Y1)-I(X;Z1)] = {lo:.3e} (>=0 only after the receiver "
           f"swap); alpha*-split caps (M,B1,B2,S1,S2) = ({M:.10f}, {B1:.10f}, "
           f"{B2:.10f}, {S1:.10f}, {S2:.10f}), dev from ceiling / SR_C = "
           f"{dev:.3e}")


def c3_arc_closed_form(K, ch):
    """The evaluator reproduces R1(beta), R2(beta), M(beta), S(beta)."""
    worst = 0.0
    for beta in np.linspace(0.0, 0.5, 101):
        P = split_witness(beta)
        M, B1, B2, S1, S2 = theorem3_caps(P, P, ch)
        R1, R2, Mc, Sc = arc(K, beta)
        worst = max(worst, abs(M - Mc), abs(B1 - R1), abs(B2 - R1),
                    abs(S1 - Sc), abs(S2 - Sc))
    record("C3 beta-split caps match the closed forms", worst < 1e-12,
           f"max |evaluator - closed form| over (M,B1,B2,S1,S2) = {worst:.3e} "
           f"on 101 values of beta in [0, 1/2]")


def c4_redundancy_identity(K, ch):
    """M(beta) = R1(beta) - R2(beta), i.e. S = B1 + B2 - M.

    This is the load-bearing identity of the leg: the R0 ceiling of every
    beta-split box sits exactly at the level the other three caps already
    force, so it is redundant inside the box.
    """
    worst_sym, worst_ev = 0.0, 0.0
    for beta in np.linspace(0.0, 0.5, 401):
        R1, R2, M, S = arc(K, beta)
        worst_sym = max(worst_sym, abs(M - (R1 - R2)), abs(S - (2 * R1 - M)))
        P = split_witness(beta)
        Me, B1e, B2e, S1e, S2e = theorem3_caps(P, P, ch)
        worst_ev = max(worst_ev, abs(S1e - (B1e + B2e - Me)),
                       abs(S2e - (B1e + B2e - Me)))
    record("C4 R0-ceiling redundancy identity  S = B1 + B2 - M",
           worst_sym < 1e-15 and worst_ev < 1e-12,
           f"max |M - (R1-R2)| = {worst_sym:.3e} (closed forms) and "
           f"max |S - (B1+B2-M)| = {worst_ev:.3e} (evaluator) over 401 beta")


def c5_identity_is_structural(K, ch, rng, draws=150):
    """Class test: S = B1+B2-M for EVERY witness with V1 = U2 = const,
    and S < B1+B2-M strictly as soon as an auxiliary is non-trivial."""
    worst_const = 0.0
    for _ in range(draws):
        nw1, nw2 = int(rng.integers(1, 5)), int(rng.integers(1, 5))
        P1 = rng.dirichlet(0.6 * np.ones(nw1 * 2)).reshape(nw1, 1, 2)
        P2 = rng.dirichlet(0.6 * np.ones(nw2 * 2)).reshape(nw2, 1, 2)
        M, B1, B2, S1, S2 = theorem3_caps(P1, P2, ch)
        worst_const = max(worst_const, abs(S1 - (B1 + B2 - M)),
                          abs(S2 - (B1 + B2 - M)))
    gaps = []
    for _ in range(draws):
        na1, na2 = int(rng.integers(2, 4)), int(rng.integers(2, 4))
        nw1, nw2 = int(rng.integers(1, 3)), int(rng.integers(1, 3))
        P1 = rng.dirichlet(0.6 * np.ones(nw1 * na1 * 2)).reshape(nw1, na1, 2)
        P2 = rng.dirichlet(0.6 * np.ones(nw2 * na2 * 2)).reshape(nw2, na2, 2)
        M, B1, B2, S1, S2 = theorem3_caps(P1, P2, ch)
        gaps.append(B1 + B2 - M - min(S1, S2))
    gaps = np.array(gaps)
    record("C5 the identity is structural (const aux) and fails otherwise",
           worst_const < 1e-12 and gaps.min() > -1e-12 and gaps.max() > 1e-3,
           f"trivial auxiliaries: max |S - (B1+B2-M)| = {worst_const:.3e} over "
           f"{draws} random (W1,W2); non-trivial auxiliaries: B1+B2-M-S in "
           f"[{gaps.min():.3e}, {gaps.max():.6f}] over {draws} witnesses -- "
           f"so the R0 ceiling is redundant exactly on the const-aux family")


def c6_sigma_sweep(K):
    """S(beta) increases strictly from 2C to SR_C on [0, alpha*]."""
    bs = np.linspace(0.0, K["astar"], 4001)
    S = np.array([arc(K, b)[3] for b in bs])
    dmin = float(np.diff(S).min())
    record("C6 S(beta) is a bijection [0,alpha*] -> [2C, SR_C]",
           dmin > 0.0 and abs(S[0] - K["twoC"]) < 1e-14
           and abs(S[-1] - K["SR"]) < 1e-14,
           f"S(0) = {S[0]:.10f} (2C = {K['twoC']:.10f}), S(alpha*) = "
           f"{S[-1]:.10f} (SR_C = {K['SR']:.10f}), min increment = "
           f"{dmin:.3e} over 4001 points")


def c7_arc_is_concave(K):
    """dR2/dR1 is monotone along the arc, so conv(arc)'s Pareto face is
    the arc itself (needed for r_beta = R1(beta(sigma))).

    # corrected by N9audit (訂正 5): the slope has NO finite lower bound.
    The value -4.1735 the first version reported as the start of the range was
    the bottom end of a linear grid np.linspace(1e-6, alpha*, 4001), not an
    infimum -- dR2/dR1 ~ -0.209 log2(1/beta) diverges as beta -> 0, so the arc
    is vertical at the beta = 0 corner and carries no finite Lipschitz constant
    there.  What the leg actually needs is the monotonicity, which does hold on
    all of (0, alpha*]; it is re-checked here on a log grid down to 1e-300.
    """
    p, C = K["p"], K["C"]

    def slope(b):
        return -(C * dh2(b)) / ((1.0 - 2.0 * p) * dh2(K["star"](b)))

    # beta increases => R1 decreases; concavity of R2(R1) <=> slope increasing
    lin = np.array([slope(b) for b in np.linspace(1e-6, K["astar"], 4001)])
    log = np.array([slope(b) for b in np.logspace(-300.0, -6.0, 30001)])
    dlin, dlog = float(np.diff(lin).min()), float(np.diff(log).min())
    tail = ", ".join(f"slope({b:.0e}) = {slope(b):.2f}"
                     for b in (1e-6, 1e-20, 1e-100, 1e-300))
    record("C7 the arc is the concave Pareto face of K_b",
           dlin > 0.0 and dlog > 0.0,
           f"dR2/dR1 is strictly increasing on (0, alpha*] -- min increment "
           f"{dlog:.3e} on a log grid 1e-300..1e-6 and {dlin:.3e} on a linear "
           f"grid 1e-6..alpha* -- and reaches {lin[-1]:.6f} at alpha*, so no "
           f"chord of the arc pokes outside it.  It is NOT bounded below: "
           f"{tail} (log divergence, i.e. the arc is vertical at beta = 0)")


def c8_r_beta_certificate(K):
    """r_beta(sigma) = R1(beta(sigma)), certified by the tangent line.

    At the arc point beta the supporting direction is (1, t_b) with
    t_b = (1-2p) h'(beta*p) / (C h'(beta)) < 1 for beta < alpha*, and
    x + t_b (sigma - x) <= R1 + t_b R2 forces x <= R1(beta).
    """
    p, C = K["p"], K["C"]
    worst_t, worst_g, worst_x = -1e9, 0.0, 0.0
    for beta in np.linspace(1e-7, K["astar"] * (1.0 - 1e-6), 400):
        R1, R2, _, S = arc(K, beta)
        tb = (1.0 - 2.0 * p) * dh2(K["star"](beta)) / (C * dh2(beta))
        worst_t = max(worst_t, tb - 1.0)
        worst_g = max(worst_g, g_beta(K, 1.0, tb) - (R1 + tb * R2))
        worst_x = max(worst_x, abs(r_beta(K, S) - R1))
    record("C8 r_beta(sigma) = R1(beta(sigma)) with a tangent certificate",
           worst_t < 0.0 and abs(worst_g) < 1e-12 and worst_x < 1e-8,
           f"max (t_b - 1) = {worst_t:.3e} (< 0 so the tangent bounds x), "
           f"max |g_b(1,t_b) - (R1 + t_b R2)| = {worst_g:.3e}, "
           f"max |r_beta(S(beta)) - R1(beta)| = {worst_x:.3e} over 400 beta")


def c9_slice_symmetry(K):
    """K_b is R1 <-> R2 symmetric, so l_beta(sigma) = sigma - r_beta(sigma)."""
    worst = 0.0
    for t in np.linspace(0.0, 1.0, 201):
        worst = max(worst, abs(g_beta(K, 1.0, t) - g_beta(K, t, 1.0)))
    record("C9 K_b is R1<->R2 symmetric (so l = sigma - r)", worst < 1e-13,
           f"max |g_b(1,t) - g_b(t,1)| = {worst:.3e} over 201 directions -- "
           f"the mirror of the arc is in the family by construction")


def c10_D_subset_C(K, ch):
    """D_b subset of union_beta Box(beta): the leg's main inclusion.

    For each sigma, the extreme points of D_b at that level are checked
    against Box(beta(sigma)) -- not sampled interior points.
    """
    worst = -1e9
    checked = 0
    for sigma in np.linspace(1e-6, K["SR"], 241):
        beta = beta_of_sigma(K, sigma)
        caps = theorem3_caps(split_witness(beta), split_witness(beta), ch)
        rs = r_beta(K, sigma)
        for R in level_vertices(sigma, rs):
            M, B1, B2, S1, S2 = caps
            slack = min(M - R[0], B1 - R[0] - R[1], B2 - R[0] - R[2],
                        min(S1, S2) - sum(R))
            worst = max(worst, -slack)
            checked += 1
    record("C10 D_b is contained in the union of the beta-split boxes",
           worst < 1e-12,
           f"max violation of Box(beta(sigma)) over {checked} extreme points "
           f"of D_b (241 levels of sigma) = {worst:.3e}")


def c11_C_subset_D(K, ch):
    """Box(beta) subset of D_b, so D_b = union_beta Box(beta) exactly."""
    worst = 0.0
    for beta in np.linspace(0.0, K["astar"], 61):
        caps = theorem3_caps(split_witness(beta), split_witness(beta), ch)
        M, B1, B2, S1, S2 = caps
        S = min(S1, S2)
        verts = [(0.0, 0.0, 0.0), (M, 0.0, 0.0), (0.0, B1, 0.0),
                 (0.0, 0.0, B2), (0.0, B1, S - B1), (0.0, S - B2, B2),
                 (M, B1 - M, S - B1), (M, S - B2, B2 - M)]
        for R in verts:
            if min(R) < -1e-12 or not in_box(caps, R):
                continue
            if not in_D(K, R, tol=1e-10):
                worst = max(worst, 1.0)
    record("C11 every beta-split box is contained in D_b", worst == 0.0,
           f"all vertices of Box(beta) for 61 values of beta lie in D_b "
           f"=> D_b = union_beta Box(beta) (with C10)")


def c12_support_identity(K, ch):
    """h_{D_b}(lam) = g_b(max lam, min(l1, l2, (l1+l2-l0)^+))."""
    dirs = []
    for l0 in np.linspace(0.05, 2.4, 25):
        for l2 in np.linspace(0.05, 1.0, 8):
            dirs.append((l0, 1.0, l2))
    worst_cf, worst_num, wd = 0.0, 0.0, None
    for lam in dirs:
        cf = D_support_closed(K, lam)
        beta_max = max1d(lambda b: box_support_closed(
            theorem3_caps(split_witness(b), split_witness(b), ch), lam),
            0.0, K["astar"], grid=401)
        if abs(cf - beta_max) > worst_cf:
            worst_cf, wd = abs(cf - beta_max), lam
    for lam in [(1.1, 1, 1), (1.2, 1, 1), (1.5, 1, 1), (1.3, 1, 0.7),
                (1.0, 1, 0.5), (1, 1, 1), (2, 1, 1)]:
        worst_num = max(worst_num,
                        abs(D_support_closed(K, lam)
                            - D_support_numeric(K, lam, grid=801)))
    record("C12 the cone support function is a reparametrised slice value",
           worst_cf < 1e-9 and worst_num < 1e-6,
           f"max |g_b(a,b) - max_beta h_Box(beta)| = {worst_cf:.3e} over 200 "
           f"cone directions (worst {wd}); max |closed form - sigma-sweep LP| "
           f"= {worst_num:.3e} on the 7 directions of N6-g")


def c13_n6_directions(K, ch):
    """The seven directions N6 screened, now as closed-form values."""
    rows, worst = [], 0.0
    for lam in [(1, 1, 1), (1.1, 1, 1), (1.2, 1, 1), (1.5, 1, 1), (2, 1, 1),
                (1, 1, 0.5), (1.3, 1, 0.7)]:
        hd = D_support_closed(K, lam)
        hc = max1d(lambda b: box_support(
            theorem3_caps(split_witness(b), split_witness(b), ch), lam),
            0.0, K["astar"], grid=401)
        worst = max(worst, abs(hd - hc))
        rows.append(f"{lam}: h={hd:.10f} (diff {hd - hc:+.1e})")
    record("C13 the seven N6 directions close by identity", worst < 1e-9,
           f"max |h_{{D_b}} - max_beta h_Box| = {worst:.3e}; " + "; ".join(rows))


def c14_box_projection(rng, draws=20000):
    """N6-g re-derived independently: phi and its mirror map each box into
    itself, hence through arbitrary unions and intersections of boxes."""
    bad = 0
    for _ in range(draws):
        A, B1, B2, S = rng.uniform(0.0, 2.0, 4)
        R = rng.uniform(0.0, 2.0, 3)
        caps = (A, B1, B2, S, S)
        if not in_box(caps, R):
            continue
        phi = (0.0, R[0] + R[1], R[2])
        psi = (0.0, R[1], R[0] + R[2])
        if not in_box(caps, phi) or not in_box(caps, psi):
            bad += 1
    record("C14 box projection identity (independent re-derivation of N6-g)",
           bad == 0, f"{bad} violations of phi(B) subset B / psi(B) subset B "
                     f"over {draws} random (box, point) pairs")


def c15_epsilon_bookkeeping(K, rng, draws=4000):
    """D(K_b + [0,eps]^2) subset D_b + {0} x [0,eps]^2, so the tolerance
    travels with coefficient 1 per rate coordinate and 0 on R0.

    # corrected by N9audit (訂正 2 / 訂正 3), on three counts:
      - the translation is the componentwise truncated one, R - (0, min(R1,eps),
        min(R2,eps)).  The verbatim R - (0,eps,eps) is false at R = (0,0,0)
        (negative coordinates), and the first version skipped precisely that
        boundary with `if min(shifted) < -1e-15: continue`.
      - the outer set uses the true right boundary r_L(sigma) instead of
        r_beta(sigma) + eps (訂正 3), and the sum level now runs to SR_C + 2 eps,
        so the band sigma in (SR_C, SR_C + 2 eps] -- the one where eps bites
        hardest in the sum-rate direction -- is swept instead of discarded.
      - the extreme points of every level are enumerated exactly; the random
        draws of the first version are kept alongside but they remain a SCREEN.
    ⚠ this is still a numerical sweep, not an identity: the identity-level
    backing for this step is the independent audit (support-function branches +
    an endpoint sweep on the true r_L), not this test.
    """
    eps = EPS_N7
    sig_max = K["SR"] + 2.0 * eps
    rL = lambda s: r_L(K, s, eps)

    def shift(R):
        return (R[0], R[1] - min(R[1], eps), R[2] - min(R[2], eps))

    # (a) exact extreme points of every level of D(K_b + [0,eps]^2)
    sig = np.unique(np.concatenate([
        np.linspace(0.0, sig_max, 2001),
        np.linspace(K["SR"] - 2.0 * eps, sig_max, 401),
        np.linspace(K["twoC"] - 2.0 * eps, K["twoC"] + 2.0 * eps, 401)]))
    band = int(((sig > K["SR"]) & (sig <= sig_max)).sum())
    worst_v, checked = -1e9, 0
    for s in sig:
        rs = rL(s)
        if not np.isfinite(rs):
            continue
        for R in level_vertices_capped(s, rs, K["twoC"]):
            if not in_D(K, R, tol=1e-12, r=rL, sig_max=sig_max):
                continue
            checked += 1
            worst_v = max(worst_v, D_violation(K, shift(R)))

    # (b) random interior draws (SCREEN), half of them inside the eps band
    worst_r, drawn = -1e9, 0
    for i in range(draws):
        lo = K["SR"] - 2.0 * eps if i % 2 else 0.0
        sigma = rng.uniform(lo, sig_max)
        rs = rL(sigma)
        if not np.isfinite(rs):
            continue
        hi0 = min(K["twoC"], max(0.0, 2.0 * rs - sigma))
        R0 = rng.uniform(0.0, hi0) if hi0 > 0.0 else 0.0
        R1 = rng.uniform(max(0.0, sigma - R0 - rs), max(0.0, sigma - R0))
        R = (R0, R1, sigma - R0 - R1)
        if min(R) < 0.0 or not in_D(K, R, tol=1e-14, r=rL, sig_max=sig_max):
            continue
        drawn += 1
        worst_r = max(worst_r, D_violation(K, shift(R)))

    record("C15 the N7 tolerance travels with coefficient lam1 + lam2",
           worst_v < 1e-9 and worst_r < 1e-9 and band > 0 and drawn > 0,
           f"max violation of 'R - (0, min(R1,eps), min(R2,eps)) in D_b' = "
           f"{worst_v:.3e} over {checked} exact extreme points of "
           f"D(K_b+[0,eps]^2) ({len(sig)} sum levels up to SR_C + 2 eps, of "
           f"which {band} lie in the band (SR_C, SR_C+2eps]) and {worst_r:.3e} "
           f"over {drawn} random draws (eps = {eps:.4e}) -- so h_D' <= "
           f"h_{{D_b}} + eps(lam1+lam2), i.e. 2 eps = {2 * eps:.4e} at "
           f"lam1 = lam2 = 1")


def c16_negative_control_polytope():
    """Structurally different control 1: the N6-n rational polytope, whose
    R0 ceiling sits strictly below the redundant level."""
    outer = (0.5, 1.0, 1.0, 1.0, 1.0)
    inner = (0.0, 1.0, 1.0, 1.0, 1.0)
    ho = box_support(outer, (2, 1, 1))
    hi = box_support(inner, (2, 1, 1))
    # D of the common slice {x,y >= 0 : x <= 1, y <= 1, x+y <= 1}
    hd = 2.0                       # attained at (1, 0, 0), sum = 1
    slack_o = (outer[1] + outer[2] - min(outer[3], outer[4])) - outer[0]
    record("C16 negative control 1: N6-n's polytope (non-redundant ceiling)",
           abs(ho - 1.5) < 1e-12 and abs(hi - 1.0) < 1e-12 and hd > ho + 0.4
           and slack_o > 0.4,
           f"h_outer(2,1,1) = {ho:.6f}, h_inner(2,1,1) = {hi:.6f}, "
           f"h_D(slice)(2,1,1) = {hd:.6f}; B1+B2-S-M = {slack_o:.3f} > 0 so "
           f"the criterion of C4 correctly predicts D strictly larger")


def c17_negative_control_witness(K, ch, rng):
    """Structurally different control 2: a genuine Theorem 3 witness with a
    non-trivial auxiliary -- its box is strictly inside D of its own slice."""
    best = None
    for _ in range(400):
        P1 = rng.dirichlet(0.6 * np.ones(2 * 2 * 2)).reshape(2, 2, 2)
        P2 = rng.dirichlet(0.6 * np.ones(2 * 2 * 2)).reshape(2, 2, 2)
        caps = theorem3_caps(P1, P2, ch)
        M, B1, B2, S1, S2 = caps
        S = min(S1, S2)
        slack = B1 + B2 - S - M
        if best is None or slack > best[0]:
            best = (slack, caps)
    slack, caps = best
    M, B1, B2, S1, S2 = caps
    S = min(S1, S2)
    # the point that D of the box's own slice admits but the box does not
    R0 = min(B1 + B2 - S, B1, B2) - 1e-9
    R = (R0, max(0.0, min(B1 - R0, S - R0 - max(0.0, S - B2))),
         max(0.0, S - R0 - max(0.0, min(B1 - R0, S - R0))))
    record("C17 negative control 2: non-trivial auxiliary breaks redundancy",
           slack > 1e-3 and R0 > M + 1e-4,
           f"best witness has B1+B2-S-M = {slack:.6f} > 0, so R0 can reach "
           f"{R0:.6f} under the three slice-driven caps while the box only "
           f"allows M = {M:.6f} -- the mechanism of C4 is not automatic")


def c18_most_general_object(rng):
    """Most-general-object test: any symmetric concave arc whose boxes obey
    S = 2 R1 - M gives D(slice) = union Box, on a synthetic family."""
    us = np.linspace(0.0, 1.0, 241)
    R1 = 2.0 - us ** 2
    R2 = us
    Ssyn = R1 + R2
    keep = np.diff(Ssyn) > 0
    n = int(keep.sum()) + 1
    R1, R2, Ssyn = R1[:n], R2[:n], Ssyn[:n]
    Msyn = R1 - R2
    worst = -1e9
    for i in range(n):
        rs, sigma = R1[i], Ssyn[i]
        for R in level_vertices(sigma, rs):
            slack = min(Msyn[i] - R[0], rs - R[0] - R[1], rs - R[0] - R[2],
                        Ssyn[i] - sum(R))
            worst = max(worst, -slack)
    record("C18 most-general-object test on a synthetic concave family",
           worst < 1e-12,
           f"max violation = {worst:.3e} on a different concave arc "
           f"(R1 = 2 - u^2, R2 = u) obeying the same redundancy identity -- "
           f"the mechanism is structural, not a numerical coincidence")


def c19_screen_general_witnesses(K, ch, rng, draws=3000):
    """SCREEN (non-violation is NOT evidence, plan 4.5): random Theorem 3
    witnesses versus the closed form, in cone directions."""
    dirs = [(1.1, 1, 1), (1.2, 1, 1), (1.5, 1, 1), (1.3, 1, 0.7),
            (1.0, 1, 0.5), (1.8, 1, 1)]
    ref = {d: D_support_closed(K, d) for d in dirs}
    worst, wd = -1e9, None
    for _ in range(draws):
        na1, na2 = int(rng.integers(1, 4)), int(rng.integers(1, 4))
        nw1, nw2 = int(rng.integers(1, 4)), int(rng.integers(1, 4))
        P1 = rng.dirichlet(0.6 * np.ones(nw1 * na1 * 2)).reshape(nw1, na1, 2)
        P2 = rng.dirichlet(0.6 * np.ones(nw2 * na2 * 2)).reshape(nw2, na2, 2)
        caps = theorem3_caps(P1, P2, ch)
        for d in dirs:
            exc = box_support_closed(caps, d) - ref[d]
            if exc > worst:
                worst, wd = exc, d
    record("C19 general witnesses vs the closed form (SCREEN, not evidence)",
           worst < 1e-9,
           f"max [h_Box(w) - g_b(a,b)] = {worst:.3e} at lam={wd} over {draws} "
           f"random Theorem 3 witnesses -- this screens C subset D_b, which "
           f"the leg does NOT claim as proved")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20260808)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)

    K = constants()
    ch = instance()

    c1_constants(K)
    c2_orientation(K, ch)
    c3_arc_closed_form(K, ch)
    c4_redundancy_identity(K, ch)
    c5_identity_is_structural(K, ch, rng)
    c6_sigma_sweep(K)
    c7_arc_is_concave(K)
    c8_r_beta_certificate(K)
    c9_slice_symmetry(K)
    c10_D_subset_C(K, ch)
    c11_C_subset_D(K, ch)
    c12_support_identity(K, ch)
    c13_n6_directions(K, ch)
    c14_box_projection(rng)
    c15_epsilon_bookkeeping(K, rng)
    c16_negative_control_polytope()
    c17_negative_control_witness(K, ch, rng)
    c18_most_general_object(rng)
    c19_screen_general_witnesses(K, ch, rng)

    bad = [n for n, ok, _ in RESULTS if not ok]
    print(f"\n{len(RESULTS) - len(bad)}/{len(RESULTS)} tests passed")
    if bad:
        print("FAILED: " + ", ".join(bad))
    raise SystemExit(1 if bad else 0)


if __name__ == "__main__":
    main()
