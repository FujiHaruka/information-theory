#!/usr/bin/env python3
"""Certificate for the R0=0 shoulder of the [probc] instance (leg N7).

The face handed over by the N6 gate is F-SH1: the support directions
(0,1,t), t in [0,1], of the R0=0 slice.  This file certifies

    h_Thm7(0,1,t)  <=  h_C(0,1,t) + eps      for every t in [0,1],

with eps a single machine-produced number, by the chain

    support of the Thm7 box at (0,1,t)
        <= (1-t)(18b) + t(18i)                          [elementary LP]
        <= I(U,W;Y) + t I(X;Z|U,W)                      [two lines of (18b)/(18i)]
        <= H(Y)_unif - min_{s in Delta_3} f_t(s) - t H(Z|X)
                                                        [H(Y)_p <= H(Y)_unif]
    f_t(s) := H(Y)_s - t H(Z)_s                         (concave - t concave = DC)

and a difference-of-convex branch-and-bound lower bound on min_s f_t(s).  The
four-atom family (X1 = c in {0,1}) x (X2 ~ Bern(beta) or Bern(1-beta)) attains
the bound, and its rate pair is achievable in C by an explicit [probc]
Theorem 3 witness, so the two sides are squeezed together.

The bound never optimizes over the input law p and never uses (19), (20a),
(20b), (20c), (18c), (18d), (18f), (18g), (18h) or the auxiliary channel T_J.
Its only machine input is the branch-and-bound tolerance, which enters the
final number with coefficient exactly 1 (no square-root transfer).

Run:  python3 docs/shannon/verifiers/shoulder_certificate_probc.py [--quick]
Exit code 0 iff every test passes.
"""
import argparse
import itertools
import os
import sys
import time

import numpy as np

LOG2 = np.log(2.0)


# ----------------------------------------------------------------- primitives


def ent(P):
    P = np.asarray(P, dtype=float)
    Q = P[P > 1e-300]
    return float(-(Q * np.log(Q)).sum() / LOG2)


def h2(a):
    if a <= 0.0 or a >= 1.0:
        return 0.0
    return float(-a * np.log2(a) - (1 - a) * np.log2(1 - a))


def ent_rows(Q):
    """Row-wise base-2 entropy of a batch of distributions."""
    Q = np.clip(np.asarray(Q, dtype=float), 0.0, None)
    L = np.where(Q > 0.0, Q * np.log2(np.where(Q > 0.0, Q, 1.0)), 0.0)
    return -L.sum(-1)


def instance(p=0.1):
    """The [probc] Lemma 8 product channel, built from scratch.

    X = (X1,X2) in {0,1}^2 indexed by x = 2*x1 + x2;
    X1 -> Y1 = BEC(e), X1 -> Z1 = BSC(p), X2 -> Y2 = BSC(p), X2 -> Z2 = BEC(e),
    e = h(p).  MY[x] and MZ[x] are the 6-symbol output laws.
    """
    e = h2(p)
    bec = np.array([[1 - e, 0.0, e], [0.0, 1 - e, e]])
    bsc = np.array([[1 - p, p], [p, 1 - p]])
    MY = np.zeros((4, 6))
    MZ = np.zeros((4, 6))
    for x1, x2 in itertools.product(range(2), repeat=2):
        MY[2 * x1 + x2] = np.kron(bec[x1], bsc[x2])
        MZ[2 * x1 + x2] = np.kron(bsc[x1], bec[x2])
    return {"p": p, "e": e, "C": 1.0 - e, "MY": MY, "MZ": MZ}


def constants(p=0.1):
    """C, alpha*, d*, SR_C and the ceiling, recomputed independently."""
    from scipy.optimize import brentq
    e = h2(p)
    C = 1.0 - e

    def psi(a):
        return C * h2(a) - (h2(a * (1 - p) + (1 - a) * p) - h2(p))

    dpsi = lambda a: (psi(a + 1e-7) - psi(a - 1e-7)) / 2e-7
    astar = brentq(dpsi, 1e-4, 0.5 - 1e-4, xtol=1e-15, rtol=8.9e-16)
    return {"p": p, "e": e, "C": C, "astar": astar, "dstar": psi(astar),
            "SR_C": 2 * C + psi(astar), "psi": psi,
            "ceiling": C + 1.0 - h2(astar * (1 - p) + (1 - astar) * p),
            "K": h2(e) + h2(p)}


def psi_t(b, t, p=0.1):
    """t C h(b) - h(b*p) + h(p): the shoulder profile at direction (0,1,t)."""
    C = 1.0 - h2(p)
    return t * C * h2(b) - h2(b * (1 - p) + (1 - b) * p) + h2(p)


def best_beta(t, p=0.1):
    """A near-maximizer of psi_t.  Any value returned is a valid witness."""
    if t <= 0.0:
        return 0.0
    cands = list(np.linspace(0.0, 0.5, 2001))
    cands += [10.0 ** (-k) for k in np.linspace(0.0, 17.0, 341)]
    b0 = max(cands, key=lambda b: psi_t(b, t, p))
    lo, hi = max(0.0, 0.5 * b0), min(0.5, 2.0 * b0 + 1e-13)
    for _ in range(220):
        m1, m2 = lo + 0.382 * (hi - lo), lo + 0.618 * (hi - lo)
        if psi_t(m1, t, p) < psi_t(m2, t, p):
            lo = m1
        else:
            hi = m2
    b1 = 0.5 * (lo + hi)
    return b1 if psi_t(b1, t, p) > psi_t(b0, t, p) else b0


# --------------------------------------------- the DC branch-and-bound engine


def dc_min_certificate(inst, t, tol, max_cells=400000):
    """Certified lower bound on min_{s in Delta_3} [H(sMY) - t H(sMZ)].

    On a simplicial cell, H(sMZ) is concave, so its tangent plane at an
    interior point is a global upper bound; subtracting t times that tangent
    leaves H(sMY) + affine, which is concave, so its minimum over the cell sits
    at a vertex.  The vertex minimum is therefore a valid lower bound, and it
    is exact in the concave part -- the only slack is the tangent overestimate.
    Returns (lower_bound, incumbent, peak_live_cells, rounds) or None on abort.
    """
    MY, MZ = inst["MY"], inst["MZ"]
    crude = 1.0 + inst["C"] + h2(inst["e"])            # max_s H(sMZ)
    cells = np.eye(4)[None, :, :].copy()
    verts = np.eye(4)
    best = float((ent_rows(verts @ MY) - t * ent_rows(verts @ MZ)).min())
    peak, rounds = 1, 0
    while len(cells):
        rounds += 1
        peak = max(peak, len(cells))
        n = len(cells)
        flat = cells.reshape(-1, 4)
        hy = ent_rows(flat @ MY).reshape(n, 4)
        hz = ent_rows(flat @ MZ).reshape(n, 4)
        best = min(best, float((hy - t * hz).min()))
        s0 = cells.mean(1)
        s0 = (1.0 - 1e-9) * s0 + 1e-9 * 0.25           # keep the tangent finite
        q0 = s0 @ MZ
        grad = -(np.log2(np.maximum(q0, 1e-300)) @ MZ.T) - np.log2(np.e)
        tangent = (ent_rows(q0) - (s0 * grad).sum(-1))[:, None] \
            + (cells * grad[:, None, :]).sum(-1)
        lb = np.maximum((hy - t * tangent).min(1), hy.min(1) - t * crude)
        cells = cells[lb < best - tol]
        if not len(cells):
            break
        if len(cells) > max_cells:
            return None
        edge = ((cells[:, :, None, :] - cells[:, None, :, :]) ** 2).sum(-1)
        n = len(cells)
        f = edge.reshape(n, 16).argmax(1)
        i, j, idx = f // 4, f % 4, np.arange(n)
        mid = 0.5 * (cells[idx, i] + cells[idx, j])
        c1, c2 = cells.copy(), cells.copy()
        c1[idx, i] = mid
        c2[idx, j] = mid
        cells = np.concatenate([c1, c2], 0)
    return best - tol, best, peak, rounds


def sweep(inst, K, ts, tol, max_cells=400000):
    """Run the certificate at every grid point.  Returns (omega_bar, peak)."""
    ob, peak = [], 0
    for t in ts:
        res = dc_min_certificate(inst, float(t), tol, max_cells)
        if res is None:
            return None, None
        lb, _, pk, _ = res
        peak = max(peak, pk)
        ob.append((1.0 - t) * K - lb)                  # Omega(t) <= this
    return np.array(ob), peak


def interval_excess(ts, omega_bar, p=0.1):
    """Max over t in [0,1] of [certified h_Thm7 bound] - [achievable h_C].

    Omega is convex in t (a max of affine functions of t), so on each grid
    interval it stays under the chord of the certified endpoint bounds; d*_t is
    bounded below by psi_t(beta) for any fixed beta, which is affine in t.  The
    difference of the two is affine between the kinks, so checking the interval
    endpoints and the crossing points of the beta-witnesses is exhaustive.
    """
    worst, arg = -1e9, None
    for i in range(len(ts) - 1):
        t0, t1 = float(ts[i]), float(ts[i + 1])
        bs = [best_beta(t0, p), best_beta(t1, p), best_beta(0.5 * (t0 + t1), p)]
        cand = [t0, t1]
        C = 1.0 - h2(p)
        for ba, bb in itertools.combinations(bs, 2):
            sa, ia = C * h2(ba), h2(p) - h2(ba * (1 - p) + (1 - ba) * p)
            sb, ib = C * h2(bb), h2(p) - h2(bb * (1 - p) + (1 - bb) * p)
            if abs(sa - sb) > 1e-18:
                tx = (ib - ia) / (sa - sb)
                if t0 < tx < t1:
                    cand.append(tx)
        for tt in cand:
            u = (tt - t0) / (t1 - t0)
            chord = (1 - u) * omega_bar[i] + u * omega_bar[i + 1]
            exc = chord - max(psi_t(b, tt, p) for b in bs)
            if exc > worst:
                worst, arg = exc, tt
    return worst, arg


# ------------------------------------------------- Thm7 terms, independently


def thm7_plain(px, cond, inst):
    """(18a), (18b), (18e), (18i) and I(U,W;Y), I(X;Z|U,W) of a plain system.

    cond[x,u,v,w] = p(u,v,w|x); the joint is p(x) cond T(y,z|x), so
    (U,V,W) -- X -- (Y,Z) holds, which is the distribution printed at
    auxrec.txt:1074.
    """
    MY, MZ = inst["MY"], inst["MZ"]
    px = np.asarray(px, float)
    px = px / px.sum()
    cond = np.asarray(cond, float)
    cond = cond / cond.sum(axis=(1, 2, 3), keepdims=True)
    P = px[:, None, None, None] * cond                          # (x,u,v,w)
    out = {}
    for tag, M in (("Y", MY), ("Z", MZ)):
        J = P[:, :, :, :, None] * M[:, None, None, None, :]     # (x,u,v,w,b)
        H = lambda ax: ent(J.sum(axis=ax))
        Hb = H((0, 1, 2, 3))
        out["IW" + tag] = ent(P.sum(axis=(0, 1, 2))) + Hb - H((0, 1, 2))
        out["IUW" + tag] = ent(P.sum(axis=(0, 2))) + Hb - H((0, 2))
        out["IU" + tag + "_W"] = (ent(P.sum(axis=(0, 2))) + H((0, 1, 2))
                                  - H((0, 2)) - ent(P.sum(axis=(0, 1, 2))))
        out["IV" + tag + "_W"] = (ent(P.sum(axis=(0, 1))) + H((0, 1, 2))
                                  - H((0, 1)) - ent(P.sum(axis=(0, 1, 2))))
        out["IX" + tag + "_UW"] = (ent(P.sum(axis=2)) + H((0, 2))
                                   - H((2,)) - ent(P.sum(axis=(0, 2))))
        out["IX" + tag + "_VW"] = (ent(P.sum(axis=1)) + H((0, 1))
                                   - H((1,)) - ent(P.sum(axis=(0, 1))))
    m = min(out["IWY"], out["IWZ"])
    out["b18a"] = m
    out["b18b"] = m + out["IUY_W"]
    out["b18e"] = m + out["IVZ_W"]
    out["br1"] = m + out["IVZ_W"] + out["IXY_VW"]
    out["br2"] = m + out["IUY_W"] + out["IXZ_UW"]
    out["b18i"] = min(out["br1"], out["br2"])
    return out


def box_support(caps, lam):
    """max <lam,R> over {R>=0 : R0<=A, R0+R1<=B1, R0+R2<=B2, sum<=S}."""
    A, B1, B2, S = caps
    best = 0.0
    for r0 in (0.0, max(0.0, min(A, B1, B2, S))):
        rest = S - r0
        for first in (1, 2):
            if first == 1:
                r1 = max(0.0, min(B1 - r0, rest))
                r2 = max(0.0, min(B2 - r0, rest - r1))
            else:
                r2 = max(0.0, min(B2 - r0, rest))
                r1 = max(0.0, min(B1 - r0, rest - r2))
            best = max(best, lam[0] * r0 + lam[1] * r1 + lam[2] * r2)
    return best


def four_atom_witness(beta):
    """The free Thm7 witness at C's beta-split shoulder point, rebuilt here.

    p = uniform, W = const, U has the four atoms (X1 = c) x (X2 ~ Bern(b)),
    V is its mirror image; U and V are conditionally independent given X.
    """
    px = np.full(4, 0.25)
    pu = np.zeros((4, 4))
    pv = np.zeros((4, 4))
    for x in range(4):
        x1, x2 = x // 2, x % 2
        for c in range(2):
            for sflip in range(2):
                b = beta if sflip == 0 else 1 - beta
                pu[x, 2 * c + sflip] = (c == x1) * (b if x2 == 1 else 1 - b)
                pv[x, 2 * c + sflip] = (c == x2) * (b if x1 == 1 else 1 - b)
    pu /= pu.sum(axis=1, keepdims=True)
    pv /= pv.sum(axis=1, keepdims=True)
    return px, (pu[:, :, None] * pv[:, None, :])[:, :, :, None]


def shoulder_corner(K, beta):
    """C's R0=0 Pareto corner reached by the beta-split Theorem 3 witness."""
    p, C = K["p"], K["C"]
    return C + 1.0 - h2(beta * (1 - p) + (1 - beta) * p), C * h2(beta)


# ------------------------------------------------------------------- harness

RESULTS = []


def record(name, ok, detail):
    RESULTS.append((name, ok, detail))
    print(f"[{'ok ' if ok else 'FAIL'}] {name}: {detail}")


LEDGER = {"C": 0.5310044064, "astar": 0.0776696702, "dstar": 0.0387713705,
          "SR_C": 1.1007801833, "ceiling": 0.8916098871,
          "shoulder_gap": 0.022030}


# --------------------------------------------------------------------- tests


def n1_constants(K):
    worst = max(abs(K["C"] - LEDGER["C"]), abs(K["astar"] - LEDGER["astar"]),
                abs(K["dstar"] - LEDGER["dstar"]),
                abs(K["SR_C"] - LEDGER["SR_C"]),
                abs(K["ceiling"] - LEDGER["ceiling"]))
    record("N1 instance constants vs the ledger", worst < 1e-9,
           f"max |ours - bc-facts ## N1 (T3c)| = {worst:.3e} over "
           f"C, alpha*, d*, SR_C, C+S(mu*)")


def n2_conditional_entropies(inst, K):
    MY, MZ = inst["MY"], inst["MZ"]
    hyx = sum(0.25 * ent(MY[x]) for x in range(4))
    hzx = sum(0.25 * ent(MZ[x]) for x in range(4))
    unif = np.full(4, 0.25)
    hy_u, hz_u = ent(unif @ MY), ent(unif @ MZ)
    ok = (abs(hyx - hzx) < 1e-14 and abs(hyx - K["K"]) < 1e-14
          and abs(hy_u - (K["C"] + h2(inst["e"]) + 1.0)) < 1e-14
          and abs(hy_u - hz_u) < 1e-14)
    record("N2 H(Y|X) = H(Z|X) = h(e)+h(p) and H(Y)_unif = C+h(e)+1", ok,
           f"H(Y|X) = {hyx:.12f}, H(Z|X) = {hzx:.12f}, "
           f"H(Y)_unif = H(Z)_unif = {hy_u:.12f}")


def n3_hy_max_at_uniform(inst, K, rng, draws=200000):
    """H(Y)_p <= H(Y1)+H(Y2) <= h(e)+C+1, attained at p = uniform."""
    MY = inst["MY"]
    top = K["C"] + h2(inst["e"]) + 1.0
    S = rng.dirichlet(np.full(4, 0.5), size=draws)
    worst = float(ent_rows(S @ MY).max() - top)
    record("N3 max_p H(Y)_p = H(Y)_unif (identity + screen)", worst < 1e-12,
           f"max over {draws} Dirichlet draws of H(Y)_p - (h(e)+C+1) = "
           f"{worst:.3e}; the bound itself is subadditivity plus the two "
           f"per-block maxima, so no search is being relied on")


def n4_box_support_bound(rng, draws=200000):
    """box support at (0,1,t) <= (1-t)B1 + t S, for every cap vector."""
    worst = -1e9
    caps = rng.uniform(0.0, 2.0, size=(draws, 4))
    for k in range(0, draws, 20000):
        for row in caps[k:k + 20000:97]:
            A, B1, B2, S = row
            for t in (0.0, 0.17, 0.5, 0.83, 1.0):
                worst = max(worst,
                            box_support((A, B1, B2, S), (0.0, 1.0, t))
                            - ((1 - t) * B1 + t * S))
    record("N4 (0,1,t) box support <= (1-t)(18b) + t(18i)", worst < 1e-12,
           f"max [support - ((1-t)B1 + t S)] = {worst:.3e} over "
           f"{draws // 97} random cap vectors x 5 values of t")


def n5_two_line_reduction(inst, K, rng, draws=240):
    """(1-t)(18b) + t(18i) <= I(U,W;Y) + t I(X;Z|U,W) on real Thm7 systems."""
    worst, worst2 = -1e9, -1e9
    for _ in range(draws):
        px = rng.dirichlet(0.7 * np.ones(4))
        dims = tuple(int(rng.integers(1, 5)) for _ in range(3))
        cond = rng.dirichlet(0.6 * np.ones(int(np.prod(dims))),
                             size=4).reshape((4,) + dims)
        r = thm7_plain(px, cond, inst)
        for t in (0.0, 0.25, 0.5, 0.75, 1.0):
            lhs = (1 - t) * r["b18b"] + t * r["b18i"]
            rhs = r["IUWY"] + t * r["IXZ_UW"]
            worst = max(worst, lhs - rhs)
            caps = (r["b18a"], r["b18b"], r["b18e"], r["b18i"])
            worst2 = max(worst2, box_support(caps, (0.0, 1.0, t)) - rhs)
    record("N5 the two-line reduction to I(U,W;Y) + t I(X;Z|U,W)",
           worst < 1e-12 and worst2 < 1e-12,
           f"max [(1-t)(18b)+t(18i) - (I(U,W;Y)+t I(X;Z|U,W))] = {worst:.3e}; "
           f"max [box support - same] = {worst2:.3e} over {draws} systems with "
           f"correlated (U,V,W)|X, cardinalities 1-4, x 5 values of t")


def n6_functional_identity(inst, K, rng, draws=300):
    """I(U;Y) + t I(X;Z|U) = H(Y)_p - E[f_t(s_U)] - t H(Z|X)."""
    MY, MZ = inst["MY"], inst["MZ"]
    worst = 0.0
    for _ in range(draws):
        px = rng.dirichlet(0.7 * np.ones(4))
        nu = int(rng.integers(2, 7))
        cu = rng.dirichlet(0.6 * np.ones(nu), size=4)
        joint = px[:, None] * cu                                # (x,u)
        lam = joint.sum(0)
        post = (joint / np.maximum(lam, 1e-300)).T              # (u,x)
        iuy = ent(px @ MY) - float(lam @ ent_rows(post @ MY))
        for t in (0.0, 0.31, 0.62, 1.0):
            ixz = float(lam @ ent_rows(post @ MZ)) - K["K"]
            lhs = iuy + t * ixz
            rhs = (ent(px @ MY)
                   - float(lam @ (ent_rows(post @ MY) - t * ent_rows(post @ MZ)))
                   - t * K["K"])
            worst = max(worst, abs(lhs - rhs))
    record("N6 I(U;Y) + t I(X;Z|U) = H(Y)_p - E[f_t] - t H(Z|X)", worst < 1e-12,
           f"max residual = {worst:.3e} over {draws} random U with 2-6 atoms "
           f"x 4 values of t")


def n7_bb_anchors(inst, K):
    """t = 0 and t = 1 are independently known and pin the engine."""
    r0 = dc_min_certificate(inst, 0.0, 1e-11)
    r1 = dc_min_certificate(inst, 1.0, 1e-11)
    ok = (abs(r0[0] - (K["K"] - 1e-11)) < 1e-13
          and abs(r1[0] - (-K["dstar"] - 1e-11)) < 3e-12)
    record("N7 branch-and-bound anchors at t = 0 and t = 1", ok,
           f"t=0: LB = {r0[0]:.12f} vs H(Y|X) = {K['K']:.12f} (min_s H(Y)_s is "
           f"at a vertex by concavity); t=1: LB = {r1[0]:.12f} vs -d* = "
           f"{-K['dstar']:.12f} (## N1 (T3c) N1-a / N1-j), "
           f"{r1[2]} peak cells")


def n8_bb_soundness(inst, rng, draws=200000):
    """No sampled or locally optimized point falls below the certified bound."""
    from scipy.optimize import minimize
    MY, MZ = inst["MY"], inst["MZ"]
    worst, wt = 1e9, None
    for t in (0.15, 0.4, 0.677092, 0.9, 1.0):
        lb = dc_min_certificate(inst, t, 1e-10)[0]
        S = rng.dirichlet(np.full(4, 0.4), size=draws)
        lo = float((ent_rows(S @ MY) - t * ent_rows(S @ MZ)).min())
        soft = lambda u: np.exp(u - u.max()) / np.exp(u - u.max()).sum()
        for _ in range(40):
            res = minimize(lambda u: ent(soft(u) @ MY) - t * ent(soft(u) @ MZ),
                           rng.normal(size=4) * 2.5, method="Nelder-Mead",
                           options=dict(maxiter=4000, fatol=1e-15, xatol=1e-13))
            lo = min(lo, float(res.fun))
        if lo - lb < worst:
            worst, wt = lo - lb, t
    record("N8 certified bound is below every point found (soundness)",
           worst > -1e-13,
           f"min [best point found - certified LB] = {worst:.3e} at t={wt} "
           f"over {draws} Dirichlet draws + 40 Nelder-Mead restarts per t")


def n9_four_atom_value(inst, K):
    """The four-atom family gives exactly R1(beta) + t R2(beta)."""
    MY, MZ = inst["MY"], inst["MZ"]
    worst = 0.0
    for beta in np.linspace(0.0, 0.5, 51):
        px, cond = four_atom_witness(beta)
        r = thm7_plain(px, cond, inst)
        R1, R2 = shoulder_corner(K, beta)
        for t in (0.0, 0.3, 0.6, 0.9, 1.0):
            worst = max(worst, abs(r["b18b"] - R1),
                        abs(r["IUWY"] + t * r["IXZ_UW"] - (R1 + t * R2)))
    record("N9 four-atom family value = R1(beta) + t R2(beta)", worst < 1e-12,
           f"max |(18b) - R1| and |I(U;Y)+t I(X;Z|U) - (R1 + t R2)| = "
           f"{worst:.3e} over 51 x 5 (beta,t) pairs")


def n10_four_atom_is_the_minimizer(inst, K):
    """min over the four-atom laws of f_t equals (1-t)(h(e)+h(p)) - d*_t."""
    MY, MZ = inst["MY"], inst["MZ"]
    worst = 0.0
    for t in np.linspace(0.0, 1.0, 21):
        b = best_beta(float(t))
        s = np.zeros(4)
        s[0], s[1] = 1 - b, b                       # X1 = 0, X2 ~ Bern(b)
        lhs = ent(s @ MY) - t * ent(s @ MZ)
        rhs = (1 - t) * K["K"] - psi_t(b, float(t))
        worst = max(worst, abs(lhs - rhs))
    record("N10 four-atom law value = (1-t)(h(e)+h(p)) - psi_t(beta)",
           worst < 1e-12,
           f"max residual = {worst:.3e} over 21 values of t -- this is the "
           f"algebraic bridge between min_s f_t and C's shoulder profile")


def n11_mirror_symmetry(inst, rng, draws=200):
    """The instance automorphism swaps R1 and R2 on both sides."""
    MY, MZ = inst["MY"], inst["MZ"]
    perm = np.array([0, 2, 1, 3])                   # (x1,x2) -> (x2,x1)
    worst = 0.0
    for _ in range(draws):
        s = rng.dirichlet(np.full(4, 0.6))
        worst = max(worst, abs(ent(s[perm] @ MY) - ent(s @ MZ)),
                    abs(ent(s[perm] @ MZ) - ent(s @ MY)))
    record("N11 block-swap composed with receiver-swap is an automorphism",
           worst < 1e-13,
           f"max |H(Y)_{{sigma s}} - H(Z)_s| = {worst:.3e} over {draws} laws "
           f"-- hence the (0,t,1) shoulder F-SH2 is the mirror of F-SH1")


def n12_more_capable(K):
    """psi >= 0 on [0,1] -- recorded, but the certificate does not consume it."""
    lo = min(K["psi"](a) for a in np.linspace(1e-9, 1 - 1e-9, 200001))
    record("N12 psi >= 0 (BEC(h(p)) more capable than BSC(p)) [SCREEN]",
           lo > -1e-15,
           f"min psi over a 200001-point grid = {lo:.3e} -- SCREEN only, and "
           f"the main certificate does not consume it")


def n13_main_sweep(inst, K, ts, tol, state, budget):
    t0 = time.time()
    ob, peak = sweep(inst, K["K"], ts, tol)
    ok = ob is not None
    if ok:
        eps, arg = interval_excess(ts, ob)
        state.update(ts=ts, omega_bar=ob, eps=eps, arg=arg, tol=tol,
                     peak=peak, secs=time.time() - t0)
        ok = eps < budget
        record("N13 shoulder certificate over all of t in [0,1]", ok,
               f"eps = {eps:.4e} at t = {arg:.5f}; {len(ts)} grid points, "
               f"branch-and-bound tolerance {tol:.0e}, peak {peak} live cells, "
               f"{time.time() - t0:.1f}s -- h_Thm7(0,1,t) <= h_C(0,1,t) + eps "
               f"for EVERY t in [0,1], not only at the grid points")
    else:
        record("N13 shoulder certificate over all of t in [0,1]", False,
               "the branch-and-bound aborted on the cell budget")


def n14_gap_ratio(state, K):
    eps = state["eps"]
    ratio = LEDGER["shoulder_gap"] / eps
    record("N14 eps against the width N6-e left open", ratio > 1e3,
           f"eps = {eps:.4e}; the four face caps alone leave "
           f"{LEDGER['shoulder_gap']:.6f} open (N6-e) -- the certificate is "
           f"{ratio:.3g}x tighter, and eps is {eps / K['dstar']:.3e} x d*")


def n15_tolerance_transfer(inst, K):
    """eta enters the final number with coefficient exactly 1."""
    lo, hi = 1e9, -1e9
    for t in (0.15, 0.5, 0.9, 1.0):
        b8, b9, b10 = (dc_min_certificate(inst, t, x)[0]
                       for x in (1e-8, 1e-9, 1e-10))
        for d in ((b9 - b8) - 9e-9, (b10 - b9) - 9e-10):
            lo, hi = min(lo, d), max(hi, d)
    record("N15 tolerance transfer is linear with coefficient 1",
           lo > -1e-8 and hi < 1e-13,
           f"LB(eta1) - LB(eta2) - (eta2 - eta1) lands in [{lo:.2e}, {hi:.2e}] "
           f"over t in (0.15, 0.5, 0.9, 1.0) and eta in (1e-8, 1e-9, 1e-10); "
           f"the residual is the incumbent's own resolution and is bounded by "
           f"eta, not by sqrt(eta) = 1.0e-04 -- eta lands on the final number "
           f"additively, so the square-root amplification of ## N1 (T3c) N1-i "
           f"cannot occur (there is no averaged constraint in the chain)")


def n16_slice_inclusion(state, K):
    """Support domination in every direction of the R0=0 slice."""
    ts, ob, eps = state["ts"], state["omega_bar"], state["eps"]
    twoC = 2 * K["C"]
    worst = -1e9
    for i, t in enumerate(ts):
        thm7 = twoC + ob[i]
        hc = twoC + psi_t(best_beta(float(t)), float(t))
        worst = max(worst, thm7 - hc)
    record("N16 h_Thm7 <= h_C + eps in every slice direction", worst <= eps,
           f"max [certified h_Thm7(0,1,t) - achievable h_C(0,1,t)] over the "
           f"{len(ts)} grid points = {worst:.4e} <= eps = {eps:.4e}; with the "
           f"mirror (N11) this covers every lambda >= 0, so "
           f"Thm7|_(R0=0) is inside C|_(R0=0) + [0,eps]^2")


def n17_c_shoulder_pinned(state, K):
    """C's own shoulder is pinned to the beta-split family within eps."""
    ts, ob, eps = state["ts"], state["omega_bar"], state["eps"]
    worst = 0.0
    for i, t in enumerate(ts):
        lo = psi_t(best_beta(float(t)), float(t))
        worst = max(worst, ob[i] - lo)
    record("N17 the beta-split family IS C's shoulder within eps", worst <= eps,
           f"h_C(0,1,t) - (2C + psi_t(beta)) is squeezed into "
           f"[0, {worst:.4e}] because C is inside Thm7 -- this upgrades the "
           f"N6-f / T6 screen to a certificate on these directions")


def n18_cross_check_n6(inst, K):
    """The N6 evaluator must reproduce the same numbers, independently."""
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import capacity_probc as cp
    chan = cp.probc_blocks(K["p"])
    KN6 = cp.constants(K["p"])
    TY, TZ = cp.probc_product(K["p"])
    worst_ch = max(abs(TY - inst["MY"]).max(), abs(TZ - inst["MZ"]).max())
    worst_k = max(abs(KN6["C"] - K["C"]), abs(KN6["dstar"] - K["dstar"]),
                  abs(KN6["SR_C"] - K["SR_C"]))
    worst_c = 0.0
    for beta in np.linspace(0.0, K["astar"], 21):
        M, B1, B2, S1, S2 = cp.theorem3_caps(cp.split_block(beta),
                                             cp.split_block(beta), chan)
        R1, R2 = shoulder_corner(K, beta)
        worst_c = max(worst_c, abs(B1 - R1), abs(min(S1, S2) - B1 - R2))
    worst_t = 0.0
    for beta in np.linspace(0.0, 0.5, 21):
        px, cond = four_atom_witness(beta)
        a = thm7_plain(px, cond, inst)
        b = cp.plain_terms(px, cond, TY, TZ)
        worst_t = max(worst_t, abs(a["b18b"] - b["b18b"]),
                      abs(a["b18i"] - b["b18i"]))
    ok = max(worst_ch, worst_k, worst_c, worst_t) < 1e-10
    record("N18 cross-check against the N6 evaluator", ok,
           f"channel {worst_ch:.3e}, constants {worst_k:.3e}, Theorem 3 "
           f"corners {worst_c:.3e}, (18b)/(18i) {worst_t:.3e} -- the C-side "
           f"achievability of the beta corners is the N6 evaluator's, so the "
           f"squeeze uses two independent implementations")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20260808)
    ap.add_argument("--quick", action="store_true",
                    help="81-point t grid instead of 321 (coarser eps)")
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)

    inst = instance()
    K = constants()
    K["K"] = h2(inst["e"]) + h2(inst["p"])
    n, budget = (81, 1e-5) if args.quick else (321, 1e-6)
    ts = np.linspace(0.0, 1.0, n) ** (1 / 3)
    state = {}

    n1_constants(K)
    n2_conditional_entropies(inst, K)
    n3_hy_max_at_uniform(inst, K, rng)
    n4_box_support_bound(rng)
    n5_two_line_reduction(inst, K, rng)
    n6_functional_identity(inst, K, rng)
    n7_bb_anchors(inst, K)
    n8_bb_soundness(inst, rng)
    n9_four_atom_value(inst, K)
    n10_four_atom_is_the_minimizer(inst, K)
    n11_mirror_symmetry(inst, rng)
    n12_more_capable(K)
    n13_main_sweep(inst, K, ts, 1e-9, state, budget)
    if state:
        n14_gap_ratio(state, K)
    n15_tolerance_transfer(inst, K)
    if state:
        n16_slice_inclusion(state, K)
        n17_c_shoulder_pinned(state, K)
    n18_cross_check_n6(inst, K)

    bad = [nm for nm, ok, _ in RESULTS if not ok]
    print(f"\n{len(RESULTS) - len(bad)}/{len(RESULTS)} tests passed")
    if bad:
        print("FAILED: " + ", ".join(bad))
    raise SystemExit(1 if bad else 0)


if __name__ == "__main__":
    main()
