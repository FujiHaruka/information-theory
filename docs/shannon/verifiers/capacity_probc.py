#!/usr/bin/env python3
"""Closed-form evaluator for C (the capacity region) of the [probc] instance,
plus the boundary inventory screens of leg N6.

C side -- [probc] Theorem 3 (probc.txt:557-574 of the `pdftotext -layout` output;
retrieval = docs/shannon/lit-fetch.sh), the capacity region of a product of
*reversely more-capable* broadcast channels.  The paper states it for
"receiver Z1 more capable than Y1, receiver Y2 more capable than Z2".  Our
[probc] Lemma 8 instance has the *opposite* orientation in both blocks
(BEC(h(p)) is more capable than BSC(p)), so Theorem 3 is applied after the
receiver swap Y <-> Z, which also swaps R1 <-> R2.  The mirrored region uses
the auxiliaries V1 (block 1, receiver Z) and U2 (block 2, receiver Y), which is
exactly the distribution `p1(w1,v1,x1) p2(w2,u2,x2)` printed under the theorem
(the region *expressions* as printed carry U1 / V2 -- one of the two is a
typo in the source; the mirrored reading is the self-consistent one and it is
the one that reproduces every calibration value of `## M6 (T3b)`).

Thm7 side -- the J-free / eligibility-free subset of Theorem 7 of [auxrec]
(auxrec.txt:1037-1082): (18a), (18b), (18e), (18i) plus (20c).  These four are
the only bounds of the bundle that carry no J, so they hold for *every*
eligible witness without consuming (19)/(20a)/(20b).

Instance:  X = (X1,X2) in {0,1}^2,  X1 -> Y1 = BEC(e), X1 -> Z1 = BSC(p),
           X2 -> Y2 = BSC(p), X2 -> Z2 = BEC(e),  p = 0.1, e = h(p).

Run:  python3 docs/shannon/verifiers/capacity_probc.py [--seed N] [--draws N]
Exit code 0 iff every test passes.
"""
import argparse
import itertools

import numpy as np
from scipy.optimize import brentq

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


def bec_matrix(e):
    return np.array([[1 - e, 0.0, e], [0.0, 1 - e, e]])


def bsc_matrix(p):
    return np.array([[1 - p, p], [p, 1 - p]])


def mi(Pxy):
    """I(A;B) from a joint matrix."""
    return ent(Pxy.sum(0)) + ent(Pxy.sum(1)) - ent(Pxy)


# ------------------------------------------------------- per-block quantities


def block_terms(P, TY, TZ):
    """Mutual informations of one [probc] block.

    P[w, a, x] is a joint law of (W, A, X) with A the block's auxiliary;
    TY[x, y] / TZ[x, z] are the two component channels.  Returns every term
    Theorem 3 needs from a single block.
    """
    P = np.asarray(P, dtype=float)
    P = P / P.sum()
    nw, na, nx = P.shape

    def joint(T):
        return P[:, :, :, None] * T[None, None, :, :]        # (w, a, x, b)

    out = {}
    for tag, T in (("Y", TY), ("Z", TZ)):
        J = joint(T)
        Hb = ent(J.sum(axis=(0, 1, 2)))
        Hwb = ent(J.sum(axis=(1, 2)))
        Hw = ent(P.sum(axis=(1, 2)))
        Hawb = ent(J.sum(axis=2))
        Haw = ent(P.sum(axis=2))
        Hxawb = ent(J)
        Hxaw = ent(P)
        Hxwb = ent(J.sum(axis=1))
        Hxw = ent(P.sum(axis=1))
        out["IW" + tag] = Hw + Hb - Hwb                       # I(W;B)
        out["IA" + tag + "_W"] = Haw + Hwb - Hawb - Hw        # I(A;B|W)
        out["IX" + tag + "_W"] = Hxw + Hwb - Hxwb - Hw        # I(X;B|W)
        out["IX" + tag + "_AW"] = Hxaw + Hawb - Hxawb - Haw   # I(X;B|A,W)
    return out


def theorem3_caps(P1, P2, chan):
    """The five caps of [probc] Theorem 3, mirrored to our orientation.

    P1[w1, v1, x1] and P2[w2, u2, x2].  Returns (M, B1, B2, S1, S2) standing for
    R0 <= M, R0+R1 <= B1, R0+R2 <= B2, R0+R1+R2 <= min(S1, S2).
    """
    b1 = block_terms(P1, chan["TY1"], chan["TZ1"])
    b2 = block_terms(P2, chan["TY2"], chan["TZ2"])
    M = min(b1["IWY"] + b2["IWY"], b1["IWZ"] + b2["IWZ"])
    B1 = M + b1["IXY_W"] + b2["IAY_W"]
    B2 = M + b1["IAZ_W"] + b2["IXZ_W"]
    S1 = M + b2["IXZ_W"] + min(b1["IAZ_W"] + b1["IXY_AW"], b1["IXY_W"])
    S2 = M + min(b2["IXZ_W"], b2["IAY_W"] + b2["IXZ_AW"]) + b1["IXY_W"]
    return M, B1, B2, S1, S2


def support_of_box(caps, lam):
    """max <lam, R> over {R >= 0 : R0 <= M, R0+R1 <= B1, R0+R2 <= B2, sum <= S}."""
    M, B1, B2, S1, S2 = caps
    S = min(S1, S2)
    best = 0.0
    # the vertices of a comprehensive box of this shape
    for r0 in (0.0, min(M, B1, B2, S)):
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


# ------------------------------------------------------------- the instance


def probc_blocks(p=0.1):
    e = h2(p)
    bec, bsc = bec_matrix(e), bsc_matrix(p)
    return {"TY1": bec, "TZ1": bsc, "TY2": bsc, "TZ2": bec, "p": p, "e": e}


def probc_product(p=0.1):
    """The 4-input product channel used by kappa2_probc.py, same convention."""
    e = h2(p)
    bec, bsc = bec_matrix(e), bsc_matrix(p)
    TY = np.zeros((4, 6))
    TZ = np.zeros((4, 6))
    for x1, x2 in itertools.product(range(2), repeat=2):
        x = 2 * x1 + x2
        TY[x] = np.kron(bec[x1], bsc[x2])
        TZ[x] = np.kron(bsc[x1], bec[x2])
    return TY, TZ


def constants(p=0.1):
    """C, alpha*, d*, SR_C, the ceiling C + S(mu*) and the sum-face segment."""
    e = h2(p)
    C = 1.0 - e

    def psi(a):                       # I(X;Y1)_a - I(X;Z1)_a on one block
        return C * h2(a) - (h2(a * (1 - p) + (1 - a) * p) - h2(p))

    dpsi = lambda a: (psi(a + 1e-7) - psi(a - 1e-7)) / 2e-7
    astar = brentq(dpsi, 1e-4, 0.5 - 1e-4, xtol=1e-15, rtol=8.9e-16)
    dstar = psi(astar)
    return {
        "p": p, "e": e, "C": C, "psi": psi, "astar": astar, "dstar": dstar,
        "SR_C": 2 * C + dstar,
        "ceiling": C + 1.0 - h2(astar * (1 - p) + (1 - astar) * p),
        "seg_lo": C * h2(astar),
        "astar_p": astar * (1 - p) + (1 - astar) * p,
        "S_mustar": 1.0 - h2(astar * (1 - p) + (1 - astar) * p),
    }


def split_block(beta, aux_const=True, nx=2):
    """W = beta-split of a uniform X (W in {0,1}), auxiliary = constant."""
    P = np.zeros((2, 1, nx))
    P[0, 0, 0] = 0.5 * (1 - beta)
    P[0, 0, 1] = 0.5 * beta
    P[1, 0, 0] = 0.5 * beta
    P[1, 0, 1] = 0.5 * (1 - beta)
    return P


# ------------------------------------------- Thm7: the J-free / free subset


def plain_terms(px, K, TY, TZ):
    """(18a),(18b),(18e),(18i), (20c) and the g-triple from a plain system.

    K[x, u, v, w] is p(u,v,w|x); px is p(x).
    """
    px = np.asarray(px, dtype=float)
    px = px / px.sum()
    K = np.asarray(K, dtype=float)
    K = K / K.sum(axis=(1, 2, 3), keepdims=True)
    P = px[:, None, None, None] * K                           # (x,u,v,w)

    def with_out(T):
        return P[:, :, :, :, None] * T[:, None, None, None, :]  # (x,u,v,w,b)

    res = {}
    for tag, T in (("Y", TY), ("Z", TZ)):
        J = with_out(T)
        H = lambda ax: ent(J.sum(axis=ax))
        Hb = H((0, 1, 2, 3))
        Hw, Hwb = ent(P.sum(axis=(0, 1, 2))), H((0, 1, 2))
        Huw, Huwb = ent(P.sum(axis=(0, 2))), H((0, 2))
        Hvw, Hvwb = ent(P.sum(axis=(0, 1))), H((0, 1))
        Hxuw, Hxuwb = ent(P.sum(axis=2)), H((2,))
        Hxvw, Hxvwb = ent(P.sum(axis=1)), H((1,))
        Hx = ent(px)
        res["IW" + tag] = Hw + Hb - Hwb
        res["IUW" + tag] = Huw + Hb - Huwb
        res["IVW" + tag] = Hvw + Hb - Hvwb
        res["IU" + tag + "_W"] = Huw + Hwb - Huwb - Hw
        res["IV" + tag + "_W"] = Hvw + Hwb - Hvwb - Hw
        res["IX" + tag + "_UW"] = Hxuw + Huwb - Hxuwb - Huw
        res["IX" + tag + "_VW"] = Hxvw + Hvwb - Hxvwb - Hvw
        res["IX" + tag] = Hx + Hb - ent(J.sum(axis=(1, 2, 3)))
    mWYZ = min(res["IWY"], res["IWZ"])
    res["b18a"] = mWYZ
    res["b18b"] = mWYZ + res["IUY_W"]
    res["b18e"] = mWYZ + res["IVZ_W"]
    res["br1"] = mWYZ + res["IVZ_W"] + res["IXY_VW"]
    res["br2"] = mWYZ + res["IUY_W"] + res["IXZ_UW"]
    res["b18i"] = min(res["br1"], res["br2"])
    res["r20c"] = res["br1"] - res["br2"]
    res["Ca"] = res["IWZ"] - res["IWY"]
    res["Cb"] = (res["IUWZ"] - res["IUWY"]) - res["Ca"]
    res["Cc"] = (res["IVWZ"] - res["IVWY"]) - res["Ca"]
    return res


def rand_plain(rng, nx, dims, conc=0.6):
    return rng.dirichlet(conc * np.ones(int(np.prod(dims))), size=nx).reshape(
        (nx,) + tuple(dims))


def rand_channel(rng, nx, nb, conc=0.7):
    return rng.dirichlet(conc * np.ones(nb), size=nx)


# ------------------------------------------------------------------- tests

RESULTS = []


def record(name, ok, detail):
    RESULTS.append((name, ok, detail))
    print(f"[{'ok ' if ok else 'FAIL'}] {name}: {detail}")


FACTS = {                       # values quoted by bc-facts.md ## N1 (T3c)
    "C": 0.5310044064, "astar": 0.0776696702, "dstar": 0.0387713705,
    "SR_C": 1.1007801833, "ceiling": 0.8916098871, "seg_lo": 0.2091702962,
    "astar_p": 0.1621357361, "S_mustar": 0.3606054807,
}


def t1_constants(K):
    """Calibration against the constants the ledger carries (## N1 (T3c))."""
    worst, where = 0.0, ""
    for k, v in FACTS.items():
        d = abs(K[k] - v)
        if d > worst:
            worst, where = d, k
    record("T1 instance constants vs bc-facts",
           worst < 5e-10,
           f"max |ours - facts| = {worst:.3e} at {where}; "
           f"C={K['C']:.10f} a*={K['astar']:.10f} d*={K['dstar']:.10f} "
           f"SR_C={K['SR_C']:.10f} ceiling={K['ceiling']:.10f}")


def t2_more_capable(K, chan):
    """Y1 = BEC(h(p)) is more capable than Z1 = BSC(p) (and the mirror)."""
    lo = min(K["psi"](a) for a in np.linspace(1e-6, 1 - 1e-6, 20001))
    record("T2 more-capable orientation (psi >= 0)", lo > -1e-12,
           f"min_a [I(X;Y1)-I(X;Z1)] = {lo:.3e} over 20001 points (screen); "
           f"max = d* = {K['dstar']:.10f} -- so the paper's hypothesis holds "
           f"after the receiver swap, not before")


def t3_m6_witness(K, chan):
    """The alpha*-split witness reproduces the five caps of ## M6 (T3b) M6-a.

    M6 evaluated them at alpha* rounded to six digits; N1-g corrected the two
    values that do not stay stationary under that rounding, so the comparison
    is run at both precisions.
    """
    M, B1, B2, S1, S2 = theorem3_caps(split_block(K["astar"]),
                                      split_block(K["astar"]), chan)
    p, C = K["p"], K["C"]
    a = K["astar"]
    M_cf = C * (1 - h2(a)) + 1.0 - h2(a * (1 - p) + (1 - a) * p)
    exact = max(abs(M - M_cf), abs(B1 - K["ceiling"]), abs(B2 - K["ceiling"]),
                abs(S1 - K["SR_C"]), abs(S2 - K["SR_C"]))
    Mr = theorem3_caps(split_block(0.077670), split_block(0.077670), chan)[0]
    rounded = abs(Mr - 0.68243834)
    record("T3 M6-a witness caps", exact < 1e-12 and rounded < 5e-9,
           f"(M,B1,B2,S1,S2) = ({M:.10f}, {B1:.10f}, {B2:.10f}, {S1:.10f}, "
           f"{S2:.10f}); dev from the closed forms = {exact:.3e}; M6's printed "
           f"0.68243834 is reproduced at alpha* = 0.077670 to {rounded:.3e} "
           f"(the un-rounded M is {M - 0.68243834:+.3e} away -- same rounding "
           f"artefact N1-g found in the ceiling)")


def t4_mirror(K, chan, rng, draws=60):
    """Block swap composed with receiver swap is an automorphism of the
    instance that exchanges the two receivers, so it acts on witnesses by
    (P1, P2) -> (P2, P1) and on the caps by B1 <-> B2, S1 <-> S2."""
    worst = 0.0
    for _ in range(draws):
        P1 = rng.dirichlet(0.7 * np.ones(2 * 2 * 2)).reshape(2, 2, 2)
        P2 = rng.dirichlet(0.7 * np.ones(3 * 2 * 2)).reshape(3, 2, 2)
        M, B1, B2, S1, S2 = theorem3_caps(P1, P2, chan)
        Mm, B1m, B2m, S1m, S2m = theorem3_caps(P2, P1, chan)
        worst = max(worst, abs(M - Mm), abs(B1 - B2m), abs(B2 - B1m),
                    abs(S1 - S2m), abs(S2 - S1m))
    record("T4 receiver-swap / block-swap self-mirror", worst < 1e-12,
           f"max |caps - mirrored caps| = {worst:.3e} over {draws} random "
           f"witnesses -- C is R1<->R2 symmetric on this instance")


def shoulder_point(K, beta):
    """Closed form of C's R0=0 Pareto corner at the beta-split witness."""
    p, C = K["p"], K["C"]
    R1 = C + 1.0 - h2(beta * (1 - p) + (1 - beta) * p)
    R2 = C * h2(beta)
    return R1, R2


def t5_shoulder_closed_form(K, chan):
    """(R1,R2) = (C+1-h(beta*p), C h(beta)) is the beta-split corner."""
    worst = 0.0
    for beta in np.linspace(0.0, K["astar"], 61):
        M, B1, B2, S1, S2 = theorem3_caps(split_block(beta), split_block(beta),
                                          chan)
        S = min(S1, S2)
        R1, R2 = shoulder_point(K, beta)
        worst = max(worst, abs(B1 - R1), abs(S - B1 - R2), abs(B1 - B2))
    record("T5 shoulder closed form", worst < 1e-12,
           f"max |evaluator - (C+1-h(beta*p), C h(beta))| = {worst:.3e} over "
           f"61 values of beta in [0, alpha*]")


def h_c_shoulder(K, t, grid=4001):
    """max_beta [ (C+1-h(beta*p)) + t C h(beta) ] -- C's support at (0,1,t)."""
    best, arg = -1e9, 0.0
    for beta in np.linspace(0.0, 0.5, grid):
        R1, R2 = shoulder_point(K, beta)
        v = R1 + t * R2
        if v > best:
            best, arg = v, beta
    return best, arg


def t6_shoulder_is_the_envelope(K, chan, rng, draws=4000):
    """Screen: no random product witness beats the beta-split shoulder."""
    ts = [0.0, 0.2, 0.4, 0.6, 0.8, 0.9, 1.0]
    hc = {t: h_c_shoulder(K, t)[0] for t in ts}
    worst, wt = -1e9, None
    for _ in range(draws):
        nw1, na1 = int(rng.integers(1, 4)), int(rng.integers(1, 4))
        nw2, na2 = int(rng.integers(1, 4)), int(rng.integers(1, 4))
        P1 = rng.dirichlet(0.6 * np.ones(nw1 * na1 * 2)).reshape(nw1, na1, 2)
        P2 = rng.dirichlet(0.6 * np.ones(nw2 * na2 * 2)).reshape(nw2, na2, 2)
        caps = theorem3_caps(P1, P2, chan)
        for t in ts:
            exc = support_of_box(caps, (0.0, 1.0, t)) - hc[t]
            if exc > worst:
                worst, wt = exc, t
    record("T6 shoulder envelope (SCREEN, non-violation is not evidence)",
           worst < 1e-9,
           f"max excess over the beta-split shoulder = {worst:.3e} at t={wt} "
           f"over {draws} random product witnesses")


def t7_n1b_identities(chan_TY, chan_TZ, rng, draws=200, tag="[probc]"):
    """N1-b: the two branches of (18i) are identities in (p, C_a, C_b, C_c)."""
    nx = chan_TY.shape[0]
    worst = 0.0
    for _ in range(draws):
        px = rng.dirichlet(0.7 * np.ones(nx))
        dims = (int(rng.integers(1, 4)), int(rng.integers(1, 4)),
                int(rng.integers(1, 4)))
        K = rand_plain(rng, nx, dims)
        r = plain_terms(px, K, chan_TY, chan_TZ)
        e1 = r["br1"] - (r["IXY"] + r["Cc"] + min(r["Ca"], 0.0))
        e2 = r["br2"] - (r["IXZ"] - r["Cb"] - max(r["Ca"], 0.0))
        worst = max(worst, abs(e1), abs(e2))
    return worst


def t7(chan, rng, draws):
    TY, TZ = probc_product(chan["p"])
    w = t7_n1b_identities(TY, TZ, rng, draws)
    record("T7 N1-b branch identities on [probc]", w < 1e-12,
           f"max |branch - closed form| = {w:.3e} over {draws} witnesses with "
           f"correlated (U,V,W)|X, no (19)/(20) imposed")


def t8_channel_generic(rng, draws=120):
    """3.0 refutation: the N1-b identities never mention C -- they are generic."""
    worst, shapes = 0.0, []
    for _ in range(draws // 3):
        nx = int(rng.integers(2, 5))
        ny = int(rng.integers(2, 5))
        nz = int(rng.integers(2, 5))
        TY, TZ = rand_channel(rng, nx, ny), rand_channel(rng, nx, nz)
        w = t7_n1b_identities(TY, TZ, rng, 3, tag="random")
        if w > worst:
            worst, shapes = w, [nx, ny, nz]
    record("T8 N1-b is channel-generic (3.0 refutation)", worst < 1e-12,
           f"max residual = {worst:.3e} over {draws} witnesses on "
           f"{draws // 3} random broadcast channels (worst shape "
           f"|X|,|Y|,|Z| = {shapes}) -- no value of C is referenced")


def t9_18b_18e(chan, rng, draws=200):
    """(18b) = I(U,W;Y) + min(C_a,0) and (18e) = I(V,W;Z) - max(C_a,0)."""
    TY, TZ = probc_product(chan["p"])
    worst = 0.0
    for _ in range(draws):
        px = rng.dirichlet(0.7 * np.ones(4))
        K = rand_plain(rng, 4, (int(rng.integers(1, 4)),
                                int(rng.integers(1, 4)),
                                int(rng.integers(1, 4))))
        r = plain_terms(px, K, TY, TZ)
        worst = max(worst,
                    abs(r["b18b"] - (r["IUWY"] + min(r["Ca"], 0.0))),
                    abs(r["b18e"] - (r["IVWZ"] - max(r["Ca"], 0.0))))
    record("T9 (18b)/(18e) closed forms", worst < 1e-12,
           f"max residual = {worst:.3e} over {draws} witnesses")


def t10_free_face_caps(K, chan, rng, draws=400):
    """Screen for the three free face bounds: (18a),(18b),(18e) <= 2C,
    and (18i) <= min{I(X;Y),I(X;Z)} + d* <= SR_C."""
    TY, TZ = probc_product(chan["p"])
    twoC = 2 * K["C"]
    worst_face, worst_sum = -1e9, -1e9
    for _ in range(draws):
        px = rng.dirichlet(0.7 * np.ones(4))
        K3 = rand_plain(rng, 4, (int(rng.integers(1, 4)),
                                 int(rng.integers(1, 4)),
                                 int(rng.integers(1, 4))))
        r = plain_terms(px, K3, TY, TZ)
        worst_face = max(worst_face, r["b18a"] - twoC, r["b18b"] - twoC,
                         r["b18e"] - twoC)
        worst_sum = max(worst_sum,
                        r["b18i"] - (min(r["IXY"], r["IXZ"]) + K["dstar"]))
    record("T10 free face caps (SCREEN of the identity chain)",
           worst_face < 1e-12 and worst_sum < 1e-12,
           f"max[(18a),(18b),(18e)] - 2C = {worst_face:.3e}; "
           f"max (18i) - (min{{I(X;Y),I(X;Z)}} + d*) = {worst_sum:.3e} "
           f"over {draws} witnesses")


def t11_w_const_wlog(chan, rng, draws=200):
    """Replacing (U,V,W) by ((U,W),(V,W),const) never lowers (18b) or (18i)."""
    TY, TZ = probc_product(chan["p"])
    worst = 1e9
    for _ in range(draws):
        px = rng.dirichlet(0.7 * np.ones(4))
        nu, nv, nw = (int(rng.integers(1, 3)), int(rng.integers(1, 3)),
                      int(rng.integers(1, 4)))
        Kk = rand_plain(rng, 4, (nu, nv, nw))
        r = plain_terms(px, Kk, TY, TZ)
        # merge W into both U and V, then set W = const
        Km = Kk.reshape(4, nu, nv, nw)
        big = np.zeros((4, nu * nw, nv * nw, 1))
        for u in range(nu):
            for v in range(nv):
                for w in range(nw):
                    big[:, u * nw + w, v * nw + w, 0] += Km[:, u, v, w]
        r2 = plain_terms(px, big, TY, TZ)
        worst = min(worst, r2["b18b"] - r["b18b"], r2["b18i"] - r["b18i"])
    record("T11 W = const is WLOG for the (0,1,t) directions", worst > -1e-12,
           f"min[(18b),(18i) gain after merging W] = {worst:.3e} over {draws} "
           f"witnesses -- both bounds are monotone under the merge")


def free_witness(beta):
    """The explicit free Thm7 witness matching C's beta-split shoulder point.

    p = uniform, W = const; U has four atoms (X1 = c in {0,1}) x
    (X2 ~ Bern(beta) or Bern(1-beta)); V is the mirror image.  Returns
    (px, K) with K[x, u, v, w] = p(u,v,w|x), U and V conditionally
    independent given X.
    """
    px = np.full(4, 0.25)
    # p(u | x): u = 2*c + s, atom (c, s) puts X1 = c, X2 ~ Bern(beta^(s))
    pu_x = np.zeros((4, 4))
    pv_x = np.zeros((4, 4))
    for x in range(4):
        x1, x2 = x // 2, x % 2
        for c in range(2):
            for s in range(2):
                b = beta if s == 0 else 1 - beta
                pu_x[x, 2 * c + s] = (1.0 if c == x1 else 0.0) * \
                    (b if x2 == 1 else 1 - b)
                pv_x[x, 2 * c + s] = (1.0 if c == x2 else 0.0) * \
                    (b if x1 == 1 else 1 - b)
    pu_x /= pu_x.sum(axis=1, keepdims=True)
    pv_x /= pv_x.sum(axis=1, keepdims=True)
    K = (pu_x[:, :, None] * pv_x[:, None, :])[:, :, :, None]
    return px, K


def t12_free_support_matches_C(K, chan):
    """The explicit free witness reproduces C's shoulder point exactly."""
    TY, TZ = probc_product(chan["p"])
    worst_pt, worst_sup, wb = 0.0, 0.0, None
    for beta in np.linspace(0.0, K["astar"], 41):
        px, Kk = free_witness(beta)
        r = plain_terms(px, Kk, TY, TZ)
        R1, R2 = shoulder_point(K, beta)
        d = max(abs(r["b18b"] - R1), abs(r["b18i"] - (R1 + R2)),
                abs(r["r20c"]))
        if d > worst_pt:
            worst_pt, wb = d, beta
        caps = (r["b18a"], r["b18b"], r["b18e"], r["b18i"], r["b18i"])
        for t in (0.0, 0.3, 0.6, 0.9, 1.0):
            worst_sup = max(worst_sup, abs(support_of_box(caps, (0, 1, t))
                                           - (R1 + t * R2)))
    record("T12 explicit free witness reproduces C's shoulder",
           worst_pt < 1e-12 and worst_sup < 1e-12,
           f"max |(18b) - R1(beta)| and |(18i) - S(beta)| and |(20c)| = "
           f"{worst_pt:.3e} (worst beta = {wb:.5f}); max |box support - "
           f"(R1 + t R2)| = {worst_sup:.3e} over 41 x 5 (beta, t) pairs")


def t13_endpoints(K, chan):
    TY, TZ = probc_product(chan["p"])
    r0 = plain_terms(*free_witness(0.0), TY, TZ)
    r1 = plain_terms(*free_witness(K["astar"]), TY, TZ)
    ok = (abs(r0["b18i"] - 2 * K["C"]) < 1e-9
          and abs(r1["b18i"] - K["SR_C"]) < 1e-9
          and abs(r1["b18b"] - K["ceiling"]) < 1e-9)
    record("T13 free-witness endpoints", ok,
           f"beta=0 -> (18i) = {r0['b18i']:.10f} (2C = {2 * K['C']:.10f}); "
           f"beta=alpha* -> (18i) = {r1['b18i']:.10f} (SR_C = "
           f"{K['SR_C']:.10f}), (18b) = {r1['b18b']:.10f} (ceiling = "
           f"{K['ceiling']:.10f})")


def t14_free_screen(K, chan, rng, draws=6000):
    """Screen: no random free witness exceeds C's shoulder in (0,1,t)."""
    TY, TZ = probc_product(chan["p"])
    ts = [0.2, 0.5, 0.8, 0.9, 0.95, 1.0]
    hc = {t: h_c_shoulder(K, t)[0] for t in ts}
    worst, wt = -1e9, None
    for _ in range(draws):
        px = rng.dirichlet(0.7 * np.ones(4)) if rng.random() < 0.5 \
            else np.full(4, 0.25)
        Kk = rand_plain(rng, 4, (int(rng.integers(1, 5)),
                                 int(rng.integers(1, 5)),
                                 int(rng.integers(1, 3))))
        r = plain_terms(px, Kk, TY, TZ)
        caps = (r["b18a"], r["b18b"], r["b18e"], r["b18i"], r["b18i"])
        for t in ts:
            exc = support_of_box(caps, (0.0, 1.0, t)) - hc[t]
            if exc > worst:
                worst, wt = exc, t
    record("T14 free witnesses vs C's shoulder (SCREEN, not evidence)",
           worst < 1e-9,
           f"max excess = {worst:.3e} at t={wt} over {draws} random free "
           f"witnesses (no (19)/(20a)/(20b) imposed)")


def t15_face_maxima(K, chan, rng, draws=3000):
    """Screen: max R0 = max(R0+R1) = max(R0+R2) = 2C and max sum = SR_C on C."""
    twoC, best = 2 * K["C"], [0.0, 0.0, 0.0, 0.0]
    for _ in range(draws):
        P1 = rng.dirichlet(0.6 * np.ones(3 * 3 * 2)).reshape(3, 3, 2)
        P2 = rng.dirichlet(0.6 * np.ones(3 * 3 * 2)).reshape(3, 3, 2)
        M, B1, B2, S1, S2 = theorem3_caps(P1, P2, chan)
        best = [max(best[0], M), max(best[1], B1), max(best[2], B2),
                max(best[3], min(S1, S2))]
    # attaining witnesses: W = X (both blocks) for R0, beta = 0 for R0+R1
    Px = np.zeros((2, 1, 2))
    Px[0, 0, 0] = Px[1, 0, 1] = 0.5
    Mx = theorem3_caps(Px, Px, chan)[0]
    ok = (max(best[:3]) < twoC + 1e-9 and best[3] < K["SR_C"] + 1e-9
          and abs(Mx - twoC) < 1e-12)
    record("T15 face maxima (SCREEN + attaining witness)", ok,
           f"random max (M, B1, B2, sum) = ({best[0]:.8f}, {best[1]:.8f}, "
           f"{best[2]:.8f}, {best[3]:.8f}); 2C = {twoC:.8f}, "
           f"SR_C = {K['SR_C']:.8f}; W=X gives M = {Mx:.10f}")


def t16_shoulder_gap_vs_box(K):
    """How much of the shoulder the four face caps alone leave open."""
    twoC = 2 * K["C"]
    worst, wt = 0.0, None
    for t in np.linspace(0.0, 1.0, 201):
        box = (1 - t) * twoC + t * K["SR_C"]     # the four caps, taken jointly
        hc, _ = h_c_shoulder(K, t)
        if box - hc > worst:
            worst, wt = box - hc, t
    record("T16 the four face caps do NOT close the shoulder", worst > 1e-3,
           f"max [box bound - h_C] = {worst:.6f} (= {worst / K['dstar']:.3f} "
           f"x d*) at t = {wt:.3f} -- the shoulder is a genuinely separate face")


def t17_envelope_column_generation(K, chan, rng, ts=(0.3, 0.6, 0.9), restarts=30):
    """SCREEN of the single question N7 has to certify.

    The free Thm7 support at (0,1,t) is
        max_p [ H(Y)_p - t H(Z|X) - conv(H(Y) - t H(Z))(p) ],
    and at p = uniform the four-atom family of free_witness() attains
    C's shoulder value.  Column generation looks for an atom that pushes the
    convex envelope strictly below that family; a negative reduced cost would
    mean the free relaxation overshoots C.
    """
    from scipy.optimize import linprog, minimize
    TY, TZ = probc_product(chan["p"])
    p, C, e = chan["p"], K["C"], K["e"]
    unif = np.full(4, 0.25)
    f = lambda s, t: ent(s @ TY) - t * ent(s @ TZ)

    def simplex(u):
        z = np.exp(u - u.max())
        return z / z.sum()

    worst_slack, worst_gap, wt = 1e9, 0.0, None
    for t in ts:
        pool = []
        for beta in np.linspace(0.0, 0.5, 201):
            for c in (0, 1):
                for flip in (0, 1):
                    s = np.zeros(4)
                    b = beta if flip == 0 else 1 - beta
                    s[2 * c + 0], s[2 * c + 1] = 1 - b, b
                    pool.append(s.copy())
        pool += [np.eye(4)[i] for i in range(4)]
        for _ in range(8):
            P = np.array(pool)
            fv = np.array([f(s, t) for s in P])
            r = linprog(fv, A_eq=np.vstack([P.T, np.ones(len(P))]),
                        b_eq=np.concatenate([unif, [1.0]]), bounds=(0, None),
                        method="highs")
            th, c0 = r.eqlin.marginals[:4], r.eqlin.marginals[4]
            best, barg = 1e9, None
            for _ in range(restarts):
                res = minimize(lambda u: f(simplex(u), t) - th @ simplex(u),
                               rng.normal(size=4) * 2.0, method="Nelder-Mead",
                               options=dict(maxiter=4000, fatol=1e-14,
                                            xatol=1e-12))
                if res.fun < best:
                    best, barg = res.fun, simplex(res.x)
            if best < c0 - 1e-9:
                pool.append(barg)
            else:
                break
        fam = min((h2(e) + h2(b * (1 - p) + (1 - b) * p))
                  - t * (h2(p) + h2(e) + C * h2(b))
                  for b in np.linspace(0.0, 0.5, 20001))
        worst_slack = min(worst_slack, best - c0)
        if fam - r.fun > worst_gap:
            worst_gap, wt = fam - r.fun, t
    record("T17 convex-envelope column generation (SCREEN -- N7's target)",
           worst_gap < 1e-6,
           f"max [four-atom value - LP envelope] = {worst_gap:.3e} at t={wt}; "
           f"min reduced cost of the best generated atom = {worst_slack:.3e} "
           f"over t in {list(ts)} -- no atom beat the family, but a "
           f"non-violating search is not a certificate (plan 4.5)")


def t18_slice_determines_region(K, chan):
    """R in a box => (0, R0+R1, R2) in the same box (identity), and a screen
    that C's R0=0 slice plus R0 <= 2C already recovers C in mixed directions.
    """
    p, C, twoC = chan["p"], K["C"], 2 * K["C"]
    bet = np.linspace(0.0, 0.5, 20001)
    B1 = np.array([C + 1 - h2(b * (1 - p) + (1 - b) * p) for b in bet])
    S = B1 + np.array([C * h2(b) for b in bet])
    bs = np.linspace(0.0, twoC, 1201)
    fr = np.array([float(np.max(np.minimum(B1[B1 >= b - 1e-15],
                                           S[B1 >= b - 1e-15] - b)))
                   if (B1 >= b - 1e-15).any() else -1.0 for b in bs])

    def in_slice(a, b):
        return 0 <= b <= bs[-1] and 0 <= a <= np.interp(b, bs, fr) + 1e-12

    caps = [theorem3_caps(split_block(b), split_block(b), chan)
            for b in np.linspace(0.0, 0.5, 401)]
    Px = np.zeros((2, 1, 2))
    Px[0, 0, 0] = Px[1, 0, 1] = 0.5
    caps.append(theorem3_caps(Px, Px, chan))
    for b in np.linspace(0.0, 0.5, 101):
        caps.append(theorem3_caps(Px, split_block(b), chan))
        caps.append(theorem3_caps(split_block(b), Px, chan))
    worst, wl = -1e9, None
    for lam in [(1, 1, 1), (1.1, 1, 1), (1.2, 1, 1), (1.5, 1, 1), (2, 1, 1),
                (1, 1, 0.5), (1.3, 1, 0.7)]:
        best = 0.0
        for R0 in np.linspace(0.0, twoC, 161):
            for R1 in np.linspace(0.0, twoC, 161):
                if not in_slice(R0 + R1, 0.0):
                    continue
                lo, hi = 0.0, twoC
                for _ in range(26):
                    mid = 0.5 * (lo + hi)
                    if in_slice(R0 + R1, mid) and in_slice(R1, R0 + mid):
                        lo = mid
                    else:
                        hi = mid
                best = max(best, lam[0] * R0 + lam[1] * R1 + lam[2] * lo)
        hc = max(support_of_box(c, lam) for c in caps)
        if best - hc > worst:
            worst, wl = best - hc, lam
    record("T18 the R0=0 slice determines the region (SCREEN)", worst < 1e-3,
           f"max [h_D - h_C] = {worst:.3e} at lam={wl} over 7 mixed directions, "
           f"where D = {{R0 <= 2C, (0,R0+R1,R2) and (0,R1,R0+R2) in C's slice}} "
           f"-- Thm7 ⊆ D holds by the box projection identity")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20260808)
    ap.add_argument("--draws", type=int, default=200)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)

    K = constants()
    chan = probc_blocks()

    t1_constants(K)
    t2_more_capable(K, chan)
    t3_m6_witness(K, chan)
    t4_mirror(K, chan, rng)
    t5_shoulder_closed_form(K, chan)
    t6_shoulder_is_the_envelope(K, chan, rng)
    t7(chan, rng, args.draws)
    t8_channel_generic(rng)
    t9_18b_18e(chan, rng, args.draws)
    t10_free_face_caps(K, chan, rng)
    t11_w_const_wlog(chan, rng, args.draws)
    t12_free_support_matches_C(K, chan)
    t13_endpoints(K, chan)
    t14_free_screen(K, chan, rng)
    t15_face_maxima(K, chan, rng)
    t16_shoulder_gap_vs_box(K)
    t17_envelope_column_generation(K, chan, rng)
    t18_slice_determines_region(K, chan)

    bad = [n for n, ok, _ in RESULTS if not ok]
    print(f"\n{len(RESULTS) - len(bad)}/{len(RESULTS)} tests passed")
    if bad:
        print("FAILED: " + ", ".join(bad))
    raise SystemExit(1 if bad else 0)


if __name__ == "__main__":
    main()
