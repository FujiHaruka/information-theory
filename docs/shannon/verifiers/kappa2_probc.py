#!/usr/bin/env python3
"""Covering-number (kappa) verifier for the [probc] reversely-more-capable instance.

Implements Theorem 7 of [auxrec] verbatim -- (18a)-(18i), (19a)-(19c), (20a)-(20c)
(auxrec.txt:1037-1082 of the `pdftotext -layout` output; retrieval = docs/shannon/lit-fetch.sh)
-- on the product channel of [probc] Lemma 8 (probc.txt:900-923):

    X = (X1, X2) in {0,1}^2,   Y = (Y1, Y2),   Z = (Z1, Z2),
    X1 -> Y1 = BEC(e),  X1 -> Z1 = BSC(p),  X2 -> Y2 = BSC(p),  X2 -> Z2 = BEC(e),
    p = 0.1,  e = h(0.1)   (so both components have the same capacity C = 1 - h(p)).

Witness w = (plain (U,V,W), tilde (Wt,Ut,Vt), hat (Wh,Uh,Vh)), the three systems
conditionally independent given X (auxrec.txt:1074).  The auxiliary receiver is
T_{J|X} only (## M4 (T3b): the index set collapses to T_{J|X} in both directions).

Run:  python3 docs/shannon/verifiers/kappa2_probc.py [--seed N] [--draws N]
Exit code 0 iff every test passes.
"""
import argparse
import itertools
import numpy as np

LOG2 = np.log(2.0)
TOL = 1e-12


# ---------------------------------------------------------------- information


def _ent(P):
    P = np.asarray(P, dtype=float)
    Q = P[P > 0]
    return float(-(Q * np.log(Q)).sum() / LOG2)


AX = {"x": 0, "w": 1, "u": 2, "v": 3, "b": 4}


def _H(P, names):
    """Entropy of the marginal of P on the named axes (P has axes x,w,u,v,b)."""
    if not names:
        return 0.0
    keep = tuple(sorted(AX[n] for n in names))
    drop = tuple(a for a in range(5) if a not in keep)
    return _ent(P.sum(axis=drop) if drop else P)


def _mi(P, A, B, C=()):
    """I(A;B|C) from the joint P over axes (x,w,u,v,b)."""
    A, B, C = tuple(A), tuple(B), tuple(C)
    return _H(P, A + C) + _H(P, B + C) - _H(P, A + B + C) - _H(P, C)


def _joint(px, K, KB):
    """p(x) K[x,w,u,v] KB[x,b] -- one system plus one of Y / Z / J."""
    return px[:, None, None, None, None] * K[:, :, :, :, None] * KB[:, None, None, None, :]


class Terms:
    """Every mutual-information term appearing in (18)/(19)/(20), evaluated once."""

    def __init__(self, px, Kp, Kt, Kh, TY, TZ, TJ):
        self.px = px
        P = {("p", "Y"): _joint(px, Kp, TY), ("p", "Z"): _joint(px, Kp, TZ),
             ("t", "Y"): _joint(px, Kt, TY), ("t", "Z"): _joint(px, Kt, TZ),
             ("t", "J"): _joint(px, Kt, TJ), ("h", "Y"): _joint(px, Kh, TY),
             ("h", "Z"): _joint(px, Kh, TZ), ("h", "J"): _joint(px, Kh, TJ),
             ("p", "J"): _joint(px, Kp, TJ)}
        self.P = P
        m = lambda s, r, A, B, C=(): _mi(P[(s, r)], A, B, C)
        # plain system
        self.WY, self.WZ = m("p", "Y", "w", "b"), m("p", "Z", "w", "b")
        self.UY_W, self.UZ_W = m("p", "Y", "u", "b", "w"), m("p", "Z", "u", "b", "w")
        self.VZ_W, self.VY_W = m("p", "Z", "v", "b", "w"), m("p", "Y", "v", "b", "w")
        self.XY_VW, self.XZ_UW = m("p", "Y", "x", "b", "vw"), m("p", "Z", "x", "b", "uw")
        self.VWZ, self.VWY = m("p", "Z", "vw", "b"), m("p", "Y", "vw", "b")
        # tilde system
        self.WtZ, self.WtJ = m("t", "Z", "w", "b"), m("t", "J", "w", "b")
        self.UtZ_Wt, self.UtJ_Wt = m("t", "Z", "u", "b", "w"), m("t", "J", "u", "b", "w")
        self.VtZ_Wt, self.VtJ_Wt = m("t", "Z", "v", "b", "w"), m("t", "J", "v", "b", "w")
        self.XZ_UtWt, self.XJ_UtWt = m("t", "Z", "x", "b", "uw"), m("t", "J", "x", "b", "uw")
        self.VtWtZ = m("t", "Z", "vw", "b")
        # hat system
        self.WhY, self.WhJ = m("h", "Y", "w", "b"), m("h", "J", "w", "b")
        self.UhY_Wh, self.UhJ_Wh = m("h", "Y", "u", "b", "w"), m("h", "J", "u", "b", "w")
        self.VhY_Wh, self.VhJ_Wh = m("h", "Y", "v", "b", "w"), m("h", "J", "v", "b", "w")
        self.XY_VhWh, self.XJ_VhWh = m("h", "Y", "x", "b", "vw"), m("h", "J", "x", "b", "vw")
        self.VhWhY = m("h", "Y", "vw", "b")
        # X vs the auxiliary receiver
        self.XJ = m("p", "J", "x", "b")
        # conditional entropies used by the structure lemma
        self.HX_VhWhY = _H(P[("h", "Y")], "xvwb") - _H(P[("h", "Y")], "vwb")
        self.HX_VhWh = _H(P[("h", "Y")], "xvw") - _H(P[("h", "Y")], "vw")
        self.HX_UtWtZ = _H(P[("t", "Z")], "xuwb") - _H(P[("t", "Z")], "uwb")
        self.HX_UtWt = _H(P[("t", "Z")], "xuw") - _H(P[("t", "Z")], "uw")

    # ---- (19) / (20): eligibility residuals (all affine in the measure mu)
    def elig(self):
        r19a = self.WtZ - self.WtJ + self.WhJ - self.WhY - self.WZ + self.WY
        r19b = self.UtZ_Wt - self.UtJ_Wt + self.UhJ_Wh - self.UhY_Wh - self.UZ_W + self.UY_W
        r19c = self.VtZ_Wt - self.VtJ_Wt + self.VhJ_Wh - self.VhY_Wh - self.VZ_W + self.VY_W
        lo_a = self.XZ_UtWt - self.XJ_UtWt
        hi_a = (self.VtZ_Wt - self.VtJ_Wt) - lo_a
        lo_b = self.XY_VhWh - self.XJ_VhWh
        hi_b = (self.UhY_Wh - self.UhJ_Wh) - lo_b
        r20c = self.VZ_W + self.XY_VW - self.UY_W - self.XZ_UW
        return dict(r19a=r19a, r19b=r19b, r19c=r19c, lo20a=lo_a, hi20a=hi_a,
                    lo20b=lo_b, hi20b=hi_b, r20c=r20c)

    # ---- (18): the rate bundle
    def bounds(self):
        mWYZ = min(self.WY, self.WZ)
        br_t = self.WtJ + self.WhY - self.WhJ
        br_h = self.WhJ + self.WtZ - self.WtJ
        b18a = min(self.WY, self.WhY, self.WZ, self.WtZ)
        b18b = mWYZ + self.UY_W
        b18c = min(self.WtZ + min(0.0, self.WY - self.WZ), br_t) \
            + self.UtJ_Wt + self.UhY_Wh - self.UhJ_Wh
        b18d = min(self.WhY + min(0.0, self.WZ - self.WY), br_h) + self.UhY_Wh
        b18e = mWYZ + self.VZ_W
        b18f = min(self.WhY + min(0.0, self.WZ - self.WY), br_h) \
            + self.VhJ_Wh + self.VtZ_Wt - self.VtJ_Wt
        b18g = min(self.WtZ + min(0.0, self.WY - self.WZ), br_t) + self.VtZ_Wt
        b18h = min(self.WhY - self.WhJ, self.WtZ - self.WtJ) + self.XJ \
            + self.UhY_Wh - self.UhJ_Wh + self.VtZ_Wt - self.VtJ_Wt
        b18i = mWYZ + min(self.VZ_W + self.XY_VW, self.UY_W + self.XZ_UW)
        return dict(b18a=b18a, b18b=b18b, b18c=b18c, b18d=b18d, b18e=b18e,
                    b18f=b18f, b18g=b18g, b18h=b18h, b18i=b18i)


# ---------------------------------------------------------------- the instance


def h2(a):
    if a <= 0.0 or a >= 1.0:
        return 0.0
    return float(-a * np.log2(a) - (1 - a) * np.log2(1 - a))


def probc_instance(p=0.1):
    """X1->Y1 = BEC(e), X1->Z1 = BSC(p), X2->Y2 = BSC(p), X2->Z2 = BEC(e)."""
    e = h2(p)
    bec = np.array([[1 - e, 0.0, e], [0.0, 1 - e, e]])       # {0,1} -> {0,1,erase}
    bsc = np.array([[1 - p, p], [p, 1 - p]])
    TY = np.zeros((4, 6))
    TZ = np.zeros((4, 6))
    for x1, x2 in itertools.product(range(2), repeat=2):
        x = 2 * x1 + x2
        TY[x] = np.kron(bec[x1], bsc[x2])                    # (Y1,Y2) = (BEC, BSC)
        TZ[x] = np.kron(bsc[x1], bec[x2])                    # (Z1,Z2) = (BSC, BEC)
    return TY, TZ, e


def mi_xy(px, T):
    P = px[:, None] * T
    return _ent(P.sum(0)) + _ent(P.sum(1)) - _ent(P)


# ---------------------------------------------------------------- random parts


def rand_kernel(rng, nx, dims, conc=0.6):
    K = rng.dirichlet(conc * np.ones(int(np.prod(dims))), size=nx)
    return K.reshape((nx,) + tuple(dims))


def det_kernel(nx, wf, uf, vf, dims):
    K = np.zeros((nx,) + tuple(dims))
    for x in range(nx):
        K[x, wf(x), uf(x), vf(x)] = 1.0
    return K


def tj_identity(nx):
    return np.eye(nx)


def tj_const(nx):
    return np.ones((nx, 1))


def tj_random(rng, nx, nj=None, conc=0.5):
    nj = nj or int(rng.integers(2, 6))
    return rng.dirichlet(conc * np.ones(nj), size=nx)


def tj_depolarizer(nx, lam):
    return lam * np.eye(nx) + (1 - lam) * np.ones((nx, nx)) / nx


def tj_mix(T1, T2, lam):
    """Tagged sum J = (S, J_S) with S ~ Bern(lam) independent of X."""
    n1, n2 = T1.shape[1], T2.shape[1]
    T = np.zeros((T1.shape[0], n1 + n2))
    T[:, :n1] = lam * T1
    T[:, n1:] = (1 - lam) * T2
    return T


def sys_mix(K1, K2, mu):
    """Time-sharing of two systems: W = (S, W_S), U = U_S, V = V_S (tagged)."""
    nx = K1.shape[0]
    d = tuple(a + b for a, b in zip(K1.shape[1:], K2.shape[1:]))
    K = np.zeros((nx,) + d)
    K[:, :K1.shape[1], :K1.shape[2], :K1.shape[3]] = mu * K1
    K[:, K1.shape[1]:, K1.shape[2]:, K1.shape[3]:] = (1 - mu) * K2
    return K


# ---------------------------------------------------------------- tests

RESULTS = []


def record(name, ok, detail):
    RESULTS.append((name, ok, detail))
    print(f"[{'PASS' if ok else 'FAIL'}] {name}: {detail}")


def t1_numerics(TY, TZ, e, p=0.1):
    from scipy.optimize import minimize
    C = 1 - h2(p)
    grid = np.linspace(1e-9, 1 - 1e-9, 2_000_001)
    hs = -grid * np.log2(grid) - (1 - grid) * np.log2(1 - grid)
    ap = grid * (1 - p) + (1 - grid) * p
    hap = -ap * np.log2(ap) - (1 - ap) * np.log2(1 - ap)
    D1 = (1 - e) * hs - hap + h2(p)                       # I(X1;Y1) - I(X1;Z1)
    dstar, astar = float(D1.max()), float(grid[int(D1.argmax())])
    # full-simplex version on the product channel (correlated inputs allowed)
    rng = np.random.default_rng(7)

    def negphi(th):
        q = np.exp(th - th.max()); q /= q.sum()
        return -(mi_xy(q, TY) - mi_xy(q, TZ))
    best = -1.0
    for _ in range(400):
        r = minimize(negphi, rng.normal(0, 3.0, 4), method="Nelder-Mead",
                     options=dict(xatol=1e-10, fatol=1e-14, maxiter=4000))
        best = max(best, -float(r.fun))
    ok = (abs(C - 0.5310044) < 5e-7 and abs(2 * C - 1.0620088) < 5e-7
          and abs(dstar - 0.03877137) < 5e-7 and abs(astar - 0.0776695) < 5e-5
          and abs(2 * C + dstar - 1.1007802) < 5e-7 and best <= dstar + 1e-6
          and float(D1.min()) >= -1e-12)
    record("T1 numerics (## M12 (T3b) row 9)", ok,
           f"C={C:.7f} 2C={2*C:.7f} d*={dstar:.8f} at alpha={astar:.7f} "
           f"SR_C={2*C+dstar:.7f} full-simplex max={best:.8f} min D1={float(D1.min()):.3e}")
    return C, dstar, 2 * C + dstar


def t2_structure_lemma(TY, TZ):
    """H(X|A,Y)=0 => H(X|A)=0 holds iff every pair of inputs is Y-confusable."""
    def pairwise(T):
        bad = []
        for a, b in itertools.combinations(range(T.shape[0]), 2):
            if not np.any((T[a] > 0) & (T[b] > 0)):
                bad.append((a, b))
        return bad
    badY, badZ = pairwise(TY), pairwise(TZ)
    # exhaustive check over every deterministic A (all 15 set partitions of X)
    viol = 0
    px = np.ones(4) / 4
    for parts in _partitions(list(range(4))):
        lab = {x: i for i, blk in enumerate(parts) for x in blk}
        A = np.zeros((4, len(parts)))
        for x in range(4):
            A[x, lab[x]] = 1.0
        for T in (TY, TZ):
            PA = px[:, None, None, None] * A[:, :, None, None] * T[:, None, None, :]
            HXA_R = _H(PA.reshape(4, len(parts), 1, 1, T.shape[1]), "xwb") \
                - _H(PA.reshape(4, len(parts), 1, 1, T.shape[1]), "wb")
            HXA = _H(PA.reshape(4, len(parts), 1, 1, T.shape[1]), "xw") \
                - _H(PA.reshape(4, len(parts), 1, 1, T.shape[1]), "w")
            if HXA_R < 1e-12 and HXA > 1e-12:
                viol += 1
    ok = (not badY) and (not badZ) and viol == 0
    record("T2 structure lemma (## M12 (T3b) row 2)", ok,
           f"non-confusable pairs: Y={badY} Z={badZ}; deterministic-A counterexamples={viol}/30")


def _partitions(xs):
    if not xs:
        yield []
        return
    first, rest = xs[0], xs[1:]
    for p in _partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]
        yield [[first]] + p


def t3_j_free(px, TY, TZ, rng, draws=12):
    """(18a),(18b),(18e),(18i) carry no J; the other five do."""
    spread = {k: [] for k in ["b18a", "b18b", "b18c", "b18d", "b18e", "b18f", "b18g", "b18h", "b18i"]}
    for _ in range(draws):
        Kp, Kt, Kh = (rand_kernel(rng, 4, (2, 2, 2)) for _ in range(3))
        vals = [Terms(px, Kp, Kt, Kh, TY, TZ, TJ).bounds()
                for TJ in [tj_const(4), tj_identity(4), tj_random(rng, 4),
                           tj_random(rng, 4), tj_depolarizer(4, 0.3)]]
        for k in spread:
            spread[k].append(max(v[k] for v in vals) - min(v[k] for v in vals))
    free = ["b18a", "b18b", "b18e", "b18i"]
    mfree = max(max(spread[k]) for k in free)
    mdep = min(max(spread[k]) for k in spread if k not in free)
    ok = mfree < 1e-14 < mdep
    record("T3 (18i) is J-free (auxrec.txt:1069-1071)", ok,
           f"max spread over J for (18a,b,e,i) = {mfree:.2e}; min spread for the other five = {mdep:.2e}")


def t4_affine_in_mu(px, TY, TZ, rng, draws=30):
    """Every (19)/(20) residual and every J-dependent (18) bound is affine in mu."""
    worst = 0.0
    for _ in range(draws):
        Kp, Kt, Kh = (rand_kernel(rng, 4, (2, 2, 2)) for _ in range(3))
        T1, T2 = tj_random(rng, 4), tj_random(rng, 4)
        for lam in (0.25, 0.5, 0.73):
            mix = Terms(px, Kp, Kt, Kh, TY, TZ, tj_mix(T1, T2, lam))
            e1 = Terms(px, Kp, Kt, Kh, TY, TZ, T1)
            e2 = Terms(px, Kp, Kt, Kh, TY, TZ, T2)
            for f in ("elig",):
                a, b, c = getattr(mix, f)(), getattr(e1, f)(), getattr(e2, f)()
                worst = max(worst, max(abs(a[k] - lam * b[k] - (1 - lam) * c[k]) for k in a))
            # (18c),(18d),(18f),(18g),(18h) are min{affine,affine}+affine: check the pieces
            for k in ("WtJ", "WhJ", "UtJ_Wt", "UhJ_Wh", "VtJ_Wt", "VhJ_Wh",
                      "XJ", "XJ_UtWt", "XJ_VhWh"):
                worst = max(worst, abs(getattr(mix, k) - lam * getattr(e1, k)
                                       - (1 - lam) * getattr(e2, k)))
    record("T4 eligibility is affine in mu => E_R(w) convex (## M11 (T3b) row 4)",
           worst < 1e-13, f"max |residual(mix) - affine mix| = {worst:.2e} over {draws} draws")


def t5_identities(px, TY, TZ, rng, draws=40):
    """The three identities behind the main theorem (## M12 (T3b) row 3)."""
    wA = wB = wC = wD = 0.0
    for _ in range(draws):
        Kp, Kt, Kh = (rand_kernel(rng, 4, (2, 2, 2)) for _ in range(3))
        t = Terms(px, Kp, Kt, Kh, TY, TZ, tj_const(4))
        IXY, IXZ = mi_xy(px, TY), mi_xy(px, TZ)
        wA = max(wA, abs(t.XY_VW + t.VWY - IXY))              # (S2) chain rule
        wB = max(wB, abs(t.WZ + t.VZ_W - t.VWZ))
        e = t.elig()
        wC = max(wC, abs((e["r19a"] + e["r19c"])
                         - ((t.VtWtZ - t.VhWhY) - (t.VWZ - t.VWY))))   # (S3)
        # (S4): a hat that determines X has I(Vh,Wh;Y) = I(X;Y)
        Kd = det_kernel(4, lambda x: x // 2, lambda x: 0, lambda x: x % 2, (2, 1, 2))
        td = Terms(px, Kp, Kt, Kd, TY, TZ, tj_const(4))
        wD = max(wD, abs(td.HX_VhWh) + abs(td.VhWhY - IXY))
    ok = max(wA, wB, wC, wD) < 1e-13
    record("T5 main-theorem identities S2/S3/S4 (## M12 (T3b) row 3)", ok,
           f"|S2|={wA:.2e} |S3-chain|={wB:.2e} |(19a)+(19c) = rate gap|={wC:.2e} |S4|={wD:.2e}")


def t5b_chain(px, TY, TZ, rng, draws=40):
    """The case-free chain: (18i) <= I(W;Z)+I(V;Z|W)+I(X;Y|V,W) = I(X;Y)+(19a)+(19c)@const
    gap, so no split on sign(I(W;Y)-I(W;Z)) is needed."""
    worst_step1, worst_step2 = -1e9, 0.0
    for _ in range(draws):
        Kp, Kt, Kh = (rand_kernel(rng, 4, (2, 2, 2)) for _ in range(3))
        t = Terms(px, Kp, Kt, Kh, TY, TZ, tj_const(4))
        e = t.elig()
        lhs = t.bounds()["b18i"]
        mid = t.WZ + t.VZ_W + t.XY_VW
        worst_step1 = max(worst_step1, lhs - mid)                      # must be <= 0
        rhs = mi_xy(px, TY) + (t.VtWtZ - t.VhWhY) - (e["r19a"] + e["r19c"])
        worst_step2 = max(worst_step2, abs(mid - rhs))                 # identity
    ok = worst_step1 <= 1e-13 and worst_step2 < 1e-13
    record("T5b case-free chain to (18i) (sharpening of ## M12 (T3b) row 3)", ok,
           f"max[(18i) - (I(W;Z)+I(V;Z|W)+I(X;Y|V,W))] = {worst_step1:.2e} (<= 0); "
           f"max |identity residual| = {worst_step2:.2e}")


def t5c_hinge(px, TY, TZ, rng, draws=40):
    """(20b)-lower at J = X is exactly -H(X|Vh,Wh,Y); likewise (20a) with Z."""
    worst = 0.0
    for _ in range(draws):
        Kp, Kt, Kh = (rand_kernel(rng, 4, (2, 2, 2)) for _ in range(3))
        t = Terms(px, Kp, Kt, Kh, TY, TZ, tj_identity(4))
        e = t.elig()
        worst = max(worst, abs(e["lo20b"] + t.HX_VhWhY), abs(e["lo20a"] + t.HX_UtWtZ))
    record("T5c (20)-lower at J = X is an equality hinge", worst < 1e-13,
           f"max |lo(20b)@X + H(X|Vh,Wh,Y)| and |lo(20a)@X + H(X|Ut,Wt,Z)| = {worst:.2e}")


def t6_main_theorem(px, TY, TZ, C, SRC, rng, draws=60):
    """Consistency check (NOT evidence, cf. plan 4.5): witnesses that satisfy
    (19)@const and (20)-lower@X all obey (18i) <= 2C < SR_C."""
    FUNS = [lambda x: 0, lambda x: x // 2, lambda x: x % 2,
            lambda x: (x // 2) ^ (x % 2), lambda x: x]
    worst, n, nweak, tested = -1e9, 0, 0, 0
    pxs = [px] + [rng.dirichlet(np.ones(4) * 1.5) for _ in range(5)]
    for q in pxs:
        for iw, iu, iv in itertools.product(range(5), repeat=3):
            Kp = det_kernel(4, FUNS[iw], FUNS[iu], FUNS[iv], (4, 4, 4))
            for Ka in (Kp, det_kernel(4, lambda x: x, lambda x: 0, lambda x: 0, (4, 4, 4))):
                tested += 1
                t0 = Terms(q, Kp, Ka, Ka, TY, TZ, tj_const(4))
                tX = Terms(q, Kp, Ka, Ka, TY, TZ, tj_identity(4))
                e0, eX = t0.elig(), tX.elig()
                if max(abs(e0["r19a"]), abs(e0["r19b"]), abs(e0["r19c"])) > 1e-11:
                    continue                                   # (19) @ J = const
                if min(eX["lo20a"], eX["lo20b"]) < -1e-11:
                    continue                                   # (20)-lower @ J = X
                n += 1
                if min(e0["lo20a"], e0["hi20a"], e0["lo20b"], e0["hi20b"]) < -1e-11 \
                        or abs(e0["r20c"]) > 1e-11:
                    nweak += 1                    # passes the weakened hypothesis only
                worst = max(worst, t0.bounds()["b18i"])
    ok = n > 0 and worst <= 2 * C + 1e-9 < SRC
    record("T6 (19)@const + (20)-lower@X => (18i) <= 2C  [consistency, not evidence]", ok,
           f"{n}/{tested} qualifying witnesses over 6 input laws; {nweak} of them are NOT "
           f"fully eligible at J = const; max (18i) = {worst:.7f} <= 2C = {2*C:.7f} "
           f"< SR_C = {SRC:.7f}")


def t7_robustness(px, TY, TZ, C, SRC, rng, draws=60):
    """## M12 (T3b) row 8: I(Vh,Wh;J1) = I(X;J1) for X-determining hats,
    plus the depolarizer calibration of the bound 2C + I(X;J1)."""
    Kd = det_kernel(4, lambda x: x // 2, lambda x: 0, lambda x: x % 2, (2, 1, 2))
    Kp = rand_kernel(rng, 4, (2, 2, 2))
    worst = 0.0
    for _ in range(draws):
        TJ = tj_random(rng, 4)
        t = Terms(px, Kp, Kd, Kd, TY, TZ, TJ)
        IVhWhJ = _mi(_joint(px, Kd, TJ), "vw", "b")
        worst = max(worst, abs(IVhWhJ - t.XJ))
    cal = {}
    for lam in (0.10, 0.20, 0.35):
        TJ = tj_depolarizer(4, lam)
        cal[lam] = (_mi(_joint(px, Kd, TJ), "x", "b"), 2 * C + _mi(_joint(px, Kd, TJ), "x", "b"))
    ok = (worst < 1e-13
          and abs(cal[0.10][0] - 0.020414) < 5e-6 and abs(cal[0.20][0] - 0.078072) < 5e-6
          and abs(cal[0.35][0] - 0.227782) < 5e-6
          and abs(cal[0.10][1] - 1.0824230) < 5e-6 and abs(cal[0.20][1] - 1.1400807) < 5e-6
          and cal[0.10][1] < SRC < cal[0.20][1])
    record("T7 robustness bound 2C + I(X;J1) (## M12 (T3b) row 8)", ok,
           "max |I(Vh,Wh;J1)-I(X;J1)| = %.2e; I(X;J1) = %.6f/%.6f/%.6f; bounds %.7f/%.7f"
           % (worst, cal[0.10][0], cal[0.20][0], cal[0.35][0], cal[0.10][1], cal[0.20][1]))


def t8_witness_mixing(px, TY, TZ, rng, draws=20):
    """## M11 (T3b) row 5: every (18)/(19)/(20) term is affine in the time-sharing
    weight, so the eligibility residual of a mixture is the mixture of residuals."""
    worst = 0.0
    for _ in range(draws):
        K1 = [rand_kernel(rng, 4, (2, 2, 2)) for _ in range(3)]
        K2 = [rand_kernel(rng, 4, (2, 2, 2)) for _ in range(3)]
        TJ = tj_random(rng, 4)
        for mu in (0.25, 0.5, 0.75):
            mix = Terms(px, *[sys_mix(a, b, mu) for a, b in zip(K1, K2)], TY, TZ, TJ)
            e1 = Terms(px, *K1, TY, TZ, TJ).elig()
            e2 = Terms(px, *K2, TY, TZ, TJ).elig()
            em = mix.elig()
            worst = max(worst, max(abs(em[k] - mu * e1[k] - (1 - mu) * e2[k]) for k in em))
    record("T8 witness time-sharing is affine (## M11 (T3b) row 5)", worst < 1e-13,
           f"max |residual(mix) - affine mix| = {worst:.2e} over {draws} draws")


def t9_uniform_attainment(px, TY, TZ, C, rng, draws=40):
    """## M12 (T3b) row 4: W = X, U = V = const is eligible for every T_J and its
    (18i) is exactly 2C."""
    K = det_kernel(4, lambda x: x, lambda x: 0, lambda x: 0, (4, 1, 1))
    b18i = Terms(px, K, K, K, TY, TZ, tj_const(4)).bounds()["b18i"]
    worst = 0.0
    for _ in range(draws):
        for TJ in (tj_const(4), tj_identity(4), tj_random(rng, 4)):
            e = Terms(px, K, K, K, TY, TZ, TJ).elig()
            worst = max(worst, abs(e["r19a"]), abs(e["r19b"]), abs(e["r19c"]), abs(e["r20c"]),
                        max(0.0, -e["lo20a"]), max(0.0, -e["hi20a"]),
                        max(0.0, -e["lo20b"]), max(0.0, -e["hi20b"]))
    ok = abs(b18i - 2 * C) < 1e-9 and worst < 1e-13
    record("T9 uniform attainment (18i) = 2C (## M12 (T3b) row 4)", ok,
           f"(18i) = {b18i:.7f}, 2C = {2*C:.7f}; max eligibility violation over J = {worst:.2e}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20260808)
    ap.add_argument("--draws", type=int, default=30)
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)
    TY, TZ, e = probc_instance()
    px = np.ones(4) / 4
    C, dstar, SRC = t1_numerics(TY, TZ, e)
    t2_structure_lemma(TY, TZ)
    t3_j_free(px, TY, TZ, rng)
    t4_affine_in_mu(px, TY, TZ, rng, a.draws)
    t5_identities(px, TY, TZ, rng, a.draws)
    t5b_chain(px, TY, TZ, rng, a.draws)
    t5c_hinge(px, TY, TZ, rng, a.draws)
    t6_main_theorem(px, TY, TZ, C, SRC, rng, a.draws)
    t7_robustness(px, TY, TZ, C, SRC, rng, a.draws)
    t8_witness_mixing(px, TY, TZ, rng, min(a.draws, 20))
    t9_uniform_attainment(px, TY, TZ, C, rng, min(a.draws, 20))
    bad = [n for n, ok, _ in RESULTS if not ok]
    print("\n%d/%d tests passed" % (len(RESULTS) - len(bad), len(RESULTS)))
    if bad:
        print("FAILED: " + ", ".join(bad))
    raise SystemExit(1 if bad else 0)


if __name__ == "__main__":
    main()
