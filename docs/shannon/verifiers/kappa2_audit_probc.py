#!/usr/bin/env python3
"""Independent audit re-implementation of Theorem 7 of [auxrec] on the [probc] instance.

Written for the adversarial audit of `docs/shannon/bc-t3c-a1-kappa2.md` (N4).
It shares no code with `docs/shannon/verifiers/kappa2_probc.py` -- (18a)-(18i),
(19a)-(19c) and (20a)-(20c) are transcribed here directly from
`auxrec.txt:1037-1082` (retrieval command: `docs/shannon/lit-fetch.sh`), and the
channel from `probc.txt:900-923`.

Conventions.  Every information term of Theorem 7 mentions at most one of the
three auxiliary systems and at most one of Y / Z, so the whole bound can be
evaluated on three separate joints  p(w,u,v,x,y,z,j)  -- one per system --
without ever building the 13-variable product.  T_{J|X} is used (the collapse of
the index set from T_{J|X,Y,Z} is `## M4 (T3b)`); a T_{J|X,Y,Z} kernel is fed in
as an extra check that it changes nothing (A0).

Run: python3 docs/shannon/verifiers/kappa2_audit_probc.py
"""

import itertools
import numpy as np

AX = "wuvxyzj"          # axis names of the per-system joint, in order


# ----------------------------------------------------------------- information

def _h(p):
    p = p[p > 0]
    return float(-(p * np.log2(p)).sum())


def H(P, names):
    """Entropy of the marginal of P on the named axes."""
    keep = tuple(AX.index(c) for c in names)
    drop = tuple(i for i in range(P.ndim) if i not in keep)
    return _h(P.sum(axis=drop).ravel()) if drop else _h(P.ravel())


def I(P, a, b, c=""):
    """I(a ; b | c) with a, b, c strings of axis names."""
    return H(P, a + c) + H(P, b + c) - H(P, c) - H(P, a + b + c)


# --------------------------------------------------------------- the instance

def hb(t):
    if t <= 0.0 or t >= 1.0:
        return 0.0
    return float(-t * np.log2(t) - (1 - t) * np.log2(1 - t))


def bec(eps):
    return np.array([[1 - eps, 0.0, eps], [0.0, 1 - eps, eps]])


def bsc(q):
    return np.array([[1 - q, q], [q, 1 - q]])


def instance(q=0.1):
    """probc.txt:900-902  X1->Y1 = BEC(e), X1->Z1 = BSC(p), X2->Y2 = BSC(p),
    X2->Z2 = BEC(e),  p = 0.1, e = H(0.1).  X = (x1,x2) indexed as 2*x1+x2."""
    eps = hb(q)
    TY = np.zeros((4, 6))
    TZ = np.zeros((4, 6))
    B, S = bec(eps), bsc(q)
    for x1 in range(2):
        for x2 in range(2):
            x = 2 * x1 + x2
            TY[x] = np.outer(B[x1], S[x2]).ravel()      # (Y1,Y2) = (BEC, BSC)
            TZ[x] = np.outer(S[x1], B[x2]).ravel()      # (Z1,Z2) = (BSC, BEC)
    return TY, TZ, eps


def joint(px, K, TY, TZ, TJ):
    """p(w,u,v,x,y,z,j) = p(x) K(w,u,v|x) TY(y|x) TZ(z|x) TJ(j|x [,y,z])."""
    nx = px.shape[0]
    P = px[None, None, None, :, None, None, None] * \
        np.moveaxis(K, 0, 3)[:, :, :, :, None, None, None]
    P = P * TY[None, None, None, :, :, None, None]
    P = P * TZ[None, None, None, :, None, :, None]
    if TJ.ndim == 1:                                     # J = const
        P = P * TJ[None, None, None, None, None, None, :]
    elif TJ.ndim == 2:                                   # T_{J|X}
        P = P * TJ[None, None, None, :, None, None, :]
    else:                                                # T_{J|X,Y,Z}
        P = P * TJ[None, None, None, :, :, :, :]
    assert P.shape[3] == nx
    return P


# ------------------------------------------------------- Theorem 7, verbatim

class Thm7:
    """(18)/(19)/(20) of auxrec.txt:1037-1082 for a full witness (plain,tilde,hat)."""

    def __init__(self, px, Kp, Kt, Kh, TY, TZ, TJ):
        P = joint(px, Kp, TY, TZ, TJ)
        T = joint(px, Kt, TY, TZ, TJ)
        Hh = joint(px, Kh, TY, TZ, TJ)
        self.P, self.T, self.Hh = P, T, Hh
        # plain
        self.WY, self.WZ = I(P, "w", "y"), I(P, "w", "z")
        self.UY_W, self.UZ_W = I(P, "u", "y", "w"), I(P, "u", "z", "w")
        self.VY_W, self.VZ_W = I(P, "v", "y", "w"), I(P, "v", "z", "w")
        self.XY_VW, self.XZ_UW = I(P, "x", "y", "vw"), I(P, "x", "z", "uw")
        self.VWY, self.VWZ = I(P, "vw", "y"), I(P, "vw", "z")
        # tilde
        self.WtZ, self.WtJ = I(T, "w", "z"), I(T, "w", "j")
        self.UtZ_Wt, self.UtJ_Wt = I(T, "u", "z", "w"), I(T, "u", "j", "w")
        self.VtZ_Wt, self.VtJ_Wt = I(T, "v", "z", "w"), I(T, "v", "j", "w")
        self.XZ_UtWt, self.XJ_UtWt = I(T, "x", "z", "uw"), I(T, "x", "j", "uw")
        self.VtWtZ, self.VtWtJ = I(T, "vw", "z"), I(T, "vw", "j")
        # hat
        self.WhY, self.WhJ = I(Hh, "w", "y"), I(Hh, "w", "j")
        self.UhY_Wh, self.UhJ_Wh = I(Hh, "u", "y", "w"), I(Hh, "u", "j", "w")
        self.VhY_Wh, self.VhJ_Wh = I(Hh, "v", "y", "w"), I(Hh, "v", "j", "w")
        self.XY_VhWh, self.XJ_VhWh = I(Hh, "x", "y", "vw"), I(Hh, "x", "j", "vw")
        self.VhWhY, self.VhWhJ = I(Hh, "vw", "y"), I(Hh, "vw", "j")
        self.HX_VhWh = H(Hh, "xvw") - H(Hh, "vw")
        self.HX_VhWhY = H(Hh, "xvwy") - H(Hh, "vwy")
        self.HX_UtWtZ = H(T, "xuwz") - H(T, "uwz")
        self.XJ = I(P, "x", "j")
        self.IXY, self.IXZ = I(P, "x", "y"), I(P, "x", "z")

    # ---- (19) residuals (LHS - RHS; eligibility demands == 0)
    def r19(self):
        a = (self.WtZ - self.WtJ) + (self.WhJ - self.WhY) - (self.WZ - self.WY)
        b = (self.UtZ_Wt - self.UtJ_Wt) + (self.UhJ_Wh - self.UhY_Wh) \
            - (self.UZ_W - self.UY_W)
        c = (self.VtZ_Wt - self.VtJ_Wt) + (self.VhJ_Wh - self.VhY_Wh) \
            - (self.VZ_W - self.VY_W)
        return a, b, c

    # ---- (20) slacks (eligibility demands >= 0, except r20c which demands == 0)
    def s20(self):
        lo_a = self.XZ_UtWt - self.XJ_UtWt
        hi_a = (self.VtZ_Wt - self.VtJ_Wt) - lo_a
        lo_b = self.XY_VhWh - self.XJ_VhWh
        hi_b = (self.UhY_Wh - self.UhJ_Wh) - lo_b
        r_c = (self.VZ_W + self.XY_VW) - (self.UY_W + self.XZ_UW)
        return lo_a, hi_a, lo_b, hi_b, r_c

    def eligible(self, tol=1e-10):
        a, b, c = self.r19()
        la, ha, lb, hb_, rc = self.s20()
        return (max(abs(a), abs(b), abs(c), abs(rc)) <= tol
                and min(la, ha, lb, hb_) >= -tol)

    # ---- (18) right-hand sides
    def b18(self):
        mWYZ = min(self.WY, self.WZ)
        tilde_branch = min(self.WtZ + min(0.0, self.WY - self.WZ),
                           self.WtJ + self.WhY - self.WhJ)
        hat_branch = min(self.WhY + min(0.0, self.WZ - self.WY),
                         self.WhJ + self.WtZ - self.WtJ)
        return {
            "18a": min(self.WY, self.WhY, self.WZ, self.WtZ),
            "18b": mWYZ + self.UY_W,
            "18c": tilde_branch + self.UtJ_Wt + self.UhY_Wh - self.UhJ_Wh,
            "18d": hat_branch + self.UhY_Wh,
            "18e": mWYZ + self.VZ_W,
            "18f": hat_branch + self.VhJ_Wh + self.VtZ_Wt - self.VtJ_Wt,
            "18g": tilde_branch + self.VtZ_Wt,
            "18h": min(self.WhY - self.WhJ, self.WtZ - self.WtJ) + self.XJ
                   + self.UhY_Wh - self.UhJ_Wh + self.VtZ_Wt - self.VtJ_Wt,
            "18i": mWYZ + min(self.VZ_W + self.XY_VW, self.UY_W + self.XZ_UW),
        }


# ------------------------------------------------------------------ kernels

def rand_K(rng, nx, dims, conc=0.7):
    return rng.dirichlet(conc * np.ones(int(np.prod(dims))), size=nx) \
              .reshape((nx,) + tuple(dims))


def det_K(nx, wf, uf, vf, dims):
    K = np.zeros((nx,) + tuple(dims))
    for x in range(nx):
        K[x, wf(x), uf(x), vf(x)] = 1.0
    return K


J_CONST = np.ones((4, 1))
J_X = np.eye(4)


def J_rand(rng, nx=4, nj=None, conc=0.6):
    nj = nj or int(rng.integers(2, 6))
    return rng.dirichlet(conc * np.ones(nj), size=nx)


def J_tag(T1, T2, lam):
    """Tagged mixture J = (S, J_S), S ~ Bern(lam) independent of everything:
    the measure-level convex combination lam*mu1 + (1-lam)*mu2 on Delta(X)."""
    out = np.zeros((T1.shape[0], T1.shape[1] + T2.shape[1]))
    out[:, :T1.shape[1]] = lam * T1
    out[:, T1.shape[1]:] = (1 - lam) * T2
    return out


def sys_tag(K1, K2, mu):
    d = tuple(a + b for a, b in zip(K1.shape[1:], K2.shape[1:]))
    K = np.zeros((K1.shape[0],) + d)
    K[:, :K1.shape[1], :K1.shape[2], :K1.shape[3]] = mu * K1
    K[:, K1.shape[1]:, K1.shape[2]:, K1.shape[3]:] = (1 - mu) * K2
    return K


# -------------------------------------------------------------------- checks

OUT = []


def say(tag, ok, msg):
    OUT.append((tag, ok))
    print(f"[{'PASS' if ok else 'FAIL'}] {tag}: {msg}")


def a0_j_reduction(px, TY, TZ, rng):
    """T_{J|X,Y,Z} changes no term beyond its induced posterior law on Delta(X)
    (`## M4 (T3b)`), and (18i) carries no J at all (auxrec.txt:1069-1071)."""
    worst_red, spread_i = 0.0, 0.0
    spread_other = {k: 0.0 for k in ("18c", "18d", "18f", "18g", "18h")}
    for _ in range(12):
        Kp, Kt, Kh = (rand_K(rng, 4, (2, 2, 2)) for _ in range(3))
        # a T_{J|X,Y,Z} kernel and the T_{J|X} with the same posterior family
        TJ3 = rng.dirichlet(0.6 * np.ones(3), size=(4, 6, 6))
        # posterior-equivalent T_{J|X}: p(j|x) = sum_{y,z} TY TZ TJ3
        TJ2 = np.einsum("xy,xz,xyzj->xj", TY, TZ, TJ3)
        e3 = Thm7(px, Kp, Kt, Kh, TY, TZ, TJ3)
        e2 = Thm7(px, Kp, Kt, Kh, TY, TZ, TJ2)
        worst_red = max(worst_red,
                        max(abs(u - v) for u, v in zip(e3.r19(), e2.r19())),
                        max(abs(u - v) for u, v in zip(e3.s20(), e2.s20())))
        vals = [Thm7(px, Kp, Kt, Kh, TY, TZ, T).b18()
                for T in (J_CONST, J_X, J_rand(rng), J_rand(rng))]
        spread_i = max(spread_i, max(v["18i"] for v in vals) - min(v["18i"] for v in vals))
        for k in spread_other:
            spread_other[k] = max(spread_other[k],
                                  max(v[k] for v in vals) - min(v[k] for v in vals))
    mdep = min(spread_other.values())
    say("A0 J-reduction + (18i) is J-free",
        worst_red < 1e-12 and spread_i < 1e-14 < mdep,
        f"max|T_(J|XYZ) - T_(J|X)| over (19)/(20) = {worst_red:.2e}; "
        f"(18i) spread over J = {spread_i:.2e}; smallest per-bound spread among the "
        f"five J-carrying bounds = {mdep:.2e}")


def a1_numbers(TY, TZ, eps):
    """C / 2C / d* / SR_C.  d* is recomputed from the channel matrices (not from
    a closed form) as max_alpha I(X1;Y1)-I(X1;Z1); SR_C = 2C + d* is Lemma 8
    (probc.txt:915-921) verbatim."""
    C = 1 - hb(0.1)
    al = np.linspace(0.0, 1.0, 4_000_001)
    # I(X1;Y1) for BEC(e) and I(X1;Z1) for BSC(p), from the matrices
    hs = np.array([hb(a) for a in np.linspace(0, 1, 4001)])
    alc = np.linspace(0, 1, 4001)
    # fine grid using the analytic entropies of the two induced output laws
    def mi_block(a, T):
        p1 = np.array([a, 1 - a])
        P = p1[:, None] * T
        return _h(P.sum(0)) + _h(P.sum(1)) - _h(P.ravel())
    grid = np.linspace(0.0, 1.0, 200001)
    B, S = bec(eps), bsc(0.1)
    # vectorised: BEC(e): I = (1-e) h(a); BSC(p): I = h(a*p) - h(p) -- but compute
    # both from the matrices at a coarse grid first, then refine analytically.
    coarse = [mi_block(a, B) - mi_block(a, S) for a in np.linspace(0, 1, 2001)]
    a_coarse = float(np.linspace(0, 1, 2001)[int(np.argmax(coarse))])
    fine = np.linspace(max(0, a_coarse - 1e-3), min(1, a_coarse + 1e-3), 200001)
    vals = np.array([mi_block(a, B) - mi_block(a, S) for a in fine])
    dstar, astar = float(vals.max()), float(fine[int(vals.argmax())])
    dmin = float(min(mi_block(a, B) - mi_block(a, S) for a in np.linspace(0, 1, 2001)))
    SRC = 2 * C + dstar
    ok = (abs(C - 0.5310044) < 5e-7 and abs(dstar - 0.03877137) < 5e-7
          and abs(astar - 0.0776695) < 1e-4 and abs(SRC - 1.1007802) < 5e-7
          and dmin >= -1e-12)
    say("A1 C / d* / SR_C (## M12 (T3b) row 9)", ok,
        f"C={C:.7f} 2C={2*C:.7f} d*={dstar:.8f} at alpha={astar:.7f} "
        f"SR_C={SRC:.7f}; min(I(X1;Y1)-I(X1;Z1)) = {dmin:.3e} (more-capable)")
    del al, hs, alc, grid
    return C, dstar, SRC


def a2_structure(TY, TZ):
    """`## M12 (T3b)` row 2: H(X|A,Y)=0 => H(X|A)=0 for EVERY A with A--X--(Y,Z).
    The complete proof is pairwise confusability, which covers stochastic A too;
    the 15-partition sweep only covers deterministic A."""
    def conf(T):
        return [(a, b) for a, b in itertools.combinations(range(4), 2)
                if not np.any((T[a] > 0) & (T[b] > 0))]
    bY, bZ = conf(TY), conf(TZ)
    # independent check that confusability really implies the lemma: exhaust
    # deterministic A (15 partitions) AND 4000 stochastic A
    rng = np.random.default_rng(11)
    px = np.ones(4) / 4
    viol = 0
    tested = 0

    def parts(xs):
        if not xs:
            yield []
            return
        for rest in parts(xs[1:]):
            for i in range(len(rest)):
                yield rest[:i] + [[xs[0]] + rest[i]] + rest[i + 1:]
            yield [[xs[0]]] + rest

    cands = []
    for pl in parts([0, 1, 2, 3]):
        A = np.zeros((4, len(pl)))
        for i, blk in enumerate(pl):
            for x in blk:
                A[x, i] = 1.0
        cands.append(A)
    for _ in range(4000):
        na = int(rng.integers(1, 5))
        cands.append(rng.dirichlet(0.35 * np.ones(na), size=4))
    for A in cands:
        na = A.shape[1]
        PA = px[:, None, None] * A[:, :, None] * TY[:, None, :]
        HXA = _h(PA.sum(2).ravel()) - _h(PA.sum((0, 2)))
        HXAY = _h(PA.ravel()) - _h(PA.sum(0).ravel())
        tested += 1
        if HXAY < 1e-12 and HXA > 1e-12:
            viol += 1
    ok = not bY and not bZ and viol == 0
    say("A2 structure lemma (## M12 (T3b) row 2)", ok,
        f"non-confusable pairs Y={bY} Z={bZ}; counterexamples {viol}/{tested} "
        f"(15 deterministic + 4000 stochastic A)")


def a3_case_free_chain(px, TY, TZ, rng, draws=60):
    """N4 (D3).  Two claims: (i) (18i) <= I(W;Z)+I(V;Z|W)+I(X;Y|V,W) holds with NO
    case split on sign(I(W;Y)-I(W;Z)); (ii) that quantity equals
    I(X;Y) + I(Vt,Wt;Z) - I(Vh,Wh;Y) - [(19a)+(19c)]@const."""
    worst_ineq, worst_id, split_needed = -1e9, 0.0, 0
    for _ in range(draws):
        Kp, Kt, Kh = (rand_K(rng, 4, (2, 2, 2)) for _ in range(3))
        t = Thm7(px, Kp, Kt, Kh, TY, TZ, J_CONST)
        mid = t.WZ + t.VZ_W + t.XY_VW
        worst_ineq = max(worst_ineq, t.b18()["18i"] - mid)
        a, _, c = t.r19()
        rhs = t.IXY + (t.VtWtZ - t.VhWhY) - (a + c)
        worst_id = max(worst_id, abs(mid - rhs))
        if t.WY < t.WZ:                     # the branch M12 row 3 splits on
            split_needed += 1
    say("A3 case-free chain (N4 (D3))", worst_ineq <= 1e-13 and worst_id < 1e-13,
        f"max[(18i) - (I(W;Z)+I(V;Z|W)+I(X;Y|V,W))] = {worst_ineq:.2e} (<=0, no split; "
        f"{split_needed}/{draws} draws are in the 'wrong' branch of M12 row 3); "
        f"max identity residual = {worst_id:.2e}")


def a4_hinge(px, TY, TZ, rng, draws=60):
    """(20b)-lower at J = X is identically -H(X|Vh,Wh,Y); (20a)-lower is -H(X|Ut,Wt,Z)."""
    worst = 0.0
    for _ in range(draws):
        Kp, Kt, Kh = (rand_K(rng, 4, (2, 2, 2)) for _ in range(3))
        t = Thm7(px, Kp, Kt, Kh, TY, TZ, J_X)
        la, _, lb, _, _ = t.s20()
        worst = max(worst, abs(lb + t.HX_VhWhY), abs(la + t.HX_UtWtZ))
    say("A4 (20)-lower at J=X is an equality hinge", worst < 1e-13,
        f"max |lo(20b)@X + H(X|Vh,Wh,Y)|, |lo(20a)@X + H(X|Ut,Wt,Z)| = {worst:.2e}")


def a5_affine_in_mu(px, TY, TZ, rng, draws=40):
    """`## M11 (T3b)` row 4: every (19)/(20) residual is affine in mu => E_R(w) convex."""
    worst = 0.0
    for _ in range(draws):
        Kp, Kt, Kh = (rand_K(rng, 4, (2, 2, 2)) for _ in range(3))
        T1, T2 = J_rand(rng), J_rand(rng)
        for lam in (0.2, 0.5, 0.83):
            m = Thm7(px, Kp, Kt, Kh, TY, TZ, J_tag(T1, T2, lam))
            e1 = Thm7(px, Kp, Kt, Kh, TY, TZ, T1)
            e2 = Thm7(px, Kp, Kt, Kh, TY, TZ, T2)
            for f in ("r19", "s20"):
                for u, v, w in zip(getattr(m, f)(), getattr(e1, f)(), getattr(e2, f)()):
                    worst = max(worst, abs(u - lam * v - (1 - lam) * w))
            for k in ("18c", "18d", "18f", "18g", "18h"):
                # min{affine, affine} + affine: check the affine pieces separately
                pass
            for attr in ("WtJ", "WhJ", "UtJ_Wt", "UhJ_Wh", "VtJ_Wt", "VhJ_Wh",
                         "XJ", "XJ_UtWt", "XJ_VhWh"):
                worst = max(worst, abs(getattr(m, attr) - lam * getattr(e1, attr)
                                       - (1 - lam) * getattr(e2, attr)))
    say("A5 eligibility affine in mu (## M11 (T3b) row 4)", worst < 1e-13,
        f"max |residual(mix) - affine mix| = {worst:.2e} over {draws} draws x 3 lambdas")


def a6_witness_mixing(px, TY, TZ, rng, draws=25):
    """`## M11 (T3b)` row 5: time-sharing of witnesses is affine in the weight."""
    worst = 0.0
    for _ in range(draws):
        A = [rand_K(rng, 4, (2, 2, 2)) for _ in range(3)]
        B = [rand_K(rng, 4, (2, 2, 2)) for _ in range(3)]
        TJ = J_rand(rng)
        for mu in (0.3, 0.5, 0.7):
            m = Thm7(px, *[sys_tag(a, b, mu) for a, b in zip(A, B)], TY, TZ, TJ)
            e1 = Thm7(px, *A, TY, TZ, TJ)
            e2 = Thm7(px, *B, TY, TZ, TJ)
            for f in ("r19", "s20"):
                for u, v, w in zip(getattr(m, f)(), getattr(e1, f)(), getattr(e2, f)()):
                    worst = max(worst, abs(u - mu * v - (1 - mu) * w))
    say("A6 witness time-sharing affine (## M11 (T3b) row 5)", worst < 1e-13,
        f"max |residual(mix) - affine mix| = {worst:.2e} over {draws} draws x 3 weights")


def a7_uniform(px, TY, TZ, C, rng, draws=30):
    """`## M12 (T3b)` row 4: W = X, U = V = const is eligible for every J and (18i) = 2C."""
    K = det_K(4, lambda x: x, lambda x: 0, lambda x: 0, (4, 1, 1))
    b = Thm7(px, K, K, K, TY, TZ, J_CONST).b18()["18i"]
    worst = 0.0
    for _ in range(draws):
        for TJ in (J_CONST, J_X, J_rand(rng), J_rand(rng, nj=5)):
            t = Thm7(px, K, K, K, TY, TZ, TJ)
            a_, b_, c_ = t.r19()
            la, ha, lb, hbv, rc = t.s20()
            worst = max(worst, abs(a_), abs(b_), abs(c_), abs(rc),
                        max(0.0, -la), max(0.0, -ha), max(0.0, -lb), max(0.0, -hbv))
    say("A7 uniform witness attains (18i) = 2C (## M12 (T3b) row 4)",
        abs(b - 2 * C) < 1e-9 and worst < 1e-13,
        f"(18i) = {b:.7f} vs 2C = {2*C:.7f}; max eligibility violation over J = {worst:.2e}")


def a8_robustness(px, TY, TZ, C, SRC, rng, draws=40):
    """`## M12 (T3b)` row 8, the bound itself (not just an ingredient):
    a witness with (19a),(19c)@J1 and (20b)-lower@X obeys (18i) <= 2C + I(X;J1).
    Verified as the identity
      I(W;Z)+I(V;Z|W)+I(X;Y|V,W) = I(X;Y) + I(Vt,Wt;Z) - I(Vt,Wt;J1)
                                    + I(Vh,Wh;J1) - I(Vh,Wh;Y) - [(19a)+(19c)]@J1
    plus I(Vh,Wh;.) = I(X;.) when the hat determines X, plus DPI."""
    Kdet = det_K(4, lambda x: x // 2, lambda x: 0, lambda x: x % 2, (2, 1, 2))
    worst_id, worst_det, worst_bound, n = 0.0, 0.0, -1e9, 0
    for _ in range(draws):
        Kp, Kt = rand_K(rng, 4, (2, 2, 2)), rand_K(rng, 4, (2, 2, 2))
        TJ1 = J_rand(rng)
        t = Thm7(px, Kp, Kt, Kdet, TY, TZ, TJ1)
        a, _, c = t.r19()
        mid = t.WZ + t.VZ_W + t.XY_VW
        rhs = t.IXY + (t.VtWtZ - t.VtWtJ) + (t.VhWhJ - t.VhWhY) - (a + c)
        worst_id = max(worst_id, abs(mid - rhs))
        worst_det = max(worst_det, abs(t.HX_VhWh),
                        abs(t.VhWhY - t.IXY), abs(t.VhWhJ - t.XJ))
        # the bound as it would be applied: drop the residuals, use DPI
        bound = t.IXZ + t.XJ
        worst_bound = max(worst_bound, (mid + (a + c)) - (bound + 1e-15))
        n += 1
    # explicit calibration at three depolarisers, as M12 row 8 does
    cal = {}
    for lam in (0.10, 0.20, 0.35):
        TJ = lam * np.eye(4) + (1 - lam) * np.ones((4, 4)) / 4
        t = Thm7(px, Kdet, Kdet, Kdet, TY, TZ, TJ)
        cal[lam] = (t.XJ, 2 * C + t.XJ)
    ok = (worst_id < 1e-13 and worst_det < 1e-13 and worst_bound <= 1e-12
          and cal[0.10][1] < SRC < cal[0.20][1])
    say("A8 robustness bound (18i) <= 2C + I(X;J1) (## M12 (T3b) row 8)", ok,
        f"identity residual = {worst_id:.2e}; |I(Vh,Wh;.)-I(X;.)| = {worst_det:.2e}; "
        f"max[mid - (I(X;Z)+I(X;J1))] with (19)@J1 restored = {worst_bound:.2e}; "
        f"I(X;J1) = {cal[0.10][0]:.6f}/{cal[0.20][0]:.6f}/{cal[0.35][0]:.6f}, "
        f"bounds {cal[0.10][1]:.7f}/{cal[0.20][1]:.7f} vs SR_C = {SRC:.7f}")


def a9_weakened_nonvacuous(px, TY, TZ, C, SRC, rng, draws=400):
    """Is N4's weakened hypothesis ((19)@const + (20b)-lower@X, WITHOUT eligibility
    at J = const) non-vacuous?  Diagonal witnesses (plain = tilde = hat) satisfy
    (19)@const identically, so the family is rich; count how many of them fail full
    eligibility at J = const, and check they all obey (18i) <= 2C."""
    FUN = [lambda x: 0, lambda x: x // 2, lambda x: x % 2,
           lambda x: (x // 2) ^ (x % 2), lambda x: x]
    n_weak_only, n_weak, worst18i, tested = 0, 0, -1e9, 0
    pxs = [px] + [rng.dirichlet(np.ones(4) * 1.2) for _ in range(4)]
    cand = []
    for iw, iu, iv in itertools.product(range(5), repeat=3):
        cand.append(det_K(4, FUN[iw], FUN[iu], FUN[iv], (4, 4, 4)))
    for _ in range(draws):                       # stochastic witnesses too
        cand.append(rand_K(rng, 4, (3, 3, 3), conc=0.5))
    for q in pxs:
        for K in cand:
            tested += 1
            t0 = Thm7(q, K, K, K, TY, TZ, J_CONST)
            tX = Thm7(q, K, K, K, TY, TZ, J_X)
            a, b, c = t0.r19()
            if max(abs(a), abs(b), abs(c)) > 1e-11:
                continue
            if tX.s20()[2] < -1e-11:             # (20b)-lower @ J = X
                continue
            n_weak += 1
            la, ha, lb, hbv, rc = t0.s20()
            if min(la, ha, lb, hbv) < -1e-11 or abs(rc) > 1e-11:
                n_weak_only += 1
            worst18i = max(worst18i, t0.b18()["18i"])
    ok = n_weak_only > 0 and worst18i <= 2 * C + 1e-9 < SRC
    say("A9 weakened hypothesis is non-vacuous (N4 (D3))", ok,
        f"{n_weak}/{tested} witnesses satisfy the weakened hypothesis, of which "
        f"{n_weak_only} are NOT fully eligible at J = const; max (18i) among them = "
        f"{worst18i:.7f} <= 2C = {2*C:.7f} < SR_C = {SRC:.7f}")


def a10_segment_lemma_attack(rng, trials=200000):
    """Attack on N4 (D2)/(K1): search for a FINITE minimal cover of a simplex by
    sets cut out by non-strict affine constraints, one of whose members lies in a
    proper affine slice.  If (K1) is false such a family exists."""
    # Delta_3 in R^4, sampled on a dense grid + random interior points
    g = []
    step = 1 / 24
    for i in range(25):
        for j in range(25 - i):
            for k in range(25 - i - j):
                g.append([i * step, j * step, k * step, 1 - (i + j + k) * step])
    G = np.array(g)
    hits, found, pair_slice, pair_slice_other_full = 0, 0, 0, 0
    for _ in range(trials):
        k = int(rng.integers(2, 4))
        members, slice_flag = [], []
        for _i in range(k):
            n_eq = int(rng.integers(0, 2))
            n_in = int(rng.integers(1, 3))
            mask = np.ones(len(G), bool)
            proper = False
            for _e in range(n_eq):
                a = rng.normal(size=4)
                b = float(a @ G[rng.integers(len(G))])   # pass through a real point
                mask &= np.abs(G @ a - b) < 1e-12
                proper = True
            for _q in range(n_in):
                a = rng.normal(size=4)
                b = float(np.quantile(G @ a, rng.uniform(0.15, 1.0)))
                mask &= (G @ a <= b + 1e-12)
            members.append(mask)
            slice_flag.append(proper)
        cover = np.zeros(len(G), bool)
        for m in members:
            cover |= m
        if not cover.all():
            continue
        hits += 1
        if k == 2 and any(slice_flag):
            pair_slice += 1
            other = members[1] if slice_flag[0] else members[0]
            if other.all():
                pair_slice_other_full += 1
        # minimal?  no proper subfamily covers
        minimal = True
        for drop in range(k):
            c = np.zeros(len(G), bool)
            for i2, m in enumerate(members):
                if i2 != drop:
                    c |= m
            if c.all():
                minimal = False
                break
        if minimal and any(slice_flag):
            found += 1
    say("A10 no minimal finite affine cover has a proper-slice member (attack on (K1))",
        found == 0,
        f"{hits} covering families of size 2-3 found in {trials} trials; "
        f"minimal ones containing a proper affine slice: {found}; "
        f"2-covers with a proper slice: {pair_slice}, of which the other member is "
        f"already the whole simplex: {pair_slice_other_full}")


def a11_fat_member(px, TY, TZ, C, SRC, alpha=0.0776696701518):
    """Hand construction refuting the blanket clause of N4 (K3) ("every member of
    the covering family is thin").  W = const, U = (X1, X2 xor N2), V = (X2, X1 xor N1)
    with N1,N2 ~ Bern(alpha*) independent, and tilde = hat = plain (so the witness is
    (19)-uniform by construction).  It carries R* = (0, SR_C/2, SR_C/2), is eligible on
    a whole relative neighbourhood of mu_const, and is NOT eligible at mu_X."""
    K = np.zeros((4, 1, 4, 4))
    for x in range(4):
        x1, x2 = x // 2, x % 2
        for u1 in range(2):
            for u2 in range(2):
                pu = (1.0 if u1 == x1 else 0.0) * ((1 - alpha) if u2 == x2 else alpha)
                for v1 in range(2):
                    for v2 in range(2):
                        pv = (1.0 if v1 == x2 else 0.0) * \
                             ((1 - alpha) if v2 == x1 else alpha)
                        K[x, 0, 2 * u1 + u2, 2 * v1 + v2] = pu * pv
    t0 = Thm7(px, K, K, K, TY, TZ, J_CONST)
    tX = Thm7(px, K, K, K, TY, TZ, J_X)
    b0 = t0.b18()
    rng = np.random.default_rng(5)
    unif = max(max(abs(z) for z in Thm7(px, K, K, K, TY, TZ, J_rand(rng)).r19())
               for _ in range(20))
    nbhd, tot = 0, 0
    for _ in range(60):
        T1 = J_rand(rng)
        base = np.tile(T1.mean(0)[None, :], (4, 1))
        for lam in (0.03, 0.10):
            tt = Thm7(px, K, K, K, TY, TZ, lam * T1 + (1 - lam) * base)
            bb = tt.b18()
            tot += 1
            if (tt.eligible() and min(bb["18h"], bb["18i"]) >= SRC - 1e-9
                    and min(bb["18b"], bb["18e"]) >= SRC / 2):
                nbhd += 1
    ok = (abs(b0["18i"] - SRC) < 1e-9 and t0.eligible() and not tX.eligible()
          and unif < 1e-13 and min(t0.s20()[:4]) > 1e-3 and nbhd == tot)
    say("A11 an eligible set with non-empty interior exists at R* (refutes the "
        "blanket clause of (K3))", ok,
        f"(18i) = {b0['18i']:.12f} vs SR_C = {SRC:.12f}; eligible@const = "
        f"{t0.eligible()}, @J=X = {tX.eligible()}; (19) residual over 20 random J = "
        f"{unif:.1e} (uniform); (20) slacks @const = "
        f"{tuple(round(q, 5) for q in t0.s20()[:4])}; carries (0,SR_C/2,SR_C/2) on "
        f"{nbhd}/{tot} perturbations of mu_const")


def main():
    rng = np.random.default_rng(20260808)
    TY, TZ, eps = instance()
    px = np.ones(4) / 4
    a0_j_reduction(px, TY, TZ, rng)
    C, dstar, SRC = a1_numbers(TY, TZ, eps)
    a2_structure(TY, TZ)
    a3_case_free_chain(px, TY, TZ, rng)
    a4_hinge(px, TY, TZ, rng)
    a5_affine_in_mu(px, TY, TZ, rng)
    a6_witness_mixing(px, TY, TZ, rng)
    a7_uniform(px, TY, TZ, C, rng)
    a8_robustness(px, TY, TZ, C, SRC, rng)
    a9_weakened_nonvacuous(px, TY, TZ, C, SRC, rng)
    a10_segment_lemma_attack(rng)
    a11_fat_member(px, TY, TZ, C, SRC)
    bad = [t for t, ok in OUT if not ok]
    print("\n%d/%d checks passed" % (len(OUT) - len(bad), len(OUT)))
    if bad:
        print("FAILED: " + ", ".join(bad))
    raise SystemExit(1 if bad else 0)


if __name__ == "__main__":
    main()
