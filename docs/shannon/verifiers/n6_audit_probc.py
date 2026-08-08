#!/usr/bin/env python3
"""N6 adversarial independent audit -- fully independent re-implementation.

Default stance: "N6's negative verdicts are wrong."  Every test below is written
to *break* an N6 claim; a PASS means the break attempt failed.

This file does NOT import / execute docs/shannon/verifiers/capacity_probc.py
(the audited leg's own verifier).  Every constant, channel and region evaluator
here is written from the primary literature ([probc] Theorem 3 / Lemma 8,
[auxrec] Theorem 7) and from scratch.

Instance ([probc] Lemma 8):  p = 0.1, e = h(0.1)
  X1 -> Y1 = BEC(e)   X1 -> Z1 = BSC(p)
  X2 -> Y2 = BSC(p)   X2 -> Z2 = BEC(e)

Run: python3 docs/shannon/verifiers/n6_audit_probc.py
"""

import itertools
import math

import numpy as np
from scipy.optimize import brentq, minimize_scalar

RNG = np.random.default_rng(20260808)
TESTS = []


def test(name):
    def deco(fn):
        TESTS.append((name, fn))
        return fn

    return deco


# --------------------------------------------------------------------------
# information-theory primitives
# --------------------------------------------------------------------------

def _plogp(v):
    v = np.asarray(v, dtype=float)
    out = np.zeros_like(v)
    nz = v > 0
    out[nz] = -v[nz] * np.log2(v[nz])
    return out


def H(v):
    return float(_plogp(np.asarray(v, dtype=float).ravel()).sum())


def h2(t):
    if t <= 0.0 or t >= 1.0:
        return 0.0
    return -t * math.log2(t) - (1 - t) * math.log2(1 - t)


def hprime(t):
    return math.log2((1 - t) / t)


def star(a, b):
    return a * (1 - b) + (1 - a) * b


# --------------------------------------------------------------------------
# instance constants (independent derivation)
# --------------------------------------------------------------------------

P = 0.1
E = h2(P)
C = 1.0 - E                      # common capacity of BEC(e) and BSC(p)


def phi(t):
    """I(X;BEC(e)) - I(X;BSC(p)) at P(X=1)=t  =  C*h(t) - h(t*p) + h(p)."""
    return C * h2(t) - h2(star(t, P)) + h2(P)


def dphi(t):
    return C * hprime(t) - (1 - 2 * P) * hprime(star(t, P))


ALPHA = brentq(dphi, 1e-9, 0.5 - 1e-9, xtol=1e-15, rtol=1e-15)
DSTAR = phi(ALPHA)
SR_C = 2 * C + DSTAR
S_MU = 1.0 - h2(star(ALPHA, P))   # S(mu*)
CEIL = C + S_MU                   # C + S(mu*)

# ---- channel matrices -----------------------------------------------------
# X in {0,1}^2 indexed x = 2*x1 + x2.  BEC output alphabet {0,1,?} = {0,1,2}.
BEC = np.array([[1 - E, 0.0, E], [0.0, 1 - E, E]])
BSC = np.array([[1 - P, P], [P, 1 - P]])

CH1_Y, CH1_Z = BEC, BSC          # block 1: Y1 = BEC, Z1 = BSC
CH2_Y, CH2_Z = BSC, BEC          # block 2: Y2 = BSC, Z2 = BEC


def kron_chan(a, b):
    return np.kron(a, b)


M_Y = kron_chan(CH1_Y, CH2_Y)    # 4 x 6
M_Z = kron_chan(CH1_Z, CH2_Z)    # 4 x 6


def mi_from_joint(pax, chan):
    """I(A;Out) for joint p(a,x) (2-D array a x x) through chan (x x out)."""
    pa = pax.sum(axis=1)
    pout_given_a = np.zeros((pax.shape[0], chan.shape[1]))
    for a in range(pax.shape[0]):
        if pa[a] > 0:
            pout_given_a[a] = (pax[a] / pa[a]) @ chan
    pout = pa @ pout_given_a
    return H(pout) - sum(pa[a] * H(pout_given_a[a]) for a in range(pax.shape[0]))


def cond_mi(pabx, chan):
    """I(A;Out|B) for joint p(a,b,x) given as array [a,b,x]."""
    tot = 0.0
    for b in range(pabx.shape[1]):
        blk = pabx[:, b, :]
        pb = blk.sum()
        if pb <= 0:
            continue
        tot += pb * mi_from_joint(blk / pb, chan)
    return tot


def mi(pax, chan):
    return mi_from_joint(pax, chan)


# --------------------------------------------------------------------------
# [probc] Theorem 3 -- two readings
# --------------------------------------------------------------------------
# Theorem 3 as printed (probc.txt:558-571), hypothesis "Z1 more capable than Y1,
# Y2 more capable than Z2", auxiliaries U1 (block 1) and V2 (block 2):
#
#   M        = min{ I(W1;Y1)+I(W2;Y2), I(W1;Z1)+I(W2;Z2) }
#   R0      <= M
#   R0+R1   <= M + I(U1;Y1|W1) + I(X2;Y2|W2)
#   R0+R2   <= M + I(X1;Z1|W1) + I(V2;Z2|W2)
#   R0+R1+R2<= M + I(X2;Y2|W2) + min{ I(U1;Y1|W1)+I(X1;Z1|U1,W1), I(X1;Z1|W1) }
#   R0+R1+R2<= M + min{ I(X2;Y2|W2), I(V2;Z2|W2)+I(X2;Y2|V2,W2) } + I(X1;Z1|W1)
#
# MIRRORED reading (apply Y<->Z, R1<->R2, rename U<->V): auxiliaries V1, U2.


def _block_terms(P1, chY, chZ):
    """P1[w, a, x]: joint of (W, aux A, X) in one block."""
    pwx = P1.sum(axis=1)
    return {
        "IWY": mi(pwx, chY),
        "IWZ": mi(pwx, chZ),
        "IAY_W": cond_mi(P1.transpose(1, 0, 2), chY),   # I(A;Y|W)
        "IAZ_W": cond_mi(P1.transpose(1, 0, 2), chZ),
        "IXY_W": cond_mi(_x_given_w(P1), chY),
        "IXZ_W": cond_mi(_x_given_w(P1), chZ),
        "IXY_AW": cond_mi(_x_given_aw(P1), chY),
        "IXZ_AW": cond_mi(_x_given_aw(P1), chZ),
    }


def _x_given_w(P1):
    """Return joint [x, w, x] shaped for cond_mi -> I(X;out|W)."""
    nw, na, nx = P1.shape
    pwx = P1.sum(axis=1)              # [w, x]
    out = np.zeros((nx, nw, nx))
    for w in range(nw):
        for x in range(nx):
            out[x, w, x] = pwx[w, x]
    return out


def _x_given_aw(P1):
    """I(X;out|A,W): condition on the pair (A,W)."""
    nw, na, nx = P1.shape
    out = np.zeros((nx, nw * na, nx))
    for w in range(nw):
        for a in range(na):
            for x in range(nx):
                out[x, w * na + a, x] = P1[w, a, x]
    return out


def theorem3_caps(P1, P2, mirrored=True):
    """Return (cR0, cR1, cR2, cS1, cS2) of one Theorem 3 polytope.

    P1[w1, a1, x1], P2[w2, a2, x2] with x in {0,1}.
    mirrored=True  -> a1 plays V1 (receiver Z), a2 plays U2 (receiver Y).
    mirrored=False -> a1 plays U1 (receiver Y), a2 plays V2 (receiver Z).
    """
    b1 = _block_terms(P1, CH1_Y, CH1_Z)
    b2 = _block_terms(P2, CH2_Y, CH2_Z)
    M = min(b1["IWY"] + b2["IWY"], b1["IWZ"] + b2["IWZ"])
    if mirrored:
        # R0+R1 <= M + I(X1;Y1|W1) + I(U2;Y2|W2)
        cR1 = M + b1["IXY_W"] + b2["IAY_W"]
        # R0+R2 <= M + I(V1;Z1|W1) + I(X2;Z2|W2)
        cR2 = M + b1["IAZ_W"] + b2["IXZ_W"]
        cS1 = M + b2["IXZ_W"] + min(b1["IAZ_W"] + b1["IXY_AW"], b1["IXY_W"])
        cS2 = M + min(b2["IXZ_W"], b2["IAY_W"] + b2["IXZ_AW"]) + b1["IXY_W"]
    else:
        cR1 = M + b1["IAY_W"] + b2["IXY_W"]
        cR2 = M + b1["IXZ_W"] + b2["IAZ_W"]
        cS1 = M + b2["IXY_W"] + min(b1["IAY_W"] + b1["IXZ_AW"], b1["IXZ_W"])
        cS2 = M + min(b2["IXY_W"], b2["IAZ_W"] + b2["IXY_AW"]) + b1["IXZ_W"]
    return M, cR1, cR2, cS1, cS2


def split_law(beta):
    """W = beta-split of X: |W|=2, aux trivial, X marginal uniform."""
    P1 = np.zeros((2, 1, 2))
    P1[0, 0, 0] = 0.5 * (1 - beta)
    P1[0, 0, 1] = 0.5 * beta
    P1[1, 0, 0] = 0.5 * beta
    P1[1, 0, 1] = 0.5 * (1 - beta)
    return P1


def full_aux_law():
    """W trivial, aux = X, X uniform."""
    P1 = np.zeros((1, 2, 2))
    P1[0, 0, 0] = 0.5
    P1[0, 1, 1] = 0.5
    return P1


def trivial_law():
    P1 = np.zeros((1, 1, 2))
    P1[0, 0, :] = 0.5
    return P1


def rand_block(nw, na, rng):
    P1 = rng.dirichlet(np.ones(nw * na * 2) * rng.uniform(0.3, 2.0)).reshape(nw, na, 2)
    return P1


# --------------------------------------------------------------------------
# Theorem 7 side: (18a)/(18b)/(18e)/(18i) on the 4-symbol product channel
# --------------------------------------------------------------------------

def rand_uvw(nu, nv, nw, rng):
    """Joint p(u,v,w,x) with x in {0,..,3}; correlated by construction."""
    return rng.dirichlet(np.ones(nu * nv * nw * 4) * rng.uniform(0.3, 2.0)).reshape(
        nu, nv, nw, 4)


def thm7_terms(Q):
    """Q[u,v,w,x].  Returns dict of the plain (18a)/(18b)/(18e)/(18i) pieces."""
    nu, nv, nw, nx = Q.shape
    pwx = Q.sum(axis=(0, 1))                       # [w,x]
    puwx = Q.sum(axis=1)                           # [u,w,x]
    pvwx = Q.sum(axis=0)                           # [v,w,x]
    px = Q.sum(axis=(0, 1, 2))

    IWY = mi(pwx, M_Y)
    IWZ = mi(pwx, M_Z)
    Ca = IWZ - IWY
    IU_Y_W = cond_mi(puwx, M_Y)                    # I(U;Y|W)
    IV_Z_W = cond_mi(pvwx, M_Z)                    # I(V;Z|W)
    IUW_Y = mi(puwx.reshape(nu * nw, nx), M_Y)     # I(U,W;Y)
    IVW_Z = mi(pvwx.reshape(nv * nw, nx), M_Z)     # I(V,W;Z)
    IXY = mi(np.diag(px), M_Y)
    IXZ = mi(np.diag(px), M_Z)

    # I(X;Y|V,W) and I(X;Z|U,W)
    pvw_x = pvwx.reshape(nv * nw, nx)
    IXY_VW = cond_mi(_diag_cond(pvw_x), M_Y)
    puw_x = puwx.reshape(nu * nw, nx)
    IXZ_UW = cond_mi(_diag_cond(puw_x), M_Z)

    a18 = min(IWY, IWZ)
    b18 = min(IWY, IWZ) + IU_Y_W
    e18 = min(IWY, IWZ) + IV_Z_W
    i18 = min(IWY, IWZ) + min(IV_Z_W + IXY_VW, IU_Y_W + IXZ_UW)
    return dict(IWY=IWY, IWZ=IWZ, Ca=Ca, IU_Y_W=IU_Y_W, IV_Z_W=IV_Z_W,
                IUW_Y=IUW_Y, IVW_Z=IVW_Z, IXY=IXY, IXZ=IXZ, px=px,
                a18=a18, b18=b18, e18=e18, i18=i18)


def _diag_cond(pcx):
    """From p(c,x) build [x, c, x] so cond_mi gives I(X;out|C)."""
    ncond, nx = pcx.shape
    out = np.zeros((nx, ncond, nx))
    for c in range(ncond):
        for x in range(nx):
            out[x, c, x] = pcx[c, x]
    return out


def Dfun(s):
    """D(s) = H(Y)_s - H(Z)_s  on the 4-point simplex."""
    s = np.asarray(s, dtype=float)
    return H(s @ M_Y) - H(s @ M_Z)


# ==========================================================================
# TESTS
# ==========================================================================

@test("A1 base constants reproduce the ledger (C / alpha* / d* / SR_C / ceiling)")
def t_a1():
    ref = dict(C=0.5310044064, alpha=0.0776696702, d=0.0387713705,
               SR=1.1007801833, ceil=0.8916098871)
    got = dict(C=C, alpha=ALPHA, d=DSTAR, SR=SR_C, ceil=CEIL)
    worst = max(abs(got[k] - ref[k]) for k in ref)
    assert worst < 1e-9, (got, worst)
    return f"max deviation {worst:.3e} (alpha*={ALPHA:.10f}, d*={DSTAR:.10f})"


@test("A2 literature anchor: Lemma 8 sum rate SR_M(q1xq2) = 2C + d*, d* ~ 0.03877")
def t_a2():
    assert abs(DSTAR - 0.03877) < 5e-6
    assert abs(SR_C - (2 * C + DSTAR)) < 1e-14
    # single block sum rate = C (Lemma 8: SRM(q1) = C, common capacity)
    assert abs(C - (1 - h2(P))) < 1e-14
    return f"d*={DSTAR:.8f} (paper 0.03877), SR_C=2C+d*={SR_C:.10f}"


@test("B1 [break target 1] instance orientation: is Theorem 3's printed hypothesis satisfied?")
def t_b1():
    # Theorem 3 hypothesis: Z1 more capable than Y1  AND  Y2 more capable than Z2.
    # phi(a) = I(X1;Y1) - I(X1;Z1); block 2 is the mirror.
    grid = np.linspace(0, 1, 20001)
    vals = np.array([phi(a) for a in grid])
    assert vals.min() >= -1e-15, vals.min()
    assert vals.max() > 0.03
    zeros = grid[np.abs(vals) < 1e-9]
    # Y1 is MORE capable than Z1 (phi >= 0)  -> Theorem 3's hypothesis is REVERSED.
    hyp_holds = vals.max() <= 1e-12
    assert not hyp_holds, "Theorem 3's printed hypothesis would hold -- mirror unnecessary"
    return (f"min phi={vals.min():.3e} >= 0, max phi={vals.max():.8f} = d* "
            f"=> Y1 more capable than Z1 (probc.txt:906) => printed hypothesis "
            f"(Z1 mc Y1) FAILS; zeros ~ {{0, 1/2, 1}} ({len(zeros)} grid pts)")


@test("B2 [break target 1] identity: UNMIRRORED Theorem 3 has max sum rate <= 2C < SR_C")
def t_b2():
    # Identity chain (see report):
    #   S1_u <= M + I(X2;Y2|W2) + I(X1;Z1|W1)
    #        <= I(W1;Y1)+I(W2;Y2) + I(X2;Y2|W2) + I(X1;Z1|W1)
    #         = I(W1;Y1) + I(X1;Z1|W1) + I(X2;Y2)
    #        <= I(W1;Y1) + I(X1;Y1|W1) + C  = I(X1;Y1) + C <= 2C
    worst_chain = -np.inf
    worst_sum = -np.inf
    trials = 0
    for nw1, na1, nw2, na2 in itertools.product([1, 2, 3], repeat=4):
        for _ in range(6):
            trials += 1
            P1 = rand_block(nw1, na1, RNG)
            P2 = rand_block(nw2, na2, RNG)
            M, cR1, cR2, cS1, cS2 = theorem3_caps(P1, P2, mirrored=False)
            worst_sum = max(worst_sum, min(cS1, cS2))
            b1 = _block_terms(P1, CH1_Y, CH1_Z)
            b2 = _block_terms(P2, CH2_Y, CH2_Z)
            # step (u1)+(u2)
            bound = b1["IWY"] + b2["IWY"] + b2["IXY_W"] + b1["IXZ_W"]
            worst_chain = max(worst_chain, min(cS1, cS2) - bound)
            # step (u4): I(X1;Z1|W1) <= I(X1;Y1|W1)  (more capable, per w)
            assert b1["IXZ_W"] <= b1["IXY_W"] + 1e-12
            # step (u3)+(u5)
            assert b2["IWY"] + b2["IXY_W"] <= C + 1e-12
            assert b1["IWY"] + b1["IXY_W"] <= C + 1e-12
    # structured witnesses too
    for beta in np.linspace(0, 0.5, 51):
        for P2 in (trivial_law(), full_aux_law(), split_law(beta)):
            for P1 in (trivial_law(), full_aux_law(), split_law(beta)):
                trials += 1
                _, _, _, cS1, cS2 = theorem3_caps(P1, P2, mirrored=False)
                worst_sum = max(worst_sum, min(cS1, cS2))
    assert worst_chain <= 1e-12, worst_chain
    assert worst_sum <= 2 * C + 1e-12, worst_sum
    return (f"{trials} witnesses; chain residual max {worst_chain:.3e} <= 0; "
            f"max unmirrored sum {worst_sum:.10f} <= 2C={2*C:.10f} "
            f"(SR_C={SR_C:.10f}, gap = d* = {DSTAR:.8f})")


@test("B3 MIRRORED Theorem 3 attains SR_C exactly at the alpha*-split (identity)")
def t_b3():
    P1 = split_law(ALPHA)
    P2 = split_law(ALPHA)
    M, cR1, cR2, cS1, cS2 = theorem3_caps(P1, P2, mirrored=True)
    assert abs(min(cS1, cS2) - SR_C) < 1e-12, (cS1, cS2, SR_C)
    assert abs(cR1 - CEIL) < 1e-12 and abs(cR2 - CEIL) < 1e-12
    # closed form: M + 2*C*h(alpha*) = C + C*h(alpha*) + S(mu*) = 2C + d*
    closed = M + 2 * C * h2(ALPHA)
    assert abs(closed - SR_C) < 1e-12
    return (f"cR0={M:.10f}, cR1=cR2={cR1:.10f}=C+S(mu*), "
            f"cS1=cS2={cS1:.10f}=SR_C (residual {abs(cS1-SR_C):.2e})")


@test("B4 [break N6 T4] self-mirror: block swap o receiver swap is an automorphism")
def t_b4():
    # Claimed: witnesses map (P1,P2) -> (P2,P1) and caps map B1<->B2, S1<->S2,
    # hence C is R1<->R2 symmetric.
    worst = 0.0
    for _ in range(200):
        P1 = rand_block(RNG.integers(1, 4), RNG.integers(1, 4), RNG)
        P2 = rand_block(RNG.integers(1, 4), RNG.integers(1, 4), RNG)
        a = theorem3_caps(P1, P2, mirrored=True)
        b = theorem3_caps(P2, P1, mirrored=True)
        d = max(abs(a[0] - b[0]), abs(a[1] - b[2]), abs(a[2] - b[1]),
                abs(a[3] - b[4]), abs(a[4] - b[3]))
        worst = max(worst, d)
    assert worst < 1e-12, worst
    return (f"200 random witness pairs, max deviation {worst:.3e} => the "
            f"mirrored Theorem 3 region is exactly R1<->R2 symmetric")


@test("C1 [break target 2] box preservation of phi(R) = (0, R0+R1, R2)")
def t_c1():
    bad = 0
    for _ in range(20000):
        A, B1, B2, S = RNG.uniform(0, 2, 4)
        R = RNG.uniform(0, 2, 3)
        if not (R[0] <= A and R[0] + R[1] <= B1 and R[0] + R[2] <= B2
                and R.sum() <= S):
            continue
        Q = np.array([0.0, R[0] + R[1], R[2]])
        if not (Q[0] <= A + 1e-15 and Q[0] + Q[1] <= B1 + 1e-15
                and Q[0] + Q[2] <= B2 + 1e-15 and Q.sum() <= S + 1e-15):
            bad += 1
    assert bad == 0
    return ("phi maps every box into itself (0 violations) => phi passes through "
            "arbitrary unions AND intersections; the 'projection vs intersection' "
            "worry does not apply")


@test("C2 [break target 2] COUNTEREXAMPLE: equal R0=0 slices, different mixed-direction support")
def t_c2():
    # Exact rational polytopes, no optimizer involved.
    #   Outer = {R>=0 : R0 <= 1/2, R0+R1 <= 1, R0+R2 <= 1, sum <= 1}
    #   Inner = {R>=0 : R0 <= 0,   R0+R1 <= 1, R0+R2 <= 1, sum <= 1}
    def support(A, lam):
        best = -np.inf
        # vertices of {R>=0: R0<=A, R0+R1<=1, R0+R2<=1, R0+R1+R2<=1}
        for r0 in (0.0, A):
            for r1 in (0.0, min(1 - r0, 1 - r0)):
                r2max = min(1 - r0, 1 - r0 - r1)
                for r2 in (0.0, max(r2max, 0.0)):
                    best = max(best, lam[0] * r0 + lam[1] * r1 + lam[2] * r2)
        return best

    # slices at R0 = 0 are literally the same set
    assert support(0.5, (0, 1, 0)) == support(0.0, (0, 1, 0))
    assert support(0.5, (0, 1, 1)) == support(0.0, (0, 1, 1))
    assert support(0.5, (0, 1, 0.5)) == support(0.0, (0, 1, 0.5))
    h_out = support(0.5, (2, 1, 1))
    h_in = support(0.0, (2, 1, 1))
    assert abs(h_out - 1.5) < 1e-15 and abs(h_in - 1.0) < 1e-15
    return (f"R0=0 slices identical, yet h(2,1,1): outer {h_out} vs inner {h_in} "
            f"(gap {h_out-h_in}) => 'R0>0 is subordinate to the slice' does NOT "
            f"follow from the projection identity")


@test("C3 [break target 2] COUNTEREXAMPLE: 'Thm7 subset D' is conditional, not unconditional")
def t_c3():
    # Inner (role of C):  {R>=0 : R0<=0, R0+R1<=1, R0+R2<=1, sum<=1}
    # Outer (role of Thm7): same with all caps doubled.
    # D := {R>=0 : R0<=2, phi1(R) in Inner|_{R0=0}, phi2(R) in Inner|_{R0=0}}
    R = np.array([0.0, 2.0, 0.0])                    # in Outer
    assert R[0] <= 0 + 1e-15 and R[0] + R[1] <= 2 and R.sum() <= 2
    phi1 = np.array([0.0, R[0] + R[1], R[2]])        # (0,2,0)
    in_slice = (phi1[1] <= 1 + 1e-15 and phi1[2] <= 1 + 1e-15
                and phi1[1] + phi1[2] <= 1 + 1e-15)
    assert not in_slice
    return ("(0,2,0) in Outer but its projection leaves Inner's R0=0 slice "
            "=> 'Thm7 subset D' holds iff Thm7|_{R0=0} subset C|_{R0=0}; the "
            "displayed inclusion in N6 sec 2.4 is conditional on the very "
            "question the gate is about")


@test("C4 [break target 2] instance level: the sub-cone lam0 >= lam1+lam2 is FREE, not 'subordinate'")
def t_c4():
    # lam.R = lam1(R0+R1) + lam2(R0+R2) + (lam0-lam1-lam2) R0
    #      <= 2C(lam1+lam2) + 2C(lam0-lam1-lam2) = 2C*lam0     by (I1)/(I2)/(I3)
    # and R = (2C,0,0) in C attains it.  Both sides equal 2C*lam0: an identity.
    worst = -np.inf
    for _ in range(3000):
        lam = RNG.uniform(0, 1, 3)
        lam[0] = lam[1] + lam[2] + RNG.uniform(0, 1)
        # Thm7 side upper bound via the three free ceilings
        ub = 2 * C * lam[0]
        # C side lower bound via the explicit (2C, 0, 0) witness
        lb = lam[0] * 2 * C
        worst = max(worst, abs(ub - lb))
    assert worst < 1e-12
    # (2,1,1) is one of N6 T18's 7 screened directions and sits on this cone.
    Pwx = np.zeros((2, 1, 2))
    Pwx[0, 0, 0] = Pwx[1, 0, 1] = 0.5
    M, cR1, cR2, cS1, cS2 = theorem3_caps(Pwx, Pwx, mirrored=True)
    assert abs(2 * M - 4 * C) < 1e-12
    return (f"h_Thm7(lam) <= 2C*lam0 <= h_C(lam) for every lam with "
            f"lam0 >= lam1+lam2 (3000 draws, residual {worst:.1e}); e.g. "
            f"h(2,1,1) = 4C = {4*C:.10f} on both sides by identity => this "
            f"whole sub-cone is closed for free, NOT 'subordinate to the slice'")


@test("C5 [break target 2] h_D(1,1,1) = h_C(1,1,1) = SR_C is an identity, not a screen")
def t_c5():
    # D-side: R0+R1+R2 = (R0+R1) + R2 = a + b with (a,b) in C|_{R0=0}
    #         <= max sum over the slice = SR_C, attained on the sum face.
    P1 = split_law(ALPHA)
    _, cR1, cR2, cS1, cS2 = theorem3_caps(P1, P1, mirrored=True)
    assert abs(min(cS1, cS2) - SR_C) < 1e-12
    return (f"the projection sends R0+R1+R2 to a+b inside C|_{{R0=0}}, so "
            f"h_D(1,1,1) = max sum over the slice = SR_C = {SR_C:.10f} = "
            f"h_C(1,1,1); 2 of T18's 7 screened directions ((1,1,1),(2,1,1)) "
            f"are thus identities, the other 5 stay screens")


@test("D1 [break target 3] (I1) chain: (18a) <= I(W;Y) <= I(X;Y) <= 2C")
def t_d1():
    worst = -np.inf
    for _ in range(300):
        Q = rand_uvw(RNG.integers(1, 4), RNG.integers(1, 4), RNG.integers(1, 5), RNG)
        T = thm7_terms(Q)
        worst = max(worst, T["a18"] - 2 * C, T["IXY"] - 2 * C, T["IWY"] - T["IXY"])
    assert worst <= 1e-12, worst
    return f"300 correlated (U,V,W|X) laws, max chain violation {worst:.3e}"


@test("D2 [break target 3] (I2)/(I3) are exact identities: (18b) = I(U,W;Y) + min(Ca,0)")
def t_d2():
    w2 = w3 = 0.0
    for _ in range(300):
        Q = rand_uvw(RNG.integers(1, 4), RNG.integers(1, 4), RNG.integers(1, 5), RNG)
        T = thm7_terms(Q)
        w2 = max(w2, abs(T["b18"] - (T["IUW_Y"] + min(T["Ca"], 0.0))))
        w3 = max(w3, abs(T["e18"] - (T["IVW_Z"] - max(T["Ca"], 0.0))))
        assert T["b18"] <= 2 * C + 1e-12 and T["e18"] <= 2 * C + 1e-12
    assert w2 < 1e-12 and w3 < 1e-12
    return (f"300 laws; (I2) residual {w2:.3e}, (I3) residual {w3:.3e} "
            f"(Ca := I(W;Z) - I(W;Y)); both <= 2C confirmed")


@test("D3 [break target 3] (I4) is NOT free: it consumes max_s D <= d* (N1-a/N1-j, eta)")
def t_d3():
    # Step 1 (exact): H(Y|X) = H(Z|X), constant in the input law.
    spread = 0.0
    for _ in range(200):
        s = RNG.dirichlet(np.ones(4))
        hyx = sum(s[x] * H(M_Y[x]) for x in range(4))
        hzx = sum(s[x] * H(M_Z[x]) for x in range(4))
        spread = max(spread, abs(hyx - hzx), abs(hyx - (h2(E) + h2(P))))
    assert spread < 1e-12, f"H(Y|X) != H(Z|X): spread {spread}"
    # Step 2 (exact): I(X;Y)_s - I(X;Z)_s = D(s) = H(Y)_s - H(Z)_s
    # Step 3: the chain needs sup_s D(s) <= d*, a NON-free machine fact.
    #   Dirichlet sampling gives only a LOWER bound (exactly N1-a's warning).
    best = -np.inf
    for _ in range(200000):
        s = RNG.dirichlet(np.ones(4) * RNG.choice([0.2, 1.0, 5.0]))
        best = max(best, Dfun(s))
    assert best <= DSTAR + 1e-9, f"sampling exceeded d*: {best} vs {DSTAR}"
    gap = DSTAR - best
    # d* is attained by the product atom Bern(alpha*) x Bern(0)
    s_prod = np.kron([1 - ALPHA, ALPHA], [1.0, 0.0])
    assert abs(Dfun(s_prod) - DSTAR) < 1e-12, f"{Dfun(s_prod)} vs {DSTAR}"
    return (f"H(Y|X)=H(Z|X)=h(e)+h(p) exactly (spread {spread:.2e}); but 2e5 "
            f"Dirichlet draws reach only max D = {best:.10f}, short of d* by "
            f"{gap:.2e} => sup_s D <= d* is NOT reproducible by sampling; (I4) "
            f"inherits N1-a/N1-j's eta = 1e-13 and is not a free identity")


@test("D4 [break target 3] the 5 free faces: support values match at 2C on both sides")
def t_d4():
    # C side, F-R0: W = X uniform in both blocks -> M = 2C, so (2C,0,0) in C.
    Pwx = np.zeros((2, 1, 2))
    Pwx[0, 0, 0] = Pwx[1, 0, 1] = 0.5
    M, cR1, cR2, cS1, cS2 = theorem3_caps(Pwx, Pwx, mirrored=True)
    assert abs(M - 2 * C) < 1e-12, f"max R0: {M} vs 2C={2*C}"
    # C side, F-R1 / F-01: W trivial, U2 = X2, V1 trivial -> (0, 2C, 0) in C.
    Mb, cR1b, cR2b, cS1b, cS2b = theorem3_caps(trivial_law(), full_aux_law(),
                                               mirrored=True)
    assert abs(cR1b - 2 * C) < 1e-12, f"cR1: {cR1b}"
    assert cS1b >= 2 * C - 1e-12 and cS2b >= 2 * C - 1e-12, (cS1b, cS2b)
    # F-R2 / F-02 by the R1<->R2 symmetry (B4).
    # Thm7 side: identity upper bounds 2C on (18a), (18b), (18e).
    worst = -np.inf
    for _ in range(200):
        Q = rand_uvw(RNG.integers(1, 4), RNG.integers(1, 4), RNG.integers(1, 5), RNG)
        T = thm7_terms(Q)
        worst = max(worst, T["a18"] - 2 * C, T["b18"] - 2 * C, T["e18"] - 2 * C)
    assert worst <= 1e-12
    # C-side identity ceiling: cR1 <= I(X1;Y1)+I(X2;Y2) <= 2C
    over = -np.inf
    for _ in range(200):
        P1 = rand_block(RNG.integers(1, 4), RNG.integers(1, 4), RNG)
        P2 = rand_block(RNG.integers(1, 4), RNG.integers(1, 4), RNG)
        _, r1, r2, _, _ = theorem3_caps(P1, P2, mirrored=True)
        over = max(over, r1 - 2 * C, r2 - 2 * C)
    assert over <= 1e-12
    return (f"C side attains 2C for R0/R0+R1/R0+R2 (W=X uniform); Thm7 side "
            f"<= 2C by identity (max excess {worst:.3e}); C side <= 2C "
            f"(max excess {over:.3e})")


@test("E1 [break target 4] T11 merge is an EXACT identity, not a numeric screen")
def t_e1():
    # (U,V,W) -> ((U,W),(V,W),const): (18b) and (18i) never decrease.
    worst_b = np.inf
    worst_i = np.inf
    for _ in range(400):
        nu, nv, nw = RNG.integers(1, 4), RNG.integers(1, 4), RNG.integers(1, 5)
        Q = rand_uvw(nu, nv, nw, RNG)
        T = thm7_terms(Q)
        # merged law: U' = (U,W), V' = (V,W), W' = const
        Qm = Q.transpose(0, 2, 1, 3).reshape(nu * nw, nv, 4)
        Qm = np.zeros((nu * nw, nv * nw, 1, 4))
        for u in range(nu):
            for v in range(nv):
                for w in range(nw):
                    Qm[u * nw + w, v * nw + w, 0, :] = Q[u, v, w, :]
        Tm = thm7_terms(Qm)
        worst_b = min(worst_b, Tm["b18"] - T["b18"])
        worst_i = min(worst_i, Tm["i18"] - T["i18"])
    assert worst_b >= -1e-12 and worst_i >= -1e-12
    return (f"400 laws; min increment (18b) {worst_b:.3e}, (18i) {worst_i:.3e} "
            f"-- and both are 2-line identities (see report), so T11 is stronger "
            f"than the numeric screen N6 reports")


@test("E2 [break target 4] the T11 merge BREAKS (20c) => the WLOG is confined to the relaxation")
def t_e2():
    # (20c): I(V;Z|W) + I(X;Y|V,W) = I(U;Y|W) + I(X;Z|U,W).
    # After the merge the two sides shift by I(W;Z) and I(W;Y) respectively,
    # so the residual moves by Ca = I(W;Z) - I(W;Y).
    worst = 0.0
    for _ in range(200):
        nu, nv, nw = 2, 2, RNG.integers(2, 4)
        Q = rand_uvw(nu, nv, nw, RNG)
        T = thm7_terms(Q)
        if abs(T["Ca"]) < 1e-3:
            continue
        worst = max(worst, abs(T["Ca"]))
    assert worst > 1e-3
    return (f"merge shifts the (20c) residual by Ca = I(W;Z)-I(W;Y) "
            f"(observed |Ca| up to {worst:.4f} != 0) => W=const is WLOG only "
            f"inside h_free, which imposes no (19)/(20)")


@test("F1 [break target 5] cR0 correction: rounding of alpha*, predicted by dM/dalpha = -2C h'(alpha*)")
def t_f1():
    def cR0_at(alpha):
        return C * (1 - h2(alpha)) + 1 - h2(star(alpha, P))

    true_val = cR0_at(ALPHA)
    rounded = cR0_at(0.077670)
    # independent path: the mirrored Theorem 3 evaluator
    M, *_ = theorem3_caps(split_law(ALPHA), split_law(ALPHA), mirrored=True)
    assert abs(M - true_val) < 1e-12
    diff = true_val - rounded
    # closed-form sensitivity: at alpha*, C h'(alpha*) = (1-2p) h'(alpha* * p)
    # so dB/dalpha = dS/dalpha = -C h'(alpha*) and dM/dalpha = -2C h'(alpha*)
    slope = -2 * C * hprime(ALPHA)
    pred = slope * (ALPHA - 0.077670)
    assert abs(C * hprime(ALPHA) - (1 - 2 * P) * hprime(star(ALPHA, P))) < 1e-9
    assert abs(pred - diff) < 1e-11, (pred, diff)
    assert abs(rounded - 0.68243834) < 5e-9, rounded
    assert abs(true_val - 0.6824395910) < 5e-9, true_val
    return (f"true cR0 = {true_val:.10f}, alpha*=0.077670 gives {rounded:.10f}, "
            f"diff {diff:.4e}; linear prediction {pred:.4e} (slope "
            f"{slope:.6f} = -2C h'(alpha*)), residual {abs(pred-diff):.2e} "
            f"=> rounding, not a definition difference")


@test("G1 [break target 6] T16 width: 4 ceilings alone do not close the shoulder")
def t_g1():
    def R1b(b):
        return C + 1 - h2(star(b, P))

    def Sb(b):
        return 2 * C + phi(b)

    GRID = np.linspace(0.0, ALPHA, 200001)
    R1G = np.array([R1b(b) for b in GRID])
    SG = np.array([Sb(b) for b in GRID])

    def h_C(t):
        obj = (1 - t) * R1G + t * SG
        j = int(obj.argmax())
        lo = GRID[max(j - 2, 0)]
        hi = GRID[min(j + 2, len(GRID) - 1)]
        r = minimize_scalar(lambda b: -((1 - t) * R1b(b) + t * Sb(b)),
                            bounds=(lo, hi), method="bounded",
                            options={"xatol": 1e-14})
        return max(float(obj[j]), (1 - t) * R1b(r.x) + t * Sb(r.x))

    def gap(t):
        return (2 * C + t * DSTAR) - h_C(t)

    ts = np.linspace(0.01, 0.99, 99)
    gaps = np.array([gap(t) for t in ts])
    i = int(gaps.argmax())
    t_hat = ts[i]
    r = minimize_scalar(lambda t: -gap(t), bounds=(max(t_hat - 0.05, 1e-4),
                                                   min(t_hat + 0.05, 0.9999)),
                        method="bounded", options={"xatol": 1e-10})
    w = gap(r.x)
    assert w > 1e-3
    assert abs(w - 0.022030) < 5e-6, w
    assert abs(r.x - 0.675) < 5e-3, r.x
    return (f"max gap {w:.6f} at t = {r.x:.6f}; ratio to d* = {w/DSTAR:.4f} "
            f"(N6: 0.022030 at t=0.675, 0.568 x d*) => the shoulder face is "
            f"non-empty")


@test("G2 [break target 7] C subset Thm7 is verbatim in [auxrec] Theorem 7 (outer bound)")
def t_g2():
    import pathlib
    lit = pathlib.Path("/private/tmp/claude-502/-Users-haruka-dev-lean-projects/"
                       "5fc80860-93c8-48b1-836d-e176acf938d4/scratchpad/lit/auxrec.txt")
    if not lit.exists():
        return "SKIP (literature scratchpad gone; see docs/shannon/lit-fetch.sh)"
    # NOTE: str.splitlines() also breaks on the form feeds pdftotext emits, so
    # its numbering diverges from grep/awk.  Split on "\n" only.
    lines = lit.read_text(errors="replace").split("\n")
    hit = [i + 1 for i, l in enumerate(lines)
           if "any achievable rate triple" in l and "Theorem 7" in l]
    assert hit, "Theorem 7 statement not located"
    assert hit[0] == 1034, f"line drift: {hit}"
    return (f"auxrec.txt:{hit[0]}-1036 -- 'Given a broadcast channel ... and any "
            f"achievable rate triple (R0,R1,R2), one can find some input "
            f"distribution p(x) such that for any auxiliary channel T_J|X,Y,Z, "
            f"the following constraints are satisfied' => C subset Thm7 is the "
            f"theorem itself, not an unproven premise")


def main():
    print(f"N6 adversarial audit -- independent verifier")
    print(f"p={P}  e=h(p)={E:.10f}  C={C:.10f}  alpha*={ALPHA:.10f}")
    print(f"d*={DSTAR:.10f}  SR_C={SR_C:.10f}  C+S(mu*)={CEIL:.10f}")
    print("=" * 78)
    npass = nfail = 0
    for name, fn in TESTS:
        try:
            note = fn()
            npass += 1
            print(f"[PASS] {name}\n       {note}")
        except AssertionError as exc:
            nfail += 1
            print(f"[FAIL] {name}\n       {exc}")
    print("=" * 78)
    print(f"{npass}/{len(TESTS)} passed, {nfail} failed")
    return 1 if nfail else 0


if __name__ == "__main__":
    raise SystemExit(main())
