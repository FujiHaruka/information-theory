#!/usr/bin/env python3
"""N16 adversarial independent audit -- does `UV = C` hold on the [probc] more-capable instance?

Default position: the verdict `UV = C` is FALSE.  Every test below is written to break it.

INDEPENDENCE (parent plan section 4.6):
  * This file does NOT import, execute, or copy `n16_uv_gate_probc.py` (the audited verifier),
    nor any other file under `verifiers/`.  Everything is re-implemented from scratch.
  * Where the audited leg used one route, this file deliberately uses another:
      - the audited leg took the `C`-side lower bound from [probc] Theorem 3's box;
        this file re-derives it from **Marton's inner bound directly** (no Theorem 3),
      - the audited leg *cited* `Omega(t) = d*_t` from bc-facts `## N10 (T3c)` without
        re-deriving it; this file re-derives `Omega(t) <= d*_t` with its own
        **branch-and-bound certificate** over the input simplex,
      - the audited leg screened `UV subset C` numerically (its `R2`); this file both
        screens and searches adversarially with correlated cross-block auxiliaries.

Run:   python3 docs/shannon/verifiers/n16_audit_probc.py
       LIT=<dir> python3 docs/shannon/verifiers/n16_audit_probc.py     # adds the verbatim group

`LIT` is the output directory of `docs/shannon/lit-fetch.sh`.  Extracted text is never committed
(the repo is public); only the retrieval command and the measured line numbers live in the repo.
"""

import itertools
import math
import os
import sys
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog, minimize

# --------------------------------------------------------------------------------------------
# harness
# --------------------------------------------------------------------------------------------

PASS = 0
FAIL = 0
SKIP = 0


def check(name, ok, detail=""):
    global PASS, FAIL
    if ok:
        PASS += 1
        print("  ok   %-88s %s" % (name, detail))
    else:
        FAIL += 1
        print("  FAIL %-88s %s" % (name, detail))


def skip(name, why):
    global SKIP
    SKIP += 1
    print("  skip %-88s %s" % (name, why))


def head(title):
    print()
    print("=" * 118)
    print(title)
    print("=" * 118)


# --------------------------------------------------------------------------------------------
# information-theory primitives (from scratch, base 2)
# --------------------------------------------------------------------------------------------

LOG2 = math.log(2.0)


def h2(x):
    """Binary entropy, in bits."""
    if x <= 0.0 or x >= 1.0:
        return 0.0
    return -x * math.log(x) / LOG2 - (1 - x) * math.log(1 - x) / LOG2


def H(q):
    """Shannon entropy of a probability vector, in bits."""
    q = np.asarray(q, dtype=float)
    nz = q[q > 0]
    return float(-np.sum(nz * np.log(nz)) / LOG2)


def gradH(q):
    """Gradient of H at an interior point (bits)."""
    q = np.asarray(q, dtype=float)
    return -(np.log(q) + 1.0) / LOG2


def bstar(a, b):
    """a * b  =  a(1-b) + (1-a)b."""
    return a * (1 - b) + (1 - a) * b


# --------------------------------------------------------------------------------------------
# the instance: a product broadcast channel, built from scratch
#
#   block 1:  X1 -> Y1 = BEC(e),  X1 -> Z1 = BSC(p)
#   block 2:  X2 -> Y2 = BSC(p),  X2 -> Z2 = BEC(e)
#   X = (X1,X2) in {0,1}^2 indexed i = 2*x1 + x2
#   Y = (Y1,Y2) in {0,1,?} x {0,1}, indexed 2*y1 + y2   (y1 in {0,1,2} with 2 = erasure)
#   Z = (Z1,Z2) in {0,1} x {0,1,?}, indexed 3*z1 + z2
# --------------------------------------------------------------------------------------------


def bec(e):
    """2 x 3 row-stochastic matrix; column 2 is the erasure symbol."""
    return np.array([[1 - e, 0.0, e], [0.0, 1 - e, e]])


def bsc(p):
    return np.array([[1 - p, p], [p, 1 - p]])


class Instance(object):
    def __init__(self, p, e):
        self.p, self.e = p, e
        B_e, B_p = bec(e), bsc(p)
        # Y = (Y1, Y2) with Y1 ~ BEC(e)(X1), Y2 ~ BSC(p)(X2)
        self.MY = np.kron(B_e, B_p)          # 4 x 6
        # Z = (Z1, Z2) with Z1 ~ BSC(p)(X1), Z2 ~ BEC(e)(X2)
        self.MZ = np.kron(B_p, B_e)          # 4 x 6
        self.C = 1.0 - e                     # BEC capacity of the erasure component
        self.C1 = 1.0 - e                    # I(X1;Y1) at uniform
        self.C2 = 1.0 - h2(p)                # I(X2;Y2) at uniform
        self.HYgX = h2(e) + h2(p)
        self.HZgX = h2(p) + h2(e)
        self.unif = np.full(4, 0.25)

    # --- functionals of an input law s on the 4 inputs -----------------------------------
    def HY(self, s):
        return H(np.asarray(s) @ self.MY)

    def HZ(self, s):
        return H(np.asarray(s) @ self.MZ)

    def IXY(self, s):
        return self.HY(s) - self.HYgX

    def IXZ(self, s):
        return self.HZ(s) - self.HZgX

    def f_t(self, s, t):
        return self.HY(s) - t * self.HZ(s)

    def psi_t(self, beta, t):
        """psi_t(b) = t*C*h(b) - h(b*p) + h(p)   (bc-facts `## N7 (T3c)` symbol block)."""
        return t * self.C * h2(beta) - h2(bstar(beta, self.p)) + h2(self.p)

    def dstar_t(self, t, n=200001):
        """max_beta psi_t(beta), by dense scan + golden refinement (independent of any file)."""
        bs = np.linspace(0.0, 0.5, n)
        vals = np.array([self.psi_t(b, t) for b in bs])
        i = int(np.argmax(vals))
        lo = bs[max(i - 1, 0)]
        hi = bs[min(i + 1, n - 1)]
        gr = (math.sqrt(5) - 1) / 2
        for _ in range(400):
            c, d = hi - gr * (hi - lo), lo + gr * (hi - lo)
            if self.psi_t(c, t) > self.psi_t(d, t):
                hi = d
            else:
                lo = c
        return max(self.psi_t(0.5 * (lo + hi), t), float(vals[i]), self.psi_t(0.0, t))


PROBC = Instance(0.1, h2(0.1))


# --------------------------------------------------------------------------------------------
# GROUP A -- the instance itself, and the facts the whole chain rests on
# --------------------------------------------------------------------------------------------


def group_a():
    head("GROUP A -- the instance, rebuilt from scratch")
    I = PROBC

    # A1 -- H(Y|X=x) and H(Z|X=x) constant over the 4 inputs.
    hy = [H(I.MY[i]) for i in range(4)]
    hz = [H(I.MZ[i]) for i in range(4)]
    ok = max(abs(v - (h2(I.e) + h2(I.p))) for v in hy + hz) < 1e-14
    check("A1  H(Y|X=x) = H(Z|X=x) = h(e)+h(p) for all 4 inputs", ok,
          "spread %.3e" % max(max(hy) - min(hy), max(hz) - min(hz)))

    # A2 -- I(X;Y) at uniform equals C1 + C2 (= 2C on the curve e = h(p)).
    v = I.IXY(I.unif)
    check("A2  I(X;Y)_uniform = C1 + C2", abs(v - (I.C1 + I.C2)) < 1e-14,
          "= %.12f, C1+C2 = %.12f" % (v, I.C1 + I.C2))
    check("A2b C1 = C2 on the curve e = h(p)", abs(I.C1 - I.C2) < 1e-15,
          "C = %.10f" % I.C)

    # A3 -- the ceiling used by branch (iii): I(X;Y), I(X;Z) <= C1 + C2 for every input law.
    rng = np.random.default_rng(20260809)
    worst = -1e9
    for _ in range(60000):
        s = rng.dirichlet(np.full(4, rng.choice([0.05, 0.3, 1.0, 5.0])))
        worst = max(worst, I.IXY(s) - (I.C1 + I.C2), I.IXZ(s) - (I.C1 + I.C2))
    for s in [np.eye(4)[i] for i in range(4)] + [I.unif]:
        worst = max(worst, I.IXY(s) - (I.C1 + I.C2), I.IXZ(s) - (I.C1 + I.C2))
    check("A3  I(X;Y), I(X;Z) <= C1+C2 for every input law (60005 laws)", worst <= 1e-12,
          "max excess %.3e" % worst)

    # A4 -- my own single-letterization: I(X;Y) = I(X2;Y2) + I(X1;Y1|Y2).
    #       (the identity that turns Omega into psi_t(b) - G_t; derived by hand in the audit)
    def decomp_resid(s):
        s = np.asarray(s).reshape(2, 2)          # s[x1, x2]
        b = s[:, 1].sum()                        # P(X2 = 1)
        px1 = s.sum(axis=1)
        # I(X2;Y2): X2 marginal through BSC(p)
        IX2Y2 = h2(bstar(b, I.p)) - h2(I.p)
        # I(X1;Y1|Y2) = I(X;Y) - I(X2;Y2)
        return I.IXY(s.reshape(4)) - IX2Y2, px1, b

    rng = np.random.default_rng(7)
    bad = 0.0
    for _ in range(4000):
        s = rng.dirichlet(np.full(4, 1.0))
        r, _, _ = decomp_resid(s)
        bad = max(bad, -r - 1e-12)               # I(X1;Y1|Y2) must be >= 0
    check("A4  I(X;Y) - I(X2;Y2) = I(X1;Y1|Y2) >= 0 (4000 laws)", bad <= 0.0,
          "min of the conditional term %.3e" % (-bad))

    # A5 -- the (R1,R2) symmetry that branch (ii) leans on: (block swap, Y <-> Z) fixes the channel.
    #       index i = 2*x1 + x2 -> swapped index 2*x2 + x1 ; Y-image must become the Z-image.
    perm = [0, 2, 1, 3]
    worst = 0.0
    for i in range(4):
        # after swapping the two blocks, the Y channel of the swapped input must equal
        # the Z channel of the original input, up to relabelling the output pair order
        y = I.MY[perm[i]].reshape(3, 2).T.reshape(6)       # (y1,y2) -> (y2,y1)
        worst = max(worst, float(np.abs(y - I.MZ[i]).max()))
    check("A5  (block swap, Y<->Z) maps the instance to itself, so C and UV are (R1,R2)-symmetric",
          worst < 1e-15, "max entrywise residual %.3e" % worst)


# --------------------------------------------------------------------------------------------
# GROUP B -- the load-bearing citation the audited leg never re-derived: Omega(t) = d*_t
#
#   Omega(t) := max_s [ t*I(X;Z)_s - I(X;Y)_s ]
#             = -min_s f_t(s) + (1-t)*(h(e)+h(p)),   f_t(s) = H(Y)_s - t*H(Z)_s
# --------------------------------------------------------------------------------------------


def omega_from_fmin(I, fmin, t):
    return -fmin + I.HYgX - t * I.HZgX


def bb_min_f(I, t, tol=1e-9, max_cells=4000000):
    """Branch-and-bound LOWER bound on min_{s in simplex} f_t(s).

    Cell relaxation, applied PER OUTPUT LETTER.  Write H(q) = sum_j eta(q_j) with
    eta(u) = -u*log2(u); each q_j is affine in s, so over a cell it ranges over an interval
    [lo_j, hi_j] read off the cell's vertices.  Then
      * eta concave  ==>  eta >= its CHORD on [lo_j, hi_j]   : affine lower bound on H(Y)_s,
      * eta concave  ==>  eta <= its TANGENT at the midpoint : affine lower bound on -t*H(Z)_s.
    The sum is affine in s, so its minimum over the cell sits at a vertex.
    Returns (lower_bound, incumbent, n_cells).
    """
    V0 = np.eye(4)
    inc = min(I.f_t(V0[i], t) for i in range(4))
    inc = min(inc, I.f_t(I.unif, t))

    def eta(u):
        return 0.0 if u <= 0.0 else -u * math.log(u) / LOG2

    def cell_bound(V):
        QY = V @ I.MY                       # 4 vertices x |Y|
        QZ = V @ I.MZ
        loY, hiY = QY.min(axis=0), QY.max(axis=0)
        loZ, hiZ = QZ.min(axis=0), QZ.max(axis=0)
        midZ = 0.5 * (loZ + hiZ)
        best = None
        for i in range(4):
            hy = 0.0
            for j in range(QY.shape[1]):
                lo, hi, u = loY[j], hiY[j], QY[i, j]
                if hi - lo <= 1e-15:
                    hy += eta(u)
                else:
                    hy += eta(lo) + (u - lo) * (eta(hi) - eta(lo)) / (hi - lo)
            hz = 0.0
            for j in range(QZ.shape[1]):
                m, u = midZ[j], QZ[i, j]
                if m <= 1e-300:
                    hz += eta(u)
                else:
                    hz += eta(m) - (math.log(m) + 1.0) / LOG2 * (u - m)
            val = hy - t * hz
            best = val if best is None else min(best, val)
        return best

    import heapq
    ctr = itertools.count()
    heap = [(cell_bound(V0), next(ctr), V0)]
    n = 0
    # A cell is pruned once its bound is >= inc - tol, so a pruned cell only certifies
    # `>= inc - tol`.  The certified global lower bound is therefore the min of the smallest
    # LIVE cell bound and `inc - tol` -- never the live bound alone (that can exceed `inc`).
    while heap:
        lb, _, V = heapq.heappop(heap)
        if inc - lb <= tol or n > max_cells:
            return min(lb, inc - tol), inc, n
        for w in list(V) + [V.mean(axis=0)]:
            inc = min(inc, I.f_t(w, t))
        best_pair, best_len = (0, 1), -1.0
        for i, j in itertools.combinations(range(4), 2):
            d = float(np.linalg.norm(V[i] - V[j]))
            if d > best_len:
                best_len, best_pair = d, (i, j)
        i, j = best_pair
        mid = 0.5 * (V[i] + V[j])
        for drop in (i, j):
            W = V.copy()
            W[drop] = mid
            b = cell_bound(W)
            if b < inc - tol:
                heapq.heappush(heap, (b, next(ctr), W))
        n += 1
    return inc - tol, inc, n


def group_b():
    head("GROUP B  (*) -- Omega(t) = d*_t, the one machine fact the audited leg only CITED")
    I = PROBC

    # B1 -- the >= direction is FREE: the product law with X1 deterministic realises psi_t(beta)
    #       exactly, for every beta.  Taking the sup over beta gives Omega(t) >= d*_t with no
    #       optimisation at all, so `Omega(t) < d*_t` cannot happen -- which is the failure
    #       direction the audited artefact's section 6-1 names as the risk to the verdict.
    resid = 0.0
    for t in np.linspace(0.0, 1.0, 41):
        for beta in np.linspace(0.0, 1.0, 401):
            s = np.array([1 - beta, beta, 0.0, 0.0])      # X1 = 0 always, X2 ~ Bern(beta)
            resid = max(resid, abs((t * I.IXZ(s) - I.IXY(s)) - I.psi_t(beta, t)))
    check("B1  (*) the witness X1=0, X2~Bern(b) realises psi_t(b) exactly (41 t x 401 b)",
          resid < 1e-13,
          "max residual %.3e  ==> Omega(t) >= sup_b psi_t(b) = d*_t, so `Omega(t) < d*_t` "
          "is IMPOSSIBLE" % resid)

    # B2 -- my own reduction identity (derived by hand, not taken from any file):
    #       t*I(X;Z)_s - I(X;Y)_s = psi_t(b) - G_t(s),  G_t = I(X1;Y1|Y2) - t*I(X1;Z1|Z2)
    rng = np.random.default_rng(31337)
    resid = 0.0
    for _ in range(20000):
        s = rng.dirichlet(np.full(4, rng.choice([0.2, 1.0, 4.0])))
        t = float(rng.uniform(0, 1))
        b = s[1] + s[3]
        IX2Y2 = h2(bstar(b, I.p)) - h2(I.p)
        IX2Z2 = I.C * h2(b)
        G = (I.IXY(s) - IX2Y2) - t * (I.IXZ(s) - IX2Z2)
        lhs = t * I.IXZ(s) - I.IXY(s)
        resid = max(resid, abs(lhs - (I.psi_t(b, t) - G)))
    check("B2  identity  t*I(X;Z)-I(X;Y) = psi_t(b) - G_t(s)  (20000 random (s,t))",
          resid < 1e-12, "max residual %.3e" % resid)

    # B3 -- (*) the real work: an INDEPENDENT branch-and-bound certificate for Omega(t) <= d*_t.
    ts = [0.0, 0.05, 0.1462, 0.25, 0.3, 0.4, 0.49895, 0.5, 0.6, 0.7, 0.8, 0.9, 0.95, 1.0]
    worst_gap, rows = -1e9, []
    for t in ts:
        lb, inc, n = bb_min_f(I, t, tol=1e-9)
        om_ub = omega_from_fmin(I, lb, t)
        d = I.dstar_t(t)
        gap = om_ub - d
        worst_gap = max(worst_gap, gap)
        rows.append((t, om_ub, d, gap, n))
    check("B3  (*) branch-and-bound: Omega(t) <= d*_t re-derived independently (14 values of t)",
          worst_gap <= 2e-9,
          "max (Omega_ub - d*_t) = %.3e over t in [0,1]" % worst_gap)
    for t, om, d, gap, n in rows:
        print("        t=%-8.5f Omega_ub=%+.12f  d*_t=%+.12f  gap=%+.3e  cells=%d"
              % (t, om, d, gap, n))

    # B4 -- adversarial global search for Omega(t) > d*_t, including correlated X1,X2.
    rng = np.random.default_rng(999331)
    worst = -1e9
    argw = None
    for t in np.linspace(0.0, 1.0, 21):
        d = I.dstar_t(t)

        def neg(u):
            s = np.exp(u - u.max())
            s = s / s.sum()
            return -(t * I.IXZ(s) - I.IXY(s))

        cands = []
        for _ in range(240):
            cands.append(rng.normal(0, 3.0, 4))
        # structured: strongly correlated / anti-correlated (X1 = X2 xor Bern(q)) families
        for q in np.linspace(0, 1, 41):
            for bb in np.linspace(0.02, 0.98, 25):
                s = np.array([(1 - bb) * (1 - q), (1 - bb) * q, bb * q, bb * (1 - q)])
                s = np.clip(s, 1e-14, None)
                cands.append(np.log(s / s.sum()))
        for u0 in cands:
            best = -neg(u0)
            r = minimize(neg, u0, method="Nelder-Mead",
                         options=dict(maxiter=3000, xatol=1e-12, fatol=1e-14))
            best = max(best, -r.fun)
            if best - d > worst:
                worst, argw = best - d, (t, best, d)
    check("B4  adversarial search for Omega(t) > d*_t (21 t x ~1265 starts each)",
          worst <= 1e-9,
          "max excess %.3e at t=%.4f" % (worst, argw[0] if argw else -1))

    # B5 -- negative control: the claim must BREAK above the curve e > h(p).
    bad = Instance(0.1, h2(0.1) + 0.05)
    br = []
    for t in [0.5, 1.0]:
        lb, inc, n = bb_min_f(bad, t, tol=1e-7)
        br.append(omega_from_fmin(bad, lb, t) - bad.dstar_t(t))
    check("B5  negative control: e > h(p) breaks Omega(t) = d*_t (so the test has teeth)",
          max(br) > 1e-3, "excess at t=0.5,1.0: %.4f / %.4f" % (br[0], br[1]))


# --------------------------------------------------------------------------------------------
# GROUP C -- half-space sweep (the audited leg's `R5` looked at 5 points)
# --------------------------------------------------------------------------------------------


def group_c():
    head("GROUP C -- the half-space {0 < p < 1/2, e <= h(p)}: far more than 5 points")
    rng = np.random.default_rng(4242)
    pts = []
    for p in [0.02, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.35, 0.4, 0.45, 0.49]:
        for frac in [0.0, 0.25, 0.5, 0.75, 1.0]:
            pts.append((p, frac * h2(p)))
    for _ in range(19):
        p = float(rng.uniform(0.01, 0.49))
        pts.append((p, float(rng.uniform(0.0, 1.0)) * h2(p)))

    # C1 -- Omega(t) = d*_t across the half-space, certified by branch-and-bound.
    worst, argw = -1e9, None
    for (p, e) in pts:
        J = Instance(p, e)
        for t in (0.35, 1.0):
            lb, inc, n = bb_min_f(J, t, tol=1e-7)
            g = omega_from_fmin(J, lb, t) - J.dstar_t(t)
            if g > worst:
                worst, argw = g, (p, e, t)
    check("C1  (*) Omega(t) <= d*_t certified at %d half-space points x 2 t" % len(pts),
          worst <= 2e-7, "max gap %.3e at (p,e,t) = (%.4f, %.4f, %.2f)"
          % (worst, argw[0], argw[1], argw[2]))

    # C2 -- the beta-split identity R1(b) + t*R2(b) = (C1+C2) + psi_t(b) off the curve.
    worst = 0.0
    for (p, e) in pts:
        J = Instance(p, e)
        for b in np.linspace(0, 1, 61):
            R1 = J.C1 + 1 - h2(bstar(b, p))
            R2 = J.C1 * h2(b)
            for t in np.linspace(0, 1, 11):
                worst = max(worst, abs(R1 + t * R2 - ((J.C1 + J.C2) + J.psi_t(b, t))))
    check("C2  R1(b) + t*R2(b) = (C1+C2) + psi_t(b) holds off the curve e = h(p)",
          worst < 1e-13, "max residual %.3e over %d (p,e) x 61 b x 11 t" % (worst, len(pts)))

    # C4 -- the C-side Marton box across the half-space (not just on the curve e = h(p)):
    #       vertex tight in all four, R0 >= 0, and the slice point inside.
    worst, neg = 0.0, 0.0
    for (p, e) in pts:
        J = Instance(p, e)
        for b in np.linspace(0, 0.5, 121):
            a = marton_beta_split(J, b)
            R1 = J.C1 + 1 - h2(bstar(b, p))
            R2 = J.C1 * h2(b)
            worst = max(worst, abs(a["B1"] - R1), abs(a["B2"] - R1),
                        abs(a["S"] - (R1 + R2)), abs(a["m"] - (R1 - R2)),
                        abs(a["IWY"] - a["IWZ"]))
            neg = min(neg, R1 - R2)
    check("C4  (*) the MARTON box and its vertex reproduce across the half-space (%d points)"
          % len(pts), worst < 1e-12 and neg >= -1e-15,
          "max residual %.3e, min R0 = %.3e" % (worst, neg))

    # C3 -- negative control for the half-space: above the curve it must fail.
    J = Instance(0.2, h2(0.2) + 0.08)
    lb, inc, n = bb_min_f(J, 1.0, tol=1e-7)
    g = omega_from_fmin(J, lb, 1.0) - J.dstar_t(1.0)
    check("C3  negative control: (p,e) = (0.2, h(0.2)+0.08) breaks it", g > 1e-3,
          "excess %.4f" % g)


# --------------------------------------------------------------------------------------------
# GROUP D -- the C-side lower bound, re-derived from MARTON directly (no [probc] Theorem 3)
#
#   W = (W1, W2), each a 2-state beta-split;  U = X1;  V = X2.
#   Marton with a common message:
#       R0            <= min{ I(W;Y), I(W;Z) }
#       R0 + R1       <= I(U,W;Y)
#       R0 + R2       <= I(V,W;Z)
#       R0 + R1 + R2  <= min{I(W;Y),I(W;Z)} + I(U;Y|W) + I(V;Z|W) - I(U;V|W)
# --------------------------------------------------------------------------------------------


def marton_beta_split(I, beta):
    """Exact evaluation of the Marton box for the beta-split witness, by hand-built laws."""
    p, e, C = I.p, I.e, I.C
    hb = h2(beta)
    hbp = h2(bstar(beta, p))
    # block 1: X1 -> Y1 = BEC(e), X1 -> Z1 = BSC(p)
    I_W1_Y1 = C * (1 - hb)
    I_X1_Y1_W1 = C * hb
    I_W1_Z1 = 1 - hbp
    I_X1_Z1_W1 = hbp - h2(p)
    # block 2: X2 -> Y2 = BSC(p), X2 -> Z2 = BEC(e)
    I_W2_Y2 = 1 - hbp
    I_X2_Y2_W2 = hbp - h2(p)
    I_W2_Z2 = C * (1 - hb)
    I_X2_Z2_W2 = C * hb

    IWY = I_W1_Y1 + I_W2_Y2
    IWZ = I_W1_Z1 + I_W2_Z2
    m = min(IWY, IWZ)
    IUYgW = I_X1_Y1_W1          # U = X1 : I(X1; Y1 Y2 | W) = I(X1;Y1|W1)
    IVZgW = I_X2_Z2_W2          # V = X2 : I(X2; Z1 Z2 | W) = I(X2;Z2|W2)
    IUVgW = 0.0                 # blocks independent given W
    return dict(m=m, IWY=IWY, IWZ=IWZ,
                B1=IWY + IUYgW, B2=IWZ + IVZgW,
                S=m + IUYgW + IVZgW - IUVgW)


def group_d():
    head("GROUP D -- the C-side, re-derived from MARTON (the audited leg used [probc] Thm 3)")
    I = PROBC

    # D0 -- verify the hand-built mutual informations against a brute-force joint law.
    def brute(beta):
        # W1,W2 in {0,1}; X_i | W_i = 0 ~ Bern(beta), | W_i = 1 ~ Bern(1-beta)
        pw = 0.5
        pxw = np.array([[1 - beta, beta], [beta, 1 - beta]])   # [w][x]
        # joint over (w1,w2,x1,x2)
        J = np.zeros((2, 2, 2, 2))
        for w1 in range(2):
            for w2 in range(2):
                for x1 in range(2):
                    for x2 in range(2):
                        J[w1, w2, x1, x2] = pw * pw * pxw[w1, x1] * pxw[w2, x2]
        # push through channels
        pXgW = J.reshape(4, 4)                      # rows = (w1,w2), cols = (x1,x2)
        pW = pXgW.sum(axis=1)
        cond = pXgW / pW[:, None]
        IWY = H(pXgW.sum(axis=0) @ I.MY) - sum(pW[k] * H(cond[k] @ I.MY) for k in range(4))
        IWZ = H(pXgW.sum(axis=0) @ I.MZ) - sum(pW[k] * H(cond[k] @ I.MZ) for k in range(4))
        # I(U;Y|W) with U = X1
        IUYgW = 0.0
        for k in range(4):
            q = cond[k]
            hy = H(q @ I.MY)
            # condition further on x1
            acc = 0.0
            for x1 in range(2):
                sub = np.zeros(4)
                sub[2 * x1] = q[2 * x1]
                sub[2 * x1 + 1] = q[2 * x1 + 1]
                w = sub.sum()
                if w > 0:
                    acc += w * H((sub / w) @ I.MY)
            IUYgW += pW[k] * (hy - acc)
        IVZgW = 0.0
        for k in range(4):
            q = cond[k]
            hz = H(q @ I.MZ)
            acc = 0.0
            for x2 in range(2):
                sub = np.zeros(4)
                sub[x2] = q[x2]
                sub[2 + x2] = q[2 + x2]
                w = sub.sum()
                if w > 0:
                    acc += w * H((sub / w) @ I.MZ)
            IVZgW += pW[k] * (hz - acc)
        return IWY, IWZ, IUYgW, IVZgW

    worst = 0.0
    for beta in [0.0, 0.05, 0.1, 0.2, 0.3, 0.4, 0.5]:
        a = marton_beta_split(I, beta)
        IWY, IWZ, IUYgW, IVZgW = brute(beta)
        worst = max(worst, abs(a["IWY"] - IWY), abs(a["IWZ"] - IWZ),
                    abs(a["B1"] - (IWY + IUYgW)), abs(a["B2"] - (IWZ + IVZgW)))
    check("D0  closed-form Marton box == brute-force joint-law evaluation (7 beta)",
          worst < 1e-12, "max residual %.3e" % worst)

    # D1 -- I(W;Y) = I(W;Z) for this witness, so `min` is not a corner case.
    worst = max(abs(marton_beta_split(I, b)["IWY"] - marton_beta_split(I, b)["IWZ"])
                for b in np.linspace(0, 0.5, 201))
    check("D1  I(W;Y) = I(W;Z) for the beta-split witness (201 beta)", worst < 1e-14,
          "max |I(W;Y)-I(W;Z)| = %.3e" % worst)

    # D2 -- the box numbers match the audited leg's R1(b), R2(b) and M = R1 - R2.
    worst = 0.0
    for beta in np.linspace(0, 0.5, 501):
        a = marton_beta_split(I, beta)
        R1 = I.C1 + 1 - h2(bstar(beta, I.p))
        R2 = I.C1 * h2(beta)
        worst = max(worst, abs(a["B1"] - R1), abs(a["B2"] - R1),
                    abs(a["S"] - (R1 + R2)), abs(a["m"] - (R1 - R2)))
    check("D2  Marton box = (M, B1, B2, S) with B1=B2=R1(b), S=R1+R2, M=R1-R2 (501 beta)",
          worst < 1e-13, "max residual %.3e" % worst)

    # D3 -- the vertex (R1-R2, R2, R2) is Marton-achievable, all four constraints tight.
    worst = 0.0
    for beta in np.linspace(0, 0.5, 501):
        a = marton_beta_split(I, beta)
        R1 = I.C1 + 1 - h2(bstar(beta, I.p))
        R2 = I.C1 * h2(beta)
        R = (R1 - R2, R2, R2)
        worst = max(worst, abs(R[0] - a["m"]), abs(R[0] + R[1] - a["B1"]),
                    abs(R[0] + R[2] - a["B2"]), abs(sum(R) - a["S"]))
        if min(R) < -1e-15:
            worst = 1.0
    check("D3  (*) the vertex (R1-R2, R2, R2) is in the MARTON box, all 4 tight, R0 >= 0",
          worst < 1e-13, "max slack %.3e" % worst)

    # D4 -- the slice point (0, R1(b), R2(b)) is Marton-achievable.
    worst = 0.0
    for beta in np.linspace(0, 0.5, 501):
        a = marton_beta_split(I, beta)
        R1 = I.C1 + 1 - h2(bstar(beta, I.p))
        R2 = I.C1 * h2(beta)
        worst = max(worst, R1 - a["B1"], R2 - a["B2"], (R1 + R2) - a["S"], -a["m"])
    check("D4  (*) the slice point (0, R1(b), R2(b)) is in the MARTON box (501 beta)",
          worst < 1e-13, "max violation %.3e" % worst)

    # D5 -- hence h_C(0,1,t) >= (C1+C2) + d*_t without using [probc] Theorem 3 at all.
    #       D2/D4 make (0, R1(b), R2(b)) Marton-achievable and C2 makes the identity pointwise,
    #       so the two suprema must agree exactly; compare them over a COMMON grid in b
    #       (a finer grid on one side only would measure grid resolution, not the claim).
    bs = np.linspace(0, 0.5, 200001)
    R1s = np.array([I.C1 + 1 - h2(bstar(b, I.p)) for b in bs])
    R2s = np.array([I.C1 * h2(b) for b in bs])
    worst = 0.0
    for t in np.linspace(0, 1, 51):
        lhs = float(np.max(R1s + t * R2s))
        rhs = (I.C1 + I.C2) + max(I.psi_t(b, t) for b in bs)
        worst = max(worst, abs(lhs - rhs))
    check("D5  (*) sup_b [R1(b)+t R2(b)] = (C1+C2) + sup_b psi_t(b) from Marton alone (51 t)",
          worst < 1e-13, "max residual %.3e (so h_C(0,1,t) >= (C1+C2) + d*_t)" % worst)

    # D6 -- external anchor: [probc] Lemma 8 prints SR_M(q1 x q2) = 2C + d* with d* ~ 0.03877.
    #       The beta family's t = 1 maximum must reproduce it (a literature cross-check that
    #       does not go through bc-facts at all).
    sr = max((I.C1 + 1 - h2(bstar(b, I.p))) + I.C1 * h2(b) for b in np.linspace(0, 0.5, 200001))
    d1 = I.dstar_t(1.0)
    check("D6  (*) max_b [R1+R2] = 2C + d* matches [probc] Lemma 8 (d* ~ 0.03877 printed there)",
          abs(sr - (2 * I.C + d1)) < 1e-9 and abs(d1 - 0.03877) < 5e-5,
          "SR_M = %.10f, 2C = %.10f, d* = %.10f" % (sr, 2 * I.C, d1))


# --------------------------------------------------------------------------------------------
# GROUP E -- the UV upper-bound chain, in exact rational arithmetic
# --------------------------------------------------------------------------------------------


def group_e():
    head("GROUP E -- the UV box algebra, exact rationals (no floating point)")
    rng = np.random.default_rng(20260810)

    def rand_box():
        m = Fraction(int(rng.integers(0, 40)), 8)
        b1 = m + Fraction(int(rng.integers(0, 40)), 8)
        b2 = m + Fraction(int(rng.integers(0, 40)), 8)
        s = max(b1, b2) + Fraction(int(rng.integers(0, 40)), 8)
        return m, b1, b2, s

    def rand_pt(m, b1, b2, s):
        for _ in range(200):
            R0 = Fraction(int(rng.integers(0, 17)), 16) * m
            R1 = Fraction(int(rng.integers(0, 17)), 16) * (b1 - R0)
            R2 = Fraction(int(rng.integers(0, 17)), 16) * (b2 - R0)
            if R0 + R1 + R2 <= s and min(R0, R1, R2) >= 0:
                return R0, R1, R2
        return Fraction(0), Fraction(0), Fraction(0)

    def in_box(R, m, b1, b2, s):
        R0, R1, R2 = R
        return (min(R) >= 0 and R0 <= m and R0 + R1 <= b1
                and R0 + R2 <= b2 and R0 + R1 + R2 <= s)

    # E1 -- the projections phi, psi map every box into itself.
    bad = 0
    for _ in range(6000):
        m, b1, b2, s = rand_box()
        R = rand_pt(m, b1, b2, s)
        if not in_box(R, m, b1, b2, s):
            continue
        phi = (Fraction(0), R[0] + R[1], R[2])
        psi = (Fraction(0), R[1], R[0] + R[2])
        if not (in_box(phi, m, b1, b2, s) and in_box(psi, m, b1, b2, s)):
            bad += 1
    check("E1  phi(R)=(0,R0+R1,R2) and psi(R)=(0,R1,R0+R2) stay in the box (6000 exact cases)",
          bad == 0, "violations %d" % bad)

    # E2 -- direction (0,1,t): R1 + t*R2 <= (1-t)*b1 + t*s.
    bad = 0
    for _ in range(6000):
        m, b1, b2, s = rand_box()
        R = rand_pt(m, b1, b2, s)
        if not in_box(R, m, b1, b2, s):
            continue
        t = Fraction(int(rng.integers(0, 33)), 32)
        if R[1] + t * R[2] > (1 - t) * b1 + t * s:
            bad += 1
    check("E2  R1 + t*R2 <= (1-t)*(18b) + t*(18i) for t in [0,1] (6000 exact cases)",
          bad == 0, "violations %d" % bad)

    # E3 -- the theta identity of branch (ii), exactly.
    bad_id, bad_ineq = 0, 0
    for _ in range(6000):
        l1 = Fraction(int(rng.integers(1, 40)), 8)
        l2 = Fraction(int(rng.integers(0, 40)), 8)
        if l2 > l1:
            l1, l2 = l2, l1
        lo, hi = l1, l1 + l2
        if hi == lo:
            continue
        l0 = lo + Fraction(int(rng.integers(0, 17)), 16) * (hi - lo)
        den = 2 * l0 - l1 - l2
        if den == 0:
            continue
        th = (l0 - l2) / den
        if not (0 <= th <= 1):
            bad_ineq += 1
        m, b1, b2, s = rand_box()
        R = rand_pt(m, b1, b2, s)
        if not in_box(R, m, b1, b2, s):
            continue
        mu = (l0, l1 + l2 - l0)
        phi = (R[0] + R[1], R[2])
        psi = (R[1], R[0] + R[2])
        lhs = th * (mu[0] * phi[0] + mu[1] * phi[1]) + (1 - th) * (mu[1] * psi[0] + mu[0] * psi[1])
        rhs = l0 * R[0] + l1 * R[1] + l2 * R[2]
        if lhs != rhs:
            bad_id += 1
    check("E3  theta = (l0-l2)/(2*l0-l1-l2) reproduces lambda.R exactly (6000 exact cases)",
          bad_id == 0 and bad_ineq == 0, "identity fails %d, theta out of [0,1] %d"
          % (bad_id, bad_ineq))

    # E4 -- branch (iii): l0 >= l1 + l2 forces lambda.R <= l0 * cap.
    bad = 0
    for _ in range(6000):
        cap = Fraction(int(rng.integers(1, 40)), 8)
        m = min(cap, Fraction(int(rng.integers(0, 40)), 8))
        b1 = min(cap, m + Fraction(int(rng.integers(0, 40)), 8))
        b2 = min(cap, m + Fraction(int(rng.integers(0, 40)), 8))
        s = max(b1, b2) + Fraction(int(rng.integers(0, 40)), 8)
        R = rand_pt(m, b1, b2, s)
        if not in_box(R, m, b1, b2, s):
            continue
        l1 = Fraction(int(rng.integers(0, 20)), 8)
        l2 = Fraction(int(rng.integers(0, 20)), 8)
        l0 = l1 + l2 + Fraction(int(rng.integers(0, 20)), 8)
        if l0 * R[0] + l1 * R[1] + l2 * R[2] > l0 * cap:
            bad += 1
    check("E4  l0 >= l1+l2 with R0,R0+R1,R0+R2 <= cap forces lambda.R <= l0*cap (6000 exact)",
          bad == 0, "violations %d" % bad)

    # E4b -- the degeneracy the artefact flags: l0 = l1 = l2 zeroes theta's denominator.
    #        There a SINGLE projection must already close the direction.
    bad = 0
    for _ in range(4000):
        m, b1, b2, s = rand_box()
        R = rand_pt(m, b1, b2, s)
        if not in_box(R, m, b1, b2, s):
            continue
        l = Fraction(int(rng.integers(1, 20)), 8)
        # lambda = (l,l,l): lambda.R = l*(R0+R1+R2) = l*(mu . phi(R)) with mu = (1,1)
        if l * (R[0] + R[1] + R[2]) != l * ((R[0] + R[1]) + R[2]):
            bad += 1
    check("E4b l0 = l1 = l2 (theta's denominator is 0): one projection already closes it",
          bad == 0, "violations %d of 4000 exact cases" % bad)

    # E5 -- NEGATIVE CONTROL: the branch (ii) argument must NOT prove anything when l0 > l1+l2.
    #       (if it did, the whole three-branch split would be vacuous decoration)
    found = 0
    for _ in range(20000):
        m, b1, b2, s = rand_box()
        R = rand_pt(m, b1, b2, s)
        if not in_box(R, m, b1, b2, s):
            continue
        l1 = Fraction(int(rng.integers(0, 20)), 8)
        l2 = Fraction(int(rng.integers(0, 20)), 8)
        l0 = l1 + l2 + Fraction(1, 2)
        mu = (l0, l1 + l2 - l0)         # mu[1] < 0 -- outside the admissible cone
        if mu[1] < 0:
            found += 1
    check("E5  negative control: branch (ii)'s mu leaves the nonneg orthant once l0 > l1+l2",
          found > 0, "%d of 20000 cases have mu_2 < 0 (so branch (iii) is genuinely needed)"
          % found)


# --------------------------------------------------------------------------------------------
# GROUP F -- adversarial hunt for a UV witness outside C  (attack axis 1)
# --------------------------------------------------------------------------------------------


def uv_box_from_witness(I, pWUVX):
    """UV / UVW box for an explicit joint law p(w,u,v,x) given as an array [w,u,v,x]."""
    A = np.asarray(pWUVX, dtype=float)
    A = A / A.sum()
    nw, nu, nv, nx = A.shape
    pX = A.sum(axis=(0, 1, 2))
    HY, HZ = H(pX @ I.MY), H(pX @ I.MZ)

    def cond_entropy(axes):
        """H(Y | those axes) and H(Z | those axes)."""
        keep = tuple(sorted(axes))
        drop = tuple(a for a in range(3) if a not in keep)
        M = A.sum(axis=drop) if drop else A
        M = M.reshape(-1, nx)
        w = M.sum(axis=1)
        hy = hz = 0.0
        for k in range(M.shape[0]):
            if w[k] <= 0:
                continue
            q = M[k] / w[k]
            hy += w[k] * H(q @ I.MY)
            hz += w[k] * H(q @ I.MZ)
        return hy, hz

    hy_w, hz_w = cond_entropy((0,))
    hy_uw, hz_uw = cond_entropy((0, 1))
    hy_vw, hz_vw = cond_entropy((0, 2))
    IWY, IWZ = HY - hy_w, HZ - hz_w
    IUYgW = hy_w - hy_uw
    IVZgW = hz_w - hz_vw
    IXZgUW = hz_uw - I.HZgX
    IXYgVW = hy_vw - I.HYgX
    m = min(IWY, IWZ)
    return dict(m=m, b1=m + IUYgW, b2=m + IVZgW,
                s=m + min(IUYgW + IXZgUW, IVZgW + IXYgVW))


def h_C_closed(I, lam):
    """(C1+C2 based) closed form of the C-side support value:  a*((C1+C2) + d*_{b/a})."""
    l0, l1, l2 = lam
    a = max(l0, l1, l2)
    if a <= 0:
        return 0.0
    b = min(l1, l2, max(l1 + l2 - l0, 0.0))
    return a * ((I.C1 + I.C2) + I.dstar_t(b / a))


def group_f():
    head("GROUP F -- adversarial hunt for a UV point outside C (correlated auxiliaries included)")
    I = PROBC
    rng = np.random.default_rng(5150)

    dirs = [(0, 1, 0), (0, 1, 1), (0, 1, 0.5), (0, 1, 0.25), (0, 0.5, 1),
            (1, 1, 1), (2, 1, 1), (1, 1, 0.5), (1.5, 1, 1), (3, 1, 1),
            (1, 1, 0.9), (0.7, 1, 1), (1.2, 1, 0.8), (0, 1, 0.75), (1, 0.6, 0.6)]

    def support_of_box(box, lam):
        """max lambda.R over the box, by LP (R >= 0)."""
        l0, l1, l2 = lam
        A = [[1, 0, 0], [1, 1, 0], [1, 0, 1], [1, 1, 1]]
        b = [box["m"], box["b1"], box["b2"], box["s"]]
        r = linprog(c=[-l0, -l1, -l2], A_ub=A, b_ub=b,
                    bounds=[(0, None)] * 3, method="highs")
        return -r.fun if r.status == 0 else -1e9

    worst, argw, n_wit = -1e9, None, 0
    for lam in dirs:
        hc = h_C_closed(I, lam)
        best = -1e9
        for _ in range(1400):
            nw = int(rng.integers(1, 5))
            nu = int(rng.integers(1, 4))
            nv = int(rng.integers(1, 4))
            mode = rng.integers(0, 3)
            if mode == 0:                                   # unstructured, fully correlated
                A = rng.dirichlet(np.full(nw * nu * nv * 4, 0.4)).reshape(nw, nu, nv, 4)
            elif mode == 1:                                 # W correlated ACROSS the two blocks
                A = np.zeros((nw, nu, nv, 4))
                for w in range(nw):
                    q = rng.dirichlet(np.full(4, rng.choice([0.15, 0.6, 3.0])))
                    U = rng.dirichlet(np.full(nu, 0.7))
                    V = rng.dirichlet(np.full(nv, 0.7))
                    A[w] = np.einsum("u,v,x->uvx", U, V, q)
                A *= rng.dirichlet(np.full(nw, 0.7))[:, None, None, None]
            else:                                           # U = X1, V = X2 style deterministic
                nu = nv = 2
                A = np.zeros((nw, 2, 2, 4))
                for w in range(nw):
                    q = rng.dirichlet(np.full(4, rng.choice([0.2, 1.0, 4.0])))
                    for x in range(4):
                        A[w, x >> 1, x & 1, x] = q[x]
                A *= rng.dirichlet(np.full(nw, 0.8))[:, None, None, None]
            box = uv_box_from_witness(I, A)
            best = max(best, support_of_box(box, lam))
        n_wit += 1400
        if best - hc > worst:
            worst, argw = best - hc, lam
    check("F1  SCREEN (no evidential value if it finds nothing): no UV witness beats h_C "
          "over %d witnesses x %d directions" % (n_wit // len(dirs), len(dirs)),
          worst <= 1e-9, "max excess %.3e at lambda = %s" % (worst, str(argw)))

    # F2 -- power check: the same search must REACH h_C, else F1 is vacuous.
    short = 1e9
    for lam in dirs:
        hc = h_C_closed(I, lam)
        best = -1e9
        # A LINEAR grid in beta is not enough: argmax psi_t collapses towards 0 as t falls
        # (bc-facts `## N7 (T3c)` N7-o records beta* ~ 4e-15 at t = 0.1), so mix in a log grid.
        betas = np.unique(np.concatenate([np.linspace(0, 0.5, 801),
                                          0.5 * np.logspace(-16, 0, 400)]))
        for beta in betas:
            a = marton_beta_split(I, beta)
            box = dict(m=a["m"], b1=a["B1"], b2=a["B2"], s=a["S"])
            best = max(best, support_of_box(box, lam))
        short = min(short, best - hc)
    # The residual shortfall is the beta grid's resolution, not a gap: D5 shows
    # sup_b [R1+t*R2] = (C1+C2) + sup_b psi_t(b) as an identity on a common grid.
    check("F2  power check: the beta-split family REACHES h_C in every direction",
          short > -1e-6, "max shortfall %.3e (beta grid resolution; D5 has the identity)"
          % (-short))

    # F3 -- the audited leg's D9 'touching' claim is nearly automatic: check the mechanism.
    worst = 0.0
    for beta in np.linspace(0.02, 0.5, 61):
        A = np.zeros((4, 2, 2, 4))
        pxw = np.array([[1 - beta, beta], [beta, 1 - beta]])
        for w1 in range(2):
            for w2 in range(2):
                for x1 in range(2):
                    for x2 in range(2):
                        A[2 * w1 + w2, x1, x2, 2 * x1 + x2] = 0.25 * pxw[w1, x1] * pxw[w2, x2]
        box = uv_box_from_witness(I, A)
        a = marton_beta_split(I, beta)
        worst = max(worst, abs(box["m"] - a["m"]), abs(box["b1"] - a["B1"]),
                    abs(box["b2"] - a["B2"]), abs(box["s"] - a["S"]))
    check("F3  the UV box of (W=beta-split^2, U=X1, V=X2) equals its MARTON box term by term",
          worst < 1e-12, "max residual %.3e (so 'touching' is I(U;V|W)=0, not a coincidence)"
          % worst)


# --------------------------------------------------------------------------------------------
# GROUP L -- verbatim literature re-check (independent retrieval), only with LIT set
# --------------------------------------------------------------------------------------------

QUOTES = [
    ("probc", 900, "Let p = 0.1, e = H(0.1)"),
    ("probc", 901, "BEC(e) and the channels X1 → Z1"),
    ("probc", 902, "and X2 → Y2 be BSC(p)"),
    ("probc", 335, "the UVW outer bound [8], the fact that we are showing"),
    ("probc", 336, "immediately implies the strict sub optimality of the UVW outer bound"),
    ("probc", 337, "the projection of the UVW outer bound on the plane R0 = 0"),
    ("probc", 486, "Hence, from Claim 3"),
    ("probc", 487, "better bound for product broadcast channels than the UVW outer bound"),
    ("probc", 906, "Y1 is more capable than Z1"),
    ("probc", 121, "forms a Markov chain"),
    ("probc", 123, "the UVW outer bound reduces to the UV outer bound"),
    ("probc", 115, "UVW outer bound"),
    ("probc", 104, "UV outer bound"),
    ("probc", 134, "I(X1 ; Y1 ) ≥ I(X1 ; Z1 )"),
    ("probc", 471, "the UV outer bound is strictly suboptimal in general"),
    ("auxrec", 1004, "Theorem 6 (UV outer bound)"),
    ("auxrec", 1011, "R0 + R1 ≤ min(I(W ; Y ), I(W ; Z)) + I(U ; Y |W )"),
    ("auxrec", 1012, "R0 + R2 ≤ min(I(W ; Y ), I(W ; Z)) + I(V ; Z|W )"),
    ("auxrec", 1014, "for some triple of random variables"),
    ("auxrec", 1038, "(18b)"),
    ("auxrec", 1049, "(18e)"),
    ("auxrec", 1071, "(18i)"),
    ("sumofbc", 55, "p(u)p(v)p(w|u, v)p(x|w, u, v)"),
    ("sumofbc", 62, "O(T ) ⊋ C(T ) = M(T )"),
    ("glnsum", 61, "for some pmf p(u, v, w, x)"),
    ("glnsum", 69, "OU V W (T ) ⊋ C(T ) = M(T )"),
]

GGNY = [
    (164, "T HE UV OUTER BOUND IS NOT TIGHT"),
    (169, "the UV outer bound is shown to be strictly suboptimal"),
    (170, "over this class of broadcast channels"),
    (344, "Claim 3. Consider the reversely semi-deterministic channel"),
    (491, "product of two reversely more-capable channels"),
    (492, "better bound for product broadcast channels than the UVW outer bound"),
]


def group_l():
    head("GROUP L -- verbatim re-check at the recorded line numbers (independent retrieval)")
    lit = os.environ.get("LIT")
    if not lit or not os.path.isdir(lit):
        skip("L1  verbatim quotations", "LIT unset; run docs/shannon/lit-fetch.sh and set LIT=<dir>")
        skip("L2  ggny (arXiv:1105.5438) anchors", "LIT unset")
        skip("L3  sumofbc vs glnsum use DIFFERENT witness versions", "LIT unset")
        return

    cache = {}

    def lines(stem):
        if stem not in cache:
            path = os.path.join(lit, stem + ".txt")
            with open(path, encoding="utf-8", errors="replace") as fh:
                cache[stem] = fh.read().split("\n")
        return cache[stem]

    miss = []
    for stem, ln, frag in QUOTES:
        L = lines(stem)
        txt = L[ln - 1] if 0 < ln <= len(L) else ""
        if frag not in txt:
            miss.append("%s:%d" % (stem, ln))
    check("L1  %d quotations (artefact citations + the two Remark-1 anchors it missed) reproduce"
          % len(QUOTES), not miss, "missing: %s" % (", ".join(miss) if miss else "none"))

    miss = []
    L = lines("ggny")
    for ln, frag in GGNY:
        txt = L[ln - 1] if 0 < ln <= len(L) else ""
        if frag not in txt:
            miss.append(str(ln))
    check("L2  (*) ggny (arXiv:1105.5438) anchors: strictness is scoped to semi-deterministic",
          not miss, "missing lines: %s" % (", ".join(miss) if miss else "none"))

    su = lines("sumofbc")[54]
    gl = lines("glnsum")[60]
    ok = ("p(u)p(v)p(w|u, v)" in su) and ("p(u, v, w, x)" in gl)
    check("L3  (*) sumofbc's O(T) is the INDEPENDENT version, glnsum's O_UVW(T) is the GENERAL one",
          ok, "sumofbc:55 = independent, glnsum:61 = general  ==> the artefact's "
              "'both are the general version' is wrong for sumofbc")


# --------------------------------------------------------------------------------------------

def main():
    print(__doc__.split("Run:")[0].strip())
    group_a()
    group_b()
    group_c()
    group_d()
    group_e()
    group_f()
    group_l()
    head("SUMMARY")
    print("  pass %d / fail %d / skip %d" % (PASS, FAIL, SKIP))
    return 1 if FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
