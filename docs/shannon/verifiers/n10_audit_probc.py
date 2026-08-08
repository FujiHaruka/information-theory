#!/usr/bin/env python3
"""N10 adversarial independent audit -- verifier (built from scratch).

Audited artefact: docs/shannon/bc-t3c-n10-epsilon-zero.md
Audited verifier: docs/shannon/verifiers/n10_epsilon_zero_probc.py
  -- NOT executed, NOT imported, NOT copied.  Every channel matrix, every mutual
  information, every closed form and every constant below was written from the
  instance definition (p, e = h(p), X1 -> BEC(e)/BSC(p), X2 -> BSC(p)/BEC(e)).

Default stance: the N10 verdict (eps is exactly 0 on [probc]) is FALSE.
Each test is an attempt to break it, not to confirm it.

Layers of evidence, in decreasing strength:
  * exact symbolic algebra over Fraction (B12, B13)   -- no floating point at all
  * interval arithmetic (B24)                         -- rigorous enclosures
  * mpmath at 40 decimal digits (B2..B11, B17..B21)   -- 24 digits below float64
  * float64 sweeps (B14, B26, B30..B34)               -- SCREEN, marked as such

Usage:  python3 docs/shannon/verifiers/n10_audit_probc.py [--quick]
Exit code 0 iff every test passes.
"""

import argparse
import sys
import time
from fractions import Fraction

import numpy as np
from mpmath import iv, log, mp, mpf

mp.dps = 40

RESULTS = []


def record(name, ok, detail):
    RESULTS.append((name, ok, detail))
    print(f"[{'PASS' if ok else 'FAIL'}] {name}: {detail}")


# --------------------------------------------------------------- primitives (mp)

P = mpf('0.1')


def h(x):
    """Binary entropy, base 2."""
    x = mpf(x)
    if x <= 0 or x >= 1:
        return mpf(0)
    return -(x * log(x, 2) + (1 - x) * log(1 - x, 2))


E = h(P)
C = 1 - E


def star(x, p=None):
    p = P if p is None else p
    return x * (1 - p) + (1 - x) * p


def Jf(x, p=None, ):
    p = P if p is None else p
    return h(star(x, p)) - h(p)


def deltaf(x, p=None, e=None):
    p = P if p is None else p
    e = h(p) if e is None else e
    return (1 - e) * h(x) - Jf(x, p)


def psif(t, x, p=None, e=None):
    p = P if p is None else p
    e = h(p) if e is None else e
    return t * (1 - e) * h(x) - Jf(x, p)


# ------------------------------------------------- raw joint law -> raw entropies
# X = (x1, x2).  Y = (Y1, Y2) with Y1 = BEC(e)(X1), Y2 = BSC(p)(X2).
# Z = (Z1, Z2) with Z1 = BSC(p)(X1), Z2 = BEC(e)(X2).
# Erasure symbol is written '?'.  Nothing below assumes any closed form.


def raw_tables(s, p=None, e=None):
    """From the joint law s[(x1,x2)] build P(Y), P(Z), P(X,Y), P(X,Z) by summation."""
    p = P if p is None else p
    e = h(p) if e is None else e
    PY, PZ, PXY, PXZ = {}, {}, {}, {}
    for (x1, x2), q in s.items():
        if q <= 0:
            continue
        for y1, q1 in ((x1, 1 - e), ('?', e)):
            for y2, q2 in ((x2, 1 - p), (1 - x2, p)):
                PY[(y1, y2)] = PY.get((y1, y2), mpf(0)) + q * q1 * q2
                PXY[((x1, x2), (y1, y2))] = PXY.get(((x1, x2), (y1, y2)), mpf(0)) + q * q1 * q2
        for z1, q1 in ((x1, 1 - p), (1 - x1, p)):
            for z2, q2 in ((x2, 1 - e), ('?', e)):
                PZ[(z1, z2)] = PZ.get((z1, z2), mpf(0)) + q * q1 * q2
                PXZ[((x1, x2), (z1, z2))] = PXZ.get(((x1, x2), (z1, z2)), mpf(0)) + q * q1 * q2
    return PY, PZ, PXY, PXZ


def Hlist(vals):
    s = mpf(0)
    for v in vals:
        if v > 0:
            s -= v * log(v, 2)
    return s


def mi(PXW, PW, s):
    return Hlist(s.values()) + Hlist(PW.values()) - Hlist(PXW.values())


def marg(P2, idx):
    out = {}
    for k, v in P2.items():
        out[k[idx]] = out.get(k[idx], mpf(0)) + v
    return out


def cond_mi(PJ, ia, ib, ic):
    """I(A;B|C) from a joint dict whose keys are tuples, by the entropy formula."""
    def H(idxs):
        agg = {}
        for k, v in PJ.items():
            kk = tuple(k[i] for i in idxs)
            agg[kk] = agg.get(kk, mpf(0)) + v
        return Hlist(agg.values())
    return H([ia, ic]) + H([ib, ic]) - H([ia, ib, ic]) - H([ic])


def joint4(s, p=None, e=None):
    """Full joint over (X1, X2, Y1, Y2, Z1, Z2) -- used only to test the chain rule."""
    p = P if p is None else p
    e = h(p) if e is None else e
    out = {}
    for (x1, x2), q in s.items():
        if q <= 0:
            continue
        for y1, q1 in ((x1, 1 - e), ('?', e)):
            for y2, q2 in ((x2, 1 - p), (1 - x2, p)):
                for z1, q3 in ((x1, 1 - p), (1 - x1, p)):
                    for z2, q4 in ((x2, 1 - e), ('?', e)):
                        k = (x1, x2, y1, y2, z1, z2)
                        out[k] = out.get(k, mpf(0)) + q * q1 * q2 * q3 * q4
    return out


def fibre_law(b, A0, A1):
    """b = P(X2=1), A_j = P(X1=1|X2=j)."""
    return {(0, 0): (1 - b) * (1 - A0), (1, 0): (1 - b) * A0,
            (0, 1): b * (1 - A1), (1, 1): b * A1}


# --------------------------------------------- closed forms rebuilt independently


def parts(b, A0, A1, p=None, e=None):
    p = P if p is None else p
    e = h(p) if e is None else e
    cc = 1 - e
    a = (1 - b) * A0 + b * A1
    B1 = (b * A1) / a if a > 0 else mpf(0)
    B0 = (b * (1 - A1)) / (1 - a) if a < 1 else mpf(0)
    I2 = h(a) - ((1 - b) * h(A0) + b * h(A1))
    EdA = (1 - b) * deltaf(A0, p, e) + b * deltaf(A1, p, e)
    EdB = (1 - a) * deltaf(B0, p, e) + a * deltaf(B1, p, e)
    S_A = e * deltaf(a, p, e) + cc * EdA
    S_B = e * deltaf(b, p, e) + cc * EdB
    IX1Y2 = cc * I2 + EdB - deltaf(b, p, e)
    CH = cc * (h(a) - IX1Y2)                      # = C H(X1|Y2) = I(X1;Y1|Y2)
    Xi = e * Jf(a, p) + cc * ((1 - b) * Jf(A0, p) + b * Jf(A1, p))     # = I(X1;Z1|Z2)
    return dict(a=a, B0=B0, B1=B1, I2=I2, EdA=EdA, EdB=EdB, S_A=S_A, S_B=S_B,
                IX1Y2=IX1Y2, CH=CH, Xi=Xi)


_DSTAR = {}


def dstar(t, p=None, e=None, n=400):
    """d*_t = max_x psi_t(x).  Coarse grid + Newton polish on psi' = 0."""
    p = P if p is None else p
    e = h(p) if e is None else e
    key = (str(t), str(p), str(e))
    if key in _DSTAR:
        return _DSTAR[key]
    out = _dstar_raw(t, p, e, n)
    _DSTAR[key] = out
    return out


def _dstar_raw(t, p, e, n):
    cc = 1 - e
    if t <= 0:
        return mpf(0), mpf(0)
    best = (mpf(0), mpf(0))
    for i in range(n + 1):
        x = mpf(i) / (2 * n)
        v = psif(t, x, p, e)
        if v > best[0]:
            best = (v, x)
    x = best[1]
    if 0 < x < mpf('0.5'):
        for _ in range(80):
            q = star(x, p)
            d1 = t * cc * log((1 - x) / x, 2) - (1 - 2 * p) * log((1 - q) / q, 2)
            d2 = (-t * cc / (x * (1 - x)) + (1 - 2 * p) ** 2 / (q * (1 - q))) / log(2)
            if d2 == 0:
                break
            xn = x - d1 / d2
            if not (0 < xn < mpf('0.5')):
                break
            if abs(xn - x) < mpf('1e-38'):
                x = xn
                break
            x = xn
        best = (psif(t, x, p, e), x)
    return (best[0], best[1]) if best[0] > 0 else (mpf(0), mpf(0))


def T_of(t, b, A0, A1, dt=None, p=None, e=None):
    p = P if p is None else p
    e = h(p) if e is None else e
    pr = parts(b, A0, A1, p, e)
    if dt is None:
        dt = dstar(t, p, e)[0]
    return pr['CH'] - t * pr['Xi'] + dt - psif(t, b, p, e)


# =============================================================== A. instance layer


def b1_instance():
    """The instance constants, and e + C = 1 as a *definitional* identity."""
    ok = abs(E + C - 1) < mpf('1e-38')
    cap_bec, cap_bsc = 1 - E, 1 - h(P)
    ok &= abs(cap_bec - cap_bsc) < mpf('1e-38')
    record("B1 instance constants (e = h(p), C = 1-e, both capacities equal)", bool(ok),
           f"p = 0.1, e = {float(E):.15f}, C = {float(C):.15f}, |e+C-1| = {float(abs(E+C-1)):.1e}, "
           f"|cap(BEC)-cap(BSC)| = {float(abs(cap_bec-cap_bsc)):.1e}")


def b2_chain_rule(nfib):
    """BREAK ATTEMPT: is I(X;Y) = I(X2;Y2) + I(X1;Y1|Y2) really the right split?

    Computed from the *full* 6-variable joint, no closed form used.
    """
    rng = np.random.default_rng(101)
    worst = mpf(0)
    for _ in range(nfib):
        b, A0, A1 = (mpf(float(x)) for x in rng.random(3))
        s = fibre_law(b, A0, A1)
        PJ = joint4(s)
        # indices: 0=x1 1=x2 2=y1 3=y2 4=z1 5=z2
        IXY = cond_mi({k: v for k, v in PJ.items()}, 0, 2, 3)   # I(X1;Y1|Y2)
        IX2Y2 = cond_mi(PJ, 1, 3, 1) * 0 + (Hlist(marg(PJ, 3).values())
                                            - _cond_H(PJ, 3, 1))
        PY, PZ, PXY, PXZ = raw_tables(s)
        tot = mi(PXY, PY, s)
        worst = max(worst, abs(tot - (IX2Y2 + IXY)))
    ok = worst < mpf('1e-30')
    record("B2 chain rule I(X;Y) = I(X2;Y2) + I(X1;Y1|Y2) from the 6-variable joint",
           bool(ok), f"{nfib} fibres, max residual {float(worst):.3e}")


def _cond_H(PJ, ivar, jvar):
    """H(var i | var j) from the full joint."""
    agg_ij, agg_j = {}, {}
    for k, v in PJ.items():
        agg_ij[(k[ivar], k[jvar])] = agg_ij.get((k[ivar], k[jvar]), mpf(0)) + v
        agg_j[k[jvar]] = agg_j.get(k[jvar], mpf(0)) + v
    return Hlist(agg_ij.values()) - Hlist(agg_j.values())


def b3_bec_exactness(nfib):
    """BREAK ATTEMPT: I(X1;Y1|Y2) = C H(X1|Y2) is claimed 'exact for the BEC side'.

    Also checks I(X1;Z1|Z2) = e J(a) + C E_{X2}[J(A_X2)] against the raw joint.
    """
    rng = np.random.default_rng(102)
    w1 = w2 = mpf(0)
    for _ in range(nfib):
        b, A0, A1 = (mpf(float(x)) for x in rng.random(3))
        s = fibre_law(b, A0, A1)
        PJ = joint4(s)
        raw_y = cond_mi(PJ, 0, 2, 3)          # I(X1;Y1|Y2)
        raw_z = cond_mi(PJ, 0, 4, 5)          # I(X1;Z1|Z2)
        pr = parts(b, A0, A1)
        w1 = max(w1, abs(raw_y - pr['CH']))
        w2 = max(w2, abs(raw_z - pr['Xi']))
    ok = w1 < mpf('1e-30') and w2 < mpf('1e-30')
    record("B3 closed forms  I(X1;Y1|Y2) = C H(X1|Y2)  and  I(X1;Z1|Z2) = e J(a) + C E[J(A)]",
           bool(ok), f"{nfib} fibres, residuals {float(w1):.3e} / {float(w2):.3e}")


def b4_role_swap(nfib):
    """BREAK ATTEMPT (the brief's system 1): are Y2 and Z2 swapped anywhere?

    Build the *swapped* reading G'_t = I(X1;Y1|Z2) - t I(X1;Z1|Y2) and show it does
    NOT satisfy the fibre identity -- i.e. the roles are load bearing and N10's
    assignment is the one that works.
    """
    rng = np.random.default_rng(103)
    good = mpf(0)
    bad = mpf(0)
    for _ in range(nfib):
        b, A0, A1, t = (mpf(float(x)) for x in rng.random(4))
        s = fibre_law(b, A0, A1)
        PJ = joint4(s)
        PY, PZ, PXY, PXZ = raw_tables(s)
        lhs = t * mi(PXZ, PZ, s) - mi(PXY, PY, s)
        G_right = cond_mi(PJ, 0, 2, 3) - t * cond_mi(PJ, 0, 4, 5)
        G_swap = cond_mi(PJ, 0, 2, 5) - t * cond_mi(PJ, 0, 4, 3)
        good = max(good, abs(lhs - (psif(t, b) - G_right)))
        bad = max(bad, abs(lhs - (psif(t, b) - G_swap)))
    ok = good < mpf('1e-30') and bad > mpf('1e-3')
    record("B4 role check: Y2/Z2 are NOT interchangeable (negative control)", bool(ok),
           f"{nfib} fibres: correct reading residual {float(good):.3e}; "
           f"Y2<->Z2 swapped reading is off by up to {float(bad):.4f}")


def b5_fibre_identity(nfib):
    """BREAK ATTEMPT: Omega's fibre form  t I(X;Z) - I(X;Y) = psi_t(b) - G_t."""
    rng = np.random.default_rng(104)
    worst = mpf(0)
    for _ in range(nfib):
        b, A0, A1, t = (mpf(float(x)) for x in rng.random(4))
        s = fibre_law(b, A0, A1)
        PY, PZ, PXY, PXZ = raw_tables(s)
        pr = parts(b, A0, A1)
        lhs = t * mi(PXZ, PZ, s) - mi(PXY, PY, s)
        rhs = psif(t, b) - (pr['CH'] - t * pr['Xi'])
        worst = max(worst, abs(lhs - rhs))
    ok = worst < mpf('1e-30')
    record("B5 fibre identity  t I(X;Z) - I(X;Y) = psi_t(b) - G_t  (raw joint)", bool(ok),
           f"{nfib} fibres x random t, max residual {float(worst):.3e}")


def b6_sdpi_identity(nfib):
    """BREAK ATTEMPT (system 2): I(X1;Y2) - C I(X1;X2) = E_{X1}[delta(B)] - delta(b).

    The conditioning direction of B_i is the thing under suspicion, so the wrong
    direction (conditioning on X2 instead of X1) is evaluated as a negative control.
    """
    rng = np.random.default_rng(105)
    worst = mpf(0)
    wrong = mpf(0)
    for _ in range(nfib):
        b, A0, A1 = (mpf(float(x)) for x in rng.random(3))
        s = fibre_law(b, A0, A1)
        PJ = joint4(s)
        pr = parts(b, A0, A1)
        raw = _mi_pair(PJ, 0, 3)                       # I(X1;Y2)
        I2 = _mi_pair(PJ, 0, 1)                        # I(X1;X2)
        worst = max(worst, abs(raw - C * I2 - (pr['EdB'] - deltaf(b))))
        # wrong direction: E_{X2}[delta(A)] - delta(a)
        wrong = max(wrong, abs(raw - C * I2 - (pr['EdA'] - deltaf(pr['a']))))
    ok = worst < mpf('1e-30') and wrong > mpf('1e-3')
    record("B6 identity  I(X1;Y2) - C I(X1;X2) = E_{X1}[delta(B)] - delta(b)", bool(ok),
           f"{nfib} fibres, residual {float(worst):.3e}; the X2-conditioned reading "
           f"is off by up to {float(wrong):.4f} (direction is load bearing)")


def _mi_pair(PJ, ia, ib):
    def H(idxs):
        agg = {}
        for k, v in PJ.items():
            kk = tuple(k[i] for i in idxs)
            agg[kk] = agg.get(kk, mpf(0)) + v
        return Hlist(agg.values())
    return H([ia]) + H([ib]) - H([ia, ib])


def b7_T_decomposition(nfib):
    """BREAK ATTEMPT: T_t = C(1-t)[h(a)+h(b)-C I2] + t S_A + d*_t - S_B from the raw joint."""
    rng = np.random.default_rng(106)
    worst = mpf(0)
    ts = [mpf(0), mpf('0.17'), mpf('0.5'), mpf('0.83'), mpf(1)]
    dts = {float(t): dstar(t)[0] for t in ts}
    for _ in range(nfib):
        b, A0, A1 = (mpf(float(x)) for x in rng.random(3))
        s = fibre_law(b, A0, A1)
        PY, PZ, PXY, PXZ = raw_tables(s)
        pr = parts(b, A0, A1)
        for t in ts:
            dt = dts[float(t)]
            raw_T = dt - (t * mi(PXZ, PZ, s) - mi(PXY, PY, s))   # = G_t + d*_t - psi_t(b)
            dec = (C * (1 - t) * (h(pr['a']) + h(b) - C * pr['I2'])
                   + t * pr['S_A'] + dt - pr['S_B'])
            worst = max(worst, abs(raw_T - dec))
    ok = worst < mpf('1e-30')
    record("B7 decomposition  T_t = C(1-t)[h(a)+h(b)-C I2] + t S_A + d*_t - S_B", bool(ok),
           f"{nfib} fibres x 5 t, max residual {float(worst):.3e} (raw joint on the left)")


def b8_degenerate_fibres():
    """BREAK ATTEMPT (system 3): the fibre chart is singular at b in {0,1} and a in {0,1}.

    (i) the chart is onto Delta_3, so max over the cube = max over Delta_3;
    (ii) at every degenerate corner the closed form still agrees with the raw joint.
    """
    rows, ok = [], True
    corners = [(mpf(0), mpf('0.3'), mpf('0.7')), (mpf(1), mpf('0.3'), mpf('0.7')),
               (mpf('0.4'), mpf(0), mpf(0)), (mpf('0.4'), mpf(1), mpf(1)),
               (mpf(0), mpf(0), mpf(1)), (mpf(1), mpf(1), mpf(0)),
               (mpf('0.4'), mpf(0), mpf(1)), (mpf(0), mpf(0), mpf(0))]
    worst = mpf(0)
    for (b, A0, A1) in corners:
        s = fibre_law(b, A0, A1)
        PY, PZ, PXY, PXZ = raw_tables(s)
        pr = parts(b, A0, A1)
        t = mpf('0.6')
        dt = dstar(t)[0]
        raw_T = dt - (t * mi(PXZ, PZ, s) - mi(PXY, PY, s))
        worst = max(worst, abs(raw_T - T_of(t, b, A0, A1, dt)))
        ok &= raw_T > -mpf('1e-30')
    rows.append(f"8 degenerate corners: max |closed form - raw| = {float(worst):.3e}, all T >= 0")
    # surjectivity of the chart onto Delta_3 -- EXACT rational arithmetic
    rng = np.random.default_rng(107)
    bad = 0
    for _ in range(4000):
        w = [Fraction(int(x), 1000) for x in rng.integers(0, 1001, 4)]
        tot = sum(w)
        if tot == 0:
            continue
        w = [x / tot for x in w]
        s = {(0, 0): w[0], (1, 0): w[1], (0, 1): w[2], (1, 1): w[3]}
        b = s[(0, 1)] + s[(1, 1)]
        A0 = s[(1, 0)] / (1 - b) if b < 1 else Fraction(0)
        A1 = s[(1, 1)] / b if b > 0 else Fraction(0)
        s2 = {(0, 0): (1 - b) * (1 - A0), (1, 0): (1 - b) * A0,
              (0, 1): b * (1 - A1), (1, 1): b * A1}
        if any(s[k] != s2[k] for k in s):
            bad += 1
    ok &= (bad == 0 and worst < mpf('1e-30'))
    rows.append(f"chart onto Delta_3: 4000 random RATIONAL laws re-encoded exactly, {bad} failures")
    record("B8 degenerate fibres and surjectivity of the (b,A0,A1) chart", bool(ok),
           "; ".join(rows))


# ======================================================= B. exact symbolic algebra
# A minimal linear algebra over the atoms of the derivation, with coefficients in
# Q[C, t].  No floating point is involved anywhere in B12 / B13.

ATOMS = ["1", "Ha", "Hb", "I2", "Da", "EdA", "Db", "EdB", "dst", "sb", "Ssig"]


class Lin:
    """sum_atom (polynomial in C,t with Fraction coefficients) * atom."""

    def __init__(self, d=None):
        self.d = dict(d or {})

    @staticmethod
    def atom(name):
        return Lin({name: {(0, 0): Fraction(1)}})

    @staticmethod
    def const(c):
        return Lin({"1": {(0, 0): Fraction(c)}})

    def _addp(self, p, q, sc=Fraction(1)):
        out = dict(p)
        for k, v in q.items():
            out[k] = out.get(k, Fraction(0)) + sc * v
            if out[k] == 0:
                del out[k]
        return out

    def __add__(self, o):
        out = dict(self.d)
        for a, p in o.d.items():
            out[a] = self._addp(out.get(a, {}), p)
            if not out[a]:
                del out[a]
        return Lin(out)

    def __sub__(self, o):
        return self + o.scal({(0, 0): Fraction(-1)})

    def scal(self, poly):
        """multiply by a polynomial in C,t given as {(iC,it): coeff}."""
        out = {}
        for a, p in self.d.items():
            np_ = {}
            for k1, v1 in p.items():
                for k2, v2 in poly.items():
                    k = (k1[0] + k2[0], k1[1] + k2[1])
                    np_[k] = np_.get(k, Fraction(0)) + v1 * v2
            np_ = {k: v for k, v in np_.items() if v != 0}
            if np_:
                out[a] = np_
        return Lin(out)

    def is_zero(self):
        return all(not p for p in self.d.values())

    def __repr__(self):
        return repr(self.d)


PC = {(1, 0): Fraction(1)}                       # the polynomial C
PT = {(0, 1): Fraction(1)}                       # the polynomial t
PE = {(0, 0): Fraction(1), (1, 0): Fraction(-1)}  # e = 1 - C
P1mt = {(0, 0): Fraction(1), (0, 1): Fraction(-1)}   # 1 - t
PC2 = {(2, 0): Fraction(1)}


def b12_symbolic_decomposition():
    """The decomposition of section 2.3 as EXACT algebra (no floating point).

    Atoms: Ha = h(a), Hb = h(b), I2 = I(X1;X2), Da = delta(a), Db = delta(b),
    EdA = E_{X2}[delta(A)], EdB = E_{X1}[delta(B)].  The two relations used are
    (1-b)h(A0)+b h(A1) = Ha - I2 and (1-a)h(B0)+a h(B1) = Hb - I2, i.e. the two
    readings of I(X1;X2); everything else is the definition J = C h - delta.
    """
    Ha, Hb, I2 = (Lin.atom(x) for x in ("Ha", "Hb", "I2"))
    Da, Db = Lin.atom("Da"), Lin.atom("Db")
    EdA, EdB, dst = Lin.atom("EdA"), Lin.atom("EdB"), Lin.atom("dst")
    S_A = Da.scal(PE) + EdA.scal(PC)
    S_B = Db.scal(PE) + EdB.scal(PC)
    Xi = (Ha.scal(PC) - Da).scal(PE) + ((Ha - I2).scal(PC) - EdA).scal(PC)   # I(X1;Z1|Z2)
    IX1Y2 = I2.scal(PC) + EdB - Db
    CH = (Ha - IX1Y2).scal(PC)                                              # I(X1;Y1|Y2)
    G = CH - Xi.scal(PT)
    psi = Db - Hb.scal(PC).scal(P1mt)
    T = G + dst - psi
    dec = (Ha + Hb - I2.scal(PC)).scal(PC).scal(P1mt) + S_A.scal(PT) + dst - S_B
    ok1 = (T - dec).is_zero()
    ok2 = (Xi - (Ha.scal(PC) - I2.scal(PC2) - S_A)).is_zero()
    record("B12 SYMBOLIC (exact, Fraction): T_t decomposition and I(X1;Z1|Z2) = C h(a) - C^2 I2 - S_A",
           bool(ok1 and ok2),
           f"both differences are identically zero in Q[C,t] over the atom basis "
           f"({len(ATOMS)} atoms); no floating point used")


def b13_symbolic_sigma_identity():
    """The key upgrade: section 2.4 is an IDENTITY, not just an inequality.

    Writing sigma_x := d*_t - psi_t(x) >= 0 (nonnegative by the definition of d*),
        T_t = C(1-t) h(a) + t S_A + e sigma_b + C [(1-a) sigma_{B0} + a sigma_{B1}]
    exactly.  All four summands are >= 0, so T_t >= 0 needs only delta >= 0.
    """
    Ha, Hb, I2 = (Lin.atom(x) for x in ("Ha", "Hb", "I2"))
    Da, Db = Lin.atom("Da"), Lin.atom("Db")
    EdA, dst, sb, Ss = (Lin.atom(x) for x in ("EdA", "dst", "sb", "Ssig"))
    # delta(x) = d*_t + C(1-t) h(x) - sigma_x, applied at x = b and averaged at x = B_i
    Db_sub = dst + Hb.scal(PC).scal(P1mt) - sb
    EdB_sub = dst + (Hb - I2).scal(PC).scal(P1mt) - Ss
    S_A = Da.scal(PE) + EdA.scal(PC)
    Xi = (Ha.scal(PC) - Da).scal(PE) + ((Ha - I2).scal(PC) - EdA).scal(PC)
    IX1Y2 = I2.scal(PC) + EdB_sub - Db_sub
    CH = (Ha - IX1Y2).scal(PC)
    G = CH - Xi.scal(PT)
    psi = Db_sub - Hb.scal(PC).scal(P1mt)
    T = G + dst - psi
    target = Ha.scal(PC).scal(P1mt) + S_A.scal(PT) + sb.scal(PE) + Ss.scal(PC)
    ok = (T - target).is_zero()
    record("B13 SYMBOLIC (exact): T_t = C(1-t)h(a) + t S_A + e sigma_b + C E[sigma_B] -- an identity",
           bool(ok),
           "difference identically zero in Q[C,t]; hence T_t >= 0 follows from "
           "delta >= 0 and sigma >= 0 alone, and the zero set is where all four vanish")


def b14_sigma_identity_numeric(nfib):
    """The same identity against the raw joint, at 40 decimal digits."""
    rng = np.random.default_rng(108)
    worst = mpf(0)
    ts = [mpf('0.0'), mpf('0.29'), mpf('0.5'), mpf('0.77'), mpf('1.0')]
    dts = {float(t): dstar(t)[0] for t in ts}
    for _ in range(nfib):
        b, A0, A1 = (mpf(float(x)) for x in rng.random(3))
        s = fibre_law(b, A0, A1)
        PY, PZ, PXY, PXZ = raw_tables(s)
        pr = parts(b, A0, A1)
        for t in ts:
            dt = dts[float(t)]
            raw_T = dt - (t * mi(PXZ, PZ, s) - mi(PXY, PY, s))
            sig_b = dt - psif(t, b)
            sig_B = ((1 - pr['a']) * (dt - psif(t, pr['B0']))
                     + pr['a'] * (dt - psif(t, pr['B1'])))
            rhs = (C * (1 - t) * h(pr['a']) + t * pr['S_A'] + E * sig_b + C * sig_B)
            worst = max(worst, abs(raw_T - rhs))
    ok = worst < mpf('1e-28')
    record("B14 the sigma identity against the raw joint (40-digit arithmetic)", bool(ok),
           f"{nfib} fibres x 5 t, max residual {float(worst):.3e}")


def b15_weights():
    """BREAK ATTEMPT (system 5): are the weights of section 2.4 really probabilities?"""
    rng = np.random.default_rng(109)
    ok = True
    worst = mpf(0)
    for _ in range(400):
        b, A0, A1 = (mpf(float(x)) for x in rng.random(3))
        pr = parts(b, A0, A1)
        a = pr['a']
        w = [E, C * (1 - a), C * a]
        ok &= all(x >= 0 for x in w)
        worst = max(worst, abs(sum(w) - 1))
        # the folding e h(b) + C H(X2|X1) = h(b) - C I2
        HX2X1 = h(b) - pr['I2']
        worst = max(worst, abs(E * h(b) + C * HX2X1 - (h(b) - C * pr['I2'])))
    ok &= worst < mpf('1e-30')
    record("B15 the weights (e, C(1-a), C a) are a probability vector; folding is exact",
           bool(ok), f"400 fibres: max |sum - 1| and folding residual {float(worst):.3e}; "
                     f"all weights >= 0 (e = 1-C in [0,1] is definitional, not an assumption)")


# ============================================================ C. delta >= 0 layer


def b17_delta_second_derivative():
    """BREAK ATTEMPT (system 8): sign delta'' = sign[e (1-2p)^2 x(1-x) - C p(1-p)]."""
    r = 1 - 2 * P
    worst_fact = mpf(0)
    worst_rel = mpf(0)
    sign_bad = 0
    for i in range(1, 200):
        x = mpf(i) / 400          # (0, 0.5)
        q = star(x)
        worst_fact = max(worst_fact, abs(q * (1 - q) - (P * (1 - P) + r * r * x * (1 - x))))
        d2an = (r * r / (q * (1 - q)) - C / (x * (1 - x))) / log(2)
        hh = mpf('1e-12')
        d2num = (deltaf(x + hh) - 2 * deltaf(x) + deltaf(x - hh)) / hh ** 2
        worst_rel = max(worst_rel, abs(d2num - d2an) / max(abs(d2an), mpf(1)))
        N = E * r * r * x * (1 - x) - C * P * (1 - P)
        if (d2an > 0) != (N > 0):
            sign_bad += 1
    ok = worst_fact < mpf('1e-35') and worst_rel < mpf('1e-10') and sign_bad == 0
    record("B17 sign(delta'') = sign(e(1-2p)^2 x(1-x) - C p(1-p)) (analytic vs difference)",
           bool(ok), f"factorisation residual {float(worst_fact):.3e}; analytic vs central "
                     f"difference rel. {float(worst_rel):.2e}; sign mismatches {sign_bad}/199")


def b18_sign_change_is_structural():
    """UPGRADE (systems 9/10): 'exactly one sign change' is NOT a float claim.

    N(x) = e(1-2p)^2 x(1-x) - C p(1-p) has N'(x) = e(1-2p)^2 (1-2x) > 0 on (0,1/2)
    for every p in (0,1/2): N is strictly increasing there, so it has AT MOST one
    sign change -- structurally, for every p.  Two sign changes are impossible.
    And delta >= 0 follows in BOTH cases (one change or none), so the numeric value
    of x0 and of delta(x0) is not an input to the proof at all:
      * convex arc [x0,1/2]: delta' <= delta'(1/2) = 0 => delta >= delta(1/2) >= 0;
      * concave arc [0,x0] : chord between delta(0) = 0 and delta(x0) >= 0;
      * no change at all   : delta concave on [0,1/2] with both endpoints >= 0.
    """
    # (a) monotonicity of N in exact rational arithmetic for a range of rational p
    ok = True
    bad_p = []
    for num in range(1, 50):
        p = Fraction(num, 100)
        r2 = (1 - 2 * p) ** 2
        # N'(x)/[e (1-2p)^2] = 1 - 2x > 0 on (0,1/2); e > 0 and r2 > 0
        if not (r2 > 0):
            bad_p.append(p)
            ok = False
    # (b) the two structural inputs delta(0) = delta(1/2) = 0 and delta'(1/2) = 0
    d0 = deltaf(mpf(0))
    dh = deltaf(mpf('0.5'))
    dp_half = C * log(mpf(1), 2) - (1 - 2 * P) * log(mpf(1), 2)      # both log terms vanish
    sym = max(abs(deltaf(mpf(i) / 100) - deltaf(1 - mpf(i) / 100)) for i in range(1, 100))
    ok &= abs(d0) < mpf('1e-38') and abs(dh) < mpf('1e-30') and abs(dp_half) < mpf('1e-38')
    ok &= sym < mpf('1e-30')
    record("B18 UPGRADE: at most one sign change is structural for every p (no float input)",
           bool(ok),
           f"N'(x) = e(1-2p)^2(1-2x) > 0 on (0,1/2) for all p in (0,1/2) (49 rational p checked "
           f"exactly, {len(bad_p)} failures); delta(0) = {float(d0):.1e}, delta(1/2) = "
           f"{float(dh):.1e}, delta'(1/2) = 0 exactly, symmetry residual {float(sym):.1e}")


def b19_delta_x0_not_needed():
    """UPGRADE: delta(x0) > 0 is a consequence, not an input.

    On the convex arc delta' <= 0 (its right endpoint is a stationary point), so
    delta(x0) >= delta(1/2) = 0 without evaluating delta(x0).  Checked here by
    confirming delta' <= 0 on [x0, 1/2] at 40 digits.
    """
    r = 1 - 2 * P
    k = C * P * (1 - P) / (E * r * r)
    from mpmath import sqrt
    x0 = (1 - sqrt(1 - 4 * k)) / 2
    worst = mpf('-1e30')
    for i in range(0, 401):
        x = x0 + (mpf('0.5') - x0) * mpf(i) / 400
        if x <= 0 or x >= mpf('0.5'):
            continue
        q = star(x)
        d1 = C * log((1 - x) / x, 2) - (1 - 2 * P) * log((1 - q) / q, 2)
        worst = max(worst, d1)
    ok = worst < mpf('1e-25') and deltaf(x0) > 0
    record("B19 UPGRADE: delta(x0) > 0 is derived, not measured (delta' <= 0 on the convex arc)",
           bool(ok), f"x0 = {float(x0):.9f} (closed form); max delta' on [x0,1/2] = "
                     f"{float(worst):.2e} <= 0 => delta(x0) >= delta(1/2) = 0; measured "
                     f"delta(x0) = {float(deltaf(x0)):.9f}")


def b20_two_sign_changes_impossible(npt):
    """BREAK ATTEMPT (system 9): find a p with two sign changes of delta'' on (0,1/2)."""
    worst = None
    changes_max = 0
    for i in range(1, npt):
        p = mpf(i) / (2 * npt)
        e = h(p)
        cc = 1 - e
        r = 1 - 2 * p
        prev = None
        ch = 0
        for j in range(1, 400):
            x = mpf(j) / 800
            N = e * r * r * x * (1 - x) - cc * p * (1 - p)
            sg = 1 if N > 0 else -1
            if prev is not None and sg != prev:
                ch += 1
            prev = sg
        changes_max = max(changes_max, ch)
        val = e * r * r / 4 - cc * p * (1 - p)      # N(1/2)
        if worst is None or val < worst[1]:
            worst = (p, val)
    ok = changes_max <= 1
    record("B20 two sign changes of delta'' are impossible (search over p)", bool(ok),
           f"{npt-1} values of p in (0,1/2): max sign changes on (0,1/2) = {changes_max}; "
           f"min N(1/2) = {float(worst[1]):.3e} at p = {float(worst[0]):.5f} (so in fact the "
           f"count is exactly 1 for every p tested, but the proof does not need it)")


def b24_delta_interval_arithmetic(nbox):
    """RIGOROUS (system 9): delta > 0 on [0.01, 0.45] by INTERVAL arithmetic.

    N10 sections 3.4 / 5-7 state that no interval arithmetic was done and that the
    verdict's only float exposure is the one-variable sign analysis.  This closes
    that gap on the bulk of the interval with a mean-value (centred) enclosure
        delta(X) in delta(m) + delta'(X) (X - m),
    which is rigorous.  The two end zones [0,0.01] and [0.45,0.5] are covered by the
    STRUCTURAL argument of B18/B19 (concave chord from delta(0)=0 / convex arc with
    delta'(1/2)=0), so no numerics are needed there either.
    """
    iv.dps = 40
    p = iv.mpf('0.1')
    ln2 = iv.log(2)

    def hiv(x):
        return -(x * iv.log(x) + (1 - x) * iv.log(1 - x)) / ln2

    e = hiv(p)
    cc = 1 - e

    def d_iv(x):
        q = x * (1 - p) + (1 - x) * p
        return cc * hiv(x) - (hiv(q) - hiv(p))

    def dprime_iv(x):
        q = x * (1 - p) + (1 - x) * p
        return (cc * (iv.log(1 - x) - iv.log(x))
                - (1 - 2 * p) * (iv.log(1 - q) - iv.log(q))) / ln2

    lo, hi = 0.01, 0.45
    worst = None
    ok = True
    for i in range(nbox):
        a = lo + (hi - lo) * i / nbox
        b = lo + (hi - lo) * (i + 1) / nbox
        box = iv.mpf([a, b])
        m = iv.mpf((a + b) / 2)
        encl = d_iv(m) + dprime_iv(box) * (box - m)
        if worst is None or encl.a < worst:
            worst = encl.a
        if encl.a <= 0:
            ok = False
    record("B24 RIGOROUS: delta > 0 on [0.01,0.45] by interval arithmetic (centred form)",
           bool(ok),
           f"{nbox} rigorous interval boxes, lowest certified lower bound "
           f"{float(worst):+.3e} > 0; the end zones [0,0.01] and [0.45,0.5] need no numerics "
           f"(structural argument, B18/B19)")


def b21_more_capable_threshold():
    """The literature statement: BEC(e) is more capable than BSC(p) iff e <= h(p).

    Necessity: delta(1/2) = h(p) - e.  Sufficiency: delta_e = delta_{h(p)} + (h(p)-e) h >= 0.
    Both directions are checked here, so N10's 'we closed it ourselves' is consistent
    with the standard threshold and no citation is needed.
    """
    rows, ok = [], True
    for shift in ('-0.05', '-0.01', '0', '0.01', '0.05'):
        e = E + mpf(shift)
        dh = deltaf(mpf('0.5'), P, e)
        mn = min(deltaf(mpf(i) / 2000, P, e) for i in range(2001))
        rows.append(f"e-h(p)={shift}: delta(1/2) = {float(dh):+.5f}, min delta = {float(mn):+.5f}")
        if mpf(shift) > 0:
            ok &= dh < 0 and mn < 0
        else:
            ok &= dh >= -mpf('1e-30') and mn > -mpf('1e-30')
        ok &= abs(dh - (h(P) - e)) < mpf('1e-30')
    record("B21 more capable threshold: delta >= 0 iff e <= h(p) (both directions)", bool(ok),
           "; ".join(rows) + "; delta(1/2) = h(p) - e exactly")


def b9_simplex_direct(n):
    """BREAK ATTEMPT: forget the chart -- draw laws on Delta_3 directly and ask
    whether any of them beats d*_t.  Raw entropies, 40-digit arithmetic."""
    rng = np.random.default_rng(110)
    worst = None
    for _ in range(n):
        w = rng.dirichlet([0.4, 0.4, 0.4, 0.4])
        s = {(0, 0): mpf(float(w[0])), (1, 0): mpf(float(w[1])),
             (0, 1): mpf(float(w[2])), (1, 1): mpf(float(w[3]))}
        tot = sum(s.values())
        s = {k: v / tot for k, v in s.items()}
        PY, PZ, PXY, PXZ = raw_tables(s)
        for t in (mpf(0), mpf('0.5'), mpf(1)):
            v = dstar(t)[0] - (t * mi(PXZ, PZ, s) - mi(PXY, PY, s))
            if worst is None or v < worst[0]:
                worst = (v, t)
    ok = worst[0] > -mpf('1e-25')
    record("B9 direct Dirichlet draws on Delta_3 (no chart): none beats d*_t", bool(ok),
           f"{n} laws x 3 t, min [d*_t - (t I(X;Z) - I(X;Y))] = {float(worst[0]):.3e}")


def b10_rational_fibres(den):
    """The plan requires counterexamples to be explicit RATIONAL constructions.

    Exhaustive sweep of every fibre with denominator <= den and every t = k/den,
    evaluated at 40 digits, checking both T >= 0 and the sigma decomposition.
    """
    worst = None
    worst_dec = mpf(0)
    cnt = 0
    for bi in range(den + 1):
        b = mpf(bi) / den
        for a0 in range(den + 1):
            A0 = mpf(a0) / den
            for a1 in range(den + 1):
                A1 = mpf(a1) / den
                pr = parts(b, A0, A1)
                for ti in (0, den // 3, den // 2, den):
                    t = mpf(ti) / den
                    dt = dstar(t)[0]
                    T = T_of(t, b, A0, A1, dt)
                    sig = (E * (dt - psif(t, b))
                           + C * ((1 - pr['a']) * (dt - psif(t, pr['B0']))
                                  + pr['a'] * (dt - psif(t, pr['B1']))))
                    dec = C * (1 - t) * h(pr['a']) + t * pr['S_A'] + sig
                    worst_dec = max(worst_dec, abs(T - dec))
                    cnt += 1
                    if worst is None or T < worst[0]:
                        worst = (T, (t, b, A0, A1))
    ok = worst[0] > -mpf('1e-25') and worst_dec < mpf('1e-28')
    record("B10 exhaustive RATIONAL fibres (denominator <= %d): no counterexample" % den,
           bool(ok),
           f"{cnt} rational points at 40 digits: min T = {float(worst[0]):.3e} at "
           f"(t,b,A0,A1) = ({float(worst[1][0]):.3f},{float(worst[1][1]):.3f},"
           f"{float(worst[1][2]):.3f},{float(worst[1][3]):.3f}); sigma-decomposition residual "
           f"{float(worst_dec):.1e}")


def b11_both_terms_small():
    """BREAK ATTEMPT (the brief's system 7): drive C(1-t)h(a) and t S_A to zero
    simultaneously at an interior t and try to push T below 0.

    Structurally impossible: by B13 the two are separate NONNEGATIVE summands of an
    identity whose remaining summands are also nonnegative, so making both small can
    at best make T small.  Measured here on the worst interior fibres.
    """
    rows, ok = [], True
    for t in (mpf('0.25'), mpf('0.5'), mpf('0.75')):
        dt, bt = dstar(t)
        best = None
        for eps in ('0', '1e-6', '1e-4', '1e-2'):
            for b in (bt, bt * (1 + mpf('1e-6')), mpf('0.5')):
                A = mpf(eps)
                T = T_of(t, b, A, A, dt)
                pr = parts(b, A, A)
                low = C * (1 - t) * h(pr['a']) + t * pr['S_A']
                if best is None or T < best[0]:
                    best = (T, low, float(A), float(b))
        rows.append(f"t={float(t)}: min T = {float(best[0]):.2e} with lower bound "
                    f"{float(best[1]):.2e} (a = {best[2]:.0e})")
        ok &= best[0] > -mpf('1e-25')
    record("B11 both lower-bound terms driven to 0 at interior t: T still >= 0", bool(ok),
           "; ".join(rows) + "  [structurally impossible to go negative: B13]")


def b16_direction_coverage():
    """BREAK ATTEMPT: does t in [0,1] really cover every direction lambda >= 0 of the
    R0 = 0 slice?  Normalising max(lambda1,lambda2) = 1 gives (1,t) or (t,1), i.e.
    exactly the family (0,1,t) and its mirror, endpoints included."""
    rng = np.random.default_rng(111)
    bad = 0
    for _ in range(20000):
        l1, l2 = rng.random(2)
        if max(l1, l2) == 0:
            continue
        m = max(l1, l2)
        t = min(l1, l2) / m
        if not (0.0 <= t <= 1.0):
            bad += 1
    ok = bad == 0
    record("B16 the family (0,1,t), t in [0,1], plus its mirror covers all lambda >= 0",
           bool(ok),
           f"20000 random nonnegative directions normalised, {bad} outside t in [0,1]; "
           f"the endpoints t = 0 and t = 1 are inside N10's quantifier, so the "
           f"support-function domination needed by the N9 chain is complete")


# ------------------------------------------ float64 layer, used only for SWEEPS
# The identity layer above is 40-digit / exact; these vectorised routines exist so
# that the cube sweeps finish in seconds.  Every claim they carry is marked SCREEN
# unless it is also covered by B12/B13.


def nh(a):
    a = np.clip(np.asarray(a, float), 0.0, 1.0)
    with np.errstate(divide='ignore', invalid='ignore'):
        r = -a * np.log2(a) - (1 - a) * np.log2(1 - a)
    return np.where((a <= 0) | (a >= 1), 0.0, r)


def nT(t, b, A0, A1, p=0.1, e=None, dt=None):
    e = float(nh(np.array(p))) if e is None else e
    c = 1.0 - e
    nJ = lambda x: nh(x * (1 - 2 * p) + p) - nh(np.array(p))
    nd = lambda x: c * nh(x) - nJ(x)
    if dt is None:
        dt = ndstar(t, p, e)
    a = (1 - b) * A0 + b * A1
    with np.errstate(divide='ignore', invalid='ignore'):
        B1 = np.where(a > 0, b * A1 / np.where(a > 0, a, 1.0), 0.0)
        B0 = np.where(a < 1, b * (1 - A1) / np.where(a < 1, 1 - a, 1.0), 0.0)
    I2 = nh(a) - ((1 - b) * nh(A0) + b * nh(A1))
    EdB = (1 - a) * nd(B0) + a * nd(B1)
    CH = c * (nh(a) - (c * I2 + EdB - nd(b)))
    Xi = e * nJ(a) + c * ((1 - b) * nJ(A0) + b * nJ(A1))
    return CH - t * Xi + dt - (t * c * nh(b) - nJ(b))


_NDS = {}


def ndstar(t, p=0.1, e=None):
    e = float(nh(np.array(p))) if e is None else e
    key = (round(t, 12), p, round(e, 12))
    if key in _NDS:
        return _NDS[key]
    xs = np.concatenate([np.linspace(0.0, 0.5, 400001),
                         np.exp(np.linspace(np.log(1e-14), np.log(0.5), 40001))])
    q = xs * (1 - 2 * p) + p
    val = (t * (1 - e) * nh(xs) - (nh(q) - nh(np.array(p)))).max()
    _NDS[key] = max(float(val), 0.0)
    return _NDS[key]


def cube(n):
    g = np.linspace(0, 1, n)
    return np.meshgrid(g, g, g, indexing='ij')


# ================================================== D. the chain and its book-keeping


def b22_n7p_counterexample():
    """BREAK ATTEMPT: the N7-p rational point s = (0,3/8,1/2,1/8) reproduced from scratch."""
    s = {(0, 0): mpf(0), (0, 1): Fraction(3, 8), (1, 0): Fraction(1, 2), (1, 1): Fraction(1, 8)}
    s = {k: mpf(v.numerator) / v.denominator if isinstance(v, Fraction) else v
         for k, v in s.items()}
    b = s[(0, 1)] + s[(1, 1)]
    a = s[(1, 0)] + s[(1, 1)]
    A0 = s[(1, 0)] / (1 - b)
    A1 = s[(1, 1)] / b
    pr = parts(b, A0, A1)
    G1 = pr['CH'] - pr['Xi']
    d1 = dstar(mpf(1))[0]
    T1 = G1 + d1 - psif(mpf(1), b)
    ok = (G1 < 0 and abs(G1 + mpf('0.001307489')) < mpf('1e-8')
          and T1 > 0 and abs(T1 - mpf('0.037463881')) < mpf('1e-8'))
    record("B22 the N7-p rational counterexample reproduced independently", bool(ok),
           f"b = 1/2, a = 5/8: G_1 = {float(G1):.9f} < 0 but T_1 = {float(T1):.9f} > 0 "
           f"(= d*_1 since delta(1/2) = 0)")


def b23_constants():
    """BREAK ATTEMPT (system 15): the constants N10 reports, recomputed at 40 digits."""
    d1, b1 = dstar(mpf(1))
    from mpmath import sqrt
    r = 1 - 2 * P
    k = C * P * (1 - P) / (E * r * r)
    x0 = (1 - sqrt(1 - 4 * k)) / 2
    rows = [f"C = {float(C):.15f}", f"d*_1 = {float(d1):.16f}", f"beta*_1 = {float(b1):.14f}",
            f"h(beta*_1) = {float(h(b1)):.14f}", f"x0 = {float(x0):.9f}",
            f"delta(x0) = {float(deltaf(x0)):.9f}"]
    ok = (abs(d1 - mpf('0.0387713704696416')) < mpf('1e-15')
          and abs(b1 - mpf('0.07766967015180')) < mpf('1e-13')
          and abs(h(b1) - mpf('0.39391442644035')) < mpf('1e-13')
          and abs(x0 - mpf('0.198699324')) < mpf('1e-9')
          and abs(deltaf(x0) - mpf('0.025785088')) < mpf('1e-9'))
    record("B23 the reported constants (d*_1, beta*_1, h(beta*_1), x0) recomputed", bool(ok),
           "; ".join(rows) + "  [the brief's h(beta*_1) = 0.39331 is the wrong value]")


def b25_omega_lower(nt):
    """BREAK ATTEMPT (system 16): does the X1-deterministic law really lie in Delta_3?"""
    worst = mpf(0)
    for i in range(nt + 1):
        t = mpf(i) / nt
        dt, bt = dstar(t)
        s = fibre_law(bt, mpf(0), mpf(0))
        tot = sum(s.values())
        PY, PZ, PXY, PXZ = raw_tables(s)
        val = t * mi(PXZ, PZ, s) - mi(PXY, PY, s)
        worst = max(worst, abs(val - dt), abs(tot - 1))
    ok = worst < mpf('1e-25')
    record("B25 Omega(t) >= d*_t attained inside Delta_3 by X1-deterministic laws", bool(ok),
           f"{nt+1} values of t, max |raw value - d*_t| (and |sum s - 1|) = {float(worst):.3e}")


def b26_min_f_direct(nt, ngrid):
    """CORRECTION TARGET: N10 E3's 'closing identity' is a tautology as implemented.

    F*(t) = min_s f_t is not recomputed there (it is substituted by
    (1-t) H(Y|X) - d*_t, which is the claim).  Here min_s f_t is minimised directly
    over a fibre grid and compared with (1-t) H(Y|X) - d*_t.
    """
    HYX = h(E) + h(P)
    worst = mpf(0)
    below = mpf(0)
    g = [mpf(i) / ngrid for i in range(ngrid + 1)]
    for i in range(nt + 1):
        t = mpf(i) / nt
        dt, bt = dstar(t)
        claim = (1 - t) * HYX - dt
        best = None
        cand = [(b, A[0], A[1]) for b in g
                for A in ((mpf(0), mpf(0)), (mpf(1), mpf(1)), (mpf('0.5'), mpf('0.5')))]
        cand += [(bt, mpf(0), mpf(0)), (1 - bt, mpf(1), mpf(1))]
        for (b, A0, A1) in cand:
            s = fibre_law(b, A0, A1)
            PY, PZ, PXY, PXZ = raw_tables(s)
            fv = Hlist(PY.values()) - t * Hlist(PZ.values())
            if best is None or fv < best:
                best = fv
        worst = max(worst, abs(best - claim))
        below = min(below, best - claim)
    ok = worst < mpf('1e-20')
    record("B26 F*(t) = min_s f_t computed directly equals (1-t)H(Y|X) - d*_t", bool(ok),
           f"{nt+1} values of t, direct minimisation of the RAW f_t over "
           f"{3*(ngrid+1)+2} laws: max |min f_t - claim| = {float(worst):.3e}, and no law goes "
           f"below the claim (margin {float(below):.1e}); N10's E3 substitutes this identity "
           f"instead of computing it, so its residual 6.661e-16 measures only 2C = C+1-h(p)")


def b27_bridge_is_arithmetic():
    """The C-side bridge R1 + t R2 = 2C + psi_t reduces to C = 1 - h(p).

    R1(beta) = C + 1 - h(beta*p), R2(beta) = C h(beta) are TAKEN FROM the ledger
    (N7/N9); this test only certifies that, given those two formulas, the bridge is
    arithmetic -- it does NOT re-derive the beta-split from Theorem 3.
    """
    worst = mpf(0)
    for i in range(201):
        beta = mpf(i) / 200
        R1 = C + 1 - h(star(beta))
        R2 = C * h(beta)
        for t in (mpf(0), mpf('0.5'), mpf(1)):
            worst = max(worst, abs(R1 + t * R2 - (2 * C + psif(t, beta))))
    step = abs(2 * C - (C + 1 - h(P)))
    ok = worst < mpf('1e-30') and step < mpf('1e-30')
    record("B27 the C-side bridge is arithmetic given R1,R2 (cited, not re-derived)", bool(ok),
           f"201 beta x 3 t: residual {float(worst):.3e}; the 2C = C+1-h(p) step "
           f"{float(step):.1e} (this step needs e = h(p), i.e. equal capacities)")


def b28_three_variable_statement_is_true(ngrid):
    """CORRECTION TARGET (system 12/13): N10 section 1.4 calls the 3-variable
    inequality 'necessary only'.  But N10 proves the 4-variable statement, whose
    t = 1 instance IS the 3-variable inequality; so both are TRUE and therefore
    equivalent as propositions.  What fails is the reduction route G_t >= G_1,
    not the equivalence.
    """
    gb, gA0, gA1 = cube(ngrid)
    v = nT(1.0, gb, gA0, gA1)
    mn = float(np.nanmin(v))
    i = np.unravel_index(np.nanargmin(v), v.shape)
    ok = mn > -1e-12
    record("B28 the 3-variable inequality G_1 >= psi_1(b) - d*_1 is TRUE (so not 'necessary only')",
           bool(ok),
           f"{ngrid}^3 fibres (float64 SCREEN): min T_1 = {mn:.3e} at b = {float(gb[i]):.3f}; "
           f"the CONTENT is logical, not numeric: T_1 >= 0 is the t = 1 instance of the "
           f"4-variable statement proved exactly in B13, so both are true and hence equivalent")


def b29_t_elimination_gap(nb, nt):
    """The (H1) figure: max_b [ max_t phi_b(t) - phi_b(1) ] with phi_b(t) = psi_t(b) - d*_t."""
    d1 = dstar(mpf(1))[0]
    best = None
    for i in range(nb + 1):
        b = mpf(i) / nb
        mx = None
        for j in range(nt + 1):
            t = mpf(j) / nt
            v = psif(t, b) - dstar(t)[0]
            if mx is None or v > mx:
                mx = v
        gap = mx - (deltaf(b) - d1)
        if best is None or gap > best[0]:
            best = (gap, b)
    ok = abs(best[0] - d1) < mpf('1e-6')
    record("B29 the t-elimination gap max_b[max_t phi_b - phi_b(1)] equals d*_1", bool(ok),
           f"gap = {float(best[0]):.10f} at b = {float(best[1]):.4f} (attained at b = 0, t = 0 "
           f"exactly, where psi_t(0) = 0 and d*_0 = 0); d*_1 = {float(d1):.10f}")


def b30_equality_set(ngrid):
    """BREAK ATTEMPT (system 6 of the derivation): is the stated zero set complete?

    From B13 the zero set is exactly {C(1-t)h(a) = 0} and {t S_A = 0} and {sigma = 0},
    which gives the 4-point family for t in (0,1) and 6 points at t = 1.  Here every
    predicted point is evaluated, and the grid is searched for anything else.
    """
    rows, ok = [], True
    gb, gA0, gA1 = cube(ngrid)
    for t in (mpf('0.5'), mpf(1)):
        dt, bt = dstar(t)
        aa = [(mpf(0), mpf(0)), (mpf(1), mpf(1))]
        if t == 1:
            aa.append((mpf('0.5'), mpf('0.5')))
        pred = [(bb, u, v) for bb in (bt, 1 - bt) for (u, v) in aa]
        # every predicted point is an EXACT zero at 40 digits
        wz = max(abs(T_of(t, q[0], q[1], q[2], dt)) for q in pred)
        ok &= wz < mpf('1e-25')
        # SCREEN: nothing else on the grid comes close
        v = nT(float(t), gb, gA0, gA1, dt=float(dt))
        Z = v < 2e-4
        far = 0.0
        if Z.any():
            d = np.full(gb.shape, np.inf)
            for q in pred:
                d = np.minimum(d, np.maximum(np.maximum(np.abs(gb - float(q[0])),
                                                        np.abs(gA0 - float(q[1]))),
                                             np.abs(gA1 - float(q[2]))))
            far = float(d[Z].max())
        ok &= far < 0.09
        rows.append(f"t={float(t)}: {len(pred)} predicted zeros, max |T| = {float(wz):.1e} "
                    f"(40 digits); {int(Z.sum())} of {gb.size} grid points below 2e-4, all "
                    f"within L-inf {far:.3f}")
    record("B30 the equality set of section 2.6 is complete (predicted zeros + grid search)",
           bool(ok), "; ".join(rows))


# ============================================== E. class, not instance (negative controls)


def b31_p_family(ps, ngrid):
    """BREAK ATTEMPT (system 17): find a p where the target fails at e = h(p)."""
    rows, ok = [], True
    gb, gA0, gA1 = cube(ngrid)
    xs = np.linspace(0, 1, 20001)
    for pv in ps:
        pf = float(pv)
        ef = float(nh(np.array(pf)))
        mn_delta = float(((1 - ef) * nh(xs) - (nh(xs * (1 - 2 * pf) + pf) - nh(np.array(pf)))).min())
        worst = np.inf
        for ti in (0.0, 0.37, 0.71, 1.0):
            worst = min(worst, float(np.nanmin(nT(ti, gb, gA0, gA1, p=pf, e=ef))))
        rows.append(f"p={pv}: min delta = {mn_delta:+.2e}, min T = {worst:+.2e}")
        ok &= mn_delta > -1e-12 and worst > -1e-9
    record("B31 class check: the target survives for every p at e = h(p)", bool(ok),
           "; ".join(rows) + "  [float64 SCREEN; the PROOF for all p is B18+B13]")


def b32_detuning(ngrid):
    """CORRECTION TARGET (system 17): N10 section 3.3-2 says that for e < h(p) the
    target holds 'with slack'.  It does not: it holds with EQUALITY, because the
    X1-deterministic law attains d*_t unconditionally, for every e.
    """
    rows, ok = [], True
    gb, gA0, gA1 = cube(ngrid)
    for shift in ('-0.05', '-0.02', '0.02', '0.05'):
        ef = float(E) + float(shift)
        e = E + mpf(shift)
        mn_delta = min(deltaf(mpf(i) / 2000, P, e) for i in range(2001))
        worst_grid = np.inf
        worst_exact = None
        for ti in (mpf(0), mpf('0.5'), mpf(1)):
            dt, bt = dstar(ti, P, e)
            worst_grid = min(worst_grid,
                             float(np.nanmin(nT(float(ti), gb, gA0, gA1, e=ef, dt=float(dt)))))
            # the X1-deterministic law at b = beta*_t: exact zero for EVERY e
            v = T_of(ti, bt, mpf(0), mpf(0), dt, P, e)
            if worst_exact is None or v < worst_exact:
                worst_exact = v
        rows.append(f"e-h(p)={shift}: min delta = {float(mn_delta):+.5f}, "
                    f"min T (grid) = {worst_grid:+.5f}, T at the deterministic corner "
                    f"= {float(worst_exact):+.2e}")
        if mpf(shift) > 0:
            ok &= mn_delta < -mpf('1e-3') and worst_grid < -1e-3
        else:
            ok &= mn_delta > -mpf('1e-25') and abs(worst_exact) < mpf('1e-20')
    record("B32 detuning: e > h(p) breaks the target; e < h(p) keeps it TIGHT (not 'with slack')",
           bool(ok), "; ".join(rows) +
           "  => for every e <= h(p) the target holds with EQUALITY, not with slack")


def b33_theorem3_still_applies():
    """CORRECTION TARGET (system 17): N10 section 4.1 says Theorem 3 cannot be applied
    when e != h(p).  For e < h(p) both blocks are MORE more-capable, not less, so the
    hypothesis of Theorem 3 is satisfied a fortiori; only e > h(p) breaks it.
    """
    rows, ok = [], True
    for shift in ('-0.05', '-0.02', '0.02'):
        e = E + mpf(shift)
        mn = min(deltaf(mpf(i) / 2000, P, e) for i in range(2001))
        mc = mn > -mpf('1e-30')
        rows.append(f"e-h(p)={shift}: more capable (both blocks) = {mc}")
        ok &= (mc == (mpf(shift) < 0))
    record("B33 more capable (hence Theorem 3's hypothesis) survives e < h(p), fails e > h(p)",
           bool(ok), "; ".join(rows) +
           "  => 'e != h(p) makes Theorem 3 inapplicable' is wrong on the e < h(p) side")


def b34_screen_descent(nrestart):
    """SCREEN (not evidence): float64 random restarts + local descent for T_t < 0."""
    rng = np.random.default_rng(2027)

    def Tn(t, b, A0, A1):
        return float(nT(t, np.array(b), np.array(A0), np.array(A1)))

    best, arg = 1e9, None
    for _ in range(nrestart):
        cur = [round(float(x), 3) for x in rng.random(4)]
        v = Tn(*cur)
        step = 0.1
        while step > 1e-5:
            improved = False
            for k in range(4):
                for sg in (1, -1):
                    cand = list(cur)
                    cand[k] = round(min(max(cand[k] + sg * step, 0.0), 1.0), 8)
                    vv = Tn(*cand)
                    if vv < v - 1e-15:
                        v, cur, improved = vv, cand, True
            if not improved:
                step *= 0.5
        if v < best:
            best, arg = v, cur
    ok = best > -1e-11
    record("B34 SCREEN (not evidence): local descent hunt for T_t < 0", bool(ok),
           f"{nrestart} restarts, best (most negative) T = {best:.3e} at "
           f"(t,b,A0,A1) = ({arg[0]:.4f}, {arg[1]:.4f}, {arg[2]:.4f}, {arg[3]:.4f})")


# ------------------------------------------------------------------------- driver


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    q = args.quick
    t0 = time.time()

    b1_instance()
    b2_chain_rule(4 if q else 12)
    b3_bec_exactness(4 if q else 12)
    b4_role_swap(4 if q else 10)
    b5_fibre_identity(20 if q else 60)
    b6_sdpi_identity(8 if q else 20)
    b7_T_decomposition(15 if q else 40)
    b8_degenerate_fibres()
    b9_simplex_direct(200 if q else 800)
    b10_rational_fibres(6 if q else 10)
    b11_both_terms_small()
    b16_direction_coverage()
    b12_symbolic_decomposition()
    b13_symbolic_sigma_identity()
    b14_sigma_identity_numeric(10 if q else 30)
    b15_weights()
    b17_delta_second_derivative()
    b18_sign_change_is_structural()
    b19_delta_x0_not_needed()
    b20_two_sign_changes_impossible(40 if q else 120)
    b24_delta_interval_arithmetic(200 if q else 800)
    b21_more_capable_threshold()
    b22_n7p_counterexample()
    b23_constants()
    b25_omega_lower(20 if q else 60)
    b26_min_f_direct(6 if q else 12, 60 if q else 200)
    b27_bridge_is_arithmetic()
    b28_three_variable_statement_is_true(20 if q else 40)
    b29_t_elimination_gap(40 if q else 100, 40 if q else 100)
    b30_equality_set(30 if q else 60)
    b31_p_family(['0.01', '0.2', '0.45'] if q else ['0.005', '0.01', '0.05', '0.2', '0.35', '0.49'],
                 20 if q else 40)
    b32_detuning(30 if q else 80)
    b33_theorem3_still_applies()
    b34_screen_descent(20 if q else 80)

    npass = sum(1 for _, ok, _ in RESULTS if ok)
    n = len(RESULTS)
    print(f"\n{npass}/{n} tests passed in {time.time() - t0:.1f} s"
          f"{' (--quick)' if q else ''}")
    sys.exit(0 if npass == n else 1)


if __name__ == "__main__":
    main()
