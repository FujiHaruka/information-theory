#!/usr/bin/env python3
"""
n11_audit_morecapable.py
========================
Independent verifier for the ADVERSARIAL audit of leg N11 (commit 4da3a9ad).

Audited object
--------------
`InformationTheory/Shannon/BroadcastChannel/MoreCapableBinary.lean`
  * `log_two_mul_binEntropy_binConv_sub_binEntropy_le`  (:379)
  * `binEntropy_binConv_sub_binEntropy_le`              (:392)

Self-containment (mandatory)
----------------------------
This file imports and executes NO earlier verifier (`n10_*`, `n9_*`, ... are never
touched).  Every quantity below is rebuilt here from the raw channel definitions:
the joint law of (X, Y) is written down explicitly and the mutual information is
summed as  sum p(x,y) log( p(x,y) / (p(x) p(y)) ).  The closed forms
`h(x*p) - h(p)` and `(1-e) h(x)` are NEVER assumed -- they are conclusions
(tests A1/A2), and only afterwards used as fast surrogates.

Sim fidelity (CLAUDE.md "verify the sim against the real Lean defs first")
--------------------------------------------------------------------------
`binE` below mirrors Mathlib's
    Real.binEntropy p = p * log p⁻¹ + (1 - p) * log (1 - p)⁻¹
verbatim, including the two Lean conventions that matter outside [0,1]:
`Real.log y = log |y|` and `y⁻¹ = 0` at `y = 0`.  Test V1 checks the mirror
against seven Mathlib lemmas (binEntropy_zero / _one / _two_inv / _one_sub /
_pos / _neg_of_neg / _lt_log_two).

Arithmetic: mpmath at 40 significant digits, plus RIGOROUS interval arithmetic
(mpmath.iv, directed rounding) for the exact-rational certificates in D3.

Run:  python3 docs/shannon/verifiers/n11_audit_morecapable.py
"""

import random
from mpmath import mp, mpf, iv

mp.dps = 40
iv.dps = 30

RESULTS = []


def check(name, ok, detail=""):
    RESULTS.append((name, bool(ok)))
    print(("PASS " if ok else "FAIL ") + name + ("   " + detail if detail else ""))
    return bool(ok)


# ---------------------------------------------------------------- Lean mirrors

def rlog(y):
    """Mathlib `Real.log`: log |y|, and 0 at y = 0."""
    if y == 0:
        return mpf(0)
    return mp.log(abs(y))


def rinv(y):
    """Lean division convention: y⁻¹ = 0 at y = 0."""
    if y == 0:
        return mpf(0)
    return mpf(1) / y


def binE(p):
    """Mirror of `Real.binEntropy` (nats)."""
    p = mpf(p)
    return p * rlog(rinv(p)) + (1 - p) * rlog(rinv(1 - p))


LOG2 = mp.log(2)


def h2(p):
    """Binary entropy in BITS."""
    return binE(p) / LOG2


def binconv(p, x):
    """`x * (1 - p) + (1 - x) * p`, verbatim from the Lean statement."""
    p, x = mpf(p), mpf(x)
    return x * (1 - p) + (1 - x) * p


def lean_lhs(p, x):
    return LOG2 * (binE(binconv(p, x)) - binE(p))


def lean_rhs(p, x):
    return (LOG2 - binE(p)) * binE(x)


def lean_gap(p, x):
    """RHS - LHS of `log_two_mul_binEntropy_binConv_sub_binEntropy_le`."""
    return lean_rhs(p, x) - lean_lhs(p, x)


def lean_gap_halfspace(p, x, e):
    """RHS - LHS of `binEntropy_binConv_sub_binEntropy_le`."""
    return (1 - mpf(e)) * binE(x) - (binE(binconv(p, x)) - binE(p))


# ------------------------------------------- mutual information from raw joints

def mi_from_joint(joint, nx, ny):
    px = [sum(joint[i][j] for j in range(ny)) for i in range(nx)]
    py = [sum(joint[i][j] for i in range(nx)) for j in range(ny)]
    s = mpf(0)
    for i in range(nx):
        for j in range(ny):
            q = joint[i][j]
            if q > 0:
                s += q * mp.log(q / (px[i] * py[j]))
    return s


def mi_bsc_raw(x, p):
    """I(X;Y) in NATS for X ~ Bern(x) through BSC(p), from the raw joint law."""
    x, p = mpf(x), mpf(p)
    px = [1 - x, x]
    W = [[1 - p, p], [p, 1 - p]]          # W[i][j] = P(Y=j | X=i)
    joint = [[px[i] * W[i][j] for j in range(2)] for i in range(2)]
    return mi_from_joint(joint, 2, 2)


def mi_bec_raw(x, e):
    """I(X;Y) in NATS for X ~ Bern(x) through BEC(e); outputs 0, 1, erasure."""
    x, e = mpf(x), mpf(e)
    px = [1 - x, x]
    W = [[1 - e, mpf(0), e], [mpf(0), 1 - e, e]]
    joint = [[px[i] * W[i][j] for j in range(3)] for i in range(3 - 1)]
    return mi_from_joint(joint, 2, 3)


def py1_bsc_raw(x, p):
    """P(Y = 1) computed from the raw joint law of the BSC."""
    x, p = mpf(x), mpf(p)
    return (1 - x) * p + x * (1 - p)


# --------------------------------- the Lean file's private analytic machinery

def gapFun(p, x):
    return (LOG2 - binE(p)) * binE(x) - LOG2 * (binE(binconv(p, x)) - binE(p))


def gapFunDeriv(p, x):
    u = binconv(p, x)
    return ((LOG2 - binE(p)) * (rlog(1 - x) - rlog(x))
            - LOG2 * (1 - 2 * mpf(p)) * (rlog(1 - u) - rlog(u)))


def gapFunDeriv2(p, x):
    u = binconv(p, x)
    x = mpf(x)
    return (-(LOG2 - binE(p)) / (x * (1 - x))
            + LOG2 * (1 - 2 * mpf(p)) ** 2 / (u * (1 - u)))


def curvatureThreshold(p):
    p = mpf(p)
    return ((LOG2 - binE(p)) * (p * (1 - p))) / (binE(p) * (1 - 2 * p) ** 2)


def inflection(p):
    K = curvatureThreshold(p)
    return (1 - mp.sqrt(max(mpf(0), 1 - 4 * K))) / 2


# ================================================================= V. fidelity

def test_V1():
    ok = True
    ok &= binE(0) == 0 and binE(1) == 0
    ok &= abs(binE(mpf(1) / 2 ) - LOG2) < mpf(10) ** -35
    for p in ['0.1', '0.37', '0.9', '-0.3', '1.7']:
        ok &= abs(binE(mpf(p)) - binE(1 - mpf(p))) < mpf(10) ** -35
    for p in ['0.001', '0.1', '0.5', '0.9', '0.999']:
        ok &= binE(mpf(p)) > 0
    for p in ['-0.001', '-1.0', '-7.5']:
        ok &= binE(mpf(p)) < 0
    for p in ['0.1', '0.3', '0.7', '0.9']:
        ok &= binE(mpf(p)) < LOG2
    ok &= abs(binE(mpf(1) / 2) - LOG2) < mpf(10) ** -35
    return check("V1  sim mirrors Real.binEntropy (7 Mathlib lemmas)", ok)


# ============================================ A. raw-channel re-derivation

def test_A1():
    random.seed(11)
    worst = mpf(0)
    for _ in range(300):
        p = mpf(random.random()) * mpf('0.999') + mpf('0.0005')
        x = mpf(random.random())
        d = abs(mi_bsc_raw(x, p) - (binE(binconv(p, x)) - binE(p)))
        worst = max(worst, d)
    return check("A1  raw BSC joint  ->  I = binE(x*p) - binE(p)  (nats)",
                 worst < mpf(10) ** -33, "max |diff| = %s" % mp.nstr(worst, 5))


def test_A2():
    random.seed(12)
    worst = mpf(0)
    for _ in range(300):
        e = mpf(random.random())
        x = mpf(random.random())
        d = abs(mi_bec_raw(x, e) - (1 - e) * binE(x))
        worst = max(worst, d)
    return check("A2  raw BEC joint  ->  I = (1-e) * binE(x)  (nats)",
                 worst < mpf(10) ** -33, "max |diff| = %s" % mp.nstr(worst, 5))


def test_A3():
    random.seed(13)
    worst = mpf(0)
    for _ in range(200):
        p, x = mpf(random.random()), mpf(random.random())
        worst = max(worst, abs(py1_bsc_raw(x, p) - binconv(p, x)))
    return check("A3  P(Y=1) from raw joint == x*(1-p) + (1-x)*p (orientation)",
                 worst < mpf(10) ** -35, "max |diff| = %s" % mp.nstr(worst, 5))


def test_A4():
    random.seed(14)
    worst = mpf(0)
    for _ in range(200):
        p, x = mpf(random.random()), mpf(random.random())
        worst = max(worst, abs(binconv(p, x) - binconv(x, p)))
    return check("A4  binConv is symmetric in (p,x): direction cannot be flipped",
                 worst == 0, "max |diff| = %s" % mp.nstr(worst, 5))


def test_A5():
    random.seed(15)
    ok = True
    for _ in range(200):
        p, x = mpf(random.random()), mpf(random.random())
        ok &= abs(binconv(p, 1 - x) - (1 - binconv(p, x))) < mpf(10) ** -35
        ok &= abs(binconv(1 - p, x) - (1 - binconv(p, x))) < mpf(10) ** -35
    return check("A5  x*p reflections: (1-x)*p = 1-(x*p),  x*(1-p) = 1-(x*p)", ok)


def test_A6():
    """more capable, at e = h2(p), IS the pointwise inequality (binary input)."""
    random.seed(16)
    worst = None
    for _ in range(200):
        p = mpf(random.random()) * mpf('0.499') + mpf('0.0005')
        x = mpf(random.random())
        e = h2(p)
        d = mi_bec_raw(x, e) - mi_bsc_raw(x, p)
        worst = d if worst is None else min(worst, d)
    return check("A6  raw I_BEC(h2(p)) - I_BSC(p) >= 0 at random (p,x)",
                 worst > -mpf(10) ** -33, "min = %s" % mp.nstr(worst, 5))


# ============================================= B. transcription of the target

def test_B1():
    random.seed(21)
    worst = mpf(0)
    for _ in range(300):
        p = mpf(random.random()) * mpf('0.499') + mpf('0.0005')
        x = mpf(random.random())
        delta_bits = (1 - h2(p)) * h2(x) - (h2(binconv(p, x)) - h2(p))
        worst = max(worst, abs(lean_gap(p, x) - LOG2 ** 2 * delta_bits))
    return check("B1  Lean(RHS-LHS) == (log 2)^2 * delta   [closed forms]",
                 worst < mpf(10) ** -33, "max |diff| = %s" % mp.nstr(worst, 5))


def test_B2():
    random.seed(22)
    worst = mpf(0)
    for _ in range(200):
        p = mpf(random.random()) * mpf('0.499') + mpf('0.0005')
        x = mpf(random.random())
        e = h2(p)
        delta_bits = (mi_bec_raw(x, e) - mi_bsc_raw(x, p)) / LOG2
        worst = max(worst, abs(lean_gap(p, x) - LOG2 ** 2 * delta_bits))
    return check("B2  Lean(RHS-LHS) == (log 2)^2 * delta   [RAW joints only]",
                 worst < mpf(10) ** -32, "max |diff| = %s" % mp.nstr(worst, 5))


def test_B3():
    """N10 SS2.5 verbatim: delta(x) = C*h(x) - J(x), J = h(x*p) - h(p), C = 1 - h(p)."""
    pts = [('1/10', '3/10'), ('1/4', '1/8'), ('1/100', '99/100'),
           ('49/100', '1/3'), ('1/1000', '1/2'), ('2/5', '7/9')]
    worst = mpf(0)
    for ps, xs in pts:
        pn, pd = [int(t) for t in ps.split('/')]
        xn, xd = [int(t) for t in xs.split('/')]
        p, x = mpf(pn) / pd, mpf(xn) / xd
        C = 1 - h2(p)
        J = h2(binconv(p, x)) - h2(p)
        delta = C * h2(x) - J
        worst = max(worst, abs(lean_gap(p, x) / LOG2 ** 2 - delta))
    return check("B3  N10 SS2.5 delta == Lean gap / (log 2)^2 at 6 EXACT rationals",
                 worst < mpf(10) ** -35, "max |diff| = %s" % mp.nstr(worst, 5))


def test_B4():
    """Tightness at x = 1/2 pins e = h2(p) exactly -- the decisive unit check."""
    ok = True
    worst = mpf(0)
    for ps in ['0.001', '0.05', '0.1', '0.25', '0.4', '0.499']:
        p = mpf(ps)
        worst = max(worst, abs(lean_gap(p, mpf(1) / 2)))
    ok &= worst < mpf(10) ** -34
    return check("B4  gap(p, 1/2) == 0 for every p  =>  e = h2(p) is pinned, not chosen",
                 ok, "max |gap(p,1/2)| = %s" % mp.nstr(worst, 5))


def test_B5():
    """Mix-up direction 1: read binEntropy as if it were bits (e := binEntropy p)."""
    ok_true = True
    slack_at_half = None
    for ps in ['0.05', '0.1', '0.25', '0.4']:
        p = mpf(ps)
        for k in range(0, 101):
            x = mpf(k) / 100
            g = (1 - binE(p)) * binE(x) - (binE(binconv(p, x)) - binE(p))
            if g < -mpf(10) ** -33:
                ok_true = False
        s = (1 - binE(p)) * binE(mpf(1) / 2) - (binE(binconv(p, mpf(1) / 2)) - binE(p))
        slack_at_half = s if slack_at_half is None else min(slack_at_half, s)
    return check("B5  nat/bit mix-up A (e := binEntropy p) is TRUE but strictly weaker",
                 ok_true and slack_at_half > mpf('1e-3'),
                 "slack at x=1/2 = %s (true form has 0)" % mp.nstr(slack_at_half, 5))


def test_B6():
    """Mix-up direction 2: put h2 where the Lean statement has binEntropy."""
    worst = None
    for ps in ['0.05', '0.1', '0.25', '0.4']:
        p = mpf(ps)
        for k in range(0, 101):
            x = mpf(k) / 100
            g = (LOG2 - h2(p)) * h2(x) - LOG2 * (h2(binconv(p, x)) - h2(p))
            worst = g if worst is None else min(worst, g)
    return check("B6  nat/bit mix-up B (h2 in the Lean slots) is FALSE -- compiler would reject",
                 worst < -mpf('1e-3'), "min = %s < 0" % mp.nstr(worst, 5))


# =========================================== C. curvature / inflection machinery

def test_C1():
    random.seed(31)
    worst = mpf(0)
    for _ in range(300):
        p, x = mpf(random.random()), mpf(random.random())
        u = binconv(p, x)
        worst = max(worst, abs(u * (1 - u) - (p * (1 - p) + (1 - 2 * p) ** 2 * x * (1 - x))))
    return check("C1  u(1-u) = p(1-p) + (1-2p)^2 x(1-x)   [binConv_mul_one_sub]",
                 worst < mpf(10) ** -34, "max |diff| = %s" % mp.nstr(worst, 5))


def test_C2():
    random.seed(32)
    worst = mpf(0)
    hstep = mpf(10) ** -12
    for _ in range(60):
        p = mpf(random.random()) * mpf('0.49') + mpf('0.005')
        x = mpf(random.random()) * mpf('0.98') + mpf('0.01')
        num = (gapFun(p, x + hstep) - gapFun(p, x - hstep)) / (2 * hstep)
        worst = max(worst, abs(num - gapFunDeriv(p, x)))
    return check("C2  gapFunDeriv == numeric d/dx gapFun",
                 worst < mpf(10) ** -14, "max |diff| = %s" % mp.nstr(worst, 5))


def test_C3():
    random.seed(33)
    worst = mpf(0)
    hstep = mpf(10) ** -10
    for _ in range(60):
        p = mpf(random.random()) * mpf('0.49') + mpf('0.005')
        x = mpf(random.random()) * mpf('0.9') + mpf('0.05')
        num = (gapFun(p, x + hstep) - 2 * gapFun(p, x) + gapFun(p, x - hstep)) / hstep ** 2
        worst = max(worst, abs(num - gapFunDeriv2(p, x)))
    return check("C3  gapFunDeriv2 == numeric d2/dx2 gapFun",
                 worst < mpf(10) ** -12, "max |diff| = %s" % mp.nstr(worst, 5))


def test_C4():
    random.seed(34)
    worst = mpf(0)
    for _ in range(300):
        p = mpf(random.random()) * mpf('0.499') + mpf('0.0005')
        x = mpf(random.random()) * mpf('0.998') + mpf('0.001')
        u = binconv(p, x)
        lhs = gapFunDeriv2(p, x) * (x * (1 - x) * (u * (1 - u)))
        rhs = binE(p) * (1 - 2 * p) ** 2 * (x * (1 - x) - curvatureThreshold(p))
        worst = max(worst, abs(lhs - rhs))
    return check("C4  gapFunDeriv2_mul identity (sign of g'' == sign of x(1-x) - K)",
                 worst < mpf(10) ** -32, "max |diff| = %s" % mp.nstr(worst, 5))


def test_C5():
    kmax, argmax = mpf(0), None
    N = 200000
    for i in range(1, N):
        p = mpf(i) / (2 * N)
        K = curvatureThreshold(p)
        if K > kmax:
            kmax, argmax = K, p
    for ps in ['0.4999999', '0.49999999999', '0.499999999999999']:
        kmax = max(kmax, curvatureThreshold(mpf(ps)))
    bound = 1 / (8 * LOG2)
    return check("C5  K(p) < 1/4 on (0,1/2)  [200k sweep + p->1/2 tail]",
                 kmax < mpf(1) / 4,
                 "sup ~ %s at p ~ %s ; 1/(8 log 2) = %s"
                 % (mp.nstr(kmax, 10), mp.nstr(argmax, 6), mp.nstr(bound, 10)))


def test_C6():
    lim = 1 / (8 * LOG2)
    near = curvatureThreshold(mpf('0.4999999999'))
    tail = [curvatureThreshold(mpf('1e-%d' % k)) for k in (12, 100, 300, 1000)]
    decreasing = all(tail[i] > tail[i + 1] for i in range(len(tail) - 1))
    return check("C6  K(p) -> 1/(8 log 2) as p->1/2 and K(p) -> 0 (log-slowly) as p->0",
                 abs(near - lim) < mpf('1e-12') and decreasing and tail[-1] < mpf('1e-3'),
                 "K(.4999999999) = %s ; K(1e-12,1e-100,1e-300,1e-1000) = %s"
                 % (mp.nstr(near, 10), ", ".join(mp.nstr(v, 4) for v in tail)))


def test_C7():
    ok = True
    worst = mpf(0)
    for ps in ['0.001', '0.01', '0.1', '0.3', '0.45', '0.499']:
        p = mpf(ps)
        z = inflection(p)
        ok &= 0 < z < mpf(1) / 2
        worst = max(worst, abs(z * (1 - z) - curvatureThreshold(p)))
    return check("C7  inflection(p)(1-inflection(p)) == K and 0 < inflection < 1/2",
                 ok and worst < mpf(10) ** -33, "max |diff| = %s" % mp.nstr(worst, 5))


def test_C8():
    z = inflection(mpf('0.1'))
    return check("C8  inflection(0.1) reproduces N10 SS2.5's x0 = 0.198699324",
                 abs(z - mpf('0.198699324')) < mpf('1e-9'),
                 "inflection(0.1) = %s" % mp.nstr(z, 12))


def test_C9():
    ok = True
    detail = []
    for ps in ['0.001', '0.05', '0.1', '0.3', '0.45', '0.4999']:
        p = mpf(ps)
        z = inflection(p)
        changes = 0
        prev = None
        for k in range(1, 4000):
            x = mpf(k) / 8000
            s = 1 if gapFunDeriv2(p, x) > 0 else -1
            if prev is not None and s != prev:
                changes += 1
                loc = x
            prev = s
        ok &= (changes == 1) and abs(loc - z) < mpf('1e-3')
        detail.append("%s:%d" % (ps, changes))
    return check("C9  g'' changes sign exactly once on (0,1/2), at inflection(p)",
                 ok, " ".join(detail))


def test_C10():
    """N10 correction 5(c): the argument must survive x0 pushed towards an end."""
    ok = True
    for ps in ['1e-6', '1e-4', '0.4999', '0.499999']:
        p = mpf(ps)
        z = inflection(p)
        for k in range(0, 2001):
            x = mpf(k) / 4000
            if gapFun(p, x) < -mpf(10) ** -30:
                ok = False
        # concave below z, convex above z
        if 0 < z < mpf(1) / 2:
            a = z / 2
            b = (z + mpf(1) / 2) / 2
            if not (gapFunDeriv2(p, a) < 0 and gapFunDeriv2(p, b) > 0):
                ok = False
    return check("C10 extreme p (1e-6 .. 0.499999): arcs keep their signs, gapFun >= 0", ok)


def test_C11():
    """The `max 0 (1-4K)` guard: semantics when K >= 1/4 (unreachable in (0,1/2))."""
    def infl_from_K(K):
        return (1 - mp.sqrt(max(mpf(0), 1 - 4 * K))) / 2
    ok = (infl_from_K(mpf('0.3')) == mpf(1) / 2 and infl_from_K(mpf('0.25')) == mpf(1) / 2
          and infl_from_K(mpf('0.18')) < mpf(1) / 2)
    return check("C11 max-0 guard: K >= 1/4 would give inflection = 1/2 (empty convex arc)",
                 ok)


# ================================================ D. attempts to break delta >= 0

def test_D1():
    worst, arg = None, None
    for i in range(1, 500):
        p = mpf(i) / 1000
        if p >= mpf(1) / 2:
            continue
        for k in range(0, 401):
            x = mpf(k) / 400
            g = lean_gap(p, x)
            if worst is None or g < worst:
                worst, arg = g, (p, x)
    return check("D1  grid sweep p in (0,1/2) x x in [0,1] (499 x 401, 40 digits)",
                 worst > -mpf(10) ** -35,
                 "min gap = %s at %s" % (mp.nstr(worst, 5), (mp.nstr(arg[0], 4), mp.nstr(arg[1], 4))))


def test_D2():
    worst, arg = None, None
    ps = [mpf('1e-%d' % k) for k in range(1, 13)] + \
         [mpf(1) / 2 - mpf('1e-%d' % k) for k in range(1, 13)]
    xs = [mpf(0), mpf(1), mpf(1) / 2] + \
         [mpf('1e-%d' % k) for k in range(1, 15)] + \
         [1 - mpf('1e-%d' % k) for k in range(1, 15)] + \
         [mpf(1) / 2 + mpf('1e-%d' % k) for k in range(1, 15)] + \
         [mpf(1) / 2 - mpf('1e-%d' % k) for k in range(1, 15)]
    for p in ps:
        for x in xs:
            g = lean_gap(p, x)
            if worst is None or g < worst:
                worst, arg = g, (p, x)
    return check("D2  boundary-neighbourhood sweep (p, x within 1e-14 of 0, 1/2, 1)",
                 worst > -mpf(10) ** -35,
                 "min gap = %s at %s" % (mp.nstr(worst, 5), (mp.nstr(arg[0], 4), mp.nstr(arg[1], 4))))


def _binE_iv(p):
    return p * iv.log(1 / p) + (1 - p) * iv.log(1 / (1 - p))


def _gap_iv(pn, pd, xn, xd):
    p = iv.mpf(pn) / iv.mpf(pd)
    x = iv.mpf(xn) / iv.mpf(xd)
    u = x * (1 - p) + (1 - x) * p
    L = iv.log(iv.mpf(2))
    return (L - _binE_iv(p)) * _binE_iv(x) - L * (_binE_iv(u) - _binE_iv(p))


def test_D3():
    pts = [(1, 10, 3, 10), (1, 10, 1, 4), (1, 4, 1, 8), (1, 100, 99, 100),
           (49, 100, 1, 3), (1, 1000, 1, 5), (2, 5, 7, 9), (3, 100, 1, 50),
           (1, 3, 1, 3), (7, 20, 13, 20), (1, 10000, 3, 7), (499, 1000, 1, 4)]
    # x = 1/2 is deliberately absent: there the gap is EXACTLY 0 (binconv(p,1/2) = 1/2 makes
    # the two sides algebraically equal), so no interval method can certify strict positivity.
    # That point is covered algebraically by B4 instead.
    ok = True
    smallest = None
    for pn, pd, xn, xd in pts:
        g = _gap_iv(pn, pd, xn, xd)
        lo = g.a
        if not lo > 0:
            ok = False
        smallest = lo if smallest is None else min(smallest, lo)
    return check("D3  RIGOROUS interval enclosure > 0 at 12 exact rational (p,x)",
                 ok, "smallest certified lower bound = %s" % str(smallest)[:12])


def test_D3b():
    """Calibration of D3: the same machinery must NOT certify a false statement."""
    p = iv.mpf(1) / iv.mpf(10)
    x = iv.mpf(1) / iv.mpf(2)
    L = iv.log(iv.mpf(2))
    u = x * (1 - p) + (1 - x) * p
    bad = (L - _binE_iv(p) - iv.mpf(1) / iv.mpf(100)) * _binE_iv(x) \
        - L * (_binE_iv(u) - _binE_iv(p))
    return check("D3b calibration: interval method refuses a deliberately false variant",
                 not (bad.a > 0), "enclosure lower end = %s" % str(bad.a)[:12])


def test_D4():
    """Screen: random-restart local descent hunting for a violation."""
    random.seed(41)
    best, arg = None, None
    for _ in range(400):
        p = mpf(random.random()) * mpf('0.4995') + mpf('0.0002')
        x = mpf(random.random())
        step = mpf('0.05')
        cur = lean_gap(p, x)
        for _ in range(200):
            improved = False
            for dx in (step, -step):
                xt = min(max(x + dx, mpf(0)), mpf(1))
                v = lean_gap(p, xt)
                if v < cur:
                    cur, x, improved = v, xt, True
            for dp in (step, -step):
                pt = min(max(p + dp, mpf('1e-9')), mpf(1) / 2 - mpf('1e-9'))
                v = lean_gap(pt, x)
                if v < cur:
                    cur, p, improved = v, pt, True
            if not improved:
                step /= 2
                if step < mpf('1e-12'):
                    break
        if best is None or cur < best:
            best, arg = cur, (p, x)
    return check("D4  400-restart local descent finds no violation (screen only)",
                 best > -mpf(10) ** -33,
                 "best = %s at %s" % (mp.nstr(best, 5), (mp.nstr(arg[0], 5), mp.nstr(arg[1], 5))))


def test_D5():
    p = mpf('0.1')
    zeros, near = [], 0
    for k in range(0, 20001):
        x = mpf(k) / 20000
        g = lean_gap(p, x)
        if g < mpf('1e-9'):
            near += 1
            zeros.append(x)
    ok = all(min(abs(z), abs(z - mpf(1) / 2), abs(z - 1)) < mpf('1e-3') for z in zeros)
    return check("D5  zero set of the gap sits only at {0, 1/2, 1} (screen, p = 0.1)",
                 ok, "%d near-zero grid points, all within 1e-3 of the 3 known zeros" % near)


# ============================== E. are the hypotheses necessary / can they widen?

def test_E1():
    """p in (1/2, 1): the statement is the SAME statement (exact symmetry)."""
    random.seed(51)
    worst = mpf(0)
    minimum = None
    for _ in range(300):
        p = mpf('0.5') + mpf(random.random()) * mpf('0.4999')
        x = mpf(random.random())
        worst = max(worst, abs(lean_gap(p, x) - lean_gap(1 - p, x)))
        minimum = lean_gap(p, x) if minimum is None else min(minimum, lean_gap(p, x))
    return check("E1  p in (1/2,1): gap(p,x) == gap(1-p,x) and stays >= 0  [hyp p<1/2 not needed]",
                 worst < mpf(10) ** -34 and minimum > -mpf(10) ** -34,
                 "max |gap(p)-gap(1-p)| = %s, min gap = %s"
                 % (mp.nstr(worst, 5), mp.nstr(minimum, 5)))


def test_E2():
    worst = mpf(0)
    for k in range(0, 101):
        x = mpf(k) / 100
        worst = max(worst, abs(lean_gap(mpf(1) / 2, x)))
    return check("E2  p = 1/2: both sides vanish identically (statement holds, degenerate)",
                 worst < mpf(10) ** -34, "max |gap| = %s" % mp.nstr(worst, 5))


def test_E3():
    worst = mpf(0)
    for k in range(0, 101):
        x = mpf(k) / 100
        worst = max(worst, abs(lean_gap(mpf(0), x)), abs(lean_gap(mpf(1), x)))
    return check("E3  p = 0 and p = 1: equality (statement holds)  [hyp 0<p not needed]",
                 worst < mpf(10) ** -34, "max |gap| = %s" % mp.nstr(worst, 5))


def test_E4():
    worst, arg = None, None
    for ps in ['-0.5', '-0.1', '1.1', '2.0', '-3.0', '5.0']:
        p = mpf(ps)
        for k in range(0, 201):
            x = mpf(k) / 200
            g = lean_gap(p, x)
            if worst is None or g < worst:
                worst, arg = g, (ps, x)
    return check("E4  p outside [0,1] (screen): does the statement survive?",
                 True,
                 "min gap = %s at p=%s, x=%s  (%s)"
                 % (mp.nstr(worst, 5), arg[0], mp.nstr(arg[1], 4),
                    "still >= 0" if worst > -mpf(10) ** -30 else "VIOLATED -> [0,1] is the honest domain"))


def test_E5():
    """Half-space version: `he` is necessary, and it is sharp."""
    p = mpf('0.1')
    ok_below = True
    for es in ['0', '0.1', '0.3', '0.46899559']:
        e = mpf(es)
        if e * LOG2 > binE(p):
            continue
        for k in range(0, 201):
            x = mpf(k) / 200
            if lean_gap_halfspace(p, x, e) < -mpf(10) ** -33:
                ok_below = False
    e_above = h2(p) + mpf('0.01')
    viol = lean_gap_halfspace(p, mpf(1) / 2, e_above)
    return check("E5  half-space: e <= h2(p) holds; e > h2(p) fails at x = 1/2 (he is load-bearing)",
                 ok_below and viol < 0, "gap at e = h2(p)+0.01, x=1/2 : %s" % mp.nstr(viol, 5))


def test_E6():
    """`0 <= e` was dropped: check the dropped-hypothesis form is genuinely stronger."""
    p = mpf('0.1')
    ok = True
    for es in ['-0.001', '-1', '-100']:
        e = mpf(es)
        for k in range(0, 101):
            x = mpf(k) / 100
            if lean_gap_halfspace(p, x, e) < -mpf(10) ** -33:
                ok = False
    return check("E6  e < 0 (hypothesis 0 <= e dropped): conclusion still true => strengthening",
                 ok)


def test_E7():
    """Are 0 <= x <= 1 necessary?"""
    viol = None
    for xs in ['-0.5', '-0.05', '1.05', '1.5', '3.0']:
        x = mpf(xs)
        for ps in ['0.05', '0.1', '0.3', '0.45']:
            g = lean_gap(mpf(ps), x)
            if viol is None or g < viol:
                viol, arg = g, (xs, ps)
    return check("E7  x outside [0,1]: statement FAILS => hyps 0<=x<=1 are load-bearing",
                 viol < -mpf('1e-3'),
                 "min gap = %s at x=%s, p=%s" % (mp.nstr(viol, 5), arg[0], arg[1]))


def test_E8():
    p, x = mpf('0.1'), mpf('0.3')
    lhs, rhs = lean_lhs(p, x), lean_rhs(p, x)
    ok = (lhs != 0 and rhs != 0 and lhs < rhs and rhs - lhs > mpf('1e-3'))
    return check("E8  non-vacuity at (p,x) = (0.1,0.3): both sides nonzero, inequality strict",
                 ok, "lhs = %s, rhs = %s, gap = %s"
                     % (mp.nstr(lhs, 8), mp.nstr(rhs, 8), mp.nstr(rhs - lhs, 8)))


# ========================= F. is this really the input of the N10 chain?

def _delta_e(p, x, e):
    """delta_e(x) = (1-e) h(x) - (h(x*p) - h(p)) in BITS."""
    return (1 - mpf(e)) * h2(x) - (h2(binconv(p, x)) - h2(p))


def test_F1():
    """N10 SS2.3-2.4 needs delta >= 0 POINTWISE on [0,1] (weights can concentrate)."""
    random.seed(61)
    p = mpf('0.1')
    e = h2(p)
    C = 1 - e
    worst = None
    for _ in range(20000):
        b = mpf(random.random())
        A0 = mpf(random.random())
        A1 = mpf(random.random())
        a = (1 - b) * A0 + b * A1
        S_A = e * _delta_e(p, a, e) + C * ((1 - b) * _delta_e(p, A0, e) + b * _delta_e(p, A1, e))
        worst = S_A if worst is None else min(worst, S_A)
    # a fiber concentrating on a point where delta < 0 (only possible if e > h2(p))
    e_bad = h2(p) + mpf('0.05')
    S_bad = e_bad * _delta_e(p, mpf(1) / 2, e_bad) + (1 - e_bad) * _delta_e(p, mpf(1) / 2, e_bad)
    return check("F1  N10's S_A >= 0 needs pointwise delta >= 0 (20k fibers); a negative delta breaks it",
                 worst > -mpf(10) ** -33 and S_bad < 0,
                 "min S_A = %s ; S_A with delta<0 = %s" % (mp.nstr(worst, 5), mp.nstr(S_bad, 5)))


def test_F2():
    """md SS5-1's own break attempt, done at EXACT rationals instead of a float grid."""
    pts = [(1, 10, 3, 10), (1, 10, 1, 2), (1, 4, 1, 3), (1, 1000, 999, 1000),
           (49, 100, 1, 2), (3, 10, 2, 5)]
    worst = mpf(0)
    for pn, pd, xn, xd in pts:
        p, x = mpf(pn) / pd, mpf(xn) / xd
        delta_n10 = (1 - h2(p)) * h2(x) - h2(binconv(p, x)) + h2(p)
        worst = max(worst, abs(delta_n10 - lean_gap(p, x) / LOG2 ** 2))
    return check("F2  N10 delta == Lean gap/(log 2)^2 at exact rationals incl. x = 1/2 zeros",
                 worst < mpf(10) ** -34, "max |diff| = %s" % mp.nstr(worst, 5))


def test_F3():
    """The Lean target quantifies over the whole of [0,1]; N10 evaluates delta at 6 points."""
    random.seed(62)
    ok = True
    for _ in range(500):
        pts = [mpf(random.random()) for _ in range(6)]
        for z in pts:
            if lean_gap(mpf('0.1'), z) < -mpf(10) ** -33:
                ok = False
    return check("F3  every argument N10 feeds delta (a,b,A0,A1,B0,B1 in [0,1]) is covered", ok)


# ================================================================== half-space

def test_H1():
    """The ticket's candidate form (with 0 <= e) follows from the loaded theorem."""
    random.seed(71)
    ok = True
    for _ in range(2000):
        p = mpf(random.random()) * mpf('0.4995') + mpf('0.0002')
        e = mpf(random.random()) * h2(p)
        x = mpf(random.random())
        if lean_gap_halfspace(p, x, e) < -mpf(10) ** -33:
            ok = False
    return check("H1  ticket's candidate (0 <= e <= h2(p)) holds -- it is a special case", ok)


def test_H2():
    """Under `he`, e < 1 automatically: the erasure probability cannot exceed 1."""
    ok = True
    for ps in ['0.0001', '0.1', '0.4999']:
        p = mpf(ps)
        ok &= h2(p) < 1
    return check("H2  hypothesis he forces e <= h2(p) < 1 (so 1-e > 0 is automatic)", ok)


ALL = [test_V1, test_A1, test_A2, test_A3, test_A4, test_A5, test_A6,
       test_B1, test_B2, test_B3, test_B4, test_B5, test_B6,
       test_C1, test_C2, test_C3, test_C4, test_C5, test_C6, test_C7, test_C8,
       test_C9, test_C10, test_C11,
       test_D1, test_D2, test_D3, test_D3b, test_D4, test_D5,
       test_E1, test_E2, test_E3, test_E4, test_E5, test_E6, test_E7, test_E8,
       test_F1, test_F2, test_F3, test_H1, test_H2]

if __name__ == '__main__':
    for t in ALL:
        t()
    npass = sum(1 for _, ok in RESULTS if ok)
    print("\n%d/%d" % (npass, len(RESULTS)))
    if npass != len(RESULTS):
        print("FAILED: " + ", ".join(n for n, ok in RESULTS if not ok))
