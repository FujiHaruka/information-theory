#!/usr/bin/env python3
"""Leg N16 -- gate on "is UV = C on the current [probc] reversely more-capable
instance?".

The verdict is carried by (i) exact-rational box algebra (``fractions.Fraction``;
groups I and B), (ii) per-point algebraic identities whose residual is pure
float64 rounding (group D), and (iii) one imported machine fact that is *not*
re-derived here: ``Omega(t) = dstar_t`` (bc-facts.md ``## N10 (T3c)`` N10-a /
N10-e).  Group R holds the controls and the two explicitly-labelled screens; a
screen that finds nothing is evidence of nothing (parent plan section 4.5).

Instance ([probc] Lemma 8, probc.txt:900-903):
  block a:  X1 -> Y1 = BEC(e),   X1 -> Z1 = BSC(p)
  block b:  X2 -> Y2 = BSC(p),   X2 -> Z2 = BEC(e)
with p = 0.1, e = H(0.1).  X = (X1,X2), Y = (Y1,Y2), Z = (Z1,Z2).

Primary sources (retrieval = docs/shannon/lit-fetch.sh; line numbers are for the
`pdftotext -layout` output).  Set LIT=<dir> to re-check the quotations.

  probc   = Geng-Gohari-Nair-Yu, product broadcast channels (proBC.pdf)
  auxrec  = Gohari-Nair, the auxiliary receiver approach (Auxiliary-Receiver.pdf)
  glnsum  = Gohari-Liu-Nair, sum-broadcast channels (arXiv:2606.12839)
  sumofbc = Gohari-Liu-Nair, sum of broadcast channels (sumofBC.pdf)

Run:  python3 docs/shannon/verifiers/n16_uv_gate_probc.py
Exit code 0 iff every test passes.
"""
import itertools
import math
import os
import random
import sys
import unicodedata
from fractions import Fraction

import numpy as np

RESULTS = []


def check(name, ok, detail=""):
    RESULTS.append((name, bool(ok), detail))
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    return bool(ok)


# ---------------------------------------------------------------------------
# group V -- verbatim re-check of every quotation this leg relies on
# ---------------------------------------------------------------------------

QUOTES = [
    ("auxrec", 1005, "R0 ≤ min(I(W ; Y ), I(W ; Z)),"),
    ("auxrec", 1011, "R0 + R1 ≤ min(I(W ; Y ), I(W ; Z)) + I(U ; Y |W ),"),
    ("auxrec", 1012, "R0 + R2 ≤ min(I(W ; Y ), I(W ; Z)) + I(V ; Z|W ),"),
    ("auxrec", 1013, "R0 + R1 + R2 ≤ min(I(W ; Y ), I(W ; Z)) + min(I(U ; Y |W ) + I(X; Z|U, W ), "
                     "I(V ; Z|W ) + I(X; Y |V, W )),"),
    ("auxrec", 1014, "for some triple of random variables (U, V, W ) such that (U, V, W ) −− X −− (Y, Z)."),
    ("auxrec", 1037, "R0 ≤ min{I(W ; Y ), I(Ŵ ; Y ), I(W ; Z), I(W̃ ; Z)},"),
    ("auxrec", 1038, "R0 + R1 ≤ min{I(W ; Y ), I(W ; Z)} + I(U ; Y |W ),"),
    ("auxrec", 1049, "R0 + R2 ≤ min{I(W ; Y ), I(W ; Z)} + I(V ; Z|W ),"),
    ("auxrec", 1069, "R0 + R1 + R2 ≤ min I(W ; Y ), I(W ; Z)"),
    ("auxrec", 1071, "+ min I(V ; Z|W ) + I(X; Y |V, W ), I(U ; Y |W ) + I(X; Z|U, W ) ,"),
    ("auxrec", 1172, "Remark 12. From (18a), (18b), (18e), (18i), we can extract the following constraints:"),
    ("auxrec", 1177, "This implies that the outer bound in Theorem 7 is at least as good as the U V outer "
                     "bound for all broadcast"),
    ("probc", 123, "It is also established in [8] that when R0 = 0, the UVW outer bound reduces to the "
                   "UV outer bound."),
    ("probc", 134, "• I(X1 ; Y1 ) ≥ I(X1 ; Z1 ), ∀p(x1 ), and I(X2 ; Z2 ) ≥ I(X2 ; Y2 ), ∀p(x2 ),"),
    ("probc", 558, "Theorem 3. The capacity region for a product of reversely more-capable (say, receiver "
                   "Z1 is more"),
    ("probc", 561, "R0 ≤ min{I(W1 ; Y1 ) + I(W2 ; Y2 ), I(W1 ; Z1 ) + I(W2 ; Z2 )}"),
    ("probc", 562, "R0 + R1 ≤ min{I(W1 ; Y1 ) + I(W2 ; Y2 ), I(W1 ; Z1 ) + I(W2 ; Z2 )} + I(U1 ; Y1 |W1 ) "
                   "+ I(X2 ; Y2 |W2 )"),
    ("probc", 563, "R0 + R2 ≤ min{I(W1 ; Y1 ) + I(W2 ; Y2 ), I(W1 ; Z1 ) + I(W2 ; Z2 )} + I(X1 ; Z1 |W1 ) "
                   "+ I(V2 ; Z2 |W2 )"),
    ("probc", 900, "Lemma 8. Let p = 0.1, e = H(0.1) = log2 10 − 0.9 log2 9. Consider a product channel "
                   "formed by the"),
    ("probc", 906, "Proof. From [12], since 1 − e = 1 − H(p) we know that Y1 is more capable than Z1 and "
                   "Z2 is more"),
    ("probc", 469, "= SRM (q1 × q2 ) = SR∗ (q1 × q2 ) <"),
    ("glnsum", 69, "capacity region. Notably, the UVW outer bound yields a strictly larger region, with "
                   "OU V W (T ) ⊋ C(T ) = M(T ). The authors"),
    ("glnsum", 70, "demonstrated that Marton’s inner bound is tight for both reversely more-capable "
                   "product broadcast channels and reversely"),
    ("glnsum", 1435, "TZ|X ∼ BEC(ϵ) and TY |X ∼ BSC(p), coupled with the condition ϵ = H2 (p). Under these "
                     "parameters, it is a well-known"),
    ("sumofbc", 63, "inner bound is the capacity region for both reversely more-capable product broadcast "
                    "channels and reversely semi-deterministic"),
]


def norm_ws(s):
    return " ".join(unicodedata.normalize("NFC", s).split())


def v_quotes():
    lit = os.environ.get("LIT")
    if not lit:
        print("SKIP V   (set LIT=<dir> to re-check the quotations)")
        return
    cache = {}
    bad = []
    for stem, line, text in QUOTES:
        if stem not in cache:
            with open(os.path.join(lit, stem + ".txt"), encoding="utf-8") as fh:
                cache[stem] = fh.read().split("\n")
        actual = cache[stem][line - 1]
        if norm_ws(text) not in norm_ws(actual):
            bad.append("%s:%d" % (stem, line))
    check("V1  %d quotations at their recorded line numbers" % len(QUOTES),
          not bad, "mismatched: " + ", ".join(bad) if bad else "")


# ---------------------------------------------------------------------------
# group I -- (18b)/(18e)/(18i) are the UV constraints verbatim, (18a) is stronger
# ---------------------------------------------------------------------------

def canon(s):
    """Drop layout noise so two printings of the same formula compare equal."""
    s = norm_ws(s)
    for a, b in (("{", "("), ("}", ")"), (" ", ""), (",", " , ")):
        s = s.replace(a, b)
    return norm_ws(s)


def min_args(s):
    """The argument multiset of a top-level min(...) written as `min A, B`."""
    body = s.split("min", 1)[1].strip()
    if body.startswith("(") and body.endswith(")"):
        body = body[1:-1]
    if body.startswith("{") and body.endswith("}"):
        body = body[1:-1]
    depth, cur, out = 0, "", []
    for ch in body:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(canon(cur))
            cur = ""
        else:
            cur += ch
    out.append(canon(cur))
    return sorted(x for x in out if x)


def i_group():
    uv_r1 = "min(I(W ; Y ), I(W ; Z)) + I(U ; Y |W )"          # auxrec:1011
    t7_18b = "min{I(W ; Y ), I(W ; Z)} + I(U ; Y |W )"          # auxrec:1038
    check("I1  (18b) is the UV R0+R1 constraint verbatim", canon(uv_r1) == canon(t7_18b))

    uv_r2 = "min(I(W ; Y ), I(W ; Z)) + I(V ; Z|W )"            # auxrec:1012
    t7_18e = "min{I(W ; Y ), I(W ; Z)} + I(V ; Z|W )"           # auxrec:1049
    check("I2  (18e) is the UV R0+R2 constraint verbatim", canon(uv_r2) == canon(t7_18e))

    # auxrec:1013 vs auxrec:1069+1071 -- the outer min and the inner min, as multisets
    uv_sum_outer = "min I(W ; Y ), I(W ; Z)"
    uv_sum_inner = "min I(U ; Y |W ) + I(X; Z|U, W ), I(V ; Z|W ) + I(X; Y |V, W )"
    t7_sum_outer = "min I(W ; Y ), I(W ; Z)"
    t7_sum_inner = "min I(V ; Z|W ) + I(X; Y |V, W ), I(U ; Y |W ) + I(X; Z|U, W )"
    check("I3  (18i) is the UV sum-rate constraint verbatim (min arguments as multisets)",
          min_args(uv_sum_outer) == min_args(t7_sum_outer)
          and min_args(uv_sum_inner) == min_args(t7_sum_inner))

    uv_r0 = "min(I(W ; Y ), I(W ; Z))"                          # auxrec:1005
    t7_18a = "min{I(W ; Y ), I(Ŵ ; Y ), I(W ; Z), I(W̃ ; Z)}"   # auxrec:1037
    a_uv, a_t7 = min_args(uv_r0), min_args(t7_18a)
    check("I4  (18a) is strictly stronger than the UV R0 constraint (2 extra min arguments)",
          set(a_uv) < set(a_t7) and len(a_t7) == len(a_uv) + 2,
          "UV=%s  Thm7=%s" % (a_uv, a_t7))


# ---------------------------------------------------------------------------
# group B -- box algebra, exact rationals, no optimizer anywhere
# ---------------------------------------------------------------------------

def box_contains(box, R):
    A, B1, B2, S = box
    R0, R1, R2 = R
    return (min(R) >= 0 and R0 <= A and R0 + R1 <= B1 and R0 + R2 <= B2
            and R0 + R1 + R2 <= S)


def rnd_box(rng):
    A = Fraction(rng.randrange(0, 40), 20)
    B1 = A + Fraction(rng.randrange(0, 40), 20)
    B2 = A + Fraction(rng.randrange(0, 40), 20)
    S = max(B1, B2) + Fraction(rng.randrange(0, 40), 20)
    return (A, B1, B2, S)


def rnd_point_in(box, rng):
    A, B1, B2, S = box
    R0 = Fraction(rng.randrange(0, 21), 20) * A
    R1 = Fraction(rng.randrange(0, 21), 20) * max(Fraction(0), min(B1 - R0, S - R0))
    R2 = Fraction(rng.randrange(0, 21), 20) * max(Fraction(0), min(B2 - R0, S - R0 - R1))
    return (R0, R1, R2)


def b_group():
    rng = random.Random(20260809)

    bad = 0
    for _ in range(4000):
        box = rnd_box(rng)
        R = rnd_point_in(box, rng)
        if not box_contains(box, R):
            continue
        phi = (Fraction(0), R[0] + R[1], R[2])
        psi = (Fraction(0), R[1], R[0] + R[2])
        if not (box_contains(box, phi) and box_contains(box, psi)):
            bad += 1
    check("B1  projections phi,psi map every UV/Thm7 box into itself (4000 exact cases)", bad == 0)

    bad = 0
    for _ in range(4000):
        A, B1, B2, S = rnd_box(rng)
        R = rnd_point_in((A, B1, B2, S), rng)
        t = Fraction(rng.randrange(0, 21), 20)
        lhs = R[1] + t * R[2]
        if lhs > (1 - t) * B1 + t * S:
            bad += 1
    check("B2  direction (0,1,t): value <= (1-t)*B1 + t*S  (4000 exact cases)", bad == 0)

    # B3 -- the theta convex combination that closes the cone max(l1,l2) <= l0 <= l1+l2.
    bad_coeff, bad_ineq = 0, 0
    for _ in range(4000):
        l1 = Fraction(rng.randrange(1, 21), 20)
        l2 = Fraction(rng.randrange(1, 21), 20)
        if l1 < l2:
            l1, l2 = l2, l1
        lo = max(l1, (l1 + l2) / 2)          # sample l0 in [max(l1,l2), l1+l2]
        l0 = lo + Fraction(rng.randrange(0, 21), 20) * (l1 + l2 - lo)
        if not (l1 <= l0 <= l1 + l2):
            continue
        # l0 = l1 = l2 is the only degenerate case in this cone; there mu = (l0,l0)
        # and either projection alone already gives lambda.R = mu.(R0+R1, R2).
        theta = (Fraction(1) if 2 * l0 - l1 - l2 == 0
                 else Fraction(l0 - l2, 2 * l0 - l1 - l2))
        if not (0 <= theta <= 1):
            bad_coeff += 1
            continue
        mu1, mu2 = l0, l1 + l2 - l0
        # theta * mu.(R0+R1, R2) + (1-theta) * mu'.(R1, R0+R2) must equal lambda.R
        R = tuple(Fraction(rng.randrange(0, 40), 20) for _ in range(3))
        lhs = (theta * (mu1 * (R[0] + R[1]) + mu2 * R[2])
               + (1 - theta) * (mu2 * R[1] + mu1 * (R[0] + R[2])))
        if lhs != l0 * R[0] + l1 * R[1] + l2 * R[2]:
            bad_coeff += 1
        # and hence: both projections in a symmetric K  =>  lambda.R <= h_K(mu)
        hK = Fraction(rng.randrange(20, 60), 20)
        if (mu1 * (R[0] + R[1]) + mu2 * R[2] <= hK
                and mu2 * R[1] + mu1 * (R[0] + R[2]) <= hK
                and l0 * R[0] + l1 * R[1] + l2 * R[2] > hK):
            bad_ineq += 1
    check("B3  cone: theta=(l0-l2)/(2l0-l1-l2) reproduces lambda exactly and forces "
          "lambda.R <= h_K(l0, l1+l2-l0)  (4000 exact cases)",
          bad_coeff == 0 and bad_ineq == 0)

    bad = 0
    for _ in range(4000):
        l1 = Fraction(rng.randrange(0, 21), 20)
        l2 = Fraction(rng.randrange(0, 21), 20)
        l0 = l1 + l2 + Fraction(rng.randrange(0, 21), 20)
        cap = Fraction(rng.randrange(1, 40), 20)
        R = tuple(Fraction(rng.randrange(0, 40), 20) for _ in range(3))
        if R[0] <= cap and R[0] + R[1] <= cap and R[0] + R[2] <= cap and min(R) >= 0:
            if l0 * R[0] + l1 * R[1] + l2 * R[2] > l0 * cap:
                bad += 1
    check("B4  l0 >= l1+l2: R0,R0+R1,R0+R2 <= cap forces lambda.R <= l0*cap (4000 exact cases)",
          bad == 0)

    # B5 -- negative control (the shape of bc-facts.md ## N6 (T3c) N6-n):
    # equal R0=0 slices do NOT force equal support outside the cone.
    outer = (Fraction(1, 2), Fraction(1), Fraction(1), Fraction(1))
    inner = (Fraction(0), Fraction(1), Fraction(1), Fraction(1))

    def sup211(box):
        A, B1, B2, S = box
        best = Fraction(0)
        for R0 in (Fraction(0), A):
            for R1 in (Fraction(0), B1 - R0, S - R0):
                for R2 in (Fraction(0), B2 - R0, S - R0 - R1):
                    R = (R0, R1, R2)
                    if box_contains(box, R):
                        best = max(best, 2 * R0 + R1 + R2)
        return best

    check("B5  negative control: identical R0=0 slices, support at (2,1,1) is 3/2 vs 1 "
          "=> the R0 ceiling is load-bearing outside the cone",
          sup211(outer) == Fraction(3, 2) and sup211(inner) == Fraction(1),
          "outer=%s inner=%s" % (sup211(outer), sup211(inner)))


# ---------------------------------------------------------------------------
# the instance
# ---------------------------------------------------------------------------

def h2(x):
    if x <= 0.0 or x >= 1.0:
        return 0.0
    return -x * math.log2(x) - (1 - x) * math.log2(1 - x)


def star(b, p):
    return b * (1 - p) + (1 - b) * p


class Instance(object):
    """BEC(e) x BSC(p) crossed product; e <= h(p) is the reversely more-capable range."""

    def __init__(self, p=0.1, e=None):
        self.p = p
        self.e = h2(p) if e is None else e
        self.C1 = 1.0 - self.e          # BEC capacity  (block a -> Y, block b -> Z)
        self.C2 = 1.0 - h2(p)           # BSC capacity  (block a -> Z, block b -> Y)
        # X = (x1,x2) in {0,1}^2 ; Y = (Y1,Y2) with Y1 in {0,1,E}, Y2 in {0,1}
        e_, p_ = self.e, self.p
        bec = np.array([[1 - e_, 0.0, e_], [0.0, 1 - e_, e_]])
        bsc = np.array([[1 - p_, p_], [p_, 1 - p_]])
        self.MY = np.array([np.kron(bec[x1], bsc[x2]) for x1 in (0, 1) for x2 in (0, 1)])
        self.MZ = np.array([np.kron(bsc[x1], bec[x2]) for x1 in (0, 1) for x2 in (0, 1)])
        self.HYgX = h2(e_) + h2(p_)
        self.HZgX = h2(p_) + h2(e_)
        self.unif = np.full(4, 0.25)

    def HY(self, s):
        return ent(s @ self.MY)

    def HZ(self, s):
        return ent(s @ self.MZ)

    def IXY(self, s):
        return self.HY(s) - self.HYgX

    def IXZ(self, s):
        return self.HZ(s) - self.HZgX

    def psi(self, t, b):
        return t * self.C1 * h2(b) - h2(star(b, self.p)) + h2(self.p)

    def dstar(self, t, n=200001):
        bs = np.linspace(0.0, 0.5, n)
        return max(self.psi(t, b) for b in bs)

    def argdstar(self, t, n=200001):
        bs = np.linspace(0.0, 0.5, n)
        vals = [self.psi(t, b) for b in bs]
        return bs[int(np.argmax(vals))]


def ent(q):
    q = np.asarray(q, dtype=float)
    q = q[q > 0]
    return float(-(q * np.log2(q)).sum())


def hC(inst, lam, dstar_cache=None):
    """Closed form of the support function of C -- proved in this leg:
    h_C(lambda) = a * ((C1+C2) + dstar_{b/a}),  a = max(lambda), b = min(l1,l2,(l1+l2-l0)+)."""
    l0, l1, l2 = lam
    a = max(l0, l1, l2)
    b = min(l1, l2, max(0.0, l1 + l2 - l0))
    if a == 0:
        return 0.0
    t = b / a
    d = dstar_cache(t) if dstar_cache else inst.dstar(t)
    return a * ((inst.C1 + inst.C2) + d)


def beta_split_box(inst, beta):
    """[probc] Theorem 3 box for the explicit witness
    W_b = W_a = beta-split, U_b = V_a = const.  Returns (M, B1, B2, S)."""
    C1, p = inst.C1, inst.p
    Mc = (1 - h2(star(beta, p))) + C1 * (1 - h2(beta))
    B1 = Mc + C1 * h2(beta)
    B2 = Mc + C1 * h2(beta)
    S = Mc + 2 * C1 * h2(beta)
    return (Mc, B1, B2, S)


def d_group():
    inst = Instance()
    C = inst.C1
    check("D1a  C = 1-H(0.1) reproduces bc-facts N6-a (0.5310044064)",
          abs(C - 0.5310044064) < 5e-10, "C=%.10f" % C)
    check("D1b  C1 = C2 on the curve e = h(p)", abs(inst.C1 - inst.C2) < 1e-15)
    d1 = inst.dstar(1.0)
    a1 = inst.argdstar(1.0)
    check("D1c  d* reproduces bc-facts N6-a (0.0387713705), alpha* (0.0776696701)",
          abs(d1 - 0.0387713705) < 5e-9 and abs(a1 - 0.0776696701) < 5e-6,
          "d*=%.10f alpha*=%.8f" % (d1, a1))
    check("D1d  SR_C = 2C + d* reproduces bc-facts N6-a (1.1007801833)",
          abs(2 * C + d1 - 1.1007801833) < 1e-8, "SR_C=%.10f" % (2 * C + d1))

    hy = [ent(inst.MY[x]) for x in range(4)]
    hz = [ent(inst.MZ[x]) for x in range(4)]
    check("D2  H(Y|X=x) and H(Z|X=x) are constant over the 4 inputs (both = h(e)+h(p))",
          max(hy) - min(hy) < 1e-15 and max(hz) - min(hz) < 1e-15
          and abs(hy[0] - hz[0]) < 1e-15 and abs(hy[0] - (h2(inst.e) + h2(inst.p))) < 1e-15)

    rng = np.random.default_rng(20260809)
    worst = -1.0
    for _ in range(20000):
        s = rng.dirichlet(np.full(4, 0.6))
        worst = max(worst, inst.HY(s) - inst.HY(inst.unif))
    check("D3  H(Y)_p <= H(Y)_uniform (20000 laws; the 2-line proof is "
          "H(Y1Y2)<=H(Y1)+H(Y2)<=max)", worst <= 1e-12, "max excess = %.3e" % worst)

    # D4 -- the per-point identity behind N7-b's chain.  Holds for EVERY s, so no
    # optimization is involved:  H(Y)_unif - t H(Z|X) - f_t(s) = I(X;Y)_unif + [t I(X;Z)_s - I(X;Y)_s]
    resid = 0.0
    for _ in range(20000):
        s = rng.dirichlet(np.full(4, 0.6))
        t = float(rng.random())
        lhs = inst.HY(inst.unif) - t * inst.HZgX - (inst.HY(s) - t * inst.HZ(s))
        rhs = inst.IXY(inst.unif) + (t * inst.IXZ(s) - inst.IXY(s))
        resid = max(resid, abs(lhs - rhs))
    check("D4  identity  H(Y)_unif - t*H(Z|X) - f_t(s) = I(X;Y)_unif + [t I(X;Z)_s - I(X;Y)_s] "
          "for every s (20000 cases)", resid < 1e-12, "max residual = %.3e" % resid)

    check("D4b  I(X;Y)_uniform = C1 + C2 (= 2C on the curve)",
          abs(inst.IXY(inst.unif) - (inst.C1 + inst.C2)) < 1e-14
          and abs(inst.IXZ(inst.unif) - (inst.C1 + inst.C2)) < 1e-14)

    # D5/D6/D7 -- the explicit [probc] Theorem 3 witness that supplies the C side.
    resid_id, resid_sup, bad_vertex = 0.0, 0.0, 0
    for beta in np.linspace(0.0, 0.5, 501):
        M, B1, B2, S = beta_split_box(inst, beta)
        R1b = inst.C1 + 1 - h2(star(beta, inst.p))
        R2b = inst.C1 * h2(beta)
        resid_id = max(resid_id, abs(B1 - R1b), abs(B2 - R1b),
                       abs(S - (R1b + R2b)), abs(M - (R1b - R2b)))
        for t in (0.0, 0.25, 0.5, 0.75, 1.0):
            resid_sup = max(resid_sup,
                            abs((R1b + t * R2b) - ((inst.C1 + inst.C2) + inst.psi(t, beta))))
        top = (M, B1 - M, B2 - M)
        if not (abs(top[0] - (R1b - R2b)) < 1e-12 and abs(top[1] - R2b) < 1e-12
                and abs(top[2] - R2b) < 1e-12):
            bad_vertex += 1
        if not (top[0] <= M + 1e-12 and top[0] + top[1] <= B1 + 1e-12
                and top[0] + top[2] <= B2 + 1e-12 and sum(top) <= S + 1e-12):
            bad_vertex += 1
    check("D5  beta-split witness: Theorem 3 box = (M,B1,B2,S) with B1=B2=R1(b), S=R1(b)+R2(b), "
          "M=R1(b)-R2(b)  (501 values of beta)", resid_id < 1e-12,
          "max residual = %.3e" % resid_id)
    check("D6  its top vertex is exactly (R1(b)-R2(b), R2(b), R2(b)) and all 4 constraints are tight",
          bad_vertex == 0)
    check("D7  R1(b) + t*R2(b) = (C1+C2) + psi_t(b)  (501 x 5 pairs)",
          resid_sup < 1e-12, "max residual = %.3e" % resid_sup)

    # D8 -- Omega(t) >= dstar_t by an explicit product law (the easy direction; the
    # hard direction Omega(t) <= dstar_t is imported from bc-facts N10-a and is NOT
    # re-derived here).
    worst = 1e9
    for t in np.linspace(0.0, 1.0, 21):
        b = inst.argdstar(float(t))
        s = np.array([(1 - b), 0.0, b, 0.0])          # X1 = 0 deterministic, X2 ~ Bern(b)
        s = np.array([(1 - b), b, 0.0, 0.0])          # index order (x1,x2): x1=0 fixed
        val = t * inst.IXZ(s) - inst.IXY(s)
        worst = min(worst, val - inst.dstar(float(t)))
    check("D8  Omega(t) >= dstar_t by the explicit product law X1=0, X2~Bern(beta*_t) (21 values)",
          worst > -1e-9, "min slack = %.3e" % worst)


# ---------------------------------------------------------------------------
# UV evaluation (used only by the screens in group R)
# ---------------------------------------------------------------------------

def uv_box(inst, pw, sw, usplit, vsplit):
    """(m, B1, B2, S) of the UVW box for the witness described by
    pw[w], sw[w] (input law given W=w), usplit[w] / vsplit[w] (lists of
    (weight, law) refining sw[w])."""
    p = sum(pw[w] * sw[w] for w in range(len(pw)))
    HYp, HZp = inst.HY(p), inst.HZ(p)
    HYw = sum(pw[w] * inst.HY(sw[w]) for w in range(len(pw)))
    HZw = sum(pw[w] * inst.HZ(sw[w]) for w in range(len(pw)))
    IWY, IWZ = HYp - HYw, HZp - HZw
    m = min(IWY, IWZ)
    u = HYw - sum(pw[w] * q * inst.HY(s) for w in range(len(pw)) for q, s in usplit[w])
    v = HZw - sum(pw[w] * q * inst.HZ(s) for w in range(len(pw)) for q, s in vsplit[w])
    IXZ_UW = sum(pw[w] * q * inst.HZ(s) for w in range(len(pw)) for q, s in usplit[w]) - inst.HZgX
    IXY_VW = sum(pw[w] * q * inst.HY(s) for w in range(len(pw)) for q, s in vsplit[w]) - inst.HYgX
    S = m + min(u + IXZ_UW, v + IXY_VW)
    return (m, m + u, m + v, S)


def box_support(box, lam):
    """max lambda.R over {R>=0: R0<=A, R0+R1<=B1, R0+R2<=B2, R0+R1+R2<=S} by vertex
    enumeration (3 variables, 7 halfspaces)."""
    A, B1, B2, S = box
    rows = [(1, 0, 0, A), (1, 1, 0, B1), (1, 0, 1, B2), (1, 1, 1, S),
            (-1, 0, 0, 0.0), (0, -1, 0, 0.0), (0, 0, -1, 0.0)]
    best = 0.0
    for trip in itertools.combinations(range(7), 3):
        Amat = np.array([rows[i][:3] for i in trip], dtype=float)
        bvec = np.array([rows[i][3] for i in trip], dtype=float)
        if abs(np.linalg.det(Amat)) < 1e-12:
            continue
        R = np.linalg.solve(Amat, bvec)
        if min(R) < -1e-10:
            continue
        if (R[0] <= A + 1e-10 and R[0] + R[1] <= B1 + 1e-10
                and R[0] + R[2] <= B2 + 1e-10 and R.sum() <= S + 1e-10):
            best = max(best, float(np.dot(lam, R)))
    return best


def split_by(s, mode):
    """Refine the law s on X=(x1,x2) by revealing const / x1 / x2 / x."""
    if mode == "const":
        return [(1.0, np.asarray(s, dtype=float))]
    groups = {"x1": [[0, 1], [2, 3]], "x2": [[0, 2], [1, 3]],
              "x": [[0], [1], [2], [3]]}[mode]
    out = []
    for g in groups:
        mass = np.zeros(4)
        mass[g] = np.asarray(s, dtype=float)[g]
        tot = float(mass.sum())
        if tot > 0:
            out.append((tot, mass / tot))
    return out


def structured_Ws(inst):
    """W = const / product of two independent beta-splits / W = X."""
    out = [(np.array([1.0]), [inst.unif.copy()])]
    for beta in np.linspace(0.0, 0.5, 51):
        b0 = np.array([1 - beta, beta])
        b1 = np.array([beta, 1 - beta])
        sw = [np.kron(a, b) for a in (b0, b1) for b in (b0, b1)]
        out.append((np.full(4, 0.25), sw))
    out.append((np.full(4, 0.25), [np.eye(4)[i] for i in range(4)]))
    return out


def random_uv_witness(inst, rng, nw=3, nu=3, nv=3):
    pw = rng.dirichlet(np.full(nw, 1.0))
    sw = [rng.dirichlet(np.full(4, rng.choice([0.3, 1.0, 3.0]))) for _ in range(nw)]
    usplit, vsplit = [], []
    for w in range(nw):
        for out in (usplit, vsplit):
            q = rng.dirichlet(np.full(nu, 1.0))
            parts = rng.dirichlet(np.full(nu, 1.0), size=4)   # x -> distribution over u
            laws = []
            for j in range(nu):
                mass = sw[w] * parts[:, j]
                tot = mass.sum()
                if tot <= 0:
                    laws.append((0.0, sw[w]))
                else:
                    laws.append((float(tot), mass / tot))
            out.append(laws)
    return pw, sw, usplit, vsplit


def d_symmetry_and_ceiling():
    """D10 -- the instance is invariant under (swap the two blocks, swap Y and Z),
    which is what makes C|_{R0=0} symmetric in (R1,R2) and lets the mirror
    direction (0,t,1) inherit the (0,1,t) bound.
    D11 -- max_p I(X;Y) = max_p I(X;Z) = C1 + C2, the ceiling used for l0 >= l1+l2."""
    inst = Instance()
    # block swap on the input: index 2*x1+x2 -> 2*x2+x1 ; output factor swap on Y/Z
    perm = [0, 2, 1, 3]
    MYs = inst.MY[perm].reshape(4, 3, 2).transpose(0, 2, 1).reshape(4, 6)
    check("D10  channel symmetry: (block swap, Y<->Z) maps the instance to itself "
          "=> C and UV are symmetric in (R1,R2)",
          np.abs(MYs - inst.MZ).max() < 1e-15,
          "max |MY^sigma - MZ| = %.3e" % float(np.abs(MYs - inst.MZ).max()))

    rng = np.random.default_rng(31337)
    worst = -1e9
    for _ in range(50000):
        s = rng.dirichlet(np.full(4, rng.choice([0.3, 1.0, 3.0])))
        worst = max(worst, inst.IXY(s) - (inst.C1 + inst.C2), inst.IXZ(s) - (inst.C1 + inst.C2))
    check("D11  I(X;Y), I(X;Z) <= C1+C2 (identity route H(Y1Y2)<=H(Y1)+H(Y2) with "
          "H(Y|X) additive) and equality at uniform",
          worst <= 1e-12 and abs(inst.IXY(inst.unif) - (inst.C1 + inst.C2)) < 1e-14,
          "max excess = %.3e" % worst)


def d9_touching_witness():
    """The UV witness W = (beta-split, beta-split), U = X1, V = X2 reproduces the
    [probc] Theorem 3 box of the same beta term by term -- so C and UV touch at
    every one of these boxes rather than merely being nested."""
    inst = Instance()
    worst = 0.0
    for beta in np.linspace(0.0, 0.5, 201):
        b0 = np.array([1 - beta, beta])
        b1 = np.array([beta, 1 - beta])
        sw = [np.kron(a, b) for a in (b0, b1) for b in (b0, b1)]
        pw = np.full(4, 0.25)
        box = uv_box(inst, pw, sw, [split_by(s, "x1") for s in sw],
                     [split_by(s, "x2") for s in sw])
        ref = beta_split_box(inst, beta)
        worst = max(worst, max(abs(a - b) for a, b in zip(box, ref)))
    check("D9  UV witness (W = product beta-splits, U = X1, V = X2) reproduces the "
          "Theorem 3 box term by term (201 values of beta)",
          worst < 1e-12, "max residual = %.3e" % worst)


def r_group():
    inst = Instance()
    cache = {}

    def dcache(t):
        key = round(t, 9)
        if key not in cache:
            cache[key] = inst.dstar(key)
        return cache[key]

    # R1 -- control: on [probc]'s reversely SEMI-DETERMINISTIC instance the very same
    # premise (UV|_{R0=0} inside C|_{R0=0}) is false, by the paper's own numbers.
    check("R1  control: [probc] Claim 3 gives SR_M = 8/3 < 44/15 <= SR_UV "
          "=> the premise this leg verifies is genuinely instance-specific",
          Fraction(8, 3) < Fraction(44, 15),
          "8/3=%.10f < 44/15=%.10f" % (8 / 3, 44 / 15))

    # R2 (SCREEN) -- adversarial search for a UV witness beating h_C.
    rng = np.random.default_rng(4242)
    dirs = [(0.0, 1.0, 1.0), (0.0, 1.0, 0.5), (0.0, 1.0, 0.0), (1.0, 1.0, 1.0),
            (1.2, 1.0, 1.0), (1.5, 1.0, 1.0), (1.8, 1.0, 1.0), (1.3, 1.0, 0.7),
            (1.0, 1.0, 0.5), (2.5, 1.0, 1.0)]
    worst, worst_dir = -1e9, None
    reach = {}
    for lam in dirs:
        target = hC(inst, lam, dcache)
        best = 0.0
        for _ in range(4000):
            w = random_uv_witness(inst, rng, nw=rng.integers(1, 4), nu=3, nv=3)
            best = max(best, box_support(uv_box(inst, *w), lam))
        # structured family: W in {const, product beta-splits, X} x U,V in {const,X1,X2,X}
        modes = ("const", "x1", "x2", "x")
        for pw, sw in structured_Ws(inst):
            for um in modes:
                usplit = [split_by(s, um) for s in sw]
                for vm in modes:
                    vsplit = [split_by(s, vm) for s in sw]
                    best = max(best, box_support(uv_box(inst, pw, sw, usplit, vsplit), lam))
        reach[lam] = (best, target)
        if best - target > worst:
            worst, worst_dir = best - target, lam
    check("R2  SCREEN (no evidential value if it finds nothing): "
          "no UV witness beat h_C in 10 directions x ~4200 witnesses",
          worst <= 1e-7, "largest excess = %.3e at %s" % (worst, str(worst_dir)))

    # R3 -- power check: the same search DOES reach h_C, so it is not stuck below.
    gaps = [(t - b) for b, t in reach.values()]
    check("R3  power check: the search attains h_C (max shortfall over the 10 directions)",
          max(gaps) < 5e-3, "max shortfall = %.3e" % max(gaps))

    # R4 -- the C-side witness and the identities off the curve e = h(p).
    bad = []
    for p, e in ((0.1, 0.2), (0.2, 0.3), (0.05, 0.1), (0.3, 0.5), (0.2, h2(0.2))):
        if e > h2(p):
            bad.append("(%.2f,%.2f) outside the more-capable range" % (p, e))
            continue
        j = Instance(p, e)
        for beta in np.linspace(0.0, 0.5, 101):
            M, B1, B2, S = beta_split_box(j, beta)
            R1b = j.C1 + 1 - h2(star(beta, j.p))
            R2b = j.C1 * h2(beta)
            if max(abs(B1 - R1b), abs(B2 - R1b), abs(S - (R1b + R2b)),
                   abs(M - (R1b - R2b))) > 1e-12:
                bad.append("box (%.2f,%.2f,%.3f)" % (p, e, beta))
            for t in (0.0, 0.5, 1.0):
                if abs((R1b + t * R2b) - ((j.C1 + j.C2) + j.psi(t, beta))) > 1e-12:
                    bad.append("support (%.2f,%.2f,%.3f)" % (p, e, beta))
        rr = np.random.default_rng(7)
        for _ in range(2000):
            s = rr.dirichlet(np.full(4, 0.6))
            t = float(rr.random())
            lhs = j.HY(j.unif) - t * j.HZgX - (j.HY(s) - t * j.HZ(s))
            rhs = j.IXY(j.unif) + (t * j.IXZ(s) - j.IXY(s))
            if abs(lhs - rhs) > 1e-12 or j.HY(s) - j.HY(j.unif) > 1e-12:
                bad.append("identity (%.2f,%.2f)" % (p, e))
                break
    check("R5  every ingredient except Omega(t)=dstar_t re-derives at 5 points of the "
          "half-space e <= h(p)", not bad, "; ".join(sorted(set(bad))[:4]))

    # R6 (SCREEN) -- Omega(t) <= dstar_t re-checked numerically (the proof is N10's).
    rr = np.random.default_rng(11)
    worst = -1e9
    for t in np.linspace(0.0, 1.0, 11):
        d = dcache(float(t))
        for _ in range(30000):
            s = rr.dirichlet(np.full(4, rr.choice([0.3, 1.0, 3.0])))
            worst = max(worst, (t * inst.IXZ(s) - inst.IXY(s)) - d)
        for b1 in np.linspace(0, 1, 41):
            for b2 in np.linspace(0, 1, 41):
                s = np.kron([1 - b1, b1], [1 - b2, b2])
                worst = max(worst, (t * inst.IXZ(s) - inst.IXY(s)) - d)
    check("R6  SCREEN (no evidential value if it finds nothing): Omega(t) <= dstar_t "
          "not violated; the identity itself is imported from bc-facts N10-a",
          worst <= 1e-9, "largest excess = %.3e" % worst)


def main():
    v_quotes()
    i_group()
    b_group()
    d_group()
    d_symmetry_and_ceiling()
    d9_touching_witness()
    r_group()
    n_ok = sum(1 for _, ok, _ in RESULTS if ok)
    print("\n%d/%d" % (n_ok, len(RESULTS)))
    return 0 if n_ok == len(RESULTS) else 1


if __name__ == "__main__":
    sys.exit(main())
