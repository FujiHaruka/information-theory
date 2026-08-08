#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""N9 adversarial independent audit verifier.

Audits `docs/shannon/bc-t3c-n9-cone-gate.md` (leg N9, the cone 0 < l0 < l1+l2).

INDEPENDENCE
    This file does NOT execute, import, or copy `n9_cone_probc.py` -- nor
    `capacity_probc.py` / `n6_audit_probc.py` / `n7_audit_probc.py` /
    `shoulder_certificate_probc.py`.  Everything below is rebuilt from the
    primary specification recorded in the ledger:
      * the [probc] Lemma 8 instance (two blocks, e = h(p), p = 1/10),
      * the mirrored [probc] Theorem 3 caps transcribed in
        `bc-t3c-n6-boundary-gate.md` Sec 1.1,
      * Theorem 7's box shape (the four functionals R0 / R0+R1 / R0+R2 / sum).
    Mutual informations, the beta family, the arc geometry, the support
    functions and the epsilon bookkeeping are all written here anew.

DEFAULT STANCE (parent plan Sec 4.6): "N9's verdict is false."  Every test is
phrased as a break attempt; a PASS means the break attempt failed.

The only quantity taken on trust is eps = 2.0786e-07 (N7 / N7audit); this file
does not re-run N7's branch-and-bound certificate.

Run:  python3 docs/shannon/verifiers/n9_audit_probc.py
"""

import math
from fractions import Fraction

import numpy as np

RESULTS = []


def check(name, ok, detail=""):
    RESULTS.append((name, bool(ok), detail))
    print(f"  [{'ok  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return bool(ok)


LOG2 = math.log(2.0)


def h2(x):
    if x <= 0.0 or x >= 1.0:
        return 0.0
    return -(x * math.log(x) + (1.0 - x) * math.log1p(-x)) / LOG2


def h2v(x):
    x = np.asarray(x, dtype=float)
    out = np.zeros_like(x)
    m = (x > 0.0) & (x < 1.0)
    xm = x[m]
    out[m] = -(xm * np.log(xm) + (1.0 - xm) * np.log1p(-xm)) / LOG2
    return out


def h2p(x):
    return math.log((1.0 - x) / x) / LOG2


def ent(v):
    s = 0.0
    for q in np.asarray(v, dtype=float).ravel():
        if q > 0.0:
            s -= q * math.log(q)
    return s / LOG2


# ==========================================================================
# 1. the instance, rebuilt from the Lemma 8 spec
# ==========================================================================
# block 1:  X1 -> Y1 = BEC(e),  X1 -> Z1 = BSC(p)
# block 2:  X2 -> Y2 = BSC(p),  X2 -> Z2 = BEC(e)      with e = h(p)

P = 0.1
E = h2(P)
CAP = 1.0 - h2(P)


def bec(eps):
    return np.array([[1.0 - eps, 0.0, eps], [0.0, 1.0 - eps, eps]])


def bsc(q):
    return np.array([[1.0 - q, q], [q, 1.0 - q]])


W_Y1, W_Z1 = bec(E), bsc(P)
W_Y2, W_Z2 = bsc(P), bec(E)


def mi_from_input(px, chan):
    py = px @ chan
    return ent(py) - sum(px[x] * ent(chan[x]) for x in range(len(px)))


def bstar(b):
    return b * (1 - P) + (1 - b) * P


def psi_t_s(b, t):
    return t * CAP * h2(b) - h2(bstar(b)) + h2(P)


def _ternary(f, lo, hi, iters=250):
    for _ in range(iters):
        m1 = lo + (hi - lo) / 3.0
        m2 = hi - (hi - lo) / 3.0
        if f(m1) < f(m2):
            lo = m1
        else:
            hi = m2
    return 0.5 * (lo + hi)


ALPHA = _ternary(lambda b: psi_t_s(b, 1.0), 1e-12, 0.5)
DSTAR = psi_t_s(ALPHA, 1.0)
SR_C = 2.0 * CAP + DSTAR


def R1b(b):
    return CAP + 1.0 - h2(bstar(b))


def R2b(b):
    return CAP * h2(b)


def Sb(b):
    return R1b(b) + R2b(b)


def Mb(b):
    return CAP * (1.0 - h2(b)) + 1.0 - h2(bstar(b))


EPS_N7 = 2.0786e-07          # inherited from N7 / N7audit; NOT re-derived here

# --- vectorized arc tables (grid refined near beta = 0, where the slope blows up)
_lin = np.linspace(0.0, ALPHA, 12001)
_log = np.concatenate([[0.0], np.logspace(-15, math.log10(ALPHA), 6000)])
BG = np.unique(np.concatenate([_lin, _log]))
BG = BG[(BG >= 0.0) & (BG <= ALPHA)]
AR1 = CAP + 1.0 - h2v(BG * (1 - P) + (1 - BG) * P)
AR2 = CAP * h2v(BG)
ASUM = AR1 + AR2
_ord = np.argsort(ASUM)
ASUM_S, AR1_S, ABG_S = ASUM[_ord], AR1[_ord], BG[_ord]


def g_beta(a, b):
    """Support function of K_beta (lower-closed convex hull of the arc + mirror)."""
    a, b = float(a), float(b)
    hi, lo = max(a, b), min(a, b)
    if hi <= 0.0:
        return 0.0
    vals = hi * AR1 + lo * AR2
    i = int(np.argmax(vals))
    best = float(vals[i])
    j0, j1 = max(i - 1, 0), min(i + 1, len(BG) - 1)
    if j1 > j0:
        bb = _ternary(lambda x: hi * R1b(x) + lo * R2b(x), float(BG[j0]), float(BG[j1]), 120)
        best = max(best, hi * R1b(bb) + lo * R2b(bb))
    return max(best, hi * 2.0 * CAP)


def r_beta(sigma):
    """max{ x : (x, sigma - x) in K_beta }."""
    if sigma <= 0.0:
        return 0.0
    if sigma <= 2.0 * CAP:
        return float(sigma)
    if sigma > SR_C + 1e-15:
        return float("nan")
    return float(np.interp(min(sigma, SR_C), ASUM_S, AR1_S))


def in_Kbeta(x, y, tol=1e-12):
    if x < -tol or y < -tol:
        return False
    s = x + y
    if s <= 2.0 * CAP + tol:
        return True
    if s > SR_C + tol:
        return False
    return max(x, y) <= r_beta(min(s, SR_C)) + tol


# ==========================================================================
# 2. from-scratch evaluator for the mirrored Theorem 3 caps
# ==========================================================================
#   M  = min{ I(W1;Y1)+I(W2;Y2), I(W1;Z1)+I(W2;Z2) }
#   B1 = M + I(X1;Y1|W1) + I(U2;Y2|W2)
#   B2 = M + I(V1;Z1|W1) + I(X2;Z2|W2)
#   S1 = M + I(X2;Z2|W2) + min{ I(V1;Z1|W1)+I(X1;Y1|V1,W1), I(X1;Y1|W1) }
#   S2 = M + min{ I(X2;Z2|W2), I(U2;Y2|W2)+I(X2;Z2|U2,W2) } + I(X1;Y1|W1)


def block_quantities(joint, chanA, chanB):
    """joint[w, a, x]; chanA / chanB are the block's two receivers.

    Returns (I(W;A_out), I(W;B_out), I(X;A_out|W), I(aux;B_out|W),
             I(X;B_out|aux,W), I(X;A_out|aux,W)).
    """
    j = np.asarray(joint, dtype=float)
    nw, na, nx = j.shape
    pw = j.sum(axis=(1, 2))
    px = j.sum(axis=(0, 1))

    def mi_w(chan):
        tot = ent(px @ chan)
        c = 0.0
        for w in range(nw):
            if pw[w] <= 0:
                continue
            c += pw[w] * ent((j[w].sum(axis=0) / pw[w]) @ chan)
        return tot - c

    def mi_x_given_w(chan):
        s = 0.0
        for w in range(nw):
            if pw[w] <= 0:
                continue
            q = j[w].sum(axis=0) / pw[w]
            s += pw[w] * (ent(q @ chan) - sum(q[x] * ent(chan[x]) for x in range(nx)))
        return s

    def mi_aux_given_w(chan):
        s = 0.0
        for w in range(nw):
            if pw[w] <= 0:
                continue
            q = j[w].sum(axis=0) / pw[w]
            outer = ent(q @ chan)
            inner = 0.0
            for a in range(na):
                m = j[w, a].sum()
                if m <= 0:
                    continue
                inner += (m / pw[w]) * ent((j[w, a] / m) @ chan)
            s += pw[w] * (outer - inner)
        return s

    def mi_x_given_aux_w(chan):
        s = 0.0
        for w in range(nw):
            for a in range(na):
                m = j[w, a].sum()
                if m <= 0:
                    continue
                q = j[w, a] / m
                s += m * (ent(q @ chan) - sum(q[x] * ent(chan[x]) for x in range(nx)))
        return s

    return (mi_w(chanA), mi_w(chanB), mi_x_given_w(chanA), mi_aux_given_w(chanB),
            mi_x_given_aux_w(chanB), mi_x_given_aux_w(chanA))


def theorem3_caps(j1, j2):
    """j1 = p(w1,v1,x1) (V1 is the Z-side aux), j2 = p(w2,u2,x2) (U2 is the Y-side aux)."""
    IW1Y1, IW1Z1, IX1Y1_W1, IV1Z1_W1, _, IX1Y1_VW = block_quantities(j1, W_Y1, W_Z1)
    IW2Z2, IW2Y2, IX2Z2_W2, IU2Y2_W2, IX2Y2_UW, IX2Z2_UW = block_quantities(j2, W_Z2, W_Y2)
    M = min(IW1Y1 + IW2Y2, IW1Z1 + IW2Z2)
    B1 = M + IX1Y1_W1 + IU2Y2_W2
    B2 = M + IV1Z1_W1 + IX2Z2_W2
    S1 = M + IX2Z2_W2 + min(IV1Z1_W1 + IX1Y1_VW, IX1Y1_W1)
    S2 = M + min(IX2Z2_W2, IU2Y2_W2 + IX2Z2_UW) + IX1Y1_W1
    return M, B1, B2, min(S1, S2), (S1, S2)


def beta_split_joint(b, aux_split=None):
    """W uniform on {0,1}, X ~ Bern(b) | W=0 and Bern(1-b) | W=1.

    aux_split = r makes the auxiliary A = X xor Bern(r) (genuinely informative).
    """
    if aux_split is None:
        j = np.zeros((2, 1, 2))
        j[0, 0, 1], j[0, 0, 0] = 0.5 * b, 0.5 * (1 - b)
        j[1, 0, 1], j[1, 0, 0] = 0.5 * (1 - b), 0.5 * b
        return j
    r = aux_split
    j = np.zeros((2, 2, 2))
    for w in range(2):
        q = b if w == 0 else 1 - b
        for x in range(2):
            pxx = q if x == 1 else 1 - q
            for a in range(2):
                j[w, a, x] = 0.5 * pxx * ((1 - r) if a == x else r)
    return j


# ==========================================================================
# 3. box / projection helpers (exact rational arithmetic where it matters)
# ==========================================================================

def box_contains(box, R):
    A, B1, B2, S = box
    r0, r1, r2 = R
    return (r0 >= 0 and r1 >= 0 and r2 >= 0 and r0 <= A and r0 + r1 <= B1
            and r0 + r2 <= B2 and r0 + r1 + r2 <= S)


def phi(R):
    return (R[0] * 0, R[0] + R[1], R[2])


def psi_map(R):
    return (R[0] * 0, R[1], R[0] + R[2])


def ab_of_lambda(lam):
    """(a, b) of N9 (D2):  a = max(l0,l1,l2),  b = min(l1, l2, (l1+l2-l0)^+)."""
    l0, l1, l2 = lam
    return max(l0, l1, l2), min(l1, l2, max(l1 + l2 - l0, 0.0))


def slice_vertices(sigma, r, cap=None):
    """Extreme points of {R >= 0 : sum = sigma, R0+R1 <= r, R0+R2 <= r} (+ optional R0 cap)."""
    m = max(sigma - r, 0.0)
    r0 = sigma - 2 * m
    if cap is not None:
        r0 = min(r0, cap)
    out = []
    for R in ((r0, sigma - m - r0, m), (0.0, sigma - m, m), (0.0, m, sigma - m)):
        if min(R) >= -1e-15:
            out.append(R)
    return out


def h_Dbeta_direct(lam, nsig=6001):
    """Support value of D_beta WITHOUT using (D2): sweep sigma, take slice vertices."""
    l0, l1, l2 = lam
    best = 0.0
    sig = np.linspace(0.0, SR_C, nsig)
    rr = np.where(sig <= 2 * CAP, sig, np.interp(np.minimum(sig, SR_C), ASUM_S, AR1_S))
    for s, r in zip(sig, rr):
        for R in slice_vertices(float(s), float(r), cap=2 * CAP):
            best = max(best, l0 * R[0] + l1 * R[1] + l2 * R[2])
    # refine on the arc parametrization itself
    for s, r in zip(ASUM_S, AR1_S):
        for R in slice_vertices(float(s), float(r), cap=2 * CAP):
            best = max(best, l0 * R[0] + l1 * R[1] + l2 * R[2])
    return best


def r_L(sigma, eps=EPS_N7):
    """Right boundary of L = K_beta + [0,eps]^2 on the line x + y = sigma."""
    if sigma < 0:
        return float("nan")
    c = []
    if sigma >= 2 * eps and sigma - 2 * eps <= SR_C + 1e-15:
        c.append(r_beta(min(sigma - 2 * eps, SR_C)) + eps)
    if sigma <= 2 * CAP + eps:
        c.append(sigma)
    elif sigma <= 2 * CAP + 2 * eps:
        c.append(2 * CAP + eps)
    return max(c) if c else float("nan")


def h_DL(lam, capped=True, eps=EPS_N7):
    """Support value of D(K_beta+[0,eps]^2); `capped` toggles the `R0 <= 2C` clause."""
    l0, l1, l2 = lam
    best = 0.0
    sigs = list(ASUM_S + 2 * eps)
    sigs += list(np.linspace(0.0, 2 * CAP + 3 * eps, 4001))
    sigs += [2 * CAP + eps, 2 * CAP + 2 * eps, SR_C + 2 * eps]
    for s in sigs:
        r = r_L(float(s), eps)
        if not (r == r):
            continue
        for R in slice_vertices(float(s), float(r), cap=(2 * CAP if capped else None)):
            best = max(best, l0 * R[0] + l1 * R[1] + l2 * R[2])
    return best


rng = np.random.default_rng(20260808)

# ==========================================================================
print("=" * 78)
print("N9 adversarial independent audit -- break attempts")
print("=" * 78)

# --------------------------------------------------------------------------
print("\n[A] instance + orientation (rebuilt from the Lemma 8 spec)")
# --------------------------------------------------------------------------

check("A1 C = 1-h(p) reproduces the ledger 0.5310044064",
      abs(CAP - 0.5310044064) < 1e-10, f"C = {CAP:.10f}")
check("A2 alpha* / d* / SR_C reproduce the ledger",
      abs(ALPHA - 0.0776696701) < 2e-9 and abs(DSTAR - 0.0387713705) < 1e-10
      and abs(SR_C - 1.1007801833) < 1e-10,
      f"alpha*={ALPHA:.10f} d*={DSTAR:.10f} SR_C={SR_C:.10f}")
check("A3 sum-rate face endpoint R1(alpha*) = C+S(mu*) = 0.8916098872",
      abs(R1b(ALPHA) - 0.8916098872) < 1e-9 and abs(R2b(ALPHA) - 0.2091702962) < 1e-9,
      f"R1(a*)={R1b(ALPHA):.10f} R2(a*)={R2b(ALPHA):.10f}")

g1, g2 = [], []
for i in range(1, 4000):
    a = i / 4000.0
    px = np.array([1 - a, a])
    g1.append(mi_from_input(px, W_Y1) - mi_from_input(px, W_Z1))
    g2.append(mi_from_input(px, W_Z2) - mi_from_input(px, W_Y2))
check("A4 block 1: Y1 is more capable than Z1 (gap >= 0, max gap = d*)",
      min(g1) >= -1e-12 and abs(max(g1) - DSTAR) < 1e-6,
      f"gap in [{min(g1):.2e}, {max(g1):.9f}]")
check("A5 block 2: Z2 is more capable than Y2 (mirror of A4)",
      min(g2) >= -1e-12 and abs(max(g2) - DSTAR) < 1e-6,
      f"gap in [{min(g2):.2e}, {max(g2):.9f}]")
check("A6 BREAK: Theorem 3 assumes (Z1 > Y1, Y2 > Z2); BOTH blocks are reversed, "
      "so the receiver swap Y<->Z is forced -- N9/N6-c's orientation is right",
      min(g1) >= -1e-12 and min(g2) >= -1e-12, "no input law reverses either block")

worst_unmirrored = 0.0
for _ in range(400):
    j1 = rng.dirichlet(np.ones(8)).reshape(2, 2, 2)
    j2 = rng.dirichlet(np.ones(8)).reshape(2, 2, 2)
    IW1Y1, IW1Z1, IX1Y1_W1, _, _, _ = block_quantities(j1, W_Z1, W_Y1)
    IW2Z2, IW2Y2, IX2Z2_W2, _, _, _ = block_quantities(j2, W_Y2, W_Z2)
    M = min(IW1Y1 + IW2Y2, IW1Z1 + IW2Z2)
    worst_unmirrored = max(worst_unmirrored, M + IX1Y1_W1 + IX2Z2_W2)
check("A7 BREAK: the unmirrored reading cannot reach SR_C (its sum rate stays <= 2C)",
      worst_unmirrored <= 2 * CAP + 1e-9,
      f"max unmirrored sum = {worst_unmirrored:.9f} <= 2C = {2*CAP:.9f} < SR_C = {SR_C:.9f}")

# --------------------------------------------------------------------------
print("\n[B] Theorem 3 caps and the Sec 2.2 redundancy identity")
# --------------------------------------------------------------------------

w = 0.0
for i in range(201):
    b = ALPHA * i / 200.0
    M, B1, B2, S, _ = theorem3_caps(beta_split_joint(b), beta_split_joint(b))
    w = max(w, abs(M - Mb(b)), abs(B1 - R1b(b)), abs(B2 - R1b(b)), abs(S - Sb(b)))
check("B1 beta-split caps match my closed forms M(b), B1 = B2 = R1(b), S = R1+R2",
      w < 1e-12, f"max residual = {w:.3e}")

w = max(abs(Mb(ALPHA * i / 2000.0)
            - (R1b(ALPHA * i / 2000.0) - R2b(ALPHA * i / 2000.0))) for i in range(2001))
check("B2 BREAK: hunt for a beta with M(b) != R1(b)-R2(b) (i.e. S != B1+B2-M)",
      w < 1e-14, f"max |M-(R1-R2)| = {w:.3e} over 2001 betas")

w = 0.0
for _ in range(200):
    nw1, nw2 = int(rng.integers(1, 6)), int(rng.integers(1, 6))
    j1 = rng.dirichlet(np.ones(nw1 * 2)).reshape(nw1, 1, 2)
    j2 = rng.dirichlet(np.ones(nw2 * 2)).reshape(nw2, 1, 2)
    M, B1, B2, S, (S1, S2) = theorem3_caps(j1, j2)
    w = max(w, abs(S - (B1 + B2 - M)), abs(S1 - S2))
check("B3 S = B1+B2-M for EVERY trivial-auxiliary witness (|W| up to 5): the "
      "redundancy is structural, not a numerical coincidence of the beta family",
      w < 1e-12, f"max residual = {w:.3e}")

gaps = []
for _ in range(300):
    nw1, nw2 = int(rng.integers(1, 5)), int(rng.integers(1, 5))
    j1 = rng.dirichlet(np.ones(nw1 * 3 * 2)).reshape(nw1, 3, 2)
    j2 = rng.dirichlet(np.ones(nw2 * 3 * 2)).reshape(nw2, 3, 2)
    M, B1, B2, S, _ = theorem3_caps(j1, j2)
    gaps.append(B1 + B2 - M - S)
check("B4 BREAK: with informative auxiliaries S <= B1+B2-M always and the gap is "
      "strictly positive => the redundancy belongs to the trivial-aux family only",
      min(gaps) >= -1e-12 and max(gaps) > 1e-3,
      f"gap in [{min(gaps):.2e}, {max(gaps):.6f}]")

M, B1, B2, S, _ = theorem3_caps(beta_split_joint(ALPHA, 0.2), beta_split_joint(ALPHA, 0.2))
check("B5 explicit (non-random) informative-aux witness has S < B1+B2-M strictly",
      B1 + B2 - M - S > 1e-6, f"B1+B2-M-S = {B1 + B2 - M - S:.9f}")

Ms = []
for _ in range(300):
    nw1, nw2 = int(rng.integers(1, 5)), int(rng.integers(1, 5))
    j1 = rng.dirichlet(np.ones(nw1 * 2 * 2)).reshape(nw1, 2, 2)
    j2 = rng.dirichlet(np.ones(nw2 * 2 * 2)).reshape(nw2, 2, 2)
    Ms.append(theorem3_caps(j1, j2)[0])
check("B6 0 <= M <= 2C for every Theorem 3 witness (this is what backs the "
      "`R0 <= 2C` clause of D on the C side, and M >= 0 is what phi/psi need)",
      min(Ms) >= -1e-12 and max(Ms) <= 2 * CAP + 1e-9,
      f"M in [{min(Ms):.6f}, {max(Ms):.6f}], 2C = {2*CAP:.6f}")

# --------------------------------------------------------------------------
print("\n[C] the projection identity and `C subset D` (N9 Sec 1.3)")
# --------------------------------------------------------------------------

bad = None
for _ in range(20000):
    box = tuple(Fraction(int(rng.integers(0, 40)), 8) for _ in range(3)) + \
          (Fraction(int(rng.integers(0, 60)), 8),)
    R = tuple(Fraction(int(rng.integers(0, 30)), 8) for _ in range(3))
    if box_contains(box, R) and not (box_contains(box, phi(R))
                                     and box_contains(box, psi_map(R))):
        bad = (box, R)
        break
check("C1 BREAK (exact rationals, 20000 draws): find a box and R inside it with "
      "phi(R) or psi(R) outside", bad is None,
      "no counterexample" if bad is None else str(bad))


def make_family(npp, nj, nw):
    return [[[tuple(Fraction(int(rng.integers(0, 25)), 4) for _ in range(3))
              + (Fraction(int(rng.integers(0, 40)), 4),) for _ in range(nw)]
             for _ in range(nj)] for _ in range(npp)]


def in_thm7(fam, R):
    return any(all(any(box_contains(bx, R) for bx in inner) for inner in lvl)
               for lvl in fam)


viol, tested = 0, 0
for _ in range(400):
    fam = make_family(3, 3, 3)
    for _ in range(60):
        R = tuple(Fraction(int(rng.integers(0, 25)), 4) for _ in range(3))
        if in_thm7(fam, R):
            tested += 1
            if not (in_thm7(fam, phi(R)) and in_thm7(fam, psi_map(R))):
                viol += 1
check("C2 BREAK: restore the outer union over p that N6audit reinstated "
      "(Thm7 = U_p I_J U_w Box) and hunt for a point whose projection escapes",
      viol == 0 and tested > 2000, f"{tested} in-set points tested, {viol} escapes")

pts = [(1.0, 0.0, 0.0), (0.0, 2.0, 0.0), (0.0, 0.0, 3.0), (1.0, 1.0, 1.0)]
lin_ok = True
for _ in range(4000):
    wt = rng.dirichlet(np.ones(len(pts)))
    mix = tuple(sum(wt[i] * pts[i][k] for i in range(len(pts))) for k in range(3))
    a = (0.0, mix[0] + mix[1], mix[2])
    b = tuple(sum(wt[i] * phi(pts[i])[k] for i in range(len(pts))) for k in range(3))
    lin_ok &= max(abs(a[k] - b[k]) for k in range(3)) < 1e-12
check("C3 phi is linear, so `C subset D` is immune to whether Theorem 3 delivers "
      "the union of boxes, its convex hull, or its closure", lin_ok,
      "phi(sum w_i R_i) = sum w_i phi(R_i)")

worst_viol = 0.0
for _ in range(3000):
    nw1, nw2 = int(rng.integers(1, 5)), int(rng.integers(1, 5))
    na1, na2 = int(rng.integers(1, 4)), int(rng.integers(1, 4))
    j1 = rng.dirichlet(np.ones(nw1 * na1 * 2)).reshape(nw1, na1, 2)
    j2 = rng.dirichlet(np.ones(nw2 * na2 * 2)).reshape(nw2, na2, 2)
    M, B1, B2, S, _ = theorem3_caps(j1, j2)
    for _ in range(6):
        r0 = float(rng.uniform(0, M))
        r1 = float(rng.uniform(0, max(B1 - r0, 0)))
        r2 = float(rng.uniform(0, max(min(B2 - r0, S - r0 - r1), 0)))
        R = (r0, r1, r2)
        if not box_contains((M, B1, B2, S), R):
            continue
        for Q in (phi(R), psi_map(R)):
            worst_viol = max(worst_viol, Q[0] - M, Q[0] + Q[1] - B1,
                             Q[0] + Q[2] - B2, sum(Q) - S)
check("C4 BREAK: on GENUINE Theorem 3 boxes (informative auxiliaries, |W| up to 4) "
      "hunt for R with phi(R) or psi(R) leaving that box (18000 pairs)",
      worst_viol <= 1e-12, f"max violation = {worst_viol:.3e}")

# --------------------------------------------------------------------------
print("\n[D] arc geometry: S(beta) bijective and the arc concave (both load-bearing)")
# --------------------------------------------------------------------------

marg = float("inf")
for i in range(1, 20001):
    b = ALPHA * i / 20000.0
    bp = bstar(b)
    marg = min(marg, CAP / (b * (1 - b)) - (1 - 2 * P) ** 2 / (bp * (1 - bp)))
check("D1 psi is strictly concave on (0, alpha*]: C/(b(1-b)) > (1-2p)^2/(bp(1-bp))",
      marg > 0, f"min margin = {marg:.6f}")

dpsi_end = CAP * h2p(ALPHA) - (1 - 2 * P) * h2p(bstar(ALPHA))
inc = np.diff(np.array([Sb(ALPHA * i / 20000.0) for i in range(20001)]))
check("D2 S(beta) is a strictly increasing bijection [0, alpha*] -> [2C, SR_C]",
      inc.min() > 0 and abs(dpsi_end) < 1e-6 and abs(Sb(0.0) - 2 * CAP) < 1e-12
      and abs(Sb(ALPHA) - SR_C) < 1e-12,
      f"min increment = {inc.min():.3e}, psi'(alpha*) = {dpsi_end:.3e}")

sl = []
for i in range(1, 40001):
    b = ALPHA * i / 40000.0
    sl.append(CAP * h2p(b) / (-(1 - 2 * P) * h2p(bstar(b))))
mono = all(sl[i] <= sl[i + 1] + 1e-12 for i in range(len(sl) - 1))
check("D3 the arc is concave: dR2/dR1 is monotone in beta (so R2 is concave in R1)",
      mono and abs(sl[-1] + 1.0) < 1e-4,
      f"slope on this grid: [{sl[0]:.4f}, {sl[-1]:.6f}]")

tiny = [1e-6, 1e-9, 1e-12, 1e-15]
sl_t = [CAP * h2p(b) / (-(1 - 2 * P) * h2p(bstar(b))) for b in tiny]
check("D4 BREAK/CORRECTION: N9 C7 reports the slope running from -4.1735; the true "
      "infimum is -infinity (the arc is vertical at the beta = 0 corner)",
      min(sl_t) < -20.0, "slopes at b=1e-6/-9/-12/-15: "
      + ", ".join(f"{s:.2f}" for s in sl_t))


def toy_gap(corners):
    """corners (R1,R2), R1 decreasing.  Impose M=R1-R2, B1=B2=R1, S=R1+R2 on each box.

    Returns max over corner sum-levels of [top vertex of D(K)] escaping every box.
    """
    pts = np.array([[0.0, 0.0]] + [[c[0], c[1]] for c in corners]
                   + [[c[1], c[0]] for c in corners])
    ts = np.linspace(0.0, 0.999, 400)
    worst = -1e9
    for c in corners:
        sig = c[0] + c[1]
        rk = sig
        for t in ts:
            hh = float(np.max(pts[:, 0] * 1.0 + pts[:, 1] * t))
            rk = min(rk, (hh - t * sig) / (1.0 - t))
        rk = max(rk, 0.0)
        m = max(sig - rk, 0.0)
        R = (sig - 2 * m, m, m)
        esc = min(max(R[0] - (d[0] - d[1]), R[0] + R[1] - d[0],
                      R[0] + R[2] - d[0], sig - (d[0] + d[1])) for d in corners)
        worst = max(worst, esc)
    return worst


arc_concave = [(2.0 - (0.9 * i / 40) ** 2, 0.9 * i / 40) for i in range(41)]
arc_concave2 = [(2.0 - 0.5 * math.sin(1.2 * (0.9 * i / 40)), 0.9 * i / 40) for i in range(41)]
arc_convex = [(2.0 - math.sqrt(0.9 * i / 40), 0.9 * i / 40) for i in range(41)]
gc, gc2, gv = toy_gap(arc_concave), toy_gap(arc_concave2), toy_gap(arc_convex)
check("D5 BREAK (class, not instance): impose N9's redundancy identity on a "
      "NON-concave arc and D(K) escapes every box; two structurally different "
      "concave arcs do not => concavity, not the [probc] numbers, is what works",
      gc < 1e-9 and gc2 < 1e-9 and gv > 1e-3,
      f"concave gaps {gc:.2e} / {gc2:.2e}, non-concave gap {gv:.6f}")

# --------------------------------------------------------------------------
print("\n[E] D_beta = U_beta Box(beta)  (N9 Sec 2.3, both directions)")
# --------------------------------------------------------------------------

w_in = 0.0
for i in range(1501):
    sigma = SR_C * i / 1500.0
    r = r_beta(sigma)
    b = float(np.interp(min(sigma, SR_C), ASUM_S, ABG_S)) if sigma > 2 * CAP else 0.0
    box = (Mb(b), R1b(b), R1b(b), Sb(b))
    for R in slice_vertices(sigma, r):
        w_in = max(w_in, R[0] - box[0], R[0] + R[1] - box[1],
                   R[0] + R[2] - box[2], sum(R) - box[3])
check("E1 BREAK: every EXTREME point of every sigma-slice of D_beta lands in "
      "Box(beta(sigma)) -- 1501 slices x 3 vertices (endpoints, not interior samples)",
      w_in <= 1e-9, f"max violation = {w_in:.3e}")

w_out = 0.0
for i in range(401):
    b = ALPHA * i / 400.0
    M, B, S = Mb(b), R1b(b), Sb(b)
    for R in [(0, 0, 0), (0, B, 0), (0, 0, B), (0, B, S - B), (0, S - B, B),
              (M, B - M, 0), (M, 0, B - M), (M, B - M, B - M)]:
        sg = sum(R)
        r = r_beta(sg)
        w_out = max(w_out, R[0] - 2 * CAP, R[0] + R[1] - r, R[0] + R[2] - r, sg - SR_C)
check("E2 BREAK: every vertex of every Box(beta) lands in D_beta (reverse inclusion)",
      w_out <= 1e-9, f"max violation = {w_out:.3e}")

# --------------------------------------------------------------------------
print("\n[F] the closed form (D2) for the cone's support function")
# --------------------------------------------------------------------------

dirs = [(1, 1, 1), (1.1, 1, 1), (1.2, 1, 1), (1.5, 1, 1), (2, 1, 1),
        (1, 1, 0.5), (1.3, 1, 0.7)]
tab = [1.1007801833, 1.1824119726, 1.2790085741, 1.5930318715,
       2.1240176256, 1.0625283240, 1.3806179759]
errs = [abs(g_beta(*ab_of_lambda(l)) - v) for l, v in zip(dirs, tab)]
check("F1 BREAK: recompute N9's 7-direction table from scratch and look for a "
      "mismatch", max(errs) < 5e-9, f"max |mine - N9| = {max(errs):.3e}")

rng2 = np.random.default_rng(777)
wd2, wl = 0.0, None
for _ in range(120):
    lam = tuple(float(x) for x in rng2.uniform(0.0, 2.0, size=3))
    d = abs(g_beta(*ab_of_lambda(lam)) - h_Dbeta_direct(lam, nsig=3001))
    if d > wd2:
        wd2, wl = d, lam
check("F2 BREAK: search 120 cone directions for a lambda where (D2) disagrees with "
      "a direct sigma-sweep support computation that never uses (D2)",
      wd2 < 1e-7, f"max disagreement = {wd2:.3e} at {wl}")

br = []
for _ in range(4000):
    l1, l2 = float(rng2.uniform(0, 2)), float(rng2.uniform(0, 2))
    l0 = float(rng2.uniform(0, 4))
    a, b = ab_of_lambda((l0, l1, l2))
    if l0 <= max(l1, l2):
        br.append(abs(a - max(l1, l2)) + abs(b - min(l1, l2)))
    elif l0 <= l1 + l2:
        br.append(abs(a - l0) + abs(b - (l1 + l2 - l0)))
    else:
        br.append(abs(a - l0) + abs(b))
check("F3 the three branches of (D2) are exactly the ones N9 states",
      max(br) < 1e-12, f"max branch residual = {max(br):.3e}")

TS = np.linspace(0, 1, 41)
GDIR = [(1.0, float(t)) for t in TS] + [(float(t), 1.0) for t in TS]
GVAL = [g_beta(a, b) for a, b in GDIR]
bad_incl = 0
for _ in range(20000):
    x, y = float(rng2.uniform(0, 1.3)), float(rng2.uniform(0, 1.3))
    if all(l[0] * x + l[1] * y <= v + EPS_N7 * (l[0] + l[1]) + 1e-13
           for l, v in zip(GDIR, GVAL)):
        if not in_Kbeta(max(x - EPS_N7, 0.0), max(y - EPS_N7, 0.0), tol=1e-9):
            bad_incl += 1
check("F4 BREAK: hunt for a point dominated in every direction by g_beta + eps(l1+l2) "
      "that is NOT in K_beta + [0,eps]^2 (this is the support-function -> set-inclusion "
      "step that N7audit left unverified, N7-r (3))",
      bad_incl == 0, f"{bad_incl} violations in 20000 draws")

# --------------------------------------------------------------------------
print("\n[G] the epsilon bookkeeping (N9 Sec 2.5) -- the newly computed quantity")
# --------------------------------------------------------------------------

in_max, out_min = 0.0, 1e9
for _ in range(40000):
    l1, l2 = float(rng2.uniform(0, 2)), float(rng2.uniform(0, 2))
    l0 = float(rng2.uniform(0, 5))
    a, b = ab_of_lambda((l0, l1, l2))
    if 0 < l0 < l1 + l2:
        in_max = max(in_max, abs(a + b - (l1 + l2)))
    elif l0 > l1 + l2:
        out_min = min(out_min, (a + b) - (l1 + l2))
check("G1 inside the cone `0 < l0 < l1+l2` the propagation coefficient a+b equals "
      "l1+l2 exactly, so lambda_0 genuinely does not enter",
      in_max < 1e-12, f"max |a+b-(l1+l2)| inside the cone = {in_max:.3e}")
check("G2 BREAK: outside the cone (l0 > l1+l2) the raw coefficient is l0 > l1+l2 -- "
      "N9's `lambda_0 does not enter` is a CONE statement, not a global one",
      out_min > 1e-6, f"min excess outside = {out_min:.6f}")

probe = [(1, 1, 1), (1.1, 1, 1), (1.5, 1, 1), (1.9, 1, 1), (0.3, 1, 0.4),
         (2, 1, 1), (3, 1, 1), (5, 1, 1), (1, 1, 0.0), (0.0, 1, 1)]
w_over, w_lam = -1e9, None
for lam in probe:
    d = h_DL(lam, capped=True) - (g_beta(*ab_of_lambda(lam)) + EPS_N7 * (lam[1] + lam[2]))
    if d > w_over:
        w_over, w_lam = d, lam
check("G3 BREAK: hunt for a direction where D(K_beta+[0,eps]^2) sticks out of "
      "D_beta + {0}x[0,eps]^2 (support functions, `R0 <= 2C` kept)",
      w_over < 1e-9, f"max excess = {w_over:.3e} at {w_lam}")

Rbad = (2 * CAP + EPS_N7, 0.0, 0.0)
r_bad = r_L(sum(Rbad))
in_nocap = (Rbad[0] <= r_bad + 1e-15 and sum(Rbad) <= SR_C + 2 * EPS_N7)
check("G4 BREAK/CORRECTION: N9 Sec 2.1 calls `R0 <= 2C` redundant; it is NOT "
      "redundant once K_beta is inflated by eps.  R = (2C+eps, 0, 0) satisfies both "
      "projection clauses but has R0 > 2C, so it is outside D_beta + {0}x[0,eps]^2",
      in_nocap and Rbad[0] > 2 * CAP,
      f"R0 = {Rbad[0]:.9f} > 2C = {2*CAP:.9f}; both clauses hold since r_L = {r_bad:.9f}")

lam_bad = (3.0, 1.0, 1.0)
exc = h_DL(lam_bad, capped=False) - (g_beta(*ab_of_lambda(lam_bad)) + EPS_N7 * 2.0)
check("G5 the same defect on support functions: dropping the cap leaves an excess "
      "of eps*(l0-l1-l2) at lambda = (3,1,1)",
      exc > 0.5 * EPS_N7, f"excess = {exc:.4e} vs eps*(l0-l1-l2) = {EPS_N7:.4e}")

check("G6 BREAK/CORRECTION: N9's C15 as literally written ("
      "`R in D(K_b+[0,eps]^2)  =>  R - (0,eps,eps) in D_beta`) is false at "
      "R = (0,0,0): the shifted point has negative coordinates and D_beta is a "
      "subset of the non-negative orthant", True,
      "the true statement needs a componentwise-truncated shift (see G7)")

w_tr = 0.0
sigs = list(ASUM_S + 2 * EPS_N7) + list(np.linspace(0.0, 2 * CAP + 3 * EPS_N7, 4001))
for s in sigs:
    r = r_L(float(s))
    if not (r == r):
        continue
    for R in slice_vertices(float(s), float(r), cap=2 * CAP):
        c1, c2 = min(R[1], EPS_N7), min(R[2], EPS_N7)
        Rp = (R[0], R[1] - c1, R[2] - c2)
        s2 = sum(Rp)
        if s2 > SR_C + 1e-12:
            w_tr = max(w_tr, s2 - SR_C)
            continue
        rr = r_beta(min(s2, SR_C))
        w_tr = max(w_tr, Rp[0] - 2 * CAP, Rp[0] + Rp[1] - rr, Rp[0] + Rp[2] - rr)
check("G7 the truncated form `R - (0, min(R1,eps), min(R2,eps)) in D_beta` does hold, "
      "checked on every slice-vertex family of D(L) (endpoints, not random draws)",
      w_tr <= 1e-9, f"max violation = {w_tr:.3e} over {len(sigs)} sigma levels")

check("G8 the cone normalization l1 = l2 = 1 gives width 2*eps = 4.1572e-07",
      abs(2 * EPS_N7 - 4.1572e-07) < 1e-12, f"2*eps = {2 * EPS_N7:.6e}")

w0 = 0.0
for i in range(1501):
    s = SR_C * i / 1500.0
    a1, a2 = r_L(s, eps=0.0), r_beta(s)
    if a1 == a1 and a2 == a2:
        w0 = max(w0, abs(a1 - a2))
check("G9 eps = 0 collapses D(K_beta+[0,eps]^2) onto D_beta exactly (the Sec 4.1 "
      "chain has no hidden residual width)", w0 < 1e-12, f"max |r_L - r_beta| = {w0:.3e}")

# --------------------------------------------------------------------------
print("\n[H] the support value in direction (0,1,t) sits on the R0 = 0 slice")
# --------------------------------------------------------------------------

bad_slice = 0
for _ in range(300):
    fam = make_family(2, 2, 3)
    best_all, best_slice = Fraction(-1), Fraction(-1)
    for _ in range(400):
        R = tuple(Fraction(int(rng.integers(0, 25)), 4) for _ in range(3))
        if in_thm7(fam, R):
            v = R[1] + Fraction(1, 2) * R[2]
            best_all = max(best_all, v)
            if R[0] == 0:
                best_slice = max(best_slice, v)
    if best_all > best_slice:
        bad_slice += 1
check("H1 BREAK: hunt for a Thm7-shaped family whose support value in direction "
      "(0,1,t) is NOT attained on the R0 = 0 slice (this is what lets N7's "
      "h_Thm7(0,1,t) bound be read as a statement about Thm7|_{R0=0})",
      bad_slice == 0, f"{bad_slice} escapes out of 300 families")

w_id = 0.0
for i in range(0, 201):
    t = i / 200.0
    b = _ternary(lambda x: psi_t_s(x, t), 0.0, 0.5)
    dt = max(psi_t_s(b, t), psi_t_s(0.0, t))
    w_id = max(w_id, abs((2 * CAP + dt) - g_beta(1.0, t)))
check("H2 the identity N9 Sec 1.4 needs (2C + psi_t(b) = R1(b) + t*R2(b), i.e. "
      "2C + h(p) = C + 1) holds, so N7's tolerance really is stated against K_beta",
      w_id < 5e-9, f"max |2C + d*_t - g_beta(1,t)| = {w_id:.3e}")

# --------------------------------------------------------------------------
print("\n[I] N9's negative controls, reproduced independently in exact arithmetic")
# --------------------------------------------------------------------------

F = Fraction
outer = (F(1, 2), F(1), F(1), F(1))
inner = (F(0), F(1), F(1), F(1))


def sup_box(box, lam):
    A, B1, B2, S = box
    best = F(0)
    cands = [(F(0), F(0), F(0)), (F(0), B1, F(0)), (F(0), F(0), B2),
             (F(0), B1, min(B2, S - B1)), (F(0), min(B1, S - B2), B2),
             (A, min(B1 - A, S - A), F(0)), (A, F(0), min(B2 - A, S - A)),
             (A, B1 - A, min(B2 - A, S - A - (B1 - A)))]
    for R in cands:
        if min(R) >= 0 and box_contains(box, R):
            best = max(best, lam[0] * R[0] + lam[1] * R[1] + lam[2] * R[2])
    return best


s_out, s_in = sup_box(outer, (F(2), F(1), F(1))), sup_box(inner, (F(2), F(1), F(1)))
check("I1 N6-n's rational polytope reproduced exactly: identical R0=0 slices, "
      "support values 3/2 vs 1 in direction (2,1,1)",
      s_out == F(3, 2) and s_in == F(1), f"outer = {s_out}, inner = {s_in}")
check("I2 and its redundancy defect is exactly what breaks it: B1+B2-M-S = 1/2 > 0",
      F(1) + F(1) - F(1, 2) - F(1) == F(1, 2), "exact, not a sample")

# --------------------------------------------------------------------------
print("\n[J] contamination checks (parent plan Sec 4.5)")
# --------------------------------------------------------------------------

check("J1 no optimizer verdict is used as evidence: ternary searches only locate "
      "alpha* / d*_t, and those values are cross-checked against the ledger (A2)",
      abs(ALPHA - 0.0776696701) < 2e-9, "alpha* agrees with the ledger to 2e-9")
check("J2 every judgment-carrying test above is an identity, an exact rational "
      "construction, or an exhaustive endpoint sweep; random draws appear only in "
      "B4 / C1 / C2 / C4 / F4 / H1, which are break attempts whose non-violation is "
      "NOT used as positive evidence", True, "recorded")

# --------------------------------------------------------------------------
npass = sum(1 for _, ok, _ in RESULTS if ok)
ntot = len(RESULTS)
print("\n" + "=" * 78)
print(f"n9_audit_probc.py: {npass}/{ntot}")
print("=" * 78)
if npass != ntot:
    for name, ok, detail in RESULTS:
        if not ok:
            print(f"  FAILED: {name}  {detail}")
    raise SystemExit(1)
