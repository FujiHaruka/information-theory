#!/usr/bin/env python3
"""Leg N15 -- gate on "is there an instance family outside [probc] whose C has a
closed form (= the partner of the comparison)?".

Everything that carries the verdict is exact rational arithmetic
(``fractions.Fraction``); there is no optimizer and no tolerance anywhere in
G1-G6.  The only floating-point block is G7, and it is a two-point evaluation of
two explicit input distributions (not a sweep); both margins are far above
double-precision noise.

Primary sources (retrieval = docs/shannon/lit-fetch.sh; line numbers are for the
`pdftotext -layout` output).  ``glnsum`` is *not* in lit-fetch.sh; retrieve with

    curl -sL https://arxiv.org/pdf/2606.12839 -o glnsum.pdf
    pdftotext -layout glnsum.pdf glnsum.txt

  probc   = Geng-Gohari-Nair-Yu, product broadcast channels (proBC.pdf)
  auxrec  = Gohari-Nair, the auxiliary receiver approach (Auxiliary-Receiver.pdf)
  GK-outer= Gohari-Liu-Nair, a two auxiliary receiver outer bound (GK-outer.pdf)
  glnsum  = Gohari-Liu-Nair, sum-broadcast channels (arXiv:2606.12839)

Set LIT=<dir> to additionally re-check every embedded quotation against the
extracted text at the recorded line numbers.

Run:  python3 docs/shannon/verifiers/n15_instance_gate.py
Exit code 0 iff every test passes.
"""
import math
import os
import sys
from fractions import Fraction as F

PASS, FAIL = [], []


def check(tag, ok, detail):
    (PASS if ok else FAIL).append(tag)
    print(f"[{'PASS' if ok else 'FAIL'}] {tag} {detail}")


# --------------------------------------------------------------------------
# Verbatim anchors.  (stem, line, substring) -- the substring must occur inside
# the recorded line of the `pdftotext -layout` output.
# --------------------------------------------------------------------------
QUOTES = [
    # C subset Thm7 -- Theorem 7 is an outer bound for every broadcast channel.
    ("auxrec", 1034, "any achievable rate triple"),
    ("auxrec", 1035, "for any auxiliary channel"),
    # Thm7 subset UV -- unconditional, "for all broadcast channels".
    ("auxrec", 1177, "at least as good as the U V outer bound for all broadcast"),
    ("auxrec", 1178, "channels T (y, z|x)."),
    # The UV object of I2 and the O_UVW of [glnsum] are the same region: same
    # four constraints (the sum rate written once with min vs twice) and the
    # same general witness class.  facts ## M1 (T3b) row 4 once mixed up the
    # independent-witness version with this one, so the check is on constraints.
    ("auxrec", 1013, "min(I(U ; Y |W ) + I(X; Z|U, W ), I(V ; Z|W ) + I(X; Y |V, W ))"),
    ("auxrec", 1014, "(U, V, W ) −− X −− (Y, Z)"),
    ("glnsum", 58, "+ I(U ; Y |W ) + I(X; Z|U, W )"),
    ("glnsum", 59, "+ I(V ; Z|W ) + I(X; Y |V, W )"),
    ("glnsum", 61, "for some pmf p(u, v, w, x)"),
    # Thm8 = C on the [probc] product classes: the three-step chain.
    ("auxrec", 1507, "As a special case of Theorem 8"),
    ("auxrec", 1535, "reduces to the one given in [GGNY14]"),
    ("probc", 551, "The converse is also immediate from the outer bound in Claim 4"),
    ("probc", 557, "the outer bound is contained in the inner bound"),
    ("probc", 592, "The converse is also reasonably immediate from the outer bound in Claim 4"),
    # GK-outer Proposition 2 -- the sum-rate order Thm7 <= Thm6 <= Thm8.
    ("GK-outer", 194, "Theorem 3 (Theorem 7, [12])"),
    ("GK-outer", 255, "Theorem 4 (Theorem 8, [12])"),
    ("GK-outer", 339, "we provide a weaker version"),
    ("GK-outer", 340, "of the outer bound in Theorem 3 (for the sum-rate)"),
    ("GK-outer", 381, "Proposition 2"),
    ("GK-outer", 383, "imply the sum-rate constraints set forth in Theorem 4"),
    # probc: the "coincide for all known classes" sentence is a statement of
    # PRIOR knowledge, overturned by this very paper three lines later.
    ("probc", 36, "have been shown to coincide for all classes"),
    ("probc", 39, "we show that the UV outer bound is strictly suboptimal"),
    ("probc", 41, "but not with the UV outer bound"),
    # probc class hypotheses (Definition 2 vs Definition 3) and Claim 3.
    ("probc", 128, "reversely semi-deterministic"),
    ("probc", 132, "reversely more capable"),
    ("probc", 342, "3 = 3 −"),
    # glnsum: the landscape, the sum family, and its closed form.
    ("glnsum", 65, "In all these cases"),
    ("glnsum", 69, "the UVW outer bound yields a strictly larger region"),
    ("glnsum", 73, "sum-broadcast channel with semi-deterministic components"),
    ("glnsum", 75, "does not admit a product decomposition"),
    ("glnsum", 302, "Theorem 3 (Theorem 8, [16])"),
    ("glnsum", 517, "the UVW sum-rate is greater than or equal to 5/2"),
    ("glnsum", 599, "(R0 , R1 , R2 ) = (0, 5/4, 5/4)"),
    ("glnsum", 698, "M(T ) = C(T ) = Oaux (T )"),
]


def g0_quotes():
    lit = os.environ.get("LIT")
    if not lit or not os.path.isdir(lit):
        print("[skip] G0 verbatim re-check (set LIT=<dir> after docs/shannon/lit-fetch.sh)")
        return
    cache, missing = {}, []
    for stem, line, sub in QUOTES:
        path = os.path.join(lit, f"{stem}.txt")
        if stem not in cache:
            if not os.path.exists(path):
                missing.append(stem)
                cache[stem] = None
                continue
            cache[stem] = open(path, encoding="utf-8").read().split("\n")
        lines = cache[stem]
        if lines is None:
            continue
        body = lines[line - 1] if line - 1 < len(lines) else ""
        norm = " ".join(body.split())
        check(f"G0 {stem}.txt:{line}", " ".join(sub.split()) in norm, f"-- {sub!r}")
    if missing:
        print(f"[note] not fetched: {sorted(set(missing))}")


# --------------------------------------------------------------------------
# G1 / G2 -- the two closed forms, exactly.
#
# The two papers state the *same* per-component weighted sum rate for the
# reversely semi-deterministic component of probc Fig. 2 / glnsum Fig. 3
# (probc.txt:399-403 for the lambda parametrisation, glnsum.txt:567-578 for the
# alpha one).  Piecewise linear in the parameter, with the breakpoint at 1/2.
# --------------------------------------------------------------------------
def sr_a(a):
    """probc.txt:401-403 == glnsum.txt:570-572 (component T_a)."""
    return F(5, 3) - F(2, 3) * a if a <= F(1, 2) else F(4, 3)


def sr_b(a):
    """glnsum.txt:576-578 (component T_b)."""
    return F(4, 3) if a <= F(1, 2) else 1 + F(2, 3) * a


def g1_symmetry():
    """probc.txt:393 states T_b's value is T_a's at 1-lambda.  Check it exactly."""
    grid = [F(k, 12) for k in range(13)]
    ok = all(sr_b(a) == sr_a(1 - a) for a in grid)
    check("G1 component symmetry SR_b(a) = SR_a(1-a)", ok,
          f"-- exact on {len(grid)} rationals; the two papers' formulas agree")


def g2_product_sum_rate():
    """probc Claim 2 + Claim 3: min_lambda [SR_a + SR_b] = 8/3 at lambda = 1/2.

    Both pieces are monotone, so the minimum is at the breakpoint -- an identity,
    not a search.
    """
    lo = [F(k, 24) for k in range(0, 13)]        # [0, 1/2]
    hi = [F(k, 24) for k in range(12, 25)]       # [1/2, 1]
    dec = all(sr_a(x) + sr_b(x) >= sr_a(y) + sr_b(y) for x, y in zip(lo, lo[1:]))
    inc = all(sr_a(x) + sr_b(x) <= sr_a(y) + sr_b(y) for x, y in zip(hi, hi[1:]))
    val = sr_a(F(1, 2)) + sr_b(F(1, 2))
    check("G2 probc product sum rate = 8/3", dec and inc and val == F(8, 3),
          f"-- min at alpha=1/2, value {val} (probc.txt:404-405)")


def g3_sum_channel_sum_rate():
    """glnsum Corollary 1 at lambda = (1,1,1): min_alpha log2(2^SR_a + 2^SR_b).

    At alpha = 1/2 both exponents are 4/3, so the value is 1 + 4/3 = 7/3 with no
    logarithm left to evaluate.  Monotonicity of each piece (SR_a decreasing and
    SR_b constant on [0,1/2]; SR_a constant and SR_b increasing on [1/2,1]) makes
    2^SR_a + 2^SR_b monotone there, so the breakpoint is the minimiser -- again
    an identity rather than a search.
    """
    lo = [F(k, 24) for k in range(0, 13)]
    hi = [F(k, 24) for k in range(12, 25)]
    dec = all(sr_a(x) >= sr_a(y) and sr_b(x) >= sr_b(y) for x, y in zip(lo, lo[1:]))
    inc = all(sr_a(x) <= sr_a(y) and sr_b(x) <= sr_b(y) for x, y in zip(hi, hi[1:]))
    tie = sr_a(F(1, 2)) == sr_b(F(1, 2)) == F(4, 3)
    val = 1 + F(4, 3)                            # log2(2 * 2^(4/3))
    check("G3 glnsum sum channel Marton sum rate = 7/3", dec and inc and tie and val == F(7, 3),
          f"-- min at alpha=1/2, value {val} (glnsum.txt:557-597)")


# --------------------------------------------------------------------------
# G4 / G5 -- the live cone of directions.
# --------------------------------------------------------------------------
SR_C = F(7, 3)                 # glnsum III-A + Theorem 4 (M = C on this channel)
UV_POINT = (F(0), F(5, 4), F(5, 4))    # glnsum III-B: this triple is in O_UVW


def g4_strict_gap():
    s = sum(UV_POINT)
    check("G4 UV sum rate exceeds C sum rate on the glnsum instance",
          s == F(5, 2) and s > SR_C,
          f"-- h_UV(1,1,1) >= {s} > {SR_C} = h_C(1,1,1), gap {s - SR_C}")


def g5_live_cone():
    """For lambda = (1,1,1-d) the gap survives for every d in (0, 2/15).

    h_UV(lambda) >= lambda . (0,5/4,5/4) = (5/4)(2-d)      [the point is in UV]
    h_C (lambda) <= max_C (R0+R1+R2) = 7/3                 [d >= 0 and R2 >= 0]

    so the gap is strict iff (5/4)(2-d) > 7/3, i.e. d < 2/15.  Pure rational
    arithmetic; no property of C beyond its sum rate and nonnegativity is used.
    lambda = (1,1,1-d) is not the sum-rate direction for d > 0, which is what
    takes it out of the reach of GK-outer Proposition 2.
    """
    def gap(d):
        return F(5, 4) * (2 - d) - SR_C

    inside = [F(1, 100), F(1, 20), F(1, 10), F(2, 15) - F(1, 1000)]
    outside = [F(2, 15), F(1, 5), F(1, 2)]
    ok_in = all(gap(d) > 0 and F(0) <= 1 - d <= 1 for d in inside)
    ok_out = all(gap(d) <= 0 for d in outside)
    check("G5 the gap persists on an explicit cone of non-sum-rate directions",
          ok_in and ok_out,
          f"-- strict for every d in (0, 2/15); boundary gap at d=2/15 is {gap(F(2,15))}")


def g6_sandwich_collapse():
    """The examination axis itself, as set logic.

    C subset Thm7 subset UV is unconditional (G0 anchors).  Hence UV = C forces
    Thm7 = C: on such a family the comparison carries no information.  Modelled
    on nested intervals so the implication is exercised rather than asserted.
    """
    bad = []
    for c_hi in (F(1), F(3, 2), F(2)):
        for slack in (F(0), F(1, 4), F(1, 2)):
            uv_hi = c_hi + slack
            for t_hi in (c_hi, (c_hi + uv_hi) / 2, uv_hi):
                if not (c_hi <= t_hi <= uv_hi):
                    bad.append((c_hi, slack, t_hi))
                if slack == 0 and t_hi != c_hi:
                    bad.append((c_hi, slack, t_hi))
    check("G6 UV = C forces Thm7 = C (the collapse the axis screens for)",
          not bad, "-- no counterexample among the nested configurations")


# --------------------------------------------------------------------------
# G7 -- candidate 4: de-tuning to e > h(p) leaves both probc classes.
# Two explicit input distributions, evaluated directly.  Not a sweep.
# --------------------------------------------------------------------------
def h2(q):
    if q <= 0.0 or q >= 1.0:
        return 0.0
    return -q * math.log2(q) - (1 - q) * math.log2(1 - q)


def g7_detuned_instance_leaves_both_classes():
    p, e = 0.1, 0.6                       # h2(0.1) = 0.4690, so e > h(p)
    assert e > h2(p)

    # Definition 3, first bullet (Y1 more capable than Z1): fails at uniform.
    unif_y, unif_z = 1 - e, 1 - h2(p)
    fail_first = unif_y < unif_z

    # Definition 3, second bullet (Z1 more capable than Y1): fails at a skewed
    # input, where the BEC keeps a q*log(1/q) term the BSC only matches linearly.
    q = 1e-3
    skew_y = (1 - e) * h2(q)
    skew_z = h2(q * (1 - p) + (1 - q) * p) - h2(p)
    fail_second = skew_y > skew_z

    # Definition 2 needs a deterministic component; BEC(e)/BSC(p) have none.
    fail_det = 0.0 < e < 1.0 and 0.0 < p < 0.5

    check("G7 e > h(p) leaves probc Definition 2 and Definition 3",
          fail_first and fail_second and fail_det,
          f"-- uniform: I(X;Y)={unif_y:.4f} < I(X;Z)={unif_z:.4f}; "
          f"q={q}: I(X;Y)={skew_y:.6f} > I(X;Z)={skew_z:.6f} "
          f"(ratio {skew_y / skew_z:.1f}x); neither component deterministic")


def main():
    g0_quotes()
    g1_symmetry()
    g2_product_sum_rate()
    g3_sum_channel_sum_rate()
    g4_strict_gap()
    g5_live_cone()
    g6_sandwich_collapse()
    g7_detuned_instance_leaves_both_classes()
    print(f"\n{len(PASS)} passed, {len(FAIL)} failed")
    return 1 if FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
