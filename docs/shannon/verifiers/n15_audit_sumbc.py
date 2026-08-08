#!/usr/bin/env python3
"""N15 gate (`bc-t3c-n15-instance-gate.md`) の**敵対的独立監査**用の検証器。

⚠ 本ファイルは被監査 leg の `n15_instance_gate.py` を 1 行も読まずに独立に書いた
(親 plan `bc-open-problem-t3c-plan.md` §4.6 の独立実装義務)。
既定の立場は「N15 の主判定 GO は偽である」であり、各チェックは**成立を確かめる**ものではなく
**壊しにいって壊れなかった**ことを記録するものである。

走らせ方:
    python3 docs/shannon/verifiers/n15_audit_sumbc.py               # A1-A8 (逐語照合を除く)
    LIT=<dir> python3 docs/shannon/verifiers/n15_audit_sumbc.py     # + L1-L6 (逐語 + 行番号照合)

`LIT` は `docs/shannon/lit-fetch.sh <dir> glnsum probc auxrec GK-outer` の出力先。
⚠ 抽出テキストは repo が public ゆえコミットしない。

⚠ A1-A8 は `fractions.Fraction` の厳密有理演算のみで、最適化器も許容差も使っていない。
   浮動小数は 1 つも使わない (対数は「指数が一致するときだけ」恒等式で潰す形に限定した)。
"""

import os
import sys
from fractions import Fraction as F

FAIL = []
PASS = []


def chk(name, cond, detail=""):
    (PASS if cond else FAIL).append(name)
    print(f"  [{'ok ' if cond else 'FAIL'}] {name}{('  — ' + detail) if detail else ''}")


# ---------------------------------------------------------------------------
# 段 A — GO の骨 (成果物 §3.4 / §5.1) を印字値からではなく計算で再導出する
# ---------------------------------------------------------------------------
# [glnsum] `:567-578` が印字した成分の重みつき和レート (λ = (1,1,1) の場合のみ):
#   SR_a(α) = 5/3 - (2/3)α  (α ∈ [0,1/2]) ,  4/3  (α ∈ (1/2,1])
#   SR_b(α) = 4/3           (α ∈ [0,1/2]) ,  1 + (2/3)α  (α ∈ (1/2,1])
# ⚠ ここから先は監査の独立計算である (印字された結論 7/3 は使わない)。


def sr_a(alpha):
    return F(5, 3) - F(2, 3) * alpha if alpha <= F(1, 2) else F(4, 3)


def sr_b(alpha):
    return F(4, 3) if alpha <= F(1, 2) else 1 + F(2, 3) * alpha


def corollary1_sumrate_exact():
    """Corollary 1 (17) を λ0 = 1 で評価する。

    (17) は `min_α log2(2^{SR_a(α)} + 2^{SR_b(α)})`。⚠ 対数は一般には有理数にならないので、
    **区分線形性から最小点を決め、そこで 2 つの指数が一致することを使って**恒等式で潰す
    (`2^t + 2^t = 2^{t+1}`)。これは探索ではない。
    """
    # 単調性: [0,1/2] で SR_a は α の減少・SR_b は定数 ⟹ 和の指数和は減少 ⟹ 最小は α=1/2。
    # (1/2,1] で SR_a は定数・SR_b は増加 ⟹ 増加 ⟹ 下限は α→1/2+ で同じ値。
    a_half, b_half = sr_a(F(1, 2)), sr_b(F(1, 2))
    return a_half, b_half


print("段 A — GO の骨の独立再導出 (厳密有理)")
a_half, b_half = corollary1_sumrate_exact()
chk("A1 [0,1/2] で SR_a は減少・SR_b は定数 (最小点が α=1/2 に決まる)",
    sr_a(F(0)) > sr_a(F(1, 2)) and sr_b(F(0)) == sr_b(F(1, 2)),
    f"SR_a: {sr_a(F(0))}->{sr_a(F(1,2))}, SR_b: {sr_b(F(0))}")
chk("A2 (1/2,1] で SR_a は定数・SR_b は増加 (α>1/2 側に改善が無い)",
    sr_a(F(3, 4)) == sr_a(F(1)) and sr_b(F(3, 4)) < sr_b(F(1)),
    f"SR_b: {sr_b(F(3,4))}->{sr_b(F(1))}")
chk("A3 α=1/2 で 2 つの指数が一致する (対数が恒等式で潰れる前提)",
    a_half == b_half, f"SR_a(1/2)=SR_b(1/2)={a_half}")
SR_C = a_half + 1  # log2(2^t + 2^t) = t + 1
chk("A4 SR_M = SR_C = 7/3 (印字値ではなく (17) + 恒等式から)",
    SR_C == F(7, 3), f"SR_C={SR_C}")

# [glnsum] `:604-680` の明示 witness を、印字された相互情報量の値から (2a)-(2e) へ直接代入する。
I_Q = F(1)          # I(Q;Y) = I(Q;Z) = H(Q) = 1        (`:636`)
I_Ua_Ya = F(1, 3)   # (`:651`)
I_Ub_Yb = F(1)      # (`:651`)
I_Va_Za = F(1, 3)   # 鏡映 (`:658`)
I_Vb_Zb = F(1)      # 鏡映 (`:658`)
I_Xa_Za_Ua = F(1)   # (`:666`)
I_Xb_Zb_Ub = F(2, 3)  # (`:666`)
R = (F(0), F(5, 4), F(5, 4))

# W̃ は定数 ⟹ min{I(W̃;Y), I(W̃;Z)} = 0。
c2a = F(0)
c2b = I_Q + F(1, 2) * I_Ua_Ya + F(1, 2) * I_Ub_Yb
c2c = I_Q + F(1, 2) * I_Va_Za + F(1, 2) * I_Vb_Zb
c2d = I_Q + F(1, 2) * I_Ua_Ya + F(1, 2) * I_Ub_Yb + F(1, 2) * I_Xa_Za_Ua + F(1, 2) * I_Xb_Zb_Ub
c2e = c2d  # 鏡映 (`:673`)

print("\n段 A(続) — UVW witness (0,5/4,5/4) を (2a)-(2e) へ直接代入")
chk("A5 (2a) R0 ≤ 0", R[0] <= c2a, f"{R[0]} ≤ {c2a}")
chk("A6 (2b) R0+R1 ≤ 5/3", R[0] + R[1] <= c2b, f"{R[0]+R[1]} ≤ {c2b}")
chk("A6' (2c) R0+R2 ≤ 5/3", R[0] + R[2] <= c2c, f"{R[0]+R[2]} ≤ {c2c}")
chk("A7 (2d)/(2e) 和レート ≤ 5/2", R[0] + R[1] + R[2] <= c2d and c2d == F(5, 2),
    f"{sum(R)} ≤ {c2d}")
chk("A8 SR_UV ≥ 5/2 > 7/3 = SR_C (ギャップが厳密に開く)", F(5, 2) > SR_C,
    f"{F(5,2)} > {SR_C}")

# ---------------------------------------------------------------------------
# 段 B — 生きた方向の錐 d < 2/15 (成果物 §3.4)
# ---------------------------------------------------------------------------
print("\n段 B — 錐 d < 2/15 の独立再計算")


def gap(d):
    """λ = (1,1,1-d) における『UV 側の下界 − C 側の上界』。"""
    lam = (F(1), F(1), F(1) - d)
    lower_uv = lam[0] * R[0] + lam[1] * R[1] + lam[2] * R[2]
    upper_c = SR_C  # λ·R ≤ R0+R1+R2 (R ≥ 0, 0 ≤ d ≤ 1 のとき)
    return lower_uv - upper_c


chk("B1 d = 2/15 でちょうど 0", gap(F(2, 15)) == 0, f"gap={gap(F(2,15))}")
chk("B2 d < 2/15 で正 (d = 1/15)", gap(F(1, 15)) > 0, f"gap={gap(F(1,15))}")
chk("B3 d > 2/15 で非正 (d = 3/15)", gap(F(3, 15)) < 0, f"gap={gap(F(3,15))}")
chk("B4 閾値が厳密有理 2/15 であること ((5/4)(2-d) = 7/3 の解)",
    F(2) - SR_C / F(5, 4) == F(2, 15), f"{F(2) - SR_C/F(5,4)}")

# λ·R ≤ R0+R1+R2 が要る前提 = R ≥ 0。C ⊆ {R ≥ 0} は文献側 ([glnsum] Theorem 1 `:43`
# "non-negative rate triples" / Theorem 3 `:303-304` "any achievable non-negative rate triple")。
# ここでは**その前提を外すと上界が壊れる**ことを 1 本の反例で示し、前提が load-bearing だと記録する。
neg = (F(0), F(0), F(-1))
d0 = F(1, 15)
chk("B5 ⚠ R ≥ 0 を外すと `h_C(λ) ≤ SR_C` は壊れる (前提は load-bearing)",
    (neg[0] + neg[1] + (1 - d0) * neg[2]) > (neg[0] + neg[1] + neg[2]),
    "R2 < 0 の点で λ·R > R0+R1+R2")

# ---------------------------------------------------------------------------
# 段 C — 成果物 §3.4 の「`h_UV(λ) > h_C(λ)` は `d < 2/15` と同値」を壊す
# ---------------------------------------------------------------------------
# 2 本の**片側**評価 (h_UV ≥ …, h_C ≤ …) から出るのは十分条件だけである。
# 逆向き (h_UV > h_C ⟹ d < 2/15) は出ない — 同じ 2 つの入力と整合しつつ
# d > 2/15 で h_UV > h_C となる模型を 1 つ作れば「同値」は反証される。
print("\n段 C — 『同値』主張の反証 (十分条件でしかないことの明示)")
# 模型: C は SR_C = 7/3 を持つが R2 方向に痩せている / UV は witness に加えてもう 1 点を持つ。
C_model = [(F(7, 3), F(0), F(0))]                    # sum-rate 7/3 を達成、R2 = 0
UV_model = [R, (F(0), F(5, 2), F(0))]                # witness + 追加点


def h(region, lam):
    return max(lam[0] * p[0] + lam[1] * p[1] + lam[2] * p[2] for p in region)


d_big = F(1, 2)  # > 2/15
lam_big = (F(1), F(1), F(1) - d_big)
chk("C1 模型が入力と整合 (SR_C = 7/3 / witness ∈ UV)",
    max(sum(p) for p in C_model) == SR_C and R in UV_model)
chk("C2 ⭐ d = 1/2 (> 2/15) でも h_UV > h_C が起きうる ⟹ 『同値』は偽",
    h(UV_model, lam_big) > h(C_model, lam_big),
    f"h_UV={h(UV_model, lam_big)} > h_C={h(C_model, lam_big)}")
chk("C3 ⟹ 成立するのは片向き `d < 2/15 ⟹ h_UV > h_C` のみ",
    gap(F(1, 15)) > 0 and h(UV_model, lam_big) > h(C_model, lam_big))

# ---------------------------------------------------------------------------
# 段 L — 逐語 + 行番号照合 (LIT が渡されたときのみ)
# ---------------------------------------------------------------------------
# ⚠ 被監査 leg が引いた 34 本とは**別に監査が選んだ**、判定の骨に当たる 6 本だけを見る。
LIT = os.environ.get("LIT")
if LIT:
    print("\n段 L — 逐語 + 行番号照合 (監査が独立に選んだ 6 本)")

    def line(stem, n):
        with open(os.path.join(LIT, f"{stem}.txt"), encoding="utf-8") as fh:
            return fh.read().split("\n")[n - 1]

    chk("L1 auxrec:1034 = Theorem 7 (I1 が無条件)",
        "Theorem 7. Given a broadcast channel characterized by T (y, z|x) and any achievable rate triple"
        in line("auxrec", 1034))
    chk("L2 auxrec:1177-1178 = Remark 12 (I2 が無条件)",
        "at least as good as the U V outer bound for all broadcast" in
        line("auxrec", 1177) + " " + line("auxrec", 1178))
    chk("L3 glnsum:61 の witness 条件が一般版 (独立性を課さない)",
        "for some pmf p(u, v, w, x)" in line("glnsum", 61))
    chk("L4 ⚠ glnsum:224-225 Lemma 3 の順序条件は `max{λ1 , λ2 }` であって `λ1 ≥ λ2` ではない",
        "max{λ1 , λ2 }" in line("glnsum", 225) and "λ1 ≥ λ2" not in line("glnsum", 224),
        "成果物 §2.4 の Lemma 3 逐語はここで実文と食い違う")
    chk("L5 glnsum:682 Theorem 4 の順序条件も `max{λ1 , λ2 }`",
        "max{λ1 , λ2 } ≥ 0" in line("glnsum", 682))
    chk("L6 ⚠ glnsum:73 が言うのは `O_UVW ⊋ M` であって `⊋ C` ではない",
        "OU V W (T ) ⊋ M(T )" in line("glnsum", 73) and "C(T )" not in line("glnsum", 73),
        "`⊋ C` は Theorem 4 (M = C) を 1 段挟んで初めて出る")
else:
    print("\n段 L — skip (LIT 未指定。`LIT=<dir>` を渡すと逐語照合が走る)")

print(f"\n=== {len(PASS)}/{len(PASS) + len(FAIL)} pass ===")
if FAIL:
    print("FAILED: " + ", ".join(FAIL))
sys.exit(1 if FAIL else 0)
