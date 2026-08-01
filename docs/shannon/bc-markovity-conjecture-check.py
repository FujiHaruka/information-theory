"""Markovity Conjecture (Gohari–Liu–Nair ISIT 2025, Conjecture 2) を我々の 2 補助変数版
Marton 領域の support function の上で数値判定する probe。

対象の逐語引用
--------------
A. Gohari, Y. Liu, C. Nair, *A Conjecture Regarding the Optimizers of Marton's Inner Bound
for the Two-Receiver Broadcast Channel* (ISIT 2025) §II, Conjecture 2:

    "(The Markovity Conjecture) When evaluating the extremal points of Marton's achievable
     region, it is sufficient to consider the random variable tuples (U, V, W, X) such that the
     Markov chain U → (W, X) → V holds. Equivalently, for every arbitrary {ax }, to compute
     F (T, {ax }), it is sufficient to consider the random variable tuples (U, V, X) such that
     the Markov chain U → X → V holds."

判定する命題 (M2 — Conjecture 2 を我々の `def` の上へ移した形)
-------------------------------------------------------------
在庫の Marton 領域は **2 補助変数版** (共通補助 `W` を持たない)。前 leg (L2) が確定させた
閉形式により、四辺形 `InMartonRegion` の theta = (lam, 1-lam), lam in [0,1] 方向の support
function は

    h_quad(lam) = lam*I1 + (1-lam)*I2 - min(lam, 1-lam)*I12

なので、`martonRegionUnion` (= その閉包) の support function は

    h_free(lam) = sup over (pV, K) of h_quad(lam).

M2 はこの sup を Markov 制約つきに絞っても値が変わらない、という主張:

    任意の lam in [0,1] について
      h_free(lam) = h_markov(lam)
        := sup over (pV,K) with V1 ⊥ V2 | X of [lam*I1 + (1-lam)*I2 - min(lam,1-lam)*I12]
    ただし V1 ⊥ V2 | X は p(v1,v2,x) = p(x) p(v1|x) p(v2|x) と書けることを意味する。

`h_markov <= h_free` は制限だから自明。**判定すべきは等号が破れるか**。破れれば M2 は
FALSE (Conjecture 2 の 2 補助変数への移植が我々の def の上で成り立たない、という確定事実)。
破れなければ M2 は生き残る (証拠であって証明ではない)。

M2 は Conjecture 2 の **移植** であって部分族ではない (射程の限定 — 重要)
------------------------------------------------------------------------
形は近い。lam >= 1/2 のとき min(lam,1-lam) = 1-lam なので

    h_quad(lam) = (1-lam) * [ I(V2;Y2) + mu * I(V1;Y1) - I(V1;V2) ],  mu = lam/(1-lam) >= 1

で、論文の `I(U;Y) + lambda*I(V;Z) - I(U;V)` の部分と (U,V) = (V2,V1) で一致する
(lam <= 1/2 は V1 <-> V2 の入れ替えで同じ)。**しかし論文の目的汎関数 (§III eq. (2)) は**

    G = -alpha*H(Y) - (lambda - alpha)*H(Z) + I(U;Y) + lambda*I(V;Z) - I(U;V) + sum_x p(x) a_x

**であり、余分な項 `-alpha*H(Y) - (lambda-alpha)*H(Z) + sum_x p(x) a_x` を恒等的に 0 に
できない**: alpha = 0 と置いても `-lambda*H(Z)` が残り、H(Z) は p(x) の狭義凹関数なので
線形項 `sum_x p(x) a_x` では相殺できない (lambda = 0 の退化点を除く)。したがって

    **M2 に反例が出ても、それは論文の Conjecture 2 の反例ではない。**

構造的な理由: 論文の F は **共通補助変数 W を持つ 3 補助版** Marton 領域の和レート制約
`min(I(W;Y), I(W;Z)) + I(U;Y|W) + I(V;Z|W) - I(U;V|W)` に由来し、`alpha` は
`min(I(W;Y),I(W;Z))` を凸結合 `alpha*I(W;Y) + (lambda-alpha)*I(W;Z)` で押さえたときの
重み、余分なエントロピー項はその `I(W;·) = H(·) - H(·|W)` から出る。**我々の在庫の def
には W が無い**ので、この項が丸ごと欠けている。M2 が破れるということは
「Conjecture 2 の Markov 性を、共通補助 W を落とした我々の def の上へそのまま移すことは
できない」という主張であって、それ以上でも以下でもない。

⚠ 自明な帰着は存在しない
------------------------
任意の p(v1,v2,x) を q(x) q(v1|x) q(v2|x) へ「Markov 化」すると (V1,X) と (V2,X) の周辺は
保たれるので I(V1;Y1) と I(V2;Y2) は **不変** だが、I(V1;V2) は **増えうる** (元が
V1 ⊥ V2 で両者が X と相関している場合、penalty が 0 から正へ増える)。したがって
Markov 化写像は目的値を下げうる = 「Markov 化しても悪くならない」という自明な証明にならない。
このため本 probe では Markov 化点は h_markov の **初期値シード** としてのみ使い、
h_markov は独立に最適化する。

誤差の向きの規律
----------------
判定量は `h_free - h_markov > 0` か。この向きだと **h_markov の最適化不足が偽陽性を作る**
(h_free の最適化不足は逆に偽陰性側 = 安全側)。よって
  * h_markov の restart 数は h_free の 2 倍以上、
  * 正のギャップが出た lam では 3 段の hardening
      (i) h_free の最適点を Markov 化した点をシードに与える、
      (ii) restart をさらに 5 倍、
      (iii) 補助アルファベットを 1 段大きくする、
    をすべて通過して初めてギャップとして報告する。

射程の注意
----------
目的値は W1(y|x) と W2(z|x) の **周辺チャネルにしか依存しない** (I(V1;Y1) / I(V2;Y2) は
周辺だけで決まる) ので、一般 BC T(y,z|x) は (W1,W2) の対で尽くされる。また L2 の結果から
**|X| = 2 の劣化 BSC 対では h_free は時分割包絡 max(lam*C1,(1-lam)*C2) に潰れ**、その達成点
(V1=X,V2=trivial / V1=trivial,V2=X) は Markov 点なので M2 は自明に真。したがって非自明なのは
**|X| >= 3**。走査はそこに集中する。

走査の骨格 (凸包絡 pool) と、なぜ素の 1 点比較では足りないか
------------------------------------------------------------
ギャップの立つ lam の窓は狭い (CEX-1 で幅 0.05 程度) ので、粗い lam 格子で
h_free(lam) と h_markov(lam) を 1 点ずつ比べるだけでは取り逃す。また実測で、素の 1 点比較は
**負のギャップ** (h_free < h_markov、数学的にありえない) を出すことがある = 自由側の
最適化不足。両方を同時に潰すのが凸包絡 pool:

  * h_free も h_markov も lam の凸関数で、ある lam で見つけた三つ組 (I1,I2,I12) は
    全 lam に対するアフィン minorant `phi(lam)` を与える。三つ組を pool に貯めて
    `LB(lam) = max_j phi_j(lam)` を持つ。
  * Markov 点は自由な点でもあるので **pool_markov の三つ組は h_free の下界でもある**。
    `LB_free := max(pool_free, pool_markov)` と取れば負のギャップは構造的に消える。
  * `D(lam) = LB_free(lam) - LB_markov(lam) >= 0` を細かい格子で最大化して lam* を出し、
    **その lam* で** Markov 側の hardening を回す。hardening すると lam* が動くので、
    動かなくなるまで反復する (報告する lam* と hardening した lam* をずらさない)。

実行方法
--------
    python3 docs/shannon/bc-markovity-conjecture-check.py            # 既定 (約 3.5 分)
    python3 docs/shannon/bc-markovity-conjecture-check.py --quick    # 縮小版 (約 25 秒)
    python3 docs/shannon/bc-markovity-conjecture-check.py --full     # 拡大版 (時間無制限)

numpy / scipy が要る。既存の `bc-marton-union-gap-check.py` / `bc-marton-convexhull-check.py` /
`bc_probe.py` / `bc-markovity-localmax-check.py` は **編集しない**。前者からは
`check_sim` / `marton_infos` / `H` / `hb` / `conv` / `bsc` を importlib 経由で読み込む
(ファイル名にハイフンがあり通常の import が効かない)。

この probe が出した結果 (要旨。数値は毎回の実行が SoT)
------------------------------------------------------
**M2 は FALSE** — 反例が出た。既定実行の 10 チャネル中 3 本でギャップが立つ。代表例を
`W1_CEX` / `W2_CEX` として **逐語でハードコードしてある** (`CEX-1`、乱数の種に依存させると
失われるため)。lam* ~ 0.76-0.80 でギャップ約 2e-4 ~ 7e-4。その lam での h_free の最適点は
決定論的 (X = f(V1,V2)) だが **非 Markov (I(V1;V2|X) ~ 3e-3) かつ非 rectangular** で、
論文が §III-B で見つけた非 rectangular 局所最大点と同じ形をしている。
偽陽性でないことは、h_markov 側を 4 系統の独立なオプティマイザ (L-BFGS/softmax、
Nelder-Mead、生の単体上の SLSQP、Dirichlet 直接乱択 24 万本) で叩いても同一値に張り付く
ことで確認した (再現は下記コマンド + hardening 3 段の出力)。

Lean の def との対応 (逐語)
---------------------------
  Shannon/Bridge.lean:40                entropy mu Xs = sum_x negMulLog ((mu.map Xs).real {x})
                                          = -sum_x P(x) log P(x)              (自然対数 = nat)
  Marton/Setup.lean:57                  martonJointDistribution pV K W
                                          : (V1,V2,X,Y1,Y2) の法則 pV -> K -> W
  Marton/Setup.lean:244                 martonInfo₁    = H(V1) + H(Y1) - H(V1,Y1)
  Marton/Setup.lean:252                 martonInfo₂    = H(V2) + H(Y2) - H(V2,Y2)
  Marton/Setup.lean:262                 martonInfoV₁V₂ = H(V1) + H(V2) - H(V1,V2)
  Marton/Basic.lean:40-46               InMartonRegion R1 R2 I1 I2 I12 :
                                          R1 <= I1, R2 <= I2, R1+R2 <= I1+I2-I12
  Operational.lean:127                  martonRegion pV K W
                                          = {p | InMartonRegion p.1 p.2 I1 I2 I12}
  MartonUnion.lean:71-77                martonRegionUnion W
                                          = closure (union over k1 k2 pV K of martonRegion pV K W)
すべて nat。この対応は `bc-marton-union-gap-check.check_sim()` を冒頭でそのまま実行して
再確認する (L2 と同じ手順、再実装しない)。
"""

import argparse
import importlib.util
import itertools
import time
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

HERE = Path(__file__).resolve().parent


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


gap = _load("bc_marton_union_gap_check", HERE / "bc-marton-union-gap-check.py")
H, hb, conv, bsc = gap.H, gap.hb, gap.conv, gap.bsc
marton_infos = gap.marton_infos

rng = np.random.default_rng(20260802)

# L2 の既知ケース (劣化 BSC 対)。`bc-marton-convexhull-check.py` 冒頭と同じ値。
Q_BSC, P_BSC = 0.10, 0.25
W1_BSC, W2_BSC = bsc(Q_BSC), bsc(P_BSC)
C1_BSC = float(np.log(2) - hb(Q_BSC))
C2_BSC = float(np.log(2) - hb(P_BSC))

# Gohari–Liu–Nair §III-B の例のチャネル対 (|X| = 3)。論文が非 rectangular な局所最大点を
# 見つけた具体例なので、非自明な走査点として名前つきで入れる (逐語、
# `bc-markovity-localmax-check.py` の T_Y / T_Z と同じ数値)。
T_Y_GLN = np.array([
    [0.35332099, 0.34718682, 0.29949219],
    [0.76824470, 0.12006556, 0.11168974],
    [0.13810833, 0.48234150, 0.37955017],
])
T_Z_GLN = np.array([
    [0.44260251, 0.21452819, 0.34286930],
    [0.40932411, 0.00992684, 0.58074905],
    [0.27754304, 0.56201647, 0.16044049],
])

# 本 probe が最初に見つけた M2 の反例チャネル対 (|X|=|Y|=|Z|=3)。ランダム生成の種に
# 依存させると失われるので、**逐語でハードコードして常に走査対象に含める**。
# lam* ~ 0.79 付近でギャップ約 5.2e-4 (詳細は判定出力を参照)。
W1_CEX = np.array([
    [0.3207815922, 0.1838072187, 0.4954111891],
    [0.8246265209, 0.1154905838, 0.0598828954],
    [0.2659265446, 0.0230243131, 0.7110491423],
])
W2_CEX = np.array([
    [6.8178330905e-01, 9.7604330643e-06, 3.1820693052e-01],
    [2.1461306484e-04, 9.9975271691e-01, 3.2670027040e-05],
    [4.4469870872e-02, 9.1241110463e-03, 9.4640601808e-01],
])
W1_CEX /= W1_CEX.sum(axis=1, keepdims=True)
W2_CEX /= W2_CEX.sum(axis=1, keepdims=True)

GAP_TOL = 1e-7          # これを超える h_free - h_markov だけを hardening にかける
SUPPORT_TOL = 1e-9      # J の cell を「台に乗っている」とみなす閾値


# ======================================================================
# 1. 目的関数 F = c1*I1 + c2*I2 - c3*I12 と 3 通りのパラメータ化
# ======================================================================
def _L(m):
    return -(np.log(np.maximum(m, 1e-300)) + 1.0)


def _core(J, W1, W2, c1, c2, c3, need_grad):
    """J[v1,v2,x] (正規化済) から F と (I1,I2,I12)、および dF/dJ を返す。

    I1 = H(V1)+H(Y1)-H(V1,Y1), I2 = H(V2)+H(Y2)-H(V2,Y2), I12 = H(V1)+H(V2)-H(V1,V2)
    は `Marton/Setup.lean:244/252/262` の逐語。
    """
    pV1 = J.sum(axis=(1, 2))
    pV2 = J.sum(axis=(0, 2))
    pV12 = J.sum(axis=2)
    pV1Y1 = J.sum(axis=1) @ W1
    pV2Y2 = J.sum(axis=0) @ W2
    pY1, pY2 = pV1Y1.sum(axis=0), pV2Y2.sum(axis=0)
    I1 = H(pV1) + H(pY1) - H(pV1Y1)
    I2 = H(pV2) + H(pY2) - H(pV2Y2)
    I12 = H(pV1) + H(pV2) - H(pV12)
    F = c1 * I1 + c2 * I2 - c3 * I12
    if not need_grad:
        return F, (I1, I2, I12), None
    LV1, LV2, L12 = _L(pV1), _L(pV2), _L(pV12)
    gY1, gY2 = W1 @ _L(pY1), W2 @ _L(pY2)
    gV1Y1, gV2Y2 = _L(pV1Y1) @ W1.T, _L(pV2Y2) @ W2.T
    dJ = (
        c1 * (LV1[:, None, None] + gY1[None, None, :] - gV1Y1[:, None, :])
        + c2 * (LV2[None, :, None] + gY2[None, None, :] - gV2Y2[None, :, :])
        - c3 * (LV1[:, None, None] + LV2[None, :, None] - L12[:, :, None])
    )
    return F, (I1, I2, I12), dJ


def J_pvk(theta, n1, n2, na):
    t = theta[: n1 * n2].reshape(n1, n2)
    u = theta[n1 * n2:].reshape(n1, n2, na)
    pV = np.exp(t - t.max()); pV /= pV.sum()
    K = np.exp(u - u.max(axis=2, keepdims=True)); K /= K.sum(axis=2, keepdims=True)
    return pV[:, :, None] * K, pV, K


def objective_pvk(theta, n1, n2, W1, W2, c1, c2, c3, need_grad=True):
    """(pV, K) の softmax パラメータ化 (`bc-marton-convexhull-check.objective` の一般化:
    W1 / W2 をモジュール定数でなく引数で受ける)。"""
    na = W1.shape[0]
    J, pV, K = J_pvk(theta, n1, n2, na)
    F, tri, dJ = _core(J, W1, W2, c1, c2, c3, need_grad)
    if not need_grad:
        return F, tri, None
    g_p = (dJ * K).sum(axis=2)
    g_t = pV * (g_p - (pV * g_p).sum())
    g_K = dJ * pV[:, :, None]
    g_u = K * (g_K - (K * g_K).sum(axis=2, keepdims=True))
    return F, tri, np.concatenate([g_t.ravel(), g_u.ravel()])


def J_joint(theta, n1, n2, na):
    t = theta.reshape(n1, n2, na)
    J = np.exp(t - t.max()); J /= J.sum()
    return J


def objective_joint(theta, n1, n2, W1, W2, c1, c2, c3, need_grad=True):
    """同時分布 J そのものの softmax。(pV,K) 分解は退化行 (pV=0 の行の K が自由) を
    持つので局所解の地形が違う。パラメータ化の人工物で sup を取りこぼしていないかの
    独立確認に使う。"""
    na = W1.shape[0]
    J = J_joint(theta, n1, n2, na)
    F, tri, dJ = _core(J, W1, W2, c1, c2, c3, need_grad)
    if not need_grad:
        return F, tri, None
    return F, tri, (J * (dJ - (J * dJ).sum())).ravel()


def J_markov(theta, n1, n2, na):
    """Markov 制約つきパラメータ化: p(x), p(v1|x), p(v2|x) から
    J[v1,v2,x] = p(x) p(v1|x) p(v2|x) を組む (= V1 ⊥ V2 | X)。"""
    a = theta[:na]
    b = theta[na: na + na * n1].reshape(na, n1)
    c = theta[na + na * n1:].reshape(na, n2)
    px = np.exp(a - a.max()); px /= px.sum()
    p1 = np.exp(b - b.max(axis=1, keepdims=True)); p1 /= p1.sum(axis=1, keepdims=True)
    p2 = np.exp(c - c.max(axis=1, keepdims=True)); p2 /= p2.sum(axis=1, keepdims=True)
    J = px[None, None, :] * p1.T[:, None, :] * p2.T[None, :, :]
    return J, px, p1, p2


def objective_markov(theta, n1, n2, W1, W2, c1, c2, c3, need_grad=True):
    na = W1.shape[0]
    J, px, p1, p2 = J_markov(theta, n1, n2, na)
    F, tri, dJ = _core(J, W1, W2, c1, c2, c3, need_grad)
    if not need_grad:
        return F, tri, None
    g_px = np.einsum("ijx,xi,xj->x", dJ, p1, p2)
    g_p1 = px[:, None] * np.einsum("ijx,xj->xi", dJ, p2)
    g_p2 = px[:, None] * np.einsum("ijx,xi->xj", dJ, p1)
    g_a = px * (g_px - (px * g_px).sum())
    g_b = p1 * (g_p1 - (p1 * g_p1).sum(axis=1, keepdims=True))
    g_c = p2 * (g_p2 - (p2 * g_p2).sum(axis=1, keepdims=True))
    return F, tri, np.concatenate([g_a, g_b.ravel(), g_c.ravel()])


DIMS = {
    "pvk": lambda n1, n2, na: n1 * n2 + n1 * n2 * na,
    "joint": lambda n1, n2, na: n1 * n2 * na,
    "markov": lambda n1, n2, na: na + na * n1 + na * n2,
}
OBJS = {"pvk": objective_pvk, "joint": objective_joint, "markov": objective_markov}
JBUILD = {"pvk": lambda th, n1, n2, na: J_pvk(th, n1, n2, na)[0],
          "joint": J_joint,
          "markov": lambda th, n1, n2, na: J_markov(th, n1, n2, na)[0]}


# ======================================================================
# 2. 肯定コントロール (c): 解析勾配 vs 中心差分
# ======================================================================
def gradient_check():
    print("=== control (c): 解析勾配の有限差分照合 (3 パラメータ化) ===")
    ok = True
    for kind in ("pvk", "joint", "markov"):
        worst = 0.0
        for (n1, n2, W1, W2) in ((2, 2, W1_BSC, W2_BSC),
                                 (3, 3, T_Y_GLN, T_Z_GLN),
                                 (4, 2, T_Y_GLN, T_Z_GLN)):
            na = W1.shape[0]
            for lam in (0.15, 0.5, 0.85):
                c1, c2, c3 = lam, 1 - lam, min(lam, 1 - lam)
                x = rng.normal(0, 1.5, DIMS[kind](n1, n2, na))
                _, _, g = OBJS[kind](x, n1, n2, W1, W2, c1, c2, c3)
                gn = np.zeros_like(g)
                e = 1e-6
                for i in range(x.size):
                    xp, xm = x.copy(), x.copy()
                    xp[i] += e; xm[i] -= e
                    gn[i] = (OBJS[kind](xp, n1, n2, W1, W2, c1, c2, c3, False)[0]
                             - OBJS[kind](xm, n1, n2, W1, W2, c1, c2, c3, False)[0]) / (2 * e)
                worst = max(worst, float(np.abs(g - gn).max()))
        print(f"  {kind:7s}: |解析勾配 - 中心差分| の最大 = {worst:.3e}")
        ok = ok and worst < 1e-6
    print(f"  -> {'OK' if ok else 'NG'}\n")
    return ok


# ======================================================================
# 3. 最大化ドライバ
# ======================================================================
def maximize(kind, lam, n1, n2, W1, W2, restarts, seeds=(), scale=2.0):
    """指定パラメータ化で F を最大化。(best F, best (I1,I2,I12), best J) を返す。"""
    na = W1.shape[0]
    c1, c2, c3 = lam, 1 - lam, min(lam, 1 - lam)
    dim = DIMS[kind](n1, n2, na)
    obj = OBJS[kind]
    best, best_tri, best_J, best_x = -np.inf, None, None, None
    starts = [np.asarray(s, float) for s in seeds]
    starts += [rng.normal(0, scale, dim) for _ in range(restarts)]
    for x0 in starts:
        if x0.size != dim:
            continue
        res = minimize(
            lambda z: (lambda F, tri, g: (-F, -g))(*obj(z, n1, n2, W1, W2, c1, c2, c3)),
            x0, jac=True, method="L-BFGS-B",
            options={"maxiter": 800, "maxfun": 1600, "ftol": 1e-15, "gtol": 1e-12},
        )
        F, tri, _ = obj(res.x, n1, n2, W1, W2, c1, c2, c3, False)
        if F > best:
            best, best_tri, best_J, best_x = F, tri, JBUILD[kind](res.x, n1, n2, na), res.x
    return best, best_tri, best_J, best_x


def markov_seed(J, n1, n2, na):
    """自由最適点 J を Markov 化した点 q(x) q(v1|x) q(v2|x) の theta 表現。

    ⚠ これは「Markov 化すれば値が保たれる」という主張ではない (冒頭の観察を参照)。
    h_markov の探索を h_free の最適点の近傍へ確実に届かせるための初期値にすぎない。
    """
    px = J.sum(axis=(0, 1))
    pxs = np.maximum(px, 1e-300)
    p1 = (J.sum(axis=1) / pxs[None, :]).T          # (na, n1) = p(v1|x)
    p2 = (J.sum(axis=0) / pxs[None, :]).T          # (na, n2) = p(v2|x)
    lg = lambda p: np.log(np.maximum(p, 1e-12))    # noqa: E731
    return np.concatenate([lg(px), lg(p1).ravel(), lg(p2).ravel()])


def h_free(lam, alphabets, W1, W2, restarts, with_joint=True, seeds=None):
    """h_free(lam) の下界 (alphabets 上の最大)。(値, 三つ組, J, (n1,n2), kind) を返す。

    パラメータ化 2 系統 ((pV,K) と 同時分布 J) の最大を取る。`seeds` は
    {(kind,(n1,n2)): [theta,...]} で warm start を与える。
    """
    best = (-np.inf, None, None, None, None)
    for (n1, n2) in alphabets:
        kinds = ("pvk", "joint") if with_joint else ("pvk",)
        for kind in kinds:
            s = (seeds or {}).get((kind, (n1, n2)), ())
            F, tri, J, x = maximize(kind, lam, n1, n2, W1, W2, restarts, s)
            if F > best[0]:
                best = (F, tri, J, (n1, n2), kind)
            if seeds is not None and x is not None:
                seeds[(kind, (n1, n2))] = [x]      # 次の lam への warm start
    return best


def h_markov(lam, alphabets, W1, W2, restarts, seed_Js=()):
    """h_markov(lam) の下界。seed_Js は Markov 化シードにする自由最適点の列。"""
    na = W1.shape[0]
    best = (-np.inf, None, None, None)
    for (n1, n2) in alphabets:
        seeds = []
        for J in seed_Js:
            if J is not None and J.shape == (n1, n2, na):
                seeds.append(markov_seed(J, n1, n2, na))
        F, tri, J, _ = maximize("markov", lam, n1, n2, W1, W2, restarts, seeds)
        if F > best[0]:
            best = (F, tri, J, (n1, n2))
    return best


# ======================================================================
# 4. 副次出力 — 決定論性と rectangularity
# ======================================================================
def determinism(J):
    """K(x|v1,v2) の決定論性: 台に乗った cell における max_x K の最小値。

    pV を固定すると I12 は K に依らず、I1 / I2 は入力を固定した相互情報量なので K に
    ついて凸 (p(y|v) は K の線形関数)。よって F は K について凸で、最大は端点 =
    決定論的 K で達成される。この出力はその予測の数値確認でもある。
    """
    pV = J.sum(axis=2)
    mask = pV > SUPPORT_TOL
    if not mask.any():
        return 0.0, mask
    K = J / np.maximum(pV[:, :, None], 1e-300)
    return float(K.max(axis=2)[mask].min()), mask


def rectangular(J):
    """誘導される写像 f(v1,v2) = argmax_x K が rectangular (各 x の逆像が S_x × T_x) か。

    論文 §II-A の定義を一般の |X| へ広げたもの (`bc-markovity-localmax-check.is_rectangular`
    は |X| = 3 固定なので流用できない)。台に乗っていない cell は K が自由なので
    wildcard 扱いにし、「rows(x) × cols(x) に他の x' の台 cell が入らない」を判定条件にする。
    """
    pV = J.sum(axis=2)
    mask = pV > SUPPORT_TOL
    f = J.argmax(axis=2)
    na = J.shape[2]
    for x in range(na):
        loc = np.argwhere(mask & (f == x))
        if loc.size == 0:
            continue
        rows, cols = sorted({int(i) for i in loc[:, 0]}), sorted({int(j) for j in loc[:, 1]})
        for i in rows:
            for j in cols:
                if mask[i, j] and f[i, j] != x:
                    return False, f, mask
    return True, f, mask


def markov_defect(J):
    """I(V1;V2|X) = H(V1|X)+H(V2|X)-H(V1,V2|X) >= 0。0 なら J は Markov 点そのもの。"""
    px = J.sum(axis=(0, 1))
    h_v1x = H(J.sum(axis=1)) - H(px)
    h_v2x = H(J.sum(axis=0)) - H(px)
    h_v12x = H(J) - H(px)
    return float(h_v1x + h_v2x - h_v12x)


def describe_opt(J, indent="      "):
    det, mask = determinism(J)
    rect, f, _ = rectangular(J)
    pat = "\n".join(indent + "  " + " ".join(
        (f"{f[i, j]}" if mask[i, j] else ".") for j in range(J.shape[1]))
        for i in range(J.shape[0]))
    return det, rect, pat


# ======================================================================
# 5. 肯定コントロール (a) / (b)
# ======================================================================
def phi(lam, tri):
    I1, I2, I12 = tri
    return lam * I1 + (1 - lam) * I2 - min(lam, 1 - lam) * I12


def control_a(cfg):
    """劣化 BSC 対 (q=0.1, p=0.25) で
       (a1) h_free(lam) が 201 点掃引の全域で時分割包絡 max(lam*C1,(1-lam)*C2) と一致、
       (a2) 同じ instance で h_free - h_markov ~ 0。"""
    print("=== control (a): 劣化 BSC 対 (q=0.10, p=0.25) の既知の答え (L2) ===")
    print(f"  C1 = ln2 - h(q) = {C1_BSC:.10f} ,  C2 = ln2 - h(p) = {C2_BSC:.10f}")
    t0 = time.time()
    # (a1) 201 点を直接最適化 (warm start で連鎖) し、包絡と点ごとに比べる。
    alph = cfg["ctrl_alph"]
    grid = np.linspace(0.0, 1.0, cfg["sweep_pts"])
    seeds, dev, tris = {}, 0.0, [(C1_BSC, 0.0, 0.0), (0.0, C2_BSC, 0.0)]
    for lam in grid:
        F, tri, _, _, _ = h_free(lam, alph, W1_BSC, W2_BSC, cfg["r_sweep"], seeds=seeds)
        tris.append(tri)
        dev = max(dev, abs(F - max(lam * C1_BSC, (1 - lam) * C2_BSC)))
    print(f"  (a1) {cfg['sweep_pts']} 点掃引 (直接最適化) での "
          f"max |h_free(lam) - max(lam*C1,(1-lam)*C2)| = {dev:.3e}")
    # pool 版 (見つけた三つ組は全 lam でアフィン minorant を与える) でも上側を確認
    dev2 = max(max(phi(l, t) for t in tris) - max(l * C1_BSC, (1 - l) * C2_BSC)
               for l in np.linspace(0.0, 1.0, 201))
    print(f"       pool 版 max( max_j phi_j(lam) - 包絡 ) over 201 点 = {dev2:+.3e}")
    ok1 = dev < 1e-9 and dev2 < 1e-9
    # (a2) 同じ instance での h_free - h_markov
    worst = -np.inf
    for lam in cfg["ctrl_lams"]:
        Ff, _, Jf, _, _ = h_free(lam, alph, W1_BSC, W2_BSC, cfg["r_free"])
        Fm, _, _, _ = h_markov(lam, alph, W1_BSC, W2_BSC, cfg["r_mk"], seed_Js=[Jf])
        worst = max(worst, Ff - Fm)
    print(f"  (a2) max over lam of (h_free - h_markov) = {worst:+.3e}  "
          f"(M2 が自明に真な既知ケース)")
    ok2 = worst < 1e-6
    print(f"  -> {'OK' if ok1 and ok2 else 'NG'}  ({time.time() - t0:.1f}s)\n")
    return ok1 and ok2


def control_b(cfg, channels):
    """lam = 0 と lam = 1 でギャップが 0 (コーナーは Markov 点で達成される)。"""
    print("=== control (b): lam = 0 / lam = 1 のコーナーでギャップ 0 ===")
    t0 = time.time()
    worst, worst_at = -np.inf, None
    for (name, W1, W2) in channels:
        for lam in (0.0, 1.0):
            Ff, _, Jf, _, _ = h_free(lam, cfg["alph"], W1, W2, cfg["r_free"])
            Fm, _, _, _ = h_markov(lam, cfg["alph"], W1, W2, cfg["r_mk"], seed_Js=[Jf])
            if Ff - Fm > worst:
                worst, worst_at = Ff - Fm, (name, lam, Ff, Fm)
    n, lam, Ff, Fm = worst_at
    print(f"  最大ギャップ = {worst:+.3e}  at {n}, lam={lam}  "
          f"(h_free={Ff:.10f}, h_markov={Fm:.10f})")
    ok = worst < 1e-6
    print(f"  -> {'OK' if ok else 'NG'}  ({time.time() - t0:.1f}s)\n")
    return ok


# ======================================================================
# 6. チャネル生成
# ======================================================================
def make_channels(cfg):
    """(name, W1, W2) の列。|X| in {3,4}, |Y|,|Z| in {2,3}, Dirichlet 濃度 = 尖り/一様。

    専用の rng を使う (走査までに何回乱数を引いたかに依存させない = instance を
    後から `make_channels` だけで正確に再現できる)。
    """
    rch = np.random.default_rng(20260802_777)
    out = [("CEX-1 (既知の反例, |X|=3)", W1_CEX, W2_CEX),
           ("GLN-ISIT2025-§III-B (|X|=3)", T_Y_GLN, T_Z_GLN)]
    combos = list(itertools.product((3, 4), (2, 3), (2, 3), (0.3, 3.0)))
    k = 0
    while len(out) < cfg["n_ch"]:
        na, nb1, nb2, conc = combos[k % len(combos)]
        rep = k // len(combos)
        W1 = rch.dirichlet(np.full(nb1, conc), size=na)
        W2 = rch.dirichlet(np.full(nb2, conc), size=na)
        out.append((f"rand#{k} |X|={na},|Y|={nb1},|Z|={nb2},conc={conc}"
                    + (f",rep{rep}" if rep else ""), W1, W2))
        k += 1
    return out[: cfg["n_ch"]]


# ======================================================================
# 7. 走査 + hardening
# ======================================================================
# 走査の骨格 (凸包絡 pool):
# h_free も h_markov も lam の **凸** 関数である (どちらも三つ組ごとのアフィン関数
# phi(lam;I1,I2,I12) = lam*I1 + (1-lam)*I2 - min(lam,1-lam)*I12 の上限で、min の折れ点
# lam = 1/2 を除けばアフィン)。ゆえに **ある lam で見つけた三つ組は、全 lam に対する
# 有効な下界 (アフィン minorant) を与える**。そこで各チャネルにつき
#   pool_free : 自由最適化で見つけた三つ組     -> LB_free(lam) = max_j phi_j(lam)
#   pool_mk   : Markov 最適化で見つけた三つ組  -> LB_mk(lam)
# を貯め、細かい lam 格子上で D(lam) = LB_free(lam) - LB_mk(lam) を最大化する lam* を
# 特定してから、そこで h_markov を集中的に叩く。
#
# この構成には 2 つの利点がある:
#   * ギャップの lam 窓は狭い (実測で幅 0.05 程度) ので、粗い格子だけでは取り逃す。
#     pool なら 1 点で見つけた三つ組が窓の外の lam からもギャップを示唆する。
#   * Markov 点は自由な点でもあるので pool_mk の三つ組は h_free の下界でもある。
#     LB_free := max(pool_free, pool_mk) と取ることで、自由側の最適化不足で
#     **見かけ上ギャップが負になる** 現象 (実測あり) が自動的に打ち消される。
def pool_lb(lam, tris):
    return max(phi(lam, t) for t in tris) if tris else -np.inf


def localize(cfg, W1, W2, pf, pm, fine, rounds=4):
    """D(lam) = LB_free - LB_markov を最大化する lam* を求め、**その lam* で** Markov 側の
    hardening を行う。hardening すると lam* が動くので、動かなくなるまで繰り返す
    (でないと「報告する lam*」と「hardening した lam*」がずれ、通っていない値を
    報告することになる)。(gap, lam*, pf, pm, hard) を返す。
    """
    hard = None
    for _ in range(rounds):
        D = np.array([max(pool_lb(l, pf), pool_lb(l, pm)) - pool_lb(l, pm) for l in fine])
        j = int(D.argmax()); lam, d = float(fine[j]), float(D[j])
        if d <= GAP_TOL:
            return d, lam, pf, pm, hard
        _, tf, Jf, alph, _ = h_free(lam, cfg["alph"] + [(5, 5)], W1, W2,
                                    cfg["r_free"] * 3)
        pf.append(tf)
        tris, steps = harden(lam, W1, W2, cfg, Jf, alph)
        pm += tris
        hard = (lam, steps, Jf, alph)
        D2 = np.array([max(pool_lb(l, pf), pool_lb(l, pm)) - pool_lb(l, pm) for l in fine])
        j2 = int(D2.argmax())
        if abs(float(fine[j2]) - lam) < 1e-12:      # lam* が動かなかった = 収束
            return float(D2[j2]), lam, pf, pm, hard
    D = np.array([max(pool_lb(l, pf), pool_lb(l, pm)) - pool_lb(l, pm) for l in fine])
    j = int(D.argmax())
    return float(D[j]), float(fine[j]), pf, pm, hard


def harden(lam, W1, W2, cfg, Jf, alph_used):
    """正のギャップに対する 3 段の増強。(三つ組のリスト, [(ラベル, 値)]) を返す。"""
    na = W1.shape[0]
    n1, n2 = alph_used
    tris, steps = [], []
    # (i) 自由最適点を Markov 化した点をシードに与える
    F1, t1, _, _ = h_markov(lam, [(n1, n2)], W1, W2, cfg["r_mk"], seed_Js=[Jf])
    tris.append(t1); steps.append(("(i) Markov 化シード", F1))
    # (ii) restart を 5 倍
    F2, t2, _, _ = h_markov(lam, cfg["alph"], W1, W2, cfg["r_mk"] * 5, seed_Js=[Jf])
    tris.append(t2); steps.append(("(ii) restart x5", F2))
    # (iii) 補助アルファベットを 1 段大きく
    big = sorted({(n1 + 1, n2 + 1), (max(n1, na) + 1, max(n2, na) + 1), (5, 5)})
    F3, t3, _, _ = h_markov(lam, big, W1, W2, cfg["r_mk"] * 2, seed_Js=[Jf])
    tris.append(t3); steps.append((f"(iii) 補助 {big}", F3))
    return tris, steps


def scan(cfg, channels):
    print("=== 本走査: h_free(lam) vs h_markov(lam) ===")
    print(f"  チャネル {len(channels)} 本 x lam {len(cfg['lams'])} 点 "
          f"x 補助 {cfg['alph']} , restart free={cfg['r_free']} / markov={cfg['r_mk']}")
    print(f"  lam* の特定は凸包絡 pool を {cfg['fine_pts']} 点格子で最大化して行う")
    t0 = time.time()
    fine = np.linspace(0.0, 1.0, cfg["fine_pts"])
    results, side, raw_neg = [], [], 0.0
    for (name, W1, W2) in channels:
        pool_f, pool_m, Jat = [], [], {}
        for lam in cfg["lams"]:
            Ff, trif, Jf, alph, kind = h_free(lam, cfg["alph"], W1, W2, cfg["r_free"])
            Fm, trim, Jm, alphm = h_markov(lam, cfg["alph"], W1, W2, cfg["r_mk"],
                                           seed_Js=[Jf])
            pool_f.append(trif); pool_m.append(trim); Jat[float(lam)] = (Jf, alph)
            raw_neg = min(raw_neg, Ff - Fm)      # 負なら自由側の最適化不足の証拠
            side.append((name, float(lam), Jf, Ff, Ff - Fm, (W1, W2)))
        # 凸包絡でギャップの lam 窓を特定し、その lam* で Markov 側を叩く
        d, lam_s, pool_f, pool_m, hard = localize(cfg, W1, W2, pool_f, pool_m, fine)
        results.append((d, lam_s, name, W1, W2, pool_f, pool_m, hard))
        flag = "  <== ギャップ候補" if d > GAP_TOL else ""
        print(f"  {name:34s} max_lam D(lam) = {d:+.3e}  at lam* = {lam_s:.4f}{flag}")
    print(f"  参考: 素の 1 点比較 h_free - h_markov の最小値 = {raw_neg:+.3e} "
          f"(負なら自由側の最適化不足。pool で打ち消される)")
    print(f"  走査時間 {time.time() - t0:.1f}s\n")
    results.sort(key=lambda r: -r[0])
    return results, side


def report_best(results, cfg):
    d, lam, name, W1, W2, pool_f, pool_m, hard = results[0]
    print("=== 最大ギャップの instance (逐語) ===")
    print(f"  channel   : {name}")
    print(f"  lam*      : {lam:.6f}")
    print(f"  h_free  下界 = {pool_lb(lam, pool_f + pool_m):.12f}")
    print(f"  h_markov 下界 = {pool_lb(lam, pool_m):.12f}")
    print(f"  gap       : {d:+.6e}")
    if d <= GAP_TOL:
        print("  (ギャップなし。以下の逐語出力は省略)\n")
        return
    np.set_printoptions(precision=10, suppress=False, linewidth=120)
    print(f"  W1 = np.{np.array_repr(W1)}")
    print(f"  W2 = np.{np.array_repr(W2)}")
    if hard is not None:
        lam_h, steps, Jf, alph = hard
        if abs(lam_h - lam) > 1e-12:
            print(f"  ⚠ hardening を回した lam = {lam_h:.6f} は最終 lam* と一致していない "
                  f"(以下は lam = {lam_h:.6f} での値)")
        print(f"  h_free を達成した補助 (n1,n2) = {alph}")
        print(f"  最適点 J[v1,v2,x] = np.{np.array_repr(Jf)}")
        det, rect, pat = describe_opt(Jf)
        print(f"  I(V1;V2|X) = {markov_defect(Jf):.6e} , 決定論性 = {det:.6f} , "
              f"rectangular = {rect}")
        print("  f(v1,v2) (. は台外):")
        print(pat)
        print("  hardening 3 段 (すべて通過して初めてギャップとして報告する):")
        for label, F in steps:
            print(f"    {label:24s} h_markov = {F:.12f}")
    print()


def refute_free(cfg, results, top=3):
    """逆向きの反証試行: ギャップが 0 に見えるのが **h_free の探索不足** のせいでないか。

    hardening は h_markov 側を叩いて偽陽性を潰す。こちらは h_free 側を叩いて偽陰性を
    潰す — D(lam) の上位チャネルで、自由側だけ restart 5 倍 + 補助 (5,5)/(6,6) で
    再探索する。**自由側を増やしたら lam* が動くので、動いた先で Markov 側の hardening
    を必ずやり直す** (でないと増強後の値が hardening を通っていない偽陽性になる)。
    更新後の results を返す。
    """
    print("=== 逆向きの反証試行 (h_free 側の増強 — 偽陰性を潰す) ===")
    fine = np.linspace(0.0, 1.0, cfg["fine_pts"])
    out = list(results)
    for k in range(min(top, len(out))):
        d, lam, name, W1, W2, pool_f, pool_m, hard = out[k]
        pf, pm = list(pool_f), list(pool_m)
        for l in sorted({lam, 0.5, min(lam + 0.05, 1.0), max(lam - 0.05, 0.0)}):
            _, tri, _, _, _ = h_free(l, cfg["alph"] + [(5, 5), (6, 6)],
                                     W1, W2, cfg["r_free"] * 5)
            pf.append(tri)
        # 自由側を増やすと lam* が動くので、動いた先で Markov 側の hardening をやり直す
        d2, lam2, pf, pm, hard2 = localize(cfg, W1, W2, pf, pm, fine)
        hard = hard2 if hard2 is not None else hard
        print(f"  {name:34s} 増強前 {d:+.3e} at lam*={lam:.4f}  ->  "
              f"増強後 {d2:+.3e} at lam*={lam2:.4f} (Markov 側 hardening 再実施)")
        out[k] = (d2, lam2, name, W1, W2, pf, pm, hard)
    out.sort(key=lambda r: -r[0])
    print(f"  増強後の最大ギャップ = {out[0][0]:+.3e}\n")
    return out


def report_side(side):
    print("=== 副次出力: h_free 最適点の決定論性 / rectangularity / Markov 欠損 ===")
    print("  (lam in {0,1} は目的関数から補助が 1 本落ちる退化点なので内点 0<lam<1 に限る)")
    dets, rects, mks = [], 0, []
    non_rect, nonmk, bad_impl = [], [], 0
    for (name, lam, J, F, d, _) in side:
        if J is None or not (0.0 < lam < 1.0):
            continue
        det, rect, pat = describe_opt(J)
        dets.append(det)
        mk = markov_defect(J)
        mks.append(mk)
        rects += int(rect)
        if not rect:
            non_rect.append((name, lam, det, pat))
        if mk > 1e-8:
            nonmk.append((mk, name, lam, d, rect, det, pat))
        # 自己検査: 決定論的 (X = f(V1,V2)) かつ Markov (V1 ⊥ V2 | X) ならば
        # p(v1,v2|x) = p(v1|x)p(v2|x) の台は積集合ゆえ f^{-1}(x) は矩形。破れたら
        # rectangular() の実装バグ。
        if det > 1 - 1e-6 and mk < 1e-8 and not rect:
            bad_impl += 1
    n = len(dets)
    print(f"  標本 {n} 点 (チャネル x 内点 lam)")
    print(f"  決定論性 max_x K(x|v1,v2) の台上最小値: "
          f"min={min(dets):.6f} 中央={float(np.median(dets)):.6f} max={max(dets):.6f}")
    print(f"  ほぼ決定論的 (>= 0.999) の割合 = {sum(1 for d in dets if d >= 0.999)}/{n}")
    print(f"  rectangular と判定された割合 = {rects}/{n}")
    print(f"  I(V1;V2|X) (Markov 欠損): max={max(mks):.3e} 中央={float(np.median(mks)):.3e}")
    print(f"    -> 最適点自身が Markov (欠損 < 1e-8) の割合 = "
          f"{sum(1 for m in mks if m < 1e-8)}/{n}")
    print(f"  自己検査 (決定論的 かつ Markov ⟹ rectangular) の違反数 = {bad_impl} "
          f"(> 0 なら rectangular() の実装バグ)")
    for (name, lam, det, pat) in non_rect[:5]:
        print(f"  非 rectangular 例: {name}, lam={lam:.2f}, 決定論性={det:.6f}")
        print("    f(v1,v2) (. は台外):")
        print(pat)
    if nonmk:
        print("  **非 Markov な h_free 最適点** (値は h_markov と一致しているのに"
              " 最適点自身は Markov でない = 最大点集合が Markov 点を含むが尽くさない):")
        for (mk, name, lam, d, rect, det, pat) in sorted(nonmk, reverse=True)[:5]:
            print(f"    {name}, lam={lam:.2f}: I(V1;V2|X)={mk:.4e}, その点でのギャップ"
                  f"={d:+.2e}, 決定論性={det:.4f}, rectangular={rect}")
    print()


# ======================================================================
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--full", action="store_true")
    args = ap.parse_args()

    if args.quick:
        cfg = dict(n_ch=3, lams=np.linspace(0, 1, 5), alph=[(2, 2), (3, 3)],
                   r_free=3, r_mk=8, ctrl_lams=np.linspace(0, 1, 5),
                   ctrl_alph=[(2, 2), (3, 3)], sweep_pts=41, r_sweep=2, fine_pts=401)
    elif args.full:
        cfg = dict(n_ch=24, lams=np.linspace(0, 1, 21),
                   alph=[(2, 2), (3, 3), (4, 4), (5, 5)],
                   r_free=20, r_mk=50, ctrl_lams=np.linspace(0, 1, 21),
                   ctrl_alph=[(2, 2), (3, 3), (4, 4)], sweep_pts=201, r_sweep=8,
                   fine_pts=2001)
    else:
        cfg = dict(n_ch=10, lams=np.linspace(0, 1, 11), alph=[(2, 2), (3, 3), (4, 4)],
                   r_free=8, r_mk=18, ctrl_lams=np.linspace(0, 1, 11),
                   ctrl_alph=[(2, 2), (3, 3), (4, 4)], sweep_pts=201, r_sweep=3,
                   fine_pts=801)

    t_start = time.time()
    print("=== sim <-> Lean def の逐語照合 (bc-marton-union-gap-check.check_sim) ===")
    gap.check_sim()

    ok_c = gradient_check()
    ok_a = control_a(cfg)
    channels = make_channels(cfg)
    ok_b = control_b(cfg, channels)
    if not (ok_a and ok_b and ok_c):
        print("!! 肯定コントロールが落ちた。本走査は行わない (合わせにいかない)。")
        print(f"   control (a)={ok_a} (b)={ok_b} (c)={ok_c}")
        return

    results, side = scan(cfg, channels)
    results = refute_free(cfg, results)
    report_best(results, cfg)
    report_side(side)

    d = results[0][0]
    n_gap = sum(1 for r in results if r[0] > GAP_TOL)
    print("=== 判定 ===")
    if d > GAP_TOL:
        print(f"  M2 に **反例が出た**: 最大ギャップ h_free - h_markov = {d:+.6e} "
              f"> {GAP_TOL:.0e}")
        print(f"  ギャップを示したチャネル = {n_gap}/{len(results)}")
        print("  (hardening 3 段をすべて通過した値。上の instance を逐語で再検査すること)")
        print("  ⚠ 射程: これは **我々の 2 補助変数 def の上の M2** の反例であって、")
        print("     論文の Conjecture 2 の反例ではない (冒頭 docstring の射程節を参照)。")
    else:
        print(f"  M2 の **反例は出なかった**: 全走査点で h_free - h_markov <= {max(d, 0.0):+.3e}")
        print("  これは証拠であって証明ではない (sup の下界どうしの比較)。")
    print(f"\n合計実行時間 {time.time() - t_start:.1f}s")


if __name__ == "__main__":
    main()
