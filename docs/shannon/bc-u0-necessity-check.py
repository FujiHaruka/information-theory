"""共通補助変数 U0 を持たない 2 補助変数 Marton union が、**時分割領域より真に強く
なりうるか**を数値判定する probe (attack `u0-necessity-quantified`)。

対応する親 docs の主張
----------------------
`bc-facts.md` §定義照合と数値 probe の判定 (L2) の V5 行の副産物:

    「201 点掃引の全域で S(lam) が 2 つの退化コーナー (C1,0) / (0,C2) の上包絡
      max(lam*C1, (1-lam)*C2) と一致した (最大偏差 +3.331e-16) ⟹ この劣化 BSC 対では
      2 補助変数 Marton union の閉凸包は時分割領域そのものに潰れる」

同じ行が **|X| = 2 ゆえ F6 (Nair-Wang-Geng: binary input BC では randomized time-division が
Marton の sum rate を達成する) と整合しており、非自明になるのは |X| >= 3 から** と射程を
限定している。本 probe はその |X| >= 3 を叩き、**潰れないチャネルを 1 つ挙げる**ことを目的と
する。挙がれば「共通補助 U0 が無い 2 補助変数 Marton union でも時分割より真に強い」の実例に
なる。

判定量
------
    S(lam)   := sup over (pV, K) of [ lam*I1 + (1-lam)*I2 - min(lam,1-lam)*I12 ]
                (= martonRegionUnion の閉凸包の theta=(lam,1-lam) 方向の support 値。
                 四辺形の閉形式は L2 の V5 行が確定させたもの)
    env(lam) := max(lam*C1, (1-lam)*C2)
                (= 時分割領域 {(R1,R2) : R1/C1 + R2/C2 <= 1} の同じ方向の support 値)
    C1 := max_p I(X;Y1) ,  C2 := max_p I(X;Y2)

S >= env は常に成り立つ (V1=X / V2=trivial の退化点とその裏返しが env の 2 頂点を与える)。
判定するのは **どこかの lam で狭義不等号が立つか**。

誤差の向きの規律 (この節に固有 — L5 とは逆で、こちらは符号保証がある)
---------------------------------------------------------------------
* S(lam) は局所最適化で計算するので、返るのは **sup の下界** `S_LB`。ただし各値は
  実際に評価した明示 witness (pV,K) に裏づけられているので、`S_LB <= S` は確実。
* env 側の C1 / C2 は **凹最適化**なので大域最大が取れる。本 probe は Blahut-Arimoto を
  使い、さらに BA が副産物として与える **証明つき上界** C_UB := max_x D(W_x || q) を採る
  (C = min_q max_x D(W_x || q) ゆえ任意の q で上界。q は BA の出力分布)。
* ⟹ 判定量を `S_LB(lam) - max(lam*C1_UB, (1-lam)*C2_UB) > 0` と組めば、これは
  **明示 witness と証明つき上界に裏づけられた確実な判定** になる (浮動小数点の丸めを除く)。
  L5 の `h_free - h_markov` は Markov 側に上界が無く「反証を潰した後に残った証拠」に
  すぎなかったが、**本 probe の正の判定はそれより強い**。

  ⚠ **逆向き (ギャップが見つからない = 潰れる) は証明ではない**。S 側は下界しか無いので、
  探索不足と真の一致を区別できない。「N 本の探索でギャップが出なかった」までしか言えない。

**最大ギャップの instance については判定が閉形式まで落ちる** (最適化に依存しない)。
Blackwell |X|=3 で X~U{0,1,2} , V1 := 1{X=2} , V2 := 1{X!=0} と取ると
I1 = I2 = h(1/3) , I12 = 2h(1/3) - ln3 ゆえ I1+I2-I12 = ln3 で S(1/2) >= (1/2)ln3。
一方 |Y1| = |Y2| = 2 ゆえ初等的に C1, C2 <= ln2 で env(1/2) <= (1/2)ln2。
⟹ ギャップ >= (1/2)(ln3 - ln2) = 0.2027325541... > 0 が手計算で出る。
数値部分は witness の三つ組の再計算だけ (`blackwell_closed_form_certificate`)。

⚠ C1 / C2 を **過小評価すると偽陽性**が出る向きなので、
  (1) BA の収束判定は上下界のギャップ `< 1e-14`、(2) 多点初期値で同一値への着地を確認、
  (3) 閉形式が既知のチャネル 4 本と照合、(4) 独立系統 (Nelder-Mead 直接最大化) と照合、
  の 4 段を踏む。判定に使うのは常に **C_UB** (下界ではない)。

肯定コントロール
----------------
  (a) L2 の劣化 BSC 対 (q=0.1, p=0.25) で潰れることの再現 (max |S - env| ~ 1e-15)。
  (b) lam in {0,1} の退化コーナーで S(0) = C2 / S(1) = C1。
  (c) 解析勾配 vs 中心差分 (`bc-markovity-conjecture-check.gradient_check` を再実行)、
      および四辺形 support function の閉形式 vs LP
      (`bc-marton-convexhull-check.support_closed_form_check` を再実行)。
  (d) **検出器の健全性** — ギャップが構成から確実に存在する |X|=4 の直積チャネル
      (Y1 = x1, Y2 = x2) でギャップ (1/2)*ln2 が出ること。
  (e) **構造的な負のコントロール** — 両受信者が X の同一の 2 値関数を見るチャネルでは
      ギャップがちょうど 0 になること (潰れる側も検出できることの確認)。
  (f) **一般結合カーネルを尽くしていることの確認** — 走査は周辺対 (W1,W2) をパラメータに
      するが、これは `Y ⊥ Z | X` の仮定ではない (facts L1 の V2 行の落とし穴)。周辺が同じで
      結合の違う T(y,z|x) を 4 通り作り、5 変数同時法則 (V1,V2,X,Y1,Y2) を組む別コード経路で
      三つ組が一致することを確かめる。判定量は S 側も env 側も周辺だけで決まるので、
      (W1,W2) の走査で一般 BC を尽くしている。

実行方法
--------
    python3 docs/shannon/bc-u0-necessity-check.py            # 既定 (約 3 分)
    python3 docs/shannon/bc-u0-necessity-check.py --quick    # 縮小版 (約 25 秒)
    python3 docs/shannon/bc-u0-necessity-check.py --full     # 拡大版 (時間無制限)

numpy / scipy が要る。乱数種は固定で、再実行で同じ値が出る。既存の
`bc-marton-union-gap-check.py` / `bc-marton-convexhull-check.py` /
`bc-markovity-conjecture-check.py` / `bc_probe.py` は **編集も再実装もしない** —
`check_sim` / `marton_infos` / `h_free` / `gradient_check` /
`support_closed_form_check` / `H` / `hb` / `bsc` / `W1_CEX` / `T_Y_GLN` は importlib で
読み込んでそのまま使う (ファイル名にハイフンがあり通常の import が効かない)。

sim <-> Lean def 照合
---------------------
`bc-marton-union-gap-check.check_sim()` を冒頭で **そのまま実行** する (L2 / L5 と同じ手順、
再実装しない)。目的関数の Lean def との対応は同ファイルの docstring が SoT:

  Marton/Setup.lean:244/252/262   martonInfo1 / martonInfo2 / martonInfoV1V2
  Marton/Basic.lean:40-46         InMartonRegion (四辺形の 3 制約)
  MartonUnion.lean:71-77          martonRegionUnion = closure (union over pV K)
すべて nat (自然対数)。

射程の限定 (何を言っていて何を言っていないか)
----------------------------------------------
* 言っている: 「2 補助変数 (U0 無し) Marton union の閉凸包 = 時分割領域」という L2 の観測は
  **|X| = 2 に固有**であり、|X| = 3 では反例がある。したがって U0 の欠落が領域を時分割まで
  潰すという説明は一般には成り立たない。
* 言っていない: U0 が不要だとは言っていない。L2 の劣化 BSC 対では U0 無しの領域は本当に
  時分割へ潰れ、容量領域 (superposition) には遠く及ばない。⟹ U0 の効き方は **チャネル依存**
  であり、本 probe はその両端を押さえただけ。
* 比較対象は **素の時分割 (TDMA) 三角形** であって、randomized time-division でも
  superposition 領域でもない。F6 は sum rate について randomized time-division を述べており、
  本 probe の env とは別の対象。
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


mk = _load("bc_markovity_conjecture_check", HERE / "bc-markovity-conjecture-check.py")
cvx = _load("bc_marton_convexhull_check", HERE / "bc-marton-convexhull-check.py")
gap = mk.gap                                     # bc-marton-union-gap-check.py
H, hb, bsc = gap.H, gap.hb, gap.bsc
marton_infos = gap.marton_infos
h_free = mk.h_free                               # S(lam) の下界を返す既存の最適化器

GAP_TOL = 1e-9        # これを超える S_LB - env_UB だけをギャップとして報告する
BA_TOL = 1e-14        # Blahut-Arimoto の上下界ギャップの停止条件


# ======================================================================
# 0. 走査対象のチャネル (ギャップを出したものは逐語ハードコード)
# ======================================================================
# 構造候補 (b): X = {A,B,C} で Y1 が {A,B} vs {C} を、Y2 が {A} vs {B,C} を見分ける。
# = Blackwell チャネルの周辺。|X| = 3 の 2 値分割は本質的にこの 1 通りしかない
# (2 つの分割が一致すれば下の退化コントロールになる)。決定論的だが、下で雑音を
# 混ぜた版も走らせて knife-edge でないことを確認する。
BW1 = np.array([[1.0, 0.0], [1.0, 0.0], [0.0, 1.0]])
BW2 = np.array([[1.0, 0.0], [0.0, 1.0], [0.0, 1.0]])

# 本 probe の走査でギャップを出したランダムチャネル。乱数種に依存させると失われるので
# **逐語でハードコードして常に走査対象に含める** (L5 の W1_CEX / W2_CEX と同じ扱い)。
W1_RGAP = np.array([
    [9.9996111066e-01, 3.8889341473e-05],
    [1.3059533679e-05, 9.9998694047e-01],
    [7.7312183991e-01, 2.2687816009e-01],
])
W2_RGAP = np.array([
    [9.7089590915e-01, 2.8072119514e-02, 1.0319713366e-03],
    [2.2753960015e-02, 1.2368931184e-03, 9.7600914687e-01],
    [5.9063298977e-07, 6.9735923082e-08, 9.9999933963e-01],
])
W1_RGAP /= W1_RGAP.sum(axis=1, keepdims=True)
W2_RGAP /= W2_RGAP.sum(axis=1, keepdims=True)

# control (d): 検出器の健全性。X = (x1,x2) の直積で Y1 = x1, Y2 = x2。
# V1 = x1, V2 = x2 と取れば I1 = I2 = ln2, I12 = 0 なので lam=1/2 で
# S >= ln2 に対し env = (1/2)ln2 ⟹ ギャップ (1/2)ln2 が構成から確実に存在する。
PROD1 = np.array([[1., 0.], [1., 0.], [0., 1.], [0., 1.]])
PROD2 = np.array([[1., 0.], [0., 1.], [1., 0.], [0., 1.]])


def mix_uniform(W, eps):
    return (1 - eps) * W + eps / W.shape[1]


def structured_channels():
    """名前つきの構造候補。(name, W1, W2, note, role) の列。

    role は判定での扱いを決める: `cand` = 主張の候補 (|X|=3)、`ctrl-*` = コントロール。
    **コントロールは主張の witness に採らない** (|X|=4 の直積は検出器の健全性のための
    自明例なので、これを「見つけたチャネル」として報告してはならない)。
    """
    return [
        ("Blackwell |X|=3 (構造候補 b)", BW1, BW2, "決定論的、2 値分割が相補的", "cand"),
        ("Blackwell + 雑音 eps=0.02", mix_uniform(BW1, 0.02), mix_uniform(BW2, 0.02),
         "決定論性が knife-edge でないことの確認", "cand"),
        ("Blackwell + 雑音 eps=0.10", mix_uniform(BW1, 0.10), mix_uniform(BW2, 0.10),
         "", "cand"),
        ("Blackwell + 雑音 eps=0.30", mix_uniform(BW1, 0.30), mix_uniform(BW2, 0.30),
         "", "cand"),
        ("CEX-1 (L5 の M2 反例, |X|=3)", mk.W1_CEX, mk.W2_CEX, "既に非自明な構造を持つ",
         "cand"),
        ("GLN-ISIT2025-§III-B (|X|=3)", mk.T_Y_GLN, mk.T_Z_GLN, "論文の非矩形局所最大点の例",
         "cand"),
        ("rand-GAP 逐語 (|X|=3,|Y|=2,|Z|=3)", W1_RGAP, W2_RGAP, "走査で出たギャップの固定版",
         "cand"),
        ("同一分割 |X|=3 [control e]", BW1, BW1, "両受信者が同じ 2 値関数を見る = 潰れる側",
         "ctrl-e"),
        ("劣化 BSC 対 q=0.1,p=0.25 [control a]", bsc(0.10), bsc(0.25),
         "L2 の既知の答え = 潰れる", "ctrl-a"),
        ("直積 |X|=4 [control d]", PROD1, PROD2, "ギャップが構成から確実に存在する",
         "ctrl-d"),
    ]


def random_channels(n, rng_seed=20260802_707):
    """|X|=3, |Y|,|Z| in {2,3}, Dirichlet 濃度 0.1/0.3/1.0/3.0。専用 rng で再現可能。"""
    rch = np.random.default_rng(rng_seed)
    combos = list(itertools.product((2, 3), (2, 3), (0.1, 0.3, 1.0, 3.0)))
    out = []
    for k in range(n):
        nb1, nb2, conc = combos[k % len(combos)]
        rep = k // len(combos)
        W1 = rch.dirichlet(np.full(nb1, conc), size=3)
        W2 = rch.dirichlet(np.full(nb2, conc), size=3)
        out.append((f"rand#{k} |X|=3,|Y|={nb1},|Z|={nb2},c={conc}"
                    + (f",rep{rep}" if rep else ""), W1, W2, "", "cand"))
    return out


# ======================================================================
# 1. 単一チャネル容量 — Blahut-Arimoto (下界 + 証明つき上界)
# ======================================================================
def dkl_rows(W, q):
    """D(W_x || q) を x ごとに (nat)。"""
    out = np.zeros(W.shape[0])
    for x in range(W.shape[0]):
        w = W[x]
        m = w > 0
        out[x] = float((w[m] * (np.log(w[m]) - np.log(np.maximum(q[m], 1e-300)))).sum())
    return out


def blahut_arimoto(W, p0=None, iters=200000, tol=BA_TOL):
    """(下界 I(p;W), 上界 max_x D(W_x||q), p, 反復数) を返す。

    上界は C = min_q max_x D(W_x || q) から来る **任意の q で妥当な上界**なので、
    収束が不十分でも上界であることは崩れない (判定に使うのはこちら)。
    """
    na = W.shape[0]
    p = np.full(na, 1.0 / na) if p0 is None else np.asarray(p0, float) / np.sum(p0)
    it = 0
    for it in range(iters):
        q = p @ W
        d = dkl_rows(W, q)
        if float(d.max()) - float(p @ d) < tol:
            break
        lp = np.log(np.maximum(p, 1e-300)) + d
        lp -= lp.max()
        p = np.exp(lp)
        p /= p.sum()
    q = p @ W
    d = dkl_rows(W, q)
    return float(p @ d), float(d.max()), p, it


def capacity(W, restarts=8, seed=0):
    """多点初期値で BA を回し (最良下界, 最良上界, 達成 p) を返す。"""
    rng = np.random.default_rng(seed)
    na = W.shape[0]
    starts = [np.full(na, 1.0 / na)] + [rng.dirichlet(np.full(na, 1.0)) for _ in range(restarts)]
    lo_best, hi_best, p_best = -np.inf, np.inf, None
    for p0 in starts:
        lo, hi, p, _ = blahut_arimoto(W, p0)
        if lo > lo_best:
            lo_best, p_best = lo, p
        hi_best = min(hi_best, hi)
    return lo_best, hi_best, p_best


def _mi(p, W):
    J = p[:, None] * W
    return H(p) + H(J.sum(axis=0)) - H(J)


def capacity_direct(W, restarts=25, seed=1):
    """softmax + Nelder-Mead による直接最大化 (BA とは独立系統。照合専用)。"""
    rng = np.random.default_rng(seed)
    na = W.shape[0]

    def neg(t):
        e = np.exp(t - t.max())
        return -_mi(e / e.sum(), W)

    best = -np.inf
    for _ in range(restarts):
        res = minimize(neg, rng.normal(0, 2.0, na), method="Nelder-Mead",
                       options={"maxiter": 20000, "xatol": 1e-13, "fatol": 1e-15})
        best = max(best, -float(res.fun))
    return best


def capacity_check():
    """C1 / C2 の過小評価を潰す 4 段 (閉形式 / 上下界 / 多点 / 独立系統)。"""
    print("=== control: 単一チャネル容量 C = max_p I(X;Y) の検証 (env 側の過小評価を潰す) ===")
    cases = [
        ("BSC(0.10)", bsc(0.10), float(np.log(2) - hb(0.10))),
        ("BSC(0.25)", bsc(0.25), float(np.log(2) - hb(0.25))),
        ("Blackwell 側 1 (決定論的 3->2)", BW1, float(np.log(2))),
        ("Blackwell 側 2 (決定論的 3->2)", BW2, float(np.log(2))),
        ("対称 3 元 (0.8,0.1,0.1)", np.array([[.8, .1, .1], [.1, .8, .1], [.1, .1, .8]]),
         float(np.log(3) - H([.8, .1, .1]))),
    ]
    ok = True
    worst_cf, worst_br, worst_dir = 0.0, 0.0, 0.0
    for name, W, closed in cases:
        lo, hi, _ = capacity(W)
        direct = capacity_direct(W)
        worst_cf = max(worst_cf, abs(lo - closed))
        worst_br = max(worst_br, hi - lo)
        worst_dir = max(worst_dir, abs(direct - lo))
        print(f"  {name:32s} BA下界={lo:.12f} 上界={hi:.12f} 閉形式={closed:.12f} "
              f"直接={direct:.12f}")
    # 閉形式が無いチャネルでも上下界ブラケットと独立系統は効く
    for name, W1, W2, _n, _r in structured_channels():
        for W in (W1, W2):
            lo, hi, _ = capacity(W)
            worst_br = max(worst_br, hi - lo)
            worst_dir = max(worst_dir, abs(capacity_direct(W) - lo))
    print(f"  閉形式との最大差            = {worst_cf:.3e}")
    print(f"  BA 上下界ブラケットの最大幅 = {worst_br:.3e}  (判定には上界のみ使う)")
    print(f"  独立系統 (Nelder-Mead) との最大差 = {worst_dir:.3e}")
    ok = worst_cf < 1e-10 and worst_br < 1e-11 and worst_dir < 1e-8
    print(f"  -> {'OK' if ok else 'NG'}\n")
    return ok


def _nw_coupling(a, b):
    """周辺 a, b をちょうど持つ結合 (北西隅ルール)。積結合とは別の結合を作るために使う。"""
    a, b = np.asarray(a, float).copy(), np.asarray(b, float).copy()
    M = np.zeros((a.size, b.size))
    i = j = 0
    while i < a.size and j < b.size:
        t = min(a[i], b[j])
        M[i, j] = t
        a[i] -= t
        b[j] -= t
        if a[i] <= b[j] and i < a.size:
            i += 1
        else:
            j += 1
    return M


def joint_kernel_check(trials=200, seed=90210):
    """一般 BC `T(y,z|x)` を周辺対 `(W1,W2)` で尽くせることの検査 (facts L1 V2 行の落とし穴)。

    走査は `(W1, W2)` の対をパラメータとして回すが、これは `Y ⊥ Z | X` を仮定しているのでは
    **ない**。判定量 (S と env) が周辺だけで決まることを、**結合カーネルから 5 変数同時法則
    `(V1,V2,X,Y1,Y2)` を組む別コード経路**で確認する: 周辺が同じで結合の違う `T` を 4 通り
    (元の T / 積 W1(x)xW2(x) / 北西隅結合 2 通り) 作り、三つ組が一致することを見る。
    一致すれば「結合の自由度は目的値に効かない」= (W1,W2) の走査で一般 BC を尽くしている。
    """
    print("=== control: 一般結合カーネル T(y,z|x) が周辺対 (W1,W2) で尽くされることの検査 ===")
    rng = np.random.default_rng(seed)
    worst = 0.0
    for _ in range(trials):
        na, nb1, nb2 = 3, int(rng.integers(2, 4)), int(rng.integers(2, 4))
        n1, n2 = int(rng.integers(2, 4)), int(rng.integers(2, 4))
        T = rng.dirichlet(np.full(nb1 * nb2, 0.7), size=na).reshape(na, nb1, nb2)
        W1, W2 = T.sum(axis=2), T.sum(axis=1)
        pV = rng.dirichlet(np.full(n1 * n2, 0.8)).reshape(n1, n2)
        K = rng.dirichlet(np.full(na, 0.8), size=n1 * n2).reshape(n1, n2, na)
        # 周辺が同じで結合の違う 4 通り
        T_prod = W1[:, :, None] * W2[:, None, :]
        T_nw = np.stack([_nw_coupling(W1[x], W2[x]) for x in range(na)])
        T_nwr = np.stack([_nw_coupling(W1[x], W2[x][::-1])[:, ::-1] for x in range(na)])
        assert max(np.abs(TT.sum(axis=2) - W1).max() for TT in (T_prod, T_nw, T_nwr)) < 1e-14
        assert max(np.abs(TT.sum(axis=1) - W2).max() for TT in (T_prod, T_nw, T_nwr)) < 1e-14
        base = marton_infos(pV, K, W1, W2)
        for TT in (T, T_prod, T_nw, T_nwr):
            # 5 変数同時法則 P[v1,v2,x,y1,y2] (Marton/Setup.lean:57 の martonJointDistribution)
            P = pV[:, :, None, None, None] * K[:, :, :, None, None] * TT[None, None, :, :, :]
            pV1 = P.sum(axis=(1, 2, 3, 4))
            pV2 = P.sum(axis=(0, 2, 3, 4))
            pV1V2 = P.sum(axis=(2, 3, 4))
            pV1Y1 = P.sum(axis=(1, 2, 4))
            pV2Y2 = P.sum(axis=(0, 2, 3))
            tri = (H(pV1) + H(pV1Y1.sum(axis=0)) - H(pV1Y1),
                   H(pV2) + H(pV2Y2.sum(axis=0)) - H(pV2Y2),
                   H(pV1) + H(pV2) - H(pV1V2))
            worst = max(worst, max(abs(a - b) for a, b in zip(tri, base)))
    print(f"  結合を変えた 4 通り x {trials} 試行での三つ組の最大差 = {worst:.3e}")
    print("  (I(V1;Y1) / I(V2;Y2) は V1-X-Y1 / V2-X-Y2 の周辺で、I(V1;V2) は (V1,V2) の周辺で")
    print("   決まるので、結合カーネルの自由度は判定量に効かない。env 側の C1 / C2 も同様。)")
    ok = worst < 1e-12
    print(f"  -> {'OK' if ok else 'NG'}\n")
    return ok


def timesharing_support_check():
    """時分割領域 {R1/C1 + R2/C2 <= 1} の support 値が max(lam*C1,(1-lam)*C2) であることの確認。"""
    print("=== control: 時分割領域の support function の形 ===")
    print("  領域は (0,0),(C1,0),(0,C2) の三角形の下方閉包。lam in [0,1] で theta >= 0 ゆえ")
    print("  sup は頂点で達成され max(0, lam*C1, (1-lam)*C2) = max(lam*C1,(1-lam)*C2)。")
    rng = np.random.default_rng(4242)
    worst = 0.0
    for _ in range(2000):
        c1, c2 = rng.uniform(1e-3, 2.0, 2)
        lam = float(rng.uniform(0, 1))
        # 三角形上の直接最大化 (R1 = a*C1, R2 = (1-a)*C2, a in [0,1] の端点評価)
        grid = np.linspace(0, 1, 100001)
        direct = float(np.max(lam * grid * c1 + (1 - lam) * (1 - grid) * c2))
        worst = max(worst, abs(direct - max(lam * c1, (1 - lam) * c2)))
        if worst > 1e-9:
            break
    print(f"  閉形式 vs 三角形上の直接最大化: 最大差 = {worst:.3e}")
    ok = worst < 1e-9
    print(f"  -> {'OK' if ok else 'NG'}\n")
    return ok


# ======================================================================
# 2. S(lam) の下界 (pool) と判定
# ======================================================================
def phi(lam, tri):
    """三つ組 (I1,I2,I12) が与える S の下界 (lam の凸区分線形関数)。L2 の V5 行の閉形式。"""
    I1, I2, I12 = tri
    return lam * I1 + (1 - lam) * I2 - min(lam, 1 - lam) * I12


def pool_lb(lam, tris):
    return max(phi(lam, t) for t in tris) if tris else -np.inf


def scan_channel(W1, W2, cfg, seed):
    """1 チャネルの判定。(gap, lam*, C1, C2, pool, best_J_at_lamstar) を返す。

    lam 格子で h_free を回して三つ組を pool に貯める。**ある lam で見つけた三つ組は
    全 lam に対する S のアフィン minorant** なので、細かい格子上で
    S_LB(lam) - env_UB(lam) を最大化できる (L2 / L5 と同じ pool の使い方)。
    """
    mk.rng = np.random.default_rng(seed)          # 再現性: チャネルごとに固定
    pool, Jat, seeds = [], {}, {}
    for lam in cfg["lams"]:
        F, tri, J, alph, kind = h_free(lam, cfg["alph"], W1, W2, cfg["r_free"], seeds=seeds)
        pool.append(tri)
        Jat[float(lam)] = (J, alph)
    (c1lo, c1hi, _), (c2lo, c2hi, _) = capacity(W1), capacity(W2)
    fine = np.linspace(0.0, 1.0, cfg["fine_pts"])
    S = np.array([pool_lb(l, pool) for l in fine])
    E = np.maximum(fine * c1hi, (1 - fine) * c2hi)
    d = S - E
    j = int(d.argmax())
    lam_s = float(fine[j])
    # lam* に最も近い格子点の J を witness として持ち帰る
    key = min(Jat, key=lambda l: abs(l - lam_s))
    return float(d[j]), lam_s, (c1lo, c1hi), (c2lo, c2hi), pool, Jat[key], key


# ======================================================================
# 3. 肯定コントロール (a) / (b) / (c)
# ======================================================================
def control_a(cfg):
    """L2 の劣化 BSC 対で S(lam) が時分割包絡に潰れることの再現 (既知の答えの再現)。"""
    print("=== control (a): 劣化 BSC 対 (q=0.10, p=0.25) で潰れることの再現 [L2 の副産物] ===")
    W1, W2 = bsc(0.10), bsc(0.25)
    c1lo, c1hi, _ = capacity(W1)
    c2lo, c2hi, _ = capacity(W2)
    print(f"  C1 = {c1lo:.10f} (閉形式 ln2-h(0.10) = {np.log(2) - hb(0.10):.10f})")
    print(f"  C2 = {c2lo:.10f} (閉形式 ln2-h(0.25) = {np.log(2) - hb(0.25):.10f})")
    t0 = time.time()
    mk.rng = np.random.default_rng(31337)
    seeds, dev, pool = {}, 0.0, []
    for lam in np.linspace(0.0, 1.0, cfg["sweep_pts"]):
        F, tri, _, _, _ = h_free(lam, cfg["ctrl_alph"], W1, W2, cfg["r_sweep"], seeds=seeds)
        pool.append(tri)
        dev = max(dev, abs(F - max(lam * c1lo, (1 - lam) * c2lo)))
    fine = np.linspace(0.0, 1.0, 801)
    dev2 = float(np.max([pool_lb(l, pool) - max(l * c1hi, (1 - l) * c2hi) for l in fine]))
    print(f"  {cfg['sweep_pts']} 点掃引 max |S(lam) - max(lam*C1,(1-lam)*C2)| = {dev:.3e}")
    print(f"  pool 版 max( S_LB(lam) - env_UB(lam) ) over 801 点 = {dev2:+.3e}")
    ok = dev < 1e-9 and dev2 < GAP_TOL
    print(f"  -> {'OK' if ok else 'NG'}  ({time.time() - t0:.1f}s)\n")
    return ok


def control_b(cfg, channels):
    """lam in {0,1} の退化コーナーで S(0) = C2 / S(1) = C1。"""
    print("=== control (b): lam = 0 / lam = 1 の退化コーナー ===")
    t0 = time.time()
    worst, at = 0.0, None
    for (name, W1, W2, _n, _r) in channels:
        mk.rng = np.random.default_rng(4711)
        c1 = capacity(W1)[0]
        c2 = capacity(W2)[0]
        for lam, target in ((0.0, c2), (1.0, c1)):
            F, _, _, _, _ = h_free(lam, cfg["alph"], W1, W2, cfg["r_free"])
            if abs(F - target) > worst:
                worst, at = abs(F - target), (name, lam, F, target)
        if worst > 1e-6:
            break
    print(f"  max |S(lam) - C| = {worst:.3e}  (最悪点: {at[0]}, lam={at[1]}, "
          f"S={at[2]:.10f}, C={at[3]:.10f})")
    ok = worst < 1e-8
    print(f"  -> {'OK' if ok else 'NG'}  ({time.time() - t0:.1f}s)\n")
    return ok


def control_c():
    """解析勾配と四辺形 support function の閉形式を既存 probe の検査で確認 (再実装しない)。"""
    print("=== control (c-1): 解析勾配 vs 中心差分 "
          "[bc-markovity-conjecture-check.gradient_check を再実行] ===")
    ok1 = mk.gradient_check()
    print("=== control (c-2): 四辺形 support function 閉形式 vs LP "
          "[bc-marton-convexhull-check.support_closed_form_check を再実行] ===")
    cvx.support_closed_form_check()
    return ok1


# ======================================================================
# 4. hardening — 正の判定に対する反証義務
# ======================================================================
def det_bc_support(W1, W2, lam, restarts=30, seed=2):
    """決定論的 BC の容量領域 (Marton/Pinsker 形)
       union over p(x) of {R1<=H(Y1), R2<=H(Y2), R1+R2<=H(Y1,Y2)} の support 値。

    W1 / W2 が決定論的なときだけ意味を持つ **独立な解析ルート**。h_free の最適化器を
    一切使わずに S(lam) を再計算するので、最適化器の人工物でないことの確認になる。
    """
    rng = np.random.default_rng(seed)
    na, nb1, nb2 = W1.shape[0], W1.shape[1], W2.shape[1]
    f1, f2 = W1.argmax(axis=1), W2.argmax(axis=1)

    def val(t):
        p = np.exp(t - t.max())
        p /= p.sum()
        a = H(np.bincount(f1, weights=p, minlength=nb1))
        b = H(np.bincount(f2, weights=p, minlength=nb2))
        c = H(np.bincount(f1 * nb2 + f2, weights=p, minlength=nb1 * nb2))
        return max(lam * a + (1 - lam) * (c - a), lam * (c - b) + (1 - lam) * b)

    best = -np.inf
    for _ in range(restarts):
        res = minimize(lambda t: -val(t), rng.normal(0, 2.0, na), method="Nelder-Mead",
                       options={"maxiter": 20000, "xatol": 1e-13, "fatol": 1e-15})
        best = max(best, -float(res.fun))
    return best


def blackwell_closed_form_certificate():
    """Blackwell |X|=3 のギャップを **最適化を一切使わない閉形式**で確立する。

    witness: X ~ Uniform{0,1,2} , V1 := 1{X=2} , V2 := 1{X!=0} (どちらも X の決定論的関数)。
      Y1 = 1{X=2} = V1 , Y2 = 1{X!=0} = V2 なので
        I1  = I(V1;Y1) = H(V1) = h(1/3)
        I2  = I(V2;Y2) = H(V2) = h(1/3)
        I12 = I(V1;V2) = H(V1) + H(V2) - H(V1,V2) = 2h(1/3) - ln3
              ((V1,V2) は X と 1 対 1 ゆえ H(V1,V2) = ln3)
      ⟹ I1 + I2 - I12 = ln3 なので S(1/2) >= (1/2)*ln3。
    env: |Y1| = |Y2| = 2 ゆえ **初等的に** C1, C2 <= ln2 (最適化不要の上界)。
      ⟹ env(1/2) = max((1/2)C1, (1/2)C2) <= (1/2)*ln2。
    ⟹ S(1/2) - env(1/2) >= (1/2)*(ln3 - ln2) = 0.2027325541... > 0。

    上界側が「C <= ln|Y|」という初等的な事実なので、この判定は Blahut-Arimoto にも
    局所最適化にも依存しない。数値部分は witness の三つ組の再計算だけ。
    """
    print("=== Blackwell |X|=3 の閉形式による証明 (最適化に依存しない判定) ===")
    h13 = float(-(1 / 3) * np.log(1 / 3) - (2 / 3) * np.log(2 / 3))
    I1_cf, I2_cf = h13, h13
    I12_cf = 2 * h13 - float(np.log(3))
    # witness を実際に組んで、独立実装 (bc-marton-union-gap-check.marton_infos) で再計算
    pV = np.zeros((2, 2))
    K = np.zeros((2, 2, 3))
    for x, (v1, v2) in enumerate([(0, 0), (0, 1), (1, 1)]):   # X=0,1,2
        pV[v1, v2] += 1 / 3
        K[v1, v2, x] = 1.0
    I1, I2, I12 = marton_infos(pV, K, BW1, BW2)
    print(f"  witness: X~U{{0,1,2}} , V1=1{{X=2}} , V2=1{{X!=0}}")
    print(f"    I1 : 閉形式 h(1/3)      = {I1_cf:.12f}  数値 = {I1:.12f}  差={I1 - I1_cf:+.2e}")
    print(f"    I2 : 閉形式 h(1/3)      = {I2_cf:.12f}  数値 = {I2:.12f}  差={I2 - I2_cf:+.2e}")
    print(f"    I12: 閉形式 2h(1/3)-ln3 = {I12_cf:.12f}  数値 = {I12:.12f}  差={I12 - I12_cf:+.2e}")
    print(f"    I1+I2-I12 : 閉形式 ln3  = {np.log(3):.12f}  数値 = {I1 + I2 - I12:.12f}")
    lhs = 0.5 * (I1 + I2 - I12)
    rhs = 0.5 * float(np.log(2))
    print(f"  S(1/2) >= (1/2)*ln3 = {lhs:.12f}")
    print(f"  env(1/2) <= (1/2)*ln2 = {rhs:.12f}   (初等的な上界 C <= ln|Y| = ln2 のみを使用)")
    print(f"  ⟹ ギャップ >= (1/2)*(ln3-ln2) = {lhs - rhs:.12f}")
    ok = (abs(I1 - I1_cf) < 1e-12 and abs(I2 - I2_cf) < 1e-12 and abs(I12 - I12_cf) < 1e-12
          and lhs - rhs > 0.2)
    print(f"  -> {'OK' if ok else 'NG'}\n")
    return ok


def is_deterministic(W):
    return bool(np.all(np.abs(W - (W == W.max(axis=1, keepdims=True))) < 1e-12))


def harden(name, W1, W2, lam_s, cfg, witness):
    """正のギャップに対する反証義務 (env 側と witness 側の両方を潰す)。"""
    print("=== hardening (正の判定なので反証義務を果たす) ===")
    J, alph = witness
    ok = True

    # (1) env 側: C1 / C2 を 2 系統 + 証明つき上界で確定させる
    print("  (1) env 側の C1 / C2 を 2 系統で一致確認 (過小評価が偽陽性を作る向き)")
    for k, W in ((1, W1), (2, W2)):
        lo, hi, p = capacity(W, restarts=32, seed=100 + k)
        direct = capacity_direct(W, restarts=60, seed=200 + k)
        print(f"      C{k}: BA下界={lo:.12f} BA上界={hi:.12f} 直接最大化={direct:.12f} "
              f"上下界幅={hi - lo:.2e} 系統差={abs(direct - lo):.2e}")
        print(f"          達成入力分布 p = {np.array2string(p, precision=10)}")
        ok = ok and (hi - lo) < 1e-11 and abs(direct - lo) < 1e-8

    # (2) witness 側: 明示 (pV, K) を印字し、独立コード経路で三つ組を再計算
    print("  (2) ギャップを出した明示 witness (pV, K) と、独立コード経路での再評価")
    pV = J.sum(axis=2)
    K = J / np.maximum(pV[:, :, None], 1e-300)
    np.set_printoptions(precision=10, suppress=False, linewidth=120)
    print(f"      補助アルファベット (|V1|,|V2|) = {alph}")
    print(f"      pV = np.{np.array_repr(pV)}")
    print(f"      K[v1,v2,x] = np.{np.array_repr(K)}")
    I1, I2, I12 = marton_infos(pV, K, W1, W2)     # bc-marton-union-gap-check の独立実装
    print(f"      marton_infos (独立実装) : I1={I1:.12f} I2={I2:.12f} I12={I12:.12f}")
    # (3) 四辺形の support 値: 閉形式 / LP / -min 形 の 3 系統
    v_phi = phi(lam_s, (I1, I2, I12))
    v_max = cvx.h_quad(lam_s, I1, I2, I12)
    v_lp = cvx.h_quad_lp(lam_s, I1, I2, I12)
    print(f"  (3) 四辺形 support 値 at lam*={lam_s:.6f}: "
          f"-min 形={v_phi:.12f} max 形={v_max:.12f} LP={v_lp:.12f}")
    print(f"      3 系統の最大差 = {max(abs(v_phi - v_max), abs(v_phi - v_lp)):.3e}")
    ok = ok and max(abs(v_phi - v_max), abs(v_phi - v_lp)) < 1e-9

    # (4) 決定論的チャネルなら、最適化器を使わない解析ルートで S(lam) を再計算
    if is_deterministic(W1) and is_deterministic(W2):
        print("  (4) 決定論的 BC なので独立な解析ルート (Marton/Pinsker 形) で S(lam) を再計算")
        worst = 0.0
        for lam in (0.2, 0.3, 0.5, lam_s, 0.7, 0.9):
            mk.rng = np.random.default_rng(555)
            F, _, _, _, _ = h_free(lam, cfg["alph"], W1, W2, cfg["r_free"] * 2)
            d = det_bc_support(W1, W2, lam)
            worst = max(worst, abs(F - d))
            print(f"      lam={lam:.6f}: h_free={F:.12f} 解析ルート={d:.12f} 差={F - d:+.2e}")
        print(f"      最大差 = {worst:.3e}")
        ok = ok and worst < 1e-9
        # lam = 1/2 は閉形式まで落ちる: S(1/2) = (1/2) * max_p H(Y1,Y2)
        nb1, nb2 = W1.shape[1], W2.shape[1]
        f1, f2 = W1.argmax(axis=1), W2.argmax(axis=1)
        keys = sorted(set(zip(f1.tolist(), f2.tolist())))
        sum_rate = float(np.log(len(keys))) if len(keys) == W1.shape[0] else None
        if sum_rate is not None:
            mk.rng = np.random.default_rng(556)
            F_half, _, _, _, _ = h_free(0.5, cfg["alph"], W1, W2, cfg["r_free"] * 2)
            print(f"      閉形式 (x -> (y1,y2) が単射ゆえ max_p H(Y1,Y2) = ln{W1.shape[0]}): "
                  f"S(1/2) = {0.5 * sum_rate:.12f} vs 数値 {F_half:.12f} "
                  f"差={F_half - 0.5 * sum_rate:+.2e}")
            ok = ok and abs(F_half - 0.5 * sum_rate) < 1e-9
    else:
        print("  (4) 決定論的でないので解析ルートの照合は省略")

    # (5) S 側の増強: 補助アルファベットと restart を増やして lam* が動かないこと
    print("  (5) S 側の増強 (補助アルファベット + restart) — 増えても判定は正のまま")
    mk.rng = np.random.default_rng(909)
    big = cfg["alph"] + [(5, 5), (6, 6)]
    F2, tri2, _, alph2, _ = h_free(lam_s, big, W1, W2, cfg["r_free"] * 3)
    c1hi = capacity(W1, restarts=32, seed=101)[1]
    c2hi = capacity(W2, restarts=32, seed=102)[1]
    env = max(lam_s * c1hi, (1 - lam_s) * c2hi)
    print(f"      補助 {big} / restart x3 で S_LB(lam*) = {F2:.12f} (達成 {alph2})")
    print(f"      env_UB(lam*) = {env:.12f} ; 増強後のギャップ = {F2 - env:+.6e}")
    ok = ok and (F2 - env) > GAP_TOL
    print(f"  -> {'OK' if ok else 'NG'}\n")
    return ok


# ======================================================================
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--full", action="store_true")
    args = ap.parse_args()

    if args.quick:
        cfg = dict(n_rand=4, lams=np.linspace(0, 1, 5), alph=[(2, 2), (3, 3)],
                   r_free=3, ctrl_alph=[(2, 2), (3, 3)], sweep_pts=21, r_sweep=2,
                   fine_pts=401)
    elif args.full:
        cfg = dict(n_rand=96, lams=np.linspace(0, 1, 21),
                   alph=[(2, 2), (3, 3), (4, 4), (5, 5)], r_free=16,
                   ctrl_alph=[(2, 2), (3, 3), (4, 4)], sweep_pts=201, r_sweep=8,
                   fine_pts=4001)
    else:
        cfg = dict(n_rand=32, lams=np.linspace(0, 1, 11), alph=[(2, 2), (3, 3), (4, 4)],
                   r_free=6, ctrl_alph=[(2, 2), (3, 3)], sweep_pts=101, r_sweep=3,
                   fine_pts=1601)

    t_start = time.time()
    print("=== sim <-> Lean def の逐語照合 (bc-marton-union-gap-check.check_sim) ===")
    gap.check_sim()

    ok_c = control_c()
    ok_cap = capacity_check()
    ok_jk = joint_kernel_check(trials=40 if args.quick else 200)
    ok_cf = blackwell_closed_form_certificate()
    ok_ts = timesharing_support_check()
    ok_a = control_a(cfg)

    structured = structured_channels()
    channels = structured + random_channels(cfg["n_rand"])
    ok_b = control_b(cfg, structured)

    if not (ok_a and ok_b and ok_c and ok_cap and ok_ts and ok_jk and ok_cf):
        print("!! 肯定コントロールが落ちた。本走査は行わない (合わせにいかない)。")
        print(f"   (a)={ok_a} (b)={ok_b} (c)={ok_c} capacity={ok_cap} "
              f"timesharing={ok_ts} joint-kernel={ok_jk} closed-form={ok_cf}")
        return

    print("=== 本走査: S_LB(lam) vs env_UB(lam) = max(lam*C1_UB, (1-lam)*C2_UB) ===")
    print(f"  チャネル {len(channels)} 本 (構造 {len(structured)} + ランダム {cfg['n_rand']}) "
          f"x lam {len(cfg['lams'])} 点 x 補助 {cfg['alph']} , restart={cfg['r_free']}")
    t0 = time.time()
    results = []
    for i, (name, W1, W2, note, role) in enumerate(channels):
        d, lam_s, c1, c2, pool, wit, wlam = scan_channel(W1, W2, cfg, 10000 + i)
        results.append((d, lam_s, name, W1, W2, pool, wit, wlam, note, role))
        flag = "  <== ギャップ" if d > GAP_TOL else ""
        print(f"  {name:38s} max_lam (S_LB - env_UB) = {d:+.6e} at lam* = {lam_s:.4f}{flag}")
    print(f"  走査時間 {time.time() - t0:.1f}s\n")

    # コントロール 3 本の事後判定 (走査と同じ経路で回したものを検定する)
    by_role = {r[9]: r for r in results if r[9].startswith("ctrl")}
    ok_d = by_role["ctrl-d"][0] > 0.3
    ok_e = by_role["ctrl-e"][0] <= GAP_TOL
    ok_a2 = by_role["ctrl-a"][0] <= GAP_TOL
    print("=== 走査経路そのものに対するコントロールの判定 ===")
    print(f"  (d) 直積 |X|=4 (ギャップが構成から確実): {by_role['ctrl-d'][0]:+.6e} "
          f"(閉形式 (1/2)ln2 = {0.5 * np.log(2):.10f}) -> {'OK' if ok_d else 'NG'}")
    print(f"  (e) 同一分割 |X|=3 (潰れる側): {by_role['ctrl-e'][0]:+.6e} "
          f"-> {'OK' if ok_e else 'NG'}")
    print(f"  (a) 劣化 BSC 対 (潰れる側、L2 の既知の答え): {by_role['ctrl-a'][0]:+.6e} "
          f"-> {'OK' if ok_a2 else 'NG'}")
    if not (ok_d and ok_e and ok_a2):
        print("!! 走査経路のコントロールが落ちた。判定を出さない。\n")
        return
    print()

    rand_res = results[len(structured):]
    n_rand_gap = sum(1 for r in rand_res if r[0] > GAP_TOL)
    print(f"  ランダム |X|=3 チャネルでギャップが立った本数 = {n_rand_gap}/{len(rand_res)}\n")

    # 主張の witness は **|X|=3 の候補チャネルのみ** から採る (コントロールは除外)
    cands = sorted([r for r in results if r[9] == "cand" and r[3].shape[0] == 3],
                   key=lambda r: -r[0])
    d, lam_s, name, W1, W2, pool, wit, wlam, note, _role = cands[0]
    print("=== 最大ギャップの instance (|X|=3 の候補のみ。コントロールは除外) ===")
    print(f"  channel : {name}  {('(' + note + ')') if note else ''}")
    print(f"  lam*    : {lam_s:.6f}   (witness は lam={wlam:.4f} の最適点)")
    print(f"  S_LB(lam*) = {pool_lb(lam_s, pool):.12f}")
    c1hi = capacity(W1, restarts=32, seed=11)[1]
    c2hi = capacity(W2, restarts=32, seed=12)[1]
    print(f"  env_UB(lam*) = {max(lam_s * c1hi, (1 - lam_s) * c2hi):.12f} "
          f"(C1_UB={c1hi:.12f}, C2_UB={c2hi:.12f})")
    print(f"  gap     : {d:+.6e}\n")
    np.set_printoptions(precision=10, suppress=False, linewidth=120)
    print(f"  W1 = np.{np.array_repr(W1)}")
    print(f"  W2 = np.{np.array_repr(W2)}\n")

    ok_h = harden(name, W1, W2, lam_s, cfg, wit)

    n_cand_gap = sum(1 for r in cands if r[0] > GAP_TOL)
    print("=== 判定 ===")
    if d > GAP_TOL and ok_h:
        print(f"  **潰れないチャネル (|X|=3) が見つかった**: S_LB - env_UB = {d:+.6e} "
              f"> {GAP_TOL:.0e}")
        print(f"  最大ギャップの instance = {name} (lam* = {lam_s:.6f})")
        print(f"  |X|=3 候補 {len(cands)} 本のうちギャップが立ったのは {n_cand_gap} 本")
        print("  S 側は明示 witness による下界、env 側は BA の証明つき上界なので、")
        print("  **この符号は確実**である (探索不足では説明できない)。")
        print("  さらに Blackwell については上の閉形式の節が示すとおり、判定は")
        print("  (1/2)*(ln3 - ln2) > 0 という手計算まで落ちる (最適化に依存しない)。")
        print("  ⟹ 共通補助 U0 を持たない 2 補助変数 Marton union は、|X|=3 で既に")
        print("     時分割領域より真に強い。L2 が劣化 BSC 対で観測した「時分割への潰れ」は")
        print("     |X|=2 に固有の現象であって U0 の欠落の一般的な帰結ではない。")
        print("  ⚠ 射程: U0 が不要だとは言っていない (冒頭 docstring の射程節を参照)。")
    elif d > GAP_TOL:
        print(f"  ギャップ候補 {d:+.6e} は出たが hardening を通過しなかった。報告しない。")
    else:
        print(f"  **ギャップは出なかった**: |X|=3 候補 {len(cands)} 本で S_LB - env_UB <= "
              f"{max(d, 0.0):+.3e}")
        print("  ⚠ これは「潰れることの証明」ではない — S 側は下界しか無いので、")
        print("     探索不足と真の一致を区別できない。言えるのは「この探索では出なかった」まで。")
    print(f"\n合計実行時間 {time.time() - t_start:.1f}s")


if __name__ == "__main__":
    main()
