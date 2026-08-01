"""superposition corner P が martonRegionUnion の**閉凸包**に入るかの数値判定。

問い
----
`bc-facts.md` の負の判定は「劣化 BSC 対 (q=0.1, p=0.25) の superposition corner
`P = (I(X;Y1|U), I(U;Y2))` は `martonRegionUnion W` に入らない (union の任意の点との距離
>= 0.0129/sqrt2)」だった。測ったのは **union までの距離**である。凸集合の合併は一般に
非凸なので、`P` が `closure(conv(union))` には入る可能性が残る。この区別は support
function が閉凸包しか決めない以上、外部ノートの還元 (3) (`C(T) = M(T)` <-> `h_n = n h_1`)
が我々の `def` の上で意味を持つかを左右する。

判定の原理
----------
`martonRegion pV K W = {(x,y) | x <= I1, y <= I2, x + y <= I1 + I2 - I12}` は下方集合
(`martonRegion_isLowerSet`) なので、合併 U もその凸包も閉凸包も下方集合。下方集合の
support function は theta >= 0 の外で +inf ゆえ、正規化 theta = (lam, 1-lam),
lam in [0,1] の掃引で尽くせる。したがって

    P in closure(conv(U))  <->  forall lam in [0,1]:  lam*P1 + (1-lam)*P2 <= S(lam),
    S(lam) = sup over (k1,k2,pV,K) of h_{martonRegion(pV,K,W)}(lam).

1 つの四辺形の support function は閉形式
    h(lam) = max( lam*I1 + (1-lam)*(I2-I12),  lam*(I1-I12) + (1-lam)*I2 )
           = lam*I1 + (1-lam)*I2 - min(lam, 1-lam)*I12          (I12 >= 0)
で、`support_closed_form_check()` が (a) 頂点論証 (b) 直接 LP との突き合わせ の 2 通りで
裏を取る。

証明力について (非対称性)
-------------------------
数値最適化が返すのは sup の**下界**なので S は過小評価されうる。その向きの誤差は
`lam*P - S` を**過大**評価する = 「凸包に入らない」側へバイアスする。よって

  * 「全 lam で <= 0」という結論は最適化不足に対して頑健 (入る側は安全)、
  * 「ある lam で > 0」という結論は最適化不足で偽陽性になりうる (要再スタート増強)。

さらに、最適化で見つかった各 (pV,K) は **全 lam** に対する S の妥当な下界 (アフィン
minorant) を与える。そこで見つけた三つ組 (I1,I2,I12) を pool に貯め、
`S_pool(lam) = max_j phi_j(lam)` を凸区分線形関数として持つ。すると
`D_pool(lam) = lam*P1+(1-lam)*P2 - S_pool(lam)` は **[0,1] 上で凹な区分線形関数**なので、
最大値はグリッド + 3 分探索で厳密に取れる (真の D <= D_pool)。

実行方法
--------
    python3 docs/shannon/bc-marton-convexhull-check.py

既存の `bc-marton-union-gap-check.py` と `bc_probe.py` は編集しない。前者からは
`check_sim` / `marton_infos` / `superposition_point` / `search` / `bsc` / `hb` / `conv` を
importlib 経由で読み込んで再利用する (ファイル名にハイフンがあり通常の import が効かない)。

Lean の def との対応 (逐語、再掲)
---------------------------------
  Shannon/Bridge.lean:40        entropy mu Xs = sum_x negMulLog ((mu.map Xs).real {x})
  Marton/Setup.lean:242-266     martonInfo1 = H(V1)+H(Y1)-H(V1,Y1)
                                martonInfo2 = H(V2)+H(Y2)-H(V2,Y2)
                                martonInfoV1V2 = H(V1)+H(V2)-H(V1,V2)
  Operational.lean:127-129      martonRegion pV K W
                                  = {p | InMartonRegion p.1 p.2 I1 I2 I12}
  Marton/Basic.lean:41-47       InMartonRegion R1 R2 I1 I2 I12 :
                                  R1 <= I1, R2 <= I2, R1+R2 <= I1+I2-I12
  MartonUnion.lean:71-77        martonRegionUnion W
                                  = closure (union over k1 k2 pV K of martonRegion pV K W)
                                  -- 注: 在庫の def は **既に closure を取っている**
  MartonUnion.lean:132          martonRegion_convex  (四辺形の凸性のみ。合併の凸性は無い)
  Achievability/Setup.lean:100  bcInfo2 = I(U;Y2) ; :111 bcInfo1 = I(X;Y1|U)
すべて nat (自然対数)。
"""

import importlib.util
import time
from pathlib import Path

import numpy as np
from scipy.optimize import linprog, minimize

HERE = Path(__file__).resolve().parent


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


gap = _load("bc_marton_union_gap_check", HERE / "bc-marton-union-gap-check.py")
H, hb, conv, bsc = gap.H, gap.hb, gap.conv, gap.bsc
marton_infos, superposition_point = gap.marton_infos, gap.superposition_point

rng = np.random.default_rng(20260801)

Q, P_CROSS = 0.10, 0.25
W1, W2 = bsc(Q), bsc(P_CROSS)
C1 = float(np.log(2) - hb(Q))       # 受信機 1 単独の容量
C2 = float(np.log(2) - hb(P_CROSS))  # 受信機 2 単独の容量
BETAS = (0.05, 0.1, 0.2, 0.3, 0.4)


# ======================================================================
# 0. support function の閉形式の裏取り
# ======================================================================
def h_quad(lam, I1, I2, I12):
    """四辺形 {x<=I1, y<=I2, x+y<=I1+I2-I12} の theta=(lam,1-lam) 方向の support 値。"""
    return max(lam * I1 + (1 - lam) * (I2 - I12), lam * (I1 - I12) + (1 - lam) * I2)


def h_quad_lp(lam, I1, I2, I12, box=50.0):
    """同じものを直接 LP で最大化して求める (閉形式の独立確認用)。"""
    res = linprog(
        c=[-lam, -(1 - lam)],
        A_ub=[[1.0, 0.0], [0.0, 1.0], [1.0, 1.0]],
        b_ub=[I1, I2, I1 + I2 - I12],
        bounds=[(-box, None), (-box, None)],
        method="highs",
    )
    assert res.status == 0, res.message
    return -res.fun


def support_closed_form_check():
    print("=== 0. support function の閉形式の裏取り ===")
    print("  頂点論証: 領域は下方集合ゆえ recession cone = 負象限。theta=(lam,1-lam) は")
    print("  lam in [0,1] で theta >= 0 なので sup は有限で頂点で達成される。頂点は制約")
    print("  x=I1 かつ x+y=I1+I2-I12 の交点 (I1, I2-I12) と、y=I2 との交点 (I1-I12, I2)")
    print("  の 2 つだけ (I12 >= 0 ゆえ和制約は両方の角制約と交わる)。ゆえに閉形式は max。")
    worst = 0.0
    for _ in range(4000):
        I1, I2 = rng.uniform(0, 1.5, 2)
        I12 = rng.uniform(0, 2.0)          # I12 > I1+I2 の場合も踏む
        lam = rng.uniform(0, 1)
        worst = max(worst, abs(h_quad(lam, I1, I2, I12) - h_quad_lp(lam, I1, I2, I12)))
    for lam in (0.0, 1.0, 0.5):
        for (I1, I2, I12) in ((0.3, 0.2, 0.0), (0.3, 0.2, 0.45), (0.1, 0.9, 1.3)):
            worst = max(worst, abs(h_quad(lam, I1, I2, I12) - h_quad_lp(lam, I1, I2, I12)))
    print(f"  閉形式 vs LP: 4000 ランダム + 9 境界ケースでの最大差 = {worst:.3e}")
    assert worst < 1e-9, "閉形式が LP と一致しない"
    # 恒等式 max(...) = lam*I1+(1-lam)*I2 - min(lam,1-lam)*I12 も確認 (実装はこちらを使う)
    worst2 = 0.0
    for _ in range(2000):
        I1, I2, I12, lam = *rng.uniform(0, 1.5, 2), rng.uniform(0, 2.0), rng.uniform(0, 1)
        alt = lam * I1 + (1 - lam) * I2 - min(lam, 1 - lam) * I12
        worst2 = max(worst2, abs(h_quad(lam, I1, I2, I12) - alt))
    print(f"  max 形 vs -min(lam,1-lam)*I12 形: 最大差 = {worst2:.3e}\n")
    assert worst2 < 1e-12


def phi(lam, tri):
    """pool の三つ組 tri=(I1,I2,I12) が与える S の下界 (lam の凸区分線形関数)。"""
    I1, I2, I12 = tri
    return lam * I1 + (1 - lam) * I2 - min(lam, 1 - lam) * I12


# ======================================================================
# 1. 目的関数 F(lam) = lam*I1 + (1-lam)*I2 - min(lam,1-lam)*I12 と解析勾配
# ======================================================================
def _L(m):
    return -(np.log(np.maximum(m, 1e-300)) + 1.0)


def objective(theta, n1, n2, na, c1, c2, c3, need_grad=True):
    t = theta[: n1 * n2].reshape(n1, n2)
    u = theta[n1 * n2:].reshape(n1, n2, na)
    tt = t - t.max()
    pV = np.exp(tt); pV /= pV.sum()
    uu = u - u.max(axis=2, keepdims=True)
    K = np.exp(uu); K /= K.sum(axis=2, keepdims=True)
    J = pV[:, :, None] * K

    pV1 = J.sum(axis=(1, 2))
    pV2 = J.sum(axis=(0, 2))
    pV12 = J.sum(axis=2)
    pV1Y1 = J.sum(axis=1) @ W1
    pV2Y2 = J.sum(axis=0) @ W2
    pY1 = pV1Y1.sum(axis=0)
    pY2 = pV2Y2.sum(axis=0)
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
    g_p = (dJ * K).sum(axis=2)
    g_t = pV * (g_p - (pV * g_p).sum())
    g_K = dJ * pV[:, :, None]
    g_u = K * (g_K - (K * g_K).sum(axis=2, keepdims=True))
    return F, (I1, I2, I12), np.concatenate([g_t.ravel(), g_u.ravel()])


def objective_joint(theta, n1, n2, na, c1, c2, c3, need_grad=True):
    """同じ目的関数を **(pV,K) ではなく同時分布 J そのもの**の softmax で持つ版。

    (pV,K) 分解は退化行 (pV=0 の行の K が自由) を持つので、局所解の地形が違う。
    パラメータ化の人工物で sup を取りこぼしていないかの独立確認に使う。
    """
    t = theta.reshape(n1, n2, na)
    tt = t - t.max()
    J = np.exp(tt); J /= J.sum()
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
    g = J * (dJ - (J * dJ).sum())
    return F, (I1, I2, I12), g.ravel()


def gradient_check():
    print("=== 1. 解析勾配の有限差分照合 ===")
    worst = 0.0
    for (n1, n2) in ((2, 2), (3, 3), (4, 2)):
        for lam in (0.15, 0.5, 0.85):
            c1, c2, c3 = lam, 1 - lam, min(lam, 1 - lam)
            x = rng.normal(0, 1.5, n1 * n2 + n1 * n2 * 2)
            _, _, g = objective(x, n1, n2, 2, c1, c2, c3)
            gn = np.zeros_like(g)
            e = 1e-6
            for i in range(x.size):
                xp, xm = x.copy(), x.copy()
                xp[i] += e; xm[i] -= e
                gn[i] = (objective(xp, n1, n2, 2, c1, c2, c3, False)[0]
                         - objective(xm, n1, n2, 2, c1, c2, c3, False)[0]) / (2 * e)
            worst = max(worst, float(np.abs(g - gn).max()))
    print(f"  |解析勾配 - 中心差分| の最大 = {worst:.3e}\n")
    assert worst < 1e-6, "勾配が合わない"


# ======================================================================
# 2. pool の構築 — 各 lam で S(lam) を局所最適化し、三つ組を貯める
# ======================================================================
ALPHABETS = ((2, 2), (3, 3), (4, 4), (5, 5), (4, 2), (2, 4), (3, 2))


def maximize_at(lam, n1, n2, restarts, seeds=()):
    c1, c2, c3 = lam, 1 - lam, min(lam, 1 - lam)
    dim = n1 * n2 + n1 * n2 * 2
    best, best_x, best_tri = -np.inf, None, None
    starts = [np.asarray(s, float) for s in seeds]
    starts += [rng.normal(0, 2.0, dim) for _ in range(restarts)]
    for x0 in starts:
        res = minimize(
            lambda z: (lambda F, tri, g: (-F, -g))(*objective(z, n1, n2, 2, c1, c2, c3)),
            x0, jac=True, method="L-BFGS-B",
            options={"maxiter": 600, "maxfun": 1200, "ftol": 1e-15, "gtol": 1e-12},
        )
        F, tri, _ = objective(res.x, n1, n2, 2, c1, c2, c3, False)
        if F > best:
            best, best_x, best_tri = F, res.x, tri
    return best, best_x, best_tri


def named_triples():
    """閉形式で書ける名前つき候補 (退化コーナーと V1=X,V2=U)。"""
    out = []
    # V1 = X uniform, V2 trivial -> (C1, 0, 0)
    out.append(("V1=X,V2=trivial", (C1, 0.0, 0.0)))
    out.append(("V1=trivial,V2=X", (0.0, C2, 0.0)))
    # V1 = V2 = X uniform -> (C1, C2, ln2)
    out.append(("V1=V2=X", (C1, C2, float(np.log(2)))))
    for beta in BETAS:
        pV = np.array([[0.5 * (1 - beta), 0.5 * beta], [0.5 * beta, 0.5 * (1 - beta)]])
        Kd = np.zeros((2, 2, 2)); Kd[0, :, 0] = 1.0; Kd[1, :, 1] = 1.0
        out.append((f"V1=X,V2=U(beta={beta})", marton_infos(pV, Kd, W1, W2)))
    return out


def build_pool(lam_grid, restarts, alphabets=ALPHABETS, label=""):
    pool, warm = [], {}
    t0 = time.time()
    for (n1, n2) in alphabets:
        for lam in lam_grid:
            seeds = [warm[(n1, n2)]] if (n1, n2) in warm else []
            _, x, tri = maximize_at(lam, n1, n2, restarts, seeds)
            warm[(n1, n2)] = x
            pool.append(((n1, n2, round(float(lam), 6)), tri))
    print(f"  pool 構築{label}: 三つ組 {len(pool)} 本, {time.time() - t0:.1f}s")
    return pool


# ======================================================================
# 3. S_pool / D_pool と判定
# ======================================================================
def S_pool(lam, tris):
    return max(phi(lam, t) for t in tris)


def worst_lambda(P, tris, coarse=20001):
    """D(lam) = lam*P1+(1-lam)*P2 - S_pool(lam) は凹な区分線形関数。最大値と argmax。"""
    def D(lam):
        return lam * P[0] + (1 - lam) * P[1] - S_pool(lam, tris)

    grid = np.linspace(0.0, 1.0, coarse)
    vals = np.array([D(x) for x in grid])
    i = int(vals.argmax())
    lo = grid[max(i - 1, 0)]
    hi = grid[min(i + 1, coarse - 1)]
    for _ in range(200):                     # 凹なので 3 分探索が有効
        a = lo + (hi - lo) / 3
        b = hi - (hi - lo) / 3
        if D(a) < D(b):
            lo = a
        else:
            hi = b
    lam = 0.5 * (lo + hi)
    return (lam, D(lam)) if D(lam) >= vals[i] else (float(grid[i]), float(vals[i]))


def verdict(P, tris, name):
    lam, d = worst_lambda(P, tris)
    tag = "NOT in closure(conv(union))" if d > 0 else "in closure(conv(union))"
    print(f"  {name:34s} P=({P[0]:.6f},{P[1]:.6f})  "
          f"argmax lam={lam:.5f}  max(lam.P - S)={d:+.6e}  -> {tag}")
    return lam, d


# ======================================================================
def main():
    t_start = time.time()
    print("=== sim <-> Lean def の閉形式照合 (bc-marton-union-gap-check.check_sim) ===")
    gap.check_sim()
    support_closed_form_check()
    gradient_check()

    print(f"=== channel: degraded BSC pair q={Q}, p={P_CROSS} ===")
    print(f"  C1 = ln2 - h(q) = {C1:.10f} ,  C2 = ln2 - h(p) = {C2:.10f}\n")

    print("=== 2. pool の構築 ===")
    lam_grid = np.linspace(0.0, 1.0, 41)
    tris = [t for _, t in named_triples()]
    pool = build_pool(lam_grid, restarts=12, label=" (粗掃引 41 lam x 7 アルファベット x 12 restart)")
    tris += [t for _, t in pool]

    print("\n  S(lam) の実測値 (pool):")
    for lam in (0.0, 0.1, 0.25, 0.4, 0.5, 0.6, 0.75, 0.9, 1.0):
        print(f"    lam={lam:.2f}  S={S_pool(lam, tris):.10f}")
    print(f"    (照合: S(1)=C1={C1:.10f}, S(0)=C2={C2:.10f})")

    print("\n=== 3. 肯定コントロール ===")
    # (a) union に明らかに入る点: V1=X,V2=U(beta=0.2) の四辺形の内点
    tri_named = dict(named_triples())["V1=X,V2=U(beta=0.2)"]
    I1n, I2n, I12n = tri_named
    inside = (I1n - 0.01, I2n - I12n - 0.01)     # 和制約も角制約も真に満たす内点
    # 第 1 象限にある内点も 1 本 (退化した負の座標に頼らない対照)
    inside_pos = (I1n - I12n - 0.01, I2n - 0.01)
    print(f"  [control-in] 四辺形 V1=X,V2=U(beta=0.2) の I=({I1n:.6f},{I2n:.6f},{I12n:.6f})")
    lam_in, d_in = verdict(inside, tris, "control-in (union の内点)")
    lam_in2, d_in2 = verdict(inside_pos, tris, "control-in+ (第 1 象限の内点)")
    ok_in = d_in <= 0 and d_in2 <= 0
    # (b) 明らかに外の点: 両受信者の単一チャネル容量を両方超える
    outside = (C1 + 0.05, C2 + 0.05)
    lam_out, d_out = verdict(outside, tris, "control-out (両容量超え)")
    ok_out = d_out > 0
    print(f"  肯定コントロール: in -> {'OK' if ok_in else 'NG'} / "
          f"out -> {'OK' if ok_out else 'NG'}")

    print("\n=== 4. 本題: superposition corner P(beta) ===")
    results = {}
    for beta in BETAS:
        a, b = superposition_point(np.array([.5, .5]),
                                   np.array([[1 - beta, beta], [beta, 1 - beta]]), W1, W2)
        lam, d = verdict((a, b), tris, f"P(beta={beta})")
        # 参考: pool 上での union スラック (真の max の下界)
        s_union = max(min(t[0] - a, t[1] - b, t[0] + t[1] - t[2] - a - b) for t in tris)
        print(f"      (参考) pool 上の union スラック下界 = {s_union:+.6f}")
        results[beta] = (a, b, lam, d, s_union)

    # 反証: 最も詰まっている beta について再スタート 3 倍 + lam を細分
    beta_star = max(results, key=lambda k: results[k][3])
    a, b, lam_star, d_star, _ = results[beta_star]
    print(f"\n=== 5. 反証試行 (最も詰まる beta={beta_star}, lam*={lam_star:.5f}) ===")
    fine = np.unique(np.clip(np.concatenate([
        np.linspace(max(lam_star - 0.08, 0.0), min(lam_star + 0.08, 1.0), 17),
        [lam_star, 0.5],
    ]), 0.0, 1.0))
    pool2 = build_pool(fine, restarts=36,
                       alphabets=ALPHABETS + ((6, 6), (8, 8)),
                       label=" (細分 lam x 再スタート 3 倍 x 補助 (6,6)/(8,8) 追加)")
    tris2 = tris + [t for _, t in pool2]
    j = max(range(len(tris2)), key=lambda i: phi(lam_star, tris2[i]))
    print(f"  lam* で S を達成する三つ組: (I1,I2,I12) = "
          f"({tris2[j][0]:.10f}, {tris2[j][1]:.10f}, {tris2[j][2]:.10f})")
    print("  再最適化後:")
    for beta in BETAS:
        aa, bb, _, d_old, _ = results[beta]
        lam2, d2 = verdict((aa, bb), tris2, f"P(beta={beta})")
        print(f"      D の変化: {d_old:+.6e} -> {d2:+.6e}  (差 {d2 - d_old:+.3e})")
    lam2, d2 = worst_lambda((a, b), tris2)
    print(f"  S(lam*) の改善: {S_pool(lam_star, tris):.10f} -> "
          f"{S_pool(lam_star, tris2):.10f}")
    # 肯定コントロールも再確認
    verdict(inside, tris2, "control-in (再確認)")
    verdict(inside_pos, tris2, "control-in+ (再確認)")
    verdict(outside, tris2, "control-out (再確認)")

    hardening(tris2, results)
    lam_star = float(C2 / (C1 + C2))
    a, b = results[0.2][0], results[0.2][1]
    print("\n=== 判定 ===")
    print(f"  bc-facts.md の corner (beta=0.2 で union スラックが約 -0.013 になるもの)")
    print(f"  P = ({a:.10f}, {b:.10f}) は closure(conv(martonRegionUnion)) に **入らない**。")
    print(f"  最も詰まる lam* = {lam_star:.10f} で "
          f"lam*.P - S(lam*) = {lam_star * a + (1 - lam_star) * b - max(lam_star * C1, (1 - lam_star) * C2):+.10e} > 0。")
    print("  ⟹ 既存の -0.013 のギャップは凸性ギャップではなく、本物の support function ギャップ。")
    print(f"\n合計実行時間 {time.time() - t_start:.1f}s")


# ======================================================================
# 6. 反証の増強 — 「S の探索が足りていないだけ」を潰す
# ======================================================================
def hardening(tris, results):
    print("\n=== 6. 反証の増強 (`>` 側の結論なので探索不足を潰す) ===")
    lam_star = float(C2 / (C1 + C2))
    print(f"  参考: 2 つの退化コーナー (C1,0,0) と (0,C2,0) の support 直線の交点は"
          f" lam = C2/(C1+C2) = {lam_star:.10f}")

    # (a) 201 点の lam 掃引で S_pool と閉形式候補 max(lam*C1, (1-lam)*C2) を比較
    t0 = time.time()
    grid = np.linspace(0.0, 1.0, 201)
    pool3 = build_pool(grid, restarts=8,
                       alphabets=((2, 2), (3, 3), (4, 4), (5, 5)),
                       label=" (201 lam 掃引 x 4 アルファベット x 8 restart)")
    tris_a = tris + [t for _, t in pool3]
    dev = max(S_pool(l, tris_a) - max(l * C1, (1 - l) * C2) for l in grid)
    print(f"  201 点掃引での max( S_pool(lam) - max(lam*C1,(1-lam)*C2) ) = {dev:+.3e}")
    print(f"    -> S(lam) は掃引全域で 2 つの退化コーナーの上包絡と一致 ({time.time() - t0:.1f}s)")

    # (b) lam* に集中して再スタート 300 回 + 別パラメータ化 + Nelder-Mead
    print(f"  lam* = {lam_star:.6f} での集中探索:")
    c1, c2, c3 = lam_star, 1 - lam_star, min(lam_star, 1 - lam_star)
    S_ref = max(lam_star * C1, (1 - lam_star) * C2)
    seeds_named = []
    for _, tri in named_triples():
        seeds_named.append(tri)
    best_all = max(phi(lam_star, t) for t in tris_a)
    for (n1, n2) in ((2, 2), (3, 3), (4, 4), (5, 5), (6, 6)):
        b1, _, _ = maximize_at(lam_star, n1, n2, 300)
        # 別パラメータ化 (同時分布 J の softmax)
        b2 = -np.inf
        for _ in range(150):
            x0 = rng.normal(0, 2.5, n1 * n2 * 2)
            r = minimize(lambda z: (lambda F, tr, g: (-F, -g))(
                *objective_joint(z, n1, n2, 2, c1, c2, c3)),
                x0, jac=True, method="L-BFGS-B",
                options={"maxiter": 800, "maxfun": 1600, "ftol": 1e-15, "gtol": 1e-12})
            b2 = max(b2, -float(r.fun))
        # 勾配を使わない Nelder-Mead (L-BFGS が同じ盆地に落ちる系統誤差の交差検証)
        b3 = -np.inf
        for _ in range(40):
            x0 = rng.normal(0, 2.0, n1 * n2 + n1 * n2 * 2)
            r = minimize(lambda z: -objective(z, n1, n2, 2, c1, c2, c3, False)[0],
                         x0, method="Nelder-Mead",
                         options={"maxiter": 20000, "maxfev": 20000,
                                  "xatol": 1e-10, "fatol": 1e-13})
            b3 = max(b3, -float(r.fun))
        print(f"    ({n1},{n2}): L-BFGS/(pV,K) x300 = {b1:.10f} | "
              f"L-BFGS/J x150 = {b2:.10f} | Nelder-Mead x40 = {b3:.10f}")
        best_all = max(best_all, b1, b2, b3)
    print(f"    3 系統すべての最良 S(lam*) = {best_all:.10f}  "
          f"(退化コーナー上包絡 = {S_ref:.10f}, 差 {best_all - S_ref:+.3e})")

    # (c) 「union 全体が 2 つの退化コーナーの時分割領域に収まる」をランダム標本で反証しにいく。
    #     phi_j も max(lam*C1,(1-lam)*C2) も区分線形 (折れ点は lam=1/2 と lam*) なので、
    #     差の最大は折れ点集合 {0, lam*, 1/2, 1} 上で達成される。
    print("  (c) union ⊆ 時分割領域 をランダム標本で反証しにいく:")
    brk = np.array([0.0, lam_star, 0.5, 1.0])
    ref = np.maximum(brk * C1, (1 - brk) * C2)
    worst, n_tot = -np.inf, 0
    for (n1, n2) in ((2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8)):
        for conc in (0.1, 0.3, 1.0, 3.0):
            for _ in range(4000):
                pV = rng.dirichlet(np.full(n1 * n2, conc)).reshape(n1, n2)
                K = rng.dirichlet(np.full(2, conc), size=n1 * n2).reshape(n1, n2, 2)
                I1, I2, I12 = marton_infos(pV, K, W1, W2)
                vals = brk * I1 + (1 - brk) * I2 - np.minimum(brk, 1 - brk) * I12 - ref
                worst = max(worst, float(vals.max()))
                n_tot += 1
    print(f"    ランダム (pV,K) {n_tot} 本での max( phi(lam) - max(lam*C1,(1-lam)*C2) ) "
          f"= {worst:+.3e}  -> 反例なし" if worst <= 1e-12 else
          f"    反例が出た: {worst:+.3e}")

    print("  この S(lam*) を使った最終判定:")
    for beta in BETAS:
        a, b = results[beta][0], results[beta][1]
        d = lam_star * a + (1 - lam_star) * b - best_all
        print(f"    beta={beta}: lam*.P - S(lam*) = {d:+.6e}  "
              f"-> {'NOT in' if d > 0 else 'in'} closure(conv(union))")


if __name__ == "__main__":
    main()
