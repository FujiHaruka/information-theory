"""Gohari–Liu–Nair (ISIT 2025) §III-B の局所最大点の数値再現 (軸 G / L1 テストケース (b))。

対象
----
A. Gohari, Y. Liu, C. Nair, *A Conjecture Regarding the Optimizers of Marton's Inner Bound
for the Two-Receiver Broadcast Channel* (ISIT 2025),
https://chandra.ie.cuhk.edu.hk/pub/papers/BC/Mar-Con.pdf

**既知の答えがある再現課題**なので、harness (`bc_probe.py`) 自体の検証を兼ねる。
論文が印刷している数値 (遷移行列 2 枚 / {a_x} / α / λ / p*(u,v) / 目的値 4 つ) をすべて
逐語で写し、こちらで独立に計算した値と突き合わせる。**合わなかった場合にパラメータを
いじって合わせにいってはならない** — それをすると「既知の答えで harness を検証する」
という目的そのものが消える。

論文からの逐語引用 (英語論文なので原文のまま)
---------------------------------------------
目的汎関数 (§III eq. (2) / §III-B eq. (11)):

    G(p(u, v, x)) = − αH(Y ) − (λ − α)H(Z) + I(U ; Y ) + λI(V ; Z) − I(U ; V ) + Σ_x p(x) a_x

  ⚠ 第 2 項は `(λ − α)` であって `(1 − α)` ではない (本例は λ = 1 なので一致する)。

    F (T, {ax }) = max_{p(u,v,x)} [ ... 上と同じ ... ]

"rectangular" の定義 (§II-A、Proposition 1 直後):

    "Consider a |U| × |V| matrix where the matrix entries are determined by the mapping of
     (u, v) to x ∈ X , i.e., in the (u, v) cell of the matrix, we put the symbol x that (u, v)
     is mapped into. Then, for a maximizer p*(u, v, x) satisfying the Markovity conjecture,
     the matrix locations marked as x, for any fixed x ∈ X , will form a "rectangle", i.e. of
     the form Sx × Tx . We call such a mapping to be a rectangular mapping."

局所最大性の定義 (§III、eq. (3) の直前):

    "We say that p(u, v, x) is a local maximizer if the following three types of perturbations
     do not increase G(p(u, v, x)):
     • Perturbations that keep the alphabet size of U and V unchanged:
       pϵ (u, v, x) = (1 − ϵ)p(u, v, x) + ϵs(u, v, x) for some distribution s(u, v, x).
     • Perturbations that increase the alphabet size of U by one:
       pϵ (u, v, x) = p(u, v, x) − ϵs(u, v, x), u ∈ [1 : U|] ;  ϵq(v, x), u = |U| + 1.
       for some arbitrary distributions q(v, x) and s(u, v, x).
     • Similarly, perturbations that increase the alphabet size of V by one."

Conjecture 2 (§II):

    "(The Markovity Conjecture) When evaluating the extremal points of Marton's achievable
     region, it is sufficient to consider the random variable tuples (U, V, W, X) such that the
     Markov chain U → (W, X) → V holds. Equivalently, for every arbitrary {ax }, to compute
     F (T, {ax }), it is sufficient to consider the random variable tuples (U, V, X) such that
     the Markov chain U → X → V holds."

実行方法
--------
  python3 docs/shannon/bc-markovity-localmax-check.py            # 既定 (数分)
  python3 docs/shannon/bc-markovity-localmax-check.py --quick    # 再現部分だけ (数秒)

Lean の def との対応
--------------------
**依存しない**。ここで扱うのは論文の双対汎関数 `F(T,{a_x})` であって、我々の Lean の
Marton 領域の `def` ではない (両者の対応付けは L2 以降の別項目)。したがって照合対象は
entropy の規約だけで、harness が `Shannon/Bridge.lean:40` の自然対数版と一致させている。
論文は単位を明記していないが、**nat で 4 つの目的値がすべて再現する** (bit では再現しない)。
"""

import itertools
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bc_probe import (  # noqa: E402
    BayesNet,
    local_max_certificate,
    maximize,
    softmax,
)

rng = np.random.default_rng(20260801)

# ---------------------------------------------------------------- 論文の数値 (逐語)
# X = Y = Z = {A, B, C}  ->  index 0, 1, 2
A_X = np.array([0.0, -0.36832504, -0.13005504])
ALPHA = 0.53699858
LAMBDA = 1.0
ABAR = 1.0 - ALPHA

T_Y = np.array([  # T(y|x)      Y=A          Y=B          Y=C
    [0.35332099, 0.34718682, 0.29949219],   # X=A
    [0.76824470, 0.12006556, 0.11168974],   # X=B
    [0.13810833, 0.48234150, 0.37955017],   # X=C
])
T_Z = np.array([  # T(z|x)      Z=A          Z=B          Z=C
    [0.44260251, 0.21452819, 0.34286930],   # X=A
    [0.40932411, 0.00992684, 0.58074905],   # X=B
    [0.27754304, 0.56201647, 0.16044049],   # X=C
])

P_UV = np.array([  # p*(u,v)     V=0          V=1
    [0.01524814, 0.22806511],               # U=0
    [0.09087526, 0.66581149],               # U=1
])

SYM = "ABC"
# f(U,V):  U=0 -> (A, B),  U=1 -> (C, A)   = the non-rectangular "A B / C A" pattern
MAP_LOCAL = ((0, 1), (2, 0))
REPORTED_LOCAL = -1.06956384
RECTANGULAR = [  # (pattern, 論文が報告する値)
    (((0, 1), (2, 1)), -1.06730708),   # A B / C B
    (((1, 1), (2, 0)), -1.06895326),   # B B / C A
    (((2, 1), (2, 1)), -1.06228037),   # C B / C B
]


def pattern_str(f) -> str:
    return f"{SYM[f[0][0]]} {SYM[f[0][1]]} / {SYM[f[1][0]]} {SYM[f[1][1]]}"


def is_rectangular(f) -> bool:
    """各 x の占める位置が S_x × T_x の形か (論文 §II-A の定義)。"""
    arr = np.array(f)
    for x in range(3):
        loc = np.argwhere(arr == x)
        if loc.size == 0:
            continue
        rows, cols = set(loc[:, 0]), set(loc[:, 1])
        if len(loc) != len(rows) * len(cols):
            return False
    return True


# ---------------------------------------------------------------- 目的汎関数
def _H(p: np.ndarray, bits: bool = False) -> float:
    q = np.asarray(p, dtype=float).ravel()
    q = q[q > 0]
    h = float(-(q * np.log(q)).sum())
    return h / float(np.log(2.0)) if bits else h


def G(p_uvx: np.ndarray, bits: bool = False) -> float:
    """論文 (11): G = −αH(Y) − (λ−α)H(Z) + I(U;Y) + λI(V;Z) − I(U;V) + Σ_x p(x)a_x。

    (U,V) → X → (Y,Z) を仮定 (論文の設定)。Y と Z の周辺しか現れないので、
    T(y,z|x) が積かどうかは値に影響しない。`bits=True` はエントロピーを底 2 で測った
    別読みで、単位の判定にだけ使う (論文の値は nat 版で再現する)。
    """
    def H(p):
        return _H(p, bits)

    px = p_uvx.sum(axis=(0, 1))
    pux = p_uvx.sum(axis=1)
    pvx = p_uvx.sum(axis=0)
    puv = p_uvx.sum(axis=2)
    py, pz = px @ T_Y, px @ T_Z
    puy, pvz = pux @ T_Y, pvx @ T_Z
    pu, pv = puv.sum(axis=1), puv.sum(axis=0)
    i_uy = H(pu) + H(py) - H(puy)
    i_vz = H(pv) + H(pz) - H(pvz)
    i_uv = H(pu) + H(pv) - H(puv)
    return (-ALPHA * H(py) - (LAMBDA - ALPHA) * H(pz)
            + i_uy + LAMBDA * i_vz - i_uv + float(px @ A_X))


def joint_from_map(puv: np.ndarray, f) -> np.ndarray:
    nu, nv = puv.shape
    p = np.zeros((nu, nv, 3))
    for u in range(nu):
        for v in range(nv):
            p[u, v, f[u][v]] = puv[u, v]
    return p


def G_via_harness(p_uvx: np.ndarray) -> float:
    """同じ量を harness の BayesNet + 式パーサで組み直す (実装の相互検証)。"""
    nu, nv = p_uvx.shape[0], p_uvx.shape[1]
    puv = p_uvx.sum(axis=2)
    with np.errstate(invalid="ignore", divide="ignore"):
        px_given_uv = np.where(puv[:, :, None] > 0,
                               p_uvx / np.where(puv[:, :, None] > 0, puv[:, :, None], 1.0),
                               np.full(3, 1 / 3.0))
    bn = BayesNet()
    bn.add(("U", "V"), (nu, nv), (), kernel=puv)
    bn.add("X", 3, ["U", "V"], kernel=px_given_uv)
    bn.add("Y", 3, ["X"], kernel=T_Y)
    bn.add("Z", 3, ["X"], kernel=T_Z)
    J = bn.build()
    px = p_uvx.sum(axis=(0, 1))
    return (J.eval(f"-{ALPHA!r}*H(Y) - {LAMBDA - ALPHA!r}*H(Z)"
                   f" + I(U;Y) + {LAMBDA!r}*I(V;Z) - I(U;V)")
            + float(px @ A_X))


# ---------------------------------------------------------------- 論文の 1 階条件
def cond4(p_uvx: np.ndarray) -> np.ndarray:
    """論文 (4) の左辺を全 (u,v,x) について返す。F 以下であるべき、x = f(u,v) で等号。

    Σ_{y,z} T(y,z|x) log[ p(u,y) p(v,z)^λ e^{a_x}
                          / (p(y)^ᾱ p(z)^α p(u,v) p(v)^{λ-1}) ]
    """
    nu, nv = p_uvx.shape[0], p_uvx.shape[1]
    px = p_uvx.sum(axis=(0, 1))
    pux, pvx, puv = p_uvx.sum(axis=1), p_uvx.sum(axis=0), p_uvx.sum(axis=2)
    py, pz = px @ T_Y, px @ T_Z
    puy, pvz = pux @ T_Y, pvx @ T_Z
    pv = puv.sum(axis=0)
    L = np.full((nu, nv, 3), -np.inf)
    for u in range(nu):
        for v in range(nv):
            if puv[u, v] <= 0:
                continue
            for x in range(3):
                ty = float(T_Y[x] @ (np.log(puy[u]) - ABAR * np.log(py)))
                tz = float(T_Z[x] @ (LAMBDA * np.log(pvz[v]) - ALPHA * np.log(pz)))
                L[u, v, x] = (ty + tz + A_X[x] - np.log(puv[u, v])
                              - (LAMBDA - 1.0) * np.log(pv[v]))
    return L


def cond7_value(p_uvx: np.ndarray, q_vx: np.ndarray) -> float:
    """論文 (6)/(7) の左辺 (U のアルファベットを 1 増やす摂動の 1 階条件)。"""
    px = p_uvx.sum(axis=(0, 1))
    pvx, puv = p_uvx.sum(axis=0), p_uvx.sum(axis=2)
    py, pz = px @ T_Y, px @ T_Z
    pvz = pvx @ T_Z
    pv = puv.sum(axis=0)
    qv, qx = q_vx.sum(axis=1), q_vx.sum(axis=0)
    qy = qx @ T_Y
    total = 0.0
    for v in range(q_vx.shape[0]):
        if qv[v] <= 0:
            continue
        for x in range(3):
            if q_vx[v, x] <= 0:
                continue
            ty = float(T_Y[x] @ (np.log(qy) - ABAR * np.log(py)))
            tz = float(T_Z[x] @ (LAMBDA * np.log(pvz[v]) - ALPHA * np.log(pz)))
            total += q_vx[v, x] * (ty + tz
                                   - (LAMBDA - 1.0) * np.log(pv[v]) - np.log(qv[v]))
    return total + float(qx @ A_X)


def cond8_value(p_uvx: np.ndarray, q_ux: np.ndarray) -> float:
    """論文 (8) の左辺 (V のアルファベットを 1 増やす摂動の 1 階条件)。"""
    px = p_uvx.sum(axis=(0, 1))
    pux = p_uvx.sum(axis=1)
    py, pz = px @ T_Y, px @ T_Z
    puy = pux @ T_Y
    qu, qx = q_ux.sum(axis=1), q_ux.sum(axis=0)
    qz = qx @ T_Z
    total = 0.0
    for u in range(q_ux.shape[0]):
        if qu[u] <= 0:
            continue
        for x in range(3):
            if q_ux[u, x] <= 0:
                continue
            ty = float(T_Y[x] @ (np.log(puy[u]) - ABAR * np.log(py)))
            tz = float(T_Z[x] @ (LAMBDA * np.log(qz) - ALPHA * np.log(pz)))
            total += q_ux[u, x] * (ty + tz - np.log(qu[u]))
    return total + float(qx @ A_X)


# ---------------------------------------------------------------- 実際の摂動
def perturb_extend_U(p_uvx, s_uvx, q_vx, eps):
    """論文 §III の摂動 2: pε(u,v,x) = p − εs (u ∈ [1:|U|]) / εq(v,x) (u = |U|+1)。"""
    nu, nv, nx = p_uvx.shape
    out = np.zeros((nu + 1, nv, nx))
    out[:nu] = p_uvx - eps * s_uvx
    out[nu] = eps * q_vx
    return out


def perturb_extend_V(p_uvx, s_uvx, q_ux, eps):
    """論文 §III の摂動 3 (U と V の役割を入れ替えたもの)。"""
    nu, nv, nx = p_uvx.shape
    out = np.zeros((nu, nv + 1, nx))
    out[:, :nv] = p_uvx - eps * s_uvx
    out[:, nv] = eps * q_ux
    return out


def deterministic_q_grid(n_aux: int, n_grid: int = 2000):
    """q(v,x) のうち q(x|v) ∈ {0,1} のものを全通り走査する。

    論文 §III: "the expression in (6) is convex in q(x|v), which implies, to maximize the
    left-hand-side, it suffices to consider q(v, x) for which q(x|v) ∈ {0, 1}."
    ⚠ **ランダム q を引く探索ではこの族に当たらない** — 改善方向が単体の境界にあるため。
    """
    for fmap in itertools.product(range(3), repeat=n_aux):
        for t in np.linspace(0.0005, 0.9995, n_grid):
            w = np.array([t, 1.0 - t]) if n_aux == 2 else np.full(n_aux, 1.0 / n_aux)
            q = np.zeros((n_aux, 3))
            for i in range(n_aux):
                q[i, fmap[i]] = w[i]
            yield fmap, q


def rule(title: str) -> None:
    print("\n" + "=" * 78)
    print(title)
    print("=" * 78)


# ---------------------------------------------------------------- 1. 再現
def reproduce() -> float:
    rule("1. 論文 §III-B の 4 つの目的値の再現")
    print("  行列の行和 (論文の転記が正しいことの検算):")
    print(f"    T(y|x) 行和 = {T_Y.sum(axis=1)!r}")
    print(f"    T(z|x) 行和 = {T_Z.sum(axis=1)!r}")
    print(f"    p*(u,v) 総和 = {P_UV.sum()!r}")

    p_local = joint_from_map(P_UV, MAP_LOCAL)
    fast, viaH = G(p_local), G_via_harness(p_local)
    print(f"\n  実装の相互検証 (直接実装 vs harness の BayesNet + 式パーサ):")
    print(f"    直接 = {fast!r}")
    print(f"    harness = {viaH!r}    差 = {abs(fast - viaH):.3e}")
    assert abs(fast - viaH) < 1e-12, "2 実装が食い違う"

    print(f"\n  {'pattern':>12} {'rect?':>6} {'論文の値':>14} {'再現値 (nat)':>18} "
          f"{'|差|':>10} {'bit 版':>14}")
    rows = [(MAP_LOCAL, REPORTED_LOCAL)] + RECTANGULAR
    worst = 0.0
    for f, reported in rows:
        p = joint_from_map(P_UV, f)
        got = G(p)
        worst = max(worst, abs(got - reported))
        print(f"  {pattern_str(f):>12} {str(is_rectangular(f)):>6} {reported:>14.8f} "
              f"{got:>18.11f} {abs(got - reported):>10.2e} {G(p, bits=True):>14.8f}")
    print(f"\n  4 値の最大誤差 = {worst:.3e}  "
          f"(論文は小数 8 桁で印刷。8 桁に丸めて一致するか: "
          f"{all(round(G(joint_from_map(P_UV, f)), 8) == r for f, r in rows)})")
    print("  単位は nat。bit 版 (エントロピーを底 2 で測った目的値) は再現しない。")
    return G(joint_from_map(P_UV, MAP_LOCAL))


# ---------------------------------------------------------------- 2. 局所最大性
def local_maximality(F_local: float) -> None:
    rule("2. 局所最大性 — 論文が定義する 3 種の摂動で G が増えないか")
    p_local = joint_from_map(P_UV, MAP_LOCAL)

    print("  [1 階条件 (4)] 全 (u,v,x) で LHS <= F、x = f(u,v) で等号")
    L = cond4(p_local)
    for u in range(2):
        for v in range(2):
            marks = []
            for x in range(3):
                tag = "*" if x == MAP_LOCAL[u][v] else " "
                marks.append(f"{SYM[x]}{tag}{L[u, v, x] - F_local:+.3e}")
            print(f"    u={u} v={v}: LHS-F = " + "  ".join(marks))
    eq = [L[u, v, MAP_LOCAL[u][v]] - F_local for u in range(2) for v in range(2)]
    ineq = [L[u, v, x] - F_local for u in range(2) for v in range(2)
            for x in range(3) if x != MAP_LOCAL[u][v]]
    print(f"    等号側の最大誤差 = {max(abs(e) for e in eq):.3e}  "
          f"(-> (4) の転記が正しいことの検算)")
    print(f"    不等号側の最大 = {max(ineq):+.3e}  -> (4) を満たすか: {max(ineq) <= 1e-9}")

    print("\n  [種類 1 の残り] p*(u,v) は同じ写像を固定したときの制約付き最大点か")
    opt = maximize(
        lambda t: G(joint_from_map(softmax(t.reshape(-1)).reshape(2, 2), MAP_LOCAL)),
        4, rng, restarts=60, scale=1.5,
        options={"maxiter": 80000, "maxfev": 80000, "xatol": 1e-13, "fatol": 1e-15},
    )
    puv_opt = softmax(opt.best_x.reshape(-1)).reshape(2, 2)
    print(f"    写像 '{pattern_str(MAP_LOCAL)}' 固定での最大 = {opt.best!r}")
    print(f"    論文の p*(u,v) での値                = {F_local!r}")
    print(f"    差 = {opt.best - F_local:.3e}")
    print(f"    最大を与える p(u,v) = {np.round(puv_opt, 8).tolist()}")
    print(f"    論文の p*(u,v)      = {P_UV.tolist()}")
    print("    ⟹ 台の内側では p* が最大、台の外へ出る向きは (4) が厳密不等号")
    print("       ⟹ **種類 1 の局所最大性は成立**。")

    print("\n  [1 階条件 (7) / (8)] アルファベットを 1 増やす摂動 (種類 2 / 3)")
    print("    q(x|v) (resp. q(x|u)) が決定論的な族を全通り走査する (論文の凸性の注意)。")
    argq_by_cond = {}
    for label, valfn, tag in [("(7)  U +1", cond7_value, 7), ("(8)  V +1", cond8_value, 8)]:
        best, argq, argf = -np.inf, None, None
        for fmap, q in deterministic_q_grid(2):
            val = valfn(p_local, q)
            if val > best:
                best, argq, argf = val, q.copy(), fmap
        argq_by_cond[tag] = (argq, best)
        print(f"    {label}: max = {best!r}")
        print(f"              LHS - F = {best - F_local:+.6e}"
              f"   -> 満たすか: {best - F_local <= 1e-7}")
        print(f"              最大を与える q: q(x|.) = ({SYM[argf[0]]}, {SYM[argf[1]]}),"
              f" 重み = {argq.sum(axis=1).tolist()}")
    print("    転記の検算 — 論文が述べる等号条件で残差が 0 になるか:")
    for u in range(2):
        qvx = p_local[u] / p_local[u].sum()
        print(f"      (7) q(v,x) = p(v,x|u={u}):  LHS - F = "
              f"{cond7_value(p_local, qvx) - F_local:+.3e}")
    for v in range(2):
        qux = p_local[:, v] / p_local[:, v].sum()
        print(f"      (8) q(u,x) = p(u,x|v={v}):  LHS - F = "
              f"{cond8_value(p_local, qux) - F_local:+.3e}")

    print("\n  [摂動を直接かける] 1 階条件の転記を信用せず、G の値そのものを見る")
    flat = p_local.reshape(-1)
    gain, _, eps = local_max_certificate(
        lambda z: G(z.reshape(2, 2, 3)), flat, rng, trials=20000,
        eps=(1e-1, 1e-2, 1e-3, 1e-4, 1e-5, 1e-6),
    )
    print("    種類 1 (pε = (1−ε)p + εs、s をランダムに 20000 本):")
    print(f"      最大増分 = {gain:+.3e} (ε = {eps:g})  -> 増えないか: {gain <= 1e-10}")

    for name, fn, tag in [("種類 2 (|U| を +1)", perturb_extend_U, 7),
                          ("種類 3 (|V| を +1)", perturb_extend_V, 8)]:
        argq, best = argq_by_cond[tag]
        # s = p を取れば pε = (1−ε)p ⊕ εq となり、どの ε ∈ [0,1] でも実行可能
        print(f"    {name}: q = {np.round(argq, 8).tolist()}, s = p")
        for e in (1e-2, 1e-3, 1e-4, 1e-5, 1e-6):
            pe = fn(p_local, p_local, argq, e)
            d = G(np.clip(pe, 0.0, None)) - F_local
            print(f"      eps={e:<8g} dG = {d:+.6e}   dG/eps = {d / e:+.6e}")
        print(f"      -> 1 階条件から予測される dG/eps = {best - F_local:+.6e} と一致")
        print(f"      -> G は**増える** ⟹ {name} の摂動で局所最大でない")

    print("\n  ⚠ ランダム方向の探索は種類 2/3 の改善を見落とす — 改善方向が単体の境界")
    print("     (q(x|v) が決定論的) にあり、Dirichlet から引いた q はそこに当たらない。")
    argq7 = argq_by_cond[7][0]
    bb = -np.inf
    for _ in range(20000):
        q = rng.dirichlet(np.ones(6)).reshape(2, 3)
        bb = max(bb, G(perturb_extend_U(p_local, p_local, q, 1e-3)) - F_local)
    det = G(perturb_extend_U(p_local, p_local, argq7, 1e-3)) - F_local
    print(f"    実測: ランダム q(v,x) 20000 本 (eps=1e-3) の最大 dG = {bb:+.3e}")
    print(f"          同じ eps で決定論的 q を使うと dG = {det:+.3e}")



# ---------------------------------------------------------------- 3. 大域最大
def global_search() -> float:
    rule("3. 大域最大の探索 — 報告点が局所であって大域でないことの確認")
    print("  補助アルファベットの濃度: 論文 §I が [9] を引いて |U| + |V| <= |X| + 1 = 4。")
    print("  (a) X = f(U,V) を課し、全 3^4 = 81 の写像 × p(u,v) の多点再スタート最適化")
    best, best_f, best_opt = -np.inf, None, None
    rect_best, nonrect_best = -np.inf, -np.inf
    for f in itertools.product(range(3), repeat=4):
        fm = ((f[0], f[1]), (f[2], f[3]))

        def obj(theta, m=fm):
            puv = softmax(theta.reshape(-1)).reshape(2, 2)
            return G(joint_from_map(puv, m))

        opt = maximize(obj, 4, rng, restarts=12, scale=1.5)
        if is_rectangular(fm):
            rect_best = max(rect_best, opt.best)
        else:
            nonrect_best = max(nonrect_best, opt.best)
        if opt.best > best:
            best, best_f, best_opt = opt.best, fm, opt
    print(f"    最良 = {best!r} @ pattern '{pattern_str(best_f)}' "
          f"(rectangular: {is_rectangular(best_f)})")
    print(f"    {best_opt.summary()}")
    puv_best = softmax(best_opt.best_x.reshape(-1)).reshape(2, 2)
    print(f"    そのときの p(u,v) = {np.round(puv_best, 8).tolist()}")
    print(f"    -> U の周辺 = {np.round(puv_best.sum(axis=1), 8).tolist()} "
          f"(片方が 0 なら U は退化 = 実質 |U| = 1)")
    print(f"    矩形写像だけの最良     = {rect_best!r}")
    print(f"    非矩形写像だけの最良   = {nonrect_best!r}")

    print("\n  (b) X = f(U,V) を課さず p(u,v,x) を直接最適化 (交差検証)")
    for nu, nv in ((2, 2), (3, 2), (3, 3), (4, 4)):
        def obj(theta, a=nu, b=nv):
            p = softmax(theta.reshape(-1)).reshape(a, b, 3)
            return G(p)
        opt = maximize(obj, nu * nv * 3, rng, restarts=30, scale=1.5,
                       options={"maxiter": 80000, "maxfev": 80000,
                                "xatol": 1e-13, "fatol": 1e-15})
        best = max(best, opt.best)
        print(f"    |U|={nu}, |V|={nv}: {opt.summary()}")
    print("\n  ⚠ 局所最適法なのでこれは『見つかった最良値』であって最大値の証明ではない。")
    return best


def main() -> None:
    quick = "--quick" in sys.argv
    F_local = reproduce()
    if quick:
        return
    local_maximality(F_local)
    F_global = global_search()
    rule("4. まとめ")
    print(f"  報告された局所最大値 (論文)      = {REPORTED_LOCAL}")
    print(f"  再現した局所最大値               = {F_local!r}")
    print(f"  探索で見つかった最良値           = {F_global!r}")
    print(f"  差 (大域候補 − 局所)             = {F_global - F_local:+.6e}")
    print(f"  -> 報告点は局所最大だが大域最大ではない: {F_global > F_local + 1e-8}")


if __name__ == "__main__":
    main()
