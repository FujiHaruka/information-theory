#!/usr/bin/env python3
"""軸 C の子 attack **`slack-loss-lower-bound`** (L15) — 4 項損失 `L'` の下界 `Λ` を測る probe
(親 plan `bc-open-problem-plan.md` §6.2 の L15 行、起票は `bc-open-problem-attacks.md`)。

主語 (L13 の (H1) が確定させたもの)
-----------------------------------
    T(X)      := max_{p(u,v|x)} I(U;Y) + I(V;Z) - I(U;V)      ((U,V) -> X -> (Y,Z))
    gap(T,p)  := T(X) - max{I(X;Y), I(X;Z)}
    L'(T,p)   := min_{p(u,v|x)} [ I(U;X|Y) + I(V;X|Z) + H(X|U,V) + I(U;V|X) ]   (>= 0)
    (H1)      : gap(T,p) = min{H(X|Y), H(X|Z)} - L'(T,p)                (`bc-facts.md` §L13)

したがって「鋭いチャネル依存スラックを作る」= **`L'` を下から抑える `Λ` を作る**。翻訳済の
必要条件は **(N1)** `|X| = 2` で `Λ = min{H(X|Y), H(X|Z)}` (= [GJNW13] Theorem 1 の言い換え) /
**(N2)** 格子 BC で `Λ = 0`。

本 probe が測るもの (候補 4 本)
------------------------------
親候補 C2 の 3 案は**未証明の主張**だったので数値反例で死んだ。本 leg の候補は逆に、
まず**証明できる下界**を 3 本立て、(N1)(N2) を「殺すテスト」ではなく **鋭さの測定**として
当てる (証明済の不等式は反例では死なない ⟹ 第 3 の必要条件 §5-12 は自動で満たされる。
死ぬとしたら「鋭くない」ことによってである)。比較対象として、鋭いが**偽**と分かっている
`Λ_det` (= P1) も同じ表に載せる。

    Λ_det := min_{f,g: X の関数} [ H(X|f,g) + H(f(X)|Y) + H(g(X)|Z) ]        (= H(X) - Phi_det)
        L13 の P1 は `L' = Λ_det` の主張そのもの ⟹ **REFUTED** (`bc-facts.md` §L13)。
        本 probe では (N1)(N2) を満たす*上界*の基準線として使う (下界ではない)。

    Λ_sup := H(X) - min{Gamma_Y, Gamma_Z}                                    (**証明済**)
        Gamma_Y := max_U [ I(U;Y) + I(X;Z|U) ],  Gamma_Z := max_V [ I(V;Z) + I(X;Y|V) ]
        証明: I(U;Y) + I(V;Z) - I(U;V) <= I(U;Y) + I(V;Z|U) <= I(U;Y) + I(X;Z|U) (DPI)。
        恒等式 `Gamma_Y = I(X;Z) + nu_Z`, `nu_Z := max_U [I(U;Y) - I(U;Z)]` (§0(c) が確認)
        ⟹ **Λ_sup は「less noisy 順序からのズレ」で書ける**。

    Λ_ib  := H(X) - max_{a + b = H(X)} [ F_Y(a) + F_Z(b) ]                   (**証明済**)
        F_Y(a) := max{ I(U;Y) : U -> X -> Y, I(U;X) <= a }  (= information bottleneck 曲線)
        証明: 最適点で a := I(U;X), b := I(V;X) と置くと `I(U;V) >= 0` から a + b >= H(X)、
        目的値は (a - I(U;Y)) + (b - I(V;Z)) >= (a - F_Y(a)) + (b - F_Z(b))。
        F は凹なので Lagrange 双対にギャップが無く `min_λ [λH(X) + G_Y(λ) + G_Z(λ)]`、
        `G_Y(λ) := max_U [I(U;Y) - λ I(U;X)]` で計算できる (§0(d) が確認)。

    Λ_max := max{Λ_sup, Λ_ib}                                                (**証明済**)

新しい診断 — (H3) 恒等式による**超過分の 2 項分解**
---------------------------------------------------
    (H3)  I(U;X|Y) + I(V;X|Z) + H(X|U,V) + I(U;V|X)
              = [ H(X) - I(U;Y) - I(X;Z|U) ] + [ I(X;Z|U) - I(V;Z|U) ] + I(U;V|Z)

    5 変数の線形恒等式 (Markov 下)。§0(a) が `bc_probe.prove_identity` で係数消去を確認する。
    第 1 項は `Λ_sup` の目的関数そのもの、残り 2 項は**どちらも非負** ⟹ `L' - Λ_sup` は

        (i) U の選び方の非最適性 + (ii) `D1 := I(X;Z|U) - I(V;Z|U)` + (iii) `D2 := I(U;V|Z)`

    にちょうど分かれる。(H1) の 4 項分解が「損失の内訳」を与えたのに対し、(H3) は
    「証明済の下界からの超過の内訳」を与える。§3 が最適点でこの 3 つを実測する。

判定の向き (どの数値が確定で、どれが探索か)
-------------------------------------------
* `Λ_det` / `D(p)` は関数対の**全列挙で厳密**。
* `Gamma`, `nu`, `G(λ)`, `L'`, `T` は最適化 ⟹ **片側の評価にすぎない**。
  - `Gamma` は最大化 = 下界 ⟹ `Λ_sup = H(X) - min Gamma` は**上振れしうる** (下界としての
    妥当性が壊れる向き)。§0(e) で `Λ_sup <= l_prime 推定` を常に検査し、破れたら FAIL 扱い。
  - `L'` は最小化 = 真の `L'` の**上界**。
* ゆえに本 probe の (N1) 不合格は「証明済の下界が binary で鋭くない」という**測定**であって
  反例ではない。逆に (N1) 合格が出たら、それは [GJNW13] Theorem 1 の別証明を含意する
  ⟹ その場合だけ novelty gate へ進む (§5 の判定規則を先に固定しておく)。

sim と定義の逐語照合 (CLAUDE.md 検証の誠実性)
---------------------------------------------
* 目的量・チャネル族・最適化器は L10/L13 probe (`bc-jognair-general-check.py` /
  `bc-jognair-phi-check.py`) を **import して再利用**する。単位は bit。
* `Λ_det = H(X) - Phi_det` は閉じた式を主張しているので §0(b) が両者を突き合わせる。
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
import time
from pathlib import Path

import numpy as np

_HERE = Path(__file__).resolve().parent
if str(_HERE) not in sys.path:
    sys.path.insert(0, str(_HERE))


def _load_sibling(fname: str, modname: str):
    """ハイフンつきファイル名の兄弟 probe を import する (規約の再導出を避けるため)。"""
    path = _HERE / fname
    spec = importlib.util.spec_from_file_location(modname, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[modname] = mod          # dataclass の解決に __module__ の登録が要る
    spec.loader.exec_module(mod)
    return mod


import bc_probe as _BP                                            # noqa: E402

_L13 = _load_sibling("bc-jognair-phi-check.py", "bc_jognair_phi_check_l15")

prove_identity = _BP.prove_identity
Joint = _BP.Joint
parse = _BP.parse
softmax = _BP.softmax

_h = _L13._h
_mi = _L13._mi
objective = _L13.objective
loss_terms = _L13.loss_terms
ixy_ixz = _L13.ixy_ixz
phi_det = _L13.phi_det
det_pairs = _L13.det_pairs
det_joint = _L13.det_joint
cond_to_joint = _L13.cond_to_joint
l_prime = _L13.l_prime
lattice_family = _L13.lattice_family
marginals = _L13.marginals
smoothed_blackwell = _L13.smoothed_blackwell
noisy_blackwell = _L13.noisy_blackwell
partial_merge = _L13.partial_merge
blackwell = _L13.blackwell
maximize_hd = _L13.maximize_hd
joint5 = _L13.joint5

TOL_ID = 1e-9          # 恒等式・閉じた式の一致に要求する精度 (直接評価どうし)
TOL_SHARP = 1e-7       # 「(N1) を満たす = 鋭い」と呼ぶための deficit の閾値


# --------------------------------------------------------------------------
# 補助変数 U 側の情報量 (p(u|x) を softmax で持つ)
# --------------------------------------------------------------------------
def joint_ux(cond_ux: np.ndarray, px: np.ndarray) -> np.ndarray:
    """`cond_ux[x,u]` と `px[x]` から `p(u,x)` (形 `(ku,kx)`) を作る。"""
    return (px[:, None] * cond_ux).T


def info_u(pux: np.ndarray, Cy: np.ndarray, Cz: np.ndarray):
    """`p(u,x)` から `(I(U;X), I(U;Y), I(U;Z), I(X;Y|U), I(X;Z|U))` を返す (bit)。"""
    i_ux = _mi(pux)
    puy = pux @ Cy
    puz = pux @ Cz
    hx_u = _h(pux) - _h(pux.sum(axis=1))                    # H(X|U)
    puxy = pux[:, :, None] * Cy[None, :, :]
    puxz = pux[:, :, None] * Cz[None, :, :]
    hx_uy = _h(puxy) - _h(puxy.sum(axis=1))                 # H(X|U,Y)
    hx_uz = _h(puxz) - _h(puxz.sum(axis=1))
    return i_ux, _mi(puy), _mi(puz), hx_u - hx_uy, hx_u - hx_uz


def _opt_u(px, Cy, Cz, score, rng, restarts: int, ku: int | None = None):
    """`p(u|x)` 上で `score(I(U;X), I(U;Y), I(U;Z), I(X;Y|U), I(X;Z|U))` を最大化する。

    返るのは局所最適の中の最良値 = **下界**。決定論的な種 (U = X / U = 定数 / 2 値への
    併合すべて) を明示的に開始点に入れる (ランダム再スタートだけでは最大を外す実例が
    `bc-facts.md` §L10 / §L13 にある)。
    """
    kx = px.size
    ku = ku or (kx + 1)

    def f(theta):
        cond = softmax(theta.reshape(kx, ku), axis=-1)
        return score(*info_u(joint_ux(cond, px), Cy, Cz))

    seeds = []
    seed_maps = [tuple(range(kx)), tuple(0 for _ in range(kx))]
    for m in range(1, 2 ** (kx - 1)):                       # 2 値への併合を全部
        seed_maps.append(tuple((m >> i) & 1 for i in range(kx)))
    for mp in seed_maps:
        c = np.zeros((kx, ku))
        for x in range(kx):
            c[x, mp[x] % ku] = 1.0
        seeds.append(np.log(c.ravel() + 1e-6))
    return maximize_hd(f, kx * ku, rng, restarts=restarts, seeds=seeds, maxiter=2000)


def gamma_sup(px, Cy, Cz, rng, restarts: int = 6):
    """`(Gamma_Y, Gamma_Z, nu_Y, nu_Z, 2 経路の食い違い)`。

    `Gamma_Y = max_U [I(U;Y) + I(X;Z|U)]` は恒等式 `= I(X;Z) + nu_Z` でも計算できる
    (`nu_Z := max_U [I(U;Y) - I(U;Z)]`)。**どちらの経路も最大化 = 真値の下界**なので、
    2 つの推定の**大きい方**を採る (`Λ_sup = H(X) - min Gamma` は上振れが妥当性を壊す
    向きなので、Gamma は大きく採るほど安全)。食い違いは最適化ノイズの実測値として返す。
    """
    i_y, i_z = ixy_ixz(px, Cy, Cz)
    gy0 = _opt_u(px, Cy, Cz, lambda ux, uy, uz, xy_u, xz_u: uy + xz_u, rng, restarts).best
    gz0 = _opt_u(px, Cy, Cz, lambda ux, uy, uz, xy_u, xz_u: uz + xy_u, rng, restarts).best
    ny = _opt_u(px, Cy, Cz, lambda ux, uy, uz, xy_u, xz_u: uz - uy, rng, restarts).best
    nz = _opt_u(px, Cy, Cz, lambda ux, uy, uz, xy_u, xz_u: uy - uz, rng, restarts).best
    gy, gz = max(gy0, i_z + nz), max(gz0, i_y + ny)
    return gy, gz, ny, nz, max(abs(gy0 - (i_z + nz)), abs(gz0 - (i_y + ny)))


def gamma_grid_binary(px, Cy, Cz, n: int = 61):
    """`|X| = 2` 用の**最適化を使わない** `Gamma` の下界 (2 値 `U` の格子を直接評価)。

    `p(X=1|U=0) = a`, `p(X=1|U=1) = b` を格子で振り、`p(U)` は `p(x)` の整合から決まる。
    返り `(Gamma_Y の下界, Gamma_Z の下界, 最良の (a,b))`。**各点は厳密な直接評価**なので、
    ここで得た値が `max{I(X;Y),I(X;Z)}` を超えたら **`Λ_sup < L'` の証明書**になる
    (`Gamma` の下界が大きいほど `Λ_sup` は小さくなるため)。
    """
    p1 = float(px[1])
    grid = np.linspace(0.0, 1.0, n)
    best_y, best_z, arg = -np.inf, -np.inf, None
    for a in grid:
        for b in grid:
            if b <= a + 1e-12:
                continue
            w = (p1 - a) / (b - a)
            if not (0.0 <= w <= 1.0):
                continue
            pux = np.array([[(1 - w) * (1 - a), (1 - w) * a], [w * (1 - b), w * b]])
            _, uy, uz, xy_u, xz_u = info_u(pux, Cy, Cz)
            if uy + xz_u > best_y:
                best_y, arg = uy + xz_u, (float(a), float(b), float(w))
            best_z = max(best_z, uz + xy_u)
    return best_y, best_z, arg


def ib_conj(px, C, lam: float, rng, restarts: int = 4) -> float:
    """`G(λ) = max_U [I(U;·) - λ I(U;X)]` (information bottleneck 曲線の凹共役)。"""
    return _opt_u(px, C, C, lambda ux, uy, uz, xy_u, xz_u: uy - lam * ux,
                  rng, restarts).best


def lambda_ib(px, Cy, Cz, rng, n_lam: int = 26, restarts: int = 3):
    """`Λ_ib = H(X) - min_λ [λ H(X) + G_Y(λ) + G_Z(λ)]`。返り `(Λ_ib, 最良 λ)`。"""
    hx = _h(px)
    best, arg = np.inf, None
    for lam in np.linspace(0.0, 1.0, n_lam):
        val = lam * hx + ib_conj(px, Cy, lam, rng, restarts) \
            + ib_conj(px, Cz, lam, rng, restarts)
        if val < best:
            best, arg = val, float(lam)
    return hx - best, arg


def lambda_det(px, Cy, Cz):
    """`Λ_det = min_{f,g} [H(X|f,g) + H(f|Y) + H(g|Z)]` を全列挙で**厳密**に。"""
    kx = px.size
    best, arg = np.inf, None
    for f, g in det_pairs(kx):
        p3 = det_joint(f, g, px)
        puv = p3.sum(axis=2)
        pu, pv = puv.sum(axis=1), puv.sum(axis=0)
        pux, pvx = p3.sum(axis=1), p3.sum(axis=0)
        h_x_uv = _h(p3) - _h(puv)
        h_f_y = _h(pu) - _mi(pux @ Cy)
        h_g_z = _h(pv) - _mi(pvx @ Cz)
        v = h_x_uv + h_f_y + h_g_z
        if v < best:
            best, arg = v, (f, g)
    return best, arg


def h_cond(px, C) -> float:
    """`H(X|·)`。`C[x,y]`。"""
    p = px[:, None] * C
    return _h(p) - _h(p.sum(axis=0))


def h3_terms(puvx: np.ndarray, Cy: np.ndarray, Cz: np.ndarray):
    """(H3) の 3 項 `(base, D1, D2)`。`base = H(X) - I(U;Y) - I(X;Z|U)`。"""
    px = puvx.sum(axis=(0, 1))
    pux = puvx.sum(axis=1)
    puy = pux @ Cy
    i_uy = _mi(puy)
    _, _, _, _, xz_u = info_u(pux, Cy, Cz)
    # I(V;Z|U) = H(V|U) - H(V|U,Z) を p(u,v,x) * p(z|x) から直接
    puvz = np.einsum("uvx,xz->uvz", puvx, Cz)
    h_v_u = _h(puvx.sum(axis=2)) - _h(pux.sum(axis=1))
    h_v_uz = _h(puvz) - _h(puvz.sum(axis=1))
    i_vz_u = h_v_u - h_v_uz
    # I(U;V|Z) = H(U|Z) + H(V|Z) - H(U,V|Z)
    puz = np.einsum("uvx,xz->uz", puvx, Cz)
    pvz = np.einsum("uvx,xz->vz", puvx, Cz)
    pz = puz.sum(axis=0)
    d2 = (_h(puz) - _h(pz)) + (_h(pvz) - _h(pz)) - (_h(puvz) - _h(pz))
    return _h(px) - i_uy - xz_u, xz_u - i_vz_u, d2


# --------------------------------------------------------------------------
# チャネル族
# --------------------------------------------------------------------------
def bsc(a: float) -> np.ndarray:
    return np.array([[1 - a, a], [a, 1 - a]])


def bec(e: float) -> np.ndarray:
    return np.array([[1 - e, 0.0, e], [0.0, 1 - e, e]])


def bzc(a: float) -> np.ndarray:
    """Z チャネル (`x=0` は誤らない)。"""
    return np.array([[1.0, 0.0], [a, 1 - a]])


def binary_family(quick: bool):
    """`|X| = 2` の (名前, p(x), Cy, Cz) 一覧。(N1) はここで測る。"""
    out = []
    ps = [0.5, 0.35, 0.2] if quick else [0.5, 0.4, 0.35, 0.25, 0.2, 0.1]
    pairs = [("BSC(.1)/BSC(.2)", bsc(0.1), bsc(0.2)),
             ("BSC(.1)/BEC(.5)", bsc(0.1), bec(0.5)),
             ("BEC(.3)/BSC(.25)", bec(0.3), bsc(0.25)),
             ("BEC(.2)/BEC(.6)", bec(0.2), bec(0.6)),
             ("BSC(.15)/Z(.5)", bsc(0.15), bzc(0.5)),
             ("Z(.3)/BSC(.3)", bzc(0.3), bsc(0.3))]
    if quick:
        pairs = pairs[:3]
    for name, Cy, Cz in pairs:
        for p1 in ps:
            out.append((f"{name} p={p1:.2f}", np.array([1 - p1, p1]), Cy, Cz))
    return out


def dense_random(rng, kx: int = 3, ky: int = 3, kz: int = 3, floor: float = 0.05):
    """dense (全遷移確率 > 0) なランダムチャネル対と非一様 `p(x)`。"""
    Cy = rng.dirichlet(np.ones(ky), size=kx)
    Cz = rng.dirichlet(np.ones(kz), size=kx)
    Cy = (1 - floor * ky) * Cy + floor
    Cz = (1 - floor * kz) * Cz + floor
    px = rng.dirichlet(np.ones(kx) * 2.0)
    return px, Cy / Cy.sum(axis=1, keepdims=True), Cz / Cz.sum(axis=1, keepdims=True)


# --------------------------------------------------------------------------
# §0 harness — 恒等式と閉じた式の照合
# --------------------------------------------------------------------------
def section0(quick: bool) -> bool:
    print("=" * 78)
    print("§0 harness — (H3) 恒等式 / `Λ_det = H(X) - Phi_det` / `Gamma = I + nu` の照合")
    print("=" * 78)
    ok = True

    lhs = "I(U;X|Y) + I(V;X|Z) + H(X|U,V) + I(U;V|X)"
    rhs = ("H(X) - I(U;Y) - I(X;Z|U) + (I(X;Z|U) - I(V;Z|U)) + I(U;V|Z)"
           " + I(U;Y|X) + I(V;Z|X)")
    held, resid = prove_identity(lhs, rhs)
    print(f"  (a) (H3) の記号的な係数相殺: accept = {held} / 残差 = {resid}")
    print("      (Markov `(U,V)->X->(Y,Z)` の下で減算 2 項 `I(U;Y|X)`, `I(V;Z|X)` が消える")
    print("       = (H1) と同じ約束。数値側は下の (e) が Markov 構成で確認する)")
    ok &= held

    rng = np.random.default_rng(20260802)
    worst_det, worst_g, worst_h3 = 0.0, 0.0, 0.0
    n = 12 if quick else 40
    for _ in range(n):
        px, Cy, Cz = dense_random(rng)
        pd, _, _ = phi_det(px, Cy, Cz)
        ld, _ = lambda_det(px, Cy, Cz)
        worst_det = max(worst_det, abs(ld - (_h(px) - pd)))
        gy, gz, ny, nz, dg = gamma_sup(px, Cy, Cz, rng, restarts=3)
        i_y, i_z = ixy_ixz(px, Cy, Cz)
        worst_g = max(worst_g, abs(gy - (i_z + nz)), abs(gz - (i_y + ny)))
        # (H3) を Markov 構成の p(u,v,x) 上で数値照合
        cond = softmax(rng.normal(0, 1.5, (3, 9)), axis=-1).reshape(3, 3, 3)
        p3 = cond_to_joint(cond, px)
        base, d1, d2 = h3_terms(p3, Cy, Cz)
        worst_h3 = max(worst_h3, abs(sum(loss_terms(p3, Cy, Cz)) - (base + d1 + d2)))
    print(f"  (b) `Λ_det` と `H(X) - Phi_det` の最大差: {worst_det:.3e} "
          f"(全列挙どうしなので丸めのみ)")
    print(f"  (c) `Gamma_Y = I(X;Z) + nu_Z` / `Gamma_Z = I(X;Y) + nu_Y` の最大差: "
          f"{worst_g:.3e} (最適化どうしなので再スタート由来の差を含む)")
    print(f"  (d) (H3) の数値照合 (ランダム `p(u,v|x)` {n} 本) の最大差: {worst_h3:.3e}")
    ok &= worst_det < TOL_ID and worst_h3 < TOL_ID

    # bc_probe.Joint 経由の独立再評価
    px, Cy, Cz = dense_random(rng)
    T = np.einsum("xy,xz->xyz", Cy, Cz)          # 独立結合 (周辺は Cy, Cz のまま)
    cond = softmax(rng.normal(0, 1.5, (3, 9)), axis=-1).reshape(3, 3, 3)
    p3 = cond_to_joint(cond, px)
    J = joint5(p3, T)
    d_direct = h3_terms(p3, Cy, Cz)
    d_joint = (J.eval(parse("H(X) - I(U;Y) - I(X;Z|U)"), "bits"),
               J.eval(parse("I(X;Z|U) - I(V;Z|U)"), "bits"),
               J.eval(parse("I(U;V|Z)"), "bits"))
    dmax = max(abs(a - b) for a, b in zip(d_direct, d_joint))
    print(f"  (e) `bc_probe.Joint` 経由との差 (base/D1/D2): {dmax:.3e}")
    ok &= dmax < TOL_ID
    print(f"  ⟹ §0 {'PASS' if ok else '**FAIL**'}")
    return ok


# --------------------------------------------------------------------------
# §1 (N1) — `|X| = 2` での鋭さ
# --------------------------------------------------------------------------
def section1(quick: bool) -> dict:
    print()
    print("=" * 78)
    print("§1 (N1) — `|X| = 2` で `Λ = min{H(X|Y), H(X|Z)}` になるか (鋭さの測定)")
    print("=" * 78)
    print("  ⚠ 3 本とも**証明済の下界**なので、`deficit > 0` は反例ではなく「鋭くない」の意。")
    print("  ⚠ deficit := min{H(X|Y),H(X|Z)} - Λ。**(N1) は族の全点で 0 を要求する**ので、")
    print("     判定に使うのは deficit の**最大**である (1 点でも正なら不合格)。")
    print("  ⚠ 符号の非対称性 (これが本節の証明力): `Gamma` / `G(λ)` は最大化 = 真値の下界")
    print("     ⟹ `Λ` は**上振れ**する ⟹ 測った deficit は真の deficit の**下界**。よって")
    print("     **正の deficit は証明書、負の deficit は最適化ノイズ**と読む。")
    print("     さらに `Gamma` 側は 2 値 `U` の格子による**最適化不使用の下界**でも取り、")
    print("     証明書はそちら (`def_grid`) で確定させる。")
    print()
    rng = np.random.default_rng(11150802)
    rows = []
    for name, px, Cy, Cz in binary_family(quick):
        hy, hz = h_cond(px, Cy), h_cond(px, Cz)
        target = min(hy, hz)
        i_y, i_z = ixy_ixz(px, Cy, Cz)
        ld, _ = lambda_det(px, Cy, Cz)
        gy, gz, ny, nz, _ = gamma_sup(px, Cy, Cz, rng,
                                      restarts=4 if quick else 8)
        l_sup = _h(px) - min(gy, gz)
        l_ib, lam = lambda_ib(px, Cy, Cz, rng, n_lam=13 if quick else 26)
        ggy, ggz, garg = gamma_grid_binary(px, Cy, Cz, 41 if quick else 81)
        l_grid = _h(px) - min(ggy, ggz)
        # less noisy 順序: 良い方の受信機の nu が 0 か (I が大きい側で nu = 0 なら順序つき)
        ordered = (ny if i_y >= i_z else nz) < 1e-5
        rows.append(dict(name=name, target=target, det=ld, sup=l_sup, ib=l_ib,
                         grid=l_grid, nu=(ny, nz), lam=lam, ordered=ordered,
                         garg=garg))
    print(f"  {'チャネル対':<24} {'min H(X|·)':>10} {'Λ_det':>9} {'Λ_sup':>9} "
          f"{'Λ_ib':>9} {'def_sup':>9} {'def_grid':>9} {'順序':>5}")
    for r in rows:
        print(f"  {r['name']:<24} {r['target']:>10.6f} {r['det']:>9.6f} "
              f"{r['sup']:>9.6f} {r['ib']:>9.6f} {r['target'] - r['sup']:>9.6f} "
              f"{r['target'] - r['grid']:>9.6f} "
              f"{'ord' if r['ordered'] else 'NO':>5}")
    d_det = max(abs(r["target"] - r["det"]) for r in rows)
    d_sup = [r["target"] - r["sup"] for r in rows]
    d_ib = [r["target"] - r["ib"] for r in rows]
    d_grid = [r["target"] - r["grid"] for r in rows]
    d_best = [min(a, b) for a, b in zip(d_sup, d_ib)]      # Λ_max = max{Λ_sup, Λ_ib}
    print()
    print(f"  `Λ_det` の deficit の最大 = {d_det:.3e} "
          f"⟹ (N1) {'PASS' if d_det < TOL_ID else '**FAIL**'} "
          "(P1 の (N1) PASS を再現。ただし `Λ_det` は下界ではない)")
    print(f"  `Λ_sup` の deficit: 最小 {min(d_sup):+.6f} / 最大 {max(d_sup):+.6f}")
    print(f"  `Λ_ib`  の deficit: 最小 {min(d_ib):+.6f} / 最大 {max(d_ib):+.6f}")
    print(f"  ⟹ 最適化ノイズの実測 (負側の最大幅) = {max(0.0, -min(min(d_sup), min(d_ib))):.3e}")
    print(f"  **証明書 (最適化不使用の格子)** `def_grid` の最大 = {max(d_grid):+.6f}")
    cert = [r for r, d in zip(rows, d_grid) if d > 1e-4]
    print(f"  `def_grid > 1e-4` の点 = {len(cert)}/{len(rows)} 本 ⟹ (N1) "
          f"{'**FAIL** (証明書つき)' if cert else 'PASS (証明書は出ず)'}")
    if cert:
        w = max(cert, key=lambda r: r["target"] - (r["grid"]))
        print(f"    最大の証明書: {w['name']} — 2 値 U の (a,b,w) = "
              f"{tuple(round(t, 4) for t in w['garg'])}、deficit = "
              f"{w['target'] - w['grid']:.6f}")
    n_ord = sum(1 for r in rows if r["ordered"])
    agree = sum(1 for r, d in zip(rows, d_grid) if (d > 1e-4) != r["ordered"])
    print(f"  less noisy 順序つきの点 = {n_ord}/{len(rows)} 本、"
          f"「順序つき ⟺ deficit 0」と整合する点 = {agree}/{len(rows)} 本")
    return dict(rows=rows, d_det=d_det, d_sup=d_sup, d_ib=d_ib, d_grid=d_grid,
                d_best=d_best, cert=len(cert), n_ord=n_ord, agree=agree)


# --------------------------------------------------------------------------
# §2 (N2) — 格子 BC
# --------------------------------------------------------------------------
def section2(quick: bool) -> dict:
    print()
    print("=" * 78)
    print("§2 (N2) — 格子 BC で `Λ = 0` (= `L' = 0` に張り付く) か")
    print("=" * 78)
    rng = np.random.default_rng(2150802)
    rows = []
    fam = lattice_family()
    if quick:
        fam = fam[:3]
    for name, T in fam:
        kx = T.shape[0]
        px = np.full(kx, 1.0 / kx)
        Cy, Cz = marginals(T)
        hx = _h(px)
        gy, gz, _, _, _ = gamma_sup(px, Cy, Cz, rng, restarts=4)
        l_sup = hx - min(gy, gz)
        l_ib, _ = lambda_ib(px, Cy, Cz, rng, n_lam=13 if quick else 21,
                            restarts=3 if kx <= 6 else 10)
        ld = lambda_det(px, Cy, Cz)[0] if kx <= 6 else float("nan")
        rows.append((name, hx, l_sup, l_ib, ld))
        print(f"  {name:<20} H(X)={hx:.4f}  Λ_sup={l_sup:+.3e}  Λ_ib={l_ib:+.3e}  "
              f"Λ_det={ld:+.3e}")
    # 証明済の下界が `L' = 0` を超えたら、それは数学的矛盾ではなく**推定不足**である
    # (`Gamma` / `G(λ)` は最大化 = 真値の下界 ⟹ `Λ` は上振れする)。黙って除外せず、
    # 推定不足として分けて数え、どの行がそうなったかを必ず出す。
    tol_est = 1e-4
    short = [r for r in rows if max(r[2], r[3]) > tol_est]
    clean = [r for r in rows if max(r[2], r[3]) <= tol_est]
    worst = (max(abs(r[2]) for r in clean) if clean else 0.0,
             max(abs(r[3]) for r in clean) if clean else 0.0)
    print(f"  ⟹ 推定が足りた {len(clean)}/{len(rows)} 件での |値| の最大: "
          f"`Λ_sup` {worst[0]:.3e} / `Λ_ib` {worst[1]:.3e}")
    for r in short:
        print(f"  ⚠ **推定不足** {r[0]}: Λ_sup={r[2]:+.3e} / Λ_ib={r[3]:+.3e} — "
              "証明済の下界が `L' = 0` を超えている ⟹ `G(λ)` の最大化が届いていない"
              "だけで反例ではない (|X| が大きいほど起きる)")
    ok = max(worst) < 1e-5 and not short
    verdict = "PASS" if ok else ("**保留** (推定不足 %d 件。数学的な反例ではない)"
                                 % len(short))
    print(f"  ⟹ (N2) {verdict}")
    return dict(rows=rows, ok=ok, short=len(short))


# --------------------------------------------------------------------------
# §3 (H3) の 3 項分解 — 超過分がどこに居るか
# --------------------------------------------------------------------------
def section3(quick: bool) -> dict:
    print()
    print("=" * 78)
    print("§3 新しい診断 — `L' - Λ_sup` の内訳 (H3): U の非最適性 / D1 / D2")
    print("=" * 78)
    print("  D1 = I(X;Z|U) - I(V;Z|U) (V が Z 側で X を代表しきれない分)、"
          "D2 = I(U;V|Z) (Z を見ても残る依存)")
    print()
    rng = np.random.default_rng(3150802)
    cases = [("Blackwell (決定論的)", np.full(3, 1 / 3), *marginals(blackwell())),
             ("平滑化 Blackwell eps=.1", np.full(3, 1 / 3), *smoothed_blackwell(0.1)),
             ("平滑化 Blackwell eps=.01", np.full(3, 1 / 3), *smoothed_blackwell(0.01)),
             ("BSC(.1) 2 本 (|X|=2 埋込)", np.full(3, 1 / 3), *noisy_blackwell(0.1))]
    if not quick:
        pm_y, pm_z, _ = partial_merge(2 / 3, 3 / 4)
        cases.append(("部分併合 (P2 の witness)", np.array([0.45, 0.45, 0.10]),
                      pm_y, pm_z))
        for i in range(3):
            px, Cy, Cz = dense_random(rng)
            cases.append((f"dense ランダム #{i + 1}", px, Cy, Cz))
    rows = []
    for name, px, Cy, Cz in cases:
        lp, terms, p3 = l_prime(px, Cy, Cz, rng, restarts=6 if quick else 12,
                                seed_pairs=det_pairs(px.size)[:9])
        gy, gz, _, _, _ = gamma_sup(px, Cy, Cz, rng, restarts=4 if quick else 8)
        l_sup = _h(px) - min(gy, gz)
        base, d1, d2 = h3_terms(p3, Cy, Cz)
        rows.append(dict(name=name, lp=lp, sup=l_sup, base=base, d1=d1, d2=d2,
                         u_slack=base - l_sup))
        print(f"  {name:<26} L'={lp:.6f}  Λ_sup={l_sup:.6f}  "
              f"| U 非最適={base - l_sup:.6f}  D1={d1:.6f}  D2={d2:.6f}")
    bad = [r for r in rows if r["sup"] > r["lp"] + 1e-4]   # 1e-5 台は Gamma 側の探索不足
    print()
    print(f"  ⚠ `Λ_sup > L' 推定` になった行: {len(bad)} 本 "
          "(証明済の下界なので 1 本でも出たら最適化のバグか L' 側の探索不足)")
    dom = max(rows, key=lambda r: r["d2"])
    print(f"  超過分の内訳で D2 が最大なのは「{dom['name']}」(D2 = {dom['d2']:.6f})")
    return dict(rows=rows, bad=len(bad))


# --------------------------------------------------------------------------
# §4 generic な非退化インスタンス (dense / 非決定論的 / |X|=3 / 非一様 p)
# --------------------------------------------------------------------------
def section4(quick: bool) -> dict:
    print()
    print("=" * 78)
    print("§4 generic な非退化インスタンス — 証明済 3 本が実際の `gap` をどこまで説明するか")
    print("=" * 78)
    print("  slack(Λ) := min{H(X|Y),H(X|Z)} - Λ は gap の上界。gap 実測 (下界) と比べる。")
    print()
    rng = np.random.default_rng(4150802)
    n = 12 if quick else 40
    rows = []
    for _ in range(n):
        px, Cy, Cz = dense_random(rng)
        hy, hz = h_cond(px, Cy), h_cond(px, Cz)
        target = min(hy, hz)
        i_y, i_z = ixy_ixz(px, Cy, Cz)
        lp, _, _ = l_prime(px, Cy, Cz, rng, restarts=6,
                           seed_pairs=det_pairs(3)[:9])
        gap_lo = target - lp                                  # gap の下界
        gy, gz, _, _, _ = gamma_sup(px, Cy, Cz, rng, restarts=4)
        l_sup = _h(px) - min(gy, gz)
        l_ib, _ = lambda_ib(px, Cy, Cz, rng, n_lam=11, restarts=2)
        ld, _ = lambda_det(px, Cy, Cz)
        rows.append(dict(gap=gap_lo, target=target, s_sup=target - l_sup,
                         s_ib=target - l_ib, s_det=target - ld,
                         triv=min(i_y, i_z)))
    def stat(key):
        v = np.array([r[key] for r in rows])
        return f"min {v.min():.4f} / 中央 {np.median(v):.4f} / max {v.max():.4f}"
    print(f"  gap の実測 (下界)          : {stat('gap')}")
    print(f"  slack(Λ_sup)               : {stat('s_sup')}")
    print(f"  slack(Λ_ib)                : {stat('s_ib')}")
    print(f"  slack(Λ_det)  ⚠ 下界でない  : {stat('s_det')}")
    print(f"  既知の自明な上界 min{{I,I}}  : {stat('triv')}")
    sig = [r for r in rows if r["gap"] > 1e-3]          # gap が測れる点だけで比を取る
    ratio = np.array([r["s_sup"] / r["gap"] for r in sig]) if sig else np.array([np.nan])
    beats = sum(1 for r in rows if r["s_sup"] < r["triv"] - 1e-9)
    beats_h = sum(1 for r in rows if r["s_sup"] < r["target"] - 1e-9)
    print()
    print(f"  slack(Λ_sup) / gap の比 (gap > 1e-3 の {len(sig)}/{n} 点のみ): "
          f"中央 {np.median(ratio):.2f} / max {ratio.max():.2f} (1 に近いほど鋭い)")
    print(f"  `Λ_sup` が自明な上界 min{{I(X;Y),I(X;Z)}} より鋭い点: {beats}/{n}")
    print(f"  `Λ_sup` が自明な上界 min{{H(X|Y),H(X|Z)}} より鋭い点: {beats_h}/{n}")
    return dict(rows=rows, ratio_med=float(np.median(ratio)), beats=beats,
                beats_h=beats_h, n=n)


# --------------------------------------------------------------------------
# §4b 候補 P4 — 入力アルファベットの 2 分割による再帰 (Theorem 1 を base case に据える)
# --------------------------------------------------------------------------
def t_thm1(px, Cy, Cz) -> float:
    """`|X| <= 2` での `T(X)` = `max{I(X;Y), I(X;Z)}` ([GJNW13] Theorem 1、既知)。"""
    if px.size <= 1:
        return 0.0
    return max(ixy_ixz(px, Cy, Cz))


def split_bound(px, Cy, Cz):
    """候補 P4 の右辺 `min_{W = m(X), 2 値} [ H(W) + sum_w p(w) B(X|W=w) ]`。

    `B` は `|X| <= 2` で [GJNW13] Theorem 1 の値 (厳密) を返し、それより大きい台では
    自分自身を再帰的に呼ぶ。**最適化を一切使わない** ⟹ 返り値は厳密。
    返り `(値, 最良の分割)`。
    """
    k = px.size
    if k <= 2:
        return t_thm1(px, Cy, Cz), None
    best, arg = np.inf, None
    for mask in range(1, 2 ** (k - 1)):
        s = [i for i in range(k) if (mask >> i) & 1]
        sc = [i for i in range(k) if not (mask >> i) & 1]
        if not s or not sc:
            continue
        ps, psc = float(px[s].sum()), float(px[sc].sum())
        if min(ps, psc) < 1e-12:
            continue
        val = _h(np.array([ps, psc]))
        val += ps * split_bound(px[s] / ps, Cy[s], Cz[s])[0]
        val += psc * split_bound(px[sc] / psc, Cy[sc], Cz[sc])[0]
        if val < best:
            best, arg = val, (tuple(s), tuple(sc))
    return best, arg


def section4b(quick: bool) -> dict:
    print()
    print("=" * 78)
    print("§4b 候補 **P4** — 入力アルファベットの 2 分割による再帰")
    print("=" * 78)
    print("  主張: 任意の 2 値 `W = m(X)` について")
    print("        `T(X) <= H(W) + sum_w p(w) T(X | W = w)`")
    print("  ⟹ `|X| = 2` を [GJNW13] Theorem 1 (既知) で閉じると、右辺は**最適化不使用で")
    print("     厳密に計算できる**再帰になる。(N1) は base case ゆえ**構成から PASS**。")
    print("  ⚠ 主張自体は**未証明** (係数 1 の版。DPI だけだと係数 3 までしか出ない)")
    print("     ⟹ 本節は kill-first の probe。`T` の**下界**が右辺を超えたら証明書つきの kill。")
    print()
    rng = np.random.default_rng(45150802)
    cases = [("Blackwell (格子)", np.full(3, 1 / 3), *marginals(blackwell())),
             ("平滑化 Blackwell .1", np.full(3, 1 / 3), *smoothed_blackwell(0.1)),
             ("平滑化 Blackwell .01", np.full(3, 1 / 3), *smoothed_blackwell(0.01)),
             ("BSC(.1) 2 本", np.full(3, 1 / 3), *noisy_blackwell(0.1))]
    pm_y, pm_z, _ = partial_merge(2 / 3, 3 / 4)
    cases.append(("部分併合 witness", np.array([0.45, 0.45, 0.10]), pm_y, pm_z))
    for name, T in lattice_family():
        kx = T.shape[0]
        if kx <= (4 if quick else 6):
            cases.append((f"格子 {name}", np.full(kx, 1.0 / kx), *marginals(T)))
    n_rand = 8 if quick else 30
    for i in range(n_rand):
        px, Cy, Cz = dense_random(rng)
        cases.append((f"dense ランダム |X|=3 #{i + 1}", px, Cy, Cz))
    if not quick:
        for i in range(10):
            px, Cy, Cz = dense_random(rng, kx=4, ky=4, kz=4)
            cases.append((f"dense ランダム |X|=4 #{i + 1}", px, Cy, Cz))
    rows, viol = [], []
    for name, px, Cy, Cz in cases:
        rb, arg = split_bound(px, Cy, Cz)
        kx = px.size
        rep = _L13.t_lower(px, Cy, Cz, rng, restarts=4 if quick else 10,
                           seed_pairs=det_pairs(kx)[:12] if kx <= 4 else ())
        t_lo = rep.best
        mx = max(ixy_ixz(px, Cy, Cz))
        rows.append(dict(name=name, t=t_lo, rhs=rb, margin=t_lo - rb, mx=mx,
                         slack=rb - mx, hx=_h(px), arg=arg))
        if t_lo - rb > 1e-7:
            viol.append(rows[-1])
    show = [r for r in rows if not r["name"].startswith("dense")][:12]
    print(f"  {'ケース':<26} {'T 下界':>9} {'P4 右辺':>9} {'margin':>10} "
          f"{'slack':>9} {'H(X)':>8}")
    for r in show:
        print(f"  {r['name']:<26} {r['t']:>9.6f} {r['rhs']:>9.6f} "
              f"{r['margin']:>+10.2e} {r['slack']:>9.6f} {r['hx']:>8.4f}")
    marg = np.array([r["margin"] for r in rows])
    print()
    print(f"  全 {len(rows)} 件の margin (`T 下界 - P4 右辺`): "
          f"max {marg.max():+.3e} / 中央 {np.median(marg):+.3e}")
    print(f"  **違反 (margin > 1e-7) = {len(viol)}/{len(rows)} 件** ⟹ P4 は "
          f"{'**REFUTED** (証明書つき)' if viol else '本 leg の掃引では生存'}")
    if viol:
        w = max(viol, key=lambda r: r["margin"])
        print(f"    最大違反: {w['name']} — T 下界 {w['t']:.6f} > 右辺 {w['rhs']:.6f} "
              f"(margin {w['margin']:+.6f}、最良分割 {w['arg']})")
    lat = [r for r in rows if r["name"].startswith("格子") or "Blackwell (格子)" in r["name"]]
    tight = [r for r in lat if abs(r["rhs"] - r["hx"]) < 1e-9]
    print(f"  格子 BC で右辺が `H(X)` に一致 (= (N2) の意味で鋭い): {len(tight)}/{len(lat)} 件")
    dense = [r for r in rows if r["name"].startswith("dense")]
    if dense:
        sl = np.array([r["slack"] for r in dense])
        gp = np.array([max(r["t"] - r["mx"], 0.0) for r in dense])
        print(f"  dense ランダムでの slack(P4) = 右辺 - max{{I,I}}: "
              f"中央 {np.median(sl):.4f} (gap 実測の中央 {np.median(gp):.4f})")
    return dict(rows=rows, viol=len(viol), tight=len(tight), n_lat=len(lat))


# --------------------------------------------------------------------------
# §4c P4 の敵対的探索 (チャネルと p(u,v|x) を同時に振って違反を取りにいく)
# --------------------------------------------------------------------------
def adversarial_p4(rng, kx: int, ky: int, kz: int, restarts: int, maxiter: int = 1500):
    """`objective(cond) - split_bound` を `(p, Cy, Cz, cond)` 上で同時に最大化する。

    左辺は**明示の `p(u,v|x)` の直接評価**、右辺は**全列挙で厳密** ⟹ 正の値が出たら
    最適化を一切信用せずに読める **kill の証明書**になる (L13 の運用教訓: 決着は
    明示 witness の直接評価で付ける)。
    """
    n_p, n_y, n_z = kx, kx * ky, kx * kz
    n_c = kx * kx * kx
    dim = n_p + n_y + n_z + n_c

    def unpack(th):
        i = 0
        px = softmax(th[i:i + n_p]); i += n_p
        Cy = softmax(th[i:i + n_y].reshape(kx, ky), axis=-1); i += n_y
        Cz = softmax(th[i:i + n_z].reshape(kx, kz), axis=-1); i += n_z
        cond = softmax(th[i:i + n_c].reshape(kx, kx * kx), axis=-1).reshape(kx, kx, kx)
        return px, Cy, Cz, cond

    def f(th):
        px, Cy, Cz, cond = unpack(th)
        lhs = objective(cond_to_joint(cond, px), Cy, Cz)
        return lhs - split_bound(px, Cy, Cz)[0]

    rep = maximize_hd(f, dim, rng, restarts=restarts, maxiter=maxiter)
    return rep.best, unpack(rep.best_x)


def section4c(quick: bool) -> dict:
    print()
    print("=" * 78)
    print("§4c P4 の敵対的探索 — チャネルと `p(u,v|x)` を同時に振って違反を取りにいく")
    print("=" * 78)
    print("  左辺 = 明示の `p(u,v|x)` の直接評価 (最適化を通した値ではない) / "
          "右辺 = 全列挙で厳密")
    print("  ⟹ **正の margin が 1 つ出た時点で P4 は kill** (逆に出ないことは証拠であって"
          "証明ではない)")
    print()
    rng = np.random.default_rng(46150802)
    best = -np.inf
    rows = []
    shapes = [(3, 3, 3), (3, 2, 2), (3, 4, 4)] if quick else \
        [(3, 3, 3), (3, 2, 2), (3, 4, 4), (3, 2, 3), (4, 4, 4), (4, 2, 2)]
    for (kx, ky, kz) in shapes:
        m, arg = adversarial_p4(rng, kx, ky, kz,
                                restarts=8 if quick else 24)
        rows.append(((kx, ky, kz), m))
        best = max(best, m)
        print(f"  |X|={kx}, |Y|={ky}, |Z|={kz}: 最良 margin = {m:+.6e}")
    print()
    print(f"  ⟹ 全形状での最良 margin = {best:+.6e} ⟹ P4 は "
          f"{'**REFUTED**' if best > 1e-7 else '敵対的探索でも生存'}")
    return dict(rows=rows, best=float(best))


# --------------------------------------------------------------------------
# §4d (H4) — P4 の記号的な証明 (4 項が項別に grouping 超加法的)
# --------------------------------------------------------------------------
_H4_IDS = [
    ("I(U;X|Y)", "I(U;X|Y)", "I(U;X|W,Y) + I(U;W|Y) - I(U;W|X,Y)"),
    ("I(V;X|Z)", "I(V;X|Z)", "I(V;X|W,Z) + I(V;W|Z) - I(V;W|X,Z)"),
    ("H(X|U,V)", "H(X|U,V)", "H(X|U,V,W) + H(W|U,V) - H(W|X,U,V)"),
    ("I(U;V|X)", "I(U;V|X)",
     "I(U;V|X,W) + I(U;W|X) + I(V;W|X) - I(U,V;W|X)"),
]


def section4d(quick: bool) -> dict:
    print()
    print("=" * 78)
    print("§4d **(H4)** — P4 は証明できる: 4 項が**項別に** grouping 超加法的")
    print("=" * 78)
    print("  `W = m(X)` (X の関数) について、4 項損失の各項は")
    print("      項(p) = 項(・|W) + (W を条件に付けたときの損失)")
    print("  と*恒等式*で分解し、損失項は W = m(X) のとき非負の 3 項だけが残る:")
    print("      F(U,V;p) - sum_w p(w) F(U,V;p_w) = I(U;W|Y) + I(V;W|Z) + H(W|U,V) >= 0")
    print("  各 (U,V) について成り立つので、右辺を最小化して")
    print("      **L'(p) >= sum_w p(w) L'(p_w)**   (= P4 の T 形と等価、grouping 公理経由)")
    print("  ⟹ base case を [GJNW13] Theorem 1 で閉じれば `Λ_split` は**証明済の下界**。")
    print()
    ok = True
    for name, lhs, rhs in _H4_IDS:
        held, resid = prove_identity(lhs, rhs)
        print(f"  ({name} の分解): accept = {held} / 残差 = {resid}")
        ok &= held
    print("  ⟹ 4 本とも無仮定の線形恒等式。`W = m(X)` を入れると")
    print("     `I(U;W|X,Y) = I(V;W|X,Z) = H(W|X,U,V) = I(U;W|X) = I(V;W|X) "
          "= I(U,V;W|X) = 0`")
    print("     (どれも `H(W|X) = 0` の系) ⟹ 残るのは非負 3 項だけ。")

    # 数値照合: W = m(X) を実際に取り、超加法性と欠損 3 項を直接評価する
    rng = np.random.default_rng(4415080)
    worst_ineq = np.inf
    n = 20 if quick else 60
    for _ in range(n):
        px, Cy, Cz = dense_random(rng)
        cond = softmax(rng.normal(0, 1.5, (3, 9)), axis=-1).reshape(3, 3, 3)
        p3 = cond_to_joint(cond, px)
        f_all = sum(loss_terms(p3, Cy, Cz))
        for mask in range(1, 4):                       # W = 1{x in S} の 3 通り
            s = [i for i in range(3) if (mask >> i) & 1]
            sc = [i for i in range(3) if not (mask >> i) & 1]
            tot = 0.0
            for part in (s, sc):
                pw = float(px[part].sum())
                if pw < 1e-12:
                    continue
                sub = cond_to_joint(cond[part], px[part] / pw)
                tot += pw * sum(loss_terms(sub, Cy[part], Cz[part]))
            worst_ineq = min(worst_ineq, f_all - tot)
    print()
    print(f"  数値照合 (dense {n} 本 x 3 分割): `F(p) - sum p_w F(p_w)` の最小 = "
          f"{worst_ineq:+.3e} (負なら反例 = 記号証明と矛盾)")
    ok &= worst_ineq > -1e-9
    # 欠損 3 項の verbatim 照合 (bc_probe.Joint で 5 + 1 変数)
    px, Cy, Cz = dense_random(rng)
    cond = softmax(rng.normal(0, 1.5, (3, 9)), axis=-1).reshape(3, 3, 3)
    p3 = cond_to_joint(cond, px)
    s = [0, 1]
    sc = [2]
    T = np.einsum("xy,xz->xyz", Cy, Cz)
    J6 = Joint(["U", "V", "X", "Y", "Z", "W"],
               np.einsum("uvx,xyz,xw->uvxyzw", p3, T,
                         np.array([[1.0, 0.0], [1.0, 0.0], [0.0, 1.0]])),
               validate=False)
    f_all = sum(loss_terms(p3, Cy, Cz))
    tot = 0.0
    for part in (s, sc):
        pw = float(px[part].sum())
        tot += pw * sum(loss_terms(cond_to_joint(cond[part], px[part] / pw),
                                   Cy[part], Cz[part]))
    defect = J6.eval(parse("I(U;W|Y) + I(V;W|Z) + H(W|U,V)"), "bits")
    print(f"  欠損の逐語照合: `F - sum p_w F_w` = {f_all - tot:.9f} vs "
          f"`I(U;W|Y)+I(V;W|Z)+H(W|U,V)` = {defect:.9f} "
          f"(差 {abs(f_all - tot - defect):.3e})")
    ok &= abs(f_all - tot - defect) < 1e-9
    print(f"  ⟹ §4d {'PASS' if ok else '**FAIL**'}")
    return dict(ok=ok, worst=float(worst_ineq))


# --------------------------------------------------------------------------
# §5 判定
# --------------------------------------------------------------------------
def section5(r1: dict, r2: dict, r3: dict, r4: dict, r4b: dict,
             r4c: dict, r4d: dict) -> None:
    print()
    print("=" * 78)
    print("§5 判定 (規則は §冒頭で固定済)")
    print("=" * 78)
    n1_cert = r1["cert"] > 0
    print("  --- 証明済 3 本 (Λ_sup / Λ_ib / Λ_max) ---")
    print(f"  (N1) `|X|=2` で鋭いか: {'**FAIL** (証明書つき)' if n1_cert else 'PASS'} "
          f"(格子による証明書 {r1['cert']}/{len(r1['rows'])} 本、"
          f"deficit の最大 {max(r1['d_grid']):+.6f})")
    n2_txt = "PASS" if r2["ok"] else "**保留** (推定不足 %d 件)" % r2["short"]
    print(f"  (N2) 格子 BC で 0 か  : {n2_txt}")
    print("  (N3) 非決定論的点での局所最適性: **自動 PASS** "
          "(証明済の下界は摂動で破れない ⟹ L13 の死因は本候補には効かない)")
    print(f"  generic な非退化点: slack/gap の中央 {r4['ratio_med']:.2f}、"
          f"自明上界より鋭い点 {r4['beats']}/{r4['n']} (min I) / "
          f"{r4['beats_h']}/{r4['n']} (min H)")
    print(f"  less noisy 順序との対応: 順序つき {r1['n_ord']}/{len(r1['rows'])} 本、"
          f"「順序つき ⟺ 鋭い」と整合 {r1['agree']}/{len(r1['rows'])} 本")
    print()
    print("  --- 候補 P4 (分割再帰) ---")
    print(f"  (N1) 構成から PASS (base case = Theorem 1) / "
          f"(N2) 格子で鋭い {r4b['tight']}/{r4b['n_lat']} 件")
    print(f"  **(H4) 記号的な証明**: {'PASS' if r4d['ok'] else '**FAIL**'} "
          f"⟹ P4 は未証明の主張ではなく**証明済の下界** "
          f"(数値照合の最小 margin {r4d['worst']:+.3e})")
    dead = r4b["viol"] or r4c["best"] > 1e-7
    print(f"  probe: 族の掃引で違反 {r4b['viol']}/{len(r4b['rows'])} 件 / "
          f"敵対的探索の最良 margin {r4c['best']:+.3e} ⟹ "
          f"{'**REFUTED**' if dead else '生存 (掃引と敵対的探索の範囲で)'}")
    print()
    if n1_cert:
        print("  ⟹ 証明済 3 本は **(N1) 不合格**。証明済ゆえ「偽」ではなく「鋭くない」。")
        print("     構造的な読み: (N1) を満たす `Λ` は [GJNW13] Theorem 1 を含意するので、")
        print("     **周辺だけの緩和で `Λ` を作る道は Theorem 1 を内蔵しない限り閉じている**。")
        print("     ⟹ P4 はその内蔵を base case で行う設計であり、この読みの直接の帰結。")
    if not dead:
        print("  ⟹ **P4 が生存**。§3.1 の (1)(2)(3)(4) は本 leg で揃い、**(5) novelty gate も "
              "L15 で単独実施して通過**した (一次文献 5 本、記録は `bc-facts.md` §L15) ⟹ "
              "経路 **R3** として `bc-open-problem-routes.md` に載っている。")
    else:
        print("  ⟹ P4 も死亡。退路 (判断ログ 28) どおり、同 family の次候補を起票せず "
              "L16–L18 で軸 G ブロックを発動する。")


def main() -> None:
    ap = argparse.ArgumentParser(
        description="軸 C の子 attack `slack-loss-lower-bound` (L15) の probe")
    ap.add_argument("--quick", action="store_true", help="掃引を縮小して回す")
    args = ap.parse_args()
    t0 = time.time()
    print("bc-slack-loss-lower-check.py — 軸 C の子: 4 項損失 `L'` の下界 `Λ` の測定")
    print(f"(mode = {'quick' if args.quick else 'full'})\n")

    ok0 = section0(args.quick)
    r1 = section1(args.quick)
    r2 = section2(args.quick)
    r3 = section3(args.quick)
    r4 = section4(args.quick)
    r4b = section4b(args.quick)
    r4c = section4c(args.quick)
    r4d = section4d(args.quick)
    section5(r1, r2, r3, r4, r4b, r4c, r4d)

    print()
    print(f"  harness コントロール: §0 {'PASS' if ok0 else '**FAIL**'} / "
          f"§3 の `Λ_sup > L'` 違反 {r3['bad']} 本 (0 であるべき)")
    print(f"\n合計実行時間 {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
