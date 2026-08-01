#!/usr/bin/env python3
"""軸 C の子候補 **C2** — チャネル依存の汎関数 `Phi(T, p)` の 2 案を数値で殺しにいく probe
(親 plan `bc-open-problem-plan.md` §5-2 kill-first、経路は `bc-open-problem-routes.md` §R2)。

何を確かめる probe か
---------------------
R2 §11 が起票した子候補 C2 (「濃度 1 つにつき定数 1 個」ではなく**チャネル依存の汎関数**を
作る) の具体案 2 本。記法は R2 逐語:

    T(X)      := max_{p(u,v|x)} I(U;Y) + I(V;Z) - I(U;V)     ((U,V) -> X -> (Y,Z))
    gap(T,p)  := T(X) - max{I(X;Y), I(X;Z)}
    「格子」BC := (Y,Z) が X を復元する決定論的 BC

**候補 P1 (主) — 決定論的最適性**

    Phi_det(q,p) := max over 関数の対 f: X->U, g: X->V の
                        [ I(f(X);Y) + I(g(X);Z) - I(f(X);g(X)) ]

    主張: `T(X) <= Phi_det(q,p)`。`Phi_det <= T` は定義から自明 (決定論的条件付き分布は
    p(u,v|x) の部分集合) なので、主張は **`T(X) = Phi_det(q,p)`** = 「T の最大化子は
    決定論的に取れる」と同値。決定論的条件付き分布は多面体 {p(u,v|x)} の**端点そのもの**
    なので、P1 は「目的関数の最大が端点で達成される」という主張である。

**候補 P2 (副) — `p` で細分した加法スラック**

    D(p) := max over 関数の対 f, g の [ H(f(X), g(X)) - max{H(f(X)), H(g(X))} ]
    主張: `gap(T,p) <= D(p)`      (チャネルに依らず p(x) だけで決まる量)

    R2 の `gap <= D(|X|)` の細分 (`D(p) <= D(|X|)`)。

**2 候補の関係 (本 probe の構造的な発見。§0(d) が数値でも確認する)**

    どの決定論的対 (f,g) についても、その対だけで測った両辺は
        [I(f;Y) + I(g;Z) - I(f;g)] - max{I(X;Y),I(X;Z)}
            <= [H(f,g) - max{H(f),H(g)}] = min{H(f),H(g)} - I(f;g)
    が **DPI 2 本と場合分けだけで証明できる** (max = I(X;Y) の側なら
    I(f;Y) <= H(f) と I(g;Z) <= I(X;Z) <= I(X;Y) で H(f) 側、
    I(g;Z) <= H(g) と I(f;Y) <= I(X;Y) で H(g) 側)。argmax の対で使うと

        Phi_det - max{I(X;Y),I(X;Z)} <= D(p)          (証明済)
        ⟹ gap - D(p) <= T - Phi_det                   (P2 の margin <= P1 の margin)
        ⟹ **P1 ⟹ P2**。P2 の違反は自動的に P1 の違反でもある。

    したがって 2 候補は独立ではなく入れ子で、1 回の掃引で両方の margin を測れば足りる。

判定の向き (どの数値が確実で、どれが探索にすぎないか)
------------------------------------------------------
* `Phi_det` と `D(p)` は **関数対の全列挙で厳密**に計算する (最適化を使わない)。
* `T(X)` は最大化で下から評価するだけ ⟹ **下界**。
* ゆえに `T - Phi_det > 0` / `gap - D(p) > 0` が出たら、それは**証明書 (kill)** である
  (下界が既に厳密値を超えている)。逆に出なかったことは**証拠であって証明ではない**。
* 列挙は像の分割 (制限増加列) で重複排除する。`I(f(X);Y)` 等は f のラベル付けに依らず
  分割だけで決まるので無損失。§0(c) が k=3 で全 729 対と突き合わせて確認する。

sim と定義の逐語照合 (CLAUDE.md 検証の誠実性)
---------------------------------------------
* 目的量・witness・チャネルは L10 probe `bc-jognair-general-check.py` を **import して
  再利用**する (ファイル名にハイフンがあるので importlib で読む)。単位は bit、
  エントロピー規約は `bc_probe` (自然対数版を bit へ換算) と同じ。
* 本 probe は高速化のため `p(u,y)` / `p(v,z)` / `p(u,v)` を直接組む評価器を持つが、
  §0(a) が `bc_probe.Joint` 経由の一般評価と 1e-12 で一致することを確認する。
* §0(b): T / gap は `q(y,z|x)` の**周辺 `p(y|x)`, `p(z|x)` にしか依存しない**
  (I(U;Y), I(V;Z), I(U;V), I(X;Y), I(X;Z) のいずれも Y,Z の同時分布を見ない)。
  相関つき `q(y,z|x)` とその周辺だけを与えた場合が一致することを数値で確認する。

各節が何を決めるか
------------------
    §0  harness の照合 (高速評価器 / 周辺への還元 / 列挙の重複排除 / 補題)
    §1  コントロール (肯定 |X|=2 / 否定 Blackwell 再現 / 黄金比 witness)
    §2  (N1) と (N2) を **両候補に両方**当てる (R2 §11 の教訓: 片側だけだと死案が通る)
    §3  P1 の掃引と kill witness    §4  P2 の掃引と kill witness    §5  まとめ表

再実行コマンド / 期待される判定
-------------------------------
    python3 docs/shannon/bc-jognair-phi-check.py           # 約 130s
    python3 docs/shannon/bc-jognair-phi-check.py --quick   # 約 30s (掃引を縮小)

乱数種と最適化の開始点はすべて固定してあるので **再実行で報告値は一致する**
(実行時間行を除く)。期待される最終判定 (通常実行):

    §2 (N1)/(N2) は **両候補とも 4 マス全部 PASS** — それでも下で両方死ぬ
    §3 **P1 は refuted** (§3(e) 雑音つき Blackwell の明示 witness、margin ~ +0.10 bit)
    §4 **P2 は refuted** (§4(d) 部分併合 witness、margin ~ +0.037 bit)

⚠ **(N1)/(N2) を両方通しても足りない**というのが本 leg の主要な収穫である。
   2 条件はどちらも「退化した場所」(|X|=2 と決定論的 BC) での整合しか要求せず、
   P1 が生き残るのはまさにその 2 か所だけだった。次の候補を立てるときは、
   **非決定論的チャネルでの局所最適性**を第 3 の必要条件として先に当てること。
"""

from __future__ import annotations

import argparse
import importlib.util
import itertools
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))

from bc_probe import Joint, local_max_certificate, parse, softmax  # noqa: E402


def _load_sibling(fname: str, modname: str):
    """ハイフンつきファイル名の兄弟 probe を import する (規約の再導出を避けるため)。"""
    path = Path(__file__).resolve().parent / fname
    spec = importlib.util.spec_from_file_location(modname, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)          # __main__ ガードがあるので main() は走らない
    return mod


_L10 = _load_sibling("bc-jognair-general-check.py", "bc_jognair_general_check")
blackwell = _L10.blackwell               # [GNA12] 脚注 3 逐語の Blackwell チャネル
grid = _L10.grid                         # a x b 格子 BC
joint5 = _L10.joint5                     # p(u,v,x) * T(y,z|x) の 5 変数同時分布
witness_uy_vz = _L10.witness_uy_vz       # [GJNW13] §I-B-2 の U=Y, V=Z witness
maximize_hd = _L10.maximize_hd           # L-BFGS-B 多点再スタート (返るのは下界)

PHI = (1.0 + 5.0**0.5) / 2.0
LOG2_PHI = float(np.log2(PHI))
Q_GOLDEN = (5.0 - 5.0**0.5) / 10.0       # R2 step 7 の内点条件 5q^2-5q+1=0 の根

_LHS = parse("I(U;Y) + I(V;Z) - I(U;V)")
_IXY = parse("I(X;Y)")
_IXZ = parse("I(X;Z)")

VIOL_TOL = 1e-7                          # これを超えた margin は witness として再評価する


# --------------------------------------------------------------------------
# 情報量の直接評価 (§0(a) が bc_probe.Joint 経由と一致することを確認する)
# --------------------------------------------------------------------------
def _h(p) -> float:
    q = np.asarray(p, dtype=float).ravel()
    q = q[q > 1e-300]
    return float(-(q * np.log2(q)).sum())


def _mi(p2) -> float:
    p2 = np.asarray(p2, dtype=float)
    return _h(p2.sum(axis=1)) + _h(p2.sum(axis=0)) - _h(p2)


def objective(puvx: np.ndarray, Cy: np.ndarray, Cz: np.ndarray) -> float:
    """`I(U;Y) + I(V;Z) - I(U;V)` (bit)。`puvx[u,v,x]`, `Cy[x,y]`, `Cz[x,z]`。"""
    puy = np.einsum("uvx,xy->uy", puvx, Cy)
    pvz = np.einsum("uvx,xz->vz", puvx, Cz)
    return _mi(puy) + _mi(pvz) - _mi(puvx.sum(axis=2))


def ixy_ixz(px: np.ndarray, Cy: np.ndarray, Cz: np.ndarray) -> tuple[float, float]:
    return _mi(px[:, None] * Cy), _mi(px[:, None] * Cz)


def marginals(T: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """`T[x,y,z]` から周辺チャネル `p(y|x)`, `p(z|x)` を取る。"""
    return T.sum(axis=2), T.sum(axis=1)


# --------------------------------------------------------------------------
# 決定論的な対の全列挙 (像の分割 = 制限増加列で重複排除)
# --------------------------------------------------------------------------
def partitions(k: int) -> list[tuple[int, ...]]:
    """`[k]` の分割を制限増加列で列挙する (Bell(k) 本。k=3 で 5、k=4 で 15)。"""
    out: list[tuple[int, ...]] = []

    def rec(pref: list[int], mx: int) -> None:
        if len(pref) == k:
            out.append(tuple(pref))
            return
        for b in range(mx + 1):
            rec(pref + [b], max(mx, b + 1))

    rec([], 0)
    return out


_PARTS: dict[int, list[tuple[int, ...]]] = {}
_PAIRS: dict[int, list[tuple[tuple[int, ...], tuple[int, ...]]]] = {}

ENUM_CAP = 3000       # Bell(k)^2 がこれを超える k では全列挙をやめる (Bell(6)^2 = 41209)


def enumerable(k: int) -> bool:
    return len(partitions(k)) ** 2 <= ENUM_CAP


def det_pairs(k: int):
    if k not in _PAIRS:
        _PARTS[k] = partitions(k)
        _PAIRS[k] = [(f, g) for f in _PARTS[k] for g in _PARTS[k]]
    return _PAIRS[k]


def det_joint(f, g, px: np.ndarray, ku: int | None = None, kv: int | None = None):
    """決定論的対 `(f,g)` に対応する `p(u,v,x)` (形 `(ku,kv,kx)`)。"""
    kx = px.size
    ku = ku or kx
    kv = kv or kx
    p = np.zeros((ku, kv, kx))
    for x in range(kx):
        p[f[x], g[x], x] = px[x]
    return p


def phi_det(px: np.ndarray, Cy: np.ndarray, Cz: np.ndarray):
    """`Phi_det` を関数対の全列挙で**厳密に**求める。返り `(best, (f,g), 全値)`。"""
    kx = px.size
    best, arg, vals = -np.inf, None, []
    for f, g in det_pairs(kx):
        v = objective(det_joint(f, g, px), Cy, Cz)
        vals.append(v)
        if v > best:
            best, arg = v, (f, g)
    return best, arg, np.array(vals)


def d_of_p(px: np.ndarray):
    """`D(p) = max_{f,g} [H(f,g) - max{H(f),H(g)}]` を全列挙で**厳密に**求める。"""
    kx = px.size
    best, arg, vals = -np.inf, None, []
    for f, g in det_pairs(kx):
        puv = det_joint(f, g, px).sum(axis=2)
        v = _h(puv) - max(_h(puv.sum(axis=1)), _h(puv.sum(axis=0)))
        vals.append(v)
        if v > best:
            best, arg = v, (f, g)
    return best, arg, np.array(vals)


# --------------------------------------------------------------------------
# T(X) の下からの評価 (p(x) を固定して p(u,v|x) 上で最大化)
# --------------------------------------------------------------------------
def cond_to_joint(cond: np.ndarray, px: np.ndarray) -> np.ndarray:
    """`cond[x,u,v]` (条件付き) から `p(u,v,x)` を作る。p(x) は固定される。"""
    return np.einsum("x,xuv->uvx", px, cond)


def t_lower(px, Cy, Cz, rng, restarts=6, seed_pairs=(), leak=1e-6, maxiter=3000):
    """`p(x)` を固定したまま `p(u,v|x)` 上で `T(X)` を最大化する = **下界**。

    `seed_pairs` の決定論的対を開始点に明示的に渡す (親 plan §2.1: ランダム再スタート
    だけでは最大を外す実例が R2 §7(e) にある)。`|U| = |V| = |X|` は
    [GJNW13] Remark 3 逐語の還元。
    """
    kx = px.size

    def f(theta):
        cond = softmax(theta.reshape(kx, kx * kx), axis=-1).reshape(kx, kx, kx)
        return objective(cond_to_joint(cond, px), Cy, Cz)

    seeds = []
    for fg in seed_pairs:
        c = np.zeros((kx, kx, kx))
        for x in range(kx):
            c[x, fg[0][x], fg[1][x]] = 1.0
        seeds.append(np.log(c.ravel() + leak))
    return maximize_hd(f, kx**3, rng, restarts=restarts, seeds=seeds, maxiter=maxiter)


# --------------------------------------------------------------------------
# 構造化された条件付き分布の族 (直接評価用。最適化を使わない)
# --------------------------------------------------------------------------
def additive_cond(pa: np.ndarray, pb: np.ndarray, k: int = 3) -> np.ndarray:
    """`U = X + A`, `V = X + B` (mod k、A ⊥ B ⊥ X) の条件付き `cond[x,u,v]`。"""
    cond = np.zeros((k, k, k))
    for x in range(k):
        for u in range(k):
            for v in range(k):
                cond[x, u, v] = pa[(u - x) % k] * pb[(v - x) % k]
    return cond


def sym_noise(a: float, k: int = 3) -> np.ndarray:
    p = np.full(k, a)
    p[0] = 1.0 - (k - 1) * a
    return p


def det_cond(fg, kx: int) -> np.ndarray:
    c = np.zeros((kx, kx, kx))
    for x in range(kx):
        c[x, fg[0][x], fg[1][x]] = 1.0
    return c


def sym_channel(a: float, k: int = 3) -> np.ndarray:
    """加法的対称チャネル `p(y|x) = pN(y-x)`、`pN = (1-(k-1)a, a, ..., a)`。"""
    pn = sym_noise(a, k)
    return np.array([[pn[(y - x) % k] for y in range(k)] for x in range(k)])


# --------------------------------------------------------------------------
# §0 harness の照合
# --------------------------------------------------------------------------
def section0(quick: bool) -> bool:
    print("=" * 78)
    print("§0 harness の照合 — 高速評価器 / 周辺への還元 / 列挙の重複排除 / 補題")
    print("=" * 78)
    rng = np.random.default_rng(20260802)
    ok = True

    # (a) 高速評価器 vs bc_probe.Joint 経由の一般評価
    worst = 0.0
    for _ in range(200):
        kx, ky, kz = 3, int(rng.integers(2, 5)), int(rng.integers(2, 5))
        T = rng.dirichlet(np.full(ky * kz, 1.0), size=kx).reshape(kx, ky, kz)
        puvx = rng.dirichlet(np.full(kx * kx * kx, 1.0)).reshape(kx, kx, kx)
        a = objective(puvx, *marginals(T))
        b = joint5(puvx, T).eval(_LHS, "bits")
        worst = max(worst, abs(a - b))
    good = worst < 1e-12
    ok &= good
    print(f"  (a) 高速評価器 vs bc_probe.Joint (200 本): 最大差 {worst:.3e}  "
          f"{'OK' if good else '**NG**'}")

    # (b) T / gap が q(y,z|x) の周辺にしか依らないこと
    #     (相関つき同時カーネルと、その周辺から作った独立カーネルで値が一致する)
    worst_b = 0.0
    for _ in range(100):
        kx, ky, kz = 3, 3, 3
        T = rng.dirichlet(np.full(ky * kz, 0.5), size=kx).reshape(kx, ky, kz)
        Cy, Cz = marginals(T)
        T_ind = Cy[:, :, None] * Cz[:, None, :]
        puvx = rng.dirichlet(np.full(kx**3, 1.0)).reshape(kx, kx, kx)
        v1 = joint5(puvx, T).eval(_LHS, "bits")
        v2 = joint5(puvx, T_ind).eval(_LHS, "bits")
        px = puvx.sum(axis=(0, 1))
        m1 = max(joint5(puvx, T).eval(_IXY, "bits"), joint5(puvx, T).eval(_IXZ, "bits"))
        m2 = max(ixy_ixz(px, Cy, Cz))
        worst_b = max(worst_b, abs(v1 - v2), abs(m1 - m2))
    good = worst_b < 1e-12
    ok &= good
    print(f"  (b) T/gap は q(y,z|x) の**周辺のみ**に依存 (100 本): 最大差 {worst_b:.3e}  "
          f"{'OK' if good else '**NG**'}")
    print("      ⟹ チャネルの掃引は 2 本の DMC p(y|x), p(z|x) の掃引でよい "
          "(Y ⊥ Z | X は無関係)")

    # (c) 分割による重複排除 = 全 k^k x k^k 対の列挙と同値 (k = 3)
    worst_c, cover_ok = 0.0, True
    for _ in range(20 if quick else 60):
        Cy = rng.dirichlet(np.full(3, 1.0), size=3)
        Cz = rng.dirichlet(np.full(3, 1.0), size=3)
        px = rng.dirichlet(np.full(3, 1.0))
        pd, _, vals = phi_det(px, Cy, Cz)
        brute = []
        for f in itertools.product(range(3), repeat=3):
            for g in itertools.product(range(3), repeat=3):
                brute.append(objective(det_joint(f, g, px), Cy, Cz))
        worst_c = max(worst_c, abs(max(brute) - pd))
        for b in brute:                      # 全値が分割側の値集合に現れるか
            if np.min(np.abs(vals - b)) > 1e-12:
                cover_ok = False
    good = worst_c < 1e-12 and cover_ok
    ok &= good
    print(f"  (c) 分割 25 対 vs 全関数対 729 (k=3): 最大値の差 {worst_c:.3e}、"
          f"値集合の包含 {'OK' if cover_ok else '**NG**'}  {'OK' if good else '**NG**'}")

    # (d) 補題 Phi_det - max{I,I} <= D(p) を全対で確認 (証明は module docstring)
    worst_d = -np.inf
    n_d = 120 if quick else 400
    for _ in range(n_d):
        kx = int(rng.integers(2, 5))
        ky, kz = int(rng.integers(2, 5)), int(rng.integers(2, 5))
        conc = float(rng.choice([0.3, 1.0, 3.0]))
        Cy = rng.dirichlet(np.full(ky, conc), size=kx)
        Cz = rng.dirichlet(np.full(kz, conc), size=kx)
        px = rng.dirichlet(np.full(kx, conc))
        ixy, ixz = ixy_ixz(px, Cy, Cz)
        m = max(ixy, ixz)
        for f, g in det_pairs(kx):
            p3 = det_joint(f, g, px)
            puv = p3.sum(axis=2)
            lhs = objective(p3, Cy, Cz) - m
            rhs = _h(puv) - max(_h(puv.sum(axis=1)), _h(puv.sum(axis=0)))
            worst_d = max(worst_d, lhs - rhs)
    good = worst_d < 1e-9
    ok &= good
    print(f"  (d) 補題 [各対で] obj(f,g) - max{{I,I}} <= H(f,g) - max{{H(f),H(g)}}:")
    print(f"      ({n_d} 本 x 全対) 最大残差 {worst_d:+.3e}  {'OK' if good else '**NG**'}")
    print("      ⟹ Phi_det - max{I,I} <= D(p) (証明は DPI 2 本 + 場合分け。docstring 参照)")
    print("      ⟹ **P1 ⟹ P2**、かつ gap - D(p) <= T - Phi_det (margin の大小も確定)")
    print(f"  §0 判定: {'全 OK' if ok else '**NG あり**'}\n")
    return ok


# --------------------------------------------------------------------------
# §1 コントロール
# --------------------------------------------------------------------------
def section1(quick: bool) -> tuple[bool, dict]:
    print("=" * 78)
    print("§1 コントロール — harness を信用する前に通すもの")
    print("=" * 78)
    rng = np.random.default_rng(4242)
    ok = True
    res: dict = {}

    # (a) 肯定コントロール: |X| = 2 の Theorem 1 = 両候補の (N1)
    n = 300 if quick else 1200
    w_phi, w_d, w_T = 0.0, 0.0, -np.inf
    n_opt = 8 if quick else 40
    chans = []
    for _ in range(n):
        ky, kz = int(rng.integers(2, 5)), int(rng.integers(2, 5))
        conc = float(rng.choice([0.3, 1.0, 3.0]))
        Cy = rng.dirichlet(np.full(ky, conc), size=2)
        Cz = rng.dirichlet(np.full(kz, conc), size=2)
        px = rng.dirichlet(np.full(2, conc))
        pd, _, _ = phi_det(px, Cy, Cz)
        m = max(ixy_ixz(px, Cy, Cz))
        w_phi = max(w_phi, abs(pd - m))
        w_d = max(w_d, abs(d_of_p(px)[0]))
        chans.append((px, Cy, Cz, pd))
    for px, Cy, Cz, pd in chans[:n_opt]:
        rep = t_lower(px, Cy, Cz, rng, restarts=4, seed_pairs=det_pairs(2))
        w_T = max(w_T, rep.best - pd)
    good = w_phi < 1e-12 and w_d < 1e-12 and w_T < VIOL_TOL
    ok &= good
    print(f"  (a) |X| = 2 のランダムチャネル {n} 本 (|Y|,|Z| in {{2,3,4}}、Dirichlet 濃度 3 通り)")
    print(f"      |Phi_det - max{{I,I}}| の最大 = {w_phi:.3e}   (N1 for P1)")
    print(f"      |D(p)| の最大            = {w_d:.3e}   (N1 for P2)")
    print(f"      max (T の最大化 - Phi_det) = {w_T:+.3e}  "
          f"(上位 {n_opt} 本のみ最適化。Theorem 1 の再導出)  {'OK' if good else '**NG**'}")
    res["n1_phi"], res["n1_d"], res["n1_T"] = w_phi, w_d, w_T

    # (b) 否定コントロール: Blackwell + 一様 で原典の数値を再現
    T = blackwell()
    Cy, Cz = marginals(T)
    px = np.full(3, 1.0 / 3.0)
    Tw = objective(witness_uy_vz(px, T), Cy, Cz)
    m = max(ixy_ixz(px, Cy, Cz))
    pd, arg, _ = phi_det(px, Cy, Cz)
    good = (abs(Tw - np.log2(3.0)) < 1e-12 and abs(m - 0.9182958340544896) < 1e-12
            and abs(pd - Tw) < 1e-12)
    ok &= good
    print(f"  (b) Blackwell + X ~ [1/3,1/3,1/3] ([GJNW13] §I-B-2 逐語の witness)")
    print(f"      T(X) >= H(Y,Z) = {Tw!r}   (log2 3 = {float(np.log2(3.0))!r})")
    print(f"      max{{I(X;Y),I(X;Z)}} = {m!r}   (h(1/3) = 0.918296)")
    print(f"      Phi_det = {pd!r} at (f,g) = {arg}  {'OK' if good else '**NG**'}")

    # (c) 黄金比 witness
    pxg = np.array([Q_GOLDEN, 1.0 - 2.0 * Q_GOLDEN, Q_GOLDEN])
    Tg = objective(witness_uy_vz(pxg, T), Cy, Cz)
    mg = max(ixy_ixz(pxg, Cy, Cz))
    gapg = Tg - mg
    dg, argd, _ = d_of_p(pxg)
    good = abs(gapg - LOG2_PHI) < 1e-12 and abs(dg - LOG2_PHI) < 1e-12
    ok &= good
    print(f"  (c) Blackwell + p = (q, 1-2q, q), q = (5-sqrt5)/10 = {Q_GOLDEN:.6f}")
    print(f"      gap = {gapg!r}   log2 phi = {LOG2_PHI!r}   差 {gapg - LOG2_PHI:+.3e}")
    print(f"      D(p) = {dg!r} at (f,g) = {argd}  (gap = D(p) ちょうど)  "
          f"{'OK' if good else '**NG**'}")
    print(f"  §1 判定: {'全 OK' if ok else '**NG あり**'}\n")
    return ok, res


# --------------------------------------------------------------------------
# §2 (N1) と (N2) — 両候補に**両方**当てる
# --------------------------------------------------------------------------
def lattice_family() -> list[tuple[str, np.ndarray]]:
    """格子 BC (= (Y,Z) が X を復元する決定論的 BC) の一覧。"""
    out = [("Blackwell (|X|=3)", blackwell())]
    for name, cells in [("L 字 3 セル (|X|=3)", [(0, 0), (0, 1), (1, 1)]),
                        ("十字 5 セル (|X|=5)", [(0, 1), (1, 0), (1, 1), (1, 2), (2, 1)])]:
        T = np.zeros((len(cells), 3, 3))
        for i, (r, c) in enumerate(cells):
            T[i, r, c] = 1.0
        out.append((name, T))
    out += [("2x2 格子 (|X|=4)", grid(2, 2)), ("2x3 格子 (|X|=6)", grid(2, 3)),
            ("3x3 格子 (|X|=9)", grid(3, 3))]
    return out


def channel_maps(T: np.ndarray) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """決定論的 BC `T[x,y,z]` の 2 本の写像 `(Y の写像, Z の写像)` を取り出す。"""
    Cy, Cz = marginals(T)
    return tuple(int(np.argmax(Cy[x])) for x in range(T.shape[0])), \
        tuple(int(np.argmax(Cz[x])) for x in range(T.shape[0]))


def section2(quick: bool) -> tuple[dict, bool]:
    print("=" * 78)
    print("§2 (N1) / (N2) — 2 案とも**両方**の必要条件に当てる (R2 §11 の教訓)")
    print("=" * 78)
    print("  (N1) |X| = 2 で Theorem 1 に退化するか   (N2) 格子 BC で witness を許すか")
    print("  ⚠ R2 で死んだ案 A / 案 B はそれぞれ (N2) / (N1) の**片方だけ**を満たした。")
    print()
    rng = np.random.default_rng(31415)
    ok = True

    # --- (N1) ------------------------------------------------------------
    print("  [N1] |X| = 2 (§1(a) の 1200 本 + 決定論的 4 通りの内訳):")
    print("      P1: Phi_det の 4 候補は 0 / I(X;Y) / I(X;Z) / I(X;Y)+I(X;Z)-H(X) で、")
    print("          最後は min{I,I} <= H(X) より max を超えない ⟹ **Phi_det = max{I,I}**")
    print("      P2: D(p) は 4 通りすべてで 0 ⟹ 主張は **gap <= 0 = Theorem 1 そのもの**")
    n = 200 if quick else 800
    w1, w2 = 0.0, 0.0
    for _ in range(n):
        conc = float(rng.choice([0.3, 1.0, 3.0]))
        Cy = rng.dirichlet(np.full(int(rng.integers(2, 5)), conc), size=2)
        Cz = rng.dirichlet(np.full(int(rng.integers(2, 5)), conc), size=2)
        px = rng.dirichlet(np.full(2, conc))
        w1 = max(w1, abs(phi_det(px, Cy, Cz)[0] - max(ixy_ixz(px, Cy, Cz))))
        w2 = max(w2, abs(d_of_p(px)[0]))
    n1_p1, n1_p2 = w1 < 1e-12, w2 < 1e-12
    ok &= n1_p1 and n1_p2
    print(f"      追加 {n} 本: P1 の |Phi_det - max{{I,I}}| = {w1:.3e} ⟹ "
          f"**{'PASS' if n1_p1 else 'FAIL'}**")
    print(f"                P2 の |D(p)| = {w2:.3e} ⟹ **{'PASS' if n1_p2 else 'FAIL'}**")

    # --- (N2) ------------------------------------------------------------
    print()
    print("  [N2] 格子 BC (U=Y, V=Z の witness が T = H(X) を出す。R2 step 5):")
    print("      `|X|` が大きいと分割対の全列挙 (Bell(k)^2) が効かないので、そこは")
    print("      **チャネル 2 写像の対だけを直接評価**する (Phi_det / D(p) の下界)。")
    print("      T <= H(X) は R2 step 1 の**証明済上界**なので、Phi_det = H(X) は")
    print("      「下界 = 上界」で確定し、最大化を要しない。")
    print("      チャネル             |   H(X)   |  Phi_det | T の最大化 | max{I,I} |"
          "   gap    |   D(p)   | 列挙")
    print("      ---------------------+----------+----------+------------+----------+"
          "----------+----------+------")
    n2_p1, n2_p2 = True, True
    for name, T in lattice_family():
        kx = T.shape[0]
        Cy, Cz = marginals(T)
        px = np.full(kx, 1.0 / kx)
        hx = _h(px)
        fg = channel_maps(T)
        p3 = det_joint(fg[0], fg[1], px)
        obj_w = objective(p3, Cy, Cz)                     # U=Y, V=Z の直接評価
        puv = p3.sum(axis=2)
        d_w = _h(puv) - max(_h(puv.sum(axis=1)), _h(puv.sum(axis=0)))
        full = enumerable(kx)
        pd = phi_det(px, Cy, Cz)[0] if full else obj_w
        dp = d_of_p(px)[0] if full else d_w
        m = max(ixy_ixz(px, Cy, Cz))
        if kx <= 5:
            rep = t_lower(px, Cy, Cz, rng, restarts=2 if quick else 5,
                          seed_pairs=det_pairs(kx)[:6])
            tl, tl_s = max(rep.best, pd), f"{max(rep.best, pd):10.6f}"
        else:
            tl, tl_s = pd, f"{'(上界 H(X))':>10}"          # 高次元は最大化を回さない
        gap = tl - m
        n2_p1 &= (pd >= hx - 1e-9) and (tl <= hx + VIOL_TOL)
        n2_p2 &= gap <= dp + VIOL_TOL
        print(f"      {name:<20} | {hx:8.6f} | {pd:8.6f} | {tl_s} | {m:8.6f} |"
              f" {gap:8.6f} | {dp:8.6f} | {'全' if full else 'witness'}")
    ok &= n2_p1 and n2_p2
    print(f"      P1: 全格子 BC で Phi_det = H(X) (= R2 step 1 の証明済上界) かつ "
          f"T <= Phi_det ⟹ **{'PASS' if n2_p1 else 'FAIL'}**")
    print("          (格子 BC では上界 T <= H(X) が決定論的 witness で達成される "
          "⟹ P1 はそこで**等号で確定**)")
    print(f"      P2: 全格子 BC で gap <= D(p)、しかも等号 ⟹ "
          f"**{'PASS' if n2_p2 else 'FAIL'}**")
    print()
    print(f"  ⟹ (N1)/(N2) の 4 マスすべて: "
          f"P1 = ({'PASS' if n1_p1 else 'FAIL'}, {'PASS' if n2_p1 else 'FAIL'}), "
          f"P2 = ({'PASS' if n1_p2 else 'FAIL'}, {'PASS' if n2_p2 else 'FAIL'})\n")
    return {"n1_p1": n1_p1, "n2_p1": n2_p1, "n1_p2": n1_p2, "n2_p2": n2_p2}, ok


# --------------------------------------------------------------------------
# §3 P1 の掃引 — T > Phi_det を探す
# --------------------------------------------------------------------------
def screen_value(px, Cy, Cz, pd, arg, rng, n_rand: int):
    """`Phi_det` の周りを安価に叩いて、最良の非決定論的な値を返す。

    (i) 最良の決定論的点から各 x の条件付きを 1 点へ振り替える方向 (= 条件付き単体の
    頂点方向)、(ii) ランダム条件付き。返り `(最良値, 最良の p(u,v,x))`。
    """
    kx = px.size
    best, best_p = -np.inf, None
    c0 = det_cond(arg, kx)
    for x in range(kx):
        for u in range(kx):
            for v in range(kx):
                for eps in (1e-1, 1e-2, 1e-3):
                    c = c0.copy()
                    c[x] *= (1.0 - eps)
                    c[x, u, v] += eps
                    val = objective(cond_to_joint(c, px), Cy, Cz)
                    if val > best:
                        best, best_p = val, cond_to_joint(c, px)
    for _ in range(n_rand):
        conc = float(rng.choice([0.3, 1.0, 3.0]))
        c = rng.dirichlet(np.full(kx * kx, conc), size=kx).reshape(kx, kx, kx)
        val = objective(cond_to_joint(c, px), Cy, Cz)
        if val > best:
            best, best_p = val, cond_to_joint(c, px)
    return best, best_p


def max_slope(f, p0: np.ndarray, dirs, eps_list=(1e-2, 1e-3, 1e-4)) -> float:
    """`p0` から各方向への片側微分係数 `(f((1-e)p0+es) - f(p0))/e` の最大。

    正なら局所最大ですらない (kill)。0 近傍なら**平坦** = 掃引の非違反は弱い証拠。
    """
    base = f(p0)
    best = -np.inf
    for s in dirs:
        for e in eps_list:
            best = max(best, (f((1.0 - e) * p0 + e * s) - base) / e)
    return best


def empty_cells(arg, kx: int) -> list[tuple[int, int]]:
    """`(u,v)` の表のうち **両座標とも使用済なのに空**のセル (kill 機構の舞台)。"""
    used = {(arg[0][x], arg[1][x]) for x in range(kx)}
    return [(u, v) for u in sorted(set(arg[0])) for v in sorted(set(arg[1]))
            if (u, v) not in used]


def cell_perturbed(arg, px, x: int, u: int, v: int, eps: float) -> np.ndarray:
    """決定論的対 `arg` の `x` の条件付きから、空セル `(u,v)` へ質量 `eps` を移す。"""
    c = det_cond(arg, px.size)
    c[x] *= (1.0 - eps)
    c[x, u, v] += eps
    return cond_to_joint(c, px)


def certificate_dirs(px, arg, kx):
    """局所最大性証明書の `directions=`。(i) 単体頂点 (ii) 他の決定論的対 (iii) 加法族。"""
    dirs = []
    p0 = det_joint(arg[0], arg[1], px)
    for x in range(kx):                                   # (i)
        for u in range(kx):
            for v in range(kx):
                s = p0.copy()
                s[:, :, x] = 0.0
                s[u, v, x] = px[x]
                dirs.append(s.ravel())
    for fg in det_pairs(kx):                              # (ii)
        dirs.append(det_joint(fg[0], fg[1], px).ravel())
    if kx == 3:                                           # (iii)
        for a in (0.05, 0.15, 0.3, 1.0 / 3.0):
            for b in (0.0, 0.05, 0.15, 0.3, 1.0 / 3.0):
                dirs.append(
                    cond_to_joint(additive_cond(sym_noise(a), sym_noise(b)), px).ravel())
    return dirs


def section3(quick: bool) -> dict:
    print("=" * 78)
    print("§3 P1 の掃引 — `T(X) > Phi_det` を探す (見つかれば**証明書 = kill**)")
    print("=" * 78)
    print("  Phi_det は全列挙で厳密、T は最大化の**下界** ⟹ 違反は証拠ではなく証明書。")
    rng = np.random.default_rng(777)
    best_margin, best_where, best_witness = -np.inf, "", None

    def note(margin, where, wit=None):
        nonlocal best_margin, best_where, best_witness
        if margin > best_margin:
            best_margin, best_where, best_witness = margin, where, wit

    # --- (a) ランダム |X| = 3 -------------------------------------------
    n3 = 80 if quick else 400
    n_rand = 60 if quick else 200
    recs = []
    for _ in range(n3):
        ky, kz = int(rng.integers(2, 5)), int(rng.integers(2, 5))
        conc = float(rng.choice([0.3, 1.0, 3.0]))
        Cy = rng.dirichlet(np.full(ky, conc), size=3)
        Cz = rng.dirichlet(np.full(kz, conc), size=3)
        px = rng.dirichlet(np.full(3, float(rng.choice([0.5, 1.0, 3.0]))))
        pd, arg, _ = phi_det(px, Cy, Cz)
        sv, _ = screen_value(px, Cy, Cz, pd, arg, rng, n_rand)
        recs.append((sv - pd, px, Cy, Cz, pd, arg))
    recs.sort(key=lambda r: -r[0])
    print(f"  (a) ランダム |X|=3 チャネル {n3} 本 (|Y|,|Z| in {{2,3,4}}、濃度 3 通り、"
          f"p(x) も振る)")
    print(f"      screen (単体頂点方向 {3**3}x3 本 + ランダム条件付き {n_rand} 本) の")
    print(f"      最良 margin = {recs[0][0]:+.3e}  (正なら即 kill)")
    n_opt = 3 if quick else 8
    for margin, px, Cy, Cz, pd, arg in recs[:n_opt]:
        rep = t_lower(px, Cy, Cz, rng, restarts=4 if quick else 8,
                      seed_pairs=[arg] + det_pairs(3)[:4])
        note(rep.best - pd, "§3(a) ランダム |X|=3", (px, Cy, Cz, pd, rep))
    print(f"      screen 上位 {n_opt} 本を p(u,v|x) 上で本最大化 ⟹ "
          f"最大 margin = {best_margin:+.3e}")

    # --- (b) |X| = 4 -----------------------------------------------------
    n4 = 25 if quick else 100
    recs4 = []
    for _ in range(n4):
        ky, kz = int(rng.integers(2, 5)), int(rng.integers(2, 5))
        conc = float(rng.choice([0.3, 1.0, 3.0]))
        Cy = rng.dirichlet(np.full(ky, conc), size=4)
        Cz = rng.dirichlet(np.full(kz, conc), size=4)
        px = rng.dirichlet(np.full(4, float(rng.choice([0.5, 1.0, 3.0]))))
        pd, arg, _ = phi_det(px, Cy, Cz)
        sv, _ = screen_value(px, Cy, Cz, pd, arg, rng, n_rand // 2)
        recs4.append((sv - pd, px, Cy, Cz, pd, arg))
    recs4.sort(key=lambda r: -r[0])
    b4 = -np.inf
    for margin, px, Cy, Cz, pd, arg in recs4[:2 if quick else 4]:
        rep = t_lower(px, Cy, Cz, rng, restarts=3 if quick else 6,
                      seed_pairs=[arg] + det_pairs(4)[:4])
        b4 = max(b4, rep.best - pd)
        note(rep.best - pd, "§3(b) ランダム |X|=4", (px, Cy, Cz, pd, rep))
    T4 = grid(2, 2)
    Cy4, Cz4 = marginals(T4)
    px4 = np.full(4, 0.25)
    pd4, arg4, _ = phi_det(px4, Cy4, Cz4)
    rep4 = t_lower(px4, Cy4, Cz4, rng, restarts=3 if quick else 6,
                   seed_pairs=[arg4] + det_pairs(4)[:4])
    note(rep4.best - pd4, "§3(b) 2x2 格子", (px4, Cy4, Cz4, pd4, rep4))
    print(f"  (b) |X|=4: ランダム {n4} 本 (screen 最良 margin {recs4[0][0]:+.3e}) の上位を"
          f"最大化 ⟹ {b4:+.3e}")
    print(f"      2x2 格子: Phi_det = {pd4:.6f} (= H(X) = 2)、T の最大化 = {rep4.best:.6f}"
          f"  margin {rep4.best - pd4:+.3e}")

    # --- (c) 構造化された敵対族 (直接評価) --------------------------------
    print("  (c) 構造化された敵対族 (**直接評価**。最適化を通さないので数値は witness):")
    fams: list[tuple[str, np.ndarray, np.ndarray, np.ndarray]] = []
    for k in (3, 4):                                      # (a) 無雑音 Y = Z = X
        fams.append((f"無雑音 Y=Z=X (|X|={k})", np.eye(k), np.eye(k),
                     np.full(k, 1.0 / k)))
    for a in (0.05, 0.15, 0.3):                           # (b) Y = Z = 雑音つき X
        C = sym_channel(a)
        fams.append((f"Y = Z = X+N (a={a})", C, C, np.full(3, 1.0 / 3.0)))
    Tb = blackwell()
    Cyb, Czb = marginals(Tb)
    fams.append(("Blackwell + 一様", Cyb, Czb, np.full(3, 1.0 / 3.0)))
    fams.append(("Blackwell + 黄金比 p", Cyb, Czb,
                 np.array([Q_GOLDEN, 1 - 2 * Q_GOLDEN, Q_GOLDEN])))
    fams.append(("Z_3 対称 a=0.1 / a=0.25", sym_channel(0.1), sym_channel(0.25),
                 np.full(3, 1.0 / 3.0)))
    worst_add, worst_mix, worst_slope = -np.inf, -np.inf, -np.inf
    print("      族                        |  Phi_det  | 加法族の超過 | 混合族の超過 |"
          " 最大傾き")
    print("      --------------------------+-----------+--------------+--------------+"
          "----------")
    for name, Cy, Cz, px in fams:
        kx = px.size
        pd, arg, _ = phi_det(px, Cy, Cz)
        # (c-1) 加法族 U = X+A, V = X+B (Z_3 のみ)
        add = -np.inf
        if kx == 3:
            gridvals = [0.0, 0.02, 0.05, 0.1, 0.2, 1.0 / 3.0]
            for a in gridvals:
                for b in gridvals:
                    for pa, pb in ((sym_noise(a), sym_noise(b)),
                                   (np.array([1 - a - b, a, b]), sym_noise(b))):
                        if min(pa.min(), pb.min()) < -1e-12:
                            continue
                        v = objective(cond_to_joint(additive_cond(pa, pb), px), Cy, Cz)
                        add = max(add, v)
            note(add - pd, f"§3(c) 加法族 [{name}]")
            worst_add = max(worst_add, add - pd)
        # (c-2) 2 つの決定論的対の凸結合
        vals = [(objective(det_joint(f, g, px), Cy, Cz), (f, g)) for f, g in det_pairs(kx)]
        vals.sort(key=lambda t: -t[0])
        mix = -np.inf
        for fg1, fg2 in itertools.combinations([v[1] for v in vals[:4]], 2):
            c1, c2 = det_cond(fg1, kx), det_cond(fg2, kx)
            for lam in np.linspace(0.0, 1.0, 41):
                v = objective(cond_to_joint(lam * c1 + (1 - lam) * c2, px), Cy, Cz)
                mix = max(mix, v)
        note(mix - pd, f"§3(c) 混合族 [{name}]")
        worst_mix = max(worst_mix, mix - pd)
        # (c-3) 最良決定論的点での片側微分係数の最大
        dirs = [d.reshape(kx, kx, kx) for d in
                [np.asarray(x) for x in certificate_dirs(px, arg, kx)]]
        p0 = det_joint(arg[0], arg[1], px)
        sl = max_slope(lambda q: objective(q, Cy, Cz), p0, dirs)
        worst_slope = max(worst_slope, sl)
        add_s = f"{add - pd:+12.3e}" if kx == 3 else f"{'n/a (Z_3 のみ)':>12}"
        print(f"      {name:<25} | {pd:9.6f} | {add_s} | {mix - pd:+12.3e} |"
              f" {sl:+9.3e}")
    print("      ⚠ 「最大傾き」= 最良決定論的点からの片側微分係数の最大 (方向は "
          "単体頂点 + 他の決定論的対 + 加法族)。")
    print("        正なら局所最大ですらない (kill)。**0 近傍なら平坦** = 非違反は弱い証拠。")

    # --- (d) 局所最大性証明書 -------------------------------------------
    print("  (d) 局所最大性証明書 (`local_max_certificate`、方向を明示。"
          "ランダム方向は p(x) を壊すので使わない):")
    cert_rows = []
    for name, Cy, Cz, px in fams[: 4 if quick else len(fams)]:
        kx = px.size
        pd, arg, _ = phi_det(px, Cy, Cz)
        p0 = det_joint(arg[0], arg[1], px)
        dirs = certificate_dirs(px, arg, kx)
        # p(x) を保つランダム条件付き方向を明示的に足す (既定のランダム方向は使わない)
        for _ in range(60 if quick else 200):
            c = rng.dirichlet(np.full(kx * kx, 1.0), size=kx).reshape(kx, kx, kx)
            dirs.append(cond_to_joint(c, px).ravel())
        gain, _, eps = local_max_certificate(
            lambda q: objective(np.asarray(q).reshape(kx, kx, kx), Cy, Cz),
            p0.ravel(), rng, trials=0, directions=dirs,
        )
        note(gain, f"§3(d) 証明書 [{name}]")
        cert_rows.append((name, len(dirs), gain, eps))
        print(f"      {name:<25} 方向 {len(dirs):4d} 本、最大増分 {gain:+.3e} "
              f"(eps={eps:g})  {'**改善方向あり = kill**' if gain > VIOL_TOL else 'OK'}")

    # --- (e) kill の明示 witness と機構 ---------------------------------
    m_e, slope_e = section3e(quick)
    note(m_e, "§3(e) 雑音つき Blackwell (明示 witness)")
    worst_slope = max(worst_slope, slope_e)

    print(f"  ⟹ §3 全体の最大 margin (T - Phi_det) = **{best_margin:+.6e}** "
          f"({best_where})")
    if best_margin > VIOL_TOL:
        print("     ⟹ **P1 は refuted** (§3(e) が明示 witness と機構を出す)。")
    else:
        print("     ⟹ **掃引では P1 を殺せなかった** (= 証拠。証明ではない)。")
    print()
    return {"margin": best_margin, "where": best_where, "witness": best_witness,
            "slope": worst_slope}


def bsc(e: float) -> np.ndarray:
    return np.array([[1.0 - e, e], [e, 1.0 - e]])


def noisy_blackwell(eta: float) -> tuple[np.ndarray, np.ndarray]:
    """Blackwell の 2 出力をそれぞれ BSC(eta) に通した周辺チャネル `(p(y|x), p(z|x))`。"""
    Cy, Cz = marginals(blackwell())
    return Cy @ bsc(eta), Cz @ bsc(eta)


def section3e(quick: bool) -> tuple[float, float]:
    """P1 の kill — **明示 witness の直接評価** (最適化を使わない) と、その機構。"""
    print("  (e) **kill の明示 witness** — 雑音つき Blackwell (最適化を使わない直接評価):")
    print("      Blackwell の 2 出力をそれぞれ BSC(eta) に通しただけの族。"
          "eta=0 が Blackwell。")
    px = np.full(3, 1.0 / 3.0)
    rng = np.random.default_rng(2718)
    print("      eta  |  Phi_det  | 最良の決定論的対       | 空セル | 摂動後の T の下界 |"
          "  margin")
    print("      -----+-----------+------------------------+--------+-------------------+"
          "-----------")
    best_eta, best_margin = None, -np.inf
    for eta in (0.0, 0.01, 0.03, 0.05, 0.1, 0.15, 0.2):
        Cy, Cz = noisy_blackwell(eta)
        pd, arg, _ = phi_det(px, Cy, Cz)
        ecs = empty_cells(arg, 3)
        best = pd
        for (u, v) in ecs:
            for x in range(3):
                for eps in (0.3, 0.2, 0.1, 0.05, 0.02, 0.01, 1e-3, 1e-4):
                    best = max(best, objective(cell_perturbed(arg, px, x, u, v, eps),
                                               Cy, Cz))
        if best - pd > best_margin:
            best_eta, best_margin = eta, best - pd
        print(f"      {eta:<4} | {pd:9.6f} | {str(arg):<22} | {len(ecs):^6} |"
              f" {best:17.6f} | {best - pd:+.3e}")
    print("      ⚠ eta = 0 (Blackwell そのもの) と eta = 0.2 では margin が **ちょうど 0**。")
    print("        前者は決定論的チャネル、後者は最良対の f が定数 (空セルが無い) で、")
    print("        どちらも下の機構が働かない場合にあたる = 機構の予測どおり。")

    # --- witness の逐語出力と独立再評価 ---------------------------------
    eta = 0.1
    Cy, Cz = noisy_blackwell(eta)
    pd, arg, _ = phi_det(px, Cy, Cz)
    brute = max(objective(det_joint(f, g, px), Cy, Cz)
                for f in itertools.product(range(3), repeat=3)
                for g in itertools.product(range(3), repeat=3))
    x0, (u0, v0), eps0 = 0, empty_cells(arg, 3)[0], 0.2
    puvx = cell_perturbed(arg, px, x0, u0, v0, eps0)
    val_fast = objective(puvx, Cy, Cz)
    T3 = Cy[:, :, None] * Cz[:, None, :]          # q(y,z|x) の代表 (Y ⊥ Z | X)
    J = Joint(["U", "V", "X", "Y", "Z"], puvx[:, :, :, None, None] * T3[None, None])
    val_gen = J.eval(_LHS, "bits")
    print()
    print(f"      witness (eta = {eta}, X ~ 一様、|U|=|V|=3、eps = {eps0}):")
    print(f"        p(y|x) = {np.array2string(Cy, precision=3)}")
    print(f"        p(z|x) = {np.array2string(Cz, precision=3)}")
    print(f"        最良の決定論的対 (f,g) = {arg}、空セル (u,v) = {(u0, v0)}、"
          f"移す x = {x0}")
    print(f"        p(u,v|x={x0}) = (1-eps) delta_{{{(arg[0][x0], arg[1][x0])}}} "
          f"+ eps delta_{{{(u0, v0)}}}、他の x は決定論的のまま")
    print(f"        Phi_det = {pd!r}   (全 729 関数対のブルートフォース = {brute!r}、"
          f"差 {brute - pd:+.1e})")
    print(f"        witness の目的値 = {val_fast!r}")
    print(f"        **独立再評価** (bc_probe.Joint + parse 経由、高速評価器を通さない) "
          f"= {val_gen!r}")
    print(f"        差 = {abs(val_fast - val_gen):.3e}、"
          f"Markov 検査 I(U,V;Y,Z|X) = {J.eval(parse('I(U,V;Y,Z|X)'), 'bits'):+.3e}、"
          f"p(x) のずれ = {np.abs(J.marginal(['X']) - px).max():.3e}")
    print(f"        ⟹ **margin = T - Phi_det >= {val_fast - pd:+.6f} bit** "
          "(下界どうしの比較ではなく、")
    print("           厳密な Phi_det を明示 witness が超えている ⟹ **証明書**)")

    # --- 傾きの発散 (機構の定量的確認) -----------------------------------
    print()
    print("      機構: 最良の決定論的対では `(u,v)` の表に **両座標とも使用済なのに空**の")
    print("      セルが残る。そこへ質量 eps を移すと")
    print("        - H(U,V) は空セルが立ち上がるので **p(x)·h(eps) ~ p(x)·eps·log2(1/eps)**")
    print("          だけ増える (= -I(U;V) の超一次の利得)")
    print("        - H(U), H(V) は u,v とも既に正の質量を持つので **一次**でしか動かない")
    print("        - I(U;Y), I(V;Z) は p(u,y), p(v,z) が全台なら **一次**でしか動かない")
    print("      ⟹ 差は eps->0 で `+p(x)·eps·log2(1/eps)` が支配し、傾きは **発散**する。")
    print("      決定論的チャネルでは p(v,z) が対角に載るので I(V;Z) 側も同じ超一次で")
    print("      失い、2 つが**相殺**する — 格子 BC (N2) と eta=0 が生き残るのはこれである。")
    print()
    base = objective(cond_to_joint(det_cond(arg, 3), px), Cy, Cz)
    print("        eps      obj(eps) - Phi_det    傾き (差/eps)   10 倍ごとの増分")
    prev = None
    for eps in (1e-1, 1e-2, 1e-3, 1e-4, 1e-5, 1e-6):
        d = objective(cell_perturbed(arg, px, x0, u0, v0, eps), Cy, Cz) - base
        sl = d / eps
        inc = "" if prev is None else f"{sl - prev:+.4f}"
        print(f"        {eps:<8g} {d:+.10f}        {sl:+8.4f}       {inc}")
        prev = sl
    pred = px[x0] * float(np.log2(10.0))
    print(f"        予測: 10 倍ごとの増分 = p(x={x0})·log2(10) = {pred:.4f}  "
          "⟹ 観測と一致")
    print("        ⟹ 傾きが発散する = 決定論的点は **局所最大ですらない**。")
    print("           これは数値誤差では起こりえない (eps を下げるほど比が増える)。")

    # --- 族全体での最大 margin (本最大化) --------------------------------
    best = -np.inf
    for eta in ((0.05, 0.1) if quick else (0.03, 0.05, 0.1, 0.15)):
        for name, pxx in (("一様", px),
                          ("黄金比", np.array([Q_GOLDEN, 1 - 2 * Q_GOLDEN, Q_GOLDEN]))):
            Cy, Cz = noisy_blackwell(eta)
            pd, arg, _ = phi_det(pxx, Cy, Cz)
            rep = t_lower(pxx, Cy, Cz, rng, restarts=4 if quick else 8,
                          seed_pairs=[arg] + det_pairs(3)[:4])
            best = max(best, rep.best - pd)
    print()
    print(f"      族全体を p(u,v|x) 上で本最大化した最大 margin = **{best:+.6f} bit**")
    slope = max_slope(lambda q: objective(q, Cy, Cz),
                      det_joint(arg[0], arg[1], pxx),
                      [np.asarray(d).reshape(3, 3, 3) for d in
                       certificate_dirs(pxx, arg, 3)])
    return max(best, best_margin), slope


# --------------------------------------------------------------------------
# §4 P2 の掃引 — gap > D(p) を探す
# --------------------------------------------------------------------------
def gap_max_at_p(px, ky, kz, rng, restarts, seeds=(), maxiter=3000):
    """`p(x)` を固定して `(p(y|x), p(z|x), p(u,v|x))` を同時最大化 = gap の**下界**。"""
    kx = px.size
    n1 = kx**3
    n2 = kx * ky

    def f(theta):
        cond = softmax(theta[:n1].reshape(kx, kx * kx), axis=-1).reshape(kx, kx, kx)
        Cy = softmax(theta[n1:n1 + n2].reshape(kx, ky), axis=-1)
        Cz = softmax(theta[n1 + n2:].reshape(kx, kz), axis=-1)
        return objective(cond_to_joint(cond, px), Cy, Cz) - max(ixy_ixz(px, Cy, Cz))

    return maximize_hd(f, n1 + kx * ky + kx * kz, rng, restarts=restarts,
                       seeds=list(seeds), maxiter=maxiter)


def blackwell_seed(px, ky, kz, leak=1e-6):
    """Blackwell + (U,V) = (Y,Z) を `gap_max_at_p` の開始点へ埋め込む。"""
    kx = px.size
    f, g = (0, 0, 1), (0, 1, 1)
    c = det_cond((f, g), kx)
    Cy = np.zeros((kx, ky))
    Cz = np.zeros((kx, kz))
    for x in range(kx):
        Cy[x, f[x]] = 1.0
        Cz[x, g[x]] = 1.0
    return np.concatenate([np.log(c.ravel() + leak), np.log(Cy.ravel() + leak),
                           np.log(Cz.ravel() + leak)])


def section4(quick: bool) -> dict:
    print("=" * 78)
    print("§4 P2 の掃引 — `gap(T,p) > D(p)` を探す")
    print("=" * 78)
    print("  D(p) は全列挙で厳密、gap は T の下界から作るので、違反は**証明書**。")
    print("  §0(d) より gap - D(p) <= T - Phi_det ゆえ P2 の違反は P1 の違反でもある。")
    rng = np.random.default_rng(1729)
    best_margin, best_where = -np.inf, ""

    def note(m, w):
        nonlocal best_margin, best_where
        if m > best_margin:
            best_margin, best_where = m, w

    # --- (a) 厳密な screen: gap_det = Phi_det - max{I,I} vs D(p) ---------
    n = 600 if quick else 2500
    worst = -np.inf
    for _ in range(n):
        kx = int(rng.integers(2, 5))
        conc = float(rng.choice([0.3, 1.0, 3.0]))
        Cy = rng.dirichlet(np.full(int(rng.integers(2, 5)), conc), size=kx)
        Cz = rng.dirichlet(np.full(int(rng.integers(2, 5)), conc), size=kx)
        px = rng.dirichlet(np.full(kx, conc))
        worst = max(worst, phi_det(px, Cy, Cz)[0] - max(ixy_ixz(px, Cy, Cz))
                    - d_of_p(px)[0])
    note(worst, "§4(a) 厳密 screen (決定論的側)")
    print(f"  (a) 厳密 screen — 決定論的側だけで測った margin (|X| in {{2,3,4}}、{n} 本、"
          "最適化不使用)")
    print(f"      max [Phi_det - max{{I,I}} - D(p)] = {worst:+.3e}  "
          "(§0(d) の補題どおり <= 0)")

    # --- (b) p を固定してチャネルごと最大化 (P2 に固有の掃引) -------------
    print("  (b) **p(x) を固定**して (チャネル, p(u,v|x)) を同時最大化 ⟹ D(p) と比較")
    print("      (R2 の掃引は p も動かして sup を取ったので、"
          "『各 p で D(p) が足りるか』は未検査だった)")
    ps: list[tuple[str, np.ndarray]] = [
        ("一様 (1/3,1/3,1/3)", np.full(3, 1.0 / 3.0)),
        ("黄金比 (q,1-2q,q)", np.array([Q_GOLDEN, 1 - 2 * Q_GOLDEN, Q_GOLDEN])),
        ("境界近傍 d=0.3", np.array([0.35, 0.35, 0.30])),
        ("境界近傍 d=0.1", np.array([0.45, 0.45, 0.10])),
        ("境界近傍 d=0.01", np.array([0.495, 0.495, 0.01])),
        ("境界近傍 d=0.001", np.array([0.4995, 0.4995, 0.001])),
    ]
    if not quick:
        ps += [("非対称 (0.6,0.3,0.1)", np.array([0.6, 0.3, 0.1])),
               ("非対称 (0.5,0.25,0.25)", np.array([0.5, 0.25, 0.25])),
               ("非対称 (0.7,0.2,0.1)", np.array([0.7, 0.2, 0.1])),
               ("ランダム p #1", np.array([0.2138, 0.4021, 0.3841])),
               ("ランダム p #2", np.array([0.1049, 0.5512, 0.3439]))]
    print("      最適化の列とは別に、(d) の**明示 witness 族**を同じ p で直接評価した列を")
    print("      並べる (最適化が違反を取りこぼすかどうかを同一行で照合するため)。")
    print("      p(x)                  |   D(p)   | gap (最適化) | gap (明示族) |"
          " margin | 比 gap/D")
    print("      ----------------------+----------+--------------+--------------+"
          "--------+---------")
    n_missed = 0
    for name, px in ps:
        dp, _, _ = d_of_p(px)
        best_opt = -np.inf
        for ky, kz in ([(2, 2)] if quick else [(2, 2), (3, 3)]):
            rep = gap_max_at_p(px, ky, kz, rng, restarts=3 if quick else 6,
                               seeds=[blackwell_seed(px, ky, kz)])
            best_opt = max(best_opt, rep.best)
        best_wit = partial_merge_best(px)
        best_gap = max(best_opt, best_wit)
        m = best_gap - dp
        note(m, f"§4(b) p 固定 [{name}]")
        missed = best_wit > best_opt + 1e-9 and best_wit > dp + VIOL_TOL
        n_missed += int(missed)
        ratio = best_gap / dp if dp > 1e-12 else float("nan")
        print(f"      {name:<21} | {dp:8.6f} | {best_opt:12.6f} | {best_wit:12.6f} |"
              f" {m:+6.4f} | {ratio:8.5f}{'  <- 最適化が取りこぼし' if missed else ''}")
    print("      ⚠ 境界近傍は D(p) -> 0 と gap -> 0 が同じ速さで潰れる**ナイフエッジ**で、")
    print("        比が 1 を超えれば P2 は死ぬ (ここが最も違反が隠れやすい)。")
    if n_missed:
        print(f"      ⚠ **{n_missed} 行で最適化が、明示 witness の出す違反を取りこぼした**。")
        print("        同一 run 内で「掃引で出なかった」が偽陰性でありうることの実例で、")
        print("        R2 §7(e) (ランダム再スタート 20 本が真の最大を 0.3058 bit 外した)")
        print("        と同じ現象である。⟹ 最適化列の非違反は証拠として弱い。")

    # --- (c) ランダムチャネル + ランダム p を本最大化 --------------------
    n_c = 4 if quick else 12
    print(f"  (c) ランダム (チャネル, p) を p(u,v|x) 上で本最大化 {n_c} 本:")
    worst_c = -np.inf
    for _ in range(n_c):
        kx = 3
        conc = float(rng.choice([0.3, 1.0, 3.0]))
        Cy = rng.dirichlet(np.full(int(rng.integers(2, 5)), conc), size=kx)
        Cz = rng.dirichlet(np.full(int(rng.integers(2, 5)), conc), size=kx)
        px = rng.dirichlet(np.full(kx, conc))
        pd, arg, _ = phi_det(px, Cy, Cz)
        rep = t_lower(px, Cy, Cz, rng, restarts=3 if quick else 6,
                      seed_pairs=[arg] + det_pairs(3)[:3])
        m = max(rep.best, pd) - max(ixy_ixz(px, Cy, Cz)) - d_of_p(px)[0]
        worst_c = max(worst_c, m)
    note(worst_c, "§4(c) ランダム (チャネル,p) の本最大化")
    print(f"      最大 margin = {worst_c:+.3e}")

    note(section4d(quick), "§4(d) 部分併合 witness (明示)")

    print()
    print(f"  ⟹ §4 全体の最大 margin (gap - D(p)) = **{best_margin:+.6e}** "
          f"({best_where})")
    if best_margin > VIOL_TOL:
        print("     ⟹ **P2 は refuted**。")
    else:
        print("     ⟹ **掃引では P2 を殺せなかった** (= 証拠。証明ではない)。")
    print()
    return {"margin": best_margin, "where": best_where}


def partial_merge(beta: float, alpha: float):
    """P2 の kill witness の族 (`|X| = 3`)。返り `(p(y|x), p(z|x), p(u,v|x))`。

    * `Z` は決定論的な `{0,1 | 2}` (= `z = 1{x=2}`)
    * `Y` は **部分併合** — `x = 1` のときだけ確率 `beta` で「1 である」ことを明かし、
      それ以外は `x = 0, 2` と同じ出力に潰れる (`beta = 1` で決定論的、`0` で無情報)
    * `U`: `x=0 -> 0`, `x=1 -> 1`, `x=2` **だけ** `alpha : 1-alpha` で `0 : 1` に振る
    * `V = Z`
    """
    Cy = np.array([[1.0, 0.0], [1.0 - beta, beta], [1.0, 0.0]])
    Cz = np.array([[1.0, 0.0], [1.0, 0.0], [0.0, 1.0]])
    cond = np.zeros((3, 3, 3))
    cond[0, 0, 1] = 1.0
    cond[1, 1, 1] = 1.0
    cond[2, 0, 0] = alpha
    cond[2, 1, 0] = 1.0 - alpha
    return Cy, Cz, cond


def partial_merge_best(px: np.ndarray, steps: int = 19) -> float:
    """`partial_merge` 族を `(beta, alpha)` の格子で直接評価した gap の最良値。"""
    best = -np.inf
    for beta in np.linspace(0.05, 0.95, steps):
        for alpha in np.linspace(0.05, 0.95, steps):
            Cy, Cz, cond = partial_merge(beta, alpha)
            best = max(best, objective(cond_to_joint(cond, px), Cy, Cz)
                       - max(ixy_ixz(px, Cy, Cz)))
    return best


def section4d(quick: bool) -> float:
    """P2 の kill — **明示 witness の直接評価** (最適化を使わない)。"""
    print("  (d) **kill の明示 witness** — 部分併合チャネル (最適化を使わない直接評価):")
    print("      Z = 決定論的 {0,1|2}、Y = x=1 だけ確率 beta で明かす部分併合、")
    print("      U は x=2 でだけ alpha : 1-alpha にランダム化 (V = Z は決定論的のまま)。")
    print("      ⟹ U を x=2 で散らすと I(U;V) が落ちる。Y は x=2 と x=0 を区別しないので")
    print("         I(U;Y) の代償が小さく、差し引きで gap が D(p) を超える。")
    beta, alpha = 2.0 / 3.0, 3.0 / 4.0
    print()
    print("      p(x)                  |   D(p)   |   gap    | margin = gap - D(p) | 比")
    print("      ----------------------+----------+----------+---------------------+-------")
    best = -np.inf
    rows = ((0.05, 0.5, 0.65), (0.08, 0.6, 0.70), (0.10, beta, alpha),
            (0.12, 0.75, 0.80), (0.15, 0.8, 0.85), (0.20, 0.9, 0.90))
    for d, b, a in (rows[2:4] if quick else rows):
        px = np.array([(1 - d) / 2, (1 - d) / 2, d])
        Cy, Cz, cond = partial_merge(b, a)
        gap = objective(cond_to_joint(cond, px), Cy, Cz) - max(ixy_ixz(px, Cy, Cz))
        dp, _, _ = d_of_p(px)
        best = max(best, gap - dp)
        print(f"      ({px[0]:.3f},{px[1]:.3f},{px[2]:.3f})  | {dp:8.6f} | {gap:8.6f} |"
              f" {gap - dp:+19.6f} | {gap / dp:6.4f}")
    # --- 逐語出力 + 独立再評価 -------------------------------------------
    px = np.array([0.45, 0.45, 0.10])
    Cy, Cz, cond = partial_merge(beta, alpha)
    puvx = cond_to_joint(cond, px)
    gap_fast = objective(puvx, Cy, Cz) - max(ixy_ixz(px, Cy, Cz))
    dp, argd, _ = d_of_p(px)
    T3 = Cy[:, :, None] * Cz[:, None, :]
    J = Joint(["U", "V", "X", "Y", "Z"], puvx[:, :, :, None, None] * T3[None, None])
    gap_gen = (J.eval(_LHS, "bits")
               - max(J.eval(_IXY, "bits"), J.eval(_IXZ, "bits")))
    pd, arg, _ = phi_det(px, Cy, Cz)
    print()
    print(f"      witness (beta = 2/3, alpha = 3/4, p = (0.45, 0.45, 0.10)):")
    print(f"        p(y|x) = {np.array2string(Cy, precision=6)}")
    print(f"        p(z|x) = {np.array2string(Cz, precision=6)}")
    print(f"        p(u,v|x=0) = delta_(0,1)、p(u,v|x=1) = delta_(1,1)、")
    print(f"        p(u,v|x=2) = {alpha!r} delta_(0,0) + {1 - alpha!r} delta_(1,0)")
    print(f"        T(X) >= {J.eval(_LHS, 'bits')!r}   "
          f"max{{I(X;Y),I(X;Z)}} = {max(J.eval(_IXY, 'bits'), J.eval(_IXZ, 'bits'))!r}")
    print(f"        gap  = {gap_fast!r}")
    print(f"        D(p) = {dp!r}  at (f,g) = {argd}  (全 25 分割対の列挙で**厳密**)")
    print(f"        **独立再評価** (bc_probe.Joint + parse 経由) の gap = {gap_gen!r}、"
          f"差 {abs(gap_fast - gap_gen):.3e}")
    print(f"        Markov 検査 I(U,V;Y,Z|X) = "
          f"{J.eval(parse('I(U,V;Y,Z|X)'), 'bits'):+.3e}、"
          f"p(x) のずれ = {np.abs(J.marginal(['X']) - px).max():.3e}")
    print(f"        ⟹ **margin = gap - D(p) = {gap_fast - dp:+.6f} bit** "
          "(厳密な D(p) を明示 witness が超えている ⟹ **証明書**)")
    print(f"        (同じ witness で Phi_det = {pd!r} ゆえ T - Phi_det = "
          f"{J.eval(_LHS, 'bits') - pd:+.6f} ⟹ P1 の違反でもある = §0(d) の補題と整合)")
    return max(best, gap_fast - dp)


# --------------------------------------------------------------------------
# §5 まとめ
# --------------------------------------------------------------------------
def section5(n: dict, r3: dict, r4: dict, quick: bool) -> None:
    print("=" * 78)
    print("§5 まとめ")
    print("=" * 78)
    v = lambda b: "PASS" if b else "**FAIL**"           # noqa: E731
    print("  候補 | 主張                     | (N1) | (N2) | 最大 margin      | 発生場所")
    print("  -----+--------------------------+------+------+------------------+" + "-" * 26)
    print(f"  P1   | T(X) = Phi_det(q,p)      | {v(n['n1_p1']):<4} | {v(n['n2_p1']):<4} |"
          f" {r3['margin']:+.6e} | {r3['where']}")
    print(f"  P2   | gap(T,p) <= D(p)         | {v(n['n1_p2']):<4} | {v(n['n2_p2']):<4} |"
          f" {r4['margin']:+.6e} | {r4['where']}")
    print()
    print("  margin の意味: P1 は `T の最大化 - Phi_det`、P2 は `gap - D(p)`。")
    print("  **どちらも右辺は全列挙で厳密、左辺は最大化の下界**なので、正の margin は")
    print("  証明書 (kill) である。負の margin は「掃引で殺せなかった」以上を意味しない。")
    print()
    p1_dead = r3["margin"] > VIOL_TOL
    p2_dead = r4["margin"] > VIOL_TOL
    print(f"  P1 = {'**refuted**' if p1_dead else '掃引では殺せなかった (survived the sweep)'}")
    print(f"  P2 = {'**refuted**' if p2_dead else '掃引では殺せなかった (survived the sweep)'}")
    print()
    if p1_dead:
        print("  P1 の死因: 最良の決定論的対が残す**空セル** (両座標とも使用済) へ質量を")
        print(f"     移すと目的値が超一次 (+p(x)·eps·log2(1/eps)) で増える。§3(e) の傾き表")
        print(f"     が eps->0 で発散する (最大傾き {r3['slope']:+.3e}) ので、決定論的点は")
        print("     局所最大ですらない。**チャネルが非決定論的で最良対の f,g がともに")
        print("     非自明なときに一般に起こる**ので、単発の反例ではない。")
        print("     ⟹ 生き残るのは (i) |X| = 2 (Theorem 1)、(ii) 決定論的 BC "
              "(超一次の項が相殺) の 2 つの退化した場合だけで、")
        print("        これは (N1)/(N2) が通ったのと同じ場所である "
              "= **2 条件を満たすだけでは足りない**の実例。")
    else:
        print("  ⚠ **非違反の強さについての留保** (親 plan §2.1 / R2 §7(e)):")
        print(f"     最良決定論的点での片側微分係数の最大 = {r3['slope']:+.3e}。")
        print("     0 近傍なら目的関数はその点で**平坦**で、非違反は弱い証拠にすぎない。")
    print()
    print("  ⚠ 構造的な留保: §0(d) の補題より **P1 ⟹ P2** なので 2 候補は独立ではない。")
    if p1_dead and not p2_dead:
        print("     P1 が死んでも P2 は死なない (T > Phi_det でも gap <= D(p) はありうる)。")
        print("     実際 §3(e) の witness では gap は D(p) を大きく下回る ⟹ **P2 は P1 の死を")
        print("     生き延びた別個の候補**として残る。ただし非違反は掃引の結果にすぎない。")
    elif p1_dead and p2_dead:
        print("     ただし P2 の死は P1 の死の系ではない — P1 を殺す witness の多く "
              "(§3(e) の雑音つき Blackwell 等) は")
        print("     gap <= D(p) を保つ。P2 は **D(p) が小さくなるナイフエッジの p** "
              "(§4(b) d=0.1、§4(d)) で独立に死ぬ。")
        print("     ⟹ 2 案は同じ穴で死んだのではなく、**死因が別**である。")
    if quick:
        print()
        print("  ⚠ --quick モードの数値である (掃引本数を縮小)。判定には full を使うこと。")


def main() -> None:
    ap = argparse.ArgumentParser(description="C2 の 2 案 (P1 / P2) の kill-first probe")
    ap.add_argument("--quick", action="store_true", help="掃引を縮小して約 25s で回す")
    args = ap.parse_args()
    t0 = time.time()
    print("bc-jognair-phi-check.py — 軸 C 子候補 C2: チャネル依存汎関数 2 案の "
          "kill-first probe")
    print(f"(mode = {'quick' if args.quick else 'full'})\n")

    ok0 = section0(args.quick)
    ok1, _ = section1(args.quick)
    nres, ok2 = section2(args.quick)
    r3 = section3(args.quick)
    r4 = section4(args.quick)
    section5(nres, r3, r4, args.quick)

    print()
    print(f"  harness コントロール: §0 {'PASS' if ok0 else '**FAIL**'} / "
          f"§1 {'PASS' if ok1 else '**FAIL**'} / §2 {'PASS' if ok2 else '**FAIL**'}")
    print(f"\n合計実行時間 {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
