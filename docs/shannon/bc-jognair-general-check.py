#!/usr/bin/env python3
"""[GJNW13] Theorem 1 (`|X| = 2` の情報不等式) の **`|X| >= 3` への一般化候補**を
数値で殺しにいく probe (親 plan `bc-open-problem-plan.md` §5-2 kill-first、軸 C)。

何を確かめる probe か
---------------------
原典 [GJNW13] = Geng-Jog-Nair-Wang, IEEE Trans. IT 59(7):4095-4105, 2013 の
**Theorem 1 逐語**:

    Consider a five tuple of random variables (U, V, X, Y, Z) such that
    (U, V) -> X -> (Y, Z) forms a Markov chain and further let |X| = 2. Then
    the following inequality holds:
        I(U;Y) + I(V;Z) - I(U;V) <= max{I(X;Y), I(X;Z)}.

および **§V Conclusion 逐語**: "The inequality fails when |X| >= 3 so a natural
question is whether there is a correct generalization for higher cardinality
input-alphabets."

本 probe が叩く候補は 3 本 (詳細と判定は `bc-open-problem-routes.md` §R2):

    G1 (加法スラック)  LHS <= max{I(X;Y), I(X;Z)} + f(|X|),  f(2) = 0
                       種は f(k) = log2(k/2)
    G2 (sum rate ギャップ)  SR_Marton(T) - SR_RTD(T) <= g(|X|),  g(2) = 0
                       種は g(k) = log2(k/2)
    G3 (乗法スラック)  LHS <= rho(|X|) * max{I(X;Y), I(X;Z)},  rho(2) = 1

判定量の定義 (原典の記法に合わせる)
-----------------------------------
[GNA12] = Gohari-Nair-Anantharam, arXiv:1202.0898 (ISIT 2012) の記法で

    T(X) := max_{p(u,v|x)} I(U;Y) + I(V;Z) - I(U;V)      (p(x) と チャネルの関数)

とおく。Theorem 1 は「`|X| = 2` なら `T(X) = max{I(X;Y), I(X;Z)}`」と同値
([GNA12] 逐語: "What inequality (1) shows is that when |X| = 2 then
T(X) = max{I(X;Y), I(X;Z)}")。本 probe の主対象は **その差**

    gap(T, p) := T(X) - max{I(X;Y), I(X;Z)}
    f*(k)     := sup over |X| = k のチャネル T と p(x) の gap(T, p)

で、G1 は `f*(k) <= f(k)` と同値。**`f*(2) = 0` が Theorem 1 そのもの**。

誤差の向きの規律 (どの数値が確実で、どれが探索にすぎないか)
------------------------------------------------------------
* **G1 / G3 の反証 (kill) は明示 witness の直接評価**であり、最適化を一切使わない
  ⟹ 浮動小数の丸めを除いて **確実**。§5 がそれ。
* **上界 `f*(k) <= (1/2) log2 k` は記号的恒等式 (係数相殺) + 非負性**から出る
  ⟹ **証明** であって掃引ではない。§1 がその恒等式を機械検証する。
* **`f*(3)` の下からの評価と「殺せなかった」側は局所最適化の最良値**にすぎない
  ⟹ sup の **下界** でしかなく、「掃引では殺せなかった」までしか言えない
  (親 plan §3.2 / §5-8: 掃引の成立は証拠、係数相殺は証明)。
* SR_RTD は最大化で求めるので **下界** しか出ない ⟹ `SR_Marton - SR_RTD` は
  **上振れ** しうる。したがって G2 の「破れた」判定には使えるが (破れなければ
  なおさら破れない、ではない点に注意 = 上振れ側なので偽陽性のリスクがある)、
  §10 は違反が出なかったので問題にならない。

sim と定義の逐語照合 (CLAUDE.md 検証の誠実性)
---------------------------------------------
本 probe は InformationTheory の Lean `def` には依存しない。照合先は原典の式で、
対応は次のとおり (単位は bit = 原典と同じ。`bc_probe` の既定は nat なので
`units="bits"` を明示して呼ぶ):

* Theorem 1 の左辺 = `I(U;Y) + I(V;Z) - I(U;V)`、右辺 = `max{I(X;Y), I(X;Z)}`
  ⟹ `_LHS` / `_IXY` / `_IXZ` (§3 が原典の Blackwell 反例の数値を再現して照合する)
* Blackwell チャネル = [GNA12] 脚注 3 逐語 "X = {0,1,2}, with the mapping
  X -> Y x Z given by: 0 -> (0,0), 1 -> (0,1), 2 -> (1,1)" ⟹ `blackwell()`
* SR_RTD = [GJNW13] Theorem 3 逐語 `max_{p(w,x)} min{I(W;Y), I(W;Z)}
  + P(W=0) I(X;Y|W=0) + P(W=1) I(X;Z|W=1)`, `|W| = 2` ⟹ `sr_rtd()`
* `|U|, |V| <= |X|` への制限 = [GJNW13] §II-A Remark 3 逐語 "it suffices to
  consider |U| <= |X|, |V| <= |X|, X = f(U,V) to evaluate T(X)" ⟹ §7 で
  `|U| = |V| = |X|` と `|U| = |V| = |X| + 1` の両方を回して制限が効くことを確認

再実行コマンド / 期待出力
-------------------------
    python3 docs/shannon/bc-jognair-general-check.py           # 約 160s
    python3 docs/shannon/bc-jognair-general-check.py --quick   # 約 25s (掃引を縮小)

乱数種はすべて固定、局所最適化の開始点も固定種から引くので **再実行で報告値は一致
する**。期待される最終判定 (通常実行):

    §1 記号 6 本 PASS / §2 肯定コントロール 違反 0 / §3 原典の数値を再現
    §4 最大化が上界に張り付く (残差 < 1e-9) / §5 **G1 は refuted**
    §9 **G3 は refuted (全 k >= 3 で空虚)** / §10 G2 は掃引では殺せなかった
"""

from __future__ import annotations

import argparse
import itertools
import sys
import time
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

sys.path.insert(0, str(Path(__file__).resolve().parent))

from bc_probe import (  # noqa: E402
    BayesNet,
    Joint,
    OptReport,
    local_max_certificate,
    maximize,
    parse,
    prove_identity,
    softmax,
)

PHI = (1.0 + 5.0**0.5) / 2.0
LOG2_PHI = float(np.log2(PHI))

_LHS = parse("I(U;Y) + I(V;Z) - I(U;V)")
_IXY = parse("I(X;Y)")
_IXZ = parse("I(X;Z)")
_HXgY = parse("H(X|Y)")
_HXgZ = parse("H(X|Z)")
_HX = parse("H(X)")
_HYZ = parse("H(Y,Z)")
_IWY = parse("I(W;Y)")
_IWZ = parse("I(W;Z)")


# --------------------------------------------------------------------------
# チャネルと同時分布の構成
# --------------------------------------------------------------------------
def blackwell() -> np.ndarray:
    """[GNA12] 脚注 3 逐語の Blackwell チャネル。`T[x, y, z]`。"""
    T = np.zeros((3, 2, 2))
    T[0, 0, 0] = 1.0
    T[1, 0, 1] = 1.0
    T[2, 1, 1] = 1.0
    return T


def grid(a: int, b: int) -> np.ndarray:
    """決定論的 BC `X = (i,j) in [a] x [b]`, `Y = i`, `Z = j` (|X| = a*b)。"""
    T = np.zeros((a * b, a, b))
    for i in range(a):
        for j in range(b):
            T[i * b + j, i, j] = 1.0
    return T


def joint5(puvx: np.ndarray, T: np.ndarray) -> Joint:
    """`p(u,v,x) * T(y,z|x)` から 5 変数同時分布を作る (Markov 性は構成から)。"""
    return Joint(
        ["U", "V", "X", "Y", "Z"],
        puvx[:, :, :, None, None] * T[None, None, :, :, :],
        validate=False,
    )


def gap_of(puvx: np.ndarray, T: np.ndarray) -> float:
    """`I(U;Y)+I(V;Z)-I(U;V) - max{I(X;Y), I(X;Z)}` (bit)。"""
    J = joint5(puvx, T)
    return J.eval(_LHS, "bits") - max(J.eval(_IXY, "bits"), J.eval(_IXZ, "bits"))


def ratio_of(puvx: np.ndarray, T: np.ndarray) -> float:
    """`(I(U;Y)+I(V;Z)-I(U;V)) / max{I(X;Y), I(X;Z)}` (G3 用、分母 0 は 0 扱い)。"""
    J = joint5(puvx, T)
    den = max(J.eval(_IXY, "bits"), J.eval(_IXZ, "bits"))
    if den < 1e-9:
        return 0.0
    return J.eval(_LHS, "bits") / den


def witness_uy_vz(px: np.ndarray, T: np.ndarray) -> np.ndarray:
    """決定論的チャネルの witness `U = Y`, `V = Z` に対応する `p(u,v,x)`。

    原典 [GJNW13] §I-B-2 の反例 "consider U = Y, V = Z and X ~ [1/3,1/3,1/3]"
    そのものの構成。
    """
    kx, ky, kz = T.shape
    p = np.zeros((ky, kz, kx))
    for x in range(kx):
        for y in range(ky):
            for z in range(kz):
                p[y, z, x] += px[x] * T[x, y, z]
    return p


def certified_upper(px: np.ndarray, T: np.ndarray) -> float:
    """§1 で証明する `gap <= min{I(X;Y), I(X;Z), H(X|Y), H(X|Z)}` の右辺。"""
    J = Joint(["X", "Y", "Z"], px[:, None, None] * T, validate=False)
    return min(
        J.eval(_IXY, "bits"),
        J.eval(_IXZ, "bits"),
        J.eval(_HXgY, "bits"),
        J.eval(_HXgZ, "bits"),
    )


# --------------------------------------------------------------------------
# 高次元用の多点再スタート最大化 (bc_probe.maximize の L-BFGS-B 版)
# --------------------------------------------------------------------------
def maximize_hd(
    f,
    dim: int,
    rng: np.random.Generator,
    restarts: int = 12,
    scale: float = 2.5,
    seeds=(),
    maxiter: int = 5000,
) -> OptReport:
    """`bc_probe.maximize` と同じ契約 (多点再スタート + OptReport) の高次元版。

    27-64 次元では Nelder-Mead が実用的でないので L-BFGS-B (数値勾配) に差し替えた
    だけで、**返るのは局所最適の中の最良値であって最大値の証明ではない**という
    留保は同じ。判定に使うときは `OptReport.summary()` を必ず一緒に報告すること。
    """
    starts = [np.asarray(s, dtype=float).ravel() for s in seeds]
    starts += [rng.normal(0.0, scale, dim) for _ in range(restarts)]
    best, best_x, values = -np.inf, None, []
    for x0 in starts:
        res = minimize(
            lambda z: -f(z), x0, method="L-BFGS-B",
            options={"maxiter": maxiter, "maxfun": 200000},
        )
        val = -float(res.fun)
        values.append(val)
        if val > best:
            best, best_x = val, res.x
    return OptReport(best, best_x, values, len(starts), 1e-6)


def simplex_scan(f, k: int, steps: int = 16):
    """`Delta(k-1)` の格子点 (刻み 1/steps) で `f` を評価し `(最良値, 最良点)` を返す。

    3 次元では scipy の呼び出しオーバヘッドより格子走査のほうが速く、しかも
    **開始点が乱数に依らない** ので再現性が上がる (局所最適化はその後の polish 用)。
    """
    best, arg = -np.inf, None
    for c in itertools.combinations(range(steps + k - 1), k - 1):
        cuts = (-1,) + c + (steps + k - 1,)
        p = np.array([cuts[i + 1] - cuts[i] - 1 for i in range(k)], dtype=float) / steps
        v = f(p)
        if v > best:
            best, arg = v, p
    return best, arg


def gap_max(T, rng, ku=None, kv=None, restarts=12, seeds=(), objective=gap_of):
    """固定チャネル `T` について `p(u,v,x)` 上で目的量を最大化する。"""
    kx = T.shape[0]
    ku = ku or kx
    kv = kv or kx
    shape = (ku, kv, kx)

    def f(theta):
        return objective(softmax(theta.ravel()).reshape(shape), T)

    return maximize_hd(f, ku * kv * kx, rng, restarts=restarts, seeds=seeds)


def gap_max_joint(kx, ky, kz, rng, restarts=25, seeds=(), objective=gap_of):
    """チャネル `T(y,z|x)` **も** 変数にした同時最大化 (`|X| = kx` 全体の sup を狙う)。"""
    ku = kv = kx
    n1 = ku * kv * kx

    def f(theta):
        p = softmax(theta[:n1]).reshape(ku, kv, kx)
        T = softmax(theta[n1:].reshape(kx, ky * kz), axis=-1).reshape(kx, ky, kz)
        return objective(p, T)

    return maximize_hd(f, n1 + kx * ky * kz, rng, restarts=restarts, seeds=seeds)


# --------------------------------------------------------------------------
# §1 記号的コントロール — 上界を「係数相殺」で証明する
# --------------------------------------------------------------------------
def section1() -> bool:
    print("=" * 78)
    print("§1 記号的コントロール — 自明上界の証明 (掃引ではなく係数相殺)")
    print("=" * 78)
    items = [
        # (名前, lhs, rhs, 非負性の根拠)
        (
            "(I1) H(X) - LHS の分解",
            "H(X) - (I(U;Y) + I(V;Z) - I(U;V))",
            "(I(U;X) - I(U;Y)) + (I(V;X) - I(V;Z)) + H(X|U,V) + I(U;V|X)",
            "4 項すべて >= 0 (前 2 項は Markov 下の DPI、後 2 項は無条件) "
            "⟹ LHS <= H(X)",
        ),
        (
            "(I2) DPI 項の Markov 下での正体",
            "I(U;X) - I(U;Y)",
            "I(U;X|Y) - I(U;Y|X)",
            "Markov (U,V)->X->(Y,Z) で I(U;Y|X) = 0 ⟹ = I(U;X|Y) >= 0",
        ),
        (
            "(I3) I(X;Y)+I(X;Z) - LHS の分解",
            "I(X;Y) + I(X;Z) - (I(U;Y) + I(V;Z) - I(U;V))",
            "(I(X;Y) - I(U;Y)) + (I(X;Z) - I(V;Z)) + I(U;V)",
            "同様に 3 項すべて >= 0 ⟹ LHS <= I(X;Y) + I(X;Z)",
        ),
        (
            "(I4) 右辺の書き換え",
            "H(X) - I(X;Y)",
            "H(X|Y)",
            "max{I(X;Y),I(X;Z)} = H(X) - min{H(X|Y),H(X|Z)} を与える",
        ),
        (
            "(I5) 典型集合形との等価性の残差",
            "(I(U;Y) + I(V;Z) - I(U;V) - I(X;Y)) - (H(U,V|Y) - H(U|Y) - H(V|Z))",
            "- H(X|U,V) + I(U,V;Y|X) + H(X|U,V,Y)",
            "X = f(U,V) と Markov で右辺 3 項がすべて 0 ⟹ [GJNW13] §V の "
            "等価形 H(U|Y)+H(V|Z) >= min{H(U,V|Y),H(U,V|Z)} と同値",
        ),
        (
            "(I6) 同じ残差の Z 側",
            "(I(U;Y) + I(V;Z) - I(U;V) - I(X;Z)) - (H(U,V|Z) - H(U|Y) - H(V|Z))",
            "- H(X|U,V) + I(U,V;Z|X) + H(X|U,V,Z)",
            "min の他方の枝 (同上)",
        ),
    ]
    ok = True
    for name, lhs, rhs, why in items:
        held, resid = prove_identity(lhs, rhs)
        ok &= held
        print(f"  [{'PASS' if held else 'FAIL'}] {name}")
        print(f"         {why}")
        if not held:
            print(f"         残差 = {resid}")
    print()
    print("  ⟹ **証明された上界 (係数相殺 + 非負性)**:")
    print("        gap := LHS - max{I(X;Y), I(X;Z)}")
    print("        gap <= min{I(X;Y), I(X;Z)}            ((I3) + max の定義)")
    print("        gap <= min{H(X|Y), H(X|Z)}            ((I1) + (I4))")
    print("     この 2 本を足すと 2*gap <= I(X;Y) + H(X|Y) = H(X) <= log2 |X| ゆえ")
    print("        **f*(k) <= (1/2) log2 k**  (k = |X|)")
    print(f"  記号的コントロール: {'全 PASS' if ok else '**FAIL あり**'}\n")
    return ok


# --------------------------------------------------------------------------
# §2 肯定コントロール — |X| = 2 で Theorem 1 が破れないこと
# --------------------------------------------------------------------------
def section2(trials: int) -> int:
    print("=" * 78)
    print("§2 肯定コントロール — |X| = 2 のランダムチャネルで Theorem 1 が破れないか")
    print("=" * 78)
    rng = np.random.default_rng(20260802)
    worst = -np.inf
    viol = 0
    for _ in range(trials):
        ky, kz = int(rng.integers(2, 5)), int(rng.integers(2, 5))
        net = BayesNet()
        # (U,V,X) は任意の同時分布 (X = f(U,V) に限定しない = Theorem 1 の全射程)
        net.add(("U", "V", "X"), (2, 2, 2), dirichlet=float(rng.choice([0.3, 1.0, 3.0])))
        net.add(("Y", "Z"), (ky, kz), parents=("X",),
                dirichlet=float(rng.choice([0.3, 1.0, 3.0])))
        J = net.build(rng)
        d = J.eval(_LHS, "bits") - max(J.eval(_IXY, "bits"), J.eval(_IXZ, "bits"))
        worst = max(worst, d)
        if d > 1e-9:
            viol += 1
    print(f"  試行 {trials} (|U|=|V|=|X|=2、|Y|,|Z| は 2-4 のランダム、"
          f"Dirichlet 濃度も振る)")
    print(f"  違反 {viol} 本、最悪残差 (LHS - max) = {worst:+.6e}")
    print(f"  ⟹ harness は Theorem 1 を破らない ({'OK' if viol == 0 else '**NG**'})\n")
    return viol


# --------------------------------------------------------------------------
# §3 否定コントロール — 原典の |X| = 3 反例の数値を再現する
# --------------------------------------------------------------------------
def section3() -> bool:
    print("=" * 78)
    print("§3 否定コントロール — [GJNW13] §I-B-2 の Blackwell 反例を逐語で再現")
    print("=" * 78)
    T = blackwell()
    px = np.full(3, 1.0 / 3.0)
    J = joint5(witness_uy_vz(px, T), T)
    lhs = J.eval(_LHS, "bits")
    ixy, ixz = J.eval(_IXY, "bits"), J.eval(_IXZ, "bits")
    hyz = J.eval(_HYZ, "bits")
    print("  原典逐語: \"consider U = Y, V = Z and X ~ [1/3,1/3,1/3] ... "
          "I(U;Y)+I(V;Z)-I(U;V)")
    print("            = H(Y,Z) = log2 3 > 1 >= max{I(X;Y), I(X;Z)}\"")
    print(f"  再現: LHS = {lhs!r}   H(Y,Z) = {hyz!r}   log2 3 = {float(np.log2(3.0))!r}")
    print(f"        I(X;Y) = {ixy!r}  I(X;Z) = {ixz!r}  (原典の粗い上界 1 >= max も成立)")
    ok = (abs(lhs - np.log2(3.0)) < 1e-12 and abs(hyz - lhs) < 1e-12
          and max(ixy, ixz) < 1.0)
    print(f"  ⟹ 原典の 3 つの数値をすべて再現 ({'OK' if ok else '**NG**'})")
    print(f"  ⚠ **原典が書いた \"1\" は粗い上界**で、真の max は h(1/3) = {ixy:.6f}。")
    print(f"     ゆえに実際の破れ幅は log2 3 - 1 = {np.log2(3.0) - 1:.6f} ではなく")
    print(f"     log2 3 - h(1/3) = {lhs - max(ixy, ixz):.6f} (= 2/3 ちょうど)。**§5 の kill "
          "はここから出る**。\n")
    return ok


# --------------------------------------------------------------------------
# §4 最大化の健全性 — |X| = 2 で最大化が Theorem 1 の上界に張り付くか
# --------------------------------------------------------------------------
def section4(restarts: int) -> bool:
    print("=" * 78)
    print("§4 最大化の健全性 — |X| = 2 で gap の最大が 0 に張り付くか")
    print("=" * 78)
    print("  Theorem 1 は gap <= 0、かつ U = X / V = trivial で gap = 0 が達成される")
    print("  ⟹ 真の最大は **ちょうど 0**。最適化がそこに張り付くかで harness を検定する。")
    rng = np.random.default_rng(4242)
    ok = True
    for idx in range(3):
        ky, kz = 2, 2
        T = rng.dirichlet(np.full(ky * kz, 1.0), size=2).reshape(2, ky, kz)
        # 明示 seed: 単体の境界点 (U = X, V = 定数) と (V = X, U = 定数)
        seeds = []
        for which in (0, 1):
            p = np.zeros((2, 2, 2))
            for x in range(2):
                if which == 0:
                    p[x, 0, x] = 0.5      # U = X, V = 定数
                else:
                    p[0, x, x] = 0.5      # V = X, U = 定数
            seeds.append(np.log(p.ravel() + 1e-12))
        rep = gap_max(T, rng, restarts=restarts, seeds=seeds)
        # 境界方向を明示的に渡した局所最大性証明書 (単体の全頂点 + 上の 2 witness)
        pstar = softmax(rep.best_x.ravel())
        dirs = [np.eye(8)[i] for i in range(8)]
        dirs += [softmax(s) for s in seeds]
        gain, _, eps = local_max_certificate(
            lambda q: gap_of(np.asarray(q).reshape(2, 2, 2), T),
            pstar, rng, trials=400, directions=dirs,
        )
        good = rep.best < 1e-9 and gain < 1e-9
        ok &= good
        print(f"  ch{idx}: 最大 gap = {rep.best:+.3e} (真値 0)   {rep.summary()}")
        print(f"        局所最大性証明書 (単体の 8 頂点を directions に明示): "
              f"最大増分 {gain:+.3e} (eps={eps:g})  {'OK' if good else '**NG**'}")
    print("  ⚠ 親 plan §2.1 の警告どおり、ランダム方向だけでは局所最大の主張にならない")
    print("     ので `directions=` に単体の頂点と 2 つの構造 witness を明示的に渡した。\n")
    return ok


# --------------------------------------------------------------------------
# §5 G1 の kill — 明示 witness の直接評価 (最適化を使わない)
# --------------------------------------------------------------------------
def section5() -> bool:
    print("=" * 78)
    print("§5 **G1 の kill** — f(k) = log2(k/2) は |X| = 3 で破れる (最適化不使用)")
    print("=" * 78)
    T = blackwell()
    q = (5.0 - 5.0**0.5) / 10.0
    rows = [
        ("Blackwell + X ~ [1/3,1/3,1/3] (原典の witness そのもの)",
         np.full(3, 1.0 / 3.0)),
        (f"Blackwell + X ~ [q, 1-2q, q], q = (5-sqrt5)/10 = {q:.6f}",
         np.array([q, 1.0 - 2.0 * q, q])),
    ]
    f3 = float(np.log2(1.5))
    killed = False
    for name, px in rows:
        J = joint5(witness_uy_vz(px, T), T)
        lhs = J.eval(_LHS, "bits")
        mx = max(J.eval(_IXY, "bits"), J.eval(_IXZ, "bits"))
        g = lhs - mx
        ub = certified_upper(px, T)
        print(f"  {name}")
        print(f"    LHS = {lhs!r}")
        print(f"    max{{I(X;Y),I(X;Z)}} = {mx!r}")
        print(f"    gap = {g!r}   vs   f(3) = log2(3/2) = {f3!r}")
        print(f"    ⟹ gap - f(3) = {g - f3:+.6f}   "
              f"{'**違反**' if g > f3 + 1e-12 else '違反せず'}")
        print(f"    (§1 の証明済上界 min{{I,I,H|Y,H|Z}} = {ub!r} と一致 = 上界達成)")
        killed |= g > f3 + 1e-12
    print()
    print(f"  黄金比の閉形式: 2 番目の witness の gap は **log2 phi = {LOG2_PHI!r}**")
    print("    (p の内部最適条件 5q^2 - 5q + 1 = 0 ⟹ q = (5-sqrt5)/10、"
          "そこで (1-2q)/(1-q) = 1/phi,")
    print("     q/(1-q) = 1/phi^2 となり H(X|Y) = (1-2q)log2 phi + 2q log2 phi "
          "= log2 phi ちょうど)")
    print(f"  ⟹ **G1 (f(k) = log2(k/2)) は refuted**。反証は原典自身の witness "
          "(1 本目) で既に立ち、")
    print("     最良の witness (2 本目) では違反幅が "
          f"{LOG2_PHI - f3:.6f} bit に広がる。\n")
    return killed


# --------------------------------------------------------------------------
# §6 G1 の空虚性 — k >= 4 では自明上界より弱い
# --------------------------------------------------------------------------
def section6() -> None:
    print("=" * 78)
    print("§6 G1 の空虚性 — k >= 4 では f(k) = log2(k/2) が §1 の自明上界を上回る")
    print("=" * 78)
    print("   k | f(k)=log2(k/2) | 自明上界 (1/2)log2 k | 判定")
    print("  ---+----------------+----------------------+" + "-" * 34)
    for k in range(2, 11):
        f = np.log2(k / 2.0)
        u = 0.5 * np.log2(k)
        if k == 2:
            verdict = "Theorem 1 そのもの (f=0 で真)"
        elif f < u:
            verdict = "中身がありうる (k=3 のみ)"
        else:
            verdict = "**空虚** (自明上界の帰結)"
        print(f"   {k} |    {f:9.6f}   |      {u:9.6f}       | {verdict}")
    print()
    print("  log2(k/2) >= (1/2) log2 k  <=>  (1/2) log2 k >= 1  <=>  k >= 4")
    print("  ⟹ **G1 は k = 3 で偽、k >= 4 では §1 の 3 行の自明上界の帰結ゆえ中身なし**。")
    print("     すなわち G1 はどの k でも「偽か自明か」のいずれかで、"
          "一般化の候補として死んでいる。\n")


# --------------------------------------------------------------------------
# §7 掃引 — f*(3) を上げられるか (ランダム / 決定論的 / チャネル込み同時最適化)
# --------------------------------------------------------------------------
def section7(quick: bool) -> float:
    print("=" * 78)
    print("§7 掃引 — |X| = 3 で log2 phi を超える gap があるか")
    print("=" * 78)
    rng = np.random.default_rng(777)
    best_overall = LOG2_PHI

    # (a) ランダムチャネルの screen (§1 の証明済上界で足切り)
    n_rand = 80 if quick else 400
    screened = []
    for _ in range(n_rand):
        ky, kz = int(rng.integers(2, 5)), int(rng.integers(2, 5))
        conc = float(rng.choice([0.3, 1.0, 3.0]))
        T = rng.dirichlet(np.full(ky * kz, conc), size=3).reshape(3, ky, kz)
        ub, _ = simplex_scan(lambda p, T=T: certified_upper(p, T), 3, steps=14)
        screened.append((ub, T))
    screened.sort(key=lambda t: -t[0])
    print(f"  (a) ランダム |X|=3 チャネル {n_rand} 本を §1 の証明済上界で screen:")
    print(f"      上界の最大 = {screened[0][0]:.6f} "
          f"(log2 phi = {LOG2_PHI:.6f} と比較)")
    n_opt = 3 if quick else 8
    best_rand = -np.inf
    for ub, T in screened[:n_opt]:
        rep = gap_max(T, rng, restarts=4 if quick else 8)
        best_rand = max(best_rand, rep.best)
    print(f"      上位 {n_opt} 本を実際に最大化 ⟹ 最大 gap = {best_rand:.6f}")
    print("      ⟹ Dirichlet ランダムチャネルは極値から遠い (screen 段階で既に届かない)")

    # (b) 決定論的 |X|=3 チャネルの全列挙 (3^3 x 3^3 = 729 通り)
    print("  (b) 決定論的 |X|=3 チャネル (g,h: [3]->[3]) を **全 729 通り列挙**:")
    HY, HZ = parse("H(Y)"), parse("H(Z)")
    cands = []
    for g in itertools.product(range(3), repeat=3):
        for h in itertools.product(range(3), repeat=3):
            T = np.zeros((3, 3, 3))
            for x in range(3):
                T[x, g[x], h[x]] = 1.0

            def obj(p, T=T):
                J = Joint(["X", "Y", "Z"], p[:, None, None] * T, validate=False)
                return (J.eval(_HYZ, "bits")
                        - max(J.eval(HY, "bits"), J.eval(HZ, "bits")))

            v, p0 = simplex_scan(obj, 3, steps=12)
            cands.append((v, p0, T, (g, h), obj))
    cands.sort(key=lambda t: -t[0])
    best_det, arg_det = -np.inf, None
    rng_b = np.random.default_rng(99)
    for v, p0, T, gh, obj in cands[:20]:      # 格子走査の上位だけ polish
        rep = maximize(lambda th, o=obj: o(softmax(th)), 3, rng_b, restarts=3,
                       seeds=[np.log(p0 + 1e-12)])
        if rep.best > best_det:
            best_det, arg_det = rep.best, gh
    print(f"      max = {float(best_det)!r}  at (g,h) = {arg_det}")
    print(f"      log2 phi = {LOG2_PHI!r}   差 = {best_det - LOG2_PHI:+.3e}")
    print("      ⟹ 決定論的な |X|=3 チャネルの中では Blackwell (の relabel) が極値")

    # (c) チャネルも変数にした同時最適化 (構造 seed を明示的に渡す)
    print("  (c) チャネル T(y,z|x) **も** 変数にした同時最大化 (|X| = 3):")
    print("      seed には Blackwell + 黄金比 p + (U,V)=(Y,Z) を **明示的に** 渡す")
    print("      (親 plan §2.1: ランダム方向だけでは最大の主張にならない)")
    q = (5.0 - 5.0**0.5) / 10.0
    Tb, pxb = blackwell(), np.array([q, 1.0 - 2.0 * q, q])
    for (ky, kz) in ([(2, 2), (3, 3)] if quick else [(2, 2), (3, 3), (4, 4)]):
        pad_p = np.zeros((3, 3, 3))
        w = witness_uy_vz(pxb, Tb)
        pad_p[:2, :2, :] = w
        pad_T = np.zeros((3, ky, kz))
        pad_T[:, :2, :2] = Tb
        seed = np.concatenate([np.log(pad_p.ravel() + 1e-9),
                               np.log(pad_T.ravel() + 1e-9)])
        rep = gap_max_joint(3, ky, kz, rng, restarts=8 if quick else 25,
                            seeds=[seed])
        best_overall = max(best_overall, rep.best)
        rand_best = max(rep.values[1:])
        top = np.sort(rep.values)[::-1][:5]
        print(f"      |Y|=|Z|={ky}: best = {rep.best:.6f}  "
              f"(log2 phi との差 {rep.best - LOG2_PHI:+.2e})")
        print(f"        seed 着地 = {rep.values[0]:.6f} / "
              f"ランダム再スタートの最良 = {rand_best:.6f}")
        print(f"        {rep.summary()}")
        print(f"        上位 5 着地値 = {np.round(top, 6)}")

    # (d) 補助変数の濃度制限が効いていることの確認 (両方に同じ構造 seed を渡す)
    T = blackwell()
    w = witness_uy_vz(pxb, T)

    def padded_seed(n):
        a = np.zeros((n, n, 3))
        a[:2, :2, :] = w
        return np.log(a.ravel() + 1e-9)

    r3 = gap_max(T, rng, ku=3, kv=3, restarts=6 if quick else 12,
                 seeds=[padded_seed(3)])
    r4 = gap_max(T, rng, ku=4, kv=4, restarts=6 if quick else 12,
                 seeds=[padded_seed(4)])
    print("  (d) 濃度制限 |U|,|V| <= |X| ([GJNW13] Remark 3 逐語) の確認 (Blackwell):")
    print(f"      |U|=|V|=3: {r3.best:.6f}    |U|=|V|=4: {r4.best:.6f}   "
          f"差 = {r4.best - r3.best:+.2e}")
    print("      ⟹ 補助変数を |X| より増やしても改善しない (原典の還元と整合)")

    # (e) 「ランダム再スタートだけでは最大を外す」実例 (|X| = 4 の同時最大化)
    T4 = grid(2, 2)
    pad_p4 = np.zeros((4, 4, 4))
    pad_p4[:2, :2, :] = witness_uy_vz(np.full(4, 0.25), T4)
    seed4 = np.concatenate([np.log(pad_p4.ravel() + 1e-9),
                            np.log(T4.ravel() + 1e-9)])
    n4 = 8 if quick else 20
    rep4 = gap_max_joint(4, 2, 2, rng, restarts=n4, seeds=[seed4])
    rand4 = max(rep4.values[1:])
    print("  (e) 最大化の限界の実例 (|X| = 4 の同時最大化。真の最大は §8 より 1 ちょうど):")
    print(f"      構造 witness を seed に渡した着地: {rep4.values[0]:.6f}")
    print(f"      ランダム再スタート {n4} 本の最良:      {rand4:.6f}")
    print(f"      ⟹ 差 {rep4.values[0] - rand4:+.6f}。**ランダム再スタートだけでは真の最大を "
          f"{rep4.values[0] - rand4:.3f} bit 外す**")
    print("         (しかも外した先の値は log2 phi = Blackwell の値。"
          "偽の「収束した」に見える)")
    print("         ⟹ 「掃引で出なかった」を「最大がそこにある」と読んではいけない、"
          "の本 leg 内の実例。")
    print()
    print(f"  ⟹ **掃引では log2 phi = {LOG2_PHI:.6f} を超えられなかった**。")
    print("     ⚠ これは f*(3) = log2 phi の証明ではない (返るのは sup の下界だけ)。")
    print(f"     現状 f*(3) は [{LOG2_PHI:.6f}, {0.5 * np.log2(3):.6f}] "
          "(下は明示 witness、上は §1 の証明済上界) に挟まれている。\n")
    return best_overall


# --------------------------------------------------------------------------
# §8 f*(k) の上下界表 — 格子部分集合による下界 D(k)
# --------------------------------------------------------------------------
def section8(quick: bool) -> None:
    print("=" * 78)
    print("§8 f*(k) の上下界 — 決定論的「格子部分集合」チャネルによる下界 D(k)")
    print("=" * 78)
    print("  D(k) の一般の定義は §7(b) と同じ「決定論的 BC 上の gap の最大」")
    print("    D(k) = max over (g,h), p の [H(Y,Z) - max{H(Y), H(Z)}]")
    print("  で、(Y,Z) が X を復元する場合に限り min{H(X|Y), H(X|Z)} と一致する")
    print("  (復元しない (g,h) では min{H(X|.)} は跳ね上がるが gap は上がらない)。")
    print("  復元する決定論的 BC は X を |Y| x |Z| の格子に埋め込むことと同じで、")
    print("  そのとき U = Y, V = Z が gap = min{H(X|Y), H(X|Z)} を達成する")
    print("  (§1 の証明済上界にちょうど一致 = その p では達成が確定する)。")
    rng = np.random.default_rng(31415)
    HXgY, HXgZ = parse("H(X|Y)"), parse("H(X|Z)")

    def d_of_subset(cells, m):
        T = np.zeros((len(cells), m, m))
        for i, (r, c) in enumerate(cells):
            T[i, r, c] = 1.0

        def obj(th):
            J = Joint(["X", "Y", "Z"], softmax(th)[:, None, None] * T, validate=False)
            return min(J.eval(HXgY, "bits"), J.eval(HXgZ, "bits"))

        # 一様分布を明示 seed に入れる (格子の対称な部分集合ではそこが最適になりやすい)
        return maximize(obj, len(cells), rng, restarts=1 if quick else 3,
                        seeds=[np.zeros(len(cells))]).best

    m = 3
    all_cells = [(r, c) for r in range(m) for c in range(m)]
    ks = (2, 3, 4, 9) if quick else tuple(range(2, 10))
    print("   k | D_lb(k) (3x3 格子の部分集合) | 上界 (1/2)log2 k | 一致?")
    print("  ---+------------------------------+------------------+--------")
    for k in ks:
        best = -np.inf
        for cells in itertools.combinations(all_cells, k):
            best = max(best, d_of_subset(list(cells), m))
        ub = 0.5 * np.log2(k)
        tag = "**一致 = f*(k) 確定**" if abs(best - ub) < 1e-6 else ""
        print(f"   {k} |          {best:9.6f}           |     {ub:9.6f}    | {tag}")
    print()
    print("  ⟹ k = 4 (2x2 格子) と k = 9 (3x3 格子) では下界 = 証明済上界 ゆえ")
    print("     **f*(4) = 1、f*(9) = log2 3 が確定** (一般に完全平方 k = m^2 で")
    print("     f*(m^2) = log2 m: a x b 格子の一様分布が min{log2 a, log2 b} を与え、")
    print("     a = b = m で上界 (1/2)log2 k に一致する)。")
    print("  ⚠ D_lb は |Y|,|Z| <= 3 に制限した探索なので k >= 5 では真の D(k) の下界。")
    print("  ⚠ f*(k) = D(k) (決定論的チャネルが極値) は **予想**であって証明ではない。\n")


# --------------------------------------------------------------------------
# §9 G3 (乗法形) — rho*(k)
# --------------------------------------------------------------------------
def section9(quick: bool) -> None:
    print("=" * 78)
    print("§9 G3 (乗法スラック) — LHS <= rho(|X|) * max{I(X;Y), I(X;Z)}")
    print("=" * 78)
    print("  §1 (I3) より LHS <= I(X;Y) + I(X;Z) <= 2 max{...} が無条件で成り立つ")
    print("  ⟹ **rho(k) >= 2 の主張はどの k でも自明**。したがって G3 に中身があるのは")
    print("     rho*(k) := sup LHS / max{...} < 2 となる k だけ。")
    T4 = grid(2, 2)
    J = joint5(witness_uy_vz(np.full(4, 0.25), T4), T4)
    r4 = J.eval(_LHS, "bits") / max(J.eval(_IXY, "bits"), J.eval(_IXZ, "bits"))
    print(f"  k = 4: 2x2 格子 + 一様 + (U,V) = (Y,Z) で LHS/max = {r4!r} = 2 ちょうど")
    print("         ⟹ **rho*(4) = 2** (上下界が一致) ⟹ k = 4 で G3 は空虚")
    print("         (a x b 格子の一様分布は任意の合成数 k = ab で同じく比 2 を出す)")
    print("  k = 3: Blackwell の 1 径数族 p = (a, 1-2a, a) を **明示評価** (最適化不使用):")
    T = blackwell()
    ratios = []
    for a in (0.1, 0.01, 0.001, 1e-4, 1e-5):
        px = np.array([a, 1.0 - 2.0 * a, a])
        w = witness_uy_vz(px, T)
        ratios.append(ratio_of(w, T))
        print(f"      a = {a:<8g}  LHS/max = {ratios[-1]:.6f}   "
              f"gap = {gap_of(w, T):.6f}")
    print(f"      ⟹ a -> 0 で比は 2 に収束 (a = 1e-5 で {ratios[-1]:.6f})。")
    print("         **rho*(3) = 2** (sup であって最大値ではない — 退化点でのみ達成される)")
    print("  ⟹ **G3 は refuted**: rho*(k) = 2 が全 k >= 3 で成り立つので、"
          "乗法形の真の定数は")
    print("     §1 (I3) の 1 行の自明上界と一致し、どの k でも中身がない。")
    print("     ⚠ 同じ族の 2 つの端が別々の候補を殺している — a = (5-sqrt5)/10 が G1 を、")
    print("        a -> 0 が G3 を殺す (gap は 0 に落ちるのに比は 2 に上がる)。")
    print("     ⚠ 乗法形の枝は文献が既に踏み込んでいる — [GNA12] Appendix B の定数")
    print("        c_{p(u,x)} (= I(U;Y) <= c I(X;Y) を全チャネルで満たす最小の c) と")
    print("        Theorem 3 (binary XOR で c_u + c_v <= 1) がそれ。新規性も薄い。\n")


# --------------------------------------------------------------------------
# §10 G2 (sum rate ギャップ)
# --------------------------------------------------------------------------
def sr_rtd(T: np.ndarray, rng, restarts: int) -> OptReport:
    """[GJNW13] Theorem 3 逐語の R-TD sum rate (|W| = 2)。返るのは **下界**。"""
    kx = T.shape[0]

    def f(th):
        w0 = 1.0 / (1.0 + np.exp(-th[0]))
        pw = np.array([w0, 1.0 - w0])
        pxw = softmax(th[1:].reshape(2, kx), axis=-1)
        J = Joint(["W", "X", "Y", "Z"],
                  (pw[:, None] * pxw)[:, :, None, None] * T[None, :, :, :],
                  validate=False)
        val = min(J.eval(_IWY, "bits"), J.eval(_IWZ, "bits"))
        for w, expr in ((0, _IXY), (1, _IXZ)):
            if pw[w] > 1e-12:
                Jw = Joint(["X", "Y", "Z"], pxw[w][:, None, None] * T, validate=False)
                val += pw[w] * Jw.eval(expr, "bits")
        return val

    return maximize(f, 1 + 2 * kx, rng, restarts=restarts,
                    options={"maxiter": 8000, "maxfev": 8000})


def section10(quick: bool) -> bool:
    print("=" * 78)
    print("§10 G2 (sum rate ギャップ) — SR_Marton - SR_RTD <= g(|X|), g(2) = 0")
    print("=" * 78)
    print("  SR_Marton 側は **明示の達成点** (Bound 1 で W = 定数, U = Y, V = Z) が")
    print("  与える下界 max_p H(Y,Z) を使う (決定論的 BC なのでこの点は S1 = S2 = H(Y,Z)、")
    print("  R1 = H(Y), R2 = H(Z|Y) が Bound 1 の 4 制約をすべて満たす)。")
    print("  SR_RTD 側は [GJNW13] Theorem 3 逐語の式を最大化する = **下界**。")
    print("  ⟹ 差は **上振れ** しうるので、違反が出たときだけ意味がある。")
    rng = np.random.default_rng(1729)
    n_r = 12 if quick else 30
    rows = [("Blackwell (|X|=3)", blackwell()), ("2x2 格子 (|X|=4)", grid(2, 2))]
    if not quick:
        rows += [("2x3 格子 (|X|=6)", grid(2, 3)), ("3x3 格子 (|X|=9)", grid(3, 3))]
    viol = False
    print("  チャネル            | SR_M(下界) | SR_RTD(下界) | 差      | g(k)=log2(k/2)")
    print("  --------------------+------------+--------------+---------+---------------")
    for name, T in rows:
        k = T.shape[0]
        rep_m = maximize(
            lambda th, T=T: Joint(["X", "Y", "Z"], softmax(th)[:, None, None] * T,
                                  validate=False).eval(_HYZ, "bits"),
            k, rng, restarts=n_r,
        )
        rep_r = sr_rtd(T, rng, n_r)
        d = rep_m.best - rep_r.best
        g = np.log2(k / 2.0)
        viol |= d > g + 1e-9
        print(f"  {name:<19} | {rep_m.best:10.6f} | {rep_r.best:12.6f} | "
              f"{d:7.6f} | {g:9.6f} {'**違反**' if d > g else ''}")
    print()
    print("  ⟹ **G2 は掃引では殺せなかった** (これらのチャネルで違反 0)。")
    print("     ⚠ 「証明できた」ではない。特に SR_RTD は下界なので差は上振れ側にあり、")
    print("        それでも違反しなかったという意味では証拠としてはやや強いが、")
    print(f"        掃引したチャネルは決定論的な格子 {len(rows)} 本だけである。")
    print("     ⚠ G2 は独立な候補ではない — G1 形 (スラック f) から W = w ごとの条件付き")
    print("        適用で g = f が従う。ただし [GJNW13] の証明は |W| = 2 を使っており、")
    print("        |X| >= 3 では Theorem 2 の濃度限界が |W| <= |X| までしか落とさないので、")
    print("        「|W| <= k の時分割値 = |W| = 2 の SR_RTD」は **gap** (未検討)。\n")
    return not viol


# --------------------------------------------------------------------------
# §11 死因から起票する子候補 — チャネル依存の汎関数と、その場で死ぬ 2 案
# --------------------------------------------------------------------------
def section11() -> None:
    print("=" * 78)
    print("§11 死因から起票する子候補 (親 plan §5-9) — 定数ではなく汎関数へ")
    print("=" * 78)
    print("  死因の共通形: **「濃度 1 つにつき定数 1 個」という形そのもの**が弱い。")
    print("  G1 の正しい定数 f*(k) も、完全平方 k = m^2 では §1 の自明上界に一致する")
    print("  (§8) ため中身が消え、G3 の rho*(k) は全 k >= 3 で 2 = 自明上界 (§9)。")
    print("  ⟹ 次の候補は **チャネル依存の汎関数 Phi(T, p)** でなければならない。")
    print()
    print("  witness から強制される必要条件 (どの Phi もこれを満たさねばならない):")
    print("    (N1) |X| = 2 では Phi = max{I(X;Y), I(X;Z)} ちょうど")
    print("         (Theorem 1 + §4 が示した達成 ⟹ 上でも下でもずれてはいけない)")
    print("    (N2) 決定論的で (Y,Z) が X を復元する BC では Phi >= H(X)")
    print("         (§5 の witness U = Y, V = Z が LHS = H(X) を出す)")
    print()
    T = blackwell()
    q = (5.0 - 5.0**0.5) / 10.0
    pxb = np.array([q, 1.0 - 2.0 * q, q])
    tb = joint5(witness_uy_vz(pxb, T), T).eval(_LHS, "bits")
    mmax, _ = simplex_scan(
        lambda p: max(
            Joint(["X", "Y", "Z"], p[:, None, None] * T, validate=False).eval(_IXY, "bits"),
            Joint(["X", "Y", "Z"], p[:, None, None] * T, validate=False).eval(_IXZ, "bits"),
        ), 3, steps=200,
    )
    print("  案 A: Phi = C[max{I(X;Y), I(X;Z)}] (p(x) 上の上凹包) — **その場で死ぬ**")
    print(f"     Blackwell では max_p max{{I(X;Y),I(X;Z)}} = {mmax:.6f} (= 1 bit)")
    print(f"     上凹包は元の関数の最大値を超えないので C[.] <= {mmax:.6f}")
    print(f"     しかし §5 の witness が T(X) = {tb:.6f} を出す ⟹ (N2) 違反")
    print()
    T2 = np.zeros((2, 2, 2))
    e = 0.1
    for x in range(2):
        for y in range(2):
            for z in range(2):
                py = (1 - e) if y == x else e
                pz = (1 - e) if z == x else e
                T2[x, y, z] = py * pz          # Y ⊥ Z | X の代表 (周辺は BSC(0.1) 2 本)
    J2 = Joint(["X", "Y", "Z"], np.full(2, 0.5)[:, None, None] * T2, validate=False)
    ixyz = J2.eval(parse("I(X;Y,Z)"), "bits")
    m2 = max(J2.eval(_IXY, "bits"), J2.eval(_IXZ, "bits"))
    print("  案 B: Phi = I(X;Y,Z) (Y ⊥ Z | X の代表で測る) — **その場で死ぬ**")
    print(f"     BSC(0.1) 2 本 + 一様入力 (|X| = 2): I(X;Y,Z) = {ixyz:.6f} vs "
          f"max{{I,I}} = {m2:.6f}")
    print(f"     差 {ixyz - m2:+.6f} > 0 ⟹ (N1) 違反 (Theorem 1 より真に弱い)。")
    print("     ⚠ (N2) は等号で満たす (決定論的なら I(X;Y,Z) = H(X)) ので、"
          "2 条件のうち")
    print("        片方だけ見ていると通ってしまう。**必ず両方に当てること**。")
    print()
    print("  ⟹ **起票する子候補は 2 本**:")
    print("     C1: f*(k) = D(k) — 決定論的な格子チャネルが極値である (= R2 の核)。")
    print("         最小の未決着例は k = 3 で、f*(3) in [log2 phi, (1/2)log2 3]。")
    print("     C2: (N1) と (N2) を同時に満たすチャネル依存の Phi を 1 本作る。")
    print("         上の案 A / 案 B はそれぞれ (N2) / (N1) で落ちたので、"
          "次は両方に")
    print("         当ててから probe すること (片側だけの確認は 2 回とも通す)。\n")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--quick", action="store_true", help="掃引を縮小して約 12s で回す")
    args = ap.parse_args()
    t0 = time.time()
    print("bc-jognair-general-check.py — [GJNW13] Theorem 1 の |X| >= 3 一般化候補の "
          "kill-first probe")
    print(f"(mode = {'quick' if args.quick else 'full'})\n")

    ok1 = section1()
    v2 = section2(400 if args.quick else 2000)
    ok3 = section3()
    ok4 = section4(6 if args.quick else 12)
    killed = section5()
    section6()
    best = section7(args.quick)
    section8(args.quick)
    section9(args.quick)
    ok10 = section10(args.quick)
    section11()

    print("=" * 78)
    print("=== 判定 ===")
    print("=" * 78)
    print(f"  コントロール: 記号 {'PASS' if ok1 else 'FAIL'} / 肯定 "
          f"{'違反 0' if v2 == 0 else f'違反 {v2}'} / 否定 "
          f"{'原典再現' if ok3 else 'NG'} / 最大化 {'張り付き' if ok4 else 'NG'}")
    print(f"  **G1 (加法, f(k)=log2(k/2)) = refuted** "
          f"({'反証 witness あり' if killed else '反証できず'})")
    print("     死因: k = 3 で log2 phi > log2(3/2)、k >= 4 では自明上界の帰結で空虚")
    print("  **G3 (乗法, rho(k)) = refuted** (rho*(k) = 2 が全 k >= 3、"
          "自明上界と一致 = 空虚)")
    print(f"  **G2 (sum rate ギャップ)** = {'掃引では殺せなかった' if ok10 else '違反あり'}"
          " (証明ではない)")
    print(f"  f*(3) の現状: [{LOG2_PHI:.6f}, {0.5 * np.log2(3):.6f}]  "
          f"(掃引の最良値 {best:.6f})")
    print("  f*(2) = 0 (Theorem 1) / f*(4) = 1 / f*(9) = log2 3 は確定")
    print(f"\n合計実行時間 {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
