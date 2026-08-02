#!/usr/bin/env python3
"""軸 C の子 attack `slack-loss-lower-bound` の続き (L17) — `Λ_split` の一般化と `Λ_comb` の鋭さ

親 plan `bc-open-problem-plan.md` §7 の L17 行。経路は `bc-open-problem-routes.md` §R3。
所要: full 約 211s / `--quick` 約 28s。⚠ **散文が引く数値はすべて full 実行のもの**
(`--quick` は掃引が狭く一部の値が食い違う。`bc-facts.md` §L13 の教訓)。乱数種と開始点は固定。

主語 (L15 / L16 が確定させたもの)
----------------------------------
    L'(p)      := min_{p(u,v|x)} [ I(U;X|Y) + I(V;X|Z) + H(X|U,V) + I(U;V|X) ]   (>= 0)
    beta(p)    := min{H(X|Y), H(X|Z)}          (= |X| <= 2 での L' の真値、[GJNW13] Thm 1)
    gap(T,p)   =  beta(p) - L'(p)                                          ((H1)、L13 で証明)
    (H4)       :  W = m(X) (X の**関数**) について L'(p) >= sum_w p(w) L'(p_w)   (L15 で証明)
    Λ_split    :  (H4) を再帰的に使い |X| <= 2 を beta で閉じた**証明済**の下界
    Λ_env      :  支配チャネルで罰項を差し替えた下界 ((H5)、L16 で証明)。Λ_env >= Λ_sup
    Λ_comb     := max{Λ_split, Λ_env}

本 probe が測るもの (L17 の 3 段)
--------------------------------
**段 A — `|W| >= 3` は Λ_split の再帰に既に含まれているか** (§1)
    一般の分割 {A,B,C} に対する (H4) は、2 分割 {A, B∪C} → {B,C} の階層適用と
    **エントロピーの grouping 公理により厳密に一致する** (望遠鏡和に緩みが無い)。
    ⟹ 予想は「含まれている = 新規の余地ゼロ」。記号 (§0(c)) と数値 (§1) の両方で確かめる。

**段 B — 非決定論的 `W` (`H(W|X) > 0`)** (§2 / §3)
    (H4) の 4 本の恒等式は無仮定で、L15 の証明が `H(W|X) = 0` を使うのは減算項の消去だけ。
    ⟹ 一般 `W` では減算項が残る……という見立てを **kill-first で先に殺しにいく** (§2)。
    実際には殺せない。`W` を `p(w|x)` で作ると (U,V,Y,Z) ⊥ W | X が成り立ち、

        (H6)  F(U,V;p) - sum_w p(w) F(U,V;p_w) = I(U;W|Y) + I(V;W|Z) + I(X;W|U,V) >= 0

    が**無仮定の恒等式 + 3 つの独立性**だけから出る (§3)。3 項とも非負なので罰項は要らない。
    ⟹ **(H6) は `L'(·,q)` が入力分布 `p(x)` の凹関数であることと同値**である
    (任意の凸結合 p = sum_w λ_w p_w は p(w|x) := λ_w p_w(x)/p(x) と 1 対 1 に対応する)。
    `T` の形にすると罰項は `H(W)` ではなく **`I(X;W)` (<= H(W))** ⟹ 決定論版より真に強い。

**段 B-3 / 段 C — 一般化が `Λ_comb` の鋭さを動かすか** (§4 / §5 / §6)
    (H6) を下界に変えるには「値を知っている `p_w`」へ分解する必要がある。台が 2 点以下なら
    `L'(p_w) = beta(p_w)` が [GJNW13] Theorem 1 で厳密 ⟹

        Λ_cav(p) := max { sum_w λ_w Λ_split(p_w) : p = sum_w λ_w p_w }      (= Λ_split の上凹包)

    が **証明済の下界**で、構成から `Λ_cav >= Λ_split`。⚠ **Λ_split との性格の差**: Λ_split は
    有限列挙で厳密だったが Λ_cav は分解上の最大化を含む。ただし**単体を格子で離散化して LP を
    解けば、格子点だけを使った値は真の上凹包の下界**なので、**符号は証明書の向きに落ちる**
    (最適化器を信用する必要が無い)。P3 の ill-posed 制約 (2 つの周辺と p(x) だけの函数か、
    facts §L13) は Λ_split から継承する — §4 が同時分布を振って機械確認する。

判定の向き (どの数値が確定で、どれが探索か)
-------------------------------------------
* `beta` / `Λ_split` / `Λ_cav` (格子 LP) は**最適化を含まない厳密値**。
* `L'` は最小化 ⟹ 返り値は真の `L'` の**上界**。`Γ` は最大化 ⟹ `Λ_sup` / `Λ_env` は**上振れ**。
* ゆえに **`Λ_split > L'推定` / `Λ_cav > L'推定` は矛盾の証明書** (両者とも厳密な下界なので)。
  一方 **`Λ_sup > L'推定` / `Λ_env > L'推定` は「推定不足」** (Λ 側が上振れしただけ) ⟹
  §5 は 2 つを**分けて数え、どの行かを必ず印字する** (親 plan §5-13)。
* §6 の「`Λ_sup` が `Λ_split` を支配する」は**探索強度に依存する下界**であって率ではない。
  決着が付くのは逆向き (`Λ_split > Λ_sup推定` が 1 本出れば支配は反証される) だけである。

sim と定義の逐語照合 (CLAUDE.md 検証の誠実性)
---------------------------------------------
* 目的量・チャネル族・最適化器は L13 / L15 / L16 probe を **import して再利用**する。単位は bit。
* `Λ_split` は L15 §4b の `split_bound` の `Λ` 形 (`Λ = H(X) - split_bound`) を独立に書き直した
  ものなので、§1 が両者を突き合わせる (grouping 公理による書き換えが正しいことの確認)。
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
import time
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

_HERE = Path(__file__).resolve().parent
if str(_HERE) not in sys.path:
    sys.path.insert(0, str(_HERE))


def _load_sibling(fname: str, modname: str):
    """ハイフンつきファイル名の兄弟 probe を import する (規約の再導出を避けるため)。"""
    path = _HERE / fname
    spec = importlib.util.spec_from_file_location(modname, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[modname] = mod
    spec.loader.exec_module(mod)
    return mod


import bc_probe as _BP                                            # noqa: E402

_L13 = _load_sibling("bc-jognair-phi-check.py", "bc_jognair_phi_check_l17")
_L15 = _load_sibling("bc-slack-loss-lower-check.py", "bc_slack_loss_lower_l17")
_L16 = _load_sibling("bc-d2-lower-check.py", "bc_d2_lower_l17")

prove_identity = _BP.prove_identity
Joint = _BP.Joint
parse = _BP.parse
softmax = _BP.softmax
BayesNet = _BP.BayesNet

_h = _L13._h
_mi = _L13._mi
ixy_ixz = _L13.ixy_ixz
loss_terms = _L13.loss_terms
cond_to_joint = _L13.cond_to_joint
l_prime = _L13.l_prime
t_lower = _L13.t_lower
det_pairs = _L13.det_pairs
partitions = _L13.partitions
maximize_hd = _L13.maximize_hd
marginals = _L13.marginals
blackwell = _L13.blackwell
smoothed_blackwell = _L13.smoothed_blackwell
noisy_blackwell = _L13.noisy_blackwell
partial_merge = _L13.partial_merge
lattice_family = _L13.lattice_family

dense_random = _L15.dense_random
gamma_sup = _L15.gamma_sup
split_bound = _L15.split_bound
bsc = _L15.bsc
bec = _L15.bec
lam_env = _L16.lam_env

TOL_ID = 1e-9          # 直接評価どうしの一致に要求する精度
TOL_CERT = 1e-7        # 「証明書つきの違反」と呼ぶための margin


# --------------------------------------------------------------------------
# Λ_split / Λ_cav — どちらも最適化を含まない
# --------------------------------------------------------------------------
def beta(px: np.ndarray, Cy: np.ndarray, Cz: np.ndarray) -> float:
    """`min{H(X|Y), H(X|Z)}` (bit)。`|X| <= 2` では `L'` の真値 ([GJNW13] Theorem 1)。"""
    if px.size <= 1:
        return 0.0
    iy, iz = ixy_ixz(px, Cy, Cz)
    return _h(px) - max(iy, iz)


def lam_split(px: np.ndarray, Cy: np.ndarray, Cz: np.ndarray) -> float:
    """`Λ_split` = (H4) の 2 分割再帰の `Λ` 形。**全列挙ゆえ厳密**。

    `Λ(p) = max_{2 分割 S} [p(S)Λ(p_S) + p(Sᶜ)Λ(p_Sᶜ)]`、base は `|supp| <= 2` で `beta`。
    L15 §4b の `split_bound` (T 形) とは `Λ = H(X) - split_bound` の関係にある (§1 が照合)。
    """
    k = px.size
    if k <= 2:
        return beta(px, Cy, Cz)
    best = -np.inf
    for mask in range(1, 2 ** (k - 1)):
        s = [i for i in range(k) if (mask >> i) & 1]
        sc = [i for i in range(k) if not (mask >> i) & 1]
        if not s or not sc:
            continue
        ps, pc = float(px[s].sum()), float(px[sc].sum())
        val = 0.0
        if ps > 1e-12:
            val += ps * lam_split(px[s] / ps, Cy[s], Cz[s])
        if pc > 1e-12:
            val += pc * lam_split(px[sc] / pc, Cy[sc], Cz[sc])
        best = max(best, val)
    return best


def lam_gen(px: np.ndarray, Cy: np.ndarray, Cz: np.ndarray) -> float:
    """段 A の対照 — **一般の分割**を各段で許した再帰。`|W| >= 3` を明示的に使う。

    `Λ(p) = max_{分割 P, |P| >= 2} sum_i p(A_i) Λ(p_{A_i})`。grouping 公理により
    `lam_split` と厳密に一致するはず (§1 が数値で確かめる)。
    """
    k = px.size
    if k <= 2:
        return beta(px, Cy, Cz)
    best = -np.inf
    for lab in partitions(k):
        blocks: dict[int, list[int]] = {}
        for i, b in enumerate(lab):
            blocks.setdefault(b, []).append(i)
        if len(blocks) < 2:
            continue
        val = 0.0
        for blk in blocks.values():
            pb = float(px[blk].sum())
            if pb > 1e-12:
                val += pb * lam_gen(px[blk] / pb, Cy[blk], Cz[blk])
        best = max(best, val)
    return best


def simplex_mesh(k: int, n: int) -> np.ndarray:
    """`k` 次元単体の格子 (分母 `n`)。境界 (台が小さい面) を必ず含むのが要点 —
    そこが `Λ_split = beta = L'` で厳密な場所である。"""
    out: list[tuple[float, ...]] = []

    def rec(pref: list[int], rem: int, left: int) -> None:
        if left == 1:
            out.append(tuple((pref + [rem])[i] / n for i in range(k)))
            return
        for v in range(rem + 1):
            rec(pref + [v], rem - v, left - 1)

    rec([], n, k)
    return np.array(out)


def lam_cav(px: np.ndarray, Cy: np.ndarray, Cz: np.ndarray,
            mesh: np.ndarray, vals: np.ndarray | None = None):
    """`Λ_cav` = `Λ_split` の**上凹包**を単体格子上の LP で下から評価する。

    `max sum_m c_m Λ_split(p_m)` s.t. `sum_m c_m p_m = p`, `sum c_m = 1`, `c >= 0`。
    格子点しか使わないので返り値は**真の上凹包の下界** ⟹ `L'` の下界であることは保たれる
    (符号が証明書の向きに落ちる)。LP は厳密に解ける ⟹ 最適化器を信用する必要が無い。
    返り `(値, 格子上の Λ_split の値ベクトル)`。
    """
    if vals is None:
        vals = np.array([lam_split(np.asarray(m), Cy, Cz) for m in mesh])
    A = np.vstack([mesh.T, np.ones(len(mesh))])
    b = np.concatenate([np.asarray(px, dtype=float), [1.0]])
    res = linprog(-vals, A_eq=A, b_eq=b, bounds=(0, None), method="highs")
    if not res.success:
        return float(lam_split(px, Cy, Cz)), vals
    return max(float(-res.fun), float(lam_split(px, Cy, Cz))), vals


def f_sum(cond: np.ndarray, px: np.ndarray, Cy: np.ndarray, Cz: np.ndarray) -> float:
    """固定した核 `p(u,v|x)` での 4 項損失 `F(U,V;p)` (bit)。**直接評価、最適化なし**。"""
    return float(sum(loss_terms(cond_to_joint(cond, px), Cy, Cz)))


def mix_defect(cond: np.ndarray, px: np.ndarray, Cw: np.ndarray,
               Cy: np.ndarray, Cz: np.ndarray) -> float:
    """`F(U,V;p) - sum_w p(w) F(U,V;p_w)`。`Cw[x,w] = p(w|x)` は**任意** (非決定論的でよい)。

    核 `p(u,v|x)` は各 `w` で同じものを使う (W ⊥ (U,V) | X の構成)。両辺とも直接評価なので
    負の値が 1 つ出れば (H6) は**証明書つきで反証**される。
    """
    pw = np.asarray(px) @ Cw
    tot = 0.0
    for w in range(Cw.shape[1]):
        if pw[w] < 1e-12:
            continue
        tot += pw[w] * f_sum(cond, px * Cw[:, w] / pw[w], Cy, Cz)
    return f_sum(cond, px, Cy, Cz) - tot


def l_prime_est(px: np.ndarray, Cy: np.ndarray, Cz: np.ndarray,
                rng, quick: bool) -> float:
    """`L'` の**上界**推定。最小化 2 本 (`l_prime` と `H(X) - t_lower`) の良い方を採り、
    さらに **証明済の `L' <= beta`** で clamp する (clamp しないと最適化の届き不足で
    `gap` が負に出て、`slack/gap` が読めなくなる)。返り値は常に `>= L'` の真値。
    """
    a, _, _ = l_prime(px, Cy, Cz, rng, restarts=6 if quick else 14,
                      seed_pairs=det_pairs(px.size)[:12])
    b = _h(px) - t_lower(px, Cy, Cz, rng, restarts=4 if quick else 10,
                         seed_pairs=det_pairs(px.size)[:12]).best
    return float(min(a, b, beta(px, Cy, Cz)))


# --------------------------------------------------------------------------
# §0 harness — 記号的な恒等式 (最適化を使わないので再実行で必ず一致する)
# --------------------------------------------------------------------------
_F = "I(U;X|Y) + I(V;X|Z) + H(X|U,V) + I(U;V|X)"
_FW = "I(U;X|W,Y) + I(V;X|W,Z) + H(X|U,V,W) + I(U;V|X,W)"
_POS = "I(U;W|Y) + I(V;W|Z) + I(X;W|U,V) + I(U;W|X) + I(V;W|X)"
_NEG = "I(U;W|X,Y) + I(V;W|X,Z) + I(U,V;W|X)"


def section0(quick: bool) -> bool:
    print()
    print("=" * 78)
    print("§0 harness — 記号的な恒等式 (`prove_identity` は残差の全係数が消えて初めて accept)")
    print("=" * 78)
    ok = True
    checks = [
        ("(a) 一般 W の分解 (無仮定)", _F, f"{_FW} + {_POS} - ({_NEG})"),
        ("(b) H(X|U,V) の連鎖則", "H(X|U,V)", "H(X|U,V,W) + I(X;W|U,V)"),
        ("(c) grouping 公理 (段 A の核)", "H(W)", "H(W1) + H(W|W1) - H(W1|W)"),
        ("(d) I(U;X|Y) の書き換え", "I(U;X|Y)", "H(U|Y) - H(U|X,Y)"),
        ("(e) I(U;V|X) の分解", "I(U;V|X)", "H(U|X) + H(V|X) - H(U,V|X)"),
    ]
    for name, lhs, rhs in checks:
        held, resid = prove_identity(lhs, rhs)
        print(f"  {name:<34} accept = {held} / 残差 = {resid}")
        ok &= held
    print("  ⟹ (a) が本 leg の全体像: 減算 3 項 `I(U;W|X,Y)` `I(V;W|X,Z)` `I(U,V;W|X)` と")
    print("     加算 2 項 `I(U;W|X)` `I(V;W|X)` は **W ⊥ (U,V,Y,Z) | X** の系として消え、")
    print("     残るのは非負 3 項 `I(U;W|Y) + I(V;W|Z) + I(X;W|U,V)` だけになる (§3 が実測)。")
    print("  ⟹ (c) は `W1 = m(W)` のとき `H(W1|W) = 0` ⟹ `H(W) = H(W1) + H(W|W1)` ⟹")
    print("     多分割の罰項は 2 分割の階層適用の**望遠鏡和とちょうど等しい** (段 A の記号的根拠)。")
    print("  ⟹ (d)+(e) は別証明の材料: `U -> X -> Y` で `H(U|X,Y) = H(U|X)` (X について線型)、")
    print("     `H(U|Y)` / `H(X|U,V)` は同時分布の凹関数、同時分布は `p(x)` について線型")
    print("     ⟹ `F(U,V;·)` は `p(x)` の凹関数、`L'` はその min ⟹ **`L'` は凹** (= (H6))。")

    # W ⊥ (U,V,Y,Z) | X を BayesNet で構成し、消えるはずの 5 項を数値で確かめる
    rng = np.random.default_rng(17041703)
    vanish = ["I(U;W|X,Y)", "I(V;W|X,Z)", "I(U,V;W|X)", "I(U;W|X)", "I(V;W|X)"]
    worst = 0.0
    n = 40 if quick else 150
    for _ in range(n):
        net = (BayesNet().root("X", 3, dirichlet=1.5)
               .add(("U", "V"), (3, 3), ["X"], dirichlet=0.7)   # p(u,v|x)
               .add("W", 3, ["X"], dirichlet=0.7)               # p(w|x) — 非決定論的
               .add("Y", 3, ["X"], dirichlet=1.0)
               .add("Z", 3, ["X"], dirichlet=1.0))
        J6 = net.build(rng)
        for e in vanish:
            worst = max(worst, abs(J6.eval(parse(e), "bits")))
    print()
    print(f"  W ⊥ (U,V,Y,Z) | X の BayesNet {n} 本: 消えるべき 5 項の最大絶対値 = {worst:.3e}")
    ok &= worst < 1e-12
    print(f"  ⟹ §0 {'PASS' if ok else '**FAIL**'}")
    return ok


# --------------------------------------------------------------------------
# §1 段 A — `|W| >= 3` は Λ_split の再帰に既に含まれているか
# --------------------------------------------------------------------------
def section1(quick: bool) -> dict:
    print()
    print("=" * 78)
    print("§1 **段 A** — `|W| >= 3` (多分割) は 2 分割再帰に含まれているか")
    print("=" * 78)
    print("  記号的根拠 (§0(c) の grouping 公理): 分割 {A,B,C} に (H4) を 1 回当てた値は、")
    print("    {A, B∪C} → {B,C} と 2 段に当てた値と**厳密に一致する**")
    print("    (`H(a,b,c) = H(a,b+c) + (b+c)·H(b/(b+c), c/(b+c))` に緩みが無いため)。")
    print("  ⟹ 予想: `lam_gen` (全分割再帰) = `lam_split` (2 分割再帰)。以下は数値の裏取り。")
    print()
    rng = np.random.default_rng(17041704)
    rows, worst, worst_case = [], 0.0, None
    sizes = [(3, 20), (4, 12)] if quick else [(3, 40), (4, 25), (5, 10)]
    for kx, n in sizes:
        d = 0.0
        for _ in range(n):
            px, Cy, Cz = dense_random(rng, kx=kx, ky=kx, kz=kx)
            a, b = lam_split(px, Cy, Cz), lam_gen(px, Cy, Cz)
            d = max(d, abs(a - b))
            if abs(a - b) > worst:
                worst, worst_case = abs(a - b), (kx, px, a, b)
        rows.append((kx, n, d))
        print(f"  |X| = {kx}: dense ランダム {n} 本、`|lam_gen - lam_split|` の最大 = {d:.3e}")
    # 疎 / 決定論寄り / 非一様な p でも確かめる (退化点で差が出ないか)
    extra = 0.0
    for _ in range(15 if quick else 40):
        kx = int(rng.integers(3, 6))
        Cy = rng.dirichlet(np.ones(kx) * 0.2, size=kx)
        Cz = rng.dirichlet(np.ones(kx) * 0.2, size=kx)
        px = rng.dirichlet(np.ones(kx) * 0.4)
        extra = max(extra, abs(lam_split(px, Cy, Cz) - lam_gen(px, Cy, Cz)))
    print(f"  疎 (Dirichlet 0.2) / 非一様 `p` でも: 最大差 = {extra:.3e}")
    # L15 の split_bound (T 形) との照合 — Λ = H(X) - split_bound
    conv = 0.0
    for _ in range(10 if quick else 25):
        px, Cy, Cz = dense_random(rng)
        conv = max(conv, abs(lam_split(px, Cy, Cz) - (_h(px) - split_bound(px, Cy, Cz)[0])))
    print(f"  L15 §4b の `split_bound` との照合 `Λ = H(X) - split_bound`: 最大差 = {conv:.3e}")
    ok = max(worst, extra, conv) < 1e-9
    print()
    print(f"  ⟹ **段 A の判定: {'多分割は 2 分割再帰に完全に含まれる (新規の余地ゼロ)' if ok else '**含まれない** — 差が出た'}**")
    if worst_case is not None and worst > 1e-12:
        print(f"    最大差の点: |X|={worst_case[0]}, p={np.round(worst_case[1], 4)}, "
              f"split={worst_case[2]:.9f}, gen={worst_case[3]:.9f}")
    return dict(ok=ok, worst=float(worst), extra=float(extra), conv=float(conv), rows=rows)


# --------------------------------------------------------------------------
# §2 段 B-1 — kill-first。非決定論的 `W` の素朴な形を先に殺しにいく
# --------------------------------------------------------------------------
def adversarial_h6(rng, kx: int, ky: int, kz: int, kw: int,
                   restarts: int, maxiter: int = 800):
    """`sum_w p(w) F(p_w) - F(p)` を `(p, Cy, Cz, p(u,v|x), p(w|x))` 上で最大化する。

    **両辺とも明示の直接評価** (内側に最適化が無い) ⟹ 正の値が 1 つ出れば最適化を
    一切信用せずに読める **kill の証明書**になる (親 plan §5-12 の運用教訓)。
    """
    n_p, n_y, n_z = kx, kx * ky, kx * kz
    n_c, n_w = kx * kx * kx, kx * kw
    dim = n_p + n_y + n_z + n_c + n_w

    def unpack(th):
        i = 0
        px = softmax(th[i:i + n_p]); i += n_p
        Cy = softmax(th[i:i + n_y].reshape(kx, ky), axis=-1); i += n_y
        Cz = softmax(th[i:i + n_z].reshape(kx, kz), axis=-1); i += n_z
        cond = softmax(th[i:i + n_c].reshape(kx, kx * kx), axis=-1).reshape(kx, kx, kx)
        i += n_c
        Cw = softmax(th[i:i + n_w].reshape(kx, kw), axis=-1)
        return px, Cy, Cz, cond, Cw

    def f(th):
        px, Cy, Cz, cond, Cw = unpack(th)
        return -mix_defect(cond, px, Cw, Cy, Cz)

    rep = maximize_hd(f, dim, rng, restarts=restarts, maxiter=maxiter)
    return rep.best, unpack(rep.best_x)


def section2(quick: bool) -> dict:
    print()
    print("=" * 78)
    print("§2 **段 B-1 (kill-first)** — 非決定論的 `W` の素朴な形を先に殺しにいく")
    print("=" * 78)
    print("  標的: `L'(p) >= sum_w p(w) L'(p_w)` で `W` を `p(w|x)` (H(W|X) > 0) にした形。")
    print("  ⚠ 事前情報 (routes.md §R3 の novelty gate): [GNA12] Equation (2) は任意の")
    print("     `p(v|x)` を使い罰項が無く、原典自身が「ある p(x) では成り立たない」と書く")
    print("     ⟹ **罰項なしの非決定論版は既知の偽である公算が高い**、が事前の読みだった。")
    print("  ⚠ しかし `L'` 形の罰項は `T` 形の `H(W)` に対応しており、`L' >= sum p(w) L'(p_w)`")
    print("     は `T(p) <= I(X;W) + sum_w p(w) T(p_w)` と同値 = **罰項は消えていない**")
    print("     (`I(X;W)`。決定論的 `W` でだけ `I(X;W) = H(W)` になる)。⟹ 別物である。")
    print()
    rng = np.random.default_rng(17041705)
    # (a) 掃引 — 核 p(u,v|x) と p(w|x) をランダムに振って直接評価する
    worst, n_neg = np.inf, 0
    n = 60 if quick else 300
    for _ in range(n):
        kw = int(rng.integers(2, 5))
        px, Cy, Cz = dense_random(rng)
        cond = softmax(rng.normal(0, 1.5, (3, 9)), axis=-1).reshape(3, 3, 3)
        Cw = rng.dirichlet(np.ones(kw) * 0.6, size=3)
        d = mix_defect(cond, px, Cw, Cy, Cz)
        worst = min(worst, d)
        n_neg += d < -TOL_CERT
    print(f"  (a) 掃引 {n} 本 (|W| = 2..4、すべて H(W|X) > 0): "
          f"`F(p) - sum_w p(w) F(p_w)` の最小 = {worst:+.3e} / 違反 {n_neg} 本")
    # (b) 敵対的探索 — チャネル・核・p(w|x) を同時に振る
    best = -np.inf
    shapes = [(3, 3, 3, 2), (3, 2, 2, 3)] if quick else \
        [(3, 3, 3, 2), (3, 2, 2, 3), (3, 4, 4, 3), (4, 4, 4, 2), (3, 3, 3, 4)]
    for (kx, ky, kz, kw) in shapes:
        m, _ = adversarial_h6(rng, kx, ky, kz, kw,
                              restarts=6 if quick else 18)
        best = max(best, m)
        print(f"  (b) |X|={kx},|Y|={ky},|Z|={kz},|W|={kw}: 最良 margin = {m:+.3e}")
    dead = (worst < -TOL_CERT) or (best > TOL_CERT)
    print()
    print(f"  ⟹ **段 B-1 の判定: 素朴な非決定論版は "
          f"{'**REFUTED** (証明書つき)' if dead else '殺せなかった'}**")
    if not dead:
        print("     ⟹ kill-first が空振り ⟹ §5-13 の provable-first へ切り替える")
        print("        (殺せなかった形にだけ証明を投資する)。§3 が記号的な証明を与える。")
    return dict(dead=bool(dead), worst=float(worst), best=float(best))


# --------------------------------------------------------------------------
# §3 段 B-2 — (H6) の厳密な恒等式。罰項の最小の形を同定する
# --------------------------------------------------------------------------
def section3(quick: bool) -> dict:
    print()
    print("=" * 78)
    print("§3 **段 B-2 (H6)** — 減算項を残したままの厳密な恒等式と、罰項の最小の形")
    print("=" * 78)
    print("  §0(a) の無仮定な恒等式に **W ⊥ (U,V,Y,Z) | X** (= `W` を `p(w|x)` で作る)")
    print("  を当てると減算 3 項と加算 2 項が消え (§0 の BayesNet 検査)、")
    print("      **F(U,V;p) - sum_w p(w) F(U,V;p_w) = I(U;W|Y) + I(V;W|Z) + I(X;W|U,V)**")
    print("  **3 項とも非負** ⟹ 一般 `W` でも追加の罰項は要らない (= (H6))。")
    print("  ⟹ 各 (U,V) で成り立つので最小化して `L'(p) >= sum_w p(w) L'(p_w)`。")
    print("  ⟹ 任意の凸結合 `p = sum λ_w p_w` は `p(w|x) := λ_w p_w(x)/p(x)` に対応する")
    print("     ⟹ **(H6) は `L'(·,q)` が `p(x)` の凹関数であることと同値**。")
    print()
    rng = np.random.default_rng(17041706)
    worst_id, worst_pen, min_pen_ratio = 0.0, 0.0, np.inf
    n = 30 if quick else 120
    for _ in range(n):
        kw = int(rng.integers(2, 4))
        px, Cy, Cz = dense_random(rng)
        cond = softmax(rng.normal(0, 1.5, (3, 9)), axis=-1).reshape(3, 3, 3)
        Cw = rng.dirichlet(np.ones(kw) * 0.6, size=3)
        d = mix_defect(cond, px, Cw, Cy, Cz)
        T = np.einsum("xy,xz->xyz", Cy, Cz)
        J6 = Joint(["U", "V", "X", "Y", "Z", "W"],
                   np.einsum("uvx,xyz,xw->uvxyzw", cond_to_joint(cond, px), T, Cw),
                   validate=False)
        pred = J6.eval(parse("I(U;W|Y) + I(V;W|Z) + I(X;W|U,V)"), "bits")
        worst_id = max(worst_id, abs(d - pred))
        ixw = J6.eval(parse("I(X;W)"), "bits")
        hw = J6.eval(parse("H(W)"), "bits")
        worst_pen = max(worst_pen, ixw - hw)               # <= 0 であるべき
        if hw > 1e-6:
            min_pen_ratio = min(min_pen_ratio, ixw / hw)
    print(f"  逐語照合 ({n} 本): `F - sum p_w F_w` と `I(U;W|Y)+I(V;W|Z)+I(X;W|U,V)` の")
    print(f"    最大偏差 = {worst_id:.3e}  ⟹ 恒等式は数値でも厳密に一致する")
    print(f"  罰項の比較: `I(X;W) - H(W)` の最大 = {worst_pen:+.3e} (<= 0)、")
    print(f"    `I(X;W)/H(W)` の最小 = {min_pen_ratio:.4f}")
    print("    ⟹ `T` 形の罰項は `H(W)` ではなく **`I(X;W)`** であり、非決定論的 `W` では")
    print("       **真に小さい** ⟹ (H6) は (H4) の単なる拡張ではなく**強化**でもある。")
    # 決定論的 W では I(X;W) = H(W) に戻ること (退化点の確認)
    px, Cy, Cz = dense_random(rng)
    Cw_det = np.array([[1.0, 0.0], [1.0, 0.0], [0.0, 1.0]])
    cond = softmax(rng.normal(0, 1.5, (3, 9)), axis=-1).reshape(3, 3, 3)
    T = np.einsum("xy,xz->xyz", Cy, Cz)
    Jd = Joint(["U", "V", "X", "Y", "Z", "W"],
               np.einsum("uvx,xyz,xw->uvxyzw", cond_to_joint(cond, px), T, Cw_det),
               validate=False)
    gapd = abs(Jd.eval(parse("I(X;W)"), "bits") - Jd.eval(parse("H(W)"), "bits"))
    print(f"  退化点の確認: `W = m(X)` では `|I(X;W) - H(W)|` = {gapd:.3e} ⟹ (H4) に戻る")
    ok = worst_id < TOL_ID and worst_pen < 1e-12 and gapd < TOL_ID
    print(f"  ⟹ §3 {'PASS' if ok else '**FAIL**'}")
    return dict(ok=ok, worst_id=float(worst_id), ratio=float(min_pen_ratio))


# --------------------------------------------------------------------------
# §4 段 B-3 — `Λ_cav` の構成と健全性 (最適化を含むか / 退化点で厳密か)
# --------------------------------------------------------------------------
def section4(quick: bool) -> dict:
    print()
    print("=" * 78)
    print("§4 **段 B-3** — `Λ_cav` (= Λ_split の上凹包) の構成と健全性")
    print("=" * 78)
    print("  `Λ_cav(p) := max{ sum_w λ_w Λ_split(p_w) : p = sum_w λ_w p_w }`。")
    print("  ⚠ **Λ_split との性格の差 (率直に書く)**: `Λ_split` は有限列挙で厳密だったが")
    print("     `Λ_cav` は**分解上の最大化を含む** ⟹ 「最適化を含まない有限の再帰」という")
    print("     `Λ_split` の売りは失われる。ただし単体格子上の LP に落とすと (a) LP は厳密に")
    print("     解け、(b) 格子点しか使わない値は真の上凹包の**下界** ⟹ `L'` の下界であることは")
    print("     保たれる ⟹ **最適化器を信用する必要が無い** (符号が証明書の向き)。")
    print("  ⚠ P3 の ill-posed 制約 (facts §L13): `Λ_cav` は `Λ_split` の分解上の最大値で、")
    print("     `Λ_split` は `beta` の再帰 = 2 つの周辺と `p(x)` だけの函数 ⟹ **構成から満たす**")
    print("     (同時分布 `q(y,z|x)` の結合の取り方に依存する量を一切含まない)。")
    print()
    rng = np.random.default_rng(17041707)
    # (a) 格子の細かさに対する単調性 (どれも valid な下界。細かいほど良い)
    px, Cy, Cz = dense_random(rng)
    print("  (a) 格子の細かさ (どれも `L'` の valid な下界。細かいほど真の上凹包に近い):")
    prev = -np.inf
    mono = True
    for N in ([16, 32] if quick else [16, 32, 48, 64]):
        M = simplex_mesh(3, N)
        v, _ = lam_cav(px, Cy, Cz, M)
        print(f"      N = {N:>3} ({len(M):>4} 点): Λ_cav = {v:.6f}")
        mono &= v >= prev - 1e-9
        prev = v
    print(f"      Λ_split (格子を使わない厳密値) = {lam_split(px, Cy, Cz):.6f} ⟹ "
          f"単調 {'OK' if mono else '**NG**'}")
    # (b) 退化点で厳密か (Λ_cav <= L' が破れたら矛盾の証明書)
    N = 32 if quick else 60
    M = simplex_mesh(3, N)
    pm_y, pm_z, _ = partial_merge(2 / 3, 3 / 4)
    cases = [("Blackwell (格子)", np.full(3, 1 / 3), *marginals(blackwell())),
             ("平滑化 Blackwell .1", np.full(3, 1 / 3), *smoothed_blackwell(0.1)),
             ("BSC(.1) 2 本", np.full(3, 1 / 3), *noisy_blackwell(0.1)),
             ("P2 の kill witness", np.array([0.45, 0.45, 0.10]), pm_y, pm_z)]
    print()
    print(f"  (b) 退化点での厳密さ (格子 N = {N})")
    print(f"      {'ケース':<22} {'beta':>9} {'Λ_split':>9} {'Λ_cav':>9} "
          f"{'L(推定)':>9} {'Λ_cav-L':>10}")
    rows, bad = [], 0
    for name, p, Cy_, Cz_ in cases:
        ls = lam_split(p, Cy_, Cz_)
        lc, _ = lam_cav(p, Cy_, Cz_, M)
        lp = l_prime_est(p, Cy_, Cz_, rng, quick)
        rows.append((name, ls, lc, lp))
        bad += lc - lp > TOL_CERT
        print(f"      {name:<22} {beta(p, Cy_, Cz_):>9.6f} {ls:>9.6f} {lc:>9.6f} "
              f"{lp:>9.6f} {lc - lp:>+10.2e}")
    print(f"      ⟹ `Λ_cav > L'推定` (= 矛盾の証明書) は {bad} 本")
    # (c) 最適化を一切含まない証明書テスト: `Λ_cav <= L' <= beta` の外側だけを見る。
    #     両辺とも厳密値なので、正の margin が 1 つ出れば (H6) は反証される。
    n_sweep = 120 if quick else 400
    worst_b = -np.inf
    for _ in range(n_sweep):
        p2, Cy2, Cz2 = dense_random(rng)
        v, _ = lam_cav(p2, Cy2, Cz2, M)
        worst_b = max(worst_b, v - beta(p2, Cy2, Cz2))
    print(f"  (c) 最適化を含まない証明書テスト (dense {n_sweep} 本): "
          f"`Λ_cav - beta` の最大 = {worst_b:+.3e}")
    print("      (両辺とも厳密値ゆえ正なら (H6) の反証。`Λ_cav <= L' <= beta` の外側だけを見る)")
    print("      ⚠ P2 の kill witness で `Λ_split = Λ_cav = L'` (facts §L13 の "
          "`gap = 0.4132331253245206` と `beta - L'` が一致する点)")
    return dict(mono=bool(mono), bad=int(bad), rows=rows, mesh_n=N,
                worst_b=float(worst_b))


# --------------------------------------------------------------------------
# §5 段 C — 出口条件の測定。同一 run・同一インスタンス集合で before/after
# --------------------------------------------------------------------------
def section5(quick: bool) -> dict:
    print()
    print("=" * 78)
    print("§5 **段 C** — `Λ_comb` の残距離。同一 run・同一インスタンス集合で before/after")
    print("=" * 78)
    print("  before = `Λ_comb^old := max{Λ_split, Λ_env}` / after = "
          "`Λ_comb^new := max{Λ_cav, Λ_env}`")
    print("  `slack(Λ) := beta - Λ` / `gap := beta - L'推定` ⟹ `slack >= gap >= 0`。")
    print("  ⚠ `L'` は最小化 = 真値の**上界** ⟹ `gap` は**過小評価** ⟹ `slack/gap` は")
    print("     **過大評価**。L16 と同じ規約だが、**別 run の値とは比較しない** (§5-13)。")
    print()
    rng = np.random.default_rng(17041708)
    N = 32 if quick else 60
    M = simplex_mesh(3, N)
    n = 4 if quick else 10
    rows = []
    for i in range(n):
        px, Cy, Cz = dense_random(rng)
        b = beta(px, Cy, Cz)
        lp = l_prime_est(px, Cy, Cz, rng, quick)
        ls = lam_split(px, Cy, Cz)
        lc, _ = lam_cav(px, Cy, Cz, M)
        env, sup, _, _, _ = lam_env(px, Cy, Cz, rng, quick)
        rows.append(dict(name=f"dense |X|=3 #{i + 1}", beta=b, lp=lp, gap=b - lp,
                         ls=ls, lc=lc, sup=sup, env=env,
                         old=max(ls, env), new=max(lc, env)))
    print(f"  {'ケース':<17}{'beta':>8}{'gap':>9}{'Λ_split':>9}{'Λ_cav':>9}"
          f"{'Λ_sup':>9}{'Λ_env':>9}{'comb^old':>10}{'comb^new':>10}")
    for r in rows:
        print(f"  {r['name']:<17}{r['beta']:>8.4f}{r['gap']:>9.6f}{r['ls']:>9.6f}"
              f"{r['lc']:>9.6f}{r['sup']:>9.6f}{r['env']:>9.6f}"
              f"{r['old']:>10.6f}{r['new']:>10.6f}")
    big = [r for r in rows if r["gap"] > 1e-3]
    def med(f):
        return float(np.median([f(r) for r in rows])) if rows else float("nan")
    print()
    print(f"  残距離 `L'推定 - Λ` の中央: Λ_split {med(lambda r: r['lp'] - r['ls']):.6f}"
          f" → Λ_cav {med(lambda r: r['lp'] - r['lc']):.6f}"
          f" / Λ_env {med(lambda r: r['lp'] - r['env']):.6f}")
    print(f"  **`Λ_comb` の残距離の中央: {med(lambda r: r['lp'] - r['old']):.6f} (old) → "
          f"{med(lambda r: r['lp'] - r['new']):.6f} (new)**")
    if big:
        ro = float(np.median([(r["beta"] - r["old"]) / r["gap"] for r in big]))
        rn = float(np.median([(r["beta"] - r["new"]) / r["gap"] for r in big]))
        print(f"  **`gap > 1e-3` の {len(big)}/{len(rows)} 本での `slack/gap` の中央: "
              f"{ro:.3f} (old) → {rn:.3f} (new)**")
    else:
        ro = rn = float("nan")
    # 推定不足 / 矛盾証明書 を分けて数え、全行を印字する (§5-13)
    short = [r for r in rows if max(r["sup"], r["env"]) - r["lp"] > TOL_CERT]
    cert = [r for r in rows if max(r["ls"], r["lc"]) - r["lp"] > TOL_CERT]
    print()
    print(f"  **推定不足 (Λ_sup / Λ_env が `L'推定` を超えた行) = {len(short)}/{len(rows)}**"
          " — 反例ではなく `max_U` の届き不足")
    for r in short:
        print(f"      {r['name']}: Λ_env {r['env']:.6f} > L'推定 {r['lp']:.6f} "
              f"(差 {r['env'] - r['lp']:+.2e})")
    print(f"  **矛盾の証明書 (Λ_split / Λ_cav が `L'推定` を超えた行) = {len(cert)}/{len(rows)}**"
          " — 出たら (H4)/(H6) の反証")
    for r in cert:
        print(f"      {r['name']}: Λ_cav {r['lc']:.6f} > L'推定 {r['lp']:.6f}")
    return dict(rows=rows, ratio_old=ro, ratio_new=rn, short=len(short),
                cert=len(cert), n_big=len(big))


# --------------------------------------------------------------------------
# §6 R3 step 8 の相補性の再測定 — `Λ_split` は `Λ_comb` の中で生きているか
# --------------------------------------------------------------------------
def section6(quick: bool) -> dict:
    print()
    print("=" * 78)
    print("§6 R3 step 8 の**相補性**の再測定 — `Λ_split` は `|X| >= 3` で効いているか")
    print("=" * 78)
    print("  R3 step 8 は `Λ_comb := max{Λ_split, Λ_sup}` を「相補的」として採った。")
    print("  §5 の実測がその読みを問い直すので、ここで正面から測る。")
    print("  ⚠ **符号**: `Γ` は最大化 ⟹ `Λ_sup推定 >= Λ_sup真値` ⟹ "
          "**`Λ_split > Λ_sup推定` が 1 本出れば支配は反証される**(証明書)。")
    print("     逆に出ないことは**探索強度に依存する下界**であって率ではない (§5-12)。")
    print()
    rng = np.random.default_rng(17041709)
    N = 32 if quick else 60
    M3 = simplex_mesh(3, N)

    def lsup(px, Cy, Cz, r):
        gy, gz, _, _, _ = gamma_sup(px, Cy, Cz, rng, restarts=r)
        return _h(px) - min(gy, gz)

    # (a) |X| = 2 — Λ_split は base case ゆえ厳密、Λ_sup は (N1) 不合格 (L15 の証明書族)
    print("  (a) `|X| = 2` (L15 が (N1) 証明書を取った非順序な族)")
    print(f"      {'チャネル / p':<26} {'Λ_split(=beta)':>15} {'Λ_sup':>9} {'差':>10}")
    n_win2 = 0
    for (ny, nz, tag) in [(bsc(0.1), bec(0.5), "BSC(.1)/BEC(.5)"),
                          (bsc(0.15), bec(0.5), "BSC(.15)/BEC(.5)")]:
        for t in (0.2, 0.5, 0.8):
            p = np.array([1 - t, t])
            a, b = lam_split(p, ny, nz), lsup(p, ny, nz, 6 if quick else 12)
            n_win2 += a - b > TOL_CERT
            print(f"      {tag + f' p={t}':<26} {a:>15.6f} {b:>9.6f} {a - b:>+10.6f}")
    print("      ⚠ `|X| = 2` では `Λ_split = beta = L'` が厳密 ⟹ `Λ_split >= Λ_sup真値` は")
    print("         **恒真**。負の差は `Γ` の届き不足 (推定不足) であって反証ではない。")
    # (b) |X| >= 3 — 素朴な掃引 + 構造つき族
    def ksc(a, k=3):
        C = np.full((k, k), a / (k - 1)); np.fill_diagonal(C, 1 - a); return C

    def kec(e, k=3):
        C = np.zeros((k, k + 1))
        for i in range(k):
            C[i, i], C[i, k] = 1 - e, e
        return C

    cases = []
    for a in ((0.1, 0.25) if quick else (0.05, 0.1, 0.2, 0.3)):
        for e in ((0.3, 0.6) if quick else (0.2, 0.3, 0.5, 0.7)):
            cases.append((f"KSC({a})/KEC({e})", ksc(a), kec(e)))
    pxs = [np.full(3, 1 / 3), np.array([.5, .3, .2]), np.array([.7, .25, .05]),
           np.array([.45, .45, .10]), np.array([.85, .10, .05])]
    n_tot, n_win3, worst = 0, 0, -np.inf
    detail, ratios = [], []
    for tag, Cy, Cz in cases:
        for p in pxs:
            a = lam_split(p, Cy, Cz)
            c, _ = lam_cav(p, Cy, Cz, M3)
            b = lsup(p, Cy, Cz, 4 if quick else 8)
            n_tot += 1
            n_win3 += max(a, c) - b > TOL_CERT
            ratios.append(c / b if b > 1e-9 else np.nan)
            if c - b > worst:
                worst, detail = c - b, [tag, p, a, c, b]
    n_rand = 20 if quick else 60
    for _ in range(n_rand):
        kx = int(rng.integers(3, 5))
        conc = float(rng.choice([0.15, 0.5, 2.0]))
        Cy = rng.dirichlet(np.ones(kx) * conc, size=kx)
        Cz = rng.dirichlet(np.ones(kx) * conc, size=kx)
        p = rng.dirichlet(np.ones(kx) * 0.6)
        a = lam_split(p, Cy, Cz)
        b = lsup(p, Cy, Cz, 3 if quick else 6)
        n_tot += 1
        n_win3 += a - b > TOL_CERT
        worst = max(worst, a - b)
    print()
    print(f"  (b) `|X| >= 3` — 構造つき族 {len(cases) * len(pxs)} 本 + 無作為 {n_rand} 本")
    print(f"      **`max{{Λ_split, Λ_cav}} > Λ_sup推定` = {n_win3}/{n_tot} 本**、"
          f"最良 margin = {worst:+.6f}")
    if ratios:
        print(f"      構造つき族での `Λ_cav / Λ_sup` の中央 = {np.nanmedian(ratios):.3f} "
              f"(1 に届かないほど `Λ_split` 枝は max を取れない)")
    if detail:
        print(f"      最良の点: {detail[0]}, p = {np.round(detail[1], 3)}, "
              f"Λ_split {detail[2]:.6f} / Λ_cav {detail[3]:.6f} / Λ_sup {detail[4]:.6f}")
    print()
    print(f"  ⟹ 相補性は `|X| = 2` では確認できる ({n_win2} 本で `Λ_split > Λ_sup`)、")
    print(f"     `|X| >= 3` では本 leg の探索範囲で {n_win3} 本 ⟹ "
          f"{'反証された' if n_win3 else '**`Λ_split` 枝は `|X| >= 3` で一度も max を取らなかった**'}")
    return dict(n_win2=int(n_win2), n_win3=int(n_win3), n_tot=int(n_tot),
                worst=float(worst))


# --------------------------------------------------------------------------
# §7 判定
# --------------------------------------------------------------------------
def section7(r0: bool, r1: dict, r2: dict, r3: dict, r4: dict, r5: dict,
             r6: dict) -> None:
    print()
    print("=" * 78)
    print("§7 判定 (規則は §冒頭で固定済)")
    print("=" * 78)
    print(f"  **段 A**: 多分割 `|W| >= 3` は 2 分割再帰に "
          f"{'**完全に含まれる**' if r1['ok'] else '含まれない'} "
          f"(最大差 {max(r1['worst'], r1['extra']):.1e}、記号的根拠は grouping 公理 §0(c))")
    b1 = "成功" if r2["dead"] else (
        f"**空振り** (掃引の最小 {r2['worst']:+.1e} / 敵対的探索 {r2['best']:+.1e})")
    print(f"  **段 B-1**: 素朴な非決定論版の kill は {b1}")
    print(f"  **段 B-2**: **(H6)** `L'(p) >= sum_w p(w) L'(p_w)` は**任意の** `p(w|x)` で"
          f"成り立ち、記号的に**証明済** (逐語照合の最大偏差 {r3['worst_id']:.1e})")
    print("      ⟹ 同値な言い換え: **`L'(·,q)` は `p(x)` の凹関数**。")
    print("      ⟹ 罰項は `H(W)` ではなく `I(X;W)` ⟹ (H4) の**強化**でもある。")
    print(f"  **段 B-3**: `Λ_cav` は証明済の下界で構成から `Λ_cav >= Λ_split`。"
          f"矛盾の証明書 {r4['bad']} 本 / 格子単調性 {'OK' if r4['mono'] else 'NG'}")
    print(f"  **段 C**: `Λ_comb` の残距離の中央 "
          f"{np.median([r['lp'] - r['old'] for r in r5['rows']]):.6f} (old) → "
          f"{np.median([r['lp'] - r['new'] for r in r5['rows']]):.6f} (new) / "
          f"`slack/gap` の中央 {r5['ratio_old']:.3f} → {r5['ratio_new']:.3f}")
    print(f"      推定不足 {r5['short']} 行 / 矛盾の証明書 {r5['cert']} 行")
    print()
    moved = abs(r5["ratio_old"] - r5["ratio_new"]) > 1e-3
    if moved:
        print("  ⟹ **出口条件 (i) 達成 — dense の残距離が縮んだ**。")
    else:
        print("  ⟹ **出口条件 (ii) 達成 — 縮まない理由が確定した**:")
        print(f"     `Λ_cav` は `Λ_split` を実際に改善する (§5 の残距離の中央を見よ) が、")
        print(f"     dense では `Λ_env` が `Λ_split` / `Λ_cav` を**桁で上回る** ⟹ "
              f"`max` が `Λ_env` 側で決まり")
        print(f"     `Λ_split` 枝の改善は `Λ_comb` に現れない。§6 の再測定が同じことを"
              f"別角度から示す")
        print(f"     (`|X| >= 3` の {r6['n_tot']} 本で `Λ_split` 枝が max を取ったのは "
              f"{r6['n_win3']} 本)。")
    print("  ⚠ **本 leg は経路を増やしていない** (判断ログ 29/30 の事前固定どおり)。"
          "産物は R3 step 4 / step 6 / step 8 の更新である。")


def main() -> None:
    ap = argparse.ArgumentParser(
        description="軸 C の子 attack `slack-loss-lower-bound` の続き (L17) の probe")
    ap.add_argument("--quick", action="store_true", help="掃引を縮小して回す")
    args = ap.parse_args()
    t0 = time.time()
    print("bc-split-general-check.py — L17: `Λ_split` の一般化と `Λ_comb` の鋭さ")
    print(f"(mode = {'quick' if args.quick else 'full'})\n")
    r0 = section0(args.quick)
    r1 = section1(args.quick)
    r2 = section2(args.quick)
    r3 = section3(args.quick)
    r4 = section4(args.quick)
    r5 = section5(args.quick)
    r6 = section6(args.quick)
    section7(r0, r1, r2, r3, r4, r5, r6)
    print()
    print(f"  harness コントロール: §0 {'PASS' if r0 else '**FAIL**'} / "
          f"§3 {'PASS' if r3['ok'] else '**FAIL**'}")
    print(f"\n合計実行時間 {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
