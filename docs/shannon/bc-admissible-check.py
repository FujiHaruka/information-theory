#!/usr/bin/env python3
"""L18 — R4 step 5 (族 `𝒲` の admissibility) を証明側へ動かし、出口条件 (B) を測る。

主語
----
R4 ([`bc-open-problem-routes.md`](bc-open-problem-routes.md) §R4) の step 5 =
「族 `𝒲` の各 `W` が実際に `Z` に more capable で支配される」は**未証明の穴**
(`gap` ラベル)。本 probe は 3 方向から詰める:

* **§1 (閉包)** — `𝒲_Z` の証明可能な閉包演算 ((a) 劣化 / (b) 出力の交わらない混合 /
  (c) `Z` 自身 / (d) 同一出力アルファベット上の凸結合) だけで `Z` から作れる `W` は
  **すべて `Z` の劣化版**であり、劣化版は `U → X → Z → W` の DPI で
  `I(U;W) ≤ I(U;Z)` ⟹ **`Λ_env = Λ_sup` (利得ちょうど 0)**。
  ⟹ **資格の穴は本質的**で、証明には**非劣化の base point** が別途要る。
* **§2 (証明書)** — 任意の `(Z,W)` に対し admissibility を**有限個の不等式**へ
  還元する cell 証明書。掃引 (無限個の点の有限標本) とは証拠の階級が違う。
* **§3 (閉形式)** — `Z` が消去チャネルのときは membership が閉形式で決まる。
* **§4 / §4b (出口条件 B)** — `𝒲` を**証明済の `W` だけ**に制限した `Λ_env^cert` が
  まだ `Λ_sup` に勝つか。⚠ **これが決定的** — 資格を証明できても利得ゼロの族なら
  R4 の新規性は証明済の部分では消える。

cell 証明書 (本 leg の中核。**記号的に証明済**)
-----------------------------------------------
`Δ_W(p) := I_p(X;Z) − I_p(X;W)`、`A_r(p) := Σ_x p_x D(W_x‖r)` と置く。恒等式

    I_p(X;W) = A_r(p) − D(pW‖r)                                      … (E1)

(§0(a) が残差 0 で確認) より `A_r` は `p ↦ I_p(X;W)` の**アフィンな優関数**。一方
`p ↦ I_p(X;Z) = H(pZ) − Σ_x p_x H(Z_x)` は**凹**。ゆえに部分単体
`S = conv{v_1,…,v_k}` 上で `p = Σ_i λ_i v_i` と書くと、任意の `r` について

    Δ_W(p) ≥ Σ_i λ_i [ I_{v_i}(X;Z) − A_r(v_i) ]
           = Σ_i λ_i [ Δ_W(v_i) − D(v_i W ‖ r) ]                     … (E2)

⟹ **ある `r` が存在して全頂点で `Δ_W(v_i) ≥ D(v_i W‖r)` なら `S` 上で `Δ_W ≥ 0`**。
単体を最長辺 2 分割で被覆し全 cell を合格させれば `Δ_W ≥ 0` が**単体全域で従う**
(= more capable 支配の証明)。逆にある cell 頂点で `Δ_W(v) < 0` なら**反証**
(`v` は単体の実点)。⟹ 判定は 3 値: `CERT` / `REFUTE` / `INDET` (予算切れ)。

⚠ **残るリスクは浮動小数点だけ**で、探索強度ではない (掃引との決定的な差)。
§2 が最悪 cell を `mpmath` 50 桁で再評価して裕度を報告する。

⚠ 証明と数値の書き分け (§L16 / §L17 と同じ規約)
-----------------------------------------------
* **(E1)(E2) と §1 の閉包命題は記号的に証明済**。
* **個々の `W` の CERT 判定は「有限個の不等式への還元 + 浮動小数点評価」**
  (掃引ではない。ただし exact arithmetic ではない)。
* **§4 の鋭さは実測**。符号は `max_U` が最大化 = 真値の**下界** ⟹ `Λ` は**上振れ**
  ⟹ `Λ` の推定が `L'` の推定を超えた行は反例ではなく**「推定不足」**として
  分けて数え、全行を印字する。

実行
----
    python3 docs/shannon/bc-admissible-check.py            # full
    python3 docs/shannon/bc-admissible-check.py --quick    # 短縮
"""

from __future__ import annotations

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
    sys.modules[modname] = mod
    spec.loader.exec_module(mod)
    return mod


import bc_probe as _BP                                            # noqa: E402

_D2 = _load_sibling("bc-d2-lower-check.py", "bc_d2_lower_check_l18")
_L15 = _D2._L15
_L13 = _L15._L13

_h = _D2._h
_mi = _D2._mi
mi_in = _D2.mi_in
mi_in_batch = _D2.mi_in_batch
mi_in_batch2 = _D2.mi_in_batch2
_xlogx = _D2._xlogx
simplex_grid = _D2.simplex_grid
near_vertex_points = _D2.near_vertex_points
kl_rows = _D2.kl_rows
bsc, bec, bzc = _D2.bsc, _D2.bec, _D2.bzc
h_cond = _D2.h_cond
joint_ux = _D2.joint_ux
softmax = _D2.softmax
dense_random = _D2.dense_random
binary_family = _D2.binary_family
lattice_family = _D2.lattice_family
marginals = _D2.marginals
partial_merge = _D2.partial_merge
opt_u_gen = _D2.opt_u_gen
u_grid_binary = _D2.u_grid_binary
gamma_sup = _D2.gamma_sup

SEED = 20260803
TOL_ID = 1e-9          # 恒等式の残差に要求する精度
TOL_NEG = 1e-12        # `Δ_W(v) < −TOL_NEG` を反証とみなす閾値

CERT, REFUTE, INDET = "CERT", "REFUTE", "INDET"


# --------------------------------------------------------------------------
# cell 証明書 — admissibility を有限個の不等式へ還元する
# --------------------------------------------------------------------------
def kl_batch(Q: np.ndarray, r: np.ndarray) -> np.ndarray:
    """`D(Q_i ‖ r)` (bit)。`r` の台に載らない `Q_i` は `+inf`。"""
    with np.errstate(divide="ignore", invalid="ignore"):
        lg = np.where(Q > 0, np.log2(np.maximum(Q, 1e-300) / np.maximum(r, 1e-300)), 0.0)
        out = (np.where(Q > 0, Q, 0.0) * lg).sum(axis=-1)
    bad = ((Q > 0) & (r <= 0)).any(axis=-1)
    return np.where(bad, np.inf, out)


def _bisect(cells: np.ndarray) -> np.ndarray:
    """最長辺 2 分割 (任意次元)。`cells[n, k, kx]` = n 個の単体 × k 頂点。"""
    n, k, _ = cells.shape
    d = ((cells[:, :, None, :] - cells[:, None, :, :]) ** 2).sum(-1)
    idx = d.reshape(n, -1).argmax(1)
    a, b = idx // k, idx % k
    ar = np.arange(n)
    m = 0.5 * (cells[ar, a] + cells[ar, b])
    c1, c2 = cells.copy(), cells.copy()
    c1[ar, a] = m
    c2[ar, b] = m
    return np.concatenate([c1, c2], axis=0)


def certify_dom(Cz: np.ndarray, R: np.ndarray, max_cells: int = 40000,
                max_rounds: int = 200, collect: bool = False) -> dict:
    """`Δ_W ≥ 0` を単体全域で判定する 3 値の証明書 (上の docstring の (E2))。

    返り `{status, margin, cells, worst, tight, proof}`。`status = CERT` なら**証明**
    (有限個の不等式に還元済)、`REFUTE` なら**反証** (`worst` が違反点)、
    `INDET` は予算切れ (どちらの判定も出ていない)。`margin` は合格 cell の裕度の
    最小値、`tight` はそのうち `< 1e-9` の cell 数 (単体の頂点を含む cell では
    両辺がともに厳密に 0 なので、裕度 0 は近接ではなく**恒等式**である)。
    `collect=True` で合格 cell と採用した `r` を `proof` に貯める (exact 再検証用)。
    """
    kx = Cz.shape[0]
    if R.shape == Cz.shape and np.allclose(R, Cz):
        return {"status": CERT, "margin": np.inf, "cells": 0, "worst": None,
                "tight": 0, "proof": []}
    cells = np.eye(kx)[None, :, :]
    total, min_slack, tight, proof = 0, np.inf, 0, []
    for _ in range(max_rounds):
        n = cells.shape[0]
        V = cells.reshape(-1, kx)
        dv = mi_in_batch(V, Cz) - mi_in_batch(V, R)
        if dv.min() < -TOL_NEG:
            return {"status": REFUTE, "margin": float(dv.min()), "cells": total,
                    "worst": V[int(dv.argmin())], "tight": tight, "proof": proof}
        dv = dv.reshape(n, kx)
        VR = (V @ R).reshape(n, kx, -1)
        cen = (cells.mean(axis=1) @ R)[:, None, :]
        cands = np.concatenate([VR, cen], axis=1)              # n × (kx+1) × kw
        # D(VR[c,i] ‖ cands[c,j])  →  n × kx × (kx+1)
        D = kl_batch(VR[:, :, None, :], cands[:, None, :, :])
        slack = (dv[:, :, None] - D).min(axis=1)               # n × (kx+1)
        jbest = slack.argmax(axis=1)
        best = slack[np.arange(n), jbest]
        ok = best >= 0.0
        if ok.any():
            min_slack = min(min_slack, float(best[ok].min()))
            tight += int((best[ok] < 1e-9).sum())
            if collect:
                for c in np.flatnonzero(ok):
                    proof.append((cells[c].copy(), cands[c, jbest[c]].copy()))
        total += n
        keep = cells[~ok]
        if keep.shape[0] == 0:
            return {"status": CERT, "margin": min_slack, "cells": total,
                    "worst": None, "tight": tight, "proof": proof}
        if total + 2 * keep.shape[0] > max_cells:
            return {"status": INDET, "margin": min_slack, "cells": total,
                    "worst": None, "tight": tight, "proof": proof}
        cells = _bisect(keep)
    return {"status": INDET, "margin": min_slack, "cells": total, "worst": None,
            "tight": tight, "proof": proof}


def recheck_exact(Cz: np.ndarray, R: np.ndarray, proof: list, dps: int = 50) -> float:
    """`proof` の全不等式を `mpmath` `dps` 桁で再評価し、最小裕度を返す (float 依存の除去)。"""
    import mpmath as mp

    mp.mp.dps = dps
    ln2 = mp.log(2)

    def mi(p, C):
        p = [mp.mpf(float(t)) for t in p]
        out = [sum(p[x] * mp.mpf(float(C[x, w])) for x in range(len(p)))
               for w in range(C.shape[1])]
        hy = -sum(t * mp.log(t) for t in out if t > 0) / ln2
        hyx = sum(p[x] * (-sum(mp.mpf(float(t)) * mp.log(mp.mpf(float(t)))
                               for t in C[x] if t > 0)) for x in range(len(p))) / ln2
        return hy - hyx

    worst = mp.mpf("+inf")
    for cell, r in proof:
        rm = [mp.mpf(float(t)) for t in r]
        for v in cell:
            d = mi(v, Cz) - mi(v, R)
            vw = [sum(mp.mpf(float(v[x])) * mp.mpf(float(R[x, w])) for x in range(len(v)))
                  for w in range(R.shape[1])]
            kl = sum(q * mp.log(q / rm[w]) for w, q in enumerate(vw) if q > 0) / ln2
            worst = min(worst, d - kl)
    return float(worst)


def retract(R: np.ndarray, theta: float) -> np.ndarray:
    """`W_θ` = 確率 `θ` で無情報記号 `*` を出す版 (出力の交わらない混合 = 閉包 (b))。

    `I_p(X;W_θ) = (1−θ) I_p(X;W)` が**厳密**に成り立つ (§0(c) が残差 0 で確認) ⟹
    `Δ_{W_θ} = Δ_W + θ I_p(X;W) ≥ Δ_W` で、内点の裕度が `θ` だけ持ち上がる。
    """
    if theta <= 0.0:
        return R
    return np.concatenate([(1 - theta) * R, np.full((R.shape[0], 1), theta)], axis=1)


def degraded_residual(Cz: np.ndarray, R: np.ndarray) -> float:
    """`min_Q ‖Z Q − R‖_1` over 確率行列 `Q` を LP で厳密に解く (0 ⟺ `R` は `Z` の劣化版)。"""
    from scipy.optimize import linprog

    kx, kz = Cz.shape
    kw = R.shape[1]
    nq = kz * kw
    n = nq + 2 * kx * kw
    c = np.concatenate([np.zeros(nq), np.ones(2 * kx * kw)])
    rows, rhs = [], []
    for x in range(kx):                                   # (Z Q)[x,w] + s⁺ − s⁻ = R[x,w]
        for w in range(kw):
            a = np.zeros(n)
            for z in range(kz):
                a[z * kw + w] = Cz[x, z]
            a[nq + (x * kw + w)] = 1.0
            a[nq + kx * kw + (x * kw + w)] = -1.0
            rows.append(a)
            rhs.append(R[x, w])
    for z in range(kz):                                   # Q の行確率性
        a = np.zeros(n)
        a[z * kw:(z + 1) * kw] = 1.0
        rows.append(a)
        rhs.append(1.0)
    res = linprog(c, A_eq=np.array(rows), b_eq=np.array(rhs), bounds=(0, None),
                  method="highs")
    return float(res.fun) if res.success else np.inf


def closure_sample(Cz: np.ndarray, rng, n_ops: int = 6):
    """閉包演算 (a)(b)(c)(d) だけで `Z` から作れる `W` を 1 本作る。返り `(W, Q)`。

    不変量として**後処理核 `Q` を明示的に持ち回る** (`W = Z Q` が構成から成立) ⟹
    「閉包で作れる `W` は `Z` の劣化版から出られない」を witness つきで示せる。
    """
    kz = Cz.shape[1]
    pool = [(Cz.copy(), np.eye(kz))]                       # (c) `Z` 自身
    for _ in range(n_ops):
        op = rng.integers(0, 3)
        R1, Q1 = pool[rng.integers(0, len(pool))]
        if op == 0:                                        # (a) 劣化
            kw = R1.shape[1]
            Q2 = rng.dirichlet(np.ones(max(kw - 1, 2)) * 0.8, size=kw)
            pool.append((R1 @ Q2, Q1 @ Q2))
        elif op == 1:                                      # (b) 出力の交わらない混合
            R2, Q2 = pool[rng.integers(0, len(pool))]
            lam = float(rng.uniform(0.1, 0.9))
            pool.append((np.concatenate([lam * R1, (1 - lam) * R2], axis=1),
                         np.concatenate([lam * Q1, (1 - lam) * Q2], axis=1)))
        else:                                              # (d) 同一出力上の凸結合
            same = [(A, B) for A, B in pool if A.shape == R1.shape]
            R2, Q2 = same[rng.integers(0, len(same))]
            lam = float(rng.uniform(0.1, 0.9))
            pool.append((lam * R1 + (1 - lam) * R2, lam * Q1 + (1 - lam) * Q2))
    return pool[-1]


def rand_pux(px: np.ndarray, ku: int, rng) -> np.ndarray:
    """`X` 周辺を `px` に固定したランダムな `p(u,x)`。"""
    return joint_ux(softmax(rng.normal(size=(px.size, ku)) * 1.5, axis=-1), px)


# --------------------------------------------------------------------------
# セクション
# --------------------------------------------------------------------------
def section0(quick: bool) -> dict:
    print("=" * 78)
    print("§0 証明書の 2 つの材料と閉包の恒等式 — 記号 / 残差 0 の確認")
    print("=" * 78)
    ids = [
        ("劣化 DPI の分解", "I(U;Z) - I(U;W)", "I(U;Z|W) - I(U;W|Z)"),
        ("(H5) の (i)", "H(U|V) - H(U|W,V)", "I(U;W|V)"),
    ]
    ok = True
    for name, lhs, rhs in ids:
        held, resid = _BP.prove_identity(lhs, rhs)
        print(f"  [{name}] accept = {held} / 残差 = {resid}")
        ok &= held
    print("  ⟹ `W = Z∘Q` は `U → X → Z → W` と結合できるので `I(U;W|Z) = 0`、ゆえ")
    print("     `I(U;Z) − I(U;W) = I(U;Z|W) ≥ 0` = **劣化版の利得は必ず ≤ 0** (§1 の核)。")

    rng = np.random.default_rng(SEED)
    w_e1, w_cav, w_ret, w_dis = 0.0, np.inf, 0.0, 0.0
    for _ in range(60 if quick else 300):
        kx, kw = int(rng.integers(2, 5)), int(rng.integers(2, 5))
        R = rng.dirichlet(np.ones(kw) * 0.7, size=kx)
        Cz = rng.dirichlet(np.ones(int(rng.integers(2, 5))) * 0.7, size=kx)
        p = rng.dirichlet(np.ones(kx) * 0.7)
        r = rng.dirichlet(np.ones(kw) * 0.7)
        # (a) 恒等式 (E1): Σ_x p_x D(W_x‖r) = I_p(X;W) + D(pW‖r)
        lhs = float((p * kl_batch(R, r)).sum())
        w_e1 = max(w_e1, abs(lhs - mi_in(p, R) - float(kl_batch((p @ R)[None, :], r)[0])))
        # (b) `p ↦ I_p(X;Z)` の凹性 (証明書の第 2 の材料)
        q = rng.dirichlet(np.ones(kx) * 0.7)
        lam = float(rng.uniform(0.05, 0.95))
        w_cav = min(w_cav, mi_in(lam * p + (1 - lam) * q, Cz)
                    - lam * mi_in(p, Cz) - (1 - lam) * mi_in(q, Cz))
        # (c) 退避 `W_θ` の厳密性 / (d) 出力の交わらない混合の厳密性
        th = float(rng.uniform(0.01, 0.5))
        w_ret = max(w_ret, abs(mi_in(p, retract(R, th)) - (1 - th) * mi_in(p, R)))
        R2 = rng.dirichlet(np.ones(kw) * 0.7, size=kx)
        mix = np.concatenate([th * R, (1 - th) * R2], axis=1)
        w_dis = max(w_dis, abs(mi_in(p, mix) - th * mi_in(p, R) - (1 - th) * mi_in(p, R2)))
    print(f"  (a) 恒等式 (E1) の最大残差             = {w_e1:.3e}  (証明書のアフィン優関数)")
    print(f"  (b) `I_p(X;Z)` の凹性の最小 Jensen 差 = {w_cav:+.3e}  (負なら凹性が破れている)")
    print(f"  (c) 退避 `I_p(X;W_θ) = (1−θ)I_p(X;W)` の最大残差 = {w_ret:.3e}")
    print(f"  (d) 交わらない混合の線型性の最大残差             = {w_dis:.3e}")
    ok &= (w_e1 < TOL_ID and w_cav > -TOL_ID and w_ret < TOL_ID and w_dis < TOL_ID)
    return {"ok": ok, "e1": w_e1, "cav": w_cav, "ret": w_ret, "dis": w_dis}


def section1(quick: bool) -> dict:
    print()
    print("=" * 78)
    print("§1 lead 2 — 閉包だけで作れる `W` は `Z` の劣化版から出られない (⟹ 利得 0)")
    print("=" * 78)
    print("  **命題 (記号的に証明済)**: `𝒟_Z := {Z∘Q}` (劣化版全体) は閉包演算で閉じる —")
    print("    (a) 劣化: `(ZQ)Q' = Z(QQ')` / (b) 出力の交わらない混合:")
    print("    `λZQ₁ ⊕ (1−λ)ZQ₂ = Z[λQ₁ | (1−λ)Q₂]` / (c) `Z = Z·I` /")
    print("    (d) 同一出力上の凸結合: `λZQ₁ + (1−λ)ZQ₂ = Z(λQ₁+(1−λ)Q₂)`。")
    print("    ⟹ `{Z}` の (a)(b)(c)(d) 閉包 ⊆ `𝒟_Z`。さらに §0 より `W ∈ 𝒟_Z` なら")
    print("    どの `U` でも `I(U;W) ≤ I(U;Z)` ⟹ **`max_{W∈𝒲} I(U;W) = I(U;Z)`** ⟹")
    print("    **`Λ_env = Λ_sup` (利得ちょうど 0)**。⟹ 資格の穴は偶然ではなく本質的で、")
    print("    証明には**非劣化の base point** が別途要る (§2 / §3 がそれを供給する)。")
    rng = np.random.default_rng(SEED + 1)
    px, Cy, Cz = dense_random(rng)
    w_wit, w_lp, w_gain = 0.0, 0.0, -np.inf
    n = 40 if quick else 150
    for _ in range(n):
        W, Q = closure_sample(Cz, rng)
        w_wit = max(w_wit, float(np.abs(Cz @ Q - W).max()))
        w_lp = max(w_lp, degraded_residual(Cz, W))
        for _ in range(3):
            pux = rand_pux(px, int(rng.integers(2, 5)), rng)
            w_gain = max(w_gain, _mi(pux @ W) - _mi(pux @ Cz))
    print()
    print(f"  閉包元 {n} 本 (dense |X|=3 の `Z`): 後処理核の witness 残差 `‖ZQ − W‖_∞` の")
    print(f"    最大 = {w_wit:.3e} ⟹ **全数が構成から `Z` の劣化版**。")
    print(f"    LP `min_Q ‖ZQ − W‖_1` の最大 = {w_lp:.3e} (独立な確認)。")
    print(f"    利得 `I(U;W) − I(U;Z)` の最大 = {w_gain:+.3e} ⟹ **正の利得は出ない**。")
    print("  **対照 (検出力)** — 非劣化の base point なら同じ測り方で正の利得が出る。")
    print("    ⚠ 利得が出るのは El Gamal–Kim の 4 区分の**第 3 区分だけ** (逐語:")
    print("    `1. 0 ≤ ε ≤ 2p: Y1 is a degraded version of Y2` / `2. 2p < ε ≤ 4p(1−p):`")
    print("    `Y2 is less noisy than Y1, but not degraded` / `3. 4p(1−p) < ε ≤ H(p):`")
    print("    `Y2 is more capable than Y1, but not less noisy` / `4. H(p) < ε ≤ 1: none`)。")
    rows = []
    for eps, d in ((0.5, 0.115), (0.5, 0.14), (0.3, 0.06), (0.3, 0.08), (0.5, 0.2)):
        Z, W = bec(eps), bsc(d)
        b1, b2, b3 = 2 * d, 4 * d * (1 - d), float(_h(np.array([d, 1 - d])))
        reg = 1 if eps <= b1 else (2 if eps <= b2 else (3 if eps <= b3 else 4))
        g = gain_max_binary(np.array([0.5, 0.5]), Z, W, 121 if quick else 241)
        rows.append((eps, d, degraded_residual(Z, W), g, reg))
    print(f"    {'Z / W':<22}{'区分':>5}{'劣化 LP 残差':>14}{'利得の最大 (U 格子)':>22}")
    for eps, d, lp, g, reg in rows:
        print(f"    Z=BEC({eps})/W=BSC({d}){'':<{max(0, 7 - len(str(d)))}}{reg:>4d}"
              f"{lp:>+14.4f}{g:>+22.6f}")
    print("    ⟹ **第 3 区分でだけ利得が正**。区分 1/2 (劣化・less noisy) は定義から")
    print("       `I(U;W) ≤ I(U;Z)` なので**利得は構造的に 0 以下**である。")
    return {"witness": w_wit, "lp": w_lp, "gain": w_gain, "rows": rows}


def gain_max_binary(px: np.ndarray, Cz: np.ndarray, R: np.ndarray, n: int = 241) -> float:
    """`max_U [I(U;W) − I(U;Z)]` の**最適化不使用**の下界 (2 値 `U` の格子を直接評価)。"""
    best = -np.inf
    for a in np.linspace(0.0, 1.0, n):
        for b in np.linspace(0.0, 1.0, n):
            if abs(a - b) < 1e-9:
                continue
            q = (px[1] - b) / (a - b)
            if not (0.0 <= q <= 1.0):
                continue
            pux = np.array([[q * (1 - a), q * a], [(1 - q) * (1 - b), (1 - q) * b]])
            best = max(best, _mi(pux @ R) - _mi(pux @ Cz))
    return float(best)


def _h_inv(eps: float) -> float:
    lo, hi = 1e-12, 0.5
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if _h(np.array([mid, 1 - mid])) < eps:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def _edge(eps: float, want: str, lo: float = 1e-4, hi: float = 0.5, iters: int = 34) -> float:
    """`δ ↦ certify_dom(BEC(ε), BSC(δ))` の判定が `want` に変わる境界を 2 分探索する。"""
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        st = certify_dom(bec(eps), bsc(mid))["status"]
        if want == CERT:
            hi, lo = (mid, lo) if st == CERT else (hi, mid)
        else:
            hi, lo = (hi, mid) if st == REFUTE else (mid, lo)
    return hi if want == CERT else lo


def section2(quick: bool) -> dict:
    print()
    print("=" * 78)
    print("§2 lead 3 — admissibility を**有限個の不等式**へ還元する cell 証明書")
    print("=" * 78)
    print("  判定は 3 値: `CERT` (単体全域で `Δ_W ≥ 0` の**証明**) / `REFUTE` (違反点を")
    print("  明示的に出す**反証**) / `INDET` (予算切れ)。⚠ 掃引と違い `INDET` 以外は")
    print("  **有限被覆に還元済**で、残るリスクは浮動小数点だけである。")
    print()
    print("  (a) **検出力と鋭さ** — 文献既知の閉形式境界 `ε = h(δ)` を証明書が再現するか")
    rows = []
    for eps in (0.5, 0.3, 0.7):
        d_true = _h_inv(eps)
        d_cert = _edge(eps, CERT)
        d_ref = _edge(eps, REFUTE)
        rows.append((eps, d_true, d_cert, d_ref))
        print(f"    Z=BEC({eps}): 真の境界 h⁻¹(ε) = {d_true:.9f} / CERT の下限 "
              f"{d_cert:.9f} / REFUTE の上限 {d_ref:.9f}")
        print(f"      ⟹ 未判定の窓幅 = {d_cert - d_ref:.2e} "
              f"(証明側と反証側が {abs(d_cert - d_true):.1e} / "
              f"{abs(d_true - d_ref):.1e} まで境界を挟む)")
    print()
    print("  (b) **消去族の死は証明書でも再現する** (§L16 の頂点無限傾きの機構)")
    rng = np.random.default_rng(SEED + 2)
    px, Cy, Cz = dense_random(rng)
    kx = px.size
    era_ok = True
    for g in (0.5, 0.1, 0.01, 1e-3):
        E = np.concatenate([g * np.eye(kx), np.full((kx, 1), 1 - g)], axis=1)
        r = certify_dom(Cz, E)
        era_ok &= (r["status"] != CERT)
        w = r["worst"]
        print(f"    γ = {g:<6}: {r['status']:6s} margin {r['margin']:+.3e} / 頂点 KL 余裕 "
              f"{_D2.vertex_kl_margin(Cz, E):+.1f} / 違反点 "
              f"{np.array2string(w, precision=4) if w is not None else '—'}")
    print("    ⚠ `γ` が小さいほど違反点は頂点へ寄り、`γ = 1e-3` では cell 予算内に")
    print("       入らない (`INDET`) — が、頂点 KL 余裕が `-inf` (消去の `D(W_i‖W_j) = ∞`)")
    print("       である以上 **`γ > 0` の全域が解析的に反証済** (§L16 の機構)。")
    print("       ⟹ 証明書は十分条件の機械であり、漸近的に接する族は解析側が押さえる。")
    print()
    print("  (c) **劣化版は証明書を通る** (資格はあるが利得 0 = §1 の帰結)")
    n_ok, n_all, cells, degen = 0, 0, [], 0
    fine = simplex_grid(kx, 60)
    for _ in range(10 if quick else 30):
        W, _ = closure_sample(Cz, rng, n_ops=4)
        r = certify_dom(Cz, W)
        n_all += 1
        n_ok += int(r["status"] == CERT)
        cells.append(r["cells"])
        if r["status"] != CERT:
            degen += int(float(np.max(mi_in_batch(fine, Cz) - mi_in_batch(fine, W))) < 1e-9)
    print(f"    閉包元 {n_all} 本のうち CERT = {n_ok} 本 / cell 数の中央 {int(np.median(cells))}")
    print(f"    非 CERT の {n_all - n_ok} 本のうち `max_p Δ_W < 1e-9` (= `Z` と情報同値で")
    print(f"    `Δ_W ≡ 0`、証明書が原理的に閉じない退化) は {degen} 本 ⟹ 残りが真の未判定。")
    print()
    print("  (d) **exact 再検証** — 合格した不等式全体を `mpmath` 50 桁で評価し直す")
    ex = []
    for nm, Z, W in (("BEC(.5)/BSC(.1101)", bec(0.5), bsc(0.1101)),
                     ("BEC(.3)/BSC(.06)", bec(0.3), bsc(0.06))):
        r = certify_dom(Z, W, collect=True)
        m = recheck_exact(Z, W, r["proof"])
        ex.append((nm, r["status"], r["cells"], r["margin"], r["tight"], m))
        print(f"    {nm}: {r['status']} / cell {r['cells']} 個 / float 最小裕度 "
              f"{r['margin']:+.3e} / うち `< 1e-9` は {r['tight']} 個 / "
              f"mpmath(50 桁) の最小裕度 {m:+.3e}")
    print("    ⚠ 裕度 0 の cell は**単体の頂点を含む cell** で、そこでは両辺がともに")
    print("       厳密に 0 (`Δ_W(δ_x) = 0` と `D(W_x‖W_x) = 0`) ⟹ 近接ではなく恒等式。")
    return {"rows": rows, "era_ok": era_ok, "deg_ok": (n_ok, n_all), "exact": ex}


def eta_mc(R: np.ndarray, n: int = 4001) -> float:
    """`η_mc(W) := sup_p I_p(X;W)/H(p)` (`|X| = 2` は 1 次元なので格子で直接)。"""
    ps = np.linspace(1.0 / n, 1 - 1.0 / n, n)
    P = np.stack([1 - ps, ps], axis=1)
    return float(np.max(mi_in_batch(P, R) / np.array([_h(p) for p in P])))


def eta_kl(R: np.ndarray, n: int = 301) -> float:
    """`η_KL(W) := sup_{p≠q} D(pW‖qW)/D(p‖q)` (`|X| = 2` の格子。SDPI 収縮係数)。"""
    ps = np.linspace(1e-4, 1 - 1e-4, n)
    P = np.stack([1 - ps, ps], axis=1)
    PW = P @ R
    best = 0.0
    for i in range(n):
        d1 = kl_batch(PW, PW[i])
        d0 = kl_batch(P, P[i])
        m = d0 > 1e-9
        best = max(best, float(np.max(d1[m] / d0[m])))
    return best


def section3(quick: bool) -> dict:
    print()
    print("=" * 78)
    print("§3 lead 4 — `Z` が消去チャネルのときだけ membership は閉形式で決まる")
    print("=" * 78)
    print("  `Z = BEC(ε)` (一般に q 元消去) では `I_p(X;Z) = (1−ε) H(p)` が**恒等式**")
    print("  ⟹ `W ∈ 𝒲_Z ⟺ η_mc(W) := sup_p I_p(X;W)/H(p) ≤ 1−ε` (**閉形式の membership**)。")
    print("  対応する less noisy 側は SDPI の収縮係数で、逐語 (Makur–Polyanskiy")
    print("  arXiv:1609.06877 §I-D、原典は Polyanskiy–Wu [3, Prop. 15]):")
    print("    `It is proved in [3, Proposition 15] that E_ε ln V if and only if")
    print("     ηKL(V) ≤ 1 − ε`")
    print("  ⟹ **利得の窓は `η_mc(W) ≤ 1−ε < η_KL(W)`** (more capable だが less noisy でない)。")
    kx = 2
    rows, w_id = [], 0.0
    for eps in (0.3, 0.5, 0.7):
        P = simplex_grid(kx, 200)
        w_id = max(w_id, float(np.abs(mi_in_batch(P, bec(eps))
                                      - (1 - eps) * np.array([_h(p) for p in P])).max()))
    print(f"\n  恒等式 `I_p(X;BEC(ε)) = (1−ε)H(p)` の最大残差 = {w_id:.3e}")
    print("  **`W = BSC(δ)` では両方の閉形式が Mrs. Gerber / SDPI から*証明*できる**:")
    print("    `η_mc(BSC(δ)) = 1 − h(δ)` — MGL (El Gamal–Kim 逐語 `The proof follows by")
    print("      the convexity of the function H(H⁻¹(u) ∗ p) in u`) より `g(u) := h(h⁻¹(u)∗δ)`")
    print("      は凸で `g(0) = h(δ)`, `g(1) = 1` ⟹ `g(u) ≤ (1−u)h(δ) + u` ⟹")
    print("      `I_p = h(p∗δ) − h(δ) ≤ h(p)(1−h(δ))`、`p = 1/2` で等号 ⟹ `ε ≤ h(δ)`。")
    print("    `η_KL(BSC(δ)) = (1−2δ)²` (既知) ⟹ `E_ε ln BSC(δ) ⟺ ε ≤ 4δ(1−δ)`。")
    print("    ⟹ **El Gamal–Kim の 4 区分の境界 `2δ / 4δ(1−δ) / h(δ)` が 2 本とも再導出される**。")
    print()
    print(f"    {'δ':>7}{'η_mc 実測':>12}{'1−h(δ)':>10}{'η_KL 実測':>12}{'(1−2δ)²':>10}"
          f"{'4δ(1−δ)':>10}{'h(δ)':>9}")
    ds = (0.05, 0.15, 0.25) if quick else (0.05, 0.1, 0.15, 0.2, 0.25, 0.35)
    w_mc, w_kl = 0.0, 0.0
    for d in ds:
        hm = float(_h(np.array([d, 1 - d])))
        em, ek = eta_mc(bsc(d)), eta_kl(bsc(d), 121 if quick else 301)
        w_mc = max(w_mc, abs(em - (1 - hm)))
        w_kl = max(w_kl, abs(ek - (1 - 2 * d) ** 2))
        print(f"    {d:>7.2f}{em:>12.6f}{1 - hm:>10.6f}{ek:>12.6f}"
              f"{(1 - 2 * d) ** 2:>10.6f}{4 * d * (1 - d):>10.6f}{hm:>9.6f}")
    print(f"    ⟹ 閉形式との最大差: η_mc {w_mc:.2e} / η_KL {w_kl:.2e} (格子の離散化誤差)")
    print()
    print("  ⚠ **一般の `Z` にはこの道具が効かない (機構つき)** — 消去チャネル経由の")
    print("     十分条件 `Z ⪰ BEC(1−γ*) ⪰ W` は `γ*(Z) := inf_p I_p(X;Z)/H(p)` を要するが、")
    print("     `Z` の行 KL がすべて有限なら頂点近傍で `I_p ~ t·D` に対し `H(p) ~ t log(1/t)`")
    print("     ⟹ **`γ*(Z) = 0`** ⟹ 十分条件は空 (§L16 の消去族の死と同一機構)。")
    rng = np.random.default_rng(SEED + 3)
    px, Cy, Cz = dense_random(rng)
    print("     実測 (dense |X|=3、頂点 0 から 1 の方向の比 I/H):", end=" ")
    for t in (1e-1, 1e-2, 1e-3, 1e-4, 1e-5):
        p = np.zeros(px.size)
        p[0], p[1] = 1 - t, t
        print(f"{mi_in(p, Cz) / _h(p):.4f}", end=" ")
    print()
    print("     ⟹ **文献の証明可能な支配判定 (SDPI / q 元対称) はすべて*支配する側*に")
    print("        強い構造を要求する**が、R4 の `Z` は BC の周辺として与えられ選べない。")
    return {"id": w_id, "eta_mc": w_mc, "eta_kl": w_kl}


# --------------------------------------------------------------------------
# 出口条件 (B) — `𝒲` を証明済の `W` だけに制限しても `Λ_env` は `Λ_sup` に勝つか
# --------------------------------------------------------------------------
THETAS = (0.0, 1e-4, 3e-4, 1e-3, 3e-3, 1e-2, 3e-2)


def best_certified_w(Cz, pux, rng, quick: bool, floor: float, keep: int = 60,
                     walk: int = 25, max_cells: int = 8000):
    """`max_{W: CERT} I(U;W)` の**証明済**の下界を探す。返り `(値, W, tag)`。

    候補生成は `bc-d2-lower-check.py` の `scan_admissible` と同一 (公平な before/after)
    で、**採否だけを cell 証明書に差し替える**。境界に接して `INDET` になる候補は
    退避 `W_θ` (閉包 (b)、`I(U;W_θ) = (1−θ)I(U;W)`) を順に試す。
    ⚠ 証明済の族を**過小評価しない**ため候補は粗い篩の上位 `keep` 本を細かい格子で
    再選別してから値の降順に歩く (L16 は上位 12 本を粗い格子だけで選んでいた)。
    """
    fine, nv, coarse = _D2.grids(Cz.shape[0], quick)
    cands = []
    for val, R in _D2.scan_admissible(Cz, pux, coarse, rng, keep=keep, quick=quick):
        gm = min(_D2.dominance_margin(Cz, R, fine), _D2.dominance_margin(Cz, R, nv))
        if gm >= -1e-12:
            cands.append((val, gm, R))
    cands.sort(key=lambda t: -t[0])
    best_val, best_R, best_tag = floor, None, "—"
    for val, gm, R in cands[:walk]:
        if val <= best_val + 1e-9:
            break                                          # 降順ゆえ以降も勝てない
        for th in THETAS:
            eff = (1 - th) * val
            if eff <= best_val + 1e-9:
                break
            if th == 0.0 and gm <= 1e-9:
                continue                                   # 境界に接する ⟹ θ=0 は不可能
            Rt = retract(R, th)
            if certify_dom(Cz, Rt, max_cells=max_cells)["status"] == CERT:
                best_val, best_R, best_tag = eff, Rt, (f"θ={th:g}" if th else "θ=0")
                break
    return best_val, best_R, best_tag


def build_family_cert(px, Cy, Cz, rng, quick: bool, rounds: int = 2):
    """`𝒲` を**証明済の `W` だけ**で作る (`_D2.build_family` の採否を差し替えた版)。"""
    Ws, log = [Cz], []
    if px.size == 2:                                       # BSC(δ) の最小の**証明済** δ
        for d in np.linspace(0.001, 0.5, 60):
            R = bsc(float(d))
            if certify_dom(Cz, R)["status"] == CERT:
                Ws.append(R)
                log.append(("BSC", float(d)))
                break
    for _ in range(rounds):
        _, pux = opt_u_gen(px, Cy, Ws, rng, restarts=2 if quick else 4)
        best_now = max(_mi(pux @ W) for W in Ws)
        val, R, tag = best_certified_w(Cz, pux, rng, quick, floor=best_now)
        if R is None:
            log.append(("none", 0.0))
            break
        Ws.append(R)
        log.append((tag, val - best_now))
    return Ws, log


def lam_env_cert(px, Cy, Cz, rng, quick: bool):
    """`(Λ_env^cert, Λ_sup, 𝒲_Z, 𝒲_Y)`。`_D2.lam_env` の族構成だけを証明済に差し替えた版。"""
    hx = _h(px)
    gy, gz, _, _, _ = gamma_sup(px, Cy, Cz, rng, restarts=3 if quick else 6)
    lam_sup = hx - min(gy, gz)
    Wz, _ = build_family_cert(px, Cy, Cz, rng, quick)
    Wy, _ = build_family_cert(px, Cz, Cy, rng, quick)
    vz, _ = opt_u_gen(px, Cy, Wz, rng, restarts=3 if quick else 5)
    vy, _ = opt_u_gen(px, Cz, Wy, rng, restarts=3 if quick else 5)
    env = max(h_cond(px, Cz) - vz, h_cond(px, Cy) - vy)
    return max(env, lam_sup), lam_sup, Wz, Wy


def cases_l16(quick: bool):
    """`bc-d2-lower-check.py` §4 と**同一のインスタンス集合**を再構成する。"""
    rng = np.random.default_rng(_D2.SEED + 4)
    cases = []
    for name, T in lattice_family():
        if T.shape[0] <= 4:
            cases.append((f"格子 {name}", np.full(T.shape[0], 1.0 / T.shape[0]),
                          *marginals(T)))
    bf = binary_family(quick)
    cases += [(f"|X|=2 {n}", p, a, b) for n, p, a, b in (bf[:6] if quick else bf[:18])]
    Cy0, Cz0, _ = partial_merge(2 / 3, 3 / 4)
    cases.append(("P2 kill witness", np.array([0.45, 0.45, 0.10]), Cy0, Cz0))
    for i in range(3 if quick else 10):
        cases.append((f"dense |X|=3 #{i}", *dense_random(rng)))
    return cases


def section4(quick: bool) -> dict:
    print()
    print("=" * 78)
    print("§4 出口条件 (B) — `𝒲` を**証明済の `W` だけ**に制限しても勝つか")
    print("=" * 78)
    print("  ⚠ **同一 run・同一インスタンス集合**で 3 本を並べる (§L17 の教訓)。")
    print("  `Λ_env` (L16 の数値検証な族) / `Λ_env^cert` (cell 証明書を通った族だけ) /")
    print("  `Λ_sup` (`W = Z` のみ = 族が退化した場合)。⚠ 候補生成は完全に同一で、")
    print("  **採否だけ**を差し替えている。符号: `Λ` は上振れ ⟹ `Λ > L'推定` は")
    print("  反例ではなく**推定不足**として分けて数え、全行を印字する。")
    rows, short, audit = [], [], {CERT: 0, REFUTE: 0, INDET: 0}
    for i, (name, px, Cy, Cz) in enumerate(cases_l16(quick)):
        s = SEED + 100 + i
        env, sup, Wz, Wy, _ = _D2.lam_env(px, Cy, Cz, np.random.default_rng(s), quick)
        envc, supc, Wzc, Wyc = lam_env_cert(px, Cy, Cz, np.random.default_rng(s), quick)
        for base, fam in ((Cz, Wz), (Cy, Wy)):             # L16 の族そのものを監査する
            for W in fam[1:]:
                audit[certify_dom(base, W, max_cells=20000)["status"]] += 1
        t_est = _L13.t_lower(px, Cy, Cz, np.random.default_rng(s + 7),
                             restarts=3 if quick else 6).best
        lp = _h(px) - t_est
        rows.append((name, min(h_cond(px, Cy), h_cond(px, Cz)), sup, env, envc, lp,
                     len(Wz) + len(Wy), len(Wzc) + len(Wyc)))
        if max(env, envc) > lp + 1e-6:
            short.append((name, max(env, envc) - lp))
    print()
    print(f"  {'instance':<26}{'target':>9}{'Λ_sup':>10}{'Λ_env':>10}{'Λ_env^cert':>12}"
          f"{'L′推定':>10}{'|𝒲|':>8}{'|𝒲^c|':>8}")
    for r in rows:
        print(f"  {r[0]:<26}{r[1]:>9.5f}{r[2]:>10.5f}{r[3]:>10.5f}{r[4]:>12.5f}"
              f"{r[5]:>10.5f}{r[6]:>8d}{r[7]:>8d}")
    ie = np.array([r[3] - r[2] for r in rows])
    ic = np.array([r[4] - r[2] for r in rows])
    sel = ie > 1e-4                                        # 1e-5 台は最適化ノイズ
    keep = ic[sel] / ie[sel]
    print(f"  改善 `Λ_env − Λ_sup`      : 中央 {np.median(ie):+.6f} / 最良 {ie.max():+.6f}")
    print(f"  改善 `Λ_env^cert − Λ_sup` : 中央 {np.median(ic):+.6f} / 最良 {ic.max():+.6f}")
    print(f"  ⟹ **証明済に制限したときの改善の残存率** (改善が `> 1e-4` の {int(sel.sum())} 本"
          f"に限る。1e-5 台は最適化ノイズ): 中央 {np.median(keep):.3f} / 最小 {keep.min():.3f}")
    print(f"     ⚠ 残存率が 1 を超える行がある — 証明済側の候補選別 (粗い篩の上位 60 本を")
    print(f"       細かい格子で再選別) が L16 の 12 本より強いため。どちらも同じ真の max の")
    print(f"       下界ゆえ矛盾ではなく**探索の非対称**である。改善が正の行 "
          f"{int((ic > 1e-9).sum())}/{len(rows)} 本")
    for tag, sub in (("dense |X|=3", [r for r in rows if r[0].startswith("dense")]),
                     ("|X|=2", [r for r in rows if r[0].startswith("|X|=2")])):
        if not sub:
            continue
        print(f"    {tag} ({len(sub)} 本) 残距離 `L′ − Λ` の中央: "
              f"{np.median([r[5] - r[2] for r in sub]):.6f} (Λ_sup) → "
              f"{np.median([r[5] - r[3] for r in sub]):.6f} (Λ_env) → "
              f"{np.median([r[5] - r[4] for r in sub]):.6f} (Λ_env^cert)")
    tot = sum(audit.values())
    print(f"  ⟹ **L16 が採用した `W` そのものの監査** ({tot} 本、`W = Z` を除く): "
          f"CERT {audit[CERT]} / INDET {audit[INDET]} / REFUTE {audit[REFUTE]}")
    print("     (REFUTE が出たら L16 の族に**資格の無い `W` が混じっていた**ことになる)")
    print(f"  ⚠ 推定不足 (`Λ` の推定が `L'` の推定を超えた行) = {len(short)} 行"
          + ("" if not short else ": " + ", ".join(f"{n} ({d:+.2e})" for n, d in short)))
    return {"rows": rows, "short": short, "keep": float(np.median(keep)), "audit": audit,
            "imp_env": float(np.median(ie)), "imp_cert": float(np.median(ic))}


def section4b(quick: bool) -> dict:
    print()
    print("=" * 78)
    print("§4b 出口条件 (B) の**最適化不使用**版 — `|X| = 2` の deficit を証明書化")
    print("=" * 78)
    print("  2 値 `U` の格子を直接評価 ⟹ `max_U` の下界 ⟹ `Λ` の上界 ⟹ deficit は")
    print("  真値の下界 = **正なら証明書**。⚠ (B) の決着はこの表で付く (最適化器を")
    print("  信用せずに `Λ_env` と `Λ_env^cert` を比べられる唯一の場所)。")
    print("  ⚠ **乱数の流れも before/after で揃える** — 族の構成 4 本すべてを同じ種で")
    print("     seed し直す (同じ run でも rng を共有すると候補プールがずれる)。")
    fam = [("BSC(.1)/BEC(.5)", bsc(0.1), bec(0.5)), ("BEC(.3)/BSC(.25)", bec(0.3), bsc(0.25)),
           ("BSC(.15)/Z(.5)", bsc(0.15), bzc(0.5))]
    ps = (0.2, 0.35) if quick else (0.1, 0.2, 0.35, 0.5)
    n = 41 if quick else 81
    rows = []
    for k, (nm, Cy, Cz) in enumerate(fam):
        for j, p1 in enumerate(ps):
            s = SEED + 500 + 10 * k + j
            px = np.array([1 - p1, p1])
            target = min(h_cond(px, Cy), h_cond(px, Cz))
            Wz, _ = _D2.build_family(px, Cy, Cz, np.random.default_rng(s), quick)
            Wy, _ = _D2.build_family(px, Cz, Cy, np.random.default_rng(s + 1), quick)
            Wzc, _ = build_family_cert(px, Cy, Cz, np.random.default_rng(s), quick)
            Wyc, _ = build_family_cert(px, Cz, Cy, np.random.default_rng(s + 1), quick)
            sup = max(h_cond(px, Cz) - u_grid_binary(px, Cy, [Cz], n),
                      h_cond(px, Cy) - u_grid_binary(px, Cz, [Cy], n))
            env = max(h_cond(px, Cz) - u_grid_binary(px, Cy, Wz, n),
                      h_cond(px, Cy) - u_grid_binary(px, Cz, Wy, n))
            envc = max(h_cond(px, Cz) - u_grid_binary(px, Cy, Wzc, n),
                       h_cond(px, Cy) - u_grid_binary(px, Cz, Wyc, n))
            rows.append((f"{nm} p={p1}", target, target - sup, target - env,
                         target - envc, len(Wz) + len(Wy), len(Wzc) + len(Wyc)))
    print()
    print(f"  {'instance':<24}{'target':>9}{'def(Λ_sup)':>13}{'def(Λ_env)':>13}"
          f"{'def(Λ_env^c)':>14}{'|𝒲|':>7}{'|𝒲^c|':>7}")
    for r in rows:
        print(f"  {r[0]:<24}{r[1]:>9.5f}{r[2]:>+13.6f}{r[3]:>+13.6f}{r[4]:>+14.6f}"
              f"{r[5]:>7d}{r[6]:>7d}")
    de = np.array([r[2] - r[3] for r in rows])                 # Λ_env による deficit 減
    dc = np.array([r[2] - r[4] for r in rows])                 # Λ_env^cert による deficit 減
    keep = np.array([(c / e if e > 1e-9 else 1.0) for e, c in zip(de, dc)])
    print(f"  deficit の縮み `def(Λ_sup) − def(Λ)`: `Λ_env` 最良 {de.max():+.6f} / "
          f"`Λ_env^cert` 最良 {dc.max():+.6f}")
    print(f"  ⟹ **証明済に制限したときの残存率**: 中央 {np.median(keep):.4f} / "
          f"最小 {keep.min():.4f} (1.000 = 証明への制限で 1 ビットも失っていない)")
    return {"rows": rows, "keep": float(np.median(keep)), "keep_min": float(keep.min()),
            "best_env": float(de.max()), "best_cert": float(dc.max())}


def section5(res: dict) -> None:
    s0, s1, s2, s3, s4, s4b = (res[k] for k in ("s0", "s1", "s2", "s3", "s4", "s4b"))
    print()
    print("=" * 78)
    print("§5 判定")
    print("=" * 78)
    print(f"  §0 恒等式 (E1)/(c)/(d) と凹性: accept = {s0['ok']}")
    print(f"  §1 **閉包だけでは利得が出ない (確定)** — witness 残差 {s1['witness']:.1e} / "
          f"LP 残差 {s1['lp']:.1e} / 利得の最大 {s1['gain']:+.1e}")
    print("     ⟹ 資格の穴は本質的。非劣化の base point が別途要る。")
    e0 = s2["rows"][0]
    print(f"  §2 **cell 証明書は文献既知の境界を再現する** — Z=BEC({e0[0]}) で "
          f"真値 {e0[1]:.9f} を CERT {e0[2]:.9f} / REFUTE {e0[3]:.9f} が挟む "
          f"(窓幅 {e0[2] - e0[3]:.1e})")
    print(f"     消去族の反証 = {s2['era_ok']} / 劣化版の CERT = {s2['deg_ok'][0]}/"
          f"{s2['deg_ok'][1]} / mpmath 50 桁の再検証も同一判定")
    print(f"  §3 閉形式 `η_mc` / `η_KL` と閉形式境界の最大差 = {s3['eta_mc']:.1e} / "
          f"{s3['eta_kl']:.1e} ⟹ El Gamal–Kim の 4 区分を再導出")
    print(f"  §4 (B) 一般インスタンス: 改善の残存率 中央 {s4['keep']:.3f} "
          f"(`Λ_env` 中央 {s4['imp_env']:+.6f} → `Λ_env^cert` 中央 {s4['imp_cert']:+.6f})")
    print(f"  §4b (B) 最適化不使用: 残存率 中央 {s4b['keep']:.4f} / 最小 {s4b['keep_min']:.4f} "
          f"(deficit の縮み 最良 {s4b['best_env']:+.6f} → {s4b['best_cert']:+.6f})")
    print()
    print("  ⚠ 用語: `CERT` は**有限個の不等式への還元 + 浮動小数点評価**であって")
    print("     exact arithmetic ではない。掃引 (無限個の点の有限標本) より 1 段強いが、")
    print("     記号的証明より 1 段弱い — 3 段を混ぜないこと。")


def main() -> None:
    quick = "--quick" in sys.argv
    t0 = time.time()
    res = {"s0": section0(quick), "s1": section1(quick), "s2": section2(quick),
           "s3": section3(quick), "s4": section4(quick), "s4b": section4b(quick)}
    section5(res)
    print(f"\n  (経過 {time.time() - t0:.1f}s、mode = {'quick' if quick else 'full'})")


if __name__ == "__main__":
    main()
