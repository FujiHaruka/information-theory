"""候補経路 R1 ([`bc-open-problem-routes.md`](bc-open-problem-routes.md)) が本文で引いている
記号的・数値的な検算を再現するスクリプト。

このスクリプトが確認するもの (docs 側の対応箇所)
------------------------------------------------
  §1  記号的検算 (16 項目)          -> routes.md「検算」節、step 2 / 3 / 4 の根拠列
  §2  線形計画双対                  -> routes.md step 1 の根拠列
  §3  `sigma = 1` のタイトさの述語   -> routes.md step 6 の根拠列、「殺され方」の 1.
  §4  step 6 の部分証明の検定        -> routes.md step 6 の根拠列「討ち取った半分」

実行: `python3 docs/shannon/bc-route-r1-check.py` (既定 20s 程度 / `--quick` 数秒)。
乱数種は固定 (SEED)。**§2 / §3 / §4 の報告値は再実行で一致する** — 局所最適化を一切
使っておらず (§2 は HiGHS の厳密解、§3 / §4 は閉形式と厳密な同時分布の評価)、着地値が
実行ごとに動く量が無いため。

R1 が確認していないもの (射程の限定 — 過大評価の防止)
------------------------------------------------------
**本スクリプトはチャネルを最適化しない**。§2 / §3 が振っているのは
`(A1, A2, S1, S2)` という **四辺形の形そのもの**であって、実在の DM-BC から `p(u,v,w,x)` を
最適化して得られる形ではない。抽出される必要条件 (下記) だけを課した**上位集合**を掃いている
ので、「`sigma = 1` が緩む割合」は**実在チャネルの最大化点で緩む頻度の上界ですらない**
(最大化点は一般の形ではない)。step 6 の本判定 = 実チャネル上で最大化点の述語を見る probe は
**L8 の P2** であって本スクリプトの守備範囲ではない。§3 が確定させるのは
「タイトさが形の性質として自動ではない」ことと「タイトさの述語が何か」の 2 点だけ。

対象の逐語定義
--------------
3 補助変数 Marton 内界 `M(T)` (私信のみ) の 4 制約。出典は Jog-Nair, arXiv:0901.1492 の
Bound 1 (逐語は [`bc-facts.md`](bc-facts.md) F2 行)。`Y1 = Y`, `Y2 = Z` と読み替えている:

    A1 = I(U,W;Y)                                  R1 <= A1
    A2 = I(V,W;Z)                                  R2 <= A2
    S1 = I(U,W;Y) + I(V;Z|W) - I(U;V|W)            R1+R2 <= S1
    S2 = I(V,W;Z) + I(U;Y|W) - I(U;V|W)            R1+R2 <= S2

双対汎関数 `F(T,{a_x})` の逐語定義は [`bc-facts.md`](bc-facts.md) V7 行
(第 2 項が `(lambda - alpha)` である訂正は同 L1 (b) 行 (4))。本スクリプトでは `F` の内部
パラメータ `lambda` を **`mu`** と書く (領域側の方向および外部ノート `lambda-SRM` の
`lambda` と 3 つ巴で衝突するため。routes.md 記法節と同じ規約)。

    F(T,{a_x}) = max over p(u,v,x) of
                   [ -alpha*H(Y) - (mu-alpha)*H(Z) + I(U;Y) + mu*I(V;Z) - I(U;V)
                     + sum_x p(x) a_x ]

`(A1,A2,S1,S2)` から代数的に従う必要条件 (§1 が記号的に証明する)
---------------------------------------------------------------
    S1 - A1     = I(V;Z|W) - I(U;V|W)          (符号は自由)
    S2 - A2     = I(U;Y|W) - I(U;V|W)          (符号は自由)
    A1 + A2 - S1 = I(W;Z) + I(U;V|W) >= 0      ==> S1 <= A1 + A2
    A1 + A2 - S2 = I(W;Y) + I(U;V|W) >= 0      ==> S2 <= A1 + A2
    S1 - A2     = I(W;Y) - I(W;Z) + I(U;Y|W) - I(U;V|W)   (step 6 の残余条件)

§2 / §3 はこの必要条件だけを課して `(A1,A2,S1,S2)` を乱択する。

基盤
----
記号計算は [`bc_probe.py`](bc_probe.py) の `parse` / `prove_identity` をそのまま import して
使う (再実装しない)。`prove_identity` が真を返すのは残差の全係数が相殺したときで、これは
**任意の有限同時分布に対する証明**であって標本証拠ではない (親 plan §2.1)。
§4 の同時分布評価も `bc_probe.Joint` をそのまま使う。
"""

import argparse
import sys
import time
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from bc_probe import Joint, prove_identity  # noqa: E402

SEED = 20260802

# M(T) の 4 制約 (上の逐語定義)
A1 = "I(U,W;Y)"
A2 = "I(V,W;Z)"
S1 = "I(U,W;Y) + I(V;Z|W) - I(U;V|W)"
S2 = "I(V,W;Z) + I(U;Y|W) - I(U;V|W)"

TOL = 1e-9


# ---------------------------------------------------------------------------
# §1 記号的検算 — routes.md「検算」節 / step 2, 3, 4 の根拠
# ---------------------------------------------------------------------------

def section1_symbolic() -> tuple[bool, int, int]:
    print("=== §1 記号的検算 (係数相殺 = 証明。掃引ではない) ===")
    checks: list[tuple[str, str, str]] = []

    # (a) 四辺形の形について従う関係 (docstring の必要条件、および step 6 の残余条件)
    checks += [
        ("S1 - A1 = I(V;Z|W) - I(U;V|W)",
         f"({S1}) - ({A1})", "I(V;Z|W) - I(U;V|W)"),
        ("S2 - A2 = I(U;Y|W) - I(U;V|W)",
         f"({S2}) - ({A2})", "I(U;Y|W) - I(U;V|W)"),
        ("A1 + A2 - S1 = I(W;Z) + I(U;V|W)   (=> S1 <= A1+A2)",
         f"({A1}) + ({A2}) - ({S1})", "I(W;Z) + I(U;V|W)"),
        ("A1 + A2 - S2 = I(W;Y) + I(U;V|W)   (=> S2 <= A1+A2)",
         f"({A1}) + ({A2}) - ({S2})", "I(W;Y) + I(U;V|W)"),
        ("S1 - A2 = I(W;Y)-I(W;Z) + I(U;Y|W)-I(U;V|W)   (step 6 の残余条件)",
         f"({S1}) - ({A2})", "I(W;Y) - I(W;Z) + I(U;Y|W) - I(U;V|W)"),
    ]

    # (b) step 2 — sigma=1 に固定し (s1,s2)=(alpha,1-alpha) と分割した LP 双対値が
    #     F の被積分量 (W 付きの形) そのものであること。
    #     両辺は (alpha, mu) についてアフィンなので、アフィン独立な有理点で恒等が従う。
    F = Fraction
    pts = [(F(0), F(1)), (F(1), F(1)), (F(0), F(2)), (F(1, 4), F(3)), (F(1, 2), F(7, 2))]
    for al, mu in pts:
        checks.append((
            f"step 2: LP-dual(sigma=1) == F-form-with-W   [alpha={al}, mu={mu}]",
            f"({mu}-1)*({A2}) + {al}*({S1}) + (1-{al})*({S2})",
            f"{al}*I(W;Y) + ({mu}-{al})*I(W;Z)"
            f" + I(U;Y|W) + {mu}*I(V;Z|W) - I(U;V|W)",
        ))

    # (c) step 3 — I(W;.) = H(.) - H(.|W) で W を剥がす段 (上凹包に渡る形)
    for al, mu in [(F(1, 4), F(3)), (F(1, 2), F(7, 2))]:
        checks.append((
            f"step 3: W-decomposition (上凹包の段)          [alpha={al}, mu={mu}]",
            f"{al}*I(W;Y) + ({mu}-{al})*I(W;Z)"
            f" + I(U;Y|W) + {mu}*I(V;Z|W) - I(U;V|W)",
            f"{al}*H(Y) + ({mu}-{al})*H(Z)"
            f" + ( -{al}*H(Y|W) - ({mu}-{al})*H(Z|W)"
            f"     + I(U;Y|W) + {mu}*I(V;Z|W) - I(U;V|W) )",
        ))

    # (d) step 4 — F の被最大化量 G の展開。routes.md の骨格の形と
    #     bc-facts.md L1 (b) 行 (5)(b) の機械確認済の形の両方に一致すること。
    #     (線形項 sum_x p(x) a_x は情報量式ではないので両辺から落としてある)
    for al, mu in [(F(1, 4), F(3)), (F(1, 2), F(7, 2))]:
        g = f"-{al}*H(Y) - ({mu}-{al})*H(Z) + I(U;Y) + {mu}*I(V;Z) - I(U;V)"
        checks.append((
            f"step 4: G == routes.md の展開形                [alpha={al}, mu={mu}]",
            g, f"(1-{al})*H(Y) + {al}*H(Z) - H(Y|U) - {mu}*H(Z|V) - I(U;V)"))
        checks.append((
            f"step 4: G == bc-facts.md L1(b) の展開形        [alpha={al}, mu={mu}]",
            g, f"(1-{al})*H(Y) + {al}*H(Z) + ({mu}-1)*H(V)"
               f" - H(U,Y) - {mu}*H(V,Z) + H(U,V)"))

    n_ok = 0
    for name, lhs, rhs in checks:
        ok, residual = prove_identity(lhs, rhs)
        n_ok += ok
        print(f"  {'PASS' if ok else 'FAIL'}  {name}")
        if not ok:
            print(f"        residual: {residual}")
    ok_all = n_ok == len(checks)
    print(f"  §1: {'PASS' if ok_all else 'FAIL'} — {n_ok}/{len(checks)} 項目")
    return ok_all, n_ok, len(checks)


# ---------------------------------------------------------------------------
# 四辺形の primal / dual (§2, §3 の共通部品)
# ---------------------------------------------------------------------------

def primal_linprog(a1: float, a2: float, s: float, mu: float) -> float:
    """max R1 + mu*R2 s.t. R1<=a1, R2<=a2, R1+R2<=s, R>=0 を HiGHS で厳密に解く。"""
    res = linprog(c=[-1.0, -mu], A_ub=[[1.0, 0.0], [0.0, 1.0], [1.0, 1.0]],
                  b_ub=[a1, a2, s], bounds=[(0, None), (0, None)], method="highs")
    assert res.status == 0, res.message
    return -res.fun


def primal_closed(a1: float, a2: float, s: float, mu: float) -> float:
    """同じ値の閉形式 (mu >= 1 なので R2 を優先)。§2 の独立コード経路。"""
    s = max(s, 0.0)
    r2 = min(a2, s)
    r1 = min(a1, s - r2)
    return r1 + mu * r2


def phi(sigma: float, a1: float, a2: float, s: float, mu: float) -> float:
    """LP 双対 (routes.md step 1): (1-sigma)^+ A1 + (mu-sigma)^+ A2 + sigma*min(S1,S2)。"""
    return max(0.0, 1.0 - sigma) * a1 + max(0.0, mu - sigma) * a2 + sigma * s


def draw_shapes(rng, n: int):
    """docstring の必要条件だけを課した (A1,A2,S1,S2,mu) の乱択。

    実在チャネルから得られる形の**上位集合**であることに注意 (冒頭「射程の限定」)。
    """
    out = []
    while len(out) < n:
        a1, a2 = rng.uniform(0.05, 2.0, 2)
        mu = rng.uniform(1.0, 4.0)
        s1 = a1 + rng.uniform(-a1 - a2, a2)   # S1 <= A1+A2
        s2 = a2 + rng.uniform(-a1 - a2, a1)   # S2 <= A1+A2
        if min(s1, s2) < 0.0:                 # 四辺形が空になる形は除く
            continue
        out.append((a1, a2, s1, s2, mu))
    return out


# ---------------------------------------------------------------------------
# §2 線形計画双対 — routes.md step 1 の根拠
# ---------------------------------------------------------------------------

def dual_exact(a1: float, a2: float, s: float, mu: float) -> float:
    """min over sigma in [0, mu] of phi(sigma) を厳密に取る。

    `phi` は sigma について**区分線形**で、折れ点は `(1-sigma)^+` と `(mu-sigma)^+` が
    傾きを変える `sigma = 1` と `sigma = mu` の 2 つだけ。したがって最小は端点と折れ点
    `{0, 1, mu}` のいずれかで達成される (グリッド掃引は不要で、そもそも誤差が乗る)。
    """
    return min(phi(x, a1, a2, s, mu) for x in (0.0, 1.0, mu))


def section2_lp_duality(n: int, n_sigma: int) -> bool:
    print("\n=== §2 step 1: 四辺形の support function = min over sigma of phi(sigma) ===")
    rng = np.random.default_rng(SEED)
    shapes = draw_shapes(rng, n)
    bad_dual = bad_weak = bad_closed = bad_grid = 0
    worst_dual = worst_closed = worst_grid = 0.0
    for a1, a2, s1, s2, mu in shapes:
        s = min(s1, s2)
        p_lp = primal_linprog(a1, a2, s, mu)
        p_cf = primal_closed(a1, a2, s, mu)
        d = dual_exact(a1, a2, s, mu)
        g = min(phi(x, a1, a2, s, mu) for x in np.linspace(0.0, mu, n_sigma))
        # 肯定コントロール 1: 弱双対性 — 全 sigma >= 0 で phi(sigma) >= primal
        if g < p_lp - 1e-9:
            bad_weak += 1
        # 肯定コントロール 2: 閉形式 primal と HiGHS が一致 (独立コード経路)
        if abs(p_lp - p_cf) > 1e-9:
            bad_closed += 1
            worst_closed = max(worst_closed, abs(p_lp - p_cf))
        # 肯定コントロール 3: グリッド掃引が折れ点評価を下回らない
        # (下回れば折れ点の集合 {0,1,mu} が不完全だったことになる)
        if g < d - 1e-12:
            bad_grid += 1
        worst_grid = max(worst_grid, g - d)
        # 本判定: min over sigma の双対値が primal に一致
        if abs(p_lp - d) > 1e-9:
            bad_dual += 1
            worst_dual = max(worst_dual, abs(p_lp - d))
    print(f"  control: 弱双対性 phi(sigma) >= primal の違反   = {bad_weak}/{n}")
    print(f"  control: 閉形式 primal vs HiGHS の不一致         = {bad_closed}/{n}"
          f" (最大 {worst_closed:.3e})")
    print(f"  control: 折れ点 {{0,1,mu}} を下回るグリッド点     = {bad_grid}/{n}"
          f" (グリッド {n_sigma} 点の超過は最大 {worst_grid:.3e} = 掃引の解像度)")
    print(f"  判定:    min_sigma phi == primal の不一致        = {bad_dual}/{n}"
          f" (最大 {worst_dual:.3e})")
    ok = bad_dual == 0 and bad_weak == 0 and bad_closed == 0 and bad_grid == 0
    print(f"  §2: {'PASS' if ok else 'FAIL'}")
    return ok


# ---------------------------------------------------------------------------
# §3 `sigma = 1` (= F) のタイトさ — routes.md step 6 の根拠 / 「殺され方」1.
# ---------------------------------------------------------------------------

def section3_tightness(n: int) -> bool:
    print("\n=== §3 step 6: F が対応する sigma=1 スライスはいつタイトか ===")
    rng = np.random.default_rng(SEED + 1)
    shapes = draw_shapes(rng, n)
    n_loose = mis = 0
    worst_gap = 0.0
    for a1, a2, s1, s2, mu in shapes:
        s = min(s1, s2)
        p = primal_linprog(a1, a2, s, mu)
        gap = phi(1.0, a1, a2, s, mu) - p
        tight = gap <= 1e-6
        if not tight:
            n_loose += 1
            worst_gap = max(worst_gap, gap)
        # 本判定: タイトさの述語が「min(S1,S2) >= A2」と一致するか
        if tight != (s >= a2 - 1e-9):
            mis += 1
    print(f"  判定:    述語 (sigma=1 がタイト) <=> (min(S1,S2) >= A2) の不一致"
          f" = {mis}/{n}")
    print(f"  観測:    sigma=1 が真に緩い形 = {n_loose}/{n}"
          f" (最大ギャップ {worst_gap:.4f})")
    print("  ⚠ この割合は**抽象的な四辺形の形**についてのもので、実在チャネルの最大化点で")
    print("     緩む頻度ではない (冒頭「射程の限定」)。実チャネル上の判定は L8 の P2。")
    ok = mis == 0
    print(f"  §3: {'PASS' if ok else 'FAIL'} — タイトさが形の性質として自動でないこと"
          f" (n_loose > 0) と、述語の同定 (mis == 0) の 2 点")
    return ok and n_loose > 0


# ---------------------------------------------------------------------------
# §4 step 6 の部分証明 — routes.md step 6「討ち取った半分」
# ---------------------------------------------------------------------------

def _joint(rng, cU, cV, cW, cX, cY, cZ) -> np.ndarray:
    """(U,V,W) -> X -> (Y,Z) の Markov 連鎖を持つ同時分布を引く。

    一般 BC は Y ⊥ Z | X を仮定できないので (Y,Z) は結合 1 カーネルから引く
    (親 plan §2.1 の落とし穴)。
    """
    puvw = rng.dirichlet(np.full(cU * cV * cW, 0.7)).reshape(cU, cV, cW)
    kx = rng.dirichlet(np.full(cX, 0.5), size=(cU, cV, cW))
    kyz = rng.dirichlet(np.full(cY * cZ, 0.5), size=cX).reshape(cX, cY, cZ)
    p = puvw[:, :, :, None] * kx                       # (U,V,W,X)
    return p[:, :, :, :, None, None] * kyz[None, None, None, :, :, :]


def section4_partial_proof(n: int) -> bool:
    print("\n=== §4 step 6 の部分証明: 最大化点では必ず S2 >= A2 ===")
    print("  主張: I(U;Y|W) < I(U;V|W) なら U を定数にすると sigma=1 の目的値が**真に増える**")
    print("        (A2 は不変・min(S1,S2) は増大) ⟹ 最大化点では S2 - A2 >= 0")
    rng = np.random.default_rng(SEED + 2)
    names = ["U", "V", "W", "X", "Y", "Z"]
    n_hit = bad_claim = bad_a2 = bad_zero = 0
    worst_a2 = 0.0
    min_increase = np.inf
    for _ in range(n):
        cU, cV, cW = rng.integers(2, 4, 3)
        cX, cY, cZ = rng.integers(2, 4, 3)
        p = _joint(rng, cU, cV, cW, cX, cY, cZ)
        mu = float(rng.uniform(1.0, 4.0))
        J = Joint(names, p)
        # U を定数にする摂動: U を周辺化して 1 点にする ((V,W,X,Y,Z) の法則は不変)
        Jc = Joint(names, p.sum(axis=0)[None, ...])

        def quad(j):
            a1, a2 = j.eval(A1), j.eval(A2)
            return a1, a2, j.eval(S1), j.eval(S2)

        a1, a2, s1, s2 = quad(J)
        a1c, a2c, s1c, s2c = quad(Jc)
        # control: 摂動は A2 = I(V,W;Z) を厳密に保つ
        if abs(a2 - a2c) > 1e-12:
            bad_a2 += 1
            worst_a2 = max(worst_a2, abs(a2 - a2c))
        # control: 摂動後は I(U;Y|W) = I(U;V|W) = 0 (ゆえに S2c - A2c = 0)
        if abs(s2c - a2c) > 1e-12:
            bad_zero += 1
        if J.eval("I(U;Y|W)") < J.eval("I(U;V|W)") - 1e-12:
            n_hit += 1
            old = (mu - 1.0) * a2 + min(s1, s2)
            new = (mu - 1.0) * a2c + min(s1c, s2c)
            if new <= old + 1e-12:
                bad_claim += 1
            else:
                min_increase = min(min_increase, new - old)
    print(f"  control: 摂動が A2 を保つ — 違反 {bad_a2}/{n} (最大 {worst_a2:.2e})")
    print(f"  control: 摂動後に S2 - A2 = 0 — 違反 {bad_zero}/{n}")
    print(f"  判定:    I(U;Y|W) < I(U;V|W) だった標本 {n_hit}/{n} のうち、"
          f"目的値が増えなかったもの = {bad_claim}")
    if n_hit:
        print(f"           増分の最小値 = {min_increase:+.3e}")
    ok = bad_claim == 0 and bad_a2 == 0 and bad_zero == 0 and n_hit > 0
    print(f"  §4: {'PASS' if ok else 'FAIL'}")
    return ok


# ---------------------------------------------------------------------------

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    n_lp, n_tight, n_joint, n_sigma = (400, 200, 120, 801) if args.quick \
        else (4000, 2000, 800, 4001)

    t0 = time.time()
    ok1, n_ok, n_tot = section1_symbolic()
    ok2 = section2_lp_duality(n_lp, n_sigma)
    ok3 = section3_tightness(n_tight)
    ok4 = section4_partial_proof(n_joint)

    print("\n=== 判定 ===")
    print(f"  §1 記号的検算 ({n_ok}/{n_tot} 項目)                 : "
          f"{'PASS' if ok1 else 'FAIL'}")
    print(f"  §2 線形計画双対 (step 1)                        : "
          f"{'PASS' if ok2 else 'FAIL'}")
    print(f"  §3 sigma=1 のタイトさの述語 (step 6)             : "
          f"{'PASS' if ok3 else 'FAIL'}")
    print(f"  §4 step 6 の部分証明 (S2 >= A2)                 : "
          f"{'PASS' if ok4 else 'FAIL'}")
    if not (ok1 and ok2 and ok3 and ok4):
        print("  !! FAIL がある。routes.md 側の根拠列を実測に合わせて直すこと")
        print("     (スクリプトを docs の数値に合わせにいかない)。")
    print("\n  ⚠ 本スクリプトは R1 の**主張そのもの**を probe していない。"
          "R1 は `unprobed` のまま")
    print("     (親 plan §3.1 の条件 4 / 5 は L8 の仕事)。")
    print(f"\n合計実行時間 {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
