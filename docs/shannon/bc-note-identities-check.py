"""外部ノート (自己テンソル化) の定理2 — 恒等式 (7) / (5) と数値例 V1–V3 の判定。

対象
----
`docs/shannon/bc-external-note-tensorization.md` §1「定理2 — 通常の single-letterization を
壊す正確な残差」。ノートの記述を**逐語で**転記して叩く (修理した版ではなく、ノートが
書いたとおりの主張を検定する)。

  Φ = I(A;Y₁,Y₂) + I(B;Z₁,Z₂)

  Ψ = I(A;Y₁|Z₂) + I(B;Z₁|Z₂) − I(A;B|Z₂)
    + I(A;Y₂|Y₁) + I(B;Z₂|Y₁) − I(A;B|Y₁)

  (4) Y₁ ⊥ Z₂ | (A,B)                          … メモリレス性の帰結だとノートが言う
  (5) Φ = Ψ + I(Y₁;Z₂) + I(A;B | Y₁,Z₂)        … 設定下で「厳密に」成り立つとノートが言う
  (6) Φ − Ψ = I(A;Y₁) − I(A;Y₁|Z₂) + I(B;Z₂) − I(B;Z₂|Y₁) + I(A;B|Z₂) + I(A;B|Y₁)
  (7) I(A;Y) − I(A;Y|Z) + I(B;Z) − I(B;Z|Y) + I(A;B|Z) + I(A;B|Y)
      = I(Y;Z) + I(A;B|Y,Z) + I(A;B) − I(Y;Z|A,B)     … 「一般に任意の A,B,Y,Z について」

判定項目 (親 plan §7 の L1)
---------------------------
  V1  (7) が一般に成り立つか        — 記号展開 (係数相殺) + 無制約ランダム分布の掃引
  V2  (5) と、その (4) の使い方     — 記号展開 + 構造制約つきランダム分布の掃引
                                       + メモリレス性を壊した負のコントロール
  V3  数値例 `X₁ = A ∧ B` の値       — 逐語再計算 (bit) + BSC_ε 摂動の実測

実行方法
--------
  python3 docs/shannon/bc-note-identities-check.py      # numpy と scipy が要る (1 分未満)

Lean の def との対応
--------------------
**依存しない**。ここで扱うのは有限アルファベット上の情報量の一般恒等式だけで、
InformationTheory 側の `def` (Marton 領域 / 容量領域 / BC 符号) は一切登場しない。
したがって CLAUDE.md の「sim を実 def と逐語照合してから FALSE を信用する」の照合対象は
entropy の規約のみで、それは harness (`bc_probe.py`) が `Shannon/Bridge.lean:40` の
自然対数版と一致させている。ノートの数値例は bit で書かれているので V3 だけ bit で出す。
"""

import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bc_probe import (  # noqa: E402
    BayesNet,
    Joint,
    prove_identity,
    random_joint,
    test_relation,
)

rng = np.random.default_rng(20260801)

# ノートの式を逐語転記したもの (下付きは ASCII 化のみ)
PHI = "I(A;Y1,Y2) + I(B;Z1,Z2)"
PSI = (
    "I(A;Y1|Z2) + I(B;Z1|Z2) - I(A;B|Z2)"
    " + I(A;Y2|Y1) + I(B;Z2|Y1) - I(A;B|Y1)"
)
EQ7_LHS = "I(A;Y) - I(A;Y|Z) + I(B;Z) - I(B;Z|Y) + I(A;B|Z) + I(A;B|Y)"
EQ7_RHS = "I(Y;Z) + I(A;B|Y,Z) + I(A;B) - I(Y;Z|A,B)"
EQ6_RHS = (
    "I(A;Y1) - I(A;Y1|Z2) + I(B;Z2) - I(B;Z2|Y1) + I(A;B|Z2) + I(A;B|Y1)"
)
EQ5_RHS = f"({PSI}) + I(Y1;Z2) + I(A;B|Y1,Z2)"


def rule(title: str) -> None:
    print("\n" + "=" * 78)
    print(title)
    print("=" * 78)


# --------------------------------------------------------------------------
# V1 — 恒等式 (7)
# --------------------------------------------------------------------------
def v1() -> None:
    rule("V1 — 恒等式 (7) は一般の (A,B,Y,Z) で成り立つか")

    proved, residual = prove_identity(EQ7_LHS, EQ7_RHS)
    print("  [記号展開] 両辺を同時エントロピーの線形結合へ展開した残差:")
    print(f"    {residual!r}")
    print(f"    -> 係数が全部相殺したか: {proved}")
    print("  参考 — 両辺の展開形 (同一のはず):")
    from bc_probe import parse

    print(f"    LHS = {parse(EQ7_LHS)!r}")
    print(f"    RHS = {parse(EQ7_RHS)!r}")

    print("\n  [ランダム掃引] 構造制約なしの同時分布 (Dirichlet)。")
    configs = [
        ({"A": 2, "B": 2, "Y": 2, "Z": 2}, 1.0, 0.0, 20000),
        ({"A": 3, "B": 2, "Y": 4, "Z": 3}, 1.0, 0.0, 20000),
        ({"A": 4, "B": 4, "Y": 4, "Z": 4}, 1.0, 0.0, 10000),
        # 尖った分布 / 台に穴 — 退化境界を踏ませる
        ({"A": 3, "B": 3, "Y": 3, "Z": 3}, 0.05, 0.0, 20000),
        ({"A": 3, "B": 3, "Y": 3, "Z": 3}, 1.0, 0.6, 20000),
        ({"A": 2, "B": 5, "Y": 2, "Z": 5}, 0.2, 0.4, 20000),
    ]
    total, viol, worst = 0, 0, 0.0
    for cards, dc, zp, n in configs:
        rep = test_relation(
            EQ7_LHS, EQ7_RHS,
            lambda c=cards, d=dc, z=zp: random_joint(c, rng, dirichlet=d, zero_prob=z),
            trials=n, tol=1e-9,
        )
        total += n
        viol += rep.violations
        worst = max(worst, rep.max_abs_residual)
        print(f"    cards={cards} dirichlet={dc} zero_prob={zp}: "
              f"試行 {n}, 違反 {rep.violations}, |残差|max = {rep.max_abs_residual:.3e}")
    print(f"\n  掃引合計: {total} 試行、違反 {viol}、|残差| の全体最大 = {worst:.3e}")
    print(f"  V1 判定: {'TRUE (記号的に証明済)' if proved else 'FALSE'}")


# --------------------------------------------------------------------------
# V2 — 恒等式 (5) と (4) の使い方
# --------------------------------------------------------------------------
def note_setup_net(
    T: np.ndarray, f1, f2, card_a: int = 2, card_b: int = 2, card_x: int = 2
) -> BayesNet:
    """ノートの設定: A ⊥ B、決定論的符号器 X₁=f₁(A,B) / X₂=f₂(A,B)、メモリレス BC `T(y,z|x)`。

    出力の組 `(Y_i, Z_i)` を**1 ノード**として置くので、`T` は積 BC でなくてよい。
    メモリレス性は「同一の `T` を X₁ と X₂ に別々に適用する」という形で入る。
    """
    ny, nz = T.shape[1], T.shape[2]
    bn = BayesNet()
    bn.root("A", card_a).root("B", card_b)
    bn.deterministic("X1", card_x, ["A", "B"], f1)
    bn.deterministic("X2", card_x, ["A", "B"], f2)
    bn.add(("Y1", "Z1"), (ny, nz), ["X1"], kernel=T)
    bn.add(("Y2", "Z2"), (ny, nz), ["X2"], kernel=T)
    return bn


def random_setup(card_x: int = 3, ny: int = 3, nz: int = 3) -> Joint:
    T = rng.dirichlet(np.ones(ny * nz), size=card_x).reshape(card_x, ny, nz)
    ca, cb = int(rng.integers(2, 4)), int(rng.integers(2, 4))
    t1 = rng.integers(0, card_x, size=(ca, cb))
    t2 = rng.integers(0, card_x, size=(ca, cb))
    bn = note_setup_net(T, lambda a, b: int(t1[a, b]), lambda a, b: int(t2[a, b]),
                        card_a=ca, card_b=cb, card_x=card_x)
    return bn.build(rng)


def random_setup_with_memory() -> Joint:
    """負のコントロール 1: メモリレス性を壊す。

    ⚠ 「2 回目の出力が X₁ にも依存する」だけでは (4) は壊れない — X₁,X₂ が (A,B) の
    決定論的関数なので (A,B) で条件付けると入力が固定され、別ノードの出力は依然
    条件付き独立になる。壊すには**4 つの出力を 1 つの結合カーネル**から引く必要がある
    (= 使用回をまたいで雑音が相関する、真の memory)。
    """
    cx, ny, nz = 3, 2, 2
    T = rng.dirichlet(np.ones((ny * nz) ** 2), size=cx * cx).reshape(
        cx, cx, ny, nz, ny, nz
    )
    t1 = rng.integers(0, cx, size=(2, 2))
    t2 = rng.integers(0, cx, size=(2, 2))
    bn = BayesNet()
    bn.root("A", 2).root("B", 2)
    bn.deterministic("X1", cx, ["A", "B"], lambda a, b: int(t1[a, b]))
    bn.deterministic("X2", cx, ["A", "B"], lambda a, b: int(t2[a, b]))
    bn.add(("Y1", "Z1", "Y2", "Z2"), (ny, nz, ny, nz), ["X1", "X2"], kernel=T)
    return bn.build(rng)


def random_setup_dependent_messages() -> Joint:
    """負のコントロール 2: メモリレスのまま A ⊥ B を壊す (相関したメッセージ)。"""
    cx, ny, nz = 3, 3, 3
    T = rng.dirichlet(np.ones(ny * nz), size=cx).reshape(cx, ny, nz)
    t1 = rng.integers(0, cx, size=(2, 2))
    t2 = rng.integers(0, cx, size=(2, 2))
    bn = BayesNet()
    bn.root("A", 2)
    bn.add("B", 2, ["A"])  # B は A に依存 -> I(A;B) > 0
    bn.deterministic("X1", cx, ["A", "B"], lambda a, b: int(t1[a, b]))
    bn.deterministic("X2", cx, ["A", "B"], lambda a, b: int(t2[a, b]))
    bn.add(("Y1", "Z1"), (ny, nz), ["X1"], kernel=T)
    bn.add(("Y2", "Z2"), (ny, nz), ["X2"], kernel=T)
    return bn.build(rng)


def v2() -> None:
    rule("V2 — 恒等式 (5) と、それが (4) を正しく使っているか")

    print("  [記号展開 その1] (6) は仮定なしの恒等式か (鎖則だけで出るはず)")
    proved6, res6 = prove_identity(f"({PHI}) - ({PSI})", EQ6_RHS)
    print(f"    残差 = {res6!r}  -> 恒等式か: {proved6}")

    print("\n  [記号展開 その2] (5) を無仮定で主張したらどうなるか")
    proved5, res5 = prove_identity(PHI, EQ5_RHS)
    print(f"    残差 (Φ − 右辺) = {res5!r}")
    print(f"    -> 無仮定では恒等式か: {proved5}")
    print("    残差が I(A;B) − I(Y1;Z2|A,B) と一致するか (= (7) から予測される形):")
    matched, res_diff = prove_identity(
        f"({PHI}) - ({EQ5_RHS})", "I(A;B) - I(Y1;Z2|A,B)"
    )
    print(f"      差 = {res_diff!r}  -> 一致: {matched}")
    print("    ⟹ (5) は『I(A;B) = 0 かつ I(Y1;Z2|A,B) = 0』と**同値**な条件の下でのみ成立。")

    print("\n  [構造制約つき掃引] A ⊥ B / 決定論的符号器 / メモリレス BC (積 BC に限らない)")
    for label, sampler, trials in [
        ("|X|=3, |Y|=|Z|=3", lambda: random_setup(3, 3, 3), 4000),
        ("|X|=2, |Y|=2,|Z|=3", lambda: random_setup(2, 2, 3), 4000),
        ("|X|=4, |Y|=3,|Z|=2", lambda: random_setup(4, 3, 2), 3000),
    ]:
        # (4) と I(A;B)=0 が本当に構造から出るか
        rep4 = test_relation("I(Y1;Z2|A,B)", "0*H(A)", sampler, trials=trials, tol=1e-12)
        rep4b = test_relation("I(Y1,Z1;Y2,Z2|A,B)", "0*H(A)", sampler,
                              trials=trials, tol=1e-12)
        repab = test_relation("I(A;B)", "0*H(A)", sampler, trials=trials, tol=1e-12)
        rep5 = test_relation(PHI, EQ5_RHS, sampler, trials=trials, tol=1e-11)
        repge = test_relation(PHI, PSI, sampler, rel=">=", trials=trials, tol=1e-11)
        print(f"    {label}: 試行 {trials}")
        print(f"      (4)  I(Y1;Z2|A,B) = 0            違反 {rep4.violations}, "
              f"max = {rep4.max_abs_residual:.3e}")
        print(f"      強い形 I(Y1,Z1;Y2,Z2|A,B) = 0    違反 {rep4b.violations}, "
              f"max = {rep4b.max_abs_residual:.3e}")
        print(f"      I(A;B) = 0                      違反 {repab.violations}, "
              f"max = {repab.max_abs_residual:.3e}")
        print(f"      (5)  Φ = Ψ + I(Y1;Z2) + I(A;B|Y1,Z2)   違反 {rep5.violations}, "
              f"|残差|max = {rep5.max_abs_residual:.3e}")
        print(f"      系   Φ >= Ψ                      違反 {repge.violations}, "
              f"最小 Φ−Ψ = {-repge.worst_residual:.6e}")

    print("\n  [負のコントロール 1] メモリレス性を壊す (4 出力を 1 つの結合カーネルから引く)")
    rep4m = test_relation("I(Y1;Z2|A,B)", "0*H(A)", random_setup_with_memory,
                          trials=2000, tol=1e-9)
    rep5m = test_relation(PHI, EQ5_RHS, random_setup_with_memory, trials=2000, tol=1e-9)
    print(f"    (4)  I(Y1;Z2|A,B) = 0   違反 {rep4m.violations}/2000, "
          f"max = {rep4m.max_abs_residual:.3e}")
    print(f"    (5)                     違反 {rep5m.violations}/2000, "
          f"|残差|max = {rep5m.max_abs_residual:.3e}")

    print("\n  [負のコントロール 2] メモリレスのまま A ⊥ B を壊す")
    repab2 = test_relation("I(A;B)", "0*H(A)", random_setup_dependent_messages,
                           trials=2000, tol=1e-9)
    rep5d = test_relation(PHI, EQ5_RHS, random_setup_dependent_messages,
                          trials=2000, tol=1e-9)
    print(f"    I(A;B) = 0              違反 {repab2.violations}/2000, "
          f"max = {repab2.max_abs_residual:.3e}")
    print(f"    (5)                     違反 {rep5d.violations}/2000, "
          f"|残差|max = {rep5d.max_abs_residual:.3e}")
    print("    ⟹ (4) と I(A;B)=0 はどちらも load-bearing — 片方でも外すと (5) は壊れる。")

    print("\n  [Φ − Ψ の符号] (5) の右辺の残差は 2 本とも相互情報量なので常に >= 0")
    vals = []
    for _ in range(3000):
        J = random_setup(3, 3, 3)
        vals.append(J.eval(PHI) - J.eval(PSI))
    vals = np.array(vals)
    print(f"    Φ−Ψ の範囲 = [{vals.min():.6e}, {vals.max():.6e}] (nat)、"
          f"負の値 {int((vals < -1e-12).sum())} 件")
    print("    ⟹ この設定では Φ ≥ Ψ が**常に**成り立つ。")


# --------------------------------------------------------------------------
# V3 — 数値例 X₁ = A ∧ B
# --------------------------------------------------------------------------
def bsc(e: float) -> np.ndarray:
    return np.array([[1 - e, e], [e, 1 - e]])


def and_example(eps: float) -> Joint:
    """A,B 独立公平ビット、X₁ = A ∧ B、X₂ = 0、T_ε(y,z|x) = BSC_ε(y|x) BSC_ε(z|x)。"""
    W = bsc(eps)
    T = W[:, :, None] * W[:, None, :]  # T[x,y,z] = BSC(y|x) BSC(z|x)
    bn = BayesNet()
    bn.root("A", 2, pmf=[0.5, 0.5]).root("B", 2, pmf=[0.5, 0.5])
    bn.deterministic("X1", 2, ["A", "B"], lambda a, b: a & b)
    bn.deterministic("X2", 2, ["A", "B"], lambda a, b: 0)
    bn.add(("Y1", "Z1"), (2, 2), ["X1"], kernel=T)
    bn.add(("Y2", "Z2"), (2, 2), ["X2"], kernel=T)
    return bn.build()


def h2(x: float) -> float:
    return float(-x * np.log2(x) - (1 - x) * np.log2(1 - x))


def v3() -> None:
    rule("V3 — 数値例 X₁ = A ∧ B の値 (すべて bit)")

    J = and_example(0.0)  # ノイズなし: Y_i = Z_i = X_i
    b = "bits"
    print("  ノートの主張値 vs 実計算 (ノイズなし Y_i = Z_i = X_i):")
    rows = [
        ("I(A;X1) = h2(1/4) - 1/2", h2(0.25) - 0.5, J.eval("I(A;Y1)", b)),
        ("I(B;X1) = h2(1/4) - 1/2", h2(0.25) - 0.5, J.eval("I(B;Z1)", b)),
        ("Phi = 2 h2(1/4) - 1  (≈ 0.62256)", 2 * h2(0.25) - 1, J.eval(PHI, b)),
        ("I(A;B|X1) = 1 - h2(1/4)  (≈ 0.18872)", 1 - h2(0.25), J.eval("I(A;B|Y1)", b)),
        ("Phi - Psi  (≈ 0.18872)", 1 - h2(0.25), J.eval(PHI, b) - J.eval(PSI, b)),
    ]
    for name, claimed, got in rows:
        print(f"    {name:42s} 主張 {claimed!r}")
        print(f"    {'':42s} 実計算 {got!r}   差 {abs(claimed - got):.3e}")
    print(f"    (参考) Psi = {J.eval(PSI, b)!r}")
    print(f"    (参考) h2(1/4) = {h2(0.25)!r}")
    print(f"    (5) の右辺内訳: I(Y1;Z2) = {J.eval('I(Y1;Z2)', b)!r}, "
          f"I(A;B|Y1,Z2) = {J.eval('I(A;B|Y1,Z2)', b)!r}")
    ok5 = abs(J.eval(PHI, b) - (J.eval(PSI, b) + J.eval("I(Y1;Z2)", b)
                                + J.eval("I(A;B|Y1,Z2)", b)))
    print(f"    (5) の残差 = {ok5:.3e}")

    print("\n  full-support への摂動 (連続性を信用せず ε を実際に振る):")
    print("    full-supp 列は**チャネル** T_ε(y,z|x) > 0 の判定 (ノートの言う full-support BC)。")
    print("    同時分布の側は決定論的符号器を含むので必ず 0 を持つ — そちらではない。")
    print(f"    {'eps':>10} {'min T(y,z|x)':>14} {'Phi':>14} {'Psi':>14} {'Phi-Psi':>14} "
          f"{'I(Y1;Z2)':>12} {'I(A;B|Y1,Z2)':>14} {'full-supp':>10}")
    for eps in (0.0, 1e-6, 1e-4, 1e-3, 0.01, 0.05, 0.1, 0.2, 0.3, 0.4, 0.45, 0.499, 0.5):
        Je = and_example(eps)
        W = bsc(eps)
        T = W[:, :, None] * W[:, None, :]
        phi, psi = Je.eval(PHI, b), Je.eval(PSI, b)
        full = "yes" if T.min() > 0 else "no"
        print(f"    {eps:>10} {T.min():>14.3e} {phi:>14.9f} {psi:>14.9f} {phi - psi:>14.9f} "
              f"{Je.eval('I(Y1;Z2)', b):>12.3e} {Je.eval('I(A;B|Y1,Z2)', b):>14.9f} "
              f"{full:>10}")
    print("    (T_ε は 0 < ε < 1/2 で full support。ε = 1/2 は Y,Z が X と独立になる退化端)")


def main() -> None:
    v1()
    v2()
    v3()


if __name__ == "__main__":
    main()
