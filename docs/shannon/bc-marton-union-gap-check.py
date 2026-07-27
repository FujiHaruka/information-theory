"""bcOuterRegionUV ⊆ martonRegionUnionFS が偽であることの数値的な再検証スクリプト。

何を計算しているか
------------------
劣化 BSC 対 (q=0.1, p=0.25) の superposition corner 点 (I(X;Y1|U), I(U;Y2)) が
martonRegionUnion W (共通補助変数 U0 を持たない Marton 内界の、補助アルファベットに
ついての和集合) に入るかを判定する。出力する「スラック」は
  min(I1 - a, I2 - b, I1 + I2 - I12 - (a + b))
を補助アルファベットの大きさごとに数値最適化した最大値で、これが負なら corner 点は
union に入らない (closure を跨いでも入らないことは、負のスラックが一様に下から
離れていることで従う)。あわせて (1) sim が閉形式と一致することの検証、(2) 退化境界
2 本 (受信機 1 が無雑音 q→0 / 受信機 2 が無用 p=1/2) でスラックがちょうど 0 になる
ことの確認、(3) 入力アルファベット 3 元の非対称チャネルでの追試を行う。

判定の位置づけと結果表 → docs/shannon/bc-facts.md /
docs/shannon/bc-lessnoisy-equality-inventory.md §Q1。

実行方法
--------
  python3 docs/shannon/bc-marton-union-gap-check.py     # numpy と scipy が要る

全体で 5 分を超える (多点再スタートの Nelder-Mead を補助アルファベットの大きさごとに
回すため)。sim が Lean の def と一致していることの確認だけなら check_sim() 単体で
数秒で終わる。

Lean の def との対応 (逐語)
---------------------------
Semantics mirrored verbatim from the Lean defs:

  Shannon/Bridge.lean:40      entropy mu Xs      = sum_x negMulLog ((mu.map Xs).real {x})
                                                 = -sum_x P(x) log P(x)      (natural log)
  Marton/Setup.lean:57        martonJointDistribution pV K W : law of (V1,V2,X,Y1,Y2)
                                                 via pV -> K -> W
  Marton/Setup.lean:244       martonInfo1   = H(V1) + H(Y1) - H(V1,Y1)
  Marton/Setup.lean:252       martonInfo2   = H(V2) + H(Y2) - H(V2,Y2)
  Marton/Setup.lean:262       martonInfoV1V2= H(V1) + H(V2) - H(V1,V2)
  Marton/Basic.lean:40        InMartonRegion R1 R2 I1 I2 I12 :
                                R1 <= I1, R2 <= I2, R1 + R2 <= I1 + I2 - I12
  Achievability/Setup.lean:100 bcInfo2  = H(U) + H(Y2) - H(U,Y2)              = I(U;Y2)
  Achievability/Setup.lean:111 bcInfo1  = H(U,X)+H(U,Y1)-H(U,X,Y1)-H(U)       = I(X;Y1|U)

Everything is in nats (Real.negMulLog / klDiv use Real.log).
"""

import itertools
import numpy as np
from scipy.optimize import minimize

rng = np.random.default_rng(20260727)
EPS = 1e-300


def H(p):
    p = np.asarray(p, dtype=float).ravel()
    p = p[p > 0]
    return float(-(p * np.log(p)).sum())


def hb(x):
    """binary entropy in nats"""
    if x <= 0 or x >= 1:
        return 0.0
    return -x * np.log(x) - (1 - x) * np.log(1 - x)


def conv(a, b):
    return a * (1 - b) + b * (1 - a)


def bsc(e):
    """W[x, y] = P(y | x) for a BSC with crossover e"""
    return np.array([[1 - e, e], [e, 1 - e]])


# ---------------------------------------------------------------- sim checks
def marton_infos(pV, K, W1, W2):
    """pV : (n1, n2);  K : (n1, n2, |a|) with K[v1,v2,x] = P(x|v1,v2)
    W1 : (|a|, |b1|),  W2 : (|a|, |b2|).  Returns (I(V1;Y1), I(V2;Y2), I(V1;V2))."""
    # joint of (V1, V2, X)
    J = pV[:, :, None] * K                      # (n1, n2, |a|)
    pV1 = J.sum(axis=(1, 2))
    pV2 = J.sum(axis=(0, 2))
    pV1V2 = J.sum(axis=2)
    pV1X = J.sum(axis=1)                        # (n1, |a|)
    pV2X = J.sum(axis=0)                        # (n2, |a|)
    pV1Y1 = pV1X @ W1                           # (n1, |b1|)
    pV2Y2 = pV2X @ W2                           # (n2, |b2|)
    I1 = H(pV1) + H(pV1Y1.sum(axis=0)) - H(pV1Y1)
    I2 = H(pV2) + H(pV2Y2.sum(axis=0)) - H(pV2Y2)
    I12 = H(pV1) + H(pV2) - H(pV1V2)
    return I1, I2, I12


def superposition_point(pU, K, W1, W2):
    """bcInfo1 = I(X;Y1|U), bcInfo2 = I(U;Y2) for pU on U and K[u,x]=P(x|u)."""
    J = pU[:, None] * K                          # (|U|, |a|)
    pUY1 = J @ W1
    pUY2 = J @ W2
    pUXY1 = J[:, :, None] * W1[None, :, :]       # (|U|, |a|, |b1|)
    # I(X;Y1|U) = H(U,X) + H(U,Y1) - H(U,X,Y1) - H(U)
    a = H(J) + H(pUY1) - H(pUXY1) - H(pU)
    # I(U;Y2) = H(U) + H(Y2) - H(U,Y2)
    b = H(pU) + H(pUY2.sum(axis=0)) - H(pUY2)
    return a, b


def check_sim():
    print("=== sim validation against closed forms ===")
    q, p = 0.10, 0.25
    W1, W2 = bsc(q), bsc(p)
    # (1) V1 = X uniform binary, V2 trivial  ->  I(V1;Y1) = ln2 - h(q)
    pV = np.array([[0.5], [0.5]])
    K = np.zeros((2, 1, 2)); K[0, 0, 0] = 1.0; K[1, 0, 1] = 1.0
    I1, I2, I12 = marton_infos(pV, K, W1, W2)
    print(f"  I(X;Y1) sim={I1:.10f} closed={np.log(2)-hb(q):.10f}")
    print(f"  I(V2;Y2) sim={I2:.10f} closed=0 ; I(V1;V2) sim={I12:.10f} closed=0")
    # (2) V1 = V2 = X uniform binary -> I(V1;V2) = ln 2
    pV = np.array([[0.5, 0.0], [0.0, 0.5]])
    K = np.zeros((2, 2, 2)); K[0, 0, 0] = 1.0; K[1, 1, 1] = 1.0
    K[0, 1, 0] = 1.0; K[1, 0, 0] = 1.0
    I1, I2, I12 = marton_infos(pV, K, W1, W2)
    print(f"  I(V1;V2) sim={I12:.10f} closed={np.log(2):.10f}")
    # (3) superposition point closed form: U~Bern(1/2), X = U + Bern(beta)
    for beta in (0.1, 0.2, 0.35):
        pU = np.array([0.5, 0.5])
        K = np.array([[1 - beta, beta], [beta, 1 - beta]])
        a, b = superposition_point(pU, K, W1, W2)
        a_cf = hb(conv(beta, q)) - hb(q)
        b_cf = np.log(2) - hb(conv(beta, p))
        print(f"  beta={beta}: a sim={a:.10f} closed={a_cf:.10f} | "
              f"b sim={b:.10f} closed={b_cf:.10f}")
    # (4) the V1 = X, V2 = U Marton choice reproduces the analytic deficit
    for beta in (0.1, 0.2, 0.35):
        # V1 = X, V2 = U, with U~Bern(1/2), X = U + Bern(beta):
        # p(v1=x, v2=u) = 1/2 * P(x|u); K is deterministic X = V1.
        pV = np.array([[0.5 * (1 - beta), 0.5 * beta],
                       [0.5 * beta, 0.5 * (1 - beta)]])   # rows v1 = x, cols v2 = u
        K = np.zeros((2, 2, 2))
        K[0, :, 0] = 1.0
        K[1, :, 1] = 1.0
        I1, I2, I12 = marton_infos(pV, K, W1, W2)
        a, b = superposition_point(np.array([.5, .5]),
                                   np.array([[1 - beta, beta], [beta, 1 - beta]]), W1, W2)
        deficit = (a + b) - (I1 + I2 - I12)
        print(f"  beta={beta}: deficit sim={deficit:.10f} "
              f"closed h(b*q)-h(b)={hb(conv(beta, q)) - hb(beta):.10f}")
    print()


# ---------------------------------------------------------------- search
def slack(theta, n1, n2, na, W1, W2, a, b):
    t = theta[: n1 * n2].reshape(n1, n2)
    t = t - t.max()
    pV = np.exp(t); pV /= pV.sum()
    kk = theta[n1 * n2:].reshape(n1, n2, na)
    kk = kk - kk.max(axis=2, keepdims=True)
    K = np.exp(kk); K /= K.sum(axis=2, keepdims=True)
    I1, I2, I12 = marton_infos(pV, K, W1, W2)
    return min(I1 - a, I2 - b, I1 + I2 - I12 - a - b)


def search(n1, n2, na, W1, W2, a, b, restarts=40):
    dim = n1 * n2 + n1 * n2 * na
    best, bestx = -np.inf, None
    for _ in range(restarts):
        x0 = rng.normal(0, 2.0, dim)
        res = minimize(lambda z: -slack(z, n1, n2, na, W1, W2, a, b), x0,
                       method="Nelder-Mead",
                       options={"maxiter": 20000, "maxfev": 20000,
                                "xatol": 1e-10, "fatol": 1e-12})
        if -res.fun > best:
            best, bestx = -res.fun, res.x
    return best, bestx


def main():
    check_sim()
    q, p = 0.10, 0.25
    W1, W2 = bsc(q), bsc(p)
    pprime = (p - q) / (1 - 2 * q)
    print(f"=== channel: degraded BSC pair q={q}, p={p} "
          f"(degrading BSC p'={pprime:.6f}, q*p'={conv(q, pprime):.6f}) ===\n")

    print(f"{'beta':>6} {'a=I(X;Y1|U)':>12} {'b=I(U;Y2)':>11} "
          f"{'V1=X,V2=U slack':>16} "
          f"{'(2,2)':>10} {'(3,3)':>10} {'(4,2)':>10} {'(4,4)':>10}")
    for beta in (0.05, 0.1, 0.2, 0.3, 0.4):
        pU = np.array([0.5, 0.5])
        Ksup = np.array([[1 - beta, beta], [beta, 1 - beta]])
        a, b = superposition_point(pU, Ksup, W1, W2)
        # the named candidate V1 = X, V2 = U
        pV = np.array([[0.5 * (1 - beta), 0.5 * beta],
                       [0.5 * beta, 0.5 * (1 - beta)]])
        Kd = np.zeros((2, 2, 2)); Kd[0, :, 0] = 1.0; Kd[1, :, 1] = 1.0
        I1, I2, I12 = marton_infos(pV, Kd, W1, W2)
        s_named = min(I1 - a, I2 - b, I1 + I2 - I12 - a - b)
        row = [f"{beta:>6.2f} {a:>12.6f} {b:>11.6f} {s_named:>16.6f}"]
        for (n1, n2) in ((2, 2), (3, 3), (4, 2), (4, 4)):
            s, _ = search(n1, n2, 2, W1, W2, a, b,
                          40 if n1 * n2 <= 9 else 25)
            row.append(f"{s:>10.6f}")
        print(" ".join(row))

    # degenerate boundary #1: noiseless first receiver q = 0
    print("\n=== degenerate boundary q = 0 (Y1 = X, expect slack ~ 0) ===")
    W1z, W2z = bsc(1e-12), bsc(0.25)
    for beta in (0.1, 0.3):
        a, b = superposition_point(np.array([.5, .5]),
                                   np.array([[1 - beta, beta], [beta, 1 - beta]]), W1z, W2z)
        s22, _ = search(2, 2, 2, W1z, W2z, a, b, restarts=40)
        s33, _ = search(3, 3, 2, W1z, W2z, a, b, restarts=40)
        print(f"  beta={beta}: a={a:.6f} b={b:.6f} slack(2,2)={s22:.6f} slack(3,3)={s33:.6f}")

    # degenerate boundary #2: p = 1/2 (second receiver useless), b = 0
    print("\n=== degenerate boundary p = 1/2 (b = 0, expect slack >= 0) ===")
    W1h, W2h = bsc(0.10), bsc(0.5)
    for beta in (0.1, 0.3):
        a, b = superposition_point(np.array([.5, .5]),
                                   np.array([[1 - beta, beta], [beta, 1 - beta]]), W1h, W2h)
        s22, _ = search(2, 2, 2, W1h, W2h, a, b, restarts=40)
        print(f"  beta={beta}: a={a:.6f} b={b:.6f} slack(2,2)={s22:.6f}")

    # non-symmetric less-noisy (non-degraded) channel: Z-channel to receiver 1
    print("\n=== larger input alphabet |a| = 3, BSC-like pair ===")
    W1t = np.array([[0.8, 0.1, 0.1], [0.1, 0.8, 0.1], [0.1, 0.1, 0.8]])
    W2t = np.array([[0.5, 0.25, 0.25], [0.25, 0.5, 0.25], [0.25, 0.25, 0.5]])
    for lam in (0.2, 0.4):
        pU = np.array([1 / 3, 1 / 3, 1 / 3])
        Ksup = (1 - lam) * np.eye(3) + lam / 3 * np.ones((3, 3))
        a, b = superposition_point(pU, Ksup, W1t, W2t)
        s33, _ = search(3, 3, 3, W1t, W2t, a, b, restarts=40)
        s44, _ = search(4, 4, 3, W1t, W2t, a, b, restarts=25)
        print(f"  lam={lam}: a={a:.6f} b={b:.6f} slack(3,3)={s33:.6f} slack(4,4)={s44:.6f}")


if __name__ == "__main__":
    main()
