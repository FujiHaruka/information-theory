"""BC 未解決問題 relay の数値 probe harness (L1 で整備)。

位置づけ
--------
親 plan `docs/shannon/bc-open-problem-plan.md` §5-2 (kill-first) の道具。候補命題を
立てたらまず数値で殺しにいく、という規約を空文にしないための共通基盤で、以後の leg は
本 module を import して「命題を差し替えるだけ」で probe を書けることを狙う。

先例は `bc-marton-union-gap-check.py` (逆包含 1 本を実際に殺した)。あれは 1 つの問い
専用に配線されていたので、そこから次の 3 つを切り出して汎用化した:

1. **情報量式の評価** — 有限個の変数の同時分布の上で、エントロピー / 条件付き
   エントロピー / 相互情報量 / 条件付き相互情報量の**線形結合**を文字列で書いて評価する
   (`parse` / `LinInfo.evaluate`)。同じ表現を**記号的に**同時エントロピーの線形結合へ
   展開できるので、恒等式の主張は係数の相殺で**証明**できる (`prove_identity`) —
   ランダム分布での成立は証拠にすぎず、係数相殺は証明である、を型で区別する。
2. **構造制約つきランダム同時分布での主張の検定** — 独立性 / Markov 連鎖 / 決定論的
   関数 / メモリレス積構造は、すべて `BayesNet` の DAG として指定する (`test_relation`)。
   無制約なら `random_joint`。
3. **補助変数上の最大化** — 多点再スタートの局所最適化 (`maximize`)。局所最大性の
   証明書は `local_max_certificate` (論文の摂動族 pε = (1−ε)p + ε s に対応)。

単位
----
既定は **nat** (`Real.log`)。これは Lean 側 `Shannon/Bridge.lean:entropy`
(`negMulLog` = 自然対数) と同じ規約。`units="bits"` で 2 を底に切り替えられる
(外部ノートの数値例は bit で書かれているのでそちら)。

Lean の def との照合について
----------------------------
本 module は**情報量の一般論しか持たない** — Marton 領域や容量領域といった
InformationTheory 側の `def` には依存しない。したがって「sim を実 `def` と逐語照合してから
FALSE を信用する」(CLAUDE.md) の照合対象は、consumer 側の probe スクリプトが自分の
扱う `def` について負う。本 module が負うのは entropy の規約 (上記) だけで、それは
`Shannon/Bridge.lean:40  entropy mu Xs = sum_x negMulLog ((mu.map Xs).real {x})` と
同じ自然対数版である。

自己検証
--------
    python3 docs/shannon/bc_probe.py     # selftest (数秒)

命名について: 親 plan §8 の `docs/shannon/bc-*-check.py` は**実行可能な probe** の規約で、
本ファイルはそれらが import するライブラリなので import 可能な名前 (アンダースコア) を採る。
"""

from __future__ import annotations

import itertools
import re
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Callable, Iterable, Sequence

import numpy as np
from scipy.optimize import minimize

LN2 = float(np.log(2.0))

__all__ = [
    "LinInfo",
    "parse",
    "prove_identity",
    "Joint",
    "BayesNet",
    "random_joint",
    "RelationReport",
    "test_relation",
    "OptReport",
    "maximize",
    "softmax",
    "local_max_certificate",
    "selftest",
]


# --------------------------------------------------------------------------
# 1. 情報量式 — 同時エントロピーの線形結合としての記号表現
# --------------------------------------------------------------------------
_Key = frozenset  # 変数名の集合。h(S) の S。


class LinInfo:
    """`sum_S c_S h(S)` (S = 変数名の集合、c_S は有理数) という形の線形結合。

    `H(...)` / `I(...)` はすべてこの形に展開できる。恒等式の主張 lhs = rhs は
    `lhs - rhs` の全係数が 0 になることと同値ではないが (十分条件)、係数が全部 0 なら
    **任意の同時分布で**等式が成り立つので、それは証明になる。
    """

    __slots__ = ("terms",)

    def __init__(self, terms: dict[_Key, Fraction] | None = None) -> None:
        self.terms: dict[_Key, Fraction] = {}
        if terms:
            for key, coef in terms.items():
                self._add(key, coef)

    # -- 構成 --------------------------------------------------------------
    @staticmethod
    def h(*names: str) -> "LinInfo":
        """同時エントロピー h(names)。空集合は 0。"""
        key = frozenset(n for n in names if n)
        if not key:
            return LinInfo()
        return LinInfo({key: Fraction(1)})

    def _add(self, key: _Key, coef: Fraction) -> None:
        if not key:
            return  # h(空集合) = 0
        new = self.terms.get(key, Fraction(0)) + coef
        if new == 0:
            self.terms.pop(key, None)
        else:
            self.terms[key] = new

    # -- 代数 --------------------------------------------------------------
    def __add__(self, other: "LinInfo") -> "LinInfo":
        out = LinInfo(self.terms)
        for key, coef in other.terms.items():
            out._add(key, coef)
        return out

    def __sub__(self, other: "LinInfo") -> "LinInfo":
        return self + (-other)

    def __neg__(self) -> "LinInfo":
        return LinInfo({k: -c for k, c in self.terms.items()})

    def __mul__(self, scalar) -> "LinInfo":
        c = _to_fraction(scalar)
        return LinInfo({k: v * c for k, v in self.terms.items()})

    __rmul__ = __mul__

    def __truediv__(self, scalar) -> "LinInfo":
        return self * (Fraction(1) / _to_fraction(scalar))

    # -- 判定と表示 --------------------------------------------------------
    def is_zero(self) -> bool:
        """全係数が 0。これが真なら主張は任意の同時分布で成り立つ (= 証明)。"""
        return not self.terms

    def __repr__(self) -> str:
        if not self.terms:
            return "0"
        parts = []
        for key in sorted(self.terms, key=lambda s: (len(s), sorted(s))):
            coef = self.terms[key]
            sign = "+" if coef > 0 else "-"
            parts.append(f"{sign}{abs(coef)} h({','.join(sorted(key))})")
        return " ".join(parts)

    # -- 評価 --------------------------------------------------------------
    def evaluate(self, joint: "Joint", units: str = "nats") -> float:
        total = 0.0
        for key, coef in self.terms.items():
            total += float(coef) * joint.entropy(key)
        return total / LN2 if units == "bits" else total

    def variables(self) -> set[str]:
        out: set[str] = set()
        for key in self.terms:
            out |= set(key)
        return out


def _to_fraction(x) -> Fraction:
    if isinstance(x, Fraction):
        return x
    if isinstance(x, int):
        return Fraction(x)
    return Fraction(str(x))


# -- パーサ ----------------------------------------------------------------
# H(A,B|C) / I(A;B|C) / I(A,B;C) の形の原子。原子の中に括弧は入らないので、
# 原子を先に置換してから残りの算術を Python の式として評価する。
_ATOM = re.compile(r"\b([HI])\(([^()]*)\)")
_NUM = re.compile(r"(?<![\w.])(\d+(?:\.\d+)?)(?![\w.])")


def _varlist(s: str) -> frozenset:
    return frozenset(v.strip() for v in s.split(",") if v.strip())


def _atom(kind: str, body: str) -> LinInfo:
    head, _, cond = body.partition("|")
    C = _varlist(cond)
    if kind == "H":
        S = _varlist(head)
        return LinInfo.h(*(S | C)) - LinInfo.h(*C)
    groups = head.split(";")
    if len(groups) != 2:
        raise ValueError(
            f"I(...) は 2 群でなければならない (与えられた群数 {len(groups)}): I({body})"
        )
    S, T = _varlist(groups[0]), _varlist(groups[1])
    if not S or not T:
        raise ValueError(f"I(...) の群が空: I({body})")
    return (
        LinInfo.h(*(S | C))
        + LinInfo.h(*(T | C))
        - LinInfo.h(*(S | T | C))
        - LinInfo.h(*C)
    )


def parse(expr: str) -> LinInfo:
    """`"I(A;Y1,Y2) + I(B;Z1,Z2) - 2*H(A|B)"` のような線形情報量式を読む。

    - `H(S)` / `H(S|C)` / `I(S;T)` / `I(S;T|C)`。S, T, C はカンマ区切りの変数名。
    - 係数は整数 / 小数 / 分数リテラル (`1/2`) が使える。
    """
    atoms: dict[str, LinInfo] = {}

    def repl(m: re.Match) -> str:
        key = f"_atom{len(atoms)}"
        atoms[key] = _atom(m.group(1), m.group(2))
        return key

    body = _ATOM.sub(repl, expr)
    if re.search(r"[A-Za-z]", re.sub(r"_atom\d+", "", body)):
        raise ValueError(f"未解釈のトークンが残った: {expr!r} -> {body!r}")
    # 数値リテラルを Fraction にして係数を厳密に保つ
    body = _NUM.sub(lambda m: f'F("{m.group(1)}")', body)
    env = dict(atoms)
    env["F"] = Fraction
    return eval(body, {"__builtins__": {}}, env)  # noqa: S307 (入力は本リポジトリ内)


def prove_identity(lhs: str | LinInfo, rhs: str | LinInfo) -> tuple[bool, LinInfo]:
    """恒等式 lhs = rhs を**記号的に**判定する。

    返り値 `(proved, residual)`。`proved` が真なら残差の全係数が相殺しており、
    主張は任意の有限同時分布で成り立つ (乱数試行ではなく証明)。偽なら残差が
    どの同時エントロピーの項として残ったかが `residual` に出る。
    """
    L = parse(lhs) if isinstance(lhs, str) else lhs
    R = parse(rhs) if isinstance(rhs, str) else rhs
    residual = L - R
    return residual.is_zero(), residual


# --------------------------------------------------------------------------
# 2. 同時分布
# --------------------------------------------------------------------------
def _entropy_nats(p: np.ndarray) -> float:
    """Lean `Shannon/Bridge.lean:entropy` と同じ規約 (自然対数、0 log 0 = 0)。"""
    q = np.asarray(p, dtype=float).ravel()
    q = q[q > 0]
    return float(-(q * np.log(q)).sum())


class Joint:
    """有限個の名前つき変数の同時 pmf。

    `p` は ndim = len(names) の非負配列で総和 1。エントロピーはキャッシュする
    (同じ表現を多数の項について評価するため)。
    """

    __slots__ = ("names", "p", "_axis", "_cache")

    def __init__(self, names: Sequence[str], p: np.ndarray, validate: bool = True):
        self.names = tuple(names)
        self.p = np.asarray(p, dtype=float)
        if validate:
            if self.p.ndim != len(self.names):
                raise ValueError(f"次元不一致: names={self.names} p.ndim={self.p.ndim}")
            if self.p.min() < -1e-12:
                raise ValueError("負の確率")
            s = self.p.sum()
            if abs(s - 1.0) > 1e-9:
                raise ValueError(f"総和が 1 でない: {s}")
        self._axis = {n: i for i, n in enumerate(self.names)}
        self._cache: dict[frozenset, float] = {}

    @property
    def cards(self) -> dict[str, int]:
        return {n: self.p.shape[i] for i, n in enumerate(self.names)}

    def marginal(self, vs: Iterable[str]) -> np.ndarray:
        keep = {self._axis[v] for v in vs}
        drop = tuple(i for i in range(self.p.ndim) if i not in keep)
        return self.p.sum(axis=drop) if drop else self.p

    def entropy(self, vs: Iterable[str]) -> float:
        key = frozenset(vs)
        if key in self._cache:
            return self._cache[key]
        val = 0.0 if not key else _entropy_nats(self.marginal(key))
        self._cache[key] = val
        return val

    def eval(self, expr: str | LinInfo, units: str = "nats") -> float:
        e = parse(expr) if isinstance(expr, str) else expr
        missing = e.variables() - set(self.names)
        if missing:
            raise ValueError(f"同時分布に無い変数: {sorted(missing)}")
        return e.evaluate(self, units)

    def describe(self, units: str = "nats", threshold: float = 0.0) -> str:
        """台の上の確率を全部並べる (反例を逐語で書き出すため)。"""
        lines = [f"names = {self.names}, shape = {self.p.shape}"]
        for idx in itertools.product(*(range(n) for n in self.p.shape)):
            val = float(self.p[idx])
            if val > threshold:
                lab = ", ".join(f"{n}={i}" for n, i in zip(self.names, idx))
                lines.append(f"  p({lab}) = {val!r}")
        return "\n".join(lines)


_LETTERS = "abcdefghijklmnopqrstuvwxyz"


@dataclass
class _Node:
    names: tuple[str, ...]
    cards: tuple[int, ...]
    parents: tuple[str, ...]
    kernel: np.ndarray | None = None
    func: Callable | None = None
    dirichlet: float = 1.0


class BayesNet:
    """構造制約を DAG で与えて同時分布を作る。

    ブリーフにある 4 種の構造制約はすべてこの 1 つの機構に載る:

    - **独立性**: 親を持たない root を複数置けば独立。
    - **Markov 連鎖** `A -> X -> Y`: 各段を 1 ノードにする (I(A;Y|X) = 0 が構造から出る)。
    - **決定論的関数**: `deterministic(...)` (`func` から one-hot カーネルを作る)。
    - **メモリレス積構造**: **同一のカーネル** `T` を各使用回の入力ノードに別々に適用する。
      1 回の使用で出力が結合している一般 BC `T(y,z|x)` は、`add(("Y1","Z1"), ..., kernel=T)`
      のように**複数名を持つ 1 ノード**として置く (Y ⊥ Z | X を仮定しないため。積 BC しか
      置けないと、メモリレス性の帰結として何が出るかの検定が狭くなる)。

    カーネル未指定のノードは `build(rng)` のたびに Dirichlet でランダムに引かれる。
    """

    def __init__(self) -> None:
        self.nodes: list[_Node] = []
        self._known: set[str] = set()

    def _register(self, names: tuple[str, ...]) -> None:
        for n in names:
            if n in self._known:
                raise ValueError(f"変数名の重複: {n}")
            self._known.add(n)

    def add(
        self,
        names: str | Sequence[str],
        cards: int | Sequence[int],
        parents: Sequence[str] = (),
        kernel: np.ndarray | None = None,
        func: Callable | None = None,
        dirichlet: float = 1.0,
    ) -> "BayesNet":
        ns = (names,) if isinstance(names, str) else tuple(names)
        cs = (cards,) if isinstance(cards, int) else tuple(cards)
        if len(ns) != len(cs):
            raise ValueError("names と cards の長さが違う")
        ps = tuple(parents)
        for p in ps:
            if p not in self._known:
                raise ValueError(f"親 {p} が未定義 (トポロジカル順に add すること)")
        self._register(ns)
        if kernel is not None:
            kernel = np.asarray(kernel, dtype=float)
            want = tuple(self._card_of(p) for p in ps) + cs
            if kernel.shape != want:
                raise ValueError(f"kernel の shape が {want} でない: {kernel.shape}")
        self.nodes.append(_Node(ns, cs, ps, kernel, func, dirichlet))
        return self

    def root(self, name: str, card: int, pmf=None, dirichlet: float = 1.0) -> "BayesNet":
        k = None if pmf is None else np.asarray(pmf, dtype=float)
        return self.add(name, card, (), kernel=k, dirichlet=dirichlet)

    def deterministic(
        self, names: str | Sequence[str], cards: int | Sequence[int],
        parents: Sequence[str], func: Callable
    ) -> "BayesNet":
        """`func(*parent_indices)` が値 (または値のタプル) を返す決定論的ノード。"""
        return self.add(names, cards, parents, func=func)

    def _card_of(self, name: str) -> int:
        for nd in self.nodes:
            for n, c in zip(nd.names, nd.cards):
                if n == name:
                    return c
        raise KeyError(name)

    # -- 構築 --------------------------------------------------------------
    def _resolve(self, nd: _Node, rng: np.random.Generator | None) -> np.ndarray:
        if nd.kernel is not None:
            return nd.kernel
        pshape = tuple(self._card_of(p) for p in nd.parents)
        if nd.func is not None:
            k = np.zeros(pshape + nd.cards)
            for idx in itertools.product(*(range(n) for n in pshape)):
                out = nd.func(*idx)
                out = (out,) if not isinstance(out, tuple) else out
                k[idx + tuple(out)] = 1.0
            return k
        if rng is None:
            raise ValueError(f"ノード {nd.names} のカーネル未指定だが rng が無い")
        nrow = int(np.prod(pshape, dtype=int)) if pshape else 1
        ncol = int(np.prod(nd.cards, dtype=int))
        k = rng.dirichlet(np.full(ncol, nd.dirichlet), size=nrow)
        return k.reshape(pshape + nd.cards)

    def build(self, rng: np.random.Generator | None = None) -> Joint:
        names: list[str] = []
        arr: np.ndarray | None = None
        for nd in self.nodes:
            k = self._resolve(nd, rng)
            if arr is None:
                arr = k.copy()
                names = list(nd.names)
                continue
            if len(names) + len(nd.names) > len(_LETTERS):
                raise ValueError("変数が 26 個を超えた")
            old_sub = "".join(_LETTERS[i] for i in range(len(names)))
            new_sub = "".join(_LETTERS[len(names) + j] for j in range(len(nd.names)))
            par_sub = "".join(_LETTERS[names.index(p)] for p in nd.parents)
            arr = np.einsum(
                f"{old_sub},{par_sub}{new_sub}->{old_sub}{new_sub}", arr, k
            )
            names += list(nd.names)
        if arr is None:
            raise ValueError("空の BayesNet")
        return Joint(names, arr)

    def sampler(self, rng: np.random.Generator) -> Callable[[], Joint]:
        return lambda: self.build(rng)


def random_joint(
    cards: dict[str, int],
    rng: np.random.Generator,
    dirichlet: float = 1.0,
    zero_prob: float = 0.0,
) -> Joint:
    """構造制約なしの同時分布 (Dirichlet)。

    `dirichlet < 1` で尖った分布、`zero_prob > 0` で台に穴を開ける (退化境界を踏むため)。
    """
    names = list(cards)
    shape = tuple(cards[n] for n in names)
    n = int(np.prod(shape, dtype=int))
    p = rng.dirichlet(np.full(n, dirichlet))
    if zero_prob > 0:
        mask = rng.random(n) < zero_prob
        if mask.all():
            mask[rng.integers(n)] = False
        p = np.where(mask, 0.0, p)
        p = p / p.sum()
    return Joint(names, p.reshape(shape))


# --------------------------------------------------------------------------
# 3. 主張の検定
# --------------------------------------------------------------------------
@dataclass
class RelationReport:
    lhs: str
    rhs: str
    rel: str
    trials: int
    tol: float
    violations: int = 0
    worst_residual: float = 0.0
    max_abs_residual: float = 0.0
    worst_joint: Joint | None = None
    worst_values: tuple[float, float] = (0.0, 0.0)

    @property
    def held(self) -> bool:
        return self.violations == 0

    def summary(self) -> str:
        head = "HELD" if self.held else "VIOLATED"
        s = (
            f"[{head}] {self.lhs} {self.rel} {self.rhs}\n"
            f"  試行 {self.trials}, 違反 {self.violations}, tol={self.tol:g}\n"
            f"  最悪残差 (lhs-rhs) = {self.worst_residual!r}, "
            f"|残差| の最大 = {self.max_abs_residual!r}"
        )
        if not self.held and self.worst_joint is not None:
            s += (
                f"\n  反例での lhs = {self.worst_values[0]!r}, rhs = {self.worst_values[1]!r}\n"
                + self.worst_joint.describe()
            )
        return s


def test_relation(
    lhs: str | LinInfo,
    rhs: str | LinInfo,
    sampler: Callable[[], Joint],
    rel: str = "==",
    trials: int = 2000,
    tol: float = 1e-9,
    units: str = "nats",
) -> RelationReport:
    """`sampler()` が返す同時分布の上で主張 `lhs rel rhs` を叩く。

    `rel` は `"=="` / `"<="` / `">="`。違反が 1 つでも出たら、最悪の反例
    (残差が最も大きいもの) を `worst_joint` に残す。
    """
    L = parse(lhs) if isinstance(lhs, str) else lhs
    R = parse(rhs) if isinstance(rhs, str) else rhs
    rep = RelationReport(str(lhs), str(rhs), rel, trials, tol)
    worst = -np.inf
    for _ in range(trials):
        J = sampler()
        lv, rv = L.evaluate(J, units), R.evaluate(J, units)
        d = lv - rv
        rep.max_abs_residual = max(rep.max_abs_residual, abs(d))
        if rel == "==":
            bad, score = abs(d) > tol, abs(d)
        elif rel == "<=":
            bad, score = d > tol, d
        elif rel == ">=":
            bad, score = d < -tol, -d
        else:
            raise ValueError(f"未知の関係 {rel!r}")
        if bad:
            rep.violations += 1
        if score > worst:
            worst, rep.worst_residual = score, d
            rep.worst_joint, rep.worst_values = J, (lv, rv)
    return rep


# --------------------------------------------------------------------------
# 4. 補助変数上の最大化
# --------------------------------------------------------------------------
def softmax(theta: np.ndarray, axis: int = -1) -> np.ndarray:
    t = np.asarray(theta, dtype=float)
    t = t - t.max(axis=axis, keepdims=True)
    e = np.exp(t)
    return e / e.sum(axis=axis, keepdims=True)


@dataclass
class OptReport:
    best: float
    best_x: np.ndarray
    values: list[float] = field(default_factory=list)
    restarts: int = 0
    tol: float = 1e-8

    @property
    def n_within_tol(self) -> int:
        return sum(1 for v in self.values if self.best - v <= self.tol)

    @property
    def spread(self) -> tuple[float, float]:
        return (min(self.values), max(self.values)) if self.values else (0.0, 0.0)

    def summary(self) -> str:
        lo, hi = self.spread
        return (
            f"best = {self.best!r}  (再スタート {self.restarts} 回、"
            f"うち best から {self.tol:g} 以内に着地 {self.n_within_tol} 回、"
            f"着地値の範囲 [{lo!r}, {hi!r}])"
        )


def maximize(
    f: Callable[[np.ndarray], float],
    dim: int,
    rng: np.random.Generator,
    restarts: int = 40,
    scale: float = 2.0,
    method: str = "Nelder-Mead",
    options: dict | None = None,
    seeds: Sequence[np.ndarray] = (),
    tol: float = 1e-8,
) -> OptReport:
    """多点再スタートの局所最適化で `f` を最大化する。

    **返るのは局所最適の中の最良値であって最大値の証明ではない**。判定に使うときは
    `OptReport.summary()` の再スタート数と着地値の散らばりを必ず一緒に報告すること。
    """
    opts = {"maxiter": 20000, "maxfev": 20000, "xatol": 1e-10, "fatol": 1e-12}
    if options:
        opts.update(options)
    best, best_x, values = -np.inf, None, []
    starts = [np.asarray(s, dtype=float) for s in seeds]
    starts += [rng.normal(0.0, scale, dim) for _ in range(restarts)]
    for x0 in starts:
        res = minimize(lambda z: -f(z), x0, method=method, options=opts)
        val = -float(res.fun)
        values.append(val)
        if val > best:
            best, best_x = val, res.x
    return OptReport(best, best_x, values, len(starts), tol)


def local_max_certificate(
    f: Callable[[np.ndarray], float],
    p: np.ndarray,
    rng: np.random.Generator,
    trials: int = 2000,
    eps: Sequence[float] = (1e-1, 1e-2, 1e-3, 1e-4, 1e-5),
    dirichlet: float = 1.0,
    directions: Sequence[np.ndarray] = (),
) -> tuple[float, np.ndarray | None, float]:
    """`p` (確率ベクトル) が `f` の局所最大かを摂動 pε = (1−ε)p + ε s で叩く。

    `s` はランダムな (または `directions` で与えた) 同じ台空間上の分布。
    返り値 `(最大増分, 増分を出した s, その ε)`。増分が 0 以下なら**この摂動族の範囲で**
    局所最大。増分が正なら局所最大ですらない。
    """
    p = np.asarray(p, dtype=float).ravel()
    base = f(p)
    n = p.size
    best_gain, best_s, best_eps = -np.inf, None, 0.0
    cand = [np.asarray(s, dtype=float).ravel() for s in directions]
    cand += [rng.dirichlet(np.full(n, dirichlet)) for _ in range(trials)]
    for s in cand:
        for e in eps:
            gain = f((1.0 - e) * p + e * s) - base
            if gain > best_gain:
                best_gain, best_s, best_eps = gain, s, e
    return best_gain, best_s, best_eps


# --------------------------------------------------------------------------
# 5. selftest
# --------------------------------------------------------------------------
def _approx(a: float, b: float, tol: float = 1e-12) -> bool:
    return abs(a - b) <= tol


def selftest() -> None:
    rng = np.random.default_rng(20260801)
    fails: list[str] = []

    def check(name: str, cond: bool, detail: str = "") -> None:
        print(f"  [{'OK ' if cond else 'NG '}] {name}" + (f"  {detail}" if detail else ""))
        if not cond:
            fails.append(name)

    print("=== 1. 記号展開 (恒等式は係数の相殺で証明される) ===")
    ok, res = prove_identity("I(A;B,C)", "I(A;B) + I(A;C|B)")
    check("連鎖則 I(A;B,C) = I(A;B) + I(A;C|B)", ok, repr(res))
    ok, res = prove_identity("H(A,B)", "H(A) + H(B|A)")
    check("連鎖則 H(A,B) = H(A) + H(B|A)", ok, repr(res))
    ok, res = prove_identity("I(A;B)", "I(A;B|C)")
    check("偽の主張 I(A;B) = I(A;B|C) は証明されない", not ok, repr(res))
    ok, res = prove_identity("2*I(A;B) - I(A;B)", "I(A;B)")
    check("係数の算術 2I - I = I", ok, repr(res))

    print("=== 2. 分布の評価 (閉形式との照合) ===")
    n = 5
    J = Joint(["X"], np.full(n, 1.0 / n))
    check(f"一様分布 H(X) = log {n}", _approx(J.eval("H(X)"), float(np.log(n))),
          f"{J.eval('H(X)')!r} vs {float(np.log(n))!r}")
    check("bit 単位", _approx(J.eval("H(X)", units="bits"), float(np.log2(n))))
    # BSC: I(X;Y) = log2 - h(e) nat
    e = 0.17
    bn = BayesNet()
    bn.root("X", 2, pmf=[0.5, 0.5])
    bn.add("Y", 2, ["X"], kernel=[[1 - e, e], [e, 1 - e]])
    JB = bn.build()
    hb = -e * np.log(e) - (1 - e) * np.log(1 - e)
    check("BSC の I(X;Y) = log2 - h(e)",
          _approx(JB.eval("I(X;Y)"), float(np.log(2) - hb)),
          f"{JB.eval('I(X;Y)')!r} vs {float(np.log(2) - hb)!r}")

    print("=== 3. 構造制約が DAG から出ること ===")
    bn = BayesNet()
    bn.root("A", 3).root("B", 4)
    JI = bn.build(rng)
    check("独立 root: I(A;B) = 0", _approx(JI.eval("I(A;B)"), 0.0, 1e-13))
    bn = BayesNet()
    bn.root("A", 3)
    bn.add("X", 2, ["A"])
    bn.add("C", 4, ["X"])
    JM = bn.build(rng)
    check("Markov 連鎖 A-X-C: I(A;C|X) = 0", _approx(JM.eval("I(A;C|X)"), 0.0, 1e-13),
          f"I(A;C) = {JM.eval('I(A;C)')!r} (非退化の確認)")
    check("非退化 (I(A;C) > 0)", JM.eval("I(A;C)") > 1e-3)
    bn = BayesNet()
    bn.root("A", 2).root("B", 2)
    bn.deterministic("F", 2, ["A", "B"], lambda a, b: a & b)
    JD = bn.build(rng)
    check("決定論的ノード: H(F|A,B) = 0", _approx(JD.eval("H(F|A,B)"), 0.0, 1e-13))
    # メモリレス積構造: 同一カーネル T(y,z|x) を 2 回別々に使う (出力は結合していてよい)
    T = rng.dirichlet(np.ones(4), size=2).reshape(2, 2, 2)
    bn = BayesNet()
    bn.root("A", 2).root("B", 2)
    bn.deterministic("X1", 2, ["A", "B"], lambda a, b: a ^ b)
    bn.deterministic("X2", 2, ["A", "B"], lambda a, b: a | b)
    bn.add(("Y1", "Z1"), (2, 2), ["X1"], kernel=T)
    bn.add(("Y2", "Z2"), (2, 2), ["X2"], kernel=T)
    JP = bn.build(rng)
    check("メモリレス: I(Y1,Z1;Y2,Z2|A,B) = 0",
          _approx(JP.eval("I(Y1,Z1;Y2,Z2|A,B)"), 0.0, 1e-13))
    check("結合出力: I(Y1;Z1|X1) > 0 (積 BC でないこと)", JP.eval("I(Y1;Z1|X1)") > 1e-4,
          f"{JP.eval('I(Y1;Z1|X1)')!r}")

    print("=== 4. test_relation ===")
    rep = test_relation("I(A;B,C)", "I(A;B) + I(A;C|B)",
                        lambda: random_joint({"A": 2, "B": 3, "C": 2}, rng),
                        trials=200)
    check("真の恒等式は違反 0", rep.held, f"|残差|max = {rep.max_abs_residual:.3e}")
    rep = test_relation("I(A;B)", "I(A;B|C)",
                        lambda: random_joint({"A": 2, "B": 2, "C": 2}, rng),
                        trials=200)
    check("偽の主張は違反が出る", not rep.held, f"違反 {rep.violations}/200")

    print("=== 5. maximize / local_max_certificate ===")
    # H(p) を 3 元単体上で最大化 -> log 3 で一意 (凹なので局所 = 大域)
    opt = maximize(lambda t: _entropy_nats(softmax(t)), 3, rng, restarts=12)
    check("max H(p) = log 3", _approx(opt.best, float(np.log(3)), 1e-9), opt.summary())
    # 局所最大の判定: 一様分布は H の最大点、尖った点はそうでない
    g0, _, _ = local_max_certificate(_entropy_nats, np.full(3, 1 / 3), rng, trials=200)
    check("一様分布は H の局所最大 (増分 <= 0)", g0 <= 1e-12, f"最大増分 {g0:.3e}")
    g1, _, _ = local_max_certificate(_entropy_nats, np.array([0.8, 0.1, 0.1]), rng, trials=200)
    check("尖った点は局所最大でない (増分 > 0)", g1 > 1e-6, f"最大増分 {g1:.3e}")

    print()
    if fails:
        raise SystemExit(f"selftest 失敗: {fails}")
    print("selftest: 全項目 OK")


if __name__ == "__main__":
    selftest()
