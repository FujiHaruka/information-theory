# Ch.14 後継 scope「Ω 自体の非計算性」 Mathlib/in-tree API 在庫

> **親計画**: [`kolmogorov-w2-moonshot-plan.md`](kolmogorov-w2-moonshot-plan.md) §Phase P9 / §settled facts /
> §residual slug 方針 (park slug `plan:kolmogorov-w2-omega-noncomputable`)。
> 兄弟在庫: [`kolmogorov-w2-inventory.md`](kolmogorov-w2-inventory.md) / [`kolmogorov-w2-p10-inventory.md`](kolmogorov-w2-p10-inventory.md)。
> **調査日 2026-07-25 / 対象機械 = `prefixUniversalEval` (`PrefixMachine.lean:172`) / gateway atom は
> `4efc230d` で着地済 (`PrefixComputability.lean` 82 行、両定理 sorryAx-free)。**
> 本ファイルは在庫のみ。plan 起票と実装は別エージェントの担当。

## 一行サマリ

**Chaitin 論法を通すために要る Mathlib 側の道具は 26/26 = 100% 既存**で、**genuine な Mathlib 壁は 0 件**。
不足しているのは「計算可能実数」という**語彙だけ** (`ComputableReal` は識別子として存在しない = loogle
`unknown identifier`) で、これは *hard* ではなく *big* (定義の選択)。⟹ 親 plan の
「`wall:` ではなく `plan:`」判定は**追認**。自作は **定義 1 本 + 橋渡し 7 ブロック / 見積 400–650 行**。

**ただし親 plan の loogle-neg claim は「追認 + 増強」が要る** — Mathlib に無いのは `ComputableReal` だけではなく、
**ℚ と ℤ の `Primrec` API が丸ごと 0 件**である (`Mathlib/Computability/` 配下に `Rat`/`Int` の語が 1 度も
出てこない)。`Primcodable ℚ` は `Denumerable ℚ` 経由で**インスタンスとしては存在する**が、その符号化は
`Denumerable.ofEncodableOfInfinite` = 「`Set.range encode` の順序同型」という不透明物なので、ℚ 上の四則の
`Primrec` 性は事実上証明不能。⟹ **近似列は ℚ ではなく ℕ (二進有理数の分子) で建てるしかない**。これが本在庫で
最も事故りやすい発見であり、定義 (§C) と型選択 (§D) の両方を決めてしまう。

---

## 到達形 (推奨) と証明骨格

```lean
/-- 非負実数の計算可能性 (二進有理近似列、分子は ℕ)。`ℝ≥0∞` 上でそのまま述べる。 -/
def IsComputableENNReal (x : ℝ≥0∞) : Prop :=
  ∃ a : ℕ → ℕ, Computable a ∧ ∀ n : ℕ,
    x ≤ (a n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n + (2 : ℝ≥0∞)⁻¹ ^ n ∧
    (a n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n ≤ x + (2 : ℝ≥0∞)⁻¹ ^ n

@[entry_point]
theorem chaitinOmega_not_computable : ¬ IsComputableENNReal chaitinOmega
```

証明戦略 (pseudo-Lean、**引き算を一切使わない加法形**で組む):

```
-- 1. 下からの計算可能近似 (Ω_t = 時刻 t までに停止した長さ ≤ t の program の質量)
omegaApprox t := ∑ p ∈ (allBitStrings≤ t).filter (fun p ↦ (prefixEvaln t p).isSome), (2:ℝ≥0∞)⁻¹ ^ p.length
omegaApprox_le      : omegaApprox t ≤ chaitinOmega              ⇐ ENNReal.sum_le_tsum  (evaln_sound)
omegaApprox_iSup    : ⨆ t, omegaApprox t = chaitinOmega         ⇐ ENNReal.tsum_eq_iSup_sum' (evaln_complete)
omegaApproxNum_comp : Computable omegaApproxNum                 ⇐ primrec_evaln + parseUnary_primrec + list_*
-- 2/3. 精度 2^{-(n+2)} の近似 a(n+2) から t を「探索」する (比較は全部 ℕ の dyadic 比較)
∃ t, chaitinOmega < omegaApprox t + (2:ℝ≥0∞)⁻¹^(n+1)            ⇐ ENNReal.sub_lt_self + lt_iSup_iff
searchTime n := Nat.find (上の存在)   ,  Computable searchTime  ⇐ Computable.find (RE.lean:177)
⟹ chaitinOmega < omegaApprox (searchTime n) + (2:ℝ≥0∞)⁻¹ ^ n
-- 4. その t 以降、長さ ≤ n の未停止 program は永久に停止しない (質量が上限を超える)
p ∉ H t ∧ |p| ≤ n ∧ Dom p → omegaApprox t + (2:ℝ≥0∞)⁻¹^|p| ≤ chaitinOmega  ⇐ Finset.sum_insert + sum_le_tsum
                                                                 ⟹ 矛盾 (2^{-|p|} ≥ 2^{-n})
-- 5. ⟹ 停止性が決定可能 ⟹ gateway atom と矛盾
ComputablePred (fun p ↦ (prefixUniversalEval p).Dom)             -- p ↦ (prefixEvaln (searchTime |p|) p).isSome
exact prefixUniversalEval_dom_not_computablePred ‹…›             -- PrefixComputability.lean:66
```

---

## API 在庫テーブル

`file:line` は Mathlib は `.lake/packages/mathlib/` 配下、in-tree は repo ルート相対。
**署名は verbatim** (`[...]` 型クラス前提を含め省略しない)。

### §A. bounded evaluation (`evaln`) — 論法ステップ 1 の生命線

すべて `Mathlib/Computability/PartrecCode.lean`、名前空間 `Nat.Partrec.Code`。
**特筆: この群は `[...]` 型クラス前提を 1 つも持たない** (全部 ℕ / `Code` / `Option ℕ` の具体型)。

| 概念 | Mathlib API (verbatim) | file:line | 状態 | 本 scope での扱い |
|---|---|---|---|---|
| 有界評価の定義 | `def evaln : ℕ → Code → ℕ → Option ℕ` (引数: `k : ℕ` explicit / `c : Code` explicit / `n : ℕ` explicit、結論形 `Option ℕ`) | `Mathlib/Computability/PartrecCode.lean:568` | ✅ 既存 | `prefixEvaln` の中核。`decodePayload` の bounded 版をこれで作る |
| 入力上界 | `theorem evaln_bound : ∀ {k c n x}, x ∈ evaln k c n → n < k` | `:604` | ✅ 既存 | 「t を上げれば入力も含まれる」の議論に使用 |
| **単調性** | `theorem evaln_mono : ∀ {k₁ k₂ c n x}, k₁ ≤ k₂ → x ∈ evaln k₁ c n → x ∈ evaln k₂ c n` | `:612` | ✅ 既存 | **`omegaApprox` の単調増加の源**。`Option` の `∈` で保存される (`x ∈ o` = `o = some x`) |
| 健全性 | `theorem evaln_sound : ∀ {k c n x}, x ∈ evaln k c n → x ∈ eval c n` | `:651` | ✅ 既存 | `Ω_t ≤ Ω` (下からの近似であること) |
| 完全性 | `theorem evaln_complete {c n x} : x ∈ eval c n ↔ ∃ k, x ∈ evaln k c n` | `:690` | ✅ 既存 | `⨆ t, Ω_t = Ω` の cofinality。停止時刻 `Nat.find` の存在証明 |
| **`evaln` の原始帰納性** | `theorem primrec_evaln : Primrec fun a : (ℕ × Code) × ℕ => evaln a.1.1 a.1.2 a.2` | `:922` | ✅ **既存** | ステップ 1 の計算可能性の生命線。**存在する** — 「無ければその旨明示」の条件は不発 |
| `eval` の rfindOpt 表示 | `theorem eval_eq_rfindOpt (c n) : eval c n = Nat.rfindOpt fun k => evaln k c n` | `:989` | ✅ 既存 | `prefixEvaln` ↔ `prefixUniversalEval` の橋の雛形 |
| `eval` の partrec 性 | `theorem eval_part : Partrec₂ eval` | `:994` | ✅ 既存 | in-tree `decodePayload_partrec` が既に消費済 |

**注意 (`evaln` の意味論)**: `evaln k c n` は「`k` ステップ以内」ではなく「**計算途中で `k` 以上の数に出会ったら
失敗**」(:564–566 の docstring 原文)。ガードは `guard (n ≤ k)` なので、`k` は時間とサイズの両方を兼ねる**単一の
予算パラメータ**である。⟹ Ω_t の「時刻 t」は `evaln t` の `t` をそのまま使えばよく、時間とサイズを別々に
持つ必要はない (定義が 1 パラメータで済む = 設計上の得)。

### §B. 有理数・整数と計算可能性 — **ここが最大の落とし穴**

| 概念 | Mathlib API (verbatim) | file:line | 状態 | 本 scope での扱い |
|---|---|---|---|---|
| `Encodable ℚ` | `instance : Encodable ℚ := Encodable.ofEquiv (Σ n : ℤ, { d : ℕ // 0 < d ∧ n.natAbs.Coprime d }) …` | `Mathlib/Data/Rat/Encodable.lean:23` | ✅ 既存 | 使わない |
| `Denumerable ℚ` | `instance instDenumerable : Denumerable ℚ := ofEncodableOfInfinite ℚ` | `Mathlib/Data/Rat/Denumerable.lean:30` | ✅ 既存 | 使わない (下記理由) |
| `Primcodable ℚ` (派生) | `instance (priority := 10) ofDenumerable (α) [Denumerable α] : Primcodable α` | `Mathlib/Computability/Primrec/Basic.lean:139` | ✅ **インスタンスは存在** | **使わない**。符号化が `Denumerable.ofEncodableOfInfinite` = `Nat.Subtype.denumerable (Set.range encode)` (`Mathlib/Logic/Denumerable.lean:316`) 経由の**不透明な順序同型**で、四則の `Primrec` 性が事実上証明不能 |
| ℚ 上の `Primrec` 四則 / 比較 | — | — | ❌ **不在 (Found 0)** | `Primrec.ratAdd` 等は**存在しない**。`Mathlib/Computability/` 配下に `ℚ`/`Rat` の語が 1 度も出ない |
| ℤ 上の `Primrec` 四則 / 比較 | — | — | ❌ **不在 (Found 0)** | 同上。`Mathlib/Computability/Primrec/` に `Int` を含むファイルが 0 |
| ℕ 上の `Primrec` 四則 | `theorem nat_add : Primrec₂ ((· + ·) : ℕ → ℕ → ℕ)` / `nat_sub` / `nat_mul` / `nat_div` / `nat_mod` | `Mathlib/Computability/Primrec/Basic.lean:593 / 596 / 599 / 710 / 728` | ✅ 既存 | **近似列は全部これで組む** |
| ℕ 上の `Primrec` 比較 | `theorem nat_le : PrimrecRel ((· ≤ ·) : ℕ → ℕ → Prop)` / `theorem nat_lt : PrimrecRel ((· < ·) : ℕ → ℕ → Prop)` / `protected theorem eq : PrimrecRel (@Eq α)` | `:610 / :660 / :651` | ✅ 既存 | dyadic 比較の決定手続き |
| ℕ 上の `min`/`max` | `theorem nat_min : Primrec₂ (@min ℕ _)` / `theorem nat_max : Primrec₂ (@max ℕ _)` | `:617 / :620` | ✅ 既存 | 共通分母 `max t (n+2)` を取る |
| **ℕ の冪** | `theorem pow : Nat.Primrec (unpaired (· ^ ·))` | `:114` | ⚠️ **低レベルのみ** | 高レベル `Primrec₂ ((·^·) : ℕ → ℕ → ℕ)` は**不在** (loogle 0-hit)。必要なのは `Primrec fun n : ℕ ↦ 2 ^ n` だけなので `Primrec.nat_iterate` で 4 行自作 (in-tree `primrec_replicate_true` @ `PrefixComputability.lean:27` が同型の雛形) |

**代替の可否 (ブリーフ §B の問い)**: 「ℚ が使えない場合の代替」— **二進有理数 `m / 2^k` に限る一択**。
ℕ×ℕ ペアで一般の有理数を表す案は、約分・比較で `Nat.gcd` の `Primrec` 性が要り (Mathlib にある: `Nat.gcd` は
`Primrec` ではあるが `Primrec.nat_gcd` という名前の補題は無く自作)、しかも Chaitin 論法は**分母が常に 2 冪**なので
一般有理数を持ち込む理由が無い。⟹ **分母を `2^n` に固定し、分子 `ℕ` だけを計算可能対象にする**。

### §C. 計算可能実数の定式化 (自前定義になる部分)

#### C-1. 親 plan の loogle-neg claim の再検証 — **追認 (overturn せず)**

| クエリ | 出力 (verbatim) |
|---|---|
| `Computable, Real` | `Found 0 declarations mentioning Real and Computable.` |
| `Primrec, Real` | `Found 0 declarations mentioning Real and Primrec.` |
| `ComputableReal` | `unknown identifier 'ComputableReal'` |
| `Computable, Rat` | `Found 0 declarations mentioning Rat and Computable.` |
| `Primrec, Rat` | `Found 0 declarations mentioning Rat and Primrec.` |
| `Primrec, Int` | `Found 0 declarations mentioning Int and Primrec.` |
| `\|- Computable (_ : ℕ → ℚ)` (二段階 conclusion-shape) | `Found 0 declarations mentioning Primcodable.ofDenumerable, Rat, Rat.instDenumerable, Nat, Denumerable.nat, and Computable.` / `Of these, 0 match your pattern(s).` |

テキスト検索 (loogle は識別子しか見ないため補完):

- `rg -ni "computable real\|computable analysis\|computably approximab\|recursively enumerable real" Mathlib/` → **0 hit**
- `rg -ni "halting probability\|left-c\.e\.\|Specker\|Chaitin\|Martin-L\|Kolmogorov complexity\|randomness" Mathlib/` → **アルゴリズム的ランダムネス関連 0 hit** (`Mathlib/Control/Random.lean` 等の乱数生成の 5 件のみ)
- `rg -n "ℚ\|Rat" Mathlib/Computability/` → **0 hit**
- `rg -n "Int" Mathlib/Computability/Primrec/` → **0 file**
- in-project: `rg -n "evaln\|IsComputable\|ComputableReal\|omegaApprox\|rfindOpt" InformationTheory/` → **0 hit** (`cause:loogle-blind` ガード通過。同家系にも近縁物は無い)

**判定**: claim は**追認**。ただし「Mathlib に計算可能実数が無い」より強く「**計算可能解析の足場となる ℚ/ℤ の
`Primrec` API 自体が無い**」が実態で、これは定義の形を強制する (§C-2)。近縁で使えるものの評価:

| 近縁候補 | file:line | 使えるか |
|---|---|---|
| `CauSeq` / `Real.mk` | `Mathlib/Data/Real/Basic.lean` 他 | ✖ **使わない**。計算可能性は `CauSeq` の**項の計算可能性**の話で、`CauSeq` 側は何も与えない。むしろ `Primcodable (CauSeq ℚ abs)` が無いので障害 |
| `Nat.rfind` / `Nat.rfindOpt` | `Mathlib/Computability/Partrec.lean:91 / :134` | △ 直接は不要 (`Computable.find` の方が使いやすい)。`rfindOpt_mono` (`:151`) は `prefixEvaln` の単調探索の雛形 |
| `Computable.find` | `Mathlib/Computability/RE.lean:177` | ○ **本命** (§E 表に verbatim) |
| `Metric` の近似列 | — | ✖ 位相の話であって計算可能性を与えない |

#### C-2. 自前定義 3 案の比較

| 案 | 定義形 (推奨実装) | Chaitin 論法で楽になる点 | 困難になる点 |
|---|---|---|---|
| **(i) 計算可能二進有理近似列 + 誤差 `2^{-n}`** ★推奨 | `∃ a : ℕ → ℕ, Computable a ∧ ∀ n, x ≤ a n * (2⁻¹)^n + (2⁻¹)^n ∧ a n * (2⁻¹)^n ≤ x + (2⁻¹)^n` | ステップ 2 が定義そのもの。比較が全部 ℕ の dyadic 比較に落ち `Primrec.nat_lt` で決定可能。ℚ/ℤ の欠落 API を一切踏まない | 「標準の計算可能実数の定義と同値か」の説明責任 (下記 ⚠️)。誤差幅の取り方を 1 回間違うと**偽より強い命題**になる |
| (ii) 二進展開の計算可能性 | `∃ b : ℕ → Bool, Computable b ∧ x = ∑' n, (if b n then (2⁻¹)^(n+1) else 0)` | 定義が短い。ステップ 3 の近似も部分和で取れる | **二進展開は二進有理点で一意でない** ⟹ Ω が二進有理でないこと (無理数性) を別途要する。Ω の無理数性は本 scope の外 ⟹ **この案は隠れ依存を作る** |
| (iii) Dedekind 切断の決定可能性 | `ComputablePred (fun q : ℚ ↦ (q : ℝ) < x)` | 述語 1 本で終わり定義が最短 | **`Primcodable ℚ` の符号化が不透明で `Primrec` 補題ゼロ** (§B) ⟹ `ComputablePred` を**消費**する側 (この述語から ℕ 上の何かを作る) が組めない。さらに古典的にも「切断が決定可能 ⟺ 計算可能」は x が有理のとき成り立たない ⟹ **偽より強い命題**になる |

**⚠️ (i) で最も事故る点 — 誤差幅を「厳密な床関数」にしてはいけない**:
`a n * 2^{-n} ≤ x ≤ (a n + 1) * 2^{-n}` (幅ちょうど `2^{-n}` の両側挟み) は、**標準の計算可能実数から導けない**。
x が格子点 `k·2^{-n}` の近傍にあるとき `a n` を `k-1` と `k` のどちらに出すかは `x - k·2^{-n}` の符号判定を要し、
計算可能実数では決定不能だからである。⟹ この形で `¬` を証明しても、**得られるのは「厳密床が計算可能でない」
という弱い命題**で、教科書の「Ω は計算可能実数でない」を主張したことにならない (name laundering 相当)。
上の (i) の推奨形 (加法的に `+ (2⁻¹)^n` を両辺に置く = `|x - a n·2^{-n}| ≤ 2^{-n}`) なら、標準の
「計算可能有理近似列 `q` で `|x - q n| ≤ 2^{-n}`」から `a n := round (q m · 2^n)` (m 十分大) で**導ける** ⟹
`¬(i)` は標準の非計算可能性を**含意する**方向の、より強い定理になる。**この向きの確認を実装前に 1 回通すこと**。

**⚠️ ℝ 版を建てるなら符号の縮退に注意**: `IsComputableReal (x : ℝ)` を分子 ℕ で定義すると `x < 0` で恒偽に
なり、`¬IsComputableReal` が負数で**自明に真** = 退化定義の濫用に見える。⟹ ℝ 版を出すなら
(a) `ℝ≥0` 上で定義する / (b) 定義に `0 ≤ x` を含める / (c) 分子を ℤ にする (ただし §B より ℤ の `Primrec` API が
無いので **証明側が詰む**) のいずれか。**推奨は ℝ≥0∞ ネイティブの `IsComputableENNReal` 1 本**で、
ℝ 版は出さない (出すなら `chaitinOmega.toReal` 用の橋補題として §退避候補 の任意項目)。

### §D. 型の選択 (ℝ≥0∞ vs ℝ vs ℚ)

**結論: `chaitinOmega` を `ℝ≥0∞` のまま扱い、`.toReal` に落とさない。** ℝ≥0∞ の truncated subtraction は
**論法を加法形で書けば 1 箇所しか現れず、その 1 箇所は既存補題で処理できる**ため、ℝ へ落とす境界は不要。

| 概念 | Mathlib API (verbatim) | file:line | 状態 | 本 scope での扱い |
|---|---|---|---|---|
| 有限部分和の上限表示 | `protected theorem tsum_eq_iSup_sum : ∑' a, f a = ⨆ s : Finset α, ∑ a ∈ s, f a` (variable: `{f : α → ℝ≥0∞}`、型クラス前提なし) | `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean:71` | ✅ 既存 | in-tree で使用済 (`PrefixFree.tsum_inv_two_pow_length_le_one`) |
| **添字列版 (単調収束)** | `protected theorem tsum_eq_iSup_sum' {ι : Type*} (s : ι → Finset α) (hs : ∀ t, ∃ i, t ⊆ s i) : ∑' a, f a = ⨆ i, ∑ a ∈ s i, f a` | `:74` | ✅ 既存 | **`⨆ t, Ω_t = Ω` はこれ 1 本**。`hs` = 任意の有限集合が或る `H t` に入る (cofinality) |
| 有限部分和 ≤ tsum | `protected theorem sum_le_tsum {f : α → ℝ≥0∞} (s : Finset α) : ∑ x ∈ s, f x ≤ ∑' x, f x` | `:118` | ✅ 既存 | `Ω_t ≤ Ω` と**ステップ 4 の質量超過**の両方 |
| 単項下界 | `protected theorem le_tsum (a : α) : f a ≤ ∑' a, f a` | `:146` | ✅ 既存 | in-tree `chaitinOmega_pos` で使用済 |
| `⨆` からの取り出し | `theorem lt_iSup_iff : a < iSup f ↔ ∃ i, a < f i` (`variable [CompleteLinearOrder α] {a b l : α} {f : ι → α}`) | `Mathlib/Order/CompleteLattice/Defs.lean:314` | ✅ 既存 | ステップ 3 の t の存在 |
| **truncated 引き算の唯一の登場箇所** | `protected theorem sub_lt_self (ha : a ≠ ∞) (ha₀ : a ≠ 0) (hb : b ≠ 0) : a - b < a` | `Mathlib/Data/ENNReal/Operations.lean:391` | ✅ 既存 | `Ω - ε < Ω` を作って `lt_iSup_iff` に食わせる。**前提 3 つは in-tree で全部証明済** (`chaitinOmega_ne_top:64` / `chaitinOmega_pos:55` / `ENNReal.pow_pos`) |
| 引き算 → 加法形への復帰 | `protected theorem sub_lt_iff_lt_right (hb : b ≠ ∞) (hab : b ≤ a) : a - b < c ↔ a < c + b` | `:379` | ✅ 既存 | `Ω - ε < Ω_t ↔ Ω < Ω_t + ε` |
| 同 (左形) | `protected theorem sub_lt_of_lt_add (hac : c ≤ a) (h : a < b + c) : a - c < b` | `:376` | ✅ 既存 | 予備 |
| 逆数の冪 | `protected theorem inv_pow : ∀ {a : ℝ≥0∞} {n : ℕ}, (a ^ n)⁻¹ = a⁻¹ ^ n` | `Mathlib/Data/ENNReal/Inv.lean:92` | ✅ 既存 | 分子↔ℝ≥0∞ の橋 |
| 約分 | `protected theorem mul_inv_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a * a⁻¹ = 1` | `:102` | ✅ 既存 | `2^(t-ℓ) · (2⁻¹)^t = (2⁻¹)^ℓ` (ℓ ≤ t) の橋。**`≠ 0` と `≠ ⊤` の両側条件が要る** |
| 割り算の不等式 | `protected theorem le_div_iff_mul_le (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) : a ≤ c / b ↔ a * b ≤ c` | `:363` | ✅ 既存 | 使わない設計を推奨 (下記) |
| ℝ へ落とす場合 | `theorem toReal_le_toReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toReal ≤ b.toReal ↔ a ≤ b` / `lemma toReal_sub_of_le (hba : b ≤ a) (ha : a ≠ ∞) : (a - b).toReal = a.toReal - b.toReal` | `Mathlib/Data/ENNReal/Real.lean:61` / `Mathlib/Data/ENNReal/Operations.lean:433` | ✅ 既存 | **不使用を推奨**。使うのは ℝ 版 headline を追加する場合のみ |

**設計原則 (Mathlib-shape-driven)**: 割り算 `/` を一切書かない。`Ω_t` は `∑ p ∈ H t, (2:ℝ≥0∞)⁻¹ ^ p.length`
(既存 `chaitinOmega` の被加数と**同一形**) で定義し、ℕ 分子 `omegaApproxNum t` との関係は
`omegaApprox t = (omegaApproxNum t : ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ t` という**1 本の橋補題**に閉じ込める。
これで `ENNReal.mul_inv_cancel` の副条件は橋補題の中 (~15 行) だけに局所化される。

### §E. 有限部分和と列挙

| 概念 | API (verbatim) | file:line | 状態 | 本 scope での扱い |
|---|---|---|---|---|
| 「長さ ≤ n の `List Bool` 全体」 | — | — | ❌ **不在** | **自作** (下記)。`List.sublistsLen` は「与えられたリストの長さ n の部分列」であって別物 |
| 汎用の断面列挙 | `theorem mem_sections {L : List (List α)} {f} : f ∈ sections L ↔ Forall₂ (· ∈ ·) f L` / `theorem mem_sections_length {L : List (List α)} {f} (h : f ∈ sections L) : length f = length L` | `Mathlib/Data/List/Sections.lean:25 / :39` | ✅ 既存 | △ `List.sections (List.replicate n [false, true])` がちょうど長さ n のビット列全体。**ただし `Primrec (List.sections)` は不在** ⟹ 採らず、`Primrec.list_flatMap` での再帰定義を自作する方が短い |
| `Finset` の計算可能性 | — | — | ❌ **不在** (`Primcodable (Finset _)` → Found 0) | **計算可能性の層は `List` で組み、`Finset` は和の評価にだけ使う** (P10 在庫と同じ罠) |
| リスト連結・写像・平坦化の Primrec | `theorem list_append : Primrec₂ ((· ++ ·) : List α → List α → List α)` / `theorem list_map {f : α → List β} {g : α → β → σ} (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).map (g a)` / `theorem list_flatMap {f : α → List β} {g : α → β → List σ} (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).flatMap (g a)` | `Mathlib/Computability/Primrec/List.lean:219 / :226 / :240` | ✅ 既存 | 列挙器の Primrec 性 |
| リスト filter / 畳み込み | `theorem listFilter (hf : PrimrecPred p) : Primrec fun L ↦ List.filter (p ·) L` / `theorem list_foldl {f : α → List β} {g : α → σ} {h : α → σ × β → σ}` | `:260 / :151` | ✅ 既存 | 停止判定でのふるい + ℕ 分子の総和 |
| `List.range` | `theorem list_range : Primrec List.range` | `:232` | ✅ 既存 | 長さ 0..t のループ |
| ℕ の反復 | `theorem nat_iterate {f : α → ℕ} {g : α → β} {h : α → β → β} (hf : Primrec f) (hg : Primrec g)` | `Mathlib/Computability/Primrec/Basic.lean:539` | ✅ 既存 | `2 ^ n` と列挙器。in-tree 雛形 = `primrec_replicate_true` |
| `Option` 系 Primrec | `theorem option_bind {f : α → Option β} {g : α → β → Option σ} (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).bind (g a)` / `theorem option_isSome : Primrec (@Option.isSome α)` / `theorem option_casesOn {o : α → Option β} {f : α → σ} {g : α → β → σ} (ho : Primrec o)` | `:555 / :580 / :544` | ✅ 既存 | `prefixEvaln` の組み立てと停止判定 |
| `Denumerable.ofNat` の Primrec | `protected theorem ofNat (α) [Denumerable α] : Primrec (ofNat α)` | `:233` | ✅ 既存 | `ofNat Code idx`。in-tree `payloadDispatch_computable` で使用済 |
| 条件分岐 | `theorem ite {c : α → Prop} [DecidablePred c] {f : α → σ} {g : α → σ} (hc : PrimrecPred c)` | `:606` | ✅ 既存 | 機械のガード `(parseUnary p).1 = (parseUnary p).2.length` |
| **有界探索 (存在保証つき)** | `lemma find {α : Type*} [Primcodable α] {P : α → ℕ → Prop} [DecidableRel P] (hP_comp : ComputablePred (fun p : α × ℕ => P p.1 p.2)) (hP_ex : ∀ x, ∃ n, P x n) : Computable (fun x => Nat.find (hP_ex x))` | `Mathlib/Computability/RE.lean:177` | ✅ **既存** | **ステップ 3 の探索はこれ 1 本**。`Nat.rfind` を直接触らずに済む |
| r.e. 述語 | `def REPred {α} [Primcodable α] (p : α → Prop) := Partrec fun a => Part.assert (p a) fun _ => Part.some ()` / `theorem Partrec.dom_re {α β} [Primcodable α] [Primcodable β] {f : α →. β} (h : Partrec f) : REPred fun a => (f a).Dom` | `Mathlib/Computability/RE.lean:157 / :164` | ✅ 既存 | △ 代替ルート (Post の定理経由) 用。主ルートでは不要 |
| Post の定理 | `theorem computable_iff_re_compl_re' {p : α → Prop} : ComputablePred p ↔ REPred p ∧ REPred fun a => ¬p a` | `:241` | ✅ 既存 | △ 代替ルート。「Ω 計算可能 ⟹ 停止集合の補集合が r.e.」で閉じる形も可 |
| 決定可能述語の定義 | `def ComputablePred {α} [Primcodable α] (p : α → Prop) := ∃ (_ : DecidablePred p), Computable fun a => decide (p a)` | `:129` | ✅ 既存 | 最終矛盾の相手方の型 |
| 有限和の挿入 | `theorem prod_insert [DecidableEq ι] : a ∉ s → ∏ x ∈ insert a s, f x = f a * ∏ x ∈ s, f x` (加法版 `Finset.sum_insert`) | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:49` | ✅ 既存 | **ステップ 4 の質量超過** |
| 部分集合での和の単調性 | `theorem prod_le_prod_of_subset_of_one_le' [MulLeftMono N] (h : s ⊆ t) (hf : ∀ i ∈ t, i ∉ s → 1 ≤ f i)` (加法版 `Finset.sum_le_sum_of_subset_of_nonneg`) | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:131` | ✅ 既存 | `Ω_t` の単調性 |
| 有限集合の上界 | `theorem Finset.exists_le [Nonempty α] [Preorder α] [IsDirectedOrder α] (s : Finset α) : ∃ M, ∀ i ∈ s, i ≤ M` | `Mathlib/Data/Finset/Order.lean:32` | ✅ 既存 | `tsum_eq_iSup_sum'` の `hs` (cofinality) |
| **in-tree の Kraft 無限化** | `theorem tsum_inv_two_pow_length_le_one {P : List Bool → Prop} (hP : ∀ p, P p → (prefixUniversalEval p).Dom) : ∑' p : { p : List Bool // P p }, (2 : ℝ≥0∞)⁻¹ ^ (p : List Bool).length ≤ 1` | `InformationTheory/Shannon/Kolmogorov/PrefixMachine.lean:270` | ✅ 既存 | ○ 接続可能。`Ω_t ≤ 1` は要らない (使うのは `Ω_t ≤ Ω`) が、**「p を 1 本足したら 1 を超える」形の別証にも流用可能** ⟹ ステップ 4 の代替 |

### §F. in-tree 資産の再利用可否 (○ = 消費する / △ = 条件つき / ✖ = 使わない)

| decl | file:line | 判定 | 理由 |
|---|---|---|---|
| `theorem prefixUniversalEval_partrec : Partrec prefixUniversalEval` | `PrefixComputability.lean:46` | ○ | 論法の骨格ではないが、`prefixEvaln` の完全性 (`Dom ↔ ∃ k, isSome`) を建てる際の sanity 参照。**論法本体は `prefixEvaln` を新たに建てて使う** |
| `theorem prefixUniversalEval_dom_not_computablePred : ¬ ComputablePred fun p : List Bool ↦ (prefixUniversalEval p).Dom` | `:66` (`@[entry_point]`) | ○ **最重要** | **最終矛盾の相手**。gateway atom はこの 1 本のために着地した |
| `theorem primrec_replicate_true : Primrec fun n : ℕ ↦ List.replicate n true` | `:27` | ○ | ビット列列挙器 / `2^n` の Primrec 化の雛形 (同じ `Primrec.nat_iterate` パターン) |
| `theorem primrec_prefixInterpretProg_nil : Primrec fun idx : ℕ ↦ prefixInterpretProg idx []` | `:36` | ✖ | gateway atom 専用 (停止問題の埋め込み)。本論法では使わない |
| `noncomputable def chaitinOmega : ℝ≥0∞` | `Omega.lean:40` | ○ | 主題。consumer 実測 = **3 decl / 1 file** (`chaitinOmega_le_one:43` / `chaitinOmega_pos:53` / `chaitinOmega_ne_top:64`、`scripts/dep_consumers.sh` 実測) ⟹ **署名変更は不要、新ファイルからの read-only 消費で ripple 0** |
| `theorem chaitinOmega_le_one : chaitinOmega ≤ 1` | `:49` | △ | 直接は不要。`≠ ⊤` が要るだけ |
| `theorem chaitinOmega_pos : 0 < chaitinOmega` | `:55` | ○ | `ENNReal.sub_lt_self` の `a ≠ 0` |
| `theorem chaitinOmega_ne_top : chaitinOmega ≠ ⊤` | `:64` | ○ | `ENNReal.sub_lt_self` の `a ≠ ∞` |
| `prefixInterpretProg` / `prefixUniversalEval_interpret` / `prefix_invariance` / `prefixComplexity_not_computable` | `Omega.lean:117 / :126 / :146 / :162` | ✖ | K の非計算性の系統。Ω の非計算性は**別 object** で、これらは論法に現れない |
| `shortestPrefixProg` / `shortestPrefixNat` / `prefixComplexity_lt_finite` / `exists_prefixIncompressible` | `Omega.lean:71 / :74 / :98 / :105` | ✖ | Berry 論法側の資産 |
| `noncomputable def prefixUniversalEval (p : List Bool) : Part ℕ` | `PrefixMachine.lean:172` | ○ | 有界版 `prefixEvaln` を定義に沿って建てる。**署名は触らない** (触ると P8 実測 ripple 21 decl / 3 file) |
| `noncomputable def decodePayload : List Bool → Part ℕ` | `:162` | ○ | 同上、有界版の対象 |
| `theorem prefixUniversalEval_dom_prefixFree : PrefixFree {p \| (prefixUniversalEval p).Dom}` | `:201` | △ | ステップ 4 の代替証明 (Kraft で 1 を超える形) を採るなら要る |
| `theorem tsum_inv_two_pow_length_le_one {P : List Bool → Prop} (hP : ∀ p, P p → (prefixUniversalEval p).Dom) : …` | `:270` | △ | 同上 (§E 表に verbatim) |
| `theorem parseUnary_primrec : Primrec parseUnary` | `SufficientStatistic.lean:319` | ○ **必須** | 機械のガードの計算可能性 |
| `theorem decodeNat_primrec : Primrec decodeNat` | `:297` | ○ **必須** | literal モードの計算可能性 |
| `theorem encodeNat_primrec : Primrec encodeNat` | `:250` | △ | 直接は不要 (往路は使わない)。ℕ↔bit の補題で要れば |
| `theorem payloadDispatch_computable : Computable payloadDispatch` | `:347` | ○ **ただし要格上げ** | `prefixEvaln` の Primrec 性には **`Primrec payloadDispatch` が要る**。証明本体 (`:370` の `(Primrec.list_casesOn …).of_eq …).to_comp`) は Primrec を作ってから `to_comp` で落としているので、**`.to_comp` を外した `payloadDispatch_primrec` を 1 本足すだけ** (~3 行、既存署名は残す ⟹ ripple 0) |
| `theorem decodePayload_eq_dispatch (d : List Bool) : decodePayload d = (payloadDispatch d : Part (Code × ℕ)).bind fun p ↦ eval p.1 p.2` | `:375` | ○ **最重要** | **有界化の設計図**。`prefixEvaln` を `(payloadDispatch d).bind fun p ↦ evaln k p.1 p.2` と定義すれば、sound/complete が `evaln_sound`/`evaln_complete` の 1 行 lift になる |
| `theorem decodePayload_partrec : Partrec decodePayload` | `:383` | △ | 参照のみ |
| `payloadComplexity_two_part_le` / `twoPartUnpack_partrec` / KSS 定義群 | `:502 / :487 / :70–110` | ✖ | P10 の十分統計量系。本論法に現れない |
| `def progNat : List Bool → ℕ` / `progNat_lt` / `progNat_injective` | `Counting.lean:26 / :35 / :46` | △ | 列挙器を自作せず「`List.range (2^(t+1))` を `progNat` の逆で引く」route を採るなら要るが、**逆写像の Primrec 性が別途要る** ⟹ 直接再帰の列挙器の方が安い。判定 = 使わない |

---

## Key-preconditions box (事故ポイント)

- **`Computable.find` (`RE.lean:177`)**: `[DecidableRel P]` が**インスタンス引数**。探索述語をℝ≥0∞ の不等式で書くと
  古典 instance になり `decide` が計算不能になる。⟹ **述語は ℕ の dyadic 比較で定義**し、ℝ≥0∞ 版とは別補題で
  同値を取る。古典 instance を使ってしまった場合でも `Computable.of_eq` で外形を差し替えれば救えるが、
  1 手増える。
- **`ComputablePred` の定義 (`RE.lean:129`)**: `∃ (_ : DecidablePred p), Computable fun a => decide (p a)`。
  決定手続きの存在を**存在量化で包んでいる**ので、`Decidable` インスタンスの選び方は証明の自由度。ただし
  `Computable (fun a ↦ decide (p a))` は選んだインスタンスに依存するため、`decide` の展開形を意識すること。
- **`ENNReal.sub_lt_self` (`Operations.lean:391`)**: 前提は `a ≠ ∞` / `a ≠ 0` / `b ≠ 0` の**3 つ**。Ω については
  すべて in-tree で証明済 (`chaitinOmega_ne_top` / `chaitinOmega_pos`) だが、`b = (2:ℝ≥0∞)⁻¹^k ≠ 0` は
  `ENNReal.pow_pos` + `simp` で別途出す (`Omega.lean:62` に同型の使用例)。
- **`ENNReal.mul_inv_cancel` (`Inv.lean:102`)**: `a ≠ 0` **かつ** `a ≠ ∞` の両側条件。`2^k` については両方
  自明だが、`simp` は自動では出さない。橋補題 1 本に閉じ込めること。
- **`ENNReal.tsum_eq_iSup_sum'` (`ENNReal.lean:74`)**: `hs : ∀ t, ∃ i, t ⊆ s i` の `t` は
  **部分型 `{p : List Bool // (prefixUniversalEval p).Dom}` 上の `Finset`**。各元から停止時刻を取り出すのに
  `Nat.find (evaln_complete …)` を使い、`Finset.exists_le` で上限を取る。**「有限集合の元ごとに選択」を
  `Finset.image` + `Finset.exists_le` の形にしないと `Classical.choice` が散らかる**。
- **`Primcodable (Finset _)` は不在**: 計算可能性の層 (`omegaApproxNum`) は `List (List Bool)` 上で組み、
  `Finset` は ℝ≥0∞ 和 (`omegaApprox`) の側でのみ使う。両者を繋ぐ `List.toFinset` の nodup 条件に注意
  (列挙器が重複を作らないことを `List.Nodup` で保つと `Finset.sum` ↔ `List.sum` の橋が簡単)。
- **`evaln` の予算パラメータは時間ではない** (`PartrecCode.lean:564–566`): 「`k` 以上の数に出会ったら失敗」。
  `evaln_bound` により入力 `n < k` が必要なので、`prefixEvaln t p` は `decodeNat` 後の値が `t` 未満でないと
  停止しない。⟹ **`Ω_t` の t は「長さ ≤ t」と「予算 t」を兼ねる**が、完全性 (`⨆ = Ω`) の証明で
  「t を十分大きく取れば両方満たす」を **`max` で 1 回組む**必要がある。
- **`prefixUniversalEval` の署名は触らない**: 触ると P8 実測 ripple (`prefixUniversalEval` = 21 decl / 3 file、
  親 plan §Phase P8)。本 scope は**新規 decl だけで閉じる**設計にすること。
- **定義の強度**: §C-2 の ⚠️ 2 件 (厳密床にしない / ℝ 版の符号縮退) は honesty gate の対象。
  「`¬` が自明に真になる定義」を作ると tier 5 (退化定義の濫用) 相当。

---

## 自作が必要な要素 (優先度順)

| # | 対象 | 推奨実装 | 見積 | 落とし穴 |
|---|---|---|---|---|
| 1 | **`prefixEvaln : ℕ → List Bool → Option ℕ`** (機械の有界版) | `fun k p ↦ if (parseUnary p).1 = (parseUnary p).2.length then (payloadDispatch (parseUnary p).2).bind (fun q ↦ evaln k q.1 q.2) else none` — **`decodePayload_eq_dispatch` (`SufficientStatistic.lean:375`) の bounded 版そのもの** | 15 行 (def + 展開補題) | `payloadDispatch` の `Option` と `evaln` の `Option` の bind 順序。`Part` を経由しないこと |
| 2 | `prefixEvaln` の sound / mono / complete | `evaln_sound` / `evaln_mono` / `evaln_complete` を `Option.bind` 越しに lift。complete は `prefixUniversalEval` の定義展開 + `decodePayload_eq_dispatch` | 60–90 行 | complete の向き。`(prefixUniversalEval p).Dom ↔ ∃ k, (prefixEvaln k p).isSome` を**両向き**で建てる |
| 3 | **`prefixEvaln` の Primrec 性** | `primrec_evaln` (`:922`) + `parseUnary_primrec` + `payloadDispatch_primrec` (§F の格上げ 3 行) + `Primrec.option_bind` / `Primrec.ite` | 30–45 行 | `payloadDispatch_computable` は `Computable` 止まり ⟹ **先に Primrec 版を足す** |
| 4 | ビット列列挙器 `allBitStringsLE : ℕ → List (List Bool)` + Primrec + メンバシップ特徴づけ | `allBitStrings 0 = [[]]` / `allBitStrings (n+1) = (allBitStrings n).flatMap (fun l ↦ [false :: l, true :: l])`、`allBitStringsLE t = (List.range (t+1)).flatMap allBitStrings`。Primrec は `Primrec.nat_rec` + `Primrec.list_flatMap` | 40–60 行 | `p ∈ allBitStringsLE t ↔ p.length ≤ t` と `Nodup` の 2 本が要る。`List.sections` 経由は Primrec 補題が無く不可 |
| 5 | `omegaApprox t : ℝ≥0∞` / `omegaApproxNum t : ℕ` / 橋補題 | `omegaApprox t := ∑ p ∈ (allBitStringsLE t).toFinset.filter (fun p ↦ (prefixEvaln t p).isSome), (2:ℝ≥0∞)⁻¹ ^ p.length`、`omegaApproxNum t := ∑ 2^(t - p.length)` (ℕ)、橋 `omegaApprox t = omegaApproxNum t * (2⁻¹)^t` | 60–90 行 | 橋で `ENNReal.mul_inv_cancel` の副条件。`t - p.length` は ℕ の truncated だが `p.length ≤ t` でふるってあるので安全 |
| 6 | `Computable omegaApproxNum` | #3 + #4 + `Primrec.listFilter` + `Primrec.list_foldl` + `Primrec fun n ↦ 2^n` (自作 4 行) | 40–60 行 | `Primrec₂ ((·^·) : ℕ→ℕ→ℕ)` は不在 (§B)。`Nat.Primrec.pow` を lift するより `nat_iterate` で `2^n` を直接作る方が短い |
| 7 | 単調性 + `⨆ t, omegaApprox t = chaitinOmega` | `Finset.sum_le_sum_of_subset_of_nonneg` + `ENNReal.tsum_eq_iSup_sum'`。cofinality は `Nat.find` の停止時刻 + `Finset.exists_le` | 50–80 行 | **最重量候補**。部分型 `Finset` と `List Bool` の `Finset` の往復が煩雑。`Finset.image Subtype.val` の `InjOn` は `PrefixMachine.lean:249` に既存の雛形あり |
| 8 | 探索ステップ (`searchTime` + `Computable searchTime`) | `ENNReal.sub_lt_self` → `lt_iSup_iff` で存在、`Computable.find` (`RE.lean:177`) で計算可能性。述語は ℕ dyadic 比較 | 50–80 行 | ℝ≥0∞ 版述語と ℕ 版述語の同値補題を先に建てること (Key-preconditions) |
| 9 | 質量超過補題 (ステップ 4) | `p ∉ H t → |p| ≤ n → Dom p → omegaApprox t + (2⁻¹)^|p| ≤ chaitinOmega` を `Finset.sum_insert` + `ENNReal.sum_le_tsum` で | 40–60 行 | `insert` の `∉` を `prefixEvaln t p = none` から出す |
| 10 | `IsComputableENNReal` の定義 + headline 組み立て | §到達形。矛盾は `prefixUniversalEval_dom_not_computablePred` | 40–70 行 | §C-2 の ⚠️ (誤差幅を厳密床にしない) |

**依存順序**: 1 → 2/3 → 4 → 5/6 → 7 → 8/9 → 10。**1–3 を 1 leg (gateway 相当)** にして
`prefixEvaln` が実際に組めるかを先に実測するのが安全 (親 plan §Phase P9 の「(a)(b) はいずれも見立てであって
未実測」に対応する検算点)。

---

## Mathlib 壁の列挙

**genuine な `wall:` は 0 件。** 以下はいずれも「Mathlib 不在の解析 (hard)」ではなく「定義・自作の選択 (big)」。

| 候補 | loogle 0-hit (verbatim) | なぜ壁ではないか | 近い template と自作行数 |
|---|---|---|---|
| 計算可能実数 `ComputableReal` | `unknown identifier 'ComputableReal'` / `Found 0 declarations mentioning Real and Computable.` / `Found 0 declarations mentioning Real and Primrec.` | 命題が難しいのではなく**語彙が無い**だけ。定義を選べば以降は既存の `Computable` 閉包で回る | template = `ComputablePred` (`RE.lean:129`、`∃ (_ : Decidable…), Computable …` という同型の「∃ + Computable」形)。**定義 4 行 + 基本補題 15 行** |
| ℚ / ℤ 上の `Primrec` 四則 | `Found 0 declarations mentioning Rat and Primrec.` / `Found 0 declarations mentioning Int and Primrec.` | **設計で回避する** (分母を 2 冪に固定し分子を ℕ に)。ℚ 上の `Primrec` を自作する必要は本 scope には無い | (自作しない。回避が正解) |
| `Primrec₂ ((·^·) : ℕ → ℕ → ℕ)` | `Found 0 declarations mentioning Primcodable.ofDenumerable, HPow.hPow, Nat, Denumerable.nat, and Primrec₂.` / `Of these, 0 match your pattern(s).` | 低レベル `Nat.Primrec.pow` (`Primrec/Basic.lean:114`) が既存。必要なのは `2 ^ n` の 1 変数版だけ | template = `primrec_replicate_true` (`PrefixComputability.lean:27`、`Primrec.nat_iterate` 適用)。**4 行** |
| ビット列の列挙 `ℕ → List (List Bool)` の Primrec | `\|- Primrec (_ : ℕ → List (List Bool))` → `Found one declaration mentioning … Of these, 0 match your pattern(s).` | `Primrec.list_flatMap` / `nat_rec` が既存 ⟹ 素直な再帰定義で通る | template = `primrec_replicate_true` (同上) + `Primrec.list_flatMap` (`Primrec/List.lean:240`)。**#4 の 40–60 行**に含む |
| `Primcodable (Finset _)` | `Found 0 declarations mentioning Finset and Primcodable.` / `Of these, 0 match your pattern(s).` | P10 で既に確認済の既知事項。**設計で回避** (計算可能性は `List` 層、和は `Finset` 層) | (自作しない) |

**共有 sorry 補題の推奨**: **不要**。同一の壁が複数ファイルに散る構図が無い (本 scope は 1 ファイルで閉じ、
かつ壁が 0 件)。⟹ `docs/audit/audit-tags.md`「Shared Mathlib walls」のパターンは適用しない。
**新 slug も追加しない** — 親 plan §residual slug 方針の `plan:kolmogorov-w2-omega-noncomputable` 1 本で足りる
(P10 での `kolmogorov-w2-machine-partrec` 不採用と同じ理由: 貼る先の `sorry` が増えないなら slug を増やさない)。

---

## §Honest scope call

**genuine な Mathlib gap (Mathlib に命題が無い)**: **0 件**。

**単に自作すればよい箇所 (語彙 / 配線)**: 上の自作表 #1–#10 の全部。内訳:

- **語彙の不在** (定義を選ぶ): `IsComputableENNReal` 1 本のみ。
- **配線 (plumbing)**: `prefixEvaln` とその 3 性質 / 列挙器 / 近似列 / 上限同一視 / 探索 / 質量超過。
  いずれも既存 Mathlib 補題 (`primrec_evaln` / `evaln_*` / `ENNReal.tsum_eq_iSup_sum'` / `Computable.find`) の
  結論形をそのまま消費でき、**変換ブリッジ (`f (compProd …)` → `∫⁻ …` 型の再整形) は 1 本も要らない**。

**既存率**: 論法で使う Mathlib API 26 項目 (§A 8 / §B 8 / §D 6 / §E 4 群) のうち **26 = 100% 既存**。
「Ω の非計算性を直接書ける高レベル API」は **0%** (計算可能実数の語彙が無いため)。
⟹ Fano 在庫と同じ構図 — **道具は全部あり、書くのは糊コード**。

**under-estimation ガード (「壁でない」を額面で受けない)**:
- 反例側の確認 = **本命題は真である**ことを 2 点で確認した。(a) 停止集合が prefix-free
  (`prefixUniversalEval_dom_prefixFree`) かつ Kraft で `Ω ≤ 1` (`chaitinOmega_le_one`) ⟹ ステップ 4 の質量論法が
  成立する。(b) 停止集合が実際に決定不能 (`prefixUniversalEval_dom_not_computablePred`、sorryAx-free) ⟹
  矛盾先が存在する。**どちらも in-tree の machine 検証済**で、仮定ではない。
- 退化境界 = `Ω = 0` なら論法が空回りするが `chaitinOmega_pos` で排除済。`Ω = ⊤` も `chaitinOmega_ne_top` で排除済。
- **textbook-object strength diff**: 教科書の「Ω is not computable」は**計算可能実数**についての主張。
  in-tree に対応物が無い以上、**自作定義の強度が教科書と一致しているかは自作者の責任**であり、
  §C-2 の ⚠️ (厳密床にすると弱くなる) が唯一の強度差リスク。**P8 の factor-2 / P10 の係数 4 と同じ構図**
  (教科書形をそのまま名乗れるか) なので、定義確定時に 1 回 diff を通すこと。

## §見積

- **全体 400–650 行 / 1 ファイル**。P10 (594 行) と同程度、P8 (245 行) の 2 倍前後。
- **最重量ブロック = #7「`⨆ t, omegaApprox t = chaitinOmega`」** (50–80 行)。部分型 `Finset` の cofinality と
  `List Bool` 側の `Finset` の往復が煩雑で、ここだけ既存雛形が薄い。次点は **#6 `Computable omegaApproxNum`**
  (40–60 行、ただし部品は全部既存なので詰まりにくい)。
- **決算の目安**: #1–#3 が 1 日で通れば残りは直線。#1–#3 が通らない場合は `evaln` の bounded 化の設計を
  疑う (`payloadDispatch` を経由しない素朴な再帰定義は `Code` の再帰と噛み合わず爆発する)。
- **P8 / P10 の実測が示した通り、行数見積は着地の可否を予言しない** — 予算超過を撤退判断の根拠にしないこと。

## §退避候補 (proof-done に届かない場合、切り落とす順)

親 plan の撤退ライン R-W2a / R-W2b / R-W2c は**いずれも第 2 波内で決着済で、本 scope を覆う active な
撤退ラインは存在しない** (親 plan「残る撤退ラインは無く、後継 scope 2 件は撤退ではなく別 object の新規建て」)。
⟹ **本 scope 用の撤退ラインは新規に建てる必要がある**。以下を提案する (採否は plan 起票側の判断):

1. **最初に切る = #7 の完全形 (`⨆ = Ω`)**。`⨆ t, Ω_t ≤ Ω` (易) だけを取り、逆向き (cofinality) を
   `sorry + @residual(plan:kolmogorov-w2-omega-noncomputable)` にする。**残る honest な着地点** =
   「有界機械 `prefixEvaln` の構成 + sound/mono/complete + Primrec 性」= 計算可能性インフラとして単体で価値があり、
   後続 (加法版 Levin 側の機械構成) でも再利用される。
2. **次に切る = #8 の探索の計算可能性**。存在 (`∃ t, Ω < Ω_t + ε`) は非構成的に取れるので、
   `Computable searchTime` だけを `sorry` に落とす。**残る着地点** = 「Ω が計算可能なら停止集合が
   *算術的に* 決定される」までの数学的骨格。
3. **最後まで残す = headline の形**。`¬ IsComputableENNReal chaitinOmega` の**署名は最後まで崩さない**。
   仮説束ね (`IsComputableApproxHypothesis` 的な述語に核を詰める) は禁止 ⟹ 退避出口は必ず
   `sorry + @residual(plan:kolmogorov-w2-omega-noncomputable)`。
4. **任意項目 (最初から入れなくてよい)**: ℝ 版 headline `¬ IsComputableReal chaitinOmega.toReal` と
   その橋補題。§C-2 の符号縮退リスクがあるので、**ℝ≥0∞ 版が proof-done になってから**着手する。

**撤退ラインとして提案する判定基準**: 「#1–#3 (有界機械の構成と Primrec 性) が leg 1 本で通らない」場合、
Chaitin 論法本体には進まず、`prefixEvaln` インフラだけを別ファイルで着地させて scope を畳む。

---

## 着手 skeleton

`InformationTheory/Shannon/Kolmogorov/OmegaNoncomputable.lean` の出だし
(`PrefixComputability.lean` が `Halting` / `Omega` / `SufficientStatistic` を既に import しているので、
`PartrecCode` / `ENNReal` の tsum / Kraft はすべて推移的に入る):

```lean
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Kolmogorov.PrefixComputability

/-!
# Chaitin's constant is not a computable real

Cover-Thomas (2nd ed.) §14.9. The halting probability of the self-delimiting
machine admits a computable lower approximation `Ω_t`, so a computable
approximation of `Ω` from above would locate a stage past which no short program
can still halt, deciding the machine's halting set.

## Main definitions

* `IsComputableENNReal` — computability of an extended nonnegative real by a
  computable sequence of dyadic rationals with error `2 ^ (-n)`.
* `prefixEvaln` — the step-bounded evaluator of the self-delimiting machine.

## Main statements

* `chaitinOmega_not_computable` — `Ω` is not a computable real.
-/

open scoped ENNReal

namespace InformationTheory.Kolmogorov

open Nat.Partrec Nat.Partrec.Code

/-- A computable nonnegative extended real: a computable sequence of dyadic
numerators `a n` whose value `a n / 2 ^ n` is within `2 ^ (-n)` of `x`. The bound
is stated additively so that no truncated subtraction occurs. -/
def IsComputableENNReal (x : ℝ≥0∞) : Prop :=
  ∃ a : ℕ → ℕ, Computable a ∧ ∀ n : ℕ,
    x ≤ (a n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n + (2 : ℝ≥0∞)⁻¹ ^ n ∧
      (a n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n ≤ x + (2 : ℝ≥0∞)⁻¹ ^ n

/-- The step-bounded evaluator: the self-delimiting machine run with budget `k`,
following `decodePayload_eq_dispatch` with `eval` replaced by `evaln k`. -/
noncomputable def prefixEvaln (k : ℕ) (p : List Bool) : Option ℕ :=
  if (parseUnary p).1 = (parseUnary p).2.length then
    (payloadDispatch (parseUnary p).2).bind fun q ↦ evaln k q.1 q.2
  else none

theorem prefixEvaln_mono {k₁ k₂ : ℕ} {p : List Bool} {x : ℕ}
    (h : k₁ ≤ k₂) (hx : x ∈ prefixEvaln k₁ p) : x ∈ prefixEvaln k₂ p := by
  sorry

theorem prefixEvaln_sound {k : ℕ} {p : List Bool} {x : ℕ}
    (hx : x ∈ prefixEvaln k p) : x ∈ prefixUniversalEval p := by
  sorry

theorem prefixEvaln_complete {p : List Bool} {x : ℕ} :
    x ∈ prefixUniversalEval p ↔ ∃ k, x ∈ prefixEvaln k p := by
  sorry

/-- Chaitin's constant is not a computable real. -/
@[entry_point]
theorem chaitinOmega_not_computable : ¬ IsComputableENNReal chaitinOmega := by
  sorry

end InformationTheory.Kolmogorov
```

着手手順は `prefixEvaln_mono` / `_sound` / `_complete` の 3 sorry を先に潰し (= 撤退ライン判定点)、
そのあと列挙器 → 近似列 → 上限 → 探索 → 質量超過 の順に補題を挿していく。
新ファイル追加時は `InformationTheory.lean` へ import 行を登録すること (現状 Kolmogorov 群は L120–L132)。
