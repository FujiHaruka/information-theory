# Asymptotic / Exponent API: Mathlib 在庫 (I-3 着手前)

> `docs/textbook-roadmap.md` の **Tier ∞ — I-3 Asymptotic / exponent framework**
> ("各 proof で inline に書いている exponent / rate 表現を集約", "`\doteq`, `o(n)` notation,
> exponent function 共通 API", 規模 ~300-500 行) 着手前の事実列挙。
>
> **実装も計画起草もしない**。「いま何があるか」「InformationTheory のどこで inline 書きしているか」
> 「教科書 `\doteq` を表現する最有力 Mathlib API は何か」を構造化テーブルで書き出す。

---

## 一行サマリ

**Big-O / little-o / Theta / IsEquivalent の 4 種は Mathlib に揃っており notation も完備**。
**指数増大率 (`(1/n) log u_n` の liminf/limsup) は `ExpGrowth.expGrowthInf` /
`expGrowthSup` として既に存在** (`Mathlib/Analysis/Asymptotics/ExpGrowth.lean`,
2025 年追加、値域 `EReal`, 入力 `ℕ → ℝ≥0∞`)。一方 **教科書 `\doteq` (`a_n ≐ b_n`,
"exponent equality") に対応する 1 つの述語は不在** — `ExpGrowth.expGrowthSup (u/v) = 0`
や `(fun n => Real.log (u n / v n)) =o[atTop] (fun n => (n : ℝ))` 等の組合せで再現
することになる。

**InformationTheory 内の inline 表現は 2 系統に分裂している**:

1. **`Tendsto (fun n => (1/n) * Real.log ...) atTop (𝓝 (-C))`** 形 (AEP, SMB, Stein,
   Sanov LDP) — 教科書 `\doteq` の **rate 形** 値そのもの。8 ファイル横断。
2. **`∃ N : ℕ, ∀ n ≥ N, exp(-(n : ℝ) * g) < ε'`** 等の closed-form `N(g, ε')` extraction
   形 (channel coding achievability, rate distortion achievability, Phase D 系) — `Tendsto`
   から `metric_atTop` で抽出した直後の `∀ ε ∃ N` 形を inline 展開している。`AEPRate.lean`
   が **専用ファイルとして 905 行存在**しており、`exp_neg_mul_lt_of_rate` / `channelCoding_E2_lt_of_rate`
   / `typicalSet_prob_ge_at_N` 等の closed-form lemma を既に切り出し済み (ただしファミリー横断
   ではなく **AEP / channel coding 特化**)。

**乖離の度合いを定量的に**:

- big-O / little-o 系: **既存率 100%**。Mathlib `Asymptotics` namespace + 3 notation
  (`=O[l]`, `=o[l]`, `=Θ[l]`) で全て揃っている。InformationTheory 内に `IsBigO` / `IsLittleO`
  を使った既存 callsite は **見当たらず** (`rg "IsBigO|IsLittleO|=O\[|=o\[" InformationTheory/`
  で 0 件) — 統合の余地が大きい。
- exponent rate 系 (`Tendsto ((1/n) log) → -C`): **既存率 0%**。Mathlib 側に**直接対応する単一述語が無い**。
  最近 (2025) 追加された `ExpGrowth.expGrowthInf / expGrowthSup` (`Mathlib/Analysis/Asymptotics/
  ExpGrowth.lean`) が **EReal 値版で最も近い** が、InformationTheory の値域 `ℝ` 形 inline 表現と
  そのままでは型が合わない (要 `EReal.toReal` 経由 bridge)。
- `\doteq` (textbook exponent equality): **既存率 0%** — 名前付き述語は不在。3 つの候補
  (`Tendsto (fun n => (1/n) log (u/v)) → 0` / `IsLittleO atTop (log u - log v) (·:ℝ)` /
  `expGrowthInf u = expGrowthSup u = expGrowthInf v = expGrowthSup v` 形) のどれを採るかは
  設計判断。
- closed-form `N` extraction wrapper: **既存率 部分的**。`AEPRate.lean` (905 行) が AEP /
  channel coding 系で先行的に整備済みだが、family 横断の general wrapper は無い。

**主な発見 (最も影響が大きい順)**:

1. **`ExpGrowth.expGrowthSup` (`Mathlib/Analysis/Asymptotics/ExpGrowth.lean:41`) は
   2025 年新規追加**で、`ℕ → ℝ≥0∞` 上の `limsup (log (u n) / n)` を `EReal` で返す。
   教科書 `\doteq` の右辺 (rate) に最も近い既存定義。**ただし値域は `EReal`、入力は
   `ℝ≥0∞`** で、InformationTheory inline (`ℝ` 値) と型が合わず、`EReal.toReal` + 正値性条件の
   bridge が要る。これを使うか自作するかが最大の設計判断。
2. **`IsBigO` / `IsLittleO` の値域は normed group**で抽象。`f =o[atTop] (fun n => (n : ℝ))`
   は **`f` が `ℝ → E` で `‖f n‖ / n → 0`** を意味する。教科書の `\doteq` を `IsLittleO`
   経由で書く場合、log を取った上で little-o する形 (`(log u - log v) =o[atTop] (·:ℝ)`)
   が筋。**ただし `log` が ℝ で `±∞` を取らない前提**が必要 (u, v > 0 を確保せよ)。
3. **`Asymptotics.IsEquivalent.log`** (`Mathlib/Analysis/Asymptotics/SpecificAsymptotics.lean:133`)
   が **`f ~[l] g → log f ~[l] log g` (under `g → ∞`)** を提供しており、`IsEquivalent` 経由で
   log を扱う bridge が一発で得られる。
4. **`Metric.tendsto_atTop` (`Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:901`) は
   `Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε`** の同値形を提供。
   InformationTheory 内で **7 ファイルが既にこれを使用**しており、closed-form `N` extraction の
   "標準入口" として確立済み。I-3 wrapper はこの周りに薄く被せる形でよい。
5. **`AEPRate.lean` (905 行) は既に I-3 相当の機能を AEP 特化で持っている** —
   `exp_neg_mul_lt_of_rate`, `channelCoding_E2_lt_of_rate`, `typicalSet_prob_ge_at_N` 等の
   closed-form `N` lemma が並ぶ。I-3 では (a) これらを family-agnostic に再定式化、
   (b) channel coding / rate distortion / Sanov 系で **重複する `N(g, ε')` extraction を
   1 本化**、が中核作業になる。
6. **教科書 `o(n)` 表記は `=o[atTop] (·:ℝ)` 形でそのまま書ける**が、InformationTheory 内では
   **コメント・docstring に "o(n)" / "o(1)" 文字列が散見されるのみ** (`SanovLDP.lean:11`,
   `:470`, `StrongStein.lean:27`, `Stein.lean:1388`) で、**Lean 式中で `=o[atTop]` を使った
   箇所はゼロ**。すなわち教科書記法を notation で導入するだけで既存 callsite を一切壊さない。

---

## A. Mathlib Asymptotics 系 API surface

### A-1. 4 つの中心述語 (`IsBigO` / `IsLittleO` / `IsTheta` / `IsEquivalent`)

| 概念 | 定義 / signature (verbatim) | file:line | notation | 型クラス要件 (verbatim) |
|---|---|---|---|---|
| Big-O with constant | `irreducible_def IsBigOWith (c : ℝ) (l : Filter α) (f : α → E) (g : α → F) : Prop := ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖` | `Mathlib/Analysis/Asymptotics/Defs.lean:91` | — | `[Norm E] [Norm F]` |
| Big-O | `irreducible_def IsBigO (l : Filter α) (f : α → E) (g : α → F) : Prop := ∃ c : ℝ, IsBigOWith c l f g` | `Mathlib/Analysis/Asymptotics/Defs.lean:103` | `notation:100 f " =O[" l "] " g:100 => IsBigO l f g` (`:107`) | `[Norm E] [Norm F]` |
| Theta | `def IsTheta (l : Filter α) (f : α → E) (g : α → F) : Prop := IsBigO l f g ∧ IsBigO l g f` | `Mathlib/Analysis/Asymptotics/Defs.lean:170` | `notation:100 f " =Θ[" l "] " g:100 => IsTheta l f g` (`:174`) | `[Norm E] [Norm F]` |
| Little-o | `irreducible_def IsLittleO (l : Filter α) (f : α → E) (g : α → F) : Prop := ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f g` | `Mathlib/Analysis/Asymptotics/Defs.lean:187` | `notation:100 f " =o[" l "] " g:100 => IsLittleO l f g` (`:191`) | `[Norm E] [Norm F]` |
| Asymptotic equivalence | `def IsEquivalent (l : Filter α) (u v : α → E') := (u - v) =o[l] v` | `Mathlib/Analysis/Asymptotics/Defs.lean:223` | `scoped notation:50 u " ~[" l:50 "] " v:50 => Asymptotics.IsEquivalent l u v` (`:226`) | `[SeminormedAddCommGroup E']` |

**重要な制約 (verbatim)**:

- すべて `Filter α` 上の述語。`atTop` (`Filter.atTop`) や `𝓝 (0 : ℝ)` などをパラメタに取り、
  「`atTop` で little-o」 = `=o[atTop]` と書ける。
- `IsBigO` / `IsLittleO` の値域型 `E`, `F` は **`[Norm E] [Norm F]` だけ**で
  `SeminormedAddCommGroup` まで要らない。`IsEquivalent` だけは `[SeminormedAddCommGroup E']`
  が要求 (引き算が要るため)。
- notation の precedence は `100` (Big-O, little-o, Theta) と `50` (IsEquivalent scoped)。
  教科書記法 `a ≐ b` を仮に追加するなら precedence は `50` 側に揃えるのが筋。
- **`IsEquivalent` は `scoped` notation** (`Asymptotics` namespace 内のみ有効)。Big-O /
  little-o / Theta は **大域 notation** (どこでも使える)。

### A-2. 基本性質 (transitivity / monotonicity / 合成)

| 概念 | API | file:line | signature (verbatim) | 用途 |
|---|---|---|---|---|
| Little-o → Big-O | `IsLittleO.isBigO (hgf : f =o[l] g) : f =O[l] g` | `Mathlib/Analysis/Asymptotics/Defs.lean:238` | 上記 | 強→弱 |
| Big-O transitive | `IsBigO.trans {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g) (hgk : g =O[l] k) : f =O[l] k` | `Mathlib/Analysis/Asymptotics/Defs.lean:481` | 上記 | 連鎖 |
| Little-o transitive | `IsLittleO.trans {f : α → E} {g : α → F} {k : α → G} (hfg : f =o[l] g) (hgk : g =o[l] k) : f =o[l] k` | `Mathlib/Analysis/Asymptotics/Defs.lean:526` | 上記 | 連鎖 |
| filter 単調 | `IsBigO.mono (h : f =O[l'] g) (hl : l ≤ l') : f =O[l] g` | `Mathlib/Analysis/Asymptotics/Defs.lean:465` | 上記 | より粗いフィルタへ |
| Big-O 合成 | `IsBigO.comp_tendsto (hfg : f =O[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) : (f ∘ k) =O[l'] (g ∘ k)` | `Mathlib/Analysis/Asymptotics/Defs.lean:435` | 上記 | 引数変数の置換 |
| Little-o 合成 | `IsLittleO.comp_tendsto (hfg : f =o[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) : (f ∘ k) =o[l'] (g ∘ k)` | `Mathlib/Analysis/Asymptotics/Defs.lean:444` | 上記 | 同上 |
| `ℝ → ℕ` 移送 (Big-O) | `IsBigO.natCast_atTop {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R] {f : R → E} {g : R → F} (h : f =O[atTop] g) : (fun (n : ℕ) => f n) =O[atTop] (fun n => g n)` | `Mathlib/Analysis/Asymptotics/Lemmas.lean:685` | 上記 | 連続 → 離散 |
| `ℝ → ℕ` 移送 (little-o) | `IsLittleO.natCast_atTop {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R] {f : R → E} {g : R → F} (h : f =o[atTop] g) : (fun (n : ℕ) => f n) =o[atTop] (fun n => g n)` | `Mathlib/Analysis/Asymptotics/Lemmas.lean:691` | 上記 | 同上 |

### A-3. `Tendsto` ↔ Asymptotics 系 bridge

| 概念 | API | file:line | signature (verbatim) | 用途 |
|---|---|---|---|---|
| little-o ↔ ratio → 0 | `isLittleO_iff_tendsto {f g : α → 𝕜} (hgf : ∀ x, g x = 0 → f x = 0) : f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0)` | `Mathlib/Analysis/Asymptotics/Lemmas.lean:382` | 上記 | `[NormedField 𝕜]` (file context); g に零点無しは `hgf` で吸収 |
| little-o ← div → ∞ | `IsLittleO.of_tendsto_div_atTop (h : Tendsto (fun x ↦ g x / f x) l atTop) : f =o[l] g` | `Mathlib/Analysis/Asymptotics/Lemmas.lean:434` | 上記 | `{𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]` |
| `Tendsto a (𝓝 a)` ↔ `IsEquivalent` to const | `isEquivalent_const_iff_tendsto {c : β} (h : c ≠ 0) : u ~[l] const _ c ↔ Tendsto u l (𝓝 c)` | `Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:119` | 上記 | `[NormedAddCommGroup β]`, `c ≠ 0` |
| `IsEquivalent` から `Tendsto 1` | `isEquivalent_iff_tendsto_one (hz : ∀ᶠ x in l, v x ≠ 0) : u ~[l] v ↔ Tendsto (u / v) l (𝓝 1)` | `Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:208` | 上記 | `[NormedField β]` |
| `IsEquivalent` 上下方向 atTop | `IsEquivalent.tendsto_atTop_iff [OrderTopology β] (huv : u ~[l] v) : Tendsto u l atTop ↔ Tendsto v l atTop` | `Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:318` | 上記 | `[NormedLinearOrderedField β]` |
| `IsEquivalent` log 移送 | `Asymptotics.IsEquivalent.log {α : Type*} {l : Filter α} {f g : α → ℝ} (hfg : f ~[l] g) (g_tendsto : Tendsto g l atTop) : (fun n ↦ Real.log (f n)) ~[l] (fun n ↦ Real.log (g n))` | `Mathlib/Analysis/Asymptotics/SpecificAsymptotics.lean:133` | 上記 | `g → ∞` 仮定 |

**重要な制約 (verbatim)**:

- `isLittleO_iff_tendsto` / `IsLittleO.of_tendsto_div_atTop` は **`[NormedField 𝕜]` 仮定の
  section** (`Mathlib/Analysis/Asymptotics/Lemmas.lean:431-432`):
  `variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]`.
  すなわち `f, g : α → 𝕜` が要求され、`f, g : α → ℝ≥0∞` 等の半順序拡張型では直接使えない。
- `IsEquivalent.tendsto_atTop_iff` は `[NormedLinearOrderedField β]` + `[OrderTopology β]`
  要求 — `ℝ` では当然成立、`EReal` では別途 bridge が要る。
- `Asymptotics.IsEquivalent.log` は **`g → atTop` 仮定が必須** — `g` が定数や `→ 0` のときは
  使えない。教科書 `\doteq` で `a_n, b_n → 0` (`exp(-n·D)` 形) を扱うケースが多いので、
  log の取り方を逆に (`-log` を取って `→ +∞` 側) するべきかは要確認。

### A-4. 関連 `Tendsto` API (extraction の入口)

| 概念 | API | file:line | signature (verbatim) | 用途 |
|---|---|---|---|---|
| `Tendsto` から ε-N 抽出 | `Metric.tendsto_atTop [Nonempty β] [SemilatticeSup β] {u : β → α} {a : α} : Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε` | `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:901` | 上記 | `[PseudoMetricSpace α]` (section context); closed-form N 抽出の標準入口 |
| `Tendsto` from sandwich | `tendsto_of_le_liminf_of_limsup_le {f : Filter β} {u : β → α} {a : α} (hinf : a ≤ liminf u f) (hsup : limsup u f ≤ a) (h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault) (h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) : Tendsto u f (𝓝 a)` | `Mathlib/Topology/Order/LiminfLimsup.lean:306` | 上記 | `[ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]` (section context); SMB / Sanov の最終合流 |
| `Tendsto` from `liminf=limsup` | `tendsto_of_liminf_eq_limsup {f : Filter β} {u : β → α} {a : α} (hinf : liminf u f = a) (hsup : limsup u f = a) ...: Tendsto u f (𝓝 a)` | `Mathlib/Topology/Order/LiminfLimsup.lean:299` | 上記 | 同上 |

### A-5. `ExpGrowth` (指数増大率、教科書 `\doteq` の右辺)

| 概念 | API | file:line | signature (verbatim) | 用途 |
|---|---|---|---|---|
| 指数増大率 (下) | `noncomputable def expGrowthInf (u : ℕ → ℝ≥0∞) : EReal := liminf (fun n ↦ log (u n) / n) atTop` | `Mathlib/Analysis/Asymptotics/ExpGrowth.lean:38` | 上記 | `ℕ → ℝ≥0∞` のみ |
| 指数増大率 (上) | `noncomputable def expGrowthSup (u : ℕ → ℝ≥0∞) : EReal := limsup (fun n ↦ log (u n) / n) atTop` | `Mathlib/Analysis/Asymptotics/ExpGrowth.lean:41` | 上記 | 同上 |
| 線形増大率 (一般) | `noncomputable def linearGrowthInf (u : ℕ → R) : R := liminf (fun n ↦ u n / n) atTop` | `Mathlib/Analysis/Asymptotics/LinearGrowth.lean:45` | 上記 | `{R : Type*} [ConditionallyCompleteLattice R] [Div R] [NatCast R]` |
| `expGrowthInf` ≤ `expGrowthSup` | `expGrowthInf_le_expGrowthSup : expGrowthInf u ≤ expGrowthSup u` | `Mathlib/Analysis/Asymptotics/ExpGrowth.lean:79` | 上記 | 自明 |
| `≤a ↔ ∀b>a, ∃ᶠ n, u n ≤ exp(b·n)` | `expGrowthInf_le_iff : expGrowthInf u ≤ a ↔ ∀ b > a, ∃ᶠ n : ℕ in atTop, u n ≤ exp (b * n)` | `Mathlib/Analysis/Asymptotics/ExpGrowth.lean:85` | 上記 | テスト関数 |
| `a≤_ ↔ ∀b<a, ∀ᶠ n, exp(b·n) ≤ u n` | `le_expGrowthInf_iff : a ≤ expGrowthInf u ↔ ∀ b < a, ∀ᶠ n : ℕ in atTop, exp (b * n) ≤ u n` | `Mathlib/Analysis/Asymptotics/ExpGrowth.lean:92` | 上記 | 同上 (上界版) |
| `Eventually.le_expGrowthInf` | `lemma _root_.Eventually.le_expGrowthInf (h : ∀ᶠ n : ℕ in atTop, exp (a * n) ≤ u n) : a ≤ expGrowthInf u` | `Mathlib/Analysis/Asymptotics/ExpGrowth.lean:138` | 上記 | 単方向; 一番使う形 |
| `Eventually.expGrowthSup_le` | `lemma _root_.Eventually.expGrowthSup_le (h : ∀ᶠ n : ℕ in atTop, u n ≤ exp (a * n)) : expGrowthSup u ≤ a` | `Mathlib/Analysis/Asymptotics/ExpGrowth.lean:142` | 上記 | 同上 |
| `(b≠0,⊤) ⟹ expGrowthInf const = 0` | `expGrowthInf_const (h : b ≠ 0) (h' : b ≠ ∞) : expGrowthInf (fun _ ↦ b) = 0` | `Mathlib/Analysis/Asymptotics/ExpGrowth.lean:172` | 上記 | 定数列 |
| `expGrowthInf (b^n) = log b` | `expGrowthInf_pow : expGrowthInf (fun n ↦ b ^ n) = log b` | `Mathlib/Analysis/Asymptotics/ExpGrowth.lean:180` | 上記 | 教科書 `c^n ≐ exp(n log c)` |
| `expGrowthInf (exp(an)) = a` | `expGrowthInf_exp : expGrowthInf (fun n ↦ exp (a * n)) = a` | `Mathlib/Analysis/Asymptotics/ExpGrowth.lean:192` | 上記 | 教科書 `exp(an) ≐ exp(an)` |

**重要な制約 (verbatim)**:

- **値域は `EReal`、入力は `ℕ → ℝ≥0∞`** (`expGrowthInf : (ℕ → ℝ≥0∞) → EReal`)。InformationTheory
  inline (例えば `Tendsto (fun n => (1/n) * Real.log P_n) atTop (𝓝 (-C))` の左辺の値域は
  `ℝ`) と直接型が合わない。bridge には `ENNReal.ofReal` で持ち上げる or `EReal.toReal` で
  落とす形が必要、しかも符号の取り扱い (`Real.log P_n` は `P_n < 1` で負) で `log` 関数の
  選び方 (`ENNReal.log` か `Real.log`) が変わる。
- `ENNReal.log : ℝ≥0∞ → EReal` (`Mathlib/Analysis/SpecialFunctions/Log/ENNRealLog.lean:46`)
  と `Real.log : ℝ → ℝ` は異なる関数。`expGrowth*` は **`ENNReal.log` を内部で使う**
  (`Mathlib/Analysis/Asymptotics/ExpGrowth.lean:32` の `open ENNReal EReal Filter Function`)。
- まだ `Tendsto` 形と `expGrowth*` 形の **同値 bridge は不在**: loogle
  `"ExpGrowth.expGrowthSup, Tendsto"` → 0 件。`expGrowthInf u = expGrowthSup u = c` が
  `Tendsto ((fun n => log (u n) / n)) atTop (𝓝 c)` に同値、という単一補題が未整備。
- `LinearGrowth` 側は **より一般的な `R : [ConditionallyCompleteLattice R] [Div R] [NatCast R]`**
  上で同型の定義 (`liminf (u n / n)`)。これも InformationTheory inline (`Tendsto (fun n => (1/n)
  * Real.log P_n)` の値そのもの) と型が一致しない (`limsup` / `liminf` 形なので)。

### A-6. Real / ENNReal の log / exp

| 概念 | API | file:line | signature (verbatim) | 用途 |
|---|---|---|---|---|
| `Real.log` mul | `theorem log_mul (hx : x ≠ 0) (hy : y ≠ 0) : log (x * y) = log x + log y` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:132` | 上記 (`Real` namespace) | 教科書 `log(ab) = log a + log b` |
| `Real.log` div | `theorem log_div (hx : x ≠ 0) (hy : y ≠ 0) : log (x / y) = log x - log y` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:137` | 同上 | `log(a/b)` |
| `Real.log` pow | `theorem log_pow (x : ℝ) (n : ℕ) : log (x ^ n) = n * log x` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:287` | 同上 | `log(c^n) = n log c` |
| `Real.log` ≤ iff | `theorem log_le_log_iff (h : 0 < x) (h₁ : 0 < y) : log x ≤ log y ↔ x ≤ y` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:146` | 同上 | 単調性 |
| `Real.exp_log` | `theorem exp_log (hx : 0 < x) : exp (log x) = x` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:58` | 同上 | 逆関数 |
| `Real.tendsto_log_atTop` | `theorem tendsto_log_atTop : Tendsto log atTop atTop` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:340` | 同上 | `log → ∞` |
| `Real.exp_mul` | `theorem exp_mul (x y : ℝ) : exp (x * y) = exp x ^ y` | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:54` | 同上 | `exp(nx) = (exp x)^n` (rpow 経由) |
| `Real.exp_nat_mul` | `nonrec theorem exp_nat_mul (x : ℝ) (n : ℕ) : exp (n * x) = exp x ^ n` | `Mathlib/Analysis/Complex/Exponential.lean:229` | 同上 | ℕ 専用 (より rewrite しやすい) |
| `Real.exp_le_exp` | `theorem exp_le_exp {x y : ℝ} : exp x ≤ exp y ↔ x ≤ y` | `Mathlib/Analysis/Complex/Exponential.lean:316` | 同上 | 単調 (iff) |
| `Real.exp_le_exp_of_le` | `theorem exp_le_exp_of_le {x y : ℝ} (h : x ≤ y) : exp x ≤ exp y` | `Mathlib/Analysis/Complex/Exponential.lean:309` | 同上 | 単方向 |
| `Real.isLittleO_log_id_atTop` | `theorem isLittleO_log_id_atTop : log =o[atTop] id` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:439` | 同上 | `log n = o(n)` (一文) |
| `Real.isLittleO_const_log_atTop` | `theorem isLittleO_const_log_atTop {c : ℝ} : (fun _ => c) =o[atTop] log` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:442` | 同上 | `c = o(log n)` |
| `Real.isLittleO_pow_exp_atTop` | `Real.isLittleO_pow_exp_atTop` | `Mathlib/Analysis/SpecialFunctions/Exp.lean` (loogle ヒット) | (未読、loogle 確定) | 教科書 `n^k = o(exp n)` |
| `ENNReal.log` | `noncomputable def log (x : ℝ≥0∞) : EReal := if x = 0 then ⊥ else if x = ⊤ then ⊤ else Real.log x.toReal` | `Mathlib/Analysis/SpecialFunctions/Log/ENNRealLog.lean:46` | `ENNReal` namespace | 値域 `EReal`, 0/⊤ も扱える |
| `ENNReal.log_mul_add` | `theorem log_mul_add {x y : ℝ≥0∞} : log (x * y) = log x + log y` | `Mathlib/Analysis/SpecialFunctions/Log/ENNRealLog.lean:134` | 同上 | mul の log (無条件) |
| `ENNReal.log_pow` | `theorem log_pow {x : ℝ≥0∞} {n : ℕ} : log (x ^ n) = n * log x` | `Mathlib/Analysis/SpecialFunctions/Log/ENNRealLog.lean:176` | 同上 | n-pow |
| `ENNReal.log_rpow` | `theorem log_rpow {x : ℝ≥0∞} {y : ℝ} : log (x ^ y) = y * log x` | `Mathlib/Analysis/SpecialFunctions/Log/ENNRealLog.lean:153` | 同上 | rpow |
| `ENNReal.exp_log` | `@[simp] lemma ENNReal.exp_log (x : ℝ≥0∞) : exp (log x) = x` | `Mathlib/Analysis/SpecialFunctions/Log/ENNRealLogExp.lean:47` | 同上 | 逆 |
| `EReal.log_exp` | `@[simp] lemma EReal.log_exp (x : EReal) : log (exp x) = x` | `Mathlib/Analysis/SpecialFunctions/Log/ENNRealLogExp.lean:41` | `EReal` namespace | 逆 |

**重要な制約 (verbatim)**:

- **`Real.log` は `x ≤ 0` で `0` を返す** (Mathlib 規約)。InformationTheory inline は `μ.real {x}`
  形で `≥ 0` だが `= 0` がありうる箇所では `Real.log 0 = 0` の事故が出る。`AEP.lean`,
  `SanovLDP.lean` 等は `hQpos`, `hPpos` で `> 0` を別途仮定して回避している。
- **`ENNReal.log` は `0 ↦ ⊥`, `⊤ ↦ ⊤`** で `±∞` 値を取る。`expGrowth*` を使う場合
  この境界処理を `Eventually` の中で吸収する必要がある。
- `Real.exp_mul (x y : ℝ) : exp (x * y) = exp x ^ y` の右辺は **`Real.rpow x.exp y`**
  (実数指数の冪)。教科書 `exp(nc) = (exp c)^n` (ℕ 指数) には **`Real.exp_nat_mul`** の方が
  rewrite で当てやすい。

### A-7. notation 一覧 (Asymptotics 関連)

| notation | 意味 | precedence | scope |
|---|---|---|---|
| `f =O[l] g` | `Asymptotics.IsBigO l f g` | 100 | global |
| `f =Θ[l] g` | `Asymptotics.IsTheta l f g` | 100 | global |
| `f =o[l] g` | `Asymptotics.IsLittleO l f g` | 100 | global |
| `u ~[l] v` | `Asymptotics.IsEquivalent l u v` | 50 | `scoped` (Asymptotics) |
| `f =o[𝕜; l] g` | `Asymptotics.IsLittleOTVS 𝕜 l f g` | 100 | global (`Asymptotics/TVS.lean:98`) |
| `f =O[𝕜; l] g` | `Asymptotics.IsBigOTVS 𝕜 l f g` | 100 | 同上 (`:116`) |
| `f =Θ[𝕜; l] g` | `Asymptotics.IsThetaTVS 𝕜 l f g` | 100 | 同上 (`:124`) |

**観察**: 「教科書 `o(n)`」を Lean で書くには `f =o[atTop] (fun (n : ℕ) => (n : ℝ))` と
**右辺に明示的に `(·:ℝ)` を渡す**必要がある (`atTop` だけでは引数型が自由)。「`o(1)`」は
`f =o[atTop] (fun _ => (1 : ℝ))` で書ける (`isLittleO_one_iff` 経由)。`o(log n)` も
同様に `f =o[atTop] Real.log`。すべて **既存 notation 1 つで足りる**。

---

## B. InformationTheory 内 inline 漸近表現 (代表 10 箇所)

| # | ファイル | 行 | 表現 (verbatim) | 親 theorem | カテゴリ |
|---|---|---|---|---|---|
| 1 | `InformationTheory/Shannon/AEP.lean` | 162-165 | `∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n) atTop (𝓝 (entropy μ (Xs 0)))` | `aep_ae` | LLN 形 (a.s. 収束) |
| 2 | `InformationTheory/Shannon/AEP.lean` | 190-194 | `Tendsto (fun n : ℕ => μ {ω | ε ≤ \|((∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n) - entropy μ (Xs 0)\|}) atTop (𝓝 0)` | `aep_inProbability` | 確率収束 (measure → 0) |
| 3 | `InformationTheory/Shannon/SMBAlgoetCover.lean` | 2840-2845 | `∀ᵐ ω ∂μ, Filter.Tendsto (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess))` (blockLogAvg = `-(1/n) * log P_n({block_n ω})`) | `shannon_mcmillan_breiman` | a.s. rate |
| 4 | `InformationTheory/Shannon/StrongStein.lean` | 509-512 | `Tendsto (fun n : ℕ => -((1 : ℝ) / n) * Real.log (steinOptimalBeta P Q n ε)) atTop (𝓝 (klDiv P Q).toReal)` | `stein_strong_lemma` | exponent rate 形 (典型) |
| 5 | `InformationTheory/Shannon/Stein.lean` | 1390-1409 | `(klDiv P Q).toReal ≤ Filter.liminf (fun n : ℕ => -((1 : ℝ) / n) * Real.log (steinOptimalBeta P Q n ε)) Filter.atTop ∧ Filter.limsup (fun n : ℕ => -((1 : ℝ) / n) * Real.log (steinOptimalBeta P Q n ε)) Filter.atTop ≤ (klDiv P Q).toReal / (1 - ε)` | `stein_lemma` | sandwich 形 (`liminf ≤ limsup`) |
| 6 | `InformationTheory/Shannon/SanovLDPEquality.lean` | 1253-1257 | `Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (((Measure.pi (fun _ : Fin n => Q)) (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal)) atTop (𝓝 (-(klDivSumForm_ofVec P (fun a => Q.real {a}))))` | `sanov_ldp_equality` | exponent rate 形 |
| 7 | `InformationTheory/Shannon/EntropyRate.lean` | 432-434 | `∃ H : ℝ, Tendsto (fun n : ℕ => blockEntropy μ p n / n) atTop (𝓝 H)` | `entropyRate_exists_of_stationary` | 平均的 (per-letter) rate; 値存在 |
| 8 | `InformationTheory/Shannon/EntropyRate.lean` | 466-468 | `Tendsto (conditionalEntropyTail μ p) atTop (𝓝 (entropyRate μ p))` | `entropyRate_eq_lim_condEntropy` | tail 収束 |
| 9 | `InformationTheory/Shannon/AEPRate.lean` | 323-324 | `∃ N : ℕ, ∀ n ≥ N, Real.exp (- (n : ℝ) * g) < ε'` | `exp_neg_mul_lt_of_rate` | closed-form N extraction |
| 10 | `InformationTheory/Shannon/AEPRate.lean` | 361-365 | `∃ N : ℕ, ∀ n ≥ N, ((Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) - 1) * Real.exp ((n : ℝ) * (-I + 3 * ε)) < ε'` | `channelCoding_E2_lt_of_rate` | closed-form N for channel coding |

**観察 — 共通形と揺れ**:

- **#1, #2 (AEP) は `Cesàro 平均形`** (`(∑_{i<n} f_i) / n`) で、教科書 LLN そのまま。`Real.log`
  は `logLikelihood` の中に隠れていて表面には出ない。
- **#3 (SMB), #4 (Stein), #6 (Sanov)** は **`(±1/n) * Real.log ... → 定数`** 形で完全に
  統一されている。係数 `-1/n` か `+1/n` の差はあるが、関数の "形" は同じ。教科書 `\doteq`
  の rate 形そのもの。
- **#5 (Stein 旧形) のみ sandwich** (`liminf ≤ ... ≤ limsup`)。新形 #4 (strong lemma) で
  `Tendsto` 形に到達。Sanov #6 も `tendsto_of_le_liminf_of_limsup_le` で sandwich → `Tendsto`
  形に降りている。
- **#7, #8 (entropy rate)** は **`H_n / n → H`** 形で、`Real.log` を内側に含まない。これは
  既に値が closed-form (entropy) なので `\doteq` ではなく **平均的 rate** という別カテゴリ。
- **#9, #10 (AEPRate)** は **closed-form `N(g, ε')` extraction** の典型例。`Tendsto.metric_atTop`
  を経由した直後の形を inline 展開している。Phase D channel coding / rate distortion で
  使う形。

**揺れ (file 間)**:

- 係数の書き方: `(1 / (n : ℝ))` vs `((1 : ℝ) / n)` の 2 通り (`StrongStein.lean:510` は後者、
  `SanovLDPEquality.lean:1254` は前者)。`ring` で解消可能だが notation 設計時に統一が要る。
- `Tendsto` の `atTop` の書き方: `Filter.atTop` (full path) と `atTop` (open 後) の混在。
- `(𝓝 _)` の中身は `ℝ` 値 (`(klDiv P Q).toReal`, `(-(klDiv ... ))`, `entropy μ X`,
  `entropyRate μ p`, `-(klDivSumForm_ofVec P Q)` 等) で全て `ℝ`. `EReal` や `ENNReal` 値の
  rate 表現は使っていない (これは I-3 で wrapper を作る際に `ℝ` 値前提でよいことを示唆)。

---

## C. 教科書 `\doteq` (exponent equality) の Mathlib 表現候補

教科書 Cover-Thomas: `a_n \doteq b_n ⟺ (1/n) log (a_n / b_n) → 0`. これを **Lean で 1 つの
述語として書く方法** を 3 通り検討。

### C-1. 候補 A: `Tendsto ((1/n) * log (·/·)) atTop (𝓝 0)`

```lean
def DotEq (a b : ℕ → ℝ) : Prop :=
  Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (a n / b n)) atTop (𝓝 0)
```

- **長所**: InformationTheory inline 表現 #4, #6 と **直接型が合う**。`a/b` の log は
  `Real.log_div` で `log a - log b` に展開可能。
- **短所**: `a_n, b_n > 0` の前提を述語の中に書かないと `Real.log` の 0 値で事故。
- **依存**: 既存 lemma で全て構成可能 (`Real.log_div`, `tendsto.div_atTop`, `Real.log`)。

### C-2. 候補 B: `(log ∘ a - log ∘ b) =o[atTop] (·:ℝ)`

```lean
def DotEq (a b : ℕ → ℝ) : Prop :=
  (fun n : ℕ => Real.log (a n) - Real.log (b n)) =o[atTop] (fun n : ℕ => (n : ℝ))
```

- **長所**: 既存 Mathlib notation (`=o[atTop]`) をそのまま使える。`IsLittleO.trans`,
  `IsLittleO.add` 等の豊富な代数を活用できる。`o(n)` 教科書記法とも統合される。
- **短所**: 「`(log a - log b) = o(n)` ⟺ `(1/n) log (a/b) → 0`」の bridge を 1 本書く
  必要 (`isLittleO_iff_tendsto` 経由)。
- **依存**: `Real.log_div`, `Asymptotics.IsLittleO`, `isLittleO_iff_tendsto`.

### C-3. 候補 C: `expGrowthInf = expGrowthSup` (両側で同じ rate)

```lean
def DotEq (a b : ℕ → ℝ≥0∞) : Prop :=
  ExpGrowth.expGrowthInf a = ExpGrowth.expGrowthInf b ∧
  ExpGrowth.expGrowthSup a = ExpGrowth.expGrowthSup b
```

- **長所**: Mathlib `ExpGrowth` の豊富な計算 lemma (`expGrowthInf_pow`,
  `expGrowthInf_const`, `expGrowthInf_exp`, `expGrowth*_mul_le` 等) を直接活用できる。
- **短所**: **値域が `ℕ → ℝ≥0∞`** で、InformationTheory inline (`ℝ` 値) と型が合わない。
  `ENNReal.ofReal` で持ち上げる bridge が必要。さらに値域は `EReal` で、教科書の rate
  値 (`ℝ`) との往復に `EReal.toReal` が要る。
- **依存**: `Mathlib/Analysis/Asymptotics/ExpGrowth.lean` (2025 年新規, まだ Mathlib 内
  でも callsite が限定的)。

### C-4. 推奨 (個別判断はしない、事実列挙のみ)

3 候補のうち **最も Mathlib API 採用率が高いのは候補 B** (`=o[atTop]`)。InformationTheory inline
形 (`Tendsto ((1/n) log ...) → 0` または `0`) との bridge は **1 補題** で済む。`ExpGrowth`
は **`ℝ≥0∞` 値の場合に限り**強力。InformationTheory はすべて `ℝ` 値で書かれているので、
`ExpGrowth` 採用は型変換 cost が大きい。

「教科書 `\doteq` を Mathlib で表現する自然な API」と問われれば、**現状の Mathlib に単一の
名前付き述語は無く、`=o[atTop]` + `Real.log` の組合せで再現するのが筋**。

---

## D. 主要前提条件ボックス (事故になりやすい lemma の前提)

- **`IsLittleO.of_tendsto_div_atTop` / `isLittleO_iff_tendsto`** は **`[NormedField 𝕜]`**
  以上の section 内 lemma (`Mathlib/Analysis/Asymptotics/Lemmas.lean:431-432`)。`f : α → ℝ`
  は OK だが `f : α → ℝ≥0∞` (`NormedField` でない) は不可。`ℝ≥0∞` のままで little-o を
  使いたい場合は `ENNReal.toReal` 経由 + 有限性仮定が要る。
- **`Asymptotics.IsEquivalent.log` は `g → atTop` 必須** (`Mathlib/Analysis/Asymptotics/
  SpecificAsymptotics.lean:134`)。教科書 `\doteq` で `a_n, b_n → 0` (`exp(-n D)` 系) を
  扱う場合は直接適用不可。`1/a_n` を取って `→ atTop` 側に持っていく必要がある。
- **`ExpGrowth.expGrowth*` は `ℕ → ℝ≥0∞` のみ**。`u : ℕ → ℝ` (InformationTheory inline の形)
  には適用不可。`ENNReal.ofReal` で持ち上げる際、**`u n` が `≤ 0` の場合 `ofReal 0 = 0`
  に縮退**し `log 0 = ⊥` で `expGrowthInf` が `⊥` に潰れる事故が起こる。
- **`Real.log` は `x ≤ 0` で `0`** を返す Mathlib 規約。InformationTheory 内では `Real.log P_n.real`
  の形が頻発し、`P_n.real = 0` のとき `Real.log 0 = 0` で式が壊れる。**既存ファイルは
  `hPpos`, `hQpos`, `hP_full` で `> 0` を明示仮定**している (`SanovLDP.lean:473`,
  `:1245`)。
- **`Metric.tendsto_atTop` は `[PseudoMetricSpace α]` + `[Nonempty β] [SemilatticeSup β]`**
  要求。`ℝ` 値 sequence (β = ℕ) には自明だが、`EReal` / `ENNReal` 値 sequence では
  metric ではなく `EMetric.tendsto_atTop` を使う (`Mathlib/Topology/MetricSpace/Closeds.lean:200`)。
- **`tendsto_of_le_liminf_of_limsup_le` は `[ConditionallyCompleteLinearOrder α]
  [TopologicalSpace α] [OrderTopology α]`** 要求。SMB / Sanov の sandwich → `Tendsto` 推論で
  使う最後の一手。`IsBoundedUnder` 仮定はデフォルト `isBoundedDefault` で大抵自動解決される。
- **`Real.exp_mul` の右辺は `exp x ^ y` (rpow)** で、`exp x ^ n` (nat pow) ではない。
  ℕ 指数の rewrite には `Real.exp_nat_mul` を使う (`Mathlib/Analysis/Complex/Exponential.lean:229`)。

---

## E. 自作が必要な要素 (I-3 で書く対象、優先順位順)

### E-1. 教科書 `\doteq` notation + 述語 (新規 def 1 本 + notation 1 行)

候補 B 採用なら:

```lean
/-- Exponent equality: `a_n ≐ b_n` iff `(log a - log b) = o(n)`. -/
def DotEq (a b : ℕ → ℝ) : Prop :=
  (fun n : ℕ => Real.log (a n) - Real.log (b n)) =o[atTop] (fun n : ℕ => (n : ℝ))

scoped[InformationTheory] notation:50 a " ≐ " b => DotEq a b
```

- **工数**: 5〜10 行 (def + notation + 1〜2 個の基本性質 `≐` is equiv relation)
- **落とし穴**: `Real.log 0 = 0` の事故 — `a_n, b_n > 0` を前提に組み込むか、別途
  `hPos : ∀ n, 0 < a n ∧ 0 < b n` を取るか、設計判断。

### E-2. `(1/n) * log` 形 Tendsto → `\doteq` への bridge (1 本)

```lean
lemma dotEq_iff_tendsto_log_div (a b : ℕ → ℝ)
    (hPos : ∀ n, 0 < a n ∧ 0 < b n) :
    DotEq a b ↔
    Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (a n / b n)) atTop (𝓝 0) := by
  sorry  -- isLittleO_iff_tendsto + Real.log_div を結合
```

- **工数**: 15〜25 行 (`Real.log_div` で `log (a/b)` を `log a - log b` に展開、
  `isLittleO_iff_tendsto` の方向で同値化)
- **落とし穴**: `n = 0` の取り扱い (`1/0 = 0` で `Tendsto` の `eventually` に吸収される)

### E-3. closed-form `N(g, ε')` extraction の family-agnostic wrapper

`AEPRate.lean:323` の `exp_neg_mul_lt_of_rate` を **AEP/channel coding 非依存**に再定式化:

```lean
/-- Closed-form rate extraction for `exp(-n·g) < ε'`: for any `g, ε' > 0`, there exists
`N := ⌈max 0 (-log ε' / g)⌉ + 1` such that for all `n ≥ N`, `exp(-n·g) < ε'`. -/
theorem exp_neg_mul_lt_of_pos {g ε' : ℝ} (hg : 0 < g) (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n ≥ N, Real.exp (-(n : ℝ) * g) < ε' := ⟨..., ...⟩
```

- **工数**: 既存の `AEPRate.lean:323-352` (30 行) をそのまま移植。ファイル横断の重複
  callsite (`AEPRate.lean`, `RateDistortionAchievabilityPhaseEStrongFinal.lean:428`,
  `InformationTheory/Probability/TwoSidedExtension.lean:1584`, `SanovLDPEquality.lean:265`,
  `BirkhoffErgodic.lean:1087`, `ConditionalMethodOfTypes.lean:1465`) を 1 本に統合する作業
  込みで 50〜100 行。
- **落とし穴**: 既存 callsite の signature と完全一致するか確認 — `g`, `ε'` の名前は
  family ごとに違うため、抽象側の名前は中立 (`r`, `c`) にする方がよい。

### E-4. `o(n)` / `o(1)` macros (任意)

教科書 `f(n) = o(n)` を Lean で書く際:

```lean
-- 教科書 f(n) = o(n) ⟺ f =o[atTop] (·:ℝ)
notation:50 f:50 " =o(n)" => f =o[atTop] (fun n : ℕ => (n : ℝ))
notation:50 f:50 " =o(1)" => f =o[atTop] (fun _ : ℕ => (1 : ℝ))
```

- **工数**: 3〜5 行 (notation 宣言のみ)
- **落とし穴**: `=o[atTop]` notation の precedence (100) と衝突しないように `50` 以下に。
  `f =o(n)` を Lean パーサ的に問題なく書けるか要検証。

### E-5. `Tendsto` ↔ `IsLittleO of constant` bridge (任意)

教科書では `f_n → c` を `f_n - c = o(1)` と同義に扱う。Mathlib に
`Filter.Tendsto.isLittleO_const_one` のような直接 lemma があるか要確認 (loogle 未調査)。
無ければ 1〜2 行で書ける。

### E-6. 工数感まとめ

- E-1 + E-2: 20〜35 行
- E-3: 50〜100 行 (既存 callsite 統合分込み)
- E-4: 3〜5 行
- E-5: 5〜10 行
- 合計: **80〜150 行** + 既存 inline callsite migration 数十箇所
- ロードマップ予想 (300-500 行) より小さく収まる可能性。**migration 込みでも 300 行
  以内**が現実的。

---

## F. 撤退ラインへの距離

本タスクには上位 plan 文書がまだ存在しない (I-3 計画起草前)。以下は I-3 計画起草時に
採用判断する **新規撤退ライン候補**:

- **教科書 `\doteq` を 1 つの述語で書こうとすると、`Real.log` の `≤ 0` 規約と `a_n → 0`
  ケースの両立が複雑になり、定義に強い仮定 (`∀ n, 0 < a n`) が要る**場合 → 縮退案: `\doteq`
  notation を `DotEq` (述語) ではなく `=o[atTop]` の直書きで通す。新規 def を作らない。
- **`ExpGrowth` を採用しようとして `ℝ≥0∞`/`EReal` 変換 bridge に 100+ 行**かかる場合 →
  縮退案: `ExpGrowth` 採用を見送り、`=o[atTop]` + `Real.log` のみで通す。
- **既存 `AEPRate.lean:323` を family-agnostic 化しようとしたら、call-by-call で `g` の
  名前 / 順序 / `Nat.ceil` の境界処理が微妙にズレていて統合できない**場合 → 縮退案:
  `AEPRate.lean` をそのまま残し、新規ファイルに **薄い alias** だけ用意 (`exp_decay_N := AEPRate.exp_neg_mul_lt_of_rate`)。重複コードは温存。
- **notation `≐` の Unicode が一部ツール / エディタで誤入力**される場合 → 縮退案: ASCII
  `=.[atTop]=` 形 (precedence 50) に降ろす。

---

## G. I-3 着手 skeleton (参考)

> **編集境界**: 本ファイルは在庫調査のみ。skeleton は計画起草 (`lean-planner`) と実装
> (`lean-implementer`) の参考用としてだけ示す。本サブエージェントは Lean ファイルを書かない。

`InformationTheory/Asymptotic/Framework.lean` (仮称) の出だし:

```lean
import Mathlib.Analysis.Asymptotics.Defs              -- IsLittleO, IsBigO, =o[atTop]
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent  -- IsEquivalent, ~[l]
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics    -- IsEquivalent.log
import Mathlib.Analysis.Asymptotics.Lemmas                 -- isLittleO_iff_tendsto, natCast_atTop
import Mathlib.Analysis.SpecialFunctions.Log.Basic         -- Real.log, log_div, log_le_log_iff
import Mathlib.Analysis.Complex.Exponential                -- Real.exp_nat_mul, exp_le_exp
import Mathlib.Topology.MetricSpace.Pseudo.Defs            -- Metric.tendsto_atTop
import Mathlib.Topology.Order.LiminfLimsup                 -- tendsto_of_le_liminf_of_limsup_le

namespace InformationTheory.Asymptotic

open Asymptotics Filter Topology Real

/-- **Exponent equality (textbook `\doteq`)**: `a_n ≐ b_n` if
  `Real.log (a n) - Real.log (b n) = o(n)` along `atTop`. -/
def DotEq (a b : ℕ → ℝ) : Prop :=
  (fun n : ℕ => Real.log (a n) - Real.log (b n)) =o[atTop] (fun n : ℕ => (n : ℝ))

@[inherit_doc] scoped notation:50 a " ≐ " b => DotEq a b

/-- Bridge: `DotEq` is equivalent to `Tendsto ((1/n) * log (a/b)) → 0` under positivity. -/
lemma dotEq_iff_tendsto (a b : ℕ → ℝ) (hPos : ∀ n, 0 < a n ∧ 0 < b n) :
    DotEq a b ↔
    Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (a n / b n)) atTop (𝓝 0) := by
  sorry

/-- **Closed-form `N` for `exp(-n·g) < ε'`** (rate extraction wrapper).
    For `g, ε' > 0`, `N := ⌈max 0 (-log ε' / g)⌉ + 1` works. -/
theorem exp_decay_N_of_pos {g ε' : ℝ} (hg : 0 < g) (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n ≥ N, Real.exp (-(n : ℝ) * g) < ε' := by
  sorry  -- 既存 AEPRate.lean:323 をここに移植

-- 任意: notation 略記
-- scoped notation:50 f " =o(n)" => f =o[atTop] (fun n : ℕ => (n : ℝ))
-- scoped notation:50 f " =o(1)" => f =o[atTop] (fun _ : ℕ => (1 : ℝ))

end InformationTheory.Asymptotic
```

---

## H. まとめ

- **Mathlib `Asymptotics` 系 (`IsBigO`, `IsLittleO`, `IsTheta`, `IsEquivalent`) は完備**で
  notation も揃う。教科書 `O(n)`, `o(n)`, `Θ(n)`, `~` をすべて 1 行で記述可能。
- **`ExpGrowth.expGrowthInf` / `expGrowthSup`** (2025 年新規) が教科書 `\doteq` の右辺に
  近い概念を提供するが、**`ℕ → ℝ≥0∞` → `EReal`** で InformationTheory inline の `ℝ` 値表現と
  型が合わない。bridge cost が高い。
- **教科書 `\doteq` (`a_n ≐ b_n`) に対応する単一述語は Mathlib に不在**。`=o[atTop]` +
  `Real.log` の組合せで再現するのが現実的 (推奨候補 B)。
- **InformationTheory 内の漸近表現は 2 系統に分かれている**: (a) `Tendsto ((1/n) log) → -C` の
  exponent rate 形 (AEP, SMB, Stein, Sanov LDP の 6〜8 ファイル)、(b) `∃ N, ∀ n ≥ N, ...`
  の closed-form N extraction 形 (`AEPRate.lean` 905 行 + 7 ファイル横断 `Metric.tendsto_atTop`
  callsite)。
- **`AEPRate.lean` (905 行) は既に I-3 相当の closed-form lemma を AEP 特化で持っており**、
  I-3 wrapper の主要作業は (a) これを family-agnostic に再定式化、(b) `\doteq` notation
  と bridge の整備、で **新規 80〜150 行**程度に収まる見込み (ロードマップ予想 300-500 行
  より小)。
- 最大の設計判断: (a) `\doteq` を `DotEq` 述語にするか `=o[atTop]` 直書きで通すか、
  (b) `ExpGrowth` 採用の是非、(c) `o(n)` notation を `=o[atTop] (·:ℝ)` のままにするか
  macros を被せるか。

---

### 関連ファイル

- `Mathlib/Analysis/Asymptotics/Defs.lean` — `IsBigO`, `IsLittleO`, `IsTheta`,
  `IsEquivalent` 定義 + notation
- `Mathlib/Analysis/Asymptotics/Lemmas.lean` — `isLittleO_iff_tendsto`,
  `IsBigO/IsLittleO.natCast_atTop`, `IsLittleO.of_tendsto_div_atTop`
- `Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean` — `IsEquivalent` 性質,
  `isEquivalent_const_iff_tendsto`
- `Mathlib/Analysis/Asymptotics/SpecificAsymptotics.lean` — `IsEquivalent.log`,
  `cesaro` 系
- `Mathlib/Analysis/Asymptotics/ExpGrowth.lean` — `expGrowthInf` / `expGrowthSup`
  (2025 新規、`ℕ → ℝ≥0∞ → EReal`)
- `Mathlib/Analysis/Asymptotics/LinearGrowth.lean` — `linearGrowthInf` / `linearGrowthSup`
  (一般 ConditionallyCompleteLattice)
- `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` — `Real.log_mul/div/pow`,
  `log_le_log_iff`, `tendsto_log_atTop`, `isLittleO_log_id_atTop`
- `Mathlib/Analysis/SpecialFunctions/Log/ENNRealLog.lean` — `ENNReal.log : ℝ≥0∞ → EReal`
- `Mathlib/Analysis/Complex/Exponential.lean` — `Real.exp_nat_mul`, `Real.exp_le_exp`
- `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:901` — `Metric.tendsto_atTop` (ε-N 抽出)
- `Mathlib/Topology/Order/LiminfLimsup.lean:299, :306` — `tendsto_of_liminf_eq_limsup`,
  `tendsto_of_le_liminf_of_limsup_le` (sandwich)
- `InformationTheory/Shannon/AEPRate.lean` — 905 行、closed-form `N` lemma 集 (I-3 の前駆体)
- `InformationTheory/Shannon/AEP.lean:162, :190` — AEP a.s. / probability rate
- `InformationTheory/Shannon/SMBAlgoetCover.lean:2840` — `shannon_mcmillan_breiman` rate
- `InformationTheory/Shannon/StrongStein.lean:498` — `stein_strong_lemma` (Tendsto → K)
- `InformationTheory/Shannon/Stein.lean:1390` — `stein_lemma` (sandwich form)
- `InformationTheory/Shannon/SanovLDPEquality.lean:1243` — `sanov_ldp_equality` rate
- `InformationTheory/Shannon/EntropyRate.lean:432, :466` — `entropyRate_exists_of_stationary`,
  `entropyRate_eq_lim_condEntropy`
