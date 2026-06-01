# Cover & Thomas Ch.2 未形式化ギャップ — Mathlib + Common2026 在庫調査

> 対象: `docs/textbook/ch02-entropy.md:517-531`「本章で未形式化の項目」が挙げる
> 2.6 / 2.7 / 2.9。本ファイルは在庫調査のみ (実装・計画起草はしない)。
> フォーマット参照: `docs/shannon/shannon-mathlib-inventory.md`。

## 一行サマリ

**3 ブロックのうち実体ベースでは 2.6 (klDivPmf full-iff) と 2.7 (log-sum) は Common2026 内に完成済 (0 sorry) で再リンクするだけ。真に未実装なのは 2.9 充足統計量のみ。その 2.9 も「I(θ;X)=I(θ;T(X)) の等号」は既存資産 (`mutualInfo_le_of_markov` + `mutualInfo_le_of_postprocess`) の 2 方向 antisymm で閉じる見込み — 不足は `IsSufficientStatistic` 定義 (1 個) と決定論写像 T を Markov chain 形に橋渡しする補題のみ。Mathlib に統計的 sufficiency の定義・定理は 0 件 (圏論版 MarkovCategory の bibliographic 言及のみ)。撤退ライン: 親計画なし (ピンポイント追加タスク)、新規撤退ライン提案を末尾に。既存率 約 80%、自作必要 2〜3 件。**

---

## ブロック A — 充足統計量 (2.9) ※最重要・最大の不確実性

### A-0. Cover-Thomas 主張と狙う Lean signature

T が θ に対し sufficient ⟺ `θ → T(X) → X` が Markov chain ⟹ **I(θ;X) = I(θ;T(X))**。
ここで T(X) = f(X) は X の決定論的関数 (statistic)。狙う形:

```lean
theorem mutualInfo_eq_of_sufficient
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace Θ] [Nonempty Θ] [StandardBorelSpace X] [Nonempty X]
    (θ : Ω → Θ) (Xs : Ω → X) {f : X → T} (hf : Measurable f)
    (hθ : Measurable θ) (hXs : Measurable Xs)
    (hsuff : IsSufficientStatistic μ θ Xs f) :   -- ← 定義は下記 A-3
    mutualInfo μ θ Xs = mutualInfo μ θ (f ∘ Xs)
```

証明戦略 (pseudo-Lean):
```
-- (≤ 方向) sufficient ⟹ θ → f∘Xs → Xs が Markov ⟹ mutualInfo_le_of_markov
have h_le : mutualInfo μ θ Xs ≤ mutualInfo μ θ (f∘Xs) :=
  mutualInfo_le_of_markov μ θ (f∘Xs) Xs hθ (hf.comp hXs) hXs hsuff.markov  -- ※引数順注意
-- (≥ 方向) f∘Xs = Xs の決定論的後処理 ⟹ DPI
have h_ge : mutualInfo μ θ (f∘Xs) ≤ mutualInfo μ θ Xs :=
  mutualInfo_le_of_postprocess μ θ Xs hθ hXs hf
exact le_antisymm h_ge h_le
```

### A-1. Mathlib に統計的 sufficiency があるか — 結論: **0 件**

| クエリ | 結果 (verbatim) |
|---|---|
| loogle `"SufficientStatistic"` | `unknown identifier 'SufficientStatistic'` (= **Found 0**) |
| loogle `"IsSufficient"` | `unknown identifier 'IsSufficient'` (= **Found 0**) |
| `rg "sufficient statistic\|IsSufficient\|SufficientStatistic\|Fisher.Neyman\|factorization theorem"` over `Mathlib/Probability/` | hit は **bibliographic 言及のみ** (`Kernel/Deterministic.lean:45`, `Kernel/Category/SFinKer.lean:25`, `Kernel/Category/Stoch.lean:26` — いずれも fritz2020 圏論論文の参考文献コメント、定義・定理ではない) |

**Mathlib に Neyman-Fisher 因子分解 / sufficient statistic の定義も定理も存在しない。** これは真の Mathlib 壁だが、Common2026 の Markov chain / DPI 資産が代替経路を提供する (下記)。

### A-2. Common2026 既存資産 — verbatim signature

#### `IsMarkovChain` (定義)
- **`Common2026/Shannon/CondMutualInfo.lean:73`**
```lean
def IsMarkovChain (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) : Prop :=
  μ.map (fun ω => (Zc ω, Xs ω, Yo ω))
    = (μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ))
```
- 引数順 **`Xs Zc Yo`** = chain `Xs → Zc → Yo` (中継が **第 2 引数 `Zc`**)。
- 型クラス前提 (instance, verbatim): `[IsFiniteMeasure μ]` `[StandardBorelSpace X]` `[Nonempty X]` `[StandardBorelSpace Y]` `[Nonempty Y]`。
- **注**: 定義は γ-form (joint factorization)。`[StandardBorelSpace Z]` (中継の型) は要求していない (Ω 制約も無い)。

#### `mutualInfo_le_of_markov`
- **`Common2026/Shannon/CondMutualInfo.lean:385`**
```lean
theorem mutualInfo_le_of_markov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo
```
- explicit 引数順: `μ Xs Zc Yo hXs hZc hYo hmarkov`。
- 型クラス前提 (verbatim): `[IsProbabilityMeasure μ]` `[StandardBorelSpace X]` `[Nonempty X]` `[StandardBorelSpace Y]` `[Nonempty Y]`。
- 結論形 verbatim: `mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo`。
- **意味**: chain `Xs → Zc → Yo` で `I(Xs; Yo) ≤ I(Zc; Yo)` (両端 Xs, Yo に対し中継 Zc が情報量を上から押さえる)。

#### `condMutualInfo_eq_zero_of_markov`
- **`Common2026/Shannon/CondMutualInfo.lean:359`**
```lean
theorem condMutualInfo_eq_zero_of_markov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    condMutualInfo μ Xs Yo Zc = 0
```
- 結論形 verbatim: `condMutualInfo μ Xs Yo Zc = 0`。
- 完成状態: **0 sorry** (`mutualInfo_le_of_markov` の内部補題)。

#### `mutualInfo_le_of_postprocess` (DPI)
- **`Common2026/Shannon/DPI.lean:142`**
```lean
theorem mutualInfo_le_of_postprocess
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo)
    {f : Y → Z} (hf : Measurable f) :
    mutualInfo μ Xs (f ∘ Yo) ≤ mutualInfo μ Xs Yo
```
- explicit 引数順: `μ Xs Yo hXs hYo {f} hf` (f は implicit、hf から推論)。
- 型クラス前提 (verbatim): **`[IsFiniteMeasure μ]` のみ** (StandardBorelSpace 不要・Nonempty 不要・Fintype 不要)。
- 結論形 verbatim: `mutualInfo μ Xs (f ∘ Yo) ≤ mutualInfo μ Xs Yo`。
- **意味**: **第 2 引数** Yo を決定論写像 f で後処理すると I が減る。`I(Xs; f∘Yo) ≤ I(Xs; Yo)`。
- 完成状態: **0 sorry**。核補題 `klDiv_map_le` (DPI.lean:54) も 0 sorry。

#### `klDiv_map_le` (DPI 核補題)
- **`Common2026/Shannon/DPI.lean:54`**
```lean
theorem klDiv_map_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν
```
- 結論形 verbatim: `klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν`。0 sorry。

#### `mutualInfo` (定義) / `mutualInfo_comm`
- **`Common2026/Shannon/MutualInfo.lean:37`**
```lean
noncomputable def mutualInfo
    (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞ :=
  klDiv (μ.map (fun ω => (Xs ω, Yo ω))) ((μ.map Xs).prod (μ.map Yo))
```
- 値型 `ℝ≥0∞`。定義レベルに型クラス前提なし。
- **`Common2026/Shannon/MutualInfo.lean:96`** `mutualInfo_comm`:
```lean
theorem mutualInfo_comm
    (μ : Measure Ω) [IsFiniteMeasure μ] (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    mutualInfo μ Xs Yo = mutualInfo μ Yo Xs
```
- 結論形 verbatim: `mutualInfo μ Xs Yo = mutualInfo μ Yo Xs`。前提 `[IsFiniteMeasure μ]`。0 sorry。

#### Mathlib `condDistrib` / `condDistrib_comp` (sufficiency 定義の素材)
- **`Mathlib/Probability/Kernel/CondDistrib.lean:64`** (Phase 4 inventory より):
```lean
noncomputable irreducible_def condDistrib (Y : α → Ω) (X : α → β) (μ : Measure α)
    [IsFiniteMeasure μ] : Kernel β Ω
```
- **`Mathlib/Probability/Kernel/CondDistrib.lean:183`** `condDistrib_comp`:
  `{Ω' : Type*} {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω'] ...` —
  既に `CondMutualInfo.lean` / `DPI` 系で利用済 (詳細 verbatim は Phase 4 inventory)。
  T(X)=f(X) の条件付き分布の Dirac 性を出すのに使える可能性 (sufficiency ⟺ markov の片方向で必要)。

### A-3. 等号 I(θ;X)=I(θ;T(X)) を出す経路の評価

記号: θ = `Θ`, X = `Xs : Ω → X`, T = `f : X → T'`, T(X) = `f ∘ Xs`。

#### (≤ 方向) `I(θ;X) ≤ I(θ;T(X))`
- Cover-Thomas の sufficient ⟺ `θ → T(X) → X` が Markov chain。
- `mutualInfo_le_of_markov` を **chain `Xs → (f∘Xs) → θ`** に適用したい。
  `IsMarkovChain μ Xs (f∘Xs) θ` (引数順 `Xs Zc Yo` で `Zc = f∘Xs` が中継)。
  結論は `mutualInfo μ Xs θ ≤ mutualInfo μ (f∘Xs) θ`。
- `mutualInfo_comm` で両辺を入れ替えれば `mutualInfo μ θ Xs ≤ mutualInfo μ θ (f∘Xs)` = **(≤ 方向)**。
- **判定: 経路は揃う。** 必要なのは「sufficient ⟹ `IsMarkovChain μ Xs (f∘Xs) θ`」を出す橋渡し
  (= 充足統計量の定義をこの markov 形にすれば自明、A-4 参照)。

#### (≥ 方向) `I(θ;T(X)) ≤ I(θ;X)`
- `T(X) = f(X)` は X の決定論的後処理。`mutualInfo_le_of_postprocess` は **第 2 引数**を後処理する形:
  `mutualInfo μ θ (f ∘ Xs) ≤ mutualInfo μ θ Xs`。
  適用: `mutualInfo_le_of_postprocess μ θ Xs hθ hXs hf` で **そのまま (≥ 方向)** が出る。
- **判定: 完全に既存資産で閉じる。追加補題ゼロ。** `[IsFiniteMeasure μ]` のみ要求。
- **欠けている bridge: なし** (この方向)。

#### antisymm
- `ℝ≥0∞` 上 `le_antisymm h_ge h_le` で等号。両方向が揃うので **等号は閉じる**。

### A-4. 型クラス前提の集約 (主定理 signature に漏れ込むもの)

(≤ 方向の `mutualInfo_le_of_markov` が最重) 主定理は以下を要求する:
- `[IsProbabilityMeasure μ]` ← `mutualInfo_le_of_markov` (DPI 側は `[IsFiniteMeasure μ]` で弱いが、強い方が支配)
- `[StandardBorelSpace X]` `[Nonempty X]` (= X の型)
- `[StandardBorelSpace Θ]` `[Nonempty Θ]` (= Yo 位置の型、`mutualInfo_le_of_markov` の `Y`)
- `IsMarkovChain` 定義は `[StandardBorelSpace _]` `[Nonempty _]` を両端 (Xs, Yo 位置) に要求。
- T'(= f の終域) の型: `mutualInfo_le_of_markov` の中継 `Zc : Ω → Z` は **型クラス前提なし**
  (`{Z : Type*} [MeasurableSpace Z]` のみ)。⟹ T' に StandardBorel/Nonempty は **不要**。
- **`f : X → T'` の `Measurable f`** が決定論写像の必須 regularity。

> **leak 注意**: `mutualInfo_le_of_markov` が `[IsProbabilityMeasure μ]` を要求するため、
> 主定理も probability measure 固定。DPI 側は finite で足りるが弱い方には合わせられない。
> X 側と θ 側 (Yo 位置) に `[StandardBorelSpace]` `[Nonempty]` が両方乗る。これは
> `mutualInfo_eq_zero_iff_indep` (Fintype 形) と違い **Fintype 不要**だが代わりに標準 Borel を要求。

### **充足統計量主定理の証明可否判定**

既存資産だけで **`I(θ;X) = I(θ;T(X))` は閉じる**。両方向が揃う: (≥) は `mutualInfo_le_of_postprocess` で追加補題ゼロ、(≤) は `mutualInfo_le_of_markov` + `mutualInfo_comm` で閉じる。`le_antisymm` で等号。**唯一の欠けピース**は「sufficient という仮定をどう Lean 化するか」だが、CLAUDE.md「Mathlib-shape-driven Definitions」に従えば答えは明快: **`IsSufficientStatistic` を `mutualInfo_le_of_markov` の結論形に直結する markov 形で定義する**。すなわち
```lean
def IsSufficientStatistic
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Θ] [Nonempty Θ]
    (θ : Ω → Θ) (Xs : Ω → X) (f : X → T') : Prop :=
  IsMarkovChain μ Xs (fun ω => f (Xs ω)) θ   -- chain  X → T(X) → θ
```
こう定義すれば `hsuff` がそのまま `mutualInfo_le_of_markov` の `hmarkov` 引数になり、bridge 補題は不要。教科書的な Neyman-Fisher 因子分解形 (条件付き分布が θ に依存しない) との同値は **将来の別補題**として残す (Mathlib 壁、A-1 で 0 件確認)。
**この markov-form 定義を採れば主定理は 8〜15 行で閉じる見込み。** 逆に教科書因子分解形を直接 def 化すると `condDistrib` の θ-非依存性から markov を導く 50〜100 行の bridge が必要になり、CLAUDE.md の red flag に該当する。

---

## ブロック B — klDivPmf 等号条件 full iff (2.6)

### 結論: full iff は **Common2026 内に完成済 (0 sorry)**。再リンクのみ。

#### `klDivPmf` (定義)
- **`Common2026/Shannon/CsiszarProjection.lean:56`**
```lean
noncomputable def klDivPmf (P Q : α → ℝ) : ℝ :=
  ∑ a : α, Q a * klFun (P a / Q a)
```
- section 変数 (verbatim): `variable {α : Type*} [Fintype α] [DecidableEq α]` (CsiszarProjection.lean:46)。値型 `ℝ`。

#### `klDivPmf_nonneg`
- **`Common2026/Shannon/CsiszarProjection.lean:62`**
```lean
lemma klDivPmf_nonneg (P Q : α → ℝ)
    (hP : ∀ a, 0 ≤ P a) (hQ : ∀ a, 0 ≤ Q a) :
    0 ≤ klDivPmf P Q
```
- 結論形 verbatim: `0 ≤ klDivPmf P Q`。0 sorry。

#### `klDivPmf_self_eq_zero` (片方向)
- **`Common2026/Shannon/Chernoff.lean:231`**
```lean
lemma klDivPmf_self_eq_zero
    (P : α → ℝ) (hP_pos : ∀ a, 0 < P a) :
    klDivPmf P P = 0
```
- 結論形 verbatim: `klDivPmf P P = 0`。0 sorry。前提 `(hP_pos : ∀ a, 0 < P a)`。

#### `klDivPmf_eq_zero_iff_pmf` (**full iff — 既存・完成**)
- **`Common2026/Shannon/MaxEntropyConstrained.lean:287`**
```lean
lemma klDivPmf_eq_zero_iff_pmf
    {P Q : α → ℝ} (hP : P ∈ stdSimplex ℝ α) (_hQ : Q ∈ stdSimplex ℝ α)
    (hQ_pos : ∀ a, 0 < Q a) :
    klDivPmf P Q = 0 ↔ P = Q
```
- explicit/implicit: `{P Q}` implicit、`hP hQ hQ_pos` explicit。
- 結論形 verbatim: `klDivPmf P Q = 0 ↔ P = Q`。**0 sorry、完成済**。
- 前提: P, Q ともに `stdSimplex ℝ α` (正規化 pmf)、Q は full support (`hQ_pos`)。
- 証明は `klFun_eq_zero_iff` (Mathlib KLFun.lean:151 `klFun x = 0 ↔ x = 1`, `(hx : 0 ≤ x)`) を per-coordinate に適用。strict convexity は **不要だった** (per-term nonneg + sum=0 で各項 0)。

#### Mathlib 参考 (測度版、pmf 版設計の参考)
- **`Mathlib/InformationTheory/KullbackLeibler/Basic.lean:377`** `klDiv_eq_zero_iff`:
```lean
lemma klDiv_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ ν = 0 ↔ μ = ν
```
- 結論形 verbatim: `klDiv μ ν = 0 ↔ μ = ν`。前提 `[IsFiniteMeasure μ]` `[IsFiniteMeasure ν]`。
- **`Basic.lean:78`** `klDiv_self`:
```lean
lemma klDiv_self (μ : Measure α) [SigmaFinite μ] : klDiv μ μ = 0
```
- 結論形 verbatim: `klDiv μ μ = 0`。前提 `[SigmaFinite μ]`。

#### 補助 (strict convexity — 今回の iff には不要だが参考)
- loogle `Real.strictConvexOn_mul_log` → `Found one` (`Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean`)。
- `klFun_eq_zero_iff` (KLFun.lean:151) で per-coordinate に閉じるため strict convexity 経路は使われていない。

> **2.6 まとめ**: `klDivPmf P Q = 0 ↔ P = Q` は `klDivPmf_eq_zero_iff_pmf` として既存・0 sorry。
> ch02 draft の「2.6 未形式化」記述は **MaxEntropyConstrained.lean:287 への再リンクで解消可能**。
> 測度版 `D(p‖q) ≥ 0` の非負性も `klDivPmf_nonneg` + Mathlib `klDiv_eq_zero_iff` で揃う。

---

## ブロック C — log-sum 再リンク (2.7) ※確認のみ

### 結論: 2 つとも **完成済 (0 sorry)**。再リンクのみ。

#### `log_sum_inequality`
- **`Common2026/Shannon/LZ78ZivEntropyBridge.lean:71`**
```lean
theorem log_sum_inequality
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
      ≤ ∑ i ∈ s, a i * Real.log (a i / b i)
```
- 結論形 verbatim: `(∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) ≤ ∑ i ∈ s, a i * Real.log (a i / b i)`。
- 前提: `(ha : ∀ i ∈ s, 0 ≤ a i)` `(hb : ∀ i ∈ s, 0 < b i)` (b は strict positive)。
- 完成状態: **0 sorry** (証明本体は `Real.convexOn_mul_log.map_sum_le` 経由)。

#### `log_sum_inequality_negMulLog`
- **`Common2026/Fano/DPI.lean:45`**
```lean
lemma log_sum_inequality_negMulLog {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (h_ac : ∀ i ∈ s, b i = 0 → a i = 0) :
    ∑ i ∈ s, (Real.negMulLog (a i) + a i * Real.log (b i))
      ≤ Real.negMulLog (∑ i ∈ s, a i)
          + (∑ i ∈ s, a i) * Real.log (∑ i ∈ s, b i)
```
- 結論形 verbatim: 上記 2 行。
- 前提: `(ha : ∀ i ∈ s, 0 ≤ a i)` `(hb : ∀ i ∈ s, 0 ≤ b i)` `(h_ac : ∀ i ∈ s, b i = 0 → a i = 0)`
  (b は **nonneg のみ**、absolute-continuity 条件 `h_ac` で b=0 のケースを許容 — `log_sum_inequality` より広い)。
- 完成状態: **0 sorry**。

> **2.7 まとめ**: log-sum 不等式は **2 形** が既存・完成。
> strict positive 形 (`LZ78ZivEntropyBridge.lean:71`) と nonneg + AC 形 (`Fano/DPI.lean:45`)。
> ch02 draft への再リンクは前者を採用すれば教科書 (2.7) の standard form と一致。

---

## 自作が必要な要素 (優先度順)

| # | 要素 | 推奨実装 | 工数感 | 落とし穴 |
|---|---|---|---|---|
| 1 | `IsSufficientStatistic` 定義 | `IsMarkovChain μ Xs (f∘Xs) θ` の markov-form (A-4 参照) | 3〜5 行 | 教科書因子分解形を直接 def 化しないこと (red flag、50-100 行 bridge を誘発) |
| 2 | `mutualInfo_eq_of_sufficient` 主定理 | (≥) `mutualInfo_le_of_postprocess` + (≤) `mutualInfo_le_of_markov` + `mutualInfo_comm` の antisymm | 8〜15 行 | 引数順: `IsMarkovChain` は `Xs Zc Yo` (中継第 2)、`mutualInfo_le_of_markov` 結論は `μ Xs Yo ≤ μ Zc Yo`。f∘Xs を中継に置く |
| 3 (optional) | Neyman-Fisher 同値補題 | markov-form ⟺ 条件付き分布 θ-非依存 | 50〜100 行 | Mathlib 壁 (A-1)。主定理には不要なので後回し可。`@residual(wall:sufficiency-factorization)` 候補 |
| — | 2.6 / 2.7 再リンク | ch02 draft の prose を既存 declaration に紐付け | docs のみ | 実装ゼロ。draft 編集タスク |

---

## Mathlib 壁の列挙 (`@residual(wall:…)` 対象)

| 壁 | loogle 確認 | shared sorry 補題化 | 主定理への影響 |
|---|---|---|---|
| **統計的 sufficient statistic の定義・定理** | `"SufficientStatistic"` → Found 0 / `"IsSufficient"` → Found 0 / `rg` Probability → bibliographic のみ | **不要** — markov-form 定義 (自作要素 1) で回避。Neyman-Fisher 同値 (自作要素 3) を将来やる場合のみ shared 壁 | **回避可能**。主定理は markov-form で閉じるので壁は触らない |

唯一の真の Mathlib 壁 (sufficiency 定義) は **markov-form への redefine で回避** できるため、主定理 (`mutualInfo_eq_of_sufficient`) は `sorry` / `@residual` ゼロで完成見込み。Neyman-Fisher 因子分解の同値補題だけが壁の残り (主定理には load-bearing でない、optional)。

---

## 撤退ラインへの距離

親計画ファイルは指定されていない (ch02 draft の未形式化マーカー解消というピンポイント追加タスク)。よって既存撤退ラインへの抵触は **なし**。新規撤退ラインを提案:

- **撤退ライン S-1**: 自作要素 2 (主定理) が「`IsMarkovChain μ Xs (f∘Xs) θ` を `mutualInfo_le_of_markov` の `hmarkov` にそのまま渡せない」型 mismatch で 1 週間溶けた場合
  → markov-form 定義 (自作要素 1) を見直す。`condDistrib (f∘Xs)` 周りの `[StandardBorelSpace]` leak が原因なら、主定理を `[Fintype]` 有限アルファベット版に縮退 (`mutualInfo_ne_top` 系の Fintype 経路に寄せる)。撤退口は主定理 body の `sorry` + `@residual(plan:ch2-sufficiency)`、定義の load-bearing bundling は禁止。
- **撤退ライン S-2**: Neyman-Fisher 同値 (自作要素 3) に着手し 2 週間で書けない場合
  → optional なので主定理を markov-form 定義のまま publish、同値は `@residual(wall:sufficiency-factorization)` で残す (shared sorry 補題候補だが現状 1 file なので集約不要)。

---

## 着手 skeleton

`Common2026/Shannon/SufficientStatistic.lean` の出だし (新規 file 想定):

```lean
import Mathlib.Probability.Kernel.CondDistrib
import Common2026.Meta.EntryPoint
import Common2026.Shannon.MutualInfo
import Common2026.Shannon.DPI
import Common2026.Shannon.CondMutualInfo

/-!
# Sufficient statistics and mutual information (Cover-Thomas 2.9)

T が θ に対し sufficient (= chain `X → T(X) → θ` が Markov) ⟹ `I(θ; X) = I(θ; T(X))`。
markov-form 定義により `mutualInfo_le_of_markov` + `mutualInfo_le_of_postprocess` の
antisymm で閉じる。在庫: `docs/shannon/ch2-gaps-inventory.md` ブロック A。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Θ : Type*} [MeasurableSpace Θ]
variable {X : Type*} [MeasurableSpace X]
variable {T' : Type*} [MeasurableSpace T']

/-- 充足統計量 (markov-form): chain `Xs → f∘Xs → θ` が Markov chain。
教科書の Neyman-Fisher 因子分解形との同値は将来の別補題 (Mathlib 壁)。 -/
def IsSufficientStatistic
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Θ] [Nonempty Θ]
    (θ : Ω → Θ) (Xs : Ω → X) (f : X → T') : Prop :=
  IsMarkovChain μ Xs (fun ω => f (Xs ω)) θ

/-- Cover-Thomas 2.9: sufficient ⟹ `I(θ; X) = I(θ; T(X))`. -/
@[entry_point]
theorem mutualInfo_eq_of_sufficient
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Θ] [Nonempty Θ]
    (θ : Ω → Θ) (Xs : Ω → X) {f : X → T'}
    (hθ : Measurable θ) (hXs : Measurable Xs) (hf : Measurable f)
    (hsuff : IsSufficientStatistic μ θ Xs f) :
    mutualInfo μ θ Xs = mutualInfo μ θ (fun ω => f (Xs ω)) := by
  sorry  -- @residual(plan:ch2-sufficiency)

end InformationTheory.Shannon
```

(注: skeleton は調査用の形提示。実装は lean-implementer の仕事。`T'` への型クラス前提が
`mutualInfo_le_of_markov` の中継 `Z` 側で **不要**なことは A-4 で確認済 — `[MeasurableSpace T']` のみで足りる。)
