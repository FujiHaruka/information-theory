# Shannon: Stein converse (Phase C/D) Mathlib インベントリ サブ計画

> **Parent**: [`stein-converse-plan.md`](stein-converse-plan.md) §Phase 0
>
> 親 inventory: [`stein-mathlib-inventory.md`](stein-mathlib-inventory.md) (achievability 用、6 軸)
>
> 本 inventory はその **delta** に絞る。Phase A〜B (achievability) が既に依存している
> `klDiv` / `MeasureTheory.llr` / `MeasureTheory.Measure.pi` 系は親で確定済みなので
> 再記載しない。Phase C/D で **新たに必要 / 親で未確定** の 5 軸のみを以下に記録。

<!--
雛形メモ: CLAUDE.md「Subagent Inventory of Mathlib Lemmas」規約に従う
- file:line / 完全署名 / 引数型 / 結論形 verbatim
- `[..]` プレリク鍵括弧は **必ず** verbatim 保持 (paraphrase 禁止)
- "無し" でも探索した query を記録 (negative grep / loogle 結果は資産)
-->

## 進捗

- [x] 軸 1: Pi 化 KL chain rule (`klDiv (Measure.pi P) (Measure.pi Q) = n · klDiv P Q`)
- [x] 軸 2: KL の Data Processing Inequality (DPI) ─ Bernoulli reduction の核
- [x] 軸 3: Bernoulli KL の log-sum 形下界 (`mul_log_le_klDiv` 系)
- [x] 軸 4: `Tendsto` / `-(1/n) * log f n` の squeeze API
- [x] 軸 5: `klDiv P Q < ∞` の finiteness API (achievability で立つか)

## ゴール / Approach

Phase C (converse) + Phase D (`Tendsto` 統合) 着手前に **Pi 化 chain rule / DPI / Tendsto squeeze** の 3 軸を Mathlib 側で確定させ、自前構築量を見積り直す。

**結論先取り**:

- **軸 1 (Pi 化 chain rule) は完全不在** ─ `klDiv (Measure.pi μs) (Measure.pi νs)` 形は loogle 0 件、自前 induction 必須 (40〜80 行見積)。`klDiv_compProd_eq_add` + `klDiv_compProd_left` + `MeasurableEquiv.piFinSuccAbove` (`measurePreserving_piFinSuccAbove`) で組める
- **軸 2 (DPI) は本 project 既存** ─ `InformationTheory/Shannon/DPI.lean` の `klDiv_map_le` が **`private`** で立っている (50〜100 行、Jensen + condExp で構築済み)。Phase C で **public 化 (or 別ファイルに公開コピー)** が必要
- **軸 3 (log-sum 下界) は Mathlib 既存** ─ `mul_log_le_klDiv` / `mul_log_le_toReal_klDiv` (`Mathlib/InformationTheory/KullbackLeibler/Basic.lean:346,360`) で `μ.real univ * log(μ.real univ / ν.real univ) + ν.real univ - μ.real univ ≤ klDiv μ ν` が直接立つ。**Bernoulli 専用補題は不在**だが、上の log-sum 形を `Bernoulli(P^n s, P^n s^c)` vs `Bernoulli(Q^n s, Q^n s^c)` に直接適用すれば代用可
- **軸 4 (`Tendsto` squeeze) は Mathlib 既存** ─ `tendsto_of_tendsto_of_tendsto_of_le_of_le` / `Filter.Tendsto.squeeze` (`Mathlib/Topology/Order/Basic.lean:230,237`)、`Tendsto.div_const` 系で `-(1/n) * log f n` の plumbing は組める
- **軸 5 (finiteness) は achievability 内で立っている** ─ Phase A `integral_logLikelihoodRatio_under_P` が `(klDiv P Q).toReal` を期待値として算出する時点で `klDiv P Q ≠ ∞` を内部で使用、外部 hypothesis として明示するのが Phase C 入口の整理

---

## 軸 1: Pi 化 KL chain rule (`klDiv (Measure.pi P) (Measure.pi Q) = n · klDiv P Q`)

### Mathlib 不在 (negative confirmation)

- **loogle query**: `InformationTheory.klDiv (MeasureTheory.Measure.pi _) (MeasureTheory.Measure.pi _)`
  → `Found 0 declarations mentioning MeasurableSpace.pi, MeasureTheory.Measure.pi, and InformationTheory.klDiv. Of these, 0 match your pattern(s).`
- **loogle query**: `InformationTheory.klDiv` (全リスト) → 29 件中 `pi` を含む補題は **0 件**
- **rg**: `klDiv.*[Pp]i|klDiv_pi` in `Mathlib/InformationTheory/` → 0 件

**結論**: Pi 化 chain rule は **完全不在**。自前で構築。

### 構築素材 (Mathlib 既存)

#### `InformationTheory.klDiv_compProd_eq_add` (chain rule、一般形)

- **file:line**: `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:204`
- **完全署名 verbatim** (chain rule 本体 + 上のセクション variable):
  ```lean
  variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
    {μ ν : Measure 𝓧} {κ η : Kernel 𝓧 𝓨}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η]
  variable (μ ν κ η) in
  theorem klDiv_compProd_eq_add :
      klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)
  ```
- **`[..]` プレリク verbatim**: `[IsFiniteMeasure μ]` `[IsFiniteMeasure ν]` `[IsMarkovKernel κ]` `[IsMarkovKernel η]`

#### `InformationTheory.klDiv_compProd_left` (degenerate kernel cancellation)

- **file:line**: `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:182` (`@[simp]`)
- **完全署名 verbatim**:
  ```lean
  variable (μ ν κ) in
  @[simp]
  lemma klDiv_compProd_left :
      klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν
  ```
- **`[..]` プレリク verbatim**: `[IsFiniteMeasure μ]` `[IsFiniteMeasure ν]` `[IsMarkovKernel κ]` (`η` 不在)

#### `MeasureTheory.measurePreserving_piFinSuccAbove` (Pi-Fin 分離 reshape)

- **file:line**: `Mathlib/MeasureTheory/Constructions/Pi.lean:802`
- **完全署名 verbatim**:
  ```lean
  theorem measurePreserving_piFinSuccAbove {n : ℕ} {α : Fin (n + 1) → Type u}
      {m : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
      (i : Fin (n + 1)) :
      MeasurePreserving (MeasurableEquiv.piFinSuccAbove α i) (Measure.pi μ)
        ((μ i).prod <| Measure.pi fun j => μ (i.succAbove j))
  ```
- **`[..]` プレリク verbatim**: `[∀ i, SigmaFinite (μ i)]` (= 各成分 `μ i` が σ-finite)
- **本 plan での用途**: `Fin (n+1)` 上の Pi 測度を **1 成分 + 残り n 成分の prod** に分離する measure-preserving 同型。Pi 化 chain rule の induction step の reshape 核

#### `MeasureTheory.measurePreserving_funUnique` (Pi-単成分の collapse)

- **file:line**: `Mathlib/MeasureTheory/Constructions/Pi.lean:836`
- **完全署名 verbatim**:
  ```lean
  theorem measurePreserving_funUnique {β : Type u} {_m : MeasurableSpace β} (μ : Measure β)
      (α : Type v) [Unique α] :
      MeasurePreserving (MeasurableEquiv.funUnique α β) (Measure.pi fun _ : α => μ) μ
  ```
- **`[..]` プレリク verbatim**: `[Unique α]`
- **本 plan での用途**: `Fin 1` (`Unique` インスタンス自動) で Pi 測度 = base measure。induction の base case で `klDiv (Measure.pi (fun _ : Fin 1 => P)) (Measure.pi (fun _ : Fin 1 => Q)) = klDiv P Q` を導出

#### `InformationTheory.Shannon.klDiv_map_measurableEquiv` (本 project 既存)

- **file:line**: `InformationTheory/Shannon/MutualInfo.lean:52`
- **完全署名 verbatim**:
  ```lean
  theorem klDiv_map_measurableEquiv {α β : Type*}
      [MeasurableSpace α] [MeasurableSpace β]
      (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
      klDiv (μ.map e) (ν.map e) = klDiv μ ν
  ```
- **`[..]` プレリク verbatim**: `[MeasurableSpace α]` `[MeasurableSpace β]` `[IsFiniteMeasure μ]` `[IsFiniteMeasure ν]`
- **本 plan での用途**: `piFinSuccAbove` 同型を介した `klDiv (Measure.pi μ) (klDiv ((μ i).prod (Measure.pi ...)))` の reshape

#### `InformationTheory.Shannon.klDiv_prod_const_left` (本 project 既存)

- **file:line**: `InformationTheory/Shannon/MutualInfo.lean:80`
- **完全署名 verbatim**:
  ```lean
  theorem klDiv_prod_const_left
      {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
      (μ : Measure α) [IsProbabilityMeasure μ]
      (ν₁ ν₂ : Measure β) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] :
      klDiv (μ.prod ν₁) (μ.prod ν₂) = klDiv ν₁ ν₂
  ```
- **`[..]` プレリク verbatim**: `[IsProbabilityMeasure μ]` `[IsFiniteMeasure ν₁]` `[IsFiniteMeasure ν₂]`
- **本 plan での用途**: 1 成分 (`P`, `Q`) と prod を取った後の **左因子 `P` (両側共通)** をキャンセル。`klDiv (P.prod (Pi P^{n})) (P.prod (Pi Q^{n})) = klDiv (Pi P^{n}) (Pi Q^{n})`。induction step で `klDiv (Pi P^{n+1}) (Pi Q^{n+1}) = klDiv P Q + klDiv (Pi P^{n}) (Pi Q^{n})` の path に乗る

### 自前 induction の見積り

```lean
theorem klDiv_pi_eq_n_smul
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) :
    klDiv (Measure.pi (fun _ : Fin n => P)) (Measure.pi (fun _ : Fin n => Q))
      = (n : ℝ≥0∞) * klDiv P Q
```

**戦略**:
- **base** (`n = 0`): `Fin 0 → α ≃ Unit`、`Measure.pi (Fin 0) = Measure.dirac default`、両側 KL = 0
- **step** (`n+1`): `Measure.pi (Fin (n+1)) = (μ 0).prod (Measure.pi (Fin n))` (via `piFinSuccAbove 0`)、`klDiv_map_measurableEquiv` で reshape、`compProd_const` で compProd 形に乗せ、`klDiv_compProd_eq_add` + `klDiv_compProd_left` で `klDiv P Q + klDiv (Pi^n)`、IH で `(n+1) · klDiv`

**行数見積り**: 40〜80 行 (親 plan 通り)。base + step + reshape (3 段、各 10〜20 行)。リスクは `compProd_const` (= `μ ⊗ₘ Kernel.const _ ν = μ.prod ν`) の plumbing を `MeasureTheory.Measure.compProd_const` で 1 行で済むかどうか。

---

## 軸 2: KL の Data Processing Inequality (DPI)

### Mathlib 不在 (negative confirmation)

- **loogle**: `|- InformationTheory.klDiv _ _ ≤ InformationTheory.klDiv _ _` → 0 件
- **loogle**: `InformationTheory.klDiv, MeasureTheory.Measure.map` → 0 件
- **rg**: `klDiv_le_klDiv|le_klDiv|klDiv_map_le|klDiv_comp_le` in `Mathlib/InformationTheory/` → 0 件
- **rg**: `fDiv_le_fDiv|fDiv_comp|fDiv.*Markov` in `Mathlib/Probability/` → 0 件 (= `fDiv` framework 自体が本 Mathlib 版に不在)

**結論**: Mathlib に DPI 直接補題は **完全不在**。**`fDiv` の親 framework もない**ため Mathlib からの DPI 導出は不可能。

### 本 project 既存 (DPI.lean: 既に書かれている、要 public 化)

#### `InformationTheory.Shannon.klDiv_map_le` (現在 `private`)

- **file:line**: `InformationTheory/Shannon/DPI.lean:52`
- **完全署名 verbatim**:
  ```lean
  private theorem klDiv_map_le {α β : Type*}
      [MeasurableSpace α] [MeasurableSpace β]
      {f : α → β} (hf : Measurable f)
      (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
      klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν
  ```
- **`[..]` プレリク verbatim**: `[MeasurableSpace α]` `[MeasurableSpace β]` `[IsFiniteMeasure μ]` `[IsFiniteMeasure ν]`
- **本 plan での用途**: 検定 `s : Set (Fin n → α)` に対し `f := s.indicator : (Fin n → α) → Bool` (= `{0, 1}`) を取り、`klDiv ((P^n).map f) ((Q^n).map f) ≤ klDiv (P^n) (Q^n)`。**LHS は `Bernoulli(P^n s)` vs `Bernoulli(Q^n s)` の KL**
- **要対応**: 現在 `private` なので **DPI.lean を編集して public 化**、または **Stein.lean に `klDiv_map_le` を copy** (50〜100 行の Jensen 証明を再呼び出し or import 路線)。**最小コストは `private` → 公開**

### Bernoulli 形検定への翻訳 (自前)

検定 `s : Set (Fin n → α)` に対し:
- `f := fun x => decide (x ∈ s) : (Fin n → α) → Bool`
- `(Measure.pi (fun _ => P)).map f = Bool 上の確率測度、Pmf := P^n s on `true`, P^n sᶜ on `false`
- `(Measure.pi (fun _ => Q)).map f = Bool 上の確率測度、Qmf := Q^n s on `true`, Q^n sᶜ on `false`
- DPI で `klDiv (P^n.map f) (Q^n.map f) ≤ klDiv P^n Q^n`
- **LHS は Bernoulli KL**: `(P^n s) * log(P^n s / Q^n s) + (P^n sᶜ) * log(P^n sᶜ / Q^n sᶜ)` (展開直接)

**プランニング判断**: Bernoulli 専用 KL 補題は不要、上の log-sum 直接展開で済む。`klDiv (Measure on Bool)` を **discrete sum** で展開する `klDiv_discrete_toReal_eq_sum` 系は `InformationTheory/Shannon/Bridge.lean:207` に既存 (`private`)、これも公開化候補。

---

## 軸 3: log-sum 下界 (`mul_log_le_klDiv` 系) — Mathlib 既存

### `InformationTheory.mul_log_le_toReal_klDiv` (Real 版、最重要)

- **file:line**: `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:346`
- **完全署名 verbatim**:
  ```lean
  lemma mul_log_le_toReal_klDiv (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
      μ.real univ * log (μ.real univ / ν.real univ) + ν.real univ - μ.real univ
        ≤ (klDiv μ ν).toReal
  ```
- **`[..]` プレリク verbatim**: `[MeasurableSpace α]` (section variable)、`{μ ν : Measure α}` ─ `IsFiniteMeasure` 等の追加 instance は不要 (`hμν` + `h_int` で自動)
- **本 plan での用途**: **これが本質的に「Bernoulli reduction の DPI 後の Bernoulli KL 下界」**。`μ`, `ν` を片側だけ取ったとき `μ.real univ * log(μ.real univ / ν.real univ) + ν.real univ - μ.real univ` の形で **log-sum 不等式** を提供。Bernoulli reduction 後に直接適用可

### `InformationTheory.mul_log_le_klDiv` (ENNReal 版)

- **file:line**: `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:360`
- **完全署名 verbatim**:
  ```lean
  lemma mul_log_le_klDiv (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
      ENNReal.ofReal (μ.real univ * log (μ.real univ / ν.real univ)
          + ν.real univ - μ.real univ)
        ≤ klDiv μ ν
  ```
- **`[..]` プレリク verbatim**: `[IsFiniteMeasure μ]` `[IsFiniteMeasure ν]`

### `Real.binEntropy` (binary entropy、補助使用候補)

- **file:line**: `Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean:63`
- **完全署名 verbatim**: `@[pp_nodot] noncomputable def binEntropy (p : ℝ) : ℝ := p * log p⁻¹ + (1 - p) * log (1 - p)⁻¹`
- **本 plan での用途**: 検定の error α (= `P^n s^c ≤ ε`) と Bernoulli KL `klDiv (Bernoulli α_n) (Bernoulli β_n)` の評価に補助的に使う候補。**Stein converse の主路線では `binEntropy` を経由する必要は低い** (上の `mul_log_le_toReal_klDiv` で直接展開可能、`(α log(α/β) + (1-α) log((1-α)/(1-β))` の形をそのまま使う)

### 結論

**Bernoulli reduction の Bernoulli KL 下界は `mul_log_le_toReal_klDiv` 1 本で済む**。Bernoulli 専用補題は自前不要。

---

## 軸 4: `Tendsto` / `-(1/n) * log f n` の squeeze API

### `tendsto_of_tendsto_of_tendsto_of_le_of_le` (squeeze theorem)

- **file:line**: `Mathlib/Topology/Order/Basic.lean:230`
- **完全署名 verbatim**:
  ```lean
  theorem tendsto_of_tendsto_of_tendsto_of_le_of_le [OrderTopology α] {f g h : β → α}
      {b : Filter β} {a : α} (hg : Tendsto g b (𝓝 a)) (hh : Tendsto h b (𝓝 a))
      (hgf : ∀ x, g x ≤ f x) (hfh : ∀ x, f x ≤ h x) : Tendsto f b (𝓝 a)
  ```
- **`[..]` プレリク verbatim**: `[OrderTopology α]` (+ section: `[TopologicalSpace α]` `[Preorder α]`)
- **alias**: `Filter.Tendsto.squeeze` (line 237)

### `Filter.Tendsto.log` (log の連続写像)

- **file:line**: `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:471`
- **完全署名 verbatim**:
  ```lean
  theorem Filter.Tendsto.log {f : α → ℝ} {l : Filter α} {x : ℝ}
      (h : Tendsto f l (𝓝 x)) (hx : x ≠ 0) :
      Tendsto (fun x => log (f x)) l (𝓝 (log x))
  ```
- **`[..]` プレリク**: 不要 (Real 標準)

### `Filter.Tendsto.div` (Tendsto の除算)

- **file:line**: `Mathlib/Topology/Algebra/GroupWithZero.lean`
- **概要**: `Tendsto f l (𝓝 a) → Tendsto g l (𝓝 b) → b ≠ 0 → Tendsto (f/g) l (𝓝 (a/b))`
- **本 plan での用途**: `(1/n) * log` の plumbing の base

### `Filter.Tendsto.mul` / `Tendsto.const_mul` / `Tendsto.neg`

- **概要**: 標準四則対応、本 plan の `-(1/n) * log f n` の自然な合成に使用
- **本 plan での用途**: lower bound (`stein_achievability` から `-(1/n) * log Q^n s ≥ K - δ_n` で `δ_n → 0`) と upper bound (`stein_converse` から `≤ K + δ_n`) を **squeeze** で `Tendsto` に乗せる

### 結論

**`-(1/n) * log f n` の `Tendsto` plumbing は標準 squeeze + Real 関数連続性で組める**。新規 API 不要。

---

## 軸 5: `klDiv P Q < ∞` finiteness (achievability で立つか)

### Phase A〜B での扱い

- `InformationTheory/Shannon/Stein.lean:113` 内 `integral_logLikelihoodRatio_under_P` で:
  ```lean
  have h_int_llr : Integrable (llr P Q) P := ...
  rw [toReal_klDiv hPQ h_int_llr]
  ```
  により **`hPQ : P ≪ Q`** + **`h_int_llr` (Fintype + IsProbabilityMeasure ⇒ 自動)** から `klDiv P Q ≠ ∞` (`toReal` が意味を持つ) を内部で使用済み
- Phase B `stein_achievability` では `(klDiv P Q).toReal` をそのまま `Tendsto` の極限として扱っている

### Mathlib `klDiv_ne_top`

- **file:line**: `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:103`
- **完全署名 verbatim**:
  ```lean
  lemma klDiv_ne_top (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : klDiv μ ν ≠ ∞
  ```
- **本 plan での用途**: Phase C/D の statement に `klDiv P Q ≠ ∞` を hypothesis として明示するか、Phase A の `Integrable (llr P Q) P` (= Fintype 自動) から内部導出するかの判断

### 結論

`klDiv P Q ≠ ∞` は Phase A の hypothesis 構成 (`hPQ : P ≪ Q` + Fintype 自動 integrable) から **既に立っている**。Phase C/D の statement には **追加 hypothesis として明示する必要はない** (achievability と同じ仮定セット `hPpos / hPQ / hQpos` で十分)。

---

## 結論サマリ (各軸 1 行)

| 軸 | 結論 | Phase 影響 |
|---|---|---|
| 1 Pi 化 chain rule | **Mathlib 不在** (loogle 0 件) → 自前 induction `klDiv_pi_eq_n_smul` 40〜80 行 (`klDiv_compProd_eq_add` + `klDiv_compProd_left` + `measurePreserving_piFinSuccAbove` で組む) | Phase A の山場 1 (本 plan Phase A) |
| 2 DPI | **本 project 既存** (`InformationTheory/Shannon/DPI.lean:52` `klDiv_map_le`、現在 `private`) → public 化 1 行 + 直接適用 | Phase B (本 plan Phase B) は既存資産で 30〜60 行 |
| 3 log-sum 下界 | **Mathlib 既存** (`mul_log_le_toReal_klDiv`、`Mathlib/InformationTheory/KullbackLeibler/Basic.lean:346`) → 直接適用、Bernoulli 専用補題不要 | Phase B 30〜60 行 |
| 4 `Tendsto` squeeze | **Mathlib 既存** (`tendsto_of_tendsto_of_tendsto_of_le_of_le`、`Mathlib/Topology/Order/Basic.lean:230`) → 標準 plumbing | Phase C 50〜100 行 |
| 5 finiteness | **achievability で立つ** (Phase A 内部使用済み)、Phase C/D で追加 hypothesis 不要 | hypothesis セット流用 |

---

## Phase C/D 着手判定

**GO**:

- 唯一の **不確実性** は **軸 1 (Pi 化 chain rule の自前 induction 40〜80 行)**。これは親 plan Phase A.7 として既に予定されていた作業 (achievability で迂回されたが Phase C で必要)
- DPI は本 project 既存資産の **public 化 1 行で再利用可**
- log-sum 下界は Mathlib 既存、Bernoulli 専用補題不要
- `Tendsto` squeeze は標準 API
- 全体として **新規 plumbing は Pi 化 chain rule の 1 本のみ** (40〜80 行)、残りは既存資産の組み合わせ

## Definition of Done (本 inventory)

- [x] 5 軸全て調査完了
- [x] `klDiv_compProd_eq_add` / `klDiv_compProd_left` の verbatim 署名 + `[..]` プレリク確定 (親 inventory 参照)
- [x] `measurePreserving_piFinSuccAbove` の verbatim 署名 + `[..]` プレリク (`[∀ i, SigmaFinite (μ i)]`) 確定
- [x] DPI は本 project 既存 (`InformationTheory/Shannon/DPI.lean:52`、`private` フラグ確認済) を確認、public 化方針確定
- [x] `mul_log_le_toReal_klDiv` の verbatim 署名 確定、Bernoulli 専用補題不要を確認
- [x] `Tendsto` squeeze (`tendsto_of_tendsto_of_tendsto_of_le_of_le`) の verbatim 署名 確定
- [x] Phase C skeleton (`InformationTheory/Shannon/Stein.lean` への append、または `InformationTheory/Shannon/SteinConverse.lean` 新ファイル) が書ける状態

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 本 inventory はまだ起草段階。本体着手で発見があれば追記。 -->
