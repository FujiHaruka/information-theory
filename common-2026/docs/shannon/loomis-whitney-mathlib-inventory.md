# Loomis–Whitney: Mathlib インベントリ サブ計画 (Phase 0)

> **Parent**: [`loomis-whitney-moonshot-plan.md`](loomis-whitney-moonshot-plan.md) §Phase 0
>
> **Status (2026-05-10):** 起草。loogle index (`.lake/build/loogle.index`) + Mathlib 直 grep
> でホットスポット 5 軸を機械的に確認。各候補補題は **CLAUDE.md「Subagent Inventory of
> Mathlib Lemmas」規約** (位置 / 完全シグネチャ / 引数 / 結論形 / 使い所) に従って記録する。

## 進捗

- [x] 軸 1: Loomis–Whitney 自体 (Mathlib に既存しないこと) 確認 ✅
- [x] 軸 2: `MeasureTheory.Measure.count` / `ProbabilityTheory.uniformOn` API 在庫整理 ✅
- [x] 軸 3: 一様分布 entropy ↔ 濃度 (`Real.log` / `negMulLog` 代数支援) ✅
- [x] 軸 4: 射影 (drop-one-coordinate) MeasurableEquiv 流用可能性 ✅
- [x] 軸 5: `shearer_inequality` (本 project 内) シグネチャ + cover 条件 verification ✅

**実装完了 (2026-05-10)**: 全 5 軸が Phase A〜C 実装で確認済み。
詳細 proof-log: [`docs/proof-logs/proof-log-loomis-whitney.md`](../proof-logs/proof-log-loomis-whitney.md)。

判断ログに **`Real.log_prod` の引数記述ミス** 訂正を記録 (実機は `(hf)` 1 引数)。

## ゴール / Approach

5 軸の調査結果を **Phase A skeleton (`Common2026/Shannon/LoomisWhitney.lean` の sorry-driven 出だし) が書ける状態** に持っていく。各軸で「Mathlib にあるか / ないか / 既存補題で代用可」の 1 行結論 + 採用する具体補題シグネチャを verbatim 記録。

## Phase 詳細

### 軸 1: Loomis–Whitney 自体

#### 結論 (1 行)

**Mathlib 不在を裏取り済み。本 plan の主定理 `loomis_whitney` は新規実装が必要。**

#### 確認手順

```bash
export PATH=$HOME/.elan/bin:$PATH
./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "Loomis"
# → unknown identifier 'Loomis' (= Mathlib に Loomis 命名の宣言なし)

./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "Shearer"
# → unknown identifier 'Shearer' (= Han Phase D inventory と同じ結論、再確認)

rg "Loomis|Whitney|loomis" .lake/packages/mathlib/Mathlib/
# → 0 件 (大文字小文字混在で確認)
```

`docs/han/han-phase-d-mathlib-inventory.md` 軸 (a) でも Shearer 不在を確認済み。Loomis–Whitney は通常 Shearer 経由で証明されるため、Shearer がない以上、Loomis–Whitney もない (combinatorial 直証版が独立にあれば別だが、今回 grep で 0 件なので無し)。

#### Phase 影響

Phase A〜C は予定通り進める。

---

### 軸 2: counting measure / `uniformOn` API

#### 結論 (1 行)

**`ProbabilityTheory.uniformOn` API は確立済み。`uniformOn_apply_finset` で singleton 質量を `1/#A` の形で取れる見込み。** ただし「`uniformOn s {x}` で 1 step に取り出す」専用補題は無いので `uniformOn_apply_finset (s) ({x})` から導く。

#### 採用候補

##### `ProbabilityTheory.uniformOn`
- **位置**: `Mathlib/Probability/UniformOn.lean:60`
- **シグネチャ**:
  ```
  def uniformOn (s : Set Ω) : Measure Ω :=
    Measure.count[|s]
  ```
  (`deriving IsZeroOrProbabilityMeasure`)
- **引数**: `s : Set Ω` explicit
- **結論形**: `Measure Ω` (counting measure conditioned by `s`)
- **使い所**: Phase A 定義の `μ` を構成。`Set` 引数なので Phase B での `(A : Finset _)` 渡しでは `(A : Set _)` coerce が必要

##### `ProbabilityTheory.uniformOn_apply_finset`
- **位置**: `Mathlib/Probability/UniformOn.lean:109`
- **シグネチャ**:
  ```
  lemma uniformOn_apply_finset [DecidableEq Ω] [MeasurableSingletonClass Ω]
      {s t : Finset Ω} :
      uniformOn (s : Set Ω) (t : Set Ω) = #(s ∩ t) / #s
  ```
- **引数**: `s t : Finset Ω` (implicit), instance 前提 `[DecidableEq Ω]` `[MeasurableSingletonClass Ω]`
- **結論形** (verbatim):
  ```
  uniformOn (s : Set Ω) (t : Set Ω) = #(s ∩ t) / #s
  ```
- **使い所**: `t = {x}` (singleton) で `uniformOn A {x} = #(A ∩ {x}) / #A`、`x ∈ A` のとき `1/#A`、`x ∉ A` のとき `0` を導く。Phase A `entropy_uniformOn_eq_log_card` の主役

##### `ProbabilityTheory.isProbabilityMeasure_uniformOn`
- **位置**: `Mathlib/Probability/UniformOn.lean:113`
- **シグネチャ**:
  ```
  theorem isProbabilityMeasure_uniformOn {s : Set Ω}
      (hs : s.Finite) (hs' : s.Nonempty) :
      IsProbabilityMeasure (uniformOn s)
  ```
- **引数**: `hs : s.Finite`、`hs' : s.Nonempty` (両方 explicit)
- **結論形** (verbatim):
  ```
  IsProbabilityMeasure (uniformOn s)
  ```
- **使い所**: Phase A entropy 計算で `[IsProbabilityMeasure μ]` instance を起こすため。`A.Nonempty` と `A.finite_toSet` を渡す

##### `MeasureTheory.Measure.count_apply_finset`
- **位置**: `Mathlib/MeasureTheory/Measure/Count.lean:50`
- **シグネチャ**:
  ```
  theorem count_apply_finset [MeasurableSingletonClass α] (s : Finset α) :
      count (↑s : Set α) = #s
  ```
- **引数**: `s : Finset α` explicit, `[MeasurableSingletonClass α]` instance
- **結論形** (verbatim):
  ```
  count (↑s : Set α) = #s
  ```
- **使い所**: `uniformOn_apply_finset` 内部で使われている。本 plan で直接使う箇所は無い見込みだが、unfolding でハマったとき下に降りる足場

#### Phase 影響

`uniformOn` を直接採用、`Measure.count` を裸で叩く必要は無い。Pi.lean / Bridge.lean 系の `entropy μ X` (= `∑ x, negMulLog ((μ.map X).real {x})`) と組み合わせるとき、`Phase A` で `(μ.map (fun ω => ω)).real {x} = uniformOn A {x} = ...` の橋を 1 段書くことになる。

---

### 軸 3: 一様分布 entropy ↔ 濃度 (代数支援)

#### 結論 (1 行)

**「一様分布の entropy が `log #A` に等しい」専用補題は Mathlib にも本 project にも無し。Phase A `entropy_uniformOn_eq_log_card` を自前で書く必要あり (見積 30〜50 行)。**ただし周辺代数 (`Real.log_prod` / `Real.log_pow` / `Real.negMulLog_*`) は揃っている。

#### 確認手順

```bash
./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "Real.log, Fintype.card"
# → 4 件 (NumberTheory.ClassNumber, NumberField.Units 系のみ; entropy 無し)

./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "ProbabilityTheory.entropy"
# → unknown identifier (= Mathlib 自体に Shannon entropy なし、この project の独自定義)
```

#### 採用候補 (代数 building blocks)

##### `Real.log_pow`
- **位置**: `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:287`
- **シグネチャ**:
  ```
  @[simp, push]
  theorem log_pow (x : ℝ) (n : ℕ) : log (x ^ n) = n * log x
  ```
- **引数**: `x : ℝ`, `n : ℕ` (両方 explicit)
- **結論形** (verbatim):
  ```
  log (x ^ n) = n * log x
  ```
- **使い所**: Phase C で `|A|^(n−1) ≤ ∏ |π_i(A)|` の log 形 `(n−1) · log |A| ≤ log (∏ |π_i(A)|)` から自然数版へ持ち上げる。Phase A の `negMulLog (1/N)` 代数でも `log_pow` を経由する可能性あり

##### `Real.log_prod`
- **位置**: `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:396`
- **シグネチャ**:
  ```
  @[push]
  theorem log_prod {α : Type*} {s : Finset α} {f : α → ℝ}
      (hf : ∀ x ∈ s, f x ≠ 0) :
      log (∏ i ∈ s, f i) = ∑ i ∈ s, log (f i)
  ```
- **引数**: `s : Finset α` (implicit), `f : α → ℝ` (implicit), `hf : ∀ x ∈ s, f x ≠ 0` (explicit)
- **結論形** (verbatim):
  ```
  log (∏ i ∈ s, f i) = ∑ i ∈ s, log (f i)
  ```
- **使い所**: Phase C 主定理の最終 step (`∑ i, log |π_i(A)| = log (∏ i, |π_i(A)|)`)。`hA.image_nonempty` から `(π_i A).card > 0`、よって cast 値 `≠ 0` を引き出す

##### `Real.log_le_log` / `Real.log_le_log_iff`
- **位置**: `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:150` / `:146`
- **シグネチャ**:
  ```
  theorem log_le_log_iff (h : 0 < x) (h₁ : 0 < y) : log x ≤ log y ↔ x ≤ y

  @[gcongr, bound]
  lemma log_le_log (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y
  ```
- **使い所**: Phase C で log 形不等式から `|A|^(n−1) ≤ ∏ |π_i(A)|` を取り出すとき。等号方向で `log_le_log_iff` を `.mpr` で使う

##### `Real.negMulLog_nonneg`
- **位置**: `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:174`
- **シグネチャ**:
  ```
  lemma negMulLog_nonneg {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) : 0 ≤ negMulLog x
  ```
- **使い所**: Phase A `entropy ≥ 0` 系で使う場面が出れば。直接の使い道は本 plan で limited だが、`HanDShearer.lean:79` で `condEntropy_nonneg` を unfold して使うパターンと並列の代数

#### Phase 影響

Phase A で 30〜50 行の自前補題が必要。`negMulLog (1/N) = (log N) / N` の代数は **`Real.negMulLog_def` + `Real.log_inv` + `mul_div`** で 5〜10 行に収まる見込み。

#### 自前で書くことが確定する補題 (Phase A target)

```
theorem entropy_uniformOn_eq_log_card
    {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    {A : Finset β} (hA : A.Nonempty) :
    entropy (uniformOn (A : Set β)) (id : β → β) = Real.log A.card
```

---

### 軸 4: 射影 (drop-one-coordinate) MeasurableEquiv

#### 結論 (1 行)

**Common2026 既存 `Common2026.Shannon.Pi.entropy_measurableEquiv_comp` で reshape 可能。`Han.lean` の `exceptIdxEquiv` (`Fin n` の `i` 抜き subtype と `Fin (n-1)` の同型) はそのまま流用、`Mathlib.MeasureTheory.MeasurableSpace.Embedding.piCongrLeft` で押し上げる。**

#### 採用候補 (既存 Common2026 補題)

##### `InformationTheory.Shannon.entropy_measurableEquiv_comp`
- **位置**: `Common2026/Shannon/Pi.lean:35`
- **シグネチャ**:
  ```
  lemma entropy_measurableEquiv_comp
      {β γ : Type*}
      [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
      [Fintype γ] [DecidableEq γ] [Nonempty γ]
      [MeasurableSpace γ] [MeasurableSingletonClass γ]
      (μ : Measure Ω) (Xs : Ω → β) (hXs : Measurable Xs) (e : β ≃ᵐ γ) :
      entropy μ (fun ω => e (Xs ω)) = entropy μ Xs
  ```
- **引数**: `μ : Measure Ω` explicit, `Xs : Ω → β` explicit, `hXs : Measurable Xs` explicit, `e : β ≃ᵐ γ` explicit; `[Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]` × γ instance すべて必要
- **結論形** (verbatim):
  ```
  entropy μ (fun ω => e (Xs ω)) = entropy μ Xs
  ```
- **使い所**: Phase B で `(j : ↥(univ.filter (· ≠ i)) → α)` 形と `(j : {j // j ≠ i} → α)` 形 (Han.lean の流儀) の間を reshape

##### `MeasurableEquiv.piCongrLeft`
- **位置**: `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:488`
- **シグネチャ**:
  ```
  def piCongrLeft (f : δ ≃ δ') :
      (∀ b, π (f b)) ≃ᵐ ∀ a, π a where ...
  ```
  (周辺の `π` は `δ' → Type*` で `[∀ a, MeasurableSpace (π a)]` 必要)
- **引数**: `f : δ ≃ δ'` explicit, `π : δ' → Type*` (implicit), instance `[∀ a, MeasurableSpace (π a)]`
- **結論形**: `(∀ b, π (f b)) ≃ᵐ ∀ a, π a`
- **使い所**: Phase B で index 同型 (`{j : Fin n // j ≠ i} ≃ ↥(univ.filter (· ≠ i))` 等) を Pi 値の MeasurableEquiv に持ち上げる

##### `InformationTheory.Shannon.exceptIdxEquiv` (本 project)
- **位置**: `Common2026/Shannon/Han.lean:151`
- **シグネチャ**:
  ```
  private def exceptIdxEquiv {n : ℕ} (i : Fin n) :
      Fin i.val ⊕ {j : Fin n // i < j} ≃ {j : Fin n // j ≠ i}
  ```
- **使い所**: 本 plan の射影では「`i` を抜いた」subtype (`{j // j ≠ i}`) を `Fin i.val ⊕ {j // i < j}` に分解する場面で再利用候補。**ただし private のため import 不可**。本 plan で必要なら同型を再定義 or `Han.lean` 側で公開化する判断が要る → Phase 0 → Phase A 移行時の判断ログに記録

##### `Finset.sort` / `Finset.orderEmbOfFin` 経由
- 既に Han Phase D で `orderEmbOfFin S : Fin S.card ↪o Fin n` の reshape pattern が確立済み (`HanD.lean` 全体)。Phase B `S i := univ.filter (· ≠ i)` は `S.card = n - 1` なので `orderEmbOfFin` で `Fin (n-1) ↪ Fin n` を得る経路もある

#### `MeasurableEquiv.piFinSuccAbove` (drop-one-coordinate の Mathlib 直対応)
- **位置**: 既に `Common2026/Shannon/Han.lean:102` で使用実績あり (検索: `MeasurableEquiv.piFinSuccAbove`)
- **使い所**: 本 plan ではあえて使わず、Phase D が確立した `{j // j ≠ i}` subtype 経路を流用する想定。`piFinSuccAbove` は cast index `i = Fin.last n` 縛りで一般 `i` には reshape 1 段足りない

#### Phase 影響

Phase B の主な作業は **既存 reshape plumbing の流用 (新規 MeasurableEquiv は不要)**。20〜40 行見積。Phase A で `entropy_uniformOn_eq_log_card` が generic な β で書ければ、Phase B は β = `({j : Fin n // j ≠ i} → α)` でそのまま呼び出せる。

#### 判断保留: `exceptIdxEquiv` の公開化

`Han.lean` の `exceptIdxEquiv` を `private` のまま流用するか、`public def` に格上げして本 plan からも import するか。Phase B 着手時に再判断。デフォルトは「再定義する (5 行で済む)」。

---

### 軸 5: `shearer_inequality` 適用形

#### 採用候補

##### `InformationTheory.Shannon.shearer_inequality` (本 project)
- **位置**: `Common2026/Shannon/HanDShearer.lean:41`
- **シグネチャ** (型クラス前提を `[...]` 込みで verbatim):
  ```
  theorem shearer_inequality
      {n : ℕ}
      {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
        [MeasurableSpace α] [MeasurableSingletonClass α]
      {Ω : Type*} [MeasurableSpace Ω]
      {ι : Type*} [Fintype ι]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
      (S : ι → Finset (Fin n))
      {k : ℕ}
      (hk : ∀ i : Fin n,
        k ≤ (Finset.univ.filter (fun j : ι => i ∈ S j)).card) :
      (k : ℝ) * jointEntropy μ Xs
        ≤ ∑ j : ι, jointEntropySubset μ Xs (S j)
  ```
- **引数**:
  - `n : ℕ` implicit
  - `α : Type*` implicit (with `[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`)
  - `Ω : Type*` implicit (with `[MeasurableSpace Ω]`)
  - `ι : Type*` implicit (with `[Fintype ι]`)
  - `μ : Measure Ω` explicit (with `[IsProbabilityMeasure μ]`)
  - `Xs : Fin n → Ω → α` explicit
  - `hXs : ∀ i, Measurable (Xs i)` explicit
  - `S : ι → Finset (Fin n)` explicit
  - `k : ℕ` implicit
  - `hk : ∀ i : Fin n, k ≤ #(univ.filter fun j => i ∈ S j)` explicit
- **結論形** (verbatim):
  ```
  (k : ℝ) * jointEntropy μ Xs
    ≤ ∑ j : ι, jointEntropySubset μ Xs (S j)
  ```
- **本 plan での適用形**:
  - `ι := Fin n` (各 `i : Fin n` で 1 つの `S i` を割り当て)
  - `S i := Finset.univ.filter (fun j => j ≠ i)` (cardinality `n - 1`)
  - `k := n - 1`
  - cover 条件 `hk j : n - 1 ≤ #(univ.filter (fun i => j ∈ S i))`:
    - `j ∈ S i ↔ j ≠ i ↔ i ≠ j`
    - `univ.filter (fun i => j ∈ S i) = univ.filter (· ≠ j) = univ.erase j`
    - `(univ.erase j).card = n - 1` (Fin n 上)
    - 等号で十分なので `le_of_eq` で `≤` 化
  - 結果: `((n - 1) : ℝ) * jointEntropy μ Xs ≤ ∑ i : Fin n, jointEntropySubset μ Xs (S i)`

#### 関連 `jointEntropy` / `jointEntropySubset` 定義

##### `InformationTheory.Shannon.jointEntropy`
- **位置**: `Common2026/Shannon/Han.lean:42`
- **シグネチャ**:
  ```
  noncomputable def jointEntropy
      (μ : Measure Ω) (Xs : Fin n → Ω → α) : ℝ :=
    entropy μ (fun ω i => Xs i ω)
  ```
- **使い所**: Phase C `μ := uniformOn A`, `Xs i ω := ω i` で `jointEntropy μ Xs = entropy μ (fun ω i => ω i) = entropy μ id`。Phase A の `entropy_uniformOn_eq_log_card` で `log #A` に潰れる

##### `InformationTheory.Shannon.jointEntropySubset`
- **位置**: `Common2026/Shannon/HanD.lean` (主定義)
- **シグネチャ** (本体では `omit` でいくつかの instance を抜いている可能性、実機検証):
  ```
  noncomputable def jointEntropySubset
      (μ : Measure Ω) (Xs : Fin n → Ω → α) (S : Finset (Fin n)) : ℝ :=
    entropy μ (fun ω (i : S) => Xs i.val ω)
  ```
- **使い所**: Phase B 主定理 `jointEntropySubset_le_log_projection_card` の左辺。射影像濃度の log との接続を Phase A `entropy_image_le_log_card` 経由で行う

#### Phase 影響

Phase C で 1 回呼ぶだけ。argument 並びが完全に一致しているので `apply shearer_inequality μ Xs hXs S` で済む見込み。cover 条件の証明だけが新規 (5〜10 行)。

---

## Phase A 着手時の不確実性ランク

| 項目 | 不確実性 | 対処 |
|---|---|---|
| `uniformOn_apply_finset` の `t = {x}` 特殊化 (`s ∩ {x} = if x ∈ s then {x} else ∅`) | **低** | `Finset.inter_singleton_of_mem` / `Finset.inter_singleton_of_not_mem` で 2 段場合分け |
| `IsProbabilityMeasure (uniformOn (A : Set β))` instance 注入 | **低** | `isProbabilityMeasure_uniformOn A.finite_toSet hA` で 1 行 |
| `μ.map id = uniformOn A` (entropy 定義に乗せるため) | **低** | `Measure.map_id` で 1 行、もしくは `id = fun ω => ω` の defeq |
| `entropy_image_le_log_card` 一般版の証明 (= "support 濃度の log を超えない") | **中** | Mathlib に直接無いので自前で書く。`negMulLog` 凹性 (Jensen) を使うか、support の uniform 化に bijection で乗せて `entropy_uniformOn_eq_log_card` を呼ぶか。後者は plumbing 重め |
| Phase B の `↥(univ.filter (· ≠ i))` ↔ `{j : Fin n // j ≠ i}` 整合 | **中** | `Finset.subtype_mk_filter_eq_subtype` 系の補題が Mathlib にあるか要確認 (loogle 候補: `Finset.filter_subtype` 周辺) |
| Phase C cover 条件 `(univ.erase j).card = n − 1` | **低** | `Finset.card_erase_of_mem` (Mathlib 既存) 1 発 |
| Phase C `Real.log_prod` 適用時の `(π_i A).card ≠ 0` 前提 | **低** | `hA.image f` から `(A.image f).Nonempty`、`Finset.Nonempty.card_pos`、cast で `(_ : ℝ) ≠ 0` |

## 全体的な Phase A〜C 工数 (再見積もり)

シードカードの「1〜2 週間 / 200〜300 行」を以下に細分化:

| Phase | 当初見積 | 再見積 (inventory 後) |
|---|---|---|
| Phase 0 | 1 ターン | 1 ターン (本 ファイル + plan 反映) |
| Phase A | — | 3〜5 日 / 80〜130 行 (`entropy_uniformOn_eq_log_card` + `entropy_image_le_log_card`) |
| Phase B | — | 2〜3 日 / 50〜80 行 (Pi.lean 流用 + adapter) |
| Phase C | — | 3〜5 日 / 100〜150 行 (cover + log↔exp 持ち上げ + cast) |
| **合計** | 1〜2 週間 | **1.5〜2.5 週間 / 230〜360 行** |

**要点**: シード見積は概ね妥当。Phase A の `entropy_image_le_log_card` 一般版が Mathlib に generic なものが無い (要 self-write) ことだけが新規発見、これで +50 行ぐらい上振れ。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### 2026-05-10 実装ターン

- **`Real.log_prod` のシグネチャ訂正**: 軸 3 の記述で
  `theorem log_prod {α} {s} {f} (hf : ∀ x ∈ s, f x ≠ 0) : log (∏ ...) = ∑ ...` と
  *3 引数 explicit* で書いていたが、実物は `{s} {f}` implicit + `(hf)` explicit で
  **1 引数 explicit**。実装中 `Real.log_prod _ _ (fun i _ => h_proj_ne i)` で 3 引数版を
  当てて型エラーになり、`Real.log_prod (fun i _ => h_proj_ne i)` 1 引数版に修正。
- **軸 4 の `exceptIdxEquiv` 公開化判断**: 「再定義 5 行」を採用。実機では 4 行で済んだ。
  Han Phase D `exceptIdxEquiv` の private 制約は本 plan には影響せず。
- **軸 3 の Jensen ルート確定**: `negMulLog` 凹性 → `ConcaveOn.le_map_sum` で 1 段適用。
  「support 圧縮 → uniform 化 → entropy_uniformOn_eq_log_card」経路は採用せず。
  Mathlib `Real.concaveOn_negMulLog` 直接利用で `entropy_le_log_image_card` が 60 行に収束。
