# Shannon: AEP + 源符号化定理 Mathlib インベントリ サブ計画

> **Parent**: [`aep-moonshot-plan.md`](aep-moonshot-plan.md) §Phase 0

<!--
雛形メモ:
- 各候補補題は CLAUDE.md「Subagent Inventory of Mathlib Lemmas」規約に従う
  (file:line / 完全署名 / 引数型 / 結論形 verbatim、`[..]` プレリク鍵括弧厳守)
- "無し" でも探索した query を記録 (negative grep / loogle 結果は資産)
-->

## 進捗

- [x] 軸 1: LLN 系 (強法則 / 弱法則の既存形 + i.i.d. の引数形)
- [x] 軸 2: `IdentDistrib` / i.i.d. predicate (Mathlib の流儀確認)
- [x] 軸 3: log 可測性 + `−log P(·)` の積分可能性
- [x] 軸 4: `Filter.liminf` / `Filter.atTop` 漸近形
- [x] 軸 5: typical set の measurability (`{x^n : |…| < ε}`)
- [x] 軸 6: block ext / Pi 構築 (`X^n : Ω → (Fin n → α)`)

## ゴール / Approach

AEP + 源符号化定理 (Phase A〜E) の着手前に **必要な Mathlib API がどれだけ揃っているか / 何を自前で書くか**
を 6 軸で固定し、本計画の skeleton を sorry-driven で書ける状態にする。**結論先取り**:

- **強法則 `strong_law_ae` は完全に揃っている**（pairwise indep + IdentDistrib(X i, X 0) 形、Banach 値）
- **`TendstoInMeasure` も既存** — a.s. → 確率収束の lift `tendstoInMeasure_of_tendsto_ae` も既存
- **`IsIID` predicate は Mathlib 不在** — 「pairwise indep + 全 i で IdentDistrib(X i, X 0)」の合成形を手書き or 自前 abbrev で
- **AEP / typical set / 源符号化定理は完全不在** — Phase B / C / D は全自作
- **`liminf` の橋渡し補題**は `Filter.liminf` API は揃っているが「`Tendsto f atTop (𝓝 L)` ⟹ `liminf f = L`」の 1 行は要確認 (本 inventory では存在を仮定し署名予測を記録)

---

## 軸 1: LLN 系 (強法則 / 弱法則 / `IsIID` 仮定の正確な形)

### Mathlib の主要 LLN 補題

#### `ProbabilityTheory.strong_law_ae_real` (実数値、Banach 一般版に統合)

- **file:line**: `Mathlib/Probability/StrongLaw.lean:598`
- **完全署名**:
  ```lean
  theorem strong_law_ae_real {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
      (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ)
      (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
      (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ i ∈ range n, X i ω) / n) atTop (𝓝 μ[X 0])
  ```
- **引数型**:
  - `[m : MeasurableSpace Ω]` (instance、無 brackets でも書ける)
  - `μ : Measure Ω` — `IsProbabilityMeasure μ` は **不要** (内部で `hint` から再構成)
  - `X : ℕ → Ω → ℝ` (= 実数値 i.i.d. 列、indexed by `ℕ`)
  - `hint : Integrable (X 0) μ`
  - `hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)` (pairwise IndepFun on the index `ℕ`)
  - `hident : ∀ i, IdentDistrib (X i) (X 0) μ μ`
- **結論形 (verbatim)**: `∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ i ∈ range n, X i ω) / n) atTop (𝓝 μ[X 0])`
- **AEP への乗せ替え**: `(1/n) · ∑ i, f(X i ω)` の形で使う。本計画 Phase B では
  `f := −Real.log ∘ (μ.map X 0).real ∘ {·}` (離散 `α` 上のシングルトン pmf 値) を `Y i := f ∘ X i` と置いて適用。

#### `ProbabilityTheory.strong_law_ae` (Banach 値)

- **file:line**: `Mathlib/Probability/StrongLaw.lean:788`
- **完全署名** (Section variable は展開して書き出す):
  ```lean
  variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
  -- omit [IsProbabilityMeasure μ] in
  theorem strong_law_ae (X : ℕ → Ω → E) (hint : Integrable (X 0) μ)
      (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
      (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (∑ i ∈ range n, X i ω)) atTop (𝓝 μ[X 0])
  ```
- **`[..]` プレリク verbatim**: `[NormedAddCommGroup E]` `[NormedSpace ℝ E]` `[CompleteSpace E]` `[MeasurableSpace E]` `[BorelSpace E]`
- **引数型**: `X : ℕ → Ω → E` (Banach 値)、`hint` / `hindep` / `hident` は実数版と同形
- **結論形 (verbatim)**: `∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (∑ i ∈ range n, X i ω)) atTop (𝓝 μ[X 0])`
- **本 plan での採用**: AEP は実数値関数 `f := −log P(·)` の和なので **`strong_law_ae_real` を採用**。Banach 値版は不要。

#### 弱法則 (`weak_law_ae` / `tendsto_inMeasure_of_lln`)

- **存否**: **直接の専用補題は無い** (`rg "weak_law"` `.lake/packages/mathlib/Mathlib/Probability/` → 0 件)
- **代替**: 強法則から `tendstoInMeasure_of_tendsto_ae` (`Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:223`) で確率収束に lift
  ```lean
  theorem tendstoInMeasure_of_tendsto_ae [IsFiniteMeasure μ]
      (hf : ∀ n, AEStronglyMeasurable (f n) μ)
      (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
      TendstoInMeasure μ f atTop g
  ```
- **本 plan の戦略**: probability AEP は **強法則 (a.s.) → `tendstoInMeasure_of_tendsto_ae` で確率収束に lift**。直接の弱法則を経由する必要なし。

### `IsIID` predicate の Mathlib 流儀

- **`IsIID` 構造体**: **無し** (`rg "IsIID|isIID|i\.i\.d" .lake/packages/mathlib/Mathlib/Probability/` → 0 件)
- **Mathlib の流儀**: `Pairwise ((· ⟂ᵢ[μ] ·) on X) ∧ ∀ i, IdentDistrib (X i) (X 0) μ μ` を **2 つの仮定として直接書き下す**
  - `IndepFun` の表記は `· ⟂ᵢ[μ] ·` (`Mathlib/Probability/Independence/Basic.lean:151`)
  - `Pairwise (R on X)` = `∀ i j, i ≠ j → R (X i) (X j)` (Mathlib `Function.onFun`)
- **本 plan での採否**: 自前 `IsIID` abbrev を導入する **意義は薄い** (Mathlib に乗っかる方が後続の plumbing が楽)。**Phase A ではこの 2 仮定を直接受ける**形にする。
  - 万一 `IsIID Xs μ := Pairwise ((· ⟂ᵢ[μ] ·) on Xs) ∧ ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ` を導入する場合は **`structure` ではなく `abbrev`** にして自動展開を効かせる

### 本計画への影響

- **Phase B (probability AEP) の主役は `strong_law_ae_real` を `Y i := −Real.log ((μ.map (Xs 0)).real {Xs i ω})` で 1 回呼ぶ** ことが確定
  - **詰まりポイント候補**: (a) `Y i` の `Integrable` 仮定 (`Y 0 ω = −log P(Xs 0 ω)` の積分可能性 — Phase B-2 で `α : Fintype` から押す)、(b) `Y i` の `IndepFun` / `IdentDistrib` の lift (`Xs i` の i.i.d. → `Y i` の i.i.d. を `IdentDistrib.comp` + `IndepFun.comp` で導く)
- **撤退ライン**: 強法則仮定の `Integrable (X 0) μ` を満たせない場合 (i.e. `α` が無限で `H(X) = ∞`) は本 plan のスコープ外、**`α : Fintype` 仮定で初手から閉じる**

---

## 軸 2: `IdentDistrib` / 独立性の predicate

### `IdentDistrib` 構造体

- **file:line**: `Mathlib/Probability/IdentDistrib.lean:71`
- **完全署名**:
  ```lean
  structure IdentDistrib (f : α → γ) (g : β → γ)
      (μ : Measure α := by volume_tac) (ν : Measure β := by volume_tac) : Prop where
    aemeasurable_fst : AEMeasurable f μ
    aemeasurable_snd : AEMeasurable g ν
    map_eq : μ.map f = ν.map g
  ```
- **`[..]` プレリク**: `[MeasurableSpace γ]` (section variable、暗黙)
- **本 plan で使う構成**:
  - `IdentDistrib.comp (h : IdentDistrib f g μ ν) (hu : Measurable u) : IdentDistrib (u ∘ f) (u ∘ g) μ ν` (`Mathlib/Probability/IdentDistrib.lean:109`) — Phase B で `−log P(·)` への lift に使う
  - `IdentDistrib.refl (hf : AEMeasurable f μ) : IdentDistrib f f μ μ` (`Mathlib/Probability/IdentDistrib.lean:84`)
- **無いもの**: 「`X^n : Ω → (Fin n → α)` の joint distribution が `(μ.map X 0)^⊗ⁿ`」の直接補題は `Mathlib/Probability/Independence/InfinitePi.lean` に近い形 (`iIndepFun_iff_map_fun_eq_infinitePi_map`) があるが、**有限 Pi (`Measure.pi`) 版 ↔ infinitePi の橋渡し**は要確認

### `iIndepFun` (family 形) と `IndepFun` (二元形)

- **file:line**: `Mathlib/Probability/Independence/Basic.lean:136` (iIndepFun) / `:144` (IndepFun)
- **完全署名 (二元 IndepFun)**:
  ```lean
  def IndepFun {β γ} {_mΩ : MeasurableSpace Ω}
      [MeasurableSpace β] [MeasurableSpace γ]
      (f : Ω → β) (g : Ω → γ) (μ : Measure Ω := by volume_tac) : Prop :=
    Kernel.IndepFun f g (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)
  ```
- **完全署名 (family iIndepFun)**:
  ```lean
  def iIndepFun {_mΩ : MeasurableSpace Ω} {β : ι → Type*}
      [m : ∀ x : ι, MeasurableSpace (β x)]
      (f : ∀ x : ι, Ω → β x) (μ : Measure Ω := by volume_tac) : Prop :=
    Kernel.iIndepFun f (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)
  ```
- **本 plan で重要な相互変換**:
  - `iIndepFun → Pairwise (IndepFun on X)` ─ `Mathlib/Probability/Independence/Basic.lean` 周辺に既存補題ありそう (要 grep、本 inventory では「あるはず」と仮定し Phase A で確認)
  - `Pairwise (IndepFun on X)` を強法則の仮定形にそのまま渡せる

### `IdentDistrib.pi` (Pi 値の同分布)

- **file:line**: `Mathlib/Probability/IdentDistribIndep.lean:57`
- **完全署名 verbatim**:
  ```lean
  lemma IdentDistrib.pi [Countable ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
      {X : (i : ι) → Ω → E i} {Y : (i : ι) → Ω' → E i}
      (h : ∀ i, IdentDistrib (X i) (Y i) μ ν)
      (hX_ind : iIndepFun X μ) (hY_ind : iIndepFun Y ν) :
      IdentDistrib (fun ω ↦ (X · ω)) (fun ω ↦ (Y · ω)) μ ν
  ```
- **`[..]` プレリク verbatim**: `[Countable ι]`、`[mE : ∀ i, MeasurableSpace (E i)]`、暗黙 `[IsFiniteMeasure μ]` ではなく `iIndepFun` 側に乗る `IsProbabilityMeasure` 自動発火
- **本 plan での用途**: Phase A で `X^n := fun ω i ↦ Xs i ω : Ω → (Fin n → α)` の joint law を扱うときに使用候補。ただし `Fin n` が `Countable` で済むか、`Fintype` 専用 lemma が要るかは Phase A 着手時に確認。

---

## 軸 3: log 可測性 + 積分可能性

### `Real.measurable_log`

- **file:line**: `Mathlib/MeasureTheory/Function/SpecialFunctions/Basic.lean:39`
- **完全署名**: `theorem measurable_log : Measurable log` (`namespace Real`)
- **派生補題 (Phase B で多用)**:
  - `Measurable.log` (`:138`): `theorem Measurable.log (hf : Measurable f) : Measurable fun x => Real.log (f x)`
  - `AEMeasurable.log` (`:170`): `lemma AEMeasurable.log (hf : AEMeasurable f μ) : AEMeasurable (fun x ↦ Real.log (f x)) μ`

### `Real.negMulLog` の可測性 / nonneg

- **file:line (nonneg)**: `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:174` —
  `lemma negMulLog_nonneg {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) : 0 ≤ negMulLog x`
- **可測性**: `negMulLog x = -x * log x` から `Measurable.log` + `Measurable.mul` で合成。直接補題は要 grep だが Phase B では `entropy μ Xs` 経由で済むため不要見込み
- **`InformationTheory` 既存利用**: `InformationTheory/Shannon/Bridge.lean:43` `entropy μ Xs := ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})` (Fintype 限定)

### `(μ.map Xs).real` の積分可能性 (Phase B で必要)

- **方針**: `α : Fintype` のもとでは `(μ.map (Xs 0)).real {x}` は **有限個の値しか取らない有界関数**、積分可能性は `IsFiniteMeasure μ` から自動
- **使う Mathlib 補題候補** (要 Phase B 着手時 grep):
  - `Integrable.bdd` 系 (有界可測関数 + 有限測度 ⟹ 積分可能)
  - `Integrable.const` (定数関数の積分可能)
- **詰まりリスク**: `−log P(Xs 0 ω)` で `P(Xs 0 ω) = 0` の点が起きると `−log 0 = +∞` を扱う羽目になる。本 plan では **`(μ.map (Xs 0)).real {x} > 0` のサポート上で議論** + サポート外は確率 0 で除外、の処理が plumbing-heavy になる可能性あり

### 本計画への影響

- **`Y i ω := −Real.log ((μ.map (Xs 0)).real {Xs i ω})` の積分可能性**は `α : Fintype` で **見かけは自明だが正規 plumbing**: (a) `Xs i` の像が有限、(b) 各 `x : α` で `(μ.map (Xs 0)).real {x}` は固定定数、(c) 全体として有限和の有界関数。**Phase B-1 (積分可能性 + 期待値計算) は 50〜80 行見積もり**
- **`μ[Y 0] = entropy μ (Xs 0)`** の評価が Phase B の重要 plumbing。`entropy μ Xs := ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})` の和形と `∫ ω, Y 0 ω ∂μ = ∫ ω, −log ((μ.map Xs 0).real {Xs 0 ω}) ∂μ` を `Fintype.sum_eq_∫` 系で接続

---

## 軸 4: `Filter.liminf` / `Filter.atTop` 漸近形

### `Filter.liminf` の Mathlib 既存形

- **定義**: `Mathlib/Order/LiminfLimsup/Basic.lean` 周辺 (`Filter.liminf : (β → α) → Filter β → α`)
- **重要補題**:
  - `Filter.Tendsto.liminf_eq` (`liminf` を `lim` に下げる): 「`Tendsto f l (𝓝 L)` ⟹ `liminf f l = L`」
  - **存在性は強い予想**だが本 inventory では未裏取り。Phase D 着手時に loogle で確認

### loogle 候補クエリ (Phase D 着手時に実行)

```text
loogle "Filter.liminf, Filter.Tendsto"
loogle "?f.liminf ?l = _"
loogle "Tendsto ?f ?l (𝓝 ?L) -> Filter.liminf ?f ?l = ?L"
```

### 教科書「lim」と Mathlib「liminf」の reconciling

- **教科書版**: `lim_n (log M_n / n) ≥ H(X)`
- **Mathlib 版**: `H(X) ≤ Filter.liminf (fun n => log (M_n n) / n) atTop`
- **bridge**: 教科書では `M_n` の数列収束を仮定するが、源符号化定理の converse は **収束を仮定しない** (任意の sequence で liminf が H(X) 以下の場合に矛盾を出す)。**`liminf` 形が正しい formalism**
- **Phase D の山場**: 「`∀ n, log M_n / n + ε ≥ H(X) - δ_n` で `δ_n → 0`」の形を `liminf_le_iff` 系で `H(X) ≤ liminf …` に翻訳

---

## 軸 5: typical set の measurability

### `MeasurableSet {a | f a < g a}` の Mathlib 既存形

- **file:line**: `Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean:245`
- **完全署名**:
  ```lean
  theorem measurableSet_lt [SecondCountableTopology α] [OrderClosedTopology α]
      {f g : δ → α} (hf : Measurable f) (hg : Measurable g) :
      MeasurableSet { a | f a < g a }
  ```
- **`[..]` プレリク verbatim**: `[SecondCountableTopology α]` `[OrderClosedTopology α]` (`α = ℝ` で自動発火)
- **本 plan での用途**: Phase C の `T_ε^n := { x : Fin n → α | |−(1/n) Σ log P(x i) − H(X)| < ε }` の measurability。`Fin n → α` 上の Borel structure (= `Pi.measurableSpace`) で
  ```
  T_ε^n = { x | (-(1/n) ∑ i, log ((μ.map Xs 0).real {x i}) − H) ∈ Set.Ioo (-ε) ε }
  ```
  の preimage、`measurableSet_lt` を 2 回 (左右の不等式) + `MeasurableSet.inter` で構成

### `MeasurableSet.preimage` (block の preimage の measurability)

- **存在**: 標準 Mathlib API (`MeasurableSet` の closure 性質)
- **本 plan での用途**: `(X^n)⁻¹ T_ε^n ⊆ Ω` の measurability を出す

---

## 軸 6: block ext / Pi 構築 (`X^n : Ω → (Fin n → α)`)

### `MeasureTheory.Measure.pi` (有限 Pi 測度)

- **file:line**: `Mathlib/MeasureTheory/Constructions/Pi.lean:213`
- **完全署名**:
  ```lean
  protected irreducible_def pi : Measure (∀ i, α i)
  -- + fundamental property:
  Measure.pi μ (Set.pi univ s) = ∏ i, μ i (s i)
  ```
- **本 plan での用途**: i.i.d. 列の joint distribution `(μ.map X^n) = (μ.map (Xs 0))^⊗ⁿ` を作るときに、`Measure.pi (fun _ : Fin n => μ.map (Xs 0))` を用いて等式 `μ.map X^n = Measure.pi (fun _ => μ.map Xs 0)` を導出
- **既存橋渡し補題**: `iIndepFun_iff_map_fun_eq_infinitePi_map` (`Mathlib/Probability/Independence/InfinitePi.lean:79`) — **infinitePi 形** であって `Measure.pi` 形ではない。有限 Pi への lower 化は要 Phase A 確認

### Han Phase B / Pi.lean の素材で足りるか

- **`InformationTheory/Shannon/Pi.lean` 既存定理**:
  - `entropy_measurableEquiv_comp`: `entropy μ (e ∘ X) = entropy μ X` (`e : β ≃ᵐ γ`)
  - `condEntropy_measurableEquiv_comp`: 同上 conditioner 側
- **Han Phase B `jointEntropy_chain_rule`**: `Fin n` 全体の chain rule、AEP では **そのままは使わない** (AEP は entropy ではなく log-likelihood の和を扱う)
- **本 plan で素材として効くもの**:
  - `entropy_measurableEquiv_comp` ─ Phase A で `X^n` の joint law を `(Fin n → α)` 上の measure に翻訳する箇所で 1〜2 回
  - `MeasurableEquiv.piCongrLeft` ─ index reshape で 0〜1 回 (Han ほどは出てこない予想)
- **Phase D で再利用**: 源符号化 converse `block per-n 適用` のときに **`shannon_converse_single_shot` を `M = M_n` で繰り返し呼ぶ** が、その encoder/decoder は `(Fin n → α) → Fin (M_n)` 形なので新規 plumbing は最小限

### 不在 / 自前で書く必要あるもの

- **「i.i.d. 列の `μ.map X^n` を `Measure.pi` 形に変換する 1 行補題」**: 不在見込み (`iIndepFun_iff_map_fun_eq_infinitePi_map` から導出する自前補題が要、Phase A の山場の 1 つ)
- **`α : Fintype` での `(Fin n → α)` の Fintype + MeasurableSingletonClass 自動発火**: Han Phase D で確認済 (`Fintype.piFintype` + `MeasurableSpace.pi` + `Pi.instMeasurableSingletonClass`)、再利用可

---

## 結論サマリ (各軸 1 行)

| 軸 | 結論 | Phase 影響 |
|---|---|---|
| 1 LLN | `strong_law_ae_real` 完備、引数形 `Pairwise IndepFun + IdentDistrib(X i, X 0)` | Phase B 主役確定、`IsIID` 自前 abbrev は不要 |
| 2 IdentDistrib | 構造体 + `comp` / `pi` / `prodMk` 既存、`iIndepFun ↔ Pairwise IndepFun` 橋渡しは要 Phase A 確認 | Phase A `−log P(·)` lift で `IdentDistrib.comp` 直接使用 |
| 3 log 可測性 | `Real.measurable_log` / `Measurable.log` 既存、`α : Fintype` 下で `Y i` の Integrable は plumbing で押せる | Phase B-1 で 50〜80 行 |
| 4 liminf | `Filter.liminf` API 既存だが `Tendsto → liminf = lim` 1 行補題は本 inventory で未裏取り | Phase D 着手時に loogle、無ければ自前 |
| 5 typical set | `measurableSet_lt` 既存、`Pi.measurableSpace` で `Fin n → α` 側 OK | Phase C で薄い plumbing 20〜30 行 |
| 6 Pi 構築 | `Measure.pi` + `iIndepFun_iff_map_fun_eq_infinitePi_map` 既存、有限 Pi ↔ infinitePi 橋渡しは要自前 | Phase A の山場の 1 つ、30〜50 行見積もり |

---

## Phase A 着手判定

**GO**:

- 強法則とその仮定形は Mathlib 完備、本 plan の skeleton はそのまま書ける
- `IsIID` predicate は不要（Mathlib 流儀の 2 仮定をそのまま受ける）
- 唯一の不確実性は **「`μ.map X^n = Measure.pi (fun _ => μ.map (Xs 0))` の 1 行補題」**の存否、これは Phase A の `i.i.d. 列の formal definition` の中で副産物として書く方針

## Definition of Done (本 inventory)

- [x] 6 軸全て調査完了
- [x] `strong_law_ae_real` の verbatim 署名 + `[..]` プレリク確定
- [x] `IsIID` predicate は Mathlib 不在を裏取り (`rg "IsIID|i\.i\.d"` → 0)
- [x] AEP / typical set / 源符号化定理は Mathlib 不在を裏取り (`rg "AEP|asymptotic.*equipartition|typical_set"` → 0)
- [x] `tendstoInMeasure_of_tendsto_ae` で a.s. → 確率収束 lift 経路確定
- [x] Phase A skeleton (`InformationTheory/Shannon/AEP.lean` の sorry-driven 出だし) が書ける状態

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 本 inventory はまだ起草段階。本体着手で発見があれば追記。 -->
