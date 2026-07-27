# BC S7 全支持への摂動 — M0 在庫

> 親 plan (SoT): [`bc-general-region-plan.md`](bc-general-region-plan.md) §Phase 5「等号 (less
> noisy)」S7 / §撤退ライン **L-BCO9** / §判断ログ 20。前段の在庫:
> [`bc-s6-timesharing-inventory.md`](bc-s6-timesharing-inventory.md) §Q2-6 (責任分界の提案) /
> [`bc-s5-quantization-inventory.md`](bc-s5-quantization-inventory.md)。
> probe は scratchpad の `ProbeS7{Setup,Sigma,Support,Mix,Slots,Unif,Unif2,All}.lean`。
> **`ProbeS7All.lean` (745 行 / 46 decl / sorry 0) が S7 全体を端から端まで通しており、到達点 2 本は
> `#print axioms` が `[propext, Classical.choice, Quot.sound]`** (sorryAx 無し)。
> ⚠ **改名**: 本ファイル中の `bc_uv_subset_superposition` は現行名 `bc_lessNoisy_uv_subset_superposition` (親 plan 判断ログ 25)。以下は改名前の履歴記録なので本文は訂正しない。

## 結論サマリ

- **S7 の到達点は真。しかも probe で全証明が通っている** — 摂動の構成・全支持・2 スロットの下界・
  ε の選択・S6 との合成・内界 union への着地まで、`lake env lean` がエラー 0 で通過済。
  実装 leg は**転記 + docstring + section 整理**に縮む。
- **署名は「五つ組の法」ではなく「達成側の対 `(pU, K)`」で立てる** (§Q1 案 A)。plan の
  「摂動対象は `ν'` が安い」は**内部実装としては正しいが、署名の高さとしては誤り** —
  S6 の到達点は `∃ k pU K, …` で `ν` を隠すので、法レベルの署名では**合成できない**。
  対から五つ組を建て直す糊が **45 行**で、これを払うと S6 は**署名変更ゼロの黒箱**として使える。
- **スロット 1 は罰則ゼロで下界が出る** — S6 在庫が「外れ」と判定した
  `IsUVChannelLaw.condMutualInfo_le_map_cond` (`Quantization.lean:126`) が、S7 では
  **粗視化の向き** (`Bool × U → U`) にそのまま当たり、**5 行**で閉じる。
- **スロット 2 は加法ペナルティ `Real.binEntropy ε` が必須** (乗法だけでは**偽**、§Q2-B に数値反例)。
  Mathlib に `Real.binEntropy` 一族 (連続性・0 での値・`negMulLog` 展開) が既にあり、
  **BC の import 閉包に既に入っている** (`ProbeS7Setup` で機械確認) ⟹ 自作ゼロ。
- **Mathlib の壁 0 件 / プロジェクト側の壁も 0 件** (BC 家系 7 leg 連続)。
  **L-BCO9 は不発動**。
- **行数見積り ~780 行 (数学 658 = probe 実測 + 散文・section 122)**。親 plan の `~120 行` は
  **約 6.5 倍への上方修正**が要る。

### 最も危ない発見 (1 行)

**plan の推す「`ν'` を摂動する」を素直に署名にすると S6 と繋がらない** — S6 の到達点
`exists_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw` は `(pU, K)` を存在量化して `ν` を捨てるため、
「法 → 法」の S7 は消費できない。対レベルで立てれば S6 は無改造で黒箱化する
(S6 の direct consumer は `dep_consumers.sh` 実測で **0 件**なので署名変更も可能だが、不要)。

## Q1 到達点の署名案

### 案 A (**推奨**、probe で証明済) — 対レベル

```lean
theorem exists_fullSupport_bcInfo_ge (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (pU : Measure U) [IsProbabilityMeasure pU] (K : Kernel U α) [IsMarkovKernel K]
    {R₁ R₂ δ : ℝ} (hδ : 0 < δ) (h₁ : R₁ ≤ bcInfo₁ pU K W) (h₂ : R₂ ≤ bcInfo₂ pU K W) :
    ∃ (pU' : Measure U) (_ : IsProbabilityMeasure pU') (_ : ∀ u : U, 0 < pU'.real {u})
      (K' : Kernel U α) (_ : IsMarkovKernel K') (_ : ∀ (u : U) (a : α), 0 < (K' u).real {a}),
      R₁ - δ ≤ bcInfo₁ pU' K' W ∧ R₂ - δ ≤ bcInfo₂ pU' K' W
```

型クラス前提は逐語 (probe の section 変数、`α` と `U` は**同じ universe u**):

```
{α : Type u} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [StandardBorelSpace α]
{β₁ : Type*} [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁]
  [MeasurableSingletonClass β₁] [StandardBorelSpace β₁]
{β₂ : Type*} [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂]
  [MeasurableSingletonClass β₂] [StandardBorelSpace β₂]
{U : Type u} [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U]
  [MeasurableSingletonClass U] [StandardBorelSpace U]
```

- **補助アルファベットは変わらない** (`U` のまま)。`Bool` タグは証明の内部にしか現れないので
  `boolProdAuxEquiv` 的な再ラベルも `bcAuxAlphabet` の番号繰り上げも**要らない**。
- **`hlam : lam ≤ 1` 等の余計な前提を 1 本も要求しない** (S6 と同じ clamp 規約で吸収)。
- **`IsBCLessNoisy` も `IsUVChannelLaw` も要求しない** — S7 は純粋に達成側の regularity 改善。
- 第 2 補助 `V` は内部で `V := U` に潰す (§Q5 の universe 罠)。

### 案 B (内部エンジン、probe で証明済) — 法レベル

```lean
theorem exists_fullSupport_bcInfo_ge_of_isUVChannelLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν)
    {R₁ R₂ δ : ℝ} (hδ : 0 < δ)
    (h₁ : R₁ ≤ (condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)).toReal)
    (h₂ : R₂ ≤ (uvInfo₂ ν).toReal) :
    ∃ (pU : Measure U) (_ : IsProbabilityMeasure pU) (_ : ∀ u : U, 0 < pU.real {u})
      (K : Kernel U α) (_ : IsMarkovKernel K) (_ : ∀ (u : U) (a : α), 0 < (K u).real {a}),
      R₁ - δ ≤ bcInfo₁ pU K W ∧ R₂ - δ ≤ bcInfo₂ pU K W
```

案 A は案 B に 45 行の糊 (`uvLawOfPair` + スロット同定 2 本) を被せたもの。**両方 public にする**
のが正しい: 案 B は more capable / semi-deterministic でも法から直接使える。

### S6 との合成 (probe で証明済、S8 の入口)

```lean
theorem exists_fullSupport_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] (hln : IsBCLessNoisy W) {m : ℕ}
    {ν : Measure (Marton.bcAuxAlphabet.{u} m × V × α × β₁ × β₂)} [IsProbabilityMeasure ν]
    (h : IsUVChannelLaw W ν) {R₁ R₂ δ : ℝ} (hδ : 0 < δ)
    (h₁ : R₁ ≤ (uvInfo₁ ν).toReal) (h₂ : R₂ ≤ (uvInfo₂ ν).toReal)
    (hsum : R₁ + R₂ ≤ (uvInfoSum₂ ν).toReal) :
    ∃ (k : ℕ) (pU : Measure (Marton.bcAuxAlphabet.{u} k)) (_ : IsProbabilityMeasure pU)
      (_ : ∀ x : Marton.bcAuxAlphabet.{u} k, 0 < pU.real {x})
      (K : Kernel (Marton.bcAuxAlphabet.{u} k) α) (_ : IsMarkovKernel K)
      (_ : ∀ (x : Marton.bcAuxAlphabet.{u} k) (a : α), 0 < (K x).real {a}),
      R₁ - δ ≤ bcInfo₁ pU K W ∧ R₂ - δ ≤ bcInfo₂ pU K W
```

本体は **3 行** (S6 を obtain → 案 A を obtain → 組み直す)。さらに内界 union への着地
`(R₁ - δ, R₂ - δ) ∈ bcSuperpositionRegionFullSupport W` が **4 行** (`subset_closure` +
`Set.mem_iUnion` + 実際の witness、probe 通過) ⟹ **S8 に残るのは m → ∞ と δ → 0 の 2 重極限だけ**。

## Q2 目標の真偽判定

### Q2-A 第一象限の暗黙仮定 — **S7 では構造的に発火しない** (S6 との違い)

S6 は `λ = R₂ / b` で割るため `R₂ ≤ 0` の枝が要った。S7 の摂動重み `ε` は **`R₁ R₂` に依存しない**
(依存するのは `A = bcInfo₁`, `B = bcInfo₂` の値だけ) ので、最終不等式は

```
R₁ - δ ≤ A - εA ≤ (1-ε)A ≤ bcInfo₁ (摂動後)       -- R₁ ≤ A と εA < δ から linarith
R₂ - δ ≤ B - (εB + binEntropy ε) ≤ bcInfo₂ (摂動後)
```

で、**`R₁ R₂` の符号をどこにも使わない**。`A, B ≥ 0` (`ENNReal.toReal_nonneg`) だけが要る。
⟹ 負レートでも命題は生きる (probe の `nlinarith` が符号場合分けなしで通っている = 機械確認)。

### Q2-B **スロット 2 の乗法だけの下界は偽** (数値反例、加法ペナルティが必須)

「`uvInfo₂ ((1-ε)ν + εσ) ≥ (1-ε) · uvInfo₂ ν`」は**偽**。反例 (`U = X = Y₂ = Bool`):
`ν` = `U` 一様・`X = U`・`W₂ = 恒等`、`σ` = `U` 一様・`X` は独立一様。混合後は
`p(y ∣ u) = (1-ε)·1{y=u} + ε/2` なので `I = log 2 - h(ε/2)`。

| ε | `I` (混合) | `(1-ε)·I(ν)` | 乗法だけの下界 | 本在庫の下界 `(1-ε)I(ν) - h(ε)` |
|---|---|---|---|---|
| 0.5 | 0.130812 | 0.346574 | ❌ 偽 | -0.346574 ✅ |
| 0.1 | 0.494632 | 0.623832 | ❌ 偽 | 0.298749 ✅ |
| 0.01 | 0.661668 | 0.686216 | ❌ 偽 | 0.630214 ✅ |
| 0.001 | 0.688847 | 0.692454 | ❌ 偽 | 0.684547 ✅ |

(nat 単位。`h` は 2 元エントロピー。再検証は §Q6 の python スクリプト)
⟹ **`binEntropy ε` の加法項は証明技法の都合ではなく命題の性質**。δ → 0 には無害
(`binEntropy` は 0 で連続かつ値 0)。

### Q2-C 退化境界 (2 つ、構造の違うもの)

| 軸 | 設定 | 予測 | 実際 |
|---|---|---|---|
| `|α| = 1` | 入力が 1 文字 | `K` は強制的に全支持、`unif α = dirac`、スロットは 0 | 摂動は恒真に成立 (probe は `Fintype.card` の逆数しか使わず `card = 1` で破れない) |
| `pU` が 1 点集中 | もとの対が退化 | 摂動後は `(1-ε)pU + ε·unif` で全支持 ✅、スロットは連続的に劣化 | `uvSpreadLaw` 側の質量 `ε · card⁻¹ > 0` が下から効く (probe `uvPerturbLaw_map_aux_input_pos`) |

**最も一般な反例 class の再検査**: 仮説は `0 < δ` と 2 本のレート不等式だけで、結論は存在命題。
`W` にも `ν` にも構造条件を課していないので「仮説を満たす最も一般な対象」= 任意の
`(pU, K)` であり、probe がその一般形で通っている ⟹ under-hyp の余地なし。

## Q3 路線比較表 (**採否は probe で決めた**)

| 路線 | 必要資産 | 0-hit | 自作行数 | 採否 |
|---|---|---|---|---|
| **R-A** 構成後の `(pU, K)` を一様平滑化 (`pU' = (1-δ)pU + δ unif`, `K' u = (1-δ)K u + δ unif`) | `Measure.compProd` の**カーネル側**分配則 / タグ 2 本 (または 4 値タグ) / `H(T)` の合成 | カーネル側分配則は未確認 | 2 本のタグ機構 ~120 | ❌ **不採用** — 積の摂動は 4 枝混合になり、タグが 2 本要る |
| **R-B** `ν` (五つ組法) を摂動 | `IsUVChannelLaw.smul/.add` ✅ / S6-a の橋 ✅ / `condDistrib` の全支持 | なし | ~230 | ✅ **採用 (内部実装)**。`.smul/.add` で 1 回の混合が両方の全支持を出す |
| **R-C** `pU` の支持へ再ラベルして全支持を無料で取る | 支持の subtype ↔ `bcAuxAlphabet k'` の equiv / a.e. 単射の下での情報量不変 (既存 `mutualInfo_eq_of_leftInverse` は**大域的**左逆を要求するので使えない) | — | ~60 | ❌ **不要になった** — R-B の混合が `pU` 側の全支持も同時に出すので、再ラベルは 1 行も要らない |
| **R-D = 採用形** R-B を**対レベルの署名**で包む | R-B + `uvLawOfPair` (対 → 五つ組) + スロット同定 2 本 | なし | R-B + 45 | ✅ **採用** — S6 を無改造の黒箱にできる唯一の形 |

**R-A を捨てた理由 (機械的根拠)**: `bcJointDistribution pU' K' W` の `(U,X)` 同時法は
`[(1-ε)pU + ε unif](u) · [(1-ε)K + ε unif](x∣u)` = **4 枝**の混合であり、
「(1-ε)·(元の同時法) + ε·(一様同時法)」**ではない**。R-B の 1 回の混合はこの積を作らない
(混合してから条件付ける) ので枝が 2 本で済む。

**`condDistrib` の心配 (plan §S7 が挙げた `disintegration` の a.e. 性)** は不発:
`condDistrib_apply_of_ne_zero` が `(μ.map U {u})⁻¹ * μ.map (U,X) ({u} ×ˢ s)` という**具体形**を
返すので、`(U,X)` 同時法の 1 点質量が正であることだけから `0 < (K u).real {a}` が 26 行で出る
(probe `uvSatelliteKernel_real_singleton_pos`)。a.e. の抜け道を通る必要がない。

## Q4 資産表

### 4-1 Mathlib (**すべて既存、追加 import は最大 1 本**)

| 用途 | 宣言 | 逐語署名 | file:line |
|---|---|---|---|
| 2 元エントロピー | `Real.binEntropy` | `@[pp_nodot] noncomputable def binEntropy (p : ℝ) : ℝ := p * log p⁻¹ + (1 - p) * log (1 - p)⁻¹` | `Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean:63` |
| ペナルティ → 0 | `Real.binEntropy_continuous` | `@[fun_prop] lemma binEntropy_continuous : Continuous binEntropy` | 同 `:167` |
| 同 | `Real.binEntropy_zero` | `@[simp] lemma binEntropy_zero : binEntropy 0 = 0` | 同 `:65` |
| 符号 | `Real.binEntropy_nonneg` | `lemma binEntropy_nonneg (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : 0 ≤ binEntropy p` | 同 `:93` |
| 対称性 | `Real.binEntropy_one_sub` | `@[simp] lemma binEntropy_one_sub (p : ℝ) : binEntropy (1 - p) = binEntropy p` | 同 `:79` |
| 和形への展開 | `Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub` | `lemma binEntropy_eq_negMulLog_add_negMulLog_one_sub (p : ℝ) : binEntropy p = p.negMulLog + (1 - p).negMulLog` | 同 `:71` |
| 条件付き分布の 1 点値 | `ProbabilityTheory.condDistrib_apply_of_ne_zero` | `lemma condDistrib_apply_of_ne_zero [MeasurableSingletonClass β] (hY : Measurable Y) (x : β) (hX : μ.map X {x} ≠ 0) (s : Set Ω) : condDistrib Y X μ x s = (μ.map X {x})⁻¹ * μ.map (fun a => (X a, Y a)) ({x} ×ˢ s)`。変数束は `{α β Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] {mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ] {X : α → β} {Y : α → Ω} {mβ : MeasurableSpace β}` | `Mathlib/Probability/Kernel/CondDistrib.lean:75` |
| 混合の compProd | `MeasureTheory.Measure.compProd_add_left` | `lemma compProd_add_left (μ ν : Measure α) [SFinite μ] [SFinite ν] (κ : Kernel α β) : (μ + ν) ⊗ₘ κ = μ ⊗ₘ κ + ν ⊗ₘ κ` | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:146` |
| 同 | `MeasureTheory.Measure.compProd_smul_left` | `lemma compProd_smul_left (a : ℝ≥0∞) [SFinite μ] [IsSFiniteKernel κ] : (a • μ) ⊗ₘ κ = a • μ ⊗ₘ κ` | 同 `:176` |
| 一様分布 (**案 1**) | `PMF.uniformOfFintype` + `PMF.toMeasure_apply_singleton` + `PMF.uniformOfFintype_apply` | `def uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] : PMF α` / `theorem uniformOfFintype_apply (a : α) : uniformOfFintype α a = (Fintype.card α)⁻¹` | `Mathlib/Probability/Distributions/Uniform.lean:283` / `:289` |
| 一様分布 (**案 2**) | `MeasureTheory.Measure.count` + `count_singleton` | `Measure.count_singleton (a : α) : Measure.count {a} = 1` | Mathlib (import 閉包内) |

⚠ **`PMF.uniformOfFintype` は BC の import 閉包に入っていない** (`ProbeS7Setup` で実測:
`Unknown constant`)。案 1 を採るなら `import Mathlib.Probability.Distributions.Uniform` を 1 本足す
(probe `ProbeS7Unif2` で全支持まで **5 行**、elaboration 時間の増分は測定範囲で 0)。案 2 は import
ゼロだが `unifLaw` を BC namespace に自作する (**20 行** + F-15「汎用補題が BC namespace に居る」を
1 件増やす)。**案 1 推奨**。

### 4-2 in-project (**S7 の核はすべて既存資産の合成**)

| 用途 | 宣言 | 逐語署名 / 結論形 | file:line |
|---|---|---|---|
| **スロット 1 の罰則ゼロ化** (最重要) | `IsUVChannelLaw.condMutualInfo_le_map_cond` | `(h : IsUVChannelLaw W ν) {f : U → U'} (hf : Measurable f) : condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1) ≤ condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ f q.1)`。型クラスは逐語 `[Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]` + β₁ β₂ 同型 + `[MeasurableSpace U] [StandardBorelSpace U] [Nonempty U]` + `[MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]` + `[MeasurableSpace U'] [StandardBorelSpace U'] [Nonempty U']` + `[IsMarkovKernel W] [IsProbabilityMeasure ν]` (**`[StandardBorelSpace α]` は要求しない**) | `OuterBoundUV/Quantization.lean:126` |
| 混合の恒等式 (スロット 2) | `mutualInfo_compProd_eq_add_lintegral` | `= mutualInfo (μ ⊗ₘ κ) Prod.fst (fun p ↦ g p.2) + ∫⁻ t, mutualInfo (κ t) f g ∂μ` (要 `hrec` = タグ復元) | `Shannon/CondMutualInfoMixture.lean:142` |
| 混合の恒等式 (スロット 1) | `condMutualInfo_compProd_snd_eq_lintegral` | `= ∫⁻ t, condMutualInfo (κ t) f g h ∂μ` (要 `hrec` + 有限性 2 本) | 同 `:164` |
| 測度書換の回避形 | `condMutualInfo_map_comp'` | `(T : Ω → Ω') (hT) (ρ : Measure Ω') [IsFiniteMeasure ρ] (hρ : ρ = μ.map T) … : condMutualInfo ρ f g h = condMutualInfo μ (f ∘ T) (g ∘ T) (h ∘ T)` | `ChannelCoding/CodeToAmbient.lean:527` |
| 連鎖律 | `mutualInfo_chain_rule` | `(μ) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs Yo Zc) (hXs hYo hZc) : mutualInfo μ (fun ω ↦ (Zc ω, Xs ω)) Yo = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc` | `Shannon/CondMutualInfo.lean:214` |
| ペナルティの上界 (1) | `condMutualInfo_eq_condEntropy_sub_condEntropy` | `(μ) [IsProbabilityMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (Zo : Ω → Z) (hXs hYo hZo) : (condMutualInfo μ Xs Zo Yo).toReal = condEntropy μ Xs Yo - condEntropy μ Xs (fun ω ↦ (Yo ω, Zo ω))`。**`Y` (条件付け側) と `Z` に `[Fintype]` を要求する** | `Shannon/Entropy.lean:200` |
| ペナルティの上界 (2) | `mutualInfo_eq_entropy_sub_condEntropy` | `(μ) [IsProbabilityMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (hXs hYo) : (mutualInfo μ Xs Yo).toReal = entropy μ Xs - condEntropy μ Xs Yo` | `Shannon/Bridge.lean:545` |
| ペナルティの上界 (3) | `condEntropy_nonneg` | `{W : Type*} [Fintype W] [Nonempty W] [MeasurableSpace W] [MeasurableSingletonClass W] {Y : Type*} [MeasurableSpace Y] (μ) [IsProbabilityMeasure μ] (Ws Yo) : 0 ≤ condEntropy μ Ws Yo` | `Shannon/Pi.lean:95` |
| エントロピーの定義 (2 点計算) | `entropy` | `noncomputable def entropy (μ : Measure Ω) (Xs : Ω → X) : ℝ := ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})` | `Shannon/Bridge.lean:40` |
| **S6 から逐語再利用する 5 本** | `boolLaw` / `lintegral_boolLaw` / `uvTagTrue` / `uvInfo₂_uvTagTrue` / `condMutualInfo_uvTagTrue` | `boolLaw lam = (lam ⊓ 1) • dirac true + (1 - lam) • dirac false` ほか | `SuperpositionTimeShare.lean:58` `:70` `:83` `:169` `:242` |
| S6-a の橋 (対を読む) | `bcInfo₁_uvCloudLaw` / `bcInfo₂_uvCloudLaw` | `bcInfo₁ (uvCloudLaw ν) (uvSatelliteKernel ν) W = (condMutualInfo ν X Y₁ U).toReal` / `bcInfo₂ … = (uvInfo₂ ν).toReal` | 同 `:366` / `:359` |
| 対 → 情報量の同定 | `bcInfo₁_eq_condMutualInfo_toReal` / `bcInfo₂_eq_mutualInfo_toReal` | `bcInfo₁ pU K W = (condMutualInfo (bcJointDistribution pU K W) (fun q ↦ q.2.1) (fun q ↦ q.2.2.1) (fun q ↦ q.1)).toReal` ほか | `SuperpositionRegion.lean:110` / `:78` |
| 法の構成の雛形 | `uvConstLaw` / `uvConstLaw_isUVChannelLaw` | `((Measure.dirac (0,0,x₀)) ⊗ₘ W.comap (fun r ↦ r.2.2) _).map (fun z ↦ (z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2))` | `OuterBoundUV/Region.lean:401` / `:424` |
| 混合の閉包性 | `IsUVChannelLaw.smul` / `.add` / `.map_auxiliaries` | (S6 在庫 §Q2-4 に逐語) | `Region.lean:153` / `:160` / `:183` |
| 内界の union | `bcSuperpositionRegionFullSupport` | 添字は `(k)(pU)(IsProbabilityMeasure pU)(∀ x, 0 < pU.real {x})(K)(IsMarkovKernel K)(∀ x a, 0 < (K x).real {a})` | `SuperpositionRegion.lean:178` |

### 4-3 **向きが逆で使えない資産** (prose ではなく数値で棄却済)

| 宣言 | 逐語結論 | なぜ使えないか |
|---|---|---|
| `klDiv_mixture_le` | `klDiv (mixtureMeasure lam ν₁ ν₂) (…) ≤ ENNReal.ofReal lam * klDiv ν₁ (…) + ENNReal.ofReal (1-lam) * klDiv ν₂ (…)` (第 1 周辺が共通のとき) | **凸性 = 上界**。S7 が要るのは**下界**。§Q2-B の数値反例が「下界は罰則なしでは存在しない」ことを示すので、どんな凸性補題からも出ない | `Shannon/RateDistortion/Convexity.lean:336` |

## Q5 前提が事故りやすい箇所 (key-preconditions box)

- **`condMutualInfo` の中の測度を `rw` すると motive not type correct** (S6 申し送りの再発、実測)。
  ⟹ 「forget 後の測度」を**引数 `ρ` + `hρ : ρ = μ.map T` として受ける**形に補題を立てる
  (`condMutualInfo_map_comp'` と同じ設計)。**`mutualInfo` 側では発火しない** (instance 引数を
  持たないため) ので、スロット 2 の同じ書換は素通りする。この非対称は probe で実測。
- **`condMutualInfo_eq_condEntropy_sub_condEntropy` は条件付け変数の型に `[Fintype]` を要求する**
  ⟹ ペナルティ補題は `U` が有限型でないと**文が書けない**。S7 の適用先は `bcAuxAlphabet k` なので OK。
- **`uvSatelliteKernel` の def が `[IsFiniteMeasure ν]` を要求** (S6 既知) +
  `condDistrib_apply_of_ne_zero` が `[MeasurableSingletonClass U]` と `[StandardBorelSpace α]
  [Nonempty α]` を要求。
- **`boolLaw` の重み規約**: `boolLaw lam` は **true に `lam ⊓ 1`**、**false に `1 - lam`**。
  S7 は「情報を保つ枝」を true に置くので `lam := ENNReal.ofReal (1 - ε)` を渡す。
  `lam ⊓ 1 = lam` / `1 - lam = ofReal ε` は `hε : 0 < ε < 1` から出る。
- **`V := PUnit` は universe 推論に失敗する** (`failed to infer universe levels`、実測)。
  ⟹ 対から法を建てるときの第 2 補助は **`V := U`** (`(pU ⊗ₘ K).map (fun p ↦ (p.1, p.1, p.2))`)。
- **`Measure.fst_compProd` は `.fst` 形なので `rw` の pattern が当たらない** ⟹
  `show (ρ ⊗ₘ κ).map Prod.fst = ρ from Measure.fst_compProd _ _` と `show` で渡す
  (`uvConstLaw_isUVChannelLaw` の先例と同じ、実測で 1 度踏んだ)。
- **`ENNReal.ofReal_lt_ofReal_of_pos` は存在しない** ⟹ `(ENNReal.ofReal_lt_ofReal_iff one_pos).mpr`。
- **`positivity` は `ℝ≥0∞` の `a⁻¹ * b ≠ 0` を出せない** ⟹
  `mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (hpos u a).ne'` と手で書く (実測)。
- `uvRelabel` は `def` なので合成後の `(uvRelabel f g q).1` は自動で簡約されない ⟹
  `mutualInfo_map_comp` の後に **`rfl` を 1 行**足す (実測)。

## Q6 probe (すべて `lake env lean` がエラー 0)

scratchpad =
`/private/tmp/claude-502/-Users-haruka-dev-lean-projects/40d6cc1b-8a8b-4830-b6ad-cabfa161585a/scratchpad`
(`InformationTheory/` は 1 バイトも触っていない)。

| probe | 内容 | 結果 | 行数 |
|---|---|---|---|
| **P0** `ProbeS7Setup` | import 閉包の確認 (`Real.binEntropy` 一族 ✅ / `PMF.uniformOfFintype` ❌) + 12 本の `#check` | ✅ | — |
| **P1** `ProbeS7Sigma` | `unifLaw` + **`uvLawOfInput`** (任意の `(U,V,X)` 法から channel law を建てる一般形) + `IsUVChannelLaw` + `(U,X)` 周辺の同定 | ✅ 全証明 | 84 |
| **P2** `ProbeS7Support` | **`uvSatelliteKernel` の全支持** (`condDistrib_apply_of_ne_zero` 経由) | ✅ 全証明 | 45 |
| **P3** `ProbeS7Mix` | `boolLaw` の 2 点値 + **タグのエントロピー = `binEntropy`** + タグ付き混合 (`uvTagFalse` / `uvMixKernel` / `uvTaggedMixLaw` + instance 3 本 + 和形 + `ae_tag` + `IsUVChannelLaw` + forget 写像) + **混合下界 2 本** | ✅ 全証明 | 205 |
| **P4** `ProbeS7Slots` | **タグ忘却の 2 本** (スロット 1 = 罰則ゼロ / スロット 2 = `+ entropy(tag)`) | ✅ 全証明 | 79 |
| **P5** `ProbeS7Unif2` | Mathlib の `PMF.uniformOfFintype` 経路 (import 1 本追加) | ✅ | 14 |
| **P6** `ProbeS7All` | 上記を 1 ファイルに統合 + `uvSpreadLaw` / `uvPerturbLaw` + **ε の選択** + **到達点 2 本** + **S6 との合成** + **内界 union への着地** | ✅ **46 decl / sorry 0 / `#print axioms` に sorryAx 無し** | **745** |

**落ちた probe (逐語エラー、実装時に再発する)** — 順に §Q5 の 7 項目。とくに
`rw [uvTaggedMixLaw_map_forget] at hforget` の **motive is not type correct** は
「`ρ` 引数形の補題を先に立てる」以外に回避手がなかった。

**数値反例の再検証** (§Q2-B):

```
python3 -c "import math
h=lambda p: 0.0 if p<=0 or p>=1 else -p*math.log(p)-(1-p)*math.log(1-p)
for e in (0.5,0.1,0.01,0.001): print(e, math.log(2)-h(e/2), (1-e)*math.log(2))"
```

## Q7 壁 / 撤退ライン

### Mathlib の壁 — **0 件** (7 leg 連続) / プロジェクト側の壁も **0 件**

| クエリ | 結果 | 影響 |
|---|---|---|
| loogle `Real.binEntropy` | `Found 28 declarations` | 連続性・0 での値・非負・対称性・`negMulLog` 展開がすべて既存 ⟹ **ペナルティ側の自作 0** |
| loogle `Real.negMulLog, Continuous` | `Found one declaration` (`Real.continuous_negMulLog`) | 予備経路も在り |
| loogle `PMF.uniformOfFintype` | `Found 6 declarations` | 一様分布は既存 (import 1 本) |
| loogle `MeasureTheory.Measure.compProd (_ + _) _` / `(_ • _) _` | 各 `one matches` | 混合の compProd 分配則は既存 |
| loogle `ProbabilityTheory.condDistrib_apply_of_ne_zero` | `Found one declaration` | 条件付き分布の 1 点値の具体形が既存 |
| loogle **`ConcaveOn, InformationTheory.klDiv`** | **`Found 0 declarations`** | 相互情報量の入力分布についての**凹性は Mathlib に無い**。in-project も `rg 'concave'` 実測で 0 (あるのは `negMulLog` / `binEntropy` の凹性のみ) ⟹ **しかし S7 は凹性を使わない** (タグ経由の混合恒等式で代替、probe 通過) ⟹ **壁ではない** |

⚠ 0-hit は 1 件だけで、それは**採用路線が要求しない資産**についてのもの。
「凹性が無いから自作 150 行」という見積りは**誤り**なので立てないこと。

### L-BCO9 との距離 — **不発動**

発動条件は (凍結文言の読み替え後)「逆包含が閉じない」。S7 の全構成要素が probe で compile 通過し、
到達点 2 本が sorryAx-free なので、**S7 が閉塞要因になる可能性は無い**。残る判定は S8
(m → ∞ と δ → 0 の 2 重極限 + closure) だが、内界 union への着地まで probe で通っているので、
S8 に残るのは極限の取り回しだけ。**退避 (`bc_uv_subset_superposition` を署名保持で `sorry` +
`@residual(plan:bc-lessnoisy-converse-quantization)`) は S7 では要らない**。

## Q8 行数見積り (**数学と散文を別枠**、判断ログ 20-(a))

| step | 内容 | 数学 (probe 実測) | 散文・section | 計 |
|---|---|---|---|---|
| **S7-a** ★gateway | 一様法 + `uvLawOfInput` + `uvUniformLaw` + `uvPerturbLaw` + **全支持 2 本** | 183 | 25 | ~208 |
| **S7-b** | タグ付き混合 (`uvTagFalse` / `uvMixKernel` / `uvMixLaw` + 6 補題) | 106 | 15 | ~121 |
| **S7-c** | タグの `binEntropy` 計算 + 混合下界 2 本 + タグ忘却 2 本 + タグ法 + 摂動後スロット 2 本 | 220 | 20 | ~240 |
| **S7-d** | ε の選択 + 到達点 (案 B → 案 A) + S6 との合成 | 149 | 20 | ~169 |
| module doc | `## Main definitions` / `## Main statements` / 設計の 3 段落 | — | 42 | ~42 |
| 計 | | **658** | **122** | **~780** |

帯は **720–850**。S6 (probe 295 → 実測 545、+85%) のような上振れは**期待しない** — S6 の probe は
核の数学だけを覆っていたのに対し、本 probe は**配線と到達点と合成まで覆っている**ので、増分は
module doc と docstring と `omit` に限られる (S5 が 280 → 289 で的中したのと同じ構造)。

**ファイル配置**: 新規 `InformationTheory/Shannon/BroadcastChannel/SuperpositionFullSupport.lean`
(**トップ直下**、import は `SuperpositionTimeShare` の **1 本だけ**。probe で cycle 無しを機械確認)。
⚠ これで `Superposition*` クラスタが **3 ファイル**になり、親 plan §後続作業 **F-19 の発火条件**
(「3 ファイルに達する」) を満たす。`Superposition/` への昇格は **S8 と同じ leg にまとめる**のを推す
(S8 のファイルも同時に置けるので、ディレクトリ名を 1 度で決められる)。

## Q9 実装 leg への申し送り

### 着手順 (gateway atom = **S7-a**)

**S7-a を最初に切る**。理由は 3 つ: (a) `condDistrib` の全支持が唯一「Mathlib の細部に依存する」
部分で、ここが通れば残りは情報量の代数、(b) S7-b/c/d のすべてが `uvPerturbLaw` の存在を前提にする、
(c) probe の実測でも最初に落ちた (`positivity` / `Measure.fst_compProd`) のがここ。

### 親 plan で書き換えが要る箇所 (編集は plan の担当)

1. **§Phase 5 S7 の行数 `(~120 行)` → `~750 行 (数学 632 + 散文 122、probe 実測 745 行)`**。
2. **§S7 の「摂動対象は `(pU, K)` ではなく `ν'` が安い」に補足** — **内部実装としては正しい**が、
   **署名は対レベル**でないと S6 と繋がらない (§Q1)。「対 → 五つ組 → 摂動 → 対」を 1 本の定理に
   閉じ込めるのが答え。
3. **§S7 の「混合側の 3 本は `hlam : lam ≤ 1` を要求しない」は S7 でも維持** — clamp 規約
   (`lam ⊓ 1`) をそのまま摂動法にも使うので、`uvPerturbLaw` の `IsProbabilityMeasure` は
   **無条件 instance** にできる (probe 通過)。
4. **§撤退ライン L-BCO9**: S7 側は**不発動が確定**した (到達点 2 本が probe で sorryAx-free)。
   判定の担い手は **S8 のみ**に移る。
5. **§在庫 に新規行 1 本**: `SuperpositionFullSupport.lean` (トップ直下、import 1 本)。
6. **§後続作業 F-19 の発火条件を満たした** — クラスタが 3 ファイルになる。昇格は S8 と同 leg を推奨。
7. **§後続作業に 2 件追加候補**:
   - **`uvTimeShareLaw` は `uvMixLaw` の特殊化** — `uvTimeShareLaw ν u₀ lam
     = uvMixLaw ν (ν.map (uvRelabel (fun _ ↦ u₀) id)) lam` (両辺とも `uvTagConst` に一致、
     `Measure.map_map` 1 行)。S7 が入った後に S6 側を特殊化として建て直せば**重複 ~60 行が消える**。
     `uvTagTrue` の direct consumer は `dep_consumers.sh` 実測で **6 decl / 1 file (すべて同ファイル)**
     なので波及ゼロ。**S7 の leg では触らない** (diff を読める大きさに保つ)。
   - **`uvLawOfInput` は `uvConstLaw` (`Region.lean:401`) の一般化** — 上流へ移して
     `uvConstLaw` をその dirac 特殊化にすると `uvConstLaw_isUVChannelLaw` の 20 行が消える。
8. **§判断ログに 1 件** — 「在庫が『外れ』と判定した資産は、**向きが反転した次の step で当たる**」:
   S6 在庫 §親 plan 書換 5 が `IsUVChannelLaw.condMutualInfo_le_map_cond` を「欲しい向きと逆」と
   判定したが、S7 は**まさにその向き** (補助の粗視化) を必要とし、5 行で当たった。
   ⟹ 却下は「この step では」と限定して書く。

### 命名の提案 (`docs/rules/naming.md` に合わせる)

`uvUniformLaw` (probe の `uvSpreadLaw`) / `uvPerturbLaw` / `uvTagFalse` / `uvMixKernel` /
`uvMixLaw` (probe の `uvTaggedMixLaw`) / `uvLawOfInput` / `uvLawOfPair` /
`exists_fullSupport_bcInfo_ge` (対レベル) / `exists_fullSupport_bcInfo_ge_of_isUVChannelLaw` (法レベル)。
`unifLaw` は **採らない** (BC namespace に汎用 def を増やす = F-15 の再生産) — Mathlib の
`PMF.uniformOfFintype` を import する。

## 着手のための skeleton

```lean
import InformationTheory.Shannon.BroadcastChannel.SuperpositionTimeShare
import Mathlib.Probability.Distributions.Uniform

/-!
# Broadcast channel — perturbing an achievability pair to full support

The superposition inner bound is a union over the pairs whose cloud law and satellite kernel
give every letter positive mass, while the pair read off a channel law need not.  Mixing the
law with the uniform one repairs both at once …
(`## Main definitions` / `## Main statements` は §Q1 / §Q9 の名前をそのまま並べる)
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal Topology

universe u

/-- The channel law generated by an arbitrary law of the auxiliaries and the input letter. -/
noncomputable def uvLawOfInput (W : BCChannel α β₁ β₂) (ρ : Measure (U × V × α)) :
    Measure (U × V × α × β₁ × β₂) :=
  (ρ ⊗ₘ W.comap (fun r : U × V × α ↦ r.2.2) (measurable_snd.comp measurable_snd)).map
    (fun z ↦ (z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2))

/-- The channel law whose auxiliary and input letter are uniform and independent. -/
noncomputable def uvUniformLaw (W : BCChannel α β₁ β₂) (v₀ : V) : Measure (U × V × α × β₁ × β₂) :=
  uvLawOfInput W (((PMF.uniformOfFintype U).toMeasure).prod
    ((Measure.dirac v₀).prod ((PMF.uniformOfFintype α).toMeasure)))

/-- The channel law perturbed toward the uniform one, clamped so that it is a probability
measure for every weight. -/
noncomputable def uvPerturbLaw (W : BCChannel α β₁ β₂) (ν : Measure (U × V × α × β₁ × β₂))
    (v₀ : V) (lam : ℝ≥0∞) : Measure (U × V × α × β₁ × β₂) :=
  (lam ⊓ 1) • ν + (1 - lam) • uvUniformLaw W v₀

end InformationTheory.Shannon.BroadcastChannel
```

⚠ skeleton に `sorry` は無く、**本在庫のどの補題にも `@residual` を付けない** — probe で全証明が
compile 通過しており、埋まらない穴は 1 つも残っていない。
