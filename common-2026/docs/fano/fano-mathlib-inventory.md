# Fano Phase 3 のための Mathlib インフラ在庫調査

> ムーンショット全体計画は [`docs/fano/fano-moonshot-plan.md`](fano-moonshot-plan.md)。本ファイルは Phase 2 の成果物。
>
> **Status (2026-05-09): Phase 3 達成済み (deterministic decoder 形)。**
> 本ファイルの予測 (plumbing 量・skeleton 構成・撤退ラインへの近さ) はおおむね当たり、Phase 3 は `Common2026/Fano/Measure.lean` で完成。各セクションの予測値と実測値の差分を「### Phase 3 結果」として末尾に追記している。

## 一行サマリ

**Phase 3 で使う API のうち、実体（測度・カーネル・不等式・凹性）はほぼ 100% Mathlib に既存。ただし「測度論的条件付きエントロピー `condEntropy`」だけが存在しないので、ここは自前で定義する必要がある。** plumbing 量は Phase 1 と同程度〜やや上で見積もれる。撤退ラインに触れるリスクは現時点では見えていない。

**Phase 3 結果**: 予測通り、自前定義したのは `condEntropy μ Xs Yo`、`errorProb`、`pointwiseErrorProb`、`diracPMF`、`pointwise_fano` の 5 種で計 ~150 行。`condDistrib` から `FiniteJointPMF X X` への橋渡しは「第二座標を Dirac にする `diracPMF`」を経由して `pointwise_fano` 7 行で完了。撤退ラインには触れず。

---

## Phase 3 の最終形（再掲）

```lean
theorem fano_inequality_measure_theoretic
    {X : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {Ω : Type*} [MeasurableSpace Ω]
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝕏 : Ω → X) (𝕐 : Ω → Y) (𝕏̂ : Ω → X)
    (h𝕏 : Measurable 𝕏) (h𝕐 : Measurable 𝕐) (h𝕏̂ : Measurable 𝕏̂)
    (hcard : 2 ≤ Fintype.card X) :
    condEntropy μ 𝕏 𝕐 ≤
      Real.binEntropy (errorProb μ 𝕏 𝕏̂)
        + errorProb μ 𝕏 𝕏̂ * Real.log ((Fintype.card X : ℝ) - 1)
```

証明戦略:

```
H(X | Y) = ∫ H(X | Y=y) dP_Y(y)                                -- 条件付きエントロピーの分解
        ≤ ∫ [h(Pe(y)) + Pe(y) log(|X|-1)] dP_Y(y)              -- 各 y で Phase 1 の離散 Fano
        ≤ h(∫ Pe(y) dP_Y(y)) + (∫ Pe(y) dP_Y(y)) log(|X|-1)    -- binEntropy の凹性 + Bochner Jensen
        = h(Pe) + Pe · log(|X|-1)                              -- Pe の積分形と直接形の同一視
```

---

## API 在庫テーブル

### A. 測度論的エントロピー（Phase 3 の中核）

| 概念 | Mathlib API | file:line | 状態 | Phase 3 での扱い |
|---|---|---|---|---|
| KL ダイバージェンス | `klDiv (μ ν : Measure α) : ℝ≥0∞` | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57` | ✅ 既存 | 直接は使わない可能性が高いが、`H(X)` を `klDiv` で書く流派もある。当面 reference のみ |
| KL の chain rule | `klDiv_compProd` 系 | `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean` | ✅ 既存 | 同上 |
| `Real.negMulLog` (= -x log x) | `def negMulLog (x : ℝ) : ℝ := -x * log x` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:164` | ✅ Phase 0 で利用済み | エントロピー積分の被積分関数 |
| `Real.binEntropy` | `def binEntropy (p : ℝ) : ℝ := p * log p⁻¹ + (1-p) * log (1-p)⁻¹` | `Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean:63` | ✅ Phase 0 で利用済み | 右辺の二値エントロピー項 |
| `Real.qaryEntropy` | `def qaryEntropy (q : ℕ) (p : ℝ) : ℝ := p * log (q-1 : ℤ) + binEntropy p` | `Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean:213` | ✅ Phase 0 で利用済み | 右辺全体 |
| **測度論的 `condEntropy(X \| Y)`** | — | — | ❌ **不在** | **自前で定義する。最大の自作タスク** |
| **測度論的 `entropy(X)`** (測度のシャノンエントロピー) | — | — | ❌ **不在** | 自前定義（または condEntropy 経由で間接的に） |
| **測度論的 `mutualInfo`** | — | — | ❌ **不在** | Phase 3 では DPI を使わなくても通せるはず（Phase 1 の DPI を pointwise 適用すれば十分） |

### B. 正則条件付き分布 / 条件付き期待値

| 概念 | Mathlib API | file:line | 状態 | Phase 3 での扱い |
|---|---|---|---|---|
| 正則条件付き分布（変数版） | `condDistrib (Y : α → Ω) (X : α → β) (μ : Measure α) : Kernel β Ω` | `Mathlib/Probability/Kernel/CondDistrib.lean:64` | ✅ 既存 | **Phase 3 の主役**: `condDistrib 𝕏 𝕐 μ : Kernel Y X` で「`Y=y` 条件下の `X` の分布」を取り出す |
| 正則条件付き分布（測度版） | `Measure.condKernel (ρ : Measure (α × Ω)) : Kernel α Ω` | `Mathlib/Probability/Kernel/Disintegration/StandardBorel.lean:361` | ✅ 既存 | 同上の別形。joint measure を直接持っているときに使う |
| disintegration 等式 | `compProd_map_condDistrib` 等 | `Mathlib/Probability/Kernel/CondDistrib.lean:82` | ✅ 既存 | `(μ.map X) ⊗ₘ condDistrib Y X μ = μ.map (fun a => (X a, Y a))` |
| 条件付き期待値 | `condExp m μ f : α → E` (notation `μ[f \| m]`) | `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean:98` | ✅ 既存 | 補助。Phase 3 の主軸は `condDistrib` だが、tower law (`integral_condExp`) を使う場面はある |
| 条件付き Jensen | `ConvexOn.map_condExp_le`, `ConcaveOn.condExp_map_le` | `Mathlib/MeasureTheory/Function/ConditionalExpectation/CondJensen.lean:168, 184` | ✅ 既存 | 当面は不使用（Bochner Jensen で間に合う） |

**重要な制約:** `condDistrib` / `condKernel` は **`StandardBorelSpace`** が要る。

ただし **どちら側に課されるかが Phase 2 時点の予測と異なっていた** ので明記する:

- Mathlib の `condDistrib (Y : α → Ω) (X : α → β) μ : Kernel β Ω` は **出力側 `Ω`（条件付きで取り出す変数の codomain）に `[StandardBorelSpace Ω]` を要求**する。条件付け側 `β`（条件として固定する変数の codomain）には StandardBorel は不要。
- 我々の Phase 3 設定 `condDistrib Xs Yo μ : Kernel Y X` では出力側 = 我々の `X`、条件付け側 = 我々の `Y`。
- 我々の `X` は `[Fintype X] [DecidableEq X] [MeasurableSpace X] [MeasurableSingletonClass X]` を持っている。Mathlib の instance チェイン `[Countable X] [MeasurableSingletonClass X] → [DiscreteMeasurableSpace X] → [StandardBorelSpace X]` が自動で発火するので、`X` 側は明示的に何も追加しなくても StandardBorel が成立する。
- したがって `Y` の側に追加の制約は不要。`Y : MeasurableSpace`（任意）のままで Phase 3 主定理が通る。

→ **計画 ([fano-moonshot-plan.md](fano-moonshot-plan.md)) の `Y : 任意の可測空間` の表現は維持する**。Phase 2 時点のメモで「`Y : StandardBorelSpace` に修正必要」と書いていた箇所は誤りなので訂正。

### C. Bochner 積分上の Jensen

| API | file:line | signature | Phase 3 での扱い |
|---|---|---|---|
| `ConvexOn.map_integral_le` | `Mathlib/Analysis/Convex/Integral.lean:199` | 確率測度上、`g (∫ f dμ) ≤ ∫ g∘f dμ`（凸） | 不使用 |
| **`ConcaveOn.le_map_integral`** | `Mathlib/Analysis/Convex/Integral.lean:208` | 確率測度上、`∫ g∘f dμ ≤ g (∫ f dμ)`（凹） | **`binEntropy` の凹性に直接適用する第一候補** |
| `ConvexOn.map_average_le` / `ConcaveOn.le_map_average` | `Mathlib/Analysis/Convex/Integral.lean:130, 141` | 有限測度版（probability normalization なしで average で書ける） | バックアップ |
| `Real.strictConcaveOn_binEntropy` | `Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean:445` | `StrictConcaveOn ℝ (Icc 0 1) binEntropy` | Phase 0 で利用済み。Bochner Jensen と組み合わせる |
| `Real.concaveOn_negMulLog` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:227` | `ConcaveOn ℝ (Set.Ici 0) negMulLog` | エントロピー単項に適用 |

**`ConcaveOn.le_map_integral` の前提条件**（事故が起きやすいので明記）:

- `[IsProbabilityMeasure μ]`
- `ContinuousOn g s`（`binEntropy` は `[0,1]` 上連続なので OK、ただし `binEntropy` の連続性 lemma を確認しておく必要あり）
- `IsClosed s`（`Icc 0 1` は閉なので OK）
- `∀ᵐ x ∂μ, f x ∈ s` （`Pe(y) ∈ [0,1]` を a.e. で示す。確率なので簡単）
- `Integrable f μ` と `Integrable (g ∘ f) μ`（boundedness から従う、`binEntropy` も `Pe` も `[0,1]` 上有界）

### D. 離散 PMF と測度の橋渡し

| API | file:line | 状態 | Phase 3 での扱い |
|---|---|---|---|
| `PMF.toMeasure : Measure α` | `Mathlib/Probability/ProbabilityMassFunction/Basic.lean:213` | ✅ 既存 | 離散辺縁 → 測度 |
| `PMF.toMeasure.toPMF = id`, `id` | `Mathlib/Probability/ProbabilityMassFunction/Basic.lean:320, 341` | ✅ 既存 | PMF と離散測度の同型 |
| `PMF.ofFintype` | `Mathlib/Probability/ProbabilityMassFunction/Constructions.lean:203` | ✅ 既存 | Phase 1 の `FiniteJointPMF` の marginal を PMF に翻訳する出口 |
| `PMF.integral_eq_sum` | `Mathlib/Probability/ProbabilityMassFunction/Integrals.lean:47` | ✅ 既存 | 離散和 ↔ 測度上積分の橋渡し |
| `Measure.compProd` (`μ ⊗ₘ κ`) | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:43` | ✅ 既存 | `Measure X × Kernel X (Measure Y)` から joint `Measure (X × Y)` を組む |
| `Measure.dirac` | `Mathlib/MeasureTheory/Measure/Dirac.lean` | ✅ 既存 | 必要なら点質量で離散測度を組む |

---

## 「Phase 3 で使う API のうち X% が Mathlib に既存」

カウント方法: 上のテーブル A〜D で「Phase 3 で実際に使う」とマークした項目を分母、`✅ 既存` を分子。

- 分母（Phase 3 で使う API）: 12 項目
  - エントロピー定数項（`negMulLog`, `binEntropy`, `qaryEntropy`）×3
  - 凹性（`strictConcaveOn_binEntropy`, `concaveOn_negMulLog`）×2
  - `condDistrib` / `condKernel` / `compProd_map_condDistrib`×3
  - Bochner Jensen（`ConcaveOn.le_map_integral`）×1
  - PMF ↔ Measure 橋渡し（`PMF.toMeasure`, `PMF.ofFintype`, `compProd`）×3
- 分子（既存）: 12 項目
- **既存率 100%（実体ベース）**

ただし「Phase 3 の主定理を直接書ける高レベル API」（`condEntropy`, `mutualInfo`, `entropy`）は **0%** 既存（不在）。そこは自前で定義する。

> **要約**: **Phase 3 で必要な道具（測度・分布・凹関数・不等式）は全部 Mathlib に揃っている。我々が書くのは「それらを組み合わせて測度論版 condEntropy を定義し、Phase 1 の離散 Fano を pointwise に適用して積分する」糊コードのみ**。

---

## 自作が必要な要素（Phase 2.5 候補）

優先度順:

1. **`condEntropy μ 𝕏 𝕐 : ℝ`** の定義
   - 推奨実装: `condDistrib 𝕏 𝕐 μ : Kernel Y X` を取り、各 `y : Y` で `H(X | Y=y) := ∑ x : X, negMulLog ((condDistrib 𝕏 𝕐 μ y).real {x})` を計算し、`P_Y = μ.map 𝕐` で積分する。
   - 出力側 `X` が `Fintype + MeasurableSingletonClass` なので自動で StandardBorel が成立し、`condDistrib` の評価先 `Kernel Y X` の各 `y` での値は `Measure X`（離散）になる。`MeasurableSingletonClass X` から `(.real {x})` で点確率を取り出せる。
2. **`errorProb μ 𝕏 𝕏̂ : ℝ`** の定義
   - `μ.real {ω | 𝕏 ω ≠ 𝕏̂ ω}` （`𝕏 ≠ 𝕏̂` の事象の確率）。
3. **「pointwise 離散 Fano」の橋渡し**
   - `condDistrib 𝕏 𝕐 μ y` を Phase 1 の `FiniteJointPMF X X` に翻訳する補題、または直接 measure 上で離散 Fano を再証明する補題。**ここが Phase 3 最大の plumbing リスク**。
4. **`Pe = ∫ Pe(y) dP_Y` の同一視**
   - 直接形 `μ.real {𝕏 ≠ 𝕏̂}` と積分形 `∫ y, (condDistrib ... y) {x : 𝕏̂...} ∂P_Y` の同値。
5. **`Pe(y) ∈ [0,1]` の a.e. 確認**
   - `IsProbabilityMeasure (condDistrib ... y)` から従う、自明だが必要。
6. **`Integrable (binEntropy ∘ Pe) P_Y`**
   - boundedness（`binEntropy ≤ log 2`、`Pe ∈ [0,1]`）から従う。

工数感（Phase 1 の plumbing コストとの比較）:

- Phase 1 で plumbing に費やしたターン: log-sum 不等式の自作（70 行）、`pushforward` / `condEntropy_le_pushforward` （200+ 行）。
- Phase 3 は **「Phase 1 の per-x̂ 離散 Fano を per-y で測度論的に再現する」**ので、plumbing 量は同程度か 1.5 倍程度を見込む。**1〜2 週間**を予算とする。

---

## 撤退ライン更新

[fano-moonshot-plan.md](fano-moonshot-plan.md) の撤退ライン:

> **Phase 2 のインベントリで `ProbabilityTheory.condEntropy` 系が想像以上に未整備**だった場合
> → Phase 3 を「`PMF`（可算離散）への拡張」に切り替える

判定: **発動しない**。

- `condEntropy` 自体は不在だが、定義に必要な primitive (`condDistrib`, `negMulLog`, `compProd`, `MeasurableSingletonClass`) は完備
- 自前定義は数十行で書けると見込まれ、その代わりに Mathlib への将来貢献余地を残せる（副次的メリット）
- Phase 3 の本来の数学的中身（pointwise 離散 Fano + Bochner Jensen）は計画通り

ただし以下を **新規撤退ライン**として追加:

- **Phase 3 開始 1 週間以内に `condEntropy` 自作 + 「`condDistrib` から `FiniteJointPMF` 経由で Phase 1 を呼ぶ」橋渡し補題が書けない**場合
  → Phase 3 を「`PMF X × Kernel X (PMF Y)` の Markov 形」（軸 1+2 の中間案）に縮退する
  → これでも `Y` を可算離散に押し込めるので Cover-Thomas の半分には到達できる
  → **判定結果（2026-05-09）**: 発動せず。`diracPMF` 経由で Phase 1 をそのまま呼べた

---

## Phase 3 着手のための skeleton

> **後日追記**: 完成形は `Common2026/Fano/Measure.lean` を参照 (391 行)。当初 skeleton (下記) との差分:
>
> 1. signature の `𝕏̂ : Ω → X` (randomized decoder) は **`decoder : Y → X` (deterministic measurable)** に固定して着地。randomized 版は Phase 3.5 へ
> 2. `errorProb` は `μ.map (Xs, decoder ∘ Yo)` 経由ではなく `μ.real {ω | Xs ω ≠ decoder (Yo ω)}` で直接定義
> 3. Phase 1 への橋渡しは「`condDistrib Xs Yo μ y : Measure X` を第二座標が Dirac の `FiniteJointPMF X X` に乗せる `diracPMF` constructor + 5 つの計算 lemma」で実装。これにより `pointwise_fano` が 7 行で書ける
> 4. 主定理証明は Step 1〜4 の `calc` 一発 chain (sub-lemma に切らず `have` で局所構築)

`Common2026/Fano/Measure.lean`（または `Phase3.lean`）の出だし：

```lean
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Common2026.Fano  -- Phase 1 の離散 Fano を呼ぶ

namespace InformationTheory.MeasureFano

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {X : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X] [MeasurableSingletonClass X]
variable {Y : Type*} [MeasurableSpace Y]

/-- 測度論版・条件付きシャノンエントロピー: H(X | Y) = ∫ H(X | Y=y) dP_Y(y)。 -/
noncomputable def condEntropy (𝕏 : Ω → X) (𝕐 : Ω → Y) : ℝ :=
  ∫ y, ∑ x : X, Real.negMulLog ((condDistrib 𝕏 𝕐 μ y).real {x}) ∂(μ.map 𝕐)

/-- 誤り確率: Pe = P(𝕏 ≠ 𝕏̂)。 -/
noncomputable def errorProb (𝕏 𝕏̂ : Ω → X) : ℝ :=
  (μ.map (fun ω => (𝕏 ω, 𝕏̂ ω))).real {p | p.1 ≠ p.2}

theorem fano_inequality_measure_theoretic
    (𝕏 𝕏̂ : Ω → X) (𝕐 : Ω → Y)
    (h𝕏 : Measurable 𝕏) (h𝕐 : Measurable 𝕐) (h𝕏̂ : Measurable 𝕏̂)
    (hcard : 2 ≤ Fintype.card X) :
    condEntropy μ 𝕏 𝕐 ≤
      Real.binEntropy (errorProb μ 𝕏 𝕏̂)
        + errorProb μ 𝕏 𝕏̂ * Real.log ((Fintype.card X : ℝ) - 1) := by
  sorry

end InformationTheory.MeasureFano
```

最初の `sorry` を「Phase 1 の離散 Fano を pointwise に呼ぶ」形で割っていくのが Phase 3-M1。

---

## Phase 2 まとめ

- インベントリは **`docs/fano/fano-mathlib-inventory.md`**（このファイル）
- Phase 3 で使う API のうち実体は 100% 既存。高レベル API（`condEntropy` 等）のみ自作
- 計画書 (`fano-moonshot-plan.md:34`) の `Y : 任意の可測空間` はそのままで OK（Phase 2 時点では `[StandardBorelSpace Y]` 必要と書いていたが、Phase 3 完成時に「`condDistrib` の StandardBorel 要求は出力側 `X` に課されるが `Fintype + MeasurableSingletonClass` から自動 derive」と判明し撤回）
- 最大リスク: 「`condDistrib` から離散 PMF への翻訳補題」の plumbing 量（1〜2 週間予算）
- 撤退ラインは新規追加（Phase 3 開始 1 週間以内に condEntropy + 橋渡しが書けないとき → PMF 軸への縮退）
- Phase 3 着手 ready

### Phase 3 結果（後日追記, 2026-05-09）

- **達成**: `Common2026/Fano/Measure.lean` の `fano_inequality_measure_theoretic` が `lake env lean` silent
- 達成形は **deterministic decoder `Y → X` (measurable) 形**。randomized decoder `𝕏̂ : Ω → X` 形は Phase 3.5 に残置
- `condDistrib` から離散 PMF への翻訳補題は「`diracPMF Q xh : FiniteJointPMF X X` を構成 → Phase 1 の `fano_core` を呼ぶ」で 7 行 (`pointwise_fano`) に圧縮できた。最大リスクは杞憂
- 自前定義 5 種 (`condEntropy` / `errorProb` / `pointwiseErrorProb` / `diracPMF` / `pointwise_fano`) 計 ~150 行
- 撤退ラインはどれも発動せず
