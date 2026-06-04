# EPI G2 bridge 補題 `differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv` Mathlib API 在庫

> 対象 bridge: `InformationTheory/Shannon/EPIG2ConvEntropyMonotone.lean:149-156`
> (`@residual(wall:cond-diff-entropy)`)。これを genuine 化すると
> `condDifferentialEntropy_le` (同 file:179) が全 genuine 化し、EPI G2 一般形サンドイッチ
> Phase 1 (β) 下界が完成する。
>
> 親計画: `docs/shannon/` の EPI G2 general-sandwich plan / handoff。撤退ライン参照は §7。

## 1. 一行サマリ

bridge を 3 sub-gap に分解した結果、**(c) Fubini + marginal 同定は API 100% 既存 (buildable)**、
**(b) per-fibre 密度展開は素材 90% 既存 (差は in-tree 既存 lemma 接続のみ、buildable)**、
**(a) 条件付き KL 積分形は真の Mathlib 壁 (`ChainRule.lean:74-77` 明示 TODO、loogle `klDiv ∩ Kernel` = compProd 2 件のみ、整合 `∫ z klDiv` 形 Found 0)**。
**山は (a) 1 本。自作 ~120-200 行、独立 reusable file 化可能** (sub-gap (a) は EPI 文脈に依存しない純 KL 補題)。
全体 closure 見込み = 1 自作 lemma (a) を closed すれば (b)(c) は既存 API plumbing で連結、bridge は **buildable**。

## 2. 主定理の最終形 (再掲)

```lean
theorem differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) (hX_ac : (μ.map X) ≪ volume) :
    differentialEntropy (μ.map X) - condDifferentialEntropy X Z μ
      = (klDiv ((μ.map Z) ⊗ₘ condDistrib X Z μ)
          ((μ.map Z) ⊗ₘ Kernel.const α (μ.map X))).toReal := by
  sorry
```

証明戦略 (pseudo-Lean):

```
-- 記号: μZ := μ.map Z,  μX := μ.map X,  κ := condDistrib X Z μ : Kernel α ℝ,  η := Kernel.const α μX
-- 1. [sub-gap a] 条件付き KL 積分形 (自作):
--    (klDiv (μZ ⊗ₘ κ) (μZ ⊗ₘ η)).toReal = ∫ z, (klDiv (κ z) μX).toReal ∂μZ
--    (両辺 first marginal が μZ で共通 → klDiv_compProd_eq_add の left項 = klDiv μZ μZ = 0、
--     残る klDiv (μZ⊗κ)(μZ⊗η) は整合化されないので、ChainRule.lean:64-71 計算を
--     ∫∫ log llr → Fubini で z-外積分に開く)
-- 2. [sub-gap b] per-fibre 密度展開 (既存接続):
--    (klDiv (κ z) μX).toReal = ∫ llr (κ z) μX ∂(κ z)   (toReal_klDiv_of_measure_eq, prob measure 同質量)
--      = -differentialEntropy (κ z) - ∫ p_z(x)·log q_X(x) dx   (llr = log(p_z/q_X), 密度展開)
-- 3. [sub-gap c] Fubini + marginal 同定 (既存):
--    ∫ z, [-h(κ z)] ∂μZ = -condDifferentialEntropy X Z μ        (条件付きエントロピー定義そのもの)
--    ∫ z, [-∫ p_z log q_X] ∂μZ = -∫ q_X log q_X = differentialEntropy μX
--      (Measure.integral_compProd で z-積分を内側へ、condDistrib_comp_map で X-marginal = μX)
-- ⇒ h(μX) - condDiffEnt = ∫ z (klDiv (κ z) μX).toReal ∂μZ = (klDiv joint product).toReal
```

---

## 3. API 在庫テーブル

### 群 A — 条件付き KL 積分形 (sub-gap a、最重要、真壁)

| 概念 | Mathlib API | file:line | 状態 | bridge での扱い |
|---|---|---|---|---|
| chain rule (compProd 形) | `theorem klDiv_compProd_eq_add` | `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:204` | ✅ 既存 | **本件では効かない** (下記) |
| chain rule (left 共通) | `lemma klDiv_compProd_left` `[simp]` | `ChainRule.lean:182` | ✅ 既存 | 第一周辺が共通のとき collapse、本件 first marginal = μZ 共通 → `klDiv μZ μZ = 0` |
| **条件付き KL 積分形** `∫ z, klDiv (κ z) (η z) ∂μ` | — | — | ❌ **不在 (明示 TODO)** | **自作必須。bridge の唯一の真壁** |
| (素材) compProd 積分 Fubini | `lemma Measure.integral_compProd` | `Mathlib/Probability/Kernel/Composition/IntegralCompProd.lean:473` | ✅ 既存 | 自作 (a) の核: ∫∫ llr を z-外積分へ |
| (素材) rnDeriv 連鎖 | `lemma ProbabilityTheory.rnDeriv_compProd` | `Mathlib/Probability/Kernel/Composition/RadonNikodym.lean:107` | ✅ 既存 | rnDeriv の点別積分解 |
| (素材) toReal klDiv 積分形 | `lemma toReal_klDiv_of_measure_eq` | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:164` | ✅ 既存 | 同質量 (Markov) のとき `(klDiv).toReal = ∫ llr ∂μ` (積分可能性不要) |

#### 群 A 候補の verbatim signature

`klDiv_compProd_eq_add` (`ChainRule.lean:200-204`):
```
variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {μ ν : Measure 𝓧} {κ η : Kernel 𝓧 𝓨}
  [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η]
theorem klDiv_compProd_eq_add :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)
```
**分解の向き**: 第一周辺 `μ` vs `ν` を `klDiv μ ν` に切り出し、残りを `klDiv (μ⊗κ)(μ⊗η)` (両者第一周辺
共通) に残す。本件は `μ = ν = μZ` (両辺 first marginal 同一) ゆえ `klDiv μZ μZ = 0` (`klDiv_self`,
Basic.lean:78) に collapse し、`klDiv (μZ⊗κ)(μZ⊗η)` がそのまま残る = **何も分解されない**。
→ chain rule は本件に対し恒等変形 `0 + KL` を返すだけで、`∫ z` 形を一切供給しない。

`klDiv_compProd_left` (`ChainRule.lean:180-182`):
```
variable (μ ν κ) in
@[simp] lemma klDiv_compProd_left : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν
```
(第二カーネル `κ` 共通のとき → 第一周辺の KL に collapse。本件は第二カーネルが `κ` vs `const μX` で
**異なる**ので適用不可。)

`Measure.integral_compProd` (`IntegralCompProd.lean:473-476`):
```
variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {κ : Kernel α β}
lemma integral_compProd [SFinite μ] [IsSFiniteKernel κ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α × β → E} (hf : Integrable f (μ ⊗ₘ κ)) :
    ∫ x, f x ∂(μ ⊗ₘ κ) = ∫ a, ∫ b, f (a, b) ∂(κ a) ∂μ
```
前提: `[SFinite μ]`, `[IsSFiniteKernel κ]`, `Integrable f (μ ⊗ₘ κ)`。

`rnDeriv_compProd` (`RadonNikodym.lean:107-110`):
```
variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {κ η : Kernel α β}
lemma rnDeriv_compProd [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) (ν : Measure α) [IsFiniteMeasure ν] :
    (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η]
      (fun p ↦ μ.rnDeriv ν p.1 * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p)
```

`toReal_klDiv_of_measure_eq` (`Basic.lean:162-165`):
```
variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}
  [IsFiniteMeasure μ] [IsFiniteMeasure ν]
lemma toReal_klDiv_of_measure_eq (h : μ ≪ ν) (h_eq : μ univ = ν univ) :
    (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ
```

**所見 (群 A)**: sub-gap (a) は **真壁**。`ChainRule.lean:74-77` に verbatim TODO:
> "Add a version of the chain rule for the integral form of the contional KL divergence, i.e.
> `μ[fun x ↦ klDiv (κ x) (η x)]`."
loogle backstop: `klDiv ∩ Kernel` → Found 2 (= `klDiv_compProd_eq_add` / `klDiv_compProd_left`
のみ)。`klDiv ∩ integral` → Found 6 (全て measure 2 引数の純 KL toReal 系、`∫ z, klDiv (κ z) _`
形は皆無)。整合 `∫ z, klDiv (κ z) (η z) ∂μ = (klDiv (μ⊗κ)(μ⊗η)).toReal` 形は **Found 0**。
→ **自作必須**。ただし素材 (`integral_compProd` / `rnDeriv_compProd` / `toReal_klDiv_of_measure_eq` /
`ChainRule.lean:64-71` の既存計算パターン) は全て揃っており、ChainRule.lean の `klDiv_compProd_eq_add`
の内部証明 (`integral_compProd` で `∫ llr ∂(μ⊗κ)` を `∫∫ llr ∂κ ∂μ` に開く 232-178 行) を
**measurability 制約付き積分形へ転写**すれば組める。自作 **~120-180 行** (measurability of
`z ↦ klDiv (κ z) (η z)` の処理が TODO で避けられた箇所そのものなので、ここに ~40-60 行)。
**Mathlib upstream PR 候補** (ChainRule.lean の明示 TODO の充足、EPI 文脈非依存)。

### 群 B — klDiv の density / llr 表現 (sub-gap b)

| 概念 | Mathlib API | file:line | 状態 | bridge での扱い |
|---|---|---|---|---|
| toReal klDiv = ∫ llr (積分可能性付) | `lemma toReal_klDiv` | `Basic.lean:157` | ✅ 既存 | `(klDiv μ ν).toReal = ∫ llr ∂μ + ν.real univ − μ.real univ` |
| toReal klDiv = ∫ llr (同質量, 可積分性不要) | `lemma toReal_klDiv_of_measure_eq` | `Basic.lean:164` | ✅ 既存 | **第一候補**: κ z, μX 共に prob measure → univ 項相殺、`= ∫ llr (κ z) μX ∂(κ z)` |
| llr 定義 | `def llr (μ ν : Measure α) (x : α) : ℝ := log (μ.rnDeriv ν x).toReal` | `Mathlib/MeasureTheory/Measure/LogLikelihoodRatio.lean:37` | ✅ 既存 | `llr (κ z) μX x = log (p_z(x)/q_X(x))` (rnDeriv 比) |
| llr_def (関数形) | `lemma llr_def : llr μ ν = fun x ↦ log (μ.rnDeriv ν x).toReal` | `LogLikelihoodRatio.lean:39` | ✅ 既存 | 書換 |
| differentialEntropy 定義 | `def differentialEntropy (μ : Measure ℝ) : ℝ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume` | `InformationTheory/Shannon/DifferentialEntropy.lean:45` | ✅ in-tree | `-h(κ z) = ∫ p_z log p_z` |
| h = ∫ withDensity 形 | `theorem differentialEntropy_eq_integral_withDensity` | `DifferentialEntropy.lean:51` | ✅ in-tree | density 直書きへ橋渡し |
| h = −∫ f log f 形 | `theorem differentialEntropy_eq_integral_density` | `DifferentialEntropy.lean:65` | ✅ in-tree | **第一候補**: `differentialEntropy μ = -∫ f·log f ∂volume` |
| klFun 定義 | `def klFun (x : ℝ) : ℝ := x * log x + 1 - x` | `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean:53` | ✅ 既存 | f-divergence 形 (backup 表現) |

#### 群 B 主要 verbatim signature

`differentialEntropy_eq_integral_density` (`DifferentialEntropy.lean:65-69`):
```
theorem differentialEntropy_eq_integral_density
    {f : ℝ → ℝ} (hf : Measurable f) (hf_nn : ∀ x, 0 ≤ f x)
    (μ : Measure ℝ)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    differentialEntropy μ = -∫ x, f x * Real.log (f x) ∂volume
```

`toReal_klDiv` (`Basic.lean:157-158`、前提が重要):
```
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
lemma toReal_klDiv (h : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ + ν.real univ - μ.real univ
```

**所見 (群 B)**: **素材 90% 既存、buildable**。`(klDiv (κ z) μX).toReal = ∫ llr (κ z) μX ∂(κ z)`
は `toReal_klDiv_of_measure_eq` が κ z, μX 共 prob measure (κ Markov, μX = μ.map X prob) で univ
項相殺するため **可積分性前提なしで** 取れる (これは大きい — chain rule では各 fibre の可積分性が
壁だったが、measure_eq 版で迂回可)。次に `∫ llr (κ z) μX ∂(κ z) = ∫ log(p_z/q_X) p_z dx
= ∫ p_z log p_z − ∫ p_z log q_X = −h(κ z) − ∫ p_z log q_X` の展開は: (i) `log(a/b) = log a − log b`
(rnDeriv の比、要 `q_X > 0` a.e. = `μX ≪ volume` + density 正値、`hX_ac` から)、(ii) 第一項を
`differentialEntropy_eq_integral_density` に接続。**自作 ~40-70 行**。落とし穴: rnDeriv `κ z` を
volume 基準 density `p_z` に書換える際 `κ z ≪ volume` a.e. `z` が要る (disintegration の絶対連続性、
群 C 参照) + `∫ p_z log q_X` の可積分性 (cross-entropy 項) は `klDiv (κ z) μX < ∞` a.e. から出すが、
ここは sub-gap (a) で a.e.-finite を確保している前提。Mathlib PR 候補ではない (in-tree
`differentialEntropy` 依存)。

### 群 C — Fubini + marginal 同定 (sub-gap c、buildable)

| 概念 | Mathlib API | file:line | 状態 | bridge での扱い |
|---|---|---|---|---|
| compProd 積分 Fubini | `lemma Measure.integral_compProd` | `IntegralCompProd.lean:473` | ✅ 既存 | `∫ f ∂(μZ⊗κ) = ∫ z ∫ x f ∂κz ∂μZ` (群 A 再掲) |
| **condDistrib X-marginal 同定** | `lemma ProbabilityTheory.condDistrib_comp_map` | `Mathlib/Probability/Kernel/CondDistrib.lean:86` | ✅ 既存 | **核心**: `condDistrib X Z μ ∘ₘ (μ.map Z) = μ.map X` |
| disintegration 等式 | `lemma ProbabilityTheory.compProd_map_condDistrib` | `CondDistrib.lean:82` | ✅ 既存 | `(μ.map Z) ⊗ₘ condDistrib X Z μ = μ.map (Z,X)` (joint 同定) |
| compProd const = prod | `lemma Measure.compProd_const` `[simp]` | `MeasureCompProd.lean:141` | ✅ 既存 | `μZ ⊗ₘ (Kernel.const α μX) = μZ.prod μX` (product 同定) |
| 第二 marginal = comp | `lemma Measure.snd_compProd` `[simp]` | `MeasureComp.lean:45` | ✅ 既存 | `(μZ ⊗ₘ κ).snd = κ ∘ₘ μZ` (∘ₘ への橋渡し) |

#### 群 C 主要 verbatim signature

`condDistrib_comp_map` (`CondDistrib.lean:54 variable block + 86-88`):
```
variable {α β Ω F : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [Nonempty Ω] {mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
  {X : α → β} {Y : α → Ω}  -- ↓ lemma 内で X Y は上記 variable
lemma condDistrib_comp_map (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    condDistrib Y X μ ∘ₘ (μ.map X) = μ.map Y
```
注意: Mathlib `condDistrib Y X μ : Kernel β Ω` は `Y` を出力 (codomain `Ω`)、`X` を条件 (codomain `β`)。
**bridge では `condDistrib X Z μ`** = (Mathlib の `Y := X : Ω→ℝ`, `X := Z : Ω→α`) なので
`condDistrib X Z μ ∘ₘ (μ.map Z) = μ.map X`。これが「z で κ の X-marginal を平均すると μX」
= sub-gap (c) の marginal 同定そのもの。

`compProd_map_condDistrib` (`CondDistrib.lean:82-83`):
```
lemma compProd_map_condDistrib (hY : AEMeasurable Y μ) :
    (μ.map X) ⊗ₘ condDistrib Y X μ = μ.map fun a ↦ (X a, Y a)
```
(bridge では joint = `(μ.map Z) ⊗ₘ condDistrib X Z μ = μ.map (Z,X)`、定義 docstring 済。)

`compProd_const` (`MeasureCompProd.lean:140-142`):
```
variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}
@[simp] lemma compProd_const {ν : Measure β} [SFinite μ] [SFinite ν] :
    μ ⊗ₘ (Kernel.const α ν) = μ.prod ν
```

**所見 (群 C)**: **API 100% 既存、buildable**。`∫ z (−h(κ z)) ∂μZ` は `condDifferentialEntropy`
定義 (EPIG2ConvEntropyMonotone.lean:104 `∫ z, differentialEntropy (κ z) ∂(μ.map Z)`) に rfl 一致。
`∫ z (−∫ p_z log q_X) ∂μZ = −∫ q_X log q_X` は: `Measure.integral_compProd` の逆向き
(z-積分を joint 積分へ) + `condDistrib_comp_map` で `κ ∘ₘ μZ = μX` から `∫ g d(κ∘ₘμZ) = ∫ g dμX`
(`Measure.integral_comp` 系または `∘ₘ = bind` の積分公式) を使い、`g := log q_X` 平均が
`∫ q_X log q_X dx = −h(μX)`。**自作 ~20-40 行** (ほぼ既存 lemma 接続)。落とし穴: `∫ g d(κ ∘ₘ μZ)`
を `∫ g dμX` に変える積分公式は `condDistrib_comp_map` で測度を一致させてから `congr`/書換、ただし
`∘ₘ` の積分は `Measure.integral_bind` 系を要確認 (本 inventory では未 verbatim、自作時に loogle
`MeasureTheory.integral, Measure.bind` で確認すること)。Mathlib PR 候補ではない。

---

## 4. 主要前提条件ボックス (前提事故が起きやすい箇所)

- **`condDistrib Y X μ` の StandardBorel 要求**: `CondDistrib.lean:54` の variable block で
  **出力空間 `Ω` に `[StandardBorelSpace Ω] [Nonempty Ω]`** を要求 (条件空間 `β` には不要)。
  bridge の `condDistrib X Z μ` は出力 = `ℝ` (X : Ω→ℝ) なので `[StandardBorelSpace ℝ]` =
  Mathlib instance で自動成立。`[Nonempty ℝ]` も自動。**条件空間 `α` (= Z の codomain) には
  StandardBorel 不要** → bridge signature の `[MeasurableSpace α]` のままで OK (追加制約なし)。
- **`klDiv_compProd_eq_add` / `klDiv_compProd_left`**: `[IsFiniteMeasure μ] [IsFiniteMeasure ν]
  [IsMarkovKernel κ] [IsMarkovKernel η]`。bridge では μZ = μ.map Z (prob, μ prob から),
  κ = condDistrib (Markov, instance CondDistrib.lean:68), η = Kernel.const μX (Markov 要 μX prob)。
  全て充足。ただし **本件では chain rule 自体が効かない** (群 A 所見)。
- **`Measure.integral_compProd`**: `[SFinite μ] [IsSFiniteKernel κ]` + `Integrable f (μ⊗ₘκ)`。
  prob measure は SFinite、Markov は SFinite kernel。**Integrable 前提**が落とし穴: 被積分
  `f = llr (μZ⊗κ)(μZ⊗η)` の joint 可積分性は `klDiv joint product < ∞` から (klDiv 有限 ⇔ ac ∧
  llr integrable, `klDiv_ne_top_iff` Basic.lean:100)。sub-gap (a) の前提として確保が必要。
- **`toReal_klDiv_of_measure_eq`**: `(h : μ ≪ ν) (h_eq : μ univ = ν univ)`。**可積分性前提なし**
  (これが chain rule 迂回の鍵)。κ z, μX 共 prob measure ゆえ `h_eq` 自明、`h : κ z ≪ μX` は
  disintegration の絶対連続性 a.e. `z` から (= `klDiv joint product < ∞` ⟹ a.e. `z` で ac、
  `Measure.absolutelyContinuous_compProd_iff` 系)。
- **`hX_ac : μ.map X ≪ volume`** (bridge precondition): 群 B で `q_X := dμX/dvolume` の density
  化と `log q_X` 定義に必須。**load-bearing ではなく regularity precondition** (audit 2026-06-04
  確認済、honest)。

---

## 5. 自作が必要な要素 (優先度順)

1. **[最優先・真壁] `klDiv_compProd_toReal_integral` (sub-gap a)** ~120-180 行
   - signature 案: `(klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal = ∫ z, (klDiv (κ z) (η z)).toReal ∂μ`
     (first marginal 共通 `μ` 版。`[IsFiniteMeasure μ] [IsMarkovKernel κ] [IsMarkovKernel η]` +
     ac/integrability 前提) — もしくは更に一般の `ν ⊗ₘ η` 版。
   - 推奨実装: ChainRule.lean:223-233 の `integral_compProd` で `∫ llr ∂(μ⊗κ)` を
     `∫ z ∫ x llr ∂κz ∂μ` に開く計算を、各 fibre の `toReal_klDiv_of_measure_eq` (= κz, ηz 同質量
     版) に接続。`z ↦ klDiv (κ z)(η z)` の可測性 (TODO が避けた箇所) は
     `Measurable.klDiv` 系が無ければ `aestronglyMeasurable_integral_condDistrib` 類推で自作。
   - 落とし穴: measurability of fibrewise klDiv (~40-60 行)、a.e. ac/integrable の伝播
     (`absolutelyContinuous_compProd_iff` / `integrable_llr_compProd_iff` ChainRule.lean:106 周辺)。
   - **独立 reusable file 化推奨** (`InformationTheory/KL/CompProdIntegral.lean` 等)。EPI 文脈に
     一切依存しない純 KL/Kernel 補題、Mathlib upstream PR 候補。

2. **[buildable] per-fibre 密度展開 (sub-gap b)** ~40-70 行
   - `(klDiv (κ z) μX).toReal = -differentialEntropy (κ z) - ∫ x, (p_z x)·log (q_X x) ∂volume`
     (a.e. `z`)。`toReal_klDiv_of_measure_eq` → llr 比展開 → `differentialEntropy_eq_integral_density`。
   - 落とし穴: `κ z ≪ volume` a.e. `z` (disintegration の絶対連続性、sub-gap a の ac から)、
     cross-entropy 項 `∫ p_z log q_X` の可積分性。

3. **[buildable] Fubini + marginal 同定 (sub-gap c)** ~20-40 行
   - `∫ z, [-∫ p_z log q_X] ∂μZ = differentialEntropy μX`、`∫ z [-h(κ z)] ∂μZ =
     condDifferentialEntropy X Z μ` (後者は def に rfl 近接)。`condDistrib_comp_map` +
     `Measure.integral_compProd` + `∘ₘ` 積分公式 (loogle 要確認)。

工数感: sub-gap (a) が全体の 60-70%。(a) を独立 file で closed すれば、(b)(c) + 連結で bridge 本体は
~80-120 行。**合計 ~200-320 行** (前 session inventory 見積 150-300 と整合、やや上振れ余地)。

---

## 6. Mathlib 壁の列挙 (`@residual(wall:...)` 対象)

- **`wall:cond-diff-entropy`** (= 既存 tag、bridge `EPIG2ConvEntropyMonotone.lean:148`):
  実体は **sub-gap (a) 条件付き KL 積分形の不在** に局在する。
  - loogle 確認: `InformationTheory.klDiv, ProbabilityTheory.Kernel` → **Found 2** (compProd 2 件のみ、
    積分形なし)。整合 `∫ z, klDiv (κ z) (η z) ∂μ = (klDiv (μ⊗κ)(μ⊗η)).toReal` 形 → **Found 0**。
  - verbatim TODO: `KullbackLeibler/ChainRule.lean:74-77`「Add a version of the chain rule for the
    integral form of the contional KL divergence, i.e. `μ[fun x ↦ klDiv (κ x) (η x)]`」。
  - **shared sorry 補題化推奨**: sub-gap (a) は EPI 文脈非依存の純 KL/Kernel 補題。`wall:` の
    nature が「EPI 固有」ではなく「Mathlib KL infra の穴」なので、独立 file の shared lemma に
    集約し、bridge はそれを呼ぶ形が望ましい (`docs/audit/audit-tags.md`「共有 Mathlib 壁」)。
    → 自作で **closed 可能な壁** (hard ではなく未整備 plumbing)。Mathlib PR で恒久 closure も視野。
  - sub-gap (b)(c) は **壁ではない** (既存 API + 自作 plumbing で buildable)。

---

## 7. 撤退ラインへの距離

bridge を closure する本タスクは **新規 sorry を増やさず既存 1 sorry を解消する方向** なので、撤退
ラインを発動させる方向には作用しない。むしろ closure 成功で (β) 下界が完成し撤退から遠ざかる。

- **発動しない** (closure に成功する限り)。
- 縮退案 (closure が当該セッションで無理な場合、新規撤退ラインとして提案):
  - **縮退 1**: sub-gap (a) のみ shared sorry 補題 `klDiv_compProd_toReal_integral` として切り出し
    `@residual(wall:cond-diff-entropy)` を付け、(b)(c) + 連結は genuine に組む。bridge は (a) の
    shared lemma を呼ぶ 1 sorry に縮退 (現状の bridge 全体 sorry より honest かつ closure 面積縮小)。
  - **縮退 2**: (a) を `[StandardBorelSpace]` 付き special case (κ, η が disintegration 由来) に
    限定した版で先に closure し、一般版は Mathlib PR 待ち。
  - いずれも撤退口は **sorry + `@residual`**、仮説束化は禁止 (bridge の hX_ac 等は regularity
    precondition のまま維持)。

---

## 8. 着手 skeleton (sub-gap a 独立 file 化想定)

```lean
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.RadonNikodym

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {μ : Measure 𝓧} {κ η : Kernel 𝓧 𝓨}
  [IsFiniteMeasure μ] [IsMarkovKernel κ] [IsMarkovKernel η]

/-- **Conditional KL divergence, integral form** (Mathlib `ChainRule.lean:74-77` TODO).
When the two joint measures share the first marginal `μ`, the `toReal` Kullback-Leibler
divergence decomposes as the `μ`-average of the fibrewise divergences:
`(klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal = ∫ z, (klDiv (κ z) (η z)).toReal ∂μ`.

Proof route: `klDiv_compProd_eq_add` collapses the first-marginal term to `klDiv μ μ = 0`,
then `Measure.integral_compProd` opens `∫ llr ∂(μ⊗ₘκ)` into the outer `z`-integral; each fibre
uses `toReal_klDiv_of_measure_eq` (Markov ⟹ equal mass ⟹ no integrability side-condition).
Fibrewise measurability of `z ↦ klDiv (κ z) (η z)` is the part the Mathlib TODO avoided.

@residual(wall:cond-diff-entropy) -/
theorem klDiv_compProd_toReal_integral
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η)
    (h_int : Integrable (llr (μ ⊗ₘ κ) (μ ⊗ₘ η)) (μ ⊗ₘ κ)) :
    (klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal = ∫ z, (klDiv (κ z) (η z)).toReal ∂μ := by
  sorry

end InformationTheory
```

(bridge 本体 `differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv` は
`EPIG2ConvEntropyMonotone.lean:149` のまま、上記 shared lemma + sub-gap (b)(c) plumbing で body
を埋める。)

---

## §結論: bridge 全体の closure 見込み

| sub-gap | 内容 | 判定 | 自作行数 | PR 候補 |
|---|---|---|---|---|
| (a) | 条件付き KL 積分形 `(klDiv (μ⊗κ)(μ⊗η)).toReal = ∫ z klDiv(κz)(ηz) ∂μ` | **真壁 (closable)** | ~120-180 | ✅ Mathlib PR (ChainRule TODO) |
| (b) | per-fibre 密度展開 `(klDiv (κz) μX).toReal = -h(κz) - ∫ p_z log q_X` | **buildable** (素材 90% 既存) | ~40-70 | ✗ (in-tree 依存) |
| (c) | Fubini + marginal 同定 (`condDistrib_comp_map` + `integral_compProd`) | **buildable** (API 100% 既存) | ~20-40 | ✗ |

**bridge 全体**: sub-gap (a) を closed すれば (b)(c) は既存 API 連結で組め、bridge は **buildable**
(真壁は (a) 1 本のみ)。最大の山 = **(a)**。

**自作必要要素 (優先度順)**:
1. `klDiv_compProd_toReal_integral` (sub-gap a、独立 reusable file、shared sorry 補題、~120-180 行)
2. per-fibre 密度展開 lemma (sub-gap b、~40-70 行)
3. Fubini/marginal 連結 (sub-gap c、~20-40 行) + bridge body 連結

**並列分割可能性**: ✅ **sub-gap (a) は独立 reusable file 化可能**
(`InformationTheory/KL/CompProdIntegral.lean` 等)。EPI 文脈・`differentialEntropy` に一切依存しない
純 KL/Kernel 補題なので、(a) を 1 agent、(b)+(c)+bridge body を別 agent に並列分割可。ただし (b)(c) は
(a) の結論を `sorry` placeholder として仮置きすれば独立に進められる (依存方向: bridge body → (a),
(b), (c); (a) ⊥ (b) ⊥ (c))。**(a) を先行 or 並列で closure → (b)(c) 連結が安全**。
