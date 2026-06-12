# 多変量 differential entropy + subadditivity 在庫調査

> **調査対象**: `h(Yⁿ) ≤ ∑ᵢ h(Yᵢ)` (多変量差分エントロピーの劣加法性 / 出力エントロピー subadditivity) を genuine 化する設計と実現可能性。
>
> **消費者 (撤退ライン発動元)**:
> - `docs/shannon/parallel-gaussian-chain-rule-plan.md` §撤退ライン **D-1** (`IsParallelGaussianMISuperadditive` honest 仮定化 / Risk #1「subadditivity が Mathlib にない」)
> - `InformationTheory/Shannon/ParallelGaussianPerCoord.lean:173` `IsParallelGaussianPerCoordRegularity.max_ent` (現状 honest 仮定で D-1 を pass-through)
> - 親: `docs/shannon/parallel-gaussian-moonshot-plan.md` §撤退ライン **L-PG1**、`docs/shannon/awgn-moonshot-plan.md` §撤退ライン F-2/F-3
>
> **既存資産の発見点**: `InformationTheory/Shannon/MutualInfo.lean` / `MIChainRule.lean` (測度 RV 版 `mutualInfo` + KL product 加法 `klDiv_pi_eq_sum`) と `ContChannelMIDecomp.lean` (MI→差分エントロピー bridge) が **subadditivity の核となる素材を既に持っている**。

## 一行サマリ

**実現可能性 = CONDITIONAL (YES with honest 仮定)。** subadditivity の数学的核 `KL(joint ‖ ∏marginals) ≥ 0` は**100% 既存**（`klDiv` が `ℝ≥0∞` 値で非負自明 + `klDiv_pi_eq_sum` 既存）。律速は **(1) 多変量 `differentialEntropy` 自体が不在**（1-D `Measure ℝ → ℝ` 専用）、**(2) `KL ↔ -∫f log f` の bridge が `Measure (ℝ × ℝ)` 上では `prod_withDensity` で閉じるが `Measure (Fin n → ℝ)` 上では `pi_withDensity` 不在で塞がる**こと。**自作必要 = 4 件 (多変量 def 1 + bridge 2 + subadd 主定理 1)、推定 ~250-400 行**。**撤退ライン D-1 は「2 変数形なら発動回避見込み / n 変数形なら発動 (honest 仮定温存)」**。

---

## 主定理の最終形（消費者から再掲 + 推奨 statement）

消費者 (`ParallelGaussianPerCoord.lean:173`) が最終的に必要とするのは：

```lean
-- IsParallelGaussianPerCoordRegularity.max_ent の核 (現状 honest 仮定):
(mutualInfoOfChannel p (parallelGaussianChannel N …)).toReal ≤ ∑ i, (1/2)·log(1 + P'ᵢ/Nᵢ)
```

これを genuine 化する経路 (chain-rule-plan §Approach 核心):

```
I(Xⁿ;Yⁿ) = h(Yⁿ) − h(Yⁿ|Xⁿ)                                  -- ContChannelMIDecomp bridge の多変量版
  h(Yⁿ|Xⁿ) = ∑ᵢ h(Yᵢ|Xᵢ)   ← memoryless ⇒ 出力 fibre 独立 (Measure.pi)、条件付き加法
  h(Yⁿ)    ≤ ∑ᵢ h(Yᵢ)       ← ★本調査の標的: 出力エントロピー subadditivity
⇒ I(Xⁿ;Yⁿ) ≤ ∑ᵢ h(Yᵢ) − ∑ᵢ h(Yᵢ|Xᵢ) = ∑ᵢ I(Xᵢ;Yᵢ)
```

本調査が genuine 化を判定する標的補題 (推奨 statement, **Mathlib-shape-driven**):

```lean
-- ★ 推奨 (KL 形を主軸、消費者の calc に直接乗る):
theorem differentialEntropy_le_sum  -- 2 変数版が最短
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    (h_int : …) :  -- honest integrability bundle
    jointDifferentialEntropy μ
      ≤ differentialEntropy (μ.map Prod.fst) + differentialEntropy (μ.map Prod.snd)
```

証明戦略 (pseudo-Lean):

```lean
-- subadditivity ⟺ total correlation ≥ 0:
-- h(X) + h(Y) − h(X,Y) = klDiv μ (μ_X.prod μ_Y) ≥ 0   (mutualInfo!)
have h_mi_nn : 0 ≤ (mutualInfo' …).toReal := ENNReal.toReal_nonneg   -- 既存・自明
-- bridge: (mutualInfo μ id id).toReal = h(μ_X) + h(μ_Y) − h_joint(μ)
have h_bridge : (mutualInfo …).toReal
    = differentialEntropy (μ.map .fst) + differentialEntropy (μ.map .snd)
        − jointDifferentialEntropy μ := …   -- ★自作 bridge (prod_withDensity + Fubini)
linarith [h_mi_nn, h_bridge]
```

---

## API 在庫テーブル

### A. 既存差分エントロピー (project, 1-D `Measure ℝ` 専用)

| 概念 | API (file:line) | signature `[...]` verbatim | 結論 verbatim | 状態 |
|---|---|---|---|---|
| 1-D 差分エントロピー | `InformationTheory.Shannon.differentialEntropy` `InformationTheory/Shannon/DifferentialEntropy.lean:42` | `(μ : Measure ℝ) : ℝ` | `:= ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume` | ✅ 既存。**1-D 専用 (codomain `Measure ℝ`)** |
| density 直書き形 | `differentialEntropy_eq_integral_density` `DifferentialEntropy.lean:60` | `{f : ℝ → ℝ} (hf : Measurable f) (hf_nn : ∀ x, 0 ≤ f x) (μ : Measure ℝ) (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x)))` | `differentialEntropy μ = -∫ x, f x * Real.log (f x) ∂volume` | ✅ 既存。bridge の出口形 |
| withDensity 形 | `differentialEntropy_eq_integral_withDensity` `DifferentialEntropy.lean:47` | `{f : ℝ → ℝ≥0∞} (hf : Measurable f)` | `differentialEntropy (volume.withDensity f) = ∫ x, Real.negMulLog (f x).toReal ∂volume` | ✅ 既存 |
| Gaussian 値 | `differentialEntropy_gaussianReal` `DifferentialEntropy.lean:406` | `(m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)` | `differentialEntropy (gaussianReal m v) = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)` | ✅ 既存。per-coord 値 |
| max-entropy (1-D) | `differentialEntropy_le_gaussian_of_variance_le` `DifferentialEntropy.lean:510` | `{μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : μ ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (h_mean : ∫ x, x ∂μ = m) (h_var : ∫ x, (x - m)^2 ∂μ ≤ (v : ℝ)) (h_var_int : Integrable (fun x => (x - m)^2) μ) (h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume)` | `differentialEntropy μ ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)` | ✅ 既存 (honest 2 integrability)。per-coord 上界 |
| **多変量 `differentialEntropy`** (`Measure (Fin n → ℝ)` / `Measure (ℝ × ℝ)` / `EuclideanSpace`) | — | — | — | ❌ **不在 (project / Mathlib 双方)**。`rg differentialEntropy.*(Fin n\|EuclideanSpace\|prod\|ℝ × ℝ)` → 0 hit |
| **条件付き差分エントロピー** `h(Y\|X)` | — | — | — | ❌ 不在。ただし `ContChannelMIDecomp` の `∫ x, h(W x) ∂p` 形で代替済 (下記 C) |

> **重要 (Mathlib-shape-driven 判断)**: 1-D `differentialEntropy` は `rnDeriv vs volume` 形。多変量版は **`volume : Measure (ℝ × ℝ)` = `volume.prod volume` (rfl, `volume_eq_prod`)** に対する `rnDeriv` 形にすれば、既存の 1-D 補題群と `prod_withDensity` がそのまま噛む。

### B. 多変量測度の Lebesgue 密度 / volume / 積構造

| 概念 | API (file:line) | signature `[...]` verbatim | 結論 verbatim | 状態 / subadd での扱い |
|---|---|---|---|---|
| `volume (ℝ×ℝ) = prod` | `MeasureTheory.volume_eq_prod` `Mathlib/MeasureTheory/Measure/Prod.lean:177` | `(α β) [MeasureSpace α] [MeasureSpace β]` | `(volume : Measure (α × β)) = (volume : Measure α).prod (volume : Measure β)` (**`:= rfl`**) | ✅ 既存・`rfl`。**2 変数 bridge の鍵** |
| product withDensity | `MeasureTheory.prod_withDensity` `Mathlib/MeasureTheory/Measure/WithDensity.lean:712` | `{f : α → ℝ≥0∞} {g : β → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)` | `(μ.withDensity f).prod (ν.withDensity g) = (μ.prod ν).withDensity (fun z ↦ f z.1 * g z.2)` | ✅ 既存。**joint density = ∏ marginal density の橋**。2 変数 bridge が閉じる |
| (AEMeasurable 版) | `prod_withDensity₀` `WithDensity.lean:705` | `(hf : AEMeasurable f μ) (hg : AEMeasurable g ν)` | 同上 | ✅ |
| product absolutelyContinuous | `MeasureTheory.Measure.AbsolutelyContinuous.prod` `Mathlib/MeasureTheory/Measure/Prod.lean` | (μ₁ ≪ μ₂) (ν₁ ≪ ν₂) → prod ≪ prod | — | ✅ 既存。`μ ≪ vol` 伝播 |
| Fubini (積分) | `MeasureTheory.integral_prod` `Mathlib/MeasureTheory/Integral/Prod.lean:494` | `(f : α × β → E) (hf : Integrable f (μ.prod ν))` | `∫ z, f z ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ` | ✅ 既存。bridge の積分分解 |
| **`pi_withDensity`** (`Measure.pi` 版) | — | — | — | ❌ **不在** (loogle `Found 0`)。**n 変数 bridge が塞がる最大 gap** |
| **`rnDeriv` of `prod` / `pi`** | — | — | — | ❌ **不在** (loogle `Found 0`)。bridge は `prod_withDensity` 経由で迂回必須 (rnDeriv 直接補題なし) |
| pi の prod 分解 (induction 素材) | `MeasureTheory.measurePreserving_piFinSuccAbove` `Mathlib/MeasureTheory/Constructions/Pi.lean` | — | `Measure.pi μs` を `μ_last × Measure.pi prefix` に分解 | ✅ 既存。`klDiv_pi_eq_sum` の induction で実証済 (D 参照) |

### C. KL / mutualInfo (subadditivity の数学的核 — 既存)

| 概念 | API (file:line) | signature `[...]` verbatim | 結論 verbatim | 状態 |
|---|---|---|---|---|
| KL (素材) | `InformationTheory.klDiv` `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57` | `(μ ν : Measure α) : ℝ≥0∞` | — | ✅ 既存。**`ℝ≥0∞` 値 ⇒ 非負自明** |
| KL = 0 ⟺ 等値 | `InformationTheory.klDiv_eq_zero_iff` `KullbackLeibler/Basic.lean:377` | `[IsFiniteMeasure μ] [IsFiniteMeasure ν]` | `klDiv μ ν = 0 ↔ μ = ν` | ✅ 既存。**等号 (独立 ⇒ subadd の等号) 用** |
| KL chain rule | `InformationTheory.klDiv_compProd_eq_add` `KullbackLeibler/ChainRule.lean:204` | `(μ ν κ η)` (kernel compProd 形、**型クラス前提なし**) | `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` | ✅ 既存 |
| KL prod 加法 (左) | `InformationTheory.klDiv_compProd_left` `ChainRule.lean:182` (`@[simp]`) | `(μ ν κ)` | `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν` | ✅ 既存 |
| **KL prod 加法** | `InformationTheory.Shannon.klDiv_prod_eq_add` (project) `InformationTheory/Shannon/MIChainRule.lean:254` | `{α' β'} [MeasurableSpace α'] [MeasurableSpace β'] (μ₁ μ₂ : Measure α') [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (ν₁ ν₂ : Measure β') [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]` | `klDiv (μ₁.prod ν₁) (μ₂.prod ν₂) = klDiv μ₁ μ₂ + klDiv ν₁ ν₂` | ✅ **project 既存** |
| **KL pi 加法** | `InformationTheory.Shannon.klDiv_pi_eq_sum` `MIChainRule.lean:273` | `{n : ℕ} {α' : Fin n → Type*} [∀ i, MeasurableSpace (α' i)] (μs νs : ∀ i, Measure (α' i)) [∀ i, IsProbabilityMeasure (μs i)] [∀ i, IsProbabilityMeasure (νs i)]` | `klDiv (Measure.pi μs) (Measure.pi νs) = ∑ i : Fin n, klDiv (μs i) (νs i)` | ✅ **project 既存。n 変数 total-correlation の核** |
| mutualInfo (RV 版) | `InformationTheory.Shannon.mutualInfo` `InformationTheory/Shannon/MutualInfo.lean:36` | `(μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞` | `:= klDiv (μ.map (fun ω => (Xs ω, Yo ω))) ((μ.map Xs).prod (μ.map Yo))` | ✅ 既存。**joint vs ∏marginal = total correlation** |
| mutualInfo 非負 | `mutualInfo_nonneg` `MutualInfo.lean:42` | `(μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y)` | `0 ≤ mutualInfo μ Xs Yo := bot_le` | ✅ 既存・自明 |
| mutualInfo pi 加法 | `mutualInfo_pi_eq_sum` `MIChainRule.lean:341` | `{n} (μ) [IsProbabilityMeasure μ] (Xs Ys : Fin n → Ω → _) (hXs hYs : ∀ i, Measurable _) + 3 i.i.d. factorization 仮定` | `mutualInfo μ (fun ω i => Xs i ω) (fun ω i => Ys i ω) = ∑ i, mutualInfo μ (Xs i) (Ys i)` | ✅ 既存。**product 入力での `=` (achiever 側)** |

### D. KL ↔ differentialEntropy bridge (subadd の翻訳 — 部分既存)

| 概念 | API (file:line) | signature `[...]` verbatim (抜粋) | 結論 verbatim | 状態 |
|---|---|---|---|---|
| **MI → 差分エントロピー差** (1-D channel bridge、**手本**) | `InformationTheory.Shannon.mutualInfoOfChannel_toReal_eq_diffEntropy_sub` `InformationTheory/Shannon/ContChannelMIDecomp.lean:223` | `(hW_ac : ∀ x, W x ≪ volume) (hq_ac : outputDistribution p W ≪ volume) (h_joint_ac : (p ⊗ₘ W) ≪ p.prod (outputDistribution p W)) (h_llr_split : … =ᵐ[p ⊗ₘ W] …) (h_int_fibre_joint : Integrable …) (h_int_out_joint : Integrable …) (h_int_out_marg : Integrable …)` | `(mutualInfoOfChannel p W).toReal = differentialEntropy (outputDistribution p W) − (∫ x, differentialEntropy (W x) ∂p)` | ✅ 既存。**bridge の構造手本 (honest 4-5 仮定込み)**。subadd 用 bridge はこれの「両座標差分エントロピー」版 |
| KL → llr 積分 | `InformationTheory.toReal_klDiv_of_measure_eq` `KullbackLeibler/Basic.lean:164` | `(h : μ ≪ ν) (h_eq : μ univ = ν univ)` | `(klDiv μ ν).toReal = ∫ x, llr μ ν x ∂μ` | ✅ 既存。bridge step 1 |
| rnDeriv chain rule | `MeasureTheory.Measure.rnDeriv_mul_rnDeriv` `Decomposition/RadonNikodym.lean` | `(hμν : μ ≪ ν)` | `μ.rnDeriv ν * ν.rnDeriv volume =ᵐ[volume] μ.rnDeriv volume` | ✅ 既存。density split に使用 (1-D maxent で実証済) |
| `negMulLog` 凹性 | `Real.concaveOn_negMulLog` `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:227` | — | `ConcaveOn ℝ (Set.Ici 0) negMulLog` | ✅ 既存。代替経路 (条件付き Jensen) 用 |
| **subadd 主 bridge** (joint h ↔ KL) | — | — | — | ❌ **自作必要**。`(mutualInfo μ id id).toReal = h(μ_X)+h(μ_Y)−h_joint(μ)`。手本 D-上を「両側差分エントロピー」に変形 |

---

## 主要前提条件ボックス (前提事故が起きやすい lemma)

- **`prod_withDensity` (`WithDensity.lean:712`)** — 前提: `Measurable f`, `Measurable g` (各座標 marginal density が可測)。**`[SigmaFinite ν]` が `Measure.prod` 自体に潜伏** (Fubini/prod の標準前提)。`volume : Measure ℝ` は σ-finite なので OK だが、joint bridge で `μ.map .fst` / `μ.map .snd` を `withDensity` 形に書き換える際の density 可測性 (= honest 仮定) が必要。
- **`klDiv_prod_eq_add` (`MIChainRule.lean:254`)** — 前提: 4 measure すべて **`[IsProbabilityMeasure]`**。subadd の marginal はすべて確率測度なので充足、ただし `[IsFiniteMeasure]` でなく `[IsProbabilityMeasure]` 縛りに注意 (有限測度版は別途 `klDiv_eq_zero_iff` の `[IsFiniteMeasure]` と整合)。
- **`klDiv_pi_eq_sum` (`MIChainRule.lean:273`)** — 前提: `[∀ i, IsProbabilityMeasure (μs i)]` と `[∀ i, IsProbabilityMeasure (νs i)]` の **両方**。n 変数 subadd で joint の各 marginal が確率測度であることを `Measure.isProbabilityMeasure_map` で供給する必要 (1-D で実証済の pattern)。
- **`mutualInfoOfChannel_toReal_eq_diffEntropy_sub` (`ContChannelMIDecomp.lean:223`)** — **honest 仮定 4-5 本** (`h_llr_split` Bayes density split + 3 integrability + 2 absolute continuity)。subadd bridge も**同型の honest bundle が必須** (multivariate density の `=ᵐ` split + integrability)。これが genuine 化の plumbing コストの本体。
- **`differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:510`)** — honest 2 integrability (`h_var_int`, `h_ent_int`)。per-coord max-entropy で必須、Gaussian で充足 (chain-rule-plan §honest 仮定 で AWGN #5 と共有)。
- **`volume_eq_prod` (`Prod.lean:177`)** は `rfl` だが、**`Measure.pi (fun _ : Fin n => (volume : Measure ℝ))` = `(volume : Measure (Fin n → ℝ))` は別の補題** (`MeasureTheory.volume_pi` / `Measure.pi`)。n 変数では `volume_pi` + `pi_pi` 経由で、2 変数より plumbing が一段重い。

---

## 自作が必要な要素 (優先度順)

1. **多変量 `jointDifferentialEntropy` の定義** (最優先, ~15-30 行)
   - **推奨実装** (Mathlib-shape-driven): `Measure (ℝ × ℝ)` (2 変数) 版を `noncomputable def jointDifferentialEntropy (μ : Measure (ℝ × ℝ)) : ℝ := ∫ z, Real.negMulLog ((μ.rnDeriv volume z).toReal) ∂volume` とする。**1-D `differentialEntropy` と完全同型**で `volume = volume.prod volume` (rfl) なので既存補題が噛む。
   - n 変数版は `Measure (Fin n → ℝ)` で同形だが、bridge で `pi_withDensity` 不在の壁 (下記 4)。
   - **落とし穴**: `EuclideanSpace ℝ (Fin n)` を codomain に選ぶと `volume` が `EuclideanSpace.volume` (内積空間 Haar) になり `Measure.pi` 系補題から乖離。**`Fin n → ℝ` を選ぶこと** (Mathlib の product Lebesgue は `Fin n → ℝ` 形に整備)。

2. **subadd 主 bridge: `(total correlation).toReal = ∑h(marginal) − h(joint)`** (~80-150 行)
   - **推奨**: `ContChannelMIDecomp.lean:223` の手本を「両座標が観測変数」形に転写。2 変数版なら `prod_withDensity` + `volume_eq_prod` (rfl) + `integral_prod` (Fubini) で density factorization が閉じる。
   - honest 仮定 bundle (density `=ᵐ` split + integrability) は手本と同型、**新規の数学的 gap はなし** (plumbing のみ)。
   - **落とし穴**: `llr` の Bayes split (`h_llr_split` 相当) は joint rnDeriv vs ∏marginal rnDeriv の `=ᵐ` を要求。`prod_withDensity` で density 形に持ち込めば `rnDeriv_withDensity` で書き換え可能だが、`μ ≪ vol` + 各 marginal `≪ vol` の伝播が必要。

3. **subadd 主定理 `differentialEntropy_le_sum`** (~20-40 行)
   - **推奨**: bridge (#2) + `mutualInfo_nonneg` (= `ENNReal.toReal_nonneg`) を `linarith` で結ぶだけ。数学的山場は #2 に吸収済。
   - n 変数版は `klDiv_pi_eq_sum` + 多変量 bridge (#4) で `∑ h(Yᵢ) − h(Yⁿ) = (total correlation).toReal ≥ 0`。

4. **(n 変数のみ) `pi_withDensity` の自作 or 迂回** (~50-100 行, **最大リスク**)
   - **Mathlib 不在** (loogle `Found 0`)。`(Measure.pi (fun i => μᵢ.withDensity fᵢ)) = (Measure.pi μᵢ).withDensity (fun x => ∏ i, fᵢ (x i))` を `measurePreserving_piFinSuccAbove` induction + `prod_withDensity` で自作。
   - **迂回案**: n 変数 subadd を 2 変数 subadd の induction で組む (`h(Y₁..Yₙ) ≤ h(Y₁..Yₙ₋₁) + h(Yₙ)` を `klDiv_prod_eq_add` の measurableEquiv reshape で)。これなら #4 を回避できる可能性。**Phase 0 で要判定**。

工数感:
- **2 変数 genuine** (#1+#2+#3): ~120-220 行。1-D maxent bridge (実証済) と同型なので中央 ~170 行。
- **n 変数 genuine** (+#4): +50-100 行 ⇒ ~250-400 行。chain-rule-plan の「subadditivity ~150-250 行」予測と整合 (やや上振れ、bridge の honest plumbing 込みで)。
- chain-rule-plan Risk #1 の「KL ≥ 0 (joint vs product) 経路で自作」は **本調査で経路確定: `mutualInfo_nonneg` + 自作 bridge**。

---

## 撤退ラインへの距離

親計画 `parallel-gaussian-chain-rule-plan.md` §撤退ライン **D-1** + `ParallelGaussianPerCoord.lean:173` `max_ent`:

> [D-1] ステップ1 (MI 優加法性 ≤) が rabbit hole (>250 行) → `IsParallelGaussianMISuperadditive` honest 仮定化、ステップ2-4 を genuine に閉じる。

判定:

- **2 変数 (`Measure (ℝ × ℝ)`) 限定なら D-1 発動回避見込み (CONDITIONAL-YES)。** `volume_eq_prod` (rfl) + `prod_withDensity` + `integral_prod` で bridge が閉じ、`mutualInfo_nonneg` で subadd が出る。~170 行 < 250 行の D-1 閾値。**ただし honest 仮定 (density split + integrability) は残る** (1-D maxent と同性質、新規でない)。
- **n 変数 (`Measure (Fin n → ℝ)`, 消費者が実際に要求する形) は D-1 発動リスク高。** `pi_withDensity` 不在 (#4) が >250 行 rabbit hole 化の主因。迂回 (2 変数 induction) が効けば回避、効かなければ D-1 発動。

**新規撤退ライン提案 (本調査が D-1 を細分化)**:

- **[D-1a] 2 変数 subadd は genuine、n 変数を 2 変数 induction に帰着できない (`pi_withDensity` 自作が >100 行)** → n 変数 subadd を honest 仮定 `differentialEntropy_le_sum_pi` (statement のみ、証明 `pass-through`) に温存し、**2 変数 genuine + n 変数 statement-level** で publish。`max_ent` の honest 仮定を「n 変数 subadd 1 本」に**縮約** (現状の MI 優加法性まるごと仮定より前進)。
- **[D-1b] 2 変数 bridge の honest density split (`h_llr_split` 相当) が Gaussian でも閉じない** → bridge を honest 仮定形 (`ContChannelMIDecomp.lean:223` と同型 signature) で温存。subadd の**構造 (KL ≥ 0 から)** は genuine、density 翻訳のみ仮定。
- **いずれも `sorry` を残さない** (CLAUDE.md 撤退ライン規約)。

**最大 gap**: `pi_withDensity` (n 変数の joint density = ∏ marginal density) が Mathlib 不在。2 変数 `prod_withDensity` は存在するので、**消費者が n 変数を要求 vs 2 変数 induction で足りるか**が genuine/honest の分水嶺。

---

## 着手 skeleton

`InformationTheory/Shannon/MultivariateDiffEntropy.lean` (新規) の出だし:

```lean
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.MIChainRule

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-- 2 変数 joint 差分エントロピー (1-D `differentialEntropy` と同型、`volume (ℝ×ℝ) = volume.prod volume` rfl)。 -/
noncomputable def jointDifferentialEntropy (μ : Measure (ℝ × ℝ)) : ℝ :=
  ∫ z, Real.negMulLog ((μ.rnDeriv volume z).toReal) ∂volume

/-- subadd 主 bridge: total correlation = ∑h(marginal) − h(joint)。
honest 仮定 bundle は `ContChannelMIDecomp.mutualInfoOfChannel_toReal_eq_diffEntropy_sub` と同型。 -/
theorem totalCorrelation_toReal_eq_sum_sub_joint
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    (h_fst_ac : μ.map Prod.fst ≪ volume) (h_snd_ac : μ.map Prod.snd ≪ volume)
    -- honest: density split (=ᵐ) + integrability bundle (手本 :223 と同型)
    (h_density_split : True)  -- ★ skeleton placeholder; 実形は手本 h_llr_split を転写
    (h_int : True) :          -- ★ skeleton placeholder
    (klDiv μ ((μ.map Prod.fst).prod (μ.map Prod.snd))).toReal
      = differentialEntropy (μ.map Prod.fst) + differentialEntropy (μ.map Prod.snd)
        - jointDifferentialEntropy μ := by
  sorry

/-- ★ 標的: 2 変数差分エントロピー subadditivity `h(X,Y) ≤ h(X) + h(Y)`。
bridge + `ENNReal.toReal_nonneg` (KL ≥ 0) の `linarith`。 -/
theorem jointDifferentialEntropy_le_sum
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    (h_fst_ac : μ.map Prod.fst ≪ volume) (h_snd_ac : μ.map Prod.snd ≪ volume)
    (h_density_split : True) (h_int : True) :
    jointDifferentialEntropy μ
      ≤ differentialEntropy (μ.map Prod.fst) + differentialEntropy (μ.map Prod.snd) := by
  have h_nn : (0 : ℝ) ≤ (klDiv μ ((μ.map Prod.fst).prod (μ.map Prod.snd))).toReal :=
    ENNReal.toReal_nonneg
  have h_bridge := totalCorrelation_toReal_eq_sum_sub_joint hμ h_fst_ac h_snd_ac h_density_split h_int
  linarith [h_nn, h_bridge]

end InformationTheory.Shannon
```

n 変数版 (`Measure (Fin n → ℝ)`, 消費者要求形) は同 file に `jointDifferentialEntropyPi` + `klDiv_pi_eq_sum` 経由で追加。`pi_withDensity` 不在の壁 (#4) は Phase 0 で 2 変数 induction 帰着可否を判定。

---

## まとめ (判定)

- **実現可能性: CONDITIONAL (YES with honest 仮定)**
- **推奨定義**: `jointDifferentialEntropy (μ : Measure (ℝ × ℝ)) := ∫ z, negMulLog ((μ.rnDeriv volume z).toReal) ∂volume` (1-D と同型、`volume_eq_prod` rfl で既存補題が噛む)。codomain は **`Fin n → ℝ` (not `EuclideanSpace`)**。
- **subadditivity 最短経路**: (A) `klDiv(joint ‖ ∏marginals) ≥ 0` (= `mutualInfo_nonneg`, 既存・自明) + 自作 bridge (`prod_withDensity` + `volume_eq_prod` + Fubini) で `∑h − h_joint = KL ≥ 0`。**(B) chain rule 経路より素材完備**。
- **推定行数**: 2 変数 genuine ~120-220 行 (中央 ~170)、n 変数 +50-100 行 (`pi_withDensity` 自作込み ~250-400)。
- **必要 honest 仮定**: density `=ᵐ` split + integrability bundle (`ContChannelMIDecomp.lean:223` 手本と同型、新規でない / AWGN #5 と共有見込み) + 各 marginal `≪ volume`。
- **最大 gap**: **`pi_withDensity` が Mathlib 不在** (`prod_withDensity` は存在)。n 変数 joint density = ∏ marginal density の橋がないため、n 変数を 2 変数 induction に帰着できるかが genuine/honest の分水嶺。**撤退ライン D-1 は 2 変数なら回避見込み、n 変数なら発動リスク高 (新規 D-1a/D-1b 提案)**。

---

## 2026-05-29 再調査 — n 変数 closure ゲート

> **調査目的**: `jointDifferentialEntropyPi_le_sum` (n 変数 subadditivity, `MultivariateDiffEntropy.lean:257`) + その bridge `klDiv_pi_marginals_toReal_eq_sum_sub_joint` (L242) — 現状 sorry-routed (`@residual(plan:multivariate-diffentropy-subadditivity-plan)`) — が closeable か、generic `withDensity_map` 自作 1 件で genuine 化できるか、を loogle で authoritative に再判定する。
>
> **前回 (Wave 3) の停止点**: 案 A (2 変数 induction via `MeasurableEquiv.piFinSuccAbove`) を ~250 行試行 → reshape 各 step で **generic `withDensity_map`** (`(μ.withDensity g).map e = (μ.map e).withDensity (g ∘ e.symm)`) を要求、これが Mathlib 不在で停止。plan は「`Measure.ext` + `MeasurableEquiv.lintegral_map` で ~10 行自作可能」と評価。本調査はこの自作可否を verbatim 確認した。

### 一行サマリ

**closeable = (b) generic `withDensity_map` は Mathlib 不在だが自作 ~10-20 行で genuine 可能。** 5 つの命名候補 (`Measure.map_withDensity` / `MeasurableEquiv.map_withDensity` / `withDensity_map` / `MeasurableEmbedding.withDensity_map` / `MeasurableEmbedding.map_withDensity`) は**全て `unknown identifier` = 不在**。ただし rnDeriv 特化版 `MeasurableEmbedding.map_withDensity_rnDeriv` (`RadonNikodym.lean:537`) が **generic 版とほぼ同型の 5 行証明** (`ext` + `hf.map_apply` + `withDensity_apply` + `setLIntegral_map`) を持ち、これを density 一般 (rnDeriv でない) に脱特化すれば generic `withDensity_map` の自作テンプレートになる。自作部品 (`Measure.ext` / `lintegral_map` / `setLIntegral_map` / `withDensity_apply` / `MeasurableEquiv.map_apply`) は全て verbatim 存在。reshape 部品 (`measurePreserving_piFinSuccAbove` 等) も全て存在。**残り規模見積**: helper ~15-25 行 + 案 A induction 本体 ~120-200 行 = **closure 全体 ~150-250 行**。代替路 (rnDeriv-of-product 直接) は **`rnDeriv_prod` / `rnDeriv_pi` 双方 Mathlib 不在** (`Found 0`) のため案 A より重い (rnDeriv の積分解自体を自作することになる)。

### 主定理の最終形 (再掲)

```lean
-- MultivariateDiffEntropy.lean:257 (sorry-routed)
theorem jointDifferentialEntropyPi_le_sum
    {n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (μ.map (fun z => z i))]
    (_h_marg_ac : ∀ i, (μ.map (fun z => z i)) ≪ volume)
    (_hμ_ac : μ ≪ (volume : Measure (Fin n → ℝ)))
    (_h_joint_ac : μ ≪ Measure.pi (fun i => μ.map (fun z => z i))) :
    jointDifferentialEntropyPi μ ≤ ∑ i, differentialEntropy (μ.map (fun z => z i))
```

closure 戦略 (案 A, pseudo-Lean):

```lean
-- 自作 helper (generic withDensity_map, ~15-25 行, rnDeriv 版を脱特化):
theorem withDensity_map_equiv (e : α ≃ᵐ β) {g : α → ℝ≥0∞} (hg : Measurable g) :
    (μ.withDensity g).map e = (μ.map e).withDensity (g ∘ e.symm) := by
  ext s hs
  rw [e.map_apply, withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
      setLIntegral_map hs (hg.comp e.symm.measurable) e.measurable]
  -- ∫⁻ in e⁻¹'s, g ∂μ = ∫⁻ in e⁻¹'s, (g∘e.symm)(e ·) ∂μ  (e.symm ∘ e = id)
  exact setLIntegral_congr_fun ... (by simp [Function.comp, e.symm_apply_apply])
-- 案 A induction: Fin (n+1) → ℝ ≃ᵐ ℝ × (Fin n → ℝ) を piFinSuccAbove で reshape、
-- 2 変数 _v2 (genuine 完成済) + 帰納仮定で h(Y₁..Yₙ₊₁) ≤ h(Y₁) + h(Y₂..Yₙ₊₁) を組む。
```

### API 在庫テーブル

#### 1. generic `withDensity_map` 系 (最重要)

| 命名候補 | loogle 結果 | file:line | 状態 / 扱い |
|---|---|---|---|
| `MeasureTheory.Measure.map_withDensity` | `unknown identifier` | — | ❌ 不在 |
| `MeasurableEquiv.map_withDensity` | `unknown identifier` | — | ❌ 不在 |
| `MeasureTheory.withDensity_map` | `unknown identifier` | — | ❌ 不在 |
| `MeasurableEmbedding.withDensity_map` | `unknown identifier` | — | ❌ 不在 |
| `MeasurableEmbedding.map_withDensity` | `unknown identifier` | — | ❌ 不在 |
| 結論パターン `Measure.map (Measure.withDensity _ _) _` | **`Found 0`** (0 match) | — | ❌ **generic 版 authoritative 不在確認** |
| 結論パターン `Measure.withDensity (Measure.map _ _) _` | `Found 11`, **1 match** | — | rnDeriv 版のみ (下記) |
| **rnDeriv 特化版** `MeasurableEmbedding.map_withDensity_rnDeriv` | `Found 1` | `Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean:537` | ✅ **存在 (脱特化テンプレート)** |

`map_withDensity_rnDeriv` verbatim (`RadonNikodym.lean:537`):

```lean
lemma _root_.MeasurableEmbedding.map_withDensity_rnDeriv (hf : MeasurableEmbedding f)
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    (ν.withDensity (μ.rnDeriv ν)).map f = (ν.map f).withDensity ((μ.map f).rnDeriv (ν.map f))
```

証明 body verbatim (`RadonNikodym.lean:540-544`, **5 行**):

```lean
  ext s hs
  rw [hf.map_apply, withDensity_apply _ (hf.measurable hs), withDensity_apply _ hs,
    setLIntegral_map hs (Measure.measurable_rnDeriv _ _) hf.measurable]
  refine setLIntegral_congr_fun_ae (hf.measurable hs) ?_
  filter_upwards [hf.rnDeriv_map μ ν] with a ha _ using ha.symm
```

> **判定**: generic `withDensity_map` 自体は不在 (5 命名候補 + 結論パターン全て negative)。だが rnDeriv 版の証明骨格 (`ext` → `map_apply` → `withDensity_apply` ×2 → `setLIntegral_map` → `setLIntegral_congr`) は **density を rnDeriv に固定していない** — 最後の `hf.rnDeriv_map` step (rnDeriv が map と可換) のみ rnDeriv 特化。generic 版では density `g` が任意なので、`setLIntegral_map` 後の被積分 `g (e.symm (e x))` を `e.symm_apply_apply` で `g x` に潰すだけ (rnDeriv_map より易しい)。**自作は rnDeriv 版より短くなる見込み**。`MeasurableEquiv` は `MeasurableEmbedding` (`f.measurableEmbedding`) なので前提も充足。

#### 2. 自作経路の部品 (全て verbatim 存在)

| 概念 | API (file:line) | signature `[...]` verbatim | 結論 verbatim | 状態 |
|---|---|---|---|---|
| 測度の外延性 | `MeasureTheory.Measure.ext` `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:143` | `(h : ∀ s, MeasurableSet s → μ₁ s = μ₂ s)` | `μ₁ = μ₂` | ✅ |
| lintegral of map | `MeasureTheory.lintegral_map` `Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean:27` | `{f : β → ℝ≥0∞} {g : α → β} (hf : Measurable f) (hg : Measurable g)` | `∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ` | ✅ (`MeasurableEquiv.lintegral_map` は不在だが本 generic 版で代用) |
| set-lintegral of map | `MeasureTheory.setLIntegral_map` `Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean:67` | `{f : β → ℝ≥0∞} {g : α → β} {s : Set β} (hs : MeasurableSet s) (hf : Measurable f) (hg : Measurable g)` | `∫⁻ y in s, f y ∂map g μ = ∫⁻ x in g ⁻¹' s, f (g x) ∂μ` | ✅ **rnDeriv 版が実際に使う step** |
| withDensity の集合測度 | `MeasureTheory.withDensity_apply` `Mathlib/MeasureTheory/Measure/WithDensity.lean:45` | `(f : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s)` | `μ.withDensity f s = ∫⁻ a in s, f a ∂μ` | ✅ |
| map of MeasurableEquiv | `MeasureTheory.Measure.map_apply` (MeasurableEquiv) `Mathlib/MeasureTheory/Measure/Map.lean:302` | `(f : α ≃ᵐ β) (s : Set β)` | `μ.map f s = μ (f ⁻¹' s)` (`protected`) | ✅ (`:= f.measurableEmbedding.map_apply _ _`) |
| map of Measurable (一般) | `MeasureTheory.Measure.map_apply` `Mathlib/MeasureTheory/Measure/Map.lean:160` | `(hf : Measurable f) {s : Set β} (hs : MeasurableSet s)` | `μ.map f s = μ (f ⁻¹' s)` | ✅ |
| lintegral_withDensity (mul 形) | `MeasureTheory.lintegral_withDensity_eq_lintegral_mul` `Mathlib/MeasureTheory/Measure/WithDensity.lean:386` | `(μ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)` (本文 hg 可測性付き) | `∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ` | ✅ (本経路では不要だが density 積分表現として在庫) |

**自作スケッチ (紙)**: `(μ.withDensity g).map e = (μ.map e).withDensity (g ∘ e.symm)`。`ext s hs` → LHS `= (μ.withDensity g) (e⁻¹'s)` (`MeasurableEquiv.map_apply` :302) `= ∫⁻ in e⁻¹'s, g ∂μ` (`withDensity_apply` :45)。RHS `= ∫⁻ in s, (g∘e.symm) ∂(μ.map e)` (`withDensity_apply` :45) `= ∫⁻ in e⁻¹'s, (g∘e.symm)(e x) ∂μ` (`setLIntegral_map` :67)。被積分 `(g∘e.symm)(e x) = g (e.symm (e x)) = g x` (`e.symm_apply_apply`)。両辺一致。**~15-25 行**。rnDeriv 版 (`:540-544`) は最後の congr が rnDeriv_map 経由で 1 step 重いだけ、generic 版はそれが `simp [e.symm_apply_apply]` で潰れる分むしろ短い。

#### 3. `pi_withDensity` 直接版 (再確認 — 不在維持)

| 命名候補 | loogle 結果 | 状態 |
|---|---|---|
| `MeasureTheory.Measure.pi_withDensity` | `unknown identifier` | ❌ 不在 (前回 `Found 0` 再確認) |
| `MeasureTheory.withDensity_pi` | `unknown identifier` | ❌ 不在 |
| `MeasureTheory.Measure.withDensity_pi` | (上と同 namespace) | ❌ 不在 |

> 案 B (`pi_withDensity` 直接自作) は依然不在。前回判断ログの通り案 B も内部で generic `withDensity_map` を要求するため、**自作すべきは generic `withDensity_map` 1 本** (案 A のため)。`pi_withDensity` 全体を自作する必要はない。

#### 4. rnDeriv-of-product 系 (代替路 — 不在で却下)

| 命名候補 | loogle 結果 | 状態 / 扱い |
|---|---|---|
| `MeasureTheory.Measure.rnDeriv_prod` | `unknown identifier` | ❌ 不在 |
| `MeasureTheory.Measure.rnDeriv_pi` | `unknown identifier` | ❌ 不在 |
| 結論パターン `Measure.rnDeriv (Measure.prod _ _) _` | **`Found 0`** | ❌ **rnDeriv-of-product authoritative 不在** |

> **代替路は案 A より重い**。bridge を density split 経由でなく rnDeriv-of-product 直接で組む路は、`rnDeriv (μ.prod ν)` / `rnDeriv (Measure.pi μs)` の積分解補題が双方不在のため、それ自体を自作することになる (rnDeriv は `prod_withDensity` のように直接の積公式を持たない)。案 A の generic `withDensity_map` 1 本より部品が多く却下。

#### 5. reshape 部品 (全て verbatim 存在)

| 概念 | API (file:line) | signature `[...]` verbatim | 結論 verbatim | 状態 |
|---|---|---|---|---|
| Fin(n+1) → ℝ ≃ᵐ reshape | `MeasurableEquiv.piFinSuccAbove` `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:560` | `{n : ℕ} (α : Fin (n + 1) → Type*) [∀ i, MeasurableSpace (α i)] (i : Fin (n + 1))` | `(∀ j, α j) ≃ᵐ α i × ∀ j, α (i.succAbove j)` | ✅ |
| 測度保存 (reshape) | `MeasureTheory.measurePreserving_piFinSuccAbove` `Mathlib/MeasureTheory/Constructions/Pi.lean:802` | `{n : ℕ} {α : Fin (n + 1) → Type u} {m : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (i : Fin (n + 1))` | `MeasurePreserving (MeasurableEquiv.piFinSuccAbove α i) (Measure.pi μ) ((μ i).prod <| Measure.pi fun j => μ (i.succAbove j))` | ✅ **一般測度版** (volume 限定でない) |
| volume 版 | `MeasureTheory.volume_preserving_piFinSuccAbove` `Constructions/Pi.lean:814` | `{n : ℕ} (α : Fin (n + 1) → Type u) [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))] (i : Fin (n + 1))` | `MeasurePreserving (MeasurableEquiv.piFinSuccAbove α i)` | ✅ |
| Unique reshape | `MeasurableEquiv.funUnique` `MeasurableSpace/Embedding.lean:541` | `(α β : Type*) [Unique α] [MeasurableSpace β]` | `(α → β) ≃ᵐ β` | ✅ (base case `n=1`) |
| Unique 測度保存 | `MeasureTheory.measurePreserving_funUnique` `Constructions/Pi.lean:836` | `{β : Type u} {_m : MeasurableSpace β} (μ : Measure β) (α : Type v) [Unique α]` | `MeasurePreserving (MeasurableEquiv.funUnique α β) (Measure.pi fun _ : α => μ) μ` | ✅ |

#### 6. 既消費部品 (2 変数 `_v2` genuine 完成済が使用 — verbatim 再確認)

| 概念 | API (file:line) | signature `[...]` verbatim | 結論 verbatim | 状態 |
|---|---|---|---|---|
| product withDensity (AEMeasurable) | `MeasureTheory.prod_withDensity₀` `Mathlib/MeasureTheory/Measure/WithDensity.lean:705` | `{f : α → ℝ≥0∞} {g : β → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g ν)` | `(μ.withDensity f).prod (ν.withDensity g) = (μ.prod ν).withDensity (fun z ↦ f z.1 * g z.2)` | ✅ |
| product withDensity (Measurable) | `MeasureTheory.prod_withDensity` `WithDensity.lean:712` | `{f : α → ℝ≥0∞} {g : β → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)` | 同上 | ✅ |
| withDensity rnDeriv 復元 | `MeasureTheory.Measure.withDensity_rnDeriv_eq` `Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean:60` | `(μ ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν)` | `ν.withDensity (μ.rnDeriv ν) = μ` (本文形) | ✅ |
| rnDeriv chain | `MeasureTheory.Measure.rnDeriv_mul_rnDeriv` `RadonNikodym.lean:402` | `{κ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ] (hμν : μ ≪ ν)` | `μ.rnDeriv ν * ν.rnDeriv κ =ᵐ[κ] μ.rnDeriv κ` | ✅ |
| volume (ℝ×ℝ) = prod | `MeasureTheory.volume_eq_prod` `Mathlib/MeasureTheory/Measure/Prod.lean:177` | `(α β) [MeasureSpace α] [MeasureSpace β]` | `(volume : Measure (α × β)) = (volume : Measure α).prod (volume : Measure β)` (`:= rfl`) | ✅ |
| volume (Fin n → ℝ) = pi | `MeasureTheory.volume_pi` `Mathlib/MeasureTheory/Constructions/Pi.lean` (`[∀ i, MeasureSpace (α i)]`) | `[∀ i, MeasureSpace (α i)]` | `(volume : Measure (∀ i, α i)) = Measure.pi fun i => volume` | ✅ |

### 主要前提条件ボックス

- **自作 `withDensity_map` helper の前提**: density `g` の `Measurable g` (rnDeriv 版は `Measure.measurable_rnDeriv` で自動充足、generic 版では明示前提)。`MeasurableEquiv` を使う限り `MeasurableEmbedding` (`e.measurableEmbedding`) + `e.measurable` / `e.symm.measurable` は自動。**`SigmaFinite` は generic density 版では不要** (rnDeriv 版が `[SigmaFinite μ] [SigmaFinite ν]` を要求するのは `rnDeriv_map` step のため、generic 版はその step を `symm_apply_apply` で回避するので落とせる見込み — 着手時要確認)。
- **`measurePreserving_piFinSuccAbove` (`Pi.lean:802`)**: `[∀ i, SigmaFinite (μ i)]` を要求。案 A induction で各 marginal `μ.map (· i)` は `IsProbabilityMeasure` (供給済 instance) ⇒ `SigmaFinite` 自動。**ただし `Measure.pi` を `(μ i).prod (Measure.pi rest)` に分解した後、`klDiv_prod_eq_add` (`MIChainRule.lean:254`) は 4 measure 全て `[IsProbabilityMeasure]` を要求** — reshape 後の `Measure.pi rest` が `IsProbabilityMeasure` であることを `MeasureTheory.isProbabilityMeasure_pi` 等で供給する必要 (前回 plan §落とし穴で言及済、`Measure.isProbabilityMeasure_map` pattern で derive)。
- **2 変数 `_v2` 既存資産は genuine 完成** (`prod_marginals_eq_volume_withDensity` / `llr_split_from_density_factorize` / `jointDifferentialEntropy_le_sum_v2`, L285+)。案 A induction の内側 (2 変数 step) はこれを `Fin n → ℝ` carrier 側に適用するだけ — **新規 honest 仮定なし、helper 1 本のみが残 gap**。

### 自作が必要な要素 (優先度順)

1. **generic `withDensity_map` helper** (~15-25 行, **唯一の真の gap**)
   - 推奨実装: `MeasurableEmbedding.map_withDensity_rnDeriv` (`RadonNikodym.lean:537`) の 5 行証明を density 一般に脱特化。最後の `hf.rnDeriv_map` step を `setLIntegral_congr_fun` + `simp [Function.comp, e.symm_apply_apply]` に置換。
   - signature 候補: `theorem withDensity_map_equiv (e : α ≃ᵐ β) {g : α → ℝ≥0∞} (hg : Measurable g) : (μ.withDensity g).map e = (μ.map e).withDensity (g ∘ e.symm)`。
   - 落とし穴: `g ∘ e.symm` の可測性 (`hg.comp e.symm.measurable`) を `setLIntegral_map` に渡す。被積分の `e.symm (e x)` 簡約は `MeasurableEquiv.symm_apply_apply` (defeq でない場合 `simp` 必要)。

2. **案 A induction 本体** `jointDifferentialEntropyPi_le_sum_v2` (~120-200 行)
   - base `n=0/1`: `funUnique` reshape で 1-D `differentialEntropy` に帰着 (subadditivity 自明 / 等号)。
   - step `n → n+1`: `piFinSuccAbove 0` で `Fin (n+1) → ℝ ≃ᵐ ℝ × (Fin n → ℝ)`、helper #1 で joint density を reshape、2 変数 `_v2` (genuine) を外側に + 帰納仮定を内側 (`Fin n → ℝ`) に適用。
   - bridge `klDiv_pi_marginals_toReal_eq_sum_sub_joint` も同 reshape で discharge (`klDiv_pi_eq_sum` 既存 + helper)。

工数感: helper #1 ~15-25 行 + induction #2 ~120-200 行 = **closure 全体 ~150-250 行**。前回 plan の「Phase 2 案 A ~50-100 行」見積りは helper を ~10 行と過小評価していた節があるが、reshape 配線 (instance 供給 + measurability) 込みで ~150-250 行が現実的。

### Mathlib 壁の列挙 (`@residual(wall:...)` 対象)

- **generic `withDensity_map`** — `Found 0` (結論パターン `Measure.map (Measure.withDensity _ _) _`) + 5 命名候補 `unknown identifier`。**ただし真の Mathlib 壁ではなく「Mathlib に lemma 名が無いだけ」= 自作 ~15-25 行で genuine 化可能な選択 (big) 案件**。`wall:` ではなく `plan:` 分類が正しい (現状の `@residual(plan:multivariate-diffentropy-subadditivity-plan)` は分類正確)。shared sorry 補題化は不要 (本 family 1 file 内 helper で足りる)。
- **`pi_withDensity` / `withDensity_pi`** — `unknown identifier` (不在維持)。だが案 A 経路では `withDensity_map` helper があれば不要なので壁として残す必要なし。
- **`rnDeriv_prod` / `rnDeriv_pi`** — `unknown identifier` + 結論パターン `Found 0`。代替路用だが案 A 採用なら不要。

> **結論**: 真の `@residual(wall:...)` 対象は **ゼロ**。現状の sorry は全て plan-closeable (helper 自作 1 本で道が開く)。`@residual(plan:...)` 分類は honest。

### 撤退ラインへの距離

親 plan `docs/shannon/multivariate-diffentropy-subadditivity-plan.md` の撤退ライン:

> 「**Phase 2 案 A / 案 B 双方で行き詰まる (>250 行) → n 変数のみ honest hyp 温存**」(plan L307)

判定:

- **撤退ライン発動: NO (close 再開推奨)。** 前回 Wave 3 の停止理由「generic `withDensity_map` が Mathlib 不在」は事実だが、**自作不能ではなく自作未着手**。rnDeriv 版 (`:537`) という 5 行のテンプレートが存在し、自作部品 (`ext` / `map_apply` / `withDensity_apply` / `setLIntegral_map`) は全て verbatim 在庫。前回 plan 自身が「`Measure.ext` + `lintegral_map` で ~10 行自作可能」と評価していた通り。
- **closure 全体見積 ~150-250 行** は撤退ライン閾値 (>250 行) の境界内〜やや下。helper #1 (~20 行) が取れれば induction 本体は 2 変数 `_v2` の機械的 lift なので 250 行は超えない見込み。
- **新規撤退ライン (本調査の細分)**: [G-1] helper #1 自作で `e.symm (e x)` 簡約 or `g ∘ e.symm` 可測性配線が予想外に重く >50 行化 → helper を共有 sorry 補題 (`withDensity_map_equiv := by sorry` + `@residual(wall:withdensity-map-equiv)`) に切り出し、induction 本体だけ genuine 化。これでも現状 (全 sorry) より前進。撤退口は sorry + `@residual`、仮説束化は禁止。

### 着手 skeleton

```lean
-- InformationTheory/Shannon/MultivariateDiffEntropy.lean (既存 file 拡張)
-- 既存 imports (L1-11) に追加不要 (Map / WithDensity / Pi / RadonNikodym 既存)

namespace InformationTheory.Shannon
open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-- **generic `withDensity_map` (Mathlib 不在、rnDeriv 版 `RadonNikodym.lean:537` を脱特化)。**
pushforward of a `withDensity` measure along a measurable equivalence. -/
theorem withDensity_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} (e : α ≃ᵐ β) {g : α → ℝ≥0∞} (hg : Measurable g) :
    (μ.withDensity g).map e = (μ.map e).withDensity (g ∘ e.symm) := by
  sorry  -- @residual(plan:multivariate-diffentropy-subadditivity-plan)
         -- ext + e.map_apply + withDensity_apply ×2 + setLIntegral_map + symm_apply_apply

/-- **n 変数 subadditivity (genuine successor, 案 A induction).** -/
theorem jointDifferentialEntropyPi_le_sum_v2
    {n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (μ.map (fun z => z i))]
    (h_marg_ac : ∀ i, (μ.map (fun z => z i)) ≪ volume)
    (hμ_ac : μ ≪ (volume : Measure (Fin n → ℝ)))
    (h_joint_ac : μ ≪ Measure.pi (fun i => μ.map (fun z => z i))) :
    jointDifferentialEntropyPi μ ≤ ∑ i, differentialEntropy (μ.map (fun z => z i)) := by
  sorry  -- @residual(plan:multivariate-diffentropy-subadditivity-plan)
         -- piFinSuccAbove reshape + withDensity_map_equiv + 2 変数 _v2 + 帰納仮定

end InformationTheory.Shannon
```

### ゲート判定

- **closeable = (b)**: generic `withDensity_map` は **Mathlib 不在** (5 命名候補 `unknown identifier` + 結論パターン `Found 0`) だが、**自作 ~15-25 行で genuine 可能**。rnDeriv 特化版 `MeasurableEmbedding.map_withDensity_rnDeriv` (`RadonNikodym.lean:537`) の 5 行証明が脱特化テンプレートで、自作部品 (`Measure.ext` :143 / `lintegral_map` :27 / `setLIntegral_map` :67 / `withDensity_apply` :45 / `MeasurableEquiv.map_apply` :302) は全て verbatim 在庫。reshape 部品 (`piFinSuccAbove` :560 / `measurePreserving_piFinSuccAbove` :802 / `funUnique` :541) も全存在。
- **規模見積**: helper #1 ~15-25 行 + 案 A induction 本体 ~120-200 行 = **closure 全体 ~150-250 行** (撤退ライン >250 行の境界内)。2 変数 `_v2` が genuine 完成済なので induction 内側は機械的 lift。
- **代替路 (rnDeriv-of-product 直接) は案 A より重い**: `rnDeriv_prod` / `rnDeriv_pi` 双方 `unknown identifier` + 結論パターン `Found 0`、rnDeriv の積分解補題自体を自作する羽目になり却下。
- **撤退ライン発動: NO** — 前回 Wave 3 は「自作未着手」を「Mathlib 不在で停止」と扱っていた。helper 1 本の自作で再開可能、`@residual(wall:...)` 対象はゼロ、現状の `@residual(plan:...)` 分類は honest。
