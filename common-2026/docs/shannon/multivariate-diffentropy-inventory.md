# 多変量 differential entropy + subadditivity 在庫調査

> **調査対象**: `h(Yⁿ) ≤ ∑ᵢ h(Yᵢ)` (多変量差分エントロピーの劣加法性 / 出力エントロピー subadditivity) を genuine 化する設計と実現可能性。
>
> **消費者 (撤退ライン発動元)**:
> - `docs/shannon/parallel-gaussian-chain-rule-plan.md` §撤退ライン **D-1** (`IsParallelGaussianMISuperadditive` honest 仮定化 / Risk #1「subadditivity が Mathlib にない」)
> - `Common2026/Shannon/ParallelGaussianPerCoord.lean:173` `IsParallelGaussianPerCoordRegularity.max_ent` (現状 honest 仮定で D-1 を pass-through)
> - 親: `docs/shannon/parallel-gaussian-moonshot-plan.md` §撤退ライン **L-PG1**、`docs/shannon/awgn-moonshot-plan.md` §撤退ライン F-2/F-3
>
> **既存資産の発見点**: `Common2026/Shannon/MutualInfo.lean` / `MIChainRule.lean` (測度 RV 版 `mutualInfo` + KL product 加法 `klDiv_pi_eq_sum`) と `ContChannelMIDecomp.lean` (MI→差分エントロピー bridge) が **subadditivity の核となる素材を既に持っている**。

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
| 1-D 差分エントロピー | `Common2026.Shannon.differentialEntropy` `Common2026/Shannon/DifferentialEntropy.lean:42` | `(μ : Measure ℝ) : ℝ` | `:= ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume` | ✅ 既存。**1-D 専用 (codomain `Measure ℝ`)** |
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
| **KL prod 加法** | `InformationTheory.Shannon.klDiv_prod_eq_add` (project) `Common2026/Shannon/MIChainRule.lean:254` | `{α' β'} [MeasurableSpace α'] [MeasurableSpace β'] (μ₁ μ₂ : Measure α') [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (ν₁ ν₂ : Measure β') [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]` | `klDiv (μ₁.prod ν₁) (μ₂.prod ν₂) = klDiv μ₁ μ₂ + klDiv ν₁ ν₂` | ✅ **project 既存** |
| **KL pi 加法** | `InformationTheory.Shannon.klDiv_pi_eq_sum` `MIChainRule.lean:273` | `{n : ℕ} {α' : Fin n → Type*} [∀ i, MeasurableSpace (α' i)] (μs νs : ∀ i, Measure (α' i)) [∀ i, IsProbabilityMeasure (μs i)] [∀ i, IsProbabilityMeasure (νs i)]` | `klDiv (Measure.pi μs) (Measure.pi νs) = ∑ i : Fin n, klDiv (μs i) (νs i)` | ✅ **project 既存。n 変数 total-correlation の核** |
| mutualInfo (RV 版) | `InformationTheory.Shannon.mutualInfo` `Common2026/Shannon/MutualInfo.lean:36` | `(μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞` | `:= klDiv (μ.map (fun ω => (Xs ω, Yo ω))) ((μ.map Xs).prod (μ.map Yo))` | ✅ 既存。**joint vs ∏marginal = total correlation** |
| mutualInfo 非負 | `mutualInfo_nonneg` `MutualInfo.lean:42` | `(μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y)` | `0 ≤ mutualInfo μ Xs Yo := bot_le` | ✅ 既存・自明 |
| mutualInfo pi 加法 | `mutualInfo_pi_eq_sum` `MIChainRule.lean:341` | `{n} (μ) [IsProbabilityMeasure μ] (Xs Ys : Fin n → Ω → _) (hXs hYs : ∀ i, Measurable _) + 3 i.i.d. factorization 仮定` | `mutualInfo μ (fun ω i => Xs i ω) (fun ω i => Ys i ω) = ∑ i, mutualInfo μ (Xs i) (Ys i)` | ✅ 既存。**product 入力での `=` (achiever 側)** |

### D. KL ↔ differentialEntropy bridge (subadd の翻訳 — 部分既存)

| 概念 | API (file:line) | signature `[...]` verbatim (抜粋) | 結論 verbatim | 状態 |
|---|---|---|---|---|
| **MI → 差分エントロピー差** (1-D channel bridge、**手本**) | `Common2026.Shannon.mutualInfoOfChannel_toReal_eq_diffEntropy_sub` `Common2026/Shannon/ContChannelMIDecomp.lean:223` | `(hW_ac : ∀ x, W x ≪ volume) (hq_ac : outputDistribution p W ≪ volume) (h_joint_ac : (p ⊗ₘ W) ≪ p.prod (outputDistribution p W)) (h_llr_split : … =ᵐ[p ⊗ₘ W] …) (h_int_fibre_joint : Integrable …) (h_int_out_joint : Integrable …) (h_int_out_marg : Integrable …)` | `(mutualInfoOfChannel p W).toReal = differentialEntropy (outputDistribution p W) − (∫ x, differentialEntropy (W x) ∂p)` | ✅ 既存。**bridge の構造手本 (honest 4-5 仮定込み)**。subadd 用 bridge はこれの「両座標差分エントロピー」版 |
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

`Common2026/Shannon/MultivariateDiffEntropy.lean` (新規) の出だし:

```lean
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Common2026.Shannon.DifferentialEntropy
import Common2026.Shannon.MutualInfo
import Common2026.Shannon.MIChainRule

namespace Common2026.Shannon

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

end Common2026.Shannon
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
