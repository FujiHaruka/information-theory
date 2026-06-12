# Rate-distortion 関数の凸性 — Mathlib / プロジェクト API 在庫調査

> 対象 sorry: `rateDistortionFunction_convexOn`
> (`InformationTheory/Shannon/RateDistortion/Convexity.lean:161`)。
> 親計画: [`docs/shannon/rate-distortion-convexity-plan.md`](rate-distortion-convexity-plan.md)。
> **本ファイルは在庫調査のみ**。route 推奨は書かない (pivot-advisor / orchestrator が判断)。

## 一行サマリ

**核心 (`klDiv` の joint convexity = Cover-Thomas 2.7.2) は Mathlib に直接不在 (loogle Found 0 × 4)。** ただし周辺の道具 (klFun 凸性, klDiv↔lintegral 橋, 条件付き Jensen, `prod_add`/`prod_smul_*`, 既存 `klDiv_map_le`, 既存 finite log-sum) はほぼ全て揃っている。「Phase B で使う primitive のうち実体 ~90% 既存・自作が必要なのは joint convexity 1 本 (DPI 経路なら 3-4 補題 / pmf 経路なら 4-5 補題)」。**最大の落とし穴: `klDiv_smul_same` は同一スカラー `klDiv (c•μ)(c•ν)=c·klDiv μ ν` のみ。混合 `λν₁+(1-λ)ν₂` の和には全く効かない (混同しやすい)。**

---

## 主定理の最終形 (再掲, code verbatim)

`InformationTheory/Shannon/RateDistortion/Convexity.lean:151-161`:

```lean
@[entry_point]
theorem rateDistortionFunction_convexOn
    (d : α → β → ℝ) (P : Measure α) [IsProbabilityMeasure P]
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) (D₁ D₂ : ℝ)
    (h_int_witness :
      ∀ (ν : Measure (α × β)), ν.map Prod.fst = P →
        Integrable (fun p => d p.1 p.2) ν) :
    rateDistortionFunction d P (lam * D₁ + (1 - lam) * D₂)
      ≤ ENNReal.ofReal lam * rateDistortionFunction d P D₁
        + ENNReal.ofReal (1 - lam) * rateDistortionFunction d P D₂ := by
  sorry
```

`variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]` (ファイル先頭, line 40)。
`h_int_witness` は **passive regularity hyp** (load-bearing でない。任意の X-marginal=P witness で distortion 可積分)。**過去の load-bearing `h_klDiv_conv` は migration note の通り削除済 (docstring:141-146)。**

`rateDistortionFunction` の定義 (`InformationTheory/Shannon/RateDistortion/Converse.lean:61-65`):

```lean
noncomputable def rateDistortionFunction (d : α → β → ℝ) (P : Measure α) (D : ℝ) : ℝ≥0∞ :=
  ⨅ (ν : Measure (α × β)) (_ : ν.map Prod.fst = P) (_ : expectedDistortion d ν ≤ D),
      klDiv ν ((ν.map Prod.fst).prod (ν.map Prod.snd))
```

証明戦略 (任意 feasible witness で press; plan 判断ログ準拠):

```
任意 feasible ν₁ at D₁ / ν₂ at D₂ をとる。
ν_λ := mixtureMeasure lam ν₁ ν₂ = ofReal lam • ν₁ + ofReal(1-lam) • ν₂   -- 既存 def
ν_λ.map fst = P                                                          -- 既存 mixtureMeasure_map_fst_eq
expectedDistortion d ν_λ ≤ lam·D₁ + (1-lam)·D₂                          -- 既存 mixtureMeasure_feasible
⟹ R(λD₁+(1-λ)D₂) ≤ klDiv ν_λ ((ν_λ.map fst).prod (ν_λ.map snd))         -- 既存 ..._le_of_feasible
                 ≤ lam·klDiv ν₁(P⊗m₁) + (1-lam)·klDiv ν₂(P⊗m₂)          -- ★ 核 = joint convexity (不在)
両辺で feasible witness 上 iInf をとり、ENNReal.mul_iInf_of_ne / iInf_add で press。
```

★印が唯一の Mathlib gap。残りは plumbing + 既存資産。

---

## A. `klDiv` の joint convexity が Mathlib に直接あるか

| 概念 | 検索クエリ | 結果 | 状態 |
|---|---|---|---|
| `(p₁,p₂) ↦ klDiv p₁ p₂` の joint 凸性 | `ConvexOn ℝ _ (fun p => InformationTheory.klDiv p.1 p.2)` | **Found 0** | ❌ **不在** |
| klDiv が ConvexOn に現れる任意補題 | `ConvexOn, InformationTheory.klDiv` | **Found 0** | ❌ **不在** |
| 第2引数についての凸性 | `ConvexOn ℝ _ (fun ν => InformationTheory.klDiv _ ν)` | **Found 0** | ❌ **不在** |
| measure 和に対する klDiv | `InformationTheory.klDiv (_ + _) _` | **Found 0 match** | ❌ **不在** |
| klDiv の劣加法性 `klDiv (..) ≤ klDiv + klDiv` | `klDiv _ _ ≤ klDiv _ _ + klDiv _ _` | **Found 0 match** | ❌ **不在** |
| 測度版 `mutualInfo` (Mathlib) | `ProbabilityTheory.mutualInfo, ConvexOn` | unknown identifier (`mutualInfo` 自体 Mathlib 不在) | ❌ **不在** |

→ **klDiv の joint convexity / 劣加法性 / 測度版 mutualInfo の凸性は Mathlib に一切ない (確認済)。** 自作必須。

**逆に「ある」smul 補題 (混同注意)** — measure scalar に効くが **同一スカラー両側のみ**:

| API | file:line | signature ([...] verbatim) | 結論形 verbatim |
|---|---|---|---|
| `klDiv_smul_same` | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:286` | `[IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : ℝ≥0)` | `klDiv (c • μ) (c • ν) = c * klDiv μ ν` |
| `klDiv_smul_right_eq_smul_left` | `Basic.lean:240` | `[IsFiniteMeasure μ] [IsFiniteMeasure ν] {c : ℝ≥0} (hc : c ≠ 0)` | `klDiv μ (c • ν) = c * klDiv (c⁻¹ • μ) ν` |
| `toReal_klDiv_smul_left` | `Basic.lean:179` | `(hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) (c : ℝ≥0)` | `(klDiv (c • μ) ν).toReal = c * (klDiv μ ν).toReal + (1 - c) * ν.real univ + c * log c * μ.real univ` |
| `toReal_klDiv_smul_same` | `Basic.lean:228` | `(hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) (c : ℝ≥0)` | `(klDiv (c • μ) (c • ν)).toReal = c * (klDiv μ ν).toReal` |

> **⚠️ 最大の落とし穴**: `klDiv_smul_same` は `klDiv (c•μ)(c•ν)` で **両側に同じ `c`**。本問題の核は `klDiv (λν₁+(1-λ)ν₂)(...)` で **和 + 異なる成分の混合**。`klDiv_smul_same` は和に分配しない (klDiv は measure 和について non-linear)。joint convexity は別物。

---

## B. `klDiv` の定義展開系 (両経路で必須の橋)

`klFun` の定義 (`Mathlib/InformationTheory/KullbackLeibler/KLFun.lean:53`):

```lean
noncomputable def klFun (x : ℝ) : ℝ := x * log x + 1 - x   -- ※ textbook の x log x - x + 1 と同値、項順注意
```

| API | file:line | signature ([...] verbatim) | 結論形 verbatim |
|---|---|---|---|
| `klDiv` (def, irreducible) | `Basic.lean:57` | `(μ ν : Measure α) : ℝ≥0∞` | `if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ) else ∞` |
| `klDiv_eq_lintegral_klFun_of_ac` | `Basic.lean:138` | `[IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν)` | `klDiv μ ν = ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν` |
| `klDiv_eq_integral_klFun` | `Basic.lean:111` | `[IsFiniteMeasure μ] [IsFiniteMeasure ν]` (open Classical) | `klDiv μ ν = if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν) else ∞` |
| `toReal_klDiv_eq_integral_klFun` | `Basic.lean:170` | `[IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ ≪ ν)` | `(klDiv μ ν).toReal = ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν` |
| `klDiv_of_not_ac` | `Basic.lean:68` (`@[simp]`) | `(h : ¬ μ ≪ ν)` | `klDiv μ ν = ∞` |
| `klDiv_of_not_integrable` | `Basic.lean:73` (`@[simp]`) | `(h : ¬ Integrable (llr μ ν) μ)` | `klDiv μ ν = ∞` |
| `klDiv_self` | `Basic.lean:78` (`@[simp]`) | `(μ : Measure α) [SigmaFinite μ]` | `klDiv μ μ = 0` |
| `klDiv_zero_left` | `Basic.lean:86` (`@[simp]`) | `[IsFiniteMeasure ν]` | `klDiv 0 ν = ν univ` |
| `klDiv_zero_right` | `Basic.lean:91` (`@[simp]`) | `[NeZero μ]` | `klDiv μ 0 = ∞` |
| `klDiv_ne_top` | `Basic.lean:103` | `(hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)` | `klDiv μ ν ≠ ∞` |
| `klDiv_ne_top_iff` | `Basic.lean:100` | — | `klDiv μ ν ≠ ∞ ↔ μ ≪ ν ∧ Integrable (llr μ ν) μ` |
| `integrable_klFun_rnDeriv_iff` | `Basic.lean` (DPI.lean:73 で利用) | `(hμν : μ ≪ ν)` | `Integrable (fun x ↦ klFun (μ.rnDeriv ν x).toReal) ν ↔ Integrable (llr μ ν) μ` |

`klFun` の凸性・連続性 (`Mathlib/InformationTheory/KullbackLeibler/KLFun.lean`):

| API | file:line | signature ([...] verbatim) | 結論形 verbatim |
|---|---|---|---|
| `convexOn_klFun` | `KLFun.lean:67` | — | `ConvexOn ℝ (Ici 0) klFun` |
| `strictConvexOn_klFun` | `KLFun.lean:62` | — | `StrictConvexOn ℝ (Ici 0) klFun` |
| `convexOn_Ioi_klFun` | `KLFun.lean:71` | — | `ConvexOn ℝ (Ioi 0) klFun` |
| `continuous_klFun` | `KLFun.lean:76` | — | `Continuous klFun` |
| `measurable_klFun` | `KLFun.lean:80` | — | `Measurable klFun` |
| `klFun_nonneg` | `KLFun.lean:149` | `(hx : 0 ≤ x)` | `0 ≤ klFun x` |
| `klFun_apply` | `KLFun.lean:55` | `(x : ℝ)` | `klFun x = x * log x + 1 - x` |
| `klFun_zero` | `KLFun.lean:57` | — | `klFun 0 = 1` |
| `klFun_one` | `KLFun.lean:59` | — | `klFun 1 = 0` |

---

## C. `klDiv` chain rule / tensorization (selector 経路の核)

`Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean`。**`⊗ₘ` = `Measure.compProd`。**

| API | file:line | signature ([...] verbatim) | 結論形 verbatim |
|---|---|---|---|
| `klDiv_compProd_left` | `ChainRule.lean:182` (`@[simp]`) | `variable (μ ν κ)` (file scope; `κ : Kernel α β` 等) | `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν` |
| `klDiv_compProd_eq_add` | `ChainRule.lean:204` | `variable (μ ν κ η)` | `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` |
| `integral_llr_compProd_eq_add` | `ChainRule.lean:151` | `(h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η)` + 可積分仮定 | (llr の積分加法、補助) |

**プロジェクト内 mutualInfo / joint 関係**:

| API | file:line | signature ([...] verbatim) | 結論形 verbatim |
|---|---|---|---|
| `mutualInfo` (def) | `InformationTheory/Shannon/MutualInfo.lean:37` | `(μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y)` (`variable {Ω}[MeasurableSpace Ω]{X}[MeasurableSpace X]{Y}[MeasurableSpace Y]`) | `klDiv (μ.map (fun ω => (Xs ω, Yo ω))) ((μ.map Xs).prod (μ.map Yo))` |
| `klDiv_joint_eq_mutualInfo` (private) | `Converse.lean:102` | `(μ : Measure Ω) (X : Ω → α) (Xh : Ω → β) (hX : Measurable X) (hXh : Measurable Xh)` | `klDiv (μ.map (X,Xh)) (((..).map fst).prod ((..).map snd)) = mutualInfo μ X Xh` (R(D) の被 iInf 項 = MI を結ぶ) |
| `mutualInfo_nonneg` | `MutualInfo.lean:44` | `(μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y)` | `0 ≤ mutualInfo μ Xs Yo` (= `bot_le`) |

> 注: R(D) の被 iInf 項は `klDiv ν ((ν.map fst).prod (ν.map snd))`。**X-marginal `ν.map fst = P` は全 witness 共有 (固定)、`ν.map snd` だけが `ν` に線形**。混合 `ν_λ` では `ν_λ.map snd = ofReal λ • (ν₁.map snd) + ofReal(1-λ) • (ν₂.map snd)`。第2引数の左因子 `P` は固定・右因子だけ混合。

---

## D. selector-forget (DPI) 経路の道具

**戦略**: `klDiv_map_le` (一般 pushforward DPI, 既存) を「selector 付き拡張測度 → selector を忘れる射影」に適用。
selector measure `μ̃ on (Bool × (α×β))` (or `Fin 2 × (α×β)`): `λ`-重み付き 2 点分布 ⊗ 各成分。
chain rule で `klDiv μ̃ ((..)分母) = klDiv(selector 周辺) + Σ λᵢ klDiv(νᵢ ‖ marginᵢ)`、selector を pushforward (`Prod.snd` で忘却) すると分子 = 混合 ν_λ、DPI で `≤`。

| API | file:line | signature ([...] verbatim) | 結論形 verbatim |
|---|---|---|---|
| **`klDiv_map_le`** (プロジェクト, 既存・proof done) | `InformationTheory/Shannon/DPI.lean:54` | `{α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β} (hf : Measurable f) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]` | `klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν` |
| `klDiv_map_measurableEquiv` (プロジェクト, 既存) | `InformationTheory/Shannon/MutualInfo.lean:54` | `{α β} [MeasurableSpace α][MeasurableSpace β] (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]` | `klDiv (μ.map e) (ν.map e) = klDiv μ ν` |
| `Measure.rnDeriv_add` | `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean:683` | `(ν₁ ν₂ μ : Measure α) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] [ν₁.HaveLebesgueDecomposition μ] [ν₂.HaveLebesgueDecomposition μ] [(ν₁ + ν₂).HaveLebesgueDecomposition μ]` | `(ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.rnDeriv μ + ν₂.rnDeriv μ` |
| `Measure.rnDeriv_smul_left` | `Lebesgue.lean:611` | `(ν μ : Measure α) [IsFiniteMeasure ν] [ν.HaveLebesgueDecomposition μ] (r : ℝ≥0)` | `(r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ` |
| `Measure.rnDeriv_smul_left_of_ne_top` | `Lebesgue.lean:628` | `(ν μ : Measure α) [IsFiniteMeasure ν] [ν.HaveLebesgueDecomposition μ] {r : ℝ≥0∞} (hr : r ≠ ∞)` | `(r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ` |
| `Measure.rnDeriv_smul_right` | `Lebesgue.lean:637` | `(ν μ : Measure α) [IsFiniteMeasure ν] [ν.HaveLebesgueDecomposition μ] {r : ℝ≥0} (hr : r ≠ 0)` | `ν.rnDeriv (r • μ) =ᵐ[μ] r⁻¹ • ν.rnDeriv μ` |
| `Measure.prod_add` | `Mathlib/MeasureTheory/Measure/Prod.lean:801` | `(ν' : Measure β) [SFinite ν']` (`variable (μ : Measure α)(ν : Measure β)`) | `μ.prod (ν + ν') = μ.prod ν + μ.prod ν'` |
| `Measure.add_prod` | `Prod.lean:809` | `(μ' : Measure α) [SFinite μ']` | `(μ + μ').prod ν = μ.prod ν + μ'.prod ν` |
| `Measure.prod_smul_left` | `Prod.lean:838` | `{μ : Measure α} (c : ℝ≥0∞)` | `(c • μ).prod ν = c • (μ.prod ν)` |
| `Measure.prod_smul_right` | `Mathlib/MeasureTheory/Measure/WithDensity.lean:718` | `(c : ℝ≥0∞)` (`variable (μ ν)`) | `μ.prod (c • ν) = c • (μ.prod ν)` |
| `Measure.map_map` (合成) | `MeasureSpace` | `(hg : Measurable g)(hf : Measurable f)` | `(μ.map f).map g = μ.map (g ∘ f)` (既存利用パターン Converse.lean:87) |
| `Measure.map_add` | `MeasureSpace` | `(hf : Measurable f)` | `(μ + ν).map f = μ.map f + ν.map f` (mixtureMeasure_map_fst で利用済) |
| `Measure.map_smul` | `MeasureSpace` | — | `(c • μ).map f = c • μ.map f` (mixtureMeasure_map_fst で利用済) |
| `Measure.isFiniteMeasure_map` | `MeasureSpace` | `(μ : Measure α)(f : α → β)` | `IsFiniteMeasure (μ.map f)` (DPI.lean:69 で利用) |

> 注: `prod_add`/`prod_smul_*` は **`SFinite` / 値が `ℝ≥0∞`** で動く。確率測度・有限測度は `SFinite` 自動。selector 拡張で `Measure (Bool × (α×β))` を扱う際 `Bool` の可測空間 (`MeasurableSpace.instBool` / discrete) は自動。

---

## E. lintegral 凸性 / Jensen 系 (DPI 経路の `klDiv_map_le` 内部・pmf 経路でも利用)

| API | file:line | signature ([...] verbatim) | 結論形 verbatim |
|---|---|---|---|
| `ConvexOn.map_condExp_le` | `Mathlib/MeasureTheory/Function/ConditionalExpectation/CondJensen.lean:168` | `(hm : m ≤ mα) [SigmaFinite (μ.trim hm)] (hφ_cvx : ConvexOn ℝ s φ) (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s) (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ)` | `φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m]` |
| `ConcaveOn.condExp_map_le` | `CondJensen.lean:184` | (上記 ConvexOn の dual) | `μ[φ ∘ f | m] ≤ᵐ[μ] φ ∘ μ[f | m]` |
| `ConvexOn.apply_rnDeriv_ae_le_integral` | `Mathlib/MeasureTheory/Measure/Decomposition/IntegralRNDeriv.lean:137` | `(hf : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0) (h_int : Integrable (fun p ↦ f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η)) (hκη : μ ⊗ₘ κ ≪ μ ⊗ₘ η)` | `(fun a ↦ f (μ.rnDeriv ν a).toReal) ≤ᵐ[ν] fun a ↦ ∫ b, f ((μ⊗ₘκ).rnDeriv (ν⊗ₘη) (a,b)).toReal ∂(η a)` |
| `toReal_rnDeriv_map` | `Mathlib/MeasureTheory/Function/ConditionalExpectation/RadonNikodym.lean:52` | `[IsFiniteMeasure μ] (hμν : μ ≪ ν) {g : 𝓧 → 𝓨} (hg : Measurable g) [hσ : SigmaFinite (ν.map g)]` | `(fun a ↦ ((μ.map g).rnDeriv (ν.map g) (g a)).toReal) =ᵐ[ν] ν[(fun a ↦ (μ.rnDeriv ν a).toReal) | m𝓨.comap g]` |
| `lintegral_add_measure` | `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean:420` (`@[simp]`) | `(f : α → ℝ≥0∞) (μ ν : Measure α)` | `∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν` |
| `lintegral_smul_measure` | `Lebesgue/Basic.lean:405` | `{R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R) (f : α → ℝ≥0∞)` | `∫⁻ a, f a ∂c • μ = c • ∫⁻ a, f a ∂μ` |
| `ConvexOn.map_integral_le` | `Mathlib/Analysis/Convex/Integral.lean:199` | `[IsProbabilityMeasure μ] (hg : ConvexOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ)` | `g (∫ x, f x ∂μ) ≤ ∫ x, g (f x) ∂μ` |
| `ConvexOn.map_sum_le` | `Mathlib/Analysis/Convex/Jensen.lean:67` | `(hf : ConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s)` | `f (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • f (p i)` |
| `ENNReal.mul_iInf_of_ne` | `Mathlib/Data/ENNReal/Inv.lean:859` | `(ha₀ : a ≠ 0) (ha : a ≠ ∞)` | `a * ⨅ i, f i = ⨅ i, a * f i` |
| `ENNReal.iInf_add` | `Mathlib/Data/ENNReal/Operations.lean:550` | — | `iInf f + a = ⨅ i, f i + a` |

---

## F. 有限 / pmf 形 fallback

| API | file:line | signature ([...] verbatim) | 結論形 verbatim |
|---|---|---|---|
| `rateDistortionFunctionPmf` (def) | `InformationTheory/Shannon/RateDistortion/Achievability.lean:234` | `[Fintype α][Fintype β]...` (file scope) `(P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) : ℝ` | `sInf (mutualInfoPmf '' RDConstraint P_X d D)` |
| `mutualInfoPmf` (def) | `Achievability.lean:201` | `(q : α × β → ℝ) : ℝ` | `(∑ a, negMulLog (marginalFst q a)) + (∑ b, negMulLog (marginalSnd q b)) - (∑ p, negMulLog (q p))` |
| `marginalFst` / `marginalSnd` | `Achievability.lean:123 / 127` | `(q : α × β → ℝ)` | (pmf の周辺) |
| `RDConstraint` | `Achievability.lean:158` | — | 制約集合 (`Set (α×β → ℝ)`) |
| `continuous_mutualInfoPmf` | `Achievability.lean:207` | — | `Continuous (fun q : α × β → ℝ => mutualInfoPmf q)` |
| **`log_sum_inequality_negMulLog`** (プロジェクト既存) | `InformationTheory/Fano/DPI.lean:45` | `{ι : Type*} (s : Finset ι) (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) (h_ac : ∀ i ∈ s, b i = 0 → a i = 0)` | `∑ i ∈ s, (negMulLog (a i) + a i * log (b i)) ≤ negMulLog (∑ i ∈ s, a i) + (∑ i ∈ s, a i) * log (∑ i ∈ s, b i)` |
| **`log_sum_inequality`** (プロジェクト既存) | `InformationTheory/Shannon/LZ78/ZivEntropyBridge.lean:71` | `{ι : Type*} (s : Finset ι) (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i)` | `(∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) ≤ ∑ i ∈ s, a i * log (a i / b i)` |
| `Finset.sum_le_sum` | Mathlib basic | `(h : ∀ i ∈ s, f i ≤ g i)` | `∑ i ∈ s, f i ≤ ∑ i ∈ s, g i` |
| `ConcaveOn.le_map_sum` | `Jensen.lean:73` | (上記 ConvexOn.map_sum_le dual) | `(∑ i ∈ t, w i • f (p i)) ≤ f (∑ i ∈ t, w i • p i)` |

> **⚠️ pmf 形は別定義 `rateDistortionFunctionPmf : ℝ` (sInf, real 値)。主問題の `rateDistortionFunction : ℝ≥0∞` (iInf, measure 形) と型が違う。** pmf 経路を採る場合は (1) 主定理 signature に `[Fintype α][Fintype β][MeasurableSingletonClass α][MeasurableSingletonClass β]` を追加し measure↔pmf 橋を書くか、(2) pmf 形 `rateDistortionFunctionPmf_convexOn` を別途立てて主定理から橋渡しするか。**この橋自体が ~100-150 行 plumbing (`klDiv_eq_lintegral_klFun_of_ac` の `≪` 前提 + Finset.sum 形)。**

---

## 重要・前提条件ボックス (事故りやすい箇所)

- **`klDiv_smul_same` を混合に使えない**: 同一スカラー両側専用。joint convexity の代替には**ならない** (再掲・最重要)。
- **`klDiv_map_le` の前提**: `[IsFiniteMeasure μ] [IsFiniteMeasure ν]` + `Measurable f`。R(D) では measure は確率/有限なので OK。selector 拡張 `Measure (Bool × (α×β))` も有限和なら有限。
- **`klDiv_eq_lintegral_klFun_of_ac` は `μ ≪ ν` 必須**: 混合で片方が非絶対連続だと `klDiv = ∞` (`klDiv_of_not_ac`)。`∞` ケースは RHS `ofReal λ * ∞` で trivially close (案: `le_top` / `iInf = ∞`)。non-ac 側の case split は plan 判断ログでも撤退点として既出。
- **`mixtureMeasure_map_fst_eq` / `mixtureMeasure_feasible` は `0 ≤ lam` `lam ≤ 1` 必須** (既存補題, marginal が P に戻るのは `ofReal λ + ofReal(1-λ) = 1` から)。境界 `lam = 0,1` は `ENNReal.mul_iInf_of_ne` が `a ≠ 0` を要求するため別 branch (plan 撤退点既出)。
- **`prod_add`/`prod_smul_right` は `SFinite` 前提**: 確率・有限測度なら自動。selector 経路で `P.prod (ν.map snd)` を混合に展開する核 (`P` 固定・右因子だけ線形)。
- **`ConvexOn.apply_rnDeriv_ae_le_integral` / `toReal_rnDeriv_map` は `compProd` 構造 (`μ ⊗ₘ κ`) / `SigmaFinite (ν.map g)` 前提**: selector measure を `μ ⊗ₘ κ` 形に乗せるか、`klDiv_map_le` (既に内部でこれらを使い proof done) をブラックボックスとして再利用するかで複雑度が変わる。**`klDiv_map_le` をそのまま呼べば内部 Jensen は触らずに済む** (DPI 経路の利点)。

---

## 自作が必要な要素 (優先度順)

### DPI (selector-forget) 経路を採る場合

1. **selector 拡張測度の構成 + 周辺/射影性質** (~40-80 行)
   - `selectorJoint lam ν₁ ν₂ : Measure (Bool × (α×β))` (or `Fin 2`): `ofReal λ • (dirac true).prod ν₁ + ofReal(1-λ) • (dirac false).prod ν₂` 等。
   - `Prod.snd` pushforward (selector 忘却) = `mixtureMeasure lam ν₁ ν₂` (既存 def に一致)。
   - 落とし穴: `Bool`/`Fin 2` の可測空間・`dirac` の prod・`map_add`/`map_smul` plumbing。
2. **`klDiv` joint convexity 核補題** `klDiv_mixture_le` (~60-120 行)
   - `klDiv (mixture λ ν₁ ν₂) (P.prod (mixture λ (ν₁.map snd) (ν₂.map snd))) ≤ λ·klDiv ν₁ (P.prod m₁) + (1-λ)·klDiv ν₂ (P.prod m₂)`。
   - 手段: selector 拡張で chain rule (`klDiv_compProd_eq_add`) → `klDiv_map_le` (Prod.snd 射影で selector 忘却) → selector 周辺の klDiv を分離。**Mathlib `klDiv_compProd_eq_add` の分母が `μ ⊗ₘ η` 形である点と、R(D) 分母が `prod` (= 独立 compProd) である点の整合**が plumbing の山。`prod_add`/`prod_smul_right` で分母を混合形に展開。
   - 落とし穴: 分母の `ν_λ.map fst = P` 固定 / `ν_λ.map snd` 線形のため、`klDiv ν₁` の分母を `P.prod m₁` ではなく `P.prod (mixture..)` に揃える必要があり、ここで convexity が効く。selector を入れずに直接 `klDiv_map_le` だけで閉じるかは要 gateway 検証 (chain rule の方向が合うか)。
3. **iInf press** (~40-60 行, plan 判断ログの手順流用)
   - 任意 feasible witness で per-pair bound → `ENNReal.mul_iInf_of_ne` 3 層 + `iInf_add`/`add_iInf` で RHS を入れ子 iInf に展開 → `le_iInf` 6 層降りる。境界 `lam=0,1` case split。
   - **これは過去 subnormal 版で一度書けていた手順** (plan 判断ログ「iInf plumbing の流れ」)。h_klDiv_conv の代わりに自作 (2) を差すだけ。

合計 DPI 経路: **~140-260 行 / 自作 2-3 補題** (うち核は (2))。

### pmf 有限形限定の場合

1. **signature 変更**: 主定理に `[Fintype α] [Fintype β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]` を追加 (consumers 0 件のため blast radius ゼロ — 下記)。
2. **measure↔pmf 橋** (~100-150 行): `klDiv ν (P.prod m) = Finset.sum 形`。`klDiv_eq_lintegral_klFun_of_ac` + `MeasurableSingletonClass` で点質量に reduce。`CsiszarProjection.klDivPmf` パターン流用 (plan が言及するが、現状そのファイルに該当補題があるか要確認)。
3. **per-atom joint convexity** (~80-150 行): 既存 `log_sum_inequality_negMulLog` (Fano/DPI.lean:45) を per-atom 適用 + `Finset.sum_le_sum` 集約。これが pmf 経路の核 (Mathlib `convexOn_klFun` だけでは `q·klFun(p/q)` の `q` 依存で出ない、と plan 撤退点が明記)。
4. **pmf 形 R(D) と measure 形 R(D) の値一致** (~50-100 行): `rateDistortionFunction (measure) = ENNReal.ofReal (rateDistortionFunctionPmf ...)` 相当。型が `ℝ≥0∞` vs `ℝ` で異なるため非自明。

合計 pmf 経路: **~230-400 行 / 自作 3-4 補題 + signature 変更**。

> **どちらが安いかの推奨はここでは書かない** (pivot-advisor / orchestrator 判断)。事実として: DPI 経路は既存 `klDiv_map_le` (proof done) を核に再利用でき行数が小さい見込みだが chain rule の方向整合が gateway risk。pmf 経路は既存 log-sum を核に確実だが measure↔pmf↔型変換の橋が嵩む + signature 変更を伴う。

---

## Mathlib 壁の列挙

| 壁 | loogle 確認 | shared sorry-lemma 候補か |
|---|---|---|
| **`klDiv` の joint convexity** `ConvexOn (fun p => klDiv p.1 p.2)` | `Found 0 declarations mentioning ... InformationTheory.klDiv, and ConvexOn.` (query `ConvexOn ℝ _ (fun p => InformationTheory.klDiv p.1 p.2)` / `ConvexOn, InformationTheory.klDiv` 双方 0) | **共有 sorry-lemma 化を推奨**: Cover-Thomas 2.7.2 = relative entropy joint convexity は E-3' achievability / 他 RD 系でも要る汎用壁。`klDiv_mixture_convexOn` (or `klDiv_jointConvex`) を 1 本立て、本定理 + 将来 achievability から呼ぶ。詳細 → `docs/audit/audit-tags.md` "Shared Mathlib walls"。 |
| **`klDiv` の measure-和 劣加法性** `klDiv (a+b)(c+d) ≤ klDiv a c + klDiv b d` | `Found 0 match` (query `klDiv _ _ ≤ klDiv _ _ + klDiv _ _`) | 上記 joint convexity の特殊形。同一壁。 |
| **測度版 `mutualInfo` の凸性 (Mathlib 側)** | Mathlib に `mutualInfo` 自体不在 (`ProbabilityTheory.mutualInfo` unknown identifier) | プロジェクト `InformationTheory.Shannon.mutualInfo` のみ。Mathlib 壁としては joint convexity に集約。 |

> **唯一の真の壁は「`klDiv` joint convexity (= relative entropy joint convexity, Cover-Thomas 2.7.2)」1 点。** 残りはすべて plumbing or 既存資産。DPI 経路ならこの壁を `klDiv_map_le` + chain rule で**自作で閉じられる見込み** (純粋 Mathlib gap ではなく "未配線" 寄り)。pmf 経路なら既存 log-sum で per-atom 閉じる。**したがって `@residual(wall:...)` ではなく `@residual(plan:rate-distortion-convexity-plan)` (現状コードの分類) が適切** — 単一 plan で閉じうる。gateway-atom (核補題 (2) を 1 本 lean-implementer に投げて通るか) で wall/plan を最終確定すべき。

---

## 撤退ラインとの距離

親計画 [`rate-distortion-convexity-plan.md`](rate-distortion-convexity-plan.md) の撤退点 (判断ログ):

- **「`klDiv` joint convexity の log-sum 経由 discharge」は撤退済** → subnormal (hypothesis) 化 → **さらに migration でその hyp を削除し `sorry` 化** (現状コード)。つまり**親計画の撤退ラインは既に発動済で、今回はその撤退の「巻き戻し」(genuine 化) を目指す**。
- **boundary case `lam = 0,1`** の case-split は撤退点というより既知の plumbing。`ENNReal.mul_iInf_of_ne` の `a ≠ 0` 要求は subnormal 版で既にハンドル済 (手順流用可能)。

判定: **新たな撤退ラインに触れる箇所はあるが、発動は現時点で不要**。

- DPI 経路の核補題 (2) が「chain rule の方向不整合で閉じない」場合 → pmf 経路に切替 (signature に Fintype 追加)。これは degenerate fallback ではなく route 切替。
- 両経路とも 1 週間で gateway atom が通らない場合の degenerate fallback (新規撤退ライン案):
  - **退避出口は `sorry` + `@residual(plan:rate-distortion-convexity-plan)` のまま据え置き** (現状維持; hypothesis bundling は禁止)。
  - 縮退案として「**有限アルファベット `[Fintype α][Fintype β]` を主定理 signature に恒久追加し pmf 形のみで genuine 化、measure 形 (一般 α,β) は別シードへ park**」。これは hypothesis 追加でなく **regularity / scope 制約の追加**なので honesty 上 OK。consumers 0 件のため安全 (下記)。

**consumers (signature 変更の blast radius, 実測値)**: `scripts/dep_consumers.sh InformationTheory.Shannon.rateDistortionFunction_convexOn` → **direct consumers: 0 decl / 0 file**。`ConvexityDischarge.lean` は import するが decl 参照ゼロ (中身は orphan 削除済の空 namespace)。**Fintype 追加・signature 変更の blast radius は事実上ゼロ。**

---

## 着手のための skeleton

`InformationTheory/Shannon/RateDistortion/Convexity.lean` は既存 (上記 sorry が live)。**核補題を 1 本足す形**で着手する skeleton (DPI 経路):

```lean
-- 既存 import に追加不要 (ConverseMonotone 経由で DPI / klDiv 系は推移的に入る)。
-- 必要なら明示: import InformationTheory.Shannon.DPI

namespace InformationTheory.Shannon
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- 核補題: `klDiv` の joint convexity (混合測度形)。
分母 `P` (X-marginal) は両 witness で固定、`ν.map snd` のみ線形。
selector-forget (DPI: `klDiv_map_le` + `klDiv_compProd_eq_add`) で構築する。
`@residual(plan:rate-distortion-convexity-plan)` -/
theorem klDiv_mixture_le
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1)
    (P : Measure α) [IsProbabilityMeasure P]
    (ν₁ ν₂ : Measure (α × β)) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : ν₁.map Prod.fst = P) (h₂ : ν₂.map Prod.fst = P) :
    klDiv (mixtureMeasure lam ν₁ ν₂)
        (((mixtureMeasure lam ν₁ ν₂).map Prod.fst).prod
          ((mixtureMeasure lam ν₁ ν₂).map Prod.snd))
      ≤ ENNReal.ofReal lam * klDiv ν₁ ((ν₁.map Prod.fst).prod (ν₁.map Prod.snd))
        + ENNReal.ofReal (1 - lam) * klDiv ν₂ ((ν₂.map Prod.fst).prod (ν₂.map Prod.snd)) := by
  sorry

-- 主定理 (既存) の sorry を上記核補題 + 既存 mixtureMeasure_feasible
-- + rateDistortionFunction_le_of_feasible + iInf press で割る。
end InformationTheory.Shannon
```

最初の `sorry` (`klDiv_mixture_le`) を gateway atom として 1 本 lean-implementer に投げ、DPI 経路で閉じるか確認 → 通れば主定理を iInf press で割る / 通らなければ pmf 経路 (Fintype 追加 + log-sum) に切替。

---

## 「Phase B で使う API のうち X% が既存」

- 分母 (主定理を割るのに使う primitive): 約 18 項目
  - mixture 既存補題 (`mixtureMeasure` / `_map_fst` / `_map_snd` / `_map_fst_eq` / `expectedDistortion_mixtureMeasure` / `_feasible`) ×6 (proof done)
  - R(D) 既存 (`rateDistortionFunction` def / `_le_of_feasible`) ×2
  - klDiv 展開・凸 (`klDiv_eq_lintegral_klFun_of_ac` / `convexOn_klFun` / `klFun_nonneg` / `klDiv_of_not_ac`) ×4
  - DPI 経路 (`klDiv_map_le` / `klDiv_compProd_eq_add` / `prod_add` / `prod_smul_right` / `rnDeriv_add`) ×5
  - iInf press (`ENNReal.mul_iInf_of_ne` / `ENNReal.iInf_add`) ×... (上記に含む)
- 分子 (既存): 17 項目 (上記すべて既存)
- **既存率 ~95% (primitive ベース)。不在は joint convexity 核 1 点 (selector 構成 + 核補題で自作)。**

> **要約**: Phase B genuine 化に必要な道具はほぼ全て Mathlib + プロジェクトに揃っている。自作するのは「joint convexity 核補題 1 本 + (DPI 経路なら) selector 拡張測度 1 個 / (pmf 経路なら) measure↔pmf 橋 + per-atom log-sum 集約」。最大の落とし穴は `klDiv_smul_same` (同一スカラー専用) を混合に流用できると誤認すること。
