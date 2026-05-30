# EPI Stam/Blachman 壁 — 密度レベル明示積分経路 Mathlib 在庫

> **⚠ 2026-05-30 戦略整合注記 (implementer 必読)**: 本 file の Part 2/Verdict/自作要素テーブルの一部は
> S1 を「`condExp_ae_eq_integral_condDistrib_id` による disintegration 表現 (~80-150 行、唯一の真壁)」と
> 記述しているが、これは**旧 condExp 経路の残骸**で、親計画 `epi-wall-reattack-plan.md` §Phase 3 が採用する
> **explicit density route とは非採用**。authoritative 戦略は plan §Phase 3 の 6-step 骨子: `s_Z(z) =
> ∫_x W_λ(x,z)·p_{X|Z}(x|z) dx` (条件付き密度 `p_{X|Z}:=fX(x)fY(z-x)/p_Z(z)` を Bochner ∫ で明示書下し、
> `condExp`/`condDistrib`/`StandardBorelSpace` を**一切使わない**) → 点ごと積分 Cauchy-Schwarz → Tonelli +
> p_Z 約分。`fisherInfoOfMeasureV2 _μ f = fisherInfoOfDensity f` (`FisherInfoV2DeBruijn.lean:86`, `rfl`,
> measure 引数無視) で target が純密度解析命題に collapse するため disintegration 不要。本 file からは
> **API 部品** (積分 CS / Tonelli / IBP の `[...]` 前提 verbatim) のみ消費し、S1/S3/S4 の condExp 戦略記述は
> 無視すること。atom 分解 (A/B/C → Phase 3a-d) は plan §Phase 3 が SoT。

> 調査対象: `stam_step2_density_wall` (`Common2026/Shannon/EPIStamInequalityBody.lean:376`,
> `@residual(wall:stam-blachman)`) を **密度レベルで条件付き密度を Bochner ∫ 明示書き下す経路**
> で closure するのに必要な Mathlib API の在庫を取る。
>
> **前任 inventory との違い**: [`epi-stam-blachman-discharge-inventory.md`](epi-stam-blachman-discharge-inventory.md)
> は抽象 `condExp`/`condDistrib` 経路で「`⋆ₗ` (lconvolution) の微分可能性が Mathlib 不在 = PR 級壁」と結論
> した。本調査は **別経路** = `convDensityAdd pX pY z := ∫ x, pX x · pY (z-x) ∂volume` (Bochner ∫,
> Phase 1 gateway `EPIConvDensity.lean` が既供給、`convDensityAdd_hasDerivAt`/`convDensityAdd_logDeriv`
> ともに `@audit:ok`) を出発点とし、**`⋆ₗ` を回避した明示積分の API 在庫**を取る。
>
> 同 family: [`fisher-info-mathlib-inventory.md`](fisher-info-mathlib-inventory.md),
> [`epi-stam-blachman-discharge-inventory.md`](epi-stam-blachman-discharge-inventory.md)。
> 親計画: [`epi-wall-reattack-plan.md`](epi-wall-reattack-plan.md) (Phase 3 = 本壁本体)。
>
> **調査日**: 2026-05-30 (subagent 1 ターン)。loogle index = `.lake/build/loogle.index`。

---

## Part 3 先出し — feasibility verdict (REQUIRED, lead with this)

### 密度レベル経路 5 step の Mathlib 充足表

`stam_step2_density_wall` の真壁 = `IsStamCauchySchwarzOptimal X Y P` の結論
`J_sum ≤ J_X·J_Y/(J_X+J_Y)`、`hconv : fXY =ᵐ[volume] convDensityAdd fX fY` 制約下で。
`J(f) := (fisherInfoOfMeasureV2 μ f).toReal = (∫⁻ (logDeriv f x)²·f x dx).toReal`
(`FisherInfoV2DeBruijn.lean:77` で `fisherInfoOfMeasureV2 _μ f := fisherInfoOfDensity f`, 測度引数は phantom)。

| step | 数学内容 | Mathlib 状態 | 補題 / gap / self-build 見積 |
|---|---|---|---|
| **S1 条件付き密度明示** | `s_Z(z) = (logDeriv convDensityAdd)(z) = (∫ pX'(x)pY(z-x)dx) / p_Z(z)` を Blachman 形 `s_Z(z) = E[s_X(X) \| X+Y=z]` に同定 | **部分在** | `convDensityAdd_logDeriv` (`EPIConvDensity.lean:113`, 自前 `@audit:ok`) が左辺を供給。右辺 condExp 表現は `condExp_ae_eq_integral_condDistrib_id` (`CondDistrib.lean:438`) で書けるが、両者を結ぶ「畳み込み密度の score = 条件付き score 期待値」の橋は **不在 self-build (~80-150 行)** |
| **S2 Blachman 積分恒等式** | `∫ pX'(x)pY(z-x)dx = ∫ pX(x)pY'(z-x)dx` (score 対称化) + cross-term drop | **部分在** | 全直線 IBP `integral_mul_deriv_eq_deriv_mul_of_integrable` (`IntegralEqImproper.lean:1318`) + 併進不変 `integral_sub_left_eq_self` (`Group/Integral.lean`, gateway で使用済) が部品。cross-term=0 は Phase 2 `score_cross_term_eq_zero` (別 file, 計画済) が供給予定。self-build ~40-80 行 |
| **S3 積分 Cauchy-Schwarz** | `s_Z(z)² ≤ E[(λs_X+(1-λ)s_Y)² \| X+Y=z]` (条件付き Jensen の `x²` 凸版) | **在** | `ConvexOn.map_condExp_le` (`CondJensen.lean:168`) — 条件付き Jensen `φ∘μ[f\|m] ≤ᵐ μ[φ∘f\|m]`。`φ = (·)²` 凸で直接。または `condVar_ae_le_condExp_sq` (`CondVar.lean:127`)。Bochner Hölder `integral_mul_le_Lp_mul_Lq_of_nonneg` (`Bochner/Basic.lean:1237`) も別ルートで在 |
| **S4 Tonelli 順序交換 + 約分** | `∫_z (∫_x …) p_Z(z) dz → ∫_x …` で total expectation を取り `J(X)/J(Y)` に約分 | **在** | `integral_integral_swap` (`Integral/Prod.lean:532`), `lintegral_lintegral_swap` (`Measure/Prod.lean:1058`), total expectation `integral_condExp` (`ConditionalExpectation/Basic.lean`). 約分は `integral_logDeriv_density_eq_zero` (`FisherInfoV2.lean:158`, `@audit:ok`) |
| **S5 λ 最適化** | `min_λ λ²a+(1-λ)²b = ab/(a+b)` at `λ=b/(a+b)` | **完済 (自前)** | `stam_lambda_min` (`EPIStamInequalityBody.lean:204`, `@audit:ok`) + `stam_lambda_lower_bound` (`:216`, `@audit:ok`)。Mathlib 不要、`field_simp`/`nlinarith` で完了済 |

### Verdict — 1 セッション closure 可能か / 支配項 atom

**1 セッションでの genuine (0-sorry) closure は NO。** ただし前任 inventory の「`⋆ₗ` 微分可能性壁
= PR 級」は **本経路で解消済** — Phase 1 gateway `convDensityAdd_hasDerivAt` (`EPIConvDensity.lean:86`,
`@audit:ok`) が parametric-integral 経路 (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) で
`HasCompactSupport` 不適合を迂回し、`∫`-form 畳み込み密度の点ごと微分可能性 + `logDeriv` 表現を
**genuine に供給している**。これが本 pivot の決定的進展。

- **支配項 atom = S1 (Blachman 条件付き score 表現)**: `s_Z = E[s_X | X+Y=z]`。`convDensityAdd_logDeriv`
  が左辺の解析的内容を closure 済なので、残るは「畳み込み密度の logDeriv (= 既知の `∫pX'·pY(z-x)/p_Z`)
  を condDistrib 積分形に同定する disintegration 橋」。Mathlib に **`condExp ∧ convolution density`
  同時補題が皆無** (`Blachman`/`Stam`/`fisherInfo` ともに loogle `Found 0`)。この橋が self-build ~80-150 行
  で **1 セッション超** (親計画 L-EPIW-3-α 発火確率高と整合)。
- **S2/S3/S4/S5 は Mathlib 部品揃い** = closure 可能パート。S3 (条件付き Jensen)・S4 (Tonelli+total exp)・
  S5 (λ 最適化, 完済) は壁なし。S2 (IBP score 対称化) も部品揃いだが cross-term drop が Phase 2 依存。
- **結論**: 本経路は前任の「PR 級壁」を **「S1 disintegration 橋の self-build (~80-150 行) のみが真壁」**
  に縮小した。closure は S1 を独立 file で建てる 2-3 セッション仕事。1 セッションでは S2-S5 を ship + S1 を
  `sorry` + `@residual(wall:stam-blachman)` 据置が現実的着地。

---

## 主定理の最終形 (再掲)

`stam_step2_density_wall` (`EPIStamInequalityBody.lean:376`、wall body):

```lean
@residual(wall:stam-blachman)
theorem stam_step2_density_wall
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) :
    IsStamCauchySchwarzOptimal X Y P := by sorry
```

`IsStamCauchySchwarzOptimal` (`EPIStamInequalityBody.lean:278`、展開すると本壁の数学的核):

```lean
def IsStamCauchySchwarzOptimal {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
    J_X = (FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
    J_Y = (FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
    J_sum = (FisherInfoV2.fisherInfoOfMeasureV2 (P.map (fun ω => X ω + Y ω)) fXY).toReal →
    FisherInfoV2.IsRegularDensityV2 fX → FisherInfoV2.IsRegularDensityV2 fY →
    (∫ x, fX x ∂volume = 1) → (∫ x, fY x ∂volume = 1) →
    (fXY =ᵐ[volume] EPIConvDensity.convDensityAdd fX fY) →     -- ★ S1 が消費する制約
    J_sum ≤ J_X * J_Y / (J_X + J_Y)
```

密度レベル証明戦略 (pseudo-Lean, ~8 行):

```text
-- S1: fXY =ᵐ convDensityAdd fX fY ⇒ logDeriv fXY = score of conv = E[s_X | X+Y]  (★ 真壁)
--     by convDensityAdd_logDeriv (EPIConvDensity:113) + condExp_ae_eq_integral_condDistrib_id (橋 self-build)
-- S2: ∫ fX'(x)·fY(z-x) = ∫ fX(x)·fY'(z-x)  by integral_mul_deriv_eq_deriv_mul_of_integrable + 併進不変
-- S3: s_Z(z)² ≤ E[(λs_X+(1-λ)s_Y)² | X+Y=z]  by ConvexOn.map_condExp_le (φ = ·²)
-- S4: ∫_z [S3] p_Z dz  → λ²J_X + (1-λ)²J_Y  by integral_integral_swap + integral_condExp + cross-term=0
-- S5: λ = J_Y/(J_X+J_Y) で min = J_X·J_Y/(J_X+J_Y)  by stam_lambda_min (完済)
-- ⇒ J_sum ≤ J_X·J_Y/(J_X+J_Y)
```

---

## API 在庫テーブル

### カテゴリ 1 — 積分の Cauchy-Schwarz / Hölder (条件付き Jensen の明示版)

| 概念 | Mathlib API | file:line | 状態 | 本経路での扱い |
|---|---|---|---|---|
| Bochner Hölder (非負, 共役指数) | `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1237` | ✅ 在 | S3 の代替ルート (p=q=2 で CS) |
| 条件付き Jensen (凸) | `ConvexOn.map_condExp_le` | `Mathlib/MeasureTheory/Function/ConditionalExpectation/CondJensen.lean:168` | ✅ 在 | **S3 第一候補** (`φ = (·)²`) |
| 条件付き分散 ≤ 条件付き二乗 | `ProbabilityTheory.condVar_ae_le_condExp_sq` | `Mathlib/Probability/CondVar.lean:127` | ✅ 在 | S3 バックアップ (`(E[g\|G])² ≤ E[g²\|G]`) |
| `∫⁻` Hölder | `ENNReal.lintegral_mul_le_Lp_mul_Lq` | `Mathlib/MeasureTheory/Integral/MeanInequalities.lean` | ✅ 在 | `J(f)` が `∫⁻` 形なので ENNReal 版も使える |
| 実数有限和 CS | `Real.inner_le_Lp_mul_Lq` | `Mathlib/Analysis/MeanInequalities.lean` | ✅ 在 | 不使用 (連続版で十分) |
| 抽象内積空間 CS `⟪x,y⟫² ≤ ‖x‖²‖y‖²` | `real_inner_mul_inner_self_le` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | ✅ 在 | 不使用 (L² 内積に乗せ替えるコスト > Jensen 直接) |
| `MeasureTheory.integral_mul_le_L2_norm_mul_L2_norm` | — | — | ❌ 不在 (loogle "L2_norm_mul" → Found 0) | 名前直接は無い。Hölder で代替 |
| `MeasureTheory.inner_mul_le_norm_mul_norm` | — | — | ❌ 不在 (loogle "inner_mul_le_norm" → Found 0) | 同上 |

**`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` 逐語 (`Bochner/Basic.lean:1237`)**:

```lean
theorem integral_mul_le_Lp_mul_Lq_of_nonneg {p q : ℝ} (hpq : p.HolderConjugate q) {f g : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal q) μ) :
    ∫ a, f a * g a ∂μ ≤ (∫ a, f a ^ p ∂μ) ^ (1 / p) * (∫ a, g a ^ q ∂μ) ^ (1 / q)
```

- section 型クラス前提 (逐語、`Bochner/Basic.lean` 冒頭): `{α : Type*} [MeasurableSpace α] {μ : Measure α}`
  + `[NormedAddCommGroup E] [NormedSpace ℝ E]` (本補題は `f g : α → ℝ` なので `E` 無関係)。
- 引数: `hpq : p.HolderConjugate q`, `hf_nonneg : 0 ≤ᵐ[μ] f`, `hg_nonneg : 0 ≤ᵐ[μ] g`,
  `hf : MemLp f (ENNReal.ofReal p) μ`, `hg : MemLp g (ENNReal.ofReal q) μ`。
- 結論形 (逐語): `∫ a, f a * g a ∂μ ≤ (∫ a, f a ^ p ∂μ) ^ (1 / p) * (∫ a, g a ^ q ∂μ) ^ (1 / q)`。

**`ConvexOn.map_condExp_le` 逐語 (`CondJensen.lean:168`)**:

```lean
theorem ConvexOn.map_condExp_le (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConvexOn ℝ s φ) (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m]
```

- 型クラス前提 (逐語): `[SigmaFinite (μ.trim hm)]` + section 変数 `{m mα : MeasurableSpace α}`
  `{μ : Measure α}` `{φ : E → ℝ}` `{s : Set E}` `{f : α → E}` (E は Banach、本用途 `E = ℝ`)。
- 引数: `hm : m ≤ mα`, `hφ_cvx : ConvexOn ℝ s φ`, `hφ_cont : LowerSemicontinuousOn φ s`,
  `hf : ∀ᵐ a ∂μ, f a ∈ s`, `hs : IsClosed s`, `hf_int : Integrable f μ`, `hφ_int : Integrable (φ ∘ f) μ`。
- 結論形 (逐語): `φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m]`。

**`condVar_ae_le_condExp_sq` 逐語 (`CondVar.lean:127`)**:

```lean
lemma condVar_ae_le_condExp_sq (hm : m ≤ m₀) [IsFiniteMeasure μ] (hX : MemLp X 2 μ) :
    Var[X; μ | m] ≤ᵐ[μ] μ[X ^ 2 | m]
```

- 型クラス前提 (逐語): `[IsFiniteMeasure μ]` + section `{m m₀ : MeasurableSpace Ω}`。
- 引数: `hm : m ≤ m₀`, `hX : MemLp X 2 μ`。
- 結論形 (逐語): `Var[X; μ | m] ≤ᵐ[μ] μ[X ^ 2 | m]` (= 条件付き Jensen `(μ[X\|m])² ≤ μ[X²\|m]` と同値、
  `condVar_ae_eq_condExp_sq_sub_sq_condExp` 経由)。

### カテゴリ 2 — Tonelli / Fubini (順序交換)

| 概念 | Mathlib API | file:line | 状態 | 本経路での扱い |
|---|---|---|---|---|
| `∫⁻` 順序交換 | `MeasureTheory.lintegral_lintegral_swap` | `Mathlib/MeasureTheory/Measure/Prod.lean:1058` | ✅ 在 | `J(f)` が `∫⁻` 形なので S4 第一候補 |
| Bochner ∫ 順序交換 | `MeasureTheory.integral_integral_swap` | `Mathlib/MeasureTheory/Integral/Prod.lean:532` | ✅ 在 | S4 の実数版 (Bochner score 積分) |
| 可積分性副条件 | `MeasureTheory.Integrable.swap` | `Mathlib/MeasureTheory/Integral/Prod.lean:239` | ✅ 在 | swap の `Integrable (uncurry f) (μ.prod ν)` を供給 |

**`lintegral_lintegral_swap` 逐語 (`Measure/Prod.lean:1058`)**:

```lean
theorem lintegral_lintegral_swap [SFinite μ] ⦃f : α → β → ℝ≥0∞⦄
    (hf : AEMeasurable (uncurry f) (μ.prod ν)) :
    ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫⁻ x, f x y ∂μ ∂ν
```

- 型クラス前提 (逐語): `[SFinite μ]` + section `[MeasurableSpace α] [MeasurableSpace β]`
  `{μ : Measure α} {ν : Measure β}`。**注意: `ν` 側に追加で `[SFinite ν]` が要求される**
  (`lintegral_prod_symm` 経由、section 上流 `variable [SFinite ν]` at `:221`)。`volume` (`ℝ`) は SFinite で充足。
- 引数: `hf : AEMeasurable (uncurry f) (μ.prod ν)` (irreducible binder `⦃⦄`)。
- 結論形 (逐語): `∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫⁻ x, f x y ∂μ ∂ν`。

**`integral_integral_swap` 逐語 (`Integral/Prod.lean:532`)**:

```lean
theorem integral_integral_swap ⦃f : α → β → E⦄ (hf : Integrable (uncurry f) (μ.prod ν)) :
    ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν
```

- 型クラス前提 (逐語): section `{α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]`
  `{μ : Measure α} {ν : Measure β}` + `[NormedAddCommGroup E] [NormedSpace ℝ E]`
  (`Integral/Prod.lean:53-71`)、加えて `[SFinite ν]` (section `:150`/`:229`) + swap が `[SFinite μ]` も要求
  (`Integrable.swap :239`)。両 measure SFinite が要る。`volume × volume` で充足。
- 引数: `hf : Integrable (uncurry f) (μ.prod ν)` (irreducible binder)。
- 結論形 (逐語): `∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν`。

### カテゴリ 3 — 部分積分 / 積分恒等式 (Blachman score 対称化)

| 概念 | Mathlib API | file:line | 状態 | 本経路での扱い |
|---|---|---|---|---|
| 全直線 IBP (improper) | `MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable` | `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:1318` | ✅ 在 | **S2 第一候補** (`∫ u·v' = -∫ u'·v`) |
| 全直線 IBP (deriv 版) | `MeasureTheory.integral_mul_deriv_eq_deriv_mul` | `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean` | ✅ 在 | S2 バックアップ |
| 全直線 deriv·v = sub 形 | `MeasureTheory.integral_deriv_mul_eq_sub` | `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean` | ✅ 在 | S2 別形 |
| 区間 IBP | `intervalIntegral.integral_mul_deriv_eq_deriv_mul` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean` | ✅ 在 | truncation 経由なら使うが全直線版優先 |
| 併進不変 `∫ f(z-x) = ∫ f` | `MeasureTheory.integral_sub_left_eq_self` | `Mathlib/MeasureTheory/Group/Integral.lean` | ✅ 在 (gateway `convDensityAdd_comm` で使用済) | S2 の `z-x` 置換 |
| 畳み込みの導関数対称性 (`deriv_convolution`) | — | — | ❌ 不在 (loogle "deriv_convolution" → Found 0) | gateway `convDensityAddDeriv` (`EPIConvDensity.lean:64`) が自前供給 |
| `lconvolution` の微分可能性 | — | — | ❌ 不在 (loogle "lconvolution"+Differentiable → Found 0) | **本 pivot で回避**: `convDensityAdd` (∫ 形) を gateway で別途微分可能化済 |
| `HasCompactSupport.contDiff_convolution_*` | `HasCompactSupport.contDiff_convolution_right/_left` | `Mathlib/Analysis/Calculus/ContDiff/Convolution.lean` | ✅ 在だが **compact support 要求** | **不適合** (Gaussian heat kernel は非 compact)。gateway が parametric-integral 経路で迂回済 |

**`integral_mul_deriv_eq_deriv_mul_of_integrable` 逐語 (`IntegralEqImproper.lean:1318`)**:

```lean
theorem integral_mul_deriv_eq_deriv_mul_of_integrable
    (hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x)
    (huv' : Integrable (u * v')) (hu'v : Integrable (u' * v)) (huv : Integrable (u * v)) :
    ∫ (x : ℝ), u x * v' x = - ∫ (x : ℝ), u' x * v x
```

- 型クラス前提 (逐語、section): `{A : Type*} [NormedRing A] [NormedAlgebra ℝ A]` + 本体は
  `u v u' v' : ℝ → A`、`A = ℝ` で充足 (`[CompleteSpace A]` は同 section `:1326` で別補題に課される)。
- 引数: `hu`/`hv` (tsupport 上の `HasDerivAt`), `huv'`/`hu'v`/`huv` (3 つの `Integrable`)。
- 結論形 (逐語): `∫ (x : ℝ), u x * v' x = - ∫ (x : ℝ), u' x * v x`。

### カテゴリ 4 — Common2026 内 FisherInfoV2 / score 既存補題

| 概念 | Common2026 API | file:line | 状態 | 本経路での扱い |
|---|---|---|---|---|
| Fisher info (`∫⁻` 形) | `FisherInfoV2.fisherInfoOfDensity (f : ℝ → ℝ) : ℝ≥0∞` | `Common2026/Shannon/FisherInfoV2.lean:89` | ✅ 自前 | `J(f)` の本体。`= ∫⁻ ofReal((logDeriv f x)²)·ofReal(f x) dx` |
| Fisher info (measure 形, phantom μ) | `FisherInfoV2.fisherInfoOfMeasureV2 (_μ) (f) : ℝ≥0∞` | `Common2026/Shannon/FisherInfoV2DeBruijn.lean:77` | ✅ 自前 | `:= fisherInfoOfDensity f` (測度引数は使われない)。wall predicate が参照 |
| 正則密度 predicate | `FisherInfoV2.IsRegularDensityV2 (f : ℝ → ℝ) : Prop` | `Common2026/Shannon/FisherInfoV2.lean:124` | ✅ 自前 (`@audit:ok` 文脈) | regularity precondition (diff/pos/tail/integrable_deriv/integral_deriv=0)。wall hyp |
| score 期待値 = 0 | `FisherInfoV2.integral_logDeriv_density_eq_zero` | `Common2026/Shannon/FisherInfoV2.lean:158` | ✅ 自前 `@audit:ok` | **S4 の cross-term/約分**: `∫ logDeriv f · f = 0` |
| Gaussian closed form | `FisherInfoV2.fisherInfoOfDensity_gaussianPDFReal` | `Common2026/Shannon/FisherInfoV2.lean:273` | ✅ 自前 `@audit:ok` | `= ofReal(1/v)`。saturation 等号確認に使う |
| 畳み込み密度 (∫ 形) | `EPIConvDensity.convDensityAdd (pX pY : ℝ→ℝ)` | `Common2026/Shannon/EPIConvDensity.lean:40` | ✅ 自前 | `:= fun z => ∫ x, pX x · pY (z-x) ∂volume`。wall の `hconv` 制約対象 |
| 畳み込み密度の導関数 | `EPIConvDensity.convDensityAddDeriv` | `Common2026/Shannon/EPIConvDensity.lean:64` | ✅ 自前 | `:= fun z x => pX x · deriv pY (z-x)` |
| **畳み込み密度の微分可能性 (S1 左辺)** | `EPIConvDensity.convDensityAdd_hasDerivAt` | `Common2026/Shannon/EPIConvDensity.lean:86` | ✅ 自前 **`@audit:ok`** | **本 pivot の決定打**。`HasDerivAt (convDensityAdd pX pY) (∫ x, convDensityAddDeriv …) z₀` |
| **畳み込み密度の logDeriv (S1 左辺, score)** | `EPIConvDensity.convDensityAdd_logDeriv` | `Common2026/Shannon/EPIConvDensity.lean:113` | ✅ 自前 **`@audit:ok`** | `logDeriv (convDensityAdd …) z₀ = (∫ x, convDensityAddDeriv …) / convDensityAdd … z₀` |
| score 関数 | `logDeriv (f := deriv f / f)` | `Mathlib/Analysis/Calculus/LogDeriv.lean:34` | ✅ Mathlib | score primitive、上記が消費 |

### カテゴリ 5 — λ 最適化 (完済、Mathlib 不要)

| 概念 | Common2026 API | file:line | 状態 | 本経路での扱い |
|---|---|---|---|---|
| `min_λ λ²a+(1-λ)²b = ab/(a+b)` | `EPIStamInequalityBody.stam_lambda_min` | `Common2026/Shannon/EPIStamInequalityBody.lean:204` | ✅ 自前 `@audit:ok` | **S5 完済** (`field_simp;ring`) |
| `∀λ: ab/(a+b) ≤ λ²a+(1-λ)²b` | `EPIStamInequalityBody.stam_lambda_lower_bound` | `Common2026/Shannon/EPIStamInequalityBody.lean:216` | ✅ 自前 `@audit:ok` | S5 下界 (`(λ-b/(a+b))²(a+b)≥0`) |
| 逆形 Stam 算術 | `EPIStamInequalityBody.stam_inverse_form_of_harmonic_mean` (周辺) | `Common2026/Shannon/EPIStamInequalityBody.lean:232+` | ✅ 自前 `@audit:ok` | `c ≤ ab/(a+b) ⇒ 1/c ≥ 1/a+1/b` |

→ S5 は Mathlib に既製の二次最小値補題を**探す必要なし**。`linarith`/`nlinarith`/`field_simp` で完結済。

### カテゴリ 補 — S1 disintegration 橋の Mathlib 部品 (条件付き表現)

| 概念 | Mathlib API | file:line | 状態 | 本経路での扱い |
|---|---|---|---|---|
| condExp = ∫ condDistrib id | `ProbabilityTheory.condExp_ae_eq_integral_condDistrib_id` | `Mathlib/Probability/Kernel/CondDistrib.lean:438` | ✅ 在 | S1 右辺 `E[s_X\|X+Y=z]` の積分形 |
| total expectation | `MeasureTheory.integral_condExp` | `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean` | ✅ 在 | S4 の `∫ μ[f\|m] = ∫ f` |
| 条件付き分布 kernel | `ProbabilityTheory.condDistrib` | `Mathlib/Probability/Kernel/CondDistrib.lean:64` | ✅ 在 | S1 の `condDistrib id (X+Y) P` |
| **Blachman score-of-convolution 恒等式** | — | — | ❌ **不在** (`Blachman`/`Stam`/`fisherInformation`/`fisherInfo` 全 loogle `Found 0`) | S1 の橋本体 = self-build |

**`condExp_ae_eq_integral_condDistrib_id` 逐語 (`CondDistrib.lean:438`)**:

```lean
theorem condExp_ae_eq_integral_condDistrib_id [NormedSpace ℝ F] [CompleteSpace F] {X : Ω → β}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hX : Measurable X) {f : Ω → F} (hf_int : Integrable f μ) :
    μ[f | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f y ∂condDistrib id X μ (X a)
```

- 型クラス前提 (逐語): `[NormedSpace ℝ F] [CompleteSpace F]` + section `[IsFiniteMeasure μ]` +
  `{β : Type*} {mβ : MeasurableSpace β}` (β は **`[StandardBorelSpace β]` を `condDistrib` 経由で要求** —
  下記前提ボックス参照) + `{F : Type*} [NormedAddCommGroup F]`。
- 引数: `hX : Measurable X`, `hf_int : Integrable f μ`。
- 結論形 (逐語): `μ[f | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f y ∂condDistrib id X μ (X a)`。

---

## 主要前提条件ボックス (前提事故注意)

- **`condExp_ae_eq_integral_condDistrib_id` (`CondDistrib.lean:438`) — S1 橋で使うなら `[StandardBorelSpace]`
  が漏れる**:
  - `condDistrib` は出力側 codomain (= ここでは `f` の値域 `F` / 条件付け側 `β`) に `[StandardBorelSpace _]`
    を要求 (`CondDistrib.lean:64` section)。`X+Y : Ω → ℝ` を条件にすると `β = ℝ` で StandardBorel は自動成立
    (`ℝ` は標準 Borel)。ただし **score `s_X : ℝ → ℝ` の値域・可積分性 (`Integrable f μ`)** が新前提として漏れる。
  - `[IsFiniteMeasure μ]` は `[IsProbabilityMeasure P]` で充足。

- **`ConvexOn.map_condExp_le` (`CondJensen.lean:168`) — S3 の前提**:
  - `[SigmaFinite (μ.trim hm)]` (確率測度の trim は SigmaFinite で充足)。
  - `hf : ∀ᵐ a ∂μ, f a ∈ s` (score が凸関数 domain に入る、`φ = (·)²` なら `s = univ` で自明)。
  - `hf_int : Integrable f μ` **かつ** `hφ_int : Integrable (φ ∘ f) μ` — **score の L² 可積分性**が前提。
    Gaussian では OK、重テール密度で破れる (= regularity precondition、`IsRegularDensityV2` から導く必要)。

- **`integral_integral_swap` / `lintegral_lintegral_swap` (S4) — 両 measure SFinite + 可積分性**:
  - `volume × volume` (`ℝ × ℝ`) は両側 SFinite で充足、漏れなし。
  - swap の本前提 `Integrable (uncurry f) (volume.prod volume)` (resp. `AEMeasurable`) — 2 変数被積分関数
    `(z,x) ↦ s_Z(z)·(…)·p_Z(z)` の **積測度上可積分性** が self-build 副条件 (Tonelli の非負性で `∫⁻` 版なら
    可積分性不要 = `lintegral_lintegral_swap` を優先する理由)。

- **`integral_mul_deriv_eq_deriv_mul_of_integrable` (`IntegralEqImproper.lean:1318`) — S2 IBP の前提**:
  - `hu`/`hv`: tsupport 上の `HasDerivAt` (密度の微分可能性、`IsRegularDensityV2.diff` から)。
  - 3 つの `Integrable (u*v')` / `(u'*v)` / `(u*v)` — score × 密度積の可積分性 (regularity precondition)。

- **`fisherInfoOfDensity` が `∫⁻` (ENNReal) 形 — S3/S4 の Bochner ∫ との往復が必要**:
  - `J(f) = (∫⁻ ofReal((logDeriv f)²·f)).toReal`。条件付き Jensen / Tonelli は `∫⁻` 版 (`lintegral_*`) を
    直接使えば `.toReal` 変換を最小化できる。実数 Bochner CS (`integral_mul_le_Lp_mul_Lq_of_nonneg`) を使うと
    `ofReal_integral_eq_lintegral_ofReal` (`Bochner/Basic.lean`) で往復 (非負性 + 可積分性が前提)。
    **`∫⁻` ルートに揃えるのが事故が少ない** (Mathlib-shape-driven、`J` の定義が `∫⁻` なので)。

---

## 自作が必要な要素 (優先度順)

1. **[支配項・真壁] S1 Blachman 条件付き score 表現の disintegration 橋**
   `logDeriv (convDensityAdd fX fY) z = E[s_X(X) | X+Y=z]` を `convDensityAdd_logDeriv`
   (`EPIConvDensity.lean:113`、左辺供給済) + `condExp_ae_eq_integral_condDistrib_id`
   (`CondDistrib.lean:438`、右辺 condExp 積分形) で結ぶ。
   - 推奨実装: 新規 `Common2026/Shannon/EPIBlachmanConvScore.lean`。`convDensityAdd_logDeriv` の
     `(∫ x, fX x · fY'(z-x)) / p_Z(z)` を、`p_Z(z) = ∫ fX(x)fY(z-x)dx` で割った重み付き積分を
     `condDistrib id (X+Y) P` の積分に同定 (disintegration / pushforward 計算)。
   - 工数: ~80-150 行。**落とし穴**: `[StandardBorelSpace]` 前提漏れ (上記ボックス)、`Integrable f μ` の
     score 可積分性、a.e. 等式と点ごと値の往復。Mathlib に `condExp ∧ convolution` 同時補題が皆無
     (loogle `Found 0`) なので橋は概念ごと自前。**親計画 L-EPIW-3-α 発火想定箇所**。

2. **[部分在] S2 Blachman 積分恒等式 (score 対称化)**
   `∫ fX'(x)·fY(z-x)dx = ∫ fX(x)·fY'(z-x)dx`。`integral_mul_deriv_eq_deriv_mul_of_integrable`
   (`IntegralEqImproper.lean:1318`) + 併進不変 `integral_sub_left_eq_self` で。cross-term=0 は
   Phase 2 `score_cross_term_eq_zero` (`epi-wall-reattack-plan.md:440`、別 file) 依存。
   - 工数: ~40-80 行。前提に #1 不要 (独立着手可)、Phase 2 完了が望ましい。

3. **[在] S3 条件付き Jensen 適用** `ConvexOn.map_condExp_le` を `φ = (·)²` で適用。score の L²
   可積分性 (`hφ_int`) を `IsRegularDensityV2` から導く plumbing。工数: ~30-60 行。前提に #1。

4. **[在] S4 Tonelli + total expectation + 約分** `lintegral_lintegral_swap` (`∫⁻` 版優先) +
   `integral_condExp` + `integral_logDeriv_density_eq_zero` (`FisherInfoV2.lean:158`) で
   `λ²J_X+(1-λ)²J_Y` に収束。`∫⁻`↔Bochner 往復の plumbing。工数: ~50-100 行。前提に #1,#2,#3。

5. **[完済] S5 λ 最適化** `stam_lambda_min` / `stam_lambda_lower_bound` で 0 行 (既存呼出のみ)。

合計 self-build 見積: **~200-390 行** (S1 が支配項 ~80-150 行、`@residual` 据置リスク最大)。

---

## Mathlib 壁の列挙 (真の不在、`@residual(wall:...)` 対象)

| 壁 | loogle 確認 | shared sorry 補題化 |
|---|---|---|
| Blachman score-of-convolution 恒等式 (S1 の核) | `"Blachman"` → **Found 0** | **`stam_step2_density_wall` (`EPIStamInequalityBody.lean:376`, `@residual(wall:stam-blachman)`) に集約済 (推奨維持)**。S2-S5 を ship しても S1 が closure できなければ同 wall の `sorry` に残す |
| Stam 不等式 (Mathlib 側) | `"_Stam"` → **Found 0** | 同上 wall に集約 |
| Fisher information (Mathlib 側定義) | `"fisherInformation"` → Found 0, `"fisherInfo"`(前任) → unknown identifier | Common2026 自前 `fisherInfoOfDensity` で代替 (壁ではない) |
| 畳み込みの導関数 (`deriv_convolution`) | `"deriv_convolution"` → **Found 0** | gateway `convDensityAddDeriv`/`convDensityAdd_hasDerivAt` で**回避済** (壁ではない) |
| `lconvolution` 微分可能性 | `"lconvolution"`+`Differentiable` → **Found 0** | `convDensityAdd` (∫ 形) を gateway で別途微分可能化済、本経路で**回避** (壁ではない) |
| `condExp ∧ convolution density` 同時補題 | `condExp`(171 lemmas) / `condDistrib`(51 lemmas) は在だが convolution 密度と結ぶ hook 不在 | S1 self-build に内包 (`wall:stam-blachman` に集約) |

**唯一の真壁 = `wall:stam-blachman` (S1 disintegration 橋)。** 既に `stam_step2_density_wall` 1 本の
`sorry` に集約されており (shared sorry 補題パターン、`docs/audit/audit-tags.md`「共有 Mathlib 壁」)、
S2-S5 を独立 file で ship しても**この集約を維持**するのが honesty 規律 (S1 を `Is...Hyp` predicate に
bundle するのは tier 5 load-bearing で禁止 — `epi-wall-reattack-plan.md:498`)。

---

## 撤退ラインへの距離

親計画 [`epi-wall-reattack-plan.md`](epi-wall-reattack-plan.md) Phase 3 の撤退ライン:

- **L-EPIW-3-α**: Blachman 条件付き score 表現 (S1) の disintegration self-build が PR 級
  → `stam_step2_density_wall` body `sorry` + `@residual(wall:stam-blachman)` 据置 (regularity hyp 維持)。
- **L-EPIW-3-β**: λ 最適化 (S5) の algebraic transform が `linarith` 吸収不可で >50 行
  → step 4 のみ `sorry`、step 1-3 ship。

**判定: L-EPIW-3-α は本経路でも発動見込み (確率高)。** S1 の disintegration 橋が本調査の真壁。ただし
**前任 inventory の「`⋆ₗ` 微分可能性 PR 級壁」は本経路で解消済**なので、撤退ラインの位置は L-EPIW-3-α
**1 本に縮小** (前任は微分可能性 + Blachman 橋の 2 重壁だった)。L-EPIW-3-β は発動せず (S5 完済確認、
`stam_lambda_min` `@audit:ok`)。

**新規撤退ライン提案 (本経路着手時)**:
- **L-EPIW-3-密度-α** (L-EPIW-3-α の精緻化): S1 橋で `condExp_ae_eq_integral_condDistrib_id` の
  `[StandardBorelSpace]` / score `Integrable f μ` 前提が `IsStamCauchySchwarzOptimal` signature に
  漏れ qualitatively 後退する場合 → S2-S5 (Mathlib 部品揃いパート) を独立 file
  `EPIBlachmanConvScore.lean` に genuine ship し、S1 のみ `stam_step2_density_wall` の `sorry` +
  `@residual(wall:stam-blachman)` に据置 (現状形を維持、撤退口 = sorry、仮説束化禁止)。
- 縮退案: smoothed/Gaussian-mollified 密度クラスに限定した `IsStamCauchySchwarzOptimalSmooth` を別 def
  として publish し、general density は撤退 (sorry なし、足場のみ)。ただし signature pivot 級なので
  owner-level 判断 (本 inventory は提案のみ)。

---

## 着手 skeleton

`Common2026/Shannon/EPIBlachmanConvScore.lean` (新規) の出だし。
**注意: 本ファイルは inventory 専用。以下は実装サブエージェント向け参考であり、本調査では一切実装しない。**

```lean
import Common2026.Shannon.EPIConvDensity          -- convDensityAdd_logDeriv (S1 左辺)
import Common2026.Shannon.FisherInfoV2            -- fisherInfoOfDensity / IsRegularDensityV2 / integral_logDeriv_density_eq_zero
import Mathlib.Probability.Kernel.CondDistrib     -- condExp_ae_eq_integral_condDistrib_id (S1 右辺)
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen  -- ConvexOn.map_condExp_le (S3)
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic       -- integral_condExp (S4)
import Mathlib.MeasureTheory.Measure.Prod         -- lintegral_lintegral_swap (S4)
import Mathlib.MeasureTheory.Integral.IntegralEqImproper  -- integral_mul_deriv_eq_deriv_mul_of_integrable (S2)

/-!
# Blachman density-route: explicit-integral path toward `stam_step2_density_wall`

別経路 (抽象 condDistrib 回避): `convDensityAdd pX pY z := ∫ x, pX x · pY (z-x) ∂volume`
を出発点に、S1 (Blachman 条件付き score 表現) のみ真壁 (`wall:stam-blachman`)、S2-S5 は
Mathlib 部品揃い。S1 = `convDensityAdd_logDeriv` (EPIConvDensity:113) と
`condExp_ae_eq_integral_condDistrib_id` (CondDistrib:438) を結ぶ disintegration 橋 (self-build)。
-/

namespace InformationTheory.Shannon.EPIBlachmanConvScore

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **[S1 真壁] Blachman score-of-convolution representation.**
`logDeriv (convDensityAdd fX fY) z = E[s_X(X) | X+Y=z]`. 左辺は
`EPIConvDensity.convDensityAdd_logDeriv` で `(∫ fX·fY'(z-·))/p_Z` に展開済。右辺 condExp 積分形を
`condExp_ae_eq_integral_condDistrib_id` で書き、両者を disintegration で同定する橋が Mathlib 不在。
詰まれば `sorry` + `@residual(wall:stam-blachman)` (shared wall に集約、predicate bundle 禁止)。 -/
theorem blachman_score_eq_condExp
    {X Y : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {fX fY : ℝ → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hregX : Common2026.Shannon.FisherInfoV2.IsRegularDensityV2 fX)
    (hregY : Common2026.Shannon.FisherInfoV2.IsRegularDensityV2 fY) :
    True := by   -- 真の結論型は disintegration 橋確定後に固定 (skeleton placeholder)
  sorry  -- @residual(wall:stam-blachman)

end InformationTheory.Shannon.EPIBlachmanConvScore
```

最初に `blachman_score_eq_condExp` (S1) に着手。詰まれば L-EPIW-3-密度-α へ撤退し、S2-S5 を genuine ship。
