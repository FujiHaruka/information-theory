# condExp-of-score (Stam Step 1-2) discharge — Mathlib feasibility inventory

> Frontier-gap feasibility scan (2026-05-20). Target: discharge the two pass-through
> predicates `IsStamScoreConvHyp` + `IsStamCondExpCSHyp` in
> `Common2026/Shannon/EPIStamStep12Body.lean` (L-S12-C, currently 未採用) to 0-sorry.
>
> Sibling docs: [`shannon-mathlib-inventory.md`](shannon-mathlib-inventory.md),
> roadmap [`../textbook-roadmap.md`](../textbook-roadmap.md) (line 710/719 names this gap).

## 一行サマリ

**「condExp の measure-theoretic 道具は予想外に揃っている」(conditional Jensen + condDistrib↔condExp + Measure.conv + rnDeriv-of-conv はすべて Mathlib 既存)。だが本タスクは見かけより 2 段ねじれている**: (1) 既存 pass-through 述語 `IsStamScoreConvHyp`/`IsStamCondExpCSHyp` は **measure-theoretic 恒等式を全く消費していない**(`fisherInfo` の `toReal` 実数だけを運ぶ純算術 Prop)。(2) その `fisherInfo` 接続は V1(`Classical.choose` で a.e. 退化、Gaussian で `0`)であり、**V2 `fisherInfoOfDensity`(密度引数形)とは別の measure に紐付かない関数**。本物の `s_Z = E[s_X | X+Y=z]` 恒átを 0-sorry で割るには **「fisherInfo を joint law / pdf に接続する基盤」を一から作る必要があり、これ自体が Mathlib に皆無**。**核心 1 ピース欠落**: 「`E[s_X(X) s_Y(Y)] = 0`(独立 + mean-zero score の cross-term orthogonality)」を与える補題が Mathlib に `Found 0`(condExp ∧ IndepFun を同時に言う lemma が一つも無い)。

既存率(本物の恒等式を割るのに必要な API):**部品 ~70% 既存 / 接着剤と score↔pdf↔fisherInfo 橋は 0% 既存**。自作必要 5 件。**撤退ライン: 発動(GO は scope を Gaussian/closed-form に縮退した時のみ。一般 X,Y の measure-theoretic full discharge は 1 セッション不可)。**

---

## 主定理の最終形(再掲)

割り対象は **2 つの pass-through 述語**(`EPIStamStep12Body.lean:164` / `:214`):

```lean
-- EPIStamStep12Body.lean:164  (Step 1, 現状: 純算術で trivial 可)
def IsStamScoreConvHyp (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ (J_X J_Y : ℝ), 0 < J_X → 0 < J_Y →
    J_X = (Common2026.Shannon.fisherInfo (P.map X)).toReal →
    J_Y = (Common2026.Shannon.fisherInfo (P.map Y)).toReal →
    ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ lam = J_Y / (J_X + J_Y)

-- EPIStamStep12Body.lean:214  (Step 2, 現状: vacuous Gaussian or pass-through)
def IsStamCondExpCSHyp (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ (J_X J_Y J_sum : ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
    J_X    = (fisherInfo (P.map X)).toReal →
    J_Y    = (fisherInfo (P.map Y)).toReal →
    J_sum  = (fisherInfo (P.map (fun ω => X ω + Y ω))).toReal →
    ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
      J_sum ≤ lam^2 * J_X + (1 - lam)^2 * J_Y
```

**重要観察**: `IsStamScoreConvHyp` は既に `isStamScoreConvHyp_intro`(`:175`)で**無条件に証明済み**(witness `J_Y/(J_X+J_Y) ∈ [0,1]` の純算術)。本物の measure-theoretic 内容を一切持たない。`IsStamCondExpCSHyp` だけが genuine な不等式 `J_sum ≤ λ²J_X + (1-λ)²J_Y` を運ぶが、これも `fisherInfo` の `.toReal` だけで、`s_Z = E[s_X|Z]` 恒等式は signature に登場しない。

数学的核心(これを割って `IsStamCondExpCSHyp` を導く場合に必要な pseudo-Lean):

```lean
-- 本物の Blachman/Stam path (約 6-10 行の戦略):
-- 1. Z := X+Y; sub-σ = MeasurableSpace.comap Z;  s_X := logDeriv p_X ∘ X
-- 2. score-conv:  P[fun ω => s_X (X ω) | comap Z] =ᵐ s_Z ∘ Z      ← (要 Blachman, 自作)
-- 3. cond-Jensen: (P[g | comap Z])^2 ≤ᵐ P[g^2 | comap Z]          ← ConvexOn.map_condExp_le
--    with  g = λ·(s_X∘X) + (1-λ)·(s_Y∘Y),  φ = (·)^2
-- 4. integral_condExp: ∫ P[g^2|comap Z] dP = ∫ g^2 dP
-- 5. expand g^2, drop cross-term 2λ(1-λ)·E[s_X(X) s_Y(Y)] = 0      ← (cross-orth, Mathlib 不在)
-- 6. ∫ (s_X∘X)^2 dP = J_X  (要 fisherInfo↔pdf 橋, 自作),  similarly J_Y, J_sum
-- ⟹  J_sum ≤ λ² J_X + (1-λ)² J_Y
```

ステップ 2, 5, 6 が Mathlib 不在の自作項。3, 4 は Mathlib 既存。

---

## API 在庫テーブル

### A. 条件付き期待値 `MeasureTheory.condExp` — 道具は揃っている(✅ 多数)

| 概念 | Mathlib API | file:line | 状態 | discharge での扱い |
|---|---|---|---|---|
| **条件付き Jensen** `φ(E[f\|m]) ≤ E[φ∘f\|m]` | `ConvexOn.map_condExp_le` | `Mathlib/MeasureTheory/Function/ConditionalExpectation/CondJensen.lean:168` | ✅ 既存 | **Step 2 の核**。`φ = (·)^2` で `(E[g\|m])² ≤ E[g²\|m]` を直接供給 |
| 条件付き Jensen(univ 版) | `ConvexOn.map_condExp_le_univ` | `CondJensen.lean:195` | ✅ 既存 | `s = univ` 簡略版。`(·)²` は `convexOn_univ` なのでこちら推奨 |
| 条件付き Jensen(有限次元版) | `ConvexOn.map_condExp_le_of_finiteDimensional` | `CondJensen.lean:227` | ✅ 既存 | `[FiniteDimensional ℝ E]` 要求。ℝ なので適用可、LSC 仮定不要で最も軽い |
| **total expectation** `∫ E[f\|m] = ∫ f` | `MeasureTheory.integral_condExp` | `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean:228` | ✅ 既存 | Step 4(条件付き不等式を積分)の核 |
| condExp tower `E[E[f\|m₂]\|m₁]=E[f\|m₁]` | `MeasureTheory.condExp_condExp_of_le` | `Basic.lean:336` | ✅ 既存 | score-conv の整合性に副次的に必要かも |
| condExp 線形性 | `MeasureTheory.condExp_add` | `Basic.lean`(loogle 確認) | ✅ 既存 | `g = λsX+(1-λ)sY` の分解 |
| condExp_smul | `MeasureTheory.condExp_smul`(同モジュール) | `Basic.lean` | ✅ 既存 | 同上 |

**`ConvexOn.map_condExp_le` 完全 signature(逐語)**:
```lean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {α : Type*} {f : α → E} {φ : E → ℝ} {m mα : MeasurableSpace α} {μ : Measure α} {s : Set E}
theorem ConvexOn.map_condExp_le (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConvexOn ℝ s φ) (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m]
```
**`integral_condExp` 完全 signature(逐語)**:
```lean
theorem integral_condExp (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] :
    ∫ x, (μ[f | m]) x ∂μ = ∫ x, f x ∂μ
```
**`condExp_condExp_of_le` 完全 signature(逐語)**:
```lean
theorem condExp_condExp_of_le {m₁ m₂ m₀ : MeasurableSpace α} {μ : Measure α} (hm₁₂ : m₁ ≤ m₂)
    (hm₂ : m₂ ≤ m₀) [SigmaFinite (μ.trim hm₂)] : μ[μ[f | m₂] | m₁] =ᵐ[μ] μ[f | m₁]
```

### B. condExp ↔ condDistrib(disintegration による条件付き期待値の積分表現)— ✅ 既存

| 概念 | Mathlib API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| **condExp = ∫ ∂condDistrib** | `ProbabilityTheory.condExp_ae_eq_integral_condDistrib` | `Mathlib/Probability/Kernel/CondDistrib.lean:381` | ✅ 既存 | sub-σ-algebra `mβ.comap X` 上の condExp を kernel 積分に変換。score-conv の RHS 表現 |
| condExp = ∫ id ∂condDistrib | `condExp_ae_eq_integral_condDistrib'` | `CondDistrib.lean:389` | ✅ 既存 | `Y` 自身の condExp 版 |
| condExp = ∫ id ∂condDistrib(id 形) | `condExp_ae_eq_integral_condDistrib_id` | `CondDistrib.lean:438` | ✅ 既存 | 補助 |
| condDistrib = condExp(指示関数) | `ProbabilityTheory.condDistrib_ae_eq_condExp` | `CondDistrib.lean:321` | ✅ 既存 | 補助 |
| condDistrib 定義(51 lemma 群) | `ProbabilityTheory.condDistrib` | `CondDistrib.lean:64`(shannon-inv 既出) | ✅ 既存 | sub-σ 生成の起点 |

**`condExp_ae_eq_integral_condDistrib` 完全 signature(逐語、`[...]` 前提含む)**:
```lean
variable {α β Ω F : Type*} [MeasurableSpace α] {μ : Measure α} ...
  [NormedAddCommGroup F] {X : α → β} {Y : α → Ω} [MeasurableSpace β]
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] ...   -- (CondDistrib 全体 prereq)
theorem condExp_ae_eq_integral_condDistrib [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ) {f : Ω → F} (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun a => f (Y a)) μ) :
    μ[fun a => f (Y a) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f y ∂condDistrib Y X μ (X a)
```
**⚠ 前提事故注意(下記ボックス参照)**: `condDistrib` 系は `[StandardBorelSpace Ω]` `[Nonempty Ω]` `[IsFiniteMeasure μ]` を要求。`Ω = ℝ` なら `StandardBorelSpace` は inferrable だが、measure には `IsFiniteMeasure`(= probability で OK)が要る。

### C. 測度の畳み込み `Measure.conv` / 畳み込み密度 — ✅ 部品あり、形が合わない(⚠)

| 概念 | Mathlib API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| 加法畳み込み `μ ∗ ν` | `MeasureTheory.Measure.conv`(`mconv` の `to_additive`) | `Mathlib/MeasureTheory/Group/Convolution.lean:35`(`mconv` def, additive `∗` notation `:42`) | ✅ 既存 | `P.map (X+Y) = (P.map X) ∗ (P.map Y)`(独立時)の表現候補 |
| 畳み込み density = density の畳み込み | `MeasureTheory.rnDeriv_conv`(`rnDeriv_mconv` の `to_additive`) | `Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean:653`(`rnDeriv_mconv`) | ✅ 既存(⚠形) | `(μ₁∗μ₂).rnDeriv ≈ rnDeriv₁ ⋆ₗ rnDeriv₂`。**結論が `mlconvolution ⋆ₗ` で pointwise score を直接出さない** |
| Gaussian ∗ Gaussian | `ProbabilityTheory.gaussianReal_conv_gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean`(loogle 確認) | ✅ 既存 | **Gaussian 限定 closed-form の決め手**(scope 縮退時) |
| 独立和の law = conv | (`indepFun → map prod` 経由で導出) | — | ⚠ 組立 | `Measure.conv` 定義 `map (·+·) (μ.prod ν)` と `indepFun_iff_map_prod_eq_prod_map_map` を繋ぐ |
| 独立和の **pdf** = pdf の畳み込み | `MeasureTheory.Measure.conv` ∧ `MeasureTheory.pdf` | — | ❌ **不在**(loogle `Found 0`) | `pdf` レベルの畳み込み公式は無い |

**`rnDeriv_mconv` 完全 signature(逐語)**:
```lean
variable {G : Type*} [MeasurableSpace G] {μ : Measure G} ...   -- (group prereq)
theorem rnDeriv_mconv [SFinite μ] {ν₁ ν₂ : Measure G} [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    [ν₁.HaveLebesgueDecomposition μ] [ν₂.HaveLebesgueDecomposition μ]
    (hν₁ : ν₁ ≪ μ) (hν₂ : ν₂ ≪ μ) :
    (ν₁ ∗ₘ ν₂).rnDeriv μ =ᵐ[μ] (ν₁.rnDeriv μ) ⋆ₘₗ[μ] (ν₂.rnDeriv μ)
```
**`Measure.conv` 定義(逐語、`mconv` の additive)**:
```lean
noncomputable def mconv (μ : Measure M) (ν : Measure M) : Measure M :=
    Measure.map (fun x : M × M ↦ x.1 * x.2) (μ.prod ν)   -- 加法版は (·+·)
```

### D. score-of-convolution / Stam / Blachman / Fisher information(本体)— ❌ ほぼ皆無

| 概念 | Mathlib API | 状態 | 検証 |
|---|---|---|---|
| Fisher information(named) | `fisherInformation` | ❌ **不在** | loogle `unknown identifier 'fisherInformation'` |
| Stam inequality | (なし) | ❌ **不在** | `EPIStamInequalityBody.lean:42` 既述 `rg "Stam\|Blachman" → 0` |
| Blachman score-of-convolution | (なし) | ❌ **不在** | 同上 |
| **`logDeriv` of convolution** | `logDeriv (_ ⋆ _)` | ❌ **不在** | loogle 構文エラー → 概念として無し |
| **score cross-term orthogonality** `E[s_X(X)·s_Y(Y)]=0` | `condExp` ∧ `IndepFun` を同時に言う lemma | ❌ **不在(致命)** | **loogle `Found 0 declarations mentioning MeasureTheory.condExp and ProbabilityTheory.IndepFun`** |
| condExp of independent var(`E[f(X)\|σ(Y)]=E[f(X)]`) | `condExp_indepFun` 系 | ❌ **不在** | loogle `unknown identifier 'condExp_indepFun'` / `'condExp_indep'` |
| `logDeriv` of density(score) | `logDeriv` | ✅ 既存 | `Mathlib/Analysis/Calculus/LogDeriv.lean:34`(`logDeriv f = deriv f / f`)。score の素材は有る |

### E. 既存 Common2026 足場 — 述語は本物の恒等式を**消費していない**(⚠ 接続なし)

| 概念 | 場所 file:line | 状態 | discharge での意味 |
|---|---|---|---|
| `IsStamScoreConvHyp`(Step 1 述語) | `EPIStamStep12Body.lean:164` | ✅ 既に無条件証明済(`isStamScoreConvHyp_intro:175`) | **measure-theoretic 内容ゼロ**。割る必要すら無い(純算術 witness) |
| `IsStamCondExpCSHyp`(Step 2 述語) | `EPIStamStep12Body.lean:214` | ⚠ pass-through(Gaussian vacuous or 仮定) | genuine な `J_sum ≤ λ²J_X+(1-λ)²J_Y` を運ぶ。**だが `fisherInfo.toReal` 実数のみで `s_Z=E[s_X\|Z]` 不在** |
| 純算術 Cauchy-Schwarz `(λsX+(1-λ)sY)² ≤ λsX²+(1-λ)sY²` | `stam_convex_cs` `EPIStamStep12Body.lean:120` | ✅ 既証明(`nlinarith`) | pointwise CS は完備。**積分への持ち上げが欠落** |
| 2-point Jensen `(E)²≤E(²)` | `stam_jensen_sq_le:130` | ✅ 既証明 | 離散版完備 |
| Step 4 λ最適化閉形式 | `stam_lambda_min`(EPIStamDischarge) | ✅ 既証明 | `IsStamCondExpCSHyp ⟹ optimal` は `stamCauchySchwarzOptimal_of_condExpCSHyp:262` で完了 |
| **fisherInfo V1**(Classical.choose) | `FisherInfo.lean:58` | ⚠ 退化 | `gaussianReal` で a.e. 非微分 → `fisherInfo = 0`(`FisherInfoV2.lean:24-29` 既述)。**実数値が間違う** |
| **fisherInfoOfDensity V2**(密度引数) | `FisherInfoV2.lean:88` | ✅ 正しい | `∫⁻ (logDeriv f)²·f`。**だが measure / pdf に紐付かない純関数**。`P.map X` との橋無し |
| V2 Gaussian closed form `= 1/v` | `fisherInfoOfDensity_gaussianPDFReal` `FisherInfoV2.lean:296` | ✅ 既証明 | Gaussian 限定 scope なら decisive |
| Step3 total-expectation 述語 | `IsStamTotalExpectation` `EPIStamStep3Body.lean:152` | ⚠ pass-through | 同型(`fisherInfo.toReal` のみ)。同じねじれ |

**消費形(下流が要求する signature)**: `IsStamCondExpCSHyp` を満たせば `stamCauchySchwarzOptimal_of_condExpCSHyp`(`:262`)→ `isStamInequalityHyp_of_step12`(`:292`)→ published `IsStamInequalityHyp` まで**既に繋がっている**。つまり下流は **`∀λ, J_sum ≤ λ²J_X+(1-λ)²J_Y`(実数不等式)だけ**を要求し、measure-theoretic 恒等式を要求しない。**割るべきは「この実数不等式を本物の積分から導く」部分のみ**だが、それには `fisherInfo.toReal = ∫ score² dP` という橋が前提となり、その橋自体が `fisherInfo` V1 の退化で**現状破綻している**。

---

## 主要前提条件ボックス(前提事故の起きやすい lemma)

- **`condExp_ae_eq_integral_condDistrib`(B 群)**: 全体に `[StandardBorelSpace Ω]` `[Nonempty Ω]` `[IsFiniteMeasure μ]`(CondDistrib モジュール変数)。`Ω=ℝ` は OK、`μ=P` は probability で OK。だが **`hX : Measurable X`(`X+Y`), `hY : AEMeasurable (s_X∘X)`** が要り、`s_X = logDeriv p_X` の可測性は `p_X` の正則性に依存 → 追加 regularity 仮定。
- **`ConvexOn.map_condExp_le`(A 群)**: `[SigmaFinite (μ.trim hm)]` + **`hf_int : Integrable g μ`** + **`hφ_int : Integrable (g²) μ`**。`g = λsX+(1-λ)sY` と `g²` の**両方の可積分性**を要する。`g²` 可積分 ⇔ score の L² 可積分 ⇔ Fisher info 有限。**`J < ∞` の追加仮定が必須**。`finiteDimensional` 版なら LSC 仮定は不要で最軽量。
- **`integral_condExp`**: `[SigmaFinite (μ.trim hm)]` のみ。sub-σ `comap (X+Y)` の trim が σ-finite であること(probability なら OK)。
- **`rnDeriv_mconv`(C 群)**: `[SFinite μ]` `[IsFiniteMeasure ν₁]` `[IsFiniteMeasure ν₂]` + `[HaveLebesgueDecomposition]` + `ν₁ ≪ μ`, `ν₂ ≪ μ`(両法則が Lebesgue 絶対連続)。結論が `⋆ₗ`(`mlconvolution`)で**pointwise 値を出すには更に積分公式が要る**。
- **cross-term orthogonality(D 群、❌不在)**: `E[s_X(X)·s_Y(Y)] = E[s_X(X)]·E[s_Y(Y)] = 0` は独立(`IndepFun.integral_mul`)+ mean-zero score(`FisherInfoV2.integral_logDeriv_density_eq_zero:155` 既存!)から組めるが、**「σ(X+Y) 上の condExp の cross-term」へ持ち上げる lemma が無い**。`IndepFun.integral_mul` 自体は存在するので、**全期待値レベルなら自作可能**(条件付きレベルは不要 — Step 4 で全積分するため)。

---

## 自作が必要な要素(優先度順)

1. **【最優先・橋】`fisherInfo.toReal = ∫ (logDeriv pdf ∘ X)² dP`** — 述語 `IsStamCondExpCSHyp` の `J_X = fisherInfo(P.map X).toReal` を本物の積分に接続。**現状 V1 fisherInfo が `gaussianReal` で `0` に退化しており、この橋は V1 では偽**。V2 `fisherInfoOfDensity` を `P.map X` の pdf に紐付ける新 lemma + 述語の `fisherInfo` を V2 系に張り替える必要。**工数 50-100 行 + 述語定義の pivot**(下流 chain への影響波及)。落とし穴: V1/V2 二重定義の整合。
2. **【核】score-of-convolution 恒等式 `P[s_X∘X | comap(X+Y)] =ᵐ s_Z∘(X+Y)`**(Blachman)— heat-kernel / Fubini で `s_Z(z) = ∫ s_X(x) p(x|z) dx`。`condExp_ae_eq_integral_condDistrib`(B)で枠は出るが、`s_Z` が `logDeriv` of convolution density である事実(D で不在)を別途証明要。**工数 100-200 行、regularity(滑らかさ・tail vanishing・L² score)を多数追加**。Mathlib PR 級。
3. **【中】cross-term orthogonality(全期待値版)`∫ (s_X∘X)(s_Y∘Y) dP = 0`** — `IndepFun.integral_mul`(既存)+ `integral_logDeriv_density_eq_zero`(`FisherInfoV2.lean:155` 既存)。**部品は揃う**。工数 20-40 行。落とし穴: `IndepFun (s_X∘X) (s_Y∘Y)`(`IndepFun.comp` 経由)+ 可積分性。
4. **【中】L² → 積分持ち上げ** — pointwise `stam_convex_cs`(既存)を `ConvexOn.map_condExp_le` + `integral_condExp` で `J_sum ≤ λ²J_X+(1-λ)²J_Y` に。**A 群が直接効く**。工数 40-80 行(可積分性 side-goal が主)。
5. **【低】Gaussian closed-form 経路(scope 縮退時)** — `gaussianReal_conv_gaussianReal`(C)+ `fisherInfoOfDensity_gaussianPDFReal:296`(`=1/v` 既存)で `J_sum = 1/(v₁+v₂)` を直接計算し、`1/(v₁+v₂) ≤ λ²/v₁+(1-λ)²/v₂` を `nlinarith`。**measure-theoretic 恒等式を完全回避**。工数 30-60 行。**1 セッション可能**。

---

## 撤退ラインへの距離

親 file `EPIStamStep12Body.lean:70` 撤退ライン:

> **L-S12-C(未採用): full `condExp`-of-score measure-theoretic discharge**

**判定: 発動する(一般 X,Y では 1 セッション不可)。**

- 自作 1(fisherInfo↔積分橋、V1 退化の pivot 込み)+ 自作 2(Blachman score-of-conv、Mathlib PR 級)だけで合計 **150-300 行 + 述語 pivot + regularity 仮定多数**。`condExp` 道具(A/B)と Gaussian 部品(C)は揃うが、**「score = logDeriv of convolution density」と「fisherInfo を pdf に正しく接続」の 2 本が一からで、いずれも単独で 1 セッションを食い尽くす**。
- 最大の障害は **D 群の `Found 0`**: score-of-convolution と condExp-of-independent が**概念として Mathlib に皆無**。これらは Blachman lemma の心臓で、heat-flow / Fubini regularity を伴う。

**新規縮退案(撤退ライン L-S12-C′ として提案)**:
> **L-S12-C′(GO 可能な縮退)**: 一般 X,Y の measure-theoretic full discharge は断念。代わりに **Gaussian 限定で `IsStamCondExpCSHyp` を `gaussianReal_conv_gaussianReal` + V2 closed-form (`=1/v`) から閉形式計算で 0-sorry 化**(自作 5、30-60 行、1 セッション可)。これにより「Gaussian なら本物の Fisher info 値で Step 2 不等式が成立」を非 vacuous に達成し、現状の「V1 fisherInfo=0 による vacuous discharge」(`isStamCondExpCSHyp_of_gaussian_fisherInfo_zero:327`)を**正しい値に格上げ**する。一般 X,Y は frontier gap のまま PR ターゲットへ。

---

## 着手 skeleton(縮退案 L-S12-C′ = Gaussian closed-form、GO 推奨経路)

`Common2026/Shannon/EPIStamCondExpScoreGaussian.lean`:

```lean
import Common2026.Shannon.EPIStamStep12Body
import Common2026.Shannon.FisherInfoV2
import Mathlib.Probability.Distributions.Gaussian.Real      -- gaussianReal_conv_gaussianReal
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace InformationTheory.Shannon.EPIStamCondExpScoreGaussian

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal
open Common2026.Shannon.FisherInfoV2
open InformationTheory.Shannon.EPIStamStep12Body

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Gaussian convex Fisher bound `1/(v₁+v₂) ≤ λ²/v₁ + (1-λ)²/v₂` — pure arithmetic
    once the three Fisher infos are pinned to `1/v` via the V2 closed form. -/
theorem gaussian_convex_fisher_bound {v₁ v₂ lam : ℝ}
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) (hlo : 0 ≤ lam) (hhi : lam ≤ 1) :
    1 / (v₁ + v₂) ≤ lam ^ 2 * (1 / v₁) + (1 - lam) ^ 2 * (1 / v₂) := by
  sorry  -- nlinarith [sq_nonneg (lam*v₂ - (1-lam)*v₁), ...] : 純算術

/-- Step 2 predicate, Gaussian closed-form discharge (replaces the V1-zero vacuous
    route with the genuine `1/v` Fisher values). Requires the law/Fisher bridge that
    pins `(fisherInfo (P.map X)).toReal = 1/v₁` etc. (自作 1 の縮退版). -/
theorem isStamCondExpCSHyp_of_gaussian_closedForm
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂)
    (hFisherX : (Common2026.Shannon.fisherInfo (P.map X)).toReal = 1 / (v₁ : ℝ))
    (hFisherY : (Common2026.Shannon.fisherInfo (P.map Y)).toReal = 1 / (v₂ : ℝ))
    (hFisherSum : (Common2026.Shannon.fisherInfo
        (P.map (fun ω => X ω + Y ω))).toReal = 1 / ((v₁ : ℝ) + v₂)) :
    IsStamCondExpCSHyp X Y P := by
  sorry  -- intro ...; rw [hFisherX, hFisherY, hFisherSum]; exact gaussian_convex_fisher_bound ...

end InformationTheory.Shannon.EPIStamCondExpScoreGaussian
```

> 注: `hFisher*` を**仮定として残す**(= 縮退の本体)。これらを `gaussianReal_conv_gaussianReal` +
> V2 `fisherInfoOfDensity_gaussianPDFReal` から無仮定化するのが自作 1 の完全版で、それは別セッション。
> 縮退案でも「Gaussian で非 vacuous な Step 2」を 0-sorry で得られる。

---

## まとめ(verdict)

- インベントリは **`docs/shannon/epi-stam-condexp-score-discharge-mathlib-inventory.md`**(本ファイル)
- **condExp 道具(A: conditional Jensen / total expectation / tower, B: condDistrib↔condExp, C: Measure.conv / rnDeriv_conv / Gaussian conv)はすべて Mathlib 既存** — 予想より整備されている
- **致命的欠落 1 件**: score-of-convolution(Blachman)と cross-term orthogonality(condExp×IndepFun)が `Found 0`。Fisher information も named lemma 皆無
- **既存述語は measure-theoretic 内容ゼロ**(`fisherInfo.toReal` 実数のみ)。本物を割るには **fisherInfo↔pdf 橋(V1 退化で現状破綻)を一から作り直す pivot が必要**
- 撤退ライン **L-S12-C 発動**。GO は **Gaussian closed-form 縮退(L-S12-C′)に限る**
