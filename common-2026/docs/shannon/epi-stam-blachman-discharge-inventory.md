# EPI Stam/Blachman discharge — Mathlib feasibility 在庫

> 調査対象: `entropy_power_inequality` (`Common2026/Shannon/EntropyPowerInequality.lean:188`)
> を Stam/Blachman 経路で **unconditional** にできるか。
> 焦点: undischarged な "genuinely-irreducible Stam primitives" の正確な同定 +
> Blachman score-of-convolution identity への Mathlib 支援の有無。
> 同 family: [`shannon-mathlib-inventory.md`](shannon-mathlib-inventory.md),
> [`cramer-chernoff-clt-closure-mathlib-inventory.md`](cramer-chernoff-clt-closure-mathlib-inventory.md)

## Part 3 先出し — Feasibility verdict (REQUIRED, lead with this)

**verdict: 1 セッションでの 0-sorry unconditional EPI は NO。** undischarged primitive のうち
*genuine 数学内容を持つ* ものは 3 本（`IsStamTotalExpectation` / `IsStamScoreConvolution` /
`IsStamToEPIScalingHyp`）あり、いずれも「Blachman の score-of-convolution + 条件付き期待値積分」
という同一の measure-theoretic コアに帰着する。このコアを 1 セッションで埋めるのは不可能。理由：

1. **Fisher 情報の抽象が flaw 上に乗っている。** 全 Stam primitive は **V1**
   `Common2026.Shannon.fisherInfo` (`FisherInfo.lean:58`、`Measure.rnDeriv` =
   `Classical.choose` 経由) を `.toReal` で参照する。V2 file 自身の docstring が明言する通り
   V1 は Gaussian で **0 を返す flaw** がある (`FisherInfoV2.lean:25-29`)。現状の Gaussian 全
   discharge (`*_of_gaussian_fisherInfo_zero`) は **この flaw を悪用**し、`0 < J_X` の前提を
   `J_X = (0).toReal = 0` で vacuous に潰しているだけ — 真の score-convolution 証明ではない。
   unconditional 化にはまず **全 primitive を V2 `fisherInfoOfDensity` に張り替える**必要があり、
   これ自体が複数 file の手術。

2. **density-of-sum の shape が壊滅的にミスマッチ。** Mathlib は
   `IndepFun.pdf_add_eq_lconvolution_pdf` (= 和の密度は Lebesgue 畳み込み) を持つが、結論は
   **`pdf (X+Y) ℙ μ =ᵐ[μ] pdf X ℙ μ ⋆ₗ[μ] pdf Y ℙ μ` という a.e. 等式**であり、`⋆ₗ`
   (`lconvolution`) は **微分可能性が一切証明されていない** (loogle `Differentiable, lconvolution
   → Found 0`)。一方プロジェクトの `fisherInfoOfDensity (f : ℝ → ℝ)` は **点ごとに微分可能な
   `f`** (`logDeriv f = deriv f / f`) を要求する。Blachman の `s_Z = E[s_X | X+Y]` を導くには
   「畳み込み密度が微分可能で、その `logDeriv` が条件付き期待値に等しい」という橋が要るが、
   この橋は **Mathlib にも本 repo にも存在しない**。

3. **score 抽象が Mathlib に皆無。** `fisherInfo` は loogle で `unknown identifier`
   (Mathlib 側に Fisher 情報の定義なし)。条件付き期待値 (`condExp` 171 lemmas)、`condDistrib`
   (51 lemmas)、条件付き分散 `condVar_ae_le_condExp_sq` (= 条件付き Jensen `(E[g|G])² ≤ E[g²|G]`
   の実体)、`hasDerivAt_integral_of_dominated_loc_of_deriv_le` (積分記号下微分) は全て**存在する**が、
   これらを `pdf`/`logDeriv`/`fisherInfoOfDensity` に結びつける hook が一切ない。

**最も tractable な sub-target**: 「`IndepFun` 和の密度 = 畳み込み」を `fisherInfoOfDensity` の
言葉に乗せる **foundational helper** ——具体的には **`pdfReal (X+Y) = (pdfReal X) ⋆ (pdfReal Y)`
の点ごと smooth 版 + その `logDeriv` 表現**。これは Mathlib の `pdf_add_eq_lconvolution_pdf` を
出発点にできるが、`⋆ₗ` の微分可能性が無いため Gaussian-mollified (heat-kernel smoothed) 密度に限定
しても **新規 50-150 行 + おそらく `lconvolution` 微分可能性の自前補題**。1 sub-target でも
1 セッション超。**型クラス漏れ警告**: `pdf_add_eq_lconvolution_pdf` の `[HasPDF X ℙ μ]
[HasPDF Y ℙ μ] [IsFiniteMeasure ℙ]` は、もし top-level EPI に持ち込むと現状の
`(P : Measure Ω) [IsProbabilityMeasure P]` に **`HasPDF X P volume` 2 本が追加漏れ**する
(EPI signature の質的後退)。

---

## Part 1 — undischarged primitive 完全マップ (CODE-GROUNDED)

凡例: 状態欄 — **`True`** = 字面 `Prop := True`、**実 Prop** = 実数不等式を持つ、
**pass-through** = 別 predicate へ defeq、**flaw-vacuous** = V1-zero artefact で前提潰し discharge。

### 1A. primitive predicate 一覧 (`def ... : Prop := ...` body 逐語)

| primitive | file:line | `def` body (要約) | 真の数学内容? | unconditional discharge? |
|---|---|---|---|---|
| `IsStamScoreConvolution` | `EPIStamInequalityBody.lean:104` | `:= True` | **無** (placeholder) | `_trivial` (= `trivial`)。実体ゼロ |
| `IsStamCauchySchwarz` | `EPIStamInequalityBody.lean:134` | `∀ J_X J_Y J_sum, …(V1 fisherInfo)… → ∃ lam∈[0,1], J_sum ≤ lam²J_X+(1-lam)²J_Y` | **有** (Step2-3 出力) | **無**。`_of_gaussian` のみ (flaw-vacuous) |
| `IsStamCauchySchwarzOptimal` | `EPIStamInequalityBody.lean:237` | `∀ …(V1)… → J_sum ≤ J_X·J_Y/(J_X+J_Y)` | **有** (harmonic mean) | **無**。`_of_gaussian_fisherInfo_zero` (flaw-vacuous) |
| `IsStamScoreConvHyp` | `EPIStamStep12Body.lean:164` | `∀ J_X J_Y, 0<·→… → ∃ lam∈[0,1], lam = J_Y/(J_X+J_Y)` | **無** (λ存在のみ、自明) | `_intro` で**真に discharge** (中身が無いので) |
| `IsStamCondExpCSHyp` | `EPIStamStep12Body.lean:214` | `∀ …(V1)… → ∀ lam∈[0,1], J_sum ≤ lam²J_X+(1-lam)²J_Y` | **有** (∀λ convex bound) | **無**。`_of_gaussian_fisherInfo_zero` (flaw-vacuous) |
| `IsStamFisherCoupling` | `EPIStamStep3Body.lean:112` | `:= IsStamCauchySchwarz X Y P` | **有** (defeq) | **無**。pass-through |
| `IsStamTotalExpectation` | `EPIStamStep3Body.lean:152` | `∀ J_X J_Y J_sum lam, 0<·→0≤lam→lam≤1→…(V1)… → J_sum ≤ lam²J_X+(1-lam)²J_Y` | **有** (cross-term drop = IBP) | **無**。`_of_gaussian_fisherInfo_zero` (flaw-vacuous) |
| `IsStamInequalityHyp` | `EPIStamDischarge.lean:121` | `∀ …(V1)… → 1/J_sum ≥ 1/J_X+1/J_Y` | **有** (Stam 真 signature) | **無**。`_of_fisher_info_zero` (flaw-vacuous) |
| `IsStamToEPIBridgeHyp` | `EPIStamDischarge.lean:304` | `:= IsStamInequalityHyp X Y P → IsEntropyPowerInequalityHypothesis X Y P` | **有** (Csiszár scaling) | **無**。`_of_gaussian_via_scaling` (saturation) |
| `IsStamToEPIScalingHyp` | `EPIStamToBridge.lean:137` | `IsStamInequalityHyp → ∀ g0 g1, g0=gap → g1=0 → g0 ≥ g1` | **有** (gap 単調性) — だが **EPI 結論を密輸** | **無**。`_of_gaussian` のみ |
| `IsStamToEPILimitHyp` | `EPIStamToBridge.lean:162` | `∃ g1, g1=0 ∧ (g1 ≤ gap ∨ EPI結論)` | **弱** (endpoint=0、構造的自明) | `_of_gaussian` (saturation) |
| `IsEntropyPowerInequalityHypothesis` | `EntropyPowerInequality.lean:168` | (EPI 結論 `entropyPower(X+Y) ≥ …` そのもの) | **= 結論** (L-EPI3 密輸) | `_of_gaussian` (saturation) |

**`fisherInfo` 参照の致命的注記**: 上表で「(V1)」と記したものは全て
`(Common2026.Shannon.fisherInfo (P.map X)).toReal` を参照 (V1、`FisherInfo.lean:58`)。
**`fisherInfoOfDensity` (V2, `FisherInfoV2.lean:88`) を使う primitive は 1 本も無い。**
V2 は Gaussian で `1/v` を正しく返す (`fisherInfoOfDensity_gaussianPDFReal`,
`FisherInfoV2.lean:296`) が、Stam 鎖は V2 に接続されていない。

### 1B. discharge 鎖の到達点 (`isStamInequalityHyp_of_primitives` が消費するもの)

`isStamInequalityHyp_of_primitives` (`EPIStamDeBruijnConclusion.lean:162`):

```lean
theorem isStamInequalityHyp_of_primitives
    {Ω : Type*} [MeasurableSpace Ω] {X Y : Ω → ℝ} {P : Measure Ω}
    (h_conv : IsStamScoreConvolution X Y P)        -- = True (中身ゼロ)
    (h_te : IsStamTotalExpectation X Y P) :          -- 実 Prop (V1 fisherInfo)
    IsStamInequalityHyp X Y P :=
  isStamInequalityHyp_via_step3 h_conv h_te
```

→ 消費する primitive は実質 **`IsStamTotalExpectation` 1 本**
(`h_conv` は `True` で何も運ばない)。`isStamInequalityHyp_via_step3`
(`EPIStamStep3Body.lean:258`) は `h_conv` を捨て `h_te` だけで
`isStamCauchySchwarzOptimal_of_coupling h_te` → harmonic mean → Stam 真 signature を出す。
Step 2 (Cauchy-Schwarz) と Step 4 (λ最適化) は**純算術で既に完済** (`stam_lambda_min` 等)。

### 1C. 依存グラフ — 何を unconditional に埋めれば鎖が崩れるか

```
entropy_power_inequality (EntropyPowerInequality.lean:188)
  └─ h_epi : IsEntropyPowerInequalityHypothesis   ← L-EPI3 で EPI 結論を直接 hypothesis 化
       ▲ これを供給する 2 経路:
       │
   [経路 A: integrated pipeline]
   entropy_power_inequality_via_stamDeBruijn (DeBruijnConclusion.lean:219)
     └─ IsEPIStamDeBruijnPipeline { convScore, totalExp, bridge }
          ├─ convScore : IsStamScoreConvolution   = True (no-op)
          ├─ totalExp  : IsStamTotalExpectation    ★★ ROOT 実 primitive #1
          │     └→ isStamInequalityHyp_of_primitives → IsStamInequalityHyp (V1 inverse Stam)
          └─ bridge    : IsStamToEPIBridgeHyp       ★★ ROOT 実 primitive #2
                └─ = (IsStamInequalityHyp → EPI 結論)   ← Csiszár scaling、EPI 結論を内蔵
                     └─ scaling : IsStamToEPIScalingHyp   ← _of_gaussian のみ (EPI 密輸)
       │
   [経路 B: Gaussian saturation] (現状 unconditional に閉じている唯一の経路)
   entropy_power_inequality_gaussian_full' (DeBruijnConclusion.lean:285)
     └─ entropy_power_inequality_gaussian_saturation (EntropyPowerInequality.lean:226)
          └─ gaussianReal_add_gaussianReal_of_indepFun (Mathlib) + closed-form entropy
             → 真に unconditional だが **Gaussian 専用** (general case 未達)
```

**鎖を崩す最小集合**: top-level EPI を一般 `X, Y` で unconditional にするには
**`IsStamTotalExpectation` (root #1) と `IsStamToEPIScalingHyp` (root #2) の両方**を
非 Gaussian で埋める必要がある。さらにこの 2 本を**意味のある形に**するには:

- root #1 を埋めるには **Blachman score-of-convolution** (`s_Z = E[λs_X+(1-λ)s_Y | X+Y]`) +
  **条件付き Cauchy-Schwarz 積分** が要る — これが「THE root primitive」。**かつ** V1→V2 fisherInfo
  張り替えが先行条件 (V1 では数値が嘘なので、埋めても無意味)。
- root #2 (`IsStamToEPIScalingHyp`) は de Bruijn FTC + heat-flow gap 単調性 — これも独立に重い。

現状 `IsStamScoreConvolution` (= Blachman identity を運ぶべき predicate) が **`True`**
である事実が、Blachman identity が **一切形式化されていない**ことの直接の証拠。
"Blachman score-of-convolution identity is THE root primitive" は本調査で**確認**。

---

## Part 2 — Blachman identity への Mathlib 支援 (loogle authoritative)

凡例: file 行は **checked-out source** (`.lake/packages/mathlib/...`) で実検証。
loogle index は **新しめの Mathlib snapshot** を指しており、和形の名前
(`map_add_eq_map_conv_map`, `pdf_add_eq_lconvolution_pdf`) は **`@[to_additive]`
自動生成**。checked-out source 側は乗法形が primary、`∗ₘ`/`⋆ₘₗ` 記法。

### 2A. density of `X + Y` (IndepFun sum = convolution)

| 概念 | Mathlib API | file:line | 状態 |
|---|---|---|---|
| 和の law = law の畳み込み (Measurable) | `IndepFun.map_add_eq_map_conv_map` (← `map_mul_eq_map_mconv_map`) | `Independence/Basic.lean:1102` (乗法), 和形は to_additive | ✅ 存在 |
| 同 (AEMeasurable, σ-finite 明示) | `IndepFun.map_add_eq_map_conv_map₀'` (← `…₀'`) | `Independence/Basic.lean:1078` | ✅ |
| 和の **pdf** = pdf の **Lebesgue 畳み込み** | `IndepFun.pdf_add_eq_lconvolution_pdf` (← `pdf_mul_eq_mlconvolution_pdf`) | `Density.lean:356` (乗法) | ✅ 存在、但 a.e. 等式 |
| 同 (σ-finite 明示) | `IndepFun.pdf_add_eq_lconvolution_pdf'` (← `…'`) | `Density.lean:349` | ✅ |
| 和が pdf を持つ | `IndepFun.add_hasPDF` (← `mul_hasPDF`) | `Density.lean:344` | ✅ |

**`IndepFun.map_mul_eq_map_mconv_map` 逐語 (`Independence/Basic.lean:1102`、和形の親)**:

```lean
@[to_additive]
theorem IndepFun.map_mul_eq_map_mconv_map
    [IsFiniteMeasure μ] {f g : Ω → M} (hf : Measurable f) (hg : Measurable g)
    (hfg : f ⟂ᵢ[μ] g) :
    μ.map (f * g) = (μ.map f) ∗ₘ (μ.map g)
```

- 型クラス前提 (逐語): `{M : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M]`
  (section `Monoid`, `Independence/Basic.lean:1074-1076`), **加えて `[IsFiniteMeasure μ]`**。
- 引数: `hf : Measurable f`, `hg : Measurable g`, `hfg : f ⟂ᵢ[μ] g` (= `IndepFun f g μ`)。
- 結論形 (逐語、加法版に読み替え): `μ.map (f + g) = (μ.map f) ∗ (μ.map g)`
  (`∗` = additive `Measure.conv`)。**measure レベル**の畳み込み、密度ではない。

**`IndepFun.pdf_mul_eq_mlconvolution_pdf` 逐語 (`Density.lean:356`、和形の親)**:

```lean
@[to_additive]
theorem IndepFun.pdf_mul_eq_mlconvolution_pdf [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
    [IsFiniteMeasure ℙ] (hXY : IndepFun X Y ℙ) :
    pdf (X * Y) ℙ μ =ᵐ[μ] pdf X ℙ μ ⋆ₘₗ[μ] pdf Y ℙ μ
```

- section context (逐語、`Density.lean:330-331`): `{Ω G : Type*} {mΩ : MeasurableSpace Ω}
  {ℙ : Measure Ω} [Group G] {mG : MeasurableSpace G} [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [IsMulLeftInvariant μ] {X Y : Ω → G}`。加法版は `[AddGroup G]
  [MeasurableAdd₂ G] [MeasurableNeg G] [IsAddLeftInvariant μ]` (= `ℝ`, `volume` で充足)。
- per-theorem 前提 (逐語): `[SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ] [IsFiniteMeasure ℙ]`。
- 引数: `hXY : IndepFun X Y ℙ`。
- 結論形 (逐語、加法版): `pdf (X + Y) ℙ μ =ᵐ[μ] pdf X ℙ μ ⋆ₗ[μ] pdf Y ℙ μ`
  (`⋆ₗ` = additive `lconvolution`)。**`=ᵐ[μ]` (a.e. 等式)**、点ごと smooth ではない。

### 2B. conditional expectation / condDistrib 機構

| 概念 | Mathlib API | file:line | 状態 |
|---|---|---|---|
| 条件付き期待値 `μ[X | m]` | `MeasureTheory.condExp` | `ConditionalExpectation/Basic.lean` | ✅ (171 lemmas) |
| 条件付き分布 kernel | `ProbabilityTheory.condDistrib` | `Kernel/CondDistrib.lean:64` | ✅ (51 lemmas) |
| condExp = ∫ condDistrib | `condExp_ae_eq_integral_condDistrib_id` | `Kernel/CondDistrib.lean` | ✅ |
| 条件付き分散 `Var[X;μ|m]` | `ProbabilityTheory.condVar` | `Probability/CondVar.lean` | ✅ (22 lemmas) |
| **条件付き Jensen** `Var ≤ E[X²|m]` | `condVar_ae_le_condExp_sq` | `Probability/CondVar.lean:127` | ✅ **(= (E[g|G])² ≤ E[g²|G] の実体)** |
| condVar = E[X²|m] - (E[X|m])² | `condVar_ae_eq_condExp_sq_sub_sq_condExp` | `Probability/CondVar.lean` | ✅ |

**`condVar_ae_le_condExp_sq` 逐語 (`Probability/CondVar.lean:127`)** — Blachman Step 2 の
条件付き Cauchy-Schwarz `(E[g|G])² ≤ E[g²|G]` に最も近い既存物:

```lean
lemma condVar_ae_le_condExp_sq (hm : m ≤ m₀) [IsFiniteMeasure μ] (hX : MemLp X 2 μ) :
    Var[X; μ | m] ≤ᵐ[μ] μ[X ^ 2 | m]
```

- 型クラス前提 (逐語): `[IsFiniteMeasure μ]`、加えて section 変数
  `{m m₀ : MeasurableSpace Ω}` (m ≤ m₀ で与える)。
- 引数: `hm : m ≤ m₀`, `hX : MemLp X 2 μ`。
- 結論形 (逐語): `Var[X; μ | m] ≤ᵐ[μ] μ[X ^ 2 | m]`。
  `Var[X;μ|m] = μ[X²|m] - (μ[X|m])²` (`condVar_ae_eq_condExp_sq_sub_sq_condExp`) なので
  これは `(μ[X|m])² ≤ μ[X²|m]` (= 条件付き Jensen) と同値。**score 関数とは未接続**。

### 2C. score / logDeriv of convolution + 積分記号下微分

| 概念 | Mathlib API | file:line | 状態 |
|---|---|---|---|
| 積分記号下微分 (deriv 版) | `hasDerivAt_integral_of_dominated_loc_of_deriv_le` | `Analysis/Calculus/ParametricIntegral.lean:289` | ✅ |
| 積分記号下微分 (fderiv/Lip 版) | `hasFDerivAt_integral_of_dominated_loc_of_lip` | `Analysis/Calculus/ParametricIntegral.lean` | ✅ |
| `logDeriv` (score) | `logDeriv` | `Analysis/Calculus/LogDeriv.lean:34` | ✅ (`= deriv f / f`) |
| **convolution の `logDeriv`** | — | — | ❌ **Found 0** |
| **`lconvolution` の微分可能性** | — | — | ❌ **Found 0** (`Differentiable, lconvolution`) |
| **Fisher 情報 (Mathlib 側定義)** | — | — | ❌ **`fisherInfo` unknown identifier** |
| **Stam / Blachman 不等式** | — | — | ❌ Found 0 (前回調査 + 今回確認) |

**`hasDerivAt_integral_of_dominated_loc_of_deriv_le` 逐語 (`ParametricIntegral.lean:289`)**:

```lean
theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    {F' : 𝕜 → α → E} (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasDerivAt (F · a) (F' x a) x) :
    Integrable (F' x₀) μ ∧ HasDerivAt (fun n ↦ ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀
```

- 型クラス前提 (逐語、section): `{𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedSpace ℝ E]` + `{α : Type*} [MeasurableSpace α] {μ : Measure α}`。
  `[CompleteSpace E]` は本体で場合分け (不要)。
- 結論形 (逐語): `Integrable (F' x₀) μ ∧ HasDerivAt (fun n ↦ ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀`。
- **Blachman で要る形** (`s_Z(z) = (d/dz) log ∫ p_X(x)p_Y(z-x)dx = ∫ p_X'(x)p_Y(z-x)/p_Z(z) dx`)
  に使えるが、**`F`/`F'`/`bound` の構築と dominated 仮定の充足**は全て自前。畳み込みの
  smooth representative を先に立てねば `h_diff` が出ない。

### 2D. Gaussian 和 (saturation 経路、現状の unconditional 経路)

| 概念 | Mathlib API | file:line | 状態 |
|---|---|---|---|
| 独立 Gaussian の和 = Gaussian | `gaussianReal_add_gaussianReal_of_indepFun` | `Distributions/Gaussian/Real.lean` | ✅ (saturation で使用済) |

---

## 主要前提条件ボックス (前提事故注意)

- **`IndepFun.pdf_add_eq_lconvolution_pdf` (`Density.lean:356`)**:
  - `[SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ] [IsFiniteMeasure ℙ]` + section の
    `[AddGroup G] [MeasurableAdd₂ G] [MeasurableNeg G] [IsAddLeftInvariant μ]`。
  - **`HasPDF X ℙ μ` が top-level に漏れる**: 現状 EPI は密度の存在を仮定していない
    (`P.map X` が `volume` に絶対連続とは限らない)。これを使うと EPI signature に
    `[HasPDF X P volume] [HasPDF Y P volume]` が**追加され質的後退**。
  - 結論は `=ᵐ[μ]` の **a.e. 等式 + `⋆ₗ` (微分不能)** — `fisherInfoOfDensity` が要求する
    点ごと smooth `f` に**直接は使えない**。

- **`IndepFun.map_add_eq_map_conv_map` (`Independence/Basic.lean:1102`)**:
  - `[IsFiniteMeasure μ]` (確率測度で充足) + `[AddMonoid M] [MeasurableSpace M]
    [MeasurableAdd₂ M]` (= `ℝ` で充足)。**HasPDF 不要**で measure レベルなら軽い。
  - だが結論は `Measure.conv` (= measure 畳み込み)。密度・score へは別途 RN 微分が要る。

- **`condVar_ae_le_condExp_sq` (`CondVar.lean:127`)**:
  - `[IsFiniteMeasure μ]` + `hX : MemLp X 2 μ` (score が L² であること)。
  - score `s_X(X)` が `MemLp 2` であることの証明が前提 — Gaussian 以外では非自明
    (重テール密度で破れる)。

- **V1→V2 fisherInfo 張り替え (前提以前の構造問題)**:
  - 全 Stam primitive が V1 `fisherInfo` 参照。V1 は Gaussian で 0 (flaw)。
  - V2 `fisherInfoOfDensity (f : ℝ → ℝ)` は密度を**明示引数**として取る (`FisherInfoV2.lean:88`)。
    Stam primitive を V2 に張り替えると、各 `J_X = …` の RHS が
    `fisherInfoOfDensity (pdfReal X) .toReal` 等になり、**`P.map X` から `pdfReal X` を
    取り出す HasPDF 前提**が新たに必要。

---

## 自作が必要な要素 (優先度順、unconditional 化に向けて)

1. **[最 tractable] 畳み込み密度の smooth 表現 + logDeriv 表現 (foundational helper)**
   — `pdfReal (X+Y) =ᵐ (pdfReal X) ⋆ (pdfReal Y)` を点ごと smooth 版にし、その `logDeriv`
   を `∫ p_X'(x) p_Y(z-x) dx / p_Z(z)` で表す。出発点 `pdf_add_eq_lconvolution_pdf`
   (`Density.lean:356`)。**落とし穴**: (i) `⋆ₗ` の微分可能性が Mathlib に無く自前
   (`hasDerivAt_integral_of_dominated_loc_of_deriv_le` で `F z x := p_X(x)p_Y(z-x)` を立て
   dominated を充足)、(ii) heat-kernel mollification なしには tail/smoothness が出ない、
   (iii) a.e. 等式と点ごと値の往復。**工数 80-200 行 + 1 セッション超**。

2. **Blachman score-of-convolution identity** (`IsStamScoreConvolution` を `True` から実体へ)
   — `s_Z(z) = E[s_X(X) | X+Y=z]`。`condExp_ae_eq_integral_condDistrib_id`
   (`CondDistrib.lean`) + helper #1 の logDeriv 表現を結合。**工数 100-250 行**。前提に #1 必須。

3. **conditional Cauchy-Schwarz の積分** (`IsStamTotalExpectation` = root #1 を実体へ)
   — `condVar_ae_le_condExp_sq` (`CondVar.lean:127`) を score `g = λs_X+(1-λ)s_Y` に適用し、
   `p_Z` に対し全期待値を取り cross-term を独立性で落とす。**工数 60-150 行**。前提に #1,#2 必須。

4. **V1→V2 fisherInfo 張り替え** — 全 Stam primitive の `Common2026.Shannon.fisherInfo`
   参照を `fisherInfoOfDensity (pdfReal ·)` に置換し、Gaussian discharge を flaw-vacuous から
   真の値 (`fisherInfoOfDensity_gaussianPDFReal = 1/v`) に切替。**工数 file 横断 50-120 行**。
   #1-3 を意味あるものにする**前提条件**。

5. **de Bruijn FTC + gap 単調性** (`IsStamToEPIScalingHyp` = root #2 を実体へ) — heat-flow
   path の gap 導関数 `g'(t) = (1/2)(J(g_t) - …) ≥ 0` を FTC で積分。de Bruijn V2 足場
   (`fisherInfoOfDensityReal_nonneg` 等) は一部あるが path 積分は未形式化。**工数 150-300 行**。

---

## 撤退ラインへの距離

各 file 内の宣言済撤退ライン (実際にコードで発動済):

- `EPIStamInequalityBody.lean:47-55`: **L-Stam-CS / L-Stam-Conv / L-Stam-Opt** — Step 1-3 を
  predicate pass-through。**発動済**。
- `EPIStamStep12Body.lean:61-71`: **L-S12-A / L-S12-B** (採用)、**L-S12-C** (未採用 = full
  condExp discharge)。**発動済**。
- `EPIStamStep3Body.lean:63-72`: **L-Step3-TE** — total-expectation を `IsStamTotalExpectation`
  predicate に sub-decompose。**発動済**。
- `FisherInfoV2.lean:58-63`: **L-FV2-A** (density-as-input 採用) — V1 flaw 回避だが
  **Stam 鎖は未接続**。
- `EntropyPowerInequality.lean:183-187`: **L-EPI1/L-EPI2/L-EPI3** — EPI 結論を hypothesis 化
  (L-EPI3 が核心の密輸)。**発動済**。

**判定: 本調査では新規撤退ラインの発動は不要 (調査のみ、実装せず)。** ただし
**unconditional EPI を目指す全 primitive が既に最深の撤退ライン (L-S12-C 未採用 = full
measure-theoretic discharge) の手前で着地している**。これ以上の縮退余地は乏しく、唯一
unconditional に閉じている経路は Gaussian saturation (`entropy_power_inequality_gaussian_full'`,
`DeBruijnConclusion.lean:285`)。

**新規撤退ライン提案 (もし unconditional 着手するなら)**:
- **L-Blachman-1**: 自作要素 #1 (畳み込み密度 smooth 化) が `lconvolution` 微分可能性で詰まる
  → Gaussian-mollified 密度 (`p_X ⋆ φ_t`, `t>0`) に限定した heat-flow path 上でのみ score を定義、
  general density は撤退して **smoothed EPI** に縮退 (sorry なし、足場のみ publish)。
- **L-Blachman-2**: V1→V2 張り替え (#4) が HasPDF 前提漏れで signature 後退を強いる
  → top-level EPI に `[HasPDF X P volume]` を**明示追加**して general case を進める
  (Gaussian saturation 経路は HasPDF 無しで温存)。

---

## 着手 skeleton (もし最 tractable sub-target に着手するなら)

`Common2026/Shannon/EPIBlachmanConvScore.lean` (新規) の出だし。
**注意: 本ファイルは inventory 専用。以下は実装サブエージェント向けの参考 skeleton であり、
本調査では一切実装しない。**

```lean
import Common2026.Shannon.FisherInfoV2
import Mathlib.Probability.Density
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.CondVar
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Group.Convolution

/-!
# Blachman score-of-convolution: foundational helper toward unconditional EPI

`IsStamScoreConvolution` (`EPIStamInequalityBody.lean:104`) is currently `:= True`.
This file targets the most tractable sub-target: representing the density of an
`IndepFun` sum as a (mollified) convolution and exposing its `logDeriv` (score),
the prerequisite for a genuine Blachman identity `s_Z = E[s_X | X+Y]`.

Mathlib basis: `IndepFun.pdf_add_eq_lconvolution_pdf` (Density.lean:356, a.e. eq +
`⋆ₗ`), `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(ParametricIntegral.lean:289), `condVar_ae_le_condExp_sq` (CondVar.lean:127).
Gap: `⋆ₗ` has NO differentiability lemmas in Mathlib (loogle Found 0).
-/

namespace InformationTheory.Shannon.EPIBlachmanConvScore

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **[sub-target] Smooth convolution density of an IndepFun sum.**
For independent `X, Y` with smooth densities, the density of `X + Y` is the
pointwise convolution `(p_X ⋆ p_Y)(z) = ∫ p_X(x) p_Y(z - x) dx`, and it is
differentiable. (Starting point: `IndepFun.pdf_add_eq_lconvolution_pdf` — but the
`⋆ₗ` differentiability is NOT in Mathlib and must be built here.) -/
theorem convDensity_add_differentiable
    {X Y : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    -- [HasPDF X P volume] [HasPDF Y P volume] + smoothness hyps will leak in here
    : True := by
  sorry

/-- **[sub-target] Blachman score representation (the root primitive).**
`s_Z(z) = E[s_X(X) | X + Y = z]`. Requires `convDensity_add_differentiable`
(score of Z well-defined) + `condExp_ae_eq_integral_condDistrib_id`. -/
theorem blachman_score_eq_condExp
    {X Y : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) :
    True := by
  sorry

end InformationTheory.Shannon.EPIBlachmanConvScore
```

`convDensity_add_differentiable` を最初に埋める (helper #1)。これが
`lconvolution` 微分可能性の自前補題で詰まれば L-Blachman-1 (Gaussian-mollified 限定) へ撤退。
