# EPI G2 端点連続性 — 一般形 genuine サンドイッチルート 在庫調査

> 対象: EPI G2 heat-flow 端点連続性 `wall:heatflow-continuity` / `wall:approx-identity-L1` を、
> 一般の有限 2 次モーメント分布で `h(X+√tZ) → h(X)` を **UnifIntegrable/UnifTight を経由せず
> genuine サンドイッチ**で閉じる候補ルートの Mathlib + in-tree 資産 verbatim 調査。
> 前回 `docs/shannon/epi-g2-sandwich-inventory.md` は naive Fatou 版サンドイッチを否定。本ファイルは
> **genuine な機構** ((α) Donsker-Varadhan 変分公式 / Gibbs / 凸汎関数 LSC、(β) 条件付き
> エントロピー / 畳み込み単調性) の Mathlib 部品有無を精査する。
> inventory のみ。実装・計画起草はしない。

## 一行サマリ

**genuine サンドイッチも両刃とも高レベル部品が Mathlib/in-tree に不在。既存率 ≈ 25%。** (α) 上界
の core (KL/相対エントロピーの **下半連続性 = Found 0**、**Donsker-Varadhan 変分公式 = Found 0**、
**凸汎関数の弱/L¹-LSC = Found 0**) はゼロ。在庫は **Gibbs/tangent-line 部品** (`mul_log_le_klDiv`、
`self_sub_one_le_mul_log`、`negMulLog_le_one_sub_self`、`convexOn_klFun`) + 単一測度 Jensen
(`le_integral_rnDeriv_of_ac`) + Fatou (`lintegral_liminf_le`) のみで、これらは LSC-in-n を組む
**素材**だが組立済み定理はない。(β) 下界の **新発見**は `IndepFun.map_add_eq_map_conv_map`
(`P.map(X+Y) = (P.map X) ∗ₘ (P.map Y)`、genuine Mathlib) だが、これは**測度の畳み込み等式のみ**で
**エントロピー単調性 `h(X+Y) ≥ h(X)` を直接与えない**。連続版 `condDifferentialEntropy` /
conditioning-reduces-entropy は **Mathlib/in-tree 双方 Found 0** (in-tree `condEntropy` は全離散
Shannon `∑ x`)。畳み込みエントロピー単調 lemma も **不在**。サンドイッチ組立 API
`tendsto_of_le_liminf_of_limsup_le` は **存在** (`ℝ` で型クラス充足)。**撤退ライン発動: yes** —
genuine サンドイッチも (α) で同型の LSC moonshot を再要求し、(β) で新 wall (畳み込みエントロピー
単調) を引き込むため、tractability は改善しない。

---

## 主定理の最終形 (証明したい端点連続性、層2 結論型 不変で載せ替え)

`EPIG2HeatFlowContinuity.lean:193` の現結論 (UI/UT 経由) を genuine サンドイッチで再導出する。
signature は不変:

```lean
theorem differentialEntropy_convDensity_integral_tendsto
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume) :
    Tendsto
      (fun t : ℝ => ∫ x, Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 t.toNNReal) x) ∂volume)
      (𝓝[Set.Ioi 0] 0)
      (𝓝 (∫ x, Real.negMulLog (pX x) ∂volume))
```

`f_n := convDensityAdd pX (gaussianPDFReal 0 ⟨u n,_⟩)`、`h(f) := ∫ negMulLog f`、
`∫ f log f = -h(f)`。genuine サンドイッチ pseudo-Lean (8 行):

```
-- 層1 (genuine closed): convDensityAdd_tendsto_L1_zero → f_n → pX in L¹(volume)
-- (α) 上界 = h の上半連続: limsup h(f_n) ≤ h(pX)
--     ⟺ liminf (∫ f_n log f_n) ≥ ∫ pX log pX   ( = ∫ f log f / KL の弱/L¹-LSC )
have hα : limsup (fun n => h (f_n)) atTop ≤ h pX     -- ← §A: KL-LSC / DV変分 / 凸LSC = Found 0
-- (β) 下界 = 畳み込み非減少: h(f_n) ≥ h(pX) 各 n
have hβ : ∀ n, h pX ≤ h (f_n)                        -- ← §B: 連続 conditioning = Found 0 / 畳み込み単調 = 不在 / EPI = transitive Stam residual
-- 組立: 端点 a := h pX に対し a ≤ liminf かつ limsup ≤ a → Tendsto
exact tendsto_of_le_liminf_of_limsup_le (β から) (α から)   -- §C: 存在 (genuine)
```

---

## §A — (α) 相対エントロピー / KL の下半連続性 + 変分公式 (Mathlib)

loogle authoritative (`--read-index .lake/build/loogle.index`、Found 件数明記)。

### A-1/A-2: Donsker-Varadhan 変分公式 + KL/相対エントロピー LSC

| 概念 | Mathlib API | file:line | 状態 | (α) での扱い |
|---|---|---|---|---|
| **Donsker-Varadhan 変分公式** `KL = sup_g (∫g dμ - log∫e^g dν)` | — | — | ❌ **不在**。`"DonskerVaradhan"` 名 = **Found 0**、`"onsker"` 名 = **Found 0**、`InformationTheory.klDiv, iSup` = **Found 0**、`InformationTheory.klDiv, SupSet.sSup` = **Found 0**、`InformationTheory.klDiv, Real.log, MeasureTheory.integral` = **Found 0** | ❌ Mathlib 不在 (authoritative) | DV 変分形は KL-LSC を「sup of 連続汎関数 ⟹ LSC」で出す王道だが、変分表現自体が Mathlib に無い |
| **klDiv の LSC** | — | — | ❌ **不在**。`InformationTheory.klDiv, LowerSemicontinuous` = **Found 0**、`InformationTheory.klDiv, Filter.liminf` = **Found 0** | ❌ Mathlib 不在 | (α) を直接出す唯一の高レベル部品が無い (前回 inventory を verbatim 追認) |
| **klDiv ≥ 0 (Gibbs 非負)** | — (名前付き lemma なし) | — | ❌ `"klDiv_nonneg"` 名 = **Found 0**、`InformationTheory.klDiv, \|- 0 ≤ _` = **Found 0**。`klDiv : ℝ≥0∞` なので `≥ 0` は型から自明 (lemma 不要) だが、`toReal` 版の明示的非負 lemma は無い | △ 型から自明 | KL 非負自体は `ℝ≥0∞`-値で自明。Gibbs の **有効内容** (cross-entropy bound) は下記 `mul_log_le_klDiv` |
| **klDiv 定義** | `InformationTheory.klDiv` | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57` | `noncomputable irreducible_def klDiv (μ ν : Measure α) : ℝ≥0∞` (namespace = `InformationTheory`) | ✅ 既存 | `∫ f log f = (klDiv (volume.withDensity f) volume).toReal` の素材。LSC は無い |

### A-3: Gibbs 不等式 / tangent-line 部品 (在庫あり、素材レベル)

| 概念 | Mathlib API | file:line | verbatim signature (`[...]` + 結論型 verbatim) | 状態 | (α) での扱い |
|---|---|---|---|---|---|
| **Gibbs (cross-entropy bound, KL ≥ 0 の本体)** | `InformationTheory.mul_log_le_klDiv` | `Basic.lean:360` | `(μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ENNReal.ofReal (μ.real univ * Real.log (μ.real univ / ν.real univ) + ν.real univ - μ.real univ) ≤ klDiv μ ν` | ✅ 既存 (genuine) | △ 質量レベルの Gibbs 下界。pointwise の `∫ f log f ≥ ∫ f log g` (cross-entropy) ではなく **集合質量** の Gibbs。LSC-in-n を直接出さない |
| (`toReal` 版) | `InformationTheory.mul_log_le_toReal_klDiv` | `Basic.lean:346` | `(hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : μ.real univ * Real.log (μ.real univ / ν.real univ) + ν.real univ - μ.real univ ≤ (klDiv μ ν).toReal` (section `variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]`) | ✅ 既存 | △ 同上、絶対連続 + 可積分前提 |
| **tangent-line `x-1 ≤ x log x`** | `Real.self_sub_one_le_mul_log` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:39` | `{x : ℝ} (h0 : 0 ≤ x) : x - 1 ≤ x * x.log` | ✅ 既存 (genuine) | ○ `f log f` の凸性 tangent-line。負部押さえ / Jensen 下界の素材。LSC 組立にはこれ + majorant が要る |
| **`negMulLog ≤ 1 - x`** | `Real.negMulLog_le_one_sub_self` | `NegMulLog.lean:234` | `{x : ℝ} (h0 : 0 ≤ x) : x.negMulLog ≤ 1 - x` | ✅ 既存 (genuine) | ○ `negMulLog` の上界 (tangent at 1)。Fatou を上から押さえる版の素材 |
| **`negMulLog ≥ 0` on [0,1]** | `Real.negMulLog_nonneg` | `NegMulLog.lean:174` | `{x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) : 0 ≤ negMulLog x` | ✅ 既存 | △ 区間 [0,1] のみ非負。`f > 1` 領域で `negMulLog < 0` (= 符号不定の根源) |
| **klFun の凸性** | `InformationTheory.convexOn_klFun` | `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean` (loogle hit) | `ConvexOn ℝ (Set.Ici 0) klFun` (klFun = `x*log x - x + 1`) | ✅ 既存 (genuine) | ○ Jensen 適用の凸性供給。`strictConvexOn_klFun` も同所 |

### A-4: 凸積分汎関数の弱/L¹-LSC (Ioffe 系) + Jensen

| 概念 | Mathlib API | file:line | verbatim signature | 状態 | (α) での扱い |
|---|---|---|---|---|---|
| **凸汎関数の弱/L¹-LSC (Ioffe)** | — | — | ❌ **不在**。`ConvexOn, MeasureTheory.lintegral` = **Found 0**、`ConvexOn, MeasureTheory.integral, LowerSemicontinuous` = **Found 0**、`Real.negMulLog, LowerSemicontinuous` = **Found 0** | ❌ Mathlib 不在 (authoritative) | 「ConvexOn integrand の積分汎関数が弱収束で LSC」という Ioffe 系汎用定理が無い。これが (α) の本体 |
| **Fatou (汎用 lintegral liminf)** | `MeasureTheory.lintegral_liminf_le` | `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:231` | `{ι : Type*} {f : ι → α → ℝ≥0∞} {u : Filter ι} [IsCountablyGenerated u] (h_meas : ∀ i, Measurable (f i)) : ∫⁻ a, liminf (fun i => f i a) u ∂μ ≤ liminf (fun i => ∫⁻ a, f i a ∂μ) u` | ✅ 既存 (genuine) | **△ 唯一の汎用 LSC 部品**。`ℝ≥0∞`-値・pointwise liminf 必須。negMulLog 符号不定 → 下方非有界部が `ℝ≥0∞` に乗らず、下方有界 integrable majorant (= heatflow/de la VP wall 同型入力) を前置要求 (§結論) |
| **Jensen 下界 (単一測度)** | `MeasureTheory.le_integral_rnDeriv_of_ac` | `Mathlib/MeasureTheory/Measure/Decomposition/IntegralRNDeriv.lean:49` | `[IsFiniteMeasure μ] [IsProbabilityMeasure ν] (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousWithinAt f (Set.Ici 0) 0) (hf_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) (hμν : μ ≪ ν) : f (μ.real univ) ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν` | ✅ 既存 | **✗ for (α)** — **単一測度**の Jensen 下界 (`f(質量) ≤ ∫ f(rnDeriv)`)。n に渡る liminf 比較ではない。`mul_le_integral_rnDeriv_of_ac` も同所 |

**§A 所見**: (α) genuine ルートの core 3 候補 — **Donsker-Varadhan 変分公式 (Found 0)**、**KL の
LSC (Found 0)**、**凸汎関数の弱/L¹-LSC = Ioffe (Found 0)** — はすべて Mathlib 不在 (authoritative,
合計 8 query すべて Found 0)。在庫は **Gibbs/tangent-line 素材** (`mul_log_le_klDiv` の質量 Gibbs、
`self_sub_one_le_mul_log`、`negMulLog_le_one_sub_self`、`convexOn_klFun`) + **単一測度 Jensen**
(`le_integral_rnDeriv_of_ac`) + **Fatou** (`lintegral_liminf_le`) のみ。これらは LSC-in-n を自力で
組む **素材**だが、組立済み定理は無い。Fatou に negMulLog を乗せるには負部の n-一様可積分 majorant
が必須で、それは **既存 `wall:heatflow-continuity` / `wall:approx-identity-L1` と数学的に同型の入力**。

---

## §B — (β) 条件付き differential entropy + conditioning reduces entropy + 畳み込み単調性

### B-5/B-6: 条件付き differential entropy + 連続 conditioning-reduces-entropy

| 概念 | API | file:line | verbatim signature | 状態 | (β) での扱い |
|---|---|---|---|---|---|
| **連続版 `condDifferentialEntropy`** | — | — | ❌ **Mathlib/in-tree 双方不在**。Mathlib loogle `"condEntropy"` 名 = **Found 0**、`MeasureTheory.condEntropy` = unknown identifier。in-tree `rg condEntropy\|condDifferentialEntropy` の hit は全て **離散 Shannon** | ❌ 不在 (連続版なし) | conditioning ルートで (β) を出す部品が連続側に皆無 |
| (in-tree 離散 condEntropy 1) | `InformationTheory.MeasureFano.condEntropy` | `InformationTheory/Fano/Measure.lean:69` | `(μ : Measure Ω) [IsFiniteMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) : ℝ := ∫ y, ∑ x : X, Real.negMulLog ((condDistrib Xs Yo μ y).real {x}) ∂(μ.map Yo)` (header: `[MeasurableSpace X] [MeasurableSingletonClass X]`, `[MeasurableSpace Y]`) | (離散) | ✗ — `∑ x : X` の**離散 Shannon** 条件付きエントロピー (Fano family)。differential 版ではない |
| (in-tree 離散 condEntropy 2) | `InformationTheory.Shannon.condEntropy` | `InformationTheory/Shannon/TypedRV.lean:51` | `[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] (μ : Measure Ω) [IsFiniteMeasure μ] (Xs : Ω → α) (Yo : Ω → β) : ℝ := MeasureFano.condEntropy μ Xs Yo` | (離散 re-export) | ✗ — `[Fintype α]` 必須の離散版 re-export |
| **連続 conditioning reduces entropy `h(X\|Z) ≤ h(X)`** | — | — | ❌ **不在**。離散版は `entropy_ge_condEntropy` のみ | ❌ 不在 | (β) の conditioning ルートは連続側に組立済み定理が無い |
| (in-tree 離散 conditioning) | `InformationTheory.Shannon.entropy_ge_condEntropy` | `InformationTheory/Shannon/SlepianWolf.lean:168` | `[Fintype W] [DecidableEq W] [Nonempty W] [MeasurableSpace W] [MeasurableSingletonClass W] [MeasurableSpace Y] (μ : Measure Ω) [IsProbabilityMeasure μ] (Ws : Ω → W) (Yo : Ω → Y) (hWs : Measurable Ws) (hYo : Measurable Yo) : MeasureFano.condEntropy μ Ws Yo ≤ entropy μ Ws` | (離散) | ✗ — `[Fintype W]` 離散版。連続類似は in-tree に無い |

### B-7: 平行移動不変 + 独立和の素材 (新発見: IndepFun conv 等式)

| 概念 | API | file:line | verbatim signature | 状態 | (β) での扱い |
|---|---|---|---|---|---|
| **独立和の law = 畳み込み (★新発見)** | `ProbabilityTheory.IndepFun.map_add_eq_map_conv_map` | `Mathlib/Probability/Independence/Basic.lean:1103` (`@[to_additive]` 源 `IndepFun.map_mul_eq_map_mconv_map`、加法形は自動生成) | `[IsFiniteMeasure μ] {f g : Ω → M} (hf : Measurable f) (hg : Measurable g) (hfg : f ⟂ᵢ[μ] g) : μ.map (f + g) = (μ.map f) ∗ₘ (μ.map g)` (M = 加法 `[MeasurableAdd₂ M]`) | ✅ 既存 (genuine) | **○ 新発見**。`P.map(X+Y)` を畳み込み `(P.map X) ∗ₘ (P.map Y)` に開く。だが **これは測度等式のみ** — `h` 単調性は別途要 (下記 B-8 不在)。AEMeasurable / SigmaFinite 版も同所 (`_₀` / `'`) |
| **differentialEntropy 平行移動不変** | `InformationTheory.Shannon.differentialEntropy_map_add_const` | `InformationTheory/Shannon/DifferentialEntropy.lean:171` | `{μ : Measure ℝ} (hμ : μ ≪ volume) [SigmaFinite μ] (y : ℝ) : differentialEntropy (μ.map (· + y)) = differentialEntropy μ` (genuine body: `MeasurableEmbedding.rnDeriv_map` + Lebesgue 平行移動不変) | **genuine** | ○ (β) の補助 (定数平行移動で normalize)。**但し (β) 本体 `h(X+Y) ≥ h(X)` ではない** (定数加算のみ) |

### B-8: 畳み込みエントロピー単調性の直接 lemma + EPI 本体

| 概念 | API | file:line | verbatim signature (結論型 verbatim) | genuine? | (β) での扱い |
|---|---|---|---|---|---|
| **直接 `h((μ.map X).conv ν) ≥ h(μ.map X)`** | — | — | ❌ **不在**。`"differentialEntropy", MeasureTheory.Measure.conv` / `differentialEntropy _ ≤ differentialEntropy _` の loogle は in-tree `differentialEntropy` が Mathlib index 外で unknown identifier だが、in-tree `rg differentialEntropy.*conv` = 0 hit。畳み込みでエントロピー非減少を直接述べる補題は in-tree/Mathlib 双方不在 | ❌ 不在 | **EPI 経由でない** (β) 直接ルートの部品なし |
| **EPI 本体 (entropyPower 加法下界)** | `InformationTheory.Shannon.entropy_power_inequality` | `InformationTheory/Shannon/EntropyPowerInequality.lean:283` | `{Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) (h_stam : IsStamInequalityResidual X Y P) : entropyPower (P.map (fun ω => X ω + Y ω)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)` (body `:= stamToEPIBridge_holds X Y P h_stam`) | **transitive sorry** | △ (β) の主部品だが未閉。`entropyPower_pos` + 正値落としで `h(f_n) ≥ h(pX)` ⟹ `entropyPower(X+√tZ) ≥ entropyPower(X)`。だが `IsStamInequalityResidual` 引数 + transitive `stamToEPIBridge_holds` sorry を背負う |
| `stamToEPIBridge_holds` (transitive 壁) | 同 file `:245` | `{Ω : Type*} [MeasurableSpace Ω] (X Y : Ω → ℝ) (P : Measure Ω) : IsStamToEPIBridge X Y P := by sorry` | **sorry** `@residual(plan:epi-stam-to-conclusion-plan)` (`:243` docstring) | ✗ | EPI 経由 (β) が transitive に消費する別 residual。plan-class だが現状未閉 |
| **entropyPower 正値** | `InformationTheory.Shannon.entropyPower_pos` | `EntropyPowerInequality.lean:109` | `(μ : Measure ℝ) : 0 < entropyPower μ := Real.exp_pos _` | **genuine `@audit:ok`** | ○ EPI 加法下界 + 正値 → 片側落とし `entropyPower(X+√tZ) ≥ entropyPower(X)` |
| **entropyPower ↔ h 単調** | `InformationTheory.Shannon.entropyPower_le_of_differentialEntropy_le` | `EPIPlumbing.lean:86` | `{μ ν : Measure ℝ} (h : differentialEntropy μ ≤ differentialEntropy ν) : entropyPower μ ≤ entropyPower ν` (body: `Real.exp_le_exp.mpr` + linarith) | **genuine** | ○ `entropyPower` 不等式 ↔ `h` 不等式の橋 |

**§B 所見**: (β) genuine 直接ルート (条件付き / 畳み込み単調) は **連続側に組立済み定理ゼロ**:
連続 `condDifferentialEntropy` = Found 0、連続 conditioning-reduces-entropy = 不在、畳み込み
エントロピー単調 `h(X+Y) ≥ h(X)` 直接 = 不在 (in-tree/Mathlib 双方)。**新発見の素材**は
`IndepFun.map_add_eq_map_conv_map` (`P.map(X+Y) = (P.map X) ∗ₘ (P.map Y)`、genuine Mathlib) だが
**測度等式のみ**で、これから `h` 単調を出すには「畳み込みでエントロピー非減少」(=不在の壁) が必要。
よって (β) の唯一の組立済みルートは依然 **EPI 本体経由** で、(i) `IsStamInequalityResidual` 供給
(Stam wall) + (ii) transitive `stamToEPIBridge_holds` sorry (`plan:epi-stam-to-conclusion-plan`、
未閉) の 2 つを背負う。

---

## §C — 層2 載せ替え接続点 (サンドイッチ組立 API + 現 body 影響範囲)

`EPIG2HeatFlowContinuity.lean:193` `differentialEntropy_convDensity_integral_tendsto` の現 body 構造 (Read 済):

| 現 body の step | 行 | 消費する witness | サンドイッチ載せ替えで |
|---|---|---|---|
| `tendsto_iff_seq_tendsto` で `𝓝[Ioi 0] 0` を列化 | `:205` | (genuine) | **保持** (列化はサンドイッチでも要る、`u : ℕ → ℝ`) |
| 正値 surrogate `v n` + per-time integrability `hFint` | `:216-234` | `convDensityAdd_negMulLog_integrable_pub` (`@audit:ok`) | **保持** (各 n の可積分性は両ルート共通) |
| **Vitali `hVitali` (部分列ルート)** | `:255-280` | `hui := negMulLog_convDensity_unifIntegrable` (**parked, wall:approx-identity-L1**)、`hut := negMulLog_convDensity_unifTight` (**parked**)、`negMulLog_convDensity_tendsto_ae_subseq` (genuine) | **消える依存** = UI/UT witness 2 本 (`:247-250`)。サンドイッチでは `eLpNorm(F n - g) → 0` を直接 L¹ 収束で出さず、(α)+(β) で `∫ F n → ∫ g` を出す |
| `tendsto_Lp_of_tendsto_ae` で L¹ 収束 | `:273` | UI+UT (上記) | **消える** |
| `tendsto_integral_of_L1'` で `∫ F n → ∫ g` | `:289` | `hVitali` (L¹ 収束) | **消える** (サンドイッチは積分収束を直接組立) |

**サンドイッチ組立 API (存在確認)**:

| 概念 | Mathlib API | file:line | verbatim signature (`[...]` 込み) | 状態 |
|---|---|---|---|---|
| **liminf/limsup → Tendsto (サンドイッチ核)** | `tendsto_of_le_liminf_of_limsup_le` | `Mathlib/Topology/Order/LiminfLimsup.lean:306` | `{f : Filter β} {u : β → α} {a : α} (hinf : a ≤ liminf u f) (hsup : limsup u f ≤ a) (h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault) (h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) : Tendsto u f (𝓝 a)` (section header `:151` `variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]`) | ✅ 既存 (genuine)。**`ℝ` は 3 型クラス全充足** (`a := h pX`、`u := h ∘ f_n`、`f := atTop`)。`IsBoundedUnder` 2 本は `isBoundedDefault` で自動 (有界性が出れば省略可) |
| (補助: liminf=limsup → Tendsto) | `tendsto_of_liminf_eq_limsup` | `LiminfLimsup.lean:299` | `(hinf : liminf u f = a) (hsup : limsup u f = a) (h … h' …) : Tendsto u f (𝓝 a)` | ✅ 既存 |
| (Portmanteau の測度版サンドイッチ、参考) | `MeasureTheory.tendsto_measure_of_le_liminf_measure_of_limsup_measure_le` | `Mathlib/MeasureTheory/Measure/Portmanteau.lean:208` | (測度収束専用、本件の `∫ negMulLog` には不適) | ✅ 既存 | 

**載せ替え後に新たに要る入力**:
- (α): `limsup (∫ F n) ≤ ∫ g` (= `limsup h(f_n) ≤ h(pX)`) — **KL-LSC / DV変分 / 凸汎関数-LSC**
  (§A: 全 Found 0、新規 moonshot)。a.e. 部分列収束 `negMulLog_convDensity_tendsto_ae_subseq`
  (genuine) は Fatou の pointwise liminf 供給に流用可だが、符号不定で `ℝ≥0∞` Fatou に乗らない。
- (β): `∀ n, ∫ g ≤ ∫ F n` (= `h(pX) ≤ h(f_n)`) — **EPI 経由** (§B: transitive Stam residual)
  または 不在の畳み込みエントロピー単調 wall。
- `IsBoundedUnder` 2 本: `∫ F n` の上下有界。下方は (β)、上方は (α) の limsup から派生 (genuine 部品で出る)。
- 組立: `tendsto_of_le_liminf_of_limsup_le` (✅ 存在、`ℝ` で型クラス充足)。

**signature 不変性**: 結論型 `Tendsto (∫ negMulLog f_t) (𝓝[Ioi 0] 0) (𝓝 (∫ negMulLog pX))` は
**不変に保てる** (サンドイッチは内部 body の置換のみ)。層2 consumer
(`heatFlowEntropyPower_continuousWithinAt_zero` 他) は影響なし。

---

## 主要前提条件ボックス (前提事故注意)

- **`lintegral_liminf_le` (`Add.lean:231`)** — `{f : ι → α → ℝ≥0∞}` **`ℝ≥0∞`-値必須** +
  `[IsCountablyGenerated u]` + `∀ i, Measurable (f i)`。**`[IsFiniteMeasure]` 不要** (volume OK)。
  負値 `negMulLog` を直接乗せられない (符号不定 → `ℝ≥0∞` 化に下方有界 majorant 必要)。
- **`le_integral_rnDeriv_of_ac` (Jensen, `IntegralRNDeriv.lean:49`)** — `[IsFiniteMeasure μ]
  [IsProbabilityMeasure ν]` + `ConvexOn ℝ (Set.Ici 0) f` + `ContinuousWithinAt f (Set.Ici 0) 0` +
  `Integrable (f ∘ rnDeriv) ν` + `μ ≪ ν`。**単一測度** Jensen 下界で n-liminf でない。
- **`mul_log_le_klDiv` (Gibbs, `Basic.lean:360`)** — `[IsFiniteMeasure μ] [IsFiniteMeasure ν]`。
  **集合質量** (`μ.real univ`) レベルの Gibbs で、pointwise cross-entropy `∫ f log f ≥ ∫ f log g` ではない。
- **`IndepFun.map_add_eq_map_conv_map` (`Basic.lean:1103`)** — `[IsFiniteMeasure μ]` +
  `(hf : Measurable f) (hg : Measurable g)` + `(hfg : f ⟂ᵢ[μ] g)` + `M` が `[MeasurableAdd₂ M]`。
  **測度の畳み込み等式のみ** — エントロピー単調を含意しない。`h(X+Y) ≥ h(X)` には別途畳み込みエントロピー
  単調 lemma (=不在の壁) が必要。
- **`entropy_power_inequality` (EPI, `:283`)** — `[IsProbabilityMeasure P]` + `IndepFun X Y P` +
  **`h_stam : IsStamInequalityResidual X Y P`** (実供給に Stam wall) + body が transitive に
  **`stamToEPIBridge_holds` sorry** を消費。「EPI が in-tree にある」を「(β) が閉じている」と誤読しない。
- **`tendsto_of_le_liminf_of_limsup_le` (`LiminfLimsup.lean:306`)** —
  `[ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]`。`ℝ` 全充足。
  `IsBoundedUnder (·≤·)` / `(·≥·)` 2 本が必要 (`isBoundedDefault` 自動、ただし有界性の実体が要る)。

---

## 自作が必要な要素 (優先度順)

1. **(α) `∫ f log f` / KL の弱 or L¹-LSC (= KL-LSC / DV変分 / 凸汎関数-LSC のいずれか)** —
   最優先・最高難度。Mathlib 完全不在 (loogle Found 0 × 8 query: DV変分 / klDiv-LSC / klDiv-liminf /
   convex-lintegral / convex-integral-LSC / negMulLog-LSC)。負値 negMulLog を扱うため Fatou に直接
   乗らず、`f log f = (f log f)₊ - (f log f)₋` の **負部 `(f log f)₋` の n-一様可積分** (= 既存
   `wall:heatflow-continuity` / `wall:approx-identity-L1` と同型) が前提。在庫の素材
   (`self_sub_one_le_mul_log`、`convexOn_klFun`、`le_integral_rnDeriv_of_ac`、`lintegral_liminf_le`)
   から自力で組むことは原理上可能だが、**majorant 供給が既存 wall と同型**で壁を回避しない。moonshot 級。
2. **(β) 畳み込みエントロピー単調 `h((μ.map X) ∗ₘ ν) ≥ h(μ.map X)` の自作、または EPI transitive
   residual 2 本の closure** — 新発見の `IndepFun.map_add_eq_map_conv_map` で測度等式までは genuine に
   出るが、そこから `h` 単調を出す lemma が不在。自作するなら本質は EPI / de Bruijn と同じ解析。
   EPI 経由なら (i) `stamToEPIBridge_holds` (`plan:epi-stam-to-conclusion-plan`、未閉) + (ii)
   `IsStamInequalityResidual` 供給 = Stam wall。これらが閉じれば (β) は `entropyPower_pos` +
   `entropyPower_le_of_differentialEntropy_le` で plumbing。
3. **連続版 `condDifferentialEntropy` + conditioning-reduces-entropy の新規定義** — (β) の
   conditioning ルートを開くには連続版エントロピーの定義自体が無い (in-tree 全離散)。定義 + DPI 系の
   一式自作は大工事で、本壁単独の closure に対して過剰投資。

工数感: 1 は既存 heatflow/de la VP wall 同型の真 moonshot。2 は新測度等式部品で一歩前進したが、
本質の単調性は別壁 (EPI line closure 待ち or 同等解析の自作)。3 は連続エントロピー基盤の新設で
scope 過大。

---

## Mathlib/in-tree 壁の列挙 (`@residual` 対象)

| wall | 内容 | loogle / rg 確認 (authoritative) |
|---|---|---|
| **KL/相対エントロピーの LSC + Donsker-Varadhan 変分** (= (α) core) | `klDiv` の下半連続性、または DV 変分表現 (sup of 連続汎関数 で LSC を出す) | `"DonskerVaradhan"` = **Found 0**、`"onsker"` = **Found 0**、`InformationTheory.klDiv, iSup` = **Found 0**、`InformationTheory.klDiv, SupSet.sSup` = **Found 0**、`InformationTheory.klDiv, LowerSemicontinuous` = **Found 0**、`InformationTheory.klDiv, Filter.liminf` = **Found 0** |
| **凸積分汎関数の弱/L¹-LSC (Ioffe)** (= (α) を凸で出す) | `ConvexOn` integrand の積分が弱/L¹ 収束で LSC | `ConvexOn, MeasureTheory.lintegral` = **Found 0**、`ConvexOn, MeasureTheory.integral, LowerSemicontinuous` = **Found 0**、`Real.negMulLog, LowerSemicontinuous` = **Found 0** |
| **negMulLog 符号不定下の Fatou 適用** (= (α) を Fatou で出す前置) | `(f log f)₋` の n-一様可積分 majorant | **既存 `wall:heatflow-continuity` / `wall:approx-identity-L1` と同型** (前回 inventory §結論)。新規でなく既存壁の別形 |
| **畳み込みでエントロピー非減少 `h((μ.map X) ∗ₘ ν) ≥ h(μ.map X)`** (= (β) 直接 core) | 畳み込み測度のエントロピー単調 (EPI 経由でない) | in-tree `rg differentialEntropy.*conv` = **0 hit**、連続 conditioning `entropy_ge_condEntropy` 類似 = 連続側不在、`"condEntropy"` Mathlib = **Found 0** |
| **Stam → EPI bridge** (= (β) を EPI で出す transitive) | `stamToEPIBridge_holds` | `@residual(plan:epi-stam-to-conclusion-plan)` (`EntropyPowerInequality.lean:245` sorry、未閉)。plan-class (closeable 申告) だが現状 open |
| **Stam 不等式供給** (= EPI の `h_stam` 実供給) | `1/J(X+Y) ≥ 1/J(X)+1/J(Y)` の in-tree 供給 | in-tree `EPIStamInequalityBody.lean` で進行中 (前回 inventory 記載) |

**shared sorry 補題化**: (α) の KL-LSC / DV / 凸-LSC wall は **既存 `wall:heatflow-continuity`
(本 EPI G2 ライン) / `wall:approx-identity-L1` (層1) と数学的に同型** (両者とも `negMulLog f_n` の
負部 / 大値部の n-一様可積分を要求)。**新規 shared sorry 補題を増やすより、既存
`wall:heatflow-continuity` の park に集約するのが正しい** (詳細 → `docs/audit/audit-tags.md`
「共有 Mathlib 壁: shared sorry 補題パターン」)。(β) の畳み込み単調 wall は新発見の
`IndepFun.map_add_eq_map_conv_map` で測度等式まで genuine に縮退できるが、単調性 core は
依然 EPI line (`plan:epi-stam-to-conclusion-plan`) 管理下。

---

## 撤退ラインへの距離

親計画 `docs/shannon/epi-g2-vitali-closure-plan.md` + handoff (`.claude/handoff.md`) の EPI G2
撤退ラインは「残壁 = de la VP / heatflow-continuity wall = 真 moonshot、着手しないなら park 確定」。
前回 naive Fatou サンドイッチ inventory も「採用見送り」判定。

- **撤退ライン発動: yes (追認 + genuine サンドイッチ・ルートも否定)**。genuine サンドイッチは
  Donsker-Varadhan / 凸汎関数 LSC / 条件付きエントロピーという「高級な機構」を期待したが、
  **(α) の core 3 候補 (DV変分 / KL-LSC / 凸-LSC) はすべて Mathlib Found 0**、**(β) の連続版
  conditioning / 畳み込み単調も不在**。在庫は素材レベル (Gibbs/tangent-line/Jensen/Fatou/conv等式)
  に留まり、組立済み定理が無い。(α) の Fatou 適用は既存 heatflow/de la VP wall を別形で再要求し、
  (β) は新発見の conv 等式で一歩進むが本質の単調性で EPI line の未閉 residual に依存が残る。
  **総 tractability は改善しない**。
- 縮退案 (新規撤退ラインとして提案): **genuine サンドイッチ・ルートも採用見送りを推奨**。理由 =
  (α) が既存 wall を別形で再要求し回避しないため。現行の UI/UT park
  (`wall:heatflow-continuity` / `wall:approx-identity-L1`、own-file sorry-free) を維持し、
  de la VP / heatflow wall closure に集中する方が bookkeeping が局所化される。**仮説束化は禁止**
  (撤退口は sorry + `@residual` のみ)。
- ただし **(β) 単独 + 新発見**: `IndepFun.map_add_eq_map_conv_map` (genuine) で `P.map(X+√tZ)` の
  畳み込み構造を明示でき、Stam line が将来 genuine closure すれば `entropyPower_pos` + EPI で
  `h(f_n) ≥ h(pX)` が出る (片刃のみ機能)。これは EPI line closure の **副産物**であって
  サンドイッチ専用投資ではない。

---

## 着手 skeleton (採用見送り推奨、参考形のみ)

> genuine サンドイッチも (α) で既存 wall 同型 moonshot を再要求するため採用見送り推奨。
> skeleton は「載せ替えるなら層2 body をどう分割するか」の参考形のみ。実装はしない。

```lean
-- InformationTheory/Shannon/EPIG2GeneralSandwich.lean (構想、未作成 / 採用見送り)
import Mathlib.MeasureTheory.Integral.Lebesgue.Add          -- lintegral_liminf_le (Fatou)
import Mathlib.Topology.Order.LiminfLimsup                   -- tendsto_of_le_liminf_of_limsup_le (組立, 存在)
import Mathlib.InformationTheory.KullbackLeibler.Basic       -- mul_log_le_klDiv (Gibbs 素材), LSC は不在
import Mathlib.Probability.Independence.Basic                -- IndepFun.map_add_eq_map_conv_map (β 素材, 新発見)
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog       -- self_sub_one_le_mul_log 等 tangent 素材
import InformationTheory.Shannon.EPIApproxIdentityL1          -- convDensityAdd_tendsto_L1_zero (層1, genuine)
import InformationTheory.Shannon.EntropyPowerInequality       -- entropy_power_inequality (β, transitive Stam residual)

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

/-- **(α) 上界 — `h(f_n)` の上半連続 (= `∫ f log f` の L¹/弱-LSC)**:
`f_n → pX` in L¹ ⟹ `limsup h(f_n) ≤ h(pX)`. Mathlib/in-tree 不在
(loogle: DV変分 = Found 0、KL-LSC = Found 0、凸-LSC = Found 0)。負値 negMulLog の Fatou 適用は
負部 `(f log f)₋` の n-一様可積分を要求し、既存 `wall:heatflow-continuity` と数学的に同型。
新規壁を増やさず既存 wall に集約。
@residual(wall:heatflow-continuity) -/
theorem negMulLog_convDensity_limsup_le
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_lim : Tendsto u atTop (𝓝[Set.Ioi 0] 0)) :
    Filter.limsup
        (fun n => ∫ x, Real.negMulLog
          (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x) ∂volume) atTop
      ≤ (∫ x, Real.negMulLog (pX x) ∂volume) := by
  sorry  -- @residual(wall:heatflow-continuity)  ((α) = 既存 wall 同型)

/-- **(β) 下界 — 畳み込みでエントロピー非減少**: `h(pX) ≤ h(f_n)` 各 n.
測度の畳み込み構造は `IndepFun.map_add_eq_map_conv_map` (genuine) で明示できるが、そこから `h` 単調を
出す lemma は不在 (`h((μ.map X) ∗ₘ ν) ≥ h(μ.map X)` は in-tree/Mathlib 双方 Found 0)。EPI 経由
(`entropy_power_inequality` + `entropyPower_pos`) は transitive に `stamToEPIBridge_holds`
(`plan:epi-stam-to-conclusion-plan`) + Stam wall を消費。 -/
theorem negMulLog_convDensity_entropy_ge
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (n : ℕ) :
    (∫ x, Real.negMulLog (pX x) ∂volume)
      ≤ ∫ x, Real.negMulLog
          (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x) ∂volume := by
  sorry  -- @residual(plan:epi-stam-to-conclusion-plan)  ((β) = 畳み込み単調 / EPI transitive Stam residual)

end InformationTheory.Shannon
```

---

## §結論 (2 つの問いへの yes/no + 既存率)

**genuine サンドイッチ・ルートも既存 heatflow/de la VP wall より tractable ではない。採用見送りを推奨。**

1. **(α) genuine KL-LSC を出す Mathlib 部品はあるか → 部分的 (素材のみ)、core は NO。**
   - **Donsker-Varadhan 変分公式 = Found 0** (`"DonskerVaradhan"` / `"onsker"` 名 0、klDiv の iSup/sSup 0、klDiv+log+integral 0)。
   - **KL の LSC = Found 0** (`klDiv, LowerSemicontinuous` / `klDiv, Filter.liminf` 0)。
   - **凸汎関数の弱/L¹-LSC (Ioffe) = Found 0** (`ConvexOn, lintegral` / `ConvexOn, integral, LowerSemicontinuous` / `negMulLog, LowerSemicontinuous` 0)。
   - **在庫 (素材レベル)**: Gibbs `mul_log_le_klDiv` (`Basic.lean:360`、質量レベル)、tangent-line
     `self_sub_one_le_mul_log` (`NegMulLog.lean:39`)、`negMulLog_le_one_sub_self` (`:234`)、
     `convexOn_klFun` (`KLFun.lean`)、単一測度 Jensen `le_integral_rnDeriv_of_ac`
     (`IntegralRNDeriv.lean:49`)、Fatou `lintegral_liminf_le` (`Add.lean:231`)。
   - これらから LSC-in-n を自力で組むのは原理上可能だが、Fatou に negMulLog を乗せる majorant が
     **既存 `wall:heatflow-continuity` と同型**で壁を回避しない。

2. **(β) 条件付きエントロピー / 畳み込み単調性の Mathlib/in-tree 部品はあるか → 素材 1 つ新発見、core は NO。**
   - **連続版 `condDifferentialEntropy` = 不在** (Mathlib `"condEntropy"` Found 0、in-tree 全離散
     Shannon `∑ x`)。**連続 conditioning-reduces-entropy = 不在** (離散 `entropy_ge_condEntropy` のみ)。
   - **畳み込みエントロピー単調 `h(X+Y) ≥ h(X)` 直接 = 不在** (in-tree `rg` 0 hit、Mathlib 0)。
   - **★新発見 (素材)**: `IndepFun.map_add_eq_map_conv_map` (`Basic.lean:1103`、genuine) が
     `μ.map(X+Y) = (μ.map X) ∗ₘ (μ.map Y)` を与える (測度等式)。`differentialEntropy_map_add_const`
     (`DifferentialEntropy.lean:171`、genuine) で定数平行移動も genuine。だが **単調性 core は別**。
   - 唯一の組立済み (β) ルートは **EPI 本体経由** で transitive Stam residual 2 本 (`stamToEPIBridge_holds`
     `:245` sorry + Stam wall) を背負う。
   - **組立 API は存在**: `tendsto_of_le_liminf_of_limsup_le` (`LiminfLimsup.lean:306`、`ℝ` で
     `[ConditionallyCompleteLinearOrder] [TopologicalSpace] [OrderTopology]` 全充足、genuine)。

**一般形サンドイッチの「既存率」概算 ≈ 25%**:
- 組立 API (`tendsto_of_le_liminf_of_limsup_le`、Fatou、Jensen、Gibbs/tangent 素材、conv 等式、
  層1 L¹ 収束、entropyPower plumbing) = 在庫あり ≈ 7 部品。
- core 2 刃 ((α) KL/凸-LSC、(β) 畳み込み単調 or 連続 conditioning) = 不在 = 2 大 wall。
- 比率: 周辺素材は揃うが**両刃の core が不在**のため、定理完成への寄与度で見れば ≈ 25%
  (素材は多いが律速の core ゼロ)。

**自作必要要素リスト** (優先度順): (1) (α) KL/凸汎関数の弱/L¹-LSC = 既存 wall 同型 moonshot、
(2) (β) 畳み込みエントロピー単調 `h((μ.map X) ∗ₘ ν) ≥ h(μ.map X)` の自作 or EPI transitive
residual 2 本 closure、(3) (任意) 連続版 condDifferentialEntropy 基盤新設 (scope 過大)。

**総合判定**: genuine サンドイッチは Donsker-Varadhan / 凸 LSC / 条件付きエントロピーという高級機構を
期待したが、**core 候補は全 Mathlib Found 0**。在庫は素材レベルに留まり、(α) は既存 wall 同型 LSC を
再要求、(β) は新発見 conv 等式で測度構造まで進むも単調性 core で EPI line の未閉 residual に依存。
loogle authoritative (主要 Found 0): `"DonskerVaradhan"` = **Found 0**、`klDiv, LowerSemicontinuous`
= **Found 0**、`klDiv, Filter.liminf` = **Found 0**、`ConvexOn, MeasureTheory.lintegral` = **Found 0**、
`ConvexOn, MeasureTheory.integral, LowerSemicontinuous` = **Found 0**、`Real.negMulLog,
LowerSemicontinuous` = **Found 0**、Mathlib `"condEntropy"` = **Found 0**。新発見の正の在庫
(`IndepFun.map_add_eq_map_conv_map` genuine、`tendsto_of_le_liminf_of_limsup_le` genuine) は周辺
plumbing を改善するが律速の core を埋めない。**撤退ライン発動: yes (追認)** — genuine サンドイッチも
採用見送り推奨、現行 `wall:heatflow-continuity` / `wall:approx-identity-L1` park 維持。
