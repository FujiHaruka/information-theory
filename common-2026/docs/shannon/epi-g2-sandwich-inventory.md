# EPI G2 端点連続性 — サンドイッチ分解 (LSC + 凸非減少) 在庫調査

> 対象: EPI G2 heat-flow 端点連続性 `wall:approx-identity-L1` を **UnifIntegrable/UnifTight 迂回**で閉じる moonshot 候補ルート (サンドイッチ分解)。
> 前回 inventory `docs/shannon/epi-g2-delavp-recheck-inventory.md` は UI/UT 直結ルート (de la VP wall) を「真 moonshot 三重確定」と判定。本ファイルは **別ルート (LSC + 凸非減少サンドイッチ)** が tractable かを独立に verbatim 調査する。
> inventory のみ。実装・計画起草はしない。

## 一行サマリ

**サンドイッチ両刃とも Mathlib/in-tree に直接部品が無い。** (α) 上界 `liminf ∫ f log f ≥ ∫ pX log pX` を出す **klDiv の LSC / 凸汎関数の L¹-LSC は loogle Found 0** (klDiv 29 補題に LSC/liminf 名は皆無、`ConvexOn + lintegral` = 0、`negMulLog + LowerSemicontinuous` = 0)。汎用 Fatou `lintegral_liminf_le` (`ℝ≥0∞`、IsCountablyGenerated) は存在するが negMulLog の **符号不定性** で直接乗らない (下半連続化に下方有界 majorant が要り、それが de la VP wall と同型の入力を再要求)。(β) 下界 `h(f_n) ≥ h(pX)` を出す in-tree 部品は EPI 本体 `entropy_power_inequality` だが、**別の未閉 residual `plan:epi-stam-to-conclusion-plan` (`stamToEPIBridge_holds` sorry) + Stam wall を transitive 消費**。de Bruijn は pointwise 符号のみ (積分版不在、前回判定を verbatim 追認)。**サンドイッチは de la VP wall を 2 つの別 wall (klDiv-LSC moonshot + Stam-to-EPI bridge plan) に置換するだけで、総 tractability は改善しない**。

---

## 主定理の最終形 (証明したい端点連続性)

層2 機構 (`EPIG2HeatFlowContinuity.lean:193`) が現状 UI/UT 経由で出している結論を、サンドイッチで再導出する:

```lean
-- 目標 (層2 の結論型、signature 不変で載せ替えたい)
theorem differentialEntropy_convDensity_integral_tendsto
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume) :
    Tendsto (fun t : ℝ => ∫ x, Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 t.toNNReal) x) ∂volume)
      (𝓝[Set.Ioi 0] 0) (𝓝 (∫ x, Real.negMulLog (pX x) ∂volume))
```

`f_n := convDensityAdd pX (gaussianPDFReal 0 ⟨u n,_⟩)`、`h(f) := ∫ negMulLog f`、`∫ f log f = -h(f)`。サンドイッチ pseudo-Lean:

```
-- 層1 (genuine closed): convDensityAdd_tendsto_L1_zero → f_n → pX in L¹(volume)
-- (α) 上界: limsup h(f_n) ≤ h(pX)  ⟺  liminf ∫ f_n log f_n ≥ ∫ pX log pX   (∫·log· の L¹-LSC)
have hα : (∫ pX·log pX) ≤ liminf (fun n => ∫ f_n·log f_n)        -- ← klDiv-LSC / 凸汎関数-LSC が要る (§A: Found 0)
-- (β) 下界: h(f_n) ≥ h(pX) 各 n  ⟹  liminf h(f_n) ≥ h(pX)
have hβ : ∀ n, h(pX) ≤ h(f_n)                                    -- ← EPI: entropyPower(X+√tZ) ≥ entropyPower(X) (§B: transitive Stam residual)
-- (α)+(β) ⟹ h(f_n) → h(pX) (= ∫ f_n log f_n → ∫ pX log pX)
exact tendsto_of_le_liminf_and_limsup_le hβ hα
```

---

## §A — (α) `∫ f log f` / klDiv / 相対エントロピーの L¹-LSC (Mathlib)

loogle authoritative (Found 件数明記、すべて `--read-index .lake/build/loogle.index`):

| 概念 | Mathlib API | file:line | 状態 | (α) での扱い |
|---|---|---|---|---|
| **klDiv 定義** | `InformationTheory.klDiv` | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57` | `noncomputable irreducible_def klDiv (μ ν : Measure α) : ℝ≥0∞` (namespace = **`InformationTheory`**、`ProbabilityTheory` ではない、loogle 名前検索で `"ProbabilityTheory.klDiv"` = Found 0 を確認) | ✅ 既存 (相対エントロピー本体) | `∫ f log f = klDiv (withDensity f) volume` の素材。だが LSC が無い |
| **klDiv の LSC** | — | — | ❌ **不在**。`InformationTheory.klDiv, LowerSemicontinuous` = **Found 0**、`InformationTheory.klDiv, Filter.liminf` = **Found 0**、`InformationTheory.klDiv, Filter.liminf, LE.le` = **Found 0**。klDiv 名前を含む宣言は全 **29 件**、いずれも `_self`/`_eq_zero_iff`/`_compProd_*`/`_smul_*`/`toReal_*`/`mul_log_le_*` のみで **LSC/liminf/continuous 名は皆無** | ❌ Mathlib 不在 (authoritative) | (α) を直接出す唯一の高レベル部品が無い |
| **klDiv の map 単調性 (DPI)** | — | — | ❌ **不在**。`InformationTheory.klDiv, MeasureTheory.Measure.map` = **Found 0** (前回 shannon-inventory と整合) | ❌ Mathlib 不在 | weak/L¹ 収束での klDiv 比較に流用不可 |
| **`klDiv = ∫⁻ klFun ∘ rnDeriv` 形** | `InformationTheory.klDiv_eq_lintegral_klFun` | `Basic.lean:119` | `klDiv μ ν = if μ ≪ ν then ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν else ∞` | ✅ 既存 | △ klDiv を `∫⁻ (nonneg integrand)` に開く → Fatou の足場。だが integrand が **`μ` (= f_n) 経由の rnDeriv** で n に依存、Fatou の pointwise liminf が `klFun ∘ (f_n の rnDeriv)` の収束を要求 (循環的) |
| **`negMulLog` の LSC** | — | — | ❌ **不在**。`Real.negMulLog, LowerSemicontinuous` = **Found 0**、`Real.negMulLog, Filter.liminf` = **Found 0** | ❌ Mathlib 不在 | (α) を `negMulLog` 直接で出す部品なし |
| **凸汎関数の L¹/弱-LSC** | — | — | ❌ **不在**。`ConvexOn, MeasureTheory.lintegral` = **Found 0**。`integral`+`liminf`+`ConvexOn` 名前同時 = **0** (liminf 名 219 件中 0) | ❌ Mathlib 不在 | 「ConvexOn integrand の積分汎関数が収束で LSC」という汎用定理が無い |
| **Fatou (汎用 lintegral liminf)** | `MeasureTheory.lintegral_liminf_le` | `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:231` | `{ι : Type*} {f : ι → α → ℝ≥0∞} {u : Filter ι} [IsCountablyGenerated u] (h_meas : ∀ i, Measurable (f i)) : ∫⁻ a, liminf (fun i => f i a) u ∂μ ≤ liminf (fun i => ∫⁻ a, f i a ∂μ) u` | ✅ 既存 (genuine) | **△ 唯一の汎用 LSC 部品**。だが `ℝ≥0∞`-値・**pointwise liminf 必須**。negMulLog は符号不定 → 下方非有界部分が `ℝ≥0∞` に乗らず、下方有界 majorant (= de la VP 同型入力) を要求 (§結論) |
| `MeasureTheory.lintegral_liminf_le'` | 同上 `:214` | `(h_meas : ∀ i, AEMeasurable (f i) μ) : …` (AEMeasurable 版) | ✅ 既存 | △ 上と同じ制約 |
| **Portmanteau LSC (弱収束 + 連続 nonneg)** | `MeasureTheory.lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure` | `Mathlib/MeasureTheory/Measure/Portmanteau.lean:496` | `{μ : Measure Ω} {μs : ℕ → Measure Ω} {f : Ω → ℝ} (f_cont : Continuous f) (f_nn : 0 ≤ f) (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i))` | ✅ 既存 (genuine) | **✗** — `f` が **連続 nonneg** + **測度** 側の弱収束を要求。我々は **積分関数 (`negMulLog ∘ density`)** が n に依存して動く形 (測度 `volume` は固定、密度 `f_n` が動く) で構造が逆。`negMulLog` も連続 nonneg でない |
| **Jensen (凸の積分下界)** | `MeasureTheory.le_integral_rnDeriv_of_ac` | `Mathlib/MeasureTheory/Measure/Decomposition/IntegralRNDeriv.lean:49` | `[IsFiniteMeasure μ] [IsProbabilityMeasure ν] (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0) (hf_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) (hμν : μ ≪ ν) : f (μ.real univ) ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν` | ✅ 既存 | **✗ for (α)** — **単一測度** Jensen 下界 (`f(質量) ≤ ∫ f(rnDeriv)`)。n に渡る liminf 比較ではない |
| `ConvexOn.map_integral_le` | `Mathlib/Analysis/Convex/Integral.lean` (loogle hit) | (Jensen 上界 `f(∫) ≤ ∫ f`) | ✅ 既存 | ✗ 同上、単一測度 Jensen で LSC-in-n でない |

**§A 所見**: klDiv は定義 + 29 補題揃うが **LSC/liminf を一切持たない** (loogle authoritative Found 0 を 3 query で確認)。`ConvexOn + lintegral` の汎用 LSC も Found 0。唯一の汎用 LSC 部品は **Fatou `lintegral_liminf_le`** (genuine, `ℝ≥0∞`, IsCountablyGenerated) だが、negMulLog の **符号不定性**が壁: `f log f` の下方 (`f > 1` 領域で `f log f > 0`、`f < 1` で `< 0`) を `ℝ≥0∞` Fatou に乗せるには下方有界 integrable majorant が要り、**それは de la VP wall が park している `∫ G(|negMulLog f_n|) ≤ M` 入力と同型**。Portmanteau LSC は連続 nonneg `f` + 測度側弱収束を要求し構造が逆 (我々は密度が動き測度固定)。

---

## §B — (β) 畳み込み/独立和でエントロピー非減少 `h(f_n) ≥ h(pX)` (in-tree + Mathlib)

| 概念 | API | file:line | verbatim signature (結論型 verbatim) | genuine? | (β) での扱い |
|---|---|---|---|---|---|
| **EPI 本体 (entropyPower 加法下界)** | `InformationTheory.Shannon.entropy_power_inequality` | `InformationTheory/Shannon/EntropyPowerInequality.lean:289` | `(P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) (h_stam : IsStamInequalityResidual X Y P) : entropyPower (P.map (fun ω => X ω + Y ω)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)` | **transitive sorry** (body `:= stamToEPIBridge_holds X Y P h_stam`、`stamToEPIBridge_holds` は `sorry`) | **△ (β) の主部品だが未閉**。`entropyPower > 0` (`entropyPower_pos`) と組めば `entropyPower(X+√tZ) ≥ entropyPower(X)` ⟹ `h(f_n) ≥ h(pX)`。だが `IsStamInequalityResidual` 引数 + transitive `stamToEPIBridge_holds` sorry を背負う |
| `stamToEPIBridge_holds` (transitive 壁) | 同 file `:251` | `(X Y : Ω → ℝ) (P : Measure Ω) : IsStamToEPIBridge X Y P := by sorry` | **sorry** `@residual(plan:epi-stam-to-conclusion-plan)` (`:223` 参照、docstring) | ✗ | EPI 経由 (β) が transitive に消費する **別 residual**。plan-class (closeable と申告) だが現状未閉 |
| `IsStamInequalityResidual` (Stam wall) | 同 file `:204` | `∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum → J_X = fisherInfoOfDensityReal fX → … → 1/J_sum ≥ 1/J_X + 1/J_Y` (Stam inverse harmonic-mean) | `@audit:ok` Prop (non-vacuous、Gaussian witness)、ただし供給は別途 `EPIStamInequalityBody.lean` の wall | (Prop は健全、供給に Stam wall) | EPI の引数。`h_stam` を実際に供給するには Stam 不等式 (Mathlib `rg "Stam" → 0 hit`) の in-tree 供給が要る |
| **entropyPower 正値** | `entropyPower_pos` | `EntropyPowerInequality.lean:109` | `(μ : Measure ℝ) : 0 < entropyPower μ := Real.exp_pos _` | **genuine `@audit:ok`** | ○ EPI 加法下界 + 正値 → 片側落とし `entropyPower(X+√tZ) ≥ entropyPower(X)` |
| **entropyPower ↔ differentialEntropy 単調** | `entropyPower_le_of_differentialEntropy_le` | `EPIPlumbing.lean:86` | `{μ ν : Measure ℝ} (h : differentialEntropy μ ≤ differentialEntropy ν) : entropyPower μ ≤ entropyPower ν` (body: `exp_le_exp.mpr` + linarith) | **genuine** | ○ `entropyPower` 不等式 ↔ `h` 不等式の橋。逆向き `differentialEntropy_le_of_entropyPower_le` も同様に出せる |
| **differentialEntropy 平行移動不変** (B6-i) | `differentialEntropy_map_add_const` | `DifferentialEntropy.lean:171` | `{μ : Measure ℝ} (hμ : μ ≪ volume) [SigmaFinite μ] (y : ℝ) : differentialEntropy (μ.map (· + y)) = differentialEntropy μ` (genuine body: `MeasurableEmbedding.rnDeriv_map` + 平行移動不変) | **genuine** | ○ (β) の補助 (平行移動で normalize)。但し (β) 本体 `h(X+Y)≥h(X)` ではない |
| **直接 differential `h(X+Y) ≥ h(X)`** | — | — | ❌ **不在** (`rg 'differentialEntropy.*≥|differentialEntropy_add' InformationTheory/Shannon/` = entry なし)。差分形 differential entropy の畳み込み非減少を直接述べる in-tree 補題は無い | ❌ in-tree 不在 | (β) を EPI 迂回で直接出す部品なし |
| **条件付き differential entropy / conditioning reduces entropy** (B6-ii) | — | — | ❌ **differential 版不在**。in-tree `condEntropy*` は全て **離散 Shannon** (`Entropy.lean:43` `entropy_pair_eq_entropy_add_condEntropy`、`SlepianWolf.lean:168` `entropy_ge_condEntropy`、`CondEntropyMemoryless.lean`)。`condDifferentialEntropy` / 連続版 conditioning-reduces-entropy は **0 hit**。Mathlib も差分エントロピー無し | ❌ in-tree/Mathlib 不在 | conditioning ルートで (β) を出す部品が連続側に無い |
| **de Bruijn 微分非負** (B7) | `deBruijn_deriv_nonneg` | `EPIStamDeBruijnConclusion.lean:132` | `(f : ℝ → ℝ) : 0 ≤ (1 / 2 : ℝ) * fisherInfoOfDensityReal f := mul_nonneg (by norm_num) (fisherInfoOfDensityReal_nonneg f)` | **genuine `@entry_point`** | **✗** — pointwise 符号 `g'(t) ≥ 0` のみ。`s ↦ h(P.map(X+√sZ))` の **積分版 MonotoneOn は in-tree 0 hit** (前回判定を verbatim 追認)。FTC-2 で組むには `s ↦ h` の `HasDerivAt` + 端点連続 (= まさに本壁) が前置で循環 |
| `deBruijn_gap_deriv_nonneg_gaussian` | `EPIStamDeBruijnConclusion.lean:260` | (Gaussian 専用の符号) `[IsProbabilityMeasure P]` | genuine | ✗ Gaussian 専用、一般 L¹ `pX` に無効 |
| **layer-1 (L¹ 収束、サンドイッチ起点)** | `convDensityAdd_tendsto_L1_zero` | `EPIApproxIdentityL1.lean:424` | `{pX} (hpX_nn hpX_meas hpX_int hpX_mom) : Tendsto (fun t => eLpNorm (convDensityAdd pX (gaussianPDFReal 0 t.toNNReal) - pX) 1 volume) (𝓝[Set.Ioi 0] 0) (𝓝 0)` | **genuine `@audit:ok`** | ○ サンドイッチの L¹ 起点 (f_n → pX in L¹)。(α) の弱収束 / a.e. 部分列はここから |

**§B 所見**: (β) `h(f_n) ≥ h(pX)` を出せる in-tree 部品は **EPI 本体 `entropy_power_inequality` のみ** (`entropyPower(X+Y) ≥ entropyPower(X) + entropyPower(Y)` + `entropyPower_pos` + `entropyPower_le_of_differentialEntropy_le`)。だがこれは **(i) `IsStamInequalityResidual` 引数の実供給 (Stam wall、Mathlib `rg Stam` = 0 hit) + (ii) transitive `stamToEPIBridge_holds` sorry (`plan:epi-stam-to-conclusion-plan`、未閉)** の 2 つを背負う。de Bruijn は pointwise 符号のみで積分版 monotone が in-tree 0 hit (前回追認)。差分 differential `h(X+Y)≥h(X)` 直接補題 / 連続 conditioning-reduces-entropy は in-tree/Mathlib 双方 **不在**。

---

## §C — 層2 機構の現状 (サンドイッチ載せ替えの影響範囲)

`EPIG2HeatFlowContinuity.lean:193` `differentialEntropy_convDensity_integral_tendsto` の現 body 構造 (Read 済):

| 現 body の step | 行 | 消費する witness | サンドイッチ載せ替えで |
|---|---|---|---|
| `tendsto_iff_seq_tendsto` で `𝓝[Ioi 0] 0` を列化 | `:205` | (genuine) | **保持** (列化はサンドイッチでも要る) |
| 正値 surrogate `v n` 構築 + per-time integrability `hFint` | `:216-234` | `convDensityAdd_negMulLog_integrable_pub` (`@audit:ok`) | **保持** (各 n の可積分性は両ルート共通) |
| **Vitali `hVitali` (部分列ルート)** | `:255-280` | `hui := negMulLog_convDensity_unifIntegrable` (**parked, wall:approx-identity-L1**)、`hut := negMulLog_convDensity_unifTight` (**parked**)、`negMulLog_convDensity_tendsto_ae_subseq` (genuine) | **消える依存** = UI/UT witness 2 本 (`:247-250`)。サンドイッチでは `eLpNorm(F n - g) → 0` を **直接** L¹ 収束で出さず、(α) LSC + (β) で `∫ F n → ∫ g` を出す |
| `tendsto_Lp_of_tendsto_ae` で L¹ 収束 | `:273` | UI+UT (上記) | **消える** |
| `tendsto_integral_of_L1'` で `∫ F n → ∫ g` | `:289` | `hVitali` (L¹ 収束) | **消える** (サンドイッチは積分収束を直接出す) |

**載せ替え後に新たに要る入力**:
- (α): `liminf (∫ F n) ≥ ∫ g` — **klDiv-LSC / 凸汎関数-LSC** (§A: Found 0、新規 moonshot)。a.e. 部分列収束 `negMulLog_convDensity_tendsto_ae_subseq` (genuine) は Fatou の pointwise liminf 供給に流用可能だが、符号不定で `ℝ≥0∞` Fatou に乗らない (§結論)。
- (β): `∀ n, ∫ g ≤ ∫ F n` (= `h(pX) ≤ h(f_n)`) — **EPI 経由** (§B: transitive Stam residual + bridge plan)。
- 組み立て: `tendsto_of_le_liminf_and_limsup_le` 相当 (Mathlib `le_antisymm`-of-liminf-limsup、汎用、存在)。

**signature 不変性**: 結論型 `Tendsto (∫ negMulLog f_t) (𝓝[Ioi 0] 0) (𝓝 (∫ negMulLog pX))` は **不変に保てる** (サンドイッチは内部 body の置換のみ)。層2 consumer (`heatFlowDifferentialEntropy_continuousWithinAt_zero` 他) は影響なし。

---

## 主要前提条件ボックス (前提事故注意)

- **`lintegral_liminf_le` (`Add.lean:231`)** — `{f : ι → α → ℝ≥0∞}` **`ℝ≥0∞`-値必須** + `[IsCountablyGenerated u]` + `∀ i, Measurable (f i)`。**`[IsFiniteMeasure]` 不要** (volume OK)。負値 `negMulLog` を直接乗せられない (符号不定 → `ℝ≥0∞` 化に下方有界 majorant 必要、それが de la VP 入力)。
- **`lintegral_le_liminf…_measure_le_liminf_measure` (Portmanteau `:496`)** — `f` が **`Continuous f` かつ `0 ≤ f`** + **測度列 `μs` の弱収束** (`∀ G open, μ G ≤ liminf μs G`)。我々は測度 `volume` 固定・密度 `f_n` が動く構造で、`f = negMulLog` は連続 nonneg でない。構造が合わない。
- **`le_integral_rnDeriv_of_ac` (Jensen, `IntegralRNDeriv.lean:49`)** — `[IsFiniteMeasure μ] [IsProbabilityMeasure ν]` + `ConvexOn ℝ (Ici 0) f` + `ContinuousWithinAt f (Ici 0) 0` + `Integrable (f ∘ rnDeriv) ν` + `μ ≪ ν`。**単一測度** Jensen 下界で n-liminf でない。
- **`entropy_power_inequality` (EPI, `:289`)** — `[IsProbabilityMeasure P]` + `IndepFun X Y P` + **`h_stam : IsStamInequalityResidual X Y P`** (実供給に Stam wall) + body が transitive に **`stamToEPIBridge_holds` sorry** を消費。「EPI が in-tree にある」を「(β) が閉じている」と誤読しない (2 つの未閉 residual 背負う)。
- **`differentialEntropy_map_add_const` (`:171`)** — `μ ≪ volume` + `[SigmaFinite μ]`。平行移動のみ、畳み込み非減少ではない。

---

## 自作が必要な要素 (優先度順)

1. **(α) `∫ f log f` の L¹-LSC (klDiv-LSC または negMulLog 汎関数 LSC)** — 最優先・最高難度。Mathlib 完全不在 (loogle Found 0 × 5 query)。負値 negMulLog を扱うため Fatou に直接乗らず、`f log f = (f log f)₊ - (f log f)₋` の **負部 `(f log f)₋` の一様可積分** (= de la VP wall の `∫ G(|negMulLog f_n|) ≤ M` と同型) が前提。**本壁が de la VP wall を別形で再要求する**ことを意味し、サンドイッチは壁を回避しない (§結論)。moonshot 級。
2. **(β) EPI の transitive residual 2 本の closure** — (i) `stamToEPIBridge_holds` (`plan:epi-stam-to-conclusion-plan`、未閉)、(ii) `IsStamInequalityResidual` 供給 = Stam 不等式 wall (Mathlib `rg Stam` = 0 hit、in-tree `EPIStamInequalityBody.lean` で進行中)。これらが閉じれば (β) `h(f_n) ≥ h(pX)` は `entropyPower_pos` + `entropyPower_le_of_differentialEntropy_le` で plumbing。
3. **de Bruijn 積分版 `s ↦ h(P.map(X+√sZ))` の MonotoneOn** — (β) の EPI 迂回候補。だが FTC-2 で組むには `HasDerivAt` + 端点連続 (= 本壁) が前置で循環。前回追認通りカテゴリ違い (pointwise 符号 ≠ 積分単調)。

工数感: 1 は de la VP wall 同型の真 moonshot。2 は既存 plan/wall の closure 待ち (本サンドイッチの新規負債ではないが、サンドイッチ採用で (β) が依存する)。3 は循環で本壁を閉じない。

---

## Mathlib/in-tree 壁の列挙 (`@residual` 対象)

| wall | 内容 | loogle / rg 確認 (authoritative) |
|---|---|---|
| **klDiv / 相対エントロピー / 凸汎関数の L¹-LSC** (= (α) 部品) | `klDiv` または `∫ negMulLog f` が L¹/弱/a.e. 収束で下半連続であることを示す定理 | `InformationTheory.klDiv, LowerSemicontinuous` = **Found 0**、`InformationTheory.klDiv, Filter.liminf` = **Found 0**、`Real.negMulLog, LowerSemicontinuous` = **Found 0**、`ConvexOn, MeasureTheory.lintegral` = **Found 0**。klDiv 29 補題に LSC/liminf 名皆無 |
| **negMulLog 符号不定下の Fatou 適用** (= (α) を Fatou で出す前置) | `(f log f)₋` の n-一様可積分 (Fatou を `ℝ≥0∞` に乗せる majorant) | **de la VP wall (`wall:approx-identity-L1`) と同型** — `∫ G(|negMulLog f_n|) ≤ M` を再要求 (前回 inventory §結論)。新規でなく既存壁の別形 |
| **Stam → EPI bridge** (= (β) を EPI で出す transitive) | `stamToEPIBridge_holds` | `@residual(plan:epi-stam-to-conclusion-plan)` (`EntropyPowerInequality.lean:251` sorry、未閉)。**plan-class** (closeable 申告) だが現状 open |
| **Stam 不等式供給** (= EPI の `h_stam` 実供給) | `1/J(X+Y) ≥ 1/J(X)+1/J(Y)` の in-tree 供給 | Mathlib `rg "Stam"` = **0 hit** (`IsStamInequalityResidual` docstring 記載)。in-tree `EPIStamInequalityBody.lean` で進行中 |

**shared sorry 補題化**: (α) の klDiv-LSC wall は **de la VP wall (`wall:approx-identity-L1`) と数学的に同型** (両者とも `negMulLog f_n` の負部 / 大値部の n-一様可積分を要求)。**新規 shared sorry 補題を増やすより、既存 `wall:approx-identity-L1` の park に集約するのが正しい** (詳細 → `docs/audit/audit-tags.md`「共有 Mathlib 壁: shared sorry 補題パターン」)。(β) の Stam-bridge は既存 `plan:epi-stam-to-conclusion-plan` 管理下で別 bookkeeping。

---

## 撤退ラインへの距離

親計画 `docs/shannon/epi-g2-vitali-closure-plan.md` + handoff (`.claude/handoff.md`) の EPI G2 撤退ラインは「残壁 = de la VP wall = 真 moonshot 三重独立確定、着手しないなら park 確定」。

- **撤退ライン発動: yes (追認 + サンドイッチ・ルートも否定)**。サンドイッチ分解は UI/UT を迂回するが、**(α) で klDiv-LSC moonshot (de la VP wall と同型)、(β) で Stam-to-EPI bridge plan + Stam wall を新たに引き込む**。総 tractability は改善せず、むしろ (β) で別ラインの未閉 residual に依存が増える。
- 縮退案 (新規撤退ラインとして提案): **サンドイッチ・ルートは採用見送りを推奨**。理由 = (α) が既存 de la VP wall を別形で再要求し壁を回避しないため、回避ルートとしての価値が無い。現行の UI/UT park (`wall:approx-identity-L1`、own-file sorry-free、active residual 2 本) を維持し、de la VP wall closure に集中する方が bookkeeping が局所化される。**仮説束化は禁止** (撤退口は sorry + `@residual` のみ)。
- ただし **(β) 単独**は、Stam line が将来 genuine closure すれば `entropyPower_pos` + EPI で `h(f_n) ≥ h(pX)` が出る (片刃のみ機能)。これは EPI line closure の **副産物**であってサンドイッチ専用投資ではない。

---

## 着手 skeleton (採用見送り推奨、参考形のみ)

> サンドイッチは (α) で de la VP wall 同型 moonshot を再要求するため採用見送り推奨。skeleton は「載せ替えるなら層2 body をどう分割するか」の参考形のみ。実装はしない。

```lean
-- InformationTheory/Shannon/EPIG2Sandwich.lean (構想、未作成 / 採用見送り)
import Mathlib.MeasureTheory.Integral.Lebesgue.Add          -- lintegral_liminf_le (Fatou)
import Mathlib.InformationTheory.KullbackLeibler.Basic       -- klDiv (LSC は不在)
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import InformationTheory.Shannon.EPIApproxIdentityL1          -- convDensityAdd_tendsto_L1_zero (層1, genuine)
import InformationTheory.Shannon.EntropyPowerInequality       -- entropy_power_inequality (β, transitive Stam residual)

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

/-- **(α) 上界 — `∫ f log f` の L¹-LSC**: `f_n → pX` in L¹ ⟹ `liminf ∫ f_n log f_n ≥ ∫ pX log pX`.
Mathlib/in-tree 不在 (loogle: klDiv-LSC = Found 0、ConvexOn+lintegral = 0)。負値 negMulLog の
Fatou 適用は負部 `(f log f)₋` の n-一様可積分を要求し、これは de la VP wall (`wall:approx-identity-L1`)
と数学的に同型。新規壁を増やさず既存 wall に集約。
@residual(wall:approx-identity-L1) -/
theorem negMulLog_convDensity_liminf_lsc
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_lim : Tendsto u atTop (𝓝[Set.Ioi 0] 0)) :
    (∫ x, Real.negMulLog (pX x) ∂volume)
      ≤ Filter.liminf
          (fun n => ∫ x, Real.negMulLog
            (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x) ∂volume)
          atTop := by
  sorry  -- @residual(wall:approx-identity-L1)  ((α) = de la VP wall 同型)

/-- **(β) 下界 — 畳み込みでエントロピー非減少**: `h(pX) ≤ h(f_n)` 各 n。
EPI 経由 (`entropy_power_inequality` + `entropyPower_pos`)。transitive に
`stamToEPIBridge_holds` (`plan:epi-stam-to-conclusion-plan`) + Stam wall を消費。 -/
theorem negMulLog_convDensity_entropy_ge
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (n : ℕ) :
    (∫ x, Real.negMulLog (pX x) ∂volume)
      ≤ ∫ x, Real.negMulLog
          (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x) ∂volume := by
  sorry  -- @residual(plan:epi-stam-to-conclusion-plan)  ((β) = EPI transitive Stam residual)

end InformationTheory.Shannon
```

---

## §結論 (2 つの問いへの yes/no)

**サンドイッチ・ルートは de la VP wall より tractable ではない。採用見送りを推奨。**

1. **(α) `∫ f log f` の L¹-LSC を出す Mathlib 部品はあるか → NO。**
   klDiv の LSC は **Found 0** (`klDiv, LowerSemicontinuous` / `klDiv, Filter.liminf` / `klDiv, Filter.liminf, LE.le` の 3 query すべて 0; klDiv 名前 29 件に LSC/liminf 名皆無)。凸汎関数 L¹-LSC も **Found 0** (`ConvexOn, MeasureTheory.lintegral` = 0、`negMulLog, LowerSemicontinuous` = 0)。唯一の汎用部品 Fatou `lintegral_liminf_le` (genuine, `ℝ≥0∞`, IsCountablyGenerated) は negMulLog の **符号不定性**で直接乗らず、負部の n-一様可積分 (= de la VP wall `∫ G(|negMulLog f_n|) ≤ M` と同型) を前置要求する。Portmanteau LSC (`:496`) は連続 nonneg `f` + 測度側弱収束で構造が逆。**(α) は de la VP wall を別形で再要求するため、サンドイッチは壁を回避しない**。

2. **(β) `h(f_n) ≥ h(pX)` を出す in-tree/Mathlib 部品はあるか → 部品はあるが未閉 residual を背負う。**
   最短ルート = **EPI `entropy_power_inequality` (`:289`) + `entropyPower_pos` (`@audit:ok`) + `entropyPower_le_of_differentialEntropy_le` (genuine)**。`entropyPower(X+√tZ) ≥ entropyPower(X) + entropyPower(√tZ) ≥ entropyPower(X)` (正値落とし) で `h(f_n) ≥ h(pX)` が出る plumbing。だが EPI は **transitive に 2 つの未閉 residual** を消費: (i) `stamToEPIBridge_holds` (`plan:epi-stam-to-conclusion-plan`、sorry 未閉)、(ii) `IsStamInequalityResidual` 供給 = Stam wall (Mathlib `rg Stam` = 0 hit)。de Bruijn 積分版 monotone は in-tree 0 hit + FTC-2 が端点連続 (本壁) を前置で循環 (前回追認)。条件付け減少・直接 differential `h(X+Y)≥h(X)` は連続側で in-tree/Mathlib **不在**。

**総合判定 (de la VP wall との tractability 比較)**: サンドイッチは UI/UT 直結ルートを迂回するが、(α) で **de la VP wall と数学的に同型の klDiv-LSC moonshot** を、(β) で **Stam line の未閉 residual 2 本**を新たに引き込む。前回 de la VP wall が「真 moonshot 三重独立確定」だったのに対し、サンドイッチは **その moonshot を (α) でそのまま再要求しつつ (β) で別ラインの open residual に依存を増やす**ため、tractability は **改善せず悪化**。loogle authoritative (Found 0 明記): `InformationTheory.klDiv, LowerSemicontinuous` = **Found 0**、`InformationTheory.klDiv, Filter.liminf` = **Found 0**、`Real.negMulLog, LowerSemicontinuous` = **Found 0**、`ConvexOn, MeasureTheory.lintegral` = **Found 0**、`InformationTheory.klDiv, MeasureTheory.Measure.map` = **Found 0**。**撤退ライン発動: yes (追認)** — サンドイッチ採用見送り推奨、現行 `wall:approx-identity-L1` park 維持。
