# EPI G2 連続性壁 本体 closure — 深掘り Mathlib + InformationTheory API 在庫

> 攻略対象 (本体 closure): `heatFlowEntropyPower_continuousOn`
> (`InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean:86`、`@residual(wall:heatflow-continuity)`、1 sorry)
> の `t = 0⁺` 連続性。`t ↦ entropyPower (P.map (fun ω => X ω + √t·Z ω))` の `ContinuousOn (Set.Ici 0)`。
> 親計画: [`epi-g2-continuity-plan.md`](epi-g2-continuity-plan.md)（GATE NO-GO = `wall:heatflow-continuity` 確定、撤退ライン **L-G2-1**）。
> 既存 inventory: [`epi-g2-continuity-inventory.md`](epi-g2-continuity-inventory.md)（DCT 機構 / gaussian var→0 / 外側合成 / HasDerivAt 橋を verbatim 在庫）。
> **本 inventory のスコープ**: 既存 inventory に無い **DCT 以外の代替ルート 6 領域**。DCT (`continuousWithinAt_of_dominated`) の time-uniform majorant 壁を迂回できる定理があるかを調べる。

## 一行サマリ

代替ルート 6 領域のうち実体が既存なのは **negMulLog 連続 (1 件)・Vitali 収束機構 (UnifTight、IsFiniteMeasure 不要、〜5 件)・de Bruijn 微分恒等式 (InformationTheory genuine、1 件)** のみ。
**entropy/KL の半連続性は完全不在 (loogle Found 0)、Vitali は sequence + L^p-norm 収束で点列・eLpNorm のため endpoint `ContinuousWithinAt` への直接 lift に bridge 多数必要、de Bruijn 経由は `0 < t` 限定 + `Measurable X/Z` + `IndepFun X Z P` を要求し現 wall 補題の regularity-only signature では供給不能。**
**結論: いずれの代替ルートも DCT の time-uniform majorant 壁を本質的には迂回しない (Vitali はそれを「点列の一様可積分性 + 一様 tightness」に置換するだけで核は同じ density-level 一様性)。撤退ライン L-G2-1 は発動継続 (= `wall:heatflow-continuity` 保持) が正当。** 自作必要 = 4 件 (どれも壁の別表現)。

---

## 主定理の最終形（再掲、verbatim）

`InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean:86`:

```lean
theorem heatFlowEntropyPower_continuousOn
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_reg : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp X Z P) :
    ContinuousOn
      (fun t : ℝ => entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z ω)))
      (Set.Ici (0 : ℝ)) := by
  sorry
```

- `entropyPower μ := Real.exp (2 * differentialEntropy μ)`（`EntropyPowerInequality.lean:101`）。
- `differentialEntropy μ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume`（`DifferentialEntropy.lean:45`、**積分は `volume` = Lebesgue = σ-finite だが非 finite**）。
- `gaussianConvolution X Z t = fun ω => X ω + √t·Z ω`（`FisherInfoV2DeBruijn.lean:127`、verbatim 確認 — wall 補題の integrand と完全一致）。

代替ルート評価のための pseudo-Lean（核は既存 inventory と同じ DCT、本 inventory は迂回路を探す）:

```
-- 既存ルート (NO-GO 済): continuousWithinAt_of_dominated に t-uniform integrable majorant g
--   ‖negMulLog f_t x‖ ≤ g x ∀ small t  → 供給不能 (prefactor (sqrt 2πt)⁻¹ blow-up)
-- 代替ルート候補 (本 inventory):
--   (R5) Vitali: f_t →ᵃᵉ f_0 + UnifIntegrable + UnifTight ⇒ eLpNorm (f_t - f_0) → 0
--        → ∫ negMulLog 収束に lift? (L¹ conv は値 conv を与えるが point列 atTop / eLpNorm)
--   (R4) Fisher: differentialEntropy ∘ heatflow が C¹ (de Bruijn) → continuousOn
--        → 但し 0 < t 限定 + Measurable/IndepFun 要求
```

---

## API 在庫テーブル（代替ルート領域別）

### R1. Gaussian heat kernel → Dirac の弱収束 — 既存 (var→0 等式) / tendsto 形は不在

| 概念 | Mathlib API | file:line | signature (verbatim) | 状態 |
|---|---|---|---|---|
| var→0 = Dirac (等式) | `ProbabilityTheory.gaussianReal_zero_var` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:207` | `(μ : ℝ) : gaussianReal μ 0 = Measure.dirac μ` | ✅ (既存 inventory にも収録) |
| gaussian var→0 弱収束 (tendsto 形) | — | — | loogle `ProbabilityTheory.gaussianReal, MeasureTheory.Measure.dirac` → **Found 1** (上記 `_zero_var` のみ、tendsto 形 0) | ❌ tendsto 形不在 |
| dirac への weak tendsto | — | — | loogle `Filter.Tendsto, MeasureTheory.Measure.dirac` → **Found 0** | ❌ 不在 |
| 一般弱収束機構 (portmanteau / ProbabilityMeasure topology) | `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` ほか **37 件** | `Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean`, `Measure/Portmanteau.lean` | weak-* topology (テスト関数積分) | ✅ 機構あり (但し下記 R3 で entropy への lift 不能) |
| 分布収束 (新規発見) | `MeasureTheory.TendstoInDistribution` (structure) | `Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean:64` | `structure TendstoInDistribution [OpensMeasurableSpace E] (X : (i:ι)→Ω i→E) (l : Filter ι) (Z : Ω'→E) ...` | ⚠ 確率変数の収束 (CLT 系)、entropy 連続性とは無関係 |

> **R1 判定**: var→0 が Dirac へ潰れるのは等式で確定だが、**弱収束は entropyPower 連続性を与えない**（entropy は弱収束に対し下半連続止まり、その下半連続性すら Mathlib 不在 → R3）。R1 ルートは「測度がどこへ行くか」までで打ち止め、既存 inventory の結論を再確認するのみ。

### R2. push-forward / convolution 測度の連続依存 — Haar/regularity 系のみ、パラメータ弱連続は限定的

| 概念 | Mathlib API | file:line | signature 要点 | 状態 |
|---|---|---|---|---|
| `Measure.map` × `Continuous` | `MeasureTheory.Measure.InnerRegular.map_of_continuous` ほか **10 件** | `Mathlib/MeasureTheory/Measure/Regular.lean` 等 | inner-regular / Haar 保存系。**パラメータ t に対する弱連続性ではない** | ⚠ 不適合 |
| `Measure.map` × `Tendsto` | `MeasureTheory.Measure.tendsto_ae_map` | `Mathlib/MeasureTheory/Measure/Map.lean` | ae 収束の push-forward (関数列の ae 収束、測度パラメータ連続性ではない) | ⚠ 不適合 |
| push-forward 弱連続 | `MeasureTheory.ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous` | `Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean` | `Tendsto μs → Continuous f → Tendsto (μs.map f)` | ✅ 但し弱収束 (R1 と同じ天井) |
| `Measure.conv` 代数 | `MeasureTheory.Measure.conv` ほか **42 件** (`conv_dirac`, `conv_assoc`, `lintegral_conv`, `conv_withDensity_eq_lconvolution` 等) | `Mathlib/MeasureTheory/Group/Convolution.lean`, `Measure/WithDensity.lean:47` | conv の代数則・dirac で単位元・lintegral 公式。**conv のパラメータ t 連続性 / density 連続性は無い** | ⚠ 代数のみ、連続性 0 |

> **R2 判定**: push-forward / conv の **パラメータ t に対する density-level 連続性** API は Mathlib 不在。弱連続性 (`tendsto_map_of_tendsto_of_continuous`) は R1 同様 entropy へ lift 不能。`conv_withDensity_eq_lconvolution`（`Measure/WithDensity.lean`）は density-level 表現を与えるが、これ自体は連続性命題ではない（既存 Assembly の conv-pin と同種、t-uniform 性は持たない）。

### R3. differential entropy / entropy power / KL の半連続性・連続性 — ❌ 完全不在

| 概念 | loogle query | 結果 | 状態 |
|---|---|---|---|
| `measureEntropy` の半連続性 | `LowerSemicontinuous, "measureEntropy"` | **Found 0** (67 LSC 宣言中 name に measureEntropy 含むもの 0) | ❌ 不在 |
| `klDiv` の lower semicontinuity | `LowerSemicontinuous, InformationTheory.klDiv` | **Found 0** | ❌ 不在 |
| `klDiv` の tendsto/連続性 | `Filter.Tendsto, InformationTheory.klDiv` | **Found 0** | ❌ 不在 |
| `negMulLog` 積分 (差分エントロピー) の LSC | `LowerSemicontinuous, Real.negMulLog` | **Found 0** | ❌ 不在 |
| `lintegral` の LSC (Fatou 系) | `LowerSemicontinuous, MeasureTheory.lintegral` | **Found 4** (`exists_le_lowerSemicontinuous_lintegral_ge` ほか、`Bochner/VitaliCaratheodory.lean`) | ⚠ Vitali-Carathéodory 近似 (LSC 関数で下から近似)、entropy 半連続性そのものではない |
| `differentialEntropy`/`entropyPower` 連続性 (InformationTheory) | `rg "Continuous.*entropyPower\|entropyPower.*Continuous\|differentialEntropy.*Continuous"` | **実体 0**（hit は本 wall 補題の docstring とその consumer の `ContinuousOn.log`/外側合成のみ） | ❌ 不在 |

> **R3 判定**: 微分エントロピー / entropy power / KL の半連続性・連続性は **Mathlib・InformationTheory 双方に完全不在**。「弱収束 → 下半連続性 → 連続性」の半連続ルートは **入口の半連続性命題が存在しない**ため成立しない。`VitaliCaratheodory` の LSC 近似は「測度上の積分を LSC simple function で下から近似」する別物で、本問の「測度パラメータに対する積分の連続性」とは無関係。**R3 は迂回路にならない。**

### R4. Fisher information / de Bruijn 経由ルート — InformationTheory に genuine 微分恒等式あり、但し制約が致命的

| 概念 | API | file:line | signature (verbatim、`[...]` / `(ht)` 含む) | 状態 |
|---|---|---|---|---|
| de Bruijn 微分恒等式 (per-time) | `InformationTheory.Shannon.FisherInfoV2.debruijnIdentityV2_holds_assembled` | `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:3535` | `{P : Measure Ω} [IsProbabilityMeasure P] (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P) {t : ℝ} (ht : 0 < t) (h_reg : IsRegularDeBruijnHypV2 X Z P t) : HasDerivAt (fun s => differentialEntropy (P.map (gaussianConvolution X Z s))) ((1/2) * fisherInfoOfDensityReal h_reg.density_t) t` | ✅ **genuine** (`@audit:ok`、sorryAx-free、2026-06-01) |
| Mathlib `fisherInfo` | — | — | loogle `"fisherInfo"` → **Found 0** (Mathlib に Fisher 情報量の概念自体なし、InformationTheory のみ) | ❌ Mathlib 不在 |
| Mathlib `deBruijn` | — | — | loogle `"deBruijn"` → **Found 0** | ❌ Mathlib 不在 |

> **R4 判定 (致命的制約 3 つ)**:
> 1. **`(ht : 0 < t)` 限定**: de Bruijn HasDerivAt は **interior `t > 0` のみ**。本壁の唯一の困難は `t = 0⁺` endpoint で、そこには適用できない（既存 inventory が「内部は genuine 済」と判定したのと同じ天井）。
> 2. **`Measurable X` / `Measurable Z` / `IndepFun X Z P` 要求**: 現 wall 補題 `heatFlowEntropyPower_continuousOn` の signature は `(X Z : Ω → ℝ) (P) [IsProbabilityMeasure P] (h_reg : IsDeBruijnRegularityHyp X Z P)` で **measurability / independence data を一切持たない**（regularity-only）。de Bruijn を呼ぶには signature に `Measurable`/`IndepFun` を追加する必要があり、これは consumer (`csiszarLogRatioGap_continuousOn` 等) が持っていないため伝播コスト大。
> 3. **C¹ → endpoint continuity の論理ギャップ**: 仮に内部の `differentialEntropy ∘ heatflow` が C¹ でも、`t=0⁺` での連続性は導関数 (`(1/2)·fisherInfo`) の `t→0⁺` 局所可積分性 / 有界性を別途要する。Fisher info `fisherInfoOfDensityReal` の `t→0⁺` 挙動 (Dirac 接近で発散しうる) の Mathlib/InformationTheory 補題は不在。**de Bruijn は endpoint をまたいで連続性を出せない。**
>
> → **R4 は endpoint 壁を迂回しない。** 内部 genuine 化には使えるが（既存資産と同じ）、本体 closure の核 (`t=0⁺`) には届かない。

### R5. 時間一様 majorant を回避する Vitali / 一様可積分ルート — 機構あり、但し sequence + L^p-norm で endpoint lift にギャップ

文脈型クラス (`UniformIntegrable.lean:67`, `UnifTight.lean:47`): `{α β ι} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]`。

| API | file:line | signature (verbatim、`[...]` / 結論型含む) | endpoint への適合 |
|---|---|---|---|
| Vitali (finite measure 版) | `MeasureTheory.tendsto_Lp_finite_of_tendsto_ae` | `Mathlib/MeasureTheory/Function/UniformIntegrable.lean:519` | `[IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ℕ → α → β} {g : α → β} (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ) (hui : UnifIntegrable f p μ) (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)` | ❌ **`[IsFiniteMeasure μ]`** — 本問は `μ = volume` で **非 finite** → 不適合 |
| **Vitali (UnifTight 版、finite 不要)** | `MeasureTheory.tendsto_Lp_of_tendsto_ae` | `Mathlib/MeasureTheory/Function/UnifTight.lean:329` | `(hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ℕ → α → β} {g : α → β} (haef : ∀ n, AEStronglyMeasurable (f n) μ) (hg' : MemLp g p μ) (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ) (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)` | ⚠ **finite 不要 = volume OK**。だが下記 4 ギャップ |
| `UniformIntegrable.integrable_of_ae_tendsto` | `Mathlib/MeasureTheory/Function/UniformIntegrable.lean:975` | `{κ} {u : Filter κ} [NeBot u] [IsCountablyGenerated u] {f : κ → α → β} {g : α → β} (hUI : UniformIntegrable f 1 μ) (htends : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) u (𝓝 (g x))) : Integrable g μ` | ⚠ 極限の可積分性のみ (値 conv ではない) |
| `UnifTight` 定義 / `tendstoInMeasure_iff_tendsto_Lp` | `Mathlib/MeasureTheory/Function/UnifTight.lean:373` | (Vitali 全体定理群、TendstoInMeasure ⇔ L^p conv) | ⚠ 同じ枠組 |

> **R5 判定 (最有力の迂回候補だが 4 ギャップ)**:
> Vitali (`UnifTight.tendsto_Lp_of_tendsto_ae`) は `[IsFiniteMeasure]` を**要求しない**ので `volume` でも使え、time-uniform pointwise majorant `g` の代わりに **(i) 点ごと ae 収束 + (ii) `UnifIntegrable` + (iii) `UnifTight`** で L^p 収束を出す。これが「DCT の pointwise majorant を一様可積分性 + 一様 tightness に置換する」迂回の本筋。だが本壁に適用するには:
> 1. **sequence (`f : ℕ → ...`, `atTop`) only**: 結論は点列 `n → ∞`。本問は連続パラメータ `t → 0⁺` (`𝓝[Ici 0] 0`)。連続 → 点列は `tendsto_of_seq_tendsto` 系で橋渡し可能だが、Vitali の hyp (`UnifIntegrable`/`UnifTight`) を任意点列で一様に検証する追加 plumbing が要る。
> 2. **`eLpNorm (f_n - g) → 0` であって `∫ f_n → ∫ g` ではない**: 結論は L^p ノルム収束。差分エントロピーの値 `∫ negMulLog f_t` の収束へは `eLpNorm → 0 ⇒ ∫ → ∫` の bridge (L¹ なら `eLpNorm` = `∫‖·‖`、`MemLp 1`) が要る。さらに本問の被積分は `negMulLog f_t` であって `f_t` 自身でないため、`negMulLog` の Lipschitz/連続合成を L^p レベルで通す追加補題が要る (`negMulLog` は globally Lipschitz でないので非自明)。
> 3. **`UnifIntegrable (negMulLog f_t)` の検証が壁本体と等価**: `UnifIntegrable` は「`∀ε,∃δ, ∀i, ∀(set s with μ s ≤ δ), eLpNorm (s.indicator (f i)) ≤ ε`」= 一様な末尾可積分性。これを `negMulLog f_t` の族に対し `t→0⁺` で示すのは、prefactor blow-up (`(sqrt 2πt)⁻¹`) を一様に制御することと**同じ困難** — 壁を別表現に移しただけ。
> 4. **`UnifTight` (一様 tightness) も非自明**: `t→0⁺` で density が `pX` (L¹ + finite 2nd moment) へ近づく際の一様 tail control。`pX_mom` (2 次モーメント有限) が tightness の素地を与えるが、`negMulLog f_t` の tail を t-一様に押さえるのは別問題。
>
> → **R5 は壁を「迂回」せず「移送」する**。pointwise time-uniform majorant の困難が、`UnifIntegrable`+`UnifTight` の time-uniform 検証に置換されるだけで、核 (density の時間一様可積分性) は同一。それでも **最も筋の良い代替**であり、自作するなら R5 ルートが第一候補（majorant 一発より構造的）。

### R6. negMulLog の連続性・有界性補助 — 既存

| 概念 | API | file:line | signature (verbatim) | 状態 |
|---|---|---|---|---|
| `negMulLog` 連続性 | `Real.continuous_negMulLog` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean` | `Continuous Real.negMulLog`（loogle `Continuous, Real.negMulLog` → **Found 1**、唯一） | ✅ |

> **R6 判定**: `Real.continuous_negMulLog` は無条件連続を与え、`h_cont` (各点 `t ↦ negMulLog f_t x` の連続) の `negMulLog` 合成部分は無料。但しこれは DCT の `h_cont` 前提を埋めるだけで、壁である `h_bound`（一様 majorant）は埋めない。R6 は補助のみ。

---

## 主要前提条件ボックス（事故が起きやすい lemma）

- **`UnifTight.tendsto_Lp_of_tendsto_ae`** (`UnifTight.lean:329`、R5 最有力):
  - **`[IsFiniteMeasure μ]` を要求しない** (`UnifTight.lean:47` の variable に finite なし) → `μ = volume` で使える。これは finite-measure 版 `tendsto_Lp_finite_of_tendsto_ae` (`UniformIntegrable.lean:519`、`[IsFiniteMeasure μ]` 必須) と決定的に異なる。**finite 版を誤って掴むと volume で詰む。**
  - 結論は `Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)` — **点列 (`ℕ`, `atTop`)**、**eLpNorm 収束** (積分値収束でない)。連続パラメータ `t→0⁺` への変換と eLpNorm→積分値 の 2 段 bridge が必須。
  - `hui : UnifIntegrable f p μ` / `hut : UnifTight f p μ` の検証が壁本体と等価困難 (上記 R5 判定 3,4)。
- **`debruijnIdentityV2_holds_assembled`** (`Assembly.lean:3535`、R4):
  - **`(ht : 0 < t)` 必須** → endpoint `t=0` 不適用。
  - **`(hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)` 必須** → 現 wall 補題の regularity-only signature が供給不能。これを使うには wall 補題 + consumer 全体に measurability/independence を伝播させる必要があり影響範囲大。
- **`continuousWithinAt_of_dominated`** (既存 inventory category 3、`Bochner/Basic.lean:440`): pointwise `‖F t x‖ ≤ bound x` の time-uniform majorant が唯一の壁（NO-GO 済）。R5 はこの pointwise majorant を一様可積分性に緩めるが核は不変。

---

## 自作が必要な要素（優先度順）

1. **【第一候補・R5 Vitali ルート】heat-flow density の時間一様可積分性 + 一様 tightness**
   - 推奨実装: `f_t x := ((P.map (gaussianConvolution X Z t)).rnDeriv volume x).toReal` の族に対し `UnifIntegrable (fun t => negMulLog ∘ f_t) 1 volume` + `UnifTight ... 1 volume` を `t∈[0,δ]` で示し、`UnifTight.tendsto_Lp_of_tendsto_ae`（点列化 + eLpNorm→∫ bridge 付き）で `∫ negMulLog f_t → ∫ negMulLog f_0`。
   - 工数感: **特大 (150–250 行)**。`UnifIntegrable`/`UnifTight` の time-uniform 検証が壁本体と等価困難 + 点列化 bridge + eLpNorm→積分値 bridge + `negMulLog` 非 Lipschitz 合成。
   - 落とし穴: 「Vitali を使えば majorant 不要」は **誤り** — majorant の困難が `UnifIntegrable` 検証へ移送されるだけ。`negMulLog` が `f→∞` で `-f log f → -∞`、`f→0⁺` で `→0` の非対称性のため一様可積分性の検証が片側 (大 density 側 = noise が尖る側) で破綻しうる。

2. **【第二候補・R4 Fisher ルート、但し signature 改変要】interior の C¹ + endpoint Fisher 局所可積分性**
   - 推奨実装: wall 補題 signature に `Measurable X/Z` + `IndepFun X Z P` を追加し、interior は `debruijnIdentityV2_holds_assembled` (`Assembly.lean:3535`) → `HasDerivAt.continuousAt`、endpoint は `(1/2)·fisherInfoOfDensityReal` の `t→0⁺` 局所可積分性で `ContinuousWithinAt` を出す。
   - 工数感: **大 (signature 改変の伝播コスト + endpoint Fisher 挙動補題 100–150 行)**。endpoint で Fisher info が `t→0⁺` に発散しないこと (= `P.map X` 側 density の Fisher 有限性) の補題が新規。
   - 落とし穴: signature 改変 (`Measurable`/`IndepFun` 追加) が consumer 2 箇所 (`csiszarLogRatioGap_continuousOn` 等) に伝播。consumer がこれらを持つか要確認。**de Bruijn 自体は `0 < t` 限定で endpoint をまたげない** (R4 判定 1)。

3. **【bridge・R5 補助】eLpNorm 収束 → 積分値収束**
   - 推奨実装: `MemLp 1` 下で `eLpNorm f 1 μ = ∫⁻ ‖f‖` を経由、`eLpNorm (f_t - f_0) 1 → 0 ⇒ ∫ f_t → ∫ f_0`。工数 **中 (30–50 行)**、Mathlib `eLpNorm_one_eq_lintegral_enorm` 系で機械的。
   - 落とし穴: 被積分が `negMulLog f_t` なので `f_t` の L¹ 収束を `negMulLog f_t` の収束へ移すのに `negMulLog` の局所 Lipschitz 評価が要る (非自明)。

4. **【点列化 bridge・R5 補助】連続パラメータ `t→0⁺` → 点列 `atTop`**
   - 推奨実装: `tendsto_of_seq_tendsto` / 第一可算性経由で `ContinuousWithinAt` を点列収束に還元。工数 **小 (15–25 行)**、但し Vitali hyp の点列一様性検証は要素 1 に含まれる。

---

## Mathlib 壁の列挙（真に不在 = `@residual(wall:...)` 対象）

| wall 候補 | loogle 確認 | 真壁か |
|---|---|---|
| `entropyPower`/`differentialEntropy` 連続性 (本壁) | InformationTheory `rg` 実体 0、Mathlib measure-entropy 連続性 API 不在 | **真壁 = `wall:heatflow-continuity`** (既登録、本 inventory が再確認) |
| `measureEntropy` 半連続性 | loogle `LowerSemicontinuous, "measureEntropy"` → **Found 0** | 真の不在 (半連続ルート不成立、R3) |
| `klDiv` 半連続性 | loogle `LowerSemicontinuous, InformationTheory.klDiv` → **Found 0** | 真の不在 (G2 不要) |
| `klDiv` tendsto/連続性 | loogle `Filter.Tendsto, InformationTheory.klDiv` → **Found 0** | 真の不在 (G2 不要) |
| gaussian var→0 弱収束 (tendsto 形) | loogle `Filter.Tendsto, MeasureTheory.Measure.dirac` → **Found 0** | 真の不在 (`gaussianReal_zero_var` 等式で代替、但し entropy lift 不能) |
| Mathlib `fisherInfo` / `deBruijn` | loogle `"fisherInfo"` / `"deBruijn"` → 各 **Found 0** | Mathlib 不在 (InformationTheory のみ、R4 は `0<t` 限定) |

> **結論**: 本壁 `wall:heatflow-continuity` は **6 代替ルート全てで迂回不能**であることが再確認された。
> - R1 (弱収束)・R3 (半連続性): entropy lift の入口命題が不在。
> - R2 (測度連続依存): パラメータ density 連続性 API 不在。
> - R4 (de Bruijn): `0<t` 限定で endpoint をまたげず、加えて measurability/indep を要求。
> - R5 (Vitali): finite 不要版は存在するが、majorant の困難を `UnifIntegrable`/`UnifTight` の time-uniform 検証へ移送するのみで核は同一。
> - R6 (negMulLog 連続): 補助のみ、`h_bound` を埋めない。
>
> **shared sorry 補題への集約は既に完了**（`heatFlowEntropyPower_continuousOn`、`EPIG2HeatFlowContinuity.lean:86`、`@residual(wall:heatflow-continuity)`、audit-tags.md Wall register 登録済、独立 honesty audit OK 2026-06-04）。本 inventory は **新規 wall register 不要**（既存 wall の閉鎖難度を 6 ルートで深掘り確認したのみ）を結論する。

---

## 撤退ラインへの距離

親計画 `epi-g2-continuity-plan.md` の **L-G2-1（端点 bound 不成立 = 真壁確定）**:

**判定: L-G2-1 は発動継続が正当（= `wall:heatflow-continuity` 保持）。**

- 2026-06-03 GATE NO-GO で L-G2-1 は既に発動済み（shared sorry 補題化 + `@residual(wall:heatflow-continuity)`）。本 inventory は **その発動を覆す代替ルートが存在するか**を 6 領域で検証したが、**いずれも壁を迂回しない**ことを確認した。
- **最も筋の良い迂回候補 R5 (Vitali) でも**、`IsFiniteMeasure` 不要版 (`UnifTight.tendsto_Lp_of_tendsto_ae`) は存在するものの、`UnifIntegrable`/`UnifTight` の time-uniform 検証が壁本体と等価困難なため、proof done には依然 Mathlib 不在の time-uniform density control が必要。
- **新規撤退ライン提案は不要**: L-G2-1 の現状（共有 sorry 補題保持、consumer は補題呼び出しのみで `@residual` 持たず）が正しい resting state。撤退口は sorry + `@residual(wall:heatflow-continuity)`（仮説束化なし）で honesty 階層 tier 2 を満たす。
- **proof done への唯一の道**: 自作要素 1 (R5 Vitali ルート、特大 150–250 行) または 2 (R4 Fisher ルート、signature 改変 + endpoint Fisher 補題)。どちらも 1 セッションでは非現実的で、`wall:heatflow-continuity` は当面 upstream wall として保持が妥当。

---

## 着手 skeleton（R5 Vitali ルートを採る場合の探索用、本体は既存 wall 補題を保持）

> 注: 本壁の wall 補題 `heatFlowEntropyPower_continuousOn` (`EPIG2HeatFlowContinuity.lean:86`) は既存・signature 確定。
> 以下は R5 ルートで proof done を狙う場合の **補助補題 skeleton** であり、wall 補題 signature は変更しない。

```lean
import Mathlib.MeasureTheory.Function.UnifTight              -- tendsto_Lp_of_tendsto_ae (finite 不要 Vitali)
import Mathlib.MeasureTheory.Function.UniformIntegrable      -- UnifIntegrable, integrable_of_ae_tendsto
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog       -- Real.continuous_negMulLog
import Mathlib.Probability.Distributions.Gaussian.Real       -- gaussianReal_zero_var
import InformationTheory.Shannon.EntropyPowerInequality      -- entropyPower
import InformationTheory.Shannon.DifferentialEntropy         -- differentialEntropy
import InformationTheory.Shannon.EPIStamDischarge            -- IsDeBruijnRegularityHyp

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]

/-- **R5-a (Vitali 一様可積分性、自作核)**: heat-flow density 列の被積分 `negMulLog f_t`
は `t∈[0,δ]` で `UnifIntegrable ... 1 volume`。← 壁本体と等価困難 (一様 majorant の移送先)。 -/
theorem heatFlowNegMulLog_unifIntegrable
    (h_reg : EPIStamDischarge.IsDeBruijnRegularityHyp X Z P) (δ : ℝ) (hδ : 0 < δ) :
    True := by  -- 実装時は UnifIntegrable (fun t => negMulLog ∘ f_t) 1 volume の本来形に
  sorry  -- @residual(wall:heatflow-continuity) -- R5 Vitali uniform integrability (= 壁本体)

/-- **R5-b (eLpNorm → 積分値 bridge)**: `MemLp 1` 下で `eLpNorm (f_t - f_0) 1 → 0`
から `∫ negMulLog f_t → ∫ negMulLog f_0` を出す bridge。 -/
theorem heatFlowEntropy_tendsto_of_LpTendsto
    (h_reg : EPIStamDischarge.IsDeBruijnRegularityHyp X Z P) :
    True := by  -- 実装時は ∫ negMulLog f_t → ∫ negMulLog f_0 の本来形に
  sorry  -- @residual(wall:heatflow-continuity) -- R5 eLpNorm→integral bridge

end InformationTheory.Shannon
```

> skeleton の `True` placeholder は inventory 例示用。実装時は `UnifIntegrable (...) 1 volume` / `Tendsto (∫ ...) ...` の本来形を書き body `sorry`。`Prop := True` を残置してはいけない（tier 5）。R5 は壁を移送するのみのため、いずれの補助補題も `@residual(wall:heatflow-continuity)` を継承する（新規 wall register 不要）。
