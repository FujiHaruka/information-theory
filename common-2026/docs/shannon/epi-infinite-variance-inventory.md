# EPI 無限分散 a.c. ケース — Mathlib + in-tree API 在庫調査

> **調査日**: 2026-06-07。
> **対象壁**: `@residual(wall:epi-infinite-variance-classical)` =
> `entropyPowerExt_add_ge_infinite_variance` (`InformationTheory/Shannon/EPICase1SmoothingLimit.lean:1407`)。
> 古典 EPI `Nₑ(X+Y) ≥ Nₑ(X)+Nₑ(Y)` を **両 a.c. + 両有限微分エントロピー** だが **有限分散仮定なし**
> (`h_infvar : ¬(Integrable (X²) P ∧ Integrable (Y²) P)`) で証明したい。
> 本ファイルは **在庫調査のみ** (実装・計画起草はしない)。
> last-verified commit: 調査時 HEAD (`dffab38`)。

## 一行サマリ

**(A) 代替直接ルートは存在しない (壁主張裏取り)**: sharp Young (Beckner-Brascamp-Lieb 定数)・Brascamp-Lieb・Riesz 対称減少再配置・Rényi entropy・Prékopa-Leindler はいずれも Mathlib 完全不在 (loogle 5 系統で確認、bare-identifier ヒットは全て無関係: `young`102件=スカラー Young、`Lieb`系=Lieb 凹性、`Riesz`45件=Riesz lemma/extension、`rearrangement`8件=Monovary 数列並替)。**(B) truncation/approximation ルートは部品の汎用機構 (Fatou・weak conv 定義・monotone convergence) は約 50% 既存だが、核心の「entropyPower / KL の弱収束下半連続性」と「Gaussian 畳み込みの t→0⁺ 弱収束」が両方 Mathlib 不在 (loogle Found 0)、さらに `IndepFun.variance_add` が `MemLp 2` (有限分散) を要求するため truncation の各近似ステップで `entropy_power_add_ge_of_finite_variance` を呼ぶには truncated X の有限分散が必要 (これは truncation で作れる) だが最終極限を取る半連続性が無い。** 自作必要 = 重い新規補題 2〜3 本 (弱収束 LSC bridge + 近似単位元弱収束 + truncation 配線)、moonshot 規模。**撤退ライン**: 親 `epi-unconditional-moonshot-plan` の **L-Uncond-3-scope (方針 X 縮退)** に**触れる — 既に発動済の壁** (本壁 `wall:epi-infinite-variance-classical` 自体が L-Uncond-3-scope の honest 着地点)。**最危険な発見: `IndepFun.variance_add` (`Mathlib/Probability/Moments/Variance.lean:406`) が `(hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)` を要求 — 無限分散では `MemLp 2` が偽なので、有限分散ルートの分散加法すら無限分散入力には直接適用できない (truncation で迂回するしかない)。**

---

## 主定理の最終形 (再掲)

`EPICase1SmoothingLimit.lean:1407-1416` (verbatim):

```lean
theorem entropyPowerExt_add_ge_infinite_variance
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (h_infvar : ¬ (Integrable (fun ω => (X ω) ^ 2) P ∧ Integrable (fun ω => (Y ω) ^ 2) P)) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by sorry
```

教科書 EPI の 2 つの証明路 (pseudo-Lean):

```text
ルート (A) sharp Young 直接路 (Lieb 1978 / Cover-Thomas 17.8):
  Nₑ(X+Y) ≥ Nₑ(X)+Nₑ(Y) を Beckner-Brascamp-Lieb の sharp 畳み込み不等式
  ‖pX ∗ pY‖_r ≤ C(p,q,r)·‖pX‖_p·‖pY‖_q で直接出す。有限分散を一切使わない。
  → 必要 API: sharp Young (定数つき) / Riesz 対称減少再配置 / Brascamp-Lieb。
    全て Mathlib 不在 (§A)。

ルート (B) truncation/approximation 路:
  1. X を |X|≤R に truncate → X_R (有限分散・有限エントロピー)。同様に Y_R。
  2. 各 R で finite-variance EPI: Nₑ(X_R+Y_R) ≥ Nₑ(X_R)+Nₑ(Y_R)
       (= entropyPowerExt_add_ge_of_finite_variance、:1351、既存)
  3. R→∞ で極限を取る:
       RHS: Nₑ(X_R) → Nₑ(X) の収束 (truncation の弱収束 + entropyPower 連続性)
       LHS: liminf を取り Nₑ(X+Y) ≤ liminf Nₑ(X_R+Y_R) (下半連続性)
  → 必要 API: entropyPower の弱収束 LSC + truncation 測度の弱収束。両方 Mathlib 不在 (§B)。
```

---

## §A. 代替直接ルート (壁主張の裏取り — Found 0 を期待し conclusion-shape 二段検索で確認)

すべて loogle で確認。bare-identifier の false-negative を避けるため、bare-string 検索 + conclusion-shape の二段で確認した。**bare-name ヒットは全て無関係** (項目ごとに明記)。

| # | 主張 (探したもの) | loogle query / 結果 | 判定 | EPI への効き方 |
|---|---|---|---|---|
| A-1a | conv の L^p Young (通常版) | `MeasureTheory.convolution, MeasureTheory.eLpNorm` → **Found 0** | ❌ 不在 | ルート A の出発点が無い |
| A-1b | conv の MemLp 評価 | `MeasureTheory.convolution, MeasureTheory.MemLp` → **Found 0** | ❌ 不在 | 同上 |
| A-1c | **conclusion-shape**: `eLpNorm (conv …) ≤` | `\|- MeasureTheory.eLpNorm (MeasureTheory.convolution _ _ _ _) _ _ ≤ _` → **Found 0 declarations mentioning LE.le, convolution, ENNReal, eLpNorm; Of these, 0 match** | ❌ 不在 (二段確認済) | bare-query の false-negative でないことを確認 |
| A-1d | sharp Young (スカラー罠) | `"young"` → **Found 102**。`Real.young_inequality` / `ENNReal.young_inequality` / `NNReal.young_inequality` / `YoungDiagram` 系 | ❌ **無関係** | これらは `a·b ≤ aᵖ/p + bᵍ/q` の**スカラー** Young (Hölder 双対) であって**畳み込み** Young ではない。sharp 定数 (Beckner) も無し |
| A-2a | Brascamp-Lieb (CamelCase) | `"BrascampLieb"` → **Found 0 declarations whose name contains "BrascampLieb"** | ❌ 不在 | ルート A の一般化が無い |
| A-2b | Brascamp (部分一致) | `"Brascamp"` → **Found 0** | ❌ 不在 | 同上。`Lieb` 単独 bare-name は 128 件返すが全て **Lieb 凹性/Lieb-Thirring 等で無関係** (epi-facts.md 既記載の罠) |
| A-3a | rearrangement (対称減少再配置) | `"rearrangement"` → **Found 8**。全て `Monovary` 系 (`antivary_iff_mul_rearrangement` 等、`Mathlib.Algebra.Order.Monovary`) | ❌ **無関係** | これらは**数列の単調並べ替え**であって関数の対称減少再配置 (Riesz rearrangement) ではない |
| A-3b | Riesz (対称減少再配置) | `"Riesz"` → **Found 45**。`riesz_lemma` (`Mathlib.Analysis.Normed.Module.RieszLemma`) / `RieszExtension` (凸錐) / `herglotzRieszKernel` (Poisson 核) | ❌ **無関係** | Riesz rearrangement inequality (対称減少再配置の畳み込み不等式) は Mathlib に**無い** (45件は functional analysis / 凸解析 / 複素解析で別物) |
| A-4a | Rényi entropy (CamelCase) | `"Renyi"` → **Found 0** | ❌ 不在 | Rényi entropy 経由の EPI 別証も不可 |
| A-4b | rényi (小文字) | `"renyi"` → **Found 0** | ❌ 不在 | 同上 |
| A-5a | Prékopa-Leindler | `"PrekopaLeindler"` → **Found 0** | ❌ 不在 | log-concave 経由 EPI 別証も不可 |
| A-5b | Prékopa (部分一致) | `"Prekopa"` / `"prekopa"` → **Found 0** | ❌ 不在 | 同上 |
| A-6 | **(追加) log-Sobolev / Gross LSI** (別証路) | `"logSobolev"` → **Found 0**; `"LogSobolev"` → **Found 0** | ❌ 不在 | LSI ⟹ EPI の Gross 路も不可 |
| A-7 | Mathlib `entropyPower` / `fisherInformation` | `"entropyPower"` → **Found 0**; `"fisherInformation"` → **Found 0** | ❌ project-local | entropy power / Fisher info の Mathlib 一般化は無い (既知、in-tree 定義のみ) |

### A 群の結論

**ルート A (sharp Young / Brascamp-Lieb / 対称減少再配置による直接証明) は Mathlib に部品ゼロ。** これは壁 docstring (`:1395`「Lieb's sharp Young inequality / Brascamp-Lieb rearrangement, none of which is present in Mathlib」) の主張を **二段検索で裏取り済**。`Mathlib.Analysis.Convolution` の `MeasureTheory.convolution` は**関数値 (内積空間値) の畳み込み**で、L^p Young 評価 (`eLpNorm`/`MemLp` 評価) を一切持たない (Found 0)。`convolution, LE.le` の 7 件は `dist_convolution_le` / `convolution_mono_right` 系の**点ごと評価**であって L^p ノルム Young ではなく、`convolution, Continuous` の 10 件は `HasCompactSupport.continuous_convolution_*` / `BddAbove.continuous_convolution_*_of_integrable` で**片側にコンパクト台/有界性を要求**し一般 a.c. 密度には効かない (`epi-finitevar-hent-sum-inventory.md` の Mathlib convolution 注記と整合)。

**反証義務 (過大評価対策、CLAUDE.md「壁と断じる側」)**: loogle Found 0 (必要条件) に加え、(a) conclusion-shape 二段検索を A-1c で実施 (bare-query false-negative 排除)、(b) **template lemma を 1 本挙げて self-build 行数見積り** → sharp Young 不等式 (Beckner 1975 の定数 `(Aₚ Aₑ / Aᵣ)`、`Aₚ = (pᵖ/p'ᵖ')^{1/2}` 形) を Mathlib 部品ゼロから自作するのは **対称減少再配置 (Riesz rearrangement) + Brascamp-Lieb 双対 + ガウス最適化** の数百〜千行規模で、template すら立たない。よって **ルート A は genuine Mathlib 壁** (大規模 gap、closeable だが moonshot 1 本分以上)。

---

## §B. truncation/approximation ルートに必要な収束系 (代替本命)

### B-1. 既存 (汎用機構、✅)

| # | 概念 | Mathlib API | file:line | `[...]` 前提 + signature verbatim | 結論形 verbatim | EPI での扱い |
|---|---|---|---|---|---|---|
| B6a | 弱収束 ↔ 有界連続関数積分収束 | `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` | `Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean:346` | `theorem tendsto_iff_forall_integral_tendsto {γ : Type*} {F : Filter γ} {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}` (section 変数 `{Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]`) | `Tendsto μs F (𝓝 μ) ↔ ∀ f : Ω →ᵇ ℝ, Tendsto (fun i ↦ ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω)))` | 弱収束の定義出口。`negMulLog` は有界連続でない (`x→0⁺` で発散、`x→∞` で `-∞`) ので**直接は使えない** (portmanteau-LSC bridge が要る、§B-2 不在) |
| B9a | Fatou (liminf 版) | `MeasureTheory.lintegral_liminf_le` | `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:231` | `theorem lintegral_liminf_le {ι : Type*} {f : ι → α → ℝ≥0∞} {u : Filter ι} [IsCountablyGenerated u] (h_meas : ∀ i, Measurable (f i))` (section `{α} [MeasurableSpace α] {μ : Measure α}`) | `∫⁻ a, liminf (fun i => f i a) u ∂μ ≤ liminf (fun i => ∫⁻ a, f i a ∂μ) u` | LSC を density a.e. 収束から出す核 (in-tree `klDiv_le_liminf_of_ae_tendsto` が既使用) |
| B8a | 単調収束 (iSup) | `MeasureTheory.lintegral_iSup` | `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean` (loogle Found 1) | (section `{α} [MeasurableSpace α] {μ}`) — iSup over monotone measurable seq | `∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ` | truncation の monotone limit に |
| B8b | 単調 lintegral 収束 | `MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone` | `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:113` | `theorem lintegral_tendsto_of_tendsto_of_monotone {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞} (hf : ∀ n, AEMeasurable (f n) μ) (h_mono : ∀ᵐ x ∂μ, Monotone fun n => f n x) (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 <| F x))` | `Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 <| ∫⁻ x, F x ∂μ)` | truncated density の単調収束 (ℕ-indexed) |
| B8b' | 反単調 lintegral 収束 | `MeasureTheory.lintegral_tendsto_of_tendsto_of_antitone` | `Mathlib/MeasureTheory/Integral/Lebesgue/Sub.lean` (loogle Found 1) | (12 件 `lintegral_tendsto` 群の 1 つ) | antitone 版 | 同上、向き別 |
| B8c | 優収束 (Bochner) | `MeasureTheory.tendsto_integral_of_dominated_convergence` | `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean` (loogle Found 1) | dominated convergence theorem (Bochner ∫) | `Tendsto (fun n => ∫ x, f n x ∂μ) F (𝓝 (∫ x, g x ∂μ))` | truncated entropy 積分の極限 (支配関数あれば) |
| B-conv-ac | conv の a.c. 伝播 | `MeasureTheory.Measure.conv_absolutelyContinuous` (= `mconv_absolutelyContinuous` の `@[to_additive]`) | `Mathlib/MeasureTheory/Group/Convolution.lean:165-167` | `@[to_additive] theorem mconv_absolutelyContinuous [MeasurableMul₂ M] {μ ν ρ : Measure M} [IsMulLeftInvariant ρ] [SFinite ν] (hν : ν ≪ ρ)` | `μ ∗ₘ ν ≪ ρ` | X+Y の a.c. (既に `map_add_absolutelyContinuous` で in-tree 利用)。⚠ **a.c. を右因子からのみ伝播** (`conv_comm` を 1 段噛む) |
| B-rn-conv | conv の rnDeriv | `MeasureTheory.rnDeriv_conv` / `rnDeriv_conv'` / `conv_eq_withDensity_lconvolution_rnDeriv` / `HaveLebesgueDecomposition.conv` | `Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean` (loogle: conv+AbsolutelyContinuous で 5 件、`@[to_additive]` 由来で bare-name grep 不可) | (multiplicative 版から to_additive 生成) | conv 測度の rnDeriv = lconvolution | 密度表現の橋 |

### B-2. 核心命題 — entropy / KL の弱収束 LSC (**Mathlib 完全不在、loogle Found 0**)

| # | 概念 (探したもの) | loogle query | 結果 | EPI での扱い |
|---|---|---|---|---|
| B7a | KL の下半連続性 | `InformationTheory.klDiv, LowerSemicontinuous` | **Found 0 declarations mentioning LowerSemicontinuous and InformationTheory.klDiv** | ❌ 不在 → ルート B step 3 (LHS LSC) の核が無い |
| B7b | KL ≤ liminf (汎用) | `InformationTheory.klDiv, Filter.liminf` | **Found 0 declarations mentioning Filter.liminf and InformationTheory.klDiv** | ❌ 不在 (in-tree `klDiv_le_liminf_of_ae_tendsto` は **density a.e. 収束を仮定**する特殊版、弱収束版でない) |
| B-gauss | Gaussian 畳み込みの弱収束 / dirac 収束 | `ProbabilityTheory.gaussianReal, Filter.Tendsto` | **Found 0 declarations mentioning gaussianReal and Filter.Tendsto** | ❌ 不在 — truncation/平滑後測度が極限へ弱収束する Mathlib lemma が無い |
| B-conv-t | Measure.conv の Tendsto | `MeasureTheory.Measure.conv, Filter.Tendsto` | **Found 0 declarations mentioning Measure.conv and Filter.Tendsto** | ❌ 不在 |

### B 群の結論

**汎用機構 (Fatou・weak conv 定義・monotone/dominated convergence・conv a.c.) は既存**。しかし truncation/approximation ルートの 2 つの核心:
1. **entropyPower / KL の弱収束 LSC** (`Nₑ(X+Y) ≤ liminf Nₑ(X_R+Y_R)`) — Found 0。
2. **truncation/Gaussian 畳み込みの弱収束** (`P.map X_R → P.map X` 法則収束) — Found 0。

が両方 Mathlib 不在。これは既存在庫 `epi-uncond-truncation-lsc-inventory.md` §2-D/§6 の所見 (`wall:entropy-lsc-weak` / `wall:gaussian-approx-identity-weak`) と完全に一致する。**本壁 (無限分散、両 a.c.、有限微分エントロピー保持) は、方針 Y (任意 a.c.) inventory が調べた弱収束 LSC 壁と同じ核を共有する** (両 a.c. でも無限分散である限り finite-variance EPI を極限で繋ぐには弱収束 LSC が要る)。

---

## §C. in-tree 定義の moment 依存確認 (verbatim 引用)

### C-1. `IsHeatFlowEndpointRegular` (`EPIG2HeatFlowContinuity.lean:490-505`、structure、14 field、verbatim)

```lean
structure IsHeatFlowEndpointRegular {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] where
  hX_meas : Measurable X
  hZ_meas : Measurable Z
  hXZ_indep : IndepFun X Z P
  v_Z : ℝ≥0
  hv_Z_pos : 0 < v_Z
  hZ_law : P.map Z = gaussianReal 0 v_Z
  pX : ℝ → ℝ
  hpX_nn : ∀ x, 0 ≤ pX x
  hpX_meas : Measurable pX
  hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x))
  hpX_int : Integrable pX volume
  hpX_mass : (∫ y, pX y ∂volume) = 1
  hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume     -- ★ 有限 2 次モーメント (有限分散)
  hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume  -- ★ 有限微分エントロピー
```

**moment 依存判定**: `hpX_mom` (line 504) = `Integrable (fun y => y² * pX y) volume` = **有限2次モーメント (= 有限分散)** を field として持つ。`hpX_ent` (line 505) = 有限微分エントロピー。**無限分散入力では `hpX_mom` が偽**なので、`IsHeatFlowEndpointRegular` を構成できない → これに依存する heat-flow 連続性 (`heatFlowEntropyPower_continuousWithinAt_zero`) も無限分散には使えない。docstring (`:483-489`) は `hpX_ent` が「L¹+二次モーメントから follow しない (concentrated density が反例)」ため削除された旧 `negMulLog_integrable_of_density` の代替 precondition であることを明記。

### C-2. `IsRescaledPathRegular` (`EPICase1RatioLimit.lean:195-253`、def、verbatim 抜粋)

```lean
def IsRescaledPathRegular (A B : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (varA : ℝ) (v_B : ℝ≥0) : Prop :=
  (∀ t : ℝ, 0 < t → IndepFun B (fun ω => A ω / Real.sqrt t) P ∧ … (8 個の a.c./integrability conjunct)) ∧
  (∀ t : ℝ, 0 < t →
      (P.map (fun ω => A ω / Real.sqrt t + B ω)) ≪ volume
      ∧ (∫ x, (x - (∫ y, y ∂(P.map (fun ω => A ω / Real.sqrt t + B ω))))^2
            ∂(P.map (fun ω => A ω / Real.sqrt t + B ω)))
          ≤ varA / t + (v_B : ℝ)                                 -- ★ 分散の上界
      ∧ Integrable
          (fun x => (x - (∫ y, y ∂(P.map (fun ω => A ω / Real.sqrt t + B ω))))^2)
          (P.map (fun ω => A ω / Real.sqrt t + B ω))             -- ★ 有限 2 次モーメント (per-t)
      ∧ Integrable
          (fun x => Real.negMulLog
            (((P.map (fun ω => A ω / Real.sqrt t + B ω)).rnDeriv volume x).toReal))
          volume)                                                -- ★ 有限微分エントロピー (per-t)
```

**引数の意味**: `A B : Ω → ℝ` は rescale path `A/√t + B` を作る 2 関数 (de Bruijn heat path、`t→0⁺` で `A/√t` が支配、`t→∞` で `B` が支配)。`varA : ℝ` = scaled 成分 `A` の variance (path 上の variance bound `varA/t + v_B` を与える)。`v_B : ℝ≥0` = base 成分 `B` の variance。**moment 依存判定**: 第 2 big conjunct (line 244-253) が **per-`t>0`** で (i) variance 上界 `≤ varA/t + v_B`、(ii) `Integrable ((x-mean)²)` (有限2次モーメント)、(iii) 有限微分エントロピー を要求。**これは「path の各時刻 t>0 で有限分散」であって入力 X 自体の有限分散ではない** — だが `varX`/`varY`/`varS` という具体的有限実数 variance を引数に取る以上、**それが有限であること (= 入力が有限分散) を暗に要求**する。`EPIDensityForm.lean:472-480` の supplier (下記 C-3) が `varX`/`varY`/`varS` をどう供給するかが鍵。

### C-3. supplier 列挙 (`IsHeatFlowEndpointRegular` / `IsRescaledPathRegular` を consume/produce する file)

`rg "IsHeatFlowEndpointRegular|IsRescaledPathRegular" -l` の結果 (8 file):

| file | 役割 | moment 依存 |
|---|---|---|
| `EPIG2HeatFlowContinuity.lean` | `IsHeatFlowEndpointRegular` **定義** + 連続性 wall lemma consumer | 定義に `hpX_mom`/`hpX_ent` (C-1) |
| `EPICase1RatioLimit.lean` | `IsRescaledPathRegular` **定義** + ratio limit consumer | 定義に variance bound/per-t mom (C-2) |
| `EPICase1TwoTime.lean` | `IsRescaledPathRegular` を 3 bundle で consume (`h_reg_X`/`h_reg_Y`/`h_reg_S`、`:1314-1316`/`:1660-1662`) | bundle 経由 (regularity precondition) |
| `EPIDensityForm.lean` | `IsRescaledPathRegular` **supplier** (`h_rescale_X`/`h_rescale_Y`/`h_rescale_S` を `:472-480` で構成、`varX`/`varY`/`varS lift 1` 引数) | ★ supplier — ここで具体 variance を供給 → **有限分散依存の核心** |
| `EPIUncondDispatch.lean` | dispatch (有限分散枝で finite-variance EPI を呼ぶ) | 枝分け |
| `EPIG2ConvEntropyMonotone.lean` / `EPIStamToBridge.lean` / `EPICase1SmoothingLimit.lean` | downstream consumer | 間接 |

**結論 (C 群)**: in-tree の heat-flow / de Bruijn / rescale-path 機構は **`IsHeatFlowEndpointRegular.hpX_mom` (有限分散) と `IsRescaledPathRegular` の variance-bound 引数を構造的に要求**する。無限分散入力では `hpX_mom` が偽になり、これら機構は **一切転用できない**。これが「finite-variance route が heat-flow machinery に依存し、無限分散では使えない」(壁 docstring `:1392-1394`) の in-tree 側証拠。

---

## §D. 主要前提条件ボックス (前提事故が起きやすい lemma)

- **`entropyPowerExt_add_ge_of_finite_variance` (`EPICase1SmoothingLimit.lean:1351`、無限分散 truncation の各ステップで呼ぶ既存 EPI)**:
  - `[IsProbabilityMeasure P]`、`hX hY : Measurable`、`hXY : IndepFun X Y P`。
  - `hX_ac hY_ac : (P.map ·) ≪ volume`。
  - **`h_mom_X : Integrable (fun ω => (X ω)^2) P` / `h_mom_Y : Integrable (fun ω => (Y ω)^2) P`** ← **有限分散を要求**。truncation した `X_R` には供給可 (compact support だから有限分散)、生 X には不可。
  - **`hX_ent`/`hY_ent`/`hent_sum`**: 各 negMulLog density の `Integrable` (有限微分エントロピー)。truncated X_R で再供給が要る (生 X の `hX_ent` から X_R の `hX_ent` は自明でない)。
  - 結論: `entropyPowerExt (P.map (X+Y)) ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y)` (ℝ≥0∞ 不等式)。
- **`IndepFun.variance_add` (`Mathlib/Probability/Moments/Variance.lean:406`、★最危険)**:
  - `nonrec theorem IndepFun.variance_add {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (h : X ⟂ᵢ[μ] Y) : Var[X + Y; μ] = Var[X; μ] + Var[Y; μ]`。
  - **`MemLp X 2 μ` = 有限2次モーメント を前提に要求**。無限分散では `MemLp 2` が**偽**なので、分散加法すら無限分散入力には直接適用不可。truncation の各 R で X_R が `MemLp 2` を満たすのを再確認してから呼ぶ必要 (compact support なら自動)。
- **`differentialEntropyExt` (`EntropyPowerExt.lean:59-64`、a.c. 枝が pos/neg part EReal 差)**:
  - a.c. 枝で `(∫⁻ ofReal(negMulLog f)) - (∫⁻ ofReal(-(negMulLog f)))` の EReal 差。`h=+∞` → ⊤、`h=-∞` → ⊥、有限 → workhorse 一致。
  - ⚠ **本壁の入力は両 a.c. + 両有限微分エントロピー** (`hX_ent`/`hY_ent`) なので、X/Y 側の `differentialEntropyExt` は**有限値**で well-behaved。`hent_sum` (X+Y の有限エントロピー) は壁 signature には**無い** (`entropy_power_add_ge_of_finite_variance` には `hent_sum` 引数があるが、`_infinite_variance` 側には無い) → truncation 後に X_R+Y_R の有限エントロピーを別途供給するか、極限の LSC で迂回する設計判断が必要。
- **`differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:520`、maxent 上界 — truncation の支配関数候補)**:
  - `[IsProbabilityMeasure μ] (hμ : μ ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (h_mean : ∫ x, x ∂μ = m) (h_var : ∫ x, (x - m)^2 ∂μ ≤ (v:ℝ)) (h_var_int : Integrable (fun x => (x - m)^2) μ) (h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume)`。
  - 結論: `differentialEntropy μ ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)`。
  - **致命的**: `h_var` (有限分散) + `h_ent_int` (= 有限エントロピー、出力ではなく**前提**) を要求。無限分散では `h_var` が立たない。**値の上界であって integrability を produce しない** (Bochner ∫ は非可積分時 `0` 返し)。truncation の極限制御で「上から抑える」道具にはなるが、生 X (無限分散) には直接効かない。

---

## §E. 自作が必要な要素 (優先度順)

| # | 要素 | 推奨実装 | 工数感 | 落とし穴 |
|---|---|---|---|---|
| 1 | **entropyPower (or differentialEntropyExt) の弱収束下半連続性** `Nₑ(X+Y) ≤ liminf_{R→∞} Nₑ(X_R+Y_R)` | `differentialEntropyExt : EReal` 上で `lowerSemicontinuousWithinAt_iff_le_liminf` (`[CompleteLinearOrder EReal]`、`Mathlib/Topology/Semicontinuity/Basic.lean:269`、既存) を出口に、`klDiv = ∫⁻ klFun(rnDeriv)` の ℝ≥0∞ 形 + `lintegral_liminf_le` (Fatou、B9a) で density a.e. 収束から組む。in-tree `klDiv_le_liminf_of_ae_tendsto` (`EPIG2KLFatouLSC.lean`) の **弱収束版への一般化** | **moonshot 規模** (density a.e. 収束を弱収束から出す portmanteau-LSC bridge が Mathlib 不在 §B-2、自作 200-400 行) | density a.e. 収束は弱収束より強い。truncation 列の特殊構造 (`X_R = X·1_{|X|≤R}` の明示形) を使えば a.e. 収束は直接出る (truncation は弱収束より強く、各点収束する) — これは方針 Y の Gaussian 平滑より**有利な点** |
| 2 | **truncation 測度の R→∞ 弱収束** `P.map X_R → P.map X` (法則収束) | truncation `X_R := if \|X\|≤R then X else 0` (or projection)。`X_R → X` 各点収束 → 法則収束 (truncation は支配収束で各点 a.e. 収束)。`tendsto_iff_forall_integral_tendsto` (B6a) 出口。Gaussian 平滑 (`gaussianReal` weak-conv 不在 B-gauss) より素朴 | 中 (truncation の各点収束は素朴、80-150 行) | truncation で X_R の law が a.c. を保つか (truncation は a.c. を壊しうる: `1_{\|X\|≤R}·X` の law は X の law を `[-R,R]` に制限 + atom を作る → **a.c. でなくなる**)。**soft truncation (mollified cutoff) or conditioning が必要** ← これが本ルートの隠れた難所 |
| 3 | **truncated 入力の finite-variance EPI 配線** | 各 R で `X_R` が有限分散・有限エントロピー・a.c. を満たすことを確立し `entropyPowerExt_add_ge_of_finite_variance` (:1351) を呼ぶ | 中 (既存 EPI への配線、項目 2 の a.c. 保存が前提) | `IndepFun.variance_add` の `MemLp 2` 前提 (§D)。X_R の有限エントロピー `hX_ent` 再供給。X_R, Y_R の独立性保存 (`IndepFun.comp`) |

---

## §F. Mathlib 壁の列挙 (真に不在、`@residual(wall:...)` 対象)

| 壁候補 | 内容 | loogle 確認 (Found 0) | 判定 |
|---|---|---|---|
| `wall:epi-infinite-variance-classical` (**既存・本壁**) | 無限分散 a.c. EPI = sharp Young / Brascamp-Lieb / 対称減少再配置による直接証明 (ルート A) | `"BrascampLieb"` / `"Brascamp"` / `"Renyi"` / `"PrekopaLeindler"` / `"Prekopa"` = **全 Found 0**; `convolution, eLpNorm` = **Found 0** (二段); `"logSobolev"` = **Found 0** | ✅ genuine Mathlib 壁 (ルート A の部品ゼロ) |
| `wall:entropy-lsc-weak` (**既存**、`epi-uncond-truncation-lsc-inventory.md` §6 と共有) | entropy / KL の弱収束下半連続性 (ルート B step 3 LHS) | `InformationTheory.klDiv, LowerSemicontinuous` = **Found 0**; `klDiv, Filter.liminf` = **Found 0** | ✅ genuine Mathlib 壁 (ルート B の核 1) |
| `wall:gaussian-approx-identity-weak` (**既存**、同 §6 と共有) | Gaussian 畳み込み / truncation 測度の弱収束 | `gaussianReal, Filter.Tendsto` = **Found 0**; `Measure.conv, Filter.Tendsto` = **Found 0** | ✅ genuine Mathlib 壁 (ルート B の核 2) — ただし truncation 版は各点収束で迂回可能性あり (§E #2) |

### shared sorry 補題化の推奨

**ルート B を採る場合、核心壁 (項目 1 = entropy 弱収束 LSC) は `wall:entropy-lsc-weak` として `epi-uncond-truncation-lsc-inventory.md` が既に登録した壁と同一**。複数 file (本壁 `EPICase1SmoothingLimit.lean` + 方針 Y の `EPIUncondTruncationLSC.lean` 想定) に散在させず、**1 本の shared sorry 補題に集約推奨** (詳細 → `docs/audit/audit-tags.md`「共有 Mathlib 壁: shared sorry 補題パターン」)。

**現状の `entropyPowerExt_add_ge_infinite_variance` の `@residual(wall:epi-infinite-variance-classical)` 分類は妥当** (ルート A の sharp Young/Brascamp-Lieb は genuine Mathlib 壁、二段検索で裏取り済)。ただし**ルート B (truncation) で攻める場合は `wall:entropy-lsc-weak` + `wall:gaussian-approx-identity-weak` の 2 壁に分解される**ので、攻め方を決めてから slug を選ぶ (現状の単一 `wall:epi-infinite-variance-classical` はルート A 想定の命名)。

---

## §G. 撤退ラインへの距離

### 親計画の撤退ライン

親 `epi-unconditional-moonshot-plan.md` の **L-Uncond-3-scope** = 「方針 Y が semicontinuity wall で genuine に詰まったら、有限分散+有限エントロピーを honest precondition として残す方針 X に縮退して着地」。

### 判定: **既に発動済の壁に触れる (発動 yes)**

本壁 `entropyPowerExt_add_ge_infinite_variance` 自体が、L-Uncond-3-scope の **honest 着地点の一部**である:

- 親計画の `entropyPowerExt_add_ge_dispatch_skeleton` は 3-case dispatch で、case-1 (有限エントロピー a.c.) が `wall:epi-finite-entropy-ac-classical` に局所化 (`epi-facts.md` 達成表)。
- 本壁は**その case-1 をさらに「有限分散あり (`_of_finite_variance`、closure 済 commit 452ea1b)」と「無限分散 (`_infinite_variance`、本壁)」に 3 分解した残り 1 つ** (壁 docstring `:455` の moonshot plan 判断ログ 4 で記録: 「旧 bundled wall を正則 [Phase A 既閉] / 有限分散 [closure 済] / 無限分散 [`@residual(wall:epi-infinite-variance-classical)`] に 3 分解」)。

つまり本壁は「方針 X (有限分散 precondition) では解決済、方針 Y (無限分散も剥がす) の残課題」という位置づけで、**L-Uncond-3-scope は既に honest に運用されている** (有限分散版が genuine closure 済、無限分散版が壁として正直に残置)。

### 縮退案 (新規撤退ライン提案、撤退口は sorry + `@residual`、仮説束化禁止)

ルート選択ごとに:

- **縮退案 α (現状維持・推奨)**: 本壁を `@residual(wall:epi-infinite-variance-classical)` のまま park 継続。無限分散古典 EPI は数学的には真だが、ルート A (sharp Young) は Mathlib 部品ゼロの大規模 gap、ルート B (truncation) は `wall:entropy-lsc-weak` + truncation a.c. 保存 (§E #2 隠れ難所) を要する moonshot。**有限分散版が既に genuine closure 済**なので、EPI の honest 射程は「両 a.c. + 有限分散」で確保されており、無限分散は park で投資効率上妥当。
- **縮退案 β (ルート B 部分着手)**: 本壁を `wall:entropy-lsc-weak` (shared) に再分類し、entropy 弱収束 LSC を共有 sorry 補題に集約。truncation 配線 (§E #2/#3) を genuine に組み、最後の LSC だけ壁に残す。**利点**: 壁を「entropy LSC 1 本」に孤立化でき、将来 Mathlib に LSC が入れば自動 closure。**欠点**: truncation a.c. 保存 (soft cutoff/conditioning) の自作が要る (§E #2 隠れ難所、各点収束だが a.c. を壊しうる)。
- **縮退案 γ (gateway atom 試行)**: ルート B feasibility の最終確証として、`lean-implementer` に **truncation a.c. 保存 atom** (`P.map X_R ≪ volume` を soft cutoff で保つ補題、§E #2) を 1 本 dispatch して通るか試す (gateway-atom-first 原則)。これが通れば縮退案 β が現実的、詰まれば縮退案 α (park) 確定。

**反証義務 (CLAUDE.md「壁と断じる側」)**: ルート A 壁判定は loogle Found 0 × 7 系統 + conclusion-shape 二段 (A-1c) + template self-build 不能 (sharp Young 定数を部品ゼロから数百行) で裏取り済。ルート B 壁判定は §B-2 の 4 系統 Found 0 + 既存 `epi-uncond-truncation-lsc-inventory.md` の独立確認と一致。**ただし「無限分散の独立和で entropyPower の劣加法性が実際に有限分散版と同じ向きで成立する小サンプル sanity」は未実行** — 数学的には Cauchy 等 heavy-tail a.c. でも EPI は真と期待されるが (Lieb 1978)、Lean 上で truncation 極限が向き整合で閉じるかは縮退案 γ の gateway dispatch で確証推奨。

---

## §H. 着手 skeleton (参考・実装は別 agent)

> ルート B (truncation) で攻める場合の出だし。`EPICase1SmoothingLimit.lean` 拡張 or 新 file `EPIInfiniteVariance.lean`。

```lean
import InformationTheory.Shannon.EntropyPowerExt
import InformationTheory.Shannon.EPICase1SmoothingLimit   -- entropyPowerExt_add_ge_of_finite_variance
import InformationTheory.Shannon.EPIG2KLFatouLSC          -- klDiv_le_liminf 系
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Add        -- lintegral_liminf_le
import Mathlib.Topology.Semicontinuity.Basic              -- lowerSemicontinuousWithinAt_iff_le_liminf
import Mathlib.Probability.Independence.Basic

namespace InformationTheory.Shannon

open MeasureTheory Filter Real ProbabilityTheory
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

/-- **gateway atom (縮退案 γ、最初に試す)**: truncation が a.c. を保つ。
soft cutoff/conditioning で `P.map X_R ≪ volume` を保証 (素朴 indicator truncation は atom を作り a.c. を壊す)。
これが通れば truncation route が現実的、詰まれば park 確定。 -/
theorem truncated_map_absolutelyContinuous
    (X : Ω → ℝ) (hX : Measurable X) (hX_ac : (P.map X) ≪ volume) (R : ℝ) (hR : 0 < R) :
    (P.map (truncate X R)) ≪ volume := by
  sorry -- @residual(wall:gaussian-approx-identity-weak) [truncation a.c. 保存、§E #2 隠れ難所]

/-- **核心壁 (縮退案 β、shared)**: entropyPowerExt の truncation 列に沿う下半連続性。
`klDiv = ∫⁻ klFun(rnDeriv)` + `lintegral_liminf_le` (Fatou) で density a.e. 収束から組む。
truncation 列は弱収束より強く a.e. 各点収束するので Fatou が直接効く想定 (§E #1)。 -/
theorem entropyPowerExt_le_liminf_truncation
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (R : ℕ → ℝ) (hR_pos : ∀ n, 0 < R n) (hR_lim : Tendsto R atTop atTop) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≤ Filter.liminf
          (fun n => entropyPowerExt
            (P.map (fun ω => truncate X (R n) ω + truncate Y (R n) ω)))
          atTop := by
  sorry -- @residual(wall:entropy-lsc-weak) [entropy 弱収束 LSC、shared、Mathlib 不在 §B-2]

/-- **本壁 (現状)**: 無限分散 a.c. 古典 EPI。ルート A (sharp Young) 部品ゼロ、
ルート B (truncation) は上 2 wall に分解。-/
theorem entropyPowerExt_add_ge_infinite_variance'
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (h_infvar : ¬ (Integrable (fun ω => (X ω) ^ 2) P ∧ Integrable (fun ω => (Y ω) ^ 2) P)) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  sorry -- @residual(wall:epi-infinite-variance-classical) [ルート選択後 wall slug 再分類]

end InformationTheory.Shannon
```

---

## 既存率 / 自作 / 撤退 サマリ

- **既存率**: ルート A = **0%** (sharp Young / Brascamp-Lieb / 対称減少再配置 / Rényi / Prékopa / LSI 全部品不在、Found 0 × 7)。ルート B = 汎用機構約 **50%** 既存 (Fatou `lintegral_liminf_le` / weak conv 定義 `tendsto_iff_forall_integral_tendsto` / monotone・dominated convergence / `lowerSemicontinuousWithinAt_iff_le_liminf` / conv a.c. が ✅、核心の entropy 弱収束 LSC + truncation 弱収束が ❌)。
- **自作必要**: ルート A は実質不可能 (moonshot 1 本以上の Mathlib 上流貢献)。ルート B は **3 件** (entropy 弱収束 LSC [moonshot 級] / truncation a.c. 保存 [隠れ難所] / finite-variance EPI 配線)。真の難所 = **2 件** (entropy LSC + truncation a.c. 保存)。
- **撤退ライン**: **発動 yes** — 本壁は親 L-Uncond-3-scope の honest 着地点の一部 (有限分散版は genuine closure 済、無限分散版が壁として正直に park)。最低コスト縮退 = **縮退案 α (現状維持 park)**。ルート B 着手なら縮退案 β (shared `wall:entropy-lsc-weak` 集約) + γ (truncation a.c. 保存 gateway dispatch で feasibility 確証)。
