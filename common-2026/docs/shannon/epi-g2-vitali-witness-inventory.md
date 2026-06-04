# EPI G2 Vitali 3 witness (UI / UT / ae) — Mathlib + InformationTheory API 在庫

> 対象: `wall:approx-identity-L1` 配下の **3 つの Vitali witness 補題**
> (`InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean`)。これらが genuine 化されれば
> 層2 (`differentialEntropy_convDensity_integral_tendsto`、own-sorry 0) → 壁補題
> `heatFlowEntropyPower_continuousWithinAt_zero` が transitive に閉じ、層1
> `convDensityAdd_tendsto_L1_zero` (`:96`) のみが残壁になる。
> - witness 1: `negMulLog_convDensity_tendsto_ae` (`:194`)
> - witness 2: `negMulLog_convDensity_unifIntegrable` (`:159`)
> - witness 3: `negMulLog_convDensity_unifTight` (`:176`)
>
> 親計画: [`epi-g2-layer2-moonshot-plan.md`](epi-g2-layer2-moonshot-plan.md) Phase 2 (UI/UT)。
> 先行在庫: [`epi-g2-layer2-semicontinuity-inventory.md`](epi-g2-layer2-semicontinuity-inventory.md)
> (machinery)、[`epi-g2-layer1-approx-identity-inventory.md`](epi-g2-layer1-approx-identity-inventory.md) (層1)。
> loogle index: 2026-05-10 build (Mathlib lemma 網羅、InformationTheory 定義は rg 併用)。

## 一行サマリ

**witness 1 (ae 点ごと収束) は層1 L¹ 収束 (`convDensityAdd_tendsto_L1_zero`) + Mathlib
`TendstoInMeasure.exists_seq_tendsto_ae` で genuine 可能だが「full 列 ae」でなく「部分列 ae」しか出ず
Vitali 直結に gap がある (要再 index)。witness 2 (UI) は決定的に新しい positive 発見 = **in-tree の Gaussian
maximum-entropy 上界 `differentialEntropy_le_gaussian_of_variance_le`
(`DifferentialEntropy.lean:520`, `@entry_point`) が存在し、`f_{u n}` を `P.map(X+√(u n)·Z)` の密度と
見れば負部 (`∫ negMulLog⁺`) を二次モーメント一様に押さえる足場になる**。ただし UI 構成補題
`unifIntegrable_of` (`:653`) は「`{C ≤ ‖f i‖}` 上の indicator Lp ノルムを一様小」を要求する形で、
maxent 上界 (積分値の上界) から indicator tail への橋が非自明 (negMulLog の符号構造が障害)。witness 3 (UT)
は二次モーメント由来 tail tightness で、Markov lintegral 版 (`mul_meas_ge_le_lintegral`、測度非依存)
が `volume` で使える一方、`meas_ge_le_variance_div_sq` は `[IsFiniteMeasure]` 要求で `volume` 直適用
不可 (密度測度経由が必要)。**総合: 3 witness とも (A) Mathlib 部品組上げで genuine 可能だが
moonshot 寄り。最大 leverage = maxent 上界の再利用 (witness 2)。撤退ライン 2 (UI/UT が pX_mom だけからは
出ない) には触れるが、maxent 上界 + hpX_ent precondition で踏み抜かない見込み。**

**既存率 ~60% (machinery + maxent + Chebyshev は在、indicator-tail 橋と ae full 列が自作) /
自作必要 4 件 / 撤退ライン発動 no (ただし witness 2 の indicator 橋が最危険、要 precondition 補強の可能性)。**

---

## 主定理の最終形 (3 witness 再掲、verbatim)

```lean
-- EPIG2HeatFlowContinuity.lean:194 — witness 1 (ae 点ごと収束)
theorem negMulLog_convDensity_tendsto_ae
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_lim : Tendsto u atTop (𝓝[Set.Ioi 0] 0)) :
    ∀ᵐ x ∂volume,
      Tendsto (fun n =>
        Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x))
        atTop (𝓝 (Real.negMulLog (pX x)))

-- EPIG2HeatFlowContinuity.lean:159 — witness 2 (UnifIntegrable)
theorem negMulLog_convDensity_unifIntegrable
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) :
    UnifIntegrable
      (fun n => fun x =>
        Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x))
      1 volume

-- EPIG2HeatFlowContinuity.lean:176 — witness 3 (UnifTight)
theorem negMulLog_convDensity_unifTight  -- 同 hyp、結論のみ差替:
    ... : UnifTight (fun n x => Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n,_⟩) x)) 1 volume
```

`f_{u n} := convDensityAdd pX (gaussianPDFReal 0 ⟨u n,_⟩) = pX ∗ g_{u n}` (Gauss 核分散 `u n`)。
`u : ℕ → ℝ`, `u n > 0`。Vitali (`tendsto_Lp_of_tendsto_ae`, UnifTight.lean:329) の hyp として
`hui` (witness 2) / `hut` (witness 3) / `hfg` (witness 1) を供給する。

pseudo-Lean (各 witness の証明戦略案):
```text
witness 1 (ae): 層1 L¹ 収束 convDensityAdd_tendsto_L1_zero (@residual)
              → tendstoInMeasure_of_tendsto_eLpNorm → exists_seq_tendsto_ae で a.e. 部分列
              → Real.continuous_negMulLog 合成。  ⚠ full 列 ae でなく部分列 ae (gap、後述)
witness 2 (UI): unifIntegrable_of (:653) の indicator tail 一様小を、
              f_{u n} の負部 ∫ negMulLog⁺ を maxent 上界 differentialEntropy_le_gaussian_of_variance_le
              で二次モーメント一様に押さえて構成。  ⚠ 積分値上界→indicator tail 橋が非自明
witness 3 (UT): unifTight 定義 (sᶜ 上 Lp 小) を、f_{u n} の二次モーメント
              = ∫x²pX + (u n)·v_g が u n→0 で一様有界 → Markov(lintegral) で遠方質量小 → tail。
```

---

## カテゴリ A — witness 1: ae 点ごと近似単位元収束

### ⚠️ 部分的 — 層1 + 部分列 ae は在、full 列 ae に gap

| 概念 | Mathlib / InformationTheory API | file:line | 状態 | witness 1 での扱い |
|---|---|---|---|---|
| 層1 L¹ 収束 (足場) | `convDensityAdd_tendsto_L1_zero` | `EPIG2HeatFlowContinuity.lean:96` (`@residual(wall:approx-identity-L1)`) | ⚠️ sorry (壁) | witness 1 の足場。これが genuine 化されないと witness 1 も transitive sorry |
| L¹→測度収束 | `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` | `MeasureTheory/Function/ConvergenceInMeasure.lean:463` | ✅ | eLpNorm 収束 → TendstoInMeasure |
| **測度収束→部分列 ae** | `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae` | `MeasureTheory/Function/ConvergenceInMeasure.lean:277` | ✅ | **部分列 ae のみ** (full 列でない、gap) |
| bump 畳込み ae 収束 (参考) | `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable` | `Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean:107` | ✅ (但し bump 限定) | 論証構造の参考のみ。gaussianPDF は ContDiffBump 不可 |
| 一般 mollifier / Gauss 核 ae 点ごと収束 | — | — | ❌ **不在** (loogle `MeasureTheory.convolution, Filter.Tendsto` → bump 4 件のみ) | gaussianPDF 一般 L¹ `pX` 版なし |
| negMulLog 連続 (合成) | `Real.continuous_negMulLog` | `Analysis/SpecialFunctions/Log/NegMulLog.lean:186` (`@[fun_prop]`) | ✅ | `f_{u n} x → pX x` を `negMulLog` 合成で持上げ |

#### 主要補題の verbatim signature

```lean
-- ConvergenceInMeasure.lean:277 — 測度収束 → 部分列 a.e.収束 (★ StrictMono ns、full 列でない)
theorem TendstoInMeasure.exists_seq_tendsto_ae (hfg : TendstoInMeasure μ f atTop g) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ, Tendsto (fun i => f (ns i) x) atTop (𝓝 (g x))
-- 文脈 variable: {α ι E} {m : MeasurableSpace α} {μ : Measure α} {f : ℕ → α → E} {g : α → E}
--   [MetricSpace E]。★ 測度非依存 (volume OK)。だが結論は f (ns i) (部分列)。

-- BumpFunction/Convolution.lean:107 — bump 限定 ae 収束 (論証構造の参考のみ)
theorem ae_convolution_tendsto_right_of_locallyIntegrable
    {ι} {φ : ι → ContDiffBump (0 : G)} {l : Filter ι} {K : ℝ}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0))
    (h'φ : ∀ᶠ i in l, (φ i).rOut ≤ K * (φ i).rIn) (hg : LocallyIntegrable g μ) :
    ∀ᵐ x₀ ∂μ, Tendsto (fun i ↦ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] g) x₀) l (𝓝 (g x₀))
-- ★ 内部は Besicovitch.vitaliFamily の Lebesgue 微分 (average) を使用。gaussianPDF は ContDiffBump
--   でないので直接適用不可。Lebesgue 点経由の独立証明の参考にはなる。
```

> **witness 1 の gap (orchestrator 必読)**: 層1 L¹ 収束を Mathlib `exists_seq_tendsto_ae` に通すと
> 得られるのは **部分列** `f (ns i)` の ae 収束。一方 witness 1 の結論は **full 列** `n ↦ negMulLog f_{u n}`
> の ae 収束。Vitali (`tendsto_Lp_of_tendsto_ae`) は full 列の `hfg` を要求するので、部分列 ae では
> 直結しない。**回避策**: 層2 machinery 側で「全部分列が同一極限へ L¹ 収束する」事実
> (`tendsto_of_subseq_tendsto` 型) を使えば部分列 ae で足りる場合がある (Mathlib 自身の
> `tendsto_Lp_finite_of_tendstoInMeasure` `:566` がこのパターン)。**しかし witness 1 の現 signature は
> full 列 ae を要求しているため、(a) 層2 を `TendstoInMeasure` 入力に書換える (Vitali を
> `tendsto_Lp_of_tendstoInMeasure` `UnifTight.lean` に差替) か、(b) witness 1 を「Gauss 核の Lebesgue
> 点 ae 点ごと収束」として直接証明 (Besicovitch average 経由、bump 版の独立再現) するか**の判断が要る。
> (b) なら full 列 ae が直接出るが工数大。**この gap は親 plan Phase 2 / Phase 3-a の「a.e. 各点収束は
> 部分列経由」(plan 落とし穴 line 217) で認識済だが、witness 1 の signature 自体は full 列のまま park
> されており未解決。**

> **loogle 否定記録**: `MeasureTheory.convolution, Filter.Tendsto` → Found 4 (すべて bump:
> `convolution_tendsto_right` / `ContDiffBump.convolution_tendsto_right(_of_continuous)` /
> `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`)。一般 L¹ `pX` + Gauss 核の
> ae 点ごと収束は **不在**。

---

## カテゴリ B — witness 2: UnifIntegrable 構成部品 (最難)

### ✅ 構成補題は網羅的に在 / ⚠️ 適用形が非自明

loogle `MeasureTheory.UnifIntegrable` → Found 27。witness 2 に効く構成系を verbatim 列挙:

| 概念 | Mathlib API | file:line | 状態 | witness 2 での扱い |
|---|---|---|---|---|
| 定義 | `MeasureTheory.UnifIntegrable` | `MeasureTheory/Function/UniformIntegrable.lean:67` | ✅ | 主張対象 |
| **indicator tail 一様小 → UI** (核) | `MeasureTheory.unifIntegrable_of` | `UniformIntegrable.lean:653` | ✅ | **第一候補構成**。`{C ≤ ‖f i‖}` 上 Lp ノルムを一様小に |
| 同 (StronglyMeasurable + C>0 版) | `MeasureTheory.unifIntegrable_of'` | `UniformIntegrable.lean:589` | ✅ | `unifIntegrable_of` の下層 (`C` 正値要求) |
| L¹ 収束 → UI | `MeasureTheory.unifIntegrable_of_tendsto_Lp` | `UniformIntegrable.lean:553` | ✅ (循環注意) | **`negMulLog f_t` の L¹ 収束**から出るが、それは層1 (密度の L¹) と別物 |
| L¹→0 → UI | `MeasureTheory.unifIntegrable_of_tendsto_Lp_zero` | `UniformIntegrable.lean:539` | ✅ | 上の下層 |
| 単一可積分 const → UI | `MeasureTheory.unifIntegrable_const` | `UniformIntegrable.lean:405` | ✅ | `{negMulLog pX}` 定数族の UI (補助) |
| 有限族 → UI | `MeasureTheory.unifIntegrable_finite` | `UniformIntegrable.lean:444` | ✅ (`[Finite ι]`) | 有限 prefix 処理 (cf. `unifIntegrable_of_tendsto_Lp_zero` 内部パターン) |
| UI 和 | `MeasureTheory.UnifIntegrable.add` | `UniformIntegrable.lean` (loogle) | ✅ | `f = const + (f-const)` 分解 |
| UI 引き / 否定 / restrict / ae_eq | `.sub` / `.neg` / `.restrict` / `.ae_eq` | `UniformIntegrable.lean` | ✅ | 補助変換 |
| **Gaussian maxent 上界** (witness 2 の鍵) | `differentialEntropy_le_gaussian_of_variance_le` | `InformationTheory/Shannon/DifferentialEntropy.lean:520` (`@entry_point`) | ✅ | **`∫ negMulLog f_{u n}` を二次モーメント一様に上界** |
| negMulLog 上界 `≤ 1 - x` | `Real.negMulLog_le_one_sub_self` | `NegMulLog.lean:234` | ✅ | 正部 `{x : f≤1}` 制御 |

#### 主要補題の verbatim signature (型クラス前提込み)

```lean
-- UniformIntegrable.lean:653 — indicator tail 一様小 → UI (★ 第一候補)
theorem unifIntegrable_of (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0,
      ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε) :
    UnifIntegrable f p μ
-- 文脈 variable: {α β ι} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
--   [NormedAddCommGroup β]。★ [IsFiniteMeasure] 不要 (volume OK)。★ `C` は ε に一様 (i に依らない)。

-- UniformIntegrable.lean:553 — L¹ 収束 → UI (★ 循環注意: f の L¹ 収束を要求)
theorem unifIntegrable_of_tendsto_Lp (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : ∀ n, MemLp (f n) p μ)
    (hg : MemLp g p μ) (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)) :
    UnifIntegrable f p μ
-- 文脈: {f : ℕ → α → β} {g : α → β}。★ hfg = negMulLog f_{u n} の L¹ 収束 (≠ 層1 = 密度の L¹ 収束)。

-- UniformIntegrable.lean:405 — 定数族 UI
theorem unifIntegrable_const {g : α → β} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (hg : MemLp g p μ) :
    UnifIntegrable (fun _ : ι => g) p μ

-- UniformIntegrable.lean:444 — 有限族 UI
theorem unifIntegrable_finite [Finite ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, MemLp (f i) p μ) : UnifIntegrable f p μ

-- DifferentialEntropy.lean:520 — Gaussian maximum-entropy 上界 (★ witness 2 の最重要足場)
theorem differentialEntropy_le_gaussian_of_variance_le
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (h_mean : ∫ x, x ∂μ = m)
    (h_var : ∫ x, (x - m)^2 ∂μ ≤ (v : ℝ))
    (h_var_int : Integrable (fun x => (x - m)^2) μ)
    (h_ent_int : Integrable
      (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) :
    differentialEntropy μ ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)
-- ★ [IsProbabilityMeasure μ] 要求 — `f_{u n}·volume` (確率測度) に適用、`volume` には直接適用不可。
-- ★ h_ent_int = `convDensityAdd_negMulLog_integrable_pub` (:139, @audit:ok) で各 n 供給可。
-- ★ 結論は ∫ の上界 (= -∫ negMulLog ... の下界、negMulLog の符号注意)。indicator tail への橋は別途。
```

> **witness 2 の構造 (最重要分析)**: UI を `unifIntegrable_of` で出すには
> `{C ≤ ‖negMulLog f_{u n}‖} 上の indicator Lp ノルムを `C` 一様 (n に依らず) に小さく」が要る。
> `negMulLog t = -t log t` は **`t∈[0,1]` で `≥0` (有界 `≤ 1/e`)、`t>1` で `<0`・`t→∞` で `-∞`**。
> よって `‖negMulLog f_{u n}‖` が大きいのは (i) `f_{u n}` が大 (`t>1` 領域、`-t log t` の絶対値大)
> または (ii) `f_{u n}` が `0` 近傍 (`-t log t → 0` なので実は問題なし)。tail mass を一様に押さえる
> 自然な道具が **maxent 上界**: `∫ negMulLog f_{u n} ≥ -(1/2)log(2πe·V_n)` (V_n = `f_{u n}` の分散
> `= ∫x²pX + u n·v_g`、`u n→0` で一様有界) で `∫ negMulLog f_{u n}` の **下界**が一様。これと正部の
> 上界 (`negMulLog_le_one_sub_self`) を組めば `∫ |negMulLog f_{u n}|` が一様有界 → de la Vallée-Poussin
> 型で UI。**ただし「積分の一様有界」から `unifIntegrable_of` の indicator-tail 一様小への橋は
> Mathlib に直接の補題がない** (de la Vallée-Poussin / `MemLp` 一様性の橋)。これが witness 2 の
> 真の自作部分 (40〜80 行、maxent 上界を足場にしても橋が残る)。

> **maxent 上界適用の前提事故 (orchestrator 必読)**: `differentialEntropy_le_gaussian_of_variance_le`
> は `[IsProbabilityMeasure μ]` + `μ ≪ volume` を要求し、`μ = f_{u n} · volume` (= `P.map(X+√(u n)·Z)`)
> に適用する形になる。`f_{u n}` を **密度として持つ確率測度**へ視点を移す必要があり、
> `pPath_eq_convDensityAdd` (`FisherInfoV2DeBruijnPerTime.lean:215`, `@audit:ok`、下記 D) で
> `(P.map(X+√s·Z)).rnDeriv volume =ᵐ ofReal∘(convDensityAdd pX g_{s·v_Z})` の同定が要る。
> ただし witness 2 の現 signature は `pX` のみ (`X, Z, P` を持たない) ため、maxent ルートを採るなら
> **witness 2 の signature に `μ_n := f_{u n}·volume` の確率測度性 / AC を内部構築するか、
> あるいは `hpX_ent` 型 precondition を追加**する判断が要る (撤退ライン 2 と連動)。

---

## カテゴリ C — witness 3: UnifTight 構成部品

### ✅ 構成補題 + Chebyshev は在 / ⚠️ volume 上の Chebyshev は密度測度経由が必要

loogle `MeasureTheory.UnifTight` → Found 16。

| 概念 | Mathlib API | file:line | 状態 | witness 3 での扱い |
|---|---|---|---|---|
| 定義 | `MeasureTheory.UnifTight` | `MeasureTheory/Function/UnifTight.lean:59` | ✅ | `∀ε>0, ∃s, μ s≠∞ ∧ ∀i, eLpNorm (sᶜ.indicator (f i)) p μ ≤ ε` |
| 定数族 UT | `MeasureTheory.unifTight_const` | `UnifTight.lean:145` | ✅ | 補助 |
| 有限族 UT | `MeasureTheory.unifTight_finite` | `UnifTight.lean:191` | ✅ (`[Finite ι]`) | 有限 prefix 処理 |
| UT 和 / 引き / 否定 | `.add` / `.sub` / `.neg` | `UnifTight.lean` | ✅ | 補助変換 |
| UT ae_eq / congr | `.aeeq` / `unifTight_congr_ae` | `UnifTight.lean` | ✅ | measurable mk 経由 |
| real/ennreal 同値 | `unifTight_iff_real` / `unifTight_iff_ennreal` | `UnifTight.lean` | ✅ | eLpNorm 計算の橋 |
| **Markov (lintegral、測度非依存)** | `MeasureTheory.mul_meas_ge_le_lintegral` | `MeasureTheory/Integral/Lebesgue/Markov.lean:57` | ✅ | **`volume` 上で遠方質量小に使える** |
| Markov (lintegral, ae 版) | `MeasureTheory.mul_meas_ge_le_lintegral₀` | `Lebesgue/Markov.lean:50` | ✅ | AEMeasurable 版 |
| Markov (Bochner、real) | `MeasureTheory.mul_meas_ge_le_integral_of_nonneg` | `Bochner/Basic.lean:1175` | ✅ | `ε·μ.real{ε≤f} ≤ ∫f` (非負・可積分) |
| Chebyshev (variance 形) | `ProbabilityTheory.meas_ge_le_variance_div_sq` | `Probability/Moments/Variance.lean:397` | ⚠️ `[IsFiniteMeasure μ]` | **`volume` 直適用不可** (密度測度経由) |

#### 主要補題の verbatim signature

```lean
-- UnifTight.lean:59 — UnifTight 定義
def UnifTight {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  ∀ ⦃ε : ℝ≥0⦄, 0 < ε → ∃ s : Set α, μ s ≠ ∞ ∧ ∀ i, eLpNorm (sᶜ.indicator (f i)) p μ ≤ ε

-- UnifTight.lean:191 — 有限族 UT
theorem unifTight_finite [Finite ι] (hp_top : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, MemLp (f i) p μ) : UnifTight f p μ

-- Lebesgue/Markov.lean:57 — Markov (★ 測度非依存、volume OK)
theorem mul_meas_ge_le_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ f x } ≤ ∫⁻ a, f a ∂μ
-- 文脈: {α} {m : MeasurableSpace α} {μ : Measure α}。★ [IsFiniteMeasure] / [SigmaFinite] 不要。

-- Bochner/Basic.lean:1175 — Markov (real, 非負可積分)
theorem mul_meas_ge_le_integral_of_nonneg {f : α → ℝ} (hf_nonneg : 0 ≤ᵐ[μ] f)
    (hf_int : Integrable f μ) (ε : ℝ) : ε * μ.real { x | ε ≤ f x } ≤ ∫ x, f x ∂μ

-- Variance.lean:397 — Chebyshev (★ [IsFiniteMeasure] 要求、volume 不可)
theorem meas_ge_le_variance_div_sq [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) {c : ℝ}
    (hc : 0 < c) : μ {ω | c ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (variance X μ / c ^ 2)
```

> **witness 3 の構造 + 前提事故 (orchestrator 必読)**: tail tightness の自然な道具 Chebyshev
> `meas_ge_le_variance_div_sq` は `[IsFiniteMeasure μ]` を要求。本件 `μ = volume` (無限測度) では
> **直接使えない**。正しい道筋: `f_{u n}` を密度に持つ確率測度 `μ_n = f_{u n}·volume` の遠方質量
> `μ_n {|x|≥R} = ∫_{|x|≥R} f_{u n} dx` を二次モーメント `∫x²f_{u n} = ∫x²pX + (u n)·v_g`
> (`u n→0` で一様有界) で Markov 評価。ここで **`volume` 上で直接使える `mul_meas_ge_le_lintegral`**
> (測度非依存) を `f_{u n}·x²` に適用するのが安全 (`∫⁻ x²·f_{u n} d volume` 一様有界 →
> `volume({|x|≥R}∩supp)` ではなく density-weighted tail mass を制御)。**UnifTight 定義は `sᶜ.indicator (negMulLog f_{u n})`
> の eLpNorm が小さい `s` (有限 volume measure) を要求**するので、`s = [-R, R]` (volume `2R < ∞`) を取り、
> `{|x|>R}` 上で `negMulLog f_{u n}` の Lp ノルムを二次モーメント tail で押さえる。`negMulLog` の符号構造
> (`x→∞` で `-∞`) があるため、tail 上の `|negMulLog f_{u n}|` を `f_{u n}` の二次モーメント tail に
> 結びつける評価が非自明 (witness 2 と同根の障害)。

> **二次モーメント計算の素材**: `f_{u n} = pX ∗ g_{u n}` の二次モーメント
> `∫ x²(pX ∗ g_t) = ∫x²pX + t·∫x²g_t` (独立和の分散加法性) は標準だが、**in-tree に
> `convDensityAdd` の二次モーメント補題は不在** (rg `moment.*convDensityAdd` → 0、下記 D)。
> 自作 (10〜25 行、`gaussianReal` の `variance_fun_id_gaussianReal` `Real.lean:518` + 畳込み分散加法)。

---

## カテゴリ D — 共通基盤 (密度同定 / 可積分性 / 二次モーメント)

| 概念 | Mathlib / InformationTheory API | file:line | 状態 | 3 witness での扱い |
|---|---|---|---|---|
| `convDensityAdd` 定義 | `InformationTheory.Shannon.EPIConvDensity.convDensityAdd` | `EPIConvDensity.lean:42` | ✅ | `f_t` 本体 (`∫ x, pX x · pY(z-x)`) |
| **密度同定** (pushforward) | `FisherInfoV2.pPath_eq_convDensityAdd` | `FisherInfoV2DeBruijnPerTime.lean:215` (`@audit:ok`) | ✅ | `f_{s·v_Z}` を `P.map(X+√s·Z)` の rnDeriv と同定 (maxent ルートの前提) |
| **per-time 可積分性** | `convDensityAdd_negMulLog_integrable_pub` | `EPIG2HeatFlowContinuity.lean:139` (`@audit:ok`) | ✅ | 各 `u n` で `Integrable (negMulLog f_{u n})` を供給 (Vitali `hFi` / maxent `h_ent_int`) |
| (同, 上流 private 元) | `FisherInfoV2.convDensityAdd_negMulLog_integrable` | `FisherInfoV2DeBruijnAssembly.lean:2529` (now public) | ✅ | 上の委譲先 |
| `convDensityAdd` 非負 | `convDensityAdd` (∫ 非負、要素から) | (witness 内 `integral_nonneg`) | ✅ | tail 評価で `f_{u n} ≥ 0` |
| `convDensityAdd` 可測 | `EPIConvDensity.convDensityAdd_pXpY_measurable` | `EPIConvDensityAssoc.lean:73` | ✅ | AEStronglyMeasurable 供給 |
| gaussian 分散 = v | `ProbabilityTheory.variance_fun_id_gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:518` | ✅ | `g_{u n}` の二次モーメント `= u n` |
| Gauss 畳込み分散倍化 | `convDensityAdd_gaussian_variance_double` | `EPIConvDensityAssoc.lean:178` (`@audit:ok`) | ✅ | `g_t ∗ g_t = g_{2t}` (補助) |
| **`f_t` 二次モーメント** `∫x²f_t = ∫x²pX + t·v_g` | — | — | ❌ **不在** (rg `moment.*convDensityAdd` 0) | witness 3 tail の核、自作 (10〜25 行) |

```lean
-- FisherInfoV2DeBruijnPerTime.lean:215 — 密度同定 (★ maxent ルートの前提)
theorem pPath_eq_convDensityAdd
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (v_Z : ℝ≥0) (hv_Z_pos : 0 < v_Z) (hZ_law : P.map Z = gaussianReal 0 v_Z)
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
    {s : ℝ} (hs : 0 < s) :
    (P.map (gaussianConvolution X Z s)).rnDeriv volume
      =ᵐ[volume] fun z => ENNReal.ofReal
        (convDensityAdd pX (gaussianPDFReal 0 ⟨s * v_Z, by positivity⟩) z)
-- ★ X, Z, P, v_Z, hZ_law を要求。witness 2/3 の現 signature (pX のみ) は持たない → maxent ルートは
--   witness signature 拡張 (X,Z,P precondition 追加) が要る。撤退ライン 2 と連動。

-- EPIG2HeatFlowContinuity.lean:139 — per-time 可積分性 (各 u n で negMulLog f_{u n} 可積分)
theorem convDensityAdd_negMulLog_integrable_pub
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x =>
      Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x)) volume
```

---

## 主要前提条件ボックス (前提事故が起きやすい lemma)

- **`differentialEntropy_le_gaussian_of_variance_le` (DifferentialEntropy.lean:520)** — Gaussian maxent
  上界。要求: **`[IsProbabilityMeasure μ]`**, `(hμ : μ ≪ volume)`, `(hv : v ≠ 0)`, `(h_mean : ∫ x ∂μ = m)`,
  `(h_var : ∫ (x-m)² ∂μ ≤ v)`, `(h_var_int : Integrable (fun x => (x-m)²) μ)`,
  **`(h_ent_int : Integrable (negMulLog ∘ (μ.rnDeriv volume).toReal) volume)`**。`μ = f_{u n}·volume`
  (確率測度) へ視点移動が必須 — `volume` 自体は確率測度でないので直接不可。`h_ent_int` は
  `convDensityAdd_negMulLog_integrable_pub` で供給可。**結論は積分値の上界** (indicator-tail には未変換)。
- **`meas_ge_le_variance_div_sq` (Variance.lean:397)** — Chebyshev。**`[IsFiniteMeasure μ]` 要求 →
  `volume` 不可**。密度測度 `f_{u n}·volume` (確率測度、有限) に適用するか、`volume` 上は
  `mul_meas_ge_le_lintegral` (測度非依存) を density-weighted moment に使う。
- **`tendsto_Lp_of_tendsto_ae` (UnifTight.lean:329)** — Vitali (無限測度 OK)。`hfg` = **full 列** ae 収束を
  要求 (witness 1 が部分列 ae しか出さないと不適合、カテゴリ A gap)。`f : ℕ → α → β` (列限定)。
- **`unifIntegrable_of` (UniformIntegrable.lean:653)** — `C` は **ε に一様 (i に依らず)**。witness 2 の
  indicator-tail 一様小はここが核で、maxent 上界 (積分値) から橋渡しが非自明。
- **`pPath_eq_convDensityAdd` (PerTime.lean:215)** — `X, Z, P, v_Z, hZ_law, pX` を要求。witness 2/3 の
  現 signature (`pX` のみ) は満たさない → maxent ルート採用時は witness signature 拡張が要る。
- **`TendstoInMeasure.exists_seq_tendsto_ae` (ConvergenceInMeasure.lean:277)** — 結論は **部分列**
  `f (ns i)` (StrictMono ns)。full 列 ae ではない。

---

## 自作が必要な要素 (優先度順)

1. **【最重要・witness 2 核】「∫|negMulLog f_{u n}| 一様有界 → UI」の de la Vallée-Poussin 橋** —
   maxent 上界 (`differentialEntropy_le_gaussian_of_variance_le`) で `∫ negMulLog f_{u n}` を二次モーメント
   一様に下界、`negMulLog_le_one_sub_self` で正部上界 → `∫|negMulLog f_{u n}|` 一様有界。これを
   `unifIntegrable_of` の indicator-tail 一様小に変換する橋が Mathlib に直接無い。工数感: **40〜80 行**
   (maxent 足場あっても橋が残る)。落とし穴: `negMulLog` 符号構造 (`x>1` で `-∞`)。**maxent ルートには
   witness 2 signature への `X,Z,P` precondition 追加が要る** (`pPath_eq_convDensityAdd` 前提)。
2. **【重要・witness 3 核】`f_t` 二次モーメント補題 + tail tightness** —
   `∫x²(pX ∗ g_t) = ∫x²pX + t·v_g` (in-tree 不在、自作 10〜25 行) + `mul_meas_ge_le_lintegral`
   (volume 直適用可) で density-weighted tail mass 一様小 → UnifTight。`s = [-R,R]` (volume 有限) を取り
   `{|x|>R}` 上 negMulLog Lp ノルムを tail moment で評価。工数感: **30〜60 行**。
3. **【中・witness 1 gap】full 列 ae の確立** — 層1 L¹ → `tendstoInMeasure_of_tendsto_eLpNorm` →
   `exists_seq_tendsto_ae` は **部分列 ae** のみ。full 列 ae を出すには (a) 層2 を `TendstoInMeasure`
   入力 + `tendsto_Lp_of_tendstoInMeasure` (UnifTight.lean) に書換 (部分列で足りる)、または
   (b) Gauss 核の Lebesgue 点 ae 点ごと収束を直接証明 (Besicovitch average、bump 版再現、工数大)。
   工数感: (a) 20〜40 行 (層2 書換)、(b) 60〜120 行 (直接証明)。**判断は親 plan 側 (signature 整合)。**
4. **【小】`f_{u n}·volume` の確率測度性 / `≪ volume` の構築** — maxent 上界適用の前提。
   `pPath_eq_convDensityAdd` + `P.map(X+√s·Z)` が確率測度 (pushforward of probability) から。工数感: **15〜30 行**。

合計工数感: **105〜290 行** (witness 2 の橋が支配項)。**maxent 上界 (in-tree 既存) が witness 2 を
真 moonshot から「橋 1 本の自作」に縮小する最大 leverage。**

---

## Mathlib 壁の列挙 (`@residual(wall:...)` 対象)

| 壁 | 内容 | loogle/rg 確認 | 集約推奨 |
|---|---|---|---|
| `wall:approx-identity-L1` (既存・親) | 近似単位元 `convDensityAdd pX g_t → pX` in L¹ as `t→0⁺` (層1) | `convolution_tendsto_right` は bump 限定、L¹ 一般 Found 0 | **既存 shared sorry `convDensityAdd_tendsto_L1_zero` (:96) に集約済**。3 witness はこれの transitive |
| 一般 mollifier ae 点ごと収束 | gaussianPDF + 一般 L¹ `pX` の ae 点ごと収束 | `MeasureTheory.convolution, Filter.Tendsto` → Found 4 (全 bump) | witness 1 を ae 直接ルートで攻めるなら新規。L¹→部分列 ae ルートなら `wall:approx-identity-L1` に集約 |
| de la Vallée-Poussin (∫一様有界→UI) 橋 | `∫|f_i|` 一様有界 → `unifIntegrable_of` indicator-tail | (loogle 確認推奨) — Mathlib に直接補題なし見込み | witness 2 の真の自作部分。**新規 shared sorry 候補ではなく genuine 自作** (素材在) |

> **集約方針**: 3 witness はいずれも層1 `wall:approx-identity-L1` の transitive 配下に既に置かれている
> (`@residual(wall:approx-identity-L1)`)。本調査の結論は **witness 2/3 は moonshot ではなく genuine 自作
> 可能** (maxent 上界 + Markov lintegral + 構成補題が在) であり、層1 (`wall:approx-identity-L1`) が
> 真壁として残る点は変わらない。witness 1 のみ層1 に依存 (足場)。**3 witness を genuine 化すれば
> 壁は層1 1 本に完全集約** — surface shrink の最終形。詳細 → `docs/audit/audit-tags.md`「共有 Mathlib 壁」。

---

## 撤退ラインへの距離

親 plan [`epi-g2-layer2-moonshot-plan.md`](epi-g2-layer2-moonshot-plan.md)「撤退ライン」:

> **撤退ライン 2**: UI/UT witness が `pX_mom` (有限2次モーメント) だけからは出ない (反例で偽)
> → 仮説強化 (落とし穴2 (a)、precondition 追加)。signature 変更 → 独立 honesty audit。
> **撤退ライン 3**: 落とし穴2 が precondition 追加でも解けない → 真 moonshot。

**判定: 撤退ライン 2 に触れるが踏み抜かない (発動 no、ただし条件付き)。**

- **witness 2 (UI)**: `pX_mom` だけからは indicator-tail 一様小は直接出ない (negMulLog 符号構造)。だが
  **in-tree maxent 上界 `differentialEntropy_le_gaussian_of_variance_le` が `∫ negMulLog f_{u n}` を
  二次モーメント一様に下界し、足場が在る**。撤退ライン 2 の「反例で偽」には該当せず (maxent ルートで
  原理的に出る)。ただし maxent 適用には witness signature への `X,Z,P` precondition (または `hpX_ent` 型)
  追加が要る可能性 — これは撤退ライン 2 の「precondition 追加」(honesty OK) の範囲内。**発動せず、
  precondition 補強で吸収。**
- **witness 3 (UT)**: 二次モーメント tail tightness は `mul_meas_ge_le_lintegral` (volume 直適用可) +
  `f_t` 二次モーメント (自作) で genuine に出る見込み。`pX_mom` が tail を直接駆動 (`u n→0` で分散
  `∫x²pX + u n·v_g` 一様有界)。**発動せず。**
- **witness 1 (ae)**: 層1 (`wall:approx-identity-L1`) に依存。層1 が genuine 化されれば
  L¹→測度→部分列 ae は genuine。full 列 ae gap は signature 整合 (撤退でなく設計) の問題。**発動せず。**

**新規撤退ライン提案 (witness 2 専用)**: maxent ルートの indicator-tail 橋 (de la Vallée-Poussin) が
2 週間で書けない、かつ `unifIntegrable_of_tendsto_Lp` (`:553`) 経由も `negMulLog f_{u n}` の L¹ 収束
(層1 と別物) が出ず循環で塞がる場合 → witness 2 を `sorry` + `@residual(wall:approx-identity-L1)`
維持で park 継続 (現状)。**仮説束化禁止** (UI/UT を `*Hypothesis` predicate に bundle しない、load-bearing)。
maxent ルートの precondition 追加 (`X,Z,P` / `hpX_ent`) は OK だが、それでも橋が出ない場合のみ真 moonshot
(`docs/audit/audit-tags.md`「共有 Mathlib 壁」で `wall:` 新設 + loogle 0 件再確認)。

---

## 着手 skeleton

```lean
import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import InformationTheory.Shannon.EPIConvDensity
import InformationTheory.Shannon.DifferentialEntropy            -- maxent 上界
import InformationTheory.Shannon.FisherInfoV2DeBruijnPerTime    -- pPath_eq_convDensityAdd

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open InformationTheory.Shannon.EPIConvDensity
open scoped ENNReal NNReal Topology

/-- witness 3 補助: `f_t = pX ∗ g_t` の二次モーメント (in-tree 不在、自作)。
`∫ x², (convDensityAdd pX g_t) = ∫ x²·pX + t·v_g`。witness 3 tail tightness の核。 -/
theorem convDensityAdd_second_moment
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) {t : ℝ} (ht : 0 < t) :
    -- 結論型は実装時に ∫ x², (convDensityAdd ...) = ... の closed form に確定
    True := by sorry  -- skeleton 方向性のみ (planner/implementer 責務、:True は inventory 記述用)

-- witness 1/2/3 本体は EPIG2HeatFlowContinuity.lean:159/176/194 に既存 (sorry park 済)。
-- 本 skeleton は補助補題 (二次モーメント) と maxent ルート結線の足場を示すのみ。

end InformationTheory.Shannon
```

> skeleton は方向性提示のみ (planner/implementer 責務)。3 witness 本体は既存 file に park 済なので
> 新 file は補助補題 (二次モーメント / de la Vallée-Poussin 橋) 用。`:True` は inventory 記述用の
> placeholder (コードでないため許容、実装時は本来の結論型に置換)。
