# EPI G2 UI witness — de la Vallée-Poussin 橋 Mathlib 在庫 (深掘り)

> 対象: `wall:approx-identity-L1` 配下の **UI witness のみ**
> `negMulLog_convDensity_unifIntegrable` (`InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean:144`)。
> 焦点 = 「**`∫|negMulLog f_{u n}|` 一様有界 → `UnifIntegrable`**」の de la Vallée-Poussin 型橋が
> Mathlib に在るか否かの確定。
>
> 親計画: [`epi-g2-vitali-closure-plan.md`](epi-g2-vitali-closure-plan.md) Phase C (UI、最難)。
> 先行在庫: [`epi-g2-vitali-witness-inventory.md`](epi-g2-vitali-witness-inventory.md) カテゴリ B
> (UI 構成補題 27 件の俯瞰)。本ファイルはその「de la Vallée-Poussin 橋の有無」を **決着** させる
> 補完調査 (重複部は参照のみ、新規発見 = `iSup`/`BddAbove`-UI 系の loogle 0 件確認に集中)。
> loogle index: 2026-06-04 build (`.lake/build/loogle.index` 既存)。Mathlib lemma 網羅、
> InformationTheory 定義は rg 併用。

`f_n := convDensityAdd pX (gaussianPDFReal 0 ⟨u n,_⟩) = pX ∗ g_{u n}` (Gauss 核分散 `u n > 0`)。
目標: `UnifIntegrable (fun n x => Real.negMulLog (f_n x)) 1 volume` (μ=volume、`[IsFiniteMeasure]`-free)。

---

## 一行サマリ — **(B) 素材はあるが自作橋要**

**de la Vallée-Poussin 定理 (`∫ G(|f_i|)` 一様有界 → UnifIntegrable、G superlinear) は Mathlib 全域に
不在 (loogle/rg 0 件、決定的)。`UnifIntegrable`/`UniformIntegrable` を `iSup`/`BddAbove`/「積分の一様
上界」から導く補題も 0 件。** したがって UI witness は「Mathlib の直接補題」(A) ではない。一方で
`unifIntegrable_of` (`UniformIntegrable.lean:653`、`[IsFiniteMeasure]`-free) という **indicator-tail
一様小 → UI** の正規入口と、その indicator-tail を p=1 で `∫⁻_{C≤|f_i|} ‖f_i‖` に落とす素材
(`eLpNorm_indicator_eq_eLpNorm_restrict` 等)、および maxent 上界
`differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:520`) は **すべて在る**。
**橋 = 「`∫|negMulLog f_n|` を二次モーメント一様に押さえる」→「`{C ≤ |negMulLog f_n|}` 上の `∫⁻` を `C`
一様に小さくする」の Markov-on-set 自作部分** (de la Vallée-Poussin の手結証明) で、これは genuine
自作可能 (新 wall 不要)。

**既存率: 素材 ~70%（`unifIntegrable_of` 入口 + p=1 indicator 還元 + maxent 上界 + Markov-lintegral
在）/ 自作必要 = 橋 1 本 (de la Vallée-Poussin の手結) + maxent framing 補助。撤退ライン発動: no
(撤退ライン 2 に触れるが、maxent precondition 補強で吸収)。**

**GO/NO-GO: 条件付き GO** — UI witness は genuine 化可能 (真 moonshot / 新 `wall:` 不要)。ただし
maxent ルートを採るなら witness signature への precondition 追加 (確率測度 framing) が要る。

---

## UI witness 最終形 (verbatim 再掲)

```lean
-- EPIG2HeatFlowContinuity.lean:144 — UI witness (現状 sorry + @residual(wall:approx-identity-L1))
theorem negMulLog_convDensity_unifIntegrable
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) :
    UnifIntegrable
      (fun n => fun x =>
        Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x))
      1 volume
```

証明戦略案 (pseudo-Lean、橋の所在を明示):

```text
-- Step 1 (Mathlib 在): unifIntegrable_of で UI を indicator-tail 一様小に還元
apply unifIntegrable_of (hp := le_refl 1) (hp' := one_ne_top) (hf := <AEStronglyMeasurable, 在>)
intro ε hε
-- 目標: ∃ C : ℝ≥0, ∀ n, eLpNorm ({x | C ≤ ‖negMulLog (f_n x)‖₊}.indicator (negMulLog ∘ f_n)) 1 volume ≤ ofReal ε

-- Step 2 (p=1 還元、Mathlib 在): eLpNorm (s.indicator g) 1 volume = ∫⁻_s ‖g‖₊
--   ⟹ 目標は ∫⁻_{C ≤ |negMulLog f_n|} ‖negMulLog (f_n x)‖ ∂volume ≤ ofReal ε (n 一様)

-- Step 3 (maxent 上界、in-tree 在 differentialEntropy_le_gaussian_of_variance_le):
--   μ_n := f_n · volume を確率測度 (≪ volume) と見て ∫ negMulLog f_n = differentialEntropy μ_n
--   ≤ (1/2) log(2πe·V_n) (上界)、V_n = ∫x²pX + u n·v_g (u n→0 で一様有界)。← 自作 framing
--   + maxent 下界補助 (∫ negMulLog ≥ -(1/2)log(2πe·V_n) も対称に出ない、正部の取り扱いが要)

-- Step 4 (★ 真の自作橋 = de la Vallée-Poussin 手結):
--   ∫|negMulLog f_n| 一様有界 M ⟹ ∫⁻_{C ≤ |negMulLog f_n|} |negMulLog f_n| → 0 一様 (C→∞)
--   Markov-on-set: ∫⁻_{C≤|g|} |g| は M に支配されつつ {C≤|g|} の質量 → 0、しかし
--   「積分の tail が C 一様に小」は単なる ∫|g|≤M では出ない (← de la Vallée-Poussin の本質、
--    superlinear moment G(|g|) の一様有界が必要)。Mathlib に補題なし、手結自作。
```

---

## カテゴリ A — UI 構成入口 (Mathlib 在、`[IsFiniteMeasure]`-free)

| 概念 | Mathlib API | file:line | 状態 | UI での扱い |
|---|---|---|---|---|
| **indicator-tail 一様小 → UI** (正規入口) | `MeasureTheory.unifIntegrable_of` | `MeasureTheory/Function/UniformIntegrable.lean:653` | ✅ | **第一候補**。`C` を ε に一様 (i 非依存) に取り `{C≤‖f i‖} 上 indicator eLpNorm ≤ ε`。`[IsFiniteMeasure]` 不要 = volume OK |
| 同 (StronglyMeasurable + `0<C` 版) | `MeasureTheory.unifIntegrable_of'` | `UniformIntegrable.lean:589` | ✅ | `unifIntegrable_of` の下層 (内部で `eLpNorm (s.indicator) ≤ eLpNorm({C≤}.indicator) + C·μ s^(1/p)` 分解) |
| p=1 indicator eLpNorm = setLIntegral | `MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict` | `MeasureTheory/Function/LpSeminorm/Indicator.lean` (loogle Q6) | ✅ | `eLpNorm (s.indicator g) 1 μ` を `∫⁻_s ‖g‖₊` に落とす (Step 2) |
| 単一 `MemLp` の indicator-tail → 0 (per-f、★ 一様性なし) | `MeasureTheory.MemLp.eLpNorm_indicator_norm_ge_le` | `UniformIntegrable.lean:272` | ✅ | 単一 `f` の `M` を返す。**`M` は f 依存 = 一様 `C` を直接は与えない** (UI gap の所在) |
| 同 (∫⁻ 版、p=1) | `MeasureTheory.MemLp.integral_indicator_norm_ge_le` | `UniformIntegrable.lean:194` | ✅ | `∃ M, ∫⁻_{M≤‖f‖} ‖f‖₊ ≤ ofReal ε` (単一 f、DCT 経由)。橋の手結で参考 |
| 同 (`0<M` 版) | `MeasureTheory.MemLp.eLpNorm_indicator_norm_ge_pos_le` | `UniformIntegrable.lean:307` | ✅ | `0 < M` 保証付き |
| 定数族 UI | `MeasureTheory.unifIntegrable_const` | `UniformIntegrable.lean:405` | ✅ | `{negMulLog pX}` 補助 (`f = const + (f-const)` 分解時) |
| 有限族 UI | `MeasureTheory.unifIntegrable_finite` | `UniformIntegrable.lean:444` (`[Finite ι]`) | ✅ | 有限 prefix 処理 |

#### 主要補題の verbatim signature (型クラス前提込み)

```lean
-- UniformIntegrable.lean:653 — indicator-tail 一様小 → UI (★ UI witness の正規入口)
theorem unifIntegrable_of (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0,
      ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε) :
    UnifIntegrable f p μ
-- 文脈 variable: {α β ι} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
--   [NormedAddCommGroup β]。★ [IsFiniteMeasure] 不要 (volume OK)。★ `C` は ε に一様 (i 非依存) = UI gap の核。

-- UniformIntegrable.lean:589 — indicator-tail 一様小 → UI (StronglyMeasurable + 0<C 版、下層)
theorem unifIntegrable_of' (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, StronglyMeasurable (f i))
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, 0 < C ∧
      ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε) :
    UnifIntegrable f p μ
-- ★ 内部 calc: eLpNorm (s.indicator (f i)) ≤ eLpNorm ({C≤‖f i‖}.indicator (f i)) + C·μ s^(1/toReal p)。
--   p=1 では μ s 項が線形、indicator-tail 項が de la Vallée-Poussin で C 一様に小さくできれば UI。

-- UniformIntegrable.lean:272 — 単一 MemLp の indicator-tail → 0 (★ M は f 依存、一様性なし = gap 源)
theorem MemLp.eLpNorm_indicator_norm_ge_le (hf : MemLp f p μ) (hmeas : StronglyMeasurable f) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ M : ℝ, eLpNorm ({ x | M ≤ ‖f x‖₊ }.indicator f) p μ ≤ ENNReal.ofReal ε
-- 文脈: {f : α → β} {p : ℝ≥0∞}。★ 単一 f に対し M を返す。family で M を一様化する仕組みは無い。

-- UniformIntegrable.lean:194 — 単一 MemLp の ∫⁻ indicator-tail → 0 (p=1、DCT 経由)
theorem MemLp.integral_indicator_norm_ge_le (hf : MemLp f 1 μ) (hmeas : StronglyMeasurable f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, (∫⁻ x, ‖{ x | M ≤ ‖f x‖₊ }.indicator f x‖₊ ∂μ) ≤ ENNReal.ofReal ε
-- ★ 証明は tendsto_indicator_ge + tendsto_lintegral_norm_of_dominated_convergence (DCT)。
--   単一 f の支配収束で M を出す。family 一様化はここに無い (de la Vallée-Poussin が要る理由)。
```

---

## カテゴリ B — de la Vallée-Poussin 橋の **不在確定** (loogle 否定記録)

### ❌ 「∫ G(|f_i|) 一様有界 → UnifIntegrable」型は Mathlib 全域に不在

| 探索対象 | クエリ / コマンド | 結果 | 含意 |
|---|---|---|---|
| de la Vallée-Poussin (name) | loogle `deLaValleePoussin` / `de_la_vallee_poussin` | **unknown identifier** (echo のみ、実 declaration 0) | 名前付き定理なし |
| 同 (text、全 Mathlib) | `rg -li "Vallée\|Poussin\|de la Vall"` Mathlib 全域 | **0 件** | docstring/コメントにも一切なし |
| superlinear moment 系 | `rg -ni "superlinear\|super.?linear"` MeasureTheory/Function | **0 件** | superlinear-growth → UI の定式化なし |
| **`iSup`/積分一様有界 → UI** | loogle `MeasureTheory.UnifIntegrable, iSup` | **Found 0** | 「∫ の sup 有界 → UI」補題なし |
| **`BddAbove` → UI** | loogle `MeasureTheory.UniformIntegrable, BddAbove` | **Found 0** | 一様有界性 → UI 補題なし |
| 一様 `MemLp` (q>p) → UI | loogle `MeasureTheory.MemLp, MeasureTheory.UnifIntegrable` | Found 13 (const/finite/subsingleton/fin/tendsto_Lp 系のみ、**一様 Lq 域 → UI は無し**) | 「sup‖f_i‖_q < ∞ (q>p) ⟹ UI in Lp」も不在 |
| 一様 `eLpNorm` 上界 → UI | loogle `MeasureTheory.UnifIntegrable, MeasureTheory.eLpNorm` (Found 11) | indicator-tail (`unifIntegrable_of/of'`) + tendsto_Lp 系のみ。**一様 eLpNorm 上界からの直接構成は無し** | 同上 |

> **de la Vallée-Poussin 橋の不在 (決定的)**: Mathlib の `UniformIntegrable.lean` (983 行) が提供する
> UI 十分条件は **4 系統のみ** — (1) indicator-tail 一様小 (`unifIntegrable_of`/`of'`)、(2) 定数族
> (`unifIntegrable_const`)、(3) 有限族 (`unifIntegrable_finite`/`fin`/`subsingleton`)、(4) Lp 収束
> (`unifIntegrable_of_tendsto_Lp(_zero)`)。**「積分量 (`∫|f_i|`・`∫ G(|f_i|)`・`sup eLpNorm`) の一様有界
> 性から UI を出す」de la Vallée-Poussin 系統は 1 つも無い。** これは「素材はあるが橋は自作」(B) を
> 決定づける否定記録。de la Vallée-Poussin の手結証明 (superlinear moment `∫ |g|·log⁺|g|` 一様有界
> → tail 質量 `∫⁻_{C≤|g|}|g| ≤ M/log C → 0` 一様) を自作する以外に道はない。

#### Lp 収束ルート (`unifIntegrable_of_tendsto_Lp`) は循環で塞がる

```lean
-- UniformIntegrable.lean:553 — L¹ 収束 → UI (★ 循環注意)
theorem unifIntegrable_of_tendsto_Lp (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : ∀ n, MemLp (f n) p μ)
    (hg : MemLp g p μ) (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)) :
    UnifIntegrable f p μ
-- 文脈: {f : ℕ → α → β} {g : α → β}。★ hfg = `negMulLog f_n` の L¹ 収束。これは層1 (密度 f_n の
--   L¹ 収束) とは別物 — negMulLog は非 Lipschitz なので密度 L¹ 収束は negMulLog 合成の L¹ 収束を
--   自動では与えない (親 plan が Vitali を選んだ真因、`wall:approx-identity-L1` docstring 参照)。
--   よって UI を「negMulLog f_n の L¹ 収束」から出すルートは、求めたいもの自身に依存し循環。
```

---

## カテゴリ C — maxent framing + Markov-on-set 素材 (橋の足場、在)

| 概念 | API | file:line | 状態 | 橋での扱い |
|---|---|---|---|---|
| **Gaussian maxent 上界** | `InformationTheory.Shannon.differentialEntropy_le_gaussian_of_variance_le` | `DifferentialEntropy.lean:520` (`@entry_point`) | ✅ | `differentialEntropy μ_n = ∫ negMulLog f_n ≤ (1/2)log(2πe·V_n)` (上界)、V_n 一様 |
| `differentialEntropy` 定義 | `differentialEntropy μ = ∫ negMulLog (rnDeriv μ volume).toReal` | `DifferentialEntropy.lean:45` | ✅ | `μ_n = f_n·volume` で `rnDeriv = f_n` ⟹ `differentialEntropy μ_n = ∫ negMulLog f_n` |
| negMulLog 正部上界 | `Real.negMulLog_le_one_sub_self` | `NegMulLog.lean:234` | ✅ | `negMulLog t ≤ 1 - t` (`0≤t`)、正部 `{t>1}` 領域の上界 |
| negMulLog `[0,1]` 非負 | `Real.negMulLog_nonneg` | `NegMulLog.lean:174` | ✅ | `0 ≤ negMulLog t` (`0≤t≤1`)。符号構造の場合分けに必須 |
| negMulLog 連続 | `Real.continuous_negMulLog` | `NegMulLog.lean:186` (`@[fun_prop]`) | ✅ | 可測性/AEStronglyMeasurable 供給 |
| **Markov (lintegral、測度非依存)** | `MeasureTheory.mul_meas_ge_le_lintegral` | `MeasureTheory/Integral/Lebesgue/Markov.lean:57` | ✅ | `C·μ{C≤g} ≤ ∫⁻ g`。volume で使える (de la VP 手結の核) |
| Markov (lintegral, ae 版) | `MeasureTheory.mul_meas_ge_le_lintegral₀` | `Lebesgue/Markov.lean:50` | ✅ | AEMeasurable 版 |
| setLIntegral ≤ lintegral | `MeasureTheory.setLIntegral_le_lintegral` | `MeasureTheory/Integral/Lebesgue/Basic.lean` (loogle Q9) | ✅ | `∫⁻_s g ≤ ∫⁻ g` (橋の単調性) |
| 確率測度 ≪ (framing) | `MeasureTheory.withDensity_absolutelyContinuous` | `MeasureTheory/Measure/WithDensity.lean:147` | ✅ | `volume.withDensity f ≪ volume` (maxent の `hμ` 供給) |
| IsProbabilityMeasure 構成 | `MeasureTheory.IsProbabilityMeasure.mk` | `Measure/Typeclasses/Probability.lean` (loogle Q16) | ✅ | `μ univ = 1` から (mass `hpX_mass` + Gauss mass) |
| 密度同定 (maxent 前提) | `FisherInfoV2.pPath_eq_convDensityAdd` | `FisherInfoV2DeBruijnPerTime.lean:215` (`@audit:ok`) | ✅ | `(P.map(X+√s·Z)).rnDeriv volume =ᵐ ofReal∘(convDensityAdd ...)`。**`X,Z,P,v_Z,hZ_law` を要求** |
| per-time 可積分性 (h_ent_int 供給) | `convDensityAdd_negMulLog_integrable_pub` | `EPIG2HeatFlowContinuity.lean:124` (`@audit:ok`) | ✅ | maxent の `h_ent_int` を各 `u n` で供給 |

#### 主要補題の verbatim signature (型クラス前提込み)

```lean
-- DifferentialEntropy.lean:520 — Gaussian maxent 上界 (★ 橋の二次モーメント足場)
theorem differentialEntropy_le_gaussian_of_variance_le
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (h_mean : ∫ x, x ∂μ = m)
    (h_var : ∫ x, (x - m)^2 ∂μ ≤ (v : ℝ))
    (h_var_int : Integrable (fun x => (x - m)^2) μ)
    (h_ent_int : Integrable
      (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) :
    differentialEntropy μ ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)
-- ★ [IsProbabilityMeasure μ] 要求 → μ = f_n·volume (確率測度) へ視点移動が必須、volume 直適用不可。
-- ★ 結論は differentialEntropy μ = ∫ negMulLog f_n の **上界** (DifferentialEntropy.lean:45 で
--   differentialEntropy = ∫ negMulLog rnDeriv、μ_n の rnDeriv = f_n)。

-- DifferentialEntropy.lean:45 — differentialEntropy 定義 (上界の左辺が ∫ negMulLog である根拠)
noncomputable def differentialEntropy (μ : Measure ℝ) : ℝ :=
  ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume

-- NegMulLog.lean:234 / :174 — negMulLog の符号制御 (∫|negMulLog| の正部/負部分解)
lemma Real.negMulLog_le_one_sub_self {x : ℝ} (h0 : 0 ≤ x) : x.negMulLog ≤ 1 - x
lemma Real.negMulLog_nonneg {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) : 0 ≤ negMulLog x

-- Lebesgue/Markov.lean:57 — Markov (★ 測度非依存、volume OK、de la VP 手結の核)
theorem mul_meas_ge_le_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ f x } ≤ ∫⁻ a, f a ∂μ
-- 文脈: {α} {m : MeasurableSpace α} {μ : Measure α}。★ [IsFiniteMeasure]/[SigmaFinite] 不要。

-- Measure/WithDensity.lean:147 — withDensity ≪ (maxent の hμ framing)
theorem withDensity_absolutelyContinuous {m : MeasurableSpace α} (μ : Measure α) (f : α → ℝ≥0∞) :
    μ.withDensity f ≪ μ

-- FisherInfoV2DeBruijnPerTime.lean:215 — 密度同定 (maxent ルートの前提、X,Z,P 要求)
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
```

---

## 主要前提条件ボックス (前提事故が起きやすい lemma)

- **`differentialEntropy_le_gaussian_of_variance_le` (DifferentialEntropy.lean:520)** — 要求:
  **`[IsProbabilityMeasure μ]`**, `(hμ : μ ≪ volume)`, `(hv : v ≠ 0)`, `(h_mean : ∫ x ∂μ = m)`,
  `(h_var : ∫ (x-m)² ∂μ ≤ v)`, `(h_var_int : Integrable (fun x => (x-m)²) μ)`,
  **`(h_ent_int : Integrable (negMulLog ∘ (μ.rnDeriv volume).toReal) volume)`**。`μ = f_n·volume`
  (確率測度) へ視点移動必須 — `volume` は確率測度でないので **直接不可**。`h_ent_int` は
  `convDensityAdd_negMulLog_integrable_pub` (`:124`) で各 `u n` 供給可。**結論は積分値の上界**
  (indicator-tail には未変換 = de la VP 橋がここから先)。
- **`pPath_eq_convDensityAdd` (PerTime.lean:215)** — `X, Z, P, v_Z, hZ_law, hpX_law` を要求。**UI witness の
  現 signature (`pX` のみ、`X,Z,P` を持たない)** はこれを満たさない → maxent ルート採用時は witness
  signature 拡張 (確率測度 framing の precondition 追加) が要る。撤退ライン 2 と連動。
- **`unifIntegrable_of` (UniformIntegrable.lean:653)** — `C` は **ε に一様 (i 非依存)**。これが UI gap の
  核で、de la Vallée-Poussin の手結で一様 `C` を構成する必要。**素材 (`MemLp.eLpNorm_indicator_norm_ge_le`
  :272) は単一 f の M しか返さない** ので、family 一様化は自作。
- **`mul_meas_ge_le_lintegral` (Markov.lean:57)** — 測度非依存、volume OK。`f` に `‖negMulLog f_n‖₊` を
  入れて `C·volume{C≤|negMulLog f_n|} ≤ ∫⁻|negMulLog f_n|`。**ただし質量バウンドであって積分 tail
  バウンドではない** — de la VP の本質 (`∫⁻_{C≤|g|}|g| → 0` 一様) には superlinear moment が要り、
  単純 Markov では tail 質量しか出ない (橋の難所)。

---

## 自作が必要な要素 (優先度順)

1. **【最重要・橋の核】de la Vallée-Poussin の手結証明** —
   「`∫ φ(|negMulLog f_n|)` 一様有界 (φ superlinear、例 `φ(t)=t·log⁺t` または二次モーメント由来) →
   `∫⁻_{C≤|negMulLog f_n|}|negMulLog f_n| ≤ (M / ψ(C)) → 0` 一様 (C→∞)」を組む。maxent 上界で
   `∫ negMulLog f_n` (符号付き積分値) の一様上界を取り、`negMulLog_le_one_sub_self` で正部、
   `negMulLog_nonneg` で `[0,1]` 領域を分け、`mul_meas_ge_le_lintegral` で tail を C 一様に押さえる。
   **superlinear moment (単なる `∫|negMulLog f_n|≤M` では tail 一様性が出ない、de la VP の本質)** が
   要点。工数感: **50〜100 行** (素材在でも橋の手結が支配項、`negMulLog` 符号構造 `t>1→-∞` が落とし穴)。
2. **【中・maxent framing】UI witness signature への確率測度 precondition 追加** —
   `μ_n := f_n·volume` を `[IsProbabilityMeasure]` + `≪ volume` と framing するために `pPath_eq_convDensityAdd`
   を呼ぶには `X,Z,P,v_Z,hZ_law` が要る。witness 現 signature は `pX` のみなので、(a) signature に
   `X,Z,P` precondition を追加するか、(b) `volume.withDensity (ofReal ∘ f_n)` を直接構成し
   `withDensity_absolutelyContinuous` + `IsProbabilityMeasure.mk` (mass = `hpX_mass` + Gauss conv mass)
   で確率測度性を出す (pPath を迂回)。**(b) のほうが signature 改変が小さく推奨** (`X,Z,P` 不要)。
   工数感: **20〜40 行** (mass の一様性 `∫ f_n = 1` 確認 + 二次モーメント `V_n` 一様有界の補題)。
3. **【小・足場】`f_n` 二次モーメント `∫x²f_n = ∫x²pX + (u n)·v_g`** — maxent の `h_var` (分散 ≤ V_n)
   を供給。in-tree 不在 (先行在庫 D 参照、rg `moment.*convDensityAdd` → 0)。自作 **10〜25 行**
   (`variance_fun_id_gaussianReal` Real.lean:518 + 畳込み分散加法)。witness 3 (UT) と共有可。

合計工数感: **80〜165 行** (de la Vallée-Poussin 橋が支配項)。**maxent 上界 (in-tree 既存) が UI を
真 moonshot から「橋 1 本 + framing」に縮小する最大 leverage。**

---

## Mathlib 壁の列挙 (`@residual(wall:...)` 対象)

| 壁 | 内容 | loogle/rg 確認 | 集約推奨 |
|---|---|---|---|
| **de la Vallée-Poussin (∫ G(\|f_i\|) 一様有界 → UI)** | superlinear moment 一様有界 → UnifIntegrable の判定条件 | loogle `UnifIntegrable, iSup` → **Found 0**; `UniformIntegrable, BddAbove` → **Found 0**; `MemLp, UnifIntegrable` → Found 13 (一様 Lq 域 → UI **無し**); rg `Vallée\|Poussin\|superlinear` Mathlib 全域 → **0 件** | **新 `wall:` 不要 = genuine 自作** (素材 = maxent 上界 + Markov-lintegral + indicator 還元が在)。`wall:approx-identity-L1` 配下に既に置かれており、UI witness を genuine 化すれば壁は層1 に集約 |
| `wall:approx-identity-L1` (親、既存) | 近似単位元 L¹ 収束 (層1)。密度 L¹ は CLOSED、残 active = UI/UT/ae witness 3 本のみ | (先行在庫参照) | UI witness は本壁の active residual 3 本のうち最難。genuine 化で本壁を ae/UT 2 本に縮小 |

> **集約方針**: de la Vallée-Poussin 橋は **真の Mathlib 不在だが「新 `wall:` 新設対象」ではない** —
> maxent 上界 (`differentialEntropy_le_gaussian_of_variance_le`、in-tree `@entry_point`) +
> Markov-lintegral (`mul_meas_ge_le_lintegral`、測度非依存) + indicator 還元 (`unifIntegrable_of` の
> p=1 setLIntegral 形) という素材が揃っており、**de la Vallée-Poussin の手結証明で genuine に閉じる**
> 見込み。新 wall (`wall:de-la-vallee-poussin` 等) を register に追加するのは、(a) 手結が
> 2 週間で書けず、かつ (b) 上流 Mathlib PR (de la Vallée-Poussin を Mathlib に入れる) を待つ判断に
> なった場合のみ。現状は UI witness の `@residual(wall:approx-identity-L1)` を維持 (層1 集約済)。
> 詳細 → `docs/audit/audit-tags.md`「共有 Mathlib 壁: shared sorry 補題パターン」。

---

## 撤退ラインへの距離

親 plan [`epi-g2-vitali-closure-plan.md`](epi-g2-vitali-closure-plan.md) / 先行在庫の「撤退ライン 2」:

> **撤退ライン 2**: UI/UT witness が `pX_mom` (有限2次モーメント) だけからは出ない (反例で偽)
> → 仮説強化 (precondition 追加)。signature 変更 → 独立 honesty audit。
> **撤退ライン 3**: precondition 追加でも解けない → 真 moonshot (`wall:` 新設)。

**判定: 撤退ライン 2 に触れるが踏み抜かない (発動 no、条件付き)。**

- **de la Vallée-Poussin 橋は `pX_mom` だけからは indicator-tail 一様小を直接出せない** (negMulLog 符号
  構造 + de la VP の superlinear moment 要件)。だが **in-tree maxent 上界が `∫ negMulLog f_n` を二次
  モーメント一様に上界**し、足場が在る。撤退ライン 2 の「反例で偽」には該当しない (maxent ルートで
  原理的に出る、偽でなく自作量の問題)。
- maxent 適用には UI witness signature への **確率測度 framing precondition** (自作要素 2、`X,Z,P` 追加
  または `withDensity` 直構成) が要る可能性 — これは撤退ライン 2 の「precondition 追加」(honesty OK、
  regularity precondition であり load-bearing でない) の範囲内。**発動せず、precondition 補強で吸収。**

**新規撤退ライン提案 (UI witness 専用)**: de la Vallée-Poussin 橋の手結 (自作要素 1) が 2 週間で
書けず、かつ maxent framing (自作要素 2) も `withDensity` 直構成で詰まる場合 → UI witness を
`sorry` + `@residual(wall:approx-identity-L1)` 維持で park 継続 (現状)。**仮説束化禁止** (UI を
`*Hypothesis` predicate に bundle しない、load-bearing)。precondition 追加 (確率測度 framing) は OK だが、
それでも橋が出ない場合のみ真 moonshot として `wall:de-la-vallee-poussin` を register 新設 + loogle 0 件
再確認 (本ファイルの否定記録を SoT に転記)。撤退口は `sorry` + `@residual`、仮説束化禁止。

---

## 着手 skeleton

```lean
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import InformationTheory.Shannon.EPIConvDensity
import InformationTheory.Shannon.DifferentialEntropy            -- maxent 上界
import InformationTheory.Shannon.FisherInfoV2DeBruijnPerTime    -- pPath_eq_convDensityAdd (採用時)

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open InformationTheory.Shannon.EPIConvDensity
open scoped ENNReal NNReal Topology

/-- 橋の核補助 (de la Vallée-Poussin 手結、自作要素 1)。
maxent 上界で `∫ negMulLog f_n` を二次モーメント一様に押さえた状態から、
`{C ≤ ‖negMulLog f_n‖} 上の `∫⁻` を C 一様に小さくする。
結論型は実装時に `∀ ε>0, ∃ C, ∀ n, eLpNorm ({C≤‖negMulLog f_n‖₊}.indicator (negMulLog ∘ f_n)) 1 volume ≤ ofReal ε`
の形に確定 (unifIntegrable_of の入力に直結)。

@residual(wall:approx-identity-L1) -/
theorem negMulLog_convDensity_indicatorTail_uniform
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ n,
      eLpNorm
        ({ x | C ≤ ‖Real.negMulLog
            (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x)‖₊ }.indicator
          (fun x => Real.negMulLog
            (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x)))
        1 volume ≤ ENNReal.ofReal ε := by
  sorry

-- UI witness 本体 (EPIG2HeatFlowContinuity.lean:144、sorry park 済) は上の補助 +
-- unifIntegrable_of (le_refl 1) one_ne_top <AEStronglyMeasurable> で genuine 化される想定。
-- 本 skeleton は de la Vallée-Poussin 橋 (自作要素 1) の signature を示すのみ。

end InformationTheory.Shannon
```

> skeleton は方向性提示のみ (planner/implementer 責務)。UI witness 本体は既存 file に park 済なので、
> 新規補助補題 = de la Vallée-Poussin 橋 + maxent framing。`@residual(wall:approx-identity-L1)` を
> 継承 (層1 集約済)。`mass`/`mom` は regularity precondition (load-bearing でない)。
