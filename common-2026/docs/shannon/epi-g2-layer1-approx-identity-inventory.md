# EPI G2 層1 (近似単位元 L¹ 収束) — Mathlib 組上げ部品 在庫

> 対象: `wall:approx-identity-L1` の核命題
> `convDensityAdd_tendsto_L1_zero` (`InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean:96`)。
> EPI G2 の **唯一の残り壁**。層2 の machinery (Vitali / L¹→積分 / exp) は既に genuine 化済
> (`differentialEntropy_convDensity_integral_tendsto` の body は own-sorry 0)。本ファイルは層1 を
> genuine に閉じる**組上げ部品** (translation continuity / Minkowski / convolution 接続 / approx-identity
> 一般定理) の在不在を新たに深掘りする在庫調査。実装・計画起草はしない。
> 出発点 (mollifier 不在のみ記載): [`epi-g2-layer2-semicontinuity-inventory.md`](epi-g2-layer2-semicontinuity-inventory.md) カテゴリ4。
> loogle index: 2026-05-10 build (Mathlib lemma は網羅、InformationTheory 定義は古い → rg 併用)。

## 一行サマリ

**層1 L¹ 収束を閉じる 3 大組上げ部品のうち、(1) L¹ 平行移動連続性は `Lp.compMeasurePreserving_continuous` /
`Filter.Tendsto.compMeasurePreservingLp` (`Mathlib/.../LpSpace/ContinuousCompMeasurePreserving.lean`) +
平行移動の `ContinuousVAdd` 作用 (`DomAct/Continuous.lean`) として既存、(3) Mathlib `convolution` への接続は
`convolution f g (lsmul ℝ ℝ) = convDensityAdd` で defeq、(5) Gauss 全積分=1 / 集中 (`v=0 → dirac`) も既存。
しかし (2) 連続版 Minkowski 積分不等式 (`‖∫ F y dν‖₁ ≤ ∫ ‖F y‖₁ dν`) と (4) 一般 L¹ `pX` に効く
approx-identity の **L¹ 収束**一般定理は `Found 0` で不在 (Mathlib の `convolution_tendsto_right` /
PeakFunction はいずれも pointwise / bump / 連続 `g` 限定)。総合判定: 層1 は (A) **Mathlib 部品の組上げで
genuine 達成可能** (真 moonshot ではない)。ただし「連続版 Minkowski の自作 (または三角不等式での迂回)」が
工数の支配項 (中核 80〜150 行)。撤退ライン (両ルート `volume` で塞がり真 moonshot) は **発動しない** —
平行移動連続性という最難部品が既存と判明したのが本調査の最重要 positive 発見。**既存率 ~70% / 自作必要 2 件
(連続 Minkowski or その迂回 + tail/集中の bridge) / 撤退ライン発動 no。**

---

## 主定理の最終形 (再掲)

```lean
-- EPIG2HeatFlowContinuity.lean:96 (verbatim, body = sorry + @residual(wall:approx-identity-L1))
theorem convDensityAdd_tendsto_L1_zero
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) :
    Tendsto (fun t : ℝ =>
      eLpNorm (convDensityAdd pX (gaussianPDFReal 0 t.toNNReal) - pX) 1 volume)
      (𝓝[Set.Ioi 0] 0) (𝓝 0)
```

定義 (verbatim 確認済):
- `convDensityAdd pX pY := fun z => ∫ x, pX x * pY (z - x) ∂volume` (`EPIConvDensity.lean:42`)
- `gaussianPDFReal 0 v` = 分散 `v` の Gauss 密度。`g_t := gaussianPDFReal 0 ⟨t,_⟩`。
- `convDensityAdd pX g_t = pX ∗ g_t` (畳み込み)。`t→0⁺` で `g_t` が近似単位元。

数学的標準証明 (どの部品が在るか):
```text
1. ∫ g_t = 1 (integral_gaussianPDFReal_eq_one) で
   (pX ∗ g_t − pX)(z) = ∫ (pX(z−y) − pX(z)) g_t(y) dy 表示              -- ✅ 部品在
2. Minkowski 積分不等式: ‖pX ∗ g_t − pX‖₁ ≤ ∫ ‖τ_y pX − pX‖₁ g_t(y) dy   -- ❌ 連続版不在 (or 迂回)
3. L¹ 平行移動連続性: y ↦ ‖τ_y pX − pX‖₁ → 0 (y→0), 有界 ≤ 2‖pX‖₁       -- ✅ compMeasurePreserving 既存
4. g_t の集中 (v→0 で dirac, gaussianReal_zero_var) で右辺 →0           -- ✅ 部品在 (DCT で組上げ)
```

---

## カテゴリ A — L¹ (Lᵖ) 平行移動連続性 (最重要・本壁の難易度を決める)

### ✅ 在る (`compMeasurePreserving` 経路) — **本調査の最重要 positive 発見**

Mathlib は「平行移動 = 測度保存連続写像」と「Lp 関数を測度保存写像と合成する作用が両引数連続」を持つ。
平行移動 `τ_y : ℝ → ℝ, x ↦ x − y` (または `x + y`) は volume を保存する `C(ℝ,ℝ)` であり、
`y ↦ Lp.compMeasurePreserving τ_y` の連続性がそのまま `y ↦ τ_y pX` の L¹ 連続性を与える。

| 概念 | Mathlib API | file:line | 状態 | 層1 での扱い |
|---|---|---|---|---|
| **Lp×測度保存写像 合成の両引数連続性** | `MeasureTheory.Lp.compMeasurePreserving_continuous` | `Mathlib/MeasureTheory/Function/LpSpace/ContinuousCompMeasurePreserving.lean:50` | ✅ | step 3 の核。`y ↦ τ_y pX` 連続の供給源 |
| **Tendsto 版 (filter)** | `Filter.Tendsto.compMeasurePreservingLp` | `…/ContinuousCompMeasurePreserving.lean:73` | ✅ | `y→0` で `τ_y pX → pX` in Lp に直接適用 |
| ContinuousWithinAt 版 | `ContinuousWithinAt.compMeasurePreservingLp` | `…/ContinuousCompMeasurePreserving.lean:87` | ✅ | `𝓝[Ioi 0] 0` 版が要る場合 |
| Continuous 版 | `Continuous.compMeasurePreservingLp` | `…/ContinuousCompMeasurePreserving.lean:102` | ✅ | 全域版 |
| **平行移動作用の連続性 (VAdd)** | `MeasureTheory.Lp.instContinuousVAddDomAddAct` | `Mathlib/MeasureTheory/Function/LpSpace/DomAct/Continuous.lean:53` (to_additive) | ✅ | `ℝᵈᵃᵃ` の Lp 上 `ContinuousVAdd`。最短経路だが DomAct 経由でやや迂遠 |
| 平行移動 = 測度保存 (右減算) | `MeasureTheory.measurePreserving_sub_right` | `Mathlib/MeasureTheory/Group/Measure.lean` | ✅ | `τ_y` が MeasurePreserving の witness |
| 平行移動 = 測度保存 (右加算) | `MeasureTheory.measurePreserving_add_right` | `Mathlib/MeasureTheory/Group/Measure.lean` | ✅ | 同上 (加算版) |

#### `compMeasurePreserving_continuous` verbatim signature + 型クラス前提

```lean
-- ContinuousCompMeasurePreserving.lean:50
-- 文脈 variable (lines 31-40):
--   variable {X Y : Type*}
--     [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
--     [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [R1Space Y]
--     {μ : Measure X} {ν : Measure Y} [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure ν]
--   variable (μ ν)
--   variable (E : Type*) [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
theorem compMeasurePreserving_continuous (hp : p ≠ ∞) :
    Continuous fun gf : Lp E p ν × {f : C(X, Y) // MeasurePreserving f μ ν} ↦
      compMeasurePreserving gf.2.1 gf.2.2 gf.1
```

```lean
-- ContinuousCompMeasurePreserving.lean:73
-- 文脈 variable (line 71): variable {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
theorem Filter.Tendsto.compMeasurePreservingLp {α : Type*} {l : Filter α}
    {f : α → Lp E p ν} {f₀ : Lp E p ν} {g : α → C(X, Y)} {g₀ : C(X, Y)}
    (hf : Tendsto f l (𝓝 f₀)) (hg : Tendsto g l (𝓝 g₀))
    (hgm : ∀ a, MeasurePreserving (g a) μ ν) (hgm₀ : MeasurePreserving g₀ μ ν) (hp : p ≠ ∞) :
    Tendsto (fun a ↦ Lp.compMeasurePreserving (g a) (hgm a) (f a)) l
      (𝓝 (Lp.compMeasurePreserving g₀ hgm₀ f₀))
```

> **型クラス前提の充足確認 (`X = Y = ℝ`, `μ = ν = volume`, `p = 1`)**:
> - `[TopologicalSpace ℝ] [MeasurableSpace ℝ] [BorelSpace ℝ] [R1Space ℝ]` — すべて既存 instance
>   (ℝ は Borel, `R1Space` = `T2Space` の弱版で metric space に自動)。
> - `[volume.InnerRegularCompactLTTop]` — ℝ の volume は sigma-finite なので
>   `MeasureTheory.Measure.InnerRegularCompactLTTop.instInnerRegularOfSigmaFinite`
>   (`Mathlib/MeasureTheory/Measure/Regular.lean`, loogle 確認済) が発火。**充足**。
> - `[IsLocallyFiniteMeasure volume]` — ℝ の volume は locally finite。既存 instance。**充足**。
> - `[Fact (1 ≤ (1:ℝ≥0∞))]` — `p = 1` で `Fact.mk le_rfl`。**充足**。`hp : (1:ℝ≥0∞) ≠ ∞` も自明。
> いずれも `volume` on ℝ で**追加仮説なしに満たされる**。`pX : ℝ → ℝ` は `Integrable` (= `MemLp 1`) で
> `Lp ℝ 1 volume` の元に持ち上がる。**層1 の最難部品「L¹ 平行移動連続性」は組上げ可能**。

> **落とし穴**: API は `Lp` 元 (`MemLp.toLp` 同値類) に対する連続性を主張する。生の関数 `pX : ℝ → ℝ` を
> `Lp` 元に lift し、`eLpNorm (τ_y pX − pX) 1 volume` を `Lp` 距離に翻訳する 1 段の plumbing が要る
> (`Lp.norm_def` / `Lp.edist_def` / `Lp.dist_def` 系)。`MemLp τ_y pX` は `measurePreserving_sub_right`
> から `MemLp.comp_measurePreserving` で従う。工数感 30〜50 行。

---

## カテゴリ B — Minkowski 積分不等式 (連続版)

### ❌ 不在 (連続版 `‖∫ F y dν‖_p ≤ ∫ ‖F y‖_p dν`) / ✅ 2 項三角版のみ

| 概念 | Mathlib API | file:line | 状態 | 層1 での扱い |
|---|---|---|---|---|
| **連続版 Minkowski (積分の Lᵖ ノルム ≤ ノルムの積分)** | — | — | ❌ **不在** (loogle: `eLpNorm (integral _ _), |- _ ≤ _` → 0 match; `eLpNorm_integral_le` → unknown identifier) | step 2 の本来形。**自作 or 迂回** |
| Minkowski (2 項三角, lintegral, ℝ≥0∞) | `MeasureTheory.lintegral_Lp_add_le` | `Mathlib/MeasureTheory/Integral/MeanInequalities.lean:380` | ✅ (但し 2 項和限定) | 連続積分版ではない。迂回には不十分 |
| Minkowski (2 項, p ≤ 1) | `MeasureTheory.lintegral_Lp_add_le_of_le_one` | `MeanInequalities.lean:407` | ✅ | 同上 |
| eLpNorm 三角不等式 (Lp 内) | `MeasureTheory.eLpNorm_add_le` 系 | `Mathlib/MeasureTheory/Function/LpSeminorm/*` | ✅ | Lp 元の三角。迂回経路で使う |

```lean
-- MeanInequalities.lean:380 — Minkowski は「2 項和」版のみ。連続積分版 (∫ F y dν) は無い。
theorem lintegral_Lp_add_le {p : ℝ} {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hp1 : 1 ≤ p) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p)
```

> **連続版 Minkowski は不在**。`loogle "MeasureTheory.eLpNorm (MeasureTheory.integral _ _) _ _"` /
> `"…, |- _ ≤ _"` ともに `Found 0` / `0 match`。`eLpNorm_integral_le` も unknown identifier。Mathlib の
> "Minkowski for functions" (`lintegral_Lp_add_le`) は **2 項和の三角不等式**であって、
> パラメタ積分 `∫ y, F y · ∂ν` の Lᵖ ノルムを内側に入れる連続版ではない。
>
> **迂回 (recommended)**: `p = 1` (L¹) なら連続版 Minkowski は **Tonelli/Fubini で初等的**:
> `‖∫ y, F(·,y) dν(y)‖₁ = ∫_z |∫_y F(z,y) dν| dz ≤ ∫_z ∫_y |F(z,y)| dν dz = ∫_y ‖F(·,y)‖₁ dν`。
> `∫_z |∫_y …|` の三角は `abs_integral_le_integral_abs` (`norm_integral_le_integral_norm`)、順序交換は
> `MeasureTheory.lintegral_lintegral` / `integral_integral_swap` (Tonelli, `[SigmaFinite]` 要、volume×g_t は
> 充足)。つまり **L¹ に限れば連続 Minkowski は Fubini + 三角で 40〜70 行で自作可能**。一般 p の連続 Minkowski を
> 待つ必要はない (本件は p=1 固定)。

---

## カテゴリ C — Mathlib `MeasureTheory.convolution` との接続 + Young

### ✅ defeq 接続あり / ❌ Young (L¹ 版) 不在

| 概念 | Mathlib API | file:line | 状態 | 層1 での扱い |
|---|---|---|---|---|
| Mathlib convolution 定義 | `MeasureTheory.convolution f g L μ := fun x => ∫ t, L (f t) (g (x - t)) ∂μ` | `Mathlib/Analysis/Convolution.lean:401` | ✅ | `L = lsmul ℝ ℝ` で `convDensityAdd` に **defeq** |
| **Young 不等式 (`‖f ⋆ g‖_p ≤ ‖f‖₁ ‖g‖_p`)** | — | — | ❌ **不在** (loogle: `convolution, eLpNorm` → `Found 0`) | あれば L¹ 評価に直効。無いので別経路 |
| 畳み込み pointwise 距離評価 (近似単位元 step) | `MeasureTheory.dist_convolution_le` | `Mathlib/Analysis/Convolution.lean:768` | ⚠️ pointwise + **compact support** 前提 | Gauss は full support → **不適合** |
| `convDensityAdd` 定義 | `InformationTheory.Shannon.EPIConvDensity.convDensityAdd` | `EPIConvDensity.lean:42` | ✅ | `f_t` 本体 |

```lean
-- Analysis/Convolution.lean:401 — 一般 convolution 定義
noncomputable def convolution [Sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : Measure G := by volume_tac) : G → F := fun x =>
  ∫ t, L (f t) (g (x - t)) ∂μ
-- L = lsmul ℝ ℝ で  (pX ⋆[lsmul ℝ ℝ] pY) z = ∫ t, pX t • pY (z-t) = ∫ t, pX t * pY (z-t)
--                  = convDensityAdd pX pY z  (defeq, smul=mul on ℝ)
```

> **接続は可能だが Young 不在で旨味が薄い**。`convDensityAdd pX pY = pX ⋆[lsmul ℝ ℝ] pY` は smul=mul on ℝ で
> defeq。だが **Young 不等式 (`eLpNorm_convolution_le`) が Mathlib に不在** (`loogle "convolution, eLpNorm"
> = Found 0`)。Mathlib の畳み込み補題で L≤ 系は `dist_convolution_le` / `dist_convolution_le'` /
> `convolution_mono_right` のみ (`loogle "convolution, |- _ ≤ _"` で 7 件中 5 件、すべて pointwise/mono)。
> `dist_convolution_le` は (a) pointwise 距離評価、(b) `support f ⊆ ball 0 R` (**compact support**) 前提で、
> full-support の Gauss 核には乗らない。**結論: Mathlib convolution へ乗せても Young が無いので L¹ 評価は
> 自力 (カテゴリ B の Fubini 迂回) に戻る。convolution への乗せ替えは必須ではない** — `convDensityAdd` の
> Bochner-∫ 形のまま Fubini を回す方が直接的 (定義を Mathlib 結論形に合わせる原則とも整合)。

---

## カテゴリ D — 近似単位元 / mollifier の収束一般定理

### ⚠️ 部分的 (pointwise / bump / 連続 g 限定、**L¹ 版は不在**)

| 概念 | Mathlib API | file:line | 状態 | 層1 での扱い |
|---|---|---|---|---|
| bump 畳み込み収束 (pointwise/uniform) | `MeasureTheory.convolution_tendsto_right` | `Mathlib/Analysis/Convolution.lean:787` | ⚠️ **support → 0 smallSets 前提** | Gauss は full support → **不適合** |
| ContDiffBump 近似 (連続 g) | `ContDiffBump.convolution_tendsto_right` | `Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean` | ⚠️ bump 限定 | gaussianPDF は ContDiffBump でない |
| ContDiffBump 近似 (局所可積分 g, a.e.) | `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable` | `…/BumpFunction/Convolution.lean` | ⚠️ bump 限定 + a.e. pointwise | L¹ 収束ではない |
| **peak/approx-identity 積分収束 (renormalize)** | `MeasureTheory.tendsto_integral_comp_smul_smul_of_integrable` | `Mathlib/MeasureTheory/Integral/PeakFunction.lean:394` | ⚠️ **pointwise (value) 収束 + ContinuousAt g** | `(φ_c ⋆ g)(0) → g(0)`、L¹ ではない |
| peak 積分収束 (一般 peak) | `MeasureTheory.tendsto_integral_peak_smul_of_integrable_of_tendsto` | `PeakFunction.lean:222` | ⚠️ pointwise + `Tendsto g (𝓝 x₀) (𝓝 a)` | 同上、点での値収束 |
| **一般 L¹ `pX` の `f_t → pX` in L¹ (`t→0⁺`)** | — | — | ❌ **不在 (真壁、but 組上げ可)** | 層1 の結論。組上げ対象 |

```lean
-- Convolution.lean:787 — ★ support (φ n) → 0 smallSets 前提 (compact-shrinking)。Gauss 不適合。
theorem convolution_tendsto_right {ι} {g : ι → G → E'} {l : Filter ι} {x₀ : G} {z₀ : E'}
    {φ : ι → G → ℝ} {k : ι → G} (hnφ : ∀ᶠ i in l, ∀ x, 0 ≤ φ i x)
    (hiφ : ∀ᶠ i in l, ∫ x, φ i x ∂μ = 1)
    (hφ : Tendsto (fun n => support (φ n)) l (𝓝 0).smallSets)   -- ★ support → 0 (Gauss 不可)
    (hmg : ∀ᶠ i in l, AEStronglyMeasurable (g i) μ) (hcg : Tendsto (uncurry g) (l ×ˢ 𝓝 x₀) (𝓝 z₀))
    (hk : Tendsto k l (𝓝 x₀)) :
    Tendsto (fun i : ι => (φ i ⋆[lsmul ℝ ℝ, μ] g i : G → E') (k i)) l (𝓝 z₀)

-- PeakFunction.lean:394 — ★ pointwise (value at 0) 収束 + ContinuousAt g 0。L¹ ノルム収束ではない。
theorem tendsto_integral_comp_smul_smul_of_integrable
    {φ : F → ℝ} (hφ : ∀ x, 0 ≤ φ x) (h'φ : ∫ x, φ x ∂μ = 1)
    (h : Tendsto (fun x ↦ ‖x‖ ^ finrank ℝ F * φ x) (cobounded F) (𝓝 0))
    {g : F → E} (hg : Integrable g μ) (h'g : ContinuousAt g 0) :    -- ★ g の連続性要求
    Tendsto (fun (c : ℝ) ↦ ∫ x, (c ^ (finrank ℝ F) * φ (c • x)) • g x ∂μ) atTop (𝓝 (g 0))
```

> **L¹ 版 approx-identity は Mathlib に不在**。既存の approx-identity 系は全て:
> - **pointwise / 値での収束** (`convolution_tendsto_right`, PeakFunction 系) であって、
>   L¹ ノルム `‖f_t − pX‖₁ → 0` を直接与えない。
> - **連続 `g`** (`ContinuousAt g`) または **bump/compact-support 核**を要求し、
>   一般 L¹ `pX` (積分可能な特異点を持ちうる) + full-support Gauss 核に乗らない。
> `PeakFunction.lean` の `tendsto_integral_comp_smul_smul_of_integrable` は renormalize `c^d φ(c•x)`
> (Gauss の `t→0⁺` 再スケールに形は合う) を扱い L¹ 入力 `g` も許すが、出力は `g(0)` への**値収束**で
> `ContinuousAt g 0` を要求 — **L¹ 収束ではない別の極限**。よって本壁の核 (一般 L¹ の L¹ 収束) は
> Mathlib 直接 lemma としては不在。**ただしカテゴリ A (平行移動連続) + B 迂回 (Fubini Minkowski) +
> E (Gauss 集中) の組上げで genuine に到達可能** (= moonshot ではない)。

---

## カテゴリ E — Gauss 核の全積分 / 集中性

### ✅ 既存

| 概念 | Mathlib API | file:line | 状態 | 層1 での扱い |
|---|---|---|---|---|
| Gauss 全積分 = 1 (Bochner ∫) | `ProbabilityTheory.integral_gaussianPDFReal_eq_one` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:121` | ✅ | step 1 (差分表示) の核。`(hv : v ≠ 0)` 要 |
| Gauss 全積分 = 1 (lintegral) | `ProbabilityTheory.lintegral_gaussianPDFReal_eq_one` | `Gaussian/Real.lean:104` | ✅ | ℝ≥0∞ 版 |
| Gauss 非負 | `ProbabilityTheory.gaussianPDFReal_nonneg` | `Gaussian/Real.lean` | ✅ | 既に in-tree で多用 |
| **分散 0 → Dirac (集中の極形)** | `ProbabilityTheory.gaussianReal_zero_var` | `Gaussian/Real.lean:207` | ✅ | `gaussianReal μ 0 = Measure.dirac μ`。`v→0` 集中の端点 |
| Gauss 二次モーメント = s | `InformationTheory.Shannon.integral_sq_mul_gaussianPDFReal` | `InformationTheory/Shannon/FisherConvBound.lean:56` | ✅ | tail/集中評価 (二次モーメント駆動) |
| weak/L¹ 集中 (`v→0` で `g_v → δ`) | — | — | ❌ **不在** (loogle: `Tendsto, gaussianReal` → Found 0) | 集中は DCT/二次モーメントで組上げ |

```lean
-- Gaussian/Real.lean:121
lemma integral_gaussianPDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, gaussianPDFReal μ v x = 1
-- Gaussian/Real.lean:207 — 分散 0 の端点 (集中の極限形)
lemma gaussianReal_zero_var (μ : ℝ) : gaussianReal μ 0 = Measure.dirac μ := if_pos rfl
```

> **全積分=1 と分散0=Dirac は既存**。step 1 の差分表示 `(f_t − pX)(z) = ∫ (pX(z−y)−pX(z)) g_t(y) dy` は
> `integral_gaussianPDFReal_eq_one` (∫ g_t = 1) から従う。集中性は「`g_v → δ` の weak/L¹ 収束一般補題」が
> 不在 (Found 0) だが、**本件では不要**: step 4 の `∫ ‖τ_y pX − pX‖₁ g_t(y) dy → 0` は、被積分関数
> `‖τ_y pX − pX‖₁` が y→0 で →0 (カテゴリ A)・有界 ≤ 2‖pX‖₁ で、`g_t` が確率密度 (∫=1) かつ二次モーメント
> →0 で 0 周辺に集中、という **DCT (有界収束) で組上げ**。集中の一般定理を待つ必要はない。

---

## カテゴリ F — 連続関数の L¹ 稠密性 (代替経路の足場)

### ✅ 既存 (compMeasurePreserving 経路が在るので主には不要、但し代替経路に有用)

| 概念 | Mathlib API | file:line | 状態 | 層1 での扱い |
|---|---|---|---|---|
| 有界連続関数で Lᵖ 近似 (eLpNorm) | `MeasureTheory.MemLp.exists_boundedContinuous_eLpNorm_sub_le` | `Mathlib/MeasureTheory/Function/ContinuousMapDense.lean:235` | ✅ | `[μ.WeaklyRegular]` 要 (volume 充足) |
| 可積分関数で有界連続近似 (lintegral 形) | `MeasureTheory.Integrable.exists_boundedContinuous_lintegral_sub_le` | `ContinuousMapDense.lean:303` | ✅ | L¹ (p=1) 特化。代替経路の核 |
| コンパクト台連続で Lᵖ 近似 | `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le` | `ContinuousMapDense.lean:137` | ✅ | locally compact (ℝ 充足) |
| 連続で近似 (閉集合上) | `MeasureTheory.exists_continuous_eLpNorm_sub_le_of_closed` | `ContinuousMapDense.lean:81` | ✅ (`[μ.OuterRegular]`) | 下層 |

```lean
-- ContinuousMapDense.lean:235 — 有界連続関数による Lᵖ 近似 (★ [μ.WeaklyRegular] 要)
theorem MemLp.exists_boundedContinuous_eLpNorm_sub_le [μ.WeaklyRegular] (hp : p ≠ ∞) {f : α → E}
    (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : α →ᵇ E, eLpNorm (f - (g : α → E)) p μ ≤ ε ∧ MemLp g p μ
-- ContinuousMapDense.lean:303 — L¹ 特化 (∫⁻ ‖f-g‖ 形)
theorem Integrable.exists_boundedContinuous_lintegral_sub_le [μ.WeaklyRegular] {f : α → E}
    (hf : Integrable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : α →ᵇ E, ∫⁻ x, ‖f x - g x‖ₑ ∂μ ≤ ε ∧ Integrable g μ
```

> **代替経路 (3 段) の足場として存在**: もしカテゴリ A の `compMeasurePreserving` 翻訳が plumbing で詰まれば、
> 古典的 3 段経路「(i) pX を有界連続 g で L¹ 近似 (`exists_boundedContinuous_eLpNorm_sub_le`)、
> (ii) g は平行移動連続 (連続関数の一様連続 + DCT)、(iii) 三角不等式」で代替できる。`[volume.WeaklyRegular]`
> は ℝ で `InnerRegularCompactLTTop.instWeaklyRegularOfBorelSpaceOfR1SpaceOfIsFiniteMeasure` 系 + sigma-finite
> で充足。**ただし A が直接 L¹ 平行移動連続を与えるので、A 優先・F は保険。**

---

## カテゴリ G — その他関連 (三角不等式 / 積分の linearity)

### ✅ 既存

| 概念 | Mathlib API | file:line | 状態 |
|---|---|---|---|
| `MemLp.tendsto_Lp` 系 (Lp 収束) | (層2 在庫参照: `tendsto_Lp_of_tendsto_ae` 等) | `Mathlib/MeasureTheory/Function/UnifTight.lean:329` | ✅ (層2 で確認済) |
| eLpNorm 三角 (`eLpNorm (f+g) ≤ …`) | `MeasureTheory.eLpNorm_add_le` | `Mathlib/MeasureTheory/Function/LpSeminorm/TriangleInequality.lean` | ✅ |
| ノルム積分の三角 (`‖∫ f‖ ≤ ∫ ‖f‖`) | `MeasureTheory.norm_integral_le_integral_norm` | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` | ✅ | Fubini 迂回 (B) の三角 step |
| 順序交換 (Tonelli/Fubini) | `MeasureTheory.lintegral_lintegral` / `integral_integral_swap` | `Mathlib/MeasureTheory/Integral/Prod.lean` (`[SigmaFinite]`) | ✅ | B の迂回核 |
| `MemLp.comp_measurePreserving` | `MeasureTheory.MemLp.comp_measurePreserving` | `Mathlib/MeasureTheory/Function/LpSeminorm/*` | ✅ | `τ_y pX ∈ Lp` の witness (A の plumbing) |

---

## 主要前提条件ボックス (前提事故が起きやすい lemma)

- **`compMeasurePreserving_continuous` (ContinuousCompMeasurePreserving.lean:50)** — 要求型クラス:
  `[BorelSpace X] [R1Space X] [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure ν] [Fact (1 ≤ p)]`
  + 引数 `(hp : p ≠ ∞)`。**`InnerRegularCompactLTTop` が事故の主候補** — ℝ の volume は sigma-finite から
  `instInnerRegularOfSigmaFinite` で自動発火するが、別測度に一般化する際は明示供給が要る。本件 (volume) は OK。
  作用対象は **`Lp` 元 (同値類)** であって生関数でない → `MemLp.toLp` lift + `Lp.dist_def` 翻訳の plumbing 必須。
- **連続版 Minkowski (不在)** — `‖∫ F y dν‖₁ ≤ ∫ ‖F y‖₁ dν` は Mathlib に無い (`Found 0`)。p=1 では
  `norm_integral_le_integral_norm` + `integral_integral_swap` (Tonelli, `[SigmaFinite]` 要、volume×g_t 充足) で
  **自作必須**。一般 p の連続 Minkowski を待つと詰む — p=1 固定で Fubini 迂回が正解。
- **`integral_gaussianPDFReal_eq_one` (Gaussian/Real.lean:121)** — `(hv : v ≠ 0)` 要。`t→0⁺` の経路では
  `t > 0` ⇒ `t.toNNReal ≠ 0` だが、`𝓝[Ioi 0] 0` filter 上で `v = t.toNNReal ≠ 0` を eventually 確保する
  1 段が要る (`self_mem_nhdsWithin` から `t > 0` → `toNNReal ≠ 0`)。
- **`convolution_tendsto_right` / PeakFunction 系 (誤用注意)** — いずれも **pointwise/値収束 + (support→0 or
  ContinuousAt g)**。本壁の **L¹ ノルム収束**には乗らない。「approx-identity の lemma があった」と早合点して
  これらに L¹ 収束を期待すると型 mismatch で詰まる。区別を明示。

---

## 自作が必要な要素 (優先度順)

1. **【中核・支配項】連続版 Minkowski (L¹) の自作 or Fubini 迂回** — `‖∫ y, F(·,y) g_t(y) dy‖₁ ≤
   ∫ y, ‖τ_y pX − pX‖₁ g_t(y) dy`。p=1 なら `norm_integral_le_integral_norm` + `integral_integral_swap`
   (Tonelli) で初等的。工数感 **40〜70 行**。落とし穴: 順序交換の `[SigmaFinite]` / 可積分性 side-goal
   (Fubini 適用条件 `Integrable (uncurry …)`)。
2. **【中核】平行移動連続 → eLpNorm 翻訳の plumbing** — カテゴリ A の `compMeasurePreserving_continuous` /
   `Tendsto.compMeasurePreservingLp` は `Lp` 元の連続性。これを `y ↦ eLpNorm (τ_y pX − pX) 1 volume → 0`
   (生関数) に翻訳 + `MemLp τ_y pX` (= `MemLp.comp_measurePreserving`) + 有界性 `≤ 2‖pX‖₁`。工数感 **30〜50 行**。
3. **【中】集中の DCT 組上げ** — `∫ y, ‖τ_y pX − pX‖₁ g_t(y) dy → 0` を、被積分 →0 (y→0) + 有界 + g_t
   確率密度・二次モーメント→0 で `tendsto_integral_filter_of_dominated_convergence` (層2 在庫済) or 直接
   評価。工数感 **30〜60 行**。落とし穴: g_t の集中を二次モーメント (Chebyshev) で定量化する評価。
4. **【小】filter 整形** — `𝓝[Ioi 0] 0` 上で `t.toNNReal ≠ 0` の eventually 確保 + `gaussianPDFReal 0 t.toNNReal`
   の各前提供給。工数感 **10〜20 行**。

合計工数感: **110〜200 行** (連続 Minkowski 迂回 + 平行移動翻訳が支配)。**層2 在庫の「層1 = 80〜150 行」見積もりと整合**、
ただし「平行移動連続性が既存と判明」した分、自作量は当初予想の下振れ側 (translation continuity を自作しないで済む)。

---

## Mathlib 壁の列挙 (`@residual(wall:...)` 対象)

| 壁 | 内容 | loogle/rg 確認 | 集約推奨 |
|---|---|---|---|
| `wall:approx-identity-L1` (既存・本壁) | 一般 L¹ `pX` の `convDensityAdd pX g_t → pX` in L¹ as `t→0⁺` | `loogle "convolution, eLpNorm" → Found 0`; `"convolution, Tendsto, eLpNorm" → Found 0`; `convolution_tendsto_right`/PeakFunction は pointwise/bump/連続g 限定 | 既存 shared sorry `convDensityAdd_tendsto_L1_zero` + 3 Vitali witness に集約済 |
| 連続版 Minkowski (L¹) | `‖∫ F y dν‖₁ ≤ ∫ ‖F y‖₁ dν` | `loogle "eLpNorm (integral _ _), |- _ ≤ _" → 0 match`; `eLpNorm_integral_le → unknown` | **壁ではない (選択)**: p=1 で Fubini 自作可能。`@residual` 不要、自作で genuine 化 |

> **集約方針**: 本壁 `wall:approx-identity-L1` は**真の Mathlib 不在だが組上げ可能 (hard でなく big)**。
> 核命題 (一般 L¹ approx-identity の L¹ 収束) の **直接 lemma** は Mathlib に無い (Found 0) が、構成部品
> (平行移動連続 ✅ / Gauss 集中 ✅ / Fubini ✅) は全て在る。よって **「Mathlib PR 不可避の hard wall」ではなく
> 「組上げ工数 110〜200 行の big task」**。これは `docs/audit/audit-tags.md`「Mathlib 壁の 4 分類」で言えば
> **big (選択) 寄り** であり、honesty 上は sorry + `@residual(wall:approx-identity-L1)` で正規撤退中の状態が、
> 1 セッションの組上げで genuine closure に到達できる見込み。**連続 Minkowski を別 wall に切り出す必要はない**
> (p=1 で Fubini により genuine、`@residual` 不要)。

---

## 撤退ラインへの距離

層2 在庫 (`epi-g2-layer2-semicontinuity-inventory.md`) の新規撤退ライン:

> 層1 L¹ 収束を 2 週間で書けない場合 → 層1 を独立 shared sorry 補題 `wall:approx-identity-L1` として切り出し、
> 層2 を genuine に閉じる。仮説束化禁止。

**判定: 既に切り出し済 (層1 = `convDensityAdd_tendsto_L1_zero` の sorry 1 本)。本調査はその先「組上げで
genuine closure 可能か」を問うもので、撤退ライン (真 moonshot 化) は発動しない。**

- **平行移動連続性 (最難部品) が `compMeasurePreserving_continuous` として既存** — 層2 在庫が「素材は散在するが
  組み上げは未整備」と書いた部分が、実は **Mathlib に翻訳済の primitive (`ContinuousCompMeasurePreserving` /
  `DomAct/Continuous`) として存在**することが本調査の最重要 positive 発見。自作量が当初見積もりより下振れ。
- **塞がりは「連続 Minkowski」のみ、しかも p=1 で Fubini 自作可能** — Young 不在・連続 Minkowski 不在だが、
  L¹ に限れば `norm_integral_le_integral_norm` + `integral_integral_swap` で初等的に迂回。**真 moonshot
  (100 行超の新数学 / Mathlib PR 不可避) ではない。**
- **撤退ライン触れない**: 3 大部品のうち 2 つ (平行移動連続・Gauss 集中) が既存、1 つ (連続 Minkowski) が
  自作可能な選択 (big)。両ルート塞がりの真 moonshot 条件には**該当しない**。

**新規撤退ライン提案 (縮退口)**: 連続 Minkowski の Fubini 迂回が `Integrable (uncurry …)` の side-goal で
2 週間詰まる場合 → カテゴリ F の **古典 3 段経路** (有界連続近似 → 連続関数の平行移動連続 → 三角) に切替。
これは `exists_boundedContinuous_eLpNorm_sub_le` (✅) で連続近似を取り、連続関数なら平行移動連続が一様連続から
直接出るため Fubini を回避できる。撤退口は依然 sorry + `@residual(wall:approx-identity-L1)` を**縮小しつつ
保持** (仮説束化禁止 — L¹ 収束を `*Hypothesis` predicate に bundle するのは load-bearing で禁止)。

---

## 着手 skeleton

```lean
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving  -- 平行移動連続 (核)
import Mathlib.MeasureTheory.Integral.Prod                                      -- integral_integral_swap (Fubini)
import Mathlib.MeasureTheory.Integral.Bochner.Basic                            -- norm_integral_le_integral_norm
import Mathlib.MeasureTheory.Group.Measure                                     -- measurePreserving_sub_right
import Mathlib.Probability.Distributions.Gaussian.Real                         -- integral_gaussianPDFReal_eq_one
import InformationTheory.Shannon.EPIConvDensity                                -- convDensityAdd

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open InformationTheory.Shannon.EPIConvDensity
open scoped ENNReal NNReal Topology Convolution

/-- **層1 補助 (genuine 目標)**: L¹ 平行移動連続性。
`y ↦ eLpNorm (fun x => pX (x - y) - pX x) 1 volume` は `y → 0` で `→ 0`。
`Lp.compMeasurePreserving_continuous` (ContinuousCompMeasurePreserving.lean:50) +
`measurePreserving_sub_right` の翻訳で genuine 化可能 (自作要素 2)。 -/
theorem translation_continuous_L1
    {pX : ℝ → ℝ} (hpX_int : Integrable pX volume) :
    Tendsto (fun y : ℝ => eLpNorm (fun x => pX (x - y) - pX x) 1 volume) (𝓝 0) (𝓝 0) := by
  sorry  -- compMeasurePreserving 翻訳 plumbing (自作要素 2、~30-50 行)

/-- **層1 補助 (genuine 目標)**: 連続版 Minkowski (L¹, Fubini 迂回)。
`‖∫ y, F(·,y) g_t(y) dy‖₁ ≤ ∫ y, ‖F(·,y)‖₁ g_t(y) dy`。
`norm_integral_le_integral_norm` + `integral_integral_swap` で初等 (自作要素 1)。 -/
theorem eLpNorm_integral_smul_le_L1
    {F : ℝ → ℝ → ℝ} {gt : ℝ → ℝ} (hgt_nn : ∀ y, 0 ≤ gt y) :
    True := by  -- 実装時は本来の Tendsto/≤ 形に置換 (:True slot は honesty defect、ここは方向提示のみ)
  sorry

/-- **層1 核命題 (壁、組上げで genuine 化目標)**: 近似単位元 L¹ 収束。
平行移動連続 (translation_continuous_L1) + 連続 Minkowski (eLpNorm_integral_smul_le_L1) +
Gauss 集中 (integral_gaussianPDFReal_eq_one + 二次モーメント DCT) の組上げ。
@residual(wall:approx-identity-L1) -/
theorem convDensityAdd_tendsto_L1_zero
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) :
    Tendsto (fun t : ℝ =>
      eLpNorm (convDensityAdd pX (gaussianPDFReal 0 t.toNNReal) - pX) 1 volume)
      (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
  sorry  -- 3 部品の組上げ (差分表示 → Minkowski → 集中 DCT)

end InformationTheory.Shannon
```

> skeleton は方向性提示のみ (planner/implementer の責務)。`eLpNorm_integral_smul_le_L1` の `True` placeholder は
> 本 inventory がコードでないため形の提示に留める (`:True` slot は実コードでは honesty defect、実装時は本来の
> `Tendsto`/`≤` 形に置換)。
