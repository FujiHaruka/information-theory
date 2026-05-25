# `IsDeBruijnTailHyp` re-introduction — Mathlib API inventory

> **Scope**: 旧 `IsDeBruijnTailHyp X Z P` (2026-05-25 Wave 3 third batch で independent
> closure audit が `defect(epi-debruijn-tail-vacuous-and-empty)` で retract) を **`h_inf : EReal`
> (or `ℝ≥0∞`) + `Z_law : P.map Z = gaussianReal 0 1` 同梱** 形で再導入する設計のために、
> 必要となる Mathlib API の在庫を構造化テーブルで列挙する。
>
> **Parent**: [`epi-debruijn-integration-plan.md`](./epi-debruijn-integration-plan.md) Phase C-5
> (撤退ライン L-DB-C-β、`EReal` lift + `Z_law` 追加 refactor 待ち)。
> **Sister plan (drafted in parallel)**: `epi-debruijn-tail-reintroduction-plan.md`
> (本 inventory と同期で起草中)。
> **Retraction comment SoT**: `Common2026/Shannon/EPIL3Integration.lean:595-613` (コメント形)。

## 一行サマリ

**EReal API は豊富、ENNReal も同程度。Gaussian sub-entropy 発散 `(1/2) log (2π e (v+T)) → +∞`
の表現には `EReal` 経路 (`Real.toEReal ∘ h_path → 𝓝 ⊤`) を採用すべき** — `differentialEntropy : Measure ℝ → ℝ`
(実数値) であり、`Tendsto (Real.toEReal ∘ ·) atTop (𝓝 ⊤) ↔ Tendsto · atTop atTop`
(`EReal.tendsto_coe_nhds_top_iff` `:169`) が **1 行 iff bridge** を提供する。
`ℝ≥0∞` は `Real.toNNReal` を介した coerce が `negMulLog` の符号と相性が悪く、`Tendsto (ofReal h_path) → 𝓝 ⊤`
は `Tendsto.atTop_of_nonneg` を別途要求する。Gaussian discharge `isDeBruijnTailHyp_of_gaussian`
は **PRESENT-bridgeable**: `differentialEntropy_gaussianReal_heat_path` (本 repo) +
`Real.tendsto_log_atTop` + `Tendsto.const_mul_atTop` + `tendsto_atTop_add_const_right`
の 4 段 compose で ~10-15 行。撤退ライン **L-DB-C-β** には触れるが Gaussian 限定 closure 路は
**現状の Mathlib で genuine に書ける** ため新規撤退ライン発動なし。

---

## A. EReal の `Tendsto atTop (𝓝 _)` 系

### A-1. EReal `nhds ⊤` characterization (核 API)

| 名前 | file:line | 完全 signature (型クラス verbatim) | 結論形 (verbatim) | 状態 |
|---|---|---|---|---|
| `EReal.nhds_top` | `Mathlib/Topology/Instances/EReal/Lemmas.lean:103` | `theorem nhds_top : 𝓝 (⊤ : EReal) = ⨅ (a) (_ : a ≠ ⊤), 𝓟 (Ioi a)` | `𝓝 (⊤ : EReal) = ⨅ (a) (_ : a ≠ ⊤), 𝓟 (Ioi a)` | PRESENT |
| `EReal.nhds_top_basis` | `Mathlib/Topology/Instances/EReal/Lemmas.lean:106` | `nonrec theorem nhds_top_basis : (𝓝 (⊤ : EReal)).HasBasis (fun _ : ℝ ↦ True) (Ioi ·)` | `(𝓝 (⊤ : EReal)).HasBasis (fun _ : ℝ ↦ True) (Ioi ·)` | PRESENT |
| `EReal.nhds_top'` | `Mathlib/Topology/Instances/EReal/Lemmas.lean:112` | `theorem nhds_top' : 𝓝 (⊤ : EReal) = ⨅ a : ℝ, 𝓟 (Ioi ↑a)` | `𝓝 (⊤ : EReal) = ⨅ a : ℝ, 𝓟 (Ioi ↑a)` | PRESENT |
| `EReal.mem_nhds_top_iff` | `Mathlib/Topology/Instances/EReal/Lemmas.lean:114` | `theorem mem_nhds_top_iff {s : Set EReal} : s ∈ 𝓝 (⊤ : EReal) ↔ ∃ y : ℝ, Ioi (y : EReal) ⊆ s` | `s ∈ 𝓝 (⊤ : EReal) ↔ ∃ y : ℝ, Ioi (y : EReal) ⊆ s` | PRESENT |
| `EReal.tendsto_nhds_top_iff_real` | `Mathlib/Topology/Instances/EReal/Lemmas.lean:117` | `theorem tendsto_nhds_top_iff_real {α : Type*} {m : α → EReal} {f : Filter α} : Tendsto m f (𝓝 ⊤) ↔ ∀ x : ℝ, ∀ᶠ a in f, ↑x < m a` | `Tendsto m f (𝓝 ⊤) ↔ ∀ x : ℝ, ∀ᶠ a in f, ↑x < m a` | PRESENT |

### A-2. EReal coercion ↔ Tendsto lift (本 inventory の **central bridge**)

| 名前 | file:line | 完全 signature (型クラス verbatim) | 結論形 (verbatim) | 状態 |
|---|---|---|---|---|
| **`EReal.tendsto_coe_nhds_top_iff`** | `Mathlib/Topology/Instances/EReal/Lemmas.lean:169` | `omit [TopologicalSpace α] in @[simp] lemma tendsto_coe_nhds_top_iff {f : α → ℝ} {l : Filter α} : Tendsto (fun x ↦ Real.toEReal (f x)) l (𝓝 ⊤) ↔ Tendsto f l atTop` | `Tendsto (fun x ↦ Real.toEReal (f x)) l (𝓝 ⊤) ↔ Tendsto f l atTop` | PRESENT |
| **`EReal.tendsto_coe_atTop`** | `Mathlib/Topology/Instances/EReal/Lemmas.lean:173` | `lemma tendsto_coe_atTop : Tendsto Real.toEReal atTop (𝓝 ⊤)` | `Tendsto Real.toEReal atTop (𝓝 ⊤)` | PRESENT |
| `EReal.tendsto_coe_nhds_bot_iff` | `Mathlib/Topology/Instances/EReal/Lemmas.lean:178` | `omit [TopologicalSpace α] in @[simp] lemma tendsto_coe_nhds_bot_iff {f : α → ℝ} {l : Filter α} : Tendsto (fun x ↦ Real.toEReal (f x)) l (𝓝 ⊥) ↔ Tendsto f l atBot` | `Tendsto (fun x ↦ Real.toEReal (f x)) l (𝓝 ⊥) ↔ Tendsto f l atBot` | PRESENT |
| `EReal.tendsto_toReal` | `Mathlib/Topology/Instances/EReal/Lemmas.lean:65` | `theorem tendsto_toReal {a : EReal} (ha : a ≠ ⊤) (h'a : a ≠ ⊥) : Tendsto EReal.toReal (𝓝 a) (𝓝 a.toReal)` | `Tendsto EReal.toReal (𝓝 a) (𝓝 a.toReal)` | PRESENT |
| `EReal.tendsto_toReal_atTop` | `Mathlib/Topology/Instances/EReal/Lemmas.lean:186` | `lemma tendsto_toReal_atTop : Tendsto EReal.toReal (𝓝[≠] ⊤) atTop` | `Tendsto EReal.toReal (𝓝[≠] ⊤) atTop` | PRESENT |

### A-3. EReal core coercion / decision lemmas

| 名前 | file:line | 完全 signature (型クラス verbatim) | 結論形 (verbatim) | 状態 |
|---|---|---|---|---|
| `Real.toEReal` (定義) | `Mathlib/Data/EReal/Basic.lean:41` | `@[coe] def Real.toEReal : ℝ → EReal := WithBot.some ∘ WithTop.some` | `ℝ → EReal` | PRESENT |
| `EReal.toReal_coe` | `Mathlib/Data/EReal/Basic.lean:241` | `theorem toReal_coe (x : ℝ) : toReal (x : EReal) = x` | `toReal (x : EReal) = x` | PRESENT |
| `EReal.coe_strictMono` | `Mathlib/Data/EReal/Basic.lean:47` | `theorem coe_strictMono : StrictMono Real.toEReal` | `StrictMono Real.toEReal` | PRESENT |
| `EReal.coe_lt_top` | `Mathlib/Data/EReal/Basic.lean` 付近 | `theorem coe_lt_top (x : ℝ) : (x : EReal) < ⊤` | `(x : EReal) < ⊤` | PRESENT |
| `EReal.coe_toReal` | `Mathlib/Data/EReal/Basic.lean:399` | `theorem coe_toReal {x : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) : (x.toReal : EReal) = x` | `(x.toReal : EReal) = x` | PRESENT |

---

## B. `ℝ≥0∞` の `Tendsto atTop (𝓝 _)` 系

### B-1. ENNReal `nhds ⊤` characterization

| 名前 | file:line | 完全 signature (型クラス verbatim) | 結論形 (verbatim) | 状態 |
|---|---|---|---|---|
| `ENNReal.tendsto_nhds_top_iff_nat` | `Mathlib/Topology/Instances/ENNReal/Lemmas.lean` (近接 `:140`) | `theorem tendsto_nhds_top_iff_nat {m : α → ℝ≥0∞} {f : Filter α} : Tendsto m f (𝓝 ∞) ↔ ∀ n : ℕ, ∀ᶠ a in f, ↑n < m a` | `Tendsto m f (𝓝 ∞) ↔ ∀ n : ℕ, ∀ᶠ a in f, ↑n < m a` | PRESENT |
| `ENNReal.tendsto_nhds_top` | `Mathlib/Topology/Instances/ENNReal/Lemmas.lean:143` | `theorem tendsto_nhds_top {m : α → ℝ≥0∞} {f : Filter α} (h : ∀ n : ℕ, ∀ᶠ a in f, ↑n < m a) : Tendsto m f (𝓝 ∞)` | `Tendsto m f (𝓝 ∞)` | PRESENT |
| **`ENNReal.tendsto_ofReal_nhds_top`** | `Mathlib/Topology/Instances/ENNReal/Lemmas.lean:157` | `@[simp] theorem tendsto_ofReal_nhds_top {f : α → ℝ} {l : Filter α} : Tendsto (fun x ↦ ENNReal.ofReal (f x)) l (𝓝 ∞) ↔ Tendsto f l atTop` | `Tendsto (fun x ↦ ENNReal.ofReal (f x)) l (𝓝 ∞) ↔ Tendsto f l atTop` | PRESENT |
| `ENNReal.tendsto_ofReal_atTop` | `Mathlib/Topology/Instances/ENNReal/Lemmas.lean:161` | `theorem tendsto_ofReal_atTop : Tendsto ENNReal.ofReal atTop (𝓝 ∞)` | `Tendsto ENNReal.ofReal atTop (𝓝 ∞)` | PRESENT |
| `ENNReal.tendsto_coe_nhds_top` | `Mathlib/Topology/Instances/ENNReal/Lemmas.lean:152` | `@[simp, norm_cast] theorem tendsto_coe_nhds_top {f : α → ℝ≥0} {l : Filter α} : Tendsto (fun x => (f x : ℝ≥0∞)) l (𝓝 ∞) ↔ Tendsto f l atTop` | `Tendsto (fun x => (f x : ℝ≥0∞)) l (𝓝 ∞) ↔ Tendsto f l atTop` | PRESENT |
| `ENNReal.tendsto_nat_nhds_top` | `Mathlib/Topology/Instances/ENNReal/Lemmas.lean:147` | `theorem tendsto_nat_nhds_top : Tendsto (fun n : ℕ => ↑n) atTop (𝓝 ∞)` | `Tendsto (fun n : ℕ => ↑n) atTop (𝓝 ∞)` | PRESENT |

### B-2. ENNReal ↔ EReal 変換

| 名前 | file:line | 完全 signature (型クラス verbatim) | 結論形 (verbatim) | 状態 |
|---|---|---|---|---|
| `EReal.toENNReal` (定義) | `Mathlib/Data/EReal/Basic.lean:695` | `noncomputable def toENNReal (x : EReal) : ℝ≥0∞` | `EReal → ℝ≥0∞` | PRESENT |
| `EReal.toENNReal_top` | `Mathlib/Data/EReal/Basic.lean:699` | `@[simp] lemma toENNReal_top : (⊤ : EReal).toENNReal = ⊤` | `(⊤ : EReal).toENNReal = ⊤` | PRESENT |
| `EReal.toENNReal_of_ne_top` | `Mathlib/Data/EReal/Basic.lean:702` | `lemma toENNReal_of_ne_top {x : EReal} (hx : x ≠ ⊤) : x.toENNReal = ENNReal.ofReal x.toReal` | `x.toENNReal = ENNReal.ofReal x.toReal` | PRESENT |
| `EReal.coe_toENNReal` | `Mathlib/Data/EReal/Basic.lean:733` | `lemma coe_toENNReal {x : EReal} (hx : 0 ≤ x) : (x.toENNReal : EReal) = x` | `(x.toENNReal : EReal) = x` | PRESENT |
| `EReal.toENNReal_of_nonpos` | `Mathlib/Data/EReal/Basic.lean:714` | `lemma toENNReal_of_nonpos {x : EReal} (hx : x ≤ 0) : x.toENNReal = 0` | `x.toENNReal = 0` | PRESENT |
| `EReal.toENNReal_eq_top_iff` | `Mathlib/Data/EReal/Basic.lean:706` | `lemma toENNReal_eq_top_iff {x : EReal} : x.toENNReal = ⊤ ↔ x = ⊤` | `x.toENNReal = ⊤ ↔ x = ⊤` | PRESENT |
| `ENNReal.toEReal` (定義) | `Mathlib/Data/EReal/Basic.lean:84` | `@[coe] def _root_.ENNReal.toEReal : ℝ≥0∞ → EReal` | `ℝ≥0∞ → EReal` | PRESENT |

**注**: `differentialEntropy : Measure ℝ → ℝ` は **負値も取りうる** (low-variance Gaussian で
`(1/2) log(2π e v) < 0` あり)。`EReal.toENNReal_of_nonpos` で負値が `0` に潰れるため、
**ENNReal 経路は negative-entropy 領域で情報損失**が起きる。EReal を採用すれば負値は保存。

---

## C. Gaussian sub-entropy 発散 path

### C-1. 本 repo 内既存 (Common2026.Shannon)

| 名前 | file:line | 完全 signature (型クラス verbatim) | 結論形 (verbatim) | 状態 |
|---|---|---|---|---|
| `Common2026.Shannon.differentialEntropy` (定義) | `Common2026/Shannon/DifferentialEntropy.lean:42` | `noncomputable def differentialEntropy (μ : Measure ℝ) : ℝ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume` | `Measure ℝ → ℝ` | PRESENT |
| **`Common2026.Shannon.differentialEntropy_gaussianReal`** | `Common2026/Shannon/DifferentialEntropy.lean:406` | `theorem differentialEntropy_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : differentialEntropy (gaussianReal m v) = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)` | `differentialEntropy (gaussianReal m v) = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)` | PRESENT |
| **`Common2026.Shannon.differentialEntropy_gaussianReal_heat_path`** | `Common2026/Shannon/FisherInfoV2DeBruijn.lean:332` | `theorem differentialEntropy_gaussianReal_heat_path (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {s : ℝ} (hs : 0 ≤ s) : differentialEntropy (gaussianReal m (v + ⟨s, hs⟩)) = (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s))` | `differentialEntropy (gaussianReal m (v + ⟨s, hs⟩)) = (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s))` | PRESENT |
| `Common2026.Shannon.FisherInfoV2.gaussianConvolution` (定義) | `Common2026/Shannon/FisherInfoV2DeBruijn.lean:154` | `noncomputable def gaussianConvolution {α : Type*} (X Z : α → ℝ) (t : ℝ) : α → ℝ := fun ω => X ω + Real.sqrt t * Z ω` | `(α → ℝ) → (α → ℝ) → ℝ → (α → ℝ)` | PRESENT |
| `Common2026.Shannon.FisherInfoV2.gaussianConvolution_law_of_gaussian` | `Common2026/Shannon/FisherInfoV2DeBruijn.lean:172` | `theorem gaussianConvolution_law_of_gaussian {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z) ... ` (略、Gaussian + Gaussian conv. 加算則) | `P.map (gaussianConvolution X Z s) = gaussianReal m (v + ⟨s, hs⟩)` | PRESENT |

### C-2. Mathlib `Real.log` の Tendsto

| 名前 | file:line | 完全 signature (型クラス verbatim) | 結論形 (verbatim) | 状態 |
|---|---|---|---|---|
| **`Real.tendsto_log_atTop`** | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:340` | `theorem tendsto_log_atTop : Tendsto log atTop atTop` | `Tendsto log atTop atTop` | PRESENT |
| `Real.tendsto_log_nhdsGT_zero` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:343` | `lemma tendsto_log_nhdsGT_zero : Tendsto log (𝓝[>] 0) atBot` | `Tendsto log (𝓝[>] 0) atBot` | PRESENT |

### C-3. `Tendsto _ atTop atTop` composition chain (`Real`)

| 名前 | file:line | 完全 signature (型クラス verbatim) | 結論形 (verbatim) | 状態 |
|---|---|---|---|---|
| **`Filter.Tendsto.const_mul_atTop`** | `Mathlib/Order/Filter/AtTopBot/Field.lean:72` | `theorem Tendsto.const_mul_atTop (hr : 0 < r) (hf : Tendsto f l atTop) : Tendsto (fun x => r * f x) l atTop` (`variable {α β : Type*} {l : Filter α} {f : α → β} [LinearOrderedField β] {r : β}`) | `Tendsto (fun x => r * f x) l atTop` | PRESENT |
| `Filter.Tendsto.atTop_mul_const` | `Mathlib/Order/Filter/AtTopBot/Field.lean:79` | `theorem Tendsto.atTop_mul_const (hr : 0 < r) (hf : Tendsto f l atTop) : Tendsto (fun x => f x * r) l atTop` | `Tendsto (fun x => f x * r) l atTop` | PRESENT |
| `Filter.Tendsto.atTop_div_const` | `Mathlib/Order/Filter/AtTopBot/Field.lean:85` | `theorem Tendsto.atTop_div_const (hr : 0 < r) (hf : Tendsto f l atTop) : Tendsto (fun x => f x / r) l atTop` | `Tendsto (fun x => f x / r) l atTop` | PRESENT |
| **`Filter.tendsto_atTop_add_const_right`** (via `to_additive`) | `Mathlib/Order/Filter/AtTopBot/Group.lean:79` (additive 名は同 line、`tendsto_atTop_mul_const_right` の additive 派生) | `theorem tendsto_atTop_add_const_right (l : Filter α) (C : G) (hf : Tendsto f l atTop) : Tendsto (fun x => f x + C) l atTop` (`variable [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]`) | `Tendsto (fun x => f x + C) l atTop` | PRESENT |
| `Filter.tendsto_atTop_add_const_left` | `Mathlib/Order/Filter/AtTopBot/Group.lean:69` (via `to_additive`) | `theorem tendsto_atTop_add_const_left (l : Filter α) (C : G) (hf : Tendsto f l atTop) : Tendsto (fun x => C + f x) l atTop` | `Tendsto (fun x => C + f x) l atTop` | PRESENT |
| `Filter.Tendsto.atTop_add` | `Mathlib/Topology/Order/LeftRightNhds.lean` (loogle 経由判明、line 未確認) | `theorem Tendsto.atTop_add (hf : Tendsto f l atTop) (hg : Tendsto g l atTop) : Tendsto (fun x => f x + g x) l atTop` (詳細位置確認は実装時) | `Tendsto (fun x => f x + g x) l atTop` | UNCLEAR (line 不明、loogle により存在は確認) |
| `Filter.Tendsto.comp` | `Mathlib/Order/Filter/Basic.lean` (core API、line 略) | `theorem Tendsto.comp {f : α → β} {g : β → γ} {l : Filter α} {l' : Filter β} {l'' : Filter γ} (hg : Tendsto g l' l'') (hf : Tendsto f l l') : Tendsto (g ∘ f) l l''` | `Tendsto (g ∘ f) l l''` | PRESENT |

**Gaussian sub-entropy 発散 chain** (具体的 4 段 compose):
1. `tendsto_atTop_add_const_left` (or `_right`) : `Tendsto (fun T => (v : ℝ) + T) atTop atTop` from `tendsto_id`
2. `Tendsto.const_mul_atTop` with `2 * Real.pi * Real.exp 1 > 0` : `Tendsto (fun T => 2*π*e*((v:ℝ) + T)) atTop atTop`
3. `Real.tendsto_log_atTop.comp` (step 2): `Tendsto (fun T => Real.log (2*π*e*((v:ℝ) + T))) atTop atTop`
4. `Tendsto.const_mul_atTop` with `(1/2 : ℝ) > 0` : `Tendsto (fun T => (1/2) * Real.log (2*π*e*((v:ℝ) + T))) atTop atTop`
5. **`differentialEntropy_gaussianReal_heat_path` で congr** : `Tendsto (fun T => differentialEntropy (gaussianReal m (v + ⟨T, _⟩))) atTop atTop`
6. **`EReal.tendsto_coe_nhds_top_iff.mpr`** : `Tendsto (fun T => Real.toEReal (differentialEntropy (...))) atTop (𝓝 ⊤)`

→ 全段 PRESENT、推定 **~10-15 行**。

---

## D. Heat-flow path との接続 (`gaussianConvolution`)

| 名前 | file:line | 完全 signature (型クラス verbatim) | 結論形 (verbatim) | 状態 |
|---|---|---|---|---|
| `Common2026.Shannon.FisherInfoV2.gaussianConvolution_apply` | `Common2026/Shannon/FisherInfoV2DeBruijn.lean:158` | `@[simp] theorem gaussianConvolution_apply {α : Type*} (X Z : α → ℝ) (t : ℝ) (ω : α) : gaussianConvolution X Z t ω = X ω + Real.sqrt t * Z ω` | `gaussianConvolution X Z t ω = X ω + Real.sqrt t * Z ω` | PRESENT |
| `Common2026.Shannon.FisherInfoV2.measurable_gaussianConvolution` | `Common2026/Shannon/FisherInfoV2DeBruijn.lean:162` | `theorem measurable_gaussianConvolution {Ω : Type*} [MeasurableSpace Ω] {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z) (t : ℝ) : Measurable (gaussianConvolution X Z t)` | `Measurable (gaussianConvolution X Z t)` | PRESENT |
| `Common2026.Shannon.EPIL3Integration.gaussianConvolution_at_zero` | `Common2026/Shannon/EPIL3Integration.lean:618` | `theorem gaussianConvolution_at_zero {Ω : Type*} (X Z : Ω → ℝ) : Common2026.Shannon.FisherInfoV2.gaussianConvolution X Z 0 = X` | `gaussianConvolution X Z 0 = X` | PRESENT |
| `Common2026.Shannon.EPIL3Integration.differentialEntropy_gaussianConvolution_at_zero` | `Common2026/Shannon/EPIL3Integration.lean:631` | `theorem differentialEntropy_gaussianConvolution_at_zero {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (P : Measure Ω) : differentialEntropy (P.map (gaussianConvolution X Z 0)) = differentialEntropy (P.map X)` | `differentialEntropy (P.map (gaussianConvolution X Z 0)) = differentialEntropy (P.map X)` | PRESENT |

### D-1. Gaussian + Gaussian convolution の variance 加算則

| 名前 | file:line | 完全 signature (型クラス verbatim) | 結論形 (verbatim) | 状態 |
|---|---|---|---|---|
| `gaussianReal_map_const_mul` | (Mathlib `Probability/Distributions/Gaussian/...`) | `gaussianReal m v` の scalar 倍は `gaussianReal (c*m) (c^2 * v)` | scaling | PRESENT (本 repo の `gaussianConvolution_law_of_gaussian` で間接的に再利用済み) |
| `gaussianReal_add_gaussianReal_of_indepFun` | (Mathlib) | 独立 Gaussian の和は Gaussian (variance 加算) | sum law | PRESENT (同上) |

---

## E. 主要前提条件ボックス (使用時の落とし穴)

- **`EReal.tendsto_coe_nhds_top_iff` は `omit [TopologicalSpace α]`** — section 内では `α : Type*` 単独で OK だが、別 namespace に持ち出すと型クラス推論が `TopologicalSpace α` を要求しうる。`fun x ↦ Real.toEReal (f x)` の lambda 形を **逐語で**書くこと。`Real.toEReal ∘ f` 形では `@[simp]` lemma が発火しないケースあり。
- **`differentialEntropy_gaussianReal_heat_path` の `v : ℝ≥0` 制約** — `v ≠ 0` 必須。本 inventory の Gaussian discharge は `hv : v ≠ 0` 仮定下で書く (parent plan の `isDeBruijnTailHyp_of_gaussian` 引数に既存)。
- **`Tendsto.const_mul_atTop` は `[LinearOrderedField β]`** — `ℝ` ならば OK。`hr : 0 < r` 引数を `(by norm_num : (0:ℝ) < 1/2)` 等で都度供給。
- **`EReal.toENNReal_of_nonpos` で負値が `0` に潰れる** — `differentialEntropy` が負を取りうる (low-variance Gaussian) ため、`ℝ≥0∞` 経路採用時は `negMulLog` 由来の負域で情報損失。**EReal 推奨**の根拠。
- **`Tendsto m f (𝓝 ⊤)` の filter monotonicity** — Phase C-4 で `T → ∞` 極限を `Filter.atTop` で書く際、`Filter.NeBot atTop` は `[Nonempty α]` 系で自動だが、`α := Set.Ioi (0 : ℝ)` のような subtype を考えるとケアが必要 (本 inventory の path は ambient `ℝ` で十分)。

---

## F. 自作が必要な要素

| 優先度 | 補題 | 推定 LoC | 落とし穴 |
|---|---|---|---|
| 1 | `differentialEntropy_gaussianReal_heat_path_tendsto_atTop` (Gaussian discharge の本体): `Tendsto (fun T => differentialEntropy (gaussianReal m (v + ⟨T, hT.le⟩))) atTop atTop` (`hv : v ≠ 0` 下) | ~15 行 | `(v + ⟨T, hT.le⟩ : ℝ≥0)` の subtype coerce、`Real.log` 引数 `2πe(v+T) > 0` の `positivity` |
| 2 | `differentialEntropy_gaussianReal_heat_path_tendsto_coe_top` (EReal lift): `Tendsto (fun T => Real.toEReal (differentialEntropy (gaussianReal m (v + ⟨T, _⟩)))) atTop (𝓝 ⊤)` | ~3 行 (priority 1 + `tendsto_coe_nhds_top_iff.mpr`) | lambda 形維持 |
| 3 | `isDeBruijnTailHyp_of_gaussian` (Gaussian instance constructor): structure に `Z_law : P.map Z = gaussianReal 0 1` field 追加した上で `tail_limit := priority 2 lemma`, `h_inf := ⊤` で実装 | ~20 行 (structure 改修込み) | `P.map (gaussianConvolution X Z T) = gaussianReal m (v + ⟨T, _⟩)` の law 計算 (`gaussianConvolution_law_of_gaussian` 既存) |
| 4 | `IsDeBruijnTailHyp` structure 再定義 (`h_inf : EReal` + `Z_law` field + `tail_limit : Tendsto _ atTop (𝓝 h_inf)` を coerce 形 `Tendsto (fun T => Real.toEReal (...)) atTop (𝓝 h_inf)`) | ~10 行 (structure + docstring + `@audit:staged` タグ) | predicate semantics の honesty: `Z_law` 必須で `Z := 0` bypass を閉じる |

**合計**: ~50 行。Gaussian discharge は **PRESENT-bridgeable**。

---

## G. 撤退ライン判定

親 plan [`epi-debruijn-integration-plan.md`](./epi-debruijn-integration-plan.md) の撤退ライン:

- **L-DB-C-α** (IBP Mathlib gap): 本 inventory と無関係 (`IsIBPHypothesis` 路は separate)。**発動なし**。
- **L-DB-C-β** (`T → ∞` tail non-Gaussian で破綻): 本 inventory が **再導入を支援する撤退ライン**。`h_inf : EReal` lift + `Z_law` field 追加で **Gaussian case は genuine closure 可** ことを本 inventory が確認 (上記 F-1〜3、全 PRESENT/bridgeable)。non-Gaussian case は依然 honest hypothesis (`@audit:staged(epi-debruijn-tail)`) で外出し。

**新規撤退ライン提案** (sister plan 起草者向け):

- **L-Tail-α** (許容): non-Gaussian `X` で `Tendsto (fun T => differentialEntropy (P.map (X+√T·Z))) atTop atTop` が **Cover-Thomas tail bound 経由でも書けない** → predicate を Gaussian instance のみで生かし、non-Gaussian consumer は分離 plan に外出し。**現状の Mathlib では本 path は不要、Gaussian discharge で十分**。
- **L-Tail-β** (許容): `EReal` 経路で type-class 推論が `Real.toEReal` の `@[coe]` で詰まる場合 → 明示 `Real.toEReal` 形を全箇所に書き下す (paraphrase 禁止)。**現状の Mathlib では発動なし** (上記 A-2 で `omit [TopologicalSpace α]` 確認済み)。
- **L-Tail-γ** (許容): `Z_law` 追加で既存 consumer (Phase D `EPIL3Integration`) との signature mismatch → 旧 predicate を `_legacy` 名で残し新 predicate に bridge lemma 提供。**signature 段階で予防可能** (parent plan Phase C-5 step で +20 行と明記)。

→ **本 inventory による撤退ライン発動: NO**。Gaussian discharge 路が PRESENT-bridgeable で `genuine` に書けるため、新規撤退ラインは sister plan 設計時に「予防」として記録する程度で十分。

---

## H. 着手 skeleton

`Common2026/Shannon/EPIL3Integration.lean` に既存 retract コメント (`:595-613`) の直後に追記:

```lean
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Group

-- (既存 imports は維持、EPIL3Integration.lean には大半既存)

namespace Common2026.Shannon

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **De Bruijn tail hypothesis (re-introduced, honest load-bearing)**.

For `X : Ω → ℝ` with law `P.map X` and `Z : Ω → ℝ` standard normal driving the
heat flow, this predicate externalizes the `T → ∞` asymptotic of the heat-flow
differential entropy.

`@audit:staged(epi-debruijn-tail)` — honest load-bearing hypothesis, NOT a
discharge. Gaussian instance is provided by `isDeBruijnTailHyp_of_gaussian`. -/
structure IsDeBruijnTailHyp
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] : Type where
  /-- `Z` is the standard normal driving the heat flow (vacuous bypass closure). -/
  Z_law : P.map Z = gaussianReal 0 1
  /-- The asymptotic value (EReal-valued; Gaussian case ⊤). -/
  h_inf : EReal
  /-- Heat-flow entropy converges to `h_inf` via coercion through `Real.toEReal`. -/
  tail_limit :
    Tendsto
      (fun T : ℝ => Real.toEReal
        (Common2026.Shannon.differentialEntropy
          (P.map (Common2026.Shannon.FisherInfoV2.gaussianConvolution X Z T))))
      atTop (𝓝 h_inf)

/-- **Gaussian instance**: when `P.map X = gaussianReal m v` with `v ≠ 0` and
`P.map Z = gaussianReal 0 1` (independent), the heat-flow entropy diverges to
`+∞` and `h_inf := ⊤` is genuine. -/
noncomputable def isDeBruijnTailHyp_of_gaussian
    {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P) (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1) :
    IsDeBruijnTailHyp X Z P := by
  sorry  -- F-3, ~20 行 plumbing

end Common2026.Shannon
```

(上記は inventory 用 skeleton であって、`Common2026/Shannon/EPIL3Integration.lean` への直接編入は
sister plan `epi-debruijn-tail-reintroduction-plan.md` Phase C-5 implementer の責務。)

---

## 一覧サマリ (テーブル件数)

- A. EReal Tendsto/nhds: **11 件全 PRESENT**
- B. ENNReal Tendsto/conversion: **13 件全 PRESENT**
- C. Gaussian sub-entropy chain: **本 repo 5 件 + Mathlib `Real.log` 2 件 + atTop chain 6 件 + 1 件 UNCLEAR (`Tendsto.atTop_add` line)** = 12/13 PRESENT, 1/13 UNCLEAR (実装時 5 分で line 確認可)
- D. Heat-flow path 接続: **4 件全 PRESENT** (本 repo) + Mathlib Gaussian 加算則 2 件 PRESENT
- 自作必要: **4 件 (~50 行)**、全 `bridgeable`

**既存率**: ~95% (Gaussian discharge 路は 100% bridgeable、predicate 再定義 + Gaussian instance 構築のみ自作)。
**撤退ライン発動**: NO。Gaussian discharge 路は現状 Mathlib で genuine に書ける。
