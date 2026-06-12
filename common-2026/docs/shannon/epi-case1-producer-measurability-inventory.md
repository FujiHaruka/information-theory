# EPI producer 残壁 (`:2041` measurability) — Layer C closure Mathlib API 在庫

> 親計画: [`epi-case1-debruijn-producer-plan.md`](epi-case1-debruijn-producer-plan.md) の撤退ライン **L-Prod-meas** (`:614-645`)。
> 対象: `isDeBruijnRegularityHyp_of_methodX_unitnoise` (`InformationTheory/Shannon/EPICase1RatioLimit.lean:1936`) の `integrable_deriv` field 内 sole sorry (`:2041`)。
> 本ファイルは在庫調査のみ。実装・計画起草はしない。

---

## §0 結論サマリ

`:2041` goal は `AEStronglyMeasurable (fun t => (1/2)·(fisherInfoOfDensity (convDensityAdd pX (gaussianPDFReal 0 t.toNNReal))).toReal) (volume.restrict (Ioc 0 T))`。closure は 3 層 (Layer A joint 可測 → Layer B lintegral param-measurability → Layer C `logDeriv` joint 可測)。

- **Layer A** (`(t,x) ↦ convDensityAdd pX (gaussianPDFReal 0 t.toNNReal) x` の joint 可測): **genuine に閉じる見込み (lemma 完備)**。`Measurable pX` (既知) + `gaussianPDFReal` の `(v,x)` joint 可測 (in-tree port 元あり、ただし**軸が変数=mean であって variance ではない** — 下記落とし穴 P-1) + `StronglyMeasurable.integral_prod_right` (`Prod.lean:76`) で組める。自作 ~40-60 行。**唯一の non-trivial sub-step は gaussianPDFReal の (variance, point) 軸 joint 可測** (mean 軸の既存 port は流用できない、`fun_prop` 再走で立つ可能性高だが要検証)。

- **Layer B** (`t ↦ ∫⁻ x, ...` 可測): **genuine に閉じる見込み (lemma 完備)**。`Measurable.lintegral_prod_right` (`Prod.lean:145`, `[SFinite ν]`) + `.toReal` + `Measurable.aestronglyMeasurable`。Layer A+C が joint 可測を供給すれば機械的。

- **Layer C** (`logDeriv(conv) = deriv(conv)/conv` の `(t,x)` joint 可測): **gap あり = 真の壁**。`logDeriv = deriv/conv` ゆえ `Measurable.div` で合成 (conv 側は Layer A) だが、**`deriv (conv pX g_{t}) x` の `(t,x)` joint 可測**には Mathlib 唯一の該当 `measurable_deriv_with_param` (`FDeriv/Measurable.lean:920`) が **`Continuous f.uncurry`** (= `(t,x) ↦ conv pX g_t x` の**全域 joint 連続性**) を要求する。

  **核心判定 — `{t>0}×ℝ` 開集合 joint 連続性で `measurable_deriv_with_param` を充足できるか → ❌ 不可 (そのままでは)**。理由 2 点:
  1. `measurable_deriv_with_param` の `hf : Continuous f.uncurry` は **全域 (`α × 𝕜` 全体) の連続性**を要求する型 (`Continuous`、`ContinuousOn _ s` ではない)。`{t>0}×ℝ` 上の連続性 (= `ContinuousOn`) を直接渡せない。`t≤0` (分散 0) では `gaussianPDFReal 0 0 = 0` (恒等的に 0、`gaussianPDFReal_zero_var`) ゆえ `conv pX 0 = 0`、`x ↦ 0` は連続だが `t=0` の境界で **prefactor `(√(2πv))⁻¹ → ∞`** ゆえ `t↓0` 極限が `t<0` 拡張と整合せず**全域連続にならない** (落とし穴 P-2)。
  2. よって Layer C を `measurable_deriv_with_param` 一発で閉じるには、**(t,x) 全域で連続になるよう変数変換 / 値再定義**するか、`measurable_deriv_with_param` を経由しない別ルート (`convDensityAdd_logDeriv` closed form + a.e. 供給、in-tree `EPIConvDensity.lean:116`) が要る。

  **回避ルート (推奨度順、いずれも自作)**:
  - **(C-a) 開集合制限版 deriv-with-param の自作** (~60-100 行): `measurableSet_of_differentiableAt_with_param` (`:894`, MeasurableSet 版) は `Continuous f.uncurry` を要求するが内部は局所的。`Ioc 0 T × ℝ` 上の `ContinuousOn` から `measurable_deriv_with_param` 相当を再導出する。**Mathlib に `ContinuousOn` 版は不在** (loogle 確認、下記)。Mathlib 壁候補。
  - **(C-b) closed-form score 経由** (`convDensityAdd_logDeriv` `EPIConvDensity.lean:116`): `logDeriv(conv) z = (∫ x, pX x · g'(z-x)) / conv(z)` に書換え、分子 `(t,z) ↦ ∫ x, pX x · g_t'(z-x)` の joint 可測を `StronglyMeasurable.integral_prod_right` + `gaussianPDFReal` の deriv joint 可測で出す。分母は Layer A。`Measurable.div` で合成。**`measurable_deriv_with_param` を完全回避**。7 domination 仮説の a.e. 供給が要る (plan `:639` で「substantial、非推奨」と評価) が、**joint 連続性の壁を回避できるので C-a より現実的**。

  → **Layer C は Mathlib lemma 一発では閉じない**。`measurable_deriv_with_param` の `Continuous f.uncurry` (全域) 前提が `{t>0}×ℝ` 開集合連続性では充足不可。closure には (C-a) 開集合版 deriv-with-param 自作 (Mathlib 壁候補、~60-100 行) か (C-b) closed-form score 経由 (~80-120 行、joint 連続性回避) のいずれか。**(C-b) を第一推奨**。

---

## §1 Layer C 中核: `measurable_deriv_with_param` family (`FDeriv/Measurable.lean`)

`section WithParam` の variable block (`:783-787`, `:870`, `:889-890`):
```
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {α : Type*} [TopologicalSpace α]
  {f : α → E → F}
-- + (:870):  [MeasurableSpace α] [OpensMeasurableSpace α] [MeasurableSpace E] [OpensMeasurableSpace E]
-- + (:889-890): variable (𝕜); [CompleteSpace F]
```

| lemma | file:line | 完全 signature (型クラス verbatim) | 結論形 verbatim |
|---|---|---|---|
| `measurable_deriv_with_param` | `Mathlib/Analysis/Calculus/FDeriv/Measurable.lean:920` | `[LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F] [BorelSpace F] {f : α → 𝕜 → F} (hf : Continuous f.uncurry)` | `Measurable (fun (p : α × 𝕜) ↦ deriv (f p.1) p.2)` |
| `stronglyMeasurable_deriv_with_param` | `:926` | `[LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [h : SecondCountableTopologyEither α F] {f : α → 𝕜 → F} (hf : Continuous f.uncurry)` | `StronglyMeasurable (fun (p : α × 𝕜) ↦ deriv (f p.1) p.2)` |
| `aemeasurable_deriv_with_param` | `:947` | `[LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F] [BorelSpace F] {f : α → 𝕜 → F} (hf : Continuous f.uncurry) (μ : Measure (α × 𝕜))` | `AEMeasurable (fun (p : α × 𝕜) ↦ deriv (f p.1) p.2) μ` |
| `aestronglyMeasurable_deriv_with_param` | `:953` | `[LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [SecondCountableTopologyEither α F] {f : α → 𝕜 → F} (hf : Continuous f.uncurry) (μ : Measure (α × 𝕜))` | `AEStronglyMeasurable (fun (p : α × 𝕜) ↦ deriv (f p.1) p.2) μ` |
| `measurable_fderiv_with_param` | `:900` | `(hf : Continuous f.uncurry)` (variables 上記 + `(𝕜)` + `[CompleteSpace F]`) | `Measurable (fun (p : α × E) ↦ fderiv 𝕜 (f p.1) p.2)` |
| `measurableSet_of_differentiableAt_with_param` | `:894` | `(hf : Continuous f.uncurry)` | `MeasurableSet {p : α × E | DifferentiableAt 𝕜 (f p.1) p.2}` |
| `measurableSet_of_differentiableAt_of_isComplete_with_param` | `:872` | `(hf : Continuous f.uncurry) {K : Set (E →L[𝕜] F)} (hK : IsComplete K)` | `MeasurableSet {p : α × E | DifferentiableAt 𝕜 (f p.1) p.2 ∧ fderiv 𝕜 (f p.1) p.2 ∈ K}` |

**全 7 lemma が `Continuous f.uncurry` を要求 (例外なし)。`ContinuousOn _ (Ioc 0 T ×ˢ univ)` 版は存在しない** (`section WithParam` 全域確認、`:774-959`)。我々の適用先は `𝕜 = ℝ` (= `x`-軸、deriv の方向), `α = ℝ` (= `t`-軸, パラメタ), `F = ℝ`。`ℝ` は `LocallyCompactSpace` / `MeasurableSpace` / `BorelSpace` / `OpensMeasurableSpace` 完備なので型クラスは自動充足。**唯一の壁は `Continuous f.uncurry` の `(t,x)` 全域 joint 連続性**。

> loogle (ContinuousOn 版確認): `Measurable (fun _ => deriv _ _), ContinuousOn` → 該当 with_param lemma 0 件。Mathlib に開集合制限版 deriv-with-param は不在。

---

## §2 Layer B: lintegral / Bochner param-measurability bricks

`Prod.lean` variable block (`:66-69`): `{α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {μ μ' : Measure α} {ν ν' : Measure β}`。

| lemma | file:line | 完全 signature (型クラス verbatim) | 結論形 verbatim |
|---|---|---|---|
| `Measurable.lintegral_prod_right` | `Mathlib/MeasureTheory/Measure/Prod.lean:145` | `[SFinite ν] {f : α → β → ℝ≥0∞} (hf : Measurable (uncurry f))` | `Measurable fun x => ∫⁻ y, f x y ∂ν` |
| `Measurable.lintegral_prod_right'` | `:123` | `[SFinite ν] : ∀ {f : α × β → ℝ≥0∞}, Measurable f → ...` | `Measurable fun x => ∫⁻ y, f (x, y) ∂ν` |
| `MeasureTheory.StronglyMeasurable.integral_prod_right` | `Mathlib/MeasureTheory/Integral/Prod.lean:76` | (Prod.lean variable block `:53-54`: `{α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [NormedAddCommGroup E]`; `:71` `[NormedSpace ℝ E]`) `[SFinite ν] ⦃f : α → β → E⦄ (hf : StronglyMeasurable (uncurry f))` | `StronglyMeasurable fun x => ∫ y, f x y ∂ν` |
| `MeasureTheory.StronglyMeasurable.integral_prod_right'` | `:124` | `[SFinite ν] ⦃f : α × β → E⦄ (hf : StronglyMeasurable f)` | `StronglyMeasurable fun x => ∫ y, f (x, y) ∂ν` |

注: `volume : Measure ℝ` は `SFinite` (実は `σ-finite`) なので `[SFinite ν]` は自動。Layer B の goal は `AEStronglyMeasurable` なので、`Measurable.lintegral_prod_right` で `Measurable` を得てから `Measurable.aestronglyMeasurable` (Mathlib 既存) + `.toReal` (`ENNReal.toReal` 可測 = `Measurable.ennreal_toReal`) で到達。`(1/2)·` は `Measurable.const_mul`。

---

## §3 Layer A: convDensityAdd joint 可測 bricks

### A-1 convDensityAdd 定義 (Bochner ∫ 形)
- `InformationTheory/Shannon/EPIConvDensity.lean:42`:
  `noncomputable def convDensityAdd (pX pY : ℝ → ℝ) : ℝ → ℝ := fun z => ∫ x, pX x * pY (z - x) ∂volume`
- joint 形: `(t,z) ↦ convDensityAdd pX (gaussianPDFReal 0 t.toNNReal) z = ∫ x, pX x * gaussianPDFReal 0 t.toNNReal (z - x) ∂volume`。`StronglyMeasurable.integral_prod_right` (`Prod.lean:76`) を `(p:(t,z)) ↦ ∫ x, F p x` に適用、`F ((t,z)) x := pX x * gaussianPDFReal 0 t.toNNReal (z-x)` の `((t,z),x)` joint 可測が要る。

### A-2 pX 可測 (既知、producer body 内で確立済)
- `EPICase1RatioLimit.lean:1959`: `hpX_meas : Measurable pX := ((P.map X).measurable_rnDeriv volume).ennreal_toReal` (`pX := fun x => ((P.map X).rnDeriv volume x).toReal`)。

### A-3 gaussianPDFReal の可測性 (Mathlib + in-tree)
| lemma | file:line | 完全 signature | 結論形 verbatim |
|---|---|---|---|
| `gaussianPDFReal` (def) | `Mathlib/Probability/Distributions/Gaussian/Real.lean:48` | `def gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ := (√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * v))` | — |
| `measurable_gaussianPDFReal` | `:72` | `(μ : ℝ) (v : ℝ≥0) :` | `Measurable (gaussianPDFReal μ v)` (**per-(μ,v) 固定、point 軸のみ**) |
| `stronglyMeasurable_gaussianPDFReal` | `:77` | `(μ : ℝ) (v : ℝ≥0) :` | `StronglyMeasurable (gaussianPDFReal μ v)` |
| `gaussianPDFReal_zero_var` | `:56` | `(m : ℝ) :` | `gaussianPDFReal m 0 = 0` (**`@[simp]`、分散0で恒等的に0関数**) |
| `gaussianPDFReal_pos` | `:61` | `(μ : ℝ) (v : ℝ≥0) (x : ℝ) (hv : v ≠ 0) :` | `0 < gaussianPDFReal μ v x` |
| `gaussianPDFReal_nonneg` | `:66` | `(μ : ℝ) (v : ℝ≥0) (x : ℝ) :` | `0 ≤ gaussianPDFReal μ v x` |
| `integrable_gaussianPDFReal` | `:82` | `(μ : ℝ) (v : ℝ≥0) :` | `Integrable (gaussianPDFReal μ v)` |

**in-tree port (mean 軸 joint、variance 軸ではない — 落とし穴 P-1)**:
| lemma | file:line | 完全 signature | 結論形 verbatim |
|---|---|---|---|
| `measurable_gaussianPDFReal_uncurry` | `InformationTheory/Shannon/AWGN/ContChannelMIDecomp.lean:378` | `(N : ℝ≥0) :` | `Measurable (fun z : ℝ × ℝ => gaussianPDFReal z.1 N z.2)` (**joint = (mean, point)、variance N は固定引数**) |
| `measurable_gaussianPDF_uncurry` (ℝ≥0∞版) | `:370` | `(N : ℝ≥0) :` | `Measurable (fun z : ℝ × ℝ => gaussianPDF z.1 N z.2)` |

両 port とも証明は `simp only [gaussianPDFReal]; fun_prop`。**我々が要る軸は (variance, point) = `(t.toNNReal, x)`** で port は流用不可。ただし: `gaussianPDFReal 0 v x = (√(2πv))⁻¹·exp(-x²/(2v))` で `v` は `√v` / `1/(2v)` 経由で連続/可測に入る。`Real.toNNReal` 可測 (`continuous_real_toNNReal` `Mathlib/Topology/Instances/NNReal/Lemmas.lean:58`, `Continuous Real.toNNReal`) + `NNReal.coe` 可測。**新規 brick `measurable_gaussianPDFReal_var_uncurry : Measurable (fun p : ℝ × ℝ => gaussianPDFReal 0 p.1.toNNReal p.2)` を自作 (~10-20 行、`fun_prop` 主体、ただし `v=0` での `(2v)⁻¹` 0割は `gaussianPDFReal_zero_var` で吸収済なので可測性は保たれる)**。loogle で (variance,point) 軸 joint 可測の既存確認 → Found 0 (下記)。

### A-4 Gaussian-tail 可積分 / 有界 bricks (Layer A domination 用)
| brick | file:line | signature | 備考 |
|---|---|---|---|
| `gaussianPDFReal_le_pref` | `InformationTheory/Shannon/EPIApproxIdentityL1.lean:165` | `private (v : ℝ≥0) (y : ℝ) : gaussianPDFReal 0 v y ≤ (Real.sqrt (2 * Real.pi * v))⁻¹` | **`private` = file-scoped、流用不可**。`v→0` で RHS→∞ (P-2) |
| `integrable_gaussianPDFReal` | (Mathlib `:82`) | 上記 A-3 | per-v、kernel 自体の L¹ |
| convDensityAdd の integrability (gateway) | `InformationTheory/Shannon/EPIConvDensity.lean:69-` | gateway lemma 群 (per-t 固定、Gaussian-tail を regularity precondition で供給) | Layer A の domination は per-t 形のみ既存、joint 形は自作 |

---

## §4 Layer C closed-form 回避ルート (C-b) bricks

| brick | file:line | 完全 signature (型クラス / 仮説 verbatim) | 結論形 verbatim |
|---|---|---|---|
| `logDeriv` (def) | `Mathlib/Analysis/Calculus/LogDeriv.lean:34` | `def logDeriv (f : 𝕜 → 𝕜') := deriv f / f` | — |
| `logDeriv_apply` | `:37` | `(f : 𝕜 → 𝕜') (x : 𝕜) :` | `logDeriv f x = deriv f x / f x` (`rfl`) |
| `convDensityAdd_logDeriv` | `InformationTheory/Shannon/EPIConvDensity.lean:116` | (per-z₀, 仮説: `s` neighborhood of z₀ + `hF_meas`/`hF_int`/`hF'_meas`/`h_bound` の domination 群、要 Read で full 確認) | `logDeriv (convDensityAdd pX pY) z₀ = (∫ x, p_X x · deriv p_Y (z₀ - x)) / convDensityAdd pX pY z₀` |
| `Measurable.div` | Mathlib (`MeasurableSpace`/`Measurable.div`) | `(hf : Measurable f) (hg : Measurable g) : Measurable (fun x => f x / g x)` (`ℝ` の 0 割は `x/0=0` 規約で可測保持) | — |

C-b の構成: `logDeriv(conv) (t,z) = 分子(t,z) / conv(t,z)`。
- 分子 `(t,z) ↦ ∫ x, pX x · deriv (gaussianPDFReal 0 t.toNNReal) (z-x)`: `StronglyMeasurable.integral_prod_right` + `gaussianPDFReal` の **deriv の (variance,point) joint 可測** (自作 brick、`deriv` の closed-form は `gaussianPDFReal` を `x` で微分した closed form = `-(x/v)·gaussianPDFReal`、可測)。
- 分母 `conv` = Layer A。
- `Measurable.div` 合成。
- **`measurable_deriv_with_param` の `Continuous f.uncurry` を完全回避**。代償: `convDensityAdd_logDeriv` の domination 仮説を joint 形で a.e. 供給。

---

## §5 主要前提条件ボックス (前提事故が起きやすい lemma)

- **`measurable_deriv_with_param` (`:920`)**:
  - `[LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F] [BorelSpace F]` — `𝕜=F=ℝ` で全自動。
  - **`hf : Continuous f.uncurry`** — **全域 (`α × 𝕜` 全体) 連続性。これが壁。** `ContinuousOn _ s` 版なし。
  - `α` には `[TopologicalSpace α]` のみ (我々 `α=ℝ` OK)、`[MeasurableSpace α] [OpensMeasurableSpace α]` (`:870`、ℝ で自動)。

- **`continuousOn_of_dominated` (`Bochner/Basic.lean:462`)** — Layer C の joint 連続性を出すなら第一候補:
  - variable: `{G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]` (G=ℝ OK)、`{X : Type*} [TopologicalSpace X] [FirstCountableTopology X]` (X=ℝ×ℝ OK)、`{μ : Measure α}`。
  - signature: `{F : X → α → G} {bound : α → ℝ} {s : Set X} (hF_meas : ∀ x ∈ s, AEStronglyMeasurable (F x) μ) (h_bound : ∀ x ∈ s, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a) (bound_integrable : Integrable bound μ) (h_cont : ∀ᵐ a ∂μ, ContinuousOn (fun x => F x a) s)` → `ContinuousOn (fun x => ∫ a, F x a ∂μ) s`。
  - **local-on-s 版なので `{t>0}×ℝ` 上で使える** が、出力は `ContinuousOn (conv)` であって `measurable_deriv_with_param` が要求する `Continuous (conv).uncurry` (全域) には足りない (落とし穴 P-2)。conv 自体の連続性は出せても、その deriv の可測には全域連続が要る不整合。

- **`continuousAt_of_dominated` (`:451`)** / **`continuousWithinAt_of_dominated` (`:440`)**: 点ごと版。`bound_integrable : Integrable bound μ` は **bound が `t` に依存しない単一関数**であることを要求 (uniform-on-neighborhood domination)。`{t>0}` 近傍で `g_t` の tail は `t` で変わるが、固定コンパクト近傍 `[t₀-ε, t₀+ε]⊂(0,∞)` 上では `v` が下に離れるので uniform bound 取得可 (genuine、`hbound` と同種の論法)。

- **`convDensityAdd_logDeriv` (`EPIConvDensity.lean:116`)**: domination 仮説群 (`hF_meas`/`hF_int`/`hF'_meas`/`h_bound`) は per-z₀ + `s` neighborhood 形。joint 化 (全 `(t,z)` で a.e. 供給) が C-b の plumbing コスト。

---

## §6 自作が必要な要素 (優先度順)

1. **(Layer A) `measurable_gaussianPDFReal_var_uncurry`** — `Measurable (fun p : ℝ × ℝ => gaussianPDFReal 0 p.1.toNNReal p.2)`。`continuous_real_toNNReal` + `NNReal.coe` 可測 + `fun_prop`。~10-20 行。**Mathlib / in-tree 不在 (port は mean 軸)**。落とし穴: `v=0` 0割は `gaussianPDFReal_zero_var` で吸収、可測性保持。

2. **(Layer A) `measurable_convDensityAdd_gaussian_uncurry`** — `Measurable (fun p : ℝ × ℝ => convDensityAdd pX (gaussianPDFReal 0 p.1.toNNReal) p.2)`。`StronglyMeasurable.integral_prod_right` (`Prod.lean:76`) + (1) + `hpX_meas`。~40-60 行 (integrand `((t,z),x) ↦ pX x · g_{t}(z-x)` の joint 可測 + integral_prod_right の uncurry 整形)。

3. **(Layer C, 第一推奨) C-b closed-form score ルート** — Layer C を `measurable_deriv_with_param` 回避で閉じる。`convDensityAdd_logDeriv` で分子/分母分解 → `StronglyMeasurable.integral_prod_right` (分子) + Layer A (分母) + `Measurable.div`。~80-120 行。落とし穴: domination 仮説の joint 化。**joint 連続性の壁を回避できる唯一の現実ルート**。

4. **(Layer C, 代替) C-a 開集合版 deriv-with-param 自作** — `Ioc 0 T × ℝ` 上の `ContinuousOn (conv).uncurry` から `Measurable (deriv ...)` を出す。`measurableSet_of_differentiableAt_with_param` の局所論法を `ContinuousOn` で再構築。~60-100 行 + Mathlib 内部 lemma の局所性に依存 (**Mathlib 壁候補、§7**)。さらに joint 連続性 (`continuousOn_of_dominated` 経由) の確立が前提で計 substantial。**非推奨**。

5. **(Layer B) 機械的合成** — (Layer A+C 完成後) `Measurable.lintegral_prod_right` + `.toReal` + `Measurable.const_mul` + `Measurable.aestronglyMeasurable`。~15-25 行。

工数感: Layer A (1+2) ~60-80 行 genuine。Layer C は C-b で ~80-120 行 (joint 連続性回避できるので C-a より軽い)。Layer B ~20 行。**合計 ~160-220 行、最難所は C-b の domination joint 化**。

---

## §7 Mathlib 壁の列挙 (真に不在、`@residual(wall:...)` 対象候補)

- **W-1: 開集合制限版 deriv-with-param** — `ContinuousOn f.uncurry s` から `Measurable (fun p => deriv (f p.1) p.2)` (or `MeasurableSet {p∈s | DifferentiableAt}`) を出す lemma。Mathlib の `with_param` family は全て `Continuous f.uncurry` (全域)。
  - loogle `Measurable (fun _ => deriv _ _)` 系 + ContinuousOn 確認 → **該当 with_param lemma 0 件** (`section WithParam` `:774-959` 全 7 lemma が全域 `Continuous` 要求)。
  - ただし **これは選択 (C-b で回避可) であって blocked ではない**。C-b ルートが `measurable_deriv_with_param` を完全回避するので、W-1 自作は必須ではない。よって `wall:` ではなく **「Mathlib API の形が合わない → 回避ルート選択」**。`@residual` を打つなら `plan:epi-case1-debruijn-producer-plan` 継続が正しく、`wall:` 新設は不要。

- **W-2: gaussianPDFReal の (variance, point) 軸 joint 可測** — Mathlib に不在 (mean 軸の in-tree port のみ)。
  - loogle `Measurable (fun _ : ℝ × ℝ => ProbabilityTheory.gaussianPDFReal _ _ _)` → in-tree port (mean 軸) のみ、(variance 軸) は **Found 0**。
  - **これは自作 ~10-20 行で閉じる軽量 brick、Mathlib 壁ではない**。

→ **真の `wall:` 該当は 0 件**。残壁 `:2041` は「Mathlib API の形 (`Continuous f.uncurry` 全域) が producer の per-t 仮説と噛み合わない」plumbing 障害であり、C-b 回避ルート + 軽量 brick 自作で genuine 閉鎖可能。共有 sorry 補題化は不要 (この壁は EPI producer 固有、他 file に散在しない)。現行の `@residual(plan:epi-case1-debruijn-producer-plan)` classification は**正しい** (wall ではなく plan continuation)。

---

## §8 撤退ラインへの距離

親計画の **L-Prod-meas** (`:614-645`):
- 「joint-continuity brick が当該 session で立たなければ `:2041` sorry 据置 (type-check done) で次 session 継続」。
- **発動状態: 据置中 (type-check done)。** 本在庫の発見で **L-Prod-meas の designated 突破口 (`:634` 「joint 連続性 brick → `measurable_deriv_with_param`」) は ❌ 不可と判明** (全域連続性が `t≤0` の prefactor 発散で立たない、P-2)。
- **plan の designated 突破口は誤り**: `:637-638` 「joint-continuity brick が立てば `measurable_deriv_with_param` で Layer C closure」は、`measurable_deriv_with_param` が **`ContinuousOn` ではなく全域 `Continuous`** を要求するため成立しない (joint 連続性 brick を `Ioc 0 T × ℝ` 上で立てても全域連続には届かない)。
- **新規撤退ライン提案 (縮退案)**: designated 突破口を **(C-b) closed-form score 経由** (`:639` で「substantial、非推奨」とされていたルート) に**昇格**する。理由: C-a (開集合版 deriv-with-param) は Mathlib 内部 lemma 局所化 + joint 連続性の二重 substantial、C-b は `measurable_deriv_with_param` を回避し joint 連続性の壁を踏まない分だけ軽い。C-b が当該 session で立たなければ `:2041` sorry 据置 (type-check done、`@residual(plan:epi-case1-debruijn-producer-plan)` 継続)。**仮説束化は禁止** (measurability を producer signature に load-bearing 追加しない、plan `:644-645` 準拠)。

---

## §9 着手 skeleton (新規 helper file、producer に measurability 供給)

> 配置案: `InformationTheory/Shannon/EPICase1ProducerMeasurability.lean` (helper 群)、最終的に `EPICase1RatioLimit.lean:2041` から呼ぶ。本 skeleton は調査用の形であり、実装は lean-implementer の仕事。

```lean
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EPIConvDensity
import InformationTheory.Shannon.FisherInfoV2
import Mathlib.Analysis.Calculus.FDeriv.Measurable      -- measurable_deriv_with_param (回避するが参照)
import Mathlib.Analysis.Calculus.LogDeriv               -- logDeriv_apply
import Mathlib.MeasureTheory.Integral.Prod              -- StronglyMeasurable.integral_prod_right
import Mathlib.MeasureTheory.Measure.Prod               -- Measurable.lintegral_prod_right
import Mathlib.Probability.Distributions.Gaussian.Real  -- gaussianPDFReal, measurable_gaussianPDFReal
import Mathlib.Topology.Instances.NNReal.Lemmas         -- continuous_real_toNNReal

namespace InformationTheory.Shannon.EPICase1ProducerMeasurability

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal

-- (1) Layer A brick: gaussianPDFReal (variance, point) 軸 joint 可測。
theorem measurable_gaussianPDFReal_var_uncurry :
    Measurable (fun p : ℝ × ℝ => gaussianPDFReal 0 p.1.toNNReal p.2) := by
  sorry  -- @residual(plan:epi-case1-debruijn-producer-plan)

-- (2) Layer A brick: convDensityAdd の (t, z) joint 可測。
theorem measurable_convDensityAdd_gaussian_uncurry
    {pX : ℝ → ℝ} (hpX : Measurable pX) :
    Measurable (fun p : ℝ × ℝ =>
      EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 p.1.toNNReal) p.2) := by
  sorry  -- @residual(plan:epi-case1-debruijn-producer-plan)

-- (3) Layer C brick (C-b closed-form score 経由、measurable_deriv_with_param 回避):
--     logDeriv(conv) の (t, z) joint 可測。
theorem measurable_logDeriv_convDensityAdd_gaussian_uncurry
    {pX : ℝ → ℝ} (hpX : Measurable pX) :
    Measurable (fun p : ℝ × ℝ =>
      logDeriv (EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 p.1.toNNReal)) p.2) := by
  sorry  -- @residual(plan:epi-case1-debruijn-producer-plan)

-- (4) 終結: :2041 が要求する t-側 AEStronglyMeasurable。Layer A+B+C 合成。
theorem aestronglyMeasurable_fisherInfo_t
    {pX : ℝ → ℝ} (hpX : Measurable pX) (T : ℝ) :
    AEStronglyMeasurable (fun t : ℝ =>
      (1 / 2) * (FisherInfoV2.fisherInfoOfDensity
        (EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 t.toNNReal))).toReal)
      (volume.restrict (Set.Ioc 0 T)) := by
  sorry  -- @residual(plan:epi-case1-debruijn-producer-plan)

end InformationTheory.Shannon.EPICase1ProducerMeasurability
```

---

## 付録: loogle negative results (negative も価値)

- `Continuous` + `ProbabilityTheory.gaussianPDFReal` → **Found 0** (Gaussian pdf の連続性 lemma が Mathlib に名前付きで不在; `measurable_gaussianPDFReal` は存在)。
- `measurable_deriv_with_param` の `ContinuousOn` 版 → **Found 0** (`section WithParam` 全 7 lemma が全域 `Continuous f.uncurry`)。
- (variance, point) 軸 gaussianPDFReal joint 可測 → **Found 0** (in-tree port は mean 軸のみ)。
