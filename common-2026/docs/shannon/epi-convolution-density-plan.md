# EPI convolution-density foundational brick サブ計画

**Status**: CLOSED ✅ — done (全 Phase 完了、`EPIConvolutionDensity.lean` 0 sorry に publish 済、Phase 2 riskiest も L-Conv-2 へ撤退せず無条件 discharge)。一般 EPI 自体は別ルート (route T) で 2026-06-08 無条件 closure 済、Blachman/Stam route は superseded。

> **Parent**: [`epi-moonshot-plan.md`](epi-moonshot-plan.md) (Blachman/Stam route to EPI)
> — この brick は **`IsStamScoreConvolution` (`EPIStamInequalityBody.lean:104`, 現状 `:= True`)
> を実体化する前段の foundational helper**。EPI 本体は discharge しない。
>
> **在庫 (code-grounded, 信頼可)**: [`epi-stam-blachman-discharge-inventory.md`](epi-stam-blachman-discharge-inventory.md)
> — 特に「Mathlib は `IndepFun.pdf_add_eq_lconvolution_pdf` (`Density.lean:356`) を持つが
> 結論は `=ᵐ[μ]` + `⋆ₗ` (lconvolution) で **微分可能性 lemma がゼロ** (loogle Found 0)」、
> 「`hasDerivAt_integral_of_dominated_loc_of_deriv_le` (`ParametricIntegral.lean:289`)、`condExp`、
> `condDistrib` は存在」。
>
> **Consumer (将来)**: `InformationTheory/Shannon/FisherInfoV2.lean` の
> `fisherInfoOfDensity (f : ℝ → ℝ) := ∫⁻ (logDeriv f)² · f` — 本 brick が出す密度 / score を
> このまま食わせられる shape にする。
>
> **新ファイル**: `InformationTheory/Shannon/EPIConvolutionDensity.lean` (新規, 0-sorry を狙う)。
>
> **Status (2026-05-20)**: 着手前。本 plan は計画のみ。proof-log: yes (Phase 2 lconvolution bridge は
> 失敗確率が高く判断ログ必須)。
>
> **実態整合 (2026-05-20): DONE-UNCOND (全 Phase 完了、0 sorry)** — `InformationTheory/Shannon/EPIConvolutionDensity.lean`
> (201 行、`InformationTheory.lean:227` で import 済) が全 deliverable を publish 済。Phase 1 `convDensityReal`
> (`:57`) / Phase 3 `hasDerivAt_convDensityReal` (`:79`、honest 解析仮定) / Phase 4 `logDeriv_convDensityReal`
> (`:108`) は計画通り。**Phase 2 (riskiest) は L-Conv-2 へ撤退せず無条件 discharge**:
> `pdf_add_toReal_ae_eq_convDensityReal` (`:180`、`IndepFun` 下で 0 sorry) + `convDensityReal_toReal_pdf_eq_lconvolution`
> (`:140`)。落とし穴 (b) (convolution-integrability wall) は `integral_toReal` を使い
> `ofReal_integral_eq_lintegral_ofReal` を回避することで side-step 済 (`:131-139` docstring 参照)。
> 撤退ライン用 named hyp `IsPdfAddConvDensityHyp` (`:124`) は `isPdfAddConvDensityHyp_of_indepFun` (`:194`)
> で無条件 discharge 済。下記「進捗」チェックボックスは全て完了扱い。

## 進捗

- [ ] Phase 0 — Mathlib + 既存足場 signature 再確認 (在庫の verbatim 固定) 📋 → [inventory](epi-stam-blachman-discharge-inventory.md)
- [ ] Phase 1 — `convDensityReal` 定義 + 純算術 unfold lemma (定義 + 正値性 helper) 📋
- [ ] Phase 3 — 積分記号下微分: `hasDerivAt_convDensityReal` (純 Mathlib calculus) 📋
- [ ] Phase 4 — `logDeriv_convDensityReal` score 表現 (純算術、Phase 3 依存) 📋
- [ ] Phase 2 — **lconvolution↔real bridge**: 和の密度 = `convDensityReal` (riskiest) 📋
- [ ] Phase 5 — skeleton 整地 + verify + `InformationTheory.lean` import + 親反映 📋

> **依存順 = Phase 1 → 3 → 4 → 2 → 5。** Phase 番号は親計画との対応を保つため非単調 (在庫の
> 自作要素番号 #1 が本 brick、その内部で純算術 3,4 を bridge 2 より先に埋める)。

## ゴール / Approach

### Goal (完成判定)

新ファイル `InformationTheory/Shannon/EPIConvolutionDensity.lean` で以下を publish。Phase 1,3,4 は
**0-sorry 確定 deliverable** (generic `(f, g)`)。Phase 2 (pdf-of-sum 同定) は **0-sorry を狙うが、
walls したら named hypothesis に縮退** (撤退ライン L-Conv-2)。

1. `convDensityReal (f g : ℝ → ℝ) : ℝ → ℝ := fun z => ∫ y, f (z - y) * g y ∂volume` — 点ごと実畳み込み。
2. **bridge** `pdf_add_toReal_ae_eq_convDensityReal`: `(pdf (X+Y) P volume ·).toReal`
   が a.e. `convDensityReal (pdfReal X) (pdfReal Y)` に等しい (出発 `IndepFun.pdf_add_eq_lconvolution_pdf`)。
3. **differentiability** `hasDerivAt_convDensityReal`: 明示的・誠実な正則性仮定下で
   `HasDerivAt (convDensityReal f g) (∫ y, deriv f (z - y) * g y ∂volume) z`。
4. **score** `logDeriv_convDensityReal`: 分母正値下で
   `logDeriv (convDensityReal f g) z = (∫ y, deriv f (z-y) * g y) / (∫ y, f (z-y) * g y)`。

### Approach (overall strategy / shape of solution)

**全体像** — 在庫が確認した致命的 shape ミスマッチ: Mathlib の和密度結論は **`=ᵐ` の a.e. 等式 +
`⋆ₗ` (lconvolution, ℝ≥0∞ 値, 微分可能性ゼロ)** だが、consumer (`fisherInfoOfDensity`) と Blachman
score は **点ごと微分可能な実値 `f` の `logDeriv`** を要求する。この gap を **2 つに分離**して攻める:

- **(A) 微分・score を generic `(f, g)` で先に証明する** (Phase 1,3,4)。ここは `lconvolution` を
  一切触らず、`convDensityReal f g z = ∫ y, f(z-y)·g(y)` を**自前の実積分定義として直接立て**、
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (積分記号下微分) と `logDeriv_apply`
  (`= deriv f / f`) の純算術だけで閉じる。`f, g` は任意の実関数なので、これは
  **lconvolution の有無と無関係に 0-sorry で立つ reusable brick**。
- **(B) その `convDensityReal` を pdf-of-sum に同定する** (Phase 2)。ここが唯一 `⋆ₗ` に触れる。
  `IndepFun.pdf_add_eq_lconvolution_pdf` の `pdf X ℙ μ ⋆ₗ[μ] pdf Y ℙ μ` を `.toReal` し、
  `lconvolution_def` (additive, `to_additive` 生成) で `∫⁻ y, pdf X y · pdf Y (-y+z) ∂volume` に展開、
  `ENNReal.toReal`↔`∫` 変換 (`integral_toReal` / `ofReal_integral_eq_lintegral_ofReal`,
  FisherInfoV2.lean:325 で実績) で `convDensityReal (pdfReal X) (pdfReal Y)` に着地させる。

**定義の shape 駆動** (CLAUDE.md「Mathlib-shape-driven Definitions」):
- consumer `fisherInfoOfDensity (f) = ∫⁻ (logDeriv f)²·f` は `logDeriv f` を直接取る ⇒
  `convDensityReal f g` は **実関数 `ℝ → ℝ`** で返す (ℝ≥0∞ ではない)。`logDeriv` / `deriv` /
  `HasDerivAt` がそのまま乗る。
- Phase 3 微分の積分記号下 lemma の結論は `HasDerivAt (fun z ↦ ∫ a, F z a ∂μ) (∫ a, F' x₀ a ∂μ) z`。
  これに合わせ `convDensityReal f g z := ∫ y, f (z - y) * g y` と **変数 `y` を `g` 側に固定**
  (`F z y := f(z-y)·g(y)`, `F' z y := deriv f (z-y)·g(y)`)。`z` 微分が `f(z-y)` だけに当たり
  `g(y)` が定数係数として残るので chain rule が `deriv f (z-y)·1` で素直に出る。

> **記法注意 (Mathlib 検証済)**: additive `lconvolution` は `mlconvolution` の `to_additive`。
> `mlconvolution f g μ x = ∫⁻ y, f y * g (y⁻¹ * x) ∂μ` (`LConvolution.lean:50`) なので加法版は
> `(f ⋆ₗ[μ] g) x = ∫⁻ y, f y * g (-y + x) ∂μ`。**変数順は `convDensityReal` (`f(z-y)·g(y)`) と逆**
> なので Phase 2 では `y ↦ z - y` の変数変換 (`integral_sub_left_eq_self` / `lintegral` の
> 平行移動不変性) を 1 段挟む。これを Phase 2 の最初の sub-step として明示する。

```
[generic brick: lconvolution に触れない]                  [pdf 同定: lconvolution に触れる]
  convDensityReal f g (def, Phase 1)                        IndepFun.pdf_add_eq_lconvolution_pdf
        │                                                          │ .toReal + lconvolution_def
  hasDerivAt_convDensityReal (Phase 3)                        ∫⁻ y, pdfX y · pdfY(-y+z)
        │                                                          │ 変数変換 y↦z-y
  logDeriv_convDensityReal (Phase 4)                          ∫⁻ y, pdfX(z-y) · pdfY y
        │                                                          │ toReal↔∫ 変換
        └──────────── reusable, 0-sorry ───────────► convDensityReal (pdfReal X)(pdfReal Y)
                                                          = pdf_add_toReal_ae_eq (Phase 2)
```

## Phase 詳細

### Phase 0 — signature 再確認 📋  (proof-log: no)

着手前に在庫の verbatim を Read で再固定 (`lake build` 不要)。確認対象:
- `IndepFun.pdf_add_eq_lconvolution_pdf` (`Density.lean:356`, 親は乗法 `pdf_mul_eq_mlconvolution_pdf`):
  `[SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ] [IsFiniteMeasure ℙ] (hXY : IndepFun X Y ℙ) :`
  `pdf (X + Y) ℙ μ =ᵐ[μ] pdf X ℙ μ ⋆ₗ[μ] pdf Y ℙ μ` (+ section `[AddGroup G] [MeasurableAdd₂ G]
  [MeasurableNeg G] [IsAddLeftInvariant μ]` = `ℝ`/`volume` で充足)。
- `mlconvolution` def (`LConvolution.lean:50`) + `mlconvolution_def` (`:69`) → additive 版の apply 形。
- `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (`ParametricIntegral.lean:289`) を**逐語**:
  ```
  (hs : s ∈ 𝓝 x₀) (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
  (hF_int : Integrable (F x₀) μ) {F' : 𝕜 → α → E} (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
  (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
  (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasDerivAt (F · a) (F' x a) x) :
  Integrable (F' x₀) μ ∧ HasDerivAt (fun n ↦ ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀
  ```
  type-class: `[RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]`
  (`ℝ` で全充足)、`[CompleteSpace E]` は本体場合分けで不要。
- `logDeriv_apply` / `logDeriv` (`Analysis/Calculus/LogDeriv.lean:34`): `logDeriv f x = deriv f x / f x`。
- `ofReal_integral_eq_lintegral_ofReal` (FisherInfoV2.lean:325 で実績), `MeasureTheory.integral_toReal`。

### Phase 1 — `convDensityReal` 定義 + helper 📋  (proof-log: no, **pure-Mathlib-calculus, 0-sorry**)

```lean
/-- Pointwise real convolution of two densities. -/
noncomputable def convDensityReal (f g : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ y, f (z - y) * g y ∂volume

theorem convDensityReal_def (f g : ℝ → ℝ) (z : ℝ) :
    convDensityReal f g z = ∫ y, f (z - y) * g y ∂volume := rfl
```

- 戦略: `rfl` のみ。`logDeriv` が乗るよう `ℝ → ℝ` 値で定義 (shape 駆動)。
- 正値性 helper (Phase 4 分母用、別 lemma):
  ```lean
  theorem convDensityReal_pos {f g : ℝ → ℝ} (z : ℝ)
      (hfg_int : Integrable (fun y => f (z - y) * g y) volume)
      (h_pos : 0 < ∫ y, f (z - y) * g y ∂volume) :
      0 < convDensityReal f g z
  ```
  戦略: `rw [convDensityReal_def]; exact h_pos` (1 行)。正値性は **積分が正という仮定を直に運ぶ**
  だけで証明しない (誠実な仮定; densities 一般では tail 条件が要るため Phase で自前証明しない)。

### Phase 3 — `hasDerivAt_convDensityReal` 📋  (proof-log: no, **pure-Mathlib-calculus, 0-sorry**)

```lean
theorem hasDerivAt_convDensityReal {f g : ℝ → ℝ} (z₀ : ℝ)
    (hf_diff : ∀ x, DifferentiableAt ℝ f x)
    (hF_meas : ∀ᶠ z in nhds z₀,
      AEStronglyMeasurable (fun y => f (z - y) * g y) volume)
    (hF_int : Integrable (fun y => f (z₀ - y) * g y) volume)
    (hF'_meas : AEStronglyMeasurable (fun y => deriv f (z₀ - y) * g y) volume)
    (bound : ℝ → ℝ) (hbound_int : Integrable bound volume)
    (h_bound : ∀ᵐ y ∂volume, ∀ z ∈ Metric.ball z₀ 1,
      ‖deriv f (z - y) * g y‖ ≤ bound y) :
    HasDerivAt (convDensityReal f g)
      (∫ y, deriv f (z₀ - y) * g y ∂volume) z₀
```

- 分類: **pure-Mathlib-calculus**。`lconvolution` を一切触らない。仮定は全て**誠実な解析仮定**
  (`:= True` pass-through ではない)。
- 戦略 (NAMING):
  1. `convDensityReal f g = fun z => ∫ y, F z y ∂volume` with `F z y := f (z - y) * g y`
     (`convDensityReal_def` で書換)。
  2. `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (`ParametricIntegral.lean:289`) を適用。
     - `hs := Metric.ball_mem_nhds z₀ one_pos` (`s := Metric.ball z₀ 1`)。
     - `h_diff`: 各 `y` で `HasDerivAt (fun z => f (z - y) * g y) (deriv f (z - y) * g y) z` を
       `((hf_diff (z-y)).hasDerivAt.comp_const_sub …).mul_const (g y)` 型の chain rule で構築。
       `z ↦ z - y` の derivative は 1 なので `HasDerivAt.comp` + `hasDerivAt_sub_const` で
       `deriv f (z-y) · 1 = deriv f (z-y)`、`*g y` は `HasDerivAt.mul_const`。
     - 残り (`hF_meas`, `hF_int`, `hF'_meas`, `h_bound`, `bound_integrable`) は仮定をそのまま渡す。
  3. 結論 conjunction の `.2` を取って `HasDerivAt (fun z ↦ ∫ y, F z y) (∫ y, F' z₀ y) z₀`。
- リスク: `comp_const_sub` 系の正確な lemma 名 (`HasDerivAt.comp_const_sub` or 手組み)。
  Phase 0 で loogle 確認 (`HasDerivAt (fun _ => _ (_ - _))`). 最悪 `HasDerivAt.comp` + `hasDerivAt_id.sub_const` で手組み (純算術, 数行)。

### Phase 4 — `logDeriv_convDensityReal` 📋  (proof-log: no, **pure-Mathlib-calculus, 0-sorry**)

```lean
theorem logDeriv_convDensityReal {f g : ℝ → ℝ} (z₀ : ℝ)
    (h_deriv : HasDerivAt (convDensityReal f g)
      (∫ y, deriv f (z₀ - y) * g y ∂volume) z₀)
    (h_pos : 0 < convDensityReal f g z₀) :
    logDeriv (convDensityReal f g) z₀
      = (∫ y, deriv f (z₀ - y) * g y ∂volume)
          / (∫ y, f (z₀ - y) * g y ∂volume)
```

- 分類: **pure-Mathlib-calculus**。Phase 3 を仮定 (`h_deriv`) として受け取り、`lconvolution` 不接触。
- 戦略 (NAMING):
  1. `logDeriv_apply`: `logDeriv F z₀ = deriv F z₀ / F z₀`。
  2. `deriv F z₀ = ∫ y, deriv f (z₀ - y) * g y` を `h_deriv.deriv` で固定。
  3. 分母 `convDensityReal f g z₀ = ∫ y, f (z₀ - y) * g y` を `convDensityReal_def` で書換。
     `h_pos` で `≠ 0` (`.ne'`) を出して `div` の well-defined を保証。
- これは completely 純算術 (3-5 行)。**Phase 3 を内部で再証明せず仮定として受ける**ことで
  Phase 3 の重い解析仮定束を logDeriv 側に持ち込まない (分離して再利用性を上げる)。

### Phase 2 — `pdf_add_toReal_ae_eq_convDensityReal` 📋  (proof-log: **yes**, **lconvolution-gap, riskiest**)

```lean
theorem pdf_add_toReal_ae_eq_convDensityReal
    {Ω : Type*} [MeasurableSpace Ω] {X Y : Ω → ℝ} {P : Measure Ω}
    [IsFiniteMeasure P] [HasPDF X P volume] [HasPDF Y P volume]
    (hXY : IndepFun X Y P) :
    (fun z => (pdf (X + Y) P volume z).toReal)
      =ᵐ[volume] convDensityReal
        (fun x => (pdf X P volume x).toReal)
        (fun y => (pdf Y P volume y).toReal)
```

- 分類: **lconvolution-gap**。**唯一 `⋆ₗ` に触れる lemma で、本 brick で最もリスクが高い**。
- 戦略 (NAMING, 4 sub-step):
  1. `IndepFun.pdf_add_eq_lconvolution_pdf hXY` で
     `pdf (X+Y) P volume =ᵐ pdf X P volume ⋆ₗ[volume] pdf Y P volume` を得る。両辺 `.toReal` を
     `Filter.EventuallyEq.fun_comp` (or `.toReal` の congr) で運ぶ。
  2. additive `lconvolution_def` (= `mlconvolution_def` の `to_additive`, `LConvolution.lean:69`):
     `(pdfX ⋆ₗ[volume] pdfY) z = ∫⁻ y, pdfX y * pdfY (-y + z) ∂volume`。
  3. **変数変換** `y ↦ z - y` (lintegral 平行移動不変, `lintegral_sub_left_eq_self` / `Measure.lintegral_comp`):
     `∫⁻ y, pdfX y * pdfY (-y+z) = ∫⁻ y, pdfX (z-y) * pdfY y`。← Approach の「変数順逆」を吸収する step。
  4. `ENNReal.toReal`↔`∫` 変換: `ENNReal.toReal (∫⁻ y, ofReal(pdfXreal(z-y)) * ofReal(pdfYreal y))`
     → `pdfReal` の非負性 (`ENNReal.toReal_ofReal`, `.toReal` of pdf は ofReal of toReal a.e.) +
     `ofReal_integral_eq_lintegral_ofReal` (FisherInfoV2.lean:325 既実績) で
     `∫ y, pdfXreal(z-y) * pdfYreal y = convDensityReal pdfXreal pdfYreal z`。
- 既知の落とし穴 (判断ログに記録):
  - **(a)** `pdf · |>.toReal` と `ofReal (pdf ·).toReal` の往復: `pdf` は `ℝ≥0∞` 値で a.e. 有限とは
    限らないが `HasPDF` 下で `lintegral pdf = 1` から a.e. `< ∞`、`ENNReal.ofReal_toReal` の
    `≠ ∞` 仮定を a.e. で出す必要。`pdf` の `lintegral_eq_one` / `HasPDF` 系で確保。
  - **(b)** step 4 の `ofReal_integral_eq_lintegral_ofReal` は **被積分関数の Integrable + 非負 a.e.**
    を要求。Integrable は `pdf` が L¹ (確率密度) であることから出すが、**畳み込み積の Integrable は
    Fubini/Young が要り得る** — ここが最大の wall 候補。詰まったら撤退ライン L-Conv-2 (下記)。
  - **(c)** `MeasurableNeg ℝ` / `IsAddLeftInvariant volume` などの section instance が `ℝ`/`volume`
    で自動 derive されるか Phase 0 で確認 (在庫は充足と記すが instance search 実走で再確認)。

### Phase 5 — 整地 + verify + 反映 📋  (proof-log: no)

- skeleton-driven: Phase 1 → 3 → 4 → 2 の順で 1 sorry ずつ。各 fill 後 `lake env lean
  InformationTheory/Shannon/EPIConvolutionDensity.lean` が silent。
- import (pinpoint, `import Mathlib` 禁止):
  ```
  import InformationTheory.Shannon.FisherInfoV2
  import Mathlib.Probability.Density
  import Mathlib.Probability.Independence.Basic
  import Mathlib.Analysis.LConvolution
  import Mathlib.Analysis.Calculus.ParametricIntegral
  import Mathlib.Analysis.Calculus.LogDeriv
  ```
- `InformationTheory.lean` に `import InformationTheory.Shannon.EPIConvolutionDensity` 1 行追加。
- 親 `epi-moonshot-plan.md` の Blachman 節に「conv-density brick 完成、`IsStamScoreConvolution`
  実体化の前提整地」を判断ログで反映 (本 plan は親本文を編集しない、append-only ログのみ)。

## 撤退ライン

- **L-Conv-1 (採用想定)**: 微分・score を **generic `(f, g)`** で立て (Phase 1,3,4)、
  `convDensityReal` を **自前実積分定義**として持つ。`lconvolution` の微分可能性ゼロ問題を
  「微分は generic 実積分で証明、lconvolution は同定 (Phase 2) のみで使う」と分離して回避。
  → これにより Phase 1,3,4 は lconvolution の状況に依らず **0-sorry 確定**。
- **L-Conv-2 (Phase 2 wall 時の段階的撤退)**: Phase 2 の `ofReal_integral_eq_lintegral_ofReal`
  Integrable 充足 (落とし穴 b) や a.e.-finite (落とし穴 a) で詰んだら、Phase 2 を
  **named hypothesis** に縮退:
  ```lean
  /-- 和の密度が `convDensityReal` の `.toReal` 表現に一致する、という橋を仮定として外出し。 -/
  def IsPdfAddConvDensityHyp {Ω} [MeasurableSpace Ω] (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
    (fun z => (pdf (X + Y) P volume z).toReal)
      =ᵐ[volume] convDensityReal (fun x => (pdf X P volume x).toReal)
                                  (fun y => (pdf Y P volume y).toReal)
  ```
  これを consumer に渡す形で publish。**Phase 1,3,4 (generic brick) は撤退しても 0-sorry の
  reusable deliverable として独立に立つ** (pdf-of-sum 同定は named hyp に deferred)。
  この場合ファイルは「Phase 2 のみ 1 named hypothesis、他 0-sorry」で着地。
- **L-Conv-3 (未採用、最終手段)**: generic `(f, g)` の Integrable / 正値性まで仮定で外出しし、
  `convDensityReal` の存在性自体を予測子化 — 採らない (誠実な解析仮定で立つ見込みのため)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!--
記録予定 (着手後):
- Phase 2 の落とし穴 (a)(b)(c) のどれが発火したか、L-Conv-2 へ撤退したか否か。
- Phase 3 の `comp_const_sub` 系 lemma 名が Mathlib に在ったか手組みだったか。
- `convDensityReal` の変数順 (`f(z-y)·g(y)`) が consumer / Phase 2 変数変換とどう噛んだか。
-->
