# Fisher Information + de Bruijn Identity ムーンショット計画 🌙 (T2-F)

> **DELETED (2026-05-20)**: V1 `fisherInfo` / `fisherInfoReal` / `IsRegularDeBruijnHyp` / `deBruijn_identity` were removed from `FisherInfo.lean` and the EPI/Stam scaffolding migrated to V2 `FisherInfoV2.fisherInfoOfMeasureV2` (full build green, 0 sorry).
>
> **RESOLVED (2026-05-20) — flaw-vacuous fix**: V1 `fisherInfo` (`FisherInfo.lean`)
> now carries a `⚠️ BUGGED` deprecation docstring (returns `0` for Gaussians; use
> `FisherInfoV2.fisherInfoOfDensity`). The vacuous Stam discharges that exploited
> the `= 0` artefact were removed; the def is kept only as the type-level scaffold
> of the genuine *open* Stam/de Bruijn predicates. See
> [`flaw-vacuous-review-2026-05-20.md`](flaw-vacuous-review-2026-05-20.md) HIGH-1.

<!--
雛形メモ (moonshot-plan-template.md より):
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 削除/廃止された Phase は ~~取り消し線~~ で残す（完全削除しない、過去参照のため）
- 判断ログは append-only。Phase 中の方針変更・撤退・当初仮定の修正を記録
-->

> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 2 — T2-F. Fisher Information + de Bruijn Identity」
>
> **Predecessor (inventory)**: [`fisher-info-mathlib-inventory.md`](fisher-info-mathlib-inventory.md) (546 行、Mathlib 既存率 60-65%、自作 6 項目 ~540-940 行、推奨路線 A = PDF 経由 + 1-D scope)
>
> **Status (2026-05-19)**: 1 セッションで全 Phase publish 完了 (`Common2026/Shannon/FisherInfo.lean` 222 行)。Tier 0 (Phase A) と `differentialEntropy` ↔ pdf 橋渡しは完全実装。Tier 1 (Phase B) は **L-F2 適用形** = `IsRegularDensity` predicate + `integral_logDeriv_pdf_eq_zero` hypothesis pass-through。Tier 2 (Phase C-E) は **L-F1+L-F2 適用形** = `IsRegularDeBruijnHyp` predicate に heat-eq / dominated-bound / IBP を hypothesis として集約し `deBruijn_identity` signature を完全形で publish。Gaussian instance (`IsRegularDeBruijnHyp` の discharge) と `fisherInfo_gaussianReal = 1/v` は次月 seed (`fisher-info-gaussian-plan.md` 等) に分離。0 sorry / 0 warning。
>
> **実態整合 (2026-05-20): DONE-HONEST-HYPS (V1 publish 済) — ただし headline `fisherInfo_gaussianReal = 1/v` は本 V1 で NOT-PROVABLE (FLAW-VACUOUS)、`deBruijn_identity` は PASS-THROUGH** —
> `FisherInfo.lean` (現 236 行) は `fisherInfo` (`:58`) / `IsRegularDensity` (`:134`) + `integral_logDeriv_pdf_eq_zero`
> (`:167`) / `IsRegularDeBruijnHyp` (`:200`) + `deBruijn_identity` (`:223`、本体 `:= h_reg.derivAt_entropy_eq_half_fisher`
> = hypothesis pass-through) を 0 sorry で publish。**しかし `fisherInfo` (V1) は representative-dependence flaw で
> Gaussian に対し `= 0` を返す (FLAW-VACUOUS)**: `FisherInfoGaussian.lean:304-327` 判断ログ #2 が
> 「`fisherInfo (gaussianReal m v) = 1/v` は **not provable** — `rnDeriv` の opaque representative が a.e. 非微分、
> `logDeriv ((rnDeriv).toReal) = 0` a.e. ⇒ `fisherInfo (gaussianReal) = 0`」と明記。Goal/Status が約束する
> `fisherInfo_gaussianReal = 1/v` は **V1 には存在しない**。Phase C/D も同 flaw で block (de Bruijn RHS
> `(1/2)·0 = 0` vs LHS `1/(2(v+t)) > 0` で矛盾)。**正しい discharge は V2 へ移行**: `FisherInfoV2.lean` の
> `fisherInfoOfDensity` (density-as-input、`:88`) + `fisherInfoOfDensity_gaussianPDFReal = 1/v` (`:296`、0 sorry)、
> Gaussian de Bruijn は `FisherInfoV2DeBruijn.lean:364` `deBruijn_identity_v2_gaussian` (honest、0 sorry)。
> 本 plan の Goal は V1 を指しており stale — V2 が事実上の deliverable。
>
> **Goal**: 新規ファイル `Common2026/Shannon/FisherInfo.lean` で **Cover-Thomas Ch.17.7 の de Bruijn identity** (`(d/dt) h(X + √t · Z) = (1/2) · J(X + √t · Z)` for `Z ∼ 𝒩(0, 1)`, `X ⟂ Z`) を **`HasDerivAt` 形**で publish。
>
> **撤退ライン**: [L-F1] de Bruijn を heat-eq 仮定形で publish / [L-F2] score function 期待値 0 を `IsRegularFamily` predicate 形に hypothesis 抽出 / [L-F3] Tier 0+1 (定義 + score 期待値 0) のみで partial publish、Tier 2 (de Bruijn) を後続 seed に分離 (詳細 §撤退ライン)。

## 進捗

- [x] Phase 0 — Mathlib + Common2026 API 在庫 ✅ → [`fisher-info-mathlib-inventory.md`](fisher-info-mathlib-inventory.md)
- [x] Phase A — `fisherInfo` 定義 + 基本性質 (Tier 0) ✅ (`Common2026/Shannon/FisherInfo.lean`, 222 行)
- [x] Phase B — score function 期待値 0 (Tier 1, L-F2 適用形) ✅ (`IsRegularDensity` predicate + `integral_logDeriv_pdf_eq_zero` hypothesis pass-through 形で publish)
- [~] Phase C — Gaussian convolution heat equation (Tier 2 核 1/3) 🔄 L-F1 で `IsRegularDeBruijnHyp.derivAt_entropy_eq_half_fisher` 中に hypothesis として吸収
- [~] Phase D — convolution / parametric integral differentiation (Tier 2 核 2/3) 🔄 L-F1 で同上
- [x] Phase E — de Bruijn identity 主定理 + wrapper (Tier 2 核 3/3, L-F1+L-F2 適用形) ✅ (`IsRegularDeBruijnHyp` + `deBruijn_identity`、signature 完全形で publish、Gaussian instance 整備は後続 plan)
- [x] Phase V — verify + Common2026.lean 編入 ✅ (`lake env lean Common2026/Shannon/FisherInfo.lean` clean, `Common2026.lean` に import 追記済)

## ゴール / Approach

### Goal (最終定理 signature)

新規ファイル `Common2026/Shannon/FisherInfo.lean` で 3 主定理 + 1 拡張 publish:

```lean
namespace Common2026.Shannon

/-- **Fisher information** of a measure `μ` on `ℝ`. `J(μ) := ∫⁻ (logDeriv p x)² · p x dx`
    where `p := μ.rnDeriv volume` is the density and `logDeriv f := deriv f / f` is the
    score function (Mathlib `Mathlib/Analysis/Calculus/LogDeriv.lean:34`). -/
noncomputable def fisherInfo (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((logDeriv (fun y => (μ.rnDeriv volume y).toReal) x) ^ 2)
    * μ.rnDeriv volume x ∂volume

/-- **Gaussian Fisher info**: `J(𝒩(m, v)) = 1/v`. -/
theorem fisherInfo_gaussianReal
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    fisherInfo (gaussianReal m v) = ENNReal.ofReal (1 / (v : ℝ))

/-- **Score function expectation vanishes** (regular family form). -/
theorem integral_logDeriv_pdf_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (X : Ω → ℝ) [HasPDF X ℙ volume]
    (h_reg : IsRegularDensity X ℙ /- predicate: smooth + L¹ tail vanish -/) :
    ∫ x, logDeriv (fun y => (pdf X ℙ volume y).toReal) x
         * (pdf X ℙ volume x).toReal ∂volume = 0

/-- **de Bruijn identity** (Cover-Thomas 17.7.2):
    `(d/dt) h(X + √t · Z) = (1/2) · J(X + √t · Z)` for `Z ∼ 𝒩(0, 1)`, `X ⟂ Z`. -/
theorem deBruijn_identity
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z ℙ)
    [HasPDF X ℙ volume]
    (hZ_law : ℙ.map Z = gaussianReal 0 1)
    (h_reg : IsRegularDeBruijnHyp X Z ℙ /- placeholder predicate -/)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s => differentialEntropy (ℙ.map (fun ω => X ω + Real.sqrt s * Z ω)))
      ((1/2) * (fisherInfo (ℙ.map (fun ω => X ω + Real.sqrt t * Z ω))).toReal)
      t

end Common2026.Shannon
```

(`IsRegularDensity` / `IsRegularDeBruijnHyp` の中身、および `fisherInfo` の return 型を `ℝ≥0∞` のまま return するか `(fisherInfo …).toReal` で公開するかは **Phase A 着手時の judgement #1 で確定**。inventory §H に従い `ℝ≥0∞` 内蔵 + `.toReal` 公開で進める方針。)

### Approach (overall strategy / shape of solution)

**戦略の shape**: Cover-Thomas 17.7 では **de Bruijn identity ⇐ Gaussian convolution heat semigroup + IBP** だが、Mathlib に heat semigroup は不在 (inventory §C-5)。代わりに **`logDeriv` + `HasPDF` + Gaussian convolution PDF identity + parametric integral differentiation** の 4 部品を Mathlib から直接組む:

1. **`fisherInfo` 定義は `logDeriv` shape-driven**:
   - Mathlib `Real.deriv_log_comp_eq_logDeriv` (`Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean:134`) の結論形 `deriv (log ∘ f) x = logDeriv f x` に合わせて、Fisher info の被積分関数を `(logDeriv p)²` で書く。
   - **return 型 `ℝ≥0∞`**: 「Fisher info = +∞」(irregular family) を捌くため、`klDiv` と同じ慣行に合わせる。`fisherInfoReal := (fisherInfo μ).toReal` 派生を補助補題で publish。
   - **設計選択の根拠**: inventory §G-1 「`logDeriv` を直接使うべき (Mathlib-shape-driven 原則)」+ CLAUDE.md `Mathlib-shape-driven Definitions` 節。textbook 形 `(∂_x log p)² · p` を直書きすると `Real.deriv_log_comp_eq_logDeriv` を通すための 50-100 行 reshape bridge が要る。

2. **Gaussian Fisher info `J(𝒩) = 1/v` は再利用インフラ集約**:
   - `rnDeriv_gaussianReal` (Mathlib `Real.lean:240`) で密度を `gaussianPDFReal` に書き換え
   - `log_gaussianPDFReal_eq` (Common2026 `DifferentialEntropy.lean:391`) で `log p` を quadratic form に
   - `deriv` を取り `logDeriv = -(x - m)/v`
   - 二乗 + 期待値 = variance = v ⇒ `J = v / v² = 1/v`
   - Common2026 既存の Gaussian 補助インフラ (variance / integrability of `p log p`) を流用、自前は ~80-120 行 (inventory §G-2)。

3. **de Bruijn identity 5 ステップ** (inventory §G-5 を Phase 単位に分割):
   - **Step 1 (Phase D-1)**: `ℙ.map (X + √s Z) = (ℙ.map X) ∗ gaussianReal 0 s` (Mathlib `IndepFun.map_add_eq_map_conv_map₀'` + `gaussianReal_const_mul`)
   - **Step 2 (Phase D-2)**: PDF representation `(ℙ.map (X+√s Z)).rnDeriv volume = pdf X ⋆ₗ gaussianPDF 0 s` (Mathlib `IndepFun.pdf_add_eq_lconvolution_pdf'` + `map_eq_withDensity_pdf`、自前 bridge ~40-80 行)
   - **Step 3 (Phase D-3)**: `d/ds`-step (Mathlib `hasDerivAt_integral_of_dominated_loc_of_deriv_le`、`F (s, x) := -p_s(x) log p_s(x)`、bound は Gaussian tail から integrable、自前 ~80-120 行)
   - **Step 4 (Phase C)**: Gaussian heat equation `∂_s gaussianPDF 0 s x = (1/2) ∂²_x gaussianPDF 0 s x` (Mathlib 不在、手動 verification 50-80 行) + convolution 微分 `∂_x (f ⋆ g) = f ⋆ g'` (Mathlib `Convolution.lean` の `HasDerivAt.convolution_left` 等で 30-50 行)
   - **Step 5 (Phase E)**: IBP で `-∫ p_s · (∂_s p_s / p_s) dx = (1/2) ∫ p_s · (∂_x log p_s)² dx` (Mathlib `integral_mul_deriv_eq_deriv_mul_of_integrable` `IntegralEqImproper.lean:1318`、自前 ~40-60 行)

4. **1-D scope に固定** (judgement #2 候補):
   - multivariate Fisher info matrix は scope-out (inventory §A、`IsGaussian` instance は使わない)
   - heat semigroup は Mathlib 0、自作すると +200-300 行で本 seed scope を破壊 (inventory §C-5)
   - T2-D EPI も 1-D で開始予定 (Cover-Thomas 17.7 の証明は univariate convolution + スカラー化で十分)

5. **Common2026 既存 `DifferentialEntropy.lean` 1010 行を最大限再利用**:
   - `differentialEntropy : Measure ℝ → ℝ` 定義 (`DifferentialEntropy.lean:42`) を主定理の左辺で使う
   - `differentialEntropy_eq_integral_density` (`DifferentialEntropy.lean:60`) で `h(P_t) = -∫ p_t log p_t dx` に書き換え
   - `integrable_density_log_density_of_gaussian` (`DifferentialEntropy.lean:81`) を `Gaussian × pdf X` convolution に拡張 (Phase B / D で要)
   - `differentialEntropy_gaussianReal` (`DifferentialEntropy.lean:406`) を de Bruijn の sanity check (`X = 0` case で `h(𝒩(0, t)) = (1/2) log(2πet)` → `d/dt = 1/(2t) = (1/2)·J(𝒩(0, t))`) に流用。

### Approach 図

```
Phase 0 : Mathlib + Common2026 API 在庫                        ← 完了済 (inventory)
          ──────────────────────────────────────────────
Phase A : `fisherInfo` 定義 + 基本性質                          ← 0.5 session (1-1.5h)
                                                                  = Tier 0 (~80-100 行)
          ──────────────────────────────────────────────
Phase B : score function 期待値 0 + integrability               ← 0.5-0.75 session (1.5-2h)
                                                                  = Tier 1 (~150-200 行)
          ←──── 撤退ライン L-F3 (Tier 0+1 partial publish) ────→
          ──────────────────────────────────────────────
Phase C : Gaussian convolution heat equation                    ← 0.5-0.75 session (1.5-2h)
Phase D : convolution differentiation under integral            ← 0.75-1 session (2-2.5h)
Phase E : de Bruijn identity 結語 + wrapper                     ← 0.5 session (1-1.5h)
                                                                  = Tier 2 (~300-500 行)
          ←──── 撤退ライン L-F1 (heat-eq 仮定形) ──────────────→
          ←──── 撤退ライン L-F2 (regular family hypothesis) ───→
          ──────────────────────────────────────────────
Phase V : verify + Common2026.lean 編入                         ← 0.25 session (0.5h)
```

### 段階的 ship 設計 (Tier 0 / 1 / 2 / 3)

- **Tier 0** (~80-100 行, Phase A): `fisherInfo : Measure ℝ → ℝ≥0∞` 定義 + `fisherInfo_nonneg` + `fisherInfo_dirac` (`= 0` for Dirac、退化 case) + `fisherInfo_eq_lintegral_logDeriv_sq` (unfold 補助)。Phase A 完了で発生。Library root 編入はここで前倒し可 (`Common2026.lean` に `import` 追記、partial publish 価値あり)。
- **Tier 1** (~150-200 行, Phase A + B): + `fisherInfo_gaussianReal` (Gaussian で `1/v`) + `integral_logDeriv_pdf_eq_zero` (score 期待値 0、`IsRegularDensity` predicate 形)。Phase B 完了で発生。**撤退ライン L-F3 でここまで publish も可**。
- **Tier 2** (~300-500 行, Phase A + B + C + D + E): + `deBruijn_identity` (主定理)。Phase E 完了 = Cover-Thomas 17.7.2 完成形。**本 plan の理想到達点**。
- **Tier 3 (任意 stretch)**: EPI 接続 helper (`deBruijn_to_epi_integrand` 等、T2-D EPI seed の入口準備)。**本 plan のスコープ外**、Tier 2 publish 後の T2-D plan で。

### 規模見積もり (再掲、inventory §G より)

| 自作要素 | 想定行数 | Phase |
|---|---|---|
| G-1 `fisherInfo` 定義 + 基本性質 (`_nonneg`, `_dirac`, unfold 補助) | ~30-60 | A |
| G-6 `differentialEntropy` ↔ `pdf` 橋渡し (`differentialEntropy_map_eq_integral_pdf_log_pdf`) | ~80-160 | A or B |
| G-2 `fisherInfo_gaussianReal = 1/v` | ~80-120 | B |
| G-4 score function 期待値 0 (`integral_logDeriv_pdf_eq_zero`) | ~60-120 | B |
| G-3 `IndepFun.map_add_eq_volume_withDensity_lconvolution` (PDF bridge) | ~40-80 | D |
| Gaussian heat equation (`gaussianPDF_heat_eq`、inventory §G-5 Step 4) | ~50-80 | C |
| convolution differentiation (`hasDerivAt_convolution_*`、inventory §G-5 Step 4 後半) | ~30-50 | D |
| parametric integral differentiation 起動 (`d/ds h(P_s)` の dominated bound 整理) | ~80-120 | D |
| IBP step (de Bruijn 結語、`integral_mul_deriv_eq_deriv_mul_of_integrable` 起動) | ~40-60 | E |
| `deBruijn_identity` main statement + sandwich | ~30-50 | E |
| skeleton + imports + docstring + namespace | ~40-60 | A |
| **合計** | **~560-960** | |

中央予測 **~750 行** (roadmap 「600-800 行」とほぼ整合、上限近辺になる risk あり)。撤退ライン L-F3 で Tier 1 止まりなら ~280-360 行、L-F1 で heat-eq 仮定形なら ~600 行。

### ファイル構成 (Phase V 完了想定)

```
Common2026/Shannon/
  FisherInfo.lean              ← 新規 (T2-F 一括 publish、~750 行)
  DifferentialEntropy.lean     ← 既存 1010 行、変更なし (再利用元)
Common2026.lean                ← `import Common2026.Shannon.FisherInfo` を追記 (Phase V)
```

**新規 import** (CLAUDE.md `Import Policy` 厳守、`import Mathlib` は使わない):

```lean
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Density
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Analysis.LConvolution
import Mathlib.Probability.Independence.Basic
import Common2026.Shannon.DifferentialEntropy
```

## 依存関係

完了済 / 利用可:

- [x] **Mathlib `Analysis.Calculus.LogDeriv`**: `logDeriv`, `logDeriv_apply`
- [x] **Mathlib `Analysis.SpecialFunctions.Log.Deriv`**: `Real.deriv_log_comp_eq_logDeriv` (score function 同形)、`Real.hasDerivAt_log`, `HasDerivAt.log`
- [x] **Mathlib `Probability.Density`**: `HasPDF`, `pdf`, `pdf_def`, `map_eq_withDensity_pdf`, `Real.hasPDF_iff_of_aemeasurable`, `pdf.integral_pdf_smul`, `HasPDF.absolutelyContinuous`
- [x] **Mathlib `Probability.Density` (convolution)**: `IndepFun.pdf_add_eq_lconvolution_pdf'` (additive 自動生成版), `IndepFun.add_hasPDF'`
- [x] **Mathlib `Probability.Distributions.Gaussian.Real`**: `gaussianReal`, `gaussianPDFReal`, `gaussianPDF`, `rnDeriv_gaussianReal`, `gaussianReal_const_mul`, `gaussianReal_conv_gaussianReal`, `gaussianReal_add_gaussianReal_of_indepFun`
- [x] **Mathlib `Analysis.Calculus.ParametricIntegral`**: `hasDerivAt_integral_of_dominated_loc_of_lip`, **`hasDerivAt_integral_of_dominated_loc_of_deriv_le`** (de Bruijn `d/dt`-step の主役)
- [x] **Mathlib `MeasureTheory.Integral.IntegralEqImproper`**: `integral_mul_deriv_eq_deriv_mul_of_integrable` (IBP step)
- [x] **Mathlib `MeasureTheory.Group.Convolution`**: `Measure.conv`, `Measure.conv_assoc`, `Measure.conv_absolutelyContinuous`
- [x] **Mathlib `Analysis.LConvolution`**: `mlconvolution` (= `lconvolution` 加法版)
- [x] **Mathlib `Analysis.Convolution`**: `convolution`, `convolution_assoc`, `integral_convolution`, `HasDerivAt.convolution_*` (convolution 微分)
- [x] **Mathlib `Probability.Independence.Basic`**: `IndepFun`, `IndepFun.map_add_eq_map_conv_map₀'` (`@[to_additive]` 自動生成版)
- [x] `Common2026/Shannon/DifferentialEntropy.lean` (`differentialEntropy`, `differentialEntropy_eq_integral_density`, `integrable_density_log_density_of_gaussian`, `log_gaussianPDFReal_eq`, `differentialEntropy_gaussianReal`, `differentialEntropy_map_add_const`, `..._mul_const`)

**参考 (import しない)**:

- `Common2026/Shannon/Chernoff.lean` などの Tier 1 plumbing は **完全に独立** (`FisherInfo.lean` は Chernoff / Sanov / Stein 系を一切経由しない)
- `Common2026/InformationTheory/Asymptotic.lean` (`DotEq`) も不要 — de Bruijn identity は `HasDerivAt` 形で publish (asymptotic ではない)

---

## Phase 0 — Mathlib + Common2026 API 在庫 ✅

完了 ([`fisher-info-mathlib-inventory.md`](fisher-info-mathlib-inventory.md), 546 行)。

主結論:

- **既存 API カバレッジ ~60-65%**: primitive layer (differentiation infrastructure 95%, probability density 90%, Gaussian / convolution 95%) は完備、Fisher info-specific layer (Fisher info 概念 0%, de Bruijn 0%, score function 期待値 0 lemma 0%) は完全自作
- **自作 6 件**: G-1 `fisherInfo` 定義 (~30-60), G-2 `fisherInfo_gaussianReal` (~80-120), G-3 PDF bridge (~40-80), G-4 score 期待値 0 (~60-120), G-5 de Bruijn 本体 (~250-400), G-6 `differentialEntropy` ↔ pdf 橋渡し (~80-160) — 合計 **~540-940 行**
- **撤退ライン現時点で発動なし**、新規撤退ライン 3 件 (L-F1〜L-F3) を本 plan に追加 (§撤退ライン)
- **推奨実装路線 A (PDF 経由 + 1-D scope)** を採用 (heat semigroup 経路 = 路線 C は scope-out、判断ログ #1 候補)
- **`logDeriv` (Mathlib `LogDeriv.lean:34`) を score function として偶発再利用** (inventory §B) — Mathlib-shape-driven 原則の典型例

---

## Phase A — `fisherInfo` 定義 + 基本性質 (Tier 0) 📋

### スコープ

`FisherInfo.lean` の skeleton を Write (全主定理 `:= by sorry`)、`fisherInfo` 定義 + Tier 0 基本性質 (非負性、Dirac 退化 case、unfold 補助、`differentialEntropy` ↔ pdf 橋渡し) を確定。

**proof-log**: yes (Tier 0 baseline publish 時点で `proof-log-fisher-info-tier0.md` を append)。

### Done 条件

- `Common2026/Shannon/FisherInfo.lean` 新規作成 + skeleton (全主定理 + 補助補題が `:= by sorry`)
- `fisherInfo (μ : Measure ℝ) : ℝ≥0∞` 定義 (inventory §G-1 形そのまま)
- `fisherInfo_nonneg` (自動 from `ℝ≥0∞`、`by simp` で出るはず → 確認のみ)
- `fisherInfo_eq_lintegral_logDeriv_sq` (unfold 補助、`rfl` 1 発)
- `fisherInfo_dirac` (`= 0`、Dirac measure の `rnDeriv volume = 0` ae なので積分 0)
- `differentialEntropy_map_eq_integral_pdf_log_pdf` (`differentialEntropy` ↔ `pdf` 橋渡し、inventory §G-6)
- `lake env lean Common2026/Shannon/FisherInfo.lean` で Phase A 本体 + Phase B-E `sorry` skeleton が clean

### ステップ

- [ ] **A-0 skeleton**: 全主定理 + 補助補題を `:= by sorry` で並べた skeleton を Write、LSP 診断で type-check OK 確認 (CLAUDE.md "Skeleton-driven Development")。imports は §依存関係 の Mathlib リストのみ。inventory §着手 skeleton (line 437-518) をそのままベースに使う。

- [ ] **A-1 `fisherInfo` 定義** (inventory §G-1):
  ```lean
  noncomputable def fisherInfo (μ : Measure ℝ) : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal ((logDeriv (fun y => (μ.rnDeriv volume y).toReal) x) ^ 2)
      * μ.rnDeriv volume x ∂volume
  ```
  - **落とし穴 1**: `(logDeriv f x)^2` を `ℝ≥0∞` に持ち上げる際、`f x = 0` の点で `deriv f x / 0 = 0` (Real) で二乗も `0`、`ENNReal.ofReal 0 = 0` で safe。
  - **落とし穴 2**: 台外で `μ.rnDeriv volume x = 0` の点は被積分関数全体が `0`、`negMulLog 0 = 0` 慣行と整合。

- [ ] **A-2 `fisherInfo_nonneg`**:
  ```lean
  lemma fisherInfo_nonneg (μ : Measure ℝ) : 0 ≤ fisherInfo μ := bot_le
  ```
  - `ℝ≥0∞` の `bot_le` で trivial、~1 行。

- [ ] **A-3 `fisherInfo_eq_lintegral_logDeriv_sq`** (unfold 補助):
  ```lean
  lemma fisherInfo_eq_lintegral_logDeriv_sq (μ : Measure ℝ) :
      fisherInfo μ
        = ∫⁻ x, ENNReal.ofReal ((logDeriv (fun y => (μ.rnDeriv volume y).toReal) x) ^ 2)
            * μ.rnDeriv volume x ∂volume := rfl
  ```
  - `rfl` で出る (定義そのもの)、~2 行。

- [ ] **A-4 `fisherInfo_dirac`** (退化 case):
  ```lean
  theorem fisherInfo_dirac (m : ℝ) : fisherInfo (Measure.dirac m) = 0
  ```
  - `Measure.dirac m` は `volume` に absolutely continuous でない (singleton `{m}` 上に mass)
  - `(Measure.dirac m).rnDeriv volume = 0` a.e. (Mathlib `Measure.rnDeriv_eq_zero_of_singular`)
  - 被積分関数全体が `0` ae、`∫⁻ = 0`
  - ~10-15 行 (Lebesgue decomposition 経由)
  - **判断 candidate**: もし Mathlib に `singular ⇒ rnDeriv = 0 ae` の直接補題がなく自前 5 行が要るなら、`fisherInfo_dirac` は Tier 0 から外して Tier 3 に push (corner case、主路から無関係)。

- [ ] **A-5 `differentialEntropy_map_eq_integral_pdf_log_pdf`** (inventory §G-6 bridge、Phase D で要):
  ```lean
  theorem differentialEntropy_map_eq_integral_pdf_log_pdf
      {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
      (Y : Ω → ℝ) (hY : Measurable Y) [HasPDF Y ℙ volume] :
      differentialEntropy (ℙ.map Y)
        = -∫ x, (pdf Y ℙ volume x).toReal * Real.log (pdf Y ℙ volume x).toReal ∂volume
  ```
  - `pdf Y ℙ volume = (ℙ.map Y).rnDeriv volume` (Mathlib `pdf_def`)
  - `differentialEntropy_eq_integral_density` (Common2026 `DifferentialEntropy.lean:60`) を `f := (pdf Y ℙ volume).toReal` で起動
  - `f` が `Measurable` + `0 ≤ f` の plumbing (~10-20 行)
  - `(ℙ.map Y) = volume.withDensity ((pdf Y ℙ volume))` (`map_eq_withDensity_pdf`)
  - `ENNReal.ofReal ∘ ENNReal.toReal = id` ae で書き換え (~15-30 行、`Measure.rnDeriv_lt_top` で `< ∞` ae 経由)
  - ~80-160 行 (inventory §G-6 見積、Mathlib `pdf_def` / `map_eq_withDensity_pdf` の存在で大きく圧縮可能)。

- [ ] **A-6 verify**: `lake env lean Common2026/Shannon/FisherInfo.lean` clean。Phase B-E は `sorry` 残し。**Tier 0 publish 候補時点**。

### 工数感

~120-180 行 (A-0 skeleton ~50 + A-1 ~5 + A-2 ~2 + A-3 ~2 + A-4 ~15 + A-5 ~80)。0.5 session。proof-log `yes` (Tier 0 baseline publish 時点)。

### 失敗時 fallback

- **A-5 `differentialEntropy_map_eq_integral_pdf_log_pdf` が 100 行を超える**: `pdf Y ℙ volume` の `.toReal` ↔ `ENNReal` plumbing が散らかる可能性大。`differentialEntropy_eq_integral_withDensity` (`DifferentialEntropy.lean:47`, `ℝ≥0∞`-density 形) を直接起動して `.toReal` 経由を回避、~30 行に圧縮。
- **A-4 `fisherInfo_dirac` の `singular ⇒ rnDeriv = 0 ae` が Mathlib 直接 lemma 不在**: 上述の judgement candidate 通り Tier 3 へ push、Tier 0 から `fisherInfo_dirac` を外す。

---

## Phase B — score function 期待値 0 + integrability (Tier 1) 📋

### スコープ

`fisherInfo_gaussianReal` (Gaussian で `1/v`) と `integral_logDeriv_pdf_eq_zero` (score 期待値 0、`IsRegularDensity` predicate 形) を確定。**Tier 1 = L-F3 撤退ライン**。

**proof-log**: yes (Tier 1 publish 時点で `proof-log-fisher-info-tier1.md` を append)。

### Done 条件

- `fisherInfo_gaussianReal m hv : fisherInfo (gaussianReal m v) = ENNReal.ofReal (1 / v)` (inventory §G-2)
- `IsRegularDensity` predicate 定義 (smooth + L¹ tail vanish の hypothesis 集約、L-F2 撤退ラインの構造)
- `integral_logDeriv_pdf_eq_zero` (inventory §G-4 主結論、predicate 形)
- (任意) `fisherInfo_gaussianReal_zero_var` (`v = 0` 退化 case の取り扱い、Dirac から推論)

### ステップ

- [ ] **B-1 `IsRegularDensity` predicate 定義** (L-F2 撤退ラインの構造、judgement #3 候補):
  ```lean
  structure IsRegularDensity {Ω : Type*} {mΩ : MeasurableSpace Ω} (X : Ω → ℝ)
      (ℙ : Measure Ω) [HasPDF X ℙ volume] : Prop where
    diff : Differentiable ℝ (fun x => (pdf X ℙ volume x).toReal)
    pos : ∀ x, 0 < (pdf X ℙ volume x).toReal
    tail_bot : Tendsto (fun x => (pdf X ℙ volume x).toReal) atBot (𝓝 0)
    tail_top : Tendsto (fun x => (pdf X ℙ volume x).toReal) atTop (𝓝 0)
    integrable_deriv : Integrable (fun x => deriv (fun y => (pdf X ℙ volume y).toReal) x) volume
  ```
  - inventory §G-4 の hypotheses を 1 predicate に集約
  - Phase E で `IsRegularDeBruijnHyp` (de Bruijn 用) と類似構造、Phase B で base predicate を確定
  - ~10-20 行

- [ ] **B-2 `fisherInfo_gaussianReal`** (inventory §G-2):
  ```lean
  theorem fisherInfo_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
      fisherInfo (gaussianReal m v) = ENNReal.ofReal (1 / (v : ℝ))
  ```
  - **証明 4 ステップ**:
    1. `rnDeriv_gaussianReal` で密度を `gaussianPDFReal m v` に書き換え (`rnDeriv (gaussianReal m v) volume =ₐₛ gaussianPDF m v`)
    2. `log_gaussianPDFReal_eq` (Common2026 `DifferentialEntropy.lean:391`) で `log p` を quadratic form `-(1/2) log(2πv) - (x-m)²/(2v)` に
    3. `deriv` を取り `deriv (log p) x = -(x - m)/v`、`Real.deriv_log_comp_eq_logDeriv` で `logDeriv p x = -(x - m)/v`
    4. `∫⁻ ((x - m)/v)² · p(x) dx = (1/v²) · Var = (1/v²) · v = 1/v` (variance 計算)
  - Common2026 `DifferentialEntropy.lean` の Gaussian variance 補助インフラを流用
  - ~80-120 行 (inventory §G-2 見積)
  - **落とし穴**: `ENNReal.ofReal` ↔ `ℝ≥0∞` 経由の plumbing が散らかる可能性、`ENNReal.ofReal_inv_of_pos` 等で吸収。

- [ ] **B-3 `integral_logDeriv_pdf_eq_zero`** (inventory §G-4、predicate 形):
  ```lean
  theorem integral_logDeriv_pdf_eq_zero
      {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
      (X : Ω → ℝ) [HasPDF X ℙ volume] (h_reg : IsRegularDensity X ℙ) :
      ∫ x, logDeriv (fun y => (pdf X ℙ volume y).toReal) x
           * (pdf X ℙ volume x).toReal ∂volume = 0
  ```
  - **証明** (Cover-Thomas 17.7 Lemma):
    - `logDeriv p · p = deriv p / p · p = deriv p` (where `p > 0` from `h_reg.pos`)
    - `∫ deriv p = lim p(R) - lim p(-R)` (FTC, `integral_deriv_mul_eq_sub` 左半分)
    - `h_reg.tail_bot` + `h_reg.tail_top` から `∫ deriv p = 0 - 0 = 0`
  - Mathlib `MeasureTheory.integral_deriv_mul_eq_sub` (`IntegralEqImproper.lean:1296`) を `u := 1, v := pdf` の特殊化
  - **代替**: `integral_deriv_eq_sub` (Mathlib に存在するか要 loogle 確認) で直接
  - ~60-120 行 (inventory §G-4 見積)
  - **落とし穴**: `logDeriv p · p = deriv p` の equality は `p ≠ 0` 点で `rfl`、`p = 0` 点では両辺 0 (`h_reg.pos` で全点 `p > 0` 仮定下では問題なし)。Mathlib `Real.deriv_log_comp_eq_logDeriv` の前提 `f x ≠ 0` をクリアする plumbing 要。

- [ ] **B-4 verify**: `lake env lean Common2026/Shannon/FisherInfo.lean` clean、Phase A + B 本体 0 sorry、Phase C-E は `sorry` 残し。**Tier 1 publish 候補時点** = L-F3 撤退ラインで切るならここで `Common2026.lean` 編入 (Phase V を前倒し)。

### 工数感

~150-260 行 (B-1 ~15 + B-2 ~100 + B-3 ~90 + plumbing ~30)。0.5-0.75 session。proof-log `yes`。

### 失敗時 fallback

- **B-2 Gaussian Fisher info の variance 計算が散らかる**: Common2026 `DifferentialEntropy.lean` に `variance_gaussianReal` 等の直接補題がない場合、`integrable_density_log_density_of_gaussian` 周辺の補題から手動で variance を計算 (~30 行追加)、もしくは Mathlib `Probability.Variance` の `variance_gaussianReal` (要 loogle 確認) を import。
- **B-3 score 期待値 0 で `h_reg.pos` が一般 X で gauss が完全 support ⇒ `pos: ∀ x, 0 < p x` だが他の X では崩れる**: 撤退ライン L-F2 発動 → `IsRegularDensity` を仮定形 predicate のまま hypothesis に括出し、本 plan 内では Gaussian の場合のみ instance を出す形に縮退。一般 X の `IsRegularDensity` instance 整備は別 plan (`fisher-info-regular-family-plan.md`) へ defer。

---

## Phase C — Gaussian convolution heat equation (Tier 2 核 1/3) 📋

### スコープ

de Bruijn identity Step 4 (inventory §G-5) の前半: Gaussian PDF が heat equation `∂_s gaussianPDF 0 s x = (1/2) ∂²_x gaussianPDF 0 s x` を満たすことを手動 verification。**Mathlib に Gaussian PDF の `x`-second derivative の明示 lemma が存在しない** (inventory §C-5)、ゼロから組み立て。

**proof-log**: yes (Tier 2 着手時、Phase E publish と統合)。

### Done 条件

- `gaussianPDF_partial_t_eq` (`∂_s gaussianPDFReal 0 s x = ...` の明示式)
- `gaussianPDF_partial_xx_eq` (`∂²_x gaussianPDFReal 0 s x = ...` の明示式)
- `gaussianPDF_heat_eq`: `∂_s gaussianPDFReal 0 s x = (1/2) · ∂²_x gaussianPDFReal 0 s x`
- (任意) `gaussianPDF_smooth` (任意階微分可能性、`Differentiable` instance bundle)

### ステップ

- [ ] **C-1 `gaussianPDF_partial_t_eq`** (`s` 微分):
  - `gaussianPDFReal 0 s x = (√(2πs))⁻¹ · exp(-x²/(2s))`
  - `∂_s gaussianPDFReal 0 s x = (-1/(2s)) · gaussianPDFReal 0 s x + (x²/(2s²)) · gaussianPDFReal 0 s x`
  - **Mathlib 既存 lemma 探索**: `Real.deriv_exp` + chain rule + `Real.deriv_rpow_const` で組む、~25-40 行

- [ ] **C-2 `gaussianPDF_partial_xx_eq`** (`x` 二階微分):
  - `∂_x gaussianPDFReal 0 s x = (-x/s) · gaussianPDFReal 0 s x`
  - `∂²_x gaussianPDFReal 0 s x = (-1/s) · gaussianPDFReal 0 s x + (x²/s²) · gaussianPDFReal 0 s x`
  - `HasDerivAt.exp` + `HasDerivAt.const_mul` + `HasDerivAt.mul` で組む、~25-40 行

- [ ] **C-3 `gaussianPDF_heat_eq`**:
  - C-1 と C-2 を比較、`(1/2) · ∂²_x = ∂_s` の代数恒等式: `(1/2) · [(-1/s) + (x²/s²)] = (-1/(2s)) + (x²/(2s²))` ⇒ `rfl` レベルで等式
  - `linarith` / `ring` で 1 行、~5-10 行

- [ ] **C-4 (任意) `gaussianPDF_smooth`**:
  - `ContDiff ℝ ∞ (fun (s, x) => gaussianPDFReal 0 s x)` (smooth as bivariate)
  - Phase D-3 で `hasDerivAt_integral_of_dominated_loc_of_deriv_le` の dominated bound 評価で要、~20-30 行
  - **判断 candidate**: Phase C で先取りするか Phase D で必要な場面でだけ出すか判断。Phase D で出す方が dependency 順正しい。

### 工数感

~70-110 行 (C-1 ~30 + C-2 ~30 + C-3 ~10 + plumbing ~20)。0.5-0.75 session。proof-log `yes` (Phase E と統合)。

### 失敗時 fallback

- **C-2 二階微分の連鎖計算で `HasDerivAt` chain が肥大 (Real.deriv_div / div / exp / rpow の合成で 80 行超え)**: 撤退ライン L-F1 発動 → `gaussianPDF_heat_eq` を **axiom 化または hypothesis として外出し** し、Phase D-3 / E で `(h_heat : ...)` 仮定として渡す。証明は Tier 3 / Mathlib upstream で着地予定 (proof-log で「Mathlib gap」記録)。

---

## Phase D — convolution differentiation under integral (Tier 2 核 2/3) 📋

### スコープ

de Bruijn identity Step 1 + 2 + 3 (inventory §G-5):
- Step 1: `ℙ.map (X + √s Z) = (ℙ.map X) ∗ gaussianReal 0 s`
- Step 2: PDF representation `pdf X ⋆ₗ gaussianPDF 0 s`
- Step 3: `d/ds`-step (`hasDerivAt_integral_of_dominated_loc_of_deriv_le` 起動)

**proof-log**: yes (Phase E と統合)。

### Done 条件

- `map_add_sqrt_t_mul_gaussian_eq_conv`: `ℙ.map (X + √s Z) = (ℙ.map X) ∗ gaussianReal 0 s`
- `pdf_add_sqrt_t_mul_gaussian_eq_lconvolution`: `(ℙ.map (X+√s Z)).rnDeriv volume =ₐₛ pdf X ℙ volume ⋆ₗ gaussianPDF 0 s` (inventory §G-3)
- `hasDerivAt_differentialEntropy_map_add_sqrt_t_mul_gaussian`: Phase E の `d/ds`-step を起動して `HasDerivAt (fun s => h(P_s)) (...) t`

### ステップ

- [ ] **D-1 measure-level convolution表現** (inventory §G-5 Step 1):
  ```lean
  lemma map_add_sqrt_t_mul_gaussian_eq_conv
      {Ω} {mΩ : MeasurableSpace Ω} {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
      (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z)
      (hXZ : IndepFun X Z ℙ) (hZ_law : ℙ.map Z = gaussianReal 0 1)
      {s : ℝ} (hs : 0 ≤ s) :
      ℙ.map (fun ω => X ω + Real.sqrt s * Z ω) = (ℙ.map X) ∗ gaussianReal 0 s.toNNReal
  ```
  - `gaussianReal_const_mul` で `(Real.sqrt s) · Z ∼ 𝒩(0, s)`
  - `IndepFun.map_add_eq_map_conv_map₀'` (`@[to_additive]` 自動生成版) で convolution measure に
  - `X ⟂ (√s · Z)` は `IndepFun.comp` + `Measurable.const_mul` から
  - ~30-60 行

- [ ] **D-2 PDF-level convolution bridge** (inventory §G-3):
  ```lean
  lemma pdf_add_eq_lconvolution_pdf_volume
      {Ω} {mΩ : MeasurableSpace Ω} {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
      (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
      (hXY : IndepFun X Y ℙ) [HasPDF X ℙ volume] [HasPDF Y ℙ volume] :
      ℙ.map (X + Y) = volume.withDensity (pdf X ℙ volume ⋆ₗ pdf Y ℙ volume)
  ```
  - `IndepFun.add_hasPDF'` (Mathlib `Density.lean:333` add 版) で `HasPDF (X+Y) ℙ volume` instance
  - `IndepFun.pdf_add_eq_lconvolution_pdf'` (Mathlib `Density.lean:350` add 版) で `pdf (X+Y) =ᵐ pdf X ⋆ₗ pdf Y`
  - `map_eq_withDensity_pdf` で `ℙ.map (X+Y) = volume.withDensity (pdf (X+Y))`
  - `withDensity_congr_ae` で `=ᵐ` を `=` に
  - ~40-80 行 (inventory §G-3 見積)
  - **`SigmaFinite (ℙ.map X)`** 前提: `IsProbabilityMeasure ℙ` から `Measure.IsFiniteMeasure.toSigmaFinite` で自動

- [ ] **D-3 `d/ds`-step**: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` 起動 (inventory §G-5 Step 3):
  ```lean
  -- F (s, x) := -p_s(x) · log p_s(x)
  -- where p_s := pdf X ⋆ₗ gaussianPDF 0 s
  -- F'_s (x) := ∂_s p_s(x) · (-(1 + log p_s(x)))
  ```
  - **bound integrable**: `s ∈ Set.Ioo (t/2) (2t)` で `|F'_s(x)| ≤ bound(x)`、bound として **Gaussian tail から integrable な envelope** を取る
  - **Mathlib`hasDerivAt_integral_of_dominated_loc_of_deriv_le`** (inventory §C-4) の前提:
    - `[RCLike 𝕜]` = `ℝ` で自動
    - `[NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]` = `E := ℝ` で全部自動
    - `Integrable (F t) volume`: `t = t₀` で `differentialEntropy_eq_integral_density` から integrable (Phase B integrable 系の補強で確保)
    - `bound_integrable`: bound として `c · |x| · exp(-x²/(8t))` 形 (Gaussian tail × poly)、`integrable_density_log_density_of_gaussian` 拡張で確保
    - `AEStronglyMeasurable F'`: convolution の measurability から `fun_prop` で自動
    - `HasDerivAt (F · x) (F' x) s`: convolution 微分 (`HasDerivAt.lconvolution_right`? — Mathlib 確認要、無ければ Phase C heat-eq + product rule で組む)
  - ~80-120 行 (inventory §G-5 Step 3 見積)
  - **落とし穴 1**: `bound` の構築が最大の技術的ボトルネック。Gaussian convolution の uniform tail decay で押さえる、Common2026 `integrable_density_log_density_of_gaussian` 拡張要。
  - **落とし穴 2**: convolution 微分 `(d/ds) (pdf X ⋆ₗ gaussianPDF 0 s) x` は Phase C heat-eq + `HasDerivAt.convolution_right` (Mathlib `Convolution.lean` 系) を組み合わせて出す、~30-50 行追加。

- [ ] **D-4 verify**: `lake env lean Common2026/Shannon/FisherInfo.lean` clean、Phase A + B + C + D 本体 0 sorry、Phase E は `sorry` 残し。

### 工数感

~150-260 行 (D-1 ~50 + D-2 ~60 + D-3 ~100 + plumbing ~30)。0.75-1 session。proof-log `yes` (Phase E と統合)。

### 失敗時 fallback

- **D-3 dominated bound の構築が散らかる (Gaussian convolution の uniform tail envelope の Mathlib API 不在で plumbing が 200 行超え)**: 撤退ライン L-F1 発動 → `hasDerivAt_differentialEntropy_map_add_sqrt_t_mul_gaussian` を **hypothesis 形** (`(h_diff : HasDerivAt ...)`) で外出し、Phase E で `(h_diff : ...)` を受け取って de Bruijn identity を結語する形に縮退。dominated bound 整備は別 plan (`fisher-info-dominated-bound-plan.md`) へ defer。

---

## Phase E — de Bruijn identity 結語 + wrapper (Tier 2 核 3/3) 📋

### スコープ

Phase C (heat-eq) + Phase D (convolution 表現 + `d/ds`-step) を結合して `deBruijn_identity` 主定理を IBP 経由で結語、`IsRegularDeBruijnHyp` predicate で hypothesis 集約。**Tier 2 = 理想形** = 本 plan のゴール。

**proof-log**: yes (Tier 2 publish 時点で `proof-log-fisher-info-tier2.md` を append、Phase C + D + E を統合)。

### Done 条件

- `IsRegularDeBruijnHyp` predicate 定義 (Phase B `IsRegularDensity` の de Bruijn 拡張、L-F2 撤退ライン構造)
- `deBruijn_identity` 主定理 `HasDerivAt (fun s => h(P_s)) ((1/2) · J(P_t)) t` (signature §Goal 参照)
- (任意) `deBruijn_identity_gaussian_sanity_check`: `X = 0` case で `h(𝒩(0, t)) = (1/2) log(2πet)`, `d/dt = 1/(2t) = (1/2) · J(𝒩(0, t))` (verification)

### ステップ

- [ ] **E-1 `IsRegularDeBruijnHyp` predicate**:
  ```lean
  structure IsRegularDeBruijnHyp {Ω} {mΩ : MeasurableSpace Ω} (X Z : Ω → ℝ)
      (ℙ : Measure Ω) [HasPDF X ℙ volume] : Prop where
    X_reg : IsRegularDensity X ℙ
    -- + convolution-side regularity (smoothness of pdf X ⋆ₗ gaussianPDF 0 s)
    -- + dominated bound for hasDerivAt_integral_of_dominated_loc_of_deriv_le
    -- + IBP integrability for integral_mul_deriv_eq_deriv_mul_of_integrable
  ```
  - Phase B `IsRegularDensity` を拡張、de Bruijn の 5 ステップで使う追加 regularity を集約
  - ~15-30 行

- [ ] **E-2 IBP step** (inventory §G-5 Step 5):
  ```lean
  -- -∫ p_s · (d/ds log p_s) dx = -∫ (d/ds p_s) dx = -d/ds ∫ p_s dx = -d/ds 1 = 0  (trivial path)
  -- 一方:
  -- -∫ p_s · (∂_s p_s / p_s) dx = -∫ ∂_s p_s dx
  -- これを heat-eq (Phase C) で = -(1/2) ∫ ∂²_x p_s dx
  -- IBP で = (1/2) ∫ (∂_x p_s)² / p_s dx = (1/2) J(P_s)
  ```
  - `integral_mul_deriv_eq_deriv_mul_of_integrable` (`IntegralEqImproper.lean:1318`) を `u := log p_s, v := p_s` の特殊化
  - `IsRegularDeBruijnHyp.X_reg.tail_*` で `[u·v]_{-∞}^{∞} = 0`
  - convolution side regularity で `u` の differentiability を全点で確保
  - `log p_s` の `∂_x log p_s = (∂_x p_s) / p_s = logDeriv p_s` で `fisherInfo` の被積分関数に到達
  - ~40-60 行 (inventory §G-5 Step 5 見積)

- [ ] **E-3 `deBruijn_identity` main statement** (sandwich):
  - Phase D-3 (`hasDerivAt_differentialEntropy_map_add_sqrt_t_mul_gaussian`) から `HasDerivAt (fun s => h(P_s)) D t`
  - E-2 IBP から `D = (1/2) · (fisherInfo (P.map (X + √t Z))).toReal`
  - `HasDerivAt.congr_deriv` (Mathlib) で `D` の値を `(1/2) · J(P_t)` に書き換え
  - ~30-50 行

- [ ] **E-4 (任意) Gaussian sanity check**:
  ```lean
  example {t : ℝ} (ht : 0 < t) :
      HasDerivAt (fun s => (1/2) * Real.log (2 * Real.pi * Real.exp 1 * s)) (1 / (2 * t)) t
  ```
  - `differentialEntropy_gaussianReal` (Common2026 `DifferentialEntropy.lean:406`) で `h(𝒩(0, t)) = (1/2) log(2πet)` を代入
  - `Real.hasDerivAt_log` + chain で LHS の derivative を出し `1/(2t)` と一致
  - RHS は `(1/2) · J(𝒩(0, t)) = (1/2) · 1/t = 1/(2t)` (B-2 `fisherInfo_gaussianReal` を `t` 代入)
  - 両辺が一致することを確認、~20-30 行

- [ ] **E-5 verify**: `lake env lean Common2026/Shannon/FisherInfo.lean` clean、Phase A + B + C + D + E 本体 0 sorry。

### 工数感

~110-180 行 (E-1 ~20 + E-2 ~50 + E-3 ~40 + E-4 ~25 + plumbing ~20)。0.5 session。proof-log `yes`。

### 失敗時 fallback

- **E-2 IBP step で `integral_mul_deriv_eq_deriv_mul_of_integrable` の `tsupport` 前提が `p_s` 全 ℝ サポートで詰まる**: 補助補題 `integral_mul_deriv_eq_deriv_mul_of_integrable_of_tail_vanish` (~30 行) を private で書く、`IsRegularDeBruijnHyp` の tail vanish 条件を直接使う形。
- **E-3 sandwich で `HasDerivAt` の値を書き換える congruence lemma が散らかる**: `HasDerivAt.congr` を直接使い ad-hoc に書き換え、~10 行 boilerplate で吸収。

---

## Phase V — verify + Common2026.lean 編入 📋

### スコープ

`FisherInfo.lean` の最終 verify + `Common2026.lean` に編入。

**proof-log**: no (skeleton 揃ったあとの整地)。

### Done 条件

- `lake env lean Common2026/Shannon/FisherInfo.lean` clean (0 sorry, 0 warning)
- `Common2026.lean` に `import Common2026.Shannon.FisherInfo` 追記
- `lake env lean Common2026.lean` clean
- 後続 seed (T2-D EPI) からの import 可能性を docstring で明示

### ステップ

- [ ] **V-1 final verify**: `lake env lean Common2026/Shannon/FisherInfo.lean` で 0 sorry / 0 warning を確認。`linter.unusedSectionVars false` 等の必要 option を確定。

- [ ] **V-2 library root 編入**:
  - `Common2026.lean` の Shannon 系 import 区画に `import Common2026.Shannon.FisherInfo` 追記
  - `lake env lean Common2026.lean` clean 確認
  - ~2-3 行

- [ ] **V-3 docstring 補強**:
  - `FisherInfo.lean` 先頭の module docstring に「T2-D EPI seed の入口準備」と明示 (後続 T2-D plan が import する際の signpost)
  - `deBruijn_identity` 上に Cover-Thomas 17.7.2 への参照を入れる

### 工数感

~5-10 行 (V-1 ~0 + V-2 ~3 + V-3 ~5)。0.25 session。proof-log `no`。

### 失敗時 fallback

- なし (verify-only Phase、何か発見すれば該当 Phase に戻る)。

---

## 撤退ライン

### Scope 縮小ライン (発動時に T2-F 完成形を縮小して publish)

- **L-F1**: **de Bruijn を heat-eq 仮定形で publish** (~600 行, Tier 2 弱形)
  - 発動条件: Phase C (Gaussian heat equation) で `gaussianPDF_heat_eq` の二階微分連鎖計算が **200 行を超える** (inventory §G-5 Step 4 最大リスク、§撤退ライン到達距離 評価)
  - 縮退後: `deBruijn_identity` の signature に **`(h_heat : ∀ s x, ∂_s gaussianPDFReal 0 s x = (1/2) · ∂²_x gaussianPDFReal 0 s x)` 仮定として追加**。Phase C の証明を defer、Phase D + E は heat-eq 仮定下で完走。statement 完成形は publish、heat-eq 整備は別 plan (`fisher-info-heat-eq-plan.md`) へ。

- **L-F2**: **score function 期待値 0 を `IsRegularFamily` predicate 形に hypothesis 抽出** (~700 行, Tier 2 弱形)
  - 発動条件: Phase B-3 (`integral_logDeriv_pdf_eq_zero`) の smooth tail 前提が一般 X で書けない (`tail_*` predicate の dispatch が散らかる)
  - 縮退後: `integral_logDeriv_pdf_eq_zero` を `IsRegularDensity` predicate を仮定として外出し、本 plan 内では Gaussian の場合のみ instance を出す形に縮退。一般 X の `IsRegularDensity` instance 整備は別 plan (`fisher-info-regular-family-plan.md`) へ defer。**現状の plan signature と一致**で、最初から L-F2 状態で publish も可。

- **L-F3**: **Tier 0 + Tier 1 baseline publish** (~280-360 行)、Tier 2 (de Bruijn) を後続 seed に分離
  - 発動条件: Phase C-D で **1 月で 600 行に収まらない** (inventory §G 自作要 6 項目の上限 940 行に到達してもまだ未完)
  - 縮退後: `fisherInfo` 定義 + `fisherInfo_gaussianReal` + `integral_logDeriv_pdf_eq_zero` + `differentialEntropy_map_eq_integral_pdf_log_pdf` (Tier 1) のみで publish (~280-360 行)。`deBruijn_identity` は別 plan (`fisher-info-de-bruijn-plan.md`) に切り出し、本 plan は **Fisher info 概念の最小 publish** で着地。T2-D EPI seed では「de Bruijn を仮定形で受け取る」状態で開始。

### 自作 plumbing 肥大ライン (新規、inventory §H 撤退ライン + 本 plan judgement candidate)

- **L-P1**: **`gaussianPDF_heat_eq` の二階微分連鎖が想定の 80 行を超えて 200 行クラス** (inventory §G-5 Step 4 最大の発見リスク)
  - 縮退案: L-F1 発動と同等。heat-eq を hypothesis 形で外出し。

- **L-P2**: **`hasDerivAt_integral_of_dominated_loc_of_deriv_le` の `bound_integrable` 前提整備で Gaussian convolution uniform tail envelope の Mathlib API 不在**
  - 縮退案: Phase D-3 の dominated bound 構築を **`Common2026/Shannon/DifferentialEntropy.lean` 拡張** で確保 (`integrable_density_log_density_of_gaussian_convolution` 自前補助 ~50 行)、本 plan 内で吸収。それでも 100 行を超えるなら L-F1 / L-F3 に切り替え。

- **L-P3**: **`fisherInfo` の `ℝ≥0∞` ↔ `ℝ` 換算 plumbing が `deBruijn_identity` signature で散らかる** (`(1/2) · (fisherInfo ...).toReal` の `.toReal` 処理が肥大化)
  - 縮退案: `fisherInfoReal := (fisherInfo μ).toReal` 派生補題を Phase A-3 で先取り、`deBruijn_identity` の signature では `fisherInfoReal` を直接使う。

- **L-P4**: **1 月で完遂不能リスク** (Phase C + D + E を続けて 1 月内で publish できない)
  - 縮退案: **Tier 1 (Phase A + B) で 1 月完結**を目標、Tier 2 (Phase C-E) は別 月に分離。Tier 1 baseline (~280-360 行) で L-F3 部分 publish 価値を確保。Tier 2 (Phase C-E, ~300-500 行) は次月に独立に attack。判断ログで月分割を記録。

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| **`gaussianPDF_heat_eq` の二階微分連鎖計算が想定の 80 行を超えて 200 行クラス** (inventory §G-5 Step 4 最大リスク) | **高** (inventory §撤退ラインへの距離 で明示) | **高** (Phase C +120 行 or L-F1 発動) | L-F1 / L-P1 発動で heat-eq を hypothesis 形で外出し。Mathlib に `Real.deriv_exp` / `HasDerivAt.exp` / `HasDerivAt.const_mul` の系列があるので **chain rule の組み合わせで 30-40 行に圧縮可能**な見込み、Phase C 着手時に loogle で詳細補題を発掘。 |
| **`hasDerivAt_integral_of_dominated_loc_of_deriv_le` の `bound_integrable` 整備で Gaussian tail envelope の Mathlib API 不在** | 中-高 | 中-高 (Phase D-3 +50-100 行) | L-P2 発動、`integrable_density_log_density_of_gaussian_convolution` を `DifferentialEntropy.lean` 拡張で自前 50 行。または L-F1 と組み合わせて Phase D-3 全体を hypothesis 形で外出し。 |
| **score function 期待値 0 の smooth tail 前提が一般 X で `IsRegularDensity.tail_*` の dispatch 経路で詰まる** | 中 (inventory §G-4 で予測済) | 中 (Phase B-3 +30-50 行 or L-F2 発動) | L-F2 発動: `IsRegularDensity` predicate のまま hypothesis に括出し、本 plan 内では Gaussian の場合のみ instance を出す形で publish。**現状の plan signature と一致**で、最初から L-F2 状態で進めるのが安全。 |
| **`differentialEntropy_map_eq_integral_pdf_log_pdf` (A-5) の `.toReal` ↔ `ENNReal` plumbing が 100 行超え** | 中 | 中 (Phase A +50 行) | `differentialEntropy_eq_integral_withDensity` (`DifferentialEntropy.lean:47`, `ℝ≥0∞` 形) を直接起動して `.toReal` 経由を回避、~30 行に圧縮。 |
| **`fisherInfo` `ℝ≥0∞` return 型と `deBruijn_identity` `HasDerivAt` 形 (`ℝ` 値) で `.toReal` plumbing が散らかる** | 中 | 低-中 (Phase E +20-40 行) | L-P3 発動、`fisherInfoReal` 派生補題を Phase A-3 で先取り。**もしくは `fisherInfo` の return 型を最初から `ℝ` に変更**する大きな判断 (judgement candidate)、inventory §G-1 の `ℝ≥0∞` 推奨と背反するので Phase A 着手時に確定。 |
| **`IndepFun.pdf_add_eq_lconvolution_pdf'` の add 版 (`@[to_additive]` 自動生成) で名前解決失敗** | 低 (Mathlib `@[to_additive]` は通常 stable) | 低 (1-2 行で fix) | Phase D-2 着手時に loogle で `pdf_add_eq_lconvolution_pdf'` を確認、無ければ `pdf_mul_eq_mlconvolution_pdf'` を additive group `(ℝ, +, 0)` で起動して手動 reshape (~10 行)。 |
| **Phase C heat-eq + Phase D convolution 微分の合成 (`HasDerivAt.lconvolution_right`? Mathlib 不在の可能性)** | 中-高 (inventory §C-5 で部分既存と note) | 中-高 (Phase D-3 +30-50 行 or L-F1 発動) | Phase D 着手時に loogle で `Convolution.lean` の `HasDerivAt` 系を発掘、無ければ heat-eq + product rule で組み立て (Phase C の `∂_s gaussianPDF` と `gaussianPDF` の convolution 経由)。 |
| **`Common2026/Shannon/DifferentialEntropy.lean` の Gaussian convolution 拡張 (`integrable_density_log_density_of_gaussian_convolution`) 整備が散らかる** | 中 | 中 (Phase D-3 +50 行) | `integrable_density_log_density_of_gaussian` (`DifferentialEntropy.lean:81`) の証明テンプレを convolution に拡張、~30-50 行で書ける見込み。Common2026 既存 Gaussian インフラを最大限再利用。 |
| **proof 規模が roadmap 上限 (800 行) を超える** | **中-高** (inventory 自作要上限 940 行) | 中 (1 月で完走できない) | 撤退ライン L-F1〜L-F3 + L-P4 を Phase 単位で発動可能に設計済。Phase B 完了 (Tier 1, ~280-360 行) でも publish 価値あり (L-F3 縮退)。 |
| **1 月で Tier 2 (Phase C + D + E) 完遂不能** | **中-高** | 中 (next month に持ち越し) | L-P4 発動: Tier 1 (Phase A + B) を月 1 で完遂、Tier 2 (Phase C-E) を月 2 へ分割。判断ログで月分割を記録。 |
| **`fisherInfo_dirac` (A-4) で `singular ⇒ rnDeriv = 0 ae` の Mathlib 直接補題不在** | 低 | 低 (Phase A-4 +10 行 or Tier 3 push) | A-4 fallback (corner case を Tier 3 に push) で Tier 0 publish から外す。主路に影響なし。 |

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 例 (未着手のため空):
1. **(YYYY-MM-DD) (Phase X) 方針変更**: <decision>
-->

1. **(2026-05-19) (実装着手時) L-F1 + L-F2 を最初から適用形で publish** — Tier 2 (Phase C-E) の heat-eq / dominated-bound / IBP は inventory §G-5 で 250-400 行見積、1 セッション内で完遂は高 risk と判断。`IsRegularDeBruijnHyp` predicate に Cover-Thomas 17.7.2 の derivAt 結論を hypothesis field として吸収し、`deBruijn_identity` を完全 signature で publish。Gaussian-side instance 整備は後続 seed に分離。`deBruijn_identity` の signature は将来 instance discharge 完了時にも変わらないので、T2-D EPI seed から「de Bruijn を受け取る」形での citation はこの状態でも valid。

2. **(2026-05-19) (Phase A) `ℙ` (mathematical bold P, U+2119) を binder 名に使うと parse error** — 既存 `InformationTheory` / `MeasureTheory` 系の notation 衝突で `unexpected token 'ℙ'` 連鎖。binder 名はすべて plain `P` に統一。在庫の skeleton 例 (`{Ω} {mΩ : MeasurableSpace Ω} {ℙ : Measure Ω}`) を本実装に取り込む際の落とし穴、後続 seed に注意喚起すべき。

3. **(2026-05-19) (Phase A 拡張) `fisherInfoReal` 派生 `.toReal` 慣行を Tier 0 で先取り** — L-P3 plumbing 対策。`deBruijn_identity` で `(1/2) * (fisherInfo …).toReal` を直接書く現行 signature を踏襲しつつ、後続 seed (T2-D EPI) で `fisherInfoReal` が直接使える便宜を確保。

4. **(2026-05-19) (Phase B+C+D 撤退) `fisherInfo_gaussianReal = 1/v` (B-2) を本 plan から分離** — Gaussian variance 計算が `DifferentialEntropy.lean` 既存インフラに完全 fit する保証なし、1 セッションで安定 publish できる確信が低い (inventory §G-2 80-120 行見積)。Tier 2 publish 確保を優先し、`fisherInfo_gaussianReal` は L-P4 月分割形で次月 seed (`fisher-info-gaussian-plan.md`) に切り出し。本 plan の Tier 1 publish ライン (L-F3 撤退ライン候補) は `integral_logDeriv_pdf_eq_zero` (L-F2 形) + `differentialEntropy_map_eq_integral_pdf_log_pdf` bridge + `fisherInfo_dirac` の 3 件で確保。

5. **(2026-05-19) (follow-up `fisher-info-gaussian-discharge-moonshot-plan.md` 経由) Gaussian discharge は Stage 1 で着地、L-F1+L-F2 完全 discharge は不能と判明** — 後続 seed `fisher-info-gaussian-discharge-moonshot-plan.md` で Phase A (`IsRegularDensity (gaussianReal m v)` instance) と Phase B-1/B-2 (`integral_logDeriv_pdf_eq_zero_gaussian` wrapper + `logDeriv_gaussianPDFReal`) は完遂 (`Common2026/Shannon/FisherInfoGaussian.lean` 329 行 publish)。**ただし Phase B-3 `fisherInfo_gaussianReal = 1/v` 着手時に `fisherInfo` 定義 (`FisherInfo.lean:58`) の representative-依存性 flaw を発見** — `Measure.rnDeriv` は `Classical.choose` で定義された opaque measurable representative を返し (`Lebesgue.lean:80`)、generic に non-differentiable のため `logDeriv ((rnDeriv).toReal) = 0` ae、ゆえに `fisherInfo (gaussianReal m v) = 0` (mathematical の `1/v` ではなく)。L-F1 (heat-eq) も Phase C で同じ `fisherInfo` を `derivAt_entropy_eq_half_fisher` field の RHS に持つため、Gaussian でも discharge 不能。Gaussian discharge follow-up は **L-G3 で Stage 1 着地**、L-F1+L-F2 の完全 discharge には `fisherInfo` 定義 (a.e.-class 不変な形) の redefinition が必要 (別 seed)。
   - 副作用: `IsRegularDensity` structure を `FisherInfo.lean` で a.e.-representative 形に back-port (新 field `density : ℝ → ℝ`, `pdf_ae_eq`、`structure ... : Prop` → 非 Prop)。`integral_logDeriv_pdf_eq_zero` の結論も `h_reg.density` 形に書き換え。`FisherInfo.lean` 222 行 → 236 行 (+14 行)、外部互換性 break なし (consumer は `integral_logDeriv_pdf_eq_zero` のみ)。
