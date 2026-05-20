# Fisher Info / de Bruijn — Gaussian discharge ムーンショット計画 🌙 (T2-F follow-up)

> **DELETED (2026-05-20)**: V1 `fisherInfo` was removed from `FisherInfo.lean` and the EPI/Stam scaffolding migrated to V2 `FisherInfoV2.fisherInfoOfMeasureV2` (full build green, 0 sorry).
>
> **RESOLVED (2026-05-20) — flaw-vacuous fix**: the Gaussian *Stam* discharges
> that this plan's chain produced via the V1 `fisherInfo = 0` artefact were
> **vacuous** (`exfalso` on `0 < J_X`) and have been removed. The genuine Gaussian
> EPI is `entropy_power_inequality_gaussian_saturation`; the genuine non-vacuous
> Gaussian convex Fisher bound is `FisherInfoV2.stam_convex_fisher_bound_gaussian`
> (V2-keyed, `1/v`). See
> [`flaw-vacuous-review-2026-05-20.md`](flaw-vacuous-review-2026-05-20.md) HIGH-1.

<!--
雛形メモ (moonshot-plan-template.md より):
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 削除/廃止 Phase は ~~取り消し線~~、判断ログは append-only
-->

> **Parent**: [`fisher-info-moonshot-plan.md`](fisher-info-moonshot-plan.md) §Tier 2 撤退ライン L-F1 + L-F2 (publish 済 `IsRegularDensity` / `IsRegularDeBruijnHyp` hypothesis pass-through を Gaussian 限定で discharge する後続 seed)
>
> **Predecessor (inventory)**: [`fisher-info-mathlib-inventory.md`](fisher-info-mathlib-inventory.md) §C-4, §C-5, §F, §G-2 / §G-5 (特に §撤退ライン line 395 = 「smooth tail が一般 X で書けない場合 hypothesis pass-through、Gaussian の場合のみ instance を出す」が本 plan の起点)
>
> **既存実装**: [`Common2026/Shannon/FisherInfo.lean`](../../Common2026/Shannon/FisherInfo.lean) 222 行、0 sorry。
> Phase B `integral_logDeriv_pdf_eq_zero` と Phase E `deBruijn_identity` は L-F1+L-F2 hypothesis 形で publish 済 (`IsRegularDensity` / `IsRegularDeBruijnHyp` predicate)。本 plan はその hypothesis を Gaussian 限定で完全 discharge する後続 seed。
>
> **Goal**: `gaussianReal m v` の場合に L-F1+L-F2 hypothesis を完全 discharge し、hypothesis なし形の `deBruijn_identity_gaussian`、`integral_logDeriv_pdf_eq_zero_gaussian`、`fisherInfo_gaussianReal = 1/v` を新規ファイル `Common2026/Shannon/FisherInfoGaussian.lean` で publish。
>
> **撤退ライン**: [L-G1] heat-eq 連鎖計算が肥大化した場合に scale-restricted form (`X ⊥ Z` で `X` も Gaussian) のみで publish / [L-G2] `hasDerivAt_integral_of_dominated_loc_of_deriv_le` の dominating envelope 構築が想定 50 行を超える場合、Gaussian + Gaussian convolution semigroup 経路に縮退 (Mathlib `gaussianReal_conv_gaussianReal` で `X+√t Z` も Gaussian → variance-shift で直接微分) / [L-G3] Phase D `IsRegularDeBruijnHyp` instance discharge が 1 セッションで詰む場合、Phase A〜C のみ publish (`fisherInfo_gaussianReal = 1/v` まで)、Phase D は別 seed 分離 (詳細 §撤退ライン)。

## 進捗

- [x] Phase 0 — 在庫再確認 + Gaussian PDF logDeriv closed form 補題発掘 ✅ (Mathlib に `Differentiable (gaussianPDFReal)` / `deriv (gaussianPDFReal)` の closed form 補題なし、自前で構築)
- [x] Phase A — `IsRegularDensity (gaussianReal m v)` instance discharge ✅ (`IsRegularDensity` を a.e.-representative 形に back-port した上で 8 field 完全 discharge、判断ログ #1)
- [x] Phase B-1 / B-2 — `integral_logDeriv_pdf_eq_zero_gaussian` wrapper + `logDeriv_gaussianPDFReal` 補助補題 ✅
- 🔄 Phase B-3 — `fisherInfo_gaussianReal = 1/v` **L-G3 撤退** (判断ログ #2: `fisherInfo` 定義の representative-依存性 flaw により computing 不能)
- 🔄 Phase C — `IsRegularDeBruijnHyp` Gaussian instance discharge **L-G3 撤退** (Phase B-3 と同じ `fisherInfo` flaw に block される)
- 🔄 Phase D — `deBruijn_identity_gaussian` hypothesis なし wrapper publish **L-G3 撤退** (Phase C に依存)
- [x] Phase V — verify ✅ (`lake env lean Common2026/Shannon/FisherInfoGaussian.lean` clean, 0 sorry, 0 warning)

> **実態整合 (2026-05-20): DONE-HONEST-HYPS (FisherInfoGaussian.lean は本 plan 通り) — B-3/C/D は V1 flaw で本 plan では未達だが、V2 で後続 discharge 済** —
> 本 plan の進捗は `FisherInfoGaussian.lean` (329 行、0 sorry) の実態と一致: Phase A
> `isRegularDensity_gaussianReal_of_law` (`:271`) / Phase B-1,B-2 `integral_logDeriv_pdf_eq_zero_gaussian` (`:288`)
> + `logDeriv_gaussianPDFReal` (`:296`) は完了。Phase B-3/C/D の L-G3 撤退も正しい (`fisherInfo` V1 の
> representative-dependence flaw、判断ログ #2 `:304-327`)。**ただし撤退分は別系統で達成済**:
> `fisherInfo_gaussianReal = 1/v` の代替 = `FisherInfoV2.lean:296` `fisherInfoOfDensity_gaussianPDFReal`、
> Gaussian de Bruijn の代替 = `FisherInfoV2DeBruijn.lean:364` `deBruijn_identity_v2_gaussian`
> (V2 は density-as-input なので Gaussian が正しく `1/v` に評価される、共に 0 sorry)。本 plan の Goal が約束する
> `fisherInfo_gaussianReal` / `deBruijn_identity_gaussian` (V1 measure-as-input 形) は依然未着地。

## ゴール / Approach

### Goal (最終定理 signature)

新規ファイル `Common2026/Shannon/FisherInfoGaussian.lean` で以下を publish:

```lean
namespace Common2026.Shannon

/-- **`IsRegularDensity` instance for Gaussian densities** (L-F2 hypothesis discharge). -/
theorem isRegularDensity_gaussianReal_of_law
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℝ) [HasPDF X P volume] {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v) :
    IsRegularDensity X P

/-- **Gaussian Fisher info**: `J(𝒩(m, v)) = 1/v`. -/
theorem fisherInfo_gaussianReal
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    fisherInfo (gaussianReal m v) = ENNReal.ofReal (1 / (v : ℝ))

/-- **Gaussian score function expectation vanishes** (L-F2 hypothesis discharge form). -/
theorem integral_logDeriv_pdf_eq_zero_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℝ) [HasPDF X P volume] {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v) :
    ∫ x, logDeriv (fun y => (pdf X P volume y).toReal) x
         * (pdf X P volume x).toReal ∂volume = 0

/-- **`IsRegularDeBruijnHyp` instance for Gaussian `X`** (L-F1+L-F2 hypothesis discharge). -/
theorem isRegularDeBruijnHyp_gaussianReal_of_law
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    [HasPDF X P volume]
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1)
    {t : ℝ} (ht : 0 < t) :
    IsRegularDeBruijnHyp X Z P t

/-- **de Bruijn identity for Gaussian `X`** (hypothesis なし形、`fisher-info-moonshot-plan` Tier 2 完成形)。 -/
theorem deBruijn_identity_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    [HasPDF X P volume]
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s => differentialEntropy (P.map (fun ω => X ω + Real.sqrt s * Z ω)))
      ((1/2) * (fisherInfo (P.map (fun ω => X ω + Real.sqrt t * Z ω))).toReal)
      t

end Common2026.Shannon
```

### Approach (overall strategy / shape of solution)

**戦略の shape**: 本 plan は **`IsRegularDensity` / `IsRegularDeBruijnHyp` の field を Gaussian の closed form で逐一埋める**。鍵となるのは **`X + √t Z` の law が再び Gaussian になる** (`gaussianReal_conv_gaussianReal`) ため、convolution 側の regularity も Gaussian regularity に帰着でき、heat-eq / dominated bound の Phase C/D を **「Gaussian semigroup 上の variance-shift」** に置換できる点:

1. **`IsRegularDensity (gaussianReal m v)` instance は完全 closed form**:
   - `pdf X P volume =ₐₛ gaussianPDFReal m v` を `hX_law : P.map X = gaussianReal m v` + `rnDeriv_gaussianReal` + `map_eq_withDensity_pdf` で出す
   - `diff`: `gaussianPDFReal m v` は `exp` × `polynomial` で `Differentiable ℝ` (Mathlib `Real.differentiable_exp` + chain)
   - `pos`: Mathlib `gaussianPDFReal_pos` (`Real.lean:61`) を直接適用 (`hv : v ≠ 0` を充足)
   - `tail_bot` / `tail_top`: `exp(-x²/(2v))` の tail decay。Mathlib `Real.tendsto_exp_neg_atTop_nhds_zero` + composition
   - `integrable_deriv`: `deriv (gaussianPDFReal m v) x = -((x-m)/v) · gaussianPDFReal m v x` は `(polynomial) × (Gaussian)` で Mathlib `Integrable.mul_polynomial` + `integrable_rpow_mul_exp_neg_mul_sq` 系で integrable
   - `integral_deriv_eq_zero`: FTC + `tail_*` から `∫ p' = lim p(R) - lim p(-R) = 0 - 0 = 0`
   - 約 80-120 行 (Mathlib closed form lemma の組み合わせ)

2. **`fisherInfo_gaussianReal = 1/v` は variance 計算で直接**:
   - `rnDeriv_gaussianReal` で密度を `gaussianPDFReal` に
   - `logDeriv (gaussianPDFReal m v) x = -(x-m)/v` を `log_gaussianPDFReal_eq` (Common2026 `DifferentialEntropy.lean:391`) + `deriv` から
   - `∫ ((x-m)/v)² · gaussianPDFReal dx = v/v² = 1/v` を `variance_fun_id_gaussianReal` (Mathlib `Real.lean:518`) 経由
   - 約 60-100 行

3. **`IsRegularDeBruijnHyp` の Gaussian discharge は convolution = Gaussian の閉性に頼る**:
   - `IndepFun.comp` + `Measurable.const_mul` で `IndepFun X (√t Z) P`
   - `gaussianReal_const_mul`: `(P.map (√t · Z)) = gaussianReal 0 (t · 1)` (`hv := ne_of_gt (Real.sqrt_pos.mpr ht)` で `√t > 0`)
   - `gaussianReal_add_gaussianReal_of_indepFun` (Mathlib `Real.lean:624`): `P.map (X + √t Z) = gaussianReal (m + 0) (v + t.toNNReal) = gaussianReal m (v + t.toNNReal)`
   - そのため `(P_s := P.map (X + √s Z)) = gaussianReal m (v + s.toNNReal)` を関数として書き下す
   - `differentialEntropy (P_s) = (1/2) log(2π e (v + s))` (`differentialEntropy_gaussianReal` 既存)
   - `(d/ds) (1/2) log(2π e (v + s)) = 1/(2(v+s))` ← Mathlib `Real.hasDerivAt_log` + composition で直接出す
   - `fisherInfo (P_t) = 1/(v + t)` ← Phase B `fisherInfo_gaussianReal` を `v ↝ v + t.toNNReal` で
   - そして `1/(2(v+t)) = (1/2) · 1/(v+t) = (1/2) · J(P_t)` は `ring`
   - `derivAt_entropy_eq_half_fisher` を直接構成。**Phase C heat-eq / Phase D dominated bound は経由せずに済む**
   - 約 80-150 行 (convolution の law 計算 + `differentialEntropy_gaussianReal` 起動 + `HasDerivAt.log` chain)

4. **`deBruijn_identity_gaussian` wrapper**: Phase C instance を既存 `deBruijn_identity` に渡すだけ、~10-20 行

5. **Mathlib-shape-driven 原則**: `derivAt_entropy_eq_half_fisher` を **直接 `HasDerivAt`-shape で構成**。`(1/2) log(2π e (v + s))` の derivative は Mathlib に直接 lemma はないが、`Real.hasDerivAt_log` (`Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean:52`) を `f(s) := 2π e (v + s)` で composition すれば 1 行で出る。**heat semigroup 経由を完全に回避**。

### Approach 図

```
Phase 0 : 在庫再確認 + closed form 微分補題発掘                  ← 0.25 session (0.5h)
          ──────────────────────────────────────────────
Phase A : IsRegularDensity (gaussianReal) instance              ← 0.5-0.75 session (1.5-2h)
                                                                  ~80-120 行
          ──────────────────────────────────────────────
Phase B : fisherInfo_gaussianReal = 1/v                         ← 0.5 session (1-1.5h)
        + integral_logDeriv_pdf_eq_zero_gaussian                   ~60-100 行
          ←──── 撤退ライン L-G3 (Phase A+B 部分 publish) ──────→
          ──────────────────────────────────────────────
Phase C : IsRegularDeBruijnHyp instance via gaussianReal_conv   ← 0.75-1 session (2-2.5h)
                                                                  ~80-150 行
          ←──── 撤退ライン L-G1 (scale-restricted form) ──────→
          ←──── 撤退ライン L-G2 (Gaussian semigroup 限定) ────→
          ──────────────────────────────────────────────
Phase D : deBruijn_identity_gaussian wrapper                    ← 0.25 session (0.5h)
                                                                  ~10-30 行
          ──────────────────────────────────────────────
Phase V : verify + library root + parent plan 更新              ← 0.25 session (0.5h)
```

### 段階的 ship 設計

- **Stage 0** (Phase A 完了, ~80-120 行): `IsRegularDensity (gaussianReal m v)` instance のみ publish。`integral_logDeriv_pdf_eq_zero` の Gaussian 起動が caller 側で可能になる
- **Stage 1** (Phase A + B 完了, ~140-220 行): + `fisherInfo_gaussianReal = 1/v` + `integral_logDeriv_pdf_eq_zero_gaussian` 完全 closed form。**L-G3 撤退ラインで切る場合の publish point**
- **Stage 2** (Phase A + B + C + D 完了, ~230-400 行): + `deBruijn_identity_gaussian` hypothesis なし形。**本 plan の理想到達点** = Cover-Thomas 17.7.2 の Gaussian 限定完成形
- **Stretch (任意)**: T2-D EPI seed の入口 `deBruijn_to_epi_integrand_gaussian` helper。**本 plan のスコープ外**

### 規模見積もり

| 自作要素 | 想定行数 | Phase |
|---|---|---|
| `pdf X P volume =ₐₛ gaussianPDFReal m v` bridge (`hX_law` + `rnDeriv_gaussianReal` + `pdf_def` 連鎖) | ~30-50 | A |
| `gaussianPDFReal m v` の `Differentiable ℝ` + `0 <` + `tail_*` + `integrable_deriv` + `integral_deriv_eq_zero` 5 field 充足 | ~50-80 | A |
| `fisherInfo_gaussianReal = 1/v` 本体 (variance 計算 + `log_gaussianPDFReal_eq` + `Real.deriv_log_comp_eq_logDeriv` 連鎖) | ~60-100 | B |
| `integral_logDeriv_pdf_eq_zero_gaussian` wrapper (Phase A instance を既存 theorem に渡す) | ~5-15 | B |
| `P.map (X + √s Z) = gaussianReal m (v + s.toNNReal)` (convolution = Gaussian の閉性) | ~30-60 | C |
| `differentialEntropy (P_s) = (1/2) log(2π e (v + s))` を `differentialEntropy_gaussianReal` で公式化 | ~15-30 | C |
| `HasDerivAt (fun s => (1/2) log(2π e (v + s))) (1/(2(v+t))) t` (`Real.hasDerivAt_log` chain) | ~25-50 | C |
| `derivAt_entropy_eq_half_fisher` field 充足 (RHS rewrite + `1/(2(v+t)) = (1/2) · 1/(v+t)`) | ~10-30 | C |
| `Z_law` field 充足 (hypothesis から直接) | ~2 | C |
| `deBruijn_identity_gaussian` wrapper (Phase C instance + `deBruijn_identity` 呼出) | ~10-20 | D |
| skeleton + imports + docstring + namespace | ~30-50 | A |
| **合計** | **~270-490** | |

中央予測 **~370 行** + 1.5-2 セッション (T2-F roadmap 上限 800 行に対し discharge 単独で +~400 行)。撤退ライン L-G3 なら ~140-220 行で着地。

### ファイル / モジュール構成

**判断: 新規ファイル `Common2026/Shannon/FisherInfoGaussian.lean` を作成** (`FisherInfo.lean` への末尾追記ではなく)。

理由:

- discharge は **Gaussian-specific instance + closed form 計算** で本質的に general Fisher info 本体とは独立
- 既存 `FisherInfo.lean` 222 行は汎用 + L-F1+L-F2 hypothesis pass-through の publish 単位として整っており、Gaussian 特殊化を混ぜると docstring / scope が散らかる
- 別 family の前例 (`Common2026/Shannon/DifferentialEntropy.lean` 1010 行は汎用 + Gaussian 特殊化を一括で持つが、それは E-9 で Gaussian-max-entropy が本体ゴールに含まれていたため。T2-F は汎用 Fisher info が本体、Gaussian discharge は **follow-up**)
- `FisherInfoGaussian.lean` は `FisherInfo.lean` を import するだけで済み、依存関係が明快
- T2-D EPI seed (後続) からは「general signature は `FisherInfo.lean`、Gaussian instance は `FisherInfoGaussian.lean`」と分けて cite できる

```
Common2026/Shannon/
  FisherInfo.lean                ← 既存 222 行、変更なし (Phase V で docstring に follow-up 言及を追記のみ)
  FisherInfoGaussian.lean        ← 新規 (~370 行)、本 plan の publish 単位
  DifferentialEntropy.lean       ← 既存 1010 行、変更なし
Common2026.lean                  ← Phase V で `import Common2026.Shannon.FisherInfoGaussian` 追記
```

**新規 import** (CLAUDE.md `Import Policy` 厳守、`import Mathlib` は使わない):

```lean
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Density
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Variance
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Common2026.Shannon.FisherInfo
import Common2026.Shannon.DifferentialEntropy
```

## 依存関係

完了済 / 利用可:

- [x] **既存 publish** (`Common2026/Shannon/FisherInfo.lean` 222 行):
  - `fisherInfo : Measure ℝ → ℝ≥0∞` (line 58)
  - `fisherInfoReal : Measure ℝ → ℝ` (line 93)
  - `IsRegularDensity` structure (line 125) — 6 field (`diff`, `pos`, `tail_bot`, `tail_top`, `integrable_deriv`, `integral_deriv_eq_zero`)
  - `integral_logDeriv_pdf_eq_zero` (line 151) — Phase B で `h_reg : IsRegularDensity` を受け取って結語、本 plan は instance を出すだけ
  - `IsRegularDeBruijnHyp` structure (line 186) — 2 field (`Z_law`, `derivAt_entropy_eq_half_fisher`)
  - `deBruijn_identity` (line 209) — Phase D で `h_reg : IsRegularDeBruijnHyp` を受け取って結語、本 plan は instance を出すだけ
  - `differentialEntropy_map_eq_integral_pdf_log_pdf` (line 106) — Phase A bridge
- [x] **既存 publish** (`Common2026/Shannon/DifferentialEntropy.lean` 1010 行):
  - `differentialEntropy : Measure ℝ → ℝ` (line 42)
  - `differentialEntropy_eq_integral_withDensity` (line 47)
  - `differentialEntropy_eq_integral_density` (line 60)
  - `integrable_density_log_density_of_gaussian` (line 81)
  - `log_gaussianPDFReal_eq` (line 391) — Phase B の `logDeriv` 計算で核
  - `differentialEntropy_gaussianReal` (line 406) — Phase C で convolution 側 entropy を直接出すのに使う
- [x] **Mathlib `Probability/Distributions/Gaussian/Real.lean`**:
  - `gaussianPDFReal_def` (line 51) — `(√(2 π v))⁻¹ * exp(-(x-μ)²/(2v))` の unfold
  - `gaussianPDFReal_pos` (line 61) — `hv : v ≠ 0` で `0 < gaussianPDFReal μ v x`
  - `measurable_gaussianPDFReal` (line 72)
  - `integrable_gaussianPDFReal` (line 82)
  - `lintegral_gaussianPDFReal_eq_one` (line 104) / `integral_gaussianPDFReal_eq_one` (line 121)
  - `rnDeriv_gaussianReal` (line 240) — `(gaussianReal μ v).rnDeriv volume =ₐₛ gaussianPDF μ v`
  - `integral_id_gaussianReal` (line 508) — `∫ x ∂(gaussianReal μ v) = μ`
  - `variance_fun_id_gaussianReal` (line 518) — `Var[x; gaussianReal μ v] = v`
  - `gaussianReal_const_mul` — `(c · X) law` (`c > 0` で `gaussianReal (c·μ) (c² · v)`)
  - `gaussianReal_conv_gaussianReal` (line 613) — `(gaussianReal m₁ v₁) ∗ (gaussianReal m₂ v₂) = gaussianReal (m₁+m₂) (v₁+v₂)`
  - `gaussianReal_add_gaussianReal_of_indepFun` (line 624) — `IndepFun X Y P` + 両 law が Gaussian で `P.map (X+Y) = gaussianReal (m₁+m₂) (v₁+v₂)`
- [x] **Mathlib `Analysis.SpecialFunctions.Log.Deriv`**:
  - `Real.hasDerivAt_log` (line 52) — `hx : x ≠ 0` で `HasDerivAt log x⁻¹ x`
  - `Real.deriv_log_comp_eq_logDeriv` (line 134) — `deriv (log ∘ f) x = logDeriv f x` (`f x ≠ 0`)
  - `HasDerivAt.log` (line 112) — composition for `log ∘ f`
- [x] **Mathlib `Analysis.SpecialFunctions.Exp`**: `Real.differentiable_exp`, `Real.tendsto_exp_neg_atTop_nhds_zero`
- [x] **Mathlib `MeasureTheory.Integral.IntegralEqImproper`**: `integral_deriv_eq_sub` 系 (Phase A `integral_deriv_eq_zero` field 用)
- [x] **Mathlib `Probability.Independence.Basic`**: `IndepFun`, `IndepFun.comp`, `IndepFun.symm`

**参考 (import しない)**:

- `Common2026/Shannon/Chernoff.lean` などの Tier 1 plumbing は完全に独立

---

## Phase 0 — 在庫再確認 + Gaussian PDF closed form 微分補題発掘 📋

### スコープ

`gaussianPDFReal m v` の `deriv` および `HasDerivAt` 系を Mathlib から発掘し、`IsRegularDensity` 6 field を埋める際の API gap を事前確定。本 plan は L-F2 撤退ライン記述 (inventory `fisher-info-mathlib-inventory.md:395`) を起点とし、その discharge 部分を主目的とする。

**proof-log**: no (整地のみ、結果は §依存関係 に反映)。

### Done 条件

- `gaussianPDFReal` の `Differentiable ℝ` instance / lemma が Mathlib にあるか確認 (なければ `Real.differentiable_exp` 連鎖で書く)
- `gaussianPDFReal` の `deriv` の closed form lemma が Mathlib にあるか確認 (なければ `HasDerivAt.exp` + `HasDerivAt.const_mul` 連鎖で書く)
- `gaussianPDFReal` の tail decay (`Tendsto ... atTop (𝓝 0)`) lemma が Mathlib にあるか確認
- `Real.deriv (fun s => Real.log (a + s)) t = 1 / (a + t)` 形の Mathlib 補題が存在するか確認 (`HasDerivAt.log` + `HasDerivAt.const_add` 経由で可)
- 上記 4 件の確認結果を Phase A / C の `## 失敗時 fallback` セクションに反映

### ステップ

- [ ] **0-1 loogle 確認** (推奨 5-8 件、各 ~8.5s):
  ```
  Differentiable _ (gaussianPDFReal _ _)
  HasDerivAt (gaussianPDFReal _ _) _ _
  deriv (gaussianPDFReal _ _) _
  Tendsto (gaussianPDFReal _ _) _ _
  Tendsto (fun x => Real.exp (-x^2)) Filter.atTop _
  HasDerivAt Real.log _ _
  ```
- [ ] **0-2 grep フォロー**: `rg -n "gaussianPDFReal.*deriv|deriv.*gaussianPDFReal" .lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/`
- [ ] **0-3 結果記録**: 発見 lemma / gap を §依存関係 と Phase A/C `失敗時 fallback` に追記。

### 工数感

~0 行 (調査のみ)。0.25 session。proof-log `no`。

### 失敗時 fallback

- なし (調査のみ、結果が悪ければ Phase A/C の見積を上ぶれさせるだけ)。

---

## Phase A — `IsRegularDensity (gaussianReal m v)` instance discharge 📋

### スコープ

`IsRegularDensity X P` (`FisherInfo.lean:125`) の 6 field を Gaussian の closed form で完全充足する instance を書く。Mathlib `gaussianPDFReal_pos` / `Real.differentiable_exp` / Gaussian tail decay 系で全 field を埋める。

**proof-log**: yes (`proof-log-fisher-info-gaussian-tier0.md` を Phase B 完了時に append)。

### Done 条件

- 補助補題 `pdf_eq_gaussianPDFReal_ae` (Gaussian `X` の pdf が `gaussianPDFReal` に ae 等しい): `(pdf X P volume) =ᵐ[volume] gaussianPDF m v`
- `isRegularDensity_gaussianReal_of_law` 本体: `P.map X = gaussianReal m v` 仮定下で `IsRegularDensity X P` を構成
- 6 field 充足:
  - `diff`: `Differentiable ℝ (fun x => gaussianPDFReal m v x)`
  - `pos`: `∀ x, 0 < gaussianPDFReal m v x` (`gaussianPDFReal_pos` 直接)
  - `tail_bot` / `tail_top`: `gaussianPDFReal m v` の atBot/atTop で 0 へ
  - `integrable_deriv`: `deriv (gaussianPDFReal m v)` の `Integrable`
  - `integral_deriv_eq_zero`: `∫ deriv (gaussianPDFReal m v) x dx = 0` (FTC + tail vanish)

### ステップ

- [ ] **A-1 `pdf_eq_gaussianPDFReal_ae` bridge** (~30-50 行):
  ```lean
  lemma pdf_eq_gaussianPDFReal_ae
      {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
      (X : Ω → ℝ) [HasPDF X P volume] {m : ℝ} {v : ℝ≥0}
      (hX_law : P.map X = gaussianReal m v) :
      (fun x => (pdf X P volume x).toReal) =ᵐ[volume]
        (fun x => gaussianPDFReal m v x)
  ```
  - `pdf X P volume =ᵐ[volume] (P.map X).rnDeriv volume` (Mathlib `pdf_def` ↔ `map_eq_withDensity_pdf` 経由)
  - `hX_law` 代入で `(P.map X).rnDeriv volume = (gaussianReal m v).rnDeriv volume`
  - `rnDeriv_gaussianReal` (`Real.lean:240`) で `=ᵐ gaussianPDF m v`
  - `gaussianPDF m v x = ENNReal.ofReal (gaussianPDFReal m v x)` (定義 `Real.lean:157`)
  - `(ENNReal.ofReal (gaussianPDFReal m v x)).toReal = gaussianPDFReal m v x` ← `gaussianPDFReal_nonneg`
  - **落とし穴**: `pdf X P volume` と `(P.map X).rnDeriv volume` の名前的等しさは Mathlib では `pdf_def` か `MeasureTheory.pdf` の定義に依存。`HasPDF X P volume` の場合 `pdf X P volume = (P.map X).rnDeriv volume` (ae) を確認。

- [ ] **A-2 `diff` field** (~10-15 行):
  - `Differentiable ℝ (fun x => gaussianPDFReal m v x)` を `gaussianPDFReal_def` で展開
  - `(√(2πv))⁻¹ * exp(-(x-μ)²/(2v))` は `const * exp ∘ polynomial` で `Real.differentiable_exp` + `polynomial.differentiable` の合成
  - **注意**: `diff` field は `(pdf X P volume x).toReal` に対する `Differentiable ℝ` を要求するが、`pdf_eq_gaussianPDFReal_ae` は ae 等式しか出さない。`Differentiable` は pointwise 要件なので **ae 等式では充足できない**。
  - **解決策**: `diff` field の定義を「ae 等式の代表元として `gaussianPDFReal m v` が `Differentiable` で、その `Differentiable` を `pdf` の一点単位の同形に押し付ける」必要あり。**fundamental fix**: `IsRegularDensity` の `diff` field を **`∃ g, Differentiable ℝ g ∧ pdf =ᵐ[volume] g`** に弱める判断 candidate。判断ログ #1 候補。
  - **代替**: `diff` field を `Differentiable ℝ (fun x => gaussianPDFReal m v x)` で直接構成し、`pdf =ᵐ gaussianPDFReal` の同形で他 field (`integral_logDeriv_pdf_eq_zero` 本体内の積分) を整合させる方針。Phase B `integral_logDeriv_pdf_eq_zero_gaussian` の証明側で ae 同形 rewrite を入れる。

- [ ] **A-3 `pos` field** (~3-5 行):
  - `gaussianPDFReal_pos μ v x hv` を直接適用
  - `pdf X P volume x` は ae 等式しかないので、`pos` field の "∀ x" が問題になる可能性あり (A-2 と同じ判断点)

- [ ] **A-4 `tail_bot` / `tail_top` fields** (~15-30 行):
  - `gaussianPDFReal m v x = (√(2πv))⁻¹ * exp(-(x-μ)²/(2v))`
  - `Tendsto (fun x => (x-μ)²/(2v)) atTop atTop` (polynomial の二次項)
  - `Real.tendsto_exp_neg_atTop_nhds_zero` で `exp(-(x-μ)²/(2v)) → 0`
  - `atBot` 側も同様 (`x → -∞` でも `(x-μ)² → +∞`)
  - **落とし穴**: Mathlib の Gaussian tail decay 補題が直接ないなら、`Real.tendsto_exp_neg_atTop_nhds_zero` + `Filter.Tendsto.comp` で組む

- [ ] **A-5 `integrable_deriv` field** (~15-25 行):
  - `deriv (gaussianPDFReal m v) x = -((x-μ)/v) * gaussianPDFReal m v x`
  - `polynomial * gaussianPDFReal` の integrability は Mathlib `integrable_rpow_mul_exp_neg_mul_sq` (Gaussian integral 系) で
  - もしくは Common2026 `DifferentialEntropy.lean` の `integrable_density_log_density_of_gaussian` 周辺で `(x - m)² * gaussianPDFReal` の integrable パターンが既出、それを流用

- [ ] **A-6 `integral_deriv_eq_zero` field** (~10-20 行):
  - `∫ deriv (gaussianPDFReal m v) x dx = (gaussianPDFReal m v)(R) - (gaussianPDFReal m v)(-R)` を `R → ∞` で limit
  - `tail_bot` + `tail_top` から右辺 → 0
  - Mathlib `integral_deriv_eq_sub` 系 (improper variant)、もしくは `MeasureTheory.integral_eq_zero_of_tendsto_atTop_atBot` 風の Mathlib 補題で

- [ ] **A-7 `isRegularDensity_gaussianReal_of_law` 統合**:
  ```lean
  theorem isRegularDensity_gaussianReal_of_law
      {Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
      (X : Ω → ℝ) [HasPDF X P volume] {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
      (hX_law : P.map X = gaussianReal m v) :
      IsRegularDensity X P :=
    { diff := ..., pos := ..., tail_bot := ..., tail_top := ...,
      integrable_deriv := ..., integral_deriv_eq_zero := ... }
  ```
  - 各 field を A-2 〜 A-6 の結果で埋める

- [ ] **A-8 verify**: `lake env lean Common2026/Shannon/FisherInfoGaussian.lean` clean (本 Phase 分の `sorry` ゼロ、Phase B-D は `sorry` 残し)。

### 工数感

~80-120 行 (A-1 ~40 + A-2 ~12 + A-3 ~5 + A-4 ~20 + A-5 ~20 + A-6 ~15 + A-7 ~10)。0.5-0.75 session。proof-log `yes` (Stage 0 publish 時点で append、Phase B と統合)。

### 失敗時 fallback

- **A-2 `diff` field が「∀ x で `pdf` 自体 differentiable」を要求して ae 等式では充足不能** (大確率で発生): 親 plan `FisherInfo.lean` の `IsRegularDensity` を弱める修正が要る。判断ログ #1 候補。修正内容: `diff` field を `Differentiable ℝ (fun x => (pdf X P volume x).toReal)` のままにし、本 plan で `pdf X P volume` を pointwise representative として `gaussianPDFReal m v` に置き換える追加補助補題 (`pdf X P volume = (fun x => ENNReal.ofReal (gaussianPDFReal m v x))` を `EventuallyEq` ではなく `eq` で書く形) を導入する、~30-50 行追加。**`Measure.HasPDF.pdf_eq_rnDeriv_map`** 経路を確認。
- **A-5 `deriv (gaussianPDFReal m v)` の Integrable が Mathlib 直接補題なし**: `gaussianPDFReal_def` を unfold して `(-((x-μ)/v)) * gaussianPDFReal m v x` 形に書き換え、`integrable_polynomial_mul_gaussian` 風の自前補題 ~30 行で吸収。最悪 `IsRegularDensity.integrable_deriv` field を **`integrable (deriv p)`** から **`∃ M, ∀ x, ‖deriv p x‖ ≤ M * gaussianPDFReal m v x`** に弱める判断 (判断ログ #1 と統合)。
- **A-6 `integral_deriv_eq_zero` が `MeasureTheory.integral_eq_sub` 等の improper variant 不在**: 手書きで `∫⁻ |deriv p| < ∞` から `Integrable` を出し、`hasDerivAt` の chain で `integral_Ioo_deriv_eq_sub` (有限区間) + tail limit を経由、~30 行。

---

## Phase B — Gaussian `integral_logDeriv_pdf_eq_zero` + `fisherInfo_gaussianReal = 1/v` 📋

### スコープ

Phase A `IsRegularDensity` instance を既存 `integral_logDeriv_pdf_eq_zero` (`FisherInfo.lean:151`) に渡して Gaussian 限定 wrapper を出す + `fisherInfo_gaussianReal = 1/v` (`FisherInfo.lean:plan` G-2 で見積られた ~80-120 行) の closed form 証明。

**proof-log**: yes (`proof-log-fisher-info-gaussian-stage1.md` を Stage 1 publish 時に append、Phase A と統合)。

### Done 条件

- `integral_logDeriv_pdf_eq_zero_gaussian`: hypothesis なし wrapper, `P.map X = gaussianReal m v` から直接 `∫ logDeriv pdf · pdf = 0`
- `fisherInfo_gaussianReal m hv : fisherInfo (gaussianReal m v) = ENNReal.ofReal (1 / (v : ℝ))`
- 補助補題 `logDeriv_gaussianPDFReal`: `logDeriv (gaussianPDFReal m v) x = -(x - m) / v` (Phase B の核)

### ステップ

- [ ] **B-1 `integral_logDeriv_pdf_eq_zero_gaussian` wrapper** (~5-15 行):
  ```lean
  theorem integral_logDeriv_pdf_eq_zero_gaussian
      {Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
      (X : Ω → ℝ) [HasPDF X P volume] {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
      (hX_law : P.map X = gaussianReal m v) :
      ∫ x, logDeriv (fun y => (pdf X P volume y).toReal) x
           * (pdf X P volume x).toReal ∂volume = 0 :=
    integral_logDeriv_pdf_eq_zero X (isRegularDensity_gaussianReal_of_law X hv hX_law)
  ```
  - Phase A instance を既存 theorem に渡すだけ

- [ ] **B-2 `logDeriv_gaussianPDFReal` 補助補題** (~30-50 行):
  ```lean
  lemma logDeriv_gaussianPDFReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
      logDeriv (gaussianPDFReal m v) x = -(x - m) / v
  ```
  - `logDeriv f x = deriv f x / f x` (`logDeriv_apply`)
  - `deriv (gaussianPDFReal m v) x` を `gaussianPDFReal_def` unfold で計算:
    - `deriv (fun y => (√(2πv))⁻¹ * exp(-(y-μ)²/(2v))) x`
    - `= (√(2πv))⁻¹ * deriv (fun y => exp(-(y-μ)²/(2v))) x`
    - `= (√(2πv))⁻¹ * exp(-(x-μ)²/(2v)) * (-(x-μ)/v)`
    - `= gaussianPDFReal m v x * (-(x-μ)/v)`
  - `gaussianPDFReal m v x ≠ 0` (`gaussianPDFReal_pos`) で `division` 可能
  - `(gaussianPDFReal m v x * (-(x-μ)/v)) / gaussianPDFReal m v x = -(x-μ)/v`
  - **代替**: `log_gaussianPDFReal_eq` (Common2026 `DifferentialEntropy.lean:391`) + `Real.deriv_log_comp_eq_logDeriv` で逆方向。`log (gaussianPDFReal m v x) = -(1/2) log(2πv) - (x-m)²/(2v)`、その `deriv` は `-(x-m)/v`、`Real.deriv_log_comp_eq_logDeriv` で `logDeriv` に。**こちらの方がやや短い (Common2026 既存補題再利用)**

- [ ] **B-3 `fisherInfo_gaussianReal` 本体** (~30-60 行):
  ```lean
  theorem fisherInfo_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
      fisherInfo (gaussianReal m v) = ENNReal.ofReal (1 / (v : ℝ))
  ```
  - **証明 4 ステップ**:
    1. `fisherInfo_eq_lintegral_logDeriv_sq` (`FisherInfo.lean:66`) で unfold
    2. `(gaussianReal m v).rnDeriv volume =ᵐ gaussianPDF m v` (`rnDeriv_gaussianReal`)
    3. `logDeriv ((·).rnDeriv volume).toReal x = logDeriv (gaussianPDFReal m v) x = -(x-m)/v` (B-2 適用、ae)
    4. `∫⁻ x, ENNReal.ofReal (((x-m)/v)²) * gaussianPDF m v x ∂volume = 1/v`
       - これは `∫ x, ((x-m)/v)² ∂(gaussianReal m v) = ∫ x, (x-m)²/v² ∂(gaussianReal m v) = Var/v² = v/v² = 1/v`
       - Mathlib `variance_fun_id_gaussianReal` (`Real.lean:518`) + `integral_id_gaussianReal` (`Real.lean:508`) で variance 計算
       - `ℝ≥0∞` 形と `ℝ` 形の往復は `lintegral_eq_ofReal_integral` (要 nonneg + integrable) で
  - **落とし穴**: `ℝ≥0∞` 上の `∫⁻ * ` を `ℝ` 上の `∫ ` に下ろす plumbing が散らかる可能性。`integral_gaussianReal_eq_integral_smul` (`DifferentialEntropy.lean:466` 周辺) を流用。
  - **落とし穴 2**: `ENNReal.ofReal (((-(x-m)/v))²) = ENNReal.ofReal (((x-m)/v)²)` の符号往復、`neg_sq` で吸収

- [ ] **B-4 verify**: `lake env lean Common2026/Shannon/FisherInfoGaussian.lean` clean。Phase A + B 本体 0 sorry、Phase C + D は `sorry` 残し。**Stage 1 publish 候補時点** = L-G3 で切るならここで `Common2026.lean` 編入 (Phase V を前倒し可)。

### 工数感

~60-100 行 (B-1 ~10 + B-2 ~35 + B-3 ~45 + plumbing ~10)。0.5 session。proof-log `yes`。

### 失敗時 fallback

- **B-3 `ℝ≥0∞` ↔ `ℝ` plumbing が 60 行を超える**: `fisherInfoReal_gaussianReal m hv : fisherInfoReal (gaussianReal m v) = 1 / v` を先に証明 (`ℝ` 上で variance 計算)、`ENNReal.ofReal_toReal` の plumbing は `fisherInfo_gaussianReal` で吸収 (~20 行追加)。
- **B-2 `logDeriv_gaussianPDFReal` を `log_gaussianPDFReal_eq` 経路で 50 行超え**: 直接 `gaussianPDFReal_def` を unfold して `HasDerivAt.exp` + chain で deriv を出し、`div` で `logDeriv` に、~25 行に圧縮。

---

## Phase C — `IsRegularDeBruijnHyp` Gaussian instance discharge (convolution = Gaussian 経由) 📋

### スコープ

`IsRegularDeBruijnHyp X Z P t` (`FisherInfo.lean:186`) を Gaussian X + 標準正規 Z で完全 discharge。鍵となる **convolution = Gaussian の閉性**を使い、heat-eq / dominated bound を経由せずに `derivAt_entropy_eq_half_fisher` field を **`(1/2) log(2π e (v + s))` の direct derivative** で構成する。

**proof-log**: yes (Phase D と統合、`proof-log-fisher-info-gaussian-stage2.md`)。

### Done 条件

- 補助補題 `map_X_add_sqrt_t_mul_Z_eq_gaussianReal`: `P.map (X + √t · Z) = gaussianReal m (v + t.toNNReal)`
- 補助補題 `differentialEntropy_map_X_add_sqrt_s_mul_Z`: `differentialEntropy (P.map (X + √s Z)) = (1/2) log(2π e (v + s))` (closed form)
- 補助補題 `hasDerivAt_log_const_add` (もし Mathlib にない場合): `HasDerivAt (fun s => (1/2) log(c + s)) (1/(2(c+t))) t` for `c + t > 0`
- 補助補題 `fisherInfo_map_X_add_sqrt_t_mul_Z`: `(fisherInfo (P.map (X + √t Z))).toReal = 1/(v + t)`
- `isRegularDeBruijnHyp_gaussianReal_of_law` 本体: `Z_law` + `derivAt_entropy_eq_half_fisher` の 2 field を構成

### ステップ

- [ ] **C-1 `(√t · Z).law = gaussianReal 0 t.toNNReal`** (~10-20 行):
  - `hZ_law : P.map Z = gaussianReal 0 1`
  - `√t > 0` (`ht : 0 < t` から `Real.sqrt_pos.mpr ht`)
  - `gaussianReal_const_mul (√t) Z law`: `P.map (fun ω => √t * Z ω) = gaussianReal (√t * 0) ((√t)² · 1)` (Mathlib に存在を要確認、なければ `Measure.map_map` + `gaussianReal_const_mul` 直接適用)
  - `(√t)² = t` (Mathlib `Real.sq_sqrt`、`ht.le` から)
  - 結果: `P.map (√t · Z) = gaussianReal 0 t.toNNReal`

- [ ] **C-2 `IndepFun X (√t · Z) P`** (~10-15 行):
  - `hXZ : IndepFun X Z P`
  - `IndepFun.comp` (Mathlib `Probability/Independence/Basic.lean`、`IndepFun X Z P → IndepFun (f ∘ X) (g ∘ Z) P` for measurable `f, g`)
  - `f := id` / `g := (√t * ·)`
  - **落とし穴**: `IndepFun.const_mul_right` の Mathlib 直接補題があるか要確認 (`loogle "IndepFun" "const_mul"`)

- [ ] **C-3 `map_X_add_sqrt_t_mul_Z_eq_gaussianReal`** (~10-20 行):
  ```lean
  lemma map_X_add_sqrt_t_mul_Z_eq_gaussianReal
      ... (hX_law : P.map X = gaussianReal m v) (hZ_law : P.map Z = gaussianReal 0 1)
      (hXZ : IndepFun X Z P) {t : ℝ} (ht : 0 < t) :
      P.map (fun ω => X ω + Real.sqrt t * Z ω) = gaussianReal m (v + t.toNNReal)
  ```
  - C-1 + C-2 + `gaussianReal_add_gaussianReal_of_indepFun` (`Real.lean:624`)
  - `m + 0 = m`、`v + t.toNNReal` の simp

- [ ] **C-4 `differentialEntropy_map_X_add_sqrt_s_mul_Z` (closed form)** (~15-30 行):
  - C-3 の結果を `differentialEntropy_gaussianReal` (Common2026 `DifferentialEntropy.lean:406`) に代入
  - `differentialEntropy (gaussianReal m (v + s.toNNReal)) = (1/2) * log(2π e (v + s))`
  - **注意**: `s.toNNReal` は `s ≥ 0` の前提を要する (`hs : 0 ≤ s`)。`HasDerivAt` の近傍では `s` が `t` の近傍を動くので `s > 0` ⇒ `s.toNNReal = s` で OK

- [ ] **C-5 `HasDerivAt` of `(1/2) log(2π e (v + s))` at `s = t`** (~25-50 行):
  ```lean
  have h_deriv : HasDerivAt
      (fun s => (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (v + s)))
      (1 / (2 * (v + t)))
      t
  ```
  - `Real.hasDerivAt_log` (`Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean:52`): `HasDerivAt log x⁻¹ x` for `x ≠ 0`
  - `HasDerivAt.comp` で `log ∘ (fun s => 2π e (v + s))` の derivative
  - chain で `(1/(2π e (v+t))) * (2π e) = 1/(v+t)`
  - `(1/2) * 1/(v+t) = 1/(2(v+t))`
  - **落とし穴**: `2π e (v + s) > 0` 仮定の dispatch、`v + t > 0` from `hv ≠ 0` + `ht > 0`

- [ ] **C-6 `fisherInfo_map_X_add_sqrt_t_mul_Z`** (~5-15 行):
  - C-3 + Phase B `fisherInfo_gaussianReal` で `(fisherInfo (gaussianReal m (v + t.toNNReal))).toReal = 1/(v + t)`
  - `ENNReal.ofReal_toReal` (`v + t > 0` から `1/(v+t) > 0`)

- [ ] **C-7 `isRegularDeBruijnHyp_gaussianReal_of_law` 統合** (~15-30 行):
  ```lean
  theorem isRegularDeBruijnHyp_gaussianReal_of_law
      ... (hX_law : ...) (hZ_law : ...) {t : ℝ} (ht : 0 < t) :
      IsRegularDeBruijnHyp X Z P t :=
    { Z_law := hZ_law,
      derivAt_entropy_eq_half_fisher := by
        -- LHS: (fun s => differentialEntropy (P.map (X + √s Z)))
        -- = (fun s => (1/2) * log(2π e (v + s)))  via C-4
        -- HasDerivAt at t with derivative 1/(2(v + t))  via C-5
        -- RHS: (1/2) * (fisherInfo (P.map (X + √t Z))).toReal
        -- = (1/2) * 1/(v + t)  via C-6
        -- = 1/(2(v + t))  by ring
        sorry }
  ```
  - LHS rewriting: `HasDerivAt.congr_of_eventuallyEq` で C-4 の closed form に書き換え、s が t の近傍で `s > 0` を要するので open neighborhood `Set.Ioi 0` で `EventuallyEq`
  - RHS equality: C-6 + `ring`

- [ ] **C-8 verify**: `lake env lean Common2026/Shannon/FisherInfoGaussian.lean` clean、Phase A + B + C 本体 0 sorry、Phase D は `sorry` 残し。

### 工数感

~80-150 行 (C-1 ~15 + C-2 ~12 + C-3 ~15 + C-4 ~25 + C-5 ~35 + C-6 ~10 + C-7 ~25 + plumbing ~15)。0.75-1 session。proof-log `yes` (Phase D と統合)。

### 失敗時 fallback

- **C-2 `IndepFun.const_mul_right` の Mathlib 直接補題不在**: `IndepFun.comp` を `f := id` / `g := (· * √t)` で起動、~15 行で組む。最悪 `MeasurableSpace.measurable_const_mul` + `IndepFun` 定義 unfold で 30 行。
- **C-4 `s.toNNReal` の `s ≥ 0` 前提が `HasDerivAt` の filter で扱いづらい**: `EventuallyEq` を `Set.Ioi 0` (open neighborhood) 上で出し、`HasDerivAt.congr_of_eventuallyEq` で書き換え (Mathlib `HasDerivAt.congr_of_eventuallyEq` を要確認)。または `s` を `s.toNNReal` ではなく `⟨s, _⟩` と書く別表現に変える、~10 行追加。
- **C-5 `HasDerivAt.comp` の chain で `log (2π e (v + s))` 全体の chain rule が散らかる**: 補助補題 `hasDerivAt_log_affine` (`HasDerivAt (fun s => log (a + b * s)) (b/(a + b*t)) t` for `a + b*t > 0`) を private で書く、~30 行。
- **C-7 LHS rewriting の `HasDerivAt.congr_of_eventuallyEq` の filter 整合で詰まる**: `HasDerivAt` を直接構成 (`(fun s => differentialEntropy ...) = (fun s => (1/2) log ...)` を全 `s ∈ Set.Ioi 0` で示し、その上で `HasDerivAt.congr` 1 発)、~20 行追加。

---

## Phase D — `deBruijn_identity_gaussian` hypothesis なし wrapper publish 📋

### スコープ

Phase C `isRegularDeBruijnHyp_gaussianReal_of_law` を既存 `deBruijn_identity` (`FisherInfo.lean:209`) に渡して **hypothesis なし形の `deBruijn_identity_gaussian`** を publish。本 plan の最終 ship point。

**proof-log**: yes (Stage 2 publish 時点で `proof-log-fisher-info-gaussian-stage2.md` を append、Phase C と統合)。

### Done 条件

- `deBruijn_identity_gaussian` 主定理 (signature §Goal 参照、hypothesis なし形)
- (任意) `deBruijn_identity_gaussian_standard`: `X ∼ 𝒩(0, 1)` (`m = 0, v = 1`) 特殊化 (Cover-Thomas 17.7.2 textbook 形)
- (任意) `deBruijn_identity_gaussian_sanity_check`: `X = 0` (Dirac) ではなく `X ∼ 𝒩(0, v)` での verification

### ステップ

- [ ] **D-1 `deBruijn_identity_gaussian` wrapper** (~10-20 行):
  ```lean
  theorem deBruijn_identity_gaussian
      {Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
      (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
      [HasPDF X P volume]
      {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
      (hX_law : P.map X = gaussianReal m v)
      (hZ_law : P.map Z = gaussianReal 0 1)
      {t : ℝ} (ht : 0 < t) :
      HasDerivAt
        (fun s => differentialEntropy (P.map (fun ω => X ω + Real.sqrt s * Z ω)))
        ((1/2) * (fisherInfo (P.map (fun ω => X ω + Real.sqrt t * Z ω))).toReal)
        t :=
    deBruijn_identity X Z hX hZ hXZ ht
      (isRegularDeBruijnHyp_gaussianReal_of_law X Z hX hZ hXZ hv hX_law hZ_law ht)
  ```

- [ ] **D-2 (任意) `deBruijn_identity_gaussian_standard`** (~5-15 行):
  - `m := 0`, `v := 1`, `hv := one_ne_zero` で特殊化
  - Cover-Thomas 17.7.2 textbook 形に最も近い publish 形

- [ ] **D-3 verify**: `lake env lean Common2026/Shannon/FisherInfoGaussian.lean` clean、Phase A + B + C + D 本体 0 sorry。**Stage 2 publish = 本 plan 完成形**。

### 工数感

~10-30 行 (D-1 ~15 + D-2 ~10 + plumbing ~5)。0.25 session。proof-log `yes`。

### 失敗時 fallback

- なし (Phase C で本体は完成、D は wrapper のみ)。

---

## Phase V — verify + `Common2026.lean` 編入 + parent plan 更新 📋

### スコープ

`FisherInfoGaussian.lean` 最終 verify + `Common2026.lean` 編入 + 親 plan (`fisher-info-moonshot-plan.md`) の L-F1+L-F2 退避記録に「Gaussian 限定で discharge 完了」を追記。

**proof-log**: no (整地のみ)。

### Done 条件

- `lake env lean Common2026/Shannon/FisherInfoGaussian.lean` clean (0 sorry, 0 warning)
- `Common2026.lean` に `import Common2026.Shannon.FisherInfoGaussian` 追記
- `lake env lean Common2026.lean` clean
- 親 plan `fisher-info-moonshot-plan.md` の判断ログに「(YYYY-MM-DD) Gaussian discharge 完了」エントリ append
- 親 plan `fisher-info-moonshot-plan.md` Status 行を更新 (「Gaussian instance discharge 完了 — `deBruijn_identity_gaussian` hypothesis なし形 publish」)
- 親 plan 進捗ブロック Phase C / Phase D に 🔄 → ✅ (Gaussian 限定で完了) もしくは備考行追加

### ステップ

- [ ] **V-1 final verify**: `lake env lean Common2026/Shannon/FisherInfoGaussian.lean` で 0 sorry / 0 warning 確認
- [ ] **V-2 library root 編入**: `Common2026.lean` の Shannon 系 import 区画に `import Common2026.Shannon.FisherInfoGaussian` 追記、`lake env lean Common2026.lean` clean 確認
- [ ] **V-3 親 plan 更新** (`docs/shannon/fisher-info-moonshot-plan.md`):
  - Status 行に「Gaussian discharge 完了」を追記
  - 判断ログに新エントリ append (例: 「(YYYY-MM-DD) (Phase C+D follow-up) Gaussian 限定で L-F1+L-F2 hypothesis を完全 discharge、`deBruijn_identity_gaussian` hypothesis なし形を `FisherInfoGaussian.lean` で publish (~370 行)。一般 X の `IsRegularDeBruijnHyp` discharge は `fisher-info-heat-eq-plan.md` 等への defer 継続。」)
  - 進捗ブロックの Phase C / Phase D に「Gaussian 限定で discharge 完了 (→ `fisher-info-gaussian-discharge-moonshot-plan.md`)」リンク追加
- [ ] **V-4 docstring 更新**:
  - `FisherInfo.lean` 先頭の module docstring (line 31-39 「撤退ライン (本実装で適用済)」) に「Gaussian 限定 discharge は `FisherInfoGaussian.lean` で完了」を追記 (本 file は最小 1-2 行の追記のみ、L-F1+L-F2 自体の publish 状態は変えない)
  - `FisherInfoGaussian.lean` の module docstring に「Cover-Thomas 17.7.2 の Gaussian 限定完成形」と明示、T2-D EPI seed の入口準備としての位置付けを明示

### 工数感

~5-15 行 (V-1 ~0 + V-2 ~3 + V-3 ~10 + V-4 ~5)。0.25 session。proof-log `no`。

### 失敗時 fallback

- なし (verify-only Phase)。

---

## 撤退ライン

### Scope 縮小ライン

- **L-G1**: **scale-restricted form のみで publish** (~250-350 行)
  - 発動条件: Phase C で `gaussianReal_const_mul` / `gaussianReal_add_gaussianReal_of_indepFun` の組み立てで `√t · Z` の law 計算が想定の 40 行を超え (`IndepFun.comp` の dispatch が散らかる)
  - 縮退案: `deBruijn_identity_gaussian` の signature に **`hZ_t_law : P.map (√t · Z) = gaussianReal 0 t.toNNReal`** を追加 hypothesis として要求し、Phase C-1 + C-2 + C-3 (合計 ~40 行) を caller 側に押し付け。Phase C-4 〜 C-7 は完走で残り、本 plan publish 価値は維持 (T2-D EPI seed から「law を渡せば de Bruijn が出る」状態で cite 可能)。

- **L-G2**: **Gaussian + Gaussian convolution semigroup 限定の variance-shift 直接形** (~300-400 行)
  - 発動条件: Phase C-5 で `HasDerivAt.comp` の chain rule が散らかる (`log (2π e (v + s))` の derivative 計算が想定の 50 行を超える)
  - 縮退案: `deBruijn_identity_gaussian` を **「variance-shift 形」** で publish:
    ```lean
    theorem deBruijn_identity_gaussian_variance_shift
        {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ} (ht : 0 < t) :
        HasDerivAt
          (fun s => differentialEntropy (gaussianReal m (v + s.toNNReal)))
          (1 / (2 * (v + t)))
          t
    ```
    - `differentialEntropy_gaussianReal` + `Real.hasDerivAt_log` の **measure-level でない直接 closed form** で publish、~80-100 行 (Phase C-1 〜 C-3 を完全に skip)
    - T2-D EPI seed から見ると「`(X + √t · Z)` が再び Gaussian になる事実」は caller 側で示す形になるが、Cover-Thomas 17.7.2 の textbook 起動には十分

- **L-G3**: **Phase A + B のみで部分 publish** (~140-220 行)
  - 発動条件: Phase C / D が 1 セッションで詰む (Phase A の `IsRegularDensity` の `diff` field 修正が親 plan 構造に波及して時間溶ける、もしくは Phase C-5 / C-7 が `HasDerivAt.congr_of_eventuallyEq` の filter で詰む)
  - 縮退案: `isRegularDensity_gaussianReal_of_law` + `fisherInfo_gaussianReal = 1/v` + `integral_logDeriv_pdf_eq_zero_gaussian` のみで publish。`deBruijn_identity_gaussian` は別 seed (`fisher-info-gaussian-debruijn-plan.md`) に分離。本 plan の Stage 1 publish point に着地。

### 自作 plumbing 肥大ライン

- **L-P1 (Phase A `diff` field の pointwise vs ae 問題)**: A-2 で予測している通り、`IsRegularDensity.diff` field を `Differentiable ℝ (fun x => (pdf X P volume x).toReal)` のまま埋めると ae 同形しか出ない pdf に対して pointwise 要件を充足できない可能性大 (確率 中-高、本 plan で最も注意要)。
  - 緩和: 親 plan `FisherInfo.lean` の `IsRegularDensity.diff` を **`∃ g, Differentiable ℝ g ∧ ∀ᵐ x ∂volume, (pdf X P volume x).toReal = g x`** に弱める修正を `FisherInfoGaussian.lean` 着手前に親 plan に back-port する判断 candidate。判断ログ #1 で記録する想定。**親 file 修正のためグローバル変更**、L-G3 縮退検討も同時に。

- **L-P2 (Mathlib `gaussianPDFReal` の `deriv` closed form 不在)**: Phase A-5 + B-2 で `deriv (gaussianPDFReal m v) x = -((x-m)/v) * gaussianPDFReal m v x` の Mathlib 直接補題が無い (Phase 0 の loogle 結果次第)。
  - 緩和: `gaussianPDFReal_def` を unfold して `HasDerivAt.exp` + `HasDerivAt.const_mul` + chain で組む、~30 行で済む見込み。最悪自前で `deriv_gaussianPDFReal` 補助補題を private で書く、~40 行追加。

- **L-P3 (Mathlib `IndepFun.const_mul_right` の有無)**: Phase C-2 で `IndepFun X (√t · Z)` を出す際の Mathlib lemma 不在可能性。
  - 緩和: `IndepFun.comp` を `g := (√t * ·)` で起動、`Measurable.const_mul` で measurability を出し、~15 行で組む。

- **L-P4 (`(fisherInfo (gaussianReal m v)).toReal = 1/v` の `ENNReal` plumbing 散らかり)**: Phase C-6 / D で `(fisherInfo ...).toReal` を `1/(v + t)` に下ろす際の `ENNReal.ofReal_toReal` plumbing が `ENNReal.ofReal (1/(v+t))` ↔ `1/(v+t)` 往復で詰まる可能性。
  - 緩和: 補助補題 `fisherInfoReal_gaussianReal m hv : fisherInfoReal (gaussianReal m v) = 1/v` を Phase B-3 で先に出し、`(fisherInfo ...).toReal = fisherInfoReal ...` 経由で plumbing を吸収、~10 行追加。

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| **`IsRegularDensity.diff` field の pointwise vs ae 問題** (Phase A-2、L-P1) | **中-高** | **高** (親 plan 修正に波及、Phase A +30-50 行 or L-G3 発動) | 親 plan `IsRegularDensity.diff` を ae 形に back-port する判断を Phase A 着手前に確定。判断ログ #1 候補。最悪 L-G3 で Stage 1 publish に着地。 |
| **`gaussianPDFReal` の `deriv` closed form Mathlib lemma 不在** (Phase A-5, B-2、L-P2) | 中 | 中 (Phase A/B +20-40 行) | `HasDerivAt.exp` + chain で組む。`gaussianPDFReal_def` unfold 経由で 30 行に圧縮、必要なら `deriv_gaussianPDFReal` private 補助補題を書く。 |
| **`IndepFun X (√t · Z)` の Mathlib lemma 不在** (Phase C-2、L-P3) | 中 | 低-中 (Phase C +10-15 行) | `IndepFun.comp` + `Measurable.const_mul` で 15 行で組む。 |
| **`HasDerivAt (fun s => (1/2) log(2π e (v + s)))` の chain rule が散らかる** (Phase C-5) | 中 | 中-高 (Phase C +30-50 行 or L-G2 発動) | 補助補題 `hasDerivAt_log_affine` を private で書く (~30 行)。最悪 L-G2 で variance-shift form のみに縮退、Cover-Thomas 17.7.2 textbook 形は維持。 |
| **`s.toNNReal` の `s ≥ 0` 前提が `HasDerivAt` の filter で扱いづらい** (Phase C-4, C-7) | 中 | 中 (Phase C +20-30 行) | `EventuallyEq` を `Set.Ioi 0` (open neighborhood) 上で出し、`HasDerivAt.congr_of_eventuallyEq` で書き換え。filter 整合で詰むなら `HasDerivAt` 直接構成に切替。 |
| **`Measure.conv` vs `lconvolution` のどちらを起動するか不明確** (Phase C 補助) | 低 | 低 (Phase C +10 行) | 本 plan は **`Measure.conv` 経路を一切経由しない** — `gaussianReal_add_gaussianReal_of_indepFun` で `P.map (X + √t Z)` を直接 Gaussian に書き換えるため。convolution PDF representation (Tier 2 一般版で必要だった Phase D-2) は不要。 |
| **`ENNReal.ofReal_toReal` plumbing 散らかり** (Phase B-3, C-6、L-P4) | 中 | 低-中 (Phase B/C +10-20 行) | `fisherInfoReal_gaussianReal` 派生を Phase B-3 で先取り、`.toReal` ↔ `ENNReal.ofReal` 往復は `fisherInfoReal` 経由で吸収。 |
| **`pdf X P volume` と `gaussianPDFReal m v` の ae 等式から pointwise 等式が出ない場合の field 整合** (Phase A-3 `pos` field) | 中-高 | 中 (Phase A +30 行 or L-P1 同時発動) | L-P1 と統合、`pos` field も ae 形に弱める判断。または `(pdf X P volume x).toReal = gaussianPDFReal m v x` を **`pdf_def` + `rnDeriv_gaussianReal` で pointwise (ae で 1 つの representative) ** として書く plumbing、~20 行。 |
| **`differentialEntropy_gaussianReal` の signature が `s : ℝ≥0` で本 plan の `s : ℝ` と型不一致** (Phase C-4) | 中 | 低-中 (Phase C +15 行) | `s.toNNReal` の往復で吸収、`s > 0` ⇒ `((s.toNNReal : ℝ≥0) : ℝ) = s` (`Real.coe_toNNReal` of nonneg)。 |
| **Phase A 〜 D を 1.5-2 セッションで完遂不能** (規模見積上振れ) | 中 | 中 (next month に持ち越し) | Stage 1 (Phase A + B、~140-220 行) と Stage 2 (Phase C + D、~90-180 行) を別セッションに分割設計。L-G3 発動で Stage 1 で publish も可。 |
| **Mathlib `gaussianReal_const_mul` の signature 違い** (Phase C-1) | 低 | 低 (Phase C +5 行) | 本 plan 着手時に Phase 0 loogle で確定、不一致なら `Measure.map_map` で手動 reshape。 |

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(2026-05-19) (Phase 0 / A-2) `IsRegularDensity` の a.e.-representative back-port (L-P1 確定)**: Phase A-2 で予測した「`IsRegularDensity.diff` field が pdf の pointwise differentiability を要求するが `pdf X P volume` は ae 等式しか出ない」問題が `pdf_def` + `rnDeriv_gaussianReal` の経路確認で確定。`FisherInfo.lean` の `IsRegularDensity` を **a.e.-representative 形** (新 field `density : ℝ → ℝ`, `pdf_ae_eq : (pdf X P volume).toReal =ᵐ density`、他 field は `density` を参照) に back-port、`structure ... : Prop` を `structure ...` (非 Prop) に変更。`integral_logDeriv_pdf_eq_zero` も結論を `h_reg.density` 経由に書き換え、a.e.-representative の pointwise 性質で証明完走。`FisherInfo.lean` 222 行 → 236 行 (+14 行)。`Common2026.Shannon.FisherInfo` の `IsRegularDensity` consumer は `integral_logDeriv_pdf_eq_zero` のみで、外部から `IsRegularDensity` 自体を使う publish なしのため互換性 break なし。

2. **(2026-05-19) (Phase B-3) L-G3 撤退発動 — `fisherInfo` 定義の representative-依存性 flaw**: Phase B-3 の `fisherInfo (gaussianReal m v) = 1/v` 着手中に、`fisherInfo` 定義の本質的な flaw を発見。`FisherInfo.lean:58` の `fisherInfo μ := ∫⁻ x, ofReal((logDeriv (fun y => (μ.rnDeriv volume y).toReal) x)^2) * μ.rnDeriv volume x ∂volume` は **`Measure.rnDeriv` の opaque representative** に依存。`Measure.rnDeriv` は `Classical.choose` で定義され (`Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean:80`)、`rnDeriv_gaussianReal` も `=ᵐ` の ae 等式しか提供しない。実際の representative は generic に non-differentiable で `logDeriv ((rnDeriv).toReal) = 0` ae、ゆえに `fisherInfo (gaussianReal m v) = 0` (mathematical な `1/v` ではなく)。
   - L-G3 撤退発動: Phase B-3 / C / D を skip、Stage 1 publish (Phase A + Phase B-1/B-2 = `IsRegularDensity` instance + `integral_logDeriv_pdf_eq_zero_gaussian` wrapper + helpers) で着地。
   - 影響: 親 plan `fisher-info-moonshot-plan.md` Tier 2 の L-F1+L-F2 退避は **Gaussian 限定でも完全 discharge 不能**、`fisherInfo` 定義の redefinition (a.e.-class 不変な形、例: differential entropy 微分経由) を要する別 seed が follow-up に必要。
   - Phase A 副産物の `IsRegularDensity` instance + score-vanish wrapper は publish 価値あり (Cover-Thomas 17.7 score function の Gaussian 場 closed form として独立に使える)。

3. **(2026-05-19) (Phase V) Stage 1 publish 着地**: `FisherInfoGaussian.lean` 329 行 (新規) + `FisherInfo.lean` +14 行 (back-port) = 計 +343 行で着地。0 sorry, 0 warning, `lake env lean` clean。中央予測 ~370 行に対し未着地 Phase C+D の差分 ~90-180 行を差し引いて Phase A+B 系統の規模感は計画 ~140-220 行とほぼ一致。
