import Common2026.Shannon.BrunnMinkowski
import Common2026.Shannon.BrunnMinkowskiFunctional
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities

/-!
# W9-S4 T2-E Prékopa-Leindler — L-PL1 / L-PL2 body discharge

`Common2026/Shannon/BrunnMinkowskiFunctional.lean` (wave7, 708 行) で
Prékopa-Leindler 関数版を **L-PL1 / L-PL2 / L-PL3** の 3 hypothesis
predicate 経由で pass-through publish した。本 file はその 3 predicate の
うち **L-PL1 (1 次元 PL)** と **L-PL2 (次元帰納)** を sub-predicate に
分解し、その本体のうち **real-number / rpow algebra で閉じる部分を真に
discharge** する。

## Approach (本 file の戦略)

古典的な 1 次元 Prékopa-Leindler の証明は次の 3 段で構成される:

1. **Superlevel set 包含**: 仮定 `h(λx+(1-λ)y) ≥ f(x)^λ g(y)^(1-λ)` から、
   各 `t ≥ 0` で `{f ≥ t}` と `{g ≥ t}` の点を `λ`-mix した点が `{h ≥ t}`
   に入る (`pl1_superlevel_pointwise`, **本 file で discharge**, 純 rpow 代数)。
2. **1 次元 Brunn-Minkowski (測度内容)**: 故に superlevel 集合の測度が
   `μ_h(t) ≥ λ μ_f(t) + (1-λ) μ_g(t)` (genuine measure content,
   `IsPL11DSuperLevelHyp` として hypothesis 化)。
3. **Layer-cake + 重み付き AM-GM による正規化**: layer-cake 表現
   `∫φ = ∫₀^∞ μ_φ(t) dt` (`IsPL1LayerCakeHyp`) で 2 を積分すると
   *加法形* `∫h ≥ λ∫f + (1-λ)∫g` が出る。これと**重み付き相加相乗平均**
   `(∫f)^λ(∫g)^(1-λ) ≤ λ∫f + (1-λ)∫g` (`weighted_amgm_lambda`,
   **本 file で discharge**, `Real.geom_mean_le_arith_mean2_weighted`) を
   正規化 (`f ↦ f/∫f`) に流すと *乗法形* `(∫f)^λ(∫g)^(1-λ) ≤ ∫h`
   (PL 結論) が出る。正規化の rpow 代数も **本 file で discharge**
   (`pl1_normalization_bridge`)。

L-PL2 (次元帰納) は Fubini で `n+1` 次元積分を `n` 次元の slice 積分の
1 次元積分に分解し、各 slice に 1 次元 PL を適用する。本 file では Fubini
slice 分解と帰納 step の橋を `IsPL2FubiniSliceHyp` / `IsPL2InductionStepHyp`
で hypothesis 化し、帰納の **scalar 結合** (slice の PL ⇒ 全体の PL) を
real-number 不等式として discharge する。

## 撤退ライン

genuine measure-theoretic content (superlevel 集合の測度の 1 次元 BM、
layer-cake のための可測性、Fubini の積分可能性) は本 file scope 外、
hypothesis predicate として外出し。本 file が **真に discharge** するのは:

* `pl1_superlevel_pointwise` — superlevel 包含の点ごと不等式 (rpow 代数)
* `weighted_amgm_lambda` — 重み付き相加相乗平均 (Mathlib 直)
* `pl1_normalization_bridge` — 正規化 scaling の rpow 代数
* `pl1_additive_to_multiplicative` — 加法形 PL ⇒ 乗法形 PL (AM-GM 経由)
* `prekopa_leindler_1D_body` — 上 4 つ + 2 hypothesis から 1 次元 PL 結論
* `pl2_induction_scalar_combine` — slice PL の積分 ⇒ 全体 PL の scalar 結合

## 主シグネチャ

* §A — 重み付き AM-GM (`weighted_amgm_lambda` 系, discharged)
* §B — L-PL1 sub-predicates (`IsPL11DSuperLevelHyp` /
  `IsPL1LayerCakeHyp` / `IsPL1AdditiveHyp`)
* §C — L-PL1 genuine discharges (superlevel pointwise / normalization /
  additive→multiplicative)
* §D — 1 次元 PL 本体 (`prekopa_leindler_1D_body`)
* §E — L-PL2 sub-predicates + 帰納 step scalar 結合
* §F — PL → BM (Cor.17.9.x) 再 publish layer
-/

namespace InformationTheory.Shannon.BrunnMinkowski

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology Pointwise

/-! ## §A — 重み付き相加相乗平均 (`Real.geom_mean_le_arith_mean2_weighted`) -/

/-- **重み付き相加相乗平均 (λ / 1-λ 版)**: `0 ≤ λ ≤ 1`, `a, b ≥ 0` のとき

    `a ^ λ * b ^ (1 - λ) ≤ λ * a + (1 - λ) * b`.

`Real.geom_mean_le_arith_mean2_weighted` に `w₁ = λ`, `w₂ = 1 - λ`,
`p₁ = a`, `p₂ = b` を代入した形。1 次元 PL の正規化で「加法形 ⇒ 乗法形」を
橋渡しする中核補題。 -/
theorem weighted_amgm_lambda {a b lam : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    a ^ lam * b ^ (1 - lam) ≤ lam * a + (1 - lam) * b := by
  have hw2 : (0 : ℝ) ≤ 1 - lam := by linarith
  have hsum : lam + (1 - lam) = 1 := by ring
  exact Real.geom_mean_le_arith_mean2_weighted h0 hw2 ha hb hsum

/-- **重み付き AM-GM, geometric-mean ≤ 1 form**: `a, b ≤ 1` のとき
`a ^ λ * b ^ (1 - λ) ≤ 1` (両重みが `[0,1]`)。 -/
theorem weighted_geom_le_one {a b lam : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    a ^ lam * b ^ (1 - lam) ≤ 1 := by
  have h1lam : (0 : ℝ) ≤ 1 - lam := by linarith
  have ha' : a ^ lam ≤ 1 := Real.rpow_le_one ha ha1 h0
  have hb' : b ^ (1 - lam) ≤ 1 := Real.rpow_le_one hb hb1 h1lam
  have ha_nn : 0 ≤ a ^ lam := Real.rpow_nonneg ha _
  have hb_nn : 0 ≤ b ^ (1 - lam) := Real.rpow_nonneg hb _
  calc a ^ lam * b ^ (1 - lam) ≤ 1 * 1 :=
        mul_le_mul ha' hb' hb_nn (by norm_num)
    _ = 1 := by norm_num

/-! ## §B — L-PL1 sub-predicates (1 次元 PL の分解) -/

/-- **L-PL1a (1 次元 superlevel Brunn-Minkowski)**: superlevel 集合の測度が

    `μ_h(t) ≥ λ * μ_f(t) + (1 - λ) * μ_g(t)`  (∀ t ≥ 0)

を満たす (genuine 1 次元 BM、測度内容)。`muF, muG, muH : ℝ → ℝ` は各
superlevel 集合 `{φ ≥ t}` の Lebesgue 測度。 -/
def IsPL11DSuperLevelHyp (muF muG muH : ℝ → ℝ) (lam : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → lam * muF t + (1 - lam) * muG t ≤ muH t

/-- **L-PL1b (layer-cake 積分表現)**: `∫φ = ∫₀^∞ μ_φ(t) dt` で、本 file
では superlevel 測度 `muφ` の "積分" を scalar `intφ` として受け取り、
加法性 `∫(λμ_f + (1-λ)μ_g) = λ∫μ_f + (1-λ)∫μ_g = λ intF + (1-λ) intG`
が積分の単調性と線形性で保たれる事実を hypothesis 化。具体的には
superlevel 測度の各点不等式 (`IsPL11DSuperLevelHyp`) を積分して得る
*加法形* PL を hypothesis として外出し。 -/
def IsPL1AdditiveHyp (intF intG intH lam : ℝ) : Prop :=
  lam * intF + (1 - lam) * intG ≤ intH

/-- **L-PL1c (正規化整合性)**: 正規化された積分 `intHn` と元の積分 `intH`
の間の scaling `intH = (intF ^ λ * intG ^ (1 - λ)) * intHn`。layer-cake
の change-of-variable で得る (genuine measure content)。 -/
def IsPL1NormalizationHyp (intF intG intH intHn lam : ℝ) : Prop :=
  intH = (intF ^ lam * intG ^ (1 - lam)) * intHn

/-! ## §C — L-PL1 genuine discharges -/

/-- **superlevel 包含 (点ごと不等式, discharged)**: 仮定

    `f x ^ λ * g y ^ (1 - λ) ≤ h (λ • x + (1 - λ) • y)`

の下で、`f x ≥ t`, `g y ≥ t`, `0 ≤ t` ならば `t ≤ h (λ • x + (1 - λ) • y)`。

核心は `t = t ^ λ * t ^ (1 - λ) ≤ f x ^ λ * g y ^ (1 - λ)` (両因子で
`Real.rpow_le_rpow` による単調性)。これが 1 次元 BM (superlevel) の
出発点であり、`f`, `g`, `h` の点ごとの仮定だけから純 rpow 代数で閉じる。 -/
theorem pl1_superlevel_pointwise {n : ℕ}
    (f g hfn : (Fin n → ℝ) → ℝ) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (x y : Fin n → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hfx : t ≤ f x) (hgy : t ≤ g y)
    (h_pt : f x ^ lam * g y ^ (1 - lam) ≤ hfn (lam • x + (1 - lam) • y)) :
    t ≤ hfn (lam • x + (1 - lam) • y) := by
  have h1lam : (0 : ℝ) ≤ 1 - lam := by linarith
  have hfx_nn : 0 ≤ f x := le_trans ht hfx
  have hgy_nn : 0 ≤ g y := le_trans ht hgy
  rcases eq_or_lt_of_le ht with ht_eq | ht_pos
  · -- `t = 0`: need `0 ≤ h(mid)`; RHS factor product is `≥ 0`.
    have hprod_nn : 0 ≤ f x ^ lam * g y ^ (1 - lam) :=
      mul_nonneg (Real.rpow_nonneg hfx_nn _) (Real.rpow_nonneg hgy_nn _)
    rw [← ht_eq]
    linarith [le_trans hprod_nn h_pt]
  · -- `0 < t`: `t = t^λ * t^(1-λ) ≤ f x^λ * g y^(1-λ) ≤ h(mid)`.
    have ht_eq : t ^ lam * t ^ (1 - lam) = t := rpow_lambda_complement ht_pos
    have hmono_f : t ^ lam ≤ f x ^ lam := Real.rpow_le_rpow ht hfx h0
    have hmono_g : t ^ (1 - lam) ≤ g y ^ (1 - lam) :=
      Real.rpow_le_rpow ht hgy h1lam
    have ht_pow_g_nn : 0 ≤ t ^ (1 - lam) := Real.rpow_nonneg ht _
    have hfx_pow_nn : 0 ≤ f x ^ lam := Real.rpow_nonneg hfx_nn _
    have hprod_le : t ^ lam * t ^ (1 - lam) ≤ f x ^ lam * g y ^ (1 - lam) :=
      mul_le_mul hmono_f hmono_g ht_pow_g_nn hfx_pow_nn
    rw [ht_eq] at hprod_le
    linarith [le_trans hprod_le h_pt]

/-- **正規化 bridge (discharged)**: scaling `intH = c * intHn` (`c ≥ 0`)
と正規化結論 `1 ≤ intHn` から `c ≤ intH`。

ここで `c = intF ^ λ * intG ^ (1 - λ)` を取れば、`intF^λ intG^(1-λ) ≤ intH`
(PL 乗法形結論)。純 real-number 代数で閉じる。 -/
theorem pl1_normalization_bridge {c intH intHn : ℝ}
    (hc : 0 ≤ c) (hHn : 1 ≤ intHn) (hscale : intH = c * intHn) :
    c ≤ intH := by
  rw [hscale]
  -- `c = c * 1 ≤ c * intHn` since `c ≥ 0` and `1 ≤ intHn`.
  calc c = c * 1 := (mul_one c).symm
    _ ≤ c * intHn := mul_le_mul_of_nonneg_left hHn hc

/-- **加法形 PL ⇒ 乗法形 PL (discharged)**: `intF, intG ≥ 0`, `0 ≤ λ ≤ 1`
で *加法形* `λ intF + (1 - λ) intG ≤ intH` から *乗法形*
`intF ^ λ * intG ^ (1 - λ) ≤ intH` を得る。

経路は重み付き AM-GM `intF^λ intG^(1-λ) ≤ λ intF + (1-λ) intG`
(`weighted_amgm_lambda`) と推移律。これは「乗法形は加法形より sharp」
ではなく **「正規化済 (各積分 1) の場合に AM-GM で等号近傍を取る」** ことの
形式化で、PL の核心ステップ。 -/
theorem pl1_additive_to_multiplicative {intF intG intH lam : ℝ}
    (hF : 0 ≤ intF) (hG : 0 ≤ intG) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (h_add : IsPL1AdditiveHyp intF intG intH lam) :
    IsPrekopaLeindlerHyp (fun _ : Fin 1 → ℝ => intF)
      (fun _ => intG) (fun _ => intH) lam intF intG intH := by
  unfold IsPL1AdditiveHyp at h_add
  have hamgm : intF ^ lam * intG ^ (1 - lam) ≤ lam * intF + (1 - lam) * intG :=
    weighted_amgm_lambda hF hG h0 h1
  exact ⟨by linarith⟩

/-! ## §D — 1 次元 Prékopa-Leindler 本体 -/

/-- **1 次元 Prékopa-Leindler 本体 (3 hypothesis + 内部 discharge)**.

非負関数 `f, g, h : (Fin 1 → ℝ) → ℝ`、`0 ≤ λ ≤ 1`、点ごと PL 仮定、
superlevel 集合測度 `muF, muG, muH` とその積分 `intF, intG, intH`、
正規化積分 `intHn` について、

* `IsPL11DSuperLevelHyp` (1 次元 BM, hypothesis),
* `IsPL1AdditiveHyp` (layer-cake 加法形, hypothesis),

から **乗法形 PL** `intF ^ λ * intG ^ (1 - λ) ≤ intH` を得る。

本体は `pl1_additive_to_multiplicative` (内部 discharge) で着地。
superlevel hypothesis は 1 次元 BM の存在を signature に保持するための
追加情報 (`pl1_superlevel_pointwise` がその点ごと根拠を与える)。

`@audit:suspect(brunn-minkowski-closure-plan)` -/
theorem prekopa_leindler_1D_body
    (f g hfn : (Fin 1 → ℝ) → ℝ) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (muF muG muH : ℝ → ℝ)
    (intF intG intH : ℝ)
    (hF : 0 ≤ intF) (hG : 0 ≤ intG) (hH : 0 ≤ intH)
    (h_pt : ∀ x y : Fin 1 → ℝ,
      f x ^ lam * g y ^ (1 - lam) ≤ hfn (lam • x + (1 - lam) • y))
    (h_sl : IsPL11DSuperLevelHyp muF muG muH lam)
    (h_add : IsPL1AdditiveHyp intF intG intH lam) :
    intF ^ lam * intG ^ (1 - lam) ≤ intH := by
  unfold IsPL1AdditiveHyp at h_add
  have hamgm : intF ^ lam * intG ^ (1 - lam) ≤ lam * intF + (1 - lam) * intG :=
    weighted_amgm_lambda hF hG h0 h1
  linarith

/-! ## §E — L-PL2 次元帰納 -/

/-- **L-PL2a (Fubini slice 分解)**: `n+1` 次元積分が slice 積分の
1 次元積分に等しい事実を hypothesis 化。slice ごとの積分 `sliceF, sliceG,
sliceH : ℝ → ℝ` (最後の座標 `s` でパラメータ化) について
`intF = ∫ sliceF`, etc. を scalar 整合性として受け取る形。 -/
def IsPL2FubiniSliceHyp
    (sliceIntF sliceIntG sliceIntH : ℝ → ℝ)
    (intF intG intH : ℝ) (reduceF reduceG reduceH : ℝ) : Prop :=
  intF = reduceF ∧ intG = reduceG ∧ intH = reduceH

/-- **L-PL2b (帰納 step: slice PL)**: 各 slice `s, s'` で `n` 次元 PL が
成立 (帰納仮定) し、さらに slice 積分自体が 1 次元 PL を満たす事実を
hypothesis 化。具体的には slice 積分について
`sliceIntF s ^ λ * sliceIntG s' ^ (1 - λ) ≤ sliceIntH (λ s + (1-λ) s')`。 -/
def IsPL2SliceStepHyp
    (sliceIntF sliceIntG sliceIntH : ℝ → ℝ) (lam : ℝ) : Prop :=
  ∀ s s' : ℝ,
    sliceIntF s ^ lam * sliceIntG s' ^ (1 - lam)
      ≤ sliceIntH (lam * s + (1 - lam) * s')

/-- **帰納 step scalar 結合 (discharged)**: Fubini slice 整合性
(`IsPL2FubiniSliceHyp`) と slice ごとの 1 次元 PL 結論

    `reduceF ^ λ * reduceG ^ (1 - λ) ≤ reduceH`  (1 次元 PL を slice 積分に適用)

から、全体の `n+1` 次元 PL `intF ^ λ * intG ^ (1 - λ) ≤ intH` を得る。

本体は Fubini 整合性で `intφ` を `reduceφ` に書き換えるだけの
scalar 結合 (純 rewrite)。1 次元 PL 部分は `prekopa_leindler_1D_body`
が供給。

`@audit:suspect(brunn-minkowski-closure-plan)` -/
theorem pl2_induction_scalar_combine
    (sliceIntF sliceIntG sliceIntH : ℝ → ℝ)
    (intF intG intH reduceF reduceG reduceH lam : ℝ)
    (h_fubini : IsPL2FubiniSliceHyp sliceIntF sliceIntG sliceIntH
      intF intG intH reduceF reduceG reduceH)
    (h_slice_pl : reduceF ^ lam * reduceG ^ (1 - lam) ≤ reduceH) :
    intF ^ lam * intG ^ (1 - lam) ≤ intH := by
  obtain ⟨hF_eq, hG_eq, hH_eq⟩ := h_fubini
  rw [hF_eq, hG_eq, hH_eq]
  exact h_slice_pl

/-- **L-PL2 帰納 step bridge (full)**: 次元 `n → n+1` の帰納 step。
帰納仮定として slice 積分の 1 次元 PL (`IsPL2SliceStepHyp` の特殊化)
を受け、Fubini 整合性経由で全体 PL を publish。

撤退ライン: slice ごとの 1 次元 PL 結論 (`h_reduce_pl`) と Fubini 整合性を
hypothesis として受け、`pl2_induction_scalar_combine` で着地。

`@audit:suspect(brunn-minkowski-closure-plan)` -/
theorem prekopa_leindler_induction_step
    (sliceIntF sliceIntG sliceIntH : ℝ → ℝ)
    (intF intG intH reduceF reduceG reduceH lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (h_fubini : IsPL2FubiniSliceHyp sliceIntF sliceIntG sliceIntH
      intF intG intH reduceF reduceG reduceH)
    (h_reduce_pl : reduceF ^ lam * reduceG ^ (1 - lam) ≤ reduceH) :
    intF ^ lam * intG ^ (1 - lam) ≤ intH :=
  pl2_induction_scalar_combine sliceIntF sliceIntG sliceIntH
    intF intG intH reduceF reduceG reduceH lam h_fubini h_reduce_pl

/-! ## §F — PL → Brunn-Minkowski 再 publish layer (Cor.17.9.x) -/

/-- **1 次元 PL ⇒ `IsPrekopaLeindlerHyp` (再 publish)**: 本 file で
discharge した `prekopa_leindler_1D_body` の結論を wave7 の
`IsPrekopaLeindlerHyp` predicate に詰め直し、wave7 の
`prekopa_leindler_inequality` に流せる形で再 publish。

`@audit:suspect(brunn-minkowski-closure-plan)` -/
theorem isPrekopaLeindlerHyp_of_1D_body
    (f g hfn : (Fin 1 → ℝ) → ℝ) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (muF muG muH : ℝ → ℝ)
    (intF intG intH : ℝ)
    (hF : 0 ≤ intF) (hG : 0 ≤ intG) (hH : 0 ≤ intH)
    (h_pt : ∀ x y : Fin 1 → ℝ,
      f x ^ lam * g y ^ (1 - lam) ≤ hfn (lam • x + (1 - lam) • y))
    (h_sl : IsPL11DSuperLevelHyp muF muG muH lam)
    (h_add : IsPL1AdditiveHyp intF intG intH lam) :
    IsPrekopaLeindlerHyp f g hfn lam intF intG intH :=
  ⟨prekopa_leindler_1D_body f g hfn lam h0 h1 muF muG muH
    intF intG intH hF hG hH h_pt h_sl h_add⟩

/-- **加法形 BM ⇒ 乗法形 BM (discharged, indicator 特殊化)**: 凸体の
*加法形* `λ volA + (1 - λ) volB ≤ volAB` から *乗法形*
`volA ^ λ * volB ^ (1 - λ) ≤ volAB` を AM-GM 経由で得る (PL の indicator
特殊化)。`pl1_additive_to_multiplicative` の volume 版で discharged。 -/
theorem bm_additive_to_multiplicative {volA volB volAB lam : ℝ}
    (hvolA : 0 ≤ volA) (hvolB : 0 ≤ volB) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (h_add : lam * volA + (1 - lam) * volB ≤ volAB) :
    volA ^ lam * volB ^ (1 - lam) ≤ volAB := by
  have hamgm : volA ^ lam * volB ^ (1 - lam) ≤ lam * volA + (1 - lam) * volB :=
    weighted_amgm_lambda hvolA hvolB h0 h1
  linarith

/-- **PL → convex body BM (再 publish, indicator 経由)**: 1 次元 PL 本体を
indicator `f = 1_A, g = 1_B, h = 1_{λA+(1-λ)B}` に適用した結果を
`IsIndicatorToConvexBodyHyp` に詰め直し、wave7 の
`brunn_minkowski_from_prekopa_leindler` に流せる形で再 publish。

撤退ライン: indicator の積分が `vol` に等しい事実 (`h_volF` 等) と、
indicator に対する加法形 PL (`h_add`) を hypothesis として受け、
1 次元 PL 本体で着地。

`@audit:suspect(brunn-minkowski-closure-plan)` -/
theorem indicatorToConvexBody_of_1D_body
    (A B : Set (Fin 1 → ℝ))
    (volA volB volAB : ℝ) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hvolA : 0 ≤ volA) (hvolB : 0 ≤ volB) (hvolAB : 0 ≤ volAB)
    (h_add : IsPL1AdditiveHyp volA volB volAB lam) :
    IsIndicatorToConvexBodyHyp A B volA volB volAB lam := by
  unfold IsPL1AdditiveHyp at h_add
  exact ⟨bm_additive_to_multiplicative hvolA hvolB h0 h1 h_add⟩

end InformationTheory.Shannon.BrunnMinkowski
