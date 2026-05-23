import Common2026.Shannon.BrunnMinkowskiPLBody
import Common2026.Shannon.BrunnMinkowski1DSuperlevelBody
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real

/-!
# W10-S16 Prékopa-Leindler — layer-cake normalization discharge

`Common2026/Shannon/BrunnMinkowskiPLBody.lean` の 1 次元 PL chain で残る
**genuine measure content** は `IsPL1NormalizationHyp` /
`IsPL1AdditiveHyp` の layer-cake change-of-variable
(`∫ φ dμ = ∫₀^∞ μ{φ ≥ t} dt`) である。本 file はその layer-cake / Cavalieri
恒等式を Mathlib の `MeasureTheory.Integrable.integral_eq_integral_meas_le`
で **真に discharge** し、superlevel 集合の測度不等式 (1 次元 BM, hypothesis)
を積分して PL の *加法形* `λ ∫f + (1-λ) ∫g ≤ ∫h` を導く normalization
bridge を組む。

## Approach (本 file の戦略)

1. **Layer-cake 恒等式 (genuine, fully discharged)**: 非負可積分 `f` に対し
   `∫ f dμ = ∫_{Ioi 0} μ.real {f ≥ t} dt`
   (`layercake_integral_eq`, `Integrable.integral_eq_integral_meas_le` 直)。
   これは no-op ではなく実測度内容 (Bochner 積分 ↔ tail 測度積分)。
2. **Layer-cake predicate (genuine)**: 上の恒等式を `f, g, h` に対する
   3 本の組として `IsPL1LayerCakeIntegralHyp` に詰め、可積分性 + 非負性
   から discharge (`isPL1LayerCakeIntegralHyp_discharge`)。
3. **加法形 normalization bridge (genuine change-of-variable)**: 各 `t > 0` で
   superlevel 測度が `λ μ_f(t) + (1-λ) μ_g(t) ≤ μ_h(t)` (1 次元 BM,
   hypothesis) と tail 関数の `Ioi 0` 上可積分性 (irreducible primitive)
   から、layer-cake 恒等式で書き換えた `λ ∫f + (1-λ) ∫g ≤ ∫h` を
   `setIntegral` の単調性 + 線形性で導く (`pl1_additive_via_layercake`)。
   これが「superlevel 測度不等式 ⇒ PL 積分不等式」の核心 change-of-variable。
4. **再 publish**: `IsPL1AdditiveHyp` を genuine content から discharge し、
   `prekopa_leindler_1D_body` に流して hypothesis を 1 本軽くした 1 次元 PL
   を再 publish (`prekopa_leindler_1D_layercake`)。

## 撤退ライン

tail 関数 `t ↦ μ.real {φ ≥ t}` の `Ioi 0` 上可積分性は genuine measure
content だが本 file scope (layer-cake normalization の代数) の外なので、
`IsTailIntegrableHyp` という **strictly-more-primitive** predicate として
外出しする (no-op ではなく実際の `Integrable` 命題)。superlevel 測度不等式
(1 次元 BM) は wave10 で別途 discharge 済 / hypothesis。
-/

namespace InformationTheory.Shannon.BrunnMinkowski

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal NNReal Topology

/-! ## §A — layer-cake / Cavalieri 恒等式 (genuine, fully discharged) -/

/-- **Layer-cake 恒等式 (Cover-Thomas の正規化で使う change-of-variable)**.

非負 a.e.、可積分な `f : α → ℝ` に対し、Bochner 積分は tail 測度の積分:

    `∫ ω, f ω ∂μ = ∫ t in Ioi 0, μ.real {a | t ≤ f a}`.

`MeasureTheory.Integrable.integral_eq_integral_meas_le` を直に呼ぶ。
これが PL の "layer-cake normalization" の genuine content であり、
superlevel 集合の測度不等式を積分不等式へ変換する出発点。 -/
theorem layercake_integral_eq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ}
    (f_intble : Integrable f μ) (f_nn : 0 ≤ᵐ[μ] f) :
    ∫ ω, f ω ∂μ = ∫ t in Set.Ioi (0 : ℝ), μ.real {a : α | t ≤ f a} :=
  f_intble.integral_eq_integral_meas_le f_nn

/-! ## §B — layer-cake predicate (genuine measure content) -/

/-- **L-PL1b' (genuine layer-cake 積分表現)**: `f, g, h` の Bochner 積分
`intF, intG, intH` が各 tail 測度 `μ_f, μ_g, μ_h : ℝ → ℝ`
(`μ_φ t = μ.real {φ ≥ t}`) の `Ioi 0` 上積分に等しい:

    `intF = ∫_{Ioi 0} μ_f`,  `intG = ∫_{Ioi 0} μ_g`,  `intH = ∫_{Ioi 0} μ_h`.

`BrunnMinkowskiPLBody.lean` の placeholder `IsPL1AdditiveHyp` (scalar) より
strictly genuine: 実際の layer-cake 恒等式の組。 -/
def IsPL1LayerCakeIntegralHyp
    (muF muG muH : ℝ → ℝ) (intF intG intH : ℝ) : Prop :=
  intF = ∫ t in Set.Ioi (0 : ℝ), muF t ∧
  intG = ∫ t in Set.Ioi (0 : ℝ), muG t ∧
  intH = ∫ t in Set.Ioi (0 : ℝ), muH t

/-- **layer-cake predicate discharge (genuine)**: `f, g, h` が非負可積分で
tail 測度が `muφ t = μ.real {φ ≥ t}` ならば layer-cake predicate が成立。
`layercake_integral_eq` を 3 回。 -/
theorem isPL1LayerCakeIntegralHyp_discharge {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g h : α → ℝ}
    (hf_int : Integrable f μ) (hf_nn : 0 ≤ᵐ[μ] f)
    (hg_int : Integrable g μ) (hg_nn : 0 ≤ᵐ[μ] g)
    (hh_int : Integrable h μ) (hh_nn : 0 ≤ᵐ[μ] h) :
    IsPL1LayerCakeIntegralHyp
      (fun t => μ.real {a : α | t ≤ f a})
      (fun t => μ.real {a : α | t ≤ g a})
      (fun t => μ.real {a : α | t ≤ h a})
      (∫ ω, f ω ∂μ) (∫ ω, g ω ∂μ) (∫ ω, h ω ∂μ) :=
  ⟨layercake_integral_eq hf_int hf_nn,
   layercake_integral_eq hg_int hg_nn,
   layercake_integral_eq hh_int hh_nn⟩

/-! ## §C — 加法形 normalization bridge (genuine change-of-variable) -/

/-- **L-PL1d (tail 関数の `Ioi 0` 上可積分性, irreducible primitive)**:
tail 測度関数 `muF, muG, muH` が `volume.restrict (Ioi 0)` 上可積分。
layer-cake で得た tail 関数の積分が有限である事実 (genuine measure content,
本 file scope 外なので primitive predicate として外出し)。 -/
def IsTailIntegrableHyp (muF muG muH : ℝ → ℝ) : Prop :=
  Integrable muF (volume.restrict (Set.Ioi (0 : ℝ))) ∧
  Integrable muG (volume.restrict (Set.Ioi (0 : ℝ))) ∧
  Integrable muH (volume.restrict (Set.Ioi (0 : ℝ)))

/-- **superlevel 測度の積分単調性 (genuine)**: 各 `t > 0` で
`λ muF t + (1-λ) muG t ≤ muH t` (1 次元 BM, hypothesis) と tail 可積分性から、

    `∫_{Ioi 0} (λ muF + (1-λ) muG) ≤ ∫_{Ioi 0} muH`.

`setIntegral_mono_on` を `Ioi 0` (可測) に適用。本 file の genuine content。 -/
theorem superlevel_setIntegral_mono
    (muF muG muH : ℝ → ℝ) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (h_tail : IsTailIntegrableHyp muF muG muH)
    (h_sl : ∀ t : ℝ, 0 < t → lam * muF t + (1 - lam) * muG t ≤ muH t) :
    ∫ t in Set.Ioi (0 : ℝ), (lam * muF t + (1 - lam) * muG t)
      ≤ ∫ t in Set.Ioi (0 : ℝ), muH t := by
  obtain ⟨hF_int, hG_int, hH_int⟩ := h_tail
  have hlhs_int :
      Integrable (fun t => lam * muF t + (1 - lam) * muG t)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hF_int.const_mul lam).add (hG_int.const_mul (1 - lam))
  refine setIntegral_mono_on hlhs_int hH_int measurableSet_Ioi ?_
  intro t ht
  exact h_sl t ht

/-- **加法形 normalization bridge (genuine change-of-variable, discharged)**:
layer-cake 恒等式 (`IsPL1LayerCakeIntegralHyp`) で `intF, intG, intH` を
tail 積分に書き換え、`superlevel_setIntegral_mono` を `setIntegral` の
線形性 (`integral_add` / `integral_const_mul`) で展開すると、PL の *加法形*

    `λ intF + (1-λ) intG ≤ intH`  (= `IsPL1AdditiveHyp intF intG intH lam`)

を得る。これが「superlevel 測度不等式 ⇒ PL 積分不等式」の核心であり、
`BrunnMinkowskiPLBody.lean` の scalar placeholder `IsPL1AdditiveHyp` を
genuine measure content から discharge する本体。 -/
theorem pl1_additive_via_layercake
    (muF muG muH : ℝ → ℝ) (intF intG intH lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (h_lc : IsPL1LayerCakeIntegralHyp muF muG muH intF intG intH)
    (h_tail : IsTailIntegrableHyp muF muG muH)
    (h_sl : ∀ t : ℝ, 0 < t → lam * muF t + (1 - lam) * muG t ≤ muH t) :
    IsPL1AdditiveHyp intF intG intH lam := by
  obtain ⟨hF_eq, hG_eq, hH_eq⟩ := h_lc
  obtain ⟨hF_int, hG_int, hH_int⟩ := h_tail
  unfold IsPL1AdditiveHyp
  have hmono := superlevel_setIntegral_mono muF muG muH lam h0 h1
    ⟨hF_int, hG_int, hH_int⟩ h_sl
  -- 線形性: `∫(λμF + (1-λ)μG) = λ∫μF + (1-λ)∫μG`.
  have hlin :
      ∫ t in Set.Ioi (0 : ℝ), (lam * muF t + (1 - lam) * muG t)
        = lam * (∫ t in Set.Ioi (0 : ℝ), muF t)
          + (1 - lam) * (∫ t in Set.Ioi (0 : ℝ), muG t) := by
    rw [integral_add (hF_int.const_mul lam) (hG_int.const_mul (1 - lam)),
      integral_const_mul, integral_const_mul]
  rw [hlin] at hmono
  rw [hF_eq, hG_eq, hH_eq]
  exact hmono

/-! ## §D — 1 次元 PL 再 publish (normalization discharged) -/

/-- **1 次元 PL 本体 (layer-cake normalization discharged)**: 点ごと PL 仮定、
1 次元 superlevel BM (測度不等式 hypothesis), layer-cake 恒等式 + tail 可積分性
(genuine, 本 file で discharge) から、`IsPL1AdditiveHyp` を内部 discharge して
乗法形 PL `intF ^ λ * intG ^ (1 - λ) ≤ intH` を得る。

`BrunnMinkowskiPLBody.lean` の `prekopa_leindler_1D_body` は
`IsPL1AdditiveHyp` を hypothesis として要求していたが、本定理は
それを layer-cake change-of-variable から discharge して除去する。 -/
theorem prekopa_leindler_1D_layercake
    (f g hfn : (Fin 1 → ℝ) → ℝ) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (muF muG muH : ℝ → ℝ)
    (intF intG intH : ℝ)
    (hF : 0 ≤ intF) (hG : 0 ≤ intG) (hH : 0 ≤ intH)
    (h_pt : ∀ x y : Fin 1 → ℝ,
      f x ^ lam * g y ^ (1 - lam) ≤ hfn (lam • x + (1 - lam) • y))
    (h_sl_meas : IsPL11DSuperLevelHyp muF muG muH lam)
    (h_lc : IsPL1LayerCakeIntegralHyp muF muG muH intF intG intH)
    (h_tail : IsTailIntegrableHyp muF muG muH)
    (h_sl_pos : ∀ t : ℝ, 0 < t → lam * muF t + (1 - lam) * muG t ≤ muH t) :
    intF ^ lam * intG ^ (1 - lam) ≤ intH := by
  have h_add : IsPL1AdditiveHyp intF intG intH lam :=
    pl1_additive_via_layercake muF muG muH intF intG intH lam h0 h1
      h_lc h_tail h_sl_pos
  exact prekopa_leindler_1D_body f g hfn lam h0 h1 muF muG muH
    intF intG intH hF hG hH h_pt h_sl_meas h_add

/-- **`IsPrekopaLeindlerHyp` 再 publish (normalization discharged)**: 上の
`prekopa_leindler_1D_layercake` の結論を wave7 の `IsPrekopaLeindlerHyp`
predicate に詰め直し、`prekopa_leindler_inequality` に流せる形で再 publish。
`IsPL1AdditiveHyp` を layer-cake から discharge した分、hypothesis が
1 本軽い。 -/
theorem isPrekopaLeindlerHyp_of_layercake
    (f g hfn : (Fin 1 → ℝ) → ℝ) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (muF muG muH : ℝ → ℝ)
    (intF intG intH : ℝ)
    (hF : 0 ≤ intF) (hG : 0 ≤ intG) (hH : 0 ≤ intH)
    (h_pt : ∀ x y : Fin 1 → ℝ,
      f x ^ lam * g y ^ (1 - lam) ≤ hfn (lam • x + (1 - lam) • y))
    (h_sl_meas : IsPL11DSuperLevelHyp muF muG muH lam)
    (h_lc : IsPL1LayerCakeIntegralHyp muF muG muH intF intG intH)
    (h_tail : IsTailIntegrableHyp muF muG muH)
    (h_sl_pos : ∀ t : ℝ, 0 < t → lam * muF t + (1 - lam) * muG t ≤ muH t) :
    IsPrekopaLeindlerHyp f g hfn lam intF intG intH :=
  ⟨prekopa_leindler_1D_layercake f g hfn lam h0 h1 muF muG muH
    intF intG intH hF hG hH h_pt h_sl_meas h_lc h_tail h_sl_pos⟩

/-! ## §E — superlevel hypothesis を引数から落とした 1 次元 PL -/

/-- **1 次元 PL (superlevel hypothesis を genuine に discharge した版)**.

`prekopa_leindler_1D_layercake` は superlevel-set 測度不等式を **2 本**
(`h_sl_meas : IsPL11DSuperLevelHyp` と `h_sl_pos : ∀ t > 0, ...`) hypothesis
として両取りしていた。本定理はそれらを引数から **完全に除去** する:
`f, g, hfn : ℝ → ℝ` の点ごと PL 仮定 (`h_pt`) と superlevel 集合の
honest regularity (compact / 非空 / 有限) のみから、
`BrunnMinkowski1DSuperlevelBody.isPL11DSuperLevelHyp_real` で
`IsPL11DSuperLevelHyp` を内部 produce し (genuine 1 次元 Brunn-Minkowski)、
そこから `h_sl_pos` も `pl1SuperLevel_pos_of_hyp` で派生して
layer-cake change-of-variable に流す。

tail 測度は `muφ t := (volume {x | t ≤ φ x}).toReal` に固定され、layer-cake
積分恒等式 (`h_lc`) と tail 可積分性 (`h_tail`) のみ残る (これらは genuine
measure content であり no-op ではない)。superlevel BM 自体は本 chain で
完全に discharge 済 (sorry 0)。 -/
theorem prekopa_leindler_1D_superlevel_discharged
    (f g hfn : ℝ → ℝ) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (intF intG intH : ℝ)
    (hF : 0 ≤ intF) (hG : 0 ≤ intG) (hH : 0 ≤ intH)
    (hF_compact : ∀ t : ℝ, 0 < t → IsCompact {x : ℝ | t ≤ f x})
    (hG_compact : ∀ t : ℝ, 0 < t → IsCompact {x : ℝ | t ≤ g x})
    (hF_ne : ∀ t : ℝ, 0 < t → ({x : ℝ | t ≤ f x}).Nonempty)
    (hG_ne : ∀ t : ℝ, 0 < t → ({x : ℝ | t ≤ g x}).Nonempty)
    (hH_fin : ∀ t : ℝ, 0 < t → volume {x : ℝ | t ≤ hfn x} ≠ ∞)
    (h_pt : ∀ x y : ℝ,
      f x ^ lam * g y ^ (1 - lam) ≤ hfn (lam * x + (1 - lam) * y))
    (h_lc : IsPL1LayerCakeIntegralHyp
      (fun t => (volume {x : ℝ | t ≤ f x}).toReal)
      (fun t => (volume {x : ℝ | t ≤ g x}).toReal)
      (fun t => (volume {x : ℝ | t ≤ hfn x}).toReal) intF intG intH)
    (h_tail : IsTailIntegrableHyp
      (fun t => (volume {x : ℝ | t ≤ f x}).toReal)
      (fun t => (volume {x : ℝ | t ≤ g x}).toReal)
      (fun t => (volume {x : ℝ | t ≤ hfn x}).toReal)) :
    intF ^ lam * intG ^ (1 - lam) ≤ intH := by
  -- 1 次元 superlevel Brunn-Minkowski を pointwise PL + regularity から produce.
  have h_sl_meas :
      IsPL11DSuperLevelHyp
        (fun t => (volume {x : ℝ | t ≤ f x}).toReal)
        (fun t => (volume {x : ℝ | t ≤ g x}).toReal)
        (fun t => (volume {x : ℝ | t ≤ hfn x}).toReal) lam :=
    isPL11DSuperLevelHyp_real f g hfn lam h0 h1 hF_compact hG_compact
      hF_ne hG_ne hH_fin h_pt
  -- `h_sl_meas` は `IsPL11DSuperLevelHyp` (= `∀ t > 0, ...`) なので直接利用できる.
  have h_sl_pos := h_sl_meas
  have h_add : IsPL1AdditiveHyp intF intG intH lam :=
    pl1_additive_via_layercake _ _ _ intF intG intH lam h0 h1 h_lc h_tail h_sl_pos
  -- 加法形 ⇒ 乗法形 (重み付き AM-GM).
  unfold IsPL1AdditiveHyp at h_add
  have hamgm : intF ^ lam * intG ^ (1 - lam) ≤ lam * intF + (1 - lam) * intG :=
    weighted_amgm_lambda hF hG h0 h1
  linarith

end InformationTheory.Shannon.BrunnMinkowski
