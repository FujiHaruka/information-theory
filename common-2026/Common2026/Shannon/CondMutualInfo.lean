import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.MapComap
import Common2026.Shannon.MutualInfo
import Common2026.Shannon.DPI

/-!
# Conditional mutual information & Markov chains (Phase 4-δ-(b) skeleton)

Shannon ムーンショット ([`docs/shannon/shannon-moonshot-plan.md`](../../../docs/shannon/shannon-moonshot-plan.md))
の Phase 4-δ-(b): 条件付き相互情報量 `condMutualInfo` と Markov chain 述語
`IsMarkovChain` を定義し、chain rule と Markov ⇒ condMI = 0、その合成として
`mutualInfo_le_of_markov` (`I(X; Y) ≤ I(Z; Y)` under `X → Z → Y`) を整備する。

設計判断 / Mathlib 在庫は [`docs/shannon/shannon-condmi-inventory.md`](../../../docs/shannon/shannon-condmi-inventory.md)
を参照。Markov 定式化は **β 形式** (condDistrib 等式形) を採用、Mathlib
`condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight` (`Conditional.lean:867`) と直結する。

主応用: `Common2026/Shannon/Converse.lean` 末尾の `shannon_converse_single_shot_markov_encoder`
(Markov chain `Msg → encoder ∘ Msg → Yo` ⇒ `I(Msg; Yo) ≤ I(encoder ∘ Msg; Yo)` で encoder を
含む single-shot converse を導く)。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [MeasurableSpace X]
variable {Y : Type*} [MeasurableSpace Y]
variable {Z : Type*} [MeasurableSpace Z]

/-- Conditional mutual information via KL divergence (compProd form):
`I(X; Y | Z) := KL(P_Z ⊗ P_{(X,Y)|Z} ‖ P_Z ⊗ (P_{X|Z} × P_{Y|Z}))`.

第 1 引数は `compProd_map_condDistrib` で `μ.map (Zc, Xs, Yo)` と等しい。compProd 形を直接の
定義として採用する理由: Mathlib の chain rule (`klDiv_compProd_eq_add`) と直結し、γ-form Markov
仮定下で `condMutualInfo = 0` が `klDiv_self` で trivial に従う。

教科書的な積分形 `∫⁻ z, klDiv (κ_joint z) (κ_factored z) ∂(μ.map Z)` との同値性 (条件付き KL の
公式) は補題として将来追加可能 (Mathlib に直接対応する補題は不在 — 必要になったら自作)。 -/
noncomputable def condMutualInfo
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) : ℝ≥0∞ :=
  klDiv ((μ.map Zc) ⊗ₘ condDistrib (fun ω => (Xs ω, Yo ω)) Zc μ)
        ((μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ)))

/-- Conditional mutual information is non-negative (signature 上自明、`klDiv` が `ℝ≥0∞` 値)。 -/
theorem condMutualInfo_nonneg
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) :
    0 ≤ condMutualInfo μ Xs Yo Zc := bot_le

/-- Markov chain `Xs → Zc → Yo` (γ-form, joint factorization): 結合分布が `Zc` を介して
`Xs` と `Yo` の条件付き分布の積に分解される。Mathlib `condIndepFun_iff_map_prod_eq_prod_
condDistrib_prod_condDistrib` (`Conditional.lean:817`) の RHS と同型。

β-form (condDistrib 等式形 + `prodMkRight`) は `[StandardBorelSpace Ω]` を経由する Mathlib
lemma を要するため (`Conditional.lean:867` の `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`
は `[StandardBorelSpace Ω]` 必須)、ここでは Ω への追加制約を避けて γ-form を採用。

両形式は標準 Borel 仮定下で同値 (Mathlib lemma 経由)。 -/
def IsMarkovChain (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) : Prop :=
  μ.map (fun ω => (Zc ω, Xs ω, Yo ω))
    = (μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ))

/-- Permutation `(Z × X) × Y ≃ᵐ (Z × Y) × X`: `((z, x), y) ↦ ((z, y), x)`. -/
private def permZXY_ZYX (Z X Y : Type*)
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y] :
    (Z × X) × Y ≃ᵐ (Z × Y) × X where
  toEquiv :=
    { toFun := fun p => ((p.1.1, p.2), p.1.2)
      invFun := fun q => ((q.1.1, q.2), q.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  measurable_toFun := by
    refine Measurable.prodMk ?_ ?_
    · exact (measurable_fst.comp measurable_fst).prodMk measurable_snd
    · exact measurable_snd.comp measurable_fst
  measurable_invFun := by
    refine Measurable.prodMk ?_ ?_
    · exact (measurable_fst.comp measurable_fst).prodMk measurable_snd
    · exact measurable_snd.comp measurable_fst

/-- Permutation `(Z × Y) × X ≃ᵐ Z × (X × Y)`: `((z, y), x) ↦ (z, (x, y))`. -/
private def permZYX_Z_XY (Z X Y : Type*)
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y] :
    (Z × Y) × X ≃ᵐ Z × (X × Y) where
  toEquiv :=
    { toFun := fun p => (p.1.1, (p.2, p.1.2))
      invFun := fun q => ((q.1, q.2.2), q.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  measurable_toFun := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_fst.comp measurable_fst
    · exact measurable_snd.prodMk (measurable_snd.comp measurable_fst)
  measurable_invFun := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_fst.prodMk (measurable_snd.comp measurable_snd)
    · exact measurable_fst.comp measurable_snd

/-- The forward map of `permZXY_ZYX` reduces to the explicit form `((z, x), y) ↦ ((z, y), x)`. -/
@[simp] private lemma permZXY_ZYX_apply (Z X Y : Type*)
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (p : (Z × X) × Y) :
    permZXY_ZYX Z X Y p = ((p.1.1, p.2), p.1.2) := rfl

/-- The forward map of `permZYX_Z_XY` reduces to the explicit form `((z, y), x) ↦ (z, (x, y))`. -/
@[simp] private lemma permZYX_Z_XY_apply (Z X Y : Type*)
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (p : (Z × Y) × X) :
    permZYX_Z_XY Z X Y p = (p.1.1, (p.2, p.1.2)) := rfl

/-- Plumbing for chain rule (A2): pushforward of the "product" side through `permZXY_ZYX`
gives a compProd with `(μ.map Zc).prod (μ.map Yo)` base and `Kernel.prodMkRight Y` of the
X kernel. 戦略は `Measure.ext_of_lintegral` + Tonelli swap。 -/
private lemma product_map_perm_eq_compProd
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc) :
    (((μ.map (fun ω => (Zc ω, Xs ω))).prod (μ.map Yo))).map (permZXY_ZYX Z X Y)
      = ((μ.map Zc).prod (μ.map Yo)) ⊗ₘ
          Kernel.prodMkRight Y (condDistrib Xs Zc μ) := by
  set K_X : Kernel Z X := condDistrib Xs Zc μ with hK_X
  have hZX : Measurable (fun ω => (Zc ω, Xs ω)) := hZc.prodMk hXs
  have hμZX : μ.map (fun ω => (Zc ω, Xs ω)) = (μ.map Zc) ⊗ₘ K_X :=
    (compProd_map_condDistrib hXs.aemeasurable).symm
  have hPZ : IsProbabilityMeasure (μ.map Zc) := Measure.isProbabilityMeasure_map hZc.aemeasurable
  have hPY : IsProbabilityMeasure (μ.map Yo) := Measure.isProbabilityMeasure_map hYo.aemeasurable
  have hPZX : IsProbabilityMeasure (μ.map (fun ω => (Zc ω, Xs ω))) :=
    Measure.isProbabilityMeasure_map hZX.aemeasurable
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hg : Measurable (fun p : (Z × X) × Y => f ((permZXY_ZYX Z X Y) p)) :=
    hf.comp (permZXY_ZYX Z X Y).measurable
  -- LHS chain
  rw [lintegral_map hf (permZXY_ZYX Z X Y).measurable]
  rw [lintegral_prod _ hg.aemeasurable]
  rw [hμZX, Measure.lintegral_compProd hg.lintegral_prod_right']
  -- LHS = ∫⁻ z, ∫⁻ x ∂(K_X z), ∫⁻ y ∂(μ.map Yo), f (permZXY_ZYX ((z, x), y)) ∂(μ.map Zc)
  -- RHS chain
  rw [Measure.lintegral_compProd hf]
  rw [lintegral_prod _ (Measurable.lintegral_kernel_prod_right' hf
        (κ := Kernel.prodMkRight Y K_X)).aemeasurable]
  -- RHS = ∫⁻ z, ∫⁻ y ∂(μ.map Yo), ∫⁻ x ∂(K_X z), f ((z, y), x) ∂(μ.map Zc)
  refine lintegral_congr fun z => ?_
  simp only [permZXY_ZYX_apply, Kernel.prodMkRight_apply]
  -- LHS: ∫⁻ x ∂(K_X z), ∫⁻ y ∂(μ.map Yo), f ((z, y), x)
  -- RHS: ∫⁻ y ∂(μ.map Yo), ∫⁻ x ∂(K_X z), f ((z, y), x)
  rw [lintegral_lintegral_swap]
  exact (hf.comp (by fun_prop : Measurable
      (fun p : X × Y => ((z, p.2), p.1)))).aemeasurable

/-- Plumbing for chain rule (B2): pushforward of the "factored" side through `permZYX_Z_XY`
gives the condMutualInfo second-argument form `(μ.map Zc) ⊗ₘ (K_X ×ₖ K_Y)`. -/
private lemma factored_map_perm_eq_compProd_prod
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc) :
    ((μ.map (fun ω => (Zc ω, Yo ω))) ⊗ₘ
        Kernel.prodMkRight Y (condDistrib Xs Zc μ)).map (permZYX_Z_XY Z X Y)
      = (μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ)) := by
  set K_X : Kernel Z X := condDistrib Xs Zc μ
  set K_Y : Kernel Z Y := condDistrib Yo Zc μ
  have hμZY : μ.map (fun ω => (Zc ω, Yo ω)) = (μ.map Zc) ⊗ₘ K_Y :=
    (compProd_map_condDistrib hYo.aemeasurable).symm
  have : IsProbabilityMeasure (μ.map Zc) := Measure.isProbabilityMeasure_map hZc.aemeasurable
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hg : Measurable (fun p : (Z × Y) × X => f ((permZYX_Z_XY Z X Y) p)) :=
    hf.comp (permZYX_Z_XY Z X Y).measurable
  -- LHS chain
  rw [lintegral_map hf (permZYX_Z_XY Z X Y).measurable]
  rw [Measure.lintegral_compProd hg]
  rw [hμZY]
  rw [Measure.lintegral_compProd
        (Measurable.lintegral_kernel_prod_right' hg
          (κ := Kernel.prodMkRight Y K_X))]
  -- LHS = ∫⁻ z, ∫⁻ y ∂(K_Y z), ∫⁻ x ∂(K_X z), f (z, (x, y)) ∂(μ.map Zc)
  -- RHS chain
  rw [Measure.lintegral_compProd hf]
  -- RHS = ∫⁻ z, ∫⁻ p ∂((K_X ×ₖ K_Y) z), f (z, p) ∂(μ.map Zc)
  refine lintegral_congr fun z => ?_
  simp only [permZYX_Z_XY_apply, Kernel.prodMkRight_apply, Kernel.prod_apply]
  -- LHS-inner: ∫⁻ y ∂(K_Y z), ∫⁻ x ∂(K_X z), f (z, (x, y))
  -- RHS-inner: ∫⁻ p ∂(K_X z).prod (K_Y z), f (z, p)
  rw [lintegral_prod (fun b : X × Y => f (z, b))
        ((hf.comp (by fun_prop : Measurable
            (fun q : X × Y => (z, q)))).aemeasurable)]
  -- After lintegral_prod: ∫⁻ x ∂(K_X z), ∫⁻ y ∂(K_Y z), f (z, (x, y))
  rw [lintegral_lintegral_swap]
  exact (hf.comp (by fun_prop : Measurable
      (fun p : Y × X => (z, (p.2, p.1))))).aemeasurable

/-- Chain rule: `I((Z, X); Y) = I(Z; Y) + I(X; Y | Z)`.

戦略 (chain rule plumbing on `(Z × X) × Y → (Z × Y) × X`):
1. `permZXY_ZYX` で LHS の両引数を `(Z × Y) × X` 上に押し出す
   - 第1引数 `μ.map ((Zc, Xs), Yo)` ↦ `μ.map ((Zc, Yo), Xs) = (μ.map (Zc, Yo)) ⊗ₘ condDistrib Xs (Zc, Yo) μ`
   - 第2引数 `(μ.map (Zc, Xs)).prod (μ.map Yo)` ↦ `((μ.map Zc).prod (μ.map Yo)) ⊗ₘ Kernel.prodMkRight Y (condDistrib Xs Zc μ)` (`product_map_perm_eq_compProd`)
2. `klDiv_compProd_eq_add` を base `(Z, Y) + X kernel` で適用
   - 第1項 = `klDiv (μ.map (Zc, Yo)) ((μ.map Zc).prod (μ.map Yo)) = mutualInfo Zc Yo`
   - 第2項 = `klDiv ((μ.map (Zc, Yo)) ⊗ₘ K) ((μ.map (Zc, Yo)) ⊗ₘ K')` (両 base 同一)
3. 第2項を `permZYX_Z_XY` で `Z × (X × Y)` 上に再度押し出して `condMutualInfo` 形に対応
   (`factored_map_perm_eq_compProd_prod` + `compProd_map_condDistrib`) -/
theorem mutualInfo_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc) :
    mutualInfo μ (fun ω => (Zc ω, Xs ω)) Yo
      = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc := by
  set K_X : Kernel Z X := condDistrib Xs Zc μ with hK_X
  set K_Y : Kernel Z Y := condDistrib Yo Zc μ with hK_Y
  set K_joint : Kernel Z (X × Y) := condDistrib (fun ω => (Xs ω, Yo ω)) Zc μ with hK_joint
  set K_pair : Kernel (Z × Y) X := condDistrib Xs (fun ω => (Zc ω, Yo ω)) μ with hK_pair
  have hZX : Measurable (fun ω => (Zc ω, Xs ω)) := hZc.prodMk hXs
  have hZY : Measurable (fun ω => (Zc ω, Yo ω)) := hZc.prodMk hYo
  have hZXY : Measurable (fun ω => ((Zc ω, Xs ω), Yo ω)) := hZX.prodMk hYo
  have hZYX : Measurable (fun ω => ((Zc ω, Yo ω), Xs ω)) := hZY.prodMk hXs
  -- Step 1: push LHS through permZXY_ZYX
  have h_joint_map :
      (μ.map (fun ω => ((Zc ω, Xs ω), Yo ω))).map (permZXY_ZYX Z X Y)
        = μ.map (fun ω => ((Zc ω, Yo ω), Xs ω)) := by
    rw [Measure.map_map (permZXY_ZYX Z X Y).measurable hZXY]; rfl
  have h_joint_compProd :
      μ.map (fun ω => ((Zc ω, Yo ω), Xs ω))
        = (μ.map (fun ω => (Zc ω, Yo ω))) ⊗ₘ K_pair :=
    (compProd_map_condDistrib hXs.aemeasurable).symm
  have h_LHS_klDiv :
      mutualInfo μ (fun ω => (Zc ω, Xs ω)) Yo
        = klDiv ((μ.map (fun ω => (Zc ω, Yo ω))) ⊗ₘ K_pair)
                (((μ.map Zc).prod (μ.map Yo)) ⊗ₘ Kernel.prodMkRight Y K_X) := by
    unfold mutualInfo
    rw [← klDiv_map_measurableEquiv (permZXY_ZYX Z X Y), h_joint_map, h_joint_compProd,
        product_map_perm_eq_compProd μ Xs Yo Zc hXs hYo hZc]
  -- Step 2: apply chain rule (Markov kernel instances needed)
  have hPZ : IsProbabilityMeasure (μ.map Zc) := Measure.isProbabilityMeasure_map hZc.aemeasurable
  have hPY : IsProbabilityMeasure (μ.map Yo) := Measure.isProbabilityMeasure_map hYo.aemeasurable
  have hPZY : IsProbabilityMeasure (μ.map (fun ω => (Zc ω, Yo ω))) :=
    Measure.isProbabilityMeasure_map hZY.aemeasurable
  -- Markov kernel instances (needed for klDiv_compProd_eq_add)
  haveI : IsMarkovKernel K_pair := by rw [hK_pair]; infer_instance
  haveI : IsMarkovKernel (Kernel.prodMkRight Y K_X) := by rw [hK_X]; infer_instance
  rw [h_LHS_klDiv,
      klDiv_compProd_eq_add (μ.map (fun ω => (Zc ω, Yo ω)))
        ((μ.map Zc).prod (μ.map Yo)) K_pair (Kernel.prodMkRight Y K_X)]
  -- Goal: klDiv μ_ZY (μ_Z × μ_Y) + klDiv (μ_ZY ⊗ K_pair) (μ_ZY ⊗ K_prodRight)
  --     = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc
  congr 1
  -- Second term: klDiv ((μ.map (Zc, Yo)) ⊗ₘ K_pair) ((μ.map (Zc, Yo)) ⊗ₘ Kernel.prodMkRight Y K_X)
  --             = condMutualInfo μ Xs Yo Zc
  haveI : IsProbabilityMeasure
      ((μ.map (fun ω => (Zc ω, Yo ω))) ⊗ₘ K_pair) := by infer_instance
  haveI : IsProbabilityMeasure
      ((μ.map (fun ω => (Zc ω, Yo ω))) ⊗ₘ Kernel.prodMkRight Y K_X) := by infer_instance
  -- Push both args through permZYX_Z_XY (klDiv invariant)
  rw [← klDiv_map_measurableEquiv (permZYX_Z_XY Z X Y)
        ((μ.map (fun ω => (Zc ω, Yo ω))) ⊗ₘ K_pair)
        ((μ.map (fun ω => (Zc ω, Yo ω))) ⊗ₘ Kernel.prodMkRight Y K_X)]
  -- Compute the two pushforwards:
  -- (1) ((μ.map (Zc, Yo)) ⊗ₘ K_pair).map perm = (μ.map Zc) ⊗ₘ K_joint
  have h_first :
      ((μ.map (fun ω => (Zc ω, Yo ω))) ⊗ₘ K_pair).map (permZYX_Z_XY Z X Y)
        = (μ.map Zc) ⊗ₘ K_joint := by
    rw [← h_joint_compProd, Measure.map_map (permZYX_Z_XY Z X Y).measurable hZYX]
    have : (permZYX_Z_XY Z X Y) ∘ (fun ω => ((Zc ω, Yo ω), Xs ω))
        = fun ω => (Zc ω, (Xs ω, Yo ω)) := by ext ω <;> rfl
    rw [this]
    exact (compProd_map_condDistrib (hXs.prodMk hYo).aemeasurable).symm
  rw [h_first, factored_map_perm_eq_compProd_prod μ Xs Yo Zc hXs hYo hZc]
  rfl

/-- 条件付き相互情報量の対称性: `I(X; Y | Z) = I(Y; X | Z)`。

戦略: 第 2 引数 `(X × Y)` を `(Y × X)` に交換する MeasurableEquiv
`(refl Z).prodCongr prodComm : Z × (Y × X) ≃ᵐ Z × (X × Y)` を介し、
`klDiv_map_measurableEquiv` で値不変。joint 側は `compProd_map_condDistrib` を 2 回挟んで
`μ.map (Zc, Xs, Yo)` を経由、factored 側は `Measure.compProd_map` + `Kernel.prodComm_prod`
で kernel の swap として処理。 -/
theorem condMutualInfo_comm
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc) :
    condMutualInfo μ Xs Yo Zc = condMutualInfo μ Yo Xs Zc := by
  haveI : IsProbabilityMeasure (μ.map Zc) :=
    Measure.isProbabilityMeasure_map hZc.aemeasurable
  unfold condMutualInfo
  have hXY : Measurable (fun ω => (Xs ω, Yo ω)) := hXs.prodMk hYo
  have hYX : Measurable (fun ω => (Yo ω, Xs ω)) := hYo.prodMk hXs
  let e : Z × (Y × X) ≃ᵐ Z × (X × Y) :=
    (MeasurableEquiv.refl Z).prodCongr MeasurableEquiv.prodComm
  -- joint pushforward via compProd_map_condDistrib + Measure.map_map
  have h_joint :
      ((μ.map Zc) ⊗ₘ condDistrib (fun ω => (Yo ω, Xs ω)) Zc μ).map e
        = (μ.map Zc) ⊗ₘ condDistrib (fun ω => (Xs ω, Yo ω)) Zc μ := by
    rw [compProd_map_condDistrib hYX.aemeasurable,
        Measure.map_map e.measurable (hZc.prodMk hYX),
        show (e ∘ (fun ω => (Zc ω, Yo ω, Xs ω)))
            = (fun ω => (Zc ω, Xs ω, Yo ω)) from rfl,
        compProd_map_condDistrib hXY.aemeasurable]
  -- factored pushforward via Measure.compProd_map + Kernel.prodComm_prod
  have h_factored :
      ((μ.map Zc) ⊗ₘ ((condDistrib Yo Zc μ) ×ₖ (condDistrib Xs Zc μ))).map e
        = (μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ)) := by
    show ((μ.map Zc) ⊗ₘ ((condDistrib Yo Zc μ) ×ₖ (condDistrib Xs Zc μ))).map
            (Prod.map id MeasurableEquiv.prodComm) = _
    rw [← Measure.compProd_map MeasurableEquiv.prodComm.measurable,
        Kernel.prodComm_prod]
  rw [← h_joint, ← h_factored, klDiv_map_measurableEquiv]

/-- 有限アルファベットでは条件付き相互情報量は有限。chain rule
`mutualInfo μ (Zc, Xs) Yo = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc` から
`condMutualInfo ≤ mutualInfo (Zc, Xs) Yo` で押さえる。後者は `mutualInfo_ne_top` で有限。 -/
theorem condMutualInfo_ne_top
    [Fintype X] [MeasurableSingletonClass X]
    [Fintype Y] [MeasurableSingletonClass Y]
    [Fintype Z] [MeasurableSingletonClass Z]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc) :
    condMutualInfo μ Xs Yo Zc ≠ ∞ := by
  have h_chain := mutualInfo_chain_rule μ Xs Yo Zc hXs hYo hZc
  have h_le : condMutualInfo μ Xs Yo Zc
      ≤ mutualInfo μ (fun ω => (Zc ω, Xs ω)) Yo := by
    rw [h_chain]; exact self_le_add_left _ _
  exact ne_top_of_le_ne_top
    (mutualInfo_ne_top μ (fun ω => (Zc ω, Xs ω)) Yo (hZc.prodMk hXs) hYo) h_le

/-- Markov chain `Xs → Zc → Yo` (γ-form) ⇒ `I(X; Y | Z) = 0`.

γ-form 採用により直接的な証明: condMutualInfo の第1引数 `(μ.map Zc) ⊗ₘ condDistrib (Xs, Yo) Zc μ`
は `compProd_map_condDistrib` で `μ.map (Zc, Xs, Yo)` と一致し、γ-form Markov の RHS が第2引数
そのものなので、両者が等しく `klDiv_self` で 0。 -/
theorem condMutualInfo_eq_zero_of_markov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    condMutualInfo μ Xs Yo Zc = 0 := by
  unfold condMutualInfo
  have h_pair : Measurable (fun ω => (Xs ω, Yo ω)) := hXs.prodMk hYo
  have h_num_eq : (μ.map Zc) ⊗ₘ condDistrib (fun ω => (Xs ω, Yo ω)) Zc μ
      = μ.map (fun ω => (Zc ω, Xs ω, Yo ω)) := compProd_map_condDistrib h_pair.aemeasurable
  rw [h_num_eq, hmarkov]
  exact klDiv_self _

/-- Markov chain `Xs → Zc → Yo` ⇒ `I(Xs; Yo) ≤ I(Zc; Yo)`.

戦略 (chain rule + condMI = 0 + DPI for `Prod.snd : Z × X → X` の合成):
1. DPI for `Prod.snd`: `I(Yo; Xs) ≤ I(Yo; (Zc, Xs))`、`mutualInfo_comm` で両端の対称化により
   `I(Xs; Yo) ≤ I((Zc, Xs); Yo)`
2. `mutualInfo_chain_rule` で `I((Zc, Xs); Yo) = I(Zc; Yo) + I(Xs; Yo | Zc)`
3. `condMutualInfo_eq_zero_of_markov` で `I(Xs; Yo | Zc) = 0`
4. 1+2+3 を合成

主応用: `shannon_converse_single_shot_markov_encoder` (Converse.lean 末尾)。 -/
theorem mutualInfo_le_of_markov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo := by
  have h_pair_meas : Measurable (fun ω => (Zc ω, Xs ω)) := hZc.prodMk hXs
  -- Step 1: DPI on second arg with f := Prod.snd, applied to Yo as first arg
  have h_snd_eq : (Prod.snd : Z × X → X) ∘ (fun ω => (Zc ω, Xs ω)) = Xs := rfl
  have h_dpi_yo :
      mutualInfo μ Yo (Prod.snd ∘ (fun ω => (Zc ω, Xs ω))) ≤
        mutualInfo μ Yo (fun ω => (Zc ω, Xs ω)) :=
    mutualInfo_le_of_postprocess μ Yo (fun ω => (Zc ω, Xs ω)) hYo h_pair_meas measurable_snd
  rw [h_snd_eq] at h_dpi_yo
  -- DPI: I(Yo; Xs) ≤ I(Yo; (Zc, Xs))
  -- Symmetrize via mutualInfo_comm: I(Xs; Yo) ≤ I((Zc, Xs); Yo)
  have h_dpi :
      mutualInfo μ Xs Yo ≤ mutualInfo μ (fun ω => (Zc ω, Xs ω)) Yo := by
    rw [mutualInfo_comm μ Xs Yo hXs hYo,
        mutualInfo_comm μ (fun ω => (Zc ω, Xs ω)) Yo h_pair_meas hYo]
    exact h_dpi_yo
  -- Step 2: chain rule I((Zc, Xs); Yo) = I(Zc; Yo) + condMutualInfo Xs Yo Zc
  have h_chain :
      mutualInfo μ (fun ω => (Zc ω, Xs ω)) Yo
        = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc :=
    mutualInfo_chain_rule μ Xs Yo Zc hXs hYo hZc
  -- Step 3: Markov ⇒ condMI = 0
  have h_zero : condMutualInfo μ Xs Yo Zc = 0 :=
    condMutualInfo_eq_zero_of_markov μ Xs Zc Yo hXs hZc hYo hmarkov
  -- Compose
  rw [h_chain, h_zero, add_zero] at h_dpi
  exact h_dpi

/-! ## Phase A (D-2'' インフラ) — `condMutualInfo` の `MeasurableEquiv` reshape 不変性

D-2'' / 後続 channel coding 系で `Y^n ↔ Y_i × Y^{≠i}` / `X^{≠i} ↔ X^{<i} × X^{>i}` などの
reshape を扱うため、`condMutualInfo` 各引数の `MeasurableEquiv` 不変性を整備する
(`mutualInfo_map_left/right_measurableEquiv` の条件付き版)。-/

/-- **Left reshape**: `I(e ∘ X; Y | Z) = I(X; Y | Z)` for any `MeasurableEquiv e : X ≃ᵐ X'`.

戦略: 第 1 引数 (joint kernel) と第 2 引数 (factored kernel) の両方に `id × (e × id)` を
pushforward。
- joint 側: `condDistrib (e∘X, Y) Z μ` の compProd 形は `μ.map (Z, e∘X, Y)` (via
  `compProd_map_condDistrib`)。これは `μ.map (Z, X, Y)` を `id × (e × id)` で押し出した形。
- factored 側: `Kernel.map_prod_eq` で `(condDistrib (e∘X) Z μ ×ₖ condDistrib Y Z μ)
  = ((condDistrib X Z μ).map e ×ₖ condDistrib Y Z μ).map (Prod.map id (id))` 形を経由、
  `condDistrib_comp` で `condDistrib (e∘X) Z μ =ᵐ (condDistrib X Z μ).map e`。 -/
theorem condMutualInfo_map_left_measurableEquiv
    {X' : Type*} [MeasurableSpace X'] [StandardBorelSpace X'] [Nonempty X']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc)
    (e : X ≃ᵐ X') :
    condMutualInfo μ (fun ω => e (Xs ω)) Yo Zc = condMutualInfo μ Xs Yo Zc := by
  haveI : IsProbabilityMeasure (μ.map Zc) :=
    Measure.isProbabilityMeasure_map hZc.aemeasurable
  unfold condMutualInfo
  -- The reshape on Z × (X × Y): apply `id × (e × id)`.
  let eProd : Z × X × Y ≃ᵐ Z × X' × Y :=
    (MeasurableEquiv.refl Z).prodCongr (e.prodCongr (.refl Y))
  -- Step 1: joint side via compProd_map_condDistrib (both ways) + Measure.map_map.
  have hXY : Measurable (fun ω => (Xs ω, Yo ω)) := hXs.prodMk hYo
  have heXY : Measurable (fun ω => (e (Xs ω), Yo ω)) := (e.measurable.comp hXs).prodMk hYo
  have h_joint :
      ((μ.map Zc) ⊗ₘ condDistrib (fun ω => (e (Xs ω), Yo ω)) Zc μ)
        = ((μ.map Zc) ⊗ₘ condDistrib (fun ω => (Xs ω, Yo ω)) Zc μ).map eProd := by
    rw [compProd_map_condDistrib heXY.aemeasurable,
        compProd_map_condDistrib hXY.aemeasurable,
        Measure.map_map eProd.measurable (hZc.prodMk hXY)]
    rfl
  -- Step 2: factored side via condDistrib_comp + Kernel.map_prod_eq.
  -- condDistrib (e ∘ Xs) Zc μ =ᵐ[μ.map Zc] (condDistrib Xs Zc μ).map e
  have h_cd_comp :
      condDistrib (fun ω => e (Xs ω)) Zc μ
        =ᵐ[μ.map Zc] (condDistrib Xs Zc μ).map e :=
    condDistrib_comp Zc hXs.aemeasurable e.measurable
  -- Replace LHS factored kernel with map-rewritten version, then pushforward.
  have h_factored_compProd_eq :
      (μ.map Zc) ⊗ₘ
          (condDistrib (fun ω => e (Xs ω)) Zc μ ×ₖ condDistrib Yo Zc μ)
        = (μ.map Zc) ⊗ₘ
          ((condDistrib Xs Zc μ).map e ×ₖ condDistrib Yo Zc μ) := by
    refine Measure.compProd_congr ?_
    filter_upwards [h_cd_comp] with z hz
    ext s hs
    rw [Kernel.prod_apply, Kernel.prod_apply, hz]
  -- (κ.map e) ×ₖ η = (κ ×ₖ η).map (Prod.map e id)
  have h_map_prod :
      (condDistrib Xs Zc μ).map e ×ₖ condDistrib Yo Zc μ
        = (condDistrib Xs Zc μ ×ₖ condDistrib Yo Zc μ).map (Prod.map e (id : Y → Y)) :=
    Kernel.map_prod_eq _ _ e.measurable
  -- Combine into pushforward via eProd.
  have h_factored :
      (μ.map Zc) ⊗ₘ
          (condDistrib (fun ω => e (Xs ω)) Zc μ ×ₖ condDistrib Yo Zc μ)
        = ((μ.map Zc) ⊗ₘ
              (condDistrib Xs Zc μ ×ₖ condDistrib Yo Zc μ)).map eProd := by
    rw [h_factored_compProd_eq, h_map_prod, Measure.compProd_map]
    · rfl
    · exact (e.measurable.prodMap measurable_id)
  rw [h_joint, h_factored, klDiv_map_measurableEquiv]

/-- **Right reshape (Y/middle)**: `I(X; e ∘ Y | Z) = I(X; Y | Z)` for `e : Y ≃ᵐ Y'`.

`condMutualInfo_comm` で第 1, 2 引数を swap し `condMutualInfo_map_left_measurableEquiv` に
帰着。 -/
theorem condMutualInfo_map_middle_measurableEquiv
    {Y' : Type*} [MeasurableSpace Y'] [StandardBorelSpace Y'] [Nonempty Y']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc)
    (e : Y ≃ᵐ Y') :
    condMutualInfo μ Xs (fun ω => e (Yo ω)) Zc = condMutualInfo μ Xs Yo Zc := by
  rw [condMutualInfo_comm μ Xs (fun ω => e (Yo ω)) Zc hXs (e.measurable.comp hYo) hZc,
      condMutualInfo_map_left_measurableEquiv μ Yo Xs Zc hYo hXs hZc e,
      condMutualInfo_comm μ Yo Xs Zc hYo hXs hZc]

/-- Helper: pushforward of a `compProd` along `Prod.map e id` equals a `compProd`
with the pushed-forward base measure and the comap'd kernel.

`((μ.map Zc) ⊗ₘ κ).map (Prod.map e id) = (μ.map (e ∘ Zc)) ⊗ₘ (κ.comap e.symm e.symm.measurable)`.

戦略: `Measure.ext_of_lintegral` + `lintegral_compProd` + `lintegral_comap`。基準点 (e.symm (e z) = z)
で comap pre-image を吸収する。 -/
private lemma compProd_map_left_prodMap
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (ν : Measure α) [SFinite ν] (κ : Kernel α γ) [IsSFiniteKernel κ]
    (e : α ≃ᵐ β) :
    (ν ⊗ₘ κ).map (Prod.map e (id : γ → γ))
      = (ν.map e) ⊗ₘ (κ.comap e.symm e.symm.measurable) := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have h_prodMap : Measurable (Prod.map (e : α → β) (id : γ → γ)) :=
    e.measurable.prodMap measurable_id
  have hfg : Measurable (f ∘ Prod.map (e : α → β) (id : γ → γ)) := hf.comp h_prodMap
  -- LHS chain.
  rw [lintegral_map hf h_prodMap]
  -- Goal LHS: ∫⁻ a, f (Prod.map e id a) ∂(ν ⊗ₘ κ).
  -- Convert via show to (f ∘ Prod.map e id) a form so lintegral_compProd applies.
  rw [show (fun a : α × γ => f (Prod.map (e : α → β) (id : γ → γ) a))
      = (f ∘ Prod.map (e : α → β) (id : γ → γ)) from rfl,
      Measure.lintegral_compProd hfg]
  -- RHS chain.
  rw [Measure.lintegral_compProd hf]
  rw [lintegral_map
        (Measurable.lintegral_kernel_prod_right' hf
          (κ := κ.comap e.symm e.symm.measurable))
        e.measurable]
  refine lintegral_congr fun a => ?_
  rw [Kernel.comap_apply _ e.symm.measurable]
  simp [Prod.map]

/-- **Right reshape (Z/conditioner)**: `I(X; Y | e ∘ Z) = I(X; Y | Z)` for `e : Z ≃ᵐ Z'`.

戦略: `(refl Z).prodCongr (.refl (X × Y))` → 簡略化のため `e.prodCongr (.refl (X × Y))`。
- joint 側: `compProd_map_condDistrib` で両側 `μ.map (Zc', X, Y)` 形に書き、`Measure.map_map`
  で `eProd` push に統合。
- factored 側: `compProd_map_left_prodMap` でベース測度 `e.push` を吸収し、`Kernel.comap`
  された factored kernel を `condDistrib X (e∘Zc) μ ×ₖ condDistrib Y (e∘Zc) μ` と
  `condDistrib_ae_eq_of_measure_eq_compProd` 経由で同一視。 -/
theorem condMutualInfo_map_right_measurableEquiv
    {Z' : Type*} [MeasurableSpace Z'] [StandardBorelSpace Z'] [Nonempty Z']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc)
    (e : Z ≃ᵐ Z') :
    condMutualInfo μ Xs Yo (fun ω => e (Zc ω)) = condMutualInfo μ Xs Yo Zc := by
  haveI : IsProbabilityMeasure (μ.map Zc) :=
    Measure.isProbabilityMeasure_map hZc.aemeasurable
  haveI : IsProbabilityMeasure (μ.map (fun ω => e (Zc ω))) :=
    Measure.isProbabilityMeasure_map (e.measurable.comp hZc).aemeasurable
  unfold condMutualInfo
  -- Reshape on Z × (X × Y): apply `e × id`.
  let eProd : Z × X × Y ≃ᵐ Z' × X × Y := e.prodCongr (.refl (X × Y))
  have heZc : Measurable (fun ω => e (Zc ω)) := e.measurable.comp hZc
  have hXY : Measurable (fun ω => (Xs ω, Yo ω)) := hXs.prodMk hYo
  -- Map relation: e ∘ Zc factors as e ∘ ... on the first coord.
  have h_eZc_map : μ.map (fun ω => e (Zc ω)) = (μ.map Zc).map e := by
    rw [Measure.map_map e.measurable hZc]; rfl
  -- Step 1: joint side.
  -- (μ.map (e∘Zc)) ⊗ₘ condDistrib (X,Y) (e∘Zc) μ = μ.map (e∘Zc, X, Y)
  --   = (μ.map (Zc, X, Y)).map eProd = ((μ.map Zc) ⊗ₘ condDistrib (X,Y) Zc μ).map eProd.
  have h_joint :
      ((μ.map (fun ω => e (Zc ω))) ⊗ₘ
          condDistrib (fun ω => (Xs ω, Yo ω)) (fun ω => e (Zc ω)) μ)
        = ((μ.map Zc) ⊗ₘ condDistrib (fun ω => (Xs ω, Yo ω)) Zc μ).map eProd := by
    rw [compProd_map_condDistrib hXY.aemeasurable,
        compProd_map_condDistrib hXY.aemeasurable,
        Measure.map_map eProd.measurable (hZc.prodMk hXY)]
    rfl
  -- Step 2: factored side.
  -- Strategy: First push the Zc-version through eProd using compProd_map_left_prodMap,
  -- yielding (μ.map (e∘Zc)) ⊗ₘ (κ.comap e.symm). Then identify the comap'd kernel with
  -- the (e∘Zc) condDistrib product via condDistrib_ae_eq_of_measure_eq_compProd.
  set K_X : Kernel Z X := condDistrib Xs Zc μ with hK_X_def
  set K_Y : Kernel Z Y := condDistrib Yo Zc μ with hK_Y_def
  set K_X' : Kernel Z' X := condDistrib Xs (fun ω => e (Zc ω)) μ with hK_X'_def
  set K_Y' : Kernel Z' Y := condDistrib Yo (fun ω => e (Zc ω)) μ with hK_Y'_def
  -- (a) Push through eProd.
  have h_factored_push :
      ((μ.map Zc) ⊗ₘ (K_X ×ₖ K_Y)).map eProd
        = (μ.map (fun ω => e (Zc ω))) ⊗ₘ ((K_X ×ₖ K_Y).comap e.symm e.symm.measurable) := by
    have h := compProd_map_left_prodMap (μ.map Zc) (K_X ×ₖ K_Y) e
    rw [← h_eZc_map] at h
    -- eProd as a function equals Prod.map e id.
    have heqMap : (eProd : Z × X × Y → Z' × X × Y) = Prod.map e (id : X × Y → X × Y) := rfl
    rw [heqMap]
    exact h
  -- (b) Identify the comap'd kernel with K_X' ×ₖ K_Y' via condDistrib uniqueness.
  -- Use condDistrib_ae_eq_of_measure_eq_compProd: it suffices to show
  --   μ.map (e∘Zc, X) = (μ.map (e∘Zc)) ⊗ₘ (K_X.comap e.symm)
  -- and the analogous for Y, then combine.
  -- Cleaner: show the full factored kernel equality on the compProd level directly.
  have h_factored_kernel_eq :
      (μ.map (fun ω => e (Zc ω))) ⊗ₘ ((K_X ×ₖ K_Y).comap e.symm e.symm.measurable)
        = (μ.map (fun ω => e (Zc ω))) ⊗ₘ (K_X' ×ₖ K_Y') := by
    -- Show K_X' =ᵐ K_X.comap e.symm and K_Y' =ᵐ K_Y.comap e.symm under (μ.map (e∘Zc)).
    have hK_X'_eq :
        K_X' =ᵐ[μ.map (fun ω => e (Zc ω))] K_X.comap e.symm e.symm.measurable := by
      refine condDistrib_ae_eq_of_measure_eq_compProd
        (fun ω => e (Zc ω)) hXs.aemeasurable ?_
      -- Need: μ.map (e∘Zc, X) = (μ.map (e∘Zc)) ⊗ₘ (K_X.comap e.symm).
      have h₁ : μ.map (fun a => ((fun ω => e (Zc ω)) a, Xs a))
          = ((μ.map (fun a => (Zc a, Xs a)))).map (Prod.map (e : Z → Z') (id : X → X)) := by
        rw [Measure.map_map (e.measurable.prodMap measurable_id) (hZc.prodMk hXs)]
        rfl
      have h₂ : μ.map (fun a => (Zc a, Xs a)) = (μ.map Zc) ⊗ₘ K_X :=
        (compProd_map_condDistrib hXs.aemeasurable).symm
      rw [h₁, h₂, compProd_map_left_prodMap (μ.map Zc) K_X e, ← h_eZc_map]
    have hK_Y'_eq :
        K_Y' =ᵐ[μ.map (fun ω => e (Zc ω))] K_Y.comap e.symm e.symm.measurable := by
      refine condDistrib_ae_eq_of_measure_eq_compProd
        (fun ω => e (Zc ω)) hYo.aemeasurable ?_
      have h₁ : μ.map (fun a => ((fun ω => e (Zc ω)) a, Yo a))
          = ((μ.map (fun a => (Zc a, Yo a)))).map (Prod.map (e : Z → Z') (id : Y → Y)) := by
        rw [Measure.map_map (e.measurable.prodMap measurable_id) (hZc.prodMk hYo)]
        rfl
      have h₂ : μ.map (fun a => (Zc a, Yo a)) = (μ.map Zc) ⊗ₘ K_Y :=
        (compProd_map_condDistrib hYo.aemeasurable).symm
      rw [h₁, h₂, compProd_map_left_prodMap (μ.map Zc) K_Y e, ← h_eZc_map]
    -- Combine: kernels equal a.e. ⇒ their products equal a.e. ⇒ compProds equal.
    refine (Measure.compProd_congr ?_).symm
    filter_upwards [hK_X'_eq, hK_Y'_eq] with z' hX' hY'
    -- (K_X ×ₖ K_Y).comap e.symm z' = (K_X (e.symm z')) ×ₘ (K_Y (e.symm z'))
    --                              = K_X' z' ×ₘ K_Y' z'
    ext s hs
    rw [Kernel.comap_apply _ e.symm.measurable, Kernel.prod_apply, Kernel.prod_apply,
        ← Kernel.comap_apply K_X e.symm.measurable,
        ← Kernel.comap_apply K_Y e.symm.measurable, ← hX', ← hY']
  have h_factored :
      ((μ.map (fun ω => e (Zc ω))) ⊗ₘ (K_X' ×ₖ K_Y'))
        = ((μ.map Zc) ⊗ₘ (K_X ×ₖ K_Y)).map eProd := by
    rw [h_factored_push, h_factored_kernel_eq]
  -- Final: combine via klDiv_map_measurableEquiv.
  rw [h_joint, h_factored, klDiv_map_measurableEquiv]

/-- **Markov chain left post-processing**: if `Xs → Zc → Yo` is a Markov chain and
`f : X → X'` is measurable, then `f ∘ Xs → Zc → Yo` is also a Markov chain.

戦略: γ-form Markov の両辺に `id × (f × id) : Z × (X × Y) → Z × (X' × Y)` を pushforward。
- LHS `μ.map (Z, X, Y)` ↦ `μ.map (Z, f∘X, Y)` (via `Measure.map_map`).
- RHS `(μ.map Z) ⊗ₘ (K_X ×ₖ K_Y)` ↦ `(μ.map Z) ⊗ₘ (K_X.map f ×ₖ K_Y)`
  (via `Measure.compProd_map` + `Kernel.map_prod_eq`).
- `condDistrib_comp` で `condDistrib (f∘X) Z μ =ᵐ K_X.map f` を吸収。

用途: D-2'' Phase B Step 1 (`X^{≠i} → X_i → Y_i` から `X^{<i} → X_i → Y_i` を `Prod.fst` で抽出). -/
theorem isMarkovChain_map_left
    {X' : Type*} [MeasurableSpace X'] [StandardBorelSpace X'] [Nonempty X']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    {f : X → X'} (hf : Measurable f)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    IsMarkovChain μ (fun ω => f (Xs ω)) Zc Yo := by
  haveI : IsProbabilityMeasure (μ.map Zc) :=
    Measure.isProbabilityMeasure_map hZc.aemeasurable
  unfold IsMarkovChain
  have hZXY : Measurable (fun ω => (Zc ω, Xs ω, Yo ω)) := hZc.prodMk (hXs.prodMk hYo)
  -- LHS: μ.map (Z, f∘X, Y) = (μ.map (Z, X, Y)).map (id × (f × id)).
  have h_LHS :
      μ.map (fun ω => (Zc ω, f (Xs ω), Yo ω))
        = (μ.map (fun ω => (Zc ω, Xs ω, Yo ω))).map
            (Prod.map (id : Z → Z) (Prod.map f (id : Y → Y))) := by
    rw [Measure.map_map (measurable_id.prodMap (hf.prodMap measurable_id)) hZXY]
    rfl
  rw [h_LHS, hmarkov]
  -- Goal: ((μ.map Zc) ⊗ₘ (K_X ×ₖ K_Y)).map (id × (f × id)) = (μ.map Zc) ⊗ₘ (K_{f∘X} ×ₖ K_Y).
  rw [← Measure.compProd_map (hf.prodMap measurable_id),
      ← Kernel.map_prod_eq _ _ hf]
  -- Goal: (μ.map Zc) ⊗ₘ ((K_X.map f) ×ₖ K_Y) = (μ.map Zc) ⊗ₘ (K_{f∘X} ×ₖ K_Y).
  refine (Measure.compProd_congr ?_).symm
  have h_cd : condDistrib (fun ω => f (Xs ω)) Zc μ
      =ᵐ[μ.map Zc] (condDistrib Xs Zc μ).map f :=
    condDistrib_comp Zc hXs.aemeasurable hf
  filter_upwards [h_cd] with z hz
  ext s hs
  rw [Kernel.prod_apply, Kernel.prod_apply, hz]

end InformationTheory.Shannon
