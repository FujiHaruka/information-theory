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

Shannon ムーンショット ([`docs/shannon-moonshot-plan.md`](../../../docs/shannon-moonshot-plan.md))
の Phase 4-δ-(b): 条件付き相互情報量 `condMutualInfo` と Markov chain 述語
`IsMarkovChain` を定義し、chain rule と Markov ⇒ condMI = 0、その合成として
`mutualInfo_le_of_markov` (`I(X; Y) ≤ I(Z; Y)` under `X → Z → Y`) を整備する。

設計判断 / Mathlib 在庫は [`docs/shannon-condmi-inventory.md`](../../../docs/shannon-condmi-inventory.md)
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

end InformationTheory.Shannon
