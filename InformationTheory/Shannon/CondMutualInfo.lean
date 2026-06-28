import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.MapComap
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.DPI

/-!
# Conditional mutual information and Markov chains

Conditional mutual information `condMutualInfo` and the Markov chain predicate
`IsMarkovChain`, together with the chain rule and the implication Markov ⇒ condMI = 0.

## Main definitions

* `condMutualInfo` — `I(X; Y | Z) := KL(P_Z ⊗ P_{(X,Y)|Z} ‖ P_Z ⊗ (P_{X|Z} × P_{Y|Z}))`.
* `IsMarkovChain` — joint factorization form (γ-form): `μ.map (Z, X, Y)` equals
  `(μ.map Z) ⊗ₘ (condDistrib X Z μ ×ₖ condDistrib Y Z μ)`.

## Main statements

* `mutualInfo_chain_rule` — `I((Z, X); Y) = I(Z; Y) + I(X; Y | Z)`.
* `condMutualInfo_comm` — `I(X; Y | Z) = I(Y; X | Z)`.
* `condMutualInfo_ne_top` — finiteness over finite alphabets.
* `condMutualInfo_eq_zero_of_markov` — Markov chain ⇒ `I(X; Y | Z) = 0`.
* `mutualInfo_le_of_markov` — `I(X; Y) ≤ I(Z; Y)` under `X → Z → Y`.
* `condMutualInfo_map_left_measurableEquiv` — `I(e ∘ X; Y | Z) = I(X; Y | Z)`.
* `condMutualInfo_map_middle_measurableEquiv` — `I(X; e ∘ Y | Z) = I(X; Y | Z)`.
* `isMarkovChain_map_left` — post-processing preserves the Markov property.

## Implementation notes

The γ-form definition of `IsMarkovChain` (joint measure factorization) is chosen over
the β-form (condDistrib equality via `prodMkRight`) because the β-form requires
`[StandardBorelSpace Ω]` on the ambient space, whereas the γ-form avoids this constraint.
The two forms are equivalent under standard Borel hypotheses via Mathlib's
`condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`.
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

The compProd form is the defining shape because it connects directly to Mathlib's chain
rule (`klDiv_compProd_eq_add`) and makes `condMutualInfo = 0` under a Markov hypothesis
immediate via `klDiv_self`. -/
noncomputable def condMutualInfo
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) : ℝ≥0∞ :=
  klDiv ((μ.map Zc) ⊗ₘ condDistrib (fun ω ↦ (Xs ω, Yo ω)) Zc μ)
        ((μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ)))

/-- Conditional mutual information is non-negative (`klDiv` is `ℝ≥0∞`-valued). -/
@[entry_point]
theorem condMutualInfo_nonneg
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) :
    0 ≤ condMutualInfo μ Xs Yo Zc := bot_le

/-- Markov chain `Xs → Zc → Yo` (γ-form, joint factorization): the joint distribution
factors through `Zc` as the product of the conditional marginals.

Chosen over the β-form (`condDistrib` equality + `prodMkRight`) to avoid requiring
`[StandardBorelSpace Ω]` on the ambient space. The two forms are equivalent under
standard Borel hypotheses. -/
def IsMarkovChain (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) : Prop :=
  μ.map (fun ω ↦ (Zc ω, Xs ω, Yo ω))
    = (μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ))

/-- Permutation `(Z × X) × Y ≃ᵐ (Z × Y) × X`: `((z, x), y) ↦ ((z, y), x)`. -/
private def permZXY_ZYX (Z X Y : Type*)
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y] :
    (Z × X) × Y ≃ᵐ (Z × Y) × X where
  toEquiv :=
    { toFun := fun p ↦ ((p.1.1, p.2), p.1.2)
      invFun := fun q ↦ ((q.1.1, q.2), q.1.2)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
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
    { toFun := fun p ↦ (p.1.1, (p.2, p.1.2))
      invFun := fun q ↦ ((q.1, q.2.2), q.2.1)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  measurable_toFun := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_fst.comp measurable_fst
    · exact measurable_snd.prodMk (measurable_snd.comp measurable_fst)
  measurable_invFun := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_fst.prodMk (measurable_snd.comp measurable_snd)
    · exact measurable_fst.comp measurable_snd

@[simp] private lemma permZXY_ZYX_apply (Z X Y : Type*)
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (p : (Z × X) × Y) :
    permZXY_ZYX Z X Y p = ((p.1.1, p.2), p.1.2) := rfl

@[simp] private lemma permZYX_Z_XY_apply (Z X Y : Type*)
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (p : (Z × Y) × X) :
    permZYX_Z_XY Z X Y p = (p.1.1, (p.2, p.1.2)) := rfl

private lemma product_map_perm_eq_compProd
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc) :
    (((μ.map (fun ω ↦ (Zc ω, Xs ω))).prod (μ.map Yo))).map (permZXY_ZYX Z X Y)
      = ((μ.map Zc).prod (μ.map Yo)) ⊗ₘ
          Kernel.prodMkRight Y (condDistrib Xs Zc μ) := by
  set K_X : Kernel Z X := condDistrib Xs Zc μ with hK_X
  have hZX : Measurable (fun ω ↦ (Zc ω, Xs ω)) := hZc.prodMk hXs
  have hμZX : μ.map (fun ω ↦ (Zc ω, Xs ω)) = (μ.map Zc) ⊗ₘ K_X :=
    (compProd_map_condDistrib hXs.aemeasurable).symm
  have hPZ : IsProbabilityMeasure (μ.map Zc) := Measure.isProbabilityMeasure_map hZc.aemeasurable
  have hPY : IsProbabilityMeasure (μ.map Yo) := Measure.isProbabilityMeasure_map hYo.aemeasurable
  have hPZX : IsProbabilityMeasure (μ.map (fun ω ↦ (Zc ω, Xs ω))) :=
    Measure.isProbabilityMeasure_map hZX.aemeasurable
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have hg : Measurable (fun p : (Z × X) × Y ↦ f ((permZXY_ZYX Z X Y) p)) :=
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
  refine lintegral_congr fun z ↦ ?_
  simp only [permZXY_ZYX_apply, Kernel.prodMkRight_apply]
  -- LHS: ∫⁻ x ∂(K_X z), ∫⁻ y ∂(μ.map Yo), f ((z, y), x)
  -- RHS: ∫⁻ y ∂(μ.map Yo), ∫⁻ x ∂(K_X z), f ((z, y), x)
  rw [lintegral_lintegral_swap]
  exact (hf.comp (by fun_prop : Measurable
      (fun p : X × Y ↦ ((z, p.2), p.1)))).aemeasurable

private lemma factored_map_perm_eq_compProd_prod
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (_hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc) :
    ((μ.map (fun ω ↦ (Zc ω, Yo ω))) ⊗ₘ
        Kernel.prodMkRight Y (condDistrib Xs Zc μ)).map (permZYX_Z_XY Z X Y)
      = (μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ)) := by
  set K_X : Kernel Z X := condDistrib Xs Zc μ
  set K_Y : Kernel Z Y := condDistrib Yo Zc μ
  have hμZY : μ.map (fun ω ↦ (Zc ω, Yo ω)) = (μ.map Zc) ⊗ₘ K_Y :=
    (compProd_map_condDistrib hYo.aemeasurable).symm
  have : IsProbabilityMeasure (μ.map Zc) := Measure.isProbabilityMeasure_map hZc.aemeasurable
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have hg : Measurable (fun p : (Z × Y) × X ↦ f ((permZYX_Z_XY Z X Y) p)) :=
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
  refine lintegral_congr fun z ↦ ?_
  simp only [permZYX_Z_XY_apply, Kernel.prodMkRight_apply, Kernel.prod_apply]
  -- LHS-inner: ∫⁻ y ∂(K_Y z), ∫⁻ x ∂(K_X z), f (z, (x, y))
  -- RHS-inner: ∫⁻ p ∂(K_X z).prod (K_Y z), f (z, p)
  rw [lintegral_prod (fun b : X × Y ↦ f (z, b))
        ((hf.comp (by fun_prop : Measurable
            (fun q : X × Y ↦ (z, q)))).aemeasurable)]
  -- After lintegral_prod: ∫⁻ x ∂(K_X z), ∫⁻ y ∂(K_Y z), f (z, (x, y))
  rw [lintegral_lintegral_swap]
  exact (hf.comp (by fun_prop : Measurable
      (fun p : Y × X ↦ (z, (p.2, p.1))))).aemeasurable

/-- Chain rule: `I((Z, X); Y) = I(Z; Y) + I(X; Y | Z)`. -/
@[entry_point]
theorem mutualInfo_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc) :
    mutualInfo μ (fun ω ↦ (Zc ω, Xs ω)) Yo
      = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc := by
  set K_X : Kernel Z X := condDistrib Xs Zc μ with hK_X
  set K_Y : Kernel Z Y := condDistrib Yo Zc μ with hK_Y
  set K_joint : Kernel Z (X × Y) := condDistrib (fun ω ↦ (Xs ω, Yo ω)) Zc μ with hK_joint
  set K_pair : Kernel (Z × Y) X := condDistrib Xs (fun ω ↦ (Zc ω, Yo ω)) μ with hK_pair
  have hZX : Measurable (fun ω ↦ (Zc ω, Xs ω)) := hZc.prodMk hXs
  have hZY : Measurable (fun ω ↦ (Zc ω, Yo ω)) := hZc.prodMk hYo
  have hZXY : Measurable (fun ω ↦ ((Zc ω, Xs ω), Yo ω)) := hZX.prodMk hYo
  have hZYX : Measurable (fun ω ↦ ((Zc ω, Yo ω), Xs ω)) := hZY.prodMk hXs
  -- Step 1: push LHS through permZXY_ZYX
  have h_joint_map :
      (μ.map (fun ω ↦ ((Zc ω, Xs ω), Yo ω))).map (permZXY_ZYX Z X Y)
        = μ.map (fun ω ↦ ((Zc ω, Yo ω), Xs ω)) := by
    rw [Measure.map_map (permZXY_ZYX Z X Y).measurable hZXY]; rfl
  have h_joint_compProd :
      μ.map (fun ω ↦ ((Zc ω, Yo ω), Xs ω))
        = (μ.map (fun ω ↦ (Zc ω, Yo ω))) ⊗ₘ K_pair :=
    (compProd_map_condDistrib hXs.aemeasurable).symm
  have h_LHS_klDiv :
      mutualInfo μ (fun ω ↦ (Zc ω, Xs ω)) Yo
        = klDiv ((μ.map (fun ω ↦ (Zc ω, Yo ω))) ⊗ₘ K_pair)
                (((μ.map Zc).prod (μ.map Yo)) ⊗ₘ Kernel.prodMkRight Y K_X) := by
    unfold mutualInfo
    rw [← klDiv_map_measurableEquiv (permZXY_ZYX Z X Y), h_joint_map, h_joint_compProd,
        product_map_perm_eq_compProd μ Xs Yo Zc hXs hYo hZc]
  -- Step 2: apply chain rule (Markov kernel instances needed)
  have hPZ : IsProbabilityMeasure (μ.map Zc) := Measure.isProbabilityMeasure_map hZc.aemeasurable
  have hPY : IsProbabilityMeasure (μ.map Yo) := Measure.isProbabilityMeasure_map hYo.aemeasurable
  have hPZY : IsProbabilityMeasure (μ.map (fun ω ↦ (Zc ω, Yo ω))) :=
    Measure.isProbabilityMeasure_map hZY.aemeasurable
  -- Markov kernel instances (needed for klDiv_compProd_eq_add)
  haveI : IsMarkovKernel K_pair := by rw [hK_pair]; infer_instance
  haveI : IsMarkovKernel (Kernel.prodMkRight Y K_X) := by rw [hK_X]; infer_instance
  rw [h_LHS_klDiv,
      klDiv_compProd_eq_add (μ.map (fun ω ↦ (Zc ω, Yo ω)))
        ((μ.map Zc).prod (μ.map Yo)) K_pair (Kernel.prodMkRight Y K_X)]
  -- Goal: klDiv μ_ZY (μ_Z × μ_Y) + klDiv (μ_ZY ⊗ K_pair) (μ_ZY ⊗ K_prodRight)
  --     = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc
  congr 1
  -- Second term: klDiv ((μ.map (Zc, Yo)) ⊗ₘ K_pair) ((μ.map (Zc, Yo)) ⊗ₘ Kernel.prodMkRight Y K_X)
  --             = condMutualInfo μ Xs Yo Zc
  haveI : IsProbabilityMeasure
      ((μ.map (fun ω ↦ (Zc ω, Yo ω))) ⊗ₘ K_pair) := by infer_instance
  haveI : IsProbabilityMeasure
      ((μ.map (fun ω ↦ (Zc ω, Yo ω))) ⊗ₘ Kernel.prodMkRight Y K_X) := by infer_instance
  -- Push both args through permZYX_Z_XY (klDiv invariant)
  rw [← klDiv_map_measurableEquiv (permZYX_Z_XY Z X Y)
        ((μ.map (fun ω ↦ (Zc ω, Yo ω))) ⊗ₘ K_pair)
        ((μ.map (fun ω ↦ (Zc ω, Yo ω))) ⊗ₘ Kernel.prodMkRight Y K_X)]
  -- Compute the two pushforwards:
  -- (1) ((μ.map (Zc, Yo)) ⊗ₘ K_pair).map perm = (μ.map Zc) ⊗ₘ K_joint
  have h_first :
      ((μ.map (fun ω ↦ (Zc ω, Yo ω))) ⊗ₘ K_pair).map (permZYX_Z_XY Z X Y)
        = (μ.map Zc) ⊗ₘ K_joint := by
    rw [← h_joint_compProd, Measure.map_map (permZYX_Z_XY Z X Y).measurable hZYX]
    have : (permZYX_Z_XY Z X Y) ∘ (fun ω ↦ ((Zc ω, Yo ω), Xs ω))
        = fun ω ↦ (Zc ω, (Xs ω, Yo ω)) := by ext ω <;> rfl
    rw [this]
    exact (compProd_map_condDistrib (hXs.prodMk hYo).aemeasurable).symm
  rw [h_first, factored_map_perm_eq_compProd_prod μ Xs Yo Zc hXs hYo hZc]
  rfl

/-- Symmetry of conditional mutual information: `I(X; Y | Z) = I(Y; X | Z)`. -/
@[entry_point]
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
  have hXY : Measurable (fun ω ↦ (Xs ω, Yo ω)) := hXs.prodMk hYo
  have hYX : Measurable (fun ω ↦ (Yo ω, Xs ω)) := hYo.prodMk hXs
  let e : Z × (Y × X) ≃ᵐ Z × (X × Y) :=
    (MeasurableEquiv.refl Z).prodCongr MeasurableEquiv.prodComm
  -- joint pushforward via compProd_map_condDistrib + Measure.map_map
  have h_joint :
      ((μ.map Zc) ⊗ₘ condDistrib (fun ω ↦ (Yo ω, Xs ω)) Zc μ).map e
        = (μ.map Zc) ⊗ₘ condDistrib (fun ω ↦ (Xs ω, Yo ω)) Zc μ := by
    rw [compProd_map_condDistrib hYX.aemeasurable,
        Measure.map_map e.measurable (hZc.prodMk hYX),
        show (e ∘ (fun ω ↦ (Zc ω, Yo ω, Xs ω)))
            = (fun ω ↦ (Zc ω, Xs ω, Yo ω)) from rfl,
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

/-- Over finite alphabets, conditional mutual information is finite. -/
@[entry_point]
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
      ≤ mutualInfo μ (fun ω ↦ (Zc ω, Xs ω)) Yo := by
    rw [h_chain]; exact self_le_add_left _ _
  exact ne_top_of_le_ne_top
    (mutualInfo_ne_top μ (fun ω ↦ (Zc ω, Xs ω)) Yo (hZc.prodMk hXs) hYo) h_le

/-- Markov chain `Xs → Zc → Yo` (γ-form) implies `I(X; Y | Z) = 0`. -/
@[entry_point]
theorem condMutualInfo_eq_zero_of_markov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (_hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    condMutualInfo μ Xs Yo Zc = 0 := by
  unfold condMutualInfo
  have h_pair : Measurable (fun ω ↦ (Xs ω, Yo ω)) := hXs.prodMk hYo
  have h_num_eq : (μ.map Zc) ⊗ₘ condDistrib (fun ω ↦ (Xs ω, Yo ω)) Zc μ
      = μ.map (fun ω ↦ (Zc ω, Xs ω, Yo ω)) := compProd_map_condDistrib h_pair.aemeasurable
  rw [h_num_eq, hmarkov]
  exact klDiv_self _

/-- Markov chain `Xs → Zc → Yo` implies `I(Xs; Yo) ≤ I(Zc; Yo)`. -/
@[entry_point]
theorem mutualInfo_le_of_markov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo := by
  have h_pair_meas : Measurable (fun ω ↦ (Zc ω, Xs ω)) := hZc.prodMk hXs
  -- Step 1: DPI on second arg with f := Prod.snd, applied to Yo as first arg
  have h_snd_eq : (Prod.snd : Z × X → X) ∘ (fun ω ↦ (Zc ω, Xs ω)) = Xs := rfl
  have h_dpi_yo :
      mutualInfo μ Yo (Prod.snd ∘ (fun ω ↦ (Zc ω, Xs ω))) ≤
        mutualInfo μ Yo (fun ω ↦ (Zc ω, Xs ω)) :=
    mutualInfo_le_of_postprocess μ Yo (fun ω ↦ (Zc ω, Xs ω)) hYo h_pair_meas measurable_snd
  rw [h_snd_eq] at h_dpi_yo
  -- DPI: I(Yo; Xs) ≤ I(Yo; (Zc, Xs))
  -- Symmetrize via mutualInfo_comm: I(Xs; Yo) ≤ I((Zc, Xs); Yo)
  have h_dpi :
      mutualInfo μ Xs Yo ≤ mutualInfo μ (fun ω ↦ (Zc ω, Xs ω)) Yo := by
    rw [mutualInfo_comm μ Xs Yo hXs hYo,
        mutualInfo_comm μ (fun ω ↦ (Zc ω, Xs ω)) Yo h_pair_meas hYo]
    exact h_dpi_yo
  -- Step 2: chain rule I((Zc, Xs); Yo) = I(Zc; Yo) + condMutualInfo Xs Yo Zc
  have h_chain :
      mutualInfo μ (fun ω ↦ (Zc ω, Xs ω)) Yo
        = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc :=
    mutualInfo_chain_rule μ Xs Yo Zc hXs hYo hZc
  -- Step 3: Markov ⇒ condMI = 0
  have h_zero : condMutualInfo μ Xs Yo Zc = 0 :=
    condMutualInfo_eq_zero_of_markov μ Xs Zc Yo hXs hZc hYo hmarkov
  -- Compose
  rw [h_chain, h_zero, add_zero] at h_dpi
  exact h_dpi

/-! ## `MeasurableEquiv` invariance of `condMutualInfo`

For channel coding arguments involving reshaping such as `Y^n ↔ Y_i × Y^{≠i}`, the
following lemmas establish invariance of `condMutualInfo` under `MeasurableEquiv` on
each argument. -/

/-- Reshaping the left argument leaves the CMI fixed: `I(e ∘ X; Y | Z) = I(X; Y | Z)` for any
`MeasurableEquiv e : X ≃ᵐ X'`. -/
@[entry_point]
theorem condMutualInfo_map_left_measurableEquiv
    {X' : Type*} [MeasurableSpace X'] [StandardBorelSpace X'] [Nonempty X']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc)
    (e : X ≃ᵐ X') :
    condMutualInfo μ (fun ω ↦ e (Xs ω)) Yo Zc = condMutualInfo μ Xs Yo Zc := by
  haveI : IsProbabilityMeasure (μ.map Zc) :=
    Measure.isProbabilityMeasure_map hZc.aemeasurable
  unfold condMutualInfo
  -- The reshape on Z × (X × Y): apply `id × (e × id)`.
  let eProd : Z × X × Y ≃ᵐ Z × X' × Y :=
    (MeasurableEquiv.refl Z).prodCongr (e.prodCongr (.refl Y))
  -- Step 1: joint side via compProd_map_condDistrib (both ways) + Measure.map_map.
  have hXY : Measurable (fun ω ↦ (Xs ω, Yo ω)) := hXs.prodMk hYo
  have heXY : Measurable (fun ω ↦ (e (Xs ω), Yo ω)) := (e.measurable.comp hXs).prodMk hYo
  have h_joint :
      ((μ.map Zc) ⊗ₘ condDistrib (fun ω ↦ (e (Xs ω), Yo ω)) Zc μ)
        = ((μ.map Zc) ⊗ₘ condDistrib (fun ω ↦ (Xs ω, Yo ω)) Zc μ).map eProd := by
    rw [compProd_map_condDistrib heXY.aemeasurable,
        compProd_map_condDistrib hXY.aemeasurable,
        Measure.map_map eProd.measurable (hZc.prodMk hXY)]
    rfl
  -- Step 2: factored side via condDistrib_comp + Kernel.map_prod_eq.
  -- condDistrib (e ∘ Xs) Zc μ =ᵐ[μ.map Zc] (condDistrib Xs Zc μ).map e
  have h_cd_comp :
      condDistrib (fun ω ↦ e (Xs ω)) Zc μ
        =ᵐ[μ.map Zc] (condDistrib Xs Zc μ).map e :=
    condDistrib_comp Zc hXs.aemeasurable e.measurable
  -- Replace LHS factored kernel with map-rewritten version, then pushforward.
  have h_factored_compProd_eq :
      (μ.map Zc) ⊗ₘ
          (condDistrib (fun ω ↦ e (Xs ω)) Zc μ ×ₖ condDistrib Yo Zc μ)
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
          (condDistrib (fun ω ↦ e (Xs ω)) Zc μ ×ₖ condDistrib Yo Zc μ)
        = ((μ.map Zc) ⊗ₘ
              (condDistrib Xs Zc μ ×ₖ condDistrib Yo Zc μ)).map eProd := by
    rw [h_factored_compProd_eq, h_map_prod, Measure.compProd_map]
    · rfl
    · exact (e.measurable.prodMap measurable_id)
  rw [h_joint, h_factored, klDiv_map_measurableEquiv]

/-- Reshaping the right (middle) argument leaves the CMI fixed: `I(X; e ∘ Y | Z) = I(X; Y | Z)`
for `e : Y ≃ᵐ Y'`.

Follows from `condMutualInfo_comm` and `condMutualInfo_map_left_measurableEquiv`. -/
@[entry_point]
theorem condMutualInfo_map_middle_measurableEquiv
    {Y' : Type*} [MeasurableSpace Y'] [StandardBorelSpace Y'] [Nonempty Y']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc)
    (e : Y ≃ᵐ Y') :
    condMutualInfo μ Xs (fun ω ↦ e (Yo ω)) Zc = condMutualInfo μ Xs Yo Zc := by
  rw [condMutualInfo_comm μ Xs (fun ω ↦ e (Yo ω)) Zc hXs (e.measurable.comp hYo) hZc,
      condMutualInfo_map_left_measurableEquiv μ Yo Xs Zc hYo hXs hZc e,
      condMutualInfo_comm μ Yo Xs Zc hYo hXs hZc]

private lemma compProd_map_left_prodMap
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (ν : Measure α) [SFinite ν] (κ : Kernel α γ) [IsSFiniteKernel κ]
    (e : α ≃ᵐ β) :
    (ν ⊗ₘ κ).map (Prod.map e (id : γ → γ))
      = (ν.map e) ⊗ₘ (κ.comap e.symm e.symm.measurable) := by
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have h_prodMap : Measurable (Prod.map (e : α → β) (id : γ → γ)) :=
    e.measurable.prodMap measurable_id
  have hfg : Measurable (f ∘ Prod.map (e : α → β) (id : γ → γ)) := hf.comp h_prodMap
  -- LHS chain.
  rw [lintegral_map hf h_prodMap]
  -- Goal LHS: ∫⁻ a, f (Prod.map e id a) ∂(ν ⊗ₘ κ).
  -- Convert via show to (f ∘ Prod.map e id) a form so lintegral_compProd applies.
  rw [show (fun a : α × γ ↦ f (Prod.map (e : α → β) (id : γ → γ) a))
      = (f ∘ Prod.map (e : α → β) (id : γ → γ)) from rfl,
      Measure.lintegral_compProd hfg]
  -- RHS chain.
  rw [Measure.lintegral_compProd hf]
  rw [lintegral_map
        (Measurable.lintegral_kernel_prod_right' hf
          (κ := κ.comap e.symm e.symm.measurable))
        e.measurable]
  refine lintegral_congr fun a ↦ ?_
  rw [Kernel.comap_apply _ e.symm.measurable]
  simp [Prod.map]

/-- Reshaping the conditioner leaves the CMI fixed: `I(X; Y | e ∘ Z) = I(X; Y | Z)` for any
`MeasurableEquiv e : Z ≃ᵐ Z'`. The conditioner carries the same information after a
measurable-equiv relabel. Companion to `condMutualInfo_map_left_measurableEquiv` and
`condMutualInfo_map_middle_measurableEquiv` (the third argument slot).
@audit:ok -/
@[entry_point]
theorem condMutualInfo_map_cond_measurableEquiv
    {Z' : Type*} [MeasurableSpace Z']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc)
    (e : Z ≃ᵐ Z') :
    condMutualInfo μ Xs Yo (fun ω ↦ e (Zc ω)) = condMutualInfo μ Xs Yo Zc := by
  haveI : IsProbabilityMeasure (μ.map Zc) :=
    Measure.isProbabilityMeasure_map hZc.aemeasurable
  have heZc : Measurable (fun ω ↦ e (Zc ω)) := e.measurable.comp hZc
  haveI : IsProbabilityMeasure (μ.map (fun ω ↦ e (Zc ω))) :=
    Measure.isProbabilityMeasure_map heZc.aemeasurable
  have hmap_e : μ.map (fun ω ↦ e (Zc ω)) = (μ.map Zc).map e :=
    (Measure.map_map e.measurable hZc).symm
  unfold condMutualInfo
  set K_X := condDistrib Xs Zc μ with hK_X
  set K_Y := condDistrib Yo Zc μ with hK_Y
  have hXY : Measurable (fun ω ↦ (Xs ω, Yo ω)) := hXs.prodMk hYo
  -- The reshape on `Z × (X × Y)`: apply `e × id`.
  let eZ : Z × (X × Y) ≃ᵐ Z' × (X × Y) := e.prodCongr (.refl (X × Y))
  -- Joint side: both via `compProd_map_condDistrib` + `Measure.map_map`.
  have h_joint :
      (μ.map (fun ω ↦ e (Zc ω))) ⊗ₘ condDistrib (fun ω ↦ (Xs ω, Yo ω)) (fun ω ↦ e (Zc ω)) μ
        = ((μ.map Zc) ⊗ₘ condDistrib (fun ω ↦ (Xs ω, Yo ω)) Zc μ).map eZ := by
    rw [compProd_map_condDistrib hXY.aemeasurable,
        compProd_map_condDistrib hXY.aemeasurable,
        Measure.map_map eZ.measurable (hZc.prodMk hXY)]
    rfl
  -- Per-marginal: reparametrizing the conditioning variable by `e` is `comap e.symm`.
  have hX_eq : condDistrib Xs (fun ω ↦ e (Zc ω)) μ
      =ᵐ[μ.map (fun ω ↦ e (Zc ω))] K_X.comap e.symm e.symm.measurable := by
    refine condDistrib_ae_eq_of_measure_eq_compProd (fun ω ↦ e (Zc ω)) hXs.aemeasurable ?_
    rw [hmap_e, hK_X, ← compProd_map_left_prodMap (μ.map Zc) (condDistrib Xs Zc μ) e,
        compProd_map_condDistrib hXs.aemeasurable,
        Measure.map_map (e.measurable.prodMap measurable_id) (hZc.prodMk hXs)]
    rfl
  have hY_eq : condDistrib Yo (fun ω ↦ e (Zc ω)) μ
      =ᵐ[μ.map (fun ω ↦ e (Zc ω))] K_Y.comap e.symm e.symm.measurable := by
    refine condDistrib_ae_eq_of_measure_eq_compProd (fun ω ↦ e (Zc ω)) hYo.aemeasurable ?_
    rw [hmap_e, hK_Y, ← compProd_map_left_prodMap (μ.map Zc) (condDistrib Yo Zc μ) e,
        compProd_map_condDistrib hYo.aemeasurable,
        Measure.map_map (e.measurable.prodMap measurable_id) (hZc.prodMk hYo)]
    rfl
  -- Factored side.
  have h_factored :
      (μ.map (fun ω ↦ e (Zc ω))) ⊗ₘ
          (condDistrib Xs (fun ω ↦ e (Zc ω)) μ ×ₖ condDistrib Yo (fun ω ↦ e (Zc ω)) μ)
        = ((μ.map Zc) ⊗ₘ (K_X ×ₖ K_Y)).map eZ := by
    rw [show ((μ.map Zc) ⊗ₘ (K_X ×ₖ K_Y)).map eZ
          = ((μ.map Zc) ⊗ₘ (K_X ×ₖ K_Y)).map (Prod.map e id) from rfl,
        compProd_map_left_prodMap (μ.map Zc) (K_X ×ₖ K_Y) e, Kernel.comap_prod, ← hmap_e]
    refine (Measure.compProd_congr ?_).symm
    filter_upwards [hX_eq, hY_eq] with z hzx hzy
    ext s hs
    rw [Kernel.prod_apply, Kernel.prod_apply, hzx, hzy]
  rw [h_joint, h_factored, klDiv_map_measurableEquiv]

/-- Markov chains are stable under post-processing on the left: if `Xs → Zc → Yo` is a Markov
chain and `f : X → X'` is measurable, then `f ∘ Xs → Zc → Yo` is also a Markov chain. -/
@[entry_point]
theorem isMarkovChain_map_left
    {X' : Type*} [MeasurableSpace X'] [StandardBorelSpace X'] [Nonempty X']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    {f : X → X'} (hf : Measurable f)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    IsMarkovChain μ (fun ω ↦ f (Xs ω)) Zc Yo := by
  haveI : IsProbabilityMeasure (μ.map Zc) :=
    Measure.isProbabilityMeasure_map hZc.aemeasurable
  unfold IsMarkovChain
  have hZXY : Measurable (fun ω ↦ (Zc ω, Xs ω, Yo ω)) := hZc.prodMk (hXs.prodMk hYo)
  -- LHS: μ.map (Z, f∘X, Y) = (μ.map (Z, X, Y)).map (id × (f × id)).
  have h_LHS :
      μ.map (fun ω ↦ (Zc ω, f (Xs ω), Yo ω))
        = (μ.map (fun ω ↦ (Zc ω, Xs ω, Yo ω))).map
            (Prod.map (id : Z → Z) (Prod.map f (id : Y → Y))) := by
    rw [Measure.map_map (measurable_id.prodMap (hf.prodMap measurable_id)) hZXY]
    rfl
  rw [h_LHS, hmarkov]
  -- Goal: ((μ.map Zc) ⊗ₘ (K_X ×ₖ K_Y)).map (id × (f × id)) = (μ.map Zc) ⊗ₘ (K_{f∘X} ×ₖ K_Y).
  rw [← Measure.compProd_map (hf.prodMap measurable_id),
      ← Kernel.map_prod_eq _ _ hf]
  -- Goal: (μ.map Zc) ⊗ₘ ((K_X.map f) ×ₖ K_Y) = (μ.map Zc) ⊗ₘ (K_{f∘X} ×ₖ K_Y).
  refine (Measure.compProd_congr ?_).symm
  have h_cd : condDistrib (fun ω ↦ f (Xs ω)) Zc μ
      =ᵐ[μ.map Zc] (condDistrib Xs Zc μ).map f :=
    condDistrib_comp Zc hXs.aemeasurable hf
  filter_upwards [h_cd] with z hz
  ext s hs
  rw [Kernel.prod_apply, Kernel.prod_apply, hz]

end InformationTheory.Shannon
