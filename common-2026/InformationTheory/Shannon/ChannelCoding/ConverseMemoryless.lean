import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.ConverseMemorylessMarkov

/-!
# Channel coding converse — pure `IsMemorylessChannel` form

Bridge lemmas deriving both `IsMemorylessChannelStrong` Markov axioms from
`IsMemorylessChannel` (γ-form: single Markov chain `(X^{≠i}, Y^{≠i}) → X_i → Y_i`).

## Main definitions

* `per_letter_markov_of_memoryless` — derives per-letter Markov chain from `IsMemorylessChannel`.
* `outputs_cond_indep_of_memoryless` — derives outputs conditional independence via the graphoid
  weak union lemma `isMarkovChain_weakUnion_left_to_conditioner` and conditioner reshape.

## Main statements

* `channel_coding_converse_general_memoryless_pure` — channel coding converse under
  `IsMemorylessChannel` alone (both axioms auto-derived).
-/

namespace InformationTheory.Shannon.ChannelCodingConverseGeneral

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Graphoid helper lemmas (file-scoped) -/

section GraphoidHelpers

set_option linter.unusedSectionVars false

variable {X Y Z : Type*}
  [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]

/-- **Bundle the conditioner into the left endpoint** (graphoid trivial-inclusion).

If `Markov μ As Zc Yo`, then `Markov μ (As, Zc) Zc Yo`: bundling the conditioner `Zc` as a
copy on the left endpoint preserves the Markov chain (since `Zc` is determined by the
conditioning, the extra copy carries no new conditional information).

**Strategy**: identify `condDistrib (As, Zc) Zc μ =ᵐ[μ.map Zc] (condDistrib As Zc μ) ×ₖ Kernel.id`
via `condDistrib_ae_eq_of_measure_eq_compProd`, then push the original γ-form through
`g : Z × (X × Y) → Z × ((X × Z) × Y)`. -/
private lemma isMarkovChain_bundle_left_with_conditioner
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (As : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hAs : Measurable As) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : Shannon.IsMarkovChain μ As Zc Yo) :
    Shannon.IsMarkovChain μ (fun ω => (As ω, Zc ω)) Zc Yo := by
  haveI : IsProbabilityMeasure (μ.map Zc) :=
    Measure.isProbabilityMeasure_map hZc.aemeasurable
  unfold Shannon.IsMarkovChain
  set K_A : Kernel Z X := condDistrib As Zc μ with hK_A_def
  set K_Y : Kernel Z Y := condDistrib Yo Zc μ with hK_Y_def
  set K_AZ : Kernel Z (X × Z) := condDistrib (fun ω => (As ω, Zc ω)) Zc μ with hK_AZ_def
  have h_K_AZ_eq : K_AZ =ᵐ[μ.map Zc] K_A ×ₖ (Kernel.id : Kernel Z Z) := by
    refine condDistrib_ae_eq_of_measure_eq_compProd Zc
      ((hAs.prodMk hZc).aemeasurable) ?_
    have h_LHS_eq :
        μ.map (fun ω => (Zc ω, As ω, Zc ω))
          = (μ.map (fun ω => (Zc ω, As ω))).map (fun p : Z × X => (p.1, (p.2, p.1))) := by
      rw [Measure.map_map ?_ (hZc.prodMk hAs)]
      · rfl
      · exact measurable_fst.prodMk (measurable_snd.prodMk measurable_fst)
    have h_marginal : μ.map (fun ω => (Zc ω, As ω)) = (μ.map Zc) ⊗ₘ K_A :=
      (compProd_map_condDistrib hAs.aemeasurable).symm
    rw [h_LHS_eq, h_marginal]
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    have h_map_meas : Measurable (fun p : Z × X => (p.1, p.2, p.1)) :=
      measurable_fst.prodMk (measurable_snd.prodMk measurable_fst)
    rw [lintegral_map hf h_map_meas]
    rw [Measure.lintegral_compProd hf]
    rw [show (fun a : Z × X => f (a.1, a.2, a.1))
        = (fun a : Z × X => (fun p : Z × X => f (p.1, p.2, p.1)) a) from rfl]
    rw [Measure.lintegral_compProd
          (show Measurable (fun p : Z × X => f (p.1, p.2, p.1)) from
            hf.comp h_map_meas)]
    refine lintegral_congr fun z => ?_
    have h_f_z : Measurable (fun p : X × Z => f (z, p)) :=
      hf.comp (measurable_const.prodMk measurable_id)
    rw [Kernel.lintegral_prod_id (κ := K_A) (b := z) h_f_z]
  have h_compProd_ae_eq :
      (μ.map Zc) ⊗ₘ (K_AZ ×ₖ K_Y)
        = (μ.map Zc) ⊗ₘ ((K_A ×ₖ (Kernel.id : Kernel Z Z)) ×ₖ K_Y) := by
    refine Measure.compProd_congr ?_
    filter_upwards [h_K_AZ_eq] with z hz
    ext s hs
    rw [Kernel.prod_apply, Kernel.prod_apply, hz]
  rw [h_compProd_ae_eq]
  have h_LHS :
      μ.map (fun ω => (Zc ω, (As ω, Zc ω), Yo ω))
        = (μ.map (fun ω => (Zc ω, As ω, Yo ω))).map
            (fun p : Z × X × Y => (p.1, (p.2.1, p.1), p.2.2)) := by
    have hm : Measurable
        (fun p : Z × X × Y => (p.1, (p.2.1, p.1), p.2.2)) := by
      refine measurable_fst.prodMk (Measurable.prodMk ?_ ?_)
      · exact (measurable_fst.comp measurable_snd).prodMk measurable_fst
      · exact measurable_snd.comp measurable_snd
    rw [Measure.map_map hm (hZc.prodMk (hAs.prodMk hYo))]
    rfl
  rw [h_LHS, hmarkov]
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have h_g_meas : Measurable
      (fun p : Z × X × Y => (p.1, (p.2.1, p.1), p.2.2)) := by
    refine measurable_fst.prodMk (Measurable.prodMk ?_ ?_)
    · exact (measurable_fst.comp measurable_snd).prodMk measurable_fst
    · exact measurable_snd.comp measurable_snd
  rw [lintegral_map hf h_g_meas]
  rw [Measure.lintegral_compProd hf]
  rw [show (fun a : Z × X × Y => f (a.1, (a.2.1, a.1), a.2.2))
      = (fun a : Z × X × Y => (fun p : Z × X × Y => f (p.1, (p.2.1, p.1), p.2.2)) a) from rfl]
  rw [Measure.lintegral_compProd
        (show Measurable (fun p : Z × X × Y => f (p.1, (p.2.1, p.1), p.2.2)) from
          hf.comp h_g_meas)]
  refine lintegral_congr fun z => ?_
  rw [Kernel.prod_apply, Kernel.prod_apply, Kernel.prod_apply, Kernel.id_apply z]
  rw [Measure.prod_dirac]
  have h_lhs_meas : Measurable (fun q : X × Y => f (z, (q.1, z), q.2)) := by
    refine hf.comp ?_
    refine measurable_const.prodMk (Measurable.prodMk ?_ ?_)
    · exact (measurable_fst.prodMk measurable_const)
    · exact measurable_snd
  have h_rhs_meas : Measurable (fun q : (X × Z) × Y => f (z, q)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  rw [MeasureTheory.lintegral_prod _ h_lhs_meas.aemeasurable,
      MeasureTheory.lintegral_prod _ h_rhs_meas.aemeasurable]
  have h_inner_meas : Measurable (fun p : X × Z => ∫⁻ y, f (z, p, y) ∂((condDistrib Yo Zc μ) z)) := by
    refine Measurable.lintegral_prod_right' (f := fun q : (X × Z) × Y => f (z, q.1, q.2)) ?_
    exact hf.comp (measurable_const.prodMk
      ((measurable_fst.prodMk measurable_snd).comp measurable_fst |>.prodMk
        measurable_snd))
  have h_pair_meas : Measurable (fun a : X => (a, z)) :=
    measurable_id.prodMk measurable_const
  rw [lintegral_map h_inner_meas h_pair_meas]

private lemma condDistrib_prodMk_right_ae_eq_comap
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (As : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hAs : Measurable As) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (h_markov : Shannon.IsMarkovChain μ As Zc Yo) :
    (condDistrib Yo (fun ω => (Zc ω, As ω)) μ)
      =ᵐ[μ.map (fun ω => (Zc ω, As ω))]
        ((condDistrib Yo Zc μ).comap (fun za : Z × X => za.1) measurable_fst
          : Kernel (Z × X) Y) := by
  haveI : IsProbabilityMeasure (μ.map Zc) :=
    Measure.isProbabilityMeasure_map hZc.aemeasurable
  have hZA : Measurable (fun ω => (Zc ω, As ω)) := hZc.prodMk hAs
  haveI : IsProbabilityMeasure (μ.map (fun ω => (Zc ω, As ω))) :=
    Measure.isProbabilityMeasure_map hZA.aemeasurable
  set K_A : Kernel Z X := condDistrib As Zc μ with hK_A_def
  set K_Y : Kernel Z Y := condDistrib Yo Zc μ with hK_Y_def
  have h_ZA_marginal : μ.map (fun ω => (Zc ω, As ω)) = (μ.map Zc) ⊗ₘ K_A :=
    (compProd_map_condDistrib hAs.aemeasurable).symm
  refine condDistrib_ae_eq_of_measure_eq_compProd
    (fun ω => (Zc ω, As ω)) hYo.aemeasurable ?_
  -- Need: μ.map ((Z, A), Y) = (μ.map (Z, A)) ⊗ₘ (K_Y.comap fst).
  -- LHS = (μ.map (Z, A, Y)).map (fun (z, a, y) => ((z, a), y)).
  have h_perm_meas : Measurable
      (fun p : Z × X × Y => ((p.1, p.2.1), p.2.2)) :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  have h_LHS_reshape :
      μ.map (fun ω => ((Zc ω, As ω), Yo ω))
        = (μ.map (fun ω => (Zc ω, As ω, Yo ω))).map
            (fun p : Z × X × Y => ((p.1, p.2.1), p.2.2)) := by
    rw [Measure.map_map h_perm_meas (hZc.prodMk (hAs.prodMk hYo))]
    rfl
  rw [h_LHS_reshape, h_markov, h_ZA_marginal]
  -- Now both sides are compProds; verify via Measure.ext_of_lintegral.
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  -- LHS: ((μ.map Zc) ⊗ₘ (K_A ×ₖ K_Y)).map perm
  rw [lintegral_map hf h_perm_meas]
  -- Rewrite the integrand into the canonical compProd form (z, ay).
  have h_LHS_fun :
      (fun a : Z × X × Y => f ((a.1, a.2.1), a.2.2))
        = fun a : Z × X × Y =>
            (fun p : Z × (X × Y) => f ((p.1, p.2.1), p.2.2)) a := rfl
  rw [h_LHS_fun]
  have hgL : Measurable (fun p : Z × (X × Y) => f ((p.1, p.2.1), p.2.2)) :=
    hf.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))
  rw [Measure.lintegral_compProd hgL]
  -- RHS: ((μ.map Zc) ⊗ₘ K_A) ⊗ₘ (K_Y.comap fst)
  rw [Measure.lintegral_compProd hf]
  rw [Measure.lintegral_compProd
        (Measurable.lintegral_kernel_prod_right' (κ := K_Y.comap _ measurable_fst) hf)]
  refine lintegral_congr fun z => ?_
  -- Inner: ∫⁻ ay ∂(K_A z ×ₖ K_Y z), f ((z, ay.1), ay.2)
  -- vs    ∫⁻ a ∂(K_A z), ∫⁻ y ∂(K_Y.comap fst (z, a)), f ((z, a), y)
  rw [Kernel.prod_apply]
  have hgL_z : Measurable (fun p : X × Y => f ((z, p.1), p.2)) :=
    hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  rw [MeasureTheory.lintegral_prod _ hgL_z.aemeasurable]
  refine lintegral_congr fun a => ?_
  rw [Kernel.comap_apply _ measurable_fst]

/-- **Graphoid weak union (γ-form direct)**: From `Markov μ (As, Bs) Zc Yo`
(i.e., `Yo ⫫ (As, Bs) | Zc`), derive `Markov μ Bs (Zc, As) Yo` (i.e.,
`Yo ⫫ Bs | (Zc, As)`).

This is the graphoid weak union axiom: bundle a piece of the joint left endpoint into
the conditioner.

**Proof structure (`Measure.ext_of_lintegral`)**:
1. Unfold the goal `IsMarkovChain` to a `compProd` equality at the level of `μ.map`.
2. Expand `μ.map (Z, A)` via `compProd_map_condDistrib` to `(μ.map Z) ⊗ₘ K_A`.
3. Identify `condDistrib Yo (Zc, As) μ =ᵐ[μ.map (Zc, As)] (K_Y).comap Prod.fst _`
   by reducing to `μ.map ((Z, A), Y) = (μ.map (Z, A)) ⊗ₘ (K_Y.comap fst)` and applying
   the original Markov to compute `μ.map (Z, A, Y)`.
4. Match the iterated lintegral on both sides. -/
private lemma isMarkovChain_weakUnion_left_to_conditioner
    {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (As : Ω → A) (Bs : Ω → B) (Zc : Ω → Z) (Yo : Ω → Y)
    (hAs : Measurable As) (hBs : Measurable Bs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : Shannon.IsMarkovChain μ (fun ω => (As ω, Bs ω)) Zc Yo) :
    Shannon.IsMarkovChain μ Bs (fun ω => (Zc ω, As ω)) Yo := by
  haveI : IsProbabilityMeasure (μ.map Zc) :=
    Measure.isProbabilityMeasure_map hZc.aemeasurable
  have hZA : Measurable (fun ω => (Zc ω, As ω)) := hZc.prodMk hAs
  haveI : IsProbabilityMeasure (μ.map (fun ω => (Zc ω, As ω))) :=
    Measure.isProbabilityMeasure_map hZA.aemeasurable
  -- Kernel abbreviations.
  set K_A : Kernel Z A := condDistrib As Zc μ with hK_A_def
  set K_Y : Kernel Z Y := condDistrib Yo Zc μ with hK_Y_def
  set K_AB : Kernel Z (A × B) :=
    condDistrib (fun ω => (As ω, Bs ω)) Zc μ with hK_AB_def
  set K_B' : Kernel (Z × A) B :=
    condDistrib Bs (fun ω => (Zc ω, As ω)) μ with hK_B'_def
  set K_Y' : Kernel (Z × A) Y :=
    condDistrib Yo (fun ω => (Zc ω, As ω)) μ with hK_Y'_def
  -- Marginal: μ.map (Z, A) = (μ.map Z) ⊗ₘ K_A.
  have h_ZA_marginal : μ.map (fun ω => (Zc ω, As ω)) = (μ.map Zc) ⊗ₘ K_A :=
    (compProd_map_condDistrib hAs.aemeasurable).symm
  -- Step (i): Drop B from the original Markov via isMarkovChain_map_left.
  -- Yields Markov μ As Zc Yo, i.e. μ.map (Zc, As, Yo) = (μ.map Zc) ⊗ₘ (K_A ×ₖ K_Y).
  have h_AZY : Shannon.IsMarkovChain μ As Zc Yo := by
    have hAB : Measurable (fun ω => (As ω, Bs ω)) := hAs.prodMk hBs
    exact Shannon.isMarkovChain_map_left μ (fun ω => (As ω, Bs ω))
      Zc Yo hAB hZc hYo measurable_fst hmarkov
  -- Step (ii): Identify K_Y' =ᵐ[μ.map (Z, A)] K_Y.comap fst.
  have h_K_Y'_eq :
      K_Y' =ᵐ[μ.map (fun ω => (Zc ω, As ω))]
        (K_Y.comap (fun za : Z × A => za.1) measurable_fst : Kernel (Z × A) Y) :=
    condDistrib_prodMk_right_ae_eq_comap μ As Zc Yo hAs hZc hYo h_AZY
  -- Replace K_Y' with K_Y.comap fst in the goal via compProd_congr.
  unfold Shannon.IsMarkovChain
  have h_RHS_replace :
      (μ.map (fun ω => (Zc ω, As ω))) ⊗ₘ (K_B' ×ₖ K_Y')
        = (μ.map (fun ω => (Zc ω, As ω))) ⊗ₘ
            (K_B' ×ₖ (K_Y.comap (fun za : Z × A => za.1) measurable_fst : Kernel (Z × A) Y)) := by
    refine Measure.compProd_congr ?_
    filter_upwards [h_K_Y'_eq] with za hza
    ext s hs
    rw [Kernel.prod_apply, Kernel.prod_apply, hza]
  rw [h_RHS_replace]
  -- Step (iii): Main equation. Strategy — reduce both sides to the SAME triple
  -- iterated lintegral
  --     ∫⁻ z ∂(μ.map Zc), ∫⁻ ab ∂(K_AB z), ∫⁻ y ∂(K_Y z), f ((z, ab.1), ab.2, y).
  -- LHS path uses the original Markov hypothesis directly.
  -- RHS path: unfold the Kernel.prod and the comap, then absorb the (μ.map (Z,A)) ⊗ₘ K_B'
  --          via compProd_map_condDistrib back to μ.map (Z, A, B), and the original Markov
  --          again to convert μ.map (Z, A, B) to a kernel-level integral over K_AB.
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  -- LHS: μ.map ((Z, A), B, Y) — express via lintegral_map then use original Markov.
  have hZABY : Measurable (fun ω => ((Zc ω, As ω), Bs ω, Yo ω)) :=
    hZA.prodMk (hBs.prodMk hYo)
  rw [lintegral_map hf hZABY]
  -- LHS form: ∫⁻ ω, f ((Z ω, A ω), B ω, Y ω) ∂μ.
  -- Rewrite as lintegral over μ.map (Z, (A, B), Y) via lintegral_map.
  -- Permute (Z, (A, B), Y) → ((Z, A), B, Y) explicitly.
  have h_perm₂_meas : Measurable
      (fun p : Z × (A × B) × Y => ((p.1, p.2.1.1), p.2.1.2, p.2.2)) := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_fst.prodMk (measurable_fst.comp (measurable_fst.comp measurable_snd))
    · exact (measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)
  have hLHS_int_eq :
      ∫⁻ ω, f ((Zc ω, As ω), Bs ω, Yo ω) ∂μ
        = ∫⁻ p, f ((p.1, p.2.1.1), p.2.1.2, p.2.2)
            ∂(μ.map (fun ω => (Zc ω, (As ω, Bs ω), Yo ω))) :=
    (lintegral_map (hf.comp h_perm₂_meas)
      (hZc.prodMk ((hAs.prodMk hBs).prodMk hYo))).symm
  rw [hLHS_int_eq, hmarkov]
  -- LHS = ∫⁻ p ∂((μ.map Zc) ⊗ₘ (K_AB ×ₖ K_Y)), f ((p.1, p.2.1.1), p.2.1.2, p.2.2).
  have h_int_LHS_meas :
      Measurable (fun p : Z × (A × B) × Y => f ((p.1, p.2.1.1), p.2.1.2, p.2.2)) :=
    hf.comp h_perm₂_meas
  rw [Measure.lintegral_compProd h_int_LHS_meas]
  -- LHS = ∫⁻ z ∂(μ.map Zc), ∫⁻ q ∂(K_AB z ×ₖ K_Y z), f ((z, q.1.1), q.1.2, q.2).
  -- RHS: μ.map (Z, A) ⊗ₘ (K_B' ×ₖ K_Y.comap fst).
  rw [Measure.lintegral_compProd hf]
  -- RHS = ∫⁻ za ∂(μ.map (Z, A)), ∫⁻ p ∂(K_B' ×ₖ K_Y.comap fst) za, f (za, p).
  rw [h_ZA_marginal]
  -- RHS = ∫⁻ za ∂((μ.map Zc) ⊗ₘ K_A), ∫⁻ p ∂(K_B' ×ₖ K_Y.comap fst) za, f (za, p).
  rw [Measure.lintegral_compProd
        (Measurable.lintegral_kernel_prod_right' (κ :=
          K_B' ×ₖ (K_Y.comap (fun za : Z × A => za.1) measurable_fst : Kernel (Z × A) Y)) hf)]
  -- RHS = ∫⁻ z ∂(μ.map Zc), ∫⁻ a ∂(K_A z),
  --         ∫⁻ p ∂((K_B' ×ₖ K_Y.comap fst) (z, a)), f ((z, a), p).
  -- Identify K_AB =ᵐ K_A ⊗ₖ K_B' under μ.map Zc, via condDistrib_ae_eq_of_measure_eq_compProd.
  -- We need: μ.map (Zc, (As, Bs)) = (μ.map Zc) ⊗ₘ (K_A ⊗ₖ K_B').
  have h_K_AB_eq :
      K_AB =ᵐ[μ.map Zc] K_A ⊗ₖ K_B' := by
    refine condDistrib_ae_eq_of_measure_eq_compProd Zc
      ((hAs.prodMk hBs).aemeasurable) ?_
    -- Goal: μ.map (Zc, (As, Bs)) = (μ.map Zc) ⊗ₘ (K_A ⊗ₖ K_B').
    -- Build chain: μ.map (Zc, (As, Bs)) = (μ.map ((Zc, As), Bs)).map prodAssoc
    --   = ((μ.map (Zc, As)) ⊗ₘ K_B').map prodAssoc   [compProd_map_condDistrib]
    --   = (((μ.map Zc) ⊗ₘ K_A) ⊗ₘ K_B').map prodAssoc [h_ZA_marginal]
    --   = (μ.map Zc) ⊗ₘ (K_A ⊗ₖ K_B')                 [compProd_assoc']
    have h_reshape :
        μ.map (fun ω => (Zc ω, As ω, Bs ω))
          = (μ.map (fun ω => ((Zc ω, As ω), Bs ω))).map MeasurableEquiv.prodAssoc := by
      rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable (hZA.prodMk hBs)]
      rfl
    rw [h_reshape, ← compProd_map_condDistrib (hBs.aemeasurable) (X := fun ω => (Zc ω, As ω)),
        h_ZA_marginal, Measure.compProd_assoc']
  -- Now use the kernel equality to rewrite the LHS inner under μ.map Zc.
  -- The current goal is at a specific z. We use lintegral_congr (under μ.map Zc) to drop into a.e.
  refine lintegral_congr_ae (μ := μ.map Zc) ?_
  filter_upwards [h_K_AB_eq] with z hz
  -- Inner goal at z (a.e. under μ.map Zc):
  --   ∫⁻ p ∂(K_AB ×ₖ K_Y) z, f ((z, p.1.1), p.1.2, p.2)
  --     = ∫⁻ a ∂(K_A z), ∫⁻ p ∂(K_B' ×ₖ K_Y.comap fst) (z, a), f ((z, a), p).
  -- Step 1: expand Kernel.prod on LHS.
  rw [Kernel.prod_apply]
  -- LHS = ∫⁻ p ∂((K_AB z).prod (K_Y z)), f ((z, p.1.1), p.1.2, p.2).
  -- Step 2: apply hz to replace K_AB z with (K_A ⊗ₖ K_B') z, fold K_AB definitionally first.
  -- The target uses condDistrib (fun ω => (As ω, Bs ω)) Zc μ z — same as K_AB z by `rfl`.
  rw [show (condDistrib (fun ω => (As ω, Bs ω)) Zc μ) z = K_AB z from rfl, hz]
  -- Step 3: convert .prod outer integral via lintegral_prod.
  have h_meas_q : Measurable (fun q : (A × B) × Y => f ((z, q.1.1), q.1.2, q.2)) := by
    refine hf.comp ?_
    refine Measurable.prodMk ?_ ?_
    · exact measurable_const.prodMk (measurable_fst.comp measurable_fst)
    · exact (measurable_snd.comp measurable_fst).prodMk measurable_snd
  rw [MeasureTheory.lintegral_prod _ h_meas_q.aemeasurable]
  -- LHS = ∫⁻ ab ∂((K_A ⊗ₖ K_B') z), ∫⁻ y ∂(K_Y z), f ((z, ab.1), ab.2, y).
  have h_inner_meas : Measurable
      (fun ab : A × B => ∫⁻ y, f ((z, ab.1), ab.2, y) ∂(K_Y z)) := by
    refine Measurable.lintegral_prod_right' (f := fun p : (A × B) × Y => f ((z, p.1.1), p.1.2, p.2)) ?_
    exact h_meas_q
  rw [Kernel.lintegral_compProd K_A K_B' z h_inner_meas]
  -- LHS = ∫⁻ a ∂(K_A z), ∫⁻ b ∂(K_B' (z, a)), ∫⁻ y ∂(K_Y z), f ((z, a), b, y).
  refine lintegral_congr fun a => ?_
  -- RHS at fixed (z, a): ∫⁻ p ∂((K_B' ×ₖ K_Y.comap fst) (z, a)), f ((z, a), p).
  rw [Kernel.prod_apply]
  have h_meas_p : Measurable (fun p : B × Y => f ((z, a), p)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  rw [MeasureTheory.lintegral_prod _ h_meas_p.aemeasurable]
  refine lintegral_congr fun b => ?_
  rw [Kernel.comap_apply _ measurable_fst]

/-- Auxiliary: `condDistrib Xs (e ∘ Zc') μ =ᵐ[μ.map (e ∘ Zc')] (condDistrib Xs Zc' μ).comap e.symm`. -/
private lemma cond_reshape_kernel_lemma {X' Z Z' : Type*}
    [MeasurableSpace X'] [StandardBorelSpace X'] [Nonempty X']
    [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    [MeasurableSpace Z'] [StandardBorelSpace Z'] [Nonempty Z']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X') (Zc' : Ω → Z')
    (hXs : Measurable Xs) (hZc' : Measurable Zc') (e : Z' ≃ᵐ Z)
    (h_map_eq : μ.map (fun ω => e (Zc' ω)) = (μ.map Zc').map e) :
    condDistrib Xs (fun ω => e (Zc' ω)) μ
      =ᵐ[μ.map (fun ω => e (Zc' ω))]
        (condDistrib Xs Zc' μ).comap (e.symm : Z → Z') e.symm.measurable := by
  haveI : IsProbabilityMeasure (μ.map Zc') :=
    Measure.isProbabilityMeasure_map hZc'.aemeasurable
  haveI : IsProbabilityMeasure (μ.map (fun ω => e (Zc' ω))) :=
    Measure.isProbabilityMeasure_map (e.measurable.comp hZc').aemeasurable
  set K_X' : Kernel Z' X' := condDistrib Xs Zc' μ
  refine condDistrib_ae_eq_of_measure_eq_compProd
    (fun ω => e (Zc' ω)) hXs.aemeasurable ?_
  have h₁ : μ.map (fun ω => (e (Zc' ω), Xs ω))
      = (μ.map (fun ω => (Zc' ω, Xs ω))).map (Prod.map (e : Z' → Z) (id : X' → X')) := by
    rw [Measure.map_map (e.measurable.prodMap measurable_id) (hZc'.prodMk hXs)]; rfl
  have h₂ : μ.map (fun ω => (Zc' ω, Xs ω)) = (μ.map Zc') ⊗ₘ K_X' :=
    (compProd_map_condDistrib hXs.aemeasurable).symm
  rw [h₁, h₂]
  refine Measure.ext_of_lintegral _ fun h hh => ?_
  rw [lintegral_map hh (e.measurable.prodMap measurable_id)]
  have hh_inner : Measurable (fun a : Z' × X' => h (Prod.map e id a)) :=
    hh.comp (e.measurable.prodMap measurable_id)
  rw [Measure.lintegral_compProd hh_inner]
  rw [Measure.lintegral_compProd hh]
  -- LHS: ∫⁻ z' ∂(μ.map Zc'), ∫⁻ x ∂(K_X' z'), h ((Prod.map e id) (z', x))
  -- RHS: ∫⁻ z ∂(μ.map (e ∘ Zc')), ∫⁻ x ∂(K_X'.comap e.symm) z, h (z, x)
  rw [h_map_eq]
  have h_inner_meas2 : Measurable
      (fun a : Z => ∫⁻ b, h (a, b) ∂(K_X'.comap e.symm e.symm.measurable) a) :=
    Measurable.lintegral_kernel_prod_right' (κ := K_X'.comap e.symm e.symm.measurable) hh
  rw [lintegral_map h_inner_meas2 e.measurable]
  refine lintegral_congr fun z' => ?_
  rw [Kernel.comap_apply _ e.symm.measurable]
  simp [Prod.map]

/-- **Markov chain conditioner reshape via measurable equiv**: if `Markov μ Xs (e ∘ Z') Yo`
and `e : Z' ≃ᵐ Z`, then `Markov μ Xs Z' Yo`. -/
private lemma isMarkovChain_map_conditioner_measurableEquiv
    {X Z Z' : Type*}
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    [MeasurableSpace Z'] [StandardBorelSpace Z'] [Nonempty Z']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Zc' : Ω → Z') (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZc' : Measurable Zc') (hYo : Measurable Yo)
    (e : Z' ≃ᵐ Z)
    (hmarkov : Shannon.IsMarkovChain μ Xs (fun ω => e (Zc' ω)) Yo) :
    Shannon.IsMarkovChain μ Xs Zc' Yo := by
  haveI : IsProbabilityMeasure (μ.map Zc') :=
    Measure.isProbabilityMeasure_map hZc'.aemeasurable
  haveI : IsProbabilityMeasure (μ.map (fun ω => e (Zc' ω))) :=
    Measure.isProbabilityMeasure_map (e.measurable.comp hZc').aemeasurable
  unfold Shannon.IsMarkovChain at hmarkov ⊢
  set K_X' : Kernel Z' X := condDistrib Xs Zc' μ
  set K_Y' : Kernel Z' Y := condDistrib Yo Zc' μ
  set K_Xe : Kernel Z X := condDistrib Xs (fun ω => e (Zc' ω)) μ
  set K_Ye : Kernel Z Y := condDistrib Yo (fun ω => e (Zc' ω)) μ
  -- Step 1: μ.map (e ∘ Z') = (μ.map Z').map e.
  have h_map_eq : μ.map (fun ω => e (Zc' ω)) = (μ.map Zc').map e := by
    rw [Measure.map_map e.measurable hZc']; rfl
  -- Step 2: Pushforward via Prod.map e.symm id.
  let g : Z × (X × Y) → Z' × (X × Y) := Prod.map e.symm id
  have hg_meas : Measurable g := e.symm.measurable.prodMap measurable_id
  have h_LHS_push :
      μ.map (fun ω => (Zc' ω, Xs ω, Yo ω))
        = (μ.map (fun ω => (e (Zc' ω), Xs ω, Yo ω))).map g := by
    have h_eq :
        (μ.map (fun ω => (e (Zc' ω), Xs ω, Yo ω))).map g
          = μ.map (g ∘ fun ω => (e (Zc' ω), Xs ω, Yo ω)) :=
      Measure.map_map hg_meas ((e.measurable.comp hZc').prodMk (hXs.prodMk hYo))
    rw [h_eq]; congr 1; funext ω; simp [g, Prod.map]
  rw [h_LHS_push, hmarkov]
  -- Goal: ((μ.map (e ∘ Z')) ⊗ₘ (K_Xe ×ₖ K_Ye)).map g = (μ.map Z') ⊗ₘ (K_X' ×ₖ K_Y').
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  -- LHS lintegral: convert to (z : Z') via z = e.symm z'.
  rw [lintegral_map hf hg_meas]
  have h_fg_meas : Measurable (fun a : Z × X × Y => f (g a)) := hf.comp hg_meas
  rw [Measure.lintegral_compProd h_fg_meas, h_map_eq]
  have h_inner_lintegral_meas : Measurable
      (fun a : Z => ∫⁻ (b : X × Y), f (g (a, b)) ∂(K_Xe ×ₖ K_Ye) a) :=
    Measurable.lintegral_kernel_prod_right' (κ := K_Xe ×ₖ K_Ye) h_fg_meas
  rw [lintegral_map h_inner_lintegral_meas e.measurable]
  -- RHS lintegral.
  rw [Measure.lintegral_compProd hf]
  -- Pointwise (under z ∂μ.map Zc') equality of inner integrals.
  refine lintegral_congr_ae ?_
  -- Identify K_Xe (e z) and K_Ye (e z) with K_X' z, K_Y' z under μ.map Z'.
  -- Strategy: prove condDistrib Xs (e ∘ Zc') μ =ᵐ[μ.map (e ∘ Zc')] K_X'.comap e.symm
  -- via condDistrib uniqueness, then pull back through `e` using ae_of_ae_map.
  have h_K_Xe_eq :
      condDistrib Xs (fun ω => e (Zc' ω)) μ
        =ᵐ[μ.map (fun ω => e (Zc' ω))]
          K_X'.comap (e.symm : Z → Z') e.symm.measurable :=
    cond_reshape_kernel_lemma μ Xs Zc' hXs hZc' e h_map_eq
  have h_K_Ye_eq :
      condDistrib Yo (fun ω => e (Zc' ω)) μ
        =ᵐ[μ.map (fun ω => e (Zc' ω))]
          K_Y'.comap (e.symm : Z → Z') e.symm.measurable :=
    cond_reshape_kernel_lemma μ Yo Zc' hYo hZc' e h_map_eq
  -- Pull back through e to get ae statements under μ.map Zc'.
  -- Note μ.map (e ∘ Zc') = (μ.map Zc').map e, so ae_of_ae_map applies.
  rw [h_map_eq] at h_K_Xe_eq h_K_Ye_eq
  have h_KX_pulled :
      ∀ᵐ z ∂(μ.map Zc'),
        condDistrib Xs (fun ω => e (Zc' ω)) μ (e z)
          = K_X'.comap (e.symm : Z → Z') e.symm.measurable (e z) :=
    ae_of_ae_map (μ := μ.map Zc') (f := (e : Z' → Z))
      e.measurable.aemeasurable h_K_Xe_eq
  have h_KY_pulled :
      ∀ᵐ z ∂(μ.map Zc'),
        condDistrib Yo (fun ω => e (Zc' ω)) μ (e z)
          = K_Y'.comap (e.symm : Z → Z') e.symm.measurable (e z) :=
    ae_of_ae_map (μ := μ.map Zc') (f := (e : Z' → Z))
      e.measurable.aemeasurable h_K_Ye_eq
  filter_upwards [h_KX_pulled, h_KY_pulled] with z hX hY
  -- hX : K_Xe (e z) = K_X'.comap e.symm (e z) = K_X' (e.symm (e z)) = K_X' z.
  rw [Kernel.comap_apply _ e.symm.measurable] at hX hY
  simp only [MeasurableEquiv.symm_apply_apply] at hX hY
  -- At ae z: ∫⁻ b ∂((K_Xe ×ₖ K_Ye) (e z)), f (g (e z, b)) = ∫⁻ b ∂((K_X' ×ₖ K_Y') z), f (z, b).
  have h_kernel_eq : (K_Xe ×ₖ K_Ye) (e z) = (K_X' ×ₖ K_Y') z := by
    rw [Kernel.prod_apply, Kernel.prod_apply, hX, hY]
  rw [h_kernel_eq]
  congr 1
  funext b
  simp [g]

end GraphoidHelpers

/-! ## Strong-axiom derivations from memoryless

The per-letter Markov chain (`per_letter_markov`) is the simpler of the two
strong-axiom derivations; the harder `outputs_cond_indep` derivation requires the
graphoid weak union axiom. -/

section BridgeMain

variable {n : ℕ}
variable {α : Type*} [MeasurableSpace α] [Nonempty α] [StandardBorelSpace α]
variable {β : Type*} [MeasurableSpace β] [Nonempty β] [StandardBorelSpace β]

/-- **Per-letter Markov chain from memoryless**: derive `Markov μ (Xs full) (Xs i) (Ys i)`
from `IsMemorylessChannel`.

Steps:
1. Drop `Yother` from the left RV `(Xother, Yother)` via `Prod.fst` and `isMarkovChain_map_left`.
2. Bundle `Xs i` to the left via `isMarkovChain_bundle_left_with_conditioner`, yielding
   `Markov μ (Xother, Xs i) (Xs i) (Ys i)`.
3. Reshape `(Xother, Xs i) ≃ᵐ (Fin n → α)` via `measurableEquivExtract.symm`, push left via
   `isMarkovChain_map_left`. -/
theorem per_letter_markov_of_memoryless
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_memo : IsMemorylessChannel μ Xs Ys) (i : Fin n) :
    Shannon.IsMarkovChain μ (fun ω j => Xs j ω) (Xs i) (Ys i) := by
  set XnoI : Ω → ({j : Fin n // j ≠ i} → α) :=
    fun ω j => Xs j.val ω with hXnoI_def
  set YnoI : Ω → ({j : Fin n // j ≠ i} → β) :=
    fun ω j => Ys j.val ω with hYnoI_def
  have hXnoI_meas : Measurable XnoI :=
    measurable_pi_iff.mpr (fun j => hXs j.val)
  have hYnoI_meas : Measurable YnoI :=
    measurable_pi_iff.mpr (fun j => hYs j.val)
  have h0 : Shannon.IsMarkovChain μ (fun ω => (XnoI ω, YnoI ω)) (Xs i) (Ys i) := h_memo i
  have h1 : Shannon.IsMarkovChain μ XnoI (Xs i) (Ys i) := by
    have h_pair_meas : Measurable (fun ω => (XnoI ω, YnoI ω)) :=
      hXnoI_meas.prodMk hYnoI_meas
    have h_proj : Measurable (Prod.fst : ({j : Fin n // j ≠ i} → α) ×
        ({j : Fin n // j ≠ i} → β) → ({j : Fin n // j ≠ i} → α)) := measurable_fst
    exact Shannon.isMarkovChain_map_left μ (fun ω => (XnoI ω, YnoI ω))
      (Xs i) (Ys i) h_pair_meas (hXs i) (hYs i) h_proj h0
  have h2 : Shannon.IsMarkovChain μ
      (fun ω => (XnoI ω, Xs i ω)) (Xs i) (Ys i) :=
    isMarkovChain_bundle_left_with_conditioner μ XnoI (Xs i) (Ys i)
      hXnoI_meas (hXs i) (hYs i) h1
  let e : (Fin n → α) ≃ᵐ α × ({j : Fin n // j ≠ i} → α) :=
    measurableEquivExtract (β := α) i
  let f : ({j : Fin n // j ≠ i} → α) × α → (Fin n → α) :=
    fun p => e.symm (p.2, p.1)
  have hf_meas : Measurable f :=
    e.symm.measurable.comp (measurable_snd.prodMk measurable_fst)
  have h3 : Shannon.IsMarkovChain μ
      (fun ω => f (XnoI ω, Xs i ω)) (Xs i) (Ys i) :=
    Shannon.isMarkovChain_map_left μ (fun ω => (XnoI ω, Xs i ω))
      (Xs i) (Ys i) (hXnoI_meas.prodMk (hXs i)) (hXs i) (hYs i) hf_meas h2
  have h_eq : (fun ω => f (XnoI ω, Xs i ω)) = (fun ω j => Xs j ω) := by
    funext ω j
    show f (XnoI ω, Xs i ω) j = Xs j ω
    by_cases hj : j = i
    · subst hj
      simp [f, e, measurableEquivExtract,
        MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
        MeasurableEquiv.prodCongr]
    · simp [f, e, measurableEquivExtract,
        MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
        MeasurableEquiv.prodCongr, hj, XnoI]
  rw [← h_eq]
  exact h3

/-- **Outputs conditional independence from memoryless**: derive
`Markov μ Y^{≠i} (X^n) Y_i` from `IsMemorylessChannel`.

Steps:
1. Apply `isMarkovChain_weakUnion_left_to_conditioner` to the original γ-form Markov
   `(X^{≠i}, Y^{≠i}) → X_i → Y_i` (with `As := X^{≠i}, Bs := Y^{≠i}, Zc := X_i, Yo := Y_i`),
   yielding `Markov μ Y^{≠i} (X_i, X^{≠i}) Y_i`.
2. Reshape conditioner `(X_i, X^{≠i}) ≃ᵐ X^n` via `measurableEquivExtract.symm`,
   pushed via `isMarkovChain_map_right_conditioner`-style reshape. Since the conditioner
   is bijectively related, we use `isMarkovChain_map_right_via_swap`. -/
theorem outputs_cond_indep_of_memoryless
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_memo : IsMemorylessChannel μ Xs Ys) (i : Fin n) :
    Shannon.IsMarkovChain μ
      (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
      (fun ω j => Xs j ω)
      (Ys i) := by
  set XnoI : Ω → ({j : Fin n // j ≠ i} → α) :=
    fun ω j => Xs j.val ω with hXnoI_def
  set YnoI : Ω → ({j : Fin n // j ≠ i} → β) :=
    fun ω j => Ys j.val ω with hYnoI_def
  have hXnoI_meas : Measurable XnoI :=
    measurable_pi_iff.mpr (fun j => hXs j.val)
  have hYnoI_meas : Measurable YnoI :=
    measurable_pi_iff.mpr (fun j => hYs j.val)
  -- Step 1: Apply graphoid weak union to h_memo i:
  -- From Markov μ (XnoI, YnoI) (Xs i) (Ys i),
  -- derive Markov μ YnoI (Xs i, XnoI) (Ys i).
  have h0 : Shannon.IsMarkovChain μ (fun ω => (XnoI ω, YnoI ω)) (Xs i) (Ys i) := h_memo i
  have h_weak : Shannon.IsMarkovChain μ YnoI (fun ω => (Xs i ω, XnoI ω)) (Ys i) :=
    isMarkovChain_weakUnion_left_to_conditioner μ XnoI YnoI (Xs i) (Ys i)
      hXnoI_meas hYnoI_meas (hXs i) (hYs i) h0
  -- Step 2: Reshape conditioner (Xs i, XnoI) ≃ᵐ X^n via measurableEquivExtract.
  -- e : (Fin n → α) ≃ᵐ α × ({j // j ≠ i} → α).
  let e : (Fin n → α) ≃ᵐ α × ({j : Fin n // j ≠ i} → α) :=
    measurableEquivExtract (β := α) i
  -- Apply conditioner reshape:
  -- We have Markov μ YnoI (fun ω => (Xs i ω, XnoI ω)) (Ys i),
  -- i.e. Markov μ YnoI (e ∘ (fun ω j => Xs j ω)) (Ys i),
  -- provided (Xs i ω, XnoI ω) = e (fun j => Xs j ω).
  -- Then apply isMarkovChain_map_conditioner_measurableEquiv to get
  -- Markov μ YnoI (fun ω j => Xs j ω) (Ys i).
  have h_pointwise : ∀ ω, (Xs i ω, XnoI ω) = e (fun j => Xs j ω) := by
    intro ω
    -- e (Xs full) = (Xs i, X^{≠i})
    -- The collapse {j // j = i} → α ≃ α uses default = ⟨i, rfl⟩; need to rewrite `Xs (↑default)` = `Xs i`.
    have h_default : (default : {j : Fin n // j = i}).val = i :=
      rfl
    simp [e, measurableEquivExtract,
      MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
      MeasurableEquiv.prodCongr, XnoI, h_default]
  have h_weak' : Shannon.IsMarkovChain μ YnoI (fun ω => e (fun j => Xs j ω)) (Ys i) := by
    have h_eq : (fun ω => (Xs i ω, XnoI ω)) = (fun ω => e (fun j => Xs j ω)) := by
      funext ω; exact h_pointwise ω
    rw [← h_eq]; exact h_weak
  have h_full_meas : Measurable (fun ω j => Xs j ω) :=
    measurable_pi_iff.mpr hXs
  exact isMarkovChain_map_conditioner_measurableEquiv μ YnoI (fun ω j => Xs j ω) (Ys i)
    hYnoI_meas h_full_meas (hYs i) e h_weak'

end BridgeMain

/-! ## Semi-pure main converse theorem -/

section MainConversePure

variable {n : ℕ}
variable {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
  [MeasurableSpace M] [MeasurableSingletonClass M] [StandardBorelSpace M]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]

omit [DecidableEq M] [DecidableEq α] [DecidableEq β] in
/-- **Channel coding converse, pure memoryless DMC form**.

Under `h_memo : IsMemorylessChannel μ Xs Ys`, auto-derives the per-letter Markov chain
`X^n → X_i → Y_i` and outputs conditional independence `Y^{≠i} → X^n → Y_i`, then
delegates to `channel_coding_converse_general_memoryless_strong`. -/
@[entry_point]
theorem channel_coding_converse_general_memoryless_pure
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → Fin n → α)
    (Ys : Fin n → Ω → β) (decoder : (Fin n → β) → M)
    (hMsg : Measurable Msg) (hYs : ∀ i, Measurable (Ys i))
    (hdecoder : Measurable decoder)
    (hmarkov : Shannon.IsMarkovChain μ Msg
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω))
    (h_memo : IsMemorylessChannel μ (fun i ω => encoder (Msg ω) i) Ys)
    (hMsg_uniform :
      μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M)
    (hMI_finite : Shannon.mutualInfo μ
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω) ≠ ∞) :
    Real.log (Fintype.card M) ≤
      (∑ i : Fin n,
        (Shannon.mutualInfo μ
          (fun ω => encoder (Msg ω) i) (Ys i)).toReal) +
        Real.binEntropy
          (InformationTheory.MeasureFano.errorProb μ Msg
            (fun ω i => Ys i ω) decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg
          (fun ω i => Ys i ω) decoder *
          Real.log ((Fintype.card M : ℝ) - 1) := by
  classical
  set Xs : Fin n → Ω → α := fun i ω => encoder (Msg ω) i with hXs_def
  have h_encoder : Measurable encoder := measurable_of_countable _
  have hXs_meas : ∀ i, Measurable (Xs i) := fun i =>
    (measurable_pi_apply i).comp (h_encoder.comp hMsg)
  -- Build IsMemorylessChannelStrong from h_memo (auto per-letter + outputs_cond_indep).
  have h_strong : IsMemorylessChannelStrong μ Xs Ys :=
    { per_letter_markov :=
        per_letter_markov_of_memoryless μ Xs Ys hXs_meas hYs h_memo
      outputs_cond_indep :=
        outputs_cond_indep_of_memoryless μ Xs Ys hXs_meas hYs h_memo }
  exact channel_coding_converse_general_memoryless_strong
    μ Msg encoder Ys decoder hMsg hYs hdecoder hmarkov h_memo h_strong
    hMsg_uniform hcard hMI_finite

end MainConversePure

end InformationTheory.Shannon.ChannelCodingConverseGeneral

