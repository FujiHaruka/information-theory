import InformationTheory.Shannon.ChannelCoding.ConverseMemorylessChainRule
import Mathlib.MeasureTheory.Integral.Marginal

/-!
# From a block code to its ambient law

Model-independent infrastructure for the operational converses: a block code together with a
message law and a per-letter product channel determines an ambient probability measure on
`message × output block`, and the structural hypotheses of the single-letter converses (Markov
factorization, memorylessness, per-letter joint laws) are read off that measure.  None of the
statements below mention a particular channel model — the encoder enters only through the
factorization hypotheses `κ m = Wcode (g m)` and `κ m = ∏ⱼ W (x m j)` — so a multi-user converse
instantiates them by supplying its own encoder and channel.

## Main statements

* `isMarkovChain_of_compProd_encoder`: an ambient `ν ⊗ₘ κ` whose kernel factors through a
  deterministic encoder `g` carries the Markov chain `M → g M → Y`.
* `isMarkovChain_of_compProd_pi`: for a per-letter product kernel `∏ⱼ W (x m j)`, the output
  letter `Yᵢ` is conditionally independent of *any* variable that does not read the `i`-th output
  coordinate, given the input letter `Xᵢ`.  The conditioner is the input letter itself; the
  variable decoupled from `Yᵢ` is an arbitrary measurable function of the whole ambient point,
  constrained only by invariance under re-randomizing coordinate `i`, so it may read the message
  as well as the other letters.
* `isMemorylessChannel_of_compProd_pi`: if the kernel is the per-letter product `∏ⱼ W (x m j)`
  of a channel applied to a deterministic codeword, the ambient is a memoryless channel.
* `compProd_pi_map_pair_eq_of_update_invariant`: the joint law of the `i`-th output letter paired
  with any map that is invariant under updating the `i`-th output coordinate and that retracts
  onto the input letter, which is what lets a padded auxiliary variable sit there.
* `compProd_pi_map_pair_eq`: its special case where that map is the input letter `x · i` itself,
  so the joint law of the `i`-th input-output pair is the channel joint
  `(ν.map fun m ↦ x m i) ⊗ₘ W`.
* `compProd_comap_map_prodMap`: a composition product with a comapped kernel is the composition
  product of the pushed-forward measure with the kernel itself.
* `compProd_map_prodMap`: the two-sided form of the previous item — a composition product
  transported by a pair of maps, one on the base and one on the fiber, provided the kernel's
  dependence on the base factors through the base map.
* `pi_map_comp_of_injective`: a finite product measure reindexed along an injection is the
  product measure of the reindexed family.
* `piBlockKernel`, `pi_map_unzip_eq_compProd`: a product of laws each of which is its own first
  marginal followed by a kernel `Q`, read as a pair of blocks, is the composition product of the
  product of the first marginals with the blockwise product of `Q`.
* `mutualInfo_map_comp`, `condDistrib_map_comp`, `condMutualInfo_map_comp`: information
  quantities and conditional distributions are invariant under a shared pushforward of all their
  arguments.
* `le_log_of_ceil_exp_le`: `⌈exp x⌉₊ ≤ M` implies `x ≤ log M`, turning a message count into a
  rate bound.
* `le_toReal_of_inv_mul_le`: an averaged bound `m⁻¹ · S ≤ J` in `ℝ≥0∞` together with
  `m · r ≤ S.toReal` gives `r ≤ J.toReal`, which is how a per-letter bound becomes a rate bound.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open InformationTheory.Shannon.ChannelCodingConverseGeneral
open scoped ENNReal

/-! ### The uniform message law -/

/-- The uniform probability law `(card X)⁻¹ • count` on a nonempty finite type. -/
instance uniformCount_isProbabilityMeasure {X : Type*}
    [Fintype X] [Nonempty X] [MeasurableSpace X] [MeasurableSingletonClass X] :
    IsProbabilityMeasure ((Fintype.card X : ℝ≥0∞)⁻¹ • Measure.count : Measure X) := by
  constructor
  have hcard : (Measure.count (Set.univ : Set X)) = (Fintype.card X : ℝ≥0∞) := by
    rw [Measure.count_apply_finite Set.univ Set.finite_univ]
    simp
  rw [Measure.smul_apply, smul_eq_mul, hcard,
    ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)]

/-! ### Markov factorization of the ambient -/

/-- Abstract Markov-chain factorization `M → g M → Y` for an ambient `ν ⊗ₘ κ` in which the
message-to-output kernel `κ` factors through a deterministic encoder `g : M → Z` and a
codeword kernel `Wcode : Z → Y` (i.e. `κ m = Wcode (g m)`).  This is the general shape behind
the message-to-codeword-to-output chain of a multi-user converse; it needs no product/pi
structure, only the factorization `hκ`.
@audit:ok -/
lemma isMarkovChain_of_compProd_encoder
    {M Z Y : Type*}
    [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
    [MeasurableSpace Z]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (ν : Measure M) [IsProbabilityMeasure ν]
    (g : M → Z) (hg : Measurable g)
    (κ : Kernel M Y) [IsMarkovKernel κ]
    (Wcode : Kernel Z Y) [IsMarkovKernel Wcode]
    (hκ : ∀ m : M, κ m = Wcode (g m)) :
    IsMarkovChain (ν ⊗ₘ κ)
      (Prod.fst : M × Y → M)
      (fun ω : M × Y ↦ g ω.1)
      (Prod.snd : M × Y → Y) := by
  set μ : Measure (M × Y) := ν ⊗ₘ κ with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  set Xs : M × Y → M := Prod.fst with hXs_def
  set Zc : M × Y → Z := fun ω ↦ g ω.1 with hZc_def
  set Yo : M × Y → Y := Prod.snd with hYo_def
  have hXs_meas : Measurable Xs := measurable_fst
  have hZc_meas : Measurable Zc := hg.comp measurable_fst
  have hYo_meas : Measurable Yo := measurable_snd
  -- Message marginal `μ.map Xs = ν`, hence codeword law `μ.map Zc = ν.map g`.
  have h_map_Xs : μ.map Xs = ν := by rw [hμ_def, hXs_def]; exact Measure.fst_compProd _ _
  have h_map_Zc : μ.map Zc = ν.map g := by
    have hcomp : Zc = g ∘ Xs := rfl
    rw [hcomp, ← Measure.map_map hg hXs_meas, h_map_Xs]
  -- Linchpin: `μ.map (Zc, Yo) = (μ.map Zc) ⊗ₘ Wcode`.
  have h_pair_eq : μ.map (fun ω ↦ (Zc ω, Yo ω)) = (μ.map Zc) ⊗ₘ Wcode := by
    rw [h_map_Zc]
    refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
    have hFmeas : Measurable (fun ω : M × Y ↦ f (Zc ω, Yo ω)) :=
      hf.comp (hZc_meas.prodMk hYo_meas)
    have hF_meas : Measurable (fun z : Z ↦ ∫⁻ y : Y, f (z, y) ∂(Wcode z)) :=
      Measurable.lintegral_kernel_prod_right' (κ := Wcode) hf
    rw [lintegral_map hf (hZc_meas.prodMk hYo_meas), hμ_def,
      Measure.lintegral_compProd hFmeas, Measure.lintegral_compProd hf,
      lintegral_map hF_meas hg]
    refine lintegral_congr fun m ↦ ?_
    rw [hκ]
  -- Identify `condDistrib Yo Zc μ =ᵐ Wcode`.
  haveI : IsProbabilityMeasure (μ.map Zc) :=
    Measure.isProbabilityMeasure_map hZc_meas.aemeasurable
  have hK_Y_eq : condDistrib Yo Zc μ =ᵐ[μ.map Zc] Wcode :=
    condDistrib_ae_eq_of_measure_eq_compProd Zc hYo_meas.aemeasurable h_pair_eq
  unfold IsMarkovChain
  set K_X : Kernel Z M := condDistrib Xs Zc μ with hK_X_def
  have h_compProd_eq :
      (μ.map Zc) ⊗ₘ (K_X ×ₖ condDistrib Yo Zc μ) = (μ.map Zc) ⊗ₘ (K_X ×ₖ Wcode) := by
    refine Measure.compProd_congr ?_
    filter_upwards [hK_Y_eq] with a ha
    ext s hs
    rw [Kernel.prod_apply, Kernel.prod_apply, ha]
  rw [h_compProd_eq]
  -- Triple-joint factorization via `ext_of_lintegral`.
  have h_LHS_meas : Measurable (fun ω ↦ (Zc ω, Xs ω, Yo ω)) :=
    hZc_meas.prodMk (hXs_meas.prodMk hYo_meas)
  have hKX_fold : (μ.map Zc) ⊗ₘ K_X = μ.map (fun ω ↦ (Zc ω, Xs ω)) :=
    compProd_map_condDistrib (μ := μ) (X := Zc) (Y := Xs) hXs_meas.aemeasurable
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [lintegral_map hf h_LHS_meas, Measure.lintegral_compProd hf]
  have h_inner_split : ∀ z : Z,
      ∫⁻ p : M × Y, f (z, p.1, p.2) ∂((K_X ×ₖ Wcode) z)
        = ∫⁻ x : M, ∫⁻ y : Y, f (z, x, y) ∂(Wcode z) ∂(K_X z) := by
    intro z
    rw [Kernel.prod_apply,
      lintegral_prod (fun p : M × Y ↦ f (z, p.1, p.2))
        (hf.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))).aemeasurable]
  simp_rw [h_inner_split]
  set G : Z × M → ℝ≥0∞ := fun p ↦ ∫⁻ y : Y, f (p.1, p.2, y) ∂(Wcode p.1) with hG_def
  have hG_meas : Measurable G := by
    let K' : Kernel (Z × M) Y := Wcode.comap (Prod.fst : Z × M → Z) measurable_fst
    have h_eq_K' : G = fun p : Z × M ↦ ∫⁻ y : Y, f (p.1, p.2, y) ∂(K' p) := by
      funext p; simp [G, K', Kernel.comap_apply]
    rw [h_eq_K']
    exact Measurable.lintegral_kernel_prod_right' (κ := K')
      (f := fun pp : (Z × M) × Y ↦ f (pp.1.1, pp.1.2, pp.2))
      (hf.comp (((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))
  have h_RHS_is_G : ∀ z : Z, ∀ x : M,
      ∫⁻ y : Y, f (z, x, y) ∂(Wcode z) = G (z, x) := fun _ _ ↦ rfl
  simp_rw [h_RHS_is_G]
  have hFmeas2 : Measurable (fun ω : M × Y ↦ f (Zc ω, Xs ω, Yo ω)) := hf.comp h_LHS_meas
  have hGmeas2 : Measurable (fun ω : M × Y ↦ G (Zc ω, Xs ω)) :=
    hG_meas.comp (hZc_meas.prodMk hXs_meas)
  rw [← Measure.lintegral_compProd hG_meas, hKX_fold,
    lintegral_map hG_meas (hZc_meas.prodMk hXs_meas), hμ_def,
    Measure.lintegral_compProd hFmeas2, Measure.lintegral_compProd hGmeas2]
  refine lintegral_congr fun m ↦ ?_
  rw [hκ]
  have hRHSconst : (fun y : Y ↦ G (Zc (m, y), Xs (m, y)))
      = (fun _ : Y ↦ ∫⁻ y' : Y, f (g m, m, y') ∂(Wcode (g m))) := by
    funext y; show G (g m, m) = _; rw [hG_def]
  rw [hRHSconst, lintegral_const, measure_univ, mul_one]

/-! ### Marginalizing and reindexing a product measure -/

/-- Re-randomizing a single coordinate of a product of probability measures leaves the
`Measure.pi`-integral unchanged.  Used to peel the `i`-th output letter off the block channel
`∏ⱼ W (xⱼ)` in the memoryless-channel derivation.
@audit:ok -/
lemma lintegral_pi_reRandomize {γ : Type*} [MeasurableSpace γ]
    {k : ℕ} (ζ : Fin k → Measure γ) [∀ j, IsProbabilityMeasure (ζ j)]
    (i : Fin k) (F : (Fin k → γ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y, F y ∂(Measure.pi ζ)
      = ∫⁻ y, (∫⁻ b, F (Function.update y i b) ∂(ζ i)) ∂(Measure.pi ζ) := by
  classical
  haveI : ∀ j, SigmaFinite (ζ j) := fun j ↦ inferInstance
  have hGmeas : Measurable (fun y ↦ ∫⁻ b, F (Function.update y i b) ∂(ζ i)) := by
    rw [show (fun y ↦ ∫⁻ b, F (Function.update y i b) ∂(ζ i))
          = MeasureTheory.lmarginal ζ ({i} : Finset (Fin k)) F from
        (MeasureTheory.lmarginal_singleton F i).symm]
    exact hF.lmarginal (μ := ζ)
  refine MeasureTheory.lintegral_eq_of_lmarginal_eq ({i} : Finset (Fin k)) hF hGmeas ?_
  rw [← MeasureTheory.lmarginal_singleton F i,
    MeasureTheory.lmarginal_singleton (MeasureTheory.lmarginal ζ ({i} : Finset (Fin k)) F) i]
  funext x
  simp_rw [MeasureTheory.lmarginal_update_of_mem ζ (Finset.mem_singleton_self i) F]
  rw [lintegral_const, measure_univ, mul_one]

/-- Marginalization of a product of probability measures at a single coordinate.
@audit:ok -/
lemma lintegral_pi_eval {γ : Type*} [MeasurableSpace γ]
    {k : ℕ} (ζ : Fin k → Measure γ) [∀ j, IsProbabilityMeasure (ζ j)]
    (i : Fin k) (g : γ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g (y i) ∂(Measure.pi ζ) = ∫⁻ b, g b ∂(ζ i) := by
  rw [lintegral_pi_reRandomize ζ i (fun y ↦ g (y i)) (hg.comp (measurable_pi_apply i))]
  simp only [Function.update_self]
  rw [lintegral_const, measure_univ, mul_one]

lemma pi_map_comp_of_injective {γ : Type*} [MeasurableSpace γ] {k m : ℕ}
    (ν : Fin m → Measure γ) [∀ j, IsProbabilityMeasure (ν j)]
    (e : Fin k → Fin m) (he : Function.Injective e) :
    (Measure.pi ν).map (fun y j ↦ y (e j)) = Measure.pi fun j ↦ ν (e j) := by
  classical
  have hmap : Measurable (fun (y : Fin m → γ) (j : Fin k) ↦ y (e j)) :=
    measurable_pi_lambda _ fun j ↦ measurable_pi_apply (e j)
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  set t : Fin m → Set γ := Function.extend e s fun _ ↦ Set.univ with ht_def
  have ht_mem : ∀ j : Fin k, t (e j) = s j := fun j ↦ he.extend_apply s _ j
  have ht_not : ∀ i : Fin m, (¬ ∃ j, e j = i) → t i = Set.univ :=
    fun i hi ↦ Function.extend_apply' s _ i hi
  have hpre : (fun (y : Fin m → γ) (j : Fin k) ↦ y (e j)) ⁻¹' (Set.univ.pi s)
      = Set.univ.pi t := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro h i
      by_cases hi : ∃ j, e j = i
      · obtain ⟨j, rfl⟩ := hi
        rw [ht_mem j]
        exact h j
      · rw [ht_not i hi]
        trivial
    · intro h j
      rw [← ht_mem j]
      exact h (e j)
  have ht_meas : ∀ i, MeasurableSet (t i) := by
    intro i
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [ht_mem j]
      exact hs j
    · rw [ht_not i hi]
      exact MeasurableSet.univ
  rw [Measure.map_apply hmap (MeasurableSet.univ_pi hs), hpre, Measure.pi_pi]
  have hprod : ∏ i ∈ Finset.univ.image e, ν i (t i) = ∏ i : Fin m, ν i (t i) := by
    refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi ↦ ?_
    have hi' : ¬ ∃ j, e j = i := fun ⟨j, hj⟩ ↦
      hi (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩)
    rw [ht_not i hi', measure_univ]
  rw [← hprod, Finset.prod_image fun x _ y _ h ↦ he h]
  exact Finset.prod_congr rfl fun j _ ↦ by rw [ht_mem j]

/-! ### Per-letter conditional independence, memorylessness and the joint law -/

/-- Per-letter conditional independence for a product-channel ambient: if the message-to-output
kernel factors as the per-letter product `κ m = ∏ⱼ W (x m j)`, then at every letter `i` the
output `ω.2 i` is conditionally independent of `F` given the input letter `x ω.1 i`, for any
measurable `F` that does not read output coordinate `i`.  Not reading that coordinate is what
`hFupd` says — re-randomizing it leaves `F` unchanged — so `F` may read the message, hence every
input letter, together with all the other output letters.
@audit:ok -/
lemma isMarkovChain_of_compProd_pi
    {M A B C : Type*}
    [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    [MeasurableSpace C] [StandardBorelSpace C] [Nonempty C]
    {k : ℕ}
    (ν : Measure M) [IsProbabilityMeasure ν]
    (x : M → Fin k → A) (hx : Measurable x)
    (W : Kernel A B) [IsMarkovKernel W]
    (κ : Kernel M (Fin k → B)) [IsMarkovKernel κ]
    (hκ : ∀ m, κ m = Measure.pi (fun j ↦ W (x m j)))
    (i : Fin k) (F : M × (Fin k → B) → C) (hF : Measurable F)
    (hFupd : ∀ (m : M) (y : Fin k → B) (b : B), F (m, Function.update y i b) = F (m, y)) :
    IsMarkovChain (ν ⊗ₘ κ) F (fun ω ↦ x ω.1 i) (fun ω ↦ ω.2 i) := by
  set μ : Measure (M × (Fin k → B)) := ν ⊗ₘ κ with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  set Zc : M × (Fin k → B) → A := fun ω ↦ x ω.1 i with hZc_def
  set Yo : M × (Fin k → B) → B := fun ω ↦ ω.2 i with hYo_def
  have hxi_meas : Measurable (fun m ↦ x m i) := (measurable_pi_apply i).comp hx
  have hZc_meas : Measurable Zc := hxi_meas.comp measurable_fst
  have hYo_meas : Measurable Yo := (measurable_pi_apply i).comp measurable_snd
  -- Codeword law `μ.map Zc = ν.map (· i ∘ x)`.
  have h_map_Zc : μ.map Zc = ν.map (fun m ↦ x m i) := by
    have hcomp : Zc = (fun m ↦ x m i) ∘ Prod.fst := rfl
    rw [hcomp, ← Measure.map_map hxi_meas measurable_fst]
    congr 1
    rw [hμ_def]; exact Measure.fst_compProd _ _
  -- Step 1: `μ.map (Zc, Yo) = (μ.map Zc) ⊗ₘ W`.
  have h_pair_eq : μ.map (fun ω ↦ (Zc ω, Yo ω)) = (μ.map Zc) ⊗ₘ W := by
    rw [h_map_Zc]
    refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
    have hFmeas : Measurable (fun ω : M × (Fin k → B) ↦ f (Zc ω, Yo ω)) :=
      hf.comp (hZc_meas.prodMk hYo_meas)
    have hFm2 : Measurable (fun z : A ↦ ∫⁻ b : B, f (z, b) ∂(W z)) :=
      Measurable.lintegral_kernel_prod_right' (κ := W) hf
    rw [lintegral_map hf (hZc_meas.prodMk hYo_meas), hμ_def,
      Measure.lintegral_compProd hFmeas, Measure.lintegral_compProd hf,
      lintegral_map hFm2 hxi_meas]
    refine lintegral_congr fun m ↦ ?_
    rw [hκ]
    exact lintegral_pi_eval (fun j ↦ W (x m j)) i (fun b ↦ f (x m i, b))
      (hf.comp (measurable_const.prodMk measurable_id))
  -- Step 2: identify `condDistrib Yo Zc μ =ᵐ W` and substitute.
  haveI : IsProbabilityMeasure (μ.map Zc) :=
    Measure.isProbabilityMeasure_map hZc_meas.aemeasurable
  have hK_Y_eq : condDistrib Yo Zc μ =ᵐ[μ.map Zc] W :=
    condDistrib_ae_eq_of_measure_eq_compProd Zc hYo_meas.aemeasurable h_pair_eq
  unfold IsMarkovChain
  set K_F := condDistrib F Zc μ with hK_F_def
  have h_compProd_eq :
      (μ.map Zc) ⊗ₘ (K_F ×ₖ condDistrib Yo Zc μ) = (μ.map Zc) ⊗ₘ (K_F ×ₖ W) := by
    refine Measure.compProd_congr ?_
    filter_upwards [hK_Y_eq] with a ha
    ext s hs
    rw [Kernel.prod_apply, Kernel.prod_apply, ha]
  rw [h_compProd_eq]
  -- Step 3: triple-joint factorization via `ext_of_lintegral` + the re-randomize identity.
  have h_LHS_meas : Measurable (fun ω ↦ (Zc ω, F ω, Yo ω)) :=
    hZc_meas.prodMk (hF.prodMk hYo_meas)
  have hKX_fold : (μ.map Zc) ⊗ₘ K_F = μ.map (fun ω ↦ (Zc ω, F ω)) :=
    compProd_map_condDistrib (μ := μ) (X := Zc) (Y := F) hF.aemeasurable
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [lintegral_map hf h_LHS_meas, Measure.lintegral_compProd hf]
  have h_inner_split : ∀ z : A,
      ∫⁻ p : C × B, f (z, p.1, p.2) ∂((K_F ×ₖ W) z)
        = ∫⁻ w, ∫⁻ b, f (z, w, b) ∂(W z) ∂(K_F z) := by
    intro z
    rw [Kernel.prod_apply,
      lintegral_prod (fun p : C × B ↦ f (z, p.1, p.2))
        (hf.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))).aemeasurable]
  simp_rw [h_inner_split]
  set G : A × C → ℝ≥0∞ := fun p ↦ ∫⁻ b, f (p.1, p.2, b) ∂(W p.1) with hG_def
  have hG_meas : Measurable G := by
    let K' : Kernel (A × C) B := W.comap Prod.fst measurable_fst
    have h_eq_K' : G = fun p ↦ ∫⁻ b, f (p.1, p.2, b) ∂(K' p) := by
      funext p; simp [G, K', Kernel.comap_apply]
    rw [h_eq_K']
    exact Measurable.lintegral_kernel_prod_right' (κ := K')
      (f := fun pp ↦ f (pp.1.1, pp.1.2, pp.2))
      (hf.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  have h_RHS_is_G : ∀ z w, ∫⁻ b, f (z, w, b) ∂(W z) = G (z, w) := fun _ _ ↦ rfl
  simp_rw [h_RHS_is_G]
  have hFmeas2 : Measurable (fun ω ↦ f (Zc ω, F ω, Yo ω)) := hf.comp h_LHS_meas
  have hGmeas2 : Measurable (fun ω ↦ G (Zc ω, F ω)) := hG_meas.comp (hZc_meas.prodMk hF)
  rw [← Measure.lintegral_compProd hG_meas, hKX_fold,
    lintegral_map hG_meas (hZc_meas.prodMk hF), hμ_def,
    Measure.lintegral_compProd hFmeas2, Measure.lintegral_compProd hGmeas2]
  refine lintegral_congr fun m ↦ ?_
  rw [hκ]
  have hpair_m : Measurable (fun y : Fin k → B ↦ ((m, y) : M × (Fin k → B))) :=
    measurable_const.prodMk measurable_id
  have hFm3 : Measurable (fun y ↦ f (Zc (m, y), F (m, y), Yo (m, y))) :=
    hf.comp ((hZc_meas.comp hpair_m).prodMk
      ((hF.comp hpair_m).prodMk (hYo_meas.comp hpair_m)))
  rw [lintegral_pi_reRandomize (fun j ↦ W (x m j)) i
    (fun y ↦ f (Zc (m, y), F (m, y), Yo (m, y))) hFm3]
  refine lintegral_congr fun y ↦ ?_
  rw [hG_def]
  show ∫⁻ b, f (Zc (m, Function.update y i b), F (m, Function.update y i b),
      Yo (m, Function.update y i b)) ∂(W (x m i))
    = ∫⁻ b, f (Zc (m, y), F (m, y), b) ∂(W (x m i))
  refine lintegral_congr fun b ↦ ?_
  exact congrArg f (Prod.ext rfl (Prod.ext (hFupd m y b) (Function.update_self i b y)))

/-- A product-channel ambient is a memoryless channel: if the message-to-output kernel
factors as the per-letter product `κ m = ∏ⱼ W (x m j)` of a channel `W` applied to a
deterministic codeword `x m`, then `ν ⊗ₘ κ` is a memoryless channel with per-letter
inputs `x ω.1 i` and per-letter outputs `ω.2 i`.  This is `isMarkovChain_of_compProd_pi` read
at the conditioner that collects every input and output letter other than the `i`-th.
@audit:ok -/
lemma isMemorylessChannel_of_compProd_pi
    {M A B : Type*}
    [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {k : ℕ}
    (ν : Measure M) [IsProbabilityMeasure ν]
    (x : M → Fin k → A) (hx : Measurable x)
    (W : Kernel A B) [IsMarkovKernel W]
    (κ : Kernel M (Fin k → B)) [IsMarkovKernel κ]
    (hκ : ∀ m, κ m = Measure.pi (fun j ↦ W (x m j))) :
    IsMemorylessChannel (ν ⊗ₘ κ) (fun i ω ↦ x ω.1 i) (fun i ω ↦ ω.2 i) := by
  classical
  intro i
  refine isMarkovChain_of_compProd_pi ν x hx W κ hκ i
    (fun ω ↦ ((fun j : {j : Fin k // j ≠ i} ↦ x ω.1 j.val),
      (fun j : {j : Fin k // j ≠ i} ↦ ω.2 j.val)))
    (Measurable.prodMk
      (measurable_pi_iff.mpr fun j ↦ (measurable_pi_apply j.val).comp (hx.comp measurable_fst))
      (measurable_pi_iff.mpr fun j ↦ (measurable_pi_apply j.val).comp measurable_snd))
    fun m y b ↦ ?_
  exact Prod.ext rfl (funext fun j ↦ Function.update_of_ne j.2 b y)

/-- @audit:ok -/
lemma compProd_comap_map_prodMap {A A' B : Type*} [MeasurableSpace A] [MeasurableSpace A']
    [MeasurableSpace B] (μ : Measure A) [SFinite μ] (κ : Kernel A' B) [IsMarkovKernel κ]
    {g : A → A'} (hg : Measurable g) :
    (μ ⊗ₘ κ.comap g hg).map (fun z ↦ (g z.1, z.2)) = (μ.map g) ⊗ₘ κ := by
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have hmap : Measurable (fun z : A × B ↦ (g z.1, z.2)) :=
    (hg.comp measurable_fst).prodMk measurable_snd
  have hin : Measurable (fun a : A' ↦ ∫⁻ b, f (a, b) ∂(κ a)) :=
    Measurable.lintegral_kernel_prod_right' (κ := κ) hf
  have hcomp : Measurable (fun z : A × B ↦ f (g z.1, z.2)) := hf.comp hmap
  rw [lintegral_map hf hmap, Measure.lintegral_compProd hcomp,
    Measure.lintegral_compProd hf, lintegral_map hin hg]
  rfl

lemma compProd_map_prodMap {Z Z' B B' : Type*} [MeasurableSpace Z] [MeasurableSpace Z']
    [MeasurableSpace B] [MeasurableSpace B']
    (ρ : Measure Z) [SFinite ρ] (κ : Kernel Z B) [IsMarkovKernel κ]
    {f : Z → Z'} (hf : Measurable f) {g : B → B'} (hg : Measurable g)
    (κ' : Kernel Z' B') [IsMarkovKernel κ']
    (hκ : κ.map g = κ'.comap f hf) :
    (ρ ⊗ₘ κ).map (Prod.map f g) = (ρ.map f) ⊗ₘ κ' := by
  have h1 : (Prod.map f g : Z × B → Z' × B')
      = (fun z : Z × B' ↦ (f z.1, z.2)) ∘ (Prod.map id g) := rfl
  rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.compProd_map hg, hκ,
    compProd_comap_map_prodMap ρ κ' hf]

/-- @audit:ok -/
lemma compProd_pi_map_pair_eq_of_update_invariant
    {M A B C : Type*} [MeasurableSpace M] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] {k : ℕ}
    (ν : Measure M) [IsProbabilityMeasure ν]
    (x : M → Fin k → A)
    (W : Kernel A B) [IsMarkovKernel W]
    (κ : Kernel M (Fin k → B)) [IsMarkovKernel κ]
    (hκ : ∀ m, κ m = Measure.pi (fun j ↦ W (x m j))) (i : Fin k)
    (G : M × (Fin k → B) → C) (hG : Measurable G)
    (hGupd : ∀ (m : M) (y : Fin k → B) (b : B), G (m, Function.update y i b) = G (m, y))
    (g : C → A) (hg : Measurable g) (hgG : ∀ ω, g (G ω) = x ω.1 i) :
    (ν ⊗ₘ κ).map (fun ω ↦ (G ω, ω.2 i)) = ((ν ⊗ₘ κ).map G) ⊗ₘ (W.comap g hg) := by
  have hYo : Measurable (fun ω : M × (Fin k → B) ↦ ω.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have hpair : Measurable (fun ω : M × (Fin k → B) ↦ (G ω, ω.2 i)) := hG.prodMk hYo
  have hlhs : Measurable (fun ω : M × (Fin k → B) ↦ f (G ω, ω.2 i)) := hf.comp hpair
  have hin : Measurable (fun c : C ↦ ∫⁻ b, f (c, b) ∂((W.comap g hg) c)) :=
    Measurable.lintegral_kernel_prod_right' (κ := W.comap g hg) hf
  have hrhs : Measurable
      (fun ω : M × (Fin k → B) ↦ ∫⁻ b, f (G ω, b) ∂((W.comap g hg) (G ω))) := hin.comp hG
  rw [lintegral_map hf hpair, Measure.lintegral_compProd hf, lintegral_map hin hG,
    Measure.lintegral_compProd hlhs, Measure.lintegral_compProd hrhs]
  refine lintegral_congr fun m ↦ ?_
  rw [hκ]
  have hFm : Measurable (fun y : Fin k → B ↦ f (G (m, y), y i)) :=
    hf.comp ((hG.comp (measurable_const.prodMk measurable_id)).prodMk (measurable_pi_apply i))
  rw [lintegral_pi_reRandomize (fun j ↦ W (x m j)) i (fun y ↦ f (G (m, y), y i)) hFm]
  refine lintegral_congr fun y ↦ ?_
  have hker : (W.comap g hg) (G (m, y)) = W (x m i) := by
    rw [Kernel.comap_apply, hgG (m, y)]
  rw [hker]
  exact lintegral_congr fun b ↦ by rw [hGupd m y b, Function.update_self i b y]

/-- Per-letter joint pushforward of a product-channel `compProd`: for an ambient `ν ⊗ₘ κ`
whose message-to-output kernel factors as the per-letter product `κ m = ∏ⱼ W (x m j)`, the
joint law of the `i`-th input-output pair `(x ω.1 i, ω.2 i)` is the channel joint
`(ν.map fun m ↦ x m i) ⊗ₘ W`.  Stated separately from `isMarkovChain_of_compProd_pi`, which
establishes the same identity internally, because it is what identifies a per-letter
information quantity of the ambient with the corresponding channel quantity. -/
lemma compProd_pi_map_pair_eq
    {M A B : Type*} [MeasurableSpace M] [MeasurableSpace A] [MeasurableSpace B]
    {k : ℕ} (ν : Measure M) [IsProbabilityMeasure ν]
    (x : M → Fin k → A) (hx : Measurable x)
    (W : Kernel A B) [IsMarkovKernel W]
    (κ : Kernel M (Fin k → B)) [IsMarkovKernel κ]
    (hκ : ∀ m, κ m = Measure.pi (fun j ↦ W (x m j))) (i : Fin k) :
    (ν ⊗ₘ κ).map (fun ω ↦ (x ω.1 i, ω.2 i)) = (ν.map (fun m ↦ x m i)) ⊗ₘ W := by
  have hxi : Measurable (fun m ↦ x m i) := (measurable_pi_apply i).comp hx
  have hmarg : (ν ⊗ₘ κ).map (fun ω ↦ x ω.1 i) = ν.map (fun m ↦ x m i) := by
    rw [show (fun ω : M × (Fin k → B) ↦ x ω.1 i) = (fun m ↦ x m i) ∘ Prod.fst from rfl,
      ← Measure.map_map hxi measurable_fst]
    exact congrArg _ (Measure.fst_compProd ν κ)
  rw [compProd_pi_map_pair_eq_of_update_invariant ν x W κ hκ i (fun ω ↦ x ω.1 i)
      (hxi.comp measurable_fst) (fun _ _ _ ↦ rfl) id measurable_id (fun _ ↦ rfl),
    Kernel.comap_id, hmarg]

/-! ### Unzipping a product of two-stage laws -/

lemma measure_singleton_eq_mul_of_append {A B : Type*}
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (Q : Kernel A B) [IsMarkovKernel Q] (ρ : Measure (A × B))
    (hρ : ρ = (ρ.map Prod.fst).bind fun a ↦ (Q a).map fun b ↦ (a, b))
    (a : A) (b : B) :
    ρ {(a, b)} = (ρ.map Prod.fst) {a} * Q a {b} := by
  classical
  have key : ∀ a' : A, ((Q a').map fun b' ↦ (a', b')) {(a, b)}
      = if a' = a then Q a {b} else 0 := by
    intro a'
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
    by_cases h : a' = a
    · subst h
      rw [if_pos rfl]
      congr 1
      ext b'
      simp
    · rw [if_neg h]
      convert measure_empty (μ := Q a')
      ext b'
      simp [Prod.ext_iff, h]
  conv_lhs => rw [hρ]
  rw [Measure.bind_apply (measurableSet_singleton _) (measurable_of_countable _).aemeasurable,
    lintegral_fintype, Finset.sum_eq_single a]
  · rw [key a, if_pos rfl, mul_comm]
  · intro a' _ hne
    rw [key a', if_neg hne, zero_mul]
  · intro h
    simp at h

/-- The blockwise product `u ↦ ∏ⱼ Q (u j)` of a kernel `Q` out of a finite alphabet.

Mathlib has no `Kernel.pi`; over a countable alphabet with measurable singletons the family of
product measures is a kernel for free, which is what `Kernel.ofFunOfCountable` supplies here. -/
noncomputable def piBlockKernel {A B : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [MeasurableSpace B] {k : ℕ} (Q : Kernel A B) :
    Kernel (Fin k → A) (Fin k → B) :=
  Kernel.ofFunOfCountable fun u ↦ Measure.pi fun j ↦ Q (u j)

instance piBlockKernel_isMarkovKernel {A B : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [MeasurableSpace B] {k : ℕ} (Q : Kernel A B) [IsMarkovKernel Q] :
    IsMarkovKernel (piBlockKernel (k := k) Q) := by
  refine ⟨fun u ↦ ?_⟩
  change IsProbabilityMeasure (Measure.pi fun j ↦ Q (u j))
  infer_instance

lemma pi_map_unzip_eq_compProd {A B : Type*}
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    {k : ℕ} (Q : Kernel A B) [IsMarkovKernel Q]
    (ρ : Fin k → Measure (A × B)) [∀ j, IsProbabilityMeasure (ρ j)]
    (hρ : ∀ j, ρ j = ((ρ j).map Prod.fst).bind fun a ↦ (Q a).map fun b ↦ (a, b)) :
    (Measure.pi ρ).map (fun y ↦ ((fun j ↦ (y j).1), (fun j ↦ (y j).2)))
      = (Measure.pi fun j ↦ (ρ j).map Prod.fst) ⊗ₘ piBlockKernel Q := by
  classical
  refine Measure.ext_of_singleton fun p ↦ ?_
  obtain ⟨u, v⟩ := p
  have hmeas : Measurable
      (fun y : Fin k → A × B ↦ ((fun j ↦ (y j).1), (fun j ↦ (y j).2))) := by fun_prop
  have hpre : (fun y : Fin k → A × B ↦ ((fun j ↦ (y j).1), (fun j ↦ (y j).2))) ⁻¹' {(u, v)}
      = {fun j ↦ (u j, v j)} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.ext_iff, funext_iff, Prod.ext_iff]
    constructor
    · rintro ⟨h1, h2⟩; intro j; exact ⟨h1 j, h2 j⟩
    · intro h; exact ⟨fun j ↦ (h j).1, fun j ↦ (h j).2⟩
  rw [Measure.map_apply hmeas (measurableSet_singleton _), hpre, Measure.pi_singleton,
    Measure.compProd_apply (measurableSet_singleton _)]
  have hsec : ∀ w : Fin k → A, Prod.mk w ⁻¹' ({(u, v)} : Set ((Fin k → A) × (Fin k → B)))
      = if w = u then {v} else ∅ := by
    intro w
    by_cases h : w = u
    · subst h; ext z; simp
    · ext z; simp [h]
  simp_rw [hsec]
  rw [lintegral_fintype, Finset.sum_eq_single u]
  · rw [if_pos rfl, Measure.pi_singleton,
      show (piBlockKernel Q) u = Measure.pi (fun j ↦ Q (u j)) from rfl, Measure.pi_singleton,
      mul_comm, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ ↦
      measure_singleton_eq_mul_of_append Q (ρ j) (hρ j) (u j) (v j)
  · intro w _ hne
    simp [hne]
  · intro h
    simp at h

/-! ### Information transport under a shared pushforward -/

/-- Mutual information is invariant under a shared pushforward of both random variables:
`I(f; g) = I(f ∘ T; g ∘ T)` when the pair law on `μ.map T` matches the pair law of the composed
variables on `μ`. -/
lemma mutualInfo_map_comp
    {Ω Ω' A B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure Ω) (T : Ω → Ω') (hT : Measurable T)
    (f : Ω' → A) (hf : Measurable f) (g : Ω' → B) (hg : Measurable g) :
    mutualInfo (μ.map T) f g = mutualInfo μ (fun ω ↦ f (T ω)) (fun ω ↦ g (T ω)) := by
  unfold mutualInfo
  rw [Measure.map_map (hf.prodMk hg) hT, Measure.map_map hf hT, Measure.map_map hg hT]
  rfl

/-- `condDistrib` is stable under a shared pushforward of the conditioning and conditioned
variables: `condDistrib f h (μ.map T) =ᵐ condDistrib (f ∘ T) (h ∘ T) μ` on the conditioning
marginal `(μ.map T).map h`. -/
lemma condDistrib_map_comp
    {Ω Ω' A C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace C]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω') (hT : Measurable T)
    (f : Ω' → A) (hf : Measurable f) (h : Ω' → C) (hh : Measurable h) :
    condDistrib f h (μ.map T)
      =ᵐ[(μ.map T).map h] condDistrib (fun ω ↦ f (T ω)) (fun ω ↦ h (T ω)) μ := by
  haveI : IsProbabilityMeasure (μ.map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  refine condDistrib_ae_eq_of_measure_eq_compProd h hf.aemeasurable ?_
  rw [Measure.map_map (hh.prodMk hf) hT, Measure.map_map hh hT]
  exact (compProd_map_condDistrib (X := fun ω ↦ h (T ω)) (Y := fun ω ↦ f (T ω))
    (hf.comp hT).aemeasurable).symm

/-- Conditional mutual information is invariant under a shared pushforward of all three random
variables: `I(f; g | h) = I(f ∘ T; g ∘ T | h ∘ T)`. -/
lemma condMutualInfo_map_comp
    {Ω Ω' A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    [MeasurableSpace C]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω') (hT : Measurable T)
    (f : Ω' → A) (hf : Measurable f) (g : Ω' → B) (hg : Measurable g)
    (h : Ω' → C) (hh : Measurable h) :
    condMutualInfo (μ.map T) f g h
      = condMutualInfo μ (fun ω ↦ f (T ω)) (fun ω ↦ g (T ω)) (fun ω ↦ h (T ω)) := by
  haveI : IsProbabilityMeasure (μ.map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  have hbase : (μ.map T).map h = μ.map (fun ω ↦ h (T ω)) := Measure.map_map hh hT
  have hpair := condDistrib_map_comp μ T hT (fun q ↦ (f q, g q)) (hf.prodMk hg) h hh
  have hf' := condDistrib_map_comp μ T hT f hf h hh
  have hg' := condDistrib_map_comp μ T hT g hg h hh
  have hprodk :
      (condDistrib f h (μ.map T)) ×ₖ (condDistrib g h (μ.map T))
        =ᵐ[(μ.map T).map h]
      (condDistrib (fun ω ↦ f (T ω)) (fun ω ↦ h (T ω)) μ)
        ×ₖ (condDistrib (fun ω ↦ g (T ω)) (fun ω ↦ h (T ω)) μ) := by
    filter_upwards [hf', hg'] with a haf hag
    ext s hs
    rw [Kernel.prod_apply, Kernel.prod_apply, haf, hag]
  rw [hbase] at hpair hprodk
  unfold condMutualInfo
  rw [hbase]
  congr 1
  · exact Measure.compProd_congr hpair
  · exact Measure.compProd_congr hprodk

lemma isMarkovChain_map_comp
    {Ω Ω' A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    [MeasurableSpace C]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω') (hT : Measurable T)
    (f : Ω' → A) (hf : Measurable f) (g : Ω' → C) (hg : Measurable g)
    (h : Ω' → B) (hh : Measurable h)
    (ρ : Measure Ω') [IsFiniteMeasure ρ] (hρ : ρ = μ.map T)
    (hchain : IsMarkovChain μ (fun ω ↦ f (T ω)) (fun ω ↦ g (T ω)) (fun ω ↦ h (T ω))) :
    IsMarkovChain ρ f g h := by
  subst hρ
  haveI : IsProbabilityMeasure (μ.map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  have hbase : (μ.map T).map g = μ.map (fun ω ↦ g (T ω)) := Measure.map_map hg hT
  have hjoint : (μ.map T).map (fun r ↦ (g r, f r, h r))
      = μ.map (fun ω ↦ (g (T ω), f (T ω), h (T ω))) :=
    Measure.map_map (hg.prodMk (hf.prodMk hh)) hT
  have hf' := condDistrib_map_comp μ T hT f hf g hg
  have hh' := condDistrib_map_comp μ T hT h hh g hg
  rw [hbase] at hf' hh'
  unfold IsMarkovChain at hchain ⊢
  rw [hjoint, hchain, hbase]
  refine Measure.compProd_congr ?_
  filter_upwards [hf', hh'] with a haf hah
  ext s hs
  rw [Kernel.prod_apply, Kernel.prod_apply, haf, hah]

/-- `condMutualInfo_map_comp` phrased against any measure `ρ` propositionally equal to `μ.map T`.
The equation hypothesis is substituted (transporting its `IsFiniteMeasure` instance), which
sidesteps the ill-typed motive of rewriting the measure argument of `condMutualInfo` directly. -/
lemma condMutualInfo_map_comp'
    {Ω Ω' A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    [MeasurableSpace C]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω') (hT : Measurable T)
    (ρ : Measure Ω') [IsFiniteMeasure ρ] (hρ : ρ = μ.map T)
    (f : Ω' → A) (hf : Measurable f) (g : Ω' → B) (hg : Measurable g)
    (h : Ω' → C) (hh : Measurable h) :
    condMutualInfo ρ f g h
      = condMutualInfo μ (fun ω ↦ f (T ω)) (fun ω ↦ g (T ω)) (fun ω ↦ h (T ω)) := by
  subst hρ
  exact condMutualInfo_map_comp μ T hT f hf g hg h hh

/-! ### From a message count to a rate -/

/-- If `⌈exp x⌉₊ ≤ M` then `x ≤ log M`, converting a message count into a rate bound.  From
`exp x ≤ ⌈exp x⌉₊ ≤ M`, taking logs (both sides positive) gives `x = log (exp x) ≤ log M`. -/
lemma le_log_of_ceil_exp_le {x : ℝ} {M : ℕ}
    (hM : Nat.ceil (Real.exp x) ≤ M) : x ≤ Real.log (M : ℝ) := by
  have h1 : Real.exp x ≤ (Nat.ceil (Real.exp x) : ℝ) := Nat.le_ceil _
  have h2 : ((Nat.ceil (Real.exp x) : ℕ) : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr hM
  have h3 : Real.exp x ≤ (M : ℝ) := h1.trans h2
  calc x = Real.log (Real.exp x) := (Real.log_exp x).symm
    _ ≤ Real.log (M : ℝ) := Real.log_le_log (Real.exp_pos x) h3

/-! ### From an averaged bound to a real inequality -/

lemma le_toReal_of_inv_mul_le {S J : ℝ≥0∞} {m : ℕ} (hm : 0 < m)
    (hSJ : (m : ℝ≥0∞)⁻¹ * S ≤ J) (hJ : J ≠ ∞) {r : ℝ} (hr : (m : ℝ) * r ≤ S.toReal) :
    r ≤ J.toReal := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hminv : ((m : ℝ≥0∞))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top m)
  have hmono := ENNReal.toReal_mono hJ hSJ
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, inv_mul_eq_div] at hmono
  have hkey : r ≤ S.toReal / (m : ℝ) := (le_div_iff₀ hm0).mpr (by linarith)
  linarith

end InformationTheory.Shannon
