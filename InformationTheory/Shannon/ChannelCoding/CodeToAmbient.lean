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
* `isMemorylessChannel_of_compProd_pi`: if the kernel is the per-letter product `∏ⱼ W (x m j)`
  of a channel applied to a deterministic codeword, the ambient is a memoryless channel.
* `compProd_pi_map_pair_eq`: the joint law of the `i`-th input-output pair is the channel joint
  `(ν.map fun m ↦ x m i) ⊗ₘ W`.
* `mutualInfo_map_comp`, `condDistrib_map_comp`, `condMutualInfo_map_comp`: information
  quantities and conditional distributions are invariant under a shared pushforward of all their
  arguments.
* `le_log_of_ceil_exp_le`: `⌈exp x⌉₊ ≤ M` implies `x ≤ log M`, turning a message count into a
  rate bound.
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

/-! ### Marginalizing a product measure at one coordinate -/

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

/-! ### Memorylessness and the per-letter joint law -/

/-- A product-channel ambient is a memoryless channel: if the message-to-output kernel
factors as the per-letter product `κ m = ∏ⱼ W (x m j)` of a channel `W` applied to a
deterministic codeword `x m`, then `ν ⊗ₘ κ` is a memoryless channel with per-letter
inputs `x ω.1 i` and per-letter outputs `ω.2 i`.
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
  intro i
  set μ : Measure (M × (Fin k → B)) := ν ⊗ₘ κ with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  -- The three RVs of the per-letter Markov chain.
  set Zc : M × (Fin k → B) → A := fun ω ↦ x ω.1 i with hZc_def
  set Yo : M × (Fin k → B) → B := fun ω ↦ ω.2 i with hYo_def
  set Full : M × (Fin k → B) → (({j : Fin k // j ≠ i} → A) × ({j : Fin k // j ≠ i} → B)) :=
    fun ω ↦ ((fun j ↦ x ω.1 j.val), (fun j ↦ ω.2 j.val)) with hFull_def
  have hxi_meas : Measurable (fun m ↦ x m i) := (measurable_pi_apply i).comp hx
  have hZc_meas : Measurable Zc := hxi_meas.comp measurable_fst
  have hYo_meas : Measurable Yo := (measurable_pi_apply i).comp measurable_snd
  have hFull_meas : Measurable Full := by
    rw [hFull_def]
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_iff.mpr
        (fun j ↦ (measurable_pi_apply j.val).comp (hx.comp measurable_fst))
    · exact measurable_pi_iff.mpr (fun j ↦ (measurable_pi_apply j.val).comp measurable_snd)
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
  set K_Full := condDistrib Full Zc μ with hK_Full_def
  have h_compProd_eq :
      (μ.map Zc) ⊗ₘ (K_Full ×ₖ condDistrib Yo Zc μ) = (μ.map Zc) ⊗ₘ (K_Full ×ₖ W) := by
    refine Measure.compProd_congr ?_
    filter_upwards [hK_Y_eq] with a ha
    ext s hs
    rw [Kernel.prod_apply, Kernel.prod_apply, ha]
  rw [h_compProd_eq]
  -- Step 3: triple-joint factorization via `ext_of_lintegral` + the re-randomize identity.
  have h_LHS_meas : Measurable (fun ω ↦ (Zc ω, Full ω, Yo ω)) :=
    hZc_meas.prodMk (hFull_meas.prodMk hYo_meas)
  have hKX_fold : (μ.map Zc) ⊗ₘ K_Full = μ.map (fun ω ↦ (Zc ω, Full ω)) :=
    compProd_map_condDistrib (μ := μ) (X := Zc) (Y := Full) hFull_meas.aemeasurable
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [lintegral_map hf h_LHS_meas, Measure.lintegral_compProd hf]
  have h_inner_split : ∀ z : A,
      ∫⁻ p : (({j : Fin k // j ≠ i} → A) × ({j : Fin k // j ≠ i} → B)) × B,
          f (z, p.1, p.2) ∂((K_Full ×ₖ W) z)
        = ∫⁻ full, ∫⁻ b, f (z, full, b) ∂(W z) ∂(K_Full z) := by
    intro z
    rw [Kernel.prod_apply,
      lintegral_prod
        (fun p : (({j : Fin k // j ≠ i} → A) × ({j : Fin k // j ≠ i} → B)) × B ↦ f (z, p.1, p.2))
        (hf.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))).aemeasurable]
  simp_rw [h_inner_split]
  set G : A × (({j : Fin k // j ≠ i} → A) × ({j : Fin k // j ≠ i} → B)) → ℝ≥0∞ :=
    fun p ↦ ∫⁻ b, f (p.1, p.2, b) ∂(W p.1) with hG_def
  have hG_meas : Measurable G := by
    let K' : Kernel (A × (({j : Fin k // j ≠ i} → A) × ({j : Fin k // j ≠ i} → B))) B :=
      W.comap Prod.fst measurable_fst
    have h_eq_K' : G = fun p ↦ ∫⁻ b, f (p.1, p.2, b) ∂(K' p) := by
      funext p; simp [G, K', Kernel.comap_apply]
    rw [h_eq_K']
    exact Measurable.lintegral_kernel_prod_right' (κ := K')
      (f := fun pp ↦ f (pp.1.1, pp.1.2, pp.2))
      (hf.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  have h_RHS_is_G : ∀ z full, ∫⁻ b, f (z, full, b) ∂(W z) = G (z, full) := fun _ _ ↦ rfl
  simp_rw [h_RHS_is_G]
  have hFmeas2 : Measurable (fun ω ↦ f (Zc ω, Full ω, Yo ω)) := hf.comp h_LHS_meas
  have hGmeas2 : Measurable (fun ω ↦ G (Zc ω, Full ω)) := hG_meas.comp (hZc_meas.prodMk hFull_meas)
  rw [← Measure.lintegral_compProd hG_meas, hKX_fold,
    lintegral_map hG_meas (hZc_meas.prodMk hFull_meas), hμ_def,
    Measure.lintegral_compProd hFmeas2, Measure.lintegral_compProd hGmeas2]
  refine lintegral_congr fun m ↦ ?_
  rw [hκ]
  have hpair_m : Measurable (fun y : Fin k → B ↦ ((m, y) : M × (Fin k → B))) :=
    measurable_const.prodMk measurable_id
  have hFm3 : Measurable (fun y ↦ f (Zc (m, y), Full (m, y), Yo (m, y))) :=
    hf.comp ((hZc_meas.comp hpair_m).prodMk
      ((hFull_meas.comp hpair_m).prodMk (hYo_meas.comp hpair_m)))
  rw [lintegral_pi_reRandomize (fun j ↦ W (x m j)) i
    (fun y ↦ f (Zc (m, y), Full (m, y), Yo (m, y))) hFm3]
  refine lintegral_congr fun y ↦ ?_
  rw [hG_def]
  show ∫⁻ b, f (Zc (m, Function.update y i b), Full (m, Function.update y i b),
      Yo (m, Function.update y i b)) ∂(W (x m i))
    = ∫⁻ b, f (Zc (m, y), Full (m, y), b) ∂(W (x m i))
  refine lintegral_congr fun b ↦ ?_
  refine congrArg f (Prod.ext rfl (Prod.ext (Prod.ext rfl ?_) ?_))
  · funext j; exact Function.update_of_ne j.2 b y
  · exact Function.update_self i b y

/-- Per-letter joint pushforward of a product-channel `compProd`: for an ambient `ν ⊗ₘ κ`
whose message-to-output kernel factors as the per-letter product `κ m = ∏ⱼ W (x m j)`, the
joint law of the `i`-th input-output pair `(x ω.1 i, ω.2 i)` is the channel joint
`(ν.map fun m ↦ x m i) ⊗ₘ W`.  Stated separately from `isMemorylessChannel_of_compProd_pi`,
which establishes the same identity internally, because it is what identifies a per-letter
information quantity of the ambient with the corresponding channel quantity. -/
lemma compProd_pi_map_pair_eq
    {M A B : Type*} [MeasurableSpace M] [MeasurableSpace A] [MeasurableSpace B]
    {k : ℕ} (ν : Measure M) [IsProbabilityMeasure ν]
    (x : M → Fin k → A) (hx : Measurable x)
    (W : Kernel A B) [IsMarkovKernel W]
    (κ : Kernel M (Fin k → B)) [IsMarkovKernel κ]
    (hκ : ∀ m, κ m = Measure.pi (fun j ↦ W (x m j))) (i : Fin k) :
    (ν ⊗ₘ κ).map (fun ω ↦ (x ω.1 i, ω.2 i)) = (ν.map (fun m ↦ x m i)) ⊗ₘ W := by
  set μ : Measure (M × (Fin k → B)) := ν ⊗ₘ κ with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  set Zc : M × (Fin k → B) → A := fun ω ↦ x ω.1 i with hZc_def
  set Yo : M × (Fin k → B) → B := fun ω ↦ ω.2 i with hYo_def
  have hxi_meas : Measurable (fun m ↦ x m i) := (measurable_pi_apply i).comp hx
  have hZc_meas : Measurable Zc := hxi_meas.comp measurable_fst
  have hYo_meas : Measurable Yo := (measurable_pi_apply i).comp measurable_snd
  show μ.map (fun ω ↦ (Zc ω, Yo ω)) = (ν.map (fun m ↦ x m i)) ⊗ₘ W
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

end InformationTheory.Shannon
