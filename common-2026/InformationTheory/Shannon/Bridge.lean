import InformationTheory.Shannon.MutualInfo
import InformationTheory.Fano.Measure
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# Bridge: mutual information (KL form) ↔ conditional entropy

For a finite alphabet `X` and a probability measure `μ`,
`(mutualInfo μ Xs Yo).toReal = entropy μ Xs - condEntropy μ Xs Yo`.

## Main statements

* `mutualInfo_eq_entropy_sub_condEntropy` — the bridge identity.

## Implementation notes

The proof establishes `(μ.map (Xs, Yo)) ≪ (μ.map Xs).prod (μ.map Yo)` on a
finite alphabet, translates the KL divergence to a Bochner integral via
`toReal_klDiv_of_measure_eq`, decomposes over the finite alphabet, and separates
into `H(X) - H(X|Y)` by linearity.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  [MeasurableSpace X] [MeasurableSingletonClass X]
variable {Y : Type*} [MeasurableSpace Y]

/-- Shannon entropy of a discrete random variable taking values in a finite alphabet. -/
noncomputable def entropy (μ : Measure Ω) (Xs : Ω → X) : ℝ :=
  ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})

omit [DecidableEq X] [Nonempty X] [MeasurableSingletonClass X] in
lemma entropy_nonneg (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (hXs : Measurable Xs) : 0 ≤ entropy μ Xs := by
  have _ : IsProbabilityMeasure (μ.map Xs) :=
    Measure.isProbabilityMeasure_map hXs.aemeasurable
  unfold entropy
  exact Finset.sum_nonneg fun x _ =>
    Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one

omit [DecidableEq X] [Nonempty X] in
private theorem absolutelyContinuous_joint_prod_marginals
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    (μ.map (fun ω => (Xs ω, Yo ω))) ≪ (μ.map Xs).prod (μ.map Yo) := by
  have hpair : Measurable (fun ω => (Xs ω, Yo ω)) := hXs.prodMk hYo
  have _ : IsProbabilityMeasure (μ.map Yo) :=
    Measure.isProbabilityMeasure_map hYo.aemeasurable
  have _ : IsProbabilityMeasure (μ.map Xs) :=
    Measure.isProbabilityMeasure_map hXs.aemeasurable
  refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
  -- 1. Expand the product-measure 0 via Tonelli + Fintype sum
  rw [Measure.prod_apply hA, lintegral_fintype] at hA0
  have hzero : ∀ x : X,
      (μ.map Yo) (Prod.mk x ⁻¹' A) * (μ.map Xs) {x} = 0 := by
    intro x
    have hsum := (Finset.sum_eq_zero_iff (s := (Finset.univ : Finset X))
        (f := fun x => (μ.map Yo) (Prod.mk x ⁻¹' A) * (μ.map Xs) {x})).mp hA0
    exact hsum x (Finset.mem_univ _)
  -- 2. Rewrite the joint measure as a finite union over Xs slices and show each slice is 0
  rw [Measure.map_apply hpair hA]
  have hslice : (fun ω => (Xs ω, Yo ω)) ⁻¹' A
      = ⋃ x : X, (Xs ⁻¹' {x}) ∩ (Yo ⁻¹' (Prod.mk x ⁻¹' A)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    refine ⟨fun h => ⟨Xs ω, rfl, h⟩, ?_⟩
    rintro ⟨x, hx, hY⟩
    rw [hx]; exact hY
  rw [hslice]
  refine measure_iUnion_null fun x => ?_
  have hAx : MeasurableSet (Prod.mk x ⁻¹' A) := measurable_prodMk_left hA
  rcases mul_eq_zero.mp (hzero x) with hY0 | hX0
  · -- (μ.map Yo)(slice) = 0 ⇒ μ(Yo ⁻¹' slice) = 0
    have : μ (Yo ⁻¹' (Prod.mk x ⁻¹' A)) = 0 := by
      rwa [← Measure.map_apply hYo hAx]
    exact measure_mono_null Set.inter_subset_right this
  · -- (μ.map Xs){x} = 0 ⇒ μ(Xs ⁻¹' {x}) = 0
    have : μ (Xs ⁻¹' {x}) = 0 := by
      rwa [← Measure.map_apply hXs (measurableSet_singleton x)]
    exact measure_mono_null Set.inter_subset_left this

/-! ### Helper lemmas for the bridge

The bridge proof goes via three independent helpers:

* `klDiv_compProd_const_eq_lintegral`: fiberwise expansion of conditional KL,
  `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ Kernel.const _ ν) = ∫⁻ x, klDiv (κ x) ν ∂μ`. The
  Mathlib chain rule (`klDiv_compProd_eq_add`) only gives the *non*-fiberwise
  form; we need the integral identity to land at `condEntropy`.

* `klDiv_discrete_toReal_eq_sum`: discrete `klDiv` on a finite alphabet
  expands as `∑ x, Q.real{x} * (log Q.real{x} - log P.real{x})`.

* `integral_condDistrib_real_singleton_eq`: marginal recovery,
  `∫ y, (condDistrib Xs Yo μ y).real {x} d(μ.map Yo) = (μ.map Xs).real {x}`.
-/

private lemma rnDeriv_compProd_ae_eq_kernel_rnDeriv
    {α β : Type*} {_mα : MeasurableSpace α} {_mβ : MeasurableSpace β}
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac_kernel : ∀ᵐ a ∂μ, κ a ≪ η a) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η]
      fun p => Kernel.rnDeriv κ η p.1 p.2 := by
  have h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
    Measure.AbsolutelyContinuous.compProd_right h_ac_kernel
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (Measure.measurable_rnDeriv _ _) (Kernel.measurable_rnDeriv κ η) fun s hs _ => ?_
  -- Step 1: rectangle case via `setLIntegral_compProd` + `Kernel.setLIntegral_rnDeriv`.
  have h_rect : ∀ t₁ t₂, MeasurableSet t₁ → MeasurableSet t₂ →
      ∫⁻ p in t₁ ×ˢ t₂, (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p ∂(μ ⊗ₘ η)
        = ∫⁻ p in t₁ ×ˢ t₂, Kernel.rnDeriv κ η p.1 p.2 ∂(μ ⊗ₘ η) := by
    intro t₁ t₂ ht₁ ht₂
    rw [Measure.setLIntegral_rnDeriv h_ac, Measure.compProd_apply_prod ht₁ ht₂,
      Measure.setLIntegral_compProd (Kernel.measurable_rnDeriv κ η) ht₁ ht₂]
    refine setLIntegral_congr_fun_ae ht₁ ?_
    filter_upwards [h_ac_kernel] with a ha _
    exact (Kernel.setLIntegral_rnDeriv ha ht₂).symm
  -- Step 2: π-system induction on rectangles in α × β.
  refine MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ s hs
  · simp
  · rintro _ ⟨t₁, ht₁, t₂, ht₂, rfl⟩
    exact h_rect t₁ t₂ ht₁ ht₂
  · intro t ht ht_eq
    have h_lhs_ne : ∫⁻ p in t, (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p ∂(μ ⊗ₘ η) ≠ ∞ :=
      ((Measure.setLIntegral_rnDeriv_le _).trans_lt (measure_lt_top _ _)).ne
    rw [setLIntegral_compl ht h_lhs_ne, ht_eq, setLIntegral_compl ht (ht_eq ▸ h_lhs_ne)]
    congr 1
    have hu := h_rect Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
    simpa only [Set.univ_prod_univ, Measure.restrict_univ] using hu
  · intro f' hf_disj hf_meas hf_eq
    rw [lintegral_iUnion hf_meas hf_disj, lintegral_iUnion hf_meas hf_disj]
    congr with i
    exact hf_eq i

private lemma klDiv_compProd_const_eq_lintegral_of_ac
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) [IsFiniteKernel κ]
    (ν : Measure β) [IsFiniteMeasure ν]
    (h_ac_kernel : ∀ᵐ x ∂μ, κ x ≪ ν) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ Kernel.const α ν)
      = ∫⁻ x, klDiv (κ x) ν ∂μ := by
  have h_ac_kernel_const : ∀ᵐ a ∂μ, κ a ≪ (Kernel.const α ν : Kernel α β) a := by
    filter_upwards [h_ac_kernel] with a ha
    simpa using ha
  have h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ Kernel.const α ν :=
    Measure.AbsolutelyContinuous.compProd_right h_ac_kernel_const
  -- Joint rnDeriv ae-identification (kernel side, jointly measurable).
  have h_rnD := rnDeriv_compProd_ae_eq_kernel_rnDeriv μ κ (Kernel.const α ν) h_ac_kernel_const
  -- LHS: rewrite via `klDiv_eq_lintegral_klFun_of_ac` and the joint rnDeriv ae-replacement.
  rw [klDiv_eq_lintegral_klFun_of_ac h_ac]
  -- Replace joint rnDeriv with `Kernel.rnDeriv κ (const ν) p.1 p.2` (still jointly measurable).
  have h_integrand :
      (fun p : α × β => ENNReal.ofReal
          (klFun ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ Kernel.const α ν) p).toReal))
        =ᵐ[μ ⊗ₘ Kernel.const α ν]
        fun p => ENNReal.ofReal
          (klFun (Kernel.rnDeriv κ (Kernel.const α ν) p.1 p.2).toReal) := by
    filter_upwards [h_rnD] with p hp
    rw [hp]
  rw [lintegral_congr_ae h_integrand,
    Measure.lintegral_compProd (by fun_prop)]
  -- For ae `a`, replace `Kernel.rnDeriv κ (const ν) a b` with `(κ a).rnDeriv ν b` (ae over `ν`),
  -- then collapse the inner integral to `klDiv (κ a) ν`.
  refine lintegral_congr_ae ?_
  filter_upwards [h_ac_kernel] with a ha
  have h_inner :
      (fun b : β => ENNReal.ofReal
          (klFun (Kernel.rnDeriv κ (Kernel.const α ν) a b).toReal))
        =ᵐ[(Kernel.const α ν : Kernel α β) a]
        fun b => ENNReal.ofReal (klFun ((κ a).rnDeriv ν b).toReal) := by
    have := Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := Kernel.const α ν) (a := a)
    filter_upwards [this] with b hb
    simp only [Kernel.const_apply] at hb
    rw [hb]
  rw [lintegral_congr_ae h_inner]
  simp_rw [Kernel.const_apply]
  rw [klDiv_eq_lintegral_klFun_of_ac ha]


omit [DecidableEq X] [Nonempty X] in
private lemma klDiv_discrete_toReal_eq_sum
    (Q P : Measure X) [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    (hQP : Q ≪ P) :
    (klDiv Q P).toReal
      = ∑ x : X, Q.real {x} * (Real.log (Q.real {x}) - Real.log (P.real {x})) := by
  -- (1) `Q univ = P univ = 1`, so we can use `toReal_klDiv_of_measure_eq`.
  have h_univ : Q Set.univ = P Set.univ := by
    rw [measure_univ, measure_univ]
  rw [toReal_klDiv_of_measure_eq hQP h_univ]
  -- (2) `llr Q P` is integrable on a Fintype with finite measure.
  have h_int : Integrable (llr Q P) Q := by
    refine ⟨(measurable_llr Q P).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_fintype]
    exact ENNReal.sum_lt_top.mpr fun _ _ =>
      ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)
  rw [integral_fintype h_int]
  -- (3) Per-`x` rewrite.
  refine Finset.sum_congr rfl fun x _ => ?_
  -- `Q.real {x} • llr Q P x = Q.real {x} * (log Q.real {x} - log P.real {x})`
  show Q.real {x} * Real.log (Q.rnDeriv P x).toReal
    = Q.real {x} * (Real.log (Q.real {x}) - Real.log (P.real {x}))
  by_cases hQx : Q.real {x} = 0
  · simp [hQx]
  -- (4) `Q.real {x} > 0`, so `P.real {x} > 0` (by `Q ≪ P`), and
  --     `(Q.rnDeriv P x).toReal * P.real {x} = Q.real {x}` (rnDeriv identification).
  have hQ_ne : Q {x} ≠ 0 := by
    intro h
    apply hQx
    rw [Measure.real, h]
    rfl
  have hP_ne : P {x} ≠ 0 := fun h => hQ_ne (hQP h)
  have hPx_pos : 0 < P.real {x} := by
    refine lt_of_le_of_ne measureReal_nonneg (Ne.symm ?_)
    intro hPx
    apply hP_ne
    rwa [Measure.real, ENNReal.toReal_eq_zero_iff,
      or_iff_left (measure_ne_top P {x})] at hPx
  have hQx_pos : 0 < Q.real {x} :=
    lt_of_le_of_ne measureReal_nonneg (Ne.symm hQx)
  -- ENNReal identity: `(Q.rnDeriv P x) * P {x} = Q {x}`.
  have h_rnD_enn : (Q.rnDeriv P x) * P {x} = Q {x} := by
    have h_wd : P.withDensity (Q.rnDeriv P) = Q :=
      Measure.withDensity_rnDeriv_eq Q P hQP
    have h1 : (P.withDensity (Q.rnDeriv P)) {x} = Q {x} := by rw [h_wd]
    rw [withDensity_apply _ (measurableSet_singleton x),
      lintegral_singleton] at h1
    exact h1
  -- toReal version.
  have h_rnD_real : (Q.rnDeriv P x).toReal * P.real {x} = Q.real {x} := by
    rw [Measure.real, Measure.real, ← ENNReal.toReal_mul, h_rnD_enn]
  -- Solve for `(Q.rnDeriv P x).toReal = Q.real {x} / P.real {x}`.
  have h_rnD_div : (Q.rnDeriv P x).toReal = Q.real {x} / P.real {x} := by
    field_simp
    linarith [h_rnD_real]
  rw [h_rnD_div, Real.log_div hQx_pos.ne' hPx_pos.ne']

omit [DecidableEq X] in
private lemma lintegral_condDistrib_singleton_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (x : X) :
    ∫⁻ y, (condDistrib Xs Yo μ y) {x} ∂(μ.map Yo)
      = (μ.map Xs) {x} := by
  have h_compProd : (μ.map Yo) ⊗ₘ (condDistrib Xs Yo μ)
      = μ.map (fun ω => (Yo ω, Xs ω)) := compProd_map_condDistrib hXs.aemeasurable
  have hpair : Measurable (fun ω => (Yo ω, Xs ω)) := hYo.prodMk hXs
  have hxs : MeasurableSet ({x} : Set X) := measurableSet_singleton x
  have h₁ : ((μ.map Yo) ⊗ₘ (condDistrib Xs Yo μ)) ((Set.univ : Set Y) ×ˢ ({x} : Set X))
      = ∫⁻ y in Set.univ, (condDistrib Xs Yo μ y) {x} ∂(μ.map Yo) :=
    Measure.compProd_apply_prod MeasurableSet.univ hxs
  rw [Measure.restrict_univ] at h₁
  rw [← h₁, h_compProd, Measure.map_apply hpair (MeasurableSet.univ.prod hxs),
      Measure.map_apply hXs hxs]
  congr 1
  ext ω
  simp

omit [DecidableEq X] in
private lemma integral_condDistrib_real_singleton_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (x : X) :
    ∫ y, (condDistrib Xs Yo μ y).real {x} ∂(μ.map Yo)
      = (μ.map Xs).real {x} := by
  have _ : IsProbabilityMeasure (μ.map Yo) :=
    Measure.isProbabilityMeasure_map hYo.aemeasurable
  -- Convert the ∫ (Bochner) into toReal of ∫⁻ via integral_toReal
  have h_ae_lt_top : ∀ᵐ y ∂(μ.map Yo), (condDistrib Xs Yo μ y) {x} < ∞ := by
    refine ae_of_all _ fun y => ?_
    exact (measure_lt_top _ _)
  have h_meas : AEMeasurable (fun y => (condDistrib Xs Yo μ y) {x}) (μ.map Yo) :=
    ((Kernel.measurable_coe _ (measurableSet_singleton x))).aemeasurable
  rw [show (fun y => ((condDistrib Xs Yo μ y).real ({x} : Set X)))
        = (fun y => ((condDistrib Xs Yo μ y) {x}).toReal) from rfl,
      integral_toReal h_meas h_ae_lt_top,
      lintegral_condDistrib_singleton_eq μ Xs Yo hXs hYo x]
  rfl

omit [DecidableEq X] in
private lemma condDistrib_ae_absolutelyContinuous_map
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    ∀ᵐ y ∂(μ.map Yo), condDistrib Xs Yo μ y ≪ μ.map Xs := by
  have _ : IsProbabilityMeasure (μ.map Yo) :=
    Measure.isProbabilityMeasure_map hYo.aemeasurable
  have _ : IsProbabilityMeasure (μ.map Xs) :=
    Measure.isProbabilityMeasure_map hXs.aemeasurable
  have h_compProd : (μ.map Yo) ⊗ₘ (condDistrib Xs Yo μ)
      = μ.map (fun ω => (Yo ω, Xs ω)) := compProd_map_condDistrib hXs.aemeasurable
  -- Step 1: per-`x` ae vanishing of `condDistrib y {x}` when `(μ.map Xs) {x} = 0`.
  have h_each_x : ∀ x : X, (μ.map Xs) {x} = 0 →
      ∀ᵐ y ∂(μ.map Yo), condDistrib Xs Yo μ y {x} = 0 := by
    intro x hx
    have hx_meas : MeasurableSet ({x} : Set X) := measurableSet_singleton x
    have h_joint_zero :
        (μ.map (fun ω => (Yo ω, Xs ω))) (Set.univ ×ˢ ({x} : Set X)) = 0 := by
      rw [Measure.map_apply (hYo.prodMk hXs) (MeasurableSet.univ.prod hx_meas)]
      have hsubset : (fun ω => (Yo ω, Xs ω)) ⁻¹' (Set.univ ×ˢ ({x} : Set X))
          ⊆ Xs ⁻¹' {x} := fun ω h => by simpa using h
      have h0 : μ (Xs ⁻¹' {x}) = 0 := by
        rwa [← Measure.map_apply hXs hx_meas]
      exact measure_mono_null hsubset h0
    rw [← h_compProd, Measure.compProd_apply_prod MeasurableSet.univ hx_meas,
      lintegral_eq_zero_iff (Kernel.measurable_coe _ hx_meas)] at h_joint_zero
    rwa [Measure.restrict_univ] at h_joint_zero
  -- Step 2: take ae intersection over the (finitely many) `x : X`.
  have h_combined :
      ∀ᵐ y ∂(μ.map Yo), ∀ x : X, (μ.map Xs) {x} = 0 → condDistrib Xs Yo μ y {x} = 0 := by
    rw [ae_all_iff]
    intro x
    by_cases hx : (μ.map Xs) {x} = 0
    · filter_upwards [h_each_x x hx] with y hy _ using hy
    · exact ae_of_all _ fun _ hxy => absurd hxy hx
  -- Step 3: conclude AC via Finset decomposition.
  classical
  filter_upwards [h_combined] with y hy
  refine Measure.AbsolutelyContinuous.mk fun A _ hA0 => ?_
  -- Decompose `A` as finite biUnion of singletons via `Finset.univ.filter (· ∈ A)`.
  set s : Finset X := Finset.univ.filter (· ∈ A)
  have hA_decomp : A = ⋃ x ∈ s, ({x} : Set X) := by
    ext z
    simp [s, Finset.mem_filter]
  have h_pwd : Set.PairwiseDisjoint (↑s) (fun x : X => ({x} : Set X)) :=
    fun a _ b _ hne => Set.disjoint_singleton.mpr hne
  have h_meas : ∀ x ∈ s, MeasurableSet ({x} : Set X) :=
    fun x _ => measurableSet_singleton x
  have hP_sum : ∑ x ∈ s, (μ.map Xs) {x} = 0 := by
    rw [← measure_biUnion_finset h_pwd h_meas, ← hA_decomp]; exact hA0
  have hP_each : ∀ x ∈ s, (μ.map Xs) {x} = 0 := fun x hx =>
    le_antisymm (hP_sum ▸ Finset.single_le_sum (f := fun y => (μ.map Xs) {y})
      (fun _ _ => bot_le) hx) bot_le
  rw [hA_decomp, measure_biUnion_finset h_pwd h_meas]
  exact Finset.sum_eq_zero fun x hx => hy x (hP_each x hx)

omit [DecidableEq X] [Nonempty X] in
private theorem integrable_sum_fibre_real_mul_log
    (κ : Kernel Y X) [IsMarkovKernel κ]
    (νY : Measure Y) [IsFiniteMeasure νY] (νX : Measure X) :
    (Integrable (fun y => ∑ x : X, (κ y).real {x}
        * Real.log ((κ y).real {x})) νY)
      ∧ (Integrable (fun y => ∑ x : X, (κ y).real {x}
        * Real.log (νX.real {x})) νY) := by
  have h_meas_real_Q : ∀ x : X, Measurable (fun y => (κ y).real {x}) :=
    fun x => (Kernel.measurable_coe _ (measurableSet_singleton x)).ennreal_toReal
  have h_Q_le_one : ∀ y x, (κ y).real {x} ≤ 1 :=
    fun y x => measureReal_le_one (μ := κ y) (s := {x})
  have h_int_QlogQ : ∀ x : X, Integrable
      (fun y => (κ y).real {x} * Real.log ((κ y).real {x})) νY := by
    intro x
    refine Integrable.mono' (g := fun _ => (1 : ℝ))
      (integrable_const _)
      ((h_meas_real_Q x).mul (h_meas_real_Q x).log).aestronglyMeasurable ?_
    refine ae_of_all _ fun y => ?_
    have hQ_nn : 0 ≤ (κ y).real {x} := measureReal_nonneg
    have hQ_le : (κ y).real {x} ≤ 1 := h_Q_le_one y x
    have h_negMulLog_nn : 0 ≤ Real.negMulLog ((κ y).real {x}) :=
      Real.negMulLog_nonneg hQ_nn hQ_le
    have h_negMulLog_le_one : Real.negMulLog ((κ y).real {x}) ≤ 1 := by
      refine (Real.negMulLog_le_one_sub_self hQ_nn).trans ?_
      linarith
    have h_eq : (κ y).real {x} * Real.log ((κ y).real {x})
        = -Real.negMulLog ((κ y).real {x}) := by
      rw [Real.negMulLog]; ring
    rw [Real.norm_eq_abs, h_eq, abs_neg, abs_of_nonneg h_negMulLog_nn]
    exact h_negMulLog_le_one
  have h_int_QlogP : ∀ x : X, Integrable
      (fun y => (κ y).real {x} * Real.log (νX.real {x})) νY := by
    intro x
    refine Integrable.mul_const ?_ _
    refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const _)
      (h_meas_real_Q x).aestronglyMeasurable ?_
    refine ae_of_all _ fun y => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact h_Q_le_one y x
  exact ⟨integrable_finsetSum _ fun x _ => h_int_QlogQ x,
    integrable_finsetSum _ fun x _ => h_int_QlogP x⟩

omit [DecidableEq X] in
private theorem klDiv_joint_prod_marginals_toReal
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    (klDiv (μ.map (fun ω => (Xs ω, Yo ω)))
        ((μ.map Xs).prod (μ.map Yo))).toReal
      = entropy μ Xs - InformationTheory.MeasureFano.condEntropy μ Xs Yo := by
  classical
  have hMYo : IsProbabilityMeasure (μ.map Yo) :=
    Measure.isProbabilityMeasure_map hYo.aemeasurable
  have hMXs : IsProbabilityMeasure (μ.map Xs) :=
    Measure.isProbabilityMeasure_map hXs.aemeasurable
  -- Step 1: swap to (Yo, Xs) form via `mutualInfo_comm`.
  have h_swap_kl : klDiv (μ.map (fun ω => (Xs ω, Yo ω))) ((μ.map Xs).prod (μ.map Yo))
      = klDiv (μ.map (fun ω => (Yo ω, Xs ω))) ((μ.map Yo).prod (μ.map Xs)) := by
    have := mutualInfo_comm μ Xs Yo hXs hYo
    simpa [mutualInfo] using this
  rw [h_swap_kl]
  -- Step 2: rewrite both sides as compProd.
  have h_eq_joint : μ.map (fun ω => (Yo ω, Xs ω))
      = (μ.map Yo) ⊗ₘ (condDistrib Xs Yo μ) :=
    (compProd_map_condDistrib hXs.aemeasurable).symm
  have h_eq_prod : (μ.map Yo).prod (μ.map Xs)
      = (μ.map Yo) ⊗ₘ Kernel.const Y (μ.map Xs) := Measure.compProd_const.symm
  rw [h_eq_joint, h_eq_prod]
  -- Step 3: Helper 1 reduces LHS to a y-lintegral of fibre KLs.
  have h_ac_fibre := condDistrib_ae_absolutelyContinuous_map μ Xs Yo hXs hYo
  rw [klDiv_compProd_const_eq_lintegral_of_ac (μ.map Yo) (condDistrib Xs Yo μ)
    (μ.map Xs) h_ac_fibre]
  -- (5a) llr Q P is integrable on each fibre (Fintype + finite measure).
  have h_int_llr : ∀ᵐ y ∂(μ.map Yo),
      Integrable (llr (condDistrib Xs Yo μ y) (μ.map Xs)) (condDistrib Xs Yo μ y) := by
    refine ae_of_all _ fun y => ?_
    refine ⟨(measurable_llr _ _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_fintype]
    exact ENNReal.sum_lt_top.mpr fun _ _ =>
      ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)
  -- (5b) klDiv ≠ ∞ on the AC fibre.
  have h_klDiv_ne_top : ∀ᵐ y ∂(μ.map Yo),
      klDiv (condDistrib Xs Yo μ y) (μ.map Xs) ≠ ∞ := by
    filter_upwards [h_ac_fibre, h_int_llr] with y hy hint
    exact klDiv_ne_top hy hint
  -- (5c) Rewrite klDiv ae as ENNReal.ofReal of the Helper 5 sum.
  have h_klDiv_eq : ∀ᵐ y ∂(μ.map Yo),
      klDiv (condDistrib Xs Yo μ y) (μ.map Xs)
        = ENNReal.ofReal (∑ x : X, (condDistrib Xs Yo μ y).real {x}
            * (Real.log ((condDistrib Xs Yo μ y).real {x})
              - Real.log ((μ.map Xs).real {x}))) := by
    filter_upwards [h_ac_fibre, h_klDiv_ne_top] with y hy hne
    rw [← ENNReal.ofReal_toReal hne]
    exact congrArg ENNReal.ofReal (klDiv_discrete_toReal_eq_sum _ _ hy)
  rw [lintegral_congr_ae h_klDiv_eq]
  -- (5d) Convert (∫⁻ ofReal S).toReal back to a Bochner integral via nonneg + AEStronglyMeasurable.
  have h_meas_real_Q : ∀ x : X,
      Measurable (fun y => (condDistrib Xs Yo μ y).real {x}) :=
    fun x => (Kernel.measurable_coe _ (measurableSet_singleton x)).ennreal_toReal
  have h_S_meas : AEStronglyMeasurable
      (fun y => ∑ x : X, (condDistrib Xs Yo μ y).real {x}
        * (Real.log ((condDistrib Xs Yo μ y).real {x})
          - Real.log ((μ.map Xs).real {x}))) (μ.map Yo) := by
    refine Finset.aestronglyMeasurable_fun_sum (M := ℝ) _ fun x _ => ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (h_meas_real_Q x).aestronglyMeasurable
    · exact ((h_meas_real_Q x).log.sub_const _).aestronglyMeasurable
  have h_S_nonneg : 0 ≤ᵐ[μ.map Yo]
      (fun y => ∑ x : X, (condDistrib Xs Yo μ y).real {x}
        * (Real.log ((condDistrib Xs Yo μ y).real {x})
          - Real.log ((μ.map Xs).real {x}))) := by
    filter_upwards [h_ac_fibre] with y hy
    rw [← klDiv_discrete_toReal_eq_sum (condDistrib Xs Yo μ y) (μ.map Xs) hy]
    exact ENNReal.toReal_nonneg
  rw [← integral_eq_lintegral_of_nonneg_ae h_S_nonneg h_S_meas]
  -- (6) Split the inner sum: Q*(logQ - logP) = Q*logQ - Q*logP, then move - outside the integral.
  have h_split : ∀ y,
      (∑ x : X, (condDistrib Xs Yo μ y).real {x}
        * (Real.log ((condDistrib Xs Yo μ y).real {x})
          - Real.log ((μ.map Xs).real {x})))
        = (∑ x : X, (condDistrib Xs Yo μ y).real {x}
              * Real.log ((condDistrib Xs Yo μ y).real {x}))
          - (∑ x : X, (condDistrib Xs Yo μ y).real {x}
              * Real.log ((μ.map Xs).real {x})) := by
    intro y
    rw [show (∑ x : X, (condDistrib Xs Yo μ y).real {x}
              * Real.log ((condDistrib Xs Yo μ y).real {x}))
            - (∑ x : X, (condDistrib Xs Yo μ y).real {x}
              * Real.log ((μ.map Xs).real {x}))
          = ∑ x : X, ((condDistrib Xs Yo μ y).real {x}
              * Real.log ((condDistrib Xs Yo μ y).real {x})
            - (condDistrib Xs Yo μ y).real {x}
              * Real.log ((μ.map Xs).real {x}))
          from (Finset.sum_sub_distrib (s := (Finset.univ : Finset X))
            (f := fun x => (condDistrib Xs Yo μ y).real {x}
                * Real.log ((condDistrib Xs Yo μ y).real {x}))
            (g := fun x => (condDistrib Xs Yo μ y).real {x}
                * Real.log ((μ.map Xs).real {x}))).symm]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  simp_rw [h_split]
  obtain ⟨h_int_sumQlogQ, h_int_sumQlogP⟩ :=
    integrable_sum_fibre_real_mul_log (condDistrib Xs Yo μ) (μ.map Yo) (μ.map Xs)
  -- Term 2: Q.real{x} * log P.real{x} = constant_x * Q.real{x}, bounded → integrable.
  have h_int_QlogP : ∀ x : X, Integrable
      (fun y => (condDistrib Xs Yo μ y).real {x}
        * Real.log ((μ.map Xs).real {x})) (μ.map Yo) := by
    intro x
    refine Integrable.mul_const ?_ _
    refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const _)
      (h_meas_real_Q x).aestronglyMeasurable ?_
    refine ae_of_all _ fun y => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one (μ := condDistrib Xs Yo μ y) (s := {x})
  -- (7) Linear split of the integral.
  rw [integral_sub h_int_sumQlogQ h_int_sumQlogP]
  -- (7-a) First term: ∫ ∑ Q*logQ = -condEntropy.
  have h_first :
      (fun y => ∑ x : X, (condDistrib Xs Yo μ y).real {x}
          * Real.log ((condDistrib Xs Yo μ y).real {x}))
        = (fun y => -∑ x : X,
            Real.negMulLog ((condDistrib Xs Yo μ y).real {x})) := by
    funext y
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Real.negMulLog]; ring
  rw [h_first, integral_neg]
  -- (7-b) Second term: ∫ ∑ Q*logP = -entropy via Helper 3.
  rw [integral_finsetSum _ fun x _ => h_int_QlogP x]
  have h_second_term_each : ∀ x : X,
      ∫ y, (condDistrib Xs Yo μ y).real {x}
        * Real.log ((μ.map Xs).real {x}) ∂(μ.map Yo)
        = (μ.map Xs).real {x} * Real.log ((μ.map Xs).real {x}) := by
    intro x
    rw [integral_mul_const, integral_condDistrib_real_singleton_eq μ Xs Yo hXs hYo x]
  simp_rw [h_second_term_each]
  -- (8) Combine: -condEntropy - (-entropy) = entropy - condEntropy.
  show -∫ y, ∑ x : X, Real.negMulLog ((condDistrib Xs Yo μ y).real {x}) ∂(μ.map Yo)
      - ∑ x : X, (μ.map Xs).real {x} * Real.log ((μ.map Xs).real {x})
    = entropy μ Xs - InformationTheory.MeasureFano.condEntropy μ Xs Yo
  unfold entropy InformationTheory.MeasureFano.condEntropy
  have h_entropy_term : ∑ x : X, (μ.map Xs).real {x} * Real.log ((μ.map Xs).real {x})
      = -∑ x : X, Real.negMulLog ((μ.map Xs).real {x}) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Real.negMulLog]; ring
  rw [h_entropy_term]
  ring

omit [DecidableEq X] in
/-- For a finite-alphabet source `X`, `(mutualInfo μ Xs Yo).toReal = entropy μ Xs - condEntropy μ Xs Yo`. -/
theorem mutualInfo_eq_entropy_sub_condEntropy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    (mutualInfo μ Xs Yo).toReal
      = entropy μ Xs - InformationTheory.MeasureFano.condEntropy μ Xs Yo := by
  classical
  unfold mutualInfo
  exact klDiv_joint_prod_marginals_toReal μ Xs Yo hXs hYo

end InformationTheory.Shannon
