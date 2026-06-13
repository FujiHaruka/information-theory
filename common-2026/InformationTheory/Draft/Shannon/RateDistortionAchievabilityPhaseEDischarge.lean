import InformationTheory.Meta.EntryPoint
import InformationTheory.Draft.Shannon.RateDistortionAchievabilityPhaseE
import InformationTheory.Shannon.IIDProductInput.Joint
import InformationTheory.Shannon.ChannelCoding.ShannonTheorem

/-!
# Rate-distortion achievability — partial discharge of the witness form

The witness form of the rate-distortion achievability theorem carries the ambient i.i.d.
construction (`μ, Xs, Ys`) and several entropy / distortion-bridge hypotheses as
pass-throughs. This file internally discharges those pass-throughs by instantiating the
ambient with `iidAmbientJointMeasure (pmfToMeasure qStar)`, where `qStar` is a feasible
joint pmf. The only remaining external hypothesis is the codebook-averaged random-coding
failure sequence, which requires strong-typicality machinery beyond the weak (entropy-only)
typicality available here.

## What is discharged here

* `μ := iidAmbientJointMeasure (pmfToMeasure qStar)` — i.i.d. ambient.
* `Xs := iidXs`, `Ys := iidYs` — coordinate projections.
* Measurability of `Xs i`, `Ys i` via `measurable_iidXs`, `measurable_iidYs`.
* `IsProbabilityMeasure (μ.map (Xs 0))`, similarly for `Ys 0`, via the marginal
  identities and `pmfToMeasure_isProbabilityMeasure`.
* `expectedJointDistortion μ (Xs 0) (Ys 0) d = expectedDistortionPmf d qStar`
  via the dirac/atom decomposition of `pmfToMeasure`.
* Marginal-source identity: `μ.map (Xs 0) = pmfToMeasure (marginalFst qStar)`.

## What is *not* discharged here

* `h_codebook_avg_failure`: requires strong typicality (joint type ~ q*) to
  bound the per-codebook conditional failure probability via the product law.
  Weak (entropy-only) typicality cannot give an exponential decay here; left as
  an external hypothesis on a `failure_seq → 0` sequence.
-/

namespace InformationTheory.Shannon

open Filter Topology MeasureTheory ProbabilityTheory InformationTheory
open InformationTheory.Shannon.ChannelCoding
  (iidXs iidYs measurable_iidXs measurable_iidYs jointSequence
    pmfToMeasure pmfToMeasure_apply_singleton pmfToMeasure_isProbabilityMeasure
    pmfToMeasure_real_singleton
    Codebook codebookMeasure jointlyTypicalSet)
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {α β : Type*}
  [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ## `pmfToMeasure` marginal identities -/

/-- `(pmfToMeasure q).map Prod.fst .real {a} = marginalFst q a` for any joint pmf
`q : α × β → ℝ` with `q ∈ stdSimplex ℝ (α × β)`. -/
lemma pmfToMeasure_map_fst_real_singleton
    {q : α × β → ℝ} (hq : q ∈ stdSimplex ℝ (α × β)) (a : α) :
    ((pmfToMeasure (α := α × β) q).map Prod.fst).real {a} = marginalFst q a := by
  haveI : IsProbabilityMeasure (pmfToMeasure (α := α × β) q) :=
    pmfToMeasure_isProbabilityMeasure hq
  -- (μ.map Prod.fst) {a} = μ (Prod.fst ⁻¹' {a}) = μ ({a} ×ˢ univ)
  have h_pre : (Prod.fst ⁻¹' ({a} : Set α) : Set (α × β))
      = ⋃ b ∈ (Finset.univ : Finset β), ({(a, b)} : Set (α × β)) := by
    ext ⟨x, y⟩
    constructor
    · intro hx
      have : x = a := hx
      subst this
      refine Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨b, hb⟩
      rcases Set.mem_iUnion.mp hb with ⟨_, hb'⟩
      simp only [Set.mem_singleton_iff] at hb'
      simp [Set.mem_preimage, hb']
  have h_map : ((pmfToMeasure (α := α × β) q).map Prod.fst).real {a}
      = (pmfToMeasure (α := α × β) q).real (Prod.fst ⁻¹' {a}) :=
    map_measureReal_apply measurable_fst (MeasurableSet.singleton a)
  rw [h_map, h_pre]
  have h_disj : (↑(Finset.univ : Finset β) : Set β).PairwiseDisjoint
      (fun b => ({(a, b)} : Set (α × β))) := by
    intro b₁ _ b₂ _ hb s hs1 hs2 p hp
    have hp1 := hs1 hp
    have hp2 := hs2 hp
    simp only [Set.mem_singleton_iff] at hp1 hp2
    have heq : (a, b₁) = (a, b₂) := hp1.symm.trans hp2
    exact (hb (Prod.mk.injEq _ _ _ _ |>.mp heq).2).elim
  have h_meas : ∀ b ∈ (Finset.univ : Finset β),
      MeasurableSet ({(a, b)} : Set (α × β)) := fun b _ => measurableSet_singleton _
  rw [measureReal_biUnion_finset h_disj h_meas]
  simp only [marginalFst]
  refine Finset.sum_congr rfl ?_
  intro b _
  exact pmfToMeasure_real_singleton hq (a, b)

/-- Symmetric: `(pmfToMeasure q).map Prod.snd .real {b} = marginalSnd q b`. -/
lemma pmfToMeasure_map_snd_real_singleton
    {q : α × β → ℝ} (hq : q ∈ stdSimplex ℝ (α × β)) (b : β) :
    ((pmfToMeasure (α := α × β) q).map Prod.snd).real {b} = marginalSnd q b := by
  haveI : IsProbabilityMeasure (pmfToMeasure (α := α × β) q) :=
    pmfToMeasure_isProbabilityMeasure hq
  have h_pre : (Prod.snd ⁻¹' ({b} : Set β) : Set (α × β))
      = ⋃ a ∈ (Finset.univ : Finset α), ({(a, b)} : Set (α × β)) := by
    ext ⟨x, y⟩
    constructor
    · intro hy
      have : y = b := hy
      subst this
      refine Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    · intro hy
      rcases Set.mem_iUnion.mp hy with ⟨a, ha⟩
      rcases Set.mem_iUnion.mp ha with ⟨_, ha'⟩
      simp only [Set.mem_singleton_iff] at ha'
      simp [Set.mem_preimage, ha']
  have h_map : ((pmfToMeasure (α := α × β) q).map Prod.snd).real {b}
      = (pmfToMeasure (α := α × β) q).real (Prod.snd ⁻¹' {b}) :=
    map_measureReal_apply measurable_snd (MeasurableSet.singleton b)
  rw [h_map, h_pre]
  have h_disj : (↑(Finset.univ : Finset α) : Set α).PairwiseDisjoint
      (fun a => ({(a, b)} : Set (α × β))) := by
    intro a₁ _ a₂ _ ha s hs1 hs2 p hp
    have hp1 := hs1 hp
    have hp2 := hs2 hp
    simp only [Set.mem_singleton_iff] at hp1 hp2
    have heq : (a₁, b) = (a₂, b) := hp1.symm.trans hp2
    exact (ha (Prod.mk.injEq _ _ _ _ |>.mp heq).1).elim
  have h_meas : ∀ a ∈ (Finset.univ : Finset α),
      MeasurableSet ({(a, b)} : Set (α × β)) := fun a _ => measurableSet_singleton _
  rw [measureReal_biUnion_finset h_disj h_meas]
  simp only [marginalSnd]
  refine Finset.sum_congr rfl ?_
  intro a _
  exact pmfToMeasure_real_singleton hq (a, b)

/-! ## Positivity of joint pmf carries to `pmfToMeasure` singletons -/

/-- If every `qStar p > 0`, then `(pmfToMeasure qStar).real {p} > 0`. -/
@[entry_point]
lemma pmfToMeasure_real_singleton_pos
    {q : α × β → ℝ} (hq : q ∈ stdSimplex ℝ (α × β))
    (hq_pos : ∀ p : α × β, 0 < q p) (p : α × β) :
    0 < (pmfToMeasure (α := α × β) q).real {p} := by
  rw [pmfToMeasure_real_singleton hq]
  exact hq_pos p

/-! ## Ambient setup from a feasible joint pmf

The remaining setup builds the i.i.d. ambient `(μ, Xs, Ys)` consumed by the
witness form. We use `iidAmbientJointMeasure (pmfToMeasure qStar)` with the
coordinate projections `iidXs`, `iidYs`. -/

/-- Ambient i.i.d. measure built from `qStar` lifted to a measure. -/
noncomputable def rdAmbient (qStar : α × β → ℝ) : Measure (ℕ → α × β) :=
  iidAmbientJointMeasure (pmfToMeasure (α := α × β) qStar)

lemma rdAmbient_isProbabilityMeasure
    (qStar : α × β → ℝ) (hq : qStar ∈ stdSimplex ℝ (α × β)) :
    IsProbabilityMeasure (rdAmbient qStar) := by
  haveI : IsProbabilityMeasure (pmfToMeasure (α := α × β) qStar) :=
    pmfToMeasure_isProbabilityMeasure hq
  unfold rdAmbient
  infer_instance

/-- The `iidXs 0` marginal of `rdAmbient qStar` is `(pmfToMeasure qStar).map Prod.fst`. -/
lemma rdAmbient_map_iidXs
    (qStar : α × β → ℝ) (hq : qStar ∈ stdSimplex ℝ (α × β)) :
    (rdAmbient qStar).map (iidXs (α := α) (β := β) 0)
      = (pmfToMeasure (α := α × β) qStar).map Prod.fst := by
  haveI : IsProbabilityMeasure (pmfToMeasure (α := α × β) qStar) :=
    pmfToMeasure_isProbabilityMeasure hq
  exact iidAmbientJoint_map_iidXs (pmfToMeasure (α := α × β) qStar) 0

/-- The `iidYs 0` marginal of `rdAmbient qStar` is `(pmfToMeasure qStar).map Prod.snd`. -/
lemma rdAmbient_map_iidYs
    (qStar : α × β → ℝ) (hq : qStar ∈ stdSimplex ℝ (α × β)) :
    (rdAmbient qStar).map (iidYs (α := α) (β := β) 0)
      = (pmfToMeasure (α := α × β) qStar).map Prod.snd := by
  haveI : IsProbabilityMeasure (pmfToMeasure (α := α × β) qStar) :=
    pmfToMeasure_isProbabilityMeasure hq
  exact iidAmbientJoint_map_iidYs (pmfToMeasure (α := α × β) qStar) 0

/-- The joint sequence marginal of `rdAmbient qStar` is `pmfToMeasure qStar`. -/
lemma rdAmbient_map_jointSequence
    (qStar : α × β → ℝ) (hq : qStar ∈ stdSimplex ℝ (α × β)) :
    (rdAmbient qStar).map (jointSequence (α := α) (β := β) iidXs iidYs 0)
      = pmfToMeasure (α := α × β) qStar := by
  haveI : IsProbabilityMeasure (pmfToMeasure (α := α × β) qStar) :=
    pmfToMeasure_isProbabilityMeasure hq
  exact iidAmbientJoint_map_jointSequence (pmfToMeasure (α := α × β) qStar) 0

lemma rdAmbient_iidXs_isProbabilityMeasure
    (qStar : α × β → ℝ) (hq : qStar ∈ stdSimplex ℝ (α × β)) :
    IsProbabilityMeasure ((rdAmbient qStar).map (iidXs (α := α) (β := β) 0)) := by
  rw [rdAmbient_map_iidXs qStar hq]
  haveI : IsProbabilityMeasure (pmfToMeasure (α := α × β) qStar) :=
    pmfToMeasure_isProbabilityMeasure hq
  exact MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable

lemma rdAmbient_iidYs_isProbabilityMeasure
    (qStar : α × β → ℝ) (hq : qStar ∈ stdSimplex ℝ (α × β)) :
    IsProbabilityMeasure ((rdAmbient qStar).map (iidYs (α := α) (β := β) 0)) := by
  rw [rdAmbient_map_iidYs qStar hq]
  haveI : IsProbabilityMeasure (pmfToMeasure (α := α × β) qStar) :=
    pmfToMeasure_isProbabilityMeasure hq
  exact MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

/-! ## Expected distortion bridge

`expectedJointDistortion (rdAmbient qStar) (iidXs 0) (iidYs 0) d = expectedDistortionPmf d qStar`. -/

/-- The expected joint distortion under `rdAmbient qStar` equals the pmf-form
`expectedDistortionPmf d qStar`. Proved by unfolding the integral over the
i.i.d. ambient, pushing forward to `pmfToMeasure qStar`, and decomposing the
dirac sum. -/
lemma expectedJointDistortion_rdAmbient
    (qStar : α × β → ℝ) (hqStar_simp : qStar ∈ stdSimplex ℝ (α × β))
    (d : DistortionFn α β) :
    expectedJointDistortion (rdAmbient qStar) (iidXs (α := α) (β := β) 0)
        (iidYs (α := α) (β := β) 0) d
      = expectedDistortionPmf d qStar := by
  haveI : IsProbabilityMeasure (pmfToMeasure (α := α × β) qStar) :=
    pmfToMeasure_isProbabilityMeasure hqStar_simp
  -- Rewrite expectedJointDistortion as the integral of `d ∘ Prod.mk` after
  -- pushforward to the joint coordinate at index 0.
  unfold expectedJointDistortion
  -- ∫ ω, d(X ω, Y ω) ∂μ = ∫ p, d p.1 p.2 ∂(μ.map (jointSequence ... 0))
  -- where `jointSequence iidXs iidYs 0 ω = (iidXs 0 ω, iidYs 0 ω) = ω 0`.
  have h_meas_d : Measurable (fun p : α × β => ((d p.1 p.2 : NNReal) : ℝ)) := by
    -- α × β is discrete; everything is measurable.
    refine Measurable.coe_nnreal_real ?_
    exact measurable_of_countable _
  have h_meas_joint :
      Measurable (jointSequence (α := α) (β := β) iidXs iidYs 0) :=
    (measurable_iidXs 0).prodMk (measurable_iidYs 0)
  have h_int_eq :
      ∫ ω, ((d (iidXs (α := α) (β := β) 0 ω)
              (iidYs (α := α) (β := β) 0 ω) : NNReal) : ℝ) ∂ rdAmbient qStar
        = ∫ p : α × β, ((d p.1 p.2 : NNReal) : ℝ)
            ∂ ((rdAmbient qStar).map
                (jointSequence (α := α) (β := β) iidXs iidYs 0)) := by
    -- Goal LHS = ∫ ω, f (φ ω) ∂μ where f p = d p.1 p.2 and φ = jointSequence 0.
    -- Use (integral_map).symm: ∫ y, f y ∂(μ.map φ) = ∫ x, f (φ x) ∂μ.
    symm
    exact MeasureTheory.integral_map h_meas_joint.aemeasurable
          h_meas_d.aestronglyMeasurable
  rw [h_int_eq, rdAmbient_map_jointSequence qStar hqStar_simp]
  -- Now: ∫ p, d p.1 p.2 ∂(pmfToMeasure qStar) = ∑ p, qStar p * d p.
  unfold pmfToMeasure
  -- Each `(ofReal (q p) • δ_p)` is a finite (in fact prob-mass times Dirac) measure;
  -- the integrand is integrable against it.
  have h_integrable : ∀ a ∈ (Finset.univ : Finset (α × β)),
      MeasureTheory.Integrable (fun p : α × β => ((d p.1 p.2 : NNReal) : ℝ))
        (ENNReal.ofReal (qStar a) • Measure.dirac a) := by
    intro a _
    haveI : IsFiniteMeasure
        ((ENNReal.ofReal (qStar a) : ℝ≥0∞) • (Measure.dirac a : Measure (α × β))) :=
      Measure.smul_finite (Measure.dirac a) ENNReal.ofReal_ne_top
    -- A.e.s.m. + finite measure → integrable.
    exact MeasureTheory.Integrable.of_finite
  rw [MeasureTheory.integral_finsetSum_measure h_integrable]
  -- After distributing: ∑ p, ∫ x, d x ∂(ofReal (qStar p) • δ_p) = ∑ p, ofReal(qStar p) * d p
  simp_rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac]
  unfold expectedDistortionPmf
  -- ∑ a, ∑ b, qStar (a,b) * d (a,b) = ∑ p ∈ univ_{α × β}, qStar p * d p
  rw [← Finset.sum_product']
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [smul_eq_mul, ENNReal.toReal_ofReal (hqStar_simp.1 p)]

end InformationTheory.Shannon
