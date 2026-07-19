import InformationTheory.Shannon.WynerZiv.Achievability.Covering

/-!
# Wyner–Ziv achievability — inner concentration sub-lemmas for the Markov-lemma covering bound
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open Real Set
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {α β γ U : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Fintype γ] [DecidableEq γ] [Nonempty γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
  [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]

/-! ### Inner concentration — band sub-lemmas

The Markov-lemma concentration `wz_covering_markov_concentration` is assembled from six band
sub-lemmas. The covering-acceptance failure event unfolds — via `mem_jointlyTypicalSet_iff` —
into a conjunction of three independent entropy-band typicalities (U-band ∧ Y-band ∧ joint-band),
so its De Morgan complement is a union of three band-failures, each with an independent witness:

* `wz_covering_uMarginal_map_eq` — the covering pmf `qStar`'s `U`-marginal equals the
  side-information marginal `wzSideInfoMarginal`'s `U`-marginal (both `= P_U`); this makes the
  `U`-band consistent between the two ambients.
* `wz_covering_success_subset_uTypical` — covering-success ⊆ {chosen word `U`-typical in the
  side-information ambient}; the covering `U`-band plus the marginal identity makes `U`-typicality
  identical in the two ambients (mass-0 set inclusion, no threshold `N`).
* `wz_covering_src_yProj_eq_pi` — the `Y`-projection of the source product measure is the product
  of the source `Y`-law (`Measure.pi_map_pi`).
* `wz_covering_yBand_aep` — the source-measure `Y`-band failure has mass `≤ tol/4` for `n` large
  (a one-dimensional AEP on the iid side-information sequence, independent of the code).
* `wz_covering_jointBand_concentration` — the hard kernel: covering-success ∩ {joint `(U,Y)`-band
  failure} has mass `≤ tol/4`. The correlated-joint conditional-typicality concentration (the
  Markov lemma); `U = c.decoder (c.encoder x)` is a function of the whole `x`-block, so `(U_i, Y_i)`
  is neither iid nor independent — a from-scratch in-project assembly absent from Mathlib.
* the assembly (the body of `wz_covering_markov_concentration`): `N := max N_Y N_J`, and a union
  bound over the three band-failures gives `0 + tol/4 + tol/4 = tol/2`.
-/

open ChannelCoding in
/-- The covering pmf `qStar`'s
`Fin k`-marginal (`iidYs 0` law of `rdAmbient qStar`) equals the side-information marginal
`wzSideInfoMarginal`'s `Fin k`-marginal (`iidXs 0` law of `rdAmbient (wzSideInfoMarginal …)`);
both are the covering-word law `P_U(u) = ∑ₓ κ'(x, u)·P_X(x)`. This aligns the `U`-band of the
covering-success set (measured in `rdAmbient qStar`) with the `U`-band of the acceptance set
(measured in the side-information ambient). -/
private lemma wz_covering_uMarginal_map_eq
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (hκ'_pos : ∀ x u, 0 < κ' x u)
    (hκ'_sum : ∀ x, ∑ u, κ' x u = 1)
    (hqStar : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)}) :
    (rdAmbient qStar).map
        (ChannelCoding.iidYs (α := {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (β := Fin k) 0)
      = (rdAmbient (wzSideInfoMarginal P_XY κ')).map
          (ChannelCoding.iidXs (α := Fin k) (β := {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) 0) := by
  classical
  obtain ⟨hne_α', -, hq_qStar_fun⟩ := wz_restrictedCoveringJoint_pos P_XY κ' hκ'_pos hκ'_sum
  haveI := hne_α'
  have hq_qStar : qStar ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k) := by
    rw [funext hqStar]; exact hq_qStar_fun
  haveI hne_prod : Nonempty ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k) :=
    Finset.univ_nonempty_iff.mp
      (Finset.nonempty_of_sum_ne_zero (by rw [hq_qStar.2]; exact one_ne_zero))
  haveI : Nonempty (Fin k) := hne_prod.map Prod.snd
  haveI hne_β' : Nonempty {y : β // 0 < ∑ x, P_XY.real {(x, y)}} :=
    wzSideInfoMarginal_subtype_nonempty P_XY
  have hq_wsm := wzSideInfoMarginal_mem_stdSimplex P_XY κ' hκ'_pos hκ'_sum
  rw [rdAmbient_map_iidYs qStar hq_qStar,
      rdAmbient_map_iidXs (wzSideInfoMarginal P_XY κ') hq_wsm]
  haveI : IsProbabilityMeasure (ChannelCoding.pmfToMeasure qStar) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure hq_qStar
  haveI : IsProbabilityMeasure (ChannelCoding.pmfToMeasure (wzSideInfoMarginal P_XY κ')) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure hq_wsm
  haveI : IsProbabilityMeasure ((ChannelCoding.pmfToMeasure qStar).map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  haveI : IsProbabilityMeasure
      ((ChannelCoding.pmfToMeasure (wzSideInfoMarginal P_XY κ')).map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  apply Measure.ext_of_singleton
  intro u
  -- The two `U`-marginal singletons agree as reals, both `= ∑ₓ κ'(x, u)·P_X(x)`.
  have hMS : marginalSnd qStar u = ∑ x, κ' x u * ∑ y, P_XY.real {(x, y)} := by
    simp only [marginalSnd]
    rw [Finset.sum_congr rfl (fun x' _ ↦ hqStar (x', u))]
    letI : DecidablePred (fun x : α ↦ 0 < ∑ y, P_XY.real {(x, y)}) := Classical.decPred _
    rw [← Finset.sum_subtype (Finset.univ.filter (fun x : α ↦ 0 < ∑ y, P_XY.real {(x, y)}))
        (fun x ↦ by simp) (fun x ↦ κ' x u * ∑ y, P_XY.real {(x, y)})]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro x _ hx
    rw [Finset.mem_filter] at hx
    push_neg at hx
    have hz : ∑ y, P_XY.real {(x, y)} = 0 :=
      le_antisymm (hx (Finset.mem_univ x)) (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg)
    rw [hz, mul_zero]
  have hMF : marginalFst (wzSideInfoMarginal P_XY κ') u
      = ∑ x, κ' x u * ∑ y, P_XY.real {(x, y)} := by
    simp only [marginalFst, wzSideInfoMarginal]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ ↦ ?_)
    rw [← Finset.mul_sum]
    congr 1
    letI : DecidablePred (fun y : β ↦ 0 < ∑ x, P_XY.real {(x, y)}) := Classical.decPred _
    rw [← Finset.sum_subtype (Finset.univ.filter (fun y : β ↦ 0 < ∑ x, P_XY.real {(x, y)}))
        (fun y ↦ by simp) (fun y ↦ P_XY.real {(x, y)})]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro y _ hy
    rw [Finset.mem_filter] at hy
    push_neg at hy
    have hz : ∑ x', P_XY.real {(x', y)} = 0 :=
      le_antisymm (hy (Finset.mem_univ y)) (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ measureReal_nonneg)).mp hz x
      (Finset.mem_univ x)
  have hreal : ((ChannelCoding.pmfToMeasure qStar).map Prod.snd).real {u}
      = ((ChannelCoding.pmfToMeasure (wzSideInfoMarginal P_XY κ')).map Prod.fst).real {u} := by
    rw [pmfToMeasure_map_snd_real_singleton hq_qStar u,
        pmfToMeasure_map_fst_real_singleton hq_wsm u, hMS, hMF]
  have hL := measure_ne_top ((ChannelCoding.pmfToMeasure qStar).map Prod.snd) {u}
  have hR := measure_ne_top
    ((ChannelCoding.pmfToMeasure (wzSideInfoMarginal P_XY κ')).map Prod.fst) {u}
  rw [← ENNReal.ofReal_toReal hL, ← ENNReal.ofReal_toReal hR]
  exact congrArg ENNReal.ofReal hreal

open ChannelCoding in
/-- If the
chosen covering word `c.decoder (c.encoder x)` typically covers `x` (covering-success in
`rdAmbient qStar`), then it is `U`-typical in the side-information ambient. The covering-success
`U`-band bands the word against `qStar`'s `U`-marginal; L0 makes that identical to the
side-information ambient's `U`-marginal, so the two `U`-typical sets coincide. Pure set
inclusion (no threshold `N`). -/
lemma wz_covering_success_subset_uTypical
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (hκ'_pos : ∀ x u, 0 < κ' x u)
    (hκ'_sum : ∀ x, ∑ u, κ' x u = 1)
    (hqStar : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
    (ε : ℝ) (n : ℕ) (M : ℕ)
    (c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k)) :
    { p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β |
        (fun j ↦ (p j).1, c.decoder (c.encoder (fun j ↦ (p j).1)))
          ∈ ChannelCoding.jointlyTypicalSet (rdAmbient qStar)
              ChannelCoding.iidXs ChannelCoding.iidYs n ε }
      ⊆ { p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β |
          c.decoder (c.encoder (fun j ↦ (p j).1))
            ∈ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ')) ChannelCoding.iidXs n ε } := by
  have hmap := wz_covering_uMarginal_map_eq P_XY κ' qStar hκ'_pos hκ'_sum hqStar
  -- `pmfLog` and `entropy` of the two `U`-marginals coincide (L0).
  have hpmf : pmfLog (rdAmbient qStar)
        (ChannelCoding.iidYs (α := {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (β := Fin k))
      = pmfLog (rdAmbient (wzSideInfoMarginal P_XY κ'))
          (ChannelCoding.iidXs (α := Fin k) (β := {y : β // 0 < ∑ x, P_XY.real {(x, y)}})) := by
    funext u'
    simp only [pmfLog]
    rw [hmap]
  have hent : entropy (rdAmbient qStar)
        (ChannelCoding.iidYs (α := {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (β := Fin k) 0)
      = entropy (rdAmbient (wzSideInfoMarginal P_XY κ'))
          (ChannelCoding.iidXs (α := Fin k) (β := {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) 0) := by
    simp only [entropy]
    rw [hmap]
  have hset : typicalSet (rdAmbient qStar)
        (ChannelCoding.iidYs (α := {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (β := Fin k)) n ε
      = typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
          (ChannelCoding.iidXs (α := Fin k) (β := {y : β // 0 < ∑ x, P_XY.real {(x, y)}})) n ε := by
    unfold typicalSet
    rw [hpmf, hent]
  intro p hp
  rw [Set.mem_setOf_eq, ChannelCoding.mem_jointlyTypicalSet_iff] at hp
  obtain ⟨_, hu, _⟩ := hp
  rw [Set.mem_setOf_eq, ← hset]
  exact hu

open ChannelCoding in
/-- Pushing the source product measure
`Measure.pi (pmfToMeasure P_XY{(x'.1, y)})` along the coordinatewise `Y`-projection gives the
product of the source `Y`-law `(pmfToMeasure P_XY{(x'.1, y)}).map Prod.snd`. Direct
`Measure.pi_map_pi`. -/
private lemma wz_covering_src_yProj_eq_pi
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY] (n : ℕ) :
    (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
          P_XY.real {(p.1.1, p.2)}))).map (fun p (i : Fin n) ↦ (p i).2)
      = Measure.pi (fun _ : Fin n ↦ (ChannelCoding.pmfToMeasure
          (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
            P_XY.real {(p.1.1, p.2)})).map Prod.snd) := by
  haveI : IsProbabilityMeasure (ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure (wz_QXY_mem_stdSimplex P_XY)
  haveI : IsProbabilityMeasure ((ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})).map
        Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact Measure.pi_map_pi (hμ := fun _ ↦ inferInstance) (fun _ ↦ measurable_snd.aemeasurable)

open ChannelCoding in
/-- For `n` large the source-measure
mass of the `Y`-band failure — the side-information block `y` is not typical in the
side-information ambient — is at most `tol/4`. A one-dimensional AEP on the iid `Y`-sequence
(law `P_Y = ∑ₓ P_XY{(x, ·)}`), independent of the code `c` and of covering-success. Transports
`typicalSet_prob_ge_of_rate` (the ℕ-process AEP) onto the source product measure via the
`β'`↔`β` coercion, mirroring the `wz_source_codeword_sideInfo_mass_le` transport. -/
lemma wz_covering_yBand_aep
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (hκ'_pos : ∀ x u, 0 < κ' x u)
    (hκ'_sum : ∀ x, ∑ u, κ' x u = 1)
    (ε : ℝ) (hε : 0 < ε) (tol : ℝ) (htol : 0 < tol) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
          (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
            P_XY.real {(p.1.1, p.2)}))).real
        { p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β |
            (fun i ↦ (p i).2) ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
                (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                  ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)) n ε }
        ≤ tol / 4 := by
  classical
  -- Nonempty instances for `α'`, `Fin k`, `β'`.
  obtain ⟨hne_α', -, hstd_qlike⟩ := wz_restrictedCoveringJoint_pos P_XY κ' hκ'_pos hκ'_sum
  haveI := hne_α'
  haveI hne_prod : Nonempty ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k) :=
    Finset.univ_nonempty_iff.mp
      (Finset.nonempty_of_sum_ne_zero (by rw [hstd_qlike.2]; exact one_ne_zero))
  haveI : Nonempty (Fin k) := hne_prod.map Prod.snd
  haveI hne_βs : Nonempty {y : β // 0 < ∑ x, P_XY.real {(x, y)}} :=
    wzSideInfoMarginal_subtype_nonempty P_XY
  have hq := wzSideInfoMarginal_mem_stdSimplex P_XY κ' hκ'_pos hκ'_sum
  haveI hamb_prob : IsProbabilityMeasure (rdAmbient (wzSideInfoMarginal P_XY κ')) :=
    rdAmbient_isProbabilityMeasure _ hq
  haveI hsrc_prob : IsProbabilityMeasure (ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure (wz_QXY_mem_stdSimplex P_XY)
  -- The one-dimensional AEP on the iid side-information sequence (in the `β'` ambient).
  obtain ⟨N, hN⟩ := typicalSet_prob_ge_of_rate (rdAmbient (wzSideInfoMarginal P_XY κ'))
    (ChannelCoding.iidYs (α := Fin k) (β := {y : β // 0 < ∑ x, P_XY.real {(x, y)}}))
    (fun i ↦ ChannelCoding.measurable_iidYs i)
    (fun i j hij ↦ (rdAmbient_iIndepFun_iidYs (wzSideInfoMarginal P_XY κ') hq).indepFun hij)
    (rdAmbient_identDistrib_iidYs (wzSideInfoMarginal P_XY κ') hq) hε (η := tol / 4) (by linarith)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hAEP := hN n hn
  -- Coercion / transport building blocks (mirror `wz_source_codeword_sideInfo_mass_le`).
  have hval_inj : Function.Injective
      (Subtype.val : {y : β // 0 < ∑ x, P_XY.real {(x, y)}} → β) := Subtype.val_injective
  have hval_meas : Measurable
      (Subtype.val : {y : β // 0 < ∑ x, P_XY.real {(x, y)}} → β) := measurable_subtype_coe
  haveI : IsProbabilityMeasure ((ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})).map
      Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  haveI : IsProbabilityMeasure ((rdAmbient (wzSideInfoMarginal P_XY κ')).map
      (ChannelCoding.iidYs (α := Fin k) 0)) :=
    Measure.isProbabilityMeasure_map (ChannelCoding.measurable_iidYs 0).aemeasurable
  haveI : IsProbabilityMeasure (((rdAmbient (wzSideInfoMarginal P_XY κ')).map
      (ChannelCoding.iidYs (α := Fin k) 0)).map Subtype.val) :=
    Measure.isProbabilityMeasure_map hval_meas.aemeasurable
  -- `pmfLog` / `entropy` invariance of the `Y`-marginal under the `β'`↪`β` coercion.
  have hpmfYeq : ∀ y' : {y : β // 0 < ∑ x, P_XY.real {(x, y)}},
      pmfLog (rdAmbient (wzSideInfoMarginal P_XY κ'))
          (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
            ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)) ((y' : β))
        = pmfLog (rdAmbient (wzSideInfoMarginal P_XY κ'))
            (ChannelCoding.iidYs (α := Fin k)) y' := by
    intro y'
    simp only [pmfLog]
    rw [wz_map_injective_real_singleton (rdAmbient (wzSideInfoMarginal P_XY κ'))
        (ChannelCoding.iidYs (α := Fin k) 0) (ChannelCoding.measurable_iidYs 0)
        Subtype.val hval_inj hval_meas y']
  have hentYeq : entropy (rdAmbient (wzSideInfoMarginal P_XY κ'))
      (fun ω ↦
        ((ChannelCoding.iidYs (α := Fin k) 0 ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))
        = entropy (rdAmbient (wzSideInfoMarginal P_XY κ')) (ChannelCoding.iidYs (α := Fin k) 0) :=
    wz_entropy_map_injective (rdAmbient (wzSideInfoMarginal P_XY κ'))
      (ChannelCoding.iidYs (α := Fin k) 0) (ChannelCoding.measurable_iidYs 0)
      Subtype.val hval_inj hval_meas
  have htypY : ∀ z : Fin n → {y : β // 0 < ∑ x, P_XY.real {(x, y)}},
      ((fun i ↦ ((z i : β))) ∈ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
          (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
            ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)) n ε)
        ↔ (z ∈ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
            (ChannelCoding.iidYs (α := Fin k)) n ε) := by
    intro z
    rw [mem_typicalSet_iff, mem_typicalSet_iff]
    have hnum : (∑ i : Fin n, pmfLog (rdAmbient (wzSideInfoMarginal P_XY κ'))
          (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
            ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)) ((z i : β)))
        = ∑ i : Fin n, pmfLog (rdAmbient (wzSideInfoMarginal P_XY κ'))
            (ChannelCoding.iidYs (α := Fin k)) (z i) :=
      Finset.sum_congr rfl (fun i _ ↦ hpmfYeq (z i))
    simp only [hnum, hentYeq]
  -- Measure transport: the source `Y`-projection law is the `β`-image of the ambient `Y`-jointRV.
  have hmeaseq : (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))).map
        (fun p (i : Fin n) ↦ (p i).2)
      = ((rdAmbient (wzSideInfoMarginal P_XY κ')).map
          (jointRV (ChannelCoding.iidYs (α := Fin k)) n)).map
          (fun (z : Fin n → {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) i ↦ ((z i : β))) := by
    rw [wz_ambient_jointRV_iidYs_eq_pi P_XY κ' hκ'_pos hκ'_sum n,
        Measure.pi_map_pi (hμ := fun _ ↦ inferInstance) (fun _ ↦ hval_meas.aemeasurable),
        Measure.pi_map_pi (hμ := fun _ ↦ inferInstance) (fun _ ↦ measurable_snd.aemeasurable)]
    refine congrArg Measure.pi (funext (fun _ ↦ ?_))
    exact wz_source_snd_eq_ambient_snd_map P_XY κ' hκ'_pos hκ'_sum
  have hYproj_meas : Measurable (fun p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
      fun i ↦ (p i).2) :=
    measurable_pi_lambda _ (fun i ↦ measurable_snd.comp (measurable_pi_apply i))
  have hΦ_meas : Measurable (fun z : Fin n → {y : β // 0 < ∑ x, P_XY.real {(x, y)}} ↦
      fun i ↦ ((z i : β))) :=
    measurable_pi_lambda _ (fun i ↦ hval_meas.comp (measurable_pi_apply i))
  have hjrv_meas : Measurable (jointRV (ChannelCoding.iidYs (α := Fin k)
      (β := {y : β // 0 < ∑ x, P_XY.real {(x, y)}})) n) :=
    measurable_jointRV _ (fun i ↦ ChannelCoding.measurable_iidYs i) n
  -- The atypical-`Y` preimage relabels along the coercion to the ambient atypical set.
  have hΦS : (fun (z : Fin n → {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) i ↦ ((z i : β))) ⁻¹'
        {yb : Fin n → β | yb ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
            (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
              ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)) n ε}
      = {z : Fin n → {y : β // 0 < ∑ x, P_XY.real {(x, y)}} |
          z ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
            (ChannelCoding.iidYs (α := Fin k)) n ε} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    exact not_congr (htypY z)
  -- Transport the source-measure atypical `Y`-band mass onto the ℕ-process atypical set.
  rw [show { p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β |
        (fun i ↦ (p i).2) ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
            (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
              ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)) n ε }
      = (fun p (i : Fin n) ↦ (p i).2) ⁻¹' {yb : Fin n → β |
          yb ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
            (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)) n ε}
        from rfl,
      ← map_measureReal_apply hYproj_meas (Set.toFinite _).measurableSet,
      hmeaseq,
      map_measureReal_apply hΦ_meas (Set.toFinite _).measurableSet,
      hΦS,
      map_measureReal_apply hjrv_meas (Set.toFinite _).measurableSet,
      Set.preimage_setOf_eq]
  -- Complement of the AEP typical set: atypical mass `= 1 − typical mass ≤ tol/4`.
  show (rdAmbient (wzSideInfoMarginal P_XY κ')).real
      {ω | jointRV (ChannelCoding.iidYs (α := Fin k)) n ω
          ∈ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
              (ChannelCoding.iidYs (α := Fin k)) n ε}ᶜ ≤ tol / 4
  rw [measureReal_compl (s := {ω | jointRV (ChannelCoding.iidYs (α := Fin k)) n ω
        ∈ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
            (ChannelCoding.iidYs (α := Fin k)) n ε})
      (hjrv_meas (measurableSet_typicalSet _ _ _ _))]
  have huniv : (rdAmbient (wzSideInfoMarginal P_XY κ')).real Set.univ = 1 := by
    rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  have hbridge : (rdAmbient (wzSideInfoMarginal P_XY κ')).real
      {ω | jointRV (ChannelCoding.iidYs (α := Fin k)) n ω
          ∈ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
              (ChannelCoding.iidYs (α := Fin k)) n ε}
      = ((rdAmbient (wzSideInfoMarginal P_XY κ'))
          {ω | jointRV (ChannelCoding.iidYs (α := Fin k)) n ω
            ∈ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
                (ChannelCoding.iidYs (α := Fin k)) n ε}).toReal := rfl
  rw [huniv]
  linarith [hAEP, hbridge]

open ChannelCoding in
/-- For `n` large the
source-measure mass of the `(X,Y)`-joint-atypical set — the block `(x_i,y_i) = p_i` is not
typical in the `(X,Y)`-joint ambient `rdAmbient Src` (`Src(x',y) = P_XY{(x'.1,y)}`, the SRC
per-coordinate law) — is at most `tol/8`. The `(x_i,y_i)` pairs are iid `~ Src` under SRC, so
this is a direct AEP (`typicalSet_prob_ge_of_rate`) transported by
`rdAmbient_map_jointRV_jointSequence_eq_pi`. Independent of the code `c`. -/
lemma wz_covering_xyBand_aep
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (ε : ℝ) (hε : 0 < ε) (tol : ℝ) (htol : 0 < tol) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
          (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))).real
        (typicalSet
          (rdAmbient
            (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
          (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n ε)ᶜ
        ≤ tol / 8 := by
  classical
  have hq_Src := wz_QXY_mem_stdSimplex P_XY
  haveI hne_α' : Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}} := by
    have hne : Nonempty ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
      Finset.univ_nonempty_iff.mp
        (Finset.nonempty_of_sum_ne_zero (by rw [hq_Src.2]; exact one_ne_zero))
    exact hne.map Prod.fst
  haveI : IsProbabilityMeasure (rdAmbient
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})) :=
    rdAmbient_isProbabilityMeasure _ hq_Src
  obtain ⟨N, hN⟩ := typicalSet_prob_ge_of_rate
    (rdAmbient (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
    (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs)
    (fun i ↦ ChannelCoding.measurable_jointSequence _ _
      (fun i ↦ ChannelCoding.measurable_iidXs i) (fun i ↦ ChannelCoding.measurable_iidYs i) i)
    (fun i j hij ↦ (rdAmbient_iIndepFun_jointSequence _ hq_Src).indepFun hij)
    (rdAmbient_identDistrib_jointSequence _ hq_Src) hε (η := tol / 8) (by linarith)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hAEP := hN n hn
  have hjrv_meas : Measurable (jointRV
      (ChannelCoding.jointSequence (α := {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (β := β)
        ChannelCoding.iidXs ChannelCoding.iidYs) n) :=
    measurable_jointRV _ (fun i ↦ ChannelCoding.measurable_jointSequence _ _
      (fun i ↦ ChannelCoding.measurable_iidXs i) (fun i ↦ ChannelCoding.measurable_iidYs i) i) n
  have huniv : (rdAmbient
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})).real
      Set.univ = 1 := by rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  rw [show (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
          (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})))
        = (rdAmbient
            (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})).map
            (jointRV (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n)
      from (rdAmbient_map_jointRV_jointSequence_eq_pi _ hq_Src n).symm,
      map_measureReal_apply hjrv_meas (measurableSet_typicalSet _ _ _ _).compl,
      Set.preimage_compl,
      measureReal_compl (hjrv_meas (measurableSet_typicalSet _ _ _ _)), huniv]
  have hbr : (rdAmbient
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})).real
        (jointRV (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n ⁻¹'
          typicalSet (rdAmbient
            (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
            (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n ε)
      = ((rdAmbient
          (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
          {ω | jointRV (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n ω
            ∈ typicalSet (rdAmbient
                (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
                (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs)
                n ε}).toReal :=
    rfl
  linarith [hAEP, hbr]

/-- The `κ'`-marginal-weighted mean of `-log wsm`
equals the `wsm`-entropy. Division-free form: the weight of each `(x, u, ys)` is
`κ'(x, u) · P_XY{(x, ys)}` (no conditional `P(y|x)` division), so no degenerate-`x`
handling is needed. Reindexing the `x`-sum inward collapses `∑ₓ κ'(x,u)·P_XY{(x,ys)}`
to `wsm(u, ys)`, matching the entropy shape `∑ p, negMulLog (wsm p)` used by
`wz_entropy_ambient_joint`. -/
private lemma wz_wsm_negLog_mean_eq_entropy
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ) :
    ∑ x, ∑ u, ∑ ys : {y : β // 0 < ∑ x', P_XY.real {(x', y)}},
        κ' x u * P_XY.real {(x, ys.1)}
          * (- Real.log (wzSideInfoMarginal P_XY κ' (u, ys)))
      = ∑ p, Real.negMulLog (wzSideInfoMarginal P_XY κ' p) := by
  classical
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ys _ ↦ ?_
  have hw : (∑ x, κ' x u * P_XY.real {(x, ys.1)})
      = wzSideInfoMarginal P_XY κ' (u, ys) := rfl
  rw [← Finset.sum_mul, hw]
  simp only [Real.negMulLog_def]
  ring

/-- The conditional mean of `-log wsm(u, y)` under
the covering law `P_X(x) · κ'(u ∣ x) · P(y ∣ x)` equals the `wsm`-entropy
`∑ p, negMulLog (wsm p)`. Here `P_X(x) = ∑_y P_XY{(x, y)}` and `P(y ∣ x) =
P_XY{(x, y)} / P_X(x)`; the outer `P_X(x)` factor cancels the conditional denominator
(and kills the term for degenerate `x` with `P_X(x) = 0`). Derived from
`wz_wsm_negLog_mean_eq_entropy`. -/
private lemma wz_wsm_negLog_condMean_eq_entropy
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ) :
    ∑ x, ∑ u, (∑ y, P_XY.real {(x, y)}) * κ' x u
        * (∑ ys : {y : β // 0 < ∑ x', P_XY.real {(x', y)}},
            (P_XY.real {(x, ys.1)} / (∑ y, P_XY.real {(x, y)}))
              * (- Real.log (wzSideInfoMarginal P_XY κ' (u, ys))))
      = ∑ p, Real.negMulLog (wzSideInfoMarginal P_XY κ' p) := by
  classical
  rw [← wz_wsm_negLog_mean_eq_entropy P_XY κ']
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ys _ ↦ ?_
  by_cases hS : (∑ y, P_XY.real {(x, y)}) = 0
  · have hP : P_XY.real {(x, ys.1)} = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun y _ ↦ measureReal_nonneg)).mp hS ys.1
        (Finset.mem_univ _)
    rw [hS, hP]; ring
  · have hcancel : (∑ y, P_XY.real {(x, y)})
        * (P_XY.real {(x, ys.1)} / (∑ y, P_XY.real {(x, y)})) = P_XY.real {(x, ys.1)} := by
      field_simp
    calc (∑ y, P_XY.real {(x, y)}) * κ' x u
            * (P_XY.real {(x, ys.1)} / (∑ y, P_XY.real {(x, y)})
              * (- Real.log (wzSideInfoMarginal P_XY κ' (u, ys))))
          = κ' x u * ((∑ y, P_XY.real {(x, y)})
              * (P_XY.real {(x, ys.1)} / (∑ y, P_XY.real {(x, y)})))
              * (- Real.log (wzSideInfoMarginal P_XY κ' (u, ys))) := by ring
        _ = κ' x u * P_XY.real {(x, ys.1)}
              * (- Real.log (wzSideInfoMarginal P_XY κ' (u, ys))) := by rw [hcancel]

/-- The Wyner–Ziv conditional-mean kernel `g(x, u) = ∑_ys P(ys | x) · (−log wsm(u, ys))`,
where `P(ys | x) = P_XY{(x, ys)} / ∑_y P_XY{(x, y)}` is the per-letter conditional side-info
law and `wsm = wzSideInfoMarginal P_XY κ'` is the `(U, Y)`-marginal. Indexed by the
positive-`X`-marginal subtype `{x // 0 < ∑ y P_XY{(x, y)}} × Fin k`, on which the conditional
denominator is positive. This is the per-symbol statistic whose empirical mean the
strong-typicality mean-pin controls; `∑_{x,u} qStar(x, u) · g(x, u) = H(wsm)` under the
`qStar–κ'` consistency (`wz_wsm_condMean_kernel_inner_eq_entropy`). -/
private noncomputable def wzCondMeanKernel
    (P_XY : Measure (α × β)) {k : ℕ} (κ' : α → Fin k → ℝ) :
    {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ :=
  fun p ↦ ∑ ys : {y : β // 0 < ∑ x', P_XY.real {(x', y)}},
    (P_XY.real {(p.1.1, ys.1)} / ∑ y, P_XY.real {(p.1.1, y)})
      * (- Real.log (wzSideInfoMarginal P_XY κ' (p.2, ys)))

/-- The `qStar`-weighted mean of the conditional-mean kernel equals
the `wsm`-entropy: `∑_{p} qStar(p) · g(p) = H(wsm)`, where `qStar(x, u) = κ'(x, u) · P_X(x)` is
the consistent covering joint pmf on the positive-`X`-marginal subtype. Reduces to the
division-free identity `wz_wsm_negLog_mean_eq_entropy` after cancelling the conditional
denominator (positive on the subtype) and extending the `x`-sum to the full alphabet
(degenerate `x` with `P_X(x) = 0` contribute `0`). -/
private lemma wz_wsm_condMean_kernel_inner_eq_entropy
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ) :
    ∑ p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k,
        (κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)}) * wzCondMeanKernel P_XY κ' p
      = ∑ q, Real.negMulLog (wzSideInfoMarginal P_XY κ' q) := by
  classical
  -- Per-`p` cancellation of the conditional denominator: on the subtype `P_X(x) > 0`.
  have hcancel : ∀ p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k,
      (κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)}) * wzCondMeanKernel P_XY κ' p
        = ∑ ys : {y : β // 0 < ∑ x', P_XY.real {(x', y)}},
            κ' p.1.1 p.2 * P_XY.real {(p.1.1, ys.1)}
              * (- Real.log (wzSideInfoMarginal P_XY κ' (p.2, ys))) := by
    intro p
    unfold wzCondMeanKernel
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ys _ ↦ ?_
    have hpos : (∑ y, P_XY.real {(p.1.1, y)}) ≠ 0 := p.1.2.ne'
    field_simp
  simp_rw [hcancel]
  rw [Fintype.sum_prod_type]
  dsimp only
  -- Extend the `x`-sum from the positive-marginal subtype to the full alphabet
  -- (degenerate `x` with `P_X(x) = 0` contribute `0`), then apply the division-free identity.
  have hext : (∑ x' : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}, ∑ u,
        ∑ ys : {y : β // 0 < ∑ x', P_XY.real {(x', y)}},
          κ' x'.1 u * P_XY.real {(x'.1, ys.1)}
            * (- Real.log (wzSideInfoMarginal P_XY κ' (u, ys))))
      = ∑ x : α, ∑ u,
        ∑ ys : {y : β // 0 < ∑ x', P_XY.real {(x', y)}},
          κ' x u * P_XY.real {(x, ys.1)}
            * (- Real.log (wzSideInfoMarginal P_XY κ' (u, ys))) := by
    letI : DecidablePred (fun x : α ↦ 0 < ∑ y, P_XY.real {(x, y)}) := Classical.decPred _
    rw [← Finset.sum_subtype (Finset.univ.filter (fun x : α ↦ 0 < ∑ y, P_XY.real {(x, y)}))
        (fun x ↦ by simp)
        (fun x ↦ ∑ u, ∑ ys : {y : β // 0 < ∑ x', P_XY.real {(x', y)}},
          κ' x u * P_XY.real {(x, ys.1)}
            * (- Real.log (wzSideInfoMarginal P_XY κ' (u, ys))))]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro x _ hx
    rw [Finset.mem_filter] at hx
    push_neg at hx
    have hz : ∑ y, P_XY.real {(x, y)} = 0 :=
      le_antisymm (hx (Finset.mem_univ x)) (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg)
    refine Finset.sum_eq_zero fun u _ ↦ Finset.sum_eq_zero fun ys _ ↦ ?_
    have hp0 : P_XY.real {(x, ys.1)} = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ measureReal_nonneg)).mp hz ys.1
        (Finset.mem_univ _)
    rw [hp0]; ring
  rw [hext]
  exact wz_wsm_negLog_mean_eq_entropy P_XY κ'

/-- Strong typicality pins the linear functional `M` to `H(wsm)`. If an empirical type `t` on the
covering subtype `{x // 0 < P_X x} × Fin k`
is within `ε` (in sup-norm) of the consistent covering pmf `qStar(x, u) = κ'(x, u) · P_X(x)`,
then the conditional-mean statistic `M(t) = ∑_{x,u} t(x, u) · g(x, u)` is within `C · ε` of the
`wsm`-entropy `H(wsm) = ∑_q negMulLog(wsm q)`, with the explicit constant
`C = ∑_{x,u} |g(x, u)|`. Strong joint typicality pins the
empirical type in total variation (`∀ p, |typeCount/n − qStar p| ≤ ε`, from
`mem_stronglyTypicalSet_iff`), which — unlike weak entropy-only typicality — pins every linear
functional of the type, in particular `M`. The identity `⟨qStar, g⟩ = H(wsm)`
(`wz_wsm_condMean_kernel_inner_eq_entropy`) turns the difference into
`⟨t − qStar, g⟩`, bounded by `(∑|g|) · ε` via the triangle inequality. -/
private lemma wz_wsm_negLog_mean_pin_of_type
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (t : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (htype : ∀ p, |t p - κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)}| ≤ ε) :
    |(∑ p, t p * wzCondMeanKernel P_XY κ' p)
        - ∑ q, Real.negMulLog (wzSideInfoMarginal P_XY κ' q)|
      ≤ (∑ p, |wzCondMeanKernel P_XY κ' p|) * ε := by
  classical
  have hid := wz_wsm_condMean_kernel_inner_eq_entropy P_XY κ'
  -- Rewrite the difference `M(t) − H(wsm)` as `⟨t − qStar, g⟩`.
  have hdiff : (∑ p, t p * wzCondMeanKernel P_XY κ' p)
      - ∑ q, Real.negMulLog (wzSideInfoMarginal P_XY κ' q)
      = ∑ p, (t p - κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
          * wzCondMeanKernel P_XY κ' p := by
    rw [← hid, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ ↦ by ring
  rw [hdiff]
  calc |∑ p, (t p - κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
          * wzCondMeanKernel P_XY κ' p|
      ≤ ∑ p, |(t p - κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
          * wzCondMeanKernel P_XY κ' p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, ε * |wzCondMeanKernel P_XY κ' p| := by
        refine Finset.sum_le_sum fun p _ ↦ ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (htype p) (abs_nonneg _)
    _ = (∑ p, |wzCondMeanKernel P_XY κ' p|) * ε := by
        rw [← Finset.mul_sum, mul_comm]

open ChannelCoding in
/-- The mean-pin `wz_wsm_negLog_mean_pin_of_type`
read directly off strong joint typicality: a block `zb` that is strongly typical for the
covering ambient `rdAmbient qStar` (`zb ∈ stronglyTypicalSet …`) has its conditional-mean
statistic `∑_{x,u} (typeCount zb / n) · g(x, u)` within `(∑|g|) · ε` of `H(wsm)`. The
strong-typicality membership yields the per-symbol type pin `∀ p, |typeCount zb p / n −
qStar p| ≤ ε` (`mem_stronglyTypicalSet_iff` + the `rdAmbient` singleton law), and `hqStar`
identifies `qStar p = κ'(p) · P_X(p)`. This is the form the strong-`Ecov` covering core
consumes. -/
private lemma wz_wsm_negLog_mean_pin_of_stronglyTypical
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (hmem : qStar ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k))
    (hqStar : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ}
    (zb : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k)
    (hzb : zb ∈ stronglyTypicalSet (rdAmbient qStar) (jointSequence iidXs iidYs) n ε) :
    |(∑ p, ((typeCount zb p : ℝ) / n) * wzCondMeanKernel P_XY κ' p)
        - ∑ q, Real.negMulLog (wzSideInfoMarginal P_XY κ' q)|
      ≤ (∑ p, |wzCondMeanKernel P_XY κ' p|) * ε := by
  classical
  haveI hne_prod : Nonempty ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k) :=
    Finset.univ_nonempty_iff.mp
      (Finset.nonempty_of_sum_ne_zero (by rw [hmem.2]; exact one_ne_zero))
  haveI hne_α' : Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}} := hne_prod.map Prod.fst
  haveI hne_k : Nonempty (Fin k) := hne_prod.map Prod.snd
  refine wz_wsm_negLog_mean_pin_of_type P_XY κ' (fun p ↦ (typeCount zb p : ℝ) / n) hε ?_
  intro p
  rw [mem_stronglyTypicalSet_iff] at hzb
  have hlaw : ((rdAmbient qStar).map (jointSequence iidXs iidYs 0)).real {p} = qStar p := by
    rw [rdAmbient_map_jointSequence qStar hmem]
    exact pmfToMeasure_real_singleton hmem p
  rw [← hqStar p, ← hlaw]
  exact hzb p

/-- Any `pmfToMeasure q` on a finite alphabet is a finite measure (its total mass is the
finite sum `∑ a, ENNReal.ofReal (q a) < ∞`), regardless of whether `q` is a proper pmf. -/
private lemma wz_pmfToMeasure_isFiniteMeasure
    {T : Type*} [Fintype T]
    [MeasurableSpace T] [MeasurableSingletonClass T] (q : T → ℝ) :
    IsFiniteMeasure (ChannelCoding.pmfToMeasure q) := by
  refine ⟨?_⟩
  unfold ChannelCoding.pmfToMeasure
  rw [Measure.finsetSum_apply Finset.univ _ Set.univ]
  have h_each : ∀ a ∈ (Finset.univ : Finset T),
      (ENNReal.ofReal (q a) • Measure.dirac a) (Set.univ : Set T) = ENNReal.ofReal (q a) := by
    intro a _; simp [Measure.smul_apply]
  rw [Finset.sum_congr rfl h_each]
  exact ENNReal.sum_lt_top.mpr (fun a _ ↦ ENNReal.ofReal_lt_top)

/-- On the finite
block space `Fin n → T`, the `Measure.pi`-mass of any set `S` reads off atom-by-atom:
`(Measure.pi (fun i ↦ pmfToMeasure (q i))).real S = ∑_p S.indicator (∏ i, q i (p i))`.
Uses `measure_biUnion_finset` over the singletons `{p}` (each a `Set.pi` box, evaluated by
`Measure.pi_pi` + `pmfToMeasure_apply_singleton`). -/
private lemma wz_pi_pmf_real_eq_sum
    {T : Type*} [Fintype T]
    [MeasurableSpace T] [MeasurableSingletonClass T] {n : ℕ} (q : Fin n → T → ℝ)
    (hq : ∀ i t, 0 ≤ q i t) (S : Set (Fin n → T)) :
    (Measure.pi (fun i ↦ ChannelCoding.pmfToMeasure (q i))).real S
      = ∑ p : Fin n → T, S.indicator (fun p ↦ ∏ i, q i (p i)) p := by
  classical
  haveI hfin : ∀ i, IsFiniteMeasure (ChannelCoding.pmfToMeasure (q i)) :=
    fun i ↦ wz_pmfToMeasure_isFiniteMeasure (q i)
  -- ENNReal singleton-sum via `measure_biUnion_finset` + `Measure.pi_pi`.
  have hmeas : (Measure.pi (fun i ↦ ChannelCoding.pmfToMeasure (q i))) S
      = ∑ p ∈ Finset.univ.filter (fun p ↦ p ∈ S),
          ∏ i, ENNReal.ofReal (q i (p i)) := by
    have hSU : S = ⋃ p ∈ Finset.univ.filter (fun p ↦ p ∈ S),
        ({p} : Set (Fin n → T)) := by
      ext x; simp [Finset.mem_filter]
    conv_lhs => rw [hSU]
    rw [measure_biUnion_finset]
    · refine Finset.sum_congr rfl (fun p _ ↦ ?_)
      have hsing : ({p} : Set (Fin n → T))
          = Set.pi Set.univ (fun i ↦ ({p i} : Set T)) := by
        ext x
        simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_implies]
        exact ⟨fun h i ↦ by rw [h], fun h ↦ funext h⟩
      rw [hsing, Measure.pi_pi]
      refine Finset.prod_congr rfl (fun i _ ↦ ?_)
      exact ChannelCoding.pmfToMeasure_apply_singleton (q i) (p i)
    · intro p₁ _ p₂ _ hp
      show Disjoint ({p₁} : Set (Fin n → T)) ({p₂} : Set (Fin n → T))
      rw [Set.disjoint_singleton]; exact hp
    · intro p _
      exact MeasurableSet.singleton p
  -- Rewrite the RHS indicator sum as a filter sum, then take `toReal`.
  have hRHS : (∑ p : Fin n → T, S.indicator (fun p ↦ ∏ i, q i (p i)) p)
      = ∑ p ∈ Finset.univ.filter (fun p ↦ p ∈ S), ∏ i, q i (p i) := by
    simp only [Set.indicator_apply, Finset.sum_filter]
  rw [hRHS, Measure.real, hmeas,
    ENNReal.toReal_sum (fun p _ ↦ ENNReal.prod_ne_top (fun i _ ↦ ENNReal.ofReal_ne_top))]
  refine Finset.sum_congr rfl (fun p _ ↦ ?_)
  rw [ENNReal.toReal_prod]
  refine Finset.prod_congr rfl (fun i _ ↦ ?_)
  exact ENNReal.toReal_ofReal (hq i (p i))

/-- The source-block measure
`SRC = Measure.pi (fun _ ↦ pmfToMeasure Src)` with `Src (x, y) = P_XY{(x, y)}` disintegrates over
the `x`-block: for any block event `S`,
`SRC.real S = ∑_{xb} (∏_i P_X(xb_i)) · condY(xb).real (xb-slice of S)`,
where `P_X(x) = ∑_y P_XY{(x, y)}` (positive on the `x`-alphabet subtype) and the conditional
`y`-block measure `condY(xb) = Measure.pi (fun i ↦ pmfToMeasure (P(·|xb_i)))` uses the *normalized*
per-coordinate law `P(y|x) = P_XY{(x, y)} / P_X(x)`, hence a genuine probability measure — the
form the conditional-Chebyshev step consumes. This avoids general `condDistrib` on
`Measure.pi` (a Mathlib 0-hit); it is elementary finite Fubini via `pmfToMeasure` atomicity and
`Measure.pi_pi`, with no AEP. -/
lemma wz_srcBlock_condMeasure_split
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY] {n : ℕ}
    (S : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β)) :
    (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
          P_XY.real {(p.1.1, p.2)}))).real S
      = ∑ xb : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}},
          (∏ i, ∑ y, P_XY.real {((xb i).1, y)})
            * (Measure.pi (fun i ↦ ChannelCoding.pmfToMeasure
                (fun y : β ↦ P_XY.real {((xb i).1, y)}
                  / ∑ y', P_XY.real {((xb i).1, y')}))).real
                {yb | (fun i ↦ (xb i, yb i)) ∈ S} := by
  classical
  -- The `x`-alphabet subtype has positive `P_X`, so the conditional denominator cancels.
  have hcancel : ∀ (x : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (y : β),
      (∑ y', P_XY.real {(x.1, y')}) * (P_XY.real {(x.1, y)} / ∑ y', P_XY.real {(x.1, y')})
        = P_XY.real {(x.1, y)} := by
    intro x y
    have hx : (∑ y', P_XY.real {(x.1, y')}) ≠ 0 := x.2.ne'
    field_simp
  -- LHS: apply the singleton-sum helper, then reindex the block sum over the x-block via the
  -- equiv `(Fin n → α'×β) ≃ (Fin n → α') × (Fin n → β)` (its `symm` is `fun i ↦ (xb i, yb i)`).
  have hLHS :
      (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
          (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
            P_XY.real {(p.1.1, p.2)}))).real S
        = ∑ xb : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}}, ∑ yb : Fin n → β,
            S.indicator (fun p ↦ ∏ i, P_XY.real {((p i).1.1, (p i).2)})
              (fun i ↦ (xb i, yb i)) := by
    rw [wz_pi_pmf_real_eq_sum
      (fun _ : Fin n ↦ fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
        P_XY.real {(p.1.1, p.2)}) (fun _ _ ↦ measureReal_nonneg) S]
    rw [← Equiv.sum_comp (Equiv.arrowProdEquivProdArrow (Fin n)
          (fun _ ↦ {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (fun _ ↦ β)).symm
        (fun p ↦ S.indicator (fun p ↦ ∏ i, P_XY.real {((p i).1.1, (p i).2)}) p),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun xb _ ↦ Finset.sum_congr rfl (fun yb _ ↦ ?_))
    rfl
  -- RHS: apply the singleton-sum helper to each conditional y-block measure.
  have hcond : ∀ xb : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}},
      (Measure.pi (fun i ↦ ChannelCoding.pmfToMeasure
          (fun y : β ↦ P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')}))).real
          {yb | (fun i ↦ (xb i, yb i)) ∈ S}
        = ∑ yb : Fin n → β, {yb | (fun i ↦ (xb i, yb i)) ∈ S}.indicator
            (fun yb ↦ ∏ i, P_XY.real {((xb i).1, yb i)} / ∑ y', P_XY.real {((xb i).1, y')}) yb :=
    fun xb ↦ wz_pi_pmf_real_eq_sum
      (fun i ↦ fun y : β ↦ P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')})
      (fun _ _ ↦ div_nonneg measureReal_nonneg (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg))
      {yb | (fun i ↦ (xb i, yb i)) ∈ S}
  rw [hLHS]
  refine Finset.sum_congr rfl (fun xb _ ↦ ?_)
  rw [hcond, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun yb _ ↦ ?_)
  by_cases hmem : (fun i ↦ (xb i, yb i)) ∈ S
  · have hmem' : yb ∈ {yb | (fun i ↦ (xb i, yb i)) ∈ S} := hmem
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem', ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ ↦ (hcancel (xb i) (yb i)).symm)
  · have hmem' : yb ∉ {yb | (fun i ↦ (xb i, yb i)) ∈ S} := hmem
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem', mul_zero]

/-- On a finite product measure
`Measure.pi ν` (each `ν i` a probability measure on the finite alphabet `β`), the empirical mean
`(∑ᵢ ψᵢ(yᵢ))/n` of a *per-coordinate* (non-identically distributed) family of statistics
`ψ : Fin n → β → ℝ` deviates from its mean `(∑ᵢ (νᵢ)[ψᵢ])/n` by at least `δ` on a set of mass at
most `(∑ᵢ Var[ψᵢ; νᵢ])/(n²δ²)`. Finite-`n` Chebyshev via `variance_sum_pi` (pairwise independence
of coordinate evaluations under `Measure.pi`, `IdentDistrib`-free) — the conditional-AEP engine for
the Wyner–Ziv Markov core: each summand `ψᵢ = -log wsm(uᵢ, ·)` is a function of the single
coordinate `yᵢ`, so the `νᵢ = P(·|xᵢ)` product structure makes them
independent-but-not-identical. -/
private lemma wz_pi_nonuniform_mean_concentration
    {n : ℕ} (hn : 0 < n)
    (ν : Fin n → Measure β) [∀ i, IsProbabilityMeasure (ν i)]
    (ψ : Fin n → β → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (Measure.pi ν).real
        { yb : Fin n → β | δ ≤ |(∑ i, ψ i (yb i)) / (n : ℝ)
            - (∑ i, ∫ y, ψ i y ∂(ν i)) / (n : ℝ)| }
      ≤ (∑ i, variance (ψ i) (ν i)) / ((n : ℝ) ^ 2 * δ ^ 2) := by
  classical
  set μpi : Measure (Fin n → β) := Measure.pi ν with hμpi
  haveI : IsProbabilityMeasure μpi := by rw [hμpi]; infer_instance
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  -- Each `ψ i` is MemLp 2 (finite alphabet + probability measure).
  have hmemν : ∀ i, MemLp (ψ i) 2 (ν i) := fun i ↦ MemLp.of_discrete
  -- Coordinate evaluations are MemLp 2 under `μpi`.
  have hmemcoord : ∀ i : Fin n, MemLp (fun yb : Fin n → β ↦ ψ i (yb i)) 2 μpi :=
    fun i ↦ (hmemν i).comp_measurePreserving (measurePreserving_eval ν i)
  set S : (Fin n → β) → ℝ := fun yb ↦ ∑ i, ψ i (yb i) with hS
  have hSmem : MemLp S 2 μpi := by
    have := memLp_finsetSum (μ := μpi) (p := (2 : ℝ≥0∞)) Finset.univ
      (f := fun (i : Fin n) (yb : Fin n → β) ↦ ψ i (yb i)) (fun i _ ↦ hmemcoord i)
    simpa [hS] using this
  -- Variance of `S` = ∑ per-coordinate variance (`variance_sum_pi`).
  have hVarS : variance S μpi = ∑ i, variance (ψ i) (ν i) := by
    have hpi := variance_sum_pi (ι := Fin n) (Ω := fun _ : Fin n ↦ β)
      (μ := ν) (X := ψ) hmemν
    rw [hS, show (fun yb : Fin n → β ↦ ∑ i, ψ i (yb i))
        = (∑ i, fun ω : Fin n → β ↦ ψ i (ω i)) by
      funext yb; simp [Finset.sum_apply]]
    rw [hpi]
  -- Mean of `S` = ∑ per-coordinate mean.
  have hmeanS : μpi[S] = ∑ i, ∫ y, ψ i y ∂(ν i) := by
    have hint : ∀ i : Fin n, μpi[fun yb : Fin n → β ↦ ψ i (yb i)] = ∫ y, ψ i y ∂(ν i) := by
      intro i
      have hmp : MeasurePreserving (Function.eval i) μpi (ν i) := measurePreserving_eval ν i
      calc μpi[fun yb : Fin n → β ↦ ψ i (yb i)]
          = ∫ yb, ψ i (Function.eval i yb) ∂μpi := rfl
        _ = ∫ y, ψ i y ∂(Measure.map (Function.eval i) μpi) := by
              rw [integral_map hmp.measurable.aemeasurable]
              exact (hmemν i).aestronglyMeasurable.aemeasurable.aestronglyMeasurable.mono_ac
                (by rw [hmp.map_eq])
        _ = ∫ y, ψ i y ∂(ν i) := by rw [hmp.map_eq]
    rw [hS, integral_finsetSum]
    · exact Finset.sum_congr rfl (fun i _ ↦ hint i)
    · exact fun i _ ↦ (hmemcoord i).integrable (by norm_num)
  -- Absolute-value identity linking empirical-mean deviation and centered-sum deviation.
  have habs : ∀ yb : Fin n → β,
      |S yb - μpi[S]| = (n : ℝ) * |(∑ i, ψ i (yb i)) / (n : ℝ)
          - (∑ i, ∫ y, ψ i y ∂(ν i)) / (n : ℝ)| := by
    intro yb
    rw [hmeanS]
    rw [show (n : ℝ) * |(∑ i, ψ i (yb i)) / (n : ℝ) - (∑ i, ∫ y, ψ i y ∂(ν i)) / (n : ℝ)|
          = |(n : ℝ) * ((∑ i, ψ i (yb i)) / (n : ℝ)
              - (∑ i, ∫ y, ψ i y ∂(ν i)) / (n : ℝ))| by
        rw [abs_mul, abs_of_pos hnR]]
    congr 1
    simp only [hS]
    field_simp
  have hset : { yb : Fin n → β | δ ≤ |(∑ i, ψ i (yb i)) / (n : ℝ)
          - (∑ i, ∫ y, ψ i y ∂(ν i)) / (n : ℝ)| }
      = { yb : Fin n → β | (n : ℝ) * δ ≤ |S yb - μpi[S]| } := by
    ext yb
    simp only [Set.mem_setOf_eq, habs yb]
    constructor
    · intro h; exact mul_le_mul_of_nonneg_left h hnR.le
    · intro h; exact le_of_mul_le_mul_left h hnR
  rw [measureReal_def, hset]
  have hcheb := meas_ge_le_variance_div_sq (μ := μpi) hSmem (c := (n : ℝ) * δ) (by positivity)
  calc (μpi { yb : Fin n → β | (n : ℝ) * δ ≤ |S yb - μpi[S]| }).toReal
      ≤ (ENNReal.ofReal (variance S μpi / ((n : ℝ) * δ) ^ 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
    _ = variance S μpi / ((n : ℝ) * δ) ^ 2 :=
        ENNReal.toReal_ofReal (div_nonneg (variance_nonneg S μpi) (by positivity))
    _ = (∑ i, variance (ψ i) (ν i)) / ((n : ℝ) ^ 2 * δ ^ 2) := by rw [hVarS, mul_pow]

/-- Uniform-in-`(ν, ψ, w)` version of
`wz_pi_nonuniform_mean_concentration`: given a common sup-bound `B` on every per-coordinate
statistic `|ψᵢ| ≤ B`, the deviation of the empirical mean from *its own (conditional) mean* by
`≥ δ` has `Measure.pi ν`-mass `≤ tol` for all `n ≥ N` (an explicit `N` depending only on
`B, δ, tol`). This is the "concentration around the conditional mean" half of the Wyner–Ziv Markov
core — the part that is a genuine theorem for *every* codeword block `w` and source block `xb`
(the variance bound `Var[ψᵢ] ≤ B²` is uniform, so no typicality of `xb` is needed here). What is
NOT supplied here — and is the residual Markov content — is that the conditional mean
`(∑ᵢ (νᵢ)[ψᵢ])/n` is close to the ambient entropy `H(wsm)`; see the note on the core. -/
private lemma wz_pi_nonuniform_concentration_tendsto
    {B δ tol : ℝ} (hδ : 0 < δ) (htol : 0 < tol) (hB : 0 ≤ B) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (ν : Fin n → Measure β),
        (∀ i, IsProbabilityMeasure (ν i)) → ∀ (ψ : Fin n → β → ℝ),
        (∀ i y, |ψ i y| ≤ B) →
        (Measure.pi ν).real
            { yb : Fin n → β | δ ≤ |(∑ i, ψ i (yb i)) / (n : ℝ)
                - (∑ i, ∫ y, ψ i y ∂(ν i)) / (n : ℝ)| }
          ≤ tol := by
  classical
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (B ^ 2 / (tol * δ ^ 2))
  refine ⟨N₀ + 1, fun n hn ν hν ψ hψ ↦ ?_⟩
  have hn_pos : 0 < n := lt_of_lt_of_le (Nat.succ_pos N₀) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn_pos
  haveI : ∀ i, IsProbabilityMeasure (ν i) := hν
  -- Chebyshev deviation bound from the engine.
  have hcheb := wz_pi_nonuniform_mean_concentration hn_pos ν ψ (δ := δ) hδ
  -- Uniform variance bound: each `variance (ψ i) (ν i) ≤ B²`.
  have hvar_le : ∀ i, variance (ψ i) (ν i) ≤ B ^ 2 := by
    intro i
    have hIcc : ∀ᵐ y ∂(ν i), ψ i y ∈ Set.Icc (-B) B :=
      Filter.Eventually.of_forall (fun y ↦ abs_le.mp (hψ i y))
    have := variance_le_sq_of_bounded hIcc (measurable_of_finite (ψ i)).aemeasurable
    calc variance (ψ i) (ν i) ≤ ((B - (-B)) / 2) ^ 2 := this
      _ = B ^ 2 := by ring
  have hsum_var : (∑ i, variance (ψ i) (ν i)) ≤ (n : ℝ) * B ^ 2 := by
    calc (∑ i, variance (ψ i) (ν i)) ≤ ∑ _i : Fin n, B ^ 2 :=
          Finset.sum_le_sum (fun i _ ↦ hvar_le i)
      _ = (n : ℝ) * B ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Chain: mass ≤ (∑ var)/(n²δ²) ≤ nB²/(n²δ²) = B²/(nδ²) ≤ tol.
  have hden : (0 : ℝ) < (n : ℝ) ^ 2 * δ ^ 2 := by positivity
  have hstep1 : (∑ i, variance (ψ i) (ν i)) / ((n : ℝ) ^ 2 * δ ^ 2)
      ≤ ((n : ℝ) * B ^ 2) / ((n : ℝ) ^ 2 * δ ^ 2) := by
    gcongr
  have hstep2 : ((n : ℝ) * B ^ 2) / ((n : ℝ) ^ 2 * δ ^ 2) = B ^ 2 / ((n : ℝ) * δ ^ 2) := by
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    field_simp
  have hstep3 : B ^ 2 / ((n : ℝ) * δ ^ 2) ≤ tol := by
    have hnδ : (0 : ℝ) < (n : ℝ) * δ ^ 2 := by positivity
    rw [div_le_iff₀ hnδ]
    have htolδ : (0 : ℝ) < tol * δ ^ 2 := by positivity
    have hn_gt : B ^ 2 / (tol * δ ^ 2) < (n : ℝ) := by
      have : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.trans' (Nat.le_succ N₀)
      linarith [hN₀]
    have : B ^ 2 < (n : ℝ) * (tol * δ ^ 2) := by
      rw [div_lt_iff₀ htolδ] at hn_gt; linarith [hn_gt]
    nlinarith [this]
  calc (Measure.pi ν).real
          { yb : Fin n → β | δ ≤ |(∑ i, ψ i (yb i)) / (n : ℝ)
              - (∑ i, ∫ y, ψ i y ∂(ν i)) / (n : ℝ)| }
        ≤ (∑ i, variance (ψ i) (ν i)) / ((n : ℝ) ^ 2 * δ ^ 2) := hcheb
      _ ≤ ((n : ℝ) * B ^ 2) / ((n : ℝ) ^ 2 * δ ^ 2) := hstep1
      _ = B ^ 2 / ((n : ℝ) * δ ^ 2) := hstep2
      _ ≤ tol := hstep3

open ChannelCoding in
/-- The independent-product mass of the strong joint-typical set under the covering ambient
`rdAmbient qStar` — the probability that an independently drawn covering word `U^n` is strongly
jointly typical with the source block `X^n` at radius `ε` — is bounded below by the standard
random-coding exponent `(1 − η)·exp(n·((H(Z) − H(X) − H(Y)) − slack))`. This is the WZ
instantiation of `jointStronglyTypicalSet_indep_prob_ge`, discharging its independence /
ident-distribution / full-support / marginal-matching premises from the ambient-regularity
lemmas of `rdAmbient qStar` (full support of `qStar` gives `hposX/Y/Z`). It is the covering-success
lower bound feeding the joint (distortion + covering-success) derandomize of
`wz_coveringFamily_of_testChannel`. -/
lemma wz_covering_strongTypical_indep_mass_ge
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} [Nonempty (Fin k)]
    [Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}}]
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (hpos : ∀ p, 0 < qStar p)
    (hmem : qStar ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k))
    {ε δ η : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1 - η) * Real.exp ((n : ℝ) *
        ((entropy (rdAmbient qStar)
              (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs 0)
            - entropy (rdAmbient qStar) (ChannelCoding.iidXs 0)
            - entropy (rdAmbient qStar) (ChannelCoding.iidYs 0))
          - (((Fintype.card (Fin k) : ℝ) * ε
                * logSumAbs (rdAmbient qStar) ChannelCoding.iidXs
              + (Fintype.card {x : α // 0 < ∑ y, P_XY.real {(x, y)}} : ℝ) * ε
                * logSumAbs (rdAmbient qStar) ChannelCoding.iidYs
              + ε * logSumAbs (rdAmbient qStar)
                  (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs))
              + 3 * δ)))
        ≤ (((rdAmbient qStar).map (jointRV ChannelCoding.iidXs n)).prod
              ((rdAmbient qStar).map (jointRV ChannelCoding.iidYs n))).real
            (jointStronglyTypicalSet (rdAmbient qStar)
              ChannelCoding.iidXs ChannelCoding.iidYs n ε) := by
  haveI : IsProbabilityMeasure (rdAmbient qStar) := rdAmbient_isProbabilityMeasure qStar hmem
  exact jointStronglyTypicalSet_indep_prob_ge (rdAmbient qStar)
    ChannelCoding.iidXs ChannelCoding.iidYs
    (fun i ↦ ChannelCoding.measurable_iidXs i) (fun i ↦ ChannelCoding.measurable_iidYs i)
    (rdAmbient_iIndepFun_iidXs qStar hmem) (rdAmbient_identDistrib_iidXs qStar hmem)
    (rdAmbient_iIndepFun_iidYs qStar hmem) (rdAmbient_identDistrib_iidYs qStar hmem)
    (rdAmbient_iIndepFun_jointSequence qStar hmem)
    (rdAmbient_pairwise_indep_jointSequence qStar hmem)
    (rdAmbient_identDistrib_jointSequence qStar hmem)
    (rdAmbient_iidXs_real_singleton_pos qStar hmem hpos)
    (rdAmbient_iidYs_real_singleton_pos qStar hmem hpos)
    (rdAmbient_jointSequence_real_singleton_pos qStar hmem hpos)
    (rdAmbient_map_fst_jointSequence qStar hmem)
    (rdAmbient_map_snd_jointSequence qStar hmem)
    hε hδ hη

/-- The radius `ε_cov = ε / (2·(1 + C))` at which the
covering word is required to be strongly `(x, U)`-typical, where `C = ∑_{x,u} |g(x, u)|` is the
mean-pin amplification constant of `wz_wsm_negLog_mean_pin_of_stronglyTypical` (`g =
wzCondMeanKernel`). The mean-pin bounds `|M(xb) − H(wsm)|` by `C · (strong radius)`, so to keep
the conditional-mean statistic within `ε/2` of `H(wsm)` — the slack the correlated Markov core
needs to absorb the acceptance-band radius `ε` — the strong covering radius must be `≤ ε/(2C)`.
Using `ε/(2·(1 + C))` makes the choice unconditional (`C ≥ 0`) and keeps `ε_cov > 0`. This is a
computed term of `ε`, `κ'`, `P_XY` (NOT a new lemma parameter), so the chain signatures stay
fixed. Strong typicality at the *same* radius `ε` would only pin `M` within `C·ε ≫ ε`, leaving an
`O(ε)` partial-relabel counterexample class open (a scaled-down label swap); the smaller radius
closes that class. -/
noncomputable def wzCoveringStrongRadius
    (P_XY : Measure (α × β)) {k : ℕ} (κ' : α → Fin k → ℝ) (ε : ℝ) : ℝ :=
  ε / (2 * (1 + ∑ p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k,
    |wzCondMeanKernel P_XY κ' p|))

/-- The strong covering radius is positive for `ε > 0` (the denominator `2·(1 + ∑|g|)` is `≥ 2`). -/
lemma wzCoveringStrongRadius_pos
    (P_XY : Measure (α × β)) {k : ℕ} (κ' : α → Fin k → ℝ) {ε : ℝ} (hε : 0 < ε) :
    0 < wzCoveringStrongRadius P_XY κ' ε := by
  unfold wzCoveringStrongRadius
  have hC : (0 : ℝ) ≤ ∑ p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k,
      |wzCondMeanKernel P_XY κ' p| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  positivity

open ChannelCoding in
/-- The covering-success event for the
strong-`Ecov` Wyner–Ziv covering chain: the chosen covering word `c.decoder (c.encoder x)` is
jointly typical with the source `x` in the covering ambient `rdAmbient qStar`, in BOTH readings.

* The strong reading (`jointStronglyTypicalSet`) is a per-symbol type pin at the *smaller*
  radius `wzCoveringStrongRadius P_XY κ' ε = ε/(2(1 + C))`; it is the strengthening that makes the
  correlated Markov core `wz_covering_jointBand_markov_core` true-as-framed, by pinning the
  conditional-mean statistic `M(xb)` to within `C · ε_cov < ε/2` of `H(wzSideInfoMarginal)`
  through `wz_wsm_negLog_mean_pin_of_stronglyTypical`. This kills not only the full
  entropy-preserving label-swap counterexample but the whole `O(ε)` partial-relabel class that
  strong typicality at the *same* radius `ε` would leave open (there `|M − H| ≤ C·ε ≫ ε`).
* The weak reading (`jointlyTypicalSet`) is an entropy band at radius `ε`; it is retained so
  that the acceptance-band `U`-typicality plumbing `wz_covering_success_subset_uTypical` — which
  needs the weak `U`-band at radius `ε` — goes through unchanged.

Strong typicality at radius `ε_cov` does not imply the weak `U`-band at radius `ε` (the
strong-to-weak bridge widens the radius by `ε_cov·logSumAbs`, an unrelated constant), so the
covering-success event is the intersection of the two readings. This keeps every lemma signature
in the chain fixed (the radii are computed terms of `ε`) while making the correlated Markov
concentration true-as-framed. -/
def wzCoveringSuccessStrong
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    {n : ℕ} {M : ℕ} (c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k))
    (ε : ℝ) : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
  { p | (fun j ↦ (p j).1, c.decoder (c.encoder (fun j ↦ (p j).1)))
      ∈ jointStronglyTypicalSet (rdAmbient qStar)
          ChannelCoding.iidXs ChannelCoding.iidYs n (wzCoveringStrongRadius P_XY κ' ε) }
  ∩ { p | (fun j ↦ (p j).1, c.decoder (c.encoder (fun j ↦ (p j).1)))
      ∈ ChannelCoding.jointlyTypicalSet (rdAmbient qStar)
          ChannelCoding.iidXs ChannelCoding.iidYs n ε }

/-- Strong covering-success implies weak covering-success (the second conjunct, at radius `ε`),
the reading the `U`-typicality plumbing consumes. -/
lemma wzCoveringSuccessStrong_subset_weak
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    {n : ℕ} {M : ℕ} (c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k))
    (ε : ℝ) :
    wzCoveringSuccessStrong P_XY κ' qStar c ε
      ⊆ { p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β |
          (fun j ↦ (p j).1, c.decoder (c.encoder (fun j ↦ (p j).1)))
            ∈ ChannelCoding.jointlyTypicalSet (rdAmbient qStar)
                ChannelCoding.iidXs ChannelCoding.iidYs n ε } :=
  fun _ hp ↦ hp.2

/-- For a block `z : Fin n → T` on a finite alphabet `T`, summing a
per-symbol statistic `f` over the coordinates equals summing over the alphabet weighted by the
empirical counts: `∑ i, f (z i) = ∑ p, (typeCount z p) · f p`. This is the standard method-of-types
regrouping (`Finset.sum_fiberwise_of_maps_to'` over the fibers `{i | z i = p}`). -/
private lemma wz_sum_eq_typeCount_mul {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
    (z : Fin n → T) (f : T → ℝ) :
    ∑ i, f (z i) = ∑ p : T, (typeCount z p : ℝ) * f p := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin n)))
        (t := (Finset.univ : Finset T)) (g := z) (fun i _ ↦ Finset.mem_univ _) f]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

private lemma wz_covering_uyBand_key
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    (∑ p, |wzCondMeanKernel P_XY κ' p|) * wzCoveringStrongRadius P_XY κ' ε < ε / 2 := by
  classical
  have hC_nonneg : 0 ≤ ∑ p, |wzCondMeanKernel P_XY κ' p| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  unfold wzCoveringStrongRadius
  set C := ∑ p, |wzCondMeanKernel P_XY κ' p| with hC
  have hden : (0 : ℝ) < 2 * (1 + C) := by linarith [hC_nonneg]
  rw [show C * (ε / (2 * (1 + C))) = C * ε / (2 * (1 + C)) from
      (mul_div_assoc C ε (2 * (1 + C))).symm, div_lt_iff₀ hden]
  nlinarith [hε, hC_nonneg, mul_nonneg hC_nonneg hε.le]

private lemma wz_covering_uyBand_mean_pin
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (hmem_q : qStar ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k))
    (hqStar : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
    (ε : ℝ) (hε : 0 < ε)
    {n : ℕ} (xb : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}})
    (U : Fin n → Fin k) (ψ : Fin n → β → ℝ)
    (hint : ∀ i, ∫ y, ψ i y ∂(ChannelCoding.pmfToMeasure
          (fun y : β ↦ P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')}))
        = wzCondMeanKernel P_XY κ' (xb i, U i))
    (hgood : (fun i ↦ (xb i, U i)) ∈ stronglyTypicalSet (rdAmbient qStar)
        (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n
        (wzCoveringStrongRadius P_XY κ' ε))
    (hkey : (∑ p, |wzCondMeanKernel P_XY κ' p|) * wzCoveringStrongRadius P_XY κ' ε < ε / 2) :
    |(∑ i, ∫ y, ψ i y ∂(ChannelCoding.pmfToMeasure
          (fun y : β ↦ P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')}))) / (n : ℝ)
        - ∑ q, Real.negMulLog (wzSideInfoMarginal P_XY κ' q)| < ε / 2 := by
  classical
  have hMstat_eq : (∑ i, ∫ y, ψ i y ∂(ChannelCoding.pmfToMeasure
        (fun y : β ↦ P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')}))) / (n : ℝ)
      = ∑ p, ((typeCount (fun i ↦ (xb i, U i)) p : ℝ) / n) * wzCondMeanKernel P_XY κ' p := by
    have hsum : (∑ i, ∫ y, ψ i y ∂(ChannelCoding.pmfToMeasure
          (fun y : β ↦ P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')})))
        = ∑ p, (typeCount (fun i ↦ (xb i, U i)) p : ℝ) * wzCondMeanKernel P_XY κ' p := by
      rw [← wz_sum_eq_typeCount_mul (fun i ↦ (xb i, U i)) (wzCondMeanKernel P_XY κ')]
      exact Finset.sum_congr rfl fun i _ ↦ hint i
    rw [hsum, Finset.sum_div]
    exact Finset.sum_congr rfl fun p _ ↦ by ring
  rw [hMstat_eq]
  refine lt_of_le_of_lt
    (wz_wsm_negLog_mean_pin_of_stronglyTypical P_XY κ' qStar hmem_q hqStar
      (wzCoveringStrongRadius_pos P_XY κ' hε).le (fun i ↦ (xb i, U i)) hgood) hkey

open ChannelCoding in
/-- For a
strong-covering `x`-block `xb` — one whose induced `(x, U)` block
`(xb i, c.decoder (c.encoder xb) i)` is strongly typical for the covering ambient at the strong
radius `ε_cov = wzCoveringStrongRadius P_XY κ' ε` — the conditional side-information measure of the
`(U, Y)`-atypical slice is `≤ tol/8` for `n ≥ N`. This is the conditional AEP `U — X — Y`: the
mean-pin (`wz_wsm_negLog_mean_pin_of_stronglyTypical`) puts the conditional mean of
`-log wsm(U_i, ·)` within `C·ε_cov < ε/2` of `H(wsm)`, and the conditional Chebyshev
(`wz_pi_nonuniform_concentration_tendsto`, deviation `ε/2`) concentrates the empirical
`(U, Y)`-entropy there, so `(U, Y)`-atypicality (radius `ε`) has vanishing conditional mass. This
is the from-scratch conditional-AEP kernel; the surrounding finite-Fubini split, good/bad
`x`-block dichotomy and summation are discharged in `wz_covering_jointBand_markov_core`.

Implementation notes. The hypothesis uses strong (not weak) typicality: strong typicality pins the
per-symbol `(x, u)`-type in total variation, controlling the linear functional `M = ⟨type, g⟩`
that the conclusion needs — no finer structure required — whereas weak entropy-only typicality
fails on an entropy-preserving label-swap counterexample class. The assembly mirrors the in-tree
template `wz_covering_yBand_aep`: a uniform sup-bound `B = ∑_q |log wsm(q)|` on the per-coordinate
log-statistic, its conditional mean identified with `wzCondMeanKernel`, and the ambient entropy
`∑_q negMulLog(wsm q)`, combined through the radius-separated mean-pin (`C·ε_cov < ε/2`) and the
Chebyshev engine (`wz_pi_nonuniform_concentration_tendsto`, `δ = ε/2`) by a strict triangle
inequality. The `hκ'_pos`/`hκ'_sum`/`hqStar` hypotheses are full-support / proper-pmf /
`qStar`–`κ'` consistency preconditions (used to place `qStar ∈ stdSimplex` and identify the
conditional mean), not the concentration conclusion — not load-bearing; the proof is sorryAx-free.

@audit:ok -/
lemma wz_covering_uyBand_condSlice_le
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (hκ'_pos : ∀ x u, 0 < κ' x u)
    (hκ'_sum : ∀ x, ∑ u, κ' x u = 1)
    (hqStar : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
    (ε : ℝ) (hε : 0 < ε) (tol : ℝ) (htol : 0 < tol) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (M : ℕ)
        (c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k))
        (xb : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}}),
        (fun i ↦ (xb i, c.decoder (c.encoder xb) i)) ∈
            stronglyTypicalSet (rdAmbient qStar)
              (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n
              (wzCoveringStrongRadius P_XY κ' ε) →
        (Measure.pi (fun i ↦ ChannelCoding.pmfToMeasure
            (fun y : β ↦ P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')}))).real
          { yb : Fin n → β | (fun i ↦ (c.decoder (c.encoder xb) i, yb i))
              ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
                  (ChannelCoding.jointSequence ChannelCoding.iidXs
                    (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                      ((ChannelCoding.iidYs i ω :
                          {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))) n ε }
          ≤ tol / 8 := by
  classical
  -- Side-information coercion `Yc` (βs ↪ β) lifted to the joint relabel `Φ (u, y') = (u, ↑y')`.
  set Yc : ℕ → (ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) → β :=
    fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
      ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β) with hYc_def
  set Φ : Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}} → Fin k × β :=
    fun p ↦ (p.1, (p.2 : β)) with hΦ_def
  -- Regularity of the side-information marginal `wsm`.
  have hmem_wsm : wzSideInfoMarginal P_XY κ'
      ∈ stdSimplex ℝ (Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) :=
    wzSideInfoMarginal_mem_stdSimplex P_XY κ' hκ'_pos hκ'_sum
  haveI hne_βs : Nonempty {y : β // 0 < ∑ x, P_XY.real {(x, y)}} :=
    wzSideInfoMarginal_subtype_nonempty P_XY
  haveI hne_prod : Nonempty (Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) :=
    Finset.univ_nonempty_iff.mp
      (Finset.nonempty_of_sum_ne_zero (by rw [hmem_wsm.2]; exact one_ne_zero))
  haveI hne_k : Nonempty (Fin k) := hne_prod.map Prod.fst
  haveI hamb_prob : IsProbabilityMeasure (rdAmbient (wzSideInfoMarginal P_XY κ')) :=
    rdAmbient_isProbabilityMeasure _ hmem_wsm
  -- `qStar ∈ stdSimplex` (from consistency with the full-support proper pmf `κ'`).
  have hmem_q : qStar ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k) := by
    obtain ⟨_, _, hstd⟩ := wz_restrictedCoveringJoint_pos P_XY κ' hκ'_pos hκ'_sum
    rwa [show qStar = (fun p ↦ κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)}) from funext hqStar]
  -- Relabel properties.
  have hΦ_inj : Function.Injective Φ := by
    intro a b hab
    have hab' : (a.1, (a.2 : β)) = (b.1, (b.2 : β)) := hab
    have hcomp := (Prod.mk.injEq _ _ _ _).mp hab'
    exact Prod.ext_iff.mpr ⟨hcomp.1, Subtype.val_injective hcomp.2⟩
  have hΦ_meas : Measurable Φ :=
    measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
  have hjoint_meas : Measurable (ChannelCoding.jointSequence ChannelCoding.iidXs
      ChannelCoding.iidYs 0 (α := Fin k) (β := {y : β // 0 < ∑ x, P_XY.real {(x, y)}})) :=
    ChannelCoding.measurable_jointSequence _ _
      (fun i ↦ ChannelCoding.measurable_iidXs i) (fun i ↦ ChannelCoding.measurable_iidYs i) 0
  have hjointYc_meas : Measurable (ChannelCoding.jointSequence ChannelCoding.iidXs Yc 0) :=
    ChannelCoding.measurable_jointSequence _ _
      (fun i ↦ ChannelCoding.measurable_iidXs i)
      (fun i ↦ measurable_subtype_coe.comp (ChannelCoding.measurable_iidYs i)) 0
  -- `jointSequence iidXs Yc 0 = Φ ∘ (jointSequence iidXs iidYs 0)` (definitional).
  have hYceq : ChannelCoding.jointSequence ChannelCoding.iidXs Yc 0
      = fun ω ↦ Φ (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs 0 ω) := by
    funext ω; rfl
  -- Coerced joint-law singleton values (positive / off-image).
  have hlaw_pos : ∀ (u : Fin k) (ys : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}),
      ((rdAmbient (wzSideInfoMarginal P_XY κ')).map
          (ChannelCoding.jointSequence ChannelCoding.iidXs Yc 0)).real {(u, ys.1)}
        = wzSideInfoMarginal P_XY κ' (u, ys) := by
    intro u ys
    rw [hYceq]
    have hbase := wz_map_injective_real_singleton (rdAmbient (wzSideInfoMarginal P_XY κ'))
      (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs 0)
      hjoint_meas Φ hΦ_inj hΦ_meas (u, ys)
    rw [rdAmbient_map_jointSequence _ hmem_wsm, pmfToMeasure_real_singleton hmem_wsm] at hbase
    exact hbase
  have hlaw_zero : ∀ (u : Fin k) (y : β), ¬ (0 < ∑ x, P_XY.real {(x, y)}) →
      ((rdAmbient (wzSideInfoMarginal P_XY κ')).map
          (ChannelCoding.jointSequence ChannelCoding.iidXs Yc 0)).real {(u, y)} = 0 := by
    intro u y hy
    rw [map_measureReal_apply hjointYc_meas (MeasurableSet.singleton _)]
    have hpre : (ChannelCoding.jointSequence ChannelCoding.iidXs Yc 0) ⁻¹' {(u, y)}
        = (∅ : Set _) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hω
      apply hy
      have h2 : ((ChannelCoding.iidYs 0 ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β) = y :=
        congrArg Prod.snd hω
      rw [← h2]
      exact (ChannelCoding.iidYs 0 ω).2
    rw [hpre, measureReal_empty]
  -- Uniform sup-bound `B = ∑_q |log wsm(q)|` and the entropy identity.
  set B : ℝ := ∑ q : Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}},
    |Real.log (wzSideInfoMarginal P_XY κ' q)| with hB_def
  have hB_nonneg : 0 ≤ B := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hH : entropy (rdAmbient (wzSideInfoMarginal P_XY κ'))
        (ChannelCoding.jointSequence ChannelCoding.iidXs Yc 0)
      = ∑ q, Real.negMulLog (wzSideInfoMarginal P_XY κ' q) := by
    rw [hYceq, wz_entropy_map_injective (rdAmbient (wzSideInfoMarginal P_XY κ'))
        (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs 0)
        hjoint_meas Φ hΦ_inj hΦ_meas]
    unfold entropy
    rw [rdAmbient_map_jointSequence _ hmem_wsm]
    exact Finset.sum_congr rfl fun q _ ↦ by rw [pmfToMeasure_real_singleton hmem_wsm]
  -- `C · ε_cov < ε/2` (radius separation).
  have hkey := wz_covering_uyBand_key P_XY κ' ε hε
  -- Uniform Chebyshev threshold from the concentration engine (δ = ε/2, tol = tol/8).
  obtain ⟨N, hN⟩ := wz_pi_nonuniform_concentration_tendsto (β := β)
    (B := B) (δ := ε / 2) (tol := tol / 8) (by linarith) (by linarith) hB_nonneg
  refine ⟨N, fun n hn M c xb hgood ↦ ?_⟩
  set U := c.decoder (c.encoder xb) with hU_def
  set ψ : Fin n → β → ℝ :=
    fun i y ↦ pmfLog (rdAmbient (wzSideInfoMarginal P_XY κ'))
      (ChannelCoding.jointSequence ChannelCoding.iidXs Yc) (U i, y) with hψ_def
  -- The conditional side-information law is a probability measure.
  have hdens_std : ∀ i, (fun y : β ↦ P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')})
      ∈ stdSimplex ℝ β := by
    intro i
    refine ⟨fun y ↦ div_nonneg measureReal_nonneg
      (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg), ?_⟩
    rw [← Finset.sum_div, div_self (xb i).2.ne']
  haveI hν_prob : ∀ i, IsProbabilityMeasure (ChannelCoding.pmfToMeasure
      (fun y : β ↦ P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')})) :=
    fun i ↦ ChannelCoding.pmfToMeasure_isProbabilityMeasure (hdens_std i)
  -- B1: uniform sup-bound on `ψ`.
  have hB1 : ∀ i y, |ψ i y| ≤ B := by
    intro i y
    show |pmfLog (rdAmbient (wzSideInfoMarginal P_XY κ'))
        (ChannelCoding.jointSequence ChannelCoding.iidXs Yc) (U i, y)| ≤ B
    rw [show pmfLog (rdAmbient (wzSideInfoMarginal P_XY κ'))
          (ChannelCoding.jointSequence ChannelCoding.iidXs Yc) (U i, y)
        = - Real.log (((rdAmbient (wzSideInfoMarginal P_XY κ')).map
            (ChannelCoding.jointSequence ChannelCoding.iidXs Yc 0)).real {(U i, y)}) from rfl]
    by_cases hy : 0 < ∑ x, P_XY.real {(x, y)}
    · rw [hlaw_pos (U i) ⟨y, hy⟩, abs_neg]
      exact Finset.single_le_sum (f := fun q ↦ |Real.log (wzSideInfoMarginal P_XY κ' q)|)
        (fun q _ ↦ abs_nonneg _)
        (Finset.mem_univ ((U i, ⟨y, hy⟩) :
          Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}))
    · rw [hlaw_zero (U i) y hy, Real.log_zero, neg_zero, abs_zero]
      exact hB_nonneg
  -- B2: conditional mean of `ψ_i` equals the kernel `g(xb_i, U_i)`.
  have hint : ∀ i, ∫ y, ψ i y ∂(ChannelCoding.pmfToMeasure
        (fun y : β ↦ P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')}))
      = wzCondMeanKernel P_XY κ' (xb i, U i) := by
    intro i
    rw [integral_fintype Integrable.of_finite]
    simp_rw [pmfToMeasure_real_singleton (hdens_std i), smul_eq_mul]
    -- ψ_i on the positive-`Y`-marginal subtype is `−log wsm(U_i, ·)`.
    have hψval : ∀ ys : {y : β // 0 < ∑ x, P_XY.real {(x, y)}},
        ψ i ys.1 = - Real.log (wzSideInfoMarginal P_XY κ' (U i, ys)) := by
      intro ys
      show pmfLog (rdAmbient (wzSideInfoMarginal P_XY κ'))
          (ChannelCoding.jointSequence ChannelCoding.iidXs Yc) (U i, ys.1)
        = - Real.log (wzSideInfoMarginal P_XY κ' (U i, ys))
      rw [show pmfLog (rdAmbient (wzSideInfoMarginal P_XY κ'))
            (ChannelCoding.jointSequence ChannelCoding.iidXs Yc) (U i, ys.1)
          = - Real.log (((rdAmbient (wzSideInfoMarginal P_XY κ')).map
              (ChannelCoding.jointSequence ChannelCoding.iidXs Yc 0)).real {(U i, ys.1)}) from rfl,
          hlaw_pos (U i) ys]
    -- The `β`-sum collapses onto the positive-`Y`-marginal subtype (excluded `y` carry mass 0).
    have hβsub : (∑ y : β,
          (P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')}) * ψ i y)
        = ∑ ys : {y : β // 0 < ∑ x, P_XY.real {(x, y)}},
            (P_XY.real {((xb i).1, ys.1)} / ∑ y', P_XY.real {((xb i).1, y')}) * ψ i ys.1 := by
      letI : DecidablePred (fun y : β ↦ 0 < ∑ x, P_XY.real {(x, y)}) := Classical.decPred _
      rw [← Finset.sum_subtype (Finset.univ.filter (fun y : β ↦ 0 < ∑ x, P_XY.real {(x, y)}))
            (fun y ↦ by simp)
            (fun y ↦ (P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')}) * ψ i y)]
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro y _ hy
      rw [Finset.mem_filter] at hy
      push_neg at hy
      have hz : ∑ x, P_XY.real {(x, y)} = 0 :=
        le_antisymm (hy (Finset.mem_univ y)) (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg)
      have hp0 : P_XY.real {((xb i).1, y)} = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ measureReal_nonneg)).mp hz (xb i).1
          (Finset.mem_univ _)
      rw [hp0, zero_div, zero_mul]
    rw [hβsub]
    unfold wzCondMeanKernel
    refine Finset.sum_congr rfl fun ys _ ↦ ?_
    rw [hψval ys]
  -- Mean identification and mean-pin `< ε/2`.
  have hpin := wz_covering_uyBand_mean_pin P_XY κ' qStar hmem_q hqStar ε hε xb U ψ hint hgood hkey
  -- The Chebyshev engine bounds the deviation set; the atypical band is included in it.
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
    (hN n hn
      (fun i ↦ ChannelCoding.pmfToMeasure
        (fun y : β ↦ P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')}))
      hν_prob ψ hB1)
  intro yb hyb
  simp only [Set.mem_setOf_eq, mem_typicalSet_iff, not_lt] at hyb
  simp only [Set.mem_setOf_eq]
  -- Triangle inequality: `ε ≤ |A − H|`, `|Mstat − H| < ε/2` ⟹ `ε/2 ≤ |A − Mstat|`.
  have htri := abs_sub_le
    ((∑ i, ψ i (yb i)) / (n : ℝ))
    ((∑ i, ∫ y, ψ i y ∂(ChannelCoding.pmfToMeasure
        (fun y : β ↦ P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')}))) / (n : ℝ))
    (∑ q, Real.negMulLog (wzSideInfoMarginal P_XY κ' q))
  rw [hH] at hyb
  linarith [hyb, htri, hpin]

end InformationTheory.Shannon
