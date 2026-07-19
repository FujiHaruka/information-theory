import InformationTheory.Shannon.WynerZiv.Achievability.SourceTransport

/-!
# Wyner–Ziv achievability — source→ambient AEP mass transport and entropy helpers (Leg E-mass)
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

/-! ### Leg E-mass helpers — source→ambient transport of the per-codeword AEP mass bound

The per-covering-codeword side-information typicality mass, taken under the Wyner–Ziv source
product measure `Measure.pi (source per-coord)` on `α' × β`, is transported to the abstract
per-codeword AEP bound `wz_covering_codeword_sideInfo_mass_le` (D2) on the side-information
ambient `rdAmbient (wzSideInfoMarginal P_XY κ')` over the positive-`Y`-marginal subtype `β'`.
The transport combines (a) the `n`-fold side-information-law agreement (the source's `Y`-law is
the `β`-image of the ambient's `β'`-`Y`-law), and (b) the entropy → `wzMutualInfoYU` exponent
bridge. The generic injective-map helpers preserve `entropy` and per-atom mass under the
`β' → β` coercion (the source lives over full `β`, the ambient over the subtype). -/


/-- Ambient entropy of the covering codeword `U` equals the `negMulLog`-sum of the `U`-marginal
of `wzSideInfoMarginal`. -/
private lemma wz_entropy_ambient_iidXs
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} [Nonempty (Fin k)] (κ' : α → Fin k → ℝ)
    (hκ'pos : ∀ x u, 0 < κ' x u) (hκ'sum : ∀ x, ∑ u, κ' x u = 1) :
    entropy (rdAmbient (wzSideInfoMarginal P_XY κ')) (ChannelCoding.iidXs (α := Fin k) 0)
      = ∑ u, Real.negMulLog (marginalFst (wzSideInfoMarginal P_XY κ') u) := by
  haveI : Nonempty {y : β // 0 < ∑ x, P_XY.real {(x, y)}} :=
    wzSideInfoMarginal_subtype_nonempty P_XY
  have hq := wzSideInfoMarginal_mem_stdSimplex P_XY κ' hκ'pos hκ'sum
  unfold entropy
  refine Finset.sum_congr rfl (fun u _ ↦ ?_)
  congr 1
  rw [rdAmbient_map_iidXs (wzSideInfoMarginal P_XY κ') hq,
      pmfToMeasure_map_fst_real_singleton hq u]

/-- Ambient entropy of the side information `Y` equals the `negMulLog`-sum of the `β'`-`Y`-marginal
of `wzSideInfoMarginal`. -/
private lemma wz_entropy_ambient_iidYs
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} [Nonempty (Fin k)] (κ' : α → Fin k → ℝ)
    (hκ'pos : ∀ x u, 0 < κ' x u) (hκ'sum : ∀ x, ∑ u, κ' x u = 1) :
    entropy (rdAmbient (wzSideInfoMarginal P_XY κ')) (ChannelCoding.iidYs (α := Fin k) 0)
      = ∑ y', Real.negMulLog (marginalSnd (wzSideInfoMarginal P_XY κ') y') := by
  haveI : Nonempty {y : β // 0 < ∑ x, P_XY.real {(x, y)}} :=
    wzSideInfoMarginal_subtype_nonempty P_XY
  have hq := wzSideInfoMarginal_mem_stdSimplex P_XY κ' hκ'pos hκ'sum
  unfold entropy
  refine Finset.sum_congr rfl (fun y' _ ↦ ?_)
  congr 1
  rw [rdAmbient_map_iidYs (wzSideInfoMarginal P_XY κ') hq,
      pmfToMeasure_map_snd_real_singleton hq y']

/-- Ambient joint entropy `H(U, Y)` equals the `negMulLog`-sum of `wzSideInfoMarginal`. -/
private lemma wz_entropy_ambient_joint
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} [Nonempty (Fin k)] (κ' : α → Fin k → ℝ)
    (hκ'pos : ∀ x u, 0 < κ' x u) (hκ'sum : ∀ x, ∑ u, κ' x u = 1) :
    entropy (rdAmbient (wzSideInfoMarginal P_XY κ'))
        (ChannelCoding.jointSequence ChannelCoding.iidXs (ChannelCoding.iidYs (α := Fin k)) 0)
      = ∑ p, Real.negMulLog (wzSideInfoMarginal P_XY κ' p) := by
  haveI : Nonempty {y : β // 0 < ∑ x, P_XY.real {(x, y)}} :=
    wzSideInfoMarginal_subtype_nonempty P_XY
  have hq := wzSideInfoMarginal_mem_stdSimplex P_XY κ' hκ'pos hκ'sum
  unfold entropy
  refine Finset.sum_congr rfl (fun p _ ↦ ?_)
  congr 1
  rw [rdAmbient_map_jointSequence (wzSideInfoMarginal P_XY κ') hq,
      ChannelCoding.pmfToMeasure_real_singleton hq p]

/-- Exponent bridge: `mutualInfoPmf (wzMarginalYU q') = mutualInfoPmf (wzSideInfoMarginal)`, i.e.
the full-`β` `(Y, U)`-marginal of `q'` and the `β'`-subtype `wzSideInfoMarginal` carry the same
mutual information (the `β`-values outside `β'` have zero mass, `negMulLog 0 = 0`). -/
private lemma wz_mutualInfoPmf_wzMarginalYU_eq
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ) (hκ'pos : ∀ x u, 0 < κ' x u) (hκ'sum : ∀ x, ∑ u, κ' x u = 1)
    (q' : α × β × Fin k → ℝ)
    (hfact_eq : ∀ x y u, q' (x, y, u) = κ' x u * P_XY.real {(x, y)}) :
    mutualInfoPmf (wzMarginalYU (Fin k) q') = mutualInfoPmf (wzSideInfoMarginal P_XY κ') := by
  classical
  have hq1v : ∀ y u, wzMarginalYU (Fin k) q' (y, u) = ∑ x, κ' x u * P_XY.real {(x, y)} := by
    intro y u
    simp only [wzMarginalYU]
    exact Finset.sum_congr rfl (fun x _ ↦ hfact_eq x y u)
  have hq2v : ∀ (u : Fin k) (y' : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}),
      wzSideInfoMarginal P_XY κ' (u, y') = ∑ x, κ' x u * P_XY.real {(x, y'.1)} := fun u y' ↦ rfl
  have hcol0 : ∀ (u : Fin k) (y : β), ¬ (0 < ∑ x, P_XY.real {(x, y)}) →
      (∑ x, κ' x u * P_XY.real {(x, y)}) = 0 := by
    intro u y hy
    have hz : ∑ x, P_XY.real {(x, y)} = 0 :=
      le_antisymm (not_lt.mp hy) (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg)
    refine Finset.sum_eq_zero (fun x _ ↦ ?_)
    have hx0 : P_XY.real {(x, y)} = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ measureReal_nonneg)).mp hz x (Finset.mem_univ x)
    rw [hx0, mul_zero]
  have subsum : ∀ f : β → ℝ, (∀ y, ¬ (0 < ∑ x, P_XY.real {(x, y)}) → f y = 0) →
      (∑ y : β, f y) = ∑ y' : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}, f y'.1 := by
    intro f hf
    letI : DecidablePred (fun y : β ↦ 0 < ∑ x, P_XY.real {(x, y)}) := Classical.decPred _
    rw [← Finset.sum_subtype (Finset.univ.filter (fun y : β ↦ 0 < ∑ x, P_XY.real {(x, y)}))
        (fun y ↦ by simp) (fun y ↦ f y)]
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro y _ hy
    rw [Finset.mem_filter] at hy
    push_neg at hy
    exact hf y (not_lt.mpr (hy (Finset.mem_univ y)))
  have hUmarg : ∀ u : Fin k,
      marginalSnd (wzMarginalYU (Fin k) q') u = marginalFst (wzSideInfoMarginal P_XY κ') u := by
    intro u
    simp only [marginalSnd, marginalFst]
    rw [show (∑ y : β, wzMarginalYU (Fin k) q' (y, u))
          = ∑ y : β, (∑ x, κ' x u * P_XY.real {(x, y)}) from
        Finset.sum_congr rfl (fun y _ ↦ hq1v y u),
        subsum (fun y ↦ ∑ x, κ' x u * P_XY.real {(x, y)}) (fun y hy ↦ hcol0 u y hy)]
    exact Finset.sum_congr rfl (fun y' _ ↦ (hq2v u y').symm)
  have hYmarg : ∀ y' : {y : β // 0 < ∑ x, P_XY.real {(x, y)}},
      marginalFst (wzMarginalYU (Fin k) q') y'.1
        = marginalSnd (wzSideInfoMarginal P_XY κ') y' := by
    intro y'
    simp only [marginalFst, marginalSnd]
    rw [show (∑ u, wzMarginalYU (Fin k) q' (y'.1, u))
          = ∑ u, (∑ x, κ' x u * P_XY.real {(x, y'.1)}) from
        Finset.sum_congr rfl (fun u _ ↦ hq1v y'.1 u)]
    exact Finset.sum_congr rfl (fun u _ ↦ (hq2v u y').symm)
  unfold mutualInfoPmf
  have hFst : (∑ y : β, Real.negMulLog (marginalFst (wzMarginalYU (Fin k) q') y))
      = ∑ y', Real.negMulLog (marginalSnd (wzSideInfoMarginal P_XY κ') y') := by
    rw [subsum (fun y ↦ Real.negMulLog (marginalFst (wzMarginalYU (Fin k) q') y)) ?_]
    · exact Finset.sum_congr rfl (fun y' _ ↦ by rw [hYmarg y'])
    · intro y hy
      have hz : marginalFst (wzMarginalYU (Fin k) q') y = 0 := by
        simp only [marginalFst]
        rw [show (∑ u, wzMarginalYU (Fin k) q' (y, u))
              = ∑ u, (∑ x, κ' x u * P_XY.real {(x, y)}) from
            Finset.sum_congr rfl (fun u _ ↦ hq1v y u)]
        exact Finset.sum_eq_zero (fun u _ ↦ hcol0 u y hy)
      rw [hz, Real.negMulLog_zero]
  have hSnd : (∑ u, Real.negMulLog (marginalSnd (wzMarginalYU (Fin k) q') u))
      = ∑ u, Real.negMulLog (marginalFst (wzSideInfoMarginal P_XY κ') u) :=
    Finset.sum_congr rfl (fun u _ ↦ by rw [hUmarg u])
  have hJoint : (∑ p : β × Fin k, Real.negMulLog (wzMarginalYU (Fin k) q' p))
      = ∑ p : Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}},
          Real.negMulLog (wzSideInfoMarginal P_XY κ' p) := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ ↦ ?_)
    rw [subsum (fun y ↦ Real.negMulLog (wzMarginalYU (Fin k) q' (y, u))) ?_]
    · exact Finset.sum_congr rfl (fun y' _ ↦ by rw [hq1v y'.1 u, ← hq2v u y'])
    · intro y hy
      rw [hq1v y u, hcol0 u y hy, Real.negMulLog_zero]
  rw [hFst, hSnd, hJoint]
  ring


/-- Per-covering-codeword side-information typicality mass, under the source product measure. For
any fixed covering codeword `u : Fin n → Fin k`, the probability — under the Wyner–Ziv source
product measure `Measure.pi` of `p ↦ P_XY{(p.1.1, p.2)}` on `α' × β` — that `u` is jointly typical
(radius `ε`, side-information ambient `rdAmbient (wzSideInfoMarginal P_XY κ')`) with the
side-information block `fun i ↦ (p i).2` is at most `exp(−n · (I(Y;U) − 3ε))`, where
`I(Y;U) = wzMutualInfoYU (Fin k) q'`.

This transports `wz_covering_codeword_sideInfo_mass_le` (D2) from the side-information ambient onto
the source product measure. Two facts do the work. Side-information-law agreement: the source pair
law's `β`-marginal is `y ↦ ∑_x P_XY{(x,y)}`, and the `β`-coerced `β'`-marginal of
`wzSideInfoMarginal` summed over the covering codeword is
`y ↦ ∑_x κ' x u · P_XY{(x,y)} = ∑_x P_XY{(x,y)}` by `hκ'sum`, so the source's `n`-fold `Y`-law is
the `β`-image (`Subtype.val`) of the ambient's `β'`-`Y`-law (`Measure.pi_map_pi` + the iid `n`-fold
law) and the fixed-`u` slice mass is preserved (the `β`-vs-`β'` alphabet gap is absorbed by the
injective coercion, under which `entropy` and `pmfLog` are invariant). Exponent bridge:
`wzMutualInfoYU (Fin k) q'` equals the ambient's `I(U;Y) = H(U)+H(Y)-H(U,Y)` (the `β`-values
outside `β'` carry zero mass, `negMulLog 0 = 0`), which discharges D2's exponent hypothesis at
`I_YU := wzMutualInfoYU q' - 3ε`.

Non-bundled: the conclusion is a per-codeword mass upper bound (`Measure.real {…} ≤ exp …`), the
same shape as D2, not the operational error probability; `hκ'pos`/`hκ'sum`/`hfact_eq` are the
covering-kernel regularity preconditions, and the exponent is pinned to the actual pmf by
`hfact_eq` (no free-exponent gap).

@audit:ok -/
lemma wz_source_codeword_sideInfo_mass_le
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    [Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}}]
    {k : ℕ} [Nonempty (Fin k)]
    (κ' : α → Fin k → ℝ) (hκ'pos : ∀ x u, 0 < κ' x u) (hκ'sum : ∀ x, ∑ u, κ' x u = 1)
    (q' : α × β × Fin k → ℝ)
    (hfact_eq : ∀ x y u, q' (x, y, u) = κ' x u * P_XY.real {(x, y)})
    (ε : ℝ) (hε_pos : 0 < ε) (n : ℕ) (u : Fin n → Fin k) :
    (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
          P_XY.real {(p.1.1, p.2)}))).real
        { p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β |
            (u, fun i ↦ (p i).2)
              ∈ ChannelCoding.jointlyTypicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
                  ChannelCoding.iidXs
                  (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                      ((ChannelCoding.iidYs i ω :
                          {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))
                  n ε }
      ≤ Real.exp (-(n : ℝ) * (wzMutualInfoYU (Fin k) q' - 3 * ε)) := by
  classical
  haveI hne_βs : Nonempty {y : β // 0 < ∑ x, P_XY.real {(x, y)}} :=
    wzSideInfoMarginal_subtype_nonempty P_XY
  have hq := wzSideInfoMarginal_mem_stdSimplex P_XY κ' hκ'pos hκ'sum
  haveI hamb_prob : IsProbabilityMeasure (rdAmbient (wzSideInfoMarginal P_XY κ')) :=
    rdAmbient_isProbabilityMeasure _ hq
  haveI hsrc_prob : IsProbabilityMeasure (ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure (wz_sourcePmf_mem_stdSimplex P_XY)
  -- The injective `β' → β` coercion and its joint `Fin k × β' → Fin k × β` version.
  have hval_inj : Function.Injective
      (Subtype.val : {y : β // 0 < ∑ x, P_XY.real {(x, y)}} → β) := Subtype.val_injective
  have hval_meas : Measurable
      (Subtype.val : {y : β // 0 < ∑ x, P_XY.real {(x, y)}} → β) := measurable_subtype_coe
  have hgj_meas : Measurable (fun p : Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}} ↦
      (p.1, (p.2 : β))) := measurable_fst.prodMk (hval_meas.comp measurable_snd)
  have hgj_inj : Function.Injective (fun p : Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}} ↦
      (p.1, (p.2 : β))) := by
    intro a b hab
    simp only [Prod.mk.injEq] at hab
    exact Prod.ext hab.1 (hval_inj hab.2)
  -- Per-atom `pmfLog` and `entropy` invariance under the coercion.
  have hpmfYeq : ∀ y' : {y : β // 0 < ∑ x, P_XY.real {(x, y)}},
      pmfLog (rdAmbient (wzSideInfoMarginal P_XY κ'))
          (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
            ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)) ((y' : β))
        = pmfLog (rdAmbient (wzSideInfoMarginal P_XY κ')) (ChannelCoding.iidYs (α := Fin k)) y' := by
    intro y'
    simp only [pmfLog]
    rw [wz_map_injective_real_singleton (rdAmbient (wzSideInfoMarginal P_XY κ'))
        (ChannelCoding.iidYs (α := Fin k) 0) (ChannelCoding.measurable_iidYs 0)
        Subtype.val hval_inj hval_meas y']
  have hentYeq : entropy (rdAmbient (wzSideInfoMarginal P_XY κ'))
      (fun ω ↦ ((ChannelCoding.iidYs (α := Fin k) 0 ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))
        = entropy (rdAmbient (wzSideInfoMarginal P_XY κ')) (ChannelCoding.iidYs (α := Fin k) 0) :=
    wz_entropy_map_injective (rdAmbient (wzSideInfoMarginal P_XY κ'))
      (ChannelCoding.iidYs (α := Fin k) 0) (ChannelCoding.measurable_iidYs 0)
      Subtype.val hval_inj hval_meas
  have hpmfJeq : ∀ p : Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}},
      pmfLog (rdAmbient (wzSideInfoMarginal P_XY κ'))
          (ChannelCoding.jointSequence ChannelCoding.iidXs
            (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
              ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)))
          (p.1, (p.2 : β))
        = pmfLog (rdAmbient (wzSideInfoMarginal P_XY κ'))
            (ChannelCoding.jointSequence ChannelCoding.iidXs (ChannelCoding.iidYs (α := Fin k))) p := by
    intro p
    simp only [pmfLog]
    congr 2
    exact wz_map_injective_real_singleton (rdAmbient (wzSideInfoMarginal P_XY κ'))
        (ChannelCoding.jointSequence ChannelCoding.iidXs (ChannelCoding.iidYs (α := Fin k)) 0)
        (ChannelCoding.measurable_jointSequence _ _ (fun i ↦ ChannelCoding.measurable_iidXs i)
          (fun i ↦ ChannelCoding.measurable_iidYs i) 0)
        (fun q : Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}} ↦ (q.1, (q.2 : β)))
        hgj_inj hgj_meas p
  have hentJeq : entropy (rdAmbient (wzSideInfoMarginal P_XY κ'))
      (ChannelCoding.jointSequence ChannelCoding.iidXs
        (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
          ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)) 0)
        = entropy (rdAmbient (wzSideInfoMarginal P_XY κ'))
            (ChannelCoding.jointSequence ChannelCoding.iidXs (ChannelCoding.iidYs (α := Fin k)) 0) :=
    wz_entropy_map_injective (rdAmbient (wzSideInfoMarginal P_XY κ'))
      (ChannelCoding.jointSequence ChannelCoding.iidXs (ChannelCoding.iidYs (α := Fin k)) 0)
      (ChannelCoding.measurable_jointSequence _ _ (fun i ↦ ChannelCoding.measurable_iidXs i)
        (fun i ↦ ChannelCoding.measurable_iidYs i) 0)
      (fun q : Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}} ↦ (q.1, (q.2 : β))) hgj_inj hgj_meas
  -- Typical-set correspondence under the coercion.
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
  have htypJ : ∀ z : Fin n → {y : β // 0 < ∑ x, P_XY.real {(x, y)}},
      ((fun i ↦ (u i, ((z i : β)))) ∈ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
          (ChannelCoding.jointSequence ChannelCoding.iidXs
            (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
              ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))) n ε)
        ↔ ((fun i ↦ (u i, z i)) ∈ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
            (ChannelCoding.jointSequence ChannelCoding.iidXs (ChannelCoding.iidYs (α := Fin k))) n ε) := by
    intro z
    rw [mem_typicalSet_iff, mem_typicalSet_iff]
    have hnum : (∑ i : Fin n, pmfLog (rdAmbient (wzSideInfoMarginal P_XY κ'))
          (ChannelCoding.jointSequence ChannelCoding.iidXs
            (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
              ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)))
          (u i, ((z i : β))))
        = ∑ i : Fin n, pmfLog (rdAmbient (wzSideInfoMarginal P_XY κ'))
            (ChannelCoding.jointSequence ChannelCoding.iidXs (ChannelCoding.iidYs (α := Fin k)))
            (u i, z i) :=
      Finset.sum_congr rfl (fun i _ ↦ hpmfJeq (u i, z i))
    simp only [hnum, hentJeq]
  -- The target set is the `Y`-projection preimage of the fixed-`u` typical fiber.
  have hΦS :
      (fun (z : Fin n → {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) i ↦ ((z i : β))) ⁻¹'
          {y : Fin n → β | (u, y) ∈ ChannelCoding.jointlyTypicalSet
              (rdAmbient (wzSideInfoMarginal P_XY κ')) ChannelCoding.iidXs
              (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)) n ε}
        = {z : Fin n → {y : β // 0 < ∑ x, P_XY.real {(x, y)}} |
            (u, z) ∈ ChannelCoding.jointlyTypicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
              ChannelCoding.iidXs (ChannelCoding.iidYs (α := Fin k)) n ε} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq,
      ChannelCoding.mem_jointlyTypicalSet_iff]
    exact and_congr Iff.rfl (and_congr (htypY z) (htypJ z))
  -- Entropy → `wzMutualInfoYU` exponent bridge.
  have hbridge : wzMutualInfoYU (Fin k) q'
      = entropy (rdAmbient (wzSideInfoMarginal P_XY κ')) (ChannelCoding.iidXs (α := Fin k) 0)
        + entropy (rdAmbient (wzSideInfoMarginal P_XY κ')) (ChannelCoding.iidYs (α := Fin k) 0)
        - entropy (rdAmbient (wzSideInfoMarginal P_XY κ'))
            (ChannelCoding.jointSequence ChannelCoding.iidXs (ChannelCoding.iidYs (α := Fin k)) 0) := by
    rw [wz_entropy_ambient_iidXs P_XY κ' hκ'pos hκ'sum,
        wz_entropy_ambient_iidYs P_XY κ' hκ'pos hκ'sum,
        wz_entropy_ambient_joint P_XY κ' hκ'pos hκ'sum]
    show mutualInfoPmf (wzMarginalYU (Fin k) q') = _
    rw [wz_mutualInfoPmf_wzMarginalYU_eq P_XY κ' hκ'pos hκ'sum q' hfact_eq]
    rfl
  -- Apply D2 on the side-information ambient over the subtype `β'`.
  have hD2 := wz_covering_codeword_sideInfo_mass_le
      (rdAmbient (wzSideInfoMarginal P_XY κ')) ChannelCoding.iidXs
      (ChannelCoding.iidYs (α := Fin k)) ε hε_pos
      (fun i ↦ ChannelCoding.measurable_iidXs i) (fun i ↦ ChannelCoding.measurable_iidYs i)
      (rdAmbient_iIndepFun_iidXs _ hq) (rdAmbient_identDistrib_iidXs _ hq)
      (rdAmbient_iIndepFun_iidYs _ hq) (rdAmbient_identDistrib_iidYs _ hq)
      (fun x ↦ rdAmbient_iidXs_real_singleton_pos _ hq (wzSideInfoMarginal_pos P_XY κ' hκ'pos) x)
      (fun y ↦ rdAmbient_iidYs_real_singleton_pos _ hq (wzSideInfoMarginal_pos P_XY κ' hκ'pos) y)
      (fun p ↦ rdAmbient_jointSequence_real_singleton_pos _ hq
        (wzSideInfoMarginal_pos P_XY κ' hκ'pos) p)
      (wzMutualInfoYU (Fin k) q' - 3 * ε)
      (le_of_eq (by rw [hbridge])) u
  -- Measure reconciliation: the source `n`-fold `Y`-law is the `β`-image of the ambient's.
  haveI : IsProbabilityMeasure ((ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})).map
      Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  haveI : IsProbabilityMeasure ((rdAmbient (wzSideInfoMarginal P_XY κ')).map
      (ChannelCoding.iidYs (α := Fin k) 0)) :=
    Measure.isProbabilityMeasure_map (ChannelCoding.measurable_iidYs 0).aemeasurable
  haveI : IsProbabilityMeasure (((rdAmbient (wzSideInfoMarginal P_XY κ')).map
      (ChannelCoding.iidYs (α := Fin k) 0)).map Subtype.val) :=
    Measure.isProbabilityMeasure_map hval_meas.aemeasurable
  have hmeaseq : (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))).map
        (fun p (i : Fin n) ↦ (p i).2)
      = ((rdAmbient (wzSideInfoMarginal P_XY κ')).map
          (jointRV (ChannelCoding.iidYs (α := Fin k)) n)).map
          (fun (z : Fin n → {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) i ↦ ((z i : β))) := by
    rw [wz_ambient_jointRV_iidYs_eq_pi P_XY κ' hκ'pos hκ'sum n,
        Measure.pi_map_pi (hμ := fun _ ↦ inferInstance) (fun _ ↦ hval_meas.aemeasurable),
        Measure.pi_map_pi (hμ := fun _ ↦ inferInstance) (fun _ ↦ measurable_snd.aemeasurable)]
    refine congrArg Measure.pi (funext (fun _ ↦ ?_))
    exact wz_source_snd_eq_ambient_snd_map P_XY κ' hκ'pos hκ'sum
  -- Assemble the mass-transport chain.
  have hYproj_meas : Measurable (fun p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
      fun i ↦ (p i).2) :=
    measurable_pi_lambda _ (fun i ↦ measurable_snd.comp (measurable_pi_apply i))
  have hΦ_meas : Measurable (fun z : Fin n → {y : β // 0 < ∑ x, P_XY.real {(x, y)}} ↦
      fun i ↦ ((z i : β))) :=
    measurable_pi_lambda _ (fun i ↦ hval_meas.comp (measurable_pi_apply i))
  have hjrv_meas : Measurable (jointRV (ChannelCoding.iidYs (α := Fin k)
      (β := {y : β // 0 < ∑ x, P_XY.real {(x, y)}})) n) :=
    measurable_jointRV _ (fun i ↦ ChannelCoding.measurable_iidYs i) n
  rw [show { p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β |
        (u, fun i ↦ (p i).2)
          ∈ ChannelCoding.jointlyTypicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
              ChannelCoding.iidXs
              (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                  ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)) n ε }
      = (fun p (i : Fin n) ↦ (p i).2) ⁻¹' {y : Fin n → β | (u, y) ∈
          ChannelCoding.jointlyTypicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
            ChannelCoding.iidXs
            (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)) n ε} from rfl,
      ← map_measureReal_apply hYproj_meas (Set.toFinite _).measurableSet,
      hmeaseq,
      map_measureReal_apply hΦ_meas (Set.toFinite _).measurableSet,
      hΦS,
      map_measureReal_apply hjrv_meas (Set.toFinite _).measurableSet]
  exact hD2

private lemma wz_E2_confusion_threshold (R R₁ IYU δ : ℝ) (hδ : 0 < δ) (d : DistortionFn α γ)
    (hc : R₁ - IYU < R) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      2 * Real.exp ((m : ℝ) * (R₁ - IYU)) * ((codebookSize R m : ℝ))⁻¹
        ≤ δ / 2 / (8 * (distortionMax d + 1)) := by
  have hdd : (0 : ℝ) ≤ distortionMax d := distortionMax_nonneg d
  have hL := wz_tendsto_exp_mul_codebookSize_inv hc
  have h2 : Filter.Tendsto
      (fun m : ℕ ↦ 2 * (Real.exp ((m : ℝ) * (R₁ - IYU)) * ((codebookSize R m : ℝ))⁻¹))
      Filter.atTop (nhds 0) := by
    have := hL.const_mul (2 : ℝ); simpa using this
  have htol : 0 < δ / 2 / (8 * (distortionMax d + 1)) :=
    div_pos (div_pos hδ (by norm_num)) (by positivity)
  rw [Metric.tendsto_atTop] at h2
  obtain ⟨N, hN⟩ := h2 (δ / 2 / (8 * (distortionMax d + 1))) htol
  refine ⟨N, fun m hm ↦ ?_⟩
  have hd := hN m hm
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (Real.exp ((m : ℝ) * (R₁ - IYU))
      * ((codebookSize R m : ℝ))⁻¹))] at hd
  rw [mul_assoc]
  exact le_of_lt hd

/-- Codebook-restricted confusion (E2) probability is squeezable. For a covering codebook of size
`M₁ ≲ exp(n·R₁)` and `n` beyond a threshold, at the shared conditional-typicality radius `ε` (an
explicit input, pinned to the covering-acceptance mass precondition and used as the bin-decoder
radius) there is a derandomized index binning `f` making the bin-decoder confusion probability so
small that `distortionMax dα' · Pr[E2] ≤ δ/4`. Combines the binning-averaged confusion exponent
(S5b `wz_codebook_confusion_expectation_le`, fed D2 `wz_covering_codeword_sideInfo_mass_le` +
collision `wzIndexBinningMeasure_collision`, instantiated over the positive-`Y`-marginal subtype
`β'`), the binning derandomization, and the exponent squeeze (`hε_conf : R₁ − I(Y;U) + 3·ε < R`),
with the source ↔ side-info-ambient identification.

The full event `{bin decoder fails to recover the true covering word}` decomposes as
`E2 ⊆ E2b {some other bin member typical, confusion} ∪ C2 {true word not jointly typical,
covering-acceptance failure}`. Two hypotheses are therefore load-free preconditions, not the
analytic core: the covering codebook size upper bound `(M₁ : ℝ) ≤ exp(n·R₁) + 1` (the confusion
count scales with the number of codewords, so the E2b squeeze needs `M₁` capped near
`⌈exp(n·R₁)⌉`, the size the covering theorem actually produces), and the pinned covering-acceptance
mass `hcov_accept` (a precondition-exposure of the covering code's own S5a/gateway-2 property,
discharged by the covering atom). The radius `ε` is pinned at a single explicit value; the huge-`ε`
regime that makes `wzCoveringAcceptFailSet` vacuously empty is excluded by `hε_conf`
(`wzCoveringAcceptFailSet`'s mass is monotone decreasing in `ε`), and `dα'` is tied to `d` by
`hd'_link : ∀ x' g, dα' x' g = d x'.1 g` (so `distortionMax dα' ≤ distortionMax d`).

The body is sorry-free: it proves `{decoder ≠ true word} ⊆ C2 ∪ E2b`
(`wzBinTypicalDecoder_eq_of_unique` contrapositive), bounds C2 by the pinned `hcov_accept` premise,
chooses `f` by one derandomization (`exists_le_integral` over `wzIndexBinningMeasure` fed the S5b
confusion bound, whose per-codeword mass is `wz_source_codeword_sideInfo_mass_le`), and squeezes the
confusion exponent to `0` (`wz_tendsto_exp_mul_codebookSize_inv`; the degenerate `M₁ ≤ 1` covering
has an empty confusion event, handled by `Subsingleton (Fin M₁)`), then scales by
`distortionMax dα' ≤ distortionMax d`. -/
lemma wz_exists_binning_E2_bound
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    [Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}}]
    (d : DistortionFn α γ) (R : ℝ) {k : ℕ} [Nonempty (Fin k)]
    (κ' : α → Fin k → ℝ) (hκ'pos : ∀ x u, 0 < κ' x u) (hκ'sum : ∀ x, ∑ u, κ' x u = 1)
    (q' : α × β × Fin k → ℝ)
    (hfact_eq : ∀ x y u, q' (x, y, u) = κ' x u * P_XY.real {(x, y)})
    (R₁ : ℝ) (ε : ℝ) (hε_pos : 0 < ε)
    (hε_conf : R₁ - wzMutualInfoYU (Fin k) q' + 3 * ε < R)
    (qf : (α × β × Fin k → ℝ) × (Fin k × β → γ))
    (dα' : DistortionFn {x : α // 0 < ∑ y, P_XY.real {(x, y)}} γ)
    (hd'_link : ∀ x' g, dα' x' g = d x'.1 g)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N_E2 : ℕ, ∀ n : ℕ, N_E2 ≤ n →
      ∀ (M₁ : ℕ) (c₁ : LossyCode M₁ n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k)),
        (M₁ : ℝ) ≤ Real.exp ((n : ℝ) * R₁) + 1 →
        (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
            (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
              P_XY.real {(p.1.1, p.2)}))).real
          (wzCoveringAcceptFailSet P_XY κ' c₁ ε)
          ≤ δ / 2 / (8 * (distortionMax d + 1)) →
        ∃ f : Fin M₁ → Fin (codebookSize R n),
          distortionMax dα' *
            (Measure.pi (fun _ : Fin n ↦
                ChannelCoding.pmfToMeasure (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
                    P_XY.real {(p.1.1, p.2)}))).real
              { p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β |
                  wzBinTypicalDecoder (rdAmbient (wzSideInfoMarginal P_XY κ'))
                      ChannelCoding.iidXs
                      (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                          ((ChannelCoding.iidYs i ω :
                              {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))
                      ε c₁ f
                      (f (c₁.encoder (fun j ↦ (p j).1)), fun i ↦ (p i).2)
                    ≠ c₁.decoder (c₁.encoder (fun j ↦ (p j).1)) }
            ≤ δ / 4 := by
  classical
  -- The per-codeword AEP exponent supplied by D2 (transported to the source measure).
  set IYU : ℝ := wzMutualInfoYU (Fin k) q' - 3 * ε with hIYU_def
  -- Confusion decay (term A): `2·exp(m·(R₁−IYU))·(codebookSize R m)⁻¹ → 0`, since
  -- `R₁ − IYU = R₁ − I(Y;U) + 3ε < R` (`hε_conf`).  The degenerate `M₁ ≤ 1` covering (empty
  -- confusion) is handled separately in the body, so only this single-exponential term is needed.
  obtain ⟨N_E2, hN_E2⟩ := wz_E2_confusion_threshold R R₁ IYU δ hδ d
    (by rw [hIYU_def]; linarith [hε_conf])
  refine ⟨N_E2, fun n hn M₁ c₁ hM_ub hcov_accept ↦ ?_⟩
  -- Fixed-`n` abbreviations.
  haveI hQ_prob : IsProbabilityMeasure
      (ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure (wz_QXY_mem_stdSimplex P_XY)
  set SRC : Measure (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
    with hSRC_def
  set AMB : Measure (ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) :=
    rdAmbient (wzSideInfoMarginal P_XY κ') with hAMB_def
  set iidYs' : ℕ → (ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) → β :=
    fun i ω ↦ ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)
    with hiidYs'_def
  set jts : Set ((Fin n → Fin k) × (Fin n → β)) :=
    ChannelCoding.jointlyTypicalSet AMB ChannelCoding.iidXs iidYs' n ε with hjts_def
  have hjts_meas : MeasurableSet jts :=
    ChannelCoding.measurableSet_jointlyTypicalSet AMB ChannelCoding.iidXs iidYs' n ε
  -- The covering index of the source block, and the side-information block RV.
  set trueIdx : (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) → Fin M₁ :=
    fun p ↦ c₁.encoder (fun j ↦ (p j).1) with htrueIdx_def
  set Ys : ℕ → (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) → β :=
    fun i p ↦ if h : i < n then (p ⟨i, h⟩).2 else Classical.arbitrary β with hYs_def
  have hjointRV : ∀ p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β,
      jointRV Ys n p = fun i ↦ (p i).2 := by
    intro p; funext i
    simp only [jointRV, hYs_def, i.isLt, dif_pos]
  -- STEP A (derandomize + S5b): a good binning `f` with confusion mass ≤ the count/bin ratio.
  haveI hSRC_prob : IsProbabilityMeasure SRC := by rw [hSRC_def]; infer_instance
  haveI hcs_ne : NeZero (codebookSize R n) := ⟨(codebookSize_pos R n).ne'⟩
  have hYs_meas : ∀ i, Measurable (Ys i) := fun i ↦ measurable_of_finite _
  have htrueIdx_meas : Measurable trueIdx := measurable_of_finite _
  -- Per-covering-codeword AEP mass (D2 transported to the source measure).
  have hmass : ∀ m' : Fin M₁,
      SRC.real {p | (c₁.decoder m', jointRV Ys n p) ∈ jts}
        ≤ Real.exp (-(n : ℝ) * IYU) := by
    intro m'
    have hset : {p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β |
          (c₁.decoder m', jointRV Ys n p) ∈ jts}
        = {p | (c₁.decoder m', fun i ↦ (p i).2) ∈ jts} := by
      ext p; simp only [Set.mem_setOf_eq, hjointRV]
    rw [hset, hIYU_def]
    exact wz_source_codeword_sideInfo_mass_le P_XY κ' hκ'pos hκ'sum q' hfact_eq
      ε hε_pos n (c₁.decoder m')
  -- STEP A (derandomize + S5b): a good binning `f` with confusion mass ≤ the count/bin ratio.
  obtain ⟨f, hf⟩ : ∃ f : Fin M₁ → Fin (codebookSize R n),
      SRC.real {p | ∃ m' : Fin M₁, m' ≠ trueIdx p ∧ f m' = f (trueIdx p)
          ∧ (c₁.decoder m', jointRV Ys n p) ∈ jts}
        ≤ (M₁ : ℝ) * Real.exp (-(n : ℝ) * IYU) * ((codebookSize R n : ℝ))⁻¹ := by
    set binMeas := wzIndexBinningMeasure M₁ (codebookSize R n) with hbin_def
    have hG_int : Integrable
        (fun g : Fin M₁ → Fin (codebookSize R n) ↦
          SRC.real {p | ∃ m' : Fin M₁, m' ≠ trueIdx p ∧ g m' = g (trueIdx p)
            ∧ (c₁.decoder m', jointRV Ys n p) ∈ jts}) binMeas :=
      Integrable.of_finite
    obtain ⟨f, hf_le⟩ := MeasureTheory.exists_le_integral hG_int
    refine ⟨f, le_trans hf_le ?_⟩
    have hcoll : ∀ m' m : Fin M₁, m' ≠ m →
        binMeas.real {g | g m' = g m} = ((codebookSize R n : ℝ))⁻¹ :=
      fun m' m h ↦ wzIndexBinningMeasure_collision h
    exact wz_codebook_confusion_expectation_le SRC Ys c₁ trueIdx
      hYs_meas htrueIdx_meas binMeas jts hjts_meas IYU hmass hcoll
  refine ⟨f, ?_⟩
  -- STEP B (set inclusion): the decoder recovers the true word off `C2 ∪ E2b`.
  have hFAIL_incl :
      { p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β |
          wzBinTypicalDecoder AMB ChannelCoding.iidXs iidYs' ε c₁ f
              (f (c₁.encoder (fun j ↦ (p j).1)), fun i ↦ (p i).2)
            ≠ c₁.decoder (c₁.encoder (fun j ↦ (p j).1)) }
        ⊆ wzCoveringAcceptFailSet P_XY κ' c₁ ε
          ∪ {p | ∃ m' : Fin M₁, m' ≠ trueIdx p ∧ f m' = f (trueIdx p)
              ∧ (c₁.decoder m', jointRV Ys n p) ∈ jts} := by
    intro p hp
    rw [Set.mem_union]
    by_contra hpc
    push_neg at hpc
    obtain ⟨hpC2, hpE2b⟩ := hpc
    apply hp
    have htrue : (c₁.decoder (c₁.encoder (fun j ↦ (p j).1)), fun i ↦ (p i).2) ∈ jts := by
      by_contra hcon
      exact hpC2 hcon
    have hunique : ∀ u : Fin n → Fin k,
        (∃ m' : Fin M₁, f m' = f (c₁.encoder (fun j ↦ (p j).1)) ∧ c₁.decoder m' = u) →
        (u, fun i ↦ (p i).2) ∈ jts →
        u = c₁.decoder (c₁.encoder (fun j ↦ (p j).1)) := by
      rintro u ⟨m', hfm', hdec⟩ htyp
      by_contra hne
      refine hpE2b ⟨m', ?_, hfm', ?_⟩
      · intro hm'eq
        exact hne (by rw [← hdec, hm'eq])
      · rw [hdec, hjointRV]; exact htyp
    have hrec := wzBinTypicalDecoder_eq_of_unique AMB ChannelCoding.iidXs iidYs' ε c₁ f
      (m₁ := c₁.encoder (fun j ↦ (p j).1)) (y := fun i ↦ (p i).2)
      (by rw [← hjointRV] at htrue ⊢; exact htrue) ?_
    · exact hrec
    · intro u hex htyp
      exact hunique u hex htyp
  -- STEP C (measure subadditivity + hypotheses + threshold).
  have hmeas_le :
      SRC.real
        { p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β |
            wzBinTypicalDecoder AMB ChannelCoding.iidXs iidYs' ε c₁ f
                (f (c₁.encoder (fun j ↦ (p j).1)), fun i ↦ (p i).2)
              ≠ c₁.decoder (c₁.encoder (fun j ↦ (p j).1)) }
        ≤ SRC.real (wzCoveringAcceptFailSet P_XY κ' c₁ ε)
          + SRC.real {p | ∃ m' : Fin M₁, m' ≠ trueIdx p ∧ f m' = f (trueIdx p)
              ∧ (c₁.decoder m', jointRV Ys n p) ∈ jts} := by
    refine le_trans (measureReal_mono hFAIL_incl (by
      exact measure_union_ne_top (measure_ne_top _ _) (measure_ne_top _ _))) ?_
    exact measureReal_union_le _ _
  -- STEP D (arithmetic).  `distortionMax dα' ≤ distortionMax d`, and each half ≤ `δ/16`.
  have hdMax_le : distortionMax dα' ≤ distortionMax d := by
    unfold distortionMax
    refine Finset.sup'_le _ _ (fun q _ ↦ ?_)
    rw [hd'_link]
    exact Finset.le_sup' (f := fun ab : α × γ ↦ ((d ab.1 ab.2 : NNReal) : ℝ))
      (Finset.mem_univ (q.1.1, q.2))
  have hdMax_nn : 0 ≤ distortionMax dα' := distortionMax_nonneg dα'
  have hd_nn : 0 ≤ distortionMax d := distortionMax_nonneg d
  have hC2 : SRC.real (wzCoveringAcceptFailSet P_XY κ' c₁ ε)
      ≤ δ / 2 / (8 * (distortionMax d + 1)) := hcov_accept
  have hE2b : SRC.real {p | ∃ m' : Fin M₁, m' ≠ trueIdx p ∧ f m' = f (trueIdx p)
        ∧ (c₁.decoder m', jointRV Ys n p) ∈ jts}
      ≤ δ / 2 / (8 * (distortionMax d + 1)) := by
    by_cases hM1 : 2 ≤ M₁
    · -- `M₁ ≥ 2` ⇒ `exp(n·R₁) ≥ 1`, so `M₁ ≤ 2·exp(n·R₁)`; term-A decay finishes.
      have hM2 : (2 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM1
      have hexp1 : (1 : ℝ) ≤ Real.exp ((n : ℝ) * R₁) := by linarith [hM_ub, hM2]
      have hM1bound : (M₁ : ℝ) ≤ 2 * Real.exp ((n : ℝ) * R₁) := by linarith [hM_ub, hexp1]
      refine le_trans hf (le_trans ?_ (hN_E2 n hn))
      calc (M₁ : ℝ) * Real.exp (-(n : ℝ) * IYU) * ((codebookSize R n : ℝ))⁻¹
          ≤ (2 * Real.exp ((n : ℝ) * R₁)) * Real.exp (-(n : ℝ) * IYU)
              * ((codebookSize R n : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hM1bound (Real.exp_nonneg _)) (by positivity)
        _ = 2 * Real.exp ((n : ℝ) * (R₁ - IYU)) * ((codebookSize R n : ℝ))⁻¹ := by
            rw [mul_assoc 2, ← Real.exp_add,
              show (n : ℝ) * R₁ + -(n : ℝ) * IYU = (n : ℝ) * (R₁ - IYU) from by ring]
    · -- `M₁ ≤ 1` ⇒ the confusion event is empty.
      push_neg at hM1
      haveI hsub : Subsingleton (Fin M₁) := by
        rw [Fin.subsingleton_iff_le_one]; omega
      have hempty : {p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β |
          ∃ m' : Fin M₁, m' ≠ trueIdx p ∧ f m' = f (trueIdx p)
            ∧ (c₁.decoder m', jointRV Ys n p) ∈ jts} = ∅ := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
        rintro m' ⟨hne, -, -⟩
        exact hne (Subsingleton.elim m' (trueIdx p))
      rw [hempty, measureReal_empty]
      exact le_of_lt (div_pos (div_pos hδ (by norm_num)) (by positivity))
  have hden_pos : 0 < 8 * (distortionMax d + 1) := by positivity
  calc distortionMax dα' *
        SRC.real
          { p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β |
              wzBinTypicalDecoder AMB ChannelCoding.iidXs iidYs' ε c₁ f
                  (f (c₁.encoder (fun j ↦ (p j).1)), fun i ↦ (p i).2)
                ≠ c₁.decoder (c₁.encoder (fun j ↦ (p j).1)) }
      ≤ distortionMax dα' *
          (δ / 2 / (8 * (distortionMax d + 1)) + δ / 2 / (8 * (distortionMax d + 1))) :=
        mul_le_mul_of_nonneg_left (le_trans hmeas_le (add_le_add hC2 hE2b)) hdMax_nn
    _ ≤ distortionMax d *
          (δ / 2 / (8 * (distortionMax d + 1)) + δ / 2 / (8 * (distortionMax d + 1))) :=
        mul_le_mul_of_nonneg_right hdMax_le (by positivity)
    _ ≤ δ / 4 := by
        have hXne : (8 * (distortionMax d + 1)) ≠ 0 := ne_of_gt hden_pos
        have hkey : distortionMax d * (δ / 2 / (8 * (distortionMax d + 1))
              + δ / 2 / (8 * (distortionMax d + 1)))
            = distortionMax d * δ / (8 * (distortionMax d + 1)) := by
          field_simp
          ring
        rw [hkey, div_le_iff₀ hden_pos]
        nlinarith [mul_nonneg hd_nn hδ.le, hδ.le]

/-- Per-`n` Wyner–Ziv code family at a fixed covering rate (Steps 2–7). Given the Step 1–2 covering
data together with an already-chosen covering rate `R₁` (strictly above `I(X;U)`, so that `hcov₁` —
the covering `LossyCode` family at rate `R₁` — is available) and the net-rate gap
`hsplit : R₁ − I(Y;U) < R`, assemble the per-`n` Wyner–Ziv code family at the operational rate `R`:
bin the covering index down to `codebookSize R n` messages (`wzIndexBinningMeasure`), decode by the
bin conditional-typicality search (S3 `wzCodeOfCoveringBinning` / S4 `wzBinTypicalDecoder`), bound
the covering-failure (S5a `wz_covering_failure_prob_le`, fed the mass lower bound via gateway 2
`wz_covering_sideInfo_mass_ge`) and the codebook-restricted decoder-confusion (S5b
`wz_codebook_confusion_expectation_le`, fed the per-codeword mass upper bound via D2
`wz_covering_codeword_sideInfo_mass_le` and the collision `wzIndexBinningMeasure_collision`) error
events, extract a good deterministic codebook + binning by double derandomization, squeeze the
residual distortion excess to `0`, and extend the covering code `α' → α` (S7 `wzLiftSupportCode`).

No error-probability or decoder-correctness claim is a hypothesis: `hcov₁` is the
separately-established rate-distortion covering `LossyCode` family at covering rate `R₁`
(≈ `I(X;U)`), not the binned `WynerZivCode` at operational rate `R`; the index binning, the bin
decoder, and the
confusion exponent are the residual body work. The distortion budget is split so `hfeas`/`hcov₁`
target `D + δ/2`, reserving `δ/2` for the finite-`n` error terms (mirrors the rate-distortion sister
`rate_distortion_achievability`): the WZ distortion decomposes as a good-event proxy +
`distortionMax d · (P[E1]+P[E2])`, so the reserved slack is absorbed by the error exponents
(S5a/S5b/D2 → 0). Three preconditions are definitional/regularity, not load-bearing on the
operational conclusion: `hd'_eq` pins the covering proxy `d'` to `𝔼_{Y|X}[d ∘ qf.2]` (killing the
`d' := 0` counterexample, where the real WZ distortion under `d ∘ qf.2` would be unconstrained),
`hqf` supplies the test channel's `WynerZivFactorizableConstraint` membership (the Markov `U-X-Y`
structure), and `hcov₁` exposes the covering size bounds `⌈exp(n·R₁)⌉ ≤ M ≤ exp(n·R₁) + 1` (the E2
squeeze needs `M` capped above, the ceiling size the covering theorem actually produces). All are
discharged by construction at `wz_coveringFamily_of_testChannel`. `hobj'`/`hsplit`/`hfeas` are
objective/feasibility/rate preconditions; positivity and simplex membership are regularity. -/
lemma wz_perN_covering_binning_code
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (k : ℕ) (qf : (α × β × Fin k → ℝ) × (Fin k × β → γ))
    (δ : ℝ) (hδ : 0 < δ)
    (q' : α × β × Fin k → ℝ) (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (d' : DistortionFn {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k))
    (R₁ : ℝ)
    (hfact_eq : ∀ x y u, q' (x, y, u) = κ' x u * P_XY.real {(x, y)})
    (hκ'pos : ∀ x u, 0 < κ' x u)
    (hκ'sum : ∀ x, ∑ u, κ' x u = 1)
    (hobj' : wzMutualInfoXU (Fin k) q' - wzMutualInfoYU (Fin k) q' < R)
    (hqStar_eq : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
    (hqStar_pos : ∀ p, 0 < qStar p)
    (hqStar_mem : qStar ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k))
    (hfeas : expectedDistortionPmf d' qStar ≤ D + δ / 2)
    (hd'_eq : ∀ x' u, d' x' u = Real.toNNReal (∑ y : β,
        (P_XY.real {(x'.1, y)} / ∑ y' : β, P_XY.real {(x'.1, y')})
          * ((d x'.1 (qf.2 (u, y)) : NNReal) : ℝ)))
    (hqf : qf ∈ WynerZivFactorizableConstraint (Fin k)
            (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D)
    (hsplit : R₁ - wzMutualInfoYU (Fin k) q' < R)
    (hcov₁ : ∀ ε' : ℝ, 0 < ε' → ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ M : ℕ,
          Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M ∧
          (M : ℝ) ≤ Real.exp ((n : ℝ) * R₁) + 1 ∧
          ∃ c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k),
            c.expectedBlockDistortion
                ((rdAmbient qStar).map (ChannelCoding.iidXs 0)) d'
              ≤ (D + δ / 2) + ε'
            ∧ (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
                  (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
                    P_XY.real {(p.1.1, p.2)}))).real
                (wzCoveringAcceptFailSet P_XY κ' c ε)
                ≤ δ / 2 / (8 * (distortionMax d + 1))) :
    ∃ N : ℕ, ∀ n : ℕ, ∃ c : WynerZivCode (codebookSize R n) n α β γ,
      N ≤ n → c.expectedBlockDistortion P_XY d ≤ D + δ := by
  classical
  -- The auxiliary covering alphabet is nonempty (the row-stochastic kernel of the
  -- factorizable test channel forces `k > 0`).
  haveI hkne : Nonempty (Fin k) := wz_nonempty_of_factorizable hqf.1
  -- Reduce the `∃ N, ∀ n, ∃ c, N ≤ n → …` conclusion to the per-`n` (for `n ≥ N`)
  -- code-existence claim; the `n < N` branch is discharged by an arbitrary inhabitant of
  -- `WynerZivCode` (available since `[Nonempty γ]` and `codebookSize R n > 0`).
  suffices hfam : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ c : WynerZivCode (codebookSize R n) n α β γ,
        c.expectedBlockDistortion P_XY d ≤ D + δ by
    obtain ⟨N, hN⟩ := hfam
    refine ⟨N, fun n ↦ ?_⟩
    by_cases hn : N ≤ n
    · obtain ⟨c, hc⟩ := hN n hn
      exact ⟨c, fun _ ↦ hc⟩
    · exact ⟨{ encoder := fun _ ↦ ⟨0, codebookSize_pos R n⟩,
                decoder := fun _ _ ↦ Classical.arbitrary γ },
             fun hle ↦ absurd hle hn⟩
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Analytic core (Legs A–D). Six-step assembly; STEP 1 (covering-side derandomize) and
  -- STEP 6 outer packaging (the `wzLiftSupportCode` factorization) are genuine glue below;
  -- STEPS 1'–5 + inner Step 6 are genuine analytic work, all closed sorry-free.
  -- ═══════════════════════════════════════════════════════════════════════════
  -- The source-support subtype `α'` is nonempty (its `stdSimplex` pmf `qStar` has total
  -- mass `1 ≠ 0`), so it has an inhabitant `x₀` for the `α' → α` support lift and the
  -- `Nonempty α'` instance the E2-squeeze adapter (A3) needs.
  haveI hne_prod :
      Nonempty ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k) :=
    Finset.univ_nonempty_iff.mp
      (Finset.nonempty_of_sum_ne_zero (by rw [hqStar_mem.2]; exact one_ne_zero))
  haveI hneα' : Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}} :=
    hne_prod.map Prod.fst
  -- STEP 1 (derandomize, covering side — genuine).  Feed `hcov₁` at slack `ε' := δ/4` to
  -- obtain the covering threshold `N_cov` and, for every `n ≥ N_cov`, the covering codebook
  -- `c₁ : LossyCode M n α' (Fin k)` whose covering distortion — over the i.i.d. covering
  -- ambient `(rdAmbient qStar).map (iidXs 0)`, w.r.t. the proxy `d'` — is `≤ (D+δ/2)+δ/4`,
  -- with codebook size `M ≥ ⌈exp(n·R₁)⌉`.
  -- Choose the shared conditional-typicality radius `ε` from the rate gap `hsplit`.  The
  -- covering-acceptance mass (C2) and the decoder-confusion (E2b) are bound at the SAME
  -- radius `ε`; the huge-`ε` regime that makes `wzCoveringAcceptFailSet` vacuously empty is
  -- excluded by `hε_conf : R₁ − I(Y;U) + 3·ε < R` (`3·ε = gap/2 < gap`).
  set ε : ℝ := (R - (R₁ - wzMutualInfoYU (Fin k) q')) / 6 with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; linarith [hsplit]
  have hε_conf : R₁ - wzMutualInfoYU (Fin k) q' + 3 * ε < R := by rw [hε_def]; linarith [hsplit]
  obtain ⟨N_cov, hN_cov⟩ := hcov₁ (δ / 4) (div_pos hδ (by norm_num)) ε hε_pos
  -- STEP 4 / 1' (binning-side derandomize + E2 squeeze, Leg D A3).  Obtain the confusion
  -- threshold `N_E2`: beyond it, for a covering codebook of size `M ≲ exp(n·R₁)`, a good
  -- binning `f` (radius `ε`) makes `distortionMax dα' · Pr[E2] ≤ δ/4`.
  obtain ⟨N_E2, hN_E2⟩ :=
    wz_exists_binning_E2_bound P_XY d R κ' hκ'pos hκ'sum q' hfact_eq R₁ ε hε_pos hε_conf qf
      (fun (x' : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) g ↦ d x'.1 g) (fun _ _ ↦ rfl) δ hδ
  refine ⟨max N_cov N_E2, fun n hn ↦ ?_⟩
  obtain ⟨M, hM_ge, hM_ub, c₁, hc₁_dist, hAccept⟩ := hN_cov n (le_trans (le_max_left _ _) hn)
  have x₀ : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} := Classical.arbitrary _
  -- ═══════════════════════════════════════════════════════════════════════════
  -- STEP 6 (outer packaging — genuine).  The Wyner–Ziv code is the `α' → α` support lift
  -- (`wzLiftSupportCode`) of a support-restricted code `codeSupp` over the source-support
  -- subtype `α'`.  This factors the α-side conclusion through the α'-side construction; the
  -- remaining source-measure transport / proxy reconciliation (the *inner* half of Step 6)
  -- lives inside the `codeSupp` existential below.
  -- ═══════════════════════════════════════════════════════════════════════════
  suffices hsupp : ∃ codeSupp : WynerZivCode (codebookSize R n) n
      {x : α // 0 < ∑ y, P_XY.real {(x, y)}} β γ,
      (wzLiftSupportCode P_XY x₀ codeSupp).expectedBlockDistortion P_XY d ≤ D + δ by
    obtain ⟨codeSupp, hcodeSupp⟩ := hsupp
    exact ⟨wzLiftSupportCode P_XY x₀ codeSupp, hcodeSupp⟩
  -- ═══════════════════════════════════════════════════════════════════════════
  -- STEPS 1'–5 + inner Step 6 (E2-only assembly via the Leg D adapters G2/A1/A2/A3):
  --   A3 (`hN_E2`) → binning `f` + radius `ε` with `distortionMax dα' · Pr[E2] ≤ δ/4`;
  --   A1 (`wz_lift_expectedBlockDistortion_eq`)  : lift identity `P_XY,d ↦ Q_XY,dα'`;
  --   G2 (`wz_expectedBlockDistortion_le_ideal_add_E2`) : actual ≤ ideal + dMax·Pr[E2];
  --   A2 (`wz_ideal_expectation_eq_covering`) : ideal = covering distortion ≤ (D+δ/2)+δ/4.
  -- Arithmetic: ((D+δ/2)+δ/4) + δ/4 = D+δ.
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Covering codebook size cap (M-direction).  The confusion count scales with the number
  -- of covering codewords, so A3 needs `M ≲ exp(n·R₁)`.  The matching upper bound
  -- `(M : ℝ) ≤ exp(n·R₁) + 1` is the size the covering theorem actually produces (`M =
  -- ⌈exp(n·R₁)⌉`, `Nat.ceil_lt_add_one`); it is threaded through `hcov₁` (Leg C.6), so
  -- `hM_ub` is now supplied by the covering family together with the codebook `c₁`.
  obtain ⟨f, hE2⟩ := hN_E2 n (le_trans (le_max_right _ _) hn) M c₁ hM_ub hAccept
  -- The co-restricted source measure `Q_XY` is a probability measure.
  haveI hQ_prob : IsProbabilityMeasure
      (ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure (wz_QXY_mem_stdSimplex P_XY)
  -- Assemble the support-restricted covering + binning code and bound its distortion.
  refine ⟨wzCodeOfCoveringBinning c₁ f qf.2
      (wzBinTypicalDecoder (rdAmbient (wzSideInfoMarginal P_XY κ')) ChannelCoding.iidXs
        (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
            ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))
        ε c₁ f), ?_⟩
  rw [wz_lift_expectedBlockDistortion_eq P_XY d x₀ _]
  calc (wzCodeOfCoveringBinning c₁ f qf.2
          (wzBinTypicalDecoder (rdAmbient (wzSideInfoMarginal P_XY κ')) ChannelCoding.iidXs
            (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))
            ε c₁ f)).expectedBlockDistortion
          (ChannelCoding.pmfToMeasure
            (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
          (fun (x' : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) g ↦ d x'.1 g)
      ≤ (∫ p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β,
            blockDistortion (fun (x' : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) g ↦ d x'.1 g) n
              (fun i ↦ (p i).1)
              (fun i ↦ qf.2 (c₁.decoder (c₁.encoder (fun j ↦ (p j).1)) i, (p i).2))
          ∂(Measure.pi (fun _ : Fin n ↦
              ChannelCoding.pmfToMeasure
                (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
                  P_XY.real {(p.1.1, p.2)}))))
        + distortionMax (fun (x' : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) g ↦ d x'.1 g)
          * (Measure.pi (fun _ : Fin n ↦
                ChannelCoding.pmfToMeasure
                  (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
                    P_XY.real {(p.1.1, p.2)}))).real
              { p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β |
                  wzBinTypicalDecoder (rdAmbient (wzSideInfoMarginal P_XY κ'))
                      ChannelCoding.iidXs
                      (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                          ((ChannelCoding.iidYs i ω :
                              {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))
                      ε c₁ f
                      (f (c₁.encoder (fun j ↦ (p j).1)), fun i ↦ (p i).2)
                    ≠ c₁.decoder (c₁.encoder (fun j ↦ (p j).1)) } :=
        wz_expectedBlockDistortion_le_ideal_add_E2 (rdAmbient (wzSideInfoMarginal P_XY κ'))
          ChannelCoding.iidXs
          (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
              ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))
          ε c₁ f qf.2 (fun (x' : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) g ↦ d x'.1 g)
          (ChannelCoding.pmfToMeasure
            (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
    _ = c₁.expectedBlockDistortion ((rdAmbient qStar).map (ChannelCoding.iidXs 0)) d'
          + distortionMax (fun (x' : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) g ↦ d x'.1 g)
            * (Measure.pi (fun _ : Fin n ↦
                  ChannelCoding.pmfToMeasure
                    (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
                      P_XY.real {(p.1.1, p.2)}))).real
                { p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β |
                    wzBinTypicalDecoder (rdAmbient (wzSideInfoMarginal P_XY κ'))
                        ChannelCoding.iidXs
                        (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                            ((ChannelCoding.iidYs i ω :
                                {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))
                        ε c₁ f
                        (f (c₁.encoder (fun j ↦ (p j).1)), fun i ↦ (p i).2)
                      ≠ c₁.decoder (c₁.encoder (fun j ↦ (p j).1)) } := by
        rw [wz_ideal_expectation_eq_covering P_XY d κ' hκ'sum qStar hqStar_eq hqStar_mem d' qf
          hd'_eq c₁]
    _ ≤ ((D + δ / 2) + δ / 4) + δ / 4 := by linarith [hc₁_dist, hE2]
    _ = D + δ := by ring

end InformationTheory.Shannon
