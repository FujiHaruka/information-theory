import InformationTheory.Shannon.WynerZiv.Achievability.Concentration

/-!
# Wyner–Ziv achievability — the Markov core
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

open ChannelCoding in
/-- Correlated-joint conditional-typicality concentration (the Markov core). For `n` large the
source-measure mass of {covering-success ∧ `(x,y)`-block jointly typical ∧ `(u,y)`-block jointly
`(U,Y)`-atypical} is at most `tol/8`. This is the Markov lemma `U—X—Y`: under SRC the pairs
`(x_i,y_i)` are iid `~ P_XY` and `u = c.decoder(c.encoder x)` is a deterministic function of the
whole `x`-block, so `Y ⊥ U ∣ X`; given `(x,u)` typical (covering success, empirical conditional
`≈ κ'(·∣x)`) AND `(x,y)` typical, the empirical `(u,y)`-entropy concentrates around
`H(wzSideInfoMarginal)` (the consistent `(U,Y)`-marginal pinned by `hqStar`/`hκ'_sum`), so
`(u,y)`-atypicality has vanishing mass. Because `wzSideInfoMarginal(u,y) = ∑ₓ κ'(x,u)·P_XY(x,y)`
is a sum over `x`, the empirical `(u,y)`-entropy is not a linear combination of the `(x,u)`- and
`(x,y)`-empirical entropies, so this is genuinely probabilistic (a conditional AEP), not a
deterministic set-inclusion.

The consistency + full-support hyps (`hκ'_pos`, `hκ'_sum`, `hqStar`) are mandatory: they pin
`qStar`'s `U`-marginal to `wzSideInfoMarginal`'s `U`-marginal `= P_U`; without them a constant-word
or entropy-preserving-relabel counterexample makes the statement false. The covering-success event
`wzCoveringSuccessStrong P_XY κ' qStar c ε` is strong joint typicality at the smaller radius
`ε_cov = wzCoveringStrongRadius P_XY κ' ε = ε/(2(1 + C))` (amplification constant
`C = ∑_{x,u} |g(x,u)|`), intersected with weak `jointlyTypicalSet` at radius `ε`. The radius
separation pins the conditional-mean statistic `M(xb) = ⟨type_xu, g⟩` to within `< ε/2` of
`H(wzSideInfoMarginal)` uniformly over the entire `ε_cov`-ball (a universal triangle bound);
composed with the conditional-AEP concentration at deviation `δ = ε/2`, the `(u,y)` empirical
entropy stays within `ε` of `H(wsm)`, i.e. not in the atypical band `Euy`. Strong typicality at
the *same* radius
`ε` would leave an `O(ε)` partial-relabel class open, so the separation is essential; the weak
conjunct is retained so the `U`-typicality plumbing `wz_covering_success_subset_uTypical` works at
radius `ε`. The analytic core is the conditional-AEP kernel `wz_covering_uyBand_condSlice_le`.

@audit:ok -/
private lemma wz_covering_jointBand_markov_core
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (ε : ℝ) (hε : 0 < ε) (tol : ℝ) (htol : 0 < tol)
    (hκ'_pos : ∀ x u, 0 < κ' x u)
    (hκ'_sum : ∀ x, ∑ u, κ' x u = 1)
    (hqStar : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)}) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (M : ℕ)
        (c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k)),
        (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
            (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
              P_XY.real {(p.1.1, p.2)}))).real
          ((wzCoveringSuccessStrong P_XY κ' qStar c ε
            ∩ typicalSet (rdAmbient
                (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
                (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n ε)
            ∩ { p | (fun i ↦ (c.decoder (c.encoder (fun j ↦ (p j).1)) i, (p i).2))
                ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
                    (ChannelCoding.jointSequence ChannelCoding.iidXs
                      (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                        ((ChannelCoding.iidYs i ω :
                            {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))) n ε })
          ≤ tol / 8 := by
  classical
  obtain ⟨N, hN⟩ :=
    wz_covering_uyBand_condSlice_le P_XY κ' qStar hκ'_pos hκ'_sum hqStar ε hε tol htol
  refine ⟨N, fun n hn M c ↦ ?_⟩
  set S : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    (wzCoveringSuccessStrong P_XY κ' qStar c ε
      ∩ typicalSet (rdAmbient
          (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
          (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n ε)
      ∩ { p | (fun i ↦ (c.decoder (c.encoder (fun j ↦ (p j).1)) i, (p i).2))
          ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
              (ChannelCoding.jointSequence ChannelCoding.iidXs
                (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                  ((ChannelCoding.iidYs i ω :
                      {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))) n ε } with hS_def
  rw [wz_srcBlock_condMeasure_split P_XY S]
  -- The total `x`-block mass is `1` (marginalization of the source pmf over the `x`-alphabet).
  have hmass : ∑ xb : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}},
      ∏ i, (∑ y : β, P_XY.real {((xb i).1, y)}) = 1 := by
    have hg1 : ∑ x : {x : α // 0 < ∑ y, P_XY.real {(x, y)}},
        (∑ y : β, P_XY.real {(x.1, y)}) = 1 := by
      have hstd := (wz_QXY_mem_stdSimplex P_XY).2
      rwa [Fintype.sum_prod_type] at hstd
    have heq := Fintype.prod_sum
      (fun (_ : Fin n) (x : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) ↦
        ∑ y : β, P_XY.real {(x.1, y)})
    rw [← heq]
    simp only [hg1, Finset.prod_const_one]
  -- Per-`x`-block: the conditional side-info mass of the slice is `≤ tol/8` (good `xb`: the
  -- conditional AEP; bad `xb`: the slice is empty because covering-success fails).
  have hterm : ∀ xb : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}},
      (Measure.pi (fun i ↦ ChannelCoding.pmfToMeasure
          (fun y : β ↦ P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')}))).real
          {yb | (fun i ↦ (xb i, yb i)) ∈ S} ≤ tol / 8 := by
    intro xb
    haveI hcondprob : IsProbabilityMeasure (Measure.pi (fun i ↦ ChannelCoding.pmfToMeasure
        (fun y : β ↦ P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')}))) := by
      haveI : ∀ i, IsProbabilityMeasure (ChannelCoding.pmfToMeasure
          (fun y : β ↦ P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')})) := by
        intro i
        refine ChannelCoding.pmfToMeasure_isProbabilityMeasure ⟨fun y ↦ ?_, ?_⟩
        · exact div_nonneg measureReal_nonneg (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg)
        · rw [← Finset.sum_div, div_self (xb i).2.ne']
      infer_instance
    by_cases hgood : (fun i ↦ (xb i, c.decoder (c.encoder xb) i)) ∈
        stronglyTypicalSet (rdAmbient qStar)
          (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n
          (wzCoveringStrongRadius P_XY κ' ε)
    · -- Good `xb`: the slice lies in the `(U,Y)`-atypical set, bounded by the conditional AEP.
      refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (hN n hn M c xb hgood)
      intro yb hyb
      simp only [hS_def, Set.mem_setOf_eq, Set.mem_inter_iff] at hyb
      exact hyb.2
    · -- Bad `xb`: covering-success fails, so the slice is empty.
      have hempty : {yb : Fin n → β | (fun i ↦ (xb i, yb i)) ∈ S} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro yb hyb
        simp only [Set.mem_setOf_eq, hS_def, wzCoveringSuccessStrong, Set.mem_inter_iff] at hyb
        exact hgood hyb.1.1.1
      rw [hempty, measureReal_empty]
      linarith
  refine (Finset.sum_le_sum (fun xb _ ↦
    mul_le_mul_of_nonneg_left (hterm xb)
      (Finset.prod_nonneg fun i _ ↦ Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg))).trans
    (le_of_eq ?_)
  rw [← Finset.sum_mul, hmass, one_mul]

open ChannelCoding in
/-- Joint `(U,Y)`-band concentration (the hard kernel). For `n` large the source-measure mass of
the event {covering-success ∧ the chosen word `U` and the side information `Y` are jointly
`(U,Y)`-atypical} is at most `tol/4`. This is the correlated-joint conditional-typicality
concentration — the Markov lemma. `U = c.decoder (c.encoder x)` is a function of the whole
`x`-block, so `(U_i, Y_i)` is neither iid nor independent, and the plain `aep_chebyshev_bound`
(`Rate.lean:108`) does not apply. The consistency + full-support hypotheses (`hκ'_pos`, `hκ'_sum`,
`hqStar`) are mandatory: without them the statement is false (a constant-word counterexample; see
the core-lemma docstring). Proved by a case split on `(X,Y)`-joint typicality (atypical ↦
`wz_covering_xyBand_aep`, typical ↦ the Markov core `wz_covering_jointBand_markov_core`) and a
union bound.

@audit:ok -/
private lemma wz_covering_jointBand_concentration
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (ε : ℝ) (hε : 0 < ε) (tol : ℝ) (htol : 0 < tol)
    (hκ'_pos : ∀ x u, 0 < κ' x u)
    (hκ'_sum : ∀ x, ∑ u, κ' x u = 1)
    (hqStar : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)}) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (M : ℕ)
        (c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k)),
        (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
            (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
              P_XY.real {(p.1.1, p.2)}))).real
          (wzCoveringSuccessStrong P_XY κ' qStar c ε
            ∩ { p | (fun i ↦ (c.decoder (c.encoder (fun j ↦ (p j).1)) i, (p i).2))
                ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
                    (ChannelCoding.jointSequence ChannelCoding.iidXs
                      (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                        ((ChannelCoding.iidYs i ω :
                            {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))) n ε })
          ≤ tol / 4 := by
  classical
  obtain ⟨N1, hN1⟩ := wz_covering_xyBand_aep P_XY ε hε tol htol
  obtain ⟨N2, hN2⟩ :=
    wz_covering_jointBand_markov_core P_XY κ' qStar ε hε tol htol hκ'_pos hκ'_sum hqStar
  refine ⟨max N1 N2, fun n hn M c ↦ ?_⟩
  have hn1 : N1 ≤ n := (le_max_left _ _).trans hn
  have hn2 : N2 ≤ n := (le_max_right _ _).trans hn
  have hxy := hN1 n hn1
  have hmk := hN2 n hn2 M c
  haveI hQ_prob : IsProbabilityMeasure (ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure (wz_QXY_mem_stdSimplex P_XY)
  set SRC : Measure (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
    with hSRC_def
  haveI hSRC_prob : IsProbabilityMeasure SRC := by rw [hSRC_def]; infer_instance
  set Ecov : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    wzCoveringSuccessStrong P_XY κ' qStar c ε with hEcov_def
  set Exytyp : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    typicalSet (rdAmbient
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
      (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n ε with hExytyp_def
  set Euy : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    { p | (fun i ↦ (c.decoder (c.encoder (fun j ↦ (p j).1)) i, (p i).2))
        ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
            (ChannelCoding.jointSequence ChannelCoding.iidXs
              (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))) n ε }
    with hEuy_def
  -- Case split on the (X,Y)-joint typicality: atypical ↦ part-1, typical ↦ part-2 (Markov core).
  have hincl : Ecov ∩ Euy ⊆ Exytypᶜ ∪ (Ecov ∩ Exytyp ∩ Euy) := by
    rintro p ⟨hcov, huy⟩
    by_cases hxt : p ∈ Exytyp
    · exact Or.inr ⟨⟨hcov, hxt⟩, huy⟩
    · exact Or.inl hxt
  have hunion : SRC.real (Exytypᶜ ∪ (Ecov ∩ Exytyp ∩ Euy))
      ≤ SRC.real Exytypᶜ + SRC.real (Ecov ∩ Exytyp ∩ Euy) := measureReal_union_le _ _
  have hmono : SRC.real (Ecov ∩ Euy) ≤ SRC.real (Exytypᶜ ∪ (Ecov ∩ Exytyp ∩ Euy)) :=
    measureReal_mono hincl (measure_ne_top _ _)
  linarith [hxy, hmk, hunion, hmono]

/-! ## Covering chosen-word side-information acceptance (Markov lemma)

For the covering `LossyCode` `c`, the *correlated joint source* mass of the acceptance-failure
event `wzCoveringAcceptFailSet` — the event that the chosen covering word `c.decoder (c.encoder x)`
is not jointly typical with the side information `y` (with `(x, y)` drawn from the true joint
`P_XY`, so `x` and `y` are correlated) — is small, given only the covering-typicality success
precondition (the chosen word covers the source `x`, a regularity precondition on the constructed
code, not the acceptance conclusion).

Its analytic core is the **Markov lemma**: if the chosen word `u = c.decoder (c.encoder x)`
typically covers `x` and the source pair `(x, y)` is jointly typical, then `(u, y)` is jointly
typical — so acceptance fails only off the (exp-small) covering-failure ∪ source-atypicality set.
The measure is the *correlated* joint source
`Measure.pi (pmfToMeasure (fun (x', y) ↦ P_XY{(x'.1, y)}))`; crucially the covering word
`c.decoder (c.encoder x)` is a function of the source `x`, so the `u`–`y` correlation that makes
acceptance likely is inherited from the `x`–`y` correlation and is destroyed by fixing `u`
independently. The lemma `wz_covering_sideInfo_mass_ge` (a *lower* bound on the *independent*
product-`Y`-law slice mass) and the broadcast confusion bound `bc_conditional_slice_prob_le`
(an *upper* bound on a *conditional-product* typical slice, the confusion/wrong-codeword direction)
are on the wrong measure/direction and do not supply this. -/

open ChannelCoding in
/-- The Markov-lemma core: the correlated-joint-source mass of the event that the chosen covering
word `u = c.decoder (c.encoder x)` *typically covers* the source `x` (jointly typical in the
covering ambient `rdAmbient qStar`) yet *fails acceptance* (`(u, y)` not jointly typical in the
side-information ambient) is at most `tol/2` for `n` large. Intersecting with the covering-success
set makes the statement self-contained.

The Markov-concentration truth requires `qStar` to be the `κ'`-consistent covering joint
`qStar (x', u) = κ' x'.1 u · (∑ y, P_XY{(x'.1, y)})` with `κ'` full-support (`0 < κ' x u`,
`∑ u κ' x u = 1`); without them the statement is false (a constant-word code with
`qStar := P_X ⊗ δ_{u₀}` satisfies covering-success yet fails acceptance on the whole space). The
consistency relation forces `qStar`'s `U`-marginal `= P_U`, so a mismatched-`U`-marginal code fails
covering-success. Proved by a De Morgan split of acceptance-failure over the three bands
(`Ecov ∩ Euf = ∅` via `wz_covering_success_subset_uTypical`, plus `wz_covering_yBand_aep` and the
outer `wz_covering_jointBand_concentration`) and a union bound.

@audit:ok -/
private lemma wz_covering_markov_concentration
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (ε : ℝ) (hε : 0 < ε) (tol : ℝ) (htol : 0 < tol)
    (hκ'_pos : ∀ x u, 0 < κ' x u)
    (hκ'_sum : ∀ x, ∑ u, κ' x u = 1)
    (hqStar : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)}) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (M : ℕ)
        (c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k)),
        (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
            (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
              P_XY.real {(p.1.1, p.2)}))).real
          (wzCoveringSuccessStrong P_XY κ' qStar c ε
            ∩ wzCoveringAcceptFailSet P_XY κ' c ε)
          ≤ tol / 2 := by
  classical
  obtain ⟨N_Y, hN_Y⟩ := wz_covering_yBand_aep P_XY κ' hκ'_pos hκ'_sum ε hε tol htol
  obtain ⟨N_J, hN_J⟩ :=
    wz_covering_jointBand_concentration P_XY κ' qStar ε hε tol htol hκ'_pos hκ'_sum hqStar
  refine ⟨max N_Y N_J, fun n hn M c ↦ ?_⟩
  have hn_Y : N_Y ≤ n := (le_max_left _ _).trans hn
  have hn_J : N_J ≤ n := (le_max_right _ _).trans hn
  have hyf := hN_Y n hn_Y
  have hjf := hN_J n hn_J M c
  haveI hQ_prob : IsProbabilityMeasure (ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure (wz_QXY_mem_stdSimplex P_XY)
  set SRC : Measure (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
    with hSRC_def
  haveI hSRC_prob : IsProbabilityMeasure SRC := by rw [hSRC_def]; infer_instance
  -- Name the covering-success event and the three band-failure witnesses.
  set Ecov : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    wzCoveringSuccessStrong P_XY κ' qStar c ε with hEcov_def
  set Euf : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    { p | c.decoder (c.encoder (fun j ↦ (p j).1))
        ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ')) ChannelCoding.iidXs n ε }
    with hEuf_def
  set Eyf : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    { p | (fun i ↦ (p i).2) ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
        (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
          ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)) n ε }
    with hEyf_def
  set Ejf : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    { p | (fun i ↦ (c.decoder (c.encoder (fun j ↦ (p j).1)) i, (p i).2))
        ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
            (ChannelCoding.jointSequence ChannelCoding.iidXs
              (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))) n ε }
    with hEjf_def
  -- De Morgan: covering-success ∩ acceptance-failure splits along the three bands.
  have hincl : Ecov ∩ wzCoveringAcceptFailSet P_XY κ' c ε
      ⊆ (Ecov ∩ Euf) ∪ Eyf ∪ (Ecov ∩ Ejf) := by
    intro p hp
    obtain ⟨hcov, hfail⟩ := hp
    rw [wzCoveringAcceptFailSet, Set.mem_setOf_eq,
      ChannelCoding.mem_jointlyTypicalSet_iff] at hfail
    by_cases hu : c.decoder (c.encoder (fun j ↦ (p j).1))
        ∈ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ')) ChannelCoding.iidXs n ε
    · by_cases hy : (fun i ↦ (p i).2) ∈ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
          (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
            ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)) n ε
      · exact Or.inr ⟨hcov, fun hjt ↦ hfail ⟨hu, hy, hjt⟩⟩
      · exact Or.inl (Or.inr hy)
    · exact Or.inl (Or.inl ⟨hcov, hu⟩)
  -- The `U`-band-failure part is empty on covering-success (L1).
  have hEmpty : Ecov ∩ Euf = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro p ⟨hcov, huf⟩
    exact huf (wz_covering_success_subset_uTypical P_XY κ' qStar hκ'_pos hκ'_sum hqStar ε n M c
      (wzCoveringSuccessStrong_subset_weak P_XY κ' qStar c ε hcov))
  have h1 : SRC.real (Ecov ∩ Euf) = 0 := by rw [hEmpty, measureReal_empty]
  have hunion1 : SRC.real ((Ecov ∩ Euf) ∪ Eyf ∪ (Ecov ∩ Ejf))
      ≤ SRC.real ((Ecov ∩ Euf) ∪ Eyf) + SRC.real (Ecov ∩ Ejf) := measureReal_union_le _ _
  have hunion2 : SRC.real ((Ecov ∩ Euf) ∪ Eyf)
      ≤ SRC.real (Ecov ∩ Euf) + SRC.real Eyf := measureReal_union_le _ _
  have hmono : SRC.real (Ecov ∩ wzCoveringAcceptFailSet P_XY κ' c ε)
      ≤ SRC.real ((Ecov ∩ Euf) ∪ Eyf ∪ (Ecov ∩ Ejf)) :=
    measureReal_mono hincl (measure_ne_top _ _)
  linarith [hyf, hjf, h1, hunion1, hunion2, hmono]

open ChannelCoding in
/-- Covering chosen-word side-information acceptance (the Markov lemma). For every tolerance
`tol > 0` there is an `N` such that for `n ≥ N` and every covering `LossyCode` `c` whose chosen
words typically cover the source (the covering-success premise, an implication hypothesis), the
correlated-joint-source mass of the covering-acceptance failure
`wzCoveringAcceptFailSet P_XY κ' c ε` (the chosen word `c.decoder (c.encoder x)` is not jointly
typical, at radius `ε`, with the side information) is at most `tol`. This is the covering half `C2`
of the Wyner–Ziv error `E2`
(`C2 ⊆ E2`), whose analytic core is a correlated-joint conditional-typicality concentration bound
absent from Mathlib and the codebase.

The covering-success premise is a regularity precondition on the constructed code (covering-failure
mass `≤ tol/2`, a property of the covering `LossyCode`) about a different event (the `x`–`u`
covering slice) than the conclusion (the `u`–`y` acceptance slice); granting it does not hand over
the acceptance bound. Proved by splitting acceptance-failure ⊆ covering-failure ∪
(covering-success ∩ acceptance-failure), bounding the first part by the premise and the second by
the inner `wz_covering_markov_concentration`, then union-bounding.

@audit:ok -/
lemma wz_covering_chosenWord_sideInfo_typical
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (ε : ℝ) (hε : 0 < ε) (tol : ℝ) (htol : 0 < tol)
    (hκ'_pos : ∀ x u, 0 < κ' x u)
    (hκ'_sum : ∀ x, ∑ u, κ' x u = 1)
    (hqStar : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)}) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (M : ℕ)
        (c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k)),
        -- covering-typicality success (covering-supplied premise): off a set of mass `≤ tol/2`,
        -- the chosen covering word `c.decoder (c.encoder x)` is jointly typical with the source
        -- `x` in the covering ambient `rdAmbient qStar`. NOT the acceptance conclusion (different
        -- ambient: covering is the `x`–`u` slice, acceptance the `u`–`y` slice).
        (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
            (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
              P_XY.real {(p.1.1, p.2)}))).real
          ((wzCoveringSuccessStrong P_XY κ' qStar c ε)ᶜ)
          ≤ tol / 2 →
        (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
            (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
              P_XY.real {(p.1.1, p.2)}))).real
          (wzCoveringAcceptFailSet P_XY κ' c ε)
          ≤ tol := by
  -- Obtain the threshold `N` from the inner Markov-lemma concentration bound.
  obtain ⟨N, hN⟩ :=
    wz_covering_markov_concentration P_XY κ' qStar ε hε tol htol hκ'_pos hκ'_sum hqStar
  refine ⟨N, fun n hn M c hprem ↦ ?_⟩
  -- The inner concentration: acceptance failure ON covering success has mass `≤ tol/2`.
  have hinner := hN n hn M c
  haveI hQ_prob : IsProbabilityMeasure
      (ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure (wz_QXY_mem_stdSimplex P_XY)
  set SRC : Measure (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
    with hSRC_def
  haveI hSRC_prob : IsProbabilityMeasure SRC := by rw [hSRC_def]; infer_instance
  -- Acceptance failure is covered by covering-failure ∪ (covering-success ∩ acceptance failure).
  have hincl : wzCoveringAcceptFailSet P_XY κ' c ε
      ⊆ (wzCoveringSuccessStrong P_XY κ' qStar c ε)ᶜ
          ∪ (wzCoveringSuccessStrong P_XY κ' qStar c ε
              ∩ wzCoveringAcceptFailSet P_XY κ' c ε) := by
    intro p hp
    by_cases hc : p ∈ wzCoveringSuccessStrong P_XY κ' qStar c ε
    · exact Or.inr ⟨hc, hp⟩
    · exact Or.inl hc
  -- Union bound over the covering-failure / covering-success split.
  have hunion : SRC.real (wzCoveringAcceptFailSet P_XY κ' c ε)
      ≤ SRC.real ((wzCoveringSuccessStrong P_XY κ' qStar c ε)ᶜ)
        + SRC.real (wzCoveringSuccessStrong P_XY κ' qStar c ε
              ∩ wzCoveringAcceptFailSet P_XY κ' c ε) :=
    le_trans
      (measureReal_mono hincl
        (measure_union_ne_top (measure_ne_top _ _) (measure_ne_top _ _)))
      (measureReal_union_le _ _)
  -- Covering-failure part `≤ tol/2` (premise); covering-success ∩ acceptance-failure `≤ tol/2`
  -- (inner concentration). Their sum is `≤ tol`.
  linarith [hprem, hinner, hunion]

open ChannelCoding in
/-- Strong joint typicality at the small encoder radius `ε_enc` implies both conjuncts of the
covering-success event: the strong conjunct at the covering radius `ε_cov` (via `ε_enc ≤ ε_cov` and
radius monotonicity) and the weak conjunct at `ε` (via the strong-to-weak inclusion
`stronglyTypicalSet_subset_typicalSet`, whose widening constants are the three `logSumAbs` bounds).
No `T_X` restriction is needed — the bridge is a pure set inclusion.

@audit:ok -/
lemma wz_jointStrongly_mem_coveringSuccessJoint
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} [Nonempty (Fin k)] [Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}}]
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (hmem : qStar ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k))
    {n : ℕ} (hn : 0 < n) {ε_enc ε_cov ε : ℝ} (hε_enc_nn : 0 ≤ ε_enc)
    (h_le_cov : ε_enc ≤ ε_cov)
    (hX : (Fintype.card (Fin k) : ℝ) * ε_enc
            * logSumAbs (rdAmbient qStar) ChannelCoding.iidXs < ε)
    (hY : (Fintype.card {x : α // 0 < ∑ y, P_XY.real {(x, y)}} : ℝ) * ε_enc
            * logSumAbs (rdAmbient qStar) ChannelCoding.iidYs < ε)
    (hJ : ε_enc * logSumAbs (rdAmbient qStar)
            (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) < ε)
    (x : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (u : Fin n → Fin k)
    (hxu : (x, u) ∈ jointStronglyTypicalSet (rdAmbient qStar)
            ChannelCoding.iidXs ChannelCoding.iidYs n ε_enc) :
    (x, u) ∈ jointStronglyTypicalSet (rdAmbient qStar)
        ChannelCoding.iidXs ChannelCoding.iidYs n ε_cov
      ∧ (x, u) ∈ ChannelCoding.jointlyTypicalSet (rdAmbient qStar)
        ChannelCoding.iidXs ChannelCoding.iidYs n ε := by
  classical
  haveI : IsProbabilityMeasure (rdAmbient qStar) := rdAmbient_isProbabilityMeasure qStar hmem
  refine ⟨?_, ?_⟩
  · -- Strong conjunct at the larger radius `ε_cov` (radius monotonicity).
    rw [mem_jointStronglyTypicalSet_iff, mem_stronglyTypicalSet_iff] at hxu ⊢
    exact fun p ↦ le_trans (hxu p) h_le_cov
  · -- Weak conjunct: all three entropy bands via strong-to-weak inclusion.
    rw [ChannelCoding.mem_jointlyTypicalSet_iff]
    have hmarg_X := rdAmbient_map_fst_jointSequence qStar hmem
    have hmarg_Y := rdAmbient_map_snd_jointSequence qStar hmem
    refine ⟨?_, ?_, ?_⟩
    · -- X-band.
      have hXstrong : x ∈ stronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs n
          ((Fintype.card (Fin k) : ℝ) * ε_enc) :=
        jointStronglyTypicalSet_implies_X_stronglyTypical (rdAmbient qStar)
          ChannelCoding.iidXs ChannelCoding.iidYs
          (fun i ↦ ChannelCoding.measurable_iidXs i) (fun i ↦ ChannelCoding.measurable_iidYs i)
          hmarg_X hn hε_enc_nn x u hxu
      exact stronglyTypicalSet_subset_typicalSet (rdAmbient qStar) ChannelCoding.iidXs
        (fun i ↦ ChannelCoding.measurable_iidXs i) hn hX hXstrong
    · -- Y-band.
      have hYstrong : u ∈ stronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidYs n
          ((Fintype.card {x : α // 0 < ∑ y, P_XY.real {(x, y)}} : ℝ) * ε_enc) :=
        jointStronglyTypicalSet_implies_Y_stronglyTypical (rdAmbient qStar)
          ChannelCoding.iidXs ChannelCoding.iidYs
          (fun i ↦ ChannelCoding.measurable_iidXs i) (fun i ↦ ChannelCoding.measurable_iidYs i)
          hmarg_Y hn hε_enc_nn x u hxu
      exact stronglyTypicalSet_subset_typicalSet (rdAmbient qStar) ChannelCoding.iidYs
        (fun i ↦ ChannelCoding.measurable_iidYs i) hn hY hYstrong
    · -- Joint-band.
      have hJstrong : (fun i ↦ (x i, u i)) ∈ stronglyTypicalSet (rdAmbient qStar)
          (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n ε_enc := hxu
      exact stronglyTypicalSet_subset_typicalSet (rdAmbient qStar)
        (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs)
        (fun i ↦ ChannelCoding.measurable_jointSequence ChannelCoding.iidXs ChannelCoding.iidYs
          ChannelCoding.measurable_iidXs ChannelCoding.measurable_iidYs i) hn hJ hJstrong

open ChannelCoding in
/-- The covering source–side product measure `SRC` pushes forward under the block `X`-projection
`p ↦ (fun j ↦ (p j).1)` to the covering ambient's block `X`-law
`Measure.pi (fun _ ↦ (rdAmbient qStar).map (iidXs 0))`. The per-coordinate map is `Prod.fst`, so
`Measure.pi_map_pi` reduces the claim to the single-coordinate marginal identity
`(pmfToMeasure P_XY').map Prod.fst = (rdAmbient qStar).map (iidXs 0)`, which holds because both
marginals equal `x ↦ ∑ y, P_XY(x.1, y)` (using `∑ u, κ' x u = 1` for the `qStar` side).

@audit:ok -/
lemma wz_covering_SRC_map_Xproj_eq
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} [Nonempty (Fin k)] [Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}}]
    (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (hqStar_mem : qStar ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k))
    (hκ'sum : ∀ x, ∑ u, κ' x u = 1)
    (hqStar_eq : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
    (n : ℕ) :
    (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
          P_XY.real {(p.1.1, p.2)}))).map
      (fun p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
        fun j ↦ (p j).1)
    = Measure.pi (fun _ : Fin n ↦
        (rdAmbient qStar).map (ChannelCoding.iidXs 0)) := by
  classical
  have hQmem := wz_QXY_mem_stdSimplex P_XY
  haveI hQprob : IsProbabilityMeasure (ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure hQmem
  haveI : IsProbabilityMeasure (rdAmbient qStar) :=
    rdAmbient_isProbabilityMeasure qStar hqStar_mem
  haveI hmapfst_prob : IsProbabilityMeasure ((ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
        P_XY.real {(p.1.1, p.2)})).map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI hmux_prob : IsProbabilityMeasure ((rdAmbient qStar).map (ChannelCoding.iidXs 0)) :=
    rdAmbient_iidXs_isProbabilityMeasure qStar hqStar_mem
  -- Single-coordinate marginal identity.
  have hmarg : (ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
        P_XY.real {(p.1.1, p.2)})).map Prod.fst
        = (rdAmbient qStar).map (ChannelCoding.iidXs 0) := by
    refine Measure.ext_of_singleton (fun a ↦ ?_)
    have hlhs : ((ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
          P_XY.real {(p.1.1, p.2)})).map Prod.fst).real {a}
          = ∑ y, P_XY.real {(a.1, y)} := by
      rw [pmfToMeasure_map_fst_real_singleton hQmem a]; rfl
    have hrhs : ((rdAmbient qStar).map (ChannelCoding.iidXs 0)).real {a}
          = ∑ y, P_XY.real {(a.1, y)} := by
      rw [rdAmbient_map_iidXs qStar hqStar_mem, pmfToMeasure_map_fst_real_singleton hqStar_mem a]
      simp only [marginalFst]
      calc (∑ u, qStar (a, u))
          = ∑ u, κ' a.1 u * ∑ y, P_XY.real {(a.1, y)} :=
            Finset.sum_congr rfl (fun u _ ↦ hqStar_eq (a, u))
        _ = (∑ u, κ' a.1 u) * ∑ y, P_XY.real {(a.1, y)} := by rw [Finset.sum_mul]
        _ = ∑ y, P_XY.real {(a.1, y)} := by rw [hκ'sum a.1, one_mul]
    have heq_real := hlhs.trans hrhs.symm
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp heq_real
  have key : (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
        P_XY.real {(p.1.1, p.2)}))).map (fun p (j : Fin n) ↦ Prod.fst (p j))
      = Measure.pi (fun _ : Fin n ↦ (ChannelCoding.pmfToMeasure
          (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
            P_XY.real {(p.1.1, p.2)})).map Prod.fst) :=
    MeasureTheory.Measure.pi_map_pi (fun _ ↦ measurable_fst.aemeasurable)
  calc (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
          P_XY.real {(p.1.1, p.2)}))).map (fun p ↦ fun j ↦ (p j).1)
      = Measure.pi (fun _ : Fin n ↦ (ChannelCoding.pmfToMeasure
          (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
            P_XY.real {(p.1.1, p.2)})).map Prod.fst) := key
    _ = Measure.pi (fun _ : Fin n ↦ (rdAmbient qStar).map (ChannelCoding.iidXs 0)) := by
        rw [hmarg]

end InformationTheory.Shannon
