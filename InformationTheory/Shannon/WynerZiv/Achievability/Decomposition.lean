import InformationTheory.Shannon.WynerZiv.Achievability.ChosenWord

/-!
# Wyner–Ziv achievability — Steps 3–7 distortion decomposition and pmf-side product bounds
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

/-! ### Steps 3–7 decomposition (binning / decoder / error exponents / squeeze)

The covering data of Steps 1–2 (`wz_coveringFamily_of_testChannel`) is consumed by
the binning + decoder leg. This leg is decomposed into:

* `wzCodeOfCoveringBinning` — the Wyner–Ziv code assembled from a covering
  codebook, a binning of the covering index, and a bin/side-information decoder
  (pure def).
* `wzBinTypicalDecoder` (+ uniqueness `wzBinTypicalDecoder_eq_of_unique`) —
  the bin-restricted conditional-typicality decoder, searching a bin's covering
  codebook members for the one jointly typical with `Y^n` (pure def + the
  decoder equation under a unique witness), mirroring Slepian–Wolf
  `swJointTypicalDecoder` / `swJointTypicalDecoder_eq_of_unique`.
* `wz_covering_failure_prob_le` — covering-failure exponent.
* `wz_codebook_confusion_expectation_le` — codebook-restricted decoder
  confusion exponent (the crux).
* `wz_perDelta_covering_binning` — the capstone consuming the covering data
  and producing the per-slack code family (binning + decoder + error exponents +
  derandomize + squeeze + source extension).
* `wzLiftSupportCode` — the source-extension lift `α' → α` (pure def), used
  together with `wz_expectedBlockDistortion_source_agree`.
-/

/-- Wyner–Ziv code from a covering codebook + binning + bin decoder.
The encoder covers the source with the covering codebook (`c₁.encoder`) and bins
the covering index (`f`). The decoder reconstructs `γ^n` letterwise via `rec`
(the test-channel decoder `qf.2 : Fin k × β → γ`) from the bin decoder's word
`dec (m, y) : Fin n → Fin k` and the side information `y`. Pure assembly; the
covering codebook `c₁`, the binning `f`, the reconstruction map `rec` and the bin
decoder `dec` are all supplied. -/
def wzCodeOfCoveringBinning {α' : Type*} [MeasurableSpace α'] {k M M₁ n : ℕ}
    (c₁ : LossyCode M₁ n α' (Fin k)) (f : Fin M₁ → Fin M)
    (rec : Fin k × β → γ)
    (dec : Fin M × (Fin n → β) → (Fin n → Fin k)) :
    WynerZivCode M n α' β γ where
  encoder := fun x ↦ f (c₁.encoder x)
  decoder := fun my ↦ fun i ↦ rec (dec my i, my.2 i)

/-- Bin/side-information conditional-typicality decoder. Given a bin `m`
and side information `y`, search the bin's covering codebook members
`{c₁.decoder m' | f m' = m}` for the unique word jointly typical with `y`, returning
that `Fin n → Fin k` word (falling back to an arbitrary word if none exists or the
witness is not unique). The search ranges over codebook members only (indexed by the
covering index `m'`), not over all `Fin n → Fin k` words — this restriction is what
makes the decoder-confusion event (S5b) achievable at the Wyner–Ziv rate. Mirror of
Slepian–Wolf `swJointTypicalDecoder`. -/
noncomputable def wzBinTypicalDecoder {α' : Type*} [MeasurableSpace α']
    {Ω : Type*} [MeasurableSpace Ω] {k M M₁ n : ℕ} [Nonempty (Fin k)]
    (μ : Measure Ω) (Us : ℕ → Ω → Fin k) (Ys : ℕ → Ω → β) (ε : ℝ)
    (c₁ : LossyCode M₁ n α' (Fin k)) (f : Fin M₁ → Fin M) :
    Fin M × (Fin n → β) → (Fin n → Fin k) := fun my ↦
  haveI : Decidable (∃! u : Fin n → Fin k,
      (∃ m' : Fin M₁, f m' = my.1 ∧ c₁.decoder m' = u)
        ∧ (u, my.2) ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε) :=
    Classical.propDecidable _
  if h : ∃! u : Fin n → Fin k,
      (∃ m' : Fin M₁, f m' = my.1 ∧ c₁.decoder m' = u)
        ∧ (u, my.2) ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε
    then Classical.choose h.exists
    else Classical.arbitrary _

/-- If the covering codeword `c₁.decoder m₁` is jointly typical with `y` and is the
unique bin-`f m₁` codebook member so typical, then `wzBinTypicalDecoder` recovers it.
Mirror of `swJointTypicalDecoder_eq_of_unique`. -/
lemma wzBinTypicalDecoder_eq_of_unique {α' : Type*} [MeasurableSpace α']
    {Ω : Type*} [MeasurableSpace Ω] {k M M₁ n : ℕ} [Nonempty (Fin k)]
    (μ : Measure Ω) (Us : ℕ → Ω → Fin k) (Ys : ℕ → Ω → β) (ε : ℝ)
    (c₁ : LossyCode M₁ n α' (Fin k)) (f : Fin M₁ → Fin M)
    {m₁ : Fin M₁} {y : Fin n → β}
    (htrue : (c₁.decoder m₁, y) ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε)
    (hunique : ∀ u : Fin n → Fin k,
        (∃ m' : Fin M₁, f m' = f m₁ ∧ c₁.decoder m' = u) →
        (u, y) ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε →
        u = c₁.decoder m₁) :
    wzBinTypicalDecoder μ Us Ys ε c₁ f (f m₁, y) = c₁.decoder m₁ := by
  have hExUnique : ∃! u : Fin n → Fin k,
      (∃ m' : Fin M₁, f m' = f m₁ ∧ c₁.decoder m' = u)
        ∧ (u, y) ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε := by
    refine ⟨c₁.decoder m₁, ⟨⟨m₁, rfl, rfl⟩, htrue⟩, ?_⟩
    intro u hu
    exact hunique u hu.1 hu.2
  unfold wzBinTypicalDecoder
  rw [dif_pos hExUnique]
  have hch_spec :
      (∃ m' : Fin M₁, f m' = f m₁
          ∧ c₁.decoder m' = Classical.choose hExUnique.exists)
        ∧ (Classical.choose hExUnique.exists, y)
            ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε :=
    Classical.choose_spec hExUnique.exists
  exact hunique (Classical.choose hExUnique.exists) hch_spec.1 hch_spec.2

/-- Covering-failure exponent. The codebook-averaged probability
that a strongly-typical source `x` finds no covering codeword jointly typical
with it decays doubly-exponentially: `∫ x, (1 − p_typ x)^{M₁} ≤ exp(−M₁ · exp(−n(I +
δ)))`, where `p_typ x` is the per-codeword conditional-typicality mass (bounded below
by `exp(−n(I + δ))` via `wz_covering_sideInfo_mass_ge`), passed here as `hmass`.

`hmass` is the per-source covering-acceptance mass lower bound `exp(−n(I+δ)) ≤ p_typ x`.
With it, `(1−p)^M₁ ≤ e^{−M₁ p} ≤ e^{−M₁·exp(−n(I+δ))}` pointwise (`p_typ x ∈ [0,1]`,
`p ≥ exp(−n(I+δ))`), then integrate over the probability measure `P_X`. The pointwise
`p_typ x ≤ 1` holds even without measurability of `Us 0`: `μ.map (Us 0)` is a
sub-probability measure (`Measure.isFiniteMeasure_map` + `map` mass `≤ 1`), so its
product `Measure.pi` is a sub-probability measure (`Measure.pi_univ`), and the mass of
any set is `≤ 1`. The `(1−t)^M ≤ e^{−Mt}` step reuses `one_sub_pow_le_exp_neg_mul`.
@audit:ok -/
lemma wz_covering_failure_prob_le {α' : Type*}
    [Fintype α'] [DecidableEq α'] [Nonempty α']
    [MeasurableSpace α'] [MeasurableSingletonClass α']
    {Ω : Type*} [MeasurableSpace Ω] {k n M₁ : ℕ} [Nonempty (Fin k)]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α') (Us : ℕ → Ω → Fin k) (ε : ℝ)
    (P_X : Measure (Fin n → α')) [IsProbabilityMeasure P_X]
    (I δ : ℝ)
    (hmass : ∀ x : Fin n → α', Real.exp (-(n : ℝ) * (I + δ)) ≤
        (Measure.pi fun _ : Fin n ↦ μ.map (Us 0)).real
          {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}) :
    ∫ x, (1 - (Measure.pi fun _ : Fin n ↦ μ.map (Us 0)).real
              {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}) ^ M₁ ∂P_X
      ≤ Real.exp (-(M₁ : ℝ) * Real.exp (-(n : ℝ) * (I + δ))) := by
  set ν : Measure (Fin n → Fin k) := Measure.pi fun _ : Fin n ↦ μ.map (Us 0) with hν
  -- The map of the probability measure `μ` is a finite (sub-probability) measure,
  -- irrespective of whether `Us 0` is measurable.
  haveI hfin : IsFiniteMeasure (μ.map (Us 0)) := Measure.isFiniteMeasure_map μ (Us 0)
  have hfac : (μ.map (Us 0)) Set.univ ≤ 1 := by
    by_cases hae : AEMeasurable (Us 0) μ
    · rw [Measure.map_apply_of_aemeasurable hae MeasurableSet.univ]; simp
    · rw [Measure.map_of_not_aemeasurable hae]; simp
  -- Hence the product measure `ν` is a sub-probability measure.
  have hν_univ : ν Set.univ ≤ 1 := by
    rw [hν, Measure.pi_univ]
    exact Finset.prod_le_one' (fun _ _ ↦ hfac)
  -- The per-source covering mass lies in `[0, 1]`.
  have h1 : ∀ x : Fin n → α',
      ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε} ≤ 1 := by
    intro x
    have hle : ν {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε} ≤ 1 :=
      le_trans (measure_mono (Set.subset_univ _)) hν_univ
    calc ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}
        = (ν {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}).toReal := rfl
      _ ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono (by simp) hle
      _ = 1 := by simp
  -- Pointwise doubly-exponential bound to the constant right-hand side.
  have hbound : ∀ x : Fin n → α',
      (1 - ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}) ^ M₁
        ≤ Real.exp (-(M₁ : ℝ) * Real.exp (-(n : ℝ) * (I + δ))) := by
    intro x
    have h0 : 0 ≤ ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε} :=
      measureReal_nonneg
    have step1 :
        (1 - ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}) ^ M₁
          ≤ Real.exp (-(M₁ : ℝ) *
              ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}) :=
      one_sub_pow_le_exp_neg_mul M₁ h0 (h1 x)
    have step2 :
        Real.exp (-(M₁ : ℝ) *
            ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε})
          ≤ Real.exp (-(M₁ : ℝ) * Real.exp (-(n : ℝ) * (I + δ))) := by
      apply Real.exp_le_exp.mpr
      have hM₁ : (0 : ℝ) ≤ (M₁ : ℝ) := Nat.cast_nonneg _
      nlinarith [hmass x, hM₁]
    exact le_trans step1 step2
  -- Integrability of the (bounded, finitely-supported-domain) integrand.
  have h_int : Integrable (fun x : Fin n → α' ↦
      (1 - ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}) ^ M₁) P_X := by
    have h_meas : Measurable (fun x : Fin n → α' ↦
        (1 - ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}) ^ M₁) :=
      measurable_of_finite _
    refine Integrable.mono' (g := fun _ ↦
        Real.exp (-(M₁ : ℝ) * Real.exp (-(n : ℝ) * (I + δ))))
      (integrable_const _) h_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x ↦ ?_)
    have hpow_nn : 0 ≤ (1 -
        ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}) ^ M₁ :=
      pow_nonneg (by linarith [h1 x]) M₁
    rw [Real.norm_eq_abs, abs_of_nonneg hpow_nn]
    exact hbound x
  calc ∫ x, (1 - ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}) ^ M₁ ∂P_X
      ≤ ∫ _x : Fin n → α',
          Real.exp (-(M₁ : ℝ) * Real.exp (-(n : ℝ) * (I + δ))) ∂P_X :=
        integral_mono h_int (integrable_const _) hbound
    _ = Real.exp (-(M₁ : ℝ) * Real.exp (-(n : ℝ) * (I + δ))) := by
        rw [integral_const]; simp

/-- Codebook-restricted decoder confusion exponent. The
binning-averaged probability that some codebook member `c₁.decoder m'` other than
the true covering codeword shares the true bin and is jointly typical with `Y^n` is at
most `M₁ · exp(−n · I(U;Y)) · M⁻¹`.

Restricting the confusable set to the covering codebook is what achieves the Wyner–Ziv
rate. Binning all `u`-sequences would give the count `exp(n·H(U|Y))`, forcing the rate
down to `H(U|Y)` — too weak; this bound instead restricts to the covering codebook
(`M₁ = ⌈exp(n·I(X;U))⌉` members), so the alias count is `M₁` rather than
`exp(n·H(U|Y))`. With `M = ⌈exp(n·R)⌉` bins, the bound is
`M₁ · exp(−n·I(U;Y)) / M ≈ exp(n·(I(X;U) − I(U;Y) − R))`, which vanishes precisely
when `R > I(X;U) − I(Y;U)` — the Wyner–Ziv rate.

`hmass` is the per-codeword joint-typicality mass upper bound
`μ{codeword m' typical with Y^n} ≤ exp(−n·I_YU)` (the AEP bound for a covering codeword
independent of `Y^n`); `hcollision` is the binning-collision property
`binMeas{f | f m' = f m} = M⁻¹` for distinct indices, mirroring `binning_collision_prob`.
The codebook-restricted union over `m' : Fin M₁` stays in the body (not a hypothesis):
swap the order of integration, bound the per-`ω` `binMeas`-slice by union bound +
`hcollision` as `M⁻¹ · #{m' typical}`, integrate over `μ`, then apply `hmass` to each of
the `M₁` codewords to get `M⁻¹ · M₁ · exp(−n·I_YU)`. `hYs`/`htrueIdx` (measurability of
the side-information block RV and of the covering index) are regularity preconditions for
the Tonelli swap, supplied by the call site.

Implementation note: the typical set is an abstract measurable set `jts` (parameter
`hjts_meas : MeasurableSet jts`) rather than a concrete `jointlyTypicalSet`, since the
body uses no property of it beyond measurability. This lets the call site instantiate the
confusion integral under the source product measure with the typical set defined on the
side-information ambient — two different measures a concrete typical set could never match;
the per-codeword mass `hmass` is then supplied via a side-information-marginal transfer to
`wz_covering_codeword_sideInfo_mass_le`.
@audit:ok -/
lemma wz_codebook_confusion_expectation_le {α' : Type*} [MeasurableSpace α']
    {Ω : Type*} [MeasurableSpace Ω] {k n M M₁ : ℕ} [Nonempty (Fin k)] [NeZero M]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Ys : ℕ → Ω → β)
    (c₁ : LossyCode M₁ n α' (Fin k)) (trueIdx : Ω → Fin M₁)
    (hYs : ∀ i, Measurable (Ys i)) (htrueIdx : Measurable trueIdx)
    (binMeas : Measure (Fin M₁ → Fin M)) [IsProbabilityMeasure binMeas]
    (jts : Set ((Fin n → Fin k) × (Fin n → β))) (hjts_meas : MeasurableSet jts)
    (I_YU : ℝ)
    (hmass : ∀ m' : Fin M₁,
        μ.real {ω | (c₁.decoder m', jointRV Ys n ω) ∈ jts}
          ≤ Real.exp (-(n : ℝ) * I_YU))
    (hcollision : ∀ m' m : Fin M₁, m' ≠ m →
        binMeas.real {f | f m' = f m} = (M : ℝ)⁻¹) :
    ∫ f, μ.real {ω | ∃ m' : Fin M₁,
            m' ≠ trueIdx ω
          ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}
        ∂binMeas
      ≤ (M₁ : ℝ) * Real.exp (-(n : ℝ) * I_YU) * ((M : ℝ))⁻¹ := by
  classical
  haveI : MeasurableSingletonClass (Fin M₁ → Fin M) := Pi.instMeasurableSingletonClass
  -- Measurability of the per-codeword typicality set in `ω`.
  have hC_meas : ∀ m' : Fin M₁,
      MeasurableSet {ω | (c₁.decoder m', jointRV Ys n ω) ∈ jts} := by
    intro m'
    have hmap : Measurable (fun ω ↦ (c₁.decoder m', jointRV Ys n ω)) :=
      measurable_const.prodMk (measurable_jointRV Ys hYs n)
    exact hmap hjts_meas
  -- Measurability of the per-`(f, m')` confusion set in `ω`.
  have hbad_meas : ∀ (f : Fin M₁ → Fin M) (m' : Fin M₁),
      MeasurableSet {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
        ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} := by
    intro f m'
    have hA : MeasurableSet {ω | m' ≠ trueIdx ω} := by
      have hpre : {ω | m' ≠ trueIdx ω} = (trueIdx ⁻¹' {m'})ᶜ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_preimage,
          Set.mem_singleton_iff]
        exact ne_comm
      rw [hpre]; exact (htrueIdx (measurableSet_singleton m')).compl
    have hB : MeasurableSet {ω | f m' = f (trueIdx ω)} :=
      htrueIdx ((Set.toFinite {m₀ : Fin M₁ | f m' = f m₀}).measurableSet)
    exact hA.inter (hB.inter (hC_meas m'))
  -- Step D: the per-`m'` integral bound `∫ f, μ.real (confusion set) ≤ exp(−n·I_YU)·M⁻¹`.
  have hD : ∀ m' : Fin M₁,
      ∫ f, μ.real {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} ∂binMeas
        ≤ Real.exp (-(n : ℝ) * I_YU) * ((M : ℝ))⁻¹ := by
    intro m'
    have h_nn : 0 ≤ᵐ[binMeas] fun f ↦ μ.real {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
        ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} :=
      Filter.Eventually.of_forall fun _ ↦ measureReal_nonneg
    have h_aesm : AEStronglyMeasurable
        (fun f ↦ μ.real {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}) binMeas :=
      (measurable_of_finite _).aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae h_nn h_aesm,
      ChannelCoding.lintegral_ofReal_measureReal_eq_lintegral_measure μ binMeas
        (fun f ↦ {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts})]
    -- Tonelli swap over `binMeas ⊗ μ`.
    have hE_meas : MeasurableSet {q : (Fin M₁ → Fin M) × Ω |
        q.2 ∈ {ω | m' ≠ trueIdx ω ∧ q.1 m' = q.1 (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}} := by
      have h_decomp : {q : (Fin M₁ → Fin M) × Ω |
          q.2 ∈ {ω | m' ≠ trueIdx ω ∧ q.1 m' = q.1 (trueIdx ω)
            ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}}
          = ⋃ f₀ : Fin M₁ → Fin M, ({f₀} : Set (Fin M₁ → Fin M)) ×ˢ
            {ω | m' ≠ trueIdx ω ∧ f₀ m' = f₀ (trueIdx ω)
              ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} := by
        ext ⟨g, ω⟩; simp
      rw [h_decomp]
      exact MeasurableSet.iUnion fun f₀ ↦
        (measurableSet_singleton f₀).prod (hbad_meas f₀ m')
    rw [ChannelCoding.lintegral_measure_swap_of_prod_measurableSet binMeas μ
      (fun f ↦ {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
        ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}) hE_meas]
    simp only [Set.mem_setOf_eq]
    -- Per-`ω` inner bound: the `binMeas`-slice is `≤ M⁻¹` on the typical set, else `0`.
    have h_inner : ∀ ω : Ω,
        binMeas {f | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}
          ≤ ENNReal.ofReal ((M : ℝ)⁻¹) *
              Set.indicator {ω' | (c₁.decoder m', jointRV Ys n ω') ∈ jts} 1 ω := by
      intro ω
      by_cases htyp : (c₁.decoder m', jointRV Ys n ω) ∈ jts
      · by_cases hidx : m' = trueIdx ω
        · have hempty : {f : Fin M₁ → Fin M | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
              ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} = ∅ := by
            ext f
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
            rintro ⟨hne, -, -⟩
            exact hne hidx
          rw [hempty]; simp
        · have hset : {f : Fin M₁ → Fin M | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
              ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}
              = {f | f m' = f (trueIdx ω)} := by
            ext f
            simp only [Set.mem_setOf_eq]
            exact ⟨fun h ↦ h.2.1, fun h ↦ ⟨hidx, h, htyp⟩⟩
          rw [hset]
          have hmem : ω ∈ {ω' | (c₁.decoder m', jointRV Ys n ω') ∈ jts} := htyp
          rw [Set.indicator_of_mem hmem]
          simp only [Pi.one_apply, mul_one]
          rw [← ofReal_measureReal (measure_ne_top binMeas {f | f m' = f (trueIdx ω)}),
            hcollision m' (trueIdx ω) hidx]
      · have hempty : {f : Fin M₁ → Fin M | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
            ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} = ∅ := by
          ext f
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨-, -, htyp'⟩
          exact htyp htyp'
        rw [hempty]; simp
    have hind_meas : Measurable
        (Set.indicator {ω' | (c₁.decoder m', jointRV Ys n ω') ∈ jts} (1 : Ω → ℝ≥0∞)) :=
      measurable_const.indicator (hC_meas m')
    have h_lint_le :
        ∫⁻ ω, binMeas {f | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
            ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} ∂μ
          ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * I_YU) * (M : ℝ)⁻¹) := by
      calc ∫⁻ ω, binMeas {f | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
              ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} ∂μ
          ≤ ∫⁻ ω, ENNReal.ofReal ((M : ℝ)⁻¹) *
              Set.indicator {ω' | (c₁.decoder m', jointRV Ys n ω') ∈ jts} 1 ω ∂μ :=
            lintegral_mono h_inner
        _ = ENNReal.ofReal ((M : ℝ)⁻¹) *
              ∫⁻ ω, Set.indicator {ω' | (c₁.decoder m', jointRV Ys n ω') ∈ jts} 1 ω ∂μ :=
            lintegral_const_mul _ hind_meas
        _ = ENNReal.ofReal ((M : ℝ)⁻¹) *
              μ {ω' | (c₁.decoder m', jointRV Ys n ω') ∈ jts} := by
            rw [lintegral_indicator_one (hC_meas m')]
        _ ≤ ENNReal.ofReal ((M : ℝ)⁻¹) *
              ENNReal.ofReal (Real.exp (-(n : ℝ) * I_YU)) := by
            gcongr
            calc μ {ω' | (c₁.decoder m', jointRV Ys n ω') ∈ jts}
                = ENNReal.ofReal (μ.real {ω' | (c₁.decoder m', jointRV Ys n ω') ∈ jts}) :=
                  (ofReal_measureReal (measure_ne_top μ _)).symm
              _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * I_YU)) :=
                  ENNReal.ofReal_le_ofReal (hmass m')
        _ = ENNReal.ofReal (Real.exp (-(n : ℝ) * I_YU) * (M : ℝ)⁻¹) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
    calc (∫⁻ ω, binMeas {f | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
            ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} ∂μ).toReal
        ≤ (ENNReal.ofReal (Real.exp (-(n : ℝ) * I_YU) * (M : ℝ)⁻¹)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top h_lint_le
      _ = Real.exp (-(n : ℝ) * I_YU) * (M : ℝ)⁻¹ :=
          ENNReal.toReal_ofReal (by positivity)
  -- Union bound over the codebook members at each hash `f`, then integrate the sum.
  have hUnion : ∀ f : Fin M₁ → Fin M,
      {ω | ∃ m' : Fin M₁, m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}
        = ⋃ m' ∈ (Finset.univ : Finset (Fin M₁)),
            {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
              ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} := by
    intro f; ext ω; simp
  have hStepA : ∀ f : Fin M₁ → Fin M,
      μ.real {ω | ∃ m' : Fin M₁, m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}
        ≤ ∑ m' : Fin M₁, μ.real {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
            ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} := by
    intro f
    rw [hUnion f]
    exact measureReal_biUnion_finset_le Finset.univ _
  have hInt_outer : Integrable (fun f ↦ μ.real {ω | ∃ m' : Fin M₁, m' ≠ trueIdx ω
      ∧ f m' = f (trueIdx ω) ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}) binMeas :=
    Integrable.of_finite
  have hInt_sum : Integrable (fun f ↦ ∑ m' : Fin M₁, μ.real {ω | m' ≠ trueIdx ω
      ∧ f m' = f (trueIdx ω) ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}) binMeas :=
    Integrable.of_finite
  calc ∫ f, μ.real {ω | ∃ m' : Fin M₁, m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} ∂binMeas
      ≤ ∫ f, ∑ m' : Fin M₁, μ.real {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} ∂binMeas :=
        integral_mono hInt_outer hInt_sum hStepA
    _ = ∑ m' : Fin M₁, ∫ f, μ.real {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} ∂binMeas :=
        integral_finsetSum Finset.univ fun _ _ ↦ Integrable.of_finite
    _ ≤ ∑ _m' : Fin M₁, Real.exp (-(n : ℝ) * I_YU) * ((M : ℝ))⁻¹ :=
        Finset.sum_le_sum fun m' _ ↦ hD m'
    _ = (M₁ : ℝ) * Real.exp (-(n : ℝ) * I_YU) * ((M : ℝ))⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Source-extension lift `α' → α`. Lift a Wyner–Ziv code over the source
support subtype `α' := {x // 0 < P_X x}` to a code over the full alphabet `α`, using
the default support element `x₀` for out-of-support coordinates (which have zero
`Measure.pi P_XY`-mass, so the lift preserves expected block distortion via
`wz_expectedBlockDistortion_source_agree`). The decoder is unchanged (it does not
touch `α`). Pure def. -/
noncomputable def wzLiftSupportCode
    (P_XY : Measure (α × β)) {M n : ℕ}
    (x₀ : {x : α // 0 < ∑ y, P_XY.real {(x, y)}})
    (cSupp : WynerZivCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} β γ) :
    WynerZivCode M n α β γ where
  encoder := fun x ↦ cSupp.encoder (fun i ↦
    haveI := Classical.propDecidable (0 < ∑ y, P_XY.real {(x i, y)})
    if h : 0 < ∑ y, P_XY.real {(x i, y)} then ⟨x i, h⟩ else x₀)
  decoder := cSupp.decoder

/-- Index-binning measure. Hash each of the `M₁` covering-codebook *indices*
`Fin M₁` independently to a uniformly random bin in `Fin M`. This is the `Fin M₁`-index
analogue of `binningMeasure` (which hashes whole sequences `(Fin n → α) → Fin M`); it is
the concrete `binMeas : Measure (Fin M₁ → Fin M)` that the codebook-restricted
decoder-confusion exponent `wz_codebook_confusion_expectation_le` consumes. -/
noncomputable def wzIndexBinningMeasure (M₁ M : ℕ) [NeZero M] :
    Measure (Fin M₁ → Fin M) :=
  Measure.pi (fun _ : Fin M₁ ↦ uniformOn (Set.univ : Set (Fin M)))

/-- The index-binning measure is a probability measure. -/
instance wzIndexBinningMeasure.instIsProbabilityMeasure (M₁ M : ℕ) [NeZero M] :
    IsProbabilityMeasure (wzIndexBinningMeasure M₁ M) := by
  unfold wzIndexBinningMeasure
  infer_instance

/-- Singleton mass for the index-binning measure. For any hash function
`f : Fin M₁ → Fin M`, its `wzIndexBinningMeasure`-mass is `(1/M)^{M₁}` (each of the
`M₁` covering indices independently picks one of `M` bins). The `Fin M₁`-index mirror
of `binningMeasure_singleton_real`. -/
lemma wzIndexBinningMeasure_singleton_real
    (M₁ M : ℕ) [NeZero M] (f : Fin M₁ → Fin M) :
    (wzIndexBinningMeasure M₁ M).real {f}
      = (((M : ℝ))⁻¹) ^ (Fintype.card (Fin M₁)) := by
  classical
  haveI : MeasurableSingletonClass (Fin M₁ → Fin M) :=
    Pi.instMeasurableSingletonClass
  unfold wzIndexBinningMeasure
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  -- Each factor is `uniformOn univ {f j}` = `1 / Fintype.card (Fin M)`.
  have h_factor : ∀ j : Fin M₁,
      ((uniformOn (Set.univ : Set (Fin M))) {f j}).toReal = (M : ℝ)⁻¹ := by
    intro j
    rw [uniformOn_univ]
    rw [Measure.count_singleton, Fintype.card_fin]
    rw [ENNReal.toReal_div]
    simp
  rw [Finset.prod_congr rfl (fun j _ ↦ h_factor j)]
  rw [Finset.prod_const]
  rfl

/-- Index-binning collision probability. Two distinct covering indices `m' ≠ m`
hash to the same bin with probability exactly `1/M`. Supplies `hcollision` to
`wz_codebook_confusion_expectation_le`; the `Fin M₁`-index mirror of
`binning_collision_prob`. -/
theorem wzIndexBinningMeasure_collision {M₁ M : ℕ} [NeZero M]
    {m' m : Fin M₁} (h : m' ≠ m) :
    (wzIndexBinningMeasure M₁ M).real {f | f m' = f m} = (M : ℝ)⁻¹ := by
  classical
  haveI : Nonempty (Fin M₁) := ⟨m'⟩
  haveI : MeasurableSingletonClass (Fin M₁ → Fin M) :=
    Pi.instMeasurableSingletonClass
  -- Expand the collision event as a finite sum of singleton masses.
  set HashFn : Type _ := Fin M₁ → Fin M with hHashFn_def
  haveI : DecidableEq (Fin M₁) := Classical.decEq _
  haveI : DecidableEq (Fin M) := Classical.decEq _
  haveI : Fintype HashFn := Pi.instFintype
  haveI : DecidableEq HashFn := Classical.decEq _
  have h_collision_sum :
      (wzIndexBinningMeasure M₁ M).real {f : HashFn | f m' = f m}
        = ∑ f : HashFn, (wzIndexBinningMeasure M₁ M).real {f} *
            (if f m' = f m then (1 : ℝ) else 0) := by
    set S : Finset HashFn := (Finset.univ : Finset HashFn).filter (fun f ↦ f m' = f m)
    have h_S_eq : (S : Set HashFn) = {f : HashFn | f m' = f m} := by
      ext f; simp [S]
    rw [← h_S_eq, ← sum_measureReal_singleton (μ := wzIndexBinningMeasure M₁ M) S]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun f _ ↦ ?_)
    split_ifs with hfx
    · rw [mul_one]
    · rw [mul_zero]
  rw [h_collision_sum]
  -- Substitute the singleton mass `(1/M)^{M₁}`.
  have h_sub : ∀ f : HashFn,
      (wzIndexBinningMeasure M₁ M).real {f} * (if f m' = f m then (1 : ℝ) else 0)
        = ((M : ℝ)⁻¹) ^ (Fintype.card (Fin M₁)) *
            (if f m' = f m then (1 : ℝ) else 0) := by
    intro f
    rw [wzIndexBinningMeasure_singleton_real M₁ M f]
  rw [Finset.sum_congr rfl (fun f _ ↦ h_sub f)]
  rw [← Finset.mul_sum]
  -- The indicator sum counts `{f | f m' = f m}`.
  have h_sum_indicator :
      (∑ f : HashFn, (if f m' = f m then (1 : ℝ) else 0))
        = (Fintype.card {f : HashFn // f m' = f m} : ℝ) := by
    rw [Fintype.card_subtype]
    rw [← Finset.sum_filter]
    rw [Finset.sum_const]
    simp
  rw [h_sum_indicator]
  -- Count `{f | f m' = f m}` via the bijection that drops the coordinate `m`
  -- (whose value is forced to equal `f m'`).
  let toFun : {f : HashFn // f m' = f m} → ({j : Fin M₁ // j ≠ m} → Fin M) :=
    fun ⟨f, _⟩ j ↦ f j.1
  let invFun : ({j : Fin M₁ // j ≠ m} → Fin M) → {f : HashFn // f m' = f m} :=
    fun g ↦ ⟨fun j ↦ if hj : j = m then g ⟨m', h⟩ else g ⟨j, hj⟩, by simp [h]⟩
  have left_inv : ∀ p, invFun (toFun p) = p := by
    intro ⟨f, hf⟩
    apply Subtype.ext
    funext j
    by_cases hj : j = m
    · subst hj
      show (if hjj : j = j then f m' else f j) = f j
      simp [hf.symm]
    · show (if hjj : j = m then f m' else f j) = f j
      simp [hj]
  have right_inv : ∀ g, toFun (invFun g) = g := by
    intro g
    funext ⟨j, hj⟩
    show (if hj_eq : j = m then g ⟨m', h⟩ else g ⟨j, hj_eq⟩) = g ⟨j, hj⟩
    simp [hj]
  set e : {f : HashFn // f m' = f m} ≃ ({j : Fin M₁ // j ≠ m} → Fin M) :=
    { toFun := toFun, invFun := invFun, left_inv := left_inv, right_inv := right_inv }
  rw [Fintype.card_congr e]
  have h_card_pi :
      Fintype.card ({j : Fin M₁ // j ≠ m} → Fin M)
        = M ^ (Fintype.card (Fin M₁) - 1) := by
    rw [Fintype.card_pi, Finset.prod_const, Fintype.card_fin]
    congr 1
    rw [Finset.card_univ, Fintype.card_subtype_compl]
    simp
  rw [h_card_pi]
  set N : ℕ := Fintype.card (Fin M₁) with hN_def
  have hN_pos : 1 ≤ N := by
    rw [hN_def]
    exact Fintype.card_pos
  have hM_ne : (M : ℝ) ≠ 0 := by
    have : NeZero M := inferInstance
    exact_mod_cast NeZero.ne M
  push_cast
  rw [inv_pow]
  have hN_eq : (M : ℝ) ^ N = (M : ℝ) ^ (N - 1) * (M : ℝ) := by
    conv_lhs => rw [show N = (N - 1) + 1 from (Nat.sub_add_cancel hN_pos).symm]
    rw [pow_succ]
  rw [hN_eq, mul_inv, mul_comm ((M : ℝ) ^ (N - 1))⁻¹ _, mul_assoc]
  rw [inv_mul_cancel₀ (pow_ne_zero _ hM_ne), mul_one]

/-- Mutual-information restriction identity. The covering
mutual information computed on the support-restricted joint `qStar` (over the source
support subtype `α' := {x // 0 < P_X x}`) equals the Wyner–Ziv covering objective
`wzMutualInfoXU` computed on the full-alphabet factorizable joint `q'`. The support
restriction drops only zero atoms of the source marginal `P_X`, which contribute
`Real.negMulLog 0 = 0` to every marginal and joint entropy sum, so the two mutual
informations coincide. This algebraic leaf lets the covering family `hcov` — whose
premise is `mutualInfoPmf qStar < R₁` — be fed at a covering rate `R₁` chosen strictly
above `wzMutualInfoXU q' = I(X;U)`.

The support-restriction principle (`key`) sums the vanishing off-support terms away
(`Real.negMulLog 0 = 0`), matching the three marginal/joint entropy sums of `qStar` (over
the support subtype) against those of `wzMarginalXU q'` (over the full alphabet). The
factorization hypotheses `hfact_eq`/`hκ'sum`/`hqStar_eq` are genuine definitional
constraints (without them the two mutual informations differ, since `qStar` lives over the
support subtype and `q'` over the full alphabet); none is the conclusion.
@audit:ok -/
lemma wz_mutualInfo_restriction_eq
    (P_XY : Measure (α × β)) (k : ℕ)
    (q' : α × β × Fin k → ℝ) (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (hfact_eq : ∀ x y u, q' (x, y, u) = κ' x u * P_XY.real {(x, y)})
    (hκ'sum : ∀ x, ∑ u, κ' x u = 1)
    (hqStar_eq : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)}) :
    mutualInfoPmf qStar = wzMutualInfoXU (Fin k) q' := by
  classical
  set PX : α → ℝ := fun x ↦ ∑ y, P_XY.real {(x, y)} with hPX
  have hPX_nn : ∀ x, (0 : ℝ) ≤ PX x :=
    fun x ↦ Finset.sum_nonneg (fun y _ ↦ measureReal_nonneg)
  -- Support-restriction: a function vanishing off `supp(P_X)` has equal `α`- and
  -- support-subtype sums (off-support terms are `0`, so they drop out).
  have key : ∀ f : α → ℝ, (∀ x, ¬ (0 < PX x) → f x = 0) →
      ∑ x : {x : α // 0 < PX x}, f x.1 = ∑ x : α, f x := by
    intro f hf
    rw [← Finset.sum_subtype (Finset.univ.filter (fun x ↦ 0 < PX x))
        (fun x ↦ by simp) f]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro x _ hx
    exact hf x (by simpa using hx)
  -- Pointwise pmf values: on the support subtype `qStar` and the full-alphabet
  -- `wzMarginalXU q'` both equal `κ'(x,u)·P_X(x)`.
  have hqStar_val : ∀ (a : {x : α // 0 < PX x}) (u : Fin k),
      qStar (a, u) = κ' a.1 u * PX a.1 := fun a u ↦ hqStar_eq (a, u)
  have hwz_val : ∀ (x : α) (u : Fin k),
      wzMarginalXU (Fin k) q' (x, u) = κ' x u * PX x := by
    intro x u
    show (∑ y, q' (x, y, u)) = κ' x u * ∑ y, P_XY.real {(x, y)}
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y _ ↦ hfact_eq x y u)
  -- Marginals: `marginalFst` of both equals `P_X`; `marginalSnd` of both agree pointwise.
  have hmargFst_star : ∀ a : {x : α // 0 < PX x}, marginalFst qStar a = PX a.1 := by
    intro a
    show (∑ u, qStar (a, u)) = PX a.1
    simp_rw [hqStar_val a]
    rw [← Finset.sum_mul, hκ'sum a.1, one_mul]
  have hmargFst_wz : ∀ x : α,
      marginalFst (wzMarginalXU (Fin k) q') x = PX x := by
    intro x
    show (∑ u, wzMarginalXU (Fin k) q' (x, u)) = PX x
    simp_rw [hwz_val x]
    rw [← Finset.sum_mul, hκ'sum x, one_mul]
  have hmargSnd_eq : ∀ u : Fin k,
      marginalSnd qStar u = marginalSnd (wzMarginalXU (Fin k) q') u := by
    intro u
    show (∑ a : {x : α // 0 < PX x}, qStar (a, u))
        = ∑ x : α, wzMarginalXU (Fin k) q' (x, u)
    simp_rw [hqStar_val _ u, hwz_val _ u]
    exact key (fun x ↦ κ' x u * PX x) (fun x hx ↦ by
      rw [le_antisymm (not_lt.mp hx) (hPX_nn x), mul_zero])
  -- Assemble the three entropy sums.
  have hA : (∑ a : {x : α // 0 < PX x}, Real.negMulLog (marginalFst qStar a))
      = ∑ a : α, Real.negMulLog (marginalFst (wzMarginalXU (Fin k) q') a) := by
    rw [Finset.sum_congr rfl (fun a _ ↦ by rw [hmargFst_star a] :
        ∀ a ∈ (Finset.univ : Finset {x : α // 0 < PX x}),
          Real.negMulLog (marginalFst qStar a) = Real.negMulLog (PX a.1))]
    rw [key (fun x ↦ Real.negMulLog (PX x)) (fun x hx ↦ by
        rw [le_antisymm (not_lt.mp hx) (hPX_nn x)]; exact Real.negMulLog_zero)]
    exact Finset.sum_congr rfl (fun x _ ↦ by rw [hmargFst_wz x])
  have hB : (∑ b : Fin k, Real.negMulLog (marginalSnd qStar b))
      = ∑ b : Fin k, Real.negMulLog (marginalSnd (wzMarginalXU (Fin k) q') b) :=
    Finset.sum_congr rfl (fun u _ ↦ by rw [hmargSnd_eq u])
  have hC : (∑ p : {x : α // 0 < PX x} × Fin k, Real.negMulLog (qStar p))
      = ∑ p : α × Fin k, Real.negMulLog (wzMarginalXU (Fin k) q' p) := by
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl (fun a _ ↦
        Finset.sum_congr rfl (fun u _ ↦ by rw [hqStar_val a u]) :
        ∀ a ∈ (Finset.univ : Finset {x : α // 0 < PX x}),
          (∑ u, Real.negMulLog (qStar (a, u)))
            = ∑ u, Real.negMulLog (κ' a.1 u * PX a.1))]
    rw [key (fun x ↦ ∑ u, Real.negMulLog (κ' x u * PX x)) (fun x hx ↦ by
        rw [le_antisymm (not_lt.mp hx) (hPX_nn x)]
        simp [Real.negMulLog_zero])]
    exact Finset.sum_congr rfl (fun x _ ↦
      Finset.sum_congr rfl (fun u _ ↦ by rw [hwz_val x u]))
  unfold wzMutualInfoXU mutualInfoPmf
  rw [hA, hB, hC]

/-! ### pmf-side product bounds for D2

The per-codeword AEP mass bound D2 is assembled purely from single-symbol pmf
products (no joint-sequence independence is available in D2's hypotheses). The
following three leaves convert the typical-set membership predicate into product
bounds on the alphabet-side laws `μ.map (Xs 0)`. -/

/-- `exp(-∑ pmfLog) = ∏ P`: the per-block likelihood as a product of single-symbol
masses, valid on a full-support alphabet. -/
private lemma exp_neg_sum_pmfLog_eq_prod
    {Ω A : Type*} [MeasurableSpace Ω] [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A]
    (μ : Measure Ω) (Xs : ℕ → Ω → A)
    (hpos : ∀ a : A, 0 < (μ.map (Xs 0)).real {a})
    (n : ℕ) (x : Fin n → A) :
    Real.exp (-(∑ i : Fin n, pmfLog μ Xs (x i)))
      = ∏ i : Fin n, (μ.map (Xs 0)).real {x i} := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have hlog : -(pmfLog μ Xs (x i)) = Real.log ((μ.map (Xs 0)).real {x i}) := by
    simp only [pmfLog, neg_neg]
  rw [hlog, Real.exp_log (hpos (x i))]

/-- pmf-side upper bound: for a typical block `x`, the product of single-symbol
masses is `≤ exp(-n(H - ε))`. Independence-free companion of `typicalSet_prob_le`. -/
private lemma prod_map_singleton_le_of_mem_typicalSet
    {Ω A : Type*} [MeasurableSpace Ω] [Fintype A] [DecidableEq A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure Ω) (Xs : ℕ → Ω → A)
    (hpos : ∀ a : A, 0 < (μ.map (Xs 0)).real {a})
    (n : ℕ) {ε : ℝ} (x : Fin n → A) (hx : x ∈ typicalSet μ Xs n ε) :
    ∏ i : Fin n, (μ.map (Xs 0)).real {x i}
      ≤ Real.exp (-(n : ℝ) * (entropy μ (Xs 0) - ε)) := by
  rw [mem_typicalSet_iff] at hx
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0; simp
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hlower : -ε < (∑ i : Fin n, pmfLog μ Xs (x i)) / n - entropy μ (Xs 0) :=
      (abs_lt.mp hx).1
    have hsum_gt : (n : ℝ) * (entropy μ (Xs 0) - ε) < ∑ i : Fin n, pmfLog μ Xs (x i) := by
      have h := (lt_div_iff₀ hnR).mp (by linarith :
        entropy μ (Xs 0) - ε < (∑ i : Fin n, pmfLog μ Xs (x i)) / n)
      linarith
    have hexp : Real.exp (-(∑ i : Fin n, pmfLog μ Xs (x i)))
        < Real.exp (-((n : ℝ) * (entropy μ (Xs 0) - ε))) :=
      Real.exp_lt_exp.mpr (by linarith)
    rw [exp_neg_sum_pmfLog_eq_prod μ Xs hpos n x] at hexp
    calc ∏ i : Fin n, (μ.map (Xs 0)).real {x i}
        ≤ Real.exp (-((n : ℝ) * (entropy μ (Xs 0) - ε))) := hexp.le
      _ = Real.exp (-(n : ℝ) * (entropy μ (Xs 0) - ε)) := by rw [neg_mul]

/-- pmf-side lower bound: for a typical block `x`, the product of single-symbol
masses is `≥ exp(-n(H + ε))`. Independence-free companion of `typicalSet_prob_ge`. -/
private lemma prod_map_singleton_ge_of_mem_typicalSet
    {Ω A : Type*} [MeasurableSpace Ω] [Fintype A] [DecidableEq A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure Ω) (Xs : ℕ → Ω → A)
    (hpos : ∀ a : A, 0 < (μ.map (Xs 0)).real {a})
    (n : ℕ) {ε : ℝ} (x : Fin n → A) (hx : x ∈ typicalSet μ Xs n ε) :
    Real.exp (-(n : ℝ) * (entropy μ (Xs 0) + ε))
      ≤ ∏ i : Fin n, (μ.map (Xs 0)).real {x i} := by
  rw [mem_typicalSet_iff] at hx
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0; simp
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hupper : (∑ i : Fin n, pmfLog μ Xs (x i)) / n - entropy μ (Xs 0) < ε :=
      (abs_lt.mp hx).2
    have hsum_lt : (∑ i : Fin n, pmfLog μ Xs (x i)) < (n : ℝ) * (entropy μ (Xs 0) + ε) := by
      have h := (div_lt_iff₀ hnR).mp (by linarith :
        (∑ i : Fin n, pmfLog μ Xs (x i)) / n < entropy μ (Xs 0) + ε)
      linarith
    have hexp : Real.exp (-((n : ℝ) * (entropy μ (Xs 0) + ε)))
        < Real.exp (-(∑ i : Fin n, pmfLog μ Xs (x i))) :=
      Real.exp_lt_exp.mpr (by linarith)
    rw [exp_neg_sum_pmfLog_eq_prod μ Xs hpos n x] at hexp
    calc Real.exp (-(n : ℝ) * (entropy μ (Xs 0) + ε))
        = Real.exp (-((n : ℝ) * (entropy μ (Xs 0) + ε))) := by rw [neg_mul]
      _ ≤ ∏ i : Fin n, (μ.map (Xs 0)).real {x i} := hexp.le

/-- Covering-codeword side-information mass upper bound. For any
fixed covering codeword `u : Fin n → Fin k`, the probability (over the noise generating
`Y^n = jointRV Ys n`) that `u` is jointly typical with `Y^n` is at most
`exp(−n · I_YU)`, where `I_YU ≲ I(U;Y)`. This is the per-codeword AEP mass bound that
`wz_codebook_confusion_expectation_le` consumes as its `hmass` hypothesis: because
the covering codewords are drawn independently of the side information `Y`, a fixed
covering codeword lands in a `Y^n`-conditional typical slice with the packing exponent
`exp(−n · I(U;Y))`.

The per-codeword form is assembled directly from single-symbol pmf products (no
joint-sequence independence is needed and none is available in the hypotheses). Reframing
the `ω`-event as the `Y`-law mass of the fixed-`u` slice
`{y | (u, y) ∈ jointlyTypicalSet}` (via `map_measureReal_apply` on `jointRV Ys n`), the
slice mass is bounded by `∑_{y} exp(−n(H(Y)−ε)) · [1 ≤ exp(n(H(Z)+ε))·∏ P_Z(u,y)]`; folding
in the joint-typical product lower bound (`prod_map_singleton_ge_of_mem_typicalSet`) and
marginalizing `∑_y ∏_i P_Z(u_i,y_i) = ∏_i P_U(u_i)` (`Finset.prod_univ_sum` +
`sum_real_prod_singleton_of_map_fst_eq`), the `U`-typical product bound
(`prod_map_singleton_le_of_mem_typicalSet`) gives `mass ≤ exp(−n(H(U)+H(Y)−H(U,Y)−3ε))
= exp(−n(I(U;Y)−3ε)) ≤ exp(−n·I_YU)` since `hI_YU : I_YU ≤ I(U;Y) − 3ε`. For an atypical `u`
the slice is empty and the mass is `0`.

The exponent slack `3ε` is exactly the sum of the joint-product slack (`ε`) and the
`Y`/`U` typicality slacks (`ε` each); `hI_YU` is a precondition supplying the standard
typicality slack, not load-bearing (the upper bound on `I_YU` only weakens the RHS
`exp(−n·I_YU)`). `hindepU`/`hidentU`/`hε` are inherited regularity preconditions that the
pmf-side assembly does not consume.
@audit:ok -/
lemma wz_covering_codeword_sideInfo_mass_le
    {Ω : Type*} [MeasurableSpace Ω] {k n : ℕ} [Nonempty (Fin k)]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Us : ℕ → Ω → Fin k) (Ys : ℕ → Ω → β) (ε : ℝ) (hε : 0 < ε)
    (hUs : ∀ i, Measurable (Us i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepU : iIndepFun (fun i ↦ Us i) μ)
    (hidentU : ∀ i, IdentDistrib (Us i) (Us 0) μ μ)
    (hindepY : iIndepFun (fun i ↦ Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hposU : ∀ u : Fin k, 0 < (μ.map (Us 0)).real {u})
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : Fin k × β,
        0 < (μ.map (ChannelCoding.jointSequence Us Ys 0)).real {p})
    (I_YU : ℝ)
    (hI_YU : I_YU ≤ entropy μ (Us 0) + entropy μ (Ys 0)
        - entropy μ (ChannelCoding.jointSequence Us Ys 0) - 3 * ε) :
    ∀ u : Fin n → Fin k,
      μ.real {ω | (u, jointRV Ys n ω)
          ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε}
        ≤ Real.exp (-(n : ℝ) * I_YU) := by
  classical
  intro u
  have hYmeas : Measurable (jointRV Ys n) := measurable_jointRV Ys hYs n
  haveI hMYprob : IsProbabilityMeasure (μ.map (jointRV Ys n)) :=
    Measure.isProbabilityMeasure_map hYmeas.aemeasurable
  haveI hMZprob : IsProbabilityMeasure (μ.map (ChannelCoding.jointSequence Us Ys 0)) :=
    Measure.isProbabilityMeasure_map
      (ChannelCoding.measurable_jointSequence Us Ys hUs hYs 0).aemeasurable
  -- Reframe the ω-event as the Y-law mass of the fixed-`u` fiber slice.
  have hpre : {ω | (u, jointRV Ys n ω)
        ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε}
      = jointRV Ys n ⁻¹' {y | (u, y) ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε} := rfl
  have hkey : μ.real {ω | (u, jointRV Ys n ω)
        ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε}
      = (μ.map (jointRV Ys n)).real
          {y | (u, y) ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε} := by
    rw [hpre, map_measureReal_apply hYmeas ((Set.toFinite _).measurableSet)]
  rw [hkey]
  set S : Set (Fin n → β) :=
    {y | (u, y) ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε} with hS_def
  by_cases hu : u ∈ typicalSet μ Us n ε
  · -- Main case: `u` is `U`-typical.
    set F : Finset (Fin n → β) := (Set.toFinite S).toFinset with hF_def
    have hcoe : (F : Set (Fin n → β)) = S := by
      rw [hF_def]; exact (Set.toFinite S).coe_toFinset
    have hmem : ∀ y ∈ F, (u, y) ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε := by
      intro y hy
      have hyS : y ∈ S := (Set.Finite.mem_toFinset (Set.toFinite S)).mp hy
      exact hyS
    -- Y-side per-atom mass bound.
    have hYterm : ∀ y ∈ F,
        (μ.map (jointRV Ys n)).real {y}
          ≤ Real.exp (-(n : ℝ) * (entropy μ (Ys 0) - ε)) := by
      intro y hy
      have hy2 : y ∈ typicalSet μ Ys n ε :=
        ((ChannelCoding.mem_jointlyTypicalSet_iff μ Us Ys n ε u y).mp (hmem y hy)).2.1
      exact typicalSet_prob_le μ Ys hYs hindepY hidentY hposY n y hy2
    -- Joint-side per-atom product lower bound.
    have hZterm : ∀ y ∈ F,
        Real.exp (-(n : ℝ) * (entropy μ (ChannelCoding.jointSequence Us Ys 0) + ε))
          ≤ ∏ i : Fin n, (μ.map (ChannelCoding.jointSequence Us Ys 0)).real {(u i, y i)} := by
      intro y hy
      have hy3 : (fun i ↦ (u i, y i))
          ∈ typicalSet μ (ChannelCoding.jointSequence Us Ys) n ε :=
        ((ChannelCoding.mem_jointlyTypicalSet_iff μ Us Ys n ε u y).mp (hmem y hy)).2.2
      exact prod_map_singleton_ge_of_mem_typicalSet μ
        (ChannelCoding.jointSequence Us Ys) hposZ n (fun i ↦ (u i, y i)) hy3
    -- Combined per-term bound: fold the trivial factor `1 ≤ exp · ∏`.
    have hperterm : ∀ y ∈ F,
        (μ.map (jointRV Ys n)).real {y}
          ≤ (Real.exp (-(n : ℝ) * (entropy μ (Ys 0) - ε))
              * Real.exp ((n : ℝ) * (entropy μ (ChannelCoding.jointSequence Us Ys 0) + ε)))
            * ∏ i : Fin n,
                (μ.map (ChannelCoding.jointSequence Us Ys 0)).real {(u i, y i)} := by
      intro y hy
      have h1 := hYterm y hy
      have h2 := hZterm y hy
      have hC2pos : (0 : ℝ) <
          Real.exp ((n : ℝ) * (entropy μ (ChannelCoding.jointSequence Us Ys 0) + ε)) :=
        Real.exp_pos _
      have heq1 :
          Real.exp ((n : ℝ) * (entropy μ (ChannelCoding.jointSequence Us Ys 0) + ε))
            * Real.exp (-(n : ℝ) * (entropy μ (ChannelCoding.jointSequence Us Ys 0) + ε))
            = 1 := by
        rw [← Real.exp_add]; simp
      have hone : (1 : ℝ) ≤
          Real.exp ((n : ℝ) * (entropy μ (ChannelCoding.jointSequence Us Ys 0) + ε))
            * ∏ i : Fin n,
                (μ.map (ChannelCoding.jointSequence Us Ys 0)).real {(u i, y i)} := by
        have hmul := mul_le_mul_of_nonneg_left h2 hC2pos.le
        rwa [heq1] at hmul
      calc (μ.map (jointRV Ys n)).real {y}
          ≤ Real.exp (-(n : ℝ) * (entropy μ (Ys 0) - ε)) := h1
        _ = Real.exp (-(n : ℝ) * (entropy μ (Ys 0) - ε)) * 1 := (mul_one _).symm
        _ ≤ Real.exp (-(n : ℝ) * (entropy μ (Ys 0) - ε))
              * (Real.exp ((n : ℝ) * (entropy μ (ChannelCoding.jointSequence Us Ys 0) + ε))
                * ∏ i : Fin n,
                    (μ.map (ChannelCoding.jointSequence Us Ys 0)).real {(u i, y i)}) :=
              mul_le_mul_of_nonneg_left hone (Real.exp_nonneg _)
        _ = (Real.exp (-(n : ℝ) * (entropy μ (Ys 0) - ε))
              * Real.exp ((n : ℝ) * (entropy μ (ChannelCoding.jointSequence Us Ys 0) + ε)))
            * ∏ i : Fin n,
                (μ.map (ChannelCoding.jointSequence Us Ys 0)).real {(u i, y i)} := by
              rw [mul_assoc]
    -- Marginalization: summing the joint product over all `y` recovers `∏ P_U`.
    have hmarg :
        (μ.map (ChannelCoding.jointSequence Us Ys 0)).map Prod.fst = μ.map (Us 0) := by
      rw [Measure.map_map measurable_fst
        (ChannelCoding.measurable_jointSequence Us Ys hUs hYs 0)]
      rfl
    have hmarginal :
        (∑ y : Fin n → β, ∏ i : Fin n,
            (μ.map (ChannelCoding.jointSequence Us Ys 0)).real {(u i, y i)})
          = ∏ i : Fin n, (μ.map (Us 0)).real {u i} := by
      have hpe := Finset.prod_univ_sum (fun _ : Fin n ↦ (Finset.univ : Finset β))
        (fun (i : Fin n) (b : β) ↦
          (μ.map (ChannelCoding.jointSequence Us Ys 0)).real {(u i, b)})
      rw [Fintype.piFinset_univ] at hpe
      rw [← hpe]
      refine Finset.prod_congr rfl (fun i _ ↦ ?_)
      exact sum_real_prod_singleton_of_map_fst_eq
        (μ.map (ChannelCoding.jointSequence Us Ys 0)) (μ.map (Us 0)) hmarg (u i)
    -- `∏ P_U ≤ exp(-n(H(U) - ε))` from `U`-typicality of `u`.
    have hUbound : ∏ i : Fin n, (μ.map (Us 0)).real {u i}
        ≤ Real.exp (-(n : ℝ) * (entropy μ (Us 0) - ε)) :=
      prod_map_singleton_le_of_mem_typicalSet μ Us hposU n u hu
    -- Constant-factor closure of the exponents.
    have hExpFactor :
        (Real.exp (-(n : ℝ) * (entropy μ (Ys 0) - ε))
          * Real.exp ((n : ℝ) * (entropy μ (ChannelCoding.jointSequence Us Ys 0) + ε)))
          * Real.exp (-(n : ℝ) * (entropy μ (Us 0) - ε))
        ≤ Real.exp (-(n : ℝ) * I_YU) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hexp_eq :
          -(n : ℝ) * (entropy μ (Ys 0) - ε)
            + (n : ℝ) * (entropy μ (ChannelCoding.jointSequence Us Ys 0) + ε)
            + -(n : ℝ) * (entropy μ (Us 0) - ε)
          = -(n : ℝ) * (entropy μ (Us 0) + entropy μ (Ys 0)
              - entropy μ (ChannelCoding.jointSequence Us Ys 0) - 3 * ε) := by ring
      rw [hexp_eq]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have := mul_le_mul_of_nonneg_left hI_YU hn
      rw [neg_mul, neg_mul]
      linarith
    -- Chain everything.
    calc (μ.map (jointRV Ys n)).real S
        = ∑ y ∈ F, (μ.map (jointRV Ys n)).real {y} := by
          rw [← hcoe, ← sum_measureReal_singleton]
      _ ≤ ∑ y ∈ F,
            (Real.exp (-(n : ℝ) * (entropy μ (Ys 0) - ε))
              * Real.exp ((n : ℝ) * (entropy μ (ChannelCoding.jointSequence Us Ys 0) + ε)))
            * ∏ i : Fin n,
                (μ.map (ChannelCoding.jointSequence Us Ys 0)).real {(u i, y i)} :=
          Finset.sum_le_sum hperterm
      _ = (Real.exp (-(n : ℝ) * (entropy μ (Ys 0) - ε))
            * Real.exp ((n : ℝ) * (entropy μ (ChannelCoding.jointSequence Us Ys 0) + ε)))
          * ∑ y ∈ F, ∏ i : Fin n,
              (μ.map (ChannelCoding.jointSequence Us Ys 0)).real {(u i, y i)} := by
          rw [← Finset.mul_sum]
      _ ≤ (Real.exp (-(n : ℝ) * (entropy μ (Ys 0) - ε))
            * Real.exp ((n : ℝ) * (entropy μ (ChannelCoding.jointSequence Us Ys 0) + ε)))
          * ∑ y : Fin n → β, ∏ i : Fin n,
              (μ.map (ChannelCoding.jointSequence Us Ys 0)).real {(u i, y i)} := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
            (fun y _ _ ↦ Finset.prod_nonneg (fun i _ ↦ measureReal_nonneg))
      _ = (Real.exp (-(n : ℝ) * (entropy μ (Ys 0) - ε))
            * Real.exp ((n : ℝ) * (entropy μ (ChannelCoding.jointSequence Us Ys 0) + ε)))
          * ∏ i : Fin n, (μ.map (Us 0)).real {u i} := by rw [hmarginal]
      _ ≤ (Real.exp (-(n : ℝ) * (entropy μ (Ys 0) - ε))
            * Real.exp ((n : ℝ) * (entropy μ (ChannelCoding.jointSequence Us Ys 0) + ε)))
          * Real.exp (-(n : ℝ) * (entropy μ (Us 0) - ε)) := by
          apply mul_le_mul_of_nonneg_left hUbound (by positivity)
      _ ≤ Real.exp (-(n : ℝ) * I_YU) := hExpFactor
  · -- `u` not `U`-typical: the slice is empty, mass is `0`.
    have hSempty : S = ∅ := by
      rw [hS_def]
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hy
      exact hu ((ChannelCoding.mem_jointlyTypicalSet_iff μ Us Ys n ε u y).mp hy).1
    rw [hSempty, measureReal_empty]
    exact (Real.exp_pos _).le

end InformationTheory.Shannon
