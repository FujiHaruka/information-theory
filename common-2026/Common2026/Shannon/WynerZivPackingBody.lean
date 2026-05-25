import Common2026.Shannon.WynerZivBinningCovering
import Mathlib.MeasureTheory.Integral.Average

/-!
# Wyner–Ziv L-WZ1 packing body discharge (T3-D wave9 gap-close, W9-G2)

This file **discharges the packing side** of the Wyner–Ziv random-binning
achievability body. The wave7 `WynerZivBinningCovering.lean` introduced the
covering / packing decomposition with two predicate pass-throughs
(`IsWynerZivBinningCovering`, `IsWynerZivBinningPacking`); a sibling wave9
seed discharges the *covering* side from the AEP joint-typicality probability.
The present seed discharges the *packing* side from the **random-binning
union bound + collision probability `1/M`** — i.e. the genuine
information-theoretic content behind `IsWynerZivBinningPacking`.

## Approach

The packing lemma (Cover–Thomas §15.9 / Lemma 15.x mutual covering) states:
at binning rate `R₂` with `M = 2^{n R₂}` bins, the probability that some
alias `u' ≠ u^n` in the same bin is jointly typical with the side-info
`y^n` vanishes, provided the *conditional typical slice* `T^n_{U|Y=y^n}`
(the set of `u'` jointly typical with `y^n`) is small relative to `M`.

We discharge it in four layers, mirroring the (already-published) Slepian–Wolf
`swError_EX_expectation_le` averaging argument verbatim, specialised to the
single side-info-`Y` axis:

1. **Per-`ω` union bound** (`wzBinning_alias_expectation_le`): for a fixed
   source realization `ω`, the `wzBinningMeasure`-mass of the set of bad
   hashes (those for which some slice member collides with the truth) is at
   most `|slice| · (1/M)`. Pure union bound + `wzBinning_collision_prob`.
2. **Averaged `E_bin` bound** (`wzBinning_E_bin_expectation_le`): a Tonelli
   swap on the product `μ ⊗ wzBinningMeasure` turns the per-`ω` bound into
   `∫ μ.real(E_bin) ∂(wzBinningMeasure) ≤ S · (1/M)`, where `S` uniformly
   bounds every per-`ω` slice cardinality.
3. **Existence of a good hash** (`wzPacking_exists_good_hash`): the first
   moment method (`MeasureTheory.exists_le_integral`) extracts a *single*
   hash `f_U` whose `E_bin`-mass is at most the average `S/M`, discharging
   `IsWynerZivBinningPacking R₂ (S/M) μ Us Ys JT f_U`.
4. **Re-publish decoder failure** (`wyner_ziv_packing_decoder_fail`): combine
   the discharged packing predicate with a covering predicate via the wave7
   `wyner_ziv_binning_via_covering_packing`, yielding the `ε₁ + S/M` decoder
   failure bound — and its asymptotic `→ 0` form when `S/M → 0`.

The two genuinely-deep ingredients are kept as **sub-predicate hypotheses**
so the body itself is the pure combinatorial discharge:

* **`IsPackingTypicalityHyp S JT`** — the conditional typical slice
  cardinality is `≤ S`, uniformly over the side-info. Its discharge is the
  3-letter analog of `conditionalTypicalSlice_card_le` (separate seed); here
  it is the *only* information-theoretic input the packing body consumes.
* **`IsPackingCollisionBoundHyp`** — measurability of every per-`f_U`
  `E_bin` event over `Ω`, needed for the Tonelli swap. (In the concrete
  instantiation `JT` is decidable and `Ω` finite, so this is automatic; we
  carry it as a hypothesis to keep the body alphabet-agnostic.)

## 撤退ライン

* **Slice cardinality `IsPackingTypicalityHyp`** — taken as input. The genuine
  bound `|T^n_{U|Y=y}| ≤ exp(n(H(U|Y)+2ε))` is the responsibility of a
  separate (typical-slice) seed; it is `y`-independent, so a single `S` works.
* **Per-`f_U` `E_bin` measurability** — taken as input via
  `IsPackingCollisionBoundHyp`. Automatic in the concrete finite-`Ω`
  instantiation; carried abstractly here.
* **`R₂` as bookkeeping** — the rate parameter enters only through the
  numerical relationship `S = exp(n(H(U|Y)+2ε))` and `M = exp(n R₂)`; the
  body works with the *error tolerance* `S/M` directly, leaving the
  `S/M → 0` arithmetic (which needs `R₂ > I(Y;U)`) to the asymptotic wrapper.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — Packing sub-predicates

We factor the packing lemma into two named hypotheses so that the body
discharge below is the *pure combinatorial argument*, with the deep
information-theoretic content (slice cardinality) and the technical
plumbing (per-`f_U` measurability) exposed as inputs.
-/

section SubPredicates

variable {Ω U β : Type*} [MeasurableSpace Ω]
variable [Fintype U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [MeasurableSpace β]

/-- **Packing typicality hypothesis.** The conditional typical slice
`{u' | JT (u', y)}` (the set of auxiliary sequences jointly typical with a
fixed side-info `y`) has cardinality at most `S`, uniformly over `y`.

This is the *only* genuinely information-theoretic input the packing body
consumes: in the concrete instantiation `S = exp(n(H(U|Y)+2ε))`, discharged
by a separate typical-slice seed. The bound is `y`-independent, so a single
`S` suffices.

`@audit:retract-candidate(load-bearing-predicate)` — load-bearing
hypothesis-form predicate marked for eventual deletion once the in-family
discharge plan (`wyner-ziv-discharge-moonshot-plan`) closes its in-family
consumers; no cross-family consumer. -/
def IsPackingTypicalityHyp
    {n : ℕ} (S : ℝ)
    (JT : (Fin n → U) × (Fin n → β) → Prop) : Prop :=
  ∀ y : Fin n → β,
    ((wzConditionalTypicalSlice (n := n) JT y).toFinite.toFinset.card : ℝ) ≤ S

/-- **Packing collision-bound (measurability) hypothesis.** Every per-hash
`E_bin` event is measurable over `Ω`. Needed for the Tonelli swap that turns
the per-`ω` union bound into the averaged `E_bin` bound.

Automatic in the concrete finite-`Ω` / decidable-`JT` instantiation; carried
abstractly here to keep the body alphabet-agnostic.

`@audit:retract-candidate(load-bearing-predicate)` — load-bearing
hypothesis-form predicate marked for eventual deletion once the in-family
discharge plan (`wyner-ziv-discharge-moonshot-plan`) closes its in-family
consumers; no cross-family consumer. -/
def IsPackingCollisionBoundHyp
    {n M : ℕ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop)
    (f_U : (Fin n → U) → Fin M) : Prop :=
  MeasurableSet (wzError_E_bin (n := n) Us Ys JT f_U)

/-- Unfolding lemma for `IsPackingTypicalityHyp`. -/
lemma IsPackingTypicalityHyp_def
    {n : ℕ} {S : ℝ}
    {JT : (Fin n → U) × (Fin n → β) → Prop} :
    IsPackingTypicalityHyp (n := n) S JT ↔
      ∀ y : Fin n → β,
        ((wzConditionalTypicalSlice (n := n) JT y).toFinite.toFinset.card : ℝ) ≤ S :=
  Iff.rfl

/-- The packing typicality hypothesis is monotone in the slice bound. -/
lemma IsPackingTypicalityHyp.mono
    {n : ℕ} {S S' : ℝ}
    {JT : (Fin n → U) × (Fin n → β) → Prop}
    (h : IsPackingTypicalityHyp (n := n) S JT) (hS : S ≤ S') :
    IsPackingTypicalityHyp (n := n) S' JT :=
  fun y => le_trans (h y) hS

end SubPredicates

/-! ## Section 2 — Per-`ω` alias union bound

The Wyner–Ziv mirror of `SlepianWolfFullRateRegion.binning_alias_expectation_le_aux`,
specialised to the single side-info-`Y` axis. For a fixed truth `u^n` and a
deterministic candidate-alias set `S`, the `wzBinningMeasure`-mass of the
"some `u' ∈ S` with `u' ≠ truth` collides with truth" event is `≤ |S| / M`.
-/

section AliasUnionBound

variable {U : Type*} [Fintype U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]

/-- **Wyner–Ziv random-binning alias expectation bound.** For a fixed truth
`u^n` and a (deterministic) finite candidate-alias set `S`, the
`wzBinningMeasure`-probability that some `u' ∈ S` with `u' ≠ truth` hashes to
the same bin as `truth` is at most `|S| / M`.

Pure union bound (`measureReal_biUnion_finset_le`) + per-alias collision
`1/M` (`wzBinning_collision_prob`). -/
lemma wzBinning_alias_expectation_le
    {n M : ℕ} [NeZero M]
    (truth : Fin n → U) (S : Finset (Fin n → U)) :
    (wzBinningMeasure U n M).real
        { f_U | ∃ u' ∈ S, u' ≠ truth ∧ f_U u' = f_U truth }
      ≤ (S.card : ℝ) * ((M : ℝ))⁻¹ := by
  classical
  -- Filter out the truth itself; the union is over genuine aliases.
  set T : Finset (Fin n → U) := S.filter (· ≠ truth) with hT_def
  set evt : Set ((Fin n → U) → Fin M) :=
      { f_U | ∃ u' ∈ S, u' ≠ truth ∧ f_U u' = f_U truth } with hevt_def
  set unionEvt : Set ((Fin n → U) → Fin M) :=
      ⋃ u' ∈ T, { f_U | f_U u' = f_U truth } with hunionEvt_def
  have h_sub : evt ⊆ unionEvt := by
    intro f hf
    rcases hf with ⟨u', huS, hne, hcoll⟩
    refine Set.mem_iUnion₂.mpr ⟨u', ?_, hcoll⟩
    simp [T, huS, hne]
  -- Lift to `μ.real` via monotonicity.
  have h_step1 :
      (wzBinningMeasure U n M).real evt
        ≤ (wzBinningMeasure U n M).real unionEvt :=
    measureReal_mono h_sub (measure_ne_top _ _)
  -- Union bound.
  have h_step2 :
      (wzBinningMeasure U n M).real unionEvt
        ≤ ∑ u' ∈ T,
            (wzBinningMeasure U n M).real { f_U | f_U u' = f_U truth } :=
    measureReal_biUnion_finset_le _ _
  -- Each summand is exactly `(M)⁻¹` (alias distinct from truth).
  have h_summand : ∀ u' ∈ T,
      (wzBinningMeasure U n M).real { f_U | f_U u' = f_U truth } = ((M : ℝ))⁻¹ := by
    intro u' hu'
    have hne : u' ≠ truth := (Finset.mem_filter.mp hu').2
    exact wzBinning_collision_prob hne
  have h_step3 :
      (∑ u' ∈ T,
          (wzBinningMeasure U n M).real { f_U | f_U u' = f_U truth })
        = (T.card : ℝ) * ((M : ℝ))⁻¹ := by
    rw [Finset.sum_congr rfl h_summand, Finset.sum_const, nsmul_eq_mul]
  have h_card : (T.card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast Finset.card_filter_le S _
  have h_inv_nn : (0 : ℝ) ≤ ((M : ℝ))⁻¹ :=
    inv_nonneg.mpr (by exact_mod_cast Nat.zero_le _)
  calc (wzBinningMeasure U n M).real evt
      ≤ (wzBinningMeasure U n M).real unionEvt := h_step1
    _ ≤ ∑ u' ∈ T,
          (wzBinningMeasure U n M).real { f_U | f_U u' = f_U truth } := h_step2
    _ = (T.card : ℝ) * ((M : ℝ))⁻¹ := h_step3
    _ ≤ (S.card : ℝ) * ((M : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right h_card h_inv_nn

end AliasUnionBound

/-! ## Section 3 — Averaged `E_bin` bound (Tonelli swap)

Mirror of `swError_EX_expectation_le`: the per-`ω` union bound plus a
Tonelli swap on `μ ⊗ wzBinningMeasure` yields the averaged `E_bin` bound
`∫ μ.real(E_bin) ∂(wzBinningMeasure) ≤ S · (1/M)`.
-/

section AveragedBound

variable {Ω U β : Type*} [MeasurableSpace Ω]
variable [Fintype U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [MeasurableSpace β]

/-- **Per-`ω` `E_bin` slice rewrite.** For fixed `ω`, the set of hashes for
which `ω ∈ E_bin` equals the binning-alias form over the conditional typical
slice `{u' | JT (u', Ys ω)}` (as a `Finset`). Definitional unfold of
`wzError_E_bin`. -/
lemma wzError_E_bin_per_omega_set_eq
    {n M : ℕ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop)
    (ω : Ω) :
    { f_U : (Fin n → U) → Fin M | ω ∈ wzError_E_bin (n := n) Us Ys JT f_U }
      = { f_U | ∃ u' ∈ (wzConditionalTypicalSlice (n := n) JT (Ys ω)).toFinite.toFinset,
              u' ≠ Us ω ∧ f_U u' = f_U (Us ω) } := by
  classical
  ext f_U
  simp only [Set.mem_setOf_eq, wzError_E_bin, Set.Finite.mem_toFinset,
    wzConditionalTypicalSlice]
  constructor
  · rintro ⟨u', hne, hhash, htyp⟩
    exact ⟨u', htyp, hne, hhash⟩
  · rintro ⟨u', htyp, hne, hhash⟩
    exact ⟨u', hne, hhash, htyp⟩

/-- **Per-`ω` `E_bin` mass bound.** For fixed `ω`, the `wzBinningMeasure`-mass
of `{f_U | ω ∈ E_bin}` is at most `S · (1/M)`, given the slice cardinality
bound `S`. Combines `wzError_E_bin_per_omega_set_eq` with
`wzBinning_alias_expectation_le` and `IsPackingTypicalityHyp`. -/
lemma wzBinning_E_bin_per_omega_le
    {n M : ℕ} [NeZero M] {S : ℝ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop)
    (h_slice : IsPackingTypicalityHyp (n := n) S JT)
    (ω : Ω) :
    (wzBinningMeasure U n M).real
        { f_U | ω ∈ wzError_E_bin (n := n) Us Ys JT f_U }
      ≤ S * ((M : ℝ))⁻¹ := by
  classical
  set Sset : Finset (Fin n → U) :=
    (wzConditionalTypicalSlice (n := n) JT (Ys ω)).toFinite.toFinset with hSset_def
  rw [wzError_E_bin_per_omega_set_eq Us Ys JT ω]
  have hA :
      (wzBinningMeasure U n M).real
          { f_U | ∃ u' ∈ Sset, u' ≠ Us ω ∧ f_U u' = f_U (Us ω) }
        ≤ (Sset.card : ℝ) * ((M : ℝ))⁻¹ :=
    wzBinning_alias_expectation_le (Us ω) Sset
  have hB : (Sset.card : ℝ) ≤ S := h_slice (Ys ω)
  have h_inv_nn : (0 : ℝ) ≤ ((M : ℝ))⁻¹ :=
    inv_nonneg.mpr (by exact_mod_cast Nat.zero_le _)
  calc (wzBinningMeasure U n M).real
          { f_U | ∃ u' ∈ Sset, u' ≠ Us ω ∧ f_U u' = f_U (Us ω) }
      ≤ (Sset.card : ℝ) * ((M : ℝ))⁻¹ := hA
    _ ≤ S * ((M : ℝ))⁻¹ := mul_le_mul_of_nonneg_right hB h_inv_nn

/-- **Averaged `E_bin` bound.** The expected `μ`-mass of the `E_bin` error
event over the random binning is at most `S · (1/M)`. Tonelli swap on the
product `μ ⊗ wzBinningMeasure` reduces the average to the uniform per-`ω`
bound. Mirror of `swError_EX_expectation_le`. -/
theorem wzBinning_E_bin_expectation_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n M : ℕ} [NeZero M] {S : ℝ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop)
    (hS_nn : 0 ≤ S)
    (h_slice : IsPackingTypicalityHyp (n := n) S JT)
    (h_meas : ∀ f_U : (Fin n → U) → Fin M,
      IsPackingCollisionBoundHyp (n := n) Us Ys JT f_U) :
    ∫ f_U : (Fin n → U) → Fin M,
        μ.real (wzError_E_bin (n := n) Us Ys JT f_U)
      ∂(wzBinningMeasure U n M)
      ≤ S * ((M : ℝ))⁻¹ := by
  classical
  haveI : MeasurableSingletonClass ((Fin n → U) → Fin M) :=
    Pi.instMeasurableSingletonClass
  haveI : Fintype ((Fin n → U) → Fin M) := Pi.instFintype
  set B : Measure ((Fin n → U) → Fin M) := wzBinningMeasure U n M with hB_def
  -- `S` is non-negative (it bounds a cardinality at `Ys ω` for any chosen ω;
  -- but to avoid needing `Ω` nonempty we derive it from the empty-slice case).
  have hMinv_nn : (0 : ℝ) ≤ ((M : ℝ))⁻¹ :=
    inv_nonneg.mpr (by exact_mod_cast Nat.zero_le _)
  -- Each `wzError_E_bin ... f_U` is measurable over Ω (hypothesis bundle).
  have h_meas_bin : ∀ f_U : (Fin n → U) → Fin M,
      MeasurableSet (wzError_E_bin (n := n) Us Ys JT f_U) := h_meas
  -- Per-ω bound on the inner B-mass.
  have h_per_omega : ∀ ω : Ω,
      B.real { f_U | ω ∈ wzError_E_bin (n := n) Us Ys JT f_U }
        ≤ S * ((M : ℝ))⁻¹ :=
    fun ω => wzBinning_E_bin_per_omega_le Us Ys JT h_slice ω
  -- `S * (M)⁻¹ ≥ 0`.
  have hSM_nn : 0 ≤ S * ((M : ℝ))⁻¹ := mul_nonneg hS_nn hMinv_nn
  -- Product set E ⊆ B-space × Ω.
  set E : Set (((Fin n → U) → Fin M) × Ω) :=
    { p | p.2 ∈ wzError_E_bin (n := n) Us Ys JT p.1 } with hE_def
  have hE_meas : MeasurableSet E := by
    have h_decomp : E = ⋃ f_U : (Fin n → U) → Fin M,
        ({f_U} : Set ((Fin n → U) → Fin M)) ×ˢ wzError_E_bin (n := n) Us Ys JT f_U := by
      ext ⟨g, ω⟩
      simp [E]
    rw [h_decomp]
    refine MeasurableSet.iUnion (fun f_U => ?_)
    exact (measurableSet_singleton _).prod (h_meas_bin f_U)
  -- Fubini both ways on `μ ⊗ B`.
  have h_fubini1 :
      (B.prod μ) E = ∫⁻ f_U, μ (wzError_E_bin (n := n) Us Ys JT f_U) ∂B := by
    rw [Measure.prod_apply hE_meas]
    congr 1
  have h_fubini2 :
      (B.prod μ) E
        = ∫⁻ ω, B { f_U | ω ∈ wzError_E_bin (n := n) Us Ys JT f_U } ∂μ := by
    rw [Measure.prod_apply_symm hE_meas]
    congr 1
  have h_swap :
      ∫⁻ f_U, μ (wzError_E_bin (n := n) Us Ys JT f_U) ∂B
        = ∫⁻ ω, B { f_U | ω ∈ wzError_E_bin (n := n) Us Ys JT f_U } ∂μ := by
    rw [← h_fubini1, h_fubini2]
  -- Per-ω bound at the ENNReal level.
  have h_per_omega_ennreal : ∀ ω : Ω,
      B { f_U | ω ∈ wzError_E_bin (n := n) Us Ys JT f_U }
        ≤ ENNReal.ofReal (S * ((M : ℝ))⁻¹) := by
    intro ω
    have hr := h_per_omega ω
    have hne_top : B { f_U | ω ∈ wzError_E_bin (n := n) Us Ys JT f_U } ≠ ∞ :=
      measure_ne_top _ _
    rw [show B.real { f_U | ω ∈ wzError_E_bin (n := n) Us Ys JT f_U }
          = (B { f_U | ω ∈ wzError_E_bin (n := n) Us Ys JT f_U }).toReal from rfl] at hr
    calc B { f_U | ω ∈ wzError_E_bin (n := n) Us Ys JT f_U }
        = ENNReal.ofReal (B { f_U | ω ∈ wzError_E_bin (n := n) Us Ys JT f_U }).toReal := by
          rw [ENNReal.ofReal_toReal hne_top]
      _ ≤ ENNReal.ofReal (S * ((M : ℝ))⁻¹) := ENNReal.ofReal_le_ofReal hr
  have h_lint_le :
      ∫⁻ ω, B { f_U | ω ∈ wzError_E_bin (n := n) Us Ys JT f_U } ∂μ
        ≤ ENNReal.ofReal (S * ((M : ℝ))⁻¹) := by
    calc ∫⁻ ω, B { f_U | ω ∈ wzError_E_bin (n := n) Us Ys JT f_U } ∂μ
        ≤ ∫⁻ _, ENNReal.ofReal (S * ((M : ℝ))⁻¹) ∂μ :=
          lintegral_mono h_per_omega_ennreal
      _ = ENNReal.ofReal (S * ((M : ℝ))⁻¹) * μ Set.univ := by rw [lintegral_const]
      _ = ENNReal.ofReal (S * ((M : ℝ))⁻¹) := by rw [measure_univ, mul_one]
  -- Convert the Bochner outer integral to a lintegral and conclude.
  have h_int_nn : 0 ≤ᵐ[B] fun f_U => μ.real (wzError_E_bin (n := n) Us Ys JT f_U) :=
    Filter.Eventually.of_forall (fun _ => measureReal_nonneg)
  have h_int_meas :
      AEStronglyMeasurable
        (fun f_U : (Fin n → U) → Fin M =>
          μ.real (wzError_E_bin (n := n) Us Ys JT f_U)) B := by
    apply Measurable.aestronglyMeasurable
    exact Measurable.of_discrete
  rw [integral_eq_lintegral_of_nonneg_ae h_int_nn h_int_meas]
  have h_ofReal_eq : ∀ f_U : (Fin n → U) → Fin M,
      ENNReal.ofReal (μ.real (wzError_E_bin (n := n) Us Ys JT f_U))
        = μ (wzError_E_bin (n := n) Us Ys JT f_U) := by
    intro f_U
    have hne_top : μ (wzError_E_bin (n := n) Us Ys JT f_U) ≠ ∞ := measure_ne_top _ _
    rw [show μ.real (wzError_E_bin (n := n) Us Ys JT f_U)
          = (μ (wzError_E_bin (n := n) Us Ys JT f_U)).toReal from rfl,
        ENNReal.ofReal_toReal hne_top]
  have h_lint_eq :
      ∫⁻ f_U, ENNReal.ofReal (μ.real (wzError_E_bin (n := n) Us Ys JT f_U)) ∂B
        = ∫⁻ f_U, μ (wzError_E_bin (n := n) Us Ys JT f_U) ∂B :=
    lintegral_congr (fun f_U => h_ofReal_eq f_U)
  rw [h_lint_eq, h_swap]
  calc (∫⁻ ω, B { f_U | ω ∈ wzError_E_bin (n := n) Us Ys JT f_U } ∂μ).toReal
      ≤ (ENNReal.ofReal (S * ((M : ℝ))⁻¹)).toReal := by
        exact ENNReal.toReal_mono ENNReal.ofReal_ne_top h_lint_le
    _ = S * ((M : ℝ))⁻¹ := ENNReal.toReal_ofReal hSM_nn

end AveragedBound

/-! ## Section 4 — Existence of a good hash ⇒ packing predicate discharge

The first moment method: since the *average* `E_bin`-mass is `≤ S/M`, some
single hash `f_U` achieves `μ.real(E_bin f_U) ≤ S/M`, discharging the wave7
`IsWynerZivBinningPacking` predicate for that hash.
-/

section GoodHash

variable {Ω U β : Type*} [MeasurableSpace Ω]
variable [Fintype U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [MeasurableSpace β]

/-- **Existence of a good hash (first moment method).** Given the averaged
`E_bin` bound `≤ S/M`, there is a single hash `f_U` whose `E_bin`-mass is at
most `S/M`. This is `MeasureTheory.exists_le_integral` applied to the
non-negative integrand `f_U ↦ μ.real(E_bin f_U)` over the probability measure
`wzBinningMeasure`. -/
theorem wzPacking_exists_good_hash
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n M : ℕ} [NeZero M] {S : ℝ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop)
    (hS_nn : 0 ≤ S)
    (h_slice : IsPackingTypicalityHyp (n := n) S JT)
    (h_meas : ∀ f_U : (Fin n → U) → Fin M,
      IsPackingCollisionBoundHyp (n := n) Us Ys JT f_U) :
    ∃ f_U : (Fin n → U) → Fin M,
      μ.real (wzError_E_bin (n := n) Us Ys JT f_U) ≤ S * ((M : ℝ))⁻¹ := by
  classical
  haveI : MeasurableSingletonClass ((Fin n → U) → Fin M) :=
    Pi.instMeasurableSingletonClass
  haveI : Fintype ((Fin n → U) → Fin M) := Pi.instFintype
  -- Average bound: `∫ μ.real(E_bin) ∂B ≤ S/M`.
  have h_avg :
      ∫ f_U : (Fin n → U) → Fin M,
          μ.real (wzError_E_bin (n := n) Us Ys JT f_U)
        ∂(wzBinningMeasure U n M)
        ≤ S * ((M : ℝ))⁻¹ :=
    wzBinning_E_bin_expectation_le μ Us Ys JT hS_nn h_slice h_meas
  -- First moment method: some hash is ≤ the average.
  have h_int :
      Integrable
        (fun f_U : (Fin n → U) → Fin M =>
          μ.real (wzError_E_bin (n := n) Us Ys JT f_U))
        (wzBinningMeasure U n M) := Integrable.of_finite
  obtain ⟨f_U, hf_U⟩ := exists_le_integral (μ := wzBinningMeasure U n M) h_int
  exact ⟨f_U, le_trans hf_U h_avg⟩

/-- **Packing predicate discharge.** The good hash from
`wzPacking_exists_good_hash` discharges the wave7 `IsWynerZivBinningPacking`
predicate at error tolerance `ε₂ = S/M` (for any bookkeeping rate `R₂`).
This is the headline `IsWynerZivBinningPacking` *body discharge*: the
predicate that wave7 left as a pass-through is now produced from the union
bound + collision probability + slice cardinality. -/
theorem wzPacking_isPacking_of_typicality
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n M : ℕ} [NeZero M] {S R₂ : ℝ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop)
    (hS_nn : 0 ≤ S)
    (h_slice : IsPackingTypicalityHyp (n := n) S JT)
    (h_meas : ∀ f_U : (Fin n → U) → Fin M,
      IsPackingCollisionBoundHyp (n := n) Us Ys JT f_U) :
    ∃ f_U : (Fin n → U) → Fin M,
      IsWynerZivBinningPacking R₂ (S * ((M : ℝ))⁻¹) μ Us Ys JT f_U := by
  obtain ⟨f_U, hf_U⟩ :=
    wzPacking_exists_good_hash μ Us Ys JT hS_nn h_slice h_meas
  refine ⟨f_U, ?_⟩
  rw [IsWynerZivBinningPacking_def]
  exact hf_U

end GoodHash

/-! ## Section 5 — Re-publish: covering + packing ⇒ decoder failure bound

Merge the discharged packing predicate with a covering predicate (from the
sibling covering-body seed) via the wave7
`wyner_ziv_binning_via_covering_packing`, yielding the decoder-failure bound
`ε₁ + S/M` for the good hash — and its asymptotic `→ 0` form.
-/

section RePublish

variable {Ω U β γ : Type*} [MeasurableSpace Ω]
variable [Fintype U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [MeasurableSpace β]
variable [MeasurableSpace γ]

/-- **Decoder failure bound from covering + discharged packing.** Given a
covering predicate `IsWynerZivBinningCovering R₁ ε₁` for the *good hash*
produced by `wzPacking_isPacking_of_typicality`, and measurability of the
relevant events, the decoder-failure probability is at most `ε₁ + S/M`.

This is the re-published `WynerZivCoveringBody`-style decoder bound, now with
the packing side fully discharged (no `IsWynerZivBinningPacking` pass-through
remaining — it is *produced* internally from `IsPackingTypicalityHyp`).

Phase 2.x ripple note: this declaration depends transitively on
`wyner_ziv_binning_via_covering_packing`, whose body is now `sorry`
(`@residual(plan:wyner-ziv-discharge-moonshot-plan)`). No `@residual` tag
is attached here — the closure responsibility belongs to the upstream
declaration's `@residual` tag, and Lean's type-check transitively tracks
the dependency. -/
theorem wyner_ziv_packing_decoder_fail
    [Nonempty β] [Nonempty γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n M : ℕ} [NeZero M] {S R₁ R₂ ε₁ : ℝ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop)
    (f : U × β → γ)
    (hS_nn : 0 ≤ S)
    (h_slice : IsPackingTypicalityHyp (n := n) S JT)
    (h_meas_bin_all : ∀ f_U : (Fin n → U) → Fin M,
      IsPackingCollisionBoundHyp (n := n) Us Ys JT f_U)
    (h_meas_typ : MeasurableSet (wzError_E_typ (n := n) Us Ys JT))
    (h_cov : ∀ _f_U : (Fin n → U) → Fin M,
      IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT)
    (h_meas_fail : ∀ f_U : (Fin n → U) → Fin M,
      MeasurableSet { ω : Ω |
        wzJointlyTypicalDecoderBody f_U JT f (f_U (Us ω), Ys ω)
          ≠ fun i => f (Us ω i, Ys ω i) }) :
    ∃ f_U : (Fin n → U) → Fin M,
      μ.real { ω : Ω |
          wzJointlyTypicalDecoderBody f_U JT f (f_U (Us ω), Ys ω)
            ≠ fun i => f (Us ω i, Ys ω i) }
        ≤ ε₁ + S * ((M : ℝ))⁻¹ := by
  -- Discharge packing for a single good hash.
  obtain ⟨f_U, h_pack⟩ :=
    wzPacking_isPacking_of_typicality (R₂ := R₂) μ Us Ys JT hS_nn h_slice h_meas_bin_all
  refine ⟨f_U, ?_⟩
  -- Combine with covering via the wave7 composition theorem.
  exact wyner_ziv_binning_via_covering_packing
    (R₁ := R₁) (R₂ := R₂) (ε₁ := ε₁) (ε₂ := S * ((M : ℝ))⁻¹)
    μ Us Ys JT f_U f h_meas_typ (h_meas_bin_all f_U) (h_meas_fail f_U)
    (h_cov f_U) h_pack

/-- **Asymptotic decoder failure → 0 from covering + discharged packing.**
Given an existence-form hypothesis bundle (at every `ε > 0`, eventually in
`n` the combined tolerance `ε₁ + S/M ≤ ε`, the slice cardinality bound
`IsPackingTypicalityHyp S`, the covering predicate at `ε₁`, and the
measurability data all hold), there is — at every such `n` — a single good
hash whose decoder failure probability is `≤ ε`.

The packing predicate is *not* an input: it is discharged internally from
`IsPackingTypicalityHyp` via the first moment method. This is the
existence-pattern consumed downstream by `wyner_ziv_achievability_existence`,
now with the packing side fully discharged.

Phase 1.5 (sorry-migration): body retreated to `sorry`. The hypothesis
bundle `h_asymp` is a load-bearing existence form combining
`IsPackingTypicalityHyp` (slice cardinality) +
`IsPackingCollisionBoundHyp` (measurability) + a covering predicate
family + measurability data. The previous body destructured `h_asymp` and
called `wyner_ziv_packing_decoder_fail`, which itself depends on the
upstream sorry-migrated `wyner_ziv_binning_via_covering_packing`. Closure
responsibility is parked on the discharge plan.

`@residual(plan:wyner-ziv-discharge-moonshot-plan)` -/
theorem wyner_ziv_packing_existence
    [Nonempty β] [Nonempty γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R₁ R₂ : ℝ}
    (JT : ∀ n : ℕ, (Fin n → U) × (Fin n → β) → Prop)
    (h_asymp :
      ∀ ε > (0 : ℝ),
        ∃ N : ℕ, ∀ n ≥ N,
          ∃ (M : ℕ) (_ : NeZero M)
            (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
            (f : U × β → γ) (S ε₁ : ℝ),
            ε₁ + S * ((M : ℝ))⁻¹ ≤ ε
              ∧ 0 ≤ S
              ∧ IsPackingTypicalityHyp (n := n) S (JT n)
              ∧ (∀ f_U : (Fin n → U) → Fin M,
                  IsPackingCollisionBoundHyp (n := n) Us Ys (JT n) f_U)
              ∧ MeasurableSet (wzError_E_typ (n := n) Us Ys (JT n))
              ∧ (∀ _f_U : (Fin n → U) → Fin M,
                  IsWynerZivBinningCovering R₁ ε₁ μ Us Ys (JT n))
              ∧ (∀ f_U : (Fin n → U) → Fin M,
                  MeasurableSet { ω : Ω |
                    wzJointlyTypicalDecoderBody f_U (JT n) f (f_U (Us ω), Ys ω)
                      ≠ fun i => f (Us ω i, Ys ω i) })) :
    ∀ ε > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M : ℕ)
          (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
          (f : U × β → γ) (f_U : (Fin n → U) → Fin M),
          μ.real { ω : Ω |
              wzJointlyTypicalDecoderBody f_U (JT n) f (f_U (Us ω), Ys ω)
                ≠ fun i => f (Us ω i, Ys ω i) }
            ≤ ε := by
  sorry

end RePublish

end InformationTheory.Shannon
