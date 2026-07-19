import InformationTheory.Shannon.WynerZiv.Operational
import InformationTheory.Shannon.WynerZiv.FactorizableRate
import InformationTheory.Shannon.WynerZiv.ConverseGateway
import InformationTheory.Shannon.ChannelCoding.ConverseMemorylessMarkov
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fin.Embedding

/-!
# Wyner–Ziv converse — preliminaries (n-letter bound, pmf→measure, append Markov)

Preliminaries for the operational lower bound on the Wyner–Ziv rate: the `n`-letter
single-letterized converse, the non-degeneracy (data-processing lower bound) of the reshaped
operational rate, the local finite pmf → measure realization feeding the DPI gateway, and the
append form of `IsMarkovChain` (target appended by a conditioner-only kernel).
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
  [Fintype U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]

/-! ## `n`-letter single-letterized converse -/

/-- For a `Fin M`-valued encoder output `Jn`, a finite source block `Xn`, and any
side-information block `Yn`, the mutual-information difference is bounded by the
log-cardinality rate: `(I(Jn; Xn) − I(Jn; Yn)).toReal ≤ log M`.

Since `I(Jn; Yn) ≥ 0`, the truncated difference is `≤ I(Jn; Xn)`, and
`I(Jn; Xn).toReal = H(Jn) − H(Jn | Xn) ≤ H(Jn) ≤ log |Fin M| = log M`
(`entropy_le_log_card` + `condEntropy_nonneg`). This is the WZ analogue of the
rate-distortion `mutualInfo_block_le_log_card`. -/
lemma mutualInfo_diff_le_log_card
    {Ω : Type*} [MeasurableSpace Ω]
    {A B : Type*}
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B]
    {M : ℕ} [NeZero M]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Jn : Ω → Fin M) (Xn : Ω → A) (Yn : Ω → B)
    (hJn : Measurable Jn) (hXn : Measurable Xn) :
    (mutualInfo μ Jn Xn - mutualInfo μ Jn Yn).toReal ≤ Real.log (M : ℝ) := by
  have hA_ne : mutualInfo μ Jn Xn ≠ ∞ := mutualInfo_ne_top μ Jn Xn hJn hXn
  have h_diff_le :
      (mutualInfo μ Jn Xn - mutualInfo μ Jn Yn).toReal ≤ (mutualInfo μ Jn Xn).toReal :=
    ENNReal.toReal_mono hA_ne tsub_le_self
  have h_A_le : (mutualInfo μ Jn Xn).toReal ≤ Real.log (M : ℝ) := by
    rw [mutualInfo_eq_entropy_sub_condEntropy μ Jn Xn hJn hXn]
    have h_ent : entropy μ Jn ≤ Real.log (Fintype.card (Fin M)) :=
      InformationTheory.Shannon.MaxEntropy.entropy_le_log_card μ Jn hJn
    have h_ce : 0 ≤ InformationTheory.MeasureFano.condEntropy μ Jn Xn :=
      condEntropy_nonneg μ Jn Xn
    rw [Fintype.card_fin] at h_ent
    linarith
  exact le_trans h_diff_le h_A_le

/-! ## Reshaped operational rate: non-degeneracy (data-processing lower bound)

The reshaped rate `wynerZivRate` (`FactorizableRate.lean` §10) is
`sInf (wzRateValueSet …)`. Its honest non-degeneracy rests on the objective's
data-processing non-negativity `I(X;U) − I(Y;U) ≥ 0` on the factorizable
manifold (Markov chain `U − X − Y`), which discharges the `BddBelow` guard that
prevents a junk `sInf` collapse to `≤ 0`. -/

/-- The source pmf `fun p ↦ P_XY.real {p}` of a probability measure lies in the
standard simplex.
@audit:ok -/
lemma measureReal_pmf_mem_stdSimplex
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY] :
    (fun p ↦ P_XY.real {p}) ∈ stdSimplex ℝ (α × β) := by
  refine ⟨fun p ↦ measureReal_nonneg, ?_⟩
  have h1 : (∑ p : α × β, P_XY.real {p}) = P_XY.real (Finset.univ : Finset (α × β)) := by
    simp [sum_measureReal_singleton]
  rw [h1, Finset.coe_univ]
  exact probReal_univ

/-! ### Local finite pmf → measure realization (for the DPI gateway)

`wzPmfMeasure p = ∑ t, ENNReal.ofReal (p t) • δ_t` realizes a finite pmf vector as
a measure; on `stdSimplex` members it is a probability measure with
`.real {t} = p t`. Mirrors `ChannelCoding.pmfToMeasure` (kept local to avoid a heavy
`ShannonTheorem` import). -/

/-- Realize a finite pmf vector `p : T → ℝ` as `∑ t, ENNReal.ofReal (p t) • δ_t`.
Mass `1` comes from the `stdSimplex` sum `∑ p t = 1`, and `μ.real {t} = p t` via
`ENNReal.toReal_ofReal` off the simplex nonnegativity.
@audit:ok -/
private noncomputable def wzPmfMeasure {T : Type*} [Fintype T] [MeasurableSpace T]
    (p : T → ℝ) : Measure T :=
  ∑ t : T, ENNReal.ofReal (p t) • Measure.dirac t

private lemma wzPmfMeasure_apply_singleton {T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] (p : T → ℝ) (t : T) :
    (wzPmfMeasure p) ({t} : Set T) = ENNReal.ofReal (p t) := by
  unfold wzPmfMeasure
  rw [Measure.finsetSum_apply Finset.univ _ {t}]
  rw [Finset.sum_eq_single t]
  · simp [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.singleton t)]
  · intro b _ hb
    simp [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.singleton t),
      Set.indicator_of_notMem
        (show b ∉ ({t} : Set T) by simp only [Set.mem_singleton_iff]; exact hb)]
  · intro h
    exact (h (Finset.mem_univ t)).elim

private lemma wzPmfMeasure_isProbabilityMeasure {T : Type*} [Fintype T] [MeasurableSpace T]
    {p : T → ℝ} (hp : p ∈ stdSimplex ℝ T) : IsProbabilityMeasure (wzPmfMeasure p) := by
  refine ⟨?_⟩
  unfold wzPmfMeasure
  rw [Measure.finsetSum_apply Finset.univ _ Set.univ]
  have h_each : ∀ t ∈ (Finset.univ : Finset T),
      (ENNReal.ofReal (p t) • Measure.dirac t) (Set.univ : Set T) = ENNReal.ofReal (p t) := by
    intro t _; simp [Measure.smul_apply]
  rw [Finset.sum_congr rfl h_each]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ ↦ hp.1 t), hp.2, ENNReal.ofReal_one]

private lemma wzPmfMeasure_real_singleton {T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] {p : T → ℝ} (hp : p ∈ stdSimplex ℝ T) (t : T) :
    (wzPmfMeasure p).real {t} = p t := by
  unfold Measure.real
  rw [wzPmfMeasure_apply_singleton]
  exact ENNReal.toReal_ofReal (hp.1 t)

/-! ### Append form of `IsMarkovChain` (target appended by a conditioner-only kernel)

If the target `Bs` is generated from the conditioner `Zc` by a Markov kernel `Q`
ignoring `As`, then `As → Zc → Bs`. General utilities re-derived locally (the
`BroadcastChannel` originals are `private`). The append identity `h_app` reduces the
Markov chain to `IsMarkovChain` via `condDistrib` uniqueness.
@audit:ok -/

private lemma wzKernel_compProd_prodMkRight_eq_prod
    {Z' A' B' : Type*} [MeasurableSpace Z'] [MeasurableSpace A'] [MeasurableSpace B']
    (κ : Kernel Z' A') [IsSFiniteKernel κ] (Q : Kernel Z' B') [IsSFiniteKernel Q] :
    κ ⊗ₖ Kernel.prodMkRight A' Q = κ ×ₖ Q := by
  rw [Kernel.ext_fun_iff]
  intro z f hf
  rw [Kernel.lintegral_compProd _ _ _ hf, Kernel.lintegral_prod _ _ _ hf]
  rfl

lemma wzIsMarkovChain_of_append
    {Ω' A' Z' B' : Type*}
    [MeasurableSpace Ω'] [MeasurableSpace A'] [MeasurableSpace Z'] [MeasurableSpace B']
    [StandardBorelSpace A'] [Nonempty A']
    [StandardBorelSpace B'] [Nonempty B']
    (μ : Measure Ω') [IsProbabilityMeasure μ]
    (As : Ω' → A') (Zc : Ω' → Z') (Bs : Ω' → B')
    (hAs : Measurable As) (hZc : Measurable Zc) (hBs : Measurable Bs)
    (Q : Kernel Z' B') [IsMarkovKernel Q]
    (h_app : μ.map (fun ω ↦ ((Zc ω, As ω), Bs ω))
           = (μ.map (fun ω ↦ (Zc ω, As ω))) ⊗ₘ (Kernel.prodMkRight A' Q)) :
    IsMarkovChain μ As Zc Bs := by
  haveI : IsProbabilityMeasure (μ.map Zc) := Measure.isProbabilityMeasure_map hZc.aemeasurable
  have hZcAs : Measurable (fun ω ↦ (Zc ω, As ω)) := hZc.prodMk hAs
  have hg : Measurable (fun p : (Z' × A') × B' ↦ (p.1.1, p.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hmarg : μ.map (fun ω ↦ (Zc ω, Bs ω)) = (μ.map Zc) ⊗ₘ Q := by
    have e1 : μ.map (fun ω ↦ (Zc ω, Bs ω))
        = (μ.map (fun ω ↦ ((Zc ω, As ω), Bs ω))).map (fun p : (Z' × A') × B' ↦ (p.1.1, p.2)) := by
      rw [Measure.map_map hg (hZcAs.prodMk hBs)]; rfl
    rw [e1, h_app]
    refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
    have hF : Measurable (fun z ↦ ∫⁻ b, f (z, b) ∂(Q z)) :=
      hf.lintegral_kernel_prod_right'
    have hF2 : Measurable (fun a : (Z' × A') × B' ↦ f (a.1.1, a.2)) := hf.comp hg
    rw [lintegral_map hf hg, Measure.lintegral_compProd hF2,
        Measure.lintegral_compProd hf]
    have hfst : μ.map Zc = (μ.map (fun ω ↦ (Zc ω, As ω))).map Prod.fst := by
      rw [Measure.map_map measurable_fst hZcAs]; rfl
    rw [hfst, lintegral_map hF measurable_fst]
    rfl
  have hcd_B : condDistrib Bs Zc μ =ᵐ[μ.map Zc] Q :=
    condDistrib_ae_eq_of_measure_eq_compProd Zc hBs.aemeasurable hmarg
  unfold IsMarkovChain
  have hLHS : μ.map (fun ω ↦ (Zc ω, As ω, Bs ω))
      = (μ.map (fun ω ↦ ((Zc ω, As ω), Bs ω))).map MeasurableEquiv.prodAssoc := by
    rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable (hZcAs.prodMk hBs)]; rfl
  rw [hLHS, h_app, ← compProd_map_condDistrib hAs.aemeasurable, Measure.compProd_assoc']
  refine Measure.compProd_congr ?_
  rw [wzKernel_compProd_prodMkRight_eq_prod]
  filter_upwards [hcd_B] with z hz
  rw [Kernel.prod_apply, Kernel.prod_apply, hz]

/-- Markov chain `Y − X − U` on the factorizable manifold. For a factorizable
joint `q(x,y,u) = κ(u|x)·P_XY(x,y)`, realized as the discrete measure
`wzPmfMeasure q` on `α × β × V`, the coordinates satisfy the Markov chain
`Y → X → U`: `U` is appended to `(X, Y)` by the conditioner-only kernel `κ`,
so `U` is conditionally independent of `Y` given `X`. This is the measure-form
content that the data-processing inequality `mutualInfo_le_of_markov` consumes.

The `U`-given-`X` kernel `Q x = κ(·|x)` is built discretely; `wzIsMarkovChain_of_append`
reduces the Markov chain to the append identity `h_app`
`μ.map ((X,Y),U) = (μ.map (X,Y)) ⊗ₘ (prodMkRight β Q)`, discharged as a
finite-support measure identity on singletons (`compProd_apply` + the dirac-sum
lintegral + the auxiliary marginalization `∑_u q(x,y,u) = P_XY(x,y)`).
@audit:ok (the append identity `h_app` genuinely consumes the factorization `hκeq`
`q = κ(u|x)·P_XY`; an arbitrary non-factorizable `q` would break it, so the chain is
in the exact orientation `mutualInfo_le_of_markov` needs, not vacuous.) -/
lemma wzFactorizable_isMarkovChain
    {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] [Nonempty V]
    {P_XY : α × β → ℝ} (h_pmf : P_XY ∈ stdSimplex ℝ (α × β))
    {q : α × β × V → ℝ} (hq : IsWynerZivFactorizable V P_XY q)
    (μ : Measure (α × β × V)) [IsProbabilityMeasure μ] (hμ : μ = wzPmfMeasure q) :
    IsMarkovChain μ
      (fun ω : α × β × V ↦ ω.2.1) (fun ω ↦ ω.1) (fun ω ↦ ω.2.2) := by
  obtain ⟨κ, hκnn, hκsum, hκeq⟩ := hq
  -- The `U`-given-`X` Markov kernel `Q x = κ(·|x)`, realized discretely.
  let Q : Kernel α V := ⟨fun x ↦ wzPmfMeasure (κ x), measurable_of_countable _⟩
  have hQ_apply : ∀ x : α, Q x = wzPmfMeasure (κ x) := fun x ↦ rfl
  haveI hQ_markov : IsMarkovKernel Q :=
    ⟨fun x ↦ wzPmfMeasure_isProbabilityMeasure ⟨fun u ↦ hκnn x u, hκsum x⟩⟩
  -- `U` is appended to `(X, Y)` by the conditioner-only kernel `Q`.
  have hproj : Measurable (fun ω : α × β × V ↦ (ω.1, ω.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  -- Marginalization over the auxiliary: `∑_u q(x,y,u) = P_XY(x,y)`.
  have hmarg : ∀ (x : α) (y : β),
      (∑ c : V, ENNReal.ofReal (q (x, y, c))) = ENNReal.ofReal (P_XY (x, y)) := by
    intro x y
    calc (∑ c : V, ENNReal.ofReal (q (x, y, c)))
        = ∑ c : V, ENNReal.ofReal (κ x c * P_XY (x, y)) := by simp_rw [hκeq]
      _ = ENNReal.ofReal (∑ c : V, κ x c * P_XY (x, y)) := by
          rw [ENNReal.ofReal_sum_of_nonneg
            (fun c _ ↦ mul_nonneg (hκnn x c) (h_pmf.1 (x, y)))]
      _ = ENNReal.ofReal (P_XY (x, y)) := by
          rw [← Finset.sum_mul, hκsum x, one_mul]
  -- `μ` over `(X, Y)` is the source pmf.
  have hν : μ.map (fun ω : α × β × V ↦ (ω.1, ω.2.1)) = wzPmfMeasure P_XY := by
    refine Measure.ext_of_singleton fun s ↦ ?_
    obtain ⟨x, y⟩ := s
    rw [Measure.map_apply hproj (measurableSet_singleton _), wzPmfMeasure_apply_singleton]
    have hfib : (fun ω : α × β × V ↦ (ω.1, ω.2.1)) ⁻¹' {(x, y)}
        = ⋃ c ∈ (Finset.univ : Finset V), ({(x, y, c)} : Set (α × β × V)) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Finset.mem_univ,
        exists_true_left, Prod.ext_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨ω.2.2, h1, h2, rfl⟩
      · rintro ⟨c, h1, h2, _⟩; exact ⟨h1, h2⟩
    rw [hμ, hfib,
        measure_biUnion_finset
          (fun a _ b _ hab ↦ by
            simp only [Function.onFun, Set.disjoint_singleton, ne_eq, Prod.mk.injEq]
            tauto)
          (fun c _ ↦ measurableSet_singleton _)]
    simp_rw [wzPmfMeasure_apply_singleton]
    exact hmarg x y
  -- `U` appended by the conditioner-only kernel `Q`: the append identity on singletons.
  have h_app : μ.map (fun ω : α × β × V ↦ ((ω.1, ω.2.1), ω.2.2))
      = (μ.map (fun ω ↦ (ω.1, ω.2.1))) ⊗ₘ (Kernel.prodMkRight β Q) := by
    refine Measure.ext_of_singleton fun s ↦ ?_
    obtain ⟨⟨x, y⟩, u⟩ := s
    have hg : Measurable (fun ω : α × β × V ↦ ((ω.1, ω.2.1), ω.2.2)) :=
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)
    have hLHS : (μ.map (fun ω : α × β × V ↦ ((ω.1, ω.2.1), ω.2.2))) {((x, y), u)}
        = ENNReal.ofReal (q (x, y, u)) := by
      rw [Measure.map_apply hg (measurableSet_singleton _)]
      have hpre : (fun ω : α × β × V ↦ ((ω.1, ω.2.1), ω.2.2)) ⁻¹' {((x, y), u)}
          = {(x, y, u)} := by
        ext ω; simp [Prod.ext_iff, and_assoc]
      rw [hpre, hμ, wzPmfMeasure_apply_singleton]
    have hRHS : ((μ.map (fun ω : α × β × V ↦ (ω.1, ω.2.1))) ⊗ₘ
          (Kernel.prodMkRight β Q)) {((x, y), u)}
        = ENNReal.ofReal (q (x, y, u)) := by
      haveI : IsProbabilityMeasure (wzPmfMeasure P_XY) :=
        wzPmfMeasure_isProbabilityMeasure h_pmf
      rw [hν, Measure.compProd_apply (measurableSet_singleton _)]
      unfold wzPmfMeasure
      rw [lintegral_finsetSum_measure]
      simp_rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
      rw [Finset.sum_eq_single (x, y)]
      · rw [Kernel.prodMkRight_apply']
        have hpre : Prod.mk (x, y) ⁻¹' ({((x, y), u)} : Set ((α × β) × V)) = {u} := by
          ext v; simp [Prod.ext_iff]
        rw [hpre, hQ_apply, wzPmfMeasure_apply_singleton, hκeq x y u,
          ENNReal.ofReal_mul (hκnn x u)]
        ring
      · intro ab _ hab
        rw [Kernel.prodMkRight_apply']
        have hpre : Prod.mk ab ⁻¹' ({((x, y), u)} : Set ((α × β) × V)) = ∅ := by
          ext v
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
            Prod.mk.injEq, not_and]
          intro h; exact absurd h hab
        rw [hpre, measure_empty, mul_zero]
      · intro h; exact absurd (Finset.mem_univ (x, y)) h
    rw [hLHS, hRHS]
  exact wzIsMarkovChain_of_append μ (fun ω ↦ ω.2.1) (fun ω ↦ ω.1) (fun ω ↦ ω.2.2)
    (measurable_fst.comp measurable_snd) measurable_fst (measurable_snd.comp measurable_snd)
    Q h_app

/-- Data-processing non-negativity of the Wyner–Ziv objective. On the
factorizable manifold the auxiliary `U` sits atop the Markov chain `U − X − Y`
(`IsWynerZivFactorizable_markov`), so the data-processing inequality gives
`I(Y;U) ≤ I(X;U)`, i.e. the objective `I(X;U) − I(Y;U)` is non-negative. This is
the uniform (in the auxiliary alphabet size) lower bound `0` that makes the
reshaped rate `wynerZivRate` non-degenerate.

`h_pmf` (the source is a genuine pmf) is a regularity precondition: it makes the
factorizable joint `q` a pmf realizable as a probability measure. `Nonempty V`
holds automatically at every non-empty-constraint index (row-stochasticity of the
kernel forces `V` non-empty).

The proof realizes `q` as the discrete measure `μ = wzPmfMeasure q` on `α × β × V`
with coordinate projections; the objective is landed onto
`(mutualInfo μ X U).toReal − (mutualInfo μ Y U).toReal` via the pmf↔measure
bridges `wzMutualInfoXU_eq_mutualInfo` / `wzMutualInfoYU_eq_mutualInfo`; the
measure-form data-processing inequality `mutualInfo_le_of_markov` is applied with
the Markov chain `Y − X − U` (`wzFactorizable_isMarkovChain`) read off the
factorization `q = κ(u|x)·P_XY`, and `ENNReal.toReal_mono` finishes.
@audit:ok (`hq` is the domain constraint defining the factorizable manifold — it
supplies the Markov structure, not the conclusion. Sufficiency: dropping `hq` makes
the claim false (a `q` with `U` depending on `Y` gives `I(Y;U) > I(X;U)`), so it is
necessary, not under-hypothesized; `h_pmf` / `Nonempty V` are regularity preconditions.) -/
theorem wzObjective_nonneg_of_factorizable
    {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] [Nonempty V]
    {P_XY : α × β → ℝ} (h_pmf : P_XY ∈ stdSimplex ℝ (α × β))
    {q : α × β × V → ℝ}
    (hq : IsWynerZivFactorizable V P_XY q) :
    0 ≤ wzMutualInfoXU V q - wzMutualInfoYU V q := by
  classical
  haveI hμ_prob : IsProbabilityMeasure (wzPmfMeasure q) :=
    wzPmfMeasure_isProbabilityMeasure (IsWynerZivFactorizable_mem_stdSimplex V h_pmf hq)
  set μ := wzPmfMeasure q with hμ
  have hX : Measurable (fun ω : α × β × V ↦ ω.1) := measurable_fst
  have hY : Measurable (fun ω : α × β × V ↦ ω.2.1) := measurable_fst.comp measurable_snd
  have hU : Measurable (fun ω : α × β × V ↦ ω.2.2) := measurable_snd.comp measurable_snd
  -- The coordinate map `(X, Y, U)` is the identity on `α × β × V`, so the empirical
  -- pmf `p ↦ (μ.map (X,Y,U)).real {p}` induced by `μ` is `q` itself.
  have hpmf_eq :
      (fun p ↦ (μ.map (fun ω : α × β × V ↦ (ω.1, ω.2.1, ω.2.2))).real {p}) = q := by
    have hid : (fun ω : α × β × V ↦ (ω.1, ω.2.1, ω.2.2)) = id := rfl
    rw [hid, Measure.map_id]
    funext p
    rw [hμ]
    exact wzPmfMeasure_real_singleton (IsWynerZivFactorizable_mem_stdSimplex V h_pmf hq) p
  -- Land the pmf-form objective onto the measure form via the proved bridges.
  have hXU : wzMutualInfoXU V q
      = (mutualInfo μ (fun ω : α × β × V ↦ ω.1) (fun ω ↦ ω.2.2)).toReal := by
    rw [← hpmf_eq]
    exact wzMutualInfoXU_eq_mutualInfo μ (fun ω ↦ ω.1) (fun ω ↦ ω.2.1) (fun ω ↦ ω.2.2) hX hY hU
  have hYU : wzMutualInfoYU V q
      = (mutualInfo μ (fun ω : α × β × V ↦ ω.2.1) (fun ω ↦ ω.2.2)).toReal := by
    rw [← hpmf_eq]
    exact wzMutualInfoYU_eq_mutualInfo μ (fun ω ↦ ω.1) (fun ω ↦ ω.2.1) (fun ω ↦ ω.2.2) hX hY hU
  -- Markov chain `Y − X − U` off the factorization ⟹ data-processing `I(Y;U) ≤ I(X;U)`.
  have hmarkov : IsMarkovChain μ (fun ω : α × β × V ↦ ω.2.1) (fun ω ↦ ω.1) (fun ω ↦ ω.2.2) :=
    wzFactorizable_isMarkovChain h_pmf hq μ hμ
  have hdpi : mutualInfo μ (fun ω : α × β × V ↦ ω.2.1) (fun ω ↦ ω.2.2)
      ≤ mutualInfo μ (fun ω ↦ ω.1) (fun ω ↦ ω.2.2) :=
    mutualInfo_le_of_markov μ (fun ω ↦ ω.2.1) (fun ω ↦ ω.1) (fun ω ↦ ω.2.2) hY hX hU hmarkov
  have hne : mutualInfo μ (fun ω : α × β × V ↦ ω.1) (fun ω ↦ ω.2.2) ≠ ⊤ :=
    mutualInfo_ne_top μ (fun ω ↦ ω.1) (fun ω ↦ ω.2.2) hX hU
  have hmono : (mutualInfo μ (fun ω : α × β × V ↦ ω.2.1) (fun ω ↦ ω.2.2)).toReal
      ≤ (mutualInfo μ (fun ω ↦ ω.1) (fun ω ↦ ω.2.2)).toReal :=
    ENNReal.toReal_mono hne hdpi
  rw [hXU, hYU]
  linarith

/-- The reshaped value set `wzRateValueSet` is bounded below by `0` when the
source is a pmf. This discharges the `BddBelow` guard of the reshaped rate,
certifying non-degeneracy: every objective value is `≥ 0` by the data-processing
non-negativity `wzObjective_nonneg_of_factorizable`, so the `sInf` cannot
collapse to a junk `≤ 0`.

@audit:ok (the `k = 0` `exfalso` (row-stochasticity `∑_{Fin 0} κ = 0 ≠ 1`) is a
genuine impossibility argument, not a vacuous-truth shortcut; the `BddBelow` guard
rests on the DPI input `wzObjective_nonneg_of_factorizable`.) -/
theorem wzRateValueSet_bddBelow_of_pmf
    {P_XY : α × β → ℝ} (h_pmf : P_XY ∈ stdSimplex ℝ (α × β))
    (d : α → γ → ℝ) (D : ℝ) :
    BddBelow (wzRateValueSet P_XY d D) := by
  refine ⟨0, ?_⟩
  rintro v hv
  rw [mem_wzRateValueSet_iff] at hv
  obtain ⟨k, qf, hqf, rfl⟩ := hv
  have hfact : IsWynerZivFactorizable (Fin k) P_XY qf.1 := hqf.1
  haveI : Nonempty (Fin k) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exfalso
      subst hk
      obtain ⟨κ, _, hκsum, _⟩ := hfact
      obtain ⟨x⟩ := (inferInstance : Nonempty α)
      have hsum := hκsum x
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
      exact absurd hsum (by norm_num)
    · exact ⟨⟨0, hk⟩⟩
  exact wzObjective_nonneg_of_factorizable h_pmf hfact

end InformationTheory.Shannon
