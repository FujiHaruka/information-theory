import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.KLCapacityAndAEP
import InformationTheory.Shannon.AWGN.PerCodewordPowerConstraint
import InformationTheory.Shannon.AWGN.ConverseMIChainRule
import InformationTheory.Shannon.Converse
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.ChannelCoding.Basic
import InformationTheory.Shannon.ChannelCoding.MIDecomp
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import InformationTheory.Shannon.MultivariateDiffEntropy

/-! # AWGN channel-coding converse — mutual-information finiteness and chain

Builds the mutual-information layer of the AWGN channel-coding converse (Cover–Thomas, 9.1.2):
the canonical joint law of `(W, Yⁿ)`, Fano's inequality dispatch, the block-mixture output
density used to bound `I(W; Yⁿ)`, the finiteness of `I(W; Yⁿ)` and `I(Xⁿ; Yⁿ)` via the
discrete-input `compProd` chain rule, the data-processing inequality, and the
mutual-information chain rule `I(Xⁿ; Yⁿ) ≤ ∑ᵢ I(Xᵢ; Yᵢ)`.

## Main definitions

* `awgnConverseJoint` — the canonical joint law of `(W, Yⁿ)` under a uniform message `W`
  and the memoryless AWGN channel, as the mixture `(1/M) ∑ₘ δ_m ⊗ ∏ᵢ AWGN_{encoder m i}`.
* `perLetterYLaw` — the per-coordinate output marginal of `Yᵢ`, a mixture of Gaussians.
* `perLetterMI` / `jointMIWYn` / `jointMIXnYn` — the per-letter and joint mutual
  informations `I(Xᵢ; Yᵢ)`, `I(W; Yⁿ)`, `I(Xⁿ; Yⁿ)` on the canonical joint.

## Main statements

* `awgn_converse_single_shot_call` — Fano dispatch yielding
  `log M ≤ I(W; Yⁿ) + binEntropy(Pe) + Pe · log(M − 1)`.
* `awgn_dpi` — `I(W; Yⁿ) ≤ I(Xⁿ; Yⁿ)` from the Markov chain `W → Xⁿ → Yⁿ`.
* `awgn_chain_rule` — `I(Xⁿ; Yⁿ) ≤ ∑ᵢ I(Xᵢ; Yᵢ)` for the memoryless channel.
* `awgnConverseJoint_mutualInfo_ne_top_via_chain` — `I(W; Yⁿ) ≠ ∞ ∧ I(Xⁿ; Yⁿ) ≠ ∞`.

## Implementation notes

* The mutual informations are stated through the single canonical joint `awgnConverseJoint`
  so that data-processing and chain-rule lemmas apply directly. Finiteness of `I(W; Yⁿ)`
  and `I(Xⁿ; Yⁿ)` is obtained from `klDiv_ne_top` (absolute continuity plus integrable
  log-likelihood ratio), constructed directly to avoid the circularity of a Real-form chain
  rule, since `W` is discrete and `Xⁿ` is finite-valued. -/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
  InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

/-! ## Local quantities: joint law, output marginals, mutual informations -/

/-- Canonical joint law of `(W, Yⁿ)` under a uniform message and the AWGN channel.

On the sample space `Ω := Fin M × (Fin n → ℝ)` with `W = Prod.fst` and `Yⁿ = Prod.snd`,
under uniform `W ∼ Uniform(Fin M)` and conditional `Yⁿ | W = m ∼ ∏ᵢ N(c.encoder m i, N)`,
the joint law is the mixture `(1/M) ∑ₘ δ_m ⊗ ∏ᵢ AWGN_{c.encoder m i}`. -/
noncomputable def awgnConverseJoint
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) :
    Measure (Fin M × (Fin n → ℝ)) :=
  ((Fintype.card (Fin M) : ℝ≥0∞)⁻¹) •
    ∑ m : Fin M,
      (Measure.dirac m).prod
        (Measure.pi (fun i : Fin n ↦ awgnChannel N h_meas (c.encoder m i)))

/-- `awgnConverseJoint` is a probability measure when `M ≥ 1` (`[NeZero M]`):
the mixture has weights `(1/M)` summing to `1`. -/
instance awgnConverseJoint.instIsProbabilityMeasure
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    IsProbabilityMeasure (awgnConverseJoint h_meas c) := by
  refine ⟨?_⟩
  -- Compute total mass: (1/M) • ∑ m, (dirac m ×ˢ Measure.pi awgn) univ = (1/M) * M = 1
  unfold awgnConverseJoint
  rw [Measure.smul_apply, Measure.finsetSum_apply _ _ Set.univ]
  -- Each summand: (dirac m).prod (Measure.pi awgn) is a probability measure
  have h_summand : ∀ m : Fin M,
      ((Measure.dirac m).prod
          (Measure.pi (fun i : Fin n ↦ awgnChannel N h_meas (c.encoder m i))))
            Set.univ = 1 := by
    intro m
    exact measure_univ
  simp only [h_summand, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  -- Goal: (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) = 1
  -- Use ENNReal.inv_mul_cancel with M ≠ 0 and M ≠ ∞
  have hM_ne_zero : (M : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (NeZero.ne M)
  have hM_ne_top : (M : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top M
  exact ENNReal.inv_mul_cancel hM_ne_zero hM_ne_top

/-- Per-letter output marginal of `Yᵢ` under a uniform message: the closed form
`(1/M) ∑ₘ AWGN_{c.encoder m i}`, a mixture of Gaussians. -/
@[entry_point]
noncomputable def perLetterYLaw
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) : Measure ℝ :=
  (awgnConverseJoint h_meas c).map (fun ω ↦ ω.2 i)

/-- per-letter mutual information `I(X_i; Y_i)` on the canonical joint
`awgnConverseJoint c h_meas`, with `X_i ω := c.encoder ω.1 i` and `Y_i ω := ω.2 i`. -/
@[entry_point]
noncomputable def perLetterMI
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) : ℝ≥0∞ :=
  mutualInfo (awgnConverseJoint h_meas c)
    (fun ω ↦ c.encoder ω.1 i) (fun ω ↦ ω.2 i)

/-- Joint MI `I(W; Y^n)` (message vs. channel output block). -/
@[entry_point]
noncomputable def jointMIWYn
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) : ℝ≥0∞ :=
  mutualInfo (awgnConverseJoint h_meas c) Prod.fst Prod.snd

/-- Joint MI `I(X^n; Y^n)` (channel input block vs. channel output block). -/
@[entry_point]
noncomputable def jointMIXnYn
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) : ℝ≥0∞ :=
  mutualInfo (awgnConverseJoint h_meas c) (fun ω ↦ c.encoder ω.1) Prod.snd

/-! ## Sub-bound lemmas

The three analytic sub-bounds (per-letter log-density integrability, the continuous
mutual-information chain rule, and the Markov-chain factorization) live as lemmas in
`InformationTheory/Shannon/AWGN/ConverseMIChainRule.lean` and are invoked here as ordinary
lemma calls. -/

/-! ## Fano dispatch

`awgn_converse_single_shot_call` invokes `shannon_converse_single_shot` with
`X := Fin M`, `Y := Fin n → ℝ`, `decoder := c.decoder`, `μ := awgnConverseJoint c h_meas`,
assembling Fano's inequality, the data-processing postprocessing step, the entropy chain,
and `H(W uniform) = log M`. -/

private lemma count_eq_finset_sum_dirac (α : Type*) [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    (Measure.count : Measure α) = ∑ a : α, Measure.dirac a := by
  -- `Measure.sum_smul_dirac : sum (fun a => μ {a} • dirac a) = μ`
  -- with `μ := count`, `count {a} = 1` ⇒ `sum (fun a => dirac a) = count`.
  -- Then `sum_fintype` converts `sum` to `∑`.
  have h_one : ∀ a : α, (Measure.count : Measure α) {a} = 1 := fun a ↦
    Measure.count_singleton a
  have h_sum : Measure.sum (fun a : α ↦ Measure.dirac a)
      = (Measure.count : Measure α) := by
    have h := Measure.sum_smul_dirac (μ := (Measure.count : Measure α))
    -- Replace each `count {a}` by `1` and `1 • dirac a` by `dirac a`.
    simp_rw [h_one, one_smul] at h
    exact h
  rw [← h_sum, Measure.sum_fintype]

/-- The message marginal `(awgnConverseJoint h_meas c).map Prod.fst` equals
`(Fintype.card (Fin M))⁻¹ • Measure.count`. -/
private lemma awgnConverseJoint_map_fst
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    (awgnConverseJoint h_meas c).map (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
      = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ • Measure.count := by
  unfold awgnConverseJoint
  -- map distributes over smul and over the Finset sum.
  rw [Measure.map_smul]
  have h_map_fst_meas :
      Measurable (Prod.fst : Fin M × (Fin n → ℝ) → Fin M) := measurable_fst
  rw [Measure.map_finset_sum (s := Finset.univ)
      (m := fun m ↦ (Measure.dirac m).prod
        (Measure.pi (fun i : Fin n ↦ awgnChannel N h_meas (c.encoder m i))))
      h_map_fst_meas.aemeasurable]
  -- Each summand: `((dirac m).prod ν_m).map Prod.fst = (ν_m univ) • dirac m = dirac m`.
  have h_each : ∀ m : Fin M,
      ((Measure.dirac m).prod
          (Measure.pi (fun i : Fin n ↦ awgnChannel N h_meas (c.encoder m i)))).map
        (Prod.fst : Fin M × (Fin n → ℝ) → Fin M) = Measure.dirac m := by
    intro m
    -- `Measure.map_fst_prod : (μ.prod ν).map Prod.fst = (ν univ) • μ`
    rw [Measure.map_fst_prod]
    have : Measure.pi (fun i : Fin n ↦ awgnChannel N h_meas (c.encoder m i))
        (Set.univ : Set (Fin n → ℝ)) = 1 := by
      exact measure_univ
    rw [this, one_smul]
  rw [Finset.sum_congr rfl (fun m _ ↦ h_each m)]
  -- Now: (M⁻¹) • ∑ m, dirac m = (M⁻¹) • Measure.count.
  rw [count_eq_finset_sum_dirac]

private lemma awgnConverseJoint_measurable_snd :
    Measurable (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) :=
  measurable_snd

private lemma awgnConverseJoint_measurable_fst :
    Measurable (Prod.fst : Fin M × (Fin n → ℝ) → Fin M) :=
  measurable_fst

/-- The Fano error probability `errorProb (awgnConverseJoint h_meas c) Prod.fst Prod.snd
c.decoder` equals the AWGN average `(1/M) ∑ₘ (errorProbAt … m).toReal`. -/
private lemma awgn_errorProb_eq_fano_errorProb
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    InformationTheory.MeasureFano.errorProb
        (awgnConverseJoint h_meas c)
        (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
        (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ)
        c.decoder
      = (1 / (M : ℝ)) * ∑ m : Fin M,
          (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal := by
  -- The error event for the Fano formulation.
  set S : Set (Fin M × (Fin n → ℝ)) :=
    {ω : Fin M × (Fin n → ℝ) | ω.1 ≠ c.decoder ω.2} with hS_def
  -- `S` is measurable (preimage of `{m} : Set (Fin M)` under decoder ∘ snd, in Boolean).
  -- We avoid relying on `MeasurableSingletonClass (Fin M × ...)` by computing per-fibre.
  -- Step 1: unfold `errorProb` to `μ.real S`.
  show (awgnConverseJoint h_meas c).real S
      = (1 / (M : ℝ)) * ∑ m : Fin M,
          (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal
  -- Step 2: expand `awgnConverseJoint` and use `measureReal_ennreal_smul_apply`.
  unfold awgnConverseJoint
  rw [measureReal_ennreal_smul_apply]
  congr 1
  · -- `((Fintype.card (Fin M))⁻¹ : ℝ≥0∞).toReal = 1 / M`.
    rw [Fintype.card_fin]
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [one_div]
  -- Step 3: distribute `.real` over the Finset sum.
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have h_fin_each : ∀ m : Fin M,
      ((Measure.dirac m).prod
        (Measure.pi (fun i : Fin n ↦ awgnChannel N h_meas (c.encoder m i)))) S ≠ ∞ := by
    intro m
    have :
        ((Measure.dirac m).prod
          (Measure.pi (fun i : Fin n ↦ awgnChannel N h_meas (c.encoder m i)))) Set.univ ≤ 1 := by
      simp [measure_univ]
    exact ne_top_of_le_ne_top (by simp) (measure_mono (Set.subset_univ _) |>.trans this)
  -- Compute the Finset sum: unfold `.real` to `(·).toReal`, distribute.
  unfold Measure.real
  rw [Measure.finsetSum_apply _ _ S]
  rw [ENNReal.toReal_sum (fun m _ ↦ h_fin_each m)]
  refine Finset.sum_congr rfl ?_
  intro m _
  congr 1
  -- Step 4: pointwise: `((dirac m).prod ν_m) S = ν_m (errorEvent m) = errorProbAt m`.
  -- `dirac_prod m : (dirac m).prod ν = map (Prod.mk m) ν`
  rw [Measure.dirac_prod]
  -- `(map (Prod.mk m) ν_m) S = ν_m ((Prod.mk m) ⁻¹' S)`.
  have hS_meas : MeasurableSet S := by
    -- `S = (fun ω => ω.1 = c.decoder ω.2)ᶜ ⊓ univ`. Use `measurableSet_setOf`.
    have h_pred : Measurable (fun ω : Fin M × (Fin n → ℝ) ↦ (ω.1, c.decoder ω.2)) :=
      measurable_fst.prodMk (c.decoder_meas.comp measurable_snd)
    have h_eq_set : MeasurableSet
        {ω : Fin M × (Fin n → ℝ) | ω.1 = c.decoder ω.2} := by
      have h_diag : MeasurableSet {p : Fin M × Fin M | p.1 = p.2} := by
        exact measurableSet_eq_fun measurable_fst measurable_snd
      exact h_pred h_diag
    exact h_eq_set.compl
  rw [Measure.map_apply measurable_prodMk_left hS_meas]
  -- `(Prod.mk m) ⁻¹' {ω | ω.1 ≠ c.decoder ω.2} = {y | m ≠ c.decoder y} = errorEvent m`.
  have h_preimage :
      (Prod.mk m : (Fin n → ℝ) → Fin M × (Fin n → ℝ)) ⁻¹' S
        = c.toCode.errorEvent m := by
    ext y
    simp only [hS_def, Set.mem_preimage, Set.mem_setOf_eq,
      InformationTheory.Shannon.ChannelCoding.Code.mem_errorEvent]
    -- AwgnCode.toCode → Code; decoder same:
    show m ≠ c.decoder y ↔ c.toCode.decoder y ≠ m
    constructor
    · intro h; exact fun h' ↦ h h'.symm
    · intro h; exact fun h' ↦ h h'.symm
  rw [h_preimage]
  -- `errorProbAt c.toCode W m = Measure.pi (W (c.encoder m i)) (errorEvent m)`.
  rfl

/-! ## Block-mixture output density

The `n`-dimensional output density needed for finiteness of `I(W; Yⁿ)` and `I(Xⁿ; Yⁿ)`.
The block output `blockYLaw` is a mixture of `n`-dimensional product Gaussians over the
finitely many codewords, so `|log density|` is dominated by a quadratic envelope centred at
component `m` via a supremum upper bound together with a same-component lower bound
(`blockDensity ≥ M⁻¹ · (density of component m)`). -/

/-- Block output law: the `Prod.snd` marginal `(awgnConverseJoint).map Prod.snd`. -/
private noncomputable def blockYLaw
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) : Measure (Fin n → ℝ) :=
  (awgnConverseJoint h_meas c).map Prod.snd

/-- Real-valued block mixture density `M⁻¹ ∑ₘ ∏ᵢ gaussianPDFReal (encoder m i) N (yᵢ)`. -/
private noncomputable def blockRealDensity
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (y : Fin n → ℝ) : ℝ :=
  (1 / (M : ℝ)) * ∑ m : Fin M, ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)

/-- `blockYLaw = M⁻¹ • ∑ₘ pi (gaussianReal (encoder m i) N)` (closed mixture form). -/
private lemma blockYLaw_eq_mixture
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    blockYLaw h_meas c
      = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ •
          ∑ m : Fin M, Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N) := by
  classical
  unfold blockYLaw awgnConverseJoint
  have h_meas_snd :
      Measurable (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) := measurable_snd
  rw [Measure.map_smul,
    Measure.map_finset_sum (s := Finset.univ)
      (m := fun m ↦ (Measure.dirac m).prod
        (Measure.pi (fun j : Fin n ↦ awgnChannel N h_meas (c.encoder m j))))
      h_meas_snd.aemeasurable]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro m _
  -- `((dirac m).prod ν).map Prod.snd = (dirac m univ) • ν = ν`, then `awgnChannel = gaussianReal`.
  rw [Measure.map_snd_prod, measure_univ, one_smul]
  refine congrArg (Measure.pi) ?_
  funext i
  rw [awgnChannel_apply]

/-- Each block mixture component `pi (gaussianReal (encoder m i) N)` equals
`volume.withDensity (∏ᵢ gaussianPDF (encoder m i) N (·ᵢ))`. -/
private lemma blockComponent_withDensity
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0)
    {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) :
    Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N)
      = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
          (fun y ↦ ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
  have h_each : ∀ i, gaussianReal (c.encoder m i) N
      = (MeasureTheory.volume : Measure ℝ).withDensity (gaussianPDF (c.encoder m i) N) :=
    fun i ↦ gaussianReal_of_var_ne_zero (c.encoder m i) hN
  haveI : ∀ i, SigmaFinite ((MeasureTheory.volume : Measure ℝ).withDensity
      (gaussianPDF (c.encoder m i) N)) := by
    intro i; rw [← h_each i]; infer_instance
  rw [show (fun i : Fin n ↦ gaussianReal (c.encoder m i) N)
        = (fun i ↦ (MeasureTheory.volume : Measure ℝ).withDensity
            (gaussianPDF (c.encoder m i) N)) from funext h_each,
    InformationTheory.Shannon.pi_withDensity_fin (fun _ ↦ (MeasureTheory.volume : Measure ℝ))
      (fun i ↦ measurable_gaussianPDF (c.encoder m i) N), ← volume_pi]

/-- `blockYLaw = volume.withDensity (ofReal ∘ blockRealDensity)`. -/
private lemma blockYLaw_withDensity_real
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    blockYLaw h_meas c
      = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
          (fun y ↦ ENNReal.ofReal (blockRealDensity N c y)) := by
  classical
  rw [blockYLaw_eq_mixture h_meas c]
  -- each component `pi (gaussianReal …) = volume.withDensity (∏ᵢ gaussianPDF …)`
  have h_comp := fun m : Fin M ↦ blockComponent_withDensity hN c m
  -- distribute the finset sum over `withDensity`
  have h_sum : ∀ s : Finset (Fin M),
      (∑ m ∈ s, Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N))
        = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
            (fun y ↦ ∑ m ∈ s, ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert m s hms ih =>
        have h_density_eq :
            (fun y : Fin n → ℝ ↦ ∑ m' ∈ insert m s,
              ∏ i : Fin n, gaussianPDF (c.encoder m' i) N (y i))
              = (fun y : Fin n → ℝ ↦ ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i))
                + (fun y : Fin n → ℝ ↦ ∑ m' ∈ s,
                  ∏ i : Fin n, gaussianPDF (c.encoder m' i) N (y i)) := by
          funext y; simp only [Pi.add_apply]; rw [Finset.sum_insert hms]
        rw [Finset.sum_insert hms, ih, h_comp m, h_density_eq]
        rw [withDensity_add_left
            (μ := (MeasureTheory.volume : Measure (Fin n → ℝ)))
            (f := fun y : Fin n → ℝ ↦ ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i))
            (Finset.measurable_prod _ (fun i _ ↦
              (measurable_gaussianPDF (c.encoder m i) N).comp (measurable_pi_apply i)))
            (fun y : Fin n → ℝ ↦ ∑ m' ∈ s, ∏ i : Fin n, gaussianPDF (c.encoder m' i) N (y i))]
  rw [h_sum Finset.univ]
  have hM_inv_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ := by
    rw [Fintype.card_fin]; simp; exact_mod_cast (NeZero.ne M)
  rw [← withDensity_smul' _ _ hM_inv_ne_top]
  congr 1
  funext y
  -- `M⁻¹ • (∑ₘ ∏ᵢ gaussianPDF) y = ofReal (M⁻¹ · ∑ₘ ∏ᵢ gaussianPDFReal)`
  simp only [Pi.smul_apply, smul_eq_mul, blockRealDensity, Fintype.card_fin]
  rw [ENNReal.ofReal_mul (by positivity)]
  congr 1
  · rw [one_div, ENNReal.ofReal_inv_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)),
      ENNReal.ofReal_natCast]
  · rw [ENNReal.ofReal_sum_of_nonneg
          (fun m _ ↦ Finset.prod_nonneg (fun i _ ↦ gaussianPDFReal_nonneg _ _ _))]
    refine Finset.sum_congr rfl (fun m _ ↦ ?_)
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ gaussianPDFReal_nonneg _ _ _)]
    refine Finset.prod_congr rfl (fun i _ ↦ ?_)
    rw [gaussianPDF]

/-- `blockYLaw ≪ volume`. -/
private lemma blockYLaw_ac_volume
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    blockYLaw h_meas c ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := by
  rw [blockYLaw_withDensity_real hN h_meas c]
  exact MeasureTheory.withDensity_absolutelyContinuous _ _

/-- `blockYLaw` is a probability measure. -/
private instance blockYLaw_isProbabilityMeasure
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    IsProbabilityMeasure (blockYLaw h_meas c) := by
  unfold blockYLaw
  exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

/-- Positivity of `blockRealDensity` (sum of positive products). -/
private lemma blockRealDensity_pos
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (y : Fin n → ℝ) :
    0 < blockRealDensity N c y := by
  classical
  obtain ⟨m₀⟩ : Nonempty (Fin M) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩⟩
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  unfold blockRealDensity
  refine mul_pos (by positivity) ?_
  refine Finset.sum_pos (fun m _ ↦ Finset.prod_pos (fun i _ ↦ gaussianPDFReal_pos _ _ _ hN)) ?_
  exact ⟨m₀, Finset.mem_univ m₀⟩

/-- Measurability of `blockRealDensity`. -/
private lemma blockRealDensity_measurable
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} (c : AwgnCode M n P) :
    Measurable (blockRealDensity N c) := by
  unfold blockRealDensity
  refine measurable_const.mul ?_
  refine Finset.measurable_sum _ (fun m _ ↦ ?_)
  exact Finset.measurable_prod _ (fun i _ ↦
    (measurable_gaussianPDFReal (c.encoder m i) N).comp (measurable_pi_apply i))

/-- Per-component lower bound:
`blockRealDensity y ≥ M⁻¹ · ∏ᵢ gaussianPDFReal (encoder m i) N (yᵢ)`. -/
private lemma blockRealDensity_ge_component
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) (y : Fin n → ℝ) :
    (1 / (M : ℝ)) * ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)
      ≤ blockRealDensity N c y := by
  unfold blockRealDensity
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine Finset.single_le_sum
    (f := fun m ↦ ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i))
    (fun m _ ↦ Finset.prod_nonneg (fun i _ ↦ gaussianPDFReal_nonneg _ _ _))
    (Finset.mem_univ m)

/-- Sup upper bound: `blockRealDensity y ≤ ∏ᵢ (√(2πN))⁻¹` (each Gaussian ≤ its peak). -/
private lemma blockRealDensity_le_sup
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (y : Fin n → ℝ) :
    blockRealDensity N c y ≤ ∏ _i : Fin n, (Real.sqrt (2 * Real.pi * N))⁻¹ := by
  classical
  unfold blockRealDensity
  set Bpeak : ℝ := (Real.sqrt (2 * Real.pi * N))⁻¹ with hBpeak
  have hBpeak_nonneg : (0 : ℝ) ≤ Bpeak := by rw [hBpeak]; positivity
  -- each coordinate Gaussian `gaussianPDFReal a N (y i) ≤ Bpeak`
  have h_comp_le : ∀ (a x : ℝ), gaussianPDFReal a N x ≤ Bpeak := by
    intro a x
    rw [gaussianPDFReal, hBpeak]
    have h_exp_le_one : Real.exp (-(x - a) ^ 2 / (2 * N)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div]
      have : 0 ≤ (x - a) ^ 2 / (2 * (N : ℝ)) := by positivity
      linarith
    calc (Real.sqrt (2 * Real.pi * N))⁻¹ * Real.exp (-(x - a) ^ 2 / (2 * N))
        ≤ (Real.sqrt (2 * Real.pi * N))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h_exp_le_one (by positivity)
      _ = (Real.sqrt (2 * Real.pi * N))⁻¹ := mul_one _
  -- each product `∏ᵢ gaussianPDFReal ≤ ∏ᵢ Bpeak`
  have h_prod_le : ∀ m : Fin M,
      (∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)) ≤ ∏ _i : Fin n, Bpeak := by
    intro m
    refine Finset.prod_le_prod (fun i _ ↦ gaussianPDFReal_nonneg _ _ _) (fun i _ ↦ ?_)
    exact h_comp_le (c.encoder m i) (y i)
  -- mixture average of `M` terms each `≤ ∏ᵢ Bpeak`
  calc (1 / (M : ℝ)) * ∑ m : Fin M, ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)
      ≤ (1 / (M : ℝ)) * ∑ _m : Fin M, ∏ _i : Fin n, Bpeak := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum (fun m _ ↦ h_prod_le m)
    _ = (1 / (M : ℝ)) * ((M : ℝ) * ∏ _i : Fin n, Bpeak) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ∏ _i : Fin n, Bpeak := by
        rcases Nat.eq_zero_or_pos M with hM0 | hMpos
        · exact absurd hM0 (NeZero.ne M)
        · have : (M : ℝ) ≠ 0 := by exact_mod_cast hMpos.ne'
          field_simp

/-- Per-component output log-density integrability (n-dim). For each codeword index
`m`, `log (blockYLaw.rnDeriv volume y)` is integrable against the m-th block component
`pi (gaussianReal (encoder m i) N)`. The mixture density is bounded above by the Gaussian
peak (so `log ≤ const`) and below by component `m` (so `-log ≤ ∑ᵢ (yᵢ − encoder m i)²/(2N)
+ const`); both sides are dominated by a finite-second-moment quadratic on the n-dim
Gaussian component. Lift of the 1-D `integrable_log_rnDeriv_perLetterYLaw`. -/
private lemma integrable_log_blockYLaw_on_component
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (m : Fin M) :
    Integrable
      (fun y ↦ Real.log ((blockYLaw h_meas c).rnDeriv MeasureTheory.volume y).toReal)
      (Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N)) := by
  classical
  set q := blockYLaw h_meas c with hq_def
  set νm := Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N) with hνm_def
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
  haveI : ∀ i, IsProbabilityMeasure (gaussianReal (c.encoder m i) N) := fun i ↦ inferInstance
  haveI hνm_prob : IsProbabilityMeasure νm := by rw [hνm_def]; infer_instance
  -- density form: `q = vol.withDensity (ofReal ∘ blockRealDensity)`
  have hq_wd : q = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
      (fun y ↦ ENNReal.ofReal (blockRealDensity N c y)) := by
    rw [hq_def]; exact blockYLaw_withDensity_real hN h_meas c
  have hDR_meas : Measurable (fun y ↦ ENNReal.ofReal (blockRealDensity N c y)) :=
    ENNReal.measurable_ofReal.comp (blockRealDensity_measurable c)
  -- `νm ≪ vol` (product of full-support Gaussians = withDensity of vol)
  have hνm_ac : νm ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := by
    rw [hνm_def, blockComponent_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  -- `q.rnDeriv vol =ᵐ[vol] ofReal ∘ blockRealDensity`, transport to `=ᵐ[νm]`
  have h_rn_vol : q.rnDeriv (MeasureTheory.volume : Measure (Fin n → ℝ))
      =ᵐ[(MeasureTheory.volume : Measure (Fin n → ℝ))]
      (fun y ↦ ENNReal.ofReal (blockRealDensity N c y)) := by
    rw [hq_wd]; exact Measure.rnDeriv_withDensity _ hDR_meas
  have h_rn_νm : q.rnDeriv (MeasureTheory.volume : Measure (Fin n → ℝ))
      =ᵐ[νm] (fun y ↦ ENNReal.ofReal (blockRealDensity N c y)) :=
    hνm_ac.ae_le h_rn_vol
  -- target integrand agrees a.e. with `log (blockRealDensity y)`
  have h_log_ae : (fun y ↦ Real.log (q.rnDeriv MeasureTheory.volume y).toReal)
      =ᵐ[νm] (fun y ↦ Real.log (blockRealDensity N c y)) := by
    filter_upwards [h_rn_νm] with y hy
    rw [hy, ENNReal.toReal_ofReal (blockRealDensity_pos hN c y).le]
  refine (Integrable.congr ?_ h_log_ae.symm)
  -- dominate `|log (blockRealDensity y)|` by `A + Bcoef · ∑ᵢ (yᵢ - encoder m i)²`
  set Bpeak : ℝ := (Real.sqrt (2 * Real.pi * N))⁻¹ with hBpeak
  have hBpeak_pos : 0 < Bpeak := by rw [hBpeak]; positivity
  -- upper: blockRealDensity y ≤ ∏ᵢ Bpeak
  have hD_le : ∀ y, blockRealDensity N c y ≤ ∏ _i : Fin n, Bpeak := blockRealDensity_le_sup c
  -- lower: blockRealDensity y ≥ M⁻¹ · ∏ᵢ gaussianPDFReal (encoder m i) N (yᵢ)
  have hD_ge : ∀ y, (1 / (M : ℝ)) * ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)
      ≤ blockRealDensity N c y := fun y ↦ blockRealDensity_ge_component c m y
  -- the dominating function (n-dim quadratic), integrable against νm
  set c₀ : ℝ := -(1 / 2) * Real.log (2 * Real.pi * N) with hc₀
  set c₁ : ℝ := -(1 / (2 * (N : ℝ))) with hc₁
  set Aconst : ℝ := |Real.log (∏ _i : Fin n, Bpeak)|
      + |Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀| with hAconst
  set Bcoef : ℝ := |c₁| with hBcoef
  have h_dom : Integrable
      (fun y : Fin n → ℝ ↦ Aconst + Bcoef * ∑ i : Fin n, (y i - c.encoder m i) ^ 2) νm := by
    refine (integrable_const Aconst).add (Integrable.const_mul ?_ Bcoef)
    -- `∑ᵢ (yᵢ - encoder m i)²` integrable against the product Gaussian νm
    rw [hνm_def]
    refine integrable_finsetSum _ (fun i _ ↦ ?_)
    -- coordinate `i` integrable: lift the 1-D second-moment integrability via
    -- `integrable_comp_eval`
    have h_1d : Integrable (fun y : ℝ ↦ (y - c.encoder m i) ^ 2)
        (gaussianReal (c.encoder m i) N) := by
      have h_id : Integrable (fun y : ℝ ↦ y) (gaussianReal (c.encoder m i) N) := by
        simpa using (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 1).integrable (by norm_num)
      have h_sq : Integrable (fun y : ℝ ↦ y ^ 2) (gaussianReal (c.encoder m i) N) :=
        (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 2).integrable_sq
      have hrw : (fun y : ℝ ↦ (y - c.encoder m i) ^ 2)
          = fun y ↦ y ^ 2 - 2 * (c.encoder m i) * y + (c.encoder m i) ^ 2 := by funext y; ring
      rw [hrw]
      exact ((h_sq.sub (h_id.const_mul (2 * c.encoder m i))).add
        (integrable_const ((c.encoder m i) ^ 2)))
    exact integrable_comp_eval (μ := fun i : Fin n ↦ gaussianReal (c.encoder m i) N)
      (i := i) h_1d
  refine Integrable.mono' h_dom ?_ ?_
  · exact (Real.measurable_log.comp (blockRealDensity_measurable c)).aestronglyMeasurable
  · filter_upwards with y
    have hDy_pos : 0 < blockRealDensity N c y := blockRealDensity_pos hN c y
    set S : ℝ := ∑ i : Fin n, (y i - c.encoder m i) ^ 2 with hS
    have hS_nonneg : 0 ≤ S := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
    have hc₁_nonpos : c₁ ≤ 0 := by rw [hc₁]; simp only [neg_nonpos]; positivity
    -- upper: log (blockRealDensity y) ≤ log (∏ᵢ Bpeak)
    have h_upper : Real.log (blockRealDensity N c y) ≤ Real.log (∏ _i : Fin n, Bpeak) := by
      have h_prod_pos : (0 : ℝ) < ∏ _i : Fin n, Bpeak := Finset.prod_pos (fun _ _ ↦ hBpeak_pos)
      exact Real.log_le_log hDy_pos (hD_le y)
    -- lower: log (blockRealDensity y) ≥ log (M⁻¹) + n·c₀ + c₁·S
    have h_lower : Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀ + c₁ * S
        ≤ Real.log (blockRealDensity N c y) := by
      have hMinv_pos : (0 : ℝ) < 1 / (M : ℝ) := by positivity
      have hprod_pos : (0 : ℝ) < ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i) :=
        Finset.prod_pos (fun i _ ↦ gaussianPDFReal_pos _ _ _ hN)
      have h_log_prod : Real.log ((1 / (M : ℝ)) *
            ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i))
          = Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀ + c₁ * S := by
        rw [Real.log_mul hMinv_pos.ne' hprod_pos.ne', Real.log_prod (fun i _ ↦
          (gaussianPDFReal_pos (c.encoder m i) N (y i) hN).ne')]
        have h_each : ∀ i : Fin n, Real.log (gaussianPDFReal (c.encoder m i) N (y i))
            = c₀ + c₁ * (y i - c.encoder m i) ^ 2 := by
          intro i
          rw [InformationTheory.Shannon.log_gaussianPDFReal_eq (c.encoder m i) hN (y i), hc₀, hc₁]
          ring
        rw [Finset.sum_congr rfl (fun i _ ↦ h_each i), hS, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
        ring
      calc Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀ + c₁ * S
          = Real.log ((1 / (M : ℝ)) * ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)) :=
            h_log_prod.symm
        _ ≤ Real.log (blockRealDensity N c y) :=
            Real.log_le_log (mul_pos hMinv_pos hprod_pos) (hD_ge y)
    -- combine: |log| ≤ Aconst + Bcoef·S
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨?_, ?_⟩
    · -- lower side: -(Aconst + Bcoef·S) ≤ log (blockRealDensity y)
      have hc₁S : c₁ * S = -(Bcoef * S) := by rw [hBcoef, abs_of_nonpos hc₁_nonpos]; ring
      have hlb : -(Aconst + Bcoef * S)
          ≤ Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀ + c₁ * S := by
        rw [hAconst, hc₁S]
        have h1 := neg_abs_le (Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀)
        have h2 := abs_nonneg (Real.log (∏ _i : Fin n, Bpeak))
        linarith
      exact le_trans hlb h_lower
    · -- upper side: log (blockRealDensity y) ≤ Aconst + Bcoef·S
      have hub : Real.log (∏ _i : Fin n, Bpeak) ≤ Aconst + Bcoef * S := by
        rw [hAconst]
        have h1 := le_abs_self (Real.log (∏ _i : Fin n, Bpeak))
        have h2 := abs_nonneg (Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀)
        have h3 : 0 ≤ Bcoef * S := mul_nonneg (abs_nonneg _) hS_nonneg
        linarith
      exact le_trans h_upper hub

/-! ### Finiteness of `I(W; Yⁿ)` via the discrete-input compProd chain rule

Since `W = Fin M` is discrete, the joint is `(M⁻¹ • count) ⊗ₘ K` with `K m` the `n`-dimensional
block component, and the product of marginals is `(M⁻¹ • count) ⊗ₘ const blockY`. Finiteness
follows from `klDiv_ne_top` (absolute continuity plus integrable log-likelihood ratio), reduced
per-fibre to the output log-density integrability of each component
(`integrable_log_blockYLaw_on_component`) and the Gaussian fibre log-density integrability. -/

/-- Discrete-input block kernel `K m := pi (gaussianReal (encoder m i) N)` (`Fin M → Yⁿ`). -/
private noncomputable def blockKernel
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) :
    Kernel (Fin M) (Fin n → ℝ) :=
  { toFun := fun m ↦ Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N)
    measurable' := measurable_of_countable _ }

private instance blockKernel_isMarkov
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} (c : AwgnCode M n P) :
    IsMarkovKernel (blockKernel N c) :=
  ⟨fun m ↦ by
    show IsProbabilityMeasure (Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N))
    infer_instance⟩

/-- Discrete message marginal `ν_W := (M⁻¹ : ℝ≥0∞) • count`. -/
private noncomputable def msgLaw (M : ℕ) : Measure (Fin M) :=
  (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ • Measure.count

private instance msgLaw_isFinite (M : ℕ) [NeZero M] : IsFiniteMeasure (msgLaw M) := by
  unfold msgLaw
  haveI : IsFiniteMeasure (Measure.count : Measure (Fin M)) := Measure.count.isFiniteMeasure
  refine Measure.smul_finite _ ?_
  rw [Fintype.card_fin]; simp; exact_mod_cast NeZero.ne M

/-- `awgnConverseJoint = msgLaw ⊗ₘ blockKernel`. -/
private lemma awgnConverseJoint_eq_compProd
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    awgnConverseJoint h_meas c = msgLaw M ⊗ₘ blockKernel N c := by
  classical
  unfold awgnConverseJoint msgLaw
  rw [Measure.compProd_smul_left]
  congr 1
  -- goal: `∑ₘ (δ_m).prod νₘ = count ⊗ₘ K` (after `congr 1`)
  rw [count_eq_finset_sum_dirac (Fin M), ← Measure.sum_fintype
        (fun a : Fin M ↦ Measure.dirac a),
    Measure.compProd_sum_left, Measure.sum_fintype]
  symm
  refine Finset.sum_congr rfl (fun m _ ↦ ?_)
  -- `(δ_m) ⊗ₘ K = (δ_m).prod (K m) = (δ_m).prod νₘ`
  -- (`K m = νₘ`, `awgnChannel = gaussianReal` defeq)
  rw [show (Measure.dirac m) ⊗ₘ blockKernel N c
        = (Measure.dirac m).prod (blockKernel N c m) by
      ext s hs
      rw [Measure.dirac_compProd_apply hs, Measure.dirac_prod,
        Measure.map_apply measurable_prodMk_left hs]]
  refine congrArg ((Measure.dirac m).prod) ?_
  show Measure.pi (fun i : Fin n ↦ awgnChannel N h_meas (c.encoder m i))
      = Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N)
  refine congrArg Measure.pi ?_
  funext i
  rw [awgnChannel_apply]

/-- `(awgnConverseJoint.map fst).prod (awgnConverseJoint.map snd) = msgLaw ⊗ₘ const blockYLaw`. -/
private lemma awgnConverseJoint_prod_marginals_eq
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    ((awgnConverseJoint h_meas c).map Prod.fst).prod ((awgnConverseJoint h_meas c).map Prod.snd)
      = msgLaw M ⊗ₘ Kernel.const (Fin M) (blockYLaw h_meas c) := by
  rw [awgnConverseJoint_map_fst h_meas c,
    show (awgnConverseJoint h_meas c).map Prod.snd = blockYLaw h_meas c from rfl,
    show ((Fintype.card (Fin M) : ℝ≥0∞)⁻¹ • Measure.count) = msgLaw M from rfl,
    Measure.compProd_const]

/-- Block component `νₘ := pi (gaussianReal (encoder m i) N) ≪ blockYLaw` (mixture dominates
each component, via `νₘ ≪ vol ≪ blockYLaw`). -/
private lemma blockComponent_ac_blockYLaw
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (m : Fin M) :
    Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N) ≪ blockYLaw h_meas c := by
  -- `νₘ ≪ vol ≪ blockYLaw`
  have h1 : Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N)
      ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := by
    rw [blockComponent_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have h2 : (MeasureTheory.volume : Measure (Fin n → ℝ)) ≪ blockYLaw h_meas c := by
    rw [blockYLaw_withDensity_real hN h_meas c]
    refine withDensity_absolutelyContinuous'
      (ENNReal.measurable_ofReal.comp (blockRealDensity_measurable c)).aemeasurable ?_
    refine Filter.Eventually.of_forall (fun y ↦ ?_)
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact blockRealDensity_pos hN c y
  exact h1.trans h2

/-- Per-fibre log-likelihood-ratio integrability: `log (νₘ.rnDeriv blockYLaw)` is integrable
against the block component `νₘ`. Chain rule `log(νₘ/blockY) = log(νₘ/vol) − log(blockY/vol)`:
the first term is the product-Gaussian log-density (quadratic, integrable) and the second is
`integrable_log_blockYLaw_on_component`. -/
private lemma integrable_log_component_rnDeriv_blockYLaw
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (m : Fin M) :
    Integrable
      (fun y ↦ Real.log
        ((Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N)).rnDeriv
          (blockYLaw h_meas c) y).toReal)
      (Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N)) := by
  classical
  set νm := Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N) with hνm
  set q := blockYLaw h_meas c with hq
  haveI : ∀ i, IsProbabilityMeasure (gaussianReal (c.encoder m i) N) := fun i ↦ inferInstance
  haveI hνm_prob : IsProbabilityMeasure νm := by rw [hνm]; infer_instance
  haveI hq_prob : IsProbabilityMeasure q := by rw [hq]; infer_instance
  have hνm_q : νm ≪ q := blockComponent_ac_blockYLaw hN h_meas c m
  have hq_vol : q ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := blockYLaw_ac_volume hN h_meas c
  have hνm_vol : νm ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := by
    rw [hνm, blockComponent_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  -- (A) `log (νm.rnDeriv vol y)` integrable against νm: product-Gaussian log-density (quadratic).
  -- `νm.rnDeriv vol =ᵐ[νm] (∏ᵢ gaussianPDF)`, so the log equals `∑ᵢ log gaussianPDFReal`.
  have h_rn_νm_vol : νm.rnDeriv (MeasureTheory.volume : Measure (Fin n → ℝ))
      =ᵐ[νm] (fun y ↦ ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
    have h_wd : νm = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
        (fun y ↦ ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
      rw [hνm]; exact blockComponent_withDensity hN c m
    have h_meas_dens :
        Measurable (fun y : Fin n → ℝ ↦ ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) :=
      Finset.measurable_prod _ (fun i _ ↦
        (measurable_gaussianPDF (c.encoder m i) N).comp (measurable_pi_apply i))
    exact hνm_vol.ae_le (by rw [h_wd]; exact Measure.rnDeriv_withDensity _ h_meas_dens)
  have h_log_νm_vol_ae : (fun y ↦ Real.log (νm.rnDeriv (MeasureTheory.volume) y).toReal)
      =ᵐ[νm] (fun y ↦ ∑ i : Fin n,
          (-(1 / 2) * Real.log (2 * Real.pi * N) - (y i - c.encoder m i) ^ 2 / (2 * (N : ℝ)))) := by
    filter_upwards [h_rn_νm_vol] with y hy
    rw [hy, ENNReal.toReal_prod]
    simp_rw [toReal_gaussianPDF]
    rw [Real.log_prod (fun i _ ↦ (gaussianPDFReal_pos (c.encoder m i) N (y i) hN).ne')]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [InformationTheory.Shannon.log_gaussianPDFReal_eq (c.encoder m i) hN (y i)]
  have h_int_νm_vol : Integrable
      (fun y ↦ Real.log (νm.rnDeriv (MeasureTheory.volume) y).toReal) νm := by
    refine Integrable.congr ?_ h_log_νm_vol_ae.symm
    refine integrable_finsetSum _ (fun i _ ↦ ?_)
    -- each `(-(1/2)log(2πN) - (yᵢ - encoder m i)²/(2N))` integrable against νm
    refine (integrable_const _).sub ?_
    have h_1d : Integrable (fun y : ℝ ↦ (y - c.encoder m i) ^ 2 / (2 * (N : ℝ)))
        (gaussianReal (c.encoder m i) N) := by
      have h_id : Integrable (fun y : ℝ ↦ y) (gaussianReal (c.encoder m i) N) := by
        simpa using (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 1).integrable (by norm_num)
      have h_sq : Integrable (fun y : ℝ ↦ y ^ 2) (gaussianReal (c.encoder m i) N) :=
        (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 2).integrable_sq
      have hrw : (fun y : ℝ ↦ (y - c.encoder m i) ^ 2 / (2 * (N : ℝ)))
          = fun y ↦ (y ^ 2 - 2 * (c.encoder m i) * y + (c.encoder m i) ^ 2) / (2 * (N : ℝ)) := by
        funext y; ring
      rw [hrw]
      exact (((h_sq.sub (h_id.const_mul (2 * c.encoder m i))).add
        (integrable_const ((c.encoder m i) ^ 2))).div_const _)
    rw [hνm]
    exact integrable_comp_eval (μ := fun i : Fin n ↦ gaussianReal (c.encoder m i) N) (i := i) h_1d
  -- (B) `log (q.rnDeriv vol)` integrable against νm: `integrable_log_blockYLaw_on_component`.
  have h_int_q_vol : Integrable
      (fun y ↦ Real.log (q.rnDeriv (MeasureTheory.volume) y).toReal) νm := by
    rw [hq, hνm]; exact integrable_log_blockYLaw_on_component hN h_meas c m
  -- chain rule split: `log (νm.rnDeriv q) =ᵐ[νm] log(νm.rnDeriv vol) − log(q.rnDeriv vol)`
  have h_split : (fun y ↦ Real.log (νm.rnDeriv q y).toReal)
      =ᵐ[νm] (fun y ↦ Real.log (νm.rnDeriv (MeasureTheory.volume) y).toReal
                - Real.log (q.rnDeriv (MeasureTheory.volume) y).toReal) := by
    have h_chain : (fun y ↦ νm.rnDeriv q y * q.rnDeriv (MeasureTheory.volume) y)
        =ᵐ[νm] νm.rnDeriv (MeasureTheory.volume) :=
      hνm_q.ae_le (Measure.rnDeriv_mul_rnDeriv' (μ := νm) (ν := q)
        (κ := (MeasureTheory.volume : Measure (Fin n → ℝ))) hq_vol)
    have h_pos_νq : ∀ᵐ y ∂νm, 0 < νm.rnDeriv q y := Measure.rnDeriv_pos hνm_q
    have h_lt_νq : ∀ᵐ y ∂νm, νm.rnDeriv q y < ∞ := hνm_q.ae_le (Measure.rnDeriv_lt_top νm q)
    have h_pos_q : ∀ᵐ y ∂νm, 0 < q.rnDeriv (MeasureTheory.volume) y :=
      hνm_q.ae_le (Measure.rnDeriv_pos hq_vol)
    have h_lt_q : ∀ᵐ y ∂νm, q.rnDeriv (MeasureTheory.volume) y < ∞ :=
      hνm_q.ae_le (hq_vol.ae_le (Measure.rnDeriv_lt_top q (MeasureTheory.volume)))
    filter_upwards [h_chain, h_pos_νq, h_lt_νq, h_pos_q, h_lt_q]
      with y hy hpos1 hlt1 hpos2 hlt2
    have hne1 : ((νm.rnDeriv q y).toReal) ≠ 0 :=
      (ENNReal.toReal_pos hpos1.ne' hlt1.ne).ne'
    have hne2 : ((q.rnDeriv (MeasureTheory.volume) y).toReal) ≠ 0 :=
      (ENNReal.toReal_pos hpos2.ne' hlt2.ne).ne'
    rw [← hy, ENNReal.toReal_mul, Real.log_mul hne1 hne2]
    ring
  exact (h_int_νm_vol.sub h_int_q_vol).congr h_split.symm

/-- I(W; Y^n) finiteness (genuine). -/
private lemma awgnConverseJoint_mi_W_ne_top
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    mutualInfo (awgnConverseJoint h_meas c)
        (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
        (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) ≠ ∞ := by
  classical
  -- `mutualInfo = klDiv (μ.map (fst,snd)) ((μ.map fst).prod (μ.map snd))`, and
  -- `μ.map (fst,snd) = μ = msgLaw ⊗ₘ K`, product of marginals = msgLaw ⊗ₘ const blockY.
  rw [mutualInfo]
  have h_joint : (awgnConverseJoint h_meas c).map
      (fun ω : Fin M × (Fin n → ℝ) ↦ (ω.1, ω.2)) = msgLaw M ⊗ₘ blockKernel N c := by
    rw [show (fun ω : Fin M × (Fin n → ℝ) ↦ (ω.1, ω.2)) = id from rfl, Measure.map_id]
    exact awgnConverseJoint_eq_compProd h_meas c
  rw [h_joint, awgnConverseJoint_prod_marginals_eq h_meas c]
  -- finiteness via `klDiv_ne_top_iff`: AC + integrable llr on the compProd
  refine klDiv_ne_top ?_ ?_
  · -- AC: msgLaw ⊗ₘ K ≪ msgLaw ⊗ₘ const blockY (per-fibre `K m ≪ blockY`)
    refine Measure.AbsolutelyContinuous.compProd_right ?_
    filter_upwards with m
    exact blockComponent_ac_blockYLaw hN h_meas c m
  · -- integrable llr via `Measure.integrable_compProd_iff` (per-fibre + finite-sum L¹ norm)
    set K := blockKernel N c with hK
    set ηc := Kernel.const (Fin M) (blockYLaw h_meas c) with hηc
    -- AC of the compProd (same as the AC branch above)
    have h_ac : msgLaw M ⊗ₘ K ≪ msgLaw M ⊗ₘ ηc := by
      refine Measure.AbsolutelyContinuous.compProd_right ?_
      filter_upwards with m
      rw [hηc]; exact blockComponent_ac_blockYLaw hN h_meas c m
    -- the joint llr agrees a.e. with the jointly-measurable kernel rnDeriv log.
    have h_llr_ae : (fun p ↦ llr (msgLaw M ⊗ₘ K) (msgLaw M ⊗ₘ ηc) p)
        =ᵐ[msgLaw M ⊗ₘ K]
        (fun p : Fin M × (Fin n → ℝ) ↦ Real.log ((K.rnDeriv ηc p.1 p.2)).toReal) := by
      -- linchpin: joint rnDeriv =ᵐ[μ⊗ₘη] fibre kernel rnDeriv; transport to a.e. on the joint
      have h1 : (msgLaw M ⊗ₘ K).rnDeriv (msgLaw M ⊗ₘ ηc)
          =ᵐ[msgLaw M ⊗ₘ K] fun p ↦ K.rnDeriv ηc p.1 p.2 :=
        h_ac.ae_le
          (InformationTheory.Shannon.ChannelCoding.rnDeriv_compProd_fibre h_ac)
      simp only [llr_def]
      filter_upwards [h1] with p hp1
      rw [hp1]
    -- prove integrability of the kernel-rnDeriv log function, then `congr` back to llr.
    refine Integrable.congr ?_ h_llr_ae.symm
    refine (Measure.integrable_compProd_iff ?_).mpr ⟨?_, ?_⟩
    · -- AEStronglyMeasurable of `fun p => log(K.rnDeriv ηc p.1 p.2)` (jointly measurable).
      exact ((Kernel.measurable_rnDeriv K ηc).ennreal_toReal.log).aestronglyMeasurable
    · -- per-fibre integrability: `log(K.rnDeriv ηc m y) =ᵐ[K m] log((K m).rnDeriv blockY y)`.
      filter_upwards with m
      have h_fibre_ae : (fun y ↦ Real.log ((K.rnDeriv ηc m y)).toReal)
          =ᵐ[K m] (fun y ↦ Real.log (((K m).rnDeriv (blockYLaw h_meas c) y)).toReal) := by
        have hKm_blockY : K m ≪ blockYLaw h_meas c := by
          show Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N) ≪ blockYLaw h_meas c
          exact blockComponent_ac_blockYLaw hN h_meas c m
        have h_meas_eq : K m ≪ ηc m := by rw [hηc, Kernel.const_apply]; exact hKm_blockY
        filter_upwards [h_meas_eq.ae_le
          (Kernel.rnDeriv_eq_rnDeriv_measure (κ := K) (η := ηc) (a := m))] with y hy
        rw [hy]; simp only [hηc, Kernel.const_apply]
      refine Integrable.congr ?_ h_fibre_ae.symm
      show Integrable
        (fun y ↦ Real.log
          ((Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N)).rnDeriv
            (blockYLaw h_meas c) y).toReal)
        (Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N))
      exact integrable_log_component_rnDeriv_blockYLaw hN h_meas c m
    · -- L¹-norm-over-fibre integral integrable over the finite message measure
      exact Integrable.of_finite

/-- AWGN converse mutual-information finiteness:
`I(W; Yⁿ) ≠ ∞ ∧ I(Xⁿ; Yⁿ) ≠ ∞` on the canonical joint.

`hN : N ≠ 0` is a regularity precondition for the density route, not a load-bearing
hypothesis: at `N = 0` each `gaussianReal _ 0` degenerates to a Dirac measure and loses its
Lebesgue density. The proposition itself still holds at `N = 0` (with discrete `W` the joint
is finitely atomic), but this proof goes through the densities, so `N ≠ 0` is required.

@audit:ok -/
private lemma awgnConverseJoint_pair_mi_ne_top
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    mutualInfo (awgnConverseJoint h_meas c)
        (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
        (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) ≠ ∞
      ∧ jointMIXnYn h_meas c ≠ ∞ := by
  -- W side: genuine compProd-chain-rule finiteness.
  have h_W : mutualInfo (awgnConverseJoint h_meas c)
      (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
      (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) ≠ ∞ :=
    awgnConverseJoint_mi_W_ne_top hN h_meas c
  refine ⟨h_W, ?_⟩
  -- X^n side: `X^n = encoder ∘ W` is a post-processing of `W`, so DPI gives
  -- `I(X^n; Y^n) ≤ I(W; Y^n) < ∞`.
  have hfst : Measurable (Prod.fst : Fin M × (Fin n → ℝ) → Fin M) := measurable_fst
  have hsnd : Measurable (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) := measurable_snd
  have henc : Measurable (c.encoder : Fin M → Fin n → ℝ) := measurable_of_countable _
  -- `mutualInfo μ (encoder∘fst) snd = mutualInfo μ snd (encoder∘fst)` (comm)
  --   ≤ `mutualInfo μ snd fst` (postprocess the 2nd arg by `encoder`)
  --   = `mutualInfo μ fst snd` (comm)
  have h_le : jointMIXnYn h_meas c
      ≤ mutualInfo (awgnConverseJoint h_meas c) Prod.fst Prod.snd := by
    unfold jointMIXnYn
    rw [mutualInfo_comm (awgnConverseJoint h_meas c)
        (fun ω : Fin M × (Fin n → ℝ) ↦ c.encoder ω.1) Prod.snd (henc.comp hfst) hsnd]
    have h_pp :
        mutualInfo (awgnConverseJoint h_meas c) Prod.snd (c.encoder ∘ Prod.fst)
          ≤ mutualInfo (awgnConverseJoint h_meas c) Prod.snd Prod.fst :=
      mutualInfo_le_of_postprocess (awgnConverseJoint h_meas c) Prod.snd Prod.fst hsnd hfst henc
    rw [show (fun ω : Fin M × (Fin n → ℝ) ↦ c.encoder ω.1)
          = c.encoder ∘ Prod.fst from rfl]
    refine h_pp.trans ?_
    rw [mutualInfo_comm (awgnConverseJoint h_meas c) Prod.snd Prod.fst hsnd hfst]
  exact ne_top_of_le_ne_top h_W h_le

/-- AWGN converse mutual-information finiteness:
`mutualInfo (awgnConverseJoint c) Prod.fst Prod.snd ≠ ∞`.

@audit:ok -/
private lemma awgnConverseJoint_mutualInfo_ne_top
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    mutualInfo (awgnConverseJoint h_meas c)
        (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
        (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) ≠ ∞ :=
  (awgnConverseJoint_pair_mi_ne_top hN h_meas c).1

/-- Fano dispatch: assembling Fano's inequality, the data-processing postprocessing step,
the entropy chain, and `H(W) = log M` through `shannon_converse_single_shot` gives
`log M ≤ I(W; Yⁿ).toReal + binEntropy(Pe) + Pe · log(M − 1)`. -/
@[entry_point]
theorem awgn_converse_single_shot_call
    (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (hM : 2 ≤ M) (c : AwgnCode M n P)
    (Pe : ℝ) (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (jointMIWYn h_meas c).toReal
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  -- `2 ≤ M` ⇒ `[NeZero M]`
  have hM_pos : 0 < M := by omega
  haveI : NeZero M := ⟨hM_pos.ne'⟩
  -- Plumb hypotheses for `shannon_converse_single_shot`.
  have hMsg_meas : Measurable (Prod.fst : Fin M × (Fin n → ℝ) → Fin M) :=
    awgnConverseJoint_measurable_fst
  have hYo_meas : Measurable (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) :=
    awgnConverseJoint_measurable_snd
  have hMsg_uniform :
      (awgnConverseJoint h_meas c).map
          (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
        = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ • Measure.count :=
    awgnConverseJoint_map_fst h_meas c
  have hcard : 2 ≤ Fintype.card (Fin M) := by simpa [Fintype.card_fin] using hM
  have hMI_finite :
      mutualInfo (awgnConverseJoint h_meas c)
          (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
          (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) ≠ ∞ :=
    awgnConverseJoint_mutualInfo_ne_top hN h_meas c
  -- Apply `shannon_converse_single_shot`.
  have h_shannon :=
    InformationTheory.Shannon.shannon_converse_single_shot
      (μ := awgnConverseJoint h_meas c)
      (Msg := Prod.fst) (Yo := Prod.snd) (decoder := c.decoder)
      hMsg_meas hYo_meas c.decoder_meas hMsg_uniform hcard hMI_finite
  -- Rewrite `log (Fintype.card (Fin M))` as `log M`.
  have hcard_eq : (Fintype.card (Fin M) : ℝ) = (M : ℝ) := by
    simp [Fintype.card_fin]
  -- Rewrite the Fano `errorProb` to AWGN `Pe`.
  have h_errProb_eq : InformationTheory.MeasureFano.errorProb
      (awgnConverseJoint h_meas c)
      (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
      (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ)
      c.decoder = Pe := by
    rw [awgn_errorProb_eq_fano_errorProb, hPe]
  -- `jointMIWYn` unfold ⇒ `mutualInfo (awgnConverseJoint h_meas c) Prod.fst Prod.snd`.
  -- Substitute everything to match the goal.
  rw [hcard_eq] at h_shannon
  rw [h_errProb_eq] at h_shannon
  -- `jointMIWYn h_meas c = mutualInfo ... Prod.fst Prod.snd` by definition.
  show Real.log M ≤
      (jointMIWYn h_meas c).toReal + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1)
  unfold jointMIWYn
  exact h_shannon

/-! ## Data-processing and chain rule

The data-processing side derives `I(W; Yⁿ) ≤ I(Xⁿ; Yⁿ)` from `mutualInfo_le_of_markov`,
with the Markov factorization supplied by `awgnConverseMarkov_holds` (`AwgnWalls.lean`). The
chain-rule side connects to `awgnContinuousMIChainRule_holds` (`AwgnWalls.lean`) by
definitional equality. -/

/-- Data-processing inequality: the Markov chain `W → encoder ∘ W → Yⁿ` yields
`I(W; Yⁿ) ≤ I(Xⁿ; Yⁿ)` via `mutualInfo_le_of_markov`, with the Markov factorization
supplied by `awgnConverseMarkov_holds`. -/
@[entry_point]
theorem awgn_dpi
    (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    (jointMIWYn h_meas c).toReal ≤ (jointMIXnYn h_meas c).toReal := by
  -- Markov chain `W → X^n → Y^n` ⇒ ENNReal DPI `mutualInfo W Y^n ≤ mutualInfo X^n Y^n`.
  -- The Markov factorization comes from `awgnConverseMarkov_holds`, connected to
  -- `IsMarkovChain (awgnConverseJoint …)` by definitional equality.
  have h_markov :
      IsMarkovChain (awgnConverseJoint h_meas c)
        (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
        (fun ω : Fin M × (Fin n → ℝ) ↦ c.encoder ω.1)
        (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) :=
    awgnConverseMarkov_holds h_meas c
  -- Measurability of the three random variables on `Fin M × (Fin n → ℝ)`.
  have hW_meas : Measurable (Prod.fst : Fin M × (Fin n → ℝ) → Fin M) :=
    measurable_fst
  have hYn_meas : Measurable (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) :=
    measurable_snd
  -- `fun ω => c.encoder ω.1` is measurable: `Fin M` is finite/discrete so any
  -- function out of it is measurable; precompose with the (measurable) `Prod.fst`.
  have hEnc_const : Measurable (c.encoder : Fin M → Fin n → ℝ) :=
    measurable_of_countable c.encoder
  have hXn_meas : Measurable (fun ω : Fin M × (Fin n → ℝ) ↦ c.encoder ω.1) :=
    hEnc_const.comp hW_meas
  -- ENNReal DPI via `mutualInfo_le_of_markov`.
  have h_dpi_enn :
      mutualInfo (awgnConverseJoint h_meas c) Prod.fst Prod.snd ≤
        mutualInfo (awgnConverseJoint h_meas c)
          (fun ω : Fin M × (Fin n → ℝ) ↦ c.encoder ω.1) Prod.snd :=
    mutualInfo_le_of_markov (μ := awgnConverseJoint h_meas c)
      (Xs := Prod.fst) (Zc := fun ω ↦ c.encoder ω.1) (Yo := Prod.snd)
      hW_meas hXn_meas hYn_meas h_markov
  -- Lift to `.toReal` via `ENNReal.toReal_mono`; the RHS finiteness is the
  -- AWGN-side MI finiteness wall (T-FFC-2/T-FFC-3 family, sibling of
  -- `awgnConverseJoint_mutualInfo_ne_top` but for `X^n`).
  have h_finite : (jointMIXnYn h_meas c) ≠ ∞ :=
    (awgnConverseJoint_pair_mi_ne_top hN h_meas c).2
  -- Unfold `jointMIWYn` / `jointMIXnYn` to match the ENNReal inequality, apply
  -- `ENNReal.toReal_mono`.
  show (jointMIWYn h_meas c).toReal ≤ (jointMIXnYn h_meas c).toReal
  unfold jointMIWYn jointMIXnYn
  exact ENNReal.toReal_mono h_finite h_dpi_enn

/-- Mutual-information chain rule for the memoryless AWGN channel:
`I(Xⁿ; Yⁿ) ≤ ∑ᵢ I(Xᵢ; Yᵢ)`, supplied by `awgnContinuousMIChainRule_holds`. `hN` and
`[NeZero M]` are regularity preconditions of that lemma's density route. -/
@[entry_point]
theorem awgn_chain_rule
    (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    (jointMIXnYn h_meas c).toReal ≤ ∑ i : Fin n, (perLetterMI h_meas c i).toReal :=
  awgnContinuousMIChainRule_holds hN h_meas c


/-- Joint mutual-information finiteness on the AWGN converse joint:
`I(W; Yⁿ) ≠ ∞ ∧ I(Xⁿ; Yⁿ) ≠ ∞`, since
`I(W; Yⁿ) ≤ I(Xⁿ; Yⁿ) ≤ ∑ᵢ I(Xᵢ; Yᵢ) ≤ n · (1/2) log(1 + P/N) < ∞`.

@audit:ok -/
@[entry_point]
theorem awgnConverseJoint_mutualInfo_ne_top_via_chain
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (hn_pos : 0 < n) (c : AwgnCode M n P) :
    mutualInfo (awgnConverseJoint h_meas c)
        (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
        (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) ≠ ∞
      ∧ jointMIXnYn h_meas c ≠ ∞ :=
  awgnConverseJoint_pair_mi_ne_top
    (by intro h; exact hN (by rw [h]; norm_num)) h_meas c

end InformationTheory.Shannon.AWGN
