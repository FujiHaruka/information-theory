import InformationTheory.Shannon.ShannonHartleyOperational
import InformationTheory.Shannon.ParallelGaussian.Converse.MixtureDensity
import InformationTheory.Shannon.Converse
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.DPI
import InformationTheory.Shannon.ChannelCoding.Basic
import InformationTheory.Shannon.BlockwiseChannel.Definition
import InformationTheory.Shannon.AWGN.ChannelMeasurability
import InformationTheory.Shannon.AWGN.ConverseMutualInfoFiniteness

/-!
# Shannon-Hartley converse — C3: operational parallel-Gaussian converse (equal-noise form)

The converse chain for a `ContAwgnCode T W P M`, reducing the operational rate `log M` to the
per-coordinate parallel-Gaussian sum plus Fano's error terms:

`log M ≤ ∑ᵢ ½·log(1 + P'ᵢ/(N₀/2)) + binEntropy(Pe) + Pe·log(M − 1)`

with `∑ᵢ P'ᵢ ≤ T·P`. This is the **equal-noise** form (constant per-coordinate noise `N₀/2`); the
Gram/prolate gains `νᵢ` enter downstream (C2 rotation + C4 water-filling) on the signal-power side.

The chain (mirroring the discrete AWGN converse's wiring):
1. Fano + DPI single-shot: `log M ≤ I(W; Y).toReal + Fano`  (`shannon_converse_single_shot`).
2. Markov DPI `W → S → Y`, `S = observation ∘ W`: `I(W; Y) ≤ I(S; Y)`  (`mutualInfo_le_of_markov`).
3. RV ↔ channel bridge: `I(S; Y) = mutualInfoOfChannel p_S W_chan`.
4. Parallel MI bound: `(mutualInfoOfChannel p_S W_chan).toReal ≤ ∑ᵢ ½log(1 + P'ᵢ/(N₀/2))`,
   `∑ P'ᵢ ≤ T·P`  (`parallel_per_input_mi_le_sum` + Bessel constraint membership).

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Chapter 9 (Gaussian channel) and the parallel-Gaussian water-filling of §9.4.
-/

namespace InformationTheory.Shannon.ShannonHartley

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.ParallelGaussian
  InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators

/-! ## §L0 — The canonical joint law and its probability-measure instance -/

/-- Canonical joint law of `(W, Y)` for a `ContAwgnCode` under a uniform message and the
inlined per-observation AWGN law — the ContAwgn analog of `AWGN.awgnConverseJoint`. -/
noncomputable def contAwgnConverseJoint {T W P : ℝ} {M : ℕ}
    (c : ContAwgnCode T W P M) (N₀ : ℝ) : Measure (Fin M × (Fin c.k → ℝ)) :=
  ((M : ℝ≥0∞)⁻¹) • ∑ m : Fin M,
    (Measure.dirac m).prod
      (Measure.pi (fun i : Fin c.k ↦ gaussianReal (c.observation m i) (N₀ / 2).toNNReal))

/-- `contAwgnConverseJoint` is a probability measure for `M ≥ 1`. -/
instance contAwgnConverseJoint.instIsProbabilityMeasure {T W P : ℝ} {M : ℕ} [NeZero M]
    (c : ContAwgnCode T W P M) (N₀ : ℝ) :
    IsProbabilityMeasure (contAwgnConverseJoint c N₀) := by
  refine ⟨?_⟩
  unfold contAwgnConverseJoint
  rw [Measure.smul_apply, Measure.finsetSum_apply _ _ Set.univ]
  have h_summand : ∀ m : Fin M,
      ((Measure.dirac m).prod
          (Measure.pi (fun i : Fin c.k ↦
            gaussianReal (c.observation m i) (N₀ / 2).toNNReal))) Set.univ = 1 :=
    fun m ↦ measure_univ
  simp only [h_summand, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  have hM_ne_zero : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hM_ne_top : (M : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top M
  exact ENNReal.inv_mul_cancel hM_ne_zero hM_ne_top

/-! ## Constant-noise parallel channel and its measurability discharge -/

/-- The per-coordinate AWGN measurability hypothesis for the constant noise family. -/
lemma contAwgn_isParallelAwgnChannelMeasurable {k : ℕ} (Nv : ℝ≥0) :
    IsParallelAwgnChannelMeasurable (n := k) (fun _ ↦ Nv) :=
  fun _ ↦ AWGN.isAwgnChannelMeasurable Nv

/-- The parallel-kernel measurability hypothesis for the constant noise family: the product
Gaussian map `x ↦ Measure.pi (fun i ↦ gaussianReal (x i) Nv)` is measurable. -/
lemma contAwgn_isParallelGaussianKernelMeasurable {k : ℕ} (Nv : ℝ≥0) :
    IsParallelGaussianKernelMeasurable (n := k) (fun _ ↦ Nv) := by
  unfold IsParallelGaussianKernelMeasurable
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := Set.pi Set.univ '' Set.pi Set.univ
      (fun _ : Fin k ↦ { s : Set ℝ | MeasurableSet s }))
    generateFrom_pi.symm isPiSystem_pi ?_
  rintro _ ⟨t, ht, rfl⟩
  simp only [Set.mem_pi, Set.mem_univ, true_imp_iff] at ht
  have ht' : ∀ i : Fin k, MeasurableSet (t i) := ht
  have h_eval : ∀ x : Fin k → ℝ,
      Measure.pi (fun i : Fin k ↦ gaussianReal (x i) Nv) (Set.univ.pi t)
        = ∏ i : Fin k, (gaussianReal (x i) Nv) (t i) := fun x ↦ by rw [Measure.pi_pi]
  simp_rw [h_eval]
  refine Finset.measurable_prod _ ?_
  intro i _
  exact ((Measure.measurable_coe (ht' i)).comp
    (AWGN.isAwgnChannelMeasurable Nv)).comp (measurable_pi_apply i)

/-- The constant-noise parallel Gaussian channel `Fin k → ℝ → Fin k → ℝ`. -/
noncomputable def contAwgnConstChannel (k : ℕ) (Nv : ℝ≥0) :
    Channel (Fin k → ℝ) (Fin k → ℝ) :=
  parallelGaussianChannel (fun _ ↦ Nv)
    (contAwgn_isParallelAwgnChannelMeasurable Nv)
    (contAwgn_isParallelGaussianKernelMeasurable Nv)

@[simp] lemma contAwgnConstChannel_apply (k : ℕ) (Nv : ℝ≥0) (x : Fin k → ℝ) :
    (contAwgnConstChannel k Nv) x = Measure.pi (fun i ↦ gaussianReal (x i) Nv) := rfl

instance contAwgnConstChannel.instIsMarkovKernel (k : ℕ) (Nv : ℝ≥0) :
    IsMarkovKernel (contAwgnConstChannel k Nv) :=
  parallelGaussianChannel.instIsMarkovKernel _ _ _

/-- The signal (codeword) law `p_S`: the law of `S = observation ∘ W` under the uniform message. -/
noncomputable def contAwgnSignalLaw {T W P : ℝ} {M : ℕ}
    (c : ContAwgnCode T W P M) (N₀ : ℝ) : Measure (Fin c.k → ℝ) :=
  (contAwgnConverseJoint c N₀).map (fun ω ↦ c.observation ω.1)

instance contAwgnSignalLaw.instIsProbabilityMeasure {T W P : ℝ} {M : ℕ} [NeZero M]
    (c : ContAwgnCode T W P M) (N₀ : ℝ) :
    IsProbabilityMeasure (contAwgnSignalLaw c N₀) := by
  unfold contAwgnSignalLaw
  exact Measure.isProbabilityMeasure_map
    ((measurable_of_countable (fun a : Fin M ↦ c.observation a)).comp measurable_fst).aemeasurable

/-! ## §L1 — Single-shot converse wiring -/

private lemma count_eq_finset_sum_dirac (α : Type*) [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    (Measure.count : Measure α) = ∑ a : α, Measure.dirac a := by
  have h_one : ∀ a : α, (Measure.count : Measure α) {a} = 1 := fun a ↦
    Measure.count_singleton a
  have h_sum : Measure.sum (fun a : α ↦ Measure.dirac a)
      = (Measure.count : Measure α) := by
    have h := Measure.sum_smul_dirac (μ := (Measure.count : Measure α))
    simp_rw [h_one, one_smul] at h
    exact h
  rw [← h_sum, Measure.sum_fintype]

/-- The message marginal `(contAwgnConverseJoint c N₀).map Prod.fst` is uniform. -/
lemma contAwgnConverseJoint_map_fst {T W P : ℝ} {M : ℕ} [NeZero M]
    (c : ContAwgnCode T W P M) (N₀ : ℝ) :
    (contAwgnConverseJoint c N₀).map (Prod.fst : Fin M × (Fin c.k → ℝ) → Fin M)
      = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ • Measure.count := by
  unfold contAwgnConverseJoint
  rw [Measure.map_smul]
  have h_map_fst_meas : Measurable (Prod.fst : Fin M × (Fin c.k → ℝ) → Fin M) := measurable_fst
  rw [Measure.map_finset_sum (s := Finset.univ)
      (m := fun m ↦ (Measure.dirac m).prod
        (Measure.pi (fun i : Fin c.k ↦
          gaussianReal (c.observation m i) (N₀ / 2).toNNReal)))
      h_map_fst_meas.aemeasurable]
  have h_each : ∀ m : Fin M,
      ((Measure.dirac m).prod
          (Measure.pi (fun i : Fin c.k ↦
            gaussianReal (c.observation m i) (N₀ / 2).toNNReal))).map
        (Prod.fst : Fin M × (Fin c.k → ℝ) → Fin M) = Measure.dirac m := by
    intro m
    rw [Measure.map_fst_prod]
    have : Measure.pi (fun i : Fin c.k ↦ gaussianReal (c.observation m i) (N₀ / 2).toNNReal)
        (Set.univ : Set (Fin c.k → ℝ)) = 1 := measure_univ
    rw [this, one_smul]
  rw [Finset.sum_congr rfl (fun m _ ↦ h_each m)]
  rw [count_eq_finset_sum_dirac, Fintype.card_fin]

/-- The Fano error probability equals the ContAwgn average error `(c.averageError N₀).toReal`. -/
lemma contAwgn_errorProb_eq_averageError {T W P : ℝ} {M : ℕ} [NeZero M]
    (c : ContAwgnCode T W P M) (N₀ : ℝ) :
    InformationTheory.MeasureFano.errorProb
        (contAwgnConverseJoint c N₀)
        (Prod.fst : Fin M × (Fin c.k → ℝ) → Fin M)
        (Prod.snd : Fin M × (Fin c.k → ℝ) → Fin c.k → ℝ)
        c.decoder
      = (c.averageError N₀).toReal := by
  classical
  set S : Set (Fin M × (Fin c.k → ℝ)) := {ω | ω.1 ≠ c.decoder ω.2} with hS_def
  show (contAwgnConverseJoint c N₀).real S = (c.averageError N₀).toReal
  have hS_meas : MeasurableSet S := by
    have h_pred : Measurable (fun ω : Fin M × (Fin c.k → ℝ) ↦ (ω.1, c.decoder ω.2)) :=
      measurable_fst.prodMk (c.decoder_meas.comp measurable_snd)
    have h_eq_set : MeasurableSet {ω : Fin M × (Fin c.k → ℝ) | ω.1 = c.decoder ω.2} :=
      h_pred (measurableSet_eq_fun measurable_fst measurable_snd)
    exact h_eq_set.compl
  have h_mu_S : (contAwgnConverseJoint c N₀) S = c.averageError N₀ := by
    unfold contAwgnConverseJoint
    rw [Measure.smul_apply, Measure.finsetSum_apply _ _ S, smul_eq_mul]
    have h_each : ∀ m : Fin M,
        ((Measure.dirac m).prod
          (Measure.pi (fun i : Fin c.k ↦
            gaussianReal (c.observation m i) (N₀ / 2).toNNReal))) S
          = c.errorProbAt N₀ m := by
      intro m
      rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hS_meas]
      have h_preim : (Prod.mk m : (Fin c.k → ℝ) → Fin M × (Fin c.k → ℝ)) ⁻¹' S
          = {y : Fin c.k → ℝ | c.decoder y ≠ m} := by
        ext y; simp only [hS_def, Set.mem_preimage, Set.mem_setOf_eq]; exact ne_comm
      rw [h_preim]
      rfl
    rw [Finset.sum_congr rfl (fun m _ ↦ h_each m),
      ContAwgnCode.averageError, if_neg (NeZero.ne M)]
  rw [Measure.real, h_mu_S]

/-! ## §L3 — RV ↔ channel bridge -/

/-- The signal law as a mixture of Diracs `(1/M) ∑ₘ δ(observation m)`. -/
lemma contAwgnSignalLaw_eq_mixture {T W P : ℝ} {M : ℕ} [NeZero M]
    (c : ContAwgnCode T W P M) (N₀ : ℝ) :
    contAwgnSignalLaw c N₀
      = (M : ℝ≥0∞)⁻¹ • ∑ m : Fin M, Measure.dirac (c.observation m) := by
  classical
  unfold contAwgnSignalLaw contAwgnConverseJoint
  have h_meas_eval :
      Measurable (fun ω : Fin M × (Fin c.k → ℝ) ↦ c.observation ω.1) :=
    (measurable_of_countable (fun a : Fin M ↦ c.observation a)).comp measurable_fst
  rw [Measure.map_smul,
    Measure.map_finset_sum (s := Finset.univ)
      (m := fun m ↦ (Measure.dirac m).prod
        (Measure.pi (fun i : Fin c.k ↦ gaussianReal (c.observation m i) (N₀ / 2).toNNReal)))
      h_meas_eval.aemeasurable]
  congr 1
  refine Finset.sum_congr rfl (fun m _ ↦ ?_)
  have h_decomp : (fun ω : Fin M × (Fin c.k → ℝ) ↦ c.observation ω.1)
      = (fun a : Fin M ↦ c.observation a) ∘ Prod.fst := rfl
  rw [h_decomp,
    ← Measure.map_map (measurable_of_countable (fun a : Fin M ↦ c.observation a)) measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul,
    Measure.map_dirac' (measurable_of_countable (fun a : Fin M ↦ c.observation a)) m]

/-- The signal-vs-output pair law factors as `p_S ⊗ₘ W_chan`. -/
lemma contAwgnConverseJoint_map_pair_eq_compProd {T W P : ℝ} {M : ℕ} [NeZero M]
    (c : ContAwgnCode T W P M) (N₀ : ℝ) :
    (contAwgnConverseJoint c N₀).map (fun ω ↦ (c.observation ω.1, ω.2))
      = contAwgnSignalLaw c N₀ ⊗ₘ contAwgnConstChannel c.k (N₀ / 2).toNNReal := by
  classical
  set Nv : ℝ≥0 := (N₀ / 2).toNNReal with hNv
  -- per-summand `δ_a ⊗ₘ W_chan = (δ_a).prod (W_chan a)`.
  have h_dirac_compProd : ∀ a : Fin c.k → ℝ,
      (Measure.dirac a) ⊗ₘ (contAwgnConstChannel c.k Nv)
        = (Measure.dirac a).prod (contAwgnConstChannel c.k Nv a) := by
    intro a
    ext s hs
    rw [Measure.dirac_compProd_apply hs, Measure.dirac_prod,
      Measure.map_apply measurable_prodMk_left hs]
  -- RHS: p_S ⊗ₘ W_chan as a mixture.
  have h_rhs : contAwgnSignalLaw c N₀ ⊗ₘ (contAwgnConstChannel c.k Nv)
      = (M : ℝ≥0∞)⁻¹ • ∑ m : Fin M,
          (Measure.dirac (c.observation m)).prod
            (contAwgnConstChannel c.k Nv (c.observation m)) := by
    rw [contAwgnSignalLaw_eq_mixture c N₀,
      ← Measure.sum_fintype (fun m : Fin M ↦ Measure.dirac (c.observation m)),
      Measure.compProd_smul_left, Measure.compProd_sum_left, Measure.sum_fintype]
    congr 1
    exact Finset.sum_congr rfl (fun m _ ↦ h_dirac_compProd (c.observation m))
  -- LHS: joint mapped through `(observation ∘ fst, snd)` as the same mixture.
  have h_lhs : (contAwgnConverseJoint c N₀).map (fun ω ↦ (c.observation ω.1, ω.2))
      = (M : ℝ≥0∞)⁻¹ • ∑ m : Fin M,
          (Measure.dirac (c.observation m)).prod
            (contAwgnConstChannel c.k Nv (c.observation m)) := by
    unfold contAwgnConverseJoint
    have hf_meas :
        Measurable (fun ω : Fin M × (Fin c.k → ℝ) ↦ (c.observation ω.1, ω.2)) :=
      ((measurable_of_countable (fun a : Fin M ↦ c.observation a)).comp measurable_fst).prodMk
        measurable_snd
    rw [Measure.map_smul,
      Measure.map_finset_sum (s := Finset.univ)
        (m := fun m ↦ (Measure.dirac m).prod
          (Measure.pi (fun i : Fin c.k ↦ gaussianReal (c.observation m i) Nv)))
        hf_meas.aemeasurable]
    congr 1
    refine Finset.sum_congr rfl (fun m _ ↦ ?_)
    rw [Measure.dirac_prod, Measure.map_map hf_meas measurable_prodMk_left]
    have h_comp : (fun ω : Fin M × (Fin c.k → ℝ) ↦ (c.observation ω.1, ω.2))
          ∘ (Prod.mk m : (Fin c.k → ℝ) → Fin M × (Fin c.k → ℝ))
        = fun y : Fin c.k → ℝ ↦ (c.observation m, y) := rfl
    rw [h_comp, ← Measure.dirac_prod]
    rfl
  rw [h_lhs, h_rhs]

/-- The output distribution equals the `Prod.snd` marginal of the joint. -/
lemma contAwgn_outputDistribution_eq {T W P : ℝ} {M : ℕ} [NeZero M]
    (c : ContAwgnCode T W P M) (N₀ : ℝ) :
    outputDistribution (contAwgnSignalLaw c N₀) (contAwgnConstChannel c.k (N₀ / 2).toNNReal)
      = (contAwgnConverseJoint c N₀).map Prod.snd := by
  rw [show outputDistribution (contAwgnSignalLaw c N₀)
        (contAwgnConstChannel c.k (N₀ / 2).toNNReal)
        = (contAwgnSignalLaw c N₀ ⊗ₘ (contAwgnConstChannel c.k (N₀ / 2).toNNReal)).map Prod.snd
      from rfl]
  rw [← contAwgnConverseJoint_map_pair_eq_compProd c N₀]
  have hf_meas :
      Measurable (fun ω : Fin M × (Fin c.k → ℝ) ↦ (c.observation ω.1, ω.2)) :=
    ((measurable_of_countable (fun a : Fin M ↦ c.observation a)).comp measurable_fst).prodMk
      measurable_snd
  rw [Measure.map_map measurable_snd hf_meas]
  rfl

/-- `I(S; Y) = mutualInfoOfChannel p_S W_chan` for `S = observation ∘ W` and the constant-noise
parallel channel `W_chan`.
@audit:ok -/
lemma contAwgn_mi_S_eq_mutualInfoOfChannel {T W P : ℝ} {M : ℕ} [NeZero M]
    (c : ContAwgnCode T W P M) (N₀ : ℝ) :
    mutualInfo (contAwgnConverseJoint c N₀)
        (fun ω : Fin M × (Fin c.k → ℝ) ↦ c.observation ω.1)
        (Prod.snd : Fin M × (Fin c.k → ℝ) → Fin c.k → ℝ)
      = mutualInfoOfChannel (contAwgnSignalLaw c N₀)
          (contAwgnConstChannel c.k (N₀ / 2).toNNReal) := by
  unfold mutualInfo
  rw [mutualInfoOfChannel_def, jointDistribution_def,
    contAwgnConverseJoint_map_pair_eq_compProd c N₀]
  congr 1
  rw [show (contAwgnConverseJoint c N₀).map (fun ω ↦ c.observation ω.1)
        = contAwgnSignalLaw c N₀ from rfl,
    contAwgn_outputDistribution_eq c N₀]

/-! ## §L2 — Markov DPI `W → S → Y` -/

/-- Message-space marginal (A): the joint factors as `(uniform W) ⊗ₘ (W_chan.comap observation)`.
Signal-level analog of `AWGN.converseMarkov_marginalA`. -/
private theorem contAwgnConverseMarkov_marginalA {T W P : ℝ} {M : ℕ} [NeZero M]
    (c : ContAwgnCode T W P M) (N₀ : ℝ)
    (Wg : Kernel (Fin M) (Fin c.k → ℝ))
    (hWg_def : Wg = (contAwgnConstChannel c.k (N₀ / 2).toNNReal).comap
      (fun m : Fin M ↦ c.observation m) Measurable.of_discrete)
    (h_map_Xs : (contAwgnConverseJoint c N₀).map (Prod.fst : Fin M × (Fin c.k → ℝ) → Fin M)
      = ((M : ℝ≥0∞)⁻¹) • ∑ m : Fin M, Measure.dirac m) :
    contAwgnConverseJoint c N₀
      = ((contAwgnConverseJoint c N₀).map (Prod.fst : Fin M × (Fin c.k → ℝ) → Fin M)) ⊗ₘ Wg := by
  haveI : IsMarkovKernel Wg := by rw [hWg_def]; infer_instance
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [Measure.lintegral_compProd hf, h_map_Xs, lintegral_smul_measure,
    lintegral_finsetSum_measure]
  have hRHS_summand : ∀ m : Fin M,
      ∫⁻ a : Fin M, ∫⁻ y : Fin c.k → ℝ, f (a, y) ∂(Wg a) ∂(Measure.dirac m)
        = ∫⁻ y : Fin c.k → ℝ, f (m, y)
            ∂(Measure.pi (fun i : Fin c.k ↦
              gaussianReal (c.observation m i) (N₀ / 2).toNNReal)) := by
    intro m
    rw [lintegral_dirac, hWg_def]
    rfl
  simp_rw [hRHS_summand]
  rw [contAwgnConverseJoint, lintegral_smul_measure, lintegral_finsetSum_measure]
  have hLHS_summand : ∀ m : Fin M,
      ∫⁻ ω : Fin M × (Fin c.k → ℝ), f ω
          ∂((Measure.dirac m).prod
            (Measure.pi (fun i : Fin c.k ↦
              gaussianReal (c.observation m i) (N₀ / 2).toNNReal)))
        = ∫⁻ y : Fin c.k → ℝ, f (m, y)
            ∂(Measure.pi (fun i : Fin c.k ↦
              gaussianReal (c.observation m i) (N₀ / 2).toNNReal)) := by
    intro m
    rw [lintegral_prod _ hf.aemeasurable, lintegral_dirac]
  simp_rw [hLHS_summand]

/-- The Markov chain `W → observation ∘ W → Y` factorization for the ContAwgn joint. The
signal-level analog of `AWGN.awgnConverseMarkov_holds`: `observation` is the deterministic encoder,
so `Y` depends on `W` only through `S = observation ∘ W`.
@audit:ok -/
lemma contAwgnConverseMarkov_holds {T W P : ℝ} {M : ℕ} [NeZero M]
    (c : ContAwgnCode T W P M) (N₀ : ℝ) :
    IsMarkovChain (contAwgnConverseJoint c N₀)
      (Prod.fst : Fin M × (Fin c.k → ℝ) → Fin M)
      (fun ω : Fin M × (Fin c.k → ℝ) ↦ c.observation ω.1)
      (Prod.snd : Fin M × (Fin c.k → ℝ) → Fin c.k → ℝ) := by
  set μ : Measure (Fin M × (Fin c.k → ℝ)) := contAwgnConverseJoint c N₀ with hμ_def
  set Xs : Fin M × (Fin c.k → ℝ) → Fin M := Prod.fst with hXs_def
  set Zc : Fin M × (Fin c.k → ℝ) → (Fin c.k → ℝ) := fun ω ↦ c.observation ω.1 with hZc_def
  set Yo : Fin M × (Fin c.k → ℝ) → (Fin c.k → ℝ) := Prod.snd with hYo_def
  set Wch : Kernel (Fin c.k → ℝ) (Fin c.k → ℝ) :=
    contAwgnConstChannel c.k (N₀ / 2).toNNReal with hWch_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  have hXs_meas : Measurable Xs := measurable_fst
  have hg_meas : Measurable (fun m : Fin M ↦ c.observation m) := measurable_of_countable _
  have hZc_meas : Measurable Zc := by
    rw [hZc_def]; exact hg_meas.comp measurable_fst
  have hYo_meas : Measurable Yo := measurable_snd
  set Wg : Kernel (Fin M) (Fin c.k → ℝ) :=
    Wch.comap (fun m : Fin M ↦ c.observation m) hg_meas with hWg_def
  -- Marginal (A): `μ = (μ.map Xs) ⊗ₘ Wg`.
  have h_map_Xs : μ.map Xs
      = ((M : ℝ≥0∞)⁻¹) • ∑ m : Fin M, Measure.dirac m := by
    rw [hμ_def, hXs_def, contAwgnConverseJoint_map_fst, Fintype.card_fin,
      count_eq_finset_sum_dirac]
  have h_marginalA : μ = (μ.map Xs) ⊗ₘ Wg := by
    rw [hμ_def, hXs_def]
    exact contAwgnConverseMarkov_marginalA c N₀ Wg hWg_def
      (by rw [← hμ_def, ← hXs_def]; exact h_map_Xs)
  -- Linchpin pair law (already proven in-file): `μ.map (Zc, Yo) = (μ.map Zc) ⊗ₘ Wch`.
  have h_pair_eq : μ.map (fun ω ↦ (Zc ω, Yo ω)) = (μ.map Zc) ⊗ₘ Wch := by
    rw [hμ_def, hZc_def, hYo_def, hWch_def]
    exact contAwgnConverseJoint_map_pair_eq_compProd c N₀
  -- `condDistrib Yo Zc μ =ᵐ[μ.map Zc] Wch`.
  haveI : IsProbabilityMeasure (μ.map Zc) := Measure.isProbabilityMeasure_map hZc_meas.aemeasurable
  have hK_Y_eq : condDistrib Yo Zc μ =ᵐ[μ.map Zc] Wch :=
    condDistrib_ae_eq_of_measure_eq_compProd Zc hYo_meas.aemeasurable h_pair_eq
  unfold IsMarkovChain
  set K_X : Kernel (Fin c.k → ℝ) (Fin M) := condDistrib Xs Zc μ with hK_X_def
  have h_compProd_eq :
      (μ.map Zc) ⊗ₘ (K_X ×ₖ condDistrib Yo Zc μ) = (μ.map Zc) ⊗ₘ (K_X ×ₖ Wch) := by
    refine Measure.compProd_congr ?_
    filter_upwards [hK_Y_eq] with a ha
    ext s hs
    rw [Kernel.prod_apply, Kernel.prod_apply, ha]
  rw [h_compProd_eq]
  have h_LHS_meas : Measurable (fun ω ↦ (Zc ω, Xs ω, Yo ω)) :=
    hZc_meas.prodMk (hXs_meas.prodMk hYo_meas)
  have hKX_fold : (μ.map Zc) ⊗ₘ K_X = μ.map (fun ω ↦ (Zc ω, Xs ω)) :=
    compProd_map_condDistrib (μ := μ) (X := Zc) (Y := Xs) hXs_meas.aemeasurable
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [lintegral_map hf h_LHS_meas]
  rw [Measure.lintegral_compProd hf]
  have h_inner_split : ∀ z : Fin c.k → ℝ,
      ∫⁻ p : Fin M × (Fin c.k → ℝ), f (z, p.1, p.2) ∂((K_X ×ₖ Wch) z)
        = ∫⁻ x : Fin M, ∫⁻ y : Fin c.k → ℝ, f (z, x, y) ∂(Wch z) ∂(K_X z) := by
    intro z
    rw [Kernel.prod_apply]
    rw [lintegral_prod (fun p : Fin M × (Fin c.k → ℝ) ↦ f (z, p.1, p.2))
      (hf.comp (measurable_const.prodMk
        (measurable_fst.prodMk measurable_snd))).aemeasurable]
  simp_rw [h_inner_split]
  set G : (Fin c.k → ℝ) × Fin M → ℝ≥0∞ :=
    fun p ↦ ∫⁻ y : Fin c.k → ℝ, f (p.1, p.2, y) ∂(Wch p.1) with hG_def
  have hG_meas : Measurable G := by
    let K' : Kernel ((Fin c.k → ℝ) × Fin M) (Fin c.k → ℝ) :=
      Wch.comap (Prod.fst : (Fin c.k → ℝ) × Fin M → (Fin c.k → ℝ)) measurable_fst
    have h_eq_K' : G = fun p : (Fin c.k → ℝ) × Fin M ↦
        ∫⁻ y : Fin c.k → ℝ, f (p.1, p.2, y) ∂(K' p) := by
      funext p; simp [G, K', Kernel.comap_apply]
    rw [h_eq_K']
    exact Measurable.lintegral_kernel_prod_right' (κ := K')
      (f := fun pp : ((Fin c.k → ℝ) × Fin M) × (Fin c.k → ℝ) ↦ f (pp.1.1, pp.1.2, pp.2))
      (hf.comp (((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))
  have h_RHS_is_G : ∀ z : Fin c.k → ℝ, ∀ x : Fin M,
      ∫⁻ y : Fin c.k → ℝ, f (z, x, y) ∂(Wch z) = G (z, x) := fun _ _ ↦ rfl
  simp_rw [h_RHS_is_G]
  rw [← Measure.lintegral_compProd hG_meas, hKX_fold]
  rw [lintegral_map hG_meas (hZc_meas.prodMk hXs_meas)]
  rw [← hμ_def]
  have h_reduce : ∀ H : Fin M × (Fin c.k → ℝ) → ℝ≥0∞, Measurable H →
      ∫⁻ ω, H ω ∂μ
        = ∫⁻ a : Fin M, ∫⁻ y : Fin c.k → ℝ, H (a, y) ∂(Wg a) ∂(μ.map Xs) := by
    intro H hH
    conv_lhs => rw [h_marginalA]
    rw [Measure.lintegral_compProd hH]
  rw [h_reduce (fun ω ↦ f (Zc ω, Xs ω, Yo ω)) (hf.comp h_LHS_meas),
    h_reduce (fun ω ↦ G (Zc ω, Xs ω)) (hG_meas.comp (hZc_meas.prodMk hXs_meas))]
  refine lintegral_congr fun a ↦ ?_
  have hWg_eq : Wg a = Wch (c.observation a) := by rw [hWg_def, Kernel.comap_apply]
  haveI : IsProbabilityMeasure (Wg a) := by rw [hWg_eq]; infer_instance
  have hRHS_eval : (fun y : Fin c.k → ℝ ↦ G (Zc (a, y), Xs (a, y)))
      = (fun _ : Fin c.k → ℝ ↦ ∫⁻ y' : Fin c.k → ℝ, f (c.observation a, a, y') ∂(Wg a)) := by
    funext y
    show G (c.observation a, a) = _
    rw [hG_def, hWg_eq]
  rw [hRHS_eval, lintegral_const, measure_univ, mul_one]

/-! ## §L4 — Power-constraint set membership (Bessel) -/

/-- Bessel's inequality against the orthonormal test family: the total observed energy of any
codeword is capped by its whole-line `L²` energy, hence by the power budget `T·P`.
@audit:ok -/
lemma contAwgn_sum_observation_sq_le {T W P : ℝ} {M : ℕ}
    (c : ContAwgnCode T W P M) (m : Fin M) :
    ∑ i : Fin c.k, (c.observation m i) ^ 2 ≤ T * P := by
  classical
  set f : Lp ℝ 2 volume := (c.encoder_memLp m).toLp (c.encoder m) with hf_def
  set φ : Fin c.k → Lp ℝ 2 volume := fun i => (c.testFn_memLp i).toLp (c.testFn i) with hφ_def
  have hinner : ∀ (i : Fin c.k) (g : Lp ℝ 2 volume),
      (inner ℝ (φ i) g : ℝ) = ∫ t, g t * c.testFn i t := by
    intro i g
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (c.testFn_memLp i)] with t ht
    simp only [hφ_def, ht, RCLike.inner_apply, conj_trivial]
  have hortho : Orthonormal ℝ φ := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hinner i (φ j)]
    have : (∫ t, (φ j : ℝ → ℝ) t * c.testFn i t) = ∫ t, c.testFn j t * c.testFn i t := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (c.testFn_memLp j)] with t ht
      simp only [hφ_def, ht]
    rw [this, c.testFn_orthonormal j i]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hbessel := hortho.sum_inner_products_le (x := f) (s := Finset.univ)
  have hobs : ∀ i : Fin c.k, (inner ℝ (φ i) f : ℝ) = c.observation m i := by
    intro i
    rw [hinner i f]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (c.encoder_memLp m)] with t ht
    simp only [hf_def, ht]
  have hnorm : ‖f‖ ^ 2 = ∫ t, (c.encoder m t) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (c.encoder_memLp m)] with t ht
    simp only [hf_def, ht, RCLike.inner_apply, conj_trivial, sq]
  calc ∑ i : Fin c.k, (c.observation m i) ^ 2
      = ∑ i : Fin c.k, ‖(inner ℝ (φ i) f : ℝ)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hobs i, Real.norm_eq_abs, sq_abs]
    _ ≤ ‖f‖ ^ 2 := hbessel
    _ = ∫ t, (c.encoder m t) ^ 2 := hnorm
    _ ≤ T * P := c.encoder_power m

/-- The signal law lies in the parallel power constraint set with budget `T·P`. -/
lemma contAwgn_signalLaw_mem_constraint {T W P : ℝ} {M : ℕ} [NeZero M]
    (c : ContAwgnCode T W P M) (N₀ : ℝ) (hTP : 0 ≤ T * P) :
    contAwgnSignalLaw c N₀ ∈ parallelGaussianPowerConstraintSet (T * P) := by
  classical
  refine ⟨inferInstance, ?_⟩
  have hobs_meas : Measurable (fun m : Fin M ↦ c.observation m) := measurable_of_countable _
  have h_law : contAwgnSignalLaw c N₀
      = ((M : ℝ≥0∞)⁻¹ • Measure.count).map (fun m : Fin M ↦ c.observation m) := by
    unfold contAwgnSignalLaw
    rw [show (fun ω : Fin M × (Fin c.k → ℝ) ↦ c.observation ω.1)
          = (fun m : Fin M ↦ c.observation m) ∘ Prod.fst from rfl,
      ← Measure.map_map hobs_meas measurable_fst, contAwgnConverseJoint_map_fst,
      Fintype.card_fin]
  have h_coord : ∀ i : Fin c.k,
      ∫⁻ x : Fin c.k → ℝ, ENNReal.ofReal ((x i) ^ 2) ∂(contAwgnSignalLaw c N₀)
        = (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, ENNReal.ofReal ((c.observation m i) ^ 2) := by
    intro i
    rw [h_law, lintegral_map (by fun_prop) hobs_meas, lintegral_smul_measure, lintegral_count,
      tsum_fintype, smul_eq_mul]
  calc ∑ i : Fin c.k, ∫⁻ x : Fin c.k → ℝ, ENNReal.ofReal ((x i) ^ 2)
          ∂(contAwgnSignalLaw c N₀)
      = ∑ i : Fin c.k,
          (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, ENNReal.ofReal ((c.observation m i) ^ 2) :=
        Finset.sum_congr rfl (fun i _ ↦ h_coord i)
    _ = (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, ∑ i : Fin c.k, ENNReal.ofReal ((c.observation m i) ^ 2) := by
        rw [← Finset.mul_sum]; congr 1; rw [Finset.sum_comm]
    _ = (M : ℝ≥0∞)⁻¹ *
          ∑ m : Fin M, ENNReal.ofReal (∑ i : Fin c.k, (c.observation m i) ^ 2) := by
        congr 1
        refine Finset.sum_congr rfl (fun m _ ↦ ?_)
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ sq_nonneg _)]
    _ ≤ (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, ENNReal.ofReal (T * P) := by
        gcongr with m
        exact contAwgn_sum_observation_sq_le c m
    _ = ENNReal.ofReal (T * P) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel (by exact_mod_cast NeZero.ne M) (ENNReal.natCast_ne_top M),
          one_mul]

/-! ## §L5 — MI-finiteness -/

/-- `I(W; Y) ≠ ∞` on the ContAwgn converse joint. Reduces to the discrete AWGN converse
finiteness `AWGN.awgnConverseJoint_mutualInfo_ne_top` by identifying `contAwgnConverseJoint` with
`AWGN.awgnConverseJoint` at encoder `= observation`, `N = (N₀/2).toNNReal`. The identification is
definitional (`awgnChannel x N = gaussianReal x N`, `Fintype.card (Fin M) = M`); the discrete
finiteness needs only `N ≠ 0`, so the power value `T·P` is irrelevant to the reduction. -/
lemma contAwgn_mi_W_ne_top {T W P : ℝ} {M : ℕ} [NeZero M]
    (c : ContAwgnCode T W P M) {N₀ : ℝ} (hN₀ : 0 < N₀) :
    mutualInfo (contAwgnConverseJoint c N₀)
        (Prod.fst : Fin M × (Fin c.k → ℝ) → Fin M)
        (Prod.snd : Fin M × (Fin c.k → ℝ) → Fin c.k → ℝ) ≠ ∞ := by
  classical
  set Nv : ℝ≥0 := (N₀ / 2).toNNReal with hNv
  have hNv_ne : Nv ≠ 0 := by
    rw [hNv, ne_eq, Real.toNNReal_eq_zero, not_le]; positivity
  have h_meas : AWGN.IsAwgnChannelMeasurable Nv := AWGN.isAwgnChannelMeasurable Nv
  haveI : Nonempty (Fin M) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩⟩
  have hTP : 0 ≤ T * P :=
    le_trans (Finset.sum_nonneg (fun i _ ↦ sq_nonneg _))
      (contAwgn_sum_observation_sq_le c (Classical.arbitrary (Fin M)))
  -- the discrete code whose encoder IS the observation map; the power value is irrelevant here.
  let ac : AWGN.AwgnCode M c.k (T * P) :=
    { encoder := fun m ↦ c.observation m
      decoder := c.decoder
      decoder_meas := c.decoder_meas
      power_constraint := fun m ↦ by
        rcases Nat.eq_zero_or_pos c.k with hk | hk
        · haveI : IsEmpty (Fin c.k) := hk ▸ inferInstance
          simp only [Finset.univ_eq_empty, Finset.sum_empty]
          exact mul_nonneg (Nat.cast_nonneg _) hTP
        · calc ∑ i : Fin c.k, (c.observation m i) ^ 2 ≤ T * P :=
                contAwgn_sum_observation_sq_le c m
            _ ≤ (c.k : ℝ) * (T * P) :=
                le_mul_of_one_le_left hTP (by exact_mod_cast hk) }
  have h_eq : contAwgnConverseJoint c N₀ = AWGN.awgnConverseJoint h_meas ac := by
    unfold contAwgnConverseJoint AWGN.awgnConverseJoint
    simp only [AWGN.awgnChannel_apply, Fintype.card_fin, hNv]
    rfl
  rw [h_eq]
  exact AWGN.awgnConverseJoint_mutualInfo_ne_top hNv_ne h_meas ac

/-! ## §C3 — the operational parallel-Gaussian converse -/

/-- **C3: operational parallel-Gaussian converse** (equal-noise form; gains `νᵢ` enter in C4).
For a `ContAwgnCode` with `2 ≤ M` and average error `Pe`, the log message count is bounded by
the per-coordinate parallel-Gaussian sum plus the Fano terms. -/
theorem contAwgn_operational_converse {T W P N₀ : ℝ} {M : ℕ}
    (hN₀ : 0 < N₀) (hP : 0 ≤ P) (hM : 2 ≤ M)
    (c : ContAwgnCode T W P M)
    (Pe : ℝ) (hPe : Pe = (c.averageError N₀).toReal) :
    ∃ P' : Fin c.k → ℝ, (∀ i, 0 ≤ P' i) ∧ (∑ i, P' i ≤ T * P) ∧
      Real.log M ≤ (∑ i : Fin c.k, (1/2) * Real.log (1 + P' i / (N₀ / 2)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  classical
  haveI : NeZero M := ⟨by omega⟩
  haveI : StandardBorelSpace (Fin c.k → ℝ) := inferInstance
  set joint := contAwgnConverseJoint c N₀ with hjoint
  set S : Fin M × (Fin c.k → ℝ) → (Fin c.k → ℝ) := fun ω ↦ c.observation ω.1 with hS
  have hSmeas : Measurable S := by
    rw [hS]; exact (measurable_of_countable (fun m : Fin M ↦ c.observation m)).comp measurable_fst
  have hfst : Measurable (Prod.fst : Fin M × (Fin c.k → ℝ) → Fin M) := measurable_fst
  have hsnd : Measurable (Prod.snd : Fin M × (Fin c.k → ℝ) → Fin c.k → ℝ) := measurable_snd
  -- `0 ≤ T·P` from the (nonempty) power constraint.
  have hTP : 0 ≤ T * P :=
    le_trans (integral_nonneg (fun t ↦ sq_nonneg _)) (c.encoder_power ⟨0, by omega⟩)
  -- `I(W; Y) ≠ ∞` (L5).
  have hMI_finite : mutualInfo joint Prod.fst Prod.snd ≠ ∞ := contAwgn_mi_W_ne_top c hN₀
  -- L1 : single-shot converse.
  have h1 : Real.log M ≤ (mutualInfo joint Prod.fst Prod.snd).toReal
      + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
    have hcard : 2 ≤ Fintype.card (Fin M) := by simpa [Fintype.card_fin] using hM
    have h_shannon := InformationTheory.Shannon.shannon_converse_single_shot
      (μ := joint) (Msg := Prod.fst) (Yo := Prod.snd) (decoder := c.decoder)
      hfst hsnd c.decoder_meas (contAwgnConverseJoint_map_fst c N₀) hcard hMI_finite
    rw [contAwgn_errorProb_eq_averageError, ← hPe] at h_shannon
    simpa only [Fintype.card_fin] using h_shannon
  -- L2 : Markov DPI `W → S → Y`.
  have h2 : mutualInfo joint Prod.fst Prod.snd ≤ mutualInfo joint S Prod.snd :=
    mutualInfo_le_of_markov joint Prod.fst S Prod.snd hfst hSmeas hsnd
      (contAwgnConverseMarkov_holds c N₀)
  -- L3 : RV ↔ channel bridge.
  have h3 : mutualInfo joint S Prod.snd
      = mutualInfoOfChannel (contAwgnSignalLaw c N₀)
          (contAwgnConstChannel c.k (N₀ / 2).toNNReal) :=
    contAwgn_mi_S_eq_mutualInfoOfChannel c N₀
  -- `I(S; Y) ≤ I(W; Y)` (post-processing), hence `mutualInfoOfChannel ≠ ∞`.
  have hpost : mutualInfo joint S Prod.snd ≤ mutualInfo joint Prod.fst Prod.snd := by
    rw [mutualInfo_comm joint S Prod.snd hSmeas hsnd,
      mutualInfo_comm joint Prod.fst Prod.snd hfst hsnd]
    exact mutualInfo_le_of_postprocess joint Prod.snd Prod.fst hsnd hfst
      (f := fun m : Fin M ↦ c.observation m) (measurable_of_countable _)
  have hSfin : mutualInfoOfChannel (contAwgnSignalLaw c N₀)
      (contAwgnConstChannel c.k (N₀ / 2).toNNReal) ≠ ∞ :=
    h3 ▸ ne_top_of_le_ne_top hMI_finite hpost
  -- L4 : parallel MI bound.
  have hN_ne : ∀ i : Fin c.k, (((fun _ : Fin c.k ↦ (N₀ / 2).toNNReal) i : ℝ)) ≠ 0 := by
    intro i
    rw [Real.coe_toNNReal _ (by positivity)]
    exact (by positivity : (0 : ℝ) < N₀ / 2).ne'
  obtain ⟨P', hP'nonneg, hP'sum, hP'bound⟩ :=
    parallel_per_input_mi_le_sum (T * P) hTP (fun _ ↦ (N₀ / 2).toNNReal) hN_ne
      (contAwgn_isParallelAwgnChannelMeasurable _)
      (contAwgn_isParallelGaussianKernelMeasurable _)
      (contAwgnSignalLaw c N₀) (contAwgn_signalLaw_mem_constraint c N₀ hTP)
  refine ⟨P', hP'nonneg, hP'sum, ?_⟩
  -- fold the channel term and rewrite the noise coercion `((N₀/2).toNNReal : ℝ) = N₀/2`.
  have hbound2 : (mutualInfoOfChannel (contAwgnSignalLaw c N₀)
        (contAwgnConstChannel c.k (N₀ / 2).toNNReal)).toReal
      ≤ ∑ i : Fin c.k, (1 / 2) * Real.log (1 + P' i / ((N₀ / 2).toNNReal : ℝ)) := hP'bound
  rw [Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ N₀ / 2)] at hbound2
  -- assemble in ℝ.
  have h23 : mutualInfo joint Prod.fst Prod.snd
      ≤ mutualInfoOfChannel (contAwgnSignalLaw c N₀)
          (contAwgnConstChannel c.k (N₀ / 2).toNNReal) := h3 ▸ h2
  have h23real : (mutualInfo joint Prod.fst Prod.snd).toReal
      ≤ (mutualInfoOfChannel (contAwgnSignalLaw c N₀)
          (contAwgnConstChannel c.k (N₀ / 2).toNNReal)).toReal :=
    ENNReal.toReal_mono hSfin h23
  linarith

end InformationTheory.Shannon.ShannonHartley
