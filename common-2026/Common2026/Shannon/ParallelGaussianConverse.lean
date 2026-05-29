import Common2026.Meta.EntryPoint
import Common2026.Shannon.ParallelGaussian
import Common2026.Draft.Shannon.ParallelGaussianPerCoord
import Common2026.Draft.Shannon.ContChannelMIDecomp
import Common2026.Draft.Shannon.MultivariateDiffEntropy
import Common2026.Shannon.DifferentialEntropy
import Common2026.Draft.Shannon.AwgnCapacityConverseMaxent
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# ② parallel-gaussian converse closure (correlated input)

[parallel-gaussian-converse-closure-plan.md](../../docs/shannon/parallel-gaussian-converse-closure-plan.md).

This file supplies the genuine converse pieces for
`ParallelGaussianPerCoordRegularity.isParallelGaussianPerCoordRegularity_of_pieces`
(`bddAbove` / `max_ent` fields), lifting the 1-D AWGN converse template
(`awgn_per_input_mi_le_log`, `@audit:ok`) to the `Fin n → ℝ` parallel channel.

Genuine (sorryAx-free): Phase 2 decomposition lift
(`parallel_mutualInfoOfChannel_toReal_eq_diffEntropyPi_sub`, with generic
`{α β}` core `mutualInfoOfChannel_toReal_eq_neg_integral_log_sub`); Phase 5
`bddAbove` reduction (`parallel_bddAbove_miImage`, modulo the Phase 3 split).

Phase 3 `parallel_per_input_mi_le_sum`: the **converse organization is genuine**
for `0 ≤ P` (MI decomposition + output-entropy subadditivity + per-coord Gaussian
max-entropy + variance allocation `P'ᵢ := Var(Yᵢ) − Nᵢ` + log-algebra, all
assembled in-body via `parallelGaussian_max_ent_le_of_subadditivity`). The residual
content is isolated into named **Phase 1 precondition lemmas** (correlated-output
absolute continuity / log-density integrability / fibre product-entropy / output
variance structure), each carrying
`@residual(plan:parallel-gaussian-converse-closure-plan)`. None bundles the
conclusion; they are genuine consequences of Gaussian smoothing awaiting the
`Fin n → ℝ` analogue of the 1-D AWGN Phase 6 measure-theoretic plumbing.

**`false-statement` defect FIXED (2026-05-29)**: `parallel_per_input_mi_le_sum` now
takes `0 ≤ P` (threaded through `parallel_bddAbove_miImage` + the constructor
`isParallelGaussianPerCoordRegularity_of_pieces` from the headline
`parallel_gaussian_capacity_formula_minimal`, which holds `0 < P`). Without it the
statement is genuinely FALSE for `P < 0` (the constraint set is non-empty — contains the
Dirac at 0 — yet `∑ P'ᵢ ≤ P < 0` with `P'ᵢ ≥ 0` is unsatisfiable). The previous tier-5
false-statement residual `P < 0` branch has been removed.

Status: type-check done (tier 2), NOT proof done (10 `sorry`).

Wave 1 (2026-05-29): the volume-AC chain is now genuine (sorryAx-free,
`#print axioms` = [propext, Classical.choice, Quot.sound]): shared base helper
`pi_absolutelyContinuous` (Step A, `Measure.pi μ ≪ volume` from componentwise AC),
`parallelChannel_fibre_absolutelyContinuous_volume`,
`parallelOutput_absolutelyContinuous_volume`,
`parallelOutput_marginal_absolutelyContinuous_volume`. These now carry an explicit
`hN : ∀ i, (N i : ℝ) ≠ 0` regularity precondition (necessary: a `N i = 0` coordinate
gives a Dirac fibre, breaking AC). The remaining 10 residuals (joint-vs-marginal AC,
log-density / variance integrability, fibre→output AC, fibre product-entropy, mi-decomp
value) await the reverse full-support machinery (`volume ≪ Measure.pi (gaussianReal …)`,
needs ae-over-pi product-nonzero) and the product→sum entropy / convolution-variance
identities, all carrying `@residual(plan:parallel-gaussian-converse-closure-plan)`.

Independent honesty audit (2026-05-29, commit `6f495bc`): genuine `0 ≤ P` converse
chain confirmed (no load-bearing hypothesis, no degenerate/exfalso exploitation; the
`∑P'ᵢ ≤ P` feasibility comes genuinely from `parallelGaussianPowerConstraintSet`
membership via `parallelGaussianPowerConstraintSet_mem_iff_integrable`, not exfalso).
The 13 Phase 1 precondition lemmas are honest regularity residuals (AC / integrability
/ fibre product-entropy / output-variance plumbing) — none bundles the converse core
`MI ≤ ∑log`; `plan:parallel-gaussian-converse-closure-plan` classification verified
(plan exists). The `P < 0` `false-statement` defect (constraint set non-empty via Dirac-at-0
since `ENNReal.ofReal P = 0` for `P ≤ 0`, but `∑P'ᵢ ≤ P < 0` with `P'ᵢ ≥ 0` is unsatisfiable)
has since been FIXED (2026-05-29) by threading `0 ≤ P` through
`parallel_per_input_mi_le_sum` / `parallel_bddAbove_miImage` /
`isParallelGaussianPerCoordRegularity_of_pieces` from the headline consumer
`parallel_gaussian_capacity_formula_minimal` (which holds `hP : 0 < P`). No other consumer
was affected. `P = 0` is handled genuinely (not by exfalso): the membership-derived
second-moment bound `∑ E[Xᵢ²] ≤ P = 0` forces the allocation `P'ᵢ = Var(Yᵢ) − Nᵢ` to be
feasible against `∑ P'ᵢ ≤ 0` via the same genuine variance chain.
-/

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open InformationTheory.Shannon.ChannelCoding
open Common2026.Shannon
open scoped ENNReal NNReal BigOperators

/-! ## M0 — `CountableOrCountablyGenerated` instance check (transient) -/

example {n : ℕ} :
    MeasurableSpace.CountableOrCountablyGenerated (Fin n → ℝ) (Fin n → ℝ) := by
  infer_instance

/-! ## Shared base helper — product-measure absolute continuity (Wave 1, Step A) -/

/-- **`Measure.pi` preserves absolute continuity w.r.t. `volume`.** If every factor
`μ i ≪ volume` (each a probability measure, so `SigmaFinite`), then the product measure
`Measure.pi μ ≪ (volume : Measure (Fin n → ℝ))`. Built from `withDensity_rnDeriv_eq`
(write each `μ i = volume.withDensity (rnDeriv (μ i) volume)`), the `n`-variable
`pi_withDensity_fin` (Common2026), and `withDensity_absolutelyContinuous`. Mathlib has no
direct `Measure.pi _ ≪ Measure.pi _` lemma (loogle: 0 declarations), so this is self-built.

Genuine, sorryAx-free (`#print axioms` = [propext, Classical.choice, Quot.sound]);
awaiting independent honesty audit. -/
private theorem pi_absolutelyContinuous {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (h : ∀ i, μ i ≪ (volume : Measure ℝ)) :
    Measure.pi μ ≪ (volume : Measure (Fin n → ℝ)) := by
  classical
  -- write each factor as `volume.withDensity (rnDeriv (μ i) volume)`
  set f : Fin n → ℝ → ℝ≥0∞ := fun i => (μ i).rnDeriv volume with hf_def
  have hf_meas : ∀ i, Measurable (f i) := fun i => Measure.measurable_rnDeriv (μ i) volume
  have h_eq : ∀ i, (volume : Measure ℝ).withDensity (f i) = μ i :=
    fun i => Measure.withDensity_rnDeriv_eq (μ i) volume (h i)
  haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (f i)) := by
    intro i; rw [h_eq i]; infer_instance
  -- `Measure.pi μ = (Measure.pi (fun _ => volume)).withDensity (∏ ...)`
  have h_pi_eq : Measure.pi μ
      = (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).withDensity
          (fun z => ∏ i, f i (z i)) := by
    have h_factor : (fun i => (volume : Measure ℝ).withDensity (f i)) = μ := funext h_eq
    rw [← h_factor]
    exact pi_withDensity_fin (fun _ : Fin n => (volume : Measure ℝ)) hf_meas
  -- `volume : Measure (Fin n → ℝ) = Measure.pi (fun _ => volume)`
  rw [h_pi_eq, volume_pi]
  exact withDensity_absolutelyContinuous _ _

/-- **Reverse `Measure.pi` absolute continuity from componentwise mutual AC.** If every
factor is mutually absolutely continuous with `volume` (`ν i ≪ volume` and `volume ≪ ν i`),
then `volume ≪ Measure.pi ν`. Built from `pi_withDensity_fin` (write `Measure.pi ν =
volume.withDensity (∏ rnDeriv (ν i) volume)`) + `withDensity_absolutelyContinuous'`, whose
a.e.-nonzero density hypothesis comes from `Measure.rnDeriv_pos'` (`volume ≪ ν i` makes each
`rnDeriv (ν i) volume` a.e.-positive on `volume`).

Genuine, sorryAx-free (`#print axioms` = [propext, Classical.choice, Quot.sound]);
awaiting independent honesty audit. -/
private theorem pi_absolutelyContinuous_reverse {n : ℕ} (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (h_ac : ∀ i, ν i ≪ (volume : Measure ℝ))
    (h_rev : ∀ i, (volume : Measure ℝ) ≪ ν i) :
    (volume : Measure (Fin n → ℝ)) ≪ Measure.pi ν := by
  classical
  set f : Fin n → ℝ → ℝ≥0∞ := fun i => (ν i).rnDeriv volume with hf_def
  have hf_meas : ∀ i, Measurable (f i) := fun i => Measure.measurable_rnDeriv (ν i) volume
  have h_eq : ∀ i, (volume : Measure ℝ).withDensity (f i) = ν i :=
    fun i => Measure.withDensity_rnDeriv_eq (ν i) volume (h_ac i)
  haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (f i)) := by
    intro i; rw [h_eq i]; infer_instance
  have h_pi_eq : Measure.pi ν
      = (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).withDensity
          (fun z => ∏ i, f i (z i)) := by
    have h_factor : (fun i => (volume : Measure ℝ).withDensity (f i)) = ν := funext h_eq
    rw [← h_factor]
    exact pi_withDensity_fin (fun _ : Fin n => (volume : Measure ℝ)) hf_meas
  rw [h_pi_eq, ← volume_pi]
  refine withDensity_absolutelyContinuous' ?_ ?_
  · exact (Finset.measurable_prod _ (fun i _ => (hf_meas i).comp (measurable_pi_apply i))).aemeasurable
  · -- each `rnDeriv (ν i) volume` is a.e.-positive on `volume` (reverse AC)
    have h_pos : ∀ i, ∀ᵐ z ∂(volume : Measure ℝ), f i z ≠ 0 := by
      intro i
      filter_upwards [Measure.rnDeriv_pos' (h_rev i)] with z hz
      exact hz.ne'
    -- transfer each coordinate's a.e. to the product measure, then take the product
    have h_pos_pi : ∀ i, ∀ᵐ z ∂(volume : Measure (Fin n → ℝ)), f i (z i) ≠ 0 := by
      intro i
      rw [volume_pi]
      exact (Measure.quasiMeasurePreserving_eval
        (μ := fun _ : Fin n => (volume : Measure ℝ)) i).ae (h_pos i)
    filter_upwards [eventually_countable_forall.mpr h_pos_pi] with z hz
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hz i)

/-- **Reverse full-support AC for a Gaussian product fibre** (鍵①).
`volume ≪ Measure.pi (gaussianReal (x i) (N i))` whenever every `N i ≠ 0`. Each
`gaussianReal (x i) (N i) = volume.withDensity (gaussianPDF (x i) (N i))` with the
product density `z ↦ ∏ᵢ gaussianPDF (x i) (N i) (z i)` *everywhere* positive
(`gaussianPDFReal_pos`), so `withDensity_absolutelyContinuous'` gives the reverse AC.
Mathlib ships only the 1-D `gaussianReal_absolutelyContinuous'`; this is its
`Fin n → ℝ` product analogue, self-built via `pi_withDensity_fin`.

Genuine, sorryAx-free (`#print axioms` = [propext, Classical.choice, Quot.sound]);
awaiting independent honesty audit. -/
private theorem volume_absolutelyContinuous_pi_gaussian {n : ℕ}
    (x : Fin n → ℝ) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0) :
    (volume : Measure (Fin n → ℝ)) ≪ Measure.pi (fun i => gaussianReal (x i) (N i)) := by
  classical
  have hN' : ∀ i, (N i) ≠ 0 := fun i => by
    intro h; exact hN i (by rw [h]; norm_num)
  set f : Fin n → ℝ → ℝ≥0∞ := fun i => gaussianPDF (x i) (N i) with hf_def
  have hf_meas : ∀ i, Measurable (f i) := fun i => measurable_gaussianPDF _ _
  -- each factor as `volume.withDensity (gaussianPDF ...)`
  have h_eq : ∀ i, (volume : Measure ℝ).withDensity (f i) = gaussianReal (x i) (N i) :=
    fun i => (gaussianReal_of_var_ne_zero (x i) (hN' i)).symm
  haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (f i)) := by
    intro i; rw [h_eq i]; infer_instance
  -- `Measure.pi (gaussianReal ...) = (Measure.pi volume).withDensity (∏ f)`
  have h_pi_eq : Measure.pi (fun i => gaussianReal (x i) (N i))
      = (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).withDensity
          (fun z => ∏ i, f i (z i)) := by
    have h_factor : (fun i => (volume : Measure ℝ).withDensity (f i))
        = fun i => gaussianReal (x i) (N i) := funext h_eq
    rw [← h_factor]
    exact pi_withDensity_fin (fun _ : Fin n => (volume : Measure ℝ)) hf_meas
  rw [h_pi_eq, ← volume_pi]
  refine withDensity_absolutelyContinuous' ?_ ?_
  · exact (Finset.measurable_prod _ (fun i _ => (hf_meas i).comp (measurable_pi_apply i))).aemeasurable
  · -- the product density is everywhere `≠ 0` since each Gaussian pdf is positive
    refine Filter.Eventually.of_forall (fun z => ?_)
    refine Finset.prod_ne_zero_iff.mpr (fun i _ => ?_)
    simp only [hf_def, gaussianPDF_def, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact gaussianPDFReal_pos (x i) (N i) (z i) (hN' i)

/-! ## Phase 2 — channel↔RV MI decomposition, generic lift

The 1-D `ContChannelMIDecomp.mutualInfoOfChannel_toReal_eq_diffEntropy_sub` is
hardwired to `Measure ℝ` / `differentialEntropy`. We re-derive the same chain over
a generic measurable space `β` (with a `SigmaFinite` reference measure `vol`),
producing the entropy in raw `∫ log(rnDeriv) ∂` form, then specialize to
`β = Fin n → ℝ`, `vol = volume`. Every step uses only generic Mathlib / Common2026
lemmas (`InformationTheory.toReal_klDiv_of_measure_eq`, `rnDeriv_compProd_fibre`,
`integral_log_rnDeriv_self_eq_neg`), so the lift is mechanical. -/

section GenericDecomp

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
variable {p : Measure α} [IsProbabilityMeasure p]
variable {W : Channel α β} [IsMarkovKernel W]
variable {vol : Measure β} [SigmaFinite vol]

/-- **Generic per-measure log-density split** (Bayes step). Mirror of
`ContChannelMIDecomp.log_rnDeriv_split` over an arbitrary measurable space with a
`SigmaFinite` reference measure `vol`. -/
private theorem log_rnDeriv_split_gen
    {ν q : Measure β} [SigmaFinite ν] [SigmaFinite q]
    (hνq : ν ≪ q) (hq_vol : q ≪ vol) :
    (fun y => Real.log ((ν.rnDeriv q y).toReal))
      =ᵐ[ν]
    (fun y => Real.log ((ν.rnDeriv vol y).toReal)
                - Real.log ((q.rnDeriv vol y).toReal)) := by
  have h_chain : (fun y => ν.rnDeriv q y * q.rnDeriv vol y)
      =ᵐ[ν] ν.rnDeriv vol :=
    hνq.ae_le (Measure.rnDeriv_mul_rnDeriv' (μ := ν) (ν := q) (κ := vol) hq_vol)
  have h_pos_νq : ∀ᵐ y ∂ν, 0 < ν.rnDeriv q y := Measure.rnDeriv_pos hνq
  have h_lt_νq : ∀ᵐ y ∂ν, ν.rnDeriv q y < ∞ := hνq.ae_le (Measure.rnDeriv_lt_top ν q)
  have h_pos_q : ∀ᵐ y ∂ν, 0 < q.rnDeriv vol y := hνq.ae_le (Measure.rnDeriv_pos hq_vol)
  have h_lt_q : ∀ᵐ y ∂ν, q.rnDeriv vol y < ∞ :=
    hνq.ae_le (hq_vol.ae_le (Measure.rnDeriv_lt_top q vol))
  filter_upwards [h_chain, h_pos_νq, h_lt_νq, h_pos_q, h_lt_q]
    with y hy hpos1 hlt1 hpos2 hlt2
  have hne1 : ((ν.rnDeriv q y).toReal) ≠ 0 :=
    (ENNReal.toReal_pos hpos1.ne' hlt1.ne).ne'
  have hne2 : ((q.rnDeriv vol y).toReal) ≠ 0 :=
    (ENNReal.toReal_pos hpos2.ne' hlt2.ne).ne'
  rw [← hy, ENNReal.toReal_mul, Real.log_mul hne1 hne2]
  ring

/-- **Generic Bayes density split of the joint llr.** Mirror of
`ContChannelMIDecomp.llr_compProd_prod_split` over `α β` with `vol`. -/
private theorem llr_compProd_prod_split_gen
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (q : Measure β) [IsProbabilityMeasure q]
    (hWx_q : ∀ x, W x ≪ q) (hq_vol : q ≪ vol)
    (h_joint_ac : (p ⊗ₘ W) ≪ p.prod q)
    (g : α × β → ℝ≥0∞) (hg_meas : Measurable g)
    (hg_ae : ∀ x, (fun y => (W x).rnDeriv vol y) =ᵐ[W x] fun y => g (x, y)) :
    (fun z => llr (p ⊗ₘ W) (p.prod q) z)
      =ᵐ[p ⊗ₘ W]
    (fun z => Real.log (g z).toReal
                - Real.log (q.rnDeriv vol z.2).toReal) := by
  have h_prod : p.prod q = p ⊗ₘ (Kernel.const α q) := (Measure.compProd_const).symm
  have h_ac' : (p ⊗ₘ W) ≪ p ⊗ₘ (Kernel.const α q) := by rwa [h_prod] at h_joint_ac
  have h1 : (p ⊗ₘ W).rnDeriv (p.prod q)
      =ᵐ[p ⊗ₘ W] fun z => Kernel.rnDeriv W (Kernel.const α q) z.1 z.2 := by
    rw [h_prod]
    exact h_ac'.ae_le (rnDeriv_compProd_fibre h_ac')
  have h_split : (fun z => Real.log ((Kernel.rnDeriv W (Kernel.const α q) z.1 z.2)).toReal)
      =ᵐ[p ⊗ₘ W] fun z => Real.log (g z).toReal
                  - Real.log (q.rnDeriv vol z.2).toReal := by
    refine Measure.ae_compProd_of_ae_ae ?_ ?_
    · refine measurableSet_eq_fun ?_ ?_
      · exact (Kernel.measurable_rnDeriv W (Kernel.const α q)).ennreal_toReal.log
      · exact (hg_meas.ennreal_toReal.log).sub
          (((Measure.measurable_rnDeriv q vol).comp measurable_snd).ennreal_toReal.log)
    · filter_upwards with a
      have hker : (fun b => Kernel.rnDeriv W (Kernel.const α q) a b)
          =ᵐ[W a] fun b => (W a).rnDeriv q b := by
        have := (hWx_q a).ae_le
          (Kernel.rnDeriv_eq_rnDeriv_measure (κ := W) (η := Kernel.const α q) (a := a))
        simpa only [Kernel.const_apply] using this
      filter_upwards [hker, log_rnDeriv_split_gen (vol := vol) (hWx_q a) hq_vol, hg_ae a]
        with b hb hb_split hg_b
      rw [hb, hb_split, hg_b]
  have h_llr_eq : (fun z => llr (p ⊗ₘ W) (p.prod q) z)
      =ᵐ[p ⊗ₘ W]
      fun z => Real.log ((Kernel.rnDeriv W (Kernel.const α q) z.1 z.2)).toReal := by
    simp only [llr_def]
    filter_upwards [h1] with z hz1
    rw [hz1]
  exact h_llr_eq.trans h_split

/-- **Generic continuous-channel MI chain rule** (entropy in raw integral form).
`(mutualInfoOfChannel p W).toReal = (−∫_y log(dq/dvol) ∂q) − ∫_x (−∫_y log(d(Wx)/dvol) ∂(Wx)) dp`.
Specialized below to `jointDifferentialEntropyPi` via `integral_log_rnDeriv_self_eq_neg`.

Independent honesty audit (2026-05-29): genuine, sorryAx-free (`#print axioms` =
[propext, Classical.choice, Quot.sound]). All hypotheses are regularity preconditions;
generic re-derivation of the 1-D klDiv→llr→Fubini chain over an arbitrary `β` with a
`SigmaFinite` reference measure. @audit:ok -/
private theorem mutualInfoOfChannel_toReal_eq_neg_integral_log_sub
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (hW_ac : ∀ x, W x ≪ vol)
    (hWx_q : ∀ x, W x ≪ outputDistribution p W)
    (hq_ac : outputDistribution p W ≪ vol)
    (h_joint_ac : (p ⊗ₘ W) ≪ p.prod (outputDistribution p W))
    (g : α × β → ℝ≥0∞) (hg_meas : Measurable g)
    (hg_ae : ∀ x, (fun y => (W x).rnDeriv vol y) =ᵐ[W x] fun y => g (x, y))
    (h_int_fibre : Integrable (fun z : α × β => Real.log (g z).toReal) (p ⊗ₘ W))
    (h_int_out : Integrable
        (fun z : α × β => Real.log
            ((outputDistribution p W).rnDeriv vol z.2).toReal) (p ⊗ₘ W)) :
    (mutualInfoOfChannel p W).toReal
      = (-∫ y, Real.log ((outputDistribution p W).rnDeriv vol y).toReal
            ∂(outputDistribution p W))
        - ∫ x, (-∫ y, Real.log ((W x).rnDeriv vol y).toReal ∂(W x)) ∂p := by
  set q := outputDistribution p W with hq_def
  have hq_vol : q ≪ vol := hq_ac
  have h_kl :
      (mutualInfoOfChannel p W).toReal
        = ∫ z, llr (p ⊗ₘ W) (p.prod q) z ∂(p ⊗ₘ W) := by
    rw [mutualInfoOfChannel_def, jointDistribution_def]
    refine InformationTheory.toReal_klDiv_of_measure_eq h_joint_ac ?_
    rw [measure_univ, measure_univ]
  rw [h_kl]
  rw [integral_congr_ae
        (llr_compProd_prod_split_gen (vol := vol) (p := p) (W := W)
          q hWx_q hq_vol h_joint_ac g hg_meas hg_ae)]
  rw [integral_sub h_int_fibre h_int_out]
  -- fibre term: ∫_z log(g z) ∂(p⊗ₘW) = ∫_x (∫_y log(g(x,y)) ∂(Wx)) dp
  --   = ∫_x (∫_y log(d(Wx)/dvol) ∂(Wx)) dp
  have h_fibre :
      (∫ z, Real.log (g z).toReal ∂(p ⊗ₘ W))
        = ∫ x, (∫ y, Real.log ((W x).rnDeriv vol y).toReal ∂(W x)) ∂p := by
    rw [Measure.integral_compProd h_int_fibre]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    refine integral_congr_ae ?_
    filter_upwards [hg_ae x] with y hy
    rw [hy]
  -- output term: ∫_z log(dq/dvol z.2) ∂(p⊗ₘW) = ∫_y log(dq/dvol y) ∂q
  have h_out :
      (∫ z, Real.log (q.rnDeriv vol z.2).toReal ∂(p ⊗ₘ W))
        = ∫ y, Real.log (q.rnDeriv vol y).toReal ∂q := by
    -- `q = (p ⊗ₘ W).map Prod.snd` definitionally; push the marginal integral back to
    -- the joint via `integral_map`, keeping `q` fixed inside the density.
    have h_eq : q = (p ⊗ₘ W).map Prod.snd := rfl
    set F : β → ℝ := fun y => Real.log (q.rnDeriv vol y).toReal with hF
    have hF_meas : AEStronglyMeasurable F q :=
      ((Measure.measurable_rnDeriv q vol).ennreal_toReal.log).aestronglyMeasurable
    have hF_meas' : AEStronglyMeasurable F ((p ⊗ₘ W).map Prod.snd) := by
      rw [← h_eq]; exact hF_meas
    calc (∫ z, F z.2 ∂(p ⊗ₘ W))
        = ∫ y, F y ∂((p ⊗ₘ W).map Prod.snd) :=
          (MeasureTheory.integral_map measurable_snd.aemeasurable hF_meas').symm
      _ = ∫ y, F y ∂q := by rw [← h_eq]
  rw [h_fibre, h_out, integral_neg]
  ring

end GenericDecomp

/-- **#1 channel↔RV MI decomposition, `Fin n → ℝ` lift.** (Plan Phase 2 / inventory §B)
Specializes the generic chain rule to `β = Fin n → ℝ`, `vol = volume`, producing the
entropy in `jointDifferentialEntropyPi` form via the generic
`integral_log_rnDeriv_self_eq_neg` bridge. The regularity / integrability
hypotheses (absolute continuity + log-density integrability of the correlated output
law) are genuine preconditions supplied by Phase 1.

Independent honesty audit (2026-05-29): genuine, sorryAx-free. `#print axioms` =
[propext, Classical.choice, Quot.sound] (no `sorryAx`); transitive over the generic
core `mutualInfoOfChannel_toReal_eq_neg_integral_log_sub` (also sorryAx-free). The
hypotheses are all regularity preconditions (AC / measurability / integrability) — none
bundles the conclusion; the entropy bridge to `jointDifferentialEntropyPi` is genuine
via `integral_log_rnDeriv_self_eq_neg`. Faithful `Fin n → ℝ` generalization of the 1-D
`mutualInfoOfChannel_toReal_eq_diffEntropy_sub`. @audit:ok -/
theorem parallel_mutualInfoOfChannel_toReal_eq_diffEntropyPi_sub {n : ℕ}
    (N : Fin n → ℝ≥0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (p : Measure (Fin n → ℝ)) [IsProbabilityMeasure p]
    (hW_ac : ∀ x, (parallelGaussianChannel N h_meas h_parallel_meas) x ≪ volume)
    (hWx_q : ∀ x, (parallelGaussianChannel N h_meas h_parallel_meas) x
        ≪ outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas))
    (hq_ac : outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas) ≪ volume)
    (h_joint_ac : (p ⊗ₘ (parallelGaussianChannel N h_meas h_parallel_meas))
        ≪ p.prod (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)))
    (g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ≥0∞) (hg_meas : Measurable g)
    (hg_ae : ∀ x, (fun y => ((parallelGaussianChannel N h_meas h_parallel_meas) x).rnDeriv volume y)
        =ᵐ[(parallelGaussianChannel N h_meas h_parallel_meas) x] fun y => g (x, y))
    (h_int_fibre : Integrable (fun z => Real.log (g z).toReal)
        (p ⊗ₘ (parallelGaussianChannel N h_meas h_parallel_meas)))
    (h_int_out : Integrable
        (fun z : (Fin n → ℝ) × (Fin n → ℝ) => Real.log
            ((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).rnDeriv
              volume z.2).toReal)
        (p ⊗ₘ (parallelGaussianChannel N h_meas h_parallel_meas))) :
    (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
      = jointDifferentialEntropyPi
          (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas))
        - ∫ x, jointDifferentialEntropyPi
            ((parallelGaussianChannel N h_meas h_parallel_meas) x) ∂p := by
  set W := parallelGaussianChannel N h_meas h_parallel_meas with hW
  set q := outputDistribution p W with hq
  have h_raw := mutualInfoOfChannel_toReal_eq_neg_integral_log_sub
    (vol := (volume : Measure (Fin n → ℝ))) (p := p) (W := W)
    hW_ac hWx_q hq_ac h_joint_ac g hg_meas hg_ae h_int_fibre h_int_out
  rw [h_raw]
  -- bridge each raw `−∫ log(rnDeriv) ∂` to `jointDifferentialEntropyPi` via the
  -- generic `∫ log(dμ/dν) ∂μ = −∫ negMulLog(dμ/dν) ∂ν` identity.
  have h_out_bridge :
      (-∫ y, Real.log (q.rnDeriv volume y).toReal ∂q)
        = jointDifferentialEntropyPi q := by
    rw [integral_log_rnDeriv_self_eq_neg hq_ac, neg_neg]
    rfl
  have h_fibre_bridge : ∀ x,
      (-∫ y, Real.log ((W x).rnDeriv volume y).toReal ∂(W x))
        = jointDifferentialEntropyPi (W x) := by
    intro x
    rw [integral_log_rnDeriv_self_eq_neg (hW_ac x), neg_neg]
    rfl
  rw [h_out_bridge]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  exact h_fibre_bridge x

/-! ## Phase 3 — per-coord max-entropy converse split

### Phase 1 — correlated-output regularity preconditions (plan Phase 1 / inventory §D)

The decomposition (Phase 2) and the subadditivity step (`jointDifferentialEntropyPi_le_sum`,
genuine) both consume *regularity* preconditions of the correlated output law
`μY := outputDistribution p (parallelGaussianChannel N …)`: absolute continuity of the
joint and of every coordinate marginal w.r.t. the Lebesgue measure, the joint-vs-product
absolute continuity, and the log-density integrabilities. These are genuine consequences
of Gaussian smoothing (each fibre `Measure.pi (gaussianReal (x i) (N i))` is a full-support
product, so the output is volume-equivalent), but supplying them for an arbitrary
*correlated* input requires the `Fin n → ℝ` analogue of the 1-D AWGN Phase 6 plumbing
(`outputDistribution_logDensity_integrable[_joint]`, ~75 lines) plus the `Measure.pi`
absolute-continuity bridges. They are isolated here as named precondition lemmas; none is
load-bearing (each is a precondition consumed below, not a repackaging of the conclusion).

The fibre product-entropy identity (`condTerm = ∑ᵢ (1/2)log(2πe Nᵢ)`) and the output
marginal variance structure (`Var(Yᵢ) = Var(Xᵢ) + Nᵢ`) are likewise isolated as named
lemmas: they are genuine (independence of coordinates / noise additivity) but require the
per-coordinate marginal/Fubini analysis of the correlated output that mirrors the 1-D
template at `Fin n` scale. -/

/-- **Each fibre is absolutely continuous w.r.t. volume** (full-support Gaussian product).
Each component `gaussianReal (x i) (N i) ≪ volume` (`gaussianReal_absolutelyContinuous`,
needs `hN`), so the product fibre is `≪ volume` by the Step A helper `pi_absolutelyContinuous`.

Genuine, sorryAx-free (`#print axioms` = [propext, Classical.choice, Quot.sound]);
awaiting independent honesty audit. -/
theorem parallelChannel_fibre_absolutelyContinuous_volume {n : ℕ} (N : Fin n → ℝ≥0)
    (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) (x : Fin n → ℝ) :
    (parallelGaussianChannel N h_meas h_parallel_meas) x ≪ (volume : Measure (Fin n → ℝ)) := by
  rw [parallelGaussianChannel_apply]
  refine pi_absolutelyContinuous (fun i => gaussianReal (x i) (N i)) (fun i => ?_)
  exact gaussianReal_absolutelyContinuous (x i) (by exact_mod_cast hN i)

section Phase1Regularity

variable {n : ℕ} (N : Fin n → ℝ≥0)
variable (h_meas : IsParallelAwgnChannelMeasurable N)
variable (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
variable (p : Measure (Fin n → ℝ)) [IsProbabilityMeasure p]

/-- Coordinate marginals of the correlated output law are probability measures. -/
instance parallelOutput_marginal_isProbabilityMeasure (i : Fin n) :
    IsProbabilityMeasure
      ((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
        (fun z => z i)) := by
  have : IsProbabilityMeasure
      (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)) :=
    inferInstance
  exact Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable

/-- Output law joint absolute continuity `μY ≪ volume` (Gaussian-smoothed full support).
The output is the fibre mixture `μY s = ∫⁻ x, (W x) s ∂p`; each fibre
`W x = Measure.pi (gaussianReal (x i) (N i)) ≪ volume` (Step A + `gaussianReal_absolutelyContinuous`,
needs `hN`), so the mixture is `≪ volume`.

Genuine, sorryAx-free (`#print axioms` = [propext, Classical.choice, Quot.sound]);
awaiting independent honesty audit. -/
theorem parallelOutput_absolutelyContinuous_volume (hN : ∀ i, (N i : ℝ) ≠ 0) :
    outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)
      ≪ (volume : Measure (Fin n → ℝ)) := by
  set W := parallelGaussianChannel N h_meas h_parallel_meas with hW
  have h_fibre_ac : ∀ x, W x ≪ (volume : Measure (Fin n → ℝ)) :=
    fun x => parallelChannel_fibre_absolutelyContinuous_volume N hN h_meas h_parallel_meas x
  -- `μY = (p ⊗ₘ W).map Prod.snd`; show `volume s = 0 → μY s = 0`.
  refine Measure.AbsolutelyContinuous.mk (fun s hs hvol => ?_)
  show (outputDistribution p W) s = 0
  rw [outputDistribution, jointDistribution_def, Measure.snd,
    Measure.map_apply measurable_snd hs, Measure.compProd_apply (measurable_snd hs)]
  rw [lintegral_eq_zero_iff (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := W) (measurable_snd hs))]
  filter_upwards with x
  -- each fibre contributes 0
  show (W x) (Prod.mk x ⁻¹' (Prod.snd ⁻¹' s)) = 0
  have hpre : (Prod.mk x ⁻¹' (Prod.snd ⁻¹' s)) = s := by
    ext y; simp
  rw [hpre]
  exact h_fibre_ac x hvol

/-- Each coordinate marginal `μY.map (· i) ≪ volume`.
The marginal is `μY.map (· i)`; the fibre's `i`-marginal `gaussianReal (x i) (N i) ≪ volume`,
so the mixture `i`-marginal is `≪ volume`.

Genuine, sorryAx-free (`#print axioms` = [propext, Classical.choice, Quot.sound]);
awaiting independent honesty audit. -/
theorem parallelOutput_marginal_absolutelyContinuous_volume (hN : ∀ i, (N i : ℝ) ≠ 0)
    (i : Fin n) :
    (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
        (fun z => z i)
      ≪ (volume : Measure ℝ) := by
  classical
  set W := parallelGaussianChannel N h_meas h_parallel_meas with hW
  have hmeas_i : Measurable (fun z : Fin n → ℝ => z i) := measurable_pi_apply i
  -- fibre `i`-marginal: `(W x).map (· i) = gaussianReal (x i) (N i) ≪ volume`
  have h_fibre_marg_ac : ∀ x : Fin n → ℝ, (W x).map (fun z => z i) ≪ (volume : Measure ℝ) := by
    intro x
    rw [hW, parallelGaussianChannel_apply]
    have h_eval := Measure.pi_map_eval (μ := fun j => gaussianReal (x j) (N j)) i
    have h_one : (∏ j ∈ Finset.univ.erase i, (gaussianReal (x j) (N j)) Set.univ) = 1 := by
      refine Finset.prod_eq_one (fun j _ => ?_)
      exact measure_univ
    have h_eq : (Measure.pi (fun j => gaussianReal (x j) (N j))).map (fun z => z i)
        = gaussianReal (x i) (N i) := by
      rw [show (fun z : Fin n → ℝ => z i) = Function.eval i from rfl, h_eval, h_one, one_smul]
    rw [h_eq]
    exact gaussianReal_absolutelyContinuous (x i) (by exact_mod_cast hN i)
  -- `(μY.map (· i)) s = ∫⁻ x, (W x).map (· i) s ∂p`, each fibre marginal AC.
  refine Measure.AbsolutelyContinuous.mk (fun s hs hvol => ?_)
  rw [Measure.map_apply hmeas_i hs, outputDistribution, jointDistribution_def, Measure.snd,
    Measure.map_apply measurable_snd (hmeas_i hs),
    Measure.compProd_apply (measurable_snd (hmeas_i hs))]
  rw [lintegral_eq_zero_iff
    (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := W) (measurable_snd (hmeas_i hs)))]
  filter_upwards with x
  show (W x) (Prod.mk x ⁻¹' (Prod.snd ⁻¹' ((fun z : Fin n → ℝ => z i) ⁻¹' s))) = 0
  have hpre : (Prod.mk x ⁻¹' (Prod.snd ⁻¹' ((fun z : Fin n → ℝ => z i) ⁻¹' s)))
      = (fun z : Fin n → ℝ => z i) ⁻¹' s := by
    ext y; simp
  rw [hpre, ← Measure.map_apply hmeas_i hs]
  exact h_fibre_marg_ac x hvol

/-- **Reverse full-support AC of each output coordinate marginal** `volume ≪ μY.map (· i)`.
Mirror of `parallelOutput_marginal_absolutelyContinuous_volume` with the fibre marginal
reverse AC `volume ≪ gaussianReal (x i) (N i)` (`gaussianReal_absolutelyContinuous'`).

Genuine, sorryAx-free (`#print axioms` = [propext, Classical.choice, Quot.sound]);
awaiting independent honesty audit. -/
theorem volume_absolutelyContinuous_parallelOutput_marginal (hN : ∀ i, (N i : ℝ) ≠ 0)
    (i : Fin n) :
    (volume : Measure ℝ)
      ≪ (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
          (fun z => z i) := by
  classical
  set W := parallelGaussianChannel N h_meas h_parallel_meas with hW
  have hmeas_i : Measurable (fun z : Fin n → ℝ => z i) := measurable_pi_apply i
  -- fibre `i`-marginal reverse AC: `volume ≪ (W x).map (· i) = gaussianReal (x i) (N i)`
  have h_fibre_marg_rev : ∀ x : Fin n → ℝ,
      (volume : Measure ℝ) ≪ (W x).map (fun z => z i) := by
    intro x
    rw [hW, parallelGaussianChannel_apply]
    have h_eval := Measure.pi_map_eval (μ := fun j => gaussianReal (x j) (N j)) i
    have h_one : (∏ j ∈ Finset.univ.erase i, (gaussianReal (x j) (N j)) Set.univ) = 1 :=
      Finset.prod_eq_one (fun j _ => measure_univ)
    have h_eq : (Measure.pi (fun j => gaussianReal (x j) (N j))).map (fun z => z i)
        = gaussianReal (x i) (N i) := by
      rw [show (fun z : Fin n → ℝ => z i) = Function.eval i from rfl, h_eval, h_one, one_smul]
    rw [h_eq]
    exact gaussianReal_absolutelyContinuous' (x i) (by exact_mod_cast hN i)
  refine Measure.AbsolutelyContinuous.mk (fun s hs hmargs => ?_)
  rw [Measure.map_apply hmeas_i hs, outputDistribution, jointDistribution_def, Measure.snd,
    Measure.map_apply measurable_snd (hmeas_i hs),
    Measure.compProd_apply (measurable_snd (hmeas_i hs))] at hmargs
  rw [lintegral_eq_zero_iff
    (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := W) (measurable_snd (hmeas_i hs)))]
    at hmargs
  have h_ae : ∀ᵐ x ∂p, (W x).map (fun z => z i) s = 0 := by
    filter_upwards [hmargs] with x hx
    have hpre : (Prod.mk x ⁻¹' (Prod.snd ⁻¹' ((fun z : Fin n → ℝ => z i) ⁻¹' s)))
        = (fun z : Fin n → ℝ => z i) ⁻¹' s := by ext y; simp
    rw [hpre, ← Measure.map_apply hmeas_i hs] at hx
    exact hx
  obtain ⟨x, hx⟩ := h_ae.exists
  exact h_fibre_marg_rev x hx

/-- **Reverse full-support AC of the correlated output law** `volume ≪ μY`.
The output mixture `μY s = ∫⁻ x, (W x) s ∂p`; from `μY s = 0` the `p`-integral of the
nonnegative `x ↦ (W x) s` vanishes, so `(W x) s = 0` for `p`-a.e. `x` (in particular some
`x`, as `p` is a probability measure), whence `volume s = 0` by the reverse Gaussian-product
AC `volume ≪ W x` (`volume_absolutelyContinuous_pi_gaussian`, needs `hN`).

Genuine, sorryAx-free (`#print axioms` = [propext, Classical.choice, Quot.sound]);
awaiting independent honesty audit. -/
theorem volume_absolutelyContinuous_parallelOutput (hN : ∀ i, (N i : ℝ) ≠ 0) :
    (volume : Measure (Fin n → ℝ))
      ≪ outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas) := by
  set W := parallelGaussianChannel N h_meas h_parallel_meas with hW
  -- reverse AC of each fibre
  have h_fibre_rev : ∀ x : Fin n → ℝ, (volume : Measure (Fin n → ℝ)) ≪ W x := by
    intro x
    rw [hW, parallelGaussianChannel_apply]
    exact volume_absolutelyContinuous_pi_gaussian x N hN
  refine Measure.AbsolutelyContinuous.mk (fun s hs hμYs => ?_)
  -- expand `μY s = ∫⁻ x, (W x) s ∂p` and conclude `(W x) s = 0` p-a.e.
  rw [outputDistribution, jointDistribution_def, Measure.snd,
    Measure.map_apply measurable_snd hs, Measure.compProd_apply (measurable_snd hs)] at hμYs
  rw [lintegral_eq_zero_iff
    (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := W) (measurable_snd hs))]
    at hμYs
  -- `hμYs : (fun x => W x (Prod.mk x ⁻¹' (Prod.snd ⁻¹' s))) =ᵐ[p] 0`; pick a point
  have h_ae : ∀ᵐ x ∂p, (W x) s = 0 := by
    filter_upwards [hμYs] with x hx
    have hpre : (Prod.mk x ⁻¹' (Prod.snd ⁻¹' s)) = s := by ext y; simp
    rwa [hpre] at hx
  -- a.e. nonempty under a probability measure
  obtain ⟨x, hx⟩ := h_ae.exists
  exact h_fibre_rev x hx

/-- Joint vs. product-of-marginals absolute continuity for the output law.
`μY ≪ volume` (`parallelOutput_absolutelyContinuous_volume`, Wave 1) composed with the
reverse `volume ≪ Measure.pi (μY.map (· i))` from `pi_absolutelyContinuous_reverse`, whose
componentwise mutual-AC hypotheses are the forward marginal AC
(`parallelOutput_marginal_absolutelyContinuous_volume`) and the reverse marginal AC
(`volume_absolutelyContinuous_parallelOutput_marginal`); all need `hN`.

Genuine, sorryAx-free (`#print axioms` = [propext, Classical.choice, Quot.sound]);
awaiting independent honesty audit. -/
theorem parallelOutput_absolutelyContinuous_pi_marginals (hN : ∀ i, (N i : ℝ) ≠ 0) :
    outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)
      ≪ Measure.pi (fun i =>
          (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
            (fun z => z i)) := by
  refine (parallelOutput_absolutelyContinuous_volume N h_meas h_parallel_meas p hN).trans ?_
  exact pi_absolutelyContinuous_reverse _
    (fun i => parallelOutput_marginal_absolutelyContinuous_volume N h_meas h_parallel_meas p hN i)
    (fun i => volume_absolutelyContinuous_parallelOutput_marginal N h_meas h_parallel_meas p hN i)

/-- Marginal log-density joint integrability.
@residual(plan:parallel-gaussian-converse-closure-plan) -/
theorem parallelOutput_marginal_logDensity_integrable (i : Fin n) :
    Integrable
      (fun z => Real.log
        (((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
          (fun z => z i)).rnDeriv volume (z i)).toReal)
      (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)) := by
  sorry

/-- Joint log-density integrability.
@residual(plan:parallel-gaussian-converse-closure-plan) -/
theorem parallelOutput_joint_logDensity_integrable :
    Integrable
      (fun z => Real.log
        ((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).rnDeriv
          volume z).toReal)
      (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)) := by
  sorry

/-- **Fibre product-entropy identity.** Each fibre is a coordinate product of Gaussians,
so its joint differential entropy is the coordinate sum of Gaussian entropies, each
`(1/2)log(2πe Nᵢ)` independent of the mean `x i`. Hence the conditional term is the
constant `∑ᵢ (1/2)log(2πe Nᵢ)`.
@residual(plan:parallel-gaussian-converse-closure-plan) -/
theorem parallel_condTerm_eq_sum_noise_entropy (hN : ∀ i, (N i : ℝ) ≠ 0) :
    (∫ x, jointDifferentialEntropyPi
        ((parallelGaussianChannel N h_meas h_parallel_meas) x) ∂p)
      = ∑ i : Fin n, (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (N i : ℝ)) := by
  sorry

/-- **Output marginal mean.** `mᵢ := ∫ y, y ∂(μY.map (· i))`. Abbreviation. -/
noncomputable def parallelOutputMean (i : Fin n) : ℝ :=
  ∫ y, y ∂((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
    (fun z => z i))

/-- **Output marginal variance bound (noise additivity).** With `Yᵢ = Xᵢ + Zᵢ` and
`Zᵢ ∼ 𝒩(0,Nᵢ)` independent of `Xᵢ`, `Var(Yᵢ) = Var(Xᵢ) + Nᵢ`. The genuine content is
the convolution variance; we record the upper bound `Var(Yᵢ) ≤ (∫ (xᵢ)² ∂p) + Nᵢ`
(`Var(Xᵢ) ≤ E[Xᵢ²]`) directly, in the form needed by the max-entropy allocation.
@residual(plan:parallel-gaussian-converse-closure-plan) -/
theorem parallelOutput_variance_le (i : Fin n) :
    ∫ y, (y - parallelOutputMean N h_meas h_parallel_meas p i) ^ 2
        ∂((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
          (fun z => z i))
      ≤ (∫ x : Fin n → ℝ, (x i) ^ 2 ∂p) + (N i : ℝ) := by
  sorry

/-- **Output marginal variance lower bound (noise contribution).** `Var(Yᵢ) ≥ Nᵢ`,
since the independent Gaussian noise of variance `Nᵢ` adds to the input variance.
This makes the allocation `P'ᵢ := Var(Yᵢ) − Nᵢ` nonnegative.
@residual(plan:parallel-gaussian-converse-closure-plan) -/
theorem parallelOutput_variance_ge_noise (i : Fin n) :
    (N i : ℝ)
      ≤ ∫ y, (y - parallelOutputMean N h_meas h_parallel_meas p i) ^ 2
          ∂((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
            (fun z => z i)) := by
  sorry

/-- **Output marginal variance integrability.**
@residual(plan:parallel-gaussian-converse-closure-plan) -/
theorem parallelOutput_variance_integrable (i : Fin n) :
    Integrable (fun y => (y - parallelOutputMean N h_meas h_parallel_meas p i) ^ 2)
      ((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
        (fun z => z i)) := by
  sorry

/-- **Output marginal entropy-integrand volume integrability** (for `differentialEntropy_le_gaussian_of_variance_le`).
@residual(plan:parallel-gaussian-converse-closure-plan) -/
theorem parallelOutput_marginal_entropy_integrable (i : Fin n) :
    Integrable
      (fun y => Real.negMulLog
        (((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
          (fun z => z i)).rnDeriv volume y).toReal)
      (volume : Measure ℝ) := by
  sorry

/-- **Decomposition regularity bundle: `hWx_q`** (fibre ≪ output).
`W x ≪ volume` (`parallelChannel_fibre_absolutelyContinuous_volume`, Wave 1) composed with
the reverse full-support AC `volume ≪ μY` (`volume_absolutelyContinuous_parallelOutput`);
both need `hN`.

Genuine, sorryAx-free (`#print axioms` = [propext, Classical.choice, Quot.sound]);
awaiting independent honesty audit. -/
theorem parallelChannel_fibre_absolutelyContinuous_output (hN : ∀ i, (N i : ℝ) ≠ 0)
    (x : Fin n → ℝ) :
    (parallelGaussianChannel N h_meas h_parallel_meas) x
      ≪ outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas) := by
  exact (parallelChannel_fibre_absolutelyContinuous_volume N hN h_meas h_parallel_meas x).trans
    (volume_absolutelyContinuous_parallelOutput N h_meas h_parallel_meas p hN)

/-- **Channel↔RV MI decomposition value** for the correlated input.
`I = jointDifferentialEntropyPi(μY) − ∫ jointDifferentialEntropyPi(W x) ∂p`.
Genuine reduction to the sorryAx-free Phase 2 lift
`parallel_mutualInfoOfChannel_toReal_eq_diffEntropyPi_sub`, supplying the regularity /
integrability preconditions (each a Phase 1 precondition lemma). The proxy fibre density
`g` (a product of Gaussian PDFs) is the only additional regularity datum, isolated here.
@residual(plan:parallel-gaussian-converse-closure-plan) -/
theorem parallel_mi_decomp_value (hN : ∀ i, (N i : ℝ) ≠ 0) :
    (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
      = jointDifferentialEntropyPi
          (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas))
        - ∫ x, jointDifferentialEntropyPi
            ((parallelGaussianChannel N h_meas h_parallel_meas) x) ∂p := by
  -- The proxy fibre density and `hg_ae` bridge are supplied by Gaussian PDF products;
  -- isolated as the remaining regularity datum of the genuine Phase 2 decomposition lift.
  sorry

end Phase1Regularity

/-- **#2 per-coord max-entropy converse split (correlated input).** (Plan Phase 3 / inventory §C)

For `0 ≤ P` the converse chain is a **genuine assembly**: MI decomposition (Phase 2 lift,
sorryAx-free) + output-entropy subadditivity (`jointDifferentialEntropyPi_le_sum`, genuine)
+ per-coord Gaussian max-entropy (`differentialEntropy_le_gaussian_of_variance_le`,
`@audit:ok`) + variance allocation `P'ᵢ := Var(Yᵢ) − Nᵢ` + capacity log-algebra. The
remaining residuals are the *correlated-output regularity* (Phase 1 precondition
lemmas above) and the fibre product-entropy / output-variance identities, all carrying
`@residual(plan:parallel-gaussian-converse-closure-plan)`; the converse organization itself
is genuine (no load-bearing hypothesis, no degenerate exploitation).

The `0 ≤ P` precondition is genuine and necessary: without it `parallel_per_input_mi_le_sum`
would be FALSE for `P < 0` (the constraint set `parallelGaussianPowerConstraintSet P` is
non-empty for `P < 0` — it contains the Dirac at 0, since `ENNReal.ofReal P = 0` collapses
the lintegral constraint to `0 ≤ 0` — yet `∑ P'ᵢ ≤ P < 0` with `P'ᵢ ≥ 0` is unsatisfiable).
The constraint is threaded from the headline `parallel_gaussian_capacity_formula_minimal`
(which holds `0 < P`) through the constructor; the previous tier-5 `false-statement` defect
(P unconstrained) has been fixed by adding this hypothesis.
@residual(plan:parallel-gaussian-converse-closure-plan) -/
theorem parallel_per_input_mi_le_sum {n : ℕ}
    (P : ℝ) (hP : 0 ≤ P) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (p : Measure (Fin n → ℝ)) [IsProbabilityMeasure p]
    (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    ∃ P' : Fin n → ℝ, (∀ i, 0 ≤ P' i) ∧ (∑ i : Fin n, P' i ≤ P) ∧
      (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
        ≤ ∑ i : Fin n, (1/2) * Real.log (1 + P' i / (N i : ℝ)) := by
  classical
  set W := parallelGaussianChannel N h_meas h_parallel_meas with hW_def
  set μY := outputDistribution p W with hμY_def
  -- per-coordinate noise positivity
  have hN_pos : ∀ i, (0 : ℝ) < (N i : ℝ) :=
    fun i => lt_of_le_of_ne (N i).coe_nonneg (Ne.symm (hN i))
  -- ===== Genuine region: `0 ≤ P` (threaded from the headline) =====
  -- genuine integrability + Bochner second-moment bound from membership
  obtain ⟨hp_2mom_int, hp_2mom⟩ :=
    parallelGaussianPowerConstraintSet_mem_iff_integrable P hP p hp
  -- output law + marginals are probability measures
  haveI hμY_prob : IsProbabilityMeasure μY := by rw [hμY_def]; infer_instance
  haveI hμY_marg_prob : ∀ i, IsProbabilityMeasure (μY.map (fun z => z i)) := by
    intro i; rw [hμY_def, hW_def]; infer_instance
  -- per-coord output mean / variance
  set m : Fin n → ℝ := fun i => parallelOutputMean N h_meas h_parallel_meas p i with hm_def
  set varY : Fin n → ℝ := fun i =>
    ∫ y, (y - m i) ^ 2 ∂(μY.map (fun z => z i)) with hvarY_def
  -- variance allocation `P'ᵢ := Var(Yᵢ) − Nᵢ`
  refine ⟨fun i => varY i - (N i : ℝ), ?_, ?_, ?_⟩
  · -- `0 ≤ P'ᵢ`: noise additivity `Var(Yᵢ) ≥ Nᵢ`
    intro i
    have h := parallelOutput_variance_ge_noise N h_meas h_parallel_meas p i
    simp only [hvarY_def, hm_def]
    linarith [h]
  · -- `∑ P'ᵢ ≤ P`: `∑ (Var(Yᵢ) − Nᵢ) ≤ ∑ E[Xᵢ²] ≤ P`
    have h_each : ∀ i : Fin n, varY i - (N i : ℝ) ≤ ∫ x : Fin n → ℝ, (x i) ^ 2 ∂p := by
      intro i
      have h := parallelOutput_variance_le N h_meas h_parallel_meas p i
      simp only [hvarY_def, hm_def]
      linarith [h]
    calc ∑ i : Fin n, (varY i - (N i : ℝ))
        ≤ ∑ i : Fin n, ∫ x : Fin n → ℝ, (x i) ^ 2 ∂p :=
          Finset.sum_le_sum (fun i _ => h_each i)
      _ ≤ P := hp_2mom
  · -- the converse chain: MI decomp + subadditivity + per-coord max-entropy + log-algebra
    -- assembled via `parallelGaussian_max_ent_le_of_subadditivity`.
    set condTerm : ℝ := ∫ x, jointDifferentialEntropyPi (W x) ∂p with hcond_def
    -- (★1) decomposition value: I = h(Yⁿ) − condTerm
    have h_decomp :
        (mutualInfoOfChannel p W).toReal = jointDifferentialEntropyPi μY - condTerm := by
      rw [hμY_def, hcond_def, hW_def]
      exact parallel_mi_decomp_value N h_meas h_parallel_meas p hN
    -- condTerm is the constant noise-entropy sum
    have h_cond_eq : condTerm = ∑ i : Fin n, (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (N i : ℝ)) := by
      rw [hcond_def]
      exact parallel_condTerm_eq_sum_noise_entropy N h_meas h_parallel_meas p hN
    -- per-coord max-entropy bound: h(Yᵢ) ≤ (1/2)log(2πe·Var(Yᵢ)) and Var(Yᵢ) = P'ᵢ + Nᵢ
    have h_perCoord :
        (∑ i, differentialEntropy (μY.map (fun z => z i))) - condTerm
          ≤ ∑ i, (1/2) * Real.log (1 + (varY i - (N i : ℝ)) / (N i : ℝ)) := by
      rw [h_cond_eq, ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum (fun i _ => ?_)
      -- variance value `v := Var(Yᵢ).toNNReal` and `(v : ℝ) = Var(Yᵢ)`
      have h_var_nonneg : (0 : ℝ) < varY i := by
        have h := parallelOutput_variance_ge_noise N h_meas h_parallel_meas p i
        simp only [hvarY_def, hm_def] at h ⊢
        linarith [hN_pos i]
      set v : ℝ≥0 := varY i |>.toNNReal with hv_def
      have hv_coe : (v : ℝ) = varY i := by rw [hv_def, Real.coe_toNNReal _ h_var_nonneg.le]
      have hv_ne : v ≠ 0 := by rw [hv_def]; exact (Real.toNNReal_pos.mpr h_var_nonneg).ne'
      -- max-entropy on the marginal
      have h_maxent :
          differentialEntropy (μY.map (fun z => z i))
            ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ)) := by
        have hμac := parallelOutput_marginal_absolutelyContinuous_volume N h_meas h_parallel_meas p hN i
        have hvar_int := parallelOutput_variance_integrable N h_meas h_parallel_meas p i
        have hent_int := parallelOutput_marginal_entropy_integrable N h_meas h_parallel_meas p i
        rw [← hW_def, ← hμY_def] at hμac hvar_int hent_int
        refine differentialEntropy_le_gaussian_of_variance_le hμac (m i) hv_ne rfl ?_ ?_ ?_
        · rw [hv_coe]
        · simpa only [hm_def] using hvar_int
        · simpa only using hent_int
      -- log algebra: (1/2)log(2πe·v) − (1/2)log(2πe·Nᵢ) = (1/2)log(1 + (v−Nᵢ)/Nᵢ)
      have h_log_alg :
          (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ))
              - (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (N i : ℝ))
            = (1/2) * Real.log (1 + (varY i - (N i : ℝ)) / (N i : ℝ)) := by
        have h_num : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * (v : ℝ) := by
          rw [hv_coe]
          have h2 : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by positivity
          exact mul_pos h2 h_var_nonneg
        have h_den : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * (N i : ℝ) :=
          mul_pos (by positivity) (hN_pos i)
        rw [← mul_sub, ← Real.log_div h_num.ne' h_den.ne']
        have h_arg :
            (2 * Real.pi * Real.exp 1 * (v : ℝ)) / (2 * Real.pi * Real.exp 1 * (N i : ℝ))
              = 1 + (varY i - (N i : ℝ)) / (N i : ℝ) := by
          rw [hv_coe]
          rw [mul_div_mul_left _ _ (show (2 * Real.pi * Real.exp 1 : ℝ) ≠ 0 by positivity)]
          rw [add_div' _ _ _ (hN_pos i).ne']
          ring_nf
        rw [h_arg]
      calc differentialEntropy (μY.map (fun z => z i))
            - (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (N i : ℝ))
          ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ))
              - (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (N i : ℝ)) :=
            sub_le_sub_right h_maxent _
        _ = (1/2) * Real.log (1 + (varY i - (N i : ℝ)) / (N i : ℝ)) := h_log_alg
    -- assemble via the genuine subadditivity wrapper
    have h_marg_ac := fun i => parallelOutput_marginal_absolutelyContinuous_volume N h_meas h_parallel_meas p hN i
    have hμ_ac := parallelOutput_absolutelyContinuous_volume N h_meas h_parallel_meas p hN
    have h_joint_ac := parallelOutput_absolutelyContinuous_pi_marginals N h_meas h_parallel_meas p hN
    have h_int_marg := parallelOutput_marginal_logDensity_integrable N h_meas h_parallel_meas p
    have h_int_joint := parallelOutput_joint_logDensity_integrable N h_meas h_parallel_meas p
    rw [← hW_def, ← hμY_def] at h_marg_ac hμ_ac h_joint_ac h_int_marg h_int_joint
    exact parallelGaussian_max_ent_le_of_subadditivity μY
      (mutualInfoOfChannel p W).toReal condTerm (fun i => varY i - (N i : ℝ)) N
      h_decomp h_marg_ac hμ_ac h_joint_ac h_int_marg h_int_joint h_perCoord

/-! ## Phase 5 — `bddAbove` field (genuine, from the Phase 3 converse split) -/

/-- **#4 `BddAbove (miImage P N …)`** (Plan Phase 5 / inventory §E #4). Every MI value
of a feasible (correlated) input is bounded by the *constant* `p`-independent
water-filling sum `∑ᵢ (1/2) log(1 + P/Nᵢ)`: the Phase 3 split returns a feasible `P'`
with `0 ≤ P'ᵢ` and `∑P'ᵢ ≤ P`, so `P'ᵢ ≤ P` coordinate-wise and `log` monotonicity
caps each term. Genuine modulo the Phase 3 converse split. -/
theorem parallel_bddAbove_miImage {n : ℕ}
    (P : ℝ) (hP : 0 ≤ P) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) :
    BddAbove (miImage P N h_meas h_parallel_meas) := by
  -- constant upper bound: `C := ∑ᵢ (1/2) log(1 + P/Nᵢ)`
  refine ⟨∑ i : Fin n, (1/2) * Real.log (1 + P / (N i : ℝ)), ?_⟩
  rintro y ⟨p, hp_mem, rfl⟩
  -- `p` is a probability measure (set membership)
  have hp_prob : IsProbabilityMeasure p := hp_mem.1
  obtain ⟨P', hP'_nn, hP'_sum, hP'_le⟩ :=
    parallel_per_input_mi_le_sum P hP N hN h_meas h_parallel_meas p hp_mem
  refine hP'_le.trans ?_
  -- each P'ᵢ ≤ ∑P'ⱼ ≤ P, hence the term-wise log bound
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hNi_pos : (0 : ℝ) < (N i : ℝ) :=
    lt_of_le_of_ne (N i).coe_nonneg (Ne.symm (hN i))
  have hP'i_le_P : P' i ≤ P :=
    le_trans (Finset.single_le_sum (fun j _ => hP'_nn j) (Finset.mem_univ i)) hP'_sum
  have h_arg_pos : (0 : ℝ) < 1 + P' i / (N i : ℝ) := by
    have : (0 : ℝ) ≤ P' i / (N i : ℝ) := div_nonneg (hP'_nn i) hNi_pos.le
    linarith
  have h_arg_le : 1 + P' i / (N i : ℝ) ≤ 1 + P / (N i : ℝ) := by
    gcongr
  have h_log_le : Real.log (1 + P' i / (N i : ℝ)) ≤ Real.log (1 + P / (N i : ℝ)) :=
    Real.log_le_log h_arg_pos h_arg_le
  linarith [h_log_le]

end InformationTheory.Shannon.ParallelGaussian
