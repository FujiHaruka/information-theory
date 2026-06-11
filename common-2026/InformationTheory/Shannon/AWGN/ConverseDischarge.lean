import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.Walls
import InformationTheory.Shannon.Converse
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.ChannelCoding.Basic
import InformationTheory.Shannon.ChannelCoding.MIDecomp
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import InformationTheory.Draft.Shannon.MultivariateDiffEntropy

/-! # AWGN F-3 converse — analytic body discharge

Plan: `docs/shannon/awgn-converse-aux-plan.md` (Phase 0 inventory 反映 1143 行)
+ `docs/shannon/awgn-m5-sorry-migration-plan.md` Phase 3-α (sorry-based migration)

Cover-Thomas 9.1.2 (converse) の analytic body (Fano + DPI + chain rule + per-letter
Gaussian max-entropy + sum-form integration) を組み立てる。

**2026-05-28 Phase 3-α sorry-based migration**: 旧 bundle predicate
`IsAwgnConverseFeasible` + 3 sub-bound predicate
(`PerLetterIntegrabilityForConverse` / `ContinuousMIChainRuleForConverse` /
`MarkovChainForConverse`) を削除し、各 analytic content を
`InformationTheory/Shannon/AwgnWalls.lean` の補題に格上げ (Tier 3 → Tier 2)。consumer
は当該補題を呼ぶ普通の lemma call に縮約 (本 file scope は 0 sorry)。3 補題のうち
per-letter integrability と markov-regularity は後に genuine 化済 (`@audit:ok`、
sorryAx-free)、残る Mathlib 壁は `awgnContinuousMIChainRule_holds` の sorry のみ。

| 旧 predicate | 後継補題 | wall name (status) |
|---|---|---|
| `PerLetterIntegrabilityForConverse` | `awgnPerLetterIntegrability_holds` | `awgn-per-letter-integrability` (closed 2026-06-10, genuine `@audit:ok`, sorryAx-free) |
| `ContinuousMIChainRuleForConverse` | `awgnContinuousMIChainRule_holds` | `awgn-continuous-mi-chain-rule` (active wall, `sorry`) |
| `MarkovChainForConverse` | `awgnConverseMarkov_holds` (旧 Route B / L-AWGNM5-1-α) | `awgn-converse-markov-regularity` (closed 2026-06-04, genuine `@audit:ok`, sorryAx-free) |

## Phase 構成

* Phase A — joint law / marginal / MI の closed-form quantity (`awgnConverseJoint` /
  `perLetterYLaw` / `perLetterMI` / `jointMIWYn` / `jointMIXnYn`)
* Phase B-Fano — `awgn_converse_single_shot_call` (Phase B-Fano dispatch)
* Phase B-DPI/chain — `awgn_dpi` (Markov DPI、`awgnConverseMarkov_holds` 経由) /
  `awgn_chain_rule` (chain rule、`awgnContinuousMIChainRule_holds` 経由)
* Phase B-Gaussian — 起草時 `awgn_per_letter_mi_le_capacity` 想定だったが
  per-message `power_constraint` から per-letter `E[X_i²] ≤ P` が genuine 化不能
  (false-statement defect) のため **撤回**。代替は Phase C の sum-form chain
  (`awgn_per_letter_input_power_avg` + `awgn_per_letter_mi_le_log_var` + Jensen)。
* Phase C — `isAwgnConverseFeasible_discharger` 統合 + `awgn_converse_F3_discharged` wrapper

## 設計指針

* `perLetterYLaw` / `awgnConverseJoint` は closed-form で genuine 化済。
  `perLetterMI` / `jointMIWYn` / `jointMIXnYn` は canonical joint `awgnConverseJoint`
  の `mutualInfo` 形で genuine 化済。
* 残る 1 hyp `h_mi_bridge_per_letter` (per-letter MI = `h(Y_i) - h(Z)` bridge) は
  F-2 closure 待ち (`awgn-mi-bridge-plan.md`)、`awgn_converse` (`AWGNConverse.lean`)
  の sorry に集約。 -/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
  InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

/-! ## Phase A — local quantities (joint law / marginal / MI) -/

/-- **Canonical joint law of `(W, Y^n)` under uniform message and AWGN channel**.

Sample space `Ω := Fin M × (Fin n → ℝ)` with `W = Prod.fst` and `Y^n = Prod.snd`.
Under uniform `W ∼ Uniform(Fin M)` and conditional `Y^n | W=m ∼ ∏ᵢ N(c.encoder m i, N)`,
the joint law is the mixture
`(1/M) ∑ m, δ_m ⊗ ∏ᵢ AWGN_{c.encoder m i}`. -/
noncomputable def awgnConverseJoint
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) :
    Measure (Fin M × (Fin n → ℝ)) :=
  ((Fintype.card (Fin M) : ℝ≥0∞)⁻¹) •
    ∑ m : Fin M,
      (Measure.dirac m).prod
        (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i)))

/-- `awgnConverseJoint` is a probability measure when `M ≥ 1` (= `[NeZero M]`):
the mixture has weights `(1/M)` summing to `1`. Body fill is Phase B-DPI side
(regularity prerequisite for `IsMarkovChain` typeclass resolution). -/
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
          (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))))
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

/-- per-letter `Y_i` 周辺分布 (uniform `W` 上の `encoder ∘ W` marginal を AWGN で
convolve)。`(1/M) ∑ₘ AWGN_{c.encoder m i}` の閉じた形 (= mixture of Gaussians)。 -/
@[entry_point]
noncomputable def perLetterYLaw
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) : Measure ℝ :=
  (awgnConverseJoint h_meas c).map (fun ω => ω.2 i)

/-- per-letter mutual information `I(X_i; Y_i)` on the canonical joint
`awgnConverseJoint c h_meas`, with `X_i ω := c.encoder ω.1 i` and `Y_i ω := ω.2 i`. -/
@[entry_point]
noncomputable def perLetterMI
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) : ℝ≥0∞ :=
  mutualInfo (awgnConverseJoint h_meas c)
    (fun ω => c.encoder ω.1 i) (fun ω => ω.2 i)

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
  mutualInfo (awgnConverseJoint h_meas c) (fun ω => c.encoder ω.1) Prod.snd

/-! ## Phase A — sub-bound walls (Phase 3-α sorry-based migration)

**2026-05-28 Phase 3-α (`awgn-m5-sorry-migration-plan.md`)**: 旧 3 sub-bound predicate
(`PerLetterIntegrabilityForConverse` / `ContinuousMIChainRuleForConverse` /
`MarkovChainForConverse`) + bundle `IsAwgnConverseFeasible` を削除し、各 analytic
content を `InformationTheory/Shannon/AwgnWalls.lean` の shared sorry 補題に格上げした
(Tier 3 `@audit:retract-candidate(load-bearing-predicate)` → Tier 2 `sorry` +
`@residual(wall:…)`)。consumer (`isAwgnConverseFeasible_discharger` /
`awgn_converse_F3_discharged`) は wall 補題を呼ぶ普通の lemma call に縮約。

| 旧 predicate | 後継補題 (`AwgnWalls.lean`) | wall name (status) |
|---|---|---|
| `PerLetterIntegrabilityForConverse` | `awgnPerLetterIntegrability_holds` | `awgn-per-letter-integrability` (closed 2026-06-10, genuine `@audit:ok`) |
| `ContinuousMIChainRuleForConverse` | `awgnContinuousMIChainRule_holds` | `awgn-continuous-mi-chain-rule` (active wall, `sorry`) |
| `MarkovChainForConverse` | `awgnConverseMarkov_holds` (旧 Route B, L-AWGNM5-1-α) | `awgn-converse-markov-regularity` (closed 2026-06-04, genuine `@audit:ok`) |

`MarkovChainForConverse` は Phase 3α-1 で当初 Route B (L-AWGNM5-1-α) に降格していたが、
独立壁再評価で plumbing 過大評価と判明し `awgnConverseMarkov_holds` で genuine 化済
(sorryAx-free)。`awgn-per-letter-integrability` も 2026-06-10 に genuine 化 (有限 1-D
Gaussian 混合密度の直接 domination、SMB 不要)。よって本 cluster の active wall は
**`awgn-continuous-mi-chain-rule` 1 件のみ**。 -/

/-! ## Phase B-Fano skeleton (本 commit は signature + sorry のみ)

`shannon_converse_single_shot` (`InformationTheory/Shannon/Converse.lean:81`) を
`X := Fin M, Y := Fin n → ℝ, decoder := c.decoder, μ := awgnConverseJoint c h_meas`
で 1 行呼出。Fano + DPI postprocess + entropy chain + `H(W uniform) = log M` を
集約。 -/

/-! ### Private helpers for `awgn_converse_single_shot_call`

`shannon_converse_single_shot` を `awgnConverseJoint` で起動するために必要な
plumbing 補題群。本 section の補題はすべて private、本 file 内専用。 -/

/-- Auxiliary: on a `Fintype` + `MeasurableSingletonClass`, `Measure.count`
equals `∑ a, Measure.dirac a` (Finset.univ sum). -/
private lemma count_eq_finset_sum_dirac (α : Type*) [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    (Measure.count : Measure α) = ∑ a : α, Measure.dirac a := by
  -- `Measure.sum_smul_dirac : sum (fun a => μ {a} • dirac a) = μ`
  -- with `μ := count`, `count {a} = 1` ⇒ `sum (fun a => dirac a) = count`.
  -- Then `sum_fintype` converts `sum` to `∑`.
  have h_one : ∀ a : α, (Measure.count : Measure α) {a} = 1 := fun a =>
    Measure.count_singleton a
  have h_sum : Measure.sum (fun a : α => Measure.dirac a)
      = (Measure.count : Measure α) := by
    have h := Measure.sum_smul_dirac (μ := (Measure.count : Measure α))
    -- Replace each `count {a}` by `1` and `1 • dirac a` by `dirac a`.
    simp_rw [h_one, one_smul] at h
    exact h
  rw [← h_sum, Measure.sum_fintype]

/-- AWGN converse の uniform message marginal: `(awgnConverseJoint h_meas c).map Prod.fst
= (Fintype.card (Fin M))⁻¹ • Measure.count`。

mixture `(1/M) ∑ m, (dirac m).prod ν_m` の `Prod.fst` 像が、各 `ν_m` が
probability measure であることから `(1/M) ∑ m, dirac m`、これが Fintype `Fin M`
上の `Measure.count` の `(1/M)` 倍に等しい (`MeasurableSingletonClass` 経由)。 -/
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
      (m := fun m => (Measure.dirac m).prod
        (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))))
      h_map_fst_meas.aemeasurable]
  -- Each summand: `((dirac m).prod ν_m).map Prod.fst = (ν_m univ) • dirac m = dirac m`.
  have h_each : ∀ m : Fin M,
      ((Measure.dirac m).prod
          (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i)))).map
        (Prod.fst : Fin M × (Fin n → ℝ) → Fin M) = Measure.dirac m := by
    intro m
    -- `Measure.map_fst_prod : (μ.prod ν).map Prod.fst = (ν univ) • μ`
    rw [Measure.map_fst_prod]
    have : Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))
        (Set.univ : Set (Fin n → ℝ)) = 1 := by
      exact measure_univ
    rw [this, one_smul]
  rw [Finset.sum_congr rfl (fun m _ => h_each m)]
  -- Now: (M⁻¹) • ∑ m, dirac m = (M⁻¹) • Measure.count.
  rw [count_eq_finset_sum_dirac]

/-- AWGN converse joint の `Prod.snd` measurability (trivial, but used for
`shannon_converse_single_shot.hYo`). -/
private lemma awgnConverseJoint_measurable_snd :
    Measurable (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) :=
  measurable_snd

private lemma awgnConverseJoint_measurable_fst :
    Measurable (Prod.fst : Fin M × (Fin n → ℝ) → Fin M) :=
  measurable_fst

/-- AWGN converse `Pe` bridge: AWGN `Pe = (1/M) ∑ m, (errorProbAt ...).toReal`
(in the theorem statement) 形 と Fano `errorProb (awgnConverseJoint h_meas c)
Prod.fst Prod.snd c.decoder` 形の同値性。

mixture `(1/M) ∑ m, (dirac m).prod ν_m` 上で `{ω | ω.1 ≠ c.decoder ω.2}` を測ると、
各 m 成分は `((dirac m).prod ν_m) S = ν_m {y | m ≠ c.decoder y} = ν_m (errorEvent m)
= errorProbAt m`。線形性で全体: `(1/M) ∑ m, errorProbAt m`。 -/
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
        (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i)))) S ≠ ∞ := by
    intro m
    have :
        ((Measure.dirac m).prod
          (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i)))) Set.univ ≤ 1 := by
      simp [measure_univ]
    exact ne_top_of_le_ne_top (by simp) (measure_mono (Set.subset_univ _) |>.trans this)
  -- Compute the Finset sum: unfold `.real` to `(·).toReal`, distribute.
  unfold Measure.real
  rw [Measure.finsetSum_apply _ _ S]
  rw [ENNReal.toReal_sum (fun m _ => h_fin_each m)]
  refine Finset.sum_congr rfl ?_
  intro m _
  congr 1
  -- Step 4: pointwise: `((dirac m).prod ν_m) S = ν_m (errorEvent m) = errorProbAt m`.
  -- `dirac_prod m : (dirac m).prod ν = map (Prod.mk m) ν`
  rw [Measure.dirac_prod]
  -- `(map (Prod.mk m) ν_m) S = ν_m ((Prod.mk m) ⁻¹' S)`.
  have hS_meas : MeasurableSet S := by
    -- `S = (fun ω => ω.1 = c.decoder ω.2)ᶜ ⊓ univ`. Use `measurableSet_setOf`.
    have h_pred : Measurable (fun ω : Fin M × (Fin n → ℝ) => (ω.1, c.decoder ω.2)) :=
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
    · intro h; exact fun h' => h h'.symm
    · intro h; exact fun h' => h h'.symm
  rw [h_preimage]
  -- `errorProbAt c.toCode W m = Measure.pi (W (c.encoder m i)) (errorEvent m)`.
  rfl

/-! ## Block-mixture output density (n-dim, finite codebook mixture)

`I(W; Y^n) ≠ ∞` / `I(X^n; Y^n) ≠ ∞` の genuine 化に必要な n 次元 mixture density 機構。
parallel-gaussian の `parallelOutputMixtureDensity*` を **finite codebook** 特化形に
lift (import cycle のため再利用不可、self-build)。block output `blockYLaw` は有限個の
codeword 上の n 次元積 Gaussian の mixture なので、concentration-box は不要 — sup 上界 +
**同一成分** 下界 (`blockDensity ≥ M⁻¹ · 成分 m の密度`) で `|log density|` を成分 m
中心の 2 次モーメント envelope に dominate できる (1-D `integrable_log_rnDeriv_perLetterYLaw`
の構造そのままの n 次元版)。 -/

/-- **Block output law** `I(·; Y^n)` の 2 番目周辺 `(awgnConverseJoint).map Prod.snd`。 -/
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
          ∑ m : Fin M, Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) := by
  classical
  unfold blockYLaw awgnConverseJoint
  have h_meas_snd :
      Measurable (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) := measurable_snd
  rw [Measure.map_smul,
    Measure.map_finset_sum (s := Finset.univ)
      (m := fun m => (Measure.dirac m).prod
        (Measure.pi (fun j : Fin n => awgnChannel N h_meas (c.encoder m j))))
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
    Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)
      = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
          (fun y => ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
  have h_each : ∀ i, gaussianReal (c.encoder m i) N
      = (MeasureTheory.volume : Measure ℝ).withDensity (gaussianPDF (c.encoder m i) N) :=
    fun i => gaussianReal_of_var_ne_zero (c.encoder m i) hN
  haveI : ∀ i, SigmaFinite ((MeasureTheory.volume : Measure ℝ).withDensity
      (gaussianPDF (c.encoder m i) N)) := by
    intro i; rw [← h_each i]; infer_instance
  rw [show (fun i : Fin n => gaussianReal (c.encoder m i) N)
        = (fun i => (MeasureTheory.volume : Measure ℝ).withDensity
            (gaussianPDF (c.encoder m i) N)) from funext h_each,
    InformationTheory.Shannon.pi_withDensity_fin (fun _ => (MeasureTheory.volume : Measure ℝ))
      (fun i => measurable_gaussianPDF (c.encoder m i) N), ← volume_pi]

/-- `blockYLaw = volume.withDensity (ofReal ∘ blockRealDensity)`. -/
private lemma blockYLaw_withDensity_real
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    blockYLaw h_meas c
      = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
          (fun y => ENNReal.ofReal (blockRealDensity N c y)) := by
  classical
  rw [blockYLaw_eq_mixture h_meas c]
  -- each component `pi (gaussianReal …) = volume.withDensity (∏ᵢ gaussianPDF …)`
  have h_comp := fun m : Fin M => blockComponent_withDensity hN c m
  -- distribute the finset sum over `withDensity`
  have h_sum : ∀ s : Finset (Fin M),
      (∑ m ∈ s, Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N))
        = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
            (fun y => ∑ m ∈ s, ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert m s hms ih =>
        have h_density_eq :
            (fun y : Fin n → ℝ => ∑ m' ∈ insert m s, ∏ i : Fin n, gaussianPDF (c.encoder m' i) N (y i))
              = (fun y : Fin n → ℝ => ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i))
                + (fun y : Fin n → ℝ => ∑ m' ∈ s, ∏ i : Fin n, gaussianPDF (c.encoder m' i) N (y i)) := by
          funext y; simp only [Pi.add_apply]; rw [Finset.sum_insert hms]
        rw [Finset.sum_insert hms, ih, h_comp m, h_density_eq]
        rw [withDensity_add_left
            (μ := (MeasureTheory.volume : Measure (Fin n → ℝ)))
            (f := fun y : Fin n → ℝ => ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i))
            (Finset.measurable_prod _ (fun i _ =>
              (measurable_gaussianPDF (c.encoder m i) N).comp (measurable_pi_apply i)))
            (fun y : Fin n → ℝ => ∑ m' ∈ s, ∏ i : Fin n, gaussianPDF (c.encoder m' i) N (y i))]
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
          (fun m _ => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _))]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)]
    refine Finset.prod_congr rfl (fun i _ => ?_)
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
  refine Finset.sum_pos (fun m _ => Finset.prod_pos (fun i _ => gaussianPDFReal_pos _ _ _ hN)) ?_
  exact ⟨m₀, Finset.mem_univ m₀⟩

/-- Measurability of `blockRealDensity`. -/
private lemma blockRealDensity_measurable
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} (c : AwgnCode M n P) :
    Measurable (blockRealDensity N c) := by
  unfold blockRealDensity
  refine measurable_const.mul ?_
  refine Finset.measurable_sum _ (fun m _ => ?_)
  exact Finset.measurable_prod _ (fun i _ =>
    (measurable_gaussianPDFReal (c.encoder m i) N).comp (measurable_pi_apply i))

/-- Per-component lower bound: `blockRealDensity y ≥ M⁻¹ · ∏ᵢ gaussianPDFReal (encoder m i) N (yᵢ)`. -/
private lemma blockRealDensity_ge_component
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) (y : Fin n → ℝ) :
    (1 / (M : ℝ)) * ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)
      ≤ blockRealDensity N c y := by
  unfold blockRealDensity
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine Finset.single_le_sum
    (f := fun m => ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i))
    (fun m _ => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _))
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
    refine Finset.prod_le_prod (fun i _ => gaussianPDFReal_nonneg _ _ _) (fun i _ => ?_)
    exact h_comp_le (c.encoder m i) (y i)
  -- mixture average of `M` terms each `≤ ∏ᵢ Bpeak`
  calc (1 / (M : ℝ)) * ∑ m : Fin M, ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)
      ≤ (1 / (M : ℝ)) * ∑ _m : Fin M, ∏ _i : Fin n, Bpeak := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum (fun m _ => h_prod_le m)
    _ = (1 / (M : ℝ)) * ((M : ℝ) * ∏ _i : Fin n, Bpeak) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ∏ _i : Fin n, Bpeak := by
        rcases Nat.eq_zero_or_pos M with hM0 | hMpos
        · exact absurd hM0 (NeZero.ne M)
        · have : (M : ℝ) ≠ 0 := by exact_mod_cast hMpos.ne'
          field_simp

/-- **Per-component output log-density integrability (n-dim).** For each codeword index
`m`, `log (blockYLaw.rnDeriv volume y)` is integrable against the m-th block component
`pi (gaussianReal (encoder m i) N)`. The mixture density is bounded above by the Gaussian
peak (so `log ≤ const`) and below by component `m` (so `-log ≤ ∑ᵢ (yᵢ − encoder m i)²/(2N)
+ const`); both sides are dominated by a finite-second-moment quadratic on the n-dim
Gaussian component. Lift of the 1-D `integrable_log_rnDeriv_perLetterYLaw`. -/
private lemma integrable_log_blockYLaw_on_component
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (m : Fin M) :
    Integrable
      (fun y => Real.log ((blockYLaw h_meas c).rnDeriv MeasureTheory.volume y).toReal)
      (Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)) := by
  classical
  set q := blockYLaw h_meas c with hq_def
  set νm := Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) with hνm_def
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
  haveI : ∀ i, IsProbabilityMeasure (gaussianReal (c.encoder m i) N) := fun i => inferInstance
  haveI hνm_prob : IsProbabilityMeasure νm := by rw [hνm_def]; infer_instance
  -- density form: `q = vol.withDensity (ofReal ∘ blockRealDensity)`
  have hq_wd : q = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
      (fun y => ENNReal.ofReal (blockRealDensity N c y)) := by
    rw [hq_def]; exact blockYLaw_withDensity_real hN h_meas c
  have hDR_meas : Measurable (fun y => ENNReal.ofReal (blockRealDensity N c y)) :=
    ENNReal.measurable_ofReal.comp (blockRealDensity_measurable c)
  -- `νm ≪ vol` (product of full-support Gaussians = withDensity of vol)
  have hνm_ac : νm ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := by
    rw [hνm_def, blockComponent_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  -- `q.rnDeriv vol =ᵐ[vol] ofReal ∘ blockRealDensity`, transport to `=ᵐ[νm]`
  have h_rn_vol : q.rnDeriv (MeasureTheory.volume : Measure (Fin n → ℝ))
      =ᵐ[(MeasureTheory.volume : Measure (Fin n → ℝ))]
      (fun y => ENNReal.ofReal (blockRealDensity N c y)) := by
    rw [hq_wd]; exact Measure.rnDeriv_withDensity _ hDR_meas
  have h_rn_νm : q.rnDeriv (MeasureTheory.volume : Measure (Fin n → ℝ))
      =ᵐ[νm] (fun y => ENNReal.ofReal (blockRealDensity N c y)) :=
    hνm_ac.ae_le h_rn_vol
  -- target integrand agrees a.e. with `log (blockRealDensity y)`
  have h_log_ae : (fun y => Real.log (q.rnDeriv MeasureTheory.volume y).toReal)
      =ᵐ[νm] (fun y => Real.log (blockRealDensity N c y)) := by
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
      ≤ blockRealDensity N c y := fun y => blockRealDensity_ge_component c m y
  -- the dominating function (n-dim quadratic), integrable against νm
  set c₀ : ℝ := -(1 / 2) * Real.log (2 * Real.pi * N) with hc₀
  set c₁ : ℝ := -(1 / (2 * (N : ℝ))) with hc₁
  set Aconst : ℝ := |Real.log (∏ _i : Fin n, Bpeak)|
      + |Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀| with hAconst
  set Bcoef : ℝ := |c₁| with hBcoef
  have h_dom : Integrable
      (fun y : Fin n → ℝ => Aconst + Bcoef * ∑ i : Fin n, (y i - c.encoder m i) ^ 2) νm := by
    refine (integrable_const Aconst).add (Integrable.const_mul ?_ Bcoef)
    -- `∑ᵢ (yᵢ - encoder m i)²` integrable against the product Gaussian νm
    rw [hνm_def]
    refine integrable_finsetSum _ (fun i _ => ?_)
    -- coordinate `i` integrable: lift the 1-D second-moment integrability via `integrable_comp_eval`
    have h_1d : Integrable (fun y : ℝ => (y - c.encoder m i) ^ 2)
        (gaussianReal (c.encoder m i) N) := by
      have h_id : Integrable (fun y : ℝ => y) (gaussianReal (c.encoder m i) N) := by
        simpa using (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 1).integrable (by norm_num)
      have h_sq : Integrable (fun y : ℝ => y ^ 2) (gaussianReal (c.encoder m i) N) :=
        (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 2).integrable_sq
      have hrw : (fun y : ℝ => (y - c.encoder m i) ^ 2)
          = fun y => y ^ 2 - 2 * (c.encoder m i) * y + (c.encoder m i) ^ 2 := by funext y; ring
      rw [hrw]
      exact ((h_sq.sub (h_id.const_mul (2 * c.encoder m i))).add
        (integrable_const ((c.encoder m i) ^ 2)))
    exact integrable_comp_eval (μ := fun i : Fin n => gaussianReal (c.encoder m i) N)
      (i := i) h_1d
  refine Integrable.mono' h_dom ?_ ?_
  · exact (Real.measurable_log.comp (blockRealDensity_measurable c)).aestronglyMeasurable
  · filter_upwards with y
    have hDy_pos : 0 < blockRealDensity N c y := blockRealDensity_pos hN c y
    set S : ℝ := ∑ i : Fin n, (y i - c.encoder m i) ^ 2 with hS
    have hS_nonneg : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hc₁_nonpos : c₁ ≤ 0 := by rw [hc₁]; simp only [neg_nonpos]; positivity
    -- upper: log (blockRealDensity y) ≤ log (∏ᵢ Bpeak)
    have h_upper : Real.log (blockRealDensity N c y) ≤ Real.log (∏ _i : Fin n, Bpeak) := by
      have h_prod_pos : (0 : ℝ) < ∏ _i : Fin n, Bpeak := Finset.prod_pos (fun _ _ => hBpeak_pos)
      exact Real.log_le_log hDy_pos (hD_le y)
    -- lower: log (blockRealDensity y) ≥ log (M⁻¹) + n·c₀ + c₁·S
    have h_lower : Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀ + c₁ * S
        ≤ Real.log (blockRealDensity N c y) := by
      have hMinv_pos : (0 : ℝ) < 1 / (M : ℝ) := by positivity
      have hprod_pos : (0 : ℝ) < ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i) :=
        Finset.prod_pos (fun i _ => gaussianPDFReal_pos _ _ _ hN)
      have h_log_prod : Real.log ((1 / (M : ℝ)) * ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i))
          = Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀ + c₁ * S := by
        rw [Real.log_mul hMinv_pos.ne' hprod_pos.ne', Real.log_prod (fun i _ =>
          (gaussianPDFReal_pos (c.encoder m i) N (y i) hN).ne')]
        have h_each : ∀ i : Fin n, Real.log (gaussianPDFReal (c.encoder m i) N (y i))
            = c₀ + c₁ * (y i - c.encoder m i) ^ 2 := by
          intro i
          rw [InformationTheory.Shannon.log_gaussianPDFReal_eq (c.encoder m i) hN (y i), hc₀, hc₁]
          ring
        rw [Finset.sum_congr rfl (fun i _ => h_each i), hS, Finset.sum_add_distrib,
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

/-! ### I(W; Y^n) finiteness via the discrete-input compProd chain rule

`W = Fin M` (discrete) のため joint は `(M⁻¹•count) ⊗ₘ K` (K m := n 次元 block component),
marginal 積は `(M⁻¹•count) ⊗ₘ const blockY`。`klDiv_ne_top_iff` (AC + integrable llr) を
`absolutelyContinuous_compProd_iff` + `integrable_llr_compProd_iff` で per-fibre に落とし、
fibre 部 = 各成分の output log-density integrability (`integrable_log_blockYLaw_on_component`)
+ Gaussian fibre log-density integrability で genuine に閉じる。 -/

/-- Discrete-input block kernel `K m := pi (gaussianReal (encoder m i) N)` (Fin M → Y^n)。 -/
private noncomputable def blockKernel
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) :
    Kernel (Fin M) (Fin n → ℝ) :=
  { toFun := fun m => Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)
    measurable' := measurable_of_countable _ }

private instance blockKernel_isMarkov
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} (c : AwgnCode M n P) :
    IsMarkovKernel (blockKernel N c) :=
  ⟨fun m => by
    show IsProbabilityMeasure (Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N))
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
        (fun a : Fin M => Measure.dirac a),
    Measure.compProd_sum_left, Measure.sum_fintype]
  symm
  refine Finset.sum_congr rfl (fun m _ => ?_)
  -- `(δ_m) ⊗ₘ K = (δ_m).prod (K m) = (δ_m).prod νₘ` (`K m = νₘ`, `awgnChannel = gaussianReal` defeq)
  rw [show (Measure.dirac m) ⊗ₘ blockKernel N c
        = (Measure.dirac m).prod (blockKernel N c m) by
      ext s hs
      rw [Measure.dirac_compProd_apply hs, Measure.dirac_prod,
        Measure.map_apply measurable_prodMk_left hs]]
  refine congrArg ((Measure.dirac m).prod) ?_
  show Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))
      = Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)
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
    Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) ≪ blockYLaw h_meas c := by
  -- `νₘ ≪ vol ≪ blockYLaw`
  have h1 : Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)
      ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := by
    rw [blockComponent_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have h2 : (MeasureTheory.volume : Measure (Fin n → ℝ)) ≪ blockYLaw h_meas c := by
    rw [blockYLaw_withDensity_real hN h_meas c]
    refine withDensity_absolutelyContinuous'
      (ENNReal.measurable_ofReal.comp (blockRealDensity_measurable c)).aemeasurable ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
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
      (fun y => Real.log
        ((Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)).rnDeriv
          (blockYLaw h_meas c) y).toReal)
      (Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)) := by
  classical
  set νm := Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) with hνm
  set q := blockYLaw h_meas c with hq
  haveI : ∀ i, IsProbabilityMeasure (gaussianReal (c.encoder m i) N) := fun i => inferInstance
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
      =ᵐ[νm] (fun y => ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
    have h_wd : νm = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
        (fun y => ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
      rw [hνm]; exact blockComponent_withDensity hN c m
    have h_meas_dens : Measurable (fun y : Fin n → ℝ => ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) :=
      Finset.measurable_prod _ (fun i _ =>
        (measurable_gaussianPDF (c.encoder m i) N).comp (measurable_pi_apply i))
    exact hνm_vol.ae_le (by rw [h_wd]; exact Measure.rnDeriv_withDensity _ h_meas_dens)
  have h_log_νm_vol_ae : (fun y => Real.log (νm.rnDeriv (MeasureTheory.volume) y).toReal)
      =ᵐ[νm] (fun y => ∑ i : Fin n,
          (-(1 / 2) * Real.log (2 * Real.pi * N) - (y i - c.encoder m i) ^ 2 / (2 * (N : ℝ)))) := by
    filter_upwards [h_rn_νm_vol] with y hy
    rw [hy, ENNReal.toReal_prod]
    simp_rw [toReal_gaussianPDF]
    rw [Real.log_prod (fun i _ => (gaussianPDFReal_pos (c.encoder m i) N (y i) hN).ne')]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [InformationTheory.Shannon.log_gaussianPDFReal_eq (c.encoder m i) hN (y i)]
  have h_int_νm_vol : Integrable
      (fun y => Real.log (νm.rnDeriv (MeasureTheory.volume) y).toReal) νm := by
    refine Integrable.congr ?_ h_log_νm_vol_ae.symm
    refine integrable_finsetSum _ (fun i _ => ?_)
    -- each `(-(1/2)log(2πN) - (yᵢ - encoder m i)²/(2N))` integrable against νm
    refine (integrable_const _).sub ?_
    have h_1d : Integrable (fun y : ℝ => (y - c.encoder m i) ^ 2 / (2 * (N : ℝ)))
        (gaussianReal (c.encoder m i) N) := by
      have h_id : Integrable (fun y : ℝ => y) (gaussianReal (c.encoder m i) N) := by
        simpa using (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 1).integrable (by norm_num)
      have h_sq : Integrable (fun y : ℝ => y ^ 2) (gaussianReal (c.encoder m i) N) :=
        (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 2).integrable_sq
      have hrw : (fun y : ℝ => (y - c.encoder m i) ^ 2 / (2 * (N : ℝ)))
          = fun y => (y ^ 2 - 2 * (c.encoder m i) * y + (c.encoder m i) ^ 2) / (2 * (N : ℝ)) := by
        funext y; ring
      rw [hrw]
      exact (((h_sq.sub (h_id.const_mul (2 * c.encoder m i))).add
        (integrable_const ((c.encoder m i) ^ 2))).div_const _)
    rw [hνm]
    exact integrable_comp_eval (μ := fun i : Fin n => gaussianReal (c.encoder m i) N) (i := i) h_1d
  -- (B) `log (q.rnDeriv vol)` integrable against νm: `integrable_log_blockYLaw_on_component`.
  have h_int_q_vol : Integrable
      (fun y => Real.log (q.rnDeriv (MeasureTheory.volume) y).toReal) νm := by
    rw [hq, hνm]; exact integrable_log_blockYLaw_on_component hN h_meas c m
  -- chain rule split: `log (νm.rnDeriv q) =ᵐ[νm] log(νm.rnDeriv vol) − log(q.rnDeriv vol)`
  have h_split : (fun y => Real.log (νm.rnDeriv q y).toReal)
      =ᵐ[νm] (fun y => Real.log (νm.rnDeriv (MeasureTheory.volume) y).toReal
                - Real.log (q.rnDeriv (MeasureTheory.volume) y).toReal) := by
    have h_chain : (fun y => νm.rnDeriv q y * q.rnDeriv (MeasureTheory.volume) y)
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

/-- **I(W; Y^n) finiteness (genuine).** -/
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
      (fun ω : Fin M × (Fin n → ℝ) => (ω.1, ω.2)) = msgLaw M ⊗ₘ blockKernel N c := by
    rw [show (fun ω : Fin M × (Fin n → ℝ) => (ω.1, ω.2)) = id from rfl, Measure.map_id]
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
    have h_llr_ae : (fun p => llr (msgLaw M ⊗ₘ K) (msgLaw M ⊗ₘ ηc) p)
        =ᵐ[msgLaw M ⊗ₘ K]
        (fun p : Fin M × (Fin n → ℝ) => Real.log ((K.rnDeriv ηc p.1 p.2)).toReal) := by
      -- linchpin: joint rnDeriv =ᵐ[μ⊗ₘη] fibre kernel rnDeriv; transport to a.e. on the joint
      have h1 : (msgLaw M ⊗ₘ K).rnDeriv (msgLaw M ⊗ₘ ηc)
          =ᵐ[msgLaw M ⊗ₘ K] fun p => K.rnDeriv ηc p.1 p.2 :=
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
      have h_fibre_ae : (fun y => Real.log ((K.rnDeriv ηc m y)).toReal)
          =ᵐ[K m] (fun y => Real.log (((K m).rnDeriv (blockYLaw h_meas c) y)).toReal) := by
        have hKm_blockY : K m ≪ blockYLaw h_meas c := by
          show Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) ≪ blockYLaw h_meas c
          exact blockComponent_ac_blockYLaw hN h_meas c m
        have h_meas_eq : K m ≪ ηc m := by rw [hηc, Kernel.const_apply]; exact hKm_blockY
        filter_upwards [h_meas_eq.ae_le
          (Kernel.rnDeriv_eq_rnDeriv_measure (κ := K) (η := ηc) (a := m))] with y hy
        rw [hy]; simp only [hηc, Kernel.const_apply]
      refine Integrable.congr ?_ h_fibre_ae.symm
      show Integrable
        (fun y => Real.log
          ((Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)).rnDeriv
            (blockYLaw h_meas c) y).toReal)
        (Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N))
      exact integrable_log_component_rnDeriv_blockYLaw hN h_meas c m
    · -- L¹-norm-over-fibre integral integrable over the finite message measure
      exact Integrable.of_finite

/-- **AWGN converse MI finiteness (genuine, formerly `wall:multivariate-mi`)**.

`I(W; Y^n) ≠ ∞` ∧ `I(X^n; Y^n) ≠ ∞` on the AWGN converse canonical joint.

**2026-06-12 genuine 化 (false wall 反証, `cause:loogle-blind` + `cause:single-route`)**:
旧 docstring の「continuous-Y llr
integrability は substantial plumbing beyond scope」「ENNReal chain rule が circular」
は **Real-form chain rule から ne_top を導こうとした場合の話**。本実装は直接
`klDiv_ne_top` (AC + integrable llr 直構築) ルートで循環を回避。`W` (Fin M, discrete) /
`X^n` (encoder∘fst, finite-valued) のため joint は有限個の codeword 上の n 次元積
Gaussian mixture、各成分 `klDiv νₘ blockYLaw < ∞` を sup 上界 + 同一成分下界で genuine 化
(parallel-gaussian `parallelOutput_joint_logDensity_integrable` 手法の finite-codebook
特化形)。`N = 0` は退化 (joint が対角 graph 上 singular → klDiv=∞ で偽) のため
`hN : N ≠ 0` を guard として追加。 -/
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
        (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1) Prod.snd (henc.comp hfst) hsnd]
    have h_pp :
        mutualInfo (awgnConverseJoint h_meas c) Prod.snd (c.encoder ∘ Prod.fst)
          ≤ mutualInfo (awgnConverseJoint h_meas c) Prod.snd Prod.fst :=
      mutualInfo_le_of_postprocess (awgnConverseJoint h_meas c) Prod.snd Prod.fst hsnd hfst henc
    rw [show (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1)
          = c.encoder ∘ Prod.fst from rfl]
    refine h_pp.trans ?_
    rw [mutualInfo_comm (awgnConverseJoint h_meas c) Prod.snd Prod.fst hsnd hfst]
  exact ne_top_of_le_ne_top h_W h_le

/-- AWGN converse の `mutualInfo` finiteness: `mutualInfo (awgnConverseJoint c) Prod.fst Prod.snd ≠ ∞`。

`awgnConverseJoint_pair_mi_ne_top` 経由 (共有 wall lemma の `.1`)。本 declaration
は **0-sorry / 0-@residual**、wall 自体は shared lemma に集約。 -/
private lemma awgnConverseJoint_mutualInfo_ne_top
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    mutualInfo (awgnConverseJoint h_meas c)
        (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
        (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) ≠ ∞ :=
  (awgnConverseJoint_pair_mi_ne_top hN h_meas c).1

/-- **Phase B-Fano**: Fano + DPI postprocess + entropy chain + `H(W) = log M` を
`shannon_converse_single_shot` 1 行呼出で集約。

結論: `log M ≤ I(W; Y^n).toReal + binEntropy(Pe) + Pe · log(M-1)`。

Pe bridge (T-FFC-5、`errorProbAt` ↔ Fano `errorProb` の同値性、private helper
`awgn_errorProb_eq_fano_errorProb` に切出し) + MI-finite plumbing (private helper
`awgnConverseJoint_mutualInfo_ne_top` に切出し) を経由。 -/
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

/-! ## Phase B-DPI/chain

DPI side: `mutualInfo_le_of_markov` (`CondMutualInfo.lean:385`) で
`I(W; Y^n) ≤ I(X^n; Y^n)` を導く (Markov factorization は shared sorry 補題
`awgnConverseMarkov_holds`、`AwgnWalls.lean`)。
Chain side: shared sorry 補題 `awgnContinuousMIChainRule_holds` (`AwgnWalls.lean`)
を defeq で接続。 -/

/-- **Phase B-DPI**: Markov chain `W → encoder ∘ W → Y^n` から
`I(W; Y^n) ≤ I(X^n; Y^n)` を `mutualInfo_le_of_markov` (genuine、判断 #3) で導く。

Markov factorization は genuine 補題 `awgnConverseMarkov_holds`
(`AwgnWalls.lean`、旧 wall `awgn-converse-markov-regularity` は closed 2026-06-04、
`@audit:ok`、sorryAx-free) から取得 (`converseJointInline` ≡ `awgnConverseJoint` defeq
で接続)。 -/
@[entry_point]
theorem awgn_dpi
    (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    (jointMIWYn h_meas c).toReal ≤ (jointMIXnYn h_meas c).toReal := by
  -- Markov chain `W → X^n → Y^n` (γ-form) ⇒ ENNReal DPI
  -- `mutualInfo W Y^n ≤ mutualInfo X^n Y^n`.
  -- shared sorry 補題から Markov factorization を取得 (defeq で
  -- `IsMarkovChain (awgnConverseJoint …)` に接続)。
  have h_markov :
      IsMarkovChain (awgnConverseJoint h_meas c)
        (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
        (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1)
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
  have hXn_meas : Measurable (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1) :=
    hEnc_const.comp hW_meas
  -- ENNReal DPI via `mutualInfo_le_of_markov`.
  have h_dpi_enn :
      mutualInfo (awgnConverseJoint h_meas c) Prod.fst Prod.snd ≤
        mutualInfo (awgnConverseJoint h_meas c)
          (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1) Prod.snd :=
    mutualInfo_le_of_markov (μ := awgnConverseJoint h_meas c)
      (Xs := Prod.fst) (Zc := fun ω => c.encoder ω.1) (Yo := Prod.snd)
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

/-- **Phase B-chain**: continuous MI chain rule for memoryless AWGN
`I(X^n; Y^n) ≤ ∑ᵢ I(X_i; Y_i)`。shared sorry 補題
`awgnContinuousMIChainRule_holds` (`AwgnWalls.lean`、wall
`awgn-continuous-mi-chain-rule`) から取得 (`converseJointInline` ≡ `awgnConverseJoint`
defeq、`jointMIXnYn` / `perLetterMI` unfold で結論一致)。 -/
@[entry_point]
theorem awgn_chain_rule
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) :
    (jointMIXnYn h_meas c).toReal ≤ ∑ i : Fin n, (perLetterMI h_meas c i).toReal :=
  awgnContinuousMIChainRule_holds h_meas c

/-! ## Phase C — Per-letter input second moment / Jensen / sum-form chain
(Phase B-Gaussian 撤回後の再設計、`awgn-converse-aux-plan.md` Phase C 反映)。

旧 `awgn_per_letter_mi_le_capacity` (per-letter `E[X_i²] ≤ P` 形、`power_constraint`
per-message 形からは genuine 化不能の false-statement defect) は本 commit で撤回し、
代わりに **sum-form + Jensen** で `∑ᵢ I(X_i; Y_i) ≤ n · (1/2) log(1+P/N)` を直接立てる。 -/

/-- Per-letter input second moment `E[X_i² | W ∼ Uniform(Fin M)]
= (1/M) ∑_m (c.encoder m i)²`。Uniform message 上で input letter `X_i = c.encoder W i`
の 2 次モーメント。`power_constraint` (per-message block 形) と `1/n ∑_i` avg で
`(1/n) ∑_i perLetterInputSecondMoment c i ≤ P` が genuine に出る (`awgn_per_letter_input_power_avg`)。 -/
@[entry_point]
noncomputable def perLetterInputSecondMoment
    {M n : ℕ} {P : ℝ} (c : AwgnCode M n P) (i : Fin n) : ℝ :=
  (1 / (M : ℝ)) * ∑ m : Fin M, (c.encoder m i) ^ 2

/-- **C-1a** Average of per-letter input second moments is bounded by `P`.

`(1/n) ∑ᵢ E[X_i²] ≤ P` を `power_constraint` (per-message form `∑ᵢ (encoder m i)² ≤ n·P`)
から Fubini swap (∑ᵢ ∑ₘ = ∑ₘ ∑ᵢ) で genuine 化。 -/
@[entry_point]
theorem awgn_per_letter_input_power_avg
    {M n : ℕ} (hM_pos : 0 < M) (hn_pos : 0 < n) {P : ℝ}
    (c : AwgnCode M n P) :
    (1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i ≤ P := by
  -- Unfold the per-letter second-moment definition.
  unfold perLetterInputSecondMoment
  -- Bring the `(1/M)` constant out of `∑ i`.
  have h_pull_M :
      (∑ i : Fin n, (1 / (M : ℝ)) * ∑ m : Fin M, (c.encoder m i) ^ 2)
        = (1 / (M : ℝ)) * ∑ i : Fin n, ∑ m : Fin M, (c.encoder m i) ^ 2 := by
    rw [← Finset.mul_sum]
  rw [h_pull_M]
  -- Fubini swap: `∑ i ∑ m = ∑ m ∑ i`.
  rw [Finset.sum_comm]
  -- Apply `power_constraint` term-by-term inside the inner sum.
  have h_power_each : ∀ m : Fin M, (∑ i : Fin n, (c.encoder m i) ^ 2) ≤ (n : ℝ) * P :=
    c.power_constraint
  -- Bound the inner double sum by `M · (n · P)`.
  have h_sum_bound :
      (∑ m : Fin M, ∑ i : Fin n, (c.encoder m i) ^ 2)
        ≤ ∑ _m : Fin M, (n : ℝ) * P := by
    apply Finset.sum_le_sum
    intro m _
    exact h_power_each m
  have h_const_sum :
      (∑ _m : Fin M, (n : ℝ) * P) = (M : ℝ) * ((n : ℝ) * P) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [h_const_sum] at h_sum_bound
  -- Now: (1/n) * ((1/M) * (something ≤ M·n·P)) ≤ P.
  have hM_real : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
  have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  -- Step: pull `(1/n)` past `(1/M) * ...`.
  have h_combine :
      (1 / (n : ℝ)) * ((1 / (M : ℝ)) *
          (∑ m : Fin M, ∑ i : Fin n, (c.encoder m i) ^ 2))
        ≤ (1 / (n : ℝ)) * ((1 / (M : ℝ)) * ((M : ℝ) * ((n : ℝ) * P))) := by
    have h_inner : (1 / (M : ℝ)) *
          (∑ m : Fin M, ∑ i : Fin n, (c.encoder m i) ^ 2)
        ≤ (1 / (M : ℝ)) * ((M : ℝ) * ((n : ℝ) * P)) := by
      apply mul_le_mul_of_nonneg_left h_sum_bound
      positivity
    apply mul_le_mul_of_nonneg_left h_inner
    positivity
  -- Simplify the RHS to `P`.
  have h_rhs : (1 / (n : ℝ)) * ((1 / (M : ℝ)) * ((M : ℝ) * ((n : ℝ) * P))) = P := by
    field_simp
  rw [h_rhs] at h_combine
  exact h_combine

/-! ### Private helpers for `awgn_per_letter_mi_le_log_var` (C-1b) -/

/-- Closed form of `perLetterYLaw`: mixture of Gaussians
`(M⁻¹ : ℝ≥0∞) • ∑ₘ gaussianReal (c.encoder m i) N`. -/
private lemma perLetterYLaw_eq_mixture
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    perLetterYLaw h_meas c i
      = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ •
          ∑ m : Fin M, gaussianReal (c.encoder m i) N := by
  classical
  unfold perLetterYLaw awgnConverseJoint
  -- map distributes over smul and finset sum.
  have h_meas_eval :
      Measurable (fun ω : Fin M × (Fin n → ℝ) => ω.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  rw [Measure.map_smul]
  rw [Measure.map_finset_sum (s := Finset.univ)
      (m := fun m => (Measure.dirac m).prod
        (Measure.pi (fun j : Fin n => awgnChannel N h_meas (c.encoder m j))))
      h_meas_eval.aemeasurable]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro m _
  -- ((dirac m).prod ν).map (fun ω => ω.2 i)
  --   = (ν.map (fun y => y i))                 -- via map_snd_prod ∘ map_eval composition
  --   = gaussianReal (c.encoder m i) N
  have h_meas_snd :
      Measurable (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) := measurable_snd
  have h_meas_eval_i :
      Measurable (Function.eval i : (Fin n → ℝ) → ℝ) := measurable_pi_apply i
  have h_decomp : (fun ω : Fin M × (Fin n → ℝ) => ω.2 i)
      = (Function.eval i) ∘ Prod.snd := rfl
  rw [h_decomp]
  rw [← Measure.map_map h_meas_eval_i h_meas_snd]
  -- Map of `Prod.snd` first.
  rw [Measure.map_snd_prod]
  -- dirac univ = 1, so `(dirac m univ) • Measure.pi ν = Measure.pi ν`.
  have h_dirac_univ : (Measure.dirac m : Measure (Fin M)) Set.univ = 1 := by
    simp
  rw [h_dirac_univ, one_smul]
  -- Now: `(Measure.pi ν).map (Function.eval i) = gaussianReal (c.encoder m i) N`.
  rw [Measure.pi_map_eval]
  -- Each `μ j Set.univ = 1` because `gaussianReal` is a probability measure.
  have h_other : ∀ j ∈ Finset.univ.erase i,
      (awgnChannel N h_meas (c.encoder m j)) Set.univ = 1 := by
    intro j _
    rw [awgnChannel_apply]
    exact measure_univ
  rw [Finset.prod_congr rfl h_other, Finset.prod_const_one, one_smul]
  rw [awgnChannel_apply]

/-- Probability measure structure of `perLetterYLaw`. -/
private lemma perLetterYLaw_isProbabilityMeasure
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    IsProbabilityMeasure (perLetterYLaw h_meas c i) := by
  unfold perLetterYLaw
  have h_meas_eval :
      Measurable (fun ω : Fin M × (Fin n → ℝ) => ω.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  exact Measure.isProbabilityMeasure_map h_meas_eval.aemeasurable

/-- Absolute continuity of `perLetterYLaw` w.r.t. Lebesgue volume,
needed for `differentialEntropy_le_gaussian_of_variance_le`. -/
private lemma perLetterYLaw_absolutelyContinuous
    {P : ℝ} {N : ℝ≥0} (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    perLetterYLaw h_meas c i ≪ MeasureTheory.volume := by
  classical
  have hN_ne : N ≠ 0 := by
    intro h; apply hN; exact_mod_cast h
  rw [perLetterYLaw_eq_mixture h_meas c i]
  -- each `gaussianReal (c.encoder m i) N ≪ volume`, finset sum AC ⇒ smul AC.
  refine Measure.AbsolutelyContinuous.smul_left ?_ _
  -- Convert finset sum to `Measure.sum` to apply `absolutelyContinuous_sum_left`.
  rw [← Measure.sum_fintype]
  exact Measure.absolutelyContinuous_sum_left fun m =>
    gaussianReal_absolutelyContinuous _ hN_ne

/-- Integral against `perLetterYLaw`: linearity over the mixture. -/
private lemma perLetterYLaw_integral
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n)
    {f : ℝ → ℝ} (hf : ∀ m : Fin M, Integrable f (gaussianReal (c.encoder m i) N)) :
    ∫ x, f x ∂(perLetterYLaw h_meas c i)
      = (1 / (M : ℝ)) * ∑ m : Fin M, ∫ x, f x ∂(gaussianReal (c.encoder m i) N) := by
  classical
  rw [perLetterYLaw_eq_mixture h_meas c i]
  rw [integral_smul_measure]
  -- Now goal: (M⁻¹ : ℝ≥0∞).toReal • ∫ f ∂(∑ m, gaussianReal ...) = (1/M) * ∑ m, ∫ ...
  rw [integral_finsetSum_measure (fun m _ => hf m)]
  rw [Fintype.card_fin]
  -- `(M⁻¹ : ℝ≥0∞).toReal = 1/M` and scalar smul on ℝ is just mul.
  have h_inv : ((M : ℝ≥0∞)⁻¹).toReal = 1 / (M : ℝ) := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
  rw [h_inv]
  show (1 / (M : ℝ)) • (∑ m : Fin M, ∫ x, f x ∂(gaussianReal (c.encoder m i) N))
      = (1 / (M : ℝ)) * (∑ m : Fin M, ∫ x, f x ∂(gaussianReal (c.encoder m i) N))
  rw [smul_eq_mul]

/-- The per-letter mean of `Y_i`: equals the average of encoder values. -/
private lemma perLetterYLaw_mean
    {P : ℝ} {N : ℝ≥0} (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    ∫ x, x ∂(perLetterYLaw h_meas c i)
      = (1 / (M : ℝ)) * ∑ m : Fin M, c.encoder m i := by
  have h_int : ∀ m : Fin M, Integrable (fun x : ℝ => x) (gaussianReal (c.encoder m i) N) := by
    intro m
    have : MemLp (id : ℝ → ℝ) 1 (gaussianReal (c.encoder m i) N) :=
      memLp_id_gaussianReal' 1 ENNReal.one_ne_top
    exact (memLp_one_iff_integrable.mp this)
  rw [perLetterYLaw_integral h_meas c i h_int]
  simp_rw [integral_id_gaussianReal]

/-- Per-letter integrability of `(x - m)²` against each mixture component. -/
private lemma gaussianReal_integrable_sub_sq (a : ℝ) {N : ℝ≥0} (m : ℝ) :
    Integrable (fun x : ℝ => (x - m) ^ 2) (gaussianReal a N) := by
  -- `id - const m` is `MemLp 2` via `memLp_id_gaussianReal 2` minus a constant.
  have h_id : MemLp (id : ℝ → ℝ) 2 (gaussianReal a N) :=
    memLp_id_gaussianReal' 2 ENNReal.ofNat_ne_top
  have h_sub : MemLp (fun x : ℝ => x - m) 2 (gaussianReal a N) := by
    have := h_id.sub (memLp_const m)
    simpa using this
  exact h_sub.integrable_sq

/-- Integrability of `(x - m)²` against `perLetterYLaw`. -/
private lemma perLetterYLaw_var_integrable
    {P : ℝ} {N : ℝ≥0} (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) (m : ℝ) :
    Integrable (fun x : ℝ => (x - m) ^ 2) (perLetterYLaw h_meas c i) := by
  classical
  rw [perLetterYLaw_eq_mixture h_meas c i]
  -- Goal: Integrable f (M⁻¹ • ∑ k, gaussianReal (c.encoder k i) N)
  have hM_ne_zero : (Fintype.card (Fin M) : ℝ≥0∞) ≠ 0 := by
    rw [Fintype.card_fin]
    exact_mod_cast (NeZero.ne M)
  have hM_inv_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr hM_ne_zero
  refine Integrable.smul_measure ?_ hM_inv_ne_top
  -- Goal: Integrable f (∑ k, gaussianReal (c.encoder k i) N)
  rw [integrable_finsetSum_measure]
  intro k _
  exact gaussianReal_integrable_sub_sq (c.encoder k i) m

/-- Second moment around an arbitrary point `m_avg` for a real Gaussian:
`∫ (x - m_avg)² ∂(gaussianReal a N) = (a - m_avg)² + N`. -/
private lemma gaussianReal_integral_sub_sq
    (a : ℝ) {N : ℝ≥0} (m_avg : ℝ) :
    ∫ x, (x - m_avg) ^ 2 ∂(gaussianReal a N)
      = (a - m_avg) ^ 2 + (N : ℝ) := by
  -- Define f x := (x - m_avg)² and rewrite the integral via the decomposition
  -- (x - m_avg)² = (x - a)² + 2(x - a)(a - m_avg) + (a - m_avg)².
  have h_int_id : Integrable (fun x : ℝ => x) (gaussianReal a N) := by
    have : MemLp (id : ℝ → ℝ) 1 (gaussianReal a N) :=
      memLp_id_gaussianReal' 1 ENNReal.one_ne_top
    exact (memLp_one_iff_integrable.mp this)
  have h_int1 : Integrable (fun x : ℝ => (x - a) ^ 2) (gaussianReal a N) :=
    gaussianReal_integrable_sub_sq a a
  have h_int_xa : Integrable (fun x : ℝ => x - a) (gaussianReal a N) :=
    h_int_id.sub (integrable_const a)
  -- Rewrite integrand pointwise via `integral_congr`.
  have h_eq_fun :
      (fun x : ℝ => (x - m_avg) ^ 2)
        = (fun x : ℝ => (x - a) ^ 2 + 2 * (x - a) * (a - m_avg) + (a - m_avg) ^ 2) := by
    funext x; ring
  rw [h_eq_fun]
  have h_int2 : Integrable (fun x : ℝ => 2 * (x - a) * (a - m_avg)) (gaussianReal a N) := by
    have h_lin : Integrable (fun x : ℝ => 2 * (x - a)) (gaussianReal a N) := by
      simpa [mul_comm] using h_int_xa.const_mul 2
    simpa [mul_assoc] using h_lin.mul_const (a - m_avg)
  have h_int3 : Integrable (fun _ : ℝ => (a - m_avg) ^ 2) (gaussianReal a N) :=
    integrable_const _
  -- Split integral by linearity.
  have h_sum_step1 :
      ∫ x, ((x - a) ^ 2 + 2 * (x - a) * (a - m_avg)) + (a - m_avg) ^ 2 ∂(gaussianReal a N)
        = ∫ x, ((x - a) ^ 2 + 2 * (x - a) * (a - m_avg)) ∂(gaussianReal a N)
          + ∫ _, (a - m_avg) ^ 2 ∂(gaussianReal a N) :=
    integral_add (h_int1.add h_int2) h_int3
  have h_sum_step2 :
      ∫ x, (x - a) ^ 2 + 2 * (x - a) * (a - m_avg) ∂(gaussianReal a N)
        = ∫ x, (x - a) ^ 2 ∂(gaussianReal a N)
          + ∫ x, 2 * (x - a) * (a - m_avg) ∂(gaussianReal a N) :=
    integral_add h_int1 h_int2
  rw [h_sum_step1, h_sum_step2]
  -- 1) ∫ (x - a)² ∂(gaussianReal a N) = N via `variance_fun_id_gaussianReal`.
  have h_var_eq : ∫ x, (x - a) ^ 2 ∂(gaussianReal a N) = (N : ℝ) := by
    have h_var := variance_fun_id_gaussianReal (μ := a) (v := N)
    rw [variance_eq_integral measurable_id'.aemeasurable] at h_var
    simp only [integral_id_gaussianReal] at h_var
    exact h_var
  -- 2) ∫ 2(x - a)(a - m_avg) ∂(gaussianReal a N) = 0 since mean = a.
  have h_lin_zero : ∫ x, 2 * (x - a) * (a - m_avg) ∂(gaussianReal a N) = 0 := by
    have h_factor : (fun x : ℝ => 2 * (x - a) * (a - m_avg))
        = (fun x : ℝ => (2 * (a - m_avg)) * (x - a)) := by
      funext x; ring
    rw [h_factor, integral_const_mul]
    have h_mean_zero : ∫ x, (x - a) ∂(gaussianReal a N) = 0 := by
      rw [integral_sub h_int_id (integrable_const a)]
      rw [integral_id_gaussianReal, integral_const]
      simp
    rw [h_mean_zero, mul_zero]
  -- 3) ∫ (a - m_avg)² ∂(prob) = (a - m_avg)² since gaussianReal is a probability measure.
  have h_const_eq : ∫ _, (a - m_avg) ^ 2 ∂(gaussianReal a N) = (a - m_avg) ^ 2 := by
    rw [integral_const]; simp
  rw [h_var_eq, h_lin_zero, h_const_eq]
  ring

/-- Variance bound for `perLetterYLaw`: `∫ (x - m_avg)² ∂μ ≤ E[X_i²] + N`. -/
private lemma perLetterYLaw_variance_le
    {P : ℝ} {N : ℝ≥0} (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    ∫ x, (x - ((1 / (M : ℝ)) * ∑ m : Fin M, c.encoder m i)) ^ 2
        ∂(perLetterYLaw h_meas c i)
      ≤ perLetterInputSecondMoment c i + (N : ℝ) := by
  classical
  set m_avg : ℝ := (1 / (M : ℝ)) * ∑ k : Fin M, c.encoder k i with hm_avg_def
  -- Step 1: distribute integral via mixture.
  have h_int_mix :
      ∫ x, (x - m_avg) ^ 2 ∂(perLetterYLaw h_meas c i)
        = (1 / (M : ℝ)) * ∑ k : Fin M,
            ∫ x, (x - m_avg) ^ 2 ∂(gaussianReal (c.encoder k i) N) :=
    perLetterYLaw_integral h_meas c i (fun k =>
      gaussianReal_integrable_sub_sq (c.encoder k i) m_avg)
  rw [h_int_mix]
  -- Step 2: each summand simplifies to `(c.encoder k i - m_avg)² + N`.
  have h_each : ∀ k : Fin M,
      ∫ x, (x - m_avg) ^ 2 ∂(gaussianReal (c.encoder k i) N)
        = (c.encoder k i - m_avg) ^ 2 + (N : ℝ) := fun k =>
    gaussianReal_integral_sub_sq (c.encoder k i) m_avg
  simp_rw [h_each]
  -- Step 3: split sum = ∑ (...)² + ∑ N = (∑ (...)²) + M·N.
  rw [Finset.sum_add_distrib]
  -- Constant sum.
  have h_const_sum : (∑ _k : Fin M, (N : ℝ)) = (M : ℝ) * (N : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [h_const_sum]
  -- Goal: (1/M) · (∑ (encoder k - m_avg)² + M·N) ≤ S² + N
  -- = (1/M) · ∑ (encoder k - m_avg)² + (1/M) · M · N
  -- = (1/M) · ∑ (encoder k - m_avg)² + N   (since M > 0)
  -- We must show (1/M) · ∑ (encoder k - m_avg)² ≤ S².
  -- Expand: ∑ (x_k - m_avg)² = ∑ x_k² - 2 m_avg ∑ x_k + M·m_avg²
  -- (1/M)·∑ (...)² = S² - 2 m_avg² + m_avg² = S² - m_avg² ≤ S².
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM_real : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
  have hM_ne : (M : ℝ) ≠ 0 := ne_of_gt hM_real
  -- RHS algebra: (1/M) · (A + M·N) = (1/M)·A + N.
  have h_split :
      (1 / (M : ℝ)) *
          ((∑ k : Fin M, (c.encoder k i - m_avg) ^ 2) + (M : ℝ) * (N : ℝ))
        = (1 / (M : ℝ)) * (∑ k : Fin M, (c.encoder k i - m_avg) ^ 2)
          + (N : ℝ) := by
    field_simp
  rw [h_split]
  -- Suffices: (1/M) · ∑ (c.encoder k i - m_avg)² ≤ perLetterInputSecondMoment c i.
  -- Expand the sum.
  have h_sum_expand :
      (∑ k : Fin M, (c.encoder k i - m_avg) ^ 2)
        = (∑ k : Fin M, (c.encoder k i) ^ 2)
          - 2 * m_avg * (∑ k : Fin M, c.encoder k i)
          + (M : ℝ) * m_avg ^ 2 := by
    have : ∀ k : Fin M,
        (c.encoder k i - m_avg) ^ 2
          = (c.encoder k i) ^ 2 - 2 * m_avg * c.encoder k i + m_avg ^ 2 := by
      intro k; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
  rw [h_sum_expand]
  -- ∑ c.encoder k i = M · m_avg.
  have h_sum_eq : (∑ k : Fin M, c.encoder k i) = (M : ℝ) * m_avg := by
    rw [hm_avg_def]
    field_simp
  rw [h_sum_eq]
  -- Now: (1/M) · ((∑ (encoder k)²) - 2 m_avg · M m_avg + M m_avg²)
  --     = (1/M) · ∑ (encoder k)² - 2 m_avg² + m_avg² = S² - m_avg².
  have h_simplify :
      (1 / (M : ℝ)) * ((∑ k : Fin M, (c.encoder k i) ^ 2)
            - 2 * m_avg * ((M : ℝ) * m_avg) + (M : ℝ) * m_avg ^ 2)
        = perLetterInputSecondMoment c i - m_avg ^ 2 := by
    unfold perLetterInputSecondMoment
    field_simp
    ring
  rw [h_simplify]
  -- Conclude: S² - m_avg² + N ≤ S² + N since m_avg² ≥ 0.
  have hm_sq_nn : 0 ≤ m_avg ^ 2 := sq_nonneg _
  linarith

/-- **C-1b** Per-letter MI bound via per-letter input variance.

Per-letter `I(X_i; Y_i) ≤ (1/2) log(1 + perLetterInputSecondMoment c i / N)`
を `differentialEntropy_le_gaussian_of_variance_le` (4 hyp 形、`DifferentialEntropy.lean:518`)
で導出。`Y_i` の分散 ≤ `E[X_i²] + N` (input ⊥⊥ noise) で Gaussian max-entropy。

戦略 (mini-plan `awgn-converse-c1b-gaussian-maxent` §Approach):
```
(perLetterMI).toReal  = h(Y_i) - h(gaussianReal 0 N)                  -- bridge hyp
                     ≤ (1/2) log(2πe·v_Y) - (1/2) log(2πe·N)          -- max-entropy 4 hyp
                     = (1/2) log(v_Y / N) ≤ (1/2) log((S²+N)/N)
                     = (1/2) log(1 + S²/N)                              -- arithmetic
```
where `v_Y := (perLetterInputSecondMoment c i + N).toNNReal`. -/
@[entry_point]
theorem awgn_per_letter_mi_le_log_var
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P)
    (h_mi_bridge_per_letter :
        ∀ i : Fin n, (perLetterMI h_meas c i).toReal
          = InformationTheory.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
            - InformationTheory.Shannon.differentialEntropy
                (ProbabilityTheory.gaussianReal 0 N))
    (i : Fin n) :
    (perLetterMI h_meas c i).toReal
      ≤ (1 / 2) * Real.log (1 + perLetterInputSecondMoment c i / (N : ℝ)) := by
  -- Positivity.
  have hN_pos : (0 : ℝ) < (N : ℝ) :=
    lt_of_le_of_ne N.coe_nonneg (Ne.symm hN)
  have hN_ne_nnreal : N ≠ 0 := by
    intro h; apply hN; exact_mod_cast h
  -- Mean of `X_i` under uniform `W`: `m := (1/M) ∑ₘ c.encoder m i`.
  set m : ℝ := (1 / (M : ℝ)) * ∑ k : Fin M, c.encoder k i with hm_def
  -- `S² := perLetterInputSecondMoment c i`, non-negative.
  set S2 : ℝ := perLetterInputSecondMoment c i with hS2_def
  have hS2_nn : (0 : ℝ) ≤ S2 := by
    rw [hS2_def]; unfold perLetterInputSecondMoment
    apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  -- `v_Y := (S² + N).toNNReal`. Positivity from N > 0.
  set v : ℝ≥0 := (S2 + (N : ℝ)).toNNReal with hv_def
  have h_v_eq : (v : ℝ) = S2 + (N : ℝ) := by
    rw [hv_def]
    have : (0 : ℝ) ≤ S2 + (N : ℝ) := by linarith
    rw [Real.coe_toNNReal _ this]
  have hv_ne : v ≠ 0 := by
    intro hv_eq
    have : (v : ℝ) = 0 := by exact_mod_cast hv_eq
    rw [h_v_eq] at this
    linarith
  have hv_pos : (0 : ℝ) < (v : ℝ) := by rw [h_v_eq]; linarith
  -- Probability measure structure on per-letter Y.
  haveI : IsProbabilityMeasure (perLetterYLaw h_meas c i) :=
    perLetterYLaw_isProbabilityMeasure h_meas c i
  -- 4 hyp for `differentialEntropy_le_gaussian_of_variance_le`.
  have h_mu_ac : perLetterYLaw h_meas c i ≪ MeasureTheory.volume :=
    perLetterYLaw_absolutelyContinuous hN h_meas c i
  have h_mean : ∫ x, x ∂(perLetterYLaw h_meas c i) = m :=
    perLetterYLaw_mean hN h_meas c i
  have h_var : ∫ x, (x - m) ^ 2 ∂(perLetterYLaw h_meas c i) ≤ (v : ℝ) := by
    rw [h_v_eq]
    exact perLetterYLaw_variance_le hN h_meas c i
  have h_var_int :
      Integrable (fun x : ℝ => (x - m) ^ 2) (perLetterYLaw h_meas c i) :=
    perLetterYLaw_var_integrable hN h_meas c i m
  -- Per-letter log-density integrability via the genuine lemma
  -- (`AwgnWalls.lean` `awgnPerLetterIntegrability_holds`, `@audit:ok`, sorryAx-free);
  -- `converseJointInline` ≡ `awgnConverseJoint`, so `perLetterYLaw h_meas c i` matches by defeq.
  have h_ent_int :
      Integrable (fun y : ℝ =>
          Real.negMulLog
            ((perLetterYLaw h_meas c i).rnDeriv MeasureTheory.volume y).toReal)
        MeasureTheory.volume := awgnPerLetterIntegrability_holds h_meas c i
  -- Apply Gaussian max-entropy upper bound.
  have h_max_ent :
      InformationTheory.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
        ≤ (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ)) :=
    InformationTheory.Shannon.differentialEntropy_le_gaussian_of_variance_le
      h_mu_ac m hv_ne h_mean h_var h_var_int h_ent_int
  -- `h(gaussianReal 0 N) = (1/2) log(2πe N)`.
  have h_gauss_ent :
      InformationTheory.Shannon.differentialEntropy (ProbabilityTheory.gaussianReal 0 N)
        = (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (N : ℝ)) :=
    InformationTheory.Shannon.differentialEntropy_gaussianReal 0 hN_ne_nnreal
  -- Combine via bridge.
  rw [h_mi_bridge_per_letter i, h_gauss_ent]
  -- Goal: h(Y) - (1/2) log(2πeN) ≤ (1/2) log(1 + S²/N).
  -- (1/2) log(2πe·v) - (1/2) log(2πe·N) = (1/2) log(v/N).
  have h2πe_pos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by
    have := Real.pi_pos
    have := Real.exp_pos 1
    positivity
  have h2πev_pos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * (v : ℝ) := by positivity
  have h2πeN_pos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * (N : ℝ) := by positivity
  have h_log_diff :
      (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ))
        - (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (N : ℝ))
        = (1 / 2) * Real.log ((v : ℝ) / (N : ℝ)) := by
    rw [← mul_sub, ← Real.log_div h2πev_pos.ne' h2πeN_pos.ne']
    congr 2
    field_simp
  -- v / N = 1 + S² / N.
  have h_v_div : (v : ℝ) / (N : ℝ) = 1 + S2 / (N : ℝ) := by
    rw [h_v_eq, add_div, div_self hN]
    linarith
  -- Chain: h(Y) - h(Z) ≤ (1/2) log(2πe·v) - (1/2) log(2πe·N)
  --       = (1/2) log(v/N) = (1/2) log(1 + S²/N).
  calc InformationTheory.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
        - (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (N : ℝ))
      ≤ (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ))
        - (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (N : ℝ)) := by linarith
    _ = (1 / 2) * Real.log ((v : ℝ) / (N : ℝ)) := h_log_diff
    _ = (1 / 2) * Real.log (1 + S2 / (N : ℝ)) := by rw [h_v_div]

/-- **C-1c** Jensen / concavity of `log(1+·/N)`:
`∑ᵢ (1/2) log(1 + xᵢ/N) ≤ n · (1/2) log(1 + (∑ᵢ xᵢ / n) / N)` for `xᵢ ≥ 0`.

`Real.log` is concave on `Ioi 0` (`Mathlib.Analysis.Convex.SpecificFunctions.Basic.
strictConcaveOn_log_Ioi`) ⇒ `fun x => Real.log (1 + x/N)` concave on `Ici 0` (composition
with affine increasing map, packaged as `concaveOn_log_one_add_div` in
`DifferentialEntropy.lean`). Apply `ConcaveOn.le_map_sum` with uniform weights
`wᵢ := 1/n`. -/
@[entry_point]
theorem sum_log_one_add_le_n_log_one_add_avg
    {n : ℕ} (hn_pos : 0 < n)
    (N : ℝ) (hN_pos : 0 < N)
    (xs : Fin n → ℝ) (hxs_nn : ∀ i, 0 ≤ xs i) :
    ∑ i : Fin n, (1 / 2) * Real.log (1 + xs i / N)
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + ((1 / (n : ℝ)) * ∑ i : Fin n, xs i) / N)) := by
  -- `f x := log(1 + x/N)` is concave on `Ici 0`.
  set f : ℝ → ℝ := fun x => Real.log (1 + x / N) with hf_def
  have hf_concave : ConcaveOn ℝ (Set.Ici (0 : ℝ)) f :=
    InformationTheory.Shannon.concaveOn_log_one_add_div hN_pos
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real_pos
  -- Uniform weights `wᵢ := 1/n`.
  set w : Fin n → ℝ := fun _ => (1 : ℝ) / (n : ℝ) with hw_def
  have hw_nn : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ w i := by
    intro i _; simp only [hw_def]; positivity
  have hw_sum : ∑ i ∈ (Finset.univ : Finset (Fin n)), w i = 1 := by
    simp [hw_def, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    field_simp
  have hxs_mem : ∀ i ∈ (Finset.univ : Finset (Fin n)), xs i ∈ Set.Ici (0 : ℝ) := by
    intro i _; exact hxs_nn i
  -- Apply Jensen.
  have h_jensen :
      (∑ i ∈ (Finset.univ : Finset (Fin n)), w i • f (xs i))
        ≤ f (∑ i ∈ (Finset.univ : Finset (Fin n)), w i • xs i) :=
    hf_concave.le_map_sum hw_nn hw_sum hxs_mem
  -- Convert `smul` to `mul` on `ℝ`.
  simp only [smul_eq_mul, hw_def] at h_jensen
  -- `h_jensen : ∑ i, (1/n) * log(1 + xs i / N) ≤ log(1 + ((1/n) * ∑ i, xs i)/N)`
  -- after factoring `(1/n)` out of `∑ i, (1/n) * xs i`.
  rw [show (∑ i : Fin n, (1 : ℝ) / (n : ℝ) * xs i) = (1 / (n : ℝ)) * ∑ i : Fin n, xs i from
    (Finset.mul_sum Finset.univ xs ((1 : ℝ) / (n : ℝ))).symm] at h_jensen
  -- Multiply both sides by `(n : ℝ) > 0` and then by `(1/2) ≥ 0`.
  -- LHS goal: ∑ (1/2) * log(1 + xᵢ/N) = (n : ℝ) * (1/2) * ((1/n) * ∑ log(1 + xᵢ/N)).
  have h_lhs_rewrite :
      ∑ i : Fin n, (1 / 2 : ℝ) * Real.log (1 + xs i / N)
        = (n : ℝ) * ((1 / 2) * ((1 / (n : ℝ)) *
            ∑ i : Fin n, Real.log (1 + xs i / N))) := by
    rw [show (∑ i : Fin n, (1 / 2 : ℝ) * Real.log (1 + xs i / N))
      = (1 / 2 : ℝ) * ∑ i : Fin n, Real.log (1 + xs i / N) from
      (Finset.mul_sum Finset.univ (fun i => Real.log (1 + xs i / N)) (1 / 2 : ℝ)).symm]
    field_simp
  rw [h_lhs_rewrite]
  -- Now goal: (n) * ((1/2) * ((1/n) * ∑ log(1+xᵢ/N))) ≤ (n) * ((1/2) * log(1+avg/N)).
  -- Apply monotonicity twice (factor (n) ≥ 0, then (1/2) ≥ 0).
  have h_half_nn : (0 : ℝ) ≤ 1 / 2 := by norm_num
  apply mul_le_mul_of_nonneg_left _ hn_real_pos.le
  apply mul_le_mul_of_nonneg_left _ h_half_nn
  -- Goal: (1/n) * ∑ log(1+xᵢ/N) ≤ log(1 + ((1/n) * ∑ xᵢ)/N).
  -- This is exactly `h_jensen` after rewriting `∑ (1/n) * log(...) = (1/n) * ∑ log(...)`.
  have h_sum_factor :
      ∑ i : Fin n, (1 / (n : ℝ)) * Real.log (1 + xs i / N)
        = (1 / (n : ℝ)) * ∑ i : Fin n, Real.log (1 + xs i / N) :=
    (Finset.mul_sum Finset.univ (fun i => Real.log (1 + xs i / N)) (1 / (n : ℝ))).symm
  rw [← h_sum_factor]
  -- `f (xs i) = log(1 + xs i / N)` and `f (∑ ...) = log(1 + (...)/N)`.
  exact h_jensen

/-- **C-2** Sum of per-letter MIs is bounded by `n · (1/2) log(1 + P/N)`.

C-1a + C-1b + C-1c の合成: per-letter MI bound (variance 形) + per-letter variance
average ≤ P + Jensen for log(1+x/N) concavity. -/
@[entry_point]
theorem awgn_sum_per_letter_mi_le_n_capacity
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (hn_pos : 0 < n) (c : AwgnCode M n P)
    (h_mi_bridge_per_letter :
        ∀ i : Fin n, (perLetterMI h_meas c i).toReal
          = InformationTheory.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
            - InformationTheory.Shannon.differentialEntropy
                (ProbabilityTheory.gaussianReal 0 N)) :
    ∑ i : Fin n, (perLetterMI h_meas c i).toReal
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ))) := by
  -- Step 1: per-letter bound via `awgn_per_letter_mi_le_log_var` for each `i`.
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have h_per_letter_bound : ∀ i : Fin n, (perLetterMI h_meas c i).toReal
      ≤ (1 / 2) * Real.log (1 + perLetterInputSecondMoment c i / (N : ℝ)) := by
    intro i
    exact awgn_per_letter_mi_le_log_var P hP N hN h_meas c
      h_mi_bridge_per_letter i
  -- Step 2: sum the per-letter bound.
  have h_sum_le_sum :
      (∑ i : Fin n, (perLetterMI h_meas c i).toReal)
        ≤ ∑ i : Fin n, (1 / 2) * Real.log (1 + perLetterInputSecondMoment c i / (N : ℝ)) :=
    Finset.sum_le_sum (fun i _ => h_per_letter_bound i)
  -- Step 3: non-negativity of `perLetterInputSecondMoment c i` (squares are ≥ 0).
  have h_nn : ∀ i : Fin n, 0 ≤ perLetterInputSecondMoment c i := by
    intro i
    unfold perLetterInputSecondMoment
    apply mul_nonneg
    · positivity
    · apply Finset.sum_nonneg
      intros m _
      positivity
  -- Step 4: Jensen / concavity bound (C-1c) yields
  --   `∑ᵢ (1/2) log(1 + xᵢ/N) ≤ n · (1/2) log(1 + (∑ᵢ xᵢ / n) / N)`.
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    refine lt_of_le_of_ne N.coe_nonneg ?_
    exact (Ne.symm hN)
  have h_jensen := sum_log_one_add_le_n_log_one_add_avg (n := n) hn_pos
    (N : ℝ) hN_pos (fun i => perLetterInputSecondMoment c i) h_nn
  -- Step 5: monotonicity of `log` to push down `avg ≤ P` (C-1a) into the RHS.
  -- `avg := (1/n) ∑ᵢ perLetterInputSecondMoment c i ≤ P` (awgn_per_letter_input_power_avg).
  have h_avg_le : (1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i ≤ P :=
    awgn_per_letter_input_power_avg hM_pos hn_pos c
  -- `1 + avg / N ≤ 1 + P / N`.
  have h_one_add_mono :
      1 + ((1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i) / (N : ℝ)
        ≤ 1 + P / (N : ℝ) := by
    have : ((1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i) / (N : ℝ)
        ≤ P / (N : ℝ) := by
      apply div_le_div_of_nonneg_right h_avg_le hN_pos.le
    linarith
  -- `log` monotone on positives.
  have h_pos_avg :
      0 < 1 + ((1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i) / (N : ℝ) := by
    have h_avg_nn :
        (0 : ℝ) ≤ (1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i := by
      apply mul_nonneg
      · positivity
      · exact Finset.sum_nonneg (fun i _ => h_nn i)
    have : (0 : ℝ) ≤ ((1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i) / (N : ℝ) := by
      exact div_nonneg h_avg_nn hN_pos.le
    linarith
  have h_log_mono :
      Real.log
          (1 + ((1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i) / (N : ℝ))
        ≤ Real.log (1 + P / (N : ℝ)) :=
    Real.log_le_log h_pos_avg h_one_add_mono
  -- Multiply by `n · (1/2) > 0` and chain.
  have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have h_jensen_chained :
      (n : ℝ) * ((1 / 2) * Real.log
          (1 + ((1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i) / (N : ℝ)))
        ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ))) := by
    have h_scaled : (1 / 2) * Real.log
          (1 + ((1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i) / (N : ℝ))
        ≤ (1 / 2) * Real.log (1 + P / (N : ℝ)) := by
      apply mul_le_mul_of_nonneg_left h_log_mono
      norm_num
    apply mul_le_mul_of_nonneg_left h_scaled
    exact le_of_lt hn_real
  -- Chain: sum ≤ ∑ log ≤ n · log_avg ≤ n · log_P.
  exact h_sum_le_sum.trans (h_jensen.trans h_jensen_chained)

/-- **C-5** Joint MI finiteness on the AWGN converse joint (transitive closure).

`I(W; Y^n) ≤ I(X^n; Y^n) ≤ ∑ᵢ I(X_i; Y_i) ≤ n · (1/2) log(1+P/N) < ∞` で両 MI が ≠ ∞。
sibling helpers `awgnConverseJoint_mutualInfo_ne_top` / `awgn_dpi` 内 `(jointMIXnYn).≠ ∞`
の二つ共通の MI-finiteness wall を一括 discharge。 -/
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

/-! ## Phase C — converse discharger + `awgn_converse_F3_discharged` wrapper -/

/-- **Phase C-3 — converse discharger** (genuine assembly of the chain).

Phase B-Fano + B-DPI + B-chain + C-2 (sum form) を連鎖:
```
log M ≤ I(W; Y^n).toReal + binEntropy(Pe) + Pe·log(M-1)     (Phase B-Fano)
      ≤ I(X^n; Y^n).toReal + binEntropy(Pe) + Pe·log(M-1)   (Phase B-DPI, Markov)
      ≤ ∑ I(X_i; Y_i).toReal + binEntropy(Pe) + Pe·log(M-1) (Phase B-chain)
      ≤ n · (1/2) log(1+P/N) + binEntropy(Pe) + Pe·log(M-1) (Phase C-2, sum form)
```

**2026-05-28 Phase 3-α sorry-based migration**: 旧 load-bearing bundle hyp
`h_feasible : IsAwgnConverseFeasible` を除去し、3 sub-bound (per-letter integrability /
continuous MI chain rule / Markov) は `AwgnWalls.lean` の補題
(`awgnPerLetterIntegrability_holds` / `awgnContinuousMIChainRule_holds` /
`awgnConverseMarkov_holds`) を `awgn_dpi` / `awgn_chain_rule` /
`awgn_sum_per_letter_mi_le_n_capacity` 内部から呼ぶ普通の lemma call に縮約した
(Tier 3 → Tier 2)。per-letter integrability と Markov は genuine 化済 (`@audit:ok`、
sorryAx-free)、残る Mathlib 壁は continuous MI chain rule のみ。残る hyp
`h_mi_bridge_per_letter` は per-letter MI = `h(Y_i) - h(Z)`
の bridge (F-2 closure 待ち、`awgn-mi-bridge-plan.md`)、本 file scope では 0 sorry。 -/
@[entry_point]
theorem isAwgnConverseFeasible_discharger
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_mi_bridge_per_letter :
        ∀ {M n : ℕ} [NeZero M] (_hM : 2 ≤ M) (c : AwgnCode M n P), ∀ i : Fin n,
          (perLetterMI h_meas c i).toReal
            = InformationTheory.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
              - InformationTheory.Shannon.differentialEntropy
                  (ProbabilityTheory.gaussianReal 0 N))
    {M n : ℕ} [NeZero M] (hM : 2 ≤ M) (hn_pos : 0 < n) (c : AwgnCode M n P)
    (Pe : ℝ) (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  have hN_nnreal : N ≠ 0 := by intro h; exact hN (by rw [h]; norm_num)
  -- Step (a)+(b)+(e) — B-Fano: `log M ≤ I(W; Y^n).toReal + binEntropy(Pe) + Pe · log(M-1)`.
  have h_fano := awgn_converse_single_shot_call P N hN_nnreal h_meas hM c Pe hPe
  -- Step (c-DPI) — B-DPI: `I(W; Y^n).toReal ≤ I(X^n; Y^n).toReal`
  -- (Markov factorization via `awgnConverseMarkov_holds`, genuine `@audit:ok`).
  have h_dpi := awgn_dpi P N hN_nnreal h_meas c
  -- Step (c-chain) — B-chain: `I(X^n; Y^n).toReal ≤ ∑ᵢ I(X_i; Y_i).toReal`
  -- (chain rule via `awgnContinuousMIChainRule_holds` shared sorry 補題).
  have h_chain_le := awgn_chain_rule P N h_meas c
  -- Step (d) — C-2: `∑ᵢ I(X_i; Y_i).toReal ≤ n · (1/2) log(1+P/N)`
  -- (per-letter integrability via `awgnPerLetterIntegrability_holds`, genuine `@audit:ok`).
  have h_sum := awgn_sum_per_letter_mi_le_n_capacity P hP N hN h_meas hn_pos c
    (h_mi_bridge_per_letter (M := M) (n := n) hM c)
  -- Assemble: transitive `≤` chain on the first summand.
  have h_lhs_chain : (jointMIWYn h_meas c).toReal
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ))) :=
    (h_dpi.trans h_chain_le).trans h_sum
  -- Add `binEntropy(Pe) + Pe · log(M-1)` (constants on both sides).
  linarith [h_fano, h_lhs_chain]

/-- **Phase C-6 — `awgn_converse_F3_discharged` wrapper**.

`awgn_converse` の body を埋めるための薄い wrapper。`2 ≤ M` から `NeZero M` typeclass を
導出し、`isAwgnConverseFeasible_discharger` に委譲。

**2026-05-28 Phase 3-α**: 旧 load-bearing bundle hyp `h_feasible :
IsAwgnConverseFeasible` を除去 (Tier 3 → Tier 2、analytic content は `AwgnWalls.lean`
shared sorry 補題に集約)。残る hyp `h_mi_bridge_per_letter` は F-2 closure 待ちの
per-letter MI bridge (`awgn-mi-bridge-plan.md`)、本 file scope では 0 sorry。 -/
@[entry_point]
theorem awgn_converse_F3_discharged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_mi_bridge_per_letter :
        ∀ {M n : ℕ} [NeZero M] (_hM : 2 ≤ M) (c : AwgnCode M n P), ∀ i : Fin n,
          (perLetterMI h_meas c i).toReal
            = InformationTheory.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
              - InformationTheory.Shannon.differentialEntropy
                  (ProbabilityTheory.gaussianReal 0 N))
    {M n : ℕ} (hM : 2 ≤ M) (hn_pos : 0 < n) (c : AwgnCode M n P)
    (Pe : ℝ) (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  haveI : NeZero M := ⟨by omega⟩
  exact isAwgnConverseFeasible_discharger P hP N hN h_meas
    h_mi_bridge_per_letter hM hn_pos c Pe hPe

end InformationTheory.Shannon.AWGN
