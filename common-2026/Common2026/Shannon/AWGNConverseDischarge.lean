import Common2026.Shannon.AWGN
import Common2026.Shannon.AWGNConverse
import Common2026.Shannon.Converse
import Common2026.Shannon.CondMutualInfo
import Common2026.Shannon.DifferentialEntropy
import Common2026.Shannon.ChannelCoding
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

/-! # AWGN F-3 converse — analytic body discharge

Plan: `docs/shannon/awgn-converse-aux-plan.md` (Phase 0 inventory 反映 1143 行)

Cover-Thomas 9.1.2 (converse) を **bundle predicate
`IsAwgnConverseFeasible P N h_meas`** で 3 Mathlib 壁 (per-letter integrability /
continuous MI chain rule / Markov-side regularity) を packing しつつ、Phase B
3 並列 + Phase C 統合の skeleton を頭出しする。

姉妹 `IsAwgnRandomCodingFeasible` (`AWGNAchievabilityDischarge.lean:834`) と
対称 structure (3 sub-bound 連言)。本 plan は **regularity (Mathlib 壁 packaging)**
側分類で、judgement 表 (`awgn-converse-aux-plan.md` §954-968) に従い:

* `PerLetterIntegrabilityForConverse` — regularity (Mathlib 壁 T-FFC-2)
* `ContinuousMIChainRuleForConverse`  — regularity (Mathlib 壁 T-FFC-3)
* `MarkovChainForConverse`            — regularity (genuine、Mathlib 壁ではない)

## Phase 構成

* Phase A (本 commit) — bundle predicate + sub-bound + Phase B/C skeleton
* Phase B-Fano — `awgn_converse_single_shot_call` (Phase B-Fano dispatch)
* Phase B-DPI/chain — `awgn_dpi` / `awgn_chain_rule` (Phase B-DPI/chain dispatch)
* Phase B-Gaussian — `awgn_per_letter_mi_le_capacity` (Phase B-Gaussian dispatch)
* Phase C — `isAwgnConverseFeasible_discharger` 統合 + `awgn_converse` body 置換

## 設計指針 (Phase B 各 dispatch 向け)

* Phase B 3 並列 dispatch は本 file の `sorry` を埋めるだけ。**signature 改変は
  禁止** (signature 改変必要なら Phase A に戻る)。
* `perLetterYLaw` / `awgnConverseJoint` は closed-form で本 commit で genuine 化済。
  `perLetterMI` / `jointMIWYn` / `jointMIXnYn` は canonical joint `awgnConverseJoint`
  の `mutualInfo` 形で genuine 化済 (Phase B 各 dispatch が unfold して使う想定)。
* `MarkovChainForConverse` は `IsMarkovChain` 形で genuine 化済 (Phase B-DPI で
  `mutualInfo_le_of_markov` 経由で discharge)。

`@audit:staged(awgn-converse-feasible)` -/

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
noncomputable def perLetterYLaw
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) : Measure ℝ :=
  (awgnConverseJoint h_meas c).map (fun ω => ω.2 i)

/-- per-letter mutual information `I(X_i; Y_i)` on the canonical joint
`awgnConverseJoint c h_meas`, with `X_i ω := c.encoder ω.1 i` and `Y_i ω := ω.2 i`. -/
noncomputable def perLetterMI
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) : ℝ≥0∞ :=
  mutualInfo (awgnConverseJoint h_meas c)
    (fun ω => c.encoder ω.1 i) (fun ω => ω.2 i)

/-- Joint MI `I(W; Y^n)` (message vs. channel output block). -/
noncomputable def jointMIWYn
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) : ℝ≥0∞ :=
  mutualInfo (awgnConverseJoint h_meas c) Prod.fst Prod.snd

/-- Joint MI `I(X^n; Y^n)` (channel input block vs. channel output block). -/
noncomputable def jointMIXnYn
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) : ℝ≥0∞ :=
  mutualInfo (awgnConverseJoint h_meas c) (fun ω => c.encoder ω.1) Prod.snd

/-! ## Phase A — sub-bound predicates -/

/-- **Per-letter integrability sub-bound** (Mathlib 壁 T-FFC-2 packaging)。

Per-letter `Y_i` の `negMulLog (rnDeriv μ_{Y_i} volume)` Lebesgue 可積分性。
`differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:518`)
の 4 hyp の中で `h_ent_int` のみが per-letter で discharge 不能 (input law μ_{Y_i}
に依存)、他 3 hyp (`hμ ≪ vol`, `h_mean`, `h_var`, `h_var_int`) は plan 内で genuine 化。

**Honesty 4 条件** (姉妹 `IsAwgnRandomCodingFeasible` と同型):
(a) signature ≠ `awgn_converse` 結論 (`Integrable (negMulLog ...) volume` の per-letter ∀ 形)
(b) Mathlib 壁明示 — T-FFC-2 continuous SMB / n-d differentialEntropy 系
(c) Phase B-Gaussian で `awgn_per_letter_mi_le_capacity` 経由で genuine assembly
(d) `@audit:staged(awgn-converse-feasible)` 付与

`@audit:staged(awgn-converse-feasible)` -/
def PerLetterIntegrabilityForConverse (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) : Prop :=
  ∀ i : Fin n,
    MeasureTheory.Integrable (fun y : ℝ =>
        Real.negMulLog
          ((perLetterYLaw h_meas c i).rnDeriv MeasureTheory.volume y).toReal)
      MeasureTheory.volume

/-- **Continuous MI chain rule sub-bound** (Mathlib 壁 T-FFC-3 packaging)。

Memoryless AWGN continuous MI chain rule `I(X^n; Y^n) ≤ ∑ᵢ I(X_i; Y_i)`。Common2026 既存
`Fintype α` 制約付き chain rule (`CondEntropyMemoryless` 系) は AWGN `α := ℝ` で reuse 不可、
`mutualInfo_pi_eq_sum` (`MIChainRule.lean:318`) も iid joint 仮定で発火不可 (AWGN code は
non-iid codebook)。姉妹 `awgn-mi-decomp-plan.md` Phase 6 一般 body 補題と相補
(closure で genuine discharge 候補)。

`@audit:staged(awgn-converse-feasible)` -/
def ContinuousMIChainRuleForConverse (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) : Prop :=
  (jointMIXnYn h_meas c).toReal
    ≤ ∑ i : Fin n, (perLetterMI h_meas c i).toReal

/-- **Markov chain `W → encoder ∘ W → Y^n` regularity hyp** (Phase 0 判断 #3: genuine 化可)。

AWGN code 構造 (encoder deterministic + channel memoryless + W uniform) の自然帰結 ⇒
**regularity hypothesis** (load-bearing ではない、Mathlib 壁ではない)。Phase B-DPI で
`mutualInfo_le_of_markov` (`CondMutualInfo.lean:385`) 経由 genuine discharge の material。

`IsMarkovChain` (`CondMutualInfo.lean:73`) の γ-form joint factorization、引数順
`(Xs Zc Yo : Ω → _) = (W = Prod.fst, encoder ∘ W = fun ω => c.encoder ω.1, Y^n = Prod.snd)`。
`[IsFiniteMeasure (awgnConverseJoint h_meas c)]` + `[StandardBorelSpace (Fin M)]` +
`[StandardBorelSpace (Fin n → ℝ)]` は AWGN code 構造 + Mathlib 既存 instance で
自動充足 (Phase B-DPI で確認)。 -/
def MarkovChainForConverse (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) : Prop :=
  IsMarkovChain (awgnConverseJoint h_meas c)
    (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
    (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1)
    (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ)

/-! ## Phase A — bundle predicate `IsAwgnConverseFeasible` -/

/-- **AWGN converse feasibility bundle** (姉妹 `IsAwgnRandomCodingFeasible`
(`AWGNAchievabilityDischarge.lean:834`) と対称)。

Phase 0 判断 #1: **3 field 連言 = 2 staged (Mathlib 壁) + 1 genuine (regularity)**。

**Honesty 4 条件** (judgement 表 `awgn-converse-aux-plan.md` §954-968):
* (a) signature ≠ `awgn_converse` 結論 (`log M ≤ n·C + binEntropy + Pe·log(M-1)` ではない、
      3 sub-bound 連言、各々が中間 quantity の bound)
* (b) Mathlib 壁明示 — `PerLetter`/`Chain` は staged (T-FFC-2/T-FFC-3)、`Markov` は
      genuine regularity (Phase 0 判断 #3)
* (c) Phase B-Fano + B-DPI + B-chain + B-Gaussian + Phase C で genuine assembly
* (d) `@audit:staged(awgn-converse-feasible)` 付与

**禁止 (load-bearing パターン、tier 5 defect)**:
* ❌ bundle 内に `log M ≤ n·C + binEntropy + Pe·log(M-1)` を field として持つ
  (predicate 自身が結論型 → CLAUDE.md circular `:= h` defect 同等)
* ❌ name laundering (`awgn_converse_full_discharged` 等の別名 passthrough)
* ❌ Phase C `isAwgnConverseFeasible_discharger` 本体が `h_feasible …` 1 行に
  縮退 (Phase B-Fano / B-DPI / B-chain / B-Gaussian が integrate されていない)

`@audit:staged(awgn-converse-feasible)` -/
def IsAwgnConverseFeasible (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ ⦃M n : ℕ⦄ [NeZero M], 2 ≤ M → ∀ (c : AwgnCode M n P),
    PerLetterIntegrabilityForConverse P N h_meas c ∧
    ContinuousMIChainRuleForConverse P N h_meas c ∧
    MarkovChainForConverse P N h_meas c

/-! ## Phase B-Fano skeleton (本 commit は signature + sorry のみ)

`shannon_converse_single_shot` (`Common2026/Shannon/Converse.lean:81`) を
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

/-- AWGN converse の `mutualInfo` finiteness: `mutualInfo (awgnConverseJoint c) Prod.fst Prod.snd ≠ ∞`。

Msg 側 `Fin M` 有限 (`Fintype`、`MeasurableSingletonClass`) ⇒ `entropy ≤ log M < ∞`、
`mutualInfo ≤ min(H(Msg), H(Yo)) ≤ H(Msg)` 系の Common2026 既存補題
(`MutualInfo.lean:197 mutualInfo_ne_top`) は **両側 `[Fintype]` 要求** で AWGN
converse `Y := Fin n → ℝ` (continuous) で reuse 不可 — Phase B-Fano dispatch 後の
独立 audit (`@residual(wall:multivariate-mi)` reclassify 推奨) で確定。
Phase C 統合内で `mutualInfo_le_of_markov` + X^n side 有限性 (Gaussian
max-entropy `(1/2) log(1+P/N) < ∞` 経由) で transitively 確立する route が clean。
plan §線 575 「~10-20 行 plumbing」想定は Mathlib 壁発火で drift。 -/
private lemma awgnConverseJoint_mutualInfo_ne_top
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    mutualInfo (awgnConverseJoint h_meas c)
        (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
        (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) ≠ ∞ := by
  sorry -- @residual(plan:awgn-converse-aux-plan)

/-- **Phase B-Fano**: Fano + DPI postprocess + entropy chain + `H(W) = log M` を
`shannon_converse_single_shot` 1 行呼出で集約。

結論: `log M ≤ I(W; Y^n).toReal + binEntropy(Pe) + Pe · log(M-1)`。

Pe bridge (T-FFC-5、`errorProbAt` ↔ Fano `errorProb` の同値性、private helper
`awgn_errorProb_eq_fano_errorProb` に切出し) + MI-finite plumbing (private helper
`awgnConverseJoint_mutualInfo_ne_top` に切出し) を経由。 -/
theorem awgn_converse_single_shot_call
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
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
    awgnConverseJoint_mutualInfo_ne_top h_meas c
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

/-! ## Phase B-DPI/chain skeleton (本 commit は signature + sorry のみ)

DPI side: `mutualInfo_le_of_markov` (`CondMutualInfo.lean:385`) で
`I(W; Y^n) ≤ I(X^n; Y^n)` を genuine discharge (Phase 0 判断 #3)。
Chain side: bundle 内 `ContinuousMIChainRuleForConverse` staged hyp を destructure。 -/

/-- **Phase B-DPI**: Markov chain `W → encoder ∘ W → Y^n` から
`I(W; Y^n) ≤ I(X^n; Y^n)` を `mutualInfo_le_of_markov` (genuine、判断 #3) で導く。

Phase B-DPI dispatch で fill 予定。 -/
theorem awgn_dpi
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P)
    (h_markov : MarkovChainForConverse P N h_meas c) :
    (jointMIWYn h_meas c).toReal ≤ (jointMIXnYn h_meas c).toReal := by
  -- Markov chain `W → X^n → Y^n` (γ-form) ⇒ ENNReal DPI
  -- `mutualInfo W Y^n ≤ mutualInfo X^n Y^n`.
  -- `MarkovChainForConverse` already unfolds to `IsMarkovChain ... Prod.fst
  -- (fun ω => c.encoder ω.1) Prod.snd` (file-internal def).
  unfold MarkovChainForConverse at h_markov
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
  have h_finite : (jointMIXnYn h_meas c) ≠ ∞ := by
    unfold jointMIXnYn
    sorry -- @residual(plan:awgn-converse-aux-plan)
  -- Unfold `jointMIWYn` / `jointMIXnYn` to match the ENNReal inequality, apply
  -- `ENNReal.toReal_mono`.
  show (jointMIWYn h_meas c).toReal ≤ (jointMIXnYn h_meas c).toReal
  unfold jointMIWYn jointMIXnYn
  exact ENNReal.toReal_mono h_finite h_dpi_enn

/-- **Phase B-chain**: continuous MI chain rule for memoryless AWGN
`I(X^n; Y^n) ≤ ∑ᵢ I(X_i; Y_i)` を bundle 内 staged hyp で discharge。

Phase B-chain dispatch で fill 予定 (staged hyp 1 行 unfold)。 -/
theorem awgn_chain_rule
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P)
    (h_chain : ContinuousMIChainRuleForConverse P N h_meas c) :
    (jointMIXnYn h_meas c).toReal ≤ ∑ i : Fin n, (perLetterMI h_meas c i).toReal :=
  -- `ContinuousMIChainRuleForConverse` def body is verbatim the conclusion;
  -- destructuring is identity-level (regularity hyp, not load-bearing core —
  -- T-FFC-3 Mathlib wall is in the *predicate definition*, this discharger
  -- is mechanical unfold).
  h_chain

/-! ## Phase B-Gaussian skeleton (本 commit は signature + sorry のみ)

Per-letter `I(X_i; Y_i) ≤ (1/2) log(1 + P/N)`:
* `I(X_i; Y_i) = h(Y_i) - h(Y_i | X_i) = h(Y_i) - h(N)` (Gaussian noise factor、F-2 共有)
* `h(Y_i) ≤ (1/2) log(2πe(P+N))` (Gaussian max-entropy、Y_i variance ≤ P+N)
* `h(N) = (1/2) log(2πeN)` (Gaussian closed form)
* 合成: `(1/2) log(1 + P/N)` -/

/-- **Phase B-Gaussian**: per-letter `I(X_i; Y_i) ≤ (1/2) log(1 + P/N)`。

* `h_per_letter : PerLetterIntegrabilityForConverse` bundle field (T-FFC-2 staged)
* `h_mi_bridge_per_letter` : F-2 (`awgn-mi-bridge` / `awgn-mi-decomp`) と共有の MI 分解
  bridge (per-letter)

3-of-4 Gaussian max-entropy hypothesis (`hμ ≪ vol`, `h_mean`, `h_var`, `h_var_int`) は
本 dispatch 内で genuine 化:
* `hμ ≪ vol` — Gaussian noise convolve から自動 (`gaussianReal_absolutelyContinuous`)
* `h_mean h_var h_var_int` — input power constraint `∑ X_i² ≤ nP` から per-letter
  `E[X_i²] ≤ P` を導出 (Cauchy-Schwarz、~20 行)

Phase B-Gaussian dispatch で fill 予定。

**⚠ honesty defect (2026-05-27 Phase B-Gaussian dispatch 発見、tier 5)**:

主定理 signature `(perLetterMI h_meas c i).toReal ≤ (1/2) * Real.log (1 + P / N)` は
**各 i ∈ Fin n に対し per-letter capacity bound** を主張するが、`AwgnCode.power_constraint`
(`AWGN.lean:98`、`∀ m, ∑ᵢ (encoder m i)² ≤ n·P`) は **per-message block constraint** で
**per-letter `E[X_i²] ≤ P` は genuine に導出不能**。具体的には:
* `E[X_i²] = (1/M) ∑ₘ (encoder m i)²` (uniform W 上)
* per-message bound `(encoder m i)² ≤ ∑ⱼ (encoder m j)² ≤ n·P` (各項 ≤ sum) ⇒
  `E[X_i²] ≤ n·P` (worst case)
* avg over i: `∑ᵢ E[X_i²] = (1/M) ∑ₘ ∑ᵢ (encoder m i)² ≤ n·P` ⇒
  `(1/n) ∑ᵢ E[X_i²] ≤ P` (**avg 形のみ** genuine)

per-letter `E[X_i²] ≤ P` (各 i に対して) は AWGN code の per-message power constraint
からは出ない。Cover-Thomas 9.1.2 step 4 のテキストブック証明も実際は per-letter
`I(X_i;Y_i) ≤ (1/2) log(1 + P_i/N)` (P_i = E[X_i²]) の形を取り、Phase C で `∑ᵢ` +
Jensen / concavity of `log` で `n · (1/2) log(1+P/N)` に結合する形。本 plan §B-Gauss-1
(line 733-737) も「avg `(1/n) ∑ E[X_i²] ≤ P`」「**per-letter は ≤ nP**」と
明記済 (orchestrator brief line 「per-letter Var bound (avg vs per-letter) の判断」
で本 dispatch 観測予定として警告あり)。

**第一選択 (CLAUDE.md §「検証の誠実性 → 対処順序」) — signature 改変で sorry を
逃がす**: 本 dispatch では brief 指示「signature 改変禁止」のため不可。Phase C
`isAwgnConverseFeasible_discharger` の組立で `∑ᵢ I(X_i;Y_i) ≤ n · (1/2) log(1+P/N)`
を直接出す Jensen / concavity 形に書き直すのが正しい構造 (本定理は retract-candidate)。

**第二選択 (本 dispatch 採用) — tier 5 defect マーカー残置**: signature を改変せず
body は `sorry` のまま、本 docstring に `@audit:defect(false-statement)` +
`@audit:retract-candidate` を併記。Phase C 完了時に signature 書換 or 撤回を
強制する暫定マーカー。

@audit:defect(false-statement) — per-letter `E[X_i²] ≤ P` は AWGN
`power_constraint` (per-message block 形) から genuine 化不能、
各 i での per-letter capacity bound は false in general
@audit:closed-by-successor(awgn-converse-aux-plan) — Phase C
`isAwgnConverseFeasible_discharger` 内で sum 形 `∑ᵢ ... ≤ n · (1/2) log(1+P/N)`
+ Jensen / concavity (`log(1+x/N)` concave) で書き直し、本 declaration は撤回
予定 (Phase C 完了時 commit で削除、後続補題 `awgn_sum_per_letter_mi_le_n_capacity`
が代替)
@residual(defect:false-statement,plan:awgn-converse-aux-plan) -/
theorem awgn_per_letter_mi_le_capacity
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P)
    (h_per_letter : PerLetterIntegrabilityForConverse P N h_meas c)
    (h_mi_bridge_per_letter :
        ∀ i : Fin n, (perLetterMI h_meas c i).toReal
          = Common2026.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
            - Common2026.Shannon.differentialEntropy
                (ProbabilityTheory.gaussianReal 0 N))
    (i : Fin n) :
    (perLetterMI h_meas c i).toReal ≤ (1/2) * Real.log (1 + P / (N : ℝ)) := by
  sorry -- @residual(plan:awgn-converse-aux-plan) @audit:defect(false-statement)

/-! ## Phase C skeleton (本 commit は signature + sorry のみ)

Phase B-Fano + B-DPI + B-chain + B-Gaussian を連鎖して
`log M ≤ n · (1/2) log(1+P/N) + binEntropy(Pe) + Pe·log(M-1)` を assemble。 -/

/-- **Phase C — `IsAwgnConverseFeasible` discharger**.

Phase B-Fano + B-DPI + B-chain + B-Gaussian を連鎖:
```
log M ≤ I(W; Y^n).toReal + binEntropy(Pe) + Pe·log(M-1)     (Phase B-Fano)
      ≤ I(X^n; Y^n).toReal + binEntropy(Pe) + Pe·log(M-1)   (Phase B-DPI, Markov)
      ≤ ∑ I(X_i; Y_i).toReal + binEntropy(Pe) + Pe·log(M-1) (Phase B-chain)
      ≤ n · (1/2) log(1+P/N) + binEntropy(Pe) + Pe·log(M-1) (Phase B-Gaussian)
```

`@audit:staged(awgn-converse-feasible)` -/
theorem isAwgnConverseFeasible_discharger
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_feasible : IsAwgnConverseFeasible P N h_meas)
    (h_mi_bridge_per_letter :
        ∀ {M n : ℕ} [NeZero M] (_hM : 2 ≤ M) (c : AwgnCode M n P), ∀ i : Fin n,
          (perLetterMI h_meas c i).toReal
            = Common2026.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
              - Common2026.Shannon.differentialEntropy
                  (ProbabilityTheory.gaussianReal 0 N))
    {M n : ℕ} [NeZero M] (hM : 2 ≤ M) (c : AwgnCode M n P)
    (Pe : ℝ) (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  sorry -- @residual(plan:awgn-converse-aux-plan)

end InformationTheory.Shannon.AWGN
