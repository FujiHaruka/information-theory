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
* Phase B-Gaussian — 起草時 `awgn_per_letter_mi_le_capacity` 想定だったが
  per-message `power_constraint` から per-letter `E[X_i²] ≤ P` が genuine 化不能
  (false-statement defect) のため **撤回**。代替は Phase C の sum-form chain
  (`awgn_per_letter_input_power_avg` + `awgn_per_letter_mi_le_log_var` + Jensen)。
* Phase C — `isAwgnConverseFeasible_discharger` 統合 + `awgn_converse_F3_discharged` wrapper

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
(c) Phase C で sum-form chain (C-1a + C-1b + C-1c) 経由で genuine assembly
    (起草時の per-letter `awgn_per_letter_mi_le_capacity` 経路は false-statement
    defect で撤回、sum-form + Jensen に差替)
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

/-! ## Phase C — Per-letter input second moment / Jensen / sum-form chain
(Phase B-Gaussian 撤回後の再設計、`awgn-converse-aux-plan.md` Phase C 反映)。

旧 `awgn_per_letter_mi_le_capacity` (per-letter `E[X_i²] ≤ P` 形、`power_constraint`
per-message 形からは genuine 化不能の false-statement defect) は本 commit で撤回し、
代わりに **sum-form + Jensen** で `∑ᵢ I(X_i; Y_i) ≤ n · (1/2) log(1+P/N)` を直接立てる。 -/

/-- Per-letter input second moment `E[X_i² | W ∼ Uniform(Fin M)]
= (1/M) ∑_m (c.encoder m i)²`。Uniform message 上で input letter `X_i = c.encoder W i`
の 2 次モーメント。`power_constraint` (per-message block 形) と `1/n ∑_i` avg で
`(1/n) ∑_i perLetterInputSecondMoment c i ≤ P` が genuine に出る (`awgn_per_letter_input_power_avg`)。 -/
noncomputable def perLetterInputSecondMoment
    {M n : ℕ} {P : ℝ} (c : AwgnCode M n P) (i : Fin n) : ℝ :=
  (1 / (M : ℝ)) * ∑ m : Fin M, (c.encoder m i) ^ 2

/-- **C-1a** Average of per-letter input second moments is bounded by `P`.

`(1/n) ∑ᵢ E[X_i²] ≤ P` を `power_constraint` (per-message form `∑ᵢ (encoder m i)² ≤ n·P`)
から Fubini swap (∑ᵢ ∑ₘ = ∑ₘ ∑ᵢ) で genuine 化。 -/
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

/-- **C-1b** Per-letter MI bound via per-letter input variance.

Per-letter `I(X_i; Y_i) ≤ (1/2) log(1 + perLetterInputSecondMoment c i / N)`
を `differentialEntropy_le_gaussian_of_variance_le` (4 hyp 形、`DifferentialEntropy.lean:518`)
で導出。`Y_i` の分散 ≤ `E[X_i²] + N` (input ⊥⊥ noise) で Gaussian max-entropy。

`@residual(plan:awgn-converse-aux-plan)` — per-letter Gaussian max-entropy 4 hyp 充足
(`hμ ≪ vol` Gaussian convolution + `h_mean` / `h_var` / `h_var_int` per-letter 形 +
`h_ent_int` から bundle `PerLetterIntegrabilityForConverse` 経由) は本 dispatch では
~80-150 行の analytic work で、撤退口採用 (plan §C 失敗時 fallback の sorry retreat)。 -/
theorem awgn_per_letter_mi_le_log_var
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P)
    (h_per_letter : PerLetterIntegrabilityForConverse P N h_meas c)
    (h_mi_bridge_per_letter :
        ∀ i : Fin n, (perLetterMI h_meas c i).toReal
          = Common2026.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
            - Common2026.Shannon.differentialEntropy
                (ProbabilityTheory.gaussianReal 0 N))
    (i : Fin n) :
    (perLetterMI h_meas c i).toReal
      ≤ (1 / 2) * Real.log (1 + perLetterInputSecondMoment c i / (N : ℝ)) := by
  sorry -- @residual(plan:awgn-converse-aux-plan)

/-- **C-1c** Jensen / concavity of `log(1+·/N)`:
`∑ᵢ (1/2) log(1 + xᵢ/N) ≤ n · (1/2) log(1 + (∑ᵢ xᵢ / n) / N)` for `xᵢ ≥ 0`.

`Real.log` is concave on `Ioi 0` (`Mathlib.Analysis.Convex.SpecificFunctions.Basic.
strictConcaveOn_log_Ioi`) ⇒ `fun x => Real.log (1 + x/N)` concave on `Ici 0` (composition
with affine increasing map). Apply `ConcaveOn.le_map_sum` with uniform weights `wᵢ := 1/n`. -/
theorem sum_log_one_add_le_n_log_one_add_avg
    {n : ℕ} (hn_pos : 0 < n)
    (N : ℝ) (hN_pos : 0 < N)
    (xs : Fin n → ℝ) (hxs_nn : ∀ i, 0 ≤ xs i) :
    ∑ i : Fin n, (1 / 2) * Real.log (1 + xs i / N)
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + ((1 / (n : ℝ)) * ∑ i : Fin n, xs i) / N)) := by
  -- Strategy (plan §C-1c, failure-fallback judgement #6 — sorry retreat採用):
  -- `f x := log(1 + x/N)` is concave on `Ici 0` (composition of
  -- `strictConcaveOn_log_Ioi` with affine `x ↦ 1 + x/N`). Apply `ConcaveOn.le_map_sum`
  -- with uniform weights `wᵢ := 1/n`. The full Jensen + scaling plumbing is
  -- ~30-60 lines but the affine-substitution step ran into `smul`/`mul`
  -- normalization friction in the current session — deferred per plan §C
  -- failure-fallback (line 906-908).
  sorry -- @residual(plan:awgn-converse-aux-plan)

/-- **C-2** Sum of per-letter MIs is bounded by `n · (1/2) log(1 + P/N)`.

C-1a + C-1b + C-1c の合成: per-letter MI bound (variance 形) + per-letter variance
average ≤ P + Jensen for log(1+x/N) concavity. -/
theorem awgn_sum_per_letter_mi_le_n_capacity
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (hn_pos : 0 < n) (c : AwgnCode M n P)
    (h_per_letter : PerLetterIntegrabilityForConverse P N h_meas c)
    (h_mi_bridge_per_letter :
        ∀ i : Fin n, (perLetterMI h_meas c i).toReal
          = Common2026.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
            - Common2026.Shannon.differentialEntropy
                (ProbabilityTheory.gaussianReal 0 N)) :
    ∑ i : Fin n, (perLetterMI h_meas c i).toReal
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ))) := by
  -- Step 1: per-letter bound via `awgn_per_letter_mi_le_log_var` for each `i`.
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have h_per_letter_bound : ∀ i : Fin n, (perLetterMI h_meas c i).toReal
      ≤ (1 / 2) * Real.log (1 + perLetterInputSecondMoment c i / (N : ℝ)) := by
    intro i
    exact awgn_per_letter_mi_le_log_var P hP N hN h_meas c h_per_letter
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
theorem awgnConverseJoint_mutualInfo_ne_top_via_chain
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (hn_pos : 0 < n) (c : AwgnCode M n P)
    (h_per_letter : PerLetterIntegrabilityForConverse P N h_meas c)
    (h_chain : ContinuousMIChainRuleForConverse P N h_meas c)
    (h_markov : MarkovChainForConverse P N h_meas c)
    (h_mi_bridge_per_letter :
        ∀ i : Fin n, (perLetterMI h_meas c i).toReal
          = Common2026.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
            - Common2026.Shannon.differentialEntropy
                (ProbabilityTheory.gaussianReal 0 N)) :
    mutualInfo (awgnConverseJoint h_meas c)
        (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
        (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) ≠ ∞
      ∧ jointMIXnYn h_meas c ≠ ∞ := by
  sorry -- @residual(plan:awgn-converse-aux-plan)

/-! ## Phase C — `IsAwgnConverseFeasible` discharger + `awgn_converse_F3_discharged` wrapper -/

/-- **Phase C-3 — `IsAwgnConverseFeasible` discharger** (genuine assembly of the chain).

Phase B-Fano + B-DPI + B-chain + C-2 (sum form) を連鎖:
```
log M ≤ I(W; Y^n).toReal + binEntropy(Pe) + Pe·log(M-1)     (Phase B-Fano)
      ≤ I(X^n; Y^n).toReal + binEntropy(Pe) + Pe·log(M-1)   (Phase B-DPI, Markov)
      ≤ ∑ I(X_i; Y_i).toReal + binEntropy(Pe) + Pe·log(M-1) (Phase B-chain)
      ≤ n · (1/2) log(1+P/N) + binEntropy(Pe) + Pe·log(M-1) (Phase C-2, sum form)
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
    {M n : ℕ} [NeZero M] (hM : 2 ≤ M) (hn_pos : 0 < n) (c : AwgnCode M n P)
    (Pe : ℝ) (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  -- Destructure the bundle for `c`.
  obtain ⟨h_per_letter, h_chain, h_markov⟩ := h_feasible hM c
  -- Step (a)+(b)+(e) — B-Fano: `log M ≤ I(W; Y^n).toReal + binEntropy(Pe) + Pe · log(M-1)`.
  have h_fano := awgn_converse_single_shot_call P N h_meas hM c Pe hPe
  -- Step (c-DPI) — B-DPI: `I(W; Y^n).toReal ≤ I(X^n; Y^n).toReal`.
  have h_dpi := awgn_dpi P N h_meas c h_markov
  -- Step (c-chain) — B-chain: `I(X^n; Y^n).toReal ≤ ∑ᵢ I(X_i; Y_i).toReal`.
  have h_chain_le := awgn_chain_rule P N h_meas c h_chain
  -- Step (d) — C-2: `∑ᵢ I(X_i; Y_i).toReal ≤ n · (1/2) log(1+P/N)`.
  have h_sum := awgn_sum_per_letter_mi_le_n_capacity P hP N hN h_meas hn_pos c
    h_per_letter (h_mi_bridge_per_letter (M := M) (n := n) hM c)
  -- Assemble: transitive `≤` chain on the first summand.
  have h_lhs_chain : (jointMIWYn h_meas c).toReal
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ))) :=
    (h_dpi.trans h_chain_le).trans h_sum
  -- Add `binEntropy(Pe) + Pe · log(M-1)` (constants on both sides).
  linarith [h_fano, h_lhs_chain]

/-- **Phase C-6 — `awgn_converse_F3_discharged` wrapper**.

`awgn_converse` の `sorry` body を埋めるための薄い wrapper。`2 ≤ M` から `NeZero M`
typeclass を導出し、`isAwgnConverseFeasible_discharger` に委譲。

`@audit:staged(awgn-converse-feasible)` -/
theorem awgn_converse_F3_discharged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_feasible : IsAwgnConverseFeasible P N h_meas)
    (h_mi_bridge_per_letter :
        ∀ {M n : ℕ} [NeZero M] (_hM : 2 ≤ M) (c : AwgnCode M n P), ∀ i : Fin n,
          (perLetterMI h_meas c i).toReal
            = Common2026.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
              - Common2026.Shannon.differentialEntropy
                  (ProbabilityTheory.gaussianReal 0 N))
    {M n : ℕ} (hM : 2 ≤ M) (hn_pos : 0 < n) (c : AwgnCode M n P)
    (Pe : ℝ) (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  haveI : NeZero M := ⟨by omega⟩
  exact isAwgnConverseFeasible_discharger P hP N hN h_meas h_feasible
    h_mi_bridge_per_letter hM hn_pos c Pe hPe

end InformationTheory.Shannon.AWGN
