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
  sorry -- @residual(plan:awgn-converse-aux-plan)

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

/-- **Phase B-Fano**: Fano + DPI postprocess + entropy chain + `H(W) = log M` を
`shannon_converse_single_shot` 1 行呼出で集約。

結論: `log M ≤ I(W; Y^n).toReal + binEntropy(Pe) + Pe · log(M-1)`。

Phase B-Fano dispatch で fill 予定。Pe bridge (T-FFC-5、`errorProbAt` ↔ Fano
`errorProb` の同値性、~25-50 行) + MI-finite plumbing (~10-20 行) を内包。 -/
theorem awgn_converse_single_shot_call
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (hM : 2 ≤ M) (c : AwgnCode M n P)
    (Pe : ℝ) (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (jointMIWYn h_meas c).toReal
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  sorry -- @residual(plan:awgn-converse-aux-plan)

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
  sorry -- @residual(plan:awgn-converse-aux-plan)

/-- **Phase B-chain**: continuous MI chain rule for memoryless AWGN
`I(X^n; Y^n) ≤ ∑ᵢ I(X_i; Y_i)` を bundle 内 staged hyp で discharge。

Phase B-chain dispatch で fill 予定 (staged hyp 1 行 unfold)。 -/
theorem awgn_chain_rule
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P)
    (h_chain : ContinuousMIChainRuleForConverse P N h_meas c) :
    (jointMIXnYn h_meas c).toReal ≤ ∑ i : Fin n, (perLetterMI h_meas c i).toReal := by
  sorry -- @residual(plan:awgn-converse-aux-plan)

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

Phase B-Gaussian dispatch で fill 予定。 -/
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
  sorry -- @residual(plan:awgn-converse-aux-plan)

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
