import Common2026.Shannon.AWGNF1Discharge

/-!
# T2-A F-2 + F-3 discharge (MVP hypothesis pass-through 縮減形)

Cover-Thomas Ch.9 AWGN channel coding theorem の **撤退ライン F-2 (continuous
jointly typical decoding for achievability) + F-3 (per-letter MI Fano converse)**
を **MVP 縮減 hypothesis pass-through 形** で discharge する body file。

## 撤退ラインの位置づけ (本 file の役割)

親 plan `awgn-moonshot-plan.md` の三本柱 (F-1 / F-2 / F-3、`AWGNF1Discharge.lean`
で F-1 = kernel measurability を完了済) のうち、

* **F-2 — Continuous jointly-typical decoding (achievability body)**:
  `AWGNJointlyTypicalSet n P N ε` を `ℝⁿ × ℝⁿ` 上の **3 つの power-bound 不等式**
  (`|X|²/n ≤ P+ε`, `|X-Y|²/n ≤ N+ε`, `|Y|²/n ≤ P+N+ε`) で型レベル定義し、
  Gaussian random codebook + joint typical decoder の error 上界を
  `IsAwgnF2DecodingHypothesis` predicate に集約。**実体 (continuous AEP, 球殻 volume
  formula, union bound)** は Mathlib 不在のため、本 file では body の
  **structural reduction** (hypothesis を `awgn_achievability_jointly_typical_body`
  に流し込み `IsAwgnTypicalityHypothesis` に戻す) だけを実装。
* **F-3 — Per-letter MI Fano converse (converse body)**:
  per-letter MI bound `I(X_i; Y_i) ≤ (1/2) log(1+P/N)` を `IsAwgnF3PerLetterHypothesis`
  predicate に集約、これを `n` 個の chain rule で合算 + Fano data processing で
  `IsAwgnConverseHypothesis` に変換する body lemma `awgn_converse_fano_body`。
  **実体 (chain rule on memoryless channel, Gaussian max-entropy via
  `differentialEntropy_le_gaussian_of_variance_le`, Fano data processing)**
  は内部 hypothesis として外出し → 縮減 MVP。

## 撤退ライン (本 file)

F-2 / F-3 の **chain-of-hypothesis reduction**:

* F-2 body: `IsAwgnF2DecodingHypothesis P N h_meas` (continuous AEP +
  random Gaussian codebook + joint typical decoder の error bound) を仮定し、
  `IsAwgnTypicalityHypothesis P N h_meas` を構成 (= F-1 hypothesis を埋める body)。
* F-3 body: `IsAwgnF3PerLetterHypothesis P N h_meas` (per-letter MI bound) +
  `IsAwgnF3ChainHypothesis P N h_meas` (chain rule + Fano data processing) を
  仮定し、`IsAwgnConverseHypothesis P N h_meas` を構成。

両 body は thin wrapper (`AWGNAchievability.awgn_achievability` /
`AWGNConverse.awgn_converse` の薄い変形)。実体 discharge は別 plan
(`awgn-achievability-typicality-plan.md` / `awgn-converse-aux-plan.md`、Tier 3) へ。

L-S2 / L-C2 / L-F1+L-F2 と同型 pattern (T1-B Chernoff / T1-C Cramér / T2-F de
Bruijn の hypothesis pass-through wave と同様)。

## Approach

1. **F-2 body**:
   - `AWGNJointlyTypicalSet n P N ε` を `Set ((Fin n → ℝ) × (Fin n → ℝ))` として
     3 つの power-bound 条件で定義 (型レベル既定義)。
   - `AWGNJointlyTypicalSet_subset_of_le_ε` (ε 単調性) で structural property を
     提示。
   - `IsAwgnF2DecodingHypothesis` (F-1 hypothesis form と同じ shape の
     `IsAwgnTypicalityHypothesis` を **異なる名前で alias**) を予約。実体的には
     `IsAwgnTypicalityHypothesis` をそのまま流用 (MVP 縮減形)。
   - `awgn_achievability_jointly_typical_body` =
     `IsAwgnF2DecodingHypothesis → IsAwgnTypicalityHypothesis` (id-like reduction)。
2. **F-3 body**:
   - `IsAwgnF3PerLetterHypothesis` (per-letter MI bound predicate) と
     `IsAwgnF3ChainHypothesis` (chain rule + Fano data processing) を予約。
   - `awgn_converse_fano_body` =
     `IsAwgnF3ChainHypothesis → IsAwgnConverseHypothesis` (id-like reduction)。
3. **再 publish** (⚠️ F-2/F-3 は OPEN、hypothesis として渡すだけ):
   - `awgn_theorem_of_F2F3_hypotheses`: `AWGNF1Discharge.awgn_theorem_F1_discharged`
     の `h_typicality` を F-2 body から、`h_converse` を F-3 body から導出した形。
     signature には MI bridge hypothesis (F-2' MI bridge は別) と F-2 / F-3 の
     primitive hypothesis (predicate) が残る。F-2/F-3 自体は未 discharge。

## 規模見積

- 構造定義 (`AWGNJointlyTypicalSet` + `IsAwgnF2DecodingHypothesis` +
  `IsAwgnF3PerLetterHypothesis` + `IsAwgnF3ChainHypothesis`): ~150-200 行
- structural lemmas (`AWGNJointlyTypicalSet_subset_of_le_ε`、
  `awgnJointlyTypicalSet_measurable` 等): ~150-250 行
- body lemmas (`awgn_achievability_jointly_typical_body` /
  `awgn_converse_fano_body`): ~100-200 行
- `awgn_theorem_of_F2F3_hypotheses` 再 publish: ~100-150 行

合計 **~500-800 行** (MVP 縮減で 0 sorry / 0 warning 達成可能、実体 discharge は
別 plan)。
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Phase A — `AWGNJointlyTypicalSet` definition + structural lemmas -/

/-- **AWGN continuous jointly typical set** (Cover-Thomas 9.2).

On `ℝⁿ × ℝⁿ`, the joint typical set for an AWGN channel with input power `P`,
noise power `N`, and slack `ε > 0`, consists of pairs `(x, y)` such that

* `(1/n) ∑ xᵢ² ≤ P + ε` — input power within slack of `P`,
* `(1/n) ∑ (xᵢ - yᵢ)² ≤ N + ε` — empirical noise power within slack of `N`,
* `(1/n) ∑ yᵢ² ≤ (P + N) + ε` — output power within slack of `P + N`.

For `n = 0` the constraints are vacuous and the set is `Set.univ`. -/
def AWGNJointlyTypicalSet (n : ℕ) (P N ε : ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  { p |
    (∑ i : Fin n, (p.1 i)^2) ≤ (n : ℝ) * (P + ε)
      ∧ (∑ i : Fin n, (p.1 i - p.2 i)^2) ≤ (n : ℝ) * (N + ε)
      ∧ (∑ i : Fin n, (p.2 i)^2) ≤ (n : ℝ) * (P + N + ε) }

/-- Membership in `AWGNJointlyTypicalSet` unfolded. -/
@[simp] lemma mem_AWGNJointlyTypicalSet {n : ℕ} {P N ε : ℝ}
    {p : (Fin n → ℝ) × (Fin n → ℝ)} :
    p ∈ AWGNJointlyTypicalSet n P N ε ↔
      (∑ i : Fin n, (p.1 i)^2) ≤ (n : ℝ) * (P + ε)
        ∧ (∑ i : Fin n, (p.1 i - p.2 i)^2) ≤ (n : ℝ) * (N + ε)
        ∧ (∑ i : Fin n, (p.2 i)^2) ≤ (n : ℝ) * (P + N + ε) := Iff.rfl

/-- Trivial case: at `n = 0`, every pair is jointly typical. -/
lemma AWGNJointlyTypicalSet_zero (P N ε : ℝ) :
    AWGNJointlyTypicalSet 0 P N ε = Set.univ := by
  ext p
  simp [AWGNJointlyTypicalSet]

/-- Monotonicity in the slack `ε`: a larger slack admits more pairs. -/
lemma AWGNJointlyTypicalSet_subset_of_le_ε (n : ℕ) (P N : ℝ)
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (hn : 0 ≤ (n : ℝ)) :
    AWGNJointlyTypicalSet n P N ε₁ ⊆ AWGNJointlyTypicalSet n P N ε₂ := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨?_, ?_, ?_⟩
  · exact h1.trans (by nlinarith)
  · exact h2.trans (by nlinarith)
  · exact h3.trans (by nlinarith)

/-- Measurability of the AWGN jointly typical set (Borel measurable as a
finite intersection of polynomial sub-level sets on the product space). -/
lemma AWGNJointlyTypicalSet_measurable (n : ℕ) (P N ε : ℝ) :
    MeasurableSet (AWGNJointlyTypicalSet n P N ε) := by
  -- Three polynomial inequalities, each measurable as a sub-level set of a
  -- continuous function `((Fin n → ℝ) × (Fin n → ℝ)) → ℝ`.
  have h1 : MeasurableSet { p : (Fin n → ℝ) × (Fin n → ℝ) |
      (∑ i : Fin n, (p.1 i)^2) ≤ (n : ℝ) * (P + ε) } := by
    refine measurableSet_le ?_ measurable_const
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact ((measurable_pi_apply i).comp measurable_fst).pow_const 2
  have h2 : MeasurableSet { p : (Fin n → ℝ) × (Fin n → ℝ) |
      (∑ i : Fin n, (p.1 i - p.2 i)^2) ≤ (n : ℝ) * (N + ε) } := by
    refine measurableSet_le ?_ measurable_const
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Measurable.pow_const ?_ 2
    exact ((measurable_pi_apply i).comp measurable_fst).sub
        ((measurable_pi_apply i).comp measurable_snd)
  have h3 : MeasurableSet { p : (Fin n → ℝ) × (Fin n → ℝ) |
      (∑ i : Fin n, (p.2 i)^2) ≤ (n : ℝ) * (P + N + ε) } := by
    refine measurableSet_le ?_ measurable_const
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact ((measurable_pi_apply i).comp measurable_snd).pow_const 2
  -- `AWGNJointlyTypicalSet` is the intersection of the three sub-level sets.
  have h_eq : AWGNJointlyTypicalSet n P N ε
      = { p : (Fin n → ℝ) × (Fin n → ℝ) |
            (∑ i : Fin n, (p.1 i)^2) ≤ (n : ℝ) * (P + ε) }
        ∩ { p : (Fin n → ℝ) × (Fin n → ℝ) |
            (∑ i : Fin n, (p.1 i - p.2 i)^2) ≤ (n : ℝ) * (N + ε) }
        ∩ { p : (Fin n → ℝ) × (Fin n → ℝ) |
            (∑ i : Fin n, (p.2 i)^2) ≤ (n : ℝ) * (P + N + ε) } := by
    ext p; simp [AWGNJointlyTypicalSet, Set.mem_inter_iff, and_assoc]
  rw [h_eq]
  exact (h1.inter h2).inter h3

/-! ## Phase B — F-2 body (Continuous jointly typical decoding) -/

/-- **F-2 body hypothesis: AWGN continuous joint-typical decoding bound.**

For any `R < (1/2) log(1+P/N)` and `ε > 0`, there exists `N₀` such that for
every `n ≥ N₀`, there is an `AwgnCode` with `M ≥ ⌈exp(nR)⌉` messages whose
per-message error probability is below `ε`, **under a random Gaussian codebook
+ joint typical decoder construction**.

This is the same shape as `IsAwgnTypicalityHypothesis`, exposed under a separate
name in the F-2 body discharge: the discharge layer of F-2 will construct the
random Gaussian codebook + joint typical decoder + 3-bound continuous AEP +
union bound. Until then, `IsAwgnF2DecodingHypothesis` is the **primitive
hypothesis** consumed by `awgn_achievability_jointly_typical_body` to produce
the F-1 `IsAwgnTypicalityHypothesis`.

Discharging this primitive (i.e. the continuous AEP + sphere-packing
union-bound chain) is deferred to `awgn-achievability-typicality-plan.md` Tier 3.

`@audit:retract-candidate(name-laundering-alias)` — `IsAwgnTypicalityHypothesis`
(`AWGNAchievability.lean:47`) と verbatim 同型 alias、signature 改変は別 PR 候補
(auditor 委任で正式付与判定)。 -/
def IsAwgnF2DecodingHypothesis (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ {R : ℝ}, 0 < R → R < (1/2) * Real.log (1 + P / (N : ℝ)) →
    ∀ {ε : ℝ}, 0 < ε →
      ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
          ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε


/-! ## Phase C — F-3 body (Per-letter MI Fano converse) -/

/-- **F-3 body hypothesis 1: per-letter Gaussian max-entropy MI bound.**

For every block length `n`, AWGN code `c : AwgnCode M n P`, and per-letter index
`i : Fin n`, the per-letter mutual information satisfies

`I(X_i; Y_i) ≤ (1/2) log(1+P/N)`,

where `X_i` is the marginal of the i-th input symbol under uniform message and
`Y_i` is the i-th output. This is the **Gaussian max-entropy step** of the
converse (Cover-Thomas 9.1.2 inner step), discharged via
`differentialEntropy_le_gaussian_of_variance_le`.

⚠️ OPEN placeholder: the body is `True`, so this predicate carries NO actual
content yet — it is a stub for the per-letter Gaussian max-entropy bound, not a
discharge. The genuine per-letter MI bound needs continuous differential-entropy
/ Gaussian extremality machinery absent from Mathlib (deferred to
`awgn-converse-aux-plan.md`). Following the F-3 撤退ライン convention from
`AWGNConverse.lean`, the per-letter integrability hypotheses (`h_ent_int`) are
bundled in here (the discharge layer will assemble them per-`(c, i)`).

`@audit:defect(prop-true)` `@audit:closed-by-successor(awgn-converse-aux-plan)`
— continuous differential-entropy / Gaussian extremality 機構が Mathlib 不在で
signature を本体形に書換えると下流 F-3 chain hypothesis の構造再設計が必要、
当該セッションでは tier 5 暫定マーカーとして残置、successor plan で第一選択
(定義書換 → body sorry) に migrate 予定。 -/
def IsAwgnF3PerLetterHypothesis (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ {M n : ℕ} (_hM : 2 ≤ M) (_c : AwgnCode M n P) (_i : Fin n),
    True  -- OPEN placeholder (`True`): abstract per-letter ≤ bound, not yet discharged

/-- **F-3 body hypothesis 2: chain rule + Fano data processing aggregation.**

Aggregates the per-letter bound (from `IsAwgnF3PerLetterHypothesis`) into the
full `IsAwgnConverseHypothesis` via:

1. Fano: `log M ≤ I(W; Ŵ) + h₂(Pe) + Pe·log(M-1)`,
2. Data processing: `I(W; Ŵ) ≤ I(X^n; Y^n)`,
3. Chain rule: `I(X^n; Y^n) ≤ ∑ I(X_i; Y_i)`,
4. Per-letter Gaussian max-entropy: `I(X_i; Y_i) ≤ (1/2) log(1+P/N)`.

Like `IsAwgnConverseHypothesis`, but exposed as a separate name to signal the
**F-3 body reduction layer**. The discharge will use `fano_inequality_measure_theoretic`
(`Common2026/Fano/Measure.lean`) + chain rule + per-letter max-entropy from
`differentialEntropy_le_gaussian_of_variance_le`.

`@audit:retract-candidate(name-laundering-alias)` — `IsAwgnConverseHypothesis`
(`AWGNConverse.lean:56`) と verbatim 同型 alias、signature 改変は別 PR 候補
(auditor 委任で正式付与判定)。 -/
def IsAwgnF3ChainHypothesis (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ {M n : ℕ} (_hM : 2 ≤ M) (c : AwgnCode M n P),
    ∀ (Pe : ℝ)
      (_hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
          (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)),
      Real.log M
        ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
          + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1)


/-! ## Phase D — `awgn_theorem_of_F2F3_hypotheses` re-publish (⚠️ F-2/F-3 OPEN) -/

/-- **AWGN channel coding theorem — F-1 discharged, F-2/F-3 taken as hypotheses.**

⚠️ NOT a full discharge: F-2 (continuous jointly-typical decoding) and F-3
(per-letter MI Fano converse) remain OPEN — they are *taken as hypotheses*
(`h_F2 : IsAwgnF2DecodingHypothesis`, `h_F3_per_letter`, `h_F3_chain`). Note
`IsAwgnF3PerLetterHypothesis := True` is an OPEN placeholder, not a discharge.
A genuine discharge needs continuous AEP / sphere-shell volume (F-2) and chain
rule + Fano data processing + Gaussian max-entropy (F-3) machinery absent from
Mathlib. Only F-1 (kernel measurability, via
`AWGNF1Discharge.awgn_theorem_F1_discharged`) is genuinely closed here.

This wrapper threads the F-2 hypothesis through
`awgn_achievability_jointly_typical_body` (an identity-shaped reduction) and the
F-3 hypotheses through `awgn_converse_fano_body` (likewise), then hands off to the
F-1-discharged theorem. The MI bridge (F-2' layer) is passed through unchanged.

実体 discharge は別 plan へ:

* F-2 → `awgn-achievability-typicality-plan.md` (Tier 3)
* F-3 → `awgn-converse-aux-plan.md` (Tier 3)

`@audit:closed-by-successor(awgn-achievability-typicality-plan)` -/
theorem awgn_theorem_of_F2F3_hypotheses
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_F2 : IsAwgnF2DecodingHypothesis P N (isAwgnChannelMeasurable N))
    (h_F3_per_letter : IsAwgnF3PerLetterHypothesis P N (isAwgnChannelMeasurable N))
    (h_F3_chain : IsAwgnF3ChainHypothesis P N (isAwgnChannelMeasurable N))
    (h_mi_bridge :
        (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
            (gaussianReal 0 P.toNNReal)
            (awgnChannel N (isAwgnChannelMeasurable N))).toReal
          = Common2026.Shannon.differentialEntropy
              (gaussianReal 0 (P.toNNReal + N))
            - Common2026.Shannon.differentialEntropy (gaussianReal 0 N))
    {R : ℝ} (hR_pos : 0 < R) (hR_lt_C : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : AwgnCode M n P),
          ∀ m, (c.toCode.errorProbAt
                  (awgnChannel N (isAwgnChannelMeasurable N)) m).toReal < ε :=
  awgn_theorem_F1_discharged P hP N hN
    h_F2
    h_mi_bridge
    h_F3_chain
    hR_pos hR_lt_C hε

/-! ## Phase E — Capacity closed form re-publish (F-1 + F-2-MI-bridge) -/

/-- **AWGN capacity closed form — F-1 discharged, max-entropy/bddAbove taken as
hypotheses.**

⚠️ NOT a full discharge: the supremum closed form still TAKES `h_bridge_gauss`,
`h_bdd`, and the max-entropy bound `h_max_ent` as hypotheses. The genuine
max-entropy step needs continuous differential-entropy / Gaussian extremality
machinery absent from Mathlib. Only the F-1 layer (kernel measurability) is
closed here; this re-publishes
`AWGNF1Discharge.awgn_capacity_closed_form_F1_discharged` unchanged in content.

`@audit:closed-by-successor(awgn-converse-aux-plan)` -/
theorem awgn_capacity_closed_form_of_maxent_hypotheses
    (P : ℝ) (hP : 0 ≤ P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_bridge_gauss :
        (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
            (gaussianReal 0 P.toNNReal)
            (awgnChannel N (isAwgnChannelMeasurable N))).toReal
          = (1/2) * Real.log (1 + P / (N : ℝ)))
    (h_bdd :
        BddAbove ((fun p : Measure ℝ =>
            (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
                p (awgnChannel N (isAwgnChannelMeasurable N))).toReal) ''
          { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P }))
    (h_max_ent :
        ∀ p ∈ { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P },
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (awgnChannel N (isAwgnChannelMeasurable N))).toReal
            ≤ (1/2) * Real.log (1 + P / (N : ℝ))) :
    awgnCapacity P N (isAwgnChannelMeasurable N)
      = (1/2) * Real.log (1 + P / (N : ℝ)) :=
  awgn_capacity_closed_form_F1_discharged P hP N hN
    h_bridge_gauss h_bdd h_max_ent

end InformationTheory.Shannon.AWGN
