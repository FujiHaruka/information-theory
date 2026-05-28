import Common2026.Meta.EntryPoint
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
  per-letter MI bound `I(X_i; Y_i) ≤ (1/2) log(1+P/N)` を `n` 個の chain rule で
  合算 + Fano data processing で converse に変換するライン。**実体 (chain rule on
  memoryless channel, Gaussian max-entropy via
  `differentialEntropy_le_gaussian_of_variance_le`, Fano data processing)** は
  Mathlib 不在。本 file が MVP で予約した F-3 hypothesis predicate はすべて
  撤回済 — genuine F-3 converse body は `AWGNConverseDischarge.lean` /
  `AWGNConverse.lean` に存在する。

## 現状 (本 file、2026-05-27/28 migration 後)

本 file が MVP として導入した F-2 / F-3 の hypothesis pass-through predicate
群および対応する body lemma はすべて撤回済 (load-bearing alias の
name-laundering 撤回 + vestigial `True` placeholder の retraction)。現在 file に
残るのは:

* `AWGNJointlyTypicalSet` 定義 + structural lemmas
  (`AWGNJointlyTypicalSet_subset_of_le_ε`、`AWGNJointlyTypicalSet_measurable`)。
* `awgn_theorem_of_F2F3_hypotheses` — `AWGNF1Discharge.awgn_theorem_F1_discharged`
  の薄い re-publish (F-4 kernel measurability + F-2 MI bridge を hypothesis に取る)。
* `awgn_capacity_closed_form_of_maxent_hypotheses` — capacity closed form の
  re-publish (max-entropy / bddAbove を hypothesis に取る)。

genuine F-2 (achievability) / F-3 (converse) body は別 file / 別 plan に存在:

* F-1 / F-2 achievability → `awgn-achievability-typicality-plan.md`
  (`awgn_achievability` body)。
* F-3 converse → `AWGNConverseDischarge.lean` (`perLetterMI` /
  `jointMIXnYn ≤ ∑ perLetterMI` / honest `h_mi_bridge_per_letter` residual) +
  `AWGNConverse.lean` (`awgn_converse`)、`awgn-converse-aux-plan.md`。
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
@[entry_point]
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
@[entry_point]
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

/-! ## Phase B — F-2 body (Continuous jointly typical decoding)

2026-05-27 F-1/F-3 peer migration: the verbatim-equivalent alias
`IsAwgnF2DecodingHypothesis` (a `name-laundering-alias` retract-candidate)
was removed together with its underlying `IsAwgnTypicalityHypothesis`
predicate. Phase B is intentionally empty now; F-2 body discharge lives in
the analytic `awgn-achievability-typicality-plan.md` successor. -/


/-! ## Phase C — F-3 body (Per-letter MI Fano converse)

2026-05-28 retraction: the vestigial per-letter `Prop := True` placeholder
predicate (tier-5 `defect(prop-true)`) was an orphan left when its sibling
chain-hypothesis predicate was deleted in the 2026-05-27 peer migration. Its
sole consumer (`awgn_theorem_of_F2F3_hypotheses`) never used it, so it has been
deleted (pure retraction, no content lost). The genuine F-3 per-letter converse
obligation lives in the converse files (`AWGNConverseDischarge.lean`'s
`perLetterMI` / `jointMIXnYn ≤ ∑ perLetterMI` / honest `h_mi_bridge_per_letter`
residual, plus `AWGNConverse.lean`'s `awgn_converse`). -/

/- **F-3 body hypothesis 2 (REMOVED)**: the verbatim-equivalent alias
`IsAwgnF3ChainHypothesis` (a `name-laundering-alias` retract-candidate) was
removed together with its underlying `IsAwgnConverseHypothesis` predicate
(2026-05-27 F-1/F-3 peer migration). The chain rule + Fano data processing
aggregation lives inside the analytic `awgn-converse-aux-plan.md` successor. -/


/-! ## Phase D — `awgn_theorem_of_F2F3_hypotheses` re-publish (⚠️ F-2/F-3 OPEN) -/

/-- **AWGN channel coding theorem — F-2/F-3 hypotheses removed (2026-05-27 peer migration).**

2026-05-27 F-1/F-3 peer migration: previously this wrapper consumed two
load-bearing aliases (`IsAwgnF2DecodingHypothesis` ≡ `IsAwgnTypicalityHypothesis`
and `IsAwgnF3ChainHypothesis` ≡ `IsAwgnConverseHypothesis`) which have been
deleted. 2026-05-28: the vestigial per-letter `:= True` placeholder predicate +
its unused parameter (never referenced in the body) were retracted; the genuine
F-3 per-letter obligation lives in the converse files
(`AWGNConverseDischarge.lean`). The wrapper now matches
`awgn_theorem_F1_discharged` exactly (F-1 / F-3 are absent as predicate hyps;
their bodies live as `sorry + @residual` inside `awgn_achievability` /
`awgn_converse`).

⚠️ NOT a full discharge: F-1 achievability body and F-3 converse body remain
OPEN. Only F-4 (kernel measurability) + F-2 MI bridge (via
`awgn_theorem_F1_discharged` ⟶ `awgn_channel_coding_theorem`) are exposed as
concrete hypotheses.

実体 discharge は別 plan へ:

* F-1 (achievability) → `awgn-achievability-typicality-plan.md`
* F-3 (converse)     → `awgn-converse-aux-plan.md`

`@audit:closed-by-successor(awgn-achievability-typicality-plan)` -/
theorem awgn_theorem_of_F2F3_hypotheses
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
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
    h_mi_bridge
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
