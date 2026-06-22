import InformationTheory.Shannon.RateDistortion.AchievabilityJointTypicalEncoder

/-!
# Rate-distortion achievability — codebook-level match probability

Lower bounds on the probability that some codeword of an i.i.d. product codebook
is jointly typical with a source word, and the source-averaged failure
probability obtained by integrating over the source distribution.

## Main statements

* `codebook_indep_no_match_prob_eq` — under the product measure
  `Measure.pi (fun _ : Fin M => p)`, the probability that no codeword matches `x`
  factors as `(1 - p.real {y | (x, y) ∈ JTS}) ^ M`.
* `single_codeword_typical_match_prob` — the probability that some codeword
  matches `x` is at least `1 - (1 - p.real {y | (x, y) ∈ JTS}) ^ M`.
* `encoder_failure_prob_le_exp_neg_M_avg` — exponentialization of the
  source-averaged failure-pow bound.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open InformationTheory.Shannon.ChannelCoding (jointlyTypicalSet measurableSet_jointlyTypicalSet)
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
variable [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]


/-! ## Source-averaged failure probability

Integrating the per-source-word bound `single_codeword_typical_match_prob` over
the source distribution `P_X` produces a bound on the source-averaged failure
probability. The non-trivial step is the Fubini-style bridge rewriting
`∫ x, p.real {y | (x, y) ∈ JTS} ∂P_X` as `(P_X.prod p).real (JTS)`.
-/

/-- **Utility**: `(1 - t)^M ≤ exp (-M·t)` for `0 ≤ t ≤ 1`. Used to convert the per-codeword
no-match probability into an exponential bound. -/
lemma one_sub_pow_le_exp_neg_mul (M : ℕ) {t : ℝ} (_h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (1 - t) ^ M ≤ Real.exp (-(M : ℝ) * t) := by
  have hbase : 1 - t ≤ Real.exp (-t) := Real.one_sub_le_exp_neg t
  have hbase_nn : 0 ≤ 1 - t := by linarith
  have hpow : (1 - t) ^ M ≤ Real.exp (-t) ^ M :=
    pow_le_pow_left₀ hbase_nn hbase M
  have hexp : Real.exp (-t) ^ M = Real.exp ((M : ℝ) * -t) := by
    rw [← Real.exp_nat_mul]
  calc (1 - t) ^ M
      ≤ Real.exp (-t) ^ M := hpow
    _ = Real.exp ((M : ℝ) * -t) := hexp
    _ = Real.exp (-(M : ℝ) * t) := by ring_nf


omit [DecidableEq α] [DecidableEq β] in
/-- **Exponentialization** of the source-averaged failure-pow bound.
Pointwise `(1 - p_typ x)^M ≤ exp(-M · p_typ x)`, then integrate. -/
@[entry_point]
theorem encoder_failure_prob_le_exp_neg_M_avg
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (ε : ℝ)
    (P_X : Measure (Fin n → α)) [IsProbabilityMeasure P_X]
    (p : Measure (Fin n → β)) [IsProbabilityMeasure p] :
    ∫ x, (1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ^ M ∂P_X
      ≤ ∫ x, Real.exp (-(M : ℝ) *
          p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ∂P_X := by
  have h_int_pow : Integrable (fun x ↦
      (1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ^ M) P_X := by
    have h_meas : Measurable (fun x : Fin n → α ↦
        (1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ^ M) :=
      measurable_of_finite _
    refine Integrable.mono' (g := fun _ ↦ (1 : ℝ)) (integrable_const 1)
      h_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x ↦ ?_)
    have h_pos : 0 ≤ p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε} :=
      measureReal_nonneg
    have h_le : p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε} ≤ 1 :=
      measureReal_le_one
    have hpow_nn : 0 ≤ (1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ^ M :=
      pow_nonneg (by linarith) M
    have hpow_le : (1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ^ M ≤ 1 := by
      have : 1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε} ≤ 1 := by linarith
      exact pow_le_one₀ (by linarith) this
    rw [Real.norm_eq_abs, abs_of_nonneg hpow_nn]
    exact hpow_le
  have h_int_exp : Integrable (fun x ↦
      Real.exp (-(M : ℝ) * p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε})) P_X := by
    have h_meas : Measurable (fun x : Fin n → α ↦
        Real.exp (-(M : ℝ) * p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε})) :=
      measurable_of_finite _
    refine Integrable.mono' (g := fun _ ↦ (1 : ℝ)) (integrable_const 1)
      h_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x ↦ ?_)
    have h_pos : 0 ≤ p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε} :=
      measureReal_nonneg
    have h_arg_le : -(M : ℝ) * p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε} ≤ 0 := by
      have hM : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.zero_le M
      nlinarith
    have h_exp_le : Real.exp (-(M : ℝ) *
        p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ≤ 1 :=
      Real.exp_le_one_iff.mpr h_arg_le
    have h_exp_nn : 0 ≤ Real.exp (-(M : ℝ) *
        p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg h_exp_nn]
    exact h_exp_le
  refine integral_mono h_int_pow h_int_exp ?_
  intro x
  have h_pos : 0 ≤ p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε} :=
    measureReal_nonneg
  have h_le : p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε} ≤ 1 :=
    measureReal_le_one
  exact one_sub_pow_le_exp_neg_mul M h_pos h_le

/-! ## Pigeonhole (existence from average)

A `Codebook M n β`-indexed function whose `codebookMeasure`-weighted average is `≤ B`
admits at least one deterministic codebook attaining `≤ B`. Verbatim mirror of
`ChannelCodingAchievability.exists_codebook_le_avg`, but stated generically over a
function `f : Codebook M n β → ℝ` so it serves both the channel-coding-style and
lossy-distortion-style consumers.
-/

open InformationTheory.Shannon.ChannelCoding (Codebook codebookMeasure)

omit [DecidableEq β] in
/-- **Pigeonhole (probabilistic-method form, lossy version).** If a real-valued
codebook functional has `codebookMeasure`-weighted average `≤ B`, then some
deterministic codebook achieves `f c ≤ B`.

Stated for a codebook over the reconstruction alphabet `β`; verbatim mirror of
`ChannelCodingAchievability.exists_codebook_le_avg`, but free of the
`codebookToCode / averageErrorProb` plumbing so it can wrap either the
channel-coding error functional or the lossy-distortion functional. -/
theorem exists_codebook_low_avg
    {M n : ℕ}
    (p : Measure β) [IsProbabilityMeasure p]
    (f : Codebook M n β → ℝ) {B : ℝ}
    (h_avg : ∑ c : Codebook M n β, (codebookMeasure p M n).real {c} * f c ≤ B) :
    ∃ c : Codebook M n β, f c ≤ B := by
  classical
  -- Convex combination `∑ w_i x_i ≤ B`, `w_i ≥ 0`, `∑ w_i = 1` ⟹ `∃ i, x_i ≤ B`.
  by_contra h_none
  simp only [not_exists, not_le] at h_none
  haveI : MeasurableSingletonClass (Fin n → β) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (Codebook M n β) := Pi.instMeasurableSingletonClass
  -- `∑ c, w c = 1` from `codebookMeasure` being a probability measure on a finite type.
  have h_sum_one : ∑ c : Codebook M n β, (codebookMeasure p M n).real {c} = 1 := by
    haveI : IsProbabilityMeasure (codebookMeasure p M n) :=
      codebookMeasure.instIsProbabilityMeasure p M n
    have h_real_univ : (codebookMeasure p M n).real
        ((Finset.univ : Finset (Codebook M n β)) : Set _) = 1 := by
      rw [Finset.coe_univ, measureReal_def, measure_univ]
      rfl
    have h_sum_eq :=
      sum_measureReal_singleton (μ := codebookMeasure p M n)
        (Finset.univ : Finset (Codebook M n β))
    rw [h_sum_eq, h_real_univ]
  have h_w_nn : ∀ c : Codebook M n β,
      0 ≤ (codebookMeasure p M n).real {c} := fun _ ↦ measureReal_nonneg
  -- Strict-sum contradiction.
  have h_contra : B < ∑ c : Codebook M n β,
      (codebookMeasure p M n).real {c} * f c := by
    calc B = B * 1 := by ring
      _ = B * ∑ c : Codebook M n β, (codebookMeasure p M n).real {c} := by rw [h_sum_one]
      _ = ∑ c : Codebook M n β, (codebookMeasure p M n).real {c} * B := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun _ _ ↦ by ring)
      _ < ∑ c : Codebook M n β, (codebookMeasure p M n).real {c} * f c := by
          have h_each : ∀ c : Codebook M n β,
              (codebookMeasure p M n).real {c} * B
                ≤ (codebookMeasure p M n).real {c} * f c := fun c ↦
            mul_le_mul_of_nonneg_left (h_none c).le (h_w_nn c)
          have h_exists_pos : ∃ c : Codebook M n β,
              0 < (codebookMeasure p M n).real {c} := by
            by_contra h_none_pos
            simp only [not_exists, not_lt] at h_none_pos
            have h_all_zero : ∀ c : Codebook M n β,
                (codebookMeasure p M n).real {c} = 0 := fun c ↦
              le_antisymm (h_none_pos c) (h_w_nn c)
            have : ∑ c : Codebook M n β,
                (codebookMeasure p M n).real {c} = 0 := by
              refine Finset.sum_eq_zero ?_
              intro c _; exact h_all_zero c
            rw [this] at h_sum_one
            exact one_ne_zero h_sum_one.symm
          obtain ⟨c₀, hc₀_pos⟩ := h_exists_pos
          have h_strict :
              (codebookMeasure p M n).real {c₀} * B
                < (codebookMeasure p M n).real {c₀} * f c₀ :=
            mul_lt_mul_of_pos_left (h_none c₀) hc₀_pos
          exact Finset.sum_lt_sum (fun i _ ↦ h_each i) ⟨c₀, Finset.mem_univ _, h_strict⟩
  exact (lt_irrefl _) (lt_of_le_of_lt h_avg h_contra)

end InformationTheory.Shannon
