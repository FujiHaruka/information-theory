import Common2026.Shannon.RateDistortionAchievabilityPhaseB

/-!
# Rate-distortion achievability — Phase C-1 (codebook-level match probability)

[`docs/shannon/rate-distortion-achievability-plan.md`](../../../docs/shannon/rate-distortion-achievability-plan.md)

Phase C-1 lifts the per-codeword joint-typicality probability bound to the
codebook level. Given a source word `x : Fin n → α` and a product codebook
`c : Fin M → (Fin n → β)` drawn i.i.d. from `p`, we want a lower bound on
the probability that **some** codeword `c m` is jointly typical with `x`.

Three lemmas:

* `per_codeword_no_match_prob` — `p.real {y | (x, y) ∉ JTS} = 1 - p.real {y | (x, y) ∈ JTS}`
  (probabilistic complement rewrite under `IsProbabilityMeasure p`).
* `codebook_indep_no_match_prob_eq` — under the product measure
  `Measure.pi (fun _ : Fin M => p)`, the probability that *no* codeword matches `x`
  factors as `(1 - p.real {y | (x, y) ∈ JTS}) ^ M`.
* `single_codeword_typical_match_prob` — direct complement: the probability that
  *some* codeword matches `x` is at least `1 - (1 - p.real {y | (x, y) ∈ JTS}) ^ M`.

The main consumer is the random-coding average distortion bound (Phase D).
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

/-- **Per-codeword no-match probability**. Under any probability measure `p` on
codewords `Fin n → β`, the probability that a single random codeword `y` is *not*
jointly typical with `x` equals one minus the probability that it *is*. -/
lemma per_codeword_no_match_prob
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {n : ℕ} (ε : ℝ) (p : Measure (Fin n → β)) [IsProbabilityMeasure p]
    (x : Fin n → α) :
    p.real {y | (x, y) ∉ jointlyTypicalSet μ Xs Ys n ε}
      = 1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε} := by
  have h_compl : {y | (x, y) ∉ jointlyTypicalSet μ Xs Ys n ε}
      = ({y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε} : Set (Fin n → β))ᶜ := by
    ext y; simp
  have h_meas : MeasurableSet {y : Fin n → β | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε} :=
    (Set.toFinite _).measurableSet
  rw [h_compl, probReal_compl_eq_one_sub h_meas]

/-- **Codebook-level no-match probability**. Under the product measure
`Measure.pi (fun _ : Fin M => p)` on i.i.d. codebooks, the probability that *no*
codeword `c m` is jointly typical with `x` equals `(1 - p_typ(x))^M`, where
`p_typ(x) := p.real {y | (x, y) ∈ JTS}`. -/
lemma codebook_indep_no_match_prob_eq
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (ε : ℝ) (p : Measure (Fin n → β)) [IsProbabilityMeasure p]
    (x : Fin n → α) :
    (Measure.pi (fun _ : Fin M => p)).real
        {c : Fin M → (Fin n → β) | ∀ m, (x, c m) ∉ jointlyTypicalSet μ Xs Ys n ε}
      = (1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ^ M := by
  classical
  set B : Set (Fin n → β) := {y | (x, y) ∉ jointlyTypicalSet μ Xs Ys n ε} with hB_def
  have h_set_eq :
      {c : Fin M → (Fin n → β) | ∀ m, (x, c m) ∉ jointlyTypicalSet μ Xs Ys n ε}
        = Set.univ.pi (fun _ : Fin M => B) := by
    ext c
    simp [hB_def, Set.mem_pi]
  have h_meas_B : MeasurableSet B := (Set.toFinite _).measurableSet
  rw [h_set_eq]
  have h_pi_apply :
      (Measure.pi (fun _ : Fin M => p)) (Set.univ.pi (fun _ : Fin M => B))
        = ∏ _m : Fin M, p B := Measure.pi_pi _ _
  show ((Measure.pi (fun _ : Fin M => p)) (Set.univ.pi (fun _ : Fin M => B))).toReal = _
  rw [h_pi_apply, ENNReal.toReal_prod, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have h_real_B : p.real B = 1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε} :=
    per_codeword_no_match_prob μ Xs Ys ε p x
  show (p B).toReal ^ M = _
  rw [show (p B).toReal = p.real B from rfl, h_real_B]

/-- **Codebook-level match probability lower bound** (Phase C-1 main theorem).
The probability that *some* codeword `c m` is jointly typical with the source
word `x` is at least `1 - (1 - p_typ(x))^M`. -/
theorem single_codeword_typical_match_prob
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (ε : ℝ) (p : Measure (Fin n → β)) [IsProbabilityMeasure p]
    (x : Fin n → α) :
    1 - (1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ^ M
      ≤ (Measure.pi (fun _ : Fin M => p)).real
          {c : Fin M → (Fin n → β) | ∃ m, (x, c m) ∈ jointlyTypicalSet μ Xs Ys n ε} := by
  classical
  haveI : ∀ _ : Fin M, IsProbabilityMeasure p := fun _ => inferInstance
  haveI : IsProbabilityMeasure (Measure.pi (fun _ : Fin M => p)) := inferInstance
  have h_compl :
      {c : Fin M → (Fin n → β) | ∃ m, (x, c m) ∈ jointlyTypicalSet μ Xs Ys n ε}
        = ({c : Fin M → (Fin n → β) | ∀ m, (x, c m) ∉ jointlyTypicalSet μ Xs Ys n ε})ᶜ := by
    ext c; simp
  have h_meas : MeasurableSet
      {c : Fin M → (Fin n → β) | ∀ m, (x, c m) ∉ jointlyTypicalSet μ Xs Ys n ε} :=
    (Set.toFinite _).measurableSet
  rw [h_compl, probReal_compl_eq_one_sub h_meas,
      codebook_indep_no_match_prob_eq μ Xs Ys ε p x]

/-! ## Phase C-2: source-averaged failure probability

The Phase C-2 layer integrates the per-source-word bound from `single_codeword_typical_match_prob`
over the source distribution `P_X`, producing a bound on the *source-averaged* failure
probability that is later combined with the WLLN over the codebook in Phase D.

The non-trivial step is the Fubini-style bridge `p_typ_avg_eq_indep_prob`, which rewrites
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

/-- **Integrability of `p_typ`**. The map `x ↦ p.real {y | (x, y) ∈ JTS}` is bounded by `1`
and (vacuously, since the codomain is finite) measurable, hence integrable under any
probability measure `P_X`. -/
lemma p_typ_integrable
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {n : ℕ} (ε : ℝ)
    (P_X : Measure (Fin n → α)) [IsProbabilityMeasure P_X]
    (p : Measure (Fin n → β)) [IsProbabilityMeasure p] :
    Integrable (fun x => p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) P_X := by
  have h_meas : Measurable (fun x : Fin n → α =>
      p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) := by
    -- domain is a finite type, so every function is measurable.
    exact measurable_of_finite _
  refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const 1)
    h_meas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  have h_pos : 0 ≤ p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε} :=
    measureReal_nonneg
  have h_le : p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε} ≤ 1 := by
    have := measureReal_le_one (μ := p)
        (s := {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε})
    exact this
  rw [Real.norm_eq_abs, abs_of_nonneg h_pos]
  exact h_le

/-- **Source-averaged typicality probability**. Fubini-style identity rewriting
`∫ x, p.real {y | (x, y) ∈ JTS} ∂P_X` as `(P_X.prod p).real (JTS)`. -/
lemma p_typ_avg_eq_indep_prob
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {n : ℕ} (ε : ℝ)
    (P_X : Measure (Fin n → α)) [IsProbabilityMeasure P_X]
    (p : Measure (Fin n → β)) [IsProbabilityMeasure p] :
    ∫ x, p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε} ∂P_X
      = (P_X.prod p).real (jointlyTypicalSet μ Xs Ys n ε) := by
  set S : Set ((Fin n → α) × (Fin n → β)) := jointlyTypicalSet μ Xs Ys n ε with hS_def
  have hS_meas : MeasurableSet S := measurableSet_jointlyTypicalSet (μ := μ)
    (Xs := Xs) (Ys := Ys) (n := n) (ε := ε)
  have h_prod_apply : (P_X.prod p) S = ∫⁻ x, p (Prod.mk x ⁻¹' S) ∂P_X :=
    Measure.prod_apply hS_meas
  -- The pointwise identity `p.real {y | (x, y) ∈ S} = (p (Prod.mk x ⁻¹' S)).toReal`.
  have h_section :
      (fun x : Fin n → α => p.real {y | (x, y) ∈ S})
        = (fun x => (p (Prod.mk x ⁻¹' S)).toReal) := by
    funext x
    rfl
  -- Move toReal outside the integral via integral_toReal.
  have h_meas_p : Measurable (fun x : Fin n → α => p (Prod.mk x ⁻¹' S)) :=
    measurable_measure_prodMk_left hS_meas
  have h_lt_top : ∀ x : Fin n → α, p (Prod.mk x ⁻¹' S) < ∞ := fun x =>
    measure_lt_top p _
  have h_ae_lt : ∀ᵐ x ∂P_X, p (Prod.mk x ⁻¹' S) < ∞ :=
    Filter.Eventually.of_forall h_lt_top
  have h_int_toReal :
      ∫ x, (p (Prod.mk x ⁻¹' S)).toReal ∂P_X
        = (∫⁻ x, p (Prod.mk x ⁻¹' S) ∂P_X).toReal :=
    integral_toReal h_meas_p.aemeasurable h_ae_lt
  calc ∫ x, p.real {y | (x, y) ∈ S} ∂P_X
      = ∫ x, (p (Prod.mk x ⁻¹' S)).toReal ∂P_X := by rw [h_section]
    _ = (∫⁻ x, p (Prod.mk x ⁻¹' S) ∂P_X).toReal := h_int_toReal
    _ = ((P_X.prod p) S).toReal := by rw [← h_prod_apply]
    _ = (P_X.prod p).real S := rfl

/-- **Encoder failure probability — Fubini step**. Integrating the per-source-word
match-probability bound `single_codeword_typical_match_prob` over `P_X` yields a
bound on the joint probability (over source word + codebook) that *some* codeword
matches. -/
lemma encoder_failure_prob_integral_bound
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (ε : ℝ)
    (P_X : Measure (Fin n → α)) [IsProbabilityMeasure P_X]
    (p : Measure (Fin n → β)) [IsProbabilityMeasure p] :
    1 - ∫ x, (1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ^ M ∂P_X
      ≤ (P_X.prod (Measure.pi (fun _ : Fin M => p))).real
          {xc : (Fin n → α) × (Fin M → (Fin n → β))
              | ∃ m, (xc.1, xc.2 m) ∈ jointlyTypicalSet μ Xs Ys n ε} := by
  classical
  -- Abbreviate the codebook product measure and the failure event.
  set q : Measure (Fin M → (Fin n → β)) := Measure.pi (fun _ : Fin M => p) with hq_def
  haveI : IsProbabilityMeasure q := by rw [hq_def]; infer_instance
  set T : Set ((Fin n → α) × (Fin M → (Fin n → β))) :=
    {xc | ∃ m, (xc.1, xc.2 m) ∈ jointlyTypicalSet μ Xs Ys n ε} with hT_def
  have hT_meas : MeasurableSet T := (Set.toFinite _).measurableSet
  -- Pointwise: `1 - (1 - p_typ x)^M ≤ q (section_x T)`.
  have h_section_eq : ∀ x : Fin n → α,
      (Prod.mk x ⁻¹' T)
        = {c : Fin M → (Fin n → β) | ∃ m, (x, c m) ∈ jointlyTypicalSet μ Xs Ys n ε} := by
    intro x; rfl
  have h_pointwise : ∀ x : Fin n → α,
      1 - (1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ^ M
        ≤ q.real (Prod.mk x ⁻¹' T) := by
    intro x
    rw [h_section_eq x, hq_def]
    exact single_codeword_typical_match_prob μ Xs Ys ε p x
  -- Rewrite the RHS via `p_typ_avg_eq_indep_prob`-style Fubini.
  have h_prod_apply : (P_X.prod q) T = ∫⁻ x, q (Prod.mk x ⁻¹' T) ∂P_X :=
    Measure.prod_apply hT_meas
  have h_meas_q : Measurable (fun x : Fin n → α => q (Prod.mk x ⁻¹' T)) :=
    measurable_measure_prodMk_left hT_meas
  have h_ae_lt : ∀ᵐ x ∂P_X, q (Prod.mk x ⁻¹' T) < ∞ :=
    Filter.Eventually.of_forall (fun _ => measure_lt_top q _)
  have h_rhs_eq :
      (P_X.prod q).real T = ∫ x, q.real (Prod.mk x ⁻¹' T) ∂P_X := by
    show ((P_X.prod q) T).toReal = _
    rw [h_prod_apply, ← integral_toReal h_meas_q.aemeasurable h_ae_lt]
    rfl
  rw [h_rhs_eq]
  -- Integrability of pointwise LHS and RHS for `integral_mono` later.
  -- First, transform LHS `1 - ∫ ... ∂P_X` to `∫ (1 - ...) ∂P_X` via `integral_const`.
  have h_one_sub : (1 : ℝ) = ∫ _x, (1 : ℝ) ∂P_X := by
    rw [integral_const]; simp
  -- Integrability of the inner pow term and the section measure term.
  have h_int_pow : Integrable (fun x =>
      (1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ^ M) P_X := by
    have h_meas : Measurable (fun x : Fin n → α =>
        (1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ^ M) :=
      measurable_of_finite _
    refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const 1)
      h_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
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
  have h_int_match : Integrable (fun x => q.real (Prod.mk x ⁻¹' T)) P_X := by
    have h_meas : Measurable (fun x : Fin n → α =>
        q.real (Prod.mk x ⁻¹' T)) := h_meas_q.ennreal_toReal
    refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const 1)
      h_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h_pos : 0 ≤ q.real (Prod.mk x ⁻¹' T) := measureReal_nonneg
    have h_le : q.real (Prod.mk x ⁻¹' T) ≤ 1 := measureReal_le_one
    rw [Real.norm_eq_abs, abs_of_nonneg h_pos]
    exact h_le
  -- 1 - ∫ (1 - p_typ)^M = ∫ (1 - (1 - p_typ)^M)
  have h_lhs_eq :
      1 - ∫ x, (1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ^ M ∂P_X
        = ∫ x, 1 - (1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ^ M ∂P_X := by
    rw [integral_sub (integrable_const 1) h_int_pow, integral_const]
    simp
  rw [h_lhs_eq]
  refine integral_mono ?_ h_int_match ?_
  · -- Integrability of `1 - (...)^M`.
    exact (integrable_const 1).sub h_int_pow
  · intro x
    exact h_pointwise x

/-- **Exponentialization** of the source-averaged failure-pow bound.
Pointwise `(1 - p_typ x)^M ≤ exp(-M · p_typ x)`, then integrate. -/
theorem encoder_failure_prob_le_exp_neg_M_avg
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (ε : ℝ)
    (P_X : Measure (Fin n → α)) [IsProbabilityMeasure P_X]
    (p : Measure (Fin n → β)) [IsProbabilityMeasure p] :
    ∫ x, (1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ^ M ∂P_X
      ≤ ∫ x, Real.exp (-(M : ℝ) *
          p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ∂P_X := by
  have h_int_pow : Integrable (fun x =>
      (1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ^ M) P_X := by
    have h_meas : Measurable (fun x : Fin n → α =>
        (1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ^ M) :=
      measurable_of_finite _
    refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const 1)
      h_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
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
  have h_int_exp : Integrable (fun x =>
      Real.exp (-(M : ℝ) * p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε})) P_X := by
    have h_meas : Measurable (fun x : Fin n → α =>
        Real.exp (-(M : ℝ) * p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε})) :=
      measurable_of_finite _
    refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const 1)
      h_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
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

/-! ## Phase C-3: pigeonhole (existence from average)

A `Codebook M n β`-indexed function whose `codebookMeasure`-weighted average is `≤ B`
admits at least one deterministic codebook attaining `≤ B`. Verbatim mirror of
`ChannelCodingAchievability.exists_codebook_le_avg`, but stated generically over a
function `f : Codebook M n β → ℝ` so it serves both the channel-coding-style and
lossy-distortion-style consumers.
-/

open InformationTheory.Shannon.ChannelCoding (Codebook codebookMeasure)

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
      0 ≤ (codebookMeasure p M n).real {c} := fun _ => measureReal_nonneg
  -- Strict-sum contradiction.
  have h_contra : B < ∑ c : Codebook M n β,
      (codebookMeasure p M n).real {c} * f c := by
    calc B = B * 1 := by ring
      _ = B * ∑ c : Codebook M n β, (codebookMeasure p M n).real {c} := by rw [h_sum_one]
      _ = ∑ c : Codebook M n β, (codebookMeasure p M n).real {c} * B := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun _ _ => by ring)
      _ < ∑ c : Codebook M n β, (codebookMeasure p M n).real {c} * f c := by
          have h_each : ∀ c : Codebook M n β,
              (codebookMeasure p M n).real {c} * B
                ≤ (codebookMeasure p M n).real {c} * f c := fun c =>
            mul_le_mul_of_nonneg_left (h_none c).le (h_w_nn c)
          have h_exists_pos : ∃ c : Codebook M n β,
              0 < (codebookMeasure p M n).real {c} := by
            by_contra h_none_pos
            simp only [not_exists, not_lt] at h_none_pos
            have h_all_zero : ∀ c : Codebook M n β,
                (codebookMeasure p M n).real {c} = 0 := fun c =>
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
          exact Finset.sum_lt_sum (fun i _ => h_each i) ⟨c₀, Finset.mem_univ _, h_strict⟩
  exact (lt_irrefl _) (lt_of_le_of_lt h_avg h_contra)

end InformationTheory.Shannon
