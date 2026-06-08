import InformationTheory.Meta.EntryPoint
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Sanov の定理 — Phase A 形 (probability upper bound on type classes)

シードカード B-1 ([`docs/shannon/sanov-moonshot-plan.md`](../../docs/shannon/sanov-moonshot-plan.md))。
Cover-Thomas Theorem 11.1.4 (method of types, probability of a type class):

  `Q^n(T(P)) ≤ exp(-n · D(P‖Q))`

ここで `T(P) := { x : Fin n → α | ∀ a, #{i | x i = a} = n · P(a) }`
(empirical 分布が `P` に完全一致する系列の集合 = "type class")。

## 構成

* **Phase A** — type class 定義 + point-wise plumbing:
  * `typeCount x a := #{i : Fin n | x i = a}`
  * `typeClass P n : Set (Fin n → α)` (empirical = P)
  * `measurableSet_typeClass`, `typeClass_pi_singleton_eq` (`Q^n({x}) = ∏ Q(x_i)`)
  * `typeClass_log_ratio_eq`: `x ∈ T(P)` ⇒ `∑ log(Q/P)(x_i) = -n · klDivSumForm P Q`
* **Phase B** — Sanov A 主定理:
  * `klDivSumForm P Q := ∑ a, P(a) · (log P(a) - log Q(a))`
  * `typeClass_Qn_le` — `Q^n(T(P)) ≤ exp(-n · klDivSumForm P Q)`
  * `klDivSumForm_eq_toReal_klDiv` — `klDivSumForm = (klDiv P Q).toReal` (Bochner 形)
  * `typeClass_Qn_le_klDiv` — `.toReal` 形 corollary

## 設計メモ

* **Stein converse の特化版**: `steinTypicalSet_Q_prob_le` (Stein.lean:341) のロジックを
  「片側 inequality `S/n - K < ε`」→「両側 equality `S/n = K`」に置換しただけ。
  textbook の「`|T(P)| ≤ exp(n·H(P))` + `Q^n({x}) = exp(-n(H+D))`」二段論法を回避し、
  `Q^n(T) = exp(-n·D) · P^n(T) ≤ exp(-n·D)` で直接結ぶ。
* `klDivSumForm` (Real-valued finite-alphabet KL 展開) を主定理 LHS の指数に使い、
  `klDiv.toReal` 形は MaxEntropy.lean:123 のテンプレで等値性を別補題に分離。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal NNReal

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Phase A — type class definition + plumbing -/

/-- 系列 `x : Fin n → α` における letter `a` の出現回数 (= "type count")。 -/
noncomputable def typeCount {n : ℕ} (x : Fin n → α) (a : α) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x i = a)).card

/-- **Type class** `T(P)` — 系列のうち empirical 分布が `P` に完全一致するもの:
`x ∈ typeClass P n ↔ ∀ a, (typeCount x a : ℝ) = n · P.real {a}`. -/
noncomputable def typeClass (P : Measure α) (n : ℕ) : Set (Fin n → α) :=
  { x | ∀ a : α, (typeCount x a : ℝ) = (n : ℝ) * P.real {a} }


/-- **Finite-alphabet KL sum form**:
`klDivSumForm P Q := ∑ a, P(a) · (log P(a) − log Q(a))`。

Mathlib の `klDiv` を avoid して finite-alphabet 上の textbook 定義で
Sanov の指数を直接書くための shorthand。等値性 `klDivSumForm = (klDiv P Q).toReal`
は support 一致 (`P ≪ Q` + 両方 prob) のもとで別補題 `klDivSumForm_eq_toReal_klDiv` で証明。 -/
noncomputable def klDivSumForm (P Q : Measure α) : ℝ :=
  ∑ a : α, P.real {a} * (Real.log (P.real {a}) - Real.log (Q.real {a}))

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **Aggregation lemma** (Phase A の core): `x ∈ typeClass P n` ⇒
`∑ i : Fin n, (log P(x_i) - log Q(x_i)) = n · klDivSumForm P Q`.

証明: `prod_fiberwise_of_maps_to'` (Mathlib) で `∑ i, f (x i) = ∑ a, (typeCount x a) · f a`
に集約 → `typeClass` 仮定で `typeCount x a = n · P(a)` を代入。 -/
lemma sum_llrPmf_eq_of_mem_typeClass
    (P Q : Measure α) {n : ℕ} {x : Fin n → α}
    (hx : x ∈ typeClass P n) :
    (∑ i : Fin n, (Real.log (P.real {x i}) - Real.log (Q.real {x i})))
      = (n : ℝ) * klDivSumForm P Q := by
  classical
  set f : α → ℝ := fun a => Real.log (P.real {a}) - Real.log (Q.real {a}) with hf_def
  -- Step 1: aggregate `∑ i, f (x i) = ∑ a, (typeCount x a) • f a`.
  have h_agg : (∑ i : Fin n, f (x i))
      = ∑ a : α, ((typeCount x a : ℝ) * f a) := by
    -- `prod_fiberwise_of_maps_to'` (additive ⇒ sum_fiberwise_of_maps_to') —
    -- `∑ a, ∑ i ∈ univ with x i = a, f a = ∑ i, f (x i)`.
    have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)), x i ∈ (Finset.univ : Finset α) :=
      fun i _ => Finset.mem_univ _
    have h := Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset α)) h_maps f
    -- h : ∑ a ∈ univ, ∑ i ∈ univ with x i = a, f a = ∑ i ∈ univ, f (x i)
    rw [← h]
    -- ∑ i ∈ univ with x i = a, f a = (typeCount x a) * f a since f a is constant on the fiber.
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    rfl
  rw [h_agg]
  -- Step 2: substitute `typeCount x a = n · P.real {a}` from `hx`.
  have h_sub : (∑ a : α, (typeCount x a : ℝ) * f a)
      = ∑ a : α, ((n : ℝ) * P.real {a}) * f a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hx a]
  rw [h_sub]
  -- Step 3: re-associate `(n * P) * f = n * (P * f)`, pull out `n`, recognise `klDivSumForm`.
  rw [show (∑ a : α, ((n : ℝ) * P.real {a}) * f a)
        = (n : ℝ) * ∑ a : α, P.real {a} * f a from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring]
  rfl

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **Per-point ratio identity**: `x ∈ typeClass P n` ⇒
`∏ i, Q.real {x i} = (∏ i, P.real {x i}) · exp(-n · klDivSumForm P Q)`.

`P(a) > 0, Q(a) > 0` を要件として log/exp の往復を踏む。 -/
lemma typeClass_prod_ratio
    (P Q : Measure α)
    (hPpos : ∀ a : α, 0 < P.real {a})
    (hQpos : ∀ a : α, 0 < Q.real {a})
    {n : ℕ} {x : Fin n → α} (hx : x ∈ typeClass P n) :
    (∏ i : Fin n, Q.real {x i})
      = (∏ i : Fin n, P.real {x i}) * Real.exp (-((n : ℝ) * klDivSumForm P Q)) := by
  classical
  -- Step 1: pointwise log-difference identity:
  -- exp(-∑ i, (log P - log Q)(x_i)) = ∏ i, Q(x_i)/P(x_i)
  have h_exp_neg_diff : ∀ i : Fin n,
      Real.exp (-(Real.log (P.real {x i}) - Real.log (Q.real {x i})))
        = Q.real {x i} / P.real {x i} := by
    intro i
    have h_neg : -(Real.log (P.real {x i}) - Real.log (Q.real {x i}))
        = Real.log (Q.real {x i}) - Real.log (P.real {x i}) := by ring
    rw [h_neg, ← Real.log_div (hQpos (x i)).ne' (hPpos (x i)).ne']
    exact Real.exp_log (div_pos (hQpos (x i)) (hPpos (x i)))
  -- Step 2: ∏ Q/P = exp(-∑ (logP - logQ)) = exp(-n · klDivSumForm) via Phase A aggregation.
  have h_prod_ratio : (∏ i : Fin n, Q.real {x i} / P.real {x i})
      = Real.exp (-((n : ℝ) * klDivSumForm P Q)) := by
    have h_rhs : Real.exp (-(∑ i : Fin n, (Real.log (P.real {x i}) - Real.log (Q.real {x i}))))
        = ∏ i : Fin n, Q.real {x i} / P.real {x i} := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      exact Finset.prod_congr rfl fun i _ => h_exp_neg_diff i
    rw [← h_rhs, sum_llrPmf_eq_of_mem_typeClass P Q hx]
  -- Step 3: ∏ Q = (∏ Q/P) · (∏ P) — algebraic split.
  have h_split : (∏ i : Fin n, Q.real {x i})
      = (∏ i : Fin n, Q.real {x i} / P.real {x i}) * ∏ i : Fin n, P.real {x i} := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [div_mul_cancel₀ _ (hPpos (x i)).ne']
  rw [h_split, h_prod_ratio]
  ring

/-! ### Phase B — Sanov A 主定理 -/

set_option linter.unusedSectionVars false in
/-- **Sanov A 形 (probability upper bound on type classes)**:
`Q^n(T(P)) ≤ exp(-n · klDivSumForm P Q)`.

Cover-Thomas Theorem 11.1.4 の `klDivSumForm` 形式。`.toReal (klDiv P Q)` 形は
`klDivSumForm_eq_toReal_klDiv` + `typeClass_Qn_le_klDiv` 経由。

証明: Stein.lean:341 `steinTypicalSet_Q_prob_le` の特化:
  `Q^n(T) = ∑_{x∈T} Q^n({x}) = ∑_{x∈T} (∏ P(x_i)) · exp(-n·D)` (typeClass_prod_ratio)
        `= exp(-n·D) · ∑_{x∈T} ∏ P(x_i)`
        `≤ exp(-n·D) · ∑_{x : Fin n → α} ∏ P(x_i) = exp(-n·D) · 1`. -/
@[entry_point]
theorem typeClass_Qn_le
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPpos : ∀ a : α, 0 < P.real {a})
    (hQpos : ∀ a : α, 0 < Q.real {a})
    (n : ℕ) :
    ((Measure.pi (fun _ : Fin n => Q)) (typeClass P n)).toReal
      ≤ Real.exp (-((n : ℝ) * klDivSumForm P Q)) := by
  classical
  -- Setup: T as Finset, marginal abbreviations.
  set T : Finset (Fin n → α) := (typeClass P n).toFinite.toFinset with hT_def
  have hT_coe : (T : Set (Fin n → α)) = typeClass P n := by simp [hT_def]
  set p : α → ℝ := fun a => P.real {a} with hp_def
  set q : α → ℝ := fun a => Q.real {a} with hq_def
  set D : ℝ := klDivSumForm P Q with hD_def
  have hp_pos : ∀ a, 0 < p a := hPpos
  -- ∑ a, p a = 1.
  have hsum_p : (∑ a : α, p a) = 1 := by
    have h1 : (∑ a : α, p a) = P.real (Finset.univ : Finset α) := by
      simp [hp_def, sum_measureReal_singleton]
    rw [h1]
    show P.real ↑(Finset.univ : Finset α) = 1
    rw [Finset.coe_univ]
    exact probReal_univ
  -- Step 1: Q^n(T) (set form) → sum over T (Finset form).
  have h_pi_singleton_Q : ∀ x : Fin n → α,
      ((Measure.pi (fun _ : Fin n => Q)).real {x}) = ∏ i : Fin n, q (x i) := by
    intro x
    show ((Measure.pi (fun _ : Fin n => Q)) {x}).toReal = ∏ i : Fin n, q (x i)
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    rfl
  have h_pi_real_eq_sum :
      ((Measure.pi (fun _ : Fin n => Q)) (typeClass P n)).toReal
        = ∑ x ∈ T, ∏ i : Fin n, q (x i) := by
    have h_step : ((Measure.pi (fun _ : Fin n => Q)) (T : Set (Fin n → α))).toReal
        = ∑ x ∈ T, ((Measure.pi (fun _ : Fin n => Q)).real {x}) := by
      rw [← MeasureTheory.measureReal_def]
      rw [← MeasureTheory.sum_measureReal_singleton
        (μ := Measure.pi (fun _ : Fin n => Q)) T]
    rw [← hT_coe]
    rw [h_step]
    refine Finset.sum_congr rfl fun x _ => h_pi_singleton_Q x
  rw [h_pi_real_eq_sum]
  -- Step 2: per-`x ∈ T`, `∏ q (x i) = (∏ p (x i)) · exp(-n·D)`.
  have h_per_point : ∀ x ∈ T,
      ∏ i : Fin n, q (x i) = (∏ i : Fin n, p (x i)) * Real.exp (-((n : ℝ) * D)) := by
    intro x hx
    have hxT : x ∈ typeClass P n := (Set.Finite.mem_toFinset _).mp hx
    exact typeClass_prod_ratio P Q hPpos hQpos hxT
  -- Step 3: sum the per-point identities, factor out exp(-n·D), use ∑ ∏ p ≤ 1.
  calc (∑ x ∈ T, ∏ i : Fin n, q (x i))
      = ∑ x ∈ T, (∏ i : Fin n, p (x i)) * Real.exp (-((n : ℝ) * D)) :=
          Finset.sum_congr rfl h_per_point
    _ = (∑ x ∈ T, ∏ i : Fin n, p (x i)) * Real.exp (-((n : ℝ) * D)) := by
          rw [← Finset.sum_mul]
    _ ≤ 1 * Real.exp (-((n : ℝ) * D)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          -- ∑ x ∈ T, ∏ p ≤ ∑ x : Fin n → α, ∏ p = 1.
          have h_total : (∑ x : Fin n → α, ∏ i : Fin n, p (x i)) = 1 := by
            classical
            rw [← Fintype.piFinset_univ, Finset.sum_prod_piFinset]
            simp [hsum_p]
          have h_nonneg : ∀ x : Fin n → α, 0 ≤ ∏ i : Fin n, p (x i) := by
            intro x
            exact Finset.prod_nonneg (fun i _ => (hp_pos (x i)).le)
          calc (∑ x ∈ T, ∏ i : Fin n, p (x i))
              ≤ ∑ x : Fin n → α, ∏ i : Fin n, p (x i) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro x _; exact Finset.mem_univ x
                · intro x _ _; exact h_nonneg x
            _ = 1 := h_total
    _ = Real.exp (-((n : ℝ) * D)) := one_mul _

/-! ### Phase B (corollary) — `.toReal (klDiv P Q)` 形 -/

omit [DecidableEq α] [Nonempty α] in
/-- **`klDivSumForm` = `(klDiv P Q).toReal`** (finite alphabet support 一致).

MaxEntropy.lean:123 `klDiv_uniformOn_univ_toReal_eq` のテンプレ:
`toReal_klDiv_of_measure_eq` で `(klDiv P Q).toReal = ∫ a, llr P Q a ∂P`、
`integral_fintype` で Bochner ⇒ finite sum、`llr` を point-wise log で展開。 -/
@[entry_point]
theorem klDivSumForm_eq_toReal_klDiv
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (hQpos : ∀ a : α, 0 < Q.real {a}) :
    klDivSumForm P Q = (klDiv P Q).toReal := by
  classical
  -- toReal_klDiv_of_measure_eq (h : P ≪ Q) (h_eq : P univ = Q univ).
  have h_univ : P Set.univ = Q Set.univ := by rw [measure_univ, measure_univ]
  -- Reduce RHS to Bochner integral.
  rw [toReal_klDiv_of_measure_eq hPQ h_univ]
  -- Bochner integral on a fintype → Finset.sum.
  have h_int : Integrable (llr P Q) P := by
    refine ⟨(measurable_llr _ _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_fintype]
    exact ENNReal.sum_lt_top.mpr fun _ _ =>
      ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)
  rw [integral_fintype h_int]
  -- ∑ a, P.real {a} • llr P Q a = ∑ a, P.real {a} * (log P.real{a} - log Q.real{a}).
  unfold klDivSumForm
  refine Finset.sum_congr rfl fun a _ => ?_
  -- term-wise equality.
  by_cases hPa : P.real {a} = 0
  · rw [hPa]; simp
  have hPa_pos : 0 < P.real {a} :=
    lt_of_le_of_ne measureReal_nonneg (Ne.symm hPa)
  have hP_ne : P {a} ≠ 0 := by
    intro h
    apply hPa
    rw [Measure.real, h]; rfl
  -- rnDeriv identification: (P.rnDeriv Q a) * Q {a} = P {a}.
  have h_rnD_enn : (P.rnDeriv Q a) * Q {a} = P {a} := by
    have h_wd : Q.withDensity (P.rnDeriv Q) = P :=
      Measure.withDensity_rnDeriv_eq P Q hPQ
    have h1 : (Q.withDensity (P.rnDeriv Q)) {a} = P {a} := by rw [h_wd]
    rw [withDensity_apply _ (measurableSet_singleton a), lintegral_singleton] at h1
    exact h1
  have h_rnD_real : (P.rnDeriv Q a).toReal * Q.real {a} = P.real {a} := by
    rw [Measure.real, Measure.real, ← ENNReal.toReal_mul, h_rnD_enn]
  have hQa_pos : 0 < Q.real {a} := hQpos a
  -- (P.rnDeriv Q a).toReal = P.real {a} / Q.real {a}.
  have h_rnD_eq : (P.rnDeriv Q a).toReal = P.real {a} / Q.real {a} := by
    have hQne : Q.real {a} ≠ 0 := hQa_pos.ne'
    field_simp at h_rnD_real ⊢
    linarith [h_rnD_real]
  -- llr = log (rnDeriv).toReal = log(P/Q) = log P - log Q.
  have hratio_pos : 0 < P.real {a} / Q.real {a} := div_pos hPa_pos hQa_pos
  have h_llr : llr P Q a = Real.log (P.real {a}) - Real.log (Q.real {a}) := by
    unfold llr
    rw [h_rnD_eq, Real.log_div hPa_pos.ne' hQa_pos.ne']
  rw [h_llr, smul_eq_mul]

set_option linter.unusedSectionVars false in
/-- **Sanov A 形 `.toReal (klDiv P Q)` 形 corollary**:
`Q^n(T(P)) ≤ exp(-n · (klDiv P Q).toReal)`. -/
@[entry_point]
theorem typeClass_Qn_le_klDiv
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPpos : ∀ a : α, 0 < P.real {a})
    (hQpos : ∀ a : α, 0 < Q.real {a})
    (hPQ : P ≪ Q)
    (n : ℕ) :
    ((Measure.pi (fun _ : Fin n => Q)) (typeClass P n)).toReal
      ≤ Real.exp (-((n : ℝ) * (klDiv P Q).toReal)) := by
  have h_eq : klDivSumForm P Q = (klDiv P Q).toReal :=
    klDivSumForm_eq_toReal_klDiv P Q hPQ hQpos
  have h_main := typeClass_Qn_le P Q hPpos hQpos n
  rw [h_eq] at h_main
  exact h_main

end InformationTheory.Shannon
