import InformationTheory.Meta.EntryPoint
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Shannon code (per-symbol prefix code achievability)

For a probability distribution `P` on a finite alphabet `α`, the Shannon codeword length
`l(a) := ⌈−logb D P(a)⌉₊` satisfies `H_D(P) ≤ E[L] < H_D(P) + 1`
(Cover–Thomas 5.4, 5.5, 5.8.1).

## Main definitions

* `entropyD` — D-ary Shannon entropy `H_D(P) := −∑ a, P.real {a} · logb D P(a)`.
* `shannonLength` — Shannon codeword length `l(a) := ⌈−logb D P(a)⌉₊`.
* `expectedLength` — expected length `E[L] := ∑ a, P.real {a} · l(a)`.
* `kraftSum` — Kraft sum `K_D(l) := ∑ a, D^{−l(a)}`.

## Main statements

* `shannonLength_kraft_le_one` — Shannon lengths satisfy Kraft: `K_D(shannonLength) ≤ 1`.
* `entropyD_le_expectedLength_of_kraft` — Gibbs lower bound: Kraft-feasible `l` satisfies
  `H_D(P) ≤ E[L]`.
* `expectedLength_shannon_lt_entropyD_add_one` — Shannon upper bound (full support):
  `E[L_Shannon] < H_D(P) + 1`.
* `shannonCode_expected_length_bounds` — sandwich: `H_D(P) ≤ E[L_Shannon] < H_D(P) + 1`.

## Implementation notes

The development works at the codeword-length level (`α → ℕ`) because Mathlib's
`kraft_mcmillan_inequality` uses a `Finset (List α)` representation. The reverse direction
(constructing a prefix code from a Kraft-feasible length function) is in
`ShannonCode/KraftReverse.lean`. We use `Real.logb D` for the D-ary logarithm throughout,
localizing the `Real.log D` factor. The upper bound (strict inequality) requires full
support `∀ a, P.real {a} > 0`; the lower bound does not.
-/

namespace InformationTheory.Shannon.ShannonCode

open MeasureTheory Real
open scoped ENNReal NNReal

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Definitions -/

/-- **D-ary Shannon entropy** (finite-alphabet, Real-valued):
`H_D(P) := -Σ a, P.real {a} · logb D P(a)`. -/
noncomputable def entropyD (D : ℝ) (P : Measure α) : ℝ :=
  -∑ a : α, P.real {a} * Real.logb D (P.real {a})

/-- **Shannon codeword length** `l(a) := ⌈−logb D P(a)⌉₊ : ℕ`.

When `P.real {a} = 0`, Mathlib sets `logb D 0 = 0` so `l(a) = 0`. -/
noncomputable def shannonLength (D : ℝ) (P : Measure α) (a : α) : ℕ :=
  ⌈- Real.logb D (P.real {a})⌉₊

/-- **Expected length** `E[L] := ∑ a, P.real {a} · l(a)`. -/
noncomputable def expectedLength (P : Measure α) (l : α → ℕ) : ℝ :=
  ∑ a : α, P.real {a} * (l a : ℝ)

/-- **Kraft sum** `K_D(l) := ∑ a, D^{−l(a)}` (Real-valued). -/
noncomputable def kraftSum (D : ℝ) (l : α → ℕ) : ℝ :=
  ∑ a : α, (D : ℝ) ^ (-(l a : ℤ))

/-! ### Auxiliary lemmas -/

/-- Gibbs log inequality in base `D`: `logb D x ≤ (x − 1) / log D` for `D > 1`, `x > 0`. -/
lemma logb_le_div_log {D x : ℝ} (hD : 1 < D) (hx : 0 < x) :
    Real.logb D x ≤ (x - 1) / Real.log D := by
  have hlogD_pos : 0 < Real.log D := Real.log_pos hD
  unfold Real.logb
  rw [div_le_div_iff_of_pos_right hlogD_pos]
  exact Real.log_le_sub_one_of_pos hx

/-- `D ^ (− logb D x) = x⁻¹` for `D > 1`, `x > 0`. -/
lemma rpow_neg_logb_eq {D x : ℝ} (hD : 1 < D) (hx : 0 < x) :
    (D : ℝ) ^ (- Real.logb D x) = x⁻¹ := by
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  rw [Real.rpow_neg hD0.le, Real.rpow_logb hD0 hD.ne' hx]

/-- `x⁻¹ ≤ D ^ ⌈−logb D x⌉₊` for `D > 1`, `x > 0`. -/
lemma rpow_natCast_shannonLength_ge_inv
    {D : ℝ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    x⁻¹ ≤ (D : ℝ) ^ ((⌈- Real.logb D x⌉₊ : ℕ) : ℝ) := by
  -- -logb D x ≤ ⌈-logb D x⌉₊
  have h_ceil : -Real.logb D x ≤ ((⌈- Real.logb D x⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil (-Real.logb D x)
  -- D^(-logb D x) ≤ D^⌈⌉₊, LHS = x⁻¹
  have h : (D : ℝ) ^ (-Real.logb D x)
      ≤ (D : ℝ) ^ ((⌈- Real.logb D x⌉₊ : ℕ) : ℝ) :=
    (Real.rpow_le_rpow_left_iff hD).mpr h_ceil
  rw [rpow_neg_logb_eq hD hx] at h
  exact h

/-- `D ^ (−(l : ℤ)) = D ^ (−(l : ℝ))` for `D > 0`, `l : ℕ`. -/
lemma zpow_neg_natCast_eq_rpow {D : ℝ} (_ : 0 < D) (l : ℕ) :
    (D : ℝ) ^ (-(l : ℤ)) = (D : ℝ) ^ (-(l : ℝ)) := by
  rw [← Real.rpow_intCast]
  push_cast
  rfl

/-! ### Kraft feasibility of Shannon lengths -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `D ^ (−shannonLength D P a) ≤ P.real {a}` for `P.real {a} > 0`. -/
lemma rpow_neg_shannonLength_le_real
    (D : ℝ) (hD : 1 < D) (P : Measure α) {a : α} (ha : 0 < P.real {a}) :
    (D : ℝ) ^ (-((shannonLength D P a : ℕ) : ℝ)) ≤ P.real {a} := by
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  unfold shannonLength
  -- 1/P.real{a} ≤ D^⌈⌉₊
  have h_ge : (P.real {a})⁻¹ ≤
      (D : ℝ) ^ ((⌈- Real.logb D (P.real {a})⌉₊ : ℕ) : ℝ) :=
    rpow_natCast_shannonLength_ge_inv hD ha
  -- take reciprocals: D^(-⌈⌉₊) ≤ P.real{a}
  have h_rpow_pos : 0 < (D : ℝ) ^ ((⌈- Real.logb D (P.real {a})⌉₊ : ℕ) : ℝ) :=
    Real.rpow_pos_of_pos hD0 _
  rw [Real.rpow_neg hD0.le, inv_le_comm₀ h_rpow_pos ha]
  exact h_ge

omit [DecidableEq α] [Nonempty α] in
/-- **Shannon code Kraft inequality**: `D > 1`, `P` a probability measure with full support
implies `∑ a, D ^ (−shannonLength D P a) ≤ 1`. -/
@[entry_point]
theorem shannonLength_kraft_le_one
    {D : ℝ} (hD : 1 < D) (P : Measure α) [IsProbabilityMeasure P]
    (hP : ∀ a : α, 0 < P.real {a}) :
    kraftSum D (shannonLength D P) ≤ 1 := by
  classical
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  unfold kraftSum
  -- rewrite D^(-(l a : ℤ)) = D^(-(l a : ℝ))
  have h_rewrite : ∀ a : α,
      (D : ℝ) ^ (-((shannonLength D P a : ℕ) : ℤ))
        = (D : ℝ) ^ (-((shannonLength D P a : ℕ) : ℝ)) := by
    intro a
    exact zpow_neg_natCast_eq_rpow hD0 _
  rw [Finset.sum_congr rfl (fun a _ => h_rewrite a)]
  -- each term ≤ P.real {a}; sum ≤ ∑ P.real {a} = 1
  calc (∑ a : α, (D : ℝ) ^ (-((shannonLength D P a : ℕ) : ℝ)))
      ≤ ∑ a : α, P.real {a} := by
        apply Finset.sum_le_sum
        intro a _
        exact rpow_neg_shannonLength_le_real D hD P (hP a)
    _ = 1 := by
        -- Σ P.real {a} = P.real univ = 1
        rw [show (∑ a : α, P.real {a}) = ∑ a ∈ (Finset.univ : Finset α), P.real {a} from rfl,
            MeasureTheory.sum_measureReal_singleton (s := (Finset.univ : Finset α))]
        rw [show ((Finset.univ : Finset α) : Set α) = Set.univ from Finset.coe_univ]
        simp [measureReal_def, measure_univ]

/-! ### Gibbs lower bound -/

omit [DecidableEq α] [Nonempty α] in
/-- **Gibbs lower bound**: for `D > 1`, probability measure `P` with full support, and
any Kraft-feasible lengths `l`, we have `H_D(P) ≤ E[L]`. -/
@[entry_point]
theorem entropyD_le_expectedLength_of_kraft
    {D : ℝ} (hD : 1 < D) (P : Measure α) [IsProbabilityMeasure P]
    (hP : ∀ a : α, 0 < P.real {a})
    (l : α → ℕ) (h_kraft : kraftSum D l ≤ 1) :
    entropyD D P ≤ expectedLength P l := by
  classical
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  have hlogD_pos : 0 < Real.log D := Real.log_pos hD
  -- Strategy: show H_D - E[L] ≤ 0.
  -- H_D - E[L] = ∑ P(a) · (−logb P(a) − l(a))
  --            = ∑ P(a) · logb (D^{−l(a)} / P(a))
  --   ≤ ∑ P(a) · (D^{−l(a)} / P(a) − 1) / log D
  --   = (∑ D^{−l(a)} − ∑ P(a)) / log D
  --   ≤ (1 − 1) / log D = 0
  unfold entropyD expectedLength
  -- per-term rewrite
  set f : α → ℝ := fun a => P.real {a} * Real.logb D (P.real {a})
  set g : α → ℝ := fun a => P.real {a} * (l a : ℝ)
  -- H_D - E[L] = -Σ f - Σ g = -Σ (f + g) = -Σ a, P(a) · (logb P(a) + l(a))
  --             = Σ a, P(a) · (-logb P(a) - l(a))
  --             = Σ a, P(a) · logb (D^{-l(a)} / P(a))
  show -∑ a, f a ≤ ∑ a, g a
  have h_swap : -∑ a, f a - ∑ a, g a = ∑ a, P.real {a} *
      (- Real.logb D (P.real {a}) - (l a : ℝ)) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    congr 1; ext a
    show -f a - g a = _
    simp [f, g]; ring
  -- per-term: P(a) · (−logb P(a) − l(a)) ≤ (D^{−l(a)} − P(a)) / log D
  have h_term : ∀ a : α,
      P.real {a} * (- Real.logb D (P.real {a}) - (l a : ℝ))
        ≤ ((D : ℝ) ^ (-((l a : ℕ) : ℤ)) - P.real {a}) / Real.log D := by
    intro a
    have hPa : 0 < P.real {a} := hP a
    -- LHS = P(a) · logb D (D^{-l(a)} / P(a))
    -- rewrite: −logb D P(a) − l(a) = logb D (D^{−l(a)} / P(a))
    have h_l_eq_logb : (l a : ℝ) = Real.logb D ((D : ℝ) ^ (l a : ℝ)) := by
      rw [Real.logb_rpow hD0 hD.ne']
    have h_rewrite_diff :
        - Real.logb D (P.real {a}) - (l a : ℝ)
          = Real.logb D ((D : ℝ) ^ (-(l a : ℝ)) / P.real {a}) := by
      have hD_pow_pos : 0 < (D : ℝ) ^ (-(l a : ℝ)) := Real.rpow_pos_of_pos hD0 _
      rw [Real.logb_div (ne_of_gt hD_pow_pos) (ne_of_gt hPa),
          show (D : ℝ) ^ (-(l a : ℝ)) = ((D : ℝ) ^ (l a : ℝ))⁻¹ from
            (Real.rpow_neg hD0.le _),
          Real.logb_inv, Real.logb_rpow hD0 hD.ne']
      ring
    rw [h_rewrite_diff]
    -- LHS = P(a) · logb (D^{−l(a)}/P(a)) ≤ P(a) · ((D^{−l(a)}/P(a) − 1)/log D)
    have h_ratio_pos : 0 < (D : ℝ) ^ (-(l a : ℝ)) / P.real {a} := by
      apply div_pos (Real.rpow_pos_of_pos hD0 _) hPa
    have h_logb_bound := logb_le_div_log hD h_ratio_pos
    have h_step : P.real {a} * Real.logb D ((D : ℝ) ^ (-(l a : ℝ)) / P.real {a})
        ≤ P.real {a} * (((D : ℝ) ^ (-(l a : ℝ)) / P.real {a} - 1) / Real.log D) := by
      apply mul_le_mul_of_nonneg_left h_logb_bound hPa.le
    refine h_step.trans ?_
    -- simplify RHS: P(a) · ((D^{−l(a)}/P(a) − 1)/log D) = (D^{−l(a)} − P(a)) / log D
    have h_simp : P.real {a} * (((D : ℝ) ^ (-(l a : ℝ)) / P.real {a} - 1) / Real.log D)
        = ((D : ℝ) ^ (-(l a : ℝ)) - P.real {a}) / Real.log D := by
      field_simp
    rw [h_simp]
    -- convert (−(l a : ℤ)) ↔ (−(l a : ℝ))
    rw [zpow_neg_natCast_eq_rpow hD0 _]
  -- sum the per-term bounds
  have h_sum_term : ∑ a, P.real {a} * (- Real.logb D (P.real {a}) - (l a : ℝ))
      ≤ ∑ a, ((D : ℝ) ^ (-((l a : ℕ) : ℤ)) - P.real {a}) / Real.log D :=
    Finset.sum_le_sum (fun a _ => h_term a)
  -- RHS = (kraftSum D l − 1) / log D
  have h_rhs_eq : (∑ a, ((D : ℝ) ^ (-((l a : ℕ) : ℤ)) - P.real {a}) / Real.log D)
      = (kraftSum D l - (1 : ℝ)) / Real.log D := by
    unfold kraftSum
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    congr 1
    -- Σ P.real {a} = 1
    rw [show (∑ a : α, P.real {a})
          = ∑ a ∈ (Finset.univ : Finset α), P.real {a} from rfl,
        MeasureTheory.sum_measureReal_singleton (s := (Finset.univ : Finset α))]
    rw [show ((Finset.univ : Finset α) : Set α) = Set.univ from Finset.coe_univ]
    simp [measureReal_def, measure_univ]
  -- Kraft hypothesis: (kraftSum − 1)/log D ≤ 0
  have h_kraft_nonpos : (kraftSum D l - 1) / Real.log D ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · exact hlogD_pos.le
  -- conclude: −∑ f − ∑ g ≤ 0 ⟹ −∑ f ≤ ∑ g
  have h_final : -∑ a, f a - ∑ a, g a ≤ 0 := by
    rw [h_swap]
    exact h_sum_term.trans (h_rhs_eq.le.trans h_kraft_nonpos)
  linarith

/-! ### Shannon upper bound -/

omit [DecidableEq α] in
/-- **Shannon code upper bound**: `D > 1`, probability measure `P` with full support ⟹
`E[L_Shannon] < H_D(P) + 1`. -/
@[entry_point]
theorem expectedLength_shannon_lt_entropyD_add_one
    {D : ℝ} (hD : 1 < D) (P : Measure α) [IsProbabilityMeasure P]
    (hP : ∀ a : α, 0 < P.real {a}) :
    expectedLength P (shannonLength D P) < entropyD D P + 1 := by
  classical
  unfold expectedLength entropyD shannonLength
  -- each a: ⌈−logb P(a)⌉₊ < −logb P(a) + 1
  -- summing: E[L] < H_D + ∑ P(a) = H_D + 1
  have h_each : ∀ a : α,
      P.real {a} * ((⌈- Real.logb D (P.real {a})⌉₊ : ℕ) : ℝ)
        ≤ P.real {a} * (- Real.logb D (P.real {a}) + 1) := by
    intro a
    have hPa : 0 ≤ P.real {a} := (hP a).le
    apply mul_le_mul_of_nonneg_left _ hPa
    -- (⌈x⌉₊ : ℝ) ≤ x + 1
    have hx_nn : 0 ≤ -Real.logb D (P.real {a}) := by
      -- logb D (P(a)) ≤ 0 since P(a) ≤ 1 (probability)
      have hP_le_one : P.real {a} ≤ 1 := by
        have : (P {a}).toReal ≤ (P Set.univ).toReal := by
          apply ENNReal.toReal_mono (by simp) (measure_mono (Set.subset_univ _))
        simpa [Measure.real, measure_univ] using this
      have := Real.logb_nonpos hD hPa hP_le_one
      linarith
    exact le_of_lt (Nat.ceil_lt_add_one hx_nn)
  -- strict: `Nat.ceil_lt_add_one` is strict for all x ≥ 0; full support ensures P(a₀) > 0
  obtain ⟨a₀⟩ : Nonempty α := inferInstance
  -- strict inequality at a₀
  have h_strict : P.real {a₀} *
      ((⌈- Real.logb D (P.real {a₀})⌉₊ : ℕ) : ℝ)
        < P.real {a₀} * (- Real.logb D (P.real {a₀}) + 1) := by
    have hPa : 0 < P.real {a₀} := hP a₀
    have hx_nn : 0 ≤ -Real.logb D (P.real {a₀}) := by
      have hP_le_one : P.real {a₀} ≤ 1 := by
        have : (P {a₀}).toReal ≤ (P Set.univ).toReal := by
          apply ENNReal.toReal_mono (by simp) (measure_mono (Set.subset_univ _))
        simpa [Measure.real, measure_univ] using this
      have := Real.logb_nonpos hD hPa.le hP_le_one
      linarith
    exact mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one hx_nn) hPa
  -- sum the bounds: weak at all terms, strict at a₀
  have h_sum_lt :
      (∑ a : α, P.real {a} *
        ((⌈- Real.logb D (P.real {a})⌉₊ : ℕ) : ℝ))
        < ∑ a : α, P.real {a} * (- Real.logb D (P.real {a}) + 1) := by
    apply Finset.sum_lt_sum (fun a _ => h_each a)
    exact ⟨a₀, Finset.mem_univ _, h_strict⟩
  -- RHS = −∑ P(a)·logb P(a) + ∑ P(a) = entropyD + 1
  have h_rhs : (∑ a : α, P.real {a} * (- Real.logb D (P.real {a}) + 1))
      = (-∑ a : α, P.real {a} * Real.logb D (P.real {a})) + 1 := by
    have h_split : ∀ a : α,
        P.real {a} * (- Real.logb D (P.real {a}) + 1)
          = - (P.real {a} * Real.logb D (P.real {a})) + P.real {a} := by
      intro a; ring
    rw [Finset.sum_congr rfl (fun a _ => h_split a)]
    rw [Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    -- Σ P.real {a} = 1
    have h_sum_one : (∑ a : α, P.real {a}) = (1 : ℝ) := by
      rw [show (∑ a : α, P.real {a})
            = ∑ a ∈ (Finset.univ : Finset α), P.real {a} from rfl,
          MeasureTheory.sum_measureReal_singleton (s := (Finset.univ : Finset α))]
      rw [show ((Finset.univ : Finset α) : Set α) = Set.univ from Finset.coe_univ]
      simp [measureReal_def, measure_univ]
    rw [h_sum_one]
  rw [h_rhs] at h_sum_lt
  -- convert to goal form
  convert h_sum_lt using 1

/-! ### Sandwich theorem -/

omit [DecidableEq α] in
/-- **Shannon code sandwich** (Cover–Thomas 5.4 + 5.8.1): for a probability measure `P`
with full support on a finite alphabet, the Shannon codeword lengths satisfy
`H_D(P) ≤ E[L_Shannon] < H_D(P) + 1`. -/
@[entry_point]
theorem shannonCode_expected_length_bounds
    {D : ℝ} (hD : 1 < D) (P : Measure α) [IsProbabilityMeasure P]
    (hP : ∀ a : α, 0 < P.real {a}) :
    entropyD D P ≤ expectedLength P (shannonLength D P) ∧
    expectedLength P (shannonLength D P) < entropyD D P + 1 := by
  refine ⟨?_, expectedLength_shannon_lt_entropyD_add_one hD P hP⟩
  exact entropyD_le_expectedLength_of_kraft hD P hP
    (shannonLength D P) (shannonLength_kraft_le_one hD P hP)

end InformationTheory.Shannon.ShannonCode
