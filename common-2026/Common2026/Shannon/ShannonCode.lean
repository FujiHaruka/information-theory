import Common2026.Meta.EntryPoint
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Shannon コード (per-symbol prefix code achievability)

B-8 ムーンショット ([`docs/shannon/shannon-code-moonshot-plan.md`](../../docs/shannon/shannon-code-moonshot-plan.md))。
Cover-Thomas 5.4 / 5.5 / 5.8.1。

有限アルファベット `α` 上の確率分布 `P` に対し、D-ary alphabet 上の Shannon 語長
`l(a) := ⌈-logb D P(a)⌉₊` で期待長が `H_D(P) ≤ E[L] < H_D(P) + 1` を達成する。

## 主定理

* `shannonLength_kraft_le_one` — Shannon 語長は Kraft 不等式を充足: `Σ D^{-l(a)} ≤ 1`
* `entropyD_le_expectedLength_of_kraft` — Gibbs 下界: 任意 lengths が Kraft 充足 ⟹ `H_D(P) ≤ E[L]`
* `expectedLength_shannon_lt_entropyD_add_one` — Shannon 上界: full support で `E[L_Shannon] < H_D(P) + 1`
* `shannonCode_expected_length_bounds` — sandwich 主定理:
  `H_D(P) ≤ E[L_Shannon] ∧ E[L_Shannon] < H_D(P) + 1`

## 設計メモ

- **語長水準**: Mathlib に prefix code 構造体は無く、`kraft_mcmillan_inequality` は
  `Finset (List α)` 表現 (文字列符号水準) であるため、本シードは語長 (`α → ℕ`) 水準で完結。
  Kraft 逆向き (prefix code 構成 from 充足) は **B-8' に切り出し**。
- **logb 規約**: `Real.logb D` で D-ary log を使用。`Real.log D` 因子は局所化。
- **support**: Phase B/C (下界) は full support 不要 (0 項は両側消える)。
  Phase D (上界、厳密不等式) は `∀ a, P.real {a} > 0` が本質的必要。
-/

namespace InformationTheory.Shannon.ShannonCode

open MeasureTheory Real
open scoped ENNReal NNReal

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### 定義 -/

/-- **D-ary Shannon entropy** (finite-alphabet, Real-valued):
`H_D(P) := -Σ a, P.real {a} · logb D P(a)`. -/
noncomputable def entropyD (D : ℝ) (P : Measure α) : ℝ :=
  -∑ a : α, P.real {a} * Real.logb D (P.real {a})

/-- **Shannon code 語長** `l(a) := ⌈-logb D P(a)⌉₊ : ℕ`.

`P.real {a} = 0` の場合は `logb D 0 = 0` (Mathlib convention) なので `l(a) = 0`. -/
noncomputable def shannonLength (D : ℝ) (P : Measure α) (a : α) : ℕ :=
  ⌈- Real.logb D (P.real {a})⌉₊

/-- **期待長** `E[L] := Σ a, P.real {a} · l(a)`. -/
noncomputable def expectedLength (P : Measure α) (l : α → ℕ) : ℝ :=
  ∑ a : α, P.real {a} * (l a : ℝ)

/-- **Kraft 和** `K_D(l) := Σ a, D^{-l(a)}` (Real-valued). -/
noncomputable def kraftSum (D : ℝ) (l : α → ℕ) : ℝ :=
  ∑ a : α, (D : ℝ) ^ (-(l a : ℤ))

/-! ### Phase A の補助補題 -/

/-- `logb` での Gibbs 一不等式 (核): `D > 1`, `0 < x` ⟹ `logb D x ≤ (x - 1) / log D`. -/
lemma logb_le_div_log {D x : ℝ} (hD : 1 < D) (hx : 0 < x) :
    Real.logb D x ≤ (x - 1) / Real.log D := by
  have hlogD_pos : 0 < Real.log D := Real.log_pos hD
  unfold Real.logb
  rw [div_le_div_iff_of_pos_right hlogD_pos]
  exact Real.log_le_sub_one_of_pos hx

/-- `D > 1` ⟹ `D ^ (- logb D x) = x` for `x > 0`. -/
lemma rpow_neg_logb_eq {D x : ℝ} (hD : 1 < D) (hx : 0 < x) :
    (D : ℝ) ^ (- Real.logb D x) = x⁻¹ := by
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  rw [Real.rpow_neg hD0.le, Real.rpow_logb hD0 hD.ne' hx]

/-- `D > 1`, `x > 0` ⟹ `D ^ ⌈-logb D x⌉₊ ≥ 1/x` (`⌈⌉` で `≥ -logb`). -/
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

/-- `D^(-l)` as `zpow` 形式 ↔ `rpow` 形式 (`D > 0`, `l : ℕ` so `-l : ℤ`). -/
lemma zpow_neg_natCast_eq_rpow {D : ℝ} (_ : 0 < D) (l : ℕ) :
    (D : ℝ) ^ (-(l : ℤ)) = (D : ℝ) ^ (-(l : ℝ)) := by
  rw [← Real.rpow_intCast]
  push_cast
  rfl

/-! ### Phase B — Shannon 語長の Kraft 充足 -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- 各 `a` で `D^{-shannonLength D P a} ≤ P.real {a}` (Shannon 語長の定義から).

`P.real {a} = 0` のとき `shannonLength = 0` だが、その項は LHS = 1 > 0 = RHS で **不成立**。
よって `P.real {a} > 0` の仮定下で成立する point-wise 不等式。 -/
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
/-- **Shannon 語長は Kraft を充足する**: `D > 1`, `P` proba ⟹ `Σ D^{-shannonLength a} ≤ 1`.

`P.real {a} = 0` の項は `shannonLength = 0` で `D^0 = 1` になり Kraft 和に余分な
寄与を与える。そこで proba `P` 上では support 制限 `0 < P.real {a}` のみで sum を取り、
support 外の項は `(if P.real{a} > 0 then ... else 0)` 形で消す版を主定理にする。

ここでは **full support 仮定** で main 形を述べる。 -/
@[entry_point]
theorem shannonLength_kraft_le_one
    {D : ℝ} (hD : 1 < D) (P : Measure α) [IsProbabilityMeasure P]
    (hP : ∀ a : α, 0 < P.real {a}) :
    kraftSum D (shannonLength D P) ≤ 1 := by
  classical
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  unfold kraftSum
  -- まず `D^(-(l a : ℤ)) = D^(-(l a : ℝ))` に書き換え
  have h_rewrite : ∀ a : α,
      (D : ℝ) ^ (-((shannonLength D P a : ℕ) : ℤ))
        = (D : ℝ) ^ (-((shannonLength D P a : ℕ) : ℝ)) := by
    intro a
    exact zpow_neg_natCast_eq_rpow hD0 _
  rw [Finset.sum_congr rfl (fun a _ => h_rewrite a)]
  -- 各項 ≤ P.real {a}, sum ≤ Σ P.real {a} = 1.
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

/-! ### Phase C — 期待長下界 (Gibbs) -/

omit [DecidableEq α] [Nonempty α] in
/-- **Gibbs 下界 (Shannon code lower bound)**: `D > 1`, `P` proba, 任意の `l : α → ℕ`
が Kraft 充足 `Σ D^{-l(a)} ≤ 1` ⟹ `H_D(P) ≤ E[L]`.

full support 仮定: support 外で `P(a) = 0` のとき `P(a) · logb D P(a) = 0` だが、
proof 中で `logb` の `>0` 引数性を使うため。 -/
@[entry_point]
theorem entropyD_le_expectedLength_of_kraft
    {D : ℝ} (hD : 1 < D) (P : Measure α) [IsProbabilityMeasure P]
    (hP : ∀ a : α, 0 < P.real {a})
    (l : α → ℕ) (h_kraft : kraftSum D l ≤ 1) :
    entropyD D P ≤ expectedLength P l := by
  classical
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  have hlogD_pos : 0 < Real.log D := Real.log_pos hD
  -- 戦略: H_D - E[L] ≤ 0 を示す。
  -- H_D - E[L] = -Σ P(a) logb P(a) - Σ P(a) l(a)
  --           = Σ P(a) · (-logb P(a) - l(a))
  --           = Σ P(a) · logb (D^{-l(a)} / P(a))
  --   ≤ Σ P(a) · (D^{-l(a)} / P(a) - 1) / log D
  --   = (Σ D^{-l(a)} - Σ P(a)) / log D
  --   ≤ (1 - 1) / log D = 0
  unfold entropyD expectedLength
  -- 個別項を再構成
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
  -- 主役: 各項 P(a) · (-logb P(a) - l(a)) ≤ (D^{-l(a)} - P(a)) / log D
  have h_term : ∀ a : α,
      P.real {a} * (- Real.logb D (P.real {a}) - (l a : ℝ))
        ≤ ((D : ℝ) ^ (-((l a : ℕ) : ℤ)) - P.real {a}) / Real.log D := by
    intro a
    have hPa : 0 < P.real {a} := hP a
    -- LHS = P(a) · logb D (D^{-l(a)} / P(a))
    -- まず -l(a) = logb D (D^{-l(a)}) を使うために
    -- - Real.logb D (P.real {a}) - (l a : ℝ) = Real.logb D ((D^{-l(a)}) / P.real {a})
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
    -- LHS = P(a) · logb (D^{-l(a)}/P(a)) ≤ P(a) · ((D^{-l(a)}/P(a) - 1)/log D)
    have h_ratio_pos : 0 < (D : ℝ) ^ (-(l a : ℝ)) / P.real {a} := by
      apply div_pos (Real.rpow_pos_of_pos hD0 _) hPa
    have h_logb_bound := logb_le_div_log hD h_ratio_pos
    have h_step : P.real {a} * Real.logb D ((D : ℝ) ^ (-(l a : ℝ)) / P.real {a})
        ≤ P.real {a} * (((D : ℝ) ^ (-(l a : ℝ)) / P.real {a} - 1) / Real.log D) := by
      apply mul_le_mul_of_nonneg_left h_logb_bound hPa.le
    refine h_step.trans ?_
    -- RHS 整理: P(a) · ((D^{-l(a)}/P(a) - 1)/log D) = (D^{-l(a)} - P(a)) / log D
    have h_simp : P.real {a} * (((D : ℝ) ^ (-(l a : ℝ)) / P.real {a} - 1) / Real.log D)
        = ((D : ℝ) ^ (-(l a : ℝ)) - P.real {a}) / Real.log D := by
      field_simp
    rw [h_simp]
    -- 変換 (-(l a : ℤ)) ↔ (-(l a : ℝ))
    rw [zpow_neg_natCast_eq_rpow hD0 _]
  -- Σ で結ぶ
  have h_sum_term : ∑ a, P.real {a} * (- Real.logb D (P.real {a}) - (l a : ℝ))
      ≤ ∑ a, ((D : ℝ) ^ (-((l a : ℕ) : ℤ)) - P.real {a}) / Real.log D :=
    Finset.sum_le_sum (fun a _ => h_term a)
  -- RHS = (kraftSum D l - 1) / log D
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
  -- Kraft 仮定で `(kraftSum - 1)/log D ≤ 0`
  have h_kraft_nonpos : (kraftSum D l - 1) / Real.log D ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · exact hlogD_pos.le
  -- 最終: -Σ f - Σ g ≤ 0  ⟹  -Σ f ≤ Σ g
  have h_final : -∑ a, f a - ∑ a, g a ≤ 0 := by
    rw [h_swap]
    exact h_sum_term.trans (h_rhs_eq.le.trans h_kraft_nonpos)
  linarith

/-! ### Phase D — 期待長上界 (Shannon 語長の `⌈⌉` 上界) -/

omit [DecidableEq α] in
/-- **Shannon code 上界**: `D > 1`, `P` proba (full support) ⟹
`E[L_Shannon] < H_D(P) + 1`. -/
@[entry_point]
theorem expectedLength_shannon_lt_entropyD_add_one
    {D : ℝ} (hD : 1 < D) (P : Measure α) [IsProbabilityMeasure P]
    (hP : ∀ a : α, 0 < P.real {a}) :
    expectedLength P (shannonLength D P) < entropyD D P + 1 := by
  classical
  unfold expectedLength entropyD shannonLength
  -- 各 a で `(⌈-logb P(a)⌉₊ : ℝ) < -logb P(a) + 1`
  -- Σ で乗じて `Σ P(a) · l(a) < Σ P(a) · (-logb P(a) + 1) = H_D + Σ P(a) = H_D + 1`
  -- まず Σ P(a) · (-logb P(a) + 1) = -Σ P(a)·logb P(a) + Σ P(a) = H_D + 1
  -- Σ P(a) = 1, `H_D = -Σ`
  -- 各項について
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
  -- 厳密不等式版: 少なくとも一つの a で `(⌈x⌉₊ : ℝ) < x + 1` & `P(a) > 0`
  -- 実は `⌈x⌉₊ < x + 1` (`Nat.ceil_lt_add_one`) は **任意** `x ≥ 0` で strict 成立
  -- そして `P` proba (Nonempty α) で `∃ a, P(a) > 0`. full support 仮定で全 a OK.
  -- なので `Σ_a P(a) · ⌈x_a⌉₊ < Σ_a P(a) · (x_a + 1)` (各項弱、少なくとも一項 strict)
  -- でも `P(a) > 0` 全部 & 各項 strict なら **Σ も strict** (sum_lt_sum)
  obtain ⟨a₀⟩ : Nonempty α := inferInstance
  -- a₀ で厳密
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
  -- Σ で結ぶ: sum_lt_sum_of_nonempty + 弱不等式 → 厳密
  have h_sum_lt :
      (∑ a : α, P.real {a} *
        ((⌈- Real.logb D (P.real {a})⌉₊ : ℕ) : ℝ))
        < ∑ a : α, P.real {a} * (- Real.logb D (P.real {a}) + 1) := by
    apply Finset.sum_lt_sum (fun a _ => h_each a)
    exact ⟨a₀, Finset.mem_univ _, h_strict⟩
  -- RHS = -Σ P(a)·logb P(a) + Σ P(a) = entropyD + 1
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
  -- 主張形
  convert h_sum_lt using 1

/-! ### Phase E — sandwich 主定理 -/

omit [DecidableEq α] in
/-- **Shannon code sandwich** (main theorem):
有限アルファベット `α` 上の確率測度 `P` (full support) に対し、
Shannon 語長 `l(a) := ⌈-logb D P(a)⌉₊` は

  `H_D(P) ≤ E[L] < H_D(P) + 1`

を達成する (Cover-Thomas 5.4 + 5.8.1). -/
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
