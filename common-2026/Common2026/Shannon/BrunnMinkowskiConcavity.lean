import Common2026.Shannon.BrunnMinkowski
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential

/-!
# T2-E Brunn-Minkowski — concavity-of-log bridge (L-BM2 / L-BM3 本体 discharge)

`Common2026/Shannon/BrunnMinkowski.lean` (310 行, 主形 + 凸体系を hypothesis
pass-through で publish 済) の **L-BM2 + L-BM3 接続 wrapper** を本 file で
discharge する。

具体的には Brunn-Minkowski の `vol(A+B)^{1/n} ≥ vol(A)^{1/n} + vol(B)^{1/n}`
形を導く際の **concavity-of-log bridge** —

  「`e^c ≥ e^a + e^b` から `c ≥ log (e^a + e^b)` を取り出す」

— の正確な形と、ナイーブな素朴版 (`c² ≥ a² + b² → c ≥ a + b` は
**一般には偽** — 例: `c = √2, a = b = 1`) との対比を本 file 内で
明示する。

## 構成

* §A — `concavity_log_ineq`: `log (1 + x) ≤ x` (concavity-of-log の
  典型形, `Real.log_le_sub_one_of_pos` を経由) と上位 corollary
* §B — `square_to_linear_bridge_naive_counterexample`: `c² ≥ a² + b²`
  からは一般に `c ≥ a + b` を取り出せないことの反例
* §C — `square_to_linear_bridge_log`: 正しい log-exp 形
  `e^c ≥ e^a + e^b → c ≥ log (e^a + e^b)`
* §D — `_concavity` wrappers: 既存 `BrunnMinkowski.lean` の L-BM2 / L-BM3
  hypothesis を本 file の補題で接続する形に specialize

## Mathlib-shape-driven

本 file は以下の Mathlib 結論形に直結:

* `Real.log_le_sub_one_of_pos : 0 < x → Real.log x ≤ x - 1`
* `Real.add_one_le_exp : ∀ x, x + 1 ≤ Real.exp x`
* `Real.log_le_iff_le_exp : 0 < x → (Real.log x ≤ y ↔ x ≤ Real.exp y)`
* `Real.le_log_iff_exp_le : 0 < y → (x ≤ Real.log y ↔ Real.exp x ≤ y)`
* `Real.exp_log : 0 < x → Real.exp (Real.log x) = x`
* `Real.log_exp : Real.log (Real.exp x) = x`

## 撤退ライン

本 file は **`BrunnMinkowski.lean` の L-BM1/L-BM2/L-BM3 predicate を
そのまま** 受け取り、`Real.exp` / `Real.log` の上で純粋な実数不等式
として discharge する。Brunn-Minkowski の本物の volume 計算 (L-BM3
の `MeasurableSet (A + B)` の真の証明、L-BM2 の `uniform = log vol` の
真の証明) は本 file scope 外。
-/

namespace InformationTheory.Shannon.BrunnMinkowski

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology Pointwise

/-! ## §A — concavity-of-log 基本補題 -/

/-- **concavity-of-log basic form**: `0 < 1 + x` ならば `log (1 + x) ≤ x`.

`Real.log_le_sub_one_of_pos : 0 < x → log x ≤ x - 1` を `x := 1 + x` に
適用した形。Cover-Thomas Ch.17 で繰り返し使う凹性の基礎不等式。 -/
theorem concavity_log_ineq {x : ℝ} (hx : 0 < 1 + x) :
    Real.log (1 + x) ≤ x := by
  have h := Real.log_le_sub_one_of_pos hx
  -- `log (1 + x) ≤ (1 + x) - 1 = x`
  linarith

/-- **Dual form (concavity-of-exp basic)**: `x + 1 ≤ exp x`.

`Real.add_one_le_exp` のそのままラップ。`concavity_log_ineq` と対をなし、
本 file の L-BM3 系 discharge で利用。 -/
theorem concavity_exp_ineq (x : ℝ) : x + 1 ≤ Real.exp x :=
  Real.add_one_le_exp x

/-- **strict form**: `0 < y` のとき `log y ≤ y - 1` (Mathlib 直
ラップ, naming alignment 用)。 -/
theorem concavity_log_ineq_strict {y : ℝ} (hy : 0 < y) :
    Real.log y ≤ y - 1 :=
  Real.log_le_sub_one_of_pos hy

/-! ## §B — 素朴版 `c² ≥ a² + b² → c ≥ a + b` の反例 -/

/-- **Naive square-to-linear bridge counterexample**: `a, b ≥ 0` かつ
`c² ≥ a² + b²` は **一般には** `c ≥ a + b` を意味しない。

具体的反例: `a = b = 1`, `c = Real.sqrt 2`. 計算:
* `c² = 2 ≥ 1 + 1 = a² + b²` ✓
* `c = √2 ≈ 1.414 < 2 = a + b` ✗

これは Brunn-Minkowski の "naive sqrt 形" `vol(A+B)^{1/n} ≥ vol(A)^{1/n} + vol(B)^{1/n}`
が `vol(A+B)^{2/n} ≥ vol(A)^{2/n} + vol(B)^{2/n}` から **直接は** 出ない
ことの本質的原因。正しい経路は log-exp 形 `square_to_linear_bridge_log`
を用いる。 -/
theorem square_to_linear_bridge_naive_counterexample :
    ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧
      c ^ 2 ≥ a ^ 2 + b ^ 2 ∧ ¬ (c ≥ a + b) := by
  refine ⟨1, 1, Real.sqrt 2, by norm_num, by norm_num, Real.sqrt_nonneg _, ?_, ?_⟩
  · -- `(√2)² = 2 ≥ 1² + 1² = 2`
    have h : Real.sqrt 2 ^ 2 = 2 := by
      rw [sq]
      exact Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
    rw [h]; norm_num
  · -- `√2 < 2 = 1 + 1`, so `¬ (√2 ≥ 1 + 1)`.
    intro hc
    -- `1 + 1 = 2`, so `Real.sqrt 2 ≥ 2`, hence `(Real.sqrt 2)^2 ≥ 4`.
    have h2 : (2 : ℝ) ≤ Real.sqrt 2 := by linarith
    have hsq : (Real.sqrt 2) ^ 2 = 2 := by
      rw [sq]
      exact Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have h4 : (4 : ℝ) ≤ (Real.sqrt 2) ^ 2 := by
      have := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2) h2
      have hsq' : Real.sqrt 2 * Real.sqrt 2 = (Real.sqrt 2) ^ 2 := by ring
      linarith [this, hsq']
    linarith

/-! ## §C — log-exp 形での正しい bridge `e^c ≥ e^a + e^b → c ≥ log (e^a + e^b)` -/

/-- **Square-to-linear bridge, log form (正しい形)**: `e^c ≥ e^a + e^b`
ならば `c ≥ log (e^a + e^b)`.

`Real.le_log_iff_exp_le` (`0 < y → (x ≤ log y ↔ exp x ≤ y)`) の反対方向。
`Real.exp x > 0` から `exp a + exp b > 0` が出る点が反例形との分かれ目。 -/
theorem square_to_linear_bridge_log {a b c : ℝ}
    (hc : Real.exp c ≥ Real.exp a + Real.exp b) :
    c ≥ Real.log (Real.exp a + Real.exp b) := by
  -- `0 < exp a + exp b`.
  have hpos : 0 < Real.exp a + Real.exp b :=
    add_pos (Real.exp_pos a) (Real.exp_pos b)
  -- `log (exp a + exp b) ≤ c ↔ exp a + exp b ≤ exp c`.
  rw [ge_iff_le, Real.log_le_iff_le_exp hpos]
  exact hc

/-- **Same bridge, ` log ≤ ` 露出形** (`log_le_iff_le_exp` を流す側): -/
theorem square_to_linear_bridge_log_le {a b c : ℝ}
    (hc : Real.exp a + Real.exp b ≤ Real.exp c) :
    Real.log (Real.exp a + Real.exp b) ≤ c :=
  square_to_linear_bridge_log hc

/-- **3-argument generalization**: `e^c ≥ e^a + e^b + e^d` ならば
`c ≥ log (e^a + e^b + e^d)`. -/
theorem square_to_linear_bridge_log_three {a b d c : ℝ}
    (hc : Real.exp c ≥ Real.exp a + Real.exp b + Real.exp d) :
    c ≥ Real.log (Real.exp a + Real.exp b + Real.exp d) := by
  have hpos : 0 < Real.exp a + Real.exp b + Real.exp d := by
    have h1 := Real.exp_pos a
    have h2 := Real.exp_pos b
    have h3 := Real.exp_pos d
    linarith
  rw [ge_iff_le, Real.log_le_iff_le_exp hpos]
  exact hc

/-- **Reverse direction**: `c ≥ log (e^a + e^b) → e^c ≥ e^a + e^b`. -/
theorem exp_ge_of_le_log_sum {a b c : ℝ}
    (hc : c ≥ Real.log (Real.exp a + Real.exp b)) :
    Real.exp c ≥ Real.exp a + Real.exp b := by
  have hpos : 0 < Real.exp a + Real.exp b :=
    add_pos (Real.exp_pos a) (Real.exp_pos b)
  -- `log (exp a + exp b) ≤ c ↔ exp a + exp b ≤ exp c`.
  have := (Real.log_le_iff_le_exp hpos).1 hc
  exact this

/-- **Equivalence form**: `c ≥ log (e^a + e^b) ↔ e^c ≥ e^a + e^b`. -/
theorem exp_ge_iff_le_log_sum {a b c : ℝ} :
    Real.exp c ≥ Real.exp a + Real.exp b
      ↔ c ≥ Real.log (Real.exp a + Real.exp b) :=
  ⟨square_to_linear_bridge_log, exp_ge_of_le_log_sum⟩

/-! ### §C-bis — `(2/n)` 係数版 (Brunn-Minkowski-entropy specialization) -/

/-- **`(2/n)` 係数版 bridge**: `exp ((2/n) hC) ≥ exp ((2/n) hA) + exp ((2/n) hB)`
ならば `(2/n) hC ≥ log (exp ((2/n) hA) + exp ((2/n) hB))`.

これは Brunn-Minkowski の主形 (`brunn_minkowski_entropy_inequality_exp_form`)
を log 側に **そのまま** 持ち上げる接続。 -/
theorem brunn_minkowski_log_form
    {n : ℕ} (hA hB hC : ℝ)
    (hbm : Real.exp ((2 / n) * hC) ≥
            Real.exp ((2 / n) * hA) + Real.exp ((2 / n) * hB)) :
    (2 / n) * hC ≥
      Real.log (Real.exp ((2 / n) * hA) + Real.exp ((2 / n) * hB)) :=
  square_to_linear_bridge_log hbm

/-- **Same with `(1/n)` 係数** (Cover-Thomas Cor 17.9.3 の sharp `vol^{1/n}` 形). -/
theorem brunn_minkowski_log_form_sharp
    {n : ℕ} (hA hB hC : ℝ)
    (hbm_sharp : Real.exp ((1 / n) * hC) ≥
                  Real.exp ((1 / n) * hA) + Real.exp ((1 / n) * hB)) :
    (1 / n) * hC ≥
      Real.log (Real.exp ((1 / n) * hA) + Real.exp ((1 / n) * hB)) :=
  square_to_linear_bridge_log hbm_sharp

/-! ## §D — `BrunnMinkowski.lean` L-BM2/L-BM3 接続 wrappers -/

/-- **L-BM2 + L-BM3 concavity wrapper for `brunn_minkowski_convex_body`**.

`brunn_minkowski_convex_body` (`BrunnMinkowski.lean` §D, L-BM1' sharp form
pass-through) は

    `exp ((1/n) log volAB) ≥ exp ((1/n) log volA) + exp ((1/n) log volB)`

を返す。本 wrapper はこの sharp 形を log 側に持ち上げ

    `(1/n) log volAB ≥ log (exp ((1/n) log volA) + exp ((1/n) log volB))`

を取り出す。`Real.exp_log` を通せば左辺は `log (volAB^{1/n})` に等価 -/
theorem brunn_minkowski_convex_body_log_form
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (A B : Set (Fin n → ℝ))
    (volA volB volAB : ℝ) (hvolA : 0 < volA) (hvolB : 0 < volB)
    (hvolAB : 0 < volAB)
    (hA_unif : IsUniformOnEntropyLogVolHypothesis n h (P.map X) volA)
    (hB_unif : IsUniformOnEntropyLogVolHypothesis n h (P.map Y) volB)
    (hAB_unif : IsUniformOnEntropyLogVolHypothesis n h
      (P.map (fun ω => X ω + Y ω)) volAB)
    (h_sum_meas : IsMinkowskiSumMeasurableHypothesis A B)
    (h_bm_sharp :
      Real.exp ((1 / n) * h (P.map (fun ω => X ω + Y ω)))
        ≥ Real.exp ((1 / n) * h (P.map X))
          + Real.exp ((1 / n) * h (P.map Y))) :
    (1 / n) * Real.log volAB
      ≥ Real.log
          (Real.exp ((1 / n) * Real.log volA)
            + Real.exp ((1 / n) * Real.log volB)) := by
  have h_main := brunn_minkowski_convex_body P h X Y hX hY hXY A B volA volB volAB
    hvolA hvolB hvolAB hA_unif hB_unif hAB_unif h_sum_meas h_bm_sharp
  exact square_to_linear_bridge_log h_main

/-- **`exp_log` form**: 同 wrapper を `volAB^{1/n} ≥ volA^{1/n} + volB^{1/n}`
**そのまま** の形で取り出す版。`Real.exp_log` を通すだけ。 -/
theorem brunn_minkowski_convex_body_exp_log_form
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (A B : Set (Fin n → ℝ))
    (volA volB volAB : ℝ) (hvolA : 0 < volA) (hvolB : 0 < volB)
    (hvolAB : 0 < volAB)
    (hA_unif : IsUniformOnEntropyLogVolHypothesis n h (P.map X) volA)
    (hB_unif : IsUniformOnEntropyLogVolHypothesis n h (P.map Y) volB)
    (hAB_unif : IsUniformOnEntropyLogVolHypothesis n h
      (P.map (fun ω => X ω + Y ω)) volAB)
    (h_sum_meas : IsMinkowskiSumMeasurableHypothesis A B)
    (h_bm_sharp :
      Real.exp ((1 / n) * h (P.map (fun ω => X ω + Y ω)))
        ≥ Real.exp ((1 / n) * h (P.map X))
          + Real.exp ((1 / n) * h (P.map Y))) :
    Real.exp ((1 / n) * Real.log volAB)
      ≥ Real.exp ((1 / n) * Real.log volA)
        + Real.exp ((1 / n) * Real.log volB) :=
  brunn_minkowski_convex_body P h X Y hX hY hXY A B volA volB volAB
    hvolA hvolB hvolAB hA_unif hB_unif hAB_unif h_sum_meas h_bm_sharp

/-! ### §D-bis — L-BM1 主形 → log 形 (concavity bridge through main entropy form) -/

/-- **Main entropy form, log-bridged**: `brunn_minkowski_entropy_inequality_exp_form`
を本 file の bridge で log 側に上げる版。

    `(2/n) h(X+Y) ≥ log (exp ((2/n) h(X)) + exp ((2/n) h(Y)))`. -/
theorem brunn_minkowski_entropy_log_form
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_bm : IsBrunnMinkowskiEntropyHypothesis n h X Y P) :
    (2 / n) * h (P.map (fun ω => X ω + Y ω))
      ≥ Real.log
          (Real.exp ((2 / n) * h (P.map X))
            + Real.exp ((2 / n) * h (P.map Y))) := by
  have h_exp := brunn_minkowski_entropy_inequality_exp_form P h X Y hX hY hXY h_bm
  exact square_to_linear_bridge_log h_exp

/-! ## §E — 補助 corollary 群 -/

/-- **Monotonicity for `Real.log` on `Real.exp` sums**: 1 つの引数の単調性。 -/
theorem log_exp_sum_mono_left {a a' b : ℝ} (hle : a ≤ a') :
    Real.log (Real.exp a + Real.exp b)
      ≤ Real.log (Real.exp a' + Real.exp b) := by
  apply Real.log_le_log
  · exact add_pos (Real.exp_pos a) (Real.exp_pos b)
  · gcongr

/-- **Right-side monotonicity** (mirror of `log_exp_sum_mono_left`). -/
theorem log_exp_sum_mono_right {a b b' : ℝ} (hle : b ≤ b') :
    Real.log (Real.exp a + Real.exp b)
      ≤ Real.log (Real.exp a + Real.exp b') := by
  apply Real.log_le_log
  · exact add_pos (Real.exp_pos a) (Real.exp_pos b)
  · gcongr

/-- **`exp ((1/n) log v) = v^{1/n}` shape (via `Real.rpow_def_of_pos`)**:
本補題は `Real.exp_log` + `Real.rpow` 経由の橋渡し、`brunn_minkowski_convex_body`
の Cor 17.9.3 化で利用。 -/
theorem exp_inv_n_log_eq_rpow {n : ℕ} (hn : 0 < (n : ℝ)) {v : ℝ} (hv : 0 < v) :
    Real.exp ((1 / n) * Real.log v) = v ^ ((1 : ℝ) / n) := by
  rw [Real.rpow_def_of_pos hv, mul_comm]

/-- **L-BM2 = log volume direct unfold** (alias clarifier). -/
theorem isUniformOnEntropyLogVolHypothesis_iff
    (n : ℕ) (h : Measure (Fin n → ℝ) → ℝ)
    (μ : Measure (Fin n → ℝ)) (vol : ℝ) :
    IsUniformOnEntropyLogVolHypothesis n h μ vol ↔ h μ = Real.log vol := by
  unfold IsUniformOnEntropyLogVolHypothesis
  rfl

/-- **L-BM3 = measurable set direct unfold** (alias clarifier). -/
theorem isMinkowskiSumMeasurableHypothesis_iff
    {n : ℕ} (A B : Set (Fin n → ℝ)) :
    IsMinkowskiSumMeasurableHypothesis A B ↔ MeasurableSet (A + B) := by
  unfold IsMinkowskiSumMeasurableHypothesis
  rfl

/-! ## §F — naive 反例の対偶 — log-exp は反例不在 -/

/-- **No counterexample for log form**: 任意の `a, b` について
`Real.exp c ≥ Real.exp a + Real.exp b` ならば
`c ≥ Real.log (Real.exp a + Real.exp b)` (常に成立, §B の反例の log 対偶)。 -/
theorem no_counterexample_log_form (a b c : ℝ)
    (hc : Real.exp c ≥ Real.exp a + Real.exp b) :
    c ≥ Real.log (Real.exp a + Real.exp b) :=
  square_to_linear_bridge_log hc

/-- **Triangle-like form for `log (exp + exp)`**: `max a b ≤ log (exp a + exp b)
≤ max a b + log 2`. 上界形のみ提供 (下界は単純な monotonicity)。 -/
theorem log_exp_add_exp_le_max_add_log_two (a b : ℝ) :
    Real.log (Real.exp a + Real.exp b) ≤ max a b + Real.log 2 := by
  have hpos : 0 < Real.exp a + Real.exp b :=
    add_pos (Real.exp_pos a) (Real.exp_pos b)
  have hle : Real.exp a + Real.exp b ≤ 2 * Real.exp (max a b) := by
    have ha : Real.exp a ≤ Real.exp (max a b) :=
      Real.exp_le_exp.mpr (le_max_left _ _)
    have hb : Real.exp b ≤ Real.exp (max a b) :=
      Real.exp_le_exp.mpr (le_max_right _ _)
    linarith
  have := Real.log_le_log hpos hle
  -- `log (2 * exp (max a b)) = log 2 + max a b`.
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hrhs : Real.log (2 * Real.exp (max a b))
      = Real.log 2 + max a b := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (Real.exp_ne_zero _),
        Real.log_exp]
  rw [hrhs] at this
  linarith

/-- **Lower bound**: `max a b ≤ log (exp a + exp b)`. -/
theorem max_le_log_exp_add_exp (a b : ℝ) :
    max a b ≤ Real.log (Real.exp a + Real.exp b) := by
  have hpos : 0 < Real.exp a + Real.exp b :=
    add_pos (Real.exp_pos a) (Real.exp_pos b)
  -- `exp (max a b) ≤ exp a + exp b`.
  have hle : Real.exp (max a b) ≤ Real.exp a + Real.exp b := by
    rcases le_total a b with hab | hab
    · have hmax : max a b = b := max_eq_right hab
      rw [hmax]
      have hpa := (Real.exp_pos a).le
      linarith
    · have hmax : max a b = a := max_eq_left hab
      rw [hmax]
      have hpb := (Real.exp_pos b).le
      linarith
  have := (Real.log_le_log_iff (Real.exp_pos _) hpos).mpr hle
  rwa [Real.log_exp] at this

/-! ## §G — log-sum-exp + concavity-of-log の系 (Cover-Thomas 17.6 系 utilities) -/

/-- **log-sum-exp shift invariance**: `log (exp (a + s) + exp (b + s)) = log (exp a + exp b) + s`.

LSE (log-sum-exp) の shift 平行移動性。Brunn-Minkowski の "scale" の引数化
で利用可能 (本 file の凸体系では未利用、Phase E 拡張で参照可)。 -/
theorem log_sum_exp_shift (a b s : ℝ) :
    Real.log (Real.exp (a + s) + Real.exp (b + s))
      = Real.log (Real.exp a + Real.exp b) + s := by
  have hpos1 : 0 < Real.exp a + Real.exp b :=
    add_pos (Real.exp_pos a) (Real.exp_pos b)
  -- `exp (a + s) + exp (b + s) = (exp a + exp b) * exp s`.
  have hsum : Real.exp (a + s) + Real.exp (b + s)
      = (Real.exp a + Real.exp b) * Real.exp s := by
    rw [Real.exp_add, Real.exp_add]; ring
  rw [hsum, Real.log_mul (ne_of_gt hpos1) (Real.exp_ne_zero _), Real.log_exp]

/-- **log-sum-exp scale invariance** (`(2/n)` の所まで一気に上げる版): 同じ
shift を `(2/n) ·` の中で取ったとき log 側に出る形。 -/
theorem log_sum_exp_scale_shift {n : ℕ} (a b s : ℝ) :
    Real.log (Real.exp ((2 / n) * a + s) + Real.exp ((2 / n) * b + s))
      = Real.log (Real.exp ((2 / n) * a) + Real.exp ((2 / n) * b)) + s :=
  log_sum_exp_shift _ _ s

/-- **log of sum of exp is positive when one summand > 1**: ノルム的下界. -/
theorem log_exp_add_exp_pos_of_pos (a b : ℝ) (h : 0 < a ∨ 0 < b) :
    0 < Real.log (Real.exp a + Real.exp b) := by
  -- `max a b ≤ log (exp a + exp b)` から、`max a b > 0` を示せばよい。
  have hmax_pos : 0 < max a b := by
    rcases h with h | h
    · exact lt_of_lt_of_le h (le_max_left a b)
    · exact lt_of_lt_of_le h (le_max_right a b)
  exact lt_of_lt_of_le hmax_pos (max_le_log_exp_add_exp a b)

/-- **log of sum of two `Real.exp` is upper-bounded by `max + log 2`**: alias. -/
theorem log_exp_add_exp_le (a b : ℝ) :
    Real.log (Real.exp a + Real.exp b) ≤ max a b + Real.log 2 :=
  log_exp_add_exp_le_max_add_log_two a b

/-- **Symmetric form**: `log (exp a + exp b) = log (exp b + exp a)`. -/
theorem log_exp_add_exp_comm (a b : ℝ) :
    Real.log (Real.exp a + Real.exp b)
      = Real.log (Real.exp b + Real.exp a) := by
  rw [add_comm]

/-! ## §H — concavity-of-log direct entropy form の brand-new wrappers -/

/-- **Concavity-of-log composition for Brunn-Minkowski main form**: 主形を
`(2/n)` 係数で log 側に持ち上げた状態に名前を付ける統合 wrapper。 -/
theorem brunn_minkowski_concavity_of_log_wrapper
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_bm : IsBrunnMinkowskiEntropyHypothesis n h X Y P) :
    (2 / n) * h (P.map (fun ω => X ω + Y ω))
      ≥ Real.log
          (Real.exp ((2 / n) * h (P.map X))
            + Real.exp ((2 / n) * h (P.map Y))) :=
  brunn_minkowski_entropy_log_form P h X Y hX hY hXY h_bm

/-- **Concavity wrapper, max lower bound form**: 主形を `max` で挟む形に
specialize したもの (`max_le_log_exp_add_exp` を経由)。 -/
theorem brunn_minkowski_concavity_max_lower_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_bm : IsBrunnMinkowskiEntropyHypothesis n h X Y P) :
    (2 / n) * h (P.map (fun ω => X ω + Y ω))
      ≥ max ((2 / n) * h (P.map X)) ((2 / n) * h (P.map Y)) := by
  have h_log := brunn_minkowski_entropy_log_form P h X Y hX hY hXY h_bm
  have h_max := max_le_log_exp_add_exp ((2 / n) * h (P.map X))
    ((2 / n) * h (P.map Y))
  linarith

/-- **Concavity wrapper, max + log 2 upper bound** (Brunn-Minkowski の右辺
を最大値 + log 2 で押さえる形 — `log_exp_add_exp_le_max_add_log_two` 経由). -/
theorem brunn_minkowski_concavity_max_log_two_upper_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_bm : IsBrunnMinkowskiEntropyHypothesis n h X Y P) :
    (2 / n) * h (P.map (fun ω => X ω + Y ω))
      ≥ Real.log
          (Real.exp ((2 / n) * h (P.map X))
            + Real.exp ((2 / n) * h (P.map Y)))
      ∧ Real.log
          (Real.exp ((2 / n) * h (P.map X))
            + Real.exp ((2 / n) * h (P.map Y)))
        ≤ max ((2 / n) * h (P.map X)) ((2 / n) * h (P.map Y))
          + Real.log 2 :=
  ⟨brunn_minkowski_entropy_log_form P h X Y hX hY hXY h_bm,
   log_exp_add_exp_le_max_add_log_two _ _⟩

/-! ## §I — naive sqrt 反例の rigorous な統計 (`c² = a² + b²` ですら `c < a + b` のケースの精緻化) -/

/-- **Strengthened counterexample**: `c² = a² + b²` (等号) でも `c < a + b` が
可能。具体的に `a = b = 1`, `c = √2`. -/
theorem square_to_linear_bridge_naive_strict_counterexample :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      c ^ 2 = a ^ 2 + b ^ 2 ∧ c < a + b := by
  refine ⟨1, 1, Real.sqrt 2, by norm_num, by norm_num, Real.sqrt_pos.mpr (by norm_num), ?_, ?_⟩
  · have h : Real.sqrt 2 ^ 2 = 2 := by
      rw [sq]
      exact Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
    rw [h]; norm_num
  · -- `√2 < 2`.
    have h_sqrt_lt : Real.sqrt 2 < 2 := by
      have : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
      have : Real.sqrt 2 < Real.sqrt 4 := by
        apply Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      rw [show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]] at this
      exact this
    linarith

/-- **square form is only a necessary condition (not sufficient)**: `c ≥ a + b`
ならば `c² ≥ a² + b² + 2ab ≥ a² + b²`. しかし逆は §B 反例で偽。 -/
theorem square_necessary_for_linear {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ≥ a + b) :
    c ^ 2 ≥ a ^ 2 + b ^ 2 := by
  -- `c ≥ a + b ≥ 0`, so `c² ≥ (a+b)² = a² + 2ab + b² ≥ a² + b²`.
  have hsum_nn : 0 ≤ a + b := by linarith
  have hc_nn : 0 ≤ c := le_trans hsum_nn hc
  have h1 : (a + b) ^ 2 ≤ c ^ 2 := by
    rw [sq, sq]
    exact mul_self_le_mul_self hsum_nn hc
  have h2 : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by
    have hab : 0 ≤ 2 * a * b := by positivity
    nlinarith
  linarith

/-! ## §J — Brunn-Minkowski entropy form と naive sqrt 反例の橋渡し -/

/-- **Why the naive form fails for Brunn-Minkowski**: もし `vol(A+B)^{1/n}
≥ vol(A)^{1/n} + vol(B)^{1/n}` を `vol(A+B)^{2/n} ≥ vol(A)^{2/n} + vol(B)^{2/n}`
から取り出そうとしても、§B / §I の反例により直接出ない。本補題はその
ことを **形式的に** 反証する。 -/
theorem brunn_minkowski_naive_two_over_n_does_not_imply_one_over_n :
    ∃ vA vB vAB : ℝ, 0 < vA ∧ 0 < vB ∧ 0 < vAB ∧
      vAB ^ (2 : ℕ) ≥ vA ^ (2 : ℕ) + vB ^ (2 : ℕ) ∧
      ¬ (vAB ≥ vA + vB) := by
  refine ⟨1, 1, Real.sqrt 2, by norm_num, by norm_num,
          Real.sqrt_pos.mpr (by norm_num), ?_, ?_⟩
  · -- `(√2)² = 2 ≥ 1 + 1`.
    have hsq : Real.sqrt 2 ^ 2 = 2 := by
      rw [sq]; exact Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
    show Real.sqrt 2 ^ (2 : ℕ) ≥ 1 ^ (2 : ℕ) + 1 ^ (2 : ℕ)
    rw [hsq]; norm_num
  · intro hc
    -- `√2 ≥ 1 + 1 = 2`, but `√2 < 2`.
    have h_sqrt_lt : Real.sqrt 2 < 2 := by
      have hsqrt4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
      have : Real.sqrt 2 < Real.sqrt 4 :=
        Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith [hsqrt4]
    linarith

/-- **Conversely, the log-exp form is robust**: §C の正しい形は反例不在
(`square_to_linear_bridge_log` で常に成立)。本補題はその統一表現。 -/
theorem log_exp_form_always_holds (a b c : ℝ) :
    Real.exp c ≥ Real.exp a + Real.exp b
      ↔ c ≥ Real.log (Real.exp a + Real.exp b) :=
  exp_ge_iff_le_log_sum

/-! ## §K — Brunn-Minkowski の "weak" form (1-arg corollaries) -/

/-- **Single-argument trivial form**: `h(X+Y) ≥ h(X) (= 0 in some normalization)`
の **(non-negative shift) Brunn-Minkowski corollary**:
`(2/n) h(X+Y) ≥ (2/n) h(X)` の trivially-true form when `h(Y) ≥ -∞`.

L-BM1 hypothesis から導出される 1-side corollary。 -/
theorem brunn_minkowski_entropy_ge_one_side
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_bm : IsBrunnMinkowskiEntropyHypothesis n h X Y P) :
    entropyPower_nDim n h (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower_nDim n h (P.map X) := by
  have h1 := brunn_minkowski_entropy_inequality P h X Y hX hY hXY h_bm
  have h2 : 0 ≤ entropyPower_nDim n h (P.map Y) :=
    entropyPower_nDim_nonneg n h _
  linarith

/-- **Symmetric one-side form**: 同 corollary, `Y` 側を取り出す版。 -/
theorem brunn_minkowski_entropy_ge_other_side
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_bm : IsBrunnMinkowskiEntropyHypothesis n h X Y P) :
    entropyPower_nDim n h (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower_nDim n h (P.map Y) := by
  have h1 := brunn_minkowski_entropy_inequality P h X Y hX hY hXY h_bm
  have h2 : 0 ≤ entropyPower_nDim n h (P.map X) :=
    entropyPower_nDim_nonneg n h _
  linarith

/-- **Brunn-Minkowski one-side weaker form via `max`**: 主形 →
`entropyPower_nDim n h (P.map (X+Y)) ≥ max (entropyPower_nDim n h (P.map X))
(entropyPower_nDim n h (P.map Y))`. -/
theorem brunn_minkowski_entropy_ge_max
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_bm : IsBrunnMinkowskiEntropyHypothesis n h X Y P) :
    entropyPower_nDim n h (P.map (fun ω => X ω + Y ω))
      ≥ max (entropyPower_nDim n h (P.map X))
            (entropyPower_nDim n h (P.map Y)) := by
  have hX' := brunn_minkowski_entropy_ge_one_side P h X Y hX hY hXY h_bm
  have hY' := brunn_minkowski_entropy_ge_other_side P h X Y hX hY hXY h_bm
  exact max_le hX' hY'

/-! ## §L — 凸体系 (`brunn_minkowski_convex_body`) と本 file の最終接続 -/

/-- **`rpow` 形での凸体系**: `volAB^{1/n} ≥ volA^{1/n} + volB^{1/n}`.
`exp_inv_n_log_eq_rpow` で `exp_log_form` を `rpow` に書き換える。 -/
theorem brunn_minkowski_convex_body_rpow_form
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < (n : ℝ))
    (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (A B : Set (Fin n → ℝ))
    (volA volB volAB : ℝ) (hvolA : 0 < volA) (hvolB : 0 < volB)
    (hvolAB : 0 < volAB)
    (hA_unif : IsUniformOnEntropyLogVolHypothesis n h (P.map X) volA)
    (hB_unif : IsUniformOnEntropyLogVolHypothesis n h (P.map Y) volB)
    (hAB_unif : IsUniformOnEntropyLogVolHypothesis n h
      (P.map (fun ω => X ω + Y ω)) volAB)
    (h_sum_meas : IsMinkowskiSumMeasurableHypothesis A B)
    (h_bm_sharp :
      Real.exp ((1 / n) * h (P.map (fun ω => X ω + Y ω)))
        ≥ Real.exp ((1 / n) * h (P.map X))
          + Real.exp ((1 / n) * h (P.map Y))) :
    volAB ^ ((1 : ℝ) / n) ≥ volA ^ ((1 : ℝ) / n) + volB ^ ((1 : ℝ) / n) := by
  have h_main := brunn_minkowski_convex_body P h X Y hX hY hXY A B volA volB volAB
    hvolA hvolB hvolAB hA_unif hB_unif hAB_unif h_sum_meas h_bm_sharp
  rw [exp_inv_n_log_eq_rpow hn hvolAB] at h_main
  rw [exp_inv_n_log_eq_rpow hn hvolA] at h_main
  rw [exp_inv_n_log_eq_rpow hn hvolB] at h_main
  exact h_main

/-- **`vol > 0` 直接形** (positivity tag): 凸体の volume が正であることを
hypothesis として要求するときの統合 specialization. -/
theorem brunn_minkowski_convex_body_rpow_pos
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < (n : ℝ))
    (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (A B : Set (Fin n → ℝ))
    (volA volB volAB : ℝ) (hvolA : 0 < volA) (hvolB : 0 < volB)
    (hvolAB : 0 < volAB)
    (hA_unif : IsUniformOnEntropyLogVolHypothesis n h (P.map X) volA)
    (hB_unif : IsUniformOnEntropyLogVolHypothesis n h (P.map Y) volB)
    (hAB_unif : IsUniformOnEntropyLogVolHypothesis n h
      (P.map (fun ω => X ω + Y ω)) volAB)
    (h_sum_meas : IsMinkowskiSumMeasurableHypothesis A B)
    (h_bm_sharp :
      Real.exp ((1 / n) * h (P.map (fun ω => X ω + Y ω)))
        ≥ Real.exp ((1 / n) * h (P.map X))
          + Real.exp ((1 / n) * h (P.map Y))) :
    0 < volAB ^ ((1 : ℝ) / n)
      ∧ volA ^ ((1 : ℝ) / n) + volB ^ ((1 : ℝ) / n)
        ≤ volAB ^ ((1 : ℝ) / n) := by
  refine ⟨Real.rpow_pos_of_pos hvolAB _, ?_⟩
  exact brunn_minkowski_convex_body_rpow_form P hn h X Y hX hY hXY A B volA volB volAB
    hvolA hvolB hvolAB hA_unif hB_unif hAB_unif h_sum_meas h_bm_sharp

end InformationTheory.Shannon.BrunnMinkowski
