import Common2026.Fano.Core
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Fano's inequality: measure-theoretic form (Phase 3 skeleton)

Cover & Thomas / Polyanskiy 級の Fano 不等式の測度論版を、Mathlib の
`condDistrib` (正則条件付き分布) を主役にして書く Phase 3 (ムーンショット) の起点。

設定:
* `X : Fintype`（離散・有限）— 通信路のアルファベット
* `Y : MeasurableSpace`（任意；`ℝ`、`ℝⁿ`、Polish 空間など連続分布 OK）
* `(Ω, μ)` 上の確率変数 `Xs : Ω → X` (送信源) と `Yo : Ω → Y` (観測)
* `decoder : Y → X` — 決定論的復号器（Phase 3 skeleton では deterministic に固定。
  randomized decoder への一般化は Phase 3.5 として後送り）

`condDistrib` の `StandardBorelSpace` 要求は出力側の型に課されるが、本定理での出力は
`X` であり、`Fintype + MeasurableSingletonClass + Countable` から
`DiscreteMeasurableSpace → StandardBorelSpace` が自動で derive される。したがって
`Y` の側に追加の制約は不要 (Phase 2 インベントリ調査時の予測との差分)。

Phase 1 (`Common2026/Fano/Core.lean`) の離散 Fano を `y : Y` ごとに pointwise 適用し、
`P_Yo = μ.map Yo` 上で Bochner Jensen により積分形に集約する戦略。詳細は
`docs/fano-mathlib-inventory.md`。

## 証明の構造図 (sorry-driven)

```
H(Xs | Yo)
  = ∫ y, [∑ x, negMulLog (Q_y {x})] dP_Yo                    -- def of condEntropy
  ≤ ∫ y, qaryEntropy |X| (Pe_y) dP_Yo                        -- pointwise_fano
  ≤ qaryEntropy |X| (∫ y, Pe_y dP_Yo)                        -- jensen_qaryEntropy
  = qaryEntropy |X| (errorProb μ Xs Yo decoder)              -- errorProb_eq_integral
  = h(Pe) + Pe · log(|X| - 1)                                -- qaryEntropy_eq_fanoBoundRHS
```

ここで `Q_y = (condDistrib Xs Yo μ y).real` (`y` 条件下の `Xs` の離散分布) と
`Pe_y = Q_y {x | x ≠ decoder y}` (`y` 条件下の誤り率)。
-/

namespace InformationTheory.MeasureFano

open MeasureTheory ProbabilityTheory

open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  [MeasurableSpace X] [MeasurableSingletonClass X]
variable {Y : Type*} [MeasurableSpace Y]

/-! ## Definitions -/

/-- 測度論版・条件付き Shannon エントロピー: `H(Xs | Yo) = ∫ H(Xs | Yo=y) dP_Yo(y)`。

各 `y : Y` で `condDistrib Xs Yo μ y : Measure X` は離散分布なので、
`negMulLog` の点和でその `y` における条件付きエントロピーを取り、`P_Yo = μ.map Yo` で積分する。 -/
def condEntropy (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) : ℝ :=
  ∫ y, ∑ x : X, Real.negMulLog ((condDistrib Xs Yo μ y).real {x}) ∂(μ.map Yo)

/-- 誤り確率: `Pe = P(Xs ≠ decoder ∘ Yo)`。 -/
def errorProb (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) (decoder : Y → X) : ℝ :=
  μ.real {ω | Xs ω ≠ decoder (Yo ω)}

/-- `y` 条件下の誤り率: `Pe(y) = (condDistrib Xs Yo μ y).real {x | x ≠ decoder y}`。 -/
def pointwiseErrorProb (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (decoder : Y → X) (y : Y) : ℝ :=
  (condDistrib Xs Yo μ y).real {x : X | x ≠ decoder y}

/-! ## Pointwise Fano (Phase 1 bridge)

各 `y : Y` で離散 Fano を呼ぶための glue lemma。`y` 依存性を取り除いた抽象形:
任意の確率測度 `Q : Measure X` と guess `xh : X` に対して、Shannon エントロピーが
`qaryEntropy |X| Pe` で押さえられる。

証明は Phase 1 の `FiniteJointPMF.fano_inequality` を、第二座標が `xh` の Dirac
になる `FiniteJointPMF X X` に適用するだけ。
-/

/-- `Q : Measure X` (確率測度) と guess `xh : X` から構成する Phase 1 用の `FiniteJointPMF X X`。
第二座標が `xh` での Dirac、すなわち `mass x x' = Q.real {x} · 𝟙[x' = xh]`。 -/
def diracPMF (Q : Measure X) [IsProbabilityMeasure Q] (xh : X) :
    FiniteJointPMF X X where
  mass := fun x x' => if x' = xh then Q.real {x} else 0
  mass_nonneg := fun x x' => by
    split_ifs
    · exact measureReal_nonneg
    · exact le_refl 0
  sum_mass := by
    -- ∑ x, ∑ x', (if x' = xh then Q.real {x} else 0) = ∑ x, Q.real {x} = 1
    have hInner : ∀ x : X,
        (∑ x' : X, if x' = xh then Q.real {x} else 0) = Q.real {x} := by
      intro x
      rw [Finset.sum_eq_single xh (fun b _ hb => by simp [hb]) (fun h => (h (Finset.mem_univ _)).elim)]
      simp
    rw [Finset.sum_congr rfl (fun x _ => hInner x)]
    -- ∑ x, Q.real {x} = Q.real Set.univ = 1
    rw [show (∑ x : X, Q.real {x}) = ∑ x ∈ (Finset.univ : Finset X), Q.real {x} from rfl,
        sum_measureReal_singleton]
    rw [show ((Finset.univ : Finset X) : Set X) = Set.univ from Finset.coe_univ]
    simp [measureReal_def, measure_univ]

/-! ### `diracPMF` の各種計算 -/

omit [DecidableEq X] [Nonempty X] in
/-- `Q : Measure X` 上の確率質量の総和は `1`。 -/
private lemma sum_real_singleton_eq_one (Q : Measure X) [IsProbabilityMeasure Q] :
    ∑ x : X, Q.real {x} = 1 := by
  rw [show (∑ x : X, Q.real {x}) = ∑ x ∈ (Finset.univ : Finset X), Q.real {x} from rfl,
      sum_measureReal_singleton]
  rw [show ((Finset.univ : Finset X) : Set X) = Set.univ from Finset.coe_univ]
  simp [measureReal_def, measure_univ]

omit [Nonempty X] in
/-- `diracPMF` の `mass` の展開形（projection 用）。 -/
private lemma diracPMF_mass (Q : Measure X) [IsProbabilityMeasure Q] (xh x x' : X) :
    (diracPMF Q xh).mass x x' = if x' = xh then Q.real {x} else 0 := rfl

omit [Nonempty X] in
/-- `diracPMF` の同時エントロピーは `Q` のエントロピーに一致。 -/
private lemma diracPMF_jointEntropy (Q : Measure X) [IsProbabilityMeasure Q] (xh : X) :
    (diracPMF Q xh).jointEntropy = ∑ x : X, Real.negMulLog (Q.real {x}) := by
  unfold FiniteJointPMF.jointEntropy
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single xh
    (fun b _ hb => by rw [diracPMF_mass, if_neg hb]; simp)
    (fun h => (h (Finset.mem_univ _)).elim)]
  rw [diracPMF_mass, if_pos rfl]

omit [Nonempty X] in
/-- `diracPMF` の `Y`-marginal は `xh` での Dirac。 -/
private lemma diracPMF_marginalY (Q : Measure X) [IsProbabilityMeasure Q] (xh x' : X) :
    (diracPMF Q xh).marginalY x' = if x' = xh then 1 else 0 := by
  unfold FiniteJointPMF.marginalY
  by_cases hx' : x' = xh
  · rw [hx', if_pos rfl]
    have : (∑ x : X, (diracPMF Q xh).mass x xh) = ∑ x : X, Q.real {x} :=
      Finset.sum_congr rfl (fun x _ => by rw [diracPMF_mass, if_pos rfl])
    rw [this, sum_real_singleton_eq_one]
  · rw [if_neg hx']
    apply Finset.sum_eq_zero
    intro x _
    rw [diracPMF_mass, if_neg hx']

omit [Nonempty X] in
/-- `diracPMF` の `Y`-エントロピーは `0`（Dirac の純粋性）。 -/
private lemma diracPMF_yEntropy (Q : Measure X) [IsProbabilityMeasure Q] (xh : X) :
    (diracPMF Q xh).yEntropy = 0 := by
  unfold FiniteJointPMF.yEntropy
  apply Finset.sum_eq_zero
  intro x' _
  rw [diracPMF_marginalY]
  by_cases hx' : x' = xh
  · rw [if_pos hx']; simp
  · rw [if_neg hx']; simp

omit [Nonempty X] in
/-- `diracPMF` の条件付きエントロピーは `Q` のエントロピーに一致。 -/
private lemma diracPMF_condEntropy (Q : Measure X) [IsProbabilityMeasure Q] (xh : X) :
    (diracPMF Q xh).condEntropy = ∑ x : X, Real.negMulLog (Q.real {x}) := by
  unfold FiniteJointPMF.condEntropy
  rw [diracPMF_jointEntropy, diracPMF_yEntropy, sub_zero]

omit [Nonempty X] in
/-- `diracPMF` の誤り確率は `Q` から見た `{xh}` の補集合の確率。 -/
private lemma diracPMF_errorProb (Q : Measure X) [IsProbabilityMeasure Q] (xh : X) :
    (diracPMF Q xh).errorProb = Q.real {x : X | x ≠ xh} := by
  unfold FiniteJointPMF.errorProb
  -- Inner sum collapses to the xh column, contributing iff x ≠ xh.
  have hInner : ∀ x : X,
      (∑ x' : X, if x = x' then 0 else (diracPMF Q xh).mass x x')
        = if x = xh then 0 else Q.real {x} := by
    intro x
    rw [Finset.sum_eq_single xh
      (fun b _ hb => by rw [diracPMF_mass, if_neg hb]; simp)
      (fun h => (h (Finset.mem_univ _)).elim)]
    rw [diracPMF_mass, if_pos rfl]
  rw [Finset.sum_congr rfl (fun x _ => hInner x)]
  -- Split the xh term out (it is 0), leaving ∑ x ∈ univ \ {xh}, Q.real {x}.
  rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ xh)
      (fun x => (if x = xh then (0:ℝ) else Q.real {x}))]
  rw [if_pos rfl, add_zero]
  have hDiff : ∀ x ∈ ((Finset.univ : Finset X) \ ({xh} : Finset X)),
      (if x = xh then (0:ℝ) else Q.real {x}) = Q.real {x} := by
    intro x hx
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hx
    rw [if_neg hx.2]
  rw [Finset.sum_congr rfl hDiff, sum_measureReal_singleton]
  -- Now: Q.real ↑(univ \ {xh}) = Q.real {x | x ≠ xh}.
  have hSet : (↑((Finset.univ : Finset X) \ ({xh} : Finset X)) : Set X)
              = {x : X | x ≠ xh} := by
    ext x
    simp
  rw [hSet]

omit [Nonempty X] in
/-- Pointwise Fano: `Q : Measure X`（確率測度）と guess `xh : X` に対し、
`∑ x, negMulLog (Q.real {x}) ≤ qaryEntropy |X| (Q.real {x | x ≠ xh})`。

`diracPMF Q xh : FiniteJointPMF X X`（第二座標が `xh` の Dirac）に対する
Phase 1 の `fano_core` がそのまま結論を与える。 -/
lemma pointwise_fano (Q : Measure X) [IsProbabilityMeasure Q] (xh : X)
    (hcard : 2 ≤ Fintype.card X) :
    (∑ x : X, Real.negMulLog (Q.real {x}))
      ≤ Real.qaryEntropy (Fintype.card X) (Q.real {x : X | x ≠ xh}) := by
  have hFano := (diracPMF Q xh).fano_core hcard
  rw [diracPMF_condEntropy, diracPMF_errorProb] at hFano
  exact hFano

/-! ## Main theorem: Fano's inequality, measure-theoretic form

各ステップを sub-sorry に分解。次セッション以降で順次埋めていく。
-/

/-- Fano's inequality, measure-theoretic form (deterministic decoder). -/
theorem fano_inequality_measure_theoretic
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (decoder : Y → X)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hdec : Measurable decoder)
    (hcard : 2 ≤ Fintype.card X) :
    condEntropy μ Xs Yo ≤
      Real.binEntropy (errorProb μ Xs Yo decoder)
        + errorProb μ Xs Yo decoder * Real.log ((Fintype.card X : ℝ) - 1) := by
  -- ## 共通 infrastructure (Step 1 / 2 / 3 で共有)
  haveI : IsProbabilityMeasure (μ.map Yo) :=
    Measure.isProbabilityMeasure_map hYo.aemeasurable
  -- "y 依存の誤り事象 {x | x ≠ decoder y}" を Y × X 上の固定可測集合へ持ち上げ、
  -- `Kernel.measurable_kernel_prodMk_left` を呼べる形に整える。
  have hMS : MeasurableSet {p : Y × X | p.2 ≠ decoder p.1} := by
    have hMS_eq : MeasurableSet {p : Y × X | p.2 = decoder p.1} :=
      measurableSet_eq_fun measurable_snd (hdec.comp measurable_fst)
    have hMS_swap : {p : Y × X | p.2 ≠ decoder p.1}
                    = ({p : Y × X | p.2 = decoder p.1})ᶜ := by
      ext p; simp [Set.mem_compl_iff]
    rw [hMS_swap]; exact hMS_eq.compl
  have hPreimage : ∀ y : Y, {x : X | x ≠ decoder y}
                   = Prod.mk y ⁻¹' {p : Y × X | p.2 ≠ decoder p.1} := by
    intro y; ext x; simp
  have hPeENN : Measurable
      (fun y => (condDistrib Xs Yo μ y) {x : X | x ≠ decoder y}) := by
    simp only [hPreimage]
    exact Kernel.measurable_kernel_prodMk_left hMS
  have hPeMeas : Measurable (pointwiseErrorProb μ Xs Yo decoder) := by
    change Measurable
      (fun y => ((condDistrib Xs Yo μ y) {x : X | x ≠ decoder y}).toReal)
    exact ENNReal.measurable_toReal.comp hPeENN
  have hPe_mem :
      ∀ᵐ y ∂(μ.map Yo), pointwiseErrorProb μ Xs Yo decoder y ∈ Set.Icc (0:ℝ) 1 :=
    Filter.Eventually.of_forall
      (fun _ => ⟨measureReal_nonneg, measureReal_le_one⟩)
  have hPe_integrable :
      Integrable (pointwiseErrorProb μ Xs Yo decoder) (μ.map Yo) :=
    Integrable.of_mem_Icc 0 1 hPeMeas.aemeasurable hPe_mem
  have hLog_nonneg : 0 ≤ Real.log ((Fintype.card X : ℝ) - 1) := by
    apply Real.log_nonneg
    have : (2 : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast hcard
    linarith
  -- ## Step 1: per-y で離散 Fano (`pointwise_fano`) を適用し、被積分関数を qaryEntropy(Pe(y)) に上から押さえる。
  have hPointwise : ∀ y : Y,
      (∑ x : X, Real.negMulLog ((condDistrib Xs Yo μ y).real {x}))
        ≤ Real.qaryEntropy (Fintype.card X)
            (pointwiseErrorProb μ Xs Yo decoder y) := fun y =>
    pointwise_fano (condDistrib Xs Yo μ y) (decoder y) hcard
  have step1 :
      condEntropy μ Xs Yo ≤
        ∫ y, Real.qaryEntropy (Fintype.card X)
              (pointwiseErrorProb μ Xs Yo decoder y) ∂(μ.map Yo) := by
    unfold condEntropy
    apply MeasureTheory.integral_mono_ae
    · -- Integrable LHS: ∑ x, negMulLog((cond y).real {x}) は probability measure 上有界可測。
      have hMeasOne : ∀ x : X,
          Measurable (fun y => (condDistrib Xs Yo μ y).real {x}) := fun x =>
        ENNReal.measurable_toReal.comp
          (Kernel.measurable_coe _ (measurableSet_singleton x))
      have hLHS : Measurable
          (fun y => ∑ x : X, Real.negMulLog ((condDistrib Xs Yo μ y).real {x})) :=
        Finset.measurable_sum _ (fun x _ =>
          Real.continuous_negMulLog.measurable.comp (hMeasOne x))
      apply Integrable.of_mem_Icc 0 (Fintype.card X) hLHS.aemeasurable
      refine Filter.Eventually.of_forall (fun y => ⟨?_, ?_⟩)
      · exact Finset.sum_nonneg (fun x _ =>
          Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one)
      · -- 各項は negMulLog t ≤ 1 - t ≤ 1 (for t ≥ 0)
        calc ∑ x : X, Real.negMulLog ((condDistrib Xs Yo μ y).real {x})
            ≤ ∑ _x : X, (1 : ℝ) := by
              refine Finset.sum_le_sum (fun x _ => ?_)
              have hUB := Real.negMulLog_le_one_sub_self
                (measureReal_nonneg (μ := condDistrib Xs Yo μ y)
                  (s := ({x} : Set X)))
              linarith [measureReal_nonneg (μ := condDistrib Xs Yo μ y)
                (s := ({x} : Set X))]
          _ = (Fintype.card X : ℝ) := by simp
    · -- Integrable RHS: y ↦ qaryEntropy |X| (Pe(y))。Pe ∈ [0,1] かつ qaryEntropy 連続。
      have hRHS : Measurable
          (fun y => Real.qaryEntropy (Fintype.card X)
                      (pointwiseErrorProb μ Xs Yo decoder y)) :=
        Real.qaryEntropy_continuous.measurable.comp hPeMeas
      apply Integrable.of_mem_Icc 0
        (Real.log ((Fintype.card X : ℝ) - 1) + Real.log 2) hRHS.aemeasurable
      refine Filter.Eventually.of_forall (fun y => ?_)
      have hPe_nn : 0 ≤ pointwiseErrorProb μ Xs Yo decoder y := measureReal_nonneg
      have hPe_le_one : pointwiseErrorProb μ Xs Yo decoder y ≤ 1 := measureReal_le_one
      refine ⟨Real.qaryEntropy_nonneg hPe_nn hPe_le_one, ?_⟩
      unfold Real.qaryEntropy
      rw [show Real.log ((Fintype.card X - 1 : ℤ) : ℝ)
            = Real.log ((Fintype.card X : ℝ) - 1) by push_cast; rfl]
      have h1 : pointwiseErrorProb μ Xs Yo decoder y * Real.log ((Fintype.card X : ℝ) - 1)
                ≤ Real.log ((Fintype.card X : ℝ) - 1) := by
        nlinarith [hPe_nn, hPe_le_one, hLog_nonneg]
      linarith [Real.binEntropy_le_log_two
        (p := pointwiseErrorProb μ Xs Yo decoder y)]
    · exact Filter.Eventually.of_forall hPointwise
  -- ## Step 2: Bochner Jensen で qaryEntropy(∫ Pe(y) dP_Yo) に上から押さえる。
  -- qaryEntropy = Pe·log(|X|-1) + binEntropy(Pe) と分解し、線形項は積分と可換、
  -- binEntropy 項は ConcaveOn.le_map_integral で凹性 Jensen を適用する。
  have step2 :
      (∫ y, Real.qaryEntropy (Fintype.card X)
              (pointwiseErrorProb μ Xs Yo decoder y) ∂(μ.map Yo))
        ≤ Real.qaryEntropy (Fintype.card X)
            (∫ y, pointwiseErrorProb μ Xs Yo decoder y ∂(μ.map Yo)) := by
    have hbinEntropy_integrable :
        Integrable (fun y => Real.binEntropy (pointwiseErrorProb μ Xs Yo decoder y))
          (μ.map Yo) := by
      apply Integrable.of_mem_Icc 0 (Real.log 2)
        (Real.binEntropy_continuous.measurable.comp hPeMeas).aemeasurable
      exact Filter.Eventually.of_forall (fun _ =>
        ⟨Real.binEntropy_nonneg measureReal_nonneg measureReal_le_one,
         Real.binEntropy_le_log_two⟩)
    have hqDecomp : ∀ p : ℝ,
        Real.qaryEntropy (Fintype.card X) p
          = p * Real.log ((Fintype.card X : ℝ) - 1) + Real.binEntropy p := by
      intro p
      unfold Real.qaryEntropy
      congr 2
      push_cast
      ring
    have hLHS_eq :
        (∫ y, Real.qaryEntropy (Fintype.card X)
                (pointwiseErrorProb μ Xs Yo decoder y) ∂(μ.map Yo))
          = (∫ y, pointwiseErrorProb μ Xs Yo decoder y ∂(μ.map Yo)) *
              Real.log ((Fintype.card X : ℝ) - 1) +
            (∫ y, Real.binEntropy (pointwiseErrorProb μ Xs Yo decoder y) ∂(μ.map Yo)) := by
      simp only [hqDecomp]
      rw [integral_add (hPe_integrable.mul_const _) hbinEntropy_integrable,
          integral_mul_const]
    have hJensen :
        (∫ y, Real.binEntropy (pointwiseErrorProb μ Xs Yo decoder y) ∂(μ.map Yo))
          ≤ Real.binEntropy
              (∫ y, pointwiseErrorProb μ Xs Yo decoder y ∂(μ.map Yo)) :=
      Real.strictConcave_binEntropy.concaveOn.le_map_integral
        Real.binEntropy_continuous.continuousOn isClosed_Icc
        hPe_mem hPe_integrable hbinEntropy_integrable
    rw [hLHS_eq, hqDecomp (∫ y, pointwiseErrorProb μ Xs Yo decoder y ∂(μ.map Yo))]
    linarith
  -- ## Step 3: disintegration で ∫ Pe(y) dP_Yo = errorProb μ Xs Yo decoder。
  -- 鎖: integral_toReal で実積分→lintegral に持ち上げ、
  -- compProd_apply (←) → compProd_map_condDistrib → map_apply で µ 上の事象に降ろす。
  have step3 :
      (∫ y, pointwiseErrorProb μ Xs Yo decoder y ∂(μ.map Yo))
        = errorProb μ Xs Yo decoder := by
    have hPe_lt_top : ∀ᵐ y ∂(μ.map Yo),
        (condDistrib Xs Yo μ y) {x : X | x ≠ decoder y} < ∞ :=
      Filter.Eventually.of_forall (fun _ => measure_lt_top _ _)
    unfold pointwiseErrorProb errorProb
    show (∫ y, ((condDistrib Xs Yo μ y) {x : X | x ≠ decoder y}).toReal ∂(μ.map Yo))
          = (μ {ω | Xs ω ≠ decoder (Yo ω)}).toReal
    rw [integral_toReal hPeENN.aemeasurable hPe_lt_top]
    congr 1
    simp_rw [hPreimage]
    rw [← Measure.compProd_apply hMS,
        compProd_map_condDistrib hXs.aemeasurable,
        Measure.map_apply (hYo.prodMk hXs) hMS]
    rfl
  -- Step 4: qaryEntropy = binEntropy + Pe * log(|X|-1) (Phase 0/1 の既知書き換え)
  have step4 :
      Real.qaryEntropy (Fintype.card X) (errorProb μ Xs Yo decoder)
        = Real.binEntropy (errorProb μ Xs Yo decoder)
          + errorProb μ Xs Yo decoder * Real.log ((Fintype.card X : ℝ) - 1) := by
    rw [InformationTheory.qaryEntropy_eq_fanoBoundRHS]
    unfold InformationTheory.fanoBoundRHS
    push_cast
    ring
  -- Chain: step1 → step2 → step3 → step4
  calc condEntropy μ Xs Yo
      ≤ ∫ y, Real.qaryEntropy (Fintype.card X)
              (pointwiseErrorProb μ Xs Yo decoder y) ∂(μ.map Yo) := step1
    _ ≤ Real.qaryEntropy (Fintype.card X)
          (∫ y, pointwiseErrorProb μ Xs Yo decoder y ∂(μ.map Yo)) := step2
    _ = Real.qaryEntropy (Fintype.card X) (errorProb μ Xs Yo decoder) := by rw [step3]
    _ = _ := step4

end

end InformationTheory.MeasureFano
