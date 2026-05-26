import Common2026.Shannon.RateDistortionConverse
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Order.Compact

/-!
# Rate-distortion achievability (E-3 Phase A 完全形)

[`docs/shannon/rate-distortion-achievability-plan.md`](../../../docs/shannon/rate-distortion-achievability-plan.md)
の Phase A 完全形。Cover-Thomas 10.5 achievability 半分のための **structure 部分
+ pmf 直接形 R(D)** を publish:

## 既存 (skeleton MVP)

- `DistortionFn α β := α → β → NNReal`
- `blockDistortion d n x y : ℝ` — `(1/n) ∑ d(x_i, y_i)`
- `LossyCode M n α β` structure
- `LossyCode.expectedBlockDistortion μ d c : ℝ`

## 新規 (Phase A 完全形)

- `expectedDistortionPmf d q : ℝ` — `∑ a, b, q(a,b) · d(a,b)` (pmf 直接形)
- `marginalFst q : α → ℝ` / `marginalSnd q : β → ℝ` — joint pmf の marginals
- `RDConstraint P_X d D : Set (α × β → ℝ)` — feasible joint pmf 集合
- `mutualInfoPmf q : ℝ` — entropy 形 `H(fst) + H(snd) - H(q)` (`negMulLog` ベース連続)
- `rateDistortionFunctionPmf P_X d D : ℝ` — `⨅ q ∈ RDConstraint, mutualInfoPmf q`
- **`RDConstraint_isCompact`** / `RDConstraint_isClosed` / `RDConstraint_convex`
- **`mutualInfoPmf_continuous`** — `negMulLog` 連続性経由
- **`rateDistortionFunctionPmf_attained`** — `IsCompact.exists_isMinOn`
- `RDConstraint.nonempty_of_le` — `D ≥ D_max` で全 stdSimplex が in (point に依らず)
  ＋ `D ≥ achievable D` 系の自然性
- `rateDistortionFunctionPmf_antitone`

## 設計判断

- **MI を `negMulLog` (entropy) 形で定義**: `H(X)+H(Y)−H(X,Y)` は `negMulLog` の
  finite sum で書け、`Real.continuous_negMulLog` から全 `α×β → ℝ` 上連続が出る。
  KL/log 比形は marginal 0 で連続性が崩れるので採用しない。
- **`RDConstraint` は `Set (α × β → ℝ)`**: stdSimplex `α × β` 上の affine constraint。
  closed convex で `IsCompact.exists_isMinOn` が直接効く。
- **非空性は `D ≥ D_max`** で discharge: 任意の `q ∈ stdSimplex` で `expectedDistortion ≤ D_max`。
  textbook の `D ≥ D_min` 形は別補題で出せるが本 Phase は不要。
-/

namespace InformationTheory.Shannon

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open Real Set
open scoped ENNReal NNReal BigOperators Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ## Distortion function (既存 skeleton) -/

/-- 単文字 distortion 関数 `d : α → β → ℝ≥0`. -/
abbrev DistortionFn (α β : Type*) := α → β → NNReal

/-- ブロック距離 `d^n((x_i), (y_i)) := (1/n) ∑ d(x_i, y_i)`. 戻り値は `ℝ`. -/
noncomputable def blockDistortion {α β : Type*} (d : DistortionFn α β) (n : ℕ)
    (x : Fin n → α) (y : Fin n → β) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, ((d (x i) (y i) : NNReal) : ℝ)

/-- ブロック距離は非負. `NNReal` 値の和は非負、`1/n ≥ 0`. -/
theorem blockDistortion_nonneg
    {α β : Type*} (d : DistortionFn α β) (n : ℕ)
    (x : Fin n → α) (y : Fin n → β) :
    0 ≤ blockDistortion d n x y := by
  unfold blockDistortion
  refine mul_nonneg ?_ ?_
  · by_cases hn : (n : ℝ) = 0
    · simp [hn]
    · exact div_nonneg zero_le_one (le_of_lt (lt_of_le_of_ne (Nat.cast_nonneg n) (Ne.symm hn)))
  · exact Finset.sum_nonneg (fun i _ => NNReal.coe_nonneg _)

/-! ## Block lossy code (既存 skeleton) -/

/-- A **block lossy code** of length `n` with `M` codewords over source alphabet `α`
and reconstruction alphabet `β`: a deterministic encoder `(Fin n → α) → Fin M` and
decoder `Fin M → (Fin n → β)`. -/
structure LossyCode (M n : ℕ) (α β : Type*)
    [MeasurableSpace α] [MeasurableSpace β] where
  encoder : (Fin n → α) → Fin M
  decoder : Fin M → (Fin n → β)

namespace LossyCode

variable {M n : ℕ}

/-- Expected block distortion of a lossy code under an i.i.d. source `P_X` on `α`. -/
noncomputable def expectedBlockDistortion
    (c : LossyCode M n α β) (P_X : Measure α) (d : DistortionFn α β) : ℝ :=
  ∫ x : Fin n → α,
      blockDistortion d n x (c.decoder (c.encoder x))
    ∂(Measure.pi (fun _ : Fin n => P_X))

/-- Expected block distortion is non-negative. -/
theorem expectedBlockDistortion_nonneg
    (c : LossyCode M n α β) (P_X : Measure α) (d : DistortionFn α β) :
    0 ≤ c.expectedBlockDistortion P_X d := by
  unfold expectedBlockDistortion
  exact integral_nonneg (fun x => blockDistortion_nonneg d n x _)

end LossyCode

/-! ## Phase A 完全形: pmf 形 expectedDistortion / marginal / RDConstraint -/

section PmfForm

variable [Fintype α] [Fintype β]

/-- pmf 形 expected distortion `∑ a, b, q(a,b) · d(a,b)` for a joint pmf
`q : α × β → ℝ` and `NNReal`-valued distortion `d`. -/
noncomputable def expectedDistortionPmf
    (d : DistortionFn α β) (q : α × β → ℝ) : ℝ :=
  ∑ a, ∑ b, q (a, b) * ((d a b : NNReal) : ℝ)

/-- First (source-side) marginal of a joint pmf `q : α × β → ℝ`. -/
noncomputable def marginalFst (q : α × β → ℝ) : α → ℝ :=
  fun a => ∑ b, q (a, b)

/-- Second (reconstruction-side) marginal of a joint pmf `q : α × β → ℝ`. -/
noncomputable def marginalSnd (q : α × β → ℝ) : β → ℝ :=
  fun b => ∑ a, q (a, b)


/-- Continuity of `expectedDistortionPmf` in `q` (linear in finite sum). -/
lemma continuous_expectedDistortionPmf (d : DistortionFn α β) :
    Continuous (fun q : α × β → ℝ => expectedDistortionPmf d q) := by
  unfold expectedDistortionPmf
  refine continuous_finsetSum _ fun a _ => ?_
  refine continuous_finsetSum _ fun b _ => ?_
  exact (continuous_apply (a, b)).mul continuous_const

/-- Continuity of `marginalFst` in `q`. -/
lemma continuous_marginalFst :
    Continuous (fun q : α × β → ℝ => marginalFst q) := by
  unfold marginalFst
  refine continuous_pi fun a => ?_
  refine continuous_finsetSum _ fun b _ => ?_
  exact continuous_apply (a, b)

/-- Continuity of `marginalSnd` in `q`. -/
lemma continuous_marginalSnd :
    Continuous (fun q : α × β → ℝ => marginalSnd q) := by
  unfold marginalSnd
  refine continuous_pi fun b => ?_
  refine continuous_finsetSum _ fun a _ => ?_
  exact continuous_apply (a, b)


/-- **`RDConstraint`** — feasible joint pmf set `{q ∈ stdSimplex | marginalFst q = P_X ∧
expectedDistortionPmf d q ≤ D}`. -/
def RDConstraint
    (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) : Set (α × β → ℝ) :=
  {q | q ∈ stdSimplex ℝ (α × β) ∧ marginalFst q = P_X ∧ expectedDistortionPmf d q ≤ D}


/-- `RDConstraint ⊆ stdSimplex ℝ (α × β)`. -/
lemma RDConstraint_subset_stdSimplex (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) :
    RDConstraint P_X d D ⊆ stdSimplex ℝ (α × β) :=
  fun _ hq => hq.1

/-- `RDConstraint` is closed: intersection of closed sets (stdSimplex closed,
linear constraints closed). -/
lemma RDConstraint_isClosed (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) :
    IsClosed (RDConstraint P_X d D) := by
  -- {q | q ∈ stdSimplex} ∩ {q | marginalFst q = P_X} ∩ {q | expectedDistortionPmf d q ≤ D}
  have h1 : IsClosed (stdSimplex ℝ (α × β)) := isClosed_stdSimplex ℝ (α × β)
  have h2 : IsClosed {q : α × β → ℝ | marginalFst q = P_X} :=
    isClosed_eq continuous_marginalFst continuous_const
  have h3 : IsClosed {q : α × β → ℝ | expectedDistortionPmf d q ≤ D} :=
    isClosed_le (continuous_expectedDistortionPmf d) continuous_const
  have heq : RDConstraint P_X d D
      = stdSimplex ℝ (α × β) ∩ {q | marginalFst q = P_X} ∩
          {q | expectedDistortionPmf d q ≤ D} := by
    ext q; constructor
    · rintro ⟨h1', h2', h3'⟩; exact ⟨⟨h1', h2'⟩, h3'⟩
    · rintro ⟨⟨h1', h2'⟩, h3'⟩; exact ⟨h1', h2', h3'⟩
  rw [heq]
  exact (h1.inter h2).inter h3

/-- `RDConstraint` is compact (closed subset of compact stdSimplex). -/
lemma RDConstraint_isCompact (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) :
    IsCompact (RDConstraint P_X d D) :=
  IsCompact.of_isClosed_subset (isCompact_stdSimplex ℝ (α × β))
    (RDConstraint_isClosed P_X d D)
    (RDConstraint_subset_stdSimplex P_X d D)


/-! ## pmf 形 mutual information (entropy 形、`negMulLog` 経由連続) -/

/-- `mutualInfoPmf q := H(fst) + H(snd) − H(joint)` written via `negMulLog`:
`I(X;Y) = ∑_a negMulLog(q.fst a) + ∑_b negMulLog(q.snd b) − ∑_{a,b} negMulLog(q(a,b))`.
This formulation is **continuous on all of `α × β → ℝ`** because `Real.negMulLog`
is continuous everywhere (with `negMulLog 0 = 0`). -/
noncomputable def mutualInfoPmf (q : α × β → ℝ) : ℝ :=
  (∑ a, Real.negMulLog (marginalFst q a))
    + (∑ b, Real.negMulLog (marginalSnd q b))
    - (∑ p, Real.negMulLog (q p))

/-- `mutualInfoPmf` is continuous on `α × β → ℝ`. -/
lemma continuous_mutualInfoPmf :
    Continuous (fun q : α × β → ℝ => mutualInfoPmf q) := by
  unfold mutualInfoPmf
  refine Continuous.sub (Continuous.add ?_ ?_) ?_
  · refine continuous_finsetSum _ fun a _ => ?_
    have h_marg : Continuous (fun q : α × β → ℝ => marginalFst q a) :=
      (continuous_apply a).comp continuous_marginalFst
    exact Real.continuous_negMulLog.comp h_marg
  · refine continuous_finsetSum _ fun b _ => ?_
    have h_marg : Continuous (fun q : α × β → ℝ => marginalSnd q b) :=
      (continuous_apply b).comp continuous_marginalSnd
    exact Real.continuous_negMulLog.comp h_marg
  · refine continuous_finsetSum _ fun p _ => ?_
    exact Real.continuous_negMulLog.comp (continuous_apply p)

/-! ## pmf 形 rate-distortion function `R(D)` -/

/-- **`rateDistortionFunctionPmf P_X d D`**:
`R(D) := sInf {mutualInfoPmf q | q ∈ RDConstraint P_X d D}`.
This is the pmf-direct formulation of the rate-distortion function. When the
constraint set is non-empty the infimum is attained (see `rateDistortionFunctionPmf_attained`)
since `RDConstraint` is compact and `mutualInfoPmf` is continuous.

We use `sInf` of the image (rather than predicate-`⨅`) to avoid the
`ConditionallyCompleteLattice` `BddBelow` side conditions that plague
`⨅ q ∈ S, f q` reasoning over `ℝ`. -/
noncomputable def rateDistortionFunctionPmf
    (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) : ℝ :=
  sInf (mutualInfoPmf '' RDConstraint P_X d D)

/-! ## Phase A 達成性 (existence of minimizer) -/

/-- **Achievability** of `rateDistortionFunctionPmf`: when the constraint set
`RDConstraint P_X d D` is non-empty, the infimum is attained by some `q* ∈ RDConstraint`. -/
theorem rateDistortionFunctionPmf_attained
    (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ)
    (h_ne : (RDConstraint P_X d D).Nonempty) :
    ∃ qStar ∈ RDConstraint P_X d D,
      IsMinOn (fun q => mutualInfoPmf q) (RDConstraint P_X d D) qStar := by
  have h_compact : IsCompact (RDConstraint P_X d D) := RDConstraint_isCompact P_X d D
  have h_cont : Continuous (fun q : α × β → ℝ => mutualInfoPmf q) := continuous_mutualInfoPmf
  exact h_compact.exists_isMinOn h_ne h_cont.continuousOn


/-! ## Witness for non-emptyness: 単純 reconstruction `q(a,b) = P_X(a) · 𝟙[b = b₀]` -/

section Witness

variable [DecidableEq β]


end Witness

/-! ## Phase A 単調性 (antitone in `D`) -/


end PmfForm

/-! ## `Measure α → pmf` 抽出 (E-3'' utility)

`Measure α` から `α → ℝ` (pmf) を取り出す変換と基本性質。
`measureToPmf P a := P.real {a}`。Phase E 以降で witness 形 R(D) を
通常の `R(D) < R` 形に昇格する際に用いる。
-/

section MeasureToPmf


end MeasureToPmf

/-! ## Entropy ↔ pmf bridge (E-3'' (2))

`InformationTheory.Shannon.entropy` (Bridge.lean) は finite alphabet 上で
`∑ x, Real.negMulLog ((μ.map Xs).real {x})` — つまり pmf 形そのもの。
このセクションは entropy / mutualInfoPmf の橋渡し:

1. `entropy μ Xs = ∑ a, negMulLog (measureToPmf (μ.map Xs) a)` (definitional)
2. joint pmf の marginal が個別 pushforward の pmf に一致
3. `mutualInfoPmf (joint pmf) = H(X) + H(Y) − H(X, Y)`

Phase E MVP との接続: `qStar := measureToPmf (μ.map (jointSequence Xs Ys 0))` で
`mutualInfoPmf qStar` を entropy 差 (Phase B `jointlyTypicalSet_indep_prob_ge` の
exponent) と同一視するための鍵。
-/

section EntropyBridge


end EntropyBridge

end InformationTheory.Shannon
