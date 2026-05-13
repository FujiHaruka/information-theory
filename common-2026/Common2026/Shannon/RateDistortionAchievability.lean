import Common2026.Shannon.RateDistortionConverse

/-!
# Rate-distortion achievability (E-3 Phase A skeleton MVP)

[`docs/shannon/rate-distortion-achievability-plan.md`](../../../docs/shannon/rate-distortion-achievability-plan.md)
の Phase A 最小 MVP。Cover-Thomas 10.5 achievability 半分のための **structure 部分**
のみを publish:

- `DistortionFn α β := α → β → NNReal`
- `blockDistortion d n x y : ℝ` — `(1/n) ∑ d(x_i, y_i)`
- `LossyCode M n α β` structure (encoder `(Fin n → α) → Fin M`, decoder `Fin M → (Fin n → β)`)
- `LossyCode.expectedBlockDistortion μ d c : ℝ` — i.i.d. source 上の `𝔼[d^n(X^n, decoder(encoder X^n))]`
- `blockDistortion_nonneg` + `expectedBlockDistortion_nonneg`

これは「E-3 完全形 (~1980 行) のための structure 定義」として publish され、
後続 Phase B-E (joint typical lossy encoder、random codebook、error analysis、主定理)
の statement 着地点を確定する。

## E-3' 後継として deferred になった items

- pmf 形 `expectedDistortion`, `mutualInfoPmf`, `RDConstraint`, `rateDistortionFunction`
  (pmf 直接形): 既存 Measure 形 (`RateDistortionConverse.rateDistortionFunction`) を
  流用 / pmf 形は B-E で必要になり次第 deferred
- `rateDistortionFunction_attained` (`IsCompact.exists_isMinOn`)、連続性、convexity、
  単調性 (E-4' で Measure 形は既出)
- `mutualInfoPmf_eq_mutualInfo_of_pmf` bridge
- Phase B: joint typical lossy encoder + decoder (`jointTypicalLossyEncoder`,
  `lossyCodeOfCodebook`)、`distortionTypicalSet`
- Phase C: random codebook + probabilistic method (`codebookMeasure` lossy mirror、
  `random_codebook_avg_distortion_le`、`exists_codebook_low_distortion`)
- Phase D: error event analysis ((10.85) bound: `M·(1-p_typ)^M → 0`)
- Phase E: 主定理 `rate_distortion_achievability`

## 設計判断

- **`DistortionFn` は `NNReal` 値**: textbook (Cover-Thomas 10.5) では `d : 𝒳 × 𝒳̂ → ℝ≥0`。
  既存 `RateDistortionConverse.lean` の `d : α → β → ℝ` 形 (非負性なし) とは異なるが、
  achievability では `d_max := sup d` の存在を使うので非負性が自然。両者は Phase B-E
  の bridge lemma で繋ぐ。
- **`expectedBlockDistortion` の戻り値 `ℝ`** (`∫` 形): `NNReal` を `ℝ` に押し出した
  ambient 積分。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ## Distortion function -/

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
  · -- 1/n ≥ 0
    by_cases hn : (n : ℝ) = 0
    · simp [hn]
    · exact div_nonneg zero_le_one (le_of_lt (lt_of_le_of_ne (Nat.cast_nonneg n) (Ne.symm hn)))
  · -- ∑ NNReal ≥ 0
    exact Finset.sum_nonneg (fun i _ => NNReal.coe_nonneg _)

/-! ## Block lossy code -/

/-- A **block lossy code** of length `n` with `M` codewords over source alphabet `α`
and reconstruction alphabet `β`: a deterministic encoder `(Fin n → α) → Fin M` (source
block to codeword index) and decoder `Fin M → (Fin n → β)` (codeword index to
reconstruction block).

`ChannelCoding.Code` (送信側) の **mirror**: encoder / decoder の方向が逆で、
decoder の codomain が `β^n` (reconstruction)。

We bundle no measurability fields: on finite alphabets all functions are
automatically measurable. -/
structure LossyCode (M n : ℕ) (α β : Type*)
    [MeasurableSpace α] [MeasurableSpace β] where
  encoder : (Fin n → α) → Fin M
  decoder : Fin M → (Fin n → β)

namespace LossyCode

variable {M n : ℕ}

/-- Expected block distortion of a lossy code under an i.i.d. source `P_X` on `α`.
The expectation is over `X^n ∼ P_X^n` (the `n`-fold product `Measure.pi`), and the
integrand is the block distortion of `X^n` against the reconstruction
`decoder (encoder X^n)`.

`(c.expectedBlockDistortion P_X d) = ∫ x : Fin n → α, blockDistortion d n x (c.decoder (c.encoder x)) ∂P_X^n`. -/
noncomputable def expectedBlockDistortion
    (c : LossyCode M n α β) (P_X : Measure α) (d : DistortionFn α β) : ℝ :=
  ∫ x : Fin n → α,
      blockDistortion d n x (c.decoder (c.encoder x))
    ∂(Measure.pi (fun _ : Fin n => P_X))

/-- Expected block distortion is non-negative: pointwise non-negativity of
`blockDistortion` lifts through the integral. -/
theorem expectedBlockDistortion_nonneg
    (c : LossyCode M n α β) (P_X : Measure α) (d : DistortionFn α β) :
    0 ≤ c.expectedBlockDistortion P_X d := by
  unfold expectedBlockDistortion
  exact integral_nonneg (fun x => blockDistortion_nonneg d n x _)

end LossyCode

end InformationTheory.Shannon
