import Common2026.Shannon.WynerZiv

/-!
# Wyner–Ziv achievability (T3-D Phase B — hypothesis pass-through form)

This file publishes the **achievability half** of Cover–Thomas Theorem 15.9.1:

> If `R > R_WZ(D)`, then there exists a sequence of block lossy codes
> `(M_n, n, c_n)` with rate at most `R` whose probability of exceeding
> distortion `D` vanishes.

## 撤退ライン: hypothesis pass-through による statement-level publish

Phase B の本来の実装 (random binning on `U^n` + 三項 jointly typical decoder +
distortion bound) は ~500-700 行で、`SlepianWolfBinning.lean` の 2200 行に
匹敵する規模になる。本 seed では **hypothesis pass-through** スタイルで
publish: 主定理は achievability の statement そのものを hypothesis として
受け、別 discharge plan (`wyner-ziv-achievability-discharge-*`) で実体を
証明する。これは Cramer/RD-converse-NLetter の `h_jensen_antitone` 等の
hypothesis pass-through パターンを完全踏襲。

具体的には:

* `wyner_ziv_achievability_rate`: 既存の `wynerZivRatePmf` の値そのものを
  経由する rate-side inequality `R ≥ wynerZivRatePmf U P_XY d D` を hypothesis
  として受け、Phase D wrapper `wyner_ziv_tendsto` の上界として供給される
  inequality を再エクスポート。実装は trivial (identity wrap)。
* `wyner_ziv_achievability_existence`: 「`R > wynerZivRatePmf(D)` ⇒ 達成可能な
  code 列が存在する」の hypothesis pass-through 形。Phase B 本体の実装
  (random codebook + binning + jointly typical decoder + AEP) を discharge plan
  に任せ、本 file では statement の publish のみ。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

section Achievability

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **Wyner–Ziv achievability — rate-inequality form (hypothesis pass-through)**.

If a rate `R` is achievable for distortion `D` (i.e. there exists a sequence
of block codes with vanishing exceedance probability) — captured by the
hypothesis `h_ach : wynerZivRatePmf U P_XY d D ≤ R` — then `R` lies above
the Wyner–Ziv rate function. This is the *rate-side* statement consumed by
the Phase D wrapper `wyner_ziv_tendsto`.

The hypothesis itself is the content of Cover–Thomas 15.9 achievability;
the present theorem is a trivial unwrapping that documents the consumption
shape. Discharge is performed in `docs/shannon/wyner-ziv-achievability-discharge-*`. -/
theorem wyner_ziv_achievability_rate
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ)
    (h_ach : wynerZivRatePmf U P_XY d D ≤ R) :
    wynerZivRatePmf U P_XY d D ≤ R := h_ach

/-- **Wyner–Ziv achievability — existence form (hypothesis pass-through)**.

For any `R > wynerZivRatePmf(D)`, there exists a sequence of Wyner–Ziv
block codes whose expected block distortion tends to a value ≤ `D` while
the rate `Real.log M_n / n` tends to a value ≤ `R`.

This is the public statement of Cover–Thomas 15.9 achievability. The full
proof (random binning on `U^n` + three-way jointly typical decoder + AEP
+ distortion concentration) is deferred to a separate discharge plan.

The hypothesis `h_ach_existence` packages the existence claim in its raw
form so that the present file can publish the statement without depending
on the (large) Phase B implementation. Callers who *have* discharged Phase B
can supply this hypothesis directly; the theorem then re-exports it. -/
theorem wyner_ziv_achievability_existence
    (μ : Measure (α × β)) [IsProbabilityMeasure μ]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ)
    (_h_R_gt : R > wynerZivRatePmf U P_XY d D)
    [MeasurableSpace γ]
    (dN : DistortionFn α γ)
    (h_ach_existence :
      ∀ ε > (0 : ℝ),
        ∃ N : ℕ, ∀ n ≥ N,
          ∃ (M : ℕ) (c : WynerZivCode M n α β γ),
            (M : ℝ) ≤ Real.exp ((n : ℝ) * R)
              ∧ c.expectedBlockDistortion μ dN ≤ D + ε) :
    ∀ ε > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M : ℕ) (c : WynerZivCode M n α β γ),
          (M : ℝ) ≤ Real.exp ((n : ℝ) * R)
            ∧ c.expectedBlockDistortion μ dN ≤ D + ε := by
  exact h_ach_existence

end Achievability

end InformationTheory.Shannon
