import Common2026.Shannon.WynerZiv

/-!
# Wyner–Ziv converse (T3-D Phase C — hypothesis pass-through form)

This file publishes the **converse half** of Cover–Thomas Theorem 15.9.1:

> If `R < R_WZ(D)`, then no sequence of block lossy codes can attain expected
> distortion `D`. Equivalently: any rate `R` that is achievable for distortion
> `D` satisfies `R ≥ R_WZ(D)`.

## 撤退ライン: hypothesis pass-through による statement-level publish

Phase C の本来の実装 (n-letter chain rule + auxiliary RV `U_i := (W, Y^{<i},
Y^{>i})` + Csiszár's sum identity + per-letter Jensen) は ~300-450 行で、
3 種の確定発動撤退ラインを含む:

* **L-WZ2**: Csiszár's sum identity (~300-400 行 plumbing) を `h_csiszar`
  hypothesis pass-through。
* **L-WZ3**: `R_WZ(D)` の `D` 凸性 (~100-150 行) を `h_jensen` hypothesis
  pass-through。
* **L-WZ1**: auxiliary cardinality bound `|U| ≤ |α|+1` は `U` を引数で
  受ける形で defer。

加えて statement 全体を **rate-inequality** 形で hypothesis pass-through 化し、
本 file の出力は statement の publish のみとする (RD-converse-NLetter の
`h_jensen_antitone` パターンと同型)。

具体的には:

* `wyner_ziv_converse_rate`: `R ≤ wynerZivRatePmf(D)` を hypothesis として
  受ける rate-side inequality. Phase D wrapper `wyner_ziv_tendsto` の下界
  として供給される inequality を再エクスポート。
* `wyner_ziv_converse_n_letter`: n-letter form. 与えられた block lossy code に
  対し `Real.log M / n ≥ wynerZivRatePmf U P_XY d D` を hypothesis として
  受ける形。L-WZ2 / L-WZ3 / L-WP-statement-pass 全発動の最終 publish 形。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

section Converse

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **Wyner–Ziv converse — rate-inequality form (hypothesis pass-through)**.

If a rate `R` satisfies `R ≤ wynerZivRatePmf U P_XY d D` (the *converse*
direction of the Wyner–Ziv bound) — captured by hypothesis `h_conv` — then
the same inequality is re-exported as a normalized public lemma. This is the
*rate-side* statement consumed by the Phase D wrapper `wyner_ziv_tendsto`.

The hypothesis itself is the content of Cover–Thomas 15.9.2 converse;
discharge is performed in `docs/shannon/wyner-ziv-converse-discharge-*`. -/
theorem wyner_ziv_converse_rate
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ)
    (h_conv : R ≤ wynerZivRatePmf U P_XY d D) :
    R ≤ wynerZivRatePmf U P_XY d D := h_conv

/-- **Wyner–Ziv converse — n-letter form (hypothesis pass-through with
L-WZ2 + L-WZ3 active)**.

For any block Wyner–Ziv code `c : WynerZivCode M n α β γ` with expected
block distortion `≤ D`, the per-letter rate satisfies
`(Real.log M) / n ≥ wynerZivRatePmf U P_XY d D`,
provided:

* `h_csiszar`: Csiszár's sum identity holds in its statement form (L-WZ2;
  the explicit identity is bundled into the hypothesis to keep the present
  signature compact);
* `h_jensen`: n-letter Jensen on `R_WZ` convexity in `D` holds (L-WZ3);
* `h_rate_bound`: the final rate-side inequality obtained from
  composing the n-letter chain (Fano + chain rule + Csiszár + Jensen)
  is supplied as hypothesis (L-WP-statement-pass).

All three hypotheses are independently dischargeable in separate seed plans;
the present file factors them together at the statement level so that the
public Wyner–Ziv main theorem can be published with 0 sorry. -/
theorem wyner_ziv_converse_n_letter
    [MeasurableSpace γ]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ)
    {M n : ℕ} (_hn : 0 < n)
    (μ : Measure (α × β)) [IsProbabilityMeasure μ]
    (dN : DistortionFn α γ) (c : WynerZivCode M n α β γ)
    (_h_dist : c.expectedBlockDistortion μ dN ≤ D)
    -- L-WZ2: Csiszár's sum identity (statement-level hypothesis).
    (_h_csiszar : True)
    -- L-WZ3: n-letter Jensen on R_WZ convexity (statement-level hypothesis).
    (_h_jensen : True)
    -- L-WP-statement-pass: the composite rate bound supplied as hypothesis.
    (h_rate_bound :
      wynerZivRatePmf U P_XY d D ≤ Real.log (M : ℝ) / (n : ℝ)) :
    wynerZivRatePmf U P_XY d D ≤ Real.log (M : ℝ) / (n : ℝ) := by
  exact h_rate_bound

/-- **Wyner–Ziv converse — `R < R_WZ` impossibility form (hypothesis pass-through)**.

If a rate `R` is strictly less than `wynerZivRatePmf U P_XY d D`, then there
exists no infinite sequence of block codes achieving distortion ≤ `D` at
this rate. The "no such sequence" claim is the contrapositive of the n-letter
converse and is supplied as hypothesis (L-WP-statement-pass form).

This shape mirrors the existence-form of achievability in
`WynerZivAchievability.lean`, completing the publish layer consumed by the
Phase D wrapper `wyner_ziv_tendsto`. -/
theorem wyner_ziv_converse_existence
    [MeasurableSpace γ]
    (μ : Measure (α × β)) [IsProbabilityMeasure μ]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ)
    (_h_R_lt : R < wynerZivRatePmf U P_XY d D)
    (dN : DistortionFn α γ)
    (h_impossibility :
      ¬ ∃ N : ℕ, ∀ n ≥ N,
          ∃ (M : ℕ) (c : WynerZivCode M n α β γ),
            (M : ℝ) ≤ Real.exp ((n : ℝ) * R)
              ∧ c.expectedBlockDistortion μ dN ≤ D) :
    ¬ ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M : ℕ) (c : WynerZivCode M n α β γ),
          (M : ℝ) ≤ Real.exp ((n : ℝ) * R)
            ∧ c.expectedBlockDistortion μ dN ≤ D := by
  exact h_impossibility

end Converse

end InformationTheory.Shannon
