import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.BlockwiseChannel
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# AWGN Walls — shared sorry 補題集約 file

Parent plan: `docs/shannon/awgn-m5-sorry-migration-plan.md` Phase 2.

10 declaration の Tier 3 (`@audit:retract-candidate(load-bearing-predicate)`、
bookkeeping) → Tier 2 (`sorry` + `@residual(<class>:<slug>)`、honest 撤退口) 移行に
おいて、analytic content の Mathlib 壁を「shared sorry 補題」(`docs/audit/audit-tags.md`
「共有 Mathlib 壁: shared sorry 補題パターン」) として 1 ヶ所に集約する file。

Phase 2 = shared sorry 補題の signature + body sorry 残置のみ (Phase 3 で consumer
側の predicate 削除 + signature 書換)。本 file 単独で type-check done。

## 3 shared sorry 補題

| 補題名 | wall name | 由来 predicate (Phase 3 で削除予定) |
|---|---|---|
| `continuousAepGaussian_holds` | `awgn-continuous-aep-gaussian` | `IsContinuousAEPGaussian` (AWGNAchievabilityDischarge:156) |
| `awgnRandomCodingBound_holds` | `awgn-random-coding-bound` | `IsAwgnRandomCodingBound` (AWGNAchievabilityDischarge:562) |
| `awgnPowerConstraintHonest_holds` | `awgn-power-constraint-honest` | `IsAwgnPowerConstraintHonest` (AWGNAchievabilityDischarge:763) |

## Signature 設計方針 (Mathlib-shape-driven)

- `continuousAepGaussian_holds` / `awgnPowerConstraintHonest_holds`: 旧 predicate body
  と verbatim 同型 (`gaussianCodebook` 不使用 / 2 段 `Measure.pi` の inline 形で書き、
  Phase 3 で consumer は `gaussianCodebook` ≡ 2 段 `Measure.pi` defeq で接続)。
- `awgnRandomCodingBound_holds`: 旧 predicate は `Code.mk` + `jointTypicalDecoder A
  codebook` で decoder を specialization していた。本 shared 補題では **任意の measurable
  decoder family** を取る抽象化形で publish し、Phase 3 で consumer が
  `jointTypicalDecoder` を inject する設計。これにより本 file は
  `InformationTheory.Shannon.AWGN` (`IsAwgnChannelMeasurable` / `awgnChannel`) +
  `Mathlib.Probability.Distributions.Gaussian.Real` のみ import で完結し、
  `AWGNAchievabilityDischarge` への循環を避ける (`jointTypicalDecoder` は
  AWGNAchievabilityDischarge.lean:201 に存在 — 本 file が import するのは Phase 3 で
  consumer 側を書き換える時点では逆方向 import が成立する)。

## Import policy

`AWGN.lean` 経由で `ChannelCoding.Code` / `errorEvent` などへの transitive access あり
(本 file 内で `Code.mk` を直接書かないため、明示 import 不要)。
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Wall 1 — `awgn-continuous-aep-gaussian`

(Note: the former Wall 0 `contChannelMIDecomp_holds` — the continuous-channel MI
chain rule `I(X;Y) = h(Y) − h(Y|X)` — was **closed 2026-05-28**: it is now assembled
genuinely from local helpers in
`InformationTheory.Draft.Shannon.ContChannelMIDecomp.mutualInfoOfChannel_toReal_eq_diffEntropy_sub`
(0 sorry), so no shared wall is needed. This file's active wall count is now **4**:
Wall 6 `awgn-converse-markov-regularity` was **genuine-closed 2026-06-04**
(`awgnConverseMarkov_holds` is sorryAx-free, see its docstring); Wall 4
`awgn-per-letter-integrability` was **genuine-closed 2026-06-10**
(`awgnPerLetterIntegrability_holds` is sorryAx-free — the wall verdict over-claimed:
the per-letter law is a finite 1-D Gaussian mixture, no SMB needed). Remaining active
walls: 1 `awgn-continuous-aep-gaussian`, 2 `awgn-random-coding-bound`, 3
`awgn-power-constraint-honest`, 5 `awgn-continuous-mi-chain-rule`.) -/

/-- **Continuous AEP for n-dim Gaussian** (Phase B-0 wall, 旧 `IsContinuousAEPGaussian`).

Given `P : ℝ`, `N : ℝ≥0` and tolerance `ε > 0`, there exists a threshold `N₀` such that
for every `n ≥ N₀`, a measurable typical set `A ⊆ (Fin n → ℝ) × (Fin n → ℝ)` exists
satisfying the 3 AEP sub-bounds:

* **(i) joint codebook+noise mass `≥ 1 - ε`**: under the joint law of `(X, Y)` with
  `X ∼ N(0,P)` i.i.d. and `Y = X + Z`, `Z ∼ N(0,N)` i.i.d.;
* **(ii) typical-set volume bound** (via `klDiv` form, judgement #3 in inventory);
* **(iii) independent-pair upper bound** (`X'` independent of `Y`).

Mathlib gap: continuous SMB (Shannon–McMillan–Breiman) + n-dim `differentialEntropy`
absent in Mathlib. Wall promote: `audit-tags.md` Wall name register entry
`awgn-continuous-aep-gaussian` (specialization of generic `continuous-aep` with the
concrete 3-sub-bound `klDiv` shape required by AWGN achievability core).

@residual(wall:awgn-continuous-aep-gaussian) -/
theorem continuousAepGaussian_holds (P : ℝ) (N : ℝ≥0) :
    ∀ ⦃ε : ℝ⦄, 0 < ε → ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n →
      ∃ A : Set ((Fin n → ℝ) × (Fin n → ℝ)),
        MeasurableSet A
        ∧ (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
              (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
                  (p.1, fun i => p.1 i + p.2 i))) A
            ≥ ENNReal.ofReal (1 - ε)
        ∧ volume A
            ≤ ENNReal.ofReal (Real.exp ((n : ℝ) *
                ((klDiv
                    (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N)))
                    (volume : Measure (Fin n → ℝ))).toReal + ε)))
        ∧ ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
              (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N)))) A
            ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) *
                ((klDiv
                    (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                        (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
                      (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
                          (p.1, fun i => p.1 i + p.2 i)))
                    ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                      (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N))))).toReal
                  - 3 * ε))) := by
  sorry

/-! ## Wall 2 — `awgn-random-coding-bound` -/

/-- **Random-coding union bound** (Phase C-3 wall, 旧 `IsAwgnRandomCodingBound`).

Average-over-codebook integral bound on the per-message error probability when the
codebook is drawn from the 2-stage Gaussian product law and any measurable decoder
family is used. Abstracted from the 旧 predicate (which fixed
`decoder := jointTypicalDecoder A codebook`) by exposing `decoder` as an explicit
parameter, so the body covers the analytic content (Fubini + IndepFun + AEP-chain)
without committing to the specific `jointTypicalDecoder` shape — consumers in
Phase 3 specialize via the standard joint typical decoder.

Mathlib gap: Fubini + IndepFun + AEP-chain over `gaussianCodebook` mass; the union
bound itself is straightforward, but the combination with continuous AEP on
non-product joint laws is the genuine Mathlib absence.

Signature note: `gaussianCodebook M n P.toNNReal` is `Measure.pi (fun _ : Fin M =>
Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal))` definitionally
(`AWGNAchievabilityDischarge.lean:62`); the body is written in the 2-stage
`Measure.pi` form to avoid importing `AWGNAchievabilityDischarge`.

@residual(wall:awgn-random-coding-bound) -/
theorem awgnRandomCodingBound_holds (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) :
    ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃R : ℝ⦄, 0 < R → R < (1/2) * Real.log (1 + P / (N : ℝ)) →
      ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n → ∀ ⦃M : ℕ⦄ (hM_pos : 0 < M),
        M ≤ Nat.ceil (Real.exp ((n : ℝ) * R)) →
        ∀ ⦃A : Set ((Fin n → ℝ) × (Fin n → ℝ))⦄, MeasurableSet A →
          ∀ ⦃decoder : (Fin M → Fin n → ℝ) → (Fin n → ℝ) → Fin M⦄,
            Measurable (Function.uncurry decoder) →
            haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM_pos⟩
            ∀ m : Fin M,
              ∫⁻ codebook : Fin M → Fin n → ℝ,
                ((Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
                  {y : Fin n → ℝ | decoder codebook y ≠ m})
              ∂(Measure.pi
                  (fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)))
                ≤ ENNReal.ofReal (2 * ε) := by
  sorry

/-! ## Wall 3 — `awgn-power-constraint-honest` -/

/-- **Power-constraint honest mass bound** (Phase D wall, 旧 `IsAwgnPowerConstraintHonest`).

Codebook is generated at variance `P_cb`; the per-message power constraint target is
`n · P_target`. Under `P_cb < P_target`, SLLN gives `(1/n) ∑ᵢ X_i² → P_cb < P_target`
a.s. and the mass of `{c | ∀ m, ∑ᵢ (c m i)² ≤ n · P_target}` tends to 1.

Mathlib gap: chi-square SLLN on `gaussianCodebook` mass concentration. `strong_law_ae`
exists but the chi-square-on-`gaussianCodebook` mass-concentration composite (uniform
across `Fin M` codewords by independence) is the analytic gap.

Signature note: `gaussianCodebook M n P_cb.toNNReal` is unfolded into the 2-stage
`Measure.pi` form to avoid importing `AWGNAchievabilityDischarge` (defeq via
`AWGNAchievabilityDischarge.lean:62`).

`P_cb < P_target` slack is required (the `P_cb = P_target` case is unsatisfiable —
the v1 false statement; see `AWGNAchievabilityDischarge.lean` Retraction log).

@residual(wall:awgn-power-constraint-honest) -/
theorem awgnPowerConstraintHonest_holds
    (P_cb P_target : ℝ) (_hP_slack : P_cb < P_target) (N : ℝ≥0) :
    ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃R : ℝ⦄, 0 < R →
        R < (1/2) * Real.log (1 + P_target / (N : ℝ)) →
      ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n → ∀ ⦃M : ℕ⦄ (_hM_pos : 0 < M),
        M ≤ Nat.ceil (Real.exp ((n : ℝ) * R)) →
        (Measure.pi
            (fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 P_cb.toNNReal)))
            {c : Fin M → Fin n → ℝ | ∀ m, (∑ i, (c m i)^2) ≤ (n : ℝ) * P_target}
          ≥ ENNReal.ofReal (1 - ε) := by
  sorry

/-! ## Converse-side walls — `awgn-per-letter-integrability` / `awgn-continuous-mi-chain-rule`
/ `awgn-converse-markov-regularity`

Phase 3-α (`docs/shannon/awgn-m5-sorry-migration-plan.md`) で `AWGNConverseDischarge.lean`
の 3 sub-bound predicate (`PerLetterIntegrabilityForConverse` /
`ContinuousMIChainRuleForConverse` / `MarkovChainForConverse`) + bundle
`IsAwgnConverseFeasible` を削除し、各 sub-bound の analytic content を shared sorry
補題に格上げする。

**Import cycle 回避**: 旧 predicate body は `awgnConverseJoint` / `perLetterYLaw` /
`perLetterMI` / `jointMIXnYn` (いずれも `AWGNConverseDischarge.lean` 定義) を参照する。
これら named def を本 file から直接参照すると `AwgnWalls → AWGNConverseDischarge →
AwgnWalls` の import cycle になるため、`awgnConverseJoint` の body を本 file の
private mirror def `converseJointInline` に inline する (両 def は同一 RHS なので
**defeq**: consumer 側 `unfold awgnConverseJoint perLetterYLaw …` で goal が本 file の
inline 形に一致し、shared 補題が適用可能)。

**Markov の Route 判定 (Phase 3α-1, 更新)**: `MarkovChainForConverse` の genuine 化
(`IsMarkovChain (awgnConverseJoint) Prod.fst (encoder∘fst) Prod.snd`) は当初 Route B
(shared sorry, wall `awgn-converse-markov-regularity`) で撤退したが、独立壁再評価で「真の
Mathlib 不在ではなく deterministic-encoder factorization plumbing 過大評価」と判定され、
`awgnConverseMarkov_holds` で **genuine 化完了** (mixture-of-diracs 上の message-space
marginal `μ = (μ.map fst) ⊗ₘ (W.comap encoder)` を起点に `condDistrib` 同定、precedent
`BlockwiseChannel.isMarkovChain_per_letter_input`)。

**Wall 4 `awgn-per-letter-integrability` の closure (2026-06-10)**: 当初の wall verdict
(continuous SMB / n-dim `differentialEntropy`) は **過大評価** だった。実際の goal は
`volume` 上の **1 次元** integrability で、per-letter 出力法 `Y_i` は有限 Gaussian 混合
`(1/M) ∑ₘ 𝒩(encoder m i, N)` (`perLetterLaw_eq_mixture`)、その `rnDeriv volume` は混合
密度 `perLetterMixtureDensity` (`perLetterLaw_withDensity`)。`negMulLog` of density を
Gaussian moment integrand で dominate して genuine 化 (`awgnPerLetterIntegrability_holds`
は sorryAx-free)。連続入力版 `outputDistribution_logDensity_integrable` を mirror した形
だが、有限混合ゆえ Chebyshev 集中不要 (lower bound は単一成分で出る)。cause:single-route
(壁判定が 1 ルート = SMB のみ想定で、1-D 混合密度の直接 domination ルートを見落とした)。

よって converse-side の active wall は **3 件** (Wall 1/2/3 = achievability 系、Wall 5 =
MI chain rule)、Markov と per-letter integrability は genuine。 -/

/-- Mirror of `awgnConverseJoint` (`AWGNConverseDischarge.lean:65`) body, inlined here
to break the would-be import cycle. Defeq to `awgnConverseJoint h_meas c` (both `def`s
share the same RHS, so consumer-side `unfold awgnConverseJoint` reduces to this form). -/
private noncomputable def converseJointInline
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) :
    Measure (Fin M × (Fin n → ℝ)) :=
  ((Fintype.card (Fin M) : ℝ≥0∞)⁻¹) •
    ∑ m : Fin M,
      (Measure.dirac m).prod
        (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i)))

/-- `converseJointInline` is a probability measure for `M ≥ 1` (mixture with weights
`1/M` summing to 1). Mirror of `awgnConverseJoint.instIsProbabilityMeasure`
(`AWGNConverseDischarge.lean:77`); needed so `IsMarkovChain`'s `[IsFiniteMeasure μ]`
prerequisite resolves on the inlined joint. -/
private instance converseJointInline.instIsProbabilityMeasure
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    IsProbabilityMeasure (converseJointInline h_meas c) := by
  refine ⟨?_⟩
  unfold converseJointInline
  rw [Measure.smul_apply, Measure.finsetSum_apply _ _ Set.univ]
  have h_summand : ∀ m : Fin M,
      ((Measure.dirac m).prod
          (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))))
            Set.univ = 1 := fun _ => measure_univ
  simp only [h_summand, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  have hM_ne_zero : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hM_ne_top : (M : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top M
  exact ENNReal.inv_mul_cancel hM_ne_zero hM_ne_top

/-! ### Wall 4 — `awgn-per-letter-integrability`

**Genuine closure (2026-06-10).** The wall verdict (continuous SMB / n-dim
`differentialEntropy`) over-claimed: the actual goal is a **1-dimensional** integrability
against `volume` on `ℝ`. The per-letter output law `Y_i` is a **finite mixture of shifted
1-D Gaussians** `(1/M) ∑ₘ 𝒩(encoder m i, N)`, so its `rnDeriv volume` is the finite
Gaussian-mixture density `(1/M) ∑ₘ gaussianPDF (encoder m i) N`. `negMulLog` of that density
is dominated by a Gaussian moment integrand — pure 1-D measure-theoretic domination, no SMB.
The proof mirrors the continuous-input analogue
`AwgnCapacityConverseMaxent.outputDistribution_logDensity_integrable` (not importable here —
import cycle), but is simpler: the finite mixture needs no Chebyshev concentration (the
lower bound comes from a single component). -/

/-- The finite per-letter Gaussian-mixture density at coordinate `i`:
`(1/M) ∑ₘ gaussianPDF (encoder m i) N y` (`ℝ≥0∞`-valued). For `M ≥ 1` and `N ≠ 0` this is
the `rnDeriv volume` of the per-letter output law `(converseJointInline h_meas c).map (·.2 i)`. -/
private noncomputable def perLetterMixtureDensity
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (y : ℝ) : ℝ≥0∞ :=
  ((M : ℝ≥0∞))⁻¹ * ∑ m : Fin M, gaussianPDF (c.encoder m i) N y

private lemma perLetterMixtureDensity_measurable
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) :
    Measurable (perLetterMixtureDensity N c i) := by
  unfold perLetterMixtureDensity
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_sum _ (fun m _ => measurable_gaussianPDF (c.encoder m i) N)

/-- The per-letter output law equals the explicit finite Gaussian mixture
`(1/M) • ∑ₘ 𝒩(encoder m i, N)` (the decisive atom: pushforward of the inlined joint
mixture-of-diracs⊗pi through `ω ↦ ω.2 i`, marginalizing the `pi` to its `i`-th factor). -/
private lemma perLetterLaw_eq_mixture
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) :
    (converseJointInline h_meas c).map (fun ω => ω.2 i)
      = ((M : ℝ≥0∞))⁻¹ • ∑ m : Fin M, gaussianReal (c.encoder m i) N := by
  classical
  have hf_meas : Measurable (fun ω : Fin M × (Fin n → ℝ) => ω.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  unfold converseJointInline
  rw [Measure.map_smul, Measure.map_finset_sum hf_meas.aemeasurable]
  simp only [Fintype.card_fin]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  -- `((dirac m).prod (pi μ_m)).map (·.2 i) = gaussianReal (encoder m i) N`
  -- via `map ((eval i) ∘ snd) = (map snd).map (eval i)`.
  have h_comp : (fun ω : Fin M × (Fin n → ℝ) => ω.2 i)
      = (Function.eval i) ∘ (Prod.snd : Fin M × (Fin n → ℝ) → (Fin n → ℝ)) := rfl
  rw [h_comp, ← Measure.map_map (measurable_pi_apply i) measurable_snd,
    Measure.map_snd_prod, measure_univ, one_smul,
    Measure.pi_map_eval]
  -- `∏ j ∈ erase i, (awgnChannel N (encoder m j)) univ = 1` (each fibre is a prob measure)
  have h_prod_one : (∏ j ∈ Finset.univ.erase i,
      (awgnChannel N h_meas (c.encoder m j)) Set.univ) = 1 := by
    refine Finset.prod_eq_one (fun j _ => ?_)
    rw [awgnChannel_apply]; exact measure_univ
  rw [h_prod_one, one_smul, awgnChannel_apply]

/-- For `M ≥ 1` and `N ≠ 0`, the per-letter output law is
`volume.withDensity (perLetterMixtureDensity c i)`. -/
private lemma perLetterLaw_withDensity
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (hM : 0 < M) (hN : N ≠ 0) :
    (converseJointInline h_meas c).map (fun ω => ω.2 i)
      = volume.withDensity (perLetterMixtureDensity N c i) := by
  classical
  rw [perLetterLaw_eq_mixture h_meas c i]
  -- Each component: `gaussianReal μ N = volume.withDensity (gaussianPDF μ N)`.
  have h_comp : ∀ m : Fin M,
      gaussianReal (c.encoder m i) N
        = volume.withDensity (gaussianPDF (c.encoder m i) N) :=
    fun m => gaussianReal_of_var_ne_zero (c.encoder m i) hN
  -- Sum of withDensity = withDensity of sum (finset induction).
  have h_sum : ∀ s : Finset (Fin M),
      (∑ m ∈ s, gaussianReal (c.encoder m i) N)
        = volume.withDensity (∑ m ∈ s, gaussianPDF (c.encoder m i) N) := by
    intro s
    induction s using Finset.induction with
    | empty => simp [withDensity_zero]
    | insert m s hms ih =>
        rw [Finset.sum_insert hms, Finset.sum_insert hms, ih, h_comp m,
          withDensity_add_left (measurable_gaussianPDF _ _)]
  rw [h_sum Finset.univ]
  -- `M⁻¹ • volume.withDensity g = volume.withDensity (M⁻¹ • g)`.
  have hM_ne_top : (M : ℝ≥0∞)⁻¹ ≠ ∞ := by
    simp
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hM)
  rw [← withDensity_smul' _ _ hM_ne_top]
  -- `M⁻¹ • (∑ₘ gaussianPDF ...) = perLetterMixtureDensity N c i` (pointwise = M⁻¹ * ∑).
  congr 1
  funext y
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, perLetterMixtureDensity]

/-- The mixture density is bounded above by `(√(2πN))⁻¹` (each component is, and the
weights `1/M` sum to ≤ 1). -/
private lemma perLetterMixtureDensity_le_sup
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (hM : 0 < M) (y : ℝ) :
    perLetterMixtureDensity N c i y ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹ := by
  -- each Gaussian component pdf is `≤ ofReal (√(2πN))⁻¹`
  have h_comp : ∀ m : Fin M,
      gaussianPDF (c.encoder m i) N y ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹ := by
    intro m
    rw [gaussianPDF]
    refine ENNReal.ofReal_le_ofReal ?_
    -- `gaussianPDFReal μ N y ≤ (√(2πN))⁻¹` (exp factor ≤ 1)
    rw [gaussianPDFReal]
    have h_const_nonneg : 0 ≤ (Real.sqrt (2 * Real.pi * N))⁻¹ := by positivity
    have h_exp_le_one : Real.exp (-(y - c.encoder m i) ^ 2 / (2 * N)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div]
      have : 0 ≤ (y - c.encoder m i) ^ 2 / (2 * (N : ℝ)) := by positivity
      linarith
    calc (Real.sqrt (2 * Real.pi * N))⁻¹ * Real.exp (-(y - c.encoder m i) ^ 2 / (2 * N))
        ≤ (Real.sqrt (2 * Real.pi * N))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h_exp_le_one h_const_nonneg
      _ = (Real.sqrt (2 * Real.pi * N))⁻¹ := mul_one _
  unfold perLetterMixtureDensity
  -- `M⁻¹ * ∑ₘ (≤ B) ≤ M⁻¹ * (M • B) = M⁻¹ * (M * B) = B`
  calc (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, gaussianPDF (c.encoder m i) N y
      ≤ (M : ℝ≥0∞)⁻¹ * ∑ _m : Fin M, ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹ := by
        gcongr with m _
        exact h_comp m
    _ = (M : ℝ≥0∞)⁻¹ * ((M : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹ := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hM))
          (ENNReal.natCast_ne_top M), one_mul]

/-- Lower bound on `log` of the mixture density (no Chebyshev needed — a single component
suffices): there are `c₀ c₁` with `|log (f y).toReal| ≤ c₀ + c₁ y²`. -/
private lemma perLetterMixtureDensity_log_abs_le
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (hM : 0 < M) (hN : N ≠ 0) :
    ∃ c₀ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ y : ℝ,
      |Real.log ((perLetterMixtureDensity N c i y).toReal)| ≤ c₀ + c₁ * y ^ 2 := by
  classical
  have hN_pos : (0 : ℝ) < N := lt_of_le_of_ne N.coe_nonneg (fun h => hN (by exact_mod_cast h.symm))
  set sup : ℝ := (Real.sqrt (2 * Real.pi * N))⁻¹ with hsup_def
  have hsup_nonneg : 0 ≤ sup := by rw [hsup_def]; positivity
  -- a fixed representative message `m₀`
  set m₀ : Fin M := ⟨0, hM⟩ with hm₀_def
  set μ₀ : ℝ := c.encoder m₀ i with hμ₀_def
  -- The mixture density never exceeds `sup` (real form via `le_sup`).
  have h_up_real : ∀ y, (perLetterMixtureDensity N c i y).toReal ≤ sup := by
    intro y
    have h := perLetterMixtureDensity_le_sup N c i hM y
    rw [← hsup_def] at h
    calc (perLetterMixtureDensity N c i y).toReal
        ≤ (ENNReal.ofReal sup).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      _ = sup := ENNReal.toReal_ofReal hsup_nonneg
  -- upper bound on `log f(y)`: `≤ max (log sup) 0`.
  have h_up : ∀ y, Real.log ((perLetterMixtureDensity N c i y).toReal) ≤ max (Real.log sup) 0 := by
    intro y
    rcases le_or_gt (perLetterMixtureDensity N c i y).toReal 0 with h0 | h0
    · have : (perLetterMixtureDensity N c i y).toReal = 0 := le_antisymm h0 ENNReal.toReal_nonneg
      rw [this, Real.log_zero]; exact le_max_right _ _
    · exact le_trans (Real.log_le_log h0 (h_up_real y)) (le_max_left _ _)
  -- single-component lower bound: `f(y).toReal ≥ M⁻¹ * gaussianPDFReal μ₀ N y`.
  have h_low_real : ∀ y, ((M : ℝ)⁻¹) * gaussianPDFReal μ₀ N y
      ≤ (perLetterMixtureDensity N c i y).toReal := by
    intro y
    -- `f y = M⁻¹ * ∑ₘ ofReal (gaussianPDFReal · ) ≥ M⁻¹ * ofReal (gaussianPDFReal μ₀)`
    have h_ne_top : perLetterMixtureDensity N c i y ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (perLetterMixtureDensity_le_sup N c i hM y)
    have h_ge : ENNReal.ofReal ((M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y)
        ≤ perLetterMixtureDensity N c i y := by
      unfold perLetterMixtureDensity
      rw [ENNReal.ofReal_mul (by positivity)]
      have h_inv : ENNReal.ofReal ((M : ℝ)⁻¹) = (M : ℝ≥0∞)⁻¹ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast hM)]
      rw [h_inv]
      gcongr
      -- `ofReal (gaussianPDFReal μ₀ N y) = gaussianPDF μ₀ N y ≤ ∑ₘ gaussianPDF · `
      rw [← gaussianPDF]
      exact Finset.single_le_sum (f := fun m => gaussianPDF (c.encoder m i) N y)
        (fun m _ => zero_le') (Finset.mem_univ m₀)
    calc ((M : ℝ)⁻¹) * gaussianPDFReal μ₀ N y
        = (ENNReal.ofReal ((M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y)).toReal := by
          rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity) (gaussianPDFReal_nonneg μ₀ N y))]
      _ ≤ (perLetterMixtureDensity N c i y).toReal := ENNReal.toReal_mono h_ne_top h_ge
  -- lower bound on `log f(y)`: `-log f(y) ≤ (1/N) y² + b` from the single-component bound.
  -- `M⁻¹ · gaussianPDFReal μ₀ N y = M⁻¹ · sup · exp(-(y-μ₀)²/(2N))`, so
  -- `-log(M⁻¹ gaussianPDFReal) = log M - log sup + (y-μ₀)²/(2N) ≤ a y² + b`.
  have hgpos : ∀ y, 0 < gaussianPDFReal μ₀ N y := fun y => gaussianPDFReal_pos μ₀ N y hN
  set bLow : ℝ := Real.log M - Real.log sup + μ₀ ^ 2 / (N : ℝ) with hbLow_def
  refine ⟨max (Real.log sup) 0 + max bLow 0, 1 / (N : ℝ), by positivity, fun y => ?_⟩
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- `-(c₀ + c₁ y²) ≤ log f(y)`: use single-component lower bound + log algebra.
    have h_low := h_low_real y
    have hlow_pos : 0 < (M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y :=
      mul_pos (by positivity) (hgpos y)
    have h_log_low : Real.log ((M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y)
        ≤ Real.log ((perLetterMixtureDensity N c i y).toReal) :=
      Real.log_le_log hlow_pos h_low
    -- compute `log (M⁻¹ gaussianPDFReal μ₀ N y)`
    have h_log_eq : Real.log ((M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y)
        = -Real.log M + (Real.log sup - (y - μ₀) ^ 2 / (2 * N)) := by
      rw [Real.log_mul (by positivity) (hgpos y).ne', Real.log_inv, gaussianPDFReal,
        Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp, ← hsup_def, neg_div]
      ring
    rw [h_log_eq] at h_log_low
    -- `(y-μ₀)²/(2N) ≤ (y²+μ₀²)/N` (cleared division)
    have h_quad : (y - μ₀) ^ 2 / (2 * (N : ℝ)) ≤ (y ^ 2 + μ₀ ^ 2) / (N : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hN_pos]
      nlinarith [sq_nonneg (y + μ₀), hN_pos]
    have h_split : (y ^ 2 + μ₀ ^ 2) / (N : ℝ) = y ^ 2 / (N : ℝ) + μ₀ ^ 2 / (N : ℝ) := by
      rw [add_div]
    have h_max1 : (0 : ℝ) ≤ max (Real.log sup) 0 := le_max_right _ _
    have h_max2 : bLow ≤ max bLow 0 := le_max_left _ _
    have h_c1 : 1 / (N : ℝ) * y ^ 2 = y ^ 2 / (N : ℝ) := by rw [div_mul_eq_mul_div, one_mul]
    rw [h_c1]
    -- unfold `bLow` so linarith sees the same atom `μ₀²/N`
    simp only [hbLow_def] at *
    linarith [h_log_low, h_quad, h_split, h_max1, h_max2]
  · -- `log f(y) ≤ c₀ + c₁ y²`: from the upper bound.
    have h := h_up y
    have h_sq : (0 : ℝ) ≤ 1 / (N : ℝ) * y ^ 2 := by positivity
    have h_max2 : (0 : ℝ) ≤ max bLow 0 := le_max_right _ _
    linarith [h, h_sq, h_max2]

/-- `y²` is integrable against the per-letter output law (finite mixture of Gaussians,
each with finite second moment). -/
private lemma perLetterLaw_sq_integrable
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (hM : 0 < M) (hN : N ≠ 0) :
    Integrable (fun y : ℝ => y ^ 2)
      ((converseJointInline h_meas c).map (fun ω => ω.2 i)) := by
  rw [perLetterLaw_eq_mixture h_meas c i]
  -- each component Gaussian has integrable `y²`
  have h_comp : ∀ m : Fin M, Integrable (fun y : ℝ => y ^ 2) (gaussianReal (c.encoder m i) N) := by
    intro m
    have h := (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 2).integrable_sq
    simpa using h
  have hM_ne_top : (M : ℝ≥0∞)⁻¹ ≠ ∞ := by
    simp only [ne_eq, ENNReal.inv_eq_top, Nat.cast_eq_zero]
    exact Nat.pos_iff_ne_zero.mp hM
  refine Integrable.smul_measure ?_ hM_ne_top
  exact integrable_finsetSum_measure.mpr (fun m _ => h_comp m)

/-- **Per-letter `Y_i` log-density integrability** (旧 `PerLetterIntegrabilityForConverse`).

For every coordinate `i`, the per-letter output law `Y_i` (here written as the pushforward
of the inlined joint along `ω ↦ ω.2 i`) has Lebesgue-integrable `negMulLog (rnDeriv · vol)`.
Consumer-side `unfold perLetterYLaw awgnConverseJoint` reduces `perLetterYLaw h_meas c i`
to `(converseJointInline h_meas c).map (fun ω => ω.2 i)` (defeq).

Genuine: the per-letter law is a finite Gaussian mixture; `negMulLog` of its `rnDeriv`
is dominated by a Gaussian-moment integrand (`perLetterMixtureDensity_log_abs_le` +
`perLetterLaw_sq_integrable`). The degenerate `M = 0` / `N = 0` cases give a singular
law (`rnDeriv = 0` a.e., `negMulLog 0 = 0`, constant, integrable).

Independently audited 2026-06-11 (wall-overturn confirmed genuine): signature is
byte-identical to the pre-closure `sorry` version (no hypothesis added, conclusion
unweakened — the former `wall:awgn-per-letter-integrability` over-claimed continuous
SMB / n-dim `differentialEntropy` for what is a 1-D finite-mixture log-density
domination); the `M = 0` / `N = 0` boundary is discharged by a genuine singular-law
argument (`rnDeriv =ᵐ 0`), not an exfalso/vacuity exploit; `#print axioms` =
`[propext, Classical.choice, Quot.sound]` (sorryAx-free, this theorem + all 6 helpers).
@audit:ok -/
@[entry_point]
theorem awgnPerLetterIntegrability_holds
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) :
    ∀ i : Fin n,
      MeasureTheory.Integrable (fun y : ℝ =>
          Real.negMulLog
            (((converseJointInline h_meas c).map (fun ω => ω.2 i)).rnDeriv
                MeasureTheory.volume y).toReal)
        MeasureTheory.volume := by
  classical
  intro i
  set ν : Measure ℝ := (converseJointInline h_meas c).map (fun ω => ω.2 i) with hν_def
  -- Degenerate cases (`M = 0` or `N = 0`): `ν ⟂ volume`, so `rnDeriv =ᵐ 0` and the
  -- integrand is a.e. `negMulLog 0 = 0`, hence integrable.
  by_cases hMN : 0 < M ∧ N ≠ 0
  · obtain ⟨hM, hN⟩ := hMN
    haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM⟩
    -- `ν` is a probability measure (pushforward of the probability mixture)
    haveI hν_prob : IsProbabilityMeasure ν := by
      rw [hν_def]
      exact Measure.isProbabilityMeasure_map ((measurable_pi_apply i).comp measurable_snd).aemeasurable
    -- main case: `ν = volume.withDensity f`, `f := perLetterMixtureDensity N c i`.
    set f : ℝ → ℝ≥0∞ := perLetterMixtureDensity N c i with hf_def
    have hf_meas : Measurable f := perLetterMixtureDensity_measurable N c i
    have hν_wd : ν = volume.withDensity f := by
      rw [hν_def, hf_def]; exact perLetterLaw_withDensity h_meas c i hM hN
    -- `ν.rnDeriv volume =ᵐ[volume] f`
    have h_rn_ae : ν.rnDeriv volume =ᵐ[volume] f := by
      rw [hν_wd]; exact Measure.rnDeriv_withDensity volume hf_meas
    -- `f y < ∞` a.e. (bounded above)
    have hf_lt_top : ∀ᵐ y ∂(volume : Measure ℝ), f y < ∞ :=
      Filter.Eventually.of_forall (fun y =>
        lt_of_le_of_lt (perLetterMixtureDensity_le_sup N c i hM y) ENNReal.ofReal_lt_top)
    -- quadratic abs bound on `log f`
    obtain ⟨c₀, c₁, hc₁, h_abs⟩ := perLetterMixtureDensity_log_abs_le N c i hM hN
    -- `c₀ + c₁ y²` integrable against ν, transport to `(f y).toReal • (c₀+c₁y²)` on volume
    have h_dom_ν : Integrable (fun y : ℝ => c₀ + c₁ * y ^ 2) ν :=
      (integrable_const c₀).add ((perLetterLaw_sq_integrable h_meas c i hM hN).const_mul c₁)
    have h_dom_vol : Integrable (fun y : ℝ => (f y).toReal • (c₀ + c₁ * y ^ 2)) volume :=
      (integrable_withDensity_iff_integrable_smul' hf_meas hf_lt_top).mp
        (by rw [← hν_wd]; exact h_dom_ν)
    -- dominate `negMulLog (rnDeriv)` by `(f y).toReal · (c₀ + c₁ y²)`
    refine Integrable.mono' h_dom_vol ?_ ?_
    · have h_rn_meas : Measurable (fun y => (ν.rnDeriv volume y).toReal) :=
        (Measure.measurable_rnDeriv ν volume).ennreal_toReal
      exact (Real.continuous_negMulLog.measurable.comp h_rn_meas).aestronglyMeasurable
    · filter_upwards [h_rn_ae] with y hy
      rw [hy, smul_eq_mul, Real.norm_eq_abs]
      set t : ℝ := (f y).toReal with ht_def
      have ht_nonneg : 0 ≤ t := ENNReal.toReal_nonneg
      rw [Real.negMulLog_def, abs_mul, abs_neg, abs_of_nonneg ht_nonneg]
      exact mul_le_mul_of_nonneg_left (h_abs y) ht_nonneg
  · -- degenerate: `ν ⟂ volume`, so `rnDeriv =ᵐ 0`; integrand a.e. `0`.
    have h_rn_zero : ν.rnDeriv volume =ᵐ[volume] 0 := by
      rcases not_and_or.mp hMN with hM0 | hN0
      · -- `M = 0`: `ν = 0` measure
        have hM_eq : M = 0 := Nat.le_zero.mp (Nat.not_lt.mp hM0)
        have hν_zero : ν = 0 := by
          rw [hν_def, perLetterLaw_eq_mixture h_meas c i]
          subst hM_eq
          simp
        rw [hν_zero]; exact Measure.rnDeriv_zero volume
      · -- `N = 0`: `ν` is a finite sum of Diracs, mutually singular with volume
        have hN_eq : N = 0 := not_not.mp hN0
        have hν_dirac : ν = ((M : ℝ≥0∞))⁻¹ • ∑ m : Fin M, Measure.dirac (c.encoder m i) := by
          rw [hν_def, perLetterLaw_eq_mixture h_meas c i]
          subst hN_eq
          simp only [gaussianReal_zero_var]
        have h_sum_sing : ∀ s : Finset (Fin M),
            (∑ m ∈ s, Measure.dirac (c.encoder m i)) ⟂ₘ (volume : Measure ℝ) := by
          intro s
          induction s using Finset.induction with
          | empty => simp [Measure.MutuallySingular.zero_left]
          | insert m s hms ih =>
              rw [Finset.sum_insert hms]
              exact (mutuallySingular_dirac (c.encoder m i) volume).add_left ih
        have h_sing : ν ⟂ₘ volume := by
          rw [hν_dirac]
          exact (h_sum_sing Finset.univ).smul _
        exact h_sing.rnDeriv_ae_eq_zero
    -- integrand a.e. equals `negMulLog 0 = 0`
    refine (integrable_zero ℝ ℝ volume).congr ?_
    filter_upwards [h_rn_zero] with y hy
    rw [hy]; simp

/-! ### Wall 5 — `awgn-continuous-mi-chain-rule` -/

/-- **Memoryless AWGN continuous MI chain rule** (旧 `ContinuousMIChainRuleForConverse`,
Mathlib 壁 T-FFC-3).

`I(X^n; Y^n) ≤ ∑ᵢ I(X_i; Y_i)` on the inlined joint. InformationTheory 既存 `Fintype α`
制約付き chain rule は AWGN `α := ℝ` で reuse 不可、`mutualInfo_pi_eq_sum`
(`MIChainRule.lean:318`) も iid joint 仮定で発火不可 (AWGN code は non-iid codebook)。
Consumer-side `unfold jointMIXnYn perLetterMI awgnConverseJoint` で defeq.

@residual(wall:awgn-continuous-mi-chain-rule) -/
@[entry_point]
theorem awgnContinuousMIChainRule_holds
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) :
    (mutualInfo (converseJointInline h_meas c)
        (fun ω => c.encoder ω.1) Prod.snd).toReal
      ≤ ∑ i : Fin n,
          (mutualInfo (converseJointInline h_meas c)
            (fun ω => c.encoder ω.1 i) (fun ω => ω.2 i)).toReal := by
  sorry

/-! ### Wall 6 — `awgn-converse-markov-regularity` (Route B, L-AWGNM5-1-α) -/

/-- **Markov chain `W → encoder ∘ W → Y^n` factorization** (旧 `MarkovChainForConverse`).

`IsMarkovChain (converseJointInline h_meas c) Prod.fst (encoder ∘ fst) Prod.snd` の γ-form
joint factorization, **genuine closure** (旧 wall `awgn-converse-markov-regularity` は
真の Mathlib 不在ではなく deterministic-encoder factorization の plumbing 過大評価だった)。

証明骨子: 基本恒等式 `μ = (μ.map fst) ⊗ₘ (W.comap encoder)` (message-space marginal、
`W := Channel.toBlock (awgnChannel N) n` は noise block kernel) を mixture-of-diracs 上で
`ext_of_lintegral` により確立 (`h_marginalA`)。これから `condDistrib Yo Zc μ =ᵐ W`
(`condDistrib_ae_eq_of_measure_eq_compProd`) を導き、`condDistrib Xs Zc μ` を
`compProd_map_condDistrib` で吸収、triple-joint factorization を `ext_of_lintegral` +
`h_marginalA` reduction で検証する (precedent:
`BlockwiseChannel.isMarkovChain_per_letter_input`)。`#print axioms` は sorryAx-free
(`[propext, Classical.choice, Quot.sound]`、本 session 機械確認)。
@audit:ok -/
@[entry_point]
theorem awgnConverseMarkov_holds
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    IsMarkovChain (converseJointInline h_meas c)
      (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
      (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1)
      (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) := by
  set μ : Measure (Fin M × (Fin n → ℝ)) := converseJointInline h_meas c with hμ_def
  -- The three RVs.
  set Xs : Fin M × (Fin n → ℝ) → Fin M := Prod.fst with hXs_def
  set Zc : Fin M × (Fin n → ℝ) → (Fin n → ℝ) := fun ω => c.encoder ω.1 with hZc_def
  set Yo : Fin M × (Fin n → ℝ) → (Fin n → ℝ) := Prod.snd with hYo_def
  -- The noise block kernel `W^{⊗n}` of the AWGN channel.
  set W : Kernel (Fin n → ℝ) (Fin n → ℝ) :=
    ChannelCoding.Channel.toBlock (awgnChannel N h_meas) n with hW_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  -- Measurability of the three RVs.
  have hXs_meas : Measurable Xs := measurable_fst
  have hZc_meas : Measurable Zc := by
    rw [hZc_def]; exact (Measurable.of_discrete).comp measurable_fst
  have hYo_meas : Measurable Yo := measurable_snd
  have hg_meas : Measurable c.encoder := Measurable.of_discrete
  -- `W.comap encoder`: the channel kernel reindexed from message to codeword.
  set Wg : Kernel (Fin M) (Fin n → ℝ) := W.comap c.encoder hg_meas with hWg_def
  -- **Fundamental message-space marginal (A)**: `μ = (μ.map Xs) ⊗ₘ (W.comap encoder)`.
  -- Since `(Xs ω, Yo ω) = ω`, this says the converse joint factors as
  -- `uniform(W) ⊗ₘ (∏ᵢ awgnChannel (encoder · i))`. Proved by `ext_of_lintegral` on the
  -- mixture-of-diracs.
  -- `μ.map Xs = (1/M) • ∑ₘ δ_m` (uniform message law).
  have h_map_Xs : μ.map Xs
      = ((Fintype.card (Fin M) : ℝ≥0∞)⁻¹) • ∑ m : Fin M, (Measure.dirac m) := by
    rw [hμ_def, hXs_def, converseJointInline]
    rw [Measure.map_smul]
    congr 1
    rw [Measure.map_finset_sum (measurable_fst.aemeasurable)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Measure.map_fst_prod]
    simp
  have h_marginalA : μ = (μ.map Xs) ⊗ₘ Wg := by
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    -- RHS via compProd, then h_map_Xs (do RHS first, before unfolding μ on LHS).
    rw [Measure.lintegral_compProd hf, h_map_Xs, lintegral_smul_measure,
      lintegral_finsetSum_measure]
    have hRHS_summand : ∀ m : Fin M,
        ∫⁻ a : Fin M, ∫⁻ y : Fin n → ℝ, f (a, y) ∂(Wg a) ∂(Measure.dirac m)
          = ∫⁻ y : Fin n → ℝ, f (m, y)
              ∂(Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))) := by
      intro m
      rw [lintegral_dirac]
      rfl
    simp_rw [hRHS_summand]
    -- LHS over the mixture.
    rw [hμ_def, converseJointInline, lintegral_smul_measure,
      lintegral_finsetSum_measure]
    have hLHS_summand : ∀ m : Fin M,
        ∫⁻ ω : Fin M × (Fin n → ℝ), f ω
            ∂((Measure.dirac m).prod
              (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))))
          = ∫⁻ y : Fin n → ℝ, f (m, y)
              ∂(Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))) := by
      intro m
      rw [lintegral_prod _ hf.aemeasurable, lintegral_dirac]
    simp_rw [hLHS_summand]
  -- `μ.map Zc = (1/M) • ∑ₘ δ_(encoder m)` (codeword law).
  have h_map_Zc : μ.map Zc
      = ((Fintype.card (Fin M) : ℝ≥0∞)⁻¹) • ∑ m : Fin M, (Measure.dirac (c.encoder m)) := by
    have hZc_comp : Zc = c.encoder ∘ Xs := rfl
    rw [hZc_comp, ← Measure.map_map Measurable.of_discrete hXs_meas, h_map_Xs,
      Measure.map_smul]
    congr 1
    rw [Measure.map_finset_sum' Measurable.of_discrete.aemeasurable]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Measure.map_dirac' Measurable.of_discrete]
  -- Linchpin marginal: `μ.map (Zc, Yo) = (μ.map Zc) ⊗ₘ W`.
  have h_pair_eq : μ.map (fun ω => (Zc ω, Yo ω)) = (μ.map Zc) ⊗ₘ W := by
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    -- RHS via compProd + h_map_Zc.
    rw [Measure.lintegral_compProd hf, h_map_Zc, lintegral_smul_measure,
      lintegral_finsetSum_measure]
    have hRHS_summand : ∀ m : Fin M,
        ∫⁻ z : Fin n → ℝ, ∫⁻ y : Fin n → ℝ, f (z, y) ∂(W z) ∂(Measure.dirac (c.encoder m))
          = ∫⁻ y : Fin n → ℝ, f (c.encoder m, y)
              ∂(Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))) := by
      intro m
      rw [lintegral_dirac' _
        (Measurable.lintegral_kernel_prod_right' (κ := W) hf)]
      rfl
    simp_rw [hRHS_summand]
    -- LHS over the mixture.
    rw [lintegral_map hf (hZc_meas.prodMk hYo_meas), hμ_def, converseJointInline,
      lintegral_smul_measure, lintegral_finsetSum_measure]
    have hLHS_summand : ∀ m : Fin M,
        ∫⁻ ω : Fin M × (Fin n → ℝ), f (Zc ω, Yo ω)
            ∂((Measure.dirac m).prod
              (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))))
          = ∫⁻ y : Fin n → ℝ, f (c.encoder m, y)
              ∂(Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))) := by
      intro m
      rw [lintegral_prod (fun ω : Fin M × (Fin n → ℝ) => f (Zc ω, Yo ω))
        (hf.comp (hZc_meas.prodMk hYo_meas)).aemeasurable, lintegral_dirac]
    simp_rw [hLHS_summand]
  -- Identify `condDistrib Yo Zc μ =ᵐ[μ.map Zc] W`.
  haveI : IsProbabilityMeasure (μ.map Zc) := Measure.isProbabilityMeasure_map hZc_meas.aemeasurable
  have hK_Y_eq : condDistrib Yo Zc μ =ᵐ[μ.map Zc] W :=
    condDistrib_ae_eq_of_measure_eq_compProd Zc hYo_meas.aemeasurable h_pair_eq
  -- Unfold IsMarkovChain and substitute condDistrib Yo Zc → W on the RHS.
  unfold IsMarkovChain
  set K_X : Kernel (Fin n → ℝ) (Fin M) := condDistrib Xs Zc μ with hK_X_def
  have h_compProd_eq :
      (μ.map Zc) ⊗ₘ (K_X ×ₖ condDistrib Yo Zc μ) = (μ.map Zc) ⊗ₘ (K_X ×ₖ W) := by
    refine Measure.compProd_congr ?_
    filter_upwards [hK_Y_eq] with a ha
    ext s hs
    rw [Kernel.prod_apply, Kernel.prod_apply, ha]
  rw [h_compProd_eq]
  -- Triple-joint factorization via ext_of_lintegral.
  have h_LHS_meas : Measurable (fun ω => (Zc ω, Xs ω, Yo ω)) :=
    hZc_meas.prodMk (hXs_meas.prodMk hYo_meas)
  -- `compProd_map_condDistrib`: fold K_X back into `μ.map (Zc, Xs)`.
  have hKX_fold : (μ.map Zc) ⊗ₘ K_X = μ.map (fun ω => (Zc ω, Xs ω)) :=
    compProd_map_condDistrib (μ := μ) (X := Zc) (Y := Xs) hXs_meas.aemeasurable
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  -- LHS: ∫⁻ ω, f (Zc ω, Xs ω, Yo ω) ∂μ.
  rw [lintegral_map hf h_LHS_meas]
  -- RHS: unfold the outer compProd over (μ.map Zc), then the inner product kernel.
  rw [Measure.lintegral_compProd hf]
  -- RHS inner: ∫⁻ p ∂((K_X ×ₖ W) z), f (z, p.1, p.2)
  --          = ∫⁻ x ∂(K_X z), ∫⁻ y ∂(W z), f (z, x, y).
  have h_inner_split : ∀ z : Fin n → ℝ,
      ∫⁻ p : Fin M × (Fin n → ℝ), f (z, p.1, p.2) ∂((K_X ×ₖ W) z)
        = ∫⁻ x : Fin M, ∫⁻ y : Fin n → ℝ, f (z, x, y) ∂(W z) ∂(K_X z) := by
    intro z
    rw [Kernel.prod_apply]
    rw [lintegral_prod (fun p : Fin M × (Fin n → ℝ) => f (z, p.1, p.2))
      (hf.comp (measurable_const.prodMk
        (measurable_fst.prodMk measurable_snd))).aemeasurable]
  simp_rw [h_inner_split]
  -- Define G (z, x) := ∫⁻ y ∂(W z), f (z, x, y), so RHS = ∫⁻ z ∂(μ.map Zc), ∫⁻ x ∂(K_X z), G (z, x).
  set G : (Fin n → ℝ) × Fin M → ℝ≥0∞ :=
    fun p => ∫⁻ y : Fin n → ℝ, f (p.1, p.2, y) ∂(W p.1) with hG_def
  have hG_meas : Measurable G := by
    let K' : Kernel ((Fin n → ℝ) × Fin M) (Fin n → ℝ) :=
      W.comap (Prod.fst : (Fin n → ℝ) × Fin M → (Fin n → ℝ)) measurable_fst
    have h_eq_K' : G = fun p : (Fin n → ℝ) × Fin M =>
        ∫⁻ y : Fin n → ℝ, f (p.1, p.2, y) ∂(K' p) := by
      funext p; simp [G, K', Kernel.comap_apply]
    rw [h_eq_K']
    exact Measurable.lintegral_kernel_prod_right' (κ := K')
      (f := fun pp : ((Fin n → ℝ) × Fin M) × (Fin n → ℝ) => f (pp.1.1, pp.1.2, pp.2))
      (hf.comp (((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))
  have h_RHS_is_G : ∀ z : Fin n → ℝ, ∀ x : Fin M,
      ∫⁻ y : Fin n → ℝ, f (z, x, y) ∂(W z) = G (z, x) := fun _ _ => rfl
  simp_rw [h_RHS_is_G]
  -- RHS = ∫⁻ z ∂(μ.map Zc), ∫⁻ x ∂(K_X z), G (z, x) = ∫⁻ p ∂((μ.map Zc) ⊗ₘ K_X), G p.
  rw [← Measure.lintegral_compProd hG_meas, hKX_fold]
  -- RHS = ∫⁻ p ∂(μ.map (Zc, Xs)), G p = ∫⁻ ω ∂μ, G (Zc ω, Xs ω).
  rw [lintegral_map hG_meas (hZc_meas.prodMk hXs_meas)]
  -- Now goal: ∫⁻ ω, f (Zc ω, Xs ω, Yo ω) ∂μ = ∫⁻ ω, G (Zc ω, Xs ω) ∂μ.
  rw [← hμ_def]
  -- Reduce any `∫⁻ ω, H ω ∂μ` through message-space marginal (A).
  have h_reduce : ∀ H : Fin M × (Fin n → ℝ) → ℝ≥0∞, Measurable H →
      ∫⁻ ω, H ω ∂μ
        = ∫⁻ a : Fin M, ∫⁻ y : Fin n → ℝ, H (a, y) ∂(Wg a) ∂(μ.map Xs) := by
    intro H hH
    conv_lhs => rw [h_marginalA]
    rw [Measure.lintegral_compProd hH]
  rw [h_reduce (fun ω => f (Zc ω, Xs ω, Yo ω)) (hf.comp h_LHS_meas),
    h_reduce (fun ω => G (Zc ω, Xs ω)) (hG_meas.comp (hZc_meas.prodMk hXs_meas))]
  -- Both inner integrals over `Wg a`. For each message `a`:
  refine lintegral_congr fun a => ?_
  have hWg_eq : Wg a = W (c.encoder a) := by rw [hWg_def, Kernel.comap_apply]
  haveI : IsProbabilityMeasure (Wg a) := by rw [hWg_eq]; infer_instance
  -- LHS inner: ∫⁻ y ∂(Wg a), f (encoder a, a, y).  `(Zc (a,y), Xs (a,y), Yo (a,y)) = (encoder a, a, y)`.
  -- RHS inner: ∫⁻ y ∂(Wg a), G (encoder a, a), constant in y, value `∫⁻ y' ∂(W (encoder a)), f (encoder a, a, y')`.
  have hRHS_eval : (fun y : Fin n → ℝ => G (Zc (a, y), Xs (a, y)))
      = (fun _ : Fin n → ℝ => ∫⁻ y' : Fin n → ℝ, f (c.encoder a, a, y') ∂(Wg a)) := by
    funext y
    show G (c.encoder a, a) = _
    rw [hG_def, hWg_eq]
  rw [hRHS_eval, lintegral_const, measure_univ, mul_one]

end InformationTheory.Shannon.AWGN
