import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN
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
(0 sorry), so no shared wall is needed and this file's wall count is 6.) -/

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

**Markov の Route 判定 (Phase 3α-1)**: `MarkovChainForConverse` の genuine 化
(`IsMarkovChain (awgnConverseJoint) Prod.fst (encoder∘fst) Prod.snd` の condDistrib
joint factorization 導出) は条件付き独立 `W ⊥ Y^n | X^n` の measure-theoretic
factorization を要し、当 session の 30-50 行 bridge 上限を超える (encoder 非単射時の
`condDistrib W (encoder∘W)` が非自明)。よって **L-AWGNM5-1-α 撤退 = Route B**:
`awgnConverseMarkov_holds` を shared sorry 補題として追加 (wall
`awgn-converse-markov-regularity`、wall 件数 3 → 4)。 -/

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

/-! ### Wall 4 — `awgn-per-letter-integrability` -/

/-- **Per-letter `Y_i` log-density integrability** (旧 `PerLetterIntegrabilityForConverse`,
Mathlib 壁 T-FFC-2).

For every coordinate `i`, the per-letter output law `Y_i` (here written as the pushforward
of the inlined joint along `ω ↦ ω.2 i`) has Lebesgue-integrable `negMulLog (rnDeriv · vol)`.
Consumer-side `unfold perLetterYLaw awgnConverseJoint` reduces `perLetterYLaw h_meas c i`
to `(converseJointInline h_meas c).map (fun ω => ω.2 i)` (defeq).

Mathlib gap: continuous SMB / n-dim `differentialEntropy` integrability of a Gaussian
mixture's log-density (`h_ent_int` of `differentialEntropy_le_gaussian_of_variance_le`,
`DifferentialEntropy.lean:518`) is absent.

@residual(wall:awgn-per-letter-integrability) -/
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
  sorry

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

`IsMarkovChain (awgnConverseJoint h_meas c) Prod.fst (encoder ∘ fst) Prod.snd` の γ-form
joint factorization. AWGN code 構造 (encoder deterministic + channel memoryless + W
uniform) から「自然帰結」だが、`IsMarkovChain` の `condDistrib` factorization
(`μ.map (Zc, Xs, Yo) = (μ.map Zc) ⊗ₘ (condDistrib Xs Zc ×ₖ condDistrib Yo Zc)`) を
genuine に導くには条件付き独立 `W ⊥ Y^n | X^n` の measure-theoretic 構成を要し、当
session の bridge 上限を超える (encoder 非単射時の `condDistrib W (encoder∘W)` が非自明)。

**Route B (L-AWGNM5-1-α 撤退)**: shared sorry 補題として保持。closure 時は本補題 1 件を
埋めれば genuine 化。Consumer-side `unfold MarkovChainForConverse awgnConverseJoint` で
defeq に接続。

@residual(wall:awgn-converse-markov-regularity) -/
@[entry_point]
theorem awgnConverseMarkov_holds
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    IsMarkovChain (converseJointInline h_meas c)
      (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
      (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1)
      (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) := by
  sorry

end InformationTheory.Shannon.AWGN
