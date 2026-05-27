import Common2026.Meta.EntryPoint
import Common2026.Shannon.AWGN
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
  `Common2026.Shannon.AWGN` (`IsAwgnChannelMeasurable` / `awgnChannel`) +
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

/-! ## Wall 1 — `awgn-continuous-aep-gaussian` -/

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

end InformationTheory.Shannon.AWGN
