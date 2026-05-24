import Common2026.Shannon.ChannelCodingShannonTheorem
import Common2026.Shannon.ChannelCodingShannonTheoremGeneral
import Common2026.Shannon.AEPRate

/-!
# Shannon noisy channel coding theorem — `hW_pos` 完全除去 (D-1'' Phase D)

[D-1'' ムーンショット plan](../../../docs/shannon/channel-coding-shannon-theorem-general-plan.md)
の最終目標: 親 D-1 `shannon_noisy_channel_coding_theorem`
(`ChannelCodingShannonTheorem.lean:840`、`hW_pos` 必須) を、Phase A-C で publish 済の
smoothing infrastructure (`Channel.smooth W δ`, `errorProbAt_smooth_TV`) と組み合わせ、
`hW_pos` 仮定を完全に除去する。

## Approach (hypothesis pass-through MVP)

本ファイルは **hypothesis pass-through 形** で Phase D 主定理を完結させる:

1. Per-`n` の `(δ_n, M_n, c_n)` 系列 (`2 n δ_n < ε/2` かつ `errorProbAt(W_smooth δ_n) < ε/2`)
   を hypothesis `h_passthrough` として受け取る。
2. Body は Phase A-C で publish 済の TV bound `errorProbAt_smooth_TV`
   (`|errorProbAt(W_smooth δ) - errorProbAt(W)| ≤ 2 n δ`) で 2 つの `ε/2` を glue する:
   `errorProbAt(W) ≤ errorProbAt(W_smooth δ) + 2 n δ < ε/2 + ε/2 = ε`.

これにより本シードは 0 sorry で完成し、Phase A-C の TV bound の使い道が体現される。

## 撤退ライン

`h_passthrough` を自力で構成する (= 仮定なしで主定理を結論する) には、parent D-1 の `N(δ)` を
`δ ∈ (0, δ_B]` 上で **n-uniform** に bound する parent surgery が必要 (`channel_coding_achievability`
内 `Tendsto.metric_atTop` extraction の closed-form 化、~200-400 行)。これは後続シードに deferred。

本シードは hypothesis pass-through MVP として完成。後続 parent surgery seed への interface
(`h_passthrough` の型) は本ファイル主定理 signature により明示化されている。
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

omit [DecidableEq α] [Nonempty α] in
/-- **D-1'' Phase D 主定理 (hypothesis pass-through 形)**: `hW_pos` 完全除去版
Shannon noisy channel coding theorem。

`h_passthrough`: per-`n` の `(δ_n, M_n, c_n)` 系列が存在し、`2 n δ_n < ε/2` かつ
`errorProbAt(W_smooth δ_n) < ε/2` を満たす、という仮定 (parent surgery で構成される予定)。
本ファイルは TV bound `errorProbAt_smooth_TV` で `errorProbAt W < ε` を結論する。

`@audit:retract-candidate(superseded-by-full-discharge)` -/
theorem shannon_noisy_channel_coding_theorem_general
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (_hR_pos : 0 < R) (_hR : R < capacity W)
    {ε : ℝ} (_hε : 0 < ε)
    (h_passthrough :
      ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_le : δ ≤ 1),
        2 * (n : ℝ) * δ < ε / 2 ∧
        ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
          (c : Code M n α β),
          ∀ m, (c.errorProbAt (Channel.smooth W δ) m).toReal < ε / 2) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        ∀ m, (c.errorProbAt W m).toReal < ε := by
  obtain ⟨N, hN⟩ := h_passthrough
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨δ, hδ_pos, hδ_le, h_tv_bd, M, hM_lb, c, hc_err⟩ := hN n hn
  refine ⟨M, hM_lb, c, fun m => ?_⟩
  -- TV bound: |errorProbAt(W_smooth δ) - errorProbAt(W)| ≤ 2 n δ.
  have h_tv := errorProbAt_smooth_TV c W hδ_pos.le hδ_le m
  -- Extract: errorProbAt(W) ≤ errorProbAt(W_smooth δ) + 2 n δ.
  have h_W_le :
      (c.errorProbAt W m).toReal
        ≤ (c.errorProbAt (Channel.smooth W δ) m).toReal + 2 * (n : ℝ) * δ := by
    have := (abs_le.mp h_tv).1
    linarith
  -- Glue: errorProbAt(W) ≤ ε/2 + ε/2 = ε.
  linarith [hc_err m]

end InformationTheory.Shannon.ChannelCoding
