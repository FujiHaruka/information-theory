import Common2026.Shannon.ChannelCodingShannonTheorem
import Common2026.Shannon.ChannelCodingShannonTheoremGeneral
import Common2026.Shannon.AEPRate

/-!
# Shannon noisy channel coding theorem — `hW_pos` 完全除去 (D-1'' Phase D)

[D-1'' ムーンショット plan](../../../docs/shannon/channel-coding-shannon-theorem-general-plan.md)
の最終目標: 親 D-1 `shannon_noisy_channel_coding_theorem`
(`ChannelCodingShannonTheorem.lean:838`、`hW_pos` 必須) を、Phase A-C で publish 済の
smoothing infrastructure (`Channel.smooth W δ`, `errorProbAt_smooth_TV`) と
D-1'' Step 1 で publish 済の AEP rate-uniform 化 (`typicalSet_prob_ge_of_rate`) を組み合わせ、
`hW_pos` 仮定を完全に除去する。

## Approach

1. `exists_smooth_capacity_gt W hR` で `(p₀, δ_B ∈ (0, 1], R < I(p₀; W_smooth δ_B))` を取得。
2. 各 `n ≥ N` で `δ_n := min(δ_B, ε/(8(n+1)))` を選ぶ → `2 n δ_n < ε/4`。
3. `W_smooth δ_n` は full support (`Channel.smooth_pos hδ_n_pos hδ_n_le_1`)。
4. 親 D-1 を `(W_smooth δ_n, R, ε/4)` で再 call、`(N_n, M_n, c_n)` を取得。
5. TV bound: `errorProbAt W ≤ errorProbAt (W_smooth δ_n) + 2 n δ_n < ε/4 + ε/4 < ε`. ✓

## 撤退ライン

本ファイルの主定理 `shannon_noisy_channel_coding_theorem_general` は親 D-1 の `N(δ)` が
`δ ∈ (0, δ_B]` 上で **n-uniform** にできることに依存する。これは親 D-1 内部の
`channel_coding_achievability` (`ChannelCodingAchievability.lean:1771, 1835` の
`Tendsto.metric_atTop` extraction) を closed-form bound に書き直す **parent surgery** を要し、
本シードでは Step 1 完成 + Phase D 主定理 statement で sorry 保留。

D-1'' 完結 (Phase D 主定理 0 sorry) は parent surgery (200-400 行) を後続シードに deferred。
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- **D-1'' Phase D 主定理**: `hW_pos` 完全除去版 Shannon noisy channel coding theorem。
任意の `IsMarkovKernel W` (0-prob atom を許容) で、`R < capacity W` ならば、十分大きな block 長
`n` で max error < ε を達成する `M ≥ exp(n R)` 個の符号が存在する。

**現状 (本シード)**: `sorry` 保留。閉じるには親 D-1 の `N(δ)` を `δ ∈ (0, δ_B]` 上で
**uniform に bound** する parent surgery が必要 (`channel_coding_achievability` の AEP +
exp-decay の closed-form 化、~200-400 行)。

本シードは D-1'' Step 1 (AEP rate-uniform、`typicalSet_prob_ge_of_rate`) + Phase A-C
(`ChannelCodingShannonTheoremGeneral.lean`、smoothing + TV bound) のみ完成。

詳細は plan 判断ログ 6 を参照。 -/
theorem shannon_noisy_channel_coding_theorem_general
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR_pos : 0 < R) (hR : R < capacity W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        ∀ m, (c.errorProbAt W m).toReal < ε := by
  -- See module docstring: the proof requires parent surgery into
  -- `channel_coding_achievability` (`ChannelCodingAchievability.lean:1771, :1835`) to obtain
  -- a `δ ∈ (0, δ_B]`-uniform `N`. D-1'' Step 1 (`typicalSet_prob_ge_of_rate`) supplies the
  -- AEP rate-uniform bound needed by the surgery. The Phase A-C smoothing infrastructure
  -- supplies `δ_B` and the TV bound `errorProbAt_smooth_TV : |Δ| ≤ 2 n δ`.
  --
  -- This `sorry` is retained as the D-1'' Phase D placeholder; closing it is a separate
  -- ~200-400 line moonshot seed (parent surgery).
  sorry

end InformationTheory.Shannon.ChannelCoding
