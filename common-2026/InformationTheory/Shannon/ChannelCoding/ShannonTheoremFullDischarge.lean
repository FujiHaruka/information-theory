import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.ShannonTheorem
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremGeneral
import InformationTheory.Shannon.IIDProductInput.Basic
import InformationTheory.Shannon.AEP.Rate
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremFullDischarge.SeedLemmas
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremFullDischarge.PmfLogBounds
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremFullDischarge.SmoothInstantiation
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremFullDischarge.OuterN
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# D-1'' Phase D — parent surgery (umbrella)

[D-1'' ムーンショット plan](../../../docs/shannon/channel-coding-shannon-theorem-general-plan.md)
の parent surgery 全体の umbrella モジュール。本体補題群は part ファイルへ分割済:

* `ShannonTheoremFullDischarge/SeedLemmas.lean` — Phase D.0 / D.0'
* `ShannonTheoremFullDischarge/PmfLogBounds.lean` — Phase D.1
* `ShannonTheoremFullDischarge/SmoothInstantiation.lean` — Phase D.2
* `ShannonTheoremFullDischarge/OuterN.lean` — Phase D.3

本ファイルには Phase D.4 の主定理
`shannon_noisy_channel_coding_theorem_general_full` のみを残す。
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ## Phase D.4 — main theorem (Shannon noisy channel coding, fully discharged) -/

/-- **D-1'' Phase D 主定理 (full discharge)**: `R < capacity W` で任意 `ε > 0` に対し
十分大きい `n` で max-error < ε を達成する `M ≥ ⌈exp(nR)⌉` 個の符号が存在。
`hW_pos` 完全除去版。 -/
@[entry_point]
theorem shannon_noisy_channel_coding_theorem_general_full
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR_pos : 0 < R) (hR : R < capacity W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        ∀ m, (c.errorProbAt W m).toReal < ε := by
  obtain ⟨N, hN⟩ := exists_N_for_smooth_achievability_uniform W hR_pos hR hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨δ, hδ_pos, hδ_le, h_tv_bd, M, hM_lb, c, hc_err⟩ := hN n hn
  refine ⟨M, hM_lb, c, fun m => ?_⟩
  -- TV bound: |errorProbAt(W_smooth δ) - errorProbAt(W)| ≤ 2 n δ.
  have h_tv := errorProbAt_smooth_TV c W hδ_pos.le hδ_le m
  have h_W_le :
      (c.errorProbAt W m).toReal
        ≤ (c.errorProbAt (Channel.smooth W δ) m).toReal + 2 * (n : ℝ) * δ := by
    have := (abs_le.mp h_tv).1
    linarith
  linarith [hc_err m]

end InformationTheory.Shannon.ChannelCoding
