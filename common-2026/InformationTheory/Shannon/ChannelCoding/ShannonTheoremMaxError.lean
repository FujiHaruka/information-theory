import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.ShannonTheorem
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremGeneral
import InformationTheory.Shannon.IIDProductInput.Basic
import InformationTheory.Shannon.AEP.Rate
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremMaxError.SeedLemmas
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremMaxError.PmfLogBounds
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremMaxError.SmoothInstantiation
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremMaxError.OuterN
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Shannon noisy channel coding theorem — max-error achievability (umbrella)

Umbrella module for the max-error form of the Shannon noisy channel coding theorem.
Supporting lemmas are split into part files:

* `ShannonTheoremMaxError/SeedLemmas.lean` — smooth input distribution and
  capacity lower bound construction.
* `ShannonTheoremMaxError/PmfLogBounds.lean` — closed-form pmfLog variance bounds.
* `ShannonTheoremMaxError/SmoothInstantiation.lean` — achievability at the smooth
  channel with explicit `N` formula.
* `ShannonTheoremMaxError/OuterN.lean` — outer `N` construction combining TV bound
  and smooth achievability.

This file contains only the main theorem
`shannon_noisy_channel_coding_theorem_general_full`.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ## Main theorem -/

omit [DecidableEq α] [DecidableEq β] in
/-- **Shannon noisy channel coding theorem (max-error achievability)**: for `R < capacity W`
and any `ε > 0`, there exists `N` such that for all `n ≥ N` there is a code with
`M ≥ ⌈exp(nR)⌉` codewords achieving max-error less than `ε`. -/
@[entry_point]
theorem shannon_noisy_channel_coding_theorem_general_full
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR_pos : 0 < R) (hR : R < capacity W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        ∀ m, (c.errorProbAt W m).toReal < ε := by
  classical
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
