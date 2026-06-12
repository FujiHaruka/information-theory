import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Main

/-!
# T2-A F-1 discharge: AWGN kernel measurability

Cover-Thomas Ch.9 AWGN channel coding theorem の **撤退ライン F-1 (kernel
measurability) を discharge** した形で `awgn_channel_coding_theorem` を再 publish。

## 撤退ラインの位置づけ

親 plan `awgn-moonshot-plan.md` §撤退ライン F-4 (= 本 plan / seed の F-1) は
`Measurable (fun x : ℝ => gaussianReal x N)` の hypothesis pass-through。

本 file ではこの述語 `IsAwgnChannelMeasurable N` を **Mathlib の `gaussianReal_map_const_add`**
(`Mathlib/Probability/Distributions/Gaussian/Real.lean:292`) と **Giry monad の構造的
measurability** (`Measure.measurable_of_measurable_coe` + `Measure.measurable_measure_prodMk_left`)
で完全証明する (`isAwgnChannelMeasurable`)。

discharge 後、`awgn_channel_coding_theorem` を `h_meas` 引数なし形で再 publish
(`awgn_theorem_F1_discharged`)。`awgn_capacity_closed_form` も同様に再 publish。

## Approach

```
gaussianReal x N
  = gaussianReal (0 + x) N                  -- `zero_add`
  = (gaussianReal 0 N).map (x + ·)          -- `gaussianReal_map_const_add` (μ=0)
```

すなわち、`x` をパラメータとする `gaussianReal x N` は「固定の `gaussianReal 0 N` を
shift する map」として書ける。Map measurability は Giry monad の `measurable_of_measurable_coe`
+ `Measure.measurable_measure_prodMk_left` で自動。

詳細は `docs/shannon/awgn-f1-discharge-moonshot-plan.md` 参照。
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Phase A — `isAwgnChannelMeasurable` discharge -/

/-- Auxiliary equality: `gaussianReal x N = (gaussianReal 0 N).map (x + ·)`.
特殊化 `μ = 0` of `gaussianReal_map_const_add` (`Mathlib`). -/
lemma gaussianReal_eq_zero_map (x : ℝ) (N : ℝ≥0) :
    gaussianReal x N = (gaussianReal 0 N).map (x + ·) := by
  rw [gaussianReal_map_const_add x, zero_add]

/-- **AWGN kernel measurability** (撤退ライン F-1 / 親 plan F-4 の discharge).

`fun x : ℝ ↦ gaussianReal x N` は Giry monad 上 measurable。証明は
`gaussianReal x N = (gaussianReal 0 N).map (x + ·)` (= mean shift) と
`Measure.measurable_measure_prodMk_left` の組合せ。

`IsAwgnChannelMeasurable N` 述語の Mathlib 直接 discharge を与え、
`awgn_channel_coding_theorem` の `h_meas` 引数を本補題で埋められるようにする。 -/
@[entry_point]
theorem isAwgnChannelMeasurable (N : ℝ≥0) : IsAwgnChannelMeasurable N := by
  unfold IsAwgnChannelMeasurable
  -- 関数等式 `fun x => gaussianReal x N = fun x => (gaussianReal 0 N).map (x + ·)`
  have h_fun_eq :
      (fun x : ℝ => gaussianReal x N)
        = (fun x : ℝ => (gaussianReal 0 N).map (x + ·)) := by
    funext x
    exact gaussianReal_eq_zero_map x N
  rw [h_fun_eq]
  -- Giry monad の measurability 判定: ∀ s, ms s → Measurable (fun x ↦ μ.map (x+·) s)
  refine Measure.measurable_of_measurable_coe _ ?_
  intro s hs
  -- `MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ∈ s}` (continuous addition の Borel preimage)
  have h_meas_add : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ∈ s} :=
    (measurable_fst.add measurable_snd) hs
  -- 関数等式: ∀ x, (gaussianReal 0 N).map (x + ·) s
  --              = (gaussianReal 0 N) (Prod.mk x ⁻¹' {p | p.1 + p.2 ∈ s})
  have h_apply_eq :
      (fun x : ℝ => ((gaussianReal 0 N).map (x + ·)) s)
        = (fun x : ℝ => (gaussianReal 0 N)
            (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 + p.2 ∈ s})) := by
    funext x
    have h_meas_x : Measurable (x + · : ℝ → ℝ) :=
      measurable_const.add measurable_id
    rw [Measure.map_apply h_meas_x hs]
    -- (x + ·) ⁻¹' s = Prod.mk x ⁻¹' {p | p.1 + p.2 ∈ s}
    rfl
  rw [h_apply_eq]
  exact measurable_measure_prodMk_left h_meas_add

/-! ## Phase B — `awgn_theorem_F1_discharged` + capacity 再 publish (F-1 discharge 形) -/

/-- **AWGN channel coding theorem** (F-1 discharge 形).

親定理 `awgn_channel_coding_theorem` (`AWGNMain.lean`) の `h_meas`
(= `IsAwgnChannelMeasurable N`) を本 file の `isAwgnChannelMeasurable N` で埋めて
再 publish。signature から `h_meas` が消える。

F-2 MI bridge (`h_mi_bridge`) hypothesis は body 未参照の dead hyp だったため
2026-06-12 cleanup で signature から除去済 (F-2 自体は genuine closure 済、
`awgn-mi-bridge-plan` closed)。
2026-05-27 F-1/F-3 peer migration: 旧 `h_typicality` / `h_converse` 引数は、
`IsAwgnTypicalityHypothesis` / `IsAwgnConverseHypothesis` predicate 削除に
伴い削除済 (F-1 / F-3 body は `awgn_achievability` / `awgn_converse` の sorry
として `awgn-achievability-typicality-plan` / `awgn-converse-aux-plan` に
defer)。

`@audit:closed-by-successor(awgn-moonshot-plan)`

@audit:ok (independent honesty audit 2026-06-12, commit e728ebf: `h_mi_bridge`
removed from signature. Pure strengthening — the parent `awgn_channel_coding_theorem`
never consumed `h_mi_bridge` in its body, so this wrapper's old `h_mi_bridge`
pass-through was dead. Post-removal body delegates to `awgn_channel_coding_theorem`
(itself a sorryAx-free pass-through of `awgn_achievability`); conclusion follows
verbatim. `#print axioms awgn_theorem_F1_discharged` = `[propext, Classical.choice,
Quot.sound]` re-confirmed by this audit.) -/
@[entry_point]
theorem awgn_theorem_F1_discharged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    {R : ℝ} (hR_pos : 0 < R) (hR_lt_C : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : AwgnCode M n P),
          ∀ m, (c.toCode.errorProbAt
                  (awgnChannel N (isAwgnChannelMeasurable N)) m).toReal < ε :=
  awgn_channel_coding_theorem P hP N hN (isAwgnChannelMeasurable N)
    hR_pos hR_lt_C hε

/-- **AWGN capacity closed form** (F-1 discharge 形).

親 corollary `awgn_capacity_closed_form` の `h_meas` を `isAwgnChannelMeasurable N` で
埋めて再 publish。残りの F-2 系 hypothesis (`h_bridge_gauss` / `h_bdd` / `h_max_ent`)
はそのまま。

`@audit:closed-by-successor(awgn-mi-bridge-plan)` -/
@[entry_point]
theorem awgn_capacity_closed_form_F1_discharged
    (P : ℝ) (hP : 0 ≤ P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_bridge_gauss :
        (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
            (gaussianReal 0 P.toNNReal)
            (awgnChannel N (isAwgnChannelMeasurable N))).toReal
          = (1/2) * Real.log (1 + P / (N : ℝ)))
    (h_bdd :
        BddAbove ((fun p : Measure ℝ =>
            (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
                p (awgnChannel N (isAwgnChannelMeasurable N))).toReal) ''
          awgnPowerConstraintSet P))
    (h_max_ent :
        ∀ p ∈ awgnPowerConstraintSet P,
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (awgnChannel N (isAwgnChannelMeasurable N))).toReal
            ≤ (1/2) * Real.log (1 + P / (N : ℝ))) :
    awgnCapacity P N (isAwgnChannelMeasurable N)
      = (1/2) * Real.log (1 + P / (N : ℝ)) :=
  awgn_capacity_closed_form P hP N hN (isAwgnChannelMeasurable N)
    h_bridge_gauss h_bdd h_max_ent

end InformationTheory.Shannon.AWGN
