import Common2026.Shannon.Entropy

/-!
# Pi 値 RV の reshape plumbing — `MeasurableEquiv` による entropy / condEntropy 不変性

5 本のムーンショット (Loomis–Whitney / Slepian–Wolf / AEP / Stein / Polymatroid) で
共通して使われる、Pi 値確率変数の `MeasurableEquiv` 押し出し不変性を集約したファイル。

Han Phase B / Phase D で `Han.lean` 内に育っていた 2 補題を上流に上げ、後続
moonshot からも見えるようにする。判断根拠: [`docs/shannon/pi-refactor-decision.md`](../../docs/shannon/pi-refactor-decision.md)。

## 主要補題

* `entropy_measurableEquiv_comp` ─ `entropy μ (e ∘ X) = entropy μ X` for `e : β ≃ᵐ γ`
* `condEntropy_measurableEquiv_comp` ─ conditioner 側 `MeasurableEquiv` reshape で
  `condEntropy μ Xc (e ∘ Yo) = condEntropy μ Xc Yo`

これらは pi 値索引の組み替え (`MeasurableEquiv.piCongrLeft` /
`MeasurableEquiv.sumPiEquivProdPi` / `MeasurableEquiv.funUnique` などの Mathlib
標準同型) と組み合わせて `Fin n → α` ↔ `α × (Fin n → α)` ↔ `(↥S → α)` のような
reshape を entropy 等式に持ち上げるために使う。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- entropy is invariant under push-forward by a `MeasurableEquiv`. Helper for the
`Fin (n+1) → α` ↔ `α × (Fin n → α)` reshape used in the chain-rule induction. -/
lemma entropy_measurableEquiv_comp
    {β γ : Type*}
    [Fintype β] [DecidableEq β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure Ω) (Xs : Ω → β) (hXs : Measurable Xs) (e : β ≃ᵐ γ) :
    entropy μ (fun ω => e (Xs ω)) = entropy μ Xs := by
  unfold entropy
  refine (Fintype.sum_equiv e.toEquiv
    (fun x => Real.negMulLog ((μ.map Xs).real {x}))
    (fun y => Real.negMulLog ((μ.map (fun ω => e (Xs ω))).real {y}))
    ?_).symm
  intro x
  have hpre : (e : β → γ) ⁻¹' {e x} = {x} := by
    ext y
    simp [Set.mem_preimage, Set.mem_singleton_iff, e.injective.eq_iff, eq_comm]
  show Real.negMulLog ((μ.map Xs).real {x})
      = Real.negMulLog ((μ.map (fun ω => e (Xs ω))).real {(e.toEquiv x : γ)})
  congr 1
  rw [show (e.toEquiv x : γ) = e x from rfl,
      show (fun ω => e (Xs ω)) = (e : β → γ) ∘ Xs from rfl,
      ← Measure.map_map e.measurable hXs,
      measureReal_def, measureReal_def,
      Measure.map_apply e.measurable (measurableSet_singleton _),
      hpre]

/-- conditioner side reshape: condEntropy is invariant under push-forward by
a `MeasurableEquiv` on the conditioner. Reduces to two applications of
`entropy_measurableEquiv_comp` via the H(Y,X) = H(Y) + H(X|Y) identity. -/
lemma condEntropy_measurableEquiv_comp
    {β γ : Type*}
    [Fintype β] [DecidableEq β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xc : Ω → α) (hXc : Measurable Xc)
    (Yo : Ω → β) (hYo : Measurable Yo) (e : β ≃ᵐ γ) :
    InformationTheory.MeasureFano.condEntropy μ Xc (fun ω => e (Yo ω))
      = InformationTheory.MeasureFano.condEntropy μ Xc Yo := by
  -- H(Yo, Xc) = H(Yo) + H(Xc | Yo)
  have h₁ := entropy_pair_eq_entropy_add_condEntropy μ Yo Xc hYo hXc
  -- H(e∘Yo, Xc) = H(e∘Yo) + H(Xc | e∘Yo)
  have h₂ := entropy_pair_eq_entropy_add_condEntropy μ
    (fun ω => e (Yo ω)) Xc (e.measurable.comp hYo) hXc
  -- H(e∘Yo) = H(Yo)
  have hY := entropy_measurableEquiv_comp μ Yo hYo e
  -- H(e∘Yo, Xc) = H(Yo, Xc) via the prod equiv (e × refl α)
  have hYX :
      entropy μ (fun ω => (e (Yo ω), Xc ω))
        = entropy μ (fun ω => (Yo ω, Xc ω)) := by
    have := entropy_measurableEquiv_comp μ
      (fun ω => (Yo ω, Xc ω)) (hYo.prodMk hXc)
      (MeasurableEquiv.prodCongr e (.refl α))
    simpa using this
  linarith

end InformationTheory.Shannon
