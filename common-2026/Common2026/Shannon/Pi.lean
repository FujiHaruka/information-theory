import Common2026.Shannon.Entropy

/-!
# Shannon 共通土台 — Pi 値 reshape + 基本 plumbing

5 本のムーンショット (Loomis–Whitney / Slepian–Wolf / AEP / Stein / Polymatroid) で
共通して使われる、Pi 値確率変数の `MeasurableEquiv` 押し出し不変性および
`condEntropy ≥ 0` の基本不等式を集約したファイル。

Han Phase B / Phase D で `Han.lean` / `HanD.lean` / `SlepianWolf.lean` 内に育っていた
補題群を上流に上げ、後続 moonshot からも見えるようにする。判断根拠:
[`docs/shannon/pi-refactor-decision.md`](../../docs/shannon/pi-refactor-decision.md)。

## 主要補題

* `entropy_measurableEquiv_comp` ─ `entropy μ (e ∘ X) = entropy μ X` for `e : β ≃ᵐ γ`
* `condEntropy_measurableEquiv_comp` ─ conditioner 側 `MeasurableEquiv` reshape で
  `condEntropy μ Xc (e ∘ Yo) = condEntropy μ Xc Yo`
* `condEntropy_nonneg` ─ `0 ≤ H(W | Y)` (probability measure 上)
* `subsetIdxEquiv` ─ `T₁ ⊆ T₂` のとき索引同型 `(↥T₁ ⊕ ↥(T₂ \ T₁)) ≃ ↥T₂`
* `subsetSplitMEquiv` ─ pi 値版 `((↥T₁ → α) × (↥(T₂\T₁) → α)) ≃ᵐ (↥T₂ → α)`
* `subsetSplitMEquiv_apply` ─ 共通生成 `Xs` の制限張り合わせ

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

/-! ## condEntropy の基本不等式 -/

/-- Conditional entropy is non-negative: `0 ≤ H(W | Y)`.
被積分関数 `∑ x, negMulLog (q.real {x})` は probability measure 上の負エントロピー和
(各項 ≥ 0)。 -/
theorem condEntropy_nonneg
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
      [MeasurableSpace W] [MeasurableSingletonClass W]
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Ws : Ω → W) (Yo : Ω → Y) :
    0 ≤ InformationTheory.MeasureFano.condEntropy μ Ws Yo := by
  unfold InformationTheory.MeasureFano.condEntropy
  refine integral_nonneg fun y => ?_
  refine Finset.sum_nonneg fun x _ => ?_
  exact Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one

/-! ## 部分集合 reshape 索引

`Finset (Fin n)` の subset 関係を pi 値型の `MeasurableEquiv` に持ち上げる plumbing。
Han Phase D / Polymatroid / (将来) Loomis–Whitney refinements で共有。 -/

/-- 索引同型 `↥T₁ ⊕ ↥(T₂ \ T₁) ≃ ↥T₂` (T₁ ⊆ T₂ のとき)。
`Equiv.Finset.union` だけでは `T₁ ∪ (T₂ \ T₁) = T₂` の cast が要るので直接構成。 -/
def subsetIdxEquiv {ι : Type*} [DecidableEq ι]
    {T₁ T₂ : Finset ι} (h : T₁ ⊆ T₂) :
    (↥T₁ ⊕ ↥(T₂ \ T₁)) ≃ ↥T₂ where
  toFun := Sum.elim
    (fun x => ⟨x.val, h x.property⟩)
    (fun x => ⟨x.val, (Finset.mem_sdiff.mp x.property).1⟩)
  invFun := fun ⟨i, hi⟩ =>
    if h₁ : i ∈ T₁ then Sum.inl ⟨i, h₁⟩
    else Sum.inr ⟨i, Finset.mem_sdiff.mpr ⟨hi, h₁⟩⟩
  left_inv := by
    rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · simp [hi]
    · have hni : i ∉ T₁ := (Finset.mem_sdiff.mp hi).2
      simp [hni]
  right_inv := by
    rintro ⟨i, hi⟩
    by_cases h₁ : i ∈ T₁
    · simp [h₁]
    · simp [h₁]

/-- Pi 値 `(↥T₂ → α) ≃ᵐ (↥T₁ → α) × (↥(T₂\T₁) → α)` (T₁ ⊆ T₂)。
`subsetIdxEquiv` を `MeasurableEquiv.piCongrLeft` で持ち上げ、
`sumPiEquivProdPi` で sum を product に直す。 -/
def subsetSplitMEquiv {n : ℕ} {T₁ T₂ : Finset (Fin n)} (h : T₁ ⊆ T₂) :
    ((↥T₁ → α) × (↥(T₂ \ T₁) → α)) ≃ᵐ (↥T₂ → α) :=
  ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : ↥T₁ ⊕ ↥(T₂ \ T₁) => α)).symm).trans
    (MeasurableEquiv.piCongrLeft (fun _ : ↥T₂ => α) (subsetIdxEquiv h))

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- subsetSplitMEquiv が、共通生成 `Xs : Fin n → α` の T₁/T₂\T₁ 制限を
T₂ 制限に貼り合わせる。これが reshape の中身。 -/
lemma subsetSplitMEquiv_apply
    {n : ℕ} {T₁ T₂ : Finset (Fin n)} (h : T₁ ⊆ T₂) (Xs : Fin n → α) :
    subsetSplitMEquiv (α := α) h
      (fun j : ↥T₁ => Xs j.val, fun j : ↥(T₂ \ T₁) => Xs j.val)
      = fun j : ↥T₂ => Xs j.val := by
  funext k
  obtain ⟨j, hj⟩ := k
  -- (subsetIdxEquiv h).symm ⟨j, hj⟩ で場合分け
  have hk : (⟨j, hj⟩ : ↥T₂)
      = (subsetIdxEquiv h) ((subsetIdxEquiv h).symm ⟨j, hj⟩) :=
    ((subsetIdxEquiv h).apply_symm_apply ⟨j, hj⟩).symm
  conv_lhs => rw [show (⟨j, hj⟩ : ↥T₂)
      = (subsetIdxEquiv h) ((subsetIdxEquiv h).symm ⟨j, hj⟩)
    from hk]
  -- subsetSplitMEquiv = sumPiEquivProdPi.symm.trans (piCongrLeft _ subsetIdxEquiv)
  -- 中の関数が Sum.elim ... なので piCongrLeft_apply_apply で展開
  show MeasurableEquiv.piCongrLeft (fun _ : ↥T₂ => α) (subsetIdxEquiv h)
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : ↥T₁ ⊕ ↥(T₂ \ T₁) => α)).symm
        (fun j : ↥T₁ => Xs j.val, fun j : ↥(T₂ \ T₁) => Xs j.val))
      ((subsetIdxEquiv h) ((subsetIdxEquiv h).symm ⟨j, hj⟩))
    = Xs j
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  -- (sumPiEquivProdPi).symm (f, g) = Sum.elim f g
  by_cases h₁ : j ∈ T₁
  · -- inl branch
    have hsymm : (subsetIdxEquiv h).symm ⟨j, hj⟩ = Sum.inl ⟨j, h₁⟩ := by
      simp [subsetIdxEquiv, h₁]
    rw [hsymm]
    rfl
  · -- inr branch
    have hsymm : (subsetIdxEquiv h).symm ⟨j, hj⟩
        = Sum.inr ⟨j, Finset.mem_sdiff.mpr ⟨hj, h₁⟩⟩ := by
      simp [subsetIdxEquiv, h₁]
    rw [hsymm]
    rfl

end InformationTheory.Shannon
