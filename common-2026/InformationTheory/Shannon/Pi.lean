import InformationTheory.Shannon.Entropy

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
* `MeasurableEquiv.coe_piFinsetUnion` / `_apply_left` / `_apply_right` ─ Mathlib
  `Equiv.piFinsetUnion_left/_right` を `MeasurableEquiv.piFinsetUnion` 版に持ち上げる
  薄いブリッジ
* `subsetSplitMEquivAux` ─ disjoint 形 `Disjoint T₁ R + T₁ ∪ R = U` 入力の Pi reshape
  `((↥T₁ → α) × (↥R → α)) ≃ᵐ (↥U → α)` (Mathlib `MeasurableEquiv.piFinsetUnion` +
  `MeasurableEquiv.cast` の薄い合成)。subset 形 `T₁ ⊆ T₂` の call site は
  `Finset.disjoint_sdiff` + `Finset.union_sdiff_of_subset` を inline で渡す。

これらは pi 値索引の組み替え (`MeasurableEquiv.piCongrLeft` /
`MeasurableEquiv.sumPiEquivProdPi` / `MeasurableEquiv.piFinsetUnion` などの Mathlib
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
Han Phase D / Polymatroid / (将来) Loomis–Whitney refinements で共有。

内部実装は Mathlib `MeasurableEquiv.piFinsetUnion`
(`Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`) を `Finset.disjoint_sdiff`
+ `Finset.union_sdiff_of_subset` で subset-form に持ち上げる薄いラッパー。 -/

/-- The coe of `MeasurableEquiv.piFinsetUnion` is defeq the underlying
`Equiv.piFinsetUnion`. Lifts pointwise apply lemmas (`Equiv.piFinsetUnion_left/_right`)
into the `MeasurableEquiv` namespace. -/
@[simp] lemma _root_.MeasurableEquiv.coe_piFinsetUnion
    {ι : Type*} [DecidableEq ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {s t : Finset ι} (h : Disjoint s t) :
    ⇑(MeasurableEquiv.piFinsetUnion (π := β) h) = Equiv.piFinsetUnion β h := rfl

/-- pointwise apply (`s` branch) for `MeasurableEquiv.piFinsetUnion`. -/
lemma _root_.MeasurableEquiv.piFinsetUnion_apply_left
    {ι : Type*} [DecidableEq ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {s t : Finset ι} (h : Disjoint s t)
    {f : ∀ i : s, β i} {g : ∀ i : t, β i}
    {i : ι} (hi : i ∈ s) (hi' : i ∈ s ∪ t) :
    MeasurableEquiv.piFinsetUnion (π := β) h (f, g) ⟨i, hi'⟩ = f ⟨i, hi⟩ := by
  rw [MeasurableEquiv.coe_piFinsetUnion]
  exact Equiv.piFinsetUnion_left β h hi hi'

/-- pointwise apply (`t` branch) for `MeasurableEquiv.piFinsetUnion`. -/
lemma _root_.MeasurableEquiv.piFinsetUnion_apply_right
    {ι : Type*} [DecidableEq ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {s t : Finset ι} (h : Disjoint s t)
    {f : ∀ i : s, β i} {g : ∀ i : t, β i}
    {i : ι} (hi : i ∈ t) (hi' : i ∈ s ∪ t) :
    MeasurableEquiv.piFinsetUnion (π := β) h (f, g) ⟨i, hi'⟩ = g ⟨i, hi⟩ := by
  rw [MeasurableEquiv.coe_piFinsetUnion]
  exact Equiv.piFinsetUnion_right β h hi hi'

/-- Pi 値 `((↥T₁ → α) × (↥R → α)) ≃ᵐ (↥U → α)` for any `T₁, R, U : Finset ι` with
`Disjoint T₁ R` and `T₁ ∪ R = U`. Mathlib `MeasurableEquiv.piFinsetUnion` post-composed
with `MeasurableEquiv.cast` of the union equation. -/
def subsetSplitMEquivAux {ι : Type*} [DecidableEq ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] {T₁ R U : Finset ι}
    (hd : Disjoint T₁ R) (hU : T₁ ∪ R = U) :
    (((i : T₁) → β i) × ((i : R) → β i)) ≃ᵐ ((i : U) → β i) :=
  (MeasurableEquiv.piFinsetUnion (π := β) hd).trans
    (MeasurableEquiv.cast (by rw [hU]) (by rw [hU]))

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- pointwise apply for `subsetSplitMEquivAux` on the canonical split of a global function. -/
lemma subsetSplitMEquivAux_apply
    {n : ℕ} {T₁ R U : Finset (Fin n)}
    (hd : Disjoint T₁ R) (hU : T₁ ∪ R = U) (Xs : Fin n → α) :
    subsetSplitMEquivAux (β := fun _ : Fin n => α) hd hU
      (fun j : ↥T₁ => Xs j.val, fun j : ↥R => Xs j.val)
      = fun j : ↥U => Xs j.val := by
  subst hU
  funext k
  obtain ⟨j, hj⟩ := k
  show ((MeasurableEquiv.piFinsetUnion (π := fun _ : Fin n => α) hd).trans
      (MeasurableEquiv.cast rfl HEq.rfl)
      (fun j : ↥T₁ => Xs j.val, fun j : ↥R => Xs j.val)) ⟨j, hj⟩ = Xs j
  -- The cast over `rfl` is the identity on values.
  by_cases hjT₁ : j ∈ T₁
  · exact MeasurableEquiv.piFinsetUnion_apply_left
      (β := fun _ : Fin n => α) hd hjT₁ hj
  · have hjR : j ∈ R := (Finset.mem_union.mp hj).resolve_left hjT₁
    exact MeasurableEquiv.piFinsetUnion_apply_right
      (β := fun _ : Fin n => α) hd hjR hj

end InformationTheory.Shannon
