import Common2026.Shannon.Han

/-!
# Han Phase D: subset 版 joint entropy infrastructure (skeleton)

Han Phase D ロードマップ ([`docs/han-phase-d-plan.md`](../../../docs/han-phase-d-plan.md))
の Phase A skeleton。`Fin n` の任意部分集合 `S : Finset (Fin n)` に対する
joint entropy `H(X_S)` を定義し、Phase B (D-1 subset average chain) /
Phase C (D-2 Shearer) の入口となる 4 主定理を sorry-driven で並べる。

## 主要定義・主定理

* `jointEntropySubset μ Xs S` ─ `(i : ↑S) → α` 値の joint entropy。
* `jointEntropySubset_univ` ─ `S = univ` で `jointEntropy μ Xs` に一致。
* `jointEntropySubset_chain_rule` ─ subset 版 chain rule。
* `condEntropy_subset_anti` ─ subset 版 conditioning monotonicity (`T₁ ⊆ T₂ ⟹` 条件側を増やすと減る)。
* `han_inequality_subset` ─ Han の不等式の subset 版。`han_inequality` を `Finset.orderEmbOfFin S` で
  restrict し reshape する見込み。

## 戦略 (inventory より)

* Pi 値 instance (`Fintype`, `MeasurableSpace`, `MeasurableSingletonClass`,
  `Nonempty`, `DecidableEq`) は `Han.lean` の `{j // j ≠ i}` 前例から自動発火見込み
  (inventory 軸 (c))。
* `jointEntropySubset_chain_rule` / `condEntropy_subset_anti` は
  `Finset.induction_on` で `S` を 1 元ずつ拡張、Phase A/B の写経再利用。
* `han_inequality_subset` は `Finset.orderEmbOfFin S rfl : Fin S.card ↪o Fin n`
  経由で既存 `han_inequality` を適用、両辺を `entropy_measurableEquiv_comp` +
  `MeasurableEquiv.piCongrLeft` で reshape (inventory 軸 (d), 50〜70 行見積もり)。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {n : ℕ}
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Pi reshape plumbing -/

/-- 索引同型 `↥T₁ ⊕ ↥(T₂ \ T₁) ≃ ↥T₂` (T₁ ⊆ T₂ のとき)。
`Equiv.Finset.union` だけでは `T₁ ∪ (T₂ \ T₁) = T₂` の cast が要るので直接構成。 -/
private def subsetIdxEquiv {ι : Type*} [DecidableEq ι]
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
private def subsetSplitMEquiv {T₁ T₂ : Finset (Fin n)} (h : T₁ ⊆ T₂) :
    ((↥T₁ → α) × (↥(T₂ \ T₁) → α)) ≃ᵐ (↥T₂ → α) :=
  ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : ↥T₁ ⊕ ↥(T₂ \ T₁) => α)).symm).trans
    (MeasurableEquiv.piCongrLeft (fun _ : ↥T₂ => α) (subsetIdxEquiv h))

/-- subsetSplitMEquiv が、共通生成 `Xs : Fin n → α` の T₁/T₂\T₁ 制限を
T₂ 制限に貼り合わせる。これが reshape の中身。 -/
private lemma subsetSplitMEquiv_apply
    {T₁ T₂ : Finset (Fin n)} (h : T₁ ⊆ T₂) (Xs : Fin n → α) :
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

/-- 部分集合 `S : Finset (Fin n)` 上の joint entropy。
`(i : ↑S) → α` 値の random variable のエントロピー。 -/
noncomputable def jointEntropySubset
    (μ : Measure Ω) (Xs : Fin n → Ω → α) (S : Finset (Fin n)) : ℝ :=
  entropy μ (fun ω (i : S) => Xs i.val ω)

/-- `S = Finset.univ` のとき subset 版は通常の `jointEntropy` に一致。 -/
theorem jointEntropySubset_univ
    (μ : Measure Ω) (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
    jointEntropySubset μ Xs Finset.univ = jointEntropy μ Xs := by
  -- 索引の同型 `↥(Finset.univ : Finset (Fin n)) ≃ Fin n`。
  let idxEquiv : ↥(Finset.univ : Finset (Fin n)) ≃ Fin n :=
    { toFun := Subtype.val
      invFun := fun i => ⟨i, Finset.mem_univ i⟩
      left_inv := by rintro ⟨_, _⟩; rfl
      right_inv := fun _ => rfl }
  -- piCongrLeft で `(↥univ → α) ≃ᵐ (Fin n → α)` を構成。
  let e : (↥(Finset.univ : Finset (Fin n)) → α) ≃ᵐ (Fin n → α) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => α) idxEquiv
  -- subset 側 RV の measurability
  have hXs_univ :
      Measurable (fun ω (j : ↥(Finset.univ : Finset (Fin n))) => Xs j.val ω) :=
    measurable_pi_iff.mpr (fun j => hXs j.val)
  -- entropy_measurableEquiv_comp : entropy μ (fun ω => e (Xs_univ ω)) = entropy μ Xs_univ
  have h := entropy_measurableEquiv_comp μ
    (fun ω (j : ↥(Finset.univ : Finset (Fin n))) => Xs j.val ω) hXs_univ e
  unfold jointEntropySubset jointEntropy
  rw [← h]
  congr 1

/-- subset 版 chain rule:
`H(X_S) = ∑ i ∈ S, H(X_i | X_{S ∩ {j : j < i}})`。

Phase A の `entropy_pair_eq_entropy_add_condEntropy` を `Finset.induction_on` で
`S` の各要素について反復適用する。 -/
theorem jointEntropySubset_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (S : Finset (Fin n)) :
    jointEntropySubset μ Xs S
      = ∑ i ∈ S,
          InformationTheory.MeasureFano.condEntropy μ (Xs i)
            (fun ω (j : (S.filter (· < i))) => Xs j.val ω) := by
  sorry

/-- subset 版 conditioning monotonicity:
`T₁ ⊆ T₂ ⟹ H(X_i | X_{T₂}) ≤ H(X_i | X_{T₁})`。

Phase A の `condEntropy_le_condEntropy_of_pair` を `T₂ \ T₁` の要素を
1 つずつ `T₁` に加える induction で繰り返す。 -/
theorem condEntropy_subset_anti
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (i : Fin n) {T₁ T₂ : Finset (Fin n)} (hT : T₁ ⊆ T₂) :
    InformationTheory.MeasureFano.condEntropy μ (Xs i)
        (fun ω (j : T₂) => Xs j.val ω)
      ≤ InformationTheory.MeasureFano.condEntropy μ (Xs i)
          (fun ω (j : T₁) => Xs j.val ω) := by
  -- Setup: T₂ への条件付けを (T₁, T₂\T₁) ペアに reshape し、
  -- condEntropy_le_condEntropy_of_pair で T₂\T₁ を捨てる。
  set XT₁ : Ω → (↥T₁ → α) := fun ω j => Xs j.val ω with hXT₁_def
  set XR : Ω → (↥(T₂ \ T₁) → α) := fun ω j => Xs j.val ω with hXR_def
  have hXT₁_meas : Measurable XT₁ :=
    measurable_pi_iff.mpr (fun _ => hXs _)
  have hXR_meas : Measurable XR :=
    measurable_pi_iff.mpr (fun _ => hXs _)
  -- Bridge: subsetSplitMEquiv ∘ (XT₁, XR) = XT₂
  let e := subsetSplitMEquiv (α := α) (n := n) hT
  have hbridge : (fun ω => e (XT₁ ω, XR ω))
      = fun ω (j : ↥T₂) => Xs j.val ω := by
    funext ω
    exact subsetSplitMEquiv_apply hT (fun k => Xs k ω)
  -- condEntropy μ (Xs i) XT₂ = condEntropy μ (Xs i) (e ∘ (XT₁, XR))
  --                          = condEntropy μ (Xs i) (XT₁, XR)        -- reshape
  have h_eq :
      InformationTheory.MeasureFano.condEntropy μ (Xs i)
          (fun ω (j : ↥T₂) => Xs j.val ω)
        = InformationTheory.MeasureFano.condEntropy μ (Xs i)
            (fun ω => (XT₁ ω, XR ω)) := by
    rw [← hbridge]
    exact condEntropy_measurableEquiv_comp μ (Xs i) (hXs i)
      (fun ω => (XT₁ ω, XR ω)) (hXT₁_meas.prodMk hXR_meas) e
  rw [h_eq]
  -- condEntropy_le_condEntropy_of_pair で R を捨てる
  exact condEntropy_le_condEntropy_of_pair μ (Xs i) XT₁ XR
    (hXs i) hXT₁_meas hXR_meas

/-- Han の不等式の subset 版:
`(|S| - 1) · H(X_S) ≤ ∑ i ∈ S, H(X_{S \ {i}})`。

`Finset.orderEmbOfFin S rfl : Fin S.card ↪o Fin n` で `S` を `Fin S.card` から
の埋め込みとみなし、`Xs' k ω := Xs (S.orderEmbOfFin rfl k) ω` に対して既存
`han_inequality` を適用、両辺を `jointEntropySubset` 形に reshape する。 -/
theorem han_inequality_subset
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (S : Finset (Fin n)) :
    ((S.card : ℝ) - 1) * jointEntropySubset μ Xs S
      ≤ ∑ i ∈ S, jointEntropySubset μ Xs (S.erase i) := by
  sorry

end InformationTheory.Shannon
