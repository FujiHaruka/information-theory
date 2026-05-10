import Common2026.Shannon.Han

/-!
# Han Phase D: subset 版 joint entropy infrastructure (skeleton)

Han Phase D ロードマップ ([`docs/han/han-phase-d-plan.md`](../../../docs/han/han-phase-d-plan.md))
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
def subsetSplitMEquiv {T₁ T₂ : Finset (Fin n)} (h : T₁ ⊆ T₂) :
    ((↥T₁ → α) × (↥(T₂ \ T₁) → α)) ≃ᵐ (↥T₂ → α) :=
  ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : ↥T₁ ⊕ ↥(T₂ \ T₁) => α)).symm).trans
    (MeasurableEquiv.piCongrLeft (fun _ : ↥T₂ => α) (subsetIdxEquiv h))

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- subsetSplitMEquiv が、共通生成 `Xs : Fin n → α` の T₁/T₂\T₁ 制限を
T₂ 制限に貼り合わせる。これが reshape の中身。 -/
lemma subsetSplitMEquiv_apply
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

/-- subset 版 chain rule の per-summand bridge:
`condEntropy μ (Xs (φ k)) (Fin k.val 形) = condEntropy μ (Xs (φ k)) (S.filter 形)`。

`Fin k.val ≃ ↥(S.filter (· < φ k))` を `(orderIsoOfFin S).symm` 経由で構成し、
`condEntropy_measurableEquiv_comp` で reshape。 -/
private lemma condEntropy_chainSummand_bridge
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (S : Finset (Fin n)) (k : Fin S.card) :
    InformationTheory.MeasureFano.condEntropy μ
        (Xs (S.orderEmbOfFin rfl k))
        (fun ω (j : Fin k.val) =>
          Xs (S.orderEmbOfFin rfl ⟨j.val, j.isLt.trans k.isLt⟩) ω)
      = InformationTheory.MeasureFano.condEntropy μ
          (Xs (S.orderEmbOfFin rfl k))
          (fun ω (j : ↥(S.filter (· < S.orderEmbOfFin rfl k))) => Xs j.val ω) := by
  set φ : Fin S.card ↪o Fin n := S.orderEmbOfFin rfl
  -- Index equiv `Fin k.val ≃ ↥(S.filter (· < φ k))` constructed via refine
  let idx : Fin k.val ≃ ↥(S.filter (· < φ k)) := by
    refine
      { toFun := fun j => ⟨φ ⟨j.val, j.isLt.trans k.isLt⟩, ?_⟩
        invFun := fun vh => ⟨((S.orderIsoOfFin rfl).symm
            ⟨vh.val, (Finset.mem_filter.mp vh.property).1⟩).val, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · rw [Finset.mem_filter]
      exact ⟨S.orderEmbOfFin_mem rfl _, φ.lt_iff_lt.mpr j.isLt⟩
    · -- Goal: ((orderIso).symm ⟨vh.val, _⟩).val < k.val
      set m : Fin S.card := (S.orderIsoOfFin rfl).symm
        ⟨vh.val, (Finset.mem_filter.mp vh.property).1⟩
      have hvLt : vh.val < φ k := (Finset.mem_filter.mp vh.property).2
      have hφm : φ m = vh.val := by
        show (S.orderEmbOfFin rfl m : Fin n) = vh.val
        rw [← S.coe_orderIsoOfFin_apply rfl m]
        change ((S.orderIsoOfFin rfl)
            ((S.orderIsoOfFin rfl).symm _) : ↥S).val = vh.val
        rw [OrderIso.apply_symm_apply]
      exact φ.lt_iff_lt.mp (hφm ▸ hvLt)
    · -- left_inv
      intro j
      apply Fin.ext
      show ((S.orderIsoOfFin rfl).symm
          ⟨φ ⟨j.val, j.isLt.trans k.isLt⟩, _⟩ : Fin S.card).val = j.val
      have h1 : (⟨φ ⟨j.val, j.isLt.trans k.isLt⟩,
          S.orderEmbOfFin_mem rfl _⟩ : ↥S)
          = S.orderIsoOfFin rfl ⟨j.val, j.isLt.trans k.isLt⟩ := by
        apply Subtype.ext
        show (φ ⟨j.val, _⟩ : Fin n)
            = (S.orderIsoOfFin rfl ⟨j.val, _⟩).val
        rw [S.coe_orderIsoOfFin_apply]
      rw [h1, OrderIso.symm_apply_apply]
    · -- right_inv
      intro vh
      apply Subtype.ext
      set m : Fin S.card := (S.orderIsoOfFin rfl).symm
        ⟨vh.val, (Finset.mem_filter.mp vh.property).1⟩
      show (φ ⟨m.val, _⟩ : Fin n) = vh.val
      -- ⟨m.val, _⟩ as Fin S.card equals m
      have hmEq : (⟨m.val, m.isLt⟩ : Fin S.card) = m := Fin.ext rfl
      change (φ (⟨m.val, m.isLt⟩ : Fin S.card) : Fin n) = vh.val
      rw [hmEq]
      show (φ m : Fin n) = vh.val
      rw [show (φ m : Fin n)
          = (S.orderIsoOfFin rfl m : ↥S).val
          from (S.coe_orderIsoOfFin_apply rfl m).symm]
      change ((S.orderIsoOfFin rfl)
          ((S.orderIsoOfFin rfl).symm _) : ↥S).val = vh.val
      rw [OrderIso.apply_symm_apply]
  -- e_cond on Pi
  let e_cond : (Fin k.val → α) ≃ᵐ (↥(S.filter (· < φ k)) → α) :=
    MeasurableEquiv.piCongrLeft (fun _ : ↥(S.filter (· < φ k)) => α) idx
  have hcond_meas : Measurable
      (fun ω (j : Fin k.val) =>
        Xs (φ ⟨j.val, j.isLt.trans k.isLt⟩) ω) :=
    measurable_pi_iff.mpr (fun _ => hXs _)
  have h_eq :
      (fun ω => e_cond (fun (j : Fin k.val) =>
          Xs (φ ⟨j.val, j.isLt.trans k.isLt⟩) ω))
        = fun ω (j : ↥(S.filter (· < φ k))) => Xs j.val ω := by
    funext ω
    funext jh
    have h_apply :=
      MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : ↥(S.filter (· < φ k)) => α)
        idx
        (fun (j : Fin k.val) => Xs (φ ⟨j.val, j.isLt.trans k.isLt⟩) ω)
        (idx.symm jh)
    have h_idx : idx (idx.symm jh) = jh := idx.apply_symm_apply jh
    rw [h_idx] at h_apply
    -- h_apply : e_cond (fun j => ...) jh = Xs (φ ⟨(idx.symm jh).val, _⟩) ω
    show e_cond (fun (j : Fin k.val) =>
        Xs (φ ⟨j.val, j.isLt.trans k.isLt⟩) ω) jh = Xs jh.val ω
    rw [h_apply]
    -- Goal: Xs (φ ⟨(idx.symm jh).val, _⟩) ω = Xs jh.val ω
    -- φ ⟨(idx.symm jh).val, _⟩ = (idx (idx.symm jh)).val = jh.val
    have hh : ((idx (idx.symm jh)) : ↥(S.filter (· < φ k))).val = jh.val :=
      congrArg Subtype.val h_idx
    -- idx.toFun (idx.symm jh) = ⟨φ ⟨(idx.symm jh).val, _⟩, _⟩
    -- so its .val = φ ⟨(idx.symm jh).val, _⟩
    show Xs (φ ⟨(idx.symm jh).val, _⟩ : Fin n) ω = Xs jh.val ω
    rw [show (φ ⟨(idx.symm jh).val, (idx.symm jh).isLt.trans k.isLt⟩ : Fin n)
        = jh.val from hh]
  exact (condEntropy_measurableEquiv_comp μ
    (Xs (φ k)) (hXs _)
    (fun ω (j : Fin k.val) =>
      Xs (φ ⟨j.val, j.isLt.trans k.isLt⟩) ω) hcond_meas e_cond).symm.trans
      (by rw [h_eq])

/-- subset 版 chain rule:
`H(X_S) = ∑ i ∈ S, H(X_i | X_{S ∩ {j : j < i}})`。

Phase B の n-変数 chain rule を `Xs ∘ orderEmbOfFin S` に適用し、
両辺を `jointEntropySubset` 形に reshape する。 -/
theorem jointEntropySubset_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (S : Finset (Fin n)) :
    jointEntropySubset μ Xs S
      = ∑ i ∈ S,
          InformationTheory.MeasureFano.condEntropy μ (Xs i)
            (fun ω (j : (S.filter (· < i))) => Xs j.val ω) := by
  set φ : Fin S.card ↪o Fin n := S.orderEmbOfFin rfl
  set Xs' : Fin S.card → Ω → α := fun k => Xs (φ k) with hXs'_def
  have hXs'_meas : ∀ k, Measurable (Xs' k) := fun k => hXs (φ k)
  have h_chain := jointEntropy_chain_rule μ Xs' hXs'_meas
  -- LHS bridge: jointEntropy μ Xs' = jointEntropySubset μ Xs S
  have h_lhs : jointEntropy μ Xs' = jointEntropySubset μ Xs S := by
    let idx : Fin S.card ≃ ↥S := (S.orderIsoOfFin rfl).toEquiv
    let e : (Fin S.card → α) ≃ᵐ (↥S → α) :=
      MeasurableEquiv.piCongrLeft (fun _ : ↥S => α) idx
    have hXs'_full : Measurable (fun ω k => Xs' k ω) :=
      measurable_pi_iff.mpr hXs'_meas
    have h_comp := entropy_measurableEquiv_comp μ
      (fun ω k => Xs' k ω) hXs'_full e
    have h_eq :
        (fun ω => e (fun k => Xs' k ω))
          = fun ω (j : ↥S) => Xs j.val ω := by
      funext ω
      funext jh
      have h_apply :=
        MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ↥S => α)
          idx (fun k => Xs' k ω) (idx.symm jh)
      have h_idx : idx (idx.symm jh) = jh := idx.apply_symm_apply jh
      rw [h_idx] at h_apply
      show e (fun k => Xs' k ω) jh = Xs jh.val ω
      rw [h_apply]
      show Xs (φ (idx.symm jh)) ω = Xs jh.val ω
      have h2 : (φ (idx.symm jh) : Fin n) = jh.val := by
        show (S.orderEmbOfFin rfl (idx.symm jh) : Fin n) = jh.val
        rw [← S.coe_orderIsoOfFin_apply rfl (idx.symm jh)]
        change ((S.orderIsoOfFin rfl)
            ((S.orderIsoOfFin rfl).symm jh) : ↥S).val = jh.val
        rw [OrderIso.apply_symm_apply]
      rw [h2]
    rw [h_eq] at h_comp
    unfold jointEntropy jointEntropySubset
    exact h_comp.symm
  -- RHS bridge: per-summand bridge + sum reindex via Finset.sum_nbij
  have h_rhs :
      (∑ k : Fin S.card,
          InformationTheory.MeasureFano.condEntropy μ (Xs' k)
            (fun ω (j : Fin k.val) =>
              Xs' ⟨j.val, j.isLt.trans k.isLt⟩ ω))
        = ∑ i ∈ S,
            InformationTheory.MeasureFano.condEntropy μ (Xs i)
              (fun ω (j : (S.filter (· < i))) => Xs j.val ω) := by
    refine Finset.sum_nbij (fun k => φ k)
      (fun k _ => S.orderEmbOfFin_mem rfl k) ?_ ?_ ?_
    · intro a _ b _ h; exact φ.injective h
    · intro v hv
      have hrange : v ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]; exact hv
      obtain ⟨k, hk⟩ := hrange
      exact ⟨k, Finset.mem_univ k, hk⟩
    · intro k _
      exact condEntropy_chainSummand_bridge μ Xs hXs S k
  rw [h_lhs] at h_chain
  rw [h_chain, h_rhs]

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

/-- Helper: `jointEntropyExcept` of `Xs ∘ orderEmb` at `k` equals `jointEntropySubset`
of `S.erase (orderEmb k)`. -/
private lemma jointEntropyExcept_orderEmb_eq
    (μ : Measure Ω) (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (S : Finset (Fin n)) (k : Fin S.card) :
    jointEntropyExcept μ (fun k' ω => Xs (S.orderEmbOfFin rfl k') ω) k
      = jointEntropySubset μ Xs (S.erase (S.orderEmbOfFin rfl k)) := by
  set φ : Fin S.card ↪o Fin n := S.orderEmbOfFin rfl
  -- Index Equiv: {j : Fin S.card // j ≠ k} ≃ ↥(S.erase (φ k))
  let idx : {j : Fin S.card // j ≠ k} ≃ ↥(S.erase (φ k)) :=
    { toFun := fun jh => ⟨φ jh.val, by
        rw [Finset.mem_erase]
        refine ⟨?_, S.orderEmbOfFin_mem rfl _⟩
        intro h
        exact jh.property (φ.injective h)⟩
      invFun := fun vh =>
        ⟨(S.orderIsoOfFin rfl).symm ⟨vh.val, (Finset.mem_erase.mp vh.property).2⟩, by
          intro h
          have hv_ne : vh.val ≠ φ k := (Finset.mem_erase.mp vh.property).1
          apply hv_ne
          have happ := congrArg (S.orderIsoOfFin rfl) h
          rw [OrderIso.apply_symm_apply] at happ
          have h2 : vh.val = (S.orderIsoOfFin rfl k : ↥S).val :=
            congrArg Subtype.val happ
          rw [h2, S.coe_orderIsoOfFin_apply]⟩
      left_inv := fun jh => by
        apply Subtype.ext
        show (S.orderIsoOfFin rfl).symm ⟨φ jh.val, _⟩ = jh.val
        have h1 : (⟨φ jh.val, S.orderEmbOfFin_mem rfl _⟩ : ↥S)
            = S.orderIsoOfFin rfl jh.val := by
          apply Subtype.ext
          show (φ jh.val : Fin n) = (S.orderIsoOfFin rfl jh.val).val
          rw [S.coe_orderIsoOfFin_apply]
        rw [h1, OrderIso.symm_apply_apply]
      right_inv := fun vh => by
        apply Subtype.ext
        show (φ ((S.orderIsoOfFin rfl).symm
            ⟨vh.val, (Finset.mem_erase.mp vh.property).2⟩) : Fin n) = vh.val
        rw [show (φ ((S.orderIsoOfFin rfl).symm
              ⟨vh.val, (Finset.mem_erase.mp vh.property).2⟩) : Fin n)
            = (S.orderIsoOfFin rfl ((S.orderIsoOfFin rfl).symm
                ⟨vh.val, (Finset.mem_erase.mp vh.property).2⟩) : ↥S).val
            from (S.coe_orderIsoOfFin_apply rfl _).symm,
            OrderIso.apply_symm_apply] }
  -- e : ({j : Fin S.card // j ≠ k} → α) ≃ᵐ (↥(S.erase (φ k)) → α)
  let e : ({j : Fin S.card // j ≠ k} → α) ≃ᵐ (↥(S.erase (φ k)) → α) :=
    MeasurableEquiv.piCongrLeft (fun _ : ↥(S.erase (φ k)) => α) idx
  unfold jointEntropyExcept jointEntropySubset
  have hmeas : Measurable
      (fun ω (j : {j : Fin S.card // j ≠ k}) => Xs (φ j.val) ω) :=
    measurable_pi_iff.mpr (fun _ => hXs _)
  have h_comp := entropy_measurableEquiv_comp μ
    (fun ω (j : {j : Fin S.card // j ≠ k}) => Xs (φ j.val) ω) hmeas e
  -- Pointwise: e (fun j => Xs (φ j) ω) ⟨v, hv⟩ = Xs v ω
  have h_eq :
      (fun ω => e (fun j : {j : Fin S.card // j ≠ k} => Xs (φ j.val) ω))
        = fun ω (j : ↥(S.erase (φ k))) => Xs j.val ω := by
    funext ω
    funext ⟨v, hv⟩
    have hk : (⟨v, hv⟩ : ↥(S.erase (φ k))) = idx (idx.symm ⟨v, hv⟩) :=
      (idx.apply_symm_apply ⟨v, hv⟩).symm
    conv_lhs => rw [hk]
    show MeasurableEquiv.piCongrLeft (fun _ : ↥(S.erase (φ k)) => α) idx
        (fun j : {j : Fin S.card // j ≠ k} => Xs (φ j.val) ω)
        (idx (idx.symm ⟨v, hv⟩)) = Xs v ω
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    -- Goal: Xs (φ ((idx.symm ⟨v, hv⟩).val)) ω = Xs v ω
    -- (idx.symm ⟨v, hv⟩).val = (S.orderIsoOfFin rfl).symm ⟨v, hvS⟩
    -- so φ (...) = (S.orderIsoOfFin rfl ((S.orderIsoOfFin rfl).symm ⟨v, hvS⟩)).val = v
    show Xs (φ (idx.symm ⟨v, hv⟩).val) ω = Xs v ω
    have hvS : v ∈ S := (Finset.mem_erase.mp hv).2
    have h1 : (idx.symm ⟨v, hv⟩).val = (S.orderIsoOfFin rfl).symm ⟨v, hvS⟩ := rfl
    rw [h1]
    rw [show (φ ((S.orderIsoOfFin rfl).symm ⟨v, hvS⟩) : Fin n)
          = (S.orderIsoOfFin rfl ((S.orderIsoOfFin rfl).symm ⟨v, hvS⟩) : ↥S).val
          from (S.coe_orderIsoOfFin_apply rfl _).symm,
        OrderIso.apply_symm_apply]
  rw [h_eq] at h_comp
  exact h_comp.symm

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
  -- Embed S as Fin S.card via orderEmbOfFin
  set φ : Fin S.card ↪o Fin n := S.orderEmbOfFin rfl with hφ_def
  set Xs' : Fin S.card → Ω → α := fun k => Xs (φ k) with hXs'_def
  have hXs'_meas : ∀ k, Measurable (Xs' k) := fun k => hXs (φ k)
  -- Apply existing Fin n han_inequality
  have h_han := han_inequality μ Xs' hXs'_meas
  -- LHS bridge: jointEntropy μ Xs' = jointEntropySubset μ Xs S
  have h_lhs : jointEntropy μ Xs' = jointEntropySubset μ Xs S := by
    -- e : (Fin S.card → α) ≃ᵐ (↥S → α) via orderIsoOfFin
    let idx : Fin S.card ≃ ↥S := (S.orderIsoOfFin rfl).toEquiv
    let e : (Fin S.card → α) ≃ᵐ (↥S → α) :=
      MeasurableEquiv.piCongrLeft (fun _ : ↥S => α) idx
    have hXs'_full :
        Measurable (fun ω k => Xs' k ω) :=
      measurable_pi_iff.mpr hXs'_meas
    have h_comp := entropy_measurableEquiv_comp μ
      (fun ω k => Xs' k ω) hXs'_full e
    -- Pointwise: e (fun k => Xs' k ω) j = Xs j.val ω
    have h_eq :
        (fun ω => e (fun k => Xs' k ω))
          = fun ω (j : ↥S) => Xs j.val ω := by
      funext ω
      funext ⟨v, hv⟩
      have hk : (⟨v, hv⟩ : ↥S) = idx (idx.symm ⟨v, hv⟩) :=
        (idx.apply_symm_apply ⟨v, hv⟩).symm
      conv_lhs => rw [hk]
      show MeasurableEquiv.piCongrLeft (fun _ : ↥S => α) idx
        (fun k => Xs' k ω) (idx (idx.symm ⟨v, hv⟩)) = Xs v ω
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
      -- Goal: Xs' (idx.symm ⟨v, hv⟩) ω = Xs v ω
      -- i.e. Xs (φ (idx.symm ⟨v, hv⟩)) ω = Xs v ω
      -- Need: (φ (idx.symm ⟨v, hv⟩)) = v.
      -- φ k = (S.orderIsoOfFin rfl k).val (by coe_orderIsoOfFin_apply)
      -- so φ (idx.symm ⟨v, hv⟩) = (idx (idx.symm ⟨v, hv⟩)).val = v.
      show Xs (φ (idx.symm ⟨v, hv⟩)) ω = Xs v ω
      have : (φ (idx.symm ⟨v, hv⟩) : Fin n) = v := by
        change (S.orderEmbOfFin rfl (idx.symm ⟨v, hv⟩) : Fin n) = v
        rw [← S.coe_orderIsoOfFin_apply rfl (idx.symm ⟨v, hv⟩)]
        show (idx (idx.symm ⟨v, hv⟩) : Fin n) = v
        rw [idx.apply_symm_apply]
      rw [this]
    rw [h_eq] at h_comp
    -- h_comp : entropy μ (fun ω j => Xs j.val ω) = entropy μ (fun ω k => Xs' k ω)
    unfold jointEntropy jointEntropySubset
    exact h_comp.symm
  -- RHS bridge: 各 summand を per-k bridge で書き換えて、sum を bij で reindex
  have h_rhs :
      ∑ k : Fin S.card, jointEntropyExcept μ Xs' k
        = ∑ i ∈ S, jointEntropySubset μ Xs (S.erase i) := by
    -- Apply Finset.sum_bij from (Finset.univ : Finset (Fin S.card)) to S via φ.
    refine Finset.sum_nbij (fun k => φ k) (fun k _ => S.orderEmbOfFin_mem rfl k)
      ?_ ?_ ?_
    · -- Injective on univ
      intro a _ b _ h
      exact φ.injective h
    · -- Surjective onto S
      intro v hv
      have hrange : v ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]; exact hv
      obtain ⟨k, hk⟩ := hrange
      exact ⟨k, Finset.mem_univ k, hk⟩
    · -- Per-summand
      intro k _
      exact jointEntropyExcept_orderEmb_eq μ Xs hXs S k
  rw [h_lhs, h_rhs] at h_han
  exact h_han

end InformationTheory.Shannon
