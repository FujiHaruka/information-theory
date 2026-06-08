import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Han.DShearer
import Mathlib.Probability.UniformOn

/-!
# Loomis–Whitney 不等式 (情報理論的証明)

InformationTheory の最初のムーンショット ([`docs/shannon/loomis-whitney-moonshot-plan.md`])。
Han Phase D の `shearer_inequality` を engine として、
任意 `n` の有限族 `α : Type` 上の有限部分集合 `A : Finset (Fin n → α)` に対する
$|A|^{n-1} \le \prod_{i : \text{Fin}\,n} |\pi_i(A)|$ を sorry なしで証明する。

## 主定義・主定理

* `projectionExcept i A` ─ `A : Finset (Fin n → α)` の `i` 成分を除いた射影像。
* `entropy_uniformOn_eq_log_card` ─ `μ = uniformOn (A : Set β)` のもとで
  `entropy μ id = log #A` (情報量はカーディナリティの log と等しい)。
* `entropy_le_log_image_card` ─ 任意 `f : β → γ` で
  `entropy μ f ≤ log #(A.image f)` (像濃度の log を超えない)。
* `loomis_whitney` ─ Loomis–Whitney 不等式 (主定理)。

## 戦略

`μ := uniformOn (A : Set (Fin n → α))`、`Xs i ω := ω i` を取る:

1. `entropy μ Xs ω↦ω = log #A` (Phase A)
2. `shearer_inequality` を `S i := univ.filter (· ≠ i)`、`k = n-1` で適用
   (cover 条件は `(univ.erase j).card = n-1`)
3. 各 marginal 項 `jointEntropySubset μ Xs (S i) ≤ log #(projectionExcept i A)`
   (Phase B; `entropy_le_log_image_card` を `f := fun ω j => ω j.val` で適用)
4. `Real.log_prod` で和をとり `Real.log_le_log_iff` で逆向きに log を剥がして
   自然数版の不等式に持ち上げる (Phase C)
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

/-! ## Phase A — counting measure 上の entropy plumbing -/

/-- 一様分布の entropy はカーディナリティの log に等しい。

`μ = uniformOn (A : Set β)` で `A` が空でないとき、恒等写像 `id : β → β` の entropy は
`log #A`。証明は per-singleton mass `1/#A` を `uniformOn_apply_finset` から取り出し、
`negMulLog (1/N) = (log N) / N` の代数で和を `#A · (log N)/N = log N` に潰す。 -/
@[entry_point]
theorem entropy_uniformOn_eq_log_card
    {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    {A : Finset β} (hA : A.Nonempty) :
    entropy (uniformOn (A : Set β)) (id : β → β) = Real.log A.card := by
  classical
  -- IsProbabilityMeasure of uniformOn
  haveI hprob : IsProbabilityMeasure (uniformOn (A : Set β)) :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  -- map id = uniformOn A
  have h_map : (uniformOn (A : Set β)).map (id : β → β)
      = uniformOn (A : Set β) :=
    Measure.map_id
  have h_card_pos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have h_card_ne : (A.card : ℝ) ≠ 0 := h_card_pos.ne'
  have h_card_pos_nat : 0 < A.card := hA.card_pos
  -- per-x measureReal value (split branches)
  have h_real_in : ∀ x ∈ A,
      ((uniformOn (A : Set β)).real ({x} : Set β)) = 1 / A.card := by
    intro x hx
    have h_finset_eq : ({x} : Set β) = (({x} : Finset β) : Set β) := by simp
    rw [Measure.real, h_finset_eq,
      uniformOn_apply_finset (s := A) (t := {x}),
      Finset.inter_singleton_of_mem hx, Finset.card_singleton]
    -- ENNReal: (1 : ℕ) / A.card → ℝ: 1 / A.card
    rw [Nat.cast_one, ENNReal.toReal_div, ENNReal.toReal_one]
    rfl
  have h_real_out : ∀ x : β, x ∉ A →
      ((uniformOn (A : Set β)).real ({x} : Set β)) = 0 := by
    intro x hx
    have h_finset_eq : ({x} : Set β) = (({x} : Finset β) : Set β) := by simp
    rw [Measure.real, h_finset_eq,
      uniformOn_apply_finset (s := A) (t := {x}),
      Finset.inter_singleton_of_notMem hx, Finset.card_empty]
    simp
  -- entropy unfold
  unfold entropy
  rw [h_map]
  -- Split universe sum into A and its complement
  rw [show (Finset.univ : Finset β)
        = A ∪ (Finset.univ \ A) from
        (Finset.union_sdiff_of_subset (Finset.subset_univ A)).symm,
    Finset.sum_union Finset.disjoint_sdiff]
  -- Outside A: terms are negMulLog 0 = 0
  have h_out_zero : ∀ x ∈ Finset.univ \ A,
      Real.negMulLog ((uniformOn (A : Set β)).real {x}) = 0 := by
    intro x hx
    have hx_not : x ∉ A := (Finset.mem_sdiff.mp hx).2
    rw [h_real_out x hx_not, Real.negMulLog_zero]
  rw [Finset.sum_eq_zero h_out_zero, add_zero]
  -- Inside A: each term is log #A / #A
  have h_in_term : ∀ x ∈ A,
      Real.negMulLog ((uniformOn (A : Set β)).real {x})
        = Real.log A.card / A.card := by
    intro x hx
    rw [h_real_in x hx]
    -- negMulLog (1/N) = -(1/N) * log (1/N) = log N / N
    rw [Real.negMulLog, Real.log_div one_ne_zero h_card_ne, Real.log_one]
    ring
  rw [Finset.sum_congr rfl h_in_term, Finset.sum_const, nsmul_eq_mul]
  -- A.card * (log A.card / A.card) = log A.card
  field_simp

/-- `Y := f ∘ id` の像で支えられる確率分布の entropy は像濃度の log を超えない。

具体的には `μ = uniformOn (A : Set β)` のもとで `entropy μ f ≤ log #(A.image f)`。
証明は: `μ.map f` の support が `A.image f` に含まれるので、
`negMulLog x ≤ x · (log #(A.image f) - log x)` 形ではなく、
**Jensen** (`negMulLog` 凹性) でやらず **直接** に
`entropy μ f ≤ entropy_uniform_on_image_f`、後者を `entropy_uniformOn_eq_log_card` で評価する
ルートを取りたいが、push-forward が一様分布になるとは限らないので
ここでは `negMulLog x ≤ -x · log p_min + x · log #` のような直接評価ではなく、

**実装ルート (採用)**: 「`y ∉ A.image f` では mass 0」から `support` を絞り、
`-∑ p_y log p_y ≤ log #support` を負エントロピー関数の凹性 (Jensen) で示す。
`Real.inner_le_nnreal_iff_norm_le` 系は重いので、ここでは `negMulLog` の上界
`negMulLog p ≤ -p · log (1 / #support)` (Gibbs) を 1 段適用、続いて
`log (1/N) = -log N` で整形、`∑ p = 1` で潰す。
-/
@[entry_point]
theorem entropy_le_log_image_card
    {β γ : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    {A : Finset β} (hA : A.Nonempty)
    (f : β → γ) (hf : Measurable f) :
    entropy (uniformOn (A : Set β)) f ≤ Real.log (A.image f).card := by
  classical
  haveI hprob : IsProbabilityMeasure (uniformOn (A : Set β)) :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  haveI hprob_map : IsProbabilityMeasure
      ((uniformOn (A : Set β)).map f) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  set N : ℕ := (A.image f).card with hN_def
  have hN_pos : 0 < N := by
    have : (A.image f).Nonempty := hA.image f
    exact this.card_pos
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN_pos.ne'
  have hN_pos_R : (0 : ℝ) < N := by exact_mod_cast hN_pos
  -- (1) Support: y ∉ A.image f ⟹ ((uniformOn A).map f).real {y} = 0.
  have h_outside : ∀ y : γ, y ∉ A.image f →
      ((uniformOn (A : Set β)).map f).real ({y} : Set γ) = 0 := by
    intro y hy
    rw [Measure.real, Measure.map_apply hf (measurableSet_singleton y)]
    -- (A : Set β) ∩ f ⁻¹' {y} = ∅, so uniformOn A (f ⁻¹' {y}) = 0
    have hempty : (A : Set β) ∩ f ⁻¹' {y} = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Finset.mem_coe, Set.mem_empty_iff_false, iff_false, not_and]
      intro hxA hfx
      apply hy
      rw [← hfx]
      exact Finset.mem_image_of_mem f hxA
    rw [(uniformOn_eq_zero_iff A.finite_toSet).mpr hempty]
    rfl
  -- (2) Each y has measure ≤ 1
  have h_le_one : ∀ y : γ,
      ((uniformOn (A : Set β)).map f).real ({y} : Set γ) ≤ 1 :=
    fun y => measureReal_le_one
  have h_nn : ∀ y : γ,
      0 ≤ ((uniformOn (A : Set β)).map f).real ({y} : Set γ) :=
    fun y => measureReal_nonneg
  -- (3) Sum of measures = 1.
  have h_sum_one :
      ∑ y : γ, ((uniformOn (A : Set β)).map f).real ({y} : Set γ) = 1 := by
    rw [show (∑ y : γ, ((uniformOn (A : Set β)).map f).real ({y} : Set γ))
          = ∑ y ∈ (Finset.univ : Finset γ),
              ((uniformOn (A : Set β)).map f).real ({y} : Set γ) from rfl,
        sum_measureReal_singleton]
    rw [show ((Finset.univ : Finset γ) : Set γ) = Set.univ from Finset.coe_univ]
    simp [measureReal_def, measure_univ]
  -- (4) Sum restricted to (A.image f) of measures = 1 (others are zero).
  have h_sum_image_one :
      ∑ y ∈ A.image f, ((uniformOn (A : Set β)).map f).real ({y} : Set γ) = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ (A.image f))
      (fun y _ hy => h_outside y hy)]
    exact h_sum_one
  -- (5) entropy expansion: outside the image, terms vanish.
  unfold entropy
  rw [show (∑ y : γ, Real.negMulLog
            (((uniformOn (A : Set β)).map f).real ({y} : Set γ)))
        = ∑ y ∈ A.image f, Real.negMulLog
            (((uniformOn (A : Set β)).map f).real ({y} : Set γ)) from
      (Finset.sum_subset (Finset.subset_univ (A.image f))
        (fun y _ hy => by rw [h_outside y hy, Real.negMulLog_zero])).symm]
  -- (6) Gibbs: negMulLog p ≤ p * log N + (1/N - p) * (algebra noise) — instead use Jensen on negMulLog (concave on [0, ∞)).
  -- Here we use: ∑ negMulLog p ≤ N * negMulLog (mean) by concavity, and mean = 1/N.
  -- mean = (∑ p) / N = 1/N. negMulLog (1/N) = (log N) / N, so N * (log N)/N = log N.
  set s : Finset γ := A.image f with hs_def
  have hs_card : s.card = N := rfl
  have hs_card_pos : 0 < s.card := hN_pos
  -- Use negMulLog concavity on Set.Ici 0:
  have h_card_R_pos : (0 : ℝ) < s.card := by exact_mod_cast hs_card_pos
  have h_one_div_pos : (0 : ℝ) ≤ 1 / s.card := by
    rw [one_div]; exact inv_nonneg.mpr h_card_R_pos.le
  have h_weights_sum : ∑ _y ∈ s, ((1 : ℝ) / s.card) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have h_each_in : ∀ y ∈ s,
      ((uniformOn (A : Set β)).map f).real ({y} : Set γ) ∈ Set.Ici (0 : ℝ) :=
    fun y _ => h_nn y
  -- Apply ConcaveOn.le_map_sum: ∑ w_i • f(p_i) ≤ f (∑ w_i • p_i)
  have h_jensen_concave :=
    ConcaveOn.le_map_sum (𝕜 := ℝ) (t := s)
      (w := fun _ => 1 / s.card)
      (p := fun y => ((uniformOn (A : Set β)).map f).real ({y} : Set γ))
      Real.concaveOn_negMulLog
      (fun _ _ => h_one_div_pos) h_weights_sum h_each_in
  -- h_jensen_concave : ∑ y ∈ s, (1/N) • negMulLog (p y) ≤ negMulLog (∑ y ∈ s, (1/N) • p y)
  -- Convert smul into mul (real • real = real * real)
  simp only [smul_eq_mul] at h_jensen_concave
  have h_jensen :
      ∑ y ∈ s, Real.negMulLog
          (((uniformOn (A : Set β)).map f).real ({y} : Set γ))
        ≤ (s.card : ℝ) * Real.negMulLog
            (∑ y ∈ s, (1 / s.card) *
              ((uniformOn (A : Set β)).map f).real ({y} : Set γ)) := by
    have h_lhs_eq :
        ∑ y ∈ s, Real.negMulLog
            (((uniformOn (A : Set β)).map f).real ({y} : Set γ))
          = (s.card : ℝ) * (∑ y ∈ s, (1 / s.card) *
              Real.negMulLog
                (((uniformOn (A : Set β)).map f).real ({y} : Set γ))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      field_simp
    rw [h_lhs_eq]
    exact mul_le_mul_of_nonneg_left h_jensen_concave h_card_R_pos.le
  -- (7) Reduce mean.
  have h_mean :
      (∑ y ∈ s, (1 / s.card) *
          ((uniformOn (A : Set β)).map f).real ({y} : Set γ))
        = 1 / s.card := by
    rw [← Finset.mul_sum, h_sum_image_one, mul_one]
  rw [h_mean] at h_jensen
  -- (8) Compute negMulLog (1/N) = (log N)/N, then s.card * (log s.card / s.card) = log s.card.
  have h_negMulLog_inv :
      Real.negMulLog ((1 : ℝ) / s.card) = Real.log s.card / s.card := by
    rw [Real.negMulLog, Real.log_div one_ne_zero (by exact_mod_cast hs_card_pos.ne'),
      Real.log_one]
    ring
  rw [h_negMulLog_inv] at h_jensen
  have h_simp :
      (s.card : ℝ) * (Real.log s.card / s.card) = Real.log s.card := by
    rw [mul_div_assoc']
    field_simp
  rw [h_simp] at h_jensen
  -- (9) s.card = N (= (A.image f).card by def).
  show ∑ y ∈ s, Real.negMulLog
        (((uniformOn (A : Set β)).map f).real ({y} : Set γ))
      ≤ Real.log (A.image f).card
  exact h_jensen

/-! ## Phase B — 射影 plumbing -/

/-- `i` 番目の成分を除いた射影像。`A : Finset (Fin n → α)` を
`{j : Fin n // j ≠ i} → α` 値の Finset に落とす。 -/
def projectionExcept {n : ℕ} {α : Type*} [DecidableEq α]
    (i : Fin n) (A : Finset (Fin n → α)) :
    Finset ({j : Fin n // j ≠ i} → α) :=
  A.image (fun x j => x j.val)

/-- 射影 entropy ≤ 射影像濃度の log。

`μ = uniformOn (A : Set (Fin n → α))` のもとで、
`Xs i ω := ω i` に対して `jointEntropySubset μ Xs (univ.filter (· ≠ i))`
は `(j : ↥(univ.filter (· ≠ i)) → α)` 値 RV の entropy。
これを `{j // j ≠ i}` 値 RV に reshape し
`entropy_le_log_image_card` を適用する。 -/
theorem jointEntropySubset_le_log_projectionExcept_card
    {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {A : Finset (Fin n → α)} (hA : A.Nonempty) (i : Fin n) :
    jointEntropySubset (uniformOn (A : Set (Fin n → α)))
        (fun (i : Fin n) (ω : Fin n → α) => ω i)
        (Finset.univ.filter (fun j : Fin n => j ≠ i))
      ≤ Real.log (projectionExcept i A).card := by
  classical
  -- IsProbabilityMeasure
  haveI hprob : IsProbabilityMeasure (uniformOn (A : Set (Fin n → α))) :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  -- Index equiv: ↥(univ.filter (· ≠ i)) ≃ {j : Fin n // j ≠ i}
  let idx : ↥(Finset.univ.filter (fun j : Fin n => j ≠ i))
      ≃ {j : Fin n // j ≠ i} :=
    { toFun := fun ⟨j, hj⟩ => ⟨j, (Finset.mem_filter.mp hj).2⟩
      invFun := fun ⟨j, hj⟩ => ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
      left_inv := by rintro ⟨j, hj⟩; rfl
      right_inv := by rintro ⟨j, hj⟩; rfl }
  -- e on Pi values
  let e : (↥(Finset.univ.filter (fun j : Fin n => j ≠ i)) → α)
      ≃ᵐ ({j : Fin n // j ≠ i} → α) :=
    MeasurableEquiv.piCongrLeft (fun _ : {j : Fin n // j ≠ i} => α) idx
  -- Setup: projection map f : (Fin n → α) → ({j // j ≠ i} → α)
  let fproj : (Fin n → α) → ({j : Fin n // j ≠ i} → α) :=
    fun x j => x j.val
  have hfproj_meas : Measurable fproj :=
    measurable_pi_iff.mpr (fun j => measurable_pi_apply j.val)
  -- jointEntropySubset = entropy μ (fun ω j => ω j.val) over univ.filter
  unfold jointEntropySubset
  -- Reshape: entropy μ (fun ω j => ω j.val : (univ.filter ...) → α)
  --        = entropy μ (fproj) via piCongrLeft idx.
  set Yo : (Fin n → α) → (↥(Finset.univ.filter (fun j : Fin n => j ≠ i)) → α) :=
    fun ω j => ω j.val with hYo_def
  have hYo_meas : Measurable Yo :=
    measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)
  -- entropy_measurableEquiv_comp e ∘ Yo = Yo
  have h_entropy_eq :
      entropy (uniformOn (A : Set (Fin n → α))) (fun ω => e (Yo ω))
        = entropy (uniformOn (A : Set (Fin n → α))) Yo :=
    entropy_measurableEquiv_comp _ Yo hYo_meas e
  -- e (Yo ω) = fproj ω pointwise
  have h_pointwise : (fun ω => e (Yo ω)) = fproj := by
    funext ω
    funext ⟨v, hv⟩
    have hk : (⟨v, hv⟩ : {j : Fin n // j ≠ i})
        = idx (idx.symm ⟨v, hv⟩) :=
      (idx.apply_symm_apply ⟨v, hv⟩).symm
    conv_lhs => rw [hk]
    show MeasurableEquiv.piCongrLeft (fun _ : {j : Fin n // j ≠ i} => α) idx
        (Yo ω) (idx (idx.symm ⟨v, hv⟩)) = ω v
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    -- After piCongrLeft_apply_apply: Yo ω (idx.symm ⟨v, hv⟩)
    show Yo ω (idx.symm ⟨v, hv⟩) = ω v
    rfl
  rw [show entropy (uniformOn (A : Set (Fin n → α)))
          (fun ω (j : ↥(Finset.univ.filter (fun j : Fin n => j ≠ i))) =>
            ω j.val)
        = entropy (uniformOn (A : Set (Fin n → α))) Yo from rfl,
    ← h_entropy_eq, h_pointwise]
  -- Now apply entropy_le_log_image_card with f := fproj.
  have h_le := entropy_le_log_image_card hA fproj hfproj_meas
  -- (A.image fproj).card = (projectionExcept i A).card by def.
  show entropy (uniformOn (A : Set (Fin n → α))) fproj
      ≤ Real.log (projectionExcept i A).card
  exact h_le

/-! ## Phase C — Loomis–Whitney 主定理 -/

/-- Loomis–Whitney 不等式 (情報理論的証明)。

任意 `n ≥ 1`、有限族 `α : Type` 上の有限部分集合 `A : Finset (Fin n → α)` で
`A.Nonempty` のとき:
$$|A|^{n-1} \le \prod_{i : \text{Fin}\,n} |\pi_i(A)|.$$

ここで `\pi_i(A) := \{x \restriction \{j \ne i\} \mid x \in A\} = projectionExcept i A`。 -/
@[entry_point]
theorem loomis_whitney
    {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {A : Finset (Fin n → α)} (hA : A.Nonempty) :
    A.card ^ (n - 1) ≤ ∏ i : Fin n, (projectionExcept i A).card := by
  classical
  -- Probability measure setup
  haveI hprob : IsProbabilityMeasure (uniformOn (A : Set (Fin n → α))) :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  set μ : Measure (Fin n → α) := uniformOn (A : Set (Fin n → α)) with hμ_def
  set Xs : Fin n → (Fin n → α) → α := fun i ω => ω i with hXs_def
  have hXs_meas : ∀ i, Measurable (Xs i) := fun i => measurable_pi_apply i
  -- Cover set: S i := univ.filter (· ≠ i)
  set S : Fin n → Finset (Fin n) :=
    fun i => Finset.univ.filter (fun j : Fin n => j ≠ i) with hS_def
  -- Cover condition: each j is in n - 1 of the S i
  have h_cover : ∀ j : Fin n,
      (n - 1) ≤ (Finset.univ.filter (fun i : Fin n => j ∈ S i)).card := by
    intro j
    -- {i | j ∈ S i} = {i | j ≠ i} = univ.erase j
    have h_filter_eq : Finset.univ.filter (fun i : Fin n => j ∈ S i)
        = Finset.univ.erase j := by
      ext i
      rw [Finset.mem_filter, Finset.mem_erase]
      simp only [Finset.mem_univ, true_and, and_true, S, Finset.mem_filter]
      -- Goal: (j ≠ i) ↔ (i ≠ j) (after simp out the universe membership)
      exact ⟨fun h hij => h hij.symm, fun h hji => h hji.symm⟩
    rw [h_filter_eq, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin]
  -- Apply Shearer
  have h_shearer := shearer_inequality μ Xs hXs_meas S h_cover
  -- LHS bridge: jointEntropy μ Xs = log #A
  have h_joint_log : jointEntropy μ Xs = Real.log A.card := by
    -- jointEntropy μ Xs = entropy μ (fun ω i => Xs i ω) = entropy μ id (def-eq).
    unfold jointEntropy
    -- (fun ω i => Xs i ω) = id
    have h_eq : (fun (ω : Fin n → α) (i : Fin n) => Xs i ω) = id := by
      funext ω; funext i; rfl
    rw [h_eq]
    exact entropy_uniformOn_eq_log_card hA
  rw [h_joint_log] at h_shearer
  -- RHS bridge: each summand ≤ log #(projectionExcept i A)
  have h_marginal : ∀ i : Fin n,
      jointEntropySubset μ Xs (S i)
        ≤ Real.log (projectionExcept i A).card := by
    intro i
    exact jointEntropySubset_le_log_projectionExcept_card hA i
  have h_RHS_le : ∑ i : Fin n, jointEntropySubset μ Xs (S i)
      ≤ ∑ i : Fin n, Real.log (projectionExcept i A).card :=
    Finset.sum_le_sum (fun i _ => h_marginal i)
  -- Combine: (n-1) · log #A ≤ ∑ i, log #(projectionExcept i A)
  have h_log :
      ((n - 1 : ℕ) : ℝ) * Real.log A.card
        ≤ ∑ i : Fin n, Real.log (projectionExcept i A).card :=
    h_shearer.trans h_RHS_le
  -- Convert ∑ log to log ∏
  have h_proj_pos : ∀ i : Fin n, 0 < (projectionExcept i A).card := by
    intro i
    have : (projectionExcept i A).Nonempty :=
      hA.image (fun (x : Fin n → α) (j : {j : Fin n // j ≠ i}) => x j.val)
    exact this.card_pos
  have h_proj_ne : ∀ i : Fin n,
      ((projectionExcept i A).card : ℝ) ≠ 0 := fun i => by
    exact_mod_cast (h_proj_pos i).ne'
  have h_sum_log_eq :
      (∑ i : Fin n, Real.log (projectionExcept i A).card)
        = Real.log (∏ i : Fin n, ((projectionExcept i A).card : ℝ)) := by
    rw [Real.log_prod (fun i _ => h_proj_ne i)]
  rw [h_sum_log_eq] at h_log
  -- LHS: ((n-1) : ℝ) * log #A = log (#A ^ (n-1))
  have h_lhs_eq :
      ((n - 1 : ℕ) : ℝ) * Real.log A.card
        = Real.log ((A.card : ℝ) ^ (n - 1)) := by
    rw [Real.log_pow]
  rw [h_lhs_eq] at h_log
  -- Both sides are log of positive reals; log_le_log_iff to peel off log.
  have h_card_pos : 0 < (A.card : ℝ) := by
    exact_mod_cast hA.card_pos
  have h_lhs_pos : (0 : ℝ) < (A.card : ℝ) ^ (n - 1) := pow_pos h_card_pos _
  have h_rhs_pos : (0 : ℝ) < ∏ i : Fin n, ((projectionExcept i A).card : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast h_proj_pos i)
  have h_pow_le :
      (A.card : ℝ) ^ (n - 1)
        ≤ ∏ i : Fin n, ((projectionExcept i A).card : ℝ) :=
    (Real.log_le_log_iff h_lhs_pos h_rhs_pos).mp h_log
  -- Cast to ℕ
  have h_cast :
      ((A.card ^ (n - 1) : ℕ) : ℝ)
        ≤ (((∏ i : Fin n, (projectionExcept i A).card) : ℕ) : ℝ) := by
    push_cast
    exact h_pow_le
  exact_mod_cast h_cast

end InformationTheory.Shannon
