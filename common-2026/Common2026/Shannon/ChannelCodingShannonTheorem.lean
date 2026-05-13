import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.ChannelCodingAchievability
import Common2026.Shannon.MaxEntropy
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Shannon noisy channel coding theorem (D-1) — full form

[D-1 ムーンショット plan](../../../docs/shannon/channel-coding-shannon-theorem-plan.md)
の Phase A-D を統合し、Cover-Thomas 7.7.1 完全形に到達する file。

**主定理 (Phase D)**:

```
shannon_noisy_channel_coding_theorem :
  (W : Channel α β) [IsMarkovKernel W]
  {R : ℝ} (hR_pos : 0 < R) (hR : R < capacity W)
  {ε : ℝ} (hε : 0 < ε) :
  ∃ N : ℕ, ∀ n, N ≤ n →
    ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
      (c : Code M n α β),
      ∀ m, (c.errorProbAt W m).toReal < ε
```

既存 `channel_coding_achievability` (固定 `p`, average error, full-support `hp_pos + hW_pos`)
を出発点に、(A) 入力分布最大化、(B) expurgation で average → max、(C) full-support 仮定の
sub-channel 切り出しで除去、(D) 主定理を統合する。

本ファイルは Phase A (入力分布最大化) を完成 + Phase B-D は skeleton (`:= by sorry`)。
後続コミットで Phase B-D を順次埋める。
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ## Phase A — 入力分布最大化

### A.1 — `pmfToMeasure` helper + `capacity` 定義 -/

/-- 有限 alphabet 上の pmf vector `p : α → ℝ` を `Measure α` に持ち上げる:
`pmfToMeasure p = ∑ a, ENNReal.ofReal (p a) • Measure.dirac a`。

`p ∈ stdSimplex ℝ α` のとき `IsProbabilityMeasure (pmfToMeasure p)` (下記 instance 候補)、
任意 `s ⊆ α` で `(pmfToMeasure p) s = ∑ a ∈ s, ENNReal.ofReal (p a)` (atom 評価)。 -/
noncomputable def pmfToMeasure (p : α → ℝ) : Measure α :=
  ∑ a : α, ENNReal.ofReal (p a) • Measure.dirac a

omit [DecidableEq α] [Nonempty α] in
/-- Atom 評価: `(pmfToMeasure p) {a} = ENNReal.ofReal (p a)` (singleton). -/
lemma pmfToMeasure_apply_singleton (p : α → ℝ) (a : α) :
    (pmfToMeasure p) ({a} : Set α) = ENNReal.ofReal (p a) := by
  unfold pmfToMeasure
  rw [Measure.finsetSum_apply Finset.univ _ {a}]
  -- ∑ b, (ENNReal.ofReal (p b) • Measure.dirac b) {a} collapses to b = a.
  rw [Finset.sum_eq_single a]
  · simp [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.singleton a)]
  · intro b _ hb
    simp [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.singleton a),
      Set.indicator_of_notMem (show b ∉ ({a} : Set α) by simp [Set.mem_singleton_iff]; exact hb)]
  · intro h
    exact (h (Finset.mem_univ a)).elim

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `p ∈ stdSimplex ℝ α` のとき `pmfToMeasure p` は probability measure。 -/
lemma pmfToMeasure_isProbabilityMeasure
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α) :
    IsProbabilityMeasure (pmfToMeasure p) := by
  refine ⟨?_⟩
  unfold pmfToMeasure
  rw [Measure.finsetSum_apply Finset.univ _ Set.univ]
  -- ∑ a, (ENNReal.ofReal (p a) • Measure.dirac a) Set.univ = ∑ a, ENNReal.ofReal (p a).
  have h_each : ∀ a ∈ (Finset.univ : Finset α),
      (ENNReal.ofReal (p a) • Measure.dirac a) (Set.univ : Set α) = ENNReal.ofReal (p a) := by
    intro a _
    simp [Measure.smul_apply]
  rw [Finset.sum_congr rfl h_each]
  -- ∑ a, ENNReal.ofReal (p a) = 1
  have hsum := hp.2
  have hnn : ∀ a, 0 ≤ p a := hp.1
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hnn a), hsum, ENNReal.ofReal_one]

omit [DecidableEq α] [Nonempty α] in
/-- `pmfToMeasure p` の `.real {a}` 評価: `p a` 自身に等しい (`p ∈ stdSimplex` で `p a ≥ 0`)。 -/
lemma pmfToMeasure_real_singleton
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α) (a : α) :
    (pmfToMeasure p).real {a} = p a := by
  unfold Measure.real
  rw [pmfToMeasure_apply_singleton]
  exact ENNReal.toReal_ofReal (hp.1 a)

/-- **Channel capacity** (Cover-Thomas 7.5):
`capacity W := sup { I(p; W).toReal | p ∈ stdSimplex }`。 -/
noncomputable def capacity (W : Channel α β) : ℝ :=
  sSup ((fun p : α → ℝ => (mutualInfoOfChannel (pmfToMeasure p) W).toReal) ''
        stdSimplex ℝ α)

omit [MeasurableSingletonClass α] [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSingletonClass β] in
/-- `capacity` value set は非空 (`Pi.single` Dirac で). -/
lemma capacity_image_nonempty (W : Channel α β) :
    ((fun p : α → ℝ => (mutualInfoOfChannel (pmfToMeasure p) W).toReal) ''
      stdSimplex ℝ α).Nonempty :=
  ⟨_, Pi.single (Classical.arbitrary α) 1, single_mem_stdSimplex ℝ _, rfl⟩

/-- `capacity` value set is bounded above by `H(X) + H(Y)`-style entropy bound. -/
theorem capacity_bddAbove (W : Channel α β) [IsMarkovKernel W] :
    BddAbove ((fun p : α → ℝ => (mutualInfoOfChannel (pmfToMeasure p) W).toReal) ''
              stdSimplex ℝ α) := by
  -- I(p; W).toReal = H(X) + H(Y) - H(X,Y) ≤ H(X) + H(Y) ≤ log |α| + log |β|.
  refine ⟨Real.log (Fintype.card α) + Real.log (Fintype.card β), ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  haveI : IsProbabilityMeasure (pmfToMeasure p) := pmfToMeasure_isProbabilityMeasure hp
  have h_id := mutualInfoOfChannel_eq_HX_add_HY_sub_HZ (pmfToMeasure p) W
  show (mutualInfoOfChannel (pmfToMeasure p) W).toReal
      ≤ Real.log (Fintype.card α) + Real.log (Fintype.card β)
  rw [h_id]
  -- H(X) ≤ log |α|.
  have hHX_le : entropy (jointDistribution (pmfToMeasure p) W) Prod.fst
      ≤ Real.log (Fintype.card α) :=
    entropy_le_log_card _ Prod.fst measurable_fst
  have hHY_le : entropy (jointDistribution (pmfToMeasure p) W) Prod.snd
      ≤ Real.log (Fintype.card β) :=
    entropy_le_log_card _ Prod.snd measurable_snd
  -- H(X,Y) ≥ 0.
  have hHXY_nn : 0 ≤ entropy (jointDistribution (pmfToMeasure p) W) id :=
    entropy_nonneg _ id measurable_id
  linarith

/-- `capacity W ≥ 0`. -/
theorem capacity_nonneg (W : Channel α β) [IsMarkovKernel W] : 0 ≤ capacity W := by
  unfold capacity
  -- Each `.toReal` value in the image is ≥ 0.
  obtain ⟨v, hv_mem_image⟩ := capacity_image_nonempty W
  refine le_csSup_of_le (capacity_bddAbove W) hv_mem_image ?_
  obtain ⟨_p, _hp_mem, hp_eq⟩ := hv_mem_image
  simp only at hp_eq
  rw [← hp_eq]
  exact ENNReal.toReal_nonneg

/-! ### A.2 — `I(p; W).toReal` の連続性 (in p) -/

/-- **Phase A.2 (deferred)**: `(p : α → ℝ) ↦ (mutualInfoOfChannel (pmfToMeasure p) W).toReal`
は `stdSimplex ℝ α` 上連続。3-entropy 形 + `Real.continuous_negMulLog` 経由。

Phase A の主定理 `capacity_lt_implies_exists_pmf` は `lt_csSup_iff` 経由で本連続性に
依存しないため、本 lemma は documentation / Phase A.3 達成元存在用。 -/
theorem continuous_mutualInfoOfChannel_left (W : Channel α β) [IsMarkovKernel W] :
    ContinuousOn (fun p : α → ℝ => (mutualInfoOfChannel (pmfToMeasure p) W).toReal)
      (stdSimplex ℝ α) := by
  sorry

/-! ### A.3 — capacity 達成元 (documentation) -/

/-- **Phase A.3 (deferred / documentation)**: `IsCompact.exists_isMaxOn` 経由で
capacity 達成元 `p* ∈ stdSimplex` の存在。主定理 (Phase D) は `capacity_lt_implies_exists_pmf`
だけで通るので documentation 用。 -/
theorem exists_capacity_achiever (W : Channel α β) [IsMarkovKernel W] :
    ∃ p ∈ stdSimplex ℝ α, IsMaxOn
      (fun p : α → ℝ => (mutualInfoOfChannel (pmfToMeasure p) W).toReal)
      (stdSimplex ℝ α) p := by
  sorry

/-! ### A.4 — `R < C ⟹ ∃ p, R < I(p; W)` (Phase A 主補題) -/

/-- **Phase A.4 (key)**: `R < capacity W` から `R < I(p; W).toReal` を満たす `p ∈ stdSimplex` を
直接取り出す。`lt_csSup_iff` (`BddAbove` + `Nonempty`) を適用。 -/
theorem capacity_lt_implies_exists_pmf
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR : R < capacity W) :
    ∃ p ∈ stdSimplex ℝ α,
      R < (mutualInfoOfChannel (pmfToMeasure p) W).toReal := by
  unfold capacity at hR
  -- `lt_csSup_iff` requires BddAbove and Nonempty.
  have h_bdd := capacity_bddAbove W
  have h_ne := capacity_image_nonempty W
  rw [lt_csSup_iff h_bdd h_ne] at hR
  obtain ⟨v, ⟨p, hp_mem, hp_eq⟩, hv_lt⟩ := hR
  refine ⟨p, hp_mem, ?_⟩
  simp only at hp_eq
  rw [hp_eq]
  exact hv_lt

/-! ## Phase B — Expurgation (skeleton)

Average → max error 化。Markov inequality on Finset で「`errorProbAt > 2·avg` な m の数 ≤ M/2」
→ 上位半分の messages を取って sub-code 化 → max error ≤ 2·avg。-/

/-- **Phase B.1**: Markov inequality on Finset で
`errorProbAt > K · avg` を満たす m の個数 ≤ M / K。 -/
theorem errorProbAt_filter_card_bound
    {M n : ℕ} (c : Code M n α β) (W : Channel α β) [IsMarkovKernel W]
    {K : ℝ} (hK : 1 < K) :
    ((Finset.univ : Finset (Fin M)).filter
        (fun m => K * (c.averageErrorProb W).toReal < (c.errorProbAt W m).toReal)).card
      * K ≤ (M : ℝ) := by
  classical
  set f : Fin M → ℝ := fun m => (c.errorProbAt W m).toReal with hf_def
  set avg : ℝ := (c.averageErrorProb W).toReal with havg_def
  set F : Finset (Fin M) := (Finset.univ : Finset (Fin M)).filter
      (fun m => K * avg < f m) with hF_def
  -- Each summand is finite and bounded.
  have hK_pos : 0 < K := lt_trans zero_lt_one hK
  have h_each_le_one : ∀ m : Fin M, c.errorProbAt W m ≤ 1 := by
    intro m
    haveI : IsProbabilityMeasure (Measure.pi (fun i => W (c.encoder m i))) := by infer_instance
    exact prob_le_one
  have h_each_ne_top : ∀ m : Fin M, c.errorProbAt W m ≠ ∞ := fun m =>
    ((h_each_le_one m).trans_lt ENNReal.one_lt_top).ne
  have hf_nn : ∀ m, 0 ≤ f m := fun m => ENNReal.toReal_nonneg
  -- Case split on M = 0.
  by_cases hM : M = 0
  · subst hM
    -- F is empty.
    have hF_empty : F = ∅ := Finset.eq_empty_of_forall_notMem (fun m => Fin.elim0 m)
    simp [hF_empty]
  · have hM_pos : 0 < M := Nat.pos_of_ne_zero hM
    have hM_R_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
    -- avg as a Real sum: avg = (1/M) * ∑ f m.
    have h_avg_eq : avg = (M : ℝ)⁻¹ * ∑ m : Fin M, f m := by
      simp only [havg_def, hf_def, Code.averageErrorProb, hM, if_false]
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
          ENNReal.toReal_sum (fun m _ => h_each_ne_top m)]
    -- Sum of f over all = M * avg.
    have h_sum_eq : ∑ m : Fin M, f m = (M : ℝ) * avg := by
      rw [h_avg_eq, ← mul_assoc, mul_inv_cancel₀ hM_R_pos.ne', one_mul]
    -- avg ≥ 0.
    have h_avg_nn : 0 ≤ avg := ENNReal.toReal_nonneg
    -- Sub-case avg = 0: F is empty.
    by_cases h_avg_zero : avg = 0
    · -- ∑ f m = 0 with all f m ≥ 0 implies each f m = 0.
      have h_sum_zero : ∑ m : Fin M, f m = 0 := by rw [h_sum_eq, h_avg_zero, mul_zero]
      have h_each_zero : ∀ m ∈ (Finset.univ : Finset (Fin M)), f m = 0 := by
        intro m hm
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hf_nn i)).mp h_sum_zero m hm
      have hF_empty : F = ∅ := by
        rw [hF_def]
        refine Finset.filter_false_of_mem ?_
        intro m hm
        rw [h_each_zero m hm, h_avg_zero, mul_zero]
        exact lt_irrefl 0
      rw [hF_empty]
      simp [hM_R_pos.le]
    · have h_avg_pos : 0 < avg := lt_of_le_of_ne h_avg_nn (Ne.symm h_avg_zero)
      -- For m ∈ F, f m ≥ K * avg (in fact >).
      have h_F_lb : ∀ m ∈ F, K * avg ≤ f m := by
        intro m hm
        rw [hF_def, Finset.mem_filter] at hm
        exact hm.2.le
      -- card F * (K * avg) ≤ ∑_{m ∈ F} f m  (via Finset.card_nsmul_le_sum).
      have h_card_le_sum_F : (F.card : ℝ) * (K * avg) ≤ ∑ m ∈ F, f m := by
        have := F.card_nsmul_le_sum (fun m => f m) (K * avg) h_F_lb
        simpa [nsmul_eq_mul] using this
      -- ∑_{m ∈ F} f m ≤ ∑ all f m = M * avg.
      have h_sum_F_le : ∑ m ∈ F, f m ≤ ∑ m : Fin M, f m := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro m _; exact Finset.mem_univ m
        · intros m _ _; exact hf_nn m
      have h_card_le_M_avg : (F.card : ℝ) * (K * avg) ≤ (M : ℝ) * avg :=
        h_card_le_sum_F.trans (h_sum_F_le.trans_eq h_sum_eq)
      -- Divide by avg > 0.
      have h_rewrite : (F.card : ℝ) * (K * avg) = ((F.card : ℝ) * K) * avg := by ring
      rw [h_rewrite] at h_card_le_M_avg
      exact (mul_le_mul_iff_of_pos_right h_avg_pos).mp h_card_le_M_avg

/-- **Phase B.2 (skeleton)**: sub-code 構築。`S : Finset (Fin M)` で encoder を S に restrict、
decoder は外を任意の固定 message に decode。`Fin S.card ≃ S` 経由。 -/
noncomputable def Code.subcode
    {M n : ℕ} (c : Code M n α β) (S : Finset (Fin M)) (hS : 0 < S.card) :
    Code S.card n α β :=
  -- 一旦 placeholder: encoder = S 内 message を順番に並べる、decoder は c.decoder の像を S
  -- に絞り込み、外なら ⟨0, hS⟩。
  { encoder := fun m' => c.encoder (S.equivFin.symm ⟨m', by simpa using m'.isLt⟩).val
    decoder := fun y =>
      let m := c.decoder y
      if h : m ∈ S then
        ⟨(S.equivFin ⟨m, h⟩).val, by simpa using (S.equivFin ⟨m, h⟩).isLt⟩
      else ⟨0, hS⟩ }

/-- **Phase B.2**: sub-code error は元 code の errorProbAt で上から抑えられる。 -/
theorem Code.subcode_errorProbAt_le
    {M n : ℕ} (c : Code M n α β) (W : Channel α β) [IsMarkovKernel W]
    (S : Finset (Fin M)) (hS : 0 < S.card) (m' : Fin S.card) :
    (c.subcode S hS).errorProbAt W m'
      ≤ c.errorProbAt W (S.equivFin.symm ⟨m', by simpa using m'.isLt⟩).val := by
  classical
  -- Notation: `m₀_sub : ↑S` is `S.equivFin.symm ⟨m'.val, _⟩`; `m₀ : Fin M` is its `.val`.
  set m₀_sub : ↑S := S.equivFin.symm ⟨m'.val, by simpa using m'.isLt⟩ with hm₀_sub_def
  set m₀ : Fin M := m₀_sub.val with hm₀_def
  have hm₀_mem : m₀ ∈ S := m₀_sub.property
  -- Encoder coincidence: (subcode).encoder m' = c.encoder m₀.
  have h_enc_eq : (c.subcode S hS).encoder m' = c.encoder m₀ := by
    show c.encoder (S.equivFin.symm ⟨m'.val, by simpa using m'.isLt⟩).val
        = c.encoder m₀
    rfl
  -- The two `Measure.pi` factors coincide.
  have h_meas_eq :
      Measure.pi (fun i => W ((c.subcode S hS).encoder m' i))
        = Measure.pi (fun i => W (c.encoder m₀ i)) := by
    rfl
  -- Set inclusion: (subcode).errorEvent m' ⊆ c.errorEvent m₀.
  have h_subset : (c.subcode S hS).errorEvent m' ⊆ c.errorEvent m₀ := by
    intro y hy
    rw [Code.mem_errorEvent] at hy ⊢
    -- hy : (subcode).decoder y ≠ m'.
    -- Goal: c.decoder y ≠ m₀.
    intro h_eq
    apply hy
    -- Show (subcode).decoder y = m'.
    show (if h : c.decoder y ∈ S then
            (⟨(S.equivFin ⟨c.decoder y, h⟩).val, by simpa using (S.equivFin ⟨c.decoder y, h⟩).isLt⟩
              : Fin S.card)
          else ⟨0, hS⟩) = m'
    have h_mem : c.decoder y ∈ S := h_eq ▸ hm₀_mem
    rw [dif_pos h_mem]
    -- Now show: ⟨(S.equivFin ⟨c.decoder y, h_mem⟩).val, _⟩ = m'.
    have h_efy_eq : S.equivFin ⟨c.decoder y, h_mem⟩ = ⟨m'.val, by simpa using m'.isLt⟩ := by
      have h_subS_eq : (⟨c.decoder y, h_mem⟩ : ↑S) = m₀_sub := by
        apply Subtype.ext
        simp [hm₀_def, h_eq]
      rw [h_subS_eq, hm₀_sub_def, Equiv.apply_symm_apply]
    -- Conclude.
    apply Fin.ext
    rw [h_efy_eq]
  -- Conclude with measure monotonicity.
  show Measure.pi (fun i => W ((c.subcode S hS).encoder m' i))
        ((c.subcode S hS).errorEvent m') ≤
      Measure.pi (fun i => W (c.encoder m₀ i)) (c.errorEvent m₀)
  rw [h_meas_eq]
  exact measure_mono h_subset

/-- Helper: linearization `(fun n : ℕ => (n : ℝ) * c) → ∞` for `c > 0`. -/
private lemma tendsto_nat_mul_atTop {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * c) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr ?_
  intro b
  refine ⟨Nat.ceil (b / c) + 1, ?_⟩
  intro n hn
  have h_n_R : b / c ≤ (n : ℝ) := by
    have h1 : (b / c : ℝ) ≤ Nat.ceil (b / c) := Nat.le_ceil _
    have h2 : (Nat.ceil (b / c) : ℝ) ≤ (n : ℝ) := by
      have : Nat.ceil (b / c) ≤ n := Nat.le_of_succ_le hn
      exact_mod_cast this
    linarith
  have h_mul : b / c * c ≤ (n : ℝ) * c :=
    mul_le_mul_of_nonneg_right h_n_R hc.le
  rwa [div_mul_cancel₀ _ hc.ne'] at h_mul

/-- Helper: for `0 < R < R'`, eventually `2 * ⌈exp(n R)⌉ ≤ ⌈exp(n R')⌉`. -/
private lemma exists_N_two_ceil_exp_le
    {R R' : ℝ} (hR_pos : 0 < R) (hRR' : R < R') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      2 * Nat.ceil (Real.exp ((n : ℝ) * R))
        ≤ Nat.ceil (Real.exp ((n : ℝ) * R')) := by
  -- We show eventually `2 * exp(n R) + 2 ≤ exp(n R')`. Then
  -- `2 * ⌈exp(n R)⌉₊ ≤ 2 * (exp(n R) + 1) = 2 * exp(n R) + 2 ≤ exp(n R') ≤ ⌈exp(n R')⌉₊`.
  have h_delta_pos : 0 < R' - R := by linarith
  -- `exp(n R) → ∞` (since R > 0).
  have h_exp_R_tendsto :
      Filter.Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * R)) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_nat_mul_atTop hR_pos)
  -- `exp(n (R' - R)) → ∞`.
  have h_exp_delta_tendsto :
      Filter.Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (R' - R))) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_nat_mul_atTop h_delta_pos)
  -- `exp(n R) * (exp(n (R'-R)) - 2) - 2 → ∞`.
  -- We bound `exp(n (R'-R)) - 2 ≥ 1` eventually, and `exp(n R) → ∞`, so the product → ∞;
  -- subtracting 2 keeps it tending to ∞.
  -- Eventually `exp(n (R'-R)) ≥ 3`.
  have h_ev_delta_3 : ∀ᶠ n : ℕ in Filter.atTop, (3 : ℝ) ≤ Real.exp ((n : ℝ) * (R' - R)) :=
    h_exp_delta_tendsto.eventually_ge_atTop 3
  -- And `exp(n R) → ∞`, so eventually `exp(n R) ≥ b + 2` for any `b`.
  -- We use that `exp(n R) * 1 ≤ exp(n R) * (exp(n (R'-R)) - 2)` once
  -- `exp(n (R'-R)) ≥ 3`, i.e., `exp(n (R'-R)) - 2 ≥ 1`.
  -- So `exp(n R) ≤ exp(n R) * (exp(n (R'-R)) - 2) = exp(n R') - 2 * exp(n R)`.
  -- Hence `2 * exp(n R) + 2 ≤ exp(n R') + 2 - exp(n R)`. Hmm that's not tight enough.
  -- Try: `exp(n R') ≥ 3 * exp(n R)`, so `exp(n R') - 2 * exp(n R) ≥ exp(n R)`.
  -- Then `2 * exp(n R) + 2 ≤ exp(n R')` iff `2 ≤ exp(n R') - 2 * exp(n R)` iff `2 ≤ exp(n R)`.
  -- So we need `exp(n R) ≥ 2` AND `exp(n (R'-R)) ≥ 3`. Both hold eventually.
  have h_ev_exp_R_2 : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ Real.exp ((n : ℝ) * R) :=
    h_exp_R_tendsto.eventually_ge_atTop 2
  rw [Filter.eventually_atTop] at h_ev_delta_3 h_ev_exp_R_2
  obtain ⟨N₁, hN₁⟩ := h_ev_delta_3
  obtain ⟨N₂, hN₂⟩ := h_ev_exp_R_2
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn1 : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn2 : N₂ ≤ n := (le_max_right _ _).trans hn
  have h_delta_ge : (3 : ℝ) ≤ Real.exp ((n : ℝ) * (R' - R)) := hN₁ n hn1
  have h_exp_R_ge : (2 : ℝ) ≤ Real.exp ((n : ℝ) * R) := hN₂ n hn2
  -- `exp(n R) * 3 ≤ exp(n R) * exp(n (R'-R)) = exp(n R')`.
  have h_exp_R_nn : 0 ≤ Real.exp ((n : ℝ) * R) := (Real.exp_pos _).le
  have h_expR'_eq : Real.exp ((n : ℝ) * R') = Real.exp ((n : ℝ) * R) * Real.exp ((n : ℝ) * (R' - R)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h_3R_le_R' : 3 * Real.exp ((n : ℝ) * R) ≤ Real.exp ((n : ℝ) * R') := by
    rw [h_expR'_eq, mul_comm (Real.exp ((n : ℝ) * R))]
    exact mul_le_mul_of_nonneg_right h_delta_ge h_exp_R_nn
  -- So `2 * exp(n R) + 2 ≤ 3 * exp(n R) ≤ exp(n R')` (using `exp(n R) ≥ 2`).
  have h_target_real : 2 * Real.exp ((n : ℝ) * R) + 2 ≤ Real.exp ((n : ℝ) * R') := by
    have : 2 * Real.exp ((n : ℝ) * R) + 2 ≤ 3 * Real.exp ((n : ℝ) * R) := by linarith
    linarith
  -- Now convert to `Nat.ceil` form.
  have h_lhs_real : ((2 * Nat.ceil (Real.exp ((n : ℝ) * R)) : ℕ) : ℝ)
      ≤ 2 * Real.exp ((n : ℝ) * R) + 2 := by
    have h_ceil_lt : (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) < Real.exp ((n : ℝ) * R) + 1 :=
      Nat.ceil_lt_add_one h_exp_R_nn
    push_cast
    linarith
  have h_rhs_real : Real.exp ((n : ℝ) * R')
      ≤ ((Nat.ceil (Real.exp ((n : ℝ) * R')) : ℕ) : ℝ) := Nat.le_ceil _
  have h_combined : ((2 * Nat.ceil (Real.exp ((n : ℝ) * R)) : ℕ) : ℝ)
      ≤ ((Nat.ceil (Real.exp ((n : ℝ) * R')) : ℕ) : ℝ) :=
    h_lhs_real.trans (h_target_real.trans h_rhs_real)
  exact_mod_cast h_combined

/-- **Phase B.4**: Average error achievability → max error achievability。 -/
theorem channel_coding_achievability_max_error
    (W : Channel α β) [IsMarkovKernel W]
    (p : Measure α) [IsProbabilityMeasure p]
    (hp_pos : ∀ a : α, 0 < p.real {a})
    (hW_pos : ∀ a : α, ∀ b : β, 0 < (W a).real {b})
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (mutualInfoOfChannel p W).toReal)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        ∀ m, (c.errorProbAt W m).toReal < ε := by
  classical
  -- Step 1: rate slack. Define `R' := (R + I)/2` so `R < R' < I`.
  set I : ℝ := (mutualInfoOfChannel p W).toReal with hI_def
  set R' : ℝ := (R + I) / 2 with hR'_def
  have hI_pos : 0 < I := lt_trans hR_pos hR
  have hR_lt_R' : R < R' := by rw [hR'_def]; linarith
  have hR'_lt_I : R' < I := by rw [hR'_def]; linarith
  have hR'_pos : 0 < R' := lt_trans hR_pos hR_lt_R'
  -- Step 2: smaller error target. `ε' := ε/4`.
  set ε' : ℝ := ε / 4 with hε'_def
  have hε'_pos : 0 < ε' := by rw [hε'_def]; linarith
  -- Step 3: apply existing average-error achievability.
  obtain ⟨N₀, hN₀⟩ := channel_coding_achievability W p hp_pos hW_pos hR'_pos hR'_lt_I hε'_pos
  -- Step 4: rate-asymptotic claim.
  obtain ⟨N_rate, hN_rate⟩ := exists_N_two_ceil_exp_le hR_pos hR_lt_R'
  -- Final N.
  refine ⟨max N₀ N_rate, ?_⟩
  intro n hn
  have hn0 : N₀ ≤ n := (le_max_left _ _).trans hn
  have hn1 : N_rate ≤ n := (le_max_right _ _).trans hn
  obtain ⟨M, hM_lb, c, h_avg_lt⟩ := hN₀ n hn0
  -- Apply B.1 (K = 2) and B.2.
  have hK : (1 : ℝ) < 2 := by norm_num
  have h_filter_bound :=
    errorProbAt_filter_card_bound (M := M) (n := n) c W hK
  -- Let T be the bad-message filter, S the good-message filter.
  set T : Finset (Fin M) := (Finset.univ : Finset (Fin M)).filter
      (fun m => 2 * (c.averageErrorProb W).toReal < (c.errorProbAt W m).toReal) with hT_def
  set S : Finset (Fin M) := (Finset.univ : Finset (Fin M)).filter
      (fun m => (c.errorProbAt W m).toReal ≤ 2 * (c.averageErrorProb W).toReal) with hS_def
  -- T and S are complements in Finset.univ.
  have hST_partition : S.card + T.card = M := by
    have h_union : S ∪ T = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro m
      rw [Finset.mem_union, hS_def, hT_def, Finset.mem_filter, Finset.mem_filter]
      rcases le_or_gt ((c.errorProbAt W m).toReal) (2 * (c.averageErrorProb W).toReal) with h | h
      · exact Or.inl ⟨Finset.mem_univ m, h⟩
      · exact Or.inr ⟨Finset.mem_univ m, h⟩
    have h_disj : Disjoint S T := by
      rw [hS_def, hT_def]
      refine Finset.disjoint_filter.mpr ?_
      intro m _ hm
      exact not_lt_of_ge hm
    have := Finset.card_union_of_disjoint h_disj
    rw [h_union, Finset.card_univ, Fintype.card_fin] at this
    linarith
  -- From h_filter_bound, T.card * 2 ≤ M (as Reals, so as Nats).
  have h_T_card_le : 2 * T.card ≤ M := by
    have h_real : ((T.card : ℝ) * 2 : ℝ) ≤ (M : ℝ) := h_filter_bound
    have h_real' : ((2 * T.card : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h_real'
  -- So `S.card = M - T.card ≥ M - M/2 ≥ ⌈M/2⌉ (as Nat division)`.
  -- More directly: 2 * S.card ≥ M (using S.card + T.card = M and 2*T.card ≤ M).
  have h_2S_ge_M : M ≤ 2 * S.card := by
    have : M = S.card + T.card := hST_partition.symm
    omega
  -- And M ≥ ⌈exp(n R')⌉, and 2 * ⌈exp(n R)⌉ ≤ ⌈exp(n R')⌉.
  have h_rate_inequality : 2 * Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ 2 * S.card := by
    calc 2 * Nat.ceil (Real.exp ((n : ℝ) * R))
        ≤ Nat.ceil (Real.exp ((n : ℝ) * R')) := hN_rate n hn1
      _ ≤ M := hM_lb
      _ ≤ 2 * S.card := h_2S_ge_M
  -- Hence ⌈exp(n R)⌉ ≤ S.card.
  have h_ceil_le_S_card : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ S.card := by
    have h2 : (2 : ℕ) > 0 := by norm_num
    exact Nat.le_of_mul_le_mul_left h_rate_inequality h2
  -- S.card > 0 (because ⌈exp(n R)⌉ ≥ 1 for n R ≥ 0 — yes since R > 0).
  have h_exp_nR_pos : 0 ≤ (n : ℝ) * R := mul_nonneg (Nat.cast_nonneg _) hR_pos.le
  have h_exp_nR_ge_1 : 1 ≤ Real.exp ((n : ℝ) * R) :=
    Real.one_le_exp h_exp_nR_pos
  have h_ceil_ge_1 : 1 ≤ Nat.ceil (Real.exp ((n : ℝ) * R)) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Nat.ceil_eq_zero, not_le]
    exact lt_of_lt_of_le zero_lt_one h_exp_nR_ge_1
  have hS_pos : 0 < S.card := lt_of_lt_of_le h_ceil_ge_1 h_ceil_le_S_card
  -- Build the subcode.
  refine ⟨S.card, h_ceil_le_S_card, c.subcode S hS_pos, ?_⟩
  intro m'
  -- The error bound: each subcode error ≤ 2 * avg < 2 * ε' = ε/2 < ε.
  have h_sub_le := c.subcode_errorProbAt_le W S hS_pos m'
  set m₀ : Fin M := (S.equivFin.symm ⟨m'.val, by simpa using m'.isLt⟩).val with hm₀_def
  have hm₀_mem : m₀ ∈ S := (S.equivFin.symm ⟨m'.val, by simpa using m'.isLt⟩).property
  -- m₀ ∈ S means errorProbAt c W m₀ ≤ 2 * avg.
  have h_m₀_le : (c.errorProbAt W m₀).toReal ≤ 2 * (c.averageErrorProb W).toReal := by
    rw [hS_def, Finset.mem_filter] at hm₀_mem
    exact hm₀_mem.2
  -- Convert h_sub_le to .toReal.
  have h_sub_le_top : c.errorProbAt W m₀ ≠ ∞ := by
    haveI : IsProbabilityMeasure (Measure.pi (fun i => W (c.encoder m₀ i))) := by infer_instance
    exact ((prob_le_one (μ := Measure.pi (fun i => W (c.encoder m₀ i))) (s := c.errorEvent m₀)).trans_lt ENNReal.one_lt_top).ne
  have h_sub_le_toReal :
      ((c.subcode S hS_pos).errorProbAt W m').toReal ≤ (c.errorProbAt W m₀).toReal :=
    (ENNReal.toReal_le_toReal
      (ne_top_of_le_ne_top h_sub_le_top h_sub_le) h_sub_le_top).mpr h_sub_le
  -- Combine.
  calc ((c.subcode S hS_pos).errorProbAt W m').toReal
      ≤ (c.errorProbAt W m₀).toReal := h_sub_le_toReal
    _ ≤ 2 * (c.averageErrorProb W).toReal := h_m₀_le
    _ < 2 * ε' := by
        have : (c.averageErrorProb W).toReal < ε' := h_avg_lt
        linarith
    _ = ε / 2 := by rw [hε'_def]; ring
    _ < ε := by linarith

/-! ## Phase C — Full support 仮定除去 (skeleton)

`p` 側 `hp_pos` を sub-channel 切り出しで vacuous 化。`α_supp := {a | 0 < p {a}}` 上で
restrict した sub-channel での MI が元の MI と一致。 -/

/-- **Phase C.1 (skeleton)**: `α_supp := {a | 0 < p.real {a}}` 上で restrict した
`(p|_supp, W|_supp)` の MI は元の `mutualInfoOfChannel p W` と一致。 -/
theorem mutualInfoOfChannel_restrict_to_support
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] :
    mutualInfoOfChannel p W
      = mutualInfoOfChannel
          (p.comap (Subtype.val : {a : α // 0 < p.real {a}} → α))
          (W.comap (Subtype.val : {a : α // 0 < p.real {a}} → α)
            (Measurable.subtype_val measurable_id)) := by
  sorry

/-- **Phase C.2 (skeleton)**: `Code` の subtype lift。`Code M n {a // 0 < p.real {a}} β` から
`Code M n α β` への injection。encoder の codomain を `Subtype → α` で expansion、`errorProbAt`
は不変。 -/
noncomputable def Code_lift_from_subtype
    {M n : ℕ} (p : Measure α)
    (c : Code M n {a : α // 0 < p.real {a}} β) : Code M n α β := by
  sorry

/-! ## Phase D — 主定理 (skeleton) -/

/-- **D-1 主定理 (Cover-Thomas 7.7.1 完全形)**: 任意 `R < capacity W` と任意 `ε > 0` で
十分大きい block 長 `n` で max error < ε を達成する `M ≥ exp(n R)` 個の符号が存在。

Proof shape:
1. Phase A.4 で `R < capacity W ⟹ ∃ p ∈ stdSimplex, R < I(p; W).toReal`。
2. Phase C.1 で `p` の support 制限 (full-support `p'` を取得)。
3. Phase B.4 (average → max wrap) を call。

注意: `hW_pos` 完全除去は本 plan scope では sub-channel 内で吸収。完全形は別 deferred plan。 -/
theorem shannon_noisy_channel_coding_theorem
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR_pos : 0 < R) (hR : R < capacity W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        ∀ m, (c.errorProbAt W m).toReal < ε := by
  sorry

end InformationTheory.Shannon.ChannelCoding
