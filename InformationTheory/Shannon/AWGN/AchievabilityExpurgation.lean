import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.KLCapacityAndAEP
import InformationTheory.Shannon.AWGN.PerCodewordPowerConstraint
import InformationTheory.Shannon.AWGN.ConverseMIChainRule
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.AWGN.AchievabilityCodebook
import InformationTheory.Shannon.AWGN.AchievabilityTypicalDecoder
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Expurgation, power-constraint witness, and code extraction

The expurgation and feasibility apparatus for AWGN achievability (Cover–Thomas
9.2): worst-half expurgation, the power-constraint slack witness producing a
strictly smaller variance, and the bridge from a deterministic codebook to the
`AwgnCode` type.

## Main statements

* `awgn_exists_codebook_le_avg` — a codebook attaining the average error bound.
* `awgn_expurgate_worst_half` — worst-half expurgation keeps `M/2` good indices.
* `awgnPowerWitness_exists` — a strictly smaller variance `P' < P` with `R`
  still below `capacity(P')`.
* `awgn_extract_AwgnCode` — packages a deterministic codebook into an `AwgnCode`.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Expurgation -/

/-- If the codebook-average of `Pe` is at most `B`, then some specific codebook
achieves `Pe ≤ B`. -/
@[entry_point]
theorem awgn_exists_codebook_le_avg
    {M n : ℕ} (σsq : ℝ≥0)
    (Pe : (Fin M → Fin n → ℝ) → ℝ≥0∞)
    (hPe_aemeas : AEMeasurable Pe (gaussianCodebook M n σsq))
    {B : ℝ≥0∞}
    (h_avg : ∫⁻ c, Pe c ∂(gaussianCodebook M n σsq) ≤ B) :
    ∃ c_specific : Fin M → Fin n → ℝ, Pe c_specific ≤ B := by
  obtain ⟨c, hc⟩ := exists_le_lintegral hPe_aemeas
  exact ⟨c, hc.trans h_avg⟩

/-- Worst-half expurgation: if the sum of `Pe m` is bounded by `M · (2ε)`, then
at least `M/2` indices `m` satisfy `Pe m ≤ 4ε`. -/
@[entry_point]
theorem awgn_expurgate_worst_half
    {M : ℕ} (hM : 2 ≤ M)
    (Pe : Fin M → ℝ) (hPe_nn : ∀ m, 0 ≤ Pe m) {ε : ℝ} (hε : 0 < ε)
    (h_avg : (∑ m, Pe m) ≤ (M : ℝ) * (2 * ε)) :
    ∃ S : Finset (Fin M), M / 2 ≤ S.card ∧ ∀ m ∈ S, Pe m ≤ 4 * ε := by
  classical
  refine ⟨Finset.univ.filter (fun m ↦ Pe m ≤ 4 * ε), ?_, ?_⟩
  · -- card ≥ M/2 via contrapositive on the "bad" filter
    by_contra hlt
    push Not at hlt
    set S_good : Finset (Fin M) :=
      Finset.univ.filter (fun m : Fin M ↦ Pe m ≤ 4 * ε) with hS_good
    set S_bad : Finset (Fin M) :=
      Finset.univ.filter (fun m : Fin M ↦ ¬ Pe m ≤ 4 * ε) with hS_bad
    have h_card_sum : S_good.card + S_bad.card = M := by
      have h := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin M))) (fun m : Fin M ↦ Pe m ≤ 4 * ε)
      have hu : (Finset.univ : Finset (Fin M)).card = M := by
        simp [Finset.card_univ, Fintype.card_fin]
      simp [hu] at h
      simpa [S_good, S_bad] using h
    have h_card_bad_gt : M / 2 < S_bad.card := by omega
    have h_two_le_card_bad : M / 2 + 1 ≤ S_bad.card := h_card_bad_gt
    -- Real lower bound on S_bad.card.
    have h_two_card_lb_nat : M < 2 * S_bad.card := by
      have h_div : 2 * (M / 2) + M % 2 = M := Nat.div_add_mod M 2 |>.symm ▸ by
        omega
      have h_mod_lt : M % 2 < 2 := Nat.mod_lt M (by norm_num)
      omega
    have h_two_card_lb : (M : ℝ) < 2 * (S_bad.card : ℝ) := by
      have := h_two_card_lb_nat
      have h_cast : ((2 * S_bad.card : ℕ) : ℝ) = 2 * (S_bad.card : ℝ) := by push_cast; ring
      have : (M : ℝ) < ((2 * S_bad.card : ℕ) : ℝ) := by exact_mod_cast this
      linarith [h_cast]
    -- Pe m > 4ε on S_bad.
    have h_strict : ∀ m ∈ S_bad, 4 * ε < Pe m := by
      intro m hm
      have := (Finset.mem_filter.mp hm).2
      push Not at this
      exact this
    have h_nonempty : S_bad.Nonempty := by
      have : 0 < S_bad.card := by omega
      exact Finset.card_pos.mp this
    have h_sum_bad_lb : (S_bad.card : ℝ) * (4 * ε) < ∑ m ∈ S_bad, Pe m := by
      have hsum_lt :
          ∑ _m ∈ S_bad, (4 * ε) < ∑ m ∈ S_bad, Pe m :=
        Finset.sum_lt_sum_of_nonempty h_nonempty h_strict
      have hconst : ∑ _m ∈ S_bad, (4 * ε) = (S_bad.card : ℝ) * (4 * ε) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      linarith
    have h_sub_le : ∑ m ∈ S_bad, Pe m ≤ ∑ m, Pe m :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun m _ _ ↦ hPe_nn m)
    -- Combine: M * 2ε < 2 * S_bad.card * 2ε = S_bad.card * 4ε < ∑ Pe ≤ M * 2ε. Contradiction.
    nlinarith [h_two_card_lb, h_sum_bad_lb, h_sub_le, h_avg, hε]
  · intro m hm
    exact (Finset.mem_filter.mp hm).2

/-! ## Power constraint and feasibility witness

The per-codeword power-constraint bound `awgnPowerConstraintPerCodeword_holds`
lives in `InformationTheory/Shannon/AWGN/PerCodewordPowerConstraint.lean`. The
achievability assembly
also needs a shared slack witness `∃ P' ∈ (0, P)` with `R < capacity(P')`,
supplied by `awgnPowerWitness_exists` below, which returns a strict `P' < P` (the
variance-level slack `(P'.toNNReal : ℝ) < P` required by the per-codeword
bound). -/

/-- The power-constraint slack witness.

Given `R < capacity(P) = (1/2) log(1 + P/N)`, produce a strictly smaller variance
`P' ∈ (0, P)` for which the rate `R` is still below `capacity(P')`. The strict
`P' < P` is genuinely required by `awgnPowerConstraintPerCodeword_holds` (its
`(P_cb.toNNReal : ℝ) < P_target` slack argument); the witness must therefore
deliver a true strict inequality, never a non-strict one fabricated from `≤`.

Construction: `capacity` is continuous and strictly increasing in the variance;
`R < capacity(P)` lies strictly below the value at `P`, so by continuity there is
a left neighbourhood of `P` on which the capacity still exceeds `R`. Picking any
`P'` in that neighbourhood with `0 < P' < P` works.
@audit:ok -/
@[entry_point]
theorem awgnPowerWitness_exists (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (1/2) * Real.log (1 + P / (N : ℝ))) :
    ∃ P', 0 < P' ∧ P' < P ∧ R < (1/2) * Real.log (1 + P' / (N : ℝ)) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) :=
    lt_of_le_of_ne N.coe_nonneg (fun h ↦ hN h.symm)
  -- `R < (1/2) log(1 + P/N)` ⟺ `2R < log(1 + P/N)` ⟺ `exp(2R) < 1 + P/N`.
  have hlogP : 2 * R < Real.log (1 + P / (N : ℝ)) := by linarith
  have harg_P_pos : (0 : ℝ) < 1 + P / (N : ℝ) := by positivity
  have hexp_lt : Real.exp (2 * R) < 1 + P / (N : ℝ) :=
    (Real.lt_log_iff_exp_lt harg_P_pos).mp hlogP
  -- Lower bound on admissible variance: `P_min := N · (exp(2R) − 1)`.
  set t : ℝ := Real.exp (2 * R) with ht_def
  have ht_gt_one : (1 : ℝ) < t := by
    rw [ht_def]; exact Real.one_lt_exp_iff.mpr (by linarith)
  set Pmin : ℝ := (N : ℝ) * (t - 1) with hPmin_def
  have hPmin_pos : 0 < Pmin := by
    rw [hPmin_def]; have : 0 < t - 1 := by linarith
    positivity
  -- `exp(2R) < 1 + P/N` rearranges to `Pmin < P`.
  have hPmin_lt_P : Pmin < P := by
    rw [hPmin_def]
    have h1 : t - 1 < P / (N : ℝ) := by linarith
    have h2 : (N : ℝ) * (t - 1) < (N : ℝ) * (P / (N : ℝ)) :=
      mul_lt_mul_of_pos_left h1 hN_pos
    rwa [mul_div_cancel₀ P (ne_of_gt hN_pos)] at h2
  -- Pick the midpoint `P' := (Pmin + P)/2 ∈ (Pmin, P)`.
  set P' : ℝ := (Pmin + P) / 2 with hP'_def
  have hP'_pos : 0 < P' := by rw [hP'_def]; linarith
  have hP'_lt_P : P' < P := by rw [hP'_def]; linarith
  have hP'_gt_Pmin : Pmin < P' := by rw [hP'_def]; linarith
  refine ⟨P', hP'_pos, hP'_lt_P, ?_⟩
  -- `P' > Pmin = N(t-1)` ⟹ `t - 1 < P'/N` ⟹ `t < 1 + P'/N`.
  have h1 : t - 1 < P' / (N : ℝ) := by
    rw [lt_div_iff₀ hN_pos]
    have := hP'_gt_Pmin; rw [hPmin_def] at this; linarith
  have harg_P'_pos : (0 : ℝ) < 1 + P' / (N : ℝ) := by
    have : 0 < P' / (N : ℝ) := div_pos hP'_pos hN_pos; linarith
  have hexp_lt' : Real.exp (2 * R) < 1 + P' / (N : ℝ) := by
    rw [← ht_def]; linarith
  have hlogP' : 2 * R < Real.log (1 + P' / (N : ℝ)) :=
    (Real.lt_log_iff_exp_lt harg_P'_pos).mpr hexp_lt'
  linarith

/-- Bridge to the `AwgnCode` type from a deterministic codebook satisfying both
the per-message error bound and the per-message power constraint, using
`jointTypicalDecoder` as the decoder and converting the `ℝ≥0∞`-valued error
bound to the `< 5ε` real-valued slack. -/
@[entry_point]
theorem awgn_extract_AwgnCode
    {P : ℝ} {N : ℝ≥0}
    (h_meas : IsAwgnChannelMeasurable N) {n : ℕ}
    {M : ℕ} [NeZero M]
    {ε : ℝ} (hε : 0 < ε)
    {A : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hA_meas : MeasurableSet A)
    (codebook : Fin M → Fin n → ℝ)
    (h_max_Pe : ∀ m,
        (Measure.pi (fun i ↦ awgnChannel N h_meas (codebook m i)))
          ((InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              codebook (jointTypicalDecoder A codebook)).errorEvent m)
        ≤ ENNReal.ofReal (4 * ε))
    (h_power : ∀ m, (∑ i, (codebook m i)^2) ≤ (n : ℝ) * P) :
    ∃ c : AwgnCode M n P,
      ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < 5 * ε := by
  refine ⟨{
    encoder := codebook
    decoder := jointTypicalDecoder A codebook
    decoder_meas := jointTypicalDecoder_measurable A hA_meas codebook
    power_constraint := h_power
  }, ?_⟩
  intro m
  -- toCode.errorProbAt = (Measure.pi (W ∘ encoder m)) (errorEvent ...).
  -- Pe ≤ 4ε in ℝ≥0∞ + 4ε.toReal = 4ε < 5ε.
  have h_pe_le := h_max_Pe m
  -- The body of c.toCode.errorProbAt for our AwgnCode equals the LHS in h_max_Pe.
  have h_eq :
      (({ encoder := codebook
          decoder := jointTypicalDecoder A codebook
          decoder_meas := jointTypicalDecoder_measurable A hA_meas codebook
          power_constraint := h_power : AwgnCode M n P }).toCode.errorProbAt
            (awgnChannel N h_meas) m)
      = (Measure.pi (fun i ↦ awgnChannel N h_meas (codebook m i)))
          ((InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              codebook (jointTypicalDecoder A codebook)).errorEvent m) := rfl
  rw [h_eq]
  -- Now compare with ENNReal.ofReal (4 * ε) ≤ ENNReal.ofReal (5 * ε), take .toReal.
  have h_target : (ENNReal.ofReal (4 * ε)).toReal < 5 * ε := by
    rw [ENNReal.toReal_ofReal (by positivity)]
    linarith
  have h_ne_top : (ENNReal.ofReal (4 * ε)) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ((Measure.pi (fun i ↦ awgnChannel N h_meas (codebook m i)))
          ((InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              codebook (jointTypicalDecoder A codebook)).errorEvent m)).toReal
      ≤ (ENNReal.ofReal (4 * ε)).toReal := by
        apply ENNReal.toReal_mono h_ne_top h_pe_le
    _ < 5 * ε := h_target

lemma exists_two_mul_ceil_exp_le_ceil_exp_of_lt {R R'' : ℝ} (hR_nonneg : 0 ≤ R)
    (hR_lt_R'' : R < R'') :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      2 * Nat.ceil (Real.exp ((n : ℝ) * R))
        ≤ Nat.ceil (Real.exp ((n : ℝ) * R'')) := by
  -- Pick `N₀ = ⌈(log 4) / (R'' - R)⌉` so that for n ≥ N₀,
  -- `exp(n(R''-R)) ≥ 4`, hence `exp(n R'') ≥ 4 * exp(n R)`. Then
  -- `2 * ⌈exp(n R)⌉ ≤ 2 * (exp(n R) + 1) ≤ 4 * exp(n R) ≤ exp(n R'') ≤ ⌈exp(n R'')⌉`.
  set δd : ℝ := R'' - R with hδd_def
  have hδd_pos : 0 < δd := by linarith
  -- Need `n * δd ≥ log 4`, i.e., `n ≥ log 4 / δd`.
  set N₀ : ℕ := Nat.ceil (Real.log 4 / δd) with hN₀_def
  refine ⟨N₀, fun n hn ↦ ?_⟩
  -- Cast `(N₀ : ℝ) ≤ (n : ℝ)`.
  have h_ndelta : Real.log 4 / δd ≤ (n : ℝ) := by
    have h_cast : ((N₀ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    calc Real.log 4 / δd ≤ (Nat.ceil (Real.log 4 / δd) : ℝ) := Nat.le_ceil _
      _ = (N₀ : ℝ) := by rfl
      _ ≤ (n : ℝ) := h_cast
  have h_exp_n_delta_ge_4 : (4 : ℝ) ≤ Real.exp ((n : ℝ) * δd) := by
    have h_n_delta : Real.log 4 ≤ (n : ℝ) * δd := by
      have := (div_le_iff₀ hδd_pos).mp h_ndelta
      linarith
    have := Real.exp_le_exp.mpr h_n_delta
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 4)] at this
  have h_exp_R''_ge : Real.exp ((n : ℝ) * R'') =
      Real.exp ((n : ℝ) * R) * Real.exp ((n : ℝ) * δd) := by
    rw [← Real.exp_add]; congr 1; ring
  have h_exp_R_pos : 0 < Real.exp ((n : ℝ) * R) := Real.exp_pos _
  have h_exp_R_ge_one : 1 ≤ Real.exp ((n : ℝ) * R) := by
    apply Real.one_le_exp
    exact mul_nonneg (Nat.cast_nonneg n) hR_nonneg
  -- 2 * ⌈exp(nR)⌉ ≤ 2 * (exp(nR) + 1) ≤ 4 * exp(nR) ≤ exp(nR'') ≤ ⌈exp(nR'')⌉.
  have h_ceil_R_le : (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ)
      ≤ Real.exp ((n : ℝ) * R) + 1 := by
    exact (Nat.ceil_lt_add_one (le_of_lt h_exp_R_pos)).le
  have h_two_ceil_R_le : (2 * Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ)
      ≤ 4 * Real.exp ((n : ℝ) * R) := by
    have : (2 : ℝ) * (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ)
        ≤ 2 * (Real.exp ((n : ℝ) * R) + 1) := by
      linarith
    calc (2 * Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ)
        = 2 * (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) := by norm_cast
      _ ≤ 2 * (Real.exp ((n : ℝ) * R) + 1) := this
      _ ≤ 2 * Real.exp ((n : ℝ) * R) + 2 * Real.exp ((n : ℝ) * R) := by linarith
      _ = 4 * Real.exp ((n : ℝ) * R) := by ring
  have h_4_le_R'' : (4 : ℝ) * Real.exp ((n : ℝ) * R) ≤ Real.exp ((n : ℝ) * R'') := by
    rw [h_exp_R''_ge]
    have : (4 : ℝ) * Real.exp ((n : ℝ) * R)
        ≤ Real.exp ((n : ℝ) * δd) * Real.exp ((n : ℝ) * R) := by
      nlinarith [h_exp_R_pos]
    linarith [this, mul_comm (Real.exp ((n : ℝ) * R)) (Real.exp ((n : ℝ) * δd))]
  have h_le_R'' : (2 * Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ)
      ≤ Real.exp ((n : ℝ) * R'') := le_trans h_two_ceil_R_le h_4_le_R''
  -- Conclude via Nat.le_ceil.
  have : (2 * Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ)
      ≤ (Nat.ceil (Real.exp ((n : ℝ) * R'')) : ℝ) :=
    le_trans h_le_R'' (Nat.le_ceil _)
  exact_mod_cast this

end InformationTheory.Shannon.AWGN
