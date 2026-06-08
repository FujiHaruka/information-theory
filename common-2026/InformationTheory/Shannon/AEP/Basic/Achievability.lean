import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Bridge
import InformationTheory.Shannon.Han.Basic
import InformationTheory.Shannon.Pi
import InformationTheory.Shannon.DPI
import InformationTheory.Shannon.SlepianWolf.Basic
import InformationTheory.Fano.Measure
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecificLimits.Basic
import InformationTheory.Shannon.AEP.Basic.Core
import InformationTheory.Shannon.AEP.Basic.Converse

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Real
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Phase E — 源符号化定理 achievability

Phase E は source-coding achievability (Cover-Thomas Theorem 5.4.2) を `Tendsto` 形で
立てる。`M_n := ⌈exp(n · R)⌉` を取り、typical set ↔ `Fin M_n` の bijection で encoder /
decoder を構成、`typicalSet_prob_tendsto_one` で error rate → 0、`Nat.le_ceil` /
`Nat.ceil_lt_add_one` の squeeze で `log M_n / n → R`。

詳細: [`docs/shannon/aep-achievability-plan.md`](../../docs/shannon/aep-achievability-plan.md).
-/

/-- The codebook size used in the achievability proof: `M_n := ⌈exp(n · R)⌉`. -/
noncomputable def codebookSize (R : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (Real.exp ((n : ℝ) * R))

/-- `M_n ≥ 1` (so `Fin M_n` is `Nonempty`). -/
lemma codebookSize_pos (R : ℝ) (n : ℕ) : 0 < codebookSize R n := by
  unfold codebookSize
  exact Nat.ceil_pos.mpr (Real.exp_pos _)

instance codebookSize_neZero (R : ℝ) (n : ℕ) : NeZero (codebookSize R n) :=
  ⟨(codebookSize_pos R n).ne'⟩

/-- Cardinality of typical set is ≤ `M_n` (provided `H + ε ≤ R` and `hpos`). -/
lemma typicalSet_card_le_codebookSize
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (n : ℕ) {ε R : ℝ} (hε : 0 < ε) (h_le : entropy μ (Xs 0) + ε ≤ R) :
    (typicalSet μ Xs n ε).toFinite.toFinset.card ≤ codebookSize R n := by
  -- card ≤ exp(n(H+ε)) ≤ exp(nR) ≤ ⌈exp(nR)⌉ = M_n.
  have h_card_le_exp := typicalSet_card_le μ Xs hXs hpos n hε
  have h_mono_arg : (n : ℝ) * (entropy μ (Xs 0) + ε) ≤ (n : ℝ) * R := by
    exact mul_le_mul_of_nonneg_left h_le (Nat.cast_nonneg n)
  have h_exp_mono : Real.exp ((n : ℝ) * (entropy μ (Xs 0) + ε))
      ≤ Real.exp ((n : ℝ) * R) := Real.exp_le_exp.mpr h_mono_arg
  have h_chain : ((typicalSet μ Xs n ε).toFinite.toFinset.card : ℝ)
      ≤ Real.exp ((n : ℝ) * R) := h_card_le_exp.trans h_exp_mono
  have h_le_ceil : Real.exp ((n : ℝ) * R) ≤ (codebookSize R n : ℝ) := by
    unfold codebookSize
    exact Nat.le_ceil _
  have h_card_le_R : ((typicalSet μ Xs n ε).toFinite.toFinset.card : ℝ)
      ≤ (codebookSize R n : ℝ) := h_chain.trans h_le_ceil
  exact_mod_cast h_card_le_R

/-- The encoder: typical blocks → `Fin M_n` index, non-typical → 0. -/
noncomputable def aepEncoder
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (n : ℕ) (ε R : ℝ)
    (h_card_le : (typicalSet μ Xs n ε).toFinite.toFinset.card ≤ codebookSize R n) :
    (Fin n → α) → Fin (codebookSize R n) := by
  classical
  intro x
  by_cases hx : x ∈ (typicalSet μ Xs n ε).toFinite.toFinset
  · -- typical: equivFin index, cast into Fin M_n.
    exact Fin.castLE h_card_le ((typicalSet μ Xs n ε).toFinite.toFinset.equivFin ⟨x, hx⟩)
  · -- non-typical: default index 0.
    exact ⟨0, codebookSize_pos R n⟩

/-- The decoder: `Fin M_n` index → typical block (out of range → default). -/
noncomputable def aepDecoder
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (n : ℕ) (ε R : ℝ) :
    Fin (codebookSize R n) → (Fin n → α) := by
  classical
  intro k
  by_cases hk : k.val < (typicalSet μ Xs n ε).toFinite.toFinset.card
  · -- in range: pull back via equivFin.symm, then take subtype value.
    exact ((typicalSet μ Xs n ε).toFinite.toFinset.equivFin.symm ⟨k.val, hk⟩).val
  · -- out of range: arbitrary block.
    exact fun _ => Classical.arbitrary α

omit [MeasurableSingletonClass α] in
/-- **Round-trip lemma**: `d_n ∘ c_n = id` on typical set. -/
lemma aepDecoder_aepEncoder_of_mem_typicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (n : ℕ) (ε R : ℝ)
    (h_card_le : (typicalSet μ Xs n ε).toFinite.toFinset.card ≤ codebookSize R n)
    (x : Fin n → α) (hx : x ∈ typicalSet μ Xs n ε) :
    aepDecoder μ Xs n ε R (aepEncoder μ Xs n ε R h_card_le x) = x := by
  classical
  -- x is in toFinset via Set.Finite.mem_toFinset.
  have hxF : x ∈ (typicalSet μ Xs n ε).toFinite.toFinset :=
    (Set.Finite.mem_toFinset _).mpr hx
  -- Unfold encoder on the `hxF` branch.
  unfold aepEncoder
  rw [dif_pos hxF]
  -- The cast preserves val, so it lands in range; equivFin.symm undoes equivFin.
  set s : Finset (Fin n → α) := (typicalSet μ Xs n ε).toFinite.toFinset with hs_def
  set k0 : Fin s.card := s.equivFin ⟨x, hxF⟩ with hk0_def
  -- Note: `(Fin.castLE h_card_le k0).val = k0.val < s.card`.
  have hcast_val : (Fin.castLE h_card_le k0).val = k0.val := rfl
  have hk0_lt : k0.val < s.card := k0.isLt
  -- Now unfold decoder on the in-range branch.
  unfold aepDecoder
  rw [dif_pos (by rw [hcast_val]; exact hk0_lt)]
  -- Show s.equivFin.symm ⟨k0.val, _⟩ = ⟨x, hxF⟩ (subtype) then take .val.
  have hsymm : s.equivFin.symm ⟨k0.val, hk0_lt⟩ = ⟨x, hxF⟩ := by
    have h1 : s.equivFin.symm (s.equivFin ⟨x, hxF⟩) = ⟨x, hxF⟩ :=
      s.equivFin.symm_apply_apply ⟨x, hxF⟩
    -- s.equivFin ⟨x, hxF⟩ has the same .val as k0, hence the input subtypes match.
    have heq : (⟨k0.val, hk0_lt⟩ : Fin s.card) = s.equivFin ⟨x, hxF⟩ := by
      apply Fin.ext
      rfl
    rw [heq]; exact h1
  -- Conclude: target is `(s.equivFin.symm ⟨(Fin.castLE … k0).val, …⟩).val = x`.
  show ((s.equivFin.symm ⟨(Fin.castLE h_card_le k0).val, _⟩) : ↑s).val = x
  -- After rewriting `Fin.castLE` val, we can apply `hsymm`.
  have : ((s.equivFin.symm ⟨k0.val, hk0_lt⟩ : ↑s) : Fin n → α) = x := by
    rw [hsymm]
  exact this

/-! #### Phase B — error rate Tendsto -/

omit [MeasurableSingletonClass α] in
/-- error event ⊆ {jointRV Xs n ∉ typicalSet}. The orientation matches
`errorProb`: `Xs ω ≠ decoder (encoder (Xs ω))`. -/
lemma error_subset_compl_typicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (n : ℕ) (ε R : ℝ)
    (h_card_le : (typicalSet μ Xs n ε).toFinite.toFinset.card ≤ codebookSize R n) :
    {ω | jointRV Xs n ω
            ≠ aepDecoder μ Xs n ε R (aepEncoder μ Xs n ε R h_card_le (jointRV Xs n ω))}
      ⊆ {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε} := by
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro hmem
  apply hω
  exact (aepDecoder_aepEncoder_of_mem_typicalSet μ Xs n ε R h_card_le _ hmem).symm

/-- error rate → 0. -/
lemma aep_errorProb_tendsto_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {ε R : ℝ} (hε : 0 < ε) (h_le : entropy μ (Xs 0) + ε ≤ R) :
    Tendsto
      (fun n => InformationTheory.MeasureFano.errorProb μ
                  (jointRV Xs n)
                  (fun ω => aepEncoder μ Xs n ε R
                              (typicalSet_card_le_codebookSize μ Xs hXs hpos n hε h_le)
                              (jointRV Xs n ω))
                  (aepDecoder μ Xs n ε R))
      atTop (𝓝 0) := by
  -- Sandwich: 0 ≤ errorProb n ≤ μ.real { ω | jointRV Xs n ω ∉ typicalSet ... } → 0.
  set h_card : ∀ n, (typicalSet μ Xs n ε).toFinite.toFinset.card ≤ codebookSize R n :=
    fun n => typicalSet_card_le_codebookSize μ Xs hXs hpos n hε h_le with h_card_def
  -- Upper-bound: error event ⊆ ∁ typicalSet (orientation matches `errorProb`).
  have h_subset : ∀ n,
      {ω | jointRV Xs n ω
              ≠ aepDecoder μ Xs n ε R
                  ((fun ω => aepEncoder μ Xs n ε R (h_card n) (jointRV Xs n ω)) ω)}
        ⊆ {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε} := by
    intro n
    exact error_subset_compl_typicalSet μ Xs n ε R (h_card n)
  -- typicalSet measurable, complement measurable.
  have h_meas_T : ∀ n, MeasurableSet {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε} := by
    intro n
    exact (measurable_jointRV Xs hXs n) (measurableSet_typicalSet μ Xs n ε)
  -- complement of typical
  have h_meas_comp : ∀ n, MeasurableSet {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε} := by
    intro n; exact (h_meas_T n).compl
  -- μ {ω | not in typicalSet} → 0 (from typicalSet_prob_tendsto_one).
  have h_compl_tendsto :
      Tendsto (fun n => (μ {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε}).toReal)
        atTop (𝓝 0) := by
    have h_pos := typicalSet_prob_tendsto_one μ Xs hXs hindep hident hε
    -- μ {... ∉ T} = 1 - μ {... ∈ T}, hence its toReal tends to 0.
    have h_id : ∀ n,
        μ {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε}
          = 1 - μ {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε} := by
      intro n
      have h_compl_eq :
          {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε}
            = {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε}ᶜ := rfl
      rw [h_compl_eq, measure_compl (h_meas_T n) (measure_ne_top μ _), measure_univ]
    -- toReal of the difference → 0.
    have h_toReal_tendsto :
        Tendsto (fun n => (1 - μ {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε}).toReal)
          atTop (𝓝 0) := by
      have h_cont : Continuous (fun x : ℝ≥0∞ => (1 : ℝ≥0∞) - x) :=
        ENNReal.continuous_sub_left (by simp)
      have h_step : Tendsto (fun n => (1 : ℝ≥0∞) -
            μ {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε}) atTop
          (𝓝 ((1 : ℝ≥0∞) - 1)) := h_cont.tendsto _ |>.comp h_pos
      simp only [tsub_self] at h_step
      have h_toReal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp h_step
      simpa using h_toReal
    refine Tendsto.congr (fun n => ?_) h_toReal_tendsto
    rw [h_id n]
  -- errorProb n = μ.real {error event} ≤ μ.real {... ∉ T} which → 0.
  have h_error_le : ∀ n,
      InformationTheory.MeasureFano.errorProb μ
          (jointRV Xs n)
          (fun ω => aepEncoder μ Xs n ε R (h_card n) (jointRV Xs n ω))
          (aepDecoder μ Xs n ε R)
        ≤ (μ {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε}).toReal := by
    intro n
    unfold InformationTheory.MeasureFano.errorProb Measure.real
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (h_subset n))
  have h_error_nn : ∀ n,
      0 ≤ InformationTheory.MeasureFano.errorProb μ
            (jointRV Xs n)
            (fun ω => aepEncoder μ Xs n ε R (h_card n) (jointRV Xs n ω))
            (aepDecoder μ Xs n ε R) := by
    intro n
    unfold InformationTheory.MeasureFano.errorProb
    exact measureReal_nonneg
  exact squeeze_zero h_error_nn h_error_le h_compl_tendsto

/-! #### Phase C — rate Tendsto + main theorem -/

/-- `log M_n / n → R` (squeeze via `Nat.le_ceil` and `Nat.ceil_lt_add_one`). -/
lemma codebookSize_log_div_tendsto
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun n : ℕ => Real.log (codebookSize R n : ℝ) / n) atTop (𝓝 R) := by
  -- Lower bound: R ≤ log M_n / n (for n ≥ 1).
  -- Upper bound: log M_n / n ≤ log (exp(nR) + 1) / n → R.
  set f : ℕ → ℝ := fun n => Real.log (codebookSize R n : ℝ) / n with hf_def
  -- Show ∀ᶠ n in atTop, R ≤ f n ≤ log (exp(nR) + 1) / n.
  -- Lower: R ≤ log M_n / n.
  have h_lower : ∀ᶠ n in atTop, R ≤ f n := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
    have hexp_pos : 0 < Real.exp ((n : ℝ) * R) := Real.exp_pos _
    have h_le : Real.exp ((n : ℝ) * R) ≤ (codebookSize R n : ℝ) := by
      unfold codebookSize
      exact Nat.le_ceil _
    have h_log : Real.log (Real.exp ((n : ℝ) * R)) ≤ Real.log (codebookSize R n : ℝ) :=
      Real.log_le_log hexp_pos h_le
    rw [Real.log_exp] at h_log
    -- (n : ℝ) * R ≤ log (M_n) ⟹ R ≤ log (M_n) / n (n > 0).
    have h_div := (div_le_div_iff_of_pos_right hn_pos_R).mpr h_log
    have h_simp : (n : ℝ) * R / (n : ℝ) = R := by field_simp
    rw [h_simp] at h_div
    exact h_div
  -- Upper: f n ≤ log (exp(nR) + 1) / n.
  set g : ℕ → ℝ := fun n => Real.log (Real.exp ((n : ℝ) * R) + 1) / n with hg_def
  have h_upper : ∀ᶠ n in atTop, f n ≤ g n := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
    have h_ceil_lt :
        (codebookSize R n : ℝ) < Real.exp ((n : ℝ) * R) + 1 := by
      unfold codebookSize
      exact Nat.ceil_lt_add_one (Real.exp_pos _).le
    have h_ceil_pos : 0 < (codebookSize R n : ℝ) := by
      have := codebookSize_pos R n
      exact_mod_cast this
    have h_log_le :
        Real.log (codebookSize R n : ℝ) ≤ Real.log (Real.exp ((n : ℝ) * R) + 1) :=
      (Real.log_le_log h_ceil_pos h_ceil_lt.le)
    exact (div_le_div_iff_of_pos_right hn_pos_R).mpr h_log_le
  -- g n → R.
  -- log (exp(nR) + 1) = log (exp(nR) (1 + exp(-nR))) = nR + log (1 + exp(-nR)).
  -- so g n = R + log (1 + exp(-nR)) / n. Both R is constant, second → 0.
  have h_g_tendsto : Tendsto g atTop (𝓝 R) := by
    have h_eq : ∀ n : ℕ, 1 ≤ n →
        g n = R + Real.log (1 + Real.exp (-((n : ℝ) * R))) / n := by
      intro n hn
      have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
      have hnR_pos : 0 < Real.exp ((n : ℝ) * R) := Real.exp_pos _
      have h_inv : Real.exp ((n : ℝ) * R) + 1
          = Real.exp ((n : ℝ) * R) * (1 + Real.exp (-((n : ℝ) * R))) := by
        rw [mul_add, mul_one, ← Real.exp_add,
          show (((n : ℝ) * R) + -((n : ℝ) * R)) = 0 from by ring, Real.exp_zero]
      have h_inner_pos : 0 < 1 + Real.exp (-((n : ℝ) * R)) := by
        have := Real.exp_pos (-((n : ℝ) * R))
        linarith
      have h_log_mul : Real.log (Real.exp ((n : ℝ) * R) + 1)
          = (n : ℝ) * R + Real.log (1 + Real.exp (-((n : ℝ) * R))) := by
        rw [h_inv, Real.log_mul hnR_pos.ne' h_inner_pos.ne', Real.log_exp]
      show Real.log (Real.exp ((n : ℝ) * R) + 1) / n
        = R + Real.log (1 + Real.exp (-((n : ℝ) * R))) / n
      rw [h_log_mul, add_div]
      have h_div_n : (n : ℝ) * R / (n : ℝ) = R := by field_simp
      rw [h_div_n]
    -- Use squeeze on |g n - R| ≤ log 2 / n.
    -- Reduce target to: g n - R → 0, i.e. log(1 + exp(-nR))/n → 0.
    -- Direct sandwich: 0 ≤ log(1 + exp(-nR))/n ≤ log 2 / n.
    have h_bound_nn : ∀ n : ℕ, 1 ≤ n →
        0 ≤ Real.log (1 + Real.exp (-((n : ℝ) * R))) / n := by
      intro n hn
      have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
      have h_pos_exp : 0 < Real.exp (-((n : ℝ) * R)) := Real.exp_pos _
      have h_one_le : 1 ≤ 1 + Real.exp (-((n : ℝ) * R)) := by linarith
      have h_log_nn : 0 ≤ Real.log (1 + Real.exp (-((n : ℝ) * R))) :=
        Real.log_nonneg h_one_le
      exact div_nonneg h_log_nn hn_pos_R.le
    have h_bound : ∀ n : ℕ, 1 ≤ n →
        Real.log (1 + Real.exp (-((n : ℝ) * R))) / n ≤ Real.log 2 / n := by
      intro n hn
      have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
      have h_exp_le_one : Real.exp (-((n : ℝ) * R)) ≤ 1 := by
        have hnR_nn : 0 ≤ (n : ℝ) * R := mul_nonneg (Nat.cast_nonneg n) hR.le
        have : -((n : ℝ) * R) ≤ 0 := by linarith
        calc Real.exp (-((n : ℝ) * R))
            ≤ Real.exp 0 := Real.exp_le_exp.mpr this
          _ = 1 := Real.exp_zero
      have h_one_le : 1 ≤ 1 + Real.exp (-((n : ℝ) * R)) := by
        have := Real.exp_pos (-((n : ℝ) * R)); linarith
      have h_le_two : 1 + Real.exp (-((n : ℝ) * R)) ≤ 2 := by linarith
      have h_log_le_log2 : Real.log (1 + Real.exp (-((n : ℝ) * R))) ≤ Real.log 2 :=
        Real.log_le_log (by linarith) h_le_two
      exact div_le_div_of_nonneg_right h_log_le_log2 hn_pos_R.le
    -- Use squeeze on log(1 + exp(-nR))/n.
    have h_log2_div : Tendsto (fun n : ℕ => Real.log 2 / n) atTop (𝓝 0) := by
      have h_one_div : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have h_mul := h_one_div.const_mul (Real.log 2)
      simp only [mul_zero] at h_mul
      refine Tendsto.congr (fun n => ?_) h_mul
      ring
    have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    have h_inner_tendsto :
        Tendsto (fun n : ℕ => Real.log (1 + Real.exp (-((n : ℝ) * R))) / n) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_log2_div
      · exact Filter.eventually_atTop.mpr ⟨1, fun n hn => h_bound_nn n hn⟩
      · exact Filter.eventually_atTop.mpr ⟨1, fun n hn => h_bound n hn⟩
    -- g n = R + (small term), and small → 0, so g → R + 0 = R.
    have h_step :
        Tendsto (fun n : ℕ => R + Real.log (1 + Real.exp (-((n : ℝ) * R))) / n) atTop
          (𝓝 (R + 0)) := tendsto_const_nhds.add h_inner_tendsto
    rw [add_zero] at h_step
    -- Congr g with this representation eventually.
    refine Tendsto.congr' ?_ h_step
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    exact (h_eq n hn).symm
  -- Squeeze: R ≤ f n ≤ g n eventually, R → R and g → R, hence f → R.
  have h_const : Tendsto (fun _ : ℕ => R) atTop (𝓝 R) := tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_const h_g_tendsto h_lower h_upper

/-- **Source coding theorem, achievability**:
For any rate `R > entropy μ (Xs 0)`, there exists a block code with rate `R` and
vanishing error. -/
@[entry_point]
theorem source_coding_achievability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {R : ℝ} (hR : entropy μ (Xs 0) < R) :
    ∃ M : ℕ → ℕ, ∃ _hM_pos : ∀ n, 0 < M n,
    ∃ c : ∀ n, (Fin n → α) → Fin (M n),
    ∃ d : ∀ n, Fin (M n) → (Fin n → α),
      Tendsto (fun n => Real.log (M n : ℝ) / n) atTop (𝓝 R) ∧
      Tendsto
        (fun n => InformationTheory.MeasureFano.errorProb μ
                    (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n))
        atTop (𝓝 0) := by
  -- Take ε := (R - H) / 2, so H + ε < R (in particular H + ε ≤ R).
  set H : ℝ := entropy μ (Xs 0) with hH_def
  set ε : ℝ := (R - H) / 2 with hε_def
  have hε : 0 < ε := by simp only [hε_def]; linarith
  have h_le : H + ε ≤ R := by simp only [hε_def]; linarith
  -- R > 0: H ≥ 0 (entropy_nonneg) + R > H ≥ 0.
  have h_R_pos : 0 < R := by
    have hH_nn : 0 ≤ H := InformationTheory.Shannon.entropy_nonneg μ (Xs 0) (hXs 0)
    linarith
  -- Pairwise independence from iIndepFun.
  have hindep_pair : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j :=
    fun _ _ hij => hindep_full.indepFun hij
  -- Provide existentials.
  refine ⟨codebookSize R, fun n => codebookSize_pos R n,
    fun n => aepEncoder μ Xs n ε R
                (typicalSet_card_le_codebookSize μ Xs hXs hpos n hε h_le),
    fun n => aepDecoder μ Xs n ε R, ?_, ?_⟩
  · exact codebookSize_log_div_tendsto h_R_pos
  · exact aep_errorProb_tendsto_zero μ Xs hXs hpos hindep_pair hident hε h_le

/-! ### Phase F — Unified source coding theorem (両側等号)

Combining Phase D (weak converse) and Phase E (achievability) yields
`sInf (achievableRates μ Xs) = entropy μ (Xs 0)`. An "achievable code" is a family
`(M_n, c_n, d_n)` whose error probability vanishes and whose rate `log M_n / n`
is universally bounded (the `hM_bdd` hypothesis of Phase D). The achievability
witnesses produced by Phase E satisfy this universally-bounded condition because
`Tendsto rate atTop (𝓝 R)` implies `BddAbove (Set.range rate)`
(`Filter.Tendsto.bddAbove_range`).
-/

/-- An achievable block source code: each `M_n > 0`, error probability vanishes,
and the rate is universally bounded. -/
structure IsAchievableCode
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (M : ℕ → ℕ)
    (c : ∀ n, (Fin n → α) → Fin (M n))
    (d : ∀ n, Fin (M n) → (Fin n → α)) : Prop where
  hM_pos : ∀ n, NeZero (M n)
  hPe_to_zero :
    Tendsto (fun n => InformationTheory.MeasureFano.errorProb μ
              (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n))
            atTop (𝓝 0)
  hM_bdd : ∃ R, ∀ n, Real.log (M n : ℝ) / n ≤ R

/-- The set of asymptotic rates (`liminf log M_n / n`) of achievable codes. -/
noncomputable def achievableRates
    (μ : Measure Ω) (Xs : ℕ → Ω → α) : Set ℝ :=
  { r | ∃ (M : ℕ → ℕ) (c : ∀ n, (Fin n → α) → Fin (M n))
        (d : ∀ n, Fin (M n) → (Fin n → α)),
        IsAchievableCode μ Xs M c d ∧
        Filter.liminf (fun n : ℕ => Real.log (M n : ℝ) / n) atTop = r }

/-- (Phase D lifted) Every achievable rate is at least the entropy. -/
@[entry_point]
theorem entropy_le_of_mem_achievableRates
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hcard : 2 ≤ Fintype.card α)
    {r : ℝ} (hr : r ∈ achievableRates μ Xs) :
    entropy μ (Xs 0) ≤ r := by
  obtain ⟨M, c, d, hAch, hlim⟩ := hr
  haveI : ∀ n, NeZero (M n) := hAch.hM_pos
  rw [← hlim]
  exact source_coding_converse μ Xs hXs hindep_full hident hcard M c d
    hAch.hPe_to_zero hAch.hM_bdd

/-- (Phase E lifted) Any rate strictly above the entropy is achievable. -/
@[entry_point]
theorem mem_achievableRates_of_gt_entropy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {R : ℝ} (hR : entropy μ (Xs 0) < R) :
    R ∈ achievableRates μ Xs := by
  obtain ⟨M, hM_pos, c, d, hRate, hPe⟩ :=
    source_coding_achievability μ Xs hXs hpos hindep_full hident hR
  refine ⟨M, c, d, ⟨fun n => ⟨(hM_pos n).ne'⟩, hPe, ?_⟩, hRate.liminf_eq⟩
  -- hM_bdd: Tendsto rate (𝓝 R) ⟹ BddAbove (Set.range rate) ⟹ ∃ R', ∀ n, rate n ≤ R'.
  obtain ⟨R', hR'⟩ := hRate.bddAbove_range
  exact ⟨R', fun n => hR' (Set.mem_range_self n)⟩

/-- **Source coding theorem (両側等号)**:
The infimum of asymptotic rates of achievable block source codes equals the
entropy of the source. -/
@[entry_point]
theorem source_coding_theorem
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hcard : 2 ≤ Fintype.card α) :
    sInf (achievableRates μ Xs) = entropy μ (Xs 0) := by
  set H : ℝ := entropy μ (Xs 0) with hH_def
  -- Lower bound H is a lower bound for achievableRates.
  have h_lb : ∀ r ∈ achievableRates μ Xs, H ≤ r := fun r hr =>
    entropy_le_of_mem_achievableRates μ Xs hXs hindep_full hident hcard hr
  have h_bddBelow : BddBelow (achievableRates μ Xs) := ⟨H, h_lb⟩
  -- Achievability gives nonemptyness (use R = H + 1).
  have h_nonempty : (achievableRates μ Xs).Nonempty :=
    ⟨H + 1, mem_achievableRates_of_gt_entropy μ Xs hXs hpos hindep_full hident
      (by linarith : H < H + 1)⟩
  apply le_antisymm
  · -- sInf ≤ H: for every a > H, a ∈ achievableRates ⟹ sInf ≤ a; dense argument.
    refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
    exact csInf_le_of_le h_bddBelow
      (mem_achievableRates_of_gt_entropy μ Xs hXs hpos hindep_full hident ha) le_rfl
  · -- H ≤ sInf: H is a lower bound and achievableRates is nonempty.
    exact le_csInf h_nonempty h_lb

/-! ### Phase G — Point-wise probability upper bound on typicalSet

Cover-Thomas Theorem 3.1.2 (a)(2): for any `x ∈ T_ε^n`,
`P^n(x) = ∏ P(x_i) ≤ exp(-n(H - ε))`. This is the **point-wise** companion of the
size bound `|T_ε^n| ≤ exp(n(H+ε))` and is the key input for the Phase B-(c)
"independent-pair" bound in channel coding achievability (B-3).

The factorization `μ.map (jointRV Xs n) = Measure.pi (μ.map (Xs ·))` requires
mutual independence (`iIndepFun`), not just pairwise independence. We obtain it
via `iIndepFun_iff_map_fun_eq_pi_map` after restricting indices `ℕ → Fin n` with
`iIndepFun.precomp Fin.val_injective`. -/

/-- **Point-wise upper bound on typical-set mass**: `(μ.map (jointRV Xs n)).real {x}
≤ exp(- n · (H - ε))` for any `x ∈ T_ε^n`. -/
@[entry_point]
theorem typicalSet_prob_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (n : ℕ) {ε : ℝ}
    (x : Fin n → α) (hx : x ∈ typicalSet μ Xs n ε) :
    (μ.map (jointRV Xs n)).real {x}
      ≤ Real.exp (- (n : ℝ) * (entropy μ (Xs 0) - ε)) := by
  classical
  -- Notation.
  set P : α → ℝ := fun a => (μ.map (Xs 0)).real {a} with hP_def
  set H : ℝ := entropy μ (Xs 0) with hH_def
  -- Reindex `Xs` to `Fin n` via `Fin.val`.
  have hFin_inj : Function.Injective (Fin.val : Fin n → ℕ) := Fin.val_injective
  have hindep_fin :
      iIndepFun (fun i : Fin n => Xs i.val) μ := hindep_full.precomp hFin_inj
  -- Each marginal `Xs i.val` has the same law as `Xs 0`.
  have hmap_eq : ∀ i : Fin n, μ.map (Xs i.val) = μ.map (Xs 0) := fun i =>
    (hident i.val).map_eq
  have hXfin_meas : ∀ i : Fin n, Measurable (Xs i.val) := fun i => hXs i.val
  -- Cast `iIndepFun` into the product-measure identity. `Mathlib`'s
  -- `iIndepFun_iff_map_fun_eq_pi_map` requires `[Fintype ι]`. We have that for
  -- `Fin n`.
  have hpi_eq :
      μ.map (fun ω i => Xs i.val ω)
        = Measure.pi (fun i : Fin n => μ.map (Xs i.val)) :=
    (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hXfin_meas i).aemeasurable)).mp
      hindep_fin
  -- Replace each `μ.map (Xs i.val)` with `μ.map (Xs 0)`.
  have hpi_eq' :
      μ.map (fun ω i => Xs i.val ω)
        = Measure.pi (fun _ : Fin n => μ.map (Xs 0)) := by
    rw [hpi_eq]
    congr 1
    funext i
    exact hmap_eq i
  -- `jointRV Xs n` is definitionally `fun ω i => Xs i.val ω` (Lean coerces `Fin n` to `ℕ`).
  have hjoint_eq : (μ.map (jointRV Xs n) : Measure (Fin n → α))
      = Measure.pi (fun _ : Fin n => μ.map (Xs 0)) := hpi_eq'
  -- Evaluate on the singleton `{x}`.
  -- `IsProbabilityMeasure (μ.map (Xs 0))` ⇒ `SigmaFinite`.
  have hMprob : IsProbabilityMeasure (μ.map (Xs 0)) :=
    Measure.isProbabilityMeasure_map (hXs 0).aemeasurable
  -- Now compute `Measure.pi {x}` via `pi_singleton`.
  have hpi_singleton :
      Measure.pi (fun _ : Fin n => μ.map (Xs 0)) ({x} : Set (Fin n → α))
        = ∏ i, (μ.map (Xs 0)) {x i} :=
    Measure.pi_singleton (μ := fun _ : Fin n => μ.map (Xs 0)) x
  have hmeas_singleton :
      (μ.map (jointRV Xs n)) ({x} : Set (Fin n → α))
        = ∏ i, (μ.map (Xs 0)) {x i} := by
    rw [hjoint_eq]; exact hpi_singleton
  -- Convert to `measureReal` (`.toReal`). Each factor is finite (probability ≤ 1).
  have hP_pos : ∀ a, 0 < P a := hpos
  have hP_lt_top : ∀ a, (μ.map (Xs 0)) {a} ≠ ∞ := fun a => measure_ne_top _ _
  have hreal :
      (μ.map (jointRV Xs n)).real {x} = ∏ i, P (x i) := by
    unfold MeasureTheory.Measure.real
    rw [hmeas_singleton]
    rw [ENNReal.toReal_prod]
    rfl
  -- Now use the typical-set lower-side inequality.
  -- `mem_typicalSet_iff`: `|(∑ pmfLog (x i)) / n - H| < ε`.
  rw [mem_typicalSet_iff] at hx
  -- Two cases: `n = 0` vs. `n > 0`.
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- n = 0: empty product = 1 = exp 0, and `Fin 0 → α` is a singleton.
    subst hn0
    have hreal0 : (μ.map (jointRV Xs 0)).real {x} = 1 := by
      rw [hreal]
      simp
    rw [hreal0]
    -- `Real.exp (- 0 * (H - ε)) = Real.exp 0 = 1`.
    simp
  · -- n > 0: use the upper-side lower bound on `∑ pmfLog (x i)`.
    have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hnpos
    -- From `|.| < ε`: `-ε < (∑ pmfLog) / n - H`, i.e. `n · (H - ε) < ∑ pmfLog`.
    have hlower : -ε < (∑ i : Fin n, pmfLog μ Xs (x i)) / n - H := (abs_lt.mp hx).1
    have hlower' : H - ε < (∑ i : Fin n, pmfLog μ Xs (x i)) / n := by linarith
    have hsum_gt : (n : ℝ) * (H - ε) < ∑ i : Fin n, pmfLog μ Xs (x i) := by
      have := (lt_div_iff₀ hn_pos_R).mp hlower'
      linarith
    -- `exp` is strictly monotone (and we use `≤` for the conclusion).
    have hneg : -(∑ i : Fin n, pmfLog μ Xs (x i)) < -((n : ℝ) * (H - ε)) := by linarith
    have hexp_lt : Real.exp (-(∑ i : Fin n, pmfLog μ Xs (x i)))
        < Real.exp (-((n : ℝ) * (H - ε))) := Real.exp_lt_exp.mpr hneg
    -- Rewrite LHS as `∏ i, P (x i)`.
    have hexp_pmfLog : ∀ a, Real.exp (-(pmfLog μ Xs a)) = P a := by
      intro a
      have : -(pmfLog μ Xs a) = Real.log (P a) := by
        simp [pmfLog, hP_def]
      rw [this, Real.exp_log (hP_pos a)]
    have hprod_eq : Real.exp (-(∑ i : Fin n, pmfLog μ Xs (x i)))
        = ∏ i : Fin n, P (x i) := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      exact Finset.prod_congr rfl fun i _ => hexp_pmfLog (x i)
    rw [hprod_eq] at hexp_lt
    -- `∏ i, P (x i) < exp(-n(H-ε))` so `≤ exp(-n(H-ε))`.
    have : ∏ i : Fin n, P (x i) ≤ Real.exp (-((n : ℝ) * (H - ε))) := hexp_lt.le
    -- Now `-(n * (H - ε)) = -n * (H - ε)` (same number).
    have hexp_rewrite : Real.exp (-((n : ℝ) * (H - ε)))
        = Real.exp (-(n : ℝ) * (H - ε)) := by ring_nf
    rw [hexp_rewrite] at this
    -- Conclude.
    rw [hreal]
    exact this

/-! ### Phase H — Point-wise lower bound + size lower bound (D-3, Cover-Thomas 3.1.2 完全形)

`typicalSet_prob_le` (Phase G, 点別上界) と `typicalSet_prob_tendsto_one` (Phase C, 集合確率
→ 1) と `typicalSet_card_le` (Phase C, サイズ上界) に加え、Cover-Thomas Theorem 3.1.2 の
完全 4 帰結を充足する残り 2 本:
- `typicalSet_prob_ge`: 点別下界 `exp(-n(H+ε)) ≤ P^n(x)` for `x ∈ T_ε^n`
- `typicalSet_card_ge`: サイズ下界 `(1-η) · exp(n(H-ε)) ≤ |T_ε^n|` whenever `μ(T) ≥ 1-η`

実装: 点別下界は `prob_le` の方向反転 (上側不等式 `(∑ pmfLog)/n - H < ε` を使う)、
サイズ下界は `μ(T) = ∑_{x∈T} p(x) ≤ |T| · exp(-n(H-ε))` (point-wise upper bound) を
変形して取得。-/

/-- **Point-wise lower bound on typical-set mass**: for `x ∈ T_ε^n`,
`exp(-n · (H + ε)) ≤ (μ.map (jointRV Xs n)).real {x}`. Dual of
`typicalSet_prob_le`. -/
@[entry_point]
theorem typicalSet_prob_ge
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (n : ℕ) {ε : ℝ}
    (x : Fin n → α) (hx : x ∈ typicalSet μ Xs n ε) :
    Real.exp (- (n : ℝ) * (entropy μ (Xs 0) + ε))
      ≤ (μ.map (jointRV Xs n)).real {x} := by
  classical
  set P : α → ℝ := fun a => (μ.map (Xs 0)).real {a} with hP_def
  set H : ℝ := entropy μ (Xs 0) with hH_def
  -- Reindex `Xs` to `Fin n` via `Fin.val`.
  have hFin_inj : Function.Injective (Fin.val : Fin n → ℕ) := Fin.val_injective
  have hindep_fin :
      iIndepFun (fun i : Fin n => Xs i.val) μ := hindep_full.precomp hFin_inj
  have hmap_eq : ∀ i : Fin n, μ.map (Xs i.val) = μ.map (Xs 0) := fun i =>
    (hident i.val).map_eq
  have hXfin_meas : ∀ i : Fin n, Measurable (Xs i.val) := fun i => hXs i.val
  have hpi_eq :
      μ.map (fun ω i => Xs i.val ω)
        = Measure.pi (fun i : Fin n => μ.map (Xs i.val)) :=
    (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hXfin_meas i).aemeasurable)).mp
      hindep_fin
  have hpi_eq' :
      μ.map (fun ω i => Xs i.val ω)
        = Measure.pi (fun _ : Fin n => μ.map (Xs 0)) := by
    rw [hpi_eq]
    congr 1
    funext i
    exact hmap_eq i
  have hjoint_eq : (μ.map (jointRV Xs n) : Measure (Fin n → α))
      = Measure.pi (fun _ : Fin n => μ.map (Xs 0)) := hpi_eq'
  have hMprob : IsProbabilityMeasure (μ.map (Xs 0)) :=
    Measure.isProbabilityMeasure_map (hXs 0).aemeasurable
  have hpi_singleton :
      Measure.pi (fun _ : Fin n => μ.map (Xs 0)) ({x} : Set (Fin n → α))
        = ∏ i, (μ.map (Xs 0)) {x i} :=
    Measure.pi_singleton (μ := fun _ : Fin n => μ.map (Xs 0)) x
  have hmeas_singleton :
      (μ.map (jointRV Xs n)) ({x} : Set (Fin n → α))
        = ∏ i, (μ.map (Xs 0)) {x i} := by
    rw [hjoint_eq]; exact hpi_singleton
  have hP_pos : ∀ a, 0 < P a := hpos
  have hreal :
      (μ.map (jointRV Xs n)).real {x} = ∏ i, P (x i) := by
    unfold MeasureTheory.Measure.real
    rw [hmeas_singleton]
    rw [ENNReal.toReal_prod]
    rfl
  rw [mem_typicalSet_iff] at hx
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- n = 0: empty product = 1, RHS = exp 0 = 1.
    subst hn0
    have hreal0 : (μ.map (jointRV Xs 0)).real {x} = 1 := by
      rw [hreal]; simp
    rw [hreal0]
    simp
  · -- n > 0: use the upper-side bound on `(∑ pmfLog) / n - H < ε`.
    have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hupper : (∑ i : Fin n, pmfLog μ Xs (x i)) / n - H < ε := (abs_lt.mp hx).2
    have hupper' : (∑ i : Fin n, pmfLog μ Xs (x i)) / n < H + ε := by linarith
    have hsum_lt : (∑ i : Fin n, pmfLog μ Xs (x i)) < (n : ℝ) * (H + ε) := by
      have := (div_lt_iff₀ hn_pos_R).mp hupper'
      linarith
    have hneg : -((n : ℝ) * (H + ε)) < -(∑ i : Fin n, pmfLog μ Xs (x i)) := by linarith
    have hexp_lt : Real.exp (-((n : ℝ) * (H + ε)))
        < Real.exp (-(∑ i : Fin n, pmfLog μ Xs (x i))) := Real.exp_lt_exp.mpr hneg
    have hexp_pmfLog : ∀ a, Real.exp (-(pmfLog μ Xs a)) = P a := by
      intro a
      have : -(pmfLog μ Xs a) = Real.log (P a) := by
        simp [pmfLog, hP_def]
      rw [this, Real.exp_log (hP_pos a)]
    have hprod_eq : Real.exp (-(∑ i : Fin n, pmfLog μ Xs (x i)))
        = ∏ i : Fin n, P (x i) := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      exact Finset.prod_congr rfl fun i _ => hexp_pmfLog (x i)
    rw [hprod_eq] at hexp_lt
    have hle : Real.exp (-((n : ℝ) * (H + ε))) ≤ ∏ i : Fin n, P (x i) := hexp_lt.le
    have hexp_rewrite : Real.exp (-((n : ℝ) * (H + ε)))
        = Real.exp (-(n : ℝ) * (H + ε)) := by ring_nf
    rw [hexp_rewrite] at hle
    rw [hreal]
    exact hle

/-- **Size lower bound on typical set**: if `μ(T_ε^n) ≥ 1 - η`, then
`(1-η) · exp(n · (H - ε)) ≤ |T_ε^n|`. Combined with `typicalSet_prob_tendsto_one`
this yields the eventually-large-n form of Cover-Thomas 3.1.2 (b)(4). -/
@[entry_point]
theorem typicalSet_card_ge
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (n : ℕ) {ε η : ℝ}
    (hμ : (1 - η) ≤ (μ.map (jointRV Xs n)).real (typicalSet μ Xs n ε)) :
    (1 - η) * Real.exp ((n : ℝ) * (entropy μ (Xs 0) - ε))
      ≤ ((typicalSet μ Xs n ε).toFinite.toFinset.card : ℝ) := by
  classical
  set H : ℝ := entropy μ (Xs 0) with hH_def
  set T : Finset (Fin n → α) := (typicalSet μ Xs n ε).toFinite.toFinset with hT_def
  set p : (Fin n → α) → ℝ := fun x => (μ.map (jointRV Xs n)).real {x} with hp_def
  -- Step 1: convert `μ(T)` to `∑ x ∈ T, p x` via finite-sum decomposition.
  have h_coe : (T : Set (Fin n → α)) = typicalSet μ Xs n ε :=
    (typicalSet μ Xs n ε).toFinite.coe_toFinset
  have hMprob_joint : IsProbabilityMeasure (μ.map (jointRV Xs n)) :=
    Measure.isProbabilityMeasure_map (measurable_jointRV Xs hXs n).aemeasurable
  have h_sum_T :
      (μ.map (jointRV Xs n)).real (typicalSet μ Xs n ε) = ∑ x ∈ T, p x := by
    rw [← h_coe]
    exact (sum_measureReal_singleton (μ := μ.map (jointRV Xs n)) T).symm
  -- Step 2: `∑ x ∈ T, p x ≤ |T| · exp(-n(H-ε))` via `typicalSet_prob_le`.
  have h_each_le : ∀ x ∈ T, p x ≤ Real.exp (-(n : ℝ) * (H - ε)) := by
    intro x hx
    have hxT : x ∈ typicalSet μ Xs n ε := (Set.Finite.mem_toFinset _).mp hx
    exact typicalSet_prob_le μ Xs hXs hindep_full hident hpos n x hxT
  have h_sum_T_le :
      (∑ x ∈ T, p x) ≤ (T.card : ℝ) * Real.exp (-(n : ℝ) * (H - ε)) := by
    calc (∑ x ∈ T, p x)
        ≤ ∑ x ∈ T, Real.exp (-(n : ℝ) * (H - ε)) := Finset.sum_le_sum h_each_le
      _ = (T.card : ℝ) * Real.exp (-(n : ℝ) * (H - ε)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- Step 3: chain `1 - η ≤ μ(T) = ∑ p ≤ |T| · exp(-n(H-ε))`.
  have h_combined :
      (1 - η) ≤ (T.card : ℝ) * Real.exp (-(n : ℝ) * (H - ε)) := by
    calc (1 - η)
        ≤ (μ.map (jointRV Xs n)).real (typicalSet μ Xs n ε) := hμ
      _ = ∑ x ∈ T, p x := h_sum_T
      _ ≤ (T.card : ℝ) * Real.exp (-(n : ℝ) * (H - ε)) := h_sum_T_le
  -- Step 4: multiply both sides by `exp(n(H-ε)) > 0`.
  have hexp_pos : 0 < Real.exp ((n : ℝ) * (H - ε)) := Real.exp_pos _
  have h_exp_cancel :
      Real.exp (-(n : ℝ) * (H - ε)) * Real.exp ((n : ℝ) * (H - ε)) = 1 := by
    rw [show -(n : ℝ) * (H - ε) = -((n : ℝ) * (H - ε)) from by ring,
        ← Real.exp_add]
    simp
  have h_mul := mul_le_mul_of_nonneg_right h_combined hexp_pos.le
  -- h_mul : (1-η) * exp(n(H-ε)) ≤ |T| * exp(-n(H-ε)) * exp(n(H-ε))
  have h_rhs :
      (T.card : ℝ) * Real.exp (-(n : ℝ) * (H - ε)) * Real.exp ((n : ℝ) * (H - ε))
        = (T.card : ℝ) := by
    rw [mul_assoc, h_exp_cancel, mul_one]
  rw [h_rhs] at h_mul
  exact h_mul

end InformationTheory.Shannon
