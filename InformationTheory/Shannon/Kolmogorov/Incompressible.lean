import InformationTheory.Shannon.Kolmogorov.Counting
import InformationTheory.Shannon.Kolmogorov.EntropyRate
import InformationTheory.Shannon.TypeClassLowerBound
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Incompressible binary sequences obey the law of large numbers

Cover–Thomas (2nd ed.) Theorem 14.5.1. An incompressible length-`n` binary
string — one whose conditional Kolmogorov complexity is at least its own length,
`n ≤ C(encodeBlock n b ∣ n)` — has empirical frequency of ones
`typeCount b true / n` close to `1/2`, and for a family of such strings the
frequency converges to `1/2` as `n → ∞`.

The argument is purely combinatorial (measure-free): it reuses the method-of-types
per-string upper bound of `EntropyRate.lean` with its typicality step removed, so
that the empirical binary entropy `binEntropy (typeCount b true / n)` bounds the
description length. Incompressibility then forces the binary entropy up to its
maximum `log 2`, and strict unimodality of `binEntropy` (via a fixed positive gap
away from `1/2`) pins the frequency to `1/2`.

## Main results

* `incompressible_freq_near_half` — the frequency of ones of every incompressible
  block is eventually within any `δ > 0` of `1/2`.
* `incompressible_seq_freq_tendsto_half` — along an eventually-incompressible
  family, the frequency of ones converges to `1/2`.
-/

namespace InformationTheory.Kolmogorov

open MeasureTheory Real Filter Topology InformationTheory.Shannon

/-- On the two-element alphabet the empirical entropy of a block's type equals the
binary entropy of its frequency of ones.
@audit:ok -/
theorem entropyByCount_bool_eq_binEntropy {n : ℕ} (hn : 0 < n) (b : Fin n → Bool) :
    entropyByCount (typeCount b) n = Real.binEntropy ((typeCount b true : ℝ) / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum : typeCount b true + typeCount b false = n := by
    have h := sum_typeCount b; rwa [Fintype.sum_bool] at h
  have hkle : typeCount b true ≤ n := by omega
  have hfalse : (typeCount b false : ℝ) / n = 1 - (typeCount b true : ℝ) / n := by
    have hnat : typeCount b false = n - typeCount b true := by omega
    rw [hnat, Nat.cast_sub hkle]; field_simp
  rw [entropyByCount, Fintype.sum_bool,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog]
  rw [hfalse]; ring

/-- Raw per-string upper bound (measure-free): the conditional complexity of a
binary block is bounded by the type-descriptor overhead plus `n · binEntropy(p)/log 2`,
with `p` the frequency of ones. Obtained from `condComplexity_block_typical_le` by
dropping the typicality step.
@audit:ok -/
theorem condComplexity_bool_block_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {n : ℕ} (_ : 0 < n) (b : Fin n → Bool),
      (condComplexity (encodeBlock n b) n : ℝ)
        ≤ 2 * Real.logb 2 ((n : ℝ) + 1)
          + (n : ℝ) * (Real.binEntropy ((typeCount b true : ℝ) / n) / Real.log 2) + c := by
  obtain ⟨b_c, hb_c⟩ := invariance (typeDecoder (α := Bool)) typeDecoder_partrec
  refine ⟨(b_c : ℝ) + 1, by positivity, ?_⟩
  intro n hn b
  have hlog2 : (0 : ℝ) < Real.log 2 := log_two_pos
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : typeCount b true + typeCount b false = n := by
    have h := sum_typeCount b; rwa [Fintype.sum_bool] at h
  have hkle : typeCount b true ≤ n := by omega
  have hp0 : 0 ≤ (typeCount b true : ℝ) / n := by positivity
  have hp1 : (typeCount b true : ℝ) / n ≤ 1 := by
    rw [div_le_one hn_pos]; exact_mod_cast hkle
  set Hb : ℝ := Real.binEntropy ((typeCount b true : ℝ) / n) with hHb
  have hHb_nn : 0 ≤ Hb := by rw [hHb]; exact Real.binEntropy_nonneg hp0 hp1
  have hEq : entropyByCount (typeCount b) n = Hb := by
    rw [hHb]; exact entropyByCount_bool_eq_binEntropy hn b
  obtain ⟨m, hmem, hmlt⟩ := exists_mem_typeDecoder_lt hn b
  have hcc : (condComplexity (encodeBlock n b) n : ℝ) ≤ (natLen m : ℝ) + b_c := by
    have hb := hb_c (encodeBlock n b) n (Computability.encodeNat m)
    rw [Computability.decode_encodeNat] at hb
    have := hb hmem
    rw [show (Computability.encodeNat m).length = natLen m from rfl] at this
    exact_mod_cast this
  have hTc_exp : ((typeClassByCount (n := n) (typeCount b)).toFinite.toFinset.card : ℝ)
      ≤ Real.exp ((n : ℝ) * Hb) := by
    have hsum' := sum_typeCount b
    have hcard := typeClassByCount_card_le (typeCount b) hsum'
    rw [pow_div_prod_pow_eq_exp_n_entropyByCount (typeCount b) hsum', hEq] at hcard
    exact hcard
  have hlogb_nn : 0 ≤ Real.logb 2 ((n : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hnHb_nn : 0 ≤ (n : ℝ) * (Hb / Real.log 2) :=
    mul_nonneg hn_pos.le (div_nonneg hHb_nn hlog2.le)
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have hnatm0 : natLen m = 0 := by
      rw [hm0]; exact Nat.le_zero.mp (natLen_le_of_lt_two_pow 0 0 (by norm_num))
    have hnat0 : (natLen m : ℝ) = 0 := by rw [hnatm0]; norm_num
    rw [hnat0] at hcc
    have h2logb_nn : (0 : ℝ) ≤ 2 * Real.logb 2 ((n : ℝ) + 1) := mul_nonneg (by norm_num) hlogb_nn
    linarith [hcc, hnHb_nn, h2logb_nn]
  · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
    have hmpR : (0 : ℝ) < (m : ℝ) := by linarith
    have hnatle : (natLen m : ℝ) ≤ 1 + Real.logb 2 m := by
      have hpow2 : ((2 : ℝ) ^ natLen m) ≤ 2 * m := by exact_mod_cast natLen_le m hmpos
      have hlog := Real.log_le_log (by positivity) hpow2
      rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity)] at hlog
      have key : (natLen m : ℝ) * Real.log 2 ≤ (1 + Real.log m / Real.log 2) * Real.log 2 := by
        rw [add_mul, one_mul, div_mul_cancel₀ _ hlog2.ne']
        linarith [hlog]
      rw [Real.logb]
      exact le_of_mul_le_mul_right key hlog2
    have hmltR : (m : ℝ)
        < ((n : ℝ) + 1) ^ Fintype.card Bool
          * ((typeClassByCount (n := n) (typeCount b)).toFinite.toFinset.card : ℝ) := by
      exact_mod_cast hmlt
    have hKr_nn : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ Fintype.card Bool := by positivity
    have hmexp : (m : ℝ) < ((n : ℝ) + 1) ^ Fintype.card Bool * Real.exp ((n : ℝ) * Hb) :=
      lt_of_lt_of_le hmltR (mul_le_mul_of_nonneg_left hTc_exp hKr_nn)
    have hlogbm : Real.logb 2 m
        ≤ (Fintype.card Bool : ℝ) * Real.logb 2 ((n : ℝ) + 1) + (n : ℝ) * Hb / Real.log 2 := by
      have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hmpR hmexp.le
      rw [Real.logb_mul (by positivity) (Real.exp_ne_zero _), Real.logb_pow] at h1
      have hexp : Real.logb 2 (Real.exp ((n : ℝ) * Hb)) = (n : ℝ) * Hb / Real.log 2 := by
        rw [Real.logb, Real.log_exp]
      rw [hexp] at h1
      exact h1
    have hcardBool : (Fintype.card Bool : ℝ) = 2 := by rw [Fintype.card_bool]; norm_num
    have hassoc : (n : ℝ) * Hb / Real.log 2 = (n : ℝ) * (Hb / Real.log 2) := mul_div_assoc _ _ _
    rw [hcardBool] at hlogbm
    linarith [hcc, hnatle, hlogbm, hassoc]

/-- Fixed-gap analytic core: if the frequency `p` is at least `δ` away from `1/2`,
then its binary entropy is at most `binEntropy (1/2 - δ)`, which is strictly below
`log 2`.
@audit:ok -/
theorem binEntropy_gap_of_far_from_half {p δ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 2⁻¹) (hfar : δ ≤ |p - 2⁻¹|) :
    Real.binEntropy p ≤ Real.binEntropy (2⁻¹ - δ) := by
  have hmono := Real.binEntropy_strictMonoOn.monotoneOn
  have hmem_target : (2⁻¹ - δ) ∈ Set.Icc (0 : ℝ) 2⁻¹ := ⟨by linarith, by linarith⟩
  rcases le_or_gt p (2⁻¹ - δ) with hle | hgt
  · have hmem_p : p ∈ Set.Icc (0 : ℝ) 2⁻¹ := ⟨hp0, by linarith⟩
    exact hmono hmem_p hmem_target hle
  · have hpge : 2⁻¹ + δ ≤ p := by
      rcases abs_cases (p - 2⁻¹) with ⟨heq, _⟩ | ⟨heq, _⟩ <;> rw [heq] at hfar <;> linarith
    have hq : (1 - p) ≤ 2⁻¹ - δ := by linarith
    have hmem_q : (1 - p) ∈ Set.Icc (0 : ℝ) 2⁻¹ := ⟨by linarith, by linarith⟩
    have hqle := hmono hmem_q hmem_target hq
    rwa [Real.binEntropy_one_sub] at hqle

/-- Incompressible binary blocks exist at every length: since fewer than `2^n`
naturals have conditional complexity below `n`, some length-`n` block is
incompressible.
@audit:ok -/
theorem exists_incompressible_bool_seq :
    ∃ w : (n : ℕ) → Fin n → Bool,
      ∀ n : ℕ, 0 < n → (n : ℝ) ≤ (condComplexity (encodeBlock n (w n)) n : ℝ) := by
  have hex : ∀ n : ℕ, ∃ b : Fin n → Bool,
      (n : ℝ) ≤ (condComplexity (encodeBlock n b) n : ℝ) := by
    intro n
    by_contra h
    rw [not_exists] at h
    have hlt : ∀ b : Fin n → Bool, condComplexity (encodeBlock n b) n < n := by
      intro b; have := h b; simp only [not_le] at this; exact_mod_cast this
    have hSfin : {x : ℕ | condComplexity x n < n}.Finite := condComplexity_lt_finite n n
    have hScard : {x : ℕ | condComplexity x n < n}.ncard < 2 ^ n := condIncompressible_count n n
    have hsub : Set.range (fun b : Fin n → Bool ↦ encodeBlock n b)
        ⊆ {x : ℕ | condComplexity x n < n} := by
      rintro _ ⟨b, rfl⟩; exact hlt b
    have hrange : (Set.range (fun b : Fin n → Bool ↦ encodeBlock n b)).ncard = 2 ^ n := by
      rw [Set.ncard_range_of_injective (encodeBlock_injective (α := Bool) n),
        Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    have hle := Set.ncard_le_ncard hsub hSfin
    rw [hrange] at hle
    omega
  choose w hw using hex
  exact ⟨w, fun n _ ↦ hw n⟩

/-- CT 14.5.1: the frequency of ones of every incompressible binary block is
eventually within `δ` of `1/2`.
@audit:ok -/
@[entry_point]
theorem incompressible_freq_near_half {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ b : Fin n → Bool,
      (n : ℝ) ≤ (condComplexity (encodeBlock n b) n : ℝ) →
        |((typeCount b true : ℝ) / n) - 2⁻¹| < δ := by
  rcases le_or_gt δ 2⁻¹ with hδ_le | hδ_gt
  · -- Main case `δ ≤ 2⁻¹`: the fixed entropy gap forces the frequency near `1/2`.
    obtain ⟨c, _hc_nn, hL2⟩ := condComplexity_bool_block_le
    have hlog2 : (0 : ℝ) < Real.log 2 := log_two_pos
    have hHd_lt : Real.binEntropy (2⁻¹ - δ) < Real.log 2 :=
      Real.binEntropy_lt_log_two.2 (by intro h; linarith)
    set Hd : ℝ := Real.binEntropy (2⁻¹ - δ) with hHd
    set γ : ℝ := Real.log 2 - Hd with hγ
    have hγ_pos : 0 < γ := by rw [hγ]; linarith
    have hframeδ_pos : 0 < γ / (2 * Real.log 2) := by positivity
    filter_upwards [framing_overhead_eventually c 2 hframeδ_pos, eventually_gt_atTop 0]
      with n hframe hn b hincompr
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have hkle : typeCount b true ≤ n := by
      have h := sum_typeCount b; rw [Fintype.sum_bool] at h; omega
    have hp0 : 0 ≤ (typeCount b true : ℝ) / n := by positivity
    have hp1 : (typeCount b true : ℝ) / n ≤ 1 := by
      rw [div_le_one hn_pos]; exact_mod_cast hkle
    by_contra hcon
    rw [not_lt] at hcon
    have hgap : Real.binEntropy ((typeCount b true : ℝ) / n) ≤ Hd :=
      binEntropy_gap_of_far_from_half hp0 hp1 hδ hδ_le hcon
    have hbound := hL2 hn b
    have hts : (n : ℝ) * (Real.binEntropy ((typeCount b true : ℝ) / n) / Real.log 2)
        ≤ (n : ℝ) * (Hd / Real.log 2) := by gcongr
    have hid1 : (n : ℝ) * (Hd / Real.log 2) + (n : ℝ) * (γ / Real.log 2) = (n : ℝ) := by
      rw [hγ]; field_simp; ring
    have hid2 : (n : ℝ) * (γ / Real.log 2) = 2 * ((n : ℝ) * (γ / (2 * Real.log 2))) := by
      field_simp
    have hpos : 0 < (n : ℝ) * (γ / (2 * Real.log 2)) :=
      mul_pos hn_pos (div_pos hγ_pos (by positivity))
    linarith [hbound, hincompr, hts, hid1, hframe, hid2, hpos]
  · -- Degenerate case `δ > 2⁻¹`: every frequency in `[0,1]` is within `2⁻¹ < δ` of `1/2`.
    refine Filter.Eventually.of_forall (fun n b _ ↦ ?_)
    have hkle : typeCount b true ≤ n := by
      have h := sum_typeCount b; rw [Fintype.sum_bool] at h; omega
    have hp0 : 0 ≤ (typeCount b true : ℝ) / n := by positivity
    have hp1 : (typeCount b true : ℝ) / n ≤ 1 := by
      rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · subst hn0; simp
      · rw [div_le_one (by exact_mod_cast hn0)]; exact_mod_cast hkle
    calc |((typeCount b true : ℝ) / n) - 2⁻¹|
        ≤ 2⁻¹ := abs_le.2 ⟨by linarith, by linarith⟩
      _ < δ := hδ_gt

/-- Law-of-large-numbers corollary: along an eventually-incompressible family the
frequency of ones converges to `1/2`.
@audit:ok -/
@[entry_point]
theorem incompressible_seq_freq_tendsto_half
    (w : (n : ℕ) → Fin n → Bool)
    (hw : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ (condComplexity (encodeBlock n (w n)) n : ℝ)) :
    Tendsto (fun n : ℕ ↦ (typeCount (w n) true : ℝ) / n) atTop (𝓝 2⁻¹) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hev : ∀ᶠ n : ℕ in atTop, |((typeCount (w n) true : ℝ) / n) - 2⁻¹| < ε := by
    filter_upwards [incompressible_freq_near_half hε, hw] with n hclose hincompr
    exact hclose (w n) hincompr
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  exact ⟨N, fun n hn ↦ by rw [Real.dist_eq]; exact hN n hn⟩

end InformationTheory.Kolmogorov
