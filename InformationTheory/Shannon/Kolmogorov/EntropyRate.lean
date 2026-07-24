import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ConditionalMethodOfTypes.Mass.Concentration
import InformationTheory.Shannon.Kolmogorov.Counting
import InformationTheory.Shannon.StrongTypicality
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Topology.Order.Basic

/-!
# Kolmogorov complexity converges to the entropy rate

For an i.i.d. source `Xs` on a finite alphabet, the expected conditional
Kolmogorov complexity of a length-`n` block, normalized by `n`, converges to the
entropy `H(X)` re-based to bits:

`(1 / n) · E[C(X^n ∣ n)] → H(X) / log 2`.

The `/ log 2` re-bases the natural-log entropy `entropy` (`Bridge.lean`, base `e`)
to the bit-length complexity `condComplexity` (base `2`).

The proof is a squeeze between an upper and a lower half. The upper half encodes
a typical block by its index inside the typical set (bits `≈ n(H+ε)`) on top of
the conditional literal bound; the lower half combines the counting bound
`#{x ∣ C(x ∣ n) < k} < 2^k` with the strong-typicality size lower bound. This
file establishes the flagship statement and the plumbing lemmas the two halves
consume.

## Main results

* `kolmogorov_entropy_rate` — the flagship convergence (via the two halves).
* `encodeBlock` / `encodeBlock_injective` — injective encoding of a block as `ℕ`.
* `integrable_condComplexity_jointRV` — the block-complexity integrand is integrable.
-/

namespace InformationTheory.Kolmogorov

open InformationTheory.Shannon
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem ofDigits_ofFn (b : ℕ) {m : ℕ} (f : Fin m → ℕ) :
    Nat.ofDigits b (List.ofFn f) = ∑ i : Fin m, f i * b ^ (i : ℕ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, Nat.ofDigits_cons, ih (fun i ↦ f i.succ), Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring

section Block
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Injective, length-efficient encoding of a length-`m` block `Fin m → α` into a
natural number: the little-endian base-`Fintype.card α` numeral whose `i`-th digit
is the index of `x i` under `Fintype.equivFin`. Its value is below `card α ^ m`, so
its bit length is `m · log₂ (card α) + O(1)`. -/
noncomputable def encodeBlock (m : ℕ) (x : Fin m → α) : ℕ :=
  (finFunctionFinEquiv fun i ↦ Fintype.equivFin α (x i)).val

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem encodeBlock_injective (m : ℕ) : Function.Injective (encodeBlock (α := α) m) := by
  intro x y h
  simp only [encodeBlock] at h
  have h2 := finFunctionFinEquiv.injective (Fin.val_injective h)
  funext i
  exact (Fintype.equivFin α).injective (congrFun h2 i)

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem encodeBlock_lt (m : ℕ) (x : Fin m → α) :
    encodeBlock (α := α) m x < Fintype.card α ^ m :=
  (finFunctionFinEquiv fun i ↦ Fintype.equivFin α (x i)).isLt

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem encodeBlock_eq_ofDigits (m : ℕ) (x : Fin m → α) :
    encodeBlock (α := α) m x
      = Nat.ofDigits (Fintype.card α) (List.ofFn fun i ↦ (Fintype.equivFin α (x i)).val) := by
  rw [ofDigits_ofFn, encodeBlock, finFunctionFinEquiv_apply]

end Block

/-! ### Base-conversion bridges (bit length `2^k` ↔ natural-log `exp`) -/

theorem log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

theorem two_pow_eq_exp (k : ℕ) : ((2 : ℝ) ^ k) = Real.exp ((k : ℝ) * Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem exp_le_two_pow_iff (t : ℝ) (k : ℕ) :
    Real.exp t ≤ (2 : ℝ) ^ k ↔ t ≤ (k : ℝ) * Real.log 2 := by
  rw [two_pow_eq_exp, Real.exp_le_exp]

/-! ### The entropy-rate theorem -/

section Rate
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Xs : ℕ → Ω → α)

omit [DecidableEq α] [Nonempty α] in
/-- The block-complexity integrand takes finitely many values (the block space is
finite), so it is a bounded measurable function and hence integrable.
@audit:ok -/
theorem integrable_condComplexity_jointRV (hXs : ∀ i, Measurable (Xs i)) (n : ℕ) :
    Integrable (fun ω ↦ (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ)) μ := by
  classical
  -- The block space `Fin n → α` is finite, so any function out of it is measurable.
  have hmeas_g : Measurable (fun b : Fin n → α ↦ (condComplexity (encodeBlock n b) n : ℝ)) :=
    measurable_of_finite _
  have hmeas : Measurable
      (fun ω ↦ (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ)) :=
    hmeas_g.comp (measurable_jointRV Xs hXs n)
  -- Bounded by the (finite) supremum over the finite block space.
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    ((Finset.univ.sup (fun b : Fin n → α ↦ condComplexity (encodeBlock n b) n) : ℕ) : ℝ) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact_mod_cast Finset.le_sup (f := fun b : Fin n → α ↦ condComplexity (encodeBlock n b) n)
    (Finset.mem_univ (jointRV Xs n ω))

/-- Per-string upper bound on the strongly typical set (method of types): a typical
block is described by its type descriptor together with its index inside the type
class, costing `n · (H + ε·L)/log 2 + o(n)` bits. The `o(n)` overhead (the type
descriptor `|α|·log n` and the pairing/framing constant) is absorbed as an
arbitrarily small linear slack `n · δ`, valid for all large `n`.
@residual(plan:kolmogorov-p4-upper) -/
theorem condComplexity_block_typical_le
    (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ a : α, 0 < (μ.map (Xs 0)).real {a})
    {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ b : Fin n → α, b ∈ stronglyTypicalSet μ Xs n ε →
      (condComplexity (encodeBlock n b) n : ℝ)
        ≤ (n : ℝ) * ((entropy μ (Xs 0) + ε * logSumAbs μ Xs) / Real.log 2) + (n : ℝ) * δ := by
  sorry

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Uniform per-string upper bound: every length-`n` block is describable by echoing
its base-`card α` numeral, costing `natLen ≤ n · ⌈log₂ card α⌉` bits plus the literal
flag, so `C(x | n) ≤ (⌈log₂ card α⌉ + 1) · (n + 1)`. -/
theorem condComplexity_block_uniform_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (b : Fin n → α),
      (condComplexity (encodeBlock n b) n : ℝ) ≤ C * ((n : ℝ) + 1) := by
  classical
  refine ⟨(Nat.clog 2 (Fintype.card α) : ℝ) + 1, by positivity, fun n b ↦ ?_⟩
  set k0 : ℕ := Nat.clog 2 (Fintype.card α) with hk0
  -- `card α ≤ 2 ^ k0`, so each of the `n` base-`card α` digits fits in `k0` bits.
  have hcard : Fintype.card α ≤ 2 ^ k0 := by rw [hk0]; exact Nat.le_pow_clog (by norm_num) _
  have hpow : Fintype.card α ^ n ≤ 2 ^ (k0 * n) := by
    calc Fintype.card α ^ n ≤ (2 ^ k0) ^ n := Nat.pow_le_pow_left hcard n
      _ = 2 ^ (k0 * n) := by rw [← pow_mul]
  have hlt : encodeBlock n b < 2 ^ (k0 * n) := lt_of_lt_of_le (encodeBlock_lt n b) hpow
  have hnat : natLen (encodeBlock n b) ≤ k0 * n := natLen_le_of_lt_two_pow _ _ hlt
  -- Literal echo: `C(x | n) ≤ natLen x + 1 ≤ k0 · n + 1`.
  have hcc : condComplexity (encodeBlock n b) n ≤ k0 * n + 1 :=
    (condComplexity_le_natLen_add_one _ _).trans (by omega)
  have hccR : (condComplexity (encodeBlock n b) n : ℝ) ≤ (k0 : ℝ) * n + 1 := by
    calc (condComplexity (encodeBlock n b) n : ℝ)
        ≤ ((k0 * n + 1 : ℕ) : ℝ) := by exact_mod_cast hcc
      _ = (k0 : ℝ) * n + 1 := by push_cast; ring
  -- `k0 · n + 1 ≤ (k0 + 1)(n + 1)` since the difference is `k0 + n ≥ 0`.
  refine hccR.trans ?_
  nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) k0]

/-- Upper half: eventually the normalized expected complexity is within `ε` above
`H / log 2`. Method-of-types assembly: split the integral at the strongly typical
set, bound the typical part by `condComplexity_block_typical_le` and the atypical
part by `condComplexity_block_uniform_le`, then let the atypical mass vanish. The
assembly itself is unconditional, resting only on the two per-string bounds above. -/
theorem kolmogorov_entropy_rate_upper
    (hXs : ∀ i, Measurable (Xs i))
    (_hindep_full : iIndepFun (fun i ↦ Xs i) μ)
    (hindep_pair : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hpos : ∀ a : α, 0 < (μ.map (Xs 0)).real {a}) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (1 / (n : ℝ)) * ∫ ω, (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) ∂μ
        ≤ entropy μ (Xs 0) / Real.log 2 + ε := by
  intro ε hε
  have hlog2 : (0 : ℝ) < Real.log 2 := log_two_pos
  have hL_nn : 0 ≤ logSumAbs μ Xs := logSumAbs_nonneg μ Xs
  have hH_nn : 0 ≤ entropy μ (Xs 0) := entropy_nonneg μ (Xs 0) (hXs 0)
  -- Typicality slack `ε₁` and linear-overhead slack `δ`, each contributing `≤ ε/3`.
  set ε₁ : ℝ := ε * Real.log 2 / (3 * (logSumAbs μ Xs + 1)) with hε₁_def
  have hε₁_pos : 0 < ε₁ := by rw [hε₁_def]; positivity
  set δ : ℝ := ε / 3 with hδ_def
  have hδ_pos : 0 < δ := by positivity
  have hε₁L : ε₁ * logSumAbs μ Xs / Real.log 2 ≤ ε / 3 := by
    have hcancel : ε₁ * logSumAbs μ Xs / Real.log 2
        = ε * logSumAbs μ Xs / (3 * (logSumAbs μ Xs + 1)) := by
      rw [hε₁_def]; field_simp
    rw [hcancel, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hε.le hL_nn, hε.le]
  -- Uniform per-string bound.
  obtain ⟨C, hC_nn, hCbound⟩ := condComplexity_block_uniform_le (α := α)
  -- Typical per-string bound (eventually in `n`).
  have h5 := condComplexity_block_typical_le μ Xs hXs hpos hε₁_pos hδ_pos
  -- Atypical mass tends to `0`.
  have hmass_real : Tendsto
      (fun n : ℕ ↦ μ.real {ω | jointRV Xs n ω ∈ stronglyTypicalSet μ Xs n ε₁}) atTop (𝓝 1) := by
    have h1 := stronglyTypicalSet_prob_tendsto_one μ Xs hXs hindep_pair hident hε₁_pos
    have h2 := (ENNReal.tendsto_toReal (by simp : (1 : ENNReal) ≠ ⊤)).comp h1
    simpa [Function.comp_def, measureReal_def] using h2
  have hatyp : Tendsto
      (fun n : ℕ ↦ μ.real {ω | jointRV Xs n ω ∉ stronglyTypicalSet μ Xs n ε₁}) atTop (𝓝 0) := by
    have hcompl : ∀ n : ℕ, μ.real {ω | jointRV Xs n ω ∉ stronglyTypicalSet μ Xs n ε₁}
        = 1 - μ.real {ω | jointRV Xs n ω ∈ stronglyTypicalSet μ Xs n ε₁} := by
      intro n
      have hmeasT : MeasurableSet {ω | jointRV Xs n ω ∈ stronglyTypicalSet μ Xs n ε₁} :=
        (measurable_jointRV Xs hXs n) (measurableSet_stronglyTypicalSet μ Xs n ε₁)
      have hc : {ω | jointRV Xs n ω ∉ stronglyTypicalSet μ Xs n ε₁}
          = {ω | jointRV Xs n ω ∈ stronglyTypicalSet μ Xs n ε₁}ᶜ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      rw [hc, measureReal_compl hmeasT, probReal_univ]
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub hmass_real
    simp only [sub_self] at h2
    exact h2.congr fun n ↦ (hcompl n).symm
  -- The atypical contribution to the normalized integral vanishes.
  have hCoef : Tendsto (fun n : ℕ ↦ C * ((n : ℝ) + 1) / n) atTop (𝓝 C) := by
    have h1 : Tendsto (fun n : ℕ ↦ (1 : ℝ) + 1 / (n : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ ↦ C * (1 + 1 / (n : ℝ))) atTop (𝓝 (C * 1)) :=
      tendsto_const_nhds.mul h1
    rw [mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have hCterm : Tendsto
      (fun n : ℕ ↦ C * ((n : ℝ) + 1) / n *
        μ.real {ω | jointRV Xs n ω ∉ stronglyTypicalSet μ Xs n ε₁}) atTop (𝓝 0) := by
    have := hCoef.mul hatyp
    simpa using this
  -- Assemble the eventual bound.
  filter_upwards [h5, eventually_gt_atTop 0,
    hCterm.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 3 by positivity))]
    with n hn5 hn hCsmall
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  set S : Set Ω := {ω | jointRV Xs n ω ∈ stronglyTypicalSet μ Xs n ε₁} with hS_def
  have hS_meas : MeasurableSet S :=
    (measurable_jointRV Xs hXs n) (measurableSet_stronglyTypicalSet μ Xs n ε₁)
  have hScompl : Sᶜ = {ω | jointRV Xs n ω ∉ stronglyTypicalSet μ Xs n ε₁} := by
    rw [hS_def]; ext ω; simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
  set f : Ω → ℝ := fun ω ↦ (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) with hf_def
  have hf_int : Integrable f μ := integrable_condComplexity_jointRV μ Xs hXs n
  set Bt : ℝ := (n : ℝ) * ((entropy μ (Xs 0) + ε₁ * logSumAbs μ Xs) / Real.log 2)
    + (n : ℝ) * δ with hBt_def
  have hBt_nn : 0 ≤ Bt := by
    rw [hBt_def]
    refine add_nonneg (mul_nonneg (by positivity) (div_nonneg (add_nonneg hH_nn ?_) hlog2.le))
      (by positivity)
    exact mul_nonneg hε₁_pos.le hL_nn
  set Bu : ℝ := C * ((n : ℝ) + 1) with hBu_def
  -- Split the integral at the typical set.
  have hsplit : ∫ ω, f ω ∂μ = ∫ ω in S, f ω ∂μ + ∫ ω in Sᶜ, f ω ∂μ :=
    (integral_add_compl hS_meas hf_int).symm
  have hSle1 : μ.real S ≤ 1 := by
    calc μ.real S ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ S) (measure_ne_top μ _)
      _ = 1 := probReal_univ
  -- Typical part `≤ Bt`.
  have htyp_int : ∫ ω in S, f ω ∂μ ≤ Bt := by
    calc ∫ ω in S, f ω ∂μ ≤ ∫ _ω in S, Bt ∂μ := by
          refine setIntegral_mono_on hf_int.integrableOn
            (integrableOn_const (measure_ne_top μ S)) hS_meas ?_
          intro ω hω; exact hn5 (jointRV Xs n ω) hω
      _ = μ.real S • Bt := by rw [setIntegral_const, measureReal_def]
      _ = μ.real S * Bt := by rw [smul_eq_mul]
      _ ≤ 1 * Bt := mul_le_mul_of_nonneg_right hSle1 hBt_nn
      _ = Bt := one_mul Bt
  -- Atypical part `≤ Bu · (atypical mass)`.
  have hatyp_int : ∫ ω in Sᶜ, f ω ∂μ ≤ Bu * μ.real Sᶜ := by
    calc ∫ ω in Sᶜ, f ω ∂μ ≤ ∫ _ω in Sᶜ, Bu ∂μ := by
          refine setIntegral_mono_on hf_int.integrableOn
            (integrableOn_const (measure_ne_top μ Sᶜ)) hS_meas.compl ?_
          intro ω _; exact hCbound n (jointRV Xs n ω)
      _ = μ.real Sᶜ • Bu := by rw [setIntegral_const, measureReal_def]
      _ = Bu * μ.real Sᶜ := by rw [smul_eq_mul, mul_comm]
  have hInt_le : ∫ ω, f ω ∂μ ≤ Bt + Bu * μ.real Sᶜ := by
    rw [hsplit]; exact add_le_add htyp_int hatyp_int
  -- Normalize and bound each slack by `ε/3`.
  have hval : (1 / (n : ℝ)) * (Bt + Bu * μ.real Sᶜ)
      = (entropy μ (Xs 0) + ε₁ * logSumAbs μ Xs) / Real.log 2 + δ
        + C * ((n : ℝ) + 1) / n * μ.real Sᶜ := by
    rw [hBt_def, hBu_def]; field_simp
  have hCsmall' : C * ((n : ℝ) + 1) / n * μ.real Sᶜ < ε / 3 := by rw [hScompl]; exact hCsmall
  calc (1 / (n : ℝ)) * ∫ ω, f ω ∂μ
      ≤ (1 / (n : ℝ)) * (Bt + Bu * μ.real Sᶜ) :=
        mul_le_mul_of_nonneg_left hInt_le (by positivity)
    _ = (entropy μ (Xs 0) + ε₁ * logSumAbs μ Xs) / Real.log 2 + δ
        + C * ((n : ℝ) + 1) / n * μ.real Sᶜ := hval
    _ = entropy μ (Xs 0) / Real.log 2 + ε₁ * logSumAbs μ Xs / Real.log 2 + δ
        + C * ((n : ℝ) + 1) / n * μ.real Sᶜ := by rw [add_div]
    _ ≤ entropy μ (Xs 0) / Real.log 2 + ε := by rw [hδ_def]; linarith [hε₁L, hCsmall']

/-- On the strongly-typical set, the empirical entropy of a block's type is bounded
above by the true entropy plus the linear typicality slack `ε · L`. -/
theorem entropyByCount_le_of_strongTypical
    (hXs : ∀ i, Measurable (Xs i))
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (x : Fin n → α)
    (hx : x ∈ stronglyTypicalSet μ Xs n ε)
    (hpos : ∀ a : α, 0 < (μ.map (Xs 0)).real {a}) :
    entropyByCount (typeCount x) n ≤ entropy μ (Xs 0) + ε * logSumAbs μ Xs := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  haveI : IsProbabilityMeasure (μ.map (Xs 0)) :=
    Measure.isProbabilityMeasure_map (hXs 0).aemeasurable
  have hqX_sum_one : (∑ a : α, (μ.map (Xs 0)).real {a}) = 1 :=
    sum_measureReal_singleton_eq_one (μ.map (Xs 0))
  have hT_sum : (∑ a : α, typeCount x a) = n := sum_typeCount x
  exact conditionalKL_HXemp_le μ Xs hXs hn_pos hn hn_ne x hx
    (fun a ↦ (μ.map (Xs 0)).real {a}) (fun _ ↦ rfl) hpos hqX_sum_one
    (typeCount x) (fun _ ↦ rfl) hT_sum
    (entropy μ (Xs 0)) (logSumAbs μ Xs) (entropyByCount (typeCount x) n) rfl rfl rfl

/-! ### Lower-half building blocks -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- The block law of an i.i.d. source is the product measure of the marginal.
@audit:ok -/
theorem blockLaw_eq_pi (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i ↦ Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (n : ℕ) :
    μ.map (jointRV Xs n) = Measure.pi (fun _ : Fin n ↦ μ.map (Xs 0)) := by
  classical
  set Xs' : Fin n → Ω → α := fun i ↦ Xs i with hXs'_def
  have hXs'_meas : ∀ i : Fin n, AEMeasurable (Xs' i) μ := fun i ↦ (hXs i).aemeasurable
  have hindep' : iIndepFun Xs' μ :=
    hindep_full.precomp (g := fun i : Fin n ↦ (i : ℕ)) Fin.val_injective
  have h_pi_form : μ.map (fun ω i ↦ Xs' i ω) = Measure.pi (fun i ↦ μ.map (Xs' i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map hXs'_meas).mp hindep'
  have h_jointRV_eq : jointRV Xs n = fun ω (i : Fin n) ↦ Xs' i ω := rfl
  rw [h_jointRV_eq, h_pi_form]
  congr 1
  funext i
  show μ.map (Xs i) = μ.map (Xs 0)
  exact (hident i).map_eq

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- The probability of a single block factors over the coordinates.
@audit:ok -/
theorem blockProb_eq_prod (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i ↦ Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (n : ℕ) (b : Fin n → α) :
    (μ.map (jointRV Xs n)).real {b} = ∏ i : Fin n, (μ.map (Xs 0)).real {b i} := by
  haveI : IsProbabilityMeasure (μ.map (Xs 0)) :=
    Measure.isProbabilityMeasure_map (hXs 0).aemeasurable
  rw [blockLaw_eq_pi μ Xs hXs hindep_full hident n]
  show ((Measure.pi (fun _ : Fin n ↦ μ.map (Xs 0))) {b}).toReal
    = ∏ i : Fin n, (μ.map (Xs 0)).real {b i}
  rw [Measure.pi_singleton, ENNReal.toReal_prod]
  rfl

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
/-- A typical block has product mass at most `exp (-n (H - ε))` (the mirror of the
`typicalSet_card_le` lower bound).
@audit:ok -/
theorem typicalSet_blockProb_le
    (hpos : ∀ a : α, 0 < (μ.map (Xs 0)).real {a})
    (n : ℕ) {ε : ℝ} (b : Fin n → α) (hb : b ∈ typicalSet μ Xs n ε) :
    ∏ i : Fin n, (μ.map (Xs 0)).real {b i}
      ≤ Real.exp (-((n : ℝ) * (entropy μ (Xs 0) - ε))) := by
  set P : α → ℝ := fun x ↦ (μ.map (Xs 0)).real {x} with hP_def
  have hexp_pmfLog : ∀ x, Real.exp (-(pmfLog μ Xs x)) = P x := by
    intro x
    have hlog : -(pmfLog μ Xs x) = Real.log (P x) := by simp [pmfLog, hP_def]
    rw [hlog, Real.exp_log (hpos x)]
  have hprod_eq : ∏ i : Fin n, P (b i)
      = Real.exp (-(∑ i : Fin n, pmfLog μ Xs (b i))) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ ↦ (hexp_pmfLog (b i)).symm
  rw [hprod_eq]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0; simp
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    rw [mem_typicalSet_iff] at hb
    have hlower : -ε < (∑ i : Fin n, pmfLog μ Xs (b i)) / n - entropy μ (Xs 0) :=
      (abs_lt.mp hb).1
    have h1 : entropy μ (Xs 0) - ε < (∑ i : Fin n, pmfLog μ Xs (b i)) / n := by linarith
    have h2 := (lt_div_iff₀ hnR).mp h1
    have hsum_ge : (n : ℝ) * (entropy μ (Xs 0) - ε) ≤ ∑ i : Fin n, pmfLog μ Xs (b i) := by
      rw [mul_comm]; exact h2.le
    apply Real.exp_le_exp.mpr
    linarith

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- Fewer than `2 ^ k` blocks have conditional complexity below `k`, via the
injective block encoding and the counting bound `condIncompressible_count`.
@audit:ok -/
theorem compressibleBlocks_card_lt (n k : ℕ) :
    (({b : Fin n → α | condComplexity (encodeBlock n b) n < k}.ncard : ℕ) : ℝ) < 2 ^ k := by
  have hinj : Function.Injective (encodeBlock (α := α) n) := encodeBlock_injective n
  have hsub : encodeBlock n '' {b : Fin n → α | condComplexity (encodeBlock n b) n < k}
      ⊆ {m : ℕ | condComplexity m n < k} := by
    rintro _ ⟨b, hb, rfl⟩; exact hb
  have hle : {b : Fin n → α | condComplexity (encodeBlock n b) n < k}.ncard
      ≤ {m : ℕ | condComplexity m n < k}.ncard := by
    calc {b : Fin n → α | condComplexity (encodeBlock n b) n < k}.ncard
        = (encodeBlock n '' {b : Fin n → α | condComplexity (encodeBlock n b) n < k}).ncard :=
          (Set.ncard_image_of_injective _ hinj).symm
      _ ≤ {m : ℕ | condComplexity m n < k}.ncard :=
          Set.ncard_le_ncard hsub (condComplexity_lt_finite n k)
  exact_mod_cast lt_of_le_of_lt hle (condIncompressible_count n k)

omit [DecidableEq α] [Nonempty α] in
/-- The mass of the typical-and-compressible blocks is at most
`2 ^ k · exp (-n (H - ε₁))` (product bound times a count below `2 ^ k`).
@audit:ok -/
theorem compressible_prob_le (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i ↦ Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hpos : ∀ a : α, 0 < (μ.map (Xs 0)).real {a})
    (n k : ℕ) {ε₁ : ℝ} :
    μ.real {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε₁ ∧
        condComplexity (encodeBlock n (jointRV Xs n ω)) n < k}
      ≤ (2 : ℝ) ^ k * Real.exp (-((n : ℝ) * (entropy μ (Xs 0) - ε₁))) := by
  classical
  set S : Set (Fin n → α) :=
    {b | b ∈ typicalSet μ Xs n ε₁ ∧ condComplexity (encodeBlock n b) n < k} with hS_def
  have hSfin : S.Finite := S.toFinite
  have hcoe : (↑hSfin.toFinset : Set (Fin n → α)) = S := hSfin.coe_toFinset
  have hpre : ∀ b : Fin n → α, MeasurableSet (jointRV Xs n ⁻¹' {b}) :=
    fun b ↦ (measurable_jointRV Xs hXs n) (measurableSet_singleton b)
  show μ.real (jointRV Xs n ⁻¹' S)
    ≤ (2 : ℝ) ^ k * Real.exp (-((n : ℝ) * (entropy μ (Xs 0) - ε₁)))
  -- Decompose the measure of the preimage as a finite sum over singleton fibers.
  have hsum : μ (jointRV Xs n ⁻¹' S) = ∑ b ∈ hSfin.toFinset, μ (jointRV Xs n ⁻¹' {b}) := by
    rw [sum_measure_preimage_singleton hSfin.toFinset (fun b _ ↦ hpre b), hcoe]
  have hbad_real : μ.real (jointRV Xs n ⁻¹' S)
      = ∑ b ∈ hSfin.toFinset, μ.real (jointRV Xs n ⁻¹' {b}) := by
    rw [measureReal_def, hsum, ENNReal.toReal_sum (fun b _ ↦ measure_ne_top μ _)]
    simp only [measureReal_def]
  rw [hbad_real]
  -- Each fiber mass factors over coordinates.
  have hterm : ∀ b : Fin n → α,
      μ.real (jointRV Xs n ⁻¹' {b}) = ∏ i : Fin n, (μ.map (Xs 0)).real {b i} := by
    intro b
    have hmap : μ (jointRV Xs n ⁻¹' {b}) = (μ.map (jointRV Xs n)) {b} :=
      (Measure.map_apply (measurable_jointRV Xs hXs n) (measurableSet_singleton b)).symm
    rw [measureReal_def, hmap]
    exact blockProb_eq_prod μ Xs hXs hindep_full hident n b
  -- The number of typical-and-compressible blocks is below `2 ^ k`.
  have hScard : (hSfin.toFinset.card : ℝ) ≤ (2 : ℝ) ^ k := by
    have h1 : hSfin.toFinset.card = S.ncard := (Set.ncard_eq_toFinset_card S hSfin).symm
    have hSsub : S ⊆ {b : Fin n → α | condComplexity (encodeBlock n b) n < k} :=
      fun b hb ↦ hb.2
    have h2 : S.ncard ≤ {b : Fin n → α | condComplexity (encodeBlock n b) n < k}.ncard :=
      Set.ncard_le_ncard hSsub (Set.toFinite _)
    rw [h1]
    calc (S.ncard : ℝ)
        ≤ ({b : Fin n → α | condComplexity (encodeBlock n b) n < k}.ncard : ℝ) := by
          exact_mod_cast h2
      _ ≤ (2 : ℝ) ^ k := (compressibleBlocks_card_lt (α := α) n k).le
  calc ∑ b ∈ hSfin.toFinset, μ.real (jointRV Xs n ⁻¹' {b})
      = ∑ b ∈ hSfin.toFinset, ∏ i : Fin n, (μ.map (Xs 0)).real {b i} :=
        Finset.sum_congr rfl fun b _ ↦ hterm b
    _ ≤ ∑ _b ∈ hSfin.toFinset, Real.exp (-((n : ℝ) * (entropy μ (Xs 0) - ε₁))) := by
        apply Finset.sum_le_sum
        intro b hb
        have hbT : b ∈ typicalSet μ Xs n ε₁ := ((hSfin.mem_toFinset).mp hb).1
        exact typicalSet_blockProb_le μ Xs hpos n b hbT
    _ = (hSfin.toFinset.card : ℝ) * Real.exp (-((n : ℝ) * (entropy μ (Xs 0) - ε₁))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ k * Real.exp (-((n : ℝ) * (entropy μ (Xs 0) - ε₁))) :=
        mul_le_mul_of_nonneg_right hScard (Real.exp_nonneg _)

/-- The floor `⌊n c⌋₊`, normalized by `n`, converges to `c` (for `c ≥ 0`).
@audit:ok -/
theorem floor_mul_div_tendsto (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ ↦ (⌊(n : ℝ) * c⌋₊ : ℝ) / n) atTop (𝓝 c) := by
  have hg : Tendsto (fun n : ℕ ↦ c - 1 / (n : ℝ)) atTop (𝓝 c) := by
    simpa using (tendsto_const_nhds (x := c)).sub tendsto_one_div_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hfloor_lt : (n : ℝ) * c < (⌊(n : ℝ) * c⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [le_div_iff₀ hnR]
    have heq : (c - 1 / (n : ℝ)) * n = (n : ℝ) * c - 1 := by field_simp
    rw [heq]; linarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hfloor_le : (⌊(n : ℝ) * c⌋₊ : ℝ) ≤ (n : ℝ) * c := Nat.floor_le (by positivity)
    rw [div_le_iff₀ hnR]
    linarith [hfloor_le, mul_comm (n : ℝ) c]

omit [DecidableEq α] [Nonempty α] in
/-- Lower half: eventually the normalized expected complexity is within `ε` below
`H / log 2`. The counting bound `condIncompressible_count` caps how many blocks can
be compressed below `k`, while the strong-typicality mass spreads over `≈ exp (nH)`
blocks; a Markov step then pushes the average up to `H / log 2 - ε`.
@audit:ok -/
theorem kolmogorov_entropy_rate_lower
    (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i ↦ Xs i) μ)
    (hindep_pair : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hpos : ∀ a : α, 0 < (μ.map (Xs 0)).real {a}) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      entropy μ (Xs 0) / Real.log 2 - ε
        ≤ (1 / (n : ℝ)) * ∫ ω, (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) ∂μ := by
  intro ε hε
  have hL_pos : 0 < Real.log 2 := log_two_pos
  have hLne : Real.log 2 ≠ 0 := ne_of_gt hL_pos
  have hH_nn : 0 ≤ entropy μ (Xs 0) := entropy_nonneg μ (Xs 0) (hXs 0)
  rcases le_or_gt (entropy μ (Xs 0) / Real.log 2 - ε) 0 with htriv | hpos_target
  · -- Trivial case: the target is nonpositive, and the average is nonnegative.
    filter_upwards with n
    have hint_nn : 0 ≤ ∫ ω, (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) ∂μ :=
      integral_nonneg fun ω ↦ by positivity
    have hmul_nn : 0 ≤ (1 / (n : ℝ)) *
        ∫ ω, (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) ∂μ := by
      apply mul_nonneg _ hint_nn; positivity
    linarith
  -- Hard case: `H / log 2 - ε > 0`.
  set γ : ℝ := ε * Real.log 2 / 2 with hγ_def
  set ε₁ : ℝ := γ / 2 with hε₁_def
  have hγ_pos : 0 < γ := by rw [hγ_def]; positivity
  have hε₁_pos : 0 < ε₁ := by rw [hε₁_def]; positivity
  have hHγ_pos : 0 < entropy μ (Xs 0) - γ := by
    have h1 : ε < entropy μ (Xs 0) / Real.log 2 := by linarith
    rw [lt_div_iff₀ hL_pos] at h1
    rw [hγ_def]; linarith [h1, mul_pos hε hL_pos]
  have hc_nn : 0 ≤ (entropy μ (Xs 0) - γ) / Real.log 2 := by positivity
  set k : ℕ → ℕ := fun n ↦ ⌊(n : ℝ) * ((entropy μ (Xs 0) - γ) / Real.log 2)⌋₊ with hk_def
  -- Markov half.
  have hE1 : ∀ n : ℕ, (k n : ℝ) / n *
      μ.real {ω | (k n : ℝ) ≤ (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ)}
      ≤ (1 / (n : ℝ)) * ∫ ω, (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) ∂μ := by
    intro n
    have hf_nn : 0 ≤ᵐ[μ]
        fun ω ↦ (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) :=
      Filter.Eventually.of_forall fun ω ↦ Nat.cast_nonneg _
    have hf_int := integrable_condComplexity_jointRV μ Xs hXs n
    have hmarkov := mul_meas_ge_le_integral_of_nonneg hf_nn hf_int (k n : ℝ)
    have hnn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    calc (k n : ℝ) / n *
          μ.real {ω | (k n : ℝ) ≤ (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ)}
        = (1 / (n : ℝ)) * ((k n : ℝ) *
            μ.real {ω | (k n : ℝ) ≤ (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ)}) := by
          ring
      _ ≤ (1 / (n : ℝ)) *
            ∫ ω, (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) ∂μ :=
          mul_le_mul_of_nonneg_left hmarkov hnn
  -- The floor-normalized threshold converges to `(H - γ) / log 2`.
  have hfloor : Tendsto (fun n : ℕ ↦ (k n : ℝ) / n) atTop
      (𝓝 ((entropy μ (Xs 0) - γ) / Real.log 2)) := by
    simp only [hk_def]
    exact floor_mul_div_tendsto ((entropy μ (Xs 0) - γ) / Real.log 2) hc_nn
  -- The mass above the threshold converges to `1`.
  have hq_lim : Tendsto (fun n : ℕ ↦
      μ.real {ω | (k n : ℝ) ≤ (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ)})
      atTop (𝓝 1) := by
    have hg_meas : ∀ n : ℕ, Measurable
        (fun ω ↦ (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ)) := fun n ↦
      (measurable_of_finite
        (fun b : Fin n → α ↦ (condComplexity (encodeBlock n b) n : ℝ))).comp
        (measurable_jointRV Xs hXs n)
    -- `q n = 1 - bad n`.
    have hq_compl : ∀ n : ℕ,
        μ.real {ω | (k n : ℝ) ≤ (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ)}
        = 1 - μ.real
            {ω | (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) < (k n : ℝ)} := by
      intro n
      have hmeas_lt : MeasurableSet
          {ω | (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) < (k n : ℝ)} :=
        measurableSet_lt (hg_meas n) measurable_const
      have hcompl : {ω | (k n : ℝ) ≤ (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ)}
          = {ω | (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) < (k n : ℝ)}ᶜ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
      rw [hcompl, measureReal_compl hmeas_lt, probReal_univ]
    -- The non-typical mass converges to `0`.
    have htyp : Tendsto (fun n : ℕ ↦ μ.real {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε₁})
        atTop (𝓝 1) := by
      have h1 := typicalSet_prob_tendsto_one μ Xs hXs hindep_pair hident hε₁_pos
      have h2 := (ENNReal.tendsto_toReal (by simp : (1 : ENNReal) ≠ ⊤)).comp h1
      simpa [Function.comp_def, measureReal_def] using h2
    have hnontyp_lim :
        Tendsto (fun n : ℕ ↦ μ.real {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε₁})
        atTop (𝓝 0) := by
      have hcompl : ∀ n : ℕ, μ.real {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε₁}
          = 1 - μ.real {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε₁} := by
        intro n
        have hmeasT : MeasurableSet {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε₁} :=
          (measurable_jointRV Xs hXs n) (measurableSet_typicalSet μ Xs n ε₁)
        have hcompl' : {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε₁}
            = {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε₁}ᶜ := by
          ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
        rw [hcompl', measureReal_compl hmeasT, probReal_univ]
      have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub htyp
      simp only [sub_self] at h2
      exact h2.congr fun n ↦ (hcompl n).symm
    -- The typical-and-compressible mass is dominated by `exp (-n γ/2) → 0`.
    have hcomp_le : ∀ n : ℕ,
        μ.real {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε₁ ∧
            condComplexity (encodeBlock n (jointRV Xs n ω)) n < k n}
        ≤ Real.exp (-((n : ℝ) * (γ / 2))) := by
      intro n
      have hcp := compressible_prob_le μ Xs hXs hindep_full hident hpos n (k n) (ε₁ := ε₁)
      have hpow : (2 : ℝ) ^ (k n) = Real.exp ((k n : ℝ) * Real.log 2) := two_pow_eq_exp (k n)
      have hkL : (k n : ℝ) * Real.log 2 ≤ (n : ℝ) * (entropy μ (Xs 0) - γ) := by
        have hfl : (k n : ℝ) ≤ (n : ℝ) * ((entropy μ (Xs 0) - γ) / Real.log 2) :=
          Nat.floor_le (by positivity)
        have hmul : (k n : ℝ) * Real.log 2
            ≤ (n : ℝ) * ((entropy μ (Xs 0) - γ) / Real.log 2) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hfl hL_pos.le
        rwa [mul_assoc, div_mul_cancel₀ _ hLne] at hmul
      refine hcp.trans ?_
      rw [hpow, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hkey : (n : ℝ) * (entropy μ (Xs 0) - γ) + -((n : ℝ) * (entropy μ (Xs 0) - ε₁))
          = -((n : ℝ) * (γ / 2)) := by rw [hε₁_def]; ring
      linarith [hkL, hkey]
    have hcomp_lim : Tendsto (fun n : ℕ ↦
        μ.real {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε₁ ∧
            condComplexity (encodeBlock n (jointRV Xs n ω)) n < k n})
        atTop (𝓝 0) := by
      have hg : Tendsto (fun n : ℕ ↦ Real.exp (-((n : ℝ) * (γ / 2)))) atTop (𝓝 0) := by
        have hrw : ∀ n : ℕ, Real.exp (-((n : ℝ) * (γ / 2))) = (Real.exp (-(γ / 2))) ^ n := by
          intro n
          rw [show -((n : ℝ) * (γ / 2)) = (n : ℝ) * (-(γ / 2)) from by ring, Real.exp_nat_mul]
        simp only [hrw]
        refine tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_nonneg _) ?_
        rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
        exact Real.exp_lt_exp.mpr (by linarith)
      exact squeeze_zero (fun n ↦ measureReal_nonneg) hcomp_le hg
    -- Bad mass squeezed to zero, hence `q → 1`.
    have hbad_lim : Tendsto (fun n : ℕ ↦
        μ.real {ω | (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) < (k n : ℝ)})
        atTop (𝓝 0) := by
      have hbad_le : ∀ n : ℕ,
          μ.real {ω | (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) < (k n : ℝ)}
          ≤ μ.real {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε₁}
            + μ.real {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε₁ ∧
                condComplexity (encodeBlock n (jointRV Xs n ω)) n < k n} := by
        intro n
        have hincl :
            {ω | (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) < (k n : ℝ)}
            ⊆ {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε₁}
              ∪ {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε₁ ∧
                  condComplexity (encodeBlock n (jointRV Xs n ω)) n < k n} := by
          intro ω hω
          simp only [Set.mem_setOf_eq] at hω
          have hlt_nat : condComplexity (encodeBlock n (jointRV Xs n ω)) n < k n := by
            exact_mod_cast hω
          by_cases hT : jointRV Xs n ω ∈ typicalSet μ Xs n ε₁
          · exact Or.inr ⟨hT, hlt_nat⟩
          · exact Or.inl hT
        calc μ.real {ω | (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) < (k n : ℝ)}
            ≤ μ.real ({ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε₁}
                ∪ {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε₁ ∧
                    condComplexity (encodeBlock n (jointRV Xs n ω)) n < k n}) :=
              measureReal_mono hincl
          _ ≤ μ.real {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε₁}
              + μ.real {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε₁ ∧
                  condComplexity (encodeBlock n (jointRV Xs n ω)) n < k n} :=
              measureReal_union_le _ _
      have hsum_lim := hnontyp_lim.add hcomp_lim
      simp only [add_zero] at hsum_lim
      exact squeeze_zero (fun n ↦ measureReal_nonneg) hbad_le hsum_lim
    have hfinal : Tendsto (fun n : ℕ ↦ 1 - μ.real
        {ω | (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) < (k n : ℝ)})
        atTop (𝓝 1) := by
      have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub hbad_lim
      simpa using h2
    exact hfinal.congr fun n ↦ (hq_compl n).symm
  -- Assemble: the product converges to `H / log 2 - ε/2 > H / log 2 - ε`.
  have hprod : Tendsto (fun n : ℕ ↦ (k n : ℝ) / n *
      μ.real {ω | (k n : ℝ) ≤ (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ)})
      atTop (𝓝 ((entropy μ (Xs 0) - γ) / Real.log 2 * 1)) := hfloor.mul hq_lim
  have hval : (entropy μ (Xs 0) - γ) / Real.log 2 * 1
      = entropy μ (Xs 0) / Real.log 2 - ε / 2 := by
    rw [mul_one, hγ_def]; field_simp
  rw [hval] at hprod
  have hE2 := hprod.eventually_const_lt
    (u := entropy μ (Xs 0) / Real.log 2 - ε) (by linarith)
  filter_upwards [hE2] with n hn
  exact le_of_lt (lt_of_lt_of_le hn (hE1 n))

/-- Kolmogorov complexity converges to the entropy rate: for an i.i.d. source, the
normalized expected conditional complexity of a length-`n` block tends to the
bit-rebased entropy `H(X) / log 2` (CT 2nd ed. Thm 14.3.1). -/
@[entry_point]
theorem kolmogorov_entropy_rate
    (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i ↦ Xs i) μ)
    (hindep_pair : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hpos : ∀ a : α, 0 < (μ.map (Xs 0)).real {a}) :
    Filter.Tendsto
      (fun n : ℕ ↦ (1 / (n : ℝ)) *
        ∫ ω, (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) ∂μ)
      Filter.atTop (nhds (entropy μ (Xs 0) / Real.log 2)) := by
  -- Squeeze between the two halves.
  rw [tendsto_order]
  refine ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩
  · filter_upwards [kolmogorov_entropy_rate_lower μ Xs hXs hindep_full hindep_pair hident hpos
      ((entropy μ (Xs 0) / Real.log 2 - b) / 2) (by linarith)] with n hn
    linarith
  · filter_upwards [kolmogorov_entropy_rate_upper μ Xs hXs hindep_full hindep_pair hident hpos
      ((b - entropy μ (Xs 0) / Real.log 2) / 2) (by linarith)] with n hn
    linarith

end Rate

end InformationTheory.Kolmogorov
