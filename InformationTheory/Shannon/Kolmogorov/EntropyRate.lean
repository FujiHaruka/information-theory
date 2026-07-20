import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Kolmogorov.Counting
import InformationTheory.Shannon.StrongTypicality
import Mathlib.Logic.Encodable.Pi
import Mathlib.Logic.Equiv.List
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

attribute [local instance] Fintype.toEncodable

section Block
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Injective encoding of a length-`m` block `Fin m → α` into a natural number,
using the `Encodable` structure a finite type carries. -/
noncomputable def encodeBlock (m : ℕ) (x : Fin m → α) : ℕ := Encodable.encode x

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem encodeBlock_injective (m : ℕ) : Function.Injective (encodeBlock (α := α) m) :=
  fun _ _ h ↦ Encodable.encode_injective h

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

/-- Upper half: eventually the normalized expected complexity is within `ε` above
`H / log 2`.
@residual(plan:kolmogorov-p4-upper) -/
theorem kolmogorov_entropy_rate_upper
    (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i ↦ Xs i) μ)
    (hindep_pair : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hpos : ∀ a : α, 0 < (μ.map (Xs 0)).real {a}) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (1 / (n : ℝ)) * ∫ ω, (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) ∂μ
        ≤ entropy μ (Xs 0) / Real.log 2 + ε := by
  sorry

/-! ### Lower-half building blocks -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- The block law of an i.i.d. source is the product measure of the marginal. -/
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
/-- The probability of a single block factors over the coordinates. -/
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
`typicalSet_card_le` lower bound). -/
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
injective block encoding and the counting bound `condIncompressible_count`. -/
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
`2 ^ k · exp (-n (H - ε₁))` (product bound times a count below `2 ^ k`). -/
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

/-- The floor `⌊n c⌋₊`, normalized by `n`, converges to `c` (for `c ≥ 0`). -/
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
blocks; a Markov step then pushes the average up to `H / log 2 - ε`. -/
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
