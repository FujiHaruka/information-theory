import InformationTheory.Meta.EntryPoint
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# LZ78 overhead control — empirical-entropy / mean bound

This file supplies the **analytic crux** behind the `o(n)` overhead estimate
required by the LZ78 achievability bound `ziv_aseventual_le_blockLogAvg₂`
(`InformationTheory/Shannon/LZ78/GreedyParsingImpl.lean`).

## Approach

The generic length-grouping inequality
(`card_mul_log_le_sum_group_mul_log_add_card_log`) controls
`c · log c ≤ ∑ … + c · log D` with a worst-case overhead `c · log D`,
where `D` is the number of distinct lengths. For the LZ78 parse `D ~ √n`, so
`c · log D ~ Θ(n)` does *not* vanish. The correct, sharper overhead is the
**empirical entropy** of the length profile,
`∑_g c_g · log (c / c_g)`, and the key analytic fact is that this empirical
entropy is controlled by the (log of the) **mean length** under the
average-length constraint `∑_l l · c_l = N`.

The proof is a one-shot application of the **log-sum inequality** (a pure
`Finset`/`Real` statement, derived here from convexity of `x ↦ x · log x`)
with a geometric reference distribution `b_l = θ^{l-1}` whose parameter
`θ = 1 - C/N` matches the empirical mean `N/C`. Concretely:

```
∑_l c_l · log (C / c_l) ≤ C · log (N / C) + C.
```

The constant `κ = 1` is forced by the geometric reference (a `log 2`
slack survives the uniform-profile check), and `C · log (N/C) = C · log(mean)`
is the `o(n)` term once `mean ~ log n` is supplied downstream.

## Main result

* `empirical_entropy_le_log_mean` — empirical entropy of a positive length
  profile is bounded by `C · log (mean) + C`, the `o(n)` overhead estimate.
-/

namespace InformationTheory.Shannon

open scoped BigOperators

/-- **Log-sum inequality** (finite form, local copy).

For nonnegative `a` and strictly positive `b` over a finite index set `s`,
`(∑ a)·log((∑ a)/(∑ b)) ≤ ∑ aᵢ·log(aᵢ/bᵢ)`. Convexity of `x ↦ x·log x`
through finite Jensen. (Re-proved locally to keep this file measure-free.) -/
theorem logSumInequality
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
      ≤ ∑ i ∈ s, a i * Real.log (a i / b i) := by
  classical
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs; simp
  set B : ℝ := ∑ i ∈ s, b i with hB_def
  have hB_pos : 0 < B := Finset.sum_pos hb hs
  have hB_ne : B ≠ 0 := hB_pos.ne'
  set A : ℝ := ∑ i ∈ s, a i with hA_def
  have h₀ : ∀ i ∈ s, 0 ≤ b i / B := fun i hi =>
    div_nonneg (hb i hi).le hB_pos.le
  have h₁ : ∑ i ∈ s, b i / B = 1 := by
    rw [← Finset.sum_div, ← hB_def, div_self hB_ne]
  have hmem : ∀ i ∈ s, a i / b i ∈ Set.Ici (0 : ℝ) := fun i hi => by
    simp only [Set.mem_Ici]; exact div_nonneg (ha i hi) (hb i hi).le
  have hJensen :=
    Real.convexOn_mul_log.map_sum_le (t := s)
      (w := fun i => b i / B) (p := fun i => a i / b i) h₀ h₁ hmem
  have hpt : ∀ i ∈ s, (b i / B) • (a i / b i) = a i / B := fun i hi => by
    have hbi : b i ≠ 0 := (hb i hi).ne'
    simp only [smul_eq_mul]
    field_simp
  have hlhs_arg : (∑ i ∈ s, (b i / B) • (a i / b i)) = A / B := by
    rw [Finset.sum_congr rfl hpt, ← Finset.sum_div, ← hA_def]
  have hrhs : (∑ i ∈ s, (b i / B) • ((a i / b i) * Real.log (a i / b i)))
      = ∑ i ∈ s, (a i / B) * Real.log (a i / b i) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hbi : b i ≠ 0 := (hb i hi).ne'
    simp only [smul_eq_mul]
    field_simp
  rw [hlhs_arg, hrhs] at hJensen
  have hkey := mul_le_mul_of_nonneg_right hJensen hB_pos.le
  calc A * Real.log (A / B)
      = (A / B) * Real.log (A / B) * B := by field_simp
    _ ≤ (∑ i ∈ s, (a i / B) * Real.log (a i / b i)) * B := hkey
    _ = ∑ i ∈ s, a i * Real.log (a i / b i) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        field_simp

/-- The finite geometric reference sum is bounded by the full geometric tail:
for `θ ∈ (0,1)` and lengths `l ≥ 1`,
`∑_{l ∈ L} θ^{l-1} ≤ (1 - θ)⁻¹`. -/
theorem sum_geom_shift_le_inv
    (L : Finset ℕ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hl1 : ∀ l ∈ L, 1 ≤ l) :
    (∑ l ∈ L, θ ^ (l - 1)) ≤ (1 - θ)⁻¹ := by
  classical
  -- Reindex `l ↦ l - 1`, injective on `L` since all lengths are `≥ 1`.
  have hInj : Set.InjOn (fun l => l - 1) (L : Set ℕ) := by
    intro x hx y hy hxy
    simp only at hxy
    have hx1 := hl1 x hx
    have hy1 := hl1 y hy
    omega
  have hreindex : (∑ l ∈ L, θ ^ (l - 1))
      = ∑ m ∈ L.image (fun l => l - 1), θ ^ m := by
    rw [Finset.sum_image hInj]
  rw [hreindex]
  -- Bound the finite sum by the full geometric series.
  have hsummable : Summable (fun n : ℕ => θ ^ n) :=
    summable_geometric_of_lt_one hθ0.le hθ1
  have hle := hsummable.sum_le_tsum (L.image (fun l => l - 1))
    (fun n _ => by positivity)
  rw [tsum_geometric_of_lt_one hθ0.le hθ1] at hle
  exact hle

/-- **Empirical-entropy / mean bound** (LZ78 overhead crux).

For a length profile `cf : ℕ → ℝ` supported on a finite set `L` of positive
lengths (`l ≥ 1`) with positive counts, writing `C = ∑ cf` (total count) and
`N = ∑ l · cf l` (total length), the empirical entropy is controlled by the
log of the mean length:

```
∑_l cf l · log (C / cf l) ≤ C · log (N / C) + C.
```

This is the `o(n)` overhead estimate: `C · log (N / C)` scales like
`C · log(mean length)`, which is `o(n)` once the mean is `~ log n`. -/
@[entry_point]
theorem empirical_entropy_le_log_mean
    (L : Finset ℕ) (cf : ℕ → ℝ)
    (hpos : ∀ l ∈ L, 0 < cf l)
    (hl1 : ∀ l ∈ L, 1 ≤ l)
    (hC : 0 < ∑ l ∈ L, cf l) :
    (∑ l ∈ L, cf l * Real.log ((∑ l ∈ L, cf l) / cf l))
      ≤ (∑ l ∈ L, cf l) * Real.log ((∑ l ∈ L, (l : ℝ) * cf l) / (∑ l ∈ L, cf l))
        + (∑ l ∈ L, cf l) := by
  classical
  set C : ℝ := ∑ l ∈ L, cf l with hC_def
  set N : ℝ := ∑ l ∈ L, (l : ℝ) * cf l with hN_def
  have hC_pos : 0 < C := hC
  have hC_ne : C ≠ 0 := hC_pos.ne'
  -- `C ≤ N` since each length `l ≥ 1`.
  have hCN : C ≤ N := by
    rw [hC_def, hN_def]
    refine Finset.sum_le_sum (fun l hl => ?_)
    have hl1' : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl1 l hl
    nlinarith [hpos l hl]
  -- Rewrite the LHS as `C · log C − ∑ cf l · log (cf l)`.
  have hLHS : (∑ l ∈ L, cf l * Real.log (C / cf l))
      = C * Real.log C - ∑ l ∈ L, cf l * Real.log (cf l) := by
    have hCsum : C * Real.log C = ∑ l ∈ L, cf l * Real.log C := by
      rw [← Finset.sum_mul, ← hC_def]
    rw [hCsum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    have hcfl : cf l ≠ 0 := (hpos l hl).ne'
    rw [Real.log_div hC_ne hcfl]
    ring
  rcases eq_or_lt_of_le hCN with hCN_eq | hCN_lt
  · -- Degenerate case `C = N`: every length is `1`, so `L = {1}` and LHS = 0.
    -- `N − C = ∑ (l − 1) · cf l = 0` forces each `l = 1`.
    have hall1 : ∀ l ∈ L, l = 1 := by
      intro l hl
      by_contra hne
      have hl2 : 2 ≤ l := by have := hl1 l hl; omega
      -- The `l` term contributes a strictly positive excess to `N − C`.
      have hexcess : C < N := by
        rw [hC_def, hN_def]
        refine Finset.sum_lt_sum (fun i hi => ?_) ⟨l, hl, ?_⟩
        · have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hl1 i hi
          nlinarith [hpos i hi]
        · have : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl2
          nlinarith [hpos l hl]
      exact absurd hCN_eq (ne_of_lt hexcess)
    -- Hence `L ⊆ {1}`; combined with `0 < C` we get `L = {1}`.
    have hLsub : L ⊆ {1} := by
      intro l hl; simp [hall1 l hl]
    have hLeq : L = {1} := by
      refine Finset.Subset.antisymm hLsub ?_
      rw [Finset.singleton_subset_iff]
      by_contra h1
      -- If `1 ∉ L` then `L ⊆ {1}` forces `L = ∅`, contradicting `0 < C`.
      have hLempty : L = ∅ := by
        rw [Finset.subset_singleton_iff] at hLsub
        rcases hLsub with h | h
        · exact h
        · exact absurd (h ▸ Finset.mem_singleton_self 1) h1
      rw [hC_def, hLempty] at hC_pos; simp at hC_pos
    -- With `L = {1}`, LHS = cf 1 · log (C/cf 1) = C · log 1 = 0 ≤ RHS.
    rw [hLeq]
    rw [Finset.sum_singleton]
    have hcf1 : cf 1 = C := by rw [hC_def, hLeq, Finset.sum_singleton]
    rw [hcf1, div_self hC_ne, Real.log_one, mul_zero]
    -- RHS `= C · log (N/C) + C ≥ 0`.
    have : 0 ≤ C * Real.log (N / C) + C := by
      have hNC1 : N / C = 1 := by rw [← hCN_eq, div_self hC_ne]
      rw [hNC1, Real.log_one, mul_zero, zero_add]
      exact hC_pos.le
    -- align with the set-folded RHS (still over `{1}` after `rw [hLeq]`).
    simpa [hLeq, Finset.sum_singleton, hcf1] using this
  · -- Main case `C < N`: geometric reference at mean `N/C`.
    have hN_pos : 0 < N := lt_trans hC_pos hCN_lt
    have hN_ne : N ≠ 0 := hN_pos.ne'
    set θ : ℝ := 1 - C / N with hθ_def
    have hCN_div : C / N < 1 := (div_lt_one hN_pos).mpr hCN_lt
    have hθ0 : 0 < θ := by rw [hθ_def]; linarith
    have hθ1 : θ < 1 := by
      rw [hθ_def]; have : 0 < C / N := div_pos hC_pos hN_pos; linarith
    have hθ_ne : θ ≠ 0 := hθ0.ne'
    have h1subθ : 1 - θ = C / N := by rw [hθ_def]; ring
    -- Apply the log-sum inequality with `a = cf`, `b l = θ^(l-1)`.
    have hb_pos : ∀ l ∈ L, 0 < θ ^ (l - 1) := fun l _ => by positivity
    have hlogsum := logSumInequality L cf (fun l => θ ^ (l - 1))
      (fun l hl => (hpos l hl).le) hb_pos
    -- `∑ a = C`.
    rw [← hC_def] at hlogsum
    -- Rewrite the RHS of `hlogsum`:
    -- `∑ cf l · log (cf l / θ^(l-1)) = ∑ cf l log cf l − (N − C) · log θ`.
    have hrhs : (∑ l ∈ L, cf l * Real.log (cf l / θ ^ (l - 1)))
        = (∑ l ∈ L, cf l * Real.log (cf l)) - (N - C) * Real.log θ := by
      have hstep : ∀ l ∈ L, cf l * Real.log (cf l / θ ^ (l - 1))
          = cf l * Real.log (cf l) - ((l : ℝ) - 1) * cf l * Real.log θ := by
        intro l hl
        have hcfl : cf l ≠ 0 := (hpos l hl).ne'
        have hpow : (θ ^ (l - 1)) ≠ 0 := (hb_pos l hl).ne'
        rw [Real.log_div hcfl hpow, Real.log_pow]
        have hl1' : 1 ≤ l := hl1 l hl
        have hcast : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
          rw [Nat.cast_sub hl1']; norm_num
        rw [hcast]; ring
      rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib]
      congr 1
      -- `∑ (l − 1) · cf l · log θ = (N − C) · log θ`.
      rw [← Finset.sum_mul]
      congr 1
      rw [hN_def, hC_def, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun l hl => ?_)
      ring
    rw [hrhs] at hlogsum
    -- LHS of `hlogsum`: `C · log (C / ∑θ^(l-1))`.
    -- `L` is nonempty since `C = ∑ cf > 0`.
    have hL_ne : L.Nonempty := by
      rcases L.eq_empty_or_nonempty with h | h
      · rw [hC_def, h] at hC_pos; simp at hC_pos
      · exact h
    set S : ℝ := ∑ l ∈ L, θ ^ (l - 1) with hS_def
    have hS_pos : 0 < S := Finset.sum_pos hb_pos hL_ne
    have hS_ne : S ≠ 0 := hS_pos.ne'
    -- `hlogsum : C · log (C / S) ≤ ∑ cf l log cf l − (N − C) · log θ`.
    -- Move to the target LHS via `hLHS` and `log (C/S) = log C − log S`.
    rw [Real.log_div hC_ne hS_ne] at hlogsum
    -- `C·(log C − log S) ≤ ∑ cf log cf − (N−C)·log θ`
    -- ⟹ target_LHS = C·log C − ∑ cf log cf ≤ C·log S − (N−C)·log θ.
    have hchain : (∑ l ∈ L, cf l * Real.log (C / cf l))
        ≤ C * Real.log S - (N - C) * Real.log θ := by
      rw [hLHS]; nlinarith [hlogsum]
    -- Bound `C · log S ≤ C · log (N/C)`.
    have hgeom := sum_geom_shift_le_inv L θ hθ0 hθ1 hl1
    rw [← hS_def] at hgeom
    have hSlog : C * Real.log S ≤ C * Real.log (N / C) := by
      have hmono : Real.log S ≤ Real.log ((1 - θ)⁻¹) :=
        Real.log_le_log hS_pos hgeom
      have hinv : Real.log ((1 - θ)⁻¹) = Real.log (N / C) := by
        rw [Real.log_inv, h1subθ]
        rw [Real.log_div hC_ne hN_ne, Real.log_div hN_ne hC_ne]
        ring
      rw [hinv] at hmono
      exact mul_le_mul_of_nonneg_left hmono hC_pos.le
    -- Bound `−(N−C)·log θ ≤ C` via `−log θ ≤ 1/θ − 1 = C/(N−C)`.
    have hNCpos : 0 < N - C := by linarith
    have hlogθ : -Real.log θ ≤ C / (N - C) := by
      have hle : Real.log (1 / θ) ≤ 1 / θ - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div one_ne_zero hθ_ne, Real.log_one, zero_sub] at hle
      -- `1/θ − 1 = (1−θ)/θ = (C/N)/((N−C)/N) = C/(N−C)`.
      have hθval : θ = (N - C) / N := by rw [hθ_def]; field_simp
      have hval : (1 : ℝ) / θ - 1 = C / (N - C) := by
        rw [hθval, eq_div_iff hNCpos.ne']
        field_simp
        ring
      rw [hval] at hle
      exact hle
    have hθbound : -(N - C) * Real.log θ ≤ C := by
      have := mul_le_mul_of_nonneg_left hlogθ hNCpos.le
      rw [mul_div_cancel₀ _ hNCpos.ne'] at this
      nlinarith [this]
    -- Combine.
    calc (∑ l ∈ L, cf l * Real.log (C / cf l))
        ≤ C * Real.log S - (N - C) * Real.log θ := hchain
      _ ≤ C * Real.log (N / C) + C := by nlinarith [hSlog, hθbound]

end InformationTheory.Shannon
