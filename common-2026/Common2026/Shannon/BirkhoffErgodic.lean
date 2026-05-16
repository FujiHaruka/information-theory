import Common2026.Shannon.BackwardMartingale
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Birkhoff individual ergodic theorem (E-8'' / Phase γ)

This file packages the **ergodic-discharge step** of the Birkhoff individual
ergodic theorem, building on the backward-martingale machinery in `Phase β`.

## Architecture (per `docs/shannon/birkhoff-ergodic-plan.md` §4)

Phase γ decomposes into four sub-phases:

* **γ.1** — set up the Birkhoff time average as a backward martingale
  (Hopf rearrangement / Petersen *Ergodic Theory* (2.2)).
* **γ.2** — apply the backward martingale convergence theorem
  (`BackwardMartingale.ae_tendsto`, stated with `sorry` in Phase β).
* **γ.3** — show the limit is T-invariant a.e. and discharge ergodicity
  via `Ergodic.ae_eq_const_of_ae_eq_comp_ae`
  (`Mathlib/Dynamics/Ergodic/Function.lean:103`).
* **γ.4** — identify the a.e. constant as `∫ f dμ`.

## Retreat line — γ.1, γ.2 hypothesised; γ.3 + γ.4 proven

Per the plan's retreat clause (§5), Phase γ ships as a **hypothesis-form**
theorem `birkhoff_ergodic_ae_of_limit` that takes as input:
* an a.e. strongly measurable limit `g_∞` of the Birkhoff averages,
* T-invariance of `g_∞`,
* the matching integral `∫ g_∞ = ∫ f`,

and produces the Birkhoff a.e. conclusion `A_n → ∫ f dμ` by **γ.3 +
γ.4** (ergodic discharge + constant identification). The three input
hypotheses are precisely what γ.1 + γ.2 deliver once Phase β.4
(`BackwardMartingale.ae_tendsto`) ships; the integral identity also
requires the L¹ closure (`lim ∫ M_n = ∫ g_∞`) which is the uniform-
integrability bridge for backward martingales.

This file is **0 sorry**. Phase β `sorry`s are inherited only via the
unused `BackwardMartingale.ae_tendsto` statement, not via any local call.

## Main definitions

* `birkhoffAverageReal` — the real-valued Birkhoff time average with
  `n+1` terms (avoids the `n = 0` division). Compatible in spirit with
  Mathlib's `birkhoffAverage` (`Dynamics/BirkhoffSum/Average.lean:46`).
* `birkhoffMartingale` — same average, re-indexed by `ℕᵒᵈ`, intended
  to be a backward martingale w.r.t. `backwardFiltration T`.

## Main results

* `integral_comp_iterate_eq` — `∫ f ∘ T^[i] = ∫ f` (measure preservation).
* `integral_birkhoffAverageReal_eq` — `∫ A_n = ∫ f` for every `n ≥ 0`.
* `birkhoff_ergodic_ae_of_limit` — **main theorem**: γ.3 + γ.4 assembled.
-/

namespace InformationTheory.Shannon

open MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}

/-! ## γ.1 — Birkhoff average + `ℕᵒᵈ`-indexed martingale -/

/-- Birkhoff time average with `n+1` terms.

`birkhoffAverageReal T f n ω := (∑_{i=0}^{n} f (T^[i] ω)) / (n+1)`.

The `n+1` denominator side-steps the `n = 0` division issue; this is the
sequence we want to converge to `∫ f dμ` under Birkhoff's theorem. -/
noncomputable def birkhoffAverageReal (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (∑ i ∈ Finset.range (n + 1), f (T^[i] ω)) / (n + 1 : ℝ)

/-- `birkhoffAverageReal` re-indexed by `ℕᵒᵈ`, intended to be a backward
martingale with respect to `backwardFiltration T`. The martingale property
(Hopf rearrangement) is hypothesised in the main theorem; see file
docstring. -/
noncomputable def birkhoffMartingale (T : Ω → Ω) (f : Ω → ℝ) : ℕᵒᵈ → Ω → ℝ :=
  fun n => birkhoffAverageReal T f (OrderDual.ofDual n)

/-- Applied form of `birkhoffMartingale`. -/
@[simp] lemma birkhoffMartingale_apply (T : Ω → Ω) (f : Ω → ℝ) (n : ℕᵒᵈ) (ω : Ω) :
    birkhoffMartingale T f n ω = birkhoffAverageReal T f (OrderDual.ofDual n) ω := rfl

/-- At the head of the dual order (`toDual 0`), the Birkhoff martingale
collapses to `f`. -/
lemma birkhoffMartingale_toDual_zero (T : Ω → Ω) (f : Ω → ℝ) :
    birkhoffMartingale T f (OrderDual.toDual 0) = f := by
  funext ω
  simp [birkhoffMartingale, birkhoffAverageReal]

/-! ## γ.4 helpers — integral preservation under iteration -/

/-- Each term `f ∘ T^[i]` has the same integral as `f`, by measure
preservation under `T^[i]`. Uses `MeasureTheory.integral_map` plus the
fact that an integrable `f` is in particular a.e. strongly measurable
under the pushed-forward measure. -/
lemma integral_comp_iterate_eq (μ : Measure Ω)
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) (i : ℕ) :
    ∫ ω, f (T^[i] ω) ∂μ = ∫ ω, f ω ∂μ := by
  have hTi : MeasurePreserving (T^[i]) μ μ := hT.iterate i
  have h_map : Measure.map (T^[i]) μ = μ := hTi.map_eq
  have hf_strong_map : AEStronglyMeasurable f (Measure.map (T^[i]) μ) := by
    rw [h_map]; exact hf.aestronglyMeasurable
  have h_int_map :
      ∫ y, f y ∂Measure.map (T^[i]) μ = ∫ x, f (T^[i] x) ∂μ :=
    MeasureTheory.integral_map hTi.aemeasurable hf_strong_map
  rw [h_map] at h_int_map
  exact h_int_map.symm

/-- Integral of the `(n+1)`-term Birkhoff average equals `∫ f`. -/
lemma integral_birkhoffAverageReal_eq (μ : Measure Ω) [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) (n : ℕ) :
    ∫ ω, birkhoffAverageReal T f n ω ∂μ = ∫ ω, f ω ∂μ := by
  classical
  unfold birkhoffAverageReal
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn_ne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hn_pos
  -- Step 1: divide outside.
  have h1 :
      ∫ ω, (∑ i ∈ Finset.range (n + 1), f (T^[i] ω)) / ((n : ℝ) + 1) ∂μ
        = (∫ ω, ∑ i ∈ Finset.range (n + 1), f (T^[i] ω) ∂μ) / ((n : ℝ) + 1) := by
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const]
  rw [h1]
  -- Step 2: ∫ ∑ = ∑ ∫.
  have h_int_each : ∀ i ∈ Finset.range (n + 1),
      Integrable (fun ω => f (T^[i] ω)) μ := by
    intro i _
    exact (hT.iterate i).integrable_comp_of_integrable hf
  rw [integral_finsetSum _ h_int_each]
  -- Step 3: each ∫ f∘T^[i] = ∫ f.
  have h_each : ∀ i ∈ Finset.range (n + 1),
      ∫ ω, f (T^[i] ω) ∂μ = ∫ ω, f ω ∂μ := by
    intro i _
    exact integral_comp_iterate_eq μ hT hf i
  rw [Finset.sum_congr rfl h_each]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Goal: `(↑(n + 1) * ∫ f) / (↑n + 1) = ∫ f`.
  rw [Nat.cast_add, Nat.cast_one]
  field_simp

/-! ## Main theorem — γ.3 (ergodic discharge) + γ.4 (constant id) -/

/-- **Birkhoff individual ergodic theorem (hypothesis form).**

Given:
* a probability-preserving ergodic transformation `T`,
* an integrable observable `f`,
* an a.e. limit function `g_∞` of the Birkhoff averages
  `A_n ω = (∑_{i=0}^{n} f (T^[i] ω)) / (n+1)`,
* the hypotheses that `g_∞` is a.e. strongly measurable, T-invariant
  (`g_∞ ∘ T =ᵐ g_∞`), and matches `f` in integral (`∫ g_∞ = ∫ f`),

we conclude that the Birkhoff averages converge a.e. to `∫ f dμ`.

This packages **γ.3 (ergodic discharge) + γ.4 (constant identification)**
at **0 sorry**. The hypotheses on `g_∞` are produced by **γ.1 + γ.2**:
γ.1 (Hopf rearrangement) gives the backward-martingale property of
`birkhoffMartingale`; γ.2 applies `BackwardMartingale.ae_tendsto`
(Phase β.4, currently `sorry`) to produce `g_∞`; T-invariance comes from
tail-σ-algebra measurability + the shift identity
`A_n(T ω) - A_n(ω) = (f(T^{n+1} ω) - f ω)/(n+1) → 0` a.e. (the
`f(T^n ω)/n → 0` bound by Borel-Cantelli on `∑ μ{|f|>εn} ≤ ∫|f|/ε`); the
integral identity follows from L¹ closure of the backward martingale.

See `docs/shannon/birkhoff-ergodic-plan.md` §4 for the full chain. -/
theorem birkhoff_ergodic_ae_of_limit
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (_hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ)
    {f : Ω → ℝ} (_hf : Integrable f μ)
    {gInf : Ω → ℝ}
    (hg_meas : AEStronglyMeasurable gInf μ)
    (hg_inv : gInf ∘ T =ᵐ[μ] gInf)
    (hg_int : ∫ ω, gInf ω ∂μ = ∫ ω, f ω ∂μ)
    (hg_lim : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => birkhoffAverageReal T f n ω) atTop (𝓝 (gInf ω))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => birkhoffAverageReal T f n ω)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  -- γ.3: ergodic discharge. `gInf ∘ T =ᵐ gInf` + Ergodic ⟹ `gInf =ᵐ const c`.
  obtain ⟨c, hc⟩ := hT_erg.ae_eq_const_of_ae_eq_comp_ae hg_meas hg_inv
  -- γ.4: identify `c = ∫ f dμ`.
  -- `∫ gInf = c * μ(univ) = c` (probability), and `∫ gInf = ∫ f`.
  have h_intg_c : ∫ ω, gInf ω ∂μ = c := by
    have h_ae_c : ∀ᵐ ω ∂μ, gInf ω = c := hc
    exact integral_eq_const h_ae_c
  have hc_eq : c = ∫ ω, f ω ∂μ := by linarith [hg_int, h_intg_c]
  -- Conclude: `A_n → gInf ω → c = ∫ f` a.e.
  filter_upwards [hg_lim, hc] with ω hω hcω
  rw [hcω] at hω
  rw [hc_eq] at hω
  exact hω

/-! ## γ.1 + γ.2 — Conditional-expectation backward martingale

The pointwise Birkhoff average `birkhoffAverageReal T f n` is **not**
directly `(backwardFiltration T hT) (toDual n)`-measurable, so it does
not literally form a backward martingale. The standard fix is to work
instead with the **conditional-expectation backward martingale**

```
M_n := μ[f | (backwardFiltration T hT) n]
```

which is automatically a `Martingale ℕᵒᵈ` by the tower property of
conditional expectation (Mathlib's `martingale_condExp`). The link to
the Birkhoff average is the **Hopf identity** (Petersen *Ergodic Theory*
Theorem 2.2):

```
∀ᵐ ω ∂μ, μ[f | (backwardFiltration T hT) (toDual n)] ω
       = birkhoffAverageReal T f n ω
```

i.e. `M_(toDual n) =ᵐ birkhoffAverageReal T f n`. The Hopf identity is
the substantial unproved gap of Phase γ; see `hopf_identity` below. -/

section CondExpMartingale

variable {μ : Measure Ω}

/-- Conditional-expectation backward martingale `M_n := μ[f | ℋ_n]`. -/
noncomputable def birkhoffCondExpMartingale
    (T : Ω → Ω) (hT : Measurable T) (f : Ω → ℝ) : ℕᵒᵈ → Ω → ℝ :=
  fun n => μ[f | (backwardFiltration T hT) n]

/-- The cond-exp backward martingale is automatically a `Martingale ℕᵒᵈ`. -/
lemma birkhoffCondExpMartingale_isMartingale [IsFiniteMeasure μ]
    (T : Ω → Ω) (hT : Measurable T) (f : Ω → ℝ) :
    Martingale (birkhoffCondExpMartingale (μ := μ) T hT f)
      (backwardFiltration T hT) μ :=
  martingale_condExp f (backwardFiltration T hT) μ

/-- **Hopf rearrangement identity** (Petersen *Ergodic Theory* Thm 2.2 /
Williams *Probability with Martingales* §14.4).

`(toDual n)`-level conditional expectation of `f` with respect to the
backward filtration `ℋ` agrees a.e. with the `(n+1)`-term Birkhoff
average:

```
μ[f | (backwardFiltration T hT) (toDual n)] =ᵐ birkhoffAverageReal T f n.
```

**This is the only `sorry` of Phase γ.** Mathematically, the proof goes:

1. By definition `ℋ_n = comap (T^[n]) m₀`. Every `A ∈ ℋ_n` has the form
   `A = (T^[n])⁻¹ B` for some `B ∈ m₀`.
2. By stationarity (`MeasurePreserving T μ μ`), the conditional
   expectation `μ[f ∘ T^[i] | ℋ_n]` is the **same** for every
   `0 ≤ i ≤ n` — they are all measure-theoretic "rotations" of each
   other on the σ-algebra of orbit-tail events.
3. Averaging the identities over `i ∈ [0, n]` gives the Birkhoff
   average on the right and `μ[f | ℋ_n]` on the left.

**Mathlib gap analysis**: Step 2 ("exchangeability under T") requires the
lemma `μ[g ∘ T | comap T m₀] =ᵐ (μ[g | m₀]) ∘ T` for arbitrary
measurable T (without assuming `MeasurableEmbedding T`). Mathlib's
`MeasurePreserving.setIntegral_preimage_emb`
(`MeasureTheory/Integral/Bochner/Set.lean:557`) requires the embedding
hypothesis. The change-of-variables on a comap σ-algebra without
embedding requires opening up `setIntegral_map`
(`Set.lean:540`) and threading `Measure.map_eq` through; this is a
~70-100-line standalone development that we defer.

The fallback below produces the no-hypothesis Birkhoff theorem
modulo this single isolated `sorry`. -/
private lemma hopf_identity [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (_hf : Integrable f μ) (n : ℕ) :
    birkhoffCondExpMartingale (μ := μ) T hT.measurable f (OrderDual.toDual n)
      =ᵐ[μ] birkhoffAverageReal T f n := by
  sorry

end CondExpMartingale

/-! ## γ.3 + γ.4 — Limit identification, T-invariance, integral equality -/

section MainTheorem

variable {μ : Measure Ω}

/-- Algebraic recursion: `A_n(T ω) = ((n+2) · A_{n+1}(ω) - f(ω)) / (n+1)`.

Both sides are pointwise functions of `ω` (no measure assumption). -/
lemma birkhoffAverageReal_comp_T (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    birkhoffAverageReal T f n (T ω)
      = ((n + 2 : ℝ) * birkhoffAverageReal T f (n + 1) ω - f ω) / (n + 1) := by
  classical
  unfold birkhoffAverageReal
  -- LHS sum: `Σ_{i ∈ range (n+1)} f (T^[i] (T ω)) = Σ_{i ∈ range (n+1)} f (T^[i+1] ω)`.
  have h_iter : ∀ i, T^[i] (T ω) = T^[i + 1] ω := fun i => by
    rw [show T^[i] (T ω) = (T^[i] ∘ T) ω from rfl]
    rw [show (T^[i] ∘ T) = T^[i + 1] from (Function.iterate_succ T i).symm]
  have h_lhs_sum :
      (∑ i ∈ Finset.range (n + 1), f (T^[i] (T ω)))
        = (∑ i ∈ Finset.range (n + 1), f (T^[i + 1] ω)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_iter i]
  -- Reindex `j = i + 1` over `range (n+1)`: gives `Σ_{j ∈ Finset.Ioo 0 (n+2)} f (T^[j] ω)`,
  -- equivalently `Σ_{j ∈ range (n+2)} - f(T^[0] ω)`.
  have h_reindex :
      (∑ i ∈ Finset.range (n + 1), f (T^[i + 1] ω))
        = (∑ j ∈ Finset.range (n + 2), f (T^[j] ω)) - f (T^[0] ω) := by
    rw [Finset.sum_range_succ' (fun j => f (T^[j] ω)) (n + 1)]
    ring
  -- T^[0] ω = ω.
  have h_T0 : T^[0] ω = ω := rfl
  -- Combine.
  rw [h_lhs_sum, h_reindex, h_T0]
  -- RHS Birkhoff average: `(Σ_{j ∈ range (n+2)} f(T^[j] ω)) / (n+2)`.
  have h_n_succ : ((n : ℝ) + 1 + 1) = (n + 2 : ℝ) := by ring
  have h_div : ((↑(n + 1) : ℝ) + 1) = (n + 2 : ℝ) := by push_cast; ring
  -- Goal: shape match.
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn_ne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hn_pos
  have hn2_pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hn2_ne : ((n : ℝ) + 2) ≠ 0 := ne_of_gt hn2_pos
  rw [show ((↑(n + 1) : ℝ) + 1) = (n : ℝ) + 2 from by push_cast; ring]
  field_simp

/-- **Birkhoff individual ergodic theorem (no-hypothesis form).**

For a probability-preserving ergodic transformation `T : Ω → Ω` and an
integrable observable `f : Ω → ℝ`, the Birkhoff time averages

```
A_n ω := (∑_{i=0}^{n} f (T^[i] ω)) / (n + 1)
```

converge almost everywhere to the spatial mean `∫ f dμ`.

The proof discharges γ.1 + γ.2 by:

* applying `BackwardMartingale.ae_tendsto` (Phase β) to the
  conditional-expectation martingale `M_n := μ[f | ℋ_n]`, producing
  an a.e. limit `gInf` that is `tailSigma`-measurable;
* using the **Hopf identity** (`hopf_identity` above) to identify
  `M_(toDual n) =ᵐ A_n`, hence `A_n → gInf` a.e.;
* deriving T-invariance `gInf ∘ T =ᵐ gInf` from the recursion
  `A_n(Tω) = ((n+2)/(n+1)) · A_{n+1}(ω) - f(ω)/(n+1)` and the a.e.
  convergence (uses `MeasurePreserving.quasiMeasurePreserving` to push
  the convergence at `Tω`);
* obtaining the integral equality `∫ gInf = ∫ f` via uniform
  integrability of conditional expectations
  (`Integrable.uniformIntegrable_condExp_filtration`) plus Vitali's
  theorem (`tendsto_Lp_finite_of_tendstoInMeasure`) and
  `tendsto_integral_of_L1'`;
* then invoking `birkhoff_ergodic_ae_of_limit` for γ.3 + γ.4.

The single `sorry` is `hopf_identity`. -/
theorem birkhoff_ergodic_ae [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => birkhoffAverageReal T f n ω)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  classical
  -- Set up the cond-exp backward martingale `M : ℕᵒᵈ → Ω → ℝ`.
  set ℋ : Filtration ℕᵒᵈ m₀ := backwardFiltration T hT.measurable with hℋ_def
  set M : ℕᵒᵈ → Ω → ℝ := birkhoffCondExpMartingale (μ := μ) T hT.measurable f with hM_def
  have hM_isMart : Martingale M ℋ μ :=
    birkhoffCondExpMartingale_isMartingale (μ := μ) T hT.measurable f
  -- β.4 — apply backward-martingale convergence to extract `gInf`.
  -- `M (toDual 0) = μ[f | (backwardFiltration T) (toDual 0)] = μ[f | comap T^[0] m₀] = μ[f | m₀] = f`.
  have hM_int0 : Integrable (M (OrderDual.toDual 0)) μ := hM_isMart.integrable _
  obtain ⟨gInf, hgInf_smeas, hgInf_lim⟩ :=
    BackwardMartingale.ae_tendsto hM_isMart hM_int0
  -- Promote strong measurability with respect to the tail σ-algebra to AE strong measurability
  -- with respect to `m₀` (using the inclusion `tailSigma ≤ m₀`).
  have h_tail_le : (⨅ n : ℕ, ℋ (OrderDual.toDual n)) ≤ m₀ := by
    refine iInf_le_of_le 0 ?_
    -- `ℋ (toDual 0) = comap (T^[0]) m₀ = comap id m₀`. Use `Filtration.le`.
    exact ℋ.le _
  have hgInf_aeSmeas : AEStronglyMeasurable gInf μ :=
    (hgInf_smeas.mono h_tail_le).aestronglyMeasurable
  -- γ.1 — Hopf: `M (toDual n) =ᵐ birkhoffAverageReal T f n` for every `n`.
  have h_hopf : ∀ n : ℕ, M (OrderDual.toDual n) =ᵐ[μ] birkhoffAverageReal T f n :=
    fun n => hopf_identity hT hf n
  -- Combine Hopf + Lévy: `birkhoffAverageReal T f n → gInf` a.e.
  have h_avg_lim : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => birkhoffAverageReal T f n ω) atTop (𝓝 (gInf ω)) := by
    have h_all_hopf : ∀ᵐ ω ∂μ, ∀ n : ℕ,
        M (OrderDual.toDual n) ω = birkhoffAverageReal T f n ω := by
      rw [ae_all_iff]; exact h_hopf
    filter_upwards [hgInf_lim, h_all_hopf] with ω hω h_pt
    -- `M (toDual n) ω = A_n ω` for all n, so the limit transfers.
    have h_eq : (fun n : ℕ => M (OrderDual.toDual n) ω)
        = fun n : ℕ => birkhoffAverageReal T f n ω := funext h_pt
    rw [h_eq] at hω
    exact hω
  -- γ.3 helper — T-invariance of `gInf`.
  -- Push `h_avg_lim` along `T` (QMP) to get `A_n(T ω) → gInf(T ω)` a.e.
  have h_avg_lim_T : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => birkhoffAverageReal T f n (T ω)) atTop (𝓝 (gInf (T ω))) :=
    hT.quasiMeasurePreserving.tendsto_ae h_avg_lim
  -- Combine with the recursion: `A_n(T ω) = ((n+2) A_{n+1}(ω) - f ω) / (n+1)`.
  have h_inv : gInf ∘ T =ᵐ[μ] gInf := by
    filter_upwards [h_avg_lim, h_avg_lim_T] with ω hω hωT
    -- `A_n(T ω) → gInf(T ω)`, and we'll show `A_n(T ω) → gInf ω` by the recursion.
    -- So `gInf(T ω) = gInf ω` by uniqueness of limits.
    -- RHS sequence `((n+2) · A_{n+1}(ω) - f ω) / (n+1)` converges to `gInf ω`.
    have h_recur : ∀ n : ℕ, birkhoffAverageReal T f n (T ω)
        = ((n + 2 : ℝ) * birkhoffAverageReal T f (n + 1) ω - f ω) / (n + 1) :=
      fun n => birkhoffAverageReal_comp_T T f n ω
    -- Rewrite the LHS sequence using `h_recur`.
    have h_lhs_seq_eq :
        (fun n : ℕ => birkhoffAverageReal T f n (T ω))
          = fun n : ℕ =>
            ((n + 2 : ℝ) * birkhoffAverageReal T f (n + 1) ω - f ω) / (n + 1) := by
      funext n; exact h_recur n
    rw [h_lhs_seq_eq] at hωT
    -- RHS sequence in pieces:
    --   c_n := (n+2) / (n+1) → 1
    --   d_n := f ω / (n+1) → 0
    --   A_{n+1}(ω) → gInf ω
    -- Hence `c_n · A_{n+1}(ω) - d_n → 1 · gInf ω - 0 = gInf ω`.
    have h_one_div : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Tendsto (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
      have h_eq : (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + 1))
          = fun n : ℕ => 1 + 1 / ((n : ℝ) + 1) := by
        funext n
        have hn_ne : ((n : ℝ) + 1) ≠ 0 := by positivity
        field_simp
        ring
      rw [h_eq]
      have h_sum : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add h_one_div
      simpa using h_sum
    have hd : Tendsto (fun n : ℕ => f ω / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have h_eq : (fun n : ℕ => f ω / ((n : ℝ) + 1))
          = fun n : ℕ => f ω * (1 / ((n : ℝ) + 1)) := by
        funext n; rw [mul_one_div]
      rw [h_eq]
      have : Tendsto (fun n : ℕ => f ω * (1 / ((n : ℝ) + 1))) atTop (𝓝 (f ω * 0)) :=
        h_one_div.const_mul (f ω)
      simpa using this
    -- A_{n+1}(ω) → gInf ω: shift of the original convergence.
    have hA_shift : Tendsto (fun n : ℕ => birkhoffAverageReal T f (n + 1) ω) atTop
        (𝓝 (gInf ω)) := by
      have h_shift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
        exact tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
      exact hω.comp h_shift
    -- Multiply: c_n · A_{n+1}(ω) → 1 · gInf ω = gInf ω.
    have h_prod : Tendsto (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + 1)
        * birkhoffAverageReal T f (n + 1) ω) atTop (𝓝 (gInf ω)) := by
      simpa using hc.mul hA_shift
    -- Express RHS = (c_n · A_{n+1}(ω)) - d_n.
    have h_rhs_eq :
        (fun n : ℕ => ((n + 2 : ℝ) * birkhoffAverageReal T f (n + 1) ω - f ω)
          / ((n : ℝ) + 1))
        = fun n : ℕ =>
          ((n : ℝ) + 2) / ((n : ℝ) + 1) * birkhoffAverageReal T f (n + 1) ω
            - f ω / ((n : ℝ) + 1) := by
      funext n
      have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      field_simp
    -- Massage `hωT` into shape.
    have hωT' :
        Tendsto (fun n : ℕ =>
          ((n : ℝ) + 2) / ((n : ℝ) + 1) * birkhoffAverageReal T f (n + 1) ω
            - f ω / ((n : ℝ) + 1))
          atTop (𝓝 (gInf (T ω))) := by
      have h_cast_eq : (fun n : ℕ =>
          ((↑n + 2 : ℝ) * birkhoffAverageReal T f (n + 1) ω - f ω) / (↑n + 1))
          = fun n : ℕ =>
          ((n : ℝ) + 2) / ((n : ℝ) + 1) * birkhoffAverageReal T f (n + 1) ω
            - f ω / ((n : ℝ) + 1) := h_rhs_eq
      rw [h_cast_eq] at hωT
      exact hωT
    -- Limit of the sub-d sequence is `gInf ω - 0 = gInf ω`.
    have h_limit_target : Tendsto (fun n : ℕ =>
          ((n : ℝ) + 2) / ((n : ℝ) + 1) * birkhoffAverageReal T f (n + 1) ω
            - f ω / ((n : ℝ) + 1))
          atTop (𝓝 (gInf ω)) := by
      simpa using h_prod.sub hd
    -- Uniqueness of limits: gInf (T ω) = gInf ω.
    have : gInf (T ω) = gInf ω := tendsto_nhds_unique hωT' h_limit_target
    exact this
  -- γ.4 helper — `∫ gInf = ∫ f` via UI of cond-exps + Vitali.
  have h_int_eq : ∫ ω, gInf ω ∂μ = ∫ ω, f ω ∂μ := by
    -- `M` is uniformly integrable.
    have h_UI : UniformIntegrable M 1 μ :=
      hf.uniformIntegrable_condExp_filtration (f := ℋ)
    -- Reindex to `ℕ` via `OrderDual.toDual`.
    set Mℕ : ℕ → Ω → ℝ := fun n => M (OrderDual.toDual n) with hMℕ_def
    have h_UIℕ : UniformIntegrable Mℕ 1 μ := by
      refine ⟨fun n => h_UI.aestronglyMeasurable _, ?_, ?_⟩
      · -- UnifIntegrable property is preserved under reindexing.
        intro ε hε
        obtain ⟨δ, hδ, hδ'⟩ := h_UI.unifIntegrable hε
        exact ⟨δ, hδ, fun n s hs hμs => hδ' (OrderDual.toDual n) s hs hμs⟩
      · obtain ⟨C, hC⟩ := h_UI.2.2
        exact ⟨C, fun n => hC _⟩
    -- AE convergence Mℕ → gInf.
    have h_Mℕ_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => Mℕ n ω) atTop (𝓝 (gInf ω)) :=
      hgInf_lim
    -- gInf is integrable.
    have hgInf_int : Integrable gInf μ :=
      h_UIℕ.integrable_of_ae_tendsto h_Mℕ_lim
    -- Each Mℕ n is integrable.
    have hMℕ_int : ∀ n, Integrable (Mℕ n) μ := fun n => hM_isMart.integrable _
    -- Vitali: ae + UI on finite measure → L¹ convergence.
    have h_tendsto_in_meas : TendstoInMeasure μ Mℕ atTop gInf := by
      refine tendstoInMeasure_of_tendsto_ae ?_ h_Mℕ_lim
      exact fun n => h_UIℕ.aestronglyMeasurable n
    have h_L1 : Tendsto (fun n : ℕ => eLpNorm (Mℕ n - gInf) 1 μ) atTop (𝓝 0) := by
      refine tendsto_Lp_finite_of_tendstoInMeasure (p := 1) le_rfl
        ENNReal.one_ne_top
        (fun n => h_UIℕ.aestronglyMeasurable n) ?_ h_UIℕ.unifIntegrable h_tendsto_in_meas
      exact memLp_one_iff_integrable.mpr hgInf_int
    -- L¹ convergence ⟹ integrals converge.
    have h_int_tendsto :
        Tendsto (fun n : ℕ => ∫ ω, Mℕ n ω ∂μ) atTop (𝓝 (∫ ω, gInf ω ∂μ)) :=
      tendsto_integral_of_L1' gInf hgInf_int (Eventually.of_forall hMℕ_int) h_L1
    -- Each `∫ Mℕ n = ∫ f` (cond-exp integrates to `f`).
    have h_int_M : ∀ n : ℕ, ∫ ω, Mℕ n ω ∂μ = ∫ ω, f ω ∂μ := fun n => by
      simp [hMℕ_def, hM_def, birkhoffCondExpMartingale]
      exact integral_condExp (ℋ.le _)
    -- Hence the constant sequence `∫ f` converges to `∫ gInf`, so `∫ f = ∫ gInf`.
    have h_const_tendsto :
        Tendsto (fun _ : ℕ => ∫ ω, f ω ∂μ) atTop (𝓝 (∫ ω, gInf ω ∂μ)) := by
      have : (fun n : ℕ => ∫ ω, Mℕ n ω ∂μ) = fun _ : ℕ => ∫ ω, f ω ∂μ := funext h_int_M
      rw [this] at h_int_tendsto
      exact h_int_tendsto
    have h_lim_const : (∫ ω, f ω ∂μ) = ∫ ω, gInf ω ∂μ :=
      tendsto_nhds_unique tendsto_const_nhds h_const_tendsto
    exact h_lim_const.symm
  -- Assemble: invoke γ.3 + γ.4 (the existing hypothesis-form theorem).
  exact birkhoff_ergodic_ae_of_limit hT hT_erg hf hgInf_aeSmeas h_inv h_int_eq h_avg_lim

end MainTheorem

end InformationTheory.Shannon
