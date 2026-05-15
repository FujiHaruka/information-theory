import Common2026.Shannon.BackwardMartingale
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.MeasureTheory.Integral.Bochner.Basic

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

end InformationTheory.Shannon
