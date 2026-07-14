import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import InformationTheory.Shannon.ShannonHartleyOperational
import InformationTheory.Shannon.NormalizedSinc
import InformationTheory.Shannon.WhittakerShannon
import InformationTheory.Shannon.AWGN.Achievability
import InformationTheory.Shannon.AWGN.Converse
import InformationTheory.Meta.EntryPoint

/-!
# Continuous-time Shannon-Hartley: achievability (Cover-Thomas Ch. 9.6, Phase 3)

The `≥` half of the operational Shannon-Hartley sandwich,

    `bandlimitedAwgnCapacity W N₀ P ≤ contAwgnOperationalCapacity W N₀ P`

(`contAwgn_ge_shannonHartley`). This direction is *wall-independent*: a discrete
per-sample AWGN codebook (`awgn_achievability`) is lifted to a continuous band-limited
signal by **sinc synthesis** at the true sampler spacing `Δ = T/n` (with `n = ⌊2WT⌋`).

## The synthesis bridge

`synthSignal T n a` reconstructs a band-limited signal interpolating the sample values
`a : Fin n → ℝ` at the grid `t_i = i·(T/n)`. Its three properties power the reduction:

* **(ii) interpolation exactness** — `synthSignal T n a (j·(T/n)) = a j`
  (`synthSignal_sample`), whence `sampledSignal (synthSignal …) = c` after the
  `√(T/n)·√(n/T)` cancellation.
* **(i) band-limitedness** — `IsBandlimited (synthSignal T n a) W` when `n ≤ 2WT`
  (`synthSignal_bandlimited`): each shifted `sincN(·/Δ)` has spectrum supported in
  `[-1/(2Δ), 1/(2Δ)] = [-n/(2T), n/(2T)] ⊆ [-W, W]`.
* **(iii) Parseval energy** — `∫ t, (synthSignal T n a t)² = (T/n)·∑ᵢ (a i)²`
  (`synthSignal_energy`), so with `a = √(n/T)·c` the whole-line energy is `∑ᵢ cᵢ² ≤ T·P`
  and the in-window energy is `≤` that.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Theorem 9.6.1 (achievability).
-/

namespace InformationTheory.Shannon.ShannonHartley

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology FourierTransform
open InformationTheory.Shannon.NormalizedSinc

/-! ## §A — Sinc synthesis -/

/-- Sinc synthesis at grid spacing `Δ = T/n`: the band-limited signal interpolating the
sample values `a : Fin n → ℝ` at the nodes `t_i = i·(T/n)`. This is the *synthesis*
direction (build a band-limited function from finitely many samples), dual to the
*analysis* direction of `whittaker_shannon_bandlimited`. -/
noncomputable def synthSignal (T : ℝ) (n : ℕ) (a : Fin n → ℝ) : ℝ → ℝ :=
  fun t => ∑ i : Fin n,
    a i * sincN ((t - ((i : ℕ) : ℝ) * (T / (n : ℝ))) / (T / (n : ℝ)))

/-- `sincN` of a difference of natural-number casts is the Kronecker delta. -/
theorem sincN_natCast_sub (p q : ℕ) :
    sincN ((p : ℝ) - (q : ℝ)) = if p = q then (1 : ℝ) else 0 := by
  rw [show ((p : ℝ) - (q : ℝ)) = ((((p : ℤ) - (q : ℤ)) : ℤ) : ℝ) by push_cast; ring,
    sincN_int_eq_kronecker]
  simp [sub_eq_zero]

/-! ## §B — (ii) interpolation exactness -/

/-- **(ii)** At a sample node `t = j·(T/n)`, the synthesis recovers the sample value exactly:
all sinc cross-terms vanish (`sincN` at nonzero integers is `0`). -/
theorem synthSignal_sample (T : ℝ) (n : ℕ) (a : Fin n → ℝ) (hT : 0 < T) (hn : 0 < n)
    (j : Fin n) :
    synthSignal T n a (((j : ℕ) : ℝ) * (T / (n : ℝ))) = a j := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hΔ : (T / (n : ℝ)) ≠ 0 := by positivity
  unfold synthSignal
  -- rewrite each summand to `if i = j then a i else 0`
  have hterm : ∀ i : Fin n,
      a i * sincN ((((j : ℕ) : ℝ) * (T / (n : ℝ)) - ((i : ℕ) : ℝ) * (T / (n : ℝ)))
          / (T / (n : ℝ)))
        = if i = j then a i else 0 := by
    intro i
    have harg : (((j : ℕ) : ℝ) * (T / (n : ℝ)) - ((i : ℕ) : ℝ) * (T / (n : ℝ)))
        / (T / (n : ℝ)) = ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by
      rw [sub_div, mul_div_assoc, mul_div_assoc, div_self hΔ, mul_one, mul_one]
    rw [harg, sincN_natCast_sub]
    by_cases h : i = j
    · rw [h]; simp
    · have hji : ¬ ((j : ℕ) = (i : ℕ)) := by
        intro hc; exact h (Fin.ext hc.symm)
      rw [if_neg hji, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq' Finset.univ j a]
  simp

/-- The `√(T/n)`-normalized samples of the synthesized signal recover `√(T/n)·a`. -/
theorem sampledSignal_synthSignal (T : ℝ) (n : ℕ) (a : Fin n → ℝ)
    (hT : 0 < T) (hn : 0 < n) :
    sampledSignal (synthSignal T n a) T n = fun j => Real.sqrt (T / (n : ℝ)) * a j := by
  funext j
  rw [sampledSignal, synthSignal_sample T n a hT hn j]

/-- Choosing `a = √(n/T)·c` makes the synthesized signal's normalized samples equal to the
discrete codeword `c` exactly (the `√(T/n)·√(n/T) = 1` cancellation). -/
theorem sampledSignal_synthSignal_sqrt (T : ℝ) (n : ℕ) (c : Fin n → ℝ)
    (hT : 0 < T) (hn : 0 < n) :
    sampledSignal (synthSignal T n (fun i => Real.sqrt ((n : ℝ) / T) * c i)) T n = c := by
  rw [sampledSignal_synthSignal T n _ hT hn]
  funext j
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : Real.sqrt (T / (n : ℝ)) * Real.sqrt ((n : ℝ) / T) = 1 := by
    rw [← Real.sqrt_mul (by positivity),
      show (T / (n : ℝ)) * ((n : ℝ) / T) = 1 by field_simp]
    exact Real.sqrt_one
  rw [← mul_assoc, h1, one_mul]

/-! ## §C — (i) band-limitedness -/

/-- **(i)** The synthesis is band-limited to `[-W, W]` provided the sample count satisfies the
Nyquist bound `n ≤ 2WT`: each shifted `sincN(·/Δ)` (spacing `Δ = T/n`) has spectrum supported
in `[-1/(2Δ), 1/(2Δ)] = [-n/(2T), n/(2T)]`, and `n/(2T) ≤ W`. -/
theorem synthSignal_bandlimited (T W : ℝ) (n : ℕ) (a : Fin n → ℝ)
    (hT : 0 < T) (hn : 0 < n) (hnW : (n : ℝ) ≤ 2 * W * T) :
    IsBandlimited (synthSignal T n a) W := by
  -- Missing: the L² Fourier transform of `sincN(·/Δ)` equals a boxcar supported in
  -- `[-1/(2Δ), 1/(2Δ)]`. Mathlib has no FT-of-sinc-equals-boxcar lemma, and `𝓕` in
  -- `IsBandlimited` is the L¹ `Real.fourierIntegral` while `synthSignal ∉ L¹` (a finite
  -- sinc combination decays like `1/t`; `Real.integrable_sinc` needs `[IsFiniteMeasure]`).
  -- A genuine (non-junk) proof needs `Lp.fourierTransformₗᵢ` + the sinc↔boxcar identity.
  sorry -- @residual(plan:shannon-hartley-op-phase3)

/-! ## §D — (iii) Parseval energy -/

/-- The squared synthesis is integrable on the whole line (it lies in `L²`). -/
theorem synthSignal_sq_integrable (T : ℝ) (n : ℕ) (a : Fin n → ℝ)
    (hT : 0 < T) (hn : 0 < n) :
    Integrable (fun t => (synthSignal T n a t) ^ 2) := by
  -- `synthSignal ∈ L²` (its square is integrable), from the L² membership of each shifted
  -- `sincN(·/Δ)`. Needs the sinc L² framework (Mathlib's `Real.integrable_sinc` is finite-
  -- measure only; `∫ sinc² = π` is absent from Mathlib — loogle Found 0).
  sorry -- @residual(plan:shannon-hartley-op-phase3)

/-- **(iii)** Parseval / sinc self-reproducing energy identity: the whole-line energy of the
synthesis equals `Δ · ∑ᵢ (a i)²` with `Δ = T/n`. Follows from the sinc orthogonality
`∫ sincN((t-iΔ)/Δ)·sincN((t-jΔ)/Δ) dt = Δ·δᵢⱼ`. -/
theorem synthSignal_energy (T : ℝ) (n : ℕ) (a : Fin n → ℝ) (hT : 0 < T) (hn : 0 < n) :
    (∫ t, (synthSignal T n a t) ^ 2) = (T / (n : ℝ)) * ∑ i : Fin n, (a i) ^ 2 := by
  -- Missing: sinc L² self-reproducing orthogonality
  -- `∫ sincN((t-iΔ)/Δ)·sincN((t-jΔ)/Δ) dt = Δ·δᵢⱼ`. Absent from Mathlib (needs the
  -- sinc↔boxcar L² Fourier identity + Plancherel `Lp.inner_fourier_eq`); the in-project
  -- `WhittakerShannon` deliberately routed through the circle to avoid exactly this.
  sorry -- @residual(plan:shannon-hartley-op-phase3)

/-- In-window energy is bounded by the whole-line energy (the integrand is `≥ 0`), giving the
`ContAwgnCode.encoder_power` obligation directly. This reduction is genuine; it transitively
carries the residuals of `synthSignal_energy` (iii) and `synthSignal_sq_integrable`. -/
theorem synthSignal_window_energy_le (T : ℝ) (n : ℕ) (a : Fin n → ℝ)
    (hT : 0 < T) (hn : 0 < n) :
    (∫ t in Set.Icc (0 : ℝ) T, (synthSignal T n a t) ^ 2)
      ≤ (T / (n : ℝ)) * ∑ i : Fin n, (a i) ^ 2 := by
  rw [← synthSignal_energy T n a hT hn]
  exact setIntegral_le_integral (synthSignal_sq_integrable T n a hT hn)
    (Filter.Eventually.of_forall (fun t => sq_nonneg _))

/-! ## §E — crude-converse boundedness (deferred to a follow-up dispatch) -/

/-- The message-count set is bounded above: a crude finite upper bound suffices (no tight
`≈2WT` count needed), obtained by applying `awgn_converse` to the sampled codeword. This is
the `BddAbove` obligation required to lower-bound `contAwgnMaxMessages` via `le_csSup`. -/
theorem contAwgnMaxMessages_bddAbove (T W N₀ P ε : ℝ)
    (hT : 0 < T) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) (hε0 : 0 < ε) (hε1 : ε < 1) :
    BddAbove { M : ℕ | ∃ c : ContAwgnCode T W P M, (c.averageError N₀).toReal ≤ ε } := by
  sorry -- @residual(plan:shannon-hartley-op-phase3)

/-! ## §F — assembly (deferred to a follow-up dispatch) -/

/-- **Shannon-Hartley achievability (`≥`)**: the operational capacity is at least the
Shannon-Hartley closed form. Proved by lifting a per-sample `awgn_achievability` codebook
through the synthesis bridge. -/
theorem contAwgn_ge_shannonHartley
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    bandlimitedAwgnCapacity W N₀ P ≤ contAwgnOperationalCapacity W N₀ P := by
  sorry -- @residual(plan:shannon-hartley-op-phase3)

end InformationTheory.Shannon.ShannonHartley
