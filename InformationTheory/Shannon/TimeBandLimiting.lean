import InformationTheory.Shannon.TimeBandLimiting.Operator
import InformationTheory.Shannon.TimeBandLimiting.Enumeration
import InformationTheory.Shannon.TimeBandLimiting.TraceBound
import InformationTheory.Shannon.TimeBandLimiting.SecondMoment
import InformationTheory.Shannon.TimeBandLimiting.Count

/-!
# The time-and-band-limiting operator on `L²(ℝ;ℂ)`

Cover–Thomas Ch. 9.6 (Shannon–Hartley), Phase 2 spectral leg A. This file builds the
self-adjoint positive contraction

    `A = P_W ∘ Q_T ∘ P_W`

on the complex Hilbert space `E = L²(ℝ;ℂ)`, where `Q_T` is the orthogonal projection onto the
time-limited subspace (functions a.e.-supported in `[0,T]`) and `P_W` the projection onto the
band-limited subspace (functions whose L²-Fourier transform is a.e.-supported in `[-W,W]`). Both
projections are `Submodule.starProjection`s onto genuinely closed subspaces, so `A`'s
self-adjointness and positivity are one-line consequences of the projection API.

## Main statements

* `timeLimitSubspace` / `bandLimitSubspace` — the two closed subspaces.
* `timeBandLimitingOp` — the operator `A = P_W ∘ Q_T ∘ P_W`.
* `timeBandLimitingOp_isSelfAdjoint` — `A` is self-adjoint.
* `timeBandLimitingOp_isPositive` — `A` is a positive operator.
* `timeBandLimitingOp_norm_le_one` — `‖A‖ ≤ 1` (contraction).

Leg B adds compactness `timeBandLimitingOp_isCompact`, reducing it — via `A = P_W ∘ C` with
`C = Q_T ∘ P_W` — to compactness of the sinc integral operator `C`, whose Hilbert–Schmidt kernel is
`sincConvKernel t s = 𝟙_[0,T](t) · 2W · sincN(2W(t−s))`.

Leg C adds the decreasing eigenvalue enumeration. Mathlib's ordered `ℕ → ℝ` eigenvalue sequence is
`FiniteDimensional`-gated, so it is rebuilt here from the structural compact self-adjoint spectral
theorem: `prolateEigenvalueSet_finite` (only finitely many eigenvalues exceed any `c > 0`) makes the
counting function `prolateCount` honest, and `prolateEigenvalues` is its generalized inverse.

* `prolateEigenvalueSet_finite` — finitely many eigenvalues above any positive threshold.
* `prolateEigenvalues` — the eigenvalues of `A` in decreasing order, listed with multiplicity.
* `prolateEigenvalues_antitone` / `_nonneg` / `_le_one` — the enumeration decreases within `[0,1]`.
* `prolateEigenvalues_hasEigenvalue` — every nonzero entry is a genuine eigenvalue of `A`.
* `prolateEigenvalues_tendsto_zero` — the enumeration tends to `0`.

Leg C' makes that enumeration non-vacuous. The headlines above are all satisfied by the constant-zero
sequence — and legitimately so, since `A` really does collapse for `W ≤ 0` or `T ≤ 0`. The single
missing input is `timeBandLimitingOp_ne_zero`, proved by exhibiting the box `𝟙_[0,T]` as a witness:
its spectrum is continuous with value `T` at the origin (via the `L¹ ∩ L²` Fourier bridge
`ShannonHartley.l2Fourier_eq_fourierIntegral`), hence survives the band cutoff since `[-W,W]` is a
neighborhood of `0`.

* `timeBandLimitingOp_ne_zero` — `A ≠ 0` for `0 < T`, `0 < W`.
* `prolateEigenvalues_zero_pos` — the leading eigenvalue is strictly positive.

Both of its hypotheses are tight, and the boundary lemmas witnessing that are in-tree rather than
prose: the two subspaces collapse to `⊥` for a nonpositive parameter
(`timeLimitSubspace_eq_bot_of_nonpos` / `bandLimitSubspace_eq_bot_of_nonpos`), hence so does `A`,
hence the enumeration is identically `0` there (`prolateEigenvalues_eq_zero_of_time_nonpos` /
`prolateEigenvalues_eq_zero_of_band_nonpos`). The degeneracy story is told once, at the section
header preceding `zeroOnLp_eq_bot_of_ae_mem`.

Leg E adds the `2WT` degrees-of-freedom bound, in the Bessel form the Hilbert-space structure
supports directly. `P_W` is the integral operator against the reproducing kernel
`k_t = 2W sincN(2W(t − ·))`, so `(P_W f)(t) = ⟪k_t, f⟫` and `⟪A f, f⟫ = ∫_[0,T] |⟪k_t, f⟫|² dt`.
Bessel's inequality applied under that integral, against the constant kernel norm `‖k_t‖² = 2W`,
caps the trace of `A` along any finite orthonormal family; Markov converts this into the counting
bound. Only a *finite* orthonormal family is involved, so no trace-class or Schatten theory (absent
from Mathlib) is needed.

* `bandKernelLp` — the reproducing kernel `k_t`, with `bandKernelLp_norm_sq : ‖k_t‖² = 2W`.
* `bandLimitProj_apply_eq_inner` — the reproducing property `(P_W f)(t) = ⟪k_t, f⟫`.
* `inner_timeBandLimitingOp_self_eq` — `⟪A f, f⟫` is the energy of `P_W f` on the window `[0,T]`.
* `sum_inner_timeBandLimitingOp_le` — `∑ᵢ ⟪A eᵢ, eᵢ⟫ ≤ 2WT` for orthonormal `e`.
* `prolateCount_mul_le` — `c · #{λ > c} ≤ 2WT`.

Both hypotheses of the last two are tight in the same way as above: for `T < 0` or `W < 0` the
operator collapses, so the trace is `0` while the claimed bound `2WT` is strictly negative.

Leg E-trace upgrades that Bessel *inequality* to a Parseval *equality*: along a *complete* basis the
trace is exactly `2WT`. The mechanism needs neither the spectral theorem nor trace-class theory —
the terms are nonnegative, so Tonelli exchanges `∑'` with `∫` unconditionally, and completeness
replaces Bessel by Parseval.

* `orthonormal_countable` — an orthonormal family in a separable space is countable (absent from
  Mathlib; it discharges the Tonelli step's countability rather than assuming it).
* `tsum_inner_timeBandLimitingOp_eq` — `∑'ᵢ ⟪A bᵢ, bᵢ⟫ = 2WT` for any `HilbertBasis`.
* `exists_hilbertBasis_tsum_inner_timeBandLimitingOp_eq` — an in-tree non-vacuity witness.

The sharp Landau–Pollak–Slepian concentration (`⌊2WT⌋ + O(log WT)` eigenvalues near `1`, i.e. the
matching lower bound and the transition width) is still not proved here, and the exact first moment
does not bring it closer: Markov uses only the `≤` half, while a lower bound on the count needs the
*second* moment `∑ λₙ(1 − λₙ) = tr A − tr A²` to control the tail `∑_{λₙ ≤ c} λₙ`. Also still open
is `λ n ≠ 0` for all `n` (which needs `A` to have infinite rank).

Leg R1 adds the spectral gap below `c`: on the orthogonal complement of the span of the eigenspaces
above `c`, the Rayleigh quotient of `A` is at most `c`. Notably this needs no eigenbasis. `Vᗮ` is
`A`-invariant by symmetry, so `A` restricts there to a compact self-adjoint `S` whose eigenvalues
all lie in `[0, c]`; for such an operator the norm *is* the spectral radius, so `‖S‖ ≤ c` and
Cauchy-Schwarz finishes. The complete orthonormal eigenbasis that
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` would supply is therefore *not*
consumed here, and remains open at `tsum_prolateEigenvalues_eq`.

* `prolateEigenspaceSup_orthogonal_invariant` — `Vᗮ` is `A`-invariant.
* `prolateRestrict` — `A` restricted to `Vᗮ`, with `prolateRestrict_norm_le : ‖S‖ ≤ c`.
* `inner_timeBandLimitingOp_le_of_mem_orthogonal` — `⟪A v, v⟫ ≤ c‖v‖²` for `v ∈ Vᗮ`.
* `le_inner_timeBandLimitingOp_of_mem` — the matched lower bound `c‖v‖² ≤ ⟪A v, v⟫` on `V`.
* `finrank_le_prolateCount_of_form_gt` — converse min-max count domination: any `S` with Rayleigh
  quotient `> c` has `finrank S ≤ prolateCount T W c`.

Unlike the trace bounds above, this one is unconditional in `T` and `W`: `A` is compact, symmetric
and positive for every parameter value, and the bound stays true where `A` collapses to `0`.

Leg R2 assembles those into the two-sided eigenvalue count concentration, with `D := 2 + log(1+2WT)`
and the threshold `c` free (not fixed at `1/2` — the converse needs `c → 0`, the achievability
`c → 1`):

* `prolateCount_le` — `#{λ > c} ≤ 2WT + D/c` for `0 < c`.
* `le_prolateCount` — `2WT − D/(1−c) ≤ #{λ > c}` for `0 < c < 1`.

Both run through `exists_hilbertBasis_prolateSplit`, a Hilbert basis adapted to `E = V ⊕ Vᗮ` whose
`V` half is an eigenbasis (finite-dimensional spectral theorem,
`exists_orthonormal_eigenbasis_prolateEigenspaceSup`) and whose `Vᗮ` half is an arbitrary Hilbert
basis. No complete eigenbasis of `A` is ever constructed, and the count needs no multiplicity
bridge: `prolateCount` *is* the `finrank` of `V`, so the `V` half is indexed by
`Fin (prolateCount T W c)` definitionally.

## Module structure

This is the umbrella of the `Shannon/TimeBandLimiting/` family; it re-exports the submodules:

* `TimeBandLimiting.Operator` — the operator `A`, its subspaces, self-adjointness, positivity,
  norm bound, compactness, and boundary degeneracy (Leg A/B).
* `TimeBandLimiting.Enumeration` — the decreasing eigenvalue enumeration and its non-vacuity
  (Leg C/C').
* `TimeBandLimiting.TraceBound` — the reproducing kernel, the Bessel trace bound `≤ 2WT`, and
  spectral gap below `c` (Leg E/R1).
* `TimeBandLimiting.SecondMoment` — the window deficit and the second moment `tr A²` (Leg E).
* `TimeBandLimiting.Count` — the two-sided eigenvalue count and achievability (Leg R2).
-/
