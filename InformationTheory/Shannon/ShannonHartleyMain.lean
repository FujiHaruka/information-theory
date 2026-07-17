import InformationTheory.Shannon.TimeBandLimiting
import InformationTheory.Meta.EntryPoint

/-!
# Continuous-time Shannon-Hartley: headline theorems

This file collects the two headline theorems of the continuous-time band-limited AWGN channel —
the achievability half `contAwgn_ge_shannonHartley` (`≥`) and the identity
`contAwgn_eq_shannonHartley` (`=`) — at a position downstream of the achievability assets they
must consume. Both are blocked on the same `nyquist-2w-dof` operational bridge, which needs the
prolate-eigenvalue count (`le_prolateCount` / `prolateCount_le`) of `TimeBandLimiting.lean`; those
prolate assets are visible only below the achievability and operational modules, so the theorems
live here rather than at their original upstream sites.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Theorem 9.6.1.
-/

namespace InformationTheory.Shannon.ShannonHartley

set_option linter.unusedVariables false

/-- **Shannon-Hartley achievability (`≥`)**: the operational capacity is at least the
Shannon-Hartley closed form.

Unlike the boundedness bound of §E, this direction does not close by Bessel alone: it needs the
`≈ 2WT` degrees-of-freedom count, in its lower-bound half.

The reason is that the receiver of `ContAwgnCode` sees a band-limited codeword only through test
functions supported in `[0, T]`, and those two constraints fight each other: a band-limited `f` is
never supported in `[0, T]`, so `⟨f, φᵢ⟩ = ⟨f, P_W φᵢ⟩` and the energy the receiver recovers is
governed by the Gram matrix `Gᵢⱼ = ⟨φᵢ, (timeBandLimitingOp T W) φⱼ⟩` — a compression of the
prolate operator, whose eigenvalues Cauchy interlacing caps by `prolateEigenvalues T W`. To reach
the closed form one must exhibit, for each `T`, a family achieving per-dimension gain `≈ 1` on
`≈ 2WT` dimensions; that is exactly the Landau-Pollak-Slepian concentration read from below,
which is `le_prolateCount` (`TimeBandLimiting.lean`): `2WT − D/(1 − c) ≤ prolateCount T W c` for
every threshold `c ∈ (0, 1)`, with `D = 2 + log(1 + 2WT)`. That count is proved; what this
statement still lacks is the bridge from it to `contAwgnOperationalCapacity` — the interlacing
step and the capacity computation on top of it.

No cheaper family is available, and this was checked rather than assumed. The obvious wall-free
candidate — the boxcar family `φᵢ = 𝟙_{[iΔ,(i+1)Δ]}/√Δ` at `Δ = 1/(2W)`, which is orthonormal and
`[0, T]`-supported by inspection — fails: a boxcar's spectrum is a sinc, so `‖P_W φᵢ‖ < 1` by a
constant factor, the per-dimension gains are bounded away from `1`, and concavity of `log` puts
the resulting rate strictly below the closed form. Adversarial search over random orthonormal
families corroborates (`docs/shannon/shannon-hartley-facts.md` §OBSERVATION-MAP: best `C/SH`
`= 0.3250` against prolate's `0.9944`, with no family beating prolate). The convergence itself is
the count: the finite-`T` shortfall is `O(log WT)`, the width of the prolate cliff's transition
band, which is the error term `D/(1 − c)` of `le_prolateCount`.

The synthesis bridge of §A–§D (`synthSignal`, `synthSignal_energy`) remains the way to build the
band-limited codewords, and `synthSignal_energy` discharges the whole-line `encoder_power`
obligation as an equality. What it does not supply is the test family.

This statement also consumes `contAwgnMaxMessages_bddAbove` (§E) through `le_csSup` — without a
`BddAbove` the ℕ-`sSup` collapses to junk `0`. That obligation is wall-independent and its
residual is tracked at its own declaration rather than duplicated here.

Hypotheses `hW`/`hN₀`/`hP` are regularity-only (not load-bearing).

The `wall:nyquist-2w-dof` slug is kept as the tracking tag, but its named proposition — the
eigenvalue concentration — is closed (`le_prolateCount` is the half this direction needs). The live
obstruction is the operational bridge above, not the count.

`@residual(wall:nyquist-2w-dof)` -/
theorem contAwgn_ge_shannonHartley
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    bandlimitedAwgnCapacity W N₀ P ≤ contAwgnOperationalCapacity W N₀ P := by
  -- Blocked on the operational bridge (test family + interlacing + capacity), not on the count
  -- itself; see docstring.
  sorry -- @residual(wall:nyquist-2w-dof)

/-- The **continuous-time Shannon-Hartley formula**: the operational capacity of the
band-limited AWGN channel equals `W · log(1 + P/(N₀·W))`.

Under the Karhunen-Loève observation map of `ContAwgnCode` this statement is expected true; an
earlier point-sampling model made it false as framed, and the def-fix that repaired it is recorded
in `docs/shannon/shannon-hartley-facts.md` §OBSERVATION-MAP. What remains is not a matter of
definition but of connecting the time-bandwidth degrees-of-freedom count to the operational
quantity.

Both halves need that count. `∫ f·φᵢ = ⟪f, P_W φᵢ⟫` for band-limited `f`, so the Gram matrix of the
test family is a compression of the time-band-limiting operator `timeBandLimitingOp T W`
(`TimeBandLimiting.lean`), and the achievable rate along any `[0, T]`-supported orthonormal family
is governed by that compression's eigenvalues, which Cauchy interlacing caps by the prolate
eigenvalues `prolateEigenvalues T W`. Reaching the closed form in the limit requires `≈ 2WT` of
them to sit near `1` and the rest near `0` — the Landau-Pollak-Slepian concentration.

That concentration is available. `prolateCount_le` and `le_prolateCount` (`TimeBandLimiting.lean`)
bracket `prolateCount T W c`, the number of prolate eigenvalues exceeding a free threshold
`c ∈ (0, 1)`, between `2WT − D/(1 − c)` and `2WT + D/c` with `D = 2 + log(1 + 2WT)`. The converse
needs the upper half (`prolateCount_le`), the achievability (`contAwgn_ge_shannonHartley`) the
lower half (`le_prolateCount`).

What is still missing is the bridge from the count to `contAwgnOperationalCapacity`: the Cauchy
interlacing step tying the Gram compression's eigenvalues to `prolateEigenvalues T W`, and the
capacity computation built on it. That bridge, not the count, is what this residual stands for.

Note the asymmetry that certifies the def-fix was a repair and not a disguise: the crude bound of
`contAwgnMaxMessages_bddAbove` closes by Bessel alone, wall-free, but caps the rate only at
`P/N₀`, and `ln(1+x) ≤ x` makes that strictly larger than the closed form. Boundedness comes for
free; the exact constant does not.

Hypotheses `hW`/`hN₀`/`hP` are regularity-only (not load-bearing).

The `wall:nyquist-2w-dof` slug is kept as the tracking tag, but its named proposition — the
eigenvalue concentration — is closed (`prolateCount_le` / `le_prolateCount`). The live obstruction
is the operational bridge above, not the count.

`@residual(wall:nyquist-2w-dof)` -/
@[entry_point]
theorem contAwgn_eq_shannonHartley
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    contAwgnOperationalCapacity W N₀ P = bandlimitedAwgnCapacity W N₀ P := by
  -- Blocked on the operational bridge (Gram compression ↔ prolate count, then capacity), not on
  -- the count itself; see docstring.
  sorry -- @residual(wall:nyquist-2w-dof)

end InformationTheory.Shannon.ShannonHartley
