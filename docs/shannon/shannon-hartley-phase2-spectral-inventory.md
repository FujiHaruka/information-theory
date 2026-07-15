# Shannon-Hartley Phase 2 — prolate-DOF spectral theory Mathlib inventory

> Parent moonshot: [`shannon-hartley-operational-moonshot-plan.md`](shannon-hartley-operational-moonshot-plan.md) §Phase 2.
> Scope: self-build the `wall:nyquist-2w-dof` core = spectral theory of the time-and-band-limiting
> operator `A = P_W ∘ Q_T ∘ P_W` on `L²(ℝ;ℂ)`. Docs-only survey; no code compiled.
> Verified against Mathlib in `.lake/packages/mathlib` on 2026-07-15 (commit a7097a27).

## One-line summary

**Of the API the Phase-2 spectral leg needs, the operator's algebraic backbone (definition,
self-adjointness, positivity) is ~100% covered by existing Mathlib assets that were not on the
plan's radar (the L²-Fourier isometry on the LINE `MeasureTheory.Lp.fourierTransformₗᵢ` exists +
`starProjection` + `conj_adjoint`/`adjoint_conj`). The compact self-adjoint SPECTRAL THEOREM exists
but only in structural form (eigenspaces span densely + nonzero eigenspaces finite-dim); there is NO
decreasing `ℕ → ℝ` eigenvalue enumeration outside finite dimension, NO Hilbert-Schmidt / Schatten /
trace-class, NO integral-operator / Mercer API.** So of the 7 target capabilities: 3 directly
available (def / self-adjoint / positive), 3 self-buildable-on-Mathlib (compactness via finite-rank
limit, eigenvalue enumeration, trace = 2WT), 1 genuine wall (the `≈2WT`-near-1 concentration count =
Landau-Pollak-Slepian, loogle `Found 0`). **The plan's "feasibility unknown (a): is Mathlib's
spectral theorem applicable" resolves to YES-structural; unknown (b) "decreasing enumeration exists"
resolves to NO (self-build); unknown (c) "concentration absent" resolves to CONFIRMED wall.**

---

## GATING verdicts (the three questions that decide whether the "genuine foundation" premise holds)

### Q1 — Spectral theorem for COMPACT self-adjoint operators (infinite-dim): **PARTIAL**

Mathlib HAS the structural spectral theorem for compact self-adjoint `T : E →L[𝕜] E` on a Hilbert
space (`[CompleteSpace E]`), in `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`:

- `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` (Spectrum.lean:443) — **THE
  spectral theorem**: the eigenspaces span a dense subspace (`(⨆ μ, eigenspace T μ)ᗮ = ⊥`).
- `ContinuousLinearMap.finite_dimensional_eigenspace` (Spectrum.lean:463) — nonzero eigenspaces are
  finite-dimensional.
- `IsCompactOperator.hasEigenvalue_iff_mem_spectrum` (Compact/FredholmAlternative.lean:220) — nonzero
  eigenvalues = nonzero spectrum (Fredholm alternative).

Mathlib does **NOT** have: a decreasing eigenvalue sequence `ℕ → ℝ`, an orthonormal eigenbasis of the
whole space indexed by `ℕ`, or a diagonalization isometry to `ℓ²`, for the infinite-dim compact case.
The enumerated/decreasing `LinearMap.IsSymmetric.eigenvalues` + `eigenvectorBasis` + `diagonalization`
(Spectrum.lean:279/300/178) are **`FiniteDimensional`-gated** (every one carries the explicit hypothesis
`(hn : Module.finrank 𝕜 E = n)`). The file's own `## TODO` reads: *"Spectral theory for bounded
self-adjoint operators."*

→ **GO for extracting eigenvalues (they exist, are real, span, finite multiplicity); NO-GO for a
ready-made ordered `ℕ`-sequence — that is a self-build (see §Self-build #3).**

### Q2 — Hilbert-Schmidt / Schatten operators: **NO (genuine gap)**

loogle `HilbertSchmidt` → `unknown identifier` (0 declarations). loogle `Schatten` → `unknown
identifier` (0 declarations). Whole-tree `rg 'Schatten|HilbertSchmidt|TraceClass'` over
`.lake/packages/mathlib/Mathlib` returns hits **only** in unrelated tactic/util files
(`Tactic/MoveAdd.lean`, `Util/Notation3.lean`, …) — zero in `Analysis/`. There is **no** Schatten-p
class, **no** `HilbertSchmidt` structure, **no** "L²-kernel ⟹ Hilbert-Schmidt", **no** "HS ⟹ compact".
`SingularValues.lean` exists but is **`[FiniteDimensional 𝕜 E]`-only**.

→ **NO-GO. The kernel-⟹-HS-⟹-compact route is entirely absent and must be self-built (or bypassed
via the finite-rank-norm-limit route, §Self-build #2).**

### Q3 — Trace-class / summable eigenvalues `∑ λ_k < ∞`: **NO (genuine gap)**

No trace-class in Mathlib (subset of Q2's absence). There is no `∑ eigenvalues` API. For our operator
the sum is analytically `∑ λ_k = trace(A) = ∫_{[0,T]} k(t,t) dt = ∫_{[0,T]} 2W dt = 2WT` (finite), but
proving it needs Mercer/trace machinery (absent) or the HS structure (absent).

→ **NO-GO for a Mathlib lemma; self-buildable once compactness + the L²-kernel representation exist,
but tied to the same effort as Q2.**

---

## The Phase-2 targets restated (from the parent plan)

```lean
-- E := Lp ℂ 2 (volume : Measure ℝ)   -- a complex Hilbert space (CompleteSpace ✓, InnerProductSpace ✓)
noncomputable def timeBandLimitingOp (T W : ℝ) : E →L[ℂ] E :=
  P_W ∘L Q_T ∘L P_W                          -- P_W = band-limit proj, Q_T = time-limit proj
theorem timeBandLimitingOp_isSelfAdjoint : IsSelfAdjoint (timeBandLimitingOp T W)   -- GENUINE, direct
theorem timeBandLimitingOp_isPositive   : (timeBandLimitingOp T W).IsPositive        -- GENUINE, direct
theorem timeBandLimitingOp_isCompact    : IsCompactOperator (timeBandLimitingOp T W) -- self-build (fin-rank limit)
noncomputable def prolateEigenvalues (T W : ℝ) : ℕ → ℝ := ...                         -- self-build (enumerate)
theorem prolate_eigenvalue_count (hT : 0 < T) (hW : 0 < W) :
    ⟨#{n | 1/2 < prolateEigenvalues T W n} concentrates at ⌊2WT⌋ + O(log WT)⟩ := by
  sorry   -- @residual(wall:nyquist-2w-dof)   -- Landau-Pollak-Slepian, Mathlib Found 0
```

Build shape (6–8 lines of pseudo-Lean):

```
Q_T := (timeLimitSubspace T).starProjection      -- orthogonal proj onto {f =ᵐ 0 off [0,T]}
P_W := (bandLimitSubspace W).starProjection       -- orthogonal proj onto {𝓕 f =ᵐ 0 off [-W,W]}
A := P_W ∘L Q_T ∘L P_W
isSelfAdjoint A  := (isSelfAdjoint_starProjection Q_T-sub).conj_adjoint P_W  -- P_W = P_W.adjoint
isPositive   A  := (IsPositive.of_isStarProjection Q_T-isStarProj).adjoint_conj P_W
isCompact    A  := isCompactOperator_of_tendsto (finite-rank kernel approximation → A)  -- SELF-BUILD
eigenvalues     := enumerate via orthogonalComplement_iSup_eigenspaces_eq_bot + finite_dimensional_eigenspace
count near 1    := sorry @residual(wall:nyquist-2w-dof)
```

---

## A. Compact operators (`IsCompactOperator`) — the compactness route

| concept | Mathlib API | file:line | status | handling in Phase 2 |
|---|---|---|---|---|
| compact-operator predicate | `IsCompactOperator (f : M₁ → M₂) : Prop` | `Mathlib/Analysis/Normed/Operator/Compact/Basic.lean` (def) | ✅ exists | the target predicate for `timeBandLimitingOp_isCompact` |
| **limit of compacts is compact** | `isCompactOperator_of_tendsto {ι 𝕜₁ 𝕜₂ …} [NontriviallyNormedField 𝕜₁] [NormedField 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂} {M₁ M₂} [SeminormedAddCommGroup M₁] [AddCommGroup M₂] [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂] [UniformSpace M₂] [IsUniformAddGroup M₂] [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] [CompleteSpace M₂] {l : Filter ι} [l.NeBot] {F : ι → M₁ →SL[σ₁₂] M₂} {f : M₁ →SL[σ₁₂] M₂} (hf : Tendsto F l (𝓝 f)) (hF : ∀ᶠ i in l, IsCompactOperator (F i))` | `Compact/Basic.lean:459` | ✅ exists | **the key tool**: approximate `A` in operator norm by finite-rank operators ⟹ `A` compact. Conclusion: `IsCompactOperator f` |
| set of compacts is closed | `isClosed_setOf_isCompactOperator […same brackets…] : IsClosed { f : M₁ →SL[σ₁₂] M₂ \| IsCompactOperator f }` | `Compact/Basic.lean:416` | ✅ exists | underlying `isCompactOperator_of_tendsto` |
| compact ∘ bounded, bounded ∘ compact | `IsCompactOperator.comp_clm`, `IsCompactOperator.clm_comp` | `Compact/Basic.lean` | ✅ exists | if any single factor is proven compact, propagate through `P_W`, `Q_T` |
| sums / smul of compacts | `IsCompactOperator.add`, `.sub`, `.neg`, `.smul` | `Compact/Basic.lean` | ✅ exists | finite-rank kernel = finite sum of rank-1 ⟹ compact |
| id compact ⟺ finite-dim | `isCompactOperator_id_iff_finiteDimensional [LocallyCompactSpace 𝕜] : IsCompactOperator (id : E → E) ↔ FiniteDimensional 𝕜 E` | `Compact/FiniteDimension.lean:26` | ✅ exists | to prove a finite-rank operator compact: it factors through a finite-dim space |
| **finite-rank ⟹ compact (direct)** | — | — | ❌ **absent as a named lemma** | derive from `isCompactOperator_id_iff_finiteDimensional` + `comp_clm` (a rank-`n` op factors `M₁ → (fin-dim range) → M₂`); ~20–40 lines |
| **L²-kernel ⟹ compact (Hilbert-Schmidt)** | — | — | ❌ **absent (Q2)** | not available; use finite-rank-norm-limit instead |

**Compactness strategy note.** With `B := P_W ∘L Q_T`, one has `A = P_W Q_T P_W = B ∘L B†` (using
`Q_T` idempotent + self-adjoint, `Q_T = Q_T ∘L Q_T`, `B† = Q_T ∘L P_W`). Its companion
`B† ∘L B = Q_T P_W Q_T` is the sinc integral operator on the time-limited subspace `≅ L²[0,T]` with
kernel `k(s,t) = 2W·sincN(2W(s−t))` (bounded, on the finite-measure square `[0,T]²` ⟹ `L²`). `A` and
`B†B` share their nonzero spectrum with multiplicities, so compactness of `A` reduces to compactness of
the sinc integral operator. **That reduction is where the finite-rank approximation lives** (approximate
the L² kernel by simple functions; each simple kernel gives a finite-rank operator; the operator-norm
error is bounded by the L² kernel error — the "Hilbert-Schmidt bound" proven inline).

---

## B. Self-adjoint / symmetric / adjoint — all DIRECTLY available

| concept | Mathlib API | file:line | status | handling in Phase 2 |
|---|---|---|---|---|
| adjoint of a CLM | `ContinuousLinearMap.adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] F →L[𝕜] E` | `Mathlib/Analysis/InnerProductSpace/Adjoint.lean:114` | ✅ exists | `(·)†` |
| self-adjoint ⟺ symmetric | `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric {A : E →L[𝕜] E} : IsSelfAdjoint A ↔ (A : E →ₗ[𝕜] E).IsSymmetric` | `Adjoint.lean:360` | ✅ exists | bridges `_root_.IsSelfAdjoint` (star algebra) with `LinearMap.IsSymmetric` |
| **conj preserves self-adjoint** | `IsSelfAdjoint.conj_adjoint {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (S : E →L[𝕜] F) : IsSelfAdjoint (S ∘L T ∘L S†)` | `Adjoint.lean:347` | ✅ exists | with `T = Q_T`, `S = P_W`, and `P_W† = P_W`: gives `IsSelfAdjoint (P_W Q_T P_W)` directly |
| conj (other side) | `IsSelfAdjoint.adjoint_conj (hT : IsSelfAdjoint T) (S : F →L[𝕜] E) : IsSelfAdjoint (S† ∘L T ∘L S)` | `Adjoint.lean:354` | ✅ exists | alternative bracketing |
| **projection is self-adjoint** | `isSelfAdjoint_starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : IsSelfAdjoint U.starProjection` | `Adjoint.lean:371` | ✅ exists | `Q_T`, `P_W` self-adjoint as orthogonal projections |
| conj of a projection | `IsSelfAdjoint.conj_starProjection (hT : IsSelfAdjoint T) (U) : IsSelfAdjoint (U.starProjection ∘L T ∘L U.starProjection)` | `Adjoint.lean:376` | ✅ exists | **exactly `P_W ∘L Q_T ∘L P_W`** — one call gives self-adjointness of `A` |
| adjoint inner identities | `ContinuousLinearMap.adjoint_inner_left/right` | `Adjoint.lean:123, 127` | ✅ exists | ⟪A†y,x⟫ = ⟪y,Ax⟫ |
| `NB: ContinuousLinearMap.IsSelfAdjoint` | — | — | ❌ **not a decl** (loogle `unknown identifier`) | self-adjointness of a CLM is the general `_root_.IsSelfAdjoint` (`star A = A`), reached via `isSelfAdjoint_iff'` / `isSelfAdjoint_iff_isSymmetric`; do NOT write `ContinuousLinearMap.IsSelfAdjoint` |

**`A`'s self-adjointness is a one-liner:** `(isSelfAdjoint_starProjection timeLimitSubspace).conj_starProjection bandLimitSubspace` (or `conj_adjoint` with `S = P_W`).

---

## C. Positive operators — DIRECTLY available

| concept | Mathlib API | file:line | status | handling in Phase 2 |
|---|---|---|---|---|
| positive CLM | `ContinuousLinearMap.IsPositive (T : E →L[𝕜] E) : Prop := T.IsSymmetric ∧ ∀ x, 0 ≤ T.reApplyInnerSelf x` | `Mathlib/Analysis/InnerProductSpace/Positive.lean:266` | ✅ exists | target of `timeBandLimitingOp_isPositive` |
| positive ⟺ selfadj + `0≤⟪Tx,x⟫` | `ContinuousLinearMap.isPositive_iff' [CompleteSpace E] (T) : IsPositive T ↔ IsSelfAdjoint T ∧ ∀ x, 0 ≤ ⟪T x, x⟫` | `Positive.lean:313` | ✅ exists | discharge form |
| **projection is positive** | `ContinuousLinearMap.IsPositive.of_isStarProjection [CompleteSpace E] {p : E →L[𝕜] E} (hp : IsStarProjection p) : p.IsPositive` | `Positive.lean:491` | ✅ exists | `Q_T` (and `P_W`) positive |
| **conj preserves positivity** | `ContinuousLinearMap.IsPositive.conj_adjoint [CompleteSpace E] [CompleteSpace F] {T : E →L[𝕜] E} (hT : T.IsPositive) (S : E →L[𝕜] F) : (S ∘L T ∘L S†).IsPositive` | `Positive.lean:355` | ✅ exists | with `T = Q_T`, `S = P_W`: `A` positive directly |
| conj (other side) | `ContinuousLinearMap.IsPositive.adjoint_conj [CompleteSpace E] [CompleteSpace F] (hT : T.IsPositive) (S : F →L[𝕜] E) : (S† ∘L T ∘L S).IsPositive` | `Positive.lean:366` | ✅ exists | alternative bracketing |
| positive ⟹ self-adjoint | `ContinuousLinearMap.IsPositive.isSelfAdjoint [CompleteSpace E] (hT : IsPositive T) : IsSelfAdjoint T` | `Positive.lean:281` | ✅ exists | derive self-adjoint from positive if preferred |
| eigenvalue ≥ 0 for positive | `eigenvalue_nonneg_of_nonneg {μ : ℝ} (hμ : HasEigenvalue T μ) (hnn : ∀ x, 0 ≤ RCLike.re ⟪x, T x⟫) : 0 ≤ μ` | `Spectrum.lean:409` | ✅ exists | prolate eigenvalues `∈ [0,1]` (`≥0` here; `≤1` from `‖A‖ ≤ 1`) |

---

## D. Orthogonal projections + the L²-Fourier isometry (defining `P_W`, `Q_T`)

| concept | Mathlib API | file:line | status | handling in Phase 2 |
|---|---|---|---|---|
| projection onto subspace (self-map CLM) | `Submodule.starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : E →L[𝕜] E` | `Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:124` | ✅ exists | `Q_T := (timeLimitSubspace T).starProjection`, `P_W := (bandLimitSubspace W).starProjection` |
| closed subspace has proj | `Submodule.HasOrthogonalProjection.ofCompleteSpace [CompleteSpace K]` (instance) | `Projection/Basic.lean` | ✅ exists | closed subspaces of `Lp ℂ 2` get the instance automatically |
| **L²-Fourier isometry on the LINE** | `MeasureTheory.Lp.fourierTransformₗᵢ (E F) : (Lp (α := E) F 2) ≃ₗᵢ[ℂ] (Lp (α := E) F 2)` — brackets: `[NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]` | `Mathlib/Analysis/Fourier/LpSpace.lean:50` | ✅ **exists (was assumed absent)** | `E = ℝ, F = ℂ` satisfy all brackets → genuine unitary `𝓕 : Lp ℂ 2 volume → Lp ℂ 2 volume`. Conjugate the frequency-indicator projection by it to define `P_W` |
| Plancherel norm | `MeasureTheory.Lp.norm_fourier_eq (f : Lp (α := E) F 2) : ‖𝓕 f‖ = ‖f‖` | `LpSpace.lean:89` | ✅ exists | energy preservation |
| Plancherel inner | `MeasureTheory.Lp.inner_fourier_eq (f g : Lp (α := E) F 2) : ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫` | `LpSpace.lean:93` | ✅ exists | self-adjointness of the conjugated projection |
| `𝓕` on Lp ↔ tempered distribution | `MeasureTheory.Lp.fourier_toTemperedDistribution_eq` | `LpSpace.lean:126` | ✅ exists | bridge to the in-project `IsBandlimited` spectral def |
| Fourier multiplier CLM | `fourierMultiplierCLM F (σ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F)` | `Mathlib/Analysis/Distribution/Sobolev.lean` | ⚠️ exists but on **tempered distributions**, not `Lp 2` | possible alt route for `P_W` (symbol `𝟙_{[-W,W]}`) but transferring the discontinuous symbol to `Lp 2` is more work than the `starProjection`-conjugation route |
| indicator-multiply on `Lp` as CLM | — | — | ❌ **no named "multiply by bounded fn" CLM on `Lp`** | `Q_T` / band-indicator are best modeled as `starProjection` onto the closed subspace `{f =ᵐ 0 off S}`, NOT as a multiplication operator |

**Design recommendation (Mathlib-shape-driven):** define `Q_T` and `P_W` as `starProjection`s onto
closed subspaces, not as multiplication operators — this makes self-adjointness (`isSelfAdjoint_starProjection`)
and positivity (`IsPositive.of_isStarProjection`) one-liners, and `A`'s self-adjoint/positive proofs
collapse to `conj_starProjection` / `conj_adjoint`. Defining them as multiplication operators would
force self-building the `M_g`-on-`Lp` boundedness/self-adjoint API.

---

## E. spectrum / eigenvalues / min-max

| concept | Mathlib API | file:line | status | handling in Phase 2 |
|---|---|---|---|---|
| **compact self-adjoint spectral thm** | `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot [CompleteSpace E] {T : E →L[𝕜] E} (hT : IsCompactOperator T) (hT' : T.IsSymmetric) : (⨆ μ, eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥` | `Spectrum.lean:443` | ✅ exists | eigenvectors are complete (dense span) — backbone of the enumeration |
| nonzero eigenspaces finite-dim | `ContinuousLinearMap.finite_dimensional_eigenspace [CompleteSpace E] (hT : IsCompactOperator T) (μ : 𝕜) (hμ : μ ≠ 0) : FiniteDimensional 𝕜 (eigenspace T.toLinearMap μ)` | `Spectrum.lean:463` | ✅ exists | finite multiplicity ⟹ can list each eigenvalue finitely often |
| nonzero eig = nonzero spectrum | `IsCompactOperator.hasEigenvalue_iff_mem_spectrum (hT : IsCompactOperator T) (hμ : μ ≠ 0) : HasEigenvalue (T : End 𝕜 X) μ ↔ μ ∈ spectrum 𝕜 T` | `Compact/FredholmAlternative.lean:220` | ✅ exists | extract eigenvalues from spectrum |
| Fredholm alternative | `IsCompactOperator.hasEigenvalue_or_mem_resolventSet` | `Compact/FredholmAlternative.lean:163` | ✅ exists | every nonzero spectral point is an eigenvalue |
| eigenvalues real | `LinearMap.IsSymmetric.conj_eigenvalue_eq_self` | `Spectrum.lean:94` | ✅ exists | prolate eigenvalues ∈ ℝ |
| eigenspaces orthogonal | `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces` | `Spectrum.lean:101` | ✅ exists | orthonormal eigenbasis pieces |
| operator norm = top Rayleigh | `LinearMap.IsSymmetric.norm_eq_iSup_rayleighQuotient (hT : T.IsSymmetric) : ‖T‖ = ⨆ x, …` | `Spectrum.lean` (Rayleigh.lean:120) | ✅ exists | top eigenvalue `λ_max = ‖A‖ ≤ 1` (min-max level 0) |
| eigenvector at extremum | `LinearMap.IsSymmetric.hasEigenvector_of_isLocalExtrOn (hT : IsSelfAdjoint T)` | `Rayleigh.lean:266` | ✅ exists | iterate for min-max enumeration |
| **decreasing `ℕ→ℝ` eigenvalue enum (infinite-dim)** | — | — | ❌ **absent** (only `LinearMap.IsSymmetric.eigenvalues (hn : Module.finrank 𝕜 E = n) : Fin n → ℝ`, Spectrum.lean:279 — FINITE-DIM) | self-build `prolateEigenvalues : ℕ → ℝ` (see §Self-build #3) |
| finite-dim min-max iSup | `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` | `Rayleigh.lean` | ✅ exists but **finite-dim only** | not directly usable on `L²(ℝ)` |
| Courant-Fischer / Weyl / Schur-Horn | — | — | ❌ absent (infinite-dim) | not needed for the count if LPS is the wall |

---

## F. Integral operators / Mercer / kernels

| concept | Mathlib API | file:line | status | handling in Phase 2 |
|---|---|---|---|---|
| integral operator `f ↦ ∫ k(·,y) f(y)` | — | — | ❌ **absent** (`rg 'integralOperator\|IntegralOperator\|withKernel'` over Mathlib = 0) | self-build if the kernel route is taken for compactness |
| kernel `L²` ⟹ HS ⟹ compact | — | — | ❌ **absent (Q2)** | self-build via finite-rank approximation |
| Mercer's theorem | — | — | ❌ **absent** (loogle `Mercer` = `unknown identifier`) | not needed unless proving `∑λ = 2WT` via the diagonal |
| eigenfunction expansion | — | — | ❌ absent | — |

---

## G. In-project reuse — closed assets

| asset | file:line | status | Phase 2 relevance |
|---|---|---|---|
| L²↔L¹ Fourier bridge | `ShannonHartleyOperational.lean:122` `l2Fourier_eq_fourierIntegral` (`@audit:ok`) | ✅ closed | connect the abstract `𝓕`-projection `P_W` to the concrete sinc/boxcar picture |
| inverse bridge | `ShannonHartleyOperational.lean:179` `l2FourierInv_eq_fourierIntegralInv` | ✅ closed | inverse direction |
| Paley-Wiener sup bound | `ShannonHartleyOperational.lean:241` `bandlimited_sup_bound` | ✅ (proof-done) | `\|f(t)\| ≤ √(2W)·‖f‖₂` for band-limited f — used in kernel boundedness |
| spectral `IsBandlimited` | `ShannonHartleyOperational.lean:104` `IsBandlimited f W := ∃ hf : MemLp …, 𝓕(hf.toLp) =ᵐ[restrict {W<\|ξ\|}] 0` | ✅ | the closed subspace `bandLimitSubspace W` is the `Lp`-membership version of this predicate |
| sinc kernel | `NormalizedSinc.lean:95` `sincN_int_eq_kronecker`; `WhittakerShannon.lean:63` `integral_exp_boxcar_eq_sincN` | ✅ closed | the kernel `k(s,t) = 2W·sincN(2W(s−t))` and its Fourier=boxcar identity |
| WS reconstruction | `WhittakerShannon.lean` `wsSignal` / `whittaker_shannon_bandlimited` | ✅ closed | analysis direction; eigenfunctions of `A` restricted to the band-limited subspace |

**No existing in-project spectral/operator machinery** (`rg 'IsCompactOperator\|IsSelfAdjoint\|LinearMap.IsSymmetric\|spectrum'` over `InformationTheory/` returns only prose mentions in Shannon-Hartley docstrings — no compact-operator or spectral-theorem usage anywhere in the project). Phase 2 builds this stack from scratch.

### In-project BddAbove-via-waterfilling assets (the achievability leg-2 alternative)

| asset | file:line | status | note |
|---|---|---|---|
| parallel-Gaussian capacity | `ParallelGaussian/Basic.lean:185` `parallelGaussianCapacity P N h_meas h_parallel_meas` | ✅ | value functional over `Fin (n+1)` modes |
| **capacity = Σ waterfill** | `ParallelGaussian/PerCoordRegularity.lean:74` `parallel_gaussian_capacity_formula_minimal {n} (P) (hP : 0 < P) (N : Fin (n+1) → ℝ≥0) (hN) (h_meas) (h_parallel_meas) (ν) (h_kkt : IsWaterFillingKKT P N ν) : parallelGaussianCapacity … = ∑ i : Fin (n+1), (1/2)*log(1 + …)` | ✅ closed | **`Fin (n+1)`-indexed (finite-dim), KKT-gated**; not an infinite-mode / operational message-count bound |
| KKT optimality | `ParallelGaussian/KKT.lean` `isWaterFillingOptimal_of_kkt` | ✅ closed | finite-mode water level |

**Verdict on the BddAbove route:** the water-filling assets give the capacity VALUE for finitely
many modes. The naive bound `∑_k (1/2)log(1 + λ_k p_k/N) ≤ (1/(2N)) ∑_k λ_k p_k ≤ (1/(2N))·‖A‖·(∑ p_k)
≤ P·‖A‖/(2N)` is **mode-count-independent** (needs only bounded eigenvalues + total power, not even
`∑λ_k<∞`). BUT this bounds a capacity FUNCTIONAL, not `contAwgnMaxMessages` (an operational `Nat.sSup`
of achievable message counts over ALL `ContAwgnCode`s). Converting requires the operational converse
(`awgn_converse` / Fano) applied to the effective channel, which needs a finite EFFECTIVE DIMENSION
bound — i.e. the eigenvalue count. So **the water-filling assets do NOT by themselves discharge leg-2
`BddAbove`; the plan's 2026-07-15 wall verdict (leg-2 shares `wall:nyquist-2w-dof`) stands.** The
crude capacity bound is worth recording as a partial refutation avenue (it shows the *information*
quantity is finite without the tight count) but it does not close the *operational* `BddAbove`.

---

## Key-preconditions box (accident-prone typeclass gotchas)

- **`fourierTransformₗᵢ` needs `[FiniteDimensional ℝ E]` + `[InnerProductSpace ℝ E]` on the DOMAIN and
  `[InnerProductSpace ℂ F] [CompleteSpace F]` on the CODOMAIN, plus `[MeasurableSpace E] [BorelSpace E]`.**
  For `E = ℝ`, `F = ℂ`, all hold, but the operator MUST live on `Lp ℂ 2 (volume : Measure ℝ)` (the
  `volume` is baked into the def to avoid timeouts — see LpSpace.lean:53). Do not silently switch the
  measure.
- **Every compact-self-adjoint spectral result requires `[CompleteSpace E]`** (the `ContinuousLinearMap`
  namespace section opens `variable [CompleteSpace E] {T : E →L[𝕜] E}`). `Lp ℂ 2` is complete ✓.
- **`orthogonalComplement_iSup_eigenspaces_eq_bot` (compact version, Spectrum.lean:443) takes BOTH
  `hT : IsCompactOperator T` AND `hT' : T.IsSymmetric`** — the compactness must be proven first
  (§Self-build #2) before the spectral theorem yields anything.
- **`finite_dimensional_eigenspace` is only for `μ ≠ 0`** — the kernel (eigenvalue 0) is infinite-dim
  (all functions not in the band-time-limited range), as expected.
- **`starProjection` needs `[U.HasOrthogonalProjection]`** — supplied by `HasOrthogonalProjection.ofCompleteSpace`
  only when `U` is a COMPLETE (= closed) subspace. Must prove `bandLimitSubspace`/`timeLimitSubspace`
  closed (preimage of a closed set under the continuous `𝓕` / restriction map).
- **`IsPositive.conj_adjoint` / `adjoint_conj` need `[CompleteSpace E] [CompleteSpace F]`** on both
  spaces (here both are `Lp ℂ 2`, fine).
- **`isCompactOperator_of_tendsto` needs `[l.NeBot]`** on the index filter — use `atTop` on `ℕ` (NeBot ✓).

---

## Elements that need self-building (priority order)

1. **`timeBandLimitingOp` + `isSelfAdjoint` + `isPositive`** — **LOW effort (~60–120 lines)**.
   Define `timeLimitSubspace`/`bandLimitSubspace` as closed subspaces, prove closed, take
   `starProjection`, compose. Self-adjoint = `conj_starProjection`; positive = `of_isStarProjection`
   + `adjoint_conj`. Pitfall: proving `bandLimitSubspace` closed needs the continuity of the
   `𝓕`-then-restrict map; use `fourierTransformₗᵢ.continuous` + `Lp.restrict`/indicator-kernel
   continuity. Not a wall.

2. **`timeBandLimitingOp_isCompact`** — **HIGH effort (~500–900 lines)**, self-buildable, NOT the wall.
   No Hilbert-Schmidt in Mathlib (Q2), so: (a) represent `B†B = Q_T P_W Q_T` as the sinc integral
   operator on `L²[0,T]`; (b) prove the kernel `2W·sincN(2W(s−t))·𝟙_{[0,T]²}` is `L²` (bounded on a
   finite-measure square); (c) approximate the kernel in `L²` by simple functions, each giving a
   finite-rank operator; (d) bound operator-norm by the L²-kernel norm (the HS bound, proven inline);
   (e) conclude via `isCompactOperator_of_tendsto`. Pitfall: this is genuinely the bulk of Phase 2's
   line count. Alternative (cheaper?): directly finite-rank-approximate `A` using the WS/sinc
   eigenfunction structure — but that risks circularity with the eigenvalue enumeration. **Recommend
   the kernel-simple-function route** (self-contained, uses `NormalizedSinc` + `bandlimited_sup_bound`).

3. **`prolateEigenvalues : ℕ → ℝ` (decreasing enumeration) + `_antitone` + `hasEigenvalue`** —
   **MEDIUM effort (~200–400 lines)**, self-buildable, NOT the wall. From
   `orthogonalComplement_iSup_eigenspaces_eq_bot` (dense span) + `finite_dimensional_eigenspace`
   (finite multiplicity) + Fredholm (`hasEigenvalue_iff_mem_spectrum`): the nonzero spectrum is
   countable, accumulates only at 0, each eigenvalue has finite multiplicity ⟹ list in decreasing
   order (repeated by multiplicity), padding with 0. Pitfall: Mathlib gives no ordered enumeration —
   you build the sorted list yourself; the "converge to 0 / discrete away from 0" fact needs the
   Fredholm `antilipschitz_of_not_hasEigenvalue` machinery.

4. **`∑ prolateEigenvalues = 2WT` (trace)** — **MEDIUM effort**, self-buildable but tied to #2.
   The trace equals `∫_{[0,T]} k(t,t) dt = 2WT`. Without trace-class API this needs the HS/kernel
   diagonal (Mercer-flavored). Only needed for the summability angle, not for the count. **May be
   scoped out** if the count wall is taken directly. Pitfall: `sincN(0)` normalization — verify the
   in-project `sincN` convention gives `k(t,t) = 2W` (not `1`).

5. **`prolate_eigenvalue_count` (≈2WT eigenvalues near 1)** — **GENUINE WALL** (see §Walls).

---

## Enumeration of Mathlib walls (`@residual(wall:...)` targets)

| wall slug | statement | loogle confirmation | verdict |
|---|---|---|---|
| **`nyquist-2w-dof`** | `#{n : ℕ \| 1/2 < prolateEigenvalues T W n}` concentrates at `⌊2WT⌋ + O(log(WT))` (Landau-Pollak-Slepian eigenvalue concentration of the prolate-spheroidal operator) | `loogle "prolate"` → `unknown identifier` (Found 0); `loogle "Slepian"` → Found 0; `loogle "Mercer"` → Found 0 | **GENUINE WALL** — the concentration asymptotic is absent from Mathlib and is the single documented sub-wall; body `sorry -- @residual(wall:nyquist-2w-dof)` |
| Hilbert-Schmidt / Schatten | "L²-kernel operator is Hilbert-Schmidt", "HS ⟹ compact", Schatten-p classes | `loogle "HilbertSchmidt"` Found 0; `loogle "Schatten"` Found 0; whole-Mathlib `rg` = 0 in `Analysis/` | **absent BUT bypassable** — not a wall for the goal; compactness self-built via finite-rank limit (§Self-build #2). **Recommend consolidating the "L²-kernel ⟹ compact" lemma into a shared in-project lemma** (it will be reused by any future integral-operator work; see `docs/audit/audit-tags.md` "Shared Mathlib walls"). This is a self-build, NOT a `wall:` sorry — it is provable. |
| integral-operator / Mercer API | `f ↦ ∫ k(·,y)f(y)` boundedness, Mercer expansion | `rg 'integralOperator'` = 0; `loogle "Mercer"` Found 0 | absent; self-build if the kernel route is used; not a `wall:` (constructible) |
| infinite-dim eigenvalue enumeration | ordered `ℕ → ℝ` eigenvalue sequence for compact self-adjoint | only `LinearMap.IsSymmetric.eigenvalues` (finite-dim, `finrank = n`) | absent; self-build (§Self-build #3); not a `wall:` (constructible from existing structural theorems) |

**Only ONE genuine `wall:` target: `nyquist-2w-dof`.** Everything else in the "absent" column is a
constructible self-build on top of the existing compact-self-adjoint spectral theorem + Fourier
isometry — expensive but not blocked. This matches the parent plan's Sub-wall map (Phase 2 row):
"operator + self-adjoint + compactness = genuine goal; only the eigenvalue concentration is the
genuine wall."

---

## Distance to the retreat lines

Parent plan Phase-2 retreat line (moonshot-plan.md:216):
> `prolate_eigenvalue_count` を `sorry + @residual(wall:nyquist-2w-dof)`. 作用素の自己共役・
> コンパクト性が Mathlib 不足で詰まる個別補題も同 wall に集約（compound 化しない）.

**Does it trigger? PARTIALLY — as designed, and MORE FAVORABLY than the plan assumed.**

- The plan's "feasibility unknown (a)" (is Mathlib's spectral theorem applicable) resolves **YES** —
  operator def + self-adjoint + positive are DIRECT (not even a large self-build), because the L²-Fourier
  isometry `MeasureTheory.Lp.fourierTransformₗᵢ` exists (the plan/inventory Phase 0 apparently did not
  register this; it unblocks defining `P_W` as a genuine unitary conjugate). → **retreat line does NOT
  trigger for self-adjoint/positive.**
- Unknown (b) (decreasing enumeration exists) resolves **NO** → self-build, not a wall → retreat line
  does NOT trigger (constructible).
- Unknown (c) (concentration absent) resolves **CONFIRMED** → the SINGLE genuine `wall:nyquist-2w-dof`
  sorry lives in `prolate_eigenvalue_count` exactly as the retreat line prescribes.
- **New risk surfaced (fold into the retreat line):** `timeBandLimitingOp_isCompact` is a LARGE
  self-build (~500–900 lines, no HS in Mathlib). If it stalls, the honest exit is
  `sorry -- @residual(wall:nyquist-2w-dof)` on the compactness lemma too (per the plan's "aggregate
  individual stuck lemmas into the same wall, no compounding"). **Proposed degenerate fallback / new
  retreat line:** if compactness cannot be self-built within budget, scope Phase 2 down to
  "operator + self-adjoint + positive proven genuine; compactness + count both left as
  `sorry @residual(wall:nyquist-2w-dof)`" — this still delivers the genuine operator object for the
  converse (Phase 4) to reference, with a single aggregated wall. Retreat exit = `sorry` + `@residual`;
  **no hypothesis bundling** (do not pass compactness/count as a `*Hypothesis` predicate — that is a
  tier-5 load-bearing defect).

No signature change to any existing shared InformationTheory lemma is required by Phase 2 (it only
ADDS a new file + reads closed sinc/Fourier assets), so no `dep_consumers` blast-radius applies.
`contAwgn_le_shannonHartley` (Phase 4) will consume `prolate_eigenvalue_count`; that consumer wiring
is Phase 4's concern, not Phase 2's.

---

## Starting skeleton

`InformationTheory/Shannon/TimeBandLimiting.lean` (new file; register in `InformationTheory.lean`):

```lean
import Mathlib.Analysis.Fourier.LpSpace                         -- MeasureTheory.Lp.fourierTransformₗᵢ (Plancherel)
import Mathlib.Analysis.InnerProductSpace.Spectrum              -- compact self-adjoint spectral theorem
import Mathlib.Analysis.InnerProductSpace.Positive              -- IsPositive.conj_adjoint / of_isStarProjection
import Mathlib.Analysis.InnerProductSpace.Adjoint               -- conj_starProjection / isSelfAdjoint_starProjection
import Mathlib.Analysis.InnerProductSpace.Projection.Basic      -- Submodule.starProjection
import Mathlib.Analysis.Normed.Operator.Compact.Basic           -- isCompactOperator_of_tendsto
import InformationTheory.Shannon.NormalizedSinc                 -- sincN kernel
import InformationTheory.Shannon.WhittakerShannon               -- integral_exp_boxcar_eq_sincN

namespace InformationTheory.Shannon.TimeBandLimiting

open MeasureTheory ProbabilityTheory
open scoped FourierTransform RealInnerProductSpace

/-- The `L²(ℝ;ℂ)` Hilbert space the operator acts on. -/
abbrev E : Type := Lp ℂ 2 (volume : Measure ℝ)

/-- Time-limited subspace: `L²` functions a.e.-supported in `[0,T]`. Closed. -/
def timeLimitSubspace (T : ℝ) : Submodule ℂ E := sorry   -- @residual(plan:shannon-hartley-operational-moonshot-plan)

/-- Band-limited subspace: `L²` functions whose `𝓕` is a.e.-supported in `[-W,W]`. Closed. -/
def bandLimitSubspace (W : ℝ) : Submodule ℂ E := sorry    -- @residual(plan:shannon-hartley-operational-moonshot-plan)

/-- Time-and-band limiting operator `P_W ∘ Q_T ∘ P_W`. -/
noncomputable def timeBandLimitingOp (T W : ℝ) : E →L[ℂ] E :=
  (bandLimitSubspace W).starProjection ∘L
    (timeLimitSubspace T).starProjection ∘L (bandLimitSubspace W).starProjection

theorem timeBandLimitingOp_isSelfAdjoint (T W : ℝ) :
    IsSelfAdjoint (timeBandLimitingOp T W) := by
  sorry   -- @residual(plan:shannon-hartley-operational-moonshot-plan)  -- conj_starProjection, DIRECT

theorem timeBandLimitingOp_isPositive (T W : ℝ) :
    (timeBandLimitingOp T W).IsPositive := by
  sorry   -- @residual(plan:shannon-hartley-operational-moonshot-plan)  -- of_isStarProjection + adjoint_conj, DIRECT

theorem timeBandLimitingOp_isCompact (T W : ℝ) :
    IsCompactOperator (timeBandLimitingOp T W) := by
  sorry   -- @residual(wall:nyquist-2w-dof)  -- self-build via finite-rank kernel limit (large; aggregate into wall if stalled)

/-- Decreasing prolate-spheroidal eigenvalue sequence. -/
noncomputable def prolateEigenvalues (T W : ℝ) : ℕ → ℝ := by
  sorry   -- @residual(plan:shannon-hartley-operational-moonshot-plan)  -- enumerate spanning eigenspaces

theorem prolate_eigenvalue_count (T W : ℝ) (hT : 0 < T) (hW : 0 < W) :
    True := by   -- placeholder for the concentration inequality (⌊2WT⌋ + O(log WT))
  sorry   -- @residual(wall:nyquist-2w-dof)  -- Landau-Pollak-Slepian, Mathlib Found 0

end InformationTheory.Shannon.TimeBandLimiting
```

(The `def`-body `sorry`s for `timeLimitSubspace`/`bandLimitSubspace`/`prolateEigenvalues` are
placeholders for the skeleton only; per CLAUDE.md "Handling order where `sorry` can't be written"
these must be real definitions before commit — a `def` body cannot honestly carry `sorry`. State
`prolate_eigenvalue_count` with the real inequality once `prolateEigenvalues` is defined; the `True`
above is a skeleton stand-in, not a shippable statement.)

---

## Feasibility summary (≤40 lines)

| target | verdict | evidence |
|---|---|---|
| **operator def** (`timeBandLimitingOp`) | **(i) directly available** | `MeasureTheory.Lp.fourierTransformₗᵢ` (LpSpace.lean:50) + `Submodule.starProjection` (Projection/Basic.lean:124) + `HasOrthogonalProjection.ofCompleteSpace`. Was assumed "unknown" by the plan; it is DIRECT. |
| **self-adjoint** | **(i) directly available** | `IsSelfAdjoint.conj_starProjection` (Adjoint.lean:376) / `conj_adjoint` (Adjoint.lean:347) + `isSelfAdjoint_starProjection` (Adjoint.lean:371). One-liner. |
| **positive** | **(i) directly available** | `IsPositive.of_isStarProjection` (Positive.lean:491) + `IsPositive.adjoint_conj` (Positive.lean:366). One-liner. |
| **compact / Hilbert-Schmidt** | **(ii) self-buildable on Mathlib** (~500–900 lines) | NO HS/Schatten (loogle Found 0); build via `isCompactOperator_of_tendsto` (Compact/Basic.lean:459) + finite-rank simple-kernel approximation of the sinc integral operator. Not a wall. |
| **eigenvalue enumeration** | **(ii) self-buildable on Mathlib** (~200–400 lines) | structural spectral thm `orthogonalComplement_iSup_eigenspaces_eq_bot` (Spectrum.lean:443) + `finite_dimensional_eigenspace` (Spectrum.lean:463) + Fredholm (FredholmAlternative.lean:220); NO ready ordered `ℕ→ℝ` seq (finite-dim only, Spectrum.lean:279). |
| **trace summability `∑λ = 2WT`** | **(ii) self-buildable** (tied to compactness) / optional | no trace-class API; = `∫_{[0,T]} 2W dt`. Only needed for the summability angle, not the count. |
| **BddAbove via water-filling** (achievability leg-2) | **(iii) does NOT close via water-filling alone** | `parallel_gaussian_capacity_formula_minimal` (PerCoordRegularity.lean:74) is finite-dim/KKT-gated; crude `log(1+x)≤x` bounds the capacity FUNCTIONAL mode-count-independently, but the operational `Nat.sSup` message-count `BddAbove` still needs the effective-dimension count = `wall:nyquist-2w-dof` (plan's 2026-07-15 verdict stands). |
| **tight concentration** (`≈2WT` near 1) | **(iii) genuine wall** | `wall:nyquist-2w-dof`; loogle `prolate`/`Slepian`/`Mercer` all Found 0. |

**Bottom line:** the "genuine foundation" premise **holds and is stronger than the plan assumed** —
operator/self-adjoint/positive are direct one-liners on existing Mathlib, so the operator OBJECT is
real (non-degenerate, non-circular). The heavy lifting is compactness (self-build, no HS) + eigenvalue
enumeration (self-build), both constructible. The ONE irreducible `wall:nyquist-2w-dof` is the
Landau-Pollak-Slepian concentration count. Single most dangerous finding: **`isCompactOperator_of_tendsto`
+ finite-rank approximation is the ~500–900-line load-bearing self-build with no Mathlib scaffolding —
if it stalls, honest-sorry it into `wall:nyquist-2w-dof` (no hypothesis bundling), don't fake it.**
```
