# Whittaker–Shannon (cardinal series) sampling theorem — Mathlib API inventory

> Scope: assess whether the **Whittaker–Shannon sampling theorem** can be
> formalized on current Mathlib via the **"WS via Fourier series"** route (§ Route below).
> Parent plan: [`docs/shannon/whittaker-shannon-partial-moonshot-plan.md`](whittaker-shannon-partial-moonshot-plan.md).
> Already-published sinc scaffolding: `InformationTheory/Shannon/NormalizedSinc.lean`
> (`sincN`, `sincN_int_eq_kronecker`, `whittaker_shannon_sample_collapse`, 13 decls, 0 sorry).
> This inventory is docs-only; it edits no `.lean` file.

## One-line summary

**Of the API used by the Fourier-series route, ~85% already exists in current Mathlib
(the full L² Fourier series on `AddCircle`, Plancherel on `Lp 2`, the interval↔circle
bridge, the boxcar-sinc integral, and the L²-`HasSum`↔inner-product interchange are all
shipped). ~3 self-built bridge lemmas remain (boxcar↔`sincN` change-of-variables ~30 lines,
`fourierCoeff ↔ sample` sign reconciliation ~40 lines, and the bandlimited-representation /
inversion glue ~60 lines).** The roadmap's "WS is a genuine ~600-line wall" verdict is
**overturned for this route** — that estimate was priced against the *direct* route
(compute `𝓕(sinc) = 1_{[-1/2,1/2]}` + shifted-sinc L²-orthogonality), which the
Fourier-series route bypasses entirely: sinc emerges as the boxcar integral
`∫_{-1/2}^{1/2} e^{2πiξs} dξ = sincN s`, and that integral is already a Mathlib lemma.

## The target theorem (restated) and the proof route

Target (WS, L² band-limited to `[-1/2, 1/2]`, period-1 normalization):

```
For f ∈ L²(ℝ) with 𝓕 f supported in [-1/2, 1/2],
    f t = ∑' n : ℤ, f n · sincN (t - n),        sincN s = Real.sinc (π · s) = sin(πs)/(πs).
```

Route "WS via Fourier series" (per-`t`, HasSum form — no `𝓕(sinc)`, no Poisson):

```lean
-- F := 𝓕 f  ∈ L²([-1/2,1/2]) ≅ Lp ℂ 2 (haarAddCircle (T := 1))         -- via memLp_liftIoc.haarAddCircle.toLp
-- Step 2 (L² Fourier series on the circle):
have hL2 : HasSum (fun n => fourierCoeff F n • fourierLp 2 n) F := hasSum_fourier_series_L2 F
-- Step 5 (push the fixed bounded functional ⟪g t, ·⟫ through the L² HasSum):
have := (innerSL ℂ (gExp t)).hasSum hL2          -- HasSum.mapL : HasSum (fun n => ⟪g t, cₙ•eₙ⟫) ⟪g t, F⟫
-- Step 4 (each monomial term is a boxcar integral = sincN):
--   ⟪g t, fourierLp 2 n⟫ = ∫_{-1/2}^{1/2} e^{2πiξt} e^{2πinξ} dξ = sincN (t + n)   -- integral_exp_mul_I_eq_sinc
-- Step 3 (the coefficient is a sample, via 𝓕⁻ / fourierCoeff sign match):
--   cₙ = fourierCoeff F n = ∫_{-1/2}^{1/2} e^{-2πinξ} F ξ dξ = 𝓕⁻ F (-n) = f (-n)
-- reindex n ↦ -n:
⊢ HasSum (fun m : ℤ => f m • sincN (t - m)) (f t)
```

The `⟪·,·⟫` here is the `Lp ℂ 2 haarAddCircle` inner product (conjugate-linear in the
first slot: `⟪a,b⟫ = ∫ conj a · b`). Because `T = 1`, `haarAddCircle` has total mass 1 and
`haarAddCircle = volume` on `AddCircle 1`, so all inner products unfold to plain
`∫_{-1/2}^{1/2}` interval integrals.

---

## Verdict table — per route step

| Step | What it needs | Mathlib status | Handling |
|---|---|---|---|
| 1. `𝓕 f ∈ L²[-1/2,1/2]` as a circle-L² element | `MemLp.memLp_liftIoc` + `.haarAddCircle` + `.toLp` | **PRESENT** | direct plumbing; `T=1` |
| 2. L² Fourier series `F = ∑ cₙ eₙ` converges in L² | `hasSum_fourier_series_L2` | **PRESENT** | apply verbatim |
| 3. coefficient = sample `cₙ = f(-n)` | `fourierCoeff_eq_intervalIntegral` + `Real.fourier_eq`/`𝓕⁻` | **PARTIAL** — sign reconciliation self-build (~40 lines) |
| 4. boxcar `∫_{-1/2}^{1/2} e^{2πiξs}dξ = sincN s` | `integral_exp_mul_I_eq_sinc` + `integral_comp_mul_left` | **PARTIAL** — change-of-variables self-build (~30 lines) |
| 5. push `⟪g,·⟫` through the L² `HasSum` | `ContinuousLinearMap.hasSum` (`HasSum.mapL`) + `innerSL` | **PRESENT** | the technical crux is a 3-liner |
| 0. bandlimited representation / `f = 𝓕⁻(𝓕 f)` | Fourier `inversion` + support glue | **PARTIAL** — modeling + inversion glue (~60 lines), or avoid by stating in terms of the circle-L² element |

Aggregate: **3 of 6 steps PRESENT verbatim, 3 PARTIAL (self-built glue).**
No step is ABSENT. The parent plan's declined retreat lines L-WS-B (shifted-sinc
orthogonality via `𝓕(sinc)`) and L-WS-C (Plancherel/Poisson) are **not on the critical
path** of this route.

---

## A. Fourier series on the circle (`Mathlib/Analysis/Fourier/AddCircle.lean`)

All under `variable {T : ℝ} [hT : Fact (0 < T)]`; scalar space `ℂ`. For the WS route take `T = 1`
(`Fact (0 < (1:ℝ))` is `Fact.mk one_pos`, always available).

| concept | Mathlib API | file:line | status | route step |
|---|---|---|---|---|
| Haar measure on circle | `def haarAddCircle : Measure (AddCircle T) := addHaarMeasure ⊤` (+ `instance : IsProbabilityMeasure (@haarAddCircle T _)`) | `Mathlib/Analysis/Fourier/AddCircle.lean:85` (inst `:89`) | ✅ | 2 |
| circle-vol = T·haar | `theorem volume_eq_smul_haarAddCircle : (volume : Measure (AddCircle T)) = ENNReal.ofReal T • (@haarAddCircle T _)` | `…/AddCircle.lean:92` | ✅ | at `T=1`, haar = volume |
| exponential monomial | `def fourier (n : ℤ) : C(AddCircle T, ℂ)` | `…/AddCircle.lean:123` | ✅ | 4 |
| its value on `ℝ` | `theorem fourier_coe_apply {n : ℤ} {x : ℝ} : fourier n (x : AddCircle T) = Complex.exp (2 * π * Complex.I * n * x / T)` | `…/AddCircle.lean:132` | ✅ | 4 (`T=1`: `e^{2πinx}`) |
| monomial in `Lp` | `abbrev fourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) : Lp ℂ p (@haarAddCircle T hT) := toLp (E := ℂ) p haarAddCircle ℂ (fourier n)` | `…/AddCircle.lean:251` | ✅ | 2,4 |
| orthonormality | `theorem orthonormal_fourier : Orthonormal ℂ (@fourierLp T _ 2 _)` | `…/AddCircle.lean:271` | ✅ | 2 (backing) |
| Fourier coefficient | `def fourierCoeff (f : AddCircle T → E) (n : ℤ) : E := ∫ t : AddCircle T, fourier (-n) t • f t ∂haarAddCircle` — under `{E} [NormedAddCommGroup E] [NormedSpace ℂ E]` | `…/AddCircle.lean:297` | ✅ | 3 |
| coeff as interval integral | `theorem fourierCoeff_eq_intervalIntegral (f : AddCircle T → E) (n : ℤ) (a : ℝ) : fourierCoeff f n = (1 / T) • ∫ x in a..a + T, @fourier T (-n) x • f x` | `…/AddCircle.lean:302` | ✅ | 3 (`a=-1/2, T=1`) |
| interval-coeff def | `def fourierCoeffOn {a b : ℝ} (hab : a < b) (f : ℝ → E) (n : ℤ) : E := … fourierCoeff (AddCircle.liftIoc (b - a) a f) n` | `…/AddCircle.lean:352` | ✅ | 3 (interval form) |
| interval-coeff integral | `theorem fourierCoeffOn_eq_integral {a b : ℝ} (f : ℝ → E) (n : ℤ) (hab : a < b) : fourierCoeffOn hab f n = (1 / (b - a)) • ∫ x in a..b, fourier (-n) (x : AddCircle (b - a)) • f x` | `…/AddCircle.lean:356` | ✅ | 3 |
| Hilbert basis | `def fourierBasis : HilbertBasis ℤ ℂ (Lp ℂ 2 <| @haarAddCircle T hT)` | `…/AddCircle.lean:410` | ✅ | 2 (backing) |
| basis coe | `theorem coe_fourierBasis : ⇑(@fourierBasis T hT) = @fourierLp T hT 2 _` | `…/AddCircle.lean:416` | ✅ | 2 |
| repr = coeff | `theorem fourierBasis_repr (f : Lp ℂ 2 <| @haarAddCircle T hT) (i : ℤ) : fourierBasis.repr f i = fourierCoeff f i` | `…/AddCircle.lean:422` | ✅ | 2 |
| **L² convergence** | `theorem hasSum_fourier_series_L2 (f : Lp ℂ 2 <| @haarAddCircle T hT) : HasSum (fun i => fourierCoeff f i • fourierLp 2 i) f` | `…/AddCircle.lean:432` | ✅ **crux** | 2 |
| Parseval (circle) | `theorem hasSum_sq_fourierCoeff (f : Lp ℂ 2 <| @haarAddCircle T hT) : HasSum (fun i => ‖fourierCoeff f i‖ ^ 2) (∫ t : AddCircle T, ‖f t‖ ^ 2 ∂haarAddCircle)` | `…/AddCircle.lean:439` | ✅ | (energy identity, optional) |
| Parseval (interval) | `theorem hasSum_sq_fourierCoeffOn {a b : ℝ} {f : ℝ → ℂ} (hab : a < b) (hL2 : MemLp f 2 (volume.restrict (Ioc a b))) : HasSum (fun i => ‖fourierCoeffOn hab f i‖ ^ 2) ((b - a)⁻¹ • ∫ x in a..b, ‖f x‖ ^ 2)` | `…/AddCircle.lean:458` | ✅ | (optional) |
| pointwise (summable) | `theorem hasSum_fourier_series_of_summable (h : Summable (fourierCoeff f)) : HasSum (fun i => fourierCoeff f i • fourier i) f` — `{f : C(AddCircle T, ℂ)}` | `…/AddCircle.lean:493` | ✅ | alt. route (needs `f∈C(circle)` + `Σ|cₙ|<∞`) |
| pointwise eval | `theorem has_pointwise_sum_fourier_series_of_summable (h : Summable (fourierCoeff f)) (x : AddCircle T) : HasSum (fun i => fourierCoeff f i • fourier i x) (f x)` | `…/AddCircle.lean:503` | ✅ | alt. route |
| coeff of a monomial | `theorem fourierCoeff_fourier {T : ℝ} [hT : Fact (0 < T)] (n : ℤ) : fourierCoeff (T := T) (fourier n) = Pi.single n 1` | `…/AddCircle.lean:513` | ✅ | 4 (Kronecker) |

## B. Interval ↔ circle bridge

| concept | Mathlib API | file:line | status | route step |
|---|---|---|---|---|
| lift `ℝ→circle` | `def AddCircle.liftIoc (f : 𝕜 → B) : AddCircle p → B := restrict _ f ∘ AddCircle.equivIoc p a` | `Mathlib/Topology/Instances/AddCircle/Defs.lean:321` | ✅ | 1 |
| lift value | `theorem AddCircle.liftIoc_coe_apply {f : 𝕜 → B} {x : 𝕜} (hx : x ∈ Ioc a (a + p)) : liftIoc p a f ↑x = f x` | `…/AddCircle/Defs.lean:373` | ✅ | 1 |
| covering map MP | `protected theorem AddCircle.measurePreserving_mk (t : ℝ) : MeasurePreserving (…) (volume.restrict (Ioc t (t+T))) volume` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean:93` | ✅ | 1 (backing) |
| circle∫ = Ioc∫ | `protected theorem AddCircle.integral_preimage (t : ℝ) (f : AddCircle T → E) : (∫ a in Ioc t (t + T), f a) = ∫ b : AddCircle T, f b` — `[NormedAddCommGroup E] [NormedSpace ℝ E]`; **`volume` on the circle** | `…/Periodic.lean:190` | ✅ | 3,4 |
| circle∫ = interval∫ | `protected theorem AddCircle.intervalIntegral_preimage (t : ℝ) (f : AddCircle T → E) : ∫ a in t..t + T, f a = ∫ b : AddCircle T, f b` | `…/Periodic.lean:205` | ✅ | 3,4 |
| lift∫ = interval∫ | `lemma AddCircle.integral_liftIoc_eq_intervalIntegral {t : ℝ} {f : ℝ → E} : ∫ a, liftIoc T t f a = ∫ a in t..t + T, f a` | `…/Periodic.lean:212` | ✅ | 3,4 |
| interval-L² → circle-L² | `lemma MeasureTheory.MemLp.memLp_liftIoc {T : ℝ} [hT : Fact (0 < T)] {t : ℝ} {f : ℝ → ℂ} {p : ℝ≥0∞} (hLp : MemLp f p (volume.restrict (Ioc t (t + T)))) : MemLp (AddCircle.liftIoc T t f) p` | `…/Periodic.lean:224` | ✅ **crux for step 1** | 1 |
| Lp under vol vs haar | `lemma MeasureTheory.memLp_haarAddCircle_iff [hT : Fact (0 < T)] {f : AddCircle T → ℂ} {p : ℝ≥0∞} : MemLp f p AddCircle.haarAddCircle ↔ MemLp f p` (alias `MemLp.haarAddCircle`) | `Mathlib/Analysis/Fourier/AddCircle.lean:105` | ✅ | 1 |

## C. Real-line Fourier transform + inversion

Convention (confirmed verbatim): `𝓕 f w = ∫ v, 𝐞 (-⟪v,w⟫) • f v = ∫ e^{-2πi⟪v,w⟫} f v`,
inverse `𝓕⁻ f w = ∫ 𝐞 (⟪v,w⟫) • f v = ∫ e^{+2πi⟪v,w⟫} f v` (the inv instance uses `-innerₗ V`).

| concept | Mathlib API | file:line | status | route step |
|---|---|---|---|---|
| `𝓕` value form | `lemma Real.fourier_eq (f : V → E) (w : V) : 𝓕 f w = ∫ v, 𝐞 (-⟪v, w⟫) • f v` | `Mathlib/Analysis/Fourier/FourierTransform.lean:435` | ✅ | 3 (sign anchor) |
| `𝓕` exp form | `lemma Real.fourier_eq' (f : V → E) (w : V) : 𝓕 f w = ∫ v, Complex.exp ((↑(-2 * π * ⟪v, w⟫) * Complex.I)) • f v` | `…/FourierTransform.lean:441` | ✅ | 3 |
| `𝓕⁻∘𝓕 = id` (a.e./cts pt) | `theorem MeasureTheory.Integrable.fourierInv_fourier_eq (hf : Integrable f) (h'f : Integrable (𝓕 f)) {v : V} (hv : ContinuousAt f v) : 𝓕⁻ (𝓕 f) v = f v` | `Mathlib/Analysis/Fourier/Inversion.lean:165` | ✅ | 0 (textbook wrapper) |
| `𝓕⁻∘𝓕 = id` (cts) | `theorem Continuous.fourierInv_fourier_eq (h : Continuous f) (hf : Integrable f) (h'f : Integrable (𝓕 f)) : 𝓕⁻ (𝓕 f) = f` | `…/Inversion.lean:177` | ✅ | 0 |
| `𝓕∘𝓕⁻ = id` (cts pt) | `theorem MeasureTheory.Integrable.fourier_fourierInv_eq (hf : Integrable f) (h'f : Integrable (𝓕 f)) {v : V} (hv : ContinuousAt f v) : 𝓕 (𝓕⁻ f) v = f v` | `…/Inversion.lean:189` | ✅ | 0 |
| `𝓕∘𝓕⁻ = id` (cts) | `theorem Continuous.fourier_fourierInv_eq (h : Continuous f) (hf : Integrable f) (h'f : Integrable (𝓕 f)) : 𝓕 (𝓕⁻ f) = f` | `…/Inversion.lean:202` | ✅ | 0 |

Inversion typeclass context (`Inversion.lean:48–50` + `variable [CompleteSpace E]` at `:160`):
`{V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
[FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E} [CompleteSpace E]`.
For the WS instance take `V = ℝ`, `E = ℂ`; `ℝ` satisfies all of these (`InnerProductSpace ℝ ℝ`,
`FiniteDimensional ℝ ℝ`, `BorelSpace ℝ`).

## D. Boxcar → sinc

| concept | Mathlib API | file:line | status | route step |
|---|---|---|---|---|
| unnormalized sinc | `noncomputable def Real.sinc (x : ℝ) : ℝ := if x = 0 then 1 else sin x / x` | `Mathlib/Analysis/SpecialFunctions/Trigonometric/Sinc.lean:38` | ✅ | 4 (`sincN s := sinc (π s)`) |
| `sinc 0` | `@[simp] lemma Real.sinc_zero : sinc 0 = 1` | `…/Sinc.lean:43` | ✅ | 4 |
| `sinc` ne-zero | `lemma Real.sinc_of_ne_zero (hx : x ≠ 0) : sinc x = sin x / x` | `…/Sinc.lean:45` | ✅ | 4 |
| `sinc` even | `@[simp] lemma Real.sinc_neg (x : ℝ) : sinc (-x) = sinc x` | `…/Sinc.lean:52` | ✅ | 4 |
| `sinc` bounded | `lemma Real.abs_sinc_le_one (x : ℝ) : |sinc x| ≤ 1` | `…/Sinc.lean:57` | ✅ | (bounds) |
| `sinc` continuous | `@[fun_prop] lemma Real.continuous_sinc : Continuous sinc` | `…/Sinc.lean:86` | ✅ | (regularity) |
| **boxcar = sinc** | `lemma integral_exp_mul_I_eq_sinc (r : ℝ) : ∫ t in -r..r, Complex.exp (t * Complex.I) = 2 * r * sinc r` (root namespace, `open Real` ⇒ `sinc = Real.sinc`) | `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean:267` | ✅ **crux for step 4** | 4 |
| change of variables | `@[simp] theorem intervalIntegral.integral_comp_mul_left (hc : c ≠ 0) : (∫ x in a..b, f (c * x)) = c⁻¹ • ∫ x in c * a..c * b, f x` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:934` | ✅ | 4 (substitution) |
| sinc-from-charFun (reference) | `lemma MeasureTheory.integral_charFun_Icc [IsFiniteMeasure μ] (hr : 0 < r) : ∫ t in -r..r, charFun μ t = 2 * r * ∫ x, sinc (r * x) ∂μ` | `Mathlib/MeasureTheory/Measure/IntegralCharFun.lean:44` | ✅ | template for step 4 |

Project-side `sincN` (already published — do **not** re-derive):
`InformationTheory/Shannon/NormalizedSinc.lean:49` `noncomputable def sincN (x : ℝ) : ℝ := Real.sinc (Real.pi * x)`,
plus `sincN_zero`, `sincN_of_ne_zero`, `sincN_int_eq_zero`, `sincN_int_eq_kronecker`,
`whittaker_shannon_sample_collapse`, `continuous_sincN`, `measurable_sincN` (13 decls, 0 sorry).

## E. Plancherel / L² Fourier transform (`Mathlib/Analysis/Fourier/LpSpace.lean`)

Context (`LpSpace.lean:37–43`): `{E F} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
[NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [InnerProductSpace ℝ E]
[FiniteDimensional ℝ E]`. For WS take `E = ℝ`, `F = ℂ`.

| concept | Mathlib API | file:line | status | route step |
|---|---|---|---|---|
| L² FT isometry | `def MeasureTheory.Lp.fourierTransformₗᵢ : (Lp (α := E) F 2) ≃ₗᵢ[ℂ] (Lp (α := E) F 2)` | `Mathlib/Analysis/Fourier/LpSpace.lean:50` | ✅ | (Plancherel; not on critical path but relates `𝓕 f` L²-norm) |
| Plancherel norm | `@[simp] theorem MeasureTheory.Lp.norm_fourier_eq (f : Lp (α := E) F 2) : ‖𝓕 f‖ = ‖f‖` | `…/LpSpace.lean:89` | ✅ | energy check |
| Plancherel inner | `theorem MeasureTheory.Lp.inner_fourier_eq (f g : Lp (α := E) F 2) : ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫` | `…/LpSpace.lean:93` | ✅ | energy check |
| Schwartz ↔ L² FT | `theorem SchwartzMap.toLp_fourier_eq (f : 𝓢(E, F)) : 𝓕 (f.toLp 2) = (𝓕 f).toLp 2` | `…/LpSpace.lean:99` | ✅ | (bridge Schwartz witness ↔ L²) |

Note: `Lp.fourierTransformₗᵢ` is the L²-Fourier transform as an isometric equivalence — the
*existence* of an L²-Fourier transform (the fact the parent plan flagged as "Plancherel present
but not the sinc transform") is fully shipped. The WS route does **not** need it directly, but
it is available for the "band-limited element ↔ its inverse transform" formulation.

## F. Poisson summation (`Mathlib/Analysis/Fourier/PoissonSummation.lean`) — alternative route

| concept | Mathlib API | file:line | status |
|---|---|---|---|
| Poisson, general | `theorem Real.tsum_eq_tsum_fourier {f : C(ℝ, ℂ)} (h_norm : ∀ K : Compacts ℝ, Summable fun n : ℤ => ‖(f.comp <| ContinuousMap.addRight n).restrict K‖) (h_sum : Summable fun n : ℤ => 𝓕 (f : ℝ → ℂ) n) (x : ℝ) : ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 (f : ℝ → ℂ) n * fourier n (x : UnitAddCircle)` | `…/PoissonSummation.lean:102` | ✅ |
| Poisson, rpow decay | `theorem Real.tsum_eq_tsum_fourier_of_rpow_decay {f : ℝ → ℂ} (hc : Continuous f) {b : ℝ} (hb : 1 < b) (hf : f =O[cocompact ℝ] (|·| ^ (-b))) (hFf : (𝓕 f) =O[cocompact ℝ] (|·| ^ (-b))) (x : ℝ) : ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle)` | `…/PoissonSummation.lean:212` | ✅ |
| Poisson, Schwartz | `theorem SchwartzMap.tsum_eq_tsum_fourier (f : 𝓢(ℝ, ℂ)) (x : ℝ) : ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle)` | `…/PoissonSummation.lean:230` | ✅ |

The parent plan asserted "Poisson summation … not in Mathlib (`PoissonSummation` placeholder does
not exist)". **That is stale/wrong**: Poisson summation ships in three forms. It is not needed on
the Fourier-series critical path but *is* the natural tool if a downstream needs a
`∑ f(x+n)`-style aliasing/dual identity.

## G. L² inner product + `HasSum`↔inner interchange (step 5, the technical crux)

| concept | Mathlib API | file:line | status | route step |
|---|---|---|---|---|
| L² inner as integral | `theorem MeasureTheory.L2.inner_def (f g : α →₂[μ] E) : ⟪f, g⟫ = ∫ a : α, ⟪f a, g a⟫ ∂μ` — `{α E 𝕜} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] …` | `Mathlib/MeasureTheory/Function/L2Space.lean:139` | ✅ | 3,4 (unfold ⟪·,·⟫ to ∫) |
| inner as CLM | `def innerSL (𝕜) : E →L⋆[𝕜] E →L[𝕜] 𝕜` ; `theorem innerSL_apply_apply (v w : E) : innerSL 𝕜 v w = ⟪v, w⟫` | `Mathlib/Analysis/InnerProductSpace/LinearMap.lean:164` (`:172`) | ✅ | 5 |
| **push CLM through HasSum** | `protected theorem ContinuousLinearMap.hasSum {f : ι → M} (φ : M →SL[σ] M₂) {x : M} (hf : HasSum f x L) : HasSum (fun b : ι ↦ φ (f b)) (φ x) L` (alias `HasSum.mapL`) | `Mathlib/Topology/Algebra/InfiniteSum/Module.lean:122` (`:126`) | ✅ **crux for step 5** | 5 |
| ℓ² inner HasSum (ref) | `theorem hasSum_inner (f g : lp G 2) : HasSum (fun i => ⟪f i, g i⟫) ⟪f, g⟫` | `Mathlib/Analysis/InnerProductSpace/l2Space.lean:150` | ✅ | (energy identity form) |

Step 5 in three lines: `(innerSL ℂ g).hasSum (hasSum_fourier_series_L2 F)` gives
`HasSum (fun n => (innerSL ℂ g) (cₙ • eₙ)) ((innerSL ℂ g) F)`; then `innerSL_apply_apply` +
`inner_smul_right` turn each summand into `cₙ · ⟪g, eₙ⟫` and the total into `⟪g, F⟫`.

## H. Band-limited representation — no Mathlib predicate

loogle name searches (index `.lake/build/loogle.index`):
- `"Bandlimited"` → **Found 0 declarations whose name contains "Bandlimited".**
- `"PaleyWiener"` → **Found 0 declarations whose name contains "PaleyWiener".**
- `"WhittakerShannon"` → **Found 0 declarations whose name contains "WhittakerShannon".**
- `"cardinalSeries"` → **Found 0 declarations whose name contains "cardinalSeries".**
- `"sincN"` → **Found 0** (normalized sinc lives only in `InformationTheory/Shannon/NormalizedSinc.lean`).

There is no `IsBandlimited` predicate and no Paley–Wiener theorem. Band-limitedness must be
self-stated. Two idiomatic options:
- **(preferred, self-contained)** phrase the theorem over an L² circle element
  `F : Lp ℂ 2 (haarAddCircle (T := 1))` directly (a band-limited `𝓕 f` *is* exactly such an
  element), and define `f t := ⟪gExp t, F⟫`. No real-line `𝓕`, no support predicate, no
  inversion glue — unconditional.
- **(textbook wrapper)** `f : ℝ → ℂ` with `Continuous f`, `Integrable f`, `Integrable (𝓕 f)`,
  and `∀ ξ, ξ ∉ Set.Icc (-1/2 : ℝ) (1/2) → 𝓕 f ξ = 0`. Recover `f = 𝓕⁻ (𝓕 f)` via §C and
  restrict the `𝓕⁻` integral to the interval using the support hypothesis.

---

## Key-preconditions box (precondition-accident traps)

- **`hasSum_fourier_series_L2`** (step 2): argument type is `Lp ℂ 2 (haarAddCircle (T := 1))`
  — *not* an `L²`-on-`ℝ` element. You must first *land* `𝓕 f` in that exact space via
  `MemLp.memLp_liftIoc` (needs `MemLp (𝓕 f) 2 (volume.restrict (Ioc a (a+1)))`, `a = -1/2`)
  then `.haarAddCircle` then `.toLp`. Getting the measure wrong (`volume` vs `haarAddCircle`)
  or the interval half-open form (`Ioc`, not `Icc`/`Ioo`) is the most likely wiring bug.
- **Fourier inversion** (`Integrable.fourierInv_fourier_eq`, only for the textbook wrapper):
  requires **all three** — `Integrable f`, `Integrable (𝓕 f)`, and `ContinuousAt f v`. Missing
  `Integrable (𝓕 f)` is the classic omission; for band-limited `f` it holds because `𝓕 f` has
  compact support, but that must be discharged (support + `IsFiniteMeasure` on the interval).
  Typeclasses on `V = ℝ`: `InnerProductSpace ℝ ℝ`, `BorelSpace ℝ`, `FiniteDimensional ℝ ℝ`,
  `CompleteSpace ℂ` — all instances, none load-bearing new hypotheses.
- **`Lp.fourierTransformₗᵢ` / Plancherel** (§E): demands `[FiniteDimensional ℝ E]` and
  `[InnerProductSpace ℝ E]` on the *domain* `E`. `E = ℝ` is fine; do not accidentally set
  `E = AddCircle 1` (the circle is not the domain of the real-line FT).
- **`AddCircle.integral_preimage` family** (§B): stated for the circle's **`volume`**, while
  `fourierCoeff` integrates against **`haarAddCircle`**. `volume_eq_smul_haarAddCircle` bridges
  them, and at `T = 1` the scalar is `ENNReal.ofReal 1 = 1`, so they coincide — but the `T = 1`
  simplification must be applied explicitly (`fourierCoeff_eq_intervalIntegral` already folds the
  `1/T` factor for you; prefer it over hand-rolling the measure swap).
- **`innerSL` conjugation slot** (step 5): `⟪·,·⟫` on `Lp ℂ 2` is conjugate-linear in the
  **first** argument (`⟪a,b⟫ = ∫ conj a · b`, per `fourierBasis_repr`). Define `gExp t` so that
  `conj (gExp t ξ) = e^{2πiξt}` (i.e. `gExp t ξ = e^{-2πiξt}`); a sign flip here silently
  reindexes the whole series.

---

## Elements that need self-building (priority order)

1. **Boxcar-to-`sincN` bridge** — `⟪gExp t, fourierLp 2 n⟫ = sincN (t + n)`, i.e.
   `∫_{-1/2}^{1/2} e^{2πiξ(t+n)} dξ = Real.sinc (π (t+n))`.
   - Recommended: unfold `L2.inner_def` + `integral_liftIoc_eq_intervalIntegral` to an
     `∫ ξ in -1/2..1/2, Complex.exp (2π(t+n)ξ · I)`; substitute `u = 2π(t+n)·ξ` via
     `intervalIntegral.integral_comp_mul_left` (case-split `t+n = 0` vs `≠ 0`); apply
     `integral_exp_mul_I_eq_sinc`; cast the resulting real `2r·sinc r` back through
     `Complex.ofReal`. Template: mirror `integral_charFun_Icc`'s proof (`IntegralCharFun.lean:44`)
     almost verbatim.
   - Effort: **~30 lines**. Pitfall: the `2r` prefactor cancels the `1/(2π(t+n))` Jacobian;
     the `r = 0` (i.e. `t + n = 0`) branch must be handled with `sinc_zero` (value `1`).
2. **Coefficient-to-sample reconciliation** — `fourierCoeff F n = f (-n)` where
   `f w = 𝓕⁻ F w` (or `f w := ⟪gExp w, F⟫` in the self-contained version).
   - Recommended (self-contained): show `fourierCoeff F n = ⟪fourierLp 2 n, F⟫`
     (`fourierBasis_repr` gives `= fourierCoeff F n` directly) and
     `f (-n) = ⟪gExp (-n), F⟫`; then `⟪gExp (-n), F⟫ = ⟪fourierLp 2 n, F⟫` because
     `conj (gExp (-n) ξ) = e^{2πinξ} = fourier n ξ` a.e. — a one-`integral_congr_ae` step.
   - Effort: **~40 lines** (mostly `a.e.` congruence + the `fourier_coe_apply` at `T=1`
     rewriting). Pitfall: sign of `n` in `fourier (-n)` inside `fourierCoeff` vs the sign in
     `gExp`; the reindex `m = -n` at the end must be a `HasSum` reindex (`Equiv.neg ℤ`), not a
     naive `tsum` relabel.
3. **Band-limited representation glue** (only for the textbook wrapper, not the self-contained
   statement) — from `Continuous f`, `Integrable f`, `Integrable (𝓕 f)`,
   `∀ ξ ∉ Icc, 𝓕 f ξ = 0`, produce `MemLp (𝓕 f) 2 (volume.restrict (Ioc (-1/2) (1/2)))` and
   `f t = ∫_{-1/2}^{1/2} 𝓕 f ξ · e^{2πiξt} dξ`.
   - Recommended: `Continuous.fourierInv_fourier_eq` gives `f = 𝓕⁻ (𝓕 f)`; then
     `𝓕⁻ (𝓕 f) t = ∫ ξ, e^{2πiξt} (𝓕 f) ξ` and `setIntegral`-restrict to the interval using the
     support hypothesis (`MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero` or
     `integral_eq_setIntegral` on the support). `MemLp 2` from boundedness of `𝓕 f` (continuous
     on a compact interval) + finite measure.
   - Effort: **~60 lines**. Pitfall: `𝓕 f` continuous requires `f` integrable (Riemann–Lebesgue
     gives continuity of `𝓕 f`, already in Mathlib); the `Integrable (𝓕 f)` hypothesis is what
     you *assume* (band-limited ⇒ compact support ⇒ integrable), so it is a genuine precondition,
     not the theorem's core.

Aggregate self-build: **~130 lines** (self-contained statement) or **~190 lines** (textbook
wrapper), versus the roadmap's ~600-line estimate for the direct route.

## Enumeration of Mathlib walls (`@residual(wall:…)` candidates)

There is **no genuine analytic wall on the Fourier-series route.** The only true Mathlib absences
are naming/predicate gaps, all trivially self-buildable:

| gap | loogle confirmation | verdict |
|---|---|---|
| `IsBandlimited` predicate | `"Bandlimited"` → **Found 0 declarations** | naming gap; self-state (§H). Not a wall. |
| Paley–Wiener theorem | `"PaleyWiener"` → **Found 0 declarations** | not needed by this route (would only be needed to *derive* band-limitedness from decay; we take it as a hypothesis). Not on path. |
| Whittaker–Shannon theorem itself | `"WhittakerShannon"` → **Found 0**, `"cardinalSeries"` → **Found 0** | this is the target we build. Not a wall — assembled from §A–G. |
| normalized `sincN` | `"sincN"` → **Found 0** in Mathlib | already published in-project (`NormalizedSinc.lean`). Not a wall. |

No shared sorry-lemma is warranted: every remaining piece is a provable bridge, not a blocked
proposition. If a future session *does* stall on step 1 or 2, the honest exit is a local
`sorry` + `@residual(plan:whittaker-shannon)` in the WS file — **not** a `wall:` tag, because
no loogle-0 proposition underlies it.

## Distance to the parent plan's retreat lines

Parent plan retreat lines (`whittaker-shannon-partial-moonshot-plan.md` §撤退ライン):
- **L-WS-A** (sinc-basic + integer-zero + sample-point collapse + 1-point pass-through):
  **adopted, already published** (`NormalizedSinc.lean`). This inventory does not touch it.
- **L-WS-B** (L²-orthogonality of `{sinc(·-n)}` via `𝓕(sinc) = 1_{[-1/2,1/2]}` + Plancherel;
  the plan priced this at ~600 lines): **does NOT trigger for the Fourier-series route.** The
  route never forms `𝓕(sinc)` nor invokes shifted-sinc orthogonality; sinc appears only as the
  boxcar integral (§D), and orthonormality is `orthonormal_fourier` on the *exponential*
  monomials, which is shipped.
- **L-WS-C** (Plancherel-style identity / Poisson summation): the plan claimed both were "far
  from Mathlib". **Overturned**: Plancherel on `Lp 2` (§E) and Poisson summation in three forms
  (§F) are both shipped. Neither is on the Fourier-series critical path, but their availability
  removes L-WS-C as a blocker.

**Verdict: the Fourier-series route does not touch L-WS-B/L-WS-C at all**, so those retreat
lines do not gate it. The route replaces "prove `𝓕(sinc)` + orthogonality" (the direct route's
expensive core) with "L² Fourier series on the circle + boxcar integral", both already in
Mathlib.

Proposed **new degenerate fallback** (retreat line for the WS file itself, if the full HasSum
theorem stalls): publish the **finite-`t`, per-`t` HasSum on the self-contained circle-L²
statement** (recommended statement (ii) below) and leave the *textbook-wrapper* (statement (i),
which needs §-element-3 inversion glue) as `sorry` + `@residual(plan:whittaker-shannon)`. The
self-contained HasSum is unconditional (no band-limited-support hypothesis needed beyond
`F : Lp ℂ 2 haarAddCircle`), so the fallback exit carries no load-bearing hypothesis bundling.

## Recommended cleanest theorem statement(s)

Chosen so the dominating lemmas' conclusion forms are usable as-is (Mathlib-shape-driven):
`hasSum_fourier_series_L2` returns a `HasSum`, and `ContinuousLinearMap.hasSum` preserves it, so
the WS conclusion is stated as a **`HasSum`** (not a `tsum` equality or an `‖·‖→0` limit).

**(ii) Self-contained / per-`t` HasSum (unconditional — the honest core).**
Define the reconstruction from an L² spectrum `F` directly; `T = 1` so `haarAddCircle` has mass 1.

```lean
open MeasureTheory Real
open scoped RealInnerProductSpace ComplexInnerProductSpace

/-- The band-limited signal reconstructed from an L² spectrum `F` on `AddCircle 1`. -/
noncomputable def wsSignal (F : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) (t : ℝ) : ℂ :=
  ⟪wsExp t, F⟫                                   -- wsExp t := (ξ ↦ e^{-2πiξt}) as an L² element

theorem whittaker_shannon_hasSum
    (F : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) (t : ℝ) :
    HasSum (fun n : ℤ => wsSignal F n • (sincN (t - n) : ℂ)) (wsSignal F t) := by
  sorry   -- assemble §A step 2 + §G step 5 + §D step 4 + self-build items 1,2
```

**(i) Textbook / real-line band-limited form (adds §C inversion glue).**

```lean
open MeasureTheory Real
open scoped FourierTransform

theorem whittaker_shannon_bandlimited
    (f : ℝ → ℂ) (hcont : Continuous f) (hf : Integrable f) (hFf : Integrable (𝓕 f))
    (hband : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2) : ℝ) (1/2) → 𝓕 f ξ = 0) (t : ℝ) :
    HasSum (fun n : ℤ => f n • (sincN (t - n) : ℂ)) (f t) := by
  sorry   -- reduce to (ii) with F := (𝓕 f restricted to the interval) as a circle-L² element,
          -- using Continuous.fourierInv_fourier_eq + the support hypothesis (self-build item 3)
```

Reindex note: the summand `f n • sincN (t - n)` is obtained from the raw `f (-n) • sincN (t + n)`
by the `HasSum` reindex along `Equiv.neg ℤ` (`sincN` is even, `sincN_neg`, so `sincN (t+n)`
under `n ↦ -n` is `sincN (t-n)`).

## Starting skeleton — `InformationTheory/Shannon/WhittakerShannon.lean`

```lean
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.L2Space
import InformationTheory.Shannon.NormalizedSinc

open MeasureTheory Real Complex intervalIntegral
open scoped FourierTransform RealInnerProductSpace ComplexInnerProductSpace

namespace InformationTheory.Shannon.WhittakerShannon

open InformationTheory.Shannon.NormalizedSinc  -- sincN, sincN_neg, sincN_int_eq_kronecker

/-- `Fact (0 < 1)` so `AddCircle 1` carries `haarAddCircle`. -/
instance : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩

/-- The evaluation kernel `ξ ↦ e^{-2πiξt}` as an `L²` element of the unit circle. -/
noncomputable def wsExp (t : ℝ) : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) := by
  sorry   -- @residual(plan:whittaker-shannon): bounded ⇒ MemLp on a finite measure; .toLp

/-- The reconstructed band-limited signal. -/
noncomputable def wsSignal (F : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) (t : ℝ) : ℂ :=
  ⟪wsExp t, F⟫

/-- Step 4 bridge: the monomial pairing is the normalized sinc. -/
theorem inner_wsExp_fourierLp (t : ℝ) (n : ℤ) :
    ⟪wsExp t, (AddCircle.fourierLp (T := 1) 2 n)⟫ = (sincN (t + n) : ℂ) := by
  sorry   -- @residual(plan:whittaker-shannon): integral_exp_mul_I_eq_sinc + integral_comp_mul_left

/-- Step 3 bridge: the Fourier coefficient is the sample value. -/
theorem fourierCoeff_eq_wsSignal (F : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) (n : ℤ) :
    AddCircle.fourierCoeff (F : AddCircle 1 → ℂ) n = wsSignal F (-n) := by
  sorry   -- @residual(plan:whittaker-shannon): fourierBasis_repr + integral_congr_ae

/-- **Whittaker–Shannon**, per-`t` HasSum on an L² spectrum (unconditional core). -/
theorem whittaker_shannon_hasSum
    (F : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) (t : ℝ) :
    HasSum (fun n : ℤ => wsSignal F n • (sincN (t - n) : ℂ)) (wsSignal F t) := by
  sorry   -- @residual(plan:whittaker-shannon): (innerSL ℂ (wsExp t)).hasSum hasSum_fourier_series_L2
          -- + the two bridges + Equiv.neg ℤ reindex

end InformationTheory.Shannon.WhittakerShannon
```

The skeleton type-checks with `sorry` warnings only; fill in dependency order
`wsExp → inner_wsExp_fourierLp → fourierCoeff_eq_wsSignal → whittaker_shannon_hasSum`.
