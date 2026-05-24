# EPI de Bruijn integration — Mathlib inventory (Phase A)

Verbatim signature inventory for `epi-debruijn-integration-plan` Phase A-D
implementation. All signatures copied **verbatim** from Mathlib / V2 Fisher info
files (no paraphrasing of `[...]` typeclass prerequisites).

Convention:
- `file:line` — anchor in Mathlib / project
- **Signature** — full statement, `[...]` typeclasses intact
- **Use in plan** — which Phase / step consumes it

---

## A-1 — `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` (FTC, bounded)

**File**: `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1141`

```lean
theorem integral_eq_sub_of_hasDerivAt_of_le
    (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b) :
    ∫ y in a..b, f' y = f b - f a
```

**Use in plan**: Phase C-1, the canonical bounded-interval FTC. Note RHS is
`f b - f a` (not `f a - f b`), and integration uses `..` notation (resolved to
`Ioc` when `a ≤ b`).

---

## A-2 — `intervalIntegral.integral_eq_sub_of_hasDerivAt` (uIcc version)

**File**: `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1149`

```lean
theorem integral_eq_sub_of_hasDerivAt
    (hderiv : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b) :
    ∫ y in a..b, f' y = f b - f a
```

**Use in plan**: alternative to A-1 when `uIcc a b` form is more convenient.

---

## A-3 — `intervalIntegral.integral_of_le` (Ioc form bridge)

**File**: `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:667`

```lean
theorem integral_of_le (h : a ≤ b) :
    ∫ x in a..b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
```

**Use in plan**: Phase C-1, convert FTC output (`∫ y in a..b, ...`) to
`Ioc`-form (matches `Set.Ioc` integration shape).

---

## A-4 — `MeasureTheory.integral_Ioc_eq_integral_Ioo`

**File**: `Mathlib/MeasureTheory/Integral/Bochner/Set.lean`

```lean
theorem integral_Ioc_eq_integral_Ioo
    {f : α → E} {a b : α} :
    ∫ t in Ioc a b, f t ∂μ = ∫ t in Ioo a b, f t ∂μ
```

(actual signature uses `NoAtoms μ` for general `α`; for `ℝ` and `volume` is
automatic)

**Use in plan**: Phase C-1, bridge to `Set.Ioo` form (matches `IsDeBruijnIntegrationHyp`
RHS shape `∫ t in Set.Ioo 0 T, ...`).

---

## A-5 — `Real.sqrt_zero`

**File**: `Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean` (Mathlib core)

```lean
@[simp] theorem Real.sqrt_zero : Real.sqrt 0 = 0
```

**Use in plan**: Phase C-2 boundary case `f 0 = differentialEntropy (P.map X)`,
since `gaussianConvolution X Z 0 = X` pointwise (`X ω + √0 · Z ω = X ω`).

---

## A-6 — V2 sub-predicate: `IsRegularDeBruijnHypV2`

**File**: `Common2026/Shannon/FisherInfoV2DeBruijn.lean:236`

```lean
structure IsRegularDeBruijnHypV2 {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P]
    (t : ℝ) where
  Z_law : P.map Z = gaussianReal 0 1
  density_t : ℝ → ℝ
  derivAt_entropy_eq_half_fisher_v2 :
    HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal density_t)
      t
```

**Use in plan**: Phase B, the per-time-point regularity. `IsDeBruijnRegularityHyp`
(in `EPIStamDischarge.lean:143`) wraps this as `∀ t > 0`.

---

## A-7 — V2 Gaussian deBruijn discharge: `deBruijn_identity_v2_gaussian`

**File**: `Common2026/Shannon/FisherInfoV2DeBruijn.lean:360`

```lean
theorem deBruijn_identity_v2_gaussian
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfMeasureV2Real (P.map (gaussianConvolution X Z t))
          (gaussianPDFReal m (v + ⟨t, ht.le⟩)))
      t
```

**Use in plan**: Phase B-4, hypothesis-free constructor for
`IsDeBruijnRegularityHyp_of_gaussian`. Gives `HasDerivAt` directly; the
`density_t` witness is `gaussianPDFReal m (v + ⟨t, ht.le⟩)`.

---

## A-8 — `gaussianConvolution_law_of_gaussian`

**File**: `Common2026/Shannon/FisherInfoV2DeBruijn.lean:172`

```lean
theorem gaussianConvolution_law_of_gaussian
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1)
    {t : ℝ} (ht : 0 ≤ t) :
    P.map (gaussianConvolution X Z t)
      = gaussianReal m (v + ⟨t, ht⟩)
```

**Use in plan**: Phase C-2/C-3, identify `P.map (gaussianConvolution X Z t)` with
a Gaussian for boundary computations.

---

## A-9 — `gaussianConvolution` abbrev + simp

**File**: `Common2026/Shannon/FisherInfoV2DeBruijn.lean:154`

```lean
noncomputable def gaussianConvolution {α : Type*} (X Z : α → ℝ) (t : ℝ) : α → ℝ :=
  fun ω => X ω + Real.sqrt t * Z ω

@[simp] theorem gaussianConvolution_apply {α : Type*} (X Z : α → ℝ) (t : ℝ) (ω : α) :
    gaussianConvolution X Z t ω = X ω + Real.sqrt t * Z ω := rfl
```

**Use in plan**: Phase C-2 unfold the heat-flow path.

---

## A-10 — `differentialEntropy_gaussianReal_heat_path`

**File**: `Common2026/Shannon/FisherInfoV2DeBruijn.lean:332`

```lean
theorem differentialEntropy_gaussianReal_heat_path
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    differentialEntropy (gaussianReal m (v + ⟨s, hs⟩))
      = (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s))
```

**Use in plan**: Phase C-3, closed-form value of `f T` (Gaussian X case).

---

## A-11 — `hasDerivAt_half_log_gaussian_entropy`

**File**: `Common2026/Shannon/FisherInfoV2DeBruijn.lean:290`

```lean
theorem hasDerivAt_half_log_gaussian_entropy
    {v : ℝ≥0} (s : ℝ) (hvs : 0 < (v : ℝ) + s) :
    HasDerivAt
      (fun s' : ℝ => (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s')))
      (1 / (2 * ((v : ℝ) + s))) s
```

**Use in plan**: Phase B-3, derivative of the Gaussian heat-flow entropy
(used for the `HasDerivAt` family lift).

---

## A-12 — `fisherInfoOfMeasureV2Real_gaussianReal` / `fisherInfoOfDensityReal_gaussianPDFReal`

**File**: `Common2026/Shannon/FisherInfoV2.lean:332` / `FisherInfoV2DeBruijn.lean:126`

```lean
theorem fisherInfoOfDensityReal_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    fisherInfoOfDensityReal (gaussianPDFReal m v) = 1 / (v : ℝ)

theorem fisherInfoOfMeasureV2Real_gaussianReal
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    fisherInfoOfMeasureV2Real (gaussianReal m v) (gaussianPDFReal m v) = 1 / (v : ℝ)
```

**Use in plan**: Phase B-3 / C-3, identify the RHS `(1/2) · J` with `1/(2(v+t))`.

---

## A-13 — `MeasureTheory.IntervalIntegrable.continuousOn_intervalIntegrable`

For showing `IntervalIntegrable f' volume a b` from continuity of `f'` on `[a, b]`.

**File**: `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`

```lean
theorem ContinuousOn.intervalIntegrable
    {f : ℝ → E} (hf : ContinuousOn f [[a, b]]) :
    IntervalIntegrable f volume a b
```

**Use in plan**: Phase C-1, used to discharge the `hint` argument of
`integral_eq_sub_of_hasDerivAt_of_le` (when the derivative is continuous,
e.g. the Gaussian case `1/(2(v+t))` is continuous on `[0, T]` because
`v + t > 0` throughout).

---

## A-14 — `continuousOn_inv` / `Continuous.div`

For continuity of `1/(2(v+t))` on `[0, T]`.

**File**: `Mathlib/Topology/ContinuousOn.lean` etc.

**Use in plan**: Phase C-1 supplement to A-13.

---

## Mathlib gaps (Phase A confirmed)

- **`Mathlib.Analysis.PDE.*`**: 不在 (`rg "PDE" .lake/packages/mathlib/Mathlib` returns
  no PDE folder). Heat-equation IBP must be self-contained or routed through V2 sub-predicate
  `IsIBPHypothesis` already in `FisherInfoV2DeBruijnBody.lean:204`.
- **Unbounded interval FTC**: `intervalIntegral.integral_deriv_eq_sub` and friends are
  **bounded only**. Unbounded `(0, ∞)` lift requires `MeasureTheory.integral_iUnion_eq_lim`
  + tail analysis. Plan uses `IsDeBruijnTailHyp` honest hypothesis to externalize.
- **`Differentiable.convolution`**: not directly available for our use case
  (`gaussianConvolution` is a plain `fun ω => X ω + √t · Z ω`, not a `MeasureTheory.convolution`).
  We don't need it since we work with `gaussianConvolution` directly.

---

## V2 sub-predicate inheritance summary

Phase B-D consume these existing V2 predicates without modification:

| Predicate | File:line | Phase usage |
|---|---|---|
| `IsRegularDeBruijnHypV2 X Z P t` | `FisherInfoV2DeBruijn.lean:236` | B (constructed for Gaussian) |
| `IsHeatFlowDensity X Z P p` | `FisherInfoV2DeBruijnBody.lean:~140` | not directly used (Gaussian case bypasses) |
| `IsIBPHypothesis X Z P p t` | `FisherInfoV2DeBruijnBody.lean:204` | not directly used (Gaussian case bypasses) |
| `deBruijn_identity_v2_gaussian` | `FisherInfoV2DeBruijn.lean:360` | B-4 hypothesis-free witness |
| `deBruijn_identity_v2_of_heat_flow` | `FisherInfoV2DeBruijnBody.lean:238` | not directly used (general case via `IsHeatFlowFamilyHyp`) |

---

## New honest predicates introduced by this plan

| Predicate | Purpose | Audit tag |
|---|---|---|
| `IsHeatFlowFamilyHyp X Z P` | Family-level regularity for general `X` (Phase B-5) | `@audit:staged(epi-heat-flow-family-regularity)` |
| `IsDeBruijnTailHyp X Z P` | `T → ∞` tail analysis for general `X` (Phase C-5) | `@audit:staged(epi-debruijn-tail)` |

Both are **load-bearing honest hypotheses**, type ≠ conclusion, docstring states
"NOT a discharge / load-bearing". Used to externalize regularity facts that
Mathlib does not yet provide and that this plan does not attempt to discharge
(Gaussian-case results are unconditional via Phase B-4 / C-4).
