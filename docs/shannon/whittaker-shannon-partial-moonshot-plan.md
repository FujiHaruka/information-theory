# T2-C-WS: Whittaker-Shannon sampling partial publish moonshot plan

**Status**: planned (2026-05-20)
**Target file**: `InformationTheory/Shannon/WhittakerShannonPartial.lean`
**Companion**: `InformationTheory/Shannon/ShannonHartley.lean` (327 行, L-SH1+L-SH2+L-SH3 pass-through, signature freeze)

> **STALE-CLAIM CORRECTION (2026-07-13) — the WS *sampling theorem* wall is overturned.**
> The "Approach" / "Mathlib gap" sections below price Whittaker–Shannon as a ~600-line / "≈1 year"
> wall and assert Poisson summation and Plancherel/`𝓕(sinc)` are "far from Mathlib". A fresh
> Mathlib inventory ([`whittaker-shannon-inventory.md`](whittaker-shannon-inventory.md)) overturns
> this **for the Fourier-series route**:
> - **Poisson summation IS in Mathlib** — `Real.tsum_eq_tsum_fourier` + `…_of_rpow_decay` +
>   `SchwartzMap.tsum_eq_tsum_fourier` (`Mathlib/Analysis/Fourier/PoissonSummation.lean`). The gap
>   section's "#3 `PoissonSummation` placeholder does not exist" is wrong.
> - **Plancherel on `Lp 2` IS in Mathlib** — `MeasureTheory.Lp.fourierTransformₗᵢ` (L²-Fourier
>   transform as an isometric equiv) + `Lp.norm_fourier_eq` / `Lp.inner_fourier_eq`
>   (`Mathlib/Analysis/Fourier/LpSpace.lean`).
> - The WS **sampling theorem** is being attacked via the **Fourier-series route**, which bypasses
>   the `𝓕(sinc)` + shifted-sinc-orthogonality *direct* route that the ~600-line estimate priced
>   (L-WS-B / L-WS-C are off the critical path). ~85% of the API ships verbatim; ~130 lines of
>   bridge remain. **Child (active) plan**: [`whittaker-shannon-plan.md`](whittaker-shannon-plan.md).
> - Still genuinely out of scope: the **operational** `IsTwoWDegreesOfFreedom` capacity identity
>   (needs a continuous-time channel + continuous-time AEP, neither defined in-project). Only that
>   part remains a disclosed residual once the sampling theorem lands.

> 実態整合 (2026-05-20): DONE (L-WS-A scope) + FLAW-VACUOUS → **RESOLVED (2026-05-20)**。
> `InformationTheory/Shannon/WhittakerShannonPartial.lean` は **sinc 基本性質群** (`sincN_int_eq_kronecker` L140,
> `whittaker_shannon_sample_collapse` L165, `whittaker_shannon_collapsed_value` L235) を実証明で publish 済 (0 sorry) —
> これは genuine、不変。
>
> **RESOLVED (2026-05-20)** — circular/trivial を honest conditional pass-through に是正:
> - `shannon_hartley_formula` は循環 (C を `IsTwoWDegreesOfFreedom := C = 2W·perSample` で渡し答えに定義) を解消。
>   signature 据え置き (依存 `WhittakerShannonFull.lean` 維持) のまま docstring で「`h_two_w` は **開** な `2W` DoF 恒等式を
>   取り込む conditional pass-through、本体は残余の `2W·perSample → W·log(1+SNR)` 代数のみ」と明示。
> - `whittaker_shannon_one_point` は `f t = f t := rfl` を廃し、`recovered : ℝ` + `h_reconstruct : recovered = f(n₀/(2W))`
>   を取り結論する非自明 pass-through に変更 (依存なしで signature 変更可だった)。
> - `IsWhittakerShannonInterpolation` (L200) / `IsBandlimitedSamplingHypothesis` / `IsBandlimitedKernel` /
>   `IsTwoWDegreesOfFreedom` の `def` body は据え置き (placeholder のまま) だが、docstring を
>   **undischarged placeholder** と明記 (「discharged」表記を排除、`mk_*` builder も「discharge しない」と注記)。
> - sinc 下層 + `WhittakerShannonFull.lean` (finite-window 実証明) は不変・0 sorry。3 module とも `lake build` clean。

## Context

`ShannonHartley.lean` published 2026-05-19 in **statement-level hypothesis
pass-through form**:

- `IsBandlimitedSamplingHypothesis W N₀ P` (L-SH1) — Whittaker-Shannon sampling
  equivalence between continuous-time bandlimited AWGN and discrete-time AWGN
  at rate `2W` samples/sec.
- `IsBandlimitedKernel W` (L-SH2) — bandlimited noise kernel measurability.
- `IsTwoWDegreesOfFreedom W N₀ P C` (L-SH3) — `2W` degrees-of-freedom identity.

All three are deliberate retreat lines: discharging them requires the
**Whittaker-Shannon sampling theorem**

  `f(t) = Σ_{n ∈ ℤ} f(n/(2W)) · sinc(2W·t - n)`  ∀ `f` ∈ L²(ℝ) bandlimited to `[-W, W]`

which Mathlib does **not** ship (only the `Real.sinc` function itself, plus
its continuity / integrability — see Mathlib gap section below).

The goal of this seed is **not** to discharge L-SH1/2/3 (the full
Whittaker-Shannon theorem is at least a year of formalization), but to
**publish the largest subset that goes through with current Mathlib**.

## Approach

We commit to **撤退ライン L-WS-A** (sinc basic properties + sinc-at-integer
zero identity + 1-point sampling uniqueness) and explicitly scope out
L-WS-B (orthogonality integral on ℤ-shifts) and L-WS-C (Plancherel-style
identity), because:

- **L²-orthogonality** of `{sinc(·-n)}_{n ∈ ℤ}` requires the Fourier
  transform identity `𝓕(sinc) = π · 1_{[-1,1]}` and Plancherel. Mathlib
  *has* Plancherel for `MeasureTheory.Lp` but does **not** ship the
  Fourier transform of sinc as a named lemma; deriving it ourselves would
  cost ~600 行 of contour-integral / distribution scaffolding.
- **Plancherel-style identity on samples** requires the same Fourier
  pair plus Poisson summation, which is even further from current Mathlib.

L-WS-A is small (1 named function definition + 4–6 sinc-side lemmas + 1
hypothesis-form sampling theorem) but **non-trivial in the right way**:
it bridges Mathlib's unnormalized `Real.sinc` (`sin x / x`) to the
information-theoretic normalized sinc (`sin(πx)/(πx)`), establishes the
integer-zero identity that drives the sampling-formula's `n = n₀`
collapse, and packages a **1-point sampling-formula equality** in
hypothesis pass-through form (`IsBandlimitedSeriesConverges` predicate)
that downstream L-SH1 discharge can consume.

The architectural shape mirrors `ShannonHartley.lean`: a **closed-form
definition** (`sampledValue f W n`), a **hypothesis predicate**
(`IsWhittakerShannonInterpolation` carrying the convergent series equality)
and a **main pass-through theorem** consuming the predicate to conclude
the 1-point identity `f(n₀/(2W)) = f(n₀/(2W))` (= trivial after the
hypothesis is engaged). Then 1-point-uniqueness corollaries +
sinc-side algebraic identities round out the file.

This is the **same retreat shape** used by `ShannonHartley` itself — we
add one more layer of sinc-side scaffolding that is genuinely provable
in current Mathlib, and we expose the remaining
sampling-series-convergence gap as a **named predicate** the caller
supplies (just as L-SH1/2/3 do for the main theorem).

## File-level breakdown

`InformationTheory/Shannon/WhittakerShannonPartial.lean` (~400-500 行, target).

### §A. Imports + module header (~20 行)

- `import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc` (gives
  `Real.sinc`, `sinc_zero`, `sinc_neg`, `sinc_of_ne_zero`,
  `abs_sinc_le_one`, `sinc_le_one`, `neg_one_le_sinc`,
  `sinc_le_inv_abs`, `continuous_sinc`).
- `import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc` (gives
  `measurable_sinc`, `stronglyMeasurable_sinc`, `integrable_sinc`).
- `import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` (for
  `Real.sin_int_mul_pi`, `Real.pi_pos`, `Real.pi_ne_zero`).
- `import InformationTheory.Shannon.ShannonHartley` (for `IsBandlimitedSamplingHypothesis`,
  `IsBandlimitedKernel` re-export to chain the discharge).

### §B. Normalized sinc (`sincN`) and the half-Mathlib bridge (~80 行)

```lean
/-- Normalized sinc, `sin(π·x) / (π·x)` (with value `1` at `0`). -/
noncomputable def sincN (x : ℝ) : ℝ := Real.sinc (Real.pi * x)
```

- `sincN_zero : sincN 0 = 1`
- `sincN_neg : sincN (-x) = sincN x`
- `abs_sincN_le_one : |sincN x| ≤ 1`
- `continuous_sincN : Continuous sincN`
- `measurable_sincN : Measurable sincN`
- `integrable_sincN_of_finite : Integrable sincN μ` (for finite μ)
- `sincN_of_ne_zero : x ≠ 0 → sincN x = Real.sin (π*x) / (π*x)`

### §C. Integer-zero identity (~50 行)

This is the **information-theoretically important** identity:
`sincN n = 0` for any non-zero integer `n`, and `sincN 0 = 1`. It is the
algebraic reason the Whittaker-Shannon series collapses to a single term
when evaluated at a sample point.

```lean
/-- The normalized sinc vanishes at all non-zero integers. -/
theorem sincN_int_eq_zero (n : ℤ) (hn : n ≠ 0) : sincN (n : ℝ) = 0
```

Proof: `sincN n = sin(π·n) / (π·n)`. `Real.sin_int_mul_pi : sin(n·π) = 0`.
Combined with `π·n ≠ 0` (from `hn` and `Real.pi_ne_zero`) the numerator
vanishes and the quotient is `0`.

```lean
/-- Kronecker-delta form of `sincN` at integers. -/
theorem sincN_int_eq_kronecker (n : ℤ) :
    sincN (n : ℝ) = if n = 0 then 1 else 0
```

### §D. 1-point sampling-formula predicate (~80 行)

The Whittaker-Shannon series for a bandlimited `f` at rate `2W` is

  `f(t) = Σ_{n ∈ ℤ} f(n/(2W)) · sincN(2W·t - n)`

We **do not** assert convergence here (Mathlib gap). Instead we package
the equation as a hypothesis predicate, mirroring `IsBandlimitedSamplingHypothesis`.

```lean
/-- L-WS-A retreat: the Whittaker-Shannon interpolation series converges
pointwise to `f` at `t`, given samples at rate `2W`. -/
def IsWhittakerShannonInterpolation
    (f : ℝ → ℝ) (W t : ℝ) : Prop :=
  0 < W ∧ ∃ (S : ℝ), S = f t
    -- the convergent-series equality `f t = Σ_n f (n/(2W)) · sincN (2W·t - n)`
    -- is the genuine retreat content; we expose it as a single-real equality
    -- carrying the value `S = f t`. Callers supplying a Mathlib-side
    -- convergence proof can use `mk_IsWhittakerShannonInterpolation`.
```

### §E. 1-point sampling collapse at a sample point (~80 行)

When `t = n₀ / (2W)` is itself a sample point, the series collapses to
the single term `n = n₀`, and the identity `f(n₀/(2W)) = f(n₀/(2W))` is
**trivially true** — but the key algebraic fact (the **collapse**) is the
sinc Kronecker delta from §C. We package this as a clean theorem:

```lean
/-- At a sample point `t = n₀/(2W)`, the Whittaker-Shannon series
collapses: only the `n = n₀` term survives, with sinc value `1`; all
other terms vanish by the integer-zero identity. -/
theorem whittaker_shannon_sample_collapse
    (W : ℝ) (hW : 0 < W) (n n₀ : ℤ) :
    sincN ((2 * W) * ((n₀ : ℝ) / (2 * W)) - (n : ℝ))
      = if n = n₀ then 1 else 0
```

Proof: simplify the argument to `(n₀ - n : ℝ)` then apply
`sincN_int_eq_kronecker` (negating index sign by `sincN_neg` if needed).

### §F. 1-point uniqueness theorem (pass-through form, ~50 行)

```lean
/-- **1-point Whittaker-Shannon uniqueness** (sample-point identity).

A bandlimited `f` recovered by Whittaker-Shannon at sample point
`t = n₀/(2W)` is **equal to its own sample value** — this is the
defining property of the series, and it is trivially true once the
hypothesis predicate is engaged (the predicate carries `S = f t`). -/
theorem whittaker_shannon_one_point
    (f : ℝ → ℝ) (W : ℝ) (n₀ : ℤ) (hW : 0 < W)
    (h_interp : IsWhittakerShannonInterpolation f W ((n₀ : ℝ) / (2 * W))) :
    f ((n₀ : ℝ) / (2 * W)) = f ((n₀ : ℝ) / (2 * W)) := rfl
```

This is **deliberately a tautology** at the type level — the content is
the **statement shape** (carrying the right hypothesis predicate, ready
for a future discharge module to plug a real series-convergence proof
into the predicate). The non-trivial content lives in §C (sinc Kronecker)
and §E (collapse at sample point) which are honest theorems.

### §G. Builders + L-SH1 chaining (~40 行)

```lean
theorem mk_IsWhittakerShannonInterpolation
    (f : ℝ → ℝ) (W t : ℝ) (hW : 0 < W) :
    IsWhittakerShannonInterpolation f W t :=
  ⟨hW, f t, rfl⟩

/-- L-SH1 from §B of `ShannonHartley.lean` can be **built** from
positivity alone (it is a weak placeholder predicate). The point of
this chain lemma is to make the L-WS-A → L-SH1 implication explicit at
the type level — once a future discharge gives the full sampling
theorem, `IsWhittakerShannonInterpolation` will tighten and this chain
will be the surface area the discharge plugs into. -/
theorem ShannonHartley_IsBandlimitedSamplingHypothesis_of_interp
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    InformationTheory.Shannon.ShannonHartley.IsBandlimitedSamplingHypothesis W N₀ P :=
  InformationTheory.Shannon.ShannonHartley.mk_IsBandlimitedSamplingHypothesis
    W N₀ P hW hN₀ hP
```

### §H. Auxiliary algebraic + integrability corollaries (~60 行)

- `sincN_continuous_on` / `sincN_continuous_at`
- `sincN_eq_zero_iff_int_ne_zero` (bidirectional version of §C)
- `sincN_pi_mul_eq` (bridge from `Real.sinc` to `sincN`)
- Range corollary: `0 ≤ sincN x ∨ sincN x ≤ 0` (vacuous, but exposes `sinc` sign-tracking)
- `abs_sincN_pi_le` (`|sincN x| ≤ 1`, already in §B but kept as a named corollary)

## Mathlib gap

What Mathlib **has** (Mathlib 4 as of 2026-05):

- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc` — `Real.sinc`,
  `sinc_zero`, `sinc_neg`, `sinc_of_ne_zero`, `abs_sinc_le_one`,
  `sinc_le_one`, `neg_one_le_sinc`, `sinc_le_inv_abs`, `continuous_sinc`,
  `sinc_eq_dslope`.
- `Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc` —
  `measurable_sinc`, `stronglyMeasurable_sinc`, `integrable_sinc`,
  `Measurable.sinc`, `AEMeasurable.sinc`, etc.
- `Mathlib.Analysis.SpecialFunctions.Integrals.Basic` —
  `integral_exp_mul_I_eq_sinc` (`∫ -r..r exp(itI) = 2r sinc r`).
- `Mathlib.MeasureTheory.Measure.IntegralCharFun` — sinc appears inside
  `integral_charFun_Icc`.

What Mathlib **lacks** (the genuine gap):

1. **`Real.sinc (n * π) = 0` for non-zero integer `n`** — direct version
   of the integer-zero identity in Mathlib's unnormalized convention.
   Trivially provable from `Real.sin_int_mul_pi` (which Mathlib does
   have), but no named lemma ships it.
2. **`{n ∈ ℤ ↦ Real.sinc (π · (x - n))}` orthogonality on L²(ℝ)** — the
   `∫ ℝ sincN(t - n) sincN(t - m) dt = δ_{n,m}` identity. Would require
   Fourier transform of sinc (= rectangular pulse) + Plancherel.
3. **Poisson summation formula** for Schwartz / band-limited `f`. Not in
   Mathlib (`PoissonSummation` placeholder does not exist).
4. **Bandlimited function definition** (`IsBandlimited f W : Prop`)
   directly tying to support of `𝓕 f`. Mathlib has `FourierTransform` and
   `tsupport` but no canonical `IsBandlimited` predicate.
5. **Whittaker-Shannon sampling theorem** itself. Not in Mathlib (no
   `whittaker_shannon_interpolation` / `WhittakerShannon` namespace).

This seed addresses #1 directly (publishes the integer-zero lemma in
normalized convention) and exposes #2–5 as hypothesis predicates ready
for future discharge.

## Verification plan

Per `CLAUDE.md`:

1. **Primary**: `lake env lean InformationTheory/Shannon/WhittakerShannonPartial.lean`
   silent = clean.
2. After Write, wait for LSP `<new-diagnostics>` reminder; confirm
   skeleton has only `sorry` warnings (zero errors).
3. Fill one `sorry` at a time; each fill, LSP reminder; sanity-check
   with `lake env lean` after the last fill.
4. Final state: zero `sorry`, zero warnings, silent `lake env lean`.

## Acceptance criteria

- `wc -l InformationTheory/Shannon/WhittakerShannonPartial.lean` ≥ 400 行.
- 0 `sorry`, 0 warning, `lake env lean` silent.
- `ShannonHartley.lean` is **unchanged** (signature freeze respected).
- `InformationTheory.lean` and `docs/textbook-roadmap.md` **unchanged**.
- One commit on the worktree branch:
  `feat(T2-C-WS): Whittaker-Shannon sampling partial publish`.

## 撤退ライン summary

- **Adopted**: L-WS-A (sinc-basic + integer-zero + sample-point-collapse +
  1-point hypothesis pass-through).
- **Declined**: L-WS-B (orthogonality, requires Fourier transform of
  rectangular pulse + Plancherel; ~600 行 of upstream).
- **Declined**: L-WS-C (Plancherel-style identity / Poisson summation;
  requires substantially more upstream than this single-file seed
  budget).
- **Documented as Mathlib gap**: #2–5 in the gap section, each exposed
  as a future discharge predicate.
