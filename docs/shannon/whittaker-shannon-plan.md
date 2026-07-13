# Shannon: Whittaker–Shannon sampling theorem sub-plan

> **Parent**: [`whittaker-shannon-partial-moonshot-plan.md`](whittaker-shannon-partial-moonshot-plan.md) §撤退ライン (L-WS-B/L-WS-C overturn)

**Status**: planned (2026-07-13)
**Target file**: `InformationTheory/Shannon/WhittakerShannon.lean` (new)
**Inventory (technical spec, do not duplicate)**: [`whittaker-shannon-inventory.md`](whittaker-shannon-inventory.md)
**Reuses**: `InformationTheory/Shannon/NormalizedSinc.lean` (`sincN` + 13 decls, 0 sorry)

## Scope line (critical)

- **In scope / provable (this plan's target):** the Whittaker–Shannon **sampling theorem**
  itself — the mathematical core of "2W degrees of freedom". Primary deliverable is the
  self-contained per-`t` `HasSum` (inventory statement (ii)): **unconditional**, over an L²
  spectrum `F : Lp ℂ 2 (haarAddCircle (T:=1))`. Stretch: the real-line band-limited textbook
  wrapper (statement (i)), which only adds Fourier-inversion glue.
- **Out of scope / documented residual (stays):** the *operational capacity* identity
  `IsTwoWDegreesOfFreedom : C = 2W · perSampleAwgnCapacity` in `ShannonHartley.lean`. It needs a
  continuous-time channel model + continuous-time AEP / channel-coding theorem, **neither of which
  exists in the project** (no continuous-time channel is even defined). Genuinely far, honestly
  disclosed. Note: once the sampling theorem below is proved, that residual is scoped down to
  **only** the AEP / operational part — it no longer bundles the false claim "the sampling theorem
  is a Mathlib wall" (the roadmap's `nyquist-2w-dof` wall framing).

## Context

The roadmap scoped out "Ch.9 Nyquist 2W-DOF" as a genuine mathematical wall, pricing
Whittaker–Shannon at ~600 lines / "≈1 year". Independent recon + the inventory **overturn** this
for the **Fourier-series route**: L² Fourier series on `AddCircle`, the boxcar→sinc integral,
the L²-`HasSum`↔inner interchange, Plancherel on `Lp 2`, and Poisson summation are **all now in
Mathlib**. The parent plan's stale claims (Poisson/Plancherel "far from Mathlib") are corrected in
its 2026-07-13 note. ~85% of the API is shipped verbatim; only ~3 bridge lemmas (~130 lines total)
are self-built. The old ~600-line estimate priced the *direct* route (`𝓕(sinc)=1_[-1/2,1/2]` +
shifted-sinc L²-orthogonality); the Fourier-series route bypasses both — sinc appears only as the
boxcar integral `∫_{-1/2}^{1/2} e^{2πiξs} dξ = sincN s`, itself a Mathlib lemma.

## Approach

The Fourier-series route, per-`t`, in `HasSum` form (no `𝓕(sinc)`, no orthogonality, no Poisson):

- Land the spectrum `F` as a circle-L² element `F : Lp ℂ 2 (haarAddCircle (T:=1))` — a band-limited
  `𝓕 f` restricted to `[-1/2,1/2]` *is* exactly such an element (crux plumbing:
  `MemLp.memLp_liftIoc` → `.haarAddCircle` → `.toLp`; `T=1` so haar = volume, mass 1).
- Take the L² Fourier series of `F` on the circle: `hasSum_fourier_series_L2 F` gives
  `HasSum (fun n => fourierCoeff F n • fourierLp 2 n) F` (**crux #1**, verbatim).
- Push the *fixed bounded functional* `⟪wsExp t, ·⟫` through that `HasSum` via
  `ContinuousLinearMap.hasSum` / `HasSum.mapL` with `innerSL ℂ (wsExp t)` (**crux #2**, a 3-liner)
  — a continuous linear map preserves `HasSum`.
- Each monomial pairing collapses to a boxcar integral = normalized sinc:
  `⟪wsExp t, fourierLp 2 n⟫ = ∫_{-1/2}^{1/2} e^{2πiξ(t+n)} dξ = sincN (t+n)`
  (via `integral_exp_mul_I_eq_sinc` + `integral_comp_mul_left`, **crux #3**).
- Each coefficient is a sample: `fourierCoeff F n = ⟪fourierLp 2 n, F⟫ = wsSignal F (-n)`
  (via `fourierBasis_repr` + an `integral_congr_ae` sign match, since `conj (wsExp(-n) ξ)=fourier n ξ`).
- Reindex `n ↦ -n` by the `HasSum` reindex `Equiv.neg ℤ` (**not** a `tsum` relabel) to land the
  textbook summand `wsSignal F m • sincN (t - m)`.

Statement shape is chosen Mathlib-shape-driven: `hasSum_fourier_series_L2` returns a `HasSum` and
`ContinuousLinearMap.hasSum` preserves it, so the WS conclusion is a `HasSum` (not a `tsum`
equality nor an `‖·‖→0` limit) — no reshaping bridge needed.

## 進捗

- [x] M0 — Mathlib API inventory ✅ → [`whittaker-shannon-inventory.md`](whittaker-shannon-inventory.md)
- [ ] Phase 1 — skeleton (5 decls + `sorry`, type-checks) 📋
- [ ] Phase 2 — `wsExp` + the two bridges (decls 1–3) 📋
- [ ] Phase 3 — headline assembly `whittaker_shannon_hasSum` (the honest core) 📋
- [ ] Phase 4 — (stretch) textbook wrapper `whittaker_shannon_bandlimited` (statement (i)) 📋

## Decomposition table

Skeleton + fill order = `wsExp → inner_wsExp_fourierLp → fourierCoeff_eq_wsSignal →
whittaker_shannon_hasSum → (wrapper)`. Verbatim signatures + typeclass contexts live in the
inventory §A–H; do not re-derive here.

| Decl | What it proves | Dominating Mathlib lemma(s) | Self-build LOC | Risk / pitfall |
|---|---|---|---|---|
| `wsExp t` (def) | the kernel `ξ ↦ e^{-2πiξt}` as an `Lp ℂ 2 (haarAddCircle 1)` element | bounded ⇒ `MemLp` on finite measure; `MemLp.haarAddCircle`; `.toLp` | ~15 | **conjugation slot**: `⟪·,·⟫` is conj-linear in slot 1, so define `wsExp t ξ = e^{-2πiξt}` (`conj = e^{+2πiξt}`); a sign flip silently reindexes the whole series. `haarAddCircle` vs `volume`; `Ioc` (half-open), not `Icc`/`Ioo`. |
| `inner_wsExp_fourierLp` | step-4 bridge: `⟪wsExp t, fourierLp 2 n⟫ = sincN (t+n)` | `integral_exp_mul_I_eq_sinc` + `intervalIntegral.integral_comp_mul_left` + `L2.inner_def` + `integral_liftIoc_eq_intervalIntegral` | ~30 | `2r` prefactor cancels the `1/(2π(t+n))` Jacobian; the `t+n=0` branch needs `sinc_zero` (value 1). Template: mirror `integral_charFun_Icc`'s proof almost verbatim. |
| `fourierCoeff_eq_wsSignal` | step-3 bridge: `fourierCoeff F n = wsSignal F (-n)` | `fourierBasis_repr` + `fourierCoeff_eq_intervalIntegral` + `fourier_coe_apply` (`T=1`) + `integral_congr_ae` | ~40 | sign of `n` in `fourier (-n)` inside `fourierCoeff` vs the sign in `wsExp`; mostly an a.e.-congruence + `T=1` rewrite. |
| `whittaker_shannon_hasSum` (**headline core**) | `HasSum (fun n:ℤ => wsSignal F n • sincN (t-n)) (wsSignal F t)`, unconditional | `hasSum_fourier_series_L2` + `ContinuousLinearMap.hasSum`/`HasSum.mapL` + `innerSL`/`innerSL_apply_apply` + `inner_smul_right` + `Equiv.neg ℤ` | ~30 (assembly) | reindex must be a `HasSum` reindex along `Equiv.neg ℤ`, **not** a `tsum` relabel. `sincN` evenness (`sincN_neg`) is **not** among the 13 published `NormalizedSinc` decls — derivable from `Real.sinc_neg` in ~2 lines if the reindex needs it (direct `t+(-m)=t-m` substitution may avoid it). |
| `whittaker_shannon_bandlimited` (**stretch, statement (i)**) | real-line form: for `f` continuous/integrable/band-limited, `HasSum (fun n => f n • sincN (t-n)) (f t)` | `Continuous.fourierInv_fourier_eq` (or `Integrable.fourierInv_fourier_eq`) + support→`setIntegral` restriction + `MemLp.memLp_liftIoc` | ~60 | `Integrable (𝓕 f)` is a **genuine precondition** (band-limited ⇒ compact support ⇒ integrable), a regularity hyp — NOT the theorem's core, so it is not hypothesis bundling. All typeclasses on `V=ℝ`, `E=ℂ` are instances. This is the retreat surface. |

Aggregate self-build ≈ **130 lines** (core, statement (ii)) or ≈ **190 lines** (with wrapper),
vs the roadmap's ~600. No step is ABSENT (inventory verdict table: 3/6 present verbatim, 3 partial).

## Phase detail

### M0 — inventory ✅ (done)
The Mathlib API inventory is complete: [`whittaker-shannon-inventory.md`](whittaker-shannon-inventory.md).
proof-log: no.

### Phase 1 — skeleton 📋
Write `InformationTheory/Shannon/WhittakerShannon.lean` from the inventory's starting skeleton
(imports + namespace + the 5 decls with `sorry` bodies, each carrying
`@residual(plan:whittaker-shannon)`). Register the import in `InformationTheory.lean`. Confirm
type-checks with `sorry` warnings only (`lake env lean`). proof-log: no.

### Phase 2 — `wsExp` + bridges (decls 1–3) 📋
Fill `wsExp`, `inner_wsExp_fourierLp`, `fourierCoeff_eq_wsSignal` in order. This is the
reshaping-risk zone (measure/conjugation/sign traps in the table). proof-log: **yes** (record
each bridge's actual Mathlib call chain — the sign/measure conventions are the likely-drift part).

### Phase 3 — headline assembly `whittaker_shannon_hasSum` 📋
Assemble crux #1 + #2 + the two bridges + the `Equiv.neg ℤ` reindex. This is the honest core =
proof-done target. proof-log: **yes**.

### Phase 4 — (stretch) wrapper `whittaker_shannon_bandlimited` 📋
Reduce statement (i) to (ii) with `F := 𝓕 f` restricted to `[-1/2,1/2]` as a circle-L² element,
via `Continuous.fourierInv_fourier_eq` + the support hypothesis. proof-log: **yes**.

## Retreat line

The honest exit if the full `HasSum` stalls:

- **Stall in Phase 2/3 (core):** publish `wsExp` + whichever bridges are done, leave
  `whittaker_shannon_hasSum`'s body as `sorry` + `@residual(plan:whittaker-shannon)`.
- **Core done, wrapper stalls (Phase 4):** publish the self-contained `whittaker_shannon_hasSum`
  (statement (ii)) and leave `whittaker_shannon_bandlimited` (statement (i)) as `sorry` +
  `@residual(plan:whittaker-shannon)`.

This is **`@residual(plan:whittaker-shannon)`, NOT a `wall:` tag** — the inventory's wall
enumeration (§ "Enumeration of Mathlib walls") confirms **no loogle-0 proposition** underlies any
remaining piece (`Bandlimited`/`PaleyWiener`/`WhittakerShannon`/`cardinalSeries` are naming gaps,
not analytic walls; every bridge is provable). **No load-bearing hypothesis bundling**: statement
(ii) is unconditional over `F : Lp ℂ 2 (haarAddCircle 1)` — there is no `*Hypothesis` predicate
carrying the core, and statement (i)'s `Integrable (𝓕 f)` / support hyps are regularity
preconditions (see table).

## Residual slug

The residual slug for this work is **`@residual(plan:whittaker-shannon)`**, and **this file
(`docs/shannon/whittaker-shannon-plan.md`)** is its referent (filename stem = slug, kebab-case).
Every `sorry` written under this plan carries that tag; a new independent honesty audit is
launched when the first such `sorry` is committed (orchestrator-mandatory).

## Definition of Done

- **proof-done (this attack's completion):** `whittaker_shannon_hasSum` (statement (ii)) is
  `sorry`-free and `#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free),
  passed by an independent honesty audit (`@audit:ok`).
- **stretch:** the textbook wrapper `whittaker_shannon_bandlimited` (statement (i)) also sorryAx-free
  + audited.
- **not in scope:** the operational `IsTwoWDegreesOfFreedom` capacity identity (see Scope line) —
  remains a disclosed residual; this plan does not close it.

## 判断ログ

1. **Route选択 = Fourier-series, not direct.** The direct route (`𝓕(sinc)` + shifted-sinc
   L²-orthogonality) is what the ~600-line/1-year estimate priced. The inventory shows the
   Fourier-series route never forms `𝓕(sinc)`; sinc emerges from the boxcar integral
   (`integral_exp_mul_I_eq_sinc`, shipped). Parent retreat lines L-WS-B/L-WS-C do **not** gate
   this route.
2. **Statement (ii) is the honest core, stated unconditionally over a circle-L² element** (not the
   real-line `𝓕`-support form). This avoids inventing an `IsBandlimited` predicate (Mathlib has
   none) and keeps the core free of any load-bearing hypothesis; the real-line wrapper (i) is the
   stretch that reintroduces support hyps as regularity preconditions.
