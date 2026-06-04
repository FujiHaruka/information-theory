# Proof log — EPI G2 (α) upper bound, klFun-Fatou KL-LSC route

File: `InformationTheory/Shannon/EPIG2KLFatouLSC.lean`
Inventory: `docs/shannon/epi-g2-alpha-klfun-fatou-inventory.md`
Parent plan: `docs/shannon/epi-g2-general-sandwich-moonshot-plan.md` (Phase 2 = (α))
Date: 2026-06-05

## Outcome

W1–W4 + 2 cross-term helpers (`log_gaussianPDFReal_zero`, `cross_term_closed_form`,
`pX_cross_term_expand`) all **genuine, sorryAx-free** (`[propext, Classical.choice,
Quot.sound]`, machine-checked). Assembly `negMulLog_convDensity_limsup_le` parked in its
honest target form with one `sorry` + `@residual(wall:kl-lower-semicontinuous)` (inherited
slug). The route's heart (KL lower-semicontinuity via klFun-Fatou) is genuinely closed —
no DV dual needed. The wall surface shrinks from "DV dual hard direction" to "bridge
precondition plumbing".

## W2 — rnDeriv withDensity quotient (the inventory's predicted largest gap)

The inventory flagged the a.e. base measure (volume vs γ) as "事故源 #1". Confirmed:

- `rnDeriv_withDensity_right μf volume` returns `=ᵐ[volume]` (base = volume, NOT γ).
- `Measure.rnDeriv_withDensity volume hF` collapses the left withDensity, also `=ᵐ[volume]`.
- The combine step is all on `=ᵐ[volume]` (no base mismatch there).
- Transfer to `=ᵐ[γ]` is the only base switch. **The direction caught me once**:
  `AbsolutelyContinuous.ae_eq (h : μ ≪ ν) (h' : _ =ᵐ[ν] _) : _ =ᵐ[μ]`. To go
  `=ᵐ[volume] ⟹ =ᵐ[γ]` you need `γ ≪ volume` (`withDensity_absolutelyContinuous`), NOT
  `volume ≪ γ`. The inventory suggested `volume ≪ γ` + `AbsolutelyContinuous.ae_eq` which
  is the wrong direction — `ae_eq` transfers FROM the `≪`-larger base. First LSP error
  caught it immediately; 1-line fix. SigmaFinite was automatic (`withDensity.instSigmaFinite`
  is an instance); `IsFiniteMeasure` via `isFiniteMeasure_withDensity_ofReal hf_int.2`.

## W1 — Fatou assembly

Clean. `klDiv_eq_lintegral_klFun_of_ac` rewrites both sides to `∫⁻ ofReal (klFun ...) ∂γ`;
the pointwise `G x ≤ liminf (F n x)` is just `(tendsto).liminf_eq.ge` (the limit equals the
liminf for a convergent sequence, hence `≤`); Fatou `lintegral_liminf_le` closes it. The
pseudo-Lean's `le_liminf` ended up being `Tendsto.liminf_eq.ge`, cleaner than the
`le_liminf_of_le` route the inventory suggested. Each `F n` measurability:
`(measurable_klFun.comp ((μ_n n).measurable_rnDeriv γ).ennreal_toReal).ennreal_ofReal`.

## W3 — cross-term (no surprises, numbers verbatim-checked)

Per CLAUDE.md numeric-verbatim rule: read `gaussianPDFReal` def
(`(√(2πv))⁻¹ · exp(-(x-μ)²/(2v))`) before writing `log_gaussianPDFReal_zero`. The closed
form `log g x = -log(√(2πσ²)) - x²/(2σ²)` then drops out of `log_mul` + `log_inv` +
`log_exp` + `ring`. Cross-term is affine in `t` via `convDensityAdd_second_moment` +
`convDensityAdd_pXpY_integral_eq` + `integral_gaussianPDFReal_eq_one`; `t → 0` limit is a
mechanical `Tendsto.sub/const_mul/const_add`. `(v:ℝ) > 0` from `v ≠ 0` (NNReal) needed
`pos_iff_ne_zero` + cast (positivity does not derive strict positivity from `≠ 0`).

## W4 — density a.e. subseq

Literal copy of `EPIVitaliAE.negMulLog_convDensity_tendsto_ae_subseq` with the final
`negMulLog`-composition `filter_upwards` removed. The `open
InformationTheory.Shannon.EPIConvDensity` is required in *this* file for the bare
`convDensityAdd` to resolve in statements (not brought in by `open
InformationTheory.Shannon` alone).

## Assembly (parked)

Honest signature in density/limsup target form. Remaining work is precondition plumbing for
the genuine bridge `klDiv_toReal_eq_neg_differentialEntropy_sub_cross`: discharging equal
mass / two-way absolute continuity / `log p`,`log q` integrability for the smoothed-density
family `μ_n` and for `μ = pX`, plus ℝ≥0∞→toReal conversion (`klDiv μ γ ≠ ∞`) and
subsequence→full promotion (`tendsto_of_subseq_tendsto`, confirmed to exist at
`Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean:138`). No Mathlib wall.

## grep/loogle misses

- `tendsto_of_subseq_tendsto` (bare) → loogle "unknown identifier", correct name
  `Filter.tendsto_of_subseq_tendsto`.
- `rnDeriv_withDensity` (bare in Mathlib) lives in `Decomposition/Lebesgue.lean:590` (not
  `RadonNikodym.lean` as one might guess); `rnDeriv_withDensity_right` is in `RadonNikodym.lean:168`.
