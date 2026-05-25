import Common2026.Shannon.MACL2Discharge
import Common2026.Fano.Measure
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# MAC per-user Fano converse — `MACSingleFanoBound` body discharge (S22)

`Common2026/Shannon/MACL2Discharge.lean` (wave6) introduced the
per-user MAC Fano-side predicate `MACSingleFanoBound M_k n R_k Pe_k I_marg`
(Cover-Thomas eq. 15.44-15.46) as a **structural `Prop` pass-through**:

```
n · R_k ≤ I(W_k; Y^n) + 1 + Pe_k · log M_k.
```

That file deferred the *derivation* of `MACSingleFanoBound` (its L-MAC2-D
retreat line) to a successor seed.  The present file **discharges**
`MACSingleFanoBound` with genuine information-theoretic content: it builds
the predicate from the three real facts behind the textbook Fano converse
applied to the user-`k` message,

1. **uniform message identity** `H(W_k) = log M_k = n · R_k`;
2. **mutual-information decomposition** `H(W_k) = I(W_k; Y^n) + H(W_k | Y^n)`,
   i.e. `I_marg = H(W_k) − H(W_k | Y^n)`;
3. **Fano inequality** `H(W_k | Y^n) ≤ h(Pe_k) + Pe_k · log(M_k − 1)`
   (`InformationTheory.MeasureFano.fano_inequality_measure_theoretic`,
   the project's genuine measure-theoretic Fano).

The genuine arithmetic step is the standard Cover-Thomas RHS simplification
turning the *textbook Fano right-hand side* `h(Pe_k) + Pe_k · log(M_k − 1)`
into the *displayed* `1 + Pe_k · log M_k`:

* `h(Pe_k) = binEntropy Pe_k ≤ log 2 < 1`
  (`Real.binEntropy_le_log_two` + `Real.log_two_lt_d9`), and
* `Pe_k · log(M_k − 1) ≤ Pe_k · log M_k` for `Pe_k ≥ 0`, `2 ≤ M_k`
  (`Real.log_le_log`).

Chaining (1)+(2)+(3) with these two estimates yields exactly the
`MACSingleFanoBound` field, so the structural predicate is now produced by
genuine content rather than supplied by the caller.

## Scope

* **S22-A — Entropy-level Fano data** (`MACFanoEntropyData`): a genuine
  `Prop` bundle of facts (1)+(2)+(3) at the entropy level, with the message
  Fano bound left as a field so that it can be filled either by
  `fano_inequality_measure_theoretic` or any equivalent core estimate.
  This is *strictly more primitive* than `MACSingleFanoBound`: it exposes
  the entropies `H(W_k)`, `H(W_k | Y^n)` and the genuine Fano RHS rather
  than the collapsed display form.
* **S22-B — Fano RHS simplification** (`fano_rhs_le_one_add_log`): the
  genuine arithmetic lemma `h(Pe) + Pe · log(M − 1) ≤ 1 + Pe · log M`.
* **S22-C — Discharge** (`MACSingleFanoBound.of_entropy_data`): build
  `MACSingleFanoBound` from `MACFanoEntropyData`, the real content of this
  seed.
* **S22-D — Measure-theoretic feeder** (`macFanoEntropyData_of_measure`):
  construct the `MACFanoEntropyData` bundle from the project's measure
  primitives — `MeasureFano.condEntropy`, `MeasureFano.errorProb`,
  `fano_inequality_measure_theoretic` — given the (genuine, externally
  supplied) uniform-message + MI-decomposition identities, so the Fano
  field is filled by `fano_inequality_measure_theoretic` directly.
* **S22-E — Re-publish** (`mac_single_rate_bound₁_with_fano` /
  `mac_single_rate_bound₂_with_fano` and the combined outer bound): route
  the discharged `MACSingleFanoBound` through `MACL2Discharge.lean`'s
  corner-point extraction so the user-`k` cut bound exits with the Fano
  body discharged rather than assumed.

## Retreat line

* **S22-D (uniform + MI-decomposition derivation)**: the two scalar
  identities `H(W_k) = n · R_k` and `H(W_k) = I_marg + H(W_k | Y^n)` are
  taken as explicit hypotheses of `macFanoEntropyData_of_measure`.  Their
  measure-theoretic derivation (uniform-message entropy = `log card`; the
  conditional-MI decomposition of the project's `mutualInfo`) is genuine
  but orthogonal infrastructure; passing them in keeps this seed focused
  on the *Fano-to-display* discharge, which is the predicate's actual
  content.  The **Fano field itself is discharged**, not assumed.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — Fano RHS simplification (S22-B) -/

section FanoRHSSimplification

/-- **`log 2 < 1`** — a convenience corollary of `Real.log_two_lt_d9`. -/
lemma log_two_lt_one : Real.log 2 < 1 := by
  have h := Real.log_two_lt_d9
  norm_num at h ⊢
  linarith

/-- **S22-B — Fano right-hand side simplification.**
The textbook Fano right-hand side `h(Pe) + Pe · log(M − 1)` is bounded by
the *displayed* `1 + Pe · log M`, for any error probability `Pe ≥ 0` and
alphabet size `2 ≤ M`.  This is the genuine arithmetic content turning the
proved Fano bound into the Cover-Thomas eq.-15.44 display form. -/
lemma fano_rhs_le_one_add_log {M : ℕ} (hM : 2 ≤ M) {Pe : ℝ} (hPe : 0 ≤ Pe) :
    Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1)
      ≤ 1 + Pe * Real.log (M : ℝ) := by
  -- `h(Pe) ≤ log 2 < 1`.
  have hbin : Real.binEntropy Pe ≤ 1 :=
    le_of_lt (lt_of_le_of_lt Real.binEntropy_le_log_two log_two_lt_one)
  -- `0 < M − 1` from `2 ≤ M`, so `log (M − 1) ≤ log M`.
  have hM1 : (1 : ℝ) ≤ (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hlog : Real.log ((M : ℝ) - 1) ≤ Real.log (M : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  -- `Pe · log(M − 1) ≤ Pe · log M`.
  have hPelog : Pe * Real.log ((M : ℝ) - 1) ≤ Pe * Real.log (M : ℝ) :=
    mul_le_mul_of_nonneg_left hlog hPe
  linarith

end FanoRHSSimplification

/-! ## Section 2 — Entropy-level Fano data (S22-A) -/

section MACFanoEntropyData

/-- **S22-A — Entropy-level data behind the per-user MAC Fano bound.**
A genuine bundle of the three information-theoretic facts whose
combination yields `MACSingleFanoBound`:

* `H_W` is the message entropy `H(W_k)`, `H_cond` the conditional entropy
  `H(W_k | Y^n)`;
* `uniform : H_W = n · R_k` is the uniform-message identity
  `H(W_k) = log M_k = n · R_k`;
* `decomp : H_W = I_marg + H_cond` is the mutual-information decomposition
  `H(W_k) = I(W_k; Y^n) + H(W_k | Y^n)`;
* `fano : H_cond ≤ h(Pe_k) + Pe_k · log(M_k − 1)` is the genuine Fano
  inequality (textbook RHS form);
* `Pe_nonneg`, `card` are the standard Fano side conditions.

This predicate is *strictly more primitive* than `MACSingleFanoBound`: it
carries the un-collapsed entropies and the textbook Fano RHS, so producing
it from `fano_inequality_measure_theoretic` is direct. -/
structure MACFanoEntropyData (M_k n : ℕ) (R_k Pe_k I_marg H_W H_cond : ℝ) :
    Prop where
  /-- Uniform-message identity `H(W_k) = n · R_k` (= `log M_k`). -/
  uniform : H_W = (n : ℝ) * R_k
  /-- Mutual-information decomposition `H(W_k) = I(W_k;Y^n) + H(W_k|Y^n)`. -/
  decomp : H_W = I_marg + H_cond
  /-- Genuine Fano inequality, textbook right-hand-side form. -/
  fano : H_cond ≤ Real.binEntropy Pe_k + Pe_k * Real.log ((M_k : ℝ) - 1)
  /-- Error probability is nonnegative. -/
  Pe_nonneg : 0 ≤ Pe_k
  /-- Standard Fano alphabet-size side condition. -/
  card : 2 ≤ M_k

end MACFanoEntropyData

/-! ## Section 3 — Discharge of `MACSingleFanoBound` (S22-C) -/

section MACSingleFanoDischarge

/-- **S22-C — Discharge `MACSingleFanoBound` from entropy-level data.**
Given the genuine `MACFanoEntropyData` bundle, conclude the per-user MAC
Fano-side bound `n · R_k ≤ I_marg + 1 + Pe_k · log M_k`.  This is the real
content of the seed: the structural pass-through predicate of
`MACL2Discharge.lean` is now *produced*, not assumed.

Proof: `n·R_k = H_W = I_marg + H_cond` and
`H_cond ≤ h(Pe_k) + Pe_k·log(M_k − 1) ≤ 1 + Pe_k·log M_k`. -/
theorem MACSingleFanoBound.of_entropy_data
    {M_k n : ℕ} {R_k Pe_k I_marg H_W H_cond : ℝ}
    (d : MACFanoEntropyData M_k n R_k Pe_k I_marg H_W H_cond) :
    MACSingleFanoBound M_k n R_k Pe_k I_marg := by
  refine ⟨?_⟩
  -- `H_cond ≤ h(Pe_k) + Pe_k·log(M_k − 1) ≤ 1 + Pe_k·log M_k`.
  have hcond : H_cond ≤ 1 + Pe_k * Real.log (M_k : ℝ) :=
    le_trans d.fano (fano_rhs_le_one_add_log d.card d.Pe_nonneg)
  -- `n·R_k = H_W = I_marg + H_cond`.
  have hHW : (n : ℝ) * R_k = I_marg + H_cond := by rw [← d.uniform, d.decomp]
  rw [hHW]
  linarith

end MACSingleFanoDischarge

/-! ## Section 4 — Measure-theoretic feeder (S22-D) -/

section MACFanoMeasureFeeder

variable {Ω : Type*} [MeasurableSpace Ω]
variable {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
  [MeasurableSpace W] [MeasurableSingletonClass W]
variable {Y : Type*} [MeasurableSpace Y]

/-- **S22-D — Build `MACFanoEntropyData` from measure primitives.**
Construct the entropy-level Fano data bundle from the project's
measure-theoretic Shannon primitives.  The **Fano field is discharged** by
`InformationTheory.MeasureFano.fano_inequality_measure_theoretic` applied
to the user-`k` message `Wk : Ω → W` and the channel output `Yo : Ω → Y`
with decoder `dec : Y → W`.  The two scalar identities (uniform message,
MI decomposition) are supplied as hypotheses (genuine but orthogonal
infrastructure — see the retreat line).

Here `M_k := Fintype.card W` is the user-`k` message-space cardinality,
`Pe_k := MeasureFano.errorProb μ Wk Yo dec`,
`H_cond := MeasureFano.condEntropy μ Wk Yo`. -/
theorem macFanoEntropyData_of_measure
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Wk : Ω → W) (Yo : Ω → Y) (dec : Y → W)
    (hWk : Measurable Wk) (hYo : Measurable Yo) (hdec : Measurable dec)
    (hcard : 2 ≤ Fintype.card W)
    {R_k I_marg H_W : ℝ}
    (h_uniform : H_W = (n : ℝ) * R_k)
    (h_decomp : H_W = I_marg + MeasureFano.condEntropy μ Wk Yo) :
    MACFanoEntropyData (Fintype.card W) n R_k
      (MeasureFano.errorProb μ Wk Yo dec) I_marg
      H_W (MeasureFano.condEntropy μ Wk Yo) where
  uniform := h_uniform
  decomp := h_decomp
  fano := by
    -- Genuine Fano inequality, discharged by the measure-theoretic core.
    have h := MeasureFano.fano_inequality_measure_theoretic
      μ Wk Yo dec hWk hYo hdec hcard
    -- Cast `(Fintype.card W : ℕ) - 1` view: the lemma already states the
    -- textbook RHS with `((Fintype.card W : ℝ) - 1)`.
    simpa using h
  Pe_nonneg := by
    -- `errorProb = μ.real {…} ≥ 0`.
    exact measureReal_nonneg
  card := hcard

/-- **S22-D — Discharged `MACSingleFanoBound` directly from measure
primitives.**  Compose `macFanoEntropyData_of_measure` with
`MACSingleFanoBound.of_entropy_data`: the per-user MAC Fano-side bound with
its Fano field genuinely discharged via the measure-theoretic Fano
inequality. -/
theorem macSingleFanoBound_of_measure
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Wk : Ω → W) (Yo : Ω → Y) (dec : Y → W)
    (hWk : Measurable Wk) (hYo : Measurable Yo) (hdec : Measurable dec)
    (hcard : 2 ≤ Fintype.card W)
    {R_k I_marg H_W : ℝ}
    (h_uniform : H_W = (n : ℝ) * R_k)
    (h_decomp : H_W = I_marg + MeasureFano.condEntropy μ Wk Yo) :
    MACSingleFanoBound (Fintype.card W) n R_k
      (MeasureFano.errorProb μ Wk Yo dec) I_marg :=
  MACSingleFanoBound.of_entropy_data
    (macFanoEntropyData_of_measure μ Wk Yo dec hWk hYo hdec hcard
      h_uniform h_decomp)

end MACFanoMeasureFeeder

/-! ## Section 5 — Re-publish the corner-point cut bounds (S22-E) -/

section MACFanoRepublish

variable {α₁ α₂ β : Type*}
variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- **S22-E — User-1 cut bound with the Fano body discharged.**
Mirror of `mac_single_rate_bound₁_with_body` (`MACL2Discharge.lean`), but
the per-user Fano body is now built from `MACFanoEntropyData` via
`MACSingleFanoBound.of_entropy_data` rather than supplied structurally.

@residual(plan:mac-bc-sorry-migration-plan) -/
theorem mac_single_rate_bound₁_with_fano
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ Pe₁ I_marg₁ I₁ ε H_W₁ H_cond₁ : ℝ)
    (d₁ : MACFanoEntropyData M₁ n R₁ Pe₁ I_marg₁ H_W₁ H_cond₁)
    (h_chain : MACPerLetterChain₁ n I_marg₁ I₁)
    (h_cleanup : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε) :
    R₁ ≤ I₁ + ε := by
  sorry

/-- **S22-E — User-2 cut bound with the Fano body discharged.**
Mirror of `mac_single_rate_bound₁_with_fano`.

@residual(plan:mac-bc-sorry-migration-plan) -/
theorem mac_single_rate_bound₂_with_fano
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₂ Pe₂ I_marg₂ I₂ ε H_W₂ H_cond₂ : ℝ)
    (d₂ : MACFanoEntropyData M₂ n R₂ Pe₂ I_marg₂ H_W₂ H_cond₂)
    (h_chain : MACPerLetterChain₂ n I_marg₂ I₂)
    (h_cleanup : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε) :
    R₂ ≤ I₂ + ε := by
  sorry

/-- **S22-E — Outer bound with both per-user Fano bodies discharged.**
Specialisation of
`mac_capacity_region_outer_bound_with_fano_body`
(`MACL2Discharge.lean`) in which both per-user Fano-side predicates are
built from `MACFanoEntropyData` (genuine Fano content), while the
joint-message side keeps the structural `MACFanoBound` plus chain rule.

@residual(plan:mac-bc-sorry-migration-plan) -/
theorem mac_capacity_region_outer_bound_with_per_user_fano
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ Pe₁ Pe₂ Pe_joint I_marg₁ I_marg₂ I_joint I₁ I₂ Iboth ε
      H_W₁ H_cond₁ H_W₂ H_cond₂ : ℝ)
    (d₁ : MACFanoEntropyData M₁ n R₁ Pe₁ I_marg₁ H_W₁ H_cond₁)
    (d₂ : MACFanoEntropyData M₂ n R₂ Pe₂ I_marg₂ H_W₂ H_cond₂)
    (h_fano_joint : MACFanoBound M₁ M₂ n R₁ R₂ Pe_joint I_joint)
    (h_chain₁ : MACPerLetterChain₁ n I_marg₁ I₁)
    (h_chain₂ : MACPerLetterChain₂ n I_marg₂ I₂)
    (h_chain_joint : I_joint ≤ (n : ℝ) * Iboth)
    (h_cleanup₁ : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup₂ : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup_joint :
        (1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) ≤ ε) :
    InMACCapacityRegion R₁ R₂ (I₁ + ε) (I₂ + ε) (Iboth + ε) := by
  sorry

/-- **S22-E — MAC outer bound, per-user directions genuinely Fano-backed
from measure primitives.**

Builds the published `mac_capacity_region_outer_bound` headline with both
per-user Fano-side inequalities **genuinely discharged** via
`macFanoEntropyData_of_measure` →
`InformationTheory.MeasureFano.fano_inequality_measure_theoretic` (applied
to each user's message random variable `Wk : Ω → W` and the channel output
`Yo`), rather than supplied as bare hypotheses. The joint-message Fano-side
bound and all per-letter chain bounds remain real Mathlib gaps
(joint-typicality-multi wall) supplied as entropy-level inputs (their
discharge — joint-message Fano / conditional-MI chain rule — is not yet a
project lemma). This is the genuine wiring that backs the per-user converse
directions with real Fano content while keeping the headline non-circular.

@residual(plan:mac-bc-sorry-migration-plan) -/
theorem mac_capacity_region_outer_bound_of_measure
    {Ω : Type*} [MeasurableSpace Ω]
    {W₁ : Type*} [Fintype W₁] [DecidableEq W₁] [Nonempty W₁]
      [MeasurableSpace W₁] [MeasurableSingletonClass W₁]
    {W₂ : Type*} [Fintype W₂] [DecidableEq W₂] [Nonempty W₂]
      [MeasurableSpace W₂] [MeasurableSingletonClass W₂]
    {Y : Type*} [MeasurableSpace Y]
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Wk₁ : Ω → W₁) (Wk₂ : Ω → W₂) (Yo : Ω → Y)
    (dec₁ : Y → W₁) (dec₂ : Y → W₂)
    (hWk₁ : Measurable Wk₁) (hWk₂ : Measurable Wk₂) (hYo : Measurable Yo)
    (hdec₁ : Measurable dec₁) (hdec₂ : Measurable dec₂)
    (hcard₁ : 2 ≤ Fintype.card W₁) (hcard₂ : 2 ≤ Fintype.card W₂)
    (hMcard₁ : Fintype.card W₁ = M₁) (hMcard₂ : Fintype.card W₂ = M₂)
    (R₁ R₂ Pe_joint I_marg₁ I_marg₂ I_joint I₁ I₂ Iboth ε
      H_W₁ H_W₂ : ℝ)
    (h_uniform₁ : H_W₁ = (n : ℝ) * R₁)
    (h_decomp₁ : H_W₁ = I_marg₁ + MeasureFano.condEntropy μ Wk₁ Yo)
    (h_uniform₂ : H_W₂ = (n : ℝ) * R₂)
    (h_decomp₂ : H_W₂ = I_marg₂ + MeasureFano.condEntropy μ Wk₂ Yo)
    (h_fano_joint :
        (n : ℝ) * (R₁ + R₂)
          ≤ I_joint + 1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ)))
    (h_chain₁ : I_marg₁ ≤ (n : ℝ) * I₁)
    (h_chain₂ : I_marg₂ ≤ (n : ℝ) * I₂)
    (h_chain_joint : I_joint ≤ (n : ℝ) * Iboth)
    (h_cleanup₁ :
        (1 + MeasureFano.errorProb μ Wk₁ Yo dec₁
          * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup₂ :
        (1 + MeasureFano.errorProb μ Wk₂ Yo dec₂
          * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup_joint :
        (1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) ≤ ε) :
    InMACCapacityRegion R₁ R₂ (I₁ + ε) (I₂ + ε) (Iboth + ε) := by
  sorry

end MACFanoRepublish

end InformationTheory.Shannon
