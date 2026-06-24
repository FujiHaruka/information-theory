import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Bridge
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.DPI
import InformationTheory.Shannon.SlepianWolf.Basic
import InformationTheory.Fano.Measure
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Typed random variable API

An opt-in notation layer that allows writing `H(μ; X)`, `H(μ; X | Y)`, `I(μ; X ; Y)`,
`I(μ; X ; Y | Z)`, and `D(μ; X ∥ Y)` directly in the style of Cover–Thomas.

## Main definitions

* `condEntropy` — re-export of `MeasureFano.condEntropy` into the `Shannon` namespace.
* `klDivRV` — KL divergence between two random variables: `klDiv (μ.map X) (μ.map Y)`.
* `differentialEntropyRV` — differential entropy of a real-valued random variable.

## Main statements

* `klDivRV_def` — `klDivRV μ X Y = klDiv (μ.map X) (μ.map Y)` (by `rfl`).
* `entropy_nonneg_rv` — `0 ≤ entropy μ X`.
* `mutualInfo_comm_rv` — `I(X; Y) = I(Y; X)`.
* `mutualInfo_le_of_postprocess_rv` — data processing inequality.

## Implementation notes

The internal representations (`entropy`, `mutualInfo`, `condMutualInfo`,
`MeasureFano.condEntropy`, `differentialEntropy`, `klDiv`) are unchanged; only thin alias
definitions and notation are added.

Notation is `scoped[InformationTheory.Shannon]` so that only call sites that `open scoped
InformationTheory.Shannon` can see it.

The notation uses `H(μ; X)` / `I(μ; X ; Y)` forms with explicit `μ` because the
`_` anonymous-placeholder approach cannot synthesize `μ` from context at `notation3`
body evaluation time. Precedence `:max` makes each notation an atomic high-precedence
term, avoiding parse errors in expressions like `0 ≤ H(μ; X)`.

The separator in `D(μ; X ∥ Y)` is `∥` (U+2225 PARALLEL TO), distinct from the norm
delimiter `‖` (U+2016 DOUBLE VERTICAL LINE), to avoid token conflicts.

Type-class constraints required by each notation propagate to the call site:
* `H(μ; X)` / `H(μ; X | Y)` require `[Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]`.
* `I(μ; X ; Y)` requires `[MeasurableSpace α] [MeasurableSpace β]`.
* `I(μ; X ; Y | Z)` additionally requires `[StandardBorelSpace α] [Nonempty α]
  [StandardBorelSpace β] [Nonempty β]`.
* `D(μ; X ∥ Y)` requires `[MeasurableSpace α]`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! ## Re-export: `MeasureFano.condEntropy` -/

/-- Re-export `InformationTheory.MeasureFano.condEntropy` into the
`InformationTheory.Shannon` namespace, so the notation `H(X | Y)` resolves here.
Internal definition is unchanged. -/
@[entry_point, reducible] noncomputable def condEntropy
    {Ω : Type*} [MeasurableSpace Ω]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {β : Type*} [MeasurableSpace β]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Ω → α) (Yo : Ω → β) : ℝ :=
  InformationTheory.MeasureFano.condEntropy μ Xs Yo

/-! ## KL divergence (typed RV form, 1-measure) -/

/-- KL divergence between two random variables on a common ambient measure `μ`:
`klDivRV μ X Y := klDiv (μ.map X) (μ.map Y)`.

This is the 1-measure form of the textbook `D(X ‖ Y)`. The 2-measure form
(`klDiv (μ.map X) (ν.map Y)`) is not provided here. -/
@[entry_point]
noncomputable def klDivRV
    {Ω : Type*} [MeasurableSpace Ω]
    {α : Type*} [MeasurableSpace α]
    (μ : Measure Ω) (X Y : Ω → α) : ℝ≥0∞ :=
  klDiv (μ.map X) (μ.map Y)

/-- `klDivRV μ X Y = klDiv (μ.map X) (μ.map Y)` by definition. -/
@[entry_point]
lemma klDivRV_def
    {Ω : Type*} [MeasurableSpace Ω]
    {α : Type*} [MeasurableSpace α]
    (μ : Measure Ω) (X Y : Ω → α) :
    klDivRV μ X Y = klDiv (μ.map X) (μ.map Y) := rfl

/-! ## Differential entropy (typed RV form) -/

/-- Differential entropy of a real-valued random variable on ambient `(Ω, μ)`:
`differentialEntropyRV μ X := differentialEntropy (μ.map X)`. -/
@[entry_point]
noncomputable def differentialEntropyRV
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  InformationTheory.Shannon.differentialEntropy (μ.map X)

/-! ## Notation -/

scoped[InformationTheory.Shannon] notation3:max "H(" μ "; " X ")" =>
  entropy μ X
scoped[InformationTheory.Shannon] notation3:max "H(" μ "; " X " | " Y ")" =>
  InformationTheory.Shannon.condEntropy μ X Y
scoped[InformationTheory.Shannon] notation3:max "I(" μ "; " X " ; " Y ")" =>
  mutualInfo μ X Y
scoped[InformationTheory.Shannon] notation3:max
  "I(" μ "; " X " ; " Y " | " Z ")" =>
  condMutualInfo μ X Y Z
scoped[InformationTheory.Shannon] notation3:max "D(" μ "; " X " ∥ " Y ")" =>
  klDivRV μ X Y
-- Note: `D(μ; X ∥ Y)` uses `∥` (U+2225 PARALLEL TO), not `‖` (U+2016 DOUBLE VERTICAL LINE).

/-! ## Sanity examples -/

section Examples

open scoped InformationTheory.Shannon

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (X : Ω → α) (hX : Measurable X) :
    0 ≤ H(μ; X) :=
  entropy_nonneg μ X hX

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {β : Type*} [MeasurableSpace β]
    (X : Ω → α) (Y : Ω → β) :
    H(μ; X | Y) = InformationTheory.MeasureFano.condEntropy μ X Y :=
  rfl

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {α : Type*} [MeasurableSpace α]
    {β : Type*} [MeasurableSpace β]
    (X : Ω → α) (Y : Ω → β) :
    0 ≤ I(μ; X ; Y) :=
  mutualInfo_nonneg μ X Y

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {β : Type*} [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
    {γ : Type*} [MeasurableSpace γ]
    (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    0 ≤ I(μ; X ; Y | Z) :=
  condMutualInfo_nonneg μ X Y Z

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {α : Type*} [MeasurableSpace α]
    (X Y : Ω → α) :
    D(μ; X ∥ Y) = klDiv (μ.map X) (μ.map Y) :=
  klDivRV_def μ X Y

end Examples

/-! ## Typed-form main lemmas

One-line aliases of the measure-form lemmas. The `_rv` suffix avoids name conflicts
with the bare names. -/

section MainLemmasRV

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Entropy -/

/-- `H(X) ≥ 0`. -/
@[entry_point]
theorem entropy_nonneg_rv
    {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (hX : Measurable X) :
    0 ≤ entropy μ X := by
  classical exact entropy_nonneg μ X hX

/-! ### Mutual information -/

/-- `I(X; Y) = I(Y; X)` (Cover–Thomas 2.4.1). -/
@[entry_point]
theorem mutualInfo_comm_rv
    {α : Type*} [MeasurableSpace α]
    {β : Type*} [MeasurableSpace β]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → α) (Y : Ω → β)
    (hX : Measurable X) (hY : Measurable Y) :
    mutualInfo μ X Y = mutualInfo μ Y X :=
  mutualInfo_comm μ X Y hX hY

/-! ### Data processing inequality -/

/-- Data processing inequality: post-processing cannot increase mutual information.
`I(X; f(Y)) ≤ I(X; Y)` — Cover–Thomas 2.8.1. -/
@[entry_point]
theorem mutualInfo_le_of_postprocess_rv
    {α : Type*} [MeasurableSpace α]
    {β : Type*} [MeasurableSpace β]
    {γ : Type*} [MeasurableSpace γ]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    {f : β → γ} (hf : Measurable f) :
    mutualInfo μ X (f ∘ Y) ≤ mutualInfo μ X Y :=
  mutualInfo_le_of_postprocess μ X Y hX hY hf

end MainLemmasRV

/-! ## Sanity examples for typed-form main lemmas -/

section MainLemmasExamples

open scoped InformationTheory.Shannon

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (X : Ω → α) (hX : Measurable X) :
    0 ≤ H(μ; X) :=
  entropy_nonneg_rv μ X hX

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {α : Type*} [MeasurableSpace α]
    {β : Type*} [MeasurableSpace β]
    (X : Ω → α) (Y : Ω → β)
    (hX : Measurable X) (hY : Measurable Y) :
    I(μ; X ; Y) = I(μ; Y ; X) :=
  mutualInfo_comm_rv μ X Y hX hY

/-- DPI (typed): post-processing cannot increase MI. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {α : Type*} [MeasurableSpace α]
    {β : Type*} [MeasurableSpace β]
    {γ : Type*} [MeasurableSpace γ]
    (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    {f : β → γ} (hf : Measurable f) :
    mutualInfo μ X (f ∘ Y) ≤ I(μ; X ; Y) :=
  mutualInfo_le_of_postprocess_rv μ X Y hX hY hf

end MainLemmasExamples

end InformationTheory.Shannon
