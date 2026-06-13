import InformationTheory.Shannon.ConditionalMethodOfTypes.Core
import InformationTheory.Shannon.ConditionalMethodOfTypes.Mass

/-!
# Conditional method of types — `conditionalStronglyTypicalSlice_mass_ge`

Cover-Thomas 10.6.1: for a fixed X-strongly-typical `x : Fin n → α`, lower-bound the
Y-product mass of the conditional strongly-typical slice
`{y | (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε}` under `μ_Y^n`:

  `exp(-n · (entropy μ Z₀ - entropy μ X₀ + slack))
     ≤ (Measure.pi (μ.map (Ys 0))^n).real (conditionalStronglyTypicalSlice ...)`

where `entropy μ Z₀ - entropy μ X₀ = H(Y|X)` (conditional entropy in chain-rule form)
and `slack = O(ε)`.

## Implementation notes

`H(Y|X)` is expressed as `entropy μ Z₀ - entropy μ X₀` (chain-rule form), matching
what the rate-distortion achievability consumer expects. The `mutualInfoOfChannel`
reshape is a separate concern and is avoided here.
-/
