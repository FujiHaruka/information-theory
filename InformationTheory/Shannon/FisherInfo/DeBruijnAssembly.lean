import InformationTheory.Shannon.FisherInfo.DeBruijnAssembly.Core
import InformationTheory.Shannon.FisherInfo.DeBruijnAssembly.Domination
import InformationTheory.Shannon.FisherInfo.DeBruijnAssembly.Derivatives
import InformationTheory.Shannon.FisherInfo.DeBruijnAssembly.Assembly

/-!
# Per-time de Bruijn identity — assembly

Aggregates the submodules that prove the per-time de Bruijn identity
`debruijnIdentityV2_holds_assembled` for a general `X`. This file is placed downstream of
the atom supplier `FisherInfoDeBruijnPerTime.lean` (which imports `FisherInfoDeBruijn`)
so that the assembly can use those atoms without an import cycle.

## Implementation notes

The per-time identity is assembled from the atoms by: identifying the path density with
`convDensityAdd`; rewriting the entropy as `∫ negMulLog pPath`; differentiating under the
integral (`entropy_hasDerivAt_via_parametric`); applying the heat equation
(`heatFlow_density_heat_equation`); integrating by parts (`debruijn_ibp_step`); and matching
the result to `(1/2) · fisherInfoOfDensityReal h_reg.density_t` (`fisher_from_logDeriv`).
The regularity discharges (Gaussian-tail domination, integrand measurability, global
`C¹`-ness, chain-rule plumbing) are factored into named private lemmas in the submodules.
-/
