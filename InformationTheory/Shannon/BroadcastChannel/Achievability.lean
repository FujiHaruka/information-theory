import InformationTheory.Shannon.BroadcastChannel.Achievability.Setup
import InformationTheory.Shannon.BroadcastChannel.Achievability.ErrorAnalysis
import InformationTheory.Shannon.BroadcastChannel.Achievability.Assembly

/-!
# Degraded broadcast channel — achievability (superposition inner bound)

The achievability half of the degraded broadcast-channel coding theorem
(Cover–Thomas *Elements of Information Theory* Thm 15.6.2): the superposition (two-tier
cloud / satellite) random-coding inner bound.  The net-new tier relative to the
multiple-access achievability (`InformationTheory.Shannon.MAC`) is the **conditional
(superposition) random codebook**: satellite codewords are drawn from a conditional
product law `Πᵢ K(Uᵢ)` steered by the cloud codeword, rather than a flat product law.

## Main definitions

* `bcJointDistribution pU K W` — the per-coordinate joint law of `(U, X, Y₁, Y₂)`,
  `U ∼ pU`, `X ∣ U ∼ K`, `(Y₁, Y₂) ∣ X ∼ W`.
* `bcInfo₂ pU K W` — the cloud information `I(U; Y₂) = H(U) + H(Y₂) − H(U, Y₂)`.
* `bcInfo₁ pU K W` — the satellite conditional information
  `I(X; Y₁ ∣ U) = H(U, X) + H(U, Y₁) − H(U, X, Y₁) − H(U)`.
* `IsBCDegraded W` — physical degradedness `X → Y₁ → Y₂` (there is a degrading kernel).
* `BCCloudCodebook` / `BCSatelliteCodebook` and their random-coding measures
  `bcCloudCodebookMeasure`, `bcSatelliteCodebookMeasure`, `bcCodebookMeasure` — the
  two-tier ensemble; the satellite law is a **conditional product** `Πᵢ K(Uᵢ)`.

## Main results

* `bc_conditional_slice_prob_le` — the gateway covering bound: the conditional-product
  mass of the jointly-typical satellite slice is `≤ exp(−n (I(X; Y₁ ∣ U) − ε))`.
* `bc_achievability` — the headline: any rate pair strictly inside the degraded-BC region
  `R₁ < I(X; Y₁ ∣ U)`, `R₂ < I(U; Y₂)` is achievable with vanishing per-receiver error.

## Module structure

Umbrella of the `Shannon/BroadcastChannel/Achievability/` family, re-exporting:

* `Achievability.Setup` — degradedness, the ambient measure, the auxiliary-variable informations,
  the two-tier codebook, the positivity / marginal / relabeling infrastructure, the covering-bound
  ingredients, and the two-tier decoders.
* `Achievability.ErrorAnalysis` — the receiver-2 (cloud) and receiver-1 (strong) error analyses
  with their random-codebook averaging.
* `Achievability.Assembly` — the superposition random-coding assembly and the headline
  `bc_achievability`.
-/
