import InformationTheory.Shannon.EPI.Unconditional.TruncationLimit.Core
import InformationTheory.Shannon.EPI.Unconditional.TruncationLimit.Mono
import InformationTheory.Shannon.EPI.Unconditional.TruncationLimit.Limit

/-!
# Truncation + monotone-limit route for gateway monotonicity

Umbrella module for the unconditional gateway-monotonicity development via integer truncation of
`W`. The construction reuses the conditioning-truncation machinery of
`EPIInfiniteVarianceTruncation`
/ `EPIInfiniteVarianceCapstone`, specialized to truncating `W` alone.

The target is the `⊤`-branch of gateway monotonicity (`h(W) = ⊤ ⟹ h(W+V) = ⊤`), which closes by
`le_top` and is therefore compatible with the lower-semicontinuous `≤`-only limit estimates.

This file re-exports the three parts `Core` / `Mono` / `Limit`.
-/
