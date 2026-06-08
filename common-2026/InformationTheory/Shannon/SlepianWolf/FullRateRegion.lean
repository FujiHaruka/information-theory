import InformationTheory.Shannon.SlepianWolf.FullRateRegion.Core
import InformationTheory.Shannon.SlepianWolf.FullRateRegion.AliasBound
import InformationTheory.Shannon.SlepianWolf.FullRateRegion.PairBound

/-!
# Slepian–Wolf full rate region — Phase D (error event decomposition)

E-5'' Phase D ([`docs/shannon/slepian-wolf-full-rate-region-plan.md`](../../docs/shannon/slepian-wolf-full-rate-region-plan.md)).
Publishes the joint typicality decoder and the 4-way error event decomposition
`E ⊆ E_0 ∪ E_X ∪ E_Y ∪ E_{XY}`.

Encoder-side mirror of `ChannelCodingAchievability.errorProbAt_le_E1_plus_E2`.
-/
