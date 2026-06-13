import InformationTheory.Shannon.SlepianWolf.FullRateRegion.Core
import InformationTheory.Shannon.SlepianWolf.FullRateRegion.AliasBound
import InformationTheory.Shannon.SlepianWolf.FullRateRegion.PairBound

/-!
# Slepian–Wolf full rate region — error event decomposition

Publishes the joint typicality decoder and the 4-way error event decomposition
`E ⊆ E_0 ∪ E_X ∪ E_Y ∪ E_{XY}`, the encoder-side mirror of
`ChannelCodingAchievability.errorProbAt_le_E1_plus_E2`.
-/
