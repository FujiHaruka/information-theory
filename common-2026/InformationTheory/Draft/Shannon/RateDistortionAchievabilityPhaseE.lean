import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.RateDistortion.AchievabilityPhaseD

/-!
# Rate-distortion achievability — import conduit

An empty shell retained only for its imports: downstream files such as
`RateDistortionAchievabilityPhaseEDischarge` obtain definitions like `expectedDistortionPmf`
through this file's transitive import. The strong-typicality form of achievability lives in
`RateDistortion.AchievabilityPhaseEStrongFinal` as `rate_distortion_achievability`.
-/

namespace InformationTheory.Shannon

open Filter Topology MeasureTheory ProbabilityTheory InformationTheory
open InformationTheory.Shannon.ChannelCoding (Codebook codebookMeasure jointSequence
  jointlyTypicalSet)
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
variable [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]


end InformationTheory.Shannon
