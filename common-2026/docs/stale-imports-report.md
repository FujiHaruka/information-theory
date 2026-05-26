# Stale / missing imports report (linter.minImports)

> **部分結果**: `lake build` を 3220 / 3266 (98.6%) で中断した時点のログ抽出。残り 46 modules 未スキャン。`Common2026/Draft/Shannon/Chernoff*` 系の重い末尾領域が一部未到達。

## Summary

- **Unneeded import candidates**: 945 件 (198 files)
- **Missing import candidates** (linter が import 追加を提案): 209 件 (186 files)

### ⚠️ 削除前にレビュー必須

linter は **直接 declaration 使用しか追わない** ため、以下は **誤検出する**:

- transitive / re-export 経由の依存 (wrapper file が名前空間継承だけしている)
- tactic-only import (`linarith` 等の tactic は decl を直接呼ばないが必要)
- instance-only import (`[X]` instance 探索のため import 必要だが decl 引いてない)

各候補は手で確認してから削除してください。`lake shake` 相当の `--keep-implied` ロジックは無いです。

## Unneeded import candidates

### `Common2026/Draft/Shannon/BroadcastChannel.lean` (3)

- L1: `Common2026.Shannon.ChannelCoding`
- L2: `Common2026.Shannon.CondMutualInfo`
- L3: `Common2026.Shannon.MIChainRule`

### `Common2026/Draft/Shannon/BroadcastChannelSuperposition.lean` (2)

- L1: `Common2026.Draft.Shannon.BroadcastChannel`
- L2: `Common2026.Draft.Shannon.MACL1Discharge`

### `Common2026/Draft/Shannon/BroadcastChannelSuperpositionBody.lean` (2)

- L1: `Common2026.Draft.Shannon.BroadcastChannelSuperposition`
- L2: `Common2026.Draft.Shannon.MACBodyDischarge`

### `Common2026/Draft/Shannon/BrunnMinkowski.lean` (6)

- L1: `Common2026.Shannon.DifferentialEntropy`
- L2: `Common2026.Shannon.EntropyPowerInequality`
- L3: `Mathlib.Analysis.SpecialFunctions.Exp`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L5: `Mathlib.Probability.Independence.Basic`
- L6: `Mathlib.Algebra.Group.Pointwise.Set.Basic`

### `Common2026/Draft/Shannon/BrunnMinkowskiConcavity.lean` (5)

- L1: `Common2026.Draft.Shannon.BrunnMinkowski`
- L2: `Mathlib.Analysis.SpecialFunctions.Exp`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L4: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L5: `Mathlib.Analysis.Complex.Exponential`

### `Common2026/Draft/Shannon/BrunnMinkowskiFunctional.lean` (6)

- L1: `Common2026.Draft.Shannon.BrunnMinkowski`
- L2: `Common2026.Draft.Shannon.BrunnMinkowskiConcavity`
- L3: `Mathlib.Analysis.SpecialFunctions.Exp`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L6: `Mathlib.Analysis.Convex.Function`
- L7: `Mathlib.MeasureTheory.Integral.Lebesgue.Basic`

### `Common2026/Draft/Shannon/ChannelCodingConverseGeneralComplete.lean` (4)

- L1: `Common2026.Shannon.ChannelCodingConverseGeneral`
- L2: `Common2026.Shannon.CondMutualInfo`
- L3: `Common2026.Shannon.MIChainRule`
- L4: `Common2026.Shannon.MutualInfo`

### `Common2026/Draft/Shannon/ChernoffBandMassDischarge.lean` (15)

- L1: `Common2026.Draft.Shannon.ChernoffSanovDischarge`
- L2: `Common2026.Draft.Shannon.ChernoffPerTiltSanov`
- L3: `Common2026.Draft.Shannon.ChernoffPerTiltDischarge`
- L4: `Common2026.Draft.Shannon.ChernoffConverse`
- L5: `Common2026.Draft.Shannon.ChernoffInformation`
- L6: `Common2026.Shannon.Chernoff`
- L7: `Common2026.Shannon.CramerLC2Discharge`
- L8: `Mathlib.Probability.StrongLaw`
- L9: `Mathlib.Probability.Independence.InfinitePi`
- L10: `Mathlib.Probability.ProductMeasure`
- L11: `Mathlib.MeasureTheory.Function.ConvergenceInMeasure`
- L12: `Mathlib.MeasureTheory.Integral.Bochner.SumMeasure`
- L13: `Mathlib.Analysis.SpecialFunctions.Pow.Deriv`
- L14: `Mathlib.Analysis.Calculus.LocalExtr.Basic`
- L15: `Mathlib.Topology.Order.LocalExtr`

### `Common2026/Draft/Shannon/ChernoffConverse.lean` (4)

- L1: `Common2026.Shannon.Chernoff`
- L2: `Common2026.Draft.Shannon.ChernoffInformation`
- L3: `Mathlib.Topology.Order.LiminfLimsup`
- L4: `Mathlib.Order.Filter.IsBounded`

### `Common2026/Draft/Shannon/ChernoffInformation.lean` (4)

- L1: `Common2026.Shannon.Chernoff`
- L2: `Common2026.InformationTheory.Asymptotic`
- L3: `Mathlib.Topology.Order.LiminfLimsup`
- L4: `Mathlib.Order.Filter.IsBounded`

### `Common2026/Draft/Shannon/ChernoffPerTiltDischarge.lean` (11)

- L1: `Common2026.Draft.Shannon.ChernoffConverse`
- L2: `Common2026.Shannon.Chernoff`
- L3: `Common2026.Draft.Shannon.ChernoffInformation`
- L4: `Common2026.InformationTheory.Asymptotic`
- L5: `Mathlib.Topology.Order.LiminfLimsup`
- L6: `Mathlib.Order.Filter.IsBounded`
- L7: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L8: `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`
- L9: `Mathlib.MeasureTheory.Measure.Dirac`
- L10: `Mathlib.MeasureTheory.Measure.MeasureSpace`
- L11: `Mathlib.MeasureTheory.Measure.Real`

### `Common2026/Draft/Shannon/ChernoffPerTiltSanov.lean` (9)

- L1: `Common2026.Draft.Shannon.ChernoffPerTiltDischarge`
- L2: `Common2026.Draft.Shannon.ChernoffConverse`
- L3: `Common2026.Shannon.Chernoff`
- L4: `Common2026.Draft.Shannon.ChernoffInformation`
- L5: `Common2026.InformationTheory.Asymptotic`
- L6: `Mathlib.MeasureTheory.Constructions.Pi`
- L7: `Mathlib.MeasureTheory.Measure.Dirac`
- L8: `Mathlib.MeasureTheory.Measure.MeasureSpace`
- L9: `Mathlib.MeasureTheory.Measure.Real`

### `Common2026/Draft/Shannon/ChernoffSanovDischarge.lean` (7)

- L1: `Common2026.Draft.Shannon.ChernoffPerTiltSanov`
- L2: `Common2026.Draft.Shannon.ChernoffPerTiltDischarge`
- L3: `Common2026.Draft.Shannon.ChernoffConverse`
- L4: `Common2026.Shannon.Chernoff`
- L5: `Common2026.Shannon.ChernoffNLetterZSum`
- L6: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L7: `Mathlib.Analysis.SpecialFunctions.Log.Basic`

### `Common2026/Draft/Shannon/Cramer.lean` (9)

- L1: `Mathlib.Probability.Moments.Basic`
- L2: `Mathlib.Probability.Moments.IntegrableExpMul`
- L3: `Mathlib.Probability.Moments.MGFAnalytic`
- L4: `Mathlib.Probability.Moments.Tilted`
- L5: `Mathlib.Probability.IdentDistrib`
- L6: `Mathlib.MeasureTheory.Measure.Tilted`
- L7: `Mathlib.Analysis.SpecialFunctions.Exp`
- L8: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L9: `Mathlib.Order.LiminfLimsup`

### `Common2026/Draft/Shannon/CramerCLTClosure.lean` (5)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.MeasureTheory.Measure.Portmanteau`
- L3: `Mathlib.Probability.CentralLimitTheorem`
- L4: `Common2026.Shannon.CramerLC2DischargeExt`
- L5: `Common2026.Draft.Shannon.InfinitePiTiltedChangeOfMeasure`

### `Common2026/Draft/Shannon/CramerLC2PhaseC.lean` (8)

- L1: `Common2026.Draft.Shannon.Cramer`
- L2: `Common2026.Shannon.CramerLC2Discharge`
- L3: `Common2026.Shannon.CramerLC2DischargeExt`
- L4: `Mathlib.Probability.StrongLaw`
- L5: `Mathlib.Probability.Independence.InfinitePi`
- L6: `Mathlib.Probability.ProductMeasure`
- L7: `Mathlib.MeasureTheory.Function.ConvergenceInMeasure`
- L8: `Mathlib.MeasureTheory.Measure.Tilted`

### `Common2026/Draft/Shannon/CramerPhaseDGapWorkaround.lean` (3)

- L1: `Common2026.Draft.Shannon.CramerLC2PhaseC`
- L2: `Common2026.Draft.Shannon.ChernoffPerTiltDischarge`
- L3: `Mathlib.MeasureTheory.Constructions.Cylinders`

### `Common2026/Draft/Shannon/EPIConvolutionDensity.lean` (7)

- L1: `Mathlib.Probability.Density`
- L2: `Mathlib.Probability.Independence.Basic`
- L3: `Mathlib.Analysis.LConvolution`
- L4: `Mathlib.Analysis.Calculus.ParametricIntegral`
- L5: `Mathlib.Analysis.Calculus.LogDeriv`
- L6: `Mathlib.MeasureTheory.Measure.Haar.Unique`
- L7: `Common2026.Shannon.FisherInfoV2`

### `Common2026/Draft/Shannon/InfinitePiTiltedChangeOfMeasure.lean` (4)

- L1: `Common2026.Shannon.MeasurePiTiltedFactorization`
- L2: `Common2026.Shannon.CramerLC2DischargeExt`
- L3: `Common2026.Draft.Shannon.CramerLC2PhaseC`
- L4: `Mathlib.Probability.ProductMeasure`

### `Common2026/Draft/Shannon/LZ78ConverseDischarge.lean` (7)

- L1: `Common2026.Shannon.LempelZiv78`
- L2: `Common2026.Shannon.LZ78ZivInequality`
- L3: `Common2026.Shannon.LZ78GreedyParsing`
- L4: `Common2026.Shannon.ShannonMcMillanBreiman`
- L5: `Common2026.Shannon.SMBChainRule`
- L6: `Mathlib.Topology.Order.LiminfLimsup`
- L7: `Mathlib.Order.LiminfLimsup`

### `Common2026/Draft/Shannon/LZ78DistinctEncoding.lean` (11)

- L1: `Common2026.Shannon.LempelZiv78`
- L2: `Common2026.Shannon.LZ78GreedyParsing`
- L3: `Common2026.Shannon.LZ78GreedyParsingImpl`
- L4: `Common2026.Shannon.LZ78GreedyLongestPrefix`
- L5: `Common2026.Shannon.LZ78ZivCountingBody`
- L6: `Common2026.Draft.Shannon.LZ78FinalGlue`
- L7: `Mathlib.Analysis.SpecialFunctions.Log.Base`
- L8: `Mathlib.Analysis.Asymptotics.Defs`
- L9: `Mathlib.Analysis.Asymptotics.Lemmas`
- L10: `Mathlib.Analysis.Complex.ExponentialBounds`
- L11: `Mathlib.Order.Filter.IsBounded`

### `Common2026/Draft/Shannon/LZ78FinalGlue.lean` (9)

- L1: `Common2026.Shannon.LempelZiv78`
- L2: `Common2026.Shannon.LZ78ZivInequality`
- L3: `Common2026.Shannon.LZ78ConverseAsymptotic`
- L4: `Common2026.Draft.Shannon.LZ78ConverseDischarge`
- L5: `Common2026.Draft.Shannon.LZ78SMBSandwich`
- L6: `Common2026.Shannon.LZ78GreedyParsingImpl`
- L7: `Common2026.Shannon.SMBAlgoetCover`
- L8: `Mathlib.Topology.Order.LiminfLimsup`
- L9: `Mathlib.Order.LiminfLimsup`

### `Common2026/Draft/Shannon/LZ78SMBSandwich.lean` (8)

- L1: `Common2026.Shannon.LempelZiv78`
- L2: `Common2026.Shannon.LZ78ZivInequality`
- L3: `Common2026.Draft.Shannon.LZ78ConverseDischarge`
- L4: `Common2026.Shannon.LZ78GreedyParsing`
- L5: `Common2026.Shannon.ShannonMcMillanBreiman`
- L6: `Common2026.Shannon.SMBAlgoetCover`
- L7: `Mathlib.Topology.Order.LiminfLimsup`
- L8: `Mathlib.Order.LiminfLimsup`

### `Common2026/Draft/Shannon/MACCornerPoint.lean` (3)

- L1: `Common2026.Draft.Shannon.MultipleAccessChannel`
- L2: `Mathlib.Analysis.Convex.Combination`
- L3: `Mathlib.Analysis.Convex.Hull`

### `Common2026/Draft/Shannon/MACFanoConverseBody.lean` (3)

- L1: `Common2026.Draft.Shannon.MACL2Discharge`
- L2: `Common2026.Fano.Measure`
- L3: `Mathlib.Analysis.Complex.ExponentialBounds`

### `Common2026/Draft/Shannon/MACL1Discharge.lean` (1)

- L1: `Common2026.Draft.Shannon.MultipleAccessChannel`

### `Common2026/Draft/Shannon/MACL2Discharge.lean` (1)

- L1: `Common2026.Draft.Shannon.MACBodyDischarge`

### `Common2026/Draft/Shannon/MACPerEventAEPDecay.lean` (1)

- L1: `Common2026.Shannon.MACRandomCodebookAveraging`

### `Common2026/Draft/Shannon/MultipleAccessChannel.lean` (3)

- L1: `Common2026.Shannon.ChannelCoding`
- L2: `Common2026.Shannon.CondMutualInfo`
- L3: `Common2026.Shannon.MIChainRule`

### `Common2026/Draft/Shannon/MultivariateDiffEntropy.lean` (10)

- L1: `Mathlib.MeasureTheory.Measure.Prod`
- L2: `Mathlib.MeasureTheory.Measure.WithDensity`
- L3: `Mathlib.MeasureTheory.Integral.Prod`
- L4: `Mathlib.MeasureTheory.Constructions.Pi`
- L5: `Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym`
- L6: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L7: `Mathlib.InformationTheory.KullbackLeibler.Basic`
- L8: `Common2026.Shannon.DifferentialEntropy`
- L9: `Common2026.Shannon.MutualInfo`
- L10: `Common2026.Shannon.MIChainRule`

### `Common2026/Draft/Shannon/RateDistortionAchievabilityPhaseE.lean` (1)

- L1: `Common2026.Shannon.RateDistortionAchievabilityPhaseD`

### `Common2026/Draft/Shannon/RateDistortionConverseNLetter.lean` (3)

- L1: `Common2026.Shannon.RateDistortionConverseMonotone`
- L2: `Common2026.Shannon.RateDistortionAchievability`
- L3: `Common2026.Shannon.RateDistortionConvexityDischarge`

### `Common2026/Draft/Shannon/RateDistortionConvexity.lean` (1)

- L1: `Common2026.Shannon.RateDistortionConverseMonotone`

### `Common2026/Draft/Shannon/RelayCutset.lean` (3)

- L1: `Common2026.Shannon.ChannelCoding`
- L2: `Common2026.Shannon.CondMutualInfo`
- L3: `Common2026.Shannon.MIChainRule`

### `Common2026/Draft/Shannon/RelayInnerBound.lean` (1)

- L1: `Common2026.Draft.Shannon.RelayCutset`

### `Common2026/Draft/Shannon/WynerZivAchievability.lean` (1)

- L1: `Common2026.Shannon.WynerZiv`

### `Common2026/Draft/Shannon/WynerZivConverse.lean` (1)

- L1: `Common2026.Shannon.WynerZiv`

### `Common2026/Draft/Shannon/WynerZivConverseChain.lean` (3)

- L1: `Common2026.Shannon.WynerZiv`
- L2: `Common2026.Draft.Shannon.WynerZivConverse`
- L3: `Common2026.Draft.Shannon.RateDistortionConverseNLetter`

### `Common2026/Fano.lean` (1)

- L2: `Mathlib.Data.Fintype.BigOperators`

### `Common2026/Fano/BinaryJensen.lean` (3)

- L1: `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`
- L2: `Mathlib.Analysis.Convex.Jensen`
- L3: `Mathlib.Data.Fintype.BigOperators`

### `Common2026/Fano/CondEntropy.lean` (2)

- L1: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L2: `Mathlib.Data.Fintype.BigOperators`

### `Common2026/Fano/Core.lean` (5)

- L1: `Common2026.Fano`
- L2: `Common2026.Fano.Entropy`
- L3: `Common2026.Fano.BinaryJensen`
- L4: `Common2026.Fano.CondEntropy`
- L5: `Mathlib.Algebra.BigOperators.Field`

### `Common2026/Fano/DPI.lean` (7)

- L1: `Common2026.Fano`
- L2: `Common2026.Fano.BinaryJensen`
- L3: `Common2026.Fano.Core`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L5: `Mathlib.Analysis.Convex.Jensen`
- L6: `Mathlib.Algebra.BigOperators.Field`
- L7: `Mathlib.Tactic.Linarith`

### `Common2026/Fano/Entropy.lean` (3)

- L1: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L2: `Mathlib.Analysis.Convex.Jensen`
- L3: `Mathlib.Data.Fintype.BigOperators`

### `Common2026/Fano/Measure.lean` (9)

- L1: `Common2026.Fano.Core`
- L2: `Mathlib.Probability.Kernel.CondDistrib`
- L3: `Mathlib.Probability.Kernel.Composition.MeasureCompProd`
- L4: `Mathlib.Probability.ProbabilityMassFunction.Basic`
- L5: `Mathlib.Probability.ProbabilityMassFunction.Constructions`
- L6: `Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic`
- L7: `Mathlib.Analysis.Convex.Integral`
- L8: `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`
- L9: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`

### `Common2026/InformationTheory/Asymptotic.lean` (6)

- L1: `Mathlib.Analysis.Asymptotics.Defs`
- L2: `Mathlib.Analysis.Asymptotics.Lemmas`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L4: `Mathlib.Analysis.SpecialFunctions.Exp`
- L5: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L6: `Mathlib.Topology.MetricSpace.Pseudo.Defs`

### `Common2026/Polymatroid/Basic.lean` (4)

- L1: `Mathlib.Data.Finset.Empty`
- L2: `Mathlib.Data.Finset.Lattice.Basic`
- L3: `Mathlib.Order.Monotone.Basic`
- L4: `Mathlib.Data.Real.Basic`

### `Common2026/Probability/TwoSidedExtension.lean` (15)

- L1: `Common2026.Shannon.Stationary`
- L2: `Common2026.Shannon.EntropyRate`
- L3: `Mathlib.MeasureTheory.Constructions.Projective`
- L4: `Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent`
- L5: `Mathlib.MeasureTheory.Constructions.Cylinders`
- L6: `Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders`
- L7: `Mathlib.MeasureTheory.OuterMeasure.OfAddContent`
- L8: `Mathlib.MeasureTheory.Measure.AddContent`
- L9: `Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic`
- L10: `Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator`
- L11: `Mathlib.Probability.Martingale.Basic`
- L12: `Mathlib.Probability.Martingale.Convergence`
- L13: `Mathlib.MeasureTheory.Measure.MeasuredSets`
- L14: `Mathlib.MeasureTheory.OuterMeasure.BorelCantelli`
- L15: `Mathlib.Dynamics.Ergodic.Ergodic`

### `Common2026/Shannon/AEP.lean` (11)

- L2: `Common2026.Shannon.Han`
- L3: `Common2026.Shannon.Pi`
- L4: `Common2026.Shannon.DPI`
- L5: `Common2026.Shannon.SlepianWolf`
- L6: `Common2026.Fano.Measure`
- L8: `Mathlib.Probability.IdentDistrib`
- L9: `Mathlib.Probability.Independence.Basic`
- L10: `Mathlib.MeasureTheory.Function.ConvergenceInMeasure`
- L11: `Mathlib.MeasureTheory.Constructions.BorelSpace.Order`
- L12: `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`
- L13: `Mathlib.Analysis.SpecificLimits.Basic`

### `Common2026/Shannon/AEPRate.lean` (3)

- L1: `Common2026.Shannon.AEP`
- L2: `Common2026.Shannon.ChannelCoding`
- L3: `Mathlib.Probability.Moments.Variance`

### `Common2026/Shannon/AWGN.lean` (5)

- L1: `Common2026.Shannon.ChannelCoding`
- L2: `Common2026.Shannon.DifferentialEntropy`
- L3: `Mathlib.Probability.Distributions.Gaussian.Real`
- L4: `Mathlib.Probability.Distributions.Gaussian.Basic`
- L5: `Mathlib.MeasureTheory.Measure.GiryMonad`

### `Common2026/Shannon/AWGNAchievability.lean` (1)

- L1: `Common2026.Shannon.AWGN`

### `Common2026/Shannon/AWGNAchievabilityDischarge.lean` (8)

- L1: `Common2026.Shannon.AWGN`
- L2: `Common2026.Shannon.AWGNAchievability`
- L3: `Common2026.Shannon.AWGNMain`
- L4: `Common2026.Shannon.AWGNF1Discharge`
- L5: `Common2026.Shannon.DifferentialEntropy`
- L6: `Mathlib.Probability.Distributions.Gaussian.Real`
- L7: `Mathlib.Probability.Independence.Basic`
- L8: `Mathlib.MeasureTheory.Constructions.Pi`

### `Common2026/Shannon/AWGNConverse.lean` (1)

- L1: `Common2026.Shannon.AWGN`

### `Common2026/Shannon/AWGNF1Discharge.lean` (1)

- L1: `Common2026.Shannon.AWGNMain`

### `Common2026/Shannon/AWGNF2F3Discharge.lean` (1)

- L1: `Common2026.Shannon.AWGNF1Discharge`

### `Common2026/Shannon/AWGNMIBridge.lean` (1)

- L1: `Common2026.Shannon.AWGNF1Discharge`

### `Common2026/Shannon/AWGNMain.lean` (3)

- L1: `Common2026.Shannon.AWGN`
- L2: `Common2026.Shannon.AWGNAchievability`
- L3: `Common2026.Shannon.AWGNConverse`

### `Common2026/Shannon/ArithmeticCoding.lean` (4)

- L1: `Common2026.Shannon.ShannonCode`
- L2: `Common2026.Shannon.ShannonCodeKraftReverse`
- L3: `Mathlib.MeasureTheory.Measure.ProbabilityMeasure`
- L4: `Mathlib.Logic.Equiv.Defs`

### `Common2026/Shannon/BackwardFiltration.lean` (3)

- L1: `Mathlib.Probability.Process.Filtration`
- L2: `Mathlib.MeasureTheory.MeasurableSpace.Basic`
- L3: `Mathlib.Dynamics.Ergodic.MeasurePreserving`

### `Common2026/Shannon/BackwardMartingale.lean` (5)

- L1: `Common2026.Shannon.BackwardFiltration`
- L2: `Mathlib.Probability.Martingale.Basic`
- L3: `Mathlib.Probability.Martingale.Convergence`
- L4: `Mathlib.Probability.Martingale.Upcrossing`
- L5: `Mathlib.MeasureTheory.Function.ConditionalExpectation.Real`

### `Common2026/Shannon/BirkhoffErgodic.lean` (8)

- L1: `Mathlib.Dynamics.Ergodic.Ergodic`
- L2: `Mathlib.Dynamics.Ergodic.Function`
- L3: `Mathlib.Dynamics.Ergodic.MeasurePreserving`
- L4: `Mathlib.MeasureTheory.Integral.Bochner.Basic`
- L5: `Mathlib.MeasureTheory.Integral.Bochner.Set`
- L6: `Mathlib.MeasureTheory.Integral.DominatedConvergence`
- L7: `Mathlib.MeasureTheory.Measure.Typeclasses.Probability`
- L8: `Mathlib.Topology.Algebra.Order.LiminfLimsup`

### `Common2026/Shannon/BlockwiseChannel.lean` (8)

- L1: `Common2026.Shannon.ChannelCoding`
- L2: `Common2026.Shannon.ChannelCodingShannonTheorem`
- L3: `Common2026.Shannon.MIChainRule`
- L4: `Common2026.Shannon.CondEntropyMemoryless`
- L5: `Mathlib.Analysis.Subadditive`
- L6: `Mathlib.MeasureTheory.Constructions.Pi`
- L7: `Mathlib.MeasureTheory.MeasurableSpace.Pi`
- L8: `Mathlib.MeasureTheory.Integral.Lebesgue.Countable`

### `Common2026/Shannon/BrascampLieb.lean` (1)

- L1: `Common2026.Shannon.LoomisWhitney`

### `Common2026/Shannon/Bridge.lean` (9)

- L1: `Common2026.Shannon.MutualInfo`
- L2: `Common2026.Fano.Measure`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L4: `Mathlib.MeasureTheory.Function.SpecialFunctions.Basic`
- L5: `Mathlib.MeasureTheory.Integral.Bochner.SumMeasure`
- L6: `Mathlib.MeasureTheory.Integral.Lebesgue.Countable`
- L7: `Mathlib.MeasureTheory.Measure.Prod`
- L8: `Mathlib.Probability.Kernel.Composition.RadonNikodym`
- L9: `Mathlib.Probability.Kernel.RadonNikodym`

### `Common2026/Shannon/BroadcastChannelAveraging.lean` (1)

- L1: `Common2026.Shannon.BroadcastChannelRandomCodebook`

### `Common2026/Shannon/BroadcastChannelRandomCodebook.lean` (1)

- L1: `Common2026.Draft.Shannon.BroadcastChannelSuperpositionBody`

### `Common2026/Shannon/BrunnMinkowski1DSuperlevelBody.lean` (7)

- L1: `Common2026.Shannon.BrunnMinkowskiPLBody`
- L2: `Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar`
- L3: `Mathlib.MeasureTheory.Measure.NullMeasurable`
- L4: `Mathlib.Algebra.Group.Pointwise.Set.Basic`
- L5: `Mathlib.MeasureTheory.Group.Measure`
- L6: `Mathlib.MeasureTheory.Group.Arithmetic`
- L7: `Mathlib.Topology.Order.Compact`

### `Common2026/Shannon/BrunnMinkowskiClosure.lean` (12)

- L1: `Common2026.Shannon.BrunnMinkowskiLayerCakeBody`
- L2: `Common2026.Shannon.BrunnMinkowskiPLBody`
- L3: `Common2026.Shannon.BrunnMinkowski1DSuperlevelBody`
- L4: `Common2026.Draft.Shannon.BrunnMinkowskiConcavity`
- L5: `Common2026.Draft.Shannon.MultivariateDiffEntropy`
- L6: `Mathlib.MeasureTheory.Constructions.Pi`
- L7: `Mathlib.MeasureTheory.Integral.Prod`
- L8: `Mathlib.MeasureTheory.Integral.Pi`
- L9: `Mathlib.MeasureTheory.Integral.IntegrableOn`
- L10: `Mathlib.MeasureTheory.Measure.Prod`
- L11: `Mathlib.Topology.Algebra.Monoid`
- L12: `Mathlib.Topology.Algebra.ConstMulAction`

### `Common2026/Shannon/BrunnMinkowskiLayerCakeBody.lean` (5)

- L1: `Common2026.Shannon.BrunnMinkowskiPLBody`
- L2: `Common2026.Shannon.BrunnMinkowski1DSuperlevelBody`
- L3: `Mathlib.MeasureTheory.Integral.Layercake`
- L4: `Mathlib.MeasureTheory.Integral.Bochner.Set`
- L5: `Mathlib.MeasureTheory.Measure.Real`

### `Common2026/Shannon/BrunnMinkowskiPLBody.lean` (4)

- L1: `Common2026.Draft.Shannon.BrunnMinkowski`
- L2: `Common2026.Draft.Shannon.BrunnMinkowskiFunctional`
- L3: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L4: `Mathlib.Analysis.MeanInequalities`

### `Common2026/Shannon/ChannelCoding.lean` (4)

- L1: `Common2026.Shannon.MutualInfo`
- L2: `Common2026.Shannon.MIChainRule`
- L3: `Common2026.Shannon.AEP`
- L4: `Mathlib.Probability.Kernel.Basic`

### `Common2026/Shannon/ChannelCodingAchievability.lean` (5)

- L1: `Common2026.Shannon.ChannelCoding`
- L2: `Common2026.Shannon.IIDProductInput`
- L3: `Common2026.Shannon.AEPRate`
- L4: `Mathlib.Probability.ProductMeasure`
- L5: `Mathlib.Probability.Independence.InfinitePi`

### `Common2026/Shannon/ChannelCodingConverse.lean` (2)

- L1: `Common2026.Shannon.Converse`
- L2: `Common2026.Shannon.MIChainRule`

### `Common2026/Shannon/ChannelCodingConverseGeneral.lean` (2)

- L1: `Common2026.Shannon.Converse`
- L2: `Common2026.Shannon.MIChainRule`

### `Common2026/Shannon/ChannelCodingConverseGeneralStrong.lean` (3)

- L1: `Common2026.Draft.Shannon.ChannelCodingConverseGeneralComplete`
- L2: `Common2026.Shannon.CondEntropyMemoryless`
- L3: `Mathlib.MeasureTheory.MeasurableSpace.Embedding`

### `Common2026/Shannon/ChannelCodingConverseMemorylessPure.lean` (1)

- L1: `Common2026.Shannon.ChannelCodingConverseGeneralStrong`

### `Common2026/Shannon/ChannelCodingFeedback.lean` (5)

- L1: `Common2026.Shannon.ChannelCoding`
- L2: `Common2026.Shannon.ChannelCodingConverse`
- L3: `Common2026.Shannon.Converse`
- L4: `Common2026.Shannon.MIChainRule`
- L5: `Common2026.Shannon.CondMutualInfo`

### `Common2026/Shannon/ChannelCodingFeedbackComplete.lean` (4)

- L1: `Common2026.Shannon.ChannelCodingFeedback`
- L2: `Common2026.Shannon.CondMutualInfo`
- L3: `Common2026.Shannon.MIChainRule`
- L4: `Common2026.Shannon.MutualInfo`

### `Common2026/Shannon/ChannelCodingShannonTheorem.lean` (7)

- L1: `Common2026.Shannon.ChannelCoding`
- L2: `Common2026.Shannon.ChannelCodingAchievability`
- L3: `Common2026.Shannon.MaxEntropy`
- L4: `Mathlib.Analysis.Convex.StdSimplex`
- L5: `Mathlib.Topology.Order.Compact`
- L6: `Mathlib.Order.ConditionallyCompleteLattice.Basic`
- L7: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`

### `Common2026/Shannon/ChannelCodingShannonTheoremFull.lean` (3)

- L1: `Common2026.Shannon.ChannelCodingShannonTheorem`
- L2: `Common2026.Shannon.ChannelCodingShannonTheoremGeneral`
- L3: `Common2026.Shannon.AEPRate`

### `Common2026/Shannon/ChannelCodingShannonTheoremGeneral.lean` (4)

- L1: `Common2026.Shannon.ChannelCoding`
- L2: `Common2026.Shannon.ChannelCodingShannonTheorem`
- L3: `Mathlib.Analysis.Convex.StdSimplex`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`

### `Common2026/Shannon/ChannelCodingStrongConverse.lean` (3)

- L1: `Common2026.Shannon.ChannelCoding`
- L2: `Common2026.Shannon.StrongStein`
- L3: `Mathlib.MeasureTheory.Constructions.Pi`

### `Common2026/Shannon/Chernoff.lean` (6)

- L1: `Common2026.Shannon.CsiszarProjection`
- L2: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L3: `Mathlib.Analysis.SpecialFunctions.Pow.Continuity`
- L4: `Mathlib.Topology.Order.Compact`
- L5: `Mathlib.Analysis.MeanInequalities`
- L6: `Mathlib.Data.Real.ConjExponents`

### `Common2026/Shannon/ChernoffNLetterZSum.lean` (3)

- L1: `Common2026.Shannon.Chernoff`
- L2: `Mathlib.Algebra.BigOperators.Ring.Finset`
- L3: `Mathlib.Data.Fintype.Pi`

### `Common2026/Shannon/CondMutualInfo.lean` (8)

- L1: `Mathlib.InformationTheory.KullbackLeibler.Basic`
- L2: `Mathlib.InformationTheory.KullbackLeibler.ChainRule`
- L3: `Mathlib.Probability.Kernel.CondDistrib`
- L4: `Mathlib.Probability.Kernel.Composition.MeasureCompProd`
- L5: `Mathlib.Probability.Kernel.Composition.CompProd`
- L6: `Mathlib.Probability.Kernel.Composition.MapComap`
- L7: `Common2026.Shannon.MutualInfo`
- L8: `Common2026.Shannon.DPI`

### `Common2026/Shannon/Converse.lean` (8)

- L1: `Common2026.Shannon.MutualInfo`
- L2: `Common2026.Shannon.DPI`
- L3: `Common2026.Shannon.Bridge`
- L4: `Common2026.Shannon.CondMutualInfo`
- L5: `Common2026.Fano.Measure`
- L6: `Mathlib.MeasureTheory.Measure.Count`
- L7: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L8: `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`

### `Common2026/Shannon/CramerLC2Discharge.lean` (5)

- L1: `Common2026.Draft.Shannon.Cramer`
- L2: `Mathlib.Probability.StrongLaw`
- L3: `Mathlib.Probability.Independence.InfinitePi`
- L4: `Mathlib.Probability.ProductMeasure`
- L5: `Mathlib.MeasureTheory.Function.ConvergenceInMeasure`

### `Common2026/Shannon/CramerLC2DischargeExt.lean` (5)

- L1: `Common2026.Shannon.CramerLC2Discharge`
- L2: `Mathlib.Probability.StrongLaw`
- L3: `Mathlib.Probability.Independence.InfinitePi`
- L4: `Mathlib.Probability.ProductMeasure`
- L5: `Mathlib.MeasureTheory.Function.ConvergenceInMeasure`

### `Common2026/Shannon/CsiszarProjection.lean` (5)

- L1: `Mathlib.InformationTheory.KullbackLeibler.KLFun`
- L2: `Mathlib.Analysis.Convex.StdSimplex`
- L3: `Mathlib.Analysis.Calculus.MeanValue`
- L4: `Mathlib.Analysis.Calculus.Deriv.Slope`
- L5: `Mathlib.Topology.Order.Compact`

### `Common2026/Shannon/DPI.lean` (11)

- L1: `Mathlib.InformationTheory.KullbackLeibler.Basic`
- L2: `Mathlib.InformationTheory.KullbackLeibler.ChainRule`
- L3: `Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv`
- L4: `Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym`
- L5: `Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen`
- L6: `Mathlib.Probability.Kernel.CondDistrib`
- L7: `Mathlib.Probability.Kernel.Composition.MeasureCompProd`
- L8: `Mathlib.Probability.Kernel.Composition.MeasureComp`
- L9: `Mathlib.Probability.Kernel.Composition.Lemmas`
- L10: `Mathlib.MeasureTheory.Measure.Prod`
- L11: `Common2026.Shannon.MutualInfo`

### `Common2026/Shannon/DifferentialEntropy.lean` (4)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.InformationTheory.KullbackLeibler.Basic`
- L3: `Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`

### `Common2026/Shannon/EPIL3Integration.lean` (16)

- L1: `Common2026.Shannon.EntropyPowerInequality`
- L2: `Common2026.Shannon.EPIPlumbing`
- L4: `Common2026.Shannon.FisherInfoV2DeBruijn`
- L5: `Common2026.Shannon.FisherInfoV2`
- L6: `Common2026.Shannon.FisherInfoGaussian`
- L7: `Common2026.Shannon.DifferentialEntropy`
- L8: `Common2026.Shannon.HeatFlowPath`
- L9: `Mathlib.Analysis.SpecialFunctions.Exp`
- L10: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L11: `Mathlib.Probability.Distributions.Gaussian.Real`
- L12: `Mathlib.Probability.Independence.Basic`
- L13: `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`
- L14: `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`
- L15: `Mathlib.MeasureTheory.Integral.Bochner.Set`
- L16: `Mathlib.Topology.Instances.EReal.Lemmas`
- L17: `Mathlib.Order.Filter.AtTopBot.Group`

### `Common2026/Shannon/EPIPlumbing.lean` (4)

- L1: `Common2026.Shannon.EntropyPowerInequality`
- L2: `Common2026.Shannon.DifferentialEntropy`
- L3: `Mathlib.Analysis.SpecialFunctions.Exp`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.Basic`

### `Common2026/Shannon/EPIStamDischarge.lean` (11)

- L1: `Common2026.Shannon.EntropyPowerInequality`
- L2: `Common2026.Shannon.EPIPlumbing`
- L3: `Common2026.Shannon.FisherInfoV2`
- L4: `Common2026.Shannon.FisherInfoV2DeBruijn`
- L5: `Common2026.Shannon.FisherInfoGaussian`
- L6: `Common2026.Shannon.DifferentialEntropy`
- L7: `Mathlib.Analysis.SpecialFunctions.Exp`
- L8: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L9: `Mathlib.Probability.Distributions.Gaussian.Real`
- L10: `Mathlib.Probability.Independence.Basic`
- L11: `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`

### `Common2026/Shannon/EPIStamInequalityBody.lean` (13)

- L1: `Common2026.Shannon.EntropyPowerInequality`
- L2: `Common2026.Shannon.EPIPlumbing`
- L3: `Common2026.Shannon.EPIStamDischarge`
- L4: `Common2026.Shannon.EPIL3Integration`
- L5: `Common2026.Shannon.FisherInfoV2`
- L6: `Common2026.Shannon.FisherInfoV2DeBruijn`
- L7: `Common2026.Shannon.FisherInfoGaussian`
- L8: `Common2026.Shannon.DifferentialEntropy`
- L9: `Mathlib.Analysis.SpecialFunctions.Exp`
- L10: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L11: `Mathlib.Probability.Distributions.Gaussian.Real`
- L12: `Mathlib.Probability.Independence.Basic`
- L13: `Mathlib.Analysis.InnerProductSpace.Basic`

### `Common2026/Shannon/EPIStamStep12Body.lean` (7)

- L1: `Common2026.Shannon.EPIStamInequalityBody`
- L2: `Common2026.Shannon.EPIStamDischarge`
- L3: `Common2026.Shannon.FisherInfoV2`
- L4: `Common2026.Shannon.FisherInfoV2DeBruijn`
- L5: `Mathlib.Tactic.Positivity`
- L6: `Mathlib.Tactic.Linarith`
- L7: `Mathlib.Tactic.Ring`

### `Common2026/Shannon/EPIStamStep3Body.lean` (11)

- L1: `Common2026.Shannon.EntropyPowerInequality`
- L2: `Common2026.Shannon.EPIPlumbing`
- L3: `Common2026.Shannon.EPIStamDischarge`
- L4: `Common2026.Shannon.EPIStamInequalityBody`
- L5: `Common2026.Shannon.FisherInfoV2`
- L6: `Common2026.Shannon.FisherInfoV2DeBruijn`
- L7: `Common2026.Shannon.FisherInfoGaussian`
- L8: `Mathlib.Analysis.SpecialFunctions.Exp`
- L9: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L10: `Mathlib.Probability.Distributions.Gaussian.Real`
- L11: `Mathlib.Probability.Independence.Basic`

### `Common2026/Shannon/EPIStamToBridge.lean` (12)

- L1: `Common2026.Shannon.EntropyPowerInequality`
- L2: `Common2026.Shannon.EPIStamDischarge`
- L3: `Common2026.Shannon.EPIL3Integration`
- L4: `Common2026.Shannon.EPIPlumbing`
- L5: `Common2026.Shannon.DifferentialEntropy`
- L6: `Common2026.Shannon.HeatFlowPath`
- L7: `Mathlib.Analysis.SpecialFunctions.Exp`
- L8: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L9: `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`
- L11: `Mathlib.Probability.Independence.Basic`
- L12: `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`
- L13: `Mathlib.Order.Monotone.Basic`

### `Common2026/Shannon/Entropy.lean` (2)

- L1: `Common2026.Shannon.Bridge`
- L2: `Common2026.Shannon.CondMutualInfo`

### `Common2026/Shannon/EntropyPowerInequality.lean` (7)

- L1: `Common2026.Shannon.DifferentialEntropy`
- L2: `Common2026.Shannon.FisherInfo`
- L3: `Common2026.Shannon.FisherInfoV2`
- L4: `Mathlib.Analysis.SpecialFunctions.Exp`
- L5: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L6: `Mathlib.Probability.Distributions.Gaussian.Real`
- L7: `Mathlib.Probability.Independence.Basic`

### `Common2026/Shannon/EntropyRate.lean` (7)

- L1: `Common2026.Shannon.Stationary`
- L2: `Common2026.Shannon.Bridge`
- L3: `Common2026.Shannon.CondMutualInfo`
- L4: `Common2026.Shannon.Pi`
- L5: `Mathlib.Analysis.Asymptotics.SpecificAsymptotics`
- L6: `Mathlib.Topology.Order.MonotoneConvergence`
- L7: `Mathlib.Order.Filter.AtTopBot.CompleteLattice`

### `Common2026/Shannon/FisherDeBruijnGaussianWitness.lean` (5)

- L1: `Common2026.Shannon.FisherInfoV2`
- L2: `Common2026.Shannon.FisherInfoV2DeBruijn`
- L3: `Common2026.Shannon.FisherInfoV2DeBruijnBody`
- L4: `Common2026.Shannon.FisherInfoV2HeatFlowBody`
- L5: `Common2026.Shannon.GaussianPDFVarianceDerivBody`

### `Common2026/Shannon/FisherInfo.lean` (7)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.Probability.Density`
- L3: `Mathlib.Analysis.Calculus.LogDeriv`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.Deriv`
- L5: `Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue`
- L6: `Mathlib.MeasureTheory.Measure.Dirac`
- L7: `Common2026.Shannon.DifferentialEntropy`

### `Common2026/Shannon/FisherInfoGaussian.lean` (7)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.Probability.Density`
- L3: `Mathlib.Probability.Independence.Basic`
- L4: `Mathlib.Analysis.Calculus.LogDeriv`
- L5: `Mathlib.Analysis.SpecialFunctions.Log.Deriv`
- L6: `Common2026.Shannon.FisherInfo`
- L7: `Common2026.Shannon.DifferentialEntropy`

### `Common2026/Shannon/FisherInfoV2.lean` (11)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.Probability.Density`
- L3: `Mathlib.Probability.Moments.Variance`
- L4: `Mathlib.Analysis.Calculus.LogDeriv`
- L5: `Mathlib.Analysis.SpecialFunctions.Log.Deriv`
- L6: `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`
- L7: `Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue`
- L8: `Mathlib.MeasureTheory.Measure.Dirac`
- L9: `Common2026.Shannon.FisherInfo`
- L10: `Common2026.Shannon.FisherInfoGaussian`
- L11: `Common2026.Shannon.DifferentialEntropy`

### `Common2026/Shannon/FisherInfoV2DeBruijn.lean` (11)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.Probability.Density`
- L3: `Mathlib.Probability.Independence.Basic`
- L4: `Mathlib.Analysis.Calculus.LogDeriv`
- L5: `Mathlib.Analysis.SpecialFunctions.Log.Deriv`
- L6: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L7: `Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue`
- L8: `Common2026.Shannon.FisherInfo`
- L9: `Common2026.Shannon.FisherInfoGaussian`
- L11: `Common2026.Shannon.DifferentialEntropy`
- L12: `Common2026.Shannon.EntropyPowerInequality`

### `Common2026/Shannon/FisherInfoV2DeBruijnBody.lean` (11)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.Deriv`
- L4: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L5: `Mathlib.Analysis.Calculus.Deriv.Add`
- L6: `Mathlib.Analysis.Calculus.Deriv.Mul`
- L7: `Mathlib.Analysis.Calculus.Deriv.Comp`
- L8: `Mathlib.Analysis.Calculus.LogDeriv`
- L9: `Common2026.Shannon.FisherInfoV2`
- L10: `Common2026.Shannon.FisherInfoV2DeBruijn`
- L11: `Common2026.Shannon.DifferentialEntropy`

### `Common2026/Shannon/FisherInfoV2HeatFlowBody.lean` (13)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.Deriv`
- L4: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L5: `Mathlib.Analysis.Calculus.Deriv.Add`
- L6: `Mathlib.Analysis.Calculus.Deriv.Mul`
- L7: `Mathlib.Analysis.Calculus.Deriv.Comp`
- L8: `Mathlib.Analysis.Calculus.LogDeriv`
- L9: `Common2026.Shannon.FisherInfoV2`
- L10: `Common2026.Shannon.FisherInfoV2DeBruijn`
- L11: `Common2026.Shannon.FisherInfoV2DeBruijnBody`
- L12: `Common2026.Shannon.FisherInfoGaussian`
- L13: `Common2026.Shannon.DifferentialEntropy`

### `Common2026/Shannon/GaussianPDFVarianceDerivBody.lean` (10)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.Analysis.SpecialFunctions.Sqrt`
- L3: `Mathlib.Analysis.SpecialFunctions.ExpDeriv`
- L4: `Mathlib.Analysis.Calculus.Deriv.Inv`
- L5: `Mathlib.Analysis.Calculus.Deriv.Mul`
- L6: `Mathlib.Analysis.Calculus.Deriv.Add`
- L7: `Mathlib.Analysis.Calculus.Deriv.Comp`
- L8: `Common2026.Shannon.FisherInfoGaussian`
- L9: `Common2026.Shannon.FisherInfoV2DeBruijnBody`
- L10: `Common2026.Shannon.FisherInfoV2HeatFlowBody`

### `Common2026/Shannon/GeneralDMC.lean` (2)

- L1: `Common2026.Shannon.BlockwiseChannel`
- L2: `Mathlib.Analysis.Subadditive`

### `Common2026/Shannon/Han.lean` (2)

- L1: `Common2026.Shannon.Entropy`
- L2: `Common2026.Shannon.Pi`

### `Common2026/Shannon/HanD.lean` (1)

- L1: `Common2026.Shannon.Han`

### `Common2026/Shannon/HanDAverage.lean` (1)

- L1: `Common2026.Shannon.HanD`

### `Common2026/Shannon/HanDShearer.lean` (1)

- L1: `Common2026.Shannon.HanD`

### `Common2026/Shannon/HeatFlowPath.lean` (7)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.Probability.Independence.Basic`
- L3: `Mathlib.MeasureTheory.MeasurableSpace.Basic`
- L4: `Mathlib.MeasureTheory.Group.Convolution`
- L5: `Mathlib.Analysis.SpecialFunctions.Sqrt`
- L6: `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`
- L7: `Common2026.Shannon.FisherInfoV2DeBruijn`

### `Common2026/Shannon/HoeffdingSandwich.lean` (4)

- L1: `Common2026.Shannon.HoeffdingTradeoff`
- L2: `Common2026.Shannon.Chernoff`
- L3: `Mathlib.Topology.Order.LiminfLimsup`
- L4: `Mathlib.Order.Filter.IsBounded`

### `Common2026/Shannon/HoeffdingTradeoff.lean` (9)

- L1: `Common2026.Shannon.Chernoff`
- L2: `Common2026.Shannon.CsiszarProjection`
- L3: `Common2026.Shannon.KLDivContinuous`
- L4: `Common2026.Shannon.SanovLDPEquality`
- L5: `Common2026.InformationTheory.Asymptotic`
- L6: `Mathlib.Probability.ProbabilityMassFunction.Basic`
- L7: `Mathlib.Probability.ProbabilityMassFunction.Constructions`
- L8: `Mathlib.Topology.Order.Compact`
- L9: `Mathlib.Topology.Order.LiminfLimsup`

### `Common2026/Shannon/Huffman.lean` (11)

- L1: `Mathlib.Analysis.SpecialFunctions.Log.Base`
- L2: `Mathlib.MeasureTheory.Measure.Real`
- L3: `Mathlib.Data.Multiset.Basic`
- L4: `Mathlib.Data.Multiset.Sort`
- L5: `Mathlib.Data.Finset.Max`
- L6: `Mathlib.Data.Finset.Image`
- L7: `Mathlib.Combinatorics.Colex`
- L9: `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- L10: `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- L11: `Common2026.Shannon.ShannonCode`
- L12: `Common2026.Shannon.ShannonCodeKraftReverse`

### `Common2026/Shannon/HuffmanColexDeterminism.lean` (1)

- L1: `Common2026.Shannon.HuffmanMergedAuxIdent`

### `Common2026/Shannon/HuffmanFirstStepProbe.lean` (1)

- L1: `Common2026.Shannon.HuffmanColexDeterminism`

### `Common2026/Shannon/HuffmanMergedAuxIdent.lean` (4)

- L1: `Mathlib.Logic.Equiv.Basic`
- L2: `Mathlib.Data.Multiset.MapFold`
- L3: `Mathlib.Tactic.Linarith`
- L4: `Common2026.Shannon.HuffmanMergedIdentBody`

### `Common2026/Shannon/HuffmanMergedIdentBody.lean` (2)

- L1: `Mathlib.Logic.Equiv.Basic`
- L2: `Common2026.Shannon.HuffmanOptimality`

### `Common2026/Shannon/HuffmanOptimality.lean` (8)

- L1: `Mathlib.Logic.Equiv.Basic`
- L2: `Mathlib.Logic.Function.Basic`
- L3: `Mathlib.Data.Finset.Max`
- L4: `Mathlib.Data.Finset.Image`
- L5: `Mathlib.Data.Fintype.EquivFin`
- L6: `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- L7: `Mathlib.MeasureTheory.Measure.Real`
- L8: `Common2026.Shannon.Huffman`

### `Common2026/Shannon/HuffmanStrongForm.lean` (3)

- L1: `Common2026.Shannon.HuffmanOptimality`
- L2: `Common2026.Shannon.HuffmanSwapNormCompletion`
- L3: `Common2026.Shannon.HuffmanMergedIdentBody`

### `Common2026/Shannon/HuffmanSwapNormCompletion.lean` (10)

- L1: `Mathlib.Data.Real.Basic`
- L2: `Mathlib.Data.Finset.Max`
- L3: `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- L4: `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise`
- L5: `Mathlib.Algebra.BigOperators.Field`
- L6: `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- L7: `Mathlib.Tactic.Positivity`
- L8: `Mathlib.Tactic.Ring`
- L9: `Mathlib.Tactic.Linarith`
- L10: `Common2026.Shannon.HuffmanSwapNormProof`

### `Common2026/Shannon/HuffmanSwapNormProof.lean` (10)

- L1: `Mathlib.Data.Real.Basic`
- L2: `Mathlib.Data.Finset.Max`
- L3: `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- L4: `Mathlib.Algebra.BigOperators.Group.Finset.Lemmas`
- L5: `Mathlib.Algebra.BigOperators.Field`
- L6: `Mathlib.Algebra.BigOperators.Ring.Finset`
- L7: `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- L8: `Mathlib.Algebra.Ring.Parity`
- L9: `Mathlib.Tactic.Push`
- L10: `Mathlib.Tactic.Ring`

### `Common2026/Shannon/HuffmanSwapNormalizationBody.lean` (5)

- L1: `Mathlib.Logic.Equiv.Basic`
- L2: `Common2026.Shannon.HuffmanOptimality`
- L3: `Common2026.Shannon.HuffmanT1APPrimePartial`
- L4: `Common2026.Shannon.HuffmanT1APPrimeBody`
- L5: `Common2026.Shannon.HuffmanSwapStepChainBody`

### `Common2026/Shannon/HuffmanSwapStepChainBody.lean` (4)

- L1: `Mathlib.Logic.Equiv.Basic`
- L2: `Common2026.Shannon.HuffmanOptimality`
- L3: `Common2026.Shannon.HuffmanT1APPrimePartial`
- L4: `Common2026.Shannon.HuffmanT1APPrimeBody`

### `Common2026/Shannon/HuffmanT1APPrimeBody.lean` (3)

- L1: `Mathlib.Logic.Equiv.Basic`
- L2: `Common2026.Shannon.HuffmanOptimality`
- L3: `Common2026.Shannon.HuffmanT1APPrimePartial`

### `Common2026/Shannon/HuffmanT1APPrimePartial.lean` (2)

- L1: `Mathlib.Logic.Equiv.Basic`
- L2: `Common2026.Shannon.HuffmanOptimality`

### `Common2026/Shannon/HypercubeEdgeBoundary.lean` (1)

- L1: `Common2026.Shannon.LoomisWhitney`

### `Common2026/Shannon/HypercubeEdgeBoundarySharp.lean` (3)

- L1: `Common2026.Shannon.HypercubeEdgeBoundary`
- L2: `Common2026.Shannon.HanD`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.Base`

### `Common2026/Shannon/IIDProductInput.lean` (3)

- L1: `Common2026.Shannon.ChannelCoding`
- L2: `Mathlib.Probability.ProductMeasure`
- L3: `Mathlib.Probability.Independence.InfinitePi`

### `Common2026/Shannon/IIDProductInputJoint.lean` (1)

- L1: `Common2026.Shannon.IIDProductInput`

### `Common2026/Shannon/KLDivContinuous.lean` (3)

- L1: `Common2026.Shannon.SanovLDP`
- L2: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L3: `Mathlib.Topology.Algebra.Monoid`

### `Common2026/Shannon/LZ78ConverseAsymptotic.lean` (5)

- L1: `Common2026.Shannon.LempelZiv78`
- L2: `Common2026.Shannon.LZ78ZivInequality`
- L3: `Mathlib.Analysis.Asymptotics.Defs`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L5: `Mathlib.Order.Filter.AtTopBot.Basic`

### `Common2026/Shannon/LZ78ConverseUDObject.lean` (4)

- L1: `Common2026.Shannon.McMillanKraftBridge`
- L2: `Common2026.Shannon.LZ78GreedyParsing`
- L3: `Mathlib.Data.Nat.Bitwise`
- L4: `Mathlib.Data.Nat.Log`

### `Common2026/Shannon/LZ78GreedyLongestPrefix.lean` (5)

- L1: `Common2026.Shannon.LempelZiv78`
- L2: `Common2026.Shannon.LZ78GreedyParsing`
- L3: `Common2026.Shannon.LZ78GreedyParsingImpl`
- L4: `Mathlib.Data.List.Nodup`
- L5: `Mathlib.Data.List.Basic`

### `Common2026/Shannon/LZ78GreedyParsing.lean` (5)

- L1: `Common2026.Shannon.LempelZiv78`
- L2: `Common2026.Shannon.LZ78ZivInequality`
- L3: `Mathlib.Data.Nat.Log`
- L4: `Mathlib.Data.List.Basic`
- L5: `Mathlib.Data.List.Range`

### `Common2026/Shannon/LZ78GreedyParsingImpl.lean` (5)

- L1: `Common2026.Shannon.LempelZiv78`
- L2: `Common2026.Shannon.LZ78GreedyParsing`
- L3: `Mathlib.Data.Nat.Log`
- L4: `Mathlib.Data.List.Basic`
- L5: `Mathlib.Data.List.Range`

### `Common2026/Shannon/LZ78PhraseCountAsymptoticBody.lean` (7)

- L1: `Common2026.Shannon.LempelZiv78`
- L2: `Common2026.Shannon.LZ78ZivInequality`
- L3: `Common2026.Shannon.LZ78ConverseAsymptotic`
- L4: `Mathlib.Analysis.Asymptotics.Defs`
- L5: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L6: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L7: `Mathlib.Order.Filter.AtTopBot.Basic`

### `Common2026/Shannon/LZ78ZivCountingBody.lean` (9)

- L1: `Common2026.Shannon.LZ78GreedyLongestPrefix`
- L2: `Common2026.Shannon.LZ78PhraseCountAsymptoticBody`
- L3: `Mathlib.Data.Nat.Log`
- L4: `Mathlib.Data.List.Nodup`
- L5: `Mathlib.Data.Fintype.Card`
- L6: `Mathlib.Data.Fintype.Pi`
- L7: `Mathlib.Algebra.BigOperators.Group.List.Basic`
- L8: `Mathlib.Algebra.Order.BigOperators.Group.List`
- L9: `Mathlib.Analysis.SpecialFunctions.Log.Basic`

### `Common2026/Shannon/LZ78ZivEntropyBridge.lean` (4)

- L1: `Common2026.Shannon.ShannonMcMillanBreiman`
- L2: `Common2026.Shannon.LZ78GreedyLongestPrefix`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L4: `Mathlib.Analysis.Convex.Jensen`

### `Common2026/Shannon/LZ78ZivInequality.lean` (6)

- L1: `Common2026.Shannon.LempelZiv78`
- L2: `Mathlib.Data.Finset.Card`
- L3: `Mathlib.Data.Finset.Image`
- L4: `Mathlib.Data.Fintype.Card`
- L5: `Mathlib.Data.Fintype.Option`
- L6: `Mathlib.Data.Fintype.Prod`

### `Common2026/Shannon/LempelZiv78.lean` (5)

- L1: `Common2026.Shannon.Stationary`
- L2: `Common2026.Shannon.EntropyRate`
- L3: `Common2026.Shannon.ShannonMcMillanBreiman`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L5: `Mathlib.Topology.Order.LiminfLimsup`

### `Common2026/Shannon/LoomisWhitney.lean` (2)

- L1: `Common2026.Shannon.HanDShearer`
- L2: `Mathlib.Probability.UniformOn`

### `Common2026/Shannon/MACCornerAchievabilityBody.lean` (3)

- L1: `Common2026.Draft.Shannon.MACBodyDischarge`
- L2: `Common2026.Draft.Shannon.MACL1Discharge`
- L3: `Common2026.Shannon.AEPRate`

### `Common2026/Shannon/MACRandomCodebookAveraging.lean` (1)

- L1: `Common2026.Shannon.MACCornerAchievabilityBody`

### `Common2026/Shannon/MACTimeSharingBody.lean` (1)

- L1: `Common2026.Draft.Shannon.MACCornerPoint`

### `Common2026/Shannon/MIChainRule.lean` (3)

- L1: `Common2026.Shannon.MutualInfo`
- L2: `Common2026.Shannon.CondMutualInfo`
- L3: `Common2026.Shannon.Entropy`

### `Common2026/Shannon/MaxEntropy.lean` (2)

- L1: `Common2026.Shannon.Bridge`
- L2: `Mathlib.Probability.UniformOn`

### `Common2026/Shannon/MaxEntropyConstrained.lean` (4)

- L1: `Common2026.Shannon.CsiszarProjection`
- L2: `Common2026.Shannon.Chernoff`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L4: `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`

### `Common2026/Shannon/MaxEntropyConstrainedKKT.lean` (1)

- L1: `Common2026.Shannon.MaxEntropyConstrained`

### `Common2026/Shannon/McMillanKraftBridge.lean` (3)

- L1: `Common2026.Shannon.ShannonCode`
- L2: `Mathlib.InformationTheory.Coding.KraftMcMillan`
- L3: `Mathlib.InformationTheory.Coding.UniquelyDecodable`

### `Common2026/Shannon/MeasurePiTiltedFactorization.lean` (5)

- L1: `Mathlib.MeasureTheory.Constructions.Pi`
- L2: `Mathlib.MeasureTheory.Integral.Pi`
- L3: `Mathlib.MeasureTheory.Measure.Tilted`
- L4: `Mathlib.MeasureTheory.Measure.WithDensity`
- L5: `Mathlib.Probability.Moments.Basic`

### `Common2026/Shannon/MutualInfo.lean` (5)

- L1: `Mathlib.InformationTheory.KullbackLeibler.Basic`
- L2: `Mathlib.InformationTheory.KullbackLeibler.ChainRule`
- L3: `Mathlib.Probability.Independence.Basic`
- L4: `Mathlib.Probability.Kernel.CondDistrib`
- L5: `Mathlib.Probability.Kernel.Composition.MeasureCompProd`

### `Common2026/Shannon/ParallelGaussian.lean` (6)

- L1: `Common2026.Shannon.AWGN`
- L2: `Common2026.Shannon.AWGNMain`
- L3: `Common2026.Shannon.ChannelCoding`
- L4: `Common2026.Shannon.DifferentialEntropy`
- L5: `Mathlib.MeasureTheory.Constructions.Pi`
- L6: `Mathlib.Probability.Distributions.Gaussian.Real`

### `Common2026/Shannon/ParallelGaussianKKT.lean` (7)

- L1: `Common2026.Shannon.ParallelGaussian`
- L2: `Common2026.Shannon.ParallelGaussianL_PG0Discharge`
- L3: `Mathlib.Topology.Order.IntermediateValue`
- L4: `Mathlib.Topology.Algebra.Monoid`
- L5: `Mathlib.Topology.Algebra.Group.Defs`
- L6: `Mathlib.Topology.Order.OrderClosed`
- L7: `Mathlib.Analysis.Convex.SpecificFunctions.Basic`

### `Common2026/Shannon/ParallelGaussianL_PG0Discharge.lean` (1)

- L1: `Common2026.Shannon.ParallelGaussian`

### `Common2026/Shannon/Pi.lean` (1)

- L1: `Common2026.Shannon.Entropy`

### `Common2026/Shannon/Pinsker.lean` (4)

- L1: `Common2026.Shannon.Bridge`
- L2: `Mathlib.Data.Real.Sqrt`
- L3: `Mathlib.Algebra.Order.BigOperators.Ring.Finset`
- L4: `Mathlib.InformationTheory.KullbackLeibler.KLFun`

### `Common2026/Shannon/PinskerSharp.lean` (4)

- L1: `Common2026.Shannon.Pinsker`
- L2: `Mathlib.Analysis.Calculus.Deriv.MeanValue`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.Basic`

### `Common2026/Shannon/Polymatroid.lean` (2)

- L1: `Common2026.Polymatroid.Basic`
- L2: `Common2026.Shannon.HanD`

### `Common2026/Shannon/RateDistortionAchievability.lean` (4)

- L1: `Common2026.Shannon.RateDistortionConverse`
- L2: `Mathlib.Analysis.Convex.StdSimplex`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L4: `Mathlib.Topology.Order.Compact`

### `Common2026/Shannon/RateDistortionAchievabilityPhaseB.lean` (5)

- L1: `Common2026.Shannon.RateDistortionAchievability`
- L2: `Common2026.Shannon.ChannelCodingAchievability`
- L3: `Common2026.Shannon.AEP`
- L4: `Mathlib.MeasureTheory.Function.ConvergenceInMeasure`
- L5: `Mathlib.Probability.StrongLaw`

### `Common2026/Shannon/RateDistortionAchievabilityPhaseC.lean` (1)

- L1: `Common2026.Shannon.RateDistortionAchievabilityPhaseB`

### `Common2026/Shannon/RateDistortionAchievabilityPhaseD.lean` (3)

- L1: `Common2026.Shannon.RateDistortionAchievabilityPhaseC`
- L2: `Mathlib.Analysis.SpecialFunctions.Exp`
- L3: `Mathlib.Order.Filter.AtTopBot.Basic`

### `Common2026/Shannon/RateDistortionConverse.lean` (6)

- L1: `Common2026.Shannon.MutualInfo`
- L2: `Common2026.Shannon.DPI`
- L3: `Common2026.Shannon.Bridge`
- L4: `Common2026.Shannon.MaxEntropy`
- L5: `Common2026.Shannon.Pi`
- L6: `Common2026.Fano.Measure`

### `Common2026/Shannon/RateDistortionConverseMonotone.lean` (1)

- L1: `Common2026.Shannon.RateDistortionConverse`

### `Common2026/Shannon/RateDistortionConvexityDischarge.lean` (3)

- L1: `Common2026.Draft.Shannon.RateDistortionConvexity`
- L2: `Common2026.Shannon.Sanov`
- L3: `Mathlib.InformationTheory.KullbackLeibler.KLFun`

### `Common2026/Shannon/SMBAlgoetCover.lean` (7)

- L1: `Common2026.Shannon.SMBChainRule`
- L2: `Common2026.Shannon.ShannonMcMillanBreiman`
- L3: `Common2026.Probability.TwoSidedExtension`
- L4: `Mathlib.MeasureTheory.OuterMeasure.BorelCantelli`
- L5: `Mathlib.MeasureTheory.Integral.Lebesgue.Markov`
- L6: `Mathlib.Analysis.PSeries`
- L7: `Mathlib.Topology.Algebra.Order.LiminfLimsup`

### `Common2026/Shannon/SMBChainRule.lean` (5)

- L1: `Common2026.Shannon.Stationary`
- L2: `Common2026.Shannon.EntropyRate`
- L3: `Common2026.Shannon.BirkhoffErgodic`
- L4: `Mathlib.Probability.Kernel.CondDistrib`
- L5: `Mathlib.MeasureTheory.Integral.Lebesgue.Countable`

### `Common2026/Shannon/Sanov.lean` (2)

- L1: `Common2026.Shannon.Stein`
- L2: `Mathlib.InformationTheory.KullbackLeibler.Basic`

### `Common2026/Shannon/SanovLDP.lean` (3)

- L1: `Common2026.Shannon.Sanov`
- L2: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L3: `Mathlib.Analysis.Asymptotics.Lemmas`

### `Common2026/Shannon/SanovLDPEquality.lean` (5)

- L1: `Common2026.Shannon.SanovLDP`
- L2: `Common2026.Shannon.KLDivContinuous`
- L3: `Mathlib.Algebra.Order.Floor.Semiring`
- L4: `Mathlib.Algebra.BigOperators.Fin`
- L5: `Mathlib.Data.Nat.Choose.Multinomial`

### `Common2026/Shannon/ShannonCode.lean` (4)

- L1: `Mathlib.Analysis.SpecialFunctions.Log.Base`
- L2: `Mathlib.MeasureTheory.Measure.Real`
- L3: `Mathlib.Probability.ProbabilityMassFunction.Basic`
- L4: `Mathlib.Algebra.Order.Floor.Semiring`

### `Common2026/Shannon/ShannonCodeKraftReverse.lean` (6)

- L1: `Mathlib.Data.List.OfFn`
- L2: `Mathlib.Data.List.Sort`
- L3: `Mathlib.Data.Finset.Dedup`
- L4: `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- L5: `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- L6: `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`

### `Common2026/Shannon/ShannonHartley.lean` (8)

- L1: `Common2026.Shannon.AWGN`
- L2: `Common2026.Shannon.AWGNAchievability`
- L3: `Common2026.Shannon.AWGNConverse`
- L4: `Common2026.Shannon.AWGNMain`
- L5: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L6: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L7: `Mathlib.Analysis.SpecialFunctions.Complex.LogBounds`
- L8: `Mathlib.Topology.Algebra.Order.LiminfLimsup`

### `Common2026/Shannon/ShannonMcMillanBreiman.lean` (4)

- L1: `Common2026.Shannon.Stationary`
- L2: `Common2026.Shannon.EntropyRate`
- L3: `Common2026.Shannon.Bridge`
- L4: `Mathlib.Topology.Order.LiminfLimsup`

### `Common2026/Shannon/SlepianWolf.lean` (7)

- L1: `Common2026.Shannon.Bridge`
- L2: `Common2026.Shannon.CondMutualInfo`
- L3: `Common2026.Shannon.DPI`
- L4: `Common2026.Shannon.Entropy`
- L5: `Common2026.Shannon.Pi`
- L6: `Common2026.Fano.Measure`
- L7: `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`

### `Common2026/Shannon/SlepianWolfAchievability.lean` (2)

- L1: `Common2026.Shannon.SlepianWolf`
- L2: `Common2026.Shannon.AEP`

### `Common2026/Shannon/SlepianWolfBinning.lean` (3)

- L1: `Common2026.Shannon.SlepianWolfAchievability`
- L2: `Mathlib.Probability.UniformOn`
- L3: `Mathlib.MeasureTheory.Constructions.Pi`

### `Common2026/Shannon/SlepianWolfConditionalTypicalSlice.lean` (2)

- L1: `Common2026.Shannon.AEP`
- L2: `Common2026.Shannon.ChannelCoding`

### `Common2026/Shannon/SlepianWolfFullRateRegion.lean` (3)

- L1: `Common2026.Shannon.SlepianWolfBinning`
- L2: `Common2026.Shannon.SlepianWolfConditionalTypicalSlice`
- L3: `Common2026.Shannon.SlepianWolfAchievability`

### `Common2026/Shannon/StamGaussianBound.lean` (4)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.Probability.Independence.Basic`
- L3: `Mathlib.Tactic.Positivity`
- L4: `Common2026.Shannon.FisherInfoV2DeBruijn`

### `Common2026/Shannon/Stationary.lean` (4)

- L1: `Mathlib.Dynamics.Ergodic.Ergodic`
- L2: `Mathlib.Dynamics.Ergodic.MeasurePreserving`
- L3: `Mathlib.Probability.IdentDistrib`
- L4: `Mathlib.MeasureTheory.MeasurableSpace.Basic`

### `Common2026/Shannon/StationaryKernel.lean` (4)

- L1: `Common2026.Shannon.LZ78ZivEntropyBridge`
- L2: `Common2026.Shannon.LZ78ZivCountingBody`
- L3: `Common2026.Shannon.EntropyRate`
- L4: `Mathlib.Algebra.BigOperators.Group.Finset.Basic`

### `Common2026/Shannon/Stein.lean` (7)

- L1: `Common2026.Shannon.AEP`
- L2: `Common2026.Shannon.DPI`
- L3: `Common2026.Shannon.MutualInfo`
- L4: `Mathlib.InformationTheory.KullbackLeibler.Basic`
- L5: `Mathlib.InformationTheory.KullbackLeibler.ChainRule`
- L6: `Mathlib.MeasureTheory.Constructions.Pi`
- L7: `Mathlib.Probability.Kernel.Composition.MeasureCompProd`

### `Common2026/Shannon/StrongStein.lean` (2)

- L1: `Common2026.Shannon.Stein`
- L2: `Mathlib.Topology.Order.LiminfLimsup`

### `Common2026/Shannon/StrongTypicality.lean` (3)

- L1: `Common2026.Shannon.AEP`
- L2: `Common2026.Shannon.Sanov`
- L3: `Mathlib.MeasureTheory.Order.Group.Lattice`

### `Common2026/Shannon/TypeClassLowerBound.lean` (1)

- L1: `Common2026.Shannon.SanovLDPEquality`

### `Common2026/Shannon/TypedRV.lean` (7)

- L1: `Common2026.Shannon.Bridge`
- L2: `Common2026.Shannon.MutualInfo`
- L3: `Common2026.Shannon.CondMutualInfo`
- L4: `Common2026.Shannon.DPI`
- L5: `Common2026.Shannon.SlepianWolf`
- L6: `Common2026.Fano.Measure`
- L8: `Mathlib.InformationTheory.KullbackLeibler.Basic`

### `Common2026/Shannon/WhittakerShannonPartial.lean` (3)

- L1: `Common2026.Shannon.ShannonHartley`
- L3: `Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc`
- L4: `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`

### `Common2026/Shannon/WynerZiv.lean` (2)

- L1: `Common2026.Shannon.RateDistortionAchievability`
- L2: `Common2026.Draft.Shannon.RateDistortionConverseNLetter`

### `Common2026/Shannon/WynerZivBinningBody.lean` (4)

- L1: `Common2026.Shannon.WynerZiv`
- L2: `Common2026.Draft.Shannon.WynerZivAchievability`
- L3: `Common2026.Shannon.SlepianWolfBinning`
- L4: `Common2026.Shannon.SlepianWolfFullRateRegion`

### `Common2026/Shannon/WynerZivConvexityBody.lean` (1)

- L1: `Common2026.Shannon.WynerZivDischarge`

### `Common2026/Shannon/WynerZivDischarge.lean` (1)

- L1: `Common2026.Shannon.WynerZiv`

## Missing import candidates

linter が「これらを追加 import すべき」と報告した module。多くは `Lean.Parser.Command` 等の **linter 自身の elaboration を満たすための内部要件** で実用上は無視可能ですが、Common2026 内部 module の名前があれば本物の不足の可能性。

### `Common2026/Draft/Shannon/BroadcastChannel.lean` (2)

- `Mathlib.Data.ENNReal.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Draft/Shannon/BroadcastChannelSuperposition.lean` (1)

- `Common2026.Shannon.ChannelCoding`

### `Common2026/Draft/Shannon/BroadcastChannelSuperpositionBody.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Draft/Shannon/BrunnMinkowski.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Draft/Shannon/BrunnMinkowskiConcavity.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Draft/Shannon/BrunnMinkowskiFunctional.lean` (2)

- `Mathlib.MeasureTheory.Constructions.BorelSpace.Basic`
- `Mathlib.MeasureTheory.Measure.Typeclasses.Probability`

### `Common2026/Draft/Shannon/ChannelCodingConverseGeneralComplete.lean` (1)

- `Mathlib.MeasureTheory.Constructions.Polish.Basic`

### `Common2026/Draft/Shannon/ChernoffBandMassDischarge.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Draft/Shannon/ChernoffConverse.lean` (3)

- `Mathlib.Data.Finset.Defs`
- `Mathlib.Data.Real.Basic`
- `Mathlib.Order.Filter.Defs`

### `Common2026/Draft/Shannon/ChernoffInformation.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Draft/Shannon/ChernoffPerTiltDischarge.lean` (1)

- `Mathlib.Data.Fintype.Defs`

### `Common2026/Draft/Shannon/ChernoffPerTiltSanov.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Draft/Shannon/ChernoffSanovDischarge.lean` (3)

- `Mathlib.Data.Finset.Defs`
- `Mathlib.Data.Real.Basic`
- `Mathlib.Order.Filter.Defs`

### `Common2026/Draft/Shannon/Cramer.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Draft/Shannon/CramerCLTClosure.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Draft/Shannon/CramerLC2PhaseC.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Draft/Shannon/CramerPhaseDGapWorkaround.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Draft/Shannon/EPIConvolutionDensity.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Draft/Shannon/InfinitePiTiltedChangeOfMeasure.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Draft/Shannon/LZ78ConverseDischarge.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Draft/Shannon/LZ78DistinctEncoding.lean` (2)

- `Mathlib.Data.ENNReal.Basic`
- `Mathlib.Data.Fintype.Defs`

### `Common2026/Draft/Shannon/LZ78FinalGlue.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Draft/Shannon/LZ78SMBSandwich.lean` (2)

- `Mathlib.Data.ENNReal.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Draft/Shannon/MACCornerPoint.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Draft/Shannon/MACFanoConverseBody.lean` (2)

- `Mathlib.Data.ENNReal.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Draft/Shannon/MACL1Discharge.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Draft/Shannon/MACL2Discharge.lean` (2)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`
- `Mathlib.Analysis.SpecialFunctions.Log.Basic`

### `Common2026/Draft/Shannon/MACPerEventAEPDecay.lean` (2)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`
- `Mathlib.Order.Filter.Defs`

### `Common2026/Draft/Shannon/MultipleAccessChannel.lean` (2)

- `Mathlib.Data.Real.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Draft/Shannon/MultivariateDiffEntropy.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Draft/Shannon/RateDistortionAchievabilityPhaseE.lean` (1)

- `Mathlib.Order.Filter.Defs`

### `Common2026/Draft/Shannon/RateDistortionConverseNLetter.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Draft/Shannon/RateDistortionConvexity.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Draft/Shannon/RelayCutset.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Draft/Shannon/RelayInnerBound.lean` (2)

- `Mathlib.Data.Real.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Draft/Shannon/WynerZivAchievability.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Draft/Shannon/WynerZivConverse.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Draft/Shannon/WynerZivConverseChain.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Fano/BinaryJensen.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Fano/CondEntropy.lean` (1)

- `Mathlib.Data.Fintype.Defs`

### `Common2026/Fano/Core.lean` (1)

- `Mathlib.Data.Fintype.Defs`

### `Common2026/Fano/DPI.lean` (1)

- `Mathlib.Data.Finset.Defs`

### `Common2026/Fano/Entropy.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Fano/Measure.lean` (1)

- `Lean.Parser.Command`

### `Common2026/InformationTheory/Asymptotic.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Polymatroid/Basic.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Probability/TwoSidedExtension.lean` (1)

- `Mathlib.Data.Finset.Max`

### `Common2026/Shannon/AEPRate.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/AWGN.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/AWGNAchievability.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/AWGNAchievabilityDischarge.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/AWGNConverse.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/AWGNF1Discharge.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/AWGNF2F3Discharge.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/AWGNMIBridge.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/AWGNMain.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/ArithmeticCoding.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/BackwardFiltration.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/BackwardMartingale.lean` (2)

- `Mathlib.Data.Real.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/BirkhoffErgodic.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/BlockwiseChannel.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/BrascampLieb.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/Bridge.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/BroadcastChannelAveraging.lean` (2)

- `Mathlib.Data.ENNReal.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/BroadcastChannelRandomCodebook.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/BrunnMinkowski1DSuperlevelBody.lean` (1)

- `Mathlib.Data.Set.Defs`

### `Common2026/Shannon/BrunnMinkowskiClosure.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/BrunnMinkowskiLayerCakeBody.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/BrunnMinkowskiPLBody.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/ChannelCodingAchievability.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/ChannelCodingConverse.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/ChannelCodingConverseGeneral.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/ChannelCodingConverseGeneralStrong.lean` (1)

- `Mathlib.MeasureTheory.Constructions.Polish.Basic`

### `Common2026/Shannon/ChannelCodingConverseMemorylessPure.lean` (1)

- `Mathlib.MeasureTheory.Constructions.Polish.Basic`

### `Common2026/Shannon/ChannelCodingFeedback.lean` (1)

- `Mathlib.MeasureTheory.Constructions.Polish.Basic`

### `Common2026/Shannon/ChannelCodingFeedbackComplete.lean` (1)

- `Mathlib.MeasureTheory.Constructions.Polish.Basic`

### `Common2026/Shannon/ChannelCodingShannonTheorem.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/ChannelCodingShannonTheoremGeneral.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/ChannelCodingStrongConverse.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/Chernoff.lean` (1)

- `Mathlib.Data.Fintype.Defs`

### `Common2026/Shannon/ChernoffNLetterZSum.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/CondMutualInfo.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/Converse.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/CramerLC2Discharge.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/CramerLC2DischargeExt.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/CsiszarProjection.lean` (1)

- `Mathlib.Data.Fintype.Defs`

### `Common2026/Shannon/DPI.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/DifferentialEntropy.lean` (1)

- `Mathlib.Data.Real.Basic`

### `Common2026/Shannon/EPIPlumbing.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/EPIStamDischarge.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/EPIStamInequalityBody.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/EPIStamStep12Body.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/EPIStamStep3Body.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/Entropy.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/EntropyPowerInequality.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/EntropyRate.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/FisherDeBruijnGaussianWitness.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/FisherInfo.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/FisherInfoGaussian.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/FisherInfoV2.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/FisherInfoV2DeBruijnBody.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/FisherInfoV2HeatFlowBody.lean` (1)

- `Mathlib.Data.Real.Basic`

### `Common2026/Shannon/GaussianPDFVarianceDerivBody.lean` (1)

- `Mathlib.Data.Real.Basic`

### `Common2026/Shannon/GeneralDMC.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/Han.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/HanD.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/HanDAverage.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/HanDShearer.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/HeatFlowPath.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/HoeffdingSandwich.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/HoeffdingTradeoff.lean` (2)

- `Mathlib.Data.Real.Basic`
- `Mathlib.Order.Filter.Defs`

### `Common2026/Shannon/Huffman.lean` (2)

- `Mathlib.Data.Finset.Defs`
- `Mathlib.Data.Real.Basic`

### `Common2026/Shannon/HuffmanColexDeterminism.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/HuffmanFirstStepProbe.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/HuffmanMergedAuxIdent.lean` (2)

- `Mathlib.Data.Real.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/HuffmanMergedIdentBody.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/HuffmanOptimality.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/HuffmanStrongForm.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/HuffmanSwapNormCompletion.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/HuffmanSwapNormalizationBody.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/HuffmanSwapStepChainBody.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/HuffmanT1APPrimeBody.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/HuffmanT1APPrimePartial.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/HypercubeEdgeBoundary.lean` (2)

- `Mathlib.Data.Nat.Notation`
- `Mathlib.Logic.Function.Basic`

### `Common2026/Shannon/HypercubeEdgeBoundarySharp.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/IIDProductInput.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/IIDProductInputJoint.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/LZ78ConverseAsymptotic.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/LZ78ConverseUDObject.lean` (1)

- `Mathlib.Tactic.TypeStar`

### `Common2026/Shannon/LZ78GreedyLongestPrefix.lean` (1)

- `Mathlib.Tactic.TypeStar`

### `Common2026/Shannon/LZ78GreedyParsing.lean` (1)

- `Mathlib.Data.Fintype.Defs`

### `Common2026/Shannon/LZ78GreedyParsingImpl.lean` (1)

- `Mathlib.Data.Fintype.Defs`

### `Common2026/Shannon/LZ78PhraseCountAsymptoticBody.lean` (1)

- `Mathlib.Order.Filter.Defs`

### `Common2026/Shannon/LZ78ZivCountingBody.lean` (1)

- `Mathlib.Data.Fintype.Defs`

### `Common2026/Shannon/LZ78ZivEntropyBridge.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/LZ78ZivInequality.lean` (1)

- `Mathlib.Tactic.TypeStar`

### `Common2026/Shannon/LempelZiv78.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/LoomisWhitney.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/MACCornerAchievabilityBody.lean` (1)

- `Mathlib.Tactic.TypeStar`

### `Common2026/Shannon/MACRandomCodebookAveraging.lean` (2)

- `Mathlib.Data.ENNReal.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/MACTimeSharingBody.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/MIChainRule.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/MaxEntropy.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/MaxEntropyConstrained.lean` (2)

- `Mathlib.Data.Fintype.Defs`
- `Mathlib.Data.Real.Basic`

### `Common2026/Shannon/MaxEntropyConstrainedKKT.lean` (1)

- `Mathlib.Analysis.SpecialFunctions.Log.Basic`

### `Common2026/Shannon/McMillanKraftBridge.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/MeasurePiTiltedFactorization.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/MutualInfo.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/ParallelGaussian.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/ParallelGaussianKKT.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/ParallelGaussianL_PG0Discharge.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/Pi.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/Pinsker.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/PinskerSharp.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/Polymatroid.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/RateDistortionAchievability.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/RateDistortionAchievabilityPhaseB.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/RateDistortionAchievabilityPhaseC.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/RateDistortionAchievabilityPhaseD.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/RateDistortionConverse.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/RateDistortionConverseMonotone.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/RateDistortionConvexityDischarge.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/SMBAlgoetCover.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/SMBChainRule.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/Sanov.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/SanovLDP.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/SanovLDPEquality.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/ShannonCode.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/ShannonCodeKraftReverse.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/ShannonHartley.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/ShannonMcMillanBreiman.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/SlepianWolf.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/SlepianWolfAchievability.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `Common2026/Shannon/SlepianWolfBinning.lean` (1)

- `Lean.Parser.Command`

### `Common2026/Shannon/SlepianWolfConditionalTypicalSlice.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/SlepianWolfFullRateRegion.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/StamGaussianBound.lean` (1)

- `Mathlib.Data.Real.Basic`

### `Common2026/Shannon/Stationary.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/StationaryKernel.lean` (1)

- `Mathlib.Tactic.TypeStar`

### `Common2026/Shannon/Stein.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/StrongStein.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/StrongTypicality.lean` (2)

- `Mathlib.Data.Real.Basic`
- `Mathlib.Order.Filter.Defs`

### `Common2026/Shannon/WynerZiv.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/WynerZivBinningBody.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/WynerZivConvexityBody.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `Common2026/Shannon/WynerZivDischarge.lean` (2)

- `Mathlib.Data.ENNReal.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

