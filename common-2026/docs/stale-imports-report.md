# Stale / missing imports report (linter.minImports)

> **部分結果**: `lake build` を 3220 / 3266 (98.6%) で中断した時点のログ抽出。残り 46 modules 未スキャン。`InformationTheory/Draft/Shannon/Chernoff*` 系の重い末尾領域が一部未到達。

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

### `InformationTheory/Draft/Shannon/BroadcastChannel.lean` (3)

- L1: `InformationTheory.Shannon.ChannelCoding`
- L2: `InformationTheory.Shannon.CondMutualInfo`
- L3: `InformationTheory.Shannon.MIChainRule`

### `InformationTheory/Draft/Shannon/BroadcastChannelSuperposition.lean` (2)

- L1: `InformationTheory.Draft.Shannon.BroadcastChannel`
- L2: `InformationTheory.Draft.Shannon.MACL1Discharge`

### `InformationTheory/Draft/Shannon/BroadcastChannelSuperpositionBody.lean` (2)

- L1: `InformationTheory.Draft.Shannon.BroadcastChannelSuperposition`
- L2: `InformationTheory.Draft.Shannon.MACBodyDischarge`

### `InformationTheory/Draft/Shannon/BrunnMinkowski.lean` (6)

- L1: `InformationTheory.Shannon.DifferentialEntropy`
- L2: `InformationTheory.Shannon.EntropyPowerInequality`
- L3: `Mathlib.Analysis.SpecialFunctions.Exp`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L5: `Mathlib.Probability.Independence.Basic`
- L6: `Mathlib.Algebra.Group.Pointwise.Set.Basic`

### `InformationTheory/Draft/Shannon/BrunnMinkowskiConcavity.lean` (5)

- L1: `InformationTheory.Draft.Shannon.BrunnMinkowski`
- L2: `Mathlib.Analysis.SpecialFunctions.Exp`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L4: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L5: `Mathlib.Analysis.Complex.Exponential`

### `InformationTheory/Draft/Shannon/BrunnMinkowskiFunctional.lean` (6)

- L1: `InformationTheory.Draft.Shannon.BrunnMinkowski`
- L2: `InformationTheory.Draft.Shannon.BrunnMinkowskiConcavity`
- L3: `Mathlib.Analysis.SpecialFunctions.Exp`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L6: `Mathlib.Analysis.Convex.Function`
- L7: `Mathlib.MeasureTheory.Integral.Lebesgue.Basic`

### `InformationTheory/Draft/Shannon/ChannelCodingConverseGeneralComplete.lean` (4)

- L1: `InformationTheory.Shannon.ChannelCodingConverseGeneral`
- L2: `InformationTheory.Shannon.CondMutualInfo`
- L3: `InformationTheory.Shannon.MIChainRule`
- L4: `InformationTheory.Shannon.MutualInfo`

### `InformationTheory/Draft/Shannon/ChernoffBandMassDischarge.lean` (15)

- L1: `InformationTheory.Draft.Shannon.ChernoffSanovDischarge`
- L2: `InformationTheory.Draft.Shannon.ChernoffPerTiltSanov`
- L3: `InformationTheory.Draft.Shannon.ChernoffPerTiltDischarge`
- L4: `InformationTheory.Draft.Shannon.ChernoffConverse`
- L5: `InformationTheory.Draft.Shannon.ChernoffInformation`
- L6: `InformationTheory.Shannon.Chernoff`
- L7: `InformationTheory.Shannon.CramerLC2Discharge`
- L8: `Mathlib.Probability.StrongLaw`
- L9: `Mathlib.Probability.Independence.InfinitePi`
- L10: `Mathlib.Probability.ProductMeasure`
- L11: `Mathlib.MeasureTheory.Function.ConvergenceInMeasure`
- L12: `Mathlib.MeasureTheory.Integral.Bochner.SumMeasure`
- L13: `Mathlib.Analysis.SpecialFunctions.Pow.Deriv`
- L14: `Mathlib.Analysis.Calculus.LocalExtr.Basic`
- L15: `Mathlib.Topology.Order.LocalExtr`

### `InformationTheory/Draft/Shannon/ChernoffConverse.lean` (4)

- L1: `InformationTheory.Shannon.Chernoff`
- L2: `InformationTheory.Draft.Shannon.ChernoffInformation`
- L3: `Mathlib.Topology.Order.LiminfLimsup`
- L4: `Mathlib.Order.Filter.IsBounded`

### `InformationTheory/Draft/Shannon/ChernoffInformation.lean` (4)

- L1: `InformationTheory.Shannon.Chernoff`
- L2: `InformationTheory.InformationTheory.Asymptotic`
- L3: `Mathlib.Topology.Order.LiminfLimsup`
- L4: `Mathlib.Order.Filter.IsBounded`

### `InformationTheory/Draft/Shannon/ChernoffPerTiltDischarge.lean` (11)

- L1: `InformationTheory.Draft.Shannon.ChernoffConverse`
- L2: `InformationTheory.Shannon.Chernoff`
- L3: `InformationTheory.Draft.Shannon.ChernoffInformation`
- L4: `InformationTheory.InformationTheory.Asymptotic`
- L5: `Mathlib.Topology.Order.LiminfLimsup`
- L6: `Mathlib.Order.Filter.IsBounded`
- L7: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L8: `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`
- L9: `Mathlib.MeasureTheory.Measure.Dirac`
- L10: `Mathlib.MeasureTheory.Measure.MeasureSpace`
- L11: `Mathlib.MeasureTheory.Measure.Real`

### `InformationTheory/Draft/Shannon/ChernoffPerTiltSanov.lean` (9)

- L1: `InformationTheory.Draft.Shannon.ChernoffPerTiltDischarge`
- L2: `InformationTheory.Draft.Shannon.ChernoffConverse`
- L3: `InformationTheory.Shannon.Chernoff`
- L4: `InformationTheory.Draft.Shannon.ChernoffInformation`
- L5: `InformationTheory.InformationTheory.Asymptotic`
- L6: `Mathlib.MeasureTheory.Constructions.Pi`
- L7: `Mathlib.MeasureTheory.Measure.Dirac`
- L8: `Mathlib.MeasureTheory.Measure.MeasureSpace`
- L9: `Mathlib.MeasureTheory.Measure.Real`

### `InformationTheory/Draft/Shannon/ChernoffSanovDischarge.lean` (7)

- L1: `InformationTheory.Draft.Shannon.ChernoffPerTiltSanov`
- L2: `InformationTheory.Draft.Shannon.ChernoffPerTiltDischarge`
- L3: `InformationTheory.Draft.Shannon.ChernoffConverse`
- L4: `InformationTheory.Shannon.Chernoff`
- L5: `InformationTheory.Shannon.ChernoffNLetterZSum`
- L6: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L7: `Mathlib.Analysis.SpecialFunctions.Log.Basic`

### `InformationTheory/Draft/Shannon/Cramer.lean` (9)

- L1: `Mathlib.Probability.Moments.Basic`
- L2: `Mathlib.Probability.Moments.IntegrableExpMul`
- L3: `Mathlib.Probability.Moments.MGFAnalytic`
- L4: `Mathlib.Probability.Moments.Tilted`
- L5: `Mathlib.Probability.IdentDistrib`
- L6: `Mathlib.MeasureTheory.Measure.Tilted`
- L7: `Mathlib.Analysis.SpecialFunctions.Exp`
- L8: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L9: `Mathlib.Order.LiminfLimsup`

### `InformationTheory/Draft/Shannon/CramerCLTClosure.lean` (5)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.MeasureTheory.Measure.Portmanteau`
- L3: `Mathlib.Probability.CentralLimitTheorem`
- L4: `InformationTheory.Shannon.CramerLC2DischargeExt`
- L5: `InformationTheory.Draft.Shannon.InfinitePiTiltedChangeOfMeasure`

### `InformationTheory/Draft/Shannon/CramerLC2PhaseC.lean` (8)

- L1: `InformationTheory.Draft.Shannon.Cramer`
- L2: `InformationTheory.Shannon.CramerLC2Discharge`
- L3: `InformationTheory.Shannon.CramerLC2DischargeExt`
- L4: `Mathlib.Probability.StrongLaw`
- L5: `Mathlib.Probability.Independence.InfinitePi`
- L6: `Mathlib.Probability.ProductMeasure`
- L7: `Mathlib.MeasureTheory.Function.ConvergenceInMeasure`
- L8: `Mathlib.MeasureTheory.Measure.Tilted`

### `InformationTheory/Draft/Shannon/CramerPhaseDGapWorkaround.lean` (3)

- L1: `InformationTheory.Draft.Shannon.CramerLC2PhaseC`
- L2: `InformationTheory.Draft.Shannon.ChernoffPerTiltDischarge`
- L3: `Mathlib.MeasureTheory.Constructions.Cylinders`

### `InformationTheory/Draft/Shannon/EPIConvolutionDensity.lean` (7)

- L1: `Mathlib.Probability.Density`
- L2: `Mathlib.Probability.Independence.Basic`
- L3: `Mathlib.Analysis.LConvolution`
- L4: `Mathlib.Analysis.Calculus.ParametricIntegral`
- L5: `Mathlib.Analysis.Calculus.LogDeriv`
- L6: `Mathlib.MeasureTheory.Measure.Haar.Unique`
- L7: `InformationTheory.Shannon.FisherInfoV2`

### `InformationTheory/Draft/Shannon/InfinitePiTiltedChangeOfMeasure.lean` (4)

- L1: `InformationTheory.Shannon.MeasurePiTiltedFactorization`
- L2: `InformationTheory.Shannon.CramerLC2DischargeExt`
- L3: `InformationTheory.Draft.Shannon.CramerLC2PhaseC`
- L4: `Mathlib.Probability.ProductMeasure`

### `InformationTheory/Draft/Shannon/LZ78ConverseDischarge.lean` (7)

- L1: `InformationTheory.Shannon.LempelZiv78`
- L2: `InformationTheory.Shannon.LZ78ZivInequality`
- L3: `InformationTheory.Shannon.LZ78GreedyParsing`
- L4: `InformationTheory.Shannon.ShannonMcMillanBreiman`
- L5: `InformationTheory.Shannon.SMBChainRule`
- L6: `Mathlib.Topology.Order.LiminfLimsup`
- L7: `Mathlib.Order.LiminfLimsup`

### `InformationTheory/Draft/Shannon/LZ78DistinctEncoding.lean` (11)

- L1: `InformationTheory.Shannon.LempelZiv78`
- L2: `InformationTheory.Shannon.LZ78GreedyParsing`
- L3: `InformationTheory.Shannon.LZ78GreedyParsingImpl`
- L4: `InformationTheory.Shannon.LZ78GreedyLongestPrefix`
- L5: `InformationTheory.Shannon.LZ78ZivCountingBody`
- L6: `InformationTheory.Draft.Shannon.LZ78FinalGlue`
- L7: `Mathlib.Analysis.SpecialFunctions.Log.Base`
- L8: `Mathlib.Analysis.Asymptotics.Defs`
- L9: `Mathlib.Analysis.Asymptotics.Lemmas`
- L10: `Mathlib.Analysis.Complex.ExponentialBounds`
- L11: `Mathlib.Order.Filter.IsBounded`

### `InformationTheory/Draft/Shannon/LZ78FinalGlue.lean` (9)

- L1: `InformationTheory.Shannon.LempelZiv78`
- L2: `InformationTheory.Shannon.LZ78ZivInequality`
- L3: `InformationTheory.Shannon.LZ78ConverseAsymptotic`
- L4: `InformationTheory.Draft.Shannon.LZ78ConverseDischarge`
- L5: `InformationTheory.Draft.Shannon.LZ78SMBSandwich`
- L6: `InformationTheory.Shannon.LZ78GreedyParsingImpl`
- L7: `InformationTheory.Shannon.SMBAlgoetCover`
- L8: `Mathlib.Topology.Order.LiminfLimsup`
- L9: `Mathlib.Order.LiminfLimsup`

### `InformationTheory/Draft/Shannon/LZ78SMBSandwich.lean` (8)

- L1: `InformationTheory.Shannon.LempelZiv78`
- L2: `InformationTheory.Shannon.LZ78ZivInequality`
- L3: `InformationTheory.Draft.Shannon.LZ78ConverseDischarge`
- L4: `InformationTheory.Shannon.LZ78GreedyParsing`
- L5: `InformationTheory.Shannon.ShannonMcMillanBreiman`
- L6: `InformationTheory.Shannon.SMBAlgoetCover`
- L7: `Mathlib.Topology.Order.LiminfLimsup`
- L8: `Mathlib.Order.LiminfLimsup`

### `InformationTheory/Draft/Shannon/MACCornerPoint.lean` (3)

- L1: `InformationTheory.Draft.Shannon.MultipleAccessChannel`
- L2: `Mathlib.Analysis.Convex.Combination`
- L3: `Mathlib.Analysis.Convex.Hull`

### `InformationTheory/Draft/Shannon/MACFanoConverseBody.lean` (3)

- L1: `InformationTheory.Draft.Shannon.MACL2Discharge`
- L2: `InformationTheory.Fano.Measure`
- L3: `Mathlib.Analysis.Complex.ExponentialBounds`

### `InformationTheory/Draft/Shannon/MACL1Discharge.lean` (1)

- L1: `InformationTheory.Draft.Shannon.MultipleAccessChannel`

### `InformationTheory/Draft/Shannon/MACL2Discharge.lean` (1)

- L1: `InformationTheory.Draft.Shannon.MACBodyDischarge`

### `InformationTheory/Draft/Shannon/MACPerEventAEPDecay.lean` (1)

- L1: `InformationTheory.Shannon.MACRandomCodebookAveraging`

### `InformationTheory/Draft/Shannon/MultipleAccessChannel.lean` (3)

- L1: `InformationTheory.Shannon.ChannelCoding`
- L2: `InformationTheory.Shannon.CondMutualInfo`
- L3: `InformationTheory.Shannon.MIChainRule`

### `InformationTheory/Draft/Shannon/MultivariateDiffEntropy.lean` (10)

- L1: `Mathlib.MeasureTheory.Measure.Prod`
- L2: `Mathlib.MeasureTheory.Measure.WithDensity`
- L3: `Mathlib.MeasureTheory.Integral.Prod`
- L4: `Mathlib.MeasureTheory.Constructions.Pi`
- L5: `Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym`
- L6: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L7: `Mathlib.InformationTheory.KullbackLeibler.Basic`
- L8: `InformationTheory.Shannon.DifferentialEntropy`
- L9: `InformationTheory.Shannon.MutualInfo`
- L10: `InformationTheory.Shannon.MIChainRule`

### `InformationTheory/Draft/Shannon/RateDistortionAchievabilityPhaseE.lean` (1)

- L1: `InformationTheory.Shannon.RateDistortionAchievabilityPhaseD`

### `InformationTheory/Draft/Shannon/RateDistortionConverseNLetter.lean` (3)

- L1: `InformationTheory.Shannon.RateDistortionConverseMonotone`
- L2: `InformationTheory.Shannon.RateDistortionAchievability`
- L3: `InformationTheory.Shannon.RateDistortionConvexityDischarge`

### `InformationTheory/Draft/Shannon/RateDistortionConvexity.lean` (1)

- L1: `InformationTheory.Shannon.RateDistortionConverseMonotone`

### `InformationTheory/Draft/Shannon/RelayCutset.lean` (3)

- L1: `InformationTheory.Shannon.ChannelCoding`
- L2: `InformationTheory.Shannon.CondMutualInfo`
- L3: `InformationTheory.Shannon.MIChainRule`

### `InformationTheory/Draft/Shannon/RelayInnerBound.lean` (1)

- L1: `InformationTheory.Draft.Shannon.RelayCutset`

### `InformationTheory/Draft/Shannon/WynerZivAchievability.lean` (1)

- L1: `InformationTheory.Shannon.WynerZiv`

### `InformationTheory/Draft/Shannon/WynerZivConverse.lean` (1)

- L1: `InformationTheory.Shannon.WynerZiv`

### `InformationTheory/Draft/Shannon/WynerZivConverseChain.lean` (3)

- L1: `InformationTheory.Shannon.WynerZiv`
- L2: `InformationTheory.Draft.Shannon.WynerZivConverse`
- L3: `InformationTheory.Draft.Shannon.RateDistortionConverseNLetter`

### `InformationTheory/Fano.lean` (1)

- L2: `Mathlib.Data.Fintype.BigOperators`

### `InformationTheory/Fano/BinaryJensen.lean` (3)

- L1: `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`
- L2: `Mathlib.Analysis.Convex.Jensen`
- L3: `Mathlib.Data.Fintype.BigOperators`

### `InformationTheory/Fano/CondEntropy.lean` (2)

- L1: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L2: `Mathlib.Data.Fintype.BigOperators`

### `InformationTheory/Fano/Core.lean` (5)

- L1: `InformationTheory.Fano`
- L2: `InformationTheory.Fano.Entropy`
- L3: `InformationTheory.Fano.BinaryJensen`
- L4: `InformationTheory.Fano.CondEntropy`
- L5: `Mathlib.Algebra.BigOperators.Field`

### `InformationTheory/Fano/DPI.lean` (7)

- L1: `InformationTheory.Fano`
- L2: `InformationTheory.Fano.BinaryJensen`
- L3: `InformationTheory.Fano.Core`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L5: `Mathlib.Analysis.Convex.Jensen`
- L6: `Mathlib.Algebra.BigOperators.Field`
- L7: `Mathlib.Tactic.Linarith`

### `InformationTheory/Fano/Entropy.lean` (3)

- L1: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L2: `Mathlib.Analysis.Convex.Jensen`
- L3: `Mathlib.Data.Fintype.BigOperators`

### `InformationTheory/Fano/Measure.lean` (9)

- L1: `InformationTheory.Fano.Core`
- L2: `Mathlib.Probability.Kernel.CondDistrib`
- L3: `Mathlib.Probability.Kernel.Composition.MeasureCompProd`
- L4: `Mathlib.Probability.ProbabilityMassFunction.Basic`
- L5: `Mathlib.Probability.ProbabilityMassFunction.Constructions`
- L6: `Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic`
- L7: `Mathlib.Analysis.Convex.Integral`
- L8: `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`
- L9: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`

### `InformationTheory/InformationTheory/Asymptotic.lean` (6)

- L1: `Mathlib.Analysis.Asymptotics.Defs`
- L2: `Mathlib.Analysis.Asymptotics.Lemmas`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L4: `Mathlib.Analysis.SpecialFunctions.Exp`
- L5: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L6: `Mathlib.Topology.MetricSpace.Pseudo.Defs`

### `InformationTheory/Polymatroid/Basic.lean` (4)

- L1: `Mathlib.Data.Finset.Empty`
- L2: `Mathlib.Data.Finset.Lattice.Basic`
- L3: `Mathlib.Order.Monotone.Basic`
- L4: `Mathlib.Data.Real.Basic`

### `InformationTheory/Probability/TwoSidedExtension.lean` (15)

- L1: `InformationTheory.Shannon.Stationary`
- L2: `InformationTheory.Shannon.EntropyRate`
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

### `InformationTheory/Shannon/AEP.lean` (11)

- L2: `InformationTheory.Shannon.Han`
- L3: `InformationTheory.Shannon.Pi`
- L4: `InformationTheory.Shannon.DPI`
- L5: `InformationTheory.Shannon.SlepianWolf`
- L6: `InformationTheory.Fano.Measure`
- L8: `Mathlib.Probability.IdentDistrib`
- L9: `Mathlib.Probability.Independence.Basic`
- L10: `Mathlib.MeasureTheory.Function.ConvergenceInMeasure`
- L11: `Mathlib.MeasureTheory.Constructions.BorelSpace.Order`
- L12: `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`
- L13: `Mathlib.Analysis.SpecificLimits.Basic`

### `InformationTheory/Shannon/AEPRate.lean` (3)

- L1: `InformationTheory.Shannon.AEP`
- L2: `InformationTheory.Shannon.ChannelCoding`
- L3: `Mathlib.Probability.Moments.Variance`

### `InformationTheory/Shannon/AWGN.lean` (5)

- L1: `InformationTheory.Shannon.ChannelCoding`
- L2: `InformationTheory.Shannon.DifferentialEntropy`
- L3: `Mathlib.Probability.Distributions.Gaussian.Real`
- L4: `Mathlib.Probability.Distributions.Gaussian.Basic`
- L5: `Mathlib.MeasureTheory.Measure.GiryMonad`

### `InformationTheory/Shannon/AWGNAchievability.lean` (1)

- L1: `InformationTheory.Shannon.AWGN`

### `InformationTheory/Shannon/AWGNAchievabilityDischarge.lean` (8)

- L1: `InformationTheory.Shannon.AWGN`
- L2: `InformationTheory.Shannon.AWGNAchievability`
- L3: `InformationTheory.Shannon.AWGNMain`
- L4: `InformationTheory.Shannon.AWGNF1Discharge`
- L5: `InformationTheory.Shannon.DifferentialEntropy`
- L6: `Mathlib.Probability.Distributions.Gaussian.Real`
- L7: `Mathlib.Probability.Independence.Basic`
- L8: `Mathlib.MeasureTheory.Constructions.Pi`

### `InformationTheory/Shannon/AWGNConverse.lean` (1)

- L1: `InformationTheory.Shannon.AWGN`

### `InformationTheory/Shannon/AWGNF1Discharge.lean` (1)

- L1: `InformationTheory.Shannon.AWGNMain`

### `InformationTheory/Shannon/AWGNF2F3Discharge.lean` (1)

- L1: `InformationTheory.Shannon.AWGNF1Discharge`

### `InformationTheory/Shannon/AWGNMIBridge.lean` (1)

- L1: `InformationTheory.Shannon.AWGNF1Discharge`

### `InformationTheory/Shannon/AWGNMain.lean` (3)

- L1: `InformationTheory.Shannon.AWGN`
- L2: `InformationTheory.Shannon.AWGNAchievability`
- L3: `InformationTheory.Shannon.AWGNConverse`

### `InformationTheory/Shannon/ArithmeticCoding.lean` (4)

- L1: `InformationTheory.Shannon.ShannonCode`
- L2: `InformationTheory.Shannon.ShannonCodeKraftReverse`
- L3: `Mathlib.MeasureTheory.Measure.ProbabilityMeasure`
- L4: `Mathlib.Logic.Equiv.Defs`

### `InformationTheory/Shannon/BackwardFiltration.lean` (3)

- L1: `Mathlib.Probability.Process.Filtration`
- L2: `Mathlib.MeasureTheory.MeasurableSpace.Basic`
- L3: `Mathlib.Dynamics.Ergodic.MeasurePreserving`

### `InformationTheory/Shannon/BackwardMartingale.lean` (5)

- L1: `InformationTheory.Shannon.BackwardFiltration`
- L2: `Mathlib.Probability.Martingale.Basic`
- L3: `Mathlib.Probability.Martingale.Convergence`
- L4: `Mathlib.Probability.Martingale.Upcrossing`
- L5: `Mathlib.MeasureTheory.Function.ConditionalExpectation.Real`

### `InformationTheory/Shannon/BirkhoffErgodic.lean` (8)

- L1: `Mathlib.Dynamics.Ergodic.Ergodic`
- L2: `Mathlib.Dynamics.Ergodic.Function`
- L3: `Mathlib.Dynamics.Ergodic.MeasurePreserving`
- L4: `Mathlib.MeasureTheory.Integral.Bochner.Basic`
- L5: `Mathlib.MeasureTheory.Integral.Bochner.Set`
- L6: `Mathlib.MeasureTheory.Integral.DominatedConvergence`
- L7: `Mathlib.MeasureTheory.Measure.Typeclasses.Probability`
- L8: `Mathlib.Topology.Algebra.Order.LiminfLimsup`

### `InformationTheory/Shannon/BlockwiseChannel.lean` (8)

- L1: `InformationTheory.Shannon.ChannelCoding`
- L2: `InformationTheory.Shannon.ChannelCodingShannonTheorem`
- L3: `InformationTheory.Shannon.MIChainRule`
- L4: `InformationTheory.Shannon.CondEntropyMemoryless`
- L5: `Mathlib.Analysis.Subadditive`
- L6: `Mathlib.MeasureTheory.Constructions.Pi`
- L7: `Mathlib.MeasureTheory.MeasurableSpace.Pi`
- L8: `Mathlib.MeasureTheory.Integral.Lebesgue.Countable`

### `InformationTheory/Shannon/BrascampLieb.lean` (1)

- L1: `InformationTheory.Shannon.LoomisWhitney`

### `InformationTheory/Shannon/Bridge.lean` (9)

- L1: `InformationTheory.Shannon.MutualInfo`
- L2: `InformationTheory.Fano.Measure`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L4: `Mathlib.MeasureTheory.Function.SpecialFunctions.Basic`
- L5: `Mathlib.MeasureTheory.Integral.Bochner.SumMeasure`
- L6: `Mathlib.MeasureTheory.Integral.Lebesgue.Countable`
- L7: `Mathlib.MeasureTheory.Measure.Prod`
- L8: `Mathlib.Probability.Kernel.Composition.RadonNikodym`
- L9: `Mathlib.Probability.Kernel.RadonNikodym`

### `InformationTheory/Shannon/BroadcastChannelAveraging.lean` (1)

- L1: `InformationTheory.Shannon.BroadcastChannelRandomCodebook`

### `InformationTheory/Shannon/BroadcastChannelRandomCodebook.lean` (1)

- L1: `InformationTheory.Draft.Shannon.BroadcastChannelSuperpositionBody`

### `InformationTheory/Shannon/BrunnMinkowski1DSuperlevelBody.lean` (7)

- L1: `InformationTheory.Shannon.BrunnMinkowskiPLBody`
- L2: `Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar`
- L3: `Mathlib.MeasureTheory.Measure.NullMeasurable`
- L4: `Mathlib.Algebra.Group.Pointwise.Set.Basic`
- L5: `Mathlib.MeasureTheory.Group.Measure`
- L6: `Mathlib.MeasureTheory.Group.Arithmetic`
- L7: `Mathlib.Topology.Order.Compact`

### `InformationTheory/Shannon/BrunnMinkowskiClosure.lean` (12)

- L1: `InformationTheory.Shannon.BrunnMinkowskiLayerCakeBody`
- L2: `InformationTheory.Shannon.BrunnMinkowskiPLBody`
- L3: `InformationTheory.Shannon.BrunnMinkowski1DSuperlevelBody`
- L4: `InformationTheory.Draft.Shannon.BrunnMinkowskiConcavity`
- L5: `InformationTheory.Draft.Shannon.MultivariateDiffEntropy`
- L6: `Mathlib.MeasureTheory.Constructions.Pi`
- L7: `Mathlib.MeasureTheory.Integral.Prod`
- L8: `Mathlib.MeasureTheory.Integral.Pi`
- L9: `Mathlib.MeasureTheory.Integral.IntegrableOn`
- L10: `Mathlib.MeasureTheory.Measure.Prod`
- L11: `Mathlib.Topology.Algebra.Monoid`
- L12: `Mathlib.Topology.Algebra.ConstMulAction`

### `InformationTheory/Shannon/BrunnMinkowskiLayerCakeBody.lean` (5)

- L1: `InformationTheory.Shannon.BrunnMinkowskiPLBody`
- L2: `InformationTheory.Shannon.BrunnMinkowski1DSuperlevelBody`
- L3: `Mathlib.MeasureTheory.Integral.Layercake`
- L4: `Mathlib.MeasureTheory.Integral.Bochner.Set`
- L5: `Mathlib.MeasureTheory.Measure.Real`

### `InformationTheory/Shannon/BrunnMinkowskiPLBody.lean` (4)

- L1: `InformationTheory.Draft.Shannon.BrunnMinkowski`
- L2: `InformationTheory.Draft.Shannon.BrunnMinkowskiFunctional`
- L3: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L4: `Mathlib.Analysis.MeanInequalities`

### `InformationTheory/Shannon/ChannelCoding.lean` (4)

- L1: `InformationTheory.Shannon.MutualInfo`
- L2: `InformationTheory.Shannon.MIChainRule`
- L3: `InformationTheory.Shannon.AEP`
- L4: `Mathlib.Probability.Kernel.Basic`

### `InformationTheory/Shannon/ChannelCodingAchievability.lean` (5)

- L1: `InformationTheory.Shannon.ChannelCoding`
- L2: `InformationTheory.Shannon.IIDProductInput`
- L3: `InformationTheory.Shannon.AEPRate`
- L4: `Mathlib.Probability.ProductMeasure`
- L5: `Mathlib.Probability.Independence.InfinitePi`

### `InformationTheory/Shannon/ChannelCodingConverse.lean` (2)

- L1: `InformationTheory.Shannon.Converse`
- L2: `InformationTheory.Shannon.MIChainRule`

### `InformationTheory/Shannon/ChannelCodingConverseGeneral.lean` (2)

- L1: `InformationTheory.Shannon.Converse`
- L2: `InformationTheory.Shannon.MIChainRule`

### `InformationTheory/Shannon/ChannelCodingConverseGeneralStrong.lean` (3)

- L1: `InformationTheory.Draft.Shannon.ChannelCodingConverseGeneralComplete`
- L2: `InformationTheory.Shannon.CondEntropyMemoryless`
- L3: `Mathlib.MeasureTheory.MeasurableSpace.Embedding`

### `InformationTheory/Shannon/ChannelCodingConverseMemorylessPure.lean` (1)

- L1: `InformationTheory.Shannon.ChannelCodingConverseGeneralStrong`

### `InformationTheory/Shannon/ChannelCodingFeedback.lean` (5)

- L1: `InformationTheory.Shannon.ChannelCoding`
- L2: `InformationTheory.Shannon.ChannelCodingConverse`
- L3: `InformationTheory.Shannon.Converse`
- L4: `InformationTheory.Shannon.MIChainRule`
- L5: `InformationTheory.Shannon.CondMutualInfo`

### `InformationTheory/Shannon/ChannelCodingFeedbackComplete.lean` (4)

- L1: `InformationTheory.Shannon.ChannelCodingFeedback`
- L2: `InformationTheory.Shannon.CondMutualInfo`
- L3: `InformationTheory.Shannon.MIChainRule`
- L4: `InformationTheory.Shannon.MutualInfo`

### `InformationTheory/Shannon/ChannelCodingShannonTheorem.lean` (7)

- L1: `InformationTheory.Shannon.ChannelCoding`
- L2: `InformationTheory.Shannon.ChannelCodingAchievability`
- L3: `InformationTheory.Shannon.MaxEntropy`
- L4: `Mathlib.Analysis.Convex.StdSimplex`
- L5: `Mathlib.Topology.Order.Compact`
- L6: `Mathlib.Order.ConditionallyCompleteLattice.Basic`
- L7: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`

### `InformationTheory/Shannon/ChannelCodingShannonTheoremFull.lean` (3)

- L1: `InformationTheory.Shannon.ChannelCodingShannonTheorem`
- L2: `InformationTheory.Shannon.ChannelCodingShannonTheoremGeneral`
- L3: `InformationTheory.Shannon.AEPRate`

### `InformationTheory/Shannon/ChannelCodingShannonTheoremGeneral.lean` (4)

- L1: `InformationTheory.Shannon.ChannelCoding`
- L2: `InformationTheory.Shannon.ChannelCodingShannonTheorem`
- L3: `Mathlib.Analysis.Convex.StdSimplex`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`

### `InformationTheory/Shannon/ChannelCodingStrongConverse.lean` (3)

- L1: `InformationTheory.Shannon.ChannelCoding`
- L2: `InformationTheory.Shannon.StrongStein`
- L3: `Mathlib.MeasureTheory.Constructions.Pi`

### `InformationTheory/Shannon/Chernoff.lean` (6)

- L1: `InformationTheory.Shannon.CsiszarProjection`
- L2: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L3: `Mathlib.Analysis.SpecialFunctions.Pow.Continuity`
- L4: `Mathlib.Topology.Order.Compact`
- L5: `Mathlib.Analysis.MeanInequalities`
- L6: `Mathlib.Data.Real.ConjExponents`

### `InformationTheory/Shannon/ChernoffNLetterZSum.lean` (3)

- L1: `InformationTheory.Shannon.Chernoff`
- L2: `Mathlib.Algebra.BigOperators.Ring.Finset`
- L3: `Mathlib.Data.Fintype.Pi`

### `InformationTheory/Shannon/CondMutualInfo.lean` (8)

- L1: `Mathlib.InformationTheory.KullbackLeibler.Basic`
- L2: `Mathlib.InformationTheory.KullbackLeibler.ChainRule`
- L3: `Mathlib.Probability.Kernel.CondDistrib`
- L4: `Mathlib.Probability.Kernel.Composition.MeasureCompProd`
- L5: `Mathlib.Probability.Kernel.Composition.CompProd`
- L6: `Mathlib.Probability.Kernel.Composition.MapComap`
- L7: `InformationTheory.Shannon.MutualInfo`
- L8: `InformationTheory.Shannon.DPI`

### `InformationTheory/Shannon/Converse.lean` (8)

- L1: `InformationTheory.Shannon.MutualInfo`
- L2: `InformationTheory.Shannon.DPI`
- L3: `InformationTheory.Shannon.Bridge`
- L4: `InformationTheory.Shannon.CondMutualInfo`
- L5: `InformationTheory.Fano.Measure`
- L6: `Mathlib.MeasureTheory.Measure.Count`
- L7: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L8: `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`

### `InformationTheory/Shannon/CramerLC2Discharge.lean` (5)

- L1: `InformationTheory.Draft.Shannon.Cramer`
- L2: `Mathlib.Probability.StrongLaw`
- L3: `Mathlib.Probability.Independence.InfinitePi`
- L4: `Mathlib.Probability.ProductMeasure`
- L5: `Mathlib.MeasureTheory.Function.ConvergenceInMeasure`

### `InformationTheory/Shannon/CramerLC2DischargeExt.lean` (5)

- L1: `InformationTheory.Shannon.CramerLC2Discharge`
- L2: `Mathlib.Probability.StrongLaw`
- L3: `Mathlib.Probability.Independence.InfinitePi`
- L4: `Mathlib.Probability.ProductMeasure`
- L5: `Mathlib.MeasureTheory.Function.ConvergenceInMeasure`

### `InformationTheory/Shannon/CsiszarProjection.lean` (5)

- L1: `Mathlib.InformationTheory.KullbackLeibler.KLFun`
- L2: `Mathlib.Analysis.Convex.StdSimplex`
- L3: `Mathlib.Analysis.Calculus.MeanValue`
- L4: `Mathlib.Analysis.Calculus.Deriv.Slope`
- L5: `Mathlib.Topology.Order.Compact`

### `InformationTheory/Shannon/DPI.lean` (11)

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
- L11: `InformationTheory.Shannon.MutualInfo`

### `InformationTheory/Shannon/DifferentialEntropy.lean` (4)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.InformationTheory.KullbackLeibler.Basic`
- L3: `Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`

### `InformationTheory/Shannon/EPIL3Integration.lean` (16)

- L1: `InformationTheory.Shannon.EntropyPowerInequality`
- L2: `InformationTheory.Shannon.EPIPlumbing`
- L4: `InformationTheory.Shannon.FisherInfoV2DeBruijn`
- L5: `InformationTheory.Shannon.FisherInfoV2`
- L6: `InformationTheory.Shannon.FisherInfoGaussian`
- L7: `InformationTheory.Shannon.DifferentialEntropy`
- L8: `InformationTheory.Shannon.HeatFlowPath`
- L9: `Mathlib.Analysis.SpecialFunctions.Exp`
- L10: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L11: `Mathlib.Probability.Distributions.Gaussian.Real`
- L12: `Mathlib.Probability.Independence.Basic`
- L13: `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`
- L14: `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`
- L15: `Mathlib.MeasureTheory.Integral.Bochner.Set`
- L16: `Mathlib.Topology.Instances.EReal.Lemmas`
- L17: `Mathlib.Order.Filter.AtTopBot.Group`

### `InformationTheory/Shannon/EPIPlumbing.lean` (4)

- L1: `InformationTheory.Shannon.EntropyPowerInequality`
- L2: `InformationTheory.Shannon.DifferentialEntropy`
- L3: `Mathlib.Analysis.SpecialFunctions.Exp`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.Basic`

### `InformationTheory/Shannon/EPIStamDischarge.lean` (11)

- L1: `InformationTheory.Shannon.EntropyPowerInequality`
- L2: `InformationTheory.Shannon.EPIPlumbing`
- L3: `InformationTheory.Shannon.FisherInfoV2`
- L4: `InformationTheory.Shannon.FisherInfoV2DeBruijn`
- L5: `InformationTheory.Shannon.FisherInfoGaussian`
- L6: `InformationTheory.Shannon.DifferentialEntropy`
- L7: `Mathlib.Analysis.SpecialFunctions.Exp`
- L8: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L9: `Mathlib.Probability.Distributions.Gaussian.Real`
- L10: `Mathlib.Probability.Independence.Basic`
- L11: `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`

### `InformationTheory/Shannon/EPIStamInequalityBody.lean` (13)

- L1: `InformationTheory.Shannon.EntropyPowerInequality`
- L2: `InformationTheory.Shannon.EPIPlumbing`
- L3: `InformationTheory.Shannon.EPIStamDischarge`
- L4: `InformationTheory.Shannon.EPIL3Integration`
- L5: `InformationTheory.Shannon.FisherInfoV2`
- L6: `InformationTheory.Shannon.FisherInfoV2DeBruijn`
- L7: `InformationTheory.Shannon.FisherInfoGaussian`
- L8: `InformationTheory.Shannon.DifferentialEntropy`
- L9: `Mathlib.Analysis.SpecialFunctions.Exp`
- L10: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L11: `Mathlib.Probability.Distributions.Gaussian.Real`
- L12: `Mathlib.Probability.Independence.Basic`
- L13: `Mathlib.Analysis.InnerProductSpace.Basic`

### `InformationTheory/Shannon/EPIStamStep12Body.lean` (7)

- L1: `InformationTheory.Shannon.EPIStamInequalityBody`
- L2: `InformationTheory.Shannon.EPIStamDischarge`
- L3: `InformationTheory.Shannon.FisherInfoV2`
- L4: `InformationTheory.Shannon.FisherInfoV2DeBruijn`
- L5: `Mathlib.Tactic.Positivity`
- L6: `Mathlib.Tactic.Linarith`
- L7: `Mathlib.Tactic.Ring`

### `InformationTheory/Shannon/EPIStamStep3Body.lean` (11)

- L1: `InformationTheory.Shannon.EntropyPowerInequality`
- L2: `InformationTheory.Shannon.EPIPlumbing`
- L3: `InformationTheory.Shannon.EPIStamDischarge`
- L4: `InformationTheory.Shannon.EPIStamInequalityBody`
- L5: `InformationTheory.Shannon.FisherInfoV2`
- L6: `InformationTheory.Shannon.FisherInfoV2DeBruijn`
- L7: `InformationTheory.Shannon.FisherInfoGaussian`
- L8: `Mathlib.Analysis.SpecialFunctions.Exp`
- L9: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L10: `Mathlib.Probability.Distributions.Gaussian.Real`
- L11: `Mathlib.Probability.Independence.Basic`

### `InformationTheory/Shannon/EPIStamToBridge.lean` (12)

- L1: `InformationTheory.Shannon.EntropyPowerInequality`
- L2: `InformationTheory.Shannon.EPIStamDischarge`
- L3: `InformationTheory.Shannon.EPIL3Integration`
- L4: `InformationTheory.Shannon.EPIPlumbing`
- L5: `InformationTheory.Shannon.DifferentialEntropy`
- L6: `InformationTheory.Shannon.HeatFlowPath`
- L7: `Mathlib.Analysis.SpecialFunctions.Exp`
- L8: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L9: `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`
- L11: `Mathlib.Probability.Independence.Basic`
- L12: `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`
- L13: `Mathlib.Order.Monotone.Basic`

### `InformationTheory/Shannon/Entropy.lean` (2)

- L1: `InformationTheory.Shannon.Bridge`
- L2: `InformationTheory.Shannon.CondMutualInfo`

### `InformationTheory/Shannon/EntropyPowerInequality.lean` (7)

- L1: `InformationTheory.Shannon.DifferentialEntropy`
- L2: `InformationTheory.Shannon.FisherInfo`
- L3: `InformationTheory.Shannon.FisherInfoV2`
- L4: `Mathlib.Analysis.SpecialFunctions.Exp`
- L5: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L6: `Mathlib.Probability.Distributions.Gaussian.Real`
- L7: `Mathlib.Probability.Independence.Basic`

### `InformationTheory/Shannon/EntropyRate.lean` (7)

- L1: `InformationTheory.Shannon.Stationary`
- L2: `InformationTheory.Shannon.Bridge`
- L3: `InformationTheory.Shannon.CondMutualInfo`
- L4: `InformationTheory.Shannon.Pi`
- L5: `Mathlib.Analysis.Asymptotics.SpecificAsymptotics`
- L6: `Mathlib.Topology.Order.MonotoneConvergence`
- L7: `Mathlib.Order.Filter.AtTopBot.CompleteLattice`

### `InformationTheory/Shannon/FisherDeBruijnGaussianWitness.lean` (5)

- L1: `InformationTheory.Shannon.FisherInfoV2`
- L2: `InformationTheory.Shannon.FisherInfoV2DeBruijn`
- L3: `InformationTheory.Shannon.FisherInfoV2DeBruijnBody`
- L4: `InformationTheory.Shannon.FisherInfoV2HeatFlowBody`
- L5: `InformationTheory.Shannon.GaussianPDFVarianceDerivBody`

### `InformationTheory/Shannon/FisherInfo.lean` (7)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.Probability.Density`
- L3: `Mathlib.Analysis.Calculus.LogDeriv`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.Deriv`
- L5: `Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue`
- L6: `Mathlib.MeasureTheory.Measure.Dirac`
- L7: `InformationTheory.Shannon.DifferentialEntropy`

### `InformationTheory/Shannon/FisherInfoGaussian.lean` (7)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.Probability.Density`
- L3: `Mathlib.Probability.Independence.Basic`
- L4: `Mathlib.Analysis.Calculus.LogDeriv`
- L5: `Mathlib.Analysis.SpecialFunctions.Log.Deriv`
- L6: `InformationTheory.Shannon.FisherInfo`
- L7: `InformationTheory.Shannon.DifferentialEntropy`

### `InformationTheory/Shannon/FisherInfoV2.lean` (11)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.Probability.Density`
- L3: `Mathlib.Probability.Moments.Variance`
- L4: `Mathlib.Analysis.Calculus.LogDeriv`
- L5: `Mathlib.Analysis.SpecialFunctions.Log.Deriv`
- L6: `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`
- L7: `Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue`
- L8: `Mathlib.MeasureTheory.Measure.Dirac`
- L9: `InformationTheory.Shannon.FisherInfo`
- L10: `InformationTheory.Shannon.FisherInfoGaussian`
- L11: `InformationTheory.Shannon.DifferentialEntropy`

### `InformationTheory/Shannon/FisherInfoV2DeBruijn.lean` (11)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.Probability.Density`
- L3: `Mathlib.Probability.Independence.Basic`
- L4: `Mathlib.Analysis.Calculus.LogDeriv`
- L5: `Mathlib.Analysis.SpecialFunctions.Log.Deriv`
- L6: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L7: `Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue`
- L8: `InformationTheory.Shannon.FisherInfo`
- L9: `InformationTheory.Shannon.FisherInfoGaussian`
- L11: `InformationTheory.Shannon.DifferentialEntropy`
- L12: `InformationTheory.Shannon.EntropyPowerInequality`

### `InformationTheory/Shannon/FisherInfoV2DeBruijnBody.lean` (11)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.Deriv`
- L4: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L5: `Mathlib.Analysis.Calculus.Deriv.Add`
- L6: `Mathlib.Analysis.Calculus.Deriv.Mul`
- L7: `Mathlib.Analysis.Calculus.Deriv.Comp`
- L8: `Mathlib.Analysis.Calculus.LogDeriv`
- L9: `InformationTheory.Shannon.FisherInfoV2`
- L10: `InformationTheory.Shannon.FisherInfoV2DeBruijn`
- L11: `InformationTheory.Shannon.DifferentialEntropy`

### `InformationTheory/Shannon/FisherInfoV2HeatFlowBody.lean` (13)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.Deriv`
- L4: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L5: `Mathlib.Analysis.Calculus.Deriv.Add`
- L6: `Mathlib.Analysis.Calculus.Deriv.Mul`
- L7: `Mathlib.Analysis.Calculus.Deriv.Comp`
- L8: `Mathlib.Analysis.Calculus.LogDeriv`
- L9: `InformationTheory.Shannon.FisherInfoV2`
- L10: `InformationTheory.Shannon.FisherInfoV2DeBruijn`
- L11: `InformationTheory.Shannon.FisherInfoV2DeBruijnBody`
- L12: `InformationTheory.Shannon.FisherInfoGaussian`
- L13: `InformationTheory.Shannon.DifferentialEntropy`

### `InformationTheory/Shannon/GaussianPDFVarianceDerivBody.lean` (10)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.Analysis.SpecialFunctions.Sqrt`
- L3: `Mathlib.Analysis.SpecialFunctions.ExpDeriv`
- L4: `Mathlib.Analysis.Calculus.Deriv.Inv`
- L5: `Mathlib.Analysis.Calculus.Deriv.Mul`
- L6: `Mathlib.Analysis.Calculus.Deriv.Add`
- L7: `Mathlib.Analysis.Calculus.Deriv.Comp`
- L8: `InformationTheory.Shannon.FisherInfoGaussian`
- L9: `InformationTheory.Shannon.FisherInfoV2DeBruijnBody`
- L10: `InformationTheory.Shannon.FisherInfoV2HeatFlowBody`

### `InformationTheory/Shannon/GeneralDMC.lean` (2)

- L1: `InformationTheory.Shannon.BlockwiseChannel`
- L2: `Mathlib.Analysis.Subadditive`

### `InformationTheory/Shannon/Han.lean` (2)

- L1: `InformationTheory.Shannon.Entropy`
- L2: `InformationTheory.Shannon.Pi`

### `InformationTheory/Shannon/HanD.lean` (1)

- L1: `InformationTheory.Shannon.Han`

### `InformationTheory/Shannon/HanDAverage.lean` (1)

- L1: `InformationTheory.Shannon.HanD`

### `InformationTheory/Shannon/HanDShearer.lean` (1)

- L1: `InformationTheory.Shannon.HanD`

### `InformationTheory/Shannon/HeatFlowPath.lean` (7)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.Probability.Independence.Basic`
- L3: `Mathlib.MeasureTheory.MeasurableSpace.Basic`
- L4: `Mathlib.MeasureTheory.Group.Convolution`
- L5: `Mathlib.Analysis.SpecialFunctions.Sqrt`
- L6: `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`
- L7: `InformationTheory.Shannon.FisherInfoV2DeBruijn`

### `InformationTheory/Shannon/HoeffdingSandwich.lean` (4)

- L1: `InformationTheory.Shannon.HoeffdingTradeoff`
- L2: `InformationTheory.Shannon.Chernoff`
- L3: `Mathlib.Topology.Order.LiminfLimsup`
- L4: `Mathlib.Order.Filter.IsBounded`

### `InformationTheory/Shannon/HoeffdingTradeoff.lean` (9)

- L1: `InformationTheory.Shannon.Chernoff`
- L2: `InformationTheory.Shannon.CsiszarProjection`
- L3: `InformationTheory.Shannon.KLDivContinuous`
- L4: `InformationTheory.Shannon.SanovLDPEquality`
- L5: `InformationTheory.InformationTheory.Asymptotic`
- L6: `Mathlib.Probability.ProbabilityMassFunction.Basic`
- L7: `Mathlib.Probability.ProbabilityMassFunction.Constructions`
- L8: `Mathlib.Topology.Order.Compact`
- L9: `Mathlib.Topology.Order.LiminfLimsup`

### `InformationTheory/Shannon/Huffman.lean` (11)

- L1: `Mathlib.Analysis.SpecialFunctions.Log.Base`
- L2: `Mathlib.MeasureTheory.Measure.Real`
- L3: `Mathlib.Data.Multiset.Basic`
- L4: `Mathlib.Data.Multiset.Sort`
- L5: `Mathlib.Data.Finset.Max`
- L6: `Mathlib.Data.Finset.Image`
- L7: `Mathlib.Combinatorics.Colex`
- L9: `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- L10: `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- L11: `InformationTheory.Shannon.ShannonCode`
- L12: `InformationTheory.Shannon.ShannonCodeKraftReverse`

### `InformationTheory/Shannon/HuffmanColexDeterminism.lean` (1)

- L1: `InformationTheory.Shannon.HuffmanMergedAuxIdent`

### `InformationTheory/Shannon/HuffmanFirstStepProbe.lean` (1)

- L1: `InformationTheory.Shannon.HuffmanColexDeterminism`

### `InformationTheory/Shannon/HuffmanMergedAuxIdent.lean` (4)

- L1: `Mathlib.Logic.Equiv.Basic`
- L2: `Mathlib.Data.Multiset.MapFold`
- L3: `Mathlib.Tactic.Linarith`
- L4: `InformationTheory.Shannon.HuffmanMergedIdentBody`

### `InformationTheory/Shannon/HuffmanMergedIdentBody.lean` (2)

- L1: `Mathlib.Logic.Equiv.Basic`
- L2: `InformationTheory.Shannon.HuffmanOptimality`

### `InformationTheory/Shannon/HuffmanOptimality.lean` (8)

- L1: `Mathlib.Logic.Equiv.Basic`
- L2: `Mathlib.Logic.Function.Basic`
- L3: `Mathlib.Data.Finset.Max`
- L4: `Mathlib.Data.Finset.Image`
- L5: `Mathlib.Data.Fintype.EquivFin`
- L6: `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- L7: `Mathlib.MeasureTheory.Measure.Real`
- L8: `InformationTheory.Shannon.Huffman`

### `InformationTheory/Shannon/HuffmanStrongForm.lean` (3)

- L1: `InformationTheory.Shannon.HuffmanOptimality`
- L2: `InformationTheory.Shannon.HuffmanSwapNormCompletion`
- L3: `InformationTheory.Shannon.HuffmanMergedIdentBody`

### `InformationTheory/Shannon/HuffmanSwapNormCompletion.lean` (10)

- L1: `Mathlib.Data.Real.Basic`
- L2: `Mathlib.Data.Finset.Max`
- L3: `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- L4: `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise`
- L5: `Mathlib.Algebra.BigOperators.Field`
- L6: `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- L7: `Mathlib.Tactic.Positivity`
- L8: `Mathlib.Tactic.Ring`
- L9: `Mathlib.Tactic.Linarith`
- L10: `InformationTheory.Shannon.HuffmanSwapNormProof`

### `InformationTheory/Shannon/HuffmanSwapNormProof.lean` (10)

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

### `InformationTheory/Shannon/HuffmanSwapNormalizationBody.lean` (5)

- L1: `Mathlib.Logic.Equiv.Basic`
- L2: `InformationTheory.Shannon.HuffmanOptimality`
- L3: `InformationTheory.Shannon.HuffmanT1APPrimePartial`
- L4: `InformationTheory.Shannon.HuffmanT1APPrimeBody`
- L5: `InformationTheory.Shannon.HuffmanSwapStepChainBody`

### `InformationTheory/Shannon/HuffmanSwapStepChainBody.lean` (4)

- L1: `Mathlib.Logic.Equiv.Basic`
- L2: `InformationTheory.Shannon.HuffmanOptimality`
- L3: `InformationTheory.Shannon.HuffmanT1APPrimePartial`
- L4: `InformationTheory.Shannon.HuffmanT1APPrimeBody`

### `InformationTheory/Shannon/HuffmanT1APPrimeBody.lean` (3)

- L1: `Mathlib.Logic.Equiv.Basic`
- L2: `InformationTheory.Shannon.HuffmanOptimality`
- L3: `InformationTheory.Shannon.HuffmanT1APPrimePartial`

### `InformationTheory/Shannon/HuffmanT1APPrimePartial.lean` (2)

- L1: `Mathlib.Logic.Equiv.Basic`
- L2: `InformationTheory.Shannon.HuffmanOptimality`

### `InformationTheory/Shannon/HypercubeEdgeBoundary.lean` (1)

- L1: `InformationTheory.Shannon.LoomisWhitney`

### `InformationTheory/Shannon/HypercubeEdgeBoundarySharp.lean` (3)

- L1: `InformationTheory.Shannon.HypercubeEdgeBoundary`
- L2: `InformationTheory.Shannon.HanD`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.Base`

### `InformationTheory/Shannon/IIDProductInput.lean` (3)

- L1: `InformationTheory.Shannon.ChannelCoding`
- L2: `Mathlib.Probability.ProductMeasure`
- L3: `Mathlib.Probability.Independence.InfinitePi`

### `InformationTheory/Shannon/IIDProductInputJoint.lean` (1)

- L1: `InformationTheory.Shannon.IIDProductInput`

### `InformationTheory/Shannon/KLDivContinuous.lean` (3)

- L1: `InformationTheory.Shannon.SanovLDP`
- L2: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L3: `Mathlib.Topology.Algebra.Monoid`

### `InformationTheory/Shannon/LZ78ConverseAsymptotic.lean` (5)

- L1: `InformationTheory.Shannon.LempelZiv78`
- L2: `InformationTheory.Shannon.LZ78ZivInequality`
- L3: `Mathlib.Analysis.Asymptotics.Defs`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L5: `Mathlib.Order.Filter.AtTopBot.Basic`

### `InformationTheory/Shannon/LZ78ConverseUDObject.lean` (4)

- L1: `InformationTheory.Shannon.McMillanKraftBridge`
- L2: `InformationTheory.Shannon.LZ78GreedyParsing`
- L3: `Mathlib.Data.Nat.Bitwise`
- L4: `Mathlib.Data.Nat.Log`

### `InformationTheory/Shannon/LZ78GreedyLongestPrefix.lean` (5)

- L1: `InformationTheory.Shannon.LempelZiv78`
- L2: `InformationTheory.Shannon.LZ78GreedyParsing`
- L3: `InformationTheory.Shannon.LZ78GreedyParsingImpl`
- L4: `Mathlib.Data.List.Nodup`
- L5: `Mathlib.Data.List.Basic`

### `InformationTheory/Shannon/LZ78GreedyParsing.lean` (5)

- L1: `InformationTheory.Shannon.LempelZiv78`
- L2: `InformationTheory.Shannon.LZ78ZivInequality`
- L3: `Mathlib.Data.Nat.Log`
- L4: `Mathlib.Data.List.Basic`
- L5: `Mathlib.Data.List.Range`

### `InformationTheory/Shannon/LZ78GreedyParsingImpl.lean` (5)

- L1: `InformationTheory.Shannon.LempelZiv78`
- L2: `InformationTheory.Shannon.LZ78GreedyParsing`
- L3: `Mathlib.Data.Nat.Log`
- L4: `Mathlib.Data.List.Basic`
- L5: `Mathlib.Data.List.Range`

### `InformationTheory/Shannon/LZ78PhraseCountAsymptoticBody.lean` (7)

- L1: `InformationTheory.Shannon.LempelZiv78`
- L2: `InformationTheory.Shannon.LZ78ZivInequality`
- L3: `InformationTheory.Shannon.LZ78ConverseAsymptotic`
- L4: `Mathlib.Analysis.Asymptotics.Defs`
- L5: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L6: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L7: `Mathlib.Order.Filter.AtTopBot.Basic`

### `InformationTheory/Shannon/LZ78ZivCountingBody.lean` (9)

- L1: `InformationTheory.Shannon.LZ78GreedyLongestPrefix`
- L2: `InformationTheory.Shannon.LZ78PhraseCountAsymptoticBody`
- L3: `Mathlib.Data.Nat.Log`
- L4: `Mathlib.Data.List.Nodup`
- L5: `Mathlib.Data.Fintype.Card`
- L6: `Mathlib.Data.Fintype.Pi`
- L7: `Mathlib.Algebra.BigOperators.Group.List.Basic`
- L8: `Mathlib.Algebra.Order.BigOperators.Group.List`
- L9: `Mathlib.Analysis.SpecialFunctions.Log.Basic`

### `InformationTheory/Shannon/LZ78ZivEntropyBridge.lean` (4)

- L1: `InformationTheory.Shannon.ShannonMcMillanBreiman`
- L2: `InformationTheory.Shannon.LZ78GreedyLongestPrefix`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L4: `Mathlib.Analysis.Convex.Jensen`

### `InformationTheory/Shannon/LZ78ZivInequality.lean` (6)

- L1: `InformationTheory.Shannon.LempelZiv78`
- L2: `Mathlib.Data.Finset.Card`
- L3: `Mathlib.Data.Finset.Image`
- L4: `Mathlib.Data.Fintype.Card`
- L5: `Mathlib.Data.Fintype.Option`
- L6: `Mathlib.Data.Fintype.Prod`

### `InformationTheory/Shannon/LempelZiv78.lean` (5)

- L1: `InformationTheory.Shannon.Stationary`
- L2: `InformationTheory.Shannon.EntropyRate`
- L3: `InformationTheory.Shannon.ShannonMcMillanBreiman`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L5: `Mathlib.Topology.Order.LiminfLimsup`

### `InformationTheory/Shannon/LoomisWhitney.lean` (2)

- L1: `InformationTheory.Shannon.HanDShearer`
- L2: `Mathlib.Probability.UniformOn`

### `InformationTheory/Shannon/MACCornerAchievabilityBody.lean` (3)

- L1: `InformationTheory.Draft.Shannon.MACBodyDischarge`
- L2: `InformationTheory.Draft.Shannon.MACL1Discharge`
- L3: `InformationTheory.Shannon.AEPRate`

### `InformationTheory/Shannon/MACRandomCodebookAveraging.lean` (1)

- L1: `InformationTheory.Shannon.MACCornerAchievabilityBody`

### `InformationTheory/Shannon/MACTimeSharingBody.lean` (1)

- L1: `InformationTheory.Draft.Shannon.MACCornerPoint`

### `InformationTheory/Shannon/MIChainRule.lean` (3)

- L1: `InformationTheory.Shannon.MutualInfo`
- L2: `InformationTheory.Shannon.CondMutualInfo`
- L3: `InformationTheory.Shannon.Entropy`

### `InformationTheory/Shannon/MaxEntropy.lean` (2)

- L1: `InformationTheory.Shannon.Bridge`
- L2: `Mathlib.Probability.UniformOn`

### `InformationTheory/Shannon/MaxEntropyConstrained.lean` (4)

- L1: `InformationTheory.Shannon.CsiszarProjection`
- L2: `InformationTheory.Shannon.Chernoff`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L4: `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`

### `InformationTheory/Shannon/MaxEntropyConstrainedKKT.lean` (1)

- L1: `InformationTheory.Shannon.MaxEntropyConstrained`

### `InformationTheory/Shannon/McMillanKraftBridge.lean` (3)

- L1: `InformationTheory.Shannon.ShannonCode`
- L2: `Mathlib.InformationTheory.Coding.KraftMcMillan`
- L3: `Mathlib.InformationTheory.Coding.UniquelyDecodable`

### `InformationTheory/Shannon/MeasurePiTiltedFactorization.lean` (5)

- L1: `Mathlib.MeasureTheory.Constructions.Pi`
- L2: `Mathlib.MeasureTheory.Integral.Pi`
- L3: `Mathlib.MeasureTheory.Measure.Tilted`
- L4: `Mathlib.MeasureTheory.Measure.WithDensity`
- L5: `Mathlib.Probability.Moments.Basic`

### `InformationTheory/Shannon/MutualInfo.lean` (5)

- L1: `Mathlib.InformationTheory.KullbackLeibler.Basic`
- L2: `Mathlib.InformationTheory.KullbackLeibler.ChainRule`
- L3: `Mathlib.Probability.Independence.Basic`
- L4: `Mathlib.Probability.Kernel.CondDistrib`
- L5: `Mathlib.Probability.Kernel.Composition.MeasureCompProd`

### `InformationTheory/Shannon/ParallelGaussian.lean` (6)

- L1: `InformationTheory.Shannon.AWGN`
- L2: `InformationTheory.Shannon.AWGNMain`
- L3: `InformationTheory.Shannon.ChannelCoding`
- L4: `InformationTheory.Shannon.DifferentialEntropy`
- L5: `Mathlib.MeasureTheory.Constructions.Pi`
- L6: `Mathlib.Probability.Distributions.Gaussian.Real`

### `InformationTheory/Shannon/ParallelGaussianKKT.lean` (7)

- L1: `InformationTheory.Shannon.ParallelGaussian`
- L2: `InformationTheory.Shannon.ParallelGaussianL_PG0Discharge`
- L3: `Mathlib.Topology.Order.IntermediateValue`
- L4: `Mathlib.Topology.Algebra.Monoid`
- L5: `Mathlib.Topology.Algebra.Group.Defs`
- L6: `Mathlib.Topology.Order.OrderClosed`
- L7: `Mathlib.Analysis.Convex.SpecificFunctions.Basic`

### `InformationTheory/Shannon/ParallelGaussianL_PG0Discharge.lean` (1)

- L1: `InformationTheory.Shannon.ParallelGaussian`

### `InformationTheory/Shannon/Pi.lean` (1)

- L1: `InformationTheory.Shannon.Entropy`

### `InformationTheory/Shannon/Pinsker.lean` (4)

- L1: `InformationTheory.Shannon.Bridge`
- L2: `Mathlib.Data.Real.Sqrt`
- L3: `Mathlib.Algebra.Order.BigOperators.Ring.Finset`
- L4: `Mathlib.InformationTheory.KullbackLeibler.KLFun`

### `InformationTheory/Shannon/PinskerSharp.lean` (4)

- L1: `InformationTheory.Shannon.Pinsker`
- L2: `Mathlib.Analysis.Calculus.Deriv.MeanValue`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L4: `Mathlib.Analysis.SpecialFunctions.Log.Basic`

### `InformationTheory/Shannon/Polymatroid.lean` (2)

- L1: `InformationTheory.Polymatroid.Basic`
- L2: `InformationTheory.Shannon.HanD`

### `InformationTheory/Shannon/RateDistortionAchievability.lean` (4)

- L1: `InformationTheory.Shannon.RateDistortionConverse`
- L2: `Mathlib.Analysis.Convex.StdSimplex`
- L3: `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`
- L4: `Mathlib.Topology.Order.Compact`

### `InformationTheory/Shannon/RateDistortionAchievabilityPhaseB.lean` (5)

- L1: `InformationTheory.Shannon.RateDistortionAchievability`
- L2: `InformationTheory.Shannon.ChannelCodingAchievability`
- L3: `InformationTheory.Shannon.AEP`
- L4: `Mathlib.MeasureTheory.Function.ConvergenceInMeasure`
- L5: `Mathlib.Probability.StrongLaw`

### `InformationTheory/Shannon/RateDistortionAchievabilityPhaseC.lean` (1)

- L1: `InformationTheory.Shannon.RateDistortionAchievabilityPhaseB`

### `InformationTheory/Shannon/RateDistortionAchievabilityPhaseD.lean` (3)

- L1: `InformationTheory.Shannon.RateDistortionAchievabilityPhaseC`
- L2: `Mathlib.Analysis.SpecialFunctions.Exp`
- L3: `Mathlib.Order.Filter.AtTopBot.Basic`

### `InformationTheory/Shannon/RateDistortionConverse.lean` (6)

- L1: `InformationTheory.Shannon.MutualInfo`
- L2: `InformationTheory.Shannon.DPI`
- L3: `InformationTheory.Shannon.Bridge`
- L4: `InformationTheory.Shannon.MaxEntropy`
- L5: `InformationTheory.Shannon.Pi`
- L6: `InformationTheory.Fano.Measure`

### `InformationTheory/Shannon/RateDistortionConverseMonotone.lean` (1)

- L1: `InformationTheory.Shannon.RateDistortionConverse`

### `InformationTheory/Shannon/RateDistortionConvexityDischarge.lean` (3)

- L1: `InformationTheory.Draft.Shannon.RateDistortionConvexity`
- L2: `InformationTheory.Shannon.Sanov`
- L3: `Mathlib.InformationTheory.KullbackLeibler.KLFun`

### `InformationTheory/Shannon/SMBAlgoetCover.lean` (7)

- L1: `InformationTheory.Shannon.SMBChainRule`
- L2: `InformationTheory.Shannon.ShannonMcMillanBreiman`
- L3: `InformationTheory.Probability.TwoSidedExtension`
- L4: `Mathlib.MeasureTheory.OuterMeasure.BorelCantelli`
- L5: `Mathlib.MeasureTheory.Integral.Lebesgue.Markov`
- L6: `Mathlib.Analysis.PSeries`
- L7: `Mathlib.Topology.Algebra.Order.LiminfLimsup`

### `InformationTheory/Shannon/SMBChainRule.lean` (5)

- L1: `InformationTheory.Shannon.Stationary`
- L2: `InformationTheory.Shannon.EntropyRate`
- L3: `InformationTheory.Shannon.BirkhoffErgodic`
- L4: `Mathlib.Probability.Kernel.CondDistrib`
- L5: `Mathlib.MeasureTheory.Integral.Lebesgue.Countable`

### `InformationTheory/Shannon/Sanov.lean` (2)

- L1: `InformationTheory.Shannon.Stein`
- L2: `Mathlib.InformationTheory.KullbackLeibler.Basic`

### `InformationTheory/Shannon/SanovLDP.lean` (3)

- L1: `InformationTheory.Shannon.Sanov`
- L2: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L3: `Mathlib.Analysis.Asymptotics.Lemmas`

### `InformationTheory/Shannon/SanovLDPEquality.lean` (5)

- L1: `InformationTheory.Shannon.SanovLDP`
- L2: `InformationTheory.Shannon.KLDivContinuous`
- L3: `Mathlib.Algebra.Order.Floor.Semiring`
- L4: `Mathlib.Algebra.BigOperators.Fin`
- L5: `Mathlib.Data.Nat.Choose.Multinomial`

### `InformationTheory/Shannon/ShannonCode.lean` (4)

- L1: `Mathlib.Analysis.SpecialFunctions.Log.Base`
- L2: `Mathlib.MeasureTheory.Measure.Real`
- L3: `Mathlib.Probability.ProbabilityMassFunction.Basic`
- L4: `Mathlib.Algebra.Order.Floor.Semiring`

### `InformationTheory/Shannon/ShannonCodeKraftReverse.lean` (6)

- L1: `Mathlib.Data.List.OfFn`
- L2: `Mathlib.Data.List.Sort`
- L3: `Mathlib.Data.Finset.Dedup`
- L4: `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- L5: `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- L6: `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`

### `InformationTheory/Shannon/ShannonHartley.lean` (8)

- L1: `InformationTheory.Shannon.AWGN`
- L2: `InformationTheory.Shannon.AWGNAchievability`
- L3: `InformationTheory.Shannon.AWGNConverse`
- L4: `InformationTheory.Shannon.AWGNMain`
- L5: `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- L6: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- L7: `Mathlib.Analysis.SpecialFunctions.Complex.LogBounds`
- L8: `Mathlib.Topology.Algebra.Order.LiminfLimsup`

### `InformationTheory/Shannon/ShannonMcMillanBreiman.lean` (4)

- L1: `InformationTheory.Shannon.Stationary`
- L2: `InformationTheory.Shannon.EntropyRate`
- L3: `InformationTheory.Shannon.Bridge`
- L4: `Mathlib.Topology.Order.LiminfLimsup`

### `InformationTheory/Shannon/SlepianWolf.lean` (7)

- L1: `InformationTheory.Shannon.Bridge`
- L2: `InformationTheory.Shannon.CondMutualInfo`
- L3: `InformationTheory.Shannon.DPI`
- L4: `InformationTheory.Shannon.Entropy`
- L5: `InformationTheory.Shannon.Pi`
- L6: `InformationTheory.Fano.Measure`
- L7: `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`

### `InformationTheory/Shannon/SlepianWolfAchievability.lean` (2)

- L1: `InformationTheory.Shannon.SlepianWolf`
- L2: `InformationTheory.Shannon.AEP`

### `InformationTheory/Shannon/SlepianWolfBinning.lean` (3)

- L1: `InformationTheory.Shannon.SlepianWolfAchievability`
- L2: `Mathlib.Probability.UniformOn`
- L3: `Mathlib.MeasureTheory.Constructions.Pi`

### `InformationTheory/Shannon/SlepianWolfConditionalTypicalSlice.lean` (2)

- L1: `InformationTheory.Shannon.AEP`
- L2: `InformationTheory.Shannon.ChannelCoding`

### `InformationTheory/Shannon/SlepianWolfFullRateRegion.lean` (3)

- L1: `InformationTheory.Shannon.SlepianWolfBinning`
- L2: `InformationTheory.Shannon.SlepianWolfConditionalTypicalSlice`
- L3: `InformationTheory.Shannon.SlepianWolfAchievability`

### `InformationTheory/Shannon/StamGaussianBound.lean` (4)

- L1: `Mathlib.Probability.Distributions.Gaussian.Real`
- L2: `Mathlib.Probability.Independence.Basic`
- L3: `Mathlib.Tactic.Positivity`
- L4: `InformationTheory.Shannon.FisherInfoV2DeBruijn`

### `InformationTheory/Shannon/Stationary.lean` (4)

- L1: `Mathlib.Dynamics.Ergodic.Ergodic`
- L2: `Mathlib.Dynamics.Ergodic.MeasurePreserving`
- L3: `Mathlib.Probability.IdentDistrib`
- L4: `Mathlib.MeasureTheory.MeasurableSpace.Basic`

### `InformationTheory/Shannon/StationaryKernel.lean` (4)

- L1: `InformationTheory.Shannon.LZ78ZivEntropyBridge`
- L2: `InformationTheory.Shannon.LZ78ZivCountingBody`
- L3: `InformationTheory.Shannon.EntropyRate`
- L4: `Mathlib.Algebra.BigOperators.Group.Finset.Basic`

### `InformationTheory/Shannon/Stein.lean` (7)

- L1: `InformationTheory.Shannon.AEP`
- L2: `InformationTheory.Shannon.DPI`
- L3: `InformationTheory.Shannon.MutualInfo`
- L4: `Mathlib.InformationTheory.KullbackLeibler.Basic`
- L5: `Mathlib.InformationTheory.KullbackLeibler.ChainRule`
- L6: `Mathlib.MeasureTheory.Constructions.Pi`
- L7: `Mathlib.Probability.Kernel.Composition.MeasureCompProd`

### `InformationTheory/Shannon/StrongStein.lean` (2)

- L1: `InformationTheory.Shannon.Stein`
- L2: `Mathlib.Topology.Order.LiminfLimsup`

### `InformationTheory/Shannon/StrongTypicality.lean` (3)

- L1: `InformationTheory.Shannon.AEP`
- L2: `InformationTheory.Shannon.Sanov`
- L3: `Mathlib.MeasureTheory.Order.Group.Lattice`

### `InformationTheory/Shannon/TypeClassLowerBound.lean` (1)

- L1: `InformationTheory.Shannon.SanovLDPEquality`

### `InformationTheory/Shannon/TypedRV.lean` (7)

- L1: `InformationTheory.Shannon.Bridge`
- L2: `InformationTheory.Shannon.MutualInfo`
- L3: `InformationTheory.Shannon.CondMutualInfo`
- L4: `InformationTheory.Shannon.DPI`
- L5: `InformationTheory.Shannon.SlepianWolf`
- L6: `InformationTheory.Fano.Measure`
- L8: `Mathlib.InformationTheory.KullbackLeibler.Basic`

### `InformationTheory/Shannon/WhittakerShannonPartial.lean` (3)

- L1: `InformationTheory.Shannon.ShannonHartley`
- L3: `Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc`
- L4: `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`

### `InformationTheory/Shannon/WynerZiv.lean` (2)

- L1: `InformationTheory.Shannon.RateDistortionAchievability`
- L2: `InformationTheory.Draft.Shannon.RateDistortionConverseNLetter`

### `InformationTheory/Shannon/WynerZivBinningBody.lean` (4)

- L1: `InformationTheory.Shannon.WynerZiv`
- L2: `InformationTheory.Draft.Shannon.WynerZivAchievability`
- L3: `InformationTheory.Shannon.SlepianWolfBinning`
- L4: `InformationTheory.Shannon.SlepianWolfFullRateRegion`

### `InformationTheory/Shannon/WynerZivConvexityBody.lean` (1)

- L1: `InformationTheory.Shannon.WynerZivDischarge`

### `InformationTheory/Shannon/WynerZivDischarge.lean` (1)

- L1: `InformationTheory.Shannon.WynerZiv`

## Missing import candidates

linter が「これらを追加 import すべき」と報告した module。多くは `Lean.Parser.Command` 等の **linter 自身の elaboration を満たすための内部要件** で実用上は無視可能ですが、InformationTheory 内部 module の名前があれば本物の不足の可能性。

### `InformationTheory/Draft/Shannon/BroadcastChannel.lean` (2)

- `Mathlib.Data.ENNReal.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Draft/Shannon/BroadcastChannelSuperposition.lean` (1)

- `InformationTheory.Shannon.ChannelCoding`

### `InformationTheory/Draft/Shannon/BroadcastChannelSuperpositionBody.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Draft/Shannon/BrunnMinkowski.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Draft/Shannon/BrunnMinkowskiConcavity.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Draft/Shannon/BrunnMinkowskiFunctional.lean` (2)

- `Mathlib.MeasureTheory.Constructions.BorelSpace.Basic`
- `Mathlib.MeasureTheory.Measure.Typeclasses.Probability`

### `InformationTheory/Draft/Shannon/ChannelCodingConverseGeneralComplete.lean` (1)

- `Mathlib.MeasureTheory.Constructions.Polish.Basic`

### `InformationTheory/Draft/Shannon/ChernoffBandMassDischarge.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Draft/Shannon/ChernoffConverse.lean` (3)

- `Mathlib.Data.Finset.Defs`
- `Mathlib.Data.Real.Basic`
- `Mathlib.Order.Filter.Defs`

### `InformationTheory/Draft/Shannon/ChernoffInformation.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Draft/Shannon/ChernoffPerTiltDischarge.lean` (1)

- `Mathlib.Data.Fintype.Defs`

### `InformationTheory/Draft/Shannon/ChernoffPerTiltSanov.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Draft/Shannon/ChernoffSanovDischarge.lean` (3)

- `Mathlib.Data.Finset.Defs`
- `Mathlib.Data.Real.Basic`
- `Mathlib.Order.Filter.Defs`

### `InformationTheory/Draft/Shannon/Cramer.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Draft/Shannon/CramerCLTClosure.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Draft/Shannon/CramerLC2PhaseC.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Draft/Shannon/CramerPhaseDGapWorkaround.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Draft/Shannon/EPIConvolutionDensity.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Draft/Shannon/InfinitePiTiltedChangeOfMeasure.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Draft/Shannon/LZ78ConverseDischarge.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Draft/Shannon/LZ78DistinctEncoding.lean` (2)

- `Mathlib.Data.ENNReal.Basic`
- `Mathlib.Data.Fintype.Defs`

### `InformationTheory/Draft/Shannon/LZ78FinalGlue.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Draft/Shannon/LZ78SMBSandwich.lean` (2)

- `Mathlib.Data.ENNReal.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Draft/Shannon/MACCornerPoint.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Draft/Shannon/MACFanoConverseBody.lean` (2)

- `Mathlib.Data.ENNReal.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Draft/Shannon/MACL1Discharge.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Draft/Shannon/MACL2Discharge.lean` (2)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`
- `Mathlib.Analysis.SpecialFunctions.Log.Basic`

### `InformationTheory/Draft/Shannon/MACPerEventAEPDecay.lean` (2)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`
- `Mathlib.Order.Filter.Defs`

### `InformationTheory/Draft/Shannon/MultipleAccessChannel.lean` (2)

- `Mathlib.Data.Real.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Draft/Shannon/MultivariateDiffEntropy.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Draft/Shannon/RateDistortionAchievabilityPhaseE.lean` (1)

- `Mathlib.Order.Filter.Defs`

### `InformationTheory/Draft/Shannon/RateDistortionConverseNLetter.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Draft/Shannon/RateDistortionConvexity.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Draft/Shannon/RelayCutset.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Draft/Shannon/RelayInnerBound.lean` (2)

- `Mathlib.Data.Real.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Draft/Shannon/WynerZivAchievability.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Draft/Shannon/WynerZivConverse.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Draft/Shannon/WynerZivConverseChain.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Fano/BinaryJensen.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Fano/CondEntropy.lean` (1)

- `Mathlib.Data.Fintype.Defs`

### `InformationTheory/Fano/Core.lean` (1)

- `Mathlib.Data.Fintype.Defs`

### `InformationTheory/Fano/DPI.lean` (1)

- `Mathlib.Data.Finset.Defs`

### `InformationTheory/Fano/Entropy.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Fano/Measure.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/InformationTheory/Asymptotic.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Polymatroid/Basic.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Probability/TwoSidedExtension.lean` (1)

- `Mathlib.Data.Finset.Max`

### `InformationTheory/Shannon/AEPRate.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/AWGN.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/AWGNAchievability.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/AWGNAchievabilityDischarge.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/AWGNConverse.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/AWGNF1Discharge.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/AWGNF2F3Discharge.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/AWGNMIBridge.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/AWGNMain.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/ArithmeticCoding.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/BackwardFiltration.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/BackwardMartingale.lean` (2)

- `Mathlib.Data.Real.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/BirkhoffErgodic.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/BlockwiseChannel.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/BrascampLieb.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/Bridge.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/BroadcastChannelAveraging.lean` (2)

- `Mathlib.Data.ENNReal.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/BroadcastChannelRandomCodebook.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/BrunnMinkowski1DSuperlevelBody.lean` (1)

- `Mathlib.Data.Set.Defs`

### `InformationTheory/Shannon/BrunnMinkowskiClosure.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/BrunnMinkowskiLayerCakeBody.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/BrunnMinkowskiPLBody.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/ChannelCodingAchievability.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/ChannelCodingConverse.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/ChannelCodingConverseGeneral.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/ChannelCodingConverseGeneralStrong.lean` (1)

- `Mathlib.MeasureTheory.Constructions.Polish.Basic`

### `InformationTheory/Shannon/ChannelCodingConverseMemorylessPure.lean` (1)

- `Mathlib.MeasureTheory.Constructions.Polish.Basic`

### `InformationTheory/Shannon/ChannelCodingFeedback.lean` (1)

- `Mathlib.MeasureTheory.Constructions.Polish.Basic`

### `InformationTheory/Shannon/ChannelCodingFeedbackComplete.lean` (1)

- `Mathlib.MeasureTheory.Constructions.Polish.Basic`

### `InformationTheory/Shannon/ChannelCodingShannonTheorem.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/ChannelCodingShannonTheoremGeneral.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/ChannelCodingStrongConverse.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/Chernoff.lean` (1)

- `Mathlib.Data.Fintype.Defs`

### `InformationTheory/Shannon/ChernoffNLetterZSum.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/CondMutualInfo.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/Converse.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/CramerLC2Discharge.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/CramerLC2DischargeExt.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/CsiszarProjection.lean` (1)

- `Mathlib.Data.Fintype.Defs`

### `InformationTheory/Shannon/DPI.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/DifferentialEntropy.lean` (1)

- `Mathlib.Data.Real.Basic`

### `InformationTheory/Shannon/EPIPlumbing.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/EPIStamDischarge.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/EPIStamInequalityBody.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/EPIStamStep12Body.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/EPIStamStep3Body.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/Entropy.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/EntropyPowerInequality.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/EntropyRate.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/FisherDeBruijnGaussianWitness.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/FisherInfo.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/FisherInfoGaussian.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/FisherInfoV2.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/FisherInfoV2DeBruijnBody.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/FisherInfoV2HeatFlowBody.lean` (1)

- `Mathlib.Data.Real.Basic`

### `InformationTheory/Shannon/GaussianPDFVarianceDerivBody.lean` (1)

- `Mathlib.Data.Real.Basic`

### `InformationTheory/Shannon/GeneralDMC.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/Han.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/HanD.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/HanDAverage.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/HanDShearer.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/HeatFlowPath.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/HoeffdingSandwich.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/HoeffdingTradeoff.lean` (2)

- `Mathlib.Data.Real.Basic`
- `Mathlib.Order.Filter.Defs`

### `InformationTheory/Shannon/Huffman.lean` (2)

- `Mathlib.Data.Finset.Defs`
- `Mathlib.Data.Real.Basic`

### `InformationTheory/Shannon/HuffmanColexDeterminism.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/HuffmanFirstStepProbe.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/HuffmanMergedAuxIdent.lean` (2)

- `Mathlib.Data.Real.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/HuffmanMergedIdentBody.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/HuffmanOptimality.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/HuffmanStrongForm.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/HuffmanSwapNormCompletion.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/HuffmanSwapNormalizationBody.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/HuffmanSwapStepChainBody.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/HuffmanT1APPrimeBody.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/HuffmanT1APPrimePartial.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/HypercubeEdgeBoundary.lean` (2)

- `Mathlib.Data.Nat.Notation`
- `Mathlib.Logic.Function.Basic`

### `InformationTheory/Shannon/HypercubeEdgeBoundarySharp.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/IIDProductInput.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/IIDProductInputJoint.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/LZ78ConverseAsymptotic.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/LZ78ConverseUDObject.lean` (1)

- `Mathlib.Tactic.TypeStar`

### `InformationTheory/Shannon/LZ78GreedyLongestPrefix.lean` (1)

- `Mathlib.Tactic.TypeStar`

### `InformationTheory/Shannon/LZ78GreedyParsing.lean` (1)

- `Mathlib.Data.Fintype.Defs`

### `InformationTheory/Shannon/LZ78GreedyParsingImpl.lean` (1)

- `Mathlib.Data.Fintype.Defs`

### `InformationTheory/Shannon/LZ78PhraseCountAsymptoticBody.lean` (1)

- `Mathlib.Order.Filter.Defs`

### `InformationTheory/Shannon/LZ78ZivCountingBody.lean` (1)

- `Mathlib.Data.Fintype.Defs`

### `InformationTheory/Shannon/LZ78ZivEntropyBridge.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/LZ78ZivInequality.lean` (1)

- `Mathlib.Tactic.TypeStar`

### `InformationTheory/Shannon/LempelZiv78.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/LoomisWhitney.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/MACCornerAchievabilityBody.lean` (1)

- `Mathlib.Tactic.TypeStar`

### `InformationTheory/Shannon/MACRandomCodebookAveraging.lean` (2)

- `Mathlib.Data.ENNReal.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/MACTimeSharingBody.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/MIChainRule.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/MaxEntropy.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/MaxEntropyConstrained.lean` (2)

- `Mathlib.Data.Fintype.Defs`
- `Mathlib.Data.Real.Basic`

### `InformationTheory/Shannon/MaxEntropyConstrainedKKT.lean` (1)

- `Mathlib.Analysis.SpecialFunctions.Log.Basic`

### `InformationTheory/Shannon/McMillanKraftBridge.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/MeasurePiTiltedFactorization.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/MutualInfo.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/ParallelGaussian.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/ParallelGaussianKKT.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/ParallelGaussianL_PG0Discharge.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/Pi.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/Pinsker.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/PinskerSharp.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/Polymatroid.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/RateDistortionAchievability.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/RateDistortionAchievabilityPhaseB.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/RateDistortionAchievabilityPhaseC.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/RateDistortionAchievabilityPhaseD.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/RateDistortionConverse.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/RateDistortionConverseMonotone.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/RateDistortionConvexityDischarge.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/SMBAlgoetCover.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/SMBChainRule.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/Sanov.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/SanovLDP.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/SanovLDPEquality.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/ShannonCode.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/ShannonCodeKraftReverse.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/ShannonHartley.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/ShannonMcMillanBreiman.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/SlepianWolf.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/SlepianWolfAchievability.lean` (1)

- `Mathlib.Data.ENNReal.Basic`

### `InformationTheory/Shannon/SlepianWolfBinning.lean` (1)

- `Lean.Parser.Command`

### `InformationTheory/Shannon/SlepianWolfConditionalTypicalSlice.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/SlepianWolfFullRateRegion.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/StamGaussianBound.lean` (1)

- `Mathlib.Data.Real.Basic`

### `InformationTheory/Shannon/Stationary.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/StationaryKernel.lean` (1)

- `Mathlib.Tactic.TypeStar`

### `InformationTheory/Shannon/Stein.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/StrongStein.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/StrongTypicality.lean` (2)

- `Mathlib.Data.Real.Basic`
- `Mathlib.Order.Filter.Defs`

### `InformationTheory/Shannon/WynerZiv.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/WynerZivBinningBody.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/WynerZivConvexityBody.lean` (1)

- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### `InformationTheory/Shannon/WynerZivDischarge.lean` (2)

- `Mathlib.Data.ENNReal.Basic`
- `Mathlib.MeasureTheory.MeasurableSpace.Defs`

