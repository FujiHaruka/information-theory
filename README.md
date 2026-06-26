# Shannon Information Theory in Lean 4

A Lean 4 + [Mathlib](https://github.com/leanprover-community/mathlib4) formalization of
Shannon information theory, following Cover & Thomas, *Elements of Information Theory*.

The project targets **Mathlib-PR quality**: an English codebase that follows Mathlib's
naming, documentation, and module-structure conventions, so finished material can
eventually be upstreamed.

## Formalized results

Selected headline theorems, organized after the chapters of Cover & Thomas. Every result
listed below is **complete and machine-checked — no `sorry`, no axioms beyond Lean's
standard `propext` / `Classical.choice` / `Quot.sound`**. Names link to their source.

| Ch. | Topic | Key results |
|-----|-------|-------------|
| 2 | Entropy, mutual information, DPI | [`entropy`](InformationTheory/Shannon/Bridge.lean) · [`mutualInfo`](InformationTheory/Shannon/MutualInfo.lean) · [`mutualInfo_chain_rule`](InformationTheory/Shannon/CondMutualInfo.lean) · [`mutualInfo_le_of_postprocess`](InformationTheory/Shannon/DPI.lean) · [`fano_inequality_measure_theoretic`](InformationTheory/Fano/Measure.lean) |
| 3 | Asymptotic equipartition (AEP) | [`aep_ae`](InformationTheory/Shannon/AEP/Basic/Core.lean) · [`typicalSet`](InformationTheory/Shannon/AEP/Basic/Core.lean) · [`stronglyTypicalSet`](InformationTheory/Shannon/StrongTypicality.lean) |
| 4 | Entropy rate & the SMB theorem | [`entropyRate`](InformationTheory/Shannon/EntropyRate.lean) · [`shannon_mcmillan_breiman`](InformationTheory/Shannon/SMB/AlgoetCover/Liminf.lean) · [`birkhoff_ergodic_ae`](InformationTheory/Shannon/BirkhoffErgodic.lean) |
| 5 | Data compression | [`shannonCode_expected_length_bounds`](InformationTheory/Shannon/ShannonCode/Basic.lean) · [`kraftSum_le_one_of_uniquelyDecodable`](InformationTheory/Shannon/McMillanKraftBridge.lean) (McMillan) · [`huffmanLength_optimal`](InformationTheory/Shannon/Huffman/StrongForm.lean) |
| 7 | Channel capacity | [`shannon_noisy_channel_coding_theorem_general_full`](InformationTheory/Shannon/ChannelCoding/ShannonTheoremMaxError.lean) · [`channel_coding_feedback_converse`](InformationTheory/Shannon/ChannelCoding/Feedback.lean) · [`shannon_converse_single_shot`](InformationTheory/Shannon/Converse.lean) |
| 8 | Differential entropy | [`differentialEntropy_gaussianReal`](InformationTheory/Shannon/DifferentialEntropy.lean) · [`jointDifferentialEntropyPi_le_sum`](InformationTheory/Shannon/MultivariateDiffEntropy.lean) |
| 9 | Gaussian channel | [`awgn_capacity_closed_form_genuine`](InformationTheory/Shannon/AWGN/CapacityConverseMaxent.lean) · [`parallel_gaussian_capacity_formula_minimal`](InformationTheory/Shannon/ParallelGaussian/PerCoordRegularity.lean) (water-filling) |
| 10 | Rate–distortion | [`rate_distortion_achievability`](InformationTheory/Shannon/RateDistortion/AchievabilityStrongTypicality.lean) · [`rateDistortionFunction_convexOn`](InformationTheory/Shannon/RateDistortion/Convexity.lean) · [`rate_distortion_converse_n_letter_singleLetter`](InformationTheory/Shannon/RateDistortion/ConverseNLetter.lean) |
| 11 | Hypothesis testing & large deviations | [`stein_converse_finite_n`](InformationTheory/Shannon/Stein/Converse.lean) · [`sanov_ldp_upper_bound`](InformationTheory/Shannon/Sanov/LDP.lean) · [`tvNorm_le_sqrt_klDiv`](InformationTheory/Shannon/Pinsker/Basic.lean) (Pinsker) |
| 12 | Maximum entropy | [`entropy_le_log_card`](InformationTheory/Shannon/MaxEntropy/Basic.lean) · [`expFamily_maximizes_entropy_of_KKT`](InformationTheory/Shannon/MaxEntropy/ConstrainedKKT.lean) |
| 13 | Universal coding (LZ78) | [`lz78_asymptotic_optimality_with_greedy`](InformationTheory/Shannon/LZ78/AsymptoticOptimality/ParentBridgeAchievability.lean) · [`arithmeticCode_expected_length_bounds`](InformationTheory/Shannon/ArithmeticCoding.lean) |
| 15 | Distributed source coding | [`slepian_wolf_full_rate_region_achievability`](InformationTheory/Shannon/SlepianWolf/FullRateRegion/PairBound.lean) |
| 17 | Entropy inequalities | [`han_inequality`](InformationTheory/Shannon/Han/Basic.lean) · [`shearer_inequality`](InformationTheory/Shannon/Han/DShearer.lean) · [`loomis_whitney`](InformationTheory/Shannon/LoomisWhitney.lean) · [`brascamp_lieb_finset`](InformationTheory/Shannon/BrascampLieb.lean) · [`entropy_power_inequality_of_density`](InformationTheory/Shannon/EPI/DensityForm.lean) |

The library root [`InformationTheory.lean`](InformationTheory.lean) imports every module.

## Build

Single-file checks against warm Mathlib oleans are the inner loop:

```bash
lake env lean InformationTheory/<path>.lean   # definitive synchronous check; silent = clean
```

This is a theorem-proving library: do not `import Mathlib` (it pulls in 8000+ modules) and
do not add a `[[lean_exe]]` target (it forces native compilation of all of Mathlib). See
[`CLAUDE.md`](CLAUDE.md) for the full import and build policy.

## Repository

- [`InformationTheory/`](InformationTheory/) — the Lean library.
- [`docs/rules/`](docs/rules/) — code conventions (naming, docstrings, Lean style, module structure).
- [`docs/`](docs/) — plans, inventories, and the textbook roadmap.
- [`CLAUDE.md`](CLAUDE.md) — project rules and workflow.
</content>
</invoke>
