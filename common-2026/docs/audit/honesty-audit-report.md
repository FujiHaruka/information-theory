# Honesty audit — full-codebase report

> ⚠️ **Historical snapshot** (2026-05-22, post-cleanup update 2026-05-24). 個別の defect/suspect 行は **rename / retract / honest-rebrand を経て陳腐化している**。現状計数は code の `@audit:KIND(SLUG)` タグが SoT で、以下で取れる:
>
> ```bash
> deno run -A scripts/audit_db.ts scan      # kind 別 count + slug histogram
> rg -nB1 "@audit:defect" Common2026/        # defect 全件の file:line + context
> rg "@audit:defer\(awgn-achievability-typicality\)" Common2026/  # 特定 plan 配下
> ```
>
> 語彙: `docs/audit/audit-tags.md`。本文書は **「pre-cleanup の defect 101 規模の audit pass で何を学んだか」** という方法論的価値で保存。

Date: 2026-05-22. Scope: all 2942 theorems/lemmas (Exam excluded) across 241 files.
Bar: CLAUDE.md「検証の誠実性」標準B. Tooling: `scripts/audit_db.ts` (SQLite worklist, `docs/audit/honesty.db`).

## Result

| status | count |
|---|---:|
| ok | 2480 |
| suspect (honest 🟢ʰ remaining tasks) | 361 |
| **defect** | **101** |
| total | 2942 |

`0 sorry`-dependent theorems confirmed (every `sorry` flag was a false positive — see Process notes).

## Method

- **Wave 1 (Sonnet, ~38 shifts × 20)**: every theorem audited, flag-score-DESC first so the 117 flagged consumed early. 3-tier read (signature/doc → body → unfold project-defined predicates).
- **QA (Opus, 2 spot-checks of 10 random `ok` each, at the 1000/2000-`ok` boundaries)**: 0 flips both times → first-pass `ok` classification reliable.
- **Wave 2 (Opus deep-dive, targeted)**: 35 "odd" suspects (non-load-bearing verdict codes) + a flag-score sample of the load-bearing pool + a name-laundering sweep + a conflict adjudication.
- **`#print axioms` settle**: all 9 `sorry`-flagged defects re-checked authoritatively → all sorry-free → corrected to `ok`.

## Defects (101) — actionable

### circular (32) — body returns a hypothesis whose type ≡ conclusion
```
AWGNAchievability.lean:61          AWGN.awgn_achievability
AWGNF2F3Discharge.lean:205         AWGN.awgn_achievability_jointly_typical_body
AWGNF2F3Discharge.lean:272         AWGN.awgn_converse_fano_body
AWGNMIBridgeDischarge.lean:136     AWGN.awgn_mi_decomp_id
BrunnMinkowskiFunctional.lean:132  BrunnMinkowski.isLogConcaveDensity_nonneg_convex
BrunnMinkowskiFunctional.lean:197  BrunnMinkowski.prekopa_leindler_inequality
BrunnMinkowskiFunctional.lean:234  BrunnMinkowski.brunn_minkowski_from_prekopa_leindler
BrunnMinkowskiFunctional.lean:249  BrunnMinkowski.brunn_minkowski_sharp_from_full_lambda
BrunnMinkowskiFunctional.lean:329  BrunnMinkowski.entropy_ge_logVolume_of_logConcave
BrunnMinkowskiFunctional.lean:372  BrunnMinkowski.prekopa_leindler_lam_zero
BrunnMinkowskiFunctional.lean:384  BrunnMinkowski.prekopa_leindler_lam_one
BrunnMinkowskiFunctional.lean:396  BrunnMinkowski.prekopa_leindler_lam_half
BrunnMinkowskiLayerCakeBody.lean:227  BrunnMinkowski.pl1SuperLevel_pos_of_hyp
ChernoffPerTiltSanov.lean:315      ChernoffPerTiltSanov.isChernoffNLetterRN.exists_witness
ChernoffPerTiltSanov.lean:325      ChernoffPerTiltSanov.isChernoffNLetterRN.of_witness
EPIStamStep12Body.lean:140         EPIStamStep12Body.stam_convex_fisher_bound
EPIStamStep3Body.lean:181          EPIStamStep3Body.isStamFisherCoupling_of_cauchySchwarz
LZ78SMBSandwich.lean:362           IsLZ78ConverseChainHyp.ofSMBBridge
MACCornerAchievabilityBody.lean:252  mac_innerBoundExistence_of_achievableWithError
MACCornerAchievabilityBody.lean:272  mac_capacity_region_inner_bound_of_achievableWithError
MACCornerAchievabilityBody.lean:283  mac_capacity_region_consistent_of_achievableWithError
MACRandomCodebookAveraging.lean:521  mac_achievableWithError_of_markov
MACRandomCodebookAveraging.lean:537  mac_innerBoundExistence_of_markov
MACRandomCodebookAveraging.lean:573  mac_inner_bound_with_averaging
MACRandomCodebookAveraging.lean:586  mac_capacity_region_consistent_of_averaging
ParallelGaussianL_PG0Discharge.lean:163  ParallelGaussian.parallel_gaussian_capacity_formula_PG0_discharged
RelayCFBinningBody.lean:488        relay_cf_inner_bound_binning_discharged_witness
RelayCutset.lean:365               relay_broadcast_cut
RelayCutset.lean:392               relay_mac_cut
WhittakerShannonFull.lean:382      WhittakerShannonFull.ShannonHartley_IsTwoWDegreesOfFreedom_of_full
WynerZivBinningBody.lean:520       wzAchievability_existence_body
WynerZivBinningBody.lean:594       wzBinning_E_bin_expected_le_slice
```

### degenerate_def (41) — gating predicate is `Prop := True` / vacuous, theorem proves nothing
```
BroadcastChannelExistenceBridgeBody.lean:301  bc_random_codebook_markov_of_ensemble
EntropyPowerInequality.lean:143    isStamInequalityHypothesis_trivial
EntropyPowerInequality.lean:157    isDeBruijnIntegrationHypothesis_trivial
EPIL3Integration.lean:122          epi_l1_of_integrated_pipeline
EPIL3Integration.lean:130          epi_l2_of_integrated_pipeline
EPIL3Integration.lean:444          isDeBruijnIntegrationHypothesis_via_v2
EPIL3Integration.lean:479          entropy_power_inequality_integrated_iff_original
EPIPlumbing.lean:59                EntropyPowerInequality.entropyPower_pos_iff
EPIStamInequalityBody.lean:111     isStamScoreConvolution_trivial
EPIStamInequalityBody.lean:115     isStamScoreConvolution_symm
EPIStamInequalityBody.lean:299     isStamScoreConvolution_of_gaussian
EPIStamStep12Body.lean:186         isStamScoreConvolution_of_hyp
FisherInfoV2DeBruijn.lean:447      FisherInfoV2.epi_de_bruijn_integration_v2_discharge
HuffmanT1APPrimeBody.lean:578      Huffman.huffmanLength_optimal_self  (conclusion is X ≤ X)
LempelZiv78.lean:243               IsZivInequalityPassthrough.trivial
LempelZiv78.lean:270               IsLZ78ConversePassthrough.trivial
LempelZiv78.lean:295               IsSMBSandwichPassthrough.trivial
LZ78ConverseAsymptotic.lean:230    IsZivInequalityPassthrough.ofAsymptotic
LZ78ConverseAsymptotic.lean:490    IsSMBSandwichPassthrough.ofPhraseCountSandwich
LZ78ConverseAsymptotic.lean:501    IsLZ78PhraseCountSandwich.toBothPassthroughs
LZ78ConverseDischarge.lean:269     IsLZ78ConversePassthrough.ofChainHyp
LZ78ConverseDischarge.lean:283     IsLZ78ConversePassthrough.ofLowerBound
LZ78FinalGlue.lean:142             IsZivInequalityPassthrough.ofAchievabilityChainHyp
LZ78GreedyParsingImpl.lean:412     lz78GreedyImplEncodingLength_isZivInequalityPassthrough
LZ78GreedyParsingImpl.lean:418     lz78GreedyImplEncodingLength_isLZ78ConversePassthrough
LZ78SMBSandwich.lean:281           IsSMBSandwichPassthrough.ofTendsto
LZ78SMBSandwich.lean:288           IsSMBSandwichPassthrough.ofLiminf
LZ78SMBSandwich.lean:295           IsSMBSandwichPassthrough.ofLimsup
LZ78SMBSandwich.lean:318           IsSMBSandwichPassthrough.ofErgodic
LZ78ZivInequality.lean:325         IsZivInequalityPassthrough.ofZivCountingBound
MaxEntropyConstrainedKKT.lean:334  expFamilyDist_satisfies_constraints_iff  (statement is A ↔ A)
ShannonHartley.lean:275            mk_IsBandlimitedSamplingHypothesis
WhittakerShannonFull.lean:307      mk_IsBandlimitedFull
WhittakerShannonFull.lean:312      IsBandlimitedFull_of_partial
WhittakerShannonFull.lean:495      IsBandlimitedFull_smul
WhittakerShannonFull.lean:502      IsBandlimitedFull_add
WhittakerShannonFull.lean:509      IsBandlimitedFull_neg
WhittakerShannonFull.lean:515      IsBandlimitedFull_zero
WhittakerShannonPartial.lean:208   mk_IsWhittakerShannonInterpolation
WhittakerShannonPartial.lean:273   ShannonHartley_IsBandlimitedSamplingHypothesis_of_interp
WhittakerShannonPartial.lean:282   ShannonHartley_IsBandlimitedKernel_of_pos
```

### true_residual (11) — real obligation hidden behind `True` / unused slot
```
BroadcastChannel.lean:436          bc_common_rate_bound        (_h_fano:True, _h_chain:True)
BroadcastChannel.lean:460          bc_private_rate_bound
LempelZiv78.lean:237               isZivInequalityPassthrough_def   (predicate = True)
LempelZiv78.lean:264               isLZ78ConversePassthrough_def
LempelZiv78.lean:290               isSMBSandwichPassthrough_def
LZ78GreedyParsing.lean:428         lz78GreedyEncodingLength_isZivInequalityPassthrough
LZ78GreedyParsing.lean:434         lz78GreedyEncodingLength_isLZ78ConversePassthrough
MultipleAccessChannel.lean:397     mac_single_rate_bound₁      (Fano + chain rule hidden in True)
MultipleAccessChannel.lean:417     mac_single_rate_bound₂
MultipleAccessChannel.lean:438     mac_sum_rate_bound
MultipleAccessChannel.lean:609     mac_capacity_region_outer_bound_three_bounds
```

### name_laundering (5) — name claims a discharge the statement does not deliver
```
AWGNMIDecompBody.lean:194          awgn_theorem_of_typicality_converse_midecomp_discharged
                                    (swaps IsAwgnMIDecomp for a DEFINITIONALLY-IDENTICAL predicate → zero net discharge)
AWGNMIDecompBody.lean:221          awgn_capacity_closed_form_of_maxent_midecomp_discharged
LZ78ConverseDischarge.lean:431     lz78_converse_lower_bound_greedy_full
                                    (_full over open h_chain/h_smb_lower + a True conjunct)
LZ78SMBSandwich.lean:559           lz78_asymptotic_optimality_two_sided_smb_discharged
                                    (byte-identical pass-through of parent; nothing discharged)
RelayDFBlockMarkovBody.lean:389    relay_df_inner_bound_block_markov_discharged
                                    (name says inner-bound discharged; conclusion is rate-only RelayDFRateWitness a degenerate error-1 code satisfies)
```

### load_bearing_hyp left as defect (12) — hypothesis IS (essentially) the conclusion, not an honest 🟢ʰ residual
```
AWGNConverse.lean:80               AWGN.awgn_converse           (IsAwgnConverseHypothesis ≡ full conclusion)
BrunnMinkowski.lean:183            brunn_minkowski_entropy_inequality   (body = h_bm; hyp ≡ conclusion)
BrunnMinkowski1DSuperlevelBody.lean:301  prekopa_leindler_1D_body_discharged
BrunnMinkowskiClosure.lean:482     brunn_minkowski_entropy_jointPi
BrunnMinkowskiFunctional.lean:209  prekopa_leindler_inequality_ge
BrunnMinkowskiFunctional.lean:319  entropy_le_logVolume_of_logConcave
ChernoffConverse.lean:400          chernoff_converse_discharged
ChernoffPerTiltDischarge.lean:255  chernoff_lemma_tendsto_discharged
ChernoffPerTiltDischarge.lean:279  chernoff_dotEq_tendsto_discharged
LZ78ZivTreeNode.lean:634           isLZ78AchievabilityZivUpperBound_distinctOverhead  (hcore is a provably-FALSE predicate)
ParallelGaussian.lean:284          parallel_gaussian_capacity_formula_of_perCoordReduction  (body = h_per_coord; hyp ≡ conclusion equality)
ParallelGaussian.lean:388          parallel_gaussian_capacity_active_form_of_perCoordReduction
```
(These are borderline with the 359 honest suspects; reviewers judged the hypothesis here to BE the conclusion, not merely carry a future obligation.)

## Suspects (361) — honest 🟢ʰ remaining tasks, not honesty failures

359 `load_bearing_hyp` + 2 `degenerate_def`. These take a genuine, openly-documented hypothesis (≠ `True`, ≠ conclusion) that carries the proof's hard part — a precondition for completion under standard B, **not** deception. Concentrated in the intentionally-staged areas: EPI/Stam (Csiszár coupling wall), Cramér/Chernoff (Sanov LDP per-tilt lower bound), AWGN (F-2/F-3 typicality/converse), Parallel-Gaussian (water-filling MI bridge), MAC/Broadcast/Relay/Wyner-Ziv (random-coding achievability, gated implications), LZ78 (Ziv inequality + converse chain), Brunn-Minkowski (Prékopa-Leindler nD).

Full list: `deno run -A scripts/audit_db.ts list --status suspect`.

## Cross-cutting root causes (highest-leverage fixes)

1. **`Prop := True` passthrough predicates** drive most degenerate defects. `IsZivInequalityPassthrough`, `IsLZ78ConversePassthrough`, `IsSMBSandwichPassthrough`, `IsStamScoreConvolution`, `IsDeBruijnIntegrationHypothesis`, `IsStamInequalityHypothesis` are all `:= True`; every `.trivial`/`.of*` constructor and downstream `_discharged` user inherits the vacuity. Fix the definitions, not the call sites.
2. **Whittaker-Shannon / Shannon-Hartley tier** is built on `IsBandlimited* := 0 < W` / `∃ _, True` placeholders — a whole API (builders, closure lemmas, "bridges") over vacuous predicates (12 degenerate defects). Real task: strengthen the 4 definitions to carry Fourier/Poisson-summation content (absent from Mathlib).
3. **MAC inner-bound + averaging** chain is circular: `MACAchievableWithError`/`IsMACRandomCodebookMarkov` are definitional aliases of `MACInnerBoundExistence`, so `_of_markov`/`_of_averaging`/`_of_achievableWithError` repackage the hypothesis as the conclusion.
4. **AWGN `_midecomp_discharged`** swaps a predicate for a definitionally-identical one — looks like a discharge, is an identity.

## Process notes / caveats

- **`f_uses_sorry` flag is unreliable** (text-based, over-matches `sorry` in adjacent comments/lemmas due to the body over-approximation in `extract_statements.ts`). All 9 `sorry`-flagged defects were false positives, confirmed sorry-free via `#print axioms` and corrected to `ok`. Recommend scoping sorry detection to the declaration's own body span.
- **Relay `_discharged` family conflict**: two Opus reviewers disagreed (alias-laundering vs honest gated-implication). A third adjudicator read the actual `def`s: `IsRelay*Witness := Relay*Achievable := (InRate → error-carrying Existence)` is a genuine gated implication, NOT a conclusion alias → 6 of 8 are honest `suspect`; only `relay_df_inner_bound_block_markov_discharged` (rate-only conclusion) and `relay_cf_inner_bound_binning_discharged_witness` (identity wrap) are real defects.
- **QA**: 2 random samples of 10 `ok` rows, 0 flips → first-pass reliability good.
- DB is gitignored and regenerable (`build`); verdicts persist. Re-run `list --status defect|suspect` for live data.

## Update — post-cleanup status (2026-05-24)

cleanup waves (defect-cleanup-plan.md 波 0/1/2) + 後続 retract/rebrand を経た **scale 変化**: defect 101 → 3。残 3 件は intentional staged Mathlib 壁案件で、200-500 LoC 規模の analytic discharge plan に切り出し済 ([AWGN](../shannon/awgn-achievability-typicality-plan.md) / [BM](../shannon/brunn-minkowski-from-epi-discharge-plan.md))。

**現状の counts は本文書ではなく code タグ から取る** (本セクションが書かれた瞬間から陳腐化するため):

```bash
deno run -A scripts/audit_db.ts scan
# 出力例:
#   @audit:defect  (8)        ← circular pass-through (declaration 単位)
#        8  circular
#   @audit:defer  (8)
#        2  awgn-achievability-typicality
#        2  brunn-minkowski-from-epi-discharge
#        4  pg-legacy-retract
#   @audit:staged  (2)
#        1  epi-n-dim
#        1  n-dim-gaussian-aep
```

`@audit:defect` の declaration count と「実質的な defect 案件数」は別物 — 同一 plan に defer されている declaration はまとめて 1 案件で潰れる。dispatch は [`defect-cleanup-plan.md`](defect-cleanup-plan.md) §波後の残り residuals。
