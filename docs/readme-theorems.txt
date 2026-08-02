# readme-theorems — source of truth for the "Formalized results" table in README.md.
#
# Each '@ <ch> | <topic>' line starts a chapter; the lines beneath it are that chapter's
# headline theorems, one per line, as 'NAME' or 'NAME | statement override'.
#
# File paths and links are NOT stored here. scripts/gen_readme_table.ts resolves each NAME
# to its current source file by scanning InformationTheory/ on every run, so a moved file
# self-heals and only a true rename/delete fails the check. To re-curate, edit this file
# and regenerate; never hand-edit the table inside the README markers.
#
# The Statement column is NOT stored here either: it is summarized from the declaration's
# docstring (the code-side source of truth), stopping before audit narration such as
# '@audit:' / 'sorryAx-free' / 'See also' / 'Proof:'. Add a '| <statement>' override only
# when that summary reads badly out of context — a hand-written statement drifts silently
# the same way a hand-written table does, so keep overrides rare and note why below.
#
#   Regenerate README : deno run -A scripts/gen_readme_table.ts --write
#   Verify (CI/manual): deno run -A scripts/gen_readme_table.ts --check
#
# '#' starts a comment; blank lines are ignored.

@ 2 | Entropy, mutual information, DPI
entropy
mutualInfo
mutualInfo_chain_rule
mutualInfo_le_of_postprocess
fano_inequality_measure_theoretic

@ 3 | Asymptotic equipartition (AEP)
aep_ae
typicalSet
stronglyTypicalSet

@ 4 | Entropy rate & the SMB theorem
entropyRate
shannon_mcmillan_breiman
birkhoff_ergodic_ae

@ 5 | Data compression
shannonCode_expected_length_bounds
kraftSum_le_one_of_uniquelyDecodable
huffmanLength_optimal

@ 6 | Gambling & the doubling rate
doublingRate_le_proportional
doublingRate_eq_proportional_iff
sideInfo_doublingRate_increment_eq_mutualInfo
condDoublingRate_le_proportional
seqLogWealth_div_tendsto_doublingRate
seqLogWealth_proportional_div_tendsto
seqLogWealth_proportional_asymptotically_optimal
seqLogWealth_tendsto_atTop_of_pos_doublingRate
seqLogWealth_tendsto_atBot_of_neg_doublingRate

@ 7 | Channel capacity
shannon_noisy_channel_coding_theorem_general
channel_coding_feedback_converse
shannon_converse_single_shot
channelCoding_strong_converse_asymptotic

@ 8 | Differential entropy
differentialEntropy_gaussianReal
# override: the docstring's second sentence is the proof recipe, not the statement.
jointDifferentialEntropyPi_le_sum | `n`-variable differential-entropy subadditivity `h(Yⁿ) ≤ ∑ᵢ h(Yᵢ)` (the parallel-Gaussian consumer form).

@ 9 | Gaussian channel
awgn_capacity_closed_form_genuine
contAwgn_eq_shannonHartley
parallel_gaussian_capacity_formula_minimal
# override: the docstring describes the wrapper's reduction rather than the statement.
whittaker_shannon_bandlimited | **Whittaker–Shannon sampling theorem**: a band-limited signal is recovered from its integer samples — for continuous integrable `f` whose Fourier transform vanishes outside `[-1/2, 1/2]`, the cardinal series `∑ n : ℤ, f n · sinc (t - n)` sums to `f t` at every real `t`.
whittaker_shannon_hasSum

@ 10 | Rate–distortion
rate_distortion_achievability
rate_distortion_achievability_operational
rate_distortion_achievability_operational_general
rateDistortionFunction_convexOn
rate_distortion_converse_n_letter_singleLetter

@ 11 | Hypothesis testing & large deviations
stein_converse_finite_n
sanov_ldp_upper_bound
# override: the docstring positions this against its sibling form instead of stating it.
cramer_lower_boundary | **Cramér's theorem** (large-deviation lower bound, boundary case): for a bounded i.i.d. sequence and a tilt `λ` whose cgf derivative is `a`, `−(λ·a − cgf λ) ≤ liminf (1/n) log P(∑ᵢ Yᵢ ≥ a·n)`.
chernoff_converse
tvNorm_le_sqrt_klDiv

@ 12 | Maximum entropy
entropy_le_log_card
expFamily_maximizes_entropy_of_KKT

@ 13 | Universal coding (LZ78)
lz78_asymptotic_optimality_with_greedy
arithmeticCode_expected_length_bounds

@ 14 | Kolmogorov complexity
kolmogorov_entropy_rate
condComplexity_not_computable
incompressible_seq_freq_tendsto_half
universalProb_ge_two_pow_neg_prefixComplexity
prefixComplexity_le_two_mul_neg_logb_universalProb
chaitinOmega_le_one
prefixComplexity_not_computable
prefixUniversalEval_dom_not_computablePred
chaitinOmega_not_computable
prefixComplexity_le_twoPartLength
mdlComplexity_sub_prefixComplexity_le

@ 15 | Distributed source coding
slepian_wolf_full_rate_region_achievability
wyner_ziv_achievability
wyner_ziv_converse
mac_converse
mac_achievability
mac_capacity_region_reconciliation
mac_timesharing_capacity_region
bc_degraded_converse_from_code
bc_achievability
marton_achievability
martonRegionUnion_subset_capacity
closure_convexHull_martonRegionUnion_eq_bounded
bc_capacity_subset_coop
bc_capacity_subset_uv
bc_lessNoisy_capacity_eq_uv
bc_moreCapable_capacity_eq_uv
bc_degraded_capacity_eq_uv
relay_cutset_outer_bound

@ 16 | Log-optimal portfolio
growthRate_concaveOn
logOptimal_of_kuhnTucker
kuhnTucker_of_logOptimal
competitive_optimality
seqLogWealth_div_tendsto_growthRate
sideInfo_growthRate_increment_le_mutualInfo
seqLogWealth_div_tendsto_stationary
growingMemory_logWealth_tendsto_condOptGrowthInfty_concrete
universal_portfolio_regret_tendsto_zero

@ 17 | Entropy inequalities
han_inequality
shearer_inequality
loomis_whitney
# override: the docstring states the bound as display math, which a table cell cannot hold.
brascamp_lieb_finset | **Brascamp–Lieb inequality** (combinatorial form): if `S : ι → Finset (Fin n)` covers each coordinate at least `k` times, then `|A|^k ≤ ∏ i, |π_{S i}(A)|` for every nonempty `A : Finset (Fin n → α)`. Loomis–Whitney is the special case `S i := univ.filter (· ≠ i)` with `k = n - 1`.
entropy_power_inequality_of_density
minkowskiDeterminantInequality
stam_inequality_smoothed_density
debruijn_identity_per_time
debruijn_identity_integrated
