# readme-theorems — source of truth for the "Formalized results" table in README.md.
#
# Each '@ <ch> | <topic>' line starts a chapter; the lines beneath it are that chapter's
# headline theorems, one per line, as 'NAME' or 'NAME | note' (note rendered in parens).
#
# File paths and links are NOT stored here. scripts/gen_readme_table.ts resolves each NAME
# to its current source file by scanning InformationTheory/ on every run, so a moved file
# self-heals and only a true rename/delete fails the check. To re-curate, edit this file
# and regenerate; never hand-edit the table inside the README markers.
#
#   Regenerate README : deno run -A scripts/gen_readme_table.ts --write
#   Verify (CI/manual): deno run -A scripts/gen_readme_table.ts --check
#
# '#' starts a comment; blank lines are ignored.

@ 2 | Entropy, mutual information, DPI
entropy
mutualInfo
mutualInfo_chain_rule
mutualInfo_le_of_postprocess | DPI
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
kraftSum_le_one_of_uniquelyDecodable | McMillan
huffmanLength_optimal

@ 6 | Gambling & the doubling rate
doublingRate_le_proportional | Kelly optimality
doublingRate_eq_proportional_iff
sideInfo_doublingRate_increment_eq_mutualInfo | side information ΔW = I(X;Y) (CT 6.1.3)
condDoublingRate_le_proportional | conditional Kelly optimality
seqLogWealth_div_tendsto_doublingRate | operational doubling rate (1/n)·log Sₙ → W(b,o,p) a.s. (CT 6.3)
seqLogWealth_proportional_div_tendsto | Kelly growth rate over sequences (CT 6.3)
seqLogWealth_proportional_asymptotically_optimal | Kelly asymptotic optimality over sequences (CT 6.3)
seqLogWealth_tendsto_atTop_of_pos_doublingRate | exponential wealth growth: W*>0 ⟹ log Sₙ→∞ a.s. (CT 6.3)
seqLogWealth_tendsto_atBot_of_neg_doublingRate | ruin: W*<0 ⟹ log Sₙ→−∞ a.s. (CT 6.3)

@ 7 | Channel capacity
shannon_noisy_channel_coding_theorem_general_full
channel_coding_feedback_converse
shannon_converse_single_shot
channelCoding_strong_converse_asymptotic | Wolfowitz strong converse (asymptotic)

@ 8 | Differential entropy
differentialEntropy_gaussianReal
jointDifferentialEntropyPi_le_sum

@ 9 | Gaussian channel
awgn_capacity_closed_form_genuine
contAwgn_eq_shannonHartley | continuous-time Shannon–Hartley operational capacity, W·log(1+P/(N₀·W))
parallel_gaussian_capacity_formula_minimal | water-filling
whittaker_shannon_bandlimited | Whittaker–Shannon sampling theorem (band-limited signal from its Nyquist-rate samples)
whittaker_shannon_hasSum | cardinal series, L² spectrum form

@ 10 | Rate–distortion
rate_distortion_achievability
rate_distortion_achievability_operational | operational achievability, unconditional form (R > R(D), full-support source)
rate_distortion_achievability_operational_general | operational achievability for an arbitrary source (full-support hypothesis removed)
rateDistortionFunction_convexOn
rate_distortion_converse_n_letter_singleLetter

@ 11 | Hypothesis testing & large deviations
stein_converse_finite_n
sanov_ldp_upper_bound
cramer_lower_boundary_unconditional | Cramér large-deviation lower bound
chernoff_converse | Chernoff information error exponent (Bayesian, converse)
tvNorm_le_sqrt_klDiv | Pinsker

@ 12 | Maximum entropy
entropy_le_log_card @ MaxEntropy/Basic
expFamily_maximizes_entropy_of_KKT

@ 13 | Universal coding (LZ78)
lz78_asymptotic_optimality_with_greedy
arithmeticCode_expected_length_bounds

@ 15 | Distributed source coding
slepian_wolf_full_rate_region_achievability
wyner_ziv_achievability | Wyner–Ziv lossy source coding with decoder side information, achievability (Cover–Thomas Thm 15.9.1)
wyner_ziv_converse | Wyner–Ziv single-letter rate characterization, converse (Cover–Thomas Thm 15.9.1)
mac_converse | MAC capacity-region outer bound (per-letter conditional MI sum form)
mac_achievability | MAC achievability (corner-point form)
mac_capacity_region_reconciliation | MAC reconciliation: achievability corner informations = converse conditional/joint MI on the same single-letter law
mac_timesharing_capacity_region | MAC time-sharing capacity region = closed convex hull of per-input pentagons (Cover–Thomas Thm 15.3.1, convex-hull form)
bc_converse | degraded broadcast-channel converse, single-letter auxiliary-variable capacity-region outer bound (Cover–Thomas Thm 15.6.2)
bc_achievability | degraded broadcast-channel achievability, superposition-coding inner bound (Cover–Thomas Thm 15.6.2)
relay_cutset_outer_bound | relay-channel cut-set outer bound, min of broadcast-cut and MAC-cut per-letter sums (Cover–Thomas Thm 15.10.1)

@ 16 | Log-optimal portfolio
growthRate_concaveOn | growth rate is concave in the portfolio (Cover–Thomas Thm 16.2.2)
logOptimal_of_kuhnTucker | Kuhn–Tucker condition ⟹ log-optimal portfolio (Cover–Thomas Thm 16.2.1, reverse)
kuhnTucker_of_logOptimal | log-optimal portfolio ⟹ Kuhn–Tucker condition (Cover–Thomas Thm 16.2.1, forward)
competitive_optimality | competitive optimality of the log-optimal portfolio, E[S_b/S_b*] ≤ 1 (Cover–Thomas Thm 16.6.1)
seqLogWealth_div_tendsto_growthRate | operational asymptotic optimality over i.i.d. markets, (1/n)·log Sₙ → W(b) a.s. (Cover–Thomas Thm 16.3)
sideInfo_growthRate_increment_le_mutualInfo | side information increases the growth rate by at most I(X;Y) (Cover–Thomas Thm 16.4.1)
seqLogWealth_div_tendsto_stationary | growth rate over a stationary ergodic market, fixed-portfolio form (Cover–Thomas Thm 16.5)
growingMemory_logWealth_tendsto_condOptGrowthInfty_concrete | growing-memory log-optimal wealth AEP over a stationary ergodic market, (1/n)·log S*ₙ → W_∞ a.s. (Cover–Thomas Thm 16.5.1)
universal_portfolio_regret_tendsto_zero | Cover's universal portfolio: per-period regret vanishes without knowing the market law (Cover–Thomas Thm 16.7.1)

@ 17 | Entropy inequalities
han_inequality
shearer_inequality
loomis_whitney
brascamp_lieb_finset
entropy_power_inequality_of_density
minkowskiDeterminantInequality | Minkowski determinant
stam_inequality_smoothed_density | Stam inequality (Gaussian-smoothed densities)
debruijn_identity_per_time | de Bruijn identity (per-time)
debruijn_identity_integrated | de Bruijn identity (integrated)
