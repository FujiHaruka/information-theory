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
parallel_gaussian_capacity_formula_minimal | water-filling

@ 10 | Rate–distortion
rate_distortion_achievability
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
mac_converse | MAC capacity-region outer bound (per-letter conditional MI sum form)
mac_achievability | MAC achievability (corner-point form)

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
