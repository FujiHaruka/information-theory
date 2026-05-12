/-
# Audit 2026-05 — `#print axioms` 一括チェック

`docs/audit-2026-05.md` §3 用。Phase B カタログの主定理を全件 `#print axioms` に通し、
`sorryAx` / カスタム公理が混入していないかを確認する。

期待値: `[propext, Classical.choice, Quot.sound]` (Lean 4 標準 3 公理) のみ。
-/

import Common2026

-- §2.1 Fano 系 (7 件)
#print axioms InformationTheory.FiniteJointPMF.fano_core
#print axioms InformationTheory.FiniteJointPMF.fano_inequality
#print axioms InformationTheory.FiniteJointPMF.error_lower_bound
#print axioms InformationTheory.FiniteJointPMF.condEntropy_le_pushforward_condEntropy
#print axioms InformationTheory.FiniteJointPMF.fano_inequality_decode
#print axioms InformationTheory.FiniteJointPMF.fano_inequality_decode'
#print axioms InformationTheory.MeasureFano.fano_inequality_measure_theoretic

-- §2.2 Shannon 基本 + 単発不等式 (12 件)
#print axioms InformationTheory.Shannon.mutualInfo_nonneg
#print axioms InformationTheory.Shannon.mutualInfo_comm
#print axioms InformationTheory.Shannon.mutualInfo_eq_zero_iff_indep
#print axioms InformationTheory.Shannon.mutualInfo_ne_top
#print axioms InformationTheory.Shannon.klDiv_map_le
#print axioms InformationTheory.Shannon.mutualInfo_le_of_postprocess
#print axioms InformationTheory.Shannon.mutualInfo_eq_entropy_sub_condEntropy
#print axioms InformationTheory.Shannon.MaxEntropy.klDiv_uniformOn_univ_toReal_eq
#print axioms InformationTheory.Shannon.MaxEntropy.entropy_le_log_card
#print axioms InformationTheory.Shannon.MaxEntropy.entropy_eq_log_card_iff
#print axioms InformationTheory.Shannon.Pinsker.tvNorm_le_sqrt_klDiv
#print axioms InformationTheory.Shannon.PinskerSharp.tvNorm_le_sqrt_klDiv_div_two

-- §2.3 Han / 組合せ (14 件)
#print axioms InformationTheory.Shannon.jointEntropy_chain_rule
#print axioms InformationTheory.Shannon.han_inequality
#print axioms InformationTheory.Shannon.jointEntropySubset_univ
#print axioms InformationTheory.Shannon.jointEntropySubset_chain_rule
#print axioms InformationTheory.Shannon.condEntropy_subset_anti
#print axioms InformationTheory.Shannon.han_inequality_subset
#print axioms InformationTheory.Shannon.subset_average_anti
#print axioms InformationTheory.Shannon.subset_average_chain
#print axioms InformationTheory.Shannon.shearer_inequality
#print axioms InformationTheory.Shannon.loomis_whitney
#print axioms InformationTheory.Shannon.brascamp_lieb_finset
#print axioms InformationTheory.Shannon.jointEntropySubset_empty
#print axioms InformationTheory.Shannon.jointEntropySubset_mono
#print axioms InformationTheory.Shannon.jointEntropySubset_submodular
#print axioms InformationTheory.Shannon.edgeBoundary_ge_AMGM
#print axioms InformationTheory.Shannon.edgeBoundary_entropy_sharp

-- §2.4 AEP / Sanov / Stein (6 件)
#print axioms InformationTheory.Shannon.typicalSet_prob_le
#print axioms InformationTheory.Shannon.typeClass_Qn_le
#print axioms InformationTheory.Shannon.sanov_ldp_upper_bound
#print axioms InformationTheory.Shannon.sanov_ldp_equality
#print axioms InformationTheory.Shannon.stein_lemma
#print axioms InformationTheory.Shannon.StrongStein.stein_strong_lemma

-- §2.5 符号化 + その他 (10 件)
#print axioms InformationTheory.Shannon.ShannonCode.shannonLength_kraft_le_one
#print axioms InformationTheory.Shannon.ShannonCode.entropyD_le_expectedLength_of_kraft
#print axioms InformationTheory.Shannon.ShannonCode.expectedLength_shannon_lt_entropyD_add_one
#print axioms InformationTheory.Shannon.ShannonCode.shannonCode_expected_length_bounds
#print axioms InformationTheory.Shannon.ShannonCodeKraftReverse.exists_prefix_code_of_kraft
#print axioms InformationTheory.Shannon.shannon_converse_single_shot
#print axioms InformationTheory.Shannon.slepian_wolf_converse_X
#print axioms InformationTheory.Shannon.slepian_wolf_converse_Y
#print axioms InformationTheory.Shannon.slepian_wolf_converse_sum
#print axioms InformationTheory.Shannon.slepian_wolf_converse_single_shot
#print axioms InformationTheory.Shannon.ChannelCoding.channel_coding_achievability
#print axioms InformationTheory.Shannon.mutualInfo_chain_rule_fin
#print axioms InformationTheory.Shannon.mutualInfo_iid_eq_nsmul
