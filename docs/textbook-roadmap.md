# Verified Information Theory Textbook ロードマップ 📚

> Cover & Thomas *Elements of Information Theory* を骨格に Lean 4 + Mathlib で **標準 B (proof done = 0 sorry ∧ 0 @residual)** を狙う上位 index。
> 章状態 + 残壁 + 戦略遷移のみ。各 seed の statement / 規模 / publish 履歴は `docs/<family>/<topic>-moonshot-plan.md` が SoT、検証 doctrine は CLAUDE.md「検証の誠実性」+ `docs/audit/audit-tags.md`、wave 別実装履歴は `git log` が SoT。

## ゴール

Cover & Thomas (2nd ed.) **Ch.2–12, 15, 17** を Lean 形式化された定理から生成される教科書として publish。成果物 3 層 = (1) Verified library (`InformationTheory/`) + (2) Typed RV API (`H(X)` / `I(X;Y)` 等の書き味) + (3) markdown / LaTeX 原稿。

## scope-out

**章単位で元から外す**: Ch.6 stock-market 部 / Ch.14 Kolmogorov Complexity / Ch.16 Portfolio Theory / Ch.13 LZ 詳細 (LZ78 漸近最適性は in)。

**当初 scope-out だが後に genuine closure して復帰済** (もはや scope-out ではない):

- **Ch.6 Gambling** — Kelly 倍加率最適性 (`doublingRate_le_proportional` CT 6.1.2 + 等号 `_eq_proportional_iff`)、副情報増分 `sideInfo_doublingRate_increment_eq_mutualInfo` (CT 6.1.3)、operational sequences (`seqLogWealth_div_tendsto_doublingRate` + Kelly 最適性 + 指数成長/破産 `seqLogWealth_tendsto_atTop/atBot_...`) すべて `@audit:ok`・sorryAx-free。stock-market 部のみ scope-out 継続。
- **Ch.9 AWGN operational 符号化定理** — achievability `awgn_achievability` + converse `awgn_converse` 両側 sorryAx-free。converse 3 壁 (mi-bridge / multivariate-mi / continuous-mi-chain-rule) は false-wall overturn、achievability は continuous AEP / sphere packing / Gaussian random codebook を `isAwgnTypicalityHypothesis` (regularity precondition のみ) で discharge。facts → `shannon/awgn-facts.md`。
- **Ch.11 Chernoff converse / Cramér 下界** — `chernoff_converse` sorryAx-free (achievability `chernoff_lemma_achievability` の片割れ)、`cramer_lower_boundary_unconditional` sorryAx-free。
- **Ch.13 LZ78** — headline `lz78_asymptotic_optimality_with_greedy` proof done (M3 achievability + M4 converse 両壁 closed)。
- **Ch.15 Network IT** — MAC 容量領域 full closure (`mac_converse` + `mac_achievability` + reconciliation `mac_capacity_region_reconciliation`)、degraded BC (`bc_converse` + `bc_achievability`)、relay cut-set outer bound (`relay_cutset_outer_bound`)、**Wyner-Ziv operational main (`wyner_ziv_achievability` + `wyner_ziv_converse`)** すべて `@audit:ok`・sorryAx-free。MAC time-sharing 全凸包形 (L-MAC5) も `mac_timesharing_capacity_region` (`@[entry_point]`、intersection 形) で proof done・sorryAx-free (2026-07-05 CLOSED、子 `mac-timesharing-plan.md` が SoT)。
- **Ch.17 EPI 一般版** — 完全無条件 `entropyPowerExt_add_ge_unconditional` + a.c. 版 `entropy_power_inequality_of_ac` sorryAx-free。CT 17.9 Minkowski determinant `minkowskiDeterminantInequality` も Gaussian additivity から導出済。

**残る真の scope-out (章内)**:

- **Ch.9 Shannon-Hartley Nyquist 2W-DOF**: (c) 数学的深さの真の壁 (C&T 自身が厳密証明せず)。`IsTwoWDegreesOfFreedom` は load-bearing predicate で honest 開示済 (`@residual(plan:whittaker-shannon-partial-moonshot-plan) @audit:retract-candidate`)。

**当初 scope-out だが genuine closure して復帰済 (Ch.10)**:

- **Ch.10 operational achievability 無条件形** — `rate_distortion_achievability_operational` (`@[entry_point]`, sorryAx-free, `@audit:ok`)。既存 conditional `rate_distortion_achievability` の pass-through 仮説 (`hqStar_pos` / `h_jts_subset_dts` / slack 群) を全て内部で discharge。full-support source (`∀ a, 0 < P_X a`) は marginal 保存摂動の strict-positive 着地に要る regularity precondition (load-bearing でない、独立監査 PASS)。完全一般 source 版 (full-support を落とす) も `rate_distortion_achievability_operational_general` (`@[entry_point]`, sorryAx-free, `@audit:ok`, 台 subtype 制限 + code lift) で **CLOSED (2026-07-13)** → `rate-distortion-achievability-general-source-plan.md`。詳細 → `rate-distortion-achievability-unconditional-plan.md`。

## 完成判定 (DoD 2 段階 = 標準 B)

- **type-check done** (commit OK): `lake env lean <file>` 0 errors、`sorry` warning は `@residual(<class>:<slug>)` 付き
- **proof done = 標準 B** (完成): 上記 + 0 `sorry` + 0 `@residual`

**仮説の区別**: regularity-hyp (full-support / `IsFiniteMeasure` / `Var > 0` / measurability) は precondition で proof done と両立。**load-bearing-hyp (証明の核心を抱える `*Hypothesis` predicate) は禁止** — 該当箇所は `sorry` + `@residual` で表現 (CLAUDE.md「検証の誠実性」、[[sorry-based-migration]])。

## 章対応進捗

状態凡例: ✅ = 主定理 proof done / 🟢 = scope 内全完成 / 🟡 = 部分達成 / ✖ = scope-out。**実 `sorry` タクティク = 0** (最終再確認 2026-06-20 full build success + sorry warning ゼロ; 都度 `rg "^\s*sorry\s*$|:= by sorry$|by sorry$|:= sorry$" InformationTheory/ | wc -l` で再導出)。

| Ch. | 章 | 状態 | 代表 (proof done) |
|---|---|---|---|
| 2 | Entropy / MI / DPI | ✅ | `entropy`, `mutualInfo`, `mutualInfo_chain_rule`, `condMutualInfo`, `mutualInfo_le_of_postprocess` (DPI), `condEntropy_pi_chain_rule`, `fano_inequality_measure_theoretic` |
| 3 | AEP | ✅ | `aep_ae`, `aep_inProbability`, `typicalSet`, `stronglyTypicalSet` |
| 4 | Entropy Rate / SMB | ✅ | `entropyRate`, `shannon_mcmillan_breiman`, `birkhoff_ergodic_ae`, `BackwardMartingale` |
| 5 | Data Compression | ✅ | `shannonCode_expected_length_bounds`, `kraftSum_le_one_of_uniquelyDecodable` (McMillan), `arithmeticCode_*` (length/prefix_free/unique_decodable), `huffmanLength_optimal` (CT 5.8.1 無条件, cost-level pivot) |
| 6 | Gambling | 🟡 | `doublingRate_le_proportional`, `_eq_proportional_iff`, `sideInfo_doublingRate_increment_eq_mutualInfo`, `condDoublingRate_le_proportional`, `seqLogWealth_div_tendsto_doublingRate`, `seqLogWealth_proportional_asymptotically_optimal`, `seqLogWealth_tendsto_atTop/atBot_...` (stock-market は scope-out) |
| 7 | Channel Capacity | ✅ | `shannon_noisy_channel_coding_theorem_general_full`, `channel_coding_feedback_converse`, `shannon_converse_single_shot` (Verdú-Han), `channelCoding_strong_converse_asymptotic` (Wolfowitz 強逆) |
| 8 | Differential Entropy | ✅ | `differentialEntropy_gaussianReal`, `_le_gaussian_of_variance_le`, `KLDivContinuous`, `jointDifferentialEntropyPi_le_sum` (n-var subadditivity) |
| 9 | Gaussian Channel | 🟢 (①②③) | ① `awgn_capacity_closed_form_genuine` = (1/2)log(1+P/N)。② parallel Gaussian water-filling proof done (`parallel_gaussian_capacity_formula_minimal` sorryAx-free, achiever+converse+per-coord+L-WF1+`KKT.isWaterFillingOptimal_of_kkt`)。③ operational `awgn_achievability` + `awgn_converse`。Nyquist 2W-DOF のみ scope-out |
| 10 | Rate Distortion | ✅ | `rate_distortion_achievability`, `rate_distortion_achievability_operational` (無条件 operational, full-support), `rate_distortion_achievability_operational_general` (任意 source, full-support 除去), `rate_distortion_converse_single_shot/_specified`, `rateDistortionFunction_convexOn` (measure 形), `rate_distortion_converse_n_letter_singleLetter` |
| 11 | Statistics | 🟢 | `stein_*`, `sanov_ldp_*`, `tvNorm_le_sqrt_klDiv` (+`_div_two` sharp Pinsker), `conditionalStronglyTypicalSlice_mass_ge`, `chernoff_lemma_achievability` + `chernoff_converse`, `hoeffding_tradeoff_exp`, `cramer_lower_boundary_unconditional`。Hoeffding interior は scope-out (dead/一部 false-as-stated) |
| 12 | Maximum Entropy | ✅ | `entropy_le_log_card`, `entropy_eq_log_card_iff`, `entropy_le_gibbs_of_constraints`, `expFamily_maximizes_entropy_of_KKT` |
| 13 | Universal Coding | ✅ | Arithmetic ✅, `lz78TokenCode_entropyD_le_expectedLength` (M1 converse), `lz78_asymptotic_optimality_with_greedy` (M3+M4 closed, sorryAx-free) |
| 14 | Kolmogorov | ✖ | — |
| 15 | Network IT (DSC mini-chapter) | 🟢 | Slepian-Wolf 完全 (corner + full rate region `slepian_wolf_full_rate_region_achievability` + 4 converse), Wyner-Ziv convexity body + operational main (`wyner_ziv_achievability` + `wyner_ziv_converse`), MAC 容量領域 full (`mac_converse` + `mac_achievability` + `mac_capacity_region_reconciliation`), degraded BC (`bc_converse` + `bc_achievability`), relay `relay_cutset_outer_bound` |
| 16 | Portfolio | ✖ | — |
| 17 | Inequalities | 🟢 | `han_inequality`, `shearer_inequality`, `loomis_whitney`, `brascamp_lieb_finset`, `jointEntropySubset_submodular` (polymatroid), `tvNorm_le_sqrt_klDiv`, `edgeBoundary_entropy_sharp`, 一般 EPI `entropyPowerExt_add_ge_unconditional` + a.c. 版, `entropyPower_gaussian_additivity`, `minkowskiDeterminantInequality` (CT 17.9), Stam `stam_inequality_smoothed_density` + de Bruijn `debruijn_identity_*`。詳細 SoT → `docs/shannon/ch17-inequalities-status.md` |

## 「Mathlib 壁」5 分類 (scope 内 frontier に残る型)

- **(a) 量の壁** (低、未構築): well-understood だが Mathlib に補題不在で一から数百行。現存例なし (Slepian-Wolf error bound / AWGN continuous AEP 等はいずれも closure 済)。
- **(b) 解析の壁** (中〜高): 計算体系自体を建てる型。EPI Stam / de Bruijn は closure 済。現存 frontier 例 0。
- **(c) 数学的深さ** (高、真の壁): Nyquist 2W-DOF (Ch.9、scope-out 確定)。
- **(d) 実は選択** (de-circularize 済): "ROI 無し" を「壁」と呼んでいたもの、現在は honest 開示のみ。
- **(e) scaffolding-was-false** (中〜大): 既存縮約 predicate / 定義が偽 / 循環 / 不健全で discharge 不能。過去例は全 closure or 削除済。

**doctrine**: 「壁を額面で受けない」— Ch.8/9/10/17 で「壁→self-buildable / 壁→既存資産で配線」を多数覆した。scope-out menu / wall verdict は着手前に gateway-atom + 退化境界 verify + transposed grep で独立再判定 (CLAUDE.md「Mathlib wall」節が SoT)。

## frontier (scope 内で残る作業)

**proof 層はほぼ全 closure 済**。scope 内で残るのは:

- **教科書原稿 (層 3)**: genuine ✅ 章を prose 化する作業が主フロンティア (下記「次の一手」)。
- **真の壁 (scope-out 確定・honest 開示)**: Ch.9 Nyquist 2W-DOF (`IsTwoWDegreesOfFreedom` load-bearing、`@residual(plan:whittaker-shannon-partial-moonshot-plan)`)。
- ~~壁ではない frontier (regularity 緩和): Ch.10 完全一般 source 版~~ **CLOSED (2026-07-13)**: `rate_distortion_achievability_operational_general` (`@[entry_point]`, sorryAx-free, `@audit:ok`)。full-support 前提 (`hP_supp`) を台 subtype 制限 + code lift で除去、新 load-bearing hyp なし。詳細 → `rate-distortion-achievability-general-source-plan.md`。

legacy migration は完了済 (active な `@audit:suspect/staged/defer` タグ 0 件、`@audit:closed-by-successor` project-wide 0 件、circular `:= h` defect 0 件)。

## 教科書原稿 (層 3) / 次の一手

- **Ch.2 パイロット済** (`docs/textbook/ch02-entropy.md`): 検証済 33 declaration を §2.1-2.10 の prose に紐付け。判明した課題 = (i) 値の型不一致 (`ℝ≥0∞` vs `ℝ`、橋渡し `.toReal`)、(ii) Markov 定義の表層差 (compProd 分解形)、(iii) n 変数 chain rule の右辺長大、(iv) 章↔file が 1:1 でない。代表名照合済 (2026-06-22、章対応表の backtick 識別子を実 declaration と機械照合)。
- **原稿起動可能な genuine ✅ 章**: Ch.2 (✅ pilot) / 3 / 4 / 5 / 7 / 8 / 9 / 10 / 12 / 15 (DSC) / 17。
- **次の一手候補**: (i) Ch.2 パイロット課題を踏まえた原稿生成テンプレ確立 (型注釈 / 代表名照合) → 他完成章 (Ch.3/4/7/12) 横展開。

## 判断ログ (戦略遷移サマリ)

完了マイルストーンのみ (何が完了したか)。過程・wave 別履歴は `git log`、doctrine 教訓は CLAUDE.md が SoT。settled-facts 台帳 = 各 family の `*-facts.md`。

- **2026-05-18〜20**: 並列実装 11 wave で 18 seed の主定理 + sub-predicate discharge を publish (累計 ~50k 行)。
- **2026-05-21**: 標準 B doctrine 確定 + Mathlib 壁 4 分類。MAC/BC/Relay の circular DEFECT 7 本を発見し全 honest-terminal 化 (後に scope-out で decl ごと物理削除 `f67ec8a`)。
- **2026-05-25**: DoD 2 段階 + load-bearing hyp 禁止を CLAUDE.md に確定 (撤退口は `sorry` + `@residual` のみ)。
- **2026-05-26**: scope 縮小決定 (原稿パイロット優先)。Ch.6/14/16 章外、Ch.15 = DSC mini-chapter、Ch.11 Chernoff converse / Ch.17 一般 EPI / Ch.9 Nyquist を future work 隔離、Ch.9 ③ AWGN operational を scope-out (後に多くが復帰)。
- **2026-05-29〜30**: Ch.9 ① 単一文字容量 genuine + ② achiever genuine + Ch.8 n-var subadditivity genuine (「壁→self-buildable」前科の起点)。Ch.5 Huffman 強形最適性 `huffmanLength_optimal` を cost-level pivot で genuine closure (per-symbol depth identity は FALSE と機械検証で確定、tie-invariant cost 漸化式へ pivot)。Ch.2 教科書パイロット起動。
- **2026-06-08**: 一般 EPI 無条件化 `entropyPowerExt_add_ge_unconditional` を 3-case dispatch + route T (truncation+Gibbs+DCT、「無限分散 a.c. 壁」を FALSE WALL 判定) で sorryAx-free 化。legacy Stam-bridge route は物理削除。facts → `epi-facts.md`。
- **2026-06-10〜11**: scope-out 低リスク 4 家系を独立再判定。Ch.7 converse / Ch.10 RD ach / Ch.11 Hoeffding interior は dead or false-as-stated と確定 → retract-tag + 物理削除。Ch.10 RD 凸性 `rateDistortionFunction_convexOn` + converse `rate_distortion_converse_n_letter_singleLetter` を genuine closure (converse は under-hyp 修正 + MI superadditivity 壁を self-build)。Cramér: false-statement 2 root を def-fix (`h_deriv` 追加) → CLT-boundary closure moonshot `cramer_lower_boundary_unconditional` (gateway `gaussianReal_Ici_eq_half` で「genuine 壁公算」予測を反証) → root 配線で sorryAx-free 化。facts → `cramer-facts.md`。
- **2026-06-12**: Ch.9 AWGN operational ③ 両側 genuine — converse `awgn_converse` (3 壁 false-wall overturn) + achievability `awgn_achievability` (`AWGN/Walls.lean` 3 shared sorry 全閉鎖、`c44be725`) ともに sorryAx-free。
- **2026-06-13**: Ch.9 ② water-filling 最適性 `KKT.isWaterFillingOptimal_of_kkt` genuine (`Real.log_le_sub_one_of_pos` の直接適用で tangent 上界、ConcaveOn 移設不要) → ② proof done。honesty 訂正: 「L-WF2 完了」の旧記録は虚偽で、load-bearing `h_opt` 仮説を看過していた (sorryAx-free ≠ unconditional)。
- **2026-06-27**: Ch.7 Wolfowitz strong converse asymptotic `channelCoding_strong_converse_asymptotic` genuine (Phase A 鞍点 `klDiv_channel_le_capacity` core、gateway one-sided 右微分 envelope cancellation)。Ch.17 Fisher 情報路 standalone genuine (`stam_inequality_smoothed_density` + `debruijn_identity_*`)。
- **2026-06-28**: Ch.15 MAC 容量領域 full closure (`mac_converse` + `mac_achievability` + reconciliation)、degraded BC converse `bc_converse` (Route B entropy-difference)、relay cut-set outer bound `relay_cutset_outer_bound` (BC-cut telescoping を gateway-atom-first で tractable 化)。AWGN ① load-bearing wrapper 群を Tier-3 `@audit:superseded-by` 一掃 (genuine `awgn_capacity_closed_form_genuine` 併存ゆえ)。`@audit:closed-by-successor` project-wide 0 化。
- **2026-07-03**: Ch.15 degraded BC achievability `bc_achievability` genuine (superposition inner bound、最終ゲート `bc_degraded_infoJoint_ge` = degradedness superadditivity を stochastic Markov 自作 + DPI で closure)。
- **2026-07-04**: Ch.6 Gambling genuine closure (Kelly 倍加率最適性 + 副情報増分 + operational sequences 系)、Ch.6 全体 scope-out 解除 (stock-market 部のみ残)。
- **2026-07 (直近)**: Ch.15 Wyner-Ziv operational main FULLY CLOSED (`wyner_ziv_achievability` + `wyner_ziv_converse` sorryAx-free、Markov-core + covering atom を joint-derandomize で closure、独立監査 PASS)。WZ main の scope-out は解除。
- **2026-07-13**: Ch.10 operational achievability 無条件形 `rate_distortion_achievability_operational` genuine sorryAx-free (`@[entry_point]`, 独立監査 `@audit:ok`)。既存 conditional 版の pass-through 仮説 (`hqStar_pos` / `h_jts_subset_dts` / slack 群) を 3 piece で内部 discharge — B: marginal 保存 full-support 摂動 (`rdPerturb`), C: jts⊆dts 包含 (`jts_subset_dts_of_dist_slack`, gateway-atom-first で機構検証), A: 15-conjunct slack existential (`rdSlack_exists`)。全 piece が (a) 量の壁クラスで Mathlib gap なし、壁誤認ゼロ。full-support は regularity precondition (over-hyp、load-bearing でない)。詳細 → `rate-distortion-achievability-unconditional-plan.md`。**同日 follow-on**: full-support 前提そのものを落とした完全一般 source 版 `rate_distortion_achievability_operational_general` (`@[entry_point]`, sorryAx-free, 独立監査 `@audit:ok`) も CLOSED。台 subtype `{a // 0 < P_X a}` に制限して full-support 版を適用、retraction で code を全 alphabet に lift (期待歪みは非台座標が a.e.-null なので `Measure.pi_map_pi` + `integral_map` で一致)。新 load-bearing hyp ゼロ、`hP_supp` を除いただけ。→ `rate-distortion-achievability-general-source-plan.md`。
