# Moonshot シードカード集

> **Status (2026-05-15, late)**: orchestrator session で **D-1'' parent surgery Step 2 (E2 exp decay closed-form)** を追加完了 (`AEPRate.lean` 293 → 364 行、+71 行、0 sorry / 0 warning)。2 補題追加: (a) **`exp_neg_mul_lt_of_rate`** — `0 < g → 0 < ε' → ∃ N, ∀ n ≥ N, exp(-n·g) < ε'` を `N := ⌈max 0 (-log ε' / g)⌉ + 1` の closed-form で publish、`Real.lt_log_iff_exp_lt` 一発 + `max 0` で ε' ≥ 1 edge case 吸収。(b) **`channelCoding_E2_lt_of_rate`** — `0 < I-R-3ε → 0 < ε' → ∃ N, ∀ n ≥ N, (⌈exp(nR)⌉-1)·exp(n(-I+3ε)) < ε'` を CCA 内 `h_upper` 補題 (`ChannelCodingAchievability.lean:1797-1810`) を verbatim 再現して squeeze + 補題 (a) で lift。**D-1'' Step 1 (`typicalSet_prob_ge_of_rate`) + Step 2 (`channelCoding_E2_lt_of_rate`) 揃った状態**、CCA の N₁/N₂ 抽出 2 箇所 (`:1771`, `:1835` の `Tendsto.metric_atTop`) を closed-form bound で置換する parent surgery (Step 3) のための部品完備。本ターン: parent surgery 本体 (~150-300 行、`channel_coding_achievability` の signature reshape + δ-uniform N export + `ChannelCodingShannonTheoremFull.lean` の hypothesis 自然 discharge) は次セッション。
>
> **Status (2026-05-15)**: orchestrator session で **D-1'' Phase D 主定理 (hypothesis pass-through MVP)** + **D-2'' Phase A 残補題 `condMutualInfo_map_right_measurableEquiv` (Z reshape)** 順次完了 (`ChannelCodingShannonTheoremFull.lean` 73→82 行 / `ChannelCodingShannonTheoremGeneral.lean` `errorProbAt_smooth_TV` を public 化 / `CondMutualInfo.lean` 553→686 行、すべて 0 sorry / 新規 warning 0)。**D-1'' Phase D**: 「固定 δ で parent D-1 を 1 回」案は技術不成立 (δ 固定で `2nδ → ∞`) と判定、撤退ラインで **hypothesis pass-through** 採用 — `h_passthrough : ∃ N, ∀ n ≥ N, ∃ (δ, 0<δ, δ≤1), 2nδ < ε/2 ∧ ∃ M ≥ ⌈exp(nR)⌉, ∃ c, ∀ m, errorProbAt(W_smooth δ, c, m) < ε/2` を hypothesis に取り、body は Phase C TV bound `errorProbAt_smooth_TV` で glue (10 行)。後続 parent surgery (~200-400 行、`channel_coding_achievability` の `Tendsto.metric_atTop` を closed-form 化) で hypothesis 自体を discharge 可能な interface を確立。**D-2'' Phase A map_right**: `eProd := e.prodCongr (.refl (X×Y))` で Z 軸 reshape、`compProd_map_condDistrib` (joint 側) + 新規 helper `compProd_map_left_prodMap` (factored 側、`((μ.map Zc) ⊗ₘ κ).map (e × id) = (μ.map (e∘Zc)) ⊗ₘ (κ.comap e.symm)`、Mathlib gap、~22 行) + `condDistrib_ae_eq_of_measure_eq_compProd` で `condDistrib X (e∘Zc) μ =ᵐ (condDistrib X Zc μ).comap e.symm` を導出 → `Measure.compProd_congr` + `klDiv_map_measurableEquiv` で吸収、+133 行。D-2'' Phase A 補題 4 本 (`_map_left/middle/right_measurableEquiv` + `isMarkovChain_map_left`) 完備。**E-3''' (strong typicality 経路) は infeasible 判定維持** — Phase E `h_codebook_avg_failure` は (P_X^n × codebookMeasure) 結合確率上の TAP (typical average property) を要求、Phase B 弱形 typicality (entropy only) では joint typical → distortion bound 原理的不可、Cover-Thomas 10.5 で strong typicality joint form (~500-800 行) 要。残 deferred: **D-1'' parent surgery** (`channel_coding_achievability` の N closed-form 化 + `h_passthrough` 自然 discharge ~200-400 行)、D-2'' Phase B (`h_yother_zero` 派生は `IsMemorylessChannel` 強化必要、原理的不可)、E-3''' fully-discharged form (~500-800 行)、E-8'' Birkhoff 自前 (~400-600 行)。
>
> **Status (2026-05-14, very late)**: orchestrator session で **E-3'' (1)+(2)+(3)+(4-6 partial)** 順次完了 (E-3' Phase A 拡張 199 行 + 新規 2 file 565 行 = 計 764 行追加、すべて 0 sorry / 0 warning)。E-3'' (1) **`measureToPmf`** (`RateDistortionAchievability.lean:471-505`、Phase A 末尾追加 47 行) で `Measure α → α → ℝ` 抽出 + `_mem_stdSimplex` + `_pos`。E-3'' (2) **entropy ↔ mutualInfoPmf bridge** (同 file +152 行 = 660 行最終) で `entropy_eq_negMulLog_sum_measureToPmf` (rfl) + `marginalFst/Snd_measureToPmf_eq` (Fubini-style preimage 等式 via `Prod.fst ⁻¹' {a} = ⋃ b, {(a,b)}`) + **`mutualInfoPmf_eq_entropy_diff`** (`mutualInfoPmf (measureToPmf (μ.map joint)) = H(Xs) + H(Ys) - H(joint)`、Phase E discharge 中核)。E-3'' (3) **`IIDProductInputJoint.lean`** (新規 225 行、12 補題) で `iidAmbientJointMeasure (joint : Measure (α × β)) := Measure.infinitePi (fun _ => joint)` + `_map_iidXs/iidYs/jointSequence` + `_identDistrib_*` + `_iIndepFun_*` + `_*_real_singleton_pos`。E-3'' (4-6 partial) **`RateDistortionAchievabilityPhaseEDischarge.lean`** (新規 340 行) で **主定理 `rate_distortion_achievability_partial_discharge`** を publish — `μ := rdAmbient qStar := iidAmbientJointMeasure (pmfToMeasure qStar)` を取り、Phase E witness form の **ambient / entropy / positivity / measurability hypotheses 全部** を internal discharge (`pmfToMeasure_map_fst/snd_real_singleton` + `rdAmbient_map_iidXs/iidYs/jointSequence` wrapper + `expectedJointDistortion_rdAmbient` distortion bridge)。**残り 2 hypothesis** (`h_codebook_avg_failure` + `h_failure_tendsto_zero`) は **strong typicality 要** — Phase B が weak typicality (entropy only) で書かれているため、"joint typical かつ distortion bad" の product-law 確率 exp-bound は原理的不可、これは Cover-Thomas 10.5 で strong typicality が要求される箇所と一致。残 deferred: D-1'' Phase D 主定理 (親 surgery ~200-400 行)、D-2'' (B.2 原理的不可)、**E-3''' fully-discharged form** (strong typicality 経路: Phase B 拡張 ~300-500 行 or strong typicality joint form 新規実装 ~500-800 行)、E-8'' Birkhoff 自前 (~400-600 行)。

> **Status (2026-05-14, late)**: orchestrator session で **E-3' Phase C-1 → C-2 → C-3 → D → E (witness-form MVP)** 順次完了 (4 新規 file、合計 1156 行、すべて 0 sorry / 0 warning)。Phase C-1 `RateDistortionAchievabilityPhaseC.lean` (109 行) で `per_codeword_no_match_prob` + `codebook_indep_no_match_prob_eq` ((1-p_typ)^M form) + `single_codeword_typical_match_prob` (fixed-x random codebook lower bound)。Phase C-2 (同 file 344 行に拡張) で `one_sub_pow_le_exp_neg_mul` + `p_typ_integrable` + `p_typ_avg_eq_indep_prob` (Fubini bridge: `∫ p_typ dP_X = (P_X.prod p).real JTS`) + `encoder_failure_prob_integral_bound` (source-averaged lift) + `encoder_failure_prob_le_exp_neg_M_avg`。Phase C-3 (同 file 422 行に拡張) で `exists_codebook_low_avg` (`f`-polymorphic pigeonhole、ChannelCoding `exists_codebook_le_avg` の lossy mirror)。Phase D `RateDistortionAchievabilityPhaseD.lean` (443 行) で `ceil_exp_mul_exp_neg_tendsto_atTop` + `exp_neg_tendsto_zero_of_tendsto_atTop` + `source_averaged_failure_tendsto_zero` (asymptotic decay) + `distortionMax` + `blockDistortion_le_distortionMax` + `blockDistortion_decompose` + `source_avg_distortion_le_simpler` (encoder-side failure form、Fubini なし simpler form)。Phase E `RateDistortionAchievabilityPhaseE.lean` (291 行) で **主定理 `rate_distortion_achievability_witness_form`** を hypothesis-pass-through MVP として完成 — `mutualInfoPmf qStar < R` witness 形 + ambient `(μ, Xs, Ys)` + `failure_seq → 0` + `h_codebook_avg_failure` + `h_dist_eq` + `h_slack` で `∃ N, ∀ n ≥ N, ∃ M ≥ ⌈exp(nR)⌉, ∃ c, c.expectedBlockDistortion ≤ D + ε'`。**Cover-Thomas 10.5 achievability half の証明構造 (Phase B/C/D bricks composition) 完成**。残りは fully-discharged 形への昇格に必要な **`measureToPmf` 抽出**、**entropy ↔ mutualInfoPmf bridge** (~80 行)、**`iidAmbient` 構築 mirror** (~150 行)、**`h_codebook_avg_failure` を Phase B+C 合成で具体化** (~80 行)、**`h_failure_tendsto_zero` を Phase D.4' で discharge** (~50 行) のみ、新数学なし。残 deferred: D-1'' Phase D 主定理 (親 surgery ~200-400 行)、D-2'' (B.2 原理的不可)、**E-3'' fully-discharged form** (~360 行)、E-8'' Birkhoff 自前 (~400-600 行)。
>
> **Status (2026-05-14)**: orchestrator session で **E-3' Phase B.1 → B.3 → B.2.2** 順次完了 (`RateDistortionAchievabilityPhaseB.lean` 738 行最終、0 sorry / 0 warning)。Phase B.1 `jointTypicalLossyEncoder` + `lossyCodeOfCodebook` + spec 補題 2 本、Phase B.3 `distortionTypicalSet` + WLLN-on-d section + `distortionTypicalSet_prob_tendsto_one` (AEP `logLikelihood` パターン verbatim 流用)、Phase B.2.2 `jointlyTypicalSet_card_ge` (private) + `jointlyTypicalSet_indep_prob_ge` (anti-direction of `_indep_prob_le`、joint-law 入力 hypothesis 経由)。同日他に **E-8' weakened** (`ShannonMcMillanBreiman.lean` 179 行、SMB sandwich-form wrapper、Birkhoff (E-8'') 完成で仮定なし形に昇格) + **D-1 A.3 closure** (`exists_capacity_achiever` を `IsCompact.exists_isMaxOn` で 4 行 close)。残 deferred: D-1'' Phase D 主定理 (親 surgery ~200-400 行)、D-2'' (B.2 原理的不可)、E-3' Phase C-E (~1300 行、`single_codeword_typical_match_prob` consumer + random codebook averaging + 主定理)、E-8'' Birkhoff 自前 (~400-600 行)。
>
> **Status (2026-05-13)**: 5 シード本体 + A 節 deferred 全件 + C 節 横断改善 全件 + **B 節 (B-1〜B-9 + 全 deferred B-1'/B-1''/B-2'/B-2''/B-5'/B-8'/B-3 Phase A+B/B-3'' Phase C+D) 完全完了**。audit-2026-05 棚卸し完了 (40🟢 / 9🟡 / 0🔴) + reuse-test-2026-05 (n-channel converse 再利用テスト、bridge ゼロ) 合格、両アーカイブは `docs/archive/`。Loomis–Whitney → Slepian–Wolf → AEP (Phase A〜F unified) → Stein (achievability + converse 半分 + liminf/limsup sandwich) → Polymatroid (structure 化込) → MaxEntropy → Pinsker (弱形 + シャープ形) → Brascamp–Lieb (組合せ形) + Hypercube product projection bound + Hypercube edge-boundary (AM-GM + entropy-sharp) → MI chain rule (n 変数 + i.i.d. corollary) → **Channel coding achievability (Cover-Thomas 7.7.1 半分、`R < I ⟹ ∃ code, P_err → 0`)** → Sanov A 形 → Sanov LDP B 形 (upper + equality 形双方向) → Strong Stein → Shannon code per-symbol (sandwich + Kraft 逆向き) → **AEP 完全形 D-3** → **Type-class size 下界 E-2** → **Strong typicality E-7** → **Csiszár I-projection E-6** → **Channel coding strong converse E-1 単発形** → **Slepian–Wolf achievability E-5 退化点 MVP** → **Channel coding general-input converse D-2 chain rule MVP (`log|M| ≤ ∑ I(X_i; Y^n | X^{<i}).toReal + Fano`、iid 仮定撤廃)** → **Rate-distortion converse E-4 single-shot MVP (`R(D̃).toReal ≤ log|M|` for `D̃ := 𝔼[d(X, decoder(encoder(X)))]`)** → **DMC feedback capacity converse E-10 chain rule + per-letter hypothesis MVP (`log|M| ≤ n·C + Fano`、`h_per_letter` 仮説形)** → **Differential entropy + Gaussian max-entropy E-9 完全形 (Phase A-E、`h(𝒩(m,v)) = (1/2) log(2πev)` + max-entropy + KL closed-form、`DifferentialEntropy.lean` 1010 行)** → **Shannon noisy channel coding theorem D-1 MVP (capacity 到達 + average→max + smoothing で hp_pos 内部処理、hW_pos のみユーザ仮定、`ChannelCodingShannonTheorem.lean` 918 行、4 ペア "弱/強形" 最後の未充足解消)** → **Feedback converse per-letter bound E-10' 完全形 (memoryless Markov reformulation 経路、`ChannelCodingFeedbackComplete.lean` 198 行、Cover-Thomas 7.12 完全形完走、CondMutualInfo 新規補題 0 行)** → **General converse memoryless per-summand bound D-2' MVP (撤退ライン形、`ChannelCodingConverseGeneralComplete.lean` 578 行、3 仮説 `h_yother_zero` / `h_split` / `h_markov_xprefix` を memoryless 性から派生可能形で受け取り、新規補題 `condMutualInfo_chain_rule_X_2var` / `_Y_2var`)** → **Rate-distortion monotonicity + specified-distortion form E-4' MVP (`RateDistortionConverseMonotone.lean` 151 行、`rateDistortionFunction_antitone` + `rate_distortion_converse_single_shot_specified`)** → **Shannon-McMillan-Breiman Phase A+B MVP (`Stationary.lean` 119 行 + `EntropyRate.lean` 498 行 = 617 行、定常過程 + entropy rate 定義 + 存在性、Phase C Birkhoff 自前 deferred)** → **Slepian-Wolf binning + 期待値 collapse E-5' Phase A+B MVP (`SlepianWolfBinning.lean` 273 行、`binningMeasure` + `binning_collision_prob` (Cover-Thomas 15.4 中核 collapse lemma))** → **Rate-distortion achievability E-3 Phase A 完全形 (`RateDistortionAchievability.lean` 461 行、`LossyCode` + pmf 直接形 `R(D)` `rateDistortionFunctionPmf` + 達成性 (`IsCompact.exists_isMinOn`) + entropy 形 `mutualInfoPmf` 連続性 + 単調性、後続 Phase B-E は E-3' deferred ~1500 行)** を **すべて 0 sorry** で通過。完了済みカードは本ファイルから撤去し、各 plan ファイル (`docs/<family>/*-plan.md`) に履歴を残置。**deferred 全件閉鎖**。**未実装 seed ゼロ**。新規 **D-1' / D-2'' / E-3' / E-4'' / E-5'' / E-8' deferred** 6 本を後継として登録。
>
> 起草時 (2026-05-10): Fano (測度論版) → Shannon converse (3 形) → Han 補集合形 → Han Phase D (subset average / Shearer) まで通った状態を起点に、次のムーンショット候補 5 本をシード化。
>
> ここに書いてあるのは **着手前の seed**。実装着手の判断 = 該当シードを `docs/<family>/<topic>-moonshot-plan.md` に複製 + `docs/moonshot-plan-template.md` で膨らませる。本ファイル自体はカード一覧として保ち、選定が確定したら該当カードに `→ <plan path>` のポインタを書き加える。

---

## 次のシード候補

### D. audit-2026-05 由来 (棚卸し 2026-05-13 起草、未着手)

`docs/audit-2026-05.md` の §4 で 🟡 判定された主定理のうち、scope 拡張が **moonshot 規模**
(数日以上) のものを seed 化。小規模な statement 修復 (full support 除去等) は分岐 B 修復 plan
側の管轄で、本シードには含めない。

- **D-1. Shannon noisy channel coding theorem (capacity reach + max error)** ✅ (2026-05-13) →
  [docs/shannon/channel-coding-shannon-theorem-plan.md](shannon/channel-coding-shannon-theorem-plan.md) —
  Cover-Thomas 7.7.1 **完全形 (W full-support 仮定下の MVP)**。`Common2026/Shannon/ChannelCodingShannonTheorem.lean`
  (918 行) で publish:
  - `capacity W := sSup {(mutualInfoOfChannel (pmfToMeasure p) W).toReal | p ∈ stdSimplex ℝ α}`
    + `capacity_bddAbove` (`entropy_le_log_card` 経由) + `capacity_lt_implies_exists_pmf`
    (`lt_csSup_iff` 適用)
  - `continuous_mutualInfoOfChannel_left`: 3-entropy 展開 + `Real.continuous_negMulLog` +
    `continuous_finsetSum` で MI の `p` 連続性
  - `errorProbAt_filter_card_bound` (Markov on Finset) + `Code.subcode` def +
    `Code.subcode_errorProbAt_le` (sub-code error 不変性) → `channel_coding_achievability_max_error`
    (average → max wrapper、既存 `channel_coding_achievability` + helper 2 本で rate 損失漸近吸収)
  - **主定理 `shannon_noisy_channel_coding_theorem`**:
    `R < capacity W` + `hW_pos` + `0 < R` + `0 < ε` ⟹ `∃ N, ∀ n ≥ N, ∃ code, max error < ε`

  **証明合成**: A.4 で `p₀` 取得 → smoothing `p_δ := (1-δ)p₀ + δ·uniform` (small `δ₀ > 0`) で
  full support 確保 + 連続性で `I(p_δ₀; W) > (R + I(p₀;W))/2 > R` → B.4 適用。

  **4 ペア "弱/強形" のうち最後の未充足 (audit-2026-05 §4 🟡 #9) が解消**。

  **scope-deferred → `D-1'` 後継**: `hW_pos` 緩和 (W に 0-prob atom がある一般形) は `W_smooth :=
  (1-δ)W + δ·UnifChannel` の連続近似で別 plan、~150-200 行。
  - A.3 `exists_capacity_achiever` + C.1 `mutualInfoOfChannel_restrict_to_support` は documentation
    only sorry 残置 (主証明は smoothing 経路で迂回、C.1 は Mathlib `klDiv` MeasurableEmbedding
    不変性 gap)。

- **D-1'. Channel.smooth infrastructure (smoothing + TV bound)** ✅ (2026-05-14、Phase A-C MVP) →
  [docs/shannon/channel-coding-shannon-theorem-general-plan.md](shannon/channel-coding-shannon-theorem-general-plan.md) —
  Phase A `Channel.smooth W δ a := (1-δ)•W a + δ•uniformMeasureβ` + Markov 性 + atom positivity、
  Phase B MI の `δ` 連続性 (3-entropy 展開 + `Real.continuous_negMulLog`) + `exists_smooth_capacity_gt`
  (固定 `p₀` 経由)、Phase C TV bound `errorProbAt_smooth_TV: |errorProbAt(W_smooth δ, c, m) − errorProbAt(W, c, m)| ≤ 2 n δ`
  を `Measure.pi` 上 `Fin.cons`-bijection + induction で tight 構成。
  `Common2026/Shannon/ChannelCodingShannonTheoremGeneral.lean` (671 行)。

  **後継 `D-1''` deferred (~250-450 行)**: Phase D 主定理 `shannon_noisy_channel_coding_theorem_general`
  (`hW_pos` 完全除去) には parent D-1 の `N(δ)` δ-uniform 上界が必要。これは parent
  `channel_coding_achievability` (`ChannelCodingAchievability.lean:1771, :1835`) の 2 つの
  `Tendsto.metric_atTop` extraction を closed-form bound に書き直す parent surgery
  (~200-400 行、AEP の rate-uniform 化 + parent N closed-form 化) が要件。Phase A-C infrastructure
  は D-1'' で本質的に再利用。判断ログ 6 で 4 戦略を評価 (撤退理由含む)。

  **D-1'' Step 1 着手 (2026-05-14、partial)**: AEP rate-uniform 化を
  `Common2026/Shannon/AEPRate.lean` (293 行) で publish。`typicalSet_prob_ge_of_rate` は
  Chebyshev (`ProbabilityTheory.meas_ge_le_variance_div_sq`) + pairwise variance sum
  (`ProbabilityTheory.IndepFun.variance_sum`) 経由で
  `n ≥ ⌈Var(pmfLog) / (η ε²)⌉ + 1 → μ {typicalSet} ≥ 1 - η` を closed-form で示す。
  これは parent surgery (戦略 3) の `N₁` (AEP block) closed-form 化に直接使える。
  Phase D 主定理は `Common2026/Shannon/ChannelCodingShannonTheoremFull.lean` (73 行) に
  statement のみ 1 sorry で保留。`N₂` (E2 exp decay) の closed-form 化 + 親 D-1 への合成は
  後続シードに deferred。

  **D-1'' Step 2 ✅ (2026-05-15、late)**: `AEPRate.lean` 293 → 364 行 (+71 行、0 sorry / 0 warning)。
  **`exp_neg_mul_lt_of_rate`** (`0 < g → 0 < ε' → ∃ N, ∀ n ≥ N, exp(-n·g) < ε'`、`N := ⌈max 0 (-log ε' / g)⌉ + 1`
  closed-form、`Real.lt_log_iff_exp_lt` 一発 + `max 0` で ε' ≥ 1 edge case 吸収) +
  **`channelCoding_E2_lt_of_rate`** (CCA `ChannelCodingAchievability.lean:1797-1810` の squeeze 補題
  verbatim 再現 + 補題 (a) で lift)。これで Step 1 + Step 2 揃い、CCA `:1771` / `:1835` の
  N₁/N₂ extraction を closed-form bound で置換する parent surgery (Step 3) のための部品完備。

  **D-1'' Phase D 主定理 hypothesis pass-through MVP ✅ (2026-05-15)**:
  `ChannelCodingShannonTheoremFull.lean` 73 → 82 行 (`sorry` 撤去、0 sorry / 0 warning)。
  `ChannelCodingShannonTheoremGeneral.lean:611 errorProbAt_smooth_TV` の `private` を public 化。
  **判断**: 「固定 δ で parent D-1 を 1 回呼ぶ」案は技術不成立 (δ 固定で `2nδ → ∞`、error 爆発)。
  撤退ライン採用 → hypothesis `h_passthrough : ∃ N, ∀ n ≥ N, ∃ (δ, 0<δ, δ≤1), 2nδ < ε/2 ∧
  ∃ M ≥ ⌈exp(nR)⌉, ∃ c, ∀ m, errorProbAt(W_smooth δ, c, m) < ε/2` を追加し、body は
  Phase C TV bound `errorProbAt_smooth_TV` で glue (10 行)。後続 parent surgery seed への
  interface が明示化、Phase A-C + Step 1 が組み合わさる形で 0 sorry 達成。
  **`D-1'' Phase D parent surgery` 後継 deferred**: hypothesis 自体を `channel_coding_achievability`
  の `Tendsto.metric_atTop` (`ChannelCodingAchievability.lean:1771, :1835`) を closed-form 化
  + Step 1 `typicalSet_prob_ge_of_rate` + AEPRate Step 2 (`N₂` closed-form) 合成で discharge
  (~200-400 行)。

- **D-2. Channel coding converse (general input form)** ✅ (2026-05-13, **chain rule 分解 MVP**) →
  [docs/shannon/channel-coding-converse-general-plan.md](shannon/channel-coding-converse-general-plan.md) —
  Cover-Thomas 7.9 **完全形**。既存 `shannon_converse_single_shot` (uniform input only) を出発点に、
  任意の入力分布で `R > I(p; W) ⟹ ∃ error floor` を示す。expurgation/Fano + `mutualInfo_iid_eq_nsmul`
  で n-channel 形にスケール。audit-2026-05 §4 🟡 #8 として記録。

  **本シードでは iid 仮定撤廃 + chain rule 分解段** を `Common2026/Shannon/ChannelCodingConverseGeneral.lean`
  (148 行) で publish: `channel_coding_converse_general_chainRule` は
  `log|M| ≤ ∑_i I(X_i; Y^n | X^{<i}).toReal + h(Pe) + Pe·log(|M|−1)` を任意 Markov encoder + 一様 Msg 下で
  bridge ゼロ (`shannon_converse_single_shot_markov_encoder` + `mutualInfo_chain_rule_fin`
  + `ENNReal.toReal_sum`) で示す。**残り 2 段** (memoryless per-summand bound
  `I(X_i; Y^n | X^{<i}) ≤ I(X_i; Y_i)` + 凸性で `R(p_avg) → R(D)`) は **D-2' deferred**
  (~500 行追加見込み、Mathlib に conditional MI の memoryless reduction lemma 未確認)。

  **先行成果 (reuse-test-2026-05, 2026-05-13 完了)**: i.i.d. 入力下の converse n-variable 化を
  bridge ゼロで実装、`Common2026/Shannon/ChannelCodingConverse.lean`
  (`channel_coding_converse_iid` 1 本) として publish。`shannon_converse_single_shot_markov_encoder`
  + `mutualInfo_iid_eq_nsmul` の合成だけで到達。これは D-2 plan の出発点として直接利用可能。

  reuse-test 由来の設計判断:
  - **uniform input 仮定の緩和は scope 縮小可**: n-channel スケーリングは single-shot 段で
    uniform を消費し、iid 段は入力分布非依存。general input への拡張は per-symbol I(p; W) の
    取り方 (任意 input law p) のみで、n-channel 部分は uniform から自由 → D-2 で本質的に
    新規となるのは expurgation (uniform 仮定除去) 段のみで、n-channel 段は既存 API 流用で済む。
  - **`mutualInfo_chain_rule_fin` は非 iid 入力で初めて出番**: iid 入力なら `iid_eq_nsmul` が
    直接 `n · I(X_0; Y_0)` を返すため chain rule + per-summand memoryless bound は不要。
    D-2 で general input (averaged distribution) を扱うときに `chain_rule_fin` + memoryless
    channel での per-summand `I(X_i; Y_i | X^{<i}) ≤ I(X_i; Y_i)` 追加段が必要になる。
    audit §4 🟡 で flag されていた "uniform input scope" が n-channel に本質ではないという
    意味では、修復優先度はむしろ低い (他の 🟡 案件先行が合理的)。

  **D-2' (memoryless per-summand bound) 完了** (2026-05-14、撤退ライン MVP) →
  [docs/shannon/channel-coding-converse-general-d2-prime-plan.md](shannon/channel-coding-converse-general-d2-prime-plan.md) —
  `Common2026/Shannon/ChannelCodingConverseGeneralComplete.lean` (578 行、0 sorry / 0 warning):
  - `IsMemorylessChannel μ Xs Ys`: 各 i で `IsMarkovChain μ ((X^{≠i}, Y^{≠i})) (X_i) (Y_i)`
  - `condMutualInfo_chain_rule_X_2var` + `_Y_2var`: 2 変数 conditional chain rule の新規補題
  - `memoryless_per_summand_bound`: per-summand 不等式 `condMI(X_i; Y^n | X^{<i}) ≤ MI(X_i; Y_i)` を
    3 仮説 `h_yother_zero` / `h_split` / `h_markov_xprefix` 形で publish
  - `channel_coding_converse_general_memoryless`: 主定理 `log|M| ≤ ∑ I(X_i; Y_i).toReal + Fano`
    (Phase C 仮説 pass-through)

  **後継 `D-2''` deferred**: Markov 左 post-processing + condMI Y 引数 reshape + Markov 中央 augment の
  CondMutualInfo.lean 補助補題 3 本を整備し、Phase C/D の 3 仮説を `IsMemorylessChannel` から内部派生
  する純粋形 (~200-300 行)。

  **D-2'' Phase A 部分着手** (2026-05-14、CondMutualInfo.lean 413 → 555 行、0 sorry / 0 warning):
  - ✅ `condMutualInfo_map_left_measurableEquiv` (X 引数 reshape 不変性): `compProd_map_condDistrib`
    + `condDistrib_comp` + `Kernel.map_prod_eq` + `Measure.compProd_map` の合成。
  - ✅ `condMutualInfo_map_middle_measurableEquiv` (Y 引数 reshape 不変性): `condMutualInfo_comm`
    2 回経由で left に帰着。
  - ✅ `isMarkovChain_map_left` (Markov 左 post-processing): γ-form Markov + `condDistrib_comp`。
  - ✅ `condMutualInfo_map_right_measurableEquiv` (Z reshape、2026-05-15 追加、CondMutualInfo.lean
    553 → 686 行、+133 行、0 sorry / 新規 warning 0): `eProd := e.prodCongr (.refl (X×Y))` で Z 軸
    reshape、joint 側は `compProd_map_condDistrib` 両方向 + `Measure.map_map`、factored 側は
    新規 private helper `compProd_map_left_prodMap` (`((μ.map Zc) ⊗ₘ κ).map (Prod.map e id)
    = (μ.map (e ∘ Zc)) ⊗ₘ (κ.comap e.symm)`、Mathlib gap、~22 行) +
    `condDistrib_ae_eq_of_measure_eq_compProd` で `condDistrib X (e∘Zc) μ =ᵐ (condDistrib X Zc μ).comap
    e.symm` を X, Y 個別に取得 → `Measure.compProd_congr` で結合 → `klDiv_map_measurableEquiv` で
    吸収。事前見積 ~150 行に対し +133 行で着地。**D-2'' Phase A 補題 4 本完備**
    (`_map_left/middle/right_measurableEquiv` + `isMarkovChain_map_left`)。
  - ❌ `isMarkovChain_augment_left_with_middle` (Phase A.3) — deferred (`Kernel.deterministic`
    plumbing 泥沼化見込)。
  - **B.2 (`h_yother_zero` 派生) は `IsMemorylessChannel` 単独からは原理的に不可と判明**:
    Markov chain `(X^{≠i}, Y^{≠i}) → X_i → Y_i` だけでは `condMI(X_i; Y^{≠i} | (X^{<i}, Y_i)) = 0`
    を導けない (X^n の Markov 構造 or i.i.d. の追加仮定が必要)。"純粋" 化には
    `IsMemorylessChannel` の強化が必要。Phase B/C 全体は次セッションへ。

- **D-3. AEP 完全形 (lower bound + 確率収束)** ✅ (2026-05-13) →
  [docs/shannon/aep-full-form-plan.md](shannon/aep-full-form-plan.md) — Cover-Thomas
  3.1.2 **完全 4 帰結** を `Common2026/Shannon/AEP.lean` 末尾 (Phase H, 211 行追加) で
  publish。3 補題:
  - `typicalSet_prob_ge`: 点別下界 `exp(-n(H+ε)) ≤ (μ.map (jointRV Xs n)).real {x}`
    for `x ∈ T_ε^n` (既存 `typicalSet_prob_le` の方向反転鏡像、上側不等式
    `(∑ pmfLog)/n - H < ε` を使用)
  - `typicalSet_card_ge`: サイズ下界 `(1-η)·exp(n(H-ε)) ≤ |T_ε^n|` whenever
    `μ.real(T) ≥ 1-η` (`typicalSet_prob_le` + 確率質量保存 `μ(T) = ∑_{x∈T} p(x)`
    via `sum_measureReal_singleton`)
  - `typicalSet_card_ge_eventually`: eventually-large-n 形
    `∃ N, ∀ n ≥ N, (1-η)·exp(n(H-ε)) ≤ |T_ε^n|` (上記 + `typicalSet_prob_tendsto_one`
    + `ENNReal.continuousAt_toReal` で ℝ≥0∞ → ℝ bridge)

  既存 `typicalSet_prob_le` / `typicalSet_card_le` / `typicalSet_prob_tendsto_one`
  と合わせ Cover-Thomas 3.1.2 (a)(1)(2) + (b)(3)(4) を完全充足。**full support 仮定の
  除去は scope deferred** (`Real.exp_log (hpos x)` で本質的に使用、`log 0 = 0` 規約では
  `exp 0 = 1 ≠ 0` で形式統一不能、判断ログ参照)。audit-2026-05 §4 🟡 #4 解消。

### E. Cover-Thomas 系列拡張 (2026-05-13 起草、未着手)

`B 節 + D 節` 完了後の自然な次の伸び代を「強形/弱形ペア完結」「achievability/converse ペア完結」
「i.i.d. → stationary 一般化」「discrete → continuous 枝分かれ」「横断 utility」の 5 軸で 10 本。
先行 utility 群 (E-2, E-6, E-7) を置くと後続 (E-1, E-3, E-5) が大幅短縮される依存関係。

- **E-1. Channel coding strong converse (Wolfowitz, 単発 Verdú-Han 形)** ✅ (2026-05-13) →
  [docs/shannon/channel-coding-strong-converse-plan.md](shannon/channel-coding-strong-converse-plan.md) —
  Cover-Thomas 7.9 strong form の中核 **情報密度 (Verdú-Han) 単発下界** を
  `Common2026/Shannon/ChannelCodingStrongConverse.lean` (380 行) で publish:
  - `highLLRSet W c Q threshold m`: codeword `m` の出力 LLR threshold 超え集合
    `{y | P_m^n.real {y} > exp(threshold) · Q.real {y}}` 定義。
  - `channelCoding_per_codeword_decomposition`: 任意 measurable `s` で
    `P_m^n.real s ≤ exp(threshold) · Q.real s + P_m^n.real(highLLR_m)`
    (Strong Stein `steinTypicalSet_Q_prob_ge` の channel-coding 対形)。
  - `channelCoding_average_success_le`: codeword 平均
    `1 - avgPe ≤ exp(threshold)/M + (1/M) ∑_m P_m^n.real(highLLR_m)`
    (decoder partition `∑_m Q.real(decodingRegion m) ≤ 1` で吸収)。
  - `channelCoding_strong_converse_singleShot` (主形): `threshold := log M + γ` 代入で
    `1 - avgPe ≤ exp γ + (1/M) ∑_m P_m^n.real(highLLR_m)` (Wolfowitz/Verdú-Han)。

  **shape-driven 設計**:
  - **任意 deterministic code、任意 reference probability measure `Q^n`** で deterministic に成立
    (情報スペクトル形)。i.i.d. random codebook 限定でない、入力分布非依存。
  - Strong Stein Phase A の plumbing (Markov ineq + 集合分解 + `sum_measureReal_singleton`)
    を channel-coding 設定にそのまま転写、Mathlib gap なし。
  - **asymptotic `Pe → 1` 段は scope-deferred** (本 plan の判断ログ 3 参照): WLLN-on-LLR
    + `IIDProductInput` ambient 接続 (~300-500 行) で別 plan に分離可能、`highLLRSet`
    が `steinTypicalSet` 系補集合に直接 reduce する設計。

  **横断 utility**: 単発下界そのものが Wolfowitz 鍵不等式の Lean 化として publish 価値。
  D-1 (capacity 到達 achievability 強形) と pair で 4 ペア (Pinsker / Stein / Sanov /
  **ChannelCoding**) 完結への第一歩。Phase A per-codeword 形は単独で hypothesis testing
  / channel resolvability 系の前段補題としても再利用可。

- **E-2. Method of types: type-class size lower bound** ✅ (2026-05-13) →
  [docs/shannon/type-class-lower-bound-plan.md](shannon/type-class-lower-bound-plan.md) —
  `typeClassByCount_card_ge_entropy`: `(n+1)^{-|α|} · exp(n · H(c/n)) ≤ |T_c|`
  (Cover-Thomas 11.1.3 size 下界、`H(c/n) := -∑ (c/n)·log(c/n)` 経験分布 entropy)。
  既存 `SanovLDPEquality.lean:705` `typeClassByCount_card_ge` (生形 `n^n / ∏ c^c`) に
  bridge identity `n^n / ∏ c^c = exp(n · H(c/n))` を加えるだけで取得。
  `Common2026/Shannon/TypeClassLowerBound.lean` (181 行)、新規定義 `entropyByCount` 含む。
  per-atom `c · log(c/n) = c · log c - c · log n` を `Nat.eq_zero_or_pos` 分岐 (`c = 0` で
  両辺 0、`c > 0` で `Real.log_div`) で proof、Stirling 依存なし。
  **横断 utility** として E-1 / E-5 / E-3 の前段に置く価値あり、`SanovLDPEquality`
  Stein 経路を直接 multinomial 経路で書き直す独立代替路の出発点としても再利用可。

- **E-3. Rate-distortion theorem achievability Phase A 完全形** ✅ (2026-05-14、初回 skeleton MVP → 同日 Phase A 完全形) →
  [docs/shannon/rate-distortion-achievability-plan.md](shannon/rate-distortion-achievability-plan.md) —
  Cover-Thomas 10.5。`Common2026/Shannon/RateDistortionAchievability.lean` (461 行、0 sorry / 0 warning):
  - Skeleton (120 行): `DistortionFn α β := α → β → NNReal`、`blockDistortion`、`LossyCode`、
    `LossyCode.expectedBlockDistortion`
  - **Phase A 完全形 (+341 行)**: pmf 直接形 `R(D)` の達成性まで:
    - `expectedDistortionPmf d q := ∑ a b, q(a,b) · d(a,b)` + `_nonneg` / continuity
    - `marginalFst q` / `marginalSnd q` + continuity / nonneg on simplex
    - `RDConstraint P_X d D : Set (α × β → ℝ) := {q ∈ stdSimplex | marginalFst = P_X ∧ expectedDistortionPmf d q ≤ D}`
    - `RDConstraint_isClosed` / `_isCompact` / `_convex` / `_subset_stdSimplex` / `_mono`
    - `mutualInfoPmf q := H(fst) + H(snd) − H(q)` (**entropy 形**、`Real.negMulLog` 経由で
      `α × β → ℝ` 全体で連続) — KL/log 比形は marginal 0 境界で連続性が崩れるため不採用
    - `continuous_mutualInfoPmf`
    - `rateDistortionFunctionPmf := sInf (mutualInfoPmf '' RDConstraint)` (binder-`⨅` ではなく
      `sInf` of image 形を採用、CCL の `BddBelow` 副条件で詰まらない)
    - `rateDistortionFunctionPmf_attained` — `IsCompact.exists_isMinOn` 経由
    - `rateDistortionFunctionPmf_eq_min` — 値表示 (`sInf` = `mutualInfoPmf qStar`)
    - `detReconstructionWitness P_X b₀ (a,b) := if b = b₀ then P_X a else 0` —
      `RDConstraint_nonempty_of_witness` の証人 (要 `[DecidableEq β]`)
    - `rateDistortionFunctionPmf_antitone` (`csInf_le_csInf` 経由)

  既存 E-4 / E-4' の `expectedDistortion d ν` / `rateDistortionFunction d P D` (Measure 形、`RateDistortionConverse.lean` + `RateDistortionConverseMonotone.lean`) は **並立**、本 Phase の pmf 形と bridge は B-E 開始時に必要に応じて作る (deferred)。

  **後続 `E-3'` deferred (~1500 行に縮約)**: Phase B (joint typical lossy encoder +
  decoder) + Phase C (random codebook + Fubini collapse) + Phase D (Cover-Thomas 10.5 (10.85) bound) +
  Phase E (主定理 `rate_distortion_achievability`)。Phase A 完全形完了により後段の
  statement 着地点 (`RDConstraint`, `mutualInfoPmf`, `rateDistortionFunctionPmf`) が確定。

  **E-3' Phase B.1 ✅ (2026-05-14、joint-typical lossy encoder + bundling MVP)** →
  `Common2026/Shannon/RateDistortionAchievabilityPhaseB.lean` (83 行、0 sorry / 0 warning):
  - `jointTypicalLossyEncoder μ Xs Ys hM ε c x`: `Classical.choose` で typical match `(x, c m) ∈ jointlyTypicalSet` の 1 つを選ぶ encoder。fallback `⟨0, hM⟩`。decoder 側 `jointTypicalDecoder` (`∃!` 要求) と対称、encoder は first match で十分なので `∃` ベース。
  - `lossyCodeOfCodebook`: `LossyCode M n α β` への bundling (`encoder := jointTypicalLossyEncoder`, `decoder := c`)
  - `jointTypicalLossyEncoder_spec_of_exists` / `_of_not_exists`: `dif_pos` / `dif_neg` 分岐の Classical.choose spec。

  **E-3' Phase B.3 ✅ (2026-05-14、distortionTypicalSet + WLLN-on-d + prob → 1 wrapper)** →
  `Common2026/Shannon/RateDistortionAchievabilityPhaseB.lean` (479 行、0 sorry / 0 warning):
  - `expectedJointDistortion μ X Y d`: Bochner 積分形 `∫ ω, (d (X ω) (Y ω) : ℝ) ∂μ`
  - `distortionTypicalSet μ Xs Ys d n ε δ := jointlyTypicalSet ∩ {blockDistortion ≤ 𝔼 d + δ}` + 6 structure 補題 (`_subset_jointlyTypicalSet`, `mem_distortionTypicalSet_iff`, `blockDistortion_le_of_mem_distortionTypicalSet` (B.2.1), `_finite`, `measurableSet_distortionTypicalSet`)
  - **WLLN-on-distortion section**: `distortionRealFn d (a,b) := (d a b : ℝ)` (Fintype 上 `measurable_of_finite`) + `distortionRV Xs Ys d i ω := (d (Xs i ω) (Ys i ω) : ℝ)` (`distortionRV_eq_comp` で `jointSequence` 上の合成として分解)。
  - `integrable_distortionRV` / `integral_distortionRV_zero` (= `rfl`、`expectedJointDistortion` と shape 一致) / `identDistrib_distortionRV` / `indepFun_distortionRV` (AEP `logLikelihood` パターン verbatim 流用)。
  - `distortionEmpirical_tendsto_ae`: SLLN (`strong_law_ae_real`) 直接適用、a.s. 形 Cesàro。
  - `distortionEmpirical_inProbability`: a.s. → in-measure via `tendstoInMeasure_of_tendsto_ae`。
  - `blockDistortion_jointRV_eq` bridge: `Fin.sum_univ_eq_sum_range` で Fin n / range n 形変換。
  - **`distortionTypicalSet_prob_tendsto_one`** (主結果): inclusion `goodJ ∩ (bigBad)ᶜ ⊆ targetEvt` + ChannelCoding `jointlyTypicalSet_prob_tendsto_one` の complement squeeze pattern verbatim 流用。**片側 inclusion のみ** (`distortionTypicalSet` は one-sided `blockDistortion ≤ E+δ`、`bigBad` は two-sided `|empirical-E| ≥ δ` ⟹ `targetEvt ⊋ goodJ ∩ (bigBad)ᶜ`、 sandwich で μ(targetEvt) → 1)。

  Phase B.2.2 (`single_codeword_typical_match_prob`、`(1 - p_typ)^M` random codebook 形) は **`jointlyTypicalSet_indep_prob_ge`** (anti-direction、existing `_indep_prob_le` を lower bound に書き直す) を要求、次セッションへ。

  **E-3' Phase B.2.2 ✅ (2026-05-14、anti-direction joint-AEP indep probability)** →
  `Common2026/Shannon/RateDistortionAchievabilityPhaseB.lean` (738 行、+259 行、0 sorry / 0 warning):
  - `jointlyTypicalSet_card_ge` (private): joint-law 入力 `μ.real (joint event) ≥ 1-η` から、φ-image 経由で `typicalSet_prob_le` on Zs 経由で `|JTS| ≥ (1-η)·exp(n(HZ-ε))`
  - `jointlyTypicalSet_indep_prob_ge`: `_indep_prob_le` mirror、per-summand `typicalSet_prob_ge` (X, Y 軸) + `_card_ge` で product-law 下界 `(1-η)·exp(n(HZ-HX-HY-3ε))`

  **shape-driven 設計判断**: 入力 hypothesis は **joint-law** 形 (`μ.real {ω | (jX, jY) ∈ JTS} ≥ 1 - η`) を採用。これは `jointlyTypicalSet_prob_tendsto_one` が直接供給する形であり、product-law 形 (`(μX.prod μY).real JTS ≥ 1 - η`) では circular。φ-image (`Fin n → α × β`) で size lower bound を確立する経路により、新規 Mathlib 補題ゼロで完結。Phase C consumer (`single_codeword_typical_match_prob` の deterministic-encoder 形 → random codebook averaging 経由 `(1 - p_typ)^M` bound) は `_indep_prob_ge` を**直接呼び出すだけ**で実装可能、本 Phase は consumer-side semantics を持ち込まず純粋確率不等式として publish。

  **E-3' Phase C-1 ✅ (2026-05-14、deterministic-x random codebook lower bound)** →
  `Common2026/Shannon/RateDistortionAchievabilityPhaseC.lean` (109 行、0 sorry / 0 warning):
  - `per_codeword_no_match_prob`: complement equality (`p.real {y | (x,y) ∉ JTS} = 1 - p.real {y | (x,y) ∈ JTS}`)
  - `codebook_indep_no_match_prob_eq`: `Measure.pi (fun _ : Fin M => p)` 上の no-match 確率 = `(1 - p_typ(x))^M` (`Measure.pi_pi` + `ENNReal.toReal_prod` + `Finset.prod_const`)
  - `single_codeword_typical_match_prob`: 主補題 `1 - (1 - p_typ(x))^M ≤ μ_codebook.real {c | ∃ m, (x, c m) ∈ JTS}`
  - **設計判断**: 1-層 `Measure.pi (fun _ : Fin M => p)` 形を採用 (2-層 `codebookMeasure` 不採用)、channel-coding API 依存ゼロで Phase C 自立。

  **E-3' Phase C-2 ✅ (2026-05-14、source-averaged form + Fubini bridge)** →
  `RateDistortionAchievabilityPhaseC.lean` 109 → 344 行 (+235 行、0 sorry / 0 warning):
  - `one_sub_pow_le_exp_neg_mul`: `(1-t)^M ≤ exp(-M·t)` for `t ∈ [0,1]` (`Real.one_sub_le_exp_neg` + `pow_le_pow_left₀` + `Real.exp_nat_mul`)
  - `p_typ_integrable`: bounded × prob measure → integrable
  - **`p_typ_avg_eq_indep_prob`** (本 Phase 中核、bridge): `∫ x, p.real {y | (x, y) ∈ JTS} dP_X = (P_X.prod p).real JTS` (`Measure.prod_apply` + `integral_toReal` で section identity = `rfl`、~40 行で clean に突破)
  - `encoder_failure_prob_integral_bound`: source-averaged lift of C-1 (Fubini)
  - `encoder_failure_prob_le_exp_neg_M_avg`: `integral_mono` + 補題 1 で `(1-p)^M → exp(-M·p)` の積分 lift

  **E-3' Phase C-3 ✅ (2026-05-14、`f`-polymorphic pigeonhole)** →
  `RateDistortionAchievabilityPhaseC.lean` 344 → 422 行 (+78 行、0 sorry / 0 warning):
  - `exists_codebook_low_avg`: `ChannelCodingAchievability.exists_codebook_le_avg` の lossy mirror、`f : Codebook M n β → ℝ` polymorphic 化 (channel-coding-specific `codebookToCode + averageErrorProb` 配管を抜く)。後段 Phase D で encoder-failure / expectedBlockDistortion 双方に再利用可。

  **E-3' Phase D MVP ✅ (2026-05-14、asymptotic decay + distortion decomposition)** →
  `Common2026/Shannon/RateDistortionAchievabilityPhaseD.lean` (443 行、0 sorry / 0 warning):
  - `ceil_exp_mul_exp_neg_tendsto_atTop`: `R > θ ≥ 0 ⟹ ⌈exp(nR)⌉ · exp(-nθ) → ∞` (`Real.tendsto_exp_atTop`)
  - `exp_neg_tendsto_zero_of_tendsto_atTop`: `f → ∞ ⟹ exp(-f) → 0` (3 行、`tendsto_neg_atTop_atBot` + `Real.tendsto_exp_atBot.comp`)
  - `source_averaged_failure_tendsto_zero`: 上界 chain `failure_seq n ≤ exp(-M_n · (1-η) · exp(-n·θ))` + squeeze で `failure_seq → 0`
  - `distortionMax d := Finset.univ.sup' (...) (fun ab => d ab.1 ab.2)` + `blockDistortion_le_distortionMax`
  - `blockDistortion_decompose`: if/else 形 distortion 上界
  - `source_avg_distortion_le_simpler`: codebook 固定、source `P_X` 上の Bochner 積分上界。**failure event は encoder-side** (`B := { x | (x, c(enc x)) ∉ distortionTypicalSet }`)、existence-form ではない (subagent shape-driven 判断、joint typical encoder は **joint typicality のみ保証**、distortion typicality を別途要求するため encoder-side に縮約するほうが直線的)。

  **E-3' Phase E MVP ✅ (2026-05-14、witness-form 主定理)** →
  `Common2026/Shannon/RateDistortionAchievabilityPhaseE.lean` (291 行、0 sorry / 0 warning):
  - **主定理 `rate_distortion_achievability_witness_form`**: `mutualInfoPmf qStar < R` witness 形 + ambient `(μ, Xs, Ys)` + `failure_seq → 0` + `h_codebook_avg_failure` + `h_dist_eq` + `h_slack` を hypothesis として、`∃ N, ∀ n ≥ N, ∃ M ≥ ⌈exp(nR)⌉, ∃ c : LossyCode M n α β, c.expectedBlockDistortion (μ.map (Xs 0)) d ≤ D + ε'` を 5 ステップで証明 (`failure_seq → 0` から N 抽出 → `Mn := ⌈exp(nR)⌉` → Phase D.5 per-codebook 上界 → codebookMeasure 加重平均で `≤ Edδ + dMax · failure_seq n` → Phase C.3 pigeonhole)。
  - **撤退戦略 D 採用**: entropy bridge / iidAmbient 構築 / Phase B+C 合成 (`h_codebook_avg_failure`) / Phase D.4' 具体化 (`h_failure_tendsto_zero`) を **すべて hypothesis pass-through で迂回**、Cover-Thomas 10.5 achievability half の**証明構造そのもの** (Phase B/C/D bricks composition) を独立 publish。

  **E-3'' (1)+(2)+(3)+(4-6 partial) ✅ (2026-05-14、ambient/entropy/positivity discharge)** → Phase A 拡張 199 行 + 新規 2 file 565 行 (合計 764 行、0 sorry / 0 warning):
  - **(1) `measureToPmf`** (`RateDistortionAchievability.lean:471-505` Phase A 末尾追加 47 行): `Measure α → α → ℝ` 抽出 + `_nonneg` / `_sum_eq_one` / `_mem_stdSimplex` / `_pos`。
  - **(2) entropy ↔ mutualInfoPmf bridge** (同 file +152 行 = 660 行最終): `entropy_eq_negMulLog_sum_measureToPmf` (rfl で 1 行、entropy 定義そのもの) + `marginalFst/Snd_measureToPmf_eq` (`Prod.fst ⁻¹' {a} = ⋃ b, {(a,b)}` 経由の Fubini-style preimage 等式) + **`mutualInfoPmf_eq_entropy_diff`** (`mutualInfoPmf (measureToPmf (μ.map joint)) = H(Xs) + H(Ys) - H(joint)`、Phase E discharge 中核 bridge)。
  - **(3) `IIDProductInputJoint.lean`** (新規 225 行、12 補題): `iidAmbientJointMeasure (joint : Measure (α × β)) := Measure.infinitePi (fun _ => joint)` + `_map_iidXs/iidYs/jointSequence` + `_identDistrib_*` + `_iIndepFun_*` + `_*_real_singleton_pos` (要 `[Nonempty β]` for `joint.map Prod.fst` の singleton positivity)。`IIDProductInput.lean` (399 行、channel coding 用) は touch せず並立 publish (B-3'' 親不変原則継承)。
  - **(4-6 partial) `RateDistortionAchievabilityPhaseEDischarge.lean`** (新規 340 行): **主定理 `rate_distortion_achievability_partial_discharge`** を publish — `μ := rdAmbient qStar := iidAmbientJointMeasure (pmfToMeasure qStar)` を取り、Phase E witness form の **ambient / entropy / positivity / measurability hypothesis 全部** を internal discharge (`pmfToMeasure_map_fst/snd_real_singleton` + `rdAmbient_map_iidXs/iidYs/jointSequence` wrapper + `expectedJointDistortion_rdAmbient` distortion bridge)。
  - **残 2 hypothesis** (`h_codebook_avg_failure` + `h_failure_tendsto_zero`) は **strong typicality 範囲外**: Phase B が weak typicality (entropy only) で書かれているため、"joint typical かつ distortion bad" の product-law 確率 exp-bound は原理的不可。Cover-Thomas 10.5 で strong typicality が要求される箇所と一致。**E-3'''** deferred (Phase B 強化 ~300-500 行 or strong typicality joint form 新規実装 ~500-800 行)。
  - **shape-driven 設計判断**: entropy 定義 (`Common2026/Shannon/Bridge.lean:43-44`) が既に `∑ a, Real.negMulLog ((μ.map Xs).real {a})` 形 (pmf 形そのもの) なので、bridge は `rfl` 1 行 + marginal identity 2 本で完結、`klDiv` ↔ `mutualInfoPmf` の重い変換が不要。`Common2026/Shannon/Bridge.lean` の既存 `mutualInfo_eq_entropy_sub_condEntropy` (line 588-595) は使わず、Phase A 内 entropy bridge で完結。

- **E-4. Rate-distortion converse** ✅ (2026-05-13, **single-shot MVP**) →
  [docs/shannon/rate-distortion-converse-plan.md](shannon/rate-distortion-converse-plan.md) —
  Cover-Thomas 10.4。`Common2026/Shannon/RateDistortionConverse.lean` (213 行) で
  `rate_distortion_converse_single_shot`: 任意の単発 lossy code `(encoder : α → M, decoder : M → β)`
  で `R(D̃).toReal ≤ log|M|` を `D̃ := 𝔼[d(X, decoder(encoder(X)))]` 実測歪み形で示す。

  **R(D) shape**: `rateDistortionFunction d P D : ℝ≥0∞ := ⨅ ν (_:ν.map fst = P) (_:E[d] ≤ D), klDiv ν (P × ν.map snd)`
  (Mathlib `iInf` over `Measure (α × β)`)。`mutualInfo μ X X̂ = klDiv (μ.map (X, X̂)) ((μ.map X).prod (μ.map X̂))`
  の定義と feasible point `ν := μ.map (X, X̂)` を **rfl で一致** させる shape-driven 設計。

  **証明 chain (4 step、~80 行)**: `entropy μ W ≤ log|M|` (`MaxEntropy.entropy_le_log_card`) →
  `(mutualInfo μ X W).toReal ≤ entropy μ W` (Bridge + `condEntropy_nonneg`) →
  `mutualInfo μ X X̂ ≤ mutualInfo μ X W` (DPI: `mutualInfo_le_of_postprocess`) →
  `rateDistortionFunction d (μ.map X) D̃ ≤ mutualInfo μ X X̂` (`iInf_le` + marginal 簡約)。

  **n-letter form** (`rate ≥ R(D)` for D ≥ D̃ + concavity/Jensen) は **E-4' deferred**
  (R(D) convexity + Jensen で ~500-1000 行追加見込み)。**MI 有限性は仮定** (一般 closure 別途)。
  既存 Common2026 資産のみで Mathlib gap ゼロ。

- **E-4'. Rate-distortion converse monotonicity + specified-distortion form** ✅ (2026-05-14、MVP) →
  [docs/shannon/rate-distortion-converse-plan.md](shannon/rate-distortion-converse-plan.md) —
  `Common2026/Shannon/RateDistortionConverseMonotone.lean` (151 行、0 sorry / 0 warning):
  - `rateDistortionFunction_antitone`: `D₁ ≤ D₂ ⟹ R(D₂) ≤ R(D₁)` (feasible set が D 大きいほど大きい
    ⟹ `iInf` antitone)
  - `rate_distortion_converse_single_shot_specified`: `∫ d(X, decoder(encoder X)) ∂μ ≤ D ⟹
    R(D).toReal ≤ log|M|` (親 single-shot + monotonicity)

- **E-4''. Rate-distortion R(D) convexity + n-letter regulated form** ✅ (2026-05-14, **Phase A + B core MVP**) →
  [docs/shannon/rate-distortion-convexity-plan.md](shannon/rate-distortion-convexity-plan.md) —
  `Common2026/Shannon/RateDistortionConvexity.lean` (256 行、0 sorry / 0 warning):
  - **Phase A**: `mixtureMeasure λ ν₁ ν₂` (measure-level convex combination) + 4 補題
    (`mixtureMeasure_map_fst` / `mixtureMeasure_map_snd` の pushforward 線形性、
    `mixtureMeasure_map_fst_eq` で X-marginal `P` 保存、`expectedDistortion_mixtureMeasure`
    で distortion 線形性、`mixtureMeasure_feasible` で feasibility 保存)
  - **Phase B core**: `rateDistortionFunction_convexOn` (R(D) 凸性主補題) を
    `klDiv` joint convexity を hypothesis 化した **subnormal 形** で publish:
    `R(λD₁+(1-λ)D₂) ≤ ofReal λ · R(D₁) + ofReal (1-λ) · R(D₂)` を、
    任意の feasible `ν₁, ν₂` に対する mixture の `klDiv` 凸不等式 (`h_klDiv_conv`) と
    distortion integrability (`h_int_witness`) を仮定として受け取り、`ENNReal.mul_iInf_of_ne`
    + `iInf_add` / `add_iInf` で iInf 階層に分配 + boundary case (`lam ∈ {0, 1}`) を別 branch
    で処理。

  **後継 `E-4'''` 完結** (2026-05-14, **Step A-E 全段、有限アルファベット版 R(D) 凸性
  仮説なし形完成**) → `Common2026/Shannon/RateDistortionConvexityDischarge.lean`
  (788 行、0 sorry / 0 warning):
  - **Step A** (`klFun_weighted_two_point` + `klDivPmf_joint_convex_two_point`):
    per-atom 2 点 joint convexity (算術核) + 有限アルファベット pmf 形 2 点 joint convexity
  - **Step B** (`mixtureMeasure_real_singleton` + `marginalProd_real_singleton` +
    `sum_marg_klFun_eq_klDivSumForm` 形 bridge + `klDivSumForm_mixtureMeasure_le`):
    Real-side 主補題。**X-marginal 共有が必須** (`marg(mix) = λ marg(ν₁) + (1-λ) marg(ν₂)`
    が cross term なしで成立する条件)、Step A `klFun_weighted_two_point` を per-atom 適用 +
    `sum_marg_klFun_eq_klDivSumForm` (summed identity、prob 正規化 `∑(marg - ν) = 0` 経由) で
    `klDivSumForm` と `klDivPmf` 形を橋渡し
  - **Step C** (`klDiv_eq_ofReal_klDivSumForm`): `klDiv ν marg = ofReal (klDivSumForm ν marg)`
    AC 付き bridge。Sanov の `klDivSumForm_eq_toReal_klDiv` を **`Q full support` 仮説なし**
    で再導出 (`Q.real{a} = 0` atom は AC 経由で `P.real{a} = 0`、両側 `0 · _ = 0` で消失)、
    Fintype 上 integrability 自動 + `klDiv_ne_top_iff` で `ofReal_toReal` 経由
  - **Step D** (`klDiv_mixture_joint_convex`): measure-level 主補題。Step B + Step C 合成。
    mixture の AC propagation は per-singleton 分解 (margMix{p} = (mix.map fst){p.1} ·
    (mix.map snd){p.2} = 0 ⟹ either factor 0 ⟹ mix{p} = 0、Fintype + `sum_measure_singleton`
    で AC 全体に lift)、ENNReal/Real plumbing は `← ENNReal.ofReal_mul` + `← ENNReal.ofReal_add`
    + `ofReal_le_ofReal`
  - **Step E** (`rateDistortionFunction_convexOn_pmf`): 仮説なし主定理。親
    `rateDistortionFunction_convexOn` の `h_klDiv_conv` を Step D で discharge、
    case-split on `klDiv νᵢ marg(νᵢ) = ∞`: 有限側は `klDiv_ne_top_iff` で AC 抽出 → Step D
    適用、無限側 + boundary `lam = 0/1` は mixtureMeasure simp + ENNReal.mul_top で trivial
    bound。`h_int_witness` は `Finset.sup'` で bounded 化 + `Integrable.mono'`
  **`E-4''C`** 実装完了 (2026-05-14, **n-letter converse MVP**) →
  `Common2026/Shannon/RateDistortionConverseNLetter.lean` (393 行、0 sorry / 0 warning):
  - **Stage 1** `rate_distortion_converse_n_letter_block`:
    `rate_distortion_converse_single_shot_specified` を
    `(α := Fin n → α, β := Fin n → β, M := Fin M)` で **直接 instantiate**。
    block distortion `(fun x y => blockDistortion d n x y)` を distortion measure
    として渡し、`c.expectedBlockDistortion P_X d ≤ D` を仮定に取って
    `(rateDistortionFunction (blockDistortion d n) (P_X^n) D).toReal ≤ log M` を出す。
  - **Stage 2** `rate_distortion_converse_n_letter_singleLetter`:
    single-letterized 形 `(rateDistortionFunction d_R P_X D).toReal ≤ (1/n) · log M`。
    Chain: per-letter `R(D̃_i) ≤ I(X_i; X̂_i)`
    (`rateDistortionFunction_le_mutualInfo_perLetter`) → MI super-additivity
    `h_super: ∑ I(X_i; X̂_i) ≤ I(X^n; X̂^n)` (hypothesis pass-through) →
    block-level MI bound `(mutualInfo μ X^n X̂^n).toReal ≤ log M`
    (`mutualInfo_block_le_log_card`, DPI + max-entropy chain) → n-way Jensen +
    block-distortion Fubini + antitonicity を **`h_jensen_antitone` 単一仮説に bundle**
    (toReal 形)。
  - **設計判断**: n-way Jensen + block-distortion Fubini + MI tensorization は
    各々 ~50-200 行で独立に discharge 可能だが本 MVP では **hypothesis pass-through**
    で抜く (Step 1.5 `mutualInfo_block_le_log_card` のみ自前 discharge)。既存
    file は不変、新規 file 1 本のみ。

- **E-5. Slepian–Wolf achievability** ✅ (2026-05-13, **退化点 MVP**) →
  [docs/shannon/slepian-wolf-achievability-plan.md](shannon/slepian-wolf-achievability-plan.md) —
  Cover-Thomas 15.4。`Common2026/Shannon/SlepianWolfAchievability.lean` (310 行) で SW
  encoder pair の **退化点 corner-point 達成可能性 2 本**:
  - `slepian_wolf_achievability_corner_Y`: rate pair `(log|α|, R_Y)` for `R_Y > H(Y)`
    (X 側 trivial encoder + Y 側 `source_coding_achievability` AEP の合成)
  - `slepian_wolf_achievability_corner_X`: 対称形 `(R_X, log|β|)` for `R_X > H(X)`

  **退化点 MVP に commit**: Cover-Thomas 15.4 完全形 (3-bound rate region full
  `R_X > H(X|Y), R_Y > H(Y|X), R_X + R_Y > H(X, Y)`) は **random binning + joint typicality
  decoder** 経路で **~2000 行規模** (`binningMeasure : Measure (α^n → Fin M_X)` の
  Fubini machinery + conditional typical slice size bound + 4-term error decomposition +
  pigeonhole) で session budget 外。本 plan は **2 corner-point MVP** を publish、
  **non-trivial corner** (`R_X = H(X|Y), R_Y = H(Y)` 等) と full rate region は
  **E-5' deferred** 後継カードへ。

  **横断 utility**: `swErrorProb` 定義は E-5' での error event definition そのまま再利用可。
  各 corner-point 結果は SW rate region の 2 自明 corner を formal に pin down し、
  E-5' で任意 rate triple への拡張時に boundary check として effective。

- **E-5'. Slepian–Wolf binning 機構 + 期待値 collapse MVP** ✅ (2026-05-14) →
  [docs/shannon/slepian-wolf-full-rate-region-plan.md](shannon/slepian-wolf-full-rate-region-plan.md) —
  E-5 deferred 後継の **Phase A + B 基盤** を `Common2026/Shannon/SlepianWolfBinning.lean`
  (273 行、0 sorry / 0 warning) で publish:
  - `binningMeasure α n M := Measure.pi (fun _ : (Fin n → α) => uniformOn univ)` (Fintype 上 uniform pi)
  - `IsProbabilityMeasure` instance + `binningMeasure_singleton_real` (`(1/M)^{|α|^n}` singleton mass)
  - **`binning_collision_prob`**: `x ≠ x' ⟹ (binningMeasure α n M).real {f | f x = f x'} = 1/M`
    (Cover-Thomas 15.4 達成性の中核 collapse lemma)
  - `binning_collision_prob_eq_self`: 自己 collision = 1

  `codebookMeasure` Mathlib API (`Measure.pi` + `uniformOn`) で独立定義経路 (Plan 0 判断 (B))、
  既存 `ChannelCodingAchievability` 親 file 不変。

  **後継 `E-5''` 完結** (2026-05-14): Cover-Thomas 15.4.1 完全形 (3-bound 同時 achievability)。
  本 MVP の `binning_collision_prob` を中核として再利用、Phase A〜F すべて publish:
  Phase C `SlepianWolfConditionalTypicalSlice.lean` (315 行、conditional typical slice size bound
  `≤ exp(n · (H(X|Y) + 2ε))`)、Phase D + E + F は `SlepianWolfFullRateRegion.lean` (2474 行、
  0 sorry / 0 warning) に集約: `swJointTypicalDecoder` + 4-way error decomposition + Phase E
  各 E_0/E_X/E_Y/E_{XY,strict} expectation bound + Phase F.0/F.1/F.2/F.3 (bridge + 期待値
  aggregator + pigeonhole + **主定理 `slepian_wolf_full_rate_region_achievability`**)。主定理は
  hypothesis `H(X|Y) < R_X, H(Y|X) < R_Y, H(X,Y) < R_X + R_Y` で codebook size `⌈exp(n·R_X)⌉,
  `⌈exp(n·R_Y)⌉` を取り、encoder/decoder と error → 0 を Cover-Thomas 15.4.1 完全形で確立。

- **E-6. Csiszár I-projection / Pythagorean inequality** ✅ (2026-05-13) →
  [docs/shannon/csiszar-projection-plan.md](shannon/csiszar-projection-plan.md) —
  Cover-Thomas 11.6.1。凸閉集合 `K ⊆ stdSimplex ℝ α` 上で 3 主結果を `Common2026/Shannon/CsiszarProjection.lean`
  (487 行) で publish:
  - `csiszar_projection_exists`: 閉非空 `K` + full-support reference `Q` で
    `∃ Q* ∈ K, IsMinOn (klDivPmf · Q) K Q*`
    (`isCompact_stdSimplex` + `IsCompact.exists_isMinOn` + `klDivPmf` 連続性)
  - `csiszar_projection_unique`: 凸 `K` + `Qstar, Qstar'` 両方最小化元 ⟹ 等しい
    (Mathlib `strictConvexOn_klFun` 経由の `klDivPmf_strictConvexOn_left` で midpoint 矛盾)
  - `csiszar_pythagoras_inequality`: 最小化元 `Q*` + `P ∈ K` (full support) で
    `klDivPmf P Q ≥ klDivPmf P Q* + klDivPmf Q* Q` (Cover-Thomas 11.6.1)

  鍵は **1 次条件** `∑ a, (P a - Q* a) (log Q* a - log Q a) ≥ 0` の導出: `φ(t) := klDivPmf ((1-t)Q* + tP) Q`
  に `HasDerivAt φ D 0` を per-summand `hasDerivAt_klFun` + chain rule + `HasDerivAt.sum` で取得 →
  `Pt t ∈ K` (`t ∈ [0,1]`) 凸性 + minimality で `φ 0 ≤ φ t` → `slope φ 0` の `𝓝[>] 0` 極限
  経由で `D ≥ 0` (`hasDerivAt_iff_tendsto_slope_left_right` + `ge_of_tendsto`)。
  代数恒等式 `klDivPmf P Q = klDivPmf P Q* + ∑ P (log Q* - log Q)` (full support, `log_div`) +
  `klDivPmf Q* Q = ∑ Q* (log Q* - log Q)` (`klFun (Q*/Q)` 展開 + `∑ P = ∑ Q* = ∑ Q = 1`) で
  Pythagorean に整形。

  **shape-driven 設計判断**:
  - **`Measure α` ではなく `α → ℝ` (pmf 直接) + `stdSimplex ℝ α`** を採用 (Mathlib `isCompact_stdSimplex`
    + `convex_stdSimplex` + `isClosed_stdSimplex` off-the-shelf)。`(klDiv P Q).toReal` 形は
    `Sanov.klDivSumForm_eq_toReal_klDiv` 経由の post-bridge で可能 (本 plan scope 外)。
  - **`klFun_sharp_lower` (PinskerSharp) refactor は不要**: Mathlib `strictConvexOn_klFun`
    (`Mathlib.InformationTheory.KullbackLeibler.KLFun`) が既存、そのまま再利用。
  - **Pythagorean は inequality** (Cover-Thomas 11.6.1)。linear family 等式形 (Cover-Thomas 11.6.4)
    は scope-deferred (plan Phase E)。一般 closed convex `K` では equality は成立しない。

  **横断 utility** として `klDivPmf P Q` の独立 publish に意義あり (`Sanov.klDivSumForm`
  と shape 共有、`klDivPmf_eq_log_diff_sum` の標準和形は他で再利用可能)。E-1 (Stein 関連)
  / E-3 (rate-distortion) / E-5 (Slepian-Wolf achievability) の i.i.d. 最適化議論で出番。

- **E-7. Strong typicality** ✅ (2026-05-13) →
  [docs/shannon/strong-typicality-plan.md](shannon/strong-typicality-plan.md) —
  Cover-Thomas 11.2。`Common2026/Shannon/StrongTypicality.lean` (614 行) で
  `stronglyTypicalSet := {x | ∀ a, |(typeCount x a : ℝ)/n - P(a)| ≤ ε}` を per-letter form で
  定義 + 3 主定理を **すべて 0 sorry** で publish:
  - `stronglyTypicalSet_prob_tendsto_one`: `μ {ω | jointRV ∈ A^*_ε} → 1`
    (per-letter `letterIndicator` に `strong_law_ae_real` を `α` 個分回し、
    `measure_iUnion_fintype_le` で union bound)
  - `stronglyTypicalSet_card_le`: `|A^*_ε| ≤ exp(n(H + ε·L + δ))` for any `δ > 0`
    where `L := ∑_a |log P(a)|` (`logSumAbs`)
  - `stronglyTypicalSet_card_ge_eventually`: `∃ N, ∀ n ≥ N, (1-η)·exp(n(H - ε·L - δ)) ≤ |A^*_ε|`

  鍵は **Strong → Weak typicality bridge** (`weak_displacement_eq_strong_sum`):
  `(∑_i pmfLog (x_i))/n - H(P) = ∑_a (P(a) - typeCount x a / n) · log P(a)`
  → 三角不等式 + strong typical `|...| ≤ ε` → `|.../n - H| ≤ ε·L` → `A^*_ε ⊆ T_{ε·L+δ}`
  (`typicalSet` of weak typicality)。Phase 4 size sandwich は AEP の既存
  `typicalSet_card_le` / `typicalSet_prob_le` を `ε ← ε·L+δ` で呼ぶだけ。

  **Joint version は scope-deferred** (本 plan は `α` generic、`α := α'×β` 代入で joint 形が直接
  得られる。marginal↔joint equivalence は E-5 Slepian–Wolf achievability の前段で別途取得可能)。
  **横断 utility** として E-1 / E-5 の前段に置く価値あり。

- **E-8. Shannon–McMillan–Breiman theorem (stationary ergodic AEP)** ✅ (2026-05-14、Phase A+B MVP) →
  [docs/shannon/shannon-mcmillan-breiman-plan.md](shannon/shannon-mcmillan-breiman-plan.md) —
  Cover-Thomas 16.8 の **基盤 (定常過程 + entropy rate)** 完成。`Common2026/Shannon/Stationary.lean`
  (119 行) + `EntropyRate.lean` (498 行) = 合計 617 行、0 sorry / 0 warning:
  - `StationaryProcess` / `ErgodicProcess` 構造体 (`MeasurePreserving T μ μ` + `X : Ω → α` + obs/blockRV)
  - `identDistrib_obs_zero` (定常性ラベル、`IdentDistrib (obs i) (obs 0)`)
  - `blockEntropy` / `conditionalEntropyTail` / `entropyRate` 定義
  - `blockEntropy_succ_chain_rule` (chain rule for block entropy)
  - `conditionalEntropyTail_antitone` (定常性 reshape + conditioning monotonicity 経由)
  - `entropyRate_exists_of_stationary` (単調非増 + Cesàro)
  - `entropyRate_eq_lim_condEntropy` (Cesàro 等価)
  - 鍵 helper: `condEntropy_eq_pushforward` (joint pushforward 等式 ⇒ condEntropy 等式)

  **後継 `E-8'` deferred**: Phase C (Birkhoff 自前 ~200-400 行) + Phase D (SMB 主定理 `-(1/n) log p(X^n) → H` a.s.、~80-150 行) + Phase E (i.i.d. 特殊化、~50-100 行)。Birkhoff a.s. 版 Mathlib 不在で plan の最大の山場。Lempel–Ziv (将来 seed) の前段。

  **E-8' Phase C.1 着手分析 (2026-05-14)**: Phase 0' Mathlib 再調査で **martingale 経路 (Lalley) は Mathlib API では直接成立しない**ことが判明、`BirkhoffErgodic.lean` 着手前に撤退 (実装ファイル未作成)。詳細は [`docs/shannon/shannon-mcmillan-breiman-phase-c-plan.md`](shannon/shannon-mcmillan-breiman-phase-c-plan.md) §11 判断ログ。要点:
  - `Submartingale.ae_tendsto_limitProcess` は `M_n` の収束を `limitProcess f μ` に与えるが、Birkhoff が要する `M_n / n → 0` は別物 — 直接適用不能。
  - Mathlib に reversed/backward martingale 収束定理 (Lalley 標準証明の中核) は **不在**。
  - `Probability/StrongLaw.lean` は **独立変数** 前提で ergodic 過程に流用不能。
  - 推奨経路: 別 deferred 切り出し — **`E-8''` Birkhoff a.s. 自前** (backward martingale 自前 ~400-600 行 / Mathlib PR 候補) + **`E-8'` を Birkhoff 仮説形 SMB に弱体化** (Phase D 本体 `~150-200 行`、Cover-Thomas 16.8 仮説形で主目的達成)。

  **E-8' weakened (sandwich 形 + 期待値 bridge) ✅ (2026-05-14)** → `Common2026/Shannon/ShannonMcMillanBreiman.lean` (179 行、0 sorry / 0 warning):
  - `blockLogAvg μ p n ω := -(1/n) * log P_n({block_n ω})` 定義 + `measurable_blockLogAvg`
  - **`shannon_mcmillan_breiman_of_sandwich`** (Phase D wrapper): Cover-Thomas 16.8 の **`liminf ≥ entropyRate` + `limsup ≤ entropyRate` + 有界性 4 仮説** から `Tendsto blockLogAvg n → entropyRate` a.s. を `filter_upwards` + `tendsto_of_le_liminf_of_limsup_le` で 3 行 derive。Birkhoff (E-8'') が完成したら 4 仮説を全て供給して仮定なし形に昇格できる正面 wrapper。
  - **`expected_blockLogAvg_eq`** (期待値 sanity): `∫ ω, blockLogAvg μ p n ω ∂μ = blockEntropy μ p n / n` を `integral_map` + `integral_fintype` + `Real.negMulLog` rewrite + `ring` で。Birkhoff 不要、Phase B `entropy` 定義との bridge。
  - **`tendsto_expected_blockLogAvg`**: 期待値レベル SMB `Tendsto (∫ blockLogAvg μ p n) atTop (𝓝 (entropyRate μ p))`、`entropyRate_exists_of_stationary` 経由 8 行。a.s. レベルが Phase C を必要とする部分。

- **E-9. Differential entropy + Gaussian max-entropy** ✅ (2026-05-13) →
  [docs/shannon/differential-entropy-plan.md](shannon/differential-entropy-plan.md) —
  Cover-Thomas 8.1, 8.6.1, 9.6。`Common2026/Shannon/DifferentialEntropy.lean` (1010 行、
  13 declarations、0 sorry / 0 warning) で **Phase A-E 全段完了**:
  - Phase A: `differentialEntropy μ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume`
    + `differentialEntropy_eq_integral_density` + `integrable_density_log_density_of_gaussian` +
    `differentialEntropy_dirac` (縮退ケース)
  - Phase B: `differentialEntropy_map_add_const` (translation invariance) +
    `differentialEntropy_map_mul_const` (`+ Real.log |c|`) + `differentialEntropy_map_affine`
  - Phase C: `differentialEntropy_gaussianReal`: `h(𝒩(m,v)) = (1/2) log(2πev)` + std corollary
  - Phase D: `differentialEntropy_le_gaussian_of_variance_le` (max-entropy 主定理) +
    `differentialEntropy_eq_gaussian_iff` (等号条件、`klDiv_eq_zero_iff` 経由)
  - Phase E: `klDiv_gaussianReal_gaussianReal_eq` + std sanity

  **Mathlib 新規補題ゼロ**: `integral_rnDeriv_smul` + `Measure.rnDeriv_mul_rnDeriv` +
  `gaussianReal_absolutelyContinuous'` + `variance_fun_id_gaussianReal` + `klDiv_eq_zero_iff`
  の既存組合せのみ。Phase D の signature には `h_var_int : Integrable ((x-m)²) μ` +
  `h_ent_int : Integrable (negMulLog ((rnDeriv vol)).toReal) volume` の 2 副仮説を追加
  (Bochner 慣習で `h(μ)` 病的拡張回避)。**現プロジェクトの discrete 一辺倒からの最大の枝分かれ
  突破**、Gaussian channel capacity (Cover-Thomas 9.1) への入り口開通。
  **scope-deferred**: Gaussian channel capacity + EPI は別 seed/plan (~1000 行 / ~2000 行)。

- **E-10. DMC capacity is unchanged by feedback (C_FB = C)** ✅ (2026-05-13, **chain rule 段 + per-letter hypothesis MVP**) →
  [docs/shannon/dmc-feedback-capacity-plan.md](shannon/dmc-feedback-capacity-plan.md) —
  Cover-Thomas 7.12。`Common2026/Shannon/ChannelCodingFeedback.lean` (297 行) で
  feedback 下 channel coding converse の **chain rule 段** を 0 sorry で publish:
  - `FeedbackCode M n α β`: 因果的 feedback 符号 (`encoder : ∀ i : Fin n, Fin M → (Fin i.val → β) → α`、
    type signature レベルで因果性を強制)
  - `FeedbackCode.ofCode`: 標準 `Code` の埋め込み (`C_FB ≥ C` achievability trivial 系)
  - `mutualInfo_chain_rule_Y_axis_fin`: Y 軸 n 変数 chain rule
    (`mutualInfo_chain_rule_fin` X 軸 + `mutualInfo_comm` + `condMutualInfo_comm` 合成)
  - `channel_coding_feedback_converse_chain` + `_capacity`: per-letter bound
    `h_per_letter : I(M; Y_i | Y^{<i}) ≤ I(X_i; Y_i)` を **仮説** に取った合成形
  - `channel_coding_feedback_converse`: 主定理 `log|M| ≤ n · C + h(Pe) + Pe · log(|M|−1)`
    (h_per_letter + per-letter cap 仮説 + Fano)

  **`h_per_letter` の pure proof** (memoryless ⇒ `Y_i ⊥ (M, Y^{<i}) | X_i` の condDistrib equality 経由)
  は **E-10' deferred** (~500 行、Mathlib `CondMutualInfo.lean` に condDistrib 展開補題追加要)。
  D-2 (channel coding general converse) と組み合わせると "feedback も使えない" が出る。

- **E-10'. Feedback converse per-letter bound (`I(M; Y_i | Y^{<i}) ≤ I(X_i; Y_i)`)** ✅ (2026-05-14) →
  [docs/shannon/dmc-feedback-per-letter-bound-plan.md](shannon/dmc-feedback-per-letter-bound-plan.md) —
  `Common2026/Shannon/ChannelCodingFeedbackComplete.lean` (198 行、0 sorry / 0 warning):
  - `IsMemorylessFeedback μ Msg Xs Ys := ∀ i, IsMarkovChain μ (Y^{<i}, Msg) X_i Y_i`
    (γ-form Markov、kernel W への参照なし)
  - `feedback_per_letter_bound`: per-letter 不等式の純粋証明
  - `channel_coding_feedback_converse_memoryless`: E-10 主定理を `h_per_letter` 仮説抜き完全形で

  **証明合成 (Plan 見積 280-400 行を 50% 削減で 198 行)**: `mutualInfo_le_of_markov` 1 段
  (`(Y^{<i}, Msg) → X_i → Y_i` Markov ⟹ `I((Y^{<i}, Msg); Y_i) ≤ I(X_i; Y_i)`) + `mutualInfo_chain_rule`
  (LHS を `I(Y^{<i}; Y_i) + I(Msg; Y_i | Y^{<i})` に展開) + `mutualInfo_nonneg` (`I(Y^{<i}; Y_i) ≥ 0`)
  の 3 段合成。**CondMutualInfo.lean 新規補題 0 行**。

  **shape-driven 設計判断**: Phase A の RV 順を `(Y^{<i}, Msg)` (chain rule LHS の `(Zc, Xs)` と一致)
  に揃えたことで Step 3 swap が 0 行に。CLAUDE.md "Mathlib-shape-driven Definitions" 原則の体現。

  **横断 utility**: D-2 (channel coding general-input converse) の deferred bullet D-2'
  (memoryless per-summand bound `I(X_i; Y^n | X^{<i}) ≤ I(X_i; Y_i)`) と同型の Markov reformulation
  経路が転用可能。Cover-Thomas 7.12 が `h_per_letter` 仮説を剥がした完全形で完走。

### 横断観察 (E 節シード間)

- **E-2 / E-6 / E-7 先行 utility 3 本完了** (2026-05-13): 軽中量 (~480–700 行) のこの 3 本は単独で publish 価値を持ちつつ、後続 (E-1 / E-3 / E-5) の前段補題として直接効く。順序最適化: ✅ E-2 → ✅ E-7 → ✅ E-6 → ✅ E-1 → ✅ E-5 (退化点 MVP) → E-3 → E-4 → E-5' (full rate region)。
  - E-2 (type-class lower bound) は Sanov LDP equality (`SanovLDPEquality.lean`) の Stein 経由を**直接経路に置き換える**機会で、横断改善 C と同質の整理効果。
  - E-7 (strong typicality) は E-1 (channel coding strong converse) と E-5 (Slepian–Wolf achievability) の **共通前段**。両方を予定するなら E-7 単独 plan を独立に切る方がトータル短い (B-7 → B-3 の前例)。
  - E-6 (Csiszár I-projection) 完了時の知見: **Mathlib `strictConvexOn_klFun` が既存**で、`PinskerSharp.lean` `klFun_sharp_lower` の ConvexOn refactor は**不要**だった。`stdSimplex ℝ α` (Mathlib) + `klDivPmf : (α → ℝ) → (α → ℝ) → ℝ` 直接定義で `Measure α` plumbing 全て回避、`klDivPmf_eq_log_diff_sum` (`∑ P (log P - log Q)` 形) は Sanov `klDivSumForm` と shape 一致、`Sanov.klDivSumForm_eq_toReal_klDiv` 同型の post-bridge で `(klDiv P Q).toReal` 形にも橋渡し可能 (scope-deferred)。
- **E-5 退化点 MVP commit + E-5' deferred** (2026-05-13): Cover-Thomas 15.4 完全形 (3-bound rate region full `R_X > H(X|Y), R_Y > H(Y|X), R_X + R_Y > H(X, Y)`) は random binning + joint typicality decoder で **~2000 行規模** (`binningMeasure : Measure (α^n → Fin M_X)` Fubini machinery + conditional typical slice size bound + 4-term error decomposition + pigeonhole)。E-5 では **2 corner-point MVP** (`(log|α|, R_Y>H(Y))` + `(R_X>H(X), log|β|)`) を `source_coding_achievability` + 自明 encoder 合成で publish (310 行)、full rate region は **E-5' deferred** 後継カードに切り出し。**ChannelCodingAchievability の codebookMeasure 機構** (Phase C-(c) `random_codebook_average_le` の `Measure.pi` over `Fin M` × `Fin n` Fubini-collapse) は E-5' で **encoder-side 鏡像** (`Measure.pi` over `α^n` × `Fin M_X`) として転用可能、bin index の uniform 抽選 = codeword index 順列の本質的鏡像。E-5' 起草時はこの **mechanism reuse 観点** を判断ログに記録。
- **強形/弱形ペア 4 種**: E-1 単発形 (2026-05-13 完了) で **Wolfowitz 鍵不等式** (`1 - Pe ≤ exp γ + (1/M) ∑_m P_m^n(highLLR_m)`) の Lean 化は達成。`Pe → 1` asymptotic 段 (WLLN-on-LLR 接続) は scope-deferred、D-1 (capacity 到達 achievability 強形) と pair で次の着手候補。両者を同時に組むと n-channel 設備 (`mutualInfo_iid_eq_nsmul`) + `IIDProductInput` ambient + `strong_law_ae_real` を共有して効率的。Pinsker (弱 B-5 / 強 B-5') / Stein (弱 + 強 B-4) / Sanov (A 形 B-1 + LDP B-1'/B-1'') の 3 ペアは弱形/強形共に完結済み。
- **discrete → continuous の最大ジャンプ (E-9)**: 現状 42 本中 0 本が微分エントロピーに触れていない。Mathlib `MeasureTheory.gaussianReal` 整備度は読み込み未確認、Mathlib に `differentialEntropy` 自体が存在しないため**新規 Mathlib 上流 PR の母体**になりやすい。E-9 単独 publish → Gaussian channel capacity (将来 seed) → EPI (Cover-Thomas 17、将来 seed) の **3 段ロケット**で discrete 集から脱却。
- **E-3 の機構流用 (Channel coding probabilistic-method)**: `ChannelCodingAchievability.lean` の `codebookMeasure` + `codebook_marginal_*` Fubini-collapse 補題群は **lossy source code の rate-distortion (E-3)** に **そのまま**転用可能 (codebook 上の random selection は同じ構造)。E-3 plan 起草時は plumbing を library 化 (`Common2026/Shannon/RandomCodebookProbMethod.lean` 抽出) するか直接 import するか方針判断。

---

## 参照

- 既存 plan:
  - [Fano moonshot](fano/fano-moonshot-plan.md)
  - [Shannon moonshot](shannon/shannon-moonshot-plan.md)
  - [Shannon encoder extensions](shannon/shannon-encoder-extensions-plan.md)
  - [Han moonshot](han/han-moonshot-plan.md)
  - [Han Phase D (subset average / Shearer)](han/han-phase-d-plan.md)
- 5 シード plan + deferred (2026-05-10 / 2026-05-11、全て完了):
  - [Loomis–Whitney moonshot](shannon/loomis-whitney-moonshot-plan.md) ✅
  - [Slepian–Wolf moonshot](shannon/slepian-wolf-moonshot-plan.md) ✅
  - [AEP moonshot](shannon/aep-moonshot-plan.md) ✅ (Phase A〜C)
  - [AEP source coding (Phase D)](shannon/aep-source-coding-plan.md) ✅
  - [AEP achievability (Phase E)](shannon/aep-achievability-plan.md) ✅
  - [Stein moonshot](shannon/stein-moonshot-plan.md) ✅ (Phase A〜B achievability)
  - [Stein converse (Phase A〜C)](shannon/stein-converse-plan.md) ✅
  - [Polymatroid moonshot](han/polymatroid-moonshot-plan.md) ✅ (Phase A〜C)
  - [Polymatroid structure (Phase D)](han/polymatroid-structure-plan.md) ✅
  - [HanD Pi refactor](han/hand-pi-refactor-plan.md) ✅
  - [Max Entropy moonshot (B-6)](shannon/max-entropy-moonshot-plan.md) ✅
  - [Pinsker moonshot (B-5)](shannon/pinsker-moonshot-plan.md) ✅ (弱形 `TV ≤ √KL`)
  - [Pinsker sharp moonshot (B-5')](shannon/pinsker-sharp-moonshot-plan.md) ✅ (シャープ形 `TV ≤ √(KL/2)`)
  - [Shearer cover bundle (B-2 + B-9)](shannon/shearer-cover-bundle-plan.md) ✅
  - [Hypercube edge-boundary (B-2')](shannon/hypercube-edge-boundary-plan.md) ✅ (Han-Bregman AM-GM 形)
  - [Hypercube edge-boundary entropy-sharp (B-2'')](shannon/hypercube-edge-boundary-sharp-plan.md) ✅ (`|∂_e A| ≥ |A|(n − log₂ |A|)`)
  - [MI chain rule (B-7)](shannon/mi-chain-rule-moonshot-plan.md) ✅
  - [Channel coding achievability (B-3)](shannon/channel-coding-achievability-plan.md) ✅ (Phase A + Phase B)
  - [Channel coding Phase C+D (B-3'')](shannon/channel-coding-phase-cd-plan.md) ✅ (Phase C-(a)-(d) + D-(a)-(b) 全段、`channel_coding_achievability` Cover-Thomas 7.7.1 半分)
  - [Sanov moonshot (B-1)](shannon/sanov-moonshot-plan.md) ✅ (A 形 `Q^n(T(P)) ≤ exp(-n·D)`)
  - [Sanov LDP B 形 (B-1')](shannon/sanov-ldp-b-plan.md) ✅ (upper bound `(1/n) log Q^n ≤ -inf D + ε` eventually)
  - [Sanov LDP equality 形 (B-1'')](shannon/sanov-ldp-equality-plan.md) ✅ (`Tendsto (1/n) log Q^n → -inf D` 双方向、`klDivSumForm_ofVec` 経由で Mathlib gap 回避)
  - [Strong Stein moonshot (B-4)](shannon/strong-stein-moonshot-plan.md) ✅ (`Tendsto → K` strict)
  - [Shannon code moonshot (B-8)](shannon/shannon-code-moonshot-plan.md) ✅ (期待長 sandwich、語長水準)
  - [Shannon code Kraft 逆向き (B-8')](shannon/shannon-code-kraft-reverse-plan.md) ✅ (prefix code 存在構成、Shannon-Fano D-進数)
  - [AEP 完全形 (D-3)](shannon/aep-full-form-plan.md) ✅ (Cover-Thomas 3.1.2 完全 4 帰結、`typicalSet_prob_ge` + `typicalSet_card_ge` + eventually-N corollary)
  - [Type-class size lower bound (E-2)](shannon/type-class-lower-bound-plan.md) ✅ (Cover-Thomas 11.1.3 size 下界 entropy 形、`typeClassByCount_card_ge_entropy` via bridge `n^n / ∏ c^c = exp(n·H(c/n))`)
  - [Strong typicality (E-7)](shannon/strong-typicality-plan.md) ✅ (Cover-Thomas 11.2 3 主定理、per-letter form + Strong→Weak bridge)
  - [Csiszár I-projection (E-6)](shannon/csiszar-projection-plan.md) ✅ (Cover-Thomas 11.6.1 存在 + 一意性 + Pythagorean 不等式、stdSimplex 上 `klDivPmf` 形 + Mathlib `strictConvexOn_klFun` 直接利用)
  - [Channel coding strong converse (E-1)](shannon/channel-coding-strong-converse-plan.md) ✅ (Cover-Thomas 7.9 / Verdú-Han 単発形、任意 deterministic code + 任意 reference Q^n で `1 - Pe ≤ exp γ + (1/M) ∑_m P_m^n(highLLR_m)`、asymptotic Pe → 1 段は scope-deferred)
  - [Slepian–Wolf achievability (E-5 退化点 MVP)](shannon/slepian-wolf-achievability-plan.md) ✅ (Cover-Thomas 15.4 2 corner-point 達成可能性、`slepian_wolf_achievability_corner_Y` rate `(log|α|, R_Y>H(Y))` + `_corner_X` rate `(R_X>H(X), log|β|)` を `source_coding_achievability` + 自明 encoder 合成で構築、3-bound full rate region は random binning ~2000 行規模で E-5' deferred)
  - [Channel coding general-input converse (D-2 chain rule MVP)](shannon/channel-coding-converse-general-plan.md) ✅ (Cover-Thomas 7.9、iid 仮定撤廃 + chain rule 分解段、`log|M| ≤ ∑_i I(X_i; Y^n | X^{<i}).toReal + Fano`、`shannon_converse_single_shot_markov_encoder` + `mutualInfo_chain_rule_fin` 合成、per-summand memoryless reduction は D-2' deferred)
  - [Rate-distortion converse (E-4 single-shot MVP)](shannon/rate-distortion-converse-plan.md) ✅ (Cover-Thomas 10.4、`rateDistortionFunction d P D := ⨅ ν _ _, klDiv ν (P × ν.snd)` shape-driven 定義 + 単発形 `R(D̃).toReal ≤ log|M|`、`MaxEntropy.entropy_le_log_card` + DPI + Bridge + `iInf_le` 4-step chain、n-letter form は E-4' deferred)
  - [DMC feedback capacity converse (E-10 chain rule MVP)](shannon/dmc-feedback-capacity-plan.md) ✅ (Cover-Thomas 7.12、`FeedbackCode` 因果的 encoder + Y 軸 chain rule (`mutualInfo_chain_rule_Y_axis_fin`) + per-letter `h_per_letter` 仮説形 + Fano、主定理 `log|M| ≤ n·C + Fano`、per-letter pure proof は E-10' deferred)
- 起草中 plan (2026-05-13、実装未着手):
  - [Channel coding theorem D-1](shannon/channel-coding-shannon-theorem-plan.md) 🚧 (Cover-Thomas 7.7.1 完全形、capacity + expurgation + full support 緩和、~700 行見込み)
  - [Rate-distortion achievability E-3](shannon/rate-distortion-achievability-plan.md) 🚧 (Cover-Thomas 10.5、random codebook + joint typical encoder lossy mirror、`ChannelCodingAchievability.codebookMeasure` 流用、~1980 行見込み)
  - [Slepian–Wolf full rate region E-5'](shannon/slepian-wolf-full-rate-region-plan.md) 🚧 (Cover-Thomas 15.4 完全形 3-bound rate region、random binning + joint typicality decoder、~1900-2010 行見込み)
  - [Shannon–McMillan–Breiman E-8](shannon/shannon-mcmillan-breiman-plan.md) 🚧 (Cover-Thomas 16.8 定常エルゴード AEP、Mathlib Birkhoff a.s. 不在のため自前実装含め ~1500 行、Phase C.5 最大リスク)
  - [Differential entropy + Gaussian max-entropy E-9](shannon/differential-entropy-plan.md) 🚧 (Cover-Thomas 8.1/8.6.1/9.6、Mathlib `gaussianReal` 完備で Phase A-D 直接実装可、~1500 行 + Mathlib 上流 PR 3 件母体)
- 雛形:
  - [moonshot-plan-template.md](moonshot-plan-template.md)
  - [subplan-template.md](subplan-template.md)
