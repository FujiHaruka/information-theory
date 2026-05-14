# Moonshot シードカード集

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
  - ⏸️ `condMutualInfo_map_right_measurableEquiv` (Z reshape) — deferred (~150 行と見積、
    `condDistrib_ae_eq_of_measure_eq_compProd` + `Kernel.comap` plumbing)。
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
  **`E-4''C`** deferred: n-letter 規定歪み形 converse (`MIChainRule.mutualInfo_pi_eq_sum`
  + Phase B 凸性 + Jensen 1/n 平均) ~300-500 行。

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

### B. 新シード入口 (5 シード完了で開いた)

- **Sanov の定理** ✅ (A 形 2026-05-12) → [docs/shannon/sanov-moonshot-plan.md](shannon/sanov-moonshot-plan.md) — `typeClass_Qn_le` / `typeClass_Qn_le_klDiv`: 有限アルファベット上で `Q^n(T(P)) ≤ exp(-n · klDivSumForm P Q)` (Cover-Thomas 11.1.4)。`klDivSumForm` 形と `(klDiv P Q).toReal` 形両方を publish。`Common2026/Shannon/Sanov.lean` (319 行)。Stein converse `steinTypicalSet_Q_prob_le` の特化 (片側 inequality → 両側 equality) で多項係数 / `|T(P)| ≤ exp(n·H(P))` を回避。
- **B-1'. Sanov LDP B 形 upper bound** ✅ (2026-05-12) → [docs/shannon/sanov-ldp-b-plan.md](shannon/sanov-ldp-b-plan.md) — `sanov_ldp_upper_bound`: 任意 `E : ∀ n, Finset (TypeCountIndex α n)` で各 `c ∈ E n` が `D ≤ klDivIndex c n Q` を満たすとき、任意 `ε > 0` で eventually `(1/n) log Q^n(⋃ c ∈ E n, typeClassByCount c) ≤ -D + ε` (Cover-Thomas Theorem 11.4.1 main statement)。`Common2026/Shannon/SanovLDP.lean` (550 行)。`TypeCountIndex α n := α → Fin (n+1)` で polynomial bound `|·| = (n+1)^|α|`、`typeClassByCount_Qn_le` (index 形 A、A 形 `typeClass_Qn_le` の Stein 経路書き直し)、`typeClassByCount_union_Qn_le_inf` (union 形)、`log_succ_div_tendsto_zero` (`Real.isLittleO_log_id_atTop` 経由) を経由。多項係数 `Nat.multinomial` 経路は不採用、A 形と整合 (`c (x_i) ≥ 1` 観察で `hPpos` 仮定回避)。**LDP equality 形** (`lim (1/n) log Q^n = -inf D` の双方向) は **B-1'' で完了** (2026-05-12、行 `B-1''` 参照)。
- **B-2. Hypercube edge isoperimetry / Han-Bregman bound** ✅ (singleton-cover 形) → [docs/shannon/shearer-cover-bundle-plan.md](shannon/shearer-cover-bundle-plan.md) — `hypercube_product_projection_bound`: 任意 `A ⊆ α^n` (`A.Nonempty`) で `|A| ≤ ∏ i, |π_{{i}}(A)|`。Brascamp–Lieb の `S i := {i}` / `k := 1` 特殊形として Phase C corollary。
- **B-2'. Hypercube edge-boundary 形 (Han-Bregman AM-GM 形)** ✅ (2026-05-12) → [docs/shannon/hypercube-edge-boundary-plan.md](shannon/hypercube-edge-boundary-plan.md) — Boolean cube `Fin n → Bool` 上の coordinate-flip pair で `edgeBoundaryCount A` を直接定義 (Mathlib `SimpleGraph.edgeBoundary` 既存なく `Sym2` 回避)。`Common2026/Shannon/HypercubeEdgeBoundary.lean` (692 行)。主結果 `edgeBoundary_ge_AMGM`: `A.Nonempty` のもとで `2n · |A|^{(n-1)/n} ≤ |∂_e A| + n · |A|` (ℝ, 整数差を `+` で回避)。鍵 counting identity `edgeBoundary_count_eq`: `|∂_e A| + n |A| = 2 Σ_i |π_{≠i}(A)|` を, 各 `i` での fibre size ∈ {1,2} 分類 (`Finset.card_eq_sum_card_fiberwise`) + 4-case 結合 (membership of two extensions in `A`) で proof。Phase B は LW (`loomis_whitney`) + AM-GM (`Real.geom_mean_le_arith_mean_weighted` + `Real.finsetProd_rpow`) の corollary。entropy-sharp 形 (`|∂_e A| ≥ |A|(n - log₂ |A|)`) は **B-2'' で完了** (2026-05-12、行 `B-2''` 参照)。`SimpleGraph` 構造 + `boxProd` n-fold は本 plan で **持ち込まず**, 上流 Mathlib PR (Boolean cube as `K_2 □ K_2 □ ...`) に分離可能。
- **Channel coding theorem (achievability)** ✅ (2026-05-12 完全閉鎖、Phase A〜D 全段) → [docs/shannon/channel-coding-achievability-plan.md](shannon/channel-coding-achievability-plan.md) + [docs/shannon/channel-coding-phase-cd-plan.md](shannon/channel-coding-phase-cd-plan.md) — DMC = `Kernel α β` (alias) + `Code` structure + `errorProb` / `averageErrorProb` / `mutualInfoOfChannel` を Phase A で publish。Phase B-(a, b, c) 全 3 bound 完了。**B-3'' (Phase C+D)**: `Common2026/Shannon/ChannelCodingAchievability.lean` (1890 行) で Phase C-(b) `errorProbAt_le_E1_plus_E2` + Phase C-(c) `random_codebook_average_le` (probabilistic-method 形、`codebookMeasure p M n := Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => p))` + 仮説 `h_match_X` / `h_match_Z` / `hindepZ_full` で abstract ambient と codebook law を coupling、内部で `codebook_marginal_one` / `codebook_marginal_two` Fubini-collapse 補題経由) + Phase C-(d) `exists_codebook_le_avg` (probabilistic-method 形 pigeonhole) + Phase D-(b) 主定理 `channel_coding_achievability` (Cover-Thomas Theorem 7.7.1 achievability 半分) を **すべて 0 sorry** で publish。precursor として `Common2026/Shannon/IIDProductInput.lean` (399 行、`Ω := ℕ → α × β` 上の `Measure.infinitePi (jointDistribution p W)` i.i.d. ambient bundle を ready-made instance として publish) と entropy-MI bridge (`MIChainRule.lean` + `ChannelCoding.lean` 拡張で `mutualInfoOfChannel_eq_HX_add_HY_sub_HZ` を publish) を新規追加。channel positivity 仮説 `∀ a y, 0 < (W a).real {y}` を主定理 signature に追加。Phase B 全 3 bound は Slepian-Wolf strong typicality 派生に **単独で再利用可能**。
- **Strong Stein** ✅ (2026-05-12) → [docs/shannon/strong-stein-moonshot-plan.md](shannon/strong-stein-moonshot-plan.md) — `stein_strong_lemma`: 任意 `ε ∈ (0,1)` で `Tendsto (-(1/n) * log (steinOptimalBeta P Q n ε)) atTop (𝓝 (klDiv P Q).toReal)`。`Common2026/Shannon/StrongStein.lean` (641 行)。Pinsker / Sanov / information spectrum を **どれも使わず**、既存 `stein_inProbability` (WLLN on LLR) + `steinTypicalSet` plumbing 上に **LLR-typicality (上側)** 経路で構築。鍵: 既存 `steinTypicalSet_Q_prob_le` (LLR 下側で `Q^n(T) ≤ exp(-n(K-δ))`) の **symmetric 対形** `steinTypicalSet_Q_prob_ge` (LLR 上側で `Q^n(T) ≥ exp(-n(K+δ)) · P^n(T)`) を新規構築 → 任意 α-level test に `s ∩ T` 経由で集合論的に延長 → `inf_s` で `steinOptimalBeta` の lower bound → log + 1/n + δ → 0 で `limsup ≤ K`、既存 achievability で `liminf ≥ K`、`tendsto_of_le_liminf_of_limsup_le` で締める。既存 `stein_lemma` (sandwich) は維持、新 file 並立で downstream 影響なし。

### B 追加 (2026-05-11 起草、既存 5 シード + B-1〜B-4 を踏まえた後続)

- **B-5. Pinsker 不等式** ✅ (弱形) → [docs/shannon/pinsker-moonshot-plan.md](shannon/pinsker-moonshot-plan.md) — Bretagnolle-Huber 経路で `tvNorm P Q ≤ √(klDiv P Q).toReal` (定数 1、シャープ Pinsker の定数 1/√2 の √2 倍ゆるい)。有限 alphabet 上で `tvNorm` を新規定義 + `klFun_ge_sub_sqrt_sq` 点別補題 + Cauchy-Schwarz on `|p-q|=|√p-√q|·(√p+√q)`。310 行。
- **B-5'. シャープ Pinsker 不等式** ✅ (2026-05-12) → [docs/shannon/pinsker-sharp-moonshot-plan.md](shannon/pinsker-sharp-moonshot-plan.md) — `tvNorm_le_sqrt_klDiv_div_two`: 有限 alphabet 上で `tvNorm P Q ≤ √((klDiv P Q).toReal / 2)` (Cover-Thomas 11.6 strict 形、定数 1/√2)。`Common2026/Shannon/PinskerSharp.lean` (429 行) を新規追加、弱形 (`Pinsker.lean`) は touch せず並立 publish (`tvNorm` 定義は共有)。鍵は点別 `klFun_sharp_lower`: `3·(t-1)² ≤ 2·(t+2)·klFun(t)` for `t ≥ 0` を **`H(t) := 2(t+2)·klFun(t) - 3(t-1)²` の 3 段微分サインチェイン** (`H''(t) = 4(log t + 1/t - 1) ≥ 0` を `Real.one_sub_inv_le_log_of_pos` 一行で潰す → `H'(1)=0` と `MonotoneOn` で `H'` sign-change at `t=1` → `H(1)=0` と双方向 monotone/antitone で `H ≥ 0` on `(0, ∞)`、`t=0` は別途)。Phase B は per-element `q · klFun(p/q) ≥ 3(p-q)²/(2(p+2q))` + Cauchy-Schwarz on `r := |p-q|`, `f := (p-q)²/(p+2q)`, `g := p+2q` で `(2 TV)² ≤ 3 · Σ f ≤ 2 · KL` を取り、`Σ g = 1 + 2 = 3` を使用。Mathlib に sharp bound 既存なく独立 PR 候補。
- **B-6. 最大エントロピー** ✅ → [docs/shannon/max-entropy-moonshot-plan.md](shannon/max-entropy-moonshot-plan.md) (有限アルファベット上の Gibbs 不等式): `entropy μ X ≤ Real.log (Fintype.card α)`、等号 iff `μ.map X` 一様。Mathlib `klDiv_eq_zero_iff` + identity `klDiv P (uniform) = log|α| - H(P)` だけで終わる軽量シード。LoomisWhitney の `entropy_le_log_image_card` (uniformOn-specific) の **一般 measure 版** で、Shannon converse・LoomisWhitney 両方で暗黙に効いている identity を独立補題として publish。Cover-Thomas 2.6.4。見積 2〜3 日 / 50〜100 行 / 低リスク。**最軽量シード**、Pinsker / Sanov の前段補題としても再利用可。
- **B-7. 相互情報量 chain rule** ✅ → [docs/shannon/mi-chain-rule-moonshot-plan.md](shannon/mi-chain-rule-moonshot-plan.md) — `mutualInfo_chain_rule_fin`: `I(X_0, …, X_{n-1}; Y) = ∑ I(X_i; Y | X_{<i})` の n 変数 chain rule + `mutualInfo_iid_eq_nsmul`: 独立同分布 (Xs, Ys) で `I(X^n; Y^n) = n · I(X_0; Y_0)` (B-3 用 corollary)。Phase A (`mutualInfo` の MeasurableEquiv reshape 不変性、`mutualInfo_map_left/right_measurableEquiv`) + Phase B (Han Phase B と対称な induction、既存 2 変数 `mutualInfo_chain_rule` + `MeasurableEquiv.piFinSuccAbove` + prodComm reshape + `Fin.sum_univ_castSucc`) + Phase C (chain rule 経由ではなく `klDiv_compProd_eq_add` + `measurePreserving_arrowProdEquivProdArrow` で直接 product joint 加法性 + 新規補題 `klDiv_pi_eq_sum`) で 418 行。`Common2026/Shannon/MIChainRule.lean` 新規。B-3 (Channel coding achievability) の前段補題として publish 済。
- **B-8. Shannon コード** ✅ (期待長 sandwich、語長水準) → [docs/shannon/shannon-code-moonshot-plan.md](shannon/shannon-code-moonshot-plan.md) — `shannonCode_expected_length_bounds`: 有限アルファベット上の確率測度 `P` (full support) で、Shannon 語長 `l(a) := ⌈-logb D P(a)⌉₊` が `H_D(P) ≤ E[L_Shannon] < H_D(P) + 1` を達成 (Cover-Thomas 5.4 + 5.8.1)。`Common2026/Shannon/ShannonCode.lean` (354 行)。Phase A 定義 (`entropyD` / `shannonLength` / `expectedLength` / `kraftSum`) + Phase B Kraft 充足 (`shannonLength_kraft_le_one`: 各 `a` で `D^{-l(a)} ≤ P(a)` から Σ ≤ 1) + Phase C Gibbs 下界 (`entropyD_le_expectedLength_of_kraft`: 任意 lengths が Kraft 充足 ⟹ `H_D ≤ E[L]`、`Real.log_le_sub_one_of_pos` 経路で Jensen 回避) + Phase D Shannon 上界 (`expectedLength_shannon_lt_entropyD_add_one`: `Nat.ceil_lt_add_one` で `l(a) < -logb P(a) + 1` を Σ) + Phase E sandwich の 5 段。**Kraft 逆向きは B-8' で別 plan として完了** (下参照)。Mathlib `kraft_mcmillan_inequality` (UD code → Σ D^{-|w|} ≤ 1) は **本シードで直接呼ばず** Shannon 語長の Kraft 充足を独立に証明 (下界に十分)。block source coding theorem (既存 `source_coding_theorem`、AEP Phase F) の **per-symbol 相補形**。
- **B-8'. Shannon コード Kraft 逆向き (prefix code 存在構成)** ✅ (2026-05-12) → [docs/shannon/shannon-code-kraft-reverse-plan.md](shannon/shannon-code-kraft-reverse-plan.md) — `exists_prefix_code_of_kraft`: 任意の `l : α → ℕ` (`∀ a, 0 < l a`) が Kraft 不等式 `Σ_a D^{-l(a)} ≤ 1` (`D ≥ 2`) を充足するとき、長さ `l(a)` の prefix code (injective + prefix-free) が存在 (Cover-Thomas 5.2.1 reverse / McMillan の逆形)。`Common2026/Shannon/ShannonCodeKraftReverse.lean` (498 行)。**Shannon-Fano D-進数構成**を採用 (Greedy with state 不採用): `List.mergeSort` で sort-by-length → 累積和 `slotStart k := Σ_{j<k} D^(L - l(as[j]))` → 各 code-word を `toBaseDLen D (l a) (slot/D^(L-l a))` で定義 (`toBaseDLen` は自前の MSB-first 固定長 base-`D` エンコーダ、Mathlib `Nat.digits` は LSB-first / 可変長で不向き)。Kraft 充足 ⟹ `slotStart |α| ≤ D^L`、prefix-free は `slotStart` の累積 gap + `toBaseDLen_injOn_lt` (digit-by-digit 帰納 with `Nat.mod_pow_succ`) で。Mathlib に prefix code 構造体は **無く** (`UniquelyDecodable` + `kraft_mcmillan_inequality` のみ)、独立 implementation。B-8 (`ShannonCode.lean` 354 行) は touch せず並立 publish。`toBaseDLen` と核補題 (`toBaseDLen_take` / `toBaseDLen_injOn_lt`) は Mathlib 上流 PR 切り出し候補。
- **B-9. Brascamp–Lieb 不等式** ✅ (組合せ形) → [docs/shannon/shearer-cover-bundle-plan.md](shannon/shearer-cover-bundle-plan.md) — `brascamp_lieb_finset`: 任意の cover `(S_i)_{i ∈ ι} ⊆ 𝒫(Fin n)` が各 `j` を `k` 回覆うとき `|A|^k ≤ ∏ i, |π_{S_i}(A)|`。Shearer engine (`HanDShearer.shearer_inequality`) + `entropy_le_log_image_card` + `entropy_uniformOn_eq_log_card` の 3 つを **任意 cover** で並べるだけ。B-2 と engine 共有で bundle 実装、`Common2026/Shannon/BrascampLieb.lean` (198 行)。LW は `S i := univ.erase i` 特殊形だが既存 `LoomisWhitney.lean` 維持 (refactor 見送り)。

### 横断観察 (B 追加シード間)

- **Pinsker → Strong Stein のショートカット** ✅ (B-4 完了で結論 2026-05-12): Pinsker 経由は **不採用**。strong converse の `1/(1-ε)` factor は KL 値の精度ではなく現行 converse の DPI on Bool reduction 構造 (`Pn(s) * (-log Qn s) ≥ (1-ε) * (-log Qn s)`) から来るため、Pinsker `TV ≤ √KL` を使っても解消しない。代わりに **LLR-typicality (上側)** で `Q^n(s) ≥ exp(-n(K+δ)) · (P^n(T) - ε)` を直接取り、既存 `stein_inProbability` (WLLN on LLR) で `P^n(T) → 1` を渡すだけで `limsup ≤ K` が出る。Pinsker / Sanov / information spectrum **どれも不要**で完成 (641 行)。
- **B-2 + B-9 の bundle 化** ✅ (2026-05-11 完了): どちらも Shearer を「異なる cover ファミリ」で呼ぶだけ。実装結果: **`structure ShearerCover` 抽象化は不要だった** — `shearer_inequality` が既に任意 `ι`/`S`/`k` に対して汎用なため、新規定義 `projectionSubset S A` + reshape lemma 1 つ (`jointEntropySubset_le_log_projectionSubset_card`) だけで BL が書ける。LW は既存形を維持 (refactor 見送り、新規 `BrascampLieb.lean` と並立)。Hypercube は singleton cover corollary `hypercube_product_projection_bound` 形のみ提供、edge-boundary 形は **B-2' deferred** に切り出し。
- **B-7 → B-3 短縮化** ✅ (2026-05-12 B-7 完了で実証): 最大の seed B-3 (Channel coding achievability、4〜6 週) を一括着手するより、B-7 (MI chain rule) を独立 plan として先に完了 → B-3 を「jointly typical decoder + 既存 MI chain rule + i.i.d. corollary」の短縮形に再見積もる方が手戻りリスクが低い。実装: chain rule 経路 (Phase B) ≠ i.i.d. corollary 経路 (Phase C、`klDiv_pi_eq_sum` 直接) と判明、Phase C は chain rule に依存せず独立 publish した方が短い (B-3 では i.i.d. corollary 単独で十分)。

- **B-3 i.i.d. product factorization の欠落** ✅ (2026-05-12 Phase B-(c) 完了で解決): Phase B-(c) `jointlyTypicalSet_indep_prob_le` を立てる際の point-wise probability `(μ.map (jointRV Xs n)) {x} = ∏ P(x_i)` を、新規 AEP 補題 `typicalSet_prob_le` (Phase G 節、~100 行) として publish 済。`iIndepFun_iff_map_fun_eq_pi_map` + `iIndepFun.precomp Fin.val_injective` + `Measure.pi_singleton` の 3 つを順に呼ぶだけで Mathlib 既存 API のみで完了。AEP の `Pairwise IndepFun` ベースの既存補題は touch せず並立 publish。本来の見積 200-400 行は ~100 行に縮減 (Mathlib 既存 `iIndepFun_iff_map_fun_eq_pi_map` が想定より直接使えたため)。

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
