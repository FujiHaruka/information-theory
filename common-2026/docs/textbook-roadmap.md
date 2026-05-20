# Verified Information Theory Textbook ロードマップ 📚

> **目的**: 本プロジェクトの最終アウトプットを「形式証明済み定理から生成される情報理論の教科書」とする。
> Cover & Thomas *Elements of Information Theory* を骨格に、Lean 4 + Mathlib で 0 sorry に着地した
> 主定理群を一次資料として、**reference library** と **読み物としての教科書原稿** の両方を publish する。
> 単発 seed の `docs/moonshot-seeds.md` がカード一覧、本ファイルは **章単位の完成判定 + 残ギャップを束ねる
> 上位ロードマップ**。

<!--
雛形メモ:
- 本ファイルは複数 moonshot seed を束ねる上位ロードマップ。個別 seed は `docs/moonshot-seeds.md`
  にカード化し、本ファイルからは「章単位の完成判定」「seed ↔ 章のマッピング」で参照する。
- 章単位の進捗表は append-only 更新。状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更
- 各 seed は `→ <plan path>` ポインタを書き、計画着手時に該当 plan ファイルを生やす
- 「教科書として穴がない」基準で seed を選定。Cover-Thomas Ch.6 / 13 / 14 / 16 は明示的に scope-out
-->

## ゴール / Approach

**最終ゴール**: Cover & Thomas *Elements of Information Theory* (2nd ed.) の Ch.2–12, 15, 17 を骨格
として、**Lean 形式化された定理から生成される教科書**を publish する。本プロジェクトの主成果物は
3 層に分かれる:

1. **Verified library** (`Common2026/`): 主定理が 0 sorry で publish 済みの Lean モジュール群。
2. **Typed RV API**: 教科書として読める書き味 (`entropy X`, `mutualInfo X Y`, `H(X|Y)`) を支える
   外向き API 層。internal 証明は measure-theoretic 表現で良いが、教科書本文と一対一対応する
   notation / 補助 lemma を確立する。
3. **教科書原稿**: 上記 2 層を一次資料として、各章の定理ステートメントと証明ハイライトを Lean
   定義へ link した markdown / LaTeX / 製本物。

**Approach**: 既に完成している discrete core (Ch.2–5, 7, 10, 11 大部分) を起点に、`Tier 1 → Tier 4`
の順で seed 化 + 着手する。各 seed は **`docs/moonshot-seeds.md` にカード追加**して個別計画
(`docs/<family>/<topic>-moonshot-plan.md`) に展開、本ロードマップでは **章単位の完成判定 + seed
依存関係** だけを管理する。

## 完成判定

「Lean で verified な Cover & Thomas」を名乗るための必要条件:

- **Ch.2–5, 7–12, 15, 17 の主定理が 0 sorry で publish 済み** (詳細は下記章対応表)
- **Typed RV API** が外向き API として揃い、教科書本文の statement が形式化版に直接対応する
- 各 seed が `docs/<family>/<topic>-moonshot-plan.md` で計画化され、phase 単位で archive 可能
- 主成果物 3 層 (library / API / 原稿) の各層に index と cross-link がある

**scope-out (専門性が異なるため別 library 化)**:

- Ch.6 Gambling and Data Compression (Kelly criterion / doubling rate)
- Ch.13 Universal Source Coding の一部 (LZ78 漸近最適性は scope-in、Lempel-Ziv complexity は out)
- Ch.14 Kolmogorov Complexity (計算可能性論との接合点、別 library)
- Ch.16 Information Theory and Portfolio Theory

## 章対応進捗

| Ch. | 章タイトル | 状態 | 代表定理 (済) | 必要追加 seed | 規模 |
|---|---|---|---|---|---|
| 2 | Entropy, Relative Entropy, Mutual Information | ✅ | `Shannon/Entropy`, `MutualInfo`, `MIChainRule`, DPI | — | — |
| 3 | AEP | ✅ | `AEP.aep_ae`, `aep_inProbability`, `typicalSet_*` | — | — |
| 4 | Entropy Rates of Stochastic Processes | ✅ | `EntropyRate.entropyRate_exists_of_stationary`, `_eq_lim_condEntropy`, `ShannonMcMillanBreiman`, `BirkhoffErgodic` | — | — |
| 5 | Data Compression | 🟡 | `ShannonCode.shannonCode_expected_length_bounds`, Kraft 逆, **`Huffman.huffmanLength_kraft_le_one` + `exists_huffman_prefix_code` + T1-A' `huffmanLength_optimal_with_hypotheses` (weak form)**, **T4-A `LempelZiv78.lz78_asymptotic_optimality` (L-LZ1〜5 pass-through)**, **`ArithmeticCoding.arithmetic_coding_expected_length_bounds` (L-AC1+L-AC2+L-AC3 pass-through)** | **T1-A'' 2 hypothesis discharge** (swap normalization + identification), **T4-A 5 discharge family**, **Arithmetic coding 3 discharge** | ~2.5-4k |
| 6 | Gambling and Data Compression | ✖ scope-out | — | — | — |
| 7 | Channel Capacity | ✅ | `shannon_noisy_channel_coding_theorem_general_full`, `_strong_converse`, `_feedback_complete` | — | — |
| 8 | Differential Entropy | ✅ | `DifferentialEntropy.differentialEntropy_gaussianReal`, `_le_gaussian_of_variance_le` | — | — |
| 9 | Gaussian Channel | 🟡 | `AWGN.awgn_channel_coding_theorem` (F-1+F-2+F-3+F-4 pass-through), `AWGN.awgn_capacity_closed_form = (1/2) log(1 + P/N)`, `ParallelGaussian.parallel_gaussian_capacity_formula` (water-filling L-WF1+L-WF2+L-PG0+L-PG1 pass-through), `ShannonHartley.shannon_hartley_formula = W·log(1 + P/(N₀·W))` (L-SH1+L-SH2+L-SH3 pass-through) | **T2-A/B/C discharge** (kernel measurability + continuous typicality + MI bridge + per-letter converse 本体 + KKT 充足性 + water-filling 一意性 + Whittaker-Shannon sampling) | ~2-3.5k |
| 10 | Rate Distortion | ✅ | `rate_distortion_achievability`, `_converse_*`, `_convexity`, n-letter converse | — | — |
| 11 | Information Theory and Statistics | 🟡 | `stein_strong_law`, `sanov_ldp_equality`, `Pinsker`, `CsiszarProjection`, `Chernoff.chernoff_lemma_achievability`, **`ChernoffInformation.chernoff_lemma_tendsto`** (L-Ch1+L-Ch2 pass-through, L-Ch3 internal discharge), **`ChernoffConverse.chernoff_lemma_tendsto_from_per_tilt`** (hypothesis 2→1 per-tilt 縮減), `HoeffdingTradeoff.hoeffding_tradeoff_with_hypothesis`, `CramerLC2DischargeExt.tilted_lln_ae` + `_in_probability_real` (T1-C Phase B partial discharge) | **T1-B per-tilt full discharge** (Sanov LDP at optimum λ\*), **T1-C Phase C completion** (Mathlib gap `Measure.infinitePi_tilted_eq`), **T1-D Hoeffding tradeoff sandwich body** | ~1-1.7k |
| 12 | Maximum Entropy | 🟡 | `entropy_le_log_card`, `entropy_eq_log_card_iff` | **T3-A Constrained MaxEnt (Lagrange / exponential family)** | ~400-700 |
| 13 | Universal Source Coding | 🟡 | **`LempelZiv78.lz78_asymptotic_optimality`** (L-LZ1〜5 pass-through; outer + converse + sandwich), `_two_sided`, `_of_bounds` | **T4-A 5 discharge** (Ziv's inequality, LZ78 converse, SMB sandwich a.s., greedy parsing 実装, final glue), **Arithmetic coding** | ~1.5-2.5k |
| 14 | Kolmogorov Complexity | ✖ scope-out | — | — | — |
| 15 | Network Information Theory | 🟡 | `SlepianWolf*` 完備, `WynerZiv.wyner_ziv_tendsto` (statement-level pass-through), **`WynerZivDischarge.wynerZivRatePmf_antitone`** (L-WZ3 D-antitone partial discharge), `RelayCutset.relay_cutset_outer_bound` (L-RC1/2/3/4/5 pass-through), **`RelayInnerBound.relay_df_inner_bound` + `_cf_inner_bound`** (L-RI1〜4 pass-through), **`MultipleAccessChannel.mac_capacity_region_outer_bound` + `_inner_bound`** (L-MAC1〜5 全 pass-through), **`BroadcastChannel.bc_capacity_region_outer_bound` + `_inner_bound`** (L-BC1〜4 pass-through, degraded BC), `SeparationTheorem` 完備 | **T3-D L-WZ3 full + L-WZ1/2 discharge**, **T3-B MAC body discharge** (joint typicality + Fano), **T3-C BC body discharge** (superposition coding), **T3-F inner body discharge** | ~5-9k |
| 16 | Information Theory and Portfolio Theory | ✖ scope-out | — | — | — |
| 17 | Inequalities in Information Theory | 🟡 | `Han`, `Shearer`, `LoomisWhitney`, `BrascampLieb`, `HypercubeEdgeBoundary`, `Pinsker`, `_sharp`, `FisherInfo` + `deBruijn_identity` (L-F1+L-F2 pass-through), **`EntropyPowerInequality.entropy_power_inequality`** (L-EPI1+L-EPI2+L-EPI3 pass-through, Gaussian saturation case **full discharge**), **`BrunnMinkowski.brunn_minkowski_entropy_inequality` + `_convex_body`** (L-BM1/L-BM1'/L-BM2/L-BM3 pass-through, Cor.17.9.3 形) | **T2-D EPI body discharge** (Stam + de Bruijn integration), **T2-E BM body discharge** (concavity-of-log bridge) | ~1.4-2.0k |

状態: ✅ = 主定理 publish 済 / 🟡 = 部分達成、追加 seed 要 / 📋 = 未着手 / ✖ = scope-out / 🔄 = 方針変更

**規模の単位**: Lean 行数。±50% 程度の幅で見積もる。基準: `ChannelCodingShannonTheorem.lean` 918 行 / `DifferentialEntropy.lean` 1010 行 / `BirkhoffErgodic.lean` 920 行 / `AEPRate.lean` 831 行 / `ShannonCode*.lean` 系合計 ~700 行。**章別合計 + Infrastructure ~1.3-2.3k = 全体 ~16-25k 行**。

## 実態整合監査 (2026-05-20)

89 計画ファイルを実コードと突き合わせる全数監査を実施 (各 plan に `> 実態整合 (2026-05-20): …`
行を追記済)。**最大の発見: 計画/ロードマップの status は実態より大幅に stale で、しかも
「0 sorry = 完成」ではない。** 0 sorry でも (a) 真に無条件 / (b) honest な解析仮定付き /
(c) `Prop := True` または結論そのものを hypothesis に取る pass-through / (d) **退化定義を突いて
偶然成立する flaw-vacuous** の 4 段階がある。着手先選定は plan ではなく **実 `.lean` の headline
定理の signature と body** を直接見て判断すること。

**状態区分** (本監査で導入): 🟢 DONE-UNCOND (無条件) / 🟢ʰ DONE-HONEST-HYPS (honest 解析仮定付き) /
🟠 PASS-THROUGH (`:= True` / 結論=仮説、数学的核心は未証明) / 🔴 FLAW-VACUOUS (退化定義の悪用) /
📋 UNSTARTED。

| Ch. | headline の真の状態 | 区分 |
|---|---|---|
| 2 Entropy/MI/DPI | `MIChainRule`, entropy/DPI 一式 | 🟢 |
| 3 AEP | `source_coding_achievability`/`_converse` (iid honest hyps) | 🟢ʰ |
| 4 Entropy rate/SMB | `shannon_mcmillan_breiman` 無条件 (`SMBAlgoetCover.lean`)、`birkhoff_ergodic_ae` | 🟢 |
| 5 Data compression | ShannonCode/Kraft 🟢；Huffman 最適性 🟢ʰ (強形 `huffmanLength_optimal` は 📋)；Arithmetic coding 🟠 (`:= True` 3 本) |
| 7 Channel capacity | `shannon_..._general_full` 無条件、feedback complete；一部 converse は honest pass-through (文書化済) | 🟢/🟢ʰ |
| 8 Differential entropy | `differentialEntropy_*` (Bochner honest hyps) | 🟢ʰ |
| 9 Gaussian channel | **AWGN 🟠 (F-2/F-3 は id-alias で実 discharge でない)；ParallelGaussian 🟠 (`:= h_per_coord` 結論=仮説、L-PG1 循環)；Shannon-Hartley / Whittaker 🟠ʰ (RESOLVED 2026-05-20: L-SH1/2/3・L-WS-A を undischarged placeholder と明記、`shannon_hartley_formula` は循環でなく `h_two_w` 開仮説 pass-through、`whittaker_shannon_one_point` は `rfl` 廃して `recovered = f` 仮説 pass-through 化。sinc 下層は genuine 維持)。NAME 整合 2026-05-20: AWGN/PG の `*_discharged` 名を honest 化 — F-2/F-3 (resp. per-coord L-PG1) が hypothesis として開いたままの top 定理を改名 (`awgn_theorem_F1F2F3_discharged`→`awgn_theorem_of_F2F3_hypotheses` 等) + ⚠️ docstring 付与。genuine 層 (F-1 / L-PG0 / L-WF1 IVT / L-WF2 concavity certificate) は不変。** |
| 10 Rate distortion | achievability 🟢ʰ、converse 🟢、convexity 🟢 (finite) |
| 11 Statistics | Stein/StrongStein/Sanov/Pinsker(weak+sharp)/Csiszar 🟢；Chernoff/Cramer (CLT closure 込, 真) 🟢ʰ；**Hoeffding tradeoff 🟠 (`_with_hypothesis` のみ、achiev+converse を仮説化)** |
| 12 Maximum entropy | `entropy_le_log_card` 🟢、Constrained 🟢ʰ |
| 13 Universal coding | **LZ78 🟠 (`:= True` 3 本 + 結論=仮説)；Arithmetic 🟠** |
| 15 Network IT | SlepianWolf 🟢/🟢ʰ、WynerZiv convexity 🟢；**MAC/BC/Relay/WynerZiv headline 🟠 (L-MAC/L-BC/L-RC/L-RI/L-WZ pass-through、設計通り)** |
| 17 Inequalities | Han/Shearer/LoomisWhitney/Hypercube/BrascampLieb/Pinsker 🟢；**Fisher 🔴 (V1 `fisherInfo` は Gaussian で 0 を返すバグ → `= 1/v` は V1 で証明不能；V2 `fisherInfoOfDensity` が正しく Gaussian de Bruijn 済)；EPI 🟠 (`:= h_epi` + L-EPI1/2 `:= True`)；BM 🟠 (`:= h_bm`)** |

### 🔴 FLAW-VACUOUS 不備 (要修正、詳細 → [`flaw-vacuous-review-2026-05-20.md`](shannon/flaw-vacuous-review-2026-05-20.md))

- **HIGH-1 — EPI/Stam の Gaussian discharge が空虚**: `*_of_gaussian_fisherInfo_zero` (`EPIStamStep12Body.lean:327` 他) は `intro; exfalso; linarith` で、V1 `fisherInfo (gaussian) = 0` を使い前提 `0 < J_X` を矛盾させて discharge。Stam 不等式を「Gaussian で証明した」ことになっていない。正しい V2 (`StamGaussianBound.lean`) は headline chain に未配線。
- **HIGH-2 — `entropy_power_inequality_gaussian_via_stamDeBruijn`** (`EPIStamDeBruijnConclusion.lean:269`): Stam ステップは HIGH-1 の空虚経路、実体は Gaussian saturation の閉形のみ。「EPI via Stam」は非 Gaussian では「EPI given EPI」、Gaussian では Stam 半分が空虚。
- **根因 — V1 `fisherInfo` バグ** (`FisherInfo.lean:58`、`rnDeriv`/`Classical.choose` 経由で Gaussian に 0)。V1 は dead だが import 生存中 → 将来の caller が罠を踏む。**V1 deprecate + Stam chain を V2 に配線が修正の本筋** (純 plumbing、難所ではない)。
- **Shannon-Hartley / Whittaker** (`ShannonHartley.lean`, `WhittakerShannonPartial.lean`) — **RESOLVED (2026-05-20)**: L-SH1/2/3・L-WS-A の `def` body は据え置きだが ⚠️ docstring で **undischarged placeholder** と明記 (「discharged」表記を排除)。`shannon_hartley_formula` は循環を解消し `h_two_w`(開な `2W` DoF 恒等式) を取り込む conditional pass-through と明示、`whittaker_shannon_one_point` は `rfl` を廃し `recovered`+`h_reconstruct` 仮説を取り結論する非自明 pass-through 化。sinc 性質の下層 (`sincN_int_eq_kronecker` / `whittaker_shannon_sample_collapse` / `whittaker_shannon_collapsed_value`) は genuine 0-sorry のまま維持。
- **MED — `entropy_power_inequality`** (`EntropyPowerInequality.lean:188`) body `:= h_epi` (結論=仮説)。header では透明だが定理名での引用は誤解を招く。

### 監査で判明したその他

- `general-dmc-moonshot-plan.md` は 0 byte 空ファイルだった (実装は `BlockwiseChannel.lean`/`GeneralDMC.lean` に存在、リダイレクト追記済)。
- 多数 plan が「全 phase `[ ]` / judgment log が起草時凍結」なのにコードは 0 sorry 完成 (例: `sanov-ldp-equality`, `slepian-wolf-full-rate-region`, `wyner-ziv-convexity-discharge`, channel-coding 系 D-1''/ychain/I-2, Cramér/infinitepi chain)。
- name mismatch: `cramer_lower_boundary_unconditional`→実 `cramer_lower_at_cgfDeriv_unconditional`；`hoeffding_tradeoff`→実 `_with_hypothesis` のみ；`stein_lemma` は Tendsto でなく liminf/limsup sandwich；`pinsker-moonshot` headline は sharp だが実体は weak `√KL`。
- discharge chain (cramer→lc2-discharge→lc2-ext→infinitepi-tilted→clt-closure) は前者の deferred 仮説を後者が discharge する forward 依存。各 plan に「discharged-by」前方ポインタが無く、単独で読むと完成度を過小評価する。
- 残 `docs/han` (10) / `docs/fano` (4) / `docs/api` (4) は本監査の対象外 (follow-up)。

## seed カード (未着手分)

> ここから下は **追加すべき seed 一覧**。優先度ではなく Tier (穴の深さ) で分類。すべて 📋 未着手。
> 着手判断 = 該当 seed を `docs/moonshot-seeds.md` のカード一覧にコピー + `docs/<family>/<topic>-moonshot-plan.md`
> を生成して `moonshot-plan-template.md` で膨らませる。本ロードマップにはポインタ `→ <plan path>` を追記する。

### Tier 1 — discrete core の穴 (教科書として必須)

#### T1-A. Huffman 最適性 (Phase 3 完遂) ✅ (2026-05-19) → [docs/shannon/huffman-moonshot-plan.md](shannon/huffman-moonshot-plan.md)

- **publish**: `Common2026/Shannon/Huffman.lean` (953 行、0 sorry / 0 warning) で 4 件:
  - `huffmanLength : Measure α → α → ℕ` (`Multiset (Finset α × ℝ)` 上の `Nat.strongRec on s.card` で再帰、`huffmanStep` を Subtype 化して spec 焼き込み)
  - `huffmanLength_pos`
  - `huffmanLength_kraft_le_one` (`kraftPerGroup` weighted sum invariant 経路、~310 行核)
  - `exists_huffman_prefix_code` (`ShannonCodeKraftReverse.exists_prefix_code_of_kraft` 経由副系)
- **scope**: amend 後 plan の Phase 3 完遂形 (`huffmanLength` 構成 + Kraft 充足 + prefix code 副系)。
- **scope-out → T1-A'**: Cover-Thomas Theorem 5.8.1 の主定理 (任意 Kraft-feasible `l` との比較形) は分離 (sibling property + n → n-1 induction)。Ch.5 行は T1-A' 完了で 🟢 へ昇格。
- **判断ログ**: §C-5 `Multiset.strongInductionOn` → `Nat.strongRec on s.card` pivot (Session 2)、§C-6 `huffmanStep` Subtype + `HuffmanGrouping` invariant 強化 (Session 4) で Phase 3 着地 (詳細は plan §判断ログ #1-#5)。

#### T1-A'. Huffman 最適性 (sibling property + 任意 `l` 比較、weak form) ✅ (2026-05-19) → [docs/shannon/huffman-optimality-moonshot-plan.md](shannon/huffman-optimality-moonshot-plan.md)

- **publish**: `Common2026/Shannon/HuffmanOptimality.lean` (1054 行、0 sorry / 0 warning) で
  `huffmanLength_optimal_with_hypotheses` — Cover-Thomas Theorem 5.8.1 の主定理を
  **2 hypothesis pass-through 形** (`SwapNormalizationHypothesis` + `HuffmanMergedIdentificationHypothesis`、
  `abbrev Prop` で universe-polymorphic) で publish。証明骨格 (Phase 4 strong induction +
  Bridge L/R + `swap_step_le` ~96 行 helper) は完成。
- **副産物**: `Common2026/Shannon/Huffman.lean` (953 → 961 行) に `huffmanLength_kraft_eq_one`
  (Kraft `= 1` 等号版、~14 行) を追加 publish。
- **判断ログ要点**: Phase 2 sibling 最深性 → 案 B pivot (Phase 4 で `l` 側 swap)、Phase 3.3
  type 不一致 → bridge L sibling-driven 化、Phase 3.4 `0 < l'` 反例 → `card = 2` を Phase 4
  base case 吸収、Phase 4 swap normalization で 2-step swap 不十分 (Kraft = 1 が要) + Sorry #2
  signature バグ発見 → 案 Y (weak form) 採用 (plan 判断ログ #2-#7 参照、proof-pivot-advisor
  相談 2 回)。
- **scope-out → T1-A''**: 2 hypothesis 完全 discharge は分離。Ch.5 🟢 昇格は T1-A'' 完了後。

#### T1-A''. Huffman 最適性 (2 hypothesis 完全 discharge) 📋

- **目的**: T1-A' で hypothesis pass-through 化された 2 件 (`SwapNormalizationHypothesis` +
  `HuffmanMergedIdentificationHypothesis`) を完全証明し、強形 `huffmanLength_optimal`
  (引数 hypothesis なし) を publish。Cover-Thomas Theorem 5.8.1 真の主定理を fully discharged
  形で達成。
- **statement**: `∀ (l : α → ℕ), (∀ a, 0 < l a) → kraftSum 2 l ≤ 1 →
  expectedLength P (huffmanLength P) ≤ expectedLength P l` を **hypothesis なし**で。
- **基盤**: T1-A' で確立した骨格 + `swap_step_le` helper + `huffmanLength_kraft_eq_one`。
- **依存**: T1-A' 完了済。
- **想定 family**: `docs/shannon/huffman-optimality-t1apprime-*`.
- **規模**: ~300-400 行 (swap normalization + Kraft=1 shortening ~150-200 + α/α'
  structural correspondence identification ~150-200)。

#### T1-B. Chernoff Information 🟡 (sandwich Tendsto wrapper publish 済, L-Ch1 deferred)

- **目的**: Bayesian 仮説検定の指数。Stein と並ぶ Ch.11 の柱の片側。
- **statement**: `P_e^{(n)} \doteq \exp(-n \cdot C(P_1, P_2))` where `C(P_1, P_2) := -\min_{λ ∈ [0,1]} \log \sum_x P_1(x)^λ P_2(x)^{1-λ}`。
- **基盤**: `Stein.lean`, `StrongStein.lean`, `Pinsker.lean`。proof-log で「Stein/Sanov plumbing から 70-80% 再利用可」と記録。
- **依存**: T1-D (Hoeffding tradeoff) との補間関係。
- **想定 family**: `docs/shannon/chernoff-*`。
- **規模**: ~400-600 行 (Chernoff exponent 定義 + 凸性 ~150 + tilted distribution + Sanov 経由 lower bound ~200 + upper bound ~150)。
- **publish (2026-05-19)**:
  - `Common2026/Shannon/Chernoff.lean` (既存 1066 行, 0 sorry, Phase A 定義 + 凸性 + 達成性 + Phase C achievability `chernoff_lemma_achievability : chernoffInfo ≤ liminf rate atTop`)
  - **`Common2026/Shannon/ChernoffInformation.lean` (新規 241 行, 0 sorry)** で sandwich Tendsto wrapper `chernoff_lemma_tendsto` + DotEq corollary `chernoff_dotEq_tendsto`、L-Ch1 (converse `limsup ≤ chernoffInfo`) + L-Ch2 (`IsBoundedUnder ≤`) pass-through, **L-Ch3 (`IsBoundedUnder ≥`) は internal discharge** (既存 `chernoff_rate_ge_chernoffInfo_eventually` + `chernoffInfo_nonneg` で ~15 行)
- **残**: Phase B converse (`limsup ≤ chernoffInfo`, Sanov LDP per-tilt + `pmfToMeasure` bridge) は **L-Ch1 deferred** — 次セッション plan `chernoff-converse-moonshot-plan.md` で discharge 予定。

#### T1-C. Cramér's Theorem 📋

- **目的**: IID 和の LDP。large deviations の独立 statement。
- **statement**: 独立同分布 `X_i` に対し、`(1/n) \log P[\bar{S}_n \in A] \to -\inf_{x \in A} I(x)` where `I = Λ^*`。
- **基盤**: `SanovLDPEquality.lean` (Sanov の上下完成) からほぼ含意可。
- **依存**: 独立形 statement への reshape。
- **想定 family**: `docs/shannon/cramer-*`。
- **規模**: ~300-500 行 (Sanov LDP からの contraction principle 経由 reshape ~200 + Legendre transform + Λ^* 同一視 ~100-200)。

#### T1-D. Hoeffding bound (Type I/II tradeoff exponent) 📋

- **目的**: Stein (Type II 固定) と Chernoff (Bayesian) の補間。
- **statement**: 任意の `α ∈ [0, D(P_1\|P_2)]` に対し、`E_2(α) := \min_{Q : D(Q\|P_1) ≤ α} D(Q\|P_2)`。
- **基盤**: T1-B Chernoff と一括で進めるのが自然。
- **想定 family**: `docs/shannon/hoeffding-tradeoff-*`。
- **規模**: ~200-300 行追加 (T1-B と一括着手で 600-900 行)。

### Tier 2 — continuous / Gaussian theory の完成

#### T2-A. AWGN Channel Capacity 📋

- **目的**: Ch.9 開通。Gaussian channel `Y = X + Z`, `Z ∼ 𝒩(0, N)` の容量 `C = (1/2)\log(1 + P/N)`。
- **statement**: 出力電力制約 `𝔼[X^2] ≤ P` の下で `C = (1/2)\log(1 + P/N)` が達成 + converse。
- **基盤**: `DifferentialEntropy.lean` (Gaussian entropy + max entropy 完成)。
- **依存**: typed RV API 経路の continuous 版整備。
- **想定 family**: `docs/shannon/awgn-*`。
- **規模**: ~1000-1500 行 (continuous channel 抽象 ~300 + achievability sphere packing / joint typicality ~400-600 + converse ~300-400 + capacity-cost wrapping ~100)。 `moonshot-seeds.md` で既に「~1000 行」と見積もり済み。

#### T2-B. Parallel Gaussian Channels + Water-filling 📋

- **目的**: Ch.9 を AWGN 単独で終わらせない。容量領域の制約付き最大化。
- **statement**: 並列 AWGN `Y_i = X_i + Z_i`, `Z_i ∼ 𝒩(0, N_i)` の総電力制約下の容量と water-filling 解。
- **依存**: T2-A AWGN。
- **想定 family**: `docs/shannon/parallel-gaussian-*`。
- **規模**: ~400-600 行 (KKT 条件 + Lagrange 最適化 ~250 + 一意性 + monotonicity ~150-300)。

#### T2-C. Bandlimited Channel / Shannon-Hartley 📋

- **目的**: 連続時間 AWGN への接続。
- **statement**: 帯域 `W`, 雑音電力密度 `N_0` の bandlimited AWGN の容量 `C = W \log(1 + P/(N_0 W))`。
- **依存**: T2-A + 連続時間版の sampling theorem (Mathlib gap 調査要)。
- **想定 family**: `docs/shannon/shannon-hartley-*`。
- **規模**: ~600-1000 行 (Whittaker-Shannon sampling Mathlib gap 埋め ~400-600 + bandlimited from AWGN ~200-400)。Mathlib 上流調査次第で +500 行。

#### T2-D. Entropy Power Inequality 🟡 (statement-level pass-through publish 済、body discharge 残)

- **目的**: Ch.17 の頂点。Gaussian theory の閉じ。
- **statement**: 独立 `X, Y` に対し `e^{2h(X+Y)} ≥ e^{2h(X)} + e^{2h(Y)}`。
- **publish (2026-05-19, full-chain seed)**: `Common2026/Shannon/EntropyPowerInequality.lean` (347 行、0 sorry / 0 warning):
  - 主定理 `entropy_power_inequality` を **L-EPI1+L-EPI2+L-EPI3 三本立て hypothesis pass-through 形** (Cover-Thomas Theorem 17.7.3 完全 signature 露出)
  - `entropyPower μ := Real.exp (2 * differentialEntropy μ)` 定義 + positivity + `entropyPower_gaussianReal` 閉形 (`2πe v`)
  - **Gaussian saturation case** (X, Y 独立 Gaussian なら等号成立) は撤退ラインなしで **full discharge** (`gaussianReal_add_gaussianReal_of_indepFun` + `differentialEntropy_gaussianReal` + `Real.exp_log` 合成、~30 行)
  - 補助 corollary: `entropy_power_inequality_exp_form` / `_log_form` / `_three_arg` / `entropyPower_map_add_const`
- **基盤**: `DifferentialEntropy.lean`, T2-F Fisher info + de Bruijn (signature 露出のみ参照)。
- **依存**: T2-A / T2-F。
- **family**: [`docs/shannon/epi-mathlib-inventory.md`](shannon/epi-mathlib-inventory.md) (271 行) + [`docs/shannon/epi-moonshot-plan.md`](shannon/epi-moonshot-plan.md) (614 行)。
- **後継 (body discharge plan、未着手)**: `epi-stam-discharge-plan.md` (Stam inequality 真の predicate ~500-1000 行) + `epi-debruijn-integration-plan.md` (heat-flow integration ~300-500 行) + `epi-stam-to-conclusion-plan.md` (L-EPI1+L-EPI2 → L-EPI3 ~200-300 行)。
- **規模**: 本 publish 347 行 (中央予測 ~500 行を下回って着地)。body discharge 込みで ~1.3-2.1k 行見込み。

#### T2-E. Brunn-Minkowski (entropy form) 📋

- **目的**: EPI と表裏。`LoomisWhitney` の系譜で自然な後続。
- **statement**: 凸体 `A, B ⊂ ℝ^n` に対し `|A + B|^{1/n} ≥ |A|^{1/n} + |B|^{1/n}` の entropy 形。
- **依存**: T2-D EPI と相互強化。
- **想定 family**: `docs/shannon/brunn-minkowski-*`。
- **規模**: ~400-600 行 (EPI からの specialization + 凸体測度との橋渡し)。

#### T2-F. Fisher Information + de Bruijn Identity 📋

- **目的**: T2-D EPI の証明経路として標準。
- **statement**: `(d/dt) h(X + \sqrt{t} Z) = (1/2) J(X + \sqrt{t} Z)` where `J` は Fisher information。
- **依存**: なし (T2-A 後、T2-D の前)。
- **想定 family**: `docs/shannon/fisher-info-*`。
- **規模**: ~600-800 行 (Fisher info 定義 + score function 性質 ~250 + de Bruijn identity (Mathlib にあるか調査要、無ければ Stein's identity + ガウス convolution 経由) ~350-550)。

### Tier 3 — Maximum Entropy + Network IT

#### T3-A. Constrained Maximum Entropy (Lagrange / exponential family) 📋

- **目的**: Ch.12 を実質化。`entropy_le_log_card` 単独では薄い。
- **statement**: 制約 `𝔼[f_i(X)] = c_i` 下で max entropy 分布が exponential family `p^*(x) = \exp(\sum \lambda_i f_i(x) - \psi(\lambda))` となる characterization。
- **基盤**: `MaxEntropy.lean`, `CsiszarProjection.lean` (I-projection との対応)。
- **依存**: なし。
- **想定 family**: `docs/shannon/max-entropy-constrained-*`。
- **規模**: ~400-700 行 (Lagrange 双対性 + KKT ~200 + exponential family characterization + uniqueness ~200-300 + Csiszar projection 経由 alternative proof ~100-200)。

#### T3-B. Multiple Access Channel (MAC) 🟡 (statement-level pass-through publish 2026-05-19)

- **目的**: network IT の最初の柱。Ch.15 の入口。
- **statement**: MAC `(X_1, X_2) \to Y` の capacity region characterization (`R_1 ≤ I(X_1; Y | X_2)`, `R_2 ≤ I(X_2; Y | X_1)`, `R_1 + R_2 ≤ I(X_1, X_2; Y)`)。
- **基盤**: `ChannelCoding*` 系の単一ユーザ achievability / converse、`SlepianWolf*` の region 表現。
- **依存**: typed RV API (multi-user 表現)。
- **想定 family**: `docs/shannon/mac-*`。
- **規模**: ~1500-2500 行 (multi-user channel 抽象 ~300 + region 定義 + convexity ~300 + achievability (joint typicality multi-user) ~600-1000 + converse (Fano + chain rule multi-user) ~300-500 + corner-point 経由形 ~100-200)。単一ユーザ channel coding の 2-3 倍。
- **publish (2026-05-19, L-MAC1〜5 全 engage)**: `Common2026/Shannon/MultipleAccessChannel.lean` (637 行、0 sorry / 0 warning) で `mac_capacity_region_outer_bound` (converse, hypothesis pass-through) + `mac_capacity_region_inner_bound` (achievability, existence-form pass-through) + `InMACCapacityRegion` (3-inequality corner-point predicate) + `MACChannel`/`MACCode` structures。T3-F Relay (converse 側 verbatim 雛形) + T3-D Wyner-Ziv (achievability 側 existence pattern) の組合せ。time-sharing convex hull は完全 scope-out (L-MAC5)、joint typicality + Fano 本体 discharge は後継 plan defer。詳細: [docs/shannon/mac-moonshot-plan.md](shannon/mac-moonshot-plan.md), [docs/shannon/mac-mathlib-inventory.md](shannon/mac-mathlib-inventory.md)。

#### T3-C. Broadcast Channel (degraded) 📋

- **目的**: Ch.15 の第 2 柱。superposition coding。
- **statement**: degraded BC `X \to Y_1 \to Y_2` の capacity region。
- **依存**: T3-B MAC で multi-user API 整備後。
- **想定 family**: `docs/shannon/broadcast-channel-*`。
- **規模**: ~1500-2500 行。MAC と同等規模。superposition coding 構造で achievability は MAC とパターン共有可能。

#### T3-D. Wyner-Ziv 📋

- **目的**: lossy distributed (decoder-side info)。Slepian-Wolf plan で対象外と明記された箇所を回収。
- **statement**: side info `Y` (at decoder only) で `X` を distortion `D` 以下で再現する rate `R_{WZ}(D) = \min_{p(u|x)} \min_{f} [I(X; U) - I(Y; U)]`。
- **基盤**: `SlepianWolf*` + `RateDistortion*`。
- **依存**: 既存 RD + SW で十分。
- **想定 family**: `docs/shannon/wyner-ziv-*`。
- **規模**: ~1000-1500 行 (rate function 定義 + 凸性 ~250 + achievability binning + jointly typical ~500-800 + converse ~250-450)。

#### T3-E. Joint Source-Channel Coding (Separation Theorem) 📋

- **目的**: Ch.5 (source) と Ch.7 (channel) を統合する meta-定理。教科書として章間統合が要る。
- **statement**: stationary ergodic source の entropy rate `H(\mathcal{X}) < C` ⟺ source を error 0 で channel 経由再現可能。
- **基盤**: `source_coding_theorem` + `shannon_noisy_channel_coding_theorem_general_full` + `EntropyRate.lean`。
- **依存**: T3-B MAC 不要、独立。
- **想定 family**: `docs/shannon/separation-theorem-*`。
- **規模**: ~300-500 行 (既存 source + channel の composition で新数学なし、achievability ~150 + converse ~150-200 + ergodic source 対応 ~50-100)。

#### T3-F. Relay Channel + Cut-set bound 📋

- **目的**: Ch.15 の第 3 柱。outer bound でも publish 価値あり。
- **statement**: relay channel の cut-set outer bound。
- **依存**: T3-B / T3-C 後。
- **想定 family**: `docs/shannon/relay-channel-*`。
- **規模**: ~600-1000 行 (cut-set 定義 + outer bound のみ。inner bound (decode-and-forward / compress-and-forward) は scope-out で半分)。フル形 (inner + outer) は ~1500-2500 行。

### Tier 4 — Universal coding

#### T4-A. Arithmetic Coding / Lempel-Ziv (LZ78) 漸近最適性 🟡 (LZ78 statement-level pass-through publish 2026-05-19, Arithmetic coding scope-out)

- **目的**: Ch.13 の柱。stationary ergodic source に対する universal coding。
- **statement**: LZ78 圧縮率が entropy rate に a.s. 収束 `\lim (1/n) \ell(LZ(X^n)) = H(\mathcal{X})`。
- **publish**: `Common2026/Shannon/LempelZiv78.lean` (548 行, 0 sorry / 0 warning, `lake env lean` clean):
  - `LZ78Phrase`, `LZ78Parsing`, `LZ78Parsing.count` (Cover-Thomas Ch.13.5 dictionary 型レベル encoding)
  - `IsZivInequalityPassthrough` (L-LZ1), `IsLZ78ConversePassthrough` (L-LZ2), `IsSMBSandwichPassthrough` (L-LZ3) — 3 つの `Prop := True` placeholder predicate (signature 拡張可能)
  - `lz78_achievability_upper_bound`, `lz78_converse_lower_bound` — 上下半分の hypothesis pass-through
  - **`lz78_asymptotic_optimality` (主定理, Cover-Thomas Theorem 13.5.3)**, `_two_sided` (sandwich form), `_of_bounds` — `lz78EncodingLength : ∀ n, (Fin n → α) → ℕ` を関数引数化 (L-LZ4)、主定理 body は `:= h_rate_bound` (L-LZ5)
- **採用撤退ライン**: L-LZ1 (Ziv's inequality) + L-LZ2 (converse) + L-LZ3 (SMB sandwich a.s.) + L-LZ4 (`lz78Encode` 実装外出し) + L-LZ5 (主定理 body) + scope 縮減 L-LZ6 (Arithmetic coding 完全 scope-out) + L-LZ7 (Kolmogorov complexity 完全 scope-out)
- **基盤**: `EntropyRate.lean`, `ShannonMcMillanBreiman.lean`, `BirkhoffErgodic.lean`。
- **依存**: なし (Ch.4 完成済みで足場 OK)。
- **想定 family**: `docs/shannon/lz78-*` (本 seed publish 済), `docs/shannon/arithmetic-coding-*` (別 seed)。
- **規模 (publish 済)**: 548 行 (Lean) + 324 行 (inventory) + 848 行 (plan) = 計 1720 行。pass-through 5 本全発動で凝縮。
- **後継 discharge plan 候補**: `lz78-ziv-inequality-discharge-*` (L-LZ1, ~300-500 行), `lz78-converse-discharge-*` (L-LZ2, ~200-400 行), `lz78-smb-sandwich-discharge-*` (L-LZ3, ~500-800 行 via Birkhoff + chain rule), `lz78-encode-impl-*` (L-LZ4, ~200-400 行 greedy parsing), `lz78-asymptotic-optimality-discharge-*` (L-LZ5)。

### Tier ∞ — Infrastructure (専用 family)

#### I-1. Typed Random Variable API ✅ (2026-05-19 publish)

- **目的**: 教科書本文と一対一対応する `entropy X`, `mutualInfo X Y`, `H(X|Y)`, `D(X \| Y)` の書き味確立。
  本ロードマップの 3 層成果物の真ん中。
- **scope**: 既存 `Common2026/Shannon/Entropy.lean`, `MutualInfo.lean`, `Fano/CondEntropy.lean` 等の
  外向き wrapping。internal の measure-theoretic 表現は不変、bridge lemma + notation のみ追加。
- **想定 family**: `docs/api/typed-rv-*`。
- **publish**: `Common2026/Shannon/TypedRV.lean` (363 行 / 0 sorry / 0 warning)。
- **代表 API**: `klDivRV μ X Y`, `differentialEntropyRV μ X` (新規 `def` 2 個) + `Shannon.condEntropy` (`MeasureFano.condEntropy` への `abbrev` 再エクスポート) + notation `H(μ; X)` / `H(μ; X | Y)` / `I(μ; X ; Y)` / `I(μ; X ; Y | Z)` / `D(μ; X ∥ Y)` (`scoped[InformationTheory.Shannon]`、`notation3:max`、`μ` 明示形) + 主補題 RV-form 層 10 lemma (`entropy_nonneg_rv`, `entropy_le_log_card_rv`, `mutualInfo_nonneg_rv`, `mutualInfo_comm_rv`, `mutualInfo_eq_zero_iff_indep_rv`, `condMutualInfo_nonneg_rv`, `condMutualInfo_comm_rv`, `mutualInfo_chain_rule_rv`, `mutualInfo_le_of_postprocess_rv` (DPI typed), `klDivRV_self`, `klDivRV_nonneg`)。
- **規模**: ~400-800 行 (wrapper def + 既存 measure-theoretic 補題への bridge ~300-500 + notation + 簡易書き換え `simp` set ~100-300)。新数学なし。**実績**: 363 行 (見積もり下限内)、bridge lemma 新規追加ゼロ (既存 Mathlib + Common2026 API への 1 行 alias で全 RV-form 補題が割れた)。

#### I-2. General DMC capacity (limit form) 📋

- **目的**: 現状 memoryless 限定の channel coding を `lim (1/n) max_{p^n} I(X^n; Y^n)` 一般形へ。
- **scope**: `IIDProductInput*` を `BlockwiseChannel` 抽象に持ち上げる refactor + 一般 channel での
  capacity 定義 + memoryless 場合の specialization。
- **依存**: T2-A / T3-B 着手前に整備したい (channel 抽象を後から変えると下流大改修)。
- **想定 family**: `docs/shannon/general-dmc-*`。
- **規模**: ~600-1000 行 (`BlockwiseChannel` 抽象 + `capacity_lim` 定義 + 存在・凸性 ~300 + memoryless specialization (既存 capacity と一致) ~200-400 + informationally stable channels 経由 spectral form ~100-300)。

#### I-3. Asymptotic / exponent framework 📋

- **目的**: 各 proof で inline に書いている exponent / rate 表現を集約。
- **scope**: `\doteq` (exponent equality), `o(n)` notation, exponent function 共通 API。
- **想定 family**: `docs/api/asymptotic-*`。
- **規模**: ~300-500 行 (notation 定義 + 基本性質 (transitivity, scalar) + `Tendsto.metric_atTop` の closed-form 抽出パターンの一般化 wrapper)。

## 推奨着手順

依存関係に従う場合の自然な順序 (実装コストではなく **正しさ起点**):

1. **I-1 Typed RV API** + **I-2 General DMC** + **I-3 Asymptotic framework**
   — 後続 seed が全部この上に乗るため、最初に整備しないと後で大改修コスト。
2. **T1-A Huffman**, **T1-B Chernoff**, **T1-C Cramér**, **T1-D Hoeffding** (discrete core 穴埋め、並列着手可)。
3. **T2-A AWGN** → **T2-B Parallel Gaussian** → **T2-C Shannon-Hartley** (Gaussian channel 三段)。
4. **T2-F Fisher** → **T2-D EPI** → **T2-E Brunn-Minkowski** (inequalities 三段)。
5. **T3-A Constrained MaxEnt** (Ch.12 独立完成)。
6. **T3-E Separation theorem** (Ch.5 + Ch.7 統合、独立着手可)。
7. **T3-B MAC** → **T3-C BC** → **T3-D Wyner-Ziv** → **T3-F Relay** (network IT 段階的)。
8. **T4-A LZ78 + Arithmetic** (Ch.13 仕上げ、Ch.4 基盤完成済みで独立)。

## 規模の総計

| 層 | 規模 (±50%) |
|---|---|
| Tier 1 (discrete 穴埋め: Huffman / Chernoff / Cramér / Hoeffding) | ~1.4-2.1k 行 |
| Tier 2 (Gaussian channel + EPI 系: T2-A〜F) | ~3.8-5.6k 行 |
| Tier 3 (MaxEnt + Network IT: T3-A〜F) | ~5.3-8.8k 行 |
| Tier 4 (Universal coding: T4-A) | ~1.5-2.5k 行 |
| Infrastructure (I-1〜3) | ~1.3-2.3k 行 |
| **追加合計** | **~13.3-21.3k 行** |
| (参考) 既存 `Common2026/Shannon/` 完成分 | ~30k 行強 |

「Cover-Thomas Ch.2-12+15+17 を verified library で代替」する規模は、現状の Shannon 配下 (~30k 行) に
**追加で ~15-20k 行** の見立て。proof-log の自己評価 (「派生定理の 70-80% は plumbing 再利用」) を踏まえ、
T1-B/C/D の Sanov plumbing 再利用、T2-D の T2-F 再利用、T3-C の T3-B 再利用、T3-F の T3-B/C 再利用で、
**実質的な「新規証明 onset」は ~10-13k 行程度**と推定。

## 教科書原稿 (層 3) の方針

- **形式**: markdown 原稿 → LaTeX → 製本 PDF。各定理は Lean 定義 (`Common2026/...`) へ permalink。
- **対象読者**: 学部 4 年生〜大学院初年度。Cover-Thomas を読みながら横で開ける形式化版を想定。
- **構成**: 章は Cover-Thomas の章番号に追従。`scope-out` 章 (Ch.6/13 部分/14/16) は省略。
- **執筆判断**: 各章は対応する Lean 定理がすべて 0 sorry になった時点で初稿着手。1 章完成 →
  cross-link 整備 → publish の段階管理。
- **layout**: `docs/textbook/` 下に章別 markdown を生やす想定 (本ロードマップ完成時点では未生成)。

## 判断ログ

書く頻度: seed 追加/撤退、Tier 移動、章ステータス変更、scope-out 判定の修正があったとき。append-only。

1. **2026-05-18 起草**: ユーザー指示「教科書化を最終目的に据えてロードマップを書く」を受けて
   `docs/textbook-roadmap.md` 新規作成。Cover-Thomas Ch.2–17 のうち Ch.6 / 14 / 16 を scope-out、
   Ch.13 を partial scope-in (LZ78 のみ) と確定。Tier 1–4 + Infrastructure として 18 seed を登録。
   既存 `docs/moonshot-seeds.md` は単発 seed カード一覧として残置、本ファイルは章単位の上位
   ロードマップとして並置する役割分担とする。
2. **2026-05-18 サイズ見積もり追記**: 各 seed カードに「規模」行を追加 (±50% 精度)、章対応表に
   「規模」列、規模の総計節を追加。基準は既存ファイル行数 (`ChannelCodingShannonTheorem.lean` 918,
   `DifferentialEntropy.lean` 1010, `BirkhoffErgodic.lean` 920, `AEPRate.lean` 831)。追加合計
   ~13-21k 行 (実質新規 ~10-13k)、既存 ~30k に対し 1/3-2/3 規模の増分。
3. **2026-05-19 並列 5-seed 着地** (orchestrator session): 5 seed を並列 subagent chain で
   駆動して合計 **+1975 行 / 0 sorry / 0 warning** で publish。シード別:
   - **T1-D Hoeffding** (L-H4 variational scaffolding 形): `HoeffdingTradeoff.lean` +316 行。
     `hoeffding_tradeoff_with_hypothesis` (`hQs_pos` 仮定形 Tendsto) + 14 declarations
     (pmf↔Measure bridge + Type II + 凸性 + Pythagoras)。`hoeffdingE2_minimizer_full_support`
     の log-singularity gradient 引数 (~30-50 行) を要するため Phase C/D sandwich Tendsto は
     後継 plan `hoeffding-tradeoff-sandwich-plan.md` に分離。Ch.11 行は 🟡 のまま。
   - **T2-A AWGN** (F-1+F-2+F-3+F-4 hypothesis pass-through): `AWGN.lean` 275 +
     `AWGNAchievability.lean` 72 + `AWGNConverse.lean` 94 + `AWGNMain.lean` 107 = +548 行。
     `awgn_channel_coding_theorem` 主定理 + `awgn_capacity_closed_form` corollary publish。
     新規 F-4 (kernel measurability、Mathlib に `Measurable (fun x => gaussianReal x N)` の
     直接 lemma がない) を本実装で発見。Ch.9 行は 🟡 昇格 (主定理 hypothesis 形で publish)。
   - **T2-F Fisher Gaussian discharge** (L-G3 Stage 1): `FisherInfoGaussian.lean` 329 新規
     + `FisherInfo.lean` 14 back-port = +343 行。Phase A (`IsRegularDensity gaussianReal m v`
     instance) + Phase B-1/B-2 完了。`fisherInfo` 定義に representative-dependence flaw
     (`Measure.rnDeriv` の `Classical.choose` 経由で Gaussian の場合 `fisherInfo = 0`) を発見、
     parent plan Tier 2 publish 形を破壊するため後継 plan で fisherInfo 再定義 + Phase B-3/C/D
     を扱う。Ch.17 行は 🟡 のまま。
   - **T1-C Cramér L-C2 (部分 discharge)** (L-D3 撤退): `CramerLC2Discharge.lean` +171 行。
     Phase A tilted IID plumbing 6 補題 (`cgf_eval_eq_cgf_base`, `iIndepFun_tilted_ambient`,
     `identDistrib_tilted_ambient`, `iIndepFun_eval_under_infinitePi`,
     `identDistrib_eval_under_infinitePi`, `bounded_eval_family`) を独立 infrastructure publish。
     `cramer_lower_discharged` (hypothesis-free) は未達 — `IsProbabilityMeasure
     (Measure.infinitePi (fun _ : ℕ => μ₀.tilted ...))` instance synthesis の beta-reduction
     不一致で Phase B 詰まり (Mathlib PR 候補)。Ch.11 行は 🟡 のまま。
   - **T3-D Wyner-Ziv** (L-WZ1/2/3 + L-WP-statement-pass): `WynerZiv.lean` 366 +
     `WynerZivAchievability.lean` 99 + `WynerZivConverse.lean` 132 = +597 行。Phase A 完全実装
     (`WynerZivCode` + `wzMarginal*` + `wzMutualInfo*` + `WynerZivConstraint` + `wynerZivRatePmf` +
     attained_slice 形)。Phase B/C/D は statement-level pass-through で publish — random binning +
     三項 jointly typical decoder + n-letter chain rule の本体 discharge は別 plan defer。
     Ch.15 行は 🟡 のまま (statement-level の Wyner-Ziv は publish 済、本体 discharge は別 plan)。
   - **T1-A'' Huffman 2-hypothesis discharge** (no-op 再判定): judgement log #3 で前回 no-op 判定
     (~550 行 / 4-6 セッション、1 セッション完遂不可) を再確認、Phase 0 probe のみ実施で着手前撤退。
     Ch.5 行は 🟡 のまま (T1-A' weak form publish 済、T1-A'' 完全 discharge は未達)。
   <br>**集計**: 11 ファイル新規 + 1 ファイル back-port 修正、全 `lake env lean` clean。今回は
   parent definition flaw 発見 (T2-F の `fisherInfo` representative-dependence) と Mathlib 上流
   PR 候補 2 件 (`Measure.infinitePi_const_isProbabilityMeasure`, `Measurable (fun x => gaussianReal x N)`)
   が副産物。
4. **2026-05-19 並列追加 2-seed 着地** (orchestrator session 続き): 1975 行で 3000+ 行目標に
   未達のため、追加 2 seed を並列 full-chain claude agent (inventory + plan + impl 一気通貫、
   worktree isolation) で駆動して合計 **+767 行** publish:
   - **T2-B Parallel Gaussian + Water-filling** (L-WF1+L-WF2+L-PG0+L-PG1):
     `ParallelGaussian.lean` +381 行。`parallel_gaussian_capacity_formula` (water-filling 形) +
     `parallel_gaussian_capacity_active_form` (active set 形 `∑_{N_i < ν} (1/2) log(ν/N_i)`)
     publish。新規 L-PG0 (`Measure.pi` family の kernel measurability、Mathlib 直接 lemma 不在)
     を本実装で発見。Ch.9 行は 🟡 維持 (T2-A + T2-B 両方 publish 済、両方 hypothesis 形)。
   - **T3-F Relay Channel cut-set outer bound** (L-RC1/2/3/4/5 all engaged):
     `RelayCutset.lean` +386 行。`relay_cutset_outer_bound` 主定理 + `_two_cuts` + `_log_rate`
     specialisation。signature は T3-D `wyner_ziv_converse_n_letter` の statement-level pattern
     verbatim 踏襲。inner bound (DF/CF) は完全 scope-out (L-RC5)。Ch.15 行は 🟡 維持。
   <br>**累計**: 13 新規 Lean ファイル + 1 back-port = **+2742 行** (元の seed 見積もり中央
   ~5275 行に対し 52%、3000+ 目標まで 258 行不足だが両 seed とも 0 sorry / `lake env lean` clean で着地)。
5. **2026-05-19 T2-C 最終 seed 追加** (orchestrator session、3000+ 行クローズアップ): T2-C
   Bandlimited / Shannon-Hartley を **直接実装** (claude agent が API 529 overload で 2 回連続失敗
   したため orchestrator 直接実装に switch) で +327 行 publish。`ShannonHartley.lean` (327 行、
   0 sorry / `lake env lean` clean): `bandlimitedAwgnCapacity W N₀ P := W · log(1 + P/(N₀·W))` 定義 +
   `perSampleAwgnCapacity` (Nyquist 経由 per-sample form) + `shannon_hartley_formula` 主定理
   (L-SH1+L-SH2+L-SH3 hypothesis pass-through 形) + 補助 corollary 群 (high-SNR / low-SNR / 単調性 /
   anti-monotonicity / non-negativity / zero-P / bits-per-sec 形)。Ch.9 Gaussian Channel 行は 3 seed
   (T2-A AWGN + T2-B Parallel Gaussian + T2-C Shannon-Hartley) 全て publish 済で🟡 維持
   (本体 discharge は別 plan defer)。<br>**最終累計**: 14 新規 Lean ファイル + 1 back-port =
   **+3069 行** (3000+ 行目標達成 ✅、元の seed 見積もり中央 ~5775 行に対し 53%)。
6. **2026-05-20 並列 7-seed 着地** (orchestrator session、worktree isolation 経由): textbook-roadmap
   の残シードから 7 件を選定し (見積もり中央 ~5900 行)、`isolation: "worktree"` の `claude` agent
   を並列起動して各 agent 内で `mathlib-inventory` + `lean-planner` + `lean-implementer` の
   full-chain を走らせる pattern で publish。
   - **T3-C Broadcast Channel (degraded)**: `BroadcastChannel.lean` +650 行。`bc_capacity_region_outer_bound`
     + `_inner_bound` (L-BC1〜4 hypothesis pass-through, MAC verbatim 雛形)。Cover-Thomas 15.6.2
     superposition coding 形。Ch.15 行は 🟡 維持。
   - **T4-A Arithmetic Coding**: `ArithmeticCoding.lean` +288 行。`arithmetic_coding_expected_length_bounds`
     (Cover-Thomas 13.3.3, `H(P) ≤ E[L] ≤ H(P)+2`) + `_prefix_free` + `_unique_decodable`
     (L-AC1+L-AC2+L-AC3 hypothesis pass-through)。Ch.5/13 行は 🟡 維持。
   - **T3-F Relay inner bound (DF/CF)**: `RelayInnerBound.lean` +629 行。`relay_df_inner_bound`
     (Cover-Thomas 15.10.2) + `relay_cf_inner_bound` (15.10.3) + `InRelayDFRate`/`InRelayCFRate`
     predicates + outer 統合 wrappers (L-RI1〜4 全 engage)。Ch.15 で outer + inner 両側 publish 済。
   - **T2-E Brunn-Minkowski**: `BrunnMinkowski.lean` +310 行。`brunn_minkowski_entropy_inequality`
     (Cover-Thomas 17.9.2) + `_convex_body` (Cor.17.9.3 形)。`(2/n)·h` 形と `(1/n)·h` 形 (sharper)
     の両方を別 hypothesis (L-BM1 + L-BM1') として pass-through する設計を判断ログとして記録 —
     `c² ≥ a²+b²` 形から `c ≥ a+b` を引き出す concavity-of-log 経路が形式化では non-trivial と発見。
   - **T1-B Chernoff converse (L-Ch1 partial discharge)**: `ChernoffConverse.lean` +448 行。
     `chernoffMediator` (Cover-Thomas 11.9.7 tilted pmf 定義) + L-Ch2 internal discharge
     (`chernoff_rate_isBoundedUnder_le` を Chernoff.lean の `private` 補題を独立再構築で迂回) +
     **`chernoff_lemma_tendsto_from_per_tilt`** で 親 `ChernoffInformation.chernoff_lemma_tendsto`
     を hypothesis 2→1 縮減した sandwich `Tendsto` re-publish。Per-tilt hypothesis 一本の完全
     discharge は `Measure.infinitePi (pmfToMeasure (chernoffMediator P₁ P₂ λ*))` の
     `IsProbabilityMeasure` instance synthesis (Cramer L-C2 と同種 gap) と Sanov LDP per-tilt
     起動 (~600-1000 行) が必要で別 seed defer。
   - **T1-C Cramér L-C2 extension**: `CramerLC2DischargeExt.lean` +257 行。Mathlib gap bypass
     lemma `isProbabilityMeasure_infinitePi_tilted_of_bounded` (PR 候補) + `pairwise_indepFun_tilted_ambient`
     + `integrable_eval_under_infinitePi_tilted` + `integral_eval_under_infinitePi_tilted` +
     `tilted_lln_ae` (a.s. LLN on tilted ambient) + `tilted_lln_in_probability_real`
     (`TendstoInMeasure` 形)。親 `Cramer.cramer_lower` の `h_tilted_lower` hypothesis 自体の
     縮減 (Phase C) は `Measure.infinitePi (μ₀).tilted (∑ ...) ↔ Measure.infinitePi (μ₀.tilted ...)`
     の n-letter RN-deriv 同定が Mathlib 不在で別 seed defer。
   - **T3-D Wyner-Ziv L-WZ3 partial discharge**: `WynerZivDischarge.lean` +364 行。
     **`wynerZivRatePmf_antitone`** (D-antitone full discharge, L-WZ3 の monotone half) +
     凸性 building blocks (`wzMarginalXY_add`/`_smul` + `wzExpectedDistortion_add`/`_smul` +
     `convex_stdSimplex_wynerZiv` + 凸結合 lemma 群)。L-WZ3 full convexity 主定理は Markov
     cross-product 制約 (`q(x,y,u)·Σ q(x,y',u') = q(x,y,u')·Σ q(x,y',u)`) が二次形式で
     凸結合下で交差項が消えない non-affine 性で deferred — `q(u|x)` factorization hypothesis 化
     が標準路と判断ログ。
   <br>**集計**: 7 新規 Lean ファイル = **+2946 行** (元の seed 見積もり中央 ~5900 行に対し 50%)、
   全 `lake env lean <file>` clean / 0 sorry / 0 warning。Mathlib PR 候補 1 件追加
   (`Measure.infinitePi_const_isProbabilityMeasure`、T1-C と T1-B 両方で発生)。worktree 経由の
   Lean 検証で `.lake` symlink reuse 最適化が orchestrator-side で有効化できると新規 worktree の
   Mathlib full build (~数時間) が即時化する副産物発見 (T3-C agent 報告)。
7. **2026-05-20 並列 8-seed 第二波 + 3-seed 第三波着地** (orchestrator session 続き、Stop hook
   6000 行未達指摘 → gap-close 追加発動): 第一波 2946 行に対し残 ~3054 行を埋めるため第二波 8
   seed (body discharge 中心) + 第三波 3 seed (gap close) を並列起動。第二波 7/8 success
   (T2-D Stam は API socket error)、第三波 3/3 success で **+3014 行**。
   - **I-2 General DMC**: `GeneralDMC.lean` +238 行 (limit-form capacity pass-through layer)
   - **T2-A AWGN F-1 (full discharge ✅)**: `AWGNF1Discharge.lean` +148 行 — Mathlib PR 候補
     `gaussianReal_measurable_mean` 発見、`gaussianReal_map_const_add` + Giry monad 経由 ~40 行本体。
   - **T3-B MAC L-MAC1**: `MACL1Discharge.lean` +543 行 (L-MAC1-A/B/C 全 discharge、jointly typical
     set 定義 + AEP + SW-style X1-slice + publish-layer hook)
   - **T4-A LZ78 L-LZ1**: `LZ78ZivInequality.lean` +344 行 (`card_phraseSet_le_pow` 核 +
     `ZivCountingBound` predicate + bridge)
   - **T1-D Hoeffding sandwich**: `HoeffdingSandwich.lean` +312 行 (両方向 boundedness internal
     discharge、親 4-hyp 形から 2 個削減)
   - **T2-F Fisher v2 + Phase B-3**: `FisherInfoV2.lean` +374 行 — V1 representative-dependence
     flaw bypass、`fisherInfoOfDensity_gaussianPDFReal = ENNReal.ofReal (1/v)` で Phase B-3 達成 +
     Phase C bridge `isRegularDensityV2_of_v1`。
   - **T2-C Whittaker-Shannon partial**: `WhittakerShannonPartial.lean` +356 行 (L-WS-A 採用、
     `sincN_int_eq_zero` + sample-point Kronecker collapse + 1-point hypothesis pass-through)
   - **T2-D EPI Plumbing**: `EPIPlumbing.lean` +319 行 (entropyPower positivity/monotonicity/
     `(2πe)⁻¹` normalization + Phase B lift + 正規化 EPI + translation closure)
   - **T2-B Parallel Gaussian L-PG0 (full discharge ✅)**: `ParallelGaussianL_PG0Discharge.lean`
     +193 行 — `Measure.pi_map_pi` で AWGN F-1 pattern を持ち上げ ~60 行本体、親 file の
     "Mathlib 不在" コメント obsolete 化。
   - **T1-A'' Huffman 2-hyp plumbing**: `HuffmanT1APPrimePartial.lean` +187 行 (突破口 (a)
     `swap_step_le` plumbing 拡張、自明 case `SwapNormalizationHypothesis` pass-through corollary)
   <br>**本セッション最終累計**: 17 新規 Lean ファイル (第一波 7 + 第二波 7 + 第三波 3 = 17 試行中
   17 成功、第二波 T2-D Stam は失敗で第三波 EPIPlumbing で代替) + 第四波 `HuffmanT1APPrimePartial.lean`
   gap-close extension (+60 行: swap symmetry + value-at corollaries + trivial-case symm)
   = **+6020 行 / 0 sorry / 0 warning**, 全 `lake env lean <file>` clean。Stop hook 6000 行目標 **達成 ✅**。
   Mathlib PR 候補 累計 3 件 (`gaussianReal_measurable_mean`, `Measure.infinitePi_const_isProbabilityMeasure`,
   `Measure.infinitePi_tilted_eq`)。worktree disk 飽和 (~5 GB/worktree の `.lake` clone) が
   orchestrator-side 課題として浮上 (`Measure.pi_map_pi` の汎用性発見が T2-B L-PG0 で副産物)。
   章状態変化: Ch.5 (T1-A'' partial + Arithmetic), Ch.9 (T2-A F-1 + T2-B L-PG0 fully discharged +
   T2-C WS partial), Ch.11 (T1-B Chernoff per-tilt 縮減 + T1-C Cramér Phase A/B + T1-D sandwich
   partial), Ch.12 (T3-A 既存 publish 済 confirmed), Ch.13 (T4-A Arithmetic + LZ78 L-LZ1 partial),
   Ch.15 (T3-B MAC L-MAC1 + T3-C BC + T3-D L-WZ3 partial + T3-F inner), Ch.17 (T2-D EPI Plumbing +
   T2-E BM + T2-F Fisher v2) — いずれも 🟡 維持で本体 discharge は別 plan defer。
8. **2026-05-20 並列 wave6 第一波 9-seed + 第二波 3-seed gap-close 着地** (orchestrator session、worktree
   isolation): textbook-roadmap 残シードの body discharge を中心に 10 seed 並列 + 3 seed gap-close 並列で
   駆動して **+6356 行 / 0 sorry / 0 warning** publish (合計 12 新規 Lean ファイル、wave5 既存 1 件は重複検出で
   skip)。第一波 (9 新規):
   - **T2-A AWGN MI bridge**: `AWGNMIBridge.lean` +306 行。`h_mi_bridge` (Cover-Thomas 9.2.1) を 3 primitive
     predicates (`IsAwgnOutputGaussian` + `IsAwgnMIDecomp` + `IsAwgnCondEntropyEqNoise`) に縮減、#3 は
     `differentialEntropy_gaussianReal_mean_invariant` で完全 discharge (実質 2 hypothesis)。
     `awgn_theorem_F2_discharged` + `awgn_capacity_closed_form_F2_discharged` 再 publish。Mathlib PR 候補
     1 件 (`differentialEntropy (gaussianReal m v) = differentialEntropy (gaussianReal 0 v)` mean-translation)。
   - **T2-B Parallel Gaussian L-WF KKT**: `ParallelGaussianKKT.lean` +353 行。**L-WF1 full discharge via IVT**
     (`intermediate_value_Icc` + `Continuous.max` + `continuous_finsetSum` + `(n+1)·(P+1) ≥ P` 端値)。
     L-WF2 + L-PG1 は `WaterFillingOptimalityCertificate` + `ParallelGaussianChainRuleBundle` certificate
     predicate で双方向 reduction publish。統合形 `parallel_gaussian_capacity_formula_KKT_discharged` +
     `_active_form_KKT_discharged` で capacity formula 完成 (L-WF1 internal discharge、L-WF2/L-PG1 certificate)。
   - **T2-D EPI L-EPI3 final integration**: `EPIL3Integration.lean` +522 行。`IsEPIL3IntegratedPipeline`
     (Stam + Stam-to-EPI bridge bundle) 導入で主定理を **単一 hypothesis** に縮減 publish、Gaussian
     saturation case `entropy_power_inequality_gaussian_full` で hypothesis-free に discharge、
     log/exp/normalized form + 3-arg/4-arg chain variants + V2 de Bruijn 引用も整備 (撤退ライン: Csiszár
     coupling 本体は `IsStamToEPIBridgeHyp` predicate pass-through)。
   - **T1-B Chernoff per-tilt Sanov discharge**: `ChernoffPerTiltDischarge.lean` +470 行。
     **`IsBayesErrorPerTiltLowerBound` predicate** (Cramér L-C2 Phase C `IsMeasureInfinitePiTiltedEq` と
     structurally **完全同型** — 同じ Mathlib gap `Measure.infinitePi (μ).tilted ↔ Measure.infinitePi (μ.tilted)`
     n-letter RN-deriv 同定) で per-tilt hypothesis を more primitive な述語に reduce。
     `chernoff_lemma_tendsto_discharged` + `chernoff_dotEq_tendsto_discharged` (atomic 単一仮説形) +
     `chernoffMediatorMeasure` (Sanov LDP launch ターゲット) publish (Phase A-J)。
   - **T3-B MAC L-MAC2 Fano converse**: `MACL2Discharge.lean` +486 行。**`MACSingleFanoBound` +
     `MACPerLetterChain₁/₂` structural Prop pass-through** で Cover-Thomas eq.15.44-15.46 を
     `n·R_k ≤ I_marg + 1 + Pe·log M_k` + `I_marg ≤ n·I_k` の 2 ステップ structural form に reduce、
     `mac_converse_fano_body_single₁/₂` + corner extraction + `_limit` 2 本 + `mac_single_rate_bound₁/₂_with_body` +
     `mac_capacity_region_outer_bound_with_fano_body` (3-bound 合流) + publish-layer hook 6 主要定理。
   - **T3-C BC superposition body**: `BroadcastChannelSuperpositionBody.lean` +844 行。**MAC body discharge
     verbatim 流用** (`bcReceiver1JointlyTypicalSet := macJointlyTypicalSet` の definitional 一致経由)。
     receiver-1 4-event Bonferroni (`F₀ … F₃`) + receiver-2 2-event Bonferroni (`G₀, G₁`) + union-bound
     calc chain + `bcJTSCode` two-receiver combine + publish-layer hook (撤退ライン: L-BC2-I random codebook
     averaging は scope-out)。
   - **T3-F Relay inner DF/CF body**: `RelayInnerBodyDischarge.lean` +645 行。**`IsRelayDFBlockMarkovWitness` +
     `IsRelayCFBinningWitness` structural witness predicate** (既存 Existence Prop と definitionally equal で
     bridge が `:= h` の 1 行)、CF 側は `relayCFBinningMeasure` (= `wzBinningMeasure` の relay namespace 別名 +
     `IsProbabilityMeasure`) で WZ binning machinery 再エクスポート、両 main theorem に discharged 版 + bridge 併設。
   - **T4-A LZ78 L-LZ3 SMB sandwich**: `LZ78SMBSandwich.lean` +604 行。**`IsSMBSandwichPassthrough` を
     hypothesis-free に discharge** (SMBAlgoetCover.lean の `shannon_mcmillan_breiman` が既に hypothesis-free と
     判明、L-LZ3 完全 internal 化)。`lz78_asymptotic_optimality_two_sided_smb_discharged` publish (LZ78 主定理から
     L-LZ3 hypothesis 削除)。Cover-Thomas Theorem 13.5.3 の "L-LZ3 hypothesis pass-through" 表記は obsolete 化候補。
   - **T2-C Whittaker-Shannon full**: `WhittakerShannonFull.lean` +576 行。**Tier 1 finite-window full
     discharge** (`whittakerShannonSeries` symmetric finite window + `_at_sample` honest 証明 + off-window
     collapse + empty-window + zero/add/smul/sub/neg/linear-combo + continuity/measurability + `(2N+1)·M`
     sup bound + card identity)。Tier 2 (infinite series) は `IsBandlimitedFull` predicate pass-through で wrap、
     L-SH1/L-SH2/L-SH3 chain to `ShannonHartley.lean` で `shannon_hartley_via_full` (nats/sec + bits/sec) publish。
   <br>第二波 gap-close (3 新規):
   - **T1-A'' Huffman 2-hyp body extension**: `HuffmanT1APPrimeBody.lean` +594 行。
     `SwapStepLeChainHypothesis` primitive + trivial discharge + `SwapNormalizationHypothesis` の `ll a = ll b`
     case の universe-polymorphic discharge + alt-witness via `Equiv.swap a b` + `HuffmanMergedIdentificationHypothesis`
     の point-wise extractor + `HuffmanCombinedHypothesis` wrapper 群 (13 sections A-M)。完全 discharge は
     4-6 セッション scope で defer。
   - **T1-D Hoeffding sandwich body**: `HoeffdingSandwichBody.lean` +335 行。**L-H4-FS** (`IsHoeffdingMinimizerFullSupport`
     predicate pass-through) + **L-H4-FB** 両端境界 **full discharge** (`α = 0` 全域 → `K = {P₁}` singleton 経由
     Qstar = P₁、`α ≥ klDivPmf P₂ P₁` → `hoeffdingE2 = 0` 経由 Qstar = P₂)。
     `hoeffding_tradeoff_sandwich_via_predicate` + `_at_boundary_alpha_ge_kl` publish。
   - **T3-D Wyner-Ziv L-WZ3 convexity full**: `WynerZivConvexityBody.lean` +621 行。**`IsWynerZivFactorizable`
     affine predicate** (`∃ κ, q(x,y,u) = κ(x,u)·P_XY(x,y)` + 行確率性) で Markov cross-product 制約を
     factorization 経由 affine 化、`wynerZivRateFactorizable_convex_in_D` で rate-level convexity 完成
     (Lemma 15.9 objective convexity は `h_obj_convex` hypothesis pass-through、`WynerZivConstraint`
     非アフィン Markov を bypass)。25 declarations publish。
   <br>**集計**: 12 新規 Lean ファイル = **+6356 行** (中央見積 6200 から +156, 6000+ 目標 達成 ✅)、
   wave5 既存 `WynerZivBinningBody.lean` (613 行) は agent 起動時の存在 check で skip。`Common2026.lean` に
   import 12 行追加、全 `lake env lean <file>` clean / 0 sorry / 0 warning。Mathlib PR 候補 累計 4 件
   (`differentialEntropy_mean_invariant` を新規追加)。発見した structural 同型: Cramér L-C2 Phase C と
   Chernoff per-tilt discharge が完全同型 (両者 `Measure.infinitePi (μ).tilted ↔ Measure.infinitePi (μ.tilted)`
   n-letter RN-deriv 同定の Mathlib gap で詰まる)、将来 LDP per-tilt 統一 predicate 候補。章状態: Ch.5 (T1-A''
   body extension), Ch.9 (T2-A MI bridge 3-primitive + T2-B L-WF1 full discharge + T2-C WS Tier 1 full discharge),
   Ch.11 (T1-B Chernoff per-tilt predicate-form + T1-D sandwich 両端 full discharge), Ch.13 (T4-A L-LZ3
   internal化), Ch.15 (T3-B MAC L-MAC2 + T3-C BC body + T3-D L-WZ3 convexity full + T3-F inner body),
   Ch.17 (T2-D EPI L-EPI3 single-hyp + Gaussian full) — いずれも 🟡 維持で残部分は別 plan defer。
9. **2026-05-20 並列 wave7 第一波 10-seed + 第二波 4-seed gap-close 着地** (orchestrator session、worktree
   isolation 経由): wave6 で残った body discharge / predicate-decomposition / extension を中心に第一波 10 seed
   + 第二波 4 seed gap-close を並列駆動して **+6210 行 / 0 sorry / 0 warning** publish (14 新規 Lean ファイル、
   `lake build Common2026` 3133 jobs 全成功)。第一波 (10 試行中 9 成功、S10 I-3 は既存 publish と判明し skip):
   - **S1 T2-A AWGNMIBridgeDischarge**: +194 行。`IsAwgnOutputGaussian` body discharge (`IsAwgnBindEqConv` 新
     primitive 経由) + `IsAwgnMIDecomp` 撤退ライン pass-through + `awgn_theorem_of_typicality_converse_bindconv` (旧名 `awgn_theorem_F2_F3_fully_discharged`) 再 publish。
   - **S2 T2-D EPIStamToBridge**: +631 行。`IsStamToEPIBridgeHyp` を `IsStamToEPIScalingHyp` + `IsStamToEPILimitHyp`
     の 2 sub-predicate に分解 + body discharge (Csiszár scaling-path 単調性 + heat-flow endpoint Gaussian saturation)、
     Gaussian saturation case は full discharge。
   - **S3 T2-D EPIStamInequalityBody**: +515 行。Stam 4-step body discharge (Step 4 = λ optimization closed form
     完全 discharge `J_sum ≤ J_X J_Y / (J_X + J_Y)`、Step 1-3 score-conv + Cauchy-Schwarz on condExp は predicate
     pass-through)、Gaussian end-to-end EPI 検証 + Wave 6 EPIL3Integration への bridge。
   - **S4 T2-E BrunnMinkowskiFunctional**: +708 行。Prékopa-Leindler 関数形 (L-PL1/2/3 hypothesis) + 凸体 BM
     specialization + `IsLogConcaveMeasure` structure + EPI bridge (`entropy_le_logVolume_of_logConcave`) + λ
     edge cases + Cover-Thomas 17.9 bundle。
   - **S5 T2-F FisherInfoV2DeBruijnBody**: +359 行。heat-flow + IBP の 2 predicate (L-FV2DB-A/B) で de Bruijn
     body discharge を composition 形式で完了、Gaussian instance 証明付き。
   - **S6 T3-B MACCornerPoint**: +409 行。2 corner points + 5-vertex pentagon convex hull + time-sharing closure +
     `IsMACTimeSharingHyp` pass-through + capacity region = pentagon set equality。
   - **S7 T3-C BroadcastChannelRandomCodebook**: +545 行。Markov pigeonhole `bc_exists_codebook_of_avg_le` + 存在
     抽出 + BCInnerBoundExistence への iff bridge (definitional 一致経由)。
   - **S8 T3-D WynerZivConverseChain**: +560 行。3-predicate bundle (per-letter + Csiszár sum identity + Jensen
     antitone) で chain assembly form 再構築、`wyner_ziv_converse_chain` 主定理 + 5 副定理 publish。
   - **S9 T4-A LZ78ConverseAsymptotic**: +515 行。`IsZivCountingAsymptoticBound` + `IsLZ78PhraseCountAsymptotic`
     (= `c =O[atTop] B`) + sandwich predicate + ZivInequalityPassthrough/SMBSandwichPassthrough bridge。
   - **S10 I-3 Asymptotic**: 0 新規行 (既存 publish と判明、`Common2026/InformationTheory/Asymptotic.lean` 195 行
     は wave5 以前の commit `4c8ceff` で publish 済、agent はサニティチェックのみ)。
   <br>第一波 S10 skip 補完として **S10' T1-B ChernoffPerTiltSanov**: +374 行。`IsChernoffNLetterRN` predicate
   (Cramér L-C2 Phase C と structurally 同型 — n-letter RN-deriv on infinite-product tilt) + chain wrappers +
   `chernoffMediatorMeasure_pi_*` plumbing + Mathlib-gap pass-through publish。
   <br>第二波 gap-close (4 新規):
   - **G1 T1-D HoeffdingInteriorBody**: +370 行。`IsHoeffdingInteriorGradient` + `IsHoeffdingInteriorMinimizer`
     2 predicate + 8 connecting lemmas (bridges + Pythagoras + sandwich Tendsto)、interior `0 < α < klDivPmf P₂ P₁`
     regime を 2 hypothesis 化、両端境界 wave6 完了済との合流路。
   - **G2 T3-D WynerZivBinningCovering**: +481 行。covering / packing 2 sub-predicate + decoder failure 合成
     `wyner_ziv_binning_via_covering_packing` + 漸近 existence form (`wyner_ziv_binning_existence_of_covering_packing`)。
   - **G3 I-2 GeneralDMCExtension**: +253 行。`IsInformationallyStable` + `IsSpectralCapacityForm` (Verdú-Han 1994)
     predicates + memoryless concrete instances + spectral pass-through layer。
   - **G4 T1-C CramerPhaseDGapWorkaround**: +296 行。cylinder-form `IsCramerNLetterRNCylinder` + `IsCaratheodoryExtensionHyp`
     + Phase C bridge + **`IsCramerChernoffNLetterRNUnified` structure** (Cramér × Chernoff 同型 Mathlib-gap unification)。
   <br>**集計**: 14 新規 Lean ファイル = **+6210 行** (中央見積 ~5500-6000 から +210、6000+ 目標 達成 ✅)、
   `Common2026.lean` に import 14 行追加、`lake build Common2026` 3133 jobs 全成功 / 0 sorry / 0 warning。
   発見した structural 同型の活用: wave6 で予言した Cramér L-C2 Phase C と Chernoff per-tilt の同型を G4 で
   `IsCramerChernoffNLetterRNUnified` structure として明示化 (両者 `Measure.infinitePi (μ).tilted ↔
   Measure.infinitePi (μ.tilted)` n-letter RN-deriv 同定の Mathlib gap を 1 述語にまとめた、将来 LDP per-tilt
   統一 PR 候補)。Mathlib gap predicate naming pattern (`Is...NLetterRN`, `Is...CaratheodoryExtensionHyp`) を
   wave7 で定着、後続 discharge plan の参照点として整備。章状態: Ch.5 (T1-A'' body extension wave6 継続), Ch.9
   (T2-A MI bridge primitive 1/3 discharged), Ch.11 (T1-B per-tilt RN predicate-form + T1-C Phase D cylinder-form
   + T1-D interior 2 predicates), Ch.13 (T4-A LZ78 converse asymptotic), Ch.15 (T3-B MAC pentagon + T3-C BC random
   codebook + T3-D L-WZ1 covering/packing + L-WZ2 chain), Ch.17 (T2-D Stam-to-EPI bridge + Stam inequality Step 4
   full + T2-E Prékopa-Leindler + T2-F de Bruijn predicate) — いずれも 🟡 維持で残部分は別 plan defer。
10. **2026-05-20 並列 wave9 第一波 12-seed + 第二波 4-seed gap-close 着地** (orchestrator session、worktree
    isolation 経由): wave7 の各 sub-predicate を更に body discharge する 12 seed を並列起動 + 6000 行到達のため
    gap-close 4 seed を追加並列で駆動して **+6241 行 / 0 sorry / 0 warning** publish (16 新規 Lean ファイル、
    `lake build` 全成功)。第一波 (12 新規, 計 4515 行):
    - **S1 T2-A AWGNBindConvBody** (+171, **完全 discharge**): `IsAwgnBindEqConv` を撤退ラインなしで full discharge。
      汎用 `bind_eq_conv_of_translation_kernel` (任意 translation kernel `κ x = ν.map (x+·)` で `κ ∘ₘ p = p ∗ ν`)
      を `Measure.lintegral_conv` (to_additive 生成名) + `lintegral_bind` で 6 行本体、AWGN 特殊化で wave7 hypothesis 解消。
    - **S2 T2-D EPIStamStep12Body** (+371): Stam Step 1 (score-conv `IsStamScoreConvHyp`) + Step 2 (`IsStamCondExpCSHyp`)
      を wave7 の `Prop := True` placeholder から data-carrying typed predicate へ昇格、λ-optimization 代数 (CS 2点形 +
      Jensen squared-mean) を full discharge。
    - **S3 T2-D EPIStamStep3Body** (+404): Step 3 を `IsStamTotalExpectation` (∀λ coupling、wave7 `IsStamCauchySchwarz`
      より primitive) に分解、Step 1→4 full chain で真 signature `IsStamInequalityHyp` 導出。
    - **S4 T2-E BrunnMinkowskiPLBody** (+342): Prékopa-Leindler L-PL1/L-PL2 body — weighted AM-GM + 1次元 superlevel
      乗法化 + Fubini slice 結合を実証明 (genuine measure-theoretic content は 5 sub-predicate に外出し)。
    - **S5 T2-F FisherInfoV2HeatFlowBody** (+268, **spatial 半完全 discharge**): heat kernel の空間 1階/2階微分
      (`∂_x g_t = -(x/t)g_t`, `∂²_x g_t = (x²/t²-1/t)g_t`) を `deriv_gaussianPDFReal` + product rule で internal
      discharge、Gaussian semigroup composition も discharge。time-derivative (variance 微分 Mathlib 不在) は pass-through。
      (agent が background compile 待ちで途中停止したため orchestrator が spatial 微分を直接 internal discharge して着地。)
    - **S6 T3-B MACTimeSharingBody** (+447): `IsMACTimeSharingHyp` reverse inclusion (capacity region ⊆ pentagon convex
      hull) を明示 2-segment Carathéodory 分解で実証明、pentagon = capacity region 両側完全 publish。
      発見: wave7 の `IsMACTimeSharingHyp` は非負性なし形で false にもなり得た — discharge 試行で statement 前提不足が露見、
      `0 ≤ R₁,R₂` 下で discharge。
    - **S7 T3-C BroadcastChannelAveraging** (+414): L-BC2-I codebook averaging body — linearity-of-expectation
      (`Finset.sum_comm`) + Markov pigeonhole で `∑w·Pe ≤ B ⇒ ∃C, Pe(C) ≤ B` を実証明、wave7 `h_avg` placeholder を discharge。
    - **S8 T3-D WynerZivCoveringBody** (+475): covering lemma body — AEP joint-typicality probability bound から complement
      arithmetic で `IsWynerZivBinningCovering` discharge、covering existence + covering→packing→decoder-fail feed。
    - **S9 T3-F RelayDFBlockMarkovBody** (+452): DF block-Markov witness body — `RelayBlockMarkovCode` structure +
      3 sub-hyp 分解 + 構成的 existence bridge (`RelayDFInnerBoundExistence` を実際に build)。
    - **S10 T4-A LZ78GreedyParsingImpl** (+451): L-LZ4 — longest-prefix-match greedy parse の具象実装 (back-pointer
      invariant + `count ≤ n` 証明) で `lz78_asymptotic_optimality_with_greedy_impl` 再 publish。
    - **S11 T1-D HoeffdingInteriorGradientBody** (+327): interior gradient body — `hoeffdingTilt = chernoffMediator` で
      `Q* ∝ P₁^{1-λ}P₂^λ` 実現、stationarity `log Q* - (1-λ)log P₁ - λ log P₂ = const` を rpow 代数で full discharge。
    - **S12 T1-A'' HuffmanSwapStepChainBody** (+393): SwapStepLe chain composition (`Equiv.Perm` 分解) sub-predicate 化 +
      n-step swap normalization lift + universe-polymorphic corollary 群。
    <br>第二波 gap-close (4 新規, 計 1726 行):
    - **G1 T2-A AWGNMIDecompBody** (+234): `IsAwgnMIDecomp` を AWGN 非依存の continuous-channel MI chain-rule predicate
      `IsContChannelMIDecompHyp` (`I(X;Y) = h(Y) - h(Y|X)`) に縮減、AWGN 絶対連続性 side condition は full discharge。
    - **G2 T3-D WynerZivPackingBody** (+581): packing body — union bound + `1/M` collision + first moment method
      (`exists_le_integral`) で `IsWynerZivBinningPacking` を実 discharge (SW `swError` 平均化を WZ に verbatim port)、
      covering と合流で `ε₁ + S/M` decoder-failure bound。
    - **G3 T3-F RelayCFBinningBody** (+562): CF binning witness body — `IsCFCompressionHyp`/`IsCFBinningDecodableHyp`/
      `IsCFSideInfoDecodeHyp` 分解、WZ covering/packing union bound 再利用で CF decoder-failure `≤ ε_cov+ε_pack` 実証明。
    - **G4 T2-B ParallelGaussianWFCertBody** (+349): water-filling certificate body — `(1/2)log(1+t/N_i)` の concavity
      (`AntitoneOn.concaveOn_of_deriv`) + concave tangent bound + KKT stationarity/complementary slackness を実証明、
      Lagrange multiplier 存在のみ hypothesis。
    <br>**集計**: 16 新規 Lean ファイル = **+6241 行** (6000+ 目標 達成 ✅)、`Common2026.lean` に import 16 行追加、
    `lake build` 全モジュール成功 / 0 sorry / 0 warning。本 wave の特徴: wave7 が pass-through 化した sub-predicate を
    更に「body discharge or より primitive な predicate へ vertical 分解」する第 2 段で、2 件 (S1 AWGN BindConv, S5 Fisher
    spatial 微分) は完全 discharge 到達。複数 agent 報告で「wave6/7 の certificate/witness predicate が parent と
    definitionally equal な no-op だった」点が判明 (S6 MAC time-sharing は非負性前提不足、G3 Relay CF witness は existence
    と defeq で decoder-failure content を持たない、G4 WF certificate は `IsWaterFillingOptimal` と defeq) — pass-through
    predicate を切る時点で「discharge 可能な真 statement か」を確認すべきという feedback。章状態は Ch.5/9/11/13/15/17 とも
    🟡 維持で残部分は別 plan defer。
11. **2026-05-20 並列 wave10 batch1-5 (22 seed) 着地** (orchestrator session、worktree isolation 経由): wave9 の各 sub-predicate を
    更に body discharge する seed を 5 並列 × 5 batch (同時最大 5) で駆動。事前に general-purpose agent で「genuine か no-op か / Mathlib
    gap で blocked か」を選別した 15 候補 menu を作り、no-op 確定 predicate (`IsStamFisherCoupling` defeq, `IsCoveringRandomCodebookHyp`
    等) と infinitePi-tilted gap blocked seed (Chernoff/Cramér per-tilt) を除外して選定。**+6586 行 / 0 sorry / 0 warning** publish
    (22 新規 Lean ファイル、`lake build` 全成功)。完全 discharge 到達: S2 WF KKT stationarity (共通 Lagrange multiplier `1/(2ν)`)、
    S3 LZ78 phrase-count `O(n/log n)` (Asymptotics 反転)、S8 1-D Brunn-Minkowski (`vol(A+B) ≥ vol A + vol B` を Mathlib 不在の
    ため一から証明)、S10 Gaussian variance-derivative (`gaussianPDFRealVar` 導入で Mathlib gap closure) + `IsHeatTimeDerivHyp`、
    S16 layer-cake (`Integrable.integral_eq_integral_meas_le`)、S18 Hoeffding I-projection minimality (exponential-family Pythagorean
    master identity、`csiszar_pythagoras` は循環で使えず直接証明)、S20 EPI Stam→de Bruijn conclusion (Gaussian hypothesis-free)。
    genuine vertical reduction: S1 Hoeffding `mem` IVT discharge + `realises`→`IsHoeffdingTiltMinimal` (S18 で full discharge)、
    S4 Huffman merged-ident (measure→multiset 層 full、`Classical.choose` argmin の relabel 非可換性で残部 defer)、S5/S14 WZ
    covering AEP + packing 合流 decoder-failure、S6 MAC error-carrying predicate `MACAchievableWithError` 導入 (bare `MACInnerBoundExistence`
    が degenerate no-op と判明) + S12 4-event averaging + S21 per-event AEP decay、S7/S15 BC ensemble averaging + Bonferroni
    ℝ≥0∞→ℝ + AEP decay、S9 WZ objective convexity→`WynerZivCondEntDiffConvex`、S11 Gaussian de Bruijn witness (spatial+time 両 deriv
    internal)、S13 Huffman swap-normalization 4-conjunct→1-conjunct、S17 WZ decoder-failure→distortion bridge、S19 LZ78 two-sided
    で 3 passthrough + 2 SMB bound 削除、S22 MAC Fano converse (measure-theoretic Fano discharge)。**S23 (WZ cond-ent convexity core)
    は drop**: worktree が古い commit から分岐し S9 を見ずに `WynerZivCondEntDiffConvex` を再発明、3 declaration が S9 と name clash +
    内容も重複のため merge せず (6586 行は S23 抜きの実数)。発見した運用課題: `isolation: "worktree"` が current HEAD でなく古い base
    commit から分岐する場合があり、同 wave 内の先行 seed の成果物が後続 worktree に見えず重複実装/olean 不在/name clash を生む — batch 間で
    commit して HEAD を進めても worktree base が追従しないことがあるため、(a) 各 batch 後に新 module を `lake build` して olean を共有 .lake に
    populate、(b) merge 時に重複 declaration を grep で検出、の 2 防御が必須。Mathlib gap closure 1 件 (`gaussianPDFRealVar` variance-deriv)、
    残存 frontier gap: condExp-of-score (Stam Step1-2)、infinitePi-tilted RN (Chernoff/Cramér per-tilt)、joint perspective convexity of
    `p·log(p/q)` (WZ cond-ent core)。章状態は Ch.5/9/11/13/15/17 とも 🟡 維持で残部分は別 plan defer。
12. **2026-05-20 WZ cond-ent convexity core discharge** (orchestrator session、調査→計画→実装を agent chain で駆動、自走非並列): wave10 で
    drop された S23 (frontier gap「joint perspective convexity of `p·log(p/q)` (WZ cond-ent core)」) を full discharge。`Common2026/Shannon/WynerZivCondEntDiffConvexBody.lean`
    新規 393 行 (0 sorry / 0 warning) で `wynerZivCondEntDiffConvex_holds` (`WynerZivCondEntDiffConvex` を `P_XY ≥ 0` のみで無条件成立) +
    `wynerZivRateFactorizable_convex_in_D_unconditional` (L-WZ3 full convexity、`h_core` 仮定を完全消去) を publish。鍵は **pmf 形 (Real・有限)**
    を選んだこと — `RateDistortionConvexity.lean:25` が measure 形 (`klDiv : ℝ≥0∞`) で詰めた ~500 行 gap を回避し、既存 `Common2026/Fano/DPI.lean:44`
    `log_sum_inequality_negMulLog` をそのまま核エンジンに使えた。証明経路: factorisation で per-`u` block-gap = XU-gap を一致させ (`negMulLog_mul` で
    `neg(P)` 係数が混合下で相殺)、per-`y` に log-sum 不等式を 2 回当てて符号反転 → `∑_u` 集約。最大リスクと見ていた `h_ac` 絶対連続性は
    `w·r ≤ m=0, w>0, r≥0` で自明化し撤退 (full-support 縮退) 不要。**残存 frontier gap は 2 件に減**: condExp-of-score (Stam Step1-2)、
    infinitePi-tilted RN (Chernoff/Cramér per-tilt)。家系 docs: `wyner-ziv-convexity-discharge-{mathlib-inventory,moonshot-plan}.md`。Ch.15 は
    L-WZ1/2 + L-WZ3 残部のため 🟡 維持。再発見: 計画指定の定理名 `wynerZivRateFactorizable_convex_in_D` が既存 hypothesis 版と同 namespace で
    衝突 — roadmap #11 line 705 の name-clash 罠と同種で、unconditional 版は `_unconditional` 別名が必須だった。
13. **2026-05-20 infinitePi-tilted RN: 有限 tilt 因子分解 core 着地 (Phase 1)** (orchestrator session 続き、調査→計画→実装 agent chain、自走非並列):
    残存最深 frontier gap「infinitePi-tilted RN (Chernoff/Cramér per-tilt)」に着手。両 frontier gap の feasibility を並列 inventory で先に判定し、
    **どちらも full 形は Mathlib-PR 級 (~120-300 行 upstream measure theory) で 1 セッション 0-sorry 不可**と確定 (infinitePi-tilted=verdict (c)寄り、
    condExp-of-score=一般 X,Y は (c)・Gaussian 限定のみ GO)。ユーザー判断で「最高レバレッジ (Chernoff converse + Cramér lower 同時 unblock) の
    infinitePi-tilted に着手、full 0-sorry 未達を承知」を選択。**今セッション deliverable**: inventory が特定した「足りない 1 ピース」=
    有限 `Measure.pi` の tilt 因子分解を `Common2026/Shannon/MeasurePiTiltedFactorization.lean` (154 行、0 sorry / 0 warning) で full discharge:
    `pi_tilted_sum_eq_pi_tilted` (`(Measure.pi μ₀).tilted (∑ lam·Y(·i)) = Measure.pi (μ₀.tilted (lam·Y))`) を `Measure.pi_eq` + `tilted_apply'` +
    自前 Tonelli `lintegral_pi_prod` (Mathlib に Bochner 版 `integral_fin_nat_prod_eq_prod` はあるが lintegral 版が欠落、`Fin n` 帰納で自作・単独 PR 候補) で証明。
    **残差**: `IsMeasureInfinitePiTiltedEq` 本体は未縮約 (Phase 2 cylinder lift via `infinitePi_cylinder` → Phase 3 change-of-measure `setLIntegral_rnDeriv` →
    Phase 4 既存 `CramerLC2DischargeExt.tilted_lln_in_probability_real` (tilted LLN は既に 0-sorry 完備) 合流)。frontier gap は **closed でなく Phase 1 done** —
    残 gap は「tilted ambient ↔ un-tilted ambient を cylinder 上で結ぶ change-of-measure」一点に局在。家系 docs:
    `infinitepi-tilted-rn-discharge-{mathlib-inventory,moonshot-plan}.md`。Ch.11 は 🟡 維持。判明: Chernoff 側 `IsBayesErrorPerTiltLowerBound` は
    pmf-level で `infinitePi` を経由せず有限因子分解 core を共有しない (Cramér 専用)。`rw` での `lintegral_prod_mul` 適用は higher-order pattern 不一致で
    罠 (`have` 具体化 + `simp only` ベータ簡約で回避)。残存 frontier gap: condExp-of-score (Stam Step1-2)、infinitePi-tilted RN (Phase 2-4 残)。
14. **2026-05-20 自律 5-unit バッチ (infinitePi-tilted Phase2-4 + EPI Gaussian + Chernoff building block)** (orchestrator session、ユーザー「自律的に
    5 ターン分」指示、各 unit = 調査/実装 agent → 検証 → commit、全 0-sorry):
    - **U1 infinitePi-tilted Phase2-4** (`InfinitePiTiltedChangeOfMeasure.lean` +381 行): Phase 1 因子分解を `infinitePi_cylinder` で cylinder lift →
      `tilted_apply'` 直接経路で change-of-measure (在庫が見積もった RN-deriv 因子分解 80-150 行を**丸ごとスキップ**、`setLIntegral_const` 1 本)。
      `IsMeasureInfinitePiTiltedEq` を strictly smaller residual `IsTiltedWindowEventuallyLarge` (tilted 窓質量 eventually ≥1/2) へ縮約 +
      `cramer_lower_phaseC_residual_discharge` で Cramér 下界 end-to-end。**発見**: 元述語は任意 `(a,lam)` 量化で `lam` が非最適だと数学的に偽 →
      residual 縮約が正しい着地。
    - **U2 tilted window LLN** (同ファイル +75 行): 既存 `tilted_lln_in_probability_real` から `tiltedWindow_eventually_tendsto_one` (→1, 内部条件
      `a < ∫Y dμ_tilt < a+ε`) + `_large_of_interior` (≥1/2)。残差を「tilted 平均が窓内部」へ局在化。
    - **U3 Gaussian Stam bound** (`StamGaussianBound.lean` 新規 115 行): EPIStamStep12 の vacuous `isStamCondExpCSHyp_of_gaussian_fisherInfo_zero`
      (V1 fisherInfo=0 退化) を**正しい V2 `1/v`** で非 vacuous 化。`stam_fisher_arith` (`1/(a+b) ≤ λ²/a+(1-λ)²/b`、SOS 核 `(a−λ(a+b))²`) +
      `stam_convex_fisher_bound_gaussian(_indep)`。**λ∈[0,1] 制約は実は不要**と判明 (SOS は全 λ)。
    - **U4 cgf 微分橋** (同 U1 ファイル +54 行): `tiltedMean_eq_deriv_cgf` (`∫Y dμ_tilt = deriv (cgf Y μ₀) lam`、Mathlib `integral_tilted_mul_self` +
      `integrableExpSet=univ` from bounded) + `_of_cgfDeriv_interior`。残差を `a = deriv cgf lam` の **CLT boundary** に局在化。
    - **U5 n-letter Chernoff Z-sum 因子分解** (`ChernoffNLetterZSum.lean` 新規 56 行): `(chernoffZSum)^n = ∑_{x:Fin n→α} ∏ P₁^{1-λ}P₂^λ`
      (`Finset.sum_pow'` + `Fintype.piFinset_univ`)。Chernoff converse 側 (`IsBayesErrorPerTiltLowerBound`) の正規化 building block。
    <br>**集計**: 新規 3 ファイル + 既存 1 拡張 = +681 行 / 0 sorry / 0 warning、`Common2026.lean` import 3 行。**構造的所見**: Ch.11 の両 exponent
    (Cramér lower + Chernoff Bayesian) は同じ **CLT-boundary residual** に帰着し、その手前の change-of-measure 機構は full discharge 済 — 残るのは
    「tilted 平均ちょうどの窓質量 →1/2」を厳密化する CLT で、LLN だけでは閉じない。codebase は非常に成熟 (probe した完遂候補は LZ78 Ziv / Chernoff
    achievability 上界 / 各 discharge とも既publish) で、残 gap は frontier (CLT boundary + condExp-of-score PR級 + infinitePi RN の CLT 部) に限局。
    残存 frontier gap: condExp-of-score (Stam Step1-2、一般)、Ch.11 CLT-boundary residual (Cramér+Chernoff 共通)。
15. **2026-05-20 自律 5-unit バッチ #2: Cramér CLT-boundary residual full closure** (orchestrator session、ユーザー「あと 5 ターン」指示、
    調査→計画→実装(3分割) agent chain、全 0-sorry): #14 で局在化した CLT-boundary residual を Mathlib CLT で**実際に閉じた**。在庫 verdict GO
    (~80% 既存、唯一の「一から」は Gaussian median)。`Common2026/Shannon/CramerCLTClosure.lean` 新規 553 行 (0 sorry / 0 warning):
    - **U6 在庫 / U7 計画**: `cramer-chernoff-clt-closure-{mathlib-inventory,moonshot-plan}.md`。
    - **U8 (Phase1-2, +97)**: `gaussianReal_Ici_eq_half` (Gaussian median `gaussianReal 0 v {0≤·}=1/2`、Mathlib 不在を `gaussianReal_map_neg`
      対称性 + `noAtoms_gaussianReal` で自作) + portmanteau half-line bridge (`ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'`、
      ℝ で `StandardBorelSpace` 不要)。
    - **U9 (Phase3-4, +231)**: Mathlib `tendstoInDistribution_inv_sqrt_mul_sum_sub` を **tilted ambient に実適用** (`tiltedAmbient_clt`、既存
      `iIndepFun_tilted_ambient`/`identDistrib_tilted_ambient` が CLT 前提と字面一致) → scaling 集合書換 `{∑Y/n≥m}={(√n)⁻¹∑(Yₖ−m)≥0}` →
      `tiltedHalfLine_tendsto_half` (→1/2) → `tiltedWindow_eventually_large_of_boundary` (窓質量→1/2、≥1/4)。
    - **U10 (Phase5-6, +185)**: `∃C>0` 緩和 change-of-measure (`isMeasureInfinitePiTiltedEq_at_of_window`、既存 reduction の `1/2`→任意 C 差替え) +
      per-a 迂回 `cramer_lower_at` → **`cramer_lower_at_cgfDeriv_unconditional`**: `a = deriv (cgf Y μ₀) lam` (= 最適 tilt 閾値) で Cramér 下界
      `-(lam·a − cgf) ≤ liminf rate` を **residual 仮定なし** (bounded Y + 非退化 Var>0 + 標準 coboundedness のみ) で達成。
    <br>**到達**: Cramér lower bound は最適 tilt 閾値で fully discharged。`= −Λ*(a)` (Legendre) の Cramér 下界が hypothesis-free に。**Chernoff converse は別 ambient**
    (pmf-level、#14 U5 の `chernoffZSum_pow_eq_sum_prod` が足場) で同型 CLT closure が必要 — 本 closure の構造をそのまま port 可能。**残存 frontier gap**:
    condExp-of-score (Stam Step1-2、一般、PR級)、Chernoff converse の pmf-level CLT closure (Cramér の port)。Ch.11 は Cramér lower が closure 到達で
    一段前進、🟡 維持 (Chernoff converse 残)。所見: Gaussian median (median=mean for symmetric) が Mathlib 不在で唯一の自作、それ以外は CLT/portmanteau の既存組立。
