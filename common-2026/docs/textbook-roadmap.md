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

> **2026-05-25 改訂**: Definition of Done が **type-check done / proof done の 2 段階** に変更
> (CLAUDE.md「Definition of Done — 2 段階」)。「proof done = 0 `sorry` ∧ 0 `@residual`」が新バー。
> 撤退口は **`sorry` + `@residual(<class>:<slug>)`** のみ — 仮説に核を bundling する `*Hypothesis`
> predicate 形式 (旧 🟢ʰ load-bearing-hyp regime) は honesty defect として **禁止**。本ファイルの
> 既存記述 (`🟢ʰ` 表記、`@audit:suspect/staged`、`load-bearing-hyp 🟢ʰ = 未完` の文言等) は
> **legacy 状態の記録** であり、コード側の sorry-based 移行は別セッションに分割実施
> ([[sorry-based-migration]] メモ参照、`docs/audit/audit-tags.md`「Deprecated / 移行レシピ」)。

「Lean で verified な Cover & Thomas」を名乗るための必要条件:

- **Ch.2–5, 7–12, 15, 17 の主定理が proof done で publish 済み** (詳細は下記章対応表) ——
  proof done = `lake env lean <file>` 0 errors ∧ 0 `sorry` ∧ 0 `@residual`。
  regularity hypothesis (full-support / `IsFiniteMeasure` 等) は precondition なので proof done と両立する
  (下記「検証強度の基準」)。load-bearing hypothesis (証明の核心を抱える predicate) は **書いてはいけない** —
  該当箇所は `sorry` + `@residual(<class>:<slug>)` に書換 (移行作業)。
- **Typed RV API** が外向き API として揃い、教科書本文の statement が形式化版に直接対応する
- 各 seed が `docs/<family>/<topic>-moonshot-plan.md` で計画化され、phase 単位で archive 可能
- 主成果物 3 層 (library / API / 原稿) の各層に index と cross-link がある

### 検証強度の基準 (標準B、2026-05-25 改訂)

本プロジェクトの野心は **標準B = 各見出し定理が Mathlib 公理まで無条件に機械検証されている**こと。
教科書が読者にする約束を「構造の検証」(標準A) でなく「定理そのものの検証」に置く。

DoD は 2 段階 (CLAUDE.md「Definition of Done — 2 段階」):

- **type-check done** (commit OK): 0 errors、`sorry` warning は `@residual(<class>:<slug>)` 付き
- **proof done** (完成 = 標準B): 上記 + 0 `sorry` + 0 `@residual`

hypothesis の中身は以下で区別する:

- **OK (regularity-hyp)**: 仮説が *regularity / genericity* 条件 (full-support `hP`、
  `IsFiniteMeasure`、`IsProbabilityMeasure`、`Var > 0`、measurability 等) で、定理本体は真の定理のまま。
  これは Mathlib の補題でも普通に付く前提で、標準B でも **proof done と両立** する (🟢 / 🟢 regularity)。
- **禁止 (load-bearing hyp)**: 仮説が *証明の難所そのもの* (Stam 不等式、achievability の typicality、
  multi-user Fano、結論と同型の存在述語) を肩代わりする `*Hypothesis` / `*Reduction` / `IsXxxClaim`
  predicate。**書いてはいけない** — 該当残作業は `sorry` + `@residual(<class>:<slug>)` で表現する
  (CLAUDE.md「検証の誠実性」、`docs/audit/audit-tags.md`)。

判定の一言: **仮説を読んで「これは前提条件か、それとも証明の核心か」**。前者は OK、後者は禁止
(sorry+@residual で表現)。

> **legacy 注**: 本ファイルの 2026-05-21 以前の記述には「load-bearing-hyp 🟢ʰ = 未完 (残タスク)」
> という表現があるが、新方針では「load-bearing-hyp 状態は存在してはならない、該当箇所は sorry に
> 書換」というより強い制約に変わった。コード側の移行は [[sorry-based-migration]] で追跡。

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
| 11 | Information Theory and Statistics | 🟡 | `stein_strong_law`, `sanov_ldp_equality`, `Pinsker`, `CsiszarProjection`, `Chernoff.chernoff_lemma_achievability`, **`ChernoffBandMassDischarge.chernoff_lemma_tendsto_holds`** (✅ 標準B, regularity-only, sorryAx-free — full Thm 11.9.1, judgment #18), `HoeffdingTradeoff.hoeffding_tradeoff_with_hypothesis`, `CramerLC2DischargeExt.tilted_lln_ae` + `_in_probability_real` (T1-C Phase B partial discharge) | ~~T1-B per-tilt full discharge~~ ✅ done, **T1-C Phase C completion** (Mathlib gap `Measure.infinitePi_tilted_eq`), **T1-D Hoeffding tradeoff sandwich body** | ~1-1.7k |
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

> **標準B での 🟢ʰ の読み替え (2026-05-21)**: 「検証強度の基準」節の通り、🟢ʰ は仮説の中身で
> 二分される。**regularity-hyp の 🟢ʰ = 完成**、**load-bearing-hyp の 🟢ʰ = 未完 (残タスク)**。
> 下表で 🟢ʰ と書いた章も、残 honest 仮説が「証明の核心」なら標準B 的には 🟠 寄りの残作業。

### 「Mathlib 壁」の 4 分類 (2026-05-21、用語の曖昧さ解消)

ログ全体で「Mathlib 壁」が**性質の違う 4 種類**を一語に潰していたため、ここで分解する。標準B では
(d) 以外は原則 **やるべき残タスク**だが、突破困難度と投資規模が大きく異なる。

- **(a) 量の壁 — 難しくない、ただ未構築**: well-understood な確率論・測度論で紙では数行だが Mathlib に
  該当補題が無く `loogle` 0件 → 一から数百行。**突破困難度: 低**。投下セッション数の問題で、競合する
  formalizer なら確実に閉じる。該当: multi-user Fano + joint typicality (Ch.15 MAC/BC/Relay)、
  continuous AEP / typicality (Ch.9 AWGN F-2)、BM slice 上半連続性 (Ch.17、~150行自作)。
- **(b) 解析の壁 — 定型だが前提インフラごと無い**: 定理を証明する前に**計算体系自体を建てる**型。
  **突破困難度: 中〜高**。該当: condExp-of-score = Stam Step 1-2 → EPI body (Ch.17)。score function の
  条件付き期待値分解 + 積分記号下微分 + 部分積分 + L² 理論。Mathlib に微分エントロピー/Fisher 情報の
  解析体系が無く "PR 級 ~120-300行 upstream" 規模。
- **(c) 本物の数学的深さ — 行数でなく難易度**: **突破困難度: 高 (真の壁)**。該当: Nyquist 2W-DOF
  (Ch.9 Shannon-Hartley `h_two_w`)。教科書の「2W サンプル/秒」の厳密版は **prolate-spheroidal
  (Slepian-Pollak-Landau) による帯域制限信号空間の次元定理** で深い調和解析。**C&T 自身が厳密証明して
  いない** → 標準B でも「Shannon-Hartley を検証済みの目玉にするか / 次元論法を公理引用するか」の
  **scope 決断点**。連続 mutualInfo 加法性 `mutualInfo_pi_eq_sum` (Ch.9) は本物の測度論定理だが (c)
  の中では中難度。
- **(d) 「壁」が実は選択だったもの**: 過去ログで "ROI 無し" の婉曲表現に "Mathlib 壁" が使われた箇所。
  de-circularization sweep (2026-05-21) で結論≡仮説の偽装は全廃済。残るのは honest 開示済みのみ。
  判定基準: **ブロックされている (hard) のか、先送りしている (big) のか**。

| Ch. | headline の真の状態 | 区分 |
|---|---|---|
| 2 Entropy/MI/DPI | `MIChainRule`, entropy/DPI 一式 | 🟢 |
| 3 AEP | `source_coding_achievability`/`_converse` (iid honest hyps) | 🟢ʰ |
| 4 Entropy rate/SMB | `shannon_mcmillan_breiman` 無条件 (`SMBAlgoetCover.lean`)、`birkhoff_ergodic_ae` | 🟢 |
| 5 Data compression | ShannonCode/Kraft 🟢；Huffman 最適性 🟢ʰ (強形 `huffmanLength_optimal` は 📋)；**Arithmetic coding 🟢ʰ (RESOLVED 2026-05-20: SFE genuine discharge — `sfeLength`+prefix-free 構成 (`exists_prefix_code_of_kraft`→`finTwoEquiv` lift)+`H≤E[L]≤H+2`+unique decodability、0 sorry、honest 仮定は full-support `hP` のみ)** |
| 7 Channel capacity | `shannon_..._general_full` 無条件、feedback complete；一部 converse は honest pass-through (文書化済) | 🟢/🟢ʰ |
| 8 Differential entropy | `differentialEntropy_*` (Bochner honest hyps) | 🟢ʰ |
| 9 Gaussian channel | **AWGN 🟠 (F-2/F-3 は id-alias で実 discharge でない)；ParallelGaussian 🟢ʰ (2026-05-21: `parallel_gaussian_capacity_formula` を `:= h_per_coord` 完全 pass-through から **sup-sandwich** discharge へ。`ParallelGaussianPerCoord.lean`: achiever 側 (≥, Gaussian feasibility) genuine + water-filling (L-WF1/L-WF2 genuine) 結合。情報容量 (sSup of MI) なので continuous AEP 不要。上界 (≤) = MI 優加法性は **多変量 differential entropy + subadditivity が Mathlib 不在**のため honest 仮定 `IsParallelGaussianPerCoordRegularity` に外出し、1-D AWGN max-entropy と同水準。docstring の「continuous AEP 必要」誤記を修正)；Shannon-Hartley / Whittaker 🟢ʰ (2026-05-21: 証明可能なのに pass-through だった 2 circular を genuine 化 — `shannon_hartley_wideband_limit` を `Filter.Tendsto (bandlimitedAwgnCapacity · N₀ P) atTop (𝓝 (P/N₀))` として Mathlib `Real.tendsto_mul_log_one_add_div_atTop` で genuine 証明、`whittaker_shannon_one_point` を circular `recovered=f` 仮説撤廃し `whittaker_shannon_sample_collapse` で無条件証明。`shannon_hartley_formula` の残 honest = `h_two_w` (Nyquist 2W-DOF サンプリング = genuine Mathlib gap、honest-🟢ʰ pass-through)。sinc/full reconstruction は genuine)。NAME 整合 2026-05-20: AWGN/PG の `*_discharged` 名を honest 化 — F-2/F-3 (resp. per-coord L-PG1) が hypothesis として開いたままの top 定理を改名 (`awgn_theorem_F1F2F3_discharged`→`awgn_theorem_of_F2F3_hypotheses` 等) + ⚠️ docstring 付与。genuine 層 (F-1 / L-PG0 / L-WF1 IVT / L-WF2 concavity certificate) は不変。**<br>**MI 分解 bridge 基盤 (2026-05-21、共通土台): `ContChannelMIDecomp.lean` で連続チャネル `I(X;Y)=h(Y)−h(Y|X)` を genuine 化。linchpin `rnDeriv_compProd_fibre` (`(μ⊗ₘκ).rnDeriv(μ⊗ₘη)=ᵐ Kernel.rnDeriv κ η`、Mathlib 明示 TODO `Composition/RadonNikodym.lean:28-29`) を withDensity ルートで full 証明。一般 body `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` は genuine。AWGN instance `isContChannelMIDecompHyp_awgn` / `isAwgnMIDecomp_of_densitySplit` は **2026-05-21 に仮定なし化 (🟢)**: 残 honest 2本 (`h_meas_fibre` = Gaussian rnDeriv の joint measurability + `h_int_fibre_joint`) を **Route B = measurable PDF proxy** で discharge。閉形式 `gaussianPDF` の everywhere-joint measurability brick `measurable_gaussianPDF_uncurry` + `llr_compProd_prod_split` の proxy 緩和 (fibre 項を `g`/`hg_meas`/`hg_ae` で受け、proxy↔rnDeriv 橋は **積分内部のみ** — pointwise 再接着は measure-form rnDeriv の joint measurability を要し**循環**、一般 s-finite kernel ルートも Mathlib 不在で不可)。`IsAwgnMIDecomp` は MI 公式まるごと pass-through → **仮定なし genuine**。残るのは F-2 (操作的 typicality/continuous AEP、operational headline `awgn_channel_coding_theorem` 用) のみで、情報容量側 (MI 分解) は閉じた。**さらに closed-form 化を wiring**: `awgn_mi_gaussian_closed_form_of_out` / `awgn_capacity_closed_form_of_out` (ContChannelMIDecomp.lean) を新設し、`isAwgnMIDecomp_of_densitySplit` で `h_decomp`(=`IsAwgnMIDecomp`) を内部 discharge → `I = (1/2)log(1+P/N)` の closed form が `h_decomp` 仮定なしで成立 (残 honest = `h_out` Gaussian 畳み込み + `h_bdd` + `h_max_ent`)。**ParallelGaussian headline de-circularize 完了 (2026-05-21 session 2)**: published `parallel_gaussian_capacity_formula` は監査時点でまだ `:= h_per_coord` (結論≡仮説、circular) だった → genuine sup-sandwich を配線し、`IsParallelGaussianPerCoordRegularity` + water-filling KKT/opt 仮説 (≠結論) から `le_antisymm (≤)(≥)` で導出する honest-🟢ʰ headline (`ParallelGaussianPerCoord.lean`) に格上げ。旧 circular root は `parallel_gaussian_capacity_formula_of_perCoordReduction` に rename + ⚠️「NOT the headline」開示。残 honest = `IsParallelGaussianPerCoordRegularity` の `achiever_mi` (連続 `mutualInfo`/`mutualInfo_pi_eq_sum` が Mathlib 不在、1-D AWGN でも未 discharge) と `bddAbove` (genuine wall、1-D AWGN と parity)、`pi_withDensity` gap も多変量 Bayes split を honest 化。`h_decomp`(多変量 Fin-n 再導出 ~150-250行) と `h_perCoord` (`differentialEntropy_le_gaussian_of_variance_le` で可) は dischargeable だが headline は変わらない。L-PG1 (相関入力 MI 優加法性) は本 proxy brick を再利用して別途 (#6 wiring)。** |
| 10 Rate distortion | achievability 🟢ʰ、converse 🟢、convexity 🟢 (finite) |
| 11 Statistics | Stein/StrongStein/Sanov/Pinsker(weak+sharp)/Csiszar 🟢；Chernoff/Cramer (CLT closure 込, 真) 🟢ʰ；**Hoeffding tradeoff 🟠 + ⚠️DEF-FLAW (2026-05-21 発見): `steinTypeII_at_level_pmf` は *定数* Type-I level `alpha` を焼き込むが、tradeoff 曲線 `E₂(alpha)` は *指数* level `α_n=exp(-nr)` 領域でのみ極限。固定 α では Stein により `rate→D(P₁‖P₂)=E₂(0)` で α>0 では `E₂(alpha)<E₂(0)` ⟹ headline `rate→E₂(alpha)` は数学的に偽 (α=0/α>0 双方で反例)。full discharge には operational 量の指数 level 再定義が必須。<br>**✅ RESOLVED (2026-05-21): `HoeffdingTradeoffExp.lean` で指数 level 再定義 → full genuine closure。`steinTypeII_exp` (acceptance region = 経験型の KL-sublevel `E_r n={c|klDivIndex c n P₁≤r}`) + headline `hoeffding_tradeoff_exp : Tendsto (-(1/n)log steinTypeII_exp) → hoeffdingE2 P₁ P₂ r` を interior `0<r<klDivPmf P₂ P₁` で hypothesis-free / 0 sorry。converse=`sanov_ldp_upper_bound`(非摂動 Qstar)、achievability=`sanov_ldp_lower_bound_pointwise`(摂動 Qstar_ε=(1-ε)Qstar+εP₁, ε→0)、Qstar full-support=`exists_hoeffding_minimizer_full_support` (genuine 3-case)。全 genuine 既存資産の collapse、新規 Mathlib gap なし。定数α版は偽のため deprecated。** honest pieces (constructive 3-case minimizer 等) は `HoeffdingSandwichDischarge.lean`** |
| 12 Maximum entropy | `entropy_le_log_card` 🟢、Constrained 🟢ʰ |
| 13 Universal coding | **LZ78 🟢ʰ (2026-05-21 監査): full pass-through → 2 honest hyps `h_achiev`/`h_converse`、headline `lz78_two_sided_optimality_distinct_bdd_free` (LZ78DistinctEncoding.lean:412) は `#print axioms` で **sorryAx-free**。**SMB/ergodic 層は genuine 証明済** (`shannon_mcmillan_breiman` SMBAlgoetCover.lean:2840、Birkhoff `birkhoffAverage` から構築、sorryAx なし) — handoff の「residual=SMB bridge」は**不正確**、SMB は done。残 honest = **Ziv 不等式の entropy 層** (Cover-Thomas Lemma 13.5.5 + Eq.13.130: random parsing 上の entropy chain rule `H(Xⁿ)≤ΣH(phraseᵢ)` (L-LZ1-C) + log-sum/final Ziv (L-LZ1-D) + converse Eq.13.130 (L-LZ3-D))、~数百行の未記述 coding theory、**単一 Mathlib wall なし**。combinatorial 層 (phrase-count cardinality, c·log c≤Kn, c=O(n/log n))・SMB sandwich・glue は全 genuine。`IsZivInequalityPassthrough.of*` は `True.intro` placeholder で headline 未使用 (混同注意)。注: `Probability/TwoSidedExtension.lean` に skeleton `sorry` 残存だが SMB path は不使用 (headline sorryAx-free) — dead-code 確認余地)；Arithmetic 🟢ʰ (RESOLVED 2026-05-20、SFE genuine discharge — Ch.5 行参照)** |
| 15 Network IT | **genuine: SlepianWolf converse (X/Y/sum/single_shot, `MeasureFano`+chain) + full-rate-region achievability + Separation (両方向) + WynerZiv D-antitone fragment;** `wyner_ziv_tendsto` は honest `le_antisymm` combinator (🟢ʰ、結論 `R=R_WZ`≠両 hyp)。**2026-05-21 監査で circular DEFECT 7本を検出 → 同日 全修復済 (🟢ʰ honest-terminal)**: MAC/BC/Relay の outer+inner 7 headline (`mac_capacity_region_outer/inner_bound`, `bc_*_outer/inner_bound`, `relay_cutset_outer_bound`, `relay_df_inner_bound`, `relay_cf_inner_bound`) は旧 body が `:= h_rate_bound`/`:= h_existence` で**結論≡仮説** (実 IT residual は未使用 `: True` スロットに放置)、かつ inner `*Existence` 述語は error-prob bound を欠き任意 code で充足可だった。**修復**: (outer) entropy-level Fano + chain + cleanup 仮説から region/bound を `*_rate_le_of_fano`+`*_region_combine`/`relay_cutset_combine` で**導出** (結論を仮定にしない)。single-user 方向 (MAC per-user, BC R₂ common, relay broadcast-cut) は `fano_inequality_measure_theoretic` で genuine、chain/Csiszár 方向は非循環 honest `Prop`。(inner) `MAC/BC/RelayDF/RelayCFInnerBoundExistence` を `(c.averageErrorProb W).toReal < ε` (∀ε>0) 込みに再定義し、honest 達成可能性述語 (`*JointTypicalityAchievable`/`*SuperpositionAchievable`/`RelayDF/CFAchievable` = rate→existence、≠結論) を modus ponens で消費。BC/Relay の `errBound<1` red-herring (channel `averageErrorProb` に未接続で実エラー減衰なしに充足、relay は constant-code で構成的充足) を excise。typicality/多変数 Fano/superposition/block-Markov は **genuine Mathlib gap** (loogle: typical 0件, IT-Fano 0件) ゆえ inner と一部 outer 方向は honest-🟢ʰ で terminal。 |
| 17 Inequalities | Han/Shearer/LoomisWhitney/Hypercube/BrascampLieb/Pinsker 🟢；**Fisher 🟢ʰ (RESOLVED 2026-05-20: バグ V1 `fisherInfo` は DELETE、EPI/Stam scaffolding を a.e.-class-invariant V2 `fisherInfoOfMeasureV2`/`fisherInfoOfDensity` に migrate、Gaussian `= 1/v` + de Bruijn 健全)；EPI 🟢ʰ (2026-05-21 de-circularize: 旧 `entropy_power_inequality := h_epi` (仮説型≡結論、circular) + L-EPI1/2 `:= True` を撤廃。新 headline は genuine `IsStamInequalityResidual` (Fisher info の Stam 逆調和平均不等式、≠ EPI 結論、real Mathlib 壁) + `IsStamToEPIBridge` を取り `h_bridge h_stam` で導出、非循環。Gaussian saturation は hypothesis-free genuine。back-door vacuous Stam discharge (V1 fisherInfo=0) は無し確認。Stam 不等式本体 (Fisher info 畳み込み) は Mathlib 不在で honest-🟢ʰ terminal)；**BM 🟠→🟢ʰ (2026-05-21、`BrunnMinkowskiClosure.lean`): 体積版 BM genuine + n-dim Prékopa-Leindler `prekopa_leindler_nDim` genuine (Fubini 帰納、最重の `piFinSuccAbove` measure 統合は Mathlib gap なし)。entropy 形 headline `brunn_minkowski_entropy_inequality_genuine`/`_scaledMul` は抽象 `h` を `jointDifferentialEntropyPi`(#12) に特化し、entropy↔geometry↔rpow + λ-最適化 (`bm_scaledMul_to_sqrt`) を全 genuine 化。残 honest = `IsSlicePLReadyHyp` (n-dim PL の slice 解析的 readiness) + uniform=log-vol 同定。`:= h_bm` 完全 pass-through から脱却。**2026-05-21 追補: (i) superlevel side-condition の量化子を `0≤t→0<t` に弱化 (`IsPL11DSuperLevelHyp` 定義含む全 chain)、indicator の `t=0` superlevel=univ vacuity を解消し compact 系 corollary を latent-vacuous→honest-open 化。(ii) ただし `IsSlicePLReadyHyp` を indicator で discharge するのは依然 fundamental Mathlib 壁: ❶ 大-t 非空性 vacuity (t=0 と対称、indicator は g 有界ゆえ大-t で superlevel 空、汎用 engine の `one_dim_bm_scaled` が非空性必須 → indicator 専用 case-split lemma が必要) + ❷ slice-体積関数 `s↦vol((cons s)⁻¹A)` の上半連続性 (loogle 0件、~150行の自作解析、compact 性 conjunct に必須)。BM は 🟢ʰ 据え置きが honest landing。**** |

### ✅ FLAW-VACUOUS 不備 (全件 RESOLVED 2026-05-20、詳細 → [`flaw-vacuous-review-2026-05-20.md`](shannon/flaw-vacuous-review-2026-05-20.md))

> 監査で挙げた 🔴 退化定義は **全て解消済み**。空虚 discharge は削除、buggy V1 `fisherInfo` は DELETE、Shannon-Hartley/Whittaker は de-circularize 済。残るのは ① の honest pass-through 本体 discharge (🟠、退化ではない) のみ。

- **HIGH-1 — EPI/Stam の Gaussian discharge が空虚** — **RESOLVED**: `*_of_gaussian_fisherInfo_zero` 系 (`exfalso` で `0 < J_X` を V1 `fisherInfo = 0` に矛盾させる空虚経路) と chain wrapper を全削除。genuine な Gaussian EPI は `entropy_power_inequality_gaussian_saturation` 経由、非空虚 V2 bound は `FisherInfoV2.stam_convex_fisher_bound_gaussian`。
- **HIGH-2 — `entropy_power_inequality_gaussian_via_stamDeBruijn`** — **RESOLVED**: 当該定理と `isEPIStamDeBruijnPipeline_of_gaussian` を削除 (Stam 半分が HIGH-1 の空虚経路で non-load-bearing)。honest な Gaussian EPI は `entropy_power_inequality_gaussian_full'`。
- **根因 — V1 `fisherInfo` バグ** — **RESOLVED**: V1 `fisherInfo` 一族 (`fisherInfo`/`fisherInfoReal`/`deBruijn_identity` 等) を `FisherInfo.lean` から **DELETE**。EPI/Stam scaffolding predicate を a.e.-class-invariant V2 `fisherInfoOfMeasureV2` に migrate。buggy symbol が存在しなくなったため再罠化不能、full build green 0 sorry。
- **Shannon-Hartley / Whittaker** (`ShannonHartley.lean`, `WhittakerShannonPartial.lean`) — **RESOLVED**: `shannon_hartley_formula` は循環を解消し `h_two_w`(開な `2W` DoF 恒等式) を取り込む conditional pass-through、`whittaker_shannon_one_point` は `rfl` を廃し `recovered`+`h_reconstruct` 仮説の非自明 pass-through 化。L-SH1/2/3・L-WS-A の `def` は ⚠️ docstring で **undischarged placeholder** と明記。sinc 下層は genuine 0-sorry 維持。
- **MED — `entropy_power_inequality`** (`EntropyPowerInequality.lean:188`) body `:= h_epi` (結論=仮説) — **honest pass-through として残置** (退化ではない、header 透明)。本体 discharge は ① T2-D EPI の作業範囲。

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
- **layout**: `docs/textbook/` 下に章別 markdown を生やす想定。

### 現況と次の一手 (2026-05-21)

- **層 3 はまだ一行も着手していない** (`docs/textbook/` 未生成)。波 5〜15 は層 1 (定理証明) に
  集中してきたが、究極ゴールは *本* であり、そのボトルネックは現状ここ。
- **今この瞬間 genuine 🟢 で原稿に即着手できる章は 6 つ**: Ch.2, 3, 4, 7, 8, 10。
- **合意した次の一手 (本セッション)**: A 群の壁なし残証明 (LZ78 Ziv / Chernoff converse port /
  Huffman 強形) を進めつつ、**完成済み 1 章で原稿層をパイロット起動**する。出発点は Ch.2 か Ch.7 が素直。
- **狙い**: 原稿を 1 章書くと「本文が *定理 Y は検証済み* と書く → 本当に標準B で検証されているか」
  という具体的な問いに変わり、どの load-bearing gap が本当に効くかが判明する。gap の優先順位を
  真空で議論するより、原稿が逆に教えてくれる。

## 判断ログ

書く頻度: seed 追加/撤退、Tier 移動、章ステータス変更、scope-out 判定の修正があったとき。append-only。

> **note (2026-05-26 整理)**: 旧 #1–#15 (2026-05-18〜05-20 の並列実装 wave の集計・seed 別 sub-predicate 詳細) は 1 行サマリに圧縮。当時の各 sub-predicate 名 / wave 別 file 数 / 累計行数は `git log` + `docs/<family>/*.md` (plan / inventory) が SoT、本ファイルは決定に inform する戦略遷移のみ残す。#16 以降の戦略決定ログは無編集。

1. **2026-05-18 起草 + 規模見積もり**: 教科書化目的で本ファイル新規作成。Cover-Thomas Ch.2–17 のうち Ch.6/14/16 scope-out、Ch.13 partial scope-in (LZ78 のみ)。Tier 1–4 + Infrastructure として 18 seed 登録、各 seed に「規模」行 (±50%) 付与、追加合計 ~13-21k 行と見積もり。
2. **2026-05-19 並列 5+2+1 seed → 累計 +3069 行**: T1-D Hoeffding scaffolding / T2-A AWGN F1-4 / T2-F Fisher discharge (representative-dependence flaw 発見) / T1-C Cramér L-C2 partial / T3-D WZ Phase A / T2-B Parallel Gaussian + Water-filling / T3-F Relay cut-set outer / T2-C Shannon-Hartley pass-through publish。Mathlib PR 候補 2 件。
3. **2026-05-20 wave5 並列 7-seed → +2946 行**: T3-C BC / T4-A Arithmetic / T3-F Relay inner DF・CF / T2-E Brunn-Minkowski / T1-B Chernoff converse partial / T1-C Cramér L-C2 ext / T3-D L-WZ3 D-antitone partial。
4. **2026-05-20 wave6 並列 8+3-seed → +6020 行**: AWGN F-1 / Parallel Gaussian L-PG0 完全 discharge 2 件、+ MAC L-MAC1 / LZ78 L-LZ1 / Hoeffding sandwich / Fisher v2 (V1 fisherInfo flaw bypass) / Whittaker-Shannon partial / EPI Plumbing / Huffman 2-hyp plumbing 等。worktree disk 飽和 (~5GB/clone) が運用課題化、`.lake` symlink reuse 確立。
5. **2026-05-20 wave6b 並列 9+3-seed → +6356 行**: AWGN MI bridge 3-primitive / Parallel Gaussian KKT (L-WF1 IVT 完全 discharge) / EPI L-EPI3 single-hyp / Chernoff per-tilt Sanov / MAC L-MAC2 Fano / BC superposition body (MAC body verbatim 流用) / Relay inner DF・CF body / LZ78 L-LZ3 internal化 / Whittaker-Shannon Tier 1 full。Cramér L-C2 Phase C ≡ Chernoff per-tilt の構造同型を予言 (両者 `Measure.infinitePi (μ).tilted ↔ Measure.infinitePi (μ.tilted)` で詰まる)。
6. **2026-05-20 wave7 並列 10+4-seed → +6210 行**: wave6 sub-predicate の更に body discharge。AWGN BindConvBody 完全 discharge / Stam Step1-2/3 / Prékopa-Leindler body / Fisher heat-flow / MAC time-sharing / BC averaging / WZ covering / Relay DF block-Markov / LZ78 greedy parsing impl / Hoeffding interior gradient / Huffman swap-step chain。Cramér × Chernoff 同型を `IsCramerChernoffNLetterRNUnified` structure として明示化。
7. **2026-05-20 wave9 並列 12+4-seed → +6241 行**: wave7 の更に body discharge。AWGN BindConv 完全 / Stam Step1-2/3 真 signature 昇格 / Prékopa-Leindler measure-theoretic / Fisher spatial 半完全 / MAC time-sharing pentagon 両側 / BC L-BC2-I averaging / WZ covering AEP / Relay DF block-Markov code / LZ78 L-LZ4 greedy / Hoeffding gradient stationarity / Huffman swap chain。発見: wave7 certificate predicate の多くが parent と defeq な no-op (S6 MAC / G3 Relay CF / G4 WF certificate)。
8. **2026-05-20 wave10 並列 22-seed → +6586 行**: wave9 sub-predicate の更に body discharge。完全 discharge 7 件 (WF KKT 共通 Lagrange / LZ78 phrase-count `O(n/log n)` / 1-D Brunn-Minkowski / Gaussian variance-deriv + heat time-deriv / layer-cake / Hoeffding I-projection / EPI Stam→de Bruijn Gaussian)、Mathlib gap closure 1 件 (`gaussianPDFRealVar`)。残存 frontier gap 3 件に縮約 (condExp-of-score / infinitePi-tilted / WZ joint perspective convexity)。worktree 古 HEAD 分岐の運用課題 (S23 重複実装 drop)。
9. **2026-05-20 WZ cond-ent convexity → +393 行**: frontier gap「joint perspective convexity」を pmf 形 (Real・有限) を選んで full discharge、log-sum inequality を核に factorisation 経由。残存 frontier gap 2 件 (condExp-of-score / infinitePi-tilted)。pmf 形を選んだことで `RateDistortionConvexity.lean` の measure 形 ~500 行 gap を回避。
10. **2026-05-20 infinitePi-tilted Phase 1 + 自律 5-unit batch → +154+681 行**: 有限 `Measure.pi` の tilt 因子分解 (`pi_tilted_sum_eq_pi_tilted`) を full discharge → Phase 2-4 (cylinder lift で RN-deriv 因子分解スキップ) + tilted window LLN + Stam Gaussian V2 non-vacuous bound (SOS 核 `(a−λ(a+b))²`、λ∈[0,1] 制約不要と判明) + cgf 微分橋 + n-letter Chernoff Z-sum 因子分解。Ch.11 両 exponent (Cramér + Chernoff) が共通 CLT-boundary residual に帰着、change-of-measure 機構は full discharge 済。
11. **2026-05-20 Cramér CLT-boundary closure → +553 行**: Mathlib CLT (`tendstoInDistribution_inv_sqrt_mul_sum_sub`) を tilted ambient に実適用、Gaussian median を自作 (Mathlib 不在唯一の自作、対称性 + `noAtoms_gaussianReal`)。`cramer_lower_at_cgfDeriv_unconditional` で Cramér 下界 `−Λ*(a)` を最適 tilt 閾値で residual 仮定なし (bounded Y + Var>0 のみ) に達成。残存 frontier gap: condExp-of-score (Stam Step1-2、PR級) + Chernoff converse pmf-level CLT port。

16. **2026-05-21 標準B 確定 + 「Mathlib 壁」用語の解像度上げ** (対話セッション、コード変更なし・ロードマップ更新のみ):
    残タスクと vision の関係を整理する対話で 3 点を確定し、ロードマップに反映。
    - **検証強度 = 標準B に確定**: 「完成判定」節に追加。教科書の約束を「定理そのものの無条件機械検証」に置く。
      `0 sorry` ≠ 完成。🟢ʰ は仮説の中身で二分 — **regularity-hyp (full-support / IsFiniteMeasure / Var>0 等) = 完成**、
      **load-bearing-hyp (Stam / typicality / multi-user Fano / 結論同型の存在述語) = 未完**。判定の一言「前提条件か、証明の核心か」。
    - **「Mathlib 壁」を 4 分類に分解** (監査節に taxonomy 追加): (a) 量の壁 (難しくない・未構築、突破困難度 低 —
      multi-user typicality / continuous AEP / BM slice u.s.c.) / (b) 解析の壁 (前提インフラごと無い、中〜高 —
      Stam→EPI) / (c) 本物の数学的深さ (高・真の壁 — Nyquist 2W-DOF prolate-spheroidal、C&T 自身が厳密証明せず → scope 決断点) /
      (d) 実は選択 (de-circularize 済)。**結論: 残 gap の大半は「数学的に難しい」でなく「未構築の定型量」**で、真の壁は Stam の解析土台と Nyquist のみ。
    - **層 3 (原稿) 未着手 = 真のボトルネック**: 「教科書原稿」節に現況追加。波 5〜15 は層 1 に集中したが究極ゴールは本。
      genuine 🟢 で即着手可能な章が 6 つ (Ch.2/3/4/7/8/10)。**合意した次の一手**: A 群壁なし 3 件 (LZ78 Ziv / Chernoff converse port /
      Huffman 強形) を進めつつ、完成済み 1 章 (Ch.2 or Ch.7) で原稿層をパイロット起動。
    - **scope 注意点 (標準B との緊張)**: Nyquist 2W-DOF は標準B では「Shannon-Hartley を検証済みの目玉にするか / 次元論法を
      公理引用するか」の未決断。C&T 自身が厳密証明していない深さなので、標準B でも例外的に scope-out / 開示が妥当という議論あり (要・原稿執筆時に最終判断)。
17. **2026-05-21 A群 (壁なし残証明 3 件) 着手 — 既存 discharge scaffolding が全件「偽 / 循環 / 不健全 predicate」と判明** (orchestrator session、
    調査(監査3並列)→独立壁再評価(pivot)→計画(planner2)→並列実装(worktree2 + main1) の agent chain)。**ロードマップの「A群 = 壁なし」分類は両方向に誤り**だったことを実装で確定:
    各件とも「真の数学的壁」ではない (全て構築可能) が「quick win」でもなく、しかも**既存の縮約 predicate が標準Bでは discharge 不能な偽/循環/不健全命題**で組まれていた。最大の収穫は
    この systematic honesty defect の発見・文書化 (将来の偽 predicate 証明への無駄打ちを防止)。各件:
    - **T1-A'' Huffman 強形**: ✅ keystone `strict_kraft_one_implies_pairing` (`HuffmanSwapNormProof.lean`, Kraft=1⇒最長 leaf 非一意、parity 論法) を genuine 証明 (commit `4020531`)。
      ❌ **既存縮約鎖 `Swap←EqualizingPerm←EqualizingSwapTarget` (`HuffmanSwapNormalizationBody.lean`) の中間述語 2 つは数学的に偽** (permutation は語長 multiset 保存 →
      `ll=![1,2,3]` で等長化不能、反例 `lake env lean` 検証済)。docstring に HONESTY ALERT 追記 (commit `b253d91`)。genuine Hyp1 は permutation を捨て **Kraft 保持の語長 multiset 変更構成** (~550 行 moonshot、
      ファイル自認)。Hyp2 (Identification) は `huffmanStep` の `Multiset.exists_min_image`+`Classical.choose` (非決定的 min 選択) が relabel 不変性を壊す **定義の問題** → 決定的選択 (`List.argmin` 等) への定義 pivot 要 (~150-250 行、blast radius 中)。
    - **T1-B Chernoff converse**: ✅ step1 逆 Hölder core (`min_ge_exp_neg_mul_rpow_mul_rpow` 等) + ε-relaxed converse 構造 (`ChernoffSanovDischarge.lean`, 474 行, axiom-clean) を genuine 証明・publish。
      ❌ **既存 predicate `IsBayesErrorPerTiltLowerBound` (定数 C・base Z(λ*)) は数学的に偽** — `bayesErrorMinPmf ~ poly(n)·Z^n` の sub-exponential prefactor (λ*=1/2 で Θ(1/√n)) で定数 C 不在。
      CLT-port も不可 (対象不一致)。残 crux = honest load-bearing `IsChernoffBandMassToOne` (λ↦Z(λ) の内点一次最適性 `∑Q(log P₁−log P₂)=0` + Q-LLN で band mass→1、~300-500 行、Mathlib-adjacent 微分可能性)。
      旧 `chernoff_per_tilt_via_RN := h_RN` (二重命名 name-laundering) は本 ε-relaxed path で迂回・置換 (旧循環は predecessor file に残存、docstring で honest 明示)。
    - **T4-A LZ78**: ✅ distinct headline を **2 つの per-path primitive 仮説**から genuine 構成 (`LZ78ConverseKraft.lean` + `LZ78AchievabilityLimsup.lean`, 両 silent)。`lz78_two_sided_optimality_distinct_genuine` (最大解消 headline) 達成 —
      blockLogAvg-level の deferral を per-path eventual 不等式に primitive 化。❌ **計画の converse 経路 `2^{-lz(x)}≤Pₙ{x}` (`rpow_neg_shannonLength_le_real`) は数学的に不健全** (Shannon-code 長の補題、`lz≥shannonLength` は pointwise 偽 = LZ78 universality の核心) → 不採用・フラグ。
      残 crux = `IsLZ78AchievabilityZivUpperBound` (per-path Ziv `c log c ≤ -log Pₙ`、parsing factorization `Pₙ=∏qⱼ` が **`blockRV` (`Stationary.lean:81`) が単純射影で kernel/compProd 構造を欠く**ため当層で導出不可 = 構造的) + `IsLZ78ConverseCodingLowerBound` (13.130 期待値→a.s. 符号化下界)。
    <br>**メタ結論 (taxonomy 更新)**: L884 の 4 分類に **(e) scaffolding-was-false** を追加すべき — 「既存の縮約 predicate が偽/循環/不健全で discharge 不能、genuine 構成を一から組み直す要」。A群 3 件は (a)/(b) でなく実態は (e) + 定義/構造の壁
    (Huffman `huffmanStep` 非決定選択 / LZ78 `blockRV` 射影 / Chernoff 一次最適性の不在)。**「真の壁は Stam と Nyquist のみ」(L886) は撤回**: A群の残 crux は数学的深さでなく定義・構造リファクタ (blast radius 中〜大) が支配。
    完遂は multi-session moonshot (残 ~1000-1500 行、定義 pivot 2 件含む)。本セッションは genuine 進捗を全件 commit し、偽 scaffolding を全件文書化した段階。
18. **2026-05-21 T1-B Chernoff converse 標準B 完成** (同 orchestrator session、ユーザー指示「Chernoff の残 crux を継続」→ inventory(GO) → main 実装):
    #17 で honest load-bearing として残した `IsChernoffBandMassToOne` を **genuine に discharge** し、Chernoff converse + full theorem を regularity 仮説のみの無条件形にした。
    `Common2026/Shannon/ChernoffBandMassDischarge.lean` (575 行, 0 sorry / silent):
    - **(a) 一次最適性**: `hasDerivAt_chernoffZSum` + Fermat (`IsLocalMin.hasDerivAt_eq_zero` + `interior_Icc`) で `chernoffMediator_mean_logRatio_eq_zero` (E_Q[log P₁−log P₂]=0)。
      境界 λ*∈{0,1} は case-split せず strict Gibbs (`Z'(0)=−KL<0`, `Z'(1)=KL>0`) で**内点最小を証明して除外** (`exists_interior_minimiser`)。
    - **(b) Q-LLN**: `strong_law_ae_real` on `infinitePi Q` + `tendstoInMeasure_of_tendsto_ae` + Cramér iid テンプレ流用で band mass→1 (`isChernoffBandMassToOne_of_interior_optimal`)。在庫最大リスクの添字 reindex (ℕ/部分型/Fin) は `infinitePi_map_take` で解決。
    - **headline**: `chernoff_converse_holds` (`limsup rate ≤ chernoffInfo`) + capstone `chernoff_lemma_tendsto_holds` (full `rate → chernoffInfo`, Cover-Thomas Thm 11.9.1)。両者 `#print axioms = [propext, Classical.choice, Quot.sound]` (**sorryAx 非依存 = 標準B**)。仮説は full-support pmf + `∑Pᵢ=1` + `P₁≠P₂` の regularity のみ。
    <br>**到達**: Ch.11 Chernoff information は achievability (既存 `chernoff_lemma_achievability`) + converse (本 discharge) のサンドイッチで **🟢ʰ regularity = 完成**。#17 Chernoff bullet の「残 crux」は RESOLVED。所見: 在庫の「LLN は使えるが直接でない (添字不整合)」予測通り reindex が最大工数だったが真の壁ゼロで GO 通り着地。旧 `IsBayesErrorPerTiltLowerBound` (偽) / `:= h_RN` 循環は ε-relaxed path で迂回済 (predecessor file に残存、docstring honest)。A群 残: Huffman 強形 (Hyp1 multiset 構成 + Hyp2 定義 pivot)、LZ78 (per-path Ziv factorization + 13.130)。
19. **2026-05-21 T1-A'' Huffman 強形 着手 — C1 (huffmanStep 再定義) 確定不可 + 既存 predicate 2 つが「誤った弱さ」で stated と判明** (同 orchestrator session、ユーザー指示「Hyp2 定義 pivot まで含めて完遂」):
    genuine cores 2 本を sorryAx 非依存で確立 (`HuffmanSwapNormCompletion.lean` の `shorten_to_kraft_one` (Kraft<1→=1 へ E 非増加、計画最大リスク) + `HuffmanStrongForm.lean` の `swap_normalization_strong` (strong precondition 下の swap 論法 core))。だが強形 publish は未到達。
    - **C1 確定不可**: `huffmanStep` を `Multiset.sort` 決定的選択に再定義する案は `LinearOrder (Finset α)` (Mathlib 不在) を要求し、`Fintype.equivFin` 順序は subtype `{y//y≠b}` で `α` の制限にならず `Multiset.map_sort` cross-type bridge 不成立 (Phase 0 probe 確定)。**C3 (tie-invariance、再定義せず) が Hyp2 の唯一の道**。
    - **既存 predicate 2 つの mis-statement (構造的負債)**: `SwapNormalizationHypothesis._h_min` が disjunctive (`∀c, Q{a}≤Q{c} ∨ Q{b}≤Q{c}`、`a` global-min のみ含意・`b` 任意) で swap 論法 (least-2→longest-2) が閉じない。`HuffmanMergedIdentificationHypothesis` は「a,b first-merged (確率最小) 対」前提を欠く。**両者とも call site (`HuffmanOptimality.lean:919`, `exists_sibling_min_pair`) が供給可能な strong 形より弱く stated** — predicate を使用箇所に合わせ strong 化するのが honest fix (循環でも弱化でもない) だが weak form の hypothesis 型変更 = 依存 ~5 file に波及。
    <br>**Huffman 完遂の残**: (i) predicate 前提を strong 形へ揃える interface refactor (~5 file) **または** disjunctive 形のまま Kraft=1 後の node 再編 general 構成 (~200-400 行)、(ii) Hyp2 を C3 tie-invariance + interface 整合で discharge、(iii) 無引数 wrapper で `huffmanLength_optimal` publish。反復ごとに構造的負債 (偽縮約鎖 #17 → C1 不可 → predicate 誤定義) ため multi-iteration moonshot。genuine 数学 (core) は済、残は interface 整合 + C3。
    **追記 (viable path 実行)**: Part A (interface refactor、6 file、disjunctive `_h_min`→strong `_h_a_min`/`_h_b_min`) + Part B (Hyp1) 完了 — **`Huffman.swap_normalization_proof : SwapNormalizationHypothesis` を無条件 genuine discharge** (sorryAx 非依存)。
    headline `Huffman.huffmanLength_optimal_modulo_aux_ident` (Hyp1 被せ済・Hyp2 のみ open、sorryAx 非依存) publish。**残るは Hyp2 のみ**: `MergedHuffmanAuxIdentHypothesis` を tie-invariance (`huffmanLengthAux` の値が `huffmanStep` の `Classical.choose` min 選択に不変) + carrier-crossing 対応 (`β`↔`{y//y≠b}`) で discharge (~400 行)。これが取れれば無引数 `huffmanLength_optimal` 完成。所見: aux 4 file (`HuffmanT1APPrimeBody`/`HuffmanSwapNormalizationBody`/`HuffmanSwapStepChainBody`/`HuffmanT1APPrimePartial`) は誰も import しない dead-weight leaf (false-chain + name-laundering の温床)、別タスクで削除候補。
    **追記2 (Part C = Hyp2 = `MergedHuffmanAuxIdentHypothesis` discharge)**: no-ties ケースは genuine に解けたが**確率 tie の一般ケースが構造的壁**と判明。
    `Common2026/Shannon/HuffmanMergedAuxIdent.lean` (487 行, 0 sorry): relabel 基盤 7 件 + cornerstone **`huffmanLengthAux_relabel`** (no-ties = `NodupChain` 下の carrier-embedding relabel-invariance、strong induction) + `huffmanStep_min_fst/snd` (定義不変で `Classical.choose_spec` から最小性 spec 抽出、tie-invariance 全証明の基盤 unlock)。
    **壁 (tie の一般ケース)**: (i) first-step identification が tie 時 `Classical.choose` の不透明な tie 破りで a,b 以外を選びうる — C1 (決定的 huffmanStep) なしには解けないが C1 は `LinearOrder (Finset α)` 不在 + carrier 横断不一致で確定不可、(ii) `mergedInitMultiset` が一般に `NodupChain` 不成立、(iii) naive per-symbol invariance は反例 (`Q={.1,.15,.15,.6}`) で偽。
    **結論 — Huffman 強形の残壁は (e) scaffolding でなく定義artifactの真壁**: 非決定的 `huffmanStep` 定義 + Mathlib の carrier 横断順序不在に根ざす。完遂の選択肢は (A) 「全確率 distinct」regularity 仮説下で publish (no-ties 機構 + collapse correspondence ~150-250 行追加、ただし uniform/tie を除外するため**標準B regularity か load-bearing か境界**)、(B) `huffmanStep` を relabel-invariant に深く再定義 (追加 moonshot、feasibility 未確定)、(C) Hyp1 完了状態 (`huffmanLength_optimal_modulo_aux_ident`) で停止。**到達: Hyp1 + interface + Hyp2 no-ties が genuine 済 (~960 行)、Hyp2 tie 一般ケースが真壁で未到達**。
    **追記3 (真壁判定の撤回 — colex 決定化で (ii)(iii) 解消)**: 「tie 真壁」判定は早計だった。`[LinearOrder α]` (有限アルファベットに常に入る構造的仮説、load-bearing でない) を加えれば `Finset.Colex.instLinearOrder` (`Mathlib/Combinatorics/Colex.lean:272`) で決定的 tie-break が組め、`toColex_image_le_toColex_image` (strict-mono が colex 保存) で carrier 横断対応も通る。
    `Common2026/Shannon/HuffmanColexDeterminism.lean` 新規: `huffmanStep` を `groupKey = toLex (p.2, toColex p.1)` の決定的 min に差し替え (signature 不変) + `[LinearOrder α]` を Huffman* 全 file に伝播 (Ch.5 無影響) + cornerstone **`huffmanLengthAux_relabel_det` (NodupChain 不要の無条件 relabel-invariance)** を確立 → Section E 障害 (ii) NodupChain 不成立 / (iii) per-symbol invariance 偽 を genuine に解消。Hyp1 (`swap_normalization_proof`) は決定化後も sorryAx 非依存で維持。`lake build` 全 3248 jobs green。
    **残る唯一のピース = collapse correspondence**: `mergedInitMultiset Q a b` の singleton group `({a},p)` と β-側 first-merge 残木の card-2 group `({a,b},p)` (同確率) の対応。per-leaf identity は数値検証で成立するが、equal-prob tie 下で 2 木の merge **order** が食い違う (colex が `{a}` と `{a,b}` を別位置にソート) ため naive lockstep 帰納で閉じない → tie-break-order 非依存の invariant (確率 multiset で depth が決まる Huffman 性質) が要、~150-250 行。**これは open-ended 真壁でなく bounded な残補題**。Hyp1 + 決定化 + cornerstone まで genuine 済、collapse correspondence のみ残。
    **追記4 (collapse の再評価 — 「bounded」は楽観、独立 pivot で moonshot 寄りと確認)**: 追記3 の「~150-250 行 bounded」は **first-step identification を見落とした過小評価**だった。独立 proof-pivot-advisor (read-only、コード精査) の判定:
    残りは実体 **2 補題** — (1) first-step identification: 決定的 huffmanStep は `groupKey=(確率, colex)` の colex tie-break のため、同確率 leaf 複数時に「与えられた `b`」(rest-min) とは別の leaf を first-merge しうる (`HuffmanMergedAuxIdent.lean:455` 障害(1)、決定化でも未解決)。(2) collapse 本体: `{a}`↔`{a,b}` の merge-order divergence が決定化で消えず (同確率だが `toColex{a}<toColex{a,b}` で後続 step の選択が分岐)、per-leaf depth は tie 下で choose 依存 (コード内反例 `Q={.1,.15,.15,.6}` で確認)。tie-robust invariant は「depth = prob multiset の関数」の特殊形に逢着し moonshot (500+ 行) に滑落するリスク。
    pivot 選択肢: A (局所 collapse 2 段、300-450 行、高リスク) / B (depth-from-prob-multiset 構造定理、500+ 行 moonshot) / C (決定化を label-blind に再々定義、cornerstone 全再証明) / **D (honest frontier `huffmanLength_optimal_modulo_aux_ident` で停止、推奨)** / E (全確率 distinct regularity で publish、50-100 行だが uniform/tie 除外で標準B 境界)。
    **結論**: 決定化は障害 (ii)(iii) を genuine 解消した本物の前進だが、Hyp2 完全 discharge は (i) first-step + (2) collapse の moonshot 寄り 2 補題が残る。**Huffman の honest frontier = `huffmanLength_optimal_modulo_aux_ident`** (Hyp1 + 決定化 + cornerstone genuine、`MergedHuffmanAuxIdentHypothesis` を honest load-bearing 引数で開示)。完全完遂は別セッション moonshot (案 A or E)。honesty defect なし。
20. **2026-05-21 moonshot バッチ (ユーザー「moonshot を承認して続行」) — 両残件で既存 scaffolding の FALSE 定義を機械検証で発見 (honesty 訂正)**:
    Huffman full-B と LZ78 kernel refactor を並列 pursue (各々 inventory→plan→implement、Huffman は worktree)。両件とも genuine 進捗 + **既存定義が数学的に偽**と判明 (faithful 反例検証)。**A群「壁なし」前提が誤りだった真因 = 既存 scaffolding が 0-sorry で偽 predicate/定義を隠していた**ことが、moonshot 着手で初めて全貌判明。
    - **T1-A'' Huffman — `MergedHuffmanAuxIdentHypothesis` は FALSE (honesty 訂正、追記4 の「defect なし」を撤回)**: full-B label-blindness 補題が偽 (faithful ランダム探索 1.13% 失敗、最小反例 rest `{0:15,2:16}`,P=16,a=1,b=3)。**根本原因**: `mergedMeasure` (`HuffmanOptimality.lean:212`) が carrier `{y≠b}` 上で **singleton `{a}` に weight `Q{a}+Q{b}`** を置くが真の Huffman 残木は **card-2 group `{a,b}`**。colex が `{a}`/`{a,b}` を区別 → tie 解決が両木で反転 → depth 発散。**card-2 collapse identity は min-pair 下で 240k 件検証で真**だが singleton 形が偽。以前の probe「identity TRUE」は colex downstream を再現しない非忠実検証だった。**→ 現 frontier `huffmanLength_optimal_modulo_aux_ident` は偽の仮説を引数に取り discharge 不能 (honesty defect — 訂正)**。genuine 完遂 = `mergedMeasure` を card-2 形に再定義 + 最適性帰納の core redesign (first-step identification は min-pair でも α-min 非固定で要再設計)。3 度目の深い構造サプライズ。
    - **T4-A LZ78 — base-2 単位バグ修正 (genuine 前進) + `factor` 定義 FALSE 発見**: 前任が log-base 不整合を発見 (blockLogAvg/entropyRate=自然log vs lz/bitLength=base-2、achievability primitive 係数1 は ergodic で偽)。承認方針 (C) で `entropyRate₂ := entropyRate/log 2` 導入、headline `lz78_two_sided_optimality_distinct_genuine → entropyRate₂` を **sorryAx 非依存**で base-2 訂正 (`f511f85`、Cover-Thomas Thm 13.5.3 の真 statement)。telescoping 層 `StationaryKernel.lean` (`prod_condPhraseProb_telescope` + `factor_of_complete_of_pos`) genuine、crux を parse-completeness 1 点に局所化。**`factor` 偽 defect は genuine 解消済 (本セッション)**: `factor` を偽の等式 `Pₙ = ∏ⱼ qⱼ` から真の Ziv 不等式 `Pₙ ≤ ∏ⱼ qⱼ` に recast (prefix monotonicity `prefixBlockProb_antitone` + telescoping、`blockProb_le_prod_condPhraseProb`)。`IsLZ78PerPathParsingFactorization` は `isLZ78PerPathParsingFactorization_of_pos` で a.s. regularity (正値 cylinder) のみから **genuine 構成可能** に (旧: 非完了 parse で unsatisfiable な vacuous 仮説 → 現: regularity 仮説付き定理)。`blockProb_neg_log_ge_sum` も `≥` 方向に更新。4 新補題すべて sorryAx 非依存、`lake build` 全 3250 jobs clean (Ch.4 非破壊)。**残 load-bearing**: Z-side core `c·log₂c ≤ -log₂Pₙ` (Cover-Thomas Lemma 13.5.5、distinct-phrase 層化の Ziv 組合せ — log-sum は `∑qⱼ≤1` を要するが telescoping ratio は path 沿いで sum≈c、stratum 別組合せが本体) + C-side (averaged Kraft + Birkhoff lift)。2 primitive (`IsLZ78AchievabilityZivUpperBound`/`IsLZ78ConverseCodingLowerBound`) は honest hyp のまま (型≠結論、load-bearing 明示)、偽の無引数 publish は不採。kernel refactor は additive・Ch.4 安全と確認済。
    - **メタ結論**: A群 残 2 件は「壁なし」でも「bounded moonshot」でもなく、**既存 scaffolding の偽定義 (Huffman mergedMeasure singleton / LZ78 factor parse-tail) の core redesign + ~400 行 cores** が必須。両件とも faithful 反例検証で偽を機械確認 (skeleton 着手前に阻止、無駄打ち回避)。inventory の盲点 = 「Mathlib に補題があるか」は見るが「定義同士の単位/shape 整合」を検査軸に入れていなかった (log-base, parse-tail, mergedMeasure-shape の 3 件とも見落とし)。**到達: Chernoff 標準B完成 (1/3)、Huffman/LZ78 は genuine 部分前進 + 偽 foundation の精密診断、完全完遂は core redesign moonshot**。
21. **2026-05-21 LZ78 集中 (/goal「LZ78 完遂」) — achievability を core 1 本に縮約 + その clean core が FALSE と判明 (M0 gate)**:
    achievability を Z3/Z4 で組立 (`c·log₂c ≤ -log₂Pₙ` 組立 + envelope + slack + headline 配線、`LZ78ZivCombinatorics.lean`, sorryAx 非依存) → **core hyp `IsLZ78ZivCombinatorialCore` 1 本に縮約**。Z2 per-symbol chain-rule (`condNextSymbol_sum_eq_one`) genuine。
    - **重大: clean per-block core `c·log c ≤ -log₂Pₙ` (∀n∀ω) は数学的に FALSE** (M0 gate、反例 `(a,a,b)` stationary Markov `π(a)=0.9` 実現可: `-log P(aab)≈0.916 < 1.386=c log c`)。根本: c phrase 上で `∑Q≤1` ∧ `∑-log Q ≤ -log Pₙ` 両立分布が一般 stationary に無い (path-prefix ∑≈c、node-context ∑>1、grouping `c log c ≤ ∑_v k_v log k_v` は Jensen 逆向きで偽=1.386≤0)。**committed Z3/Z4 は偽 clean core を honest hyp に取っていた (Huffman Hyp2 と同型)**。
    - **constructive fix**: genuine Cover-Thomas は `O(c)` overhead を伴い `c/n→0` で消える (clean 版が真より強すぎた)。修正 = **core を overhead 込み (`+ c·log(|α|+1)` 等) に再定義 + downstream slack で吸収**。tree-node 基盤 (T1 worker 不変 GREEN, T2 per-node sub-dist genuine) は overhead 込みで効く。M0 gate が「偽 core 上に ~750-1100 行」を未然防止。
    - **LZ78 完遂の残 (precise)**: achievability = overhead-aware core 再定義 + Z3/Z4 rework + tree-node 基盤 (~750-1100 行)。converse = McMillan (UD→Kraft、**Mathlib 不在**) + Birkhoff a.s. lift。両者 genuine 達成可能だが multi-session の hard math + 新規 foundation。
22. **2026-05-21 LZ78 — per-block Ziv core (clean も overhead も) は数学的に FALSE と確定、genuine path は a.s.-eventual ergodic (CT 13.5.3)**:
    bridge lemma (CT 13.5.5 tree-measure domination) の skeleton 検証中に、**overhead core `IsLZ78ZivCombinatorialCoreOverhead` も FALSE** と判明 (前 run の「TRUE」は単発 `(a,a,b)` チェックのみで `Pₙ→1` family を見逃した — honesty tell「1 点で universal を true と称する」)。machine-checked DISPROOF `not_isLZ78ZivCombinatorialCoreOverhead` (`LZ78ZivTreeBridge.lean`, sorryAx 非依存) を publish + 上流 docstring の誤主張訂正。
    - **反例**: constant process (`X≡true`, Dirac)、`n=16` で `Pₙ=1` (`-log Pₙ=0`)、LZ parse 実評価で `c=5` → core は `5 log5 ≤ 0 + 5 log3` = `log5 ≤ log3` で偽。根本: `Pₙ→1` で `c log c ∼ √n log√n → ∞` vs `-log Pₙ → 0`、O(c) overhead では gap 不足 (textbook `c log(n/c)` でも p→1 で不足)。grouping-overhead も `a^k` で偽。
    - **判明した genuine path**: per-block `∀n∀ω` Ziv 不等式は (clean/overhead とも) **誤った formulation**。CT 13.5.3 のオリジナルは **a.s.-eventual な ergodic/AEP argument** (非退化 ergodic で `-log Pₙ/n → H>0`、`c log c/n → H` も a.s.、両者 o(n) で一致)。真の honest input は既存 `IsLZ78AchievabilityZivUpperBound` の a.s.-eventual rate-bound 構造であって per-block 不等式でない。
    - **genuine 資産として残るもの** (sorryAx 非依存): tree-node 基盤 T1/T2/T3 (per-node sub-distribution、a.s.-eventual path でも部分再利用可)、Z2 cylinder chain-rule、telescoping、base-2 層、parse-completeness recast、2 つの per-block core の DISPROOF (将来の誤着手防止)。
    - **メタ**: LZ78 achievability の真の難所は per-block 組合せでなく **a.s.-eventual ergodic 論法 (CT 13.5.3 実質フル証明、既存 SMB/AEP/Birkhoff 上)**。per-block 方向 (本 round 多数 run) は formulation 誤りと確定。完遂は a.s.-eventual achievability build + McMillan converse build の multi-session 研究的形式化。**各 run は genuine 増分 + 偽 foundation の精密 disproof を積んだが、achievability の 2→1 は per-block では原理的に不可能と判明**。
23. **2026-05-21 LZ78 a.s.-eventual feasibility gate (M0) — full 完遂は library-scale gap 2 本と definitive 確定、honest landing = L-AS1 frontier**:
    a.s.-eventual achievability (CT 13.5.3) の M0 gate (proof-pivot, read-only) で完遂 feasibility を確定:
    - **RHS genuine**: SMB 無条件版 `SMBAlgoetCover.lean:2840` (`blockLogAvg → entropyRate`) が `-log₂Pₙ/n → H` を供給。
    - **SMB 内部に固定深さ k の tree-measure AEP が既に genuine**: `qkSingleton`/`sum_qkSingleton_le_one`/`negLogQk_div_tendsto_condEntropyTail` (`SMBAlgoetCover.lean:219`, `-log qk/n → H_k`) + `conditionalEntropyTail_tendsto_entropyRate` (`EntropyRate.lean:468`, `H_k → H`)。
    - **真の gap = 可変 context-depth AEP**: LZ78 `Q_c` は固定 k でなく可変長 dictionary node context。`-log Q_c/n → H` を k↔n diagonal/cutoff (CT 13.5.3 核心) で組む必要、`birkhoffAverage` (固定 f Cesàro) 直接不適用 → SMB と独立な新規 ergodic content (~500-900 行、壁分類 (b))。
    - **honest landing = L-AS1 frontier** (~200-300 行): envelope reduction genuine + achievability を honest named hyp `IsTreeInducedAEP` (= CT 13.5.3 可変depth AEP、唯一の解析壁) に localize。Chernoff band-mass / Huffman modulo_aux_ident と同型の正当 partial completion。
    <br>**definitive bottom line**: LZ78 full standard-B 完遂 = **library-scale ergodic/coding 定理 2 本** (achievability の可変depth tree-induced AEP ~500-900 行 + converse の McMillan UD→Kraft [Mathlib 不在])、どちらも SMB (2800 行) 級の壁分類 (b) 解析 gap。本セッション ~30 エージェントで genuine 進捗 + 精密 disproof + この特定に到達。full 完遂は autonomous incremental では届かない major research-formalization。**A群 最終到達: Chernoff 標準B完成 (1/3)、Huffman = mergedMeasure core redesign 要、LZ78 = library-scale 定理 2 本要、いずれも honest frontier まで精密 localize 済**。
24. **2026-05-21 LZ78 可変depth AEP build (ユーザー commit) — AEP は red herring と判明、achievability の真の gap は CT 13.5.5 組合せ核に確定**:
    可変depth `Q_c` AEP の build に着手したが M0 で **AEP は achievability の gap でなかった**ことを発見。`treeInducedProb_negLogb_div_limsup_le_entropyRate₂` (`LZ78TreeInducedAEP.lean`, sorryAx 非依存) = `∀ᵐω, limsup(-log₂Q_c/n) ≤ entropyRate₂` を **`Pₙ ≤ Q_c` (既存) + SMB で ~80 行・新規 ergodic content ゼロ**で genuine 証明 — つまり AEP は trivial。route C の `qkSingleton` sandwich (`Q_c ≥ qk`) は条件付き確率の context-depth 非単調で factor-by-factor 不成立 → 放棄、`Pₙ≤Q_c` で bypass。
    - **plan 前提の誤り (honesty)**: plan は achievability gap を「`Q_c` AEP」とした (`Q_c` AEP と組合せ核 `c log c ≤ -log Q_c` を混同)。実際は AEP は trivial、**真の gap は組合せ核**。`c log c ≤ -log Q_c` は path-prefix 形 (∑qⱼ≈c) も tree-node 形 (`node_logsum_step` は `∑_v k_v log k_v ≤ -log Q_c` までで、`c log c ≤ ∑_v k_v log k_v` は CT 13.5.5 Jensen で overhead 付き) も **per-block では偽**。
    - **真の achievability 核 = CT 13.5.5 組合せ不等式 `c log c ≤ -log Pₙ + o(n)`** (TRUE、published、LZ78 optimality の真の数学的核心)。clean per-block は FALSE (disproof 済)、genuine は a.s.-eventual の正確な o(n) overhead argument。**~32 エージェントの徹底 localization (per-path→base-2→telescope→parse→Z2→Z3/Z4→tree-node→overhead core FALSE→a.s.-eventual→AEP red herring→CT 13.5.5 核) の末、この組合せ核は per-block/tree-node/AEP の全足場で cracking 未達** — 反復 grind でなく genuine な数学的洞察 (正しい o(n)-overhead argument) を要する research-level の deep heart。
    <br>**A群 セッション総括 (確定)**: Chernoff 標準B完成 (1/3、genuine, sorryAx 非依存)。Huffman = mergedMeasure card-2 redesign + length-multiset 構造定理 (research-level)。LZ78 = CT 13.5.5 組合せ核 (achievability、research-level、AEP は trivial と判明) + McMillan (converse、Mathlib gap)。**当初「壁なし3件」は全件 0-sorry が偽 foundation を隠していた + 真の核は research-level math と判明**。genuine 進捗・精密 disproof・honest frontier localization は全件バンク済。残 3 核 (Huffman 構造定理、LZ78 CT 13.5.5、McMillan) は dedicated mathematical work 案件。
25. **2026-05-21 LZ78 achievability clean honest frontier 着地 (CT 13.5.5 length-grouping 確定 + L-AS1 landing)**:
    CT 13.5.5 戦略 pivot が definitive 決着: **node-grouping overhead `(c log D)/n` は D≈c で定数収束=vanish しない (FALSE)**、**genuine は length-grouping** (overhead `c·H(length-dist) ≤ c log(maxlen)`, maxlen≤log_b n で `(c log log n)/n → 0`)。前 run の停滞は `log D=log c` (node) を `log(n/c)≈log log n` (length) と取り違えた為。
    - **achievability honest landing 完了** (`Common2026/Shannon/LZ78AsEventualAchievability.lean`, 447 行, 全 sorryAx 非依存, lake build 3255 jobs): Step1 `lz78DistinctRate_le_countLogRate₂_add_slack` (`lz/n ≤ (c log₂c)/n + slack`, **FALSE core 非依存**・distribution-free・ω-uniform) genuine。Step3 satisfiable honest hyp **`IsLZ78ZivAsEventual`** (`∀ᵐω, limsup (c log₂c)/n ≤ entropyRate₂`, 型≠結論, satisfiable [ergodic で真, H=0 でも genuine]) を定義し、新 headline `lz78_two_sided_optimality_distinct_aseventual` が消費。**FALSE cores (`IsLZ78ZivCombinatorialCore`/`...Overhead`) を satisfiable hyp に置換 → headline honesty 改善** (vacuously-conditioned [偽 hyp] → satisfiable honest hyp)。
    - **full discharge の残 = library-scale tree-node AEP**: length-grouping の genuine route は tree-node `Pₙ ≤ Q_c^{tree}` + その AEP を要するが committed layer 不在 (SMB 独立 ergodic gap, 壁分類 (b))。path-prefix `Q_c` AEP は genuine だが achievability に繋がらない (docstring 正直明示)。
    <br>**A群 確定最終到達 (~34 エージェント)**: Chernoff 標準B完成 (1/3)。Huffman/LZ78 = **全 FALSE foundation を machine-disproof で暴き、両件とも satisfiable honest frontier まで精密 localize 完了** (Huffman: `huffmanLength_optimal_modulo_aux_ident`、LZ78: `lz78_two_sided_optimality_distinct_aseventual` + converse hyp)。残 3 核 (Huffman length-multiset 構造定理、LZ78 tree-node AEP [CT 13.5.5 length-grouping]、McMillan) は SMB 級の research-level dedicated work。autonomous orchestration はここまで — genuine 進捗・正確診断・honest frontier は全件バンク、偽完遂ゼロ。
26. **2026-05-21 LZ78 converse — McMillan は Mathlib 既存と判明 (bridge wire 済)、converse の真の核は UD-object + Barron a.s. lift (research-level)**:
    McMillan を「Mathlib 不在の新規」として着手したが **`InformationTheory.kraft_mcmillan_inequality` が既存 genuine** と判明 (再発明回避、`ShannonCode.lean:25-27` の「Mathlib に無い」docstring は古い)。`Common2026/Shannon/McMillanKraftBridge.lean` (sorryAx 非依存) で project の Kraft/Gibbs 枠に wire: `kraftSum_le_one_of_uniquelyDecodable` + **期待値 converse `entropyD_le_expectedLength_of_uniquelyDecodable` (`H_D ≤ E[L]`)** genuine。
    - **だが LZ78 converse には直接効かない** (honest): (1) `lz78PhraseStrings` は **prefix-complete で UD でない** (真の UD object は encoded (index,symbol) stream、別構造の新規構築要)。`_nodup` は UD の必要条件にすぎず不十分。(2) McMillan/Gibbs は**期待値のみ**、`IsLZ78ConverseCodingLowerBound` は a.s.-eventual pointwise (LZ78 は pointwise で Shannon code を破れる) → lift は **Barron/competitive-optimality 系の research-level**。
    <br>**LZ78 両半分の確定特定**: achievability = tree-node AEP (CT 13.5.5 length-grouping、research-level a.s.-ergodic)、converse = UD-object 構築 + Barron a.s. lift (research-level a.s.-ergodic)。**両者とも expectation-level/foundation は genuine 済 (envelope / McMillan 期待値 converse)、a.s.-eventual lift が研究レベル**。**A群 確定 (~35 エージェント)**: Chernoff 標準B完成 (1/3)。Huffman/LZ78 = 全 FALSE foundation を disproof で暴き両件 satisfiable honest frontier まで精密 localize、残核は全て research-level a.s.-ergodic/structural (Huffman length-multiset 構造定理、LZ78 tree-node AEP + Barron lift)、autonomous iteration の射程外。McMillan は Mathlib 既存と判明し bridge 済 (gap でなかった)。偽完遂ゼロ、lake build 全 clean。
    <br>**→ LZ78 完遂は incremental 専用ロードマップ [`lz78-completion-roadmap.md`](shannon/lz78-completion-roadmap.md) に派生** (M1 UD-object → M2 length-grouping Ziv → M3 tree-node AEP → M4 Barron lift → M5 合成、各 milestone が genuine deliverable、既知地雷 D1-D7 記載)。`/goal` 反復でなく腰を据えた漸進で進める方針。
