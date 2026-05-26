# Verified Information Theory Textbook ロードマップ 📚

> Cover & Thomas *Elements of Information Theory* を骨格に Lean 4 + Mathlib で **標準 B (proof done = 0 sorry ∧ 0 @residual)** を狙う上位 index。
> 章状態 + 残壁 + 戦略遷移のみ。各 seed の statement / 規模 / publish 履歴は `docs/<family>/<topic>-moonshot-plan.md` が SoT、検証 doctrine は CLAUDE.md「検証の誠実性」+ `docs/audit/audit-tags.md`、wave 別実装履歴は `git log` が SoT。

## ゴール

Cover & Thomas (2nd ed.) **Ch.2–12, 15, 17** を Lean 形式化された定理から生成される教科書として publish。成果物 3 層 = (1) Verified library (`Common2026/`) + (2) Typed RV API (`H(X)` / `I(X;Y)` 等の書き味) + (3) markdown / LaTeX 原稿。

**scope-out**: Ch.6 Gambling / Ch.13 LZ complexity (LZ78 漸近最適性は in) / Ch.14 Kolmogorov Complexity / Ch.16 Portfolio Theory。

## 完成判定 (DoD 2 段階 = 標準 B)

- **type-check done** (commit OK): `lake env lean <file>` 0 errors、`sorry` warning は `@residual(<class>:<slug>)` 付き
- **proof done = 標準 B** (完成): 上記 + 0 `sorry` + 0 `@residual`

**仮説の区別**: regularity-hyp (full-support / `IsFiniteMeasure` / `Var > 0` / measurability) は precondition で proof done と両立。**load-bearing-hyp (証明の核心を抱える `*Hypothesis` predicate) は禁止** — 該当箇所は `sorry` + `@residual` で表現する (詳細: CLAUDE.md「検証の誠実性」、移行: [[sorry-based-migration]])。

## 章対応進捗

**2026-05-26 audit 反映済** (9 並列 chapter audit、judgment #9)。状態凡例: ✅ = 主定理 proof done / 🟢ʰ = honest hyps 付き / 🟡 = 部分達成 / ✖ = scope-out。

| Ch. | 章 | 状態 | 代表 (proof done / pass-through) | 残 seed / frontier |
|---|---|---|---|---|
| 2 | Entropy / MI / DPI | ✅ | Entropy, MutualInfo, MIChainRule, CondMutualInfo, DPI, CondEntropyMemoryless, Fano | — |
| 3 | AEP | ✅ | aep_ae, aep_inProbability, typicalSet, stronglyTypicalSet | — |
| 4 | Entropy Rate / SMB | ✅ | entropyRate, `shannon_mcmillan_breiman` (unconditional), `birkhoff_ergodic_ae` (unconditional), BackwardMartingale | — |
| 5 | Data Compression | 🟡 | ShannonCode / Kraft / McMillan ✅、Arithmetic SFE ✅ (prefix / UD)、Huffman weak `huffmanLength_kraft_*` | T1-A' 2-hyp vertical reduction (21 wrapper)、T1-A'' Huffman 強形 `huffmanLength_optimal_modulo_aux_ident` (card-2 mergedMeasure redesign 進行中)、**DEFECT-untracked: HuffmanSwapNormalizationBody の `EqualizingPerm*Hypothesis` 4 件 (反例で偽性 ack、retract/successor 未紐付け)** |
| 6 | Gambling | ✖ scope-out | — | — |
| 7 | Channel Capacity | ✅ | `shannon_noisy_..._general_full` (FullDischarge), `_feedback_complete`, `strong_converse_singleShot` (Verdú-Han 単発のみ) | strong converse asymptotic (`Pe → 1`, R > C) は deferred plan; Draft `ConverseGeneralComplete` 2 sorry は `_memoryless_pure` で置換可 |
| 8 | Differential Entropy | ✅ (1-var) / 🟡 (n-var Draft) | `differentialEntropy_gaussianReal`, `_le_gaussian_of_variance_le`, KLDivContinuous | n-var subadditivity `jointDifferentialEntropyPi_le_sum` (Draft 2 sorry、`plan:multivariate-diffentropy-subadditivity-plan`、Parallel Gaussian L-PG1 と共有壁) |
| 9 | Gaussian Channel | 🟡 | AWGN main + `awgn_capacity_closed_form`、Parallel Gaussian `parallel_gaussian_capacity_formula_minimal` (L-PG1 honest sup-sandwich、`@audit:ok`)、Shannon-Hartley + wideband limit、F-1 / L-PG0 / L-WF1/WF2 discharge | **AWGN F-2** `IsAwgnTypicalityHypothesis` = `@audit:defect(circular)` tier-5 (closure plan 紐付け済); **F-3** `IsAwgnConverseHypothesis` 同上 + `IsAwgnF3PerLetterHypothesis := True` `@audit:defect(prop-true)`; **Nyquist 2W-DOF** `IsTwoWDegreesOfFreedom` degenerate-def hypothesis (**tier-5 タグ未付与** — 要 retro-tag); MI 分解 Draft 2 sorry |
| 10 | Rate Distortion | ✅ (pmf-form) / 🟢ʰ (measure-form Draft) | `rate_distortion_achievability` (Shannon), `rate_distortion_converse_single_shot/_specified`, `rateDistortionFunction_convexOn_pmf` (3 件 `@audit:ok`) | Draft measure-form: convexity (1) / n-letter converse (1) / achievability witness-form + partial-discharge (2) = 4 sorry / 4 residual; pmf ↔ measure bridge 1 本で複数 closure 可能性 |
| 11 | Statistics | 🟢ʰ | Stein / StrongStein / Sanov / SanovLDP / SanovLDPEquality / Pinsker (+sharp) / Csiszar / CondMethodOfTypes ✅、Chernoff **achievability** `chernoff_lemma_achievability` (one-sided liminf) ✅、Hoeffding sandwich Tendsto + tradeoff exp、Cramér LC2 discharge ext ✅ | **roadmap 修正**: judgment #5 が主張する `chernoff_lemma_tendsto_holds` (両側 Tendsto / 標準 B) は publish されておらず、achievability 半分のみ。converse は Draft staged (`plan:chernoff-converse-sanov-discharge`、6 file / 41 sorry / 12 defect); Hoeffding interior body (Draft 4 file / 19 sorry); Cramér CLT closure + LC2 Phase C (Draft 5 file / 36 sorry); main `hoeffding_tradeoff_with_hypothesis` (4-hyp pass-through) は tier-4 marker 未付与 |
| 12 | Maximum Entropy | ✅ | `entropy_le_log_card`, `entropy_eq_log_card_iff`, `entropy_le_gibbs_of_constraints`, `expFamily_maximizes_entropy_of_KKT` (KKT / exponential family / Legendre 同一性 完成) | — (旧 T3-A Constrained MaxEnt は audit で closure 確認、`MaxEntropyConstrained` + `MaxEntropyConstrainedKKT` 全 0 sorry) |
| 13 | Universal Coding | 🟡 | Arithmetic ✅ (expected_length_bounds / prefix_free / unique_decodable)、LZ78 UD-object + path-prefix tree AEP sorry-free、headline `lz78_two_sided_optimality_distinct_aseventual` (2 satisfiable load-bearing hyp: `IsLZ78ZivAsEventual`, `IsLZ78ConverseCodingLowerBound`) | M3 variable-depth tree AEP + M4 Barron a.s. lift = research-level、`lz78-completion-roadmap.md`; 旧 FALSE per-block `IsLZ78ZivCombinatorialCore` 撤回済、3 件 `@residual(defect:false-hypothesis)` は successor plan 付き |
| 14 | Kolmogorov | ✖ scope-out | — | — |
| 15 | Network IT | 🟡 | Slepian-Wolf 完全 ✅ (achievability + 4 converse、0/0/0)、MAC / BC / Relay DF / Wyner-Ziv main pass-through 0/0、Wyner-Ziv convexity body 4 file ✅、judgment #3 de-circularization は散文 De-circularization note で記録 | T3-B/C/D/F: Draft 23 file = 64 tactic-sorry / 91 residual / 4 plan slug (`wyner-ziv-discharge` 27 / `relay-inner-bound` 29 / `mac-bc-sorry-migration` 23 / `relay-cutset` 9); load-bearing predicate 15 本 `@audit:retract-candidate`; multi-user Fano + joint typicality = (a) 量の壁; **judgment #3 「circular 7 本修復」の機械可読 `@audit:closed-by-successor` タグ未付与** |
| 16 | Portfolio | ✖ scope-out | — | — |
| 17 | Inequalities | 🟡 | Han / HanD / Shearer / LoomisWhitney / BrascampLieb / Polymatroid / Pinsker (+sharp) / Hypercube / StamGaussianBound / HeatFlowPath ✅、EPI Gaussian-saturation pass-through (`entropy_power_inequality_gaussian_full`)、Stam Step 1 honestly discharged (`IsStamScoreConvHyp` intro 補題 tier-1)、Fisher V2 + deBruijn 0 body sorry (IBP 1 honest wall) | **T2-D EPI Step 2**: `IsStamCondExpCSHyp` (conditional CS) = (b) 解析の壁 frontier; **2 件 tier-5 `:Prop:=True` defect** `IsStamInequalityHypothesis` / `IsDeBruijnIntegrationHypothesis` (closed-by-successor 付与済、但し主定理は honest 経路を別途持つ); **32 件 legacy `@audit:suspect` の sorry-based migration**; T2-E BM: `IsBMEntropyPowerVolumeHyp` (Cover-Thomas sqrt 形) honest wall + Draft 16 sorry (BMFunctional 11、BM 4、EPIConvolutionDensity 1); T2-F Fisher legacy 6 件 |

**規模見積**: 残合計 ~12-18k 行 (既存 ~30k に対し 1/2 弱、Ch.12 closure + Ch.10 pmf-form 確定で前回見積より圧縮)。

## 「Mathlib 壁」5 分類

残 gap を 5 種に分解 (突破困難度と投資規模が異なる):

- **(a) 量の壁** (低、未構築): well-understood、Mathlib に補題不在で一から数百行。multi-user Fano + joint typicality (Ch.15)、continuous AEP (Ch.9 F-2)、BM slice u.s.c. (Ch.17)、variable-depth tree AEP (Ch.13 M3)
- **(b) 解析の壁** (中〜高): 計算体系自体を建てる型。condExp-of-score = Stam Step 2 → EPI body (Ch.17)、Mathlib に微分エントロピー / Fisher 情報の解析体系不在で PR 級 ~120-300 行 upstream
- **(c) 数学的深さ** (高、真の壁): Nyquist 2W-DOF (Ch.9 Shannon-Hartley、現コードは `IsTwoWDegreesOfFreedom` degenerate-def 経由で凍結中)、prolate-spheroidal 次元定理、C&T 自身が厳密証明せず → **scope 決断点** (公理引用 or scope-out が現実解)
- **(d) 実は選択** (de-circularize 済): "ROI 無し" の婉曲表現で「壁」と呼ばれていたもの、現在は honest 開示のみ
- **(e) scaffolding-was-false** (中〜大): 既存縮約 predicate / 定義が偽 / 循環 / 不健全で discharge 不能、genuine 構成を一から組み直す必要 (Huffman mergedMeasure / LZ78 per-block Ziv core / Chernoff `IsBayesErrorPerTiltLowerBound` で実観測、judgment #4)

## frontier (現時点の残壁)

- **Stam Step 2 → EPI** (Ch.17): `IsStamCondExpCSHyp` (conditional CS) = (b) 解析の壁、Mathlib `condExp` Jensen 不在、PR 級 upstream
- **Nyquist 2W-DOF** (Ch.9): (c) 真の壁、`IsTwoWDegreesOfFreedom` degenerate-def hypothesis で凍結中、原稿執筆時に scope 決断
- **Huffman 強形** (Ch.5): `mergedMeasure` card-2 redesign 進行中、honest frontier `huffmanLength_optimal_modulo_aux_ident` まで精密 localize 済 (judgment #6)
- **LZ78 完全完遂** (Ch.13): M3 variable-depth tree AEP + M4 Barron a.s. lift = research-level、専用 roadmap → [`lz78-completion-roadmap.md`](shannon/lz78-completion-roadmap.md)
- **Network IT body discharge** (Ch.15): MAC / BC / Relay / Wyner-Ziv の Draft 23 file = 64 sorry / 91 residual、4 plan slug に分割済、multi-user Fano + joint typicality の (a) 量の壁
- **AWGN F-2/F-3** (Ch.9): tier-5 circular hypothesis (`IsAwgnTypicalityHypothesis` / `IsAwgnConverseHypothesis` / `IsAwgnF3PerLetterHypothesis := True`) で凍結中、analytic body (sphere packing / continuous AEP / random codebook) は未着手で (a) 量の壁

## 監査ハイライト (2026-05-26 — 9 並列 chapter audit、judgment #9)

audit が detect した既存 roadmap との乖離 + 未追跡 honesty defect は別 session で trial 修正する候補。本ロードマップでは認識のみ記録、code 修正は後続。

### roadmap claim と実態の乖離

- **Ch.7 `_strong_converse` 過大表示**: `channelCoding_strong_converse_singleShot` (Verdú-Han 単発下界) のみ存在。Cover-Thomas 7.9 asymptotic `Pe → 1` (R > C) は file docstring 自身が「deferred plan」と明記。
- **Ch.11 judgment #5 `chernoff_lemma_tendsto_holds` 不在**: `Common2026/` 内に当該名 declaration が存在せず、`Chernoff.lean:1059` `chernoff_lemma_achievability` (one-sided liminf) のみ。「Chernoff 完成 (1/3)」表記は achievability 半分のみで、converse + Tendsto は Draft で staged (`plan:chernoff-converse-sanov-discharge`)。
- **Ch.12 状態昇格**: 旧 🟡 → ✅。`MaxEntropyConstrained` (Boltzmann–Gibbs) + `MaxEntropyConstrainedKKT` (Lagrange / exponential family / Legendre) 両 layer が 0 sorry / 0 residual で publish 済、T3-A は closure。
- **Ch.10 ✅ / 🟢ʰ の二重判定**: pmf-form (有限型 + ℝ-valued pmf) は genuine proof done、measure-form 一般化版は Draft 隔離で 4 sorry。textbook scope を pmf-form 完成とみなすか measure-form 完成を要求するかで状態が変わる。

### 未追跡 / 機械可読化漏れ tier-5 / tier-4 markers

- **Ch.5 `HuffmanSwapNormalizationBody`** `EqualizingPerm*Hypothesis` 4 件 = false predicate (docstring に反例 `ll=![1,2,3], a=0, b=1` 自認) → `@audit:retract-candidate` / `@audit:closed-by-successor` 未紐付け、CLAUDE.md「sorry を書けない箇所での対処順序」第二選択の要件不充足
- **Ch.9 `IsTwoWDegreesOfFreedom`** degenerate-def hypothesis (ShannonHartley.lean:128) = 自己申告「hypothesis pass-through, NOT a self-contained proof」だが `@audit:defect(degenerate)` タグ未付与
- **Ch.11 `hoeffding_tradeoff_with_hypothesis`** (HoeffdingTradeoff.lean:296) = 4 仮説 sandwich pass-through (旧方針 🟢ʰ 相当) だが tier-4 marker 未付与
- **Ch.11 `IsHoeffdingMinimizerFullSupport`** (HoeffdingSandwichBody.lean:127) = docstring に「general-α discharge は L-H4 deferred」記述あるが `@residual` / `@audit:*` tag 不在
- **Ch.15 judgment #3 「circular 7 本修復済」**: `@audit:closed-by-successor` hit 0 (散文 De-circularization note 2 件のみ、`BroadcastChannelRandomCodebook.lean:6`, `RelayDFBlockMarkovBody.lean:20`)。retro-tag 1 turn で機械可読化推奨
- **Ch.17 EPI**: 2 件 `:Prop:=True` (`IsStamInequalityHypothesis`、`IsDeBruijnIntegrationHypothesis`) は `@audit:defect(prop-true)` + `closed-by-successor` 付与済、但し signature 露出のみ; 32 件 legacy `@audit:suspect` (EPIL3Integration 30 等) の sorry-based migration が hotspot

### 集計

- Ch.2-4 + 8 (1-var) + 12 + Slepian-Wolf + Han 群 + Pinsker 群 + Stein/Sanov/Csiszar + Hoeffding sandwich Tendsto + Cramér LC2 ext = **genuine proof done に到達した seed の主要 family** (約 14-17 主定理 family、文献の "完成" と互換)
- 残 134 sorry / 113 residual (audit 推定総和、Draft 隔離分含む、stale-imports script 進行中のため精密値は別途)
- 4 plan slug = Ch.15 (`wyner-ziv-discharge` / `relay-inner-bound` / `mac-bc-sorry-migration` / `relay-cutset`)、3 plan slug = Ch.10 (`achievability-phase-e-strong` / `converse` / `convexity`)、1 plan slug = Ch.11 (`chernoff-converse-sanov-discharge`)、1 plan slug = Ch.13 (`lz78-residual-discharge` + `lz78-aseventual-achievability`)、複数 plan slug = Ch.17 (EPI / BM / Fisher 各 family)、1 plan = Ch.5 (`huffman-strong-form-completion` 等)
- 専用 roadmap: `docs/shannon/lz78-completion-roadmap.md` (Ch.13 M1-M5 + 地雷 D1-D7)

詳細歴史 (FLAW-VACUOUS 監査 / Mathlib 壁 taxonomy 起源 / 実態整合監査) は [`flaw-vacuous-review-2026-05-20.md`](shannon/flaw-vacuous-review-2026-05-20.md) + `docs/audit/` 配下を参照。

## 教科書原稿 (層 3) / 次の一手

- 層 3 (原稿) は未着手 (`docs/textbook/` 未生成)、これが現状の真のボトルネック
- genuine 🟢 で着手可能な章: **Ch.2 / 3 / 4 / 7 / 8 (1-var) / 10 (pmf-form) / 12 / 17 (Han/Shearer/LW/BL/Pinsker/Hypercube/StamGauss/HeatFlow + EPI Gaussian)** — Ch.12 と Ch.17 inequality 群が今回 audit で確定昇格
- **合意した次の一手**: 完成済み 1 章 (Ch.2 or Ch.7 or Ch.12) で原稿層をパイロット起動 — 本文が「定理 Y は検証済み」と書くことで、どの load-bearing gap が本当に効くかが具体化する

## 判断ログ

戦略遷移のみ記録。wave 別 publish 集計 / 各 seed の publish 履歴 / sub-predicate 詳細は `git log` + plan / inventory が SoT。

1. **2026-05-18〜05-20 並列実装 11 wave → 累計 ~50k 行 publish**: 18 seed の pass-through 主定理 + sub-predicate body discharge を 5〜22 並列で駆動 (AWGN / Parallel Gaussian / Shannon-Hartley / MAC / BC / Relay / EPI / Brunn-Minkowski / Wyner-Ziv / LZ78 / Arithmetic / Hoeffding / Chernoff / Cramér / Fisher 全 publish)。残存 frontier gap: condExp-of-score / infinitePi-tilted RN / WZ joint perspective convexity (後 2 件は次 wave で discharge、後者は pmf 形採用)
2. **2026-05-20 Cramér CLT closure**: Mathlib CLT を tilted ambient に実適用、`cramer_lower_at_cgfDeriv_unconditional` で Cramér 下界 `−Λ*(a)` を最適 tilt 閾値で residual 仮定なし達成。残存: condExp-of-score (Stam Step1-2、PR級) + Chernoff converse pmf-level port
3. **2026-05-21 標準 B 確定 + Mathlib 壁 4 分類**: 「完成 = 定理そのものの無条件機械検証」を doctrine 化。Mathlib 壁を (a)/(b)/(c)/(d) 4 種に taxonomy 化、残 gap の大半は「未構築の定型量」で真の壁は Stam + Nyquist のみと仮置き (#4 で撤回)。同 session で MAC/BC/Relay の circular DEFECT 7 本を発見し全 honest-terminal に修復
4. **2026-05-21 A 群着手 — 「壁なし 3 件」分類が両方向で誤りと判明 + (e) scaffolding-was-false 追加**: 既存縮約 predicate が 0-sorry で偽 / 循環 / 不健全命題を隠していたことを実装で発見 (Huffman SwapNorm 偽鎖 / Chernoff `IsBayesErrorPerTiltLowerBound` 偽 / LZ78 converse 計画路 不健全)。faithful 反例検証で偽を機械確認、A 群残 crux は数学的深さでなく構造リファクタが支配
5. **2026-05-21 Chernoff 標準 B 完成 (主張) — judgment #9 で撤回**: 当時 `chernoff_lemma_tendsto_holds` を publish と記載したが、9 並列 audit で **当該名 declaration は `Common2026/` 内に存在せず**、`chernoff_lemma_achievability` (one-sided liminf) のみが完成と確認。両側 Tendsto / converse は Draft staged (`plan:chernoff-converse-sanov-discharge`、6 file / 41 sorry / 12 defect 残置) — 表記を「Chernoff achievability ✅」に格下げ
6. **2026-05-21 Huffman / LZ78 完遂 frontier 確定 (両者 research-level)**: ~35 エージェントの徹底 localization の末、両者の残核を研究レベルと確定。
   - Huffman: `mergedMeasure` singleton 形が FALSE (card-2 形に redesign 必要)、`MergedHuffmanAuxIdentHypothesis` も FALSE (faithful 反例 1.13%)、決定化 (colex tie-break) は (ii)(iii) を解消したが first-step identification + collapse correspondence が残る。honest frontier = `huffmanLength_optimal_modulo_aux_ident`
   - LZ78: per-block Ziv core (clean / overhead 双方) は数学的 FALSE (machine-checked disproof publish)、genuine は a.s.-eventual + CT 13.5.5 length-grouping、achievability honest frontier = `lz78_two_sided_optimality_distinct_aseventual`、converse は McMillan (Mathlib 既存 `kraft_mcmillan_inequality`) を bridge 済だが UD-object + Barron lift が research-level。完遂は専用 roadmap [`lz78-completion-roadmap.md`](shannon/lz78-completion-roadmap.md) に派生
7. **2026-05-25 DoD 2 段階確定 + load-bearing hyp 禁止** (CLAUDE.md 改訂): DoD = type-check done / proof done の 2 段階に分離、proof done = 0 sorry ∧ 0 @residual を新バーに。撤退口は **`sorry` + `@residual(<class>:<slug>)`** のみ、`*Hypothesis` predicate (旧 🟢ʰ load-bearing-hyp regime) は honesty defect として禁止。コード側の sorry-based 移行は family 単位で別セッション
8. **2026-05-26 ロードマップ整理 (上位 index 化)**: 旧 #1–#15 (wave 別実装集計) + 旧 #17–#26 (Huffman/LZ78 moonshot grind 詳細) + 旧 seed カード詳細 (239 行) + 実態整合監査 (74 行) + FLAW-VACUOUS 詳細を削除し、本ファイルを「章状態 + frontier + 戦略遷移」の上位 index に縮約 (994→~85 行、~91% 圧縮)。SoT 重複解消 — 詳細は plan / git log / CLAUDE.md / audit-tags.md / `flaw-vacuous-review-2026-05-20.md`
9. **2026-05-26 9 並列 chapter audit → 章別実態棚卸**: roadmap の章状態 / 代表定理 / frontier を実コードと突合。**修正**: Ch.12 → ✅ 昇格 (KKT + Boltzmann-Gibbs 完成、T3-A closure)、Ch.5 / 9 / 11 / 15 / 17 の代表定理列を実コード verbatim に揃え直し。**判明**: (a) Ch.7 `_strong_converse` は single-shot のみで asymptotic は deferred、(b) Ch.11 `chernoff_lemma_tendsto_holds` は不在で achievability 半分のみ (judgment #5 表記撤回)、(c) Ch.10 は pmf-form ✅ / measure-form 🟢ʰ の二重判定、(d) Ch.9 AWGN F-2/F-3 は tier-5 circular hypothesis で凍結中 + Nyquist 2W-DOF も degenerate-def 経由で凍結中、(e) 未追跡 markers (HuffmanSwapNorm 4 件 false-hyp / IsTwoWDegreesOfFreedom degenerate / hoeffding_tradeoff_with_hypothesis 4-hyp / judgment #3 circular 7 本散文記録) は別 session で sorry-based migration / retro-tag 候補
