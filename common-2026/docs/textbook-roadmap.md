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

| Ch. | 章 | 状態 | 代表 (済) | 残 seed |
|---|---|---|---|---|
| 2 | Entropy / MI / DPI | ✅ | Entropy, MutualInfo, MIChainRule, DPI | — |
| 3 | AEP | ✅ | aep_ae, aep_inProbability, typicalSet | — |
| 4 | Entropy Rate / SMB | ✅ | entropyRate_*, ShannonMcMillanBreiman, BirkhoffErgodic | — |
| 5 | Data Compression | 🟡 | ShannonCode, Kraft, Huffman weak form, Arithmetic SFE, LZ78 pass-through | T1-A'' Huffman 強形 (research-level、frontier 節), T4-A discharge |
| 6 | Gambling | ✖ scope-out | — | — |
| 7 | Channel Capacity | ✅ | shannon_noisy_..._general_full, _strong_converse, _feedback_complete | — |
| 8 | Differential Entropy | ✅ | differentialEntropy_gaussianReal, _le_gaussian_of_variance_le | — |
| 9 | Gaussian Channel | 🟡 | AWGN / Parallel Gaussian / Shannon-Hartley 各 pass-through publish (F-1 / L-PG0 / L-WF1 IVT 完全 discharge) | T2-A/B/C body discharge (continuous typicality + Nyquist 2W-DOF = frontier) |
| 10 | Rate Distortion | ✅ | rate_distortion_achievability, _converse_*, _convexity, n-letter converse | — |
| 11 | Statistics | 🟡 | Stein / Sanov / Pinsker / Csiszar 🟢、**Chernoff 完成 (judgment #5)**、Hoeffding tradeoff exp 🟢ʰ、Cramér CLT closure 🟢ʰ | T1-C Phase C completion, T1-D Hoeffding sandwich body |
| 12 | Maximum Entropy | 🟡 | entropy_le_log_card, entropy_eq_log_card_iff | T3-A Constrained MaxEnt (Lagrange / exponential family) |
| 13 | Universal Coding | 🟡 | LZ78 pass-through (sorryAx-free, 2 honest hyps)、Arithmetic SFE 🟢ʰ | T4-A 5 discharge family (research-level、別 roadmap `lz78-completion-roadmap.md`) |
| 14 | Kolmogorov | ✖ scope-out | — | — |
| 15 | Network IT | 🟡 | SlepianWolf / Separation 🟢、MAC / BC / Relay / Wyner-Ziv outer+inner pass-through (judgment #3 で circular DEFECT 7 本修復済) | T3-B/C/D/F body discharge (multi-user Fano + joint typicality = (a) 量の壁) |
| 16 | Portfolio | ✖ scope-out | — | — |
| 17 | Inequalities | 🟡 | Han / Shearer / LoomisWhitney / BrascampLieb / Pinsker 🟢、Fisher V2 + EPI + BM pass-through (Gaussian saturation full discharge) | T2-D EPI body (Stam = (b) 解析の壁、frontier), T2-E BM honest landing, T2-F Fisher |

状態: ✅ = 主定理 publish 済 / 🟡 = 部分達成 / 🟢ʰ = honest hyps 付き完成 / ✖ = scope-out。**規模見積**: 残合計 ~14-21k 行 (既存 ~30k に対し 1/2)。

## 「Mathlib 壁」5 分類

残 gap を 5 種に分解 (突破困難度と投資規模が異なる):

- **(a) 量の壁** (低、未構築): well-understood、Mathlib に補題不在で一から数百行。multi-user Fano + joint typicality (Ch.15)、continuous AEP (Ch.9 F-2)、BM slice u.s.c. (Ch.17)
- **(b) 解析の壁** (中〜高): 計算体系自体を建てる型。condExp-of-score = Stam Step 1-2 → EPI body (Ch.17)、Mathlib に微分エントロピー / Fisher 情報の解析体系不在で PR 級 ~120-300 行 upstream
- **(c) 数学的深さ** (高、真の壁): Nyquist 2W-DOF (Ch.9 Shannon-Hartley)、prolate-spheroidal 次元定理、C&T 自身が厳密証明せず → **scope 決断点** (公理引用 or scope-out が現実解)
- **(d) 実は選択** (de-circularize 済): "ROI 無し" の婉曲表現で「壁」と呼ばれていたもの、現在は honest 開示のみ
- **(e) scaffolding-was-false** (中〜大): 既存縮約 predicate / 定義が偽 / 循環 / 不健全で discharge 不能、genuine 構成を一から組み直す必要 (Huffman mergedMeasure / LZ78 per-block Ziv core / Chernoff `IsBayesErrorPerTiltLowerBound` で実観測、judgment #4)

## frontier (現時点の残壁)

- **Stam → EPI** (Ch.17): condExp-of-score = (b) 解析の壁、PR 級 upstream
- **Nyquist 2W-DOF** (Ch.9): (c) 真の壁、原稿執筆時に scope 決断
- **Huffman 強形** (Ch.5): `mergedMeasure` card-2 redesign + length-multiset 構造定理 = research-level a.s.-ergodic、honest frontier `huffmanLength_optimal_modulo_aux_ident` まで精密 localize 済 (judgment #6)
- **LZ78 完全完遂** (Ch.13): achievability = tree-node AEP (CT 13.5.5 length-grouping) + converse = UD-object + Barron a.s. lift、両者 research-level、専用 roadmap → [`lz78-completion-roadmap.md`](shannon/lz78-completion-roadmap.md)

詳細歴史 (FLAW-VACUOUS 監査 / Mathlib 壁 taxonomy 起源 / 実態整合監査) は [`flaw-vacuous-review-2026-05-20.md`](shannon/flaw-vacuous-review-2026-05-20.md) + `docs/audit/` 配下を参照。

## 教科書原稿 (層 3) / 次の一手

- 層 3 (原稿) は未着手 (`docs/textbook/` 未生成)、これが現状の真のボトルネック
- genuine 🟢 で着手可能な章: Ch.2 / 3 / 4 / 7 / 8 / 10
- **合意した次の一手**: 完成済み 1 章 (Ch.2 or Ch.7) で原稿層をパイロット起動 — 本文が「定理 Y は検証済み」と書くことで、どの load-bearing gap が本当に効くかが具体化する

## 判断ログ

戦略遷移のみ記録。wave 別 publish 集計 / 各 seed の publish 履歴 / sub-predicate 詳細は `git log` + plan / inventory が SoT。

1. **2026-05-18〜05-20 並列実装 11 wave → 累計 ~50k 行 publish**: 18 seed の pass-through 主定理 + sub-predicate body discharge を 5〜22 並列で駆動 (AWGN / Parallel Gaussian / Shannon-Hartley / MAC / BC / Relay / EPI / Brunn-Minkowski / Wyner-Ziv / LZ78 / Arithmetic / Hoeffding / Chernoff / Cramér / Fisher 全 publish)。残存 frontier gap: condExp-of-score / infinitePi-tilted RN / WZ joint perspective convexity (後 2 件は次 wave で discharge、後者は pmf 形採用)
2. **2026-05-20 Cramér CLT closure**: Mathlib CLT を tilted ambient に実適用、`cramer_lower_at_cgfDeriv_unconditional` で Cramér 下界 `−Λ*(a)` を最適 tilt 閾値で residual 仮定なし達成。残存: condExp-of-score (Stam Step1-2、PR級) + Chernoff converse pmf-level port
3. **2026-05-21 標準 B 確定 + Mathlib 壁 4 分類**: 「完成 = 定理そのものの無条件機械検証」を doctrine 化。Mathlib 壁を (a)/(b)/(c)/(d) 4 種に taxonomy 化、残 gap の大半は「未構築の定型量」で真の壁は Stam + Nyquist のみと仮置き (#4 で撤回)。同 session で MAC/BC/Relay の circular DEFECT 7 本を発見し全 honest-terminal に修復
4. **2026-05-21 A 群着手 — 「壁なし 3 件」分類が両方向で誤りと判明 + (e) scaffolding-was-false 追加**: 既存縮約 predicate が 0-sorry で偽 / 循環 / 不健全命題を隠していたことを実装で発見 (Huffman SwapNorm 偽鎖 / Chernoff `IsBayesErrorPerTiltLowerBound` 偽 / LZ78 converse 計画路 不健全)。faithful 反例検証で偽を機械確認、A 群残 crux は数学的深さでなく構造リファクタが支配
5. **2026-05-21 Chernoff 標準 B 完成 (1/3)**: `chernoff_lemma_tendsto_holds` を regularity-only / sorryAx-free / 標準 B で publish (Cover-Thomas Thm 11.9.1)。鍵 = 一次最適性 (Fermat for `chernoffZSum`) + Q-LLN + reindex `infinitePi_map_take`
6. **2026-05-21 Huffman / LZ78 完遂 frontier 確定 (両者 research-level)**: ~35 エージェントの徹底 localization の末、両者の残核を研究レベルと確定。
   - Huffman: `mergedMeasure` singleton 形が FALSE (card-2 形に redesign 必要)、`MergedHuffmanAuxIdentHypothesis` も FALSE (faithful 反例 1.13%)、決定化 (colex tie-break) は (ii)(iii) を解消したが first-step identification + collapse correspondence が残る。honest frontier = `huffmanLength_optimal_modulo_aux_ident`
   - LZ78: per-block Ziv core (clean / overhead 双方) は数学的 FALSE (machine-checked disproof publish)、genuine は a.s.-eventual + CT 13.5.5 length-grouping、achievability honest frontier = `lz78_two_sided_optimality_distinct_aseventual`、converse は McMillan (Mathlib 既存 `kraft_mcmillan_inequality`) を bridge 済だが UD-object + Barron lift が research-level。完遂は専用 roadmap [`lz78-completion-roadmap.md`](shannon/lz78-completion-roadmap.md) に派生
7. **2026-05-25 DoD 2 段階確定 + load-bearing hyp 禁止** (CLAUDE.md 改訂): DoD = type-check done / proof done の 2 段階に分離、proof done = 0 sorry ∧ 0 @residual を新バーに。撤退口は **`sorry` + `@residual(<class>:<slug>)`** のみ、`*Hypothesis` predicate (旧 🟢ʰ load-bearing-hyp regime) は honesty defect として禁止。コード側の sorry-based 移行は family 単位で別セッション
8. **2026-05-26 ロードマップ整理**: 旧 #1–#15 (wave 別実装集計) + 旧 #17–#26 (Huffman/LZ78 moonshot grind 詳細) + 旧 seed カード詳細 (239 行) + 実態整合監査 (74 行) + FLAW-VACUOUS 詳細を削除し、本ファイルを「章状態 + frontier + 戦略遷移」の上位 index に縮約 (994→~85 行、~91% 圧縮)。SoT 重複解消 — 詳細は plan / git log / CLAUDE.md / audit-tags.md / `flaw-vacuous-review-2026-05-20.md`
