# Verified Information Theory Textbook ロードマップ 📚

> Cover & Thomas *Elements of Information Theory* を骨格に Lean 4 + Mathlib で **標準 B (proof done = 0 sorry ∧ 0 @residual)** を狙う上位 index。
> 章状態 + 残壁 + 戦略遷移のみ。各 seed の statement / 規模 / publish 履歴は `docs/<family>/<topic>-moonshot-plan.md` が SoT、検証 doctrine は CLAUDE.md「検証の誠実性」+ `docs/audit/audit-tags.md`、wave 別実装履歴は `git log` が SoT。

## ゴール

Cover & Thomas (2nd ed.) **Ch.2–12, 15, 17** を Lean 形式化された定理から生成される教科書として publish。成果物 3 層 = (1) Verified library (`Common2026/`) + (2) Typed RV API (`H(X)` / `I(X;Y)` 等の書き味) + (3) markdown / LaTeX 原稿。

## scope-out

**章単位** (元から外す):
- Ch.6 Gambling / Ch.14 Kolmogorov Complexity / Ch.16 Portfolio Theory
- Ch.13 LZ complexity 詳細 (LZ78 漸近最適性は in)

**章内部分 scope-out** (2026-05-26 judgment #10):
- **Ch.9 Shannon-Hartley Nyquist 2W-DOF**: (c) 数学的深さ の真の壁、C&T 自身が厳密証明せず。`IsTwoWDegreesOfFreedom` degenerate-def の凍結を確定
- **Ch.9 AWGN operational 符号化定理 (n-letter achievability + converse)** (2026-05-29 judgment #11): `情報容量 = 操作的容量` の等価性 (Shannon 雑音通信路符号化定理の Gaussian 版)。continuous AEP / SMB・random coding bound・sphere packing・連続領域 MI chain rule・Fano converse など (a) 量の壁が大量 (`AwgnWalls.lean` 6 壁 + `AWGNConverse*`/`AWGNAchievability*`/`AWGNMain` の数十 residual)。原稿パイロット優先方針 (judgment #10) では Nyquist と同じく future work に隔離。Ch.9 は**単一文字情報容量公式 + max-entropy converse** として publish (① genuine ✅)。残る honest sorry+@residual は honest marker として保持 (削除しない)
- **Ch.10 measure-form Rate Distortion**: pmf-form ✅ で C&T 10.5 acceptable、measure-form は将来拡張に隔離
- **Ch.11 Chernoff Information converse / Hoeffding interior body / Cramér Phase C**: C&T §11.9 自身が Sanov `≐` heuristic (textbook rigor で converse は不要)、MacKay/Yeung/El Gamal-Kim は触れもしない。Sanov LDP ✅ から将来 1 段落 corollary 可能
- **Ch.13 LZ78 M3 (variable-depth tree AEP) / M4 (Barron a.s. lift)**: research-level upstream (Mathlib 測度論基盤の新規追加要)、M1 + Arithmetic で Ch.13 closure
- **Ch.15 MAC / Broadcast / Relay / Wyner-Ziv main**: Slepian-Wolf + Wyner-Ziv convexity body で「Distributed Source Coding」mini-chapter として publish (El Gamal-Kim も SW を独立章扱い)
- **Ch.17 EPI 一般版 / Brunn-Minkowski body / Fisher chain legacy**: `_gaussian_saturation` は実質 Gaussian variance additivity (3 行 corollary) で EPI と呼ぶのは name laundering → `entropyPower_gaussian_additivity` リネーム + 一般 EPI は sorry+@residual で signature 維持。CT 17.9 Minkowski determinant は Gaussian additivity から導出可能 (新規 ✅ promote 候補)

## 完成判定 (DoD 2 段階 = 標準 B)

- **type-check done** (commit OK): `lake env lean <file>` 0 errors、`sorry` warning は `@residual(<class>:<slug>)` 付き
- **proof done = 標準 B** (完成): 上記 + 0 `sorry` + 0 `@residual`

**仮説の区別**: regularity-hyp (full-support / `IsFiniteMeasure` / `Var > 0` / measurability) は precondition で proof done と両立。**load-bearing-hyp (証明の核心を抱える `*Hypothesis` predicate) は禁止** — 該当箇所は `sorry` + `@residual` で表現する (詳細: CLAUDE.md「検証の誠実性」、移行: [[sorry-based-migration]])。

## 章対応進捗 (scope-out 反映後)

状態凡例: ✅ = 主定理 proof done / 🟢 = scope 内全完成 (scope-out 後の残 frontier 込み判定) / 🟢ʰ = honest hyps 付き / 🟡 = 部分達成 / ✖ = scope-out。

| Ch. | 章 | 状態 | 代表 (proof done) | 残 frontier (scope 内) |
|---|---|---|---|---|
| 2 | Entropy / MI / DPI | ✅ | Entropy, MutualInfo, MIChainRule, CondMutualInfo, DPI, CondEntropyMemoryless, Fano | — |
| 3 | AEP | ✅ | aep_ae, aep_inProbability, typicalSet, stronglyTypicalSet | — |
| 4 | Entropy Rate / SMB | ✅ | entropyRate, shannon_mcmillan_breiman, birkhoff_ergodic_ae, BackwardMartingale | — |
| 5 | Data Compression | 🟡 | ShannonCode / Kraft / McMillan ✅、Arithmetic SFE ✅ (prefix / UD)、Huffman weak `huffmanLength_kraft_*` ✅、**Huffman 強形 Hyp1 (SwapNormalization) 無条件 genuine discharge 済 ✅** + **決定的 relabel cornerstone `huffmanLengthAux_relabel_det` ✅ (2026-05-30、sorryAx 非依存、`@audit:ok`、docstring-only defect 解消)** | T1-A'' Huffman 強形 `huffmanLength_optimal_modulo_aux_ident`: 残 frontier = collapse correspondence `MergedHuffmanAuxIdentHypothesis` (honest sorry、`huffman-2hyp-vertical-reduction` も要 closure)。**collapse 補題 `collapseLabel_huffmanLengthAux` は FALSE statement と確定 (2026-05-30、機械的反例 + 独立監査 confirm、`@audit:defect(false-statement)`)** — 旧「tie-order 独立 invariant の壁」診断は誤りで、`huffmanLengthAux` の depth は colex tie-break に**依存する**ため、colex を変える relabel (`{a}→{a,b}`) 下の per-symbol 不変性は偽。consumer 設計は per-symbol collapse を捨て leaf-merge / length-multiset reduction へ pivot 必要 (判断ログ #4)。standalone (consumer 0、伝播ゼロ)。注: `EqualizingPerm*Hypothesis` は Common2026 から既に削除済 (旧 roadmap「4 件 retro-tag 必要」は stale) |
| 6 | Gambling | ✖ scope-out | — | — |
| 7 | Channel Capacity | ✅ | `shannon_noisy_..._general_full`, `_feedback_complete`, `strong_converse_singleShot` (Verdú-Han 単発) | strong converse asymptotic (`Pe → 1`, R > C) は deferred plan; Draft `ConverseGeneralComplete` 2 sorry は `_memoryless_pure` で置換可 |
| 8 | Differential Entropy | ✅ (1-var) / ✅ (n-var subadd) | `differentialEntropy_gaussianReal`, `_le_gaussian_of_variance_le`, KLDivContinuous, **n-var subadditivity `jointDifferentialEntropyPi_le_sum` genuine ✅** (2026-05-29、0/0 sorryAx 非依存、監査 OK。`withDensity_map` helper + `pi_withDensity_fin` を self-build、前回 withdrawal は誤診) | — |
| 9 | Gaussian Channel | 🟢 (① ✅ / ② genuine ✅ achiever+converse、headline sorryAx-free) | **① 単一文字情報容量 `awgn_capacity_closed_form_genuine` = (1/2)log(1+P/N) genuine ✅** (0/0、sorryAx 非依存、監査 OK) + hypothesis-free MI 後継 ✅ + ParallelGaussian 電力制約 lintegral pivot ✅ + F-1 / L-PG0 / L-WF1/WF2 discharge。**② 完全 genuine ✅ (2026-05-29)**: achiever (judgment #13) に加え **converse も closure**。最後の residual #5 `parallelOutput_joint_logDensity_integrable` (旧 `@residual(wall:multivariate-mi)`) は **3 者独立再裁定 (inventory + proof-pivot-advisor + honesty-auditor) で self-buildable と確定 → `plan:...-5-closure` reclassify → 多変量 mixture density lift で genuine closure** (def + withDensity 等式 + 上界 + 座標箱 Chebyshev + Gaussian tail 座標積下界 + quadratic 包絡 + `Integrable.mono'` 締め、全 `@audit:ok`、n=0 退化 honest)。`#print axioms parallel_gaussian_capacity_formula_minimal` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free)。教訓: loogle 0 件は壁の必要条件であって十分条件でない (`feedback_independent_wall_recheck`) | **② Parallel Gaussian water-filling 完了 ✅** (achiever + converse + headline すべて genuine、sorryAx-free)。**③ operational 符号化定理は scope-out (judgment #11)**。Shannon-Hartley Nyquist も scope-out |
| 10 | Rate Distortion | ✅ (pmf-form scope) | `rate_distortion_achievability` (Shannon), `rate_distortion_converse_single_shot/_specified`, `rateDistortionFunction_convexOn_pmf` | — (measure-form Draft は **scope-out**) |
| 11 | Statistics | 🟢 (scope 内) | Stein / StrongStein / Sanov / SanovLDP / SanovLDPEquality / Pinsker (+sharp) / Csiszar / CondMethodOfTypes ✅、Chernoff **achievability** `chernoff_lemma_achievability` ✅、Hoeffding sandwich Tendsto + tradeoff exp ✅、Cramér LC2 discharge ext ✅ | `hoeffding_tradeoff_with_hypothesis` tier-4 marker retro-tag。Chernoff converse / Hoeffding interior / Cramér Phase C は **scope-out** (C&T 自身が `≐` heuristic で textbook rigor 達成) |
| 12 | Maximum Entropy | ✅ | `entropy_le_log_card`, `entropy_eq_log_card_iff`, `entropy_le_gibbs_of_constraints`, `expFamily_maximizes_entropy_of_KKT` | — |
| 13 | Universal Coding | 🟢 (scope 内) | Arithmetic ✅ (expected_length_bounds / prefix_free / unique_decodable)、LZ78 M1 `lz78_converse_with_ud_object` ✅ (UD-object 定長 + McMillan 期待値 converse)、headline `lz78_two_sided_optimality_distinct_aseventual` (2 satisfiable load-bearing hyp) | LZ78 M3 (variable-depth tree AEP) / M4 (Barron a.s. lift) は **scope-out** (research-level upstream)。旧 FALSE per-block `IsLZ78ZivCombinatorialCore` 撤回済、3 件 `@residual(defect:false-hypothesis)` は successor plan 付き |
| 14 | Kolmogorov | ✖ scope-out | — | — |
| 15 | Network IT (DSC mini-chapter) | 🟢 | Slepian-Wolf 完全 ✅ (achievability corner + 4 converse、0/0/0)、**Slepian-Wolf Full Rate Region achievability `slepian_wolf_full_rate_region_achievability` ✅ (2026-05-30、proof done、`#print axioms` sorryAx-free、honesty audit 全 `@audit:ok`)** — 3-bound rate region 全域 (`H(X|Y)<R_X`,`H(Y|X)<R_Y`,`H(X,Y)<R_X+R_Y`) を random binning + joint typicality decoder で達成、Wyner-Ziv convexity body ✅ (4 file 0/0/0)、judgment #3 de-circularization は散文 note | judgment #3 「circular 7 本修復」の `@audit:closed-by-successor` 機械可読化 (bookkeeping)。MAC / BC / Relay / Wyner-Ziv main は **scope-out** |
| 16 | Portfolio | ✖ scope-out | — | — |
| 17 | Inequalities | 🟢 (scope 内) / 🟡 | Han / HanD / Shearer / LoomisWhitney / BrascampLieb / Polymatroid / Pinsker (+sharp) / Hypercube / StamGaussianBound / HeatFlowPath ✅、Stam Step 1 honest discharge ✅、**`entropyPower_gaussian_additivity` + `entropyPower_pos/nonneg/gaussianReal` 等 genuine sorryAx-free ✅** (Gaussian EPI = variance additivity) | **⚠ 2026-05-30 honesty 是正: 一般 EPI は proof done でない** — `entropy_power_inequality` (headline) + log/exp form + `epi_via_stam_main` 等 **12 件の `@audit:ok` は誤付与だった** (transitive wall 経由で sorryAx 依存、`#print axioms` sweep で降格)。**EPI Stam Step 2 = scope-out 確定**: 旧 load-bearing hyp `IsStamCauchySchwarzOptimal` (`entropy_power_inequality_via_body` の仮説引数 = tier-5 defect) を shared sorry 補題 `stam_step2_density_wall` (`@residual(wall:stam-step2-density)`) に降格。Rioul 2011「~100 行」見積りは誤り (Fisher info / score / density 計算が Mathlib **全不在**、(a)+(b) 混合壁 ~300 行 PR 級)。active 壁 = `wall:stam-step2-density` + `wall:debruijn-integration` + `plan:epi-stam-to-conclusion-plan`/`-phaseA-plan`。`entropy_power_inequality_gaussian_saturation` → リネーム `entropyPower_gaussian_additivity` (consumer 23+、別 plan); CT 17.9 Minkowski determinant **新規 ✅ promote 候補**。残: `EPIStamStep3Body` の `IsStamTotalExpectation` load-bearing path (`stam_step2_density_wall` と同根、統合候補); EPI 一般版 / BM body / Fisher legacy は **scope-out** |

**規模見積**: scope-out 拡張により残 ~22k 行 Draft + ~250 residual を解放、scope 内 frontier は数百 sorry オーダーに縮小。

## 「Mathlib 壁」5 分類 (scope 内 frontier に残る型)

- **(a) 量の壁** (低、未構築): well-understood、Mathlib に補題不在で一から数百行。Slepian-Wolf Phase E error bound (Ch.15)。(Ch.9 AWGN operational 符号化定理の continuous AEP / sphere packing も本型だったが judgment #11 で scope-out)
- **(b) 解析の壁** (中〜高): 計算体系自体を建てる型。EPI Stam Step 2 (Ch.17) — Rioul 2011 §II-C より score-cond-mean identity + total variance decomposition で ~100 行 density-level computation (従来 ~300 行 PR 級見積りより小)、再見積もり後 scope 内に戻す余地あり
- **(c) 数学的深さ** (高、真の壁): Nyquist 2W-DOF (Ch.9、scope-out 確定)
- **(d) 実は選択** (de-circularize 済): "ROI 無し" の婉曲表現で「壁」と呼ばれていたもの、現在は honest 開示のみ
- **(e) scaffolding-was-false** (中〜大): 既存縮約 predicate / 定義が偽 / 循環 / 不健全で discharge 不能、genuine 構成を一から組み直す。Huffman mergedMeasure card-2 redesign (Ch.5)

## frontier (scope 内 closure 必要)

- **Ch.5 Huffman 強形**: Hyp1 (SwapNormalization) 無条件 discharge 済 ✅ + 決定的 relabel cornerstone `huffmanLengthAux_relabel_det` genuine ✅ (2026-05-30)。**collapse 補題 `collapseLabel_huffmanLengthAux` は FALSE statement と確定** (2026-05-30、機械的反例 + 独立監査、`@audit:defect(false-statement)`、standalone)。**旧「tie-order 独立 invariant の壁」診断は誤り** — `huffmanLengthAux` の depth は colex tie-break に依存し、per-symbol collapse path は dead-end。残 frontier = `MergedHuffmanAuxIdentHypothesis` (`HuffmanWalls.lean:70` honest sorry) の discharge を leaf-merge / length-multiset reduction へ pivot (判断ログ #4、新規設計要)。別壁 `huffman-2hyp-vertical-reduction` も要 closure
- **Ch.8 n-var DiffEnt subadditivity**: genuine ✅ (2026-05-29 closure、もはや壁ではない)
- **Ch.9 ② Parallel Gaussian water-filling**: **完了 ✅ (2026-05-29)** — achiever + converse + headline すべて genuine、`parallel_gaussian_capacity_formula_minimal` sorryAx-free。最後の residual #5 joint log-density integrability を多変量 mixture density lift で genuine closure (3 者独立再裁定で wall→plan reclassify 後)。③ operational 符号化定理は scope-out (judgment #11)。**もはや scope 内 frontier ではない**
- **Ch.15 Slepian-Wolf Full Rate Region**: **完了 ✅ (2026-05-30)** — Phase D/E (decomposition + 4 expectation bound) に加え Phase F (E.5 squeeze + F.3 headline assembly) を genuine closure。`slepian_wolf_full_rate_region_achievability` proof done、sorryAx-free。**もはや scope 内 frontier ではない** (旧「Phase E 確率上界収束のみ残」は誤り — 実際は headline assembly が未実装だった、2026-05-30 実コード確認で訂正)
- **Ch.17 EPI Stam Step 2**: **scope-out 確定 ✅ (2026-05-30)** — load-bearing hyp `IsStamCauchySchwarzOptimal` を shared sorry `stam_step2_density_wall` (`@residual(wall:stam-step2-density)`) に降格、`entropy_power_inequality_via_body` signature から除去。Rioul「~100 行」見積りは誤り (Fisher/score/density 計算 Mathlib 全不在、(a)+(b) 混合壁)。honest sorry 据置で proof-done 集計外
- **Ch.17 EPI @audit:ok 12 件降格済 ✅ (2026-05-30)**: 一般 EPI (`entropy_power_inequality` headline 含む) は transitive wall 経由で sorryAx 依存 = proof done でない。genuine sorryAx-free は Gaussian additivity 系のみ。`#print axioms` sweep で誤付与 tier-1 タグを除去済
- **Ch.17 wall 集約候補**: `EPIStamStep3Body` の `IsStamTotalExpectation` load-bearing path (4 件) が `stam_step2_density_wall` と同根 — shared wall 統合の別 task 候補 (未着手)
- **legacy migration は完了済 (frontier ではない)**: Common2026 に active な `@audit:suspect(`/`@audit:staged(`/`@audit:defer(` declaration タグは **0 件** (paren-pattern 確認、bareword ヒットは全て過去 migration の docstring 内文字列参照)。旧 roadmap「32 件」は stale claim
- **未追跡 marker retro-tag (残)**: Ch.9 `IsTwoWDegreesOfFreedom` / Ch.11 `hoeffding_tradeoff_with_hypothesis` / Ch.15 judgment #3 circular 7 本 (Ch.5 `EqualizingPerm*` は Common2026 から削除済で対象外、Ch.17 `IsStamToEPIBridge` は 2026-05-30 sweep で処理済)

## 教科書原稿 (層 3) / 次の一手

- 層 3 (原稿) は未着手 (`docs/textbook/` 未生成)
- genuine ✅ で原稿起動可能: **Ch.2 / 3 / 4 / 7 / 8 (1-var) / 9 (単一文字 AWGN 容量公式 + max-ent converse) / 10 (pmf-form) / 12 / 17 inequality 群** — scope-out 反映で Ch.9 (③ 除く), Ch.10, 11, 13, 15, 17 も部分 publish 圏内
- **合意した次の一手**: 完成済み 1 章 (Ch.2 or Ch.7 or Ch.12) で原稿層をパイロット起動 — 本文が「定理 Y は検証済み」と書くことで、scope-out した範囲が原稿として acceptable か、scope 内 frontier の優先度がどう動くかが具体化する

## 判断ログ

戦略遷移のみ記録。wave 別 publish 集計 / 各 seed の publish 履歴 / sub-predicate 詳細は `git log` + plan / inventory が SoT。

1. **2026-05-18〜05-20 並列実装 11 wave → 累計 ~50k 行 publish**: 18 seed の pass-through 主定理 + sub-predicate body discharge を 5〜22 並列で駆動
2. **2026-05-20 Cramér CLT closure**: Mathlib CLT を tilted ambient に実適用、`cramer_lower_at_cgfDeriv_unconditional` で Cramér 下界 `−Λ*(a)` を residual 仮定なしで達成
3. **2026-05-21 標準 B 確定 + Mathlib 壁 4 分類**: 「完成 = 定理そのものの無条件機械検証」を doctrine 化。Mathlib 壁を (a)/(b)/(c)/(d) 4 種に taxonomy 化、MAC/BC/Relay の circular DEFECT 7 本を発見し全 honest-terminal に修復
4. **2026-05-21 A 群着手 — 「壁なし 3 件」分類が誤りと判明 + (e) scaffolding-was-false 追加**: 既存縮約 predicate が 0-sorry で偽 / 循環 / 不健全命題を隠していたことを実装で発見 (Huffman SwapNorm 偽鎖 / Chernoff `IsBayesErrorPerTiltLowerBound` 偽 / LZ78 converse 計画路 不健全)
5. **2026-05-21 Chernoff 標準 B 完成 (主張) — judgment #9 で撤回**: `chernoff_lemma_tendsto_holds` は当時 publish と記載したが、当該名 declaration は不在で `chernoff_lemma_achievability` (one-sided liminf) のみ完成と確認
6. **2026-05-21 Huffman / LZ78 完遂 frontier 確定 (両者 research-level)**: ~35 エージェントの徹底 localization の末、両者の残核を研究レベルと確定 (Huffman: `mergedMeasure` card-2 redesign / LZ78: per-block Ziv core FALSE + Barron a.s. lift research-level)
7. **2026-05-25 DoD 2 段階確定 + load-bearing hyp 禁止** (CLAUDE.md 改訂): proof done = 0 sorry ∧ 0 @residual を新バーに、撤退口は `sorry` + `@residual(<class>:<slug>)` のみ、`*Hypothesis` predicate は honesty defect として禁止
8. **2026-05-26 ロードマップ整理 (上位 index 化)**: 旧 #1–#15 + 旧 #17–#26 (Huffman/LZ78 grind 詳細) + seed カード詳細 + FLAW-VACUOUS 詳細を削除し、本ファイルを「章状態 + frontier + 戦略遷移」の上位 index に縮約 (994→~85 行)
9. **2026-05-26 9 並列 chapter audit → 章別実態棚卸**: roadmap の章状態 / 代表定理 / frontier を実コードと突合 (Ch.12 ✅ 昇格、Ch.7/10/11 表記補正、Ch.9 tier-5 + Nyquist degenerate-def 列挙、未追跡 markers 5 件特定)
10. **2026-05-26 scope 縮小決定 (主流教科書調査 + 規模測定)**: 原稿パイロット (Ch.2/7/12) 起動可能規模に縮小するため scope-out 拡張。**根拠**:
    - **Ch.15 部分 scope-out** — Slepian-Wolf + WZ convexity body (~2.3k 行 ✅) で「Distributed Source Coding」mini-chapter として publish 可 (El Gamal-Kim も SW 独立章扱い)、MAC/BC/Relay/WZ main (Draft 11.6k 行) は捨てる
    - **Ch.11 Chernoff Information converse scope-out** — C&T Thm 11.9.1 の "proof" 自身が Sanov `≐` heuristic、MacKay/Yeung/El Gamal-Kim は触れもしない。Sanov LDP ✅ から将来 1 段落 corollary
    - **Ch.17 EPI 一般版 scope-out + リネーム** — 現 `_gaussian_saturation` は実質 Gaussian variance additivity (3 行 corollary)、EPI と呼ぶのは name laundering → `entropyPower_gaussian_additivity` リネーム必須、一般 EPI は sorry+@residual。**bonus**: CT 17.9 Minkowski determinant が Gaussian additivity から直接導出可能 (新規 ✅ 候補)。**留保**: Rioul 2011 §II-C で Stam Step 2 が ~100 行 density 計算 (従来見積り ~300 行 PR 級より小) と判明、再見積もり後 keep 余地
    - **Ch.13 LZ78 M3/M4 scope-out** — variable-depth tree AEP + Barron a.s. lift は research-level upstream、M1 + Arithmetic で Ch.13 closure
    - **Ch.10 measure-form scope-out** — pmf-form ✅ で C&T 10.5 acceptable
    - **Ch.9 Shannon-Hartley Nyquist scope-out** — (c) 数学的深さ の真の壁、C&T 自身が厳密証明せず
    - scope-out 総量 ~22k 行 Draft + ~250 residual 解放、scope 内 frontier は数百 sorry オーダー
11. **2026-05-29 Ch.9 AWGN 単一文字容量 genuine closure + ③ operational 符号化定理 scope-out**:
    - **① 単一文字情報容量 genuine 完成** — `awgn_capacity_closed_form_genuine = (1/2)log(1+P/N)` (0 sorry / 0 residual、`#print axioms` sorryAx 非依存、独立監査 OK)。max-entropy converse 込み。Ch.9 を 🟡 → 「① ✅ / ② frontier」に更新
    - **ParallelGaussian 多次元 false-statement defect 修正** — 電力制約集合が Bochner `∑ᵢ ∫(xᵢ)²∂p ≤ P` で非可積分入力 (Cauchy 等) が `integral_undef→0` で紛れ込み converse を偽命題化。AWGN と同型の lintegral pivot (`parallelGaussianPowerConstraintSet` + bridge) で修正、3 file 8 site 全置換、独立監査 OK (3 decl `@audit:ok`)
    - **load-bearing wrapper `mutualInfoOfChannel_gaussianInput_closed_form` retire** — base `AWGN.lean` の `h_bridge`-form load-bearing wrapper を削除、唯一の genuine consumer (`AWGNMIBridge.awgn_mi_gaussian_closed_form_of_primitives`、bridge を primitives から genuine 構築済) に log 代数を inline。後継 `_closed_form'` も併存。sorry 化は genuine 証明上の fake wall になるため**不可**、削除が正しい retirement
    - **③ scope-out 決定** — operational 符号化定理 (n-letter achievability + converse) の continuous AEP / random coding / sphere packing / 連続 MI chain rule / Fano は (a) 量の壁が大量。原稿パイロット優先方針 (judgment #10) で Nyquist と同じく future work に隔離。Ch.9 は単一文字容量公式の章として publish 可。honest sorry+@residual は marker として保持
    - **次セッション = AWGN 継続 (② Parallel Gaussian water-filling)** — `IsParallelGaussianPerCoordRegularity` の load-bearing hyp 解消。依存先は Ch.8 共有壁 `jointDifferentialEntropyPi_le_sum` (多変量 diffent subadditivity、sorry-routed) + channel↔RV MI decomp。着手は `docs/shannon/multivariate-diffentropy-subadditivity-plan.md` + L-PG1 discharge plan の tractability 評価から
12. **2026-05-29 (続) Ch.8 n-var subadditivity + Ch.9 ② multivariate-mi 壁 2 連続 genuine closure** (orchestrator pattern、複数 wave):
    - **Ch.8 n-var subadditivity genuine** — `jointDifferentialEntropyPi_le_sum` を 0/0 sorryAx 非依存で closure。前回 (2026-05-25 Wave 3) の honest withdrawal は **gap 誤診** (「generic `withDensity_map` Mathlib 不在」を自作不能と扱ったが、`MeasurableEmbedding.map_withDensity_rnDeriv` テンプレで ~13 行 self-build 可能だった)。`withDensity_map_equiv` + `pi_withDensity_fin` 新設、bridge は 2 変数版と同型 structural、独立監査 OK (6 decl `@audit:ok`)。**教訓: Mathlib「壁」(loogle Found 0) は鵜呑みにせず独立再判定 — 「不在 ≠ 証明不能」**
    - **Ch.9 ② `wall:multivariate-mi` genuine closure** — achiever MI per-channel 加法性 `MI(product input × parallel channel) = ∑ per-coord MI` を closure。core = `gaussianProductInput_compProd_parallelGaussianChannel_eq_pi` (compProd-of-`Measure.pi` factorization、`Measure.pi_eq` box 普遍性) + `lintegral_fin_nat_prod_eq_prod` (lintegral n-variate Fubini 自作、`Kernel.pi`/`lintegral_pi` Mathlib 不在を induction で迂回)。これも独立 wall 再検証で「self-buildable (~120-200 行)」と判定 → closure。監査 OK (3 decl `@audit:ok` sorryAx 非依存)
    - **② frontier 縮小** — headline `parallel_gaussian_capacity_formula_minimal` の bundled `h_bridge_per_coord` を per-coord `h_perCoordMI` に分解 (strictly more honest)。残 residual は AWGN single-channel MI finiteness `awgn_mutualInfoOfChannel_ne_top` (`@residual(plan:l-pg1-discharge)`、① の `.toReal` 経路から closeable でない真の residual) + per-coord MI 値 + max_ent の channel↔RV decomp。**② の bottleneck = AWGN single-channel MI bridge family (`IsAwgnOutputGaussian`/`IsAwgnMIDecomp` load-bearing) の closure**
    - **次セッション target** — AWGN single-channel MI bridge family closure (② 残 residual の共通 bottleneck)。finiteness `awgn_mutualInfoOfChannel_ne_top` (llr integrability、~moderate) と per-coord MI 値の genuine 化。`max_ent` の `h_decomp` は新設 factorization machinery で mechanical lift の可能性 (再評価)
13. **2026-05-29 (続々) Ch.9 ② achiever side 完全 genuine + headline honesty 是正** (orchestrator pattern、複数 wave):
    - **AWGN single-channel MI finiteness genuine + false-statement edge 修正** — `awgn_mutualInfoOfChannel_ne_top` を `klDiv_ne_top` (AC + llr integrability、analytic core は `ContChannelMIDecomp.lean` に既存) で closure。独立 wall 再検証で「self-buildable ~75 行」判定 (judgment #12 教訓の適用、loogle Found 0 鵜呑み回避)。**実装中に command-line で発見: 元 signature は `N≠0` 仮定欠落で `N=0`(決定論 channel)+連続入力(`P≠0`) のとき joint が対角グラフ上 = `p.prod q`-null → `klDiv=⊤` で命題が genuinely 偽**。`N≠0` を追加 (regularity precondition、headline は既に `∀i,(Nᵢ:ℝ)≠0` 保持) → residual 完全消滅・genuine。在庫 §E の「N=0 で finite」予測は誤りだった (退化境界の verbatim 確認義務の実例)
    - **headline load-bearing hyp の tier-5 honesty 検出 → 是正** — `parallel_gaussian_capacity_formula_minimal` / `isParallelGaussianPerCoordRegularity_of_pieces` が `@audit:ok` 付きのまま load-bearing open hyp (`h_bdd_global`/`h_multivar_decomp` = 相関入力 max-entropy converse、`h_perCoordMI` = per-coord achiever value) を保持。独立監査で **tier-5 (load-bearing + name laundering) 確定**、旧 `@audit:ok` は誤付与。`h_bdd_global`/`h_multivar_decomp` を drop → `sorry+@residual(wall:multivariate-mi)`、`h_perCoordMI` は **wall ではなく既存 genuine closed form `mutualInfoOfChannel_gaussianInput_closed_form'` を in-body 適用で discharge** (Q=0 退化も `klDiv_self` で genuine)。achiever_mi 完全 genuine 化、残 residual は converse 2 件のみに収斂。**教訓: 「load-bearing hyp を per-coord に分解 = strictly more honest」(judgment #12) は誤り — 分解しても load-bearing なら tier-4/5、honest なのは sorry or genuine closure**
    - **converse self-buildable 判定** — 残 `wall:multivariate-mi` (bddAbove/max_ent) を独立 wall 再検証 → self-buildable (~285-430 行、1-D template の `Fin n` lift、真の Mathlib 壁ではない)。closure plan `docs/shannon/parallel-gaussian-converse-closure-plan.md` (7 Phase、core = `h_decomp` の `Fin n→ℝ` lift)。⚠ 退化ガード: constructor が `P:ℝ` 無制約 → `P<0` で trivially 成立する退化定義悪用 (tier-5) 注意
    - **次セッション target** — converse closure (Phase 0 = `CountableOrCountablyGenerated (Fin n→ℝ)` instance 確認 → Phase 2 `h_decomp` lift core)
14. **2026-05-30 honesty 是正 sweep (orchestrator pattern、複数 wave)** — 2 frontier (Ch.5 Huffman collapse / Ch.17 EPI Stam Step 2) を attack した結果、両者とも proof done 前進ではなく **honesty 是正** に帰結 (frontier が偽 or 真の壁だった)。さらに副産物で EPI family の tier-1 タグ系統的誤付与を発見:
    - **Ch.5 collapse 補題は FALSE statement** — `collapseLabel_huffmanLengthAux` を tie-order 独立 invariant (~150-250 行) で閉じる想定で着手したが、着手前 small-case シミュレーションで **statement 自体が偽**と判明 (a=1,b=6,p=4 の反例、`{a}→{a,b}` の colex 変化が同確率 group の tie-break を反転 → 他 leaf depth が動く)。独立監査が反例を step-by-step 検算 + `Colex.toColex_lt_toColex_iff_max'_mem` で confirm。`@audit:defect(false-statement)`、standalone (伝播ゼロ)。旧判断ログ #3 の「true-but-hard 壁」診断は誤り。**教訓: 撤退ライン設計時に「閉じない」と「偽」を区別する verify step (small-case sim) を必須化** — 偽命題の証明に 200 行費やす前に検出
    - **Ch.17 EPI Stam Step 2 は load-bearing defect → scope-out** — read-only advisor が `entropy_power_inequality_via_body` の `IsStamCauchySchwarzOptimal` 仮説引数 = tier-5 load-bearing defect を発見 (`@audit:ok` の裏)。shared sorry `stam_step2_density_wall` に降格して signature から除去 (tier 5→2)。Rioul「~100 行」見積りは Fisher/score/density 計算 Mathlib 全不在で誤り、scope-out 確定
    - **EPI family @audit:ok 12 件降格** — `#print axioms` sweep で `entropy_power_inequality` (headline) 含む 12 declaration が transitive wall 経由で sorryAx 依存 = proof done でないのに `@audit:ok` 保持と判明、降格。**教訓: file-local `rg sorry` は transitive sorry を捕捉できず、conditional wrapper (sorryAx-free) と headline-routing wrapper (sorryAx 依存) が同型 signature でも proof-done 状態が逆になる。tier-1 タグ付与は `#print axioms` 必須**。load-bearing hyp → shared sorry migration では rewrite 後 wrapper の `@audit:ok` 繰越が defect を温存する経路 (migration brief に「rewrite 後 `#print axioms` 再判定」を入れる)
    - **stale claim 訂正** — roadmap「legacy migration 32 件」は実際 0 件 (paren-pattern 確認)、「EqualizingPerm 4 件 retro-tag」は declaration 削除済で対象外、と verbatim 確認で訂正
    - **次セッション target** — Ch.5 は `MergedHuffmanAuxIdentHypothesis` discharge を leaf-merge / length-multiset reduction へ pivot する新規設計 (per-symbol collapse は dead-end 確定)。Ch.17 は `EPIStamStep3Body` の `IsStamTotalExpectation` load-bearing path を `stam_step2_density_wall` へ統合 (wall 集約) が候補
