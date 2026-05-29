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
| 5 | Data Compression | 🟡 | ShannonCode / Kraft / McMillan ✅、Arithmetic SFE ✅ (prefix / UD)、Huffman weak `huffmanLength_kraft_*` ✅ | T1-A' 2-hyp vertical reduction、T1-A'' Huffman 強形 `huffmanLength_optimal_modulo_aux_ident` (card-2 mergedMeasure redesign 進行中)、DEFECT: `EqualizingPerm*Hypothesis` 4 件 retro-tag 必要 |
| 6 | Gambling | ✖ scope-out | — | — |
| 7 | Channel Capacity | ✅ | `shannon_noisy_..._general_full`, `_feedback_complete`, `strong_converse_singleShot` (Verdú-Han 単発) | strong converse asymptotic (`Pe → 1`, R > C) は deferred plan; Draft `ConverseGeneralComplete` 2 sorry は `_memoryless_pure` で置換可 |
| 8 | Differential Entropy | ✅ (1-var) / ✅ (n-var subadd) | `differentialEntropy_gaussianReal`, `_le_gaussian_of_variance_le`, KLDivContinuous, **n-var subadditivity `jointDifferentialEntropyPi_le_sum` genuine ✅** (2026-05-29、0/0 sorryAx 非依存、監査 OK。`withDensity_map` helper + `pi_withDensity_fin` を self-build、前回 withdrawal は誤診) | — |
| 9 | Gaussian Channel | 🟢 (① ✅ / ② genuine ✅ achiever+converse、headline sorryAx-free) | **① 単一文字情報容量 `awgn_capacity_closed_form_genuine` = (1/2)log(1+P/N) genuine ✅** (0/0、sorryAx 非依存、監査 OK) + hypothesis-free MI 後継 ✅ + ParallelGaussian 電力制約 lintegral pivot ✅ + F-1 / L-PG0 / L-WF1/WF2 discharge。**② 完全 genuine ✅ (2026-05-29)**: achiever (judgment #13) に加え **converse も closure**。最後の residual #5 `parallelOutput_joint_logDensity_integrable` (旧 `@residual(wall:multivariate-mi)`) は **3 者独立再裁定 (inventory + proof-pivot-advisor + honesty-auditor) で self-buildable と確定 → `plan:...-5-closure` reclassify → 多変量 mixture density lift で genuine closure** (def + withDensity 等式 + 上界 + 座標箱 Chebyshev + Gaussian tail 座標積下界 + quadratic 包絡 + `Integrable.mono'` 締め、全 `@audit:ok`、n=0 退化 honest)。`#print axioms parallel_gaussian_capacity_formula_minimal` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free)。教訓: loogle 0 件は壁の必要条件であって十分条件でない (`feedback_independent_wall_recheck`) | **② Parallel Gaussian water-filling 完了 ✅** (achiever + converse + headline すべて genuine、sorryAx-free)。**③ operational 符号化定理は scope-out (judgment #11)**。Shannon-Hartley Nyquist も scope-out |
| 10 | Rate Distortion | ✅ (pmf-form scope) | `rate_distortion_achievability` (Shannon), `rate_distortion_converse_single_shot/_specified`, `rateDistortionFunction_convexOn_pmf` | — (measure-form Draft は **scope-out**) |
| 11 | Statistics | 🟢 (scope 内) | Stein / StrongStein / Sanov / SanovLDP / SanovLDPEquality / Pinsker (+sharp) / Csiszar / CondMethodOfTypes ✅、Chernoff **achievability** `chernoff_lemma_achievability` ✅、Hoeffding sandwich Tendsto + tradeoff exp ✅、Cramér LC2 discharge ext ✅ | `hoeffding_tradeoff_with_hypothesis` tier-4 marker retro-tag。Chernoff converse / Hoeffding interior / Cramér Phase C は **scope-out** (C&T 自身が `≐` heuristic で textbook rigor 達成) |
| 12 | Maximum Entropy | ✅ | `entropy_le_log_card`, `entropy_eq_log_card_iff`, `entropy_le_gibbs_of_constraints`, `expFamily_maximizes_entropy_of_KKT` | — |
| 13 | Universal Coding | 🟢 (scope 内) | Arithmetic ✅ (expected_length_bounds / prefix_free / unique_decodable)、LZ78 M1 `lz78_converse_with_ud_object` ✅ (UD-object 定長 + McMillan 期待値 converse)、headline `lz78_two_sided_optimality_distinct_aseventual` (2 satisfiable load-bearing hyp) | LZ78 M3 (variable-depth tree AEP) / M4 (Barron a.s. lift) は **scope-out** (research-level upstream)。旧 FALSE per-block `IsLZ78ZivCombinatorialCore` 撤回済、3 件 `@residual(defect:false-hypothesis)` は successor plan 付き |
| 14 | Kolmogorov | ✖ scope-out | — | — |
| 15 | Network IT (DSC mini-chapter) | 🟡 | Slepian-Wolf 完全 ✅ (achievability corner + 4 converse、0/0/0)、Wyner-Ziv convexity body ✅ (4 file 0/0/0、main から独立)、judgment #3 de-circularization は散文 note で記録 | Slepian-Wolf Full Rate Region Phase E error bound 完成 (Phase D ✅)、judgment #3 「circular 7 本修復」の `@audit:closed-by-successor` 機械可読化。MAC / BC / Relay / Wyner-Ziv main は **scope-out** |
| 16 | Portfolio | ✖ scope-out | — | — |
| 17 | Inequalities | 🟢 (scope 内) / 🟡 | Han / HanD / Shearer / LoomisWhitney / BrascampLieb / Polymatroid / Pinsker (+sharp) / Hypercube / StamGaussianBound / HeatFlowPath ✅、Stam Step 1 honest discharge ✅、Fisher V2 + de Bruijn 0 body sorry (IBP 1 honest wall)、`entropy_power_inequality` + saturation + log/exp form など 9 件 @audit:ok 昇格 (`epi-stam-fisher-epi` 統合 sweep `2026-05-27` Phase V closure) ✅ | `entropy_power_inequality_gaussian_saturation` → **リネーム延期** `entropyPower_gaussian_additivity` (consumer 23+ occurrence、Ch.17 frontier sweep 別 plan で実施); CT 17.9 Minkowski determinant inequality **新規 ✅ promote 候補** (Gaussian additivity から直接); 一般 EPI / `IsStamToEPIBridge` load-bearing は sorry+@residual に移行; **Cluster C declaration の Tier 3→2 移行完了** (2026-05-28、3 並列 + honesty audit OK、`epi-stam-cluster-c-sorry-migration-plan`): pipeline wrapper 群が `stamToEPIBridge_holds` 委任で load-bearing predicate を解消、active 壁 sorry は `wall:debruijn-integration` (`FisherInfoV2DeBruijn`: `debruijnIdentityV2_holds` + `debruijnIntegrationIdentity_holds`) + `plan:epi-stam-to-conclusion-plan` / `epi-stam-to-conclusion-phaseA-plan` (Stam→EPI bridge / scaling `stamToEPIScaling_holds` / noise `stamScalingNoise_exists`) に局所化。新規 wall file 0 / 新規 wall name 0。EPI 一般版 / BM body / Fisher legacy 6 件は **scope-out** |

**規模見積**: scope-out 拡張により残 ~22k 行 Draft + ~250 residual を解放、scope 内 frontier は数百 sorry オーダーに縮小。

## 「Mathlib 壁」5 分類 (scope 内 frontier に残る型)

- **(a) 量の壁** (低、未構築): well-understood、Mathlib に補題不在で一から数百行。Slepian-Wolf Phase E error bound (Ch.15)。(Ch.9 AWGN operational 符号化定理の continuous AEP / sphere packing も本型だったが judgment #11 で scope-out)
- **(b) 解析の壁** (中〜高): 計算体系自体を建てる型。EPI Stam Step 2 (Ch.17) — Rioul 2011 §II-C より score-cond-mean identity + total variance decomposition で ~100 行 density-level computation (従来 ~300 行 PR 級見積りより小)、再見積もり後 scope 内に戻す余地あり
- **(c) 数学的深さ** (高、真の壁): Nyquist 2W-DOF (Ch.9、scope-out 確定)
- **(d) 実は選択** (de-circularize 済): "ROI 無し" の婉曲表現で「壁」と呼ばれていたもの、現在は honest 開示のみ
- **(e) scaffolding-was-false** (中〜大): 既存縮約 predicate / 定義が偽 / 循環 / 不健全で discharge 不能、genuine 構成を一から組み直す。Huffman mergedMeasure card-2 redesign (Ch.5)

## frontier (scope 内 closure 必要)

- **Ch.5 Huffman 強形**: `mergedMeasure` card-2 redesign 進行中、honest frontier `huffmanLength_optimal_modulo_aux_ident` まで精密 localize 済
- **Ch.8 n-var DiffEnt subadditivity**: genuine ✅ (2026-05-29 closure、もはや壁ではない)
- **Ch.9 ② Parallel Gaussian water-filling**: **完了 ✅ (2026-05-29)** — achiever + converse + headline すべて genuine、`parallel_gaussian_capacity_formula_minimal` sorryAx-free。最後の residual #5 joint log-density integrability を多変量 mixture density lift で genuine closure (3 者独立再裁定で wall→plan reclassify 後)。③ operational 符号化定理は scope-out (judgment #11)。**もはや scope 内 frontier ではない**
- **Ch.15 Slepian-Wolf Phase E**: Full Rate Region 4-way error decomposition は Phase D ✅、Phase E 確率上界収束のみ残
- **Ch.17 EPI Stam Step 2 再見積もり**: Rioul 2011 経路で ~100 行 density-level computation の見込み、keep するか scope-out 確定するか要判断
- **Ch.17 legacy migration**: 32 件 `@audit:suspect` の sorry-based 移行 (mechanical)
- **未追跡 marker retro-tag**: Ch.5 `EqualizingPerm*Hypothesis` 4 件 / Ch.9 `IsTwoWDegreesOfFreedom` / Ch.11 `hoeffding_tradeoff_with_hypothesis` / Ch.15 judgment #3 circular 7 本 / Ch.17 `IsStamToEPIBridge` 移行

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
