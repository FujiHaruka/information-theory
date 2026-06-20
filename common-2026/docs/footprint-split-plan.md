# footprint split plan — モノリシック証明を named helper へ分解する純リファクタ ✂️

**Status**: Phase 0 DONE / **Phase 1 (優先1 = >250 tier) 全 25 本処理 DONE** (2026-06-14) /
**DoD 緩和済** (現実的版) / **Parent**: なし (standalone) /
**関連**: 実測 SoT [`mathlib-conventions-gap.md`](mathlib-conventions-gap.md) §3.A.1 / §4.1 ・
命名 [`rules/naming.md`](rules/naming.md) ・docstring [`rules/docstrings.md`](rules/docstrings.md) ・
Lean style [`rules/lean-style.md`](rules/lean-style.md) ・honesty タグ [`audit/audit-tags.md`](audit/audit-tags.md)

## 進捗

- [x] Phase 0 — 測定 + pilot 較正 ✅ (`floorMatrix_dist_le`、commit `d2fb1fa`)
- [x] Phase 1 — 優先1 (>250 行 tier) を named helper へ分解 ✅ **全 25 本処理済** (clean 割れブロックは全抽出、>250 残留=不可分 core は現実的 DoD で許容)
- [ ] Phase 2 — 優先2 (>150 tier) を機会主義的に分解 🔨 進行中 (Wave 1-17、>150: 91→49)
- [ ] Phase 3 — 最終再実測 + 裾縮小確認 📋
- [ ] Phase 4 — **option C (>250 spine 攻略)** 🔨 (2026-06-14 着手。**3 本クリア >250: 15→12、両機構検証済**。残 12 本。下記 Phase 4 節)

## Context

Mathlib 最大の暗黙規律は **1 宣言の footprint を小さく保ち、長くなったら名前付き補題に割る** こと
([`mathlib-conventions-gap.md`](mathlib-conventions-gap.md) §1.2 / §3.A.1)。footprint =
宣言の `theorem`/`lemma`/`def` 行から次の top-level 宣言までの行数。Mathlib は IT+Probability で
**中央値 7 / 最大 115 / 150 超ゼロ**。本プロジェクトは粒度が大きく乖離している。

**分布スナップショット (再実測コマンドは [`mathlib-conventions-gap.md`](mathlib-conventions-gap.md)、母集団は全宣言)** —
Phase 1 前 (commit `7771687`) → Phase 1 完了後 (`afdb482`):

| 指標 | Phase 1 前 | Phase 1 後 |
|---|---|---|
| 中央値 | 18 | 19 (抽出 helper が分布を上へ引く、知見通り) |
| p99 | 238 | 213 |
| 最大 | 907 | 677 (Mass の不可分 core) |
| **> 250 行** | **25** | **15** (−10、本セッション clean 割れ分) |
| > 150 行 | 97 | 91 |
| > 115 行 | 159 | 159 (= 優先2、抽出 helper 流入で件数は据置) |

> 250 残留 15 本は全て不可分 assembly core (10+ `set` ローカル結合 / `private` 参照 / sorry 持ち
spine)。option C (private de-private 化 + spine 再設計) なしには純抽出で消せない (DoD 緩和の根拠)。

このパスは **モノリシック証明の自己完結 `have` ブロックを top-level named helper 補題に切り出す**
だけの **純リファクタ**: 証明内容不変・対象 signature 不変・axiom 不変・sorry 数不変。proof done
(0 sorry / 0 residual) とは独立に進められる = 壁を一切触らない。

## 知見 — 純 `have` 抽出は >250 tier を clear しない (2026-06-14 実測)

**最大の 12 本をリファクタした後の裾の動き** (`python3` footprint 再実測):

| 指標 | リファクタ前 | 12 本後 |
|---|---|---|
| **> 250 行 件数** | 25 | **24** (−1 のみ) |
| 最大 footprint | 907 | **677** (−25%) |
| 中央値 | 18 | **19** (微増) |

**結論: 純 `have` 抽出は >250 の裾を消せない。** 根本原因 — 各証明に残る組立核 (300–680 行) は
抽出で不可分: (a) 10+ の `set` ローカルを束ねており切り出すと項が unify しない、(b) public helper に
漏らせない `private` 定義を参照する。閾値近傍 (~250–300、pilot 253 の類) の証明のみが ≤250 へ clean に
割れる。**中央値が微増したのは、抽出した helper が母集団の中央値より大きく分布を上へ引くため。**

抽出の **真の価値 = (i) 再利用可能な public helper の創出 (12 本で計 42 本) + (ii) 最大 footprint の
~20–30% 縮小** であって、**裾の消去ではない**。>250 の完全 clear には option C (`private` 定義の
public 化 + 組立 spine の再設計) が要り、本純リファクタパスの外 (DoD 緩和の根拠、下記)。

## Approach

**全体の形**: 「巨大証明を読む → 自己完結する `have` ブロックを抽出単位として特定 → top-level の
public・記述的命名・docstring なしの補題へ切り出し → 元証明はその補題を `exact`/`apply` で呼ぶ →
axiom 不変を `#print axioms` で確認」を、ファイル単位で 1 宣言ずつ適用する。

抽出は **Skeleton-driven** に行う: 先に helper の signature を `:= by sorry` で立てて型が通ることを
確認 → 中身を元証明の `have` ブロックから移植 → 元証明側を呼出に置換 → orphan `have` を削除。
中身を 1 つ移すごとに `lake env lean <file>` でグリーンを確認する (一括書換しない)。

### Hard rule — 抽出 helper 自身が新たな >250 モノリスになってはならない (anti-relabeling)

**抽出した helper の証明が大きい (>~150 行) 場合は、その helper をさらに小さい named helper へ
再分解する** (= 再帰)。1 つのモノリスを別名のモノリスへ **付け替えるだけ (relabel)** にしてはならない。
ゴールは **多数の小さい再利用可能宣言** であって、1 つの巨大 `have` を 1 つの巨大 `lemma` に
リネームすることではない。

戒めの実例: `isRescaledPathRegular_of_methodX` (#7) は body を 590→25 行に縮めたが、抽出先
`rescaledPath_indep_regular` が **498 行**になった = relabel に陥った。これは Phase 1 残作業
(下表) で **anti-relabeling ルールに従い再分解**する。抽出時は helper の footprint を都度測り、
>150 なら確定前にさらに割る。

### 抽出の単位 — どの `have` を切るか

- **数学 (measure 非依存) を優先抽出する** (pilot gotcha 3)。pure な `(n:ℕ)(q s ε:ℝ)` 補題で
  measure 引数を取らないものが最も clean かつ再利用性が高い。`μ` を引数に取る抽象化より、
  `μ` 依存を結論に持たない算術核を切るほうが良い。
- **自己完結 (call site のローカルへの依存が浅い) ブロック**を選ぶ。`set ... with hX` のローカルを
  多数参照するブロックは抽出コストが高い。
- **`private` 定数を参照するブロックは切らない** (pilot gotcha 5): public helper の statement に
  private symbol が漏れる。そういうブロックは inline のまま残す。

### Pilot で確定した 5 つの gotcha (ロールアウト必読)

pilot = `ConditionalMethodOfTypes/Core.lean` の `floorMatrix_dist_le` (commit `d2fb1fa`):
public・記述的命名・docstring なしの helper 3 本を抽出、body 241→97 行、
`#print axioms` は `[propext, Classical.choice, Quot.sound]` で抽出前後一致、`lake env lean` clean。

1. **`set ... with hX_def` のローカルは抽出補題の項と自動 unify しない**。call site で
   `rw [hX_def]` を入れて unfold してから `exact <helper>` する必要がある。
2. **auto-param で自動 discharge されていた副条件 (`finiteness`/`positivity`/`measurability`) が
   抽象化で壊れる**。helper の signature に対応する regularity instance/hypothesis を明示追加して
   直す (例: `[IsFiniteMeasure ν]`)。
3. **数学を抽象化せよ** (上の「抽出の単位」)。`μ` でなく純算術を切るのが最も clean。
4. **対象ファイルが `set_option linter.unusedVariables false` を持つ場合、抽出後に dead になった
   `have` が linter で検出されない**。`rg` で usage を grep してから orphan `have` を手で削除する
   (linter に頼らない)。
5. **`private` 定数を参照するブロックは切らない** (上記)。

### Mathlib 流 helper のルール (§4.1 / [`rules/naming.md`](rules/naming.md) / [`rules/docstrings.md`](rules/docstrings.md))

- **public で残す** (§1.4: 小補題 = 再利用 API。Mathlib の private は 1.3%、本プロジェクトは
  逆方向の 15.4%)。`private` 化しない。
- **記述的命名** ([`rules/naming.md`](rules/naming.md): 名前が結論の形を語る、`_of_` で仮説後置、
  `_le_`/`_eq_`/`_iff_`)。staging 語彙 (`Step`/`Bridge`/`Partial`/`Full`/`Discharge`) は使わない。
- **新規 `_aux` 補題を作らない** (名前で事実を語らせる)。機械連番 `aux1`/`aux2` は禁止。
- **docstring を付けない** (§1.4: 補助補題は裸。名前と module doc が意味を担う)。新規 helper に
  docstring を書かない (docstring-tidyup パスの方向と一致)。

### オーケストレーション

- **並列度 ≤ 2** の disjoint-file ownership。1 ファイル = 1 エージェントが所有する
  (純リファクタゆえ実装エージェントだが、衝突回避のため worktree isolation + boilerplate を付す
  — CLAUDE.md「Parallel orchestration」)。**マルチターゲットのファイルは 1 エージェントが
  全ターゲットを所有**する (下の Wave 表で注記)。
- **オーケストレータが検証 + commit** する。各ファイル完了後に `lake env lean` clean +
  `#print axioms` 不変 + signature byte-identical をオーケストレータが確認してから commit する
  (Hard invariants 全 4 点)。

## Hard invariants (違反 = DEFECT)

純リファクタの定義そのもの。1 つでも破れば抽出は不正。

1. **対象 signature が byte-identical**: 切り出し対象の `theorem`/`lemma`/`def` 行 (名前・引数・
   型・instance bracket) はリファクタ前後で 1 byte も変わらない。consumer から見た API 不変。
2. **`#print axioms <target>` 不変**: 抽出前の axiom 集合 (pilot は
   `[propext, Classical.choice, Quot.sound]`) と抽出後が完全一致。`sorryAx` が増えない/減らない。
3. **sorry 数不変 + honesty タグ verbatim 保存**: ファイル内 `sorry` 総数不変。`@residual(...)` /
   `@audit:*` タグはタグ文字列ごと verbatim 保存。**sorry を含む `have` を抽出する場合は、helper が
   その `@residual(...)` を verbatim relocate して担う** (タグが宙に浮かない)。最も安全なのは
   sorry ブロックを inline のまま残すこと (下の `ConvEntropyDensity` 注記)。
4. **compile clean**: 各ファイル `lake env lean <file>` が 0 error (sorry warning は元から
   ある分のみ許容)。最終 Phase で full `lake build` green。

## Phase 1 — 優先1 (>250 行 tier) を named helper へ分解 📋

**proof-log: no** (純リファクタ。判断の余地が小さく、proof-log 不要。axiom 確認結果は commit
message に残す)。

**Wave 編成はファイル単位の ownership で組む** (1 ファイル 1 エージェント、並列 ≤ 2)。
file:line (footprint) sorry-count は §4.1 入力データを verbatim 使用 (2026-06-14)。

### マルチターゲット・ファイル (1 エージェントが全ターゲットを所有)

| ファイル | ターゲット (footprint) | 状態 |
|---|---|---|
| `AWGN/AchievabilityDischarge.lean` | `awgn_random_coding_union_bound` (672→536) + `isAwgnTypicalityHypothesis` (597→432) — 計 2 本 | **DONE** |
| `EPI/Case1/SmoothingLimit.lean` | `entropy_power_inequality_of_density_explicit` (464→338) + `entropyPower_smoothed_epi_perT` (365→336) + `entropy_power_add_ge_of_finite_variance` (310→264) — 計 3 本 | **DONE** |

同一ファイル内の複数ターゲットは編集領域が重なるため **必ず同一エージェント**が直列処理する
(`.git/index.lock` 競合 + 行番号ドリフト回避)。SmoothingLimit の 3 本は全て 264–338 で **>250 残留**
(現実的 DoD で許容、下記)。

### 優先1 ターゲット一覧 (25 本 + pilot)

**前セッション DONE (12 本 + pilot 1 本)** — 検証済: signature byte-identical / `#print axioms` 不変 /
タグ保存 / compile clean。footprint は before→after。**DONE でも >250 残留分は現実的 DoD で許容**。

| file:line (footprint before→after) | 対象 | 備考 |
|---|---|---|
| `ConditionalMethodOfTypes/Core.lean` (253→122) | `floorMatrix_dist_le` | pilot `d2fb1fa` (>250 clear、helper 3 本) |
| `ConditionalMethodOfTypes/Mass.lean` (907→677) | `conditional_KL_concentration_ge` | 最大。**>250 残留** (組立核不可分) |
| `RateDistortion/.../FailureTendsto.lean` (798→653) | `codebookAvgFailureStrong_tendsto_zero` | **>250 残留** |
| `AWGN/AchievabilityDischarge.lean` (672→536) | `awgn_random_coding_union_bound` | マルチ。**>250 残留** |
| `AWGN/AchievabilityDischarge.lean` (597→432) | `isAwgnTypicalityHypothesis` | マルチ。**>250 残留** |
| `ChannelCoding/.../OuterN.lean` (608→466) | `exists_N_for_smooth_achievability_uniform` | **>250 残留** |
| `EPI/Case1/SmoothingLimit.lean` (464→338) | `entropy_power_inequality_of_density_explicit` | マルチ。**>250 残留** |
| `EPI/Case1/SmoothingLimit.lean` (365→336) | `entropyPower_smoothed_epi_perT` | マルチ。**>250 残留** |
| `EPI/Case1/SmoothingLimit.lean` (310→264) | `entropy_power_add_ge_of_finite_variance` | マルチ。**>250 残留** |
| `AWGN/Walls.lean` (485→323) | `continuousAepGaussian_holds` | **>250 残留** |
| `EPI/Case1/RatioLimit/PathRegular.lean` (590→25) | `isRescaledPathRegular_of_methodX` | body 縮小 + helper `rescaledPath_indep_regular` を 498→**122** へ 14 小 helper 再帰分解済 (`b2887fa`、anti-relabel 実証)。file max 122 で >250 clear |
| `SlepianWolf/FullRateRegion/PairBound.lean` (420→386) | `swErrorProb_total_expectation_le` | **>250 残留** |

**本セッション完了分 (13 本、commit `89f3331`..`afdb482`、全 Hard invariant 機械検証済)** —
8 本が ≤250 へ clear、5 本は不可分 core で >250 残留 (DoD 許容)。計 ~70 本の再利用 public helper 抽出。

| 対象 (footprint before→after) | 結果 | helper |
|---|---|---|
| `Boundary` `two_sum_projection_eq` 355→**50** | ✅ clear | 7 (anti-relabel: per-fibre core を 123 で止め再分解) |
| `GeneralDensity` `isBlachmanConvReady_convDensityAdd_gaussian` 346→**54** | ✅ clear | 11 (import cycle 回避でローカル抽出) |
| `GaussianWitness` `isBlachmanConvReady_gaussianPDFReal` 390→**78** | ✅ clear | 6 (int_prod dedup) |
| `SupplyTwoTime` `isBlachmanConvReady_convDensityAdd_gaussian_asym` 364→**92** | ✅ clear | 11 |
| `Assembly` `entropyPower_add_ge_case1_of_methodX` 253→**146** | ✅ clear | 2 (閾値近傍 over-shoot) |
| `Construction` `integrable_negPart_negMulLog_map_condTrunc_sum` 250→205 | ✅ clear | 3 |
| `SmoothInstantiation` `channel_coding_achievability_smooth_at_N_le` 256→218 | ✅ clear | 4 |
| `RandomCodebook` `random_codebook_E1_swap` 260→230 | ✅ clear | 4 (+E2/marginal dedup) |
| `KLFatouLSC` `negMulLog_convDensity_limsup_le` 374→353 | >250 残留 | 2 |
| `TwoSidedRatio` `integral_MRatioLowerZ_le_one` 382→350 | >250 残留 | 3 (+Liminf 重複2補題 dedup) |
| `ConvEntropyDensity` `negMulLog_convDensity_entropy_ge_density` 608→337 | >250 残留 | dead helper 4 本配線+~270行 dedup |
| `DensityForm` `entropy_power_inequality_of_density` 429→298 | >250 残留 | 3 |
| `Mono` `differentialEntropyExt_mono_add_of_integrable` 330→289 | >250 残留 | 6 |

注: #4 `ConvEntropyDensity` は plan の「sorry=1」想定が **誤り** だった (実際は `@audit:ok` の
sorryAx-free)。コード側の `@audit:ok`/`@residual`/sorry 数は全 13 本で機械検証して verbatim 保存
(Assembly は既存 sorry+@residual を含め 1→1 保存)。

## Phase 2 — 優先2 (>150 tier) を機会主義的に分解 🔨 進行中 (Wave 1-16 完了)

**proof-log: no**。

**状態 (2026-06-20)**: Wave 1-17 完了。**>150 tier: 91 → 49 (−42)、>250 は 0 維持** (official
decl-to-next-decl metric で再実測)。各 Wave は全 Hard invariants (対象 sig byte-identical /
`#print axioms` = `[propext, Classical.choice, Quot.sound]` 不変 / sorry 数不変 / `lake env lean`
clean + 該当 build green) を orchestrator が独立機械検証済。**新規 sorry/residual なし (純リファクタ)
ゆえ honesty audit 不要**。

着手ルール: 優先1 と同じ抽出ルール・gotcha・Mathlib 流 helper ルール・Hard invariants を適用。
本 Phase は個別列挙でなく着手時に再実測してファイル単位で拾う。49–115 行 tier は機会主義のみ
(専用 Wave を組まず、開いたファイルにあれば拾う程度)。

### 完了 Wave (詳細は commit、ここは 1 行要約)

- **Wave 1** (`b2a9bf4`): `Huffman/Optimality.lean` 3 本 (`huffmanLength_optimal_aux` 188→66 /
  `expectedLength_merged_cost_bridge` 174→137 / `expectedLength_bridge_R` 163→27) +
  `Sanov/LDPEquality.lean` 3 本 (`typeClassByCount_card_ge` 211→140 /
  `sanov_ldp_lower_bound_pointwise` 174→78 / `sanov_ldp_equality` 152→88)。計 12 public helper、全 <150。
- **Wave 2** (`4cd9578`): `ChannelCoding/Achievability/RandomCodebook.lean`
  (`codebook_marginal_one` 197→149 clear / `codebook_marginal_two` 154→135 clear /
  `random_codebook_average_le` 235→176 partial=不可分 Code-API spine / `E1_swap`230・`E2_swap`215 は
  floor で inline 維持) + `SlepianWolf/FullRateRegion/{PairBound,AliasBound}.lean` 4 本
  (`swError_EXY_strict_expectation_le` 235→body144 / `slepian_wolf_full_rate_region_achievability`
  213→139 / `swError_EX_expectation_le` 187→131 / `conditionalTypicalSliceY_card_le` 176→124)。
  共有 Fubini-lift helper 6 本を下位 `AliasBound` へ集約し `PairBound` が import 経由共有
  (cross-file、cycle なし、full build green 3471)。
- **Wave 3** (BackwardIntegral / Object):
  `Probability/TwoSidedExtension/BackwardIntegral.lean` 2 本
  (`integrable_indicator_mul_negLog_of_condExp` 217→body148 /
  `joint_pastBlock_coord0_eq` 201→23) + `EPI/Case1/TwoTime/Object.lean` 2 本
  (`twoTimeLogRatioGap_tendsto_zero_atTop` 224→98 /
  `entropyPower_add_ge_case1_of_regular_twotime` 201→143)。計 20 helper。
- **Wave 4** (`13aab27`): `Shannon/HypercubeEdge/BoundarySharp.lean` `entropy_projMap_eq` 229→143
  (helper 1 本 `fibre_oneortwo_of_mem_projectionExcept` 85、純組合せ) +
  `Shannon/ConditionalMethodOfTypes/Core.lean` `conditionalTypeClass_card_eq_prod_typeClass` 212→74
  (helper 3 本 public: `conditionalTypeClass_joint_iff_slice` 39 / `filter_card_comp_equiv_symm_eq` 13 /
  `sliceSubtype_equiv_typeClassByCount` 31)。計 4 helper 全 <150。
- **Wave 5** (`6e88c90`): `Shannon/Hoeffding/TradeoffExp.lean` entry_point `hoeffding_tradeoff_exp`
  198→114 (helper 3 本 measure 引数化: `E_r_union_meas_pos_eventually` 39 /
  `E_r_union_rate_isBoundedUnder_above` 24 / `E_r_union_rate_isBoundedUnder_below` 88) +
  `Shannon/SlepianWolf/ConditionalTypicalSlice.lean` entry_point `conditionalTypicalSlice_card_le`
  199→144 (helper 2 本: `jointRV_jointSequence_proj_measureReal_eq` 34 /
  `le_exp_sub_of_mul_exp_neg_le_exp_neg` 10)。計 5 helper 全 <150。
- **Wave 6** (`7cc5b52`/`0172774`/`c18ff0a`): `Shannon/DifferentialEntropy.lean` entry
  `klDiv_gaussianReal_gaussianReal_eq` 204→93 (Gaussian モーメント系 public helper 6 本、全 <30:
  `gaussianReal_variance_eq` / `gaussianReal_integrable_sq` / `gaussianReal_integrable_sq_sub` /
  `gaussianReal_integral_sq_sub_eq` (mean-shift) / `gaussianReal_integrable_log_gaussianPDFReal` /
  `gaussianReal_integral_log_gaussianPDFReal_eq`) + `Shannon/Pinsker/Basic.lean` entry
  `tvNorm_le_sqrt_klDiv` 194→143 (Hellinger²/CS pure-real public helper 2 本: `finset_cs_sqrt_sq` ~32 /
  `sum_sqrt_add_sq_le_four` ~24。per-element Bretagnolle-Huber は measure 結合が深く inline 維持 partial)。
  計 8 helper 全 <150。>150 tier 73→71。
- **Wave 7** (`9130241`/`893aa89`): `EPI/Unconditional/TruncationLimit/Mono.lean` entry
  `differentialEntropyExt_mono_add_truncW` 205→124 (public helper 2 本:
  `truncW_indepFun_of_indepFun` ~34 = 条件付けが W⊥V 保存・再利用可 /
  `truncW_map_negMulLog_negPart_lintegral_ne_top` ~65 = truncated 密度負部 lintegral 有限性) +
  `EPI/InfiniteVariance/Capstone.lean` entry `integrable_negPart_negMulLog_map_sum` 231→137
  (convolution-Jensen public helper 3 本: `lintegral_conv_kernel_eq` 24 = translation-invariant
  Tonelli / `integrable_conv_kernel` 16 / `conv_jensen_bound` 58 = μX-smul + ConvexOn.map_integral_le)。
  計 5 helper 全 <150。>150 tier 71→69。
- **Wave 8** (`1a987b4`/`120490d`): `FisherInfo/V2DeBruijnAssembly/Assembly.lean` entry
  `debruijnIdentityV2_holds_assembled_chain_hdiff` 231→126 (public helper 1 本:
  `debruijnIdentityV2_chain_hdiff_pathDeriv` ~138 = heatFlow_density σ-derivative domination ブロック切出) +
  `Shannon/RateDistortion/AchievabilityPhaseEStrong.lean` entry_point
  `jointStronglyTypicalSet_indep_prob_ge` 227→149 (public helper 3 本:
  card_eq / perPair / sum_marginals 系)。計 4 helper 全 <150。>150 tier 69→67。
- **Wave 9** (`4f343d6`/`604283e`): `Probability/TwoSidedExtension/Core.lean` `@[entry_point]`
  `ergodic_shiftZ` 223→94 (public helper 1 本:
  `exists_posSigma_ae_eq_of_shiftZ_invariant` ~115 = cylinder 近似 + Borel-Cantelli で
  posSigma-可測代表元を作る存在証明ブロック切出、`omit` で section 変数から切離) +
  `EPI/Unconditional/TruncationLimit/Limit.lean`
  `differentialEntropyExt_top_of_indep_add_unconditional` 202→130 (public helper 1 本:
  `differentialEntropyExt_truncW_add_le_two_mul_Aν` ~76 = per-n Gibbs + 測度 domination の hub
  ブロック切出、`[IsProbabilityMeasure ν]` を追加引数として明示)。計 2 helper 全 <150。>150 tier 67→65。
- **Wave 10** (`00bb7ee`/`b04062e`): `EPI/G2/KLFatouLSC.lean` `negMulLog_convDensity_limsup_le`
  228→120 (public helper 2 本: `negMulLog_klFatou_bridge_identities` = density-form bridge + cross/entropy
  同定の 2 bridge identity 返却 / `negMulLog_klFatou_entropy_tendsto` = klFun-Fatou squeeze tail で
  `Tendsto h_n (𝓝 L)`。1 本では 174 止まりで 2 本に分割) +
  `FisherInfo/V2DeBruijnPerTime.lean` `heatFlow_density_heat_equation` 208→143 (public helper 1 本:
  `heatFlow_pathDeriv2_eq_integral` ~73 = STEP D spatial-derivative identification ブロック切出)。
  計 3 helper 全 <150。>150 tier 65→63。
- **Wave 11** (`3fcc99e`/`87ca1c7`): `ChannelCoding/ShannonTheoremFullDischarge/OuterN.lean`
  `exists_N_for_smooth_achievability_uniform` 241→146 (private helper 3 本:
  `outerN_variance_bounds` ~52 = μ 構築 + 3 pointwise bound + pmfLogVariance で 3 variance bound /
  `outerN_logSq_bounds` = log² square bound 2 本 / `outerN_smoothMinN_le` =
  channelCodingSmoothMinN ≤ n 算術。dead 化 positivity fact 除去 + コメント圧縮) +
  `EPI/InfiniteVariance/Truncation/Construction.lean`
  `integrable_negPart_negMulLog_map_condTrunc_sum` 211→147 (public helper 2 本:
  `jensen_convDensityAdd_le_section_integral` ~64 = per-z Jensen bound を convDensityAdd ベースに書換 /
  `ae_section_integrable_convKernel` = section integrability 3 本を prod_right_ae 汎用化)。
  計 5 helper 全 <150。>150 tier 63→61。
- **Wave 12** (`637b2c6`/`2802899`): `FisherInfo/V2DeBruijnAssembly/Derivatives.lean`
  `convDensityAdd_negMulLog_integrable` 187→119 (public helper 1 本:
  `convDensityAdd_sq_mul_integrable` = `Integrable (x²·p_t x)` ブロック ~70 行抽出、p_t/g を抽象関数+等式仮説で受ける) +
  `ChannelCoding/ShannonTheoremFullDischarge/SmoothInstantiation.lean`
  `channel_coding_achievability_smooth_at_N_le` 219→128 (public helper 2 本:
  `channelCodingSmooth_avg_bound` = μ-regularity bundle → random_codebook_average_le 結論を直接返す (full/pos/match facts 内部再生成) /
  `channelCodingSmooth_assemble` = E1/E2 bound block + exists_codebook_le_avg pigeonhole 集約)。
  計 3 helper 全 <150。>150 tier 61→59。
- **Wave 13** (`69d1d44`/`db7d0df`): `Shannon/Bridge.lean` (private) `klDiv_joint_prod_marginals_toReal`
  181→148 (public helper 1 本: `integrable_sum_fibre_real_mul_log` = integrability block ~46 行抽出、
  一般 kernel κ/νY/νX で 2 sum-integrability を ∧ 返却) +
  `EPI/Unconditional/TruncationLimit/Mono.lean` `differentialEntropyExt_mono_add_of_integrable`
  183→69 (public helper 1 本: `differentialEntropy_le_of_conv_finite` = Case B finite branch
  = per-fibre translate Gibbs 全体 ~114 行抽出、helper 自身も 141 行で <150)。
  計 2 helper 全 <150。>150 tier 59→57。
- **Wave 14** (`55b3811`/`6c9f7b7`): `EPI/InfiniteVariance/Truncation/Density.lean`
  `convDensity_condTrunc_tendsto` 193→117 (public helper 1 本:
  `condTrunc_marginal_density_tendsto` 84 = per-component pointwise convergence の `hconv_comp`
  ブロックを standalone 化) + `Shannon/Fano/Measure.lean` `fano_inequality_measure_theoretic`
  175→143 (public helper 1 本: `integral_qaryEntropy_le_qaryEntropy_integral` 32 =
  「確率測度上 [0,1]値 integrable g に対し ∫ qaryEntropy(g) ≤ qaryEntropy(∫g)」汎用 Bochner-Jensen 抽象補題)。
  計 2 helper 全 <150。>150 tier 57→55。
- **Wave 15** (`c6412e4`/`a9549ee`): `ChannelCoding/Basic.lean` `jointlyTypicalSet_prob_tendsto_one`
  172→80 (helper 1 本 `measure_inter3_tendsto_one` 75 = 「3 可測事象が各々 μ→1 なら triple
  intersection も →1」汎用 complement-union-bound 抽象補題) +
  `RateDistortion/ConverseNLetter.lean` `rate_distortion_converse_n_letter_singleLetter`
  173→146 (helper 1 本 `blockDistortion_eq_avg_perLetter` 57 = per-letter 歪み平均 = block 期待歪みの
  change-of-variables 恒等式)。計 2 helper 全 <150。>150 tier 55→53、>250 = 0 維持。
- **Wave 16** (`57f4d05`/`f5e1f0e`): `ChannelCoding/ConverseMemorylessPure.lean` (private)
  `isMarkovChain_weakUnion_left_to_conditioner` 188→147 (helper 1 本
  `condDistrib_prodMk_right_ae_eq_comap` 75 = Yo の (Zc,As) 条件付き分布 = Zc 条件付き分布の fst-comap
  という conditional-independence reshape、Markov 前提を直接受ける) +
  `EPI/Stam/SupplyTwoTime.lean` `twoTime_stam_supply` 170→132 (helper 1 本
  `reg_density_t_sum_eq_convDensityAdd` 105 = sum density_t = X/Y density_t の convDensityAdd という
  conv-pin gate、h_reg_X/Y/sum + σ/τ を受け内部で reg_at 構造再構築)。計 2 helper 全 <150。
  >150 tier 53→51、>250 = 0 維持。
- **Wave 17** (`5c3fdd8`/`f37ac78`): `FisherInfo/V2DeBruijnAssembly/Domination.lean`
  `debruijnIdentityV2_holds_assembled_chain_domination` 184→58 (private helper 1 本
  `convDensityAdd_jointMajorant_integrable` 137 = route-II Tonelli 被覆積分可能性ブロック切出) +
  `AEP/Rate.lean` `jointlyTypicalSet_prob_ge_of_rate` 168→146 (helper 1 本
  `badEvt_toReal_le_of_good_bound` 16 = 3 軸対称の per-axis `(μ goodᶜ).toReal ≤ η/3` 導出を 1 本に集約)。
  計 2 helper 全 <150。>150 tier 51→49、>250 = 0 維持。

### 計測ニュアンス (Phase 2 で確立、Wave 4+ でも適用)

- footprint = **宣言行から次の top-level 宣言までの距離** (docstring・空行込み)。proof body 長と乖離する:
  body が 144 行でも **次の宣言の docstring が宣言間に挟まる**と decl-to-next metric は 170 になりうる。
  Wave 2/3 の `swError_EXY_strict` (body144/metric170)・`integrable_indicator...` (body148/metric157) が
  この artifact。**進捗は metric (decl-to-next) で追うが、body <150 を実質達成と見なす**。
- **sorry 計測の落とし穴**: 単純 `grep -c sorry` は **docstring 内の "sorry"/"sorry-free" 文字列**を拾う
  (Object.lean は docstring に 5 箇所、実 sorry tactic は 0)。ターゲット選定で sorry 持ち判定する際は実
  sorry tactic token を確認する (decl span の `grep sorry` は over-count)。

### Wave 18+ への申し送り

- **触らない (option-C 済 floor 残留)**: Mass 249 / union_bound 245 / ConvEntropyDensity 245 等。
- **計測アーティファクト — `convex_fisher_bound` (EPI/Blachman/Density 238) は候補から除外**:
  この theorem の実 body は line 467〜603 の約 137 行で**既に <150**。footprint が 238 に膨れるのは、
  直後に来る `structure IsBlachmanConvReady` (line 631) が footprint 計測スクリプト `footprint_v2.py` の
  `decl_re` (`theorem|lemma|def` のみマッチ、`structure` は非マッチ) に拾われず、次の theorem
  (`isBlachmanConvReady_symm` line 705) までが 1 宣言として測られるため。body を抽出で縮めても
  宣言行 (467) から次 matched decl (705) までの距離は変わらず、measured footprint は下がらない → count-win
  不能。**一般教訓**: `theorem` 直後に `structure`/`instance`/`abbrev` が挟まるケースは同種アーティファクト。
  候補選定時は target の**実 body 末尾**と**次の matched decl** を Read で確認すること。
- **中位 tier 151-157 の single-target disjoint 候補群 (小抽出で <150 到達見込み、ただし margin 薄く
  net 削減を要確認、着手時 Read で実 body 末尾・次 matched decl を確認)**:
  `integrable_indicator_mul_negLog_of_condExp` (BackwardIntegral 157) /
  `csiszar_first_order_condition` (CsiszarProjection 154) /
  `total_length_ge_count_mul_log` (LZ78/ZivCountingBody 154) /
  `birkhoffAverage_pmfLogCondMarkov_tendsto` (SMB/AlgoetCover/Core 154) /
  `birkhoffAverageReal_limsup_comp_T_ae` (BirkhoffErgodic 153) /
  `condEntropy_pi_eq_sum_of_memoryless_strong` (CondEntropyMemoryless 151)。
  互いに別ファイルゆえ disjoint、1 agent 1 file で同時処理可。
- **高 count single-target (orchestrator が Wave 18 でスカウト中)**:
  `channel_coding_achievability` (Main.lean 192、entropy block + setup の 2 seam) /
  `negPart_negMulLog_conv_single_ne_top` (Core.lean 191、hjensen seam だが local set 多数 thread)。
- **後回し寄り (signature 密結合で抽出が重い)**: `entropy_power_inequality_of_density`
  (EPI/DensityForm.lean 172) — signature ~40 行 + lift-space wiring 密結合で、抽出に lift/X'/Y'/ZX/ZY/Z
  多数を thread する必要があり重い。優先度低。
- **後回し候補 (高 count multi-target = 単独抽出で <150 未達、複数 seam/helper 要)**:
  `codebookAvgFailureStrong_tendsto_zero` (RateDistortion/.../FailureTendsto 226、2+ helper 要・
  ファイル末尾の宣言・set 重め) /
  `integral_MRatioLowerZ_le_one` (SMB/AlgoetCover/TwoSidedRatio 231、同ファイルに condLExp... 179 同居 =
  2 target 注意) /
  `entropy_power_inequality_of_density_explicit` (EPI/Case1/SmoothingLimit 225、同ファイルに複数 >150 同居)。
- **multi-target 同居ファイル群 (1 file 1 agent 規律で同時処理、別 agent に割らない)**:
  `RandomCodebook` 3 件 (`random_codebook_E1_swap` 230 / `random_codebook_E2_swap` 215 ほか) /
  `SmoothingLimit` 3 件 / `Mass` 3 件 / `AWGN Walls` 4 件 / `PairBound` 2 件 / `BackwardMartingale` 2 件 /
  `TwoSidedRatio` 2 件。同一ファイル内の複数 target は編集領域が重なるため必ず同一 agent が直列処理する
  (`.git/index.lock` 競合 + 行番号ドリフト回避)。
  ※ `convJointLlr_integrable` (ConvEntropyDensity 229) は floor `negMulLog_convDensity_entropy_ge_density`
  (245) と同居 = floor sibling、touch 注意。
- **運用注記**: 上記 footprint はスナップショット値。同居 floor sibling (option-C 済 >250 残留や別 >150
  target) の有無は Wave 着手時に target ファイルを Read して確認すること (Wave 13 までの計測アーティファクト
  教訓 = 次 matched decl までの距離で測るため、同居宣言の有無で count-win 可否が変わる)。
- プロトコル: 並列 ≤ 2・1 ファイル 1 エージェント・orchestrator 検証は同一。
- **process 申し送り (確定運用)**: worktree isolation 指定が **Wave 6・7 と 2 連続で機能せず**、
  agent commit が main 直書きになった (分離ブランチが作られない)。Wave 7 では wave7a の WIP が
  orchestrator の working tree に `M Mono.lean` として可視化された。確定した運用: (a) この環境では
  worktree が効かない前提で、disjoint file を選べば main 直書きでも衝突しない、(b) orchestrator は各
  agent の **commit 後** に検証する (WIP 中の `M` ファイルには触れない)、(c) 検証は HEAD に乗った状態で
  per-file 実施。次回は worktree 指定を続けても良いが分離は期待しない。

### Phase 1 由来 dedup 候補 (全 4 件決着済、参考)

純抽出で >250 を消せない代わり **重複削除**は総行数を下げるが、裾 >250 は縮まない (重複補題は大定理より
前にあり footprint は独立)。Phase 1 で発見した候補は **4 件すべて決着**: #1 DONE 2/3 (`f7dc459`、
SmoothingLimit ⊃ DensityForm sibling の lift 2 本削除) / #2 import cycle DEAD (Ext→Mono は直接 cycle) /
#3 re-arch 要 = option C 寄り (GeneralDensity ↔ SupplyTwoTime の Blachman per-field、import cycle) /
#4 重複なし FALSE (`eq_sum_indicator_preimage_mul` は TwoSidedRatio 内部 1 件のみ)。

### Phase 1 で確立した検証プロトコル (process 教訓、Phase 2 でも適用)

- **`lake env lean` の silence は「出力が空」で判定する。`rg 'error'` で grep しない。** 新しい Lean の
  `ring`/`ring_nf` 失敗診断は `Try this: [apply] ring_nf` 形式で **"error" 語を含まず**、keyword フィルタを
  すり抜ける (Phase 1 で GaussianWitness の検証を一度すり抜けた)。`out=$(lake env lean $F 2>&1); [ -z "$out" ]`。
- **`lake env lean` の phantom 失敗 (spurious な `ring` 失敗 / unknown identifier) は stale dependency olean
  が原因。`lake build <module>` が arbiter** — 依存を順に rebuild すれば解消し、target は sorryAx-free の
  まま (#print axioms で確認)。並行 `lake build` を多数走らせた後は特に出やすい。
- **namespace はファイル毎に違う** (`EPIDensityForm` / `EPIBlachmanGaussianWitness` / `EPIG2KLFatou` /
  `EPIStamSupplyTwoTime` / `EPIBlachmanGeneralDensity` / `EPIInfiniteVarianceTruncation` /
  `EPICase1RatioLimit` …)。`#print axioms` の FQ 名は `rg '^namespace'` で確認、`.Shannon.` 直下と仮定しない。
- **抽出で露出した unused binder は `_` プレフィックス**して compile を silent に保つ (Mathlib 慣習)。
- **閾値近傍 (~250–300) で ∀-quantified の pure-math ブロックを 2 つ以上持つ target は sub-150 へ
  over-shoot し得る** (Assembly 253→146、Boundary 355→50)。Phase 2 でこの形を優先的に狙うと裾も減る。

## Phase 3 — 最終再実測 + 裾縮小確認 📋

**proof-log: no**。

優先1 (+機会主義分) 完了後:

1. full `lake build` green。
2. `@residual` / `@audit:` タグ総数がパス全体で不変であることを再集計
   ([`audit-tags.md`](audit/audit-tags.md) grep レシピ)。
3. footprint 分布を再実測 ([`mathlib-conventions-gap.md`](mathlib-conventions-gap.md)「再実測コマンド」)。
   **裾の件数 (>250) + max は進捗指標として追跡する** が、現実的 DoD では **pass/fail ゲートではない**
   (知見の通り純抽出では裾は消えない)。本 Phase の達成基準 = 全優先1ターゲットで「clean に割れる
   ブロックを全て抽出済 + max footprint を抽出が許す限り縮小済」。>250 → 0 / 各 ≤150 は **aspirational**
   (option C 待ち)。

## Phase 4 — option C (>250 spine 攻略) ✅ COMPLETE (2026-06-14)

**2026-06-14 ユーザー決定で着手 → 同日完了** (純抽出 DoD とは別軸の aspirational を実スコープ化)。残留 15 本の
不可分 assembly core を `private` de-private 化 + **組立 spine の分解**で >250 から落とし切った。**>250: 15 → 0、
max 907→249**。aspirational DoD「>250→0 / 各 ≤150 (新規 helper)」達成。

**proof-log: no** (純リファクタの延長。target sig + axioms 不変は維持)。

### 阻害メカニズム triage (15 本、`set` 数 / `private` 参照 / sorry=全0、2026-06-14 実測)

| カテゴリ | 本 (fp, set, priv) | option C 手法 |
|---|---|---|
| **set-heavy (≥15 set、最難)** | Mass(677,22,3) / union_bound(536,25,1) / FailureTendsto(653,15,0) / OuterN(468,22,0) / isAwgnTypicality(432,22,2) / Walls(323,16,3) | spine 分解 (set-locals 多数を引数化) + 一部 de-private。最後に回す |
| **mid set (6-11、priv=0、spine 再設計系)** | KLFatouLSC(353,11) / SmoothingLimit explicit(339,9)・smoothed(336,10)・add(264,7) / DensityForm(298,9) / **Mono(289,6)** | set-locals (密度・測度) を純 math helper へ抽出して spine 分解。de-private 不要 |
| **private-blocked (low set、de-private 系)** | TwoSidedRatio(350,2,14) / PairBound(390,2,1) / ConvEntropyDensity(337,9,1) | 参照 `private` を de-private → `have` ブロック抽出。最もクリーン |

### Approach (anti-relabel が本質)

純抽出が >250 を消せなかった原因は (a) `have` ブロックが多数の `set` ローカルを束ねる、(b) `private`
定義を参照し public helper に漏らせない。option C はこの 2 つを解く:

1. **`private` 参照の de-private 化**: 参照される `private` def/lemma から `private` を外し public API 化
   (記述的命名・docstring なし)。これで private-blocked ブロックが top-level 抽出可能になる。
2. **spine 分解 (relabel 厳禁)**: set-coupled な組立核を、束ねている `set` ローカル (密度 `fW`/`rfun`、
   測度 `ν`/`μV`/`μWz` 等 = **数学的対象**) を明示引数に取る純 measure-theory helper へ**複数本**抽出する。
   **1 本の巨大 helper への relabel は禁止** (R8): target が <250 でも新 helper が >250 なら **件数は減らない**。
   各 helper を <150 に分解して初めて >250 件数が減る。seam = Case 分岐 / 自己完結 `have` ブロック。

### 進捗 (option C) — 全 15 本クリア (>250: 15 → 0)

全 target sig byte-identical / `#print axioms` = `[propext, Classical.choice, Quot.sound]` 不変 / 0 新 sorry /
連結ビルド green を orchestrator が**ファイル毎に独立検証**済 (private target は in-namespace short-name で axioms 確認)。
新規 helper は**全 <150** (relabel 回避、R8)。確立した 3 機構:

- **spine 再設計系 (set-local → 明示引数 pure helper)**: Mono 289→188 / KLFatouLSC 353→228 /
  DensityForm 298→172 / SmoothingLimit smoothed 336→196・add 264→192 / OuterN 468→241 (helper5) /
  FailureTendsto 653→226 (helper10、本パス最大2位) / Mass 677→249 (helper15、最大、private target 維持)。
- **de-private 系**: PairBound 390→210 / ConvEntropyDensity 337→245 (de-private1) /
  TwoSidedRatio 350→231 (de-private13) / Walls 323→164 (de-private3) /
  AchievabilityDischarge union_bound 536→245・isAwgnTypicality 432→190 (de-private2)。
- **★ helper 再利用系 (新機構)**: SmoothingLimit explicit 339→225 = DensityForm の 5 lift helper を FQ 名で
  呼ぶだけ (inline 重複除去、新 helper ゼロ)。lift3 系の横断重複は既存 helper 再利用で安く落とせると判明。

**残 0 本。option C 完了。**

### dedup フォローアップ候補 (option C で発見、本パス外・任意)

- **#1 DONE** (`d0cabca`): subcode max-error trick の重複を解消。import 方向は **OuterN → ShannonTheorem** ゆえ「ShannonTheorem を OuterN 呼び出しに差し替え」は cycle で不可。逆に下位 (ShannonTheorem) へ `exists_subcode_maxError_lt_two_mul` を移し、inline 重複 (旧 `ShannonTheorem:609-690`) をその呼び出しへ、OuterN の重複定義を削除 (同名前空間で自動解決)。sig byte-identical / axioms 不変 (sorryAx-free) / full build green、純 ~74 行減。
- **#2 DEAD** (検証済、非機会): `FailureTendsto.encoder_strong_failure_prob_le_rdAmbient` の concrete positivity/indep/marginal 束は **wrapper 1 箇所のみ** (FailureTendsto:382-395) で組まれ、唯一の consumer `codebookAvgFailureStrong_tendsto_zero` に既に再利用済。`AchievabilityPhaseEStrong` は完全 generic (`rdAmbient` 言及 0、docstring のみ)、`Setup` にも具体束なし。consumer が組む X 軸 (iidXs) の indep/ident は wrapper の joint 束とは別系統で重複ではない。**dedup 対象なし。**
- 各ファイルの既存 `mul_le_mul_left'` deprecation (Walls L1079 等) / longLine / `show`→`change` style nit は別スタイルパス。

### Hard invariants (Phase 1 の 4 点 + option C 追加分)

Phase 1 の 4 点 (target sig byte-identical / `#print axioms` 不変 / sorry 数不変・タグ verbatim / compile
clean) をそのまま適用。**加えて**: de-private 化した helper は public API として記述的命名 (staging 語彙
禁止)。spine 分解後に各 helper の footprint を測り **>150 なら更に分解** (anti-relabel)。連結ビルドで
importer green を確認 (de-private は可視性変更ゆえ consumer 再ビルドが要る)。

## 検証

**per-file (各ターゲット完了時、オーケストレータが確認)**:

- `lake env lean <file>` clean (0 error、新規 sorry warning なし)。
- `#print axioms <target>` がリファクタ前と一致 (invariant 2)。
- 対象 signature が byte-identical (invariant 1)。`git diff` で対象宣言行に変化がないこと。
- footprint が下がった (対象 body が短縮された)。

**final (Phase 3)**:

- full `lake build` green (invariant 4)。
- `@residual` (タグ) + `@audit:` 総数が pass 前後で保存 (invariant 3)。
- footprint 分布再実測で裾が縮小。

## DoD (現実的版、2026-06-14 ユーザー決定で緩和)

旧 DoD「>250 tier → 0 / 各 ≤150」は **純 `have` 抽出では達成不能**と実測判明 (上記知見、12 本後
25→24)。組立核 (10+ `set` ローカル結合 / `private` 定義参照) は抽出で不可分。ユーザー決定で
**現実的 DoD** に置換:

- **現実的 DoD (pass/fail ゲート)**: 全優先1ターゲットで **clean に割れるブロックを全て再利用可能な
  public helper へ抽出済** + **max footprint を抽出が許す限り縮小済** + 各ファイルで 4 つの Hard
  invariant を満たし、full build green、タグ総数保存。**不可分な組立核の >250 残留は許容**。
- **裾件数 (>250) + max は進捗指標**として追跡するが pass/fail ゲートではない。
- **aspirational (本パス外)**: 「>250 → 0」「各 ≤150」は option C (= `private` helper の de-private 化
  + 組立 spine の再アーキテクト) を要し本純リファクタパスのスコープ外。
- proof done (0 sorry / 0 residual) は **本パスの DoD ではない**: 純リファクタゆえ sorry 数は不変
  (#4 の 1 sorry を含め保存する)。完成度は別軸 (各 family の moonshot plan が tally)。

## Risks & mitigations

- **R1: auto-param 副条件の暗黙 discharge が抽象化で壊れる** (pilot gotcha 2)。
  → helper signature に regularity instance/hypothesis を明示追加。skeleton 段階で型が通ることを
  先に確認してから中身を移す。
- **R2: `set ... with` のローカルが helper 項と unify せず call site が `exact` で落ちる**
  (gotcha 1)。→ call site で `rw [hX_def]` を入れてから `exact`。
- **R3: `linter.unusedVariables false` のファイルで dead `have` が検出されず残る** (gotcha 4)。
  → 抽出後に `rg` で usage を grep し orphan `have` を手で削除。linter に依存しない。
- **R4: sorry 持ち #4 で `@residual` タグが宙に浮く / 二重化する**。→ デフォルトは sorry ブロックを
  inline 維持 (タグ移動なし)。やむを得ず抽出する場合のみ verbatim relocate (invariant 3)。
- **R5: マルチターゲット・ファイルで並列エージェントが衝突** (`AchievabilityDischarge` ×2 /
  `SmoothingLimit` ×3)。→ 1 ファイル = 1 エージェントが全ターゲットを直列処理 (Approach 参照)。
- **R6: helper が private 定数を引きずり出して public statement に private symbol が漏れる**
  (gotcha 5)。→ private 参照ブロックは抽出せず inline 維持。
- **R7: axiom が静かに変わる (`sorryAx` 混入等)**。→ invariant 2 を per-file で必ず機械確認。
  一致しなければその抽出を revert。
- **R8: relabel — 抽出 helper 自身が新たな >250 モノリスになる** (実例: `rescaledPath_indep_regular`
  498 行)。→ Approach の anti-relabeling Hard rule: helper footprint を都度測り >150 なら確定前に
  さらに小 helper へ再分解。1 モノリスを別名モノリスに付け替えない。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除 (git が履歴)。
プラン予算 ≤ 600 行 / active 判断ログ ≤ 10 entry。

active 判断は無し (option C 完了)。閉じた経緯のみ要約:

1. **純 have 抽出は >250 tier を clear できない → option C で解決** (settled)。当初の純抽出パスは 12 本後 25→24
   止まり (max 907→677) と実測。原因 = (a) `have` が多数 `set` ローカルを束ねる / (b) `private` 参照漏れ。
   option C (= 参照 `private` の de-private + set-local を明示引数化した spine 分解) で **15→0 を達成**。
   anti-relabel (R8、helper >150 は再分解) と「set 結合オーバーヘッドが嵩の主因 = 不可分な数学核は小さい」が鍵。
   なお当初プランの「`negMulLog_convDensity_entropy_ge_density` に 1 sorry」は誤認 (実体は `ConvEntropyMonotone.lean`
   の別宣言 `negMulLog_convDensity_entropy_ge`)。本 target は元から sorry-free だった。
