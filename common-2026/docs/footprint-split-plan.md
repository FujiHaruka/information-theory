# footprint split plan — モノリシック証明を named helper へ分解する純リファクタ ✂️

**Status**: Phase 0 DONE (pilot 較正済) / 優先1 Wave 着手前 / **Parent**: なし (standalone) /
**関連**: 実測 SoT [`mathlib-conventions-gap.md`](mathlib-conventions-gap.md) §3.A.1 / §4.1 ・
命名 [`rules/naming.md`](rules/naming.md) ・docstring [`rules/docstrings.md`](rules/docstrings.md) ・
Lean style [`rules/lean-style.md`](rules/lean-style.md) ・honesty タグ [`audit/audit-tags.md`](audit/audit-tags.md)

## 進捗

- [x] Phase 0 — 測定 + pilot 較正 ✅ (`floorMatrix_dist_le`、commit `d2fb1fa`)
- [ ] Phase 1 — 優先1 (>250 行 tier、25 本中 1 本 done) を named helper へ分解 📋
- [ ] Phase 2 — 優先2 (>115 行 tier、159 本) を機会主義的に分解 📋
- [ ] Phase 3 — 最終再実測 + 裾縮小確認 📋

## Context

Mathlib 最大の暗黙規律は **1 宣言の footprint を小さく保ち、長くなったら名前付き補題に割る** こと
([`mathlib-conventions-gap.md`](mathlib-conventions-gap.md) §1.2 / §3.A.1)。footprint =
宣言の `theorem`/`lemma`/`def` 行から次の top-level 宣言までの行数。Mathlib は IT+Probability で
**中央値 7 / 最大 115 / 150 超ゼロ**。本プロジェクトは粒度が大きく乖離している。

**現状分布 (2026-06-14 実測、§4.1 の母集団 = 全宣言 2663 本)**:

| 指標 | 値 |
|---|---|
| 中央値 | 18 |
| p90 | 87 |
| p99 | 238 |
| 最大 | 907 |
| **> 250 行** | **25 本** (= 優先1) |
| > 150 行 | 97 本 |
| > 115 行 | 159 本 (= 優先2) |
| 49–115 行 | 392 本 (機会主義のみ) |

このパスは **モノリシック証明の自己完結 `have` ブロックを top-level named helper 補題に切り出す**
だけの **純リファクタ**: 証明内容不変・対象 signature 不変・axiom 不変・sorry 数不変。proof done
(0 sorry / 0 residual) とは独立に進められる = 壁を一切触らない。

## Approach

**全体の形**: 「巨大証明を読む → 自己完結する `have` ブロックを抽出単位として特定 → top-level の
public・記述的命名・docstring なしの補題へ切り出し → 元証明はその補題を `exact`/`apply` で呼ぶ →
axiom 不変を `#print axioms` で確認」を、ファイル単位で 1 宣言ずつ適用する。

抽出は **Skeleton-driven** に行う: 先に helper の signature を `:= by sorry` で立てて型が通ることを
確認 → 中身を元証明の `have` ブロックから移植 → 元証明側を呼出に置換 → orphan `have` を削除。
中身を 1 つ移すごとに `lake env lean <file>` でグリーンを確認する (一括書換しない)。

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

| ファイル | ターゲット (footprint) |
|---|---|
| `AWGN/AchievabilityDischarge.lean` | `awgn_random_coding_union_bound` (672) + `isAwgnTypicalityHypothesis` (597) — 計 2 本 |
| `EPI/Case1/SmoothingLimit.lean` | `entropy_power_inequality_of_density_explicit` (464) + `entropyPower_smoothed_epi_perT` (365@:645) + `entropy_power_add_ge_of_finite_variance` (310@:1010) — 計 3 本 |

同一ファイル内の複数ターゲットは編集領域が重なるため **必ず同一エージェント**が直列処理する
(`.git/index.lock` 競合 + 行番号ドリフト回避)。

### 優先1 ターゲット一覧 (25 本、1 本 done)

| # | file:line (footprint) | 対象 | sorry | 備考 |
|---|---|---|---|---|
| 1 | `ConditionalMethodOfTypes/Mass.lean:318` (907) | `conditional_KL_concentration_ge` | 0 | 最大。筆頭 |
| 2 | `RateDistortion/AchievabilityPhaseEStrongFinal/FailureTendsto.lean:50` (798) | `codebookAvgFailureStrong_tendsto_zero` | 0 | |
| 3 | `AWGN/AchievabilityDischarge.lean:427` (672) | `awgn_random_coding_union_bound` | 0 | マルチ (with #6) |
| 4 | `EPI/G2/ConvEntropyDensity.lean:117` (629) | `negMulLog_convDensity_entropy_ge_density` | **1** | **要注意** (下記) |
| 5 | `ChannelCoding/ShannonTheoremFullDischarge/OuterN.lean:126` (608) | `exists_N_for_smooth_achievability_uniform` | — | |
| 6 | `AWGN/AchievabilityDischarge.lean:1347` (597) | `isAwgnTypicalityHypothesis` | — | マルチ (with #3) |
| 7 | `EPI/Case1/RatioLimit/PathRegular.lean:466` (590) | `isRescaledPathRegular_of_methodX` | — | |
| 8 | `AWGN/Walls.lean:739` (485) | `continuousAepGaussian_holds` | — | §3 筆頭例 |
| 9 | `EPI/Case1/SmoothingLimit.lean:132` (464) | `entropy_power_inequality_of_density_explicit` | — | マルチ (3 ターゲット) |
| 10 | `EPI/DensityForm.lean:48` (430) | `entropy_power_inequality_of_density` | — | |
| 11 | `SlepianWolf/FullRateRegion/PairBound.lean:451` (420) | `swErrorProb_total_expectation_le` | — | |
| 12 | `EPI/Blachman/GaussianWitness.lean:301` (390) | `isBlachmanConvReady_gaussianPDFReal` | — | |
| 13 | `SMB/AlgoetCover/TwoSidedRatio.lean:986` (382) | `integral_MRatioLowerZ_le_one` | — | |
| 14 | `EPI/G2/KLFatouLSC.lean:351` (374) | `negMulLog_convDensity_limsup_le` | — | |
| 15 | `EPI/Case1/SmoothingLimit.lean:645` (365) | `entropyPower_smoothed_epi_perT` | — | マルチ (3 ターゲット) |
| 16 | `EPI/Stam/SupplyTwoTime.lean:193` (364) | `isBlachmanConvReady_convDensityAdd_gaussian_asym` | — | |
| 17 | `HypercubeEdge/Boundary.lean:193` (355) | `two_sum_projection_eq` | — | |
| 18 | `EPI/Blachman/GeneralDensity.lean:201` (347) | `isBlachmanConvReady_convDensityAdd_gaussian` | — | |
| 19 | `EPI/Unconditional/TruncationLimit/Mono.lean:77` (330) | `differentialEntropyExt_mono_add_of_integrable` | — | |
| 20 | `EPI/Case1/SmoothingLimit.lean:1010` (310) | `entropy_power_add_ge_of_finite_variance` | — | マルチ (3 ターゲット) |
| — | `ConditionalMethodOfTypes/Core.lean:360` (was 267) | `floorMatrix_dist_le` | 0 | **DONE** pilot `d2fb1fa` (253→122、helper 3 本) |
| 21 | `ChannelCoding/Achievability/RandomCodebook.lean:507` (260) | `random_codebook_E1_swap` | — | |
| 22 | `EPI/InfiniteVariance/Truncation/Construction.lean:505` (256) | `integrable_negPart_negMulLog_map_condTrunc_sum` | — | |
| 23 | `ChannelCoding/ShannonTheoremFullDischarge/SmoothInstantiation.lean:51` (256) | `channel_coding_achievability_smooth_at_N_le` | — | |
| 24 | `EPI/Case1/RatioLimit/Assembly.lean:342` (253) | `entropyPower_add_ge_case1_of_methodX` | — | |

### sorry 持ちターゲット (#4) の特別扱い

`EPI/G2/ConvEntropyDensity.lean:117` `negMulLog_convDensity_entropy_ge_density` は **sorry=1**。
invariant 3 より:

- sorry を含む `have` ブロックを **抽出する場合**、切り出した helper が当該 `@residual(...)` タグを
  **verbatim relocate** して担う (元の sorry 直前/docstring 末尾の文字列をそのまま移す)。
- **最も安全な選択は、sorry ブロックを inline のまま残す**こと。sorry を持たない周辺の自己完結
  `have` のみ抽出し、sorry ブロックは元証明に置いておく。この場合タグの移動は発生せず invariant 3 は
  自明に保たれる。**デフォルトはこちら**。

## Phase 2 — 優先2 (>115 行 tier) を機会主義的に分解 📋

**proof-log: no**。

優先1 完了後に着手。>115 行 tier は **159 本**。本 Phase では個別列挙しない (優先1 と異なり、
着手時に再実測してファイル単位で拾う = §4.1 入力データのスナップショットに固定しない)。

- 優先1 と同じ抽出ルール・gotcha・Mathlib 流 helper ルール・Hard invariants を適用する。
- **機会主義的に進める**: 優先1 で触ったファイルに >115 の隣接宣言があれば同 Wave で拾う。
- **49–115 行 tier (392 本) は機会主義のみ**: 専用 Wave を組まない。優先1/2 で開いたファイルに
  あれば拾う程度。

## Phase 3 — 最終再実測 + 裾縮小確認 📋

**proof-log: no**。

優先1 (+機会主義分) 完了後:

1. full `lake build` green。
2. `@residual` / `@audit:` タグ総数がパス全体で不変であることを再集計
   ([`audit-tags.md`](audit/audit-tags.md) grep レシピ)。
3. footprint 分布を再実測 ([`mathlib-conventions-gap.md`](mathlib-conventions-gap.md)「再実測コマンド」)
   して **裾が縮んだ** (>250 件数の減少 / max の低下) ことを確認。中央値を 7〜10 へ寄せるのが
   長期目標だが、本 Phase の達成基準は **>250 tier の解消** (各ターゲット ≤ 150 行への分解)。

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

## DoD

- **本パスの "done"**: 優先1 の 25 本 (pilot 1 本済) が全て ≤ 150 行へ分解され、各ファイルで 4 つの
  Hard invariant を満たし、full build green、タグ総数保存、footprint 再実測で >250 tier = 0。
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

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除 (git が履歴)。
プラン予算 ≤ 600 行 / active 判断ログ ≤ 10 entry。

1. **抽出単位は「数学優先」**: pilot 較正で `μ` 抽象化より pure 算術核 (`(n:ℕ)(q s ε:ℝ)`) を切るのが
   最 clean と確定 (gotcha 3)。優先1 でも measure 非依存ブロックを第一候補にする。
2. **sorry 持ち #4 のデフォルトは inline 維持**: `negMulLog_convDensity_entropy_ge_density` の
   1 sorry は抽出せず inline に残し、周辺の sorry-free ブロックのみ切る。タグ移動を回避し invariant 3 を
   自明化する (抽出が必要になったら verbatim relocate へ切替)。
