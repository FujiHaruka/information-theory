# module restructure plan — プロセス語彙ファイル名の概念名化 + 大ファイルの概念分割 🗂️

**Status**: Phase 0 未着手 (本プラン新規作成 2026-06-21) / **Parent**: なし (standalone) /
**関連**: 実測 SoT [`mathlib-conventions-gap.md`](mathlib-conventions-gap.md) §3.A.2 / §3.A.3 / §3.A.6 ・§4 action 2 ・
姉妹リファクタ [`footprint-split-plan.md`](footprint-split-plan.md) (証明内分割) / [`docstring-tidyup-plan.md`](docstring-tidyup-plan.md) (散文プロセス語彙除去、DONE) ・
命名 [`rules/naming.md`](rules/naming.md) ・honesty タグ [`audit/audit-tags.md`](audit/audit-tags.md)

## 進捗

- [ ] Phase 0 — 測定 + 改名マッピング確定 + pilot 1 本で較正 📋
- [ ] Phase 1 — `Draft/` 解消 + 純プロセス語彙ファイル名の概念名化 (path-only 改名中心、低リスク) 📋
- [ ] Phase 2 — `AWGN/Walls.lean` (3549 行) を概念単位に分割 + 改名 📋
- [ ] Phase 3 — 残り 1200+ 行ファイルを概念単位に分割 📋
- [ ] Phase 4 — 最終再実測 + full build green 📋

## Context

`docstring-tidyup-plan.md` (DONE) が **docstring の散文**から、`footprint-split-plan.md` (DONE) が
**証明本体**から Mathlib との乖離を消した。残る最大のギャップは
[`mathlib-conventions-gap.md`](mathlib-conventions-gap.md) §3.A の項目 2/3/6 = **ファイル名・モジュール構造**に
プロセス語彙とモノリスが残っていること。これは散文版・証明版でやったことの「ファイル間版」。

実測スナップショット (2026-06-21、再実測コマンドは gap doc 末尾):

| 指標 | Mathlib | 本プロジェクト | 残ギャップ |
|---|---|---|---|
| ファイル行数 中央値 / 最大 | 185 / 1523 | 315 / **3549** (`AWGN/Walls.lean`) | 1200 行超 **14 本** |
| プロセス由来ファイル名 | 0 | `*Discharge.lean` ×15・`Walls.lean`・`Draft/` 4 本・`*Body`/`*Complete`/`*Partial`/`*Pure`/`*Setup` 多数 | 概念名へ |

Mathlib の慣習 (§1.1): **ファイル = 1 数学概念、ファイル名は数学的対象** (`Hamming.lean`/`KraftMcMillan.lean`)。
開発プロセス・進捗段階を名前にしない。`Walls`/`Discharge`/`Draft`/`Body` は全てプロセス語彙。

### 鍵となる構造的事実 — namespace はディレクトリ由来 (リスクを大きく下げる)

`rename-module-plan.md` (ライブラリ名 → `InformationTheory`、**完了済**) が扱った 552 ファイル波及とは
**桁違いに小さい**。理由: **Lean では namespace と module path (ファイル名) は独立**で、本プロジェクトの
namespace は大半が**ディレクトリ由来** (`namespace InformationTheory.Shannon.AWGN`)。

- ファイルを同一ディレクトリ内で**改名 / 分割**しても、各 decl の **fully-qualified 名は byte-identical** →
  **consumer 側の decl 参照は一切壊れない**。波及するのは `import <path>` 行**だけ**。
- 実測した import 波及: `AWGN.Walls` を import = **4 ファイル** / `AchievabilityDischarge` = 2 / 全 `*Discharge`
  合計 = **29 ファイル** / `Draft.*` = 8 ファイル (root + 7 実 consumer)。
- **例外 (高リスク)**: namespace **自体**にプロセス語彙を持つファイルがある:
  `Draft/.../HoeffdingInteriorBody.lean` は `namespace InformationTheory.Shannon.HoeffdingInteriorBody`、
  `Draft/.../ChannelCodingConverseGeneralComplete.lean` は `namespace ...ChannelCodingConverseGeneral`。
  これらの namespace を直すと **decl 参照に波及**する → 必ず `scripts/dep_consumers.sh <FQ名>` を先に取る。

→ 含意: **path-only 改名 (namespace 既に clean) は import 行のみ = 低リスク・機械的**。
**namespace-also 改名は dep 波及あり = consumer 確認必須**。Phase 1 は前者を優先する。

## Approach

**全体の形**: 「プロセス語彙ファイル名 → 数学概念名への改名」と「巨大ファイル → 複数の概念ファイルへの分割」を、
**共通の機械的手順**で扱う純構造リファクタ。証明内容・decl の FQ 名・axiom・sorry 数は全て不変
(`footprint-split` / `docstring-tidyup` と同じ「内容不変」の系譜)。

共通手順 (1 ターゲット = 1 単位):

1. **概念名を確定**: 対象ファイルの headline (`@[entry_point]`) と数学的内容を Read し、Mathlib 流の
   数学的対象名を決める ([`rules/naming.md`](rules/naming.md)、staging 語彙 `Discharge`/`Body`/`Full`/`Strong`
   /`Complete`/`Partial`/`Pure`/`Draft` 禁止)。最終名は**実行時に Read で確定** (プラン段階では候補)。
2. **`git mv`** で改名 / 分割 (履歴保持)。分割は概念の継ぎ目 (`/-! ## ... -/` セクション境界) で切る。
3. **import 行を一括更新**: 旧 path を import する全ファイルの `import` 行を新 path に置換
   (分割なら 1 → 複数 import に展開)。root `InformationTheory.lean` の登録も更新。
4. **namespace を変える場合のみ** decl 参照も置換 (事前に `dep_consumers.sh` で blast radius 確定)。
5. **検証**: full `lake build` green (import 波及があるため per-file `lake env lean` では不十分、§検証) +
   移動した headline の `#print axioms` 不変 + sorry/タグ数不変。

**リスク順に進める**: Phase 1 (path-only 改名、import 行のみ) → Phase 2/3 (大ファイル分割、概念の継ぎ目読解が要る)。
最大の山 `Walls.lean` (3549 行・プロセス名・モノリスの三重ギャップ) は Phase 2 で単独攻略。

**オーケストレーション**: 並列度 ≤ 2 の disjoint-file ownership。改名/分割は import 行が他ファイルに波及するため、
**並列時は import を共有しないターゲットを選ぶ** (同一 importer を持つ 2 ファイルを別エージェントに振らない)。
本質的に逐次寄り (full build が arbiter ゆえ commit 前に毎回 full build)。**オーケストレータが full build 検証 + commit**。

## 改名 / 分割マッピング (実行時に Read で最終確定、ここは候補)

### Phase 1 ターゲット — path-only 改名 + Draft 解消

namespace が既に clean (`InformationTheory.Shannon[.AWGN|.RateDistortion|...]`) なものは **import 行のみ波及**。

| 現ファイル | headline (概念の手がかり) | 候補概念名 / 移設先 | 波及 |
|---|---|---|---|
| `Draft/Shannon/RateDistortionAchievabilityPhaseE.lean` (29) | (薄い wrapper) | `RateDistortion/` 配下の概念名 | path-only |
| `Draft/Shannon/RateDistortionAchievabilityPhaseEDischarge.lean` (270) | `pmfToMeasure_real_singleton_pos` 系 | `RateDistortion/` 配下 | path-only |
| `Draft/Shannon/ChannelCodingConverseGeneralComplete.lean` (273) | `condMutualInfo_le_of_markov_joint` | `ChannelCoding/` 配下 (例 `ConverseGeneralMarkov`) | **namespace も** (`...ChannelCodingConverseGeneral`)→ dep 確認 |
| `Draft/Shannon/HoeffdingInteriorBody.lean` (220) | `hoeffding_minimizer_ge_at_interior` 等 | `Hoeffding/` 配下 (例 `InteriorMinimizer`) | **namespace も** (`...HoeffdingInteriorBody`)→ dep 確認 |
| `AWGN/AchievabilityDischarge.lean` (1997) | `awgn_avg_error_union_bound` / `gaussianCodebook_*` | 分割対象 (Phase 3 へ送る、>1200) | import 2 |
| `AWGN/ConverseDischarge.lean` (1756) | `perLetterMI`/`jointMIXnYn` 系 def | 分割対象 (Phase 3 へ送る、>1200) | — |
| `AWGN/F1Discharge.lean` (129) | `awgn_theorem_F1_discharged` 等 | `AWGN/` 概念名 (F1=?, 内容で確定) | path-only |
| `AWGN/F2F3Discharge.lean` (145) | `awgn_capacity_closed_form_of_maxent_hypotheses` | `AWGN/` 概念名 | path-only |
| `AWGN/MIBridgeDischarge.lean` (124) | `awgn_output_gaussian_of_bind_eq_conv` | `AWGN/MutualInfoBridge` 等 | path-only |
| `Hoeffding/SandwichDischarge.lean` (177) | `hoeffding_tradeoff_achievability_at_boundary` | `Hoeffding/` 概念名 | path-only |
| `RateDistortion/ConvexityDischarge.lean` (15) | (薄い) | `RateDistortion/` 概念名 or 親へ吸収 | path-only |
| `WynerZiv/Discharge.lean` (327) | `wynerZivRatePmf_antitone` 等 | `WynerZiv/RateMonotone` 等 | path-only |
| `ParallelGaussian/L_PG0Discharge.lean` (25) | (薄い) | `ParallelGaussian/` 概念名 | path-only |
| `Cramer/LC2Discharge.lean` (147) | `cgf_eval_eq_cgf_base` | `Cramer/` 概念名 (cgf 系) | path-only |
| `Cramer/LC2DischargeExt.lean` (217) | `tilted_lln_*` | `Cramer/TiltedLLN` 等 | path-only |
| `ChannelCoding/ShannonTheoremFullDischarge.lean` (70) | `shannon_noisy_channel_coding_theorem_general_full` | `ChannelCoding/` 概念名 or 親へ吸収 | path-only |
| `EPI/Stam/Discharge.lean` (544) | `epi_via_stam` 系 | `EPI/Stam/EpiViaStam` 等 | path-only |
| `*Body.lean` 群 (~13: `GaussianPDFVarianceDerivBody`/`BindConvBody`/`MIDecompBody`/`SandwichBody`/`LagrangeIVTBody`/`InteriorGradientBody`/`ZivCountingBody`/`PhraseCountAsymptoticBody`/`CondEntDiffConvexBody`/`ObjectiveConvexityBody`/`ConvexityBody`/`V2DeBruijnBody`/`V2HeatFlowBody`) | 各 headline | `Body` を外した概念名 | path-only (namespace 要確認) |
| `*Complete`/`*Partial`/`*Pure`/`*Setup`/`*Witness`/`*Final` 系 | 各 headline | 概念名へ (`FeedbackComplete`→?, `ConverseMemorylessPure`→?, `WhittakerShannonPartial`→?) | 個別確認 |

> 注: `Converse`/`Achievability` は情報理論の**数学概念**ゆえ語として残してよい (達成可能性・逆定理)。
> 除去対象は `Discharge`/`Body`/`Draft`/`Complete`/`Full`/`Strong`/`Pure`/`Partial`/`Setup` 等の**開発段階語**。
> `F1`/`F2F3`/`LC2`/`L_PG0` 等の **task-code** も数学概念名へ (docstring-tidyup の dev-slug 除去と同方針)。

### Phase 2 ターゲット — `AWGN/Walls.lean` (3549 行) の概念分割

実測したセクション境界 (= 概念の継ぎ目、namespace は全体 `InformationTheory.Shannon.AWGN` ゆえ分割で decl 不変):

| 行範囲 | セクション (現 `/-! -/`) | 分割先候補 |
|---|---|---|
| 44–144 | `## Continuous Gaussian AEP` | `AWGN/ContinuousGaussianAEP.lean` |
| 145–1307 | `### Per-letter AWGN KL closed form and n-fold identity` | `AWGN/PerLetterKL.lean` (最大塊、要更分割検討) |
| 1308–1442 | `## Per-codeword power constraint` | `AWGN/PerCodewordPowerConstraint.lean` |
| 1489–1822 | `### Per-letter log-density integrability` | `AWGN/PerLetterLogDensityIntegrable.lean` |
| 1823–3321 | `### Memoryless MI chain rule` | `AWGN/MemorylessMIChainRule.lean` (最大塊、要更分割検討) |
| 3322–3548 | `### Markov factorization` | `AWGN/MarkovFactorization.lean` |

`Walls.lean` 自体は消す (薄い re-export も残さない方針 = Mathlib に re-export hub の慣習なし)。
分割後の各ファイルが依然 >1200 なら Phase 3 で更分割。`import ...AWGN.Walls` を持つ 4 importer は
分割後の必要ファイル群への import に展開する。

### Phase 3 ターゲット — 残り 1200+ 行ファイル (14 本、Walls 除く 13 本)

`GreedyParsingImpl` 2090 / `AchievabilityDischarge` 1997 / `ConverseDischarge` 1756 /
`ConditionalMethodOfTypes/Mass` 1482 / `Sanov/LDPEquality` 1395 / `SMB/AlgoetCover/TwoSidedRatio` 1381 /
`Stein` 1358 / `EPI/Case1/TwoTime/Object` 1320 / `ChannelCoding/Achievability/RandomCodebook` 1303 /
`Huffman/Basic` 1279 / `BlockwiseChannel` 1239 / `Probability/TwoSidedExtension/BackwardIntegral` 1229 /
`SMB/AlgoetCover/Core` 1216。

着手時に各ファイルのセクション構造を Read で確認し、概念の継ぎ目で分割。Mathlib 中央値 185・最大 1523 が
目安だが、**1523 は固定キャップでなく診断トリガー** (footprint plan と同じ思想)。不可分な 1 概念が大きいなら
許容 (例: `Stein` は Stein の補題 1 概念で 1358、分割せず据え置きの判断もあり得る = 着手時に判定)。

## Hard invariants (違反 = DEFECT — 純構造リファクタの定義)

1. **decl の FQ 名が不変**: 移動/分割した全 `theorem`/`lemma`/`def`/`structure` の fully-qualified 名が
   byte-identical (namespace を変えない限り自動的に満たされる。namespace を変える場合は dep_consumers で
   全参照を追従更新したことを確認)。consumer から見た API 不変。
2. **`#print axioms <headline>` 不変**: 移動した各 `@[entry_point]` の axiom 集合が
   `[propext, Classical.choice, Quot.sound]` (sorry 持ちは `sorryAx` 込み) で改名前後一致。
3. **sorry 数 + honesty タグ verbatim 保存**: ツリー全体の `sorry` 総数不変。`@residual(...)`/`@audit:*` は
   タグ文字列ごと verbatim 保存 (分割でファイルを跨いでも移動先に verbatim relocate)。
4. **full `lake build` green**: import 行が他ファイルに波及するため、per-file `lake env lean` では不十分。
   各 Phase 完了時に full `lake build InformationTheory` が 0 error。
5. **プロセス語彙 0**: 新ファイル名・新 namespace に `Discharge`/`Walls`/`Draft`/`Body`/`Complete`/`Full`/
   `Strong`/`Pure`/`Partial`/`Setup`/`Witness` 及び task-code (`F1`/`LC2`/`L_PG0` 等) を使わない。
6. **root 登録の整合**: 新ファイルは `InformationTheory.lean` に import 登録、消したファイルは登録削除
   (pre-commit が「新ファイルの import 未登録」を WARN)。

## Phases

### Phase 0 — 測定 + 改名マッピング確定 + pilot 📋

**proof-log: no** (純構造リファクタ)。

1. 改名対象を全列挙し、各ファイルの namespace を確認 (`rg '^namespace'`) して **path-only / namespace-also** に
   二分する。namespace-also は `scripts/dep_consumers.sh <FQ名>` で blast radius を確定。
2. 上記マッピング表の候補概念名を、各ファイルの headline を Read して確定 ([`rules/naming.md`](rules/naming.md))。
3. **pilot**: 最小の path-only 改名 1 本 (例 `ParallelGaussian/L_PG0Discharge.lean` 25 行 or
   `RateDistortion/ConvexityDischarge.lean` 15 行) で「git mv → import 行置換 → full build green →
   #print axioms 不変」の手順を較正し、gotcha を本節に記録。

### Phase 1 — Draft/ 解消 + 純プロセス語彙ファイル名の改名 📋

**proof-log: no**。低リスク (path-only 中心)。

- **Draft/ ディレクトリを消す**: 4 ファイルを正規の math サブツリー (`RateDistortion/`/`ChannelCoding/`/
  `Hoeffding/`) へ移設 + 概念名化。`Draft` は「下書き」を含意するが実 consumer (7 本) を持つ = 本採用ゆえ
  正規化する。namespace-also の 2 本 (`HoeffdingInteriorBody`/`ChannelCodingConverseGeneral`) は dep 追従。
- **`*Discharge.lean` ×15 を概念名化** (>1200 の Achievability/Converse は除き Phase 3 へ送る)。
- **`*Body`/`*Complete`/`*Pure`/`*Partial`/`*Setup`/`*Witness`/`*Final` 系**を概念名化。
- マッピング表の波及列に従い、disjoint import のものから並列 ≤ 2 で。各 commit 前に full build green。

### Phase 2 — `AWGN/Walls.lean` (3549 行) 概念分割 📋

**proof-log: 推奨** (最大の山。分割の継ぎ目判断に余地があり、教訓を残す価値がある)。

- 上記セクション表の 6 概念へ `git mv` 分割。namespace `InformationTheory.Shannon.AWGN` は全分割先で不変
  ゆえ decl FQ 名不変 = consumer 無破壊。
- 最大塊 (`PerLetterKL` 145–1307 / `MemorylessMIChainRule` 1823–3321) が分割後も >1200 なら、その内部の
  サブセクションで更分割 (anti-monolith)。
- `Walls.lean` を削除、4 importer の import 行を分割先群へ展開。full build green。

### Phase 3 — 残り 1200+ 行ファイルの概念分割 📋

**proof-log: 機会主義的** (大きな分割のみ)。

- 13 ファイルを着手時にセクション構造を Read して概念分割。不可分 1 概念の大ファイルは許容判定 (§Phase 3 ターゲット注)。
- `AchievabilityDischarge`/`ConverseDischarge` は Phase 1 で送られた分割対象。分割と同時にファイル名の
  `Discharge` も除去 (一石二鳥)。

### Phase 4 — 最終再実測 + 検証 📋

**proof-log: no**。

1. full `lake build InformationTheory` green。
2. プロセス語彙ファイル名 0 を確認 (`find InformationTheory -name '*.lean' | grep -iE 'Discharge|Walls|Draft|Body|...'` 空)。
3. ファイル行数分布再実測 (gap doc 再実測コマンド)。1200 行超件数 + max の縮小を進捗指標として記録
   (footprint plan 同様、不可分 1 概念の大ファイルは pass/fail ゲートにしない)。
4. `@residual`/`@audit:` タグ総数がパス前後で不変を再集計。

## 検証

**per-target (各改名/分割完了時、オーケストレータが確認)**:

- full `lake build InformationTheory` が 0 error (import 波及ゆえ per-file では不十分)。
  ※ 速度のため、波及が局所的な path-only 改名は「対象 + 全 importer の `lake build <module>`」で代替可、
    Phase 末で full build を 1 回。
- 移動した `@[entry_point]` の `#print axioms` が改名前と一致 (invariant 2)。
- 改名なら decl FQ 名不変 / namespace 改名なら `dep_consumers.sh` の全参照が追従済 (invariant 1)。

**final (Phase 4)**: full build green / プロセス語彙ファイル名 0 / タグ総数保存 / 行数分布再実測。

## DoD

- **現実的 DoD (pass/fail ゲート)**: 全プロセス語彙ファイル名 (Discharge/Walls/Draft/Body/task-code 等) が
  数学概念名に置換済 + Draft/ ディレクトリ解消済 + `Walls.lean` 分割済 + 6 つの Hard invariant を全て満たし、
  full build green、タグ総数保存。
- **進捗指標 (pass/fail ゲートではない)**: 1200 行超件数 + max。不可分 1 概念の大ファイル残留は許容
  (footprint plan と同じ思想。Mathlib 1523 もキャップでなく診断トリガー)。
- proof done (0 sorry / 0 residual) は**本パスの DoD ではない**: 純構造リファクタゆえ sorry 数不変。完成度は
  別軸 (各 family の moonshot plan が tally)。honesty audit は**不要** (新規 sorry/@residual を導入しないため。
  タグ数保存で代替検証)。

## Risks & mitigations

- **R1: namespace-also 改名で decl 参照が壊れる** (`HoeffdingInteriorBody` 等)。→ 改名前に
  `scripts/dep_consumers.sh <FQ名> --transitive` で全参照を確定、namespace + 参照を同一 commit で追従更新。
  迷ったら **namespace は据え置き path のみ改名** (低リスク優先)。
- **R2: import 行の置換漏れで build が壊れる**。→ full build を arbiter にする (invariant 4)。phantom な
  `unknown identifier` は stale olean ゆえ `lake build <module>` で refresh (footprint plan 教訓)。
- **R3: 分割で `@residual`/`@audit` タグが宙に浮く / ファイルを跨いで失われる**。→ タグ持ち decl は移動先へ
  タグごと verbatim relocate。Phase 末でタグ総数照合 (invariant 3)。
- **R4: private helper を共有する decl を別ファイルに分けると private が見えなくなる** (CLAUDE.md:
  「private は file-scoped」)。→ 分割で private を跨ぐ場合は de-private 化 (public + 記述的命名、
  footprint option C と同手法) するか、private 共有群を同一ファイルに保つ継ぎ目を選ぶ。
- **R5: 並列エージェントが同一 importer の import 行を同時編集して衝突**。→ disjoint import のターゲットのみ
  並列 (Approach)。同一 importer を共有する 2 ファイルは同一エージェント直列。
- **R6: full build コストで inner loop が遅い**。→ path-only 改名は局所 `lake build <module>` で回し、
  Phase 末に full build を 1 回 (検証節)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除 (git が履歴)。
プラン予算 ≤ 600 行 / active 判断ログ ≤ 10 entry。

1. **2026-06-21 起案**: footprint split / docstring tidyup 完遂後、残る Mathlib ギャップ = ファイル名・構造の
   プロセス語彙 (gap §4 action 2)。ユーザー決定で専用プラン化。鍵は「namespace ディレクトリ由来 → 改名は
   import 行のみ波及 (Walls 4 / 全 Discharge 29)、ライブラリ名 rename の 552 波及とは桁違いに小」。
   path-only / namespace-also の二分でリスク管理し、低リスクの Phase 1 から。Copyright ヘッダ (§4-3) は
   従来通り upstream まで保留 (本パス対象外)。
