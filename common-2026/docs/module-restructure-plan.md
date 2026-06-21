# module restructure plan — プロセス語彙ファイル名の概念名化 + 大ファイルの概念分割 🗂️ ✅ DONE

**Status**: **完了 (2026-06-21)** — 全 Phase green、DoD met / **Parent**: なし (standalone) /
**関連**: 実測 SoT [`mathlib-conventions-gap.md`](mathlib-conventions-gap.md) §3.A.2 / §3.A.3 / §3.A.6 ・§4 action 2 ・
姉妹リファクタ [`footprint-split-plan.md`](footprint-split-plan.md) (証明内分割) / [`docstring-tidyup-plan.md`](docstring-tidyup-plan.md) (散文プロセス語彙除去、DONE) ・
命名 [`rules/naming.md`](rules/naming.md) ・honesty タグ [`audit/audit-tags.md`](audit/audit-tags.md)

## 進捗

- [x] Phase 0 — 測定 + 改名マッピング確定 + pilot 1 本で較正 (bisection 完了、pilot `MIBridgeDischarge → MutualInfoBridge` 完了) ✅
- [x] Phase 1a — path-only 改名 + 空スタブ削除 (低リスク、機械的)。pilot+AWGN群 / batch2 WynerZiv·LZ78·Gaussian / FisherInfo Body 除去 / ChannelCoding dir 改名 + 空スタブ 2 本 / RateDistortion PhaseE family 完了 ✅
- [x] Phase 1b — namespace-also 改名 (全 8 family DONE: WhittakerShannon/Hoeffding×5/EPI-Stam×4/Cramer/Blachman/ChannelCodingConverseGeneral/ChannelCodingFeedback/FisherInfoV2)。Draft/ dir 完全解消 ✅
- [x] Phase 2 — `AWGN/Walls.lean` (3549 行) を3概念に分割 (`KLCapacityAndAEP`/`PerCodewordPowerConstraint`/`ConverseMIChainRule`)。private 結合で6→3に圧縮 (R4(b)、de-privateゼロ)。full build green(3477) ✅ (24111a5)
- [x] Phase 3 — 残り 1200+ 行ファイル 13/13 処理完了 (2 構造変更: Stein 3分割 / GreedyParsingImpl→AsymptoticOptimality 改名; 3 不可分1概念許容; 他 8 は前 leg) ✅
- [x] Phase 4 — 最終再実測 + full build green(≈3496)・プロセス語彙ファイル名0(scope内)・タグ保存・行数分布再実測 ✅

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
- **高リスク group (実測で判明)**: namespace **自体**にプロセス語彙を持つファイルが **~16 本** (当初「例外 2 本」
  という見積もりは過小 — 後述の実測 bisection 参照)。これらの namespace を直すと **decl 参照に波及**する →
  必ず `scripts/dep_consumers.sh <FQ名> --transitive` を先に取る。namespace を複数ファイルが共有している
  グループ (例: `...ChannelCodingConverseGeneral` ×3 本、`...Cramer.Discharge` ×2 本) は**グループ全体を
  同一 commit で移動**しないと build が壊れる。
- **空スタブ 2 本** (宣言 0) が判明 → 改名ではなく**削除 + importer redirect** で処理 (後述)。

→ 含意: **path-only 改名 (namespace 既に clean) は import 行のみ = 低リスク・機械的** → Phase 1a 優先。
**namespace-also 改名は dep 波及あり = consumer 確認必須** → Phase 1b に分離。

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

## 改名 / 分割マッピング (実測 bisection 結果 — 実行時に Read で概念名を最終確定)

> 注: `Converse`/`Achievability` は情報理論の**数学概念**ゆえ語として残してよい (達成可能性・逆定理)。
> 除去対象は `Discharge`/`Body`/`Draft`/`Complete`/`Full`/`Strong`/`Pure`/`Partial`/`Setup` 等の**開発段階語**。
> `F1`/`F2F3`/`LC2`/`L_PG0` 等の **task-code** も数学概念名へ (docstring-tidyup の dev-slug 除去と同方針)。

### Phase 1a ターゲット — path-only 改名 (namespace clean → import 行のみ波及、低リスク)

namespace が既に clean (`InformationTheory.Shannon[.AWGN|.RateDistortion|...]` 等) なもの。

| 現ファイル | 候補概念名 / 移設先 | 備考 |
|---|---|---|
| `AWGN/MIBridgeDischarge.lean` (124) | `AWGN/MutualInfoBridge` | **pilot 完了** |
| `AWGN/F1Discharge.lean` (129) | `AWGN/` 概念名 (実行時 Read で確定) | ns `...AWGN` |
| `AWGN/F2F3Discharge.lean` (145) | `AWGN/CapacityClosedForm` 等 | ns `...AWGN` |
| `AWGN/BindConvBody.lean` | `AWGN/` 概念名 (実行時確定) | ns `...AWGN` |
| `AWGN/MIDecompBody.lean` | `AWGN/` 概念名 (実行時確定) | ns `...AWGN` |
| `AWGN/AchievabilityDischarge.lean` (1997) | 分割対象 → Phase 3 へ | >1200、ns `...AWGN`、分割時は path-only |
| `AWGN/ConverseDischarge.lean` (1756) | 分割対象 → Phase 3 へ | >1200、ns `...AWGN`、分割時は path-only |
| `ChannelCoding/ShannonTheoremFullDischarge.lean` (70) | `ChannelCoding/` 概念名 (実行時確定) | ns `...ChannelCoding` |
| `GaussianPDFVarianceDerivBody.lean` | 概念名 (実行時確定) | ns `...Shannon` |
| `LZ78/PhraseCountAsymptoticBody.lean` | 概念名 (実行時確定) | ns `...Shannon` |
| `LZ78/ZivCountingBody.lean` | 概念名 (実行時確定) | ns `...Shannon` |
| `WynerZiv/Discharge.lean` (327) | `WynerZiv/RateMonotone` 等 | ns `...Shannon` |
| `WynerZiv/CondEntDiffConvexBody.lean` | 概念名 (実行時確定) | ns `...Shannon` |
| `WynerZiv/ConvexityBody.lean` | 概念名 (実行時確定) | ns `...Shannon` |
| `WynerZiv/ObjectiveConvexityBody.lean` | 概念名 (実行時確定) | ns `...Shannon` |
| `Shannon/RateDistortion/AchievabilityPhaseB.lean` | `AchievabilityJointTypicalEncoder` | joint-typical lossy encoder + distortion typical set。ns `...Shannon` flat |
| `Shannon/RateDistortion/AchievabilityPhaseC.lean` | `AchievabilityCodebookMatchProbability` | codebook-level match probability |
| `Shannon/RateDistortion/AchievabilityPhaseD.lean` | `AchievabilityAsymptoticFailureDecay` | asymptotic decay + distortion decomposition |
| `Draft/Shannon/RateDistortionAchievabilityPhaseE.lean` (0 decl) | **削除 + redirect** → renamed PhaseD | 空 conduit (下記 空スタブ表) |
| `Draft/Shannon/RateDistortionAchievabilityPhaseEDischarge.lean` (270) | `Shannon/RateDistortion/AchievabilityAmbientMeasure` | i.i.d. ambient measure (rdAmbient) + witness discharge。Draft 解消 |
| `Shannon/RateDistortion/AchievabilityPhaseEStrong.lean` | `AchievabilityJointStrongTypicality` | joint strong-typicality apparatus (Strong = 数学概念、判断ログ参照) |
| `Shannon/RateDistortion/AchievabilityPhaseEStrongFinal/Setup.lean` | `AchievabilityStrongTypicality/SupportingBounds` | strong supporting bounds + witness |
| `Shannon/RateDistortion/AchievabilityPhaseEStrongFinal/FailureTendsto.lean` | `AchievabilityStrongTypicality/FailureTendstoZero` | codebook-avg failure → 0 |
| `Shannon/RateDistortion/AchievabilityPhaseEStrongFinal.lean` | `AchievabilityStrongTypicality` (+ dir) | final assembly → `rate_distortion_achievability` |
| `FisherInfo/V2DeBruijnBody.lean` | `FisherInfo/` 概念名 (Body 除去のみ) | ns `...FisherInfoV2`、V2 ns cleanup は Phase 1b |
| `FisherInfo/V2HeatFlowBody.lean` | `FisherInfo/` 概念名 (Body 除去のみ) | 同上 |
| `Hoeffding/SandwichDischarge.lean` (177) | 概念名 (実行時確定) | ns `...HoeffdingSandwichDischarge` → **namespace-also**、Phase 1b へ |

> `Hoeffding/SandwichDischarge` は後段の表で再掲 (ns にプロセス語彙あり)。上表からは除外扱い。

### Phase 1a — 空スタブ削除 (宣言 0 → 改名でなく削除 + importer redirect)

| 現ファイル | sole importer | 処理 |
|---|---|---|
| `RateDistortion/ConvexityDischarge.lean` (0 decl) | `RateDistortion/ConverseNLetter.lean` | transitive imports (`RateDistortion.Convexity`/`Sanov.Basic`/`Mathlib.InformationTheory.KullbackLeibler.KLFun`) を ConverseNLetter に直接追加 → stub 削除 + root 登録削除 |
| `ParallelGaussian/L_PG0Discharge.lean` (0 decl) | `ParallelGaussian/KKT.lean` (既に `ParallelGaussian.Basic` を直 import) | KKT の `import ...L_PG0Discharge` 行を削除 → stub 削除 + root 登録削除 |
| `Draft/Shannon/RateDistortionAchievabilityPhaseE.lean` (0 decl, transitive import 専用 conduit) | importer は改名後 PhaseD へ redirect | importer の `import ...RateDistortionAchievabilityPhaseE` を改名後 PhaseD (`AchievabilityAsymptoticFailureDecay`) へ向け直し → stub 削除 + root 登録削除 + Draft 解消 |

### Phase 1b ターゲット — namespace-also 改名 (ns にプロセス語彙 → decl 参照に波及)

各グループで `scripts/dep_consumers.sh <FQ名> --transitive` を事前実行し blast radius を確定してから移動。
**namespace を共有するグループは同一 commit で全ファイル移動**。

| namespace (変更前) | 対象ファイル群 | 概念名候補 | 注記 |
|---|---|---|---|
| ~~`...Cramer.Discharge`~~ | ~~`Cramer/LC2Discharge.lean`, `Cramer/LC2DischargeExt.lean`~~ | **✅ DONE → `Cramer.TiltedLLN` / `TiltedIID.lean`+`TiltedLLN.lean`** | 共有 ns は実は6ファイルで宣言 (LC2PhaseC/InfinitePiTiltedChangeOfMeasure/MeasurePiTiltedFactorization/CramerBoundaryUpstream も) → 一括 migrate |
| ~~`...EPIStamDischarge`~~ | ~~`EPI/Stam/Discharge.lean`~~ | **✅ DONE → `StamEPIBridge` / `EPIBridge.lean`** | EPI via Stam + de Bruijn (16-consumer hub) |
| ~~`...EPIStamInequalityBody`~~ | ~~`EPI/Stam/InequalityBody.lean`~~ | **✅ DONE → `StamInequality` / `Inequality.lean`** | Stam inequality body (CS/convolution-score path) |
| ~~`...EPIStamStep12Body`~~ | ~~`EPI/Stam/Step12Body.lean`~~ | **✅ DONE → `StamConditionalCauchySchwarz` / `ConditionalCauchySchwarz.lean`** | Step1 score-conv + Step2 conditional CS |
| ~~`...EPIStamStep3Body`~~ | ~~`EPI/Stam/Step3Body.lean`~~ | **✅ DONE → `StamFisherCoupling` / `FisherCoupling.lean`** | Step3 symmetric Fisher coupling |
| ~~`...HoeffdingInteriorGradientBody`~~ | ~~`Hoeffding/InteriorGradientBody.lean`~~ | **✅ DONE → `HoeffdingTilt` / `Tilt.lean`** | tilt object + gradient stationarity |
| ~~`...HoeffdingLagrangeIVTBody`~~ | ~~`Hoeffding/LagrangeIVTBody.lean`~~ | **✅ DONE → `HoeffdingLagrange` / `Lagrange.lean`** | IVT constraint-match + Lagrange hyp 構築 |
| ~~`...HoeffdingSandwichBody`~~ | ~~`Hoeffding/SandwichBody.lean`~~ | **✅ DONE → `HoeffdingBoundaryMinimizer` / `BoundaryMinimizer.lean`** | full-support predicate + boundary discharge |
| ~~`...HoeffdingSandwichDischarge`~~ | ~~`Hoeffding/SandwichDischarge.lean`~~ | **✅ DONE → `HoeffdingMinimizerExistence` / `MinimizerExistence.lean`** | constructive minimizer 存在 + achievability |
| ~~`...HoeffdingInteriorBody`~~ | ~~`Draft/Shannon/HoeffdingInteriorBody.lean`~~ | **✅ DONE → `HoeffdingInteriorMinimizer` / `Hoeffding/InteriorMinimizer.lean`** | interior minimizer + Draft 解消 |
| ~~`...ChannelCodingConverseGeneral`~~ | ~~`Draft/Shannon/ChannelCodingConverseGeneralComplete.lean`, `ChannelCoding/ConverseGeneralStrong.lean`, `ChannelCoding/ConverseMemorylessPure.lean`~~ | **✅ DONE → `ConverseMemorylessChainRule.lean` + `ConverseMemorylessMarkov.lean` + `ConverseMemoryless.lean`** | ns に staging token 無し → **namespace 不変・ファイル改名のみ** (bisection の namespace-also 想定は過大)。Strong は IsMemorylessChannelStrong の二重 Markov 公理 (既存 StrongConverse.lean と混同回避で除去)。Draft/ dir 完全除去 |
| ~~`...ChannelCodingFeedback`~~ | ~~`ChannelCoding/FeedbackComplete.lean`~~ | **✅ DONE → `FeedbackMemoryless.lean`** | ns clean=不変 (ファイル改名のみ)。`Feedback.lean` 衝突回避 + content 命名 (memoryless feedback 変種)。importer は root のみ (依存方向は FeedbackComplete→Feedback、plan の consumer=Feedback.lean は誤り) |
| ~~`...EPIBlachmanGaussianWitness`~~ | ~~`EPI/Blachman/GaussianWitness.lean`~~ | **✅ DONE → `EPIGaussianDensityRoute` / `GaussianDensityRoute.lean`** | Gaussian density-route inhabitant (非空性) |
| ~~`...WhittakerShannonPartial`~~ | ~~`WhittakerShannonPartial.lean`~~ | **✅ DONE → `NormalizedSinc`** | `Partial` は load-bearing (Mathlib にある WS の部分集合のみ; L²直交/Poisson は out-of-scope) ゆえ bare `WhittakerShannon` は over-claim → primary object `sincN` で命名。consumer=root のみ |
| ~~`...FisherInfoV2`~~ | ~~`FisherInfo/V2*.lean` 群 (7本) + `FisherDeBruijnGaussianWitness`~~ | **✅ DONE → ns `FisherInfo` + ファイル `OfDensity`/`DeBruijn`/`DeBruijnGeneral`/`DeBruijnHeatFlow`/`DeBruijnPerTime`/`HeatFlow`/`DeBruijnAssembly`(+dir)/`FisherDeBruijnGaussian`** | **想定より大: ns 宣言13本 + 置換46ファイル/303箇所 + import 39+root**。decl 名の V2 (`fisherInfoOfMeasureV2` 等) は out-of-scope で保存。Witness=禁止語ゆえ同時除去。sorry 107・tag 不変 |

> flat namespace (e.g. `EPIStamDischarge`) はディレクトリ構造由来でなく手書き。変更方針: プロセス語彙 token
> だけを strip して概念名化 (e.g. `EPIStamInequalityBody` → headline を Read して概念名を決定)。
> ディレクトリ由来の階層 (`EPI.Stam`) への折り畳みは decl 名衝突リスクがあるため**行わない**。

### Phase 2 ターゲット — `AWGN/Walls.lean` (3549 行) の概念分割

**R4 verbatim 確認結果 (leg6)**: 当初の 6 セクション境界で分割しようとすると `private` ヘルパーが
セクションを跨ぐ。実測した跨ぎ:
- `map_shear_withDensity`/`lintegral_pi_prod_eq_prod` (AEP @52,80) が PerLetterKL 内 (265,825,1188) で使用
  → **AEP + PerLetterKL は private 結合**。
- `converseJointInline` (@1459) が Integrability/MIChainRule/Markov 全域 (1520〜3443) で、
  `perLetterMixtureDensity` (@1503) が MIChainRule (2863〜3084) で使用
  → **Converse-shared + Integrability + MIChainRule + Markov は `converseJointInline` を中心に private 結合**。

R4 の対処 (a) de-private 化 / (b) private共有群を同一ファイルに保つ のうち、**(b) を採用**
(path-only 不変を完全保持・public API surface 不変・de-private のリスク/命名コスト回避、footprint
「不可分1概念の大ファイル許容」)。よって **clean cut は seam=1308, 1443 の 3 ファイル**:

| 行範囲 | 含むセクション | 分割先 | headline (@[entry_point]) |
|---|---|---|---|
| 44–1307 | Continuous Gaussian AEP + Per-letter/n-fold KL | `AWGN/KLCapacityAndAEP.lean` | `klDiv_perLetter_eq_capacity` / `klDiv_nFold_eq_nsmul` / `continuousAepGaussian_holds` |
| 1308–1442 | Per-codeword power constraint (private-free) | `AWGN/PerCodewordPowerConstraint.lean` | `awgnPowerConstraintPerCodeword_holds` |
| 1443–3549 | Converse-shared + log-density integrability + memoryless MI chain rule + Markov | `AWGN/ConverseMIChainRule.lean` | `awgnPerLetterIntegrability_holds` / `awgnContinuousMIChainRule_holds` / `awgnConverseMarkov_holds` |

`Walls.lean` 自体は消す (薄い re-export も残さない方針 = Mathlib に re-export hub の慣習なし)。
`ConverseMIChainRule` は ~2107 行と大きいが、`converseJointInline` 中心の private 群が**不可分**ゆえ
据え置き (更分割には de-private 化が必要 = 別 Phase 候補)。`import ...AWGN.Walls` を持つ 3 importer
(ConverseDischarge / ContChannelMIDecomp / AchievabilityDischarge) は分割後の必要ファイル群への import に展開。

### Phase 3 ターゲット — 残り 1200+ 行ファイル (Walls 除く 13 本) ✅ 13/13 処理済

13 本すべて処理完了。**構造変更 2 本**: `Stein` (1358) → 3分割 (`Stein/Achievability`/`Stein/Converse`/
`Stein/OptimalExponent`、§境界 seam、Converse に private 8 本集約) (a709a7d) / `GreedyParsingImpl` (2090)
→ `LZ78/AsymptoticOptimality` 改名のみ (§3 が 1680 行不可分モノリス、3 private 結合で分割不可) (13993be)。
**不可分 1 概念として許容 3 本** (NO-OP、概念名済): `ChannelCoding/Achievability/RandomCodebook` (1303、
`block_law_*` private が遠方消費で seam なし) / `ConditionalMethodOfTypes/Mass` (1482、唯一 headline が
2 private を直参照) / `SMB/AlgoetCover/TwoSidedRatio` (1381、深い terminal chain + 散在 private)。
**他 8 本は前 leg で処理済**。

判断基準: Mathlib 中央値 185・最大 1523 は **診断トリガーであって固定キャップでない** (footprint plan と
同じ思想)。private 結合 (R4) で clean seam が無い不可分 1 概念は許容 (進捗指標であって pass/fail ゲート
ではない、§DoD)。

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
   **whitelist (数学概念ゆえ許容、staging でない)**: `StrongTypicality`/`StronglyTypical` (Cover–Thomas
   strong typicality、先例 `Shannon/StrongTypicality.lean`) / `StrongConverse` (strong converse 定理) /
   `StrongStein` (strong Stein の補題) / `StrongForm` (Huffman strong-form) / `FullRateRegion` (Slepian–Wolf
   full rate region — `Full` は領域の数学的形容、staging でない)。bare `Strong`/`Full` grep (Phase 4) は
   これらを除外する (false positive 防止)。これら 8 ファイルは本プランの改名/分割ターゲット表に元から非掲載
   (Phase 4 grep で surface しただけ)。**`EPI/Unconditional/DispatchFull.lean` のみ EPI family の follow-up
   として別途記録** (本プラン scope 外、下記 Phase 4)。
6. **root 登録の整合**: 新ファイルは `InformationTheory.lean` に import 登録、消したファイルは登録削除
   (pre-commit が「新ファイルの import 未登録」を WARN)。

## Phases

### Phase 0 — 測定 + 改名マッピング確定 + pilot ✅

**proof-log: no** (純構造リファクタ)。

1. 改名対象を全列挙し、各ファイルの namespace を確認 (`rg '^namespace'`) して **path-only / namespace-also** に
   二分する (実測 bisection 結果は上記マッピング表に反映済)。namespace-also は実行時に
   `scripts/dep_consumers.sh <FQ名> --transitive` で blast radius を確定。
2. 上記マッピング表の候補概念名を、各ファイルの headline を Read して確定 ([`rules/naming.md`](rules/naming.md))。
3. **pilot**: `AWGN/MIBridgeDischarge.lean` (124 行、path-only) で「git mv → import 行置換 → full build green →
   #print axioms 不変」の手順を較正。**完了** (`MutualInfoBridge` へ改名済)。

**進捗 (2026-06-21)**: bisection 実測完了 (path-only ~25 本、namespace-also ~16 本、空スタブ 2 本)。
pilot `MIBridgeDischarge → MutualInfoBridge` 完了 (手順較正済)。

### Phase 1a — path-only 改名 + 空スタブ削除 🔄

**proof-log: no**。低リスク・機械的。**進捗**: pilot+AWGN 群 / batch2 (WynerZiv·LZ78·Gaussian) /
FisherInfo Body 除去 / ChannelCoding dir 改名 + 空スタブ 2 本 (`ConvexityDischarge`/`L_PG0Discharge`) 削除 完了。
残るは RateDistortion PhaseE family 1 件 (本 leg、これで Phase 1a 完了 → Phase 1b へ)。

- **空スタブ 2 本を削除**: `ConvexityDischarge` + `L_PG0Discharge` (各 0 decl) — 改名でなく
  importer redirect + ファイル削除 + root 登録削除 (上記 Phase 1a 空スタブ表参照)。
- **path-only 改名**: 上記 Phase 1a 表の各ターゲットを `git mv` + import 行置換 + root 登録更新。
  `AchievabilityDischarge`/`ConverseDischarge` (>1200 行) は改名せず Phase 3 (分割と同時に改名)。
- **RateDistortion PhaseE family (Phase 1a 最終ターゲット)**: B→C→D→E→EStrong→EStrongFinal の同一 staging
  ladder を一括改名 (上記 Phase 1a 表)。`PhaseEDischarge` (Draft, 270 行) は `RateDistortion/` へ移設 +
  概念名化、空 conduit `RateDistortionAchievabilityPhaseE` (0 decl) は削除 + importer を改名後 PhaseD へ redirect。
  `StrongTypicality`/`StronglyTypical` の "Strong" は数学概念 (Cover–Thomas strong typicality) ゆえ残す
  (判断ログ・invariant 5 whitelist 参照)。
- disjoint import のものから並列 ≤ 2。各 commit 前に full build (or 局所 `lake build <module>`) green。

### Phase 1b — namespace-also 改名 📋

**proof-log: no**。namespace 変更 → decl 参照に波及 → 事前 dep 確認必須。

- 上記 Phase 1b 表の各グループを順番に処理:
  1. `scripts/dep_consumers.sh <FQ名> --transitive` で blast radius 取得。
  2. namespace を概念名に変更 + 全参照ファイルを追従更新。
  3. 共有 namespace グループ (×3 `ChannelCodingConverseGeneral`、×2 `Cramer.Discharge`) は
     グループ全体を同一 commit で移動 (build が途中で壊れないよう)。
  4. **Draft/ のうち namespace-also 2 本** (`HoeffdingInteriorBody`/`ChannelCodingConverseGeneral 系`) も
     ここで正規サブツリーへ移設 (Draft 解消を兼ねる)。
  5. 各 commit 前に full build green。
- `FisherInfoV2` の `V2` 除去は Phase 1b の最後: `FisherInfo/V2DeBruijnBody`/`V2HeatFlowBody` の
  Body 除去 (Phase 1a で先行) 後、ns `FisherInfoV2` → 概念名に変更。`FisherDeBruijnGaussianWitness` も
  同一 ns を共有するなら同一 commit。

### Phase 2 — `AWGN/Walls.lean` (3549 行) 概念分割 📋

**proof-log: 推奨** (最大の山。分割の継ぎ目判断に余地があり、教訓を残す価値がある)。

- 上記セクション表の 6 概念へ `git mv` 分割。namespace `InformationTheory.Shannon.AWGN` は全分割先で不変
  ゆえ decl FQ 名不変 = consumer 無破壊。
- 最大塊 (`PerLetterKL` 145–1307 / `MemorylessMIChainRule` 1823–3321) が分割後も >1200 なら、その内部の
  サブセクションで更分割 (anti-monolith)。
- `Walls.lean` を削除、4 importer の import 行を分割先群へ展開。full build green。

### Phase 3 — 残り 1200+ 行ファイルの概念分割 ✅

**proof-log: 機会主義的** (大きな分割のみ)。**13/13 完了** (§Phase 3 ターゲット参照): 構造変更 2 本
(Stein 3分割 / GreedyParsingImpl→AsymptoticOptimality 改名) + 不可分 1 概念許容 3 本 + 前 leg 8 本。
全変更 path-only (namespace 不変・decl FQ 名不変・sorry/タグ保存)。`AchievabilityDischarge`/`ConverseDischarge`
は前 leg で分割と同時に `Discharge` 除去済。

### Phase 4 — 最終再実測 + 検証 ✅

**proof-log: no**。本 leg ですべての gate を verify、green:

1. **full `lake build InformationTheory` green** (≈3496 jobs)。
2. **プロセス語彙ファイル名 0 (scope 内)**: grep が surface した 8 ファイル
   (`StrongConverse`/`StrongStein`/`Huffman/StrongForm`/`SlepianWolf/FullRateRegion/*`×4) はいずれも本プラン
   ターゲット表に元から非掲載 + 全て数学概念 → invariant 5 whitelist に追記済 (false positive)。
   `EPI/Unconditional/DispatchFull.lean` ("Full"+"Dispatch") は **EPI family の follow-up として別途記録**
   (本 restructure scope 外、EPI moonshot plan owner、module-restructure residual ではない)。
3. **行数分布再実測** (上位): `ConverseMIChainRule` 2139 / `AsymptoticOptimality` 2090 / `Mass` 1482 /
   `TwoSidedRatio` 1381 / `RandomCodebook` 1303。残 1200+ は全て不可分 1 概念モノリス (進捗指標、§DoD)。
4. **タグ保存**: 本 leg は新規 sorry/@residual 0 (全変更 path-only)。現状 `@residual` 14・`@audit` 545。

## 検証

**per-target (各改名/分割完了時、オーケストレータが確認)**:

- full `lake build InformationTheory` が 0 error (import 波及ゆえ per-file では不十分)。
  ※ 速度のため、波及が局所的な path-only 改名は「対象 + 全 importer の `lake build <module>`」で代替可、
    Phase 末で full build を 1 回。
- 移動した `@[entry_point]` の `#print axioms` が改名前と一致 (invariant 2)。
- 改名なら decl FQ 名不変 / namespace 改名なら `dep_consumers.sh` の全参照が追従済 (invariant 1)。

**final (Phase 4)**: full build green / プロセス語彙ファイル名 0 / タグ総数保存 / 行数分布再実測。

## DoD ✅ MET (2026-06-21)

- **現実的 DoD (pass/fail ゲート) — 充足**: 全プロセス語彙ファイル名 (Discharge/Walls/Draft/Body/task-code 等)
  数学概念名化済 + Draft/ 解消済 + `Walls.lean` 分割済 + 6 Hard invariant 充足 + full build green(≈3496) +
  タグ保存 (新規 sorry/@residual 0、`@residual` 14・`@audit` 545)。
- **進捗指標 (pass/fail ゲートではない)**: 1200 行超の残留は全て不可分 1 概念モノリス (許容、footprint plan と
  同思想)。max は 2139 (`ConverseMIChainRule`、private 結合不可分)。
- proof done (0 sorry / 0 residual) は**本パスの DoD ではない**: 純構造リファクタゆえ sorry 数不変。honesty
  audit は**不要** (新規 sorry/@residual を導入しないため、タグ数保存で代替検証)。
- **残 build-neutral 整合 follow-up (DoD ゲート外、低優先)**: 4 AWGN `.lean` ファイル
  (`AWGN/Achievability`/`AWGN/ConverseMIChainRule`/`AWGN/KLCapacityAndAEP`/`GeneralDMC/Basic`) の docstring 散文に
  前 leg (r6/r7) 改名前の名 (`AchievabilityDischarge`/`AWGNConverseDischarge`/`Walls`) が残存。file-path ref
  (更新可) と namespace-qualified decl ref (保存必須) が混在するため一括置換不可、prose-consistency の手作業
  follow-up として記録。build は green ゆえ DoD ゲートに含めない。

## Risks & mitigations

- **R1: namespace-also 改名で decl 参照が壊れる** (実測 ~16 本、うち共有 ns グループあり)。→ 改名前に
  `scripts/dep_consumers.sh <FQ名> --transitive` で全参照を確定、namespace + 参照を同一 commit で追従更新。
  共有 ns グループ (×3 `ChannelCodingConverseGeneral`、×2 `Cramer.Discharge`) は全ファイルを同一 commit。
  迷ったら **namespace は据え置き path のみ改名** (低リスク優先) → Phase 1b 後回し。
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

1. **2026-06-21 完了 — DoD MET**: Phase 0–4 全 green。Phase 3 が最終 leg で 13/13 処理完了 (構造変更 2 本 =
   Stein 3分割 + GreedyParsingImpl→AsymptoticOptimality 改名; 不可分 1 概念許容 3 本 = RandomCodebook/Mass/
   TwoSidedRatio; 他 8 本前 leg)。Phase 4 gate green: full build(≈3496) / プロセス語彙ファイル名 0 (scope 内、
   grep の 8 surface は数学概念 whitelist 化済) / タグ保存 (新規 sorry/@residual 0) / 行数分布再実測 (max 2139)。
   `EPI/Unconditional/DispatchFull.lean` は EPI family follow-up (scope 外) として記録。残 build-neutral follow-up =
   4 AWGN ファイルの旧名 docstring 散文 (DoD ゲート外、§DoD)。

   **設計の要点 (完了時に固定)**: namespace ディレクトリ由来 → 改名は import 行のみ波及 (ライブラリ名 rename の
   552 波及とは桁違いに小) ゆえ path-only / namespace-also の二分でリスク管理。実測 bisection で namespace-also は
   ~16 本 (当初「2 本」見積を 3 倍化)、flat 手書き namespace は token strip のみ (directory 形折り畳みなし)、空スタブ
   2 本は削除+redirect。`StrongTypicality`/`StrongConverse`/`StrongStein`/`StrongForm`/`FullRateRegion` は数学概念
   ゆえ invariant 5 whitelist (詳細は invariant 5 / Phase 4)。Copyright ヘッダは upstream まで保留 (本パス対象外)。
