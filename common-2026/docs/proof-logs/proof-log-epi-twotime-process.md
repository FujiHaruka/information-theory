# EPI two-time restructure セッション — プロセス・ボトルネック分析

将来 orchestrator の dispatch ループ / honesty 監査を自動化・前倒しするための一次記録。
このログは **証明の中身ではなくセッションの進め方** に焦点を当てる（補題の有無ではなく、
補題・正直形を「発見できたか / 詰まったときどうしたか」のプロセス）。技術的中身は
`docs/shannon/proof-log-epi-case1-genvar-struct.md` §Two-time に既出。

**定量データ**: [docs/metrics/epi-twotime-process.metrics.md](../metrics/epi-twotime-process.metrics.md)

## 0. 対象セッションと到達点

1 セッションで EPI case-1 two-time restructure を Phase 1〜3 entry gate まで進めた:

- Phase 1 formulation gate PASS（`ProbeF1.lean` scratch、逆関数微分 glue を機械検証、hard wall ゼロ）
- Phase 2 skeleton（`EPICase1TwoTime.lean`、9 decls、0 errors、9 sorry+@residual）
- Phase 3 entry gate CLOSED（`_hasDerivAt` の `J_S` pin defect を直接埋込で構造解消、3-pass 監査 PASS）
- `matchedSum_law_eq` genuine closure（sorry 除去）

オーケストレーション構成: orchestrator（本体）+ `lean-implementer` ×4 + `honesty-auditor` ×3。
worktree なし（単独 dispatch）。

## 1. このセッションの工程プロファイル

支配項は **Mathlib 補題探索ではなく「正直形 (honest shape) の適用」だった**。必要だった
Mathlib 補題（`gaussianReal_map_const_mul` / `gaussianReal_add_gaussianReal_of_indepFun` 等）は
直前の W-law probe（genvar-struct §Two-time Item 1）で既に在庫済で、本セッションでは再利用のみ。
grep 空振り・Mathlib 壁との格闘はゼロ。

代わりに時間を食ったのは **`implementer → auditor → defect → 修正` のループを 3 周** したこと。
詰まりの正体は「どう証明するか」ではなく「false-as-framed にならない signature をどう組むか」。
過去ログ（fano / shannon-converse 等）が「Mathlib 部品呼出 / 数え上げ書下し」型だったのに対し、
本セッションは **honesty 制約駆動** 型。ツール開発の含意がまったく違う（§6）。

## 2. オーケストレーションの流れ（実録）

タイムラインは metrics 元データから再構成（時刻は metrics.md 参照、ここでは順序のみ）:

1. **formulation gate を skeleton 投資前に置いた** — orchestrator 自身が `ProbeF1.lean` を書き、
   最も誤りが隠れやすい逆関数微分 glue だけ isolate して機械検証 → GO 確認後に scratch 削除。
   plumbing 前に最大 risk を gate する GS-A3' 教訓の適用。**これは効いた**（§5）。
2. `lean-implementer` → Phase 2 skeleton（9 decls）
3. `honesty-auditor`（1-pass）→ `_hasDerivAt` の `J_S/J_X/J_Y` 全 free で **universally false** を検出
4. `lean-implementer` → fix-1（X/Y を `reg_at` density に pin、`J_S` は `withDensity` a.e.-pin）
5. `honesty-auditor`（2-pass）→ **`J_S` の a.e.-pin が不十分**（`fisherInfoOfDensityReal` は
   `logDeriv` を pointwise に取るため representative-dependent、a.e. 等価な non-diff representative で
   `J_S=0` に落とせる）を検出 → tier-5 `@audit:defect(false-statement)` 残置を orchestrator が直接 edit
6. orchestrator が **解消 lead を plan/handoff に書込み**（matched sum = `X+Y` の単一-noise heat-flow
   at τ → 既存 `IsDeBruijnRegularityHyp` を τ 評価して `J_S` を結論に直接埋込）
7. `lean-implementer` → Phase 3-0a 直接埋込 rewrite
8. `honesty-auditor`（3-pass）→ escape 消滅を確認、**defect 構造解消 PASS**
9. `lean-implementer` → `matchedSum_law_eq` genuine closure

## 3. 補題・正直形の「探索」実録

このセッションは Mathlib 補題探索が支配項ではないので、表は薄い。重要なのは「無かったもの」より
**「在ったのに最初に適用されなかったもの」**:

| 必要だったもの | どこに在ったか | プロセス上の扱い |
|---|---|---|
| Fisher-info を honest に持つ導関数 lemma の **正直形** | in-tree sibling `csiszarLogRatioGap_hasDerivAt`（`EPIStamToBridge.lean:744-883`、single-t 版）が **結論に直接埋込** で実装済 | **cycle 1/2 の brief に「sibling の埋込形をミラーせよ」が無く**、free-var → a.e.-pin → cycle 3 でようやく直接埋込。在庫済の正直形に 2 周遅れて到達 |
| `matchedSum_law_eq` の Mathlib 部品 | `gaussianReal_map_const_mul` / `gaussianReal_add_gaussianReal_of_indepFun` | 直前 W-law probe で在庫済 → 再利用、新規探索ゼロ ✅ |
| formulation gate の asset（`of_local_left_inverse` / `strictMonoOn_of_deriv_pos` / `intermediate_value_Ici` 等） | loogle + rg で name-confirm（gate 内） | 探索成功、hard wall ゼロ ✅ |

**Mathlib に無かった補題**: 本セッションでは新規には発生せず（探索はすべて在庫 hit）。

## 4. プロセス・ボトルネック（状況→原因→抜け方→教訓）

### 4.1 正直形が in-tree sibling に在ったのに brief が front-load しなかった（中核）

**状況**: `_hasDerivAt` の skeleton と fix-1 が Fisher info を free 変数 + 仮説 pin で渡し、監査に
2 連続で defect 判定された。

**原因**: honest な実装パターン（Fisher info を free 変数にせず結論に直接埋込み、
`density_t_eq` の pointwise-smooth pin に escape を消させる）は single-t 版 sibling で **既に確立済**。
だが skeleton / fix-1 の brief に「sibling `csiszarLogRatioGap_hasDerivAt:744-883` の埋込形を
ミラーせよ。free-var + a.e.-pin は false-as-framed になる」という **hard 制約が入っていなかった**。
implementer は素直に textbook 形（J を変数で受けて仮説で縛る）を組み、a.e.-pin で「縛ったつもり」になった。

**抜け方**: 2-pass 監査が J_S の不十分を 1 変数に局在化 → orchestrator が rushed 4 回目を避けて
第二選択 marked-defect で一旦 honest 残置 → heat-flow at τ の lead を確定させてから直接埋込で再 dispatch。

**教訓**: CLAUDE.md「Mathlib-shape-driven Definitions」「Brief content checklist」の Fisher-info 版。
**Fisher info / Radon-Nikodym 由来の representative-dependent 量を結論に持つ lemma を実装させるときは、
brief に (a) 既存 honest sibling の file:line、(b)「free 変数で受けず結論に直接埋込」、
(c)「a.e.-pin は不十分、pointwise-smooth pin (`density_t_eq` 経由) のみ honest」を明記する**。
これがあれば cycle 1/2 は不要だった（2 周ぶんの implementer+auditor 往復が削れた）。

### 4.2 honesty 監査は「1-pass では subtle defect を取りこぼす」

**状況**: fix-1（X/Y pin + J_S a.e.-pin）に対し、最初の監査観点では X/Y pin が PASS 判定され得た。
J_S の不十分は **2-pass 目** で初めて局在した。

**原因**: representative-dependent（a.e. 等価な non-diff representative で値が変わる）型の defect は、
「pin されているか」を表面的に見ると見逃す。実際に skeptic が `J_S=0` を構成できるかまで
踏み込まないと false-as-framed と判定できない。

**抜け方**: fresh auditor を fix ごとに起動し直し（self-audit 不可の原則）、再 dispatch で 2-pass 化。

**教訓**: honesty-auditor に **representative-dependence チェックリストを内蔵** すべき
（「この量は a.e. 等式で縛れるか? pointwise 必須か?」「skeptic は退化 representative を構成できるか?」）。
監査は早期検出のセーフティネットとして機能したが **reactive**。`@residual` を持つ各変数について
「pin の強度（a.e. / pointwise）と量の representative-sensitivity」を 1 表で出させれば 1-pass で局在できる。

### 4.3 genuine closure の verdict に `#print axioms` 裏取りが無い

**状況**: `matchedSum_law_eq` を「genuine closure (sorryAx-free)」と commit。

**原因**: orchestrator 側の検証は `lake env lean`（0 errors / sorry warning 無し）+ implementer 自己申告。
`#print axioms matchedSum_law_eq` は走っていない（metrics の Bash 内訳: `lake_env_lean` 1、`#print` 0）。

**抜け方**: （未実施。0-sorry warning で代替したが、CLAUDE.md「最終判定は必ず `lake env lean` +
`#print axioms` で裏取り」を満たしていない）。

**教訓**: **genuine closure（proof-done 増分を主張する commit）には `#print axioms` を必須化** する。
sorry warning の不在は sorryAx を捕まえるが、依存先 sorry / 別経路の axiom 混入を保証しない。
proof-done を集計対象にする以上、verdict の機械裏取りは sorry 残置時より厳しくすべき。

### 4.4 委譲すると orchestrator-side metrics が実作業を取りこぼす

**状況**: metrics.md の「対象ファイル Edit 回数 = 2」は orchestrator が直接打った defect-marking
edit のみ。genuine な実装 edit は subagent transcript 側にあり「サブエージェント側 entries = 0」。

**原因**: `session_metrics.ts` は orchestrator セッションの JSONL を読む。dispatch した
implementer/auditor の作業量・lake 実行回数・試行錯誤は別 transcript で、ベースラインに入らない。

**教訓**: proof-log のベースライン目的（自動証明支援ツールの計測）に対し、**委譲比率が高いセッションは
定量が過小評価される**。subagent transcript も discover 対象に含めるか、dispatch 時の brief/結果を
orchestrator 側に echo させる運用が要る。本セッションは「見かけ Edit 2」だが実体は 4 implementer 分。

## 5. ボトルネックではなかったもの

- **数学的アイデア / 解析核** — two-time の arith core は前セッションで gate PASS 済（harmonic Stam）。
  本セッションは plumbing と honesty が主で、新しい数学的詰まりはゼロ。
- **Mathlib 補題探索** — 必要部品は全て在庫 hit（W-law probe / formulation gate で先行調査済）。
  「無いものを無いと判断する」コストも発生せず。
- **risk-ordering 判断** — formulation gate を skeleton 前に置く判断は迷い無し（GS-A3' 教訓が効いている）。
  cheap scratch で最大 risk を先に潰す型は **再現性のある orchestration パターン**。
- **撤退判断** — 2-pass defect 後、4 回目 rushed patch を回避して marked-defect 残置 → lead 確定 → 再構築、
  の判断は速かった。「詰まったら honest に sorry/defect で残す」撤退口が機能。

## 6. ツール / 運用への示唆

| 優先度 | 施策 | 節約できたであろうコスト |
|---|---|---|
| 高 | **brief への honest-sibling front-load**（Fisher/RN 等 representative-dependent 量を持つ lemma 実装時、既存 honest 版の file:line + 「直接埋込・a.e.-pin 禁止」を必須記載） | implementer+auditor 往復 2 周（cycle 1/2）。再発頻度高（single-t→two-time 等の構造移植で毎回） |
| 高 | **honesty-auditor に representative-dependence チェックリスト内蔵**（各 `@residual` 変数の pin 強度 × 量の representative-sensitivity を 1 表出力） | 1-pass で defect 局在 → 2-pass 監査の往復 1 周 |
| 中 | **genuine closure commit に `#print axioms` 必須ゲート**（proof-done 主張時のみ） | verdict の機械裏取り漏れ。コストでなく信頼性 |
| 中 | **subagent transcript を metrics discover 対象に**（委譲比率の高い session の過小評価是正） | 定量ベースラインの精度 |
| 低 | formulation gate scratch（ProbeF1 型）の **テンプレ化** | gate 立上げの定型化。既に習慣化済なので利得は小 |

## 7. 補足

- 在庫済だった正直形 sibling: `EPIStamToBridge.lean:744-883`
  `csiszarLogRatioGap_hasDerivAt`（`set J_X := fisherInfoOfDensityReal ((h_reg_X.reg_at t ht).density_t)`
  で **free 変数を作らず結論に直接埋込** — これが honest pattern の手本）。
- defect の技術的詳細・iteration 3 cycle・heat-flow at τ lead は
  `docs/shannon/proof-log-epi-case1-genvar-struct.md` §Two-time Phase 2 honesty audit に既出。
- 監査ループの dispatch 順序・時刻は metrics 元データ（session `1479c259`）から再構成。
