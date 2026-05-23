# Defect cleanup — 101 defect の戦略整理 (設計)

ステータス: **設計確定・未実行（波0 から開始可）**

入力: `docs/audit/honesty-audit-report.md` の defect 101 件、`docs/audit/honesty.db` の `audit` テーブル。
出力: 波 0/1/2 を経て `list --status defect` が 0 になる（多くは honest-rebrand で suspect 列に合流、一部 retract、一部 actually-fix）。

## Context / 目的

honesty audit で **defect 101 件**が確定（`2480 ok / 361 suspect / 101 defect`、commit `4dd21be`）。defect は CLAUDE.md「検証の誠実性」標準B 違反 — `0 sorry` で機械検証は通るが、循環 / vacuous / name laundering 等で意味的に何も保証していないもの。

個別に順番に潰すのは非効率。defect は cross-cutting root を共有する **cluster** として現れ、根を 1 つ直すと 6-12 件まとめて消える（report §"Cross-cutting root causes" の 4 root がその実例）。誰からも参照されていない **leaf** も多く、バケツ議論を待たず即削除できる。

→ **「個別に潰す」前に「束 × 影響度」で再分類してから波で処理する**。

## Approach（全体の形）

**3 バケツ × 3 軸タグ × 3 波** で進める。

- **バケツ**（修正方針の選択肢）: (1) retract / (2) honest-rebrand / (3) actually-fix
- **タグ軸**（決定を変える次元）: `refs`（参照数）・`cluster_id`（root 帰属）・`dag_position`（terminal/helper）
- **波**（実行スケジュール）: 波0 タグ付け → 波1 cluster 一括 → 波2 残り (isolated) bucket sweep

タグはバケツ判定の入力。axes を埋めれば、ref=0 → 削除 / cluster の root → 連鎖 / terminal → 優先 / helper → 後回し、と機械的に振り分けられる。**Mathlib 壁距離は事前タグに含めない** — 実際に (3) actually-fix を試みる段階で都度判定すれば足りる（過剰計測を避ける）。

現実的な goal は **defect 101 → 0 / suspect 361 → ~450 / project は標準B-with-documented-residuals のまま**。Mathlib 壁の向こうにある定理を全部 green にするのは狙わない。

## バケツ（修正方針）

| バケツ | 内容 | 主対象 |
|---|---|---|
| **(1) retract** | 述語 / 定理を削除、または subtree ごと scope 撤退 | leaf defect、Whittaker-Shannon のように Mathlib に本物の API が無く長期 staged にする領域 |
| **(2) honest-rebrand** | 仮説を openly named load-bearing hyp として表出、docstring で load-bearing 明示、必要なら `_discharged` 接尾辞を外す。**defect → suspect** に flip | true_residual 11、load_bearing_hyp defect 12、`Prop := True` placeholder の大半 |
| **(3) actually-fix** | 数学的内容を増やさず alias / identity を解消するだけで直るもの | name_laundering 5 の AWGN swap、MAC averaging alias chain |

## タグ軸

### `refs`（必須）
`short_name` を `Common2026/` から rg、定義ファイル自身を除外した cross-file 出現数。
- `refs = 0` → **leaf**（即削除候補、バケツ議論不要）
- `refs ≥ 1` → 参照先一覧から `cluster_id` を割り当て

### `cluster_id`（強推奨）
defect が依拠する root definition / 共通親述語の fqn。**既知 4 cluster**（report §"Cross-cutting root causes"）:

- **`Prop_True_passthrough`**: `IsZivInequalityPassthrough` / `IsLZ78ConversePassthrough` / `IsSMBSandwichPassthrough` / `IsStamScoreConvolution` / `IsDeBruijnIntegrationHypothesis` / `IsStamInequalityHypothesis` を root とする群
- **`WhittakerShannon_placeholder`**: `IsBandlimitedFull` / `IsBandlimitedSamplingHypothesis` / `IsWhittakerShannonInterpolation` / `IsBandlimitedKernel` 系
- **`MAC_alias_chain`**: `MACAchievableWithError ≡ IsMACRandomCodebookMarkov ≡ MACInnerBoundExistence` の alias 群
- **`AWGN_midecomp_swap`**: `IsAwgnMIDecomp` ≈ 別述語のすり替え群

長尾 cluster は波0 で発見する（同一ファイル内多発・同 root への参照集中）。cluster に属さないものは `isolated` タグ。

### `dag_position`（推奨）
- **terminal**: `Common2026.lean` の import 端、または `docs/textbook-roadmap.md` の章末 capstone（`shannon_coding_theorem` / `awgn_converse` / `brunn_minkowski_*` 等）
- **helper**: 中間 discharge body / 補助補題

terminal は外向き信頼度を直撃するので同 bucket 内で優先処理。helper は honest-rebrand で suspect 化しても影響小。

## 決定マトリクス（バケツ × refs）— 概念図

**この表は rationale / cost 直観の図。実行用 SSOT は `defect-cleanup-worker-prompts.md` §W0-S5 の verdict × refs 表**（mechanical rule）。`mid` を含む 4 段 (`leaf=0 / local 1-4 / mid 5-14 / hub ≥15`、`NULL → hub` 扱い) は worker prompt 側で定義。

|                | **leaf** (refs=0)     | **local** (1-4)         | **mid** (5-14)          | **hub** (≥15)                |
|---|---|---|---|---|
| **(1) retract** | **削除一択**          | クラスタごと削除         | クラスタごと削除          | subtree ごと scope 撤退、`Common2026.lean` から import 削除 |
| **(2) honest-rebrand** | 削除で十分 (rebrand 不要) | rename + doc 一括    | rename + doc 一括       | rename → 全 caller cascade、コスト高 — hub の honest-rebrand は実質 retract に倒す方が安い |
| **(3) actually-fix** | 安価 (identity 解消)  | 安価                    | 安価                    | 安価 (cascade しない)         |

`dag_position=terminal` は同 cell 内で優先 / `retract` 上書き禁止 (worker prompt の override 参照)。

## データモデル（audit テーブル拡張）

`audit` テーブルに以下カラムを追加（既存スキーマ非破壊・nullable）:

| カラム | 型 | 内容 |
|---|---|---|
| `refs` | int | cross-file 参照数（波0 で測定） |
| `cluster_id` | text | 所属 cluster 名（波0 でタグ付け、未割当は `isolated`） |
| `dag_position` | text | `terminal` / `helper`（波0 でタグ付け） |
| `bucket` | text | `retract` / `honest-rebrand` / `actually-fix`（波0 終了時に確定） |

defect 行のみ埋まれば良い（suspect / ok 行は null のままで可）。DB は gitignored、`build` で再生成可（既存決定#1）。

## ツール（`scripts/audit_db.ts` 拡張）

スキーマ拡張（`audit` テーブルに非破壊で追加）:

```sql
ALTER TABLE audit ADD COLUMN refs INTEGER;
ALTER TABLE audit ADD COLUMN cluster_id TEXT;
ALTER TABLE audit ADD COLUMN dag_position TEXT;
ALTER TABLE audit ADD COLUMN bucket TEXT;
```

新サブコマンド:

```
refs-bulk [--status defect]                 # 全 defect の refs を測り audit.refs に書く
tag --id <ID> [--cluster X] [--dag terminal|helper] [--bucket retract|honest-rebrand|actually-fix]
tag-bulk --ids ID1,ID2,... [--cluster X] [--dag ...] [--bucket ...]
list --status defect [--order-by refs|cluster_id|...] [--cluster X] [--bucket B] [--dag D] [--refs-max N] [--refs-min N]
```

`list` は既存出力 (id, file:line, verdict, note) に `refs, cluster_id, dag_position, bucket` カラムを追記。

**`refs` 測定方法**: `rg -w -c <short_name> Common2026 --type lean` から定義ファイル自身の出現件数を差し引く。

- short_name 衝突（同名が複数 namespace に存在）対応: `refs-bulk` 内で (a) まず単純 short_name 計数、(b) `theorems.fqn` で `short_name` が複数行に hit したら module-tail (`Foo.bar` 形式) で qualifier 付き再 grep、(c) それでも曖昧なら `refs=NULL` + 警告。**NULL は W0-S5 で hub 扱い (保守的)**。common name (`Inner` / `map` / `id` 等) は数十件オーダーで衝突しうるので NULL 件数は実測してから次工程に進む。
- 自ファイル除外: `--glob '!{module_path}'`。

## 実行体制

### モデル割当（既定）

| 作業性質 | モデル | 理由 |
|---|---|---|
| refs 測定 / DB 書き込み / leaf 削除 / import 整理 / `lake env lean` 検証 | **Sonnet** | 機械作業、判断ゼロ。並列スループット優先 |
| cluster 発見 / dag terminal 抽出 / bucket 確定 / retract / actually-fix の alias 解消 | **Sonnet** | 読解中心、ルール明文化済み |
| **honest-rebrand 文言**（named load-bearing hyp 書き換え + docstring）| **Opus** | 「仮説型 ≠ 結論型」「load-bearing 明示」を再生産しない判断要 |
| **circular / degenerate_def 判定**（波2）| **Opus** | 結論真偽 / 述語強化の妥当性、誤ると新 defect を産む |

ざっくり比率: Sonnet 7-8 割 / Opus 2-3 割。

### 並列度

- **同時起動 5 cap**。波1 cluster batch も波2 sweep も 5 並列まで、完了したら次バッチを launch。
- mutating work（削除 / 書き換え）は CLAUDE.md「Parallel orchestration」boilerplate に従い **worktree + `.lake` symlink reuse**。`feat/...` ブランチ作成禁止、起動 worktree branch に居続け。
- read-only work（cluster 発見 / terminal 抽出 / bucket 確定）は worktree 不要、main で `general-purpose` subagent。
- **`Common2026.lean` 編集は orchestrator が直列で行う**。複数 worktree が同時に root import file を編集するとマージで必ず衝突するため、subagent には「`Common2026.lean` を触らない、削除/移動した module path をレポートで返す」と指示。orchestrator が全 worker の戻り値を集約してから import 整理 commit を 1 本入れる（決定#4 と整合）。

### Orchestrator の責務（read/judge しない）

- **する**: `audit_db.ts` のサブコマンド実行（tag / list / verdict flip / refs-bulk）、subagent の verbatim dispatch、worktree 起動・マージ、`lake env lean` の最終 silent 確認。
- **しない**: `Common2026/` 配下の `.lean` 本体 / `docs/audit/honesty-audit-report.md` 本文 / proof body の Read。Cluster 命名・bucket 判定・rebrand 文言は全部 subagent 内で確定。判定の根拠は subagent の note に書かせる。
- DB 操作（テーブル更新・bulk tag）は本体読みではないので orchestrator が直接実行 OK。

→ `feedback_orchestrator_never_reads_files` の踏襲。

## 波構造

### 波0 — 仕分け（タグ付け、~4-8h）

**step は厳密に逐次** (S0→S1→S1.5→S2→S3→S4→S5→S6)。S2 と S3 の並列化は cluster_id の上書き競合を起こす — S2 完了 (= 既知 4 cluster の tag 書き込み終了) を確認してから S3 を launch する。

| step | precondition | owner | 並列 | input | output / 完了基準 |
|---|---|---|---|---|---|
| **W0-S0** `audit_db.ts` 拡張（ALTER + 新サブコマンド refs-bulk / tag / tag-bulk / list 拡張） | — | Sonnet 1 | — | 上記スペック | 単体実行で stderr エラー無し |
| **W0-S1** `refs-bulk --status defect` 実行 + 分布出力 | S0 完 | Sonnet 1（or orchestrator 直接） | — | 既定 DB | 101 行に `refs` 充填、`{0, 1-4, 5-14, ≥15, NULL}` のヒスト出力 (NULL 件数も明示) |
| **W0-S1.5** bucket threshold 確定 | S1 完 | orchestrator → user 1-line approve | — | S1 ヒスト | `leaf=0 / local≤4 / mid≤14 / hub≥15 / NULL→hub` を W0-S5 prompt に埋め込む |
| **W0-S2** 既知 4 cluster の cluster_id 書き戻し | S1 完 | Sonnet 1 | — | `honesty-audit-report.md §"Cross-cutting root causes"` | `Prop_True_passthrough` / `WhittakerShannon_placeholder` / `MAC_alias_chain` / `AWGN_midecomp_swap` の caller 全件に `tag --cluster X` |
| **W0-S3** 長尾 cluster 発見 + 残り全件への cluster_id 付与 | **S2 完 (cluster_id 衝突防止のため必須)** | Sonnet 1（**並列化しない**＝命名一貫性確保） | — | `list --status defect --cluster NULL` | 全 defect に cluster_id（残りは `isolated`）。新 cluster 名は短い snake_case fqn ベース、既知 4 名と substring overlap 禁止 |
| **W0-S4** dag_position terminal 抽出 + bulk tag | S3 完 | Sonnet 1 | — | `Common2026.lean` import 端 + `docs/textbook-roadmap.md` 章末 capstone | terminal 該当 fqn を `tag --dag terminal`、残りは default helper（明示 tag 不要、`list` 側で NULL → helper 解釈） |
| **W0-S5** bucket 確定 | S4 完 | Sonnet 1 | — | 全 defect の `(refs, cluster_id, dag_position, category)` + worker-prompts §W0-S5 mechanical rule + S1.5 threshold | 全 defect に `bucket` |
| **W0-S6** leaf 即削除（`bucket=retract & refs=0`）| S5 完 | Sonnet 並列 3-5（worktree） | 最大 5 | 該当 id リストを K 分割、**`module` 重複は同一 worker に集約** | 該当 `.lean` 削除 or 該当 decl 削除、`Common2026.lean` import 整理、`verdict --status skip`、`lake env lean Common2026/<touched>.lean` silent |

deliverable: `list --status defect` の全行に `(refs, cluster_id, dag_position, bucket)` が埋まっている。leaf 削除済み（defect 列が一段減る）。

### 波1 — cluster 一括処理（最大レバレッジ）

cluster ごとに 1 worktree、**同時 5 cluster** を launch（完了したら次 5 つ）。

**Launch 前の orchestrator 直列前処理 (file-disjointness check)**: cluster ≠ file。同一 `.lean` モジュールに異 cluster の defect が同居するケースは複数 worktree が同じ file を書き換えて merge 衝突する。orchestrator は launch 候補 5 cluster 各々について `list --cluster <X>` で `module` 集合を取得し、5 集合の和集合内に重複モジュールがあれば: (a) 該当 cluster 群を同一 worker に統合、(b) または別バッチに分離、いずれかで衝突を 0 にしてから launch。

| cluster の bucket | model | 1 cluster あたり作業 |
|---|---|---|
| **retract** | Sonnet (worktree) | root def + caller を一括削除、`Common2026.lean` から import 外す、verdict=`skip` |
| **honest-rebrand** | **Opus** (worktree) | root def を named load-bearing hyp に書き換え（型 ≠ 結論を確保）、caller docstring 一括更新（"load-bearing / NOT a discharge" 明示）、verdict=`suspect` に flip。weaker honest precondition が無い row は worker prompt の Override パスで `bucket=retract` に flip して当該 worktree 内で retract 実行 (DB op 完結) |
| **actually-fix** | Sonnet (worktree) | alias 解消 / identity 書き換え、verdict=`ok` に flip |

共通完了基準: 各 worktree で `lake env lean <touched>` silent → main にマージ → main 側で再度 `lake env lean` 確認（worktree の olean は main で無効化されうるため）。

report の 4 root（passthrough / Whittaker-Shannon / MAC alias / AWGN swap）はここで一掃される見込み（推定 50-70 defect collapse）。長尾 cluster は W0-S3 で発見した数による。

### 波2 — 残り (isolated) sweep — bucket-driven dispatch

bucket は W0-S5 で既に確定済み。category は dispatch ロジックを駆動しない (= bucket がする)。よって波2 は **`cluster_id=isolated` の残り defect 全件を bucket に応じて W1-{retract,rebrand,fix} prompt の再利用** で sweep する。

- `list --status defect --cluster isolated --bucket retract` → W1-retract prompt (Sonnet, worktree) — "## Your cluster" を "## Your isolated sweep batch" に置換
- `list --status defect --cluster isolated --bucket honest-rebrand` → W1-rebrand prompt (**Opus**, worktree) — 同
- `list --status defect --cluster isolated --bucket actually-fix` → W1-fix prompt (Sonnet, worktree) — 同

並列度・worktree・file-disjointness check は波1 と同じ。category 情報は dispatch ではなく worker 内 reasoning hint としてのみ note 経由で渡る (W0-S5 mechanical 表が category 経由で bucket を決定済)。

## 停止条件

- **波0**: `list --status defect` の全行が tag 済み、leaf 削除済み
- **波1**: 既知 cluster 全件処理済み（`list --status defect --cluster <id>` が空）
- **波2**: `list --status defect` が 0、`Common2026.lean` から削除した import が反映済み、`lake env lean Common2026/<touched>` が silent

最終状態: defect 101 → 0、suspect 361 → ~450、project は標準B-with-documented-residuals のまま。

## 決定事項

1. **Mathlib 壁距離は事前タグに含めない**。実際に (3) actually-fix を試みる段階で都度判定（過剰計測を避ける）。
2. **roadmap relevance / honesty severity も事前タグに含めない**。`dag_position` が roadmap relevance の粗代理、defect category が honesty severity の代理、で実用十分。
3. **波0 で ref=0 を即削除**。バケツ議論を待たず、leaf は無条件削除（defect であれ helper であれ、誰も使ってないなら残す理由が無い）。
4. **`Common2026.lean` の import 削除は専用 commit に分ける**。scope 撤退の境界が git log で見えるように。
5. **タグは audit テーブルに persist**。セッションをまたいで継続作業できる（DB は gitignored だが手元には残る、決定#1 と整合）。
6. **goal は "defect=0 かつ標準B-with-residuals"**。「全部 green」は狙わない — Mathlib 壁の向こうにある定理は honest-rebrand で suspect 列に流す。
7. **同時 subagent 起動は 5 cap**。波1 cluster batch / 波2 sweep / 波0 leaf 削除いずれも、完了したら次バッチを launch する逐次バッチ運用。
8. **orchestrator は `.lean` / `report.md` 本体を Read しない**。判定は全部 subagent 内、orchestrator は DB 操作・dispatch・最終 `lake env lean` 確認のみ（`feedback_orchestrator_never_reads_files` 踏襲）。
9. **モデル既定: Sonnet 7-8 割 / Opus 2-3 割**。honest-rebrand と circular/degenerate_def 判定のみ Opus（honesty defect の再生産を避けるため）、それ以外は Sonnet。
10. **worker prompt は別ファイル**（`docs/audit/defect-cleanup-worker-prompts.md`）に verbatim 化し、orchestrator は `<...>` だけ置換して dispatch する（audit phase の `worker-prompts.md` パターン踏襲）。

## 波後の残り residuals → Tier-3 discharge plans

波0/1/2 + 後続 retract/rebrand 後、残 residuals は **3 つの discharge 案件** に集約された (declaration count は変動するが「案件」は安定):

| 案件 | 当該 declaration の grep query | discharge plan |
|---|---|---|
| **AWGN F-1 typicality** | `rg "@audit:defer\(awgn-achievability-typicality\)" Common2026/` | [`awgn-achievability-typicality-plan.md`](../shannon/awgn-achievability-typicality-plan.md) (Cover-Thomas 9.2) |
| **BM from EPI** | `rg "@audit:defer\(brunn-minkowski-from-epi-discharge\)" Common2026/` | [`brunn-minkowski-from-epi-discharge-plan.md`](../shannon/brunn-minkowski-from-epi-discharge-plan.md) (Cover-Thomas 17.7.4) |
| **PG legacy retract** | `rg "@audit:defer\(pg-legacy-retract\)" Common2026/` | (handoff の Next step #1) — `parallel_gaussian_capacity_formula_of_perCoordReduction` 系 4 件を honest 経路 `ParallelGaussianPerCoord.parallel_gaussian_capacity_formula` に rewire |

全体集計は `deno run -A scripts/audit_db.ts scan` で取れる (snapshot を文書に書かない — 陳腐化する)。語彙詳細: [`audit-tags.md`](audit-tags.md)。

撤退ライン: 突破不可なら "Mathlib staged" 文書化のみで closure する条件は各 plan §撤退ライン参照 (CLAUDE.md「検証の誠実性」標準B の load-bearing-hyp 残課題化)。

なお、本 cleanup pass で `def` を audit kinds に加えたことで新たに surface した 12 件 (うち 9 件は honest, 3 件は上記 defect として確定) の経緯は本 plan の決定 #1 (Mathlib 壁距離は事前タグに含めない) の典型ケース: actually-fix を試みる段階 (= Tier-3 plan 起草段階) で初めて壁の具体形が固まる。
