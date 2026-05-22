# Honesty audit — 全定理の並列監査基盤 (設計)

ステータス: **設計確定・実装済み・calibration 合格 → 実行可能**

実行 runbook（この plan だけで完結）: ①「オーケストレーション（外側ループ・開始前チェックリスト）」の手順に従う → ② ワーカーは `docs/audit/worker-prompts.md` のテンプレを verbatim で `Agent` に渡す → ③ ゲート基準は `docs/audit/calibration-set.md`。新セッションはこの3ファイルだけ読めば監査を開始できる。

## Context / 目的

無理な拡張の結果、機械検証は通る（`0 sorry`）が**主張が弱い / 仮定が結論を肩代わりしている**怪しい証明が紛れ込んでいる。これを全定理（Exam 除く 2942 件 / 241 ファイル）にわたって、**複数セッション・複数エージェント並列**で honesty 監査したい。

判定バーは CLAUDE.md「検証の誠実性」標準B。defect の型:
循環 (`:= h`) / `:True` residual / 退化定義 / load-bearing 仮定 / name laundering / Mathlib 壁の誤用。

1.9MB の Markdown は文脈に載らず破綻する。→ **データとして管理し、必要分だけ取り出す**。

## Approach（全体の形）

**「再生成可能な在庫テーブル × 永続する監査台帳」を SQLite 1ファイルに同居**させる。

- 在庫 (`theorems`): コードから抽出。いつでも `build` で再生成。署名・doc・proof 本体シグナル・トリアージフラグを持つ。
- 台帳 (`audit`): エージェントが書く判定。`build` で**絶対に上書きしない**。`id` で join。

並列の肝は **WAL ＋ `BEGIN IMMEDIATE` による claim（リース）**。各エージェントは未監査行を排他的に N 件確保 → 監査 → 判定書き込み、を回す。エージェントは**サブコマンドだけ叩き、生 SQL を書かない**（原子性・スキーマをツール側に閉じ込める）。

サイズ問題は「小さくする」のではなく**行指向＋クエリで取り出す**ことで解く。フラグは判定ではなく**着手順の優先度付け**（怪しい順）。最終判定は必ずエージェントが statement+doc を読んで下す。

## データモデル

`id = "<module path>::<fully-qualified name>"`（安定キー）。

### `theorems`（source of truth、再生成可能）
`id, module, fqn, short_name, ns, kind, line, signature(verbatim), doc, body_lines, body_head, f_*(フラグ), flag_score, src_hash`

`src_hash = hash(signature + body)`。再抽出で署名/本体が変われば変化する。

### `audit`（永続、エージェントが書く）
`id, status, claimed_by, claimed_at, verdict, note, audited_at, audited_hash`

- `status`: `unaudited | claimed | ok | suspect | defect | skip`
- `audited_hash`: 判定時の `src_hash` を保存 → 後で `theorems.src_hash` と不一致なら **stale**（監査後に文が変わった）と検出。

## トリアージ・フラグ（怪しさ＝着手優先度。判定ではない）

| flag | 対応する defect | ドライラン件数 |
|---|---|---:|
| `f_uses_sorry` | sorry/sorryAx 依存 | 17 |
| `f_trivial_body` | 循環 `:= h` / `exact`/`rfl` 単発 | 9 |
| `f_name_laundering` | `_discharged/_full/_complete/_unconditional` | 41 |
| `f_load_bearing_doc` | docstring が load-bearing/核心/🟢ʰ を自己申告 | 38 |
| `f_true_in_sig` | 結論/仮定に `True`（residual 隠し） | 13 |

`flag_score = Σ flags`。何か1つ以上 = **117 件**。`claim` は `flag_score DESC` 順 → 怪しいものから。
※ あくまで proxy。proof 級の確証（sorryAx を依存経由で拾う）は flagged のみ `#print axioms` で別途。

## 並列の仕組み

- `PRAGMA journal_mode=WAL` + `busy_timeout=5000`：並列読み取り＋直列の小さな書き込み。
- `claim` は `BEGIN IMMEDIATE` 内で「未監査 N 件 select → status=claimed に update」を原子実行 → 2エージェントが同じ行を掴まない。
- crash で取り残された claim は `release --minutes M` で回収。

## 監査ワークフロー詳細設計

### 索引 vs 原典（2つの読み）

- **DB（`claim`/`show`）= ワークリスト＋第一読**。返すのは署名・doc・flags・`file:line`・`body_lines`(行数)・`body_head`(先頭語) のみ。**証明本体テキストは持たない**（`toRow` が本体を行数と先頭語に潰す）。
- **原典 `file:line` = 本体と周辺定義の ground truth**。verdict 級の証拠は必ずここから取る（原典なら周辺の定義も見え、stale も無い）。

> 注意: `audit_db.ts:17` の docstring と旧記述にあった「show は本体を含む」は**誤り**（本体カラムは無い）。本体は `file:line` Read で取る。

### 判定ツリー（claim → どこまで読むか → verdict）

**「claim → 即 verdict」は原則しない。** claim の JSON（署名+doc+flags）は *仮説を立てる* ためのもので、`ok` を書くには最低でも本体を読む。3層で深さを上げる：

- **層A — 署名+doc のみ（claim JSON）**: 主張が妥当か／名前が過剰主張(laundering)か／結論に `True` が紛れていないか。これだけで書けるのは、署名段階で明白な `defect`（例: `_unconditional` 名なのに仮定の一つが結論そのもの）と、対象外の `skip` だけ。**`ok` はここでは出さない**。
- **層B — `file:line` で本体を読む（既定の主戦場）**: 循環 `:= h` / trivial body / `sorry` / true_residual / 仮定が実際に使われているか。大半の `ok`/`defect` はここで決まる。
- **層C — 定義を追う（最も高コスト・狭く必要）**: verdict が「ある自作定義が何に展開されるか」に依存する場合のみ。degenerate_def（その def は vacuous か）/ load_bearing_hyp（`IsXxxRegularity` が証明の核心を束ねていないか）。定義を開き、束ねた仮定が**前提条件か証明の核心か**を判定する。CLAUDE.md の一言判定はこの層C。`#print axioms` では検出不能（load-bearing 仮定は束縛変数であって公理でない＝定理は axiom-free に見える）。起動条件と読み方は下記。

### 層C — 起動条件と定義の bounded read

**起動条件**（条件1が層C入りの必要条件、条件2が深さを決める）:

1. **【必要】自作述語仮定**: 仮定（または結論）の型 head が **Common2026 内で `def/abbrev/structure/class/inductive` 定義された述語**。Mathlib/stdlib のクラス（`IsFiniteMeasure` / `Measurable` / `Fintype` / `0 < _` 等）は対象外 → 層Bで `ok` 終了。判定は locate の rg がそのまま兼ねる（ヒット0件＝自作でない）。
2. **【深さ】discharge 風 or 自己申告**: その仮定を持つ定理の証明が主張の難度に対し不自然に短い／`by exact h.xxx` 的に当該仮定へ寄りかかる（`body_lines` 小 ＋ `body_head` が `by`/`exact`/仮定名）、または doc が 🟢ʰ / load-bearing を自己申告。
   - 条件1 のみ（証明が実質的で仮定は補助）→ **軽い層C**: 定義を1回読んで「前提条件である」ことを確認し `ok`。
   - 条件1＋2 → **深い層C**: 定義を unfold して核心肩代わりを精査。決め切れねば `suspect`。

**定義の読み方（ファイル全体を読まない）**:

```
# 1. locate（自作述語かの判定も兼ねる、索引不要・即時）
rg -n --type lean '^\s*(def|abbrev|structure|class|inductive)\s+<TypeHead>\b' Common2026
#   → file:line。0件＝stdlib述語 → 層C不要。複数ヒットは namespace で選別。
# 2. その定義本体だけを bounded read（def/abbrev: ~30行 / structure: 次宣言まで）
Read <file> --offset <line> --limit 30
#   → `: Prop := <本体>` / structure のフィールド群を読み、前提条件 vs 核心 を判定。
# 3. 本体がさらに別の自作述語を含めば 1 に戻る（通常1段、まれに2段）。
```

> 例: `IsParallelGaussianPerCoordRegularity`（structure, L156）は 22 行の bounded read だけで、`bddAbove`(前提条件) に加え `achiever_mi`(達成可能性) と `max_ent`(逆問題=壁) の**両難題を束ねている**ことが判明する。ファイル全体は不要。

DB には `theorem`/`lemma` のみ索引（`def`/`structure` は無い）ので、定義の locate は rg が正。索引化すれば `claim`/`show` で位置を即取得でき `f_custom_pred_hyp` フラグの基盤にもなるが、層Cは flagged 中心（~80–120件）で発火頻度が低く、rg+bounded read で十分（決定#4 を尊重し索引拡張は保留）。

### load-bearing 判定ドクトリン（worker 指示に必須埋め込み）

監査の中核。**これ無しでは Sonnet は `🟢ʰ` load-bearing 定理を `ok` と誤判定する**（calibration run #1 で実証: `isParallelGaussianPerCoordReduction_discharged` を `ok` 誤判定。原因は doc 自己申告の鵜呑み＋仮定束をフィールド単位で見たこと）。worker prompt に必ず以下5ルールを埋める。

1. **doc の自己申告は"検証対象"であって"安心材料"ではない。** 「genuine」「honest hypotheses」「sup-sandwich」「none is the conclusion」で `ok` にしない。むしろ `🟢ʰ`／「absent from Mathlib」／「load-bearing」／「the wall」は **load-bearing の陽性指標**。verdict は statement+body+定義から導き、**doc と矛盾してよい**。
2. **仮定束は"まとめて"見る（核心再構成テスト）。** 問い: 「これらの仮定を全部認めたら、達成可能性＋逆問題／鍵となる等式・限界＝定理が主張する核心が手に入るか？」YES なら load-bearing。**個々のフィールドが結論と逐語一致しなくても無関係**（今回の構造体は `achiever_mi`=達成 ＋ `max_ent`=逆問題 で、まとめて核心）。
3. **regularity vs 核心チェックリスト**（一言判定を操作可能化）:
   - **regularity（前提条件・OK）**: 可測性・可積分性・有限性(`IsFiniteMeasure`)・full-support・正値(`0<P`)・`BddAbove`・summability・補助量の KKT/最適性
   - **核心（load-bearing・✗）**: 達成可能性の値・逆問題/上界・定理の主張そのものである等式や限界・doc が「壁／Mathlib に無い／hard part」と認めるもの
   - 灰色 → `suspect`
4. **「両側が同一仮定から」tell**: `le_antisymm`／サンドイッチの両方向が**同じ自作述語仮定**で埋まっていたら、その仮定は load-bearing（今回まさに `..._le_sum ... h_reg` ＋ `..._ge_sum ... h_reg`）。
5. **層C深さ分離**: trigger は自作述語仮定で発火、深さは透明な1行 `def:Prop:=式`＝1行読むだけ／`structure`・多連言＝全フィールド。透明さは**読みコストを下げるが判定は同じ**（1行 `def:=（容量=和）` を仮定に持てば load-bearing）。

**verdict ルール**: 上記で核心肩代わりと判定したら **`ok` にしない**。`--verdict load_bearing_hyp`、`--status suspect`（暫定）。note に「honest `🟢ʰ`（残タスク）か / dishonest（name laundering・偽完成）か」を明記。`🟢ʰ` の status を `suspect`/`defect` どちらに寄せるかは verdict 語彙の意味論として別途確定。

### 粒度: バッチ claim・直列判定・1件ずつ verdict・context 上限

- **claim N**: フラグ波 N=10（散在・深い）／本体波 N=20–30（claim は `module,line` 順なので同一ファイルが連続クラスタ化 → ファイルを1回 Read して数件まとめて見る）。
- **1 サブエージェント = 1 シフト**: `claim → バッチ監査 → 各 verdict → 余りを release → exit`。1 シフトは ~20–40 件（1–2 バッチ）で打ち切り、context を小さく安く保つ。次シフトは fresh sub-agent。
- **バッチ内は直列判定**（verdict は id 単位、status 混在をまとめて書けない）。ただし *読み* はまとめてよい（本体波は同一モジュールを1回 Read）。
- **claim した行は exit 前に必ず verdict か release**。`claimed` のまま残すとリースが他をブロックする。

### status 意味論とモデル2段

- `ok` — 本体（層B）を読んで確信。
- `defect` — 確定。`--verdict <code>` ＋ `--note` に具体的欠陥と位置。
- `suspect` — 匂うが Sonnet が決め切れない（多くは層Cの load-bearing 判断）。= **エスカレーション待ち行列**。
- `skip` — honesty 対象外（誤抽出の `def`・記法・足場コード）。
- **2段モデル**: 全件パスは Sonnet。`suspect` だけ第2波で **Opus**（小 N・定義追跡）。suspect は少数なので安い。
  - 第2波の対象供給: `list --status suspect`（一覧＋1次note、単一 Opus 用）／`claim --status suspect --agent opus-K`（並列 Opus 用に排他再リース）。どちらも実装済み。

### クラッシュ / リース衛生・並列度

- exit 時に未判定行が残れば `release --agent A`（or orchestrator が `release --minutes 30`）。
- 走行中にコードが変われば `reaudit-stale`。
- WAL は「多数の読み＋直列の極小書き込み」。verdict/claim の書き込みは sub-ms なので **並列度 N の制約は DB でなく API レート**。N=4–8。各エージェントは固有 `--agent` 名（`sonnet-1`…）で起動（`release --agent`・帰属のため）。

### 1 シフトの具体レシピ（サブエージェントへの指示）

> ↓ は要約。**ワーカーに渡す完成形プロンプトは `docs/audit/worker-prompts.md`「TASK A」**（CORE＋シフト指示）を verbatim で使う。doctrine を取りこぼすと偽陰性が出るので自前で短縮しない。`subagent_type:"general-purpose"`、DB は既定。

```
1. claim --agent sonnet-K --n 20        # JSON 受領（怪しい順 / 同一モジュール連続）
2. 各 id について:
     - 層A: 署名+doc で仮説。明白 defect / 対象外 skip ならここで verdict。
     - 層B: file:line を Read（同一ファイルは1回でまとめ読み）。本体で確定 → verdict。
     - 層C: 自作述語仮定があるときのみ。rg で定義 locate → Read --offset --limit で
            定義本体だけ bounded read（ファイル全体は読まない）。前提条件 か 核心 か を
            判定。決め切れなければ status=suspect。
     - verdict --id <ID> --status ... --verdict <code> --note ...
3. 全件 verdict 済みを確認 → 残あれば release --agent sonnet-K → exit
```

### オーケストレーション（外側ループ・開始前チェックリスト）

シフト＝内側ループ。オーケストレータ（Opus）は外側で波を回す。**ワーカーは固有 `--agent` 名**（`sonnet-1`…/`opus-1`…）で起動する（`release --agent` とクラッシュ回収が名前依存）。

> **★ オーケストレータ不可侵原則: オーケストレータは"調整専任"。** やってよいのは (1) `audit_db.ts` のサブコマンド実行（`build/stats/claim/list/release` — 返るのは件数と小さな JSON のみ）と (2) サブエージェント起動だけ。**ソース `.lean`・証明本体・定義・docstring を自分で Read してはならない。** 読みと判定はすべてサブエージェント内で行う（QA の Opus も例外なくサブエージェント）。理由: 1.9MB 級の本文がオーケストレータ context に流入すると破綻する。これを避けるための SQLite worklist であり、原則を破ると設計目的が無効化する。

```
# --- 開始前 ---
deno run -A scripts/audit_db.ts build      # 索引を現コードに更新（DB は既存だが古い可能性）
deno run -A scripts/audit_db.ts stats      # unaudited 件数・flag 分布を確認 → コード凍結
deno run -A scripts/audit_db.ts release --minutes 0   # （任意）前回の claimed 残を回収
# ★ calibration gate（必須）: cp docs/audit/honesty.db /tmp/cal.db して
#   worker-prompts.md「TASK B」(Sonnet) で calibration-set.md の8件を試走。
#   LB 6件が全て status!=ok なら合格。1件でも ok（偽陰性）なら doctrine 修正して再走。
#   合格まで本番に進まない。終わったら rm -f /tmp/cal.db*。

# --- 第1波: Sonnet 全件 ---
# unaudited>0 の間、worker-prompts.md「TASK A」を Agent(model:"sonnet",
#   subagent_type:"general-purpose") で N=4–8 個 並列起動（1メッセージに複数 Agent 呼び出し）。
#   各ワーカー = 1 シフト。固有 --agent 名 sonnet-1..K。DB は既定。
#   ※ claim は flag_score DESC 順 → フラグ117件が自然に先頭で消化される（別波にしなくてよい）。
# 波の合間に: release --minutes 30   # クラッシュした stragglers を回収
# stats で unaudited=0 かつ claimed=0 を確認 → 第1波完了

# --- 第2波: Opus が suspect を深掘り ---
deno run -A scripts/audit_db.ts list --status suspect       # 対象と1次note を一覧
#   単一 Opus: そのまま処理 / 並列 Opus: claim --status suspect --agent opus-K で再リース
#   起動は worker-prompts.md「TASK A」相当を model:"opus" で（claim 行を --status suspect に）。
# 各 suspect: 深い層C（定義 unfold）→ verdict を defect|ok|suspect(据置) に確定

# --- 終了・レポート ---
deno run -A scripts/audit_db.ts list --status defect        # 確定欠陥（id, file:line, verdict, note）
deno run -A scripts/audit_db.ts list --status suspect       # 未決（人手 or 追加調査へ）
```

**stop 条件**: 第1波 = `unaudited=0 ∧ claimed=0`。全体 = `suspect` が空（or 人手送り）かつ `defect` をレポート化済み。

### (c) QA スポットチェック（`ok` の偽陰性率を継続推定）

Sonnet の `ok` には偽陰性（load-bearing 見逃し）が混じりうる（calibration はゼロにしたが本番母集団で再発しないとは限らない）。**Opus の QA サブエージェント**が `ok` をランダム再監査し、偽陰性率を推定する。

**頻度（被覆 ~1%）**: オーケストレータは `stats` の `ok` 件数を見て、**累積 `ok` が 1000 件境界を超えるごとに1回**、QA Opus を `--sample 10` で起動する。全工程（`ok` ≈ 2942）で計 **~3回・~30件 ≒ 母集団の約1%** の薄いサニティ抽出。**主防御は calibration gate**（本番前に doctrine を保証済み）であって QA ではない — QA は in-flight の異常検知で十分なので 1% に抑える。トリガー判定は件数のみ（ファイル不読の原則を保つ）。

**オーケストレータの動き（ファイルは読まない）**: `Agent(model:"opus", ...)` で QA サブエージェントを起動するだけ。読み戻すのは QA の**要約（チェック件数 K・flip 件数 m・flip した id）**のみ。`list` の生 JSON すら自分で開かない（QA 内で完結させる）。

**QA サブエージェント（Opus）の手順**（完成形プロンプトは `worker-prompts.md`「TASK C」）:
```
1. deno run -A scripts/audit_db.ts list --status ok --sample 10   # ランダム10件を自分で取得
2. 各 id を doctrine で再監査（show → 本体 Read → 層C）
3. flip（ok → load-bearing 等）した行のみ verdict で上書き:
     verdict --id <ID> --status suspect|defect --verdict <code> --note "QA-flip: <理由>" --agent qa-opus
   confirmed-ok はそのまま（書き換えない）
4. 要約だけ返す: 「K=10 中 flip m 件、内訳 <id: 理由>」
```

**判定とフィードバック（オーケストレータ）**:
- flip が出たら、それは **doctrine の穴**のサイン（同型の見逃しが母集団に散在しうる）。
- m=0 → 健全。次の 1000-件境界まで QA は撃たない（被覆 ~1% を超えない）。
- m≥1 で **load-bearing の明白な見逃し** → **停止**。flip 事例から doctrine を補強 → calibration gate 再走（合格まで）→ 影響母集団（同じ flag/同種述語の `ok`）を **`claim --status ok` で再リース**して再監査（`reaudit-stale` は src_hash 変化時のみで doctrine 修正には効かないため不可）。
- flip した行自体は QA が既に修正済み（`ok` プールから抜ける＝self-correcting）。
- ランダムなので再サンプルは重複しうる（推定値としては許容）。被覆を厳密に追うなら別途 note マーカーを足すが、現状は不要。

冪等再抽出: `build` はいつでも再実行可。`stats` が stale 件数を表示、`reaudit-stale` で該当だけ `unaudited` に戻す。

> フラグの注意: `body` は「`:=` から次の宣言開始まで」の過大近似（末尾 `end`/section 行を含みうる, `extract_statements.ts:202`）。`f_uses_sorry` 等はこの近似本体上で計算されるので**まれに隣接行由来の誤検出**を含む。フラグは着手優先度であって判定ではないので許容。verdict は必ず `file:line` 原典で。

## ファイル構成

- `scripts/extract_statements.ts` — 抽出コア（`parse` を export、proof 本体も取得）。Markdown 出力は人間用に維持。
- `scripts/audit_db.ts` — SQLite ツール。`build / stats / claim / show / list / verdict / release / reaudit-stale`。`list --status S` と `claim --status S` で suspect 第2波・最終レポートを生 SQL なしで賄う。
- `docs/audit/honesty.db` — SQLite 本体（WAL）。**git 追跡しない**（`.gitignore` 済み）。
- `docs/audit/calibration-set.md` — 本番前の必須ゲート。既知 load-bearing 6＋genuine ok 2 のラベル済みセット＋PASS 基準（偽陰性ゼロ）。
- `docs/audit/worker-prompts.md` — ワーカーに verbatim で渡す prompt テンプレ（CORE doctrine ＋ TASK A シフト/B calibration/C QA）。`subagent_type`・DB パス・並列起動の規約もここ。

## 決定事項

1. **DB は git 追跡しない**（`.gitignore` 済み）。理由: 監査は「ある時点のコードベース」に対するもので、再生成可能。verdict も追跡しない。
2. **起動方法**: worktree は使わない（コード変更を伴わないため）。**このプロジェクト内で並列 N エージェント**が 1 つの DB を共有し `claim` で排他分担。N は起動時に指定。
3. **verdict コード体系**（固定語彙＋ catch-all）:
   `ok` / `load_bearing_hyp` / `degenerate_def` / `circular` / `sorry` / `name_laundering` / `mathlib_wall_misuse` / `true_residual` / **`other`**（上記に当てはまらないもの。`--note` に詳細）。
   ※ `--verdict` は自由記述（強制バリデーションなし）。集計しやすいよう上記語彙を推奨。
4. **フラグは現状の簡単な5つのみ**、強化しない。load-bearing の高度検出（仮定数・仮定型が結論を含む等）は**入れない**。最終的な load-bearing 判定はエージェントが doc とステートメントを読んで下す。`f_name_laundering` 等が誤検出を含むのは許容（着手優先度であって判定ではない）。
5. **監査エージェントは Sonnet を使う**（Opus でなく）。判定は「statement+doc+body を読んで固定語彙（`ok`/`load_bearing_hyp`/`circular`/…）に分類」と仕様が明確で、Opus 級の探索は不要。コストが約 1/5（全件で Sonnet ~$50–100 vs Opus ~$250–450）。並列 N=4–8・2波（フラグ117件→残り2825件）で全件 8–28h、最重要117件なら 2–4h／$10–20 が目安。
   - **起動**: オーケストレータ（Opus）が `Agent(model:"sonnet", ...)` で Sonnet ワーカーを起動する。`Agent` の `model` は親と独立指定でき、親が Opus でも子は Sonnet になる（実証済み: 親 Opus → 子 `claude-sonnet-4-6`）。suspect 第2波は `Agent(model:"opus", ...)`。
