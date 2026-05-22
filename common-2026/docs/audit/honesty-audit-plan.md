# Honesty audit — 全定理の並列監査基盤 (設計)

ステータス: **設計確定**（実装済み）

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
- **層C — 定義を追う（最も高コスト）**: verdict が「ある定義が何に展開されるか」に依存する場合。degenerate_def（その def は vacuous か）/ load_bearing_hyp（`IsXxxRegularity` が証明の核心を束ねていないか）。grep/loogle/Read で定義を開き、束ねた仮定が**前提条件か証明の核心か**を判定する。CLAUDE.md の一言判定はこの層C。`load_bearing` はフラグで拾えない（決定#4）ので、未フラグ品でも匂えば層Cへ。

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
  - ※ ツールは `status=suspect` の claim を持たない。第2波は単一 Opus エージェントが `SELECT ... WHERE status='suspect'` 相当を引いて直接 Read で処理する（claim 不要）。多数並列で潰すなら `claim --status suspect` フィルタ追加を検討。

### クラッシュ / リース衛生・並列度

- exit 時に未判定行が残れば `release --agent A`（or orchestrator が `release --minutes 30`）。
- 走行中にコードが変われば `reaudit-stale`。
- WAL は「多数の読み＋直列の極小書き込み」。verdict/claim の書き込みは sub-ms なので **並列度 N の制約は DB でなく API レート**。N=4–8。各エージェントは固有 `--agent` 名（`sonnet-1`…）で起動（`release --agent`・帰属のため）。

### 1 シフトの具体レシピ（サブエージェントへの指示）

```
1. claim --agent sonnet-K --n 20        # JSON 受領（怪しい順 / 同一モジュール連続）
2. 各 id について:
     - 層A: 署名+doc で仮説。明白 defect / 対象外 skip ならここで verdict。
     - 層B: file:line を Read（同一ファイルは1回でまとめ読み）。本体で確定 → verdict。
     - 層C: 定義依存で決まらなければ定義を grep/loogle/Read。
            前提条件 か 核心 か を判定。決め切れなければ status=suspect。
     - verdict --id <ID> --status ... --verdict <code> --note ...
3. 全件 verdict 済みを確認 → 残あれば release --agent sonnet-K → exit
```

冪等再抽出: `build` はいつでも再実行可。`stats` が stale 件数を表示、`reaudit-stale` で該当だけ `unaudited` に戻す。

> フラグの注意: `body` は「`:=` から次の宣言開始まで」の過大近似（末尾 `end`/section 行を含みうる, `extract_statements.ts:202`）。`f_uses_sorry` 等はこの近似本体上で計算されるので**まれに隣接行由来の誤検出**を含む。フラグは着手優先度であって判定ではないので許容。verdict は必ず `file:line` 原典で。

## ファイル構成

- `scripts/extract_statements.ts` — 抽出コア（`parse` を export、proof 本体も取得）。Markdown 出力は人間用に維持。
- `scripts/audit_db.ts` — SQLite ツール。`build / stats / claim / show / verdict / release / reaudit-stale`。
- `docs/audit/honesty.db` — SQLite 本体（WAL）。**git 追跡しない**（`.gitignore` 済み）。

## 決定事項

1. **DB は git 追跡しない**（`.gitignore` 済み）。理由: 監査は「ある時点のコードベース」に対するもので、再生成可能。verdict も追跡しない。
2. **起動方法**: worktree は使わない（コード変更を伴わないため）。**このプロジェクト内で並列 N エージェント**が 1 つの DB を共有し `claim` で排他分担。N は起動時に指定。
3. **verdict コード体系**（固定語彙＋ catch-all）:
   `ok` / `load_bearing_hyp` / `degenerate_def` / `circular` / `sorry` / `name_laundering` / `mathlib_wall_misuse` / `true_residual` / **`other`**（上記に当てはまらないもの。`--note` に詳細）。
   ※ `--verdict` は自由記述（強制バリデーションなし）。集計しやすいよう上記語彙を推奨。
4. **フラグは現状の簡単な5つのみ**、強化しない。load-bearing の高度検出（仮定数・仮定型が結論を含む等）は**入れない**。最終的な load-bearing 判定はエージェントが doc とステートメントを読んで下す。`f_name_laundering` 等が誤検出を含むのは許容（着手優先度であって判定ではない）。
5. **監査エージェントは Sonnet を使う**（Opus でなく）。判定は「statement+doc+body を読んで固定語彙（`ok`/`load_bearing_hyp`/`circular`/…）に分類」と仕様が明確で、Opus 級の探索は不要。コストが約 1/5（全件で Sonnet ~$50–100 vs Opus ~$250–450）。並列 N=4–8・2波（フラグ117件→残り2825件）で全件 8–28h、最重要117件なら 2–4h／$10–20 が目安。
