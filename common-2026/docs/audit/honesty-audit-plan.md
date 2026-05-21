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

## エージェント・ワークフロー（1サイクル）

```
claim   --agent A --n 20         # 割当を JSON で受け取る (id, signature, doc, flags)
show    --id <ID>                # 必要なら全文(本体含む) / または file:line を Read
verdict --id <ID> --status ok|suspect|defect|skip --verdict <code> --note <text>
```

冪等再抽出: `build` はいつでも再実行可。`stats` が stale 件数を表示、`reaudit-stale` で該当だけ `unaudited` に戻す。

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
