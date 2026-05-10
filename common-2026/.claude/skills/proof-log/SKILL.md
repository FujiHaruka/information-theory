---
name: proof-log
description: 共通テスト・東大の数学問題を Lean で解いた直後（または後続セッション）に、その作業のボトルネックをログとして記録する。`docs/proof-logs/proof-log-<slug>.md` と `docs/metrics/<slug>.{manifest,metrics}.{json,md}` を作る。ユーザーが「ログを残して」「proof-log を作って」「ボトルネックを記録して」「振り返りを残して」「今回の作業を記録して」のように依頼したときは必ずこのスキルを起動すること。Claude Code 自身のツールコール数や所要時間の自己申告は 2-3 倍ずれることが実測されているので、定量データは必ず `scripts/session_metrics.ts` から取り、proof-log の本文は質的観察（Mathlib 探索の試行錯誤、後戻り、ハマりどころ、欲しかったツール）に集中させる。最終目的は claude code 自身による自動証明支援ツールを作るためのベースラインデータを溜めること。
---

# proof-log: 解答作業のボトルネック記録

このプロジェクトで Lean 形式化を行ったあとに、**「次に同じことをするときに claude code を支援するツールが何をすべきか」を後から判断するための一次データ**を残すスキル。

## なぜ機械化された定量データが必須か

このスキルを書いている時点で実測済みの事実:

- ある問題（東大 2026 第1問）の proof-log を claude code が自分で書いたところ、「ツールコール総数 30〜40 回前後」と書かれていた
- JSONL から実測すると **128 回**（除 Task系で 90 回）
- 体感所要時間「約 90 分」 → 実測 **42 分**（コア解答ターンに絞ると 22 分）
- Mathlib grep 回数「約 18」 → 実測 **31 回**

つまり Claude Code 自身は自分の作業量を再現性なく見積もる。proof-log がツール開発のベースラインとして使える条件は「数値部分が機械的に検証可能」であること。だから:

- 定量データは `scripts/session_metrics.ts` を必ず実行して JSONL から抽出する
- proof-log 本文には自己申告の数値を書かない（必要なら metrics.md へリンク）
- 本文は **スクリプトでは取れないこと**だけに集中する

## 成果物

スラッグの規則は問題の種類による:

| 問題種別 | スラッグ例 | 対象ファイル prefix |
|---|---|---|
| 東大 2026 第N問 | `todai-2026-q<N>` | `Common2026/Exam/Todai2026/T_Q<N>` |
| 東大 2024 第N問 | `todai-2024-q<N>` | `Common2026/Exam/Todai2024/T2024_Q<N>` |
| 共通テスト 1A 第N問 | `kyotsu-1a-q<N>` | `Common2026/Exam/KyoTsu2026/A_Q<N>` |
| 共通テスト 2B 第N問 | `kyotsu-2b-q<N>` | `Common2026/Exam/KyoTsu2026/B_Q<N>` |

生成するファイル:

- `docs/proof-logs/proof-log-<slug>.md` — 質的ログ（人間が書く本文）
- `docs/metrics/<slug>.manifest.json` — 計測対象セッション/ターンの宣言（人間が書く入力）
- `docs/metrics/<slug>.metrics.json` — スクリプトが生成（生メトリクス）
- `docs/metrics/<slug>.metrics.md` — スクリプトが生成（人間可読サマリ）

## ワークフロー

### ステップ 1: 対象ファイル prefix を決める

ユーザーの言う問題から上の表で対応する `Common2026/<prefix>` を決める。例: 東大 2026 第3問なら `Common2026/Exam/Todai2026/T_Q3`。

### ステップ 2: 該当セッションを発見

```bash
deno run -A scripts/session_metrics.ts --discover --file-prefix Common2026/<prefix>
```

該当ファイルを Edit/Write/Read したセッションが時系列で出力される。**`writes >= 1` のセッションがその問題の作成セッション**である可能性が高い。後続のリファクタや読み直しセッションも一覧されるので、それらは別途用途を判断する。

### ステップ 3: セッション内のターンを特定

```bash
deno run -A scripts/session_metrics.ts --turns <session-id> --file-prefix Common2026/<prefix>
```

各ターン（promptId 単位）の開始時刻・所要時間・ツールコール数・ユーザー prompt 文の先頭・触ったファイルが表示される。

**「コア解答ターン」**を特定する。判定ルール（強い順）:

1. **対象ファイルを最初に Write したターンを必ず含める**。それが解答の本体である可能性がほぼ確実。
2. その Write ターンの前後で、ユーザー prompt が「解いて／挑戦して／続けて／実装して」または問題自体を参照していて、対象 prefix のファイルを Edit しているターンも含める（同じ解答作業の続きである可能性が高い）
3. ターン内で `tool_uses >= 5` 程度の規模感がある

含めない:

- PDF ダウンロード／問題の確認だけ
- 解答後の「ボトルネックは何だった？」のような事後分析ターン
- proof-log 自体を書くターン（このスキル実行ターン自身もそう）
- `--discover` で同じ prefix にヒットしたが、実際は別問題の解答セッションで対象 prefix のファイルを Read しただけのもの（`writes_by_file` / `edits_by_file` で対象ファイルが空ならスキップ）
- 名前空間統一など複数問題にまたがる横断リファクタ（その問題のためだけの作業ではない）

ユーザーが途中で「思ったより速いね、続けて」のような進捗確認をしている場合、ターンが2つ以上に分かれていることがある。両方コアに含めるのが自然。

セッションIDは `--turns` でも manifest でも 8文字プレフィックスで OK（一意に決まれば自動的に完全 UUID へ解決される）。

### ステップ 4: manifest を書く

`docs/metrics/<slug>.manifest.json`:

```json
{
  "problem": "<日本語の問題名>",
  "proof_log": "docs/proof-logs/proof-log-<slug>.md",
  "sessions": [
    {
      "id": "<完全な UUID>",
      "prompt_ids": ["<8文字プレフィックスでよい>", "..."],
      "note": "<このセッションで何をしたか>"
    }
  ],
  "filters": { "file_prefix": "Common2026/<prefix>" },
  "idle_gap_minutes": 5
}
```

複数セッションにまたがる場合は `sessions` 配列に並べる。

### ステップ 5: メトリクス生成

```bash
deno run -A scripts/session_metrics.ts docs/metrics/<slug>.manifest.json --render-md
```

`<slug>.metrics.json` と `<slug>.metrics.md` が生成される。

### ステップ 6: 質的ログを書く

`references/template.md` を読んで、その骨組みに沿って `docs/proof-logs/proof-log-<slug>.md` を書く。

書くべき／書かざるべきの方針は `references/writing-guide.md` を参照。

## 後続セッションで書く場合の注意

スキル起動時のセッションが解答セッションと別の場合、会話メモリには解答中の試行錯誤が残っていない。そのときは JSONL を直接読んで再構成する：

- `--turns <session-id>` の出力は質的観察の**最初の足がかり**になる（ターン分割と各ターンの規模が見える）
- それ以上の細部は JSONL を `jq` などで解析する。具体的なコマンドは `references/reconstruction.md` 参照
- `git log -p Common2026/<prefix>*` で実際にコミットされた最終形を確認できる（`<prefix>` には `Exam/Todai2026/T_Q3` のようにサブディレクトリを含むので、コマンドはこのままでよい）

詳細は `references/reconstruction.md`。

## 既存の proof-log を書き直す場合

このスキルは新規作成だけでなく、旧形式（自己申告の数値が本文にある）proof-log の書き直しにも使う。手順:

1. **旧 proof-log は読まない**。読むと旧版の自己申告数値（「ツールコール約N回」「目視カウント、誤差±M」など）を引き写す事故が起きる。git に commit 済みなので失われない。
2. manifest が既にある場合（`docs/metrics/<slug>.manifest.json` が存在）は内容を確認し、必要なら prompt_ids を更新してから `--render-md` で再生成。manifest が無い場合はステップ 1 から通常通り。
3. 新形式の proof-log を `Write` で完全に置き換える（`Edit` で部分追記しない — 旧構造が混入するため）。

## 重要な制約

- **自己申告の数値を本文に書かない**: 「ツールコール総数 約N回」「目視カウント、誤差±M」「`lake env lean` 約12回」「所要時間1〜2時間」のような表現は書かない。すべて metrics.md にリンクする。
- **旧版 proof-log の数値を引き写さない**: 書き直しのときに最も起きやすい事故。旧版を読まないのが最も安全（前項参照）。
- **空疎な一般論を書かない**: 「Mathlib 検索は難しい」のような誰でも書ける文は価値がない。ファイル名・補題名・実際の grep クエリ・所要試行回数といった**具体**で書く。
- **「無かった」を書く**: Mathlib に存在しなかった補題、空振りした grep クエリ、deprecated だったタクティクは特に重要。これらが将来のツール仕様を駆動する。
