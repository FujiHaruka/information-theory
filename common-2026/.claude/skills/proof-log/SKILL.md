---
name: proof-log
description: Lean 形式化作業のボトルネックを `docs/proof-logs/proof-log-<slug>.md` + `docs/metrics/<slug>.{manifest,metrics}.{json,md}` として残す。定量データは `scripts/session_metrics.ts` 任せ、本文は質的観察（grep 空振り、Mathlib に無かった補題、設計の後戻り）に集中させる。
---

# proof-log

Lean 形式化のボトルネックを記録し、claude code 自身の自動証明支援ツールのベースラインデータを溜めるスキル。

自己申告の定量数値（ツールコール数・所要時間など）は 2-3 倍ずれることが実測されている。定量データは必ず `scripts/session_metrics.ts` で JSONL から抽出し、proof-log の本文には書かない。

## 成果物

- `docs/proof-logs/proof-log-<slug>.md` — 質的ログ（このスキルで書く本文）
- `docs/metrics/<slug>.manifest.json` — 計測対象セッション/ターンの宣言（人間が書く入力）
- `docs/metrics/<slug>.metrics.json` / `.metrics.md` — スクリプト生成（定量データ）

スラッグは作業内容で自由に決める（既存例: `fano-phase1`, `han-moonshot`, `shannon-converse`）。

## ワークフロー

### 1. 対象ファイル prefix を確認

ユーザーから対象ファイル群を確認する。例: `InformationTheory/Shannon/Han.lean` 系列なら prefix は `InformationTheory/Shannon/Han`。

### 2. セッションとコア解答ターンを特定

```bash
deno run -A scripts/session_metrics.ts --discover --file-prefix <prefix>
deno run -A scripts/session_metrics.ts --turns <session-id> --file-prefix <prefix>
```

「コア解答ターン」の判定（強い順）:

1. 対象ファイルを最初に Write したターンを必ず含める
2. その前後で同じ作業の続きである Edit ターンも含める（prompt が「続けて」「実装して」など、または対象ファイルを直接いじっている）
3. ターン内 `tool_uses >= 5` 程度の規模感

含めない: 対象の確認だけ／事後分析（「ボトルネックは？」など）／proof-log 自体を書くターン／別作業のついでに Read しただけ／複数タスクにまたがる横断リファクタ。

セッションIDは 8文字プレフィックスで OK（一意なら自動で完全 UUID へ解決）。

### 3. manifest を書いて metrics を生成

`docs/metrics/<slug>.manifest.json`:

```json
{
  "problem": "<対象の説明>",
  "proof_log": "docs/proof-logs/proof-log-<slug>.md",
  "sessions": [
    { "id": "<UUID>", "prompt_ids": ["<8文字>", "..."], "note": "<このセッションで何をしたか>" }
  ],
  "filters": { "file_prefix": "<prefix>" },
  "idle_gap_minutes": 5
}
```

```bash
deno run -A scripts/session_metrics.ts docs/metrics/<slug>.manifest.json --render-md
```

### 4. 本文を書く

`references/template.md` に沿って `docs/proof-logs/proof-log-<slug>.md` を書く。書く／書かないの方針は `references/writing-guide.md`。解答とは別セッションで書く場合の再構成手順は `references/reconstruction.md`。

## 重要な制約

- **自己申告の数値を本文に書かない**: 「ツールコール約N回」「目視カウント、誤差±M」「`lake env lean` 約N回」「所要時間1〜2時間」などは禁止。すべて metrics.md にリンク。
- **旧版を書き直すときは旧 proof-log を読まない**: 自己申告数値を引き写す事故が起きる。git に残っているので失われない。manifest が既存なら `--render-md` で再生成、本文は `Write` で完全置換（Edit で部分追記しない — 旧構造が混入する）。
- **「無かった」を書く**: Mathlib に存在しなかった補題・空振り grep・deprecated タクティクは将来のツール仕様を駆動する一次データ。空疎な一般論（「Mathlib 検索は難しい」）ではなく具体（補題名・クエリ・試行回数）で書く。
