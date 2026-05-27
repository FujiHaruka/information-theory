---
name: compact-plan
description: 進捗追記で肥大化した `docs/**/*-plan.md` を要約 + 削除で圧縮する。ユーザーが「プランを圧縮して」「計画ダイエット」「plan をスリムに」「/compact-plan」と言ったときに起動する。鮮度が落ちた履歴 / 決着済選択肢 / 重複記述を畳んで、アクティブな scope / 撤退ライン / 判断軸を残す。
---

# compact-plan: 鮮度低下した plan ファイルを圧縮する

`docs/<family>/*-plan.md` は進捗・ピボット履歴・判断ログを追記し続けるうちに 60-80 KB / 800-1300 行になり、`/resume` 時の cache を一気に食う。完了済 Phase の細目や、本文 + 判断ログの二重保持を畳んで 30-40% 削減する。

## 起動条件

ユーザーが以下を発話したら起動:

- 「プランを圧縮して」「計画ダイエット」「plan をスリムに」「サイズ縮めて」
- 「/compact-plan」「/compact-plan <path>」

引数で path 指定があればそれを対象、なければ「`docs/**/*-plan.md` のうち最大のもの」を `wc -c` で 1 件選んで提案。

## やること

### 1. 計測

```bash
wc -l <path> && wc -c <path>
```

40 KB / 600 行を超えていれば圧縮価値あり。下回るならユーザに「現状で十分小さい、本当に圧縮する?」と確認。

### 2. 構造把握

```bash
awk '/^##[^#]/ || /^### / {printf "%4d  %s\n", NR, $0}' <path>
```

節タイトル + 行番号一覧を取得。どの節がどの行範囲を占めているかを把握する。

### 3. 圧縮ルール R1-R8 で診断

各節を以下のヒューリスティクスで分類し、削減候補行数を見積もる。**コードに即して判断**する (該当する pattern が実際にあるか Read で確認)。

| ルール | 検知 | 置換 |
|---|---|---|
| **R1. 履歴重複の削除** | 同じピボット経緯が Context / 該当 Phase 冒頭 / 判断ログに 2-3 重記述 | 判断ログを SoT、本文は「経緯 → 判断ログ」リンクのみ |
| **R2. 決着済選択肢の畳み込み** | 「候補 1 vs 候補 2」「trade-off 表」だが既に方針確定済 | 採用結論を 1-2 行、選択肢列挙は削除 |
| **R3. 完了 Phase の status 圧縮** | `[x]` チェック済 step だけが並ぶ完了 Phase 節 | "完了 (commit XXX)" + 残 step のみ |
| **R4. verbatim audit 引用の単化** | 「audit docstring verbatim:〜」が plan 内で 2+ 回引用 | コード側 docstring が SoT、本文は 1 行サマリ |
| **R5. project-level rule の外出し** | 「先制検出ルール」「判定基準」など他 plan でも使える一般化 | 判定軸の 3 行だけ残し「→ audit-tags.md / CLAUDE.md 反映候補」を marker |
| **R6. 検証 bash ループの統合** | Phase 別 + Phase V で同じ file list を 2 回列挙 | 統合 final loop のみ verbatim、Phase 別は散文 |
| **R7. file reference の commentary 削除** | 関連 Files の各 path 末尾に長い散文 commentary | path のみ、必要なら 1-3 語の prefix (`SoT:` / `親 plan:`) |
| **R8. 予測・見積もり表の圧縮** | 計数表に「baseline / Done 条件」の 2 列予測、Phase 別行数 × session 数の 5×4 表 | baseline と Done 予測を各 1 段落散文 |

### 4. 残す対象 (削らない判定リスト)

進行中タスクの anchor になっているものは保持する:

- **未実行 Phase の verbatim scope 表** (file × tag カウント) — 実行時の anchor
- **撤退ライン総覧** — 進行中に発火しうる選択肢
- **判定軸 / 判定基準** — sweep 内で繰り返し使われる判断ロジック
- **アクティブな Phase の scope 表 / Approach 段階分解**

「判断したロジック」は残し、「決着した選択の経緯」は畳む、と覚える。

### 5. ユーザに診断結果を提示 + 確認

以下のフォーマットで 1 つのメッセージにまとめる:

```
## ブロート診断 (<path>、現在 N 行 / M KB)

| カテゴリ | 行数目安 | 内容 |
|---|---:|---|
| R1. 履歴重複 | ~XX | 該当節 + 重複先の節 |
| R2. 決着済選択肢 | ~XX | 該当の trade-off 表 / 候補列挙 |
| ... | | |
| 小計 | ~YY | (~ZZ%) |

残すもの: <未実行 Phase scope 表 / 撤退ライン / 判定軸>

目標: N → ~K 行 (~Z% 削減)。進めて良い?
```

ユーザーの green light を待つ。「方針に修正があるか?」と聞いて redirect を許す。

### 6. 実行

Edit ベースで節単位に削減する。**1 つの大きな Edit ではなく、節ごとに小さな Edit を積む** — 失敗時の rollback と差分レビューが楽。順序:

1. 履歴重複削除 (R1) — 一番効く、最初に
2. 決着済選択肢畳み込み (R2)
3. 完了 Phase 圧縮 (R3)
4. それ以外 (R4-R8) を機械的に

各 Edit 後は file state を信頼 (CLAUDE.md「Edit は file state 既知」)、Read は必要時のみ。

### 7. 検証 + コミット

```bash
wc -l <path> && wc -c <path>
git diff --stat <path>
```

before/after を比較。CLAUDE.md「Commits」に従い autonomous commit + push。メッセージ例:

```
<plan-slug>: plan ダイエット (786→567 行、-28%)
```

## 出力

ユーザーへの返答は短く:

- 削減後の行数 / バイト数 / 削減率
- どのカテゴリが効いたか 2-3 行
- 残ったブロート (もしあれば次回候補として 1 行)

長い経過説明は不要 (diff と commit log で確認可能)。

## 気をつけること

- **plan の凍結された Phase 番号 / hypothesis 名 / 撤退ライン slug (L-INT-2-α 等) は触らない** — 他文書から参照されている可能性。本文の説明だけ縮める
- **判断ログは append-only 規約** (各 plan の判断ログ節冒頭に書いてあるはず) — 既存 entry を編集して短くするのは OK、削除は不可
- **コード側 docstring の `@residual` / `@audit:*` は touch しない** — plan ダイエットの scope 外、別 task
- **`/resume` が依存する handoff.md は touch しない** — plan dir 以外には触らない

## トリガー語彙 (再掲)

「プランを圧縮して」「計画ダイエット」「plan をスリムに」「サイズ縮めて」「/compact-plan」
