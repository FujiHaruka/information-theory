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

### 3. 圧縮ルール R1-R14 で診断

各節を以下のヒューリスティクスで分類し、削減候補行数を見積もる。**コードに即して判断**する (該当する pattern が実際にあるか Read で確認)。

R1-R8 は穏当な line-level 削減、R9-R14 は **section rewrite** (積極的に節を解体して再構成)。1st-pass で R1-R8 だけ適用すると -25-30% 程度で頭打ちになる。50%+ 削減したい場合は R9-R14 も並行適用する。

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
| **R9. 進捗 checkbox + 撤退ライン総覧の削除** | 進捗 checkbox list (Phase ヘッダと重複) + per-Phase 撤退ライン がある状態での「撤退ライン総覧」表 | 両方とも純重複なので削除 (Phase ヘッダ + per-Phase 撤退ライン で十分) |
| **R10. 未起動 Phase 詳細の anchor 化** | 未起動 Phase の file × tag 9-row 表 + sub-step A/B/C/D 詳細 | 1 段落 anchor (主要対象 + dispatch 設計 + Done + 撤退ライン slug のみ)。詳細は Phase 起動時に Phase 0 inventory 表で verbatim 再取得 |
| **R11. per-file 表を cluster 合計表へ** | Cluster 別 file × tag count の verbatim 表 (15-30 行) | cluster 合計行のみ (3-5 行)、per-file 内訳は Phase 起動時に `rg -c` で再取得 |
| **R12. 完了済 Phase の解説段落圧縮** | Phase 2.A / 2.C など完了済 Phase の現状・採用根拠・改訂内容を本文に多段落 | 1-2 行 (commit hash + 結論 + 「詳細 → 判断ログ entry N」)。verdict サマリ V1-V4 等は判断ログに統合 |
| **R13. アクティブ Phase の選択肢 deliberation 削除** | 段 1/2/3 内の「選択肢 A: ... 選択肢 B: ... default は A」 | default のみ記述、選択肢列挙削除 (撤退ラインで represent) |
| **R14. Phase 別検証 bash の単化** | Phase 1/2/3 ごとに同型の `for f in <file list>; do lake env lean ...` bash | 散文 1 行 (「該当 Cluster の file を `lake env lean`」)、bash block は Phase V 最終 loop のみ |

### 4. 残す対象 (削らない判定リスト)

進行中タスクの anchor になっているものは保持する:

- **アクティブ Phase の scope 表 + 3 段 Approach** (実行中の参照点)
- **撤退ライン entry (per-Phase 内)** — 進行中に発火しうる選択肢
- **判定軸 / 判定基準** — sweep 内で繰り返し使われる判断ロジック (Phase 跨ぎ再利用)
- **Cluster 別 baseline 合計** (tag カウント) — sweep 全体の anchor

**未起動 Phase の per-file 表 / 未起動 sub-step の詳細手順は anchor のみで OK** — 起動時に verbatim 再取得すれば良い。「決着したロジック」は残し、「決着済の選択経緯」「未起動 Phase の予想 walkthrough」は畳む、と覚える。

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

### 6. 実行 (2-pass 戦略)

Edit ベースで節単位に削減。**1 つの大きな Edit ではなく、節ごとに小さな Edit を積む** — 失敗時の rollback と差分レビューが楽。

**1st pass — line-level 削減 (R1-R8)**:
1. R1 履歴重複削除 — 一番効く、最初に
2. R2 決着済選択肢畳み込み
3. R3 完了 Phase 圧縮
4. R4-R8 機械的に適用

ここまでで -25~30% が typical。1st pass 後に `wc -l <path>` で計測。**目標未達なら 2nd pass に進む**。

**2nd pass — section rewrite (R9-R14)**:
- 1st pass は行単位の削除が主体で天井がある。50%+ 削減には **節を解体して 1-3 行 anchor に書き換える** 積極的姿勢が必要。
- 特に「未起動 Phase の詳細手順」「per-file 表」「完了済 Phase の解説段落」は anchor + 判断ログ参照に縮約。
- 大きく書き換える節があるときは 1 つずつ Read → 書き換え後の像を頭で確認 → Edit。複数の節を一度に書き換えると整合性が崩れる。

各 Edit 後は file state を信頼 (CLAUDE.md「Edit は file state 既知」)、Read は必要時のみ。

### 7. 検証 + コミット

```bash
wc -l <path> && wc -c <path>
git diff --stat <path>
```

before/after を比較。CLAUDE.md「Commits」に従い autonomous commit + push。メッセージ例:

```
<plan-slug>: plan ダイエット (786→311 行、-60%)
```

1st pass / 2nd pass を別 commit にする (各 commit のメッセージに削減率)。

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
