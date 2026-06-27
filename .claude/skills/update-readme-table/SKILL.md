---
name: update-readme-table
description: README.md の「Formalized results」定理表を最新化する。ユーザーが「readme の定理表を更新して」「定理表を直して」「README に定理を追加して」「定理一覧を同期して」「/update-readme-table」と言ったときに起動する。表は手書きせず、curation を `docs/readme-theorems.txt` で編集し `scripts/gen_readme_table.ts` で再生成する手順に乗せる。
---

# update-readme-table: README の証明済み定理表を再生成する

`README.md` の「Formalized results」表は **生成物** (`<!-- THEOREMS:START/END -->` マーカー間)。手書きすると rename / move / scope-out で黙って drift し、公開 README が嘘をつく。curation は `docs/readme-theorems.txt` 1 本だけに置き、表は `scripts/gen_readme_table.ts` で生成する。このスキルはその手順を実行する。

## 起動条件

ユーザーが以下を発話したら起動:

- 「README の定理表を更新して」「定理表を直して / 同期して」「定理一覧を最新化」
- 「README に `<定理名>` を追加して」「この章の代表を差し替えて」
- 「/update-readme-table」

## 前提 (この仕組みの SoT)

- **唯一の編集対象** = `docs/readme-theorems.txt`。`@ <章番号> | <トピック>` で章を開始、以下の行が代表定理。1 行 = `NAME` / `NAME | 注記` / `NAME @ パス断片`(同名 decl の曖昧性解消) / `NAME @ パス断片 | 注記`。
- **パスは書かない** — スクリプトが毎回 `InformationTheory/` を走査して解決する。ファイル移動は自動追従、true rename/delete だけが落ちる。
- README のマーカー間は **絶対に手で編集しない**。

## やること

### 1. 現状確認 + 意図の切り分け

```bash
deno run -A scripts/gen_readme_table.ts --check
```

- **緑 (in sync)** かつ依頼が「同期して」だけ → 既に最新。ユーザーに「現状 in sync」と報告して終了。
- **赤 (drift)** → メッセージが not-found / ambiguous / out-of-date のどれか教えてくれる。下記で対処。
- 依頼が「`<定理名>` を追加 / 差し替え」なら curation 変更 → step 2 へ。

### 2. curation を変更する場合 — マニフェストを編集

`docs/readme-theorems.txt` を `Edit`。

- **載せてよいのは proof-done (sorry なし) の定理だけ** (README は「machine-checked, no sorry」と公称)。追加前に実在 + sorry-free を確認:
  ```bash
  rg -n "(theorem|lemma|def) <NAME>\b" InformationTheory/
  ```
  ヒット 0 なら名前違い (綴り / 下付き文字 `₂` / namespace) を疑い再 grep。
- 該当する Cover & Thomas の章 (`@ <num> | ...`) の下に名前を追記。短い説明を付けたいときは `NAME | 注記`。
- どの定理を代表にするか (curation) は editorial。**1 本の名指し追加**なら該当章にそのまま置く。**大幅な入れ替え / 章の代表総入れ替え**はユーザーに方針確認してから。

### 3. 再生成

```bash
deno run -A scripts/gen_readme_table.ts --write
```

エラーが出たら:

- **`ambiguous (N decls)`** — 同名 decl が複数。意図する側のパス断片を `NAME @ MaxEntropy/Basic` のように足して再実行。
- **`not found`** — マニフェストの名前が実コードに無い。step 2 の grep で正しい名前を確認して直す。

### 4. 検証 + コミット

```bash
deno run -A scripts/gen_readme_table.ts --check   # ✓ in sync を確認
git diff --stat README.md docs/readme-theorems.txt
```

緑を確認したら CLAUDE.md「Commits」に従い autonomous commit + push (報告不要)。`README.md` と `docs/readme-theorems.txt` を明示パスで `git add` (`git add -A` は使わない)。

## 気をつけること

- **マーカー間を手書きしない** — 必ず `docs/readme-theorems.txt` を編集して `--write`。markers 内の差分を直接 Edit したくなったら step 2 に戻る。
- **誠実性の不変条件は迂回しない** — `--check` が `honesty: N file(s) contain a real 'sorry'` / `custom 'axiom'` で落ちたら、それは README の公称が崩れているプロジェクト側の実問題。表をいじって誤魔化さず、その事実をユーザーに surface する。
- **proof-done でない定理を表に入れない** — 表は完成定理の showcase。`sorry` / `@residual` が残る定理は載せない。
- CI ジョブ `readme-table` (`.github/workflows/lean_action_ci.yml`) が push 時に `--check` を回すので、drift したまま push すると赤くなる。手元で緑にしてから push する。

## トリガー語彙 (再掲)

「README の定理表を更新して」「定理表を直して / 同期して」「README に定理を追加して」「定理一覧を最新化」「/update-readme-table」
