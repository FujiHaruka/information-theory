# `InformationTheory` モジュール名リネーム — 手順見積もり

## 確定した方針(2026-06-03)

- **新ライブラリ名 = `InformationTheory`**(以降 `<NEW>` = `InformationTheory`)。
- **namespace も `InformationTheory.*` に統一**(C層、下記)。
- **リポジトリのフォルダ名 `common-2026` は据え置き**(ローカルパス・worktree boilerplate・
  loogle index パスへの波及を避ける)。lakefile の `name` は `common-2026` のまま、
  `[[lean_lib]] name` / `defaultTargets` / モジュールパスだけが `InformationTheory` になる。

### 採用に伴う注意:Mathlib との `InformationTheory` 共存

- **namespace**:Mathlib にも `InformationTheory.*` namespace がある(`klDiv` 等)。
  ただし lib 本体は既に `namespace InformationTheory` を多用しており、今と同じ状況が続くだけで
  **新規の衝突リスクは増えない**(同名シンボルを我々が定義しない限り共存)。
- **モジュールパス**:Mathlib 側は `Mathlib.InformationTheory.*`(`Mathlib.` 接頭辞付き)。
  我々の root は接頭辞なしの `InformationTheory` なので **パス衝突なし**。
- 残る懸念は認知コスト(読むとき Mathlib の namespace と紛らわしい)のみ。ビルド上は問題なし。

## Context — 現状の使われ方(実測)

`rg 'InformationTheory'` で **552 ファイル / 7387 箇所**。ただし用途は質的に 3 層に分かれ、
リネームの「必須度」が層ごとに違う。

| 層 | 対象 | 箇所 | 必須度 |
|----|------|------|--------|
| **A. モジュールパス / ライブラリ名** | `lakefile.toml` (`name`/`defaultTargets`/`[[lean_lib]]`)、root `InformationTheory.lean`、ディレクトリ `InformationTheory/` (205 `.lean`)、`import InformationTheory.*` 872 行 | 大半 | **必須**(壊れる) |
| **B. ハードコード Name リテラル** | `scripts/{SorryAudit,FindOrphans,EntryPointReport,SorryAuditPerModule}.lean` の `` `InformationTheory `` プレフィックス判定 | ~6 | **必須**(無言で 0 件返す) |
| **C. namespace `InformationTheory.*`** | lib の Shannon 系 ~20 ファイル (`namespace InformationTheory.Shannon[.…]`) + scripts の `InformationTheory.{SorryAudit,…}` | ~45 (20+21+4) | **任意**(モジュールパスと独立) |
| **D. テキスト参照** | docstring 内のパス文字列、`docs/**` (md 322 箇所)、`docs/metrics/*.json` (18)、`README`、`CLAUDE.md`、`scripts/*.txt`/`*.ts`、`docs/textbook/site/build.mjs` | 残り | **任意**(壊れないが残ると紛らわしい) |

重要な事実:
- **Lean ではモジュールパスと namespace は独立**。ディレクトリ `InformationTheory/` を改名しても、
  ファイル内の `namespace InformationTheory.Shannon` は強制では変わらない。逆も同様。
  → A と C は**別判断**。
- lib 本体の namespace の主流は `InformationTheory.*`。`InformationTheory.*` namespace は
  Shannon 系一部だけの少数派(規約の揺れ)。
- **CI は無改修で OK**:`.github/workflows/lean_action_ci.yml` は generic な
  `leanprover/lean-action@v1` でターゲット名をハードコードしていない。
- `lake-manifest.json` / `.gitignore` に `InformationTheory` 参照なし。
- loogle index は Mathlib のみなので無関係。

## Approach — 戦略

**「ディレクトリ名 = ライブラリ名」という Lean の制約が全体を駆動する。**
A 層(モジュールパス)だけは原子的に一括で行う必要があり、ここを外すとビルドが全面的に壊れる。
B 層は A と必ずセット(A だけ直すと tooling が無言で壊れる)。C・D 層は独立に後追い可能。

したがって手順は **2 つの必須コミット + 任意の後追い** に分解する:

1. **必須リネーム(A + B)を 1 コミットで原子的に**:`git mv` でディレクトリ history を保持しつつ、
   `import` 行 / lakefile / Name リテラルを一括 sed 置換。**この時点で full `lake build` が通ること**を
   完了条件にする(全 olean が無効化されるため、ここだけは例外的に full build が必要)。
2. **namespace 改名(C)を行うか別途決定**。行うなら 2 コミット目で機械置換 + full build 再確認。
   行わないなら新ライブラリ内に旧名 namespace が残る(動作上は無害)。
3. **テキスト参照(D)の掃除**。docstring パス・docs・metrics json・README 等。
   履歴文書(proof-logs / 古い plan)は「当時の記録」として凍結する判断もあり得る。

機械置換の安全性:`InformationTheory` は他の語の部分文字列にならない一意なトークンなので、
単純な文字列 `InformationTheory` → `<NEW>` の全置換で誤爆リスクは低い(`grep -F` レベル)。
唯一の注意は B 層の Name リテラル `` `InformationTheory `` がパスではなく**シンボル名前空間**を
指している点だが、これも文字列としては同一なので同じ置換でカバーされる。

## 手順詳細

### Phase 1 — 必須(A + B):モジュールパス + tooling リテラル

1. ディレクトリ改名:`git mv InformationTheory <NEW>` および `git mv InformationTheory.lean <NEW>.lean`。
   (`git mv` で rename を履歴に残す)
2. `lakefile.toml`:`name` / `defaultTargets` / `[[lean_lib]] name` の 3 箇所を `<NEW>` に。
3. 全 `.lean` の `import InformationTheory` → `import <NEW>`(lib 205 + scripts、872 行)。
4. scripts の Name リテラル `` `InformationTheory `` → `` `<NEW> ``(4 ファイル)。
5. root `<NEW>.lean` 冒頭コメント `the \`InformationTheory\` library` を更新。
6. **完了条件**:`lake build`(全面再ビルド、数分)が 0 error。
   ※ ここは CLAUDE.md「full build は使うな」の例外 — 全 olean 無効化のため単一ファイル検証では不十分。
7. tooling 動作確認:`lake env lean scripts/EntryPointReport.lean` 等が 0 件でなく正しく列挙するか
   (B 層の置換漏れは「0 declarations」という無言の失敗で出る)。
8. 1 コミット。

### Phase 2 — 確定(C):namespace `InformationTheory.*` → `InformationTheory.*` に統一

- 対象:lib の Shannon 系 ~20 ファイルの `namespace InformationTheory.Shannon[.…]` を
  `namespace InformationTheory.Shannon[.…]` に。これで lib 主流規約に揃い、揺れが解消する。
- 完全修飾参照(docstring 含む `InformationTheory.Shannon.foo` 等)も同時に置換。
- scripts の `InformationTheory.{SorryAudit,FindOrphans,EntryPointReport,SorryAuditPerModule}` namespace は
  tooling 専用。`InformationTheory.*` に寄せると Mathlib namespace と紛らわしいので、
  中立な接頭辞(例 `Tooling.*` / namespace 無し)も選択肢 — Phase 2 着手時に確認。
- full build 再確認 + 1 コミット。

### Phase 3 — 任意(D):テキスト参照の掃除

- docstring 内のパス文字列 `InformationTheory/…` / `InformationTheory.…`(lib `.lean` 多数)。
- `docs/**/*.md`(322 箇所):アクティブな plan/inventory は更新、proof-logs 等の履歴は凍結可。
- `docs/metrics/*.{json}`(18):manifest のモジュールパス。再生成で済むものは再生成。
- `README.md`(`common-2026` → 新名 or 据え置き)、`CLAUDE.md`(随所)、
  `scripts/*.txt`(生成物、再生成可)、`scripts/session_metrics.ts`、`docs/textbook/site/build.mjs`。
- これらは段階的に複数コミットで可。

## リスク / 注意

- **Phase 1 は原子的に**。中途半端な状態(import だけ直してディレクトリ未改名 等)は
  全面ビルド不能。1 コミットに収める。
- **B 層の無言失敗**:`` `InformationTheory `` リテラル置換漏れは、コンパイルは通るのに
  orphan/entry-point 検出が空になる。Phase 1 step 7 の動作確認で必ず検出する。
- **full build コスト**:本タスクは inner-loop の単一ファイル検証では閉じない。
  Phase 1 と Phase 2 の各完了時に full `lake build`(数分)が要る。
- **GitHub リポジトリ名 / `common-2026` ディレクトリ名**:lakefile の `name` は
  ライブラリ名(`InformationTheory`)であり、リポジトリのフォルダ名 `common-2026` とは別物。
  フォルダ名・リポジトリ名まで変えるかは別判断(ローカルパス・worktree boilerplate・
  loogle index パス等への波及があるため、変えるならさらに別 Phase)。

## ざっくり工数感

- Phase 1(必須):機械置換自体は 10 分程度だが、full build 待ち(数分)込みで 1 セッション内。
- Phase 2(任意):置換 + build。30 分〜。
- Phase 3(任意):掃除範囲しだい。履歴凍結なら小、全置換なら中。
