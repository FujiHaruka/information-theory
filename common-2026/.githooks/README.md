# .githooks — git 管理された pre-commit hook

`pre-commit` は **テキスト検査のみ (lake compile 無し、一瞬)** で、本プロジェクトの再発失敗モード
(honesty 規律 / import policy) を最安段階で止める。compile-check はあえて載せない (cold olean で
分単位になり高頻度自走コミット + inner-loop 検証と冗長。compile 保証が要るなら非同期で別途)。

## 有効化 (clone / 新環境で 1 回)

`core.hooksPath` はローカル config なので commit されない。各環境で 1 回:

```bash
git config core.hooksPath common-2026/.githooks
```

(リポジトリ root = `/Users/haruka/dev/lean-projects` 基準の相対パス。worktree でも committed な
本ディレクトリがそのまま効く。)

## 何をチェックするか (対象: staged な `**/InformationTheory/**.lean`)

| 種別 | 条件 |
|---|---|
| **BLOCK** | bare `import Mathlib` を新規追加 (pinpoint import policy 違反) |
| **BLOCK** | `sorry` を追加したのに file 内に `@residual` タグが皆無 (type-check done 要件) |
| WARN | sorry 数 > @residual 数 (undercount の疑い) |
| WARN | `@residual(<class>:...)` の class が `plan` / `wall` / `defect` 以外 |
| WARN | deprecated tag (`@audit:suspect` / `staged` / `defer` / 散文 `🟢ʰ`) を新規追加 |
| WARN | 新規 `InformationTheory/X.lean` が aggregator `InformationTheory.lean` に未 import |

docs-only コミットは対象ファイルが無いので即通過。意味的 honesty defect (核 bundling / 循環 `:= h` /
退化定義悪用) は grep 不能なので **対象外** — そこは `honesty-auditor` の領域 (線引きは意図的)。

## Bypass

```bash
SKIP_LEAN_HOOK=1 git commit ...   # または
git commit --no-verify ...
```

WIP チェックポイントや意図的な暫定コミットで使う。
