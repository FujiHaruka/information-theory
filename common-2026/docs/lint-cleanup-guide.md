# Lint cleanup guide (mathlibStandardSet 実害系)

lakefile で `weak.linter.mathlibStandardSet = true` を有効化した結果出る lint warning のうち、
**実害系カテゴリだけ**を潰す作業の共通手順。style 系（ヘッダ/長行/show 等）は別タスクなので触らない。

## 対象 / 非対象リンター

**修正する（実害系、6カテゴリ）:**
- `linter.unusedDecidableInType` — 型で未使用の `[DecidableEq _]` / `[Decidable _]`
- `linter.unusedVariables` — 未使用のローカル変数 / binder
- `linter.unusedSectionVars` — 型・proof 両方で未使用の section variable
- `linter.flexible` — flexible tactic（`simp` 等）が後続に脆く依存
- `linter.unnecessarySimpa` — 不要な `simpa`
- `linter.style.multiGoal` — 複数 goal がある状態でのフォーカス漏れ

**触らない（出ても無視）:**
- `linter.unusedFintypeInType` — **lakefile で無効化済み**（このコードベースは Fintype 前提で proof が
  `Fintype.card`/`∑` を実使用するため修正不能。検証時は `-Dlinter.unusedFintypeInType=false` で消える）。
- style 系: `linter.style.header`（Copyright too short）/ `linter.style.longLine` / `linter.style.show`
  / `linter.style.whitespace` / `linter.style.maxHeartbeats` / `linter.style.docString`

## 1ファイルあたりのループ（行番号ドリフト対策で必ず再導出）

**重要**: 素の `lake env lean <file>` は lakefile の leanOptions を適用せず、デフォルト
リンターしか走らない。lib build と同じリンターセットにするには**必ず2フラグを付ける**
（`mathlibStandardSet` を on、`unusedFintypeInType` を off にして lakefile と一致させる）:

```
lake env lean -Dlinter.mathlibStandardSet=true -Dlinter.unusedFintypeInType=false <file> 2>&1 | grep -E 'error|warning'
```

を走らせ、出力から**上記6カテゴリの warning だけ**を拾って修正 → 再実行 → 6カテゴリが 0 になるまで反復。
`error:` が出たら直前の編集が proof を壊している → 下記パターンで対処。
style 系 warning が残るのは想定どおり（無視してよい）。

完了条件: 上記2フラグ付き `lake env lean` が **0 error** かつ **対象6カテゴリの warning が 0**。

## 修正パターン（検証済み）

### unusedDecidableInType
warning 例:
```
`foo` does not use the following hypothesis in its type:
  • [DecidableEq X] (#3)
```
これは section の `variable {X} [Fintype X] [DecidableEq X] ...` がレンマに自動 include され、
**型には現れない**ために出る。直し方:

1. その decl の直前に `omit [当該インスタンス] in` を**追加**する（`omit` は docstring/属性より**前**に置く。
   docstring と decl の間に置くと `unexpected token 'omit'` になる）。既に `omit [...] in` があれば
   そこへ追記してまとめる（例: `omit [Nonempty X] in` → `omit [DecidableEq X] [Nonempty X] in`）。
2. 2フラグ付き `lake env lean` で再検証。**proof が DecidableEq を使っていると error になる**ので、
   その時は proof 冒頭に `classical` を1行足す（classical が DecidableEq インスタンスを供給）。これで
   **原則すべて解消可能**。term-mode 証明（`:= ⟨...⟩`）で classical が必要なら `:= by classical exact ⟨...⟩`
   に変換（数学的中身は不変）。
3. 1つの omit が unusedSectionVars と unusedDecidableInType を同時に解消することが多い。

注意: 削除は consumer 側を壊さない（consumer は強いインスタンスを持っているので OK）。
リスクは当該 proof のコンパイルのみ。全体の consumer 破壊チェックはオーケストレーター側で最後に
`lake build` する。

### unusedVariables
未使用のローカル変数 / binder。`intro h`（h 未使用）→ `intro _`、`fun x _ => ...`、
`rintro ⟨a, _⟩`、未使用 `have h := ...` は名前を `_` にするか削除。warning が指す変数名を `_` 化。

### unusedSectionVars
型・proof 両方で未使用の section variable。`omit [当該変数] in` を decl 直前に追加。
（`unusedDecidableInType` と違い proof でも未使用なので `classical` 不要、安全に omit できる。）

### flexible
warning 例: `'simp' is a flexible tactic modifying '⊢'. Try 'simp?' and use the suggested 'simp only [...]'`。
直し方: 当該 `simp` を一旦 `simp?` に変えて `lake env lean` を走らせ、出力の
`Try this: simp only [...]` をコピーして `simp only [...]` に置換 → 再検証。
（`simp_all` → `simp_all only [...]`、`dsimp` → `dsimp only [...]` も同様。）
simp only の集合が巨大でも、それが sanctioned な直し方。挙動が変わって proof が壊れたら
元の `simp` に戻し、その1件はスキップして次へ。

### unnecessarySimpa
`simpa using e` で simp 不要 → `exact e`、`simpa` 単独 → `simp`。warning / `lake env lean` の
示唆に従う。置換後に proof が通ることを確認。

### multiGoal
複数 goal がフォーカスされていない箇所。`·`（cdot）で各 goal を囲む、`<;>`、`all_goals`、
`constructor <;> ...` 等で1 goal ずつに。warning が指す tactic を focus する。

## 禁止 / 厳守

- `sorry` / `@residual(...)` / `@audit:*` タグには**一切触れない**。proof の数学的中身を変えない
  （omit / classical / simp only / `_` 化 / focus のみ。新しい補題化・仮定追加・結論変更は禁止）。
- 通らない1件は**無理に通さずスキップ**（元に戻す）。全カテゴリを潰しきれなくても、壊さないことが優先。
- style 系リンター（header/longLine/show 等）は触らない。
- 各ファイル完了時に2フラグ付き `lake env lean` が 0 error であることを必ず確認してから次へ。
