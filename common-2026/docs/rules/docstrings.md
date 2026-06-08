# docstring 規約

Mathlib のドキュメント規約（<https://leanprover-community.github.io/contribute/doc.html>、linter `DocString.lean` / `DocPrime.lean`）から本プロジェクトに適用する分。スタイル全体は [`lean-style.md`](lean-style.md)。

本リポジトリの docstring は独自進化している。以下では **Mathlib の目標形** を先に示し、続けて **本リポジトリの乖離点とあるべき形** を挙げる。プロジェクト固有タグ（`@residual` / `@audit:*`）との同居は最後の節。

## コメント 4 種の使い分け

| 記法 | 用途 | doc 生成 |
|---|---|---|
| `/-- … -/` | 宣言 docstring（def / theorem / instance / フィールド） | ○ |
| `/-! … -/` | module docstring・ファイル内の見出し / 区切り | ○ |
| `/- … -/` | 技術コメント（TODO / 実装メモ）、証明中コメント | × |
| `--` | 短い / 行内コメント | × |

ドキュメントになるのは `/--` と `/-!` だけ。

## 宣言 docstring (`/-- … -/`) の目標形

1. **付ける対象**: すべての def と主要 theorem に必須。補題にも推奨（特に数学的内容 / ファイル跨ぎで使うもの）。
2. **数学的意味を述べる**完全な文で始める。「実装について多少 *嘘をついてよい*」（意味を伝えることが優先、実装の細部より）。
3. 完全文なら **末尾ピリオド**。
4. Lean 識別子は **バッククォート** `` `DotEq` ``。完全修飾名 `` `Real.log_mul` `` はオンライン doc でリンクになる。
5. **named theorem は太字** `**…**`（例: `**mean value theorem**`）。— 太字はここに限る（下記乖離点参照）。
6. **継続行を字下げしない**（宣言 docstring では）。
7. 数式は `$ … $`（inline）/ `$$ … $$`（display）。URL は山括弧 `<…>` で囲む（クリック可能化）。
8. 名前が `'` で終わる宣言は、`'` の理由（unprimed 版との差 / より良い命名が無い理由）を docstring で説明する（`DocPrime` linter）。
9. 空 docstring は警告（`DocString.empty`）。

## module docstring (`/-! … -/`) の目標形

ファイル先頭の import 群の直後（本プロジェクトは copyright header を置かない → [`lean-style.md`](lean-style.md)）。**継続行は 2 スペース字下げ**（markdown 要件。宣言 docstring と逆なので注意）。atx 見出し（`#`、下線式ダッシュ不可）。

セクションはこの順:

1. `#` タイトル（必須）
2. ファイル内容の要約
3. *Main definitions* / *Main statements*（要約に含めるなら省略可）
4. *Notation*（表記法を導入したら必須）
5. *Implementation notes*（設計判断・型クラス・simp 正規形）
6. *References*（教科書 / 論文 / Wikipedia。`docs/references.bib` の BibTeX を `[Key]` で参照）
7. *Tags*（テキスト検索用キーワード）

本文は日本語で可（本プロジェクトの実態。識別子は英語のまま）。

## 本リポジトリの乖離点とあるべき形

| 乖離点（独自進化） | Mathlib のあるべき形 | 対応 |
|---|---|---|
| **宣言 docstring の継続行を 2 スペース字下げ** | 宣言 `/--` の継続行は開始 `/--` のカラムに揃える（トップレベルは字下げしない、フィールドはフィールド列に揃う）。2 スペース字下げは module `/-!` だけ | ✅ トップレベル分は一括除去済（11 ファイル）。フィールド docstring は既に `/--` 列に揃っており対象外。新規も字下げしない |
| **ほぼ全 docstring を `**ラベル**:` で太字始まり** | 太字は **named theorem に限る**。通常の topic ラベルは太字にしない（地の文で書く） | 新規は太字を named theorem に限定。既存は無理に剥がさない（無害） |
| **末尾ピリオド無し**（特に日本語終わり） | 完全文なら末尾ピリオド | 新規は付ける。日本語文末は「。」で可 |
| 散文が日本語 | Mathlib は英語のみ | **本プロジェクトでは散文は日本語可**（[`README.md`](README.md) のとおり。識別子は英語） |

継続行字下げの一括除去は完了（トップレベル宣言 docstring）。残る乖離（太字始まり・末尾ピリオド無し）は無害なので一括移行せず、新規 / 編集時に随時 Mathlib 形へ寄せる。

## プロジェクト固有タグとの同居

本リポジトリは docstring 内に honesty / audit システムのタグを書く（110 箇所）。これらは **Mathlib に無い本プロジェクト固有の拡張**で、**配置規約は `docs/audit/audit-tags.md` が SoT**（本ファイルは重複定義しない）。要点だけ:

- `@residual(<class>:<slug>)`: `sorry` の分類。単一 sorry は **docstring 末尾**、複数 sorry は各 sorry の直前行コメント。
- `@audit:*`: 必ず **docstring 内**（行コメント不可。declaration とライフサイクルを揃え grep で pair 取得するため）。

**レイアウト**: Mathlib 形の散文 docstring を**先**に書き、固有タグは**その後ろ**に置く。散文（数学的意味）とタグ（incompleteness / 監査マーカー）の役割を分離する。

```lean
/-- `DotEq` の乗法両立性: 正値性の下で `a₁ * a₂ ≐ b₁ * b₂`。
`Real.log_mul` で `log(a₁·a₂) - log(b₁·b₂)` を和に分解する。

@residual(wall:some-slug) -/
lemma DotEq.mul … := by sorry
```

固有タグの語彙・分類・honesty 階層は `docs/audit/audit-tags.md`、ワークフロー上の意味は `CLAUDE.md`「Verification honesty」を見る。
