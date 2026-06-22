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

1. **付ける対象（Mathlib docBlame 非対称）**: docstring を**必須**とするのは
   `def` / `abbrev` / `structure` / `class` / `inductive` と、headline 定理
   （`@[entry_point]` / module doc の *Main results* に挙がるもの）。
   **内部の補助 theorem / lemma には原則付けない** — 名前で statement を語らせる
   （Mathlib は補助補題をほぼ裸にしており、文書化率は宣言全体の ~17–20%）。
   - **name-adequacy gate**: 名前が statement を語れない補題だけ、最小 1 行の数学的 docstring を付ける
     （本来は語れる名前へ rename するのが筋だが dep graph に波及するので別 pass）。
   - `@residual(...)` / `@audit:*` を持つ宣言は docstring を**保持**する（散文は削ってタグだけ残してよい）。
   - 背景の実測と移行計画 → [`../mathlib-conventions-gap.md`](../mathlib-conventions-gap.md) §1.4 /
     [`../docstring-tidyup-plan.md`](../docstring-tidyup-plan.md)。
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

本文は**英語で書く**（識別子も英語）。将来の Mathlib PR を見据え、コード表面（`.lean` の docstring / コメント）の散文は英語に統一する（2026-06-13 方針転換 → [`../docstring-tidyup-plan.md`](../docstring-tidyup-plan.md)）。内部の plan / handoff（`docs/**/*.md`）は作業言語として日本語のままでよい。

**プロセス語彙を永続記録に書かない**: `Phase A/B`・`Wall N`・`判断 #X`・`Retraction log`・`撤退ライン`
といった**開発プロセス / control state / 決定履歴**は module doc にも宣言 docstring にも書かない
（Mathlib の永続ドキュメントは数学だけを語る）。これらの置き場所は plan / handoff
（`docs/**/*-plan.md` / `.claude/handoff.md`）。コードに残すのは**数学的・構造的な設計判断のみ**
（型クラス選択・simp 正規形・定義形を選んだ理由）で、*Implementation notes* に書く。
honesty タグ（`@residual` / `@audit:*`）はプロセス語彙ではなく**残す**（下記「プロジェクト固有タグとの同居」）。

## 本リポジトリの乖離点とあるべき形

| 乖離点（独自進化） | Mathlib のあるべき形 | 対応 |
|---|---|---|
| **宣言 docstring の継続行を 2 スペース字下げ** | 宣言 `/--` の継続行は開始 `/--` のカラムに揃える（トップレベルは字下げしない、フィールドはフィールド列に揃う）。2 スペース字下げは module `/-!` だけ | ✅ トップレベル分は一括除去済（11 ファイル）。フィールド docstring は既に `/--` 列に揃っており対象外。新規も字下げしない |
| **ほぼ全 docstring を `**ラベル**:` で太字始まり** | 太字は **named theorem に限る**。通常の topic ラベルは太字にしない（地の文で書く） | 🔧 完全文の地の文へ書き換え中（2026-06-22 能動移行、tidyup-plan Phase 4）。太字は inline named-theorem 言及のみ残す |
| **補助補題までほぼ全部 docstring（~94%）** | 補助補題は裸（Mathlib ~17–20%）。文書化は API 表面（def + headline）のみ | 🔧 [`../docstring-tidyup-plan.md`](../docstring-tidyup-plan.md) で内部補助補題の散文を選別削除中。新規は付けない（name-adequacy gate） |
| **docstring / module doc にプロセス語彙**（Phase/Wall/判断/Retraction/撤退） | 永続記録は数学のみ。プロセスは plan / handoff へ | 🔧 同 plan で除去/移設。数学的・構造的な設計判断のみ *Implementation notes* に残す |
| **末尾ピリオド無し** | 完全文なら末尾ピリオド | 🔧 bold-label pass と同時に付与中（2026-06-22、Phase 4）。formula 末尾は不要 |
| **散文が日本語** | Mathlib は英語のみ | 🔧 **英語へ全面移行**（コード表面の docstring / コメント）。[`../docstring-tidyup-plan.md`](../docstring-tidyup-plan.md) で移行中。新規は英語で書く |

継続行字下げの一括除去は完了（トップレベル宣言 docstring）。残る乖離（太字始まり・末尾ピリオド無し）は 2026-06-22 に能動一括移行へ切替（[`../docstring-tidyup-plan.md`](../docstring-tidyup-plan.md) Phase 4）。

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
