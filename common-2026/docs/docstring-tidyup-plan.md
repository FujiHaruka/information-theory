# docstring tidy-up plan — Mathlib スタイルへの寄せ込み

**Status**: ACTIVE (2026-06-13 起票) / **Parent**: なし (standalone) /
**関連**: 規約 SoT [`rules/docstrings.md`](rules/docstrings.md) ・実測 [`mathlib-conventions-gap.md`](mathlib-conventions-gap.md) ・honesty タグ SoT [`audit/audit-tags.md`](audit/audit-tags.md)

分割リファクタ (footprint の裾を named lemma に割る) に着手する**前に**、既存 docstring を Mathlib スタイルへ整える。
docstring が綺麗だと、後続の概念分割で切り出し単位を判断しやすくなる。

## Context

実測 ([`mathlib-conventions-gap.md`](mathlib-conventions-gap.md) §1.4):

- **文書化率**: Mathlib は宣言の ~17–20% しか docstring を持たない (def + headline 定理が中心、補助補題は裸)。
  本プロジェクトは private 含め ~94%。= 大幅な過剰文書化。
- **プロセス語彙の混入**: docstring / module doc に `Phase A/B`・`Wall N`・`判断 #X`・`Retraction log`・`撤退ライン`
  といった**開発プロセス情報**が蓄積 ('Phase' は 187 ファイル、'撤退' 42、'判断' 28)。
  Mathlib の永続ドキュメントは数学だけを語り、control state / 決定履歴は語らない。
- **decision (2026-06-13)**: 補助補題の docstring は **Mathlib 流に大幅に削る** (ユーザー決定)。
  現行 [`rules/docstrings.md`](rules/docstrings.md) の「補題にも推奨」と方針が変わる → 規約も改訂する。

宣言内訳 (2026-06-13 実測):

| 区分 | 数 | 扱い |
|---|---|---|
| def / abbrev | 445 | **保持**して中身整理 (Mathlib も def は文書化必須) |
| structure / class / inductive | 33 | **保持** |
| theorem / lemma | 2176 | 削る候補母集団 |
| `@[entry_point]` 付き | 709 | **保持** (headline = main results) |
| `@residual` 保持 | 66 | **保持必須** (honesty 台帳) |
| `@audit:` 保持 | 644 | **保持必須** (タグだけ残し散文は削れる) |

## Approach

**2 つの結合したワークストリームを、ファイル単位で 1 パスにまとめて適用する** (全ファイルを 2 回走査しない):

1. **module doc 整形** — [`rules/docstrings.md`](rules/docstrings.md) のテンプレ順序へ寄せ、
   プロセス語彙の散文を除去/移設し、`## Main results` に headline を捕捉する。
2. **宣言 docstring の選別削除** — 下記 keep/strip ルールで、内部補助補題の**散文**を削る。
   honesty タグは残す。名前が事実を語れない補題は削らず最小 1 行に留める (name-adequacy gate)。

**順序**: 規約改訂 (新ポリシー = SoT 化) → 1 ファミリで pilot して削除ルールと「整形後の形」を較正
→ ファミリ単位で展開 → 検証 (text-only ゆえ compile 影響なし。最後に full build + tag 数保存 + pre-commit)。

**なぜこの形か**:

- module doc と宣言 docstring は結合している。補助補題の散文を削ると、その意味の置き場所は module doc の
  `## Main results` / `## Main definitions` に移る。だから「削る」と「main results 捕捉」は同一パスで行う。
- 純 doc 編集は**コメントだけ**を触るので elaboration に影響しない (= compile が壊れない)。
  rename を**この pass では行わない**ことで text-only を保ち、ファミリ並列 / 高速化を可能にする。
- 「2 割まで下げる」という数値は**追わない**。タグ保持 (644+66) と entry_point (709) と def (478) を残すため、
  文書化率は構造的に Mathlib より高く着地する。意味ルール (補助補題の散文を削る) で削る。

## Keep / Strip ルール (新ポリシー)

宣言 docstring の**散文**は、宣言が次のいずれかなら **keep**(整える):

- `def` / `abbrev` / `structure` / `class` / `inductive` (Mathlib docBlame と同じ: 定義は文書化必須)
- `@[entry_point]` 付き / module doc の `## Main results` に挙がる headline 定理
- `@residual(...)` / `@audit:*` を持つ宣言 — ただし**散文は削ってタグだけ残してよい**
  (例: audit:ok の補助補題は散文を削り `/-- @audit:ok(...) -/` だけ残す)

上記以外 (= 内部の補助 theorem / lemma) は散文を **strip**。ただし **name-adequacy gate**:

- 削る前に「Mathlib 流の名前が statement を語れているか」を確認する。
- 語れている → 散文を削る (docstring ごと削除、タグが無ければ)。
- 語れていない → **削らず最小 1 行**の数学的 docstring に縮める + rename 候補として別リストに記録
  (rename は dep graph に波及するので**この pass ではやらない**。後続の分割/命名 pass で処理)。

## Hard invariants (違反したら DEFECT)

1. **honesty タグを落とさない**: `@residual` (66) / `@audit:` (644) の総数は pass 前後で**不変**。
   タグを含む docstring を丸ごと削除してはならない (散文だけ削り、タグ行を残す)。
   pre-commit hook が「sorry に @residual 無し」を BLOCK するので安全網はあるが、依存しない。
2. **main results を捨てない**: 補助補題の散文を削る前に、その意味が名前 or module doc で拾えることを確認。
3. **compile を壊さない**: コメント以外を触らない。最後に full `lake build` で 0 error 確認。
4. **rename しない (この pass では)**: 名前が不十分でも削るのでなく最小 1 行に留める。

## Phases

### Phase 0 — 規約改訂 (SoT 化)

- [`rules/docstrings.md`](rules/docstrings.md) を新ポリシーへ改訂: 「補題にも推奨」→
  「def/structure/class/inductive + headline(@[entry_point]) + タグ保持宣言のみ文書化。
  内部補助補題は名前で語らせ裸 (name-adequacy gate)」。
- module doc のプロセス語彙除去ルールを明文化 (Phase/Wall/判断/Retraction/撤退 の散文は plan/handoff へ移すか削除。
  数学的・構造的な設計判断のみ `## Implementation notes` に残す)。
- linter 方針の追記 (docBlame 非対称: def には docstring 要求、theorem/lemma には要求しない。
  pre-commit / plan_lint への弱い enforcement は分割リファクタ後に判断 → 本 pass では linter 化しない)。

### Phase 1 — pilot (1〜2 ファイルで較正)

- 概念集中型で Phase 散文を持つ代表ファイル (例 `Shannon/Stein.lean`) と、
  プロセス語彙が濃いファイル 1 本で両ワークストリームを適用。
- diff をレビューし、keep/strip 境界・name-adequacy gate の運用・整形後の module doc 形を確定。
- pilot で確定した「before/after の見本」をこの plan か rules/docstrings.md に 1 例貼る。

### Phase 2 — ファミリ単位ロールアウト

- ファミリ (Shannon/AWGN, EPI, SlepianWolf, Fano, Probability, …) ごとに 1 パスで両ワークストリーム適用。
- 純 doc 編集 (text-only) なので worktree 不要。ファミリ間でファイル所有を分離すれば並列も可
  ([`.claude/guides/agent-dispatch-guide.md`](../.claude/guides/agent-dispatch-guide.md) の docs-only 例外)。
- 各ファミリ完了時に tag 数 (@residual/@audit) を before/after で照合。

### Phase 3 — 検証 / メトリクス

- full `lake build InformationTheory` 1 回 (0 error)。pre-commit 0 BLOCK。
- tag 保存確認: `@residual` / `@audit:` 総数が起票時と一致。
- プロセス語彙残量: docstring/module doc 内の Phase/Wall/判断/Retraction/撤退 が near 0。
- 文書化率の推移を記録 (94% → 着地値。数値目標ではなく副指標)。

## DoD

- proof done / proof 内容は**不変** (これは純 doc tidy であって proof には触れない)。
- 上記 Hard invariants 4 点を全て満たす。
- 新ポリシーが [`rules/docstrings.md`](rules/docstrings.md) に反映済 (= SoT 更新済)。
- honesty audit は**不要** (新規 sorry/@residual を導入しないため)。タグ数保存で代替検証。

## Risks & mitigations

| リスク | 緩和 |
|---|---|
| 散文削除で hard-won な理解を喪失 | name-adequacy gate (名前が語れない補題は削らず最小化)。git 履歴が全文保持。pilot で較正。 |
| honesty タグを巻き込んで削除 | invariant #1 (タグ数保存照合) + pre-commit BLOCK の二重網。 |
| プロセス散文と正当な Implementation note の誤判定 | 数学的/構造的(型クラス選択・simp 正規形・定義形の理由)は残す。開発履歴(Phase 順序・Retraction・撤退・判断番号)のみ削る。 |
| 並列編集で main がドリフト | ファミリ単位でファイル所有分離。text-only ゆえ衝突は git index のみ → 逐次 commit。 |

## Decision log

- 2026-06-13: 補助補題 docstring は Mathlib 流に**大幅削除**する方針をユーザー決定。rules/docstrings.md 改訂を Phase 0 に含める。
- 2026-06-13: 文書化率の数値目標 (2 割) は追わない。タグ/entry_point/def 保持で構造的に高く着地するため、意味ルールで削る。
- 2026-06-13: rename はこの pass のスコープ外 (text-only 維持 + dep 波及回避)。名前不十分は最小 1 行 + 別リスト記録に留める。
