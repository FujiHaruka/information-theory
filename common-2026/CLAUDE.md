# InformationTheory Project Rules

A Lean 4 + Mathlib formalization project. Scope evolves; for the current focus see `docs/`.

## Project Layout

- `InformationTheory.lean` — library root. After adding a new file under `InformationTheory/`, append the corresponding `import` line here.
- `private` is **file-scoped, not namespace-scoped**. Sub-modules that share `private` helpers must live in the same file, or those helpers leak as public symbols.
- `docs/` holds source materials (PDFs / plans / inventories) and per-task `proof-log-*.md` + `metrics/` outputs. Treat plan and inventory files as the source of truth for whatever is currently active.

## Build Setup

- This is a theorem-proving project, so **do not add a `[[lean_exe]]` target**. An executable target forces native compilation (`.c.o`) of all of Mathlib, which takes minutes.
- A single-file `lake env lean <file>` should finish within a few seconds once Mathlib oleans are warm. If it doesn't, suspect the imports.

## Import Policy

- **Do not use `import Mathlib`.** It pulls in 8000+ Mathlib modules as dependencies, making even a warm rebuild take 40+ seconds.
- Import only the specific tactics and lemmas you need. Add more imports only when something is actually missing.

## Verification

Prefer single-file `lake env lean <file>` over full project builds for the inner loop.

- **Primary — `lake env lean <file>`** is the definitive synchronous check. Silent output = clean. Run after each fill / edit when you want an explicit verdict.
- **Do NOT use `lake build` for verification.** It rebuilds every module and is too slow for the inner loop. Reserve it for one-off project-wide sanity checks after a large refactor.
- **After upstream edits, dependents may need olean refresh.** module A の public symbol / namespace / signature を変えると dependent が A の旧 `.olean` を拾い phantom `unknown identifier` を出すことがある → `lake build InformationTheory.<A>` で 1 度 refresh。

**「Mathlib 壁」判定は反証を 1 度試みてから受け入れる** (覆し ~40 件の真因はほぼ全て「別ルート or 反例を 1 つも探さずに断じた」)。`@residual(wall:slug)` を書く / lemma を「壁」と scope-out する **前に** 判定の向きに応じた反証を 1 回行い、最終判定は必ず実機械検証 (`lake env lean` + `#print axioms`) で裏取りする。監査 / 在庫の壁判定を鵜呑みにせず `proof-pivot-advisor` で別 lemma chain を在庫横断で再確認するのが定石。

- **壁と断じる側 (過大評価対策)**: loogle 0 件は *必要条件であって十分条件でない*。0 件の後に (a) **conclusion-shape 二段検索** (bare-identifier でなく `|- _ ≤ _` 等の subterm / conclusion pattern で再検索)、(b) **期待結論形に近い template lemma を 1 本挙げ self-build 行数を見積もる**。これが書けないなら壁判定保留。詰まりが「命題が Mathlib に無い (真の gap)」か「既存 asset への配線 (import cycle 含む plumbing)」かを区別する。
- **family 丸ごと壁 / scope-out と断じる前 (gateway-atom-first)**: その family の決定的 atom 1 本を `lean-implementer` に実装 dispatch して通るか試してから判定する。
- **非壁 / 仮説 OK と断じる側 (過小評価対策)**: 受け入れる前に **small-case で反例を 1 度探す** + **退化境界を 1 つ代入** (`=0` / Dirac / 非可積分 / `N=0`) して statement が生きているか確認する。述語の signature が constraint を落としていないか (`*_def` の Read) を確認。具体的数値・型の予測は「具体的数値・型予測の verbatim 確認」節に従う。

壁判定の必須メタデータ・cause タグ・覆し分析テーブル → `docs/audit/audit-tags.md`「壁判定の必須メタデータ」。

- **pre-commit hook** (git 管理、テキスト検査のみ、lake 不使用): `common-2026/.githooks/pre-commit` が staged `InformationTheory/**.lean` に honesty/import 規律を検査 (BLOCK: bare `import Mathlib` 追加 / `sorry` 追加で `@residual` 皆無。WARN: residual undercount・class 語彙外・deprecated tag・新規 file の import 未登録)。bypass は `SKIP_LEAN_HOOK=1 git commit ...` か `--no-verify`。新環境では `git config core.hooksPath common-2026/.githooks` で有効化 (詳細 → `.githooks/README.md`)。

## Mathlib API Search (loogle)

For "does Mathlib have lemma X?" questions, **try `loogle` before `rg`/`grep`**. Loogle answers authoritatively (e.g., `Found 0 declarations`); negative grep can miss differently-named lemmas.

- **One-time index build** (~2 min, ~350 MB, gitignored under `.lake/`):
  ```bash
  mkdir -p .lake/build && lake exe loogle --write-index .lake/build/loogle.index
  ```
- **Per-query** — invoke the binary directly (skip `lake env`):
  ```bash
  ./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "<query>"
  ```
  Cost: ~8.5 s/query with index vs ~60 s cold via `lake exe loogle`.
- **Query syntax**:
  - **Full namespace required**: `MeasureTheory.Measure.map` not `Measure.map`. Loogle prints "Maybe you meant: ..." with the right qualifier.
  - **Subterm pattern**: `Foo.bar (Baz.qux _ _) (Baz.qux _ _)` finds `Foo.bar` applied to two `Baz.qux`.
  - **Multi-term (any of)**: comma-separated, e.g. `Foo.bar, Baz.qux` finds lemmas mentioning both.
  - **Conclusion pattern**: `|- _ ≤ _` finds inequalities.
- **Fall back to `rg`** for text-level searches: comments, docstrings, file-structure exploration, or pattern matches not tied to a specific identifier.

## 依存 / consumer 逆引きツール (`scripts/dep_*.sh`)

プロジェクト内 declaration の依存関係を機械的に引く。実体は `scripts/DepGraph.lean` (`import InformationTheory`)。`rg` のテキスト一致と違い **term レベルの真の参照** を拾う (docstring / コメントの言及は数えない)。3 モード:

- **`scripts/dep_consumers.sh <完全修飾名> [--transitive]`** — **逆依存 (consumer graph)**。指定 decl を *直接参照している* InformationTheory decl を `file:line` 付きで列挙。**共有補題の signature を変更 (仮説 threading 等) する前に必ず 1 度引く** — ripple (touch が要る decl 群) を初回 brief に正確に載せる前提作業。`--transitive` で full blast radius (推移閉包)。
- **`scripts/dep_graph.sh <完全修飾名>`** — forward 依存グラフ (root が何に依存するか) を Graphviz dot で出力。`--svg`/`--png` で画像化。
- **`scripts/dep_rank.sh [N]`** — `@[entry_point]` 限定で推移的依存数の多い順ランキング。

注意: いずれも root olean を読む。最近追加した decl が「未知の declaration」と出たら root が stale → `lake build InformationTheory` で refresh してから再実行。各 `-h` でオプション一覧。

## Subagent Inventory of Mathlib Lemmas

When delegating Mathlib API inventory to a subagent ("find candidate lemmas for X"), require **structured per-lemma output**, not prose summaries. For each candidate, the subagent must record:

- **`file:line` location** (e.g., `Mathlib/Foo/Bar.lean:123`).
- **Full signature**, including the **`[...]` type-class prerequisites verbatim**. Do not let the subagent paraphrase or drop brackets.
- **Argument types** (explicit and instance), in order.
- **Conclusion form**, copied verbatim — not paraphrased into prose.

Type-class prerequisites in particular leak silently into your main theorem the moment you apply the lemma. A missed `[StandardBorelSpace _]`, `[IsFiniteMeasure _]`, `[Countable _]` etc. forces a mid-proof pivot of the surrounding statement (or worse, of the definition itself). Reject subagent output that summarizes signatures or omits brackets, and re-prompt.

## Mathlib-shape-driven Definitions

When introducing a new definition that will be reasoned about via existing Mathlib lemmas, do **not** transcribe the textbook formulation directly. Before finalizing the definition:

1. Identify the 1–3 Mathlib lemmas you expect to dominate proofs about this definition.
2. Read their **conclusion form** verbatim — what shape do they return?
3. Choose the definition so those conclusion forms are usable as-is.

The textbook-equivalent form can be re-derived as a separate equivalence lemma later if needed. Skipping this step routinely forces a mid-proof definition pivot or 50–100 lines of self-written bridge lemmas to convert between "the form Mathlib hands you" and "the form your proof expects". A red flag that you skipped this step: you find yourself searching for "the lemma that turns `f (compProd ...)` into `∫⁻ ... ∂ ...`" or any analogous re-shaping bridge. If that bridge is not in Mathlib, the cheapest fix is almost always to redefine, not to write the bridge.

This rewrite is also the **第一選択 mitigation** when a definition / `Prop` RHS / `inductive` constructor can't accept `sorry` directly (`sorry` lives in proof body only). Convert the def's core into a separate `theorem` whose body is `sorry` + `@residual(<class>:<slug>)`, and have the def call that theorem (or a shared sorry lemma — `docs/audit/audit-tags.md`「共有 Mathlib 壁」). The fallback when rewrite isn't feasible — keep the signature as a defect-marked tier-5 placeholder — is under「検証の誠実性 → sorry を書けない箇所での対処順序」.

### 具体的数値・型予測の verbatim 確認 (plan / inventory 共通)

Plan / inventory で具体的な **数値・型値** (例: `differentialEntropy (Dirac 0) = ?`、ある関数の `.toReal` 値、境界 case の `≠ 0` / `= 0`) を**予測**する箇所は、書き出す前に **実コード verbatim 確認** (Mathlib lemma + InformationTheory file の該当行を Read) を必ず行う。予測値が誤りだと、それを前提に組まれた撤退ライン / 退化境界 / 戦略選択がすべて drift する。「常識的にこの値だろう」「-∞ になるはず」のような直感は信用しない — Mathlib / InformationTheory の境界 case 定義は `Real` / `EReal` / `ℝ≥0∞` で慣行が異なり、Dirac / 退化 measure の値は特に直感と乖離しやすい。

確認方法: Mathlib API → loogle で完全 namespace 検索後 verbatim signature を Read。InformationTheory 内定義 → `rg` で grep → 該当行 Read。

同じ verbatim 確認義務は **依存方向 / Phase 順序 / wrapper 呼出方向 / import cycle** にも適用される (orchestrator brief で in-mind 仮定したそれらを subagent が verbatim 検証で逆順修正する提案は accept がデフォルト)。

## Skeleton-driven Development

Do **not** write a whole proof file in one shot. Instead:

1. Sketch the file as a skeleton: state every helper lemma and theorem with `:= by sorry`, plus the namespace and imports.
2. After Write, wait for the LSP `<new-diagnostics>` reminder. Confirm the skeleton type-checks (only `sorry` warnings expected).
3. Fill in **one** `sorry` at a time. Trust the LSP diagnostic reminder for fast feedback; reach for `lake env lean <file>` when you want a synchronous confirmation.
4. Let the diagnostics tell you when a tactic doesn't fire or a case is missing, instead of pattern-matching in your head.
5. **Dead-end は `sorry` で抜く**: 詰まったら signature を本来証明したい形に保ち、body を `sorry` のまま残し `@residual(<class>:<slug>)` を付与する (配置 + 語彙 → `docs/audit/audit-tags.md`)。`*Hypothesis` predicate に核を bundling する撤退は禁止 (→「検証の誠実性」)。`sorry` は正直な未完成マーカーとして commit してよい (→「Definition of Done」)。

## Parallel orchestration

Trigger: user が並列実行を明示要求 (「並列で」「N seed 並列」「並列実行」)。`Agent` + `isolation: "worktree"` で独立 seed を起動。**各 agent prompt には `.claude/guides/agent-dispatch-guide.md` の Standard boilerplate を必ず含める** (省略すると disk full / branch drift)。merge 後の cleanup 手順・Brief content checklist も同ガイドが SoT。

**単独 dispatch では worktree 不要**: 並列トリガーが無い単独 `lean-implementer` dispatch は `isolation` 省略 + main 直接作業で良い。worktree は並列時の disk / branch 衝突対策で、単独では merge / cleanup cost が増えるだけ。boilerplate の worktree symlink / ブランチ規律 / commit-push 分離は省略可 (main 上で自走 commit + push OK)。skeleton-driven / 検証 / scope / import / 撤退口は単独でも有効。

**Orchestrator role 規律**: 並列 dispatch を伴う作業では orchestrator 役の自分は **コード / docs を直接編集しない**。`Edit` / `Write` は subagent に dispatch し、自分は `git commit` / `git push` / TaskCreate / `git status` / `lake env lean` / `Read` 等の monitoring・調整のみ行う。trivial に見える 1-line patch でも brief を書いて投げる。handoff に「orchestrator が direct edit」とあっても (前 session の自分が書いたもの) 現 session では従わず subagent 化する (user redirect 優先)。例外は user が明示的に「自分でやって」と言った場合のみ。**並列を伴わない単独 session ではこの規律は適用外** (自由に直接編集してよい)。

**Exception — planner / docs-only agents**: `lean-planner` / `mathlib-inventory` / 監査系 agent は `docs/<family>/*.md` への書込みのみで Lean compile しないため worktree 隔離は不要 (harness が worktree dir を不完全に作り agent が main に直書きする failure mode あり)。docs-only 並列は `isolation` 省略 + brief で「触る file の所有権 (Agent N は file F のみ編集)」を明示するだけ。実装系 (`lean-implementer`) は **並列時のみ** worktree 隔離 + boilerplate 必要。

## Commits

- Commits and pushes are autonomous. Decide when to commit and push on each turn without waiting for the user to ask. The user will not give commit instructions. Commit autonomously even for changes that did not originate in the current session (e.g. uncommitted edits already on disk).
- Do not report commits or pushes. The user is not interested in commit/push activity. Skip mentioning them in turn summaries or status updates.
- Keep commit messages short. One concise line, no body unless absolutely necessary.
- **実装系 subagent は自走 commit することがある**: `lean-implementer` 等は brief に「commit するな」と書いても完了時に `git commit` 済のことがある。完了後は `git log --oneline -3` + `git status --short` で **既コミットの有無を確認してから** 差分のみ commit する (二重コミット防止)。`git add -A` は `.claude/worktrees/agent-*` の embedded repo を巻き込むため避け、対象 path を明示。

## Textbook site deploy

`docs/textbook/` の原稿を編集したら、確認を求めず **常に** サイトを再デプロイする (`docs/textbook/site/deploy.sh` を実行)。外向き公開だが毎回承認は不要 (ユーザー明言、原稿とライブサイトを常に同期させたい)。

- ワークフロー: ソース編集 → ビルド → commit → `deploy.sh` を自動実行。
- surge は処理エラーで初回失敗することがある (`payload.error.filename` undefined 系) — transient なので 1 回リトライすれば通る。

## Handoff

The `handoff` skill writes session state to `.claude/handoff.md` so the next session can `/carryon` from it. Default behavior is user-triggered, but autonomously invoke it at end-of-turn when **both**:

- the turn's work is finished and there is a clear, concrete next action, **and**
- this session is a continuation of a prior handoff (started via `/carryon`, or otherwise picking up an in-flight thread).

If the session is ad-hoc — opened with no prior handoff context, scope unrelated to any in-flight work — do not autonomously hand off; wait for explicit instruction.

**Interrupt trigger — malformed tool call が 2 件目で handoff + セッション終了** (ad-hoc でも override、上の both 条件を待たない): ツール呼び出しが `Your tool call was malformed and could not be parsed` で弾かれたら (開始タグが余計な先頭トークンや `antml:` プレフィックス欠落の素の `<invoke>` / `<parameter>` に化ける)、**1 件目は transient とみなして 1 回だけリトライする** (同じ呼び出しを最小ブロックで出し直し、壊れたトークンを散文に書かない = 自己増幅を断つ)。リトライが通れば通常続行。**2 件目 (リトライ失敗 or 別の独立再発) が出たら粘らず停止する**: (a) 安全なら進行中の atomic step だけ畳み、(b) `handoff` skill で状態 + 次の一手を書き出し、(c) user に「`/clear` → `/carryon` で新セッション再開」を促す。根拠: この failure は**総コンテキスト量と単調相関**し (高コンテキストほど多発・自己増幅 cascade)、低コンテキストの 1 件はほぼ独立ノイズだが再発は cascade の信号なので続行は悪化させるだけ。高コンテキスト域 (~260K 超) に自覚的に居るなら 1 件目でも即停止してよい。根本原因は harness バグでなく長コンテキスト下の特殊トークン忠実度低下 (背景 → memory `pitfall-agent-invoke-malformed`)。

**Single file 規約**: handoff は `.claude/handoff.md` **1 本のみ**。`handoff-<slug>.md` の named slot は作らない。複数 active line を並行管理する場合は 1 ファイル内をセクションで分割 (例: `## Line A — AWGN`, `## Line B — EPI/Stam`)。完全 closed なラインは handoff から削除し (履歴は git に残る)、必要なら `## Closure summary` セクションで参照のみ残す。session 終了時の handoff 書き出しは既存 line を上書きせず追記 (セクション追加) で merge する。

**gitignore 済み — commit しない**: `.claude/handoff.md` は意図的に gitignore されている (ローカル作業状態、追跡対象外)。「Commits」節の自走コミット対象から **除外** する。handoff を書いた後に `git add` / `git commit` を試みない (毎回 git に弾かれて gitignore と再発見するループになる)。

## Plan / docs hygiene

プランは「**制御状態** (scope/approach/next) / **判断履歴** / **確定事実** (sorryAx-free・壁・補題不在)」の3つを混ぜると肥大・stale 化する。寿命が違うので分離する。

**確定事実は prose にキャッシュしない (再導出 > キャッシュ)**:

- 機械再導出できる事実 (`sorryAx-free` / sorry 有無 / decl 存在) は plan 本文に書かず都度 `#print axioms` / `rg` で引く。prose キャッシュは無効化されず stale 化するので「再検証コストが安いなら毎回再導出」が正しい。
- 壁は `@residual(wall:slug)` がコード側 SoT。plan は slug にリンクし「X は壁」と本文に断定しない (壁が解消されると plan が誤った確定を伝播する)。
- 再導出が高コストな少数 (loogle Found 0 / 解析的な壁判断) **だけ**確定事実台帳へ。

**確定事実台帳 `docs/<family>/<family>-facts.md`** (family ごと 1 本): 列 = 主張 / 確信度 / 再検証コマンド / last-verified (commit hash) / 備考。確信度は `machine` (axiom/sorry 機械検証済、再検証コマンド必須) / `loogle-neg` (loogle Found 0、query 併記) / `human-judgment` (解析的壁判断、**過大も過小も起きるので低信頼、独立 pivot で再確認**) の 3 値。

**判断ログ + ライフサイクル**:

- 判断ログは **決着済** (採用確定 / 反例却下 / commit 済) entry を削除する (git が履歴を持つ)。**active な撤退ライン・判定軸・進行中 Phase の判断は残す**。凍結 slug (L-* 系) / 凍結 Phase 番号は他文書参照ありうるので削除不可。
- 廃止 / 完了 Phase は取り消し線残置でなく 1 行 + commit に圧縮。
- **プラン予算**: 1 plan ≤ 600 行 / active 判断ログ ≤ 10 entry。超過したら `/compact-plan` (handoff 境界で自動起動)。pre-commit が docs-plan の予算超過を WARN。

**staleness 検出**: `scripts/plan_lint.ts` が plan の decl / file:line / 壁 slug 参照をコードと照合し STALE/SUSPECT を出す。STALE 確定は (file 消失 / 壁 slug 消失 / dead `*-plan.md` リンク) の 3 ルールのみ、残りは要レビューの SUSPECT。親子グラフも同 linter が検査。

**親子プラン整合 (handoff/carryon ドリフト対策)**: 親 moonshot plan は子の **状態** (DAG の本線/park、sub-plan テーブルの進捗) を *キャッシュ* として持つ。子だけ更新して親 DAG を直し忘れると、cold な次セッションが `/carryon` で親 DAG を最初に読み park 経路を本線と取り違える。構造 (DAG エッジ) は滅多に変わらない — drift するのは状態 / ルート選択なので、そこにだけ「再導出 > キャッシュ」を効かせる。

- **衝突時は子が SoT**: 親 DAG / sub-plan テーブルと子 plan が食い違ったら、子が作業に近く新しい。**親を子に合わせて直す** (子を親に揃えない)。
- **編集時の強制点** (pre-commit, text のみ): 子 plan (`**Parent**:`/`**親**:` ヘッダ持ち) を編集する commit に親 plan が co-staged されていないと WARN。子を直したらできるだけ親も同コミットに含める。
- **検査の強制点** (`plan_lint.ts`): 親子グラフを照合 — dead 親/子リンク (STALE)、backlink 欠落 / 親子 drift (SUSPECT)。`handoff` / `carryon` が family 単位で `deno run -A scripts/plan_lint.ts docs/<family>/*-plan.md` を走らせ SUSPECT を解消してから引き継ぐ / 着手する。
- **規約上の同期点**: 子の `**Parent**:` ヘッダが親へのリンク兼「親更新の同期点」、親の sub-plan テーブル / DAG 行が子への backlink。両端を linter が双方向照合する (テンプレ → `docs/subplan-template.md` / `docs/moonshot-plan-template.md`)。

## Definition of Done — 2 段階

検証バーは 2 段階。commit 可否と「証明完成」を分離することで、未完成を `sorry` で正直に残せるようにする (`sorry` を消すための仮説束 / `:True` slot / 退化定義悪用が起きないよう撤退口を構造的に確保する)。

- **type-check done** (commit / push OK): `lake env lean <file>` が 0 errors。`sorry` warning は許容。各 `sorry` は `@residual(<class>:<slug>)` タグを持つ (配置 + 語彙 → `docs/audit/audit-tags.md`「配置ルール」)。
- **proof done** (genuine completion): 上記に加えて当該 file 内 0 `sorry` / 0 `@residual`。独立 auditor が pass 判定すれば `@audit:ok` 付与。

実装中の中間状態は type-check done で十分 (commit / push 可)。proof done は本物の完成を表す独立指標で、moonshot plan / textbook roadmap 側の集計対象。`sorry` は **正直な未完成マーカー** として積極的に使う。仮説に核を抱えさせて `sorry` を消すのは禁止 (→「検証の誠実性」)。

## 検証の誠実性 (honesty) — 全エージェント常時

標準B (無条件機械検証) が本プロジェクトの検証バー。**`0 sorry` だけでは完成判定にならない** — 仮説に核を抱えさせて `sorry` を消すパターンを許すと、コンパイラが通る (≒ 0 sorry) のに proof は完成していない状態が無限に作れる。proof done は「0 sorry **かつ** 0 residual」。

直接タスクに取り組んでいる最中でも、以下の honesty defect を **作らない** + **見つけたら即アラート** する。専用監査を待たない。

**defect の兆候 (tells):**

- 循環: 仮説型 ≡ 結論型 で body が `:= h` (何も証明していない)
- `:True` / 未使用スロットに実 residual を隠す
- 退化定義の悪用 (vacuous truth、例: `0 = 値` を突いた exfalso)
- **load-bearing hypothesis bundling**: 証明の核心を `*Hypothesis` / `*Reduction` / `IsXxxClaim` predicate にまとめて仮説として渡し、body は機械的展開だけにする (Stam / typicality / multi-user Fano 等)。regularity hyp (full-support / `IsFiniteMeasure` / measurability 等) は precondition なので OK。**この区別の判定軸 → 後述**
- name laundering: 仮説が開いたままの定理を `*_discharged` / `*_full` / `*_unconditional` と命名
- 「Mathlib 壁」の誤用: 実は選択 (big) を blocked (hard) と偽る
- **under-hypothesized / insufficient signature**: 仮説群から結論が semantic に follow しない (非循環・非バンドルでも偽の含意を主張)。非循環・非バンドルは honesty の **必要条件であって十分条件ではない** (sufficiency check の SoT → `docs/audit/audit-tags.md`)。

**作る側 (実装中)**: 行き詰まったら **`sorry` + `@residual(<class>:<slug>)`** で抜く (→ Skeleton-driven Development 手順 5)。仮説に核を bundling する撤退は禁止。type-check done で commit して次セッションに引き継ぐ。

**見つけた側**: 既存コード / 依存 / 計画に defect を見つけたら、現タスクと無関係でも **その場で即フラグ** (任意の気づきに埋めない)。defect の上に黙って積み上げない。フラグの仕方は defect の重さで分岐:

- **tier 5 defect** (循環 `:= h` / `:True` slot / 退化定義悪用 / load-bearing hyp / name laundering): silent fix しない。signature 改変 + sorry 化が必要だが、見つけた turn では **(a) defect の場所と種類を報告**、**(b) その上に build しない** で止める。実際の rewrite は当該 declaration の owner / 別 task。一時的に既存 docstring に `@audit:defect(<kind>)` を TODO marker として書込む (signature はまだ defect 形) のも可だが「defect 残置中」を明示。
- **tier 4 legacy** (`@audit:suspect/staged`、散文 `🟢ʰ`): tier 5 ほど urgent ではない。当該 file を current task で touch するなら incidental に sorry-based へ migrate、touch しないなら触らない。

タスクリストや snapshot 文書に分散保管しない (code が SoT)。語彙詳細 → `docs/audit/audit-tags.md`。

### sorry を書けない箇所 (def / Prop RHS / inductive constructor) での対処順序

`sorry` は proof body にしか書けない。`def` / `abbrev` / `Prop := ...` の RHS / `inductive` constructor 等が詰まったときの対処順:

1. **第一選択 — 定義書換で `sorry` を proof body に逃がす** (→「Mathlib-shape-driven Definitions」)。textbook の formulation を直接 def 化せず、結論型を Mathlib 結論形に合わせて再定義 → 性質を別 `theorem` で述べる → body `sorry` + `@residual(<class>:<slug>)` に持ち込む。例: `IsXxxHypothesis : Prop` を補題 `xxxInequality : ... := by sorry` に分割し、原 def は補題呼び出しに置換 / shared sorry 補題化 (audit-tags.md「共有 Mathlib 壁」)。

2. **第二選択 (暫定) — `@audit:defect(<kind>)` でマークして tier 5 のまま残す**。第一選択が当該セッションで無理 (循環構造解消に上流再設計必要 / signature 改変の影響範囲が大 / vacuously-true wrapper として acknowledged 等) な場合は signature を defect 形のまま残し、docstring に `@audit:defect(<kind>)` (`circular` / `prop-true` / `launder` / `degenerate` / `false-statement` / `false-hypothesis` から選択、語彙 → `docs/audit/audit-tags.md`「Defect kind 語彙」) + `@audit:retract-candidate(<reason>)` または `@audit:closed-by-successor(<plan-slug>)` を併記する。これは **後の (1) を待つ暫定マーカー** であり stable な resting state ではない。残す場合は (a) なぜ (1) が無理だったか 1 行散文、(b) 後続 plan slug、の 2 点を docstring に書く。

**禁止** (= 上記 tells 再掲、マーカー無しでの導入は tier 5 silent defect): `Prop := True` placeholder / 仮説型≡結論の `:= h` 循環 / load-bearing `*Hypothesis` predicate に核を bundle / 退化定義悪用。

**判定の一言**: 「その仮説は前提条件 (regularity) か、それとも証明の核心 (load-bearing) か」。前者 OK、後者は **書いてはいけない** — sorry に置き換える。詳細 → `docs/textbook-roadmap.md`「完成判定 / 検証強度の基準」「Mathlib 壁の 4 分類」。

**honesty 階層** (`docs/audit/audit-tags.md`「Honesty 階層」が SoT):

```
Tier 1: @audit:ok                                                 ← 最高 honest
Tier 2: sorry + @residual(<class>:<slug>)                         ← 新規実装の唯一の正規撤退口
Tier 3: @audit:superseded-by / @audit:retract-candidate           ← bookkeeping (履歴 / 削除候補)
Tier 4: legacy @audit:suspect / @audit:staged / @audit:defer / @audit:closed-by-successor / 散文 🟢ʰ  ← 旧方針で許容、新方針で defect 寄り
Tier 5: @audit:defect / 循環 := h / :True slot / 退化定義悪用 / name laundering  ← 真の defect
```

**一番 honest なのは `sorry`** — コンパイラ可視 + 「ごめんね」と明示する隠蔽不能なマーカー。旧方針で許容されていた load-bearing hypothesis (`@audit:suspect`、🟢ʰ) は tier 4 = sorry-based より strictly less honest なので、新規導入禁止 + legacy 発見は incidental migration 推奨。

## Independent honesty audit (orchestrator 必須)

実装サブエージェントが新規に `sorry` + `@residual(<class>:<slug>)` を含む commit を作った場合、orchestrator は当該セッション中 (遅くとも `InformationTheory.lean` 編入 commit 前) に **独立 audit subagent** を 1 件起動する。実装 agent の self-申告だけでは classification (`<class>:<slug>` の正しさ) + signature の honesty を誰も独立に検証していない (書いた本人 = 申告者)。

**起動条件**: 新規 `sorry` + `@residual` を導入する commit が session 内にある / 共有 sorry 補題を新規追加した / 既存 declaration の signature を変更し honesty 関連の意味が変わる / legacy `@audit:suspect` / `@audit:staged` の sorry-based 移行を行った。「既存 `@residual` を継承使用するだけ」のケースは不要。

**subagent**: 専用 agent `honesty-auditor` (`.claude/agents/honesty-auditor.md`、CORE doctrine 内蔵) を `subagent_type: "honesty-auditor"` で起動 (CORE + audit-tags.md 語彙適用が自動)。必須条件は実装に関与していない fresh subagent (self-audit 不可)。渡す入力 = 対象 file path + 監査対象 declaration 名 + line 番号 + 関連 commit hash + 親 plan path。書込先 = コード docstring の `@residual(...)` / `@audit:*` タグ (Edit 経由、**コードタグが SoT**)。書込後 orchestrator に 200 行以内サマリ返却。

**監査スコープ**: (a) signature の honesty (結論型 ≡ 仮説型 の `:= h` 循環 / `:True` slot / 退化定義悪用 / `*Hypothesis` predicate への核 bundling)、(b) `@residual(<class>:<slug>)` の classification 正しさ (`wall:X` だが実は plan 1 つで closure 可能、`plan:foo` だが対応 plan 不在 等の誤分類)、(c) shared sorry 補題の集約状態 (同じ壁が複数 file に散らばっていないか)、(d) deprecated タグの残置 (`@audit:suspect` / `@audit:staged` / 散文 `🟢ʰ` の移行漏れ)。

**closure 判定**: verdict が **全 OK** → session 完了 OK (handoff に明記)、**questionable** → docstring refine / 追加コメント / 必要なら追加 patch、**DEFECT** → 当該 declaration を撤回 or 修正 (sorry-based に書換) を session 中に処理。

**inline policy との関係**: 「専用監査を待たない」は **inline 検出** の原則 (実装中に気付いたら即フラグ)。本独立監査は **実装後の二段目** であって inline の代替ではない — 両方走らせる。orchestrator が新規 `@residual` 導入を検出していながら独立監査を起動せずに session を closure するのは **honesty workflow 違反**。
