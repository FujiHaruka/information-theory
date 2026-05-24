# Common2026 Project Rules

A Lean 4 + Mathlib formalization project. Scope evolves; for the current focus see `docs/`.

## Project Layout

- `Common2026.lean` — library root. After adding a new file under `Common2026/`, append the corresponding `import` line here.
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
- **Do NOT use `lake build` for verification.** It rebuilds every module in the library and is too slow for the inner loop. Reserve it for one-off project-wide sanity checks after a large refactor — never as the per-fill verifier.
- **After upstream edits, dependents may need olean refresh.** When you change a public symbol, namespace, or signature in module A, dependents may still pick up A's old `.olean`. If `lake env lean <dependent>` reports phantom `unknown identifier`, run `lake build Common2026.<A>` once to refresh the olean.

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
- **Fall back to `rg`** for text-level searches: comments, docstrings, file-structure exploration, or pattern matches that aren't tied to a specific identifier.

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

The textbook-equivalent form can be re-derived as a separate equivalence lemma later if needed. Skipping this step routinely forces a mid-proof definition pivot or 50–100 lines of self-written bridge lemmas to convert between "the form Mathlib hands you" and "the form your proof expects".

A red flag that you skipped this step: you find yourself searching for "the lemma that turns `f (compProd ...)` into `∫⁻ ... ∂ ...`" or any analogous re-shaping bridge. If that bridge is not already in Mathlib, the cheapest fix is almost always to redefine, not to write the bridge.

## Skeleton-driven Development

Do **not** write a whole proof file in one shot. Instead:

1. Sketch the file as a skeleton: state every helper lemma and theorem with `:= by sorry`, plus the namespace and imports.
2. After Write, wait for the LSP `<new-diagnostics>` reminder. Confirm the skeleton type-checks (only `sorry` warnings expected).
3. Fill in **one** `sorry` at a time. Trust the LSP diagnostic reminder for fast feedback; reach for `lake env lean <file>` when you want a synchronous confirmation.
4. Let the diagnostics tell you when a tactic doesn't fire or a case is missing, instead of pattern-matching in your head.

## Parallel orchestration

Trigger: user explicitly asks for parallel execution (「並列で」「N seed 並列」「並列実行」). Use `Agent` with `isolation: "worktree"` to launch independent seeds concurrently. Each agent prompt MUST include the boilerplate below — past sessions hit two operational failures without it: (a) disk full from per-worktree 5 GB Mathlib clones, (b) branch drift from agents creating `feat/...` branches and stealing HEAD.

### Standard agent prompt boilerplate

```
## 運用ルール (絶対遵守)

1. **worktree .lake 共有 (最初に必ず実行)**: `ln -sfn /Users/haruka/dev/lean-projects/common-2026/.lake .lake` (inner `common-2026` directory 内)。親の `.lake` (Mathlib 7-8 GB) を symlink reuse、5 GB Mathlib clone は disk 破綻。
2. **ブランチ規律**: 起動時にいる worktree branch に居続ける。**絶対に** `git checkout`/`git branch`/`git switch` で他ブランチへ切替・作成しない。**`feat/...` ブランチ作成は禁止**。
3. **skeleton-driven**: skeleton → 1 sorry ずつ埋める (CLAUDE.md 参照)。
4. **検証**: 完了時 `lake env lean Common2026/<path>/<file>.lean` が silent (0 sorry / 0 warning)。
5. **scope**: 1 file (or 既存 file 拡張)。完了時 `Common2026.lean` に import 1 行追加。
6. **import policy**: `import Mathlib` 禁止。pinpoint import。
7. **撤退ライン (honest 限定)**: 行き詰まったら honest な名前付き仮説 (型 ≠ 結論、docstring で load-bearing 明示) で抜く。**`Prop := True` placeholder / 仮説型≡結論の `:= h` (循環) / 退化定義の悪用は禁止** (CLAUDE.md「検証の誠実性」参照)。既存コードに defect を見つけたら即報告し、その上に積まない。`sorry` も残さない。
8. **commit**: 自走 commit、push なし (orchestrator が main にマージ後 push)。コミットメッセージは 1 行短く。
```

After all agents complete: copy each agent's `.lean` files from `.claude/worktrees/agent-*/common-2026/...` to main, merge imports into `Common2026.lean`, re-verify each touched file with `lake env lean` (parent .olean reuse は worktree から main に切り替わるので個別検証必須)、最後に 1 squashed commit + push。

## Commits

- Commits and pushes are autonomous. Decide when to commit and push on each turn without waiting for the user to ask. The user will not give commit instructions. Commit autonomously even for changes that did not originate in the current session (e.g. uncommitted edits already on disk).
- Do not report commits or pushes. The user is not interested in commit/push activity. Skip mentioning them in turn summaries or status updates.
- Keep commit messages short. One concise line, no body unless absolutely necessary.

## Handoff

The `handoff` skill writes session state to `.claude/handoff.md` so the next session can `/resume` from it. Default behavior is user-triggered, but autonomously invoke it at end-of-turn when **both**:

- the turn's work is finished and there is a clear, concrete next action, **and**
- this session is a continuation of a prior handoff (started via `/resume`, or otherwise picking up an in-flight thread).

If the session is ad-hoc — opened with no prior handoff context, scope unrelated to any in-flight work — do not autonomously hand off; wait for explicit instruction.

## Definition of Done

`lake env lean <file>` must pass cleanly on the file you touched — zero errors, no remaining `sorry`, minimal warnings.

## 検証の誠実性 (honesty) — 全エージェント常時

標準B (無条件機械検証) が本プロジェクトの検証バー。`0 sorry` は完成を意味しない。直接タスクに取り組んでいる最中でも、以下の honesty defect を **作らない** + **見つけたら即アラート** する。専用監査を待たない。

**defect の兆候 (tells):**

- 循環: 仮説型 ≡ 結論型 で body が `:= h` (何も証明していない)
- `:True` / 未使用スロットに実 residual を隠す
- 退化定義の悪用 (vacuous truth、例: `0 = 値` を突いた exfalso)
- load-bearing hypothesis を完成と称する (Stam / typicality / multi-user Fano 等、証明の核心を仮定が肩代わり)。regularity hyp (full-support / `IsFiniteMeasure` 等) は OK
- name laundering: 仮説が開いたままの定理を `*_discharged` / `*_full` と命名
- 「Mathlib 壁」の誤用: 実は選択 (big) を blocked (hard) と偽る

**作る側**: 行き詰まって撤退する場合も honest に — 名前付き仮説 (≠結論)、docstring で「NOT a discharge / load-bearing」を明示、`:True` スロット禁止。これは既存の撤退ライン慣習の延長。

**見つけた側**: 既存コード/依存/計画に defect を見つけたら、現タスクと無関係でも **その場で即フラグ** (任意の気づきに埋めない)。defect の上に黙って積み上げない。フラグの形式は **当該 docstring 内に `@audit:KIND(SLUG)` タグ** (語彙: `docs/audit/audit-tags.md`) を直書きする。タスクリストや snapshot 文書に分散保管しない (code が SoT)。

判定の一言: **「その仮説は前提条件か、それとも証明の核心か」**。前者 OK、後者は残タスク。詳細 → `docs/textbook-roadmap.md`「完成判定 / 検証強度の基準」「Mathlib 壁の 4 分類」。

## Independent honesty audit (orchestrator 必須)

実装サブエージェントが **新たに `@audit:staged(<slug>)` / `@audit:residual(<slug>)` predicate を導入した場合** (既存タグの継承使用ではなく predicate そのものを新規 def したケース)、orchestrator は当該セッション中 (遅くとも `Common2026.lean` 編入 commit 前) に **独立 audit subagent** を 1 件起動する。実装 agent 自身の「honesty 4 条件 確認」自己申告だけでは **タグの正確さを誰も独立に検証していない** 状態 (書いた本人 = 申告者)。

### 起動条件

- 新規 `@audit:staged(<slug>)` predicate を 1 件以上含む commit が session 内にある
- 新規 `@audit:residual(<slug>)` を作って closure 不能と判定した
- 既存 staged predicate の signature 変更 (引数追加・型変更)

「既存 staged の継承使用」「`@audit:suspect` 散布」のみのケースは不要。

### subagent

専用 agent: **`honesty-auditor`** (`.claude/agents/honesty-auditor.md`、CORE doctrine 内蔵)。orchestrator は `subagent_type: "honesty-auditor"` で起動するだけで CORE + 3-tier 規律 + audit-tags.md 語彙適用が自動。

- **必須条件**: 実装に関与していない fresh subagent (実装 agent の self-audit は不可)
- 渡す入力: 対象 file path + 監査対象 predicate 名 + line 番号 + consumer 主定理名 + line + 関連 commit hash + 親 plan path
- **書込先 = コード docstring の `@audit:KIND(SLUG)` タグ** (Edit 経由)。**コードタグが SoT** (memory `feedback_audit_tags_source_of_truth.md` / `docs/audit/audit-tags.md` 冒頭)
- 書込後: orchestrator に 200 行以内サマリ返却

### closure 判定

audit subagent の verdict が:

- **全 OK** → session 完了 OK、handoff に明記
- **questionable** → docstring refine or 追加コメントで対応、必要なら追加 patch
- **DEFECT** → 当該 predicate を撤回 or 修正、session 中に処理

### 既存「検証の誠実性」inline policy との関係

直前セクション「**専用監査を待たない**」は **inline 検出** の原則 — 実装中に気付いたら即フラグするのを止めない。本独立監査は **実装後の二段目** であって inline の代替ではない。両方走らせる:

- **inline** (実装 agent 自身): 1 行レベルの defect tells を即フラグ
- **独立監査** (orchestrator が起動した fresh subagent): predicate 全体の構造的 honesty を独立視点で verify

orchestrator が新規 staging を検出していながら独立監査を起動せずに session を closure するのは **honesty workflow 違反**。
