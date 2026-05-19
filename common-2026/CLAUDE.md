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
7. **撤退ライン**: 行き詰まったら hypothesis pass-through (`Prop := True` placeholder or 明示 signature) で抜く。`sorry` を残さない。
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
