# Common2026 Project Rules

A Lean 4 + Mathlib formalization project. Scope evolves; for the current focus see `docs/`.

## Project Layout

- `Common2026.lean` — library root. `lake build` がここを起点にビルドする。新ファイルを足すときは原則 import を追記するが、`Common2026/Exam/` 配下（完成済みの入試ファイル）は除外している（`lake build` の負担を抑えるため）。Exam 配下の検証は `lake env lean <file>` または `lake build Common2026.Exam.<...>` で個別に行う。
- `private` is **file-scoped, not namespace-scoped**. Sub-modules that share `private` helpers must live in the same file, or those helpers leak as public symbols.
- `docs/` holds source materials (PDFs / plans / inventories) and per-task `proof-log-*.md` + `metrics/` outputs. Treat plan and inventory files as the source of truth for whatever is currently active.

## Build Setup

- This is a theorem-proving project, so **do not add a `[[lean_exe]]` target**. An executable target forces native compilation (`.c.o`) of all of Mathlib, which takes minutes.
- A single-file `lake env lean <file>` should finish within a few seconds once Mathlib oleans are warm. If it doesn't, suspect the imports.

## Import Policy

- **Do not use `import Mathlib`.** It pulls in 8000+ Mathlib modules as dependencies, making even a warm rebuild take 40+ seconds.
- Import only the specific tactics and lemmas you need. Add more imports only when something is actually missing.

## Verification

The Lean LSP plugin (`lean4-lake-lsp@claude-code-lsps`) is enabled, so prefer LSP feedback plus single-file type-checking over full project builds.

- **Primary — LSP automatic diagnostics.** After every Write/Edit to a `.lean` file, the LSP server runs `lake setup-file` in the background and surfaces results as a `<new-diagnostics>` system-reminder within a few seconds. It covers both parse errors and proof failures (`unsolved goals`, `unknown identifier`, etc). Wait for this signal after each fill — silence (or only `declaration uses 'sorry'`) means the file is clean.
- **Secondary — `lake env lean <file>` as the definitive synchronous check.** When you need an explicit verdict (e.g., before declaring a sorry-fill done), run it. Silent output = clean.
- **Do NOT use `lake build` for verification.** It rebuilds every module in the library and is too slow for the inner loop. Reserve it for one-off project-wide sanity checks after a large refactor — never as the per-fill verifier.
- **Known LSP limitation.** The LSP tool exposed here only surfaces `hover` / `documentSymbol` etc, not `lean_goal` or `lean_diagnostic_messages`. So mid-proof goal inspection (after each tactic) isn't directly available; fall back to reading error spans from `lake env lean <file>` when stuck.
- **LSP shows stale errors after upstream edits.** The LSP runs `lake setup-file`, which locates `.olean` files but does not rebuild them. So when you change a public symbol, namespace, or signature in module A, the LSP keeps checking dependents against A's old `.olean` and reports phantom `unknown identifier` errors. In this situation `lake env lean <dependent>` will be silent — trust it over the LSP. To clear the LSP, run `lake build Common2026.<A>` once after the upstream edit; the dependent's next LSP check will pick up the fresh `.olean`.

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
