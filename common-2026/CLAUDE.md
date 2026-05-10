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

## Definition of Done

`lake env lean <file>` must pass cleanly on the file you touched — zero errors, no remaining `sorry`, minimal warnings.
