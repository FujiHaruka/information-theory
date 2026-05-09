# Common2026 Project Rules

Formalization of Japan's 2026 Common Test (共通テスト) math problems in Lean 4 + Mathlib.

## Project Layout

- `docs/1a.pdf`, `docs/2b.pdf` — original problem booklets (**source of truth**). `1a.pdf` covers 数学Ⅰ・A, `2b.pdf` covers 数学Ⅱ・B・C. Read them with the Read tool's `pages` parameter.
- `Common2026/<exam>_Q<X>...lean` — one file per **main question (大問)** by default. `<exam>` is `A` for 1A, `B` for 2B, `T` for 東大 (the same problem numbers appear across exams, so the prefix disambiguates).
  - Sub-problems (小問) of the same 大問 share infrastructure (`def`, `private lemma`, etc.). `private` is **file-scoped, not namespace-scoped**, so splitting a 大問 across files forces helpers to leak as public symbols. Keep the 大問 in one file (e.g. `T_Q4.lean`) so private helpers stay private.
  - Split into per-小問 files (`<exam>_QX_Y.lean`, `<exam>_QX_Y_z.lean`) only when the sub-problems are genuinely independent — different definitions, different imports, no shared helpers.
- `Common2026.lean` — library root. After adding a new file, append the corresponding `import Common2026.<...>`.

## Build Setup

- This is a theorem-proving project, so **do not add a `[[lean_exe]]` target**. An executable target forces native compilation (`.c.o`) of all of Mathlib, which takes minutes.
- A single-file `lake env lean <file>` should finish within a few seconds once Mathlib oleans are warm. If it doesn't, suspect the imports.

## Import Policy

- **Do not use `import Mathlib`.** It pulls in 8000+ Mathlib modules as dependencies, making even a warm rebuild take 40+ seconds.
- Import only the specific tactics and lemmas you need. The usual minimum is:
  ```lean
  import Mathlib.Tactic.IntervalCases  -- interval_cases
  import Mathlib.Tactic.Linarith       -- includes omega
  ```
- Add more imports only when something is actually missing.

## Proof Style (follow `A_Q1_1_i.lean`)

- Define sets as `Prop`-valued predicates, not `Set`. Example: `def A (a k : Nat) : Prop := U k ∧ ...`.
- Name complements `Ac`, `Bc` (the token `ᶜ` is reserved by Lean).
- Lean heavily on case analysis and decidability: `interval_cases`, `decide`, `omega`.
- Extract reusable helpers like `(∃ d ≠ 1, d ∣ p ∧ d ∣ a) ↔ p ∣ a` as `private lemma`s.
- Write the problem statement at the top of the file as a Japanese docstring.

## Verification

The Lean LSP plugin (`lean4-lake-lsp@claude-code-lsps`) is enabled, so prefer LSP feedback plus single-file type-checking over full project builds.

- **Primary — LSP automatic diagnostics.** After every Write/Edit to a `.lean` file, the LSP server runs `lake setup-file` in the background and surfaces results as a `<new-diagnostics>` system-reminder within a few seconds. It covers both parse errors and proof failures (`unsolved goals`, `unknown identifier`, etc). Wait for this signal after each fill — silence (or only `declaration uses 'sorry'`) means the file is clean.
- **Secondary — `lake env lean <file>` as the definitive synchronous check.** When you need an explicit verdict (e.g., before declaring a sorry-fill done), run:
  ```bash
  lake env lean Common2026/<exam>_Q<X>...lean
  ```
  With Mathlib oleans warm, it returns in seconds. Silent output = clean.
- **Do NOT use `lake build` for verification.** It rebuilds every module in the library and is too slow for the inner loop. Reserve it for one-off project-wide sanity checks after a large refactor — never as the per-fill verifier.
- **Known LSP limitation.** The LSP tool exposed here only surfaces `hover` / `documentSymbol` etc, not `lean_goal` or `lean_diagnostic_messages`. So mid-proof goal inspection (after each tactic) isn't directly available; fall back to reading error spans from `lake env lean <file>` when stuck.
- **LSP shows stale errors after upstream edits.** The LSP runs `lake setup-file`, which locates `.olean` files but does not rebuild them. So when you change a public symbol, namespace, or signature in module A, the LSP keeps checking dependents against A's old `.olean` and reports phantom `unknown identifier` / `function expected at ... but this term has type ?m.1` errors. In this situation `lake env lean <dependent>` will be silent — trust it over the LSP. To clear the LSP, run `lake build Common2026.<A>` once after the upstream edit; the dependent's next LSP check will pick up the fresh `.olean`.

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
  - **Full namespace required**: `InformationTheory.klDiv` not `klDiv`; `MeasureTheory.Measure.map` not `Measure.map`. Loogle prints "Maybe you meant: ..." with the right qualifier.
  - **Subterm pattern**: `InformationTheory.klDiv (MeasureTheory.Measure.map _ _) (MeasureTheory.Measure.map _ _)` finds KL applied to two pushforwards.
  - **Multi-term (any of)**: comma-separated, e.g. `MeasurableEquiv, InformationTheory.klDiv` finds lemmas mentioning both.
  - **Conclusion pattern**: `|- _ ≤ _` finds inequalities.
- **Fall back to `rg`** for text-level searches: comments, docstrings, file-structure exploration, or pattern matches that aren't tied to a specific identifier.

## Workflow (sorry-driven)

Do **not** write a whole problem file in one shot — it gambles on getting every divisor case and tactic incantation right with no compiler feedback. Instead:

1. Sketch the file as a skeleton: state every helper lemma and theorem with `:= by sorry`, plus the namespace and imports.
2. After Write, wait for the LSP `<new-diagnostics>` reminder. Confirm the skeleton type-checks (only `sorry` warnings expected).
3. Fill in **one** `sorry` at a time. Trust the LSP diagnostic reminder for fast feedback; reach for `lake env lean Common2026/<exam>_Q<X>...lean` when you want a synchronous confirmation.
4. Let the diagnostics tell you when a tactic doesn't fire or a divisor case is missing, instead of pattern-matching in your head.

## Commits

- Commits and pushes are autonomous. Decide when to commit and push on each turn without waiting for the user to ask. The user will not give commit instructions. Commit autonomously even for changes that did not originate in the current session (e.g. uncommitted edits already on disk).
- Do not report commits or pushes. The user is not interested in commit/push activity. Skip mentioning them in turn summaries or status updates.
- Keep commit messages short. One concise line, no body unless absolutely necessary.

## Definition of Done

After solving a new problem, `lake env lean Common2026/<exam>_Q<X>...lean` must pass cleanly — zero errors, no remaining `sorry`, minimal warnings.
