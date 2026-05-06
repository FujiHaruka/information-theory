# Common2026 Project Rules

Formalization of Japan's 2026 Common Test (共通テスト) math problems in Lean 4 + Mathlib.

## Project Layout

- `docs/1a.pdf`, `docs/2b.pdf` — original problem booklets (**source of truth**). `1a.pdf` covers 数学Ⅰ・A, `2b.pdf` covers 数学Ⅱ・B・C. Read them with the Read tool's `pages` parameter.
- `Common2026/<exam>_QX_Y_z.lean` — one file per sub-problem. Naming: `<exam>_Q<oomon>_<chuumon>_<shoumon>.lean`, where `<exam>` is `A` for 1A and `B` for 2B (the same problem numbers appear in both exams, so the prefix disambiguates).
- `Common2026.lean` — library root. After adding a new file, append `import Common2026.<exam>_QX_Y_z`.

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
  lake env lean Common2026/<exam>_QX_Y_z.lean
  ```
  With Mathlib oleans warm, it returns in seconds. Silent output = clean.
- **Do NOT use `lake build` for verification.** It rebuilds every module in the library and is too slow for the inner loop. Reserve it for one-off project-wide sanity checks after a large refactor — never as the per-fill verifier.
- **Known LSP limitation.** The LSP tool exposed here only surfaces `hover` / `documentSymbol` etc, not `lean_goal` or `lean_diagnostic_messages`. So mid-proof goal inspection (after each tactic) isn't directly available; fall back to reading error spans from `lake env lean <file>` when stuck.
- **LSP shows stale errors after upstream edits.** The LSP runs `lake setup-file`, which locates `.olean` files but does not rebuild them. So when you change a public symbol, namespace, or signature in module A, the LSP keeps checking dependents against A's old `.olean` and reports phantom `unknown identifier` / `function expected at ... but this term has type ?m.1` errors. In this situation `lake env lean <dependent>` will be silent — trust it over the LSP. To clear the LSP, run `lake build Common2026.<A>` once after the upstream edit; the dependent's next LSP check will pick up the fresh `.olean`.

## Workflow (sorry-driven)

Do **not** write a whole problem file in one shot — it gambles on getting every divisor case and tactic incantation right with no compiler feedback. Instead:

1. Sketch the file as a skeleton: state every helper lemma and theorem with `:= by sorry`, plus the namespace and imports.
2. After Write, wait for the LSP `<new-diagnostics>` reminder. Confirm the skeleton type-checks (only `sorry` warnings expected).
3. Fill in **one** `sorry` at a time. Trust the LSP diagnostic reminder for fast feedback; reach for `lake env lean Common2026/<exam>_QX_Y_z.lean` when you want a synchronous confirmation.
4. Let the diagnostics tell you when a tactic doesn't fire or a divisor case is missing, instead of pattern-matching in your head.

## Definition of Done

After solving a new problem, `lake env lean Common2026/<exam>_QX_Y_z.lean` must pass cleanly — zero errors, no remaining `sorry`, minimal warnings.
