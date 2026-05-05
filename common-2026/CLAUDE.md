# Common2026 Project Rules

Formalization of Japan's 2026 Common Test (共通テスト) math problems in Lean 4 + Mathlib.

## Project Layout

- `docs/1a.pdf` — original problem booklet (**source of truth**)
- `docs/1a.txt` — manual transcription of the PDF. May contain transcription errors; **when in doubt, check the PDF**.
- `Common2026/QX_Y_z.lean` — one file per sub-problem. Naming: `Q<oomon>_<chuumon>_<shoumon>.lean`.
- `Common2026.lean` — library root. After adding a new file, append `import Common2026.QX_Y_z`.

## Build Setup

- This is a theorem-proving project, so **do not add a `[[lean_exe]]` target**. An executable target forces `lake build` to natively compile (`.c.o`) all of Mathlib, which takes minutes.
- `lake build` should finish within 1 minute. If it doesn't, suspect the imports.

## Import Policy

- **Do not use `import Mathlib`.** It pulls in 8000+ Mathlib modules as dependencies, making even a warm rebuild take 40+ seconds.
- Import only the specific tactics and lemmas you need. The usual minimum is:
  ```lean
  import Mathlib.Tactic.IntervalCases  -- interval_cases
  import Mathlib.Tactic.Linarith       -- includes omega
  ```
- Add more imports only when something is actually missing.

## Proof Style (follow `Q1_1_i.lean`)

- Define sets as `Prop`-valued predicates, not `Set`. Example: `def A (a k : Nat) : Prop := U k ∧ ...`.
- Name complements `Ac`, `Bc` (the token `ᶜ` is reserved by Lean).
- Lean heavily on case analysis and decidability: `interval_cases`, `decide`, `omega`.
- Extract reusable helpers like `(∃ d ≠ 1, d ∣ p ∧ d ∣ a) ↔ p ∣ a` as `private lemma`s.
- Write the problem statement at the top of the file as a Japanese docstring.

## Workflow (sorry-driven)

Do **not** write a whole problem file in one shot — it gambles on getting every divisor case and tactic incantation right with no compiler feedback. Instead:

1. Sketch the file as a skeleton: state every helper lemma and theorem with `:= by sorry`, plus the namespace and imports.
2. Run `lake build` (or `lake build Common2026.QX_Y_z` to scope to one module). Confirm the skeleton type-checks with sorries.
3. Fill in **one** `sorry` at a time; rebuild after each. Let the compiler tell you when a tactic doesn't fire or a divisor case is missing, instead of pattern-matching in your head.
4. Keep `lake build` warm — after the first cold build, incremental rebuilds should be a few seconds.

This trades a single ~20s cold build for a tight feedback loop and avoids whole-file rewrites when one tactic is off.

## Definition of Done

After solving a new problem, `lake build` must pass cleanly — zero errors, no remaining `sorry`, minimal warnings.
