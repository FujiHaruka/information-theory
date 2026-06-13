# common-2026

A Lean 4 + Mathlib formalization of Shannon information theory.

This project aims for **Mathlib-PR quality**: an English codebase following
Mathlib's naming, documentation, and module-structure conventions, so that
finished material can eventually be upstreamed.

- **Code-surface prose** (`.lean` docstrings and comments) is **English**, American-spelled.
  Identifiers follow Mathlib naming. Internal working docs (`docs/**/*.md`, handoffs) may stay Japanese.
- **Conventions (SoT)**: [`docs/rules/`](docs/rules/) — naming, docstrings, Lean style, module structure.
- **Project rules / workflow**: [`CLAUDE.md`](CLAUDE.md).
- **Active plans, inventories, audit ledger**: under [`docs/`](docs/).

## Build

Single-file checks (warm Mathlib oleans) are the inner loop:

```bash
lake env lean InformationTheory/<path>.lean   # definitive synchronous check; silent = clean
```

Do not use `import Mathlib` (pulls in 8000+ modules) and do not add a `[[lean_exe]]` target
(forces native compilation of all of Mathlib). See [`CLAUDE.md`](CLAUDE.md) for the import and build policy.
