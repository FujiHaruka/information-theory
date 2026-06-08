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
- **After upstream edits, dependents may need olean refresh.** Changing a public symbol / namespace / signature in module A can make a dependent pick up A's stale `.olean` and emit a phantom `unknown identifier` → refresh once with `lake build InformationTheory.<A>`.

**Accept a "Mathlib wall" verdict only after attempting one refutation** (the root cause of the ~40 overturned verdicts was almost always "declared a wall without searching for a single alternative route or counterexample"). **Before** you write `@residual(wall:slug)` or scope a lemma out as a "wall", perform one refutation in the direction of the verdict, and always back the final verdict with real machine verification (`lake env lean` + `#print axioms`). The standard practice is to not take audit / inventory wall verdicts at face value and to re-confirm an alternative lemma chain across the inventory with `proof-pivot-advisor`.

- **When declaring a wall (guarding against over-estimation)**: a loogle 0-hit is *necessary but not sufficient*. After a 0-hit, do (a) a **two-stage conclusion-shape search** (re-search by subterm / conclusion pattern such as `|- _ ≤ _`, not a bare identifier), and (b) **name one template lemma close to the expected conclusion form and estimate the self-build line count**. If you can't write that, hold off on the wall verdict. Distinguish whether the blocker is "the proposition is absent from Mathlib (a genuine gap)" or "wiring to an existing asset (plumbing, including import cycles)".
- **Before declaring an entire family a wall / scoping it out (gateway-atom-first)**: dispatch one decisive atom of that family to `lean-implementer` and see whether it goes through before deciding.
- **When declaring something not-a-wall / a hypothesis OK (guarding against under-estimation)**: before accepting, **search once for a counterexample in a small case** + **substitute one degenerate boundary** (`=0` / Dirac / non-integrable / `N=0`) to confirm the statement is still alive. Check that the predicate's signature hasn't dropped a constraint (Read its `*_def`). For concrete numeric / type predictions, follow the "Verbatim confirmation of concrete numeric / type predictions" section.

Required metadata for wall verdicts, cause tags, and the overturn-analysis table → `docs/audit/audit-tags.md` "Required metadata for wall verdicts".

- **pre-commit hook** (git-managed, text inspection only, no lake): `common-2026/.githooks/pre-commit` checks honesty / import discipline on staged `InformationTheory/**.lean` (BLOCK: adding a bare `import Mathlib` / adding a `sorry` with no `@residual` at all. WARN: residual undercount, out-of-vocabulary class, deprecated tag, a new file's import not registered). Bypass with `SKIP_LEAN_HOOK=1 git commit ...` or `--no-verify`. In a new environment, enable it with `git config core.hooksPath common-2026/.githooks` (details → `.githooks/README.md`).

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

## Dependency / consumer reverse-lookup tools (`scripts/dep_*.sh`)

Mechanically look up dependency relations among in-project declarations. The implementation is `scripts/DepGraph.lean` (`import InformationTheory`). Unlike `rg`'s text matching, it picks up **true term-level references** (mentions in docstrings / comments don't count). Three modes:

- **`scripts/dep_consumers.sh <fully-qualified-name> [--transitive]`** — **reverse dependencies (consumer graph)**. Lists, with `file:line`, the InformationTheory decls that *directly reference* the given decl. **Always run this once before changing a shared lemma's signature (hypothesis threading, etc.)** — prerequisite work for putting the ripple (the set of decls that need touching) accurately into the initial brief. `--transitive` gives the full blast radius (transitive closure).
- **`scripts/dep_graph.sh <fully-qualified-name>`** — emits the forward dependency graph (what the root depends on) as Graphviz dot. `--svg`/`--png` to render an image.
- **`scripts/dep_rank.sh [N]`** — ranking by transitive-dependency count, descending, restricted to `@[entry_point]`.

Note: all of them read the root olean. If a recently added decl shows up as an "unknown declaration", the root is stale → refresh with `lake build InformationTheory` and re-run. `-h` on each for the option list.

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

This rewrite is also the **first-choice mitigation** when a definition / `Prop` RHS / `inductive` constructor can't accept `sorry` directly (`sorry` lives in proof body only). Convert the def's core into a separate `theorem` whose body is `sorry` + `@residual(<class>:<slug>)`, and have the def call that theorem (or a shared sorry lemma — `docs/audit/audit-tags.md` "Shared Mathlib walls"). The fallback when rewrite isn't feasible — keep the signature as a defect-marked tier-5 placeholder — is under "Verification honesty → Handling order where `sorry` can't be written".

### Verbatim confirmation of concrete numeric / type predictions (common to plan / inventory)

Anywhere a plan / inventory **predicts** a concrete **numeric / type value** (e.g. `differentialEntropy (Dirac 0) = ?`, some function's `.toReal` value, a boundary case's `≠ 0` / `= 0`), always do a **verbatim confirmation against the real code** (Read the relevant lines of the Mathlib lemma + the InformationTheory file) before writing it down. If a predicted value is wrong, every retreat line / degenerate boundary / strategy choice built on top of it drifts. Don't trust intuitions like "this is surely the value" or "it should be -∞" — boundary-case definitions in Mathlib / InformationTheory follow different conventions across `Real` / `EReal` / `ℝ≥0∞`, and the values for Dirac / degenerate measures are especially prone to diverging from intuition.

How to confirm: Mathlib API → search by full namespace in loogle, then Read the verbatim signature. In-project (InformationTheory) definitions → grep with `rg` → Read the relevant line.

The same verbatim-confirmation obligation applies to **dependency direction / Phase order / wrapper call direction / import cycles** (when a subagent's verbatim verification proposes reversing one of those that the orchestrator brief assumed in-mind, accepting is the default).

## Skeleton-driven Development

Do **not** write a whole proof file in one shot. Instead:

1. Sketch the file as a skeleton: state every helper lemma and theorem with `:= by sorry`, plus the namespace and imports.
2. After Write, wait for the LSP `<new-diagnostics>` reminder. Confirm the skeleton type-checks (only `sorry` warnings expected).
3. Fill in **one** `sorry` at a time. Trust the LSP diagnostic reminder for fast feedback; reach for `lake env lean <file>` when you want a synchronous confirmation.
4. Let the diagnostics tell you when a tactic doesn't fire or a case is missing, instead of pattern-matching in your head.
5. **Exit a dead-end with `sorry`**: when stuck, keep the signature in the form you actually want to prove, leave the body as `sorry`, and attach `@residual(<class>:<slug>)` (placement + vocabulary → `docs/audit/audit-tags.md`). Retreating by bundling the core into a `*Hypothesis` predicate is forbidden (→ "Verification honesty"). A `sorry` may be committed as an honest incompleteness marker (→ "Definition of Done").

## Parallel orchestration

Trigger: the user explicitly requests parallel execution ("in parallel", "N seeds in parallel", "parallel run"). Launch independent seeds with `Agent` + `isolation: "worktree"`. **Every agent prompt must include the Standard boilerplate from `.claude/guides/agent-dispatch-guide.md`** (omitting it causes disk-full / branch drift). The post-merge cleanup procedure and the Brief content checklist are also owned (SoT) by that guide.

**A solo dispatch needs no worktree**: a solo `lean-implementer` dispatch with no parallel trigger can omit `isolation` and work directly on main. The worktree exists to avoid disk / branch collisions during parallel runs; for a solo run it only adds merge / cleanup cost. The boilerplate's worktree symlink / branch discipline / commit-push separation may be omitted (autonomous commit + push on main is fine). Skeleton-driven development / verification / scope / imports / retreat exits still apply for a solo run.

**Orchestrator role discipline**: in work that involves parallel dispatch, you-as-orchestrator **do not edit code / docs directly**. Dispatch `Edit` / `Write` to subagents and limit yourself to monitoring / coordination such as `git commit` / `git push` / TaskCreate / `git status` / `lake env lean` / `Read`. Even a seemingly trivial 1-line patch is written up as a brief and dispatched. Even if a handoff says "orchestrator edits directly" (written by a past-session self), don't follow it in the current session — subagent-ize it (user redirect takes precedence). The only exception is when the user explicitly says "do it yourself". **This discipline does not apply to a solo session with no parallelism** (you may edit directly at will).

**Exception — planner / docs-only agents**: `lean-planner` / `mathlib-inventory` / audit agents only write to `docs/<family>/*.md` and don't compile Lean, so worktree isolation is unnecessary (there is a failure mode where the harness creates the worktree dir incompletely and the agent writes straight to main). For docs-only parallelism, just omit `isolation` and make file ownership explicit in the brief ("Agent N edits only file F"). Implementation agents (`lean-implementer`) need worktree isolation + boilerplate **only when running in parallel**.

## Commits

- Commits and pushes are autonomous. Decide when to commit and push on each turn without waiting for the user to ask. The user will not give commit instructions. Commit autonomously even for changes that did not originate in the current session (e.g. uncommitted edits already on disk).
- Do not report commits or pushes. The user is not interested in commit/push activity. Skip mentioning them in turn summaries or status updates.
- Keep commit messages short. One concise line, no body unless absolutely necessary.
- **Implementation subagents may commit on their own**: `lean-implementer` and the like may have already run `git commit` on completion even if the brief said "don't commit". After they finish, **check for existing commits with `git log --oneline -3` + `git status --short` before** committing only the remaining diff (to prevent double commits). Avoid `git add -A` — it sweeps in the embedded repos under `.claude/worktrees/agent-*` — and name the target path explicitly.

## Textbook site deploy

After editing a manuscript under `docs/textbook/`, **always** redeploy the site without asking for confirmation (run `docs/textbook/site/deploy.sh`). It is an outward-facing publish, but per-time approval is not required (the user has stated this — they want the manuscript and the live site always in sync).

- Workflow: edit source → build → commit → run `deploy.sh` automatically.
- surge sometimes fails on the first attempt with a processing error (the `payload.error.filename` undefined family) — it's transient, so one retry gets through.

## Handoff

The `handoff` skill writes session state to `.claude/handoff.md` so the next session can `/carryon` from it. Default behavior is user-triggered, but autonomously invoke it at end-of-turn when **both**:

- the turn's work is finished and there is a clear, concrete next action, **and**
- this session is a continuation of a prior handoff (started via `/carryon`, or otherwise picking up an in-flight thread).

If the session is ad-hoc — opened with no prior handoff context, scope unrelated to any in-flight work — do not autonomously hand off; wait for explicit instruction.

**Interrupt trigger — on the 2nd malformed tool call, hand off + end the session** (overrides even ad-hoc, doesn't wait for the two conditions above): when a tool call is rejected with `Your tool call was malformed and could not be parsed` (the opening tag degenerates into a bare `<invoke>` / `<parameter>` with an extra leading token or a missing `antml:` prefix), **treat the 1st one as transient and retry exactly once** (re-emit the same call in the most minimal block, and don't write the broken token into prose = cut off the self-amplification). If the retry goes through, continue as normal. **If a 2nd one occurs (retry fails, or another independent recurrence), stop instead of pushing on**: (a) if safe, fold up only the atomic step in progress, (b) write the state + next move with the `handoff` skill, (c) prompt the user to restart a fresh session via `/clear` → `/carryon`. Rationale: this failure correlates monotonically with total context volume (more frequent and self-amplifying into a cascade at higher context); a single occurrence at low context is nearly independent noise, but a recurrence is a cascade signal, so continuing only makes it worse. If you're consciously in the high-context zone (~260K+), it's fine to stop on the 1st one. The root cause is not a harness bug but reduced special-token fidelity under long context (background → memory `pitfall-agent-invoke-malformed`).

**Single-file convention**: there is **only one** handoff, `.claude/handoff.md`. Don't create `handoff-<slug>.md` named slots. To manage multiple active lines concurrently, split within the one file by section (e.g. `## Line A — AWGN`, `## Line B — EPI/Stam`). Remove a fully closed line from the handoff (history stays in git), leaving only a reference in a `## Closure summary` section if needed. When writing the handoff at session end, merge by appending (adding a section) rather than overwriting an existing line.

**gitignored — don't commit**: `.claude/handoff.md` is deliberately gitignored (local working state, untracked). **Exclude** it from the autonomous-commit scope of the "Commits" section. Don't try to `git add` / `git commit` it after writing the handoff (it just loops: git rejects it every time and you rediscover the gitignore).

## Plan / docs hygiene

A plan bloats and goes stale if you mix the three: **control state** (scope/approach/next) / **decision history** / **settled facts** (sorryAx-free, walls, absent lemmas). Their lifetimes differ, so separate them.

**Don't cache settled facts in prose (re-derive > cache)**:

- Machine-re-derivable facts (`sorryAx-free` / presence of `sorry` / existence of a decl) don't belong in plan prose — look them up each time with `#print axioms` / `rg`. A prose cache is never invalidated and goes stale, so "if re-verification is cheap, re-derive every time" is the right rule.
- For walls, `@residual(wall:slug)` is the code-side SoT. The plan links to the slug and does not assert "X is a wall" in prose (once a wall is resolved, the plan would propagate a false certainty).
- Only the few facts that are expensive to re-derive (loogle Found 0 / analytic wall judgments) go into the settled-facts ledger.

**Settled-facts ledger `docs/<family>/<family>-facts.md`** (one per family): columns = claim / confidence / re-verification command / last-verified (commit hash) / notes. Confidence is one of three values: `machine` (axiom/sorry machine-verified, re-verification command required) / `loogle-neg` (loogle Found 0, with the query alongside) / `human-judgment` (analytic wall judgment — **low trust because it can both over- and under-estimate; re-confirm with an independent pivot**).

**Decision log + lifecycle**:

- Delete **settled** entries from the decision log (adoption confirmed / rejected by counterexample / committed) — git keeps the history. **Keep active retreat lines, decision axes, and in-progress Phase decisions.** Frozen slugs (the L-* family) / frozen Phase numbers can't be deleted, as other documents may reference them.
- Compress retired / completed Phases to one line + a commit rather than leaving struck-through text.
- **Plan budget**: one plan ≤ 600 lines / active decision log ≤ 10 entries. On overflow, `/compact-plan` (auto-invoked at handoff boundaries). pre-commit WARNs on a docs-plan budget overflow.

**Staleness detection**: `scripts/plan_lint.ts` cross-checks a plan's decl / file:line / wall-slug references against the code and emits STALE/SUSPECT. A definite STALE comes from only three rules (file vanished / wall slug vanished / dead `*-plan.md` link); the rest is review-needed SUSPECT. The same linter also inspects the parent/child graph.

**Parent/child plan consistency (guarding against handoff/carryon drift)**: a parent moonshot plan holds the child's **state** (mainline/park in the DAG, progress in the sub-plan table) as a *cache*. If you update only the child and forget to fix the parent DAG, a cold next session reading the parent DAG first under `/carryon` mistakes a parked route for the mainline. The structure (DAG edges) rarely changes — what drifts is state / route selection, so apply "re-derive > cache" only there.

- **On conflict the child is SoT**: when the parent DAG / sub-plan table and the child plan disagree, the child is closer to the work and newer. **Fix the parent to match the child** (don't align the child to the parent).
- **Enforcement point on edit** (pre-commit, text only): a commit that edits a child plan (one with a `**Parent**:`/`**親**:` header) WARNs if the parent plan isn't co-staged. When you fix a child, try to include the parent in the same commit.
- **Enforcement point on inspection** (`plan_lint.ts`): cross-checks the parent/child graph — dead parent/child links (STALE), missing backlink / parent-child drift (SUSPECT). `handoff` / `carryon` run `deno run -A scripts/plan_lint.ts docs/<family>/*-plan.md` per family and resolve SUSPECT before handing off / starting work.
- **Conventional sync points**: the child's `**Parent**:` header is both the link to the parent and the "sync point for updating the parent"; the parent's sub-plan table / DAG row is the backlink to the child. The linter cross-checks both ends bidirectionally (templates → `docs/subplan-template.md` / `docs/moonshot-plan-template.md`).

## Definition of Done — two stages

The verification bar has two stages. Separating "can it be committed" from "is the proof complete" lets you honestly leave incomplete work as `sorry` (structurally guaranteeing a retreat exit so that hypothesis bundling / `:True` slots / abuse of degenerate definitions to erase `sorry` don't happen).

- **type-check done** (commit / push OK): `lake env lean <file>` has 0 errors. `sorry` warnings are allowed. Each `sorry` carries a `@residual(<class>:<slug>)` tag (placement + vocabulary → `docs/audit/audit-tags.md` "Placement rules").
- **proof done** (genuine completion): the above, plus 0 `sorry` / 0 `@residual` within the file. If an independent auditor passes it, attach `@audit:ok`.

An intermediate state during implementation only needs type-check done (commit / push allowed). proof done is an independent metric for genuine completion and is what the moonshot plan / textbook roadmap tally. Use `sorry` liberally as an **honest incompleteness marker**. Erasing `sorry` by making a hypothesis carry the core is forbidden (→ "Verification honesty").

## Verification honesty — at all times, for every agent

Standard B (unconditional machine verification) is this project's verification bar. **`0 sorry` alone is not a completion verdict** — if you allow the pattern of erasing `sorry` by making a hypothesis carry the core, you can manufacture endless states where the compiler passes (≈ 0 sorry) yet the proof is not complete. proof done is "0 sorry **and** 0 residual".

Even while working directly on a task, **do not create** the honesty defects below + **alert immediately if you find one**. Don't wait for a dedicated audit.

**Signs of a defect (tells):**

- Circularity: hypothesis type ≡ conclusion type with the body `:= h` (proves nothing)
- Hiding a real residual in a `:True` / unused slot
- Abuse of a degenerate definition (vacuous truth, e.g. an exfalso exploiting `0 = value`)
- **load-bearing hypothesis bundling**: packing the proof's core into a `*Hypothesis` / `*Reduction` / `IsXxxClaim` predicate, passing it as a hypothesis, and leaving the body as mechanical unfolding only (Stam / typicality / multi-user Fano, etc.). Regularity hyps (full-support / `IsFiniteMeasure` / measurability, etc.) are preconditions and are OK. **The axis for this distinction → below**
- name laundering: naming a theorem whose hypotheses are still open `*_discharged` / `*_full` / `*_unconditional`
- Misuse of "Mathlib wall": passing off what is actually a choice (big) as blocked (hard)
- **under-hypothesized / insufficient signature**: the conclusion doesn't semantically follow from the hypotheses (claiming a false implication even when non-circular and non-bundled). Non-circular and non-bundled is **necessary but not sufficient** for honesty (the SoT for the sufficiency check → `docs/audit/audit-tags.md`).

**As the author (during implementation)**: when stuck, exit with **`sorry` + `@residual(<class>:<slug>)`** (→ Skeleton-driven Development, step 5). Retreating by bundling the core into a hypothesis is forbidden. Commit at type-check done and hand off to the next session.

**As the finder**: when you find a defect in existing code / dependencies / plans, **flag it on the spot** even if it's unrelated to the current task (don't bury it in an optional observation). Don't silently build on top of a defect. How you flag it branches on the defect's severity:

- **tier 5 defect** (circular `:= h` / `:True` slot / abuse of a degenerate definition / load-bearing hyp / name laundering): don't silent-fix. It needs a signature change + sorry-ification, but in the turn you find it, stop at **(a) report the defect's location and kind** and **(b) don't build on top of it**. The actual rewrite belongs to that declaration's owner / a separate task. You may temporarily write `@audit:defect(<kind>)` into the existing docstring as a TODO marker (the signature is still in defect form), but make "defect left in place" explicit.
- **tier 4 legacy** (`@audit:suspect/staged`, prose `🟢ʰ`): not as urgent as tier 5. If the current task touches that file, incidentally migrate it to sorry-based; if not, leave it alone.

Don't scatter this across task lists or snapshot documents (code is SoT). Vocabulary details → `docs/audit/audit-tags.md`.

### Handling order where `sorry` can't be written (def / Prop RHS / inductive constructor)

`sorry` can only go in a proof body. When you're stuck on a `def` / `abbrev` / the RHS of `Prop := ...` / an `inductive` constructor, etc., the handling order is:

1. **First choice — rewrite the definition to push the `sorry` into a proof body** (→ "Mathlib-shape-driven Definitions"). Don't def-ify the textbook formulation directly; redefine the conclusion type to match Mathlib's conclusion form → state the property as a separate `theorem` → bring it down to a body of `sorry` + `@residual(<class>:<slug>)`. Example: split `IsXxxHypothesis : Prop` into a lemma `xxxInequality : ... := by sorry`, and replace the original def with a call to that lemma / turn it into a shared sorry lemma (audit-tags.md "Shared Mathlib walls").

2. **Second choice (provisional) — mark it with `@audit:defect(<kind>)` and leave it at tier 5**. When the first choice is infeasible in the current session (resolving the circular structure needs upstream redesign / the signature change has a large blast radius / it's an acknowledged vacuously-true wrapper, etc.), leave the signature in defect form and write in the docstring both `@audit:defect(<kind>)` (choose from `circular` / `prop-true` / `launder` / `degenerate` / `false-statement` / `false-hypothesis`; vocabulary → `docs/audit/audit-tags.md` "Defect kind vocabulary") and either `@audit:retract-candidate(<reason>)` or `@audit:closed-by-successor(<plan-slug>)`. This is a **provisional marker awaiting a later (1)**, not a stable resting state. If you leave it, write two things in the docstring: (a) one line of prose on why (1) was infeasible, and (b) the successor plan slug.

**Forbidden** (= the tells above restated; introducing any of these without a marker is a tier 5 silent defect): `Prop := True` placeholder / a `:= h` circularity where hypothesis type ≡ conclusion / bundling the core into a load-bearing `*Hypothesis` predicate / abuse of a degenerate definition.

**The decision in one line**: "Is that hypothesis a precondition (regularity), or the core of the proof (load-bearing)?" The former is OK; the latter **must not be written** — replace it with sorry. Details → `docs/textbook-roadmap.md` "Completion verdict / verification-strength criteria" and "The four classes of Mathlib wall".

**Honesty hierarchy** (`docs/audit/audit-tags.md` "Honesty hierarchy" is SoT):

```
Tier 1: @audit:ok                                                 ← most honest
Tier 2: sorry + @residual(<class>:<slug>)                         ← the only sanctioned retreat exit for new implementation
Tier 3: @audit:superseded-by / @audit:retract-candidate           ← bookkeeping (history / deletion candidate)
Tier 4: legacy @audit:suspect / @audit:staged / @audit:defer / @audit:closed-by-successor / prose 🟢ʰ  ← allowed under the old policy, defect-leaning under the new
Tier 5: @audit:defect / circular := h / :True slot / abuse of a degenerate definition / name laundering  ← a true defect
```

**The most honest thing is `sorry`** — a compiler-visible, un-hideable marker that explicitly says "sorry". A load-bearing hypothesis (`@audit:suspect`, 🟢ʰ) allowed under the old policy is strictly less honest than tier 4 = sorry-based, so new introductions are forbidden and incidental migration is recommended when legacy ones are found.

## Independent honesty audit (orchestrator-mandatory)

When an implementation subagent makes a commit that introduces a new `sorry` + `@residual(<class>:<slug>)`, the orchestrator launches one **independent audit subagent** during that session (at the latest, before the commit that wires it into `InformationTheory.lean`). With only the implementation agent's self-report, no one has independently verified the classification (correctness of `<class>:<slug>`) + the signature's honesty (the author = the reporter).

**Launch conditions**: there is a commit in the session that introduces a new `sorry` + `@residual` / a new shared sorry lemma was added / an existing declaration's signature changed in a way that alters honesty-relevant meaning / a legacy `@audit:suspect` / `@audit:staged` was migrated to sorry-based. The "merely inheriting an existing `@residual`" case does not need it.

**subagent**: launch the dedicated agent `honesty-auditor` (`.claude/agents/honesty-auditor.md`, with the CORE doctrine built in) via `subagent_type: "honesty-auditor"` (CORE + audit-tags.md vocabulary apply automatically). The hard requirement is a fresh subagent not involved in the implementation (no self-audit). Inputs to pass = target file path + the declaration name(s) to audit + line number(s) + the relevant commit hash + the parent plan path. Write target = the `@residual(...)` / `@audit:*` tags in the code docstring (via Edit, **code tags are SoT**). After writing, return a summary of ≤ 200 lines to the orchestrator.

**Audit scope**: (a) the signature's honesty (a `:= h` circularity where conclusion type ≡ hypothesis type / `:True` slot / abuse of a degenerate definition / bundling the core into a `*Hypothesis` predicate), (b) the correctness of the `@residual(<class>:<slug>)` classification (misclassifications such as `wall:X` that is actually closable by a single plan, or `plan:foo` with no corresponding plan), (c) the consolidation state of shared sorry lemmas (whether the same wall is scattered across multiple files), (d) leftover deprecated tags (un-migrated `@audit:suspect` / `@audit:staged` / prose `🟢ʰ`).

**Closure verdict**: if the verdict is **all OK** → the session may complete (note it in the handoff); **questionable** → refine the docstring / add comments / an additional patch if needed; **DEFECT** → retract or fix the declaration (rewrite to sorry-based) within the session.

**Relation to the inline policy**: "don't wait for a dedicated audit" is the principle of **inline detection** (flag immediately when you notice during implementation). This independent audit is a **second stage after implementation**, not a replacement for the inline one — run both. For the orchestrator to close a session having detected a new `@residual` introduction without launching the independent audit is a **honesty-workflow violation**.
