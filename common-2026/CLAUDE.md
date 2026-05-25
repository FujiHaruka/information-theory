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

### 具体的数値・型予測の verbatim 確認 (plan / inventory 共通)

Plan / inventory で具体的な **数値・型値** (例: `differentialEntropy (Dirac 0) = ?`、`entropyPower (Measure.dirac 0) = ?`、`gaussianReal 0 0 = ?`、ある関数の `.toReal` 値、境界 case の `≠ 0` / `= 0`) を**予測**する箇所は、plan / inventory に書き出す前に **実コード verbatim 確認** (Mathlib lemma + Common2026 file の該当行を Read で照合) を必ず行う。

予測値が誤りだと、それを前提に組まれた撤退ライン / 退化境界 / 戦略選択がすべて drift する。2026-05-25 Phase D mini-plan は `entropyPower (Dirac 0) = 0` (`differentialEntropy (Dirac 0) = -∞` 想定) と予測し、戦略 β の `Y := 0` 退化境界処理を設計したが、実コード `DifferentialEntropy.lean:147` `differentialEntropy_dirac = 0` (= `entropyPower (Dirac 0) = 1`) で予測が外れ、退化 gap = `-1` 定数 → trivially `AntitoneOn` → degenerate-definition exploitation 直撃で L-DBD-2-α 発火、戦略 γ 降格となった。実コード verbatim 確認していれば設計段階で防げた drift。

確認方法:
- Mathlib API → `loogle` で完全 namespace 検索後、該当 file の verbatim signature を Read
- Common2026 内定義 → `rg` で grep → 該当行 Read (`Common2026/Shannon/DifferentialEntropy.lean:147` 等)

「常識的にこの値だろう」「-∞ になるはず」のような直感は信用しない。Mathlib / Common2026 の境界 case 定義は `Real` / `EReal` / `ℝ≥0∞` で慣行が異なり、Dirac / 退化 measure の値は特に直感と乖離しやすい。

## Skeleton-driven Development

Do **not** write a whole proof file in one shot. Instead:

1. Sketch the file as a skeleton: state every helper lemma and theorem with `:= by sorry`, plus the namespace and imports.
2. After Write, wait for the LSP `<new-diagnostics>` reminder. Confirm the skeleton type-checks (only `sorry` warnings expected).
3. Fill in **one** `sorry` at a time. Trust the LSP diagnostic reminder for fast feedback; reach for `lake env lean <file>` when you want a synchronous confirmation.
4. Let the diagnostics tell you when a tactic doesn't fire or a case is missing, instead of pattern-matching in your head.
5. **Dead-end は `sorry` で抜く**: 詰まったら signature を本来証明したい形に保ち、body を `sorry` のまま残し、近接 docstring/コメントに `@residual(<class>:<slug>)` を付与する (語彙 → `docs/audit/audit-tags.md`)。`*Hypothesis` predicate に核を bundling する撤退は禁止 (→「検証の誠実性」)。`sorry` は正直な未完成マーカーとして commit してよい (→「Definition of Done」2-tier)。

## Parallel orchestration

Trigger: user explicitly asks for parallel execution (「並列で」「N seed 並列」「並列実行」). Use `Agent` with `isolation: "worktree"` to launch independent seeds concurrently. Each agent prompt MUST include the boilerplate below — past sessions hit two operational failures without it: (a) disk full from per-worktree 5 GB Mathlib clones, (b) branch drift from agents creating `feat/...` branches and stealing HEAD.

**Exception — planner / docs-only agents**: `lean-planner` / `mathlib-inventory` / 監査系 agent は `docs/<family>/*.md` への書込みのみで Lean compile しないため worktree 隔離は不要 (むしろ harness 側で worktree dir が不完全に作られ agent が main に直書きする failure mode が観察されている、2026-05-24 Wave 2)。docs-only 並列は `isolation` 省略 + brief で「触る file の所有権 (Agent N は file F のみ編集)」を明示するだけでよい。file 競合は brief 設計で防ぐ。実装系 (`lean-implementer`) のみ worktree 隔離 + 上記 boilerplate 必要。

### Standard agent prompt boilerplate

```
## 運用ルール (絶対遵守)

1. **worktree .lake 共有 (最初に必ず実行)**: `ln -sfn /Users/haruka/dev/lean-projects/common-2026/.lake .lake` (inner `common-2026` directory 内)。親の `.lake` (Mathlib 7-8 GB) を symlink reuse、5 GB Mathlib clone は disk 破綻。
2. **ブランチ規律**: 起動時にいる worktree branch に居続ける。**絶対に** `git checkout`/`git branch`/`git switch` で他ブランチへ切替・作成しない。**`feat/...` ブランチ作成は禁止**。
3. **skeleton-driven**: skeleton → 1 sorry ずつ埋める (CLAUDE.md 参照)。
4. **検証**: 完了時 `lake env lean Common2026/<path>/<file>.lean` が 0 errors (type-check done)。`sorry` warning は許容、ただし各 `sorry` は近接 docstring/コメントに `@residual(<class>:<slug>)` 付き (→ `docs/audit/audit-tags.md`)。
5. **scope**: 1 file (or 既存 file 拡張)。完了時 `Common2026.lean` に import 1 行追加。
6. **import policy**: `import Mathlib` 禁止。pinpoint import。
7. **撤退口**: 行き詰まったら **`sorry` + `@residual(<class>:<slug>)`** で抜く。signature は本来証明したい形に保つ。**禁止**: `*Hypothesis` predicate に核を bundling する / `Prop := True` placeholder / 仮説型≡結論の `:= h` (循環) / 退化定義悪用 (CLAUDE.md「検証の誠実性」)。既存コードに defect を見つけたら即報告し、その上に積まない。
8. **commit**: 自走 commit、push なし (orchestrator が main にマージ後 push)。コミットメッセージは 1 行短く。
```

After all agents complete: copy each agent's `.lean` files from `.claude/worktrees/agent-*/common-2026/...` to main, merge imports into `Common2026.lean`, re-verify each touched file with `lake env lean` (parent .olean reuse は worktree から main に切り替わるので個別検証必須)、最後に 1 squashed commit + push。

### Brief content checklist — body fill / refactor (parallel or single dispatch)

`lean-implementer` を body fill (sorry 埋め) / 既存 body の P→P' 等 mechanical refactor に出すときは、brief に以下 2 項目を含める。planner / orchestrator 側の責務で、implementer 自身に判断させない。

1. **Sub-bound 引数表** (`P_cb` / `P_target` 分離型 predicate を扱うとき) — bundle / composite predicate の各 sub-bound が、rate-bound 引数 `R < (1/2) log(1 + ?/N)` の `?` 部に `P_cb` 側 / `P_target` 側のどちらの capacity を要求するかを 1 枚の表で列挙する (sub-bound 名 × 要求 capacity 側 × 必要 bridge 補題)。Bundle destructure 後に sub-bound 毎の capacity 引数が異なる場合があり (例: `IsAwgnPowerConstraintHonest P_cb P_target N` の rate-bound は `P_target` 側、bundle が供給する `hR_lt_P'C` は `P_cb = P'` 側)、表が無いと LSP 第 1 戻りまで気づけない型 mismatch で 1 turn ループ。Brief 段階で predicate signature を 1 度読めば書ける情報。

2. **継承タグの語彙整合 inline check** (git history からの body 復元時) — `git show <commit>^:<path>` で旧 body を抽出 + sed 書換するワークフローでは、旧 docstring の deprecated タグ (`@audit:suspect("")`、`@audit:staged(<slug>)`、散文 `🟢ʰ` 等) が literally 引き継がれる可能性がある。brief の検証 step に「貼付後 `rg -n '@audit:|@residual|🟢ʰ' <touched-file>` で deprecated タグ / 散文表現 / 既存語彙外 slug を列挙し orchestrator に報告」と 1 行追加。orchestrator 側で `docs/audit/audit-tags.md` 語彙と照合 → `Edit` で sorry-based 形式に確定 → 追加 commit。

由来: 2026-05-24 AWGN pivot Phase 3 で両項目とも実観測 (前者 1 turn 詰まり、後者 4 件継承)。書き漏らした場合は agent の proof-log 観察を次の brief に反映させる feedback loop で改善。

## Commits

- Commits and pushes are autonomous. Decide when to commit and push on each turn without waiting for the user to ask. The user will not give commit instructions. Commit autonomously even for changes that did not originate in the current session (e.g. uncommitted edits already on disk).
- Do not report commits or pushes. The user is not interested in commit/push activity. Skip mentioning them in turn summaries or status updates.
- Keep commit messages short. One concise line, no body unless absolutely necessary.

## Handoff

The `handoff` skill writes session state to `.claude/handoff.md` so the next session can `/resume` from it. Default behavior is user-triggered, but autonomously invoke it at end-of-turn when **both**:

- the turn's work is finished and there is a clear, concrete next action, **and**
- this session is a continuation of a prior handoff (started via `/resume`, or otherwise picking up an in-flight thread).

If the session is ad-hoc — opened with no prior handoff context, scope unrelated to any in-flight work — do not autonomously hand off; wait for explicit instruction.

## Definition of Done — 2 段階

検証バーは 2 段階。commit 可否と「証明完成」を分離することで、未完成を `sorry` で正直に残せるようにする (`sorry` を消すための仮説束 / `:True` slot / 退化定義悪用が起きないよう、撤退口を構造的に確保する)。

- **type-check done** (commit / push OK): `lake env lean <file>` が 0 errors。`sorry` warning は許容。各 `sorry` は直近 docstring または直前行コメントに `@residual(<class>:<slug>)` タグを持つ (語彙 → `docs/audit/audit-tags.md`)。
- **proof done** (genuine completion): 上記に加えて当該 file 内 0 `sorry` / 0 `@residual`。独立 auditor が pass 判定すれば `@audit:ok` 付与。

実装中の中間状態は type-check done で十分。commit / push 可。proof done は本物の完成を表す独立指標で、moonshot plan / textbook roadmap 側の集計対象。

`sorry` は **正直な未完成マーカー** として積極的に使う。仮説に核を抱えさせて `sorry` を消すのは禁止 (→「検証の誠実性」)。

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

**作る側 (実装中)**: 行き詰まったら **`sorry` + `@residual(<class>:<slug>)`** で抜く (→ Skeleton-driven Development 手順 5、`docs/audit/audit-tags.md`)。仮説に核を bundling する撤退は禁止。type-check done で commit して次セッションに引き継ぐ。

**見つけた側**: 既存コード/依存/計画に defect を見つけたら、現タスクと無関係でも **その場で即フラグ** (任意の気づきに埋めない)。defect の上に黙って積み上げない。**フラグ = 当該 sorry/decl の docstring に `@residual(defect:<kind>)` または bookkeeping `@audit:*` を書き込む** (語彙: `docs/audit/audit-tags.md`)。タスクリストや snapshot 文書に分散保管しない (code が SoT)。

**判定の一言**: 「その仮説は前提条件 (regularity) か、それとも証明の核心 (load-bearing) か」。前者 OK、後者は **書いてはいけない** — sorry に置き換える。詳細 → `docs/textbook-roadmap.md`「完成判定 / 検証強度の基準」「Mathlib 壁の 4 分類」。

## Independent honesty audit (orchestrator 必須)

実装サブエージェントが新規に `sorry` + `@residual(<class>:<slug>)` を含む commit を作った場合、orchestrator は当該セッション中 (遅くとも `Common2026.lean` 編入 commit 前) に **独立 audit subagent** を 1 件起動する。実装 agent の self-申告だけでは **classification (`<class>:<slug>` の正しさ)** + **signature の honesty** を誰も独立に検証していない状態 (書いた本人 = 申告者)。

### 起動条件

- 新規 `sorry` + `@residual(<class>:<slug>)` を導入する commit が session 内にある
- 共有 sorry 補題を新規追加 (shared wall lemma) した
- 既存 declaration の signature を変更 (引数削除 / 型変更) して honesty 関連の意味が変わる
- legacy `@audit:suspect` / `@audit:staged` の sorry-based 移行を行った

「既存 `@residual` を継承使用するだけ」のケースは不要。

### subagent

専用 agent: **`honesty-auditor`** (`.claude/agents/honesty-auditor.md`、CORE doctrine 内蔵)。orchestrator は `subagent_type: "honesty-auditor"` で起動するだけで CORE + audit-tags.md 語彙適用が自動。

- **必須条件**: 実装に関与していない fresh subagent (実装 agent の self-audit は不可)
- 渡す入力: 対象 file path + 監査対象 declaration 名 + line 番号 + 関連 commit hash + 親 plan path
- **書込先 = コード docstring の `@residual(...)` / `@audit:*` タグ** (Edit 経由)。**コードタグが SoT** (memory `feedback_audit_tags_source_of_truth.md` / `docs/audit/audit-tags.md` 冒頭)
- 書込後: orchestrator に 200 行以内サマリ返却

### 監査スコープ

- **signature の honesty**: 結論型 ≡ 仮説型 (`:= h` 循環) になっていないか、`:True` slot / 退化定義悪用していないか、`*Hypothesis` predicate に核を bundling していないか
- **`@residual(<class>:<slug>)` の classification 正しさ**: `wall:stam` と書いてあるが実は plan 1 つで closure 可能だったり、`plan:foo` と書いてあるが対応 plan が存在しないなどの誤分類
- **shared sorry 補題の集約状態**: 同じ Mathlib 壁が複数 file に散らばっていないか
- **deprecated タグの残置**: `@audit:suspect` / `@audit:staged` / 散文 `🟢ʰ` が残っていないか (移行漏れ)

### closure 判定

audit subagent の verdict が:

- **全 OK** → session 完了 OK、handoff に明記
- **questionable** → docstring refine or 追加コメントで対応、必要なら追加 patch
- **DEFECT** → 当該 declaration を撤回 or 修正 (sorry-based に書換)、session 中に処理

### 既存「検証の誠実性」inline policy との関係

直前セクション「**専用監査を待たない**」は **inline 検出** の原則 — 実装中に気付いたら即フラグするのを止めない。本独立監査は **実装後の二段目** であって inline の代替ではない。両方走らせる:

- **inline** (実装 agent 自身): 1 行レベルの defect tells を即フラグ
- **独立監査** (orchestrator が起動した fresh subagent): declaration 全体の構造的 honesty + classification を独立視点で verify

orchestrator が新規 `@residual` 導入を検出していながら独立監査を起動せずに session を closure するのは **honesty workflow 違反**。
