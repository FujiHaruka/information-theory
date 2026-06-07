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
- **Do NOT use `lake build` for verification.** It rebuilds every module in the library and is too slow for the inner loop. Reserve it for one-off project-wide sanity checks after a large refactor — never as the per-fill verifier.
- **After upstream edits, dependents may need olean refresh.** When you change a public symbol, namespace, or signature in module A, dependents may still pick up A's old `.olean`. If `lake env lean <dependent>` reports phantom `unknown identifier`, run `lake build InformationTheory.<A>` once to refresh the olean.
- **「Mathlib 壁」判定は独立 pivot で再確認してから受け入れる。** 監査エージェント / 在庫が「これは Mathlib の壁 (証明不能・大規模 gap)」と判定しても鵜呑みにせず、`proof-pivot-advisor` で「別の主要 lemma chain で同じ結論に届かないか」を在庫横断で再確認する。監査は **想定した唯一のルートが詰まる** ことを「壁」と誤認し規模を過大評価しがち (A群 Huffman/Chernoff/LZ78 で 3倍過大評価の実例、Chernoff は既存 Sanov 経由で壁ゼロだった)。逆に pivot が楽観しすぎることもある (Huffman Hyp1 の縮約鎖は偽と実装で判明)。壁主張・楽観主張のどちらも、**最終判定は必ず実機械検証** (`lake env lean` + `#print axioms`) で裏取りする。

- **壁判定は「肯定的に 1 度確認」でなく「反証を 1 度試みる」プロセスにする (初回精度対策、↑の事後 pivot 再確認の前段)。** `@residual(wall:slug)` を書く / lemma を「Mathlib 壁」と scope-out する **前に**、判定の向きに応じた反証を 1 度行う。覆し ~40 件の真因はほぼ全て「別ルート or 反例を 1 つも探さずに断じた」(過大評価は wall register、過小評価は `docs/audit/defect-inventory-*.md` に記録され台帳が分離している)。判定時に試したルート・gateway atom・反証結果・plumbing/gap 区別を記録する (テンプレート → `docs/audit/audit-tags.md`「壁判定の必須メタデータ」)。
  - **壁と断じる側 (過大評価対策)**: loogle 0 件は *必要条件であって十分条件でない*。0 件の後に (a) **conclusion-shape 二段検索** (bare-identifier だけでなく `|- _ ≤ _` 等の subterm/conclusion pattern で再検索、bare-query の false-negative を回避)、(b) **期待結論形に近い template lemma を 1 本挙げ self-build 行数を見積もる** (`MeasurableEmbedding.map_withDensity_rnDeriv` から generic 版を ~15-20 行で自作した実例)。これが書けないなら壁判定保留。詰まりが「命題が Mathlib に無い (真の gap)」か「既存 asset への配線 (import cycle 含む)」かも区別する (`debruijn-integration` / `entropy-finiteness` / `awgn-mi-decomp` は後者を前者と誤認した)。
  - **family 丸ごと壁 / scope-out と断じる前 (gateway-atom-first)**: その family の決定的 atom 1 本を `lean-implementer` に実装 dispatch して通るか試してから判定する。`stam-blachman` / `convDensity_add_differentiable` / Chernoff (Sanov 経由) は全て「全体を壁判定 → 後で atom が genuine と判明」で覆った。
  - **非壁 / 仮説 OK と断じる側 (過小評価対策)**: 受け入れる前に **small-case で反例を 1 度探す** + **退化境界を 1 つ代入** (`=0` / Dirac / 非可積分 / `N=0`) して statement が生きているか確認する。Huffman merged-identity / collapse-label / LZ78 Ziv core の false-statement は全て small-case sim で即死した。述語の signature が constraint を落としていないか (`fisherInfoOfMeasureV2` が measure 引数を捨てて false-as-framed になった実例) を `*_def` の Read で確認。具体的数値・型の予測は「具体的数値・型予測の verbatim 確認」節に従い実 code 照合する (`entropyPower (Dirac 0) = 1` を `0` と誤予測 → Phase D 全 rewrite)。

- **pre-commit hook (git 管理、テキスト検査のみ、lake 不使用)。** `common-2026/.githooks/pre-commit` が staged な `InformationTheory/**.lean` に対し honesty/import 規律を最安段階で検査する (BLOCK: bare `import Mathlib` 追加 / `sorry` 追加で `@residual` 皆無。WARN: residual undercount・class 語彙外・deprecated tag・新規 file の import 未登録)。意図的な暫定コミットは `SKIP_LEAN_HOOK=1 git commit ...` か `--no-verify` で bypass。新環境では 1 回 `git config core.hooksPath common-2026/.githooks` で有効化 (詳細 → `.githooks/README.md`)。compile-check は載せない (cold olean で分単位、inner-loop と冗長)。

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

## 依存 / consumer 逆引きツール (`scripts/dep_*.sh`)

プロジェクト内 declaration の依存関係を機械的に引く。実体は `scripts/DepGraph.lean` (`import InformationTheory`)。`rg` のテキスト一致と違い **term レベルの真の参照** を拾う (docstring / コメントの言及は数えない)。3 モード:

- **`scripts/dep_consumers.sh <完全修飾名> [--transitive]`** — **逆依存 (consumer graph)**。指定 decl を *直接参照している* InformationTheory decl を `file:line` 付きで列挙する。**共有補題の signature を変更 (仮説 threading 等) する前に必ず 1 度引く** — ripple (touch が要る decl 群) を初回 brief に正確に載せるための前提作業。`--transitive` で full blast radius (推移閉包) も。
  - 由来: 共有補題の consumer graph を threading 前に洗い出していれば、`hX_ent`/`hY_ent` の ripple 範囲を初回 brief で正確に渡せた (rg だと散文言及と真の参照を区別できず過大/過小に振れる)。
- **`scripts/dep_graph.sh <完全修飾名>`** — forward 依存グラフ (root が何に依存するか) を Graphviz dot で出力。`--svg`/`--png` で画像化。
- **`scripts/dep_rank.sh [N]`** — `@[entry_point]` 限定で推移的依存数の多い順ランキング (複雑な定理の俯瞰)。

注意: いずれも root olean を読む。最近追加した decl が「未知の declaration」と出たら root が stale → `lake build InformationTheory` で refresh してから再実行 (`dep_consumers.sh` のエラーにもこのヒントを出す)。各 `-h` でオプション一覧。

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

This rewrite is also the **第一選択 mitigation** when a definition / `Prop` RHS / `inductive` constructor can't accept `sorry` directly (`sorry` lives in proof body only). Convert the def's core into a separate `theorem` whose body is `sorry` + `@residual(<class>:<slug>)`, and have the def call that theorem (or a shared sorry lemma — `docs/audit/audit-tags.md`「共有 Mathlib 壁」). The fallback when rewrite isn't feasible in the current session — keep the signature as a defect-marked tier-5 placeholder — is documented under 「検証の誠実性 → sorry を書けない箇所での対処順序」.

### 具体的数値・型予測の verbatim 確認 (plan / inventory 共通)

Plan / inventory で具体的な **数値・型値** (例: `differentialEntropy (Dirac 0) = ?`、`entropyPower (Measure.dirac 0) = ?`、`gaussianReal 0 0 = ?`、ある関数の `.toReal` 値、境界 case の `≠ 0` / `= 0`) を**予測**する箇所は、plan / inventory に書き出す前に **実コード verbatim 確認** (Mathlib lemma + InformationTheory file の該当行を Read で照合) を必ず行う。

予測値が誤りだと、それを前提に組まれた撤退ライン / 退化境界 / 戦略選択がすべて drift する。2026-05-25 Phase D mini-plan は `entropyPower (Dirac 0) = 0` (`differentialEntropy (Dirac 0) = -∞` 想定) と予測し、戦略 β の `Y := 0` 退化境界処理を設計したが、実コード `DifferentialEntropy.lean:147` `differentialEntropy_dirac = 0` (= `entropyPower (Dirac 0) = 1`) で予測が外れ、退化 gap = `-1` 定数 → trivially `AntitoneOn` → degenerate-definition exploitation 直撃で L-DBD-2-α 発火、戦略 γ 降格となった。実コード verbatim 確認していれば設計段階で防げた drift。

確認方法:
- Mathlib API → `loogle` で完全 namespace 検索後、該当 file の verbatim signature を Read
- InformationTheory 内定義 → `rg` で grep → 該当行 Read (`InformationTheory/Shannon/DifferentialEntropy.lean:147` 等)

「常識的にこの値だろう」「-∞ になるはず」のような直感は信用しない。Mathlib / InformationTheory の境界 case 定義は `Real` / `EReal` / `ℝ≥0∞` で慣行が異なり、Dirac / 退化 measure の値は特に直感と乖離しやすい。

同じ verbatim 確認義務は **依存方向 / Phase 順序 / wrapper 呼出方向 / import cycle** にも適用される (orchestrator brief で in-mind 仮定したそれらを subagent が verbatim 検証で逆順修正することがある — その提案は accept がデフォルト)。

## Skeleton-driven Development

Do **not** write a whole proof file in one shot. Instead:

1. Sketch the file as a skeleton: state every helper lemma and theorem with `:= by sorry`, plus the namespace and imports.
2. After Write, wait for the LSP `<new-diagnostics>` reminder. Confirm the skeleton type-checks (only `sorry` warnings expected).
3. Fill in **one** `sorry` at a time. Trust the LSP diagnostic reminder for fast feedback; reach for `lake env lean <file>` when you want a synchronous confirmation.
4. Let the diagnostics tell you when a tactic doesn't fire or a case is missing, instead of pattern-matching in your head.
5. **Dead-end は `sorry` で抜く**: 詰まったら signature を本来証明したい形に保ち、body を `sorry` のまま残し、`@residual(<class>:<slug>)` を付与する (配置 + 語彙 → `docs/audit/audit-tags.md`)。`*Hypothesis` predicate に核を bundling する撤退は禁止 (→「検証の誠実性」)。`sorry` は正直な未完成マーカーとして commit してよい (→「Definition of Done」2-tier)。

## Parallel orchestration

Trigger: user explicitly asks for parallel execution (「並列で」「N seed 並列」「並列実行」). Use `Agent` with `isolation: "worktree"` to launch independent seeds concurrently. Each agent prompt MUST include the boilerplate below — past sessions hit two operational failures without it: (a) disk full from per-worktree 5 GB Mathlib clones, (b) branch drift from agents creating `feat/...` branches and stealing HEAD.

**単独 dispatch では worktree 不要**: 並列トリガーが無い単独 `lean-implementer` dispatch は `isolation` 省略 + main 直接作業で良い。worktree は並列時の disk / branch 衝突対策であり、単独 dispatch では merge cost / cleanup cost が増えるだけで利得がない。boilerplate の (1) worktree symlink / (2) ブランチ規律 / (8) commit/push 分離も省略可 — main 上で自走 commit OK、push もそのまま (CLAUDE.md「Commits」)。boilerplate の (3)-(7) (skeleton-driven / 検証 / scope / import / 撤退口) は単独 dispatch でも有効。

**Orchestrator role 規律**: 並列 dispatch を伴う作業では、orchestrator 役の自分は **コード / docs を直接編集しない**。`Edit` / `Write` は subagent に dispatch し、自分は `git commit` / `git push` / TaskCreate / `git status` / `lake env lean` / `Read` 等の monitoring・調整のみ行う。`Edit` が必要に見える 1-line patch / trivial restore でも brief を書いて投げる。handoff に「並行して orchestrator が direct edit」と書いてあっても (前 session の自分が書いたもの)、**現 session では従わず subagent 化する** — user redirect 優先。例外は user が明示的に「自分でやって」と言った場合のみ。並列を伴わない単独 session ではこの規律は適用外 (自由に直接編集してよい)。

**Exception — planner / docs-only agents**: `lean-planner` / `mathlib-inventory` / 監査系 agent は `docs/<family>/*.md` への書込みのみで Lean compile しないため worktree 隔離は不要 (むしろ harness 側で worktree dir が不完全に作られ agent が main に直書きする failure mode が観察されている、2026-05-24 Wave 2)。docs-only 並列は `isolation` 省略 + brief で「触る file の所有権 (Agent N は file F のみ編集)」を明示するだけでよい。file 競合は brief 設計で防ぐ。実装系 (`lean-implementer`) は **並列時のみ** worktree 隔離 + 上記 boilerplate 必要。

### Standard agent prompt boilerplate

```
## 運用ルール (絶対遵守)

1. **worktree .lake 共有 (最初に必ず実行)**: `ln -sfn /Users/haruka/dev/lean-projects/common-2026/.lake .lake` (inner `common-2026` directory 内)。親の `.lake` (Mathlib 7-8 GB) を symlink reuse、5 GB Mathlib clone は disk 破綻。
2. **ブランチ規律**: 起動時にいる worktree branch に居続ける。**絶対に** `git checkout`/`git branch`/`git switch` で他ブランチへ切替・作成しない。**`feat/...` ブランチ作成は禁止**。
3. **skeleton-driven**: skeleton → 1 sorry ずつ埋める (CLAUDE.md 参照)。
4. **検証**: 完了時 `lake env lean InformationTheory/<path>/<file>.lean` が 0 errors (type-check done)。`sorry` warning は許容、ただし各 `sorry` は `@residual(<class>:<slug>)` 付き (配置 + 語彙 → `docs/audit/audit-tags.md`)。
5. **scope**: 1 file (or 既存 file 拡張)。完了時 `InformationTheory.lean` に import 1 行追加。
6. **import policy**: `import Mathlib` 禁止。pinpoint import。
7. **撤退口**: 行き詰まったら **`sorry` + `@residual(<class>:<slug>)`** で抜く。signature は本来証明したい形に保つ。**禁止**: `*Hypothesis` predicate に核を bundling する / `Prop := True` placeholder / 仮説型≡結論の `:= h` (循環) / 退化定義悪用 (CLAUDE.md「検証の誠実性」)。既存コードに defect を見つけたら即報告し、その上に積まない。
8. **commit**: 自走 commit、push なし (orchestrator が main にマージ後 push)。コミットメッセージは 1 行短く。
```

After all agents complete: copy each agent's `.lean` files from `.claude/worktrees/agent-*/common-2026/...` to main, merge imports into `InformationTheory.lean`, re-verify each touched file with `lake env lean` (parent .olean reuse は worktree から main に切り替わるので個別検証必須)、最後に 1 squashed commit + push。

**Cleanup after merge**: merge + push 完了後、worktree と branch を必ず削除する。残置すると locked 状態で `git worktree list` に蓄積し、次回 cleanup 時に untracked docs (回収済か否かの新旧比較等) の判断コストが発生する。30 件以上溜まった実例あり (2026-05-25)。

```bash
cd /Users/haruka/dev/lean-projects  # main worktree から実行
for d in .claude/worktrees/agent-*/; do
  git worktree unlock "$d" 2>/dev/null
  git worktree remove --force "$d" 2>/dev/null
done
git worktree prune
git branch | grep '^  worktree-agent-' | xargs -I {} git branch -D {}
```

`--force` は agent commit が main 回収済を前提。untracked file が残っていたら main 側と diff し、main が新しければ破棄して OK (worktree HEAD ≠ main HEAD なので status は dirty に見えるが、回収済なら本物の差分はない)。

### Brief content checklist — skeleton / body fill / refactor (parallel or single dispatch)

`lean-implementer` を skeleton 設計 (signature 含む) / body fill (sorry 埋め) / 既存 body の P→P' 等 mechanical refactor に出すときは、brief に以下の項目を含める (項目により適用 phase が違う: 項目 4 は主に signature 設計時、項目 2 は body 復元時)。planner / orchestrator 側の責務で、implementer 自身に判断させない。

1. **Sub-bound 引数表** (`P_cb` / `P_target` 分離型 predicate を扱うとき) — bundle / composite predicate の各 sub-bound が、rate-bound 引数 `R < (1/2) log(1 + ?/N)` の `?` 部に `P_cb` 側 / `P_target` 側のどちらの capacity を要求するかを 1 枚の表で列挙する (sub-bound 名 × 要求 capacity 側 × 必要 bridge 補題)。Bundle destructure 後に sub-bound 毎の capacity 引数が異なる場合があり (例: `IsAwgnPowerConstraintHonest P_cb P_target N` の rate-bound は `P_target` 側、bundle が供給する `hR_lt_P'C` は `P_cb = P'` 側)、表が無いと LSP 第 1 戻りまで気づけない型 mismatch で 1 turn ループ。Brief 段階で predicate signature を 1 度読めば書ける情報。

2. **継承タグの語彙整合 inline check** (git history からの body 復元時) — `git show <commit>^:<path>` で旧 body を抽出 + sed 書換するワークフローでは、旧 docstring の deprecated タグ (`@audit:suspect`、`@audit:staged`、`@audit:defer`、`@audit:closed-by-successor`、散文 `🟢ʰ` 等) が literally 引き継がれる可能性がある。brief の検証 step に「貼付後 `rg -n '@audit:|@residual|🟢ʰ' <touched-file>` で deprecated タグ / 散文表現 / 既存語彙外 slug を列挙し orchestrator に報告」と 1 行追加。これらは tier 4 legacy (`docs/audit/audit-tags.md`「Deprecated」表 + 移行レシピ) — orchestrator 側で sorry-based 形式に置換 commit を別途追加 (incidental migration、新規導入は禁止)。

3. **担当 file list は実値検証してから貼る** — brief 内に「担当 file list」を書くときは、記憶 / 予測で file 名を並べず、**必ず実ファイル (split 結果 / `find` 出力等) を `cat /tmp/group-X.txt` で確認してから貼る**。抽象指定 (「`InformationTheory/Shannon/<X>.lean` 系の 27 file」) は禁止、具体 path リテラルで。代替として agent 自身に `find ... | head -N` で file list を作らせ orchestrator を間に立たせない手もある。2026-05-26 session で fabricated file 名混入により 5 回の取りこぼし (27 file 中 19 file が存在せず agent skip) を実観測。

4. **honesty-load-bearing signature は goal でなく mechanism を渡す** (representative-dependent な量を結論に持つ lemma の実装時) — Fisher info / Radon-Nikodym 微分 / `logDeriv` など **a.e. 同値類から pointwise を取る量** (`fisherInfoOfDensityReal` 系) を signature に持つ lemma は、pin の強度 (a.e. か pointwise か) と「free 変数で受ける vs 結論に直接埋込」が **正直さそのものを決める** (a.e.-pin + free 変数は false-as-framed、skeptic が non-diff representative を取り値=0 に落とせる)。この種の signature を implementer に **「honest 化せよ」「pin せよ」という goal で投げて draft させない**。brief に (a) in-tree の honest sibling を `file:line` で、(b)「free 変数を作らず結論に直接埋込 (direct embed)」、(c)「a.e.-pin は不十分、pointwise-smooth pin (`density_t_eq` 等) のみ honest」の **3 点を mechanism として転写**する。判別軸は「その量は a.e. 等式で縛れるか、pointwise 必須か」。全 brief への mechanism front-load は delegation を殺すので、escalate するのは **honesty-load-bearing signature のときだけ** (routine body-fill は goal で良い)。

5. **共有補題の signature を変更するなら consumer graph を brief に添付** (shared lemma に仮説 threading / 引数追加・削除をするとき) — 変更前に **`scripts/dep_consumers.sh <完全修飾名>` を 1 度引き** (→「依存 / consumer 逆引きツール」)、direct consumers (= 直接 touch が要る decl 群) の `file:line` list をそのまま brief に貼る。これが ripple 範囲の見積もり前提。`rg` で済ませると docstring/コメントの言及を真の参照と混同し、ripple を過大/過小に振る (本ツールは term レベル参照のみ数える)。複数系統から消費される補題ほど初回 brief に正確な consumer list を載せないと、threading 後に LSP 第 1 戻りまで取りこぼしに気づけない。

由来: 2026-05-24 AWGN pivot Phase 3 で項目 1/2 を実観測 (前者 1 turn 詰まり、後者 4 件継承)、項目 3 は 2026-05-26 で実観測。項目 5 は共有補題 `integrable_negMulLog_map_condTrunc_sum` が EPI 加法側と Gibbs 単調側の両系統から消費され、threading 前に consumer graph を洗い出していれば `hX_ent`/`hY_ent` の ripple を初回 brief で正確に渡せた実例 (この気づきが `dep_consumers.sh` 新設の契機)。項目 4 は 2026-06-06 EPI two-time `twoTimeLogRatioGap_hasDerivAt` で実観測 — honest 機構 (直接埋込) が in-tree sibling `EPIStamToBridge.lean:744-883` `csiszarLogRatioGap_hasDerivAt` に既存だったのに、cycle 2 brief が「equality-pin せよ」の goal 止まりで a.e.-pin を誘発、`implementer→honesty-auditor` を 2 周空転 (cycle 3 で「τ 評価 density_t に直接埋込」を mechanism 指定して一発 PASS)。書き漏らした場合は agent の proof-log 観察を次の brief に反映させる feedback loop で改善。

## Commits

- Commits and pushes are autonomous. Decide when to commit and push on each turn without waiting for the user to ask. The user will not give commit instructions. Commit autonomously even for changes that did not originate in the current session (e.g. uncommitted edits already on disk).
- Do not report commits or pushes. The user is not interested in commit/push activity. Skip mentioning them in turn summaries or status updates.
- Keep commit messages short. One concise line, no body unless absolutely necessary.
- **実装系 subagent は自走 commit することがある**: `lean-implementer` 等は brief に「commit するな」と書いても完了時に `git commit` 済のことがある (2026-05-21 観測)。完了後は `git log --oneline -3` + `git status --short` で **既コミットの有無を確認してから** 差分のみ commit する (二重コミット防止)。`git add -A` は `.claude/worktrees/agent-*` の embedded repo を巻き込む事故があるため避け、対象 path を明示。

## Textbook site deploy

`docs/textbook/` の原稿を編集したら、確認を求めず **常に** サイトを再デプロイする (`docs/textbook/site/deploy.sh` を実行)。外向き公開だが毎回承認は不要 (ユーザー明言、原稿とライブサイトを常に同期させたい)。

- ワークフロー: ソース編集 → ビルド → commit → `deploy.sh` を自動実行。
- surge は処理エラーで初回失敗することがある (`payload.error.filename` undefined 系) — transient なので 1 回リトライすれば通る。

## Handoff

The `handoff` skill writes session state to `.claude/handoff.md` so the next session can `/carryon` from it. Default behavior is user-triggered, but autonomously invoke it at end-of-turn when **both**:

- the turn's work is finished and there is a clear, concrete next action, **and**
- this session is a continuation of a prior handoff (started via `/carryon`, or otherwise picking up an in-flight thread).

If the session is ad-hoc — opened with no prior handoff context, scope unrelated to any in-flight work — do not autonomously hand off; wait for explicit instruction.

**Interrupt trigger — malformed tool call が 1 度でも出たら即 handoff + セッション終了** (ad-hoc でも override、上の both 条件を待たない): ツール呼び出しが `Your tool call was malformed and could not be parsed` で弾かれたら (開始タグが `court\n<invoke` や `antml:` プレフィックス欠落の素の `<invoke>` / `<parameter>` に化ける)、retry で粘らない。この failure は**総コンテキスト量と単調相関**し (過去 34000 ターン集計で ~140K まで 0.01%、140–260K で 0.08%、260–320K で 0.52%、worst session の 250K 以降は ~21%/turn)、しかも `court` が一度文脈に入ると次ターンも真似て**自己増幅**する (散文に `court` と書くだけでも誘発) ので、続行は cascade を招くだけ。よって最初の 1 件で (a) 安全なら進行中の atomic step だけ畳み、(b) `handoff` skill で状態 + 次の一手を書き出し、(c) user に「`/clear` → `/carryon` で新セッション再開」を促して止める。根本原因は harness バグでなく長コンテキスト下の特殊トークン忠実度低下 (背景 → memory `pitfall-agent-invoke-malformed`)。

**Single file 規約**: handoff は `.claude/handoff.md` **1 本のみ**。`handoff-<slug>.md` の named slot は作らない。複数 active line を並行管理する場合は 1 ファイル内をセクションで分割 (例: `## Line A — AWGN`, `## Line B — EPI/Stam`)。完全 closed なラインは handoff から削除し (履歴は git に残る)、必要なら `## Closure summary` セクションで参照のみ残す。session 終了時の handoff 書き出しは既存 line を上書きせず、追記 (セクション追加) で merge する。

**gitignore 済み — commit しない**: `.claude/handoff.md` は意図的に gitignore されている (ローカル作業状態、追跡対象外)。「Commits」節の自走コミット対象から **除外** する。handoff を書いた後に `git add` / `git commit` を試みない (毎回 git に弾かれて gitignore と再発見するループになる)。

## Plan / docs hygiene

プランは「**制御状態** (scope/approach/next) / **判断履歴** (判断ログ) / **確定事実** (sorryAx-free・壁・補題不在)」の3つを混ぜると肥大・stale 化する。寿命が違うので分離する。

**確定事実は prose にキャッシュしない (再導出 > キャッシュ)**:

- 機械再導出できる事実 (`sorryAx-free` / sorry 有無 / decl 存在) は plan 本文に書かず、都度 `#print axioms` / `rg` で引く。prose キャッシュは無効化されず stale 化するので「再検証コストが安いなら毎回再導出」が正しい。同じ decl の `#print axioms` を別セッションで再実行するのは無駄でなく、prose を信用しない正しい挙動。
- 壁は `@residual(wall:slug)` がコード側 SoT。plan は slug にリンクし「X は壁」と本文に断定しない (壁が解消されると plan が誤った確定を伝播する)。
- 再導出が高コストな少数 (loogle Found 0 / 解析的な壁判断) **だけ**確定事実台帳へ。

**確定事実台帳 `docs/<family>/<family>-facts.md`** (family ごと 1 本、散在の単一源化):

| 列 | 内容 |
|---|---|
| 主張 | 1 行 |
| 確信度 | `machine` / `loogle-neg` / `human-judgment` |
| 再検証コマンド | `#print axioms ...` / loogle query / `rg ...` |
| last-verified | commit hash |
| 備考 | 任意 |

- `machine` — axiom/sorry 機械検証済。再検証コマンドを必ず併記。
- `loogle-neg` — loogle Found 0。query 併記 (bare-identifier 失敗と区別)。
- `human-judgment` — 解析的な壁判断。**過大評価 (実は通れる) も過小評価 (反例で偽) も起きるので低信頼**。鵜呑みにせず独立 pivot で再確認 (→「Verification」)。
- plan top-of-file の「Wall SoT: <file:line>」ヘッダは台帳行への参照に置換してよい。

**判断ログ + プランのライフサイクル**:

- 判断ログは「**決着済** (採用方針確定 / 反例で却下済 / commit 済) entry は削除」。git が履歴を持つので prose 二重保存は純肥大。**active な撤退ライン・判定軸・進行中 Phase の判断は残す**。凍結 slug (L-* 系) / 凍結 Phase 番号は他文書参照ありうるので削除不可。
- 廃止 Phase は取り消し線残置でなく 1 行 + commit に圧縮。完了 Phase の本文も同様。
- **プラン予算**: 1 plan ≤ 600 行 / active 判断ログ ≤ 10 entry。超過したら `/compact-plan` (handoff 境界で自動起動)。pre-commit が docs-plan の予算超過を WARN。

**staleness 検出**: `scripts/plan_lint.ts` が plan の decl / file:line / 壁 slug 参照をコードと照合し STALE/SUSPECT を出す。STALE 確定は (file 消失 / 壁 slug 消失 / dead `*-plan.md` リンク) の 3 ルールのみ、残りは要レビューの SUSPECT。親子グラフ (下記) も同 linter が検査する。

**親子プラン整合 (handoff/carryon ドリフト対策)**:

親 moonshot plan は子の **状態** (DAG の本線/park、sub-plan テーブルの進捗) を *キャッシュ* として持つ。子だけ更新して親 DAG を直し忘れると、cold な次セッションが `/carryon` で親 DAG を最初に読み、park 経路を本線と取り違える。構造 (DAG エッジ) は滅多に変わらない — drift するのは状態/ルート選択なので、そこにだけ「再導出 > キャッシュ」を効かせる。

- **衝突時は子が SoT**: 親 DAG/sub-plan テーブルと子 plan が食い違ったら、子が作業に近く新しい。**親を子に合わせて直す** (子を親に揃えない)。これが混乱した cold セッションの decision rule。
- **編集時の強制点** (pre-commit, text のみ): 子 plan (`**Parent**:`/`**親**:` ヘッダ持ち) を編集する commit に親 plan が co-staged されていないと WARN。子を直したらできるだけ親も同コミットに含める。
- **検査の強制点** (`plan_lint.ts`): 親子グラフを照合 — dead 親/子リンク (STALE)、backlink 欠落 (親が子を sub-plan 参照していない、SUSPECT)、親子 drift (子が親より後にコミット、SUSPECT)。`handoff` / `carryon` が family 単位で `deno run -A scripts/plan_lint.ts docs/<family>/*-plan.md` を走らせ、SUSPECT を解消してから引き継ぐ / 着手する。
- **規約上の同期点**: 子の `**Parent**:` ヘッダが親へのリンク兼「親更新の同期点」、親の sub-plan テーブル / DAG 行が子への backlink。両端を linter が双方向照合する (テンプレ → `docs/subplan-template.md` / `docs/moonshot-plan-template.md`)。

## Definition of Done — 2 段階

検証バーは 2 段階。commit 可否と「証明完成」を分離することで、未完成を `sorry` で正直に残せるようにする (`sorry` を消すための仮説束 / `:True` slot / 退化定義悪用が起きないよう、撤退口を構造的に確保する)。

- **type-check done** (commit / push OK): `lake env lean <file>` が 0 errors。`sorry` warning は許容。各 `sorry` は `@residual(<class>:<slug>)` タグを持つ (配置 + 語彙 → `docs/audit/audit-tags.md`「配置ルール」)。
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
- **under-hypothesized / insufficient signature**: 仮説群から結論が semantic に follow しない (非循環・非バンドルでも偽の含意を主張している)。非循環・非バンドルは honesty の **必要条件であって十分条件ではない**。例: 差分形 gap derivative が plain Stam から出ないのに結論している (`csiszarGap1Source_deriv_le_zero` の false-negative 事例、SoT → `docs/audit/audit-tags.md`「sufficiency check」)

**作る側 (実装中)**: 行き詰まったら **`sorry` + `@residual(<class>:<slug>)`** で抜く (→ Skeleton-driven Development 手順 5、`docs/audit/audit-tags.md`)。仮説に核を bundling する撤退は禁止。type-check done で commit して次セッションに引き継ぐ。

**見つけた側**: 既存コード/依存/計画に defect を見つけたら、現タスクと無関係でも **その場で即フラグ** (任意の気づきに埋めない)。defect の上に黙って積み上げない。

フラグの仕方は defect の重さで分岐:

- **tier 5 defect** (循環 `:= h` / `:True` slot / 退化定義悪用 / load-bearing hyp / name laundering): silent fix しない。signature 改変 + sorry 化が必要だが、見つけた turn では **(a) defect の場所と種類を報告**、**(b) その上に build しない**で止める。実際の rewrite は当該 declaration の owner / 別 task として扱う。一時的に既存 docstring に `@residual(defect:<kind>)` を **TODO marker として書込む** (signature はまだ defect 形のまま、auditor が後で迎える) のも可だが、その場合「defect 残置中」を明示。
- **tier 4 legacy** (`@audit:suspect/staged`、散文 `🟢ʰ`): tier 5 ほど urgent ではない。当該 file を current task で touch するなら incidental に sorry-based に migrate、touch しないなら触らない。

タスクリストや snapshot 文書に分散保管しない (code が SoT)。語彙詳細 → `docs/audit/audit-tags.md`。

### sorry を書けない箇所 (def / Prop RHS / inductive constructor) での対処順序

`sorry` は proof body にしか書けない。`def` / `abbrev` / `Prop := ...` の RHS / `inductive` constructor 等が詰まったときの対処は以下の順:

1. **第一選択 — 定義書換で `sorry` を proof body に逃がす** (→ 「Mathlib-shape-driven Definitions」)。
   textbook の formulation を直接 def 化せず、結論型を Mathlib 結論形に合わせて再定義 → 性質を別 `theorem` で述べる → body `sorry` + `@residual(<class>:<slug>)` に持ち込む。これが基本ルート。例: `IsXxxHypothesis : Prop` を補題 `xxxInequality : ... := by sorry` に分割し、原 def は補題呼び出しに置き換える / shared sorry 補題化 (audit-tags.md「共有 Mathlib 壁」)。

2. **第二選択 (暫定) — `@audit:defect(<kind>)` でマークして tier 5 のまま残す**。
   第一選択が当該セッションで無理 (循環構造解消に上流再設計必要 / signature 改変の影響範囲が大 / vacuously-true wrapper として acknowledged 等) な場合は signature を defect 形のまま残し、docstring に `@audit:defect(<kind>)` (`circular` / `prop-true` / `launder` / `degenerate` / `false-statement` / `false-hypothesis` から選択、語彙 → `docs/audit/audit-tags.md`「Defect kind 語彙」) + `@audit:retract-candidate(<reason>)` または `@audit:closed-by-successor(<plan-slug>)` を併記する。これは **後の (1) を待つ暫定マーカー** であり stable な resting state ではない (tier 5)。残す場合は (a) なぜ (1) が無理だったか 1 行散文、(b) 後続 plan slug、の 2 点を docstring に書く。

**禁止** (= 上記 tells 再掲、マーカー無しでの導入は tier 5 silent defect): `Prop := True` placeholder / 仮説型≡結論の `:= h` 循環 / load-bearing `*Hypothesis` predicate に核を bundle / 退化定義悪用。

**判定の一言**: 「その仮説は前提条件 (regularity) か、それとも証明の核心 (load-bearing) か」。前者 OK、後者は **書いてはいけない** — sorry に置き換える。詳細 → `docs/textbook-roadmap.md`「完成判定 / 検証強度の基準」「Mathlib 壁の 4 分類」。

**honesty 階層** (`docs/audit/audit-tags.md`「Honesty 階層」が SoT):

```
Tier 1: @audit:ok                                                 ← 最高 honest
Tier 2: sorry + @residual(<class>:<slug>)                         ← 新規実装の唯一の正規撤退口
Tier 3: @audit:superseded-by / @audit:retract-candidate           ← bookkeeping (履歴 / 削除候補)
Tier 4: legacy @audit:suspect / @audit:staged / @audit:defer / @audit:closed-by-successor / 散文 🟢ʰ  ← 旧方針で許容、新方針で defect 寄り
Tier 5: @audit:defect / 循環 := h / :True slot / 退化定義悪用 / name laundering  ← 真の defect
```

**一番 honest なのは `sorry`** — コンパイラ可視 + 「ごめんね」と明示する隠蔽不能なマーカー。旧方針で許容されていた load-bearing hypothesis (`@audit:suspect`、🟢ʰ) は tier 4 = sorry-based より strictly less honest なので、新規導入禁止 + legacy 発見は incidental migration 推奨。

## Independent honesty audit (orchestrator 必須)

実装サブエージェントが新規に `sorry` + `@residual(<class>:<slug>)` を含む commit を作った場合、orchestrator は当該セッション中 (遅くとも `InformationTheory.lean` 編入 commit 前) に **独立 audit subagent** を 1 件起動する。実装 agent の self-申告だけでは **classification (`<class>:<slug>` の正しさ)** + **signature の honesty** を誰も独立に検証していない状態 (書いた本人 = 申告者)。

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
