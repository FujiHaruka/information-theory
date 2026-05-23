# Defect cleanup — ワーカー prompt テンプレート（そのまま Agent に渡す）

オーケストレータはこのファイルのブロックを **ほぼ verbatim** で `Agent(prompt: ...)` に渡す（`<...>` だけ置換）。設計の根拠と全体像は `defect-cleanup-plan.md`、判定 doctrine は `worker-prompts.md` の CORE を参照。

- 並列起動: 複数ワーカーは **1 メッセージ内に複数 `Agent` 呼び出し** を並べて同時起動。**同時 5 cap**。
- mutating タスク（削除 / 書き換え）は `isolation: "worktree"` を必ず指定。
- read-only タスク（DB タグ付け / 抽出）は worktree 不要。
- 全 mutating ワーカー: 起動時に CLAUDE.md「Parallel orchestration」boilerplate を **prompt 冒頭に貼る**（このファイルでは `<<BOILERPLATE>>` と略記）。
- `Common2026.lean` は worker が触らない（orchestrator が直列で集約編集）。
- `--db` 省略時は既定 DB（`docs/audit/honesty.db`）。

---

## CORE-CLEANUP（mutating ワーカー共通・省略禁止）

```
You are a defect-cleanup worker for the common-2026 Lean 4 + Mathlib project. The honesty audit produced 101 defect rows (each tagged with refs/cluster_id/dag_position/bucket in `docs/audit/honesty.db`). Your job is to execute the bucket assigned to your batch WITHOUT regenerating a new honesty defect.

## Honesty doctrine (standard B — never violate)
A 0-sorry file is NOT a completion if any of:
- circular: hypothesis type ≡ conclusion type, body essentially `:= h`.
- true_residual: real obligation hidden behind `True` in an unused slot.
- degenerate_def: conclusion (or a def it uses) vacuous / trivially true.
- load_bearing_hyp dishonest: hypothesis carries the proof's CORE and the name does not say so.
- name_laundering: `_discharged` / `_full` / `_unconditional` while a hypothesis is still open.

When in doubt, prefer **honest-rebrand** (named load-bearing hyp, `verdict=suspect`) over a forced "fix". Only mark `verdict=ok` if the theorem is genuine AND complete.

## Tool (SQLite worklist; never write raw SQL)
  deno run -A scripts/audit_db.ts <cmd>
  show     --id <ID>
  list     --status defect [--bucket B] [--cluster C] [--refs-max N] [--refs-min N]
  verdict  --id <ID> --status <ok|suspect|defect|skip> --verdict <code> --note "..." --agent <AGENT>
  tag      --id <ID> [--cluster X] [--dag terminal|helper] [--bucket ...]

## Constraints
- DO NOT edit `Common2026.lean`. Report removed/renamed module paths in your final summary; the orchestrator integrates imports.
- DO NOT create `feat/...` branches. Stay on your worktree branch.
- DO NOT introduce `sorry`. Either complete honestly, retract, or rebrand (named hyp ≠ conclusion, docstring marks load-bearing).
- Verification gate: every touched file must pass `lake env lean Common2026/<path>.lean` silent (0 error, 0 sorry).
- Autonomous commit on your worktree branch; no push.
```

---

## W0-S0 — `audit_db.ts` 拡張（Sonnet 1, no worktree）

`Agent(model:"sonnet", subagent_type:"general-purpose", prompt: 下記)`。

```
Extend `scripts/audit_db.ts` (Deno + SQLite) for the defect-cleanup phase. Spec is in `docs/audit/defect-cleanup-plan.md` §"ツール".

1. ALTER `audit` table (idempotent): add columns `refs INTEGER`, `cluster_id TEXT`, `dag_position TEXT`, `bucket TEXT`. Use `PRAGMA table_info(audit)` to check before adding.

2. New subcommands (follow existing style — small helpers, no raw SQL exposed to callers):
   - `refs-bulk [--status defect] [--db F]`
     For each row in scope: look up `short_name` and `module` from `theorems`; run
       rg -w -c --type lean --glob '!<module>' <short_name> Common2026
     to count cross-file references; sum the counts; write to `audit.refs`.
     If `short_name` matches multiple `fqn` rows in `theorems`, fall back to an fqn-qualified count: derive a unique module-tail (e.g., for `Common2026.MAC.Foo.bar` use `Foo.bar`) and re-run `rg -w --type lean --glob '!<module>' -c '\b<tail>\b' Common2026`. If that resolves the ambiguity, write that count; otherwise leave `refs` NULL and log a warning. Downstream (W0-S5) treats NULL = hub (conservative).
     Print final histogram on stderr: `refs=0: N`, `1-4: N`, `5-14: N`, `≥15: N`.
   - `tag --id <ID> [--cluster X] [--dag terminal|helper] [--bucket retract|honest-rebrand|actually-fix] [--db F]`
     Update only the columns provided (UPDATE ... SET col=? WHERE id=?).
   - `tag-bulk --ids <ID1,ID2,...> [--cluster X] [--dag ...] [--bucket ...] [--db F]`
     Same as `tag` but for many ids in one transaction.
   - Extend `list`: accept `--cluster X`, `--bucket B`, `--dag D`, `--refs-min N`, `--refs-max N`, `--order-by refs|cluster_id|bucket|fqn`. Output JSON now also includes `refs, cluster_id, dag_position, bucket` columns.

3. Validation: run `deno check scripts/audit_db.ts` (or `deno run -A scripts/audit_db.ts stats --db /tmp/sanity.db` after `cp docs/audit/honesty.db /tmp/sanity.db`) to confirm no runtime error. Do NOT run mutating commands against `docs/audit/honesty.db` yet.

Commit on current branch (single concise message). Report: which subcommands added, the histogram from a dry run on /tmp/sanity.db.
```

---

## W0-S1 — refs-bulk 実行（orchestrator 直接 or Sonnet 1）

```
deno run -A scripts/audit_db.ts refs-bulk --status defect
```

ヒストグラム stderr を user に提示 → W0-S1.5 で threshold 確定（user 1-line approve）。

---

## W0-S2 — 既知 4 cluster 書き戻し（Sonnet 1, no worktree）

`Agent(model:"sonnet", subagent_type:"general-purpose", prompt: 下記)`。

```
Read `docs/audit/honesty-audit-report.md` §"Cross-cutting root causes". For each of the 4 root clusters, list the defect `id`s that belong to that cluster (the report names each predicate / theorem family). Then tag them in the DB.

Cluster names (use exactly these strings):
- Prop_True_passthrough
- WhittakerShannon_placeholder
- MAC_alias_chain
- AWGN_midecomp_swap

For each cluster:
1. Identify the member fqns from the report.
2. For each fqn: `deno run -A scripts/audit_db.ts list --status defect | rg <fqn>` to get its id.
3. `deno run -A scripts/audit_db.ts tag --id <ID> --cluster <CLUSTER>`
   (or use `tag-bulk --ids` if multiple ids share a cluster).

Report a table: cluster → list of (id, fqn) tagged.
```

---

## W0-S3 — 長尾 cluster 発見 + 全件 cluster_id 付与（Sonnet 1, no worktree, **並列化しない**）

`Agent(model:"sonnet", subagent_type:"general-purpose", prompt: 下記)`。並列化しない理由: cluster 命名の一貫性を 1 主体に集約。

```
The 4 known clusters are already tagged. Now assign `cluster_id` to ALL remaining defect rows. Use ONE consistent naming scheme (short snake_case derived from a shared root fqn or a shared structural pattern).

0. Inventory existing cluster_ids first (avoid collisions / near-duplicates with the 4 known names):
   deno run -A scripts/audit_db.ts list --status defect --order-by cluster_id
   Note the set of existing cluster_id values; any new name MUST be distinct (no substring overlap with `Prop_True_passthrough` / `WhittakerShannon_placeholder` / `MAC_alias_chain` / `AWGN_midecomp_swap`).
1. Get the candidates:
   deno run -A scripts/audit_db.ts list --status defect --cluster NULL
2. For each defect, run `show --id <ID>` to see signature + flags. Group by:
   - shared root predicate (multiple defects depend on the same project-defined `Is*` predicate)
   - same-file dense occurrence (≥3 defects in one module is a cluster candidate)
   - same `verdict` code + same family (e.g. all `name_laundering` in `Common2026/MAC/...`)
3. For each group ≥2 members: invent a cluster_id like `<family>_<pattern>` (e.g. `LZ78_passthrough`, `BMI_alias`). For singletons: tag as `isolated`.
4. `tag --id <ID> --cluster <CLUSTER>` (or `tag-bulk` per cluster).
5. DO NOT modify `verdict` / `note` — just `cluster_id`.

Report: count of new clusters discovered, member counts, and the `isolated` total. Under 300 words.
```

---

## W0-S4 — dag_position terminal 抽出 + 付与（Sonnet 1, no worktree）

`Agent(model:"sonnet", subagent_type:"general-purpose", prompt: 下記)`。

```
Tag defect rows whose fqn is a "terminal" (import endpoint or roadmap capstone). All others stay default (NULL → treated as helper).

1. Read `Common2026.lean` (the library root). Every `import Common2026.<X>` line is a candidate terminal module. Note the modules.
2. Read `docs/textbook-roadmap.md` and extract chapter-end capstone theorem names (look for headings like "capstone" / "main theorem" / chapter conclusions like `shannon_coding_theorem`, `awgn_converse`, `brunn_minkowski_*`).
3. Get all defect ids: `deno run -A scripts/audit_db.ts list --status defect`. For each, check whether its `module` is in the terminal-module set OR its `fqn` matches a capstone name.
4. For matching ids: `tag --id <ID> --dag terminal` (use `tag-bulk` per batch).
5. Do NOT tag others — NULL is treated as helper downstream.

Report: count tagged terminal, with their (module, fqn). Under 200 words.
```

---

## W0-S5 — bucket 確定（Sonnet 1, no worktree）

`Agent(model:"sonnet", subagent_type:"general-purpose", prompt: 下記)`。`<THRESHOLD>` は S1.5 で決まった値を埋める。

```
Assign `bucket` to every defect row using a fixed rule (no judgment per row — apply the decision matrix mechanically).

Threshold (from refs-bulk histogram):
- leaf:  refs = 0
- local: 1 ≤ refs ≤ <LOCAL_MAX>     # default <LOCAL_MAX>=4
- mid:   <LOCAL_MAX>+1 ≤ refs ≤ <MID_MAX>   # default <MID_MAX>=14
- hub:   refs ≥ <MID_MAX>+1
- **NULL refs** (short_name collision unresolved by `refs-bulk`): treat as hub (most conservative — never auto-retract a row whose true reach is unknown).

Rule table (verdict code from `audit.verdict`) — **this table is the SSOT for bucket assignment; the plan §"決定マトリクス" is rationale only**:
| verdict             | leaf       | local            | mid              | hub              |
|---------------------|------------|------------------|------------------|------------------|
| name_laundering     | retract    | actually-fix     | actually-fix     | actually-fix     |
| true_residual       | retract    | honest-rebrand   | honest-rebrand   | retract          |
| circular            | retract    | honest-rebrand   | honest-rebrand   | retract          |
| degenerate_def      | retract    | honest-rebrand   | honest-rebrand   | retract          |
| load_bearing_hyp    | retract    | honest-rebrand   | honest-rebrand   | retract          |
| mathlib_wall_misuse | retract    | honest-rebrand   | honest-rebrand   | retract          |
| other               | retract    | honest-rebrand   | honest-rebrand   | retract          |

Note on circular: the rebrand worker (W1-rebrand) decides per row whether a circular defect can be saved by introducing a strictly weaker honest precondition (→ stays `honest-rebrand`) or must be retracted (→ uses the override path to flip `bucket=retract`). W0-S5 does NOT make that per-row call.

Override: if `dag_position = terminal`, never `retract` unilaterally — bump to `honest-rebrand` (preserve the capstone name, expose load-bearing hyp).

1. `deno run -A scripts/audit_db.ts list --status defect` → JSON.
2. For each row apply the rule, then `tag --id <ID> --bucket <B>`.
3. NO file reads. NO per-row judgment. Mechanical only.

Report: bucket distribution table (retract/honest-rebrand/actually-fix counts) and any rule applied via the terminal override. Under 200 words.
```

---

## W0-S6 — leaf 即削除（Sonnet 並列 3-5, worktree）

各 worker に id サブセットを割り当てる。`<IDS>` は orchestrator が `list --status defect --bucket retract --refs-max 0` を K 分割した結果。

`Agent(model:"sonnet", subagent_type:"general-purpose", isolation:"worktree", prompt: <<BOILERPLATE>> + CORE-CLEANUP + 下記)`。

```
## Your batch: leaf retraction
Delete the following defect declarations (refs=0, bucket=retract, no caller):
<IDS>

For each id:
1. `deno run -A scripts/audit_db.ts show --id <ID>` → get module + line.
2. Open the file, delete the declaration (and its docstring directly above). If the file becomes empty (no theorems left, only imports), delete the whole file.
3. After all deletions in a module: `lake env lean Common2026/<module>.lean` must be silent.
4. `deno run -A scripts/audit_db.ts verdict --id <ID> --status skip --verdict <original> --note "leaf retract (refs=0)" --agent leaf-<K>`
5. DO NOT edit `Common2026.lean`. Record any whole-file deletions for the final report.

Commit per file or per cluster (small messages). Final report:
- ids successfully retracted (count + list)
- whole-file deletions (module paths) — orchestrator will remove these from `Common2026.lean`
- any id you could NOT retract and why (e.g. discovered a hidden caller via lake error)
```

---

## W1-retract — cluster 一括 retract（Sonnet, worktree, 並列最大 5）

`Agent(model:"sonnet", subagent_type:"general-purpose", isolation:"worktree", prompt: <<BOILERPLATE>> + CORE-CLEANUP + 下記)`。

```
## Your cluster: <CLUSTER_ID> (bucket=retract)
Members:
<IDS_WITH_FQN>

Strategy: remove the root definition and all callers. Imports stay in caller files for now (orchestrator handles `Common2026.lean`).

1. `list --cluster <CLUSTER_ID>` to confirm scope.
2. Identify the root: the predicate / definition that the others depend on (usually the one with most refs or named in `audit.note`).
3. Delete in topological order: leaves first, then root.
4. After each module is touched: `lake env lean Common2026/<module>.lean` silent.
5. `verdict --id <ID> --status skip --verdict <original> --note "cluster retract: <CLUSTER_ID>" --agent retract-<K>` per member.
6. DO NOT edit `Common2026.lean`. Record whole-file deletions for the final report.

Final report: members retracted (count), whole-file deletions (paths), and any blocking issue.
```

---

## W1-rebrand — cluster honest-rebrand（**Opus**, worktree, 並列最大 5）

`Agent(model:"opus", subagent_type:"general-purpose", isolation:"worktree", prompt: <<BOILERPLATE>> + CORE-CLEANUP + 下記)`。

```
## Your cluster: <CLUSTER_ID> (bucket=honest-rebrand)
Members:
<IDS_WITH_FQN>

Goal: turn each defect into an HONEST suspect — named load-bearing hypothesis, docstring openly marks it as load-bearing.

For each member:
1. `show --id <ID>` → read signature + body location.
2. Read the file (the actual `.lean`). Identify the load-bearing piece:
   - If a hypothesis is `True` in an unused slot → replace with a NEW named predicate `h_<descriptive_name> : <the real obligation>`. The new predicate type MUST NOT equal the conclusion type (no circular rebrand).
   - If a definition is `:= True` or vacuous → replace with the intended honest statement (NOT the theorem's conclusion), keeping the predicate's role as a precondition.
   - If the body discharges via `:= h` where `h`'s type matches the conclusion → rewrite the hypothesis to a strictly weaker, honest precondition that `h` could plausibly provide. `sorry` is NEVER allowed as an escape. If no honest weaker precondition exists, switch to retract — see "Override → retract" under step 6.
3. Update the docstring to lead with one of these markers:
   - `🟢ʰ load-bearing hypothesis — NOT a discharge.`
   - `🟢ʰ Mathlib-wall residual: <which wall>.`
   followed by what the hypothesis carries.
4. If the name contains `_discharged` / `_full` / `_unconditional` → rename without that suffix (rename callers in the same cluster only; cross-cluster callers stay defect for now).
5. `lake env lean Common2026/<module>.lean` silent.
6. `verdict --id <ID> --status suspect --verdict load_bearing_hyp --note "honest-rebrand: <one-line what is now load-bearing>" --agent rebrand-<K>`
   - **Override → retract**: if you decided to retract this row (no honest weaker precondition exists, or any self-check below failed irrecoverably), do ALL THREE in this order: (a) `tag --id <ID> --bucket retract`, (b) delete the declaration in the file (and its docstring; if the file becomes empty, delete the file and record the path for the orchestrator), (c) `verdict --id <ID> --status skip --verdict <original> --note "rebrand→retract: <reason>" --agent rebrand-<K>`. Then continue with the next member.

Honesty self-check before committing each member:
- New hypothesis type ≠ conclusion type? (else: circular → retract instead)
- **Non-vacuous predicate**: pick 2-3 representative callers of this rebrand (root defs in a cluster touch many); mentally expand the new predicate against each caller's instantiation and confirm it is NOT trivially provable (`True`-equivalent, `x = x`, `0 = 0`, `∀ x ∈ ∅, ...`, ...). (else: degenerate-by-reformulation → retract.)
- **Hypothesis is actually used**: the new named hyp appears syntactically in the proof body (not just decoratively in the signature). (else: degenerate — the body would still discharge without it → retract.)
- Docstring openly says load-bearing? (else: dishonest)
- No `True` placeholder AND new predicate is not `True`-equivalent under expansion? (else: still defect)
- No `sorry`? (else: invalid)

Final report: per member — old verdict → new (suspect + reason). Flag any you converted to retract.
```

---

## W1-fix — cluster actually-fix（Sonnet, worktree, 並列最大 5）

`Agent(model:"sonnet", subagent_type:"general-purpose", isolation:"worktree", prompt: <<BOILERPLATE>> + CORE-CLEANUP + 下記)`。

```
## Your cluster: <CLUSTER_ID> (bucket=actually-fix)
Members:
<IDS_WITH_FQN>

Goal: resolve alias / identity issues WITHOUT adding mathematical content.

Typical fix shapes:
- alias chain (e.g. `MACAchievableWithError ≡ IsMACRandomCodebookMarkov`): collapse to one canonical name, replace callers, delete the others.
- swap (e.g. `IsAwgnMIDecomp` ≈ different predicate): the theorem is provable as stated; rewrite the body to actually prove it (small lemma chain, no new hypothesis).
- name_laundering with provable content: same as above — write the missing 5-30 lines.

For each member:
1. `show --id <ID>` → read the file.
2. Apply the smallest fix that removes the defect — NO new hypothesis, NO `sorry`, NO True placeholder.
3. If the fix balloons past ~50 lines or requires a new lemma: STOP — change `bucket` to `honest-rebrand` (`tag --id <ID> --bucket honest-rebrand`) and report it to orchestrator for the next rebrand batch.
4. `lake env lean Common2026/<module>.lean` silent.
5. `verdict --id <ID> --status ok --verdict ok --note "actually-fix: <one-line>" --agent fix-<K>`

Final report: per member — fix shape (alias/swap/proof-added) and line delta. Flag any you bumped to honest-rebrand.
```

---

## W2-sweep — isolated bucket-driven sweep（mixed Sonnet/Opus, worktree, 並列最大 5）

W2 は **bucket で dispatch**（category ではない — bucket は W0-S5 が category × refs から既に決定済）。`cluster_id=isolated` の残り defect を 3 つのバッチに分けて W1-* prompt をそのまま再利用する:

| bucket フィルタ | 再利用 prompt | model | 取得コマンド |
|---|---|---|---|
| `retract` | W1-retract | Sonnet | `list --status defect --cluster isolated --bucket retract` |
| `honest-rebrand` | W1-rebrand | **Opus** | `list --status defect --cluster isolated --bucket honest-rebrand` |
| `actually-fix` | W1-fix | Sonnet | `list --status defect --cluster isolated --bucket actually-fix` |

prompt 差分: "## Your cluster: `<CLUSTER_ID>`" を "## Your isolated sweep batch (bucket=`<B>`)" に置換、`Members:` に該当 id 列を埋める。それ以外は完全同一 (honesty doctrine / self-check / override 含む)。

並列度: 同時 5 cap、worktree、`Common2026.lean` 不可触、起動 boilerplate 必須 — W1 と同じ。file-disjointness pre-check (波1 の orchestrator 直列前処理) も同じ — id 群を `module` で groupby して 5 worker に disjoint 配分。

---

## オーケストレータの集約タスク（worker 完了後）

各波の worker batch 完了ごとに orchestrator が直列で:

1. **`Common2026.lean` import 整理**: 全 worker から戻ってきた whole-file deletion path を集約 → `Common2026.lean` から該当 `import Common2026.<X>` 行を削除 → `lake env lean Common2026.lean` silent 確認 → 専用 commit（決定#4）。
2. **DB 整合性確認**: `deno run -A scripts/audit_db.ts list --status defect --bucket <B>` が想定残数に減ったか確認。
3. **次バッチ launch**: 並列 5 cap で次の cluster (波1) / bucket-sweep バッチ (波2) を投入。
