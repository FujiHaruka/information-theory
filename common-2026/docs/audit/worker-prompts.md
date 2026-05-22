# Honesty audit — ワーカー prompt テンプレート（そのまま Agent に渡す）

オーケストレータはこのファイルのブロックを**ほぼ verbatim** で `Agent(prompt: ...)` に渡す（`<...>` だけ置換）。doctrine を取りこぼすと偽陰性が出る（calibration run #1 で実証）ので、CORE は省略・要約しないこと。

- 全ワーカー: `subagent_type: "general-purpose"`（Read/Bash/Grep が要る。**`lean-implementer` 等のコード編集エージェントは使わない** — 監査は read-only）。
- DB パス: **本番シフト・QA は既定 DB**（`docs/audit/honesty.db`、`--db` 省略）。**calibration のみ `/tmp/cal.db` コピー**。
- 並列起動: 複数ワーカーは**1メッセージ内に複数 `Agent` 呼び出し**を並べて同時起動。各ワーカーは固有 `--agent` 名。

---

## CORE（全タスク共通・省略禁止）

```
You are a honesty-audit worker for a Lean 4 + Mathlib formalization project (cwd = repo root). A theorem can pass machine-checking (`0 sorry`) yet be dishonest or incomplete: its claim is weaker than it looks, or a hypothesis silently does the proof's hard work. Classify each theorem you are given.

## Verdict codes
- `circular`: hypothesis type ≡ conclusion, body essentially `:= h`.
- `sorry`: depends on sorry/sorryAx.
- `true_residual`: a real obligation hidden behind `True` in an unused slot.
- `degenerate_def`: the conclusion (or a def it uses) is vacuous / trivially true.
- `load_bearing_hyp`: a hypothesis (often a project-defined predicate like `IsXxxRegularity` / a `*Hypothesis` / `*Reduction` argument) bundles the proof's CORE rather than being a precondition.
- `name_laundering`: the name claims more than the statement (`_discharged`/`_full`/`_unconditional` with open hypotheses).
- `mathlib_wall_misuse`: claims "blocked by Mathlib" when actually a solvable choice.
- `other`: none of the above (explain in --note).
- `ok`: genuine AND complete — no hypothesis carries the core.

## ★ LOAD-BEARING JUDGMENT DOCTRINE (apply rigorously — this is the crux)
1. The docstring's self-assessment is to VERIFY, not trust. "genuine", "honest hypotheses", "sup-sandwich", "none is the conclusion" do NOT make it `ok`. Conversely 🟢ʰ / "absent from Mathlib" / "load-bearing" / "hypothesis pass-through" / "NOT a discharge" / "the wall" are POSITIVE INDICATORS of load-bearing. Derive the verdict from statement + body + definitions; you MAY contradict the doc.
2. Judge the hypothesis bundle JOINTLY (core-reconstruction test): "If I grant all these hypotheses, do they hand me the key equality / achievability + converse / the hard bound — the substance the theorem claims to prove?" If YES → load_bearing_hyp, EVEN IF no single hypothesis equals the conclusion verbatim.
3. Regularity vs core checklist:
   - regularity (precondition, OK): measurability, integrability, finiteness (IsFiniteMeasure), full-support, positivity (0<P), BddAbove, summability, KKT/optimality of an auxiliary quantity.
   - core (load-bearing, NOT ok): an asserted achievability VALUE, a converse/upper bound, an asserted equality/inequality that IS (part of) the theorem's claim, anything the doc admits is "a wall / absent from Mathlib / the hard part / a hypothesis pass-through".
   - gray → `suspect`.
4. "Both branches / whole body from one hyp" tell: if a `le_antisymm` / two-sided sandwich has BOTH directions discharged by lemmas taking the SAME project-defined hypothesis (or the body's only hard step feeds a `*Hypothesis`/`*Reduction`/regularity-bundle arg into a lemma), that hypothesis is load-bearing.
5. Tier-C depth: trigger Tier C on any project-defined predicate hypothesis; depth scales — a transparent 1-line `def : Prop := <expr>` = read 1 line; a `structure` / multi-conjunct def = read all fields. Transparency lowers READ cost, not the judgment.
VERDICT RULE: if the core is carried by a hypothesis, do NOT mark `ok`. Use `--verdict load_bearing_hyp --status suspect` (or `circular` if the body literally returns the conclusion-as-hypothesis; `degenerate_def` if the gating predicate is vacuous). In the note, say whether it is honest 🟢ʰ (remaining task) or dishonest (name-laundering / false completion).

## How to read (3 tiers — escalate only as needed)
- Tier A (from the claim/show JSON: signature + doc): form a hypothesis. Enough for a blatant `defect` or out-of-scope `skip`, but NOT enough for `ok`.
- Tier B (READ THE BODY — the DB does NOT store proof bodies): `Read <module> --offset <line> --limit <body_lines+12>`. Catches circular/trivial/sorry/true_residual and whether hypotheses are actually used. Most verdicts settle here.
- Tier C (chase definitions) — ONLY when a hypothesis/conclusion is typed by a PROJECT-DEFINED predicate:
   1. locate (also confirms it is project-defined): `rg -n --type lean '^\s*(def|abbrev|structure|class|inductive)\s+<Head>\b' Common2026` — 0 hits = stdlib predicate, skip Tier C.
   2. read ONLY that definition: `Read <file> --offset <line> --limit 30` (structures may need more — read to the next decl).
   3. apply the DOCTRINE above. If undecidable → `suspect` with a note.

## Tool (a SQLite worklist; never write raw SQL). Use `deno run -A scripts/audit_db.ts <cmd>`.
  show    --id <ID>                 # index record (signature, doc, line, body_lines, flags). NOT the body.
  verdict --id <ID> --status <ok|suspect|defect|skip> --verdict <code> --note "<concise reasoning>" --agent <AGENT>
  list    --status <S> [--sample N] # read-only listing
(claim is task-specific — see below.)
```

---

## TASK A — 本番シフト（Sonnet）

`Agent(model:"sonnet", subagent_type:"general-purpose", prompt: CORE + 下記)`。`<K>` はワーカー番号。**DB は既定**（`--db` 省略）。

```
## Your shift
1. deno run -A scripts/audit_db.ts claim --agent sonnet-<K> --n 20
   (atomically leases 20 un-audited rows, most-suspicious first; JSON: id, module, line, fqn, signature, doc, flags.)
2. For EACH leased id: walk Tier A → B → (C if a project-defined predicate hypothesis is present) → then
   deno run -A scripts/audit_db.ts verdict --id <ID> --status ... --verdict <code> --note "..." --agent sonnet-<K>
   (rows from the same module are adjacent — Read that file region once and judge several.)
3. Every leased row MUST get a verdict. If any remain, deno run -A scripts/audit_db.ts release --agent sonnet-<K>. Then exit.
Report back (under 200 words): count audited, and a one-line status+verdict for any you marked defect or suspect.
```

---

## TASK B — calibration gate（Sonnet, 本番前必須）

合格基準・対象8件は `docs/audit/calibration-set.md`。**DB は `/tmp/cal.db` コピー**（事前に `cp docs/audit/honesty.db /tmp/cal.db`）。`Agent(model:"sonnet", subagent_type:"general-purpose", prompt: CORE + 下記)`。`<ID1..8>` は calibration-set.md の id。

```
## Calibration task
Audit these 8 specific theorems on the test DB. For each: show → read body → Tier C as needed → verdict.
Append `--db /tmp/cal.db` to EVERY audit_db.ts command. Use --agent cal.
IDs:
  <ID1>
  ...
  <ID8>
Steps per id: deno run -A scripts/audit_db.ts show --db /tmp/cal.db --id <ID>  → Read body → (Tier C) →
  deno run -A scripts/audit_db.ts verdict --db /tmp/cal.db --id <ID> --status ... --verdict <code> --note "..." --agent cal
Then run: deno run -A scripts/audit_db.ts list --db /tmp/cal.db --status ok
Report: a table (fqn, status, verdict, the hypothesis that carries the core if any). State which IDs ended up `ok`.
```

オーケストレータの合格判定: calibration-set.md の `LB` 6件が `list --status ok` に**1つも現れなければ合格**。1件でも `ok` → doctrine 修正 → 再走。

---

## TASK C — QA スポットチェック（Opus, 本番中〜直後）

`Agent(model:"opus", subagent_type:"general-purpose", prompt: CORE + 下記)`。**DB は既定**。オーケストレータは要約だけ受け取る。

```
## QA task
1. deno run -A scripts/audit_db.ts list --status ok --sample 30   # you fetch your own random sample
2. Re-audit each with the doctrine (show → read body → Tier C).
3. Overwrite ONLY rows you flip (ok → load-bearing etc.):
   deno run -A scripts/audit_db.ts verdict --id <ID> --status suspect|defect --verdict <code> --note "QA-flip: <reason>" --agent qa-opus
   Leave confirmed-ok rows untouched.
4. Report ONLY a summary: "K=30, flipped m: <id — reason> ...". Do not dump the bodies.
```

オーケストレータの対応: `m=0` 健全（随時継続）／`m≥1` で明白な見逃し → **停止** → flip 事例から doctrine 補強 → calibration 再走（合格まで）→ 影響母集団を `claim --status ok` で再リースし再監査。
