# Sorry-based migration runbook

> Legacy `@audit:suspect` / `@audit:staged` / 散文 `🟢ʰ` / `@audit:defer` /
> `@audit:closed-by-successor` を **`sorry` + `@residual(<class>:<slug>)`** に
> family 単位で sweep するための per-family runbook。
> Pilot: `docs/shannon/hoeffding-sorry-migration-plan.md` + commits
> `29dabff` (Phase 1) / `51fca41` (Phase 2 + V)。本 runbook は pilot 実観測を
> 並列実行可能な形に抽象化したもの。

## Scope

- 対象: `Common2026/Shannon/*.lean` 全 family。Hoeffding は closed (2026-05-25)。
- DoD: per file `lake env lean` 0 errors、`@audit:suspect` / `@audit:staged` /
  散文 `🟢ʰ` 0 件、各新規 `sorry` に `@residual(<class>:<slug>)`。
- proof done (`@audit:ok`) は本 runbook の出力にしない (= 別 workstream)。

## Phase 構造 (固定、family 共通)

```
Phase 0  Inventory     ← mathlib-inventory agent, docs-only
Phase 1  V/C cleanup   ← @audit:suspect タグ削除のみ (variational pass-through + in-tree constructive primitive 経由)
Phase 1.4 audit-1      ← honesty-auditor 起動 (Phase 1 全件)
Phase 2.1 P retreat    ← signature 改変 + body sorry + @residual (file A)
Phase 2.2 P retreat    ← signature 改変 + body sorry + @residual (file B)
Phase 2.x ripple       ← Phase 2.1/2.2 派生で caller が type drift した分の underscore 化 + 散文 transitive 明示
Phase 2.3 retract      ← 3 predicate に @audit:retract-candidate(load-bearing-predicate)
Phase 2.4 audit-2      ← honesty-auditor 起動 (Phase 2 全件 + predicate)
Phase V  verify        ← 全 file lake env lean 0 errors + handoff/banner 反映
```

各 Phase 完了時 `lake env lean <file>` が **0 errors**。`sorry` warning は許容。
ただし Phase 2 で signature 改変したら **必ず** `lake build Common2026.<改変 module>`
で olean refresh、その後 dependent 再 verify (Pilot Pattern A 参照)。

## 並列実行プロトコル

### 並列度の判断軸

| 条件 | 並列 OK? |
|---|---|
| inventory / planner (docs-only) | ✅ いつでも並列 (file 競合は brief 設計で防ぐ) |
| implementer (worktree 必須) | △ shared wall lemma 集約 family は逐次、他は並列 OK |
| audit-2 (fresh subagent) | ✅ family 単位で完了したら即起動 (並列 audit 可) |

shared wall lemma の判定: `docs/audit/audit-tags.md`「Wall name register」に
当該 family の壁名が登録済か。例:
- **集約必要**: EPI/Stam (`wall:stam`) + ParallelGaussianPerCoord
  (`wall:n-dim-gaussian-aep`) — 同じ Stam を複数 family が参照する可能性
- **集約不要**: Hoeffding (壁名なし、`plan:<slug>` で集約済)、Relay/MAC/BC
  (個別 plan slug、壁なし)

### 1 セッション当たりの推奨並列度

- **docs-only (inventory + planner)**: 4-6 family を並列起動可能 (file 競合
  なし、ブランチ規律のみ要)
- **implementer (worktree)**: 2-3 family が現実的。worktree あたり Mathlib
  symlink 7-8 GB reuse なので 3 並列でも disk 余裕、ただし parent .olean
  refresh の調整で 2 並列が安全
- **audit-2**: 各 family 完了直後に 1 件起動、orchestrator が逐次受領

### worktree 共有 (絶対遵守)

CLAUDE.md「Standard agent prompt boilerplate」と同じ:

```bash
ln -sfn /Users/haruka/dev/lean-projects/common-2026/.lake .lake
```

inner `common-2026` directory 内で実行。親の `.lake` (Mathlib 7-8 GB) を
symlink reuse。5 GB Mathlib clone は disk 破綻。

## Agent brief テンプレート

### Step 1 — Inventory (mathlib-inventory, docs-only)

```
## ゴール

`Common2026/Shannon/<family>*.lean` の legacy tag 在庫を verbatim 確認して
`docs/<area>/<family>-sorry-migration-inventory.md` に構造化テーブルで書出し。

## SoT

1. docs/audit/sorry-migration-runbook.md (本 runbook)
2. docs/audit/audit-tags.md
3. docs/shannon/hoeffding-sorry-migration-plan.md (pilot 参考)

## 出力

各 declaration 1 行で:
| file:line | decl 名 | 現タグ | 削除/置換予定タグ | パターン (P/V/C/S/H) | suspect の核 (verbatim docstring 1 行) | **circular?** | **cross-family?** |

- **circular?** — 仮説型 ≡ 結論型 で body が `:= h` (or 同等の name laundering
  `_rate` / `_existence` / `_full` 化) になっていないか。✅ なら tier 5 defect
  (Pattern F)。`@residual(defect:circular)` 付き sorry 化扱いを Phase 2 に
  含めることを inventory 段階で flag
- **cross-family?** — declaration が他 family の namespace の predicate / lemma
  を bundling / re-export していないか (`rg` で当該 file 外の use site を
  検索、複数 family namespace に跨るなら ✅)。✅ なら Pattern G (cross-family
  unified predicate) で planner 段階の判断材料

## 計数規則

- `@audit:suspect` / `@audit:staged` / 散文 `🟢ʰ` / `@audit:defer` /
  `@audit:closed-by-successor` 別に件数集計
- 既存 `sorry` 件数は **必ず `rg -nw 'sorry'` (word-boundary)** で計数。
  docstring 内文字列リテラル (``sorry``、`0-sorry`) を排除 (Pattern D)
- **既存 HONESTY ALERT / `⚠` の検出** (Pattern H): `rg '⚠|HONESTY ALERT|FALSE'`
  で著者が既に false-hypothesis 等を明示済かを検出。検出時は別行で flag、
  本 sweep scope 外として別 plan 化候補

## 構成済 family の参考

Hoeffding (pilot, 19 suspect → 0 + 8 sorry+@residual)
```

### Step 2 — Plan (lean-planner, docs-only)

```
## ゴール

`docs/<area>/<family>-sorry-migration-plan.md` を起草。in inventory の
declarations を P/V/C パターン分類し、Phase 1 (V+C cleanup) / Phase 2.1
(file A P retreat) / Phase 2.2 (file B P retreat) / Phase 2.3 (predicate
retract-candidate) に振分け。

## SoT

1. docs/audit/sorry-migration-runbook.md「Phase 構造」+「失敗パターン」
2. docs/audit/audit-tags.md 移行レシピ + Wall name register
3. docs/shannon/hoeffding-sorry-migration-plan.md (pilot reference)
4. `docs/<area>/<family>-sorry-migration-inventory.md` (前 step 出力)

## Approach の必須要件

CLAUDE.md global rule に従い Approach section を最初に。決定事項:
- file 単位 sweep か incidental か (理由付き)
- shared wall lemma 集約の要否 (Wall name register 照合)
- constructive recovery 候補の identify (結論型が `∀ a, 0 < · a` /
  `IsBoundedUnder` / `IsMinOn` の primitive で reducible な declaration は
  事前に flag、planner inventory step で取りこぼさない — Pilot Pattern B)
- transitive sorry の handling 方針 (タグ付与せず docstring 散文 — Pilot
  Pattern C)
- **tier 5 defect の inline 扱い** (Pattern F): inventory で circular?=✅ と
  flag された declaration は Phase 2 で `@residual(defect:circular)` 付き
  sorry 化を明示。silent fix しない (CLAUDE.md「検証の誠実性」)
- **cross-family unified predicate の identify** (Pattern G): inventory で
  cross-family?=✅ と flag された declaration は当該 family 単独で deprecate
  判断不可。Phase 2.3 で **predicate 削除禁止**、関係 family の planner / sweep
  完了を待って統合 plan 化候補として未決事項に escalate
- **既存 HONESTY ALERT の扱い** (Pattern H): inventory で `⚠` / `HONESTY ALERT`
  flag された declaration は本 sweep scope 外。別 plan 化候補として未決事項
  に分離

## 在庫表 (verbatim 必須)

各 declaration を Read で **verbatim 確認** (docstring + signature + body
1-3 行)。memory / inventory step を鵜呑みにしない (CLAUDE.md「具体的数値・
型予測の verbatim 確認」)。

## 未決事項

planner が判断つかない事項 (predicate deprecate 方針 / variational hyp の
load-bearing 境界判定 / proof done を目指さないことの明示) を列挙。
auditor 委任で済む項目は「auditor 判定対象」と明記。

## 撤退ライン

L-MIG-1 (variational hyp 誤判定) / L-MIG-2 (predicate 削除で大量 drift) /
L-MIG-3 (Phase C/D closure と方向衝突) / L-MIG-4 (pilot scope 縮減) を
family 文脈で書き下す。
```

### Step 3 — Implement (lean-implementer, worktree 必須)

```
## ゴール

`docs/<area>/<family>-sorry-migration-plan.md` を実装。Phase 1 → Phase 2.1
→ Phase 2.2 → Phase 2.3 順次。各 Phase 完了時 `lake env lean <file>` 0
errors を確認、commit。

## SoT

1. docs/audit/sorry-migration-runbook.md (本 runbook、特に「失敗パターン」)
2. docs/audit/audit-tags.md
3. `docs/<area>/<family>-sorry-migration-plan.md`
4. CLAUDE.md「Standard agent prompt boilerplate」+「Skeleton-driven Development」

## 運用ルール (絶対遵守、CLAUDE.md ベース + sorry-migration 追加)

1. **worktree .lake 共有**: `ln -sfn /Users/haruka/dev/lean-projects/common-2026/.lake .lake`
2. **ブランチ規律**: 起動時にいる worktree branch に居続ける。`feat/...`
   作成禁止、`git checkout` 他禁止
3. **scope**: 1 family、`Common2026/Shannon/<family>*.lean` のみ。完了時
   `Common2026.lean` の import 行は **変更しない** (declaration 名は維持)
4. **import policy**: `import Mathlib` 禁止、pinpoint
5. **commit**: 自走 commit、push なし (orchestrator が main にマージ後 push)
6. **olean refresh** (Pilot Pattern A): Phase 2 で signature 改変したら
   `lake build Common2026.<改変 module>` で olean refresh、その後 dependent
   ファイルを **必ず** `lake env lean` で再 verify。stale olean で type
   error を見逃すと caller の broken state を commit してしまう
7. **inline detection** (Pilot Pattern B): plan が「全件 sorry」と指示
   していても結論型を読み、`∀ a, 0 < · a` / `IsBoundedUnder` / `IsMinOn`
   等の regularity に reducible なら constructive recovery する。不要 sorry
   は作らない (`sorry` は真の未完成マーカー、CLAUDE.md「検証の誠実性」)
8. **transitive sorry の handling** (Pilot Pattern C): 上流の sorry に
   依存する dependent declaration には **`@residual` タグを付与しない**。
   docstring 散文で transitive 性を明示し、closure 責任は upstream の
   `@residual` が保有する旨を書く。即興 `(<class>:<slug>, transitive)`
   等の vocabulary は **使わない** (audit-tags.md 未登録)
9. **検証バー**: 各 Phase 完了時 `lake env lean <file>` 0 errors、`sorry`
   warnings 許容、各 sorry に `@residual(<class>:<slug>)` (配置 →
   audit-tags.md「配置ルール」)
10. **撤退口**: 行き詰まったら sorry + `@residual` で抜く。**禁止**:
    `*Hypothesis` predicate に核を bundling / `Prop := True` placeholder /
    仮説型≡結論の `:= h` (循環) / 退化定義悪用 (CLAUDE.md「検証の誠実性」)
11. **defect 発見**: 既存コードに defect (tier 5: 循環 := h / :True slot /
    退化定義悪用 / load-bearing hyp / name laundering) を見つけたら即報告、
    その上に積まない。tier 4 legacy (`@audit:suspect/staged`、散文 🟢ʰ) は
    current task で touch するなら incidental migration、touch しないなら
    触らない
```

### Step 4 — Audit (general-purpose subagent w/ honesty-auditor SoT brief)

orchestrator (= main agent) が起動。`subagent_type: "honesty-auditor"` は
agent registry 未登録 (CLAUDE.md「Independent honesty audit」section の
"honesty-auditor" agent type は事前定義済前提だが、現状の available
subagent types に含まれていない可能性が高い)。代替: **`general-purpose`**
agent を起動し、brief 内で SoT (`docs/audit/audit-tags.md` + CLAUDE.md
「Independent honesty audit」) を読ませる。

brief 必須項目:
- 監査対象 declaration の **(file:line + decl 名 + 削除 hypothesis +
  結論型)** を表で列挙
- verbatim verify の指示 (plan / brief を鵜呑みにせず実コード Read)
- verdict 語彙: **ok / questionable / defect** + 必要に応じて refine 提案
- L-MIG-1〜L-MIG-4 の発動条件 (verdict defect ≥ 1 件 → L-MIG-2 推奨など)

## 失敗パターン (pilot 実観測 + 回避策)

### Pattern A — stale olean で type error 見逃し

Phase 2 で upstream signature 改変直後の `lake env lean <dependent>` が
**caller の type error を見逃す**。pilot で `HoeffdingMinimizerAttainment.lean`
が `isHoeffdingInteriorMinimizer_of_lagrange` の `h_lag` 削除で broken
state に陥ったが、最初の `lake env lean` 実行で 0 errors と誤判定 (.olean
の stale 値が import 時に参照されたため)。

**回避策**: signature 改変 commit 前に必ず

```bash
lake build Common2026.Shannon.<改変 module>
```

で olean refresh、その後

```bash
for f in $(rg -l '改変 module の名前' Common2026/); do
  lake env lean "$f"
done
```

で dependent 再 verify。CLAUDE.md「After upstream edits」が SoT。

### Pattern B — planner 全件 sorry 指示の overcorrect

planner が「Phase 2 で predicate hypothesis 全件削除 → body sorry」と
一律指示するが、結論型が regularity (`∀ a, 0 < · a` / `IsBoundedUnder` /
`IsMinOn`) に reducible な declaration は constructive recovery 可能。
pilot で `isHoeffdingMinimizerFullSupport_of_lagrange` が 1 件該当 —
結論型 `IsHoeffdingMinimizerFullSupport (hoeffdingTilt P₁ P₂ lam)` =
`∀ a, 0 < hoeffdingTilt P₁ P₂ lam a` が `hoeffdingTilt_pos` で `h_lag`
不要に純構成的 closure 可能 (`IsHoeffdingMinimizerFullSupport.of_pos`)。

**回避策**:
- planner step で結論型を読み、regularity 形 (`∀ a, 0 < · a` 系 + 既存
  in-tree primitive の constructive closure 経路があるもの) を **inventory
  表で flag** ("constructive recovery 候補" 列を追加)
- implementer は inline detection で結論型を再確認、planner 指示通りでも
  recovery 可能なら sorry 化せず constructive 維持。判断ログに append。
- audit-2 で「不要 sorry」を defect ではなく questionable で flag

不要 sorry は honesty 原則「sorry は真の未完成マーカー」に反する。

### Pattern C — transitive sorry の tag 誤付与

Phase 2 で upstream を sorry 化すると、本来 constructive な caller が
transitive sorry を引き継ぐ。即興で `@residual(<class>:<slug>, transitive)`
等の suffix を付与しがちだが **audit-tags.md 未登録 vocabulary**。

**回避策**:
- 即興 suffix 禁止
- `@residual` タグは付与せず、docstring 散文で次を明示:
  ```
  Transitive `sorry` via `<upstream decl>` (Phase 2 retreat). No `@residual`
  tag is attached — the closure responsibility belongs to the upstream
  declaration's `@residual(<class>:<slug>)`.
  ```
- signature underscore 化は最小限 (caller signature 保護のみ、API 互換性)。
  declaration 自体の意味は変わらない旨を docstring に明記

### Pattern D — `sorry` 件数の docstring 文字列誤計数

`rg 'sorry'` だと docstring 内文字列リテラル (``sorry``、`0-sorry`) を
hit。pilot で「既存 sorry 3 件」と handoff brief に書いてあったが実態は
0 件 (3 hit は全部 docstring 内文字列)。

**回避策**: **必ず** `rg -nw 'sorry'` (word-boundary)。

### Pattern E — predicate retract-candidate の extract-only consumer 見落とし

Phase 2.3 で predicate を `@audit:retract-candidate` 化するとき、
hypothesis-form consumer が 0 件と判断しがちだが、`.field` 抽出 / bridge
を介した extract-only consumer (= pass-through、load-bearing claim を
inject しない) が残っていることがある。pilot で `IsHoeffdingInteriorMinimizer`
で 5 件、`IsHoeffdingInteriorGradient` で 1 件発見。

**回避策**: docstring に次のように明示:

```
`@audit:retract-candidate(load-bearing-predicate)` — all *hypothesis-form
load-bearing* consumers were retreated. N extract-only consumers remain
(pass-through, no load-bearing claim injected): <列挙>. Producer-side
constructors <列挙> remain but their bodies depend transitively on
<upstream sorry>.
```

「all in-tree consumers were retreated」と書いてしまうと字義的に false で
audit-2 で questionable。

### Pattern F — tier 5 defect (循環 := h / name laundering) を suspect 計数で見落とし

`@audit:suspect` の rg 計数だけで「全件同質」扱いすると、その中に紛れた
**tier 5 defect (循環 `:= h` / `:True` slot / 退化定義悪用 / name laundering)**
の上に sorry 化を積み上げる。Round 1 WynerZiv で 2 件発見:

- `wyner_ziv_achievability_rate (h_ach : ≤) : ≤ := h_ach` — 仮説型 ≡ 結論型
  の典型循環、name laundering で `_rate` suffix
- `wyner_ziv_achievability_existence (h_ach_existence : ∀ε∃N...) : ∀ε∃N... := h_ach_existence`
  — 同上 + `_existence` name laundering

両者は `@audit:suspect(wyner-ziv-moonshot-plan)` で `wyner_ziv_tendsto`
(constructive な `le_antisymm h_conv h_ach` 純合成、非 defect) と同一タグ。
signature を verbatim 読まないと判別不可能。

**回避策**:
- Inventory step の出力フォーマットに **circular? 列** を必須化 (本 runbook
  Step 1 ゴール参照)。各 declaration で「仮説型 ≡ 結論型?」を 1 行 check
- planner Approach に「tier 5 defect の inline 扱い」決定事項を明示。
  detected 行を Phase 2 で `@residual(defect:circular)` 付き sorry 化に分配
- implementer step でも signature を verbatim 読み、planner の指示通り
  `@residual(plan:...)` を貼ろうとしているが circular だった場合は
  `@residual(defect:circular)` に補正 (inline detection、Pattern B と同様の
  honesty 優先)
- silent fix 禁止 (CLAUDE.md tier 5 defect の扱い)。発見した turn で必ず
  signature 改変 + sorry 化のため Phase 2 plan を refine

### Pattern G — cross-family unified predicate の単独 deprecate 不可

declaration が他 family の namespace の predicate / lemma を bundling /
re-export している場合、当該 family 単独 sweep で predicate を deprecate
すると他 family の use site が broken state に陥る。Round 1 Cramer で
発見:

- `IsCramerChernoffNLetterRNUnified` — Cramér 側 `IsCramerNLetterRNCylinder`
  + `IsCaratheodoryExtensionHyp` + Chernoff 側 `IsBayesErrorPerTiltLowerBound`
  を 1 structure に bundling。Cramer sweep 単独で Phase 2.3 retract 判断
  不可

別事例 (Round 1 WynerZiv): `RelayCFBinningBody` が `IsWynerZivBinning*` 3
predicate を re-namespacing 利用 (`:127/195/262`)。Phase 2.3 で WynerZiv
側が predicate 削除すると Relay 側 broken。

**回避策**:
- Inventory step の出力フォーマットに **cross-family? 列** を必須化。各
  declaration で当該 file 外の use site を `rg` で検索、複数 family
  namespace に跨るなら ✅
- planner Approach に「cross-family unified predicate の identify」決定
  事項を明示
- 該当 predicate の Phase 2.3 では **削除禁止**、`@audit:retract-candidate`
  付与のみ + docstring 散文に「<列挙> family の <列挙> file が consumer」
  を明記
- 関係 family の planner / sweep 完了を待って統合 plan 化候補として
  planner 未決事項に escalate (実 sweep は別 session)

#### Cross-family 検出 3 段階判定 (Round 2 補強、2026-05-25)

cross-family ✅/❌ の二値判定だけでは Round 2 plans (Relay / MAC-BC / LZ78 /
BrunnMinkowski / WynerZiv Phase 2.x) で過剰検出 + 過剰回避を起こした実例があり、
inventory step では **3 段階で severity を分けて記録** する:

| Stage | 検出条件 | sweep 影響 | 対処 |
|---|---|---|---|
| **S1 散文 reference** | 他 family の declaration / file 名を docstring / コメントに mention するが `import` 無し | sweep 単独実施 OK。当該 declaration touch 時は散文を更新するのみ | inventory 表で `cross-family?` 欄に「S1: docstring mention only」と注記、Phase 2.3 で予防的処置なし |
| **S2 import 実依存** | `import Common2026.Shannon.<他 family>` あり + 当該 family の lemma / def を本体で使用 | sweep 単独実施 OK。下流 (consumer) として transitive sorry を引き継ぐが、Phase 2.x ripple で散文化対応可能 (Pattern C) | inventory 表で「S2: import + use of <decl>」と注記。Pattern C 散文 transitive 適用、predicate 自身の削除は不要 |
| **S3 infrastructure construction** | 他 family の predicate / structure を **本 family の declaration の field / constructor / type alias として bundling / re-namespacing**、または他 family 側 use site が本 family の predicate を hypothesis 形で消費する | **単独 sweep で predicate 削除すると他 family broken**。`@audit:retract-candidate(load-bearing-predicate)` 付与のみ + docstring 散文で consumer 列挙 + 統合 plan 化候補として escalate | inventory 表で「S3: <bundle 形> via <field / namespace> from <他 family>」と明記、planner 未決事項に必ず escalate |

**判定例** (Round 1/2 sweep 実観測):

| 例 | Stage | 根拠 |
|---|---|---|
| `LZ78ConverseDischarge.lean:67` の WynerZiv 言及 | S1 | docstring 散文のみ、`import` 無し (verbatim 確認済) |
| MAC/BC → Relay 名前言及 | S1 | mac-bc-sorry-migration-plan で確認、prose mention のみ |
| `BroadcastChannelSuperposition` → `MACL1Discharge` | S2 | mac-bc plan で観測、import + 経由の transitive sorry を Pattern C 散文化 |
| `IsCramerChernoffNLetterRNUnified` | S3 | Cramér + Chernoff 2 family の predicate を 1 structure に bundling、単独 deprecate 不可 (Round 1) |
| `RelayCFBinningBody` の `IsWynerZivBinning*` 3 predicate re-namespacing | S3 | Relay 側 `:127/195/262` で WynerZiv predicate を re-namespacing 利用、WynerZiv 単独 sweep で predicate 削除すると Relay broken (Round 1 WynerZiv) |

**inventory step で必須**: cross-family? 列を S1/S2/S3 のいずれかでラベル化し、planner step で
S3 のみを Phase 2.3 retract-candidate 化 + 未決事項に escalate。S1/S2 は本 sweep 内で完結可能。

### Pattern H — 既存 HONESTY ALERT / FALSE predicate の重畳

著者が既に `⚠ HONESTY ALERT` / `FALSE predicate` を docstring に明記済の
declaration を本 sweep で機械的に sorry 化すると、既存の honesty 表明が
失われる + scope 外の defect を本 plan に巻き込む。Round 1 Huffman で
発見:

- `HuffmanSwapNormalizationBody.lean:91/:181` — `EqualizingPermHypothesis` /
  `EqualizingSwapTargetHypothesis` は機械検証済の FALSE predicate、
  docstring に `⚠ HONESTY ALERT — この述語は FALSE であり discharge 不能`
  と明記。これらを hypothesis に取る 4 wrapper は vacuously-true 含意

**回避策**:
- Inventory step で `rg '⚠|HONESTY ALERT|FALSE'` を必須化 (本 runbook
  Step 1 計数規則参照)。検出時は別行で flag
- planner Approach で「既存 HONESTY ALERT の扱い」決定事項を明示。本 sweep
  scope 外として未決事項に分離 (別 plan 化候補)、本 sweep の Phase 2 では
  touch しない
- 別 plan は `audit-tags.md` の「Deprecated」表に **false-hypothesis 由来
  の vacuously-true 含意 wrapper の扱い** を別行追加するコミットとセットで
  検討 (tier 4 staged と tier 5 defect の境界例)

## audit-tags.md 拡張提案 (次の sweep 前に検討)

Pilot 由来の vocabulary gap。本 runbook は **暫定的に docstring 散文で
対応する方針** を取るが、後続 family が増えると divergence の懸念があり、
別コミットで formal 拡張を検討:

1. **`@residual(<class>:<slug>[:transitive])` の transitive suffix**:
   上流 sorry 依存の transitive sorry を tag 上で正式に表現できるよう
   EBNF 拡張。本 pilot では「タグ付与せず散文で明示」で回避。
2. **`@audit:retract-candidate(<reason>)` の reason variant 拡充**:
   - `load-bearing-predicate-empty-consumers` (consumer 0 件)
   - `load-bearing-predicate-extract-only` (extract-only consumer 残存)
   現状は単一 `load-bearing-predicate` で docstring 補足に頼っている。

## 並列実行候補 family (2026-05-25 集計)

`rg -c '@audit:suspect'` / `@audit:staged` / `🟢ʰ` / `@audit:defer` の
合算 (Hoeffding は closed):

| family | files (代表) | suspect | staged | 🟢ʰ | defer/closed | 推定サイズ | shared wall? |
|---|---|---:|---:|---:|---:|---|---|
| **EPI/Stam** | EPIL3Integration, EPIStamStep3Body, EPIStamDeBruijnConclusion, EPIStamToBridge, EPIPlumbing, EPIStamDischarge | 53 | 8 | ~0 | 2 | 大 | `wall:stam` (要集約) |
| **Relay** | RelayInnerBoundDischarge, RelayInnerBound, RelayCFBinningBody, RelayDFBlockMarkovBody, RelayCutset | 36 | ~0 | 15 | ~0 | 中-大 | (調査要) |
| **MAC/BC** | MultipleAccessChannel, BroadcastChannel, BroadcastChannelExistenceBridgeBody, MACCornerPoint, MACBodyDischarge, MACFanoConverseBody | 25 | ~0 | 18 | ~0 | 中 | (調査要) |
| **BrunnMinkowski** | BrunnMinkowskiFunctional, BrunnMinkowskiConcavity, BrunnMinkowski, BrunnMinkowskiPLBody | 30 | 1 | 6 | 2 | 中-大 | `wall:brunn-minkowski-functional` 候補 |
| **AWGN** | AWGN, AWGNMIBridge, AWGNAchievabilityDischarge, AWGNAchievability, ShannonHartley | 14 | 14 | 3 | 2 | 中 | (要確認、200+ 行 bundle predicate 既知) |
| **LZ78** | LZ78FinalGlue, LZ78ZivCombinatorics, LZ78ConverseDischarge, LZ78SMBSandwich, LZ78ZivTreeNode, LZ78AsEventualAchievability, LZ78AchievabilityLimsup | 26 | ~0 | ~0 | ~0 | 中 | なし? |
| **Huffman** | HuffmanT1APPrimeBody, HuffmanT1APPrimePartial, HuffmanSwapNormalizationBody, HuffmanSwapStepChainBody, HuffmanOptimality, HuffmanMergedIdentBody, HuffmanStrongForm | ~0 | 30 | ~0 | 2 | 中 | なし? (staged の migration recipe を pilot で確立する candidate) |
| **WynerZiv** | WynerZiv, WynerZivConverse, WynerZivAchievability, WynerZivConverseChain, WynerZivBinningCovering, WynerZivPackingBody, WynerZivCoveringBody, WynerZivBinningBody | 6 | 13 | 3 | ~0 | 中 | なし? |
| **Chernoff** | ChernoffPerTiltSanov, ChernoffPerTiltDischarge, ChernoffSanovDischarge, ChernoffConverse, ChernoffInformation | ~0 | ~0 | 8 | 19 | 中 | closed-by-successor 多め (bookkeeping 系の pilot candidate) |
| **Cramer** | Cramer, CramerLC2PhaseC, CramerPhaseDGapWorkaround | 12 | ~0 | ~0 | ~0 | 小 | なし? |
| **ParallelGaussianPerCoord** | ParallelGaussianPerCoord, ParallelGaussianPerCoordRegularity | ~0 | 1 | 5 | 5 | 小 | (EPI/Stam dependency 要確認) |
| **MultivariateDiffEntropy** | MultivariateDiffEntropy | 4 | ~0 | ~0 | ~0 | 小 | なし? |
| **RateDistortion** | RateDistortionAchievabilityPhaseEStrongFinal | 2 | ~0 | ~0 | ~0 | 最小 | なし? |
| **WhittakerShannonFull** | WhittakerShannonFull | 2 | ~0 | ~0 | ~0 | 最小 | なし? |

### 並列セッション設計の推奨

- **Round 1 (並列度高、低 risk pilots)**: Cramer / Huffman / WynerZiv の
  3 つを並列 (各小〜中、Hoeffding 同様 wall 集約不要、独立 docs path)。
  inventory + planner を並列、implementer も並列可
- **Round 2 (中規模)**: Relay / MAC・BC / LZ78 / BrunnMinkowski の 3-4
  並列 (wall 集約候補 1-2 件あり、要 wall 名 register 拡張判断)
- **Round 3 (大規模 + dependency 注意)**: EPI/Stam + ParallelGaussianPerCoord
  (shared wall:stam 集約、要逐次実行 + handoff-epi.md と統合)、AWGN
  (200+ 行 bundle predicate のため 1 セッション独占)、Chernoff
  (bookkeeping 系、`@audit:closed-by-successor` migration の pilot)

各 family について、orchestrator が「session 開始時に inventory + planner
を docs-only で 3-6 並列起動 → 結果回収 → implementer を worktree で 2-3
並列起動 → audit-2 を逐次起動 → main にマージ + push」のパターンで進める。

## 関連文書

- 本 runbook の親方針: `docs/audit/audit-tags.md`
- pilot example: `docs/shannon/hoeffding-sorry-migration-plan.md` (+ commits
  `29dabff`, `51fca41`)
- CLAUDE.md「Definition of Done — 2 段階」「検証の誠実性」「Independent
  honesty audit」「Parallel orchestration」「Skeleton-driven Development」
- handoff: `.claude/handoff-sorry-migration.md` (次セッション resume 用)
