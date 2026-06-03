# Shannon: Hoeffding `@audit:suspect` → sorry-based migration plan

> **Parent**: [`hoeffding-tradeoff-moonshot-plan.md`](hoeffding-tradeoff-moonshot-plan.md)
> + 関連 [`hoeffding-tradeoff-sandwich-plan.md`](hoeffding-tradeoff-sandwich-plan.md) /
> [`hoeffding-sandwich-discharge-inventory.md`](hoeffding-sandwich-discharge-inventory.md) /
> [`hoeffding-exponent-level-redef-plan.md`](hoeffding-exponent-level-redef-plan.md)。
> 本 plan は **proof completion ではなく `@audit:suspect` 語彙の honesty 強化**
> (`docs/audit/audit-tags.md`「Deprecated」+「移行レシピ」) を目的とする独立 workstream。

## Context

### なぜ Hoeffding が pilot か

`.claude/handoff-sorry-migration.md` (2026-05-25) は次セッションの pilot family 選定を
「小 (~6 file)」「中」「大」の 3 段階に分類した。Hoeffding 系は次の条件で **小 pilot** に該当:

- 対象 9 file (`HoeffdingTradeoff.lean` ほか) で `@audit:suspect` 19 件 (legacy tier 4)。
- `@audit:staged` / `@audit:defer` / `@audit:closed-by-successor` / 散文 `🟢ʰ` は **0 件**。
- **既存 `sorry` キーワードも 0 件** (verbatim 確認: `rg -nw 'sorry' InformationTheory/Shannon/Hoeffding*.lean` の 3 ヒットは全て docstring 内の文字列リテラル ``sorry`` または `0-sorry`)。
  → ブリーフ「既存 sorry 3 件」は誤計数。実数は 0。
- 移行対象がほぼ単一の plan slug (`hoeffding-tradeoff-moonshot-plan` 16 件 + `hoeffding-tradeoff-sandwich-plan` 3 件) に偏っており、`@residual(plan:...)` の対応関係を 1 対 1 で評価しやすい。
- 「load-bearing predicate bundling 容認 → sorry-based 移行」の典型パターン (`IsHoeffdingLagrangeHyp` / `IsHoeffdingInteriorMinimizer` / `IsHoeffdingInteriorGradient`) を含み、tier 4 vs tier 5 の判定が実地で問われる。pilot 結果が WynerZiv / EPI / AWGN への移行レシピ拡張の参考になる。

### 上位 moonshot plan との関係

`hoeffding-tradeoff-moonshot-plan.md` は L-H4 (sandwich の variational 縮退) により
**Phase C/D を defer して `hoeffding_tradeoff_with_hypothesis` で close** している。
本 plan は **その defer 状態を変えない**。 sorry-based 移行は

- 仮説束 (`IsHoeffdingInteriorMinimizer` 等) の中の **load-bearing claim** を仮説から外して **本文 `sorry`** に降ろす、
- regularity (`IsHoeffdingMinimizerFullSupport` の `∀ a, 0 < Qstar a` 等) は precondition なので残す、
- variational 仮説 (`h_liminf` / `h_limsup`) の load-bearing 性は wrapper を **honest variational pass-through** として残すか **本体 `sorry` + `@residual(plan:hoeffding-tradeoff-sandwich-plan)`** に降ろすかを declaration 単位で判断する、

という書換であり、**proof completion** (Phase C/D の実 closure) は別 workstream (`hoeffding-tradeoff-sandwich-plan.md` 等) に残る。

### Honesty workflow と DoD

本 plan の DoD は `CLAUDE.md`「Definition of Done — 2 段階」の **type-check done**:
- 各 file `lake env lean InformationTheory/Shannon/<file>.lean` が 0 errors、
- 各新規 `sorry` に `@residual(<class>:<slug>)` タグが付き、
- 各 Phase 完了時に `honesty-auditor` を起動して classification を独立検証する。

`@audit:ok` (proof done) は **本 plan の出力にはならない** — Phase C/D の analytical closure (Sanov LDP per-Qstar / Stein typicality) が completion の必要条件であり、本 plan の scope 外。

## Approach

**file 単位 sweep を 2 Phase に分割**、共有 wall lemma は **集約しない** (理由は下記)。

### 戦略の選択軸

`.claude/handoff-sorry-migration.md`「Load-bearing context」が示す 2 つの軸 (incidental migration / family sweep、shared wall 集約の要否) を本 family について次のように決める:

1. **family sweep を採用** (incidental ではなく一括)。理由:
   - 19 件の suspect が **3 つの load-bearing predicate** (`IsHoeffdingInteriorGradient` / `IsHoeffdingInteriorMinimizer` / `IsHoeffdingLagrangeHyp`) に集中しており、ある file の predicate を外すと依存 file の signature が機械的に更新を要する。incidental だと file 間 drift が起きやすい。
   - 19 件全体で 1 PR 規模 (中央値 ~300 行のうち docstring 書換 + signature 改変 + body `sorry` 化が主体、新規 proof は書かない)。1-2 セッションで sweep できる規模。

2. **共有 sorry 補題に集約しない**。理由:
   - 19 件の suspect の closure 担当は **すべて同じ plan** (`hoeffding-tradeoff-moonshot-plan` の Phase B / Phase C/D defer、または `hoeffding-tradeoff-sandwich-plan`) で、Mathlib 壁 (`wall:stam` 等) に該当しない。`audit-tags.md`「Wall name register」表のいずれにも該当する壁名がない。
   - 検証: `docs/audit/audit-tags.md` の Wall name register に `hoeffding-tradeoff` 系 wall は登録されていない (`stam` / `csiszar` / `n-dim-gaussian-aep` / `sphere-volume` / `continuous-aep` / `nyquist-2w-dof` / `multivariate-mi` / `joint-typicality-multi` / `epi-n-dim` / `fourier`)。
   - したがって `@residual` の class は **`plan:`** で揃え、shared wall lemma の置き場所 (新規 `HoeffdingWalls.lean` 等) は不要。

### 移行レシピ (declaration 単位)

`docs/audit/audit-tags.md`「移行レシピ」をそのまま適用するが、Hoeffding 系では declaration ごとに **3 つのパターン** が出現する:

- **パターン P (predicate consumer)**: signature が load-bearing predicate hypothesis (`IsHoeffdingLagrangeHyp` / `IsHoeffdingInteriorMinimizer` / `IsHoeffdingInteriorGradient`) を取り、body はそれを field destructure するだけ。
  - 移行: predicate hypothesis を **削除**、結論型は変えない、body `sorry` + `@residual(plan:hoeffding-tradeoff-moonshot-plan)`。
  - 注意: 同じ predicate を複数 file で消費しているため、predicate **定義側** (`HoeffdingSandwichBody.lean` の `IsHoeffdingMinimizerFullSupport` を除く 3 つ) を `def`/`structure` 削除するか、`@audit:retract-candidate(load-bearing-predicate)` で deprecate するかは Phase 2 で判定 (下記「未決事項」)。

- **パターン V (variational pass-through)**: signature が `h_liminf` / `h_limsup` を hypothesis として取り、body は `tendsto_of_le_liminf_of_limsup_le` 一発。これは **honest variational pass-through** として load-bearing ではない (achievability / converse 本体ではない slim wrapper)。
  - 移行: signature **変えない**、`@audit:suspect` タグだけ削除し `@residual` も付与しない (= regularity hyp 扱い)。
  - ただし auditor 視点で「load-bearing か変動 hyp か」が境界例なので、Phase 2 中に honesty-auditor が判定する。

- **パターン C (constructive bridge)**: signature が `IsHoeffdingTiltMinimal` 等の **すでに in-tree で discharge 済の primitive** を取る。
  - 検証: `isHoeffdingTiltMinimal_of_constraint_eq` (`HoeffdingMinimizerAttainment.lean:206`) が in-tree 純構成的に discharge 済 (verbatim 確認、wall でない)。
  - 移行: tag を `@audit:suspect` から **削除**するだけ (residual を新規に作らない、type-check done のまま)。

詳細な per-declaration の pattern 判定は次セクション「在庫」表で示す。

### Phase 分割

- **Phase 1 — Cleanup pass (low-risk substitution)**: パターン V / C に該当する declarations (variational pass-through wrapper 5 件 + constructive bridge 1 件) を file ごとに sweep。
  signature 改変なし、`@audit:suspect` タグ削除のみ。
- **Phase 2 — Predicate retreat (signature 改変)**: パターン P (load-bearing predicate consumer) 13 件を sweep。
  predicate hypothesis を signature から削除、body を `sorry` + `@residual(plan:hoeffding-tradeoff-moonshot-plan)` に降ろす。
  Phase 2 完了で predicate 定義側 (`IsHoeffdingInteriorGradient` / `IsHoeffdingInteriorMinimizer` / `IsHoeffdingLagrangeHyp`) が unused になる場合は `@audit:retract-candidate(load-bearing-predicate)` を付与。

Phase 順を選んだ理由: Phase 1 (低 risk) を先行することで、Phase 2 の signature 改変中に file 間 drift が起きても影響が変動 wrapper 側に閉じる。逆順だと Phase 2 の sorry 化が Phase 1 (variational) の signature を変えてしまう可能性がある。

## 在庫: 19 件の `@audit:suspect` の verbatim 分類

verbatim 確認方法: `InformationTheory/Shannon/Hoeffding*.lean` を Read で
`@audit:suspect` 周辺 docstring + 直後 `theorem` signature + body 1-3 行を実コードから読み込み、
「signature の hypothesis が load-bearing か regularity か」を 1 件ずつ判定。

各 declaration の `path:line` は `@audit:suspect` タグ行 (docstring 末尾)。declaration 名はその直後。

| file:line | decl 名 | suspect の核 (1 行) | パターン | 移行後 class:slug | 備考 |
|---|---|---|---|---|---|
| `HoeffdingInteriorBody.lean:194` | `isHoeffdingInteriorMinimizer_of_gradient` | `IsHoeffdingInteriorGradient` 仮説経由で interior minimizer 構成。`h_grad : IsHoeffdingInteriorGradient` が L-H4-FS の log-singularity 主張を bundle | P | `plan:hoeffding-tradeoff-moonshot-plan` | predicate `IsHoeffdingInteriorGradient` (file:109) の唯一の consumer。Phase 2 で predicate も `@audit:retract-candidate` 候補 |
| `HoeffdingInteriorBody.lean:275` | `hoeffding_tradeoff_sandwich_at_interior_via_predicate` | `IsHoeffdingInteriorMinimizer` 仮説 + 変動 `h_liminf`/`h_limsup` を pass-through。body は `hoeffding_tradeoff_sandwich_via_predicate` を呼ぶだけ | P (predicate 消費) + V (変動 hyp) | `plan:hoeffding-tradeoff-moonshot-plan` | Phase 2 で `IsHoeffdingInteriorMinimizer` 削除。変動 hyp は残す |
| `HoeffdingInteriorBody.lean:308` | `hoeffding_tradeoff_sandwich_at_interior_via_gradient` | 上の variant、`IsHoeffdingInteriorGradient` 経由 | P + V | `plan:hoeffding-tradeoff-moonshot-plan` | 同上 |
| `HoeffdingInteriorBody.lean:343` | `hoeffdingE2_interior_minimizer_via_predicates` | `IsHoeffdingInteriorGradient` 仮説で `Qstar` 存在を主張、existential conclusion | P | `plan:hoeffding-tradeoff-moonshot-plan` | predicate 削除、conclusion は existential のまま、body `sorry` |
| `HoeffdingInteriorGradientBody.lean:238` | `isHoeffdingInteriorMinimizer_of_lagrange` | `IsHoeffdingLagrangeHyp` の `mem ∧ realises` を `IsHoeffdingInteriorMinimizer` に転写 | P | `plan:hoeffding-tradeoff-moonshot-plan` | predicate `IsHoeffdingLagrangeHyp` (file:222) の core consumer |
| `HoeffdingInteriorGradientBody.lean:250` | `isHoeffdingInteriorMinimizer_exists_of_lagrange` | 上の existential variant | P | `plan:hoeffding-tradeoff-moonshot-plan` | 同上 |
| `HoeffdingInteriorGradientBody.lean:263` | `isHoeffdingMinimizerFullSupport_of_lagrange` | `IsHoeffdingLagrangeHyp` 経由で full-support 抽出 | P | `plan:hoeffding-tradeoff-moonshot-plan` | 同上、Phase 2 |
| `HoeffdingInteriorGradientBody.lean:279` | `hoeffdingE2_interior_minimizer_via_lagrange` | `IsHoeffdingLagrangeHyp` 仮説で existential `Qstar`. body は `h_lag.mem` / `h_lag.realises` の destructure | P | `plan:hoeffding-tradeoff-moonshot-plan` | predicate 削除、existential conclusion |
| `HoeffdingInteriorGradientBody.lean:295` | `csiszar_pythagoras_at_lagrange` | `IsHoeffdingLagrangeHyp` から Pythagoras を派生 | P | `plan:hoeffding-tradeoff-moonshot-plan` | 同上 |
| `HoeffdingInteriorGradientBody.lean:316` | `hoeffding_tradeoff_sandwich_at_lagrange` | `IsHoeffdingLagrangeHyp` 仮説 + 変動 `h_liminf`/`h_limsup`。最も ergonomic な interior entry point | P + V | `plan:hoeffding-tradeoff-moonshot-plan` | 同上 |
| `HoeffdingSandwichBody.lean:281` | `hoeffding_tradeoff_sandwich_via_predicate` | `IsHoeffdingMinimizerFullSupport` (= `∀ a, 0 < Qstar a`、純 regularity) + 変動 `h_liminf`/`h_limsup` + `_hQs_mem`/`_hQs_min` (underscore = unused) | V のみ (regularity hyp は OK) | (タグ削除のみ) | `IsHoeffdingMinimizerFullSupport` は alias `∀ a, 0 < Qstar a` で純 regularity。残りは変動 hyp pass-through。**Phase 1 で `@audit:suspect` 削除のみ、residual 不要** |
| `HoeffdingSandwichBody.lean:315` | `hoeffding_tradeoff_sandwich_at_boundary_alpha_ge_kl` | 境界 `α ≥ klDivPmf P₂ P₁` で `Qstar := P₂` 構成、変動 hyp は pass-through。body は in-tree の `hoeffdingE2_minimizer_at_boundary_alpha_ge_kl` 呼出 (constructive) | V のみ | (タグ削除のみ) | Phase 1。境界 case は L-H4-FB で full discharge 済 (verbatim 確認、file:228) |
| `HoeffdingLagrangeIVTBody.lean:202` | `isHoeffdingTiltMinimal_realises` | `IsHoeffdingTiltMinimal` (= `IsMinOn`、Csiszár I-projection minimality の primitive) を仮説に取り `realises` に転写。primitive 自体は `HoeffdingMinimizerAttainment.lean:206` の `isHoeffdingTiltMinimal_of_constraint_eq` で **constructive discharge 済 (verbatim 確認)** | C | (タグ削除のみ) | `IsHoeffdingTiltMinimal` は wall ではない。Phase 1 で `@audit:suspect` 削除 |
| `HoeffdingLagrangeIVTBody.lean:239` | `isHoeffdingLagrangeHyp_of_minimal` | IVT `mem` + `IsHoeffdingTiltMinimal` 仮説 → `IsHoeffdingLagrangeHyp` 構築 | C | (タグ削除のみ) | 同上 |
| `HoeffdingLagrangeIVTBody.lean:257` | `exists_isHoeffdingLagrangeHyp_of_minimal` | `IsHoeffdingTiltMinimal` 量化仮説 + IVT existential | C | (タグ削除のみ) | 同上 |
| `HoeffdingLagrangeIVTBody.lean:281` | `isHoeffdingInteriorMinimizer_of_ivt` | IVT + `IsHoeffdingTiltMinimal` → `IsHoeffdingInteriorMinimizer` (load-bearing predicate を **構築**する側) | C | (タグ削除のみ) | 同上。ただし結論型は `IsHoeffdingInteriorMinimizer` で、Phase 2 で predicate 自体を deprecate するときに connectness を再判定 |
| `HoeffdingSandwich.lean:291` | `hoeffding_tradeoff_sandwich` | 変動 `h_liminf`/`h_limsup` のみ仮説、body は `tendsto_of_le_liminf_of_limsup_le` (boundedness は in-file discharge 済) | V | (タグ削除のみ) | Phase 1。slim sandwich wrapper、honest variational pass-through。slug `hoeffding-tradeoff-sandwich-plan` は本来 Phase C/D を指すが、wrapper 自身は load-bearing でない |
| `HoeffdingSandwichDischarge.lean:187` | `hoeffding_tradeoff_of_asymptotics` | 変動 hyp pass-through (`hoeffding_tradeoff_sandwich` への rename wrapper)。docstring に judgement log #1 (fixed-α scaffolding が tradeoff curve に対応しないこと) を保持 | V | (タグ削除のみ) | Phase 1。judgement log は docstring に残す |
| `HoeffdingTradeoff.lean:297` | `hoeffding_tradeoff_with_hypothesis` | **4 hypothesis form**: `h_liminf` / `h_limsup` / `h_bdd_le` / `h_bdd_ge` をすべて pass-through、body は `tendsto_of_le_liminf_of_limsup_le` 一行 | V | (タグ削除のみ) | Phase 1。最も透明な variational pass-through |

集計 (パターン別):
- P (predicate 削除 + `sorry` 化): **10 件** (Phase 2)
- P+V (predicate + 変動 hyp 同時): **3 件** (Phase 2 で predicate のみ削除、変動 hyp は残す)
- V (純 variational pass-through): **5 件** (Phase 1、タグ削除のみ)
- C (in-tree 構成済 primitive 経由): **4 件** (Phase 1、タグ削除のみ)

→ Phase 1 で 9 件処理 (タグ削除のみ、新規 `sorry` なし)、Phase 2 で 13 件処理 (新規 `sorry` 10-13 件発生、predicate signature 3 件改変)。

## Phase 詳細

### Phase 1 — Cleanup pass (低 risk、新規 sorry なし) 📋

- [ ] **1.1** `HoeffdingSandwichBody.lean` Phase 1 候補 2 件 (`hoeffding_tradeoff_sandwich_via_predicate` / `hoeffding_tradeoff_sandwich_at_boundary_alpha_ge_kl`) の `@audit:suspect` 削除。
  - `IsHoeffdingMinimizerFullSupport` は `def := ∀ a, 0 < Qstar a` (verbatim 確認、file:127) → 純 regularity hyp。signature 改変不要。
  - `lake env lean InformationTheory/Shannon/HoeffdingSandwichBody.lean` で type-check done 確認。
- [ ] **1.2** `HoeffdingLagrangeIVTBody.lean` Phase 1 候補 4 件 (`isHoeffdingTiltMinimal_realises` / `isHoeffdingLagrangeHyp_of_minimal` / `exists_isHoeffdingLagrangeHyp_of_minimal` / `isHoeffdingInteriorMinimizer_of_ivt`) の `@audit:suspect` 削除。
  - `IsHoeffdingTiltMinimal` は `IsMinOn` (`Prop`) で in-tree 構成的 closure (`HoeffdingMinimizerAttainment.lean:206`) が verbatim 存在。primitive predicate 扱い、load-bearing ではない。
  - `isHoeffdingInteriorMinimizer_of_ivt` の結論型は `IsHoeffdingInteriorMinimizer` (load-bearing predicate を **構築**する側)。Phase 2 で predicate 定義が `retract-candidate` 化された場合、本 wrapper の利用者は Phase 2 完了時点で消えている想定 (auditor が verify)。
- [ ] **1.3** `HoeffdingSandwich.lean` / `HoeffdingSandwichDischarge.lean` / `HoeffdingTradeoff.lean` の variational pass-through wrapper 3 件 (`hoeffding_tradeoff_sandwich` / `hoeffding_tradeoff_of_asymptotics` / `hoeffding_tradeoff_with_hypothesis`) の `@audit:suspect` 削除。
  - `h_liminf` / `h_limsup` は achievability / converse の **claim そのもの**ではなく、Phase C/D の closure plan (`hoeffding-tradeoff-sandwich-plan.md`) で別途閉じる **scaffolding pass-through**。
  - 判定境界例: 「variational 仮説は load-bearing か?」 → honesty-auditor の独立判定対象。auditor が DEFECT 判定なら `@residual(plan:hoeffding-tradeoff-sandwich-plan)` 付き sorry に降ろす (撤退ライン参照)。
- [ ] **1.4** Phase 1 完了時 honesty-auditor 起動。対象: 9 件すべての declaration。verdict 確認後 commit。

**Phase 1 DoD**: 9 件で `@audit:suspect` 0 件、新規 `sorry` 0 件、`lake env lean` 各 file 0 errors。

**proof-log**: no (mechanical tag removal、interesting なし)。

### Phase 2 — Predicate retreat (signature 改変 + 新規 sorry) 📋

- [ ] **2.1** `HoeffdingInteriorBody.lean` 4 件 (`isHoeffdingInteriorMinimizer_of_gradient` / `hoeffding_tradeoff_sandwich_at_interior_via_predicate` / `hoeffding_tradeoff_sandwich_at_interior_via_gradient` / `hoeffdingE2_interior_minimizer_via_predicates`)。
  - signature 改変: `IsHoeffdingInteriorGradient` / `IsHoeffdingInteriorMinimizer` 仮説を **削除**。結論型は変えない (`existential ∃ Qstar` / `Tendsto` / `IsHoeffdingMinimizerFullSupport` のまま)。
  - body: `sorry` + docstring 末尾に `@residual(plan:hoeffding-tradeoff-moonshot-plan)` を **書き込む** (旧 `@audit:suspect` 行を置換)。
  - 変動 hyp (`h_liminf` / `h_limsup`) はそのまま signature に残す (V パターン項)。
  - **regularity hyp** (`hP₁_pos` / `hP₂_pos` / `hP₁_sum` / `hP₂_sum` / `h_alpha_nn` / `h_alpha_lt`) は precondition なので残す。

- [ ] **2.2** `HoeffdingInteriorGradientBody.lean` 6 件 (`isHoeffdingInteriorMinimizer_of_lagrange` / `isHoeffdingInteriorMinimizer_exists_of_lagrange` / `isHoeffdingMinimizerFullSupport_of_lagrange` / `hoeffdingE2_interior_minimizer_via_lagrange` / `csiszar_pythagoras_at_lagrange` / `hoeffding_tradeoff_sandwich_at_lagrange`)。
  - `IsHoeffdingLagrangeHyp` 仮説を **削除**、body `sorry` + `@residual(plan:hoeffding-tradeoff-moonshot-plan)`。
  - 変動 hyp は `hoeffding_tradeoff_sandwich_at_lagrange` のみで残る、それ以外は predicate 削除のみで signature 縮小。

- [ ] **2.3** Predicate 定義側の処理 (`HoeffdingInteriorBody.lean:109/123` / `HoeffdingInteriorGradientBody.lean:222`):
  - Phase 2.1 / 2.2 完了後、3 つの predicate (`IsHoeffdingInteriorGradient` / `IsHoeffdingInteriorMinimizer` / `IsHoeffdingLagrangeHyp`) の利用者を `rg -n 'IsHoeffdingInteriorGradient|IsHoeffdingInteriorMinimizer|IsHoeffdingLagrangeHyp' InformationTheory/` で再確認。
  - **依存ゼロなら**: `@audit:retract-candidate(load-bearing-predicate)` を docstring 末尾に付与 (削除はしない、history record として残す)。
  - **依然依存ありなら**: 「未決事項」セクション #1 参照 → user 判断仰ぐ。
  - 同時に `IsKLGradientHyp` / `IsHoeffdingTiltMinimal` (Phase 1 で in-tree closure 確認済の primitive) は **触らない** — 構成的 lemma の primitive。

- [ ] **2.4** Phase 2 完了時 honesty-auditor 起動。対象: 13 件すべての declaration + 3 つの predicate 定義。verdict 確認後 commit。

**Phase 2 DoD**:
- 13 件で `@audit:suspect` 0 件、`@residual(plan:hoeffding-tradeoff-moonshot-plan)` タグ付き `sorry` 10-13 件 (V+P の 3 件は predicate 削除のみで sorry 不要かどうか auditor が判定)。
- 3 つの load-bearing predicate が `@audit:retract-candidate` または「未決」マーク付き。
- `lake env lean` 各 file 0 errors、`InformationTheory.lean` の import 行は変更なし (declaration 名は維持)。

**proof-log**: yes (`docs/shannon/proof-log-hoeffding-sorry-migration-phase2.md`)。理由: Phase 2 は signature 改変 + body `sorry` 化を 13 件で行うため、honest 判定境界 (V+P の 3 件で predicate 削除後に変動 hyp だけ残すべきか、それも `sorry` 化すべきか) の判定理由を残す。

### Phase V — verify + plan の集約 📋

- [ ] **V.1** 全 9 file で `lake env lean` 確認 (Phase 2 で signature 改変があったため dependent file の olean refresh が必要。CLAUDE.md「After upstream edits」参照)。
- [ ] **V.2** 集計コマンド実行:
  ```bash
  rg '@audit:suspect' InformationTheory/Shannon/Hoeffding*.lean | wc -l      # = 0
  rg '@residual\(plan:hoeffding-tradeoff-moonshot-plan\)' InformationTheory/Shannon/Hoeffding*.lean | wc -l
  rg -nw 'sorry' InformationTheory/Shannon/Hoeffding*.lean
  ```
- [ ] **V.3** `hoeffding-tradeoff-moonshot-plan.md` 冒頭 banner 更新 (sorry-based 移行完了の追記)。
- [ ] **V.4** Pilot 知見を `.claude/handoff-sorry-migration.md` または後続 family plan 用テンプレートに反映:
  - shared wall lemma 集約が **本 family では不要** だった事実 (wall name register に該当なし) を記録。後続 family が「同じく集約不要」なのか確認する手順を残す。
  - 「既存 sorry 件数」の自動計数を `rg -nw 'sorry'` (word-boundary) で行うべき (docstring 内の文字列リテラル誤計数を防ぐ)。

## 撤退ライン

- **L-MIG-1 (variational hyp が auditor で load-bearing 判定された場合)**: Phase 1 の 3 件 (`hoeffding_tradeoff_sandwich` / `hoeffding_tradeoff_of_asymptotics` / `hoeffding_tradeoff_with_hypothesis`) について auditor が「`h_liminf`/`h_limsup` は achievability/converse 本体と等価」と判定したら、それらを Phase 2 相当の処理 (body `sorry` + `@residual(plan:hoeffding-tradeoff-sandwich-plan)`、signature の変動 hyp は **残す** — 削除すると signature 改変が広範に波及するため) に降格。Phase 1 のタグ削除のみは undo。
- **L-MIG-2 (Phase 2 で predicate を消すと依存先で大量に signature drift が起きる場合)**: 3 つの predicate の使用箇所が Phase 2 で全件処理済かを `rg` で再確認後、依存先が残っているなら未決事項 #1 を user に escalate して **Phase 2 を中断** (Phase 1 は close 可能)。本 pilot が「sweep agent / scripts なし」(handoff-sorry-migration)の制約下で完走しないと判明した時点で escalate。
- **L-MIG-3 (Phase C/D closure と方向不一致)**: 本 plan の `sorry` 化が `hoeffding-tradeoff-sandwich-plan.md` の Phase C/D 進行と衝突 (例: 後者が `IsHoeffdingInteriorMinimizer` predicate を closure の入口として使う設計) した場合、本 plan は Phase 2 を pause、Phase C/D 側 plan の signature を変更しない範囲で predicate を residual 化する別レシピを検討。
- **L-MIG-4 (Approach 変更: pilot scope を縮める)**: Phase 2 が 1 セッションで完走しない / honesty-auditor が DEFECT を多発させる場合、`HoeffdingInteriorBody.lean` 4 件のみで pilot を close し、`HoeffdingInteriorGradientBody.lean` 以降は後続 family sweep として別 plan に分離。

## 未決事項

1. **`IsHoeffdingInteriorGradient` / `IsHoeffdingInteriorMinimizer` / `IsHoeffdingLagrangeHyp` の deprecate 方針**: Phase 2 で全 consumer が `sorry` 化された場合、predicate 定義は (a) 削除する / (b) `@audit:retract-candidate` 付きで残す / (c) public API として残し続ける、のどれを選ぶか。本 plan のデフォルトは (b)。user の確認待ち (`@audit:superseded-by` 候補が無いため、削除より retract-candidate 推奨)。

2. **`HoeffdingSandwich.lean` variational pass-through の honesty 判定**: `hoeffding_tradeoff_sandwich` の `h_liminf` / `h_limsup` は achievability / converse の **claim そのもの**を仮説に取っているか (load-bearing) それとも下流 wrapper の都合上抽出された **scaffolding pass-through** か。Phase 1 ではデフォルトで後者 (= タグ削除のみ) と判断したが、honesty-auditor が前者と判定した場合 L-MIG-1 を発動。

3. **proof done を本 plan で目指さない方針の明示確認**: 本 plan の DoD は **type-check done** のみ。Phase C/D (achievability / converse の analytical closure) は **未着手のまま**で本 plan は close する。`hoeffding-tradeoff-moonshot-plan.md` の Phase C/D defer 状態は変えない。user の合意確認のため明示。

## 判断ログ

書く頻度: 方針変更 / 撤退ライン発動 / 当初仮定の修正があったとき。append-only。

1. **2026-05-25 plan 起草**: lean-planner agent (本セッション) が `InformationTheory/Shannon/Hoeffding*.lean` 9 file の `@audit:suspect` 19 件を verbatim 読込で per-declaration 分類。「既存 sorry 3 件」(handoff の brief 記述) は誤計数で **実数 0 件** であることを `rg -nw 'sorry'` で確認 (3 ヒットは docstring 内の文字列 ``sorry`` / `0-sorry`)。pilot 戦略を「file 単位 sweep + shared wall 集約なし (該当 wall 不在)」に確定。Approach の 2 軸決定根拠を在庫表で示した。

2. **2026-05-25 Phase 1 完了**: 9 件タグ削除 + lake env lean 0 errors。honesty-auditor verdict `defect 0 / ok 8 / questionable 1` (#9 `isHoeffdingInteriorMinimizer_of_ivt`)、結論型が load-bearing predicate を返す唯一の declaration のため docstring に Phase 2 連動の retract-candidate note を追記して closure。L-MIG-1 (variational hyp の load-bearing 化) は発動せず。

3. **2026-05-25 Phase 2.1 / 2.2 完了 + constructive recovery**: 13 declarations のうち 8 件で signature 改変 (predicate hypothesis 削除) + body `sorry` + `@residual(plan:hoeffding-tradeoff-moonshot-plan)`、1 件 (`isHoeffdingMinimizerFullSupport_of_lagrange`) は **planner 指示と異なり constructive recovery** に切替 — 結論型 `IsHoeffdingMinimizerFullSupport (hoeffdingTilt P₁ P₂ lam)` (= `∀ a, 0 < hoeffdingTilt P₁ P₂ lam a`) が `hoeffdingTilt_pos` で `h_lag` 不要に純構成的 closure 可能と inline 判定、不要 sorry を作らない原則を優先。残り 4 件 (`isHoeffdingInteriorMinimizer_exists_of_lagrange` + ... 含む) は transitive sorry / 直接 sorry。

4. **2026-05-25 Phase 2 派生波及 (2 件)**: Phase 2.2 `isHoeffdingInteriorMinimizer_of_lagrange` の signature 改変で既存 caller 2 件が type error。同 family 内なので Phase 2 incidental 修正:
   - `HoeffdingMinimizerAttainment.lean:298` `isHoeffdingInteriorMinimizer_of_constraint_eq` — caller signature 保持のため 5 引数を underscore 化 + body から余分引数削除。本来 in-tree constructive な closure だったが transitive sorry に降格、docstring で明示。
   - `HoeffdingLagrangeIVTBody.lean:284` `isHoeffdingInteriorMinimizer_of_ivt` — 同様に `_h_kl` / `_h_min` underscore 化。Phase 1 で `@audit:suspect` を削除した declaration の body が transitive sorry に変わった。
   両件とも `@residual` タグは付与せず、docstring 散文で transitive 性を明示 (Lean 型システムで sorry は伝播するため、上流の `@residual` が closure 責任を保有)。

5. **2026-05-25 Phase 2.3 + 2.4 audit**: 3 predicate (`IsHoeffdingInteriorGradient` / `IsHoeffdingInteriorMinimizer` / `IsHoeffdingLagrangeHyp`) に `@audit:retract-candidate(load-bearing-predicate)` を付与。Phase 2.4 honesty-auditor 起動、verdict `defect 0 / ok 10 / questionable 6` (slug 細分化未実施 / docstring 文言 / transitive vocabulary 未整備)。questionable のうち docstring 文言 refine 2 件 + transitive vocabulary 散文化 3 件を即時適用、slug 細分化は未対応 (`plan:hoeffding-tradeoff-moonshot-plan/phase-b` vs `/phase-c-d` の候補は後続 family または別 patch)。L-MIG-2 (predicate 削除時の波及大量化) は発動せず。

6. **2026-05-25 pilot finding (audit-tags.md 拡張提案)**: 本 pilot で **transitive sorry の表現語彙** が未整備であることが発覚。即興で `(plan:hoeffding-tradeoff-moonshot-plan, transitive)` 形式を検討したが docstring 散文に降ろし、vocabulary divergence を回避。後続 family sweep 前に `audit-tags.md` の `@residual(<class>:<slug>)` EBNF 拡張 (例: `@residual(<class>:<slug>[:transitive])`) を別 PR で検討する。本 finding は handoff-sorry-migration.md に明記。

7. **2026-05-25 Phase V verify 完了**: 全 9 file (+ `HoeffdingMinimizerAttainment.lean`) で `lake env lean` 0 errors。`@audit:suspect` 0 件、`@residual(plan:hoeffding-tradeoff-moonshot-plan)` 8 件 (直接 sorry)、`@audit:retract-candidate(load-bearing-predicate)` 3 件 (3 predicate)。`rg -nw 'sorry'` の word-boundary 計数で実 sorry 8 件 (4 in HoeffdingInteriorBody + 4 in HoeffdingInteriorGradientBody) を確定。
<!-- 後続セッションで判断変更があれば下記に追記 (append-only):
8. **YYYY-MM-DD <要点>**: <変更理由 + 撤退ラインへの紐付け>。
-->
