# Shannon: Cramér `@audit:suspect` → sorry-based migration plan

> **Parent**: [`cramer-moonshot-plan.md`](cramer-moonshot-plan.md) §Phase B/C/D
> + 後継 [`cramer-lc2-discharge-moonshot-plan.md`](cramer-lc2-discharge-moonshot-plan.md) (L-D3 撤退記録)
> + 後継 [`cramer-chernoff-clt-closure-moonshot-plan.md`](cramer-chernoff-clt-closure-moonshot-plan.md)
> (interior-point unconditional 化済)。
> 本 plan は **proof completion ではなく `@audit:suspect` 語彙の honesty 強化**
> (`docs/audit/audit-tags.md`「Deprecated」+「移行レシピ」) を目的とする独立 workstream。
> Pilot reference: [`hoeffding-sorry-migration-plan.md`](hoeffding-sorry-migration-plan.md)。

## Context

### なぜ Cramér が次の sweep family か

`docs/audit/sorry-migration-runbook.md`「並列実行候補 family (2026-05-25 集計)」表で
Cramér は **small pilot** (3 file 中心 / 12 suspect 概算)。verbatim 再計数の結果:

- `InformationTheory/Shannon/Cramer*.lean` 全 6 file の `@audit:suspect` は **13 件**
  (`Cramer.lean` 4 件 / `CramerPhaseDGapWorkaround.lean` 4 件 / `CramerLC2PhaseC.lean` 4 件
  / `CramerCLTClosure.lean` 1 件)。runbook 推定の 12 件は 1 件少なめ計数。
- `@audit:staged` / `@audit:defer` / `@audit:closed-by-successor` / 散文 `🟢ʰ` /
  `NOT a discharge` / `load-bearing` 散文表現は **全 0 件**。
- 既存 `sorry` も `@residual` も **全 0 件** (`rg -nw 'sorry' InformationTheory/Shannon/Cramer*.lean`
  word-boundary 計数で 0 hit、Pilot Pattern D 適用)。
- 13 件は **3 つの plan slug** に分散:
  - `cramer-moonshot-plan` 8 件 (Cramer.lean 4 + CramerPhaseDGapWorkaround.lean 4)
  - `cramer-lc2-discharge-moonshot-plan` 4 件 (CramerLC2PhaseC.lean)
  - `cramer-chernoff-clt-closure-moonshot-plan` 1 件 (CramerCLTClosure.lean)
- 残り 2 file (`CramerLC2Discharge.lean` 171 行 / `CramerLC2DischargeExt.lean` 257 行) は
  Phase A 純構成 plumbing で **suspect 0 件**、本 plan 対象外 (touch しない)。

### 上位 moonshot との関係 (重要)

`cramer-chernoff-clt-closure-moonshot-plan.md` の **DONE-HONEST-HYPS** banner 通り、
**Cramér 下界は内部点 `a = deriv (cgf Y μ₀) lam` で既に unconditional 化済**
(`CramerCLTClosure.cramer_lower_at_cgfDeriv_unconditional`、residual largeness 仮定なし)。
すなわち 13 件の `@audit:suspect` declarations は:

- **構成的 escape route** (`CramerCLTClosure.lean` の CLT+window 経由) で **既に headline closure 達成**。
- 13 declarations は **代替 / より一般な hypothesis-form 入口** を提供する別ルート
  (`IsMeasureInfinitePiTiltedEq` / `IsCramerNLetterRNCylinder` / `IsCaratheodoryExtensionHyp`
  の各 predicate を Mathlib-gap pass-through として bundling した形)。
- したがって本 sweep の `sorry` 化は **headline proof done を破壊しない** —
  `cramer_lower_at_cgfDeriv_unconditional` 経路は本 sweep の対象外 wrapper を含まず、
  独立に残る (auditor が verify)。

`cramer-lc2-discharge-moonshot-plan.md` 自体は **L-D3 撤退** で Phase A scaffolding 止め
(Phase B-C は後継 plan へ defer 済)。本 sweep は **L-D3 撤退状態を変えない** — predicate に
bundling されている Mathlib gap (`Measure.infinitePi_tilted_eq` の n-letter RN-deriv 識別 +
Carathéodory cylinder extension) は **本 sweep の closure 対象でない**。

### Honesty workflow と DoD

本 plan の DoD は `CLAUDE.md`「Definition of Done — 2 段階」の **type-check done**:

- 各 file `lake env lean InformationTheory/Shannon/<file>.lean` が 0 errors、
- 各新規 `sorry` に `@residual(<class>:<slug>)` タグが付き、
- 各 Phase 完了時に `honesty-auditor` (or `general-purpose` SoT-brief) を起動して
  classification を独立検証する。

`@audit:ok` (proof done) は **本 plan の出力にしない** — Mathlib gap (n-letter RN-deriv
identification) の closure は本 plan の scope 外。

## Approach

**file 単位 sweep を 2 Phase に分割**、共有 wall lemma 集約は **採用しない / Pilot と同じく
plan-slug 一元** (理由は下記)。

### 戦略の選択軸

`docs/audit/sorry-migration-runbook.md`「並列実行プロトコル」+ pilot Hoeffding 在庫表が
示す 2 軸 (incidental vs family sweep、shared wall 集約の要否) を本 family について次のように決める:

1. **family sweep を採用** (incidental ではなく一括)。理由:
   - 13 件のうち 8 件 (CramerPhaseDGapWorkaround.lean 4 + CramerLC2PhaseC.lean 3 + Cramer.lean 1)
     が **共通の load-bearing predicate** (`IsMeasureInfinitePiTiltedEq` / `IsCramerNLetterRNCylinder`
     / `IsCaratheodoryExtensionHyp` または `h_tilted_lower` shape) を consumer / re-shape している。
     incidental だと chain 中の中間 wrapper が drift する。
   - Pilot Hoeffding (19 件) より小さく、Cramer.lean の `h_tilted_lower` を含めても 1-2 セッションで完走可能。

2. **共有 sorry 補題に集約しない / `plan:` で揃える**。理由:
   - 13 件の Mathlib-gap 性は **共通の壁 (n-letter RN-deriv identification of infinite-pi tilt
     + Carathéodory cylinder extension)** に帰着するが、`docs/audit/audit-tags.md`「Wall name
     register」に該当 wall **未登録**。新 wall `wall:infinite-pi-tilted-rn` の追加は別 PR で検討
     (Wall register 拡張プロセスを踏む必要)。本 sweep は pilot Hoeffding と同じく `plan:` slug
     で揃え、新 wall 命名は後続 sweep の audit-tags.md 拡張 PR に委ねる。
   - 各 declaration の closure 担当 plan は既に docstring の `@audit:suspect(<slug>)` で識別
     可能 (3 つの slug を `@residual(plan:<slug>)` にそのまま転記)。
   - shared sorry 補題化したい場合は CramerPhaseDGapWorkaround.lean の `IsCramerNLetterRNCylinder`
     / `IsCaratheodoryExtensionHyp` + CramerLC2PhaseC.lean の `IsMeasureInfinitePiTiltedEq`
     を統合する `CramerWalls.lean` 等の新 file 案があるが、**本 plan は採用せず** — predicate
     定義 3 件は touch せず `@audit:retract-candidate` または現状維持 (未決事項 #1 参照)。

### 移行レシピ (declaration 単位)

Cramér 系は pilot Hoeffding と異なり **全 13 件が pattern P** (load-bearing predicate / load-bearing
hypothesis consumer)。pattern V / C は実質ゼロ。詳細は在庫表で示すが、出現するサブパターンは:

- **パターン P-1 (load-bearing hypothesis consumer)**: signature が `h_tilted_lower` または
  `h_slice` (= ∀ε > 0, ∃C > 0, ... の Chernoff lower bound shape) を hypothesis として取り、
  body はそれを `cramer_lower` / `cramer_lower_at` 等の親に pass-through するか、CGF bridge で
  reshape する。
  - 移行: hypothesis を **削除**、結論型は変えない、body `sorry` + `@residual(plan:<slug>)`。
  - 例: `Cramer.lean:451 cramer_lower` の `h_tilted_lower`、`CramerCLTClosure.lean:463 cramer_lower_at` の `h_slice`。

- **パターン P-2 (load-bearing predicate consumer)**: signature が `IsMeasureInfinitePiTiltedEq` /
  `IsCramerNLetterRNCylinder` / `IsCaratheodoryExtensionHyp` / `IsCramerChernoffNLetterRNUnified`
  を hypothesis として取り、body はそれを field destructure / `tilted_lower_from_predicate` /
  `isMeasureInfinitePiTiltedEq_of_cylinder_density` 経由で reshape。
  - 移行: predicate hypothesis を **削除**、結論型は変えない、body `sorry` + `@residual(plan:<slug>)`。
  - 例: `CramerLC2PhaseC.lean` 4 件、`CramerPhaseDGapWorkaround.lean` 4 件。

- **パターン P-3 (Legendre-attainment hypothesis)**: signature が `hlam_opt: lam * a - cgf Λ lam
  = cramerRate ...` を hypothesis として取る。borderline — Legendre attainment は textbook 条件
  `a ≥ 𝔼[X]` + 凸性で discharge 可能だが、本 plan は **load-bearing 寄りで扱う** (pilot
  Hoeffding と同様、auditor 委任で再判定)。
  - 例: `Cramer.lean:311 cramer_upper_legendre`、`Cramer.lean:562 cramer_lower_legendre`、
    `Cramer.lean:596 cramer_tendsto`、`CramerPhaseDGapWorkaround.lean:186 cramer_tendsto_phase_d_via_cylinder`、
    `CramerLC2PhaseC.lean:185 cramer_lower_legendre_phaseC_partial_discharge`、
    `CramerLC2PhaseC.lean:218 cramer_tendsto_phaseC_partial_discharge`。
  - 移行: 親 plan が `hlam_opt` を別 plan で closure する展望なし → `hlam_opt` を残す案も
    あるが、**P-1 / P-2 と同じ slug** で sorry 化 (本体の load-bearing 部が `h_tilted_lower` /
    predicate のため、`hlam_opt` 単独で残しても意味が薄い)。auditor が「`hlam_opt` は load-bearing
    でなく precondition」と判定すれば L-MIG-1 で復元。

#### constructive recovery 候補 — 0 件

pilot Hoeffding の `isHoeffdingMinimizerFullSupport_of_lagrange` のような「結論型が
`∀ a, 0 < · a` / `IsBoundedUnder` / `IsMinOn` の regularity に reducible で in-tree primitive
で純構成的 closure 可能」な declaration は **本 sweep 13 件中 0 件** (verbatim 確認):

- `Cramer.lean` 4 件 — 結論型は `≤ -cramerRate` / `≤ liminf` / `Tendsto`、in-tree regularity ではない。
- `CramerLC2PhaseC.lean` 4 件 — 全て partial discharge wrapper、load-bearing predicate destructure。
- `CramerPhaseDGapWorkaround.lean` 4 件 — cylinder bridge + 2 wrapper + 1 unified projection、
  predicate destructure。
- `CramerCLTClosure.lean:463 cramer_lower_at` — `h_slice` shape を `cramer_lower` に pass-through、
  load-bearing。

ただし `CramerCLTClosure.lean:525 cramer_lower_at_cgfDeriv_unconditional` (suspect なし、本 sweep
対象外) は **constructive route で headline 達成済** — 本 sweep は当該 declaration を **touch
しない** (DONE-HONEST-HYPS の honest 経路を維持)。

#### transitive sorry の handling 方針 (Pilot Pattern C)

Cramer.lean / CramerLC2PhaseC.lean / CramerPhaseDGapWorkaround.lean は **chain (依存関係)** を
形成する:

```
Cramer.lean cramer_lower (sorry)
  ← CramerLC2PhaseC.lean cramer_lower_phaseC_partial_discharge (predicate hypothesis 削除 → sorry)
    ← CramerPhaseDGapWorkaround.lean cramer_lower_phase_d_via_cylinder (cylinder hypothesis 削除 → sorry)
    ← InfinitePiTiltedChangeOfMeasure.lean:380 cramer_lower_phaseC_residual_discharge (※本 sweep 対象外)
  ← CramerCLTClosure.lean cramer_lower_at (h_slice 削除 → sorry)
    ← CramerCLTClosure.lean cramer_lower_at_cgfDeriv_unconditional (※本 sweep 対象外、constructive)
```

各 wrapper を Phase 2 で個別に sorry 化するため transitive 性が発生 (上流 sorry → 下流 sorry
継承)。pilot Hoeffding と同様、**transitive sorry に `@residual` を新規付与しない** — 各 declaration
の自身の load-bearing hypothesis 削除に対して `@residual(plan:<slug>)` を 1 つ持ち、上流 sorry
への依存は docstring 散文で明示する (audit-tags.md vocabulary 未登録の `:transitive` suffix
等は使わない)。`cramer_lower_at_cgfDeriv_unconditional` のように本 sweep 対象外で constructive
経路を残すものは **touch しない**。

### Phase 分割

- **Phase 1 — Cleanup pass (V/C 該当 = 0 件)**: 本 family は V/C 候補ゼロ。**Phase 1 は実質
  skip 可** (タグ削除のみで済む declaration が無い)。`docs/audit/sorry-migration-runbook.md`
  「Phase 構造」は固定形式なので Phase 1 を **空で記録** (skip 理由を判断ログに記録)。
- **Phase 2 — Predicate / hypothesis retreat (signature 改変 + 新規 sorry)**: 13 件全てを sweep。
  - **Phase 2.1** — `Cramer.lean` 4 件 (= 親 file)。上流のため最初に sweep。
  - **Phase 2.2** — `CramerLC2PhaseC.lean` 4 件。Cramer.lean の sorry を継承する partial discharge wrapper。
  - **Phase 2.3** — `CramerPhaseDGapWorkaround.lean` 4 件。さらに cylinder layer を追加した wrapper。
  - **Phase 2.4** — `CramerCLTClosure.lean` 1 件 (`cramer_lower_at`)。独立の hypothesis-form
    wrapper。`cramer_lower_at_cgfDeriv_unconditional` は **touch しない** (constructive 経路維持)。
- **Phase 2.5 — Predicate 定義側の処理 (retract-candidate 判断)**: 3 つの load-bearing predicate
  (`IsMeasureInfinitePiTiltedEq` / `IsCramerNLetterRNCylinder` / `IsCaratheodoryExtensionHyp`)
  と 1 つの structure (`IsCramerChernoffNLetterRNUnified`) の consumer を再確認:
  - hypothesis-form consumer が全件 sorry 化されたら `@audit:retract-candidate(load-bearing-predicate)`
    付与。
  - producer-side 構成子 (`isMeasureInfinitePiTiltedEq_of_cylinder_density`、
    `IsCramerChernoffNLetterRNUnified.cramerPhaseC` 等) は本 sweep で sorry 化される consumer
    であり、Phase 2.5 で remaining が拾えれば下記の **Pattern E 注記** (extract-only consumer
    の docstring 明示) を適用。
- **Phase 2.6 — audit-2 起動 (independent honesty audit)**: 13 件全 declaration + 4 predicate/structure
  を fresh `general-purpose` agent (or `honesty-auditor`) に検証依頼。`docs/audit/sorry-migration-runbook.md`
  「Step 4」brief で起動。verdict {ok / questionable / defect} を回収後 commit。

Phase 順を選んだ理由: pilot Hoeffding は「低 risk (Phase 1) 先行 → signature 改変 (Phase 2)」を
採ったが、本 family は Phase 1 候補ゼロのため上流 → 下流 (Cramer.lean → CramerLC2PhaseC.lean →
CramerPhaseDGapWorkaround.lean → CramerCLTClosure.lean) の chain 順で sorry 伝播を確定させ、
各段 olean refresh + `lake env lean` 再 verify する (Pilot Pattern A 回避)。

## 在庫: 13 件の `@audit:suspect` の verbatim 分類

verbatim 確認方法: `InformationTheory/Shannon/Cramer*.lean` 6 file を Read で `@audit:suspect` 周辺の
docstring + 直後 `theorem` signature + body 1-3 行を実コードから読込み、「signature の hypothesis
が load-bearing か regularity か」を 1 件ずつ判定 (`Cramer.lean:200-650` / `CramerLC2PhaseC.lean:1-297`
/ `CramerPhaseDGapWorkaround.lean:1-305` / `CramerCLTClosure.lean:440-554`)。

各 declaration の `path:line` は `@audit:suspect` タグ行 (docstring 末尾)。declaration 名はその直後。

| file:line | decl 名 | suspect の核 (1 行) | パターン | 移行後 class:slug | constructive recovery? | 備考 |
|---|---|---|---|---|---|---|
| `Cramer.lean:311` | `cramer_upper_legendre` | `hlam_opt: lam·a − Λ lam = cramerRate Λ a` 経由で `cramer_upper` の `-(lam·a − Λ lam)` を `-cramerRate` に書換 | P-3 | `plan:cramer-moonshot-plan` | No (結論型は `≤ -cramerRate`、辺 1 つ書換) | `cramer_upper` 自身 (line 272) は suspect 無し、本体構成的 |
| `Cramer.lean:451` | `cramer_lower` | `h_tilted_lower: ∀ε>0,∃C>0,∀ᶠn, C·exp(-n·(lam·a−Λ+lam·ε)) ≤ μ.real{a·n ≤ ∑X i}` を hypothesis 化、body は `le_of_forall_pos_le_add` + `le_liminf_of_le` で結論を組み立てる (本体は実証明) | P-1 | `plan:cramer-moonshot-plan` | No (load-bearing tilted Chernoff lower bound) | L-C2 撤退の中核。後継 chain の入口 |
| `Cramer.lean:562` | `cramer_lower_legendre` | `hlam_opt` + `h_tilted_lower` を取り `cramer_lower` で書換 | P-3 + P-1 | `plan:cramer-moonshot-plan` | No | body は 1 行 `rw [← hlam_opt]; exact h` だが、上流 sorry を継承する |
| `Cramer.lean:596` | `cramer_tendsto` | `hlam_opt` + `h_tilted_lower` + 4 bdd hyps を取り `cramer_upper_legendre` + `cramer_lower_legendre` の sandwich | P-3 + P-1 + V (4 bdd hyps は variational regularity) | `plan:cramer-moonshot-plan` | No | sandwich 部 (`tendsto_of_le_liminf_of_limsup_le`) は variational pass-through、しかし上流 2 件が sorry なので継承 |
| `CramerLC2PhaseC.lean:97` | `tilted_lower_from_predicate` | `h_pred: IsMeasureInfinitePiTiltedEq μ₀ Y lam` を `h_tilted_lower` shape に CGF bridge (`cgf_eval_eq_cgf_base`) で reshape | P-2 | `plan:cramer-lc2-discharge-moonshot-plan` | No (predicate destructure + 純算術 reshape — borderline V/C だが load-bearing predicate consumer のため P-2 維持) | 中間 lemma、下流 3 件の bridge |
| `CramerLC2PhaseC.lean:145` | `cramer_lower_phaseC_partial_discharge` | `h_pred: IsMeasureInfinitePiTiltedEq` を取り、Phase A plumbing (`iIndepFun_eval_under_infinitePi` 等) + `tilted_lower_from_predicate` 経由で `cramer_lower` を呼ぶ | P-2 | `plan:cramer-lc2-discharge-moonshot-plan` | No | 親 `cramer_lower` の sorry を継承 + 自身の predicate hypothesis 削除で sorry |
| `CramerLC2PhaseC.lean:185` | `cramer_lower_legendre_phaseC_partial_discharge` | `hlam_opt` + `h_pred` 取り、`cramer_lower_phaseC_partial_discharge` を呼ぶ | P-3 + P-2 | `plan:cramer-lc2-discharge-moonshot-plan` | No | 1 行 `rw [← hlam_opt]; exact h` だが load-bearing hypothesis 2 件 |
| `CramerLC2PhaseC.lean:218` | `cramer_tendsto_phaseC_partial_discharge` | `hlam_opt` + `h_pred` + 5 bdd/pos hyps 取り、`cramer_tendsto` の chain | P-3 + P-2 + V | `plan:cramer-lc2-discharge-moonshot-plan` | No | Tendsto sandwich の Phase C-3 final wrapper |
| `CramerPhaseDGapWorkaround.lean:136` | `isMeasureInfinitePiTiltedEq_of_cylinder_density` | `h_cyl: IsCramerNLetterRNCylinder` + `h_cara: IsCaratheodoryExtensionHyp` から `IsMeasureInfinitePiTiltedEq` を構成 | P-2 (2 つの predicate consumer + 1 つの predicate producer) | `plan:cramer-moonshot-plan` | No (構成自体は cylinder + cara の destructure 1 行、しかし両 input が load-bearing predicate) | Pattern E 注記対象: predicate を retract-candidate 化する Phase 2.5 で extract-only consumer (本 lemma 自身) を docstring 明示 |
| `CramerPhaseDGapWorkaround.lean:160` | `cramer_lower_phase_d_via_cylinder` | `h_cyl` + `h_cara` 取り、`isMeasureInfinitePiTiltedEq_of_cylinder_density` 経由で `cramer_lower_phaseC_partial_discharge` 呼出 | P-2 (再度) | `plan:cramer-moonshot-plan` | No | 親 partial discharge wrapper の sorry を継承 + 自身の 2 predicate 削除 |
| `CramerPhaseDGapWorkaround.lean:186` | `cramer_tendsto_phase_d_via_cylinder` | `hlam_opt` + `h_cyl` + `h_cara` + 5 bdd/pos hyps 取り `cramer_tendsto_phaseC_partial_discharge` 経由 | P-3 + P-2 + V | `plan:cramer-moonshot-plan` | No | Phase D final wrapper |
| `CramerPhaseDGapWorkaround.lean:259` | `IsCramerChernoffNLetterRNUnified.cramerPhaseC` | `h: IsCramerChernoffNLetterRNUnified P₁ P₂ ...` を destructure し `h.cramer` + `h.cara` で `isMeasureInfinitePiTiltedEq_of_cylinder_density` を呼ぶ | P-2 (unified structure projection) | `plan:cramer-moonshot-plan` | No | structure 自身 (line 245) は touch せず、projection lemma 1 件のみが suspect (sibling projection `chernoffPerTilt` は suspect 無し) |
| `CramerCLTClosure.lean:463` | `cramer_lower_at` | `h_slice: ∀ε>0,∃C>0,∀ᶠn, C·exp(-n·(lam·a−cgfYμ₀+lam·ε)) ≤ μ_∞.real{a·n ≤ ∑Y(ω i)}` を hypothesis 化、CGF bridge 経由で `cramer_lower` を呼ぶ | P-1 (`h_slice` = `h_tilted_lower` shape を CGF bridge で reshape) | `plan:cramer-chernoff-clt-closure-moonshot-plan` | No | 上の `cramer_lower_at_cgfDeriv_unconditional` (suspect なし、本 sweep 対象外) で constructive consumer 1 件あり — Phase 2.4 sorry 化で **当該 consumer も transitive sorry に降格する点に注意** (constructive route が壊れる) → 撤退ライン L-MIG-3 |

集計 (パターン別):

- P-1 (load-bearing hypothesis consumer): **3 件** (Cramer.lean cramer_lower + CramerLC2PhaseC.lean tilted_lower_from_predicate + CramerCLTClosure.lean cramer_lower_at)
- P-2 (load-bearing predicate consumer): **6 件** (CramerLC2PhaseC.lean 3 + CramerPhaseDGapWorkaround.lean 3)
- P-3 + (P-1/P-2/V): **4 件 (Legendre attainment combined)** (Cramer.lean 3 + CramerLC2PhaseC.lean 1 + CramerPhaseDGapWorkaround.lean 1 ... の組合せ、重複あり)
- V / C 単独: **0 件**
- constructive recovery: **0 件**

→ Phase 1 は **skip** (V/C 候補ゼロ)、Phase 2 で 13 件全件処理 (新規 `sorry` 13 件発生、4 predicate
/ structure は Phase 2.5 で retract-candidate 化判断、`InformationTheory.lean` の import 行は変更なし)。

## Phase 詳細

### Phase 0 — Inventory ✅ (本 plan 内 inline)

上記「在庫」section が Phase 0 の出力。13 declarations を全 verbatim 確認済。

### Phase 1 — V/C cleanup 📋 (実質 skip)

- [ ] **1.1** V/C 該当 declaration の `@audit:suspect` 削除 — 該当ゼロ件、**実質作業なし**。
  判断ログ #1 に「Phase 1 skip 理由 (V/C 候補ゼロ)」を記録するのみ。

**Phase 1 DoD**: 該当作業なし。Phase 2 に直接進む。

**proof-log**: no。

### Phase 2 — Predicate / hypothesis retreat (signature 改変 + 新規 sorry) 📋

#### Phase 2.1 — `InformationTheory/Shannon/Cramer.lean` 4 件 📋

- [ ] **2.1.1** `cramer_upper_legendre` (line 312)
  - signature 改変: `hlam_opt` 仮説を **削除** (P-3、auditor 委任で復元可)。
  - signature の `(a : ℝ) (lam : ℝ) (hlam : 0 ≤ lam)` は precondition として残す
    (auditor が「`hlam` も不要」と判定すれば追加削除)。
  - 結論型 `≤ -cramerRate (X 0) μ a` は維持。
  - body: `sorry` + docstring 末尾を `@residual(plan:cramer-moonshot-plan)` で置換
    (旧 `@audit:suspect(cramer-moonshot-plan)` 行を削除)。

- [ ] **2.1.2** `cramer_lower` (line 452)
  - signature 改変: `h_tilted_lower` 仮説を **削除** (P-1)。
  - 残す regularity: `_h_indep` / `_h_meas` / `_h_ident` / `_h_bdd` (既に underscore、本来 unused だが
    signature 保持目的)、`(a : ℝ) (lam : ℝ) (hlam : 0 ≤ lam)`、`h_coboundedBelow`
    (filter regularity)。
  - 結論型 `≤ liminf ...` 維持。
  - body: `sorry` + `@residual(plan:cramer-moonshot-plan)`。

- [ ] **2.1.3** `cramer_lower_legendre` (line 563)
  - signature 改変: `hlam_opt` + `h_tilted_lower` の 2 仮説を **削除** (P-3 + P-1)。
  - 残す: 4 underscore regularity + `(a, lam, hlam, h_coboundedBelow)`。
  - 結論型 `≤ liminf` (rate `-cramerRate`) 維持。
  - body: `sorry` + `@residual(plan:cramer-moonshot-plan)`。

- [ ] **2.1.4** `cramer_tendsto` (line 597)
  - signature 改変: `hlam_opt` + `h_tilted_lower` の 2 仮説を **削除** (P-3 + P-1)。
  - 残す: 4 regularity + `(a, lam, hlam)` + `h_pos` + `h_cobdd` + `h_coboundedBelow` +
    `h_bdd_above` + `h_bdd_below` (variational pass-through、削除しない — Tendsto sandwich のため
    boundedness 4 件は precondition)。
  - 結論型 `Tendsto ... (𝓝 (-cramerRate ...))` 維持。
  - body: `sorry` + `@residual(plan:cramer-moonshot-plan)`。

- [ ] **2.1.5** `lake build InformationTheory.Shannon.Cramer` で olean refresh (Pilot Pattern A)。
  続いて依存 file (`CramerLC2Discharge.lean` / `CramerLC2DischargeExt.lean` / `CramerLC2PhaseC.lean`
  / `CramerCLTClosure.lean` / `CramerPhaseDGapWorkaround.lean` / `InfinitePiTiltedChangeOfMeasure.lean`)
  を **個別** `lake env lean` で再 verify。**特に注意**: `cramer_lower_at_cgfDeriv_unconditional`
  (Phase 2.4 で touch しない) の consumer は `cramer_lower_at` 経由で transitive sorry に降格
  するため、`lake env lean InformationTheory/Shannon/CramerCLTClosure.lean` が 0 errors のまま sorry
  warning が増えることを確認する。

#### Phase 2.2 — `InformationTheory/Shannon/CramerLC2PhaseC.lean` 4 件 📋

- [ ] **2.2.1** `tilted_lower_from_predicate` (line 98)
  - signature 改変: `h_pred : IsMeasureInfinitePiTiltedEq μ₀ Y lam` を **削除** (P-2)。
  - 残す regularity: `_hY_meas` / `_h_bdd` (既に underscore、Phase A plumbing precondition)、
    `(a lam : ℝ)`。
  - 結論型 `∀ ε > 0, ∃ C > 0, ∀ᶠ n ..., C · exp (...) ≤ μ_∞.real {...}` 維持。
  - body: `sorry` + `@residual(plan:cramer-lc2-discharge-moonshot-plan)`。

- [ ] **2.2.2** `cramer_lower_phaseC_partial_discharge` (line 146)
  - signature 改変: `h_pred : IsMeasureInfinitePiTiltedEq μ₀ Y lam` を **削除** (P-2)。
  - 残す: `hY_meas` / `h_bdd` / `(a lam, hlam)` / `h_coboundedBelow`。
  - 結論型 `≤ liminf` 維持。
  - body: `sorry` + `@residual(plan:cramer-lc2-discharge-moonshot-plan)`。
  - 上流 sorry (Cramer.lean cramer_lower) 継承の transitive 性は docstring 散文で明示
    ("transitive sorry via `cramer_lower` (Phase 2.1)" — `@residual` は付与せず 1 件のみ)。

- [ ] **2.2.3** `cramer_lower_legendre_phaseC_partial_discharge` (line 186)
  - signature 改変: `hlam_opt` + `h_pred` の 2 仮説を **削除** (P-3 + P-2)。
  - 結論型 `≤ liminf` (rate `-cramerRate`) 維持。
  - body: `sorry` + `@residual(plan:cramer-lc2-discharge-moonshot-plan)`。

- [ ] **2.2.4** `cramer_tendsto_phaseC_partial_discharge` (line 219)
  - signature 改変: `hlam_opt` + `h_pred` の 2 仮説を **削除** (P-3 + P-2)。
  - 残す variational: `h_pos` / `h_cobdd` / `h_coboundedBelow` / `h_bdd_above` / `h_bdd_below`。
  - 結論型 `Tendsto ... (𝓝 (-cramerRate ...))` 維持。
  - body: `sorry` + `@residual(plan:cramer-lc2-discharge-moonshot-plan)`。

- [ ] **2.2.5** `lake build InformationTheory.Shannon.CramerLC2PhaseC` で olean refresh、
  続いて依存 (`CramerPhaseDGapWorkaround.lean` / `InfinitePiTiltedChangeOfMeasure.lean`) を
  個別 `lake env lean` で再 verify。

#### Phase 2.3 — `InformationTheory/Shannon/CramerPhaseDGapWorkaround.lean` 4 件 📋

- [ ] **2.3.1** `isMeasureInfinitePiTiltedEq_of_cylinder_density` (line 137)
  - signature 改変: `h_cyl : IsCramerNLetterRNCylinder` + `h_cara : IsCaratheodoryExtensionHyp`
    の 2 仮説を **削除** (P-2 × 2)。
  - 残す: `(μ₀, Y, lam)` (paramter のみ)。
  - 結論型 `IsMeasureInfinitePiTiltedEq μ₀ Y lam` 維持。
  - body: `sorry` + `@residual(plan:cramer-moonshot-plan)`。
  - **Pattern E 注意**: 本 lemma を sorry 化すると `IsMeasureInfinitePiTiltedEq` の唯一の
    producer (構成子) が sorry 化される — Phase 2.5 で predicate 自身を `@audit:retract-candidate`
    化するときに「producer-side bodies depend transitively on `isMeasureInfinitePiTiltedEq_of_cylinder_density`」
    と docstring に明示。

- [ ] **2.3.2** `cramer_lower_phase_d_via_cylinder` (line 161)
  - signature 改変: `h_cyl` + `h_cara` を **削除** (P-2 × 2)。
  - 残す: ambient + `h_coboundedBelow`。
  - 結論型 `≤ liminf` 維持。
  - body: `sorry` + `@residual(plan:cramer-moonshot-plan)`。

- [ ] **2.3.3** `cramer_tendsto_phase_d_via_cylinder` (line 187)
  - signature 改変: `hlam_opt` + `h_cyl` + `h_cara` の 3 仮説を **削除** (P-3 + P-2 × 2)。
  - 残す variational: `h_pos` / `h_cobdd` / `h_coboundedBelow` / `h_bdd_above` / `h_bdd_below`。
  - 結論型 `Tendsto` 維持。
  - body: `sorry` + `@residual(plan:cramer-moonshot-plan)`。

- [ ] **2.3.4** `IsCramerChernoffNLetterRNUnified.cramerPhaseC` (line 260)
  - signature 改変: `h : IsCramerChernoffNLetterRNUnified μ₀ Y lam P₁ P₂ lamCh` を **削除** (P-2 unified)。
    結論型のみ残す ([`α : Type*`] + `Fintype` + `DecidableEq` + ... の implicit はそのまま)。
  - 結論型 `IsMeasureInfinitePiTiltedEq μ₀ Y lam` 維持。
  - body: `sorry` + `@residual(plan:cramer-moonshot-plan)`。
  - 注: sibling projection `IsCramerChernoffNLetterRNUnified.chernoffPerTilt` (line 270) は
    suspect 無し、本 sweep で **touch しない** (`h.chernoff` の 1 行 destructure、constructive)。
    structure 自身 (line 245) も touch しない (Phase 2.5 で retract-candidate 化判断)。

- [ ] **2.3.5** `lake build InformationTheory.Shannon.CramerPhaseDGapWorkaround` で olean refresh。
  CramerPhaseDGapWorkaround.lean は terminal file (依存元なし、library leaf)、再 verify は
  当該 file の `lake env lean` のみで足りる。

#### Phase 2.4 — `InformationTheory/Shannon/CramerCLTClosure.lean` 1 件 📋

- [ ] **2.4.1** `cramer_lower_at` (line 464)
  - signature 改変: `h_slice : ∀ ε > 0, ∃ C > 0, ∀ᶠ n ...` を **削除** (P-1)。
  - 残す: `hY_meas` / `h_bdd` / `(a lam, hlam)` / `h_coboundedBelow`。
  - 結論型 `≤ liminf` 維持。
  - body: `sorry` + `@residual(plan:cramer-chernoff-clt-closure-moonshot-plan)`。
  - **重要**: 同 file の `cramer_lower_at_cgfDeriv_unconditional` (line 525) は **touch しない**。
    しかし本 sweep の 2.4.1 で `cramer_lower_at` が sorry 化されると、`cramer_lower_at_cgfDeriv_unconditional`
    の body (line 552 で `exact cramer_lower_at hY_meas h_bdd (deriv (cgf Y μ₀) lam) lam hlam ...`)
    が transitive sorry に降格する。`cramer-chernoff-clt-closure-moonshot-plan.md` の
    DONE-HONEST-HYPS 状態 (constructive 完成) が破壊される可能性 → **撤退ライン L-MIG-3 候補**
    (実発動時の対応は L-MIG-3 参照)。
  - 代替案: `cramer_lower_at` の `h_slice` を hypothesis として残す (= 当該 declaration を本 sweep
    対象外にする) — pilot Hoeffding の Phase 1 (V) と同じ「load-bearing 寄りだが variational
    pass-through として残す」判断を auditor に委ねる。本 plan のデフォルトは「13 件全件 sweep」
    だが、auditor が DEFECT 判定 / L-MIG-3 発動なら本 declaration を **Phase 2.4 から除外**して
    `@audit:suspect` のまま残す (incidental migration を後続 sweep に委ねる)。

- [ ] **2.4.2** `lake build InformationTheory.Shannon.CramerCLTClosure` で olean refresh。
  当該 file 自身を `lake env lean` で再 verify、`cramer_lower_at_cgfDeriv_unconditional` の
  body に transitive sorry が発生しても 0 errors であることを確認 (sorry warning 件数増のみ)。
  CramerCLTClosure.lean は library leaf、それ以上の依存 verify は不要。

#### Phase 2.5 — Predicate / structure 定義側の処理 📋

- [ ] **2.5.1** Phase 2.1 / 2.2 / 2.3 / 2.4 完了後、以下の consumer を `rg` で再確認:
  ```bash
  rg -n 'IsMeasureInfinitePiTiltedEq|IsCramerNLetterRNCylinder|IsCaratheodoryExtensionHyp|IsCramerChernoffNLetterRNUnified' InformationTheory/
  ```
  - hypothesis-form (引数として) consumer が **0 件**になっていれば該当 predicate 定義の
    docstring 末尾に `@audit:retract-candidate(load-bearing-predicate)` を付与 (削除はしない、
    history record として残す)。
  - extract-only consumer / producer 構成子が残っていれば **Pattern E 注記**:
    ```
    @audit:retract-candidate(load-bearing-predicate) — all *hypothesis-form load-bearing*
    consumers were retreated (Phase 2.1–2.4). N extract-only/producer consumers remain:
    <列挙>. Their bodies depend transitively on the upstream `sorry`.
    ```

- [ ] **2.5.2** `IsCramerChernoffNLetterRNUnified` structure (line 245-256) の処理:
  - sibling projection `chernoffPerTilt` (line 270) は constructive `h.chernoff` (1 行 destructure)、
    本 sweep で touch しない。
  - structure 自身は producer (consumer 側は Chernoff family 別 sweep で扱われる可能性あり)。
    本 plan では structure 自身に `@audit:retract-candidate(load-bearing-predicate)` を **付与しない**
    (Chernoff side の `IsBayesErrorPerTiltLowerBound` が同様の load-bearing 性を持ち、両 family
    sweep を経た後で統合判断するため、本 family sweep だけで retract 判断を下さない)。判断ログ
    に記録、未決事項 #1 で escalate。

#### Phase 2.6 — Independent honesty audit (audit-2) 📋

- [ ] **2.6.1** Fresh `general-purpose` agent (or `honesty-auditor`) を起動。brief 必須項目
  (runbook Step 4 準拠):
  - 監査対象 declaration の `(file:line + decl 名 + 削除 hypothesis + 結論型)` 表
    (上記在庫表をそのまま渡す)
  - verbatim verify の指示 (plan / brief を鵜呑みにせず実コード Read、CLAUDE.md
    「具体的数値・型予測の verbatim 確認」)
  - verdict 語彙: `ok / questionable / defect`
  - L-MIG-1〜L-MIG-4 の発動条件 (verdict `defect ≥ 1 件` → L-MIG-2 推奨、`questionable ≥ 5 件`
    → docstring refine batch など)
- [ ] **2.6.2** verdict 回収後、`questionable` は docstring refine、`defect` は当該 declaration
  を撤回 (`@audit:suspect` 形に復元 or sorry 化解除 = signature 復元) + 判断ログに記録。

### Phase V — verify + 計画反映 📋

- [ ] **V.1** 全 6 file (5 file は touch、1 file は CramerCLTClosure で部分 touch) で
  `lake env lean` 確認:
  ```bash
  for f in InformationTheory/Shannon/Cramer.lean \
           InformationTheory/Shannon/CramerLC2PhaseC.lean \
           InformationTheory/Shannon/CramerPhaseDGapWorkaround.lean \
           InformationTheory/Shannon/CramerCLTClosure.lean \
           InformationTheory/Shannon/CramerLC2Discharge.lean \
           InformationTheory/Shannon/CramerLC2DischargeExt.lean; do
    lake env lean "$f"
  done
  ```
  最後の 2 file は touch しないが、上流 sorry の transitive 影響確認のため verify する。

- [ ] **V.2** 集計コマンド実行:
  ```bash
  rg '@audit:suspect' InformationTheory/Shannon/Cramer*.lean | wc -l       # = 0
  rg '@residual\(plan:cramer-moonshot-plan\)' InformationTheory/Shannon/Cramer*.lean | wc -l
  rg '@residual\(plan:cramer-lc2-discharge-moonshot-plan\)' InformationTheory/Shannon/Cramer*.lean | wc -l
  rg '@residual\(plan:cramer-chernoff-clt-closure-moonshot-plan\)' InformationTheory/Shannon/Cramer*.lean | wc -l
  rg -nw 'sorry' InformationTheory/Shannon/Cramer*.lean | wc -l
  rg '@audit:retract-candidate' InformationTheory/Shannon/Cramer*.lean | wc -l
  ```
  期待値: suspect 0、residual 合計 13 (8 + 4 + 1)、sorry 13 (各 residual 1 sorry)、retract-candidate
  0-3 (Phase 2.5 判断次第)。

- [ ] **V.3** 親 plan banner 更新:
  - `cramer-moonshot-plan.md` 冒頭 banner に「sorry-based 移行完了 (sweep date)」追記、
    8 件の `@audit:suspect` → 8 件の `sorry + @residual(plan:cramer-moonshot-plan)` 旨を明示。
  - `cramer-lc2-discharge-moonshot-plan.md` 冒頭 banner に同様の追記 (4 件)。
  - `cramer-chernoff-clt-closure-moonshot-plan.md` 冒頭 banner に「`cramer_lower_at` を
    hypothesis-form sweep に降格 (1 件)、unconditional headline `cramer_lower_at_cgfDeriv_unconditional`
    は constructive 経路維持 (本 sweep 対象外)」旨を追記。
    **ただし L-MIG-3 発動で 2.4.1 を skip した場合は banner 追記不要**。

- [ ] **V.4** Pilot 知見を `.claude/handoff-sorry-migration.md` または後続 family plan 用テンプレ
  に反映:
  - Cramér family は **V/C 候補ゼロ** → Phase 1 skip の事例として記録。
  - 3 つの load-bearing predicate (`IsMeasureInfinitePiTiltedEq` 等) が Mathlib gap (n-letter
    RN-deriv identification of infinite-pi tilt + Carathéodory cylinder extension) を bundling
    している点を、`audit-tags.md`「Wall name register」拡張 PR の候補 (`wall:infinite-pi-tilted-rn`)
    として記録。
  - `CramerCLTClosure.cramer_lower_at_cgfDeriv_unconditional` (constructive headline) の transitive
    sorry 降格は **構成的経路の壊れ** に近く、family sweep の risk として handoff に記載。

## 撤退ライン

- **L-MIG-1 (Legendre-attainment hypothesis `hlam_opt` の auditor 判定が load-bearing でなく precondition)**:
  Phase 2.6 audit で「`hlam_opt` は Legendre 凸性 + `a ≥ 𝔼[X]` で discharge 可能な regularity
  precondition」と判定された場合、P-3 該当 declarations (`cramer_upper_legendre` /
  `cramer_lower_legendre` / `cramer_tendsto` / `cramer_lower_legendre_phaseC_partial_discharge`
  / `cramer_tendsto_phaseC_partial_discharge` / `cramer_tendsto_phase_d_via_cylinder` の 6 件)
  について `hlam_opt` を signature に戻し、residual は P-1/P-2 部分 (`h_tilted_lower` / 各
  predicate) のみに残す。Approach の「P-3 を sorry 化する」判断を撤回。

- **L-MIG-2 (Phase 2.5 で predicate を retract-candidate 化すると依存先 file (Chernoff family
  等) に signature drift が発生)**: `IsCramerChernoffNLetterRNUnified` は Chernoff side の
  `IsBayesErrorPerTiltLowerBound` を含む unified structure のため、本 family sweep だけで
  retract-candidate 判断を下せない (Chernoff family sweep との順序依存)。Phase 2.5 で 3
  predicate (`IsMeasureInfinitePiTiltedEq` / `IsCramerNLetterRNCylinder` / `IsCaratheodoryExtensionHyp`)
  に retract-candidate 化を試み、`rg` で Chernoff family 等の外部 consumer が見つかった場合
  は付与せず、未決事項 #1 で escalate して Phase 2.5 を **保留** (Phase 2.1-2.4 + Phase 2.6
  + Phase V までで close、Phase 2.5 は後続 Chernoff family sweep と統合)。

- **L-MIG-3 (Phase 2.4 で `cramer_lower_at` を sorry 化すると `cramer_lower_at_cgfDeriv_unconditional`
  が transitive sorry に降格、constructive headline 経路が壊れる)**: `cramer-chernoff-clt-closure-moonshot-plan.md`
  DONE-HONEST-HYPS 状態 (residual hypothesis なしの unconditional 化) が現状の唯一の constructive
  Cramér lower bound completion 経路。本 sweep がこれを壊すと **後続の textbook-roadmap T1-C 集計
  にも影響**。auditor が「`cramer_lower_at` の sorry 化は constructive 経路を毀損し、honesty 上の
  純利得が無い」と判定したら、Phase 2.4.1 を **skip** して `cramer_lower_at` の `@audit:suspect`
  を残す (incidental migration を後続 sweep に委ねる)。13 件 → 12 件 sweep に縮小。

- **L-MIG-4 (Approach 変更: pilot scope を縮める)**: Phase 2 全体 (13 件 sorry 化 + 4 predicate
  処理) が 1 セッションで完走しない / Phase 2.6 audit が DEFECT を多発させる場合、`Cramer.lean`
  4 件 + `CramerLC2PhaseC.lean` 4 件 (= 上流 8 件) のみで pilot を close し、`CramerPhaseDGapWorkaround.lean`
  4 件 + `CramerCLTClosure.lean` 1 件は後続 family sweep として別 plan に分離。
  Phase 2.5 (predicate 処理) も延期。

## 未決事項 (auditor 委任可)

1. **`IsMeasureInfinitePiTiltedEq` / `IsCramerNLetterRNCylinder` / `IsCaratheodoryExtensionHyp`
   / `IsCramerChernoffNLetterRNUnified` の deprecate 方針**: Phase 2 で全 hypothesis-form
   consumer が `sorry` 化された場合、(a) `@audit:retract-candidate` 付きで残す / (b) 完全削除する /
   (c) public API として残し続ける、のどれを選ぶか。本 plan のデフォルトは (a) — ただし
   `IsCramerChernoffNLetterRNUnified` は Chernoff family 依存のため Phase 2.5 で保留判断
   (L-MIG-2 参照)。**auditor 判定対象** + user 確認待ち。

2. **Legendre-attainment `hlam_opt` の honesty 判定**: 6 件 (P-3) で `hlam_opt` を hypothesis
   から削除して sorry 化するが、Hoeffding pilot の `IsHoeffdingMinimizerFullSupport` (純
   regularity = `∀ a, 0 < · a`) と同様、`hlam_opt` も「textbook 条件 `a ≥ 𝔼[X]` + 凸性で
   discharge 可能な precondition」と判定される可能性。L-MIG-1 発動の判断は Phase 2.6 auditor
   に委任。**auditor 判定対象**。

3. **`CramerCLTClosure.cramer_lower_at` の sorry 化判断**: `cramer_lower_at_cgfDeriv_unconditional`
   が transitive sorry に降格 → constructive headline 経路の毀損リスク。L-MIG-3 発動の可否は
   auditor 判定 + user 確認。**auditor 判定対象** + 重要な user 確認候補 (DONE-HONEST-HYPS
   banner の解釈変更を伴うため)。

4. **proof done を本 plan で目指さない方針の明示確認**: 本 plan の DoD は **type-check done**
   のみ。Mathlib gap (n-letter RN-deriv identification + Carathéodory extension) の closure は
   **未着手のまま**で本 plan は close する。`cramer-moonshot-plan.md` の Phase C/D 状態は
   変えない (L-C2 撤退状態維持、ただし constructive 経路 `cramer_lower_at_cgfDeriv_unconditional`
   は維持)。user の合意確認のため明示。

5. **Wall register 拡張 PR の検討**: `audit-tags.md`「Wall name register」に
   `wall:infinite-pi-tilted-rn` (n-letter RN-deriv identification of infinite-pi tilt) を追加
   する候補。本 plan では追加せず `plan:` slug で揃えるが、将来の Cramér Phase B/C 完全 closure
   plan を立てる際に wall register 拡張 PR を別途検討する。**user 判断対象** (本 plan の範囲外
   だが、handoff 反映時に明示)。

## 判断ログ

書く頻度: 方針変更 / 撤退ライン発動 / 当初仮定の修正があったとき。append-only。

1. **2026-05-25 Phase 1 skip 確定**: 在庫 13 件は全て pattern P (load-bearing
   hypothesis / predicate consumer)。V (variational pass-through) / C (constructive
   recovery) 該当 declaration ゼロのため Phase 1 は空処理で記録のみ。Phase 2 で 13 件
   全件を sorry 化 (デフォルト sweep、user 承認済)。

2. **2026-05-25 Phase 2.5 `IsCramerChernoffNLetterRNUnified` 保留 (L-MIG-2 対応)**:
   sibling projection `chernoffPerTilt` (本 sweep 対象外) は依然 `h : IsCramerChernoffNLetterRNUnified`
   を hypothesis として取り `h.chernoff` を返す。Cramér side だけで structure 自身に
   `@audit:retract-candidate` 付与すると Chernoff family sweep 時の判定と衝突する
   可能性があるため、本 plan では structure 自身は touch せず、3 predicate
   (`IsMeasureInfinitePiTiltedEq` / `IsCramerNLetterRNCylinder` / `IsCaratheodoryExtensionHyp`)
   のみに retract-candidate 付与。

3. **2026-05-25 InfinitePiTiltedChangeOfMeasure.lean drift incidental fix**: Phase 2.2.5
   で `cramer_lower_phaseC_partial_discharge` の signature 改変により、touch 対象外の
   `InformationTheory/Shannon/InfinitePiTiltedChangeOfMeasure.lean:380 cramer_lower_phaseC_residual_discharge`
   が caller drift で type-check error。Plan は当該 file の再 verify を予期していたが
   修正方法は明示なし。実施: 該当呼び出しから
   `(isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge ...)` 引数を削除する 1 行修正。
   `h_res` が unused に降格 (unused-variable warning 1 件)。本 declaration は
   `@audit:closed-by-successor` 付き (本 sweep 対象外) のため tier 4 legacy 状態のまま
   触らない方針を維持。

4. **2026-05-25 Phase 2.4.1 L-MIG-3 デフォルト sweep 適用**: orchestrator が user 承認済の
   「13 件全件 sweep」を確定。`cramer_lower_at` を sorry 化したことで上流の
   `cramer_lower_at_cgfDeriv_unconditional` (本 sweep の touch 対象外) も signature drift
   (Function expected at ...)。constructive 経路を保ったまま 0 errors を実現するため、
   `cramer_lower_at_cgfDeriv_unconditional` の body を「`cramer_lower_at hY_meas h_bdd
   (deriv (cgf Y μ₀) lam) lam hlam h_coboundedBelow`」の 1 行に縮退 — 旧 body の
   `hmean` + `tiltedHalfLine_chernoff_lower_at_boundary` 経由の constructive 構成は削除
   (transitive sorry に降格)。`hVar` が unused-variable に降格 (unused-variable warning 1 件)。
   signature 上は依然 `unconditional` 名のまま (load-bearing residual hypothesis なし)
   だが、proof done ではなく type-check done で commit (DONE-HONEST-HYPS banner は
   `cramer-chernoff-clt-closure-moonshot-plan.md` 冒頭で更新済)。

5. **2026-05-25 sorry 集計の docstring 散文混入**: `rg -nw 'sorry' InformationTheory/Shannon/Cramer*.lean`
   は **28 hits** を返したが、内訳は実コード `sorry` body **13 件** (期待通り) + docstring
   散文「Transitive `sorry` via ...」「`sorry + @residual(...)` migration」等の説明文 15 件。
   `rg -nw 'sorry'` は word-boundary を取るが backtick で囲まれた docstring 内の `sorry` も
   word として match する。期待値 13 と実測 28 は本質的に乖離していない (実 body 部
   は 13 件、`lake env lean` の "uses sorry" warning 数とも一致)。次 sweep の brief では
   「sorry 集計は警告ベース (`grep -c 'uses .sorry.'`) の方が確実」と note 推奨。

6. **2026-05-25 L-MIG-1 適用 (audit-2 verdict 反映)**: audit-2 で「`hlam_opt` は
   Legendre 凸性 + `a ≥ 𝔼[X]` で textbook discharge 可能な regularity precondition、
   load-bearing でなく `@residual` 不要」と判定されたため、P-3 該当 6 declaration
   (`cramer_upper_legendre` / `cramer_lower_legendre` / `cramer_tendsto` /
   `cramer_lower_legendre_phaseC_partial_discharge` /
   `cramer_tendsto_phaseC_partial_discharge` / `cramer_tendsto_phase_d_via_cylinder`)
   で `hlam_opt` を signature に **戻し**、`@residual(plan:...)` を **削除**。
   `cramer_upper_legendre` は constructive 経路 (`cramer_upper` 経由) で完全
   **proof done** 化、他 5 件は transitive sorry pass-through (上流 `cramer_lower`
   / `cramer_lower_phaseC_partial_discharge` / `cramer_lower_phase_d_via_cylinder`
   の P-1/P-2 sorry に依存)。net residual: 13 → 7 件。
-->

## Round 4 残作業 (2026-05-26 verbatim 再集計)

> **位置付け**: Round 1 (2026-05-25) sweep は上記 Phase 0-V + 判断ログ #1-#6 で
> **完遂済** (`@audit:suspect` 13 → 0、`sorry + @residual(plan:...)` 7 件、
> `@audit:retract-candidate(load-bearing-predicate)` 3 件)。本 Round 4 section は
> **新規 sorry 化作業ではなく**、Round 3 escalate (#2/#4/#5/#7) で挙がった
> 横断改善が Cramér family に該当するかの判定 + 該当する場合の minor 追加処置を計画する。
> handoff-sorry-migration.md L111 の「Cramer (suspect=12 in 3 file): Round 1 で
> 部分着手済、後続予定」は **stale 情報** — 本 Round 4 で archival 状態を確定する。

### Round 1 完了状況 (verbatim 再確認、2026-05-26)

実コード grep 結果 (`rg -c '@audit:suspect\(' InformationTheory/Shannon/Cramer*.lean
InformationTheory/Shannon/MeasurePiTiltedFactorization.lean`):

| file | suspect | residual(plan) | retract-candidate | sorry body |
|---|---:|---:|---:|---:|
| `InformationTheory/Shannon/Cramer.lean` | 0 | 1 | 0 | 1 (`cramer_lower:463`) |
| `InformationTheory/Shannon/CramerCLTClosure.lean` | 0 | 1 | 0 | 1 (`cramer_lower_at:482`) |
| `InformationTheory/Shannon/CramerLC2Discharge.lean` | 0 | 0 | 0 | 0 |
| `InformationTheory/Shannon/CramerLC2DischargeExt.lean` | 0 | 0 | 0 | 0 |
| `InformationTheory/Shannon/CramerLC2PhaseC.lean` | 0 | 3 | 1 | 2 (`tilted_lower_from_predicate:130` + `cramer_lower_phaseC_partial_discharge:165`) |
| `InformationTheory/Shannon/CramerPhaseDGapWorkaround.lean` | 0 | 3 | 2 | 3 (`isMeasureInfinitePiTiltedEq_of_cylinder_density:148` + `cramer_lower_phase_d_via_cylinder:177` + `IsCramerChernoffNLetterRNUnified.cramerPhaseC:319`) |
| `InformationTheory/Shannon/MeasurePiTiltedFactorization.lean` | 0 | 0 | 0 | 0 |
| **合計** | **0** | **8** | **3** | **7** |

(`residual=8` vs `sorry=7` の 1 差は CramerLC2PhaseC.lean:94 の docstring **散文** mention
"sorry'd unconditional producer (`@residual(plan:cramer-moonshot-plan)`)" による false positive
hit、Pattern D 発展形類似。判断ログ #5 の「sorry 集計の docstring 散文混入」と同型。)

判断ログ #6 では「net residual: 13 → 7 件」と書かれており、実 sorry body 数 = 7 と一致。
plan slug 別内訳:

- `@residual(plan:cramer-moonshot-plan)`: 4 件 (Cramer.lean `cramer_lower` + PhaseDGap 3 件
  `isMeasureInfinitePiTiltedEq_of_cylinder_density` / `cramer_lower_phase_d_via_cylinder` /
  `IsCramerChernoffNLetterRNUnified.cramerPhaseC`)
- `@residual(plan:cramer-lc2-discharge-moonshot-plan)`: 2 件 (LC2PhaseC `tilted_lower_from_predicate`
  + `cramer_lower_phaseC_partial_discharge`)
- `@residual(plan:cramer-chernoff-clt-closure-moonshot-plan)`: 1 件 (CLTClosure `cramer_lower_at`)

`@audit:retract-candidate(load-bearing-predicate)` 付与済 (3 件):

- `IsMeasureInfinitePiTiltedEq` (CramerLC2PhaseC.lean:85 docstring + line 116 definition)
- `IsCramerNLetterRNCylinder` (CramerPhaseDGapWorkaround.lean:96 docstring)
- `IsCaratheodoryExtensionHyp` (CramerPhaseDGapWorkaround.lean:123 docstring)

`IsCramerChernoffNLetterRNUnified` structure (PhaseDGapWorkaround.lean:245) は判断ログ #2
通り **未付与** (Chernoff family sweep との順序依存、L-MIG-2)。

`MeasurePiTiltedFactorization.lean` は Round 1 で **touch せず** (Phase A plumbing、tag 0 件、
`namespace InformationTheory.Shannon.Cramer.Discharge`、本 sweep の Approach「3 file 中心」
内には含まれていたが、suspect 0 件で実作業ゼロ)。Round 4 でも touch 不要。

### Round 4 Approach

Round 1 sweep の DoD (type-check done + suspect 0) は達成済。Round 4 は **3 件の minor
横断改善** を行うが、いずれも **任意 (optional)** + **本 plan 単独完結不可** な特性を持つため、
escalate 先 / 判断委任先 / 後続 plan の発火条件を明示し、Cramér family 単独では archival
状態に persist させる。

### Phase R4 — Round 3 escalate 起源の横断改善判定 📋

#### Phase R4.1 — `@audit:retract-candidate(closure-plan-completed)` semantic 検討 📋

- [ ] **R4.1.1** Round 3 escalate #2 (handoff L70-78、BMClosure 起源) で議論中の
  `closure-plan-completed` semantic 拡張が Cramér family にも適用可能か判定する。
  BMClosure の使用例:「active consumer ありの load-bearing wall を closure plan で
  acknowledged 済として bookkeeping」。Cramér 3 predicate (現
  `@audit:retract-candidate(load-bearing-predicate)`) の状態を verbatim 確認:
  - `IsMeasureInfinitePiTiltedEq`: hypothesis-form consumer 0 件、producer-side 構成子
    1 件 (`InfinitePiTiltedChangeOfMeasure.isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge`)
    + Cramér 内 producer 1 件 (`isMeasureInfinitePiTiltedEq_of_cylinder_density`、sorry'd) +
    Cramér 内 projection 1 件 (`IsCramerChernoffNLetterRNUnified.cramerPhaseC`、sorry'd)
  - `IsCramerNLetterRNCylinder`: hypothesis-form consumer 0 件、producer-side
    `IsCramerChernoffNLetterRNUnified.cramer` (structure projection) のみ
  - `IsCaratheodoryExtensionHyp`: hypothesis-form consumer 0 件、producer-side
    `IsCramerChernoffNLetterRNUnified.cara` (structure projection) のみ
  → 3 predicate とも **active consumer なし** (transitively sorry 化されたものを除けば)。
  BMClosure と異なり「active consumer あり」のケースではない → `closure-plan-completed`
  ではなく現状の `load-bearing-predicate` が **正しい reason**。
- [ ] **R4.1.2** R4.1.1 の判定 (Cramér 3 件は `load-bearing-predicate` を維持、
  `closure-plan-completed` への書換不要) を escalate #2 への入力 fact として handoff に
  記録 (本 plan としては action ゼロ、Cramér family 観点での semantic 拡張 demand 無し)。

**Phase R4.1 DoD**: 判断のみ、コード edit ゼロ。escalate #2 の参考資料として整理。

**proof-log**: no。

#### Phase R4.2 — `cramer_lower_at_cgfDeriv_unconditional` honesty downgrade の rewrite recovery 検討 📋

判断ログ #4 で「`cramer_lower_at_cgfDeriv_unconditional` の body を `cramer_lower_at` を
呼ぶ 1 行に縮退、constructive 経路 (boundary CLT + Phase 5 + tiltedHalfLine change-of-measure)
は transitive `sorry` を経由する状態に降格」と記録。Round 3 escalate #5
(`rateDistortionFunction_convexOn_pmf` rewrite recovery) と同パターン。

- [ ] **R4.2.1** 当該 declaration の旧 body (commit 履歴) を verbatim 確認:
  ```bash
  git log --oneline -- InformationTheory/Shannon/CramerCLTClosure.lean | head -10
  git show <pre-sweep-commit>:InformationTheory/Shannon/CramerCLTClosure.lean | sed -n '500,560p'
  ```
  旧 body は `hmean` + `tiltedHalfLine_chernoff_lower_at_boundary` 経由の constructive
  構成 (判断ログ #4 verbatim)。`cramer_lower_at` の `h_slice` を本体内部で **自前構成**
  していた可能性が高い (= L-MIG-3 想定の「downstream genuine proof が upstream load-bearing
  hyp を discharge する」inverted dependency パターン、Round 3 Pattern J)。
- [ ] **R4.2.2** Pattern J recovery 可能性判定:
  - 旧 body が `h_slice` を自前構成していたなら、`cramer_lower_at` を呼ばずに直接
    `cramer_lower` を呼ぶ rewrite で proof done 復元可能 — Round 3 Pattern J 回避策と同型
    (downstream の genuine proof を保持しつつ upstream P retreat を別経路で吸収)
  - ただし `cramer_lower` も sorry 化済 (`cramer_lower:463`) のため、`cramer_lower` 経由
    でも transitive sorry は不可避 — **rewrite recovery 不可** と結論付ける可能性高
  - 旧 body が `tiltedHalfLine_chernoff_lower_at_boundary` を載せていれば、当該 boundary
    lemma が `cramer_lower` の hypothesis form ではなく直接 measure-theoretic に書かれて
    いるかを確認 (CLTClosure.lean:421 周辺を Read)。直接形なら recovery 可能
- [ ] **R4.2.3** R4.2.2 で recovery 可能と判明したら R4.2 を「rewrite による proof done
  復元 plan」として独立 plan 化候補に escalate (本 plan の scope を超える、別 plan)。
  recovery 不可と判明したら docstring に「rewrite recoverable not feasible (`cramer_lower`
  も sorry 化のため transitive 不可避)」note 追記のみ + escalate #5 への入力 fact として
  記録。
- [ ] **R4.2.4** `hVar` unused-variable 警告 (判断ログ #4) を解消するため body を `_` で
  ignore 或いは `:=` を消して `(_hVar : ...)` underscore 化検討 — ただし signature に
  影響あるため、R4.2.2 の rewrite 判定と一括で扱う (R4.2.2 で recovery 不可と確定したら
  underscore 化のみ実施、recovery 可能なら rewrite が unused を解消)。

**Phase R4.2 DoD**: 旧 body verbatim 確認 + rewrite 可能性判定 1 件。実装 (rewrite) は
別 plan に分離。

**proof-log**: no。

#### Phase R4.3 — `wall:infinite-pi-tilted-rn` promote 判定 (escalate #4 類似) 📋

未決事項 #5 (本 plan 内) で「Wall register 拡張 PR の検討」と記載済。Round 3 escalate
#4 (`wall:bm-convex-body-sqrt` promote 待機) と同型の「2+ family 参照」trigger 条件あり。

- [ ] **R4.3.1** 3 predicate の壁性質を verbatim 確認:
  - `IsMeasureInfinitePiTiltedEq`: n-letter RN-deriv identification of infinite-pi tilt
    (Mathlib 未整備、`Measure.infinitePi` + `Measure.tilted` の compositional shape)
  - `IsCramerNLetterRNCylinder`: cylinder density product over n letters
  - `IsCaratheodoryExtensionHyp`: Carathéodory cylinder extension
  → 共通核は **「n 次元 product measure 上の RN-deriv identification + extension」**。
  単一 wall に統合できれば `wall:infinite-pi-tilted-rn` が register 候補。
- [ ] **R4.3.2** promote trigger 条件 (audit-tags.md「提案中 wall」§) の確認:
  - (1) 該当 declaration が shared sorry 補題として 2+ family で再利用される
  - (2) `plan:<slug>` 集約より wall 化のほうが closure 計画と整合する
  - Cramér family 内: 3 predicate consumer すべて Cramér file 内に閉じている (R4.1.1
    で確認済)。**他 family で参照無し** → (1) は **不満足**。
  - ただし Chernoff family の `IsCramerChernoffNLetterRNUnified` structure
    (PhaseDGap:245) が 3 predicate のうち 2 つ (`IsCramerNLetterRNCylinder` + `IsCaratheodoryExtensionHyp`)
    を field として保持 → Chernoff family の closure plan が Cramér wall を参照する
    可能性あり (L-MIG-2 で保留中の `IsCramerChernoffNLetterRNUnified` deprecate 判断と
    連動)。
- [ ] **R4.3.3** 判定: 現時点では promote 見送り、`plan:cramer-moonshot-plan` /
  `plan:cramer-lc2-discharge-moonshot-plan` 集約のまま維持。Chernoff family sweep
  (handoff Next step A の AWGN cluster と独立) 時 + escalate #7 (AWGNMIDecompBody) と
  まとめて再判定。本 plan としては action ゼロ。

**Phase R4.3 DoD**: 判断ログに promote 見送り記録、`audit-tags.md`「提案中 wall」§ への
追記なし (escalate 経由で扱う)。

**proof-log**: no。

### Phase R4 完了の condition

- R4.1 + R4.2 + R4.3 のいずれも **判断のみ + コード edit ゼロ** (本 plan 内 scope では)
- R4.2 で rewrite recovery が可能と判明した場合のみ別 plan 起票が必要 — その場合は
  `docs/shannon/cramer-cltclosure-rewrite-recovery-plan.md` を新規作成 (本 plan には
  scope 外、orchestrator 判断)
- 完了後本 plan は **archival** に移行 — Cramér family の `@audit:suspect` migration は
  Round 1 で完遂、Round 4 は escalate 起源の横断判定のみで close

### Round 4 撤退ライン

- **L-R4-1 (R4.1 で `closure-plan-completed` 必要と判明)**: Cramér 3 predicate のうち
  hypothesis-form consumer 復活 (= 別 sweep で誰かが再導入) があった場合、現
  `load-bearing-predicate` → `closure-plan-completed` 書換が妥当に転じる。本 plan
  R4.1.1 は「現時点で hypothesis-form consumer 0 件」を前提とするため、Phase R4 開始時
  に再 grep で前提崩れ確認 必須。崩れていたら escalate #2 の決定 (3 案 a/b/c) を待ち
  本 plan は R4.1 を skip。
- **L-R4-2 (R4.2 で rewrite recovery が genuine な constructive proof を毀損)**:
  旧 body の boundary CLT + Phase 5 + tiltedHalfLine 経路を rewrite で復元する場合、
  `cramer_lower` の sorry を経由しない別経路を引かないと意味なし。R4.2.2 で「`cramer_lower`
  経由でも transitive sorry 不可避」と判明した時点で R4.2 は実装段階に進めない (escalate
  #5 の rewrite plan に委ねる)、本 plan R4.2 は docstring note 追記のみで close。
- **L-R4-3 (R4.3 で Chernoff family sweep の優先度を逆転させない)**: `wall:infinite-pi-tilted-rn`
  promote には Chernoff family の `IsCramerChernoffNLetterRNUnified` deprecate 判断
  (handoff Next step A) が前提。Chernoff sweep 未着手の状態で Cramér 単独 promote すると
  wall register が drift。本 plan R4.3 は **見送り** を default に置く理由。

### Round 4 未決事項 (auditor 委任 / user 判断)

7. **R4.2 rewrite recovery 別 plan 起票判断**: R4.2.2 で旧 body が `cramer_lower` を
   経由しない構成 (= `tiltedHalfLine_chernoff_lower_at_boundary` 直接形) と判明した
   場合、別 plan `cramer-cltclosure-rewrite-recovery-plan` 起票を user に escalate。
   recovery 不可なら docstring note 追記のみで close。
8. **R4.3 `wall:infinite-pi-tilted-rn` promote 待機の handoff 反映**: 本 plan 内では
   見送りとするが、Chernoff family sweep + escalate #7 (AWGNMIDecompBody) と一括判定
   する旨を `.claude/handoff-sorry-migration.md` Next step A に注記する必要あり (本 plan
   からの handoff 反映 task)。
9. **handoff-sorry-migration.md L111 の stale 修正**: 「Cramer (suspect=12 in 3 file):
   Round 1 で部分着手済、後続予定」を「Cramer (suspect=0, sorry=7 in 4 file): Round 1
   完了、Round 4 minor 横断判定済」に書換える、Round 4 完了後の bookkeeping action。
   handoff edit 権限は orchestrator 側 (本 plan の sub-action ではない)。

## Round 4 判断ログ

書く頻度: Round 4 中の方針変更 / 撤退ライン発動 / 当初仮定の修正があったとき。append-only。

7. **2026-05-26 Round 4 scope 確定**: handoff-sorry-migration.md L111 の stale
   「suspect=12 in 3 file」表記に反し、実コード verbatim 確認で `@audit:suspect` 0 件
   / `sorry + @residual(plan:...)` 7 件 / `@audit:retract-candidate(load-bearing-predicate)`
   3 件 = Round 1 sweep 完遂済と判明。Round 4 は新規 sorry 化なし、Round 3 escalate
   #2/#4/#5 のうち Cramér family に該当する横断改善 3 件 (R4.1 closure-plan-completed
   semantic / R4.2 cltClosure rewrite recovery / R4.3 wall:infinite-pi-tilted-rn
   promote) を判定する scope に確定。本 plan は archival に移行 + handoff stale 修正
   (未決事項 #9) を依頼。


