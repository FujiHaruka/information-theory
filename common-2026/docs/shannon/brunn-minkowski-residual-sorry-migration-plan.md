# Shannon: BrunnMinkowski + WynerZiv residual `@audit:suspect` / `🟢ʰ` → sorry-based migration plan

> **Parent**: [`brunn-minkowski-moonshot-plan.md`](brunn-minkowski-moonshot-plan.md) §残① / pass-through publish 部分
> + sibling [`brunn-minkowski-closure-plan.md`](brunn-minkowski-closure-plan.md) §Phase V — clean (現状 🚧、残 2 件保持)
> + sibling [`brunn-minkowski-sorry-migration-plan.md`](brunn-minkowski-sorry-migration-plan.md) (Round 2、touch 禁止)
> + sibling [`wynerziv-sorry-migration-plan.md`](wynerziv-sorry-migration-plan.md) (Round 1、touch 禁止) /
>   [`wynerziv-phase2-predicate-removal-plan.md`](wynerziv-phase2-predicate-removal-plan.md) (Round 2 Wave 2、touch 禁止)
> 関連 [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md) /
> [`audit/audit-tags.md`](../audit/audit-tags.md)。
>
> 本 plan は **proof completion ではなく Round 2 後の `@audit:suspect` / 散文 `🟢ʰ`
> 残置の最終 sweep** (`audit-tags.md`「Deprecated」+ 「移行レシピ」+
> closure plan §Phase V — clean の正式 close) を目的とする独立 workstream。
> proof done は本 plan の出力にしない (= `brunn-minkowski-closure-plan.md`
> Phase 1-4 で達成済 genuine chain を変えない + entropy 形 BM full closure は
> 別 workstream)。

## Context

### なぜ Round 3 (residual) なのか — Round 2 完了状態と意図的 scope-out

Round 2 (`brunn-minkowski-sorry-migration-plan.md` Phase 2 + 3、commits
`419be86` + `8c31ff6`) は **`BrunnMinkowskiClosure.lean` の 2 件**
(`brunn_minkowski_volume_indicator` L373 + `brunn_minkowski_entropy_jointPi` L494)
を **意図的に scope 外** とした (Round 2 plan 在庫表 #30 + #32、L. 247/249
verbatim):

```
| 30 | BrunnMinkowskiClosure.lean:373 | brunn_minkowski_volume_indicator |
     | @audit:suspect(brunn-minkowski-closure-plan) | V (closure plan §F 段階着地点) |
     | 本 sweep では touch しない (closure plan 完了済の genuine 着地点)
     | — タグは @audit:retract-candidate(closure-plan-completed) 化を
     | Phase 2 で auditor 委任 |
| 32 | BrunnMinkowskiClosure.lean:493 | brunn_minkowski_entropy_jointPi |
     | 散文 🟢ʰ load-bearing — NOT a discharge + @audit:suspect(brunn-minkowski-closure-plan) |
     | closure plan Phase 3 pivot で 4 honest hyp 縮約済
     | (hA_unif/hB_unif/hAB_unif + IsBMEntropyPowerVolumeHyp) |
     | 本 sweep では touch しない (closure plan が wall:bm-convex-body-sqrt 化検討中)
     | — タグは @audit:retract-candidate(closure-plan-completed) 化を
     | Phase 2 で auditor 委任 |
```

scope-out 理由 (Round 2 L-MIG-3 撤退ライン)**:
- 両 declaration は `brunn-minkowski-closure-plan.md` の Phase 1 段階着地点
  (L372) + Phase 3 pivot 着地点 (L493) として **genuine chain で publish 済**。
  本 sweep で sorry 化すると closure plan の genuine chain が逆行する。
- `closure plan Phase V — clean (🚧)` で本 2 件を保持中 — 本 residual plan は
  **closure plan Phase V の formal 形式化 = honesty tag 整理のみ** として独立
  workstream 化する。

`WynerZiv.lean` は Round 1 (`wynerziv-sorry-migration-plan.md` Phase 1、commit
`36633fe`) で `@audit:suspect` を **完全削除済** (verbatim 確認: 実 declaration
への tag 0 件、grep ヒット 2 件は両方 docstring 内 `「Phase 1 (sorry-migration):
the \`@audit:suspect\` tag was removed — ...」` という migration done note の
文字列リテラル)。本 plan で **touch しない**。

`BrunnMinkowskiFunctional.lean` は Round 2 (commit `419be86` + `8c31ff6`) で
**suspect 0 / staged 0 / 🟢ʰ 0** の状態に既に達している (実 declaration への
tag 0 件、grep ヒット 4 件は docstring 内 `「旧 \`@audit:suspect\` で legacy
計数」` という migration done note の文字列リテラル)。本 plan で **touch しない**。

### 実残置の verbatim 確認 (2026-05-26、本 session orchestrator 計測差分)

orchestrator brief で「BrunnMinkowskiFunctional 4 suspect / BrunnMinkowskiClosure
2 suspect + 1 🟢ʰ / WynerZiv 2 suspect」と通告されていたが、`rg -n` で実行コード
を verbatim 確認した結果:

| file | grep `@audit:suspect` hit 数 | 実 declaration への tag | docstring 内文字列 (migration done note) | 真の残置? |
|---|---:|---:|---:|---|
| `BrunnMinkowskiFunctional.lean` | 4 | **0** | 4 | ❌ Round 2 で sweep 完了済、本 plan scope 外 |
| `BrunnMinkowskiClosure.lean` | 2 | **2** (L372 + L493) | 0 | ✅ 真の残置 (closure plan §F + §G 段階着地点) |
| `WynerZiv.lean` | 2 | **0** | 2 | ❌ Round 1 で sweep 完了済、本 plan scope 外 |

| file | grep `🟢ʰ` hit 数 | 実 docstring 内 load-bearing 散文 | 真の残置? |
|---|---:|---:|---|
| `BrunnMinkowskiClosure.lean` | 1 | **1** (L476、`brunn_minkowski_entropy_jointPi` の docstring 内) | ✅ 真の残置 (上記 L493 declaration の docstring に同居) |
| `WynerZiv.lean` | 0 | 0 | ❌ なし |
| `BrunnMinkowskiFunctional.lean` | 0 | 0 | ❌ なし |

**実 sweep 対象 = BrunnMinkowskiClosure.lean の 2 declaration (L372 + L493) のみ**、
うち L493 は docstring 内 🟢ʰ 散文 (L476) を同居 = 同 declaration の処理で同時に
1 件解消。

### Pattern D (sorry 計数 docstring 文字列誤計数) 適用例

本件は runbook 「**Pattern D — `sorry` 件数の docstring 文字列誤計数**」の
発展形であり、`rg @audit:suspect` でも同種誤計数が発生することを実観測。次の
sweep からは inventory step で **declaration 直接タグ** と **docstring 内
literal mention** を区別するための grep pattern を runbook に追記候補
(本 plan §「audit-tags.md 拡張提案」参照)。

具体的回避策:

```bash
# declaration 直接タグ のみ (`\`` literal を除外):
rg -n '@audit:suspect\(' InformationTheory/Shannon/<file>.lean \
  | rg -v 'tag was removed|legacy 計数|旧 `'
```

または (より厳密に):

```bash
# 直前行が `-/` (docstring 終了) ではない `@audit:suspect(` (= declaration
# 注釈中):
awk '/@audit:suspect\(/ {prev_close = (prev ~ /-\/$/); print FILENAME":"NR":"$0, "(prev_close="prev_close")"} {prev=$0}' \
  InformationTheory/Shannon/<file>.lean
```

### 親 moonshot との関係

`brunn-minkowski-moonshot-plan.md` は **hypothesis pass-through publish 済**
(`brunn_minkowski_entropy_inequality` は L-BM1 結論を `:= h_bm` で着地、抽象
`h` 引数)。本 residual plan は親 moonshot の signature を変更しない:

- 残 2 件は `brunn-minkowski-closure-plan.md` で publish 済の genuine chain
  着地点 (L372 体積版 + L493 entropy 形 `jointDifferentialEntropyPi` 特化)。
- 本 plan は **tag migration のみ** で signature / body は変えない。
- `@audit:retract-candidate(closure-plan-completed)` を付与する選択肢は Round 2
  plan が既に明示 (在庫表 #30/#32) — 本 plan の主 recipe として採用。

### closure plan Phase V との関係

`brunn-minkowski-closure-plan.md` §「Phase V — clean ✅ (2026-05-25 wave 3-4
verify + 棚卸し)」は実態は **🚧 (進捗 L16: `@audit:suspect` 残 2 件)** であり、
本 residual plan は **closure plan §Phase V の独立 close** として位置付ける。
完了時に closure plan §Phase V を ✅ にする banner 更新を伴う (本 plan Phase V
の出力)。

### Honesty workflow と DoD

本 plan の DoD は `CLAUDE.md`「Definition of Done — 2 段階」の **type-check done**:

- `lake env lean InformationTheory/Shannon/BrunnMinkowskiClosure.lean` が 0 errors、
- 各 declaration の docstring 内 `@audit:suspect(brunn-minkowski-closure-plan)`
  tag を **削除** + `@audit:retract-candidate(closure-plan-completed)` に置換
  (Phase 2 で auditor 委任の判断結果)、
- 🟢ʰ 散文は **削除** (上記 retract-candidate で代替)、
- Phase 完了時に `honesty-auditor` を起動して classification + signature
  honesty を独立 verify。

`@audit:ok` (proof done) は **本 plan の出力にしない** — entropy 形 BM の
完全 closure (凸体 Brunn-Minkowski の Mathlib 不在解消、`wall:bm-convex-body-sqrt`
discharge) は本 plan scope 外。

### Tier 5 defect (inline detection、planner 段階)

`rg '⚠|HONESTY ALERT|FALSE'` を対象 file に実行 → **0 hit** (Pattern H 該当
なし)。

新規 tier 5 defect の発見も planner 段階で **0 件**:

- `brunn_minkowski_volume_indicator` (L373): body は
  `rw [integral_indicator_one_eq_volume A hA, ...]; exact h_pl` — `h_pl` は
  「`(∫ 1_A)^λ * (∫ 1_B)^(1-λ) ≤ ∫ 1_{λA+(1-λ)B}` という n-dim PL の indicator
  特殊化結論を直接 hypothesis として受領」する形式。これは **load-bearing**
  だが circular `:= h_pl` 単独ではなく、3 つの genuine `rw` 経由で書き換えた
  後の `exact` であり、本体 indicator → volume 変換 (genuine
  `integral_indicator_one_eq_volume`) を消費する **段階着地点**。tier 5 ではなく
  tier 4 寄り (= closure plan の意図的着地点)。
- `brunn_minkowski_entropy_jointPi` (L494): body は entropy power ↔
  `vol^(2/n)` の `rw` 4 件 + `bm_volume_sqrt_to_entropyPower` の genuine 適用。
  `h_geom_bm_assumed : IsBMEntropyPowerVolumeHyp` は **load-bearing** だが
  closure plan で「唯一外出しする geometric content」として acknowledged
  済の honest hyp (`@audit:retract-candidate` 候補ではなく `wall:bm-convex-body-sqrt`
  化の R4 候補 + Phase 2.3 で予防的 deprecation 注記済)。これも tier 5 では
  なく tier 4 寄り。

両 declaration は **genuine chain の着地点として acknowledged 済の load-bearing
形態**であり、本 plan で sorry 化する対象ではない。本 plan の目的は **tag
vocabulary を migration done state に揃える** こと (= retract-candidate 化 +
🟢ʰ 散文削除) のみ。

## Approach

### 全体戦略

**file 単位 sweep を 2 sub-family に分割**、本実 sweep は BM closure のみ
(WynerZiv は scope-out 確認のみ)、共有 wall lemma 集約は **しない** (本 plan
は新規 sorry を作らない):

```
Phase 0   Inventory (本 plan 内 inline、完了済)
   │
Phase 1   WynerZiv scope-out 確認 (sweep 対象なし)
   │      └─ verbatim 確認のみ、touch しない
   │
Phase 1.4 audit-1 (Phase 1 verbatim 確認の独立検証、optional)
   │
Phase 2.BM.1  BrunnMinkowskiClosure.lean L372 (brunn_minkowski_volume_indicator)
   │      └─ @audit:suspect → @audit:retract-candidate(closure-plan-completed)
   │
Phase 2.BM.2  BrunnMinkowskiClosure.lean L493 (brunn_minkowski_entropy_jointPi)
   │      └─ @audit:suspect 削除 + 🟢ʰ 散文 削除 →
   │         @audit:retract-candidate(closure-plan-completed) 統一
   │
Phase 2.X     retract — 関連 predicate の docstring 整合
   │      └─ IsBMEntropyPowerVolumeHyp (L441) docstring に
   │         「closure plan Phase V close 済、wall:bm-convex-body-sqrt
   │         化候補 (別 PR)」を追記
   │
Phase 2.audit honesty-auditor 起動 (BM 残 2 件 + Phase 2.X 整合確認)
   │
Phase V    verify + closure plan §Phase V banner 更新 + moonshot banner 更新
```

### Phase 順序の理由

- **WynerZiv scope-out 確認を最初 (Phase 1)**: 万が一 Round 1 sweep に漏れがあった
  場合の早期検出。実態は migration done note の docstring 文字列のみと既に
  verbatim 確認済だが、本 plan の DoD 担保のため audit-1 で独立検証を併走可能。
- **BM 2 件は file 内 line 順に処理 (Phase 2.BM.1 → 2.BM.2)**: 両 declaration
  は同 file 内 closure 経路で **L372 → L493 の dependency 順** (L548 で
  `brunn_minkowski_entropy_inequality_genuine` が L493 を呼び出す chain、 L656
  で `bm_scaledMul_to_sqrt` chain の中で L372 を間接消費)。tag 移行のみで
  signature / body は変えないため依存方向は本 plan の挙動に影響しないが、
  読解の自然順として line 順を採用。
- **Phase 2.X (predicate 注記) を最後**: `IsBMEntropyPowerVolumeHyp` (L441) は
  Round 2 plan で **「`wall:bm-convex-body-sqrt` 化候補だが R4 拡張で別 PR」**
  と明示済 (Round 2 plan §「Wall name register 拡張提案 (R4)」#2)。本 plan は
  R4 を **採用せず**、docstring 注記更新のみで closure plan Phase V の close
  ポインタを提供する (R4 採用は本 plan scope 外、別 PR 候補)。

### 共有 wall lemma 集約の要否

**集約しない**。本 plan は新規 `sorry` を作らず、既存 `@audit:suspect` 2 件を
`@audit:retract-candidate(closure-plan-completed)` に置換するのみ (`@residual`
タグも新規付与しない)。`docs/audit/audit-tags.md`「Wall name register」拡張も
本 plan の commit に同梱しない。

**R4 候補 (本 plan で採用しない、別 PR 候補として記録)**:

1. **`wall:bm-convex-body-sqrt`** — Cover-Thomas sqrt 形
   `volAB^(1/n) ≥ volA^(1/n) + volB^(1/n)`。Mathlib 不在。closure plan §G で
   `IsBMEntropyPowerVolumeHyp` honest hyp として外出し済、§H で
   `IsBMScaledMulHyp` (より primitive) から `bm_scaledMul_to_sqrt` で genuine
   縮約済。完全 discharge は **凸体 Brunn-Minkowski の Mathlib 不在** で塞がる。
   - 該当 declaration: `BrunnMinkowskiClosure.lean:441 IsBMEntropyPowerVolumeHyp`
     (def) + `:594 bm_scaledMul_to_sqrt` (consumer)
   - 該当 plan: 後続の `brunn-minkowski-from-epi-discharge-plan.md` (EPI route、
     現状未着手) または `prekopa-leindler-induction-plan.md` (n-dim PL route)。

本 R4 提案は本 plan の commit には同梱せず、Phase 2.X で docstring に
「wall 化候補、別 PR」と記録するのみ。

### Pattern A-H 適合チェック (CLAUDE.md runbook §「失敗パターン」逐一確認)

| Pattern | 該当性 | 対処 |
|---|---|---|
| **A** (stale olean で type error 見逃し) | △ 弱該当 — 本 plan は signature / body 改変なし、docstring 編集のみ | Phase V で `lake env lean InformationTheory/Shannon/BrunnMinkowskiClosure.lean` 0 errors 確認のみで十分 (olean refresh 不要) |
| **B** (planner 全件 sorry 指示の overcorrect) | ✗ 不該当 — 本 plan は新規 sorry を作らない | (回避不要) |
| **C** (transitive sorry の tag 誤付与) | ✗ 不該当 — 本 plan で sorry を作らない、transitive も発生しない | (回避不要) |
| **D** (`sorry` 計数 docstring 文字列誤計数) | ✅ **強い該当 — 本 plan の起草段階で発覚** | inventory step で `rg @audit:suspect\(` 直接タグ patternを使用 (本 §Context 参照)、declaration 行と docstring 内文字列を区別。発展形として runbook 拡張提案 (本 plan §「audit-tags.md 拡張提案」) |
| **E** (predicate retract-candidate の extract-only consumer 見落とし) | △ 弱該当 — `IsBMEntropyPowerVolumeHyp` (L441) は file 内 consumer のみ | Phase 2.X で docstring に「file 内 consumer のみ、cross-family なし」を verbatim 確認 + 注記 |
| **F** (tier 5 defect の suspect 計数見落とし) | ✗ 不該当 — planner 段階で実コード Read で確認、両 declaration は genuine chain 着地点 (tier 5 ではなく tier 4 寄り) | (回避済) |
| **G** (cross-family unified predicate の単独 deprecate 不可) | ✗ 不該当 — `rg brunn_minkowski_volume_indicator\|brunn_minkowski_entropy_jointPi` で同 file 内のみ (S1 散文 reference でもなし)。`IsBMEntropyPowerVolumeHyp` も同 file 内 closed | (回避済) |
| **H** (既存 HONESTY ALERT / FALSE predicate の重畳) | ✗ 不該当 — `rg '⚠\|HONESTY ALERT\|FALSE'` 0 hit | (回避済) |

### Cross-family 検出 (S1/S2/S3 判定、runbook 3 段階)

| declaration | cross-family stage | 根拠 |
|---|---|---|
| `BrunnMinkowskiClosure.lean:372 brunn_minkowski_volume_indicator` | **なし (in-family closed)** | `rg brunn_minkowski_volume_indicator InformationTheory/` で同 file 内のみ (`:373 theorem` 定義 + `:656/:825/:852/:856 in-file caller` のみ)、cross-family consumer 0 件 |
| `BrunnMinkowskiClosure.lean:493 brunn_minkowski_entropy_jointPi` | **なし (in-family closed)** | `rg brunn_minkowski_entropy_jointPi InformationTheory/` で同 file 内のみ (`:494 theorem` 定義 + `:548/:711 caller` のみ)、cross-family consumer 0 件 |
| `BrunnMinkowskiClosure.lean:441 IsBMEntropyPowerVolumeHyp` (Phase 2.X 注記対象) | **なし (in-family closed)** | `rg IsBMEntropyPowerVolumeHyp InformationTheory/` で同 file 内のみ、cross-family consumer 0 件 |

S3 = なし → 単独 sweep で完結可能、escalate 不要。S1 散文 reference も
`BrunnMinkowski.lean:196` (`BrunnMinkowskiClosure.lean の brunn_minkowski_entropy_jointPi`)
の docstring mention 1 件のみ (import 経由の実依存ではなく散文言及)、本 plan
の declaration 自体に touch しないため drift 発生せず。

## 在庫: 残 2 declaration + 1 散文 verbatim 分類

verbatim 確認方法: `InformationTheory/Shannon/BrunnMinkowskiClosure.lean` を Read で
直接タグ + 直後 `theorem` signature + body 1-3 行を実コードから読込み。

### sub-family BM — BrunnMinkowskiClosure.lean (2 declaration + 1 同居 🟢ʰ 散文)

| # | file:line | decl 名 | 現タグ (verbatim) | パターン | 結論型 (verbatim 1 行) | 提案 tag 置換 | cross-family? |
|---|---|---|---|---|---|---|---|
| 1 | `BrunnMinkowskiClosure.lean:372` | `brunn_minkowski_volume_indicator` | `@audit:suspect(brunn-minkowski-closure-plan)` (docstring 末尾 L372) | V (closure plan §F 段階着地点、`h_pl : ... ≤ ...` n 次元 PL 結論を indicator 特殊化で直接 hypothesis 受領) | `(volume A).toReal ^ lam * (volume B).toReal ^ (1 - lam) ≤ (volume (lam • A + (1 - lam) • B)).toReal` | `@audit:suspect(brunn-minkowski-closure-plan)` を **削除** + `@audit:retract-candidate(closure-plan-completed)` 追加 (`brunn-minkowski-closure-plan` Phase 1 段階着地点 = genuine chain 着地済 = 単独 deprecate 不可、wall 化候補は別 PR) | なし |
| 2 | `BrunnMinkowskiClosure.lean:493` | `brunn_minkowski_entropy_jointPi` | `@audit:suspect(brunn-minkowski-closure-plan)` (docstring 末尾 L493) + docstring 内 散文 `🟢ʰ load-bearing hypothesis — NOT a discharge` (L476) | V (closure plan §G Phase 3 pivot 着地点、4 honest hyp 縮約済: `hA_unif/hB_unif/hAB_unif` + `IsBMEntropyPowerVolumeHyp`) | `entropyPower_nDim n InformationTheory.Shannon.jointDifferentialEntropyPi (P.map (fun ω => X ω + Y ω)) ≥ entropyPower_nDim n ... (P.map X) + entropyPower_nDim n ... (P.map Y)` | `@audit:suspect(brunn-minkowski-closure-plan)` を **削除** + 🟢ʰ 散文 (L476) を **削除** + `@audit:retract-candidate(closure-plan-completed)` 統一 (closure plan §G 縮約着地済、load-bearing 部分は `IsBMEntropyPowerVolumeHyp` honest hyp に集約済) | なし |

### sub-family BM 補助 — `IsBMEntropyPowerVolumeHyp` (predicate def)

| # | file:line | def 名 | 現タグ | Phase 2.X 後の docstring 追記 | cross-family? |
|---|---|---|---|---|---|
| 3 | `BrunnMinkowskiClosure.lean:441` | `def IsBMEntropyPowerVolumeHyp` | (タグなし、honest hyp として acknowledged) | 「closure plan Phase V close 済 (`brunn-minkowski-residual-sorry-migration-plan` 経由)。`wall:bm-convex-body-sqrt` 化候補 (Round 2 plan §R4 #2、本 plan では採用せず別 PR)」を docstring 末尾に追記 | なし |

### sub-family WynerZiv — scope-out 確認のみ (sweep 対象 0 件)

| # | file:line | 観察 | 結論 |
|---|---|---|---|
| 4 | `WynerZiv.lean:328` | docstring 内 `「Phase 1 (sorry-migration): the \`@audit:suspect\` tag was removed — the body is already purely constructive」` 文字列 | Round 1 で sweep 完了済の migration done note。**本 plan で touch しない** |
| 5 | `WynerZiv.lean:363` | docstring 内 `「Phase 1 (sorry-migration): the \`@audit:suspect\` tag was removed — the body \`le_antisymm h_conv h_ach\` is a pure variational ≤ ∧ ≥ → = composition」` 文字列 | 同上、Round 1 完了済の migration done note。**本 plan で touch しない** |

### 集計 (パターン別)

- **tag migration 対象 (BMClosure)**: **2 件** + 同居 🟢ʰ 散文 1 件 = 実 tag
  操作 3 箇所、ただし同 declaration 内に統合される)
- **predicate docstring 注記更新 (Phase 2.X)**: **1 件** (`IsBMEntropyPowerVolumeHyp`)
- **scope-out 確認のみ (WynerZiv)**: **2 件 (docstring 文字列、本 plan で
  touch しない)**
- **scope-out 確認のみ (BrunnMinkowskiFunctional)**: **4 件 (docstring 文字列、
  本 plan で touch しない、Round 2 で sweep 完了済)**

総計 9 件の grep ヒットのうち **真の sweep 対象 = BMClosure 3 件 (2 declaration
+ 1 同居 🟢ʰ)** + **Phase 2.X 注記 1 件 = 計 4 箇所のみ**、残り 6 件は
docstring 内 migration done note の文字列リテラル (Pattern D 発展形)。

## Phase 詳細

### Phase 0 — Inventory (本 plan 内 inline、完了) 📋 ✅

- [x] BrunnMinkowskiClosure.lean / BrunnMinkowskiFunctional.lean / WynerZiv.lean
  の 3 file を Read で verbatim 確認 (`@audit:suspect` 直接タグ + 🟢ʰ 散文 +
  docstring 内文字列リテラルの区別)。
- [x] Round 2 BM commit (`419be86` + `8c31ff6`) + Round 1 WynerZiv commit
  (`36633fe`) を `git log --oneline` + `git show --stat` で確認、scope-out
  declaration を特定。
- [x] cross-family 検出 (`rg brunn_minkowski_volume_indicator|brunn_minkowski_entropy_jointPi|IsBMEntropyPowerVolumeHyp InformationTheory/`)
  → in-family closed、S3 該当 0 件、escalate 不要。
- [x] `rg '⚠|HONESTY ALERT|FALSE'` で Pattern H 検出 → 0 hit。
- [x] tier 5 defect 新規検出 0 件 (planner 段階)、本 plan は新規 sorry なし。

**proof-log**: no (mechanical 在庫確認、interesting なし)。

### Phase 1 — WynerZiv scope-out 確認 (sweep 対象なし) 📋

- [ ] **1.1** `WynerZiv.lean` の grep `@audit:suspect` 2 ヒットを **verbatim
  確認**:
  ```bash
  rg -n '@audit:suspect' InformationTheory/Shannon/WynerZiv.lean
  ```
  期待出力: 2 件とも docstring 内文字列 (L328 + L363) — 真の declaration
  注釈タグ 0 件。
- [ ] **1.2** **本 plan では touch しない** ことを判断ログ #1 に記録。Round 1
  `wynerziv-sorry-migration-plan.md` Phase 1 で既に sweep 完了済 (commit
  `36633fe`)、本 plan の scope 外。
- [ ] **1.3** Phase 1 完了時 `lake env lean InformationTheory/Shannon/WynerZiv.lean`
  で 0 errors を保持していることを確認 (touch していないので変化なし、念のため
  の sanity check)。

**Phase 1 DoD**: `WynerZiv.lean` 未編集、`lake env lean` 0 errors 維持、判断ログ
#1 に scope-out 確認記録。

**proof-log**: no (scope-out 確認のみ)。

### Phase 1.4 — audit-1 (Phase 1 verbatim 確認の独立検証、optional) 📋

- [ ] **1.4.1** orchestrator が optional に `honesty-auditor` (or `general-purpose`
  + brief で SoT 指定) を起動。対象: WynerZiv.lean L328 + L363 が真に migration
  done note の docstring 文字列であり、隠れた直接タグが存在しないこと。
- [ ] **1.4.2** verdict 受領:
  - **ok** → Phase 2.BM.1 着手
  - **questionable** → docstring refine (Phase 1 では skip 可、本 plan 完了
    後の handoff として記録)
  - **defect** (隠れタグ検出) → Phase 1 を本 sweep 対象として復活させる
    (auditor 報告に従って sweep recipe を本 plan に追加)

本 audit-1 は **本 plan 起草段階の verbatim 確認** を独立検証する保険として
optional。orchestrator が起草時の確認に信頼を置く場合は skip 可能 (Phase 2.audit
で全体 audit を実施するため)。

**proof-log**: no (audit verdict 受領のみ、本 plan の Phase 2.audit に統合可能)。

### Phase 2.BM.1 — `brunn_minkowski_volume_indicator` (L372) tag migration 📋

`proof-log: no` (mechanical tag 置換、signature / body 改変なし)。

- [ ] **2.BM.1.1** `BrunnMinkowskiClosure.lean:372` docstring 末尾の
  `@audit:suspect(brunn-minkowski-closure-plan)` 行を **削除**。
- [ ] **2.BM.1.2** 同 docstring 末尾に
  `@audit:retract-candidate(closure-plan-completed)` を追加。
  Rationale: `brunn-minkowski-closure-plan.md` §Phase 1 段階着地点 (entry §F
  L360-385) として genuine chain (`integral_indicator_one_eq_volume` 経由) で
  publish 済の load-bearing 着地点。本 declaration の `h_pl` hypothesis は
  closure plan の意図通り「n 次元 PL 結論を indicator 特殊化に直渡し」する
  honest hyp = 単独 deprecate 不可。本 plan で **削除しない**、retract-candidate
  注記のみで genuine chain 着地済を明示。
- [ ] **2.BM.1.3** docstring 内に **追加散文** で次を明示 (`audit-tags.md`
  「移行レシピ」散文サンプル踏襲):
  ```
  Phase V tag migration (residual sorry-migration plan、2026-05-26): legacy
  `@audit:suspect(brunn-minkowski-closure-plan)` → `@audit:retract-candidate(
  closure-plan-completed)`. closure plan §F 段階着地点 (entry §F L360-385) として
  genuine chain で publish 済、`h_pl` honest hyp は closure plan の意図通りの
  load-bearing 着地形態。declaration 自体は維持。
  ```
- [ ] **2.BM.1.4** `lake env lean InformationTheory/Shannon/BrunnMinkowskiClosure.lean`
  で 0 errors 確認 (docstring 編集のみのため type-check 影響なし、念のため
  確認)。

**Phase 2.BM.1 DoD**:
- L372 `brunn_minkowski_volume_indicator` の docstring から `@audit:suspect`
  0 件、`@audit:retract-candidate(closure-plan-completed)` 1 件。
- `lake env lean` 0 errors。

### Phase 2.BM.2 — `brunn_minkowski_entropy_jointPi` (L493) tag migration + 🟢ʰ 散文削除 📋

`proof-log: no` (mechanical tag 置換 + 散文削除、signature / body 改変なし)。

- [ ] **2.BM.2.1** `BrunnMinkowskiClosure.lean:476` の docstring 内 散文
  `🟢ʰ load-bearing hypothesis — NOT a discharge. 本定理の load-bearing 部分は
  ...` (L476-481 の 6 行) を **削除**。
  - 削除理由: 散文 `🟢ʰ` は tier 4 deprecated 表記 (audit-tags.md「Deprecated」表)。
  - 同等の意味論的説明は `@audit:retract-candidate` の reason variant で代替可能。
- [ ] **2.BM.2.2** 削除した 6 行の意味論的内容を **保持** するため、docstring
  内に **再表現** された散文を追記 (Round 1 WynerZiv plan の 🟢ʰ refine 手順
  踏襲):
  ```
  Closure plan §G Phase 3 pivot 着地点: 4 honest hyp に縮約済
  (`hA_unif/hB_unif/hAB_unif` = uniform=log-vol regularity 3 本 +
  `IsBMEntropyPowerVolumeHyp` = Cover-Thomas sqrt 形 geometric 不等式 1 本)。
  load-bearing 部分は `IsBMEntropyPowerVolumeHyp` 1 本に集約済 (Mathlib に凸体
  Brunn-Minkowski sqrt 形が存在しないため honest hyp として外出し、`wall:bm-convex-body-sqrt`
  化候補は Round 2 plan §R4 #2 で記録、本 plan では採用せず別 PR)。entropy
  power ↔ `vol^(2/n)` の代数 (`entropyPower_nDim_eq_exp` / `Real.rpow_def_of_pos`)
  と sqrt → entropy-power 加法形持ち上げ (`bm_volume_sqrt_to_entropyPower`) は
  すべて genuine。
  ```
  (= tier 4 散文 `🟢ʰ` 言及を完全削除しつつ、closure plan §G の意味論的
  content を維持。)
- [ ] **2.BM.2.3** docstring 末尾の
  `@audit:suspect(brunn-minkowski-closure-plan)` 行を **削除**、
  `@audit:retract-candidate(closure-plan-completed)` に置換。
- [ ] **2.BM.2.4** docstring 末尾に追加散文 (Phase 2.BM.1.3 と同様の Phase V
  tag migration note):
  ```
  Phase V tag migration (residual sorry-migration plan、2026-05-26): legacy
  `@audit:suspect(brunn-minkowski-closure-plan)` + 散文 `🟢ʰ load-bearing` →
  `@audit:retract-candidate(closure-plan-completed)` に統一。closure plan §G
  Phase 3 pivot で 4 honest hyp 縮約済の load-bearing 着地形態。declaration
  自体は維持。
  ```
- [ ] **2.BM.2.5** `lake env lean InformationTheory/Shannon/BrunnMinkowskiClosure.lean`
  で 0 errors 確認。

**Phase 2.BM.2 DoD**:
- L493 `brunn_minkowski_entropy_jointPi` の docstring から `@audit:suspect`
  0 件、🟢ʰ 散文 0 件、`@audit:retract-candidate(closure-plan-completed)` 1 件。
- `lake env lean` 0 errors。

### Phase 2.X — `IsBMEntropyPowerVolumeHyp` (L441) docstring 注記更新 📋

`proof-log: no` (mechanical docstring 編集)。

- [ ] **2.X.1** `BrunnMinkowskiClosure.lean:441` の `def IsBMEntropyPowerVolumeHyp`
  docstring 末尾に次を追記:
  ```
  Phase V residual sorry-migration plan close 済 (`brunn-minkowski-residual-sorry-migration-plan`、
  2026-05-26): file 内 consumer (`bm_volume_sqrt_to_entropyPower` L451 +
  `brunn_minkowski_entropy_jointPi` L493 + `brunn_minkowski_entropy_inequality_genuine`
  L532 + downstream chain) のみ、cross-family consumer なし (`rg
  IsBMEntropyPowerVolumeHyp InformationTheory/` で in-file 11 hit 全件 file 内)。
  `wall:bm-convex-body-sqrt` 化候補 (Round 2 plan §R4 #2、`audit-tags.md`
  「Wall name register」拡張) は本 plan では採用せず、別 PR / 後続 plan
  (`brunn-minkowski-from-epi-discharge-plan` EPI route or `prekopa-leindler-induction-plan`
  n-dim PL route) に委ねる。
  ```
- [ ] **2.X.2** `lake env lean InformationTheory/Shannon/BrunnMinkowskiClosure.lean`
  で 0 errors 確認。

**Phase 2.X DoD**:
- L441 `IsBMEntropyPowerVolumeHyp` docstring に Phase V close 済注記が追加済。
- `lake env lean` 0 errors。

### Phase 2.audit — honesty-auditor 起動 (BM 残 2 件 + Phase 2.X 整合確認) 📋

- [ ] **2.audit.1** orchestrator は `honesty-auditor` (or `general-purpose` +
  brief で `docs/audit/honesty-auditor-core.md` を SoT 指定) を起動。対象:
  - Phase 2.BM.1: `brunn_minkowski_volume_indicator` (L372) の tag migration
    正しさ + signature honesty (genuine chain 着地点として load-bearing 形態が
    closure plan の意図と整合)
  - Phase 2.BM.2: `brunn_minkowski_entropy_jointPi` (L493) の tag migration +
    🟢ʰ 散文削除 + 再表現散文の意味論的整合性
  - Phase 2.X: `IsBMEntropyPowerVolumeHyp` (L441) の Phase V close 済注記の
    verbatim 整合 + cross-family consumer の verifiability (`rg` 結果再確認)
- [ ] **2.audit.2** verdict 受領 + 3 値判定 (CLAUDE.md「Independent honesty
  audit」§closure 判定):
  - **ok** → Phase V 着手
  - **questionable** → docstring refine or 追加コメントで対応、Phase V 進行
  - **defect** (実は load-bearing claim が結論 unfold で循環 / `🟢ʰ` 散文
    削除が意味論を毀損 / wall 化候補注記が誤分類など) → 当該 declaration の
    tag を再修正、Phase V 進行前に解決
- [ ] **2.audit.3** **audit focus** (orchestrator brief に明記):
  - (a) `@audit:retract-candidate(closure-plan-completed)` reason variant が
    `audit-tags.md`「Retract-candidate reason 語彙」で許容範囲か
    (`closure-plan-completed` は既存語彙 `load-bearing-predicate` /
    `conclusion-as-hypothesis` / `name-laundering-alias` のいずれにも明確に
    fit せず、本 plan で **新規 variant** を導入提案 — auditor 委任)
  - (b) 散文削除の意味論的等価性 (Phase 2.BM.2 の 🟢ʰ 散文 6 行 →
    `@audit:retract-candidate` + 再表現散文への置換が情報損失を生じていないか)
  - (c) Phase 2.X 注記の cross-family verifiability (`IsBMEntropyPowerVolumeHyp`
    が真に in-family closed か、auditor が `rg` 再確認)

**proof-log**: yes (`docs/proof-logs/proof-log-brunn-minkowski-residual-2.audit.md`)。
理由: auditor verdict + `closure-plan-completed` reason variant の新規導入判定 +
🟢ʰ 散文削除の意味論的整合性レビュー結果を残す。

### Phase V — verify + 集約 + closure plan banner 更新 + moonshot banner 更新 📋

- [ ] **V.1** `lake env lean InformationTheory/Shannon/BrunnMinkowskiClosure.lean` 確認
  (0 errors):
  ```bash
  lake env lean InformationTheory/Shannon/BrunnMinkowskiClosure.lean
  ```
  本 plan は signature / body 改変なしのため olean refresh 不要 (Pattern A
  非適用)。WynerZiv.lean / BrunnMinkowskiFunctional.lean も touch していない
  ため sanity 確認のみ:
  ```bash
  lake env lean InformationTheory/Shannon/WynerZiv.lean
  lake env lean InformationTheory/Shannon/BrunnMinkowskiFunctional.lean
  ```
- [ ] **V.2** 集計コマンド実行:
  ```bash
  rg -c '@audit:suspect' InformationTheory/Shannon/BrunnMinkowskiClosure.lean
  # 期待値: 0 (本 plan Phase 2.BM.1 + 2.BM.2 で削除)

  rg -c '🟢ʰ' InformationTheory/Shannon/BrunnMinkowskiClosure.lean
  # 期待値: 0 (本 plan Phase 2.BM.2 で削除)

  rg -c '@audit:retract-candidate\(closure-plan-completed\)' InformationTheory/Shannon/BrunnMinkowskiClosure.lean
  # 期待値: 2 (Phase 2.BM.1 + 2.BM.2 で付与)

  rg -nw 'sorry' InformationTheory/Shannon/BrunnMinkowskiClosure.lean | wc -l
  # 期待値: 不変 (本 plan は新規 sorry 0 件、既存 sorry 件数も変えない)

  rg -c '@audit:suspect' InformationTheory/Shannon/WynerZiv.lean
  # 期待値: 0 (Round 1 完了状態を維持、本 plan touch しない)

  rg -c '@audit:suspect\(' InformationTheory/Shannon/BrunnMinkowskiFunctional.lean
  # 期待値: 0 (Round 2 完了状態を維持、本 plan touch しない、`\(` 直接タグ pattern)
  ```
- [ ] **V.3** **closure plan banner 更新**: `brunn-minkowski-closure-plan.md`
  の進捗 L16 を編集:
  ```
  - [x] Phase V — clean ✅ (`lake env lean InformationTheory/Shannon/BrunnMinkowskiClosure.lean` silent +
    残 honest hyp 棚卸し完了。`@audit:suspect(brunn-minkowski-closure-plan)` 残 2 件は
    `brunn-minkowski-residual-sorry-migration-plan.md` 経由で
    `@audit:retract-candidate(closure-plan-completed)` に migration 完了 (2026-05-26))
  ```
- [ ] **V.4** **moonshot banner 更新**: `brunn-minkowski-moonshot-plan.md` 冒頭
  banner に Phase V close 済を反映 (closure plan Phase V banner 更新と同期):
  ```
  Phase V residual sorry-migration 完了 (`docs/shannon/brunn-minkowski-residual-sorry-migration-plan.md`
  参照)、closure plan §Phase V — clean を ✅ に確定。BrunnMinkowskiClosure.lean 内
  legacy `@audit:suspect` / 散文 `🟢ʰ` は 0 件、`@audit:retract-candidate(closure-plan-completed)`
  に統一済。
  ```
- [ ] **V.5** **Pilot 知見の handoff 反映** (`.claude/handoff-sorry-migration.md`
  Active orchestration log + Next phase に追記):
  - Pattern D 発展形 (`rg @audit:suspect` で docstring 内 migration done note の
    文字列リテラルが grep ヒット) → runbook §「失敗パターン」拡張提案を本
    plan §「audit-tags.md 拡張提案」として記録
  - `@audit:retract-candidate` の **`closure-plan-completed` reason variant**
    の新規導入 (本 plan で初出) → audit-tags.md「Retract-candidate reason
    語彙」拡張提案として記録 (本 plan の commit に同梱せず、別 PR 候補)
  - Round 2 plan 在庫表 #30 / #32 の意図的 scope-out (closure plan §F + §G
    着地点) を本 plan の Phase V close で正式 close 化した recipe (= 段階着地点
    の tag migration は signature / body 改変なし + retract-candidate 化のみ
    で十分) → 後続 family の段階着地点 tag migration の参考に。

**Phase V DoD**:
- BrunnMinkowskiClosure.lean で `@audit:suspect` 0 件 + 🟢ʰ 0 件 +
  `@audit:retract-candidate(closure-plan-completed)` 2 件。
- WynerZiv.lean / BrunnMinkowskiFunctional.lean 未編集 (Round 1 / Round 2
  完了状態維持)。
- `lake env lean` 各 file 0 errors。
- closure plan §Phase V banner ✅ 確定 + moonshot banner 更新済。
- handoff §Active orchestration log に Pattern D 発展形 + `closure-plan-completed`
  reason variant の新規導入記録済。

**proof-log**: yes (`docs/proof-logs/proof-log-brunn-minkowski-residual-V.md`)。
理由: Pattern D 発展形の発覚 + `closure-plan-completed` reason variant の
新規導入 + closure plan Phase V close 確定の判断材料を残す。

## 撤退ライン

- **L-RES-1 (`closure-plan-completed` reason variant が auditor で却下)**:
  Phase 2.audit で auditor が「`@audit:retract-candidate(closure-plan-completed)`
  は `audit-tags.md`「Retract-candidate reason 語彙」未登録、新規 variant の
  導入は別 PR 必須」と判定した場合、本 plan は Phase 2.BM.1 / Phase 2.BM.2 の
  reason variant を **既存語彙** (`load-bearing-predicate` または `conclusion-as-hypothesis`)
  に降格する。降格時の reason 選択:
  - L372 `brunn_minkowski_volume_indicator` → `load-bearing-predicate` (h_pl
    が n-dim PL 結論を hypothesis として直接受領するため)
  - L493 `brunn_minkowski_entropy_jointPi` → `load-bearing-predicate` (4 honest
    hyp 縮約済の load-bearing 形態)

  この降格は意味論的に等価 (両 declaration とも load-bearing predicate を
  hypothesis として持つため) だが、closure plan §F / §G 段階着地点の意図的
  load-bearing を明示する vocabulary が失われる。`audit-tags.md` 拡張提案
  (本 plan §「audit-tags.md 拡張提案」) の別 PR で `closure-plan-completed`
  variant を formal 導入後に再度 migration するワークフローを記録。

- **L-RES-2 (Phase 2.BM.2 の 🟢ʰ 散文削除が意味論毀損と判定)**: Phase 2.audit
  で auditor が「Phase 2.BM.2.2 の再表現散文が L476-481 の 🟢ʰ 散文 6 行と
  意味論的に等価ではない (例: `closure plan §G Phase 3 pivot` の文脈が伝わら
  ない / `load-bearing 部分は IsBMEntropyPowerVolumeHyp に集約済` の明示性が
  弱い)」と判定した場合、本 plan は再表現散文を auditor 提案に従って refine
  する (Phase 2.BM.2.2 を再実行)。最悪 case では 🟢ʰ 散文の literal 表記を
  維持 + `(* tier 4 deprecated — Phase V tag migration 後の意味論保持目的
  で literal 維持 *)` の補足コメントを追加する hybrid 形式に降格。

- **L-RES-3 (`IsBMEntropyPowerVolumeHyp` の cross-family verifiability で defect
  検出)**: Phase 2.X の cross-family `rg` 確認で「実は LZ78 / EPI / Stam 等
  他 family で参照されている」と判明した場合、本 plan は Phase 2.X の Phase V
  close 注記を「in-file 11 hit + cross-family <列挙>」に修正する。S3 (infrastructure
  construction) 該当の場合は Phase 2.X を保留 + 統合 plan 化候補として未決事項
  に escalate (runbook 「3 段階判定」遵守)。

- **L-RES-4 (Approach 変更: pilot scope 縮減)**: Phase 2.BM.1 / 2.BM.2 / 2.X /
  2.audit が 1 session で完走しない / `lake env lean` が想定外 error を発生
  させる場合、本 plan は **Phase 2.BM.1 のみで pilot を close** (L372
  `brunn_minkowski_volume_indicator` 1 件のみ migration 完了)、L493 / Phase 2.X
  は後続 session に分離する。closure plan §Phase V — clean の正式 close は
  L493 完了まで待つ。

## 未決事項

planner が判断つかない事項を列挙。実装 / auditor 委任で済む項目は明記。

1. **`@audit:retract-candidate(closure-plan-completed)` reason variant の正式
   導入** (auditor 判定対象 + audit-tags.md 拡張提案):
   - 本 plan で **新規 variant** として導入提案。`audit-tags.md`「Retract-candidate
     reason 語彙」既存:
     - `load-bearing-predicate`
     - `conclusion-as-hypothesis`
     - `name-laundering-alias` (2026-05-26 Relay honesty audit で導入)
   - 提案理由: closure plan §F / §G の **段階着地点** (genuine chain で publish
     済の load-bearing 形態、closure plan の意図通りの honest hyp 着地、本来は
     deprecation 対象ではない) を tier 3 bookkeeping 表記する vocabulary が
     既存に存在しない。`load-bearing-predicate` は「load-bearing 形態だが
     retract 候補」を含意するが、closure plan §F / §G は **retract 候補ではなく
     完了着地点** であり意味が異なる。
   - planner 推奨: `closure-plan-completed` を **新規 variant** として正式
     導入 (本 plan の Phase V handoff §「audit-tags.md 拡張提案」記録経由)。
   - **auditor 委任**: Phase 2.audit verdict 次第。auditor が「既存
     `load-bearing-predicate` で十分」と判定すれば本 plan は降格 (L-RES-1)、
     auditor が「新規 variant 必要」と承認すれば本 plan の commit に
     audit-tags.md 拡張 PR を同梱しない (別 PR、本 plan scope 外)。

2. **`wall:bm-convex-body-sqrt` 化候補の別 PR 化** (user 確認):
   - Round 2 plan §R4 #2 で提案済 (`IsBMEntropyPowerVolumeHyp` を wall name
     register に正式登録)。本 plan は **採用せず** (Phase 2.X 注記で別 PR
     候補として記録のみ)。
   - 別 PR 候補 plan 候補: `brunn-minkowski-from-epi-discharge-plan.md` (EPI
     route、現状未着手) または `prekopa-leindler-induction-plan.md` (n-dim PL
     route、closure plan §F で部分的に触れている)。
   - user 確認待ち: 別 PR を本 session 完了後すぐに起こすか、後続 sweep
     (EPI/Stam family + ParallelGaussianPerCoord、runbook Round 3) と合流させるか。

3. **Phase 1.4 audit-1 を skip するか実施するか** (orchestrator 判断):
   - Phase 1.4 は WynerZiv scope-out 確認の独立検証 (本 plan 起草段階の verbatim
     確認の保険) で optional。orchestrator が起草時の確認 (本 plan §Context
     「実残置の verbatim 確認」表) を信頼すれば Phase 1.4 skip 可能、Phase 2.audit
     で全体 audit に統合可能。
   - planner 推奨: **skip** (本 plan の本実 sweep 対象は BM 2 件のみで、WynerZiv
     touch なしを Phase 2.audit で確認すれば十分)。

4. **proof done を本 plan で目指さない方針の明示確認** (user 確認):
   - 本 plan の DoD は **type-check done** のみ。entropy 形 BM の完全 closure
     (凸体 Brunn-Minkowski の Mathlib 不在解消、`wall:bm-convex-body-sqrt`
     discharge) は **未着手のまま** で本 plan は close する。
   - closure plan §Phase V — clean を本 plan で ✅ 確定するのは「`@audit:suspect`
     / 🟢ʰ 散文 0 件」レベルの **honesty 強化のみ** で、genuine chain
     completion (= proof done) は本 plan の出力にしない。

5. **handoff §6 A3 §2 との関係 (本 plan の scope 外確認)**:
   - 本 plan は BrunnMinkowski 系のみで Round 1 WynerZiv plan の handoff
     §6 A3 §2 (`wyner_ziv_tendsto_chain` / `wzAchievability_random_binning_body`
     境界判定 + body restoration) には関与しない (WynerZiv scope-out 確認のみ)。
   - WynerZiv handoff §6 A3 §2 の進行は本 plan と独立に Round 2 Wave 2
     (`wynerziv-phase2-predicate-removal-plan.md`) で扱う。

## audit-tags.md 拡張提案 (本 plan 経由で議題化)

本 plan の Phase 2.audit verdict (未決事項 #1) を経て、`docs/audit/audit-tags.md`
への formal 拡張を **別 PR で提案**:

1. **`@audit:retract-candidate(closure-plan-completed)` reason variant 追加**:
   - 既存 reason 語彙 (`load-bearing-predicate` / `conclusion-as-hypothesis` /
     `name-laundering-alias`) と並列に追加。
   - 意味: 「closure plan / family-specific plan で genuine chain 着地済の
     load-bearing 形態。declaration 自体は維持、tag は migration done 表記
     として retract-candidate に降格」。
   - 適用例: 本 plan の L372 + L493 の 2 件、後続の段階着地点 (例: EPI/Stam
     family の `IsStamMain` 等の段階着地点) でも同パターンが出現可能。

2. **Pattern D 発展形 (grep 直接タグ vs docstring 文字列リテラル区別) の
   runbook 拡張**:
   - 現行 `audit/sorry-migration-runbook.md` §「Pattern D — `sorry` 件数の
     docstring 文字列誤計数」は `rg -nw 'sorry'` (word-boundary) で解決と記述。
   - 本 plan で発覚した発展形: `rg @audit:suspect` でも docstring 内 migration
     done note の文字列リテラル (`「Phase 1 (sorry-migration): the \`@audit:suspect\`
     tag was removed — ...」`) が grep ヒット (本 plan §Context「Pattern D
     適用例」参照)。
   - 拡張提案: 「inventory step では **declaration 直接タグ** `@audit:suspect\(`
     (パーレン付きパターン) と **docstring 内 mention** (`「\`@audit:suspect\`」`
     等の literal) を区別する grep pattern を併用」。本 plan §Context の
     `awk` ベース判定例も runbook に併記候補。

両拡張提案とも本 plan の commit に同梱しない。本 plan の handoff §V.5 に
記録 + 別 PR / 別 session で formal 議題化。

## 判断ログ

書く頻度: 方針変更 / 撤退ラインへの紐付け / 当初仮定の修正があったとき。
append-only。

1. **2026-05-26 plan 起草**: lean-planner (本 session、docs-only) が
   `InformationTheory/Shannon/BrunnMinkowski{Functional,Closure}.lean` +
   `InformationTheory/Shannon/WynerZiv.lean` 3 file の `@audit:suspect` / 🟢ʰ 残置を
   verbatim 読込で per-declaration 分類。
   - **orchestrator brief との計数差分**: 起動 brief は「BrunnMinkowskiFunctional
     4 suspect / BrunnMinkowskiClosure 2 suspect + 1 🟢ʰ / WynerZiv 2 suspect」
     と通告したが、`rg -n` + Read で実コードを verbatim 確認した結果、
     **真の直接タグ = BMClosure 2 件 + 同居 🟢ʰ 1 件のみ**。残り 6 件 (BMFunctional
     4 件 + WynerZiv 2 件) は **docstring 内 migration done note の文字列
     リテラル** (Round 2 / Round 1 で sweep 完了済の sign-off note の文字列が
     grep ヒット)。Pattern D (`sorry` 文字列誤計数) の発展形であり、本 plan
     §Context + §「audit-tags.md 拡張提案」#2 で runbook 拡張議題化。
   - **scope 確定**: 本 plan は **BMClosure 2 件 (L372 + L493) のみ** の sweep
     対象、WynerZiv + BMFunctional は scope-out 確認のみ (本 plan で touch
     しない、Round 1 / Round 2 完了状態を維持)。
   - **closure plan §Phase V 連動**: 本 plan の Phase V close で
     `brunn-minkowski-closure-plan.md` §Phase V — clean の 🚧 を ✅ に確定。
     closure plan の genuine chain は変えない、tag vocabulary 整理のみ。
   - **新規 reason variant 提案**: `@audit:retract-candidate(closure-plan-completed)`
     を本 plan で **初出**として導入。auditor 委任で正式承認確認後に
     audit-tags.md 拡張 PR (本 plan scope 外、別 PR)。
   - **cross-family 検出**: BMClosure 残 2 件 + `IsBMEntropyPowerVolumeHyp`
     とも in-file closed (`rg` で同 file 内のみ、S3 該当 0 件)、escalate 不要。
   - **tier 5 defect 新規発見 0 件** (両 declaration は closure plan §F / §G の
     genuine chain 着地点として load-bearing 形態が **意図的かつ acknowledged**、
     tier 4 寄りで tier 5 ではない)。

<!-- 後続セッションで判断変更があれば下記に追記 (append-only):
2. **YYYY-MM-DD <要点>**: <変更理由 + 撤退ラインへの紐付け>。
-->
