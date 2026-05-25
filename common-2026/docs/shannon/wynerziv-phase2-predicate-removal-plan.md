# Shannon: Wyner–Ziv Phase 2.x — load-bearing predicate residue removal

> **Parent**: [`wyner-ziv-moonshot-plan.md`](wyner-ziv-moonshot-plan.md)
> **Predecessor (Round 1)**: [`wynerziv-sorry-migration-plan.md`](wynerziv-sorry-migration-plan.md)
> 関連 [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md) /
> [`audit/audit-tags.md`](../audit/audit-tags.md) /
> CLAUDE.md「検証の誠実性」+「sorry を書けない箇所での対処順序」+
> 「Mathlib-shape-driven Definitions」+「Standard agent prompt boilerplate」。
>
> 本 plan は **Round 1 完了後の intermediate state** — body は `sorry +
> @residual(plan:wyner-ziv-discharge-moonshot-plan)` に置換済だが、signature 上に
> **load-bearing predicate hypothesis (`WZ*Bound` / `Is*Hyp` 系)** を **残置**
> している 13 declaration を tier 2 (sorry + residual + clean signature) まで
> 引き上げる **honesty 強化のみ** の workstream。proof completion は本 plan の
> 出力にしない (= `wyner-ziv-discharge-moonshot-plan` 等別 workstream 継続)。
>
> **Round 4 closure (2026-05-26)**: 境界判定 2 件 (`wyner_ziv_tendsto_chain` /
> `wzAchievability_random_binning_body`) が proof done 到達 (Tier 1 `@audit:ok`、
> 0 sorry / 0 @residual)、in-flight tracker から除外済 (判断ログ #2)。本 plan
> の実 scope = 明確改変対象 11 declaration、Phase 2.x.1.a.6 / Phase 2.x.1.e /
> L-PR-1 / 未決事項 2 / 3 closed。

## Context

### なぜ Phase 2.x なのか — Round 1 完了状態と honesty 不足

Round 1 (`wynerziv-sorry-migration-plan.md` Phase 1.5) は **「signature を改変せず
body のみ `sorry` に retreat」** という設計判断を採用 (cross-family Relay 衝突
回避のため Phase 2.3 で `@audit:retract-candidate(load-bearing-predicate)` 付与
に留め、predicate 自体は削除しないと決定)。結果として、Round 1 完了後の
declaration は次のような形になっている:

```lean
/-- ... `@residual(plan:wyner-ziv-discharge-moonshot-plan)` -/
theorem wyner_ziv_converse_chain
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) {n : ℕ} (hn : 0 < n) (M : ℕ)
    (D : ℝ) (D_arr : Fin n → ℝ)
    (wzPerLetterObjective : Fin n → ℝ)
    (h_perLetter : WZPerLetterBound U P_XY d D_arr wzPerLetterObjective)  -- ← load-bearing
    (h_csiszar : CsiszarSumIdentity wzPerLetterObjective M)                 -- ← load-bearing
    (h_jensen_antitone : WZJensenAntitone U P_XY d D D_arr) :               -- ← load-bearing
    wynerZivRatePmf U P_XY d D ≤ Real.log (M : ℝ) / (n : ℝ) := by
  sorry
```

これは **type-check done** (`lake env lean` 0 errors、`@residual` 付き sorry) は
満たしているが、CLAUDE.md「検証の誠実性」の honesty 階層では tier 2 と tier 4 の
間に位置する **半 honest** 状態:

- `@audit:staged(wyner-ziv-load-bearing)` から `@residual(plan:...)` への置換は
  完了 → tier 4 (legacy) から tier 2 (sorry-based) への前進
- しかし **signature 上の load-bearing predicate は残置** → 仮に将来の auditor /
  closer が「`sorry` を埋める」と読んだ場合、predicate を hypothesis として受け
  取り body で機械展開すれば `sorry` を消せてしまう余地が残る (load-bearing
  hypothesis bundling 再発の温床)

`@residual(plan:wyner-ziv-discharge-moonshot-plan)` が指す discharge plan が
predicate-consumer 形態の closure を選んだ場合、それは Round 1 で disposed したはずの
**「load-bearing predicate に核を bundle」** パターンを実質的に復活させる結果と
なる。本 Phase 2.x はこのリスクを構造的に閉じる:

- signature から load-bearing predicate を削除 (predicate definition 自体は
  cross-family Relay 保護のため残す — Phase 2.3 と同じ方針)
- body は引き続き `sorry + @residual(plan:wyner-ziv-discharge-moonshot-plan)`
- 結論型は変えない (downstream caller の API 互換性を保つ)

Round 1 の Phase 1.5 と異なるのは **signature 改変が伴う** こと。caller drift が
発生するため、Round 1 ripple 設計 (Pattern C 散文方式) と同じ handling を再適用
する。

### Round 1 完了状態の verbatim 確認 (2026-05-25)

`rg -nw 'sorry' Common2026/Shannon/WynerZiv*.lean` 出力に基づく現状計数:

| 計数項目 | 件数 | 検証コマンド |
|---|---:|---|
| `@audit:suspect` total | **0** | `rg -c '@audit:suspect' Common2026/Shannon/WynerZiv*.lean` (Round 1 で sweep 済) |
| `@audit:staged` total | **0** | `rg -c '@audit:staged' Common2026/Shannon/WynerZiv*.lean` (Round 1 で sweep 済) |
| `🟢ʰ` 散文 | **0** | `rg -c '🟢ʰ' Common2026/Shannon/WynerZiv*.lean` (Round 1 で sweep 済) |
| `@residual(plan:wyner-ziv-discharge-moonshot-plan)` | **15** (declaration 付与は 13 件、残 2 件は docstring 内言及) | Round 1 完了 |
| `@residual(defect:false-statement)` | **2** | `WynerZivAchievability.lean:76` + `WynerZivConverse.lean:243` — 本 plan **scope 外** (discharge plan 委譲) |
| `@residual(defect:circular)` | **1** | `WynerZivAchievability.lean:103` — `wyner_ziv_achievability_existence` Phase 2.1 retreat 済、本 plan **scope 外** |
| `@audit:retract-candidate(load-bearing-predicate)` | **多数** | 12 predicate に Round 1 で付与済 — 本 Phase 2.x で 3 件 (cross-family) は Relay 注記維持、9 件 (family 内) は signature 改変成功後に scope 外 deprecation 候補 |
| `⚠ HONESTY ALERT` / `FALSE` | **0** | `rg '⚠\|HONESTY ALERT\|FALSE' Common2026/Shannon/WynerZiv*.lean` — Pattern H 該当なし |

### Round 1 → Phase 2.x の honesty 差分

| Tier | Round 1 完了状態 | 本 Phase 2.x 完了状態 |
|---|---|---|
| 2 (sorry + @residual、clean signature) | 0 件 | **+13 件** (本 plan で予測 11-13、境界判定で 11-12 件、option A scope) |
| 4-寄り (sorry + @residual だが signature に load-bearing predicate) | 13 件 | 0 件 (option A scope) |
| 5 (defect:circular / false-statement) | 3 件 (Achievability 2 + Converse 1) | 不変 (scope 外) |

「半 honest」状態 13 件を清算するのが本 plan の唯一の目的。

### 親 moonshot との関係

`wyner-ziv-moonshot-plan.md` Phase 0-D の pass-through 設計は変更しない。Round 1
が「load-bearing predicate を consumer body から削除して `sorry` に」と書換えた
のと同じ方向の延長で、本 Phase は predicate を **signature 上から** も削除する。
結論型は変えないため、`Common2026.lean` 編入状態 (Phase V) は変えない。

### Honesty workflow と DoD

本 plan の DoD は CLAUDE.md「Definition of Done — 2 段階」の **type-check done**:

- 各 file `lake env lean Common2026/Shannon/WynerZiv<X>.lean` が 0 errors
- 各 `sorry` に `@residual(plan:wyner-ziv-discharge-moonshot-plan)`
- caller drift 発生時は Round 1 と同じ「散文 transitive 明示、即興 vocabulary
  禁止」(Pattern C)
- Phase 完了時に `honesty-auditor` (or `general-purpose` + brief で SoT 指定) を
  起動し、signature honesty + classification + (重要) **load-bearing predicate
  hypothesis が signature から落ちたこと** を独立 verify

`@audit:ok` (proof done) は本 plan の出力にならない。

### Tier 5 defect 検出 (inline policy 適用、planner 段階)

`rg '⚠|HONESTY ALERT|FALSE' Common2026/Shannon/WynerZiv*.lean` を実行 → **0 hit**
(Pattern H 該当なし)。Round 1 で既に 2 件の tier 5 false-statement
(`wyner_ziv_converse_rate` + `wyner_ziv_achievability_rate`、`@residual(defect:false-statement)`)
+ 1 件の circular defect (`wyner_ziv_achievability_existence`、
`@residual(defect:circular)`) は **scope 外 (discharge plan 委譲)** として明示処理
済 — 本 Phase 2.x はこれらを touch しない。

新規 tier 5 defect の発見も planner 段階で **0 件**。13 件 declaration は全て
load-bearing predicate consumer の半 honest 形態 (tier 2/4 中間) であり、circular
`:= h` / name laundering / 退化定義悪用には該当しない。signature から load-bearing
predicate を削除 + body `sorry` 維持で tier 2 化が成立する直線的な状況。

## Approach

**file 単位 sweep + scope option A 採用 + Round 1 と同じ「predicate definition は
削除しない、cross-family Relay 保護」設計の延長**。

### Scope 選択 — Option A 採用 (planner 判断)

User brief で提示された 2 option:

- **Option A**: 「Relay 側の re-namespacing 残置を許容 + WynerZiv 側のみ
  predicate hypothesis 除去」 (scope 狭、進行可)
- **Option B**: 「両 family 統合 plan 化として未決事項に escalate」 (scope 広、
  Relay planner 完了後に統合判断)

**Option A を採用**。根拠 (3 点):

1. **本 Phase の唯一の目的は signature honesty 強化**。consumer 側の signature
   から load-bearing predicate を削除すれば honesty 階層 tier 2 化が成立し、
   predicate definition は signature 上に現れなくなる。predicate **definition
   自体の存在** は cross-family Relay 利用のため必要だが、honesty 観点では
   problem ではない (Round 1 Phase 2.3 で既に `@audit:retract-candidate(load-bearing-predicate)`
   が付与済、bookkeeping は完了済)。

2. **Round 1 が既に同方針を選択済**。Round 1 Phase 2.3 は predicate を削除せず
   `@audit:retract-candidate` 付与のみで close した (L-MIG-2 撤退ライン)。本
   Phase 2.x で同じ predicate に新たな構造的判断を加えることは Round 1 設計の
   trace continuation。

3. **並行する Relay planner との衝突回避**。並列起動中の Relay
   sorry-migration plan は本 plan と同 session で起草されており、Relay 側で
   `IsWynerZivBinningCovering` / `..._Packing` / `..._Achievable` 3 predicate を
   re-namespacing 利用する scheme を変更する可能性は低い (verbatim 確認:
   `RelayCFBinningBody.lean:127/195/262` で `IsWynerZivBinningCovering.mono` /
   `.rate_irrelevant` 等の field accessor + Iff.rfl で再公開している)。本 Phase
   が Relay 側 namespace を touch しないなら衝突しない。

Option B は次の case で再考 (撤退ライン L-PR-3 として記録): Relay sweep が
「`IsWynerZivBinning*` predicate を Round 2 で削除しないと Relay 側が type-check
できない」と planner 判断した場合、本 Phase 2.x は pause、両 plan の Approach を
統合判断にエスカレートする (本 plan の Phase 2.x.3 / 2.x.4 のみが影響を受ける、
Phase 2.x.1 / 2.x.2 は予定通り完走可能)。

### 戦略 (Phase 構造)

```
Phase 0   Inventory (本 plan 内 inline、完了済)
   │
Phase 2.x.1  signature 改変 (consumer 13 件、load-bearing predicate hyp を削除)
   │      ├─ WynerZivConverseChain.lean 6 件
   │      ├─ WynerZivBinningCovering.lean 4 件 (cross-family caller 注記)
   │      ├─ WynerZivCoveringBody.lean 1 件
   │      ├─ WynerZivPackingBody.lean 1 件
   │      └─ WynerZivBinningBody.lean 1 件 (境界判定対象)
   │
Phase 2.x.2  ripple — caller drift handling
   │      ├─ in-family caller drift (WynerZivAchievabilityBridge /
   │      │    WynerZivDischarge / WynerZivDecoderFailureAssembly 等) は
   │      │    Round 1 と同じ散文 transitive 形式 (Pattern C)
   │      └─ cross-family caller (RelayCFBinningBody.lean:348
   │           `wyner_ziv_binning_via_covering_packing` 直接呼出) は touch しない
   │           — Relay 側 sweep agent の責務
   │
Phase 2.x.3  predicate definitions の deprecation 注記更新 (cross-family 注記
   │           re-confirm、family 内 9 predicate は scope 外 deprecation 候補)
   │
Phase 2.x.4  audit-2 (honesty-auditor 起動、Phase 2.x.1 全件 + Phase 2.x.2 ripple)
   │
Phase V    verify + 集計 + 親 plan banner 更新
```

各 Phase 完了時 `lake env lean <file>` 0 errors。signature 改変が発生する Phase
2.x.1 commit 前に **必ず** `lake build Common2026.Shannon.<改変 module>` で olean
refresh を実行 (Pattern A、Round 1 で実証済)、その後 dependent file 再 verify。

### Sub-bound 引数表 (CLAUDE.md「Brief content checklist 項目 1」)

本 plan は P_cb / P_target 分離型 capacity 引数を扱わないため (rate-bound の RHS
は `Real.log (M : ℝ) / (n : ℝ)` または `μ.real ... ≤ ε_typ + ε_bin` 等の単純合成)、
sub-bound 引数表は不要。各 declaration の load-bearing predicate hypothesis は
同 namespace 内の predicate を 1-3 個取るだけで、capacity 引数の側別 routing は
発生しない。

### 共有 wall lemma 集約の要否

**集約しない**。Round 1 と同じ判断:
`docs/audit/audit-tags.md`「Wall name register」に Wyner–Ziv 関連 wall は未登録、
本 Phase 2.x で新規 wall を導入しない。全件 `@residual(plan:wyner-ziv-discharge-moonshot-plan)`
で揃える。

### Wall name register 拡張提案 (R4)

**提案 0 件**。本 Phase 2.x は signature 改変のみで新規 sorry は発生しない (既存
sorry の `@residual` タグは継承)。新規 Mathlib 壁の identification は本 Phase の
scope ではない。

### Pattern A-H 適合チェック (CLAUDE.md runbook §「失敗パターン」逐一確認)

| Pattern | 該当性 | 対処 |
|---|---|---|
| **A** (stale olean で type error 見逃し) | ✅ 強い該当 — Phase 2.x.1 は **全 declaration が signature 改変** | Phase 2.x.1 commit 前に `lake build Common2026.Shannon.<改変 module>` 必須、その後 dependent ファイル全件 `lake env lean` 再 verify (Phase 2.x.2 ripple step に組込) |
| **B** (planner 全件 sorry 指示の overcorrect) | ✗ 不該当 — 本 Phase は新規 sorry を作らない、既存 sorry を維持 | constructive recovery 候補 0 件 (13 件全部が deep info-theoretic content、Round 1 で staged だった件はすべて genuine load-bearing) |
| **C** (transitive sorry の tag 誤付与) | ✅ 強い該当 — Phase 2.x.2 で caller drift | 即興 vocabulary 禁止、docstring 散文「Transitive sorry via <upstream> (Phase 2.x.1 retreat). No `@residual` tag is attached — closure responsibility belongs to upstream's `@residual(plan:wyner-ziv-discharge-moonshot-plan)`」を一律 |
| **D** (`sorry` 計数 docstring 文字列誤計数) | ✗ 不該当 — Round 1 で適用済、本 Phase でも `rg -nw 'sorry'` で word-boundary 計数を継続 | (継続のみ) |
| **E** (predicate retract-candidate の extract-only consumer 見落とし) | △ 注意 — `IsWynerZivBinningAchievable.covering` / `.packing` (field accessor) は extract-only consumer の代表例 | Phase 2.x.3 で 3 cross-family predicate の docstring に「Relay 側で `.field` accessor + Iff.rfl の extract-only consumer が複数残存」と verbatim 注記 (Round 1 Phase 2.3 docstring に既出、本 Phase は維持 + auditor 確認) |
| **F** (tier 5 defect の suspect 計数見落とし) | ✗ 不該当 — Round 1 で 3 件の tier 5 defect (Achievability 2 件 + Converse 1 件) は既に分類済、本 Phase scope 外として明示 | (再確認のみ、新規 tier 5 defect 検出は planner 段階で 0 件) |
| **G** (cross-family unified predicate の単独 deprecate 不可) | ✅ 強い該当 — `IsWynerZivBinning{Covering,Packing,Achievable}` 3 件が Relay 利用 | Phase 2.x.3 で **predicate definition は touch しない**、docstring 注記のみ。Option A scope の中核設計 |
| **H** (既存 HONESTY ALERT / FALSE predicate の重畳) | ✗ 不該当 — planner 段階で `rg '⚠\|HONESTY ALERT\|FALSE'` 実行、0 hit | (継続のみ) |

## 在庫: 13 declaration の verbatim 分類

verbatim 確認方法: 各 `@residual(plan:wyner-ziv-discharge-moonshot-plan)` 周辺の
docstring + theorem signature を実コードから読込み、「signature の hypothesis が
load-bearing predicate (`Is*Hyp` / `WZ*Bound` / `CsiszarSumIdentity` /
`WZJensenAntitone` 等) を含むか / regularity のみか」を 1 件ずつ判定。

### 13 件の inventory 表 (sub-section 別)

#### WynerZivConverseChain.lean (6 件、全件 chain assembly の predicate consumer)

| file:line | decl 名 | 現 signature の load-bearing predicate hypothesis | 提案 sorry-only signature (Phase 2.x.1 後) | cross-family? |
|---|---|---|---|---|
| `WynerZivConverseChain.lean:154` | `wyner_ziv_converse_chain` | `h_perLetter : WZPerLetterBound U P_XY d D_arr wzPerLetterObjective`<br>`h_csiszar : CsiszarSumIdentity wzPerLetterObjective M`<br>`h_jensen_antitone : WZJensenAntitone U P_XY d D D_arr` | 3 hyp 全削除、`wzPerLetterObjective`/`D_arr` も引数から削除 (predicate 経由でしか使われない explicit param)。残る引数: `(P_XY)(d)(hn)(M)(D)` + 結論 `wynerZivRatePmf U P_XY d D ≤ Real.log (M : ℝ) / (n : ℝ)` | なし |
| `WynerZivConverseChain.lean:177` | `wyner_ziv_converse_chain_block` | 同上 3 hyp + `[MeasurableSpace γ]` + `WynerZivCode` 引数群 | 同上 3 hyp 削除、`D_arr`/`wzPerLetterObjective` 削除。残る引数: `(P_XY)(d)(D)(M n)(hn)(μ)(dN)(c)(_h_dist)` | なし |
| `WynerZivConverseChain.lean:472` | `wyner_ziv_converse_chain_composite` | `h_perLetter : WZPerLetterBound ...`<br>`h_jensen_antitone : WZJensenAntitone ...` (2 件、`CsiszarSumIdentity` は 3 ingredient に分解された形式: `h_perLetter_le_condMI` / `h_chain` / `h_fano`) | `h_perLetter` + `h_jensen_antitone` の 2 件削除。3 ingredient (`h_perLetter_le_condMI`/`h_chain`/`h_fano`) は **境界判定** — auditor 委任 (これらは `wzPerLetterObjective` / `condMI` / `block` 等の sum-and-log inequalities = load-bearing なので併せて削除推奨)。残る引数: `(U)(P_XY)(d)(hn)(M)(D)` + 結論 | なし |
| `WynerZivConverseChain.lean:503` | `wyner_ziv_converse_n_letter_chain` | 同 `wyner_ziv_converse_chain_block` の 3 hyp | 同上 3 hyp 削除、`D_arr`/`wzPerLetterObjective` 削除 | なし |
| `WynerZivConverseChain.lean:557` | `wyner_ziv_converse_chain_existence` | `h_chain_nletter : ∀ n : ℕ, 0 < n → ∀ M : ℕ, ∀ c : WynerZivCode M n α β γ, (M : ℝ) ≤ Real.exp ((n : ℝ) * R) → c.expectedBlockDistortion μ dN ≤ D → wynerZivRatePmf U P_XY d D ≤ R` (= 結論を quantified 形で抱える) | `h_chain_nletter` 削除。残る引数: `[MeasurableSpace γ](μ)(P_XY)(d)(D R)(h_R_lt)(dN)` + 結論 (impossibility statement) | なし |
| ~~`WynerZivConverseChain.lean:611`~~ → `:656` | `wyner_ziv_tendsto_chain` | `h_ach : wynerZivRatePmf U P_XY d D ≤ R`<br>`h_chain_conv : R ≤ wynerZivRatePmf U P_XY d D` | ~~**境界判定** (auditor 委任) — 2 hyp とも `≤` order claim だが、`le_antisymm` 合成 = 構造的 non-load-bearing。Round 1 Phase 1.5 段階で auditor が「pure forwarder、`@residual` 不要」と判定する可能性あり (Round 1 plan 未決事項 2 で言及済)。本 Phase 2.x.1 では **暫定的に 2 hyp 維持** (auditor 判定後に再評価)~~ → **2026-05-26 Round 4 closure: proof done 到達** (Tier 1 `@audit:ok`、body `le_antisymm h_chain_conv h_ach`、0 sorry / 0 @residual)。「pure forwarder、`@residual` 不要」確定、tracker から除外。 | なし |

#### WynerZivBinningCovering.lean (4 件、cross-family Relay 影響あり)

| file:line | decl 名 | 現 signature の load-bearing predicate hypothesis | 提案 sorry-only signature (Phase 2.x.1 後) | cross-family? |
|---|---|---|---|---|
| `WynerZivBinningCovering.lean:268` | `wyner_ziv_binning_via_covering_packing` | `h_cov : IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT`<br>`h_pack : IsWynerZivBinningPacking R₂ ε₂ μ Us Ys JT f_U` | 2 hyp 削除。残る引数: `[Nonempty β][Nonempty γ]{R₁ R₂ ε₁ ε₂}(μ)[IsFiniteMeasure μ]{n M}(Us)(Ys)(JT)(f_U)(f)(h_meas_typ)(h_meas_bin)(h_meas_fail)` + 結論 `μ.real {ω : Ω \| ... } ≤ ε₁ + ε₂` | **あり** (`RelayCFBinningBody.lean:348` で `IsWynerZivBinningCovering` / `..._Packing` を作って直接呼出 — caller drift 発生、Relay 側 sweep で handling) |
| `WynerZivBinningCovering.lean:300` | `wynerZivBinningBody_of_covering_packing` | 同上 2 hyp (純 re-export forwarder) | 同上 2 hyp 削除 | あり (Relay 側 caller の有無は Round 2 Relay planner verify、`RelayCFBinningBody.lean` 内 `wynerZivBinningBody_of_covering_packing` への直接呼出は要確認 — 暫定的に「あり」と扱い Phase 2.x.2 ripple で再確認) |
| `WynerZivBinningCovering.lean:357` | `wyner_ziv_binning_existence_of_covering_packing` | `h_asymp : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ M Us Ys f_U f ε₁ ε₂, ... ∧ IsWynerZivBinningCovering R₁ ε₁ μ Us Ys (JT n) ∧ IsWynerZivBinningPacking R₂ ε₂ μ Us Ys (JT n) f_U` | `h_asymp` 削除。残る引数: `[Nonempty β][Nonempty γ]{R₁ R₂ : ℝ}(μ)[IsFiniteMeasure μ](JT)` + 結論 (existence-form decoder-fail bound) | あり (cross-family caller verify は Phase 2.x.2 ripple) |
| `WynerZivBinningCovering.lean:501` | `wyner_ziv_binning_decoder_fail_of_achievable` | `h_ach : IsWynerZivBinningAchievable R₁ R₂ ε₁ ε₂ μ Us Ys JT f_U` (= covering + packing の joint) | `h_ach` 削除。残る引数: `[Nonempty β][Nonempty γ]{R₁ R₂ ε₁ ε₂}(μ)[IsFiniteMeasure μ]{n M}(Us)(Ys)(JT)(f_U)(f)(h_meas_typ)(h_meas_bin)(h_meas_fail)` + 結論 | あり (`IsWynerZivBinningAchievable` も Relay で re-namespacing 利用) |

#### WynerZivCoveringBody.lean (1 件)

| file:line | decl 名 | 現 signature の load-bearing predicate hypothesis | 提案 sorry-only signature (Phase 2.x.1 後) | cross-family? |
|---|---|---|---|---|
| `WynerZivCoveringBody.lean:424` | `wzCovering_feed_asymp` | `h_cov : IsCoveringTypicalityHyp μ JT`<br>`h_pack : IsPackingExistenceHyp (γ := γ) μ JT` | 2 hyp 削除。残る引数: `[Nonempty β][Nonempty γ](μ)[IsProbabilityMeasure μ](JT)` + 結論 (existence-form joint asymp bundle) | なし (`IsCoveringTypicalityHyp` / `IsPackingExistenceHyp` は family 内 closed、要 `rg` 最終確認、Phase 2.x.3 で実施) |

#### WynerZivPackingBody.lean (1 件)

| file:line | decl 名 | 現 signature の load-bearing predicate hypothesis | 提案 sorry-only signature (Phase 2.x.1 後) | cross-family? |
|---|---|---|---|---|
| `WynerZivPackingBody.lean:563` | `wyner_ziv_packing_existence` | `h_asymp : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ M (_:NeZero M) Us Ys f S ε₁, ... ∧ IsPackingTypicalityHyp (n:=n) S (JT n) ∧ (∀ f_U, IsPackingCollisionBoundHyp (n:=n) Us Ys (JT n) f_U) ∧ MeasurableSet ... ∧ (∀ _f_U, IsWynerZivBinningCovering R₁ ε₁ μ Us Ys (JT n)) ∧ ...` (= 5+ predicate bundle) | `h_asymp` 削除。残る引数: `[Nonempty β][Nonempty γ](μ)[IsProbabilityMeasure μ]{R₁ R₂ : ℝ}(JT)` + 結論 (existence-form decoder-fail bound) | △ 部分的 (`IsWynerZivBinningCovering` を `h_asymp` 内で参照しているが、`h_asymp` を削除すれば signature から消える — predicate definition の cross-family 性は維持) |

#### WynerZivBinningBody.lean (1 件、境界判定対象)

| file:line | decl 名 | 現 signature の load-bearing predicate hypothesis | 提案 sorry-only signature (Phase 2.x.1 後) | cross-family? |
|---|---|---|---|---|
| ~~`WynerZivBinningBody.lean:492`~~ → `:493` | `wzAchievability_random_binning_body` | `h_typ_prob : μ.real (wzError_E_typ (n:=n) Us Ys JT) ≤ ε_typ`<br>`h_bin_prob : μ.real (wzError_E_bin (n:=n) Us Ys JT f_U) ≤ ε_bin` | ~~**境界判定** (auditor 委任、Round 1 plan 未決事項 2 と同様) — 2 hyp とも `μ.real (...) ≤ ε` 形 = probability bound (regularity-like)。Round 1 Phase 1.5 boundary case 注記 (`docstring:479-489`) で「auditor may rule that this should revert to constructive (tag-removal only)」と既出。本 Phase 2.x.1 では **暫定的に 2 hyp 維持 + auditor verdict 待ち**。auditor が「regularity-only、load-bearing ではない」と判定したら、本 declaration は本 Phase 2.x scope **外** に降格 → `@residual` 削除 + body constructive 復元 (Round 1 plan handoff §6 A3 §2 で言及された 4-line union-bound + add_le_add restoration が選択肢)~~ → **2026-05-26 Round 4 closure: proof done 到達** (Tier 1 `@audit:ok`、body は 4-line `wzAchievability_decoder_fail_le` + `add_le_add` の calc block、0 sorry / 0 @residual)。「regularity-only、non-load-bearing、body constructive 復元」確定、tracker から除外。 | なし |

### 集計 (パターン別、Round 1 Phase 1.5 plan の集計フォーマット踏襲)

- **明確に signature 改変対象 (load-bearing predicate consumer)**: **11 件**
  (ConverseChain 5 件 + BinningCovering 4 件 + CoveringBody 1 件 + PackingBody 1 件)
- ~~**境界判定 (auditor 委任)**: **2 件**~~ → **0 件** (2026-05-26 Round 4 closure 済、判断ログ #2)
  - ~~`wyner_ziv_tendsto_chain` (ConverseChain.lean:611) — 純 forwarder 性 vs.
    `≤` order claim の load-bearing 性~~ → proof done (Tier 1 `@audit:ok`、body
    `le_antisymm h_chain_conv h_ach`)
  - ~~`wzAchievability_random_binning_body` (BinningBody.lean:492) — regularity
    probability bound vs. load-bearing claim~~ → proof done (Tier 1 `@audit:ok`、
    body 4-line `wzAchievability_decoder_fail_le` + `add_le_add` calc)
- **cross-family caller drift 発生 (Relay 側 file)**: **4 件**
  (`wyner_ziv_binning_via_covering_packing` 直接呼出 1 件 + 残 3 件の Relay 利用
  ありなしは Phase 2.x.2 ripple で再確認)

総計 13 = 11 (明確改変) + 2 (境界判定)。

## Phase 詳細

### Phase 0 — Inventory (本 plan 内 inline、完了) 📋 ✅

- [x] 13 declaration を verbatim 確認 (`rg -n '@residual\(plan:wyner-ziv-discharge-moonshot-plan\)'`
  + 該当 docstring + signature 1-3 行を実コード Read)
- [x] load-bearing predicate hypothesis 列挙 (per declaration)
- [x] cross-family Relay 影響 verbatim 確認 (`RelayCFBinningBody.lean` 内
  `IsWynerZivBinningCovering` / `IsWynerZivBinningPacking` /
  `IsWynerZivBinningAchievable` 使用箇所 4 個所確認)
- [x] tier 5 defect 新規発見 0 件 (planner 段階)
- [x] `⚠ HONESTY ALERT` / `FALSE` 検出 0 件 (Pattern H)
- [x] 既存 `sorry` 計数: word-boundary `rg -nw 'sorry'` で 13 declaration 全てが
  body `sorry`、+ Round 1 Phase 2.1 / 2.2 で sorry 化された 4 declaration
  (`wyner_ziv_achievability_*`、`wyner_ziv_converse_*`) も合算で **17 sorry 既存**

**proof-log**: no (mechanical 在庫確認、interesting なし)。

### Phase 2.x.1 — signature 改変 (consumer 13 declaration の load-bearing predicate hyp 削除) 📋

各 sub-step 完了時、対象 file で `lake env lean` 0 errors 確認。signature 改変
が caller に drift を起こすため、各 file の commit 前に必ず `lake build
Common2026.Shannon.<改変 module>` で olean refresh (Pattern A)。

#### 2.x.1.a — WynerZivConverseChain.lean (6 件、境界判定 1 件)

- [ ] **2.x.1.a.1** `wyner_ziv_converse_chain` (line 154):
  - signature から `(h_perLetter : WZPerLetterBound ...)` / `(h_csiszar :
    CsiszarSumIdentity ...)` / `(h_jensen_antitone : WZJensenAntitone ...)` の
    3 hyp を削除。
  - explicit param `(wzPerLetterObjective : Fin n → ℝ)` も削除 (predicate 経由
    でしか使われない、削除後 unused になる)。`(D_arr : Fin n → ℝ)` も同様に
    予測 — verbatim 確認: `D_arr` は `WZJensenAntitone U P_XY d D D_arr` でのみ
    使用、`(D : ℝ)` だけが結論型で参照 → `D_arr` も削除。
  - body は `sorry` 維持。docstring 末尾の `@residual(plan:wyner-ziv-discharge-moonshot-plan)`
    は維持、docstring 散文に **「Phase 2.x.1 retreat — signature から
    load-bearing predicates (`WZPerLetterBound` / `CsiszarSumIdentity` /
    `WZJensenAntitone`) を削除し signature を honest 化。closure responsibility
    は引き続き discharge plan」** を追記。
- [ ] **2.x.1.a.2** `wyner_ziv_converse_chain_block` (line 177): 同上 3 hyp 削除、
  `wzPerLetterObjective` / `D_arr` 削除。`[MeasurableSpace γ]` / `WynerZivCode` 系
  引数 (`μ`, `dN`, `c`, `_h_dist`) は維持 (block-code 文脈の precondition、
  regularity 系)。
- [ ] **2.x.1.a.3** `wyner_ziv_converse_chain_composite` (line 472):
  - signature から `h_perLetter` + `h_jensen_antitone` の 2 件削除。
  - 3 ingredient (`h_perLetter_le_condMI : ∀ i, wzPerLetterObjective i ≤ condMI i`
    / `h_chain : ∑ condMI i ≤ block` / `h_fano : block ≤ Real.log (M : ℝ)`) は
    **境界判定** — 暫定で削除候補 (これらは sum-and-log inequalities = 各々が
    load-bearing claim)。auditor 判定後に再評価。
  - 暫定削除前提で `condMI` / `block` / `wzPerLetterObjective` / `D_arr` の
    explicit param も削除。残る引数: `(U)(P_XY)(d)(hn)(M)(D)` + 結論。
- [ ] **2.x.1.a.4** `wyner_ziv_converse_n_letter_chain` (line 503): 同
  `wyner_ziv_converse_chain_block` の 3 hyp + explicit param 群削除。
- [ ] **2.x.1.a.5** `wyner_ziv_converse_chain_existence` (line 557):
  - `h_chain_nletter` (= 結論を `∀ n M c, ...` 形で quantify した load-bearing
    bundle) を削除。
  - `(h_R_lt : R < wynerZivRatePmf U P_XY d D)` は **precondition (regularity)
    維持** — 結論型 `¬ ∃ N, ...` の前提条件であり、結論自体を bundling して
    いない。
  - 残る引数: `[MeasurableSpace γ](μ)(P_XY)(d)(D R)(h_R_lt)(dN)`。
- [x] ~~**2.x.1.a.6** `wyner_ziv_tendsto_chain` (line 611): **境界判定** — 暫定で
  signature 維持 (auditor 判定待ち)。Phase 2.x.4 audit-2 で「pure forwarder、
  `@residual` 不要、body は `le_antisymm h_chain_conv h_ach` に restoration」と
  判定されれば本 declaration は scope **外** に降格、本 Phase の Phase 2.x.1
  での改変なし。~~ → **2026-05-26 Round 4 closure 済 (判断ログ #2)**: 予想された
  「pure forwarder、body restoration」path が proof done として確定 (Tier 1
  `@audit:ok`、現 line `:656`)。本 Phase scope 外で確定。
- [ ] **2.x.1.a.7** Phase 2.x.1.a 完了時:
  ```bash
  lake build Common2026.Shannon.WynerZivConverseChain
  lake env lean Common2026/Shannon/WynerZivConverseChain.lean
  ```
  for dependent: `rg -l '(wyner_ziv_converse_chain|wyner_ziv_converse_chain_block|wyner_ziv_converse_chain_composite|wyner_ziv_converse_n_letter_chain|wyner_ziv_converse_chain_existence|wyner_ziv_tendsto_chain)' Common2026/Shannon/`
  で caller 列挙 → 各 file `lake env lean` 再 verify。

#### 2.x.1.b — WynerZivBinningCovering.lean (4 件、cross-family Relay 影響あり)

- [ ] **2.x.1.b.1** `wyner_ziv_binning_via_covering_packing` (line 268):
  - signature から `(h_cov : IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT)` /
    `(h_pack : IsWynerZivBinningPacking R₂ ε₂ μ Us Ys JT f_U)` 削除。
  - **caller drift 確実** (`RelayCFBinningBody.lean:348` で直接呼出)。Phase
    2.x.2 ripple で散文化 (Relay 側は本 plan scope 外、Relay sweep agent の責務)。
  - explicit param `(R₁ R₂ : ℝ)` も predicate 経由でしか使われない場合は削除。
    verbatim 確認要 — `ε₁` / `ε₂` は結論 `μ.real {...} ≤ ε₁ + ε₂` で使われる
    ため維持必須、`R₁` / `R₂` は predicate のみで使用 → 削除候補だが Relay
    caller との API 互換性のため **暫定維持** (implementer 判断、auditor 委任)。
- [ ] **2.x.1.b.2** `wynerZivBinningBody_of_covering_packing` (line 300):
  同 2 hyp 削除、`R₁` / `R₂` の維持/削除は **2.x.1.b.1 と同期**。
- [ ] **2.x.1.b.3** `wyner_ziv_binning_existence_of_covering_packing` (line 357):
  `h_asymp` 削除 (predicate を内部に含む大型 existence bundle)。
- [ ] **2.x.1.b.4** `wyner_ziv_binning_decoder_fail_of_achievable` (line 501):
  `h_ach : IsWynerZivBinningAchievable R₁ R₂ ε₁ ε₂ μ Us Ys JT f_U` 削除。
- [ ] **2.x.1.b.5** Phase 2.x.1.b 完了時:
  ```bash
  lake build Common2026.Shannon.WynerZivBinningCovering
  lake env lean Common2026/Shannon/WynerZivBinningCovering.lean
  ```
  cross-family caller (`RelayCFBinningBody.lean`) は本 plan scope 外 — touch
  しない。Relay 側 `lake env lean` で type drift 発生時は Phase 2.x.2 で散文
  対応 (declaration を maintaining、Relay 側 sweep agent が closure)。

#### 2.x.1.c — WynerZivCoveringBody.lean (1 件)

- [ ] **2.x.1.c.1** `wzCovering_feed_asymp` (line 424):
  - signature から `(h_cov : IsCoveringTypicalityHyp μ JT)` / `(h_pack :
    IsPackingExistenceHyp (γ := γ) μ JT)` 削除。
- [ ] **2.x.1.c.2** Phase 2.x.1.c 完了時:
  ```bash
  lake build Common2026.Shannon.WynerZivCoveringBody
  lake env lean Common2026/Shannon/WynerZivCoveringBody.lean
  ```

#### 2.x.1.d — WynerZivPackingBody.lean (1 件)

- [ ] **2.x.1.d.1** `wyner_ziv_packing_existence` (line 563):
  - signature から `h_asymp : ∀ ε > 0, ∃ N, ... ∧ IsPackingTypicalityHyp ... ∧
    (∀ f_U, IsPackingCollisionBoundHyp ...) ∧ ... ∧ (∀ _f_U,
    IsWynerZivBinningCovering R₁ ε₁ μ Us Ys (JT n)) ∧ ...` 削除。
  - `{R₁ R₂ : ℝ}` は `IsWynerZivBinningCovering` 経由 + `h_asymp` 内のみで使用
    のため削除候補だが、結論型に出現するか verbatim 再確認 (line 586-595 確認)
    — 結論型 `∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ M Us Ys f f_U, μ.real {...} ≤ ε` に
    `R₁` / `R₂` は出ない → 削除。残る引数: `[Nonempty β][Nonempty γ](μ)[IsProbabilityMeasure μ](JT)`。
- [ ] **2.x.1.d.2** Phase 2.x.1.d 完了時 `lake build` + `lake env lean` 同様。

#### 2.x.1.e — WynerZivBinningBody.lean (1 件、境界判定)

- [x] ~~**2.x.1.e.1** `wzAchievability_random_binning_body` (line 492): **境界判定**
  — 暫定で 2 hyp (`h_typ_prob` / `h_bin_prob`) 維持。本 Phase 2.x.1 では改変
  しない、Phase 2.x.4 audit-2 で「regularity-only、`@residual` 削除 + body
  constructive 復元」と判定されたら scope **外**、本 Phase 完了後の handoff §6
  A3 §2 直接編集に委譲。~~ → **2026-05-26 Round 4 closure 済 (判断ログ #2)**:
  予想された「regularity-only、body constructive 復元 = 4-line union-bound +
  add_le_add」path が proof done として確定 (Tier 1 `@audit:ok`、現 line `:493`)。
  本 Phase scope 外で確定。
- [x] ~~**2.x.1.e.2** 改変なしのため `lake env lean` 確認のみ (0 errors を維持)。~~ → 上記により不要。

**Phase 2.x.1 DoD**:
- 明確改変対象 11 declaration で load-bearing predicate hypothesis が signature
  から削除済、結論型は変えない、body は `sorry + @residual(plan:wyner-ziv-discharge-moonshot-plan)`
  維持
- ~~境界判定 2 件 (`wyner_ziv_tendsto_chain` + `wzAchievability_random_binning_body`)
  は暫定維持、Phase 2.x.4 audit-2 verdict 待ち~~ → 2026-05-26 Round 4 closure 済
  (両者 proof done 到達、判断ログ #2)、Phase scope 外確定
- 各 file `lake env lean` 0 errors、olean refresh 経由で dependent file 再 verify
  済

**proof-log**: yes (`docs/proof-logs/proof-log-wynerziv-phase2-predicate-removal-2.x.1.md`)。
理由: cross-family Relay caller drift の発生範囲 + auditor 委任した境界判定 2 件
の判断材料を残す。

### Phase 2.x.2 — ripple (caller drift handling) 📋

- [ ] **2.x.2.1** in-family caller 列挙:
  ```bash
  rg -l '(wyner_ziv_converse_chain|wyner_ziv_converse_chain_block|wyner_ziv_converse_chain_composite|wyner_ziv_converse_n_letter_chain|wyner_ziv_converse_chain_existence|wyner_ziv_tendsto_chain|wyner_ziv_binning_via_covering_packing|wynerZivBinningBody_of_covering_packing|wyner_ziv_binning_existence_of_covering_packing|wyner_ziv_binning_decoder_fail_of_achievable|wzCovering_feed_asymp|wyner_ziv_packing_existence|wzAchievability_random_binning_body)' Common2026/Shannon/
  ```
  予想 caller (Round 1 で部分的に既に sorry 化済): `WynerZivAchievabilityBridge.lean`
  / `WynerZivDischarge.lean` / `WynerZivDecoderFailureAssembly.lean` / `WynerZivConverseChain.lean`
  内部 caller / `WynerZivCoveringBody.lean:461` `wzCovering_decoder_fail_existence`
  (Round 1 で既に transitive sorry 散文付与済) 等。
- [ ] **2.x.2.2** 各 in-family caller について **既存 docstring 散文** に Phase
  2.x.1 retreat の追記 (Round 1 と同じ Pattern C 文言):
  ```
  Phase 2.x.1 ripple — upstream `<decl 名>` had its load-bearing predicate
  hypothesis (`<predicate 名 列挙>`) removed from its signature. The transitive
  `sorry` continues to be tracked by upstream's
  `@residual(plan:wyner-ziv-discharge-moonshot-plan)`. No new `@residual` is
  attached here — closure responsibility belongs to the upstream declaration.
  ```
  既に Round 1 で transitive sorry 散文を持つ declaration には Phase 2.x.1
  retreat 言及を 1 行追記するだけ (重複した `@residual` を追加しない)。
- [ ] **2.x.2.3** **cross-family caller (`RelayCFBinningBody.lean:348` + 他
  3 件 verify)** は本 plan で touch しない (Option A scope 確定)。Relay 側
  sweep agent が transitive sorry 散文付与を担当する旨を本 plan の判断ログに
  記録 + Relay 側 planner との handoff coordination は orchestrator に委任。
- [ ] **2.x.2.4** ripple 完了時、改変された全 file で `lake env lean` 再 verify
  (olean refresh は Phase 2.x.1 で済んでいる、それでも parent .olean 更新を
  確実にするため `lake build Common2026.Shannon.<改変 module>` を 1 度実行)。
- [ ] **2.x.2.5** cross-family file (`RelayCFBinningBody.lean` 等) で type drift
  が発生していないか `lake env lean Common2026/Shannon/RelayCFBinningBody.lean`
  で sanity check (Option A 設計上は drift は発生しないはず — predicate
  definition は維持しているため、Relay 側で `IsWynerZivBinningCovering R_cov
  ε_cov μ Ŷs Ys JT` を作って使う scheme は影響を受けない)。drift 発生時は
  Phase 2.x.4 audit verdict + L-PR-3 撤退ライン発動判断へ。

**Phase 2.x.2 DoD**:
- in-family caller 全件 docstring 散文に Phase 2.x.1 retreat 言及追記済
- cross-family file は untouched + `lake env lean` 0 errors 維持
- 各 file `lake env lean` 0 errors

**proof-log**: no (mechanical 散文追記)。

### Phase 2.x.3 — predicate definitions の deprecation 注記更新 📋

Phase 2.x.1 で consumer side から load-bearing predicate hypothesis が削除された
ため、predicate definition の `@audit:retract-candidate(load-bearing-predicate)`
注記を re-confirm + 「in-family consumer 0 件」を verbatim 追記:

| file:line | predicate | cross-family Relay? | Phase 2.x.3 後の docstring 更新 |
|---|---|---|---|
| `WynerZivConverse.lean:95` | `WZFanoConverseBound` | なし | 「in-family consumer 0 件 (Phase 2.x.1 で全削除)、Wyner–Ziv family 内で predicate deprecation 候補」を docstring 追記 |
| `WynerZivConverse.lean:121` | `WZCsiszarSumBound` | なし | 同上 |
| `WynerZivConverse.lean:131` | `WZRateCleanup` | なし | 同上 |
| `WynerZivConverseChain.lean:92` | `WZPerLetterBound` (structure) | なし | 同上 |
| `WynerZivConverseChain.lean:116` | `CsiszarSumIdentity` | なし | 同上 |
| `WynerZivConverseChain.lean:128` | `WZJensenAntitone` | なし | 同上 |
| `WynerZivBinningCovering.lean:98` | `IsWynerZivBinningCovering` | **あり** (`RelayCFBinningBody.lean:127` `Iff.rfl` 再公開 + `.mono` / `.rate_irrelevant` field accessor 利用) | 既存「Relay 再利用 — 削除前に Relay 側 incidental migration 必要」注記を維持 + 「Wyner–Ziv 側 in-family consumer 0 件 (Phase 2.x.1 retreat)」を追記 |
| `WynerZivBinningCovering.lean:172` | `IsWynerZivBinningPacking` | **あり** (`RelayCFBinningBody.lean:195` 同上) | 同上 |
| `WynerZivBinningCovering.lean:408` | `IsWynerZivBinningAchievable` | **あり** (`RelayCFBinningBody.lean:262` 同上) | 同上 |
| `WynerZivCoveringBody.lean:256` | `IsCoveringTypicalityHyp` | なし (`rg` で WynerZiv 外 0 件、Phase 2.x.3 で再確認) | 「in-family consumer 0 件、Wyner–Ziv family 内で predicate deprecation 候補」追記 |
| `WynerZivPackingBody.lean:102` | `IsPackingTypicalityHyp` | なし (要 `rg` 再確認) | 同上 |
| `WynerZivPackingBody.lean:119` | `IsPackingCollisionBoundHyp` | なし (要 `rg` 再確認) | 同上 |

- [ ] **2.x.3.1** 各 predicate definition の docstring 更新 (上表通り)。
- [ ] **2.x.3.2** cross-family なし predicate (9 件) の verbatim `rg` 確認:
  ```bash
  rg -n 'WZFanoConverseBound|WZCsiszarSumBound|WZRateCleanup|WZPerLetterBound|CsiszarSumIdentity|WZJensenAntitone|IsCoveringTypicalityHyp|IsPackingTypicalityHyp|IsPackingCollisionBoundHyp' Common2026/ | grep -v 'Common2026/Shannon/WynerZiv'
  ```
  これらが Common2026 内の WynerZiv 外で参照されていないこと確認 → 確認できた
  ら docstring に「in-family closed」と追記。万一 cross-family consumer
  発見時は対応 predicate の `@audit:retract-candidate` reason を「load-bearing-predicate」
  維持 + 散文に cross-family caller 列挙。
- [ ] **2.x.3.3** **deprecation 候補 9 件の実削除は本 plan scope 外**。次 family
  cleanup session (or 別 plan) に escalate (`@audit:retract-candidate(load-bearing-predicate)`
  + 「in-family consumer 0 件」注記が deprecate-ready state)。
- [ ] **2.x.3.4** Phase 2.x.3 完了時 `lake env lean` 全 file 再 verify、type
  drift なし (docstring 編集のみ)。

**Phase 2.x.3 DoD**:
- 12 predicate definition (cross-family 3 + family 内 9) の docstring 更新済、
  「in-family consumer 0 件 (Phase 2.x.1 retreat)」が明示
- 各 file `lake env lean` 0 errors

**proof-log**: no (mechanical docstring 編集)。

### Phase 2.x.4 — audit-2 (Phase 2.x.1 / 2.x.2 / 2.x.3 全件) 📋

- [ ] **2.x.4.1** orchestrator は `honesty-auditor` (or `general-purpose` +
  brief で `docs/audit/honesty-auditor-core.md` を SoT 指定) を起動。対象:
  - Phase 2.x.1: 11 件 (明確改変、signature honesty が strictly 上がったか
    auditor verify)
  - 境界判定 2 件 (`wyner_ziv_tendsto_chain` + `wzAchievability_random_binning_body`)
    の最終分類確定 (Round 1 Phase 1.6 plan 未決事項 2 と同じ判断軸を踏襲)
  - Phase 2.x.2 ripple 散文の vocabulary 整合 (即興 tag 不在確認、Pattern C)
  - Phase 2.x.3 predicate definition 注記の verbatim 整合 (cross-family Relay
    注記の正確性、in-family consumer 0 件 claim の verifiability)
- [ ] **2.x.4.2** verdict 受領 + 3 値判定:
  - **ok** → Phase V 着手
  - **questionable** → docstring refine or 追加コメントで対応、Phase V 進行
  - **defect** → 当該 declaration を撤回 / 修正 (signature 再改変 + sorry
    維持)、Phase V 進行前に解決
- [x] ~~**2.x.4.3** 境界判定 2 件の最終分類:~~ → **2026-05-26 Round 4 closure 済 (判断ログ #2)**: 両者 Tier 1 `@audit:ok` 到達 (proof done)、scope 外で確定。
  - ~~`wyner_ziv_tendsto_chain`: auditor が「pure forwarder、`@residual` 不要、
    body restoration 推奨」と判定 → 本 declaration を scope 外 (handoff §6
    A3 §2 で既に restoration 計画あり) として記録、`@residual` 削除 +
    `le_antisymm h_chain_conv h_ach` body restoration は handoff direct edit に
    委譲。本 plan 完了時点では `sorry` + `@residual` 維持。~~ → 想定 path 実施済、`@audit:ok` 付与。
  - ~~`wzAchievability_random_binning_body`: 同様に auditor 判定で scope 外
    降格 + handoff §6 A3 §2 への委譲を確認。~~ → 想定 path 実施済、`@audit:ok` 付与。

**proof-log**: yes (`docs/proof-logs/proof-log-wynerziv-phase2-predicate-removal-2.x.4.md`)。
理由: auditor verdict + 境界判定 2 件の最終分類 + cross-family Relay 注記の
verbatim 検証結果。

### Phase V — verify + 集約 + 親 plan banner 更新 📋

- [ ] **V.1** 全 WynerZiv*.lean file で `lake env lean` 確認:
  ```bash
  for f in Common2026/Shannon/WynerZiv*.lean; do
    echo "=== $f ==="
    lake env lean "$f"
  done
  ```
  signature 改変 file は事前 `lake build Common2026.Shannon.WynerZiv...` で
  olean refresh (Phase 2.x.1 / 2.x.2 で個別実施済、最終確認のため再実行)。
- [ ] **V.2** cross-family sanity check:
  ```bash
  lake env lean Common2026/Shannon/RelayCFBinningBody.lean
  lake env lean Common2026/Shannon/RelayInnerBodyDischarge.lean
  ```
  Option A scope では untouched + 0 errors 維持が期待値。drift 発生時は
  L-PR-3 撤退ライン発動 (本 plan を完了せず Relay sweep agent との統合判断へ
  pause)。
- [ ] **V.3** 集計コマンド実行:
  ```bash
  rg -c '@residual\(plan:wyner-ziv-discharge-moonshot-plan\)' Common2026/Shannon/WynerZiv*.lean | awk -F: '{s+=$2} END {print "residual(plan):", s}'
  # 期待値: ~15 (Round 1 と同等、signature 改変では @residual 件数不変)
  rg -c '@audit:retract-candidate\(load-bearing-predicate\)' Common2026/Shannon/WynerZiv*.lean | awk -F: '{s+=$2} END {print "retract-candidate:", s}'
  # 期待値: 12 (Round 1 と同等、docstring 注記更新のみ)
  rg -nw 'sorry' Common2026/Shannon/WynerZiv*.lean | wc -l
  # 期待値: ~17 (Round 1 と同等、signature 改変は sorry 件数を増減させない)
  rg -nw 'WZPerLetterBound|CsiszarSumIdentity|WZJensenAntitone|WZFanoConverseBound|WZCsiszarSumBound|WZRateCleanup|IsCoveringTypicalityHyp|IsPackingTypicalityHyp|IsPackingCollisionBoundHyp' Common2026/Shannon/WynerZiv*.lean | grep -v 'def \|structure \|/--\|`@audit:' | wc -l
  # 期待値: 0 (in-family consumer 0 件、predicate signature 上の使用消滅) — 但し
  # IsWynerZivBinning{Covering,Packing,Achievable} は Relay 側で残るので
  # WynerZiv*.lean 内では 0 件 (Phase 2.x.1 後)
  ```
- [ ] **V.4** 親 plan `wyner-ziv-moonshot-plan.md` の banner 更新:
  「Phase 2.x predicate removal 完了 (`docs/shannon/wynerziv-phase2-predicate-removal-plan.md`
  参照)、Round 1 で sorry 化済の 13 declaration の signature から load-bearing
  predicate hypothesis を構造的に除去。Phase 0-D の pass-through 設計は変更
  なし、cross-family Relay 利用 3 predicate (`IsWynerZivBinning{Covering,Packing,Achievable}`)
  の definition 自体は維持」を追記。
- [ ] **V.5** Pilot 知見の handoff 反映 (`.claude/handoff-sorry-migration.md`
  Active orchestration log + Next phase に追記):
  - signature 改変による olean refresh の必須性は Round 1 と同等の頻度 (Pattern A)
  - cross-family Relay 保護は Round 1 設計を継続成功 (Option A scope の妥当性)
  - 境界判定 2 件は handoff §6 A3 §2 への委譲が前提

## 撤退ライン

- **L-PR-1 (境界判定 2 件が auditor verdict で逆方向に動く)**: ~~`wyner_ziv_tendsto_chain`
  / `wzAchievability_random_binning_body` について auditor が「2 hyp とも
  load-bearing、signature 改変必要」と判定 → 本 Phase 2.x.1 に追加 sub-step を
  発生させて 2 declaration の signature 改変も実施 (新規 sorry なし、既存
  sorry 維持で hyp 削除のみ)。逆判定 (「regularity-only、scope 外 + body
  restoration」) は Round 1 plan 未決事項 2 と handoff §6 A3 §2 の前提どおり
  scope 外に降格 (本 plan 完了範囲は 11 declaration、+ 2 件は scope 外で別途
  direct edit)。~~ → **2026-05-26 Round 4 closure 済 (判断ログ #2)**: 逆判定 path
  (「regularity-only / pure forwarder、scope 外 + body restoration」) が実施済 +
  proof done 到達。撤退ライン消化、追加 sub-step 不要。
- **L-PR-2 (cross-family Relay caller drift が予想外に発生)**: Phase 2.x.2 ripple
  で `RelayCFBinningBody.lean` 等の cross-family file が `lake env lean` で type
  error → Option A scope 内で対応不可能なら Phase 2.x.4 audit-2 verdict 待ちで
  pause、Relay sweep agent と統合判断 (Option B scope 移行)。本 plan は Phase
  2.x.1 完了 + Phase 2.x.2/2.x.3/V を pause で commit。
- **L-PR-3 (Relay planner が Round 2 で `IsWynerZivBinning*` 削除を要求)**: 並列
  Relay planner との衝突 — 並列起動の Relay planner が同 session で
  `IsWynerZivBinning*` 3 predicate を「Relay 側 sweep で削除候補」と判定した
  場合 (例: Relay 側で Wyner–Ziv namespace 依存を解消する独自 closure を提案)、
  本 Phase 2.x の Option A scope は collision → 統合判断のため pause。
  orchestrator が両 planner output (本 plan + Relay plan) の Approach 段階で
  衝突解消方針を escalate decision、本 plan は Phase 2.x.1 / 2.x.2 completion
  範囲を切り出して partial commit。
- **L-PR-4 (Approach 変更: pilot scope 縮減)**: Phase 2.x.1 sub-step (6 file 13
  declaration) が 1-2 session で完走しない / honesty-auditor が DEFECT を多発
  させる場合、`WynerZivConverseChain.lean` の 6 件のみで本 plan を close し、
  `WynerZivBinningCovering` / `WynerZivCoveringBody` / `WynerZivPackingBody` /
  `WynerZivBinningBody` の 5+2 件は後続 session に分離 (Round 1 plan L-MIG-4
  相当)。

## 未決事項

planner が判断つかない事項を列挙。実装 / auditor 委任で済む項目は明記。

1. **`wyner_ziv_converse_chain_composite` (line 472) の 3 ingredient (`h_perLetter_le_condMI`
   / `h_chain` / `h_fano`) の load-bearing 判定** (auditor 判定対象):
   3 件とも sum-and-log inequalities = 各々が load-bearing claim と planner は
   暫定判定 (削除推奨)。但し `h_chain : ∑ i, condMI i ≤ block` は条件付き MI
   chain rule の **statement-level identity** (Csiszár sum identity の n-letter
   chain rule) なので、Mathlib 整備があれば genuinely derived 可能 — load-bearing
   ではなく **未整備な Mathlib bridge** の可能性。auditor 判定対象。auditor が
   「Mathlib 整備可能、load-bearing claim ではない」と判定したら本 Phase で
   signature 維持、未整備 wall として `@residual(wall:csiszar-sum)` の新規
   wall name register 拡張 PR を別途検討。

2. ~~**`wyner_ziv_tendsto_chain` (line 611) の境界判定** (auditor 判定対象):
   Round 1 plan 未決事項 2 と同じ判断軸。`(h_ach : ≤) (h_chain_conv : ≤) : =`
   は `le_antisymm` 1 行で構造的に正当な合成 → auditor が「pure forwarder、
   `@residual` 削除推奨、body は `le_antisymm h_chain_conv h_ach` に restoration」
   と判定する高い可能性。本 Phase 2.x.1 では暫定維持、Phase 2.x.4 audit-2
   verdict で確定、scope 外降格時は handoff §6 A3 §1 direct edit に委譲 (handoff
   既存項目)。~~ → **2026-05-26 Round 4 closure 済 (判断ログ #2)**: 予想 path 実施
   + Tier 1 `@audit:ok` 到達 (現 line `:656`)。

3. ~~**`wzAchievability_random_binning_body` (line 492) の境界判定** (auditor 判定
   対象): Round 1 Phase 1.5 boundary case 注記 + Round 1 plan 未決事項 2 を
   継承。`h_typ_prob` / `h_bin_prob` は `μ.real (...) ≤ ε` 形 probability bound
   = regularity 寄り。auditor 判定で scope 外降格 + body constructive 復元
   (4-line union-bound + `add_le_add`) が handoff §6 A3 §2 既知計画。本 Phase
   は暫定維持、Phase 2.x.4 verdict 経由で handoff direct edit 連携。~~ →
   **2026-05-26 Round 4 closure 済 (判断ログ #2)**: 予想 path 実施 + Tier 1
   `@audit:ok` 到達 (現 line `:493`)。

4. **cross-family Relay sweep agent との同 session coordination** (orchestrator
   判断対象): 並列起動中の Relay planner が本 plan と同じ session で起草中。
   Relay planner が Option B scope (両 family 統合 plan 化) を提案した場合の
   handling は orchestrator 側で escalate decision。本 plan は Option A scope
   採用前提で Approach 起草、L-PR-3 撤退ラインで pause 設計済 — orchestrator
   が両 plan の Approach を Comparing 後 Option A 維持 or Option B 統合の判断
   を実施。

5. **`wyner_ziv_converse_chain_composite` (line 472) の `condMI` / `block` /
   `wzPerLetterObjective` / `D_arr` explicit param 削除可否** (implementer 判断
   + auditor 委任): 3 ingredient hyp を削除すると、explicit param `(condMI :
   Fin n → ℝ)` / `(block : ℝ)` も unused に。削除推奨だが、結論型の
   `wynerZivRatePmf U P_XY d D ≤ Real.log (M : ℝ) / (n : ℝ)` で参照されない場合
   削除、参照されていれば維持。verbatim 確認 (line 484 結論型) で `M` / `D` /
   `n` のみ参照 → 全 explicit param 削除可能 — implementer が verbatim 確認
   後実施。

6. **proof done を本 plan で目指さない方針の明示確認** (user 確認):
   本 plan の DoD は **type-check done** のみ。Wyner–Ziv 系の analytical
   closure (Csiszár sum identity / `R_WZ(D)` 凸性 / 三項 typicality + AEP /
   chain rule for conditional MI) は **未着手のまま** で本 plan は close する。
   `wyner-ziv-moonshot-plan.md` の Phase D pass-through 状態 +
   `wyner-ziv-discharge-moonshot-plan` / `wyner-ziv-convexity-discharge-*` の
   defer 状態を変えない。Round 1 plan 未決事項 4 と同じ確認。

## 判断ログ

書く頻度: 方針変更 / 撤退ライン発動 / 当初仮定の修正があったとき。append-only。

1. **2026-05-25 plan 起草 (Round 2 + WynerZiv Phase 2.x parallel session)**:
   lean-planner (本 session、docs-only) が Round 1 完了後の 13 declaration の
   load-bearing predicate residue を verbatim 読込で per-declaration 分類:
   - WynerZivConverseChain 6 件 (chain assembly の WZ namespace predicate
     consumer) — 構造的に signature 改変対象、境界判定 1 件
     (`wyner_ziv_tendsto_chain`)
   - WynerZivBinningCovering 4 件 (cross-family Relay 利用 predicate consumer)
     — `IsWynerZivBinning{Covering,Packing,Achievable}` 3 predicate definition
     は cross-family のため Phase 2.x.3 で削除しない、Option A scope 確定
   - WynerZivCoveringBody / PackingBody 2 件 (family 内 predicate consumer)
   - WynerZivBinningBody 1 件 (境界判定、Round 1 から継承)
   - **scope option A 採用**: Relay 側 re-namespacing を許容 + WynerZiv 側
     consumer signature のみ改変。根拠は Approach §「Scope 選択 — Option A
     採用」参照。
   - **cross-family Relay 衝突 4 件**: `wyner_ziv_binning_via_covering_packing`
     直接呼出 (`RelayCFBinningBody.lean:348`) + 3 predicate re-namespacing
     (`:127/195/262`) は本 plan touch 外、Phase 2.x.2 ripple で Relay 側 sweep
     agent 責務として明示。
   - **⚠ HONESTY ALERT / FALSE 検出 0 件** (Pattern H 該当なし、planner 段階)
   - **wall name register 拡張提案 0 件** (新規 sorry なし、新規 Mathlib 壁
     identification は本 plan scope 外)
   - **新規 tier 5 defect 発見 0 件** (Round 1 で 3 件は scope 外明示済)
   - 未決事項 6 件 (auditor 委任 3 件 + orchestrator coordination 1 件 +
     implementer 判断 1 件 + user 確認 1 件)
   - 撤退ライン 4 件 (L-PR-1 / L-PR-2 / L-PR-3 / L-PR-4)

2. **2026-05-26 Round 4 closure (境界判定 2 件 proof done 到達 / Phase scope 確定)**:
   Round 4 sweep 完了後の状態確認で、本 plan で「境界判定 (auditor 委任) / 暫定
   維持 / Phase 2.x.4 verdict 待ち」と設定した 2 declaration の現状を
   `Common2026/Shannon/WynerZivConverseChain.lean:656` +
   `Common2026/Shannon/WynerZivBinningBody.lean:493` で verbatim 確認:
   - **`wyner_ziv_tendsto_chain`** (line `:611` → 現 `:656`): body
     `le_antisymm h_chain_conv h_ach` で proof done、Tier 1 `@audit:ok` 付与済
     (`@audit:ok` docstring: 「No `sorry`, no `@residual`. Genuine 0/0 proof done.」)。
     L-PR-1 / 未決事項 2 で予想した「pure forwarder、`@residual` 削除、body
     restoration」path が実施済。
   - **`wzAchievability_random_binning_body`** (line `:492` → 現 `:493`): body
     4-line calc block (`wzAchievability_decoder_fail_le` + `add_le_add`
     composition) で proof done、Tier 1 `@audit:ok` 付与済 (`@audit:ok`
     docstring: 「The hyps do not bundle the conclusion — they supply the
     per-set bounds that get added; the lemma's content is the subadditivity
     composition. No `sorry`, no `@residual`. Genuine 0/0 proof done.」)。
     L-PR-1 / 未決事項 3 で予想した「regularity-only、body constructive 復元 =
     4-line union-bound + add_le_add restoration」path が実施済。
   - 影響:
     - Phase 2.x.1.a.6 (`wyner_ziv_tendsto_chain`) と Phase 2.x.1.e.1-2
       (`wzAchievability_random_binning_body`) を closed mark
     - 集計の「境界判定 (auditor 委任) 2 件」→ 0 件、本 plan の実 scope = 明確
       改変対象 11 declaration のみで確定
     - L-PR-1 撤退ライン消化、未決事項 2 / 3 closure
     - Phase 2.x.4 audit-2 の判定対象から境界判定 2 件を除外
     - 本 plan の in-flight tracker から両 declaration を除外

<!-- 後続セッションで判断変更があれば下記に追記 (append-only):
3. **YYYY-MM-DD <要点>**: <変更理由 + 撤退ラインへの紐付け>。
-->
