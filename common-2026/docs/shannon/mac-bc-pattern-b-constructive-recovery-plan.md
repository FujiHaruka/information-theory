# Shannon: MAC-BC Pattern B constructive recovery サブ計画

> **Parent**: [`mac-bc-sorry-migration-plan.md`](mac-bc-sorry-migration-plan.md) Round 2 残課題 follow-up
> **由来**: `.claude/handoff-sorry-migration.md`「Round 2 残課題 follow-up closure 状況」表の最終未対応行 (signature rewrite と独立した別アプローチ、Round 4 escalate #1〜#7 と並走)
> **Pattern B 出典**: `docs/audit/sorry-migration-runbook.md`「Pattern B — planner 全件 sorry 指示の overcorrect」+ Chernoff 前例 (`docs/shannon/chernoff-sorry-migration-plan.md` L497-521 inventory 表で「constructive recovery 候補は 0 件」と判定された対照例)

## 進捗

- [ ] Phase 0 — 規模見積もり + verbatim 確認 + Pattern B 適用可能性判定 📋
- [ ] Phase 1 — `mac_capacity_region_outer_bound_three_bounds` constructive recovery 📋
- [ ] Phase 2 — `bc_capacity_region_outer_bound_corner_limit` constructive recovery 📋
- [ ] Phase V — verify + audit (proof done 到達なら `@audit:ok`、不到達なら `@residual` 維持で stable) 📋

## ゴール / Approach

`mac-bc-sorry-migration-plan` Phase 2.1 で sorry 化された 2 declaration を、**Round 2 で signature rewrite が完遂した近傍 declaration (`bc_common_rate_bound` / `bc_private_rate_bound` / `bc_capacity_region_outer_bound`、Wave 6-BC `f0d51e4`) で既に揃った constructive 部品**を呼び出すだけで Tier 1 (proof done + `@audit:ok`) に押し上げる。新規 wall promotion / signature 改変 / hypothesis 追加は一切なし。

**観察**: 両 declaration の sorry body は signature の hyp の **直接組合せだけで closure 可能** な形に既になっている。

- MAC `_three_bounds` の結論型 `InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth` は同 file `mac_region_combine` (`:517`) で `⟨h₁, h₂, hs⟩` 直接構築 → ⋆ 1 行で proof done。
- BC `_corner_limit` の結論型 `InBCCapacityRegion R₁ R₂ I_u I_xy` は同 file `bc_capacity_region_outer_bound` (`:618`、Round 2 Wave 6 で proof done 化済) で `InBCCapacityRegion R₁ R₂ (I_u+ε) (I_xy+ε)` を得て、`ε ≤ 0` を `linarith` で transitive 適用 → ⋆ MAC peer `mac_capacity_region_outer_bound_corner_limit` (`:602`) と完全に同型 body で proof done。

**ゆえに本 sweep は両 declaration とも Pattern B 適用可、proof done 到達 2 件、残置 sorry 0 件、新規 wall 0 件**。Phase 0 verbatim 確認で前提が崩れた場合のみ Phase 1/2 を skip して `@residual(plan:mac-bc-sorry-migration-plan)` 維持で stable (撤退ライン L-PB-1/L-PB-2)。

### Chernoff plan Pattern B 前例との対比

Chernoff sweep (`chernoff-sorry-migration-plan.md` L497-521) では **19 declaration 全件が constructive recovery 不可** と判定された。理由は全て結論型が `limsup rate ≤ -log Z(λ)` / `Tendsto rate atTop ...` といった **load-bearing claim** であり、肝心の rate inequality を hypothesis として inject しないと closure 不可能だったため。本 sweep の 2 declaration は逆で、結論型が `InMACCapacityRegion` / `InBCCapacityRegion` という **2-3 不等式を bundling した structure**、入力 hyp が **その不等式そのもの** (`h₁ : R₁ ≤ I₁` 等) または **その不等式と 1 つの `linarith` で接続可能なもの** (`bc_capacity_region_outer_bound` 戻り + `ε ≤ 0`)。Hoeffding pilot で `isHoeffdingMinimizerFullSupport_of_lagrange` が「結論型 `∀ a, 0 < · a` を `hoeffdingTilt_pos` で純構成 closure」した状況と同型 — **結論型を構築するための部品が既に in-tree に揃っている**。

## Phase 0 — 規模見積もり + Pattern B 適用可能性判定 📋

**Sub-step**:

- [ ] **0.1** 両 declaration の verbatim 確認 (本 plan の冒頭 §「verbatim signature + body」転記済、Phase 0 実施時は実コードと再照合)
  - `Common2026/Shannon/MultipleAccessChannel.lean:645-651` (`mac_capacity_region_outer_bound_three_bounds`、`sorry` body)
  - `Common2026/Shannon/BroadcastChannel.lean:640-652` (`bc_capacity_region_outer_bound_corner_limit`、`sorry` body)
- [ ] **0.2** 必要部品 (Pattern B 適用後 body の依存先) の verbatim 確認:
  - `mac_region_combine` (`MultipleAccessChannel.lean:517`、`@residual` なし = 既に proof done)
  - `bc_capacity_region_outer_bound` (`BroadcastChannel.lean:618`、Wave 6 で proof done 化済 + Wave 7 で `@audit:ok` 付与)
  - `mac_capacity_region_outer_bound_corner_limit` (`MultipleAccessChannel.lean:602`、template、`@residual` なし)
  - `InBCCapacityRegion.bound_R₂_le_I_u` / `bound_R₁_le_I_xy` (`BroadcastChannel.lean:351-353` field accessors)
- [ ] **0.3** Pattern B 適用可能性 inline 判定 (前提崩れ flag):
  - MAC `_three_bounds`: 結論型 `InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth` の constructor は `⟨bound₁, bound₂, boundSum⟩` で 3 引数 = `(h₁, h₂, hs)`。**型完全一致** で `mac_region_combine R₁ R₂ I₁ I₂ Iboth h₁ h₂ hs` または直接 `⟨h₁, h₂, hs⟩` で closure 可能。
  - BC `_corner_limit`: signature の `h_fano₂ / h_cond_fano₁ / h_chain_u / h_chain_xy / h_cleanup₂ / h_cleanup₁` を `bc_capacity_region_outer_bound hn c R₁ R₂ Pe₂ Pe₁ I_marg_u I_marg_xy I_u I_xy ε _ _ _ _ _ _` に渡すと `InBCCapacityRegion R₁ R₂ (I_u + ε) (I_xy + ε)` を得る。`ε ≤ 0` から `I_u + ε ≤ I_u` / `I_xy + ε ≤ I_xy` が `linarith` で出るので `⟨_.bound_R₂_le_I_u.trans (by linarith), _.bound_R₁_le_I_xy.trans (by linarith)⟩` で `InBCCapacityRegion R₁ R₂ I_u I_xy` を構築。**MAC peer `mac_capacity_region_outer_bound_corner_limit` body と同型** (verbatim 確認済、`:619-625` の `h.bound₁.trans (by linarith)` 等)。
- [ ] **0.4** 親 plan (`mac-bc-sorry-migration-plan.md`) の在庫表 L343 (`_three_bounds`、Phase 2.1 sweep 済) と L400 (`_corner_limit`、Phase 2.2 sweep 済) で本 declaration が「auditor 委任」「P (transitive wrapper)」と分類されていることを確認。本 sweep は親 plan の auditor 委任結論 = **constructive で closure 可能 ↔ load-bearing precondition ではない** を Pattern B 実装で確定させる役割。

`proof-log: yes` (Phase 0 で `docs/proof-log-mac-bc-pattern-b-<date>.md` 起票、Phase V で archive)

## Phase 1 — MAC `_three_bounds` constructive recovery 📋

**対象**: `Common2026/Shannon/MultipleAccessChannel.lean:645-651`

**現状 body** (verbatim):

```lean
theorem mac_capacity_region_outer_bound_three_bounds
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (h₁ : R₁ ≤ I₁) (h₂ : R₂ ≤ I₂) (hs : R₁ + R₂ ≤ Iboth) :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth := by
  sorry
```

**Pattern B 適用後の body** (skeleton):

```lean
theorem mac_capacity_region_outer_bound_three_bounds
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (h₁ : R₁ ≤ I₁) (h₂ : R₂ ≤ I₂) (hs : R₁ + R₂ ≤ Iboth) :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth :=
  mac_region_combine R₁ R₂ I₁ I₂ Iboth h₁ h₂ hs
```

または `⟨h₁, h₂, hs⟩` (anonymous constructor) で同等。前者は他 declaration (`mac_capacity_region_outer_bound` body の `mac_region_combine R₁ R₂ ...` 適用) と語彙統一する利点があるので **前者を採用**。

**Sub-step**:

- [ ] **1.1** signature 維持で body を `mac_region_combine R₁ R₂ I₁ I₂ Iboth h₁ h₂ hs` に置換。
- [ ] **1.2** docstring 末尾の `@residual(plan:mac-bc-sorry-migration-plan)` 行を削除 (Pattern B closure で `@residual` 不要、Phase V で `@audit:ok` 付与候補)。
- [ ] **1.3** docstring 散文に「Pattern B constructive recovery via `mac_region_combine`」の 1 行 trail を追加 (Wave 7 BC audit `@audit:ok` 散文と同体裁、`docs/shannon/mac-bc-pattern-b-constructive-recovery-plan` への back-reference)。
- [ ] **1.4** `lake env lean Common2026/Shannon/MultipleAccessChannel.lean` で 0 errors + `sorry` 警告消失を確認。

**撤退ライン**:

- **L-PB-1-MAC**: `mac_region_combine` の signature が `(R₁ R₂ I₁ I₂ Iboth : ℝ) (h₁ : R₁ ≤ I₁) (h₂ : R₂ ≤ I₂) (hs : R₁ + R₂ ≤ Iboth) : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth` であることを Phase 0.2 で verbatim 確認済。万一 implicit / 引数順 / instance 引数が想定と異なれば、anonymous constructor `⟨h₁, h₂, hs⟩` に降格 (Pattern B 適用は維持)。
- **L-PB-2-MAC**: `InMACCapacityRegion` 構造が field 順 `bound₁, bound₂, boundSum` (verbatim 確認、`:292-298`) と一致しているので anonymous constructor も成功するはず。両者とも fail なら **Pattern B 路線不採用** で `@residual(plan:mac-bc-sorry-migration-plan)` 維持 (現状から後退なし)。

## Phase 2 — BC `_corner_limit` constructive recovery 📋

**対象**: `Common2026/Shannon/BroadcastChannel.lean:640-652`

**現状 body** (verbatim):

```lean
theorem bc_capacity_region_outer_bound_corner_limit
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (R₁ R₂ Pe₂ Pe₁ I_marg_u I_marg_xy I_u I_xy ε : ℝ)
    (h_fano₂ : (n : ℝ) * R₂ ≤ I_marg_u + 1 + Pe₂ * Real.log (M₂ : ℝ))
    (h_cond_fano₁ : (n : ℝ) * R₁ ≤ I_marg_xy + 1 + Pe₁ * Real.log (M₁ : ℝ))
    (h_chain_u : I_marg_u ≤ (n : ℝ) * I_u)
    (h_chain_xy : I_marg_xy ≤ (n : ℝ) * I_xy)
    (h_cleanup₂ : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup₁ : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε)
    (h_ε : ε ≤ 0) :
    InBCCapacityRegion R₁ R₂ I_u I_xy := by
  sorry
```

**Pattern B 適用後の body** (skeleton、MAC peer L619-625 と同型):

```lean
theorem bc_capacity_region_outer_bound_corner_limit
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (R₁ R₂ Pe₂ Pe₁ I_marg_u I_marg_xy I_u I_xy ε : ℝ)
    (h_fano₂ : ...)
    (h_cond_fano₁ : ...)
    (h_chain_u : ...) (h_chain_xy : ...)
    (h_cleanup₂ : ...) (h_cleanup₁ : ...)
    (h_ε : ε ≤ 0) :
    InBCCapacityRegion R₁ R₂ I_u I_xy := by
  have h := bc_capacity_region_outer_bound hn c R₁ R₂ Pe₂ Pe₁
    I_marg_u I_marg_xy I_u I_xy ε
    h_fano₂ h_cond_fano₁ h_chain_u h_chain_xy h_cleanup₂ h_cleanup₁
  exact ⟨h.bound_R₂_le_I_u.trans (by linarith),
         h.bound_R₁_le_I_xy.trans (by linarith)⟩
```

(MAC peer `mac_capacity_region_outer_bound_corner_limit` の L620-625 body と完全に同型。MAC は 3 cut bound なので `⟨_, _, _⟩` 3 引数、BC は 2 cut bound なので `⟨_, _⟩` 2 引数。`InBCCapacityRegion` field 名 `bound_R₂_le_I_u` / `bound_R₁_le_I_xy` は verbatim 確認済 = `BroadcastChannel.lean:351-353`.)

**Sub-step**:

- [ ] **2.1** signature 維持で body を上記 `have h := bc_capacity_region_outer_bound ...` + `exact ⟨..., ...⟩` に置換。
- [ ] **2.2** docstring 末尾の `@residual(plan:mac-bc-sorry-migration-plan)` 行を削除。
- [ ] **2.3** docstring 散文に「Pattern B constructive recovery via `bc_capacity_region_outer_bound` + `ε ≤ 0` corner limit、MAC peer `mac_capacity_region_outer_bound_corner_limit` body と同型」trail を追加。
- [ ] **2.4** `lake env lean Common2026/Shannon/BroadcastChannel.lean` で 0 errors + `sorry` 警告消失を確認。

**撤退ライン**:

- **L-PB-1-BC**: `bc_capacity_region_outer_bound` (`:618`) の signature/引数順が想定と異なる場合 (Phase 0.2 で verbatim 確認済、Wave 6 で proof done 化済、Wave 7 で `@audit:ok` 付与済なので想定外発生確率は低)。fail 時は MAC peer (`mac_capacity_region_outer_bound` + `_corner_limit`) body の coding style を再確認、差分を吸収。
- **L-PB-2-BC**: `InBCCapacityRegion` field accessor `bound_R₂_le_I_u` / `bound_R₁_le_I_xy` が `:351-353` のとおり anonymous constructor `⟨_, _⟩` 2 引数 (Mathlib convention) と整合しているはず。verbatim 確認済。
- **L-PB-3-BC**: `linarith` が `I_u + ε ≤ I_u` を `h_ε : ε ≤ 0` から解けないケース (Real 線形不等式、確実に解ける)、または `bc_capacity_region_outer_bound` 戻り型が `InBCCapacityRegion ... (I_u + ε) (I_xy + ε)` でなく予期せぬ別形 (verbatim L628 で確認、想定一致)。fail 時は **Pattern B 路線不採用** で `@residual(plan:mac-bc-sorry-migration-plan)` 維持。

## Phase V — verify + honesty audit 📋

- [ ] **V.1** `lake env lean Common2026/Shannon/MultipleAccessChannel.lean` + `lake env lean Common2026/Shannon/BroadcastChannel.lean` 0 errors、新規 `sorry` 警告 0 件 (両 file の他 declaration の既存 sorry はそのまま、本 plan scope 外)。
- [ ] **V.2** `rg -n '@residual|@audit:' Common2026/Shannon/MultipleAccessChannel.lean Common2026/Shannon/BroadcastChannel.lean` で本 2 declaration から `@residual` 消失を確認。
- [ ] **V.3** 独立 `honesty-auditor` (or `general-purpose` CORE 内蔵 prompt) を 1 件 dispatch:
  - 入力: 2 declaration の `file:line` + 親 plan + 本 plan path + commit hash
  - 監査スコープ: (a) Pattern B constructive recovery body が genuine か (循環 `:= h` でないか、`*Hypothesis` 核 bundling でないか、退化定義悪用でないか)、(b) MAC `_three_bounds` の `h₁ / h₂ / hs` は **precondition** か **load-bearing claim** か (= 結論 `InMACCapacityRegion` を構築する **constructor の構成要素** であり、Mathlib 結論型を再パッケージする pass-through、load-bearing claim とは異なる ↔ Chernoff plan の `limsup rate ≤ -log Z(λ)` 型と対比して honest 判断)
  - 期待 verdict: **全 OK → `@audit:ok` 付与** (Wave 6-BC `f0d51e4` の `bc_common_rate_bound` / `bc_private_rate_bound` Tier 1 到達と同パターン)
- [ ] **V.4** 親 plan `mac-bc-sorry-migration-plan.md` の進捗 banner / Round 2 残課題行を update:
  - `.claude/handoff-sorry-migration.md` Section D の「`mac_capacity_region_outer_bound_three_bounds` + `bc_capacity_region_outer_bound_corner_limit` Pattern B constructive recovery」行を **完了** に切替 (orchestrator 側で実施)
  - `mac-bc-sorry-migration-plan.md` 在庫表 L343 / L400 に「Phase 2.1 (auditor 委任) → Pattern B constructive recovery で proof done 到達」append 1 行 (orchestrator 側で実施)
- [ ] **V.5** proof-log `docs/proof-log-mac-bc-pattern-b-<date>.md` を archive (Phase 0 で起票したものを finalize)。

### Verdict matrix (Phase V 完了時の最終状態予測)

| declaration | Phase V 完了後 expected state | tier |
|---|---|---|
| `mac_capacity_region_outer_bound_three_bounds` | 0 sorry + 0 `@residual` + `@audit:ok` | Tier 1 (proof done) |
| `bc_capacity_region_outer_bound_corner_limit` | 0 sorry + 0 `@residual` + `@audit:ok` | Tier 1 (proof done) |

**中央予測**: proof done 到達件数 **2**、残置 sorry **0**、新規 wall promote **0**、Round 2 残課題 5 行中 4 行 closure (本 plan 完了 + Wave 5-7 closure)。

### 後続 (本 plan 完了後)

- `.claude/handoff-sorry-migration.md` Section D 残 1 行 (`WynerZiv `wyner_ziv_tendsto_chain` + `wzAchievability_random_binning_body` plan tracker 外し`) は別 docs-only task。Pattern B とは独立。
- 新規候補 (handoff Section D 末尾) `mac_rate_le_of_fano` kernel 整備で MAC peer 3 件 proof done 化 は別 plan (T3-B follow-up) の対象、本 sweep には含めない。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!--
例:
1. **Phase 0.3 で MAC `_three_bounds` の signature が想定と差異あり**: …。Pattern B 適用先を `mac_region_combine` から `⟨h₁, h₂, hs⟩` anonymous constructor に切替。
2. **Phase 2 の L-PB-3-BC 発火**: linarith が `I_u + ε ≤ I_u` を解けず、Phase 2 を skip、`@residual(plan:mac-bc-sorry-migration-plan)` 維持で stable。
-->
