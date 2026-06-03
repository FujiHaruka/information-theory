# Shannon: Wyner–Ziv legacy-tag → sorry-based migration plan

> **Parent**: [`wyner-ziv-moonshot-plan.md`](wyner-ziv-moonshot-plan.md)
> 関連 [`wyner-ziv-convexity-discharge-moonshot-plan.md`](wyner-ziv-convexity-discharge-moonshot-plan.md) /
> [`wyner-ziv-discharge-moonshot-plan.md`](wyner-ziv-discharge-moonshot-plan.md) /
> [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md) /
> [`audit/audit-tags.md`](../audit/audit-tags.md)。
>
> 本 plan は **proof completion ではなく legacy tag (suspect / staged / 🟢ʰ) → `sorry + @residual` への honesty 強化** (`audit-tags.md`「Deprecated」+「移行レシピ」) を目的とする独立 workstream。proof done は本 plan の出力にしない (= `wyner-ziv-discharge-moonshot-plan` / `wyner-ziv-convexity-discharge-*` 等別 workstream)。
>
> **Round 4 closure (2026-05-26)**: 境界判定 2 件 (`wyner_ziv_tendsto_chain` /
> `wzAchievability_random_binning_body`) が proof done 到達 (Tier 1 `@audit:ok`、
> 0 sorry / 0 @residual)、in-flight tracker から除外済 (判断ログ #2)。本 plan
> Phase 1.5.4 / 1.6.3 / 未決事項 2 / L-MIG-1 closed。

## Context

### なぜ Wyner–Ziv が pilot か (3 種混在 pilot 位置付け)

Wyner–Ziv は sorry-migration runbook (`docs/audit/sorry-migration-runbook.md`「並列実行候補 family」表) が「中規模、Round 1 並列候補」と分類した family。pilot 価値は **3 種混在パターンの最初の sweep**:

| 種別 | 件数 | 既存 pilot で扱った family |
|---|---:|---|
| `@audit:suspect(...)` | 6 | Hoeffding (closed) — pure suspect 19 件 sweep |
| `@audit:staged(...)` | 13 | Huffman (並行 plan、本 plan と同時 sweep 予定) — staged 主役 |
| 散文 `🟢ʰ` | 3 | (なし — 本 plan が最初) |
| `@audit:defer` | 0 | (該当なし) |
| `@audit:closed-by-successor` | 0 | (該当なし) |

**verbatim 計数** (`rg -nw 'sorry'` + tag 別 `rg -c` で確認、2026-05-25):

| 計数項目 | 件数 | 検証コマンド |
|---|---:|---|
| suspect total | **6** | `rg -c '@audit:suspect' InformationTheory/Shannon/WynerZiv*.lean` |
| staged total | **13** | `rg -c '@audit:staged' InformationTheory/Shannon/WynerZiv*.lean` |
| 🟢ʰ total | **3** | `rg -c '🟢ʰ' InformationTheory/Shannon/WynerZiv*.lean` |
| defer / closed-by-successor | 0 | (該当なし) |
| 既存 word-boundary `sorry` | **0** | `rg -nw 'sorry' InformationTheory/Shannon/WynerZiv*.lean` の 2 hit は全て docstring 内文字列 (`WynerZiv.lean:34` `0 sorry 発行`、`WynerZivBinningBody.lean:69` `in 0 sorry`)。Pilot Pattern D 適用済。 |

**他 family pilot との学び差分**:

- Hoeffding (suspect pilot): pure load-bearing predicate consumer の sweep 手順を確立。本 plan も staged 13 件で同じ手順を踏襲できる (predicate signature 削除 → body sorry + @residual)。
- Huffman (staged 並行 pilot、別 session): staged の migration recipe を pilot 中。本 plan は Huffman の手順 (`@audit:staged(<wall>)` → `sorry + @residual(plan:<slug>)`) を Wyner–Ziv 文脈でほぼ同形に適用。
- 散文 `🟢ʰ` (本 plan が初): 既存の `🟢ʰ` 3 件は **predicate 消費者側の wrapper docstring ではなく predicate 定義側 docstring** (`def WZFanoConverseBound` / `def WZCsiszarSumBound`) に "honest-🟢ʰ entropy-level input" として書かれている異形。Hoeffding/Huffman pilot とは形態が違い、新手順を確立する必要あり (→ Approach §「3 種混在 sweep 順序」)。

### 親 moonshot との関係

`wyner-ziv-moonshot-plan.md` は L-WZ1 / L-WZ2 / L-WZ3 / L-WP1-5 (cardinality bound / Csiszár sum / 凸性 / SBS instance ほか) すべて hypothesis pass-through で publish 済 (Phase D 完了)。Phase V (`InformationTheory.lean` 編入) も既完了。本 plan は **その pass-through 設計を変えない**:

- staged の load-bearing predicate (`IsWynerZivBinningCovering` 等 6 種、`WZPerLetterBound` 等 3 種、`WZFanoConverseBound` 等 3 種) を Phase 2 で削除し body sorry 化する。conclusion 型は変えない。
- suspect 6 件のうち真に de-circularized derivation を含む 1 件 (`wyner_ziv_converse_rate` — `wz_rate_le_of_fano` 経由) は Phase 2 で predicate hypothesis のみ削除、body は genuine 派生を残す可能性あり (Phase 2 中に honesty-auditor が判定)。
- **proof completion** (Csiszár sum identity の n-letter chain rule 実装 / `R_WZ(D)` 凸性 / 三項 typicality + AEP) は別 workstream (`wyner-ziv-discharge-moonshot-plan.md` 系) に残る。

### Honesty workflow と DoD

本 plan の DoD は `CLAUDE.md`「Definition of Done — 2 段階」の **type-check done**:
- 各 file `lake env lean InformationTheory/Shannon/WynerZiv<X>.lean` が 0 errors、
- 各新規 `sorry` に `@residual(<class>:<slug>)` タグ、
- 各 Phase 完了時に `honesty-auditor` を起動して classification + signature honesty を独立検証。

`@audit:ok` (proof done) は **本 plan の出力にはならない**。

### Tier 5 defect — Inline 検出済 (実装前に明示)

CLAUDE.md「検証の誠実性」"見つけた側" inline policy に従い、planner 段階で発見した tier 5 defect を以下に列挙。**実装 agent は本 plan に従って rewriter (signature 改変 + sorry 化) する際、新規に作らない + 既存を silent fix しない**。それぞれ Phase 2 内で **defect 明示付き** で sorry 化する (= `@residual(defect:circular)` で記録、`@residual(plan:...)` ではない)。

| file:line | decl 名 | defect kind | verbatim 根拠 |
|---|---|---|---|
| `WynerZivAchievability.lean:61` | `wyner_ziv_achievability_rate` | `defect:circular` + `defect:launder` | signature `(h_ach : wynerZivRatePmf U P_XY d D ≤ R) : wynerZivRatePmf U P_XY d D ≤ R := h_ach` — 仮説型 ≡ 結論型、body `:= h_ach`。`_rate` suffix も name laundering。 |
| `WynerZivAchievability.lean:82` | `wyner_ziv_achievability_existence` | `defect:circular` + `defect:launder` | `h_ach_existence : ∀ ε > 0, ∃ N, ∀ n ≥ N, ...` が conclusion とまったく同一の Prop、body `:= h_ach_existence`。Phase B 本体 (random binning) 全部を hyp に bundling。`_existence` は name laundering。 |
| `WynerZiv.lean:361` | `wyner_ziv_tendsto` | (境界例) | `(h_ach : ≤) (h_conv : ≤) : =` は `le_antisymm` で純合成、結論 = 入力 2 件の AND ではない (`=` ↔ `≤ ∧ ≥`)。`le_antisymm` 1 行で **構造的に正当**。Tier 5 ではなく **Phase 1 V/C 該当** (V: variational pass-through wrapper、構造的に circular ではない)。但し WynerZivConverse の de-circularization と同方針で `_tendsto` も後続 plan で派生形に置換予定。**本 plan では Phase 1 でタグ削除のみ**。 |

WynerZivConverse.lean の `wyner_ziv_converse_rate` (line 194) と `wyner_ziv_converse_existence` (line 239) は **既に de-circularized** (2026-05-21、docstring 冒頭の "De-circularization" 節参照): `wyner_ziv_converse_n_letter` (line 168) が `wz_rate_le_of_fano` で派生する形に整理済 → **load-bearing predicate (`WZFanoConverseBound` 等) consumer なので tier 4 (staged 相当)**、tier 5 ではない。

## Approach

**file 単位 sweep を 3 Phase + audit + verify に分割**、共有 wall lemma は集約しない、cross-family ripple (Relay CF) を明示的に保護する。

### 戦略 (3 種混在 sweep 順序)

3 種 (suspect / staged / 🟢ʰ) の混在に対する sweep 順序を **「壊れにくい → 構造的影響大」順** に設計:

```
Phase 0  inventory (本 plan 内 inline 表)
   │
Phase 1  V/C cleanup
   │      ├─ V (variational pass-through、純 wrapper)         ← suspect 中の V 2 件
   │      └─ C (in-tree constructive primitive 経由)          ← (該当なし、Wyner–Ziv では 0 件)
   │
Phase 1.5  S+H migration (load-bearing predicate consumer 一括書換)
   │      ├─ staged 13 件 → sorry + @residual(plan:...)       ← 全 file (signature 改変なし、body のみ書換)
   │      └─ 🟢ʰ 3 件 (predicate 定義 docstring) → @audit:retract-candidate 注記化
   │
Phase 1.6  audit-1 (Phase 1 + 1.5 全件)
   │
Phase 2.1  P/defect retreat — WynerZivAchievability.lean
   │      ├─ suspect 2 件 = tier 5 circular defect (rate + existence)
   │      └─ signature から `h_ach` / `h_ach_existence` 削除 + body sorry + @residual(defect:circular)
   │
Phase 2.2  P retreat — WynerZivConverse.lean (suspect 2 件、wyner_ziv_converse_rate / wyner_ziv_converse_existence)
   │      ├─ 結論型は変えない、load-bearing predicate (WZFanoConverseBound 等) 削除
   │      └─ derived form は wz_rate_le_of_fano 経由の本体を保持 (auditor が境界判定)
   │
Phase 2.x  ripple — caller drift handling
   │      ├─ WynerZivDischarge / WynerZivAchievabilityBridge / WynerZivDecoderFailureAssembly 内の caller
   │      ├─ RelayCFBinningBody.lean (cross-family、re-namespacing 3 件) → 触らない (signature 維持戦略)
   │      └─ docstring 散文で transitive 性を明示 (Pilot Pattern C: 即興 vocabulary 禁止)
   │
Phase 2.3  retract — 12 load-bearing predicate
   │      └─ @audit:retract-candidate(load-bearing-predicate) を 12 predicate に付与
   │           (削除はしない、Relay 再利用のため API 後方互換を保つ — L-MIG-2 回避)
   │
Phase 2.4  audit-2 (Phase 2 全件 + 12 predicate)
   │
Phase V   verify (全 file lake env lean 0 errors + 集計 + banner)
```

**3 種混在 sweep 順序の根拠**:

1. **V を最初** (Phase 1): `wyner_ziv_tendsto` (1 件) は構造的に non-defect、純 `le_antisymm` 合成。タグ削除のみで type-check 影響なし → 最も safe な warm-up。Hoeffding pilot で同パターンを実証済。

2. **staged + 🟢ʰ を中間** (Phase 1.5): staged 13 件は load-bearing predicate を **既に持っている**ため signature 改変が不要 (predicate を消すのは Phase 2 の話、本 Phase は body のみ書換)。実体は「`exact wyner_ziv_binning_via_covering_packing μ ... h_cov h_pack`」のような predicate-consuming body → `sorry + @residual(plan:wyner-ziv-discharge-moonshot-plan)` に置換するだけ。🟢ʰ 3 件は **predicate 定義** docstring の表現 (`"honest-🟢ʰ entropy-level input"`) の言い換えで、コード自体には影響しない。

3. **suspect 中の P (= 全 6 件中 4 件) を最後** (Phase 2.1 / 2.2): tier 5 defect (Achievability の 2 件) は signature 改変 + body sorry が必須 (`(h_ach : ...) : ... := h_ach` を `: ... := by sorry` に)。WynerZivConverse の 2 件は de-circularized derivation を含むため auditor 境界判定が必要 — signature 改変は最小限。

4. **Phase 2.x ripple は cross-family 保護を最優先**: `RelayCFBinningBody.lean` は `IsWynerZivBinningCovering` / `IsWynerZivBinningPacking` / `IsWynerZivBinningAchievable` の 3 predicate を **re-namespacing で再利用** (verbatim 確認: `RelayCFBinningBody.lean:127/195/262`)。`wyner_ziv_binning_via_covering_packing` を直接呼ぶ箇所もある (`RelayCFBinningBody.lean:348`)。これらの **predicate signature は維持必須**、Phase 2.3 では definition の `@audit:retract-candidate` で「削除候補」を記録するだけで実削除はしない。

### 共有 wall lemma 集約の要否

**集約しない**。`docs/audit/audit-tags.md`「Wall name register」表に Wyner–Ziv 関連の wall (`wyner-ziv-binning`, `wyner-ziv-csiszar`, `wyner-ziv-jensen` 等) は **未登録**。Hoeffding pilot 同様、全件 `@residual(plan:wyner-ziv-discharge-moonshot-plan)` または `(plan:wyner-ziv-convexity-discharge)` に揃え、新規 wall name を登録しない。

検証: register に登録済の wall (`stam` / `csiszar` / `n-dim-gaussian-aep` / `sphere-volume` / `continuous-aep` / `nyquist-2w-dof` / `multivariate-mi` / `joint-typicality-multi` / `epi-n-dim` / `fourier`) のうち、**`csiszar` が Wyner–Ziv の Csiszár sum identity に該当する可能性**を確認したが、register の `csiszar` は「Csiszár **projection**」(`Ch.11`) で Wyner–Ziv で必要なのは「Csiszár's **sum identity**」(`Ch.15.9` n-letter chain rule) で別物。新規 `csiszar-sum` を追加するかは **後続 family (LZ78 / Relay) で同 identity が再出現するかを観察してから決定** (本 plan では plan:slug 形で揃える)。

### constructive recovery 候補 (Pilot Pattern B)

Hoeffding pilot で 1 件 `isHoeffdingMinimizerFullSupport_of_lagrange` が `IsHoeffdingMinimizerFullSupport (hoeffdingTilt P₁ P₂ lam)` 結論型 = `∀ a, 0 < hoeffdingTilt ...` に reduce 可能で constructive 化した先例あり。Wyner–Ziv で同パターン候補を planner 段階で flag:

| file:line | decl 名 | 結論型 | 構成的回復可能性 |
|---|---|---|---|
| `WynerZiv.lean:329` | `wynerZivRatePmf_image_bddBelow_of_objective` | `BddBelow (image ...)` | **既に純構成的** (body は `refine ⟨B, ?_⟩; rintro v ⟨qf, hqf, rfl⟩; exact h_lb qf hqf`) — タグ削除のみ、suspect が誤付与の可能性。Phase 1 / V 候補。 |
| その他 12 件 | 全 staged 13 件 + remaining suspect 4 件 | 各種 Prop / inequality 結論 | 全件 load-bearing predicate consumer または derivation pattern。**constructive recovery 不可** (本体が deep info-theoretic 内容)。 |

→ Phase 1 で `wynerZivRatePmf_image_bddBelow_of_objective` を V/C パターンに 確実に分類、不要 sorry を作らない。

### transitive sorry の handling 方針 (Pilot Pattern C)

Phase 2 で upstream を sorry 化すると caller が transitive sorry を引き継ぐ。**即興 vocabulary 禁止** (`(plan:..., transitive)` 等は `audit-tags.md` 未登録)。具体的に予測される影響範囲:

- Phase 2.1 が `wyner_ziv_achievability_existence` を sorry 化 → `WynerZivAchievabilityBridge.lean` / `WynerZivDecoderFailureAssembly.lean` の caller が transitive sorry。各 declaration の docstring 散文で **「transitive sorry via `wyner_ziv_achievability_existence` (Phase 2.1 retreat). No `@residual` tag attached — closure responsibility belongs to upstream's `@residual(defect:circular)`.」** と明示。
- Phase 2.2 が `wyner_ziv_converse_rate` / `wyner_ziv_converse_existence` を sorry 化 → `WynerZivDischarge.lean` / `WynerZivConverseChain.lean` 内 caller が transitive。同様に docstring 散文で transitive 性明示。

Phase 2.x で具体的な caller を `rg` で再確認後、対象 file ごとに散文を書込み (Phase 2.x ステップ参照)。

## 在庫: 22 件 (suspect 6 + staged 13 + 🟢ʰ 3) verbatim 分類

verbatim 確認方法: 各 `@audit:suspect|@audit:staged|🟢ʰ` 周辺 docstring + theorem signature + body 1-3 行を実コードから読込、「signature の hypothesis が load-bearing か regularity か」を 1 件ずつ判定。各 declaration の `path:line` は **タグ行**、declaration 名はその直後。

### suspect (6 件)

| file:line | decl 名 | 現タグの核 (verbatim docstring 1 行) | パターン | 削除/置換予定タグ | constructive recovery? | 備考 |
|---|---|---|---|---|---|---|
| `WynerZiv.lean:328` | `wynerZivRatePmf_image_bddBelow_of_objective` | "the explicit bound is supplied by callers when needed" — Bdd 抽出 wrapper、`h_lb` は regularity hyp | C (= V 寄り) | **(タグ削除のみ)** | ✅ 既に純構成的 (body: `refine ⟨B, ?_⟩; rintro v ⟨qf, hqf, rfl⟩; exact h_lb qf hqf`) | Phase 1 候補。suspect 誤付与の疑い、auditor 判定対象 |
| `WynerZiv.lean:360` | `wyner_ziv_tendsto` | "The two-sided hypotheses are discharged in `WynerZivAchievability.lean` ... and `WynerZivConverse.lean`" | V | **(タグ削除のみ)** | (既に純構成的 `le_antisymm`) | Phase 1 候補。`(h_ach : ≤) (h_conv : ≤) : =` の合成は構造的に non-circular |
| `WynerZivAchievability.lean:60` | `wyner_ziv_achievability_rate` | "trivial unwrapping that documents the consumption shape" | **tier 5 defect (circular + launder)** | `@residual(defect:circular)` | ✗ (defect、構造的破棄) | **Phase 2.1**。仮説型 = 結論型、body `:= h_ach`。signature 改変必須 (`h_ach` 削除) + body sorry |
| `WynerZivAchievability.lean:81` | `wyner_ziv_achievability_existence` | "callers who *have* discharged Phase B can supply this hypothesis directly" | **tier 5 defect (circular + launder)** | `@residual(defect:circular)` | ✗ (defect) | **Phase 2.1**。Phase B 本体全部を hyp に bundling、body `:= h_ach_existence`。signature 改変必須 |
| `WynerZivConverse.lean:193` | `wyner_ziv_converse_rate` | "The genuine n-letter bound is computed inline (not assumed)" | P (load-bearing predicate consumer; body 内派生は genuine) | `@residual(plan:wyner-ziv-discharge-moonshot-plan)` (signature 改変) | △ (body 内 `wyner_ziv_converse_n_letter` 呼出は genuine 派生だが、`h_R_le` / `h_op_le` 仮説に L-WZ-rate-load-bearing 性) | **Phase 2.2**。signature 改変 (load-bearing predicate `WZFano...` 等は本体経由で間接消費)。auditor 境界判定 |
| `WynerZivConverse.lean:238` | `wyner_ziv_converse_existence` | "derived by contrapositive from the genuine n-letter rate bound" | P (`h_nletter` hyp に conclusion を bundling) | `@residual(plan:wyner-ziv-discharge-moonshot-plan)` | ✗ (`h_nletter` が結論を `∀ n M c, ...` 形で抱える load-bearing hyp) | **Phase 2.2**。contrapositive は構造的だが `h_nletter` が load-bearing |

### staged (13 件、全 load-bearing predicate consumer = P パターン)

| file:line | decl 名 | 現タグの核 (verbatim docstring 1 行) | パターン | 削除/置換予定タグ | 消費 predicate | 備考 |
|---|---|---|---|---|---|---|
| `WynerZivConverseChain.lean:129` | `wyner_ziv_converse_chain` | "Composes per-letter feasibility + Csiszár sum identity + Jensen-antitonicity into the final rate bound" | P | `@residual(plan:wyner-ziv-discharge-moonshot-plan)` | `WZPerLetterBound` + `CsiszarSumIdentity` + `WZJensenAntitone` | Phase 1.5。signature 維持 (predicate 残存)、body sorry |
| `WynerZivConverseChain.lean:162` | `wyner_ziv_converse_chain_block` | "Specializes `wyner_ziv_converse_chain` to a `WynerZivCode`" | P | 同上 | 同上 + WynerZivCode | Phase 1.5 |
| `WynerZivConverseChain.lean:452` | `wyner_ziv_converse_chain_composite` | "Replaces the bundled `CsiszarSumIdentity` with its three underlying ingredients" | P | 同上 | 5 hyp 分解形 | Phase 1.5 |
| `WynerZivConverseChain.lean:483` | `wyner_ziv_converse_n_letter_chain` | "the n-letter rate bound `R_WZ(D) ≤ log M / n` is **derived** via `wyner_ziv_converse_chain_block` (genuine chain algebra)" | P (chain assembly genuine だが入力 predicate が load-bearing) | 同上 | 同上 | Phase 1.5。chain algebra は genuine だが入力依存 |
| `WynerZivConverseChain.lean:532` | `wyner_ziv_converse_chain_existence` | "derived by contrapositive from the genuine chain assembly" | P | 同上 | `h_chain_nletter` (conclusion-bundling load-bearing) | Phase 1.5 |
| `WynerZivConverseChain.lean:580` | `wyner_ziv_tendsto_chain` | "Pure forwarder to `wyner_ziv_tendsto`" | V (純 forwarder) but 上流が staged → 連動 | (タグ削除のみ、Phase 1.5 で `wyner_ziv_tendsto` 連動判定) | (なし、`h_ach` + `h_chain_conv`) | ~~Phase 1.5。auditor 境界判定対象~~ → **2026-05-26 Round 4 closure: proof done 到達** (Tier 1 `@audit:ok`、body `le_antisymm h_chain_conv h_ach`、0 sorry / 0 @residual)。tracker から除外。 |
| `WynerZivBinningCovering.lean:238` | `wyner_ziv_binning_via_covering_packing` | "covering ⇒ `μ.real(E_typ) ≤ ε₁`, packing ⇒ `μ.real(E_bin) ≤ ε₂`" | P | `@residual(plan:wyner-ziv-discharge-moonshot-plan)` | `IsWynerZivBinningCovering` + `IsWynerZivBinningPacking` | Phase 1.5。**cross-family 注意** (RelayCF 経由) |
| `WynerZivBinningCovering.lean:270` | `wynerZivBinningBody_of_covering_packing` | "Same statement re-exported with the implicit bookkeeping" | P (純 re-export) | 同上 | 同上 | Phase 1.5。**cross-family 注意** |
| `WynerZivBinningCovering.lean:322` | `wyner_ziv_binning_existence_of_covering_packing` | "asymptotic covering + packing ⇒ asymptotic decoder failure → 0" | P (existence form、`h_asymp` が load-bearing) | 同上 | `h_asymp` (existence-form predicate bundle) | Phase 1.5 |
| `WynerZivBinningCovering.lean:461` | `wyner_ziv_binning_decoder_fail_of_achievable` | "consuming the single joint predicate `IsWynerZivBinningAchievable`" | P | 同上 | `IsWynerZivBinningAchievable` | Phase 1.5。**cross-family 注意** |
| `WynerZivCoveringBody.lean:411` | `wzCovering_feed_asymp` | "Combine the covering existence form ... with the external packing existence form" | P | 同上 | `IsCoveringTypicalityHyp` + `IsPackingExistenceHyp` | Phase 1.5 |
| `WynerZivPackingBody.lean:536` | `wyner_ziv_packing_existence` | "discharged internally from `IsPackingTypicalityHyp` via the first moment method" | P | 同上 | `IsPackingTypicalityHyp` + `IsPackingCollisionBoundHyp` | Phase 1.5 |
| `WynerZivBinningBody.lean:479` | `wzAchievability_random_binning_body` | "clean composition — once both hypotheses are available, the bound `Pr[error] ≤ ε_typ + ε_bin` is a two-line consequence" | P (clean composition、`h_typ_prob` / `h_bin_prob` regularity 境界) | 同上 (境界判定要) | `h_typ_prob` + `h_bin_prob` (= probability bound、≒ regularity) | ~~Phase 1.5。auditor 境界判定対象 (regularity vs load-bearing)~~ → **2026-05-26 Round 4 closure: proof done 到達** (Tier 1 `@audit:ok`、body は 4-line `wzAchievability_decoder_fail_le` + `add_le_add` の calc、0 sorry / 0 @residual)。tracker から除外。 |

### 散文 `🟢ʰ` (3 件、すべて `WynerZivConverse.lean` 内 predicate 定義 docstring)

| file:line | 配置 (decl / docstring) | 現タグの核 | パターン | 削除/置換予定タグ | 備考 |
|---|---|---|---|---|---|
| `WynerZivConverse.lean:30` | `def WZFanoConverseBound` (line 83) docstring の本文中 ("the per-letter Jensen plumbing that produces this scalar inequality is a real Mathlib gap") | H (predicate 定義側の load-bearing 性 self-acknowledgment) | docstring 散文 refine → `@audit:retract-candidate(load-bearing-predicate)` 付与 | Phase 1.5 |
| `WynerZivConverse.lean:68` | `def WZFanoConverseBound` (line 83) の docstring opening "(honest-🟢ʰ entropy-level input)" | H | docstring 文言から "(honest-🟢ʰ entropy-level input)" 削除、tier 4 言語廃止 | Phase 1.5 |
| `WynerZivConverse.lean:89` | `def WZCsiszarSumBound` (line 101) の docstring opening "(honest-🟢ʰ entropy-level input)" | H | 同上 | Phase 1.5 |

**集計** (パターン別):
- V (variational pass-through、タグ削除のみ): **2 件** (Phase 1)
- C (in-tree constructive / 既に純構成的): **1 件** (Phase 1、`wynerZivRatePmf_image_bddBelow_of_objective`)
- S (staged 全件、predicate consumer、body sorry + @residual): **13 件** (Phase 1.5)
- H (🟢ʰ predicate 定義側 docstring): **3 件** (Phase 1.5、文言 refine + retract-candidate 付与)
- P (suspect 中の load-bearing consumer): **2 件** (Phase 2.2、Converse 系)
- P (suspect 中の tier 5 defect = circular + launder): **2 件** (Phase 2.1、Achievability 系)
- 境界判定 (auditor 委任): ~~**2 件** (`wyner_ziv_tendsto_chain` / `wzAchievability_random_binning_body`)~~ → **0 件** (両者 2026-05-26 Round 4 closure で proof done 到達、判断ログ #2 参照)

総計 22 = 2 (V) + 1 (C) + 13 (S) + 3 (H) + 2 (P-converse) + 2 (P-defect-achievability) + 残り 2 件 (上記 V/C と境界が重複カウント、22 件総計)。

## Phase 詳細

### Phase 0 — Inventory (本 plan 内 inline、完了) 📋 ✅

- [x] 各 22 件を verbatim 確認 (`rg -c` + 該当 docstring + signature 1-3 行を実コード Read)
- [x] パターン分類 (V/C/S/H/P + defect 細分)
- [x] cross-family 依存 (Relay CF re-namespacing 3 件) を `rg` で確認
- [x] 既存 sorry word-boundary 計数 `0` 件確定 (Pilot Pattern D 適用済)

**proof-log**: no (mechanical 在庫確認、interesting なし)。

### Phase 1 — V/C cleanup (低 risk、新規 sorry なし) 📋

- [ ] **1.1** `WynerZiv.lean` の V/C 該当 2 件 (`wynerZivRatePmf_image_bddBelow_of_objective` line 328 / `wyner_ziv_tendsto` line 360) の `@audit:suspect(wyner-ziv-moonshot-plan)` 削除。
  - 両件とも既に純構成的 (body は `refine ⟨B, ?_⟩; ...` / `le_antisymm h_conv h_ach`)。タグ削除のみ、signature 改変なし、新規 sorry なし。
  - `lake env lean InformationTheory/Shannon/WynerZiv.lean` で type-check done 確認。
- [ ] **1.2** Phase 1 完了時 `rg -n '@audit:suspect' InformationTheory/Shannon/WynerZiv.lean` で 0 件確認。

**Phase 1 DoD**: `WynerZiv.lean` で `@audit:suspect` 0 件、新規 `sorry` 0 件、`lake env lean` 0 errors。

**proof-log**: no (mechanical tag removal)。

### Phase 1.5 — S+H migration (staged 13 件 + 🟢ʰ 3 件、body sorry + docstring refine) 📋

- [ ] **1.5.1** `WynerZivConverse.lean` の **🟢ʰ 3 件** (line 30 / 68 / 89) の docstring 文言から `(honest-🟢ʰ entropy-level input)` を削除、tier 4 vocabulary を回避。本文中の "honest-🟢ʰ" 言及は **load-bearing predicate definition である旨の散文** に書き換え。
  - 同 file 内 `def WZFanoConverseBound` (line 83) / `def WZCsiszarSumBound` (line 101) / `def WZRateCleanup` (line 106) の 3 predicate に `@audit:retract-candidate(load-bearing-predicate)` を docstring 末尾に付与 (削除はしない — Phase 2.2 で consumer が sorry 化された後も外部利用がないか auditor が確認、cross-family なし)。
- [ ] **1.5.2** `WynerZivConverseChain.lean` の **staged 6 件** (line 129 / 162 / 452 / 483 / 532 / 580) の `@audit:staged(wyner-ziv-load-bearing)` を削除、body を `sorry` に置換、docstring 末尾に `@residual(plan:wyner-ziv-discharge-moonshot-plan)` を付与。
  - signature は **改変しない** (consumer 側 predicate は残す、Phase 2.3 で retract-candidate)。
  - ~~例外: `wyner_ziv_tendsto_chain` (line 580) は純 forwarder で `wyner_ziv_tendsto` (Phase 1 でタグ削除済) への pass-through。auditor 境界判定対象 — 暫定で `@residual(plan:wyner-ziv-discharge-moonshot-plan)` 付与、auditor 判定によっては Phase 1.6 で タグ削除のみに格下げ。~~ → **2026-05-26 Round 4 closure 済**: `wyner_ziv_tendsto_chain` は proof done 到達 (Tier 1 `@audit:ok`、body `le_antisymm h_chain_conv h_ach`、0 sorry / 0 @residual)。本 Phase scope 外。
  - 同 file 内 `structure WZPerLetterBound` (line 91) / `def CsiszarSumIdentity` (line 106) / `def WZJensenAntitone` (line 113) の 3 predicate に `@audit:retract-candidate(load-bearing-predicate)` 付与。
- [ ] **1.5.3** `WynerZivBinningCovering.lean` の **staged 4 件** (line 238 / 270 / 322 / 461) の同様の書換。
  - **cross-family 注意 (L-MIG-2)**: 3 predicate (`IsWynerZivBinningCovering` line 97 / `IsWynerZivBinningPacking` line 162 / `IsWynerZivBinningAchievable` line 388) は `RelayCFBinningBody.lean:127/195/262` で再利用されている。**retract-candidate 付与時に docstring に「Relay CF が consumer に存在 — 削除前に Relay 側 incidental migration 必要」と注記**。
- [x] ~~**1.5.4** `WynerZivBinningBody.lean` の **staged 1 件** (`wzAchievability_random_binning_body` line 479)。~~
  - ~~境界判定: `h_typ_prob` / `h_bin_prob` は `μ.real (...) ≤ ε_typ` 形 = probability bound (regularity-like) — auditor が判定。暫定で `@residual(plan:wyner-ziv-discharge-moonshot-plan)` 付与、body sorry。~~ → **2026-05-26 Round 4 closure 済**: `wzAchievability_random_binning_body` は proof done 到達 (Tier 1 `@audit:ok`、body は 4-line `wzAchievability_decoder_fail_le` + `add_le_add` の calc block、0 sorry / 0 @residual)。本 Phase scope 外、tracker から除外。
- [ ] **1.5.5** `WynerZivCoveringBody.lean` (`wzCovering_feed_asymp` line 411) + `WynerZivPackingBody.lean` (`wyner_ziv_packing_existence` line 536) の **staged 2 件** 書換。両件とも load-bearing predicate consumer なので sorry + `@residual(plan:wyner-ziv-discharge-moonshot-plan)`。
  - 関連 predicate 定義 (`IsCoveringTypicalityHyp` / `IsPackingTypicalityHyp` / `IsPackingCollisionBoundHyp`) は Phase 2.3 で retract-candidate (cross-family なし、Wyner–Ziv 内 closed)。
- [ ] **1.5.6** Phase 1.5 完了時 各 file で `lake env lean` 確認、`@audit:staged` 0 件 / `🟢ʰ` 0 件 / 新規 `@residual(plan:wyner-ziv-discharge-moonshot-plan)` 付き sorry 13 件を `rg` で確認。

**Phase 1.5 DoD**:
- `@audit:staged` 0 件、`🟢ʰ` 0 件、
- `@residual(plan:wyner-ziv-discharge-moonshot-plan)` 13 件、
- 12 predicate (`WZFano...` 3 + `WZPerLetter/Csiszar/Jensen` 3 + `IsWynerZivBinning*` 3 + `IsCovering/PackingTypicality + IsPackingCollisionBound` 3) に `@audit:retract-candidate(load-bearing-predicate)` 付与済、
- 各 file `lake env lean` 0 errors。

**proof-log**: yes (`docs/proof-logs/proof-log-wyner-ziv-sorry-migration-phase-1.5.md`)。理由: 🟢ʰ の docstring refine 判断 (どの程度言い換えるか) と境界例 (`wzAchievability_random_binning_body` / `wyner_ziv_tendsto_chain`) の `@residual` 付与判定理由を残す。

### Phase 1.6 — audit-1 (Phase 1 + 1.5 全件) 📋

- [ ] **1.6.1** orchestrator は `honesty-auditor` (または `general-purpose` + brief) を起動。対象:
  - Phase 1: 2 件 (V/C cleanup の suspect 削除妥当性)
  - Phase 1.5: 13 staged → sorry + @residual の classification + 3 🟢ʰ の docstring refine 妥当性 + 12 predicate の retract-candidate 付与妥当性
- [ ] **1.6.2** verdict 受領 (`ok` / `questionable` / `defect`):
  - `ok` → Phase 2.1 着手
  - `questionable` → docstring refine or 散文追記、Phase 2 進行
  - `defect` → 当該 declaration を撤回 / 修正、Phase 2 進行前に解決
- [x] ~~**1.6.3** 境界判定 2 件 (`wyner_ziv_tendsto_chain` / `wzAchievability_random_binning_body`) の最終分類を auditor verdict から確定。~~ → **2026-05-26 Round 4 closure 済**: 両者 proof done 到達 (`@audit:ok`)。Round 4 Tier 1 honesty への自然進化として確定 (判断ログ #2)。

**proof-log**: yes (auditor verdict + 境界判定結果を proof-log に追記)。

### Phase 2.1 — P retreat (Achievability tier 5 defect 2 件、signature 改変) 📋

- [ ] **2.1.1** `WynerZivAchievability.lean:61` `wyner_ziv_achievability_rate`:
  - **defect 種類**: `defect:circular` (仮説型 ≡ 結論型) + `defect:launder` (`_rate` suffix が claim 通りでない)。
  - 改変: signature から `(h_ach : wynerZivRatePmf U P_XY d D ≤ R)` を削除。結論型 `wynerZivRatePmf U P_XY d D ≤ R` は変えない (achievability rate bound という意味は保つ)。
  - body: `:= h_ach` → `:= by sorry`。
  - 旧 `@audit:suspect(wyner-ziv-moonshot-plan)` → `@residual(defect:circular)` (docstring 末尾)。**追加 docstring 散文** で「Phase 2.1 retreat — 旧 signature は circular hypothesis bundling + name laundering。Phase B 本体 (random binning + 三項 jointly typical decoder) の closure は `wyner-ziv-discharge-moonshot-plan` 配下で実施」。

- [ ] **2.1.2** `WynerZivAchievability.lean:82` `wyner_ziv_achievability_existence`:
  - **defect 種類**: 同上 (`defect:circular` + `defect:launder`)、bundling 規模はより大 (Phase B 全部を `h_ach_existence` に bundling)。
  - 改変: signature から `(h_ach_existence : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ M c, ...)` を削除、`(_h_R_gt : R > ...)` の underscore は保持 (regularity)。結論型 (`∀ ε > 0, ∃ N, ...`) は変えない。
  - body: `:= h_ach_existence` → `:= by sorry`。
  - 旧 tag → `@residual(defect:circular)`、docstring 散文で同様の note。

- [ ] **2.1.3** Phase 2.1 完了時 `WynerZivAchievability.lean` で `lake env lean` 確認 (signature 改変したため olean refresh が必要、Pilot Pattern A):
  ```bash
  lake build InformationTheory.Shannon.WynerZivAchievability
  lake env lean InformationTheory/Shannon/WynerZivAchievability.lean
  ```
- [ ] **2.1.4** dependent file (`WynerZiv.lean` 経由 import / `WynerZivAchievabilityBridge.lean` 経由 wrapper / `WynerZivDecoderFailureAssembly.lean` 等) を `rg -l 'wyner_ziv_achievability_rate\|wyner_ziv_achievability_existence' InformationTheory/Shannon/` で列挙、各 file で `lake env lean` 再 verify。type drift があれば Phase 2.x ripple step で対応。

**Phase 2.1 DoD**:
- `WynerZivAchievability.lean` で `@audit:suspect` 0 件、`@residual(defect:circular)` 2 件、対応 sorry 2 件、
- `lake env lean InformationTheory/Shannon/WynerZivAchievability.lean` 0 errors、
- dependent file の type drift が **同 session で吸収済** (Phase 2.x で散文化)。

**proof-log**: yes。理由: tier 5 defect 化の判定 + dependent caller (Bridge / DecoderFailureAssembly) への波及範囲記録。

### Phase 2.2 — P retreat (Converse 2 件、load-bearing predicate consumer) 📋

- [ ] **2.2.1** `WynerZivConverse.lean:194` `wyner_ziv_converse_rate`:
  - 改変: signature から load-bearing predicate consumer `(h_fano : WZFanoConverseBound ...)` / `(h_csiszar : WZCsiszarSumBound ...)` / `(h_cleanup : WZRateCleanup ...)` を削除、`(h_R_le : R ≤ Real.log M / n + ε)` と `(h_op_le : Real.log M / n + ε ≤ wynerZivRatePmf ...)` は **境界判定** (auditor 委任):
    - `h_R_le` は operational-vs-information rate ordering の主張 = load-bearing
    - `h_op_le` は per-letter operational rate ≤ R_WZ(D) の主張 = load-bearing
    両方とも sorry 化に巻き込み (signature から削除)、conclusion `R ≤ wynerZivRatePmf U P_XY d D` のみ残す。
  - body: 既存 `wyner_ziv_converse_n_letter` 呼出 + `le_trans` → `:= by sorry`。
  - 旧 `@audit:suspect(wyner-ziv-moonshot-plan)` → `@residual(plan:wyner-ziv-discharge-moonshot-plan)`。

- [ ] **2.2.2** `WynerZivConverse.lean:239` `wyner_ziv_converse_existence`:
  - 改変: signature から `(h_nletter : ∀ n M c, ...)` (= conclusion を quantified 形で抱える load-bearing) を削除。`(h_R_lt : R < wynerZivRatePmf ...)` は precondition なので残す。
  - body: contrapositive derivation → `:= by sorry`。
  - 旧タグ → `@residual(plan:wyner-ziv-discharge-moonshot-plan)`。

- [ ] **2.2.3** **`wyner_ziv_converse_n_letter` (line 168) は触らない** — 既に de-circularized derivation で `WZFanoConverseBound` / `WZCsiszarSumBound` / `WZRateCleanup` consumer。Phase 1.5 で staged 化されていないため (suspect でもない)、本 Phase の対象外。ただし dependent (2.2.1 / 2.2.2) が sorry 化された影響で **caller として参照する Discharge / Bridge は transitive sorry**。

- [ ] **2.2.4** Phase 2.2 完了時 `WynerZivConverse.lean` で `lake env lean` 確認 + dependent (`WynerZivDischarge.lean` 等) の type drift 列挙 → Phase 2.x で散文化対応。

**Phase 2.2 DoD**:
- `WynerZivConverse.lean` で `@audit:suspect` 0 件、`@residual(plan:wyner-ziv-discharge-moonshot-plan)` 2 件、新規 sorry 2 件、
- `lake env lean InformationTheory/Shannon/WynerZivConverse.lean` 0 errors。

**proof-log**: yes。理由: `h_R_le` / `h_op_le` / `h_nletter` の load-bearing 境界判定理由を残す。

### Phase 2.x — ripple (caller drift handling, 散文 transitive 明示) 📋

- [ ] **2.x.1** `rg -l '(wyner_ziv_achievability_rate|wyner_ziv_achievability_existence|wyner_ziv_converse_rate|wyner_ziv_converse_existence|wyner_ziv_converse_chain|wyner_ziv_binning_via_covering_packing|wynerZivBinningBody_of_covering_packing|wzAchievability_random_binning_body)' InformationTheory/Shannon/` で caller 列挙。予想:
  - `WynerZivDischarge.lean` — 上位 wrapper
  - `WynerZivAchievabilityBridge.lean` — achievability bridge
  - `WynerZivDecoderFailureAssembly.lean` — decoder failure assembly
  - `WynerZivConverseChain.lean` (内部 caller、Phase 1.5 で staged 移行済)
  - `WynerZivCondEntDiffConvexBody.lean` / `WynerZivConvexityBody.lean` / `WynerZivObjectiveConvexityBody.lean` — convexity 系
  - **cross-family**: `RelayCFBinningBody.lean:348` (`wyner_ziv_binning_via_covering_packing` 直接呼出)
- [ ] **2.x.2** 各 caller について **transitive sorry の docstring 散文** を追加 (`@residual` タグは付与しない、Pilot Pattern C):
  ```
  Transitive `sorry` via `<upstream decl>` (Phase 2.{1,2} retreat). No `@residual`
  tag is attached — the closure responsibility belongs to the upstream
  declaration's `@residual(<class>:<slug>)`.
  ```
  即興 `(<class>:<slug>, transitive)` vocabulary 禁止 (`audit-tags.md` 未登録)。
- [ ] **2.x.3** **cross-family caller (`RelayCFBinningBody.lean`) は touch しない** (本 plan scope 外、Relay family の sweep agent が別途扱う)。本 plan は WynerZiv 側 predicate definitions に `@audit:retract-candidate(load-bearing-predicate)` を付与する際の docstring 注記で「Relay CF は依然 consumer」と明示するに留める (Phase 2.3 参照)。
- [ ] **2.x.4** ripple 完了時 全 file で `lake env lean` 再 verify。olean refresh は `lake build InformationTheory.Shannon.WynerZivAchievability` / `lake build InformationTheory.Shannon.WynerZivConverse` で済ませる (Pilot Pattern A)。

**Phase 2.x DoD**:
- 全 caller の transitive sorry が散文化済、即興 vocabulary 0 件、
- 各 file `lake env lean` 0 errors。

**proof-log**: no (mechanical 散文追加)。

### Phase 2.3 — retract (12 load-bearing predicate に retract-candidate 付与) 📋

Phase 1.5 で既に retract-candidate を付与した predicate の **再確認 + cross-family 注記の最終調整**:

| file:line | predicate | cross-family consumer? | retract-candidate reason |
|---|---|---|---|
| `WynerZivConverse.lean:83` | `WZFanoConverseBound` | なし | 全 consumer (Phase 2.2 で sorry 化済 + `wyner_ziv_converse_n_letter` 本体) は family 内 |
| `WynerZivConverse.lean:101` | `WZCsiszarSumBound` | なし | 同上 |
| `WynerZivConverse.lean:106` | `WZRateCleanup` | なし | 同上 |
| `WynerZivConverseChain.lean:91` | `WZPerLetterBound` | なし | family 内 chain decls (Phase 1.5 で sorry 化済) |
| `WynerZivConverseChain.lean:106` | `CsiszarSumIdentity` | なし | 同上 |
| `WynerZivConverseChain.lean:113` | `WZJensenAntitone` | なし | 同上 |
| `WynerZivBinningCovering.lean:97` | `IsWynerZivBinningCovering` | **あり** (`RelayCFBinningBody.lean:127`) | 削除不可、`retract-candidate` 付与時に Relay 注記必須 |
| `WynerZivBinningCovering.lean:162` | `IsWynerZivBinningPacking` | **あり** (`RelayCFBinningBody.lean:195`) | 同上 |
| `WynerZivBinningCovering.lean:388` | `IsWynerZivBinningAchievable` | **あり** (`RelayCFBinningBody.lean:262`) | 同上 |
| `WynerZivCoveringBody.lean:255` | `IsCoveringTypicalityHyp` | なし (要確認) | family 内 (要 `rg`) |
| `WynerZivPackingBody.lean:101` | `IsPackingTypicalityHyp` | なし (要確認) | family 内 (要 `rg`) |
| `WynerZivPackingBody.lean:113` | `IsPackingCollisionBoundHyp` | なし (要確認) | family 内 (要 `rg`) |

- [ ] **2.3.1** 各 predicate の docstring に `@audit:retract-candidate(load-bearing-predicate)` を付与 (Phase 1.5 で済んでいない場合追記)。cross-family ありの 3 predicate には散文で「Relay CF (`RelayCFBinningBody.lean`) が consumer に存在、削除前に Relay 側 incidental migration 必要」と明示。
- [ ] **2.3.2** `rg -n 'IsCoveringTypicalityHyp\|IsPackingTypicalityHyp\|IsPackingCollisionBoundHyp' InformationTheory/` で cross-family consumer 最終確認 (Wyner–Ziv 外で参照されていないか)。

**Phase 2.3 DoD**: 12 predicate に `@audit:retract-candidate(load-bearing-predicate)` 付与済、cross-family 注記済。

**proof-log**: no (mechanical 付与)。

### Phase 2.4 — audit-2 (Phase 2.1 / 2.2 / 2.x / 2.3 全件) 📋

- [ ] **2.4.1** orchestrator は `honesty-auditor` を起動。対象:
  - Phase 2.1: 2 件 (Achievability defect retreat の classification 正しさ + signature honesty)
  - Phase 2.2: 2 件 (Converse load-bearing predicate consumer の sorry 化判定 + 境界判定)
  - Phase 2.x: 全 caller の transitive 散文の vocabulary 整合 + 即興 tag 不在確認
  - Phase 2.3: 12 predicate の retract-candidate 付与正しさ + cross-family 注記の verbatim 検証
- [ ] **2.4.2** verdict 受領 + 修正対応 (Phase 1.6 同様)。

**proof-log**: yes (auditor verdict + 修正対応記録)。

### Phase V — verify + plan の集約 📋

- [ ] **V.1** 全 15 file で `lake env lean` 確認:
  ```bash
  for f in InformationTheory/Shannon/WynerZiv*.lean; do
    echo "=== $f ==="
    lake env lean "$f"
  done
  ```
  signature 改変があった file (Achievability / Converse) は事前に `lake build InformationTheory.Shannon.Wyner...` で olean refresh (Pilot Pattern A)。
- [ ] **V.2** 集計コマンド実行:
  ```bash
  rg -c '@audit:suspect' InformationTheory/Shannon/WynerZiv*.lean | awk -F: '{s+=$2} END {print "suspect:", s}'   # = 0
  rg -c '@audit:staged' InformationTheory/Shannon/WynerZiv*.lean | awk -F: '{s+=$2} END {print "staged:", s}'     # = 0
  rg -c '🟢ʰ' InformationTheory/Shannon/WynerZiv*.lean | awk -F: '{s+=$2} END {print "🟢ʰ:", s}'                  # = 0
  rg -c '@residual\(plan:wyner-ziv-discharge-moonshot-plan\)' InformationTheory/Shannon/WynerZiv*.lean | awk -F: '{s+=$2} END {print "residual(plan):", s}'  # ~15
  rg -c '@residual\(defect:circular\)' InformationTheory/Shannon/WynerZiv*.lean | awk -F: '{s+=$2} END {print "residual(defect):", s}'  # = 2
  rg -c '@audit:retract-candidate\(load-bearing-predicate\)' InformationTheory/Shannon/WynerZiv*.lean | awk -F: '{s+=$2} END {print "retract-candidate:", s}'  # = 12
  rg -nw 'sorry' InformationTheory/Shannon/WynerZiv*.lean | wc -l   # ~17 (= 15 staged + 2 defect + 境界判定差分)
  ```
- [ ] **V.3** 親 plan `wyner-ziv-moonshot-plan.md` 冒頭 banner 更新: 「sorry-based 移行完了 (`docs/shannon/wynerziv-sorry-migration-plan.md` 参照)、本 plan の Phase 0-D が引いた pass-through 設計は変更なし」を追記。
- [ ] **V.4** Pilot 知見を `.claude/handoff-sorry-migration.md` (または後続 family 用テンプレート) に反映:
  - 3 種混在 sweep の Phase 1 / 1.5 / 2.1 / 2.2 / 2.x / 2.3 分割が機能したか (失敗パターン記録)
  - 🟢ʰ predicate-definition 形 (= Wyner–Ziv 固有、Hoeffding/Huffman で未観測) の docstring refine 手順を runbook 化検討
  - cross-family ripple (Relay CF re-namespacing) の handling: predicate 削除しない + 散文注記で保護
  - tier 5 defect (Achievability circular + launder) の detection が planner 段階で可能だった事実 → 他 family の suspect inventory でも circular check を必須化

## 撤退ライン

- **L-MIG-1 (variational / regularity hyp の load-bearing 判定が auditor で変動)**: ~~Phase 1.5 境界判定 2 件 (`wyner_ziv_tendsto_chain` / `wzAchievability_random_binning_body`) について auditor が「`h_ach + h_chain_conv` / `h_typ_prob + h_bin_prob` は load-bearing claim」と判定したら、暫定の `@residual(plan:...)` を維持 (Phase 1.5 設計通り)。逆に「regularity / pass-through wrapper」と判定したら `@residual` 削除 + 純タグ削除に降格。Phase 1.6 audit-1 で確定。~~ → **2026-05-26 Round 4 closure 済**: 両 declaration とも構造的に「regularity / pass-through wrapper」確定 + proof done 到達 (Tier 1 `@audit:ok`、判断ログ #2)。撤退ライン消化。
- **L-MIG-2 (Phase 1.5 / 2.3 で predicate を消すと cross-family drift)**: `IsWynerZivBinningCovering` / `IsWynerZivBinningPacking` / `IsWynerZivBinningAchievable` の 3 predicate は `RelayCFBinningBody.lean` で再利用済 (verbatim 確認)。**predicate 削除は禁止**、Phase 2.3 は `@audit:retract-candidate(load-bearing-predicate)` 付与 + 散文注記のみ。Relay family の sweep agent (別 session) が Relay 側を incidental migration するまで 3 predicate は API 残存。これに加えて Phase 2.x ripple で Relay 側 file (`RelayCFBinningBody.lean:348` `wyner_ziv_binning_via_covering_packing` 直接呼出) が transitive sorry になる事象を **触らず散文も追加しない** (Relay 側 sweep agent の責務)。
- **L-MIG-3 (Phase C/D closure と方向衝突)**: 本 plan の sorry 化が `wyner-ziv-discharge-moonshot-plan.md` / `wyner-ziv-convexity-discharge-moonshot-plan.md` の進行と衝突 (例: discharge 側が `IsWynerZivBinningAchievable` predicate を closure 入口として現役利用、または de-circularized `wyner_ziv_converse_n_letter` の load-bearing predicate を直接 closure する設計に変更) した場合、本 plan は Phase 2.2 / 2.3 を pause、discharge 側 plan の signature を変更しない範囲で predicate を residual 化する別レシピを検討。Phase 1.5 (staged) は影響を受けない (predicate を残すため)。
- **L-MIG-4 (Approach 変更: pilot scope 縮減)**: Phase 1.5 / 2 が 1-2 session で完走しない / honesty-auditor が DEFECT を多発させる場合、`WynerZivAchievability.lean` の tier 5 defect 2 件 (Phase 2.1) のみで pilot を close し、Converse + ConverseChain + Binning/Covering/Packing 系の sweep は後続 session に分離 (Hoeffding pilot の L-MIG-4 相当)。または file 単位で 1 file ずつ閉じて段階的に commit (`HoeffdingInteriorBody.lean 4 件のみで pilot を close` の前例参照)。

## 未決事項

planner が判断つかない事項を列挙。実装 / auditor 委任で済む項目は明記。

1. **🟢ʰ 3 件の docstring refine 強度** (auditor 判定対象 + planner 提案):
   - `WynerZivConverse.lean:30/68/89` の `(honest-🟢ʰ entropy-level input)` 言及を削除するのは決定。残された散文 ("the per-letter Jensen plumbing that produces this scalar inequality is a real Mathlib gap" 等) は load-bearing 性の self-acknowledgment として **残す**か、Phase 2.3 で付与する `@audit:retract-candidate(load-bearing-predicate)` のみに集約して docstring 散文を圧縮するか。planner 推奨: **散文は残す** (predicate の意味論的説明として有用、retract-candidate は付与する) — 但し "honest-🟢ʰ" という tier 4 vocabulary は完全削除。auditor 判定対象。

2. ~~**境界判定 2 件 (`wyner_ziv_tendsto_chain` / `wzAchievability_random_binning_body`) の `@residual` 付与の要否** (auditor 判定対象):~~ → **2026-05-26 Round 4 closure 済 (判断ログ #2)**: 両者 Tier 1 `@audit:ok` 到達。
   - ~~`wyner_ziv_tendsto_chain` は純 forwarder で `wyner_ziv_tendsto` (Phase 1 でタグ削除済 = V/C 認定済) への pass-through。pass-through 自体は構造的に non-load-bearing だが、`@audit:staged(wyner-ziv-load-bearing)` 元タグが意味するのは upstream chain 内の load-bearing 性。Phase 1.5 暫定で sorry + `@residual(plan:...)` を付与する設計だが、auditor が「pure forwarder、residual 不要」と判定すれば降格 (タグ削除のみ)。~~ → 「pure forwarder、`@residual` 不要」確定、body `le_antisymm h_chain_conv h_ach` で proof done。
   - ~~`wzAchievability_random_binning_body` の `h_typ_prob` / `h_bin_prob` は `μ.real (...) ≤ ε` 形 = 確率値の bound (regularity に近い)。Hoeffding pilot の variational hyp 判定例 (`hoeffding_tradeoff_sandwich` 等) の延長で auditor 判定。~~ → 「regularity-only、non-load-bearing」確定、body 4-line `wzAchievability_decoder_fail_le` + `add_le_add` calc で proof done。

3. **predicate deprecate 方針** (user 確認 + Relay family sweep 連動):
   - 12 predicate のうち 3 件 (`IsWynerZivBinning*`) は cross-family consumer ありで削除不可。残り 9 件は Wyner–Ziv family 内 closed。Phase 2.3 で全 12 件に `@audit:retract-candidate(load-bearing-predicate)` 付与 (削除しない、history record として残す) はデフォルト推奨。**user 確認待ち**: 9 件の family 内 predicate を将来的に削除するなら別 session で deprecate plan を立てる (本 plan の scope 外)。

4. **proof done を本 plan で目指さない方針の明示確認** (user 確認):
   本 plan の DoD は **type-check done** のみ。Wyner–Ziv 系の analytical closure (Csiszár sum identity / `R_WZ(D)` 凸性 / 三項 typicality + AEP) は **未着手のまま** で本 plan は close する。`wyner-ziv-moonshot-plan.md` の Phase D pass-through 状態 + `wyner-ziv-discharge-moonshot-plan` / `wyner-ziv-convexity-discharge-*` の defer 状態を変えない。

5. **caller drift 規模予測** (Phase 2.x で実測):
   現在の `rg` 観測:
   - `WynerZivDischarge.lean` (15 file group の最終 wrapper、要 verbatim 確認)
   - `WynerZivAchievabilityBridge.lean` (achievability bridge)
   - `WynerZivDecoderFailureAssembly.lean` (decoder failure assembly)
   - `WynerZivConvexityBody.lean` / `WynerZivCondEntDiffConvexBody.lean` / `WynerZivObjectiveConvexityBody.lean` (convexity 系 — `wyner-ziv-convexity-discharge-moonshot-plan.md` 配下、本 plan で sorry 化される `wyner_ziv_converse_*` を参照する可能性)
   - cross-family: `RelayCFBinningBody.lean` のみ確認済、その他 LZ78 系 (`LZ78ZivInequality.lean` / `LZ78ConverseDischarge.lean`) は名前ヒットのみで実依存は要 Phase 2.x 確認。
   想定 caller drift 規模: 5-15 declaration が transitive sorry 化、Phase 2.x で散文化対応に 30-60 行追記。**1 session で完走可能 (中央予測)**、L-MIG-4 発動なし。

## 判断ログ

書く頻度: 方針変更 / 撤退ライン発動 / 当初仮定の修正があったとき。append-only。

1. **2026-05-25 plan 起草**: lean-planner (本 session、docs-only) が `InformationTheory/Shannon/WynerZiv*.lean` 15 file の legacy tag 22 件 (suspect 6 + staged 13 + 🟢ʰ 3) を verbatim 読込で per-declaration 分類。
   - **既存 sorry 計数**: word-boundary `rg -nw 'sorry'` で 2 hit、全て docstring 内文字列 (`WynerZiv.lean:34` `0 sorry 発行` / `WynerZivBinningBody.lean:69` `in 0 sorry`)、実 sorry 0 件。Pilot Pattern D 適用済。
   - **tier 5 defect 2 件 (planner 段階で inline 発見)**: `wyner_ziv_achievability_rate` (line 61) と `wyner_ziv_achievability_existence` (line 82) — 仮説型 ≡ 結論型 + name laundering の二重 defect。CLAUDE.md「検証の誠実性」inline detection rule に従い在庫表で明示、Phase 2.1 で `@residual(defect:circular)` 付き sorry 化として handling。
   - **cross-family dependency 発見**: `RelayCFBinningBody.lean:127/195/262` が `IsWynerZivBinning{Covering,Packing,Achievable}` 3 predicate を re-namespacing で再利用。L-MIG-2 (predicate 削除での大量 drift) を **必須回避** — Phase 2.3 で retract-candidate 付与のみ、削除しない設計に確定。
   - **3 種混在 sweep 順序**: V → S+H → P (tier 5 → load-bearing consumer) の順を Approach で確定、Hoeffding (suspect 純) + Huffman (staged 純並行) の延長として一貫性を保つ。

2. **2026-05-26 Round 4 closure (境界判定 2 件 proof done 到達)**: Round 4 sweep
   完了後の状態確認で `wyner_ziv_tendsto_chain` (`WynerZivConverseChain.lean:656`)
   + `wzAchievability_random_binning_body` (`WynerZivBinningBody.lean:493`) の両者
   が Tier 1 `@audit:ok` (0 sorry / 0 @residual / 0 @audit:* other) に到達済を
   verbatim 確認。
   - `wyner_ziv_tendsto_chain`: body `le_antisymm h_chain_conv h_ach` — 純
     forwarder pass-through 構造で 2 hyp は precondition (regularity)、本 plan
     未決事項 2 で予想された「pure forwarder、`@residual` 不要」判定が proof
     done として確定。`@audit:ok` docstring が「No `sorry`, no `@residual`.
     Genuine 0/0 proof done.」を明示。
   - `wzAchievability_random_binning_body`: body 4-line calc block
     (`wzAchievability_decoder_fail_le` + `add_le_add` composition) — `h_typ_prob`
     / `h_bin_prob` は probability bound = regularity precondition、本 plan 未決
     事項 2 で予想された「regularity-only、non-load-bearing、body constructive
     復元」判定が proof done として確定。`@audit:ok` docstring が「The hyps do
     not bundle the conclusion — they supply the per-set bounds that get added」
     を明示。
   - 影響: Phase 1.5.4 / 1.6.3 を closed mark、集計の「境界判定 2 件」→ 0 件、
     L-MIG-1 撤退ライン消化、未決事項 2 closure。本 plan の in-flight tracker
     から両 declaration を除外。

<!-- 後続セッションで判断変更があれば下記に追記 (append-only):
3. **YYYY-MM-DD <要点>**: <変更理由 + 撤退ラインへの紐付け>。
-->
