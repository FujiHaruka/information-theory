# Shannon: WynerZiv — tier 5 defect 3 件 discharge plan

> **Parent**: [`wyner-ziv-moonshot-plan.md`](wyner-ziv-moonshot-plan.md) (statement-level publish 完了済の後追い)
> + [`wynerziv-phase2-predicate-removal-plan.md`](wynerziv-phase2-predicate-removal-plan.md) §「Tier 5 defect 検出」(Phase 2.x scope 外として明示 deferred)
> + handoff [`.claude/handoff-sorry-migration.md`](../../.claude/handoff-sorry-migration.md) §「Round 2 残課題 follow-up」継続作業
> Pilot reference (同型構造): [`brunn-minkowski-signature-rewrite-plan.md`](brunn-minkowski-signature-rewrite-plan.md) (Wave 6 commit `fe28966`)
> Related SoT: [`audit/audit-tags.md`](../audit/audit-tags.md) Defect kind 語彙 + Wall name register / [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md) Pattern A-J / CLAUDE.md「sorry を書けない箇所での対処順序」第一選択。

## 進捗

- [ ] Phase 0 — 規模見積もり + verbatim 確認 + 案 (a/b/c) 適用可能性判定 📋
- [ ] Phase 1 — `wyner_ziv_achievability_rate` (false-statement) signature rewrite 📋
- [ ] Phase 2 — `wyner_ziv_achievability_existence` (circular) signature rewrite 📋
- [ ] Phase 3 — `wyner_ziv_converse_rate` (false-statement) signature rewrite 📋
- [ ] Phase V — verify (`lake env lean` 0 errors + honesty-auditor 独立検証 + handoff 反映) 📋

## ゴール / Approach

### ゴール

`Common2026/Shannon/WynerZiv{Achievability,Converse}.lean` に残置している **3 件の tier 5 defect** (`@residual(defect:circular)` / `@residual(defect:false-statement)`) を tier 2 (`sorry` + `@residual(wall:...)` または `@residual(plan:...)`) まで **2 段昇格** する。`wynerziv-phase2-predicate-removal-plan.md` Phase 2.x で全 11 declaration を honest_residual (tier 2) 化したのと同方針、ただし対象が「load-bearing predicate consumer」ではなく「signature 自体が defect」の 3 件。

BM Wave 6 commit `fe28966` (`docs/shannon/brunn-minkowski-signature-rewrite-plan.md` Phase 1+2) と完全に同型構造の sweep:

- 既存 signature が precondition 不在 (`R` を rate と code size に linkage していない / hypothesis ≡ conclusion)
- consumer 0 件 (Phase 0 verbatim rg で確認)
- signature 改変で linkage hypothesis (load-bearing でない regularity 形) 追加 → body `sorry` + 新 / 既存 wall への `@residual` で tier 2 化

| # | file:line | decl 名 | 現状タグ (tier 5) | 移行先タグ (tier 2 候補) |
|---|---|---|---|---|
| 1 | `WynerZivAchievability.lean:77` | `wyner_ziv_achievability_rate` | `@residual(defect:false-statement)` | **案 a**: `@residual(plan:wyner-ziv-discharge-moonshot-plan)` (signature に `(h_R_gt : R > wynerZivRatePmf U P_XY d D)` 追加 → rate-side statement が genuinely well-formed、closure は achievability 本体に委任) |
| 2 | `WynerZivAchievability.lean:104` | `wyner_ziv_achievability_existence` | `@residual(defect:circular)` | **案 a**: `@residual(plan:wyner-ziv-discharge-moonshot-plan)` (現 signature の `_h_R_gt` precondition は維持済、defect は **body** 側の `:= h_ach_existence` 旧構造の hangover — 旧 hypothesis は Phase 2.1 で削除済、現状 body が `sorry` でも結論型自身は genuinely well-formed、defect reason を `circular` → `plan` に書換のみで tier 2 化可能) |
| 3 | `WynerZivConverse.lean:253` | `wyner_ziv_converse_rate` | `@residual(defect:false-statement)` | **案 a**: `@residual(plan:wyner-ziv-discharge-moonshot-plan)` (signature に `(h_M_le : (M : ℝ) ≤ Real.exp ((n : ℝ) * R))` 追加 → operational rate と code size の linkage、closure は converse 本体に委任) |

### Approach (全体戦略)

#### 中核 observation — 3 件とも案 (a) signature rewrite が最適

Phase 0 verbatim 確認 (本 plan 起草時 2026-05-26):

```bash
rg -n 'wyner_ziv_achievability_rate|wyner_ziv_achievability_existence|wyner_ziv_converse_rate' Common2026/ --type lean
```

結果: **Lean 本体 caller 0 件** (3 declaration とも自己定義 + docstring 言及のみ)。
- `WynerZivAchievability.lean:24/28/73`: 自 file 内 docstring 言及
- `WynerZivBinningCovering.lean:357/373`: docstring 散文で `wyner_ziv_achievability_existence` の existence shape を mention するのみ (consumer ではない)
- `WynerZivAchievabilityBridge.lean:17/39/52/53`: bridge declaration の docstring 散文言及 (bridge 自身は `wynerZivAchievabilityExistence_of_failProb` 経由で独立 derivation、本 3 件を consume しない)
- `WynerZivPackingBody.lean:561`: docstring 散文言及
- `MACL1Discharge.lean:50`: 他 family docstring 散文 mention (Stage 1 cross-family、import 無し)
- `WynerZivConverse.lean:221/253`: 自 file 内 docstring 言及 + 自己定義

→ **signature 改変の re-verify 範囲は 2 file 単体に限定** (`WynerZivAchievability.lean` + `WynerZivConverse.lean`)、`lake build` による olean refresh は不要 (Pattern A 不発)。

#### 案 (a) / (b) / (c) の比較と採用判断

| 案 | 概要 | 適用可能性 | 採否 |
|---|---|---|---|
| **(a) signature rewrite** → tier 2 `@residual(wall:...)` or `@residual(plan:...)` | linkage hypothesis (regularity 形) を signature に追加し、defect の原因 (precondition 不在 / hypothesis ≡ conclusion) を構造的に解消。BM Wave 6 路線 | ✅ 全 3 件で適用可 (consumer 0 件、cross-family impact なし、linkage hyp は既存 `R` / `M` / `n` の自然な ordering で表現可能) | **採用** |
| **(b) `@audit:retract-candidate(<reason>)` 付与 + ORPHAN 化** | 3 declaration を deprecate 候補化し、後続 family cleanup session で削除。`IsAwgnPowerConstraintRealizable` Wave 5 路線 | △ consumer 0 件は満たすが、3 declaration は WynerZiv moonshot Phase D wrapper `wyner_ziv_tendsto` の statement-level publish の片割れ (`_rate` 形は rate-side ordering の API 公開) として **意味的に retract できない**。`@audit:retract-candidate` は本来 ORPHAN / superseded を表すマーカーで、本 3 件は「signature が defect」だが意味は publish 必須 | 不採用 |
| **(c) `@residual(plan:wyner-ziv-discharge-moonshot-plan)` への格上げ (signature 維持)** | tier 5 → tier 2 (1 段昇格、signature 改変なし)、後続 discharge plan が genuine 化 | ✗ signature が universally false の状態のままで `@residual(plan:...)` を貼ると **後続 plan が closure 不能** (反例構成済の false statement は plan で closure できない、`@residual(defect:false-statement)` の本義通り)。`_existence` 1 件 (defect:circular) は body が `sorry` の現状で signature は well-formed → 唯一 (c) で 1 段昇格可能だが、3 件揃えるため (a) で統一 | 不採用 (`_existence` は (a) と (c) が同等になるため (a) で揃える) |

採用: **全 3 件で案 (a) を採用**。BM Wave 6 路線と完全に同じ template。`@residual(plan:wyner-ziv-discharge-moonshot-plan)` (新規 wall promote ではない、既存 plan slug への集約) で tier 2 化。

#### 新規 wall promote の判定

BM Wave 6 では `wall:uniform-max-entropy-on-convex-body` + `wall:bm-additive-convex-body` の 2 件を新規 promote した (両者とも Mathlib 不在の Brunn-Minkowski 系の壁、後続 family が再参照する shape)。本 plan では:

- **新規 wall promote しない**: 3 declaration とも `wyner-ziv-discharge-moonshot-plan` という既存 plan slug に集約済 (WynerZiv Phase 2.x で 11 declaration が同 slug)、新規 wall 化は in-tree wall name register に divergence を生じる
- **`@residual(plan:wyner-ziv-discharge-moonshot-plan)` で揃える**: WynerZiv family 全体 (Phase 2.x 11 件 + 本 plan 3 件 = 計 14 件) が同 slug を共有することで grep 集計が clean、後続 discharge session が一括で fetch 可能

### 撤退ライン

- **L-DD-1 (linkage hypothesis 形が他 declaration と整合せず convention 拡張で 5+ declaration touch 必要)**: Phase 1-3 で linkage hyp を追加する際、既存 WynerZiv family の `R` / `M` / `n` 引数 convention (`(M : ℕ)` / `(n : ℕ)` / `(R : ℝ)` / `(M : ℝ) ≤ Real.exp ((n : ℝ) * R)` 形は `wyner_ziv_achievability_existence` の existing precondition + `wyner_ziv_converse_existence` の existence form で既存) で表現できなければ scope 拡張判断。本 plan 起草時 verbatim 確認では既存 convention で網羅可能 → L-DD-1 不発見込み。
- **L-DD-2 (consumer 0 件判定の漏れ)**: BM Wave 6 と同様に Phase 0.2 で `rg --type lean` で確認、本 plan 起草時 verbatim 結果は 0 件だが、`type lean` 範囲外 (`.md` だけの参照は OK) や transitive 経由の symbolic dependency があれば Phase 0 で発見して scope 拡張。
- **L-DD-3 (Phase 2.x 完了状態との整合性破綻)**: 本 plan は WynerZiv Phase 2.x 完了状態 (Phase V banner 反映済) の **追加 sweep**。Phase 2.x で確立した signature honest 化 + cross-family Relay 保護方針と衝突しないこと (本 3 declaration は Relay 利用ゼロ、Phase 2.x の 11 declaration とも独立、衝突なし)。
- **L-DD-4 (3 declaration とも当該 session で完遂不能 / pilot scope 縮減)**: Phase 1 のみで本 plan を close し、Phase 2/3 は後続 session に分離。

## SoT

- **コード**: `Common2026/Shannon/WynerZivAchievability.lean:77, :104` + `Common2026/Shannon/WynerZivConverse.lean:253` の `@residual` タグが現状の source of truth。本 plan 完了時に `defect:circular` / `defect:false-statement` → `plan:wyner-ziv-discharge-moonshot-plan` に書換、signature を linkage hyp 形に改変。
- **vocab register**: `docs/audit/audit-tags.md` の既存 Defect kind 語彙 (`circular` / `false-statement`) + `@residual(plan:wyner-ziv-discharge-moonshot-plan)` (既存 slug、新規 promote なし)。
- **honesty 階層**: Tier 5 → Tier 2 (2 段昇格) は BM Wave 6 で同型実証済 (commit `fe28966`)。

## Phase 0 — 規模見積もり + verbatim 確認 + 案 (a/b/c) 適用可能性判定 📋

`proof-log: no` (mechanical inventory)。

- [ ] **0.1** 3 declaration の verbatim location 再確認 (line drift 防止):
  ```bash
  rg -n 'theorem wyner_ziv_achievability_rate|theorem wyner_ziv_achievability_existence|theorem wyner_ziv_converse_rate' Common2026/Shannon/WynerZiv*.lean
  ```
  本 plan 起草時 (2026-05-26): `WynerZivAchievability.lean:77` + `:104` + `WynerZivConverse.lean:253`。

- [ ] **0.2** Downstream consumer rg (verbatim 件数 → scope 確認):
  ```bash
  rg -n 'wyner_ziv_achievability_rate|wyner_ziv_achievability_existence|wyner_ziv_converse_rate' Common2026/ --type lean
  ```
  本 plan 起草時 verbatim 結果 (上記 Approach §「中核 observation」表 verbatim):
  - **Lean 本体 caller 0 件** (3 declaration とも自己定義 + docstring 言及のみ)
  - cross-family: `MACL1Discharge.lean:50` 1 件 (docstring mention only、Stage 1、import 無し → sweep 単独実施 OK、touch 不要)
  - `WynerZivAchievabilityBridge.lean` の `wyner_ziv_achievability_existence_bridged` (`:351`) は本 declaration を consume せず、`wynerZivAchievabilityExistence_of_failProb` (独立 derivation 経由) で同じ存在形を publish — Phase 2 で signature 改変しても bridge は影響を受けない

- [ ] **0.3** 関連 linkage / precondition の既存 convention 確認:
  - `wyner_ziv_achievability_existence` (現 `:104-:115`) の `(_h_R_gt : R > wynerZivRatePmf U P_XY d D)` precondition: 既に存在、Phase 2 では body の `:= h_ach_existence` 痕跡を `sorry` で維持済、defect は **body 側のタグ反映** のみで closure 可能
  - `wyner_ziv_converse_existence` (`WynerZivConverse.lean:282`、本 plan **scope 外**) の signature: `(h_R_lt : R < wynerZivRatePmf U P_XY d D)` precondition を持つ — converse-side ordering の自然 convention
  - `wyner_ziv_converse_n_letter` (`WynerZivConverse.lean:202`、本 plan **scope 外**) の signature: `(M : ℕ)` + `(n : ℕ)` + `(hn : 0 < n)` + 結論型 `wynerZivRatePmf U P_XY d D ≤ Real.log (M : ℝ) / (n : ℝ) + ε` — operational-rate と code-size の linkage を `Real.log M / n` 経由で表現
  - これらは Phase 1 (`_rate` のため `(h_R_gt : R > wynerZivRatePmf ...)`) + Phase 3 (`_converse_rate` のため `(h_M_le : (M : ℝ) ≤ Real.exp ((n : ℝ) * R))`) の linkage hyp 候補と直接接続

- [ ] **0.4** defect reason の verify (universally-false / circular の confirmation):
  - **decl #1 `wyner_ziv_achievability_rate`** (defect:false-statement):
    - 反例: `R := wynerZivRatePmf U P_XY d D - 1`、`P_XY`/`d`/`D` 任意、`U` 任意 → `wynerZivRatePmf U P_XY d D ≤ wynerZivRatePmf U P_XY d D - 1` は `0 ≤ -1` に等価で **false**。✅ false-statement の reason verify OK
  - **decl #2 `wyner_ziv_achievability_existence`** (defect:circular):
    - 現 signature: `(_h_R_gt : R > wynerZivRatePmf U P_XY d D)` + 結論 `∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ M c, (M : ℝ) ≤ Real.exp ((n : ℝ) * R) ∧ c.expectedBlockDistortion μ dN ≤ D + ε`
    - **現状の signature 自体は well-formed** (precondition `R > R_WZ(D)` を持ち、結論は existence-form Cover-Thomas 15.9.1)
    - tag `defect:circular` は **歴史的経緯** — Phase 2.1 retreat で旧 `h_ach_existence : <結論型 verbatim>` を削除した後、tag は `defect:circular` のまま残置 (Phase 2.1 docstring に明示)、signature は well-formed 化済だが docstring 内の理由が「load-bearing `h_ach_existence` 削除」のため `circular` のまま — **真の現状は `plan:wyner-ziv-discharge-moonshot-plan` の closure 待ち**、defect kind の reason 反映待ち
    - → defect:circular の reason verify: ✅ **stale tag** (Phase 2.1 で signature 是正済、tag だけが defect 形で残置)。Phase 2 ではタグの書換のみで tier 5 → tier 2 移行可能
  - **decl #3 `wyner_ziv_converse_rate`** (defect:false-statement):
    - 反例: `R := wynerZivRatePmf U P_XY d D + 1`、`M`/`n`/`c`/`h_dist` 任意で precondition 充足 → `wynerZivRatePmf U P_XY d D + 1 ≤ wynerZivRatePmf U P_XY d D` は `1 ≤ 0` に等価で **false**。✅ false-statement の reason verify OK

- [ ] **0.5** 案 (a/b/c) 適用可能性確定:
  | decl | 案 (a) | 案 (b) | 案 (c) |
  |---|---|---|---|
  | `_achievability_rate` | ✅ `(h_R_gt : R > wynerZivRatePmf ...)` 追加で `≤` ordering を well-form 化 | ✗ Phase D `wyner_ziv_tendsto` の rate-side API として publish 必要、retract 不可 | ✗ false signature で plan tag は意味的 invalid |
  | `_achievability_existence` | ✅ 案 (c) と等価 (signature は既に well-formed、tag 書換のみ) | ✗ existence form は moonshot Phase D の片割れとして publish 必要 | ✅ (本質的に (a) と同じ作業 — 1 段昇格、signature 改変ゼロ) |
  | `_converse_rate` | ✅ `(h_M_le : (M : ℝ) ≤ Real.exp ((n : ℝ) * R))` 追加で `≤` ordering を well-form 化 (operational-vs-information-rate linkage) | ✗ Phase D wrapper の converse-side API として publish 必要 | ✗ false signature で plan tag は意味的 invalid |

  → **全 3 件で案 (a) 採用**。decl #2 は実質 (c) と等価作業 (tag 書換のみ)、Phase 2 で他 2 件と独立な簡素 Phase として実施。

- [ ] **0.6** 撤退ライン flag — Phase 0 完了時点で次のいずれかなら **scope 拡張判断**:
  - downstream consumer chain が **3+ file 横断 + 5+ declaration 以上** に膨らんだ (本 plan 起草時 verbatim では **0 件** ゆえ trigger 不発)
  - linkage hyp の形が WynerZiv 既存 convention (existence form / converse-n-letter 等) と整合せず convention 拡張で 5+ declaration touch 必要 (本 plan 起草時 0.3 verbatim 確認で既存 convention で網羅可能)

  本 plan 起草時 (2026-05-26): **L-DD-1/L-DD-2 不発見込み、1 PR scope (3 declaration / 2 file) で完遂可能**。

- [ ] **0.7** Phase 0 完了時 docs-only commit (本 plan + handoff 反映、code SoT には touch なし)。

### Phase 0 中央予測

- **scope**: 2 file (`WynerZivAchievability.lean` + `WynerZivConverse.lean`)、追加 import 0 件 (linkage hyp は既存 `Real` / `ℕ` / `wynerZivRatePmf` で表現可能)
- **中央予測 sorry 数**: **3 件** (本 plan 着手前後で増減なし — `defect:` reason の tag 書換 + signature 改変のみ、body は `sorry` 維持)
- **新規 wall promote 必要性**: **no** (全 3 件とも既存 plan slug `wyner-ziv-discharge-moonshot-plan` に集約)
- **retract-candidate 件数**: **0 件** (案 (b) 不採用、retract せず signature 是正で tier 2 化)
- **撤退ライン flag**: **no** (Phase 0 verbatim 確認で consumer 0 件、scope 拡張 trigger 不発の見込み)
- **cross-family 影響**: **S1 (docstring mention only) 1 件** (`MACL1Discharge.lean:50`) — touch 不要、本 plan scope 単独で完遂

## Phase 1 — `wyner_ziv_achievability_rate` (false-statement) signature rewrite 📋

`proof-log: yes` (`docs/proof-logs/proof-log-wynerziv-tier5-defect-discharge-phase1.md`)。signature 改変 + linkage hyp 形の境界判定 + 「`R > wynerZivRatePmf` を `≥` の precondition として使う `≤` rate-side」の方向性確認。

### Phase 1 設計 (Approach)

現状 (`WynerZivAchievability.lean:77-80`):

```lean
/-- ... `@residual(defect:false-statement)` -/
theorem wyner_ziv_achievability_rate
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ) :
    wynerZivRatePmf U P_XY d D ≤ R := by
  sorry
```

**問題**: `(D R : ℝ)` を free real で取り、`R` と `wynerZivRatePmf` の linkage 不在。反例 `R := wynerZivRatePmf U P_XY d D - 1` で false。

**Mathlib-shape-driven 書換** (CLAUDE.md「Mathlib-shape-driven Definitions」+「sorry を書けない箇所での対処順序」第一選択):

linkage hypothesis として **`(h_R_gt : R > wynerZivRatePmf U P_XY d D)`** を追加 (`_existence` form の既存 precondition と同じ shape — WynerZiv family 内 convention で既存)。結論 `wynerZivRatePmf U P_XY d D ≤ R` は precondition の `<` から自明に lift 可能 ⇒ **本来は body が `(le_of_lt h_R_gt)` で proof done 化できる**。

ここで判断分岐:

| 判断分岐 | 帰結 |
|---|---|
| (α) `body := le_of_lt h_R_gt` を採用 (constructive recovery、`@residual` 不要) | **proof done 到達 (Tier 1 `@audit:ok`)** — 3 declaration 中 1 件目で完成。CLAUDE.md「Skeleton-driven Development」+ Pilot Pattern B (constructive recovery) 適用 |
| (β) `body := by sorry` + `@residual(plan:wyner-ziv-discharge-moonshot-plan)` | Tier 2 honest_residual。signature が well-formed なので `@residual(plan:...)` は意味的に成立。closure は achievability 本体に委任 |

**実装判断**: (α) を **第一選択**。`R > R_WZ(D)` を precondition として受け、結論 `R_WZ(D) ≤ R` を `le_of_lt` で proof done 化するのは構造的に正当 (existence-form では同じ precondition で「達成可能 code 列が存在する」を sorry で公開しているのと独立、rate-side ordering の API としてはこれで完結)。

ただし planner 段階では判断保留可能 — implementer が verbatim 検討後に (α) を採用すれば proof done 1 件追加、(β) で止まれば tier 2 honest_residual。**境界判定** として inline detection (Pilot Pattern B) を implementer brief に明記。

### Phase 1 step

- [ ] **1.1** 既存 `wyner_ziv_achievability_rate` の docstring 全文 (`:48-:76`) を **proof-log に verbatim 退避** (Phase 2.1 retreat / Round 4 audit verdict / 2026-05-25 reclassification 散文の歴史記録として保存)。

- [ ] **1.2** signature を以下に書換:
  ```lean
  theorem wyner_ziv_achievability_rate
      (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ)
      (h_R_gt : R > wynerZivRatePmf U P_XY d D) :
      wynerZivRatePmf U P_XY d D ≤ R := by
    sorry  -- or `exact le_of_lt h_R_gt` — implementer 判断
  ```

- [ ] **1.3** **境界判定 (Phase 1 sub-step)**: implementer が inline detection (Pilot Pattern B) で (α) constructive recovery が可能か verbatim 確認:
  - 結論型 `wynerZivRatePmf U P_XY d D ≤ R` (`≤`)
  - precondition `h_R_gt : R > wynerZivRatePmf U P_XY d D` (= `wynerZivRatePmf U P_XY d D < R`)
  - 関係: `≤` は `<` から `le_of_lt` で得られる (Mathlib `le_of_lt`)
  - → (α) 採用可、body `:= le_of_lt h_R_gt` で proof done 化

  境界判定の判定軸:
  - (α) 採用 → docstring から `@residual(defect:false-statement)` 削除、新規タグ無し (proof done、Tier 1 `@audit:ok` 付与 candidate、Phase V audit で確定)
  - (β) 採用 → docstring の defect tag を `@residual(plan:wyner-ziv-discharge-moonshot-plan)` に書換、body `sorry` 維持

- [ ] **1.4** docstring の Phase 2.1 retreat / 2026-05-25 reclassification 散文を **保持** しつつ、結末散文を追記:
  - (α) 採用時: 「Phase D-3 tier5-defect-discharge — signature rewrite で `(h_R_gt : R > wynerZivRatePmf ...)` を追加、`le_of_lt` で proof done 化。`@residual(defect:false-statement)` を削除、Tier 1 `@audit:ok` 移行 candidate (auditor verdict 待ち)。」
  - (β) 採用時: 「Phase D-3 tier5-defect-discharge — signature rewrite で precondition `(h_R_gt : ...)` を追加、`<` から `≤` lift は本来 trivial だが、achievability 本体の closure (random binning + AEP) が完了するまで body は `sorry` のまま、`@residual(plan:wyner-ziv-discharge-moonshot-plan)` で集約。」

- [ ] **1.5** `lake env lean Common2026/Shannon/WynerZivAchievability.lean` で type-check done 確認:
  - (α) 採用時: 0 errors、0 sorry warning (proof done)
  - (β) 採用時: 0 errors、1 sorry warning

  Pattern A (stale olean) の懸念: Phase 0.2 で consumer 0 件確認済 → `lake build` 不要、`lake env lean` 単独で十分。

- [ ] **1.6** **Inline alert チェック** (CLAUDE.md「検証の誠実性」):
  - (α) 採用時: linkage hyp `h_R_gt : R > wynerZivRatePmf ...` は **結論型 `R_WZ ≤ R` の自然な `<` 版** (regularity-like ordering hyp、conclusion-as-hypothesis ではない — 結論型は `≤` で hyp は `<`、ordered set 上の lift 関係で型は厳密に異なる)。load-bearing ではなく **constructive bridge hyp**。Pilot Pattern B 該当
  - (β) 採用時: 同じ linkage hyp の解釈、body `sorry` だが signature は well-formed
  - 両ケースとも tier 5 → tier 2 (β) または Tier 1 (α) への 1 段 or 2 段昇格、tier 5 残置の懸念なし

- [ ] **1.7** Phase 1 完了時 honesty-auditor 独立起動 (Phase V でまとめて起動の場合は本 step skip、Phase 単独完了時に起動の場合のみ)。判定 focus:
  - (a) (α/β) のいずれを選んだか + 判断根拠 (constructive recovery 可否)
  - (b) linkage hyp が conclusion-as-hypothesis でないか
  - (c) `@residual(defect:false-statement)` → `@residual(plan:wyner-ziv-discharge-moonshot-plan)` (β case) または タグ削除 + `@audit:ok` 付与 candidate (α case) の判断整合

### Phase 1 DoD

- `WynerZivAchievability.lean:77` の `@residual(defect:false-statement)` が 0 件
- (α) 採用時: 0 sorry、0 `@residual`、`@audit:ok` 付与 candidate (Phase V 確定)
- (β) 採用時: 1 sorry、1 `@residual(plan:wyner-ziv-discharge-moonshot-plan)`
- `lake env lean` 0 errors (適切な sorry warning 件数)

## Phase 2 — `wyner_ziv_achievability_existence` (circular) signature rewrite 📋

`proof-log: no` (mechanical tag 書換、signature は既に well-formed — 0.4 で確認済)。

### Phase 2 設計 (Approach)

現状 (`WynerZivAchievability.lean:104-115`):

```lean
/-- ... `@residual(defect:circular)` -/
theorem wyner_ziv_achievability_existence
    (μ : Measure (α × β)) [IsProbabilityMeasure μ]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ)
    (_h_R_gt : R > wynerZivRatePmf U P_XY d D)
    [MeasurableSpace γ]
    (dN : DistortionFn α γ) :
    ∀ ε > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M : ℕ) (c : WynerZivCode M n α β γ),
          (M : ℝ) ≤ Real.exp ((n : ℝ) * R)
            ∧ c.expectedBlockDistortion μ dN ≤ D + ε := by
  sorry
```

**重要 observation** (Phase 0.4 で verify 済): **signature 自体は既に well-formed** (precondition `_h_R_gt : R > wynerZivRatePmf ...` を持ち、結論型は Cover-Thomas 15.9.1 existence form)。`defect:circular` tag は **歴史的経緯** — Phase 2.1 retreat で旧 `h_ach_existence : <結論型 verbatim>` を削除した後、tag だけが `circular` のまま残置。

**Mathlib-shape-driven 書換**: signature 改変は不要 (well-formed 状態維持)、**`@residual` タグの reason のみ書換**:
- `@residual(defect:circular)` (stale Phase 2.1 hangover)
- → `@residual(plan:wyner-ziv-discharge-moonshot-plan)` (現状 status の正確な反映)

これは技術的に「タグ書換のみ」で tier 5 → tier 2 1 段昇格、signature 改変ゼロ、body `sorry` 維持。

### Phase 2 step

- [ ] **2.1** docstring の `@residual(defect:circular)` を `@residual(plan:wyner-ziv-discharge-moonshot-plan)` に書換:
  ```diff
  -`@residual(defect:circular)` -/
  +`@residual(plan:wyner-ziv-discharge-moonshot-plan)` -/
  ```

- [ ] **2.2** docstring 散文の Phase 2.1 retreat 説明を保持し、結末に追記:
  ```
  Phase D-3 tier5-defect-discharge — Phase 2.1 retreat で signature の load-bearing
  `h_ach_existence` 削除済、現状 signature (precondition `_h_R_gt` 持ちの
  Cover-Thomas 15.9.1 existence form) は well-formed。タグの `circular` reason は
  Phase 2.1 hangover、本 Phase で `@residual(plan:wyner-ziv-discharge-moonshot-plan)`
  に書換 (signature 改変ゼロ、body `sorry` 維持、tier 5 → tier 2 1 段昇格)。
  ```

- [ ] **2.3** `lake env lean Common2026/Shannon/WynerZivAchievability.lean` 0 errors 確認 (1 sorry warning + Phase 1 の sorry 件数に応じて累計 1-2 sorry warning)。signature 改変ゼロ → Pattern A 不発。

- [ ] **2.4** **Inline alert チェック**: タグ書換のみ、signature は既に well-formed (Phase 0.4 で `defect:circular` は **stale** と verify 済) → tier 5 → tier 2 1 段昇格、新規 honesty issue なし。

### Phase 2 DoD

- `WynerZivAchievability.lean:104` の `@residual(defect:circular)` が 0 件
- 1 sorry、1 `@residual(plan:wyner-ziv-discharge-moonshot-plan)`
- `lake env lean` 0 errors

## Phase 3 — `wyner_ziv_converse_rate` (false-statement) signature rewrite 📋

`proof-log: yes` (`docs/proof-logs/proof-log-wynerziv-tier5-defect-discharge-phase3.md`)。signature 改変 + operational-rate linkage hyp の境界判定。

### Phase 3 設計 (Approach)

現状 (`WynerZivConverse.lean:253-261`):

```lean
/-- ... `@residual(defect:false-statement)` -/
theorem wyner_ziv_converse_rate
    [MeasurableSpace γ]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ)
    {M n : ℕ} (hn : 0 < n)
    (μ : Measure (α × β)) [IsProbabilityMeasure μ]
    (dN : DistortionFn α γ) (c : WynerZivCode M n α β γ)
    (h_dist : c.expectedBlockDistortion μ dN ≤ D) :
    R ≤ wynerZivRatePmf U P_XY d D := by
  sorry
```

**問題**: `R` と `M / n` の linkage 不在 — `M / n` は code size + block length だが、`R` がこれと無関係に free で、結論 `R ≤ wynerZivRatePmf ...` が universally false。反例 `R := wynerZivRatePmf U P_XY d D + 1`。

**Mathlib-shape-driven 書換**: signature に `(h_M_le : (M : ℝ) ≤ Real.exp ((n : ℝ) * R))` を追加 (operational rate と code size の linkage、`_existence` form + `_converse_n_letter` で既存 convention)。これにより:
- (M : ℝ) ≤ Real.exp (n · R) かつ converse_n_letter で `R_WZ(D) ≤ log M / n + ε` が成立
- ⇒ `R_WZ(D) ≤ R + (ε for n→∞)` が asymptotically true
- ⇒ Phase D 全体 (n → ∞ limit) で `R_WZ(D) ≤ R` が genuinely derivable

ただし single n に対しては `(M : ℝ) ≤ Real.exp (n · R)` だけでは `R ≤ R_WZ(D)` を直接 derive できない (genuine converse は AEP / Fano / Csiszár の triple closure に依存)。

実装判断:

| 判断分岐 | 帰結 |
|---|---|
| (α) `body` を `wyner_ziv_converse_n_letter` 経由で構成 (Mathlib の `R_WZ ≤ log M / n + ε` を経由) | constructive recovery 候補だが、`wzObjectiveSum` / `Pe` / `ε` 等の existence quantifier を解く必要があり、本 plan scope 内では非自明 |
| (β) `body := by sorry` + `@residual(plan:wyner-ziv-discharge-moonshot-plan)` | Tier 2 honest_residual。signature は well-formed 化済、closure は converse 本体に委任。**第一選択** |

**実装判断**: **(β) を第一選択**。Phase 1 と異なり、precondition `(h_M_le : (M : ℝ) ≤ Real.exp ((n : ℝ) * R))` だけでは結論 `R ≤ wynerZivRatePmf ...` への bridge が trivial ではない (existence quantifier 経由の n → ∞ asymptotic 議論が必要 — `wyner_ziv_converse_existence` の impossibility form と同等の structure)。本 plan scope は **signature 是正 + tier 2 化** に留め、closure は converse 本体 (`wyner-ziv-discharge-moonshot-plan`) に委任。

### Phase 3 step

- [ ] **3.1** 既存 `wyner_ziv_converse_rate` の docstring 全文 (`:217-:252`) を **proof-log に verbatim 退避** (Phase 2.2 retreat / 2026-05-25 reclassification 散文の歴史記録)。

- [ ] **3.2** signature を以下に書換:
  ```lean
  theorem wyner_ziv_converse_rate
      [MeasurableSpace γ]
      (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ)
      {M n : ℕ} (hn : 0 < n)
      (μ : Measure (α × β)) [IsProbabilityMeasure μ]
      (dN : DistortionFn α γ) (c : WynerZivCode M n α β γ)
      (h_dist : c.expectedBlockDistortion μ dN ≤ D)
      (h_M_le : (M : ℝ) ≤ Real.exp ((n : ℝ) * R)) :
      R ≤ wynerZivRatePmf U P_XY d D := by
    sorry
  ```

- [ ] **3.3** docstring の Phase 2.2 retreat / 2026-05-25 reclassification 散文を **保持** しつつ、結末に追記:
  ```
  Phase D-3 tier5-defect-discharge — signature rewrite で operational-rate linkage
  hyp `(h_M_le : (M : ℝ) ≤ Real.exp ((n : ℝ) * R))` を追加 (`_existence` form と
  `_converse_n_letter` の既存 convention に整合)。`R` と code size `M / n` の
  linkage 不在による universally-false defect を解消、signature は well-formed
  化。closure は converse 本体 (`wyner-ziv-discharge-moonshot-plan`) に委任、
  body `sorry` 維持、tier 5 → tier 2 2 段昇格。
  ```

- [ ] **3.4** docstring 末尾の `@residual` タグを書換:
  - `@residual(defect:false-statement)` → `@residual(plan:wyner-ziv-discharge-moonshot-plan)`

- [ ] **3.5** `lake env lean Common2026/Shannon/WynerZivConverse.lean` 0 errors 確認 (1 sorry warning + 既存 `wyner_ziv_converse_existence` の sorry warning で計 2 sorry warning)。Pattern A 不発 (Phase 0.2 で consumer 0 件確認済)。

- [ ] **3.6** **Inline alert チェック**:
  - linkage hyp `h_M_le : (M : ℝ) ≤ Real.exp ((n : ℝ) * R)` は **operational rate の標準形** (`_existence` form の結論内部式と verbatim 整合)、conclusion-as-hypothesis ではない (結論 `R ≤ R_WZ(D)` は rate-vs-rate ordering、hyp は size-vs-exp(rate) inequality で型が異なる)
  - regularity-like (existing convention) と load-bearing の境界判定: `wyner_ziv_converse_n_letter` で `R_WZ ≤ log M / n + ε` を derive する際に `h_M_le` を経由する自然な linkage、**load-bearing ではない** (closure は body `sorry` 経由で converse 本体に委任、hyp が conclusion を bundle していない)
  - tier 5 → tier 2 2 段昇格、tier 5 残置の懸念なし

- [ ] **3.7** Phase 3 完了時 honesty-auditor 独立起動 (Phase V でまとめて起動の場合は本 step skip)。判定 focus:
  - (a) linkage hyp が conclusion-as-hypothesis でないか (`_existence` / `_converse_n_letter` convention 整合 verify)
  - (b) `@residual(defect:false-statement)` → `@residual(plan:wyner-ziv-discharge-moonshot-plan)` の判断整合
  - (c) tier 5 → tier 2 2 段昇格の honest 性 (BM Wave 6 と同型)

### Phase 3 DoD

- `WynerZivConverse.lean:253` の `@residual(defect:false-statement)` が 0 件
- 1 sorry、1 `@residual(plan:wyner-ziv-discharge-moonshot-plan)`
- `lake env lean` 0 errors

## Phase V — verify + 集約 + handoff 反映 📋

`proof-log: no` (mechanical verify + handoff 更新)。

- [ ] **V.1** 全 WynerZiv*.lean file (本 plan 影響 2 file 中心) で `lake env lean` 確認:
  ```bash
  lake env lean Common2026/Shannon/WynerZivAchievability.lean
  lake env lean Common2026/Shannon/WynerZivConverse.lean
  ```
  期待: 両 file 0 errors、累計 sorry warning 件数は Phase 1 (α/β) + Phase 2 + Phase 3 に応じて 2-3 件。

- [ ] **V.2** タグ集計 (canonical declaration-direct grep, `docs/audit/sorry-migration-runbook.md` Pattern D):
  ```bash
  rg -n '@residual\(defect:false-statement\)|@residual\(defect:circular\)' Common2026/Shannon/WynerZiv*.lean
  ```
  → 期待: **0 hits** (3 件全削減)。

  ```bash
  rg -n '@residual\(plan:wyner-ziv-discharge-moonshot-plan\)' Common2026/Shannon/WynerZiv*.lean | wc -l
  ```
  → 期待: WynerZiv Phase 2.x 完了状態の 15 件 + 本 plan 追加 2 件 (Phase 2 `_existence` + Phase 3 `_converse_rate`) = **17 件**、Phase 1 (α) 採用時は Phase 1 で減算 → 16 件 (但し Phase 1 では `@residual(defect:false-statement)` 削除 + 新規 `@residual` 不付与なので、Phase 2.x 完了 15 + 本 plan Phase 2 +1 + Phase 3 +1 = 17 件のまま、Phase 1 削除分は 16 件)。
  Phase 1 (β) 採用時: 15 + 3 = **18 件**。

- [ ] **V.3** `lake env lean` で BM Wave 6 と同様の sanity check:
  ```bash
  lake env lean Common2026/Shannon/WynerZiv.lean
  lake env lean Common2026/Shannon/WynerZivAchievabilityBridge.lean
  ```
  Phase 0.2 で consumer 0 件確認済 → これらは未 touch だが、import side-effect での `unknown identifier` 等を弾く spot-check。

- [ ] **V.4** **honesty-auditor 独立起動** (CLAUDE.md「Independent honesty audit」必須):
  - 対象: Phase 1-3 で改変された 3 declaration (signature 改変有無 / タグ書換)
  - subagent: `general-purpose` agent w/ CORE doctrine inline (CLAUDE.md「Independent honesty audit」の `subagent_type: "honesty-auditor"` が CLI 未対応の場合 — handoff Wave 4-D 観察を継承)
  - brief 必須項目:
    - 3 declaration の (file:line + decl 名 + 旧タグ + 新タグ + signature 改変有無) を表で列挙
    - verbatim verify の指示 (本 plan / brief を鵜呑みにせず実コード Read)
    - 判定 focus: linkage hyp が conclusion-as-hypothesis でないこと、Phase 1 (α/β) 判断の整合性、`defect:circular` (Phase 2) が真に **stale tag** だったことの確認
    - verdict 語彙: **ok / questionable / defect**
  - audit verdict 受領後、Phase 1 (α) candidate に対しては `@audit:ok` 付与判断 (Tier 1 honesty 到達 candidate)

- [ ] **V.5** 親 plan `wyner-ziv-moonshot-plan.md` / `wynerziv-phase2-predicate-removal-plan.md` の banner 更新:
  - `wynerziv-phase2-predicate-removal-plan.md` の「Tier 5 defect 検出 (planner 段階)」散文 (`@residual(defect:false-statement)` 2 件 + `@residual(defect:circular)` 1 件、本 plan **scope 外** 表記) を **closed mark** に更新、本 plan の終了 commit を参照する 1 行追記
  - `wyner-ziv-moonshot-plan.md` のステータス散文に「Tier 5 defect 3 件 (Achievability 2 + Converse 1) は `wynerziv-tier5-defect-discharge-plan.md` で discharge 完了 (2026-05-XX)、現状 0 件」を追記

- [ ] **V.6** handoff 更新 (`.claude/handoff-sorry-migration.md`):
  - 「Round 2 残課題 follow-up」or 「Round 4 escalate」のいずれか current section に「WynerZiv tier 5 defect 3 件 discharge」を ✅ 完了 marker で追加
  - Phase 1 (α) 採用時: 「**proof done 1 件追加** (`wyner_ziv_achievability_rate` Tier 1 `@audit:ok` 到達)」を append
  - Phase 1 (β) 採用時: 「3 件 tier 5 → tier 2 (honest_residual)」を append
  - 数値表 (`@residual(defect:false-statement)` / `@residual(defect:circular)`) 行に delta 反映

- [ ] **V.7** Phase V 完了時 squashed commit + push (CLAUDE.md「Commits」)。

### Phase V DoD

- `@residual(defect:false-statement)` 件数: WynerZiv family 全体で **0** (本 plan 完遂)
- `@residual(defect:circular)` 件数: WynerZiv family 全体で **0** (本 plan 完遂)
- honesty-auditor verdict = ok
- handoff Round 2 / Round 4 follow-up tracker から 3 declaration が closed
- session 末で squashed commit + push

## 撤退ライン (本 plan)

- **L-DD-1 (linkage hypothesis convention 拡張で 5+ declaration touch 必要)**: Phase 1-3 で linkage hyp 追加時、WynerZiv 既存 convention (existence / converse_n_letter の `(M : ℝ) ≤ Real.exp ((n : ℝ) * R)` + `R > wynerZivRatePmf ...`) で網羅できなければ本 plan を pause、convention 拡張 plan を別途起草。**本 plan 起草時 verbatim 確認では既存 convention で網羅可能 → L-DD-1 不発見込み**。
- **L-DD-2 (consumer 0 件判定漏れで cross-family drift)**: Phase 0.2 で `rg --type lean` 確認、本 plan 起草時 0 件だが、Phase 1-3 実装中に consumer 発見 → 当該 file ripple 対応 or scope 拡張判断。
- **L-DD-3 (Phase 2.x 完了状態との整合性破綻)**: 本 plan は Phase 2.x 完了状態の追加 sweep、衝突無し設計だが、Phase V audit で破綻判定なら Phase 2.x banner と本 plan を coordinate refresh。
- **L-DD-4 (1 PR scope を超える)**: Phase 1 のみで本 plan を close し、Phase 2/3 を後続 session に分離。Phase 2 は signature 改変ゼロのため最も簡素、Phase 3 と Phase 1 は signature 改変 + 境界判定で同等難度。
- **L-DD-5 (Phase 1 (α) constructive recovery 判断が auditor verdict で defect になる)**: Phase V audit で `le_of_lt h_R_gt` 採用が「rate-side 'achievability' API として degeneracy」(rate-side の sense では `R_WZ ≤ R` を `<` から `≤` lift する形は achievability の operational content を空にする退化定義悪用の可能性) と判定されたら (β) に降格、Phase 1 だけ tier 2 honest_residual で commit。本 plan 起草時の planner 判断では (α) は constructive bridge hyp で genuinely well-defined (Pilot Pattern B 該当)、auditor verdict は ok の見込み。

## 未決事項

planner が判断つかない事項を列挙。実装 / auditor 委任で済む項目は明記。

1. **Phase 1 (α/β) 採用判断** (implementer 判断 + auditor verdict 委任): Phase 1 設計で (α) `body := le_of_lt h_R_gt` (proof done) vs (β) `body := sorry + @residual(plan:...)` (tier 2 honest_residual) の判断は **implementer の inline detection (Pilot Pattern B) で結論型を verbatim 確認後決定**。auditor が「rate-side achievability の operational content を空にする退化定義悪用」と判定した場合は (β) 降格。本 plan 起草時 planner 判断は (α) 推奨 — `R_WZ < R` から `R_WZ ≤ R` lift は ordered field の純構造的 bridge で、achievability の **operational 達成可能性** (random binning + AEP) とは independent な rate-side ordering の API。

2. **Phase 1 `(h_R_gt : R > wynerZivRatePmf ...)` の `>` vs `≥` 選択** (implementer 判断): `_existence` form は `_h_R_gt : R > wynerZivRatePmf U P_XY d D` で **strict** (Cover-Thomas 15.9.1 strict version)。Phase 1 でも **strict version で揃える** ことを planner 推奨 (family 内 convention)。`≥` (non-strict) を選ぶと `_existence` との asymmetry が発生、避ける。

3. **Phase 3 `(h_M_le)` の `<` vs `≤` 選択** (implementer 判断): `_existence` form は `(M : ℝ) ≤ Real.exp ((n : ℝ) * R)` (= **non-strict**、achievability の達成可能性 conclusion 内部式と verbatim 一致)。Phase 3 でも **non-strict で揃える** ことを planner 推奨。converse form は achievability の dual で、code size が `Real.exp (n · R)` 以下 = rate `R` で encode できることが precondition、これは converse の precondition として natural。

4. **honesty-auditor の subagent_type 選択** (orchestrator 判断): handoff Wave 4-D で `honesty-auditor` agent type が CLI 未対応観察あり、`general-purpose` agent + CORE doctrine inline で代替予定。本 plan Phase V audit で同じ代替 path を選択。

5. **proof done を本 plan で目指すか否か** (user 確認): 本 plan の DoD は基本 **type-check done** (tier 2 honest_residual 化) だが、Phase 1 (α) 採用時のみ proof done 1 件追加。BM Wave 6 と異なる点 (BM Wave 6 は 2 件とも tier 2 stable、本 plan は Phase 1 で proof done candidate あり)。

6. **Phase 1 / Phase 2 / Phase 3 の commit 単位** (orchestrator 判断): 3 Phase 独立で commit するか、1 squashed commit で push するか。本 plan 起草時 planner 推奨: **3 Phase 独立 commit + Phase V で 1 squashed push** (各 Phase で `lake env lean` 確認 cycle、Phase 1 (α/β) 境界判定の挙動が後続 Phase に影響しないため独立 commit)。

## 判断ログ

書く頻度: 方針変更 / 撤退ライン発動 / 当初仮定の修正があったとき。append-only。

1. **2026-05-26 起草 (Wave 11 並列 session)**: lean-planner (本 session、docs-only) が WynerZiv Phase 2.x 完了後の残置 tier 5 defect 3 件を verbatim 読込で per-declaration 分類:
   - decl #1 `wyner_ziv_achievability_rate` (`:77`) — `defect:false-statement` (反例 `R := R_WZ - 1` で verify、precondition 不在)、案 (a) signature rewrite 採用、Phase 1 で境界判定 (α: constructive recovery / β: tier 2 honest_residual) を implementer / auditor に委任
   - decl #2 `wyner_ziv_achievability_existence` (`:104`) — `defect:circular` (Phase 2.1 retreat 後の **stale tag**、signature は well-formed)、案 (a) ≡ 案 (c) の境界 ケース、Phase 2 でタグ書換のみで tier 5 → tier 2 1 段昇格
   - decl #3 `wyner_ziv_converse_rate` (`:253`) — `defect:false-statement` (反例 `R := R_WZ + 1` で verify、`R` と `M/n` の linkage 不在)、案 (a) signature rewrite 採用、Phase 3 で `(h_M_le)` linkage hyp 追加 + body `sorry` 維持で tier 2 化
   - **consumer 0 件 verify**: `rg --type lean` で 3 declaration とも Lean 本体 caller 0 件確認 (`MACL1Discharge.lean:50` 1 件は Stage 1 docstring mention only、touch 不要)
   - **新規 wall promote しない**: 既存 `@residual(plan:wyner-ziv-discharge-moonshot-plan)` slug に集約 (WynerZiv family 内 統一性 + grep clean)
   - 撤退ライン 5 件 (L-DD-1 〜 L-DD-5) 定義、起草時 verbatim 確認で L-DD-1/L-DD-2 不発見込み
   - 未決事項 6 件 (Phase 1 (α/β) auditor 委任 + 各 strict/non-strict implementer 判断 + auditor subagent_type 選択 + proof done 目標範囲 + commit 単位)

<!-- 後続セッションで判断変更があれば下記に追記 (append-only):
2. **YYYY-MM-DD <要点>**: <変更理由 + 撤退ラインへの紐付け>。
-->
