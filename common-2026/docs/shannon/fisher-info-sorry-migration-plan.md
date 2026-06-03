# Shannon: FisherInfo legacy-tag → sorry-based migration plan

> **Parent**: family-level moonshot plan は不在。`@audit:suspect(fisher-info-moonshot-plan)` slug は `.claude/handoff-epi.md` (EPI Stam Phase A) と暗黙連動する legacy slug。
> 関連: [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md), [`audit/audit-tags.md`](../audit/audit-tags.md)。
>
> 本 plan は **legacy tag (`@audit:suspect`) → `sorry + @residual` への honesty 強化**を目的とする独立 workstream (proof completion ではない)。
>
> Pilot references: [`chernoff-sorry-migration-plan.md`](chernoff-sorry-migration-plan.md), [`relay-sorry-migration-plan.md`](relay-sorry-migration-plan.md)。
>
> **本 plan の verdict (2026-05-26)**: 全 5 file が EPI/Stam Phase A active reference に直撃 → **Case α 全降格**。Phase 0 のみ実施、Phase 1 以降は Phase A 完了後の再起動 plan に委譲。

## 進捗

- [ ] Phase 0 — 規模見積もり + Phase A 共存判定 + tier 5 defect inline 検出 📋
- [ ] Phase 1 — declaration-direct tag sweep (Phase 0 判定により skip) 📋
- [ ] Phase 2 — incidental tier 4 → tier 2 移行 (本 sweep では 0 件想定) 📋
- [ ] Phase V — verify + handoff 反映 📋

## Context

### 計数 (verbatim 確認、2026-05-26)

`@audit:suspect(fisher-info-moonshot-plan)` 各 1 件 × 5 file = **5 tags**:
`FisherInfo.lean`, `FisherInfoV2.lean`, `FisherInfoV2DeBruijn.lean`, `FisherInfoV2DeBruijnBody.lean`, `FisherInfoV2HeatFlowBody.lean`。他 legacy タグ (staged / closed-by-successor / defer / retract-candidate / defect / 🟢ʰ) 全て 0 件。

追加発見: `FisherInfoV2DeBruijnBody.lean` に既存 `sorry` 2 件 (別 declaration、本 sweep 対象外)。Pattern H 該当 0 件 (`rg '⚠|HONESTY ALERT|FALSE'` 該当無し)。

### scope 外 file

- `FisherDeBruijnGaussianWitness.lean` (1 tag、EPI/Stam family 所属)
- `FisherInfoGaussian.lean` (0 tag、上流 supplier)
- `FisherInfoV2DeBruijn.IsRegularDeBruijnHypV2:236` (predicate def、タグ無し、Phase A active reference)

### Phase A active 同期判定

`handoff-epi.md` (2026-05-25): **Phase A 3/8 完了、A-3 から再開**。A-2 出力で `fisherInfoOfDensityReal ((h_reg_*.reg_at t ht).density_t)` shape が verbatim 確定 — `IsRegularDeBruijnHypV2` の `density_t` field 経由で active use 中。**signature 改変 1 件で EPI 主定理 closure path 全壊**。

各対象 declaration の EPI consumer (verbatim 確認、影響度 = 致命/高/中/低):
- `deBruijn_identity_v2:262` → **致命** (EPIStamDeBruijnConclusion + EPIStamToBridge 直接、A-3 chain rule plumbing 直撃)
- `deBruijn_identity_v2_of_heat_flow:238` / `_of_heat_subhyp:240` → **高** (Gaussian witness path 経由 EPIL3 連鎖)
- `integral_logDeriv_pdf_eq_zero:127` → **中** (Gaussian wrapper 経由)
- `integral_logDeriv_density_eq_zero:157` → **低** (family 内孤立)

### tier 5 defect inline 検出

CLAUDE.md「検証の誠実性」"見つけた側" inline policy に従い verbatim 確認した defect (本 plan で touch 禁止、後続 plan の input):

- **重 3 件** (predicate field = conclusion type の name laundering chain):
  - `deBruijn_identity_v2:262` — `:= h_reg.derivAt_entropy_eq_half_fisher_v2` (load-bearing structure field 抽出のみ)
  - `deBruijn_identity_v2_of_heat_flow:238` — `:= h_ibp` literal alias (`IsIBPHypothesis := HasDerivAt ...` が `Iff.rfl`、`FisherInfoV2DeBruijnBody:204-220` で公式宣言)
  - `deBruijn_identity_v2_of_heat_subhyp:240` — 上の transitive forward
- **中 2 件** (`IsRegularDensity.integral_deriv_eq_zero` field が core claim、5-line `calc` plumbing は honest だが load-bearing field 経由):
  - `integral_logDeriv_pdf_eq_zero:127` / `integral_logDeriv_density_eq_zero:157`

honest sweep には signature 改変必須 (literal alias body を sorry 化するには hypothesis 削除が前提)。

### Honesty workflow と DoD

本 plan は **type-check done を取らない可能性が高い** — Phase 0 判定次第:

- **Case α (全降格、最有力 = default 採用)**: scope 外 + 再開条件のみ。該当 file 不変。
- **Case β (部分降格、低確率)**: Phase A 直撃でない 1-2 件のみ sweep。
- **Case γ (全件 sweep)**: Phase A 完了後 + EPI/Stam 統合 sweep として進める判定 (Round 4 起動対象外)。

本 plan は新規 `@residual` 0 件のため `honesty-auditor` 起動条件不充足。

### 退化境界

本 plan で signature 改変なし → 退化境界 predict 不要。再起動 plan で改めて verbatim 確認。`IsRegularDensity.pos` / `IsRegularDeBruijnHypV2.Z_law` field により退化 measure は構造で除外 → L-DBD-2-α 発火不能。

## Approach

### Phase A 共存判定の結論

**本 plan は default で Case α (全降格)**。根拠:

1. 全 5 declaration が EPI Phase A active reference chain 直撃 (特に重 3 件は A-3 chain rule plumbing 直撃)
2. 3/5 declaration が tier 5 defect 構造で sorry-based migration は signature 改変必須 → Phase A active 中の改変は **意図的破壊** 同等
3. handoff-epi.md の Phase A shape caveat と本 plan の改変が真っ向衝突
4. 中 2 件 (`integral_logDeriv` 系) も Gaussian wrapper 経由で EPIL3 Gaussian discharge path へ transitive 伝播

**判定**: scope 外 — Phase A 完了後に EPI/Stam + FisherInfo 統合 sweep として再起動。Round 4 起動対象 family から外す。

### 再起動条件 (Phase A 完了後)

全 3 条件成立で 0 から書き直し再起動:

1. handoff-epi.md Phase A 全 step (A-3〜A-V) 完了 (EPI 主定理 hypothesis-free 化達成)
2. `epi-stam-sorry-migration-plan.md` (未起草) 起草済
3. `IsRegularDeBruijnHypV2` field restructuring 完了 (core claim を sorry-based shared wall 補題に集約、structure は regularity-only 残し)

最も hard は (3): EPI 主定理 closure 後でも `IsRegularDeBruijnHypV2` は EPIStamDeBruijnConclusion publish の前段に居続ける可能性が高く、EPI/Stam migration plan で predicate 再設計が必須前提。

### 戦略 (本 session 範囲)

**Phase 0 のみ** 実施 (上記 Context 節を再確認、判定「Case α」を確定)。Phase 1-V は Phase A 完了待ち。

### 共有 wall lemma 集約

`wall:stam` (Stam 不等式、Cover-Thomas Ch.17) が `audit-tags.md` Wall register に既登録、本 cluster の集約候補。ただし primary owner = EPI/Stam family で本 plan 単独判断は tier shift 越権 → Phase A 完了後の統合 sweep で判定 (`stam` 1 wall 統合 vs `stam-debruijn` / `stam-score` 細分割)。

### Pattern G (cross-family unified predicate) 判定

全 5 file が **Stage S3 (infrastructure construction)** — EPI 全 file (EPIStamDischarge / EPIStamToBridge / EPIL3Integration / EPIStamInequalityBody / EPIStamDeBruijnConclusion / EPIStamStep3Body / EPIStamStep12Body) が import + active use。`IsRegularDeBruijnHypV2` は EPI Phase A の load-bearing structure field。

→ **Pattern G escalate 必須** — 単独 sweep 禁止、EPI/Stam family と統合判断必要。

### constructive recovery 候補 (Pilot Pattern B)

verbatim 確認結果: **0 件**。全 5 declaration が load-bearing field 抽出 or literal alias で、hypothesis 削除なしには constructive 経路を提供できない (sorry を残すか hypothesis を残すかの二択)。Hoeffding pilot 形 (`IsHoeffdingMinimizerFullSupport.of_pos`) のような「regularity reducible」declaration は本 cluster に存在しない。

### transitive sorry の handling (Pilot Pattern C、再起動時)

Phase A 完了後の Case γ shift では上流 sorry 化が EPI/Stam 各 EPI* file に大規模波及 (EPIStamDeBruijnConclusion / EPIStamToBridge / EPIL3Integration / EPIStamDischarge の Gaussian/general path 連鎖)。回避策: 統合 sweep として 1 plan で扱い、Chernoff Round 3 確立の Phase Z (closed-by-successor migration) Recipe A/B/C を EPI/Stam shape に拡張。

## Phase 0 — 規模見積もり + Phase A 共存判定 + tier 5 defect inline 検出 📋

本 plan の **唯一実施 Phase**。

- [ ] step 1 — Context 節計数表を Phase 0 完了時に再 verify (Phase A patch で declaration / tag が動いた可能性)
- [ ] step 2 — Case α 判定を handoff-epi.md 最新 state と整合性確認
- [ ] step 3 — tier 5 defect inline 検出表 verbatim 確認 (Context 節)、signature 改変必要 declaration 列挙 (後続 plan の input)
- [ ] step 4 — 再起動 3 条件を handoff-sorry-migration.md「Next step → A」に明示反映

退化境界 predict: 本 plan で signature 改変なし → 不要。再起動時に verbatim 確認。

## Phase 1 — declaration-direct tag sweep (skip) 📋

**本 session 実施せず** (Case α)。再起動 plan で改めて起草。

将来 reference 用予測 (本 plan では touch 禁止): 5 declaration 全件 `@residual(wall:stam)` 候補、signature 改変必要 (predicate `IsRegularDeBruijnHypV2` / `IsIBPHypothesis` は EPI active consumer ありで retract 不可)。中央予測 = 新規 sorry 5 / retract 0 / tag-only 削除 0。

## Phase 2 — incidental tier 4 → tier 2 移行 (0 件) 📋

本 cluster に tier 4 legacy (`@audit:staged` / 散文 `🟢ʰ` / `@audit:defer` / `@audit:closed-by-successor`) **0 件** → incidental migration 対象なし。`@audit:suspect` 5 件は touch 禁止 (上記 Phase 1 skip)。

## Phase V — verify + handoff 反映 📋

- [ ] step 1 — `InformationTheory/Shannon/FisherInfo*.lean` 5 file の改変なし確認 (`git diff` / `git status` 差分 0)
- [ ] step 2 — `handoff-sorry-migration.md`「Next step → A」section に再起動 3 条件明示反映
- [ ] step 3 — Case α 全降格判定を Round 4 全降格 family list に列挙 (orchestrator roster から外す)

`honesty-auditor` 起動なし (新規 `sorry` + `@residual` 0 件)。

## 未決事項

Phase A 完了後再起動時に re-evaluate:

1. **`IsRegularDeBruijnHypV2` field restructuring の前提タイミング**: EPIStamDischarge.lean が `reg_at` field で hypothesis 形に消費し続ける可能性 → predicate signature 改変が先行必要。EPI/Stam migration plan の Phase 0 で判定要請。
2. **`wall:stam` 集約 vs `plan:fisher-info` slug 新設**: EPI/Stam の shared wall lemma 設計次第。
3. **`integral_logDeriv` 系 2 件の sweep separation**: Phase A 直撃でない (Gaussian wrapper 間接) ため先行 sweep 可能性 → `IsRegularDensity.integral_deriv_eq_zero` core claim の signature 改変は EPIL3 Gaussian discharge path 影響評価要 (Phase 0 で再評価)。
4. **本 plan vs `epi-stam-sorry-migration-plan` の責任分担**: sub-plan として吸収される設計の可能性 → 後続 plan 起草時判断。

## 撤退ライン

- **L-MIG-EPI-INTEGRATION** (発火確率 高、default 撤退): 全 declaration signature 改変が EPI Phase A active chain 破壊 → **Phase 0 で確定 (Case α 全降格)**、Phase 1 以降は再起動 plan へ委譲。本撤退ラインは default として既発火。
- **L-MIG-RECURSIVE-REDESIGN** (発火確率 中): 再起動時に `IsRegularDeBruijnHypV2` field structure を保ったまま honest 化する path が無い → EPI/Stam migration plan で predicate 再設計実施、本 plan は再起動 plan として完全書き直し。
- **L-DBD-2-α** (degenerate-definition exploitation、発火確率 低): Fisher info 退化境界突きの vacuous instance → `pos` / `Z_law` field で構造的に発火不能。再起動 plan の Phase 0 で再 verify。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正時。append-only。

1. **2026-05-26 — Phase 0 判定 = Case α 全降格 (起草時)**:
   verbatim 確認の結果、全 5 declaration が EPI Phase A active reference 直接含 (特に `deBruijn_identity_v2` 系 3 件は EPIStamDeBruijnConclusion / EPIStamToBridge 直接 consumer、A-3 chain rule plumbing 直撃)。
   - Round 4 起動対象 family から外す
   - 再起動 plan は Phase A 完了後 (3 条件成立) に 0 から書き直し
   - 本 session 出力 = Phase 0 判定 + Phase 1 以降の予定 inventory + tier 5 defect inline 検出表 + 再起動条件 + 撤退ライン
2. **tier 5 defect inline 検出の報告のみ・rewrite なし** (起草時発見、CLAUDE.md「検証の誠実性」"見つけた側" inline policy 準拠):
   重 3 件 + 中 2 件 (Context 節 tier 5 defect inline 検出 表参照)。全件 silent fix せず、(a) 場所と種類を Context 節 + 本 entry に報告、(b) その上に build しない方針で、Phase A 完了後の再起動 plan で signature 改変を扱う。

## Files to read (再起動時に必須)

- `.claude/handoff-epi.md` — Phase A 最終 state (closed 時の最新 commit hash)
- `.claude/handoff-sorry-migration.md` — Round 4 全体 state
- `docs/audit/sorry-migration-runbook.md` — Step 1-4 + Pattern A-J
- `docs/audit/audit-tags.md` — vocab SoT
- `docs/shannon/chernoff-sorry-migration-plan.md` — Phase Z recipe reference
- `docs/shannon/epi-stam-sorry-migration-plan.md` — (未起草) 前提条件
- `InformationTheory/Shannon/FisherInfo*.lean` (5 file) — Phase A 完了後の状態を再 verify
- `InformationTheory/Shannon/EPIStamDischarge.lean:97-205` — `IsStamInequalityHyp` / `IsRegularDeBruijnHypFamily` の Phase A 完了後 signature verbatim 確認

## 計数 — Phase 0 完了時の最終 verdict

| 項目 | 本 plan 本 session |
|---|---:|
| 新規 sorry 数 | **0** (sweep skip、再起動 plan へ委譲) |
| retract-candidate 付与数 | **0** |
| tag-only 削除数 | **0** |
| touch する .lean file 数 | **0** |
| touch する .md file 数 | **1** (本 plan のみ) |
| Phase A active 同期 file (touch 禁止) | 全 5 file (`FisherInfo*.lean`) |
