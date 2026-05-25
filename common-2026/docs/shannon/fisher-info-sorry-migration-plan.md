# Shannon: FisherInfo legacy-tag → sorry-based migration plan

> **Parent**: 該当 family-level moonshot plan は不在 (`docs/shannon/` に
> `fisher-info-moonshot-plan` のような単独 plan は **未生成**)。本 plan の
> `@audit:suspect(fisher-info-moonshot-plan)` slug は handoff
> `.claude/handoff-epi.md` (EPI Stam Phase A) と暗黙連動する legacy slug。
> + 関連 [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md) /
>   [`audit/audit-tags.md`](../audit/audit-tags.md)。
>
> 本 plan は **proof completion ではなく legacy tag (`@audit:suspect`) →
> `sorry + @residual` への honesty 強化** (`audit-tags.md`「Deprecated」表 +
> 「移行レシピ」) を目的とする独立 workstream。
>
> Pilot references:
> - [`chernoff-sorry-migration-plan.md`](chernoff-sorry-migration-plan.md)
>   (Round 3 直近、tier 5 既存マーカー混在 family の sweep recipe)
> - [`relay-sorry-migration-plan.md`](relay-sorry-migration-plan.md)
>   (上流→下流 chain sweep、cross-family ripple 散文化)
>
> **本 plan の特殊性 — Phase A 共存リスク**: 全 5 file が EPI/Stam Phase A
> (`handoff-epi.md` A-3 active) の **active reference chain** に組み込まれており、
> signature 改変は EPI 連鎖を全壊させる。Phase 0 で Phase A 共存判定を最優先で
> 行い、本 plan は **scope 大幅縮退または全降格**の判定を出す可能性が高い。

## 進捗

- [ ] Phase 0 — 規模見積もり + Phase A 共存判定 + tier 5 defect inline 検出 📋
- [ ] Phase 1 — declaration-direct tag sweep (Phase 0 判定に従って実施 or 全降格) 📋
- [ ] Phase 2 — incidental tier 4 → tier 2 移行 (本 sweep では 0 件想定) 📋
- [ ] Phase V — verify + handoff 反映 📋

## Context

### 計数 (verbatim 確認、2026-05-26)

`rg -n '@audit:suspect\(|@audit:staged\(|@audit:closed-by-successor\(|@audit:defer\(|@audit:retract-candidate\(|@audit:defect\(|🟢ʰ'`
+ 各タグ周辺 docstring / signature / body 1-3 行を Read で照合した実数値:

| file | suspect | staged | closed-by-successor | defer | retract-candidate | defect | 🟢ʰ (散文) | 既存 sorry (`rg -nwc`) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `FisherInfo.lean` | **1** | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `FisherInfoV2.lean` | **1** | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `FisherInfoV2DeBruijn.lean` | **1** | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `FisherInfoV2DeBruijnBody.lean` | **1** | 0 | 0 | 0 | 0 | 0 | 0 | **2** |
| `FisherInfoV2HeatFlowBody.lean` | **1** | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| **合計** | **5** | 0 | 0 | 0 | 0 | 0 | 0 | **2** |

**計数の verbatim 確認結果は orchestrator brief 「5 file × 1 tag = 5 tags」と一致** (suspect / staged / 🟢ʰ 内訳 0 件も brief 通り)。

**追加発見** (brief 在庫表に未掲載):
- `FisherInfoV2DeBruijnBody.lean` に既存 `sorry` 2 件 (word-boundary `rg -nwc`)。本 plan の sweep scope 内 declaration とは独立、別 declaration での既存 placeholder と推定 (Phase 0 で verbatim 確認)。
- 既存 `@audit:defect` / `@audit:retract-candidate` 0 件 (本 cluster は tier 5 既存マーカー無し)。
- Pattern H (⚠ HONESTY ALERT / FALSE) 0 件 (verbatim 確認、`rg '⚠|HONESTY ALERT|FALSE'` 該当無し)。

### scope 外 file (Phase A 共存判定とは別)

- `FisherDeBruijnGaussianWitness.lean` (1 tag、EPI/Stam family 所属、本 plan **scope 外**、orchestrator brief 明示)
- `FisherInfoGaussian.lean` (0 tag、本 plan scope 外、上流 supplier として参照)
- `FisherInfoV2DeBruijn.lean` 内の `IsRegularDeBruijnHypV2` (predicate def、`:236`) は本 plan の Phase 1 対象 declaration ではない (タグ無し、Phase A active reference)。

### 上位 plan / handoff との関係 — Phase A active 同期判定

`docs/audit/sorry-migration-runbook.md`「並列実行候補 family (2026-05-25 集計)」で
FisherInfo 系は **Round 3 (大規模 + dependency 注意)** の「EPI/Stam cluster の一部、関連 sweep で」と分類済。
`handoff-sorry-migration.md` の「Next step → A」項目で **EPI/Stam + AWGN +
ParallelGaussianPerCoord 続き** の文脈に置かれ、EPI/Stam Phase A
(`handoff-epi.md`) との統合判断が前提。

`handoff-epi.md` (2026-05-25 15:40) state:
- **Phase A 3/8 step 完了** (A-1 + A-0' + A-2、計 +635 行)、A-3 (1-source Stam reduction、`csiszarGap1Source_deriv_le_zero`) から再開
- **A-2 出力の Fisher info shape caveat**: implementer 報告で「mini-plan 想定 `fisherInfoOfMeasureV2Real (...)` 形 → 実コード verbatim `fisherInfoOfDensityReal ((h_reg_*.reg_at t ht).density_t)`」と判明。`IsRegularDeBruijnHypV2` の `density_t` field 経由で活用中

**Phase A 真っ最中**で、`IsRegularDeBruijnHypV2`/`deBruijn_identity_v2`/`deBruijn_identity_v2_of_heat_flow`/`deBruijn_identity_v2_of_heat_subhyp` の **どれか 1 つを signature 改変するだけ** で EPI 主定理 closure path が全壊する。

#### EPI Phase A active consumer chain (verbatim 確認)

各本 plan 対象 declaration の Phase A 内 consumer:

| 対象 declaration (本 plan tag 付き) | EPI Phase A active consumer | 影響 |
|---|---|---|
| `FisherInfoV2DeBruijn.deBruijn_identity_v2:262` | `EPIStamDeBruijnConclusion.lean:30/146/150` (`deBruijn_identity_v2_deriv_nonneg`) + `EPIStamToBridge.lean:450` (Phase A A-3 入口 docstring 明示) + `EPIL3Integration.lean:756/790/927` (Gaussian discharge) | **致命**: A-3 の chain rule plumbing で直接呼出、signature 改変で `EPIStamDeBruijnConclusion` から `EPIStamToBridge` まで全壊 |
| `FisherInfoV2DeBruijnBody.deBruijn_identity_v2_of_heat_flow:238` | `FisherInfoV2HeatFlowBody.lean:253` (本 plan の別対象が forward) + transitively via `IsRegularDeBruijnHypV2.ofHeatFlow:257` → `FisherDeBruijnGaussianWitness.lean:166` (`isRegularDeBruijnHypV2_gaussian_heatFlow`、Phase A A-0' EPIL3Integration の Gaussian witness path に組込) | **高**: Gaussian witness path 経由で EPIL3 / EPIStamDischarge 連鎖 |
| `FisherInfoV2HeatFlowBody.deBruijn_identity_v2_of_heat_subhyp:240` | `FisherDeBruijnGaussianWitness.lean:145` (`isRegularDeBruijnHypV2_gaussian_heatFlow_via_subhyp`) | **高**: 同上、Gaussian witness 経由 |
| `FisherInfoV2.integral_logDeriv_density_eq_zero:157` | `rg` で family 外 consumer 検出 0 件 (FisherInfo cluster 内 only) | **低**: family 内孤立 |
| `FisherInfo.integral_logDeriv_pdf_eq_zero:127` | `FisherInfoGaussian.lean:293` (`integral_logDeriv_pdf_eq_zero_gaussian`、hypothesis-free Gaussian wrapper) | **中**: Gaussian wrapper 経由、EPIL3 へ partial chain。Phase A 直接ではない (Gaussian path 上の utility) |

**結論**: 全 5 declaration が EPI Phase A active reference に含まれる。特に 3 件
(`deBruijn_identity_v2` / `_of_heat_flow` / `_of_heat_subhyp`) は **Phase A A-3
実装の chain rule plumbing 直撃**。Phase A 完了前に signature 改変すると A-3〜A-V
全 dispatch が hyp shape 不整合で 1 turn 詰まり。

### tier 5 defect — inline 検出 (planner 段階)

CLAUDE.md「検証の誠実性」"見つけた側" inline policy に従い、planner 段階で
verbatim 確認した tier 5 構造的観察:

| file:line | decl 名 | 構造的観察 | verbatim 根拠 |
|---|---|---|---|
| `FisherInfoV2DeBruijnBody.lean:204-210` | `IsIBPHypothesis` (def) | **predicate 自身が結論型と literal alias** (`:= HasDerivAt ((1/2) * fisherInfoOfDensityReal (p t)) t`)、`isIBPHypothesis_iff:213-220` body `:= Iff.rfl` で公式に「仮説型 ≡ 結論型」を declare 済 | def `:204-210` + `Iff.rfl:220` |
| `FisherInfoV2DeBruijnBody.lean:238-250` | `deBruijn_identity_v2_of_heat_flow` (theorem) | **tier 5 defect: 仮説型 ≡ 結論型 で body `:= h_ibp`** (literal alias unfold)。`h_ibp : IsIBPHypothesis X Z P p t` を取り、結論型は IBP の定義そのもの。`_h_heat : IsHeatFlowDensity` は underscore (未使用) | signature + body verbatim |
| `FisherInfoV2HeatFlowBody.lean:240-254` | `deBruijn_identity_v2_of_heat_subhyp` (theorem) | **tier 5 defect chain**: 上の `deBruijn_identity_v2_of_heat_flow` を forward する 1 行 wrapper。`h_conv` / `h_time` は `IsHeatFlowDensity_of_sub_predicates` 経由で `_h_heat` を構築するが、最終的に `h_ibp` literal alias で結論。本質的に同種の defect | body `:= deBruijn_identity_v2_of_heat_flow X Z hX hZ hXZ ht (IsHeatFlowDensity_of_sub_predicates h_conv h_time) h_ibp` |
| `FisherInfoV2DeBruijn.lean:236-249` | `IsRegularDeBruijnHypV2` (structure) | **structure field `derivAt_entropy_eq_half_fisher_v2:245-249` が結論型と同一の `HasDerivAt` 形** (load-bearing predicate bundling) | structure def verbatim |
| `FisherInfoV2DeBruijn.lean:262-272` | `deBruijn_identity_v2` (theorem) | **tier 5 defect: 仮説 field 抽出だけで結論を出す** (`:= h_reg.derivAt_entropy_eq_half_fisher_v2`)。`(_hX, _hZ, _hXZ, _ht)` は underscore (未使用)、load-bearing claim は `h_reg` field 1 つに集約 | body `:= h_reg.derivAt_entropy_eq_half_fisher_v2:272` |
| `FisherInfo.lean:92-113` | `IsRegularDensity` (structure) | **regularity 形にも見えるが field `integral_deriv_eq_zero:113` が score expectation 0 の core claim そのもの** (load-bearing field)。残り 5 field (`diff` / `pos` / `tail_bot` / `tail_top` / `integrable_deriv`) は正規 regularity だが、`integral_deriv_eq_zero` だけが claim form | structure def verbatim |
| `FisherInfo.lean:127-143` | `integral_logDeriv_pdf_eq_zero` (theorem) | **5-line constructive proof**: `h_reg.pos x` + `logDeriv_apply` + `div_mul_cancel₀` で `logDeriv g · g = deriv g` → `integral_congr_ae` で integral 一致 → `h_reg.integral_deriv_eq_zero` で 0。**core claim は `h_reg.integral_deriv_eq_zero` field 抽出**、残りは calc plumbing | body verbatim |
| `FisherInfoV2.lean:131-143` | `IsRegularDensityV2` (structure) | 上の `IsRegularDensity` V2 analog。同じ `integral_deriv_eq_zero` field を持つ load-bearing structure | structure def verbatim |
| `FisherInfoV2.lean:157-168` | `integral_logDeriv_density_eq_zero` (theorem) | V2 analog の同じ 5-line constructive proof、同じ pattern | body verbatim |

**結論**:
- **5 declaration 全件が tier 5 defect 寄り** (degree は差あり):
  - 重 (3 件): `deBruijn_identity_v2` / `_of_heat_flow` / `_of_heat_subhyp` — predicate field = conclusion type の name laundering chain、honest sweep には signature **改変必須**
  - 中 (2 件): `integral_logDeriv_pdf_eq_zero` / `integral_logDeriv_density_eq_zero` — `IsRegularDensity` の `integral_deriv_eq_zero` field が core claim、5-line constructive plumbing は honest だが load-bearing field 経由

- ただし **本 plan で touch 禁止** (Phase A 共存)。tier 5 defect の inline 検出は本 plan の Phase 0 出力として **報告のみ**、実際の rewrite は Phase A 完了後 (handoff-epi.md A-3〜A-V 終了後) に EPI/Stam + FisherInfo 統合 sweep として scope 設計し直す。

### Honesty workflow と DoD

本 plan は **type-check done を取らない可能性が高い** — Phase 0 の判定結果次第:

- **Case α (全降格、最有力)**: Phase 0 で「Phase A active のため scope 外」判定 → 本 plan は方針表明 + 再開条件のみ書き、Phase 1 以降は 0 件で skip。type-check done = 該当 file は不変 (legacy `@audit:suspect` 5 件残置)
- **Case β (部分降格、低確率)**: 5 declaration のうち Phase A 直撃でない 1-2 件 (`FisherInfo.lean:127` / `FisherInfoV2.lean:157`) のみ sweep。EPI consumer chain への影響は signature underscore 化等で吸収
- **Case γ (全件 sweep、最低確率)**: Phase A 完了後 + EPI/Stam 統合 sweep として進める判定。**本 plan の Round 4 起動条件ではない** (Phase A まだ active)

各 Phase 完了時に `honesty-auditor` を起動して classification + signature
honesty を独立検証 (CLAUDE.md「Independent honesty audit」)。**ただし本 plan で
新規 `@residual` が 0 件のままなら honesty-auditor 起動条件不充足** (起動条件
「新規 sorry + @residual を含む commit」が満たされないため)。

### 退化境界 verbatim 確認

CLAUDE.md「具体的数値・型予測の verbatim 確認」に従い、Fisher info 周辺の退化
境界 case を確認:

- `fisherInfoOfDensityReal` の退化 case (定義 file: `FisherInfoV2.lean` 確認要):
  - Dirac 0 → `gaussianPDFReal 0 0` 等の境界は本 plan の signature 改変対象外なので予測不要
  - **Phase A 側の caveat** (handoff-epi.md): A-2 出力で `fisherInfoOfDensityReal ((h_reg_*.reg_at t ht).density_t)` 形が verbatim 確定済、本 plan の touch によりこの shape を改変すると Phase A A-3 brief で「mini-plan 想定 vs 実コード verbatim」 drift と同種の事態を **意図的に** 引き起こすことになる。**回避策**: 本 plan で `fisherInfoOfDensityReal` を取る位置の引数型 (`h_reg.density_t` の出所) を改変しない
- `differentialEntropy` の退化 case は本 plan の関与外 (Phase A 側の責務)
- `IsRegularDensity` の Dirac 退化: `pos : ∀ x, 0 < density x` field により Dirac (0 measure) は構造で除外、退化境界 vacuous instance による degenerate-definition exploitation (L-DBD-2-α) は構造的に発火不能

退化境界の predict 値: **本 plan では predict しない** — signature 改変を伴う実 sweep を本 plan では実施しないため (Phase A active 中)。

## Approach

### Phase A 共存判定の結論 (Phase 0 で再確認 + finalize)

**本 plan は default として Case α (全降格)** を採用。理由:

1. **全 5 declaration が EPI Phase A active reference chain に含まれる** (`deBruijn_identity_v2` 系 3 件は EPIStamDeBruijnConclusion / EPIStamToBridge 直接 consumer、Phase A A-3 implementation の chain rule plumbing 直撃)
2. **3/5 declaration が tier 5 defect 構造** で sorry-based migration は signature 改変必須 (literal alias body `:= h_ibp` / `:= h_reg.derivAt_entropy_eq_half_fisher_v2` を sorry 化するには hypothesis 削除が前提)。Phase A 完了前の signature 改変は EPI 連鎖の **意図的破壊** 同等
3. **handoff-epi.md** の Phase A A-3 sub-bound 引数表 / shape caveat と本 plan の signature 改変は **真っ向衝突**。Round 3 Wave A planner が同 file に並列着手したら branch drift より深刻な「mini-plan vs implementer」shape drift を引き起こす
4. **2/5 declaration (`integral_logDeriv_pdf_eq_zero` / `_density_eq_zero`)** は Phase A 共存 risk が中程度に下がるが、Gaussian wrapper (`FisherInfoGaussian.integral_logDeriv_pdf_eq_zero_gaussian:288-293`) が EPI 連鎖の utility 上にあり、本 plan の Phase 1 で `IsRegularDensity` 仮説を削除して body sorry 化すると Gaussian wrapper も transitive sorry 化 → EPIL3Integration の Gaussian discharge path に伝播

**判定**: 本 plan は **scope 外 — Phase A 完了後に EPI/Stam + FisherInfo
統合 sweep として再起動**。Round 4 sorry-based migration の起動対象 family
からは **本 family を外す**。

### 再起動条件 (Phase A 完了後)

以下の **全条件** が満たされた時点で本 plan を 0 から書き直して再起動:

1. **handoff-epi.md** の Phase A 全 step (A-3 / A-4 / A-5 / A-6 / A-V) が完了
   (= EPI 主定理 hypothesis-free 化達成、`@audit:suspect` 14 件の post-merge
   cleanup 完了)
2. **EPI/Stam family** の sorry-based migration plan (`docs/shannon/epi-stam-sorry-migration-plan.md`、未起草) が起草済
3. **FisherInfo cluster の EPI 連鎖上 active consumer** が解消 (新 EPI 主定理 path
   が `IsRegularDeBruijnHypV2` を通らない / 通る場合でも predicate signature が
   honest 形に書換済)

3 条件のうち最も hard なのは (3): EPI 主定理 closure 後でも `IsRegularDeBruijnHypV2`
は `EPIStamDeBruijnConclusion` で publish される headline の前段に居続ける可能性が
高いため、EPI/Stam migration plan で **`IsRegularDeBruijnHypV2` の field
restructuring** (= core claim を sorry-based shared wall 補題に集約、structure は
regularity-only 残し) が必須の前提条件。

### 戦略 (本 plan の本 session 範囲)

本 plan の **本 session の出力は Phase 0 のみ**:

```
Phase 0    規模見積もり + Phase A 共存判定 + tier 5 defect inline 検出 (上記 Context 節を再確認)
   │       → 判定結論「全降格 (Case α)」を確定
   │
Phase 1-V  本 session では実施しない (Phase A 完了待ち)
```

Phase 1 以降の skeleton は **後続 plan (Phase A 完了後の再起動 plan)** に委ね、
本 plan では空のまま (起動条件のみ残置)。

### 共有 wall lemma 集約の要否

**集約検討対象 (Phase A 完了後再起動時)**: `audit-tags.md`「Wall name register」
表に **`stam`** (Stam 不等式、Blachman score-of-convolution identity) が既登録、
Cover-Thomas Ch.17 EPI 関連。Fisher info 連鎖の core claim 群 (`deBruijn_identity_v2`
系 3 件 + `integral_logDeriv` 系 2 件) は textbook 文脈上は EPI 章に属し、
`wall:stam` への集約候補。

ただし `wall:stam` は EPI/Stam family が primary owner で、FisherInfo 単独 sweep で
集約判断するのは tier shift 越権。**Phase A 完了後の EPI/Stam + FisherInfo
統合 sweep で集約判断** (`stam` 1 wall に統合 or `stam-debruijn` / `stam-score`
等の細分割で register 拡張)。

本 plan 本 session では集約検討せず、Phase A 完了後の再起動 plan に委ねる。

### Pattern G (cross-family unified predicate) 判定

本 sweep scope (5 file) の import 構造 (verbatim 確認):

| file | family-内 import | EPI-向 export (downstream EPI consumer) | Stage (S1/S2/S3) |
|---|---|---|---|
| `FisherInfo.lean` | `DifferentialEntropy` | `FisherInfoGaussian:6` (上流 supplier) | **S3** (Gaussian wrapper 経由 EPIL3 へ伝播、`integral_logDeriv_pdf_eq_zero` を Gaussian discharge が depends on) |
| `FisherInfoV2.lean` | `FisherInfo` + `FisherInfoGaussian` + `DifferentialEntropy` | EPI 全 file (`EPIStamDischarge:3` / `EPIStamToBridge` / `EPIL3Integration:5` / `EPIStamInequalityBody:5` / `EPIStamDeBruijnConclusion:7` / `EPIStamStep3Body:5` / `EPIStamStep12Body:3`) | **S3** (`fisherInfoOfDensityReal` / `IsRegularDensityV2` を EPI 全体が import + use) |
| `FisherInfoV2DeBruijn.lean` | `FisherInfo` + `FisherInfoGaussian` + `FisherInfoV2` + `DifferentialEntropy` + `EntropyPowerInequality` | EPI 全 file (同上) + `IsRegularDeBruijnHypV2` を EPIStamDischarge `reg_at` field で active use | **S3** (predicate `IsRegularDeBruijnHypV2` が EPI Phase A の load-bearing structure field) |
| `FisherInfoV2DeBruijnBody.lean` | `FisherInfoV2` + `FisherInfoV2DeBruijn` + `DifferentialEntropy` | `FisherInfoV2HeatFlowBody:11` + `FisherDeBruijnGaussianWitness:3` 経由で EPI 連鎖 | **S3** (`IsIBPHypothesis` / `IsHeatFlowDensity` を heat flow path が active use) |
| `FisherInfoV2HeatFlowBody.lean` | `FisherInfoV2` + `FisherInfoV2DeBruijn` + `FisherInfoV2DeBruijnBody` + `FisherInfoGaussian` + `DifferentialEntropy` | `FisherDeBruijnGaussianWitness:4` 経由で EPI 連鎖 | **S3** (heat flow path が EPI Gaussian witness の前段) |

**結論**: 全 5 file が **Stage S3 (infrastructure construction)**。runbook
「Cross-family 検出 3 段階判定」で「単独 sweep で predicate 削除すると他 family
broken」 該当。Pattern G escalate **必須** — 本 plan を単独で進めることは禁止、
EPI/Stam family と統合判断必要。

### constructive recovery 候補 (Pilot Pattern B)

5 declaration の結論型 + body 構造を verbatim 確認 (上記 tier 5 inline 検出 表):

| file:line | decl 名 | 結論型 | body 構造 | constructive recovery 可能? |
|---|---|---|---|---|
| `FisherInfo.lean:127` | `integral_logDeriv_pdf_eq_zero` | `∫ logDeriv h_reg.density · h_reg.density = 0` | 5-line `calc` (logDeriv_apply + div_mul_cancel₀ + integral_congr_ae + `h_reg.integral_deriv_eq_zero`) | **No (h_reg.integral_deriv_eq_zero load-bearing)** — `IsRegularDensity` 6 field 中 `integral_deriv_eq_zero` だけが claim form、削除すれば body 1 行目で詰まる |
| `FisherInfoV2.lean:157` | `integral_logDeriv_density_eq_zero` | `∫ logDeriv f · f = 0` | 5-line `calc` 同上 (V2 analog) | **No** 同上 |
| `FisherInfoV2DeBruijn.lean:262` | `deBruijn_identity_v2` | `HasDerivAt (...) ((1/2) * fisherInfoOfDensityReal h_reg.density_t) t` | 1 行 `:= h_reg.derivAt_entropy_eq_half_fisher_v2` (literal alias) | **No (load-bearing field)** — structure field が結論型と同一、`h_reg` 削除で body 全空 |
| `FisherInfoV2DeBruijnBody.lean:238` | `deBruijn_identity_v2_of_heat_flow` | `HasDerivAt (...) ((1/2) * fisherInfoOfDensityReal (p t)) t` | 1 行 `:= h_ibp` (literal alias via `IsIBPHypothesis := HasDerivAt ...` Iff.rfl) | **No (literal alias)** — body は `Iff.rfl` 展開だけ |
| `FisherInfoV2HeatFlowBody.lean:240` | `deBruijn_identity_v2_of_heat_subhyp` | 同上 | 1 行 forward to `deBruijn_identity_v2_of_heat_flow` | **No (transitive literal alias)** |

→ **constructive recovery 候補は 0 件**。本 cluster の核心は EPI 主定理に
hypothesis-form で predicate を渡すための load-bearing pass-through であり、
hypothesis 削除なしには constructive 経路を提供できない (本来は sorry を残すか、
hypothesis を残すかの二択)。Pilot Pattern B (Hoeffding の `IsHoeffdingMinimizer-
FullSupport.of_pos`) のような「regularity に reducible」declaration は本
cluster に存在しない。

### transitive sorry の handling 方針 (Pilot Pattern C、Phase A 完了後再起動時)

本 plan を Phase A 完了後に再起動する際 (Case γ shift)、上流 sorry 化に伴う
transitive sorry は EPI/Stam family の各 EPI* file に **大規模に** 波及する
(EPIStamDeBruijnConclusion / EPIStamToBridge / EPIL3Integration / EPIStamDischarge
の Gaussian/general path が連鎖)。

**回避策**: 統合 sweep として EPI/Stam + FisherInfo を 1 plan で扱い、
Phase Z (closed-by-successor migration、Chernoff Round 3 で確立済) の Recipe A/B/C
を **EPI/Stam shape に拡張**して適用。

### ⚠ HONESTY ALERT / FALSE 検出 (Pattern H、R8)

`rg '⚠|HONESTY ALERT|FALSE' Common2026/Shannon/FisherInfo*.lean` 結果: **0 hits**。
本 cluster には著者明示の honest defect 注記は無し。

(参考: Pattern H 該当は EPI Phase A 完了前後で `EPIStamToBridge.lean:451-493` の
`fisherInfoOfDensityReal ((h_reg_*.reg_at t ht).density_t)` shape caveat 注記が
近い position だが、これは Phase A 側の documentation で本 plan scope 外)

## Phase 0 — 規模見積もり + Phase A 共存判定 + tier 5 defect inline 検出 📋

本 plan の **唯一実施する Phase** (Phase 1 以降は Phase A 完了後の再起動 plan に委譲)。

### Phase 0 steps

- [ ] step 1 — Context 節の計数表を **本 session の Phase 0 完了時** に再 verify (Phase A side の patch で declaration が動いた / tag が増減した可能性)
- [ ] step 2 — Phase A 共存判定の結論「Case α (全降格)」を確認、handoff-epi.md
      の最新 state (今 session に追加 commit があれば回収) と整合性確認
- [ ] step 3 — tier 5 defect inline 検出表を verbatim 確認 (上記 Context 節
      「tier 5 defect」表) + signature 改変が必要な declaration を列挙
      (本 sweep では touch しないが、後続 plan の input として保存)
- [ ] step 4 — 再起動条件 3 条件 (handoff-epi.md Phase A 完了 / EPI/Stam migration
      plan 起草済 / `IsRegularDeBruijnHypV2` field restructuring 完了) を文書化、
      handoff-sorry-migration.md「Next step → A」に明示済か確認

### Phase 0 退化境界の predict

本 plan で signature 改変を実施しないため、退化境界 (Dirac 0 / `gaussianReal 0 0`
等) の predict は **不要**。Phase A 完了後再起動時に改めて verbatim 確認。

参考データ (CLAUDE.md「具体的数値・型予測の verbatim 確認」由来、本 plan では
predict しないが将来 reference):
- `IsRegularDensity` の `pos : ∀ x, 0 < density x` field は Dirac (0 measure) を
  構造で除外 → 退化境界での vacuous instance を構造的に不可
- `IsRegularDeBruijnHypV2` の `Z_law : P.map Z = gaussianReal 0 1` field は退化
  measure を排除 (verbatim 確認、`FisherInfoV2DeBruijn.lean:241`)

## Phase 1 — declaration-direct tag sweep (Phase 0 判定により skip) 📋

**本 plan 本 session では実施しない**。Phase 0 判定 = Case α (全降格) のため。

(将来 Phase A 完了後の再起動 plan で改めて起草)

予定 declaration table (将来 reference、本 plan では touch しない):

| file:line | decl 名 | 現タグ | 削除/置換予定タグ | Pattern | sub-pattern | 想定 sorry 数 | retract 数 | tag-only 削除 |
|---|---|---|---|---|---|---:|---:|---:|
| `FisherInfo.lean:127` | `integral_logDeriv_pdf_eq_zero` | `@audit:suspect(fisher-info-moonshot-plan)` | `@residual(wall:stam)` 候補 | P | load-bearing field (IsRegularDensity.integral_deriv_eq_zero) | 1 | 0 | 0 |
| `FisherInfoV2.lean:157` | `integral_logDeriv_density_eq_zero` | 同上 | 同上 | P | 同上 (V2 analog) | 1 | 0 | 0 |
| `FisherInfoV2DeBruijn.lean:262` | `deBruijn_identity_v2` | 同上 | `@residual(wall:stam)` 候補 + signature 改変 (h_reg 削除) | P | tier 5 load-bearing predicate bundling (`IsRegularDeBruijnHypV2.derivAt_entropy_eq_half_fisher_v2` field = conclusion) | 1 | 0 (predicate `IsRegularDeBruijnHypV2` は EPI active consumer あり、retract 不可) | 0 |
| `FisherInfoV2DeBruijnBody.lean:238` | `deBruijn_identity_v2_of_heat_flow` | 同上 | `@residual(wall:stam)` 候補 + signature 改変 (h_ibp 削除) | P | tier 5 literal alias (`IsIBPHypothesis := HasDerivAt ... Iff.rfl`) | 1 | 0 (predicate `IsIBPHypothesis` は EPI 連鎖 consumer あり) | 0 |
| `FisherInfoV2HeatFlowBody.lean:240` | `deBruijn_identity_v2_of_heat_subhyp` | 同上 | `@residual(wall:stam)` 候補 + signature 改変 | P | tier 5 transitive literal alias | 1 | 0 | 0 |
| **合計** | | | | | | **5** | **0** | **0** |

**中央予測** (本 plan 本 session の出力ではなく、将来 Phase A 完了後の再起動
plan で実施した場合の予測値):
- 新規 sorry 数: **5** (全 5 declaration 各 1 件)
- retract-candidate 付与数: **0** (predicate def 側は EPI active consumer により retract 不可、`@audit:retract-candidate` 付与で意味矛盾)
- tag-only 削除数: **0** (Hoeffding pilot や RateDistortion sweep のような「タグだけ消す」case は本 cluster に存在しない、全件 signature 改変必要)

## Phase 2 — incidental tier 4 → tier 2 移行 (本 sweep では 0 件) 📋

**本 plan 本 session では実施しない**。本 cluster には tier 4 legacy (`@audit:staged`
/ 散文 `🟢ʰ` / `@audit:defer` / `@audit:closed-by-successor`) が **0 件** で、
incidental migration 対象なし。

`@audit:suspect` のみ 5 件は tier 4 legacy だが、touch しない方針 (上記 Phase 1 skip)。

## Phase V — verify + handoff 反映 📋

本 plan 本 session の Phase V は:

- [ ] step 1 — `Common2026/Shannon/FisherInfo*.lean` 5 file の **改変なし**を確認
      (`git diff` / `git status` で本 family 内 .lean 差分 0)
- [ ] step 2 — `handoff-sorry-migration.md`「Next step → A」section に Phase A
      完了後の本 plan 再起動条件 (3 条件) を明示反映
- [ ] step 3 — 本 plan の判定結論 (Case α 全降格) を Round 4 全降格対象 family
      list に列挙 (orchestrator 出力で family family roster から外す)

本 plan 本 session では **honesty-auditor は起動しない** (新規 `sorry` + `@residual`
を含む commit が 0 件、CLAUDE.md「Independent honesty audit」起動条件不充足)。

## 未決事項

planner が判断つかない事項 (Phase A 完了後再起動時に re-evaluate):

1. **`IsRegularDeBruijnHypV2` field restructuring の前提条件成立タイミング**:
   EPI/Stam Phase A 完了後でも `IsRegularDeBruijnHypV2` を EPIStamDischarge.lean
   が `reg_at : ∀ t > 0, IsRegularDeBruijnHypV2 X Z P t` field で hypothesis 形に
   消費し続ける可能性 → 本 cluster の sorry-based migration は `EPIStamDischarge`
   側の predicate signature 改変が **先行必要**。EPI/Stam migration plan の Phase 0
   で判定要請。
2. **`wall:stam` への集約 vs `plan:fisher-info` の slug 新設**: 5 declaration の
   `@residual` 行先選択。`wall:stam` 集約は 1 wall 増殖無しで済むが、EPI/Stam の
   shared wall lemma 設計次第。
3. **`integral_logDeriv` 系 2 件の sweep separation**: V2 analog の 2 件は EPI Phase A
   直撃ではない (Gaussian wrapper 経由間接) ため、Phase A 完了前に切り出して
   先行 sweep 可能性 → ただし `IsRegularDensity` field = `integral_deriv_eq_zero`
   が core claim で signature 改変は EPIL3 Gaussian discharge path への影響評価
   要 (Phase 0 で再評価)。
4. **本 plan vs `epi-stam-sorry-migration-plan` の責任分担**: 本 cluster が
   EPI/Stam migration plan の sub-plan として吸収される設計の可能性 → 後続 plan
   起草時に判断。

## 撤退ライン

- **L-MIG-EPI-INTEGRATION** (発火確率 高、本 plan の default 撤退): 本 plan で
  実施する全 declaration の signature 改変が EPI Phase A active reference chain
  を壊す → **本 session の Phase 0 で確定 (Case α 全降格)**、Phase 1 以降は
  Phase A 完了後の再起動 plan に委譲。本撤退ラインは default として既に発火済。
- **L-MIG-RECURSIVE-REDESIGN** (発火確率 中): 再起動 plan 起草時に
  `IsRegularDeBruijnHypV2` の field structure を保ったまま honest 化する path
  が存在しない (= EPI/Stam の predicate signature を改変するか、本 cluster の
  sorry を残すか二択) → EPI/Stam migration plan で predicate 再設計を実施し、
  本 plan は再起動 plan として完全に書き直し。
- **L-DBD-2-α** (degenerate-definition exploitation、発火確率 低): Fisher info の
  退化境界 (`fisherInfoOfDensityReal` の Dirac / `gaussianReal 0 0` 退化) を
  突いた vacuous instance → 本 plan の signature 改変対象 declaration には
  `pos : ∀ x, 0 < density x` / `Z_law : P.map Z = gaussianReal 0 1` 等の構造で
  退化境界を排除しているため発火不能。確認は再起動 plan の Phase 0 で再 verify。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-26 — Phase 0 判定 = Case α 全降格 (本 plan 起草時の起動判定)**:
   orchestrator brief で「Phase A 共存リスクが高い場合は plan を『scope 外
   判定 + 再開条件』だけにして短くまとめて OK」とあり、verbatim 確認の結果
   全 5 declaration が EPI Phase A active reference に直接含まれることを確認
   (特に `deBruijn_identity_v2` 系 3 件は EPIStamDeBruijnConclusion / EPIStamToBridge
   での直接 consumer、Phase A A-3 chain rule plumbing 直撃)。
   - 本 plan は **Round 4 sorry-based migration の起動対象 family から外す**
   - Phase A 完了後 (handoff-epi.md A-3〜A-V 終了 + EPI/Stam migration plan
     起草 + `IsRegularDeBruijnHypV2` field restructuring 完了) の再起動 plan を
     0 から書き直す方針
   - 本 plan は Phase 0 判定 + Phase 1 以降の予定 inventory + tier 5 defect
     inline 検出表 + 再起動条件 + 撤退ラインのみ残置 (本 session で書く本文は
     上記)
   - 並列起動された他 Round 4 family planner (Chernoff Round 3 完了後の継続
     candidate) と本 plan は file 所有権分離済 (`docs/shannon/fisher-info-sorry-
     migration-plan.md` 単独)
2. **tier 5 defect inline 検出の報告のみ・rewrite なし** (本 plan 起草時に
   発見、CLAUDE.md「検証の誠実性」"見つけた側" inline policy に準拠):
   - `deBruijn_identity_v2:262` (load-bearing predicate bundling、`h_reg.derivAt_entropy_eq_half_fisher_v2` 直接抽出)
   - `deBruijn_identity_v2_of_heat_flow:238` (仮説型≡結論型 literal alias、body `:= h_ibp`)
   - `deBruijn_identity_v2_of_heat_subhyp:240` (上の transitive literal alias)
   - `IsRegularDeBruijnHypV2.derivAt_entropy_eq_half_fisher_v2` field (load-bearing structure field)
   - `IsIBPHypothesis := HasDerivAt ... Iff.rfl` (`isIBPHypothesis_iff:213-220` で公式に「仮説型 ≡ 結論型」を declare 済)
   - これら全件、本 plan で **silent fix しない** (tier 5 defect の rewrite は当該
     declaration の owner = EPI/Stam family と統合判断必要)。**(a) defect の場所と
     種類を本 plan の Context 節 + 判断ログに報告**、**(b) その上に build しない**
     方針で、Phase A 完了後の再起動 plan で signature 改変を扱う。

## Files to read (再起動 plan 起草時に必須)

本 plan を Phase A 完了後に再起動する際の参照 file list:

- `.claude/handoff-epi.md` — Phase A の最終 state (closed 時の最新 commit hash)
- `.claude/handoff-sorry-migration.md` — Round 4 全体の state
- `docs/audit/sorry-migration-runbook.md` — Step 1-4 手順 + Pattern A-J
- `docs/audit/audit-tags.md` — vocab SoT
- `docs/shannon/chernoff-sorry-migration-plan.md` — Phase Z recipe (closed-by-successor migration 用) の reference
- `docs/shannon/epi-stam-sorry-migration-plan.md` — (未起草) EPI/Stam family の sorry-based migration plan、本 plan の前提条件
- `Common2026/Shannon/FisherInfo*.lean` (5 file) — Phase A 完了後の状態を再 verify
- `Common2026/Shannon/EPIStamDischarge.lean:97-205` — `IsStamInequalityHyp` /
  `IsRegularDeBruijnHypFamily` の Phase A 完了後 signature を verbatim 確認

## 計数 — Phase 0 完了時の最終 verdict

| 項目 | 本 plan 本 session |
|---|---:|
| 新規 sorry 数 | **0** (sweep 実施しない、Phase A 完了後再起動 plan に委譲) |
| retract-candidate 付与数 | **0** |
| tag-only 削除数 | **0** |
| touch する .lean file 数 | **0** |
| touch する .md file 数 | **1** (本 plan のみ) |
| commit 数 | 1 (本 plan 起草 commit のみ) |
| Phase A active 同期 file (touch 禁止 list) | 全 5 file (`FisherInfo.lean`, `FisherInfoV2.lean`, `FisherInfoV2DeBruijn.lean`, `FisherInfoV2DeBruijnBody.lean`, `FisherInfoV2HeatFlowBody.lean`) |
