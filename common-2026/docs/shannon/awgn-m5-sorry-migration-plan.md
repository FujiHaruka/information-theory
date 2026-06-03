# AWGN M5 — true sorry-based migration plan (Path 1)

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md)
> + [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md)
> + [`awgn-converse-aux-plan.md`](awgn-converse-aux-plan.md)
> + [`awgn-power-constraint-realizable-pivot-plan.md`](awgn-power-constraint-realizable-pivot-plan.md)
> + [`awgn-mi-decomp-plan.md`](awgn-mi-decomp-plan.md)
>
> **Sister precedent**: [`docs/audit/audit-tags.md`](../audit/audit-tags.md)「Honesty 階層」
> + commit [`34e17bc`](../../) EPI-Stam Cluster C+D (Tier 4 → Tier 3
> bookkeeping migration、本 plan の **入口**) +
> commit [`37284f1`](../../) AWGN M5 9 件 Tier 4 → Tier 3 bookkeeping (本 plan の
> **直接の前段**)
>
> **Predecessor (bookkeeping-only)**:
> [`awgn-sorry-migration-plan.md`](awgn-sorry-migration-plan.md) (Round 4 Wave A、
> 36 declaration を **signature 改変なし** で tag migration 完了済、
> 同 plan §line 198 verbatim「load-bearing wrapper の sorry 化方針 (Phase 1 主軸):
> 36 declaration の signature 改変は **しない**」)。
>
> 本 plan はその scope を **意図的に超え** て、9 件の load-bearing predicate を
> Honesty 階層 Tier 3 (`@audit:retract-candidate(load-bearing-predicate)`、
> bookkeeping) → **Tier 2** (`sorry` + `@residual(<class>:<slug>)`、新規実装の
> 唯一の honest 撤退口) に格上げする。Path 1 = 「**真の sorry-based migration**」。

## Context — 9 件の現状 (verbatim)

`rg -n '@audit:retract-candidate\(load-bearing-predicate\)' InformationTheory/Shannon/AWGN*.lean`
(commit `37284f1` 時点):

| # | file:line | declaration | 種別 | 既存タグ |
|---|---|---|---|---|
| 1 | `AWGNConverseDischarge.lean:148` | `def PerLetterIntegrabilityForConverse` | sub-bound predicate (load-bearing) | `@audit:retract-candidate(load-bearing-predicate)` (旧 slug `awgn-converse-feasible`) |
| 2 | `AWGNConverseDischarge.lean:168` | `def ContinuousMIChainRuleForConverse` | sub-bound predicate (load-bearing) | 同上 |
| 3 | `AWGNConverseDischarge.lean:185` | `def MarkovChainForConverse` | sub-bound predicate (genuine regularity、Markov chain) | docstring に「regularity hypothesis、load-bearing ではない」と明示 (line 174-178) |
| 4 | `AWGNConverseDischarge.lean:218` | `def IsAwgnConverseFeasible` | bundle predicate (3 sub-bound 連言) | `@audit:retract-candidate(load-bearing-predicate)` |
| 5 | `AWGNConverseDischarge.lean:1226` | `theorem isAwgnConverseFeasible_discharger` | bundle hyp consumer (genuine 580-line body) | 同上 |
| 6 | `AWGNConverseDischarge.lean:1268` | `theorem awgn_converse_F3_discharged` | thin wrapper (`2 ≤ M` → `NeZero M` + delegation) | 同上 |
| 7 | `AWGNAchievabilityDischarge.lean:156` | `def IsContinuousAEPGaussian` | continuous AEP predicate (load-bearing) | `@audit:retract-candidate(load-bearing-predicate)` (旧 slug `continuous-aep-gaussian`) |
| 8 | `AWGNAchievabilityDischarge.lean:562` | `def IsAwgnRandomCodingBound` | random coding integral bound predicate (load-bearing) | 同上 (旧 slug `awgn-random-coding-bound`) |
| 9 | `AWGNAchievabilityDischarge.lean:763` | `def IsAwgnPowerConstraintHonest` | power constraint mass bound predicate (`P_cb` / `P_target` 分離形、load-bearing) | 同上 (旧 slug `awgn-power-constraint-honest`) |
| 10 | `AWGNAchievabilityDischarge.lean:842` | `def IsAwgnRandomCodingFeasible` | bundle predicate (3 sub-bound + 共有 `P'` witness、load-bearing) | 同上 (旧 slug `awgn-random-coding-feasible`) |

**実件数 = 10 declaration** (orchestrator brief の「9 件」は近似値。`PerLetterIntegrability` / `ContinuousMIChainRule` / `MarkovChain` / `IsAwgnConverseFeasible` / `discharger` / `F3_discharged` の **6 件 converse 側 + 4 件 achievability 側 = 10 件**。`MarkovChainForConverse` (line 185) は本来 genuine regularity だが `IsAwgnConverseFeasible` bundle field 経由で hypothesis 形式に組み込まれているため移行 scope に含めた。Phase 0 で再判定する)。

## Context — 既存 import / consumer graph (verbatim)

`rg -n '^import' InformationTheory/Shannon/AWGN*.lean InformationTheory.lean` および
`rg -nc '<predname>' InformationTheory/Shannon/` で確認 (2026-05-28):

```
AWGN.lean (基盤定義)
└── AWGNConverseDischarge.lean (本 plan converse 側、5 declarations)
      └── AWGNConverse.lean (`awgn_converse` 1-line `exact` delegation、
            `IsAwgnConverseFeasible` hyp + `h_mi_bridge_per_letter` hyp pass-through)
            └── AWGNMain.lean (`awgn_converse` を呼ばない — F-3 wiring は別 path)
└── AWGNAchievability.lean (achievability stub、body sorry 済)
      └── AWGNAchievabilityDischarge.lean (本 plan achievability 側、4 declarations
            + `isAwgnTypicalityHypothesis` + `awgn_achievability_F1_via_staged_hyps`
            + `awgn_theorem_F4_discharged_F1_via_staged` の hypothesis-form consumer 3)
            └── (外部 consumer 無し、`AWGNMain.awgn_channel_coding_theorem` は
                  2026-05-27 F-1/F-3 peer migration で `h_feasible` hyp pass-through を廃止)
```

**外部 hypothesis-form consumer の verbatim 数え**:

- **converse 5 件**: `AWGNConverse.awgn_converse` (`AWGNConverse.lean:75-89`) のみが
  `h_feasible : IsAwgnConverseFeasible` + `h_mi_bridge_per_letter` を取って
  `awgn_converse_F3_discharged` に 1-line `exact` delegate。`AWGNConverse.lean`
  の外には `IsAwgnConverseFeasible` を取る consumer 無し。
- **achievability 4 件**: self-file `AWGNAchievabilityDischarge.lean` 内のみ
  (`awgn_avg_error_union_bound` (line 602) / `isAwgnTypicalityHypothesis`
  (line 947) / `awgn_achievability_F1_via_staged_hyps` (line 1582) /
  `awgn_theorem_F4_discharged_F1_via_staged` (line 1622))。
  `AWGNMain.awgn_channel_coding_theorem` (line 76-90) は `h_feasible` hyp を
  取らず `awgn_achievability` を 1-line `exact` 委譲、`awgn_achievability` は
  body sorry + `@residual(plan:awgn-achievability-typicality-plan)` で
  既に正規 sorry-based 形 (predicate 不依存)。

→ **predicate 削除の blast radius は AWGN family の closure path 1 本のみに局所化**。
F-1/F-2/F-4 main wrapper 系は影響を受けない (2026-05-27 peer migration の
利得が本 plan で initial use)。

## ゴール / Approach

### 全体方針 — Tier 3 → Tier 2 への 3 段分類

CLAUDE.md「sorry を書けない箇所での対処順序」第一選択 (定義書換で `sorry` を proof body
に逃がす) を 10 declaration それぞれに適用。各 declaration は以下の 3 ルート分類:

- **Route A — predicate 削除 (純削除)**: 当該 predicate が `IsAwgnConverseFeasible` /
  `IsAwgnRandomCodingFeasible` bundle field 経由でしか使われておらず、bundle 自身を
  削除すれば consumer も連動して書換できる sub-bound predicate (`PerLetterIntegrability` /
  `ContinuousMIChainRule` / `MarkovChain` / `IsContinuousAEPGaussian` /
  `IsAwgnRandomCodingBound` / `IsAwgnPowerConstraintHonest`)。
- **Route B — shared sorry 補題化 (共有 Mathlib 壁、`docs/audit/audit-tags.md`
  「共有 Mathlib 壁」)**: 当該 predicate 自身を削除し、その「結論」を新規 file
  `InformationTheory/Shannon/AwgnWalls.lean` の **shared sorry 補題** に格上げする
  (`continuous-aep-gaussian` / `awgn-random-coding-bound` / `awgn-power-constraint-honest`
  の 3 つは Mathlib 壁 = analytic content、wall name register `continuous-aep` 系で
  promote 候補)。
- **Route C — bundle 削除 + consumer signature 書換 (`@residual(plan:<slug>)`)**:
  bundle 自身 (`IsAwgnConverseFeasible` / `IsAwgnRandomCodingFeasible`) は削除し、
  consumer (`isAwgnConverseFeasible_discharger` / `awgn_converse_F3_discharged` /
  `awgn_converse` / `isAwgnTypicalityHypothesis` / `awgn_achievability_F1_via_staged_hyps`
  / `awgn_theorem_F4_discharged_F1_via_staged`) の signature から hyp を除去、body を
  `sorry` + `@residual(plan:awgn-m5-sorry-migration-plan)` または
  `@residual(wall:<wall-name>)` に置換。

**設計判断**: Route A の sub-bound predicate を **route B (shared sorry 補題)** に置換
することで、各 consumer は「shared sorry 補題を呼ぶ普通の lemma call」に縮約される。
これは sister 34e17bc EPI-Stam Cluster C `wall:debruijn-integration` で initial use
が達成されたパターン (`debruijnIdentityV2_holds` shared sorry 補題、`EPIL3Integration.lean`
1297 周辺 verbatim 確認済) と同型。

### Phase 構成

- **Phase 0** — verbatim 棚卸し + 共有 sorry 補題候補確定 + Approach 確定 (本 plan)
- **Phase 1 — Wall name register 提案** (`docs/audit/audit-tags.md` への提案 PR):
  既存 register に類似 wall が無い 3 wall を Proposed 表に追加
- **Phase 2 — shared sorry 補題 file 新設** (`InformationTheory/Shannon/AwgnWalls.lean`):
  3 shared sorry 補題 (`continuousAepGaussian` / `awgnRandomCodingBound` /
  `awgnPowerConstraintHonest` の analytic content を Mathlib 壁として publish)
- **Phase 3 — predicate 削除 + consumer signature 書換**:
  - **3-α (converse 側 6 declaration)**: bundle `IsAwgnConverseFeasible` + 3 sub-bound
    predicate を削除、`isAwgnConverseFeasible_discharger` / `awgn_converse_F3_discharged`
    / `awgn_converse` の signature から hyp 除去、body は `awgn_converse_single_shot_call`
    + Phase B-DPI + Phase B-chain shared sorry 補題 + Phase C-2 sum form の chain に置換
    (`sorry` + `@residual(plan:awgn-m5-sorry-migration-plan)` を 1 件残置)
  - **3-β (achievability 側 4 declaration)**: bundle `IsAwgnRandomCodingFeasible`
    + 3 sub-bound predicate を削除、`isAwgnTypicalityHypothesis` /
    `awgn_achievability_F1_via_staged_hyps` / `awgn_theorem_F4_discharged_F1_via_staged`
    の signature から hyp 除去、body は shared sorry 補題 3 件を thread して
    `awgn_extract_AwgnCode` (line 856 — 既に genuine) で `AwgnCode` 抽出
- **Phase V — 検証 + honesty audit + roadmap update**:
  - 全 touched file `lake env lean` 0 errors
  - `honesty-auditor` 起動 (CLAUDE.md「Independent honesty audit」)
  - `docs/shannon/awgn-moonshot-plan.md` Phase 進捗ブロック + 判断ログ更新
  - `docs/textbook-roadmap.md` Ch.9 行 update

## Phase 0 — verbatim 棚卸し + shared sorry 補題候補確定 📋

- [ ] **0-1**: 10 declaration の signature + docstring + 既存タグを verbatim で本 plan の
      `Context — 9 件の現状` 表に転記 (上記表で完了済、再確認のみ)
- [ ] **0-2**: 各 declaration の **hypothesis-form consumer** を
      `rg -n '<PredName>' InformationTheory/Shannon/` で列挙、本 plan の
      `Context — 既存 import / consumer graph` セクションに転記済 — 再確認のみ
- [ ] **0-3**: **`MarkovChainForConverse` の genuine vs load-bearing 再判定** —
      docstring `line 174-178` verbatim 「regularity hypothesis、load-bearing ではない、
      Mathlib 壁ではない」が正しいか independent verify:
      - **判定材料**: `IsMarkovChain` (CondMutualInfo.lean:73) instance 自動 derive 可能か
        `awgnConverseJoint` で確認 → 可なら Route A (純削除 → genuine instance に置換)
      - **不可なら**: shared sorry 補題候補 (wall name `awgn-converse-markov` 等) 提案 →
        Phase 1 register 追加
- [ ] **0-4**: 3 共有 sorry 補題候補に対応する wall name の `docs/audit/audit-tags.md`
      Wall name register (line 52) との照合:
      - `continuous-aep-gaussian` → 既存 wall `continuous-aep` の specialization 形か独立か
      - `awgn-random-coding-bound` → 新規 wall (Gaussian random coding integral bound)
      - `awgn-power-constraint-honest` → 新規 wall (chi-square SLLN on `gaussianCodebook`)
- [ ] **0-5**: import 依存 verbatim 確認 — `InformationTheory/Shannon/AwgnWalls.lean` (新規) が
      持つべき import = `InformationTheory.Shannon.AWGN` (`gaussianCodebook` / `awgnChannel`
      access) + `InformationTheory.Shannon.ChannelCoding` (`AwgnCode` / `errorProbAt`) +
      `Mathlib.Probability.Distributions.Gaussian.Real`。**Import cycle check**:
      `AwgnWalls.lean` → `AWGN.lean` の 1 方向、`AWGNAchievabilityDischarge.lean` /
      `AWGNConverseDischarge.lean` → `AwgnWalls.lean` の追加 import で循環無し。

## Phase 1 — Wall name register 提案 (`docs/audit/audit-tags.md`) 📋

`docs/audit/audit-tags.md`「Wall name register」(line 52) に **3 提案 wall** を Proposed 表
(line 78) に追加する PR。本 plan の Phase 0-4 確定結果に基づく。

- [ ] **1-1**: 新規 wall `awgn-continuous-aep-gaussian` (旧 slug `continuous-aep-gaussian`
      を wall 化)
- [ ] **1-2**: 新規 wall `awgn-random-coding-bound` (Gaussian random codebook 上の
      union bound と Fubini + IndepFun + AEP-chain の analytic content)
- [ ] **1-3**: 新規 wall `awgn-power-constraint-honest` (chi-square SLLN on
      `gaussianCodebook` の analytic content)

各 wall に対して `docs/audit/audit-tags.md` の規約 `(1) loogle で 0 件確認 (本当に
Mathlib 不在か)、(2) 既存 register に類似がないか確認、(3) 本表に直接追記してコミット`
を厳守 (Phase 1 は本 plan 範囲、Phase 1 で書き換える file は `docs/audit/audit-tags.md`
のみ)。

**Promote 判定**: 「2+ family で再利用」または「1 family 複数 file で参照」が trigger。
本 plan 適用後の状態は **1 family / 2 file (`AwgnWalls.lean` + 各 consumer file)** で、
trigger 条件は満たす (`audit-tags.md` line 88 verbatim)。

## Phase 2 — shared sorry 補題 file 新設 `InformationTheory/Shannon/AwgnWalls.lean` 📋

新規 file。3 shared sorry 補題のみを集約 (各 declaration は `sorry` 1 + `@residual(wall:<name>)` 1)。

- [ ] **2-1**: file skeleton
      (CLAUDE.md「Skeleton-driven Development」、import pinpoint、namespace
      `InformationTheory.Shannon.AWGN`)
- [ ] **2-2**: `theorem continuousAepGaussian_holds` — 3 sub-bound (mass / volume /
      independent-pair) を返す Σ 形 (旧 `IsContinuousAEPGaussian` body の Mathlib-shape
      化)。body `sorry` + `@residual(wall:awgn-continuous-aep-gaussian)`
- [ ] **2-3**: `theorem awgnRandomCodingBound_holds` — `∀ ε R, R < capacity → ∃ N₀,
      ∀ n ≥ N₀, ∀ M ≤ ⌈exp(nR)⌉, ∀ A measurable, …` の integral bound (旧
      `IsAwgnRandomCodingBound` body の lemma 化)。body `sorry` +
      `@residual(wall:awgn-random-coding-bound)`
- [ ] **2-4**: `theorem awgnPowerConstraintHonest_holds (P_cb P_target N)` —
      `(P_cb < P_target)` 条件付きで mass bound を返す (旧 `IsAwgnPowerConstraintHonest`
      body の lemma 化、`P_cb = P_target` 退化 case 除外で v1 false statement
      問題を回避)。body `sorry` + `@residual(wall:awgn-power-constraint-honest)`
- [ ] **2-5**: `InformationTheory.lean` に `import InformationTheory.Shannon.AwgnWalls` を 1 行追加
- [ ] **2-6**: `lake env lean InformationTheory/Shannon/AwgnWalls.lean` で 0 errors / 3 sorry
      warning 確認

**確認**: Phase 2 完了時点で 3 sorry + 3 `@residual(wall:...)`、各 declaration の
signature は **regularity precondition のみ** (`hP : 0 < P` 等)、core claim 抱える
predicate hypothesis 無し。Tier 2 = `sorry` + `@residual(wall:<name>)` honest 撤退口。

## Phase 3-α — converse 側 6 declaration sorry-based 移行 📋

Phase 3-α は `AWGNConverseDischarge.lean` + `AWGNConverse.lean` を touch。

- [ ] **3α-1**: `MarkovChainForConverse` 取扱判定 (Phase 0-3 結果に依拠):
  - **Route A (純削除)**: `IsMarkovChain (awgnConverseJoint h_meas c) (Prod.fst, encoder
    ∘ ω.1, Prod.snd)` の instance を `awgn_converse_F3_discharged` body 内で
    `awgnConverseJoint_markov_chain_of_code_structure` (新規 genuine lemma、
    line 1226 周辺で導出) として inline、predicate def 削除 → consumer 引数除去
  - **Route B (shared sorry)**: 4 wall (`awgn-converse-markov-regularity`) として
    `AwgnWalls.lean` に追加 (Phase 2 補追)
- [ ] **3α-2**: `PerLetterIntegrabilityForConverse` 削除 →
      `awgnPerLetterIntegrability_holds` を `AwgnWalls.lean` に追加 (Phase 2 補追、
      `@residual(wall:awgn-per-letter-integrability)`)
- [ ] **3α-3**: `ContinuousMIChainRuleForConverse` 削除 →
      `awgnContinuousMIChainRule_holds` を `AwgnWalls.lean` に追加 (Phase 2 補追、
      `@residual(wall:awgn-continuous-mi-chain-rule)` — 既存 `multivariate-mi` wall と
      類似だが iid 仮定が無い AWGN 専用形)
- [ ] **3α-4**: `IsAwgnConverseFeasible` bundle 削除 (`AWGNConverseDischarge.lean:218`)
- [ ] **3α-5**: `isAwgnConverseFeasible_discharger` (`line 1226`) signature 書換:
      `(h_feasible : IsAwgnConverseFeasible ...)` 引数除去、body は Phase B-Fano +
      shared sorry 補題 3 件 (Markov 取扱判定次第で 2-4 件) を thread して 580 行 chain を
      assemble (既存 body のまま、`obtain ⟨h_per_letter, h_chain, h_markov⟩ := h_feasible hM c`
      の左辺を shared sorry 補題呼出に書換)
- [ ] **3α-6**: `awgn_converse_F3_discharged` (`line 1268`) signature 書換: 同上、
      `h_feasible` 引数除去、body は `isAwgnConverseFeasible_discharger` への delegation
      を維持
- [ ] **3α-7**: `AWGNConverse.awgn_converse` (`line 75`) signature 書換:
      `(h_feasible : IsAwgnConverseFeasible …)` 引数除去 + `(h_mi_bridge_per_letter …)`
      引数除去 (本 plan で `awgn-mi-bridge-plan.md` 委任、`@residual(plan:awgn-mi-bridge-plan)`
      で wrapper body 内に 1 sorry 残置) → body は `awgn_converse_F3_discharged` delegate
- [ ] **3α-8**: file 単独で `lake env lean InformationTheory/Shannon/AWGNConverseDischarge.lean`
      + `lake env lean InformationTheory/Shannon/AWGNConverse.lean` の 2 file 検証 0 errors

## Phase 3-β — achievability 側 4 declaration sorry-based 移行 📋

Phase 3-β は `AWGNAchievabilityDischarge.lean` のみ touch (consumer 全てが self-file)。

- [ ] **3β-1**: `IsContinuousAEPGaussian` predicate 削除 (Phase 2 で `AwgnWalls.lean` の
      shared sorry 補題に集約済)
- [ ] **3β-2**: `IsAwgnRandomCodingBound` predicate 削除 (同上)
- [ ] **3β-3**: `IsAwgnPowerConstraintHonest` predicate 削除 (同上)
- [ ] **3β-4**: `IsAwgnRandomCodingFeasible` bundle 削除
      (`AWGNAchievabilityDischarge.lean:842`)
- [ ] **3β-5**: `awgn_avg_error_union_bound` (`line 602`) signature 書換:
      `(h_aep : IsContinuousAEPGaussian)` + `(h_rand : IsAwgnRandomCodingBound)` 引数除去、
      body は `continuousAepGaussian_holds` + `awgnRandomCodingBound_holds` 呼出に置換
- [ ] **3β-6**: `isAwgnTypicalityHypothesis` (`line 947`) signature 書換:
      `(h_feasible : IsAwgnRandomCodingFeasible)` 引数除去、body は
      `obtain ⟨P', hP'_pos, hP'_lt_P, hR_lt_P'C, h_aep', h_rand', h_power'⟩ := h_feasible …`
      を **shared sorry 補題 3 件 + `awgnPowerWitness_exists` (新規 helper、
      `∃ P' ∈ (0, P), …` の slack 選択を genuine 化)** に置換
- [ ] **3β-7**: `awgn_achievability_F1_via_staged_hyps` (`line 1582`) signature 書換:
      `h_feasible` 引数除去、body は `isAwgnTypicalityHypothesis` 呼出
- [ ] **3β-8**: `awgn_theorem_F4_discharged_F1_via_staged` (`line 1622`) signature 書換:
      同上
- [ ] **3β-9**: file 単独で `lake env lean InformationTheory/Shannon/AWGNAchievabilityDischarge.lean`
      検証 0 errors

## Phase V — closure 📋

- [ ] **V-1**: 全 touched file の `lake env lean` 検証 0 errors:
      `AwgnWalls.lean` (新規) / `AWGNConverseDischarge.lean` / `AWGNConverse.lean` /
      `AWGNAchievabilityDischarge.lean` / `InformationTheory.lean` (import 1 行追加)
- [ ] **V-2**: `lake env lean` 検証で各 file の `sorry` 件数を verbatim 確認:
      - 期待値: `AwgnWalls.lean` で 3-6 sorry (wall 数次第)、各 sorry に
        `@residual(wall:<name>)` 1 件併設
      - consumer file (`AWGNConverseDischarge.lean` / `AWGNAchievabilityDischarge.lean`)
        は **0 sorry** (predicate hyp 削除後、shared sorry 補題呼出に置換)
      - `AWGNConverse.lean` は `awgn-mi-bridge-plan` 委任 1 sorry + `@residual(plan:awgn-mi-bridge-plan)`
- [ ] **V-3**: CLAUDE.md「Independent honesty audit」必須条件発動: 新規 `sorry` +
      `@residual(wall:<name>)` を 3-6 件導入 + 既存 declaration の signature 改変
      (predicate hyp 引数削除) → `honesty-auditor` subagent を fresh 起動
- [ ] **V-4**: auditor verdict 反映 (DEFECT 検出時は当該 declaration 撤回 + sorry-based
      書換、questionable は docstring refine、全 OK は session 完了)
- [ ] **V-5**: `docs/shannon/awgn-moonshot-plan.md` 進捗ブロック更新 + 判断ログ追記
      (本 plan の closure 実績、M5 9 declaration の Tier 3 → Tier 2 移行完了)
- [ ] **V-6**: `docs/textbook-roadmap.md` Ch.9 行 update
      (`continuous-aep` 系 wall の active sorry 件数増加、`awgn_*` wall の新規登録、
      `awgn_channel_coding_theorem` の publish 状態は変わらず "achievability sorry
      via `awgn_achievability`" を維持)

## 撤退ライン

- **L-AWGNM5-1-α** — `MarkovChainForConverse` の genuine 化が `awgnConverseJoint` 構造
  解析で詰まる (Phase 0-3 / Phase 3α-1)。
  **撤退**: Route B (shared sorry `awgn-converse-markov-regularity`) に降格、wall
  register 追加 1 件増、本 plan 完了時の wall 件数は 3 → 4 に増加。Tier 2 移行自体は
  完遂可能 (honest sorry を別 wall で抱えるだけ)。
- **L-AWGNM5-2-α** — `awgnPowerWitness_exists` (Phase 3β-6) の `∃ P' ∈ (0, P)` slack
  選択補題が `δ(R, P, N)` の閉形を要求し、Phase 内で構成不能。
  **撤退**: helper lemma 自身も `sorry` + `@residual(plan:awgn-m5-sorry-migration-plan)`
  で残置 (本 plan slug に集約)、後続 mini-plan で discharge。`isAwgnTypicalityHypothesis`
  body は 1 sorry + plan-slug 残置で全 Tier 2 達成。
- **L-AWGNM5-3-β** — Phase 3-α / 3-β の chain 内で **新規 honesty defect 発見**
  (例: 既存 `awgn_extract_AwgnCode` (line 856) が実は load-bearing predicate を内部で
  consume している、`isAwgnTypicalityHypothesis` body 580 行 assembly が shared sorry
  補題 3 件 + power witness で再構成不能)。
  **撤退**: CLAUDE.md「検証の誠実性」inline alert 発動 + 該当 declaration の上に build
  しない、本 plan を **段階完了** で closure (3-α のみ landing、3-β は別 plan に分割)、
  新規 defect 用に sub-plan filename `awgn-m5-achievability-followup-plan` を予約。
- **L-AWGNM5-4-γ** — Phase 1 wall name register PR が rejected (auditor が「`continuous-aep`
  既存 wall で十分」と判定、新規 wall name 増加を拒否)。
  **撤退**: 3 shared sorry 補題を 1 つの既存 wall (`continuous-aep`) に集約、各
  `@residual(wall:continuous-aep)` で 1 wall name に統一。これは降格ではなく
  consolidation (audit-tags.md 推奨)、本 plan 完了時の wall 件数は 3 → 1 (既存)。
- **L-AWGNM5-5-honest-defect** — Phase 0 verbatim 再確認で「実は 10 件中 N 件が
  consumer 0 の純粋削除候補 (`@audit:retract-candidate(load-bearing-predicate-empty-consumers)`
  の sister 34e17bc precedent)」と判明。
  **対処**: 純粋削除を Phase 3 に先行 sub-step 化 (Phase 3-0 として 1 commit で
  declaration 削除のみ)、shared sorry 補題化が不要になった declaration は本 plan の
  scope から外す (Tier 3 retract-candidate 維持で OK と判定)。

## scope-out (本 plan で扱わない)

- **EPI-Stam Cluster C 6 件** (`EPIL3Integration.lean` / `EPIStamDischarge.lean` /
  `EPIStamToBridge.lean` / `EntropyPowerInequality.lean`) — sister 34e17bc で同型 Tier 3
  化済、本 plan と同型の Path 1 plan は別 session で起草 (`epi-stam-cluster-c-sorry-migration-plan`
  仮名)。
- **AWGN family 残り 36 declaration** (`awgn-sorry-migration-plan.md` Round 4 Wave A
  対象) — Tier 4 → Tier 3 bookkeeping migration は完了済、Tier 3 → Tier 2 への昇格は
  本 plan の precedent を sweep 終了後に別 session で適用判定 (`@audit:closed-by-successor`
  系の signature 改変は scope 外維持)。
- **`ParallelGaussianPerCoord.lean`** — `IsParallelGaussianPerCoordRegularity` structure
  + 🟢ʰ 4 件、本 plan 同型の Path 1 migration は別 PR (escalate #6、`parallel-gaussian-l-pg1-discharge-plan`
  sibling)。
- **`AWGNMain.lean` / `awgn_channel_coding_theorem`** — F-1/F-3 peer migration
  (2026-05-27) で既に Tier 2 形 (predicate hyp 引数なし、body は genuine delegation
  または `sorry` + `@residual(plan:...)`)、本 plan の touch 不要。
- **Ch.17 frontier sweep plan (`chapter-17-frontier-sweep-plan.md`)** との同時 landing
  調整は本 plan で言及するが調整自体は別 session (orchestrator 管理)。Ch.17 が touch
  する `EntropyPowerInequality.lean` は本 plan の sister precedent file で、本 plan の
  完了が Ch.17 phase 4-5 の wall name register の参照対象になる可能性あり (片方向の
  依存、循環なし)。

## 報告フォーマット (本 plan を消費する implementer / orchestrator 向け)

本 plan の完了時、orchestrator は以下を確認:

1. `InformationTheory/Shannon/AwgnWalls.lean` が新設され、3-6 shared sorry 補題が
   `@residual(wall:<name>)` 付きで type-check done
2. `AWGNConverseDischarge.lean` / `AWGNConverse.lean` / `AWGNAchievabilityDischarge.lean`
   の 10 declaration から load-bearing predicate hyp が **完全除去** (= predicate
   削除 + consumer signature 書換)
3. `lake env lean` 全 touched file 0 errors
4. `honesty-auditor` verdict = 全 OK or questionable (DEFECT は L-AWGNM5-3-β 発動で
   段階完了 closure)
5. `docs/shannon/awgn-moonshot-plan.md` 進捗ブロック + 判断ログ更新済
6. `docs/audit/audit-tags.md` Wall name register に新規 wall 3 件 (L-AWGNM5-4-γ 発動時は
   1 件) 追加済

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **Phase 3 closure (2026-05-28、3 並列 orchestrator)**: Phase 3-α (converse) +
   Phase 3-β (achievability) を並列 dispatch + Ch.17 Minkowski を 3rd stream で同時実行。
   - **Phase 3-β achievability: 完全 proof done** — `AWGNAchievabilityDischarge.lean`
     0 sorry / 0 @residual。新 helper `awgnPowerWitness_exists` が strict `P' < P`
     witness を genuine 閉形 (`P_min := N·(exp(2R)−1)`、中点) で構成、L-AWGNM5-2-α 不発。
     honesty-auditor が `@audit:ok` stamp (strict slack の non-fabricate 検証 PASS)。
     bundle `IsAwgnRandomCodingFeasible` + 3 sub-bound predicate 削除、consumer 3 +
     glue `awgn_avg_error_union_bound` の signature から hyp 除去。
   - **Phase 3-α converse: L-AWGNM5-1-α 発火** — Markov を genuine 化できず Route B
     降格 (encoder 非単射時の condDistrib factorization に measure-theoretic 構成が必要)。
     `awgnConverseMarkov_holds` を AwgnWalls 4th wall として追加。converse wall 計 3
     (`awgn-per-letter-integrability` / `awgn-continuous-mi-chain-rule` /
     `awgn-converse-markov-regularity`)。`AWGNConverseDischarge.lean` の migration 由来
     sorry は 0 (残 1 件は pre-existing `wall:multivariate-mi`)、`AWGNConverse.lean` は
     `awgn-mi-bridge-plan` 委任 sorry 1 件。import cycle 回避に private mirror def
     `converseJointInline` (defeq、auditor genuine 評価)。
   - **Ch.17 Minkowski**: Stage A (`minkowskiDeterminantInequality` +
     `@residual(wall:minkowski-det-posdef)`) landing + genuine helper
     `det_rpow_le_arith_mean_eigenvalues` (AM-GM 半分、0 sorry)。同時対角化 congruence
     step が残壁。
   - honesty-auditor verdict: **全 OK / honest_residual、tier 5 defect 0**。
     4 新規 wall を audit-tags.md register に追記、stale `@audit:closed-by-successor`
     3 件を `@audit:ok` に incidental migration。

<!-- 例:
1. **Phase 0-3 で `MarkovChainForConverse` Route B 降格**: `IsMarkovChain` instance
   自動 derive が `awgnConverseJoint` 構造で不可と判明、L-AWGNM5-1-α 発動、新規 wall
   `awgn-converse-markov-regularity` を register に追加。
-->
