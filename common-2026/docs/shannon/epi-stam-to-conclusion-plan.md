# EPI Stam → EPI conclusion — merge / conclusion plan

> **Status**: Phase 0 / 0-Plumbing 完了 (2026-05-25)、Phase A skeleton 着地済だが
>   headline wall `stamToEPIBridge_holds` 未 discharge。**2026-06-01 re-assessment**:
>   両 sister (L-EPI1 Stam / L-EPI2 de Bruijn) は genuine sorryAx-free、残るは
>   assembly + 2 個の analytic atom (§re-assessment 参照)。
> **Created**: 2026-05-24 (Wave 1.5 item #8、`epi-moonshot-plan` 76 件 slug 分割)。

## 2026-06-01 re-assessment (genuine 基盤照合)

per-time de Bruijn が genuine sorryAx-free 化したのを受け、EPI frontier をコード verbatim 再照合。
すべて `lake env lean` + `#print axioms` で実測。

### 検証済 genuine 基盤 (sorryAx-free、`[propext, Classical.choice, Quot.sound]` のみ)

| 部品 | file:line | 状態 |
|---|---|---|
| **L-EPI2 per-time de Bruijn** `debruijnIdentityV2_holds_assembled` | `FisherInfoV2DeBruijnAssembly.lean:3513` | **genuine** (`#print axioms` 実測 sorryAx-free) |
| **L-EPI2 積分形** `debruijnIntegrationIdentity_holds` (genuine) | `FisherInfoV2DeBruijnGenuine.lean:83` | genuine (assembled + Mathlib FTC、0 local sorry) |
| **L-EPI1 Stam** `isStamInequalityHyp_via_body` | `EPIStamInequalityBody.lean:464` | **genuine** (`#print axioms` 実測 sorryAx-free) |
| **L-EPI1 壁** `stam_step2_density_wall` | `EPIStamInequalityBody.lean:349` | genuine (`convex_fisher_bound_of_ready` 経由、`@audit:ok`) |
| Stam 主 `EPIStamDischarge.lean` | 全体 | **0 real sorry** (L248/L476 は docstring 文字列) |
| `EPIStamDeBruijnConclusion.lean` | 全体 | **0 real sorry** |
| `EPIStamStep3Body.lean` | 全体 | **0 real sorry** |
| bridge body discharge `isStamToEPIBridgeHyp_of_scaling` | `EPIStamToBridge.lean:235` | genuine (`@audit:ok`、endpoint antitonicity + Gaussian saturation) |
| `csiszarGap1Source_differentiableOn_interior` (A-4-2) | `EPIStamToBridge.lean:788` | genuine |
| `csiszarGap1Source_antitoneOn_Ici_zero` (A-4-3) | `EPIStamToBridge.lean:820` | genuine assembly (A-2-3 + A-3 を `antitoneOn_of_deriv_nonpos` で繋ぐ、下流 sorry 依存のみ) |
| `csiszarGap_eq_one_source_via_rescale` / `csiszarGap_at_one_eq_zero_of_gaussian_pair` / `csiszarGap1Source_at_zero` | `EPIL3Integration.lean:1365/1154/1544` | genuine (`@audit:ok`) |
| `entropyPower_gaussian_additivity` (Gaussian saturation) | `EntropyPowerInequality.lean:331` | genuine |

### 何が unblock されたか

- **L-EPI2 (de Bruijn) は完全に genuine、かつ EPI チェーン下流に効いている**。
  `csiszarGap1Source_hasDerivAt` (`EPIStamToBridge.lean:474`) は `#print axioms` 実測で
  **sorryAx-free** (`[propext, Classical.choice, Quot.sound]`、2026-06-01 orchestrator 検証)。
  shim `debruijnIdentityV2_holds` は commit `7f6576b` で削除済、genuine
  `deBruijn_identity_v2` (`FisherInfoV2DeBruijnGenuine.lean:50`、`_assembled` 経由) が唯一の定義。
  （旧 drift 警告は解消済 — 下記参照。）
- **L-EPI1 (Stam) は完全に genuine**。`isStamInequalityHyp_via_body` が sorryAx-free。
- 合流 path の構造補題 (rescale / endpoint / differentiability / Gaussian saturation) はすべて
  genuine。残る wall は純粋に **2 個の analytic atom + 1 個の richness gap** に局所化された。

### 残る genuine な穴 (Phase A の真の closure target)

headline `stamToEPIBridge_holds` (`EntropyPowerInequality.lean:252`) は以下を transitive に消費する。
file:line + 性質を verbatim 列挙:

| # | sorry | file:line | 種別 | 障害 |
|---|---|---|---|---|
| **G1** | `csiszarGap1Source_deriv_le_zero` (A-3) | `EPIStamToBridge.lean:682` | ⚠ **FALSE-AS-FRAMED → 後継 plan に移管** | difference-gap `eP_sum·J_sum ≤ eP_X·J_X + eP_Y·J_Y` は plain Stam から従わない (反例: `N_sum` 巨大/`N_X,N_Y` 微小、orchestrator + proof-pivot-advisor 確認 2026-06-01)。**G1 は当初謳われた「最 tractable な純 algebra FIRST step」ではない** — as-stated は closure 不能。fix = log-ratio gap への再frame → **[`epi-csiszar-ratio-reframe-plan.md`](epi-csiszar-ratio-reframe-plan.md)** (ratio 形 `r=log N_sum−log(N_X+N_Y)` の monotonicity は genuine、純 algebra で閉じる)。D3 行は `@audit:defect(false-statement) @audit:closed-by-successor(epi-csiszar-ratio-reframe-plan)` 済 |
| **G2** | `csiszarGap1Source_continuousOn` (A-4-1) | `EPIStamToBridge.lean:783` | **真の Mathlib 壁 (寄り)** | `entropyPower ∘ P.map` の heat-flow path 上 `√t→0` 連続性。Lebesgue dominated convergence machinery が現 `IsDeBruijnRegularityHyp` bundle に無い。退避なら `@residual` 継続 |
| **G3** | `csiszarGap_antitoneOn_Icc_zero_one` (A-4-4 rescale) | `EPIStamToBridge.lean:897` | **assembly (per-`s` AC/integrability 引数の materialize)** | 1-source `AntitoneOn (Ici 0)` を 2-source `AntitoneOn (Icc 0 1)` に持ち上げ。`csiszarGap_eq_one_source_via_rescale` (genuine) が `s∈Ico 0 1` ごとに 6 個の AC + integrability hyp を要求、これを uniform に供給する組立 |
| **G4** | `IndepFun (X+Y) (Z_X+Z_Y)` joint independence | `EPIStamToBridge.lean:968` | **richness gap** | `IsStamScalingNoiseHyp` は pairwise indep のみ供給、4-tuple joint indep を供給しない。noise model 強化が closure |
| W1 | `stamToEPIScaling_holds` (shared sorry) | `EPIStamToBridge.lean:211` | assembly | G1-G4 を組んだ `isStamToEPIScalingHyp_of_stam_debruijn` を呼べば閉じる集約点 |
| W2 | `stamScalingNoise_exists` (shared sorry) | `EPIStamToBridge.lean:387` | richness | standard-normal pair の存在 (任意確率空間上の noise extension)。G4 と同根 |
| W0 | `stamToEPIBridge_holds` (**headline**) | `EntropyPowerInequality.lean:252` | assembly | `IsStamInequalityResidual → IsEPIHyp`。`isStamToEPIBridgeHyp_of_scaling ∘ stamToEPIScaling_holds` で閉じる集約点 (defeq bridging 要) |

**結論**: headline wall は 1 個の monolithic 壁ではなく、**構造補題チェーンの末端に残る
G1 (⚠ false-as-framed)・G2 (continuity, 真 Mathlib 壁)・G3 (rescale assembly)・G4/W2 (richness)** に分解。

> **⚠ G1 訂正 (2026-06-01)**: G1 (`csiszarGap1Source_deriv_le_zero`) は当初「純 in-house algebra の最
> tractable FIRST step」と謳ったが、**difference-gap 形が FALSE-AS-FRAMED** であることが判明
> (orchestrator + proof-pivot-advisor 独立確認)。plain Stam から `eP_sum·J_sum ≤ eP_X·J_X+eP_Y·J_Y`
> は従わず (`N_i` 無制約、反例構成済)、as-stated は closure 不能。**G1 を FIRST step として着手しては
> いけない**。genuine な後継 = log-ratio gap への再frame
> ([`epi-csiszar-ratio-reframe-plan.md`](epi-csiszar-ratio-reframe-plan.md))。そちらの R-3
> (`csiszarLogRatioGap_deriv_le_zero`、ratio 微分 `≤0`) が真の純 algebra FIRST tractable step。
> 残る tractable atom は G3 (rescale assembly)・G2 (continuity 壁) で、これらは ratio 再frame と
> 並行/後続で進められる。

### drift 警告 → **解消済 (2026-06-01, commit `7f6576b`)**

> この警告は本 re-assessment 起草時 (implementer の cycle-break commit と concurrent) の stale read に
> 由来する誤検知だった。実際には commit `7f6576b` で shim は削除され、`deBruijn_identity_v2` は
> genuine 版 1 定義のみ、Genuine は `InformationTheory.lean:143` に編入済。名前衝突は存在しない。
> orchestrator が `#print axioms` で `csiszarGap1Source_hasDerivAt` /
> `isDeBruijnIntegrationHyp_holds` の両方が sorryAx-free であることを実測確認。
> **M0-1 (de Bruijn genuine wiring 解消) は完了** — G1/G2/G3 はこの前提なしに直接着手してよい。

(履歴) 旧警告: `csiszarGap1Source_hasDerivAt` が shim 版 `deBruijn_identity_v2` を拾い、Genuine が
`InformationTheory.lean` 未編入と報告されていたが、いずれも commit 前の concurrent 状態の read であり、
最終状態では成立しない。

## Position

- 親: [`epi-moonshot-plan.md`](./epi-moonshot-plan.md) (L-EPI3 hypothesis pass-through)
- Sister (上流): [`epi-stam-discharge-plan.md`](./epi-stam-discharge-plan.md) (L-EPI1) /
  [`epi-debruijn-integration-plan.md`](./epi-debruijn-integration-plan.md) (L-EPI2)
- 関連: [`fisher-info-moonshot-plan.md`](./fisher-info-moonshot-plan.md)

## Motivation

Stam (L-EPI1) + de Bruijn (L-EPI2) → EPI conclusion 合流部 + Phase E corollary 群 (multi-arg /
monotonicity / scaling / log-form) の genuine 化。L-EPI3 = `IsEntropyPowerInequalityHypothesis`
pass-through (`EntropyPowerInequality.lean:168` 真 Prop、`:= h_epi` 着地 `:188`) を hypothesis-free
化することが最終目標。

Phase A は sister 両方の Phase D 出力待ち。Phase 0 / Phase 0-Plumbing / Phase B 一部 (reshape) は
独立着手可 (詳細 → 判断ログ 1-2)。

## Scope

担当 file 群 (合計 23 件 suspect / 1507 LoC):

| file | suspect | LoC |
|---|---:|---:|
| `EPIStamStep3Body.lean` (Lagrange / λ 最適化) | 9 | 391 |
| `EPIStamDeBruijnConclusion.lean` (合流) | 6 | 377 |
| `EntropyPowerInequality.lean` (主定理 + Phase E corollary) | 5 | 420 |
| `EPIPlumbing.lean` (normalized / 4-arg / log-form) | 3 | 319 |

増分予想 ~260-430 行 (中央 ~350)。Tier 3 (long-term)、EPIPlumbing 3 件は先行 close 可。

## Closure criteria

- 主定理 `entropy_power_inequality` を L-EPI3 hypothesis なしの genuine theorem 化、
  `IsEntropyPowerInequalityHypothesis` を `theorem` 格上げ
- 23 件 `@audit:suspect(epi-stam-to-conclusion-plan)` → `@audit:ok`
- EPI エコシステム全 76 件 close (sister 39 + 14 + 本 23)

## Approach

**EPI 結論** (Cover-Thomas 17.7.3、n=1): `exp(2 h(X+Y)) ≥ exp(2 h(X)) + exp(2 h(Y))`

合流 path (Csiszár scaling argument):
```
Stam: 1/J(X+Y) ≥ 1/J(X) + 1/J(Y)        ←── sister: epi-stam-discharge Phase D
de Bruijn integ: h_target - h_X = ∫ J dt ←── sister: epi-debruijn-integration Phase D
        ↓ Csiszár scaling (heat-flow path)
g(t) := EP(X+Y+√t·Z) − EP(X+√t·Z) − EP(Y+√t·Z)
g'(t) ≤ 0 (Stam + de Bruijn) ∧ g(∞) = 0 (Gaussian limit) ⇒ g(0) ≤ 0 ⇒ EPI
```

**Mathlib-shape 鍵**: `entropyPower μ := Real.exp (2 · differentialEntropy μ)`
(`EntropyPowerInequality.lean:80`) → `Real.exp_pos` / `Real.exp_log` / `Real.exp_add` /
`Real.exp_le_exp` 結論形に直結。Gaussian saturation `:226` を Phase B で再利用。

**Phase 依存**: 0 (独立) → 0-Plumbing (独立) → A (sister 待ち) → B (A 依存) → V

---

## 進捗

- [x] Phase 0 — `IsStamToEPIScalingHyp` defect cleanup (prerequisite, sister/A/B 全 block) ✅ 2026-05-25 (commits `0d54e89` / `78cf2ec` / `2809168`)
- [x] Phase 0-Plumbing — `EPIPlumbing.lean` 3 件先行 close (high ROI、独立着手可) ✅ 2026-05-25 (prior commit `f150cdc` + `5f923e4`)
- [x] Phase A skeleton — A-1〜A-6 構造補題着地 (合流 path の骨格) ✅ 2026-05-27 (`epi-stam-to-conclusion-phaseA-plan.md`)
- [ ] Phase A-close — 残 G1〜G4 atom discharge + headline wall closure 🔄 (2026-06-01 re-assess で skeleton 化) → 下記 §Phase A-close
- [ ] Phase B — Phase E corollary 各種 genuine 化 (Phase A-close 完了前提) 📋
- [ ] Phase V — verify (`lake env lean ...`) + InformationTheory.lean 編入 📋

proof-log: yes (各 Phase 完了時に `docs/shannon/proof-log-epi-stam-to-conclusion-phase-*.md`)

---

## Phase 0 — `IsStamToEPIScalingHyp` defect cleanup ✅

完了 (2026-05-25、commits `0d54e89` / `78cf2ec` / `2809168`)。Wave 3 second batch (`0fe2ad4`) で
発見された `EPIStamToBridge.lean:147-154` launder defect (`g1 = 0` 固定で EPI 結論に reduce する
cosmetic wrap) を **案 1 (genuine Csiszár scaling 化、`∃ Z_X Z_Y, ... ∧ AntitoneOn gap`)** で解消。
詳細 → 判断ログ entry 3-4。撤退ライン L-Concl-0Sc-α/β/γ は全非該当。Independent honesty audit PASS。

撤退ライン (履歴):
- **L-Concl-0Sc-α** (非該当): 案 1 規模超過時 → 案 2 (cosmetic alias rename) 退避
- **L-Concl-0Sc-β** (非該当): heat-flow Mathlib 壁時 → hypothesis 化 + `@audit:residual`
- **L-Concl-0Sc-γ** (非該当): defect 発見時の停止 + honest-auditor 起動

---



## Phase 0-Plumbing — EPIPlumbing 3 件先行 close ✅

完了 (2026-05-25、prior commits `f150cdc` / `5f923e4`)。EPIPlumbing.lean 3 件 (`:181` normalized /
`:212` four-arg / `:249` log-form) は L-EPI3 hypothesis pass-through reshape、`@audit:suspect` →
`@audit:staged` 書換完了 (Phase A 完了時 `@audit:ok` 降格予定)。撤退ライン L-Concl-0-α 非該当。

---

## Phase A skeleton — Stam + de Bruijn 合流 (着地済) ✅

> mini-plan `docs/shannon/epi-stam-to-conclusion-phaseA-plan.md` が SoT。A-1〜A-6 の構造補題は
> 2026-05-27 に着地済。残った穴は §re-assessment の G1〜G4 / W0〜W2。closure は次節 Phase A-close。

合流 path の骨格 (`csiszarGap1Source` 定義 / derivative / antitone lift / bridge body discharge /
Gaussian saturation endpoint) はすべて genuine に着地。残るは末端 atom の discharge のみ。

---

## Phase A-close — 残 atom discharge + headline wall closure 🔄

> **目標**: headline `stamToEPIBridge_holds` (`EntropyPowerInequality.lean:252`) を sorryAx-free 化。
> §re-assessment の G1〜G4 / W0〜W2 を closure。

### Approach (全体の shape)

合流の structural backbone (path 微分 → `antitoneOn_of_deriv_nonpos` → rescale → endpoint
Gaussian saturation → bridge body discharge) は **すでに genuine に組まれている**。残るのは
4 個の局所 atom (G1〜G4) を埋め、それらを集約点 (W2→W1→W0) で繋ぐだけ。新しい math 構造の設計は不要 —
**fill + assembly**。Mathlib-shape 整合は既存物が保証済 (各補題の結論 form は consumer slot と
verbatim 一致するよう Phase A で設計済)。よって closure は以下の依存順で進む:

```
M0 (de Bruijn genuine wiring) ✅済 ─────────┐
G1 ⚠ FALSE-AS-FRAMED → ratio 再frame plan ──┤  (R-3 ratio deriv ≤0 が genuine 後継)
   epi-csiszar-ratio-reframe-plan           ├──→ A-4-3 (genuine, 既存) ──→ G3 rescale ──→ W2/G4 richness ──→ W1 scaling_holds ──→ W0 headline
G2 continuity (Mathlib 壁寄り)  ────────────┘
```

> **⚠ G1 訂正 (2026-06-01)**: G1 (difference-gap `deriv ≤ 0`) は FALSE-AS-FRAMED (closure 不能)。
> genuine な純 algebra FIRST step は後継 [`epi-csiszar-ratio-reframe-plan.md`](epi-csiszar-ratio-reframe-plan.md)
> の R-3 (log-ratio `r'≤0`)。G2 は唯一の真 Mathlib 壁候補で退避時 `@residual(wall:...)` 継続
> (closure を ratio 再frame / G3 / G4 と分離可能)。

### M0 — 在庫調査 + de Bruijn genuine wiring 解消 (前提工程)

proof-log: no (調査のみ)

1. **drift 解消 — ✅ 完了 (2026-06-01, commit `7f6576b`)**: shim 削除 + Genuine を
   `InformationTheory.lean:143` 編入済、`csiszarGap1Source_hasDerivAt` は `#print axioms` 実測で
   sorryAx-free。M0-1 は no-op (前提充足済)。G1/G2/G3 に直接着手してよい。
2. **G1 Mathlib 在庫**: `nlinarith` / `div_le_div_iff` / `Real.exp_le_exp` / harmonic-mean ↔ 重み付き形の
   変形補題を loogle で照合 (`docs/shannon/epi-stam-to-conclusion-phaseA-plan.md` Brief A §4 既出)。
3. **G2 Mathlib 在庫**: `entropyPower ∘ P.map` の heat-flow 連続性に使える DCT 系
   (`MeasureTheory.continuous_integral_of_dominated` 等) の有無を loogle で確認 → 不在なら真 wall 確定。

### ~~G1 — `csiszarGap1Source_deriv_le_zero` (純 algebra FIRST step)~~ ⚠ FALSE-AS-FRAMED → 後継 plan に移管 🔄

proof-log: yes (後継 plan 側で記録)

**位置**: `EPIStamToBridge.lean:682` (signature は `@audit:defect(false-statement)` 形のまま残置、
body `sorry`、`@audit:closed-by-successor(epi-csiszar-ratio-reframe-plan)`)。

**⚠ 訂正 (2026-06-01)**: 当初この G1 を「最 tractable な純 algebra FIRST step」と謳ったが、
**結論 (difference-gap `eP_sum·J_sum ≤ eP_X·J_X + eP_Y·J_Y`) が plain Stam から従わない =
FALSE-AS-FRAMED** であることが判明 (orchestrator + 独立 proof-pivot-advisor)。

- 障害の本質: chain rule は genuine (`d/dt N_i = N_i·J_i`) だが、差分微分
  `g'(t) = N_sum·J_sum − N_X·J_X − N_Y·J_Y ≤ 0` は plain harmonic Stam `1/J_sum ≥ 1/J_X+1/J_Y` から
  **従わない**。`N_i` が `h_stam` に対し無制約なため反例構成可能 (`N_sum` 巨大 / `N_X,N_Y` 微小で
  全 hyp 成立・結論破綻)。当初の closure 手順 step 3 (Cover-Thomas eq.(17.43) weighting) は
  difference 形では存在しない不等式を仮定していた。
- 旧 `audit:PASS 2026-05-27` は **false negative**: 非循環 + 非bundling は verify したが
  **sufficiency (hyp ⊢ concl) は未検証**だった。
- **正しい fix = log-ratio gap への再frame**。`r(t)=log N_sum − log(N_X+N_Y)` の monotonicity
  `r'(t)=J_sum − (N_X·J_X+N_Y·J_Y)/(N_X+N_Y) ≤ 0` は重み `α=N_X/(N_X+N_Y)` の weighted Stam
  で genuine に閉じる (`α²≤α` を使う純 algebra、Mathlib 壁なし)。EPI 復元も equivalent
  (`r(0)≥0 ⟺ EPI`、`r(1)=0` Gaussian saturation)。

**移管先**: [`epi-csiszar-ratio-reframe-plan.md`](epi-csiszar-ratio-reframe-plan.md)。
その Phase R-3 (`csiszarLogRatioGap_deriv_le_zero`) が genuine な純 algebra FIRST tractable step。
**この G1 を直接埋めようとしてはいけない** — as-stated は closure 不能。後継 plan の R-5 で D3
(本 lemma) は削除予定。

### G3 — `csiszarGap_antitoneOn_Icc_zero_one` (rescale assembly) 📋

proof-log: yes

**位置**: `EPIStamToBridge.lean:897` (signature stable、body `sorry`)。

`csiszarGap_eq_one_source_via_rescale` (genuine) は `s∈Ico 0 1` ごとに 6 個の AC + integrability
hyp を要求。closure はこれらを uniform に供給する組立 (signature に `∀ s ∈ Ico 0 1, …` 形で precondition
追加するか、`IsDeBruijnPathRegular` 系から導出)。`s=1` endpoint は既存 genuine
`csiszarGap_at_one_eq_zero_of_gaussian_pair` (`EPIL3Integration.lean:1154`) で接続。
**撤退**: precondition materialize が file scope を膨らませる場合 `sorry` + `@residual` 継続。

### G2 — `csiszarGap1Source_continuousOn` (真 Mathlib 壁候補) 📋

proof-log: yes (壁判定込み)

**位置**: `EPIStamToBridge.lean:783`。`entropyPower ∘ P.map` の `√t→0` 連続性が現
`IsDeBruijnRegularityHyp` bundle で carry されない。M0-3 で DCT 系 Mathlib API を照合し:
- **在庫あり** → assembly で closure
- **不在** → `@residual(wall:...)` 化 (新 wall name register 追加候補、`docs/audit/audit-tags.md`
  「Wall name register」に loogle 0 件確認後追記)。closure を G1/G3/G4 から分離。

### G4 / W2 — richness gap (`IndepFun (X+Y) (Z_X+Z_Y)` + `stamScalingNoise_exists`) 📋

proof-log: yes

**位置**: `EPIStamToBridge.lean:968` (G4) + `:387` (W2)。`IsStamScalingNoiseHyp` が pairwise indep のみ
供給 → 4-tuple joint indep が不足。closure = noise model を 4-tuple joint independence 供給形に強化
(任意確率空間上の standard-normal pair extension、Mathlib `ProbabilityTheory` の product space 構成)。
**撤退**: noise extension が Mathlib 不在なら richness を honest precondition として signature に残す
(load-bearing でない regularity)。

### W0 / W1 — 集約点 closure (assembly のみ) 📋

proof-log: no (G1〜G4 完了後の機械的接続)

- **W1** `stamToEPIScaling_holds` (`:211`): G1〜G4 を組んだ `isStamToEPIScalingHyp_of_stam_debruijn`
  (`:912`、genuine assembly) を呼ぶだけで閉じる。
- **W0** `stamToEPIBridge_holds` (`EntropyPowerInequality.lean:252`、**headline**): `IsStamToEPIBridge`
  = `IsStamInequalityResidual → IsEntropyPowerInequalityHypothesis`。`isStamToEPIBridgeHyp_of_scaling`
  (genuine `@audit:ok`) ∘ `stamToEPIScaling_holds` で閉じる。`IsStamInequalityResidual` ↔ `IsStamInequalityHyp`
  の defeq bridging (`fisherInfoOfMeasureV2_def`) を unfold で discharge。

### Done 条件 (Phase A-close)

- headline `stamToEPIBridge_holds` (`EntropyPowerInequality.lean:252`) が `#print axioms` sorryAx-free
  (G2 が真 wall で残る場合は `@residual(wall:...)` 1 件のみ残す部分達成も可、honest 命名)
- 主定理 `entropy_power_inequality` (`:287`) + exp/log form が transitive sorryAx-free
- 新規 `sorry` + `@residual` を導入したら **独立 honesty-auditor 起動** (CLAUDE.md 必須)

### 撤退ライン (Phase A-close)

- **L-Concl-A-α** (許容): sister 由来 regularity precondition 伝播 → smooth density 限定 partial EPI、
  honest 命名 (`entropy_power_inequality_under_smooth_density` 等)
- **L-Concl-A-β** (許容): G3 rescale `s=1` endpoint 接続失敗 → Gaussian saturation limit を
  honest precondition 化
- **L-Concl-A-ζ** (G1、確率 15%): Cauchy-Schwarz weight が `nlinarith` 不可 → `sorry` 継続
- **L-Concl-A-θ** (G2): heat-flow 連続性 DCT 不在 → `@residual(wall:...)` 化、closure 分離
- **L-Concl-A-richness** (G4/W2): noise extension Mathlib 不在 → richness を honest precondition 化

**共通禁止** (CLAUDE.md 検証の誠実性): `Prop := True` / `:= h` 循環 / load-bearing `*Hypothesis` bundle /
退化定義悪用 (`Y:=0` / `Z_Y:=0` trivial AntitoneOn)。撤退時 docstring に「NOT a discharge」明示。

---

## Phase B — Phase E corollary 各種 genuine 化 📋

Phase A 完了で主定理が hypothesis-free になった後、corollary を主定理から reshape で genuine 化。
内訳: EntropyPowerInequality 5 件 (multi-arg / scaling / monotonicity / normalized / log-form)、
EPIStamStep3Body 9 件 (Lagrange、Phase A `g'(t) ≤ 0` で使用)、EPIStamDeBruijnConclusion 5 件
(合流系)、EPIPlumbing 3 件 (`@audit:staged` → `@audit:ok` 降格)。合計 23 件 `@audit:ok`。

ステップ: B-1 EPIPlumbing 3 件降格 (~10-15) / B-2 EPI Phase E corollary 5 件 (~80-120) /
B-3 Lagrange 9 件 (~30-50) / B-4 合流系 5 件 (~30-50)。

撤退ライン:
- **L-Concl-B-α** (許容): Phase A-α 伝播時 corollary も partial 化 (`@audit:staged` 留め)、
  honest 命名で明示

---

## Phase V — verify + InformationTheory.lean 編入 📋

4 file (`EPIPlumbing` / `EntropyPowerInequality` / `EPIStamStep3Body` / `EPIStamDeBruijnConclusion`)
silent `lake env lean` clean、23 件 `@audit:ok` 降格完了、`docs/textbook-roadmap.md` Ch.17 EPI を
`[x]` に、`epi-moonshot-plan.md` の split-into 注記更新 (EPI 76 件全 close)。

---

## 撤退ライン共通規律

全 slug 一覧は per-Phase に記述 (Phase 0 / A / B 各節)。共通禁止事項:
`Prop := True` placeholder / 結論型≡仮説型 `:= h` 循環 / load-bearing hypothesis を完成と称する
name laundering (`*_discharged` / `*_full` / `*_unconditional` 等)。撤退ライン発動時は docstring で
「NOT a discharge / load-bearing on <sister 由来 hypothesis>」を必ず明示。詳細 → CLAUDE.md
「検証の誠実性」+ `docs/audit/audit-tags.md`。

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 仮定修正時。append-only。

1. **2026-05-24 Wave 2 起草**: stub plan (75 行) に Phase 0 / A / B / V 埋込。EPIPlumbing 3 件は
   L-EPI3 hypothesis pass-through reshape で sister 待ち不要、Phase 0 先行 close 候補に確定
   (Phase 0 単独では `@audit:staged` 昇格、Phase A 完了で `@audit:ok` 降格)。
2. **2026-05-24 sister 依存**: Phase A は sister 両 Phase D 待ち。Phase 0 / B 一部独立。sister 撤退
   ライン (L-Stam-D-α / L-DB-D-α/β) は L-Concl-A-α として伝播。
3. **2026-05-25 Phase 0 新規追加 (scaling defect)**: Wave 3 second batch (`0fe2ad4`) で
   `IsStamToEPIScalingHyp` (`EPIStamToBridge.lean:147-154`) の launder defect 発見 (`g1 = 0` 固定で
   EPI 結論に reduce する cosmetic wrap)。prerequisite Phase 0 として追加、既存 EPIPlumbing 3 件は
   Phase 0-Plumbing にリネーム。推奨案 1 (genuine Csiszár scaling、~300-500 行)、stop-gap 案 2
   (cosmetic alias rename、~30 行)。consumer ripple ~20 件。L-Concl-0Sc-α/β/γ 新設。
4. **2026-05-25 Phase 0 closure (案 1 完遂)**: orchestrator 4 stage 並列実行で完了 (commits
   `0d54e89` / `78cf2ec` / `2809168`)。
   - Stage 1: heat-flow inventory + Phase 0-Plumbing 確認 (prior `f150cdc`/`5f923e4` 実質完了済)
   - Stage 2 (`0d54e89`): `HeatFlowPath.lean` 新規 6 lemma 132 行、`gaussianConvolution` 2-source 拡張
   - Stage 2-bis (`78cf2ec`): signature → `∃ Z_X Z_Y, ... ∧ AntitoneOn gap (Set.Icc 0 1)` refactor
     (+252/-163)、6 件 retract + 6 件 body rewrite。**`AntitoneOn`** が正符号 (inventory §G(b) の
     `MonotoneOn` 推奨は sign error)。retract 6 件: `isStamToEPIScalingHyp_of_{gaussian,epi,
     fisherInfoReal_zero}` / `isEPIScalingDecomposedPipeline_of_{epi,gaussian}` /
     `entropy_power_inequality_gaussian_via_scaling_decomposition`
   - Stage 4 (`2809168`): Independent honesty audit PASS、Tier 3 で `staged(plan-slug)` →
     `suspect(plan-slug)` refine。`IsStamToEPILimitHyp` launder は scaling refactor を打ち消さず
     (Phase 0' は LOW priority 後日)。
   - 規模実績 ~580 行 (見積中央 ~350 の +66%)、撤退ライン発動 0 件
   - 次段: Phase A は sister 両 Phase D 出力待ち
5. **2026-05-25 Phase A line drift 修正**: 親 plan の line 番号 2 件 drift を mini-plan 起草時に発見。
   `IsStamToEPIBridgeHyp` は `EPIStamDischarge.lean:304` ではなく **`:337`**、主定理 `entropy_power_inequality`
   は `EntropyPowerInequality.lean:188` ではなく **`:232`**。mini-plan
   `docs/shannon/epi-stam-to-conclusion-phaseA-plan.md` が SoT として正しい line を扱う。原因: append が
   line 番号未更新で drift。今後 line 番号は作業前に `rg -n` verbatim 照合 (CLAUDE.md 数値 verbatim の
   line 番号版)。

6. **2026-06-01 re-assessment (genuine 基盤照合 + Phase A-close skeleton 化)**: per-time de Bruijn の
   genuine sorryAx-free 化 (`debruijnIdentityV2_holds_assembled`、commit `5636db4` 系) を受けて EPI
   frontier をコード verbatim 再照合 (`lake env lean` + `#print axioms` 実測)。判明事項:
   - **L-EPI1 Stam** (`isStamInequalityHyp_via_body`) + **L-EPI2 de Bruijn** (`_assembled`) は
     **両方 genuine sorryAx-free**。Stam 主 file 群 (`EPIStamDischarge` / `EPIStamDeBruijnConclusion` /
     `EPIStamStep3Body`) は real sorry 0 件 (旧 plan が "23 件 suspect" 等と書いていたのは sorry-based
     migration 前の数字、現状とは drift)。
   - headline `stamToEPIBridge_holds` は **1 個の monolithic 壁ではなく**、genuine 構造補題チェーンの
     末端に残る G1 (algebra) / G2 (continuity, 真 Mathlib 壁候補) / G3 (rescale assembly) /
     G4+W2 (richness) に分解済。最有力 FIRST step は **G1 `csiszarGap1Source_deriv_le_zero`**
     (`EPIStamToBridge.lean:727`、純 in-house algebra、Mathlib 壁なし)。
   - ~~**drift 警告 (要解消)**~~ → **誤検知だった、解消済** (commit `7f6576b`): 起草が implementer の
     cycle-break commit と concurrent だったため stale read で「shim/genuine 2 定義共存・Genuine 未 import」
     と報告したが、最終状態では shim は削除され genuine 1 定義のみ・Genuine は `InformationTheory.lean:143` 編入済。
     orchestrator が `csiszarGap1Source_hasDerivAt` / `isDeBruijnIntegrationHyp_holds` の sorryAx-free を
     `#print axioms` 実測。M0-1 は no-op。
   - Phase 構成変更: 旧 "Phase A (sister 待ち)" → "Phase A skeleton ✅ (着地済)" + "Phase A-close
     (G1〜G4 + W0〜W2 closure)" に再構成。旧 Phase A の `g(t)` 抽象ステップ (A-1〜A-6) は既に
     `csiszarGap1Source` 系として着地済なので、Phase A-close は fill + assembly に焦点。
