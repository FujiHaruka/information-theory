# EPI Stam → EPI conclusion — merge / conclusion plan

> **Status**: Phase 0 / 0-Plumbing 完了 (2026-05-25)、Phase A 待機中 (sister 両 Phase D 出力待ち)。
> **Created**: 2026-05-24 (Wave 1.5 item #8、`epi-moonshot-plan` 76 件 slug 分割)。

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
- [ ] Phase A — Stam + de Bruijn 合流 skeleton (sister 待ち、Phase 0 完了前提) 📋
- [ ] Phase B — Phase E corollary 各種 genuine 化 (Phase 0 完了前提) 📋
- [ ] Phase V — verify (`lake env lean ...`) + Common2026.lean 編入 📋

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

## Phase A — Stam + de Bruijn 合流 skeleton (sister 待ち) 📋

> Phase A は mini-plan `docs/shannon/epi-stam-to-conclusion-phaseA-plan.md` が SoT。
> ここは anchor 用サマリ。

### スコープ

sister Phase D 出力 (`epi-stam-discharge` + `epi-debruijn-integration`) を入力に、
`IsStamToEPIBridgeHyp` (`EPIStamDischarge.lean:337`) を genuine 化 + `IsEPIL3IntegratedPipeline`
(`EPIL3Integration.lean:105`) を construct → 主定理 `entropy_power_inequality`
(`EntropyPowerInequality.lean:232`) を hypothesis-free `theorem` 化。

### Done 条件

- `IsStamToEPIBridgeHyp` / `IsEPIL3IntegratedPipeline` genuine 化、主定理 hypothesis-free 化
- `EPIStamDeBruijnConclusion.lean` 6 件 + `EPIStamStep3Body.lean` 9 件 + 主定理含 1 件 `@audit:ok`
- **post-merge cleanup**: `EPIL3Integration.lean` 14 件 `@audit:suspect(epi-debruijn-integration-plan)`
  → `@audit:closed-by-successor(epi-stam-to-conclusion-plan)` 一括書換
  (位置 120/134/210/224/239/253/268/283/316/365/378/401/458/485)
- **Phase D 出力 contract**: `csiszarGap` 系 4 件 (`EPIL3Integration.lean` §13) を `g(t)` 定義に
  再利用、shape `rfl` 一致は `csiszarGap_shape_for_sister` が保証
- **退化境界注意**: `entropyPower (Measure.dirac 0) = 1` (Phase D で確認、判断ログ 4 参照)、
  `Y := 0` 退化は L-DBD-2-α 直撃に注意

### ステップ (~150-260 行)

- A-0: sister Phase D 完了確認
- A-1: `g(t)` 定義 + 基本性質 (~30-50)
- A-2: `g'(t) ≤ 0` (Stam + de Bruijn) (~50-80)
- A-3: `g(∞) = 0` Gaussian limit (~30-50)
- A-4: `g(0) ≤ 0` → EPI (~20-30)
- A-5: `IsStamToEPIBridgeHyp` genuine 化 (~20-30)
- A-6: 主定理 hypothesis-free 化 (~10-20)

### 撤退ライン

- **L-Concl-A-α** (許容): sister 撤退ライン (L-Stam-D-α / L-DB-D-α/β) 伝播 → "smooth density 限定"
  partial EPI、honest 命名 (`entropy_power_inequality_under_smooth_density` 等)
- **L-Concl-A-β** (許容): `g(∞) = 0` non-Gaussian 破綻 → Gaussian saturation limit hypothesis 追加

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

## Phase V — verify + Common2026.lean 編入 📋

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
