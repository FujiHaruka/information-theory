# EPI Stam inequality — discharge plan

> **Status**: **38/39 ok (97%)** (commit `0fe2ad4`, 2026-05-25)。Phase A-V 完了。
> 残 1 件 `IsStamToEPIScalingHyp` (`EPIStamToBridge.lean:147`) は sister plan
> `epi-stam-to-conclusion-plan` 所管 (§残 1 件)。

## Position

- 親: [`epi-moonshot-plan.md`](./epi-moonshot-plan.md) — L-EPI1 hypothesis pass-through publish 済
- sister: [`epi-stam-to-conclusion-plan.md`](./epi-stam-to-conclusion-plan.md) /
  [`epi-debruijn-integration-plan.md`](./epi-debruijn-integration-plan.md)
- 上流 wall: [`fisher-info-moonshot-plan.md`](./fisher-info-moonshot-plan.md) (V2 Fisher info)
- inventory: `epi-stam-blachman-discharge-inventory.md` /
  `epi-stam-condexp-score-discharge-mathlib-inventory.md`

## Motivation / Scope

Stam inequality `1/J(X+Y) ≥ 1/J(X) + 1/J(Y)` の genuine discharge。V2 Fisher info 経路
(`FisherInfoV2.lean` 系 4 件、`@audit:suspect(fisher-info-moonshot-plan)`) を所与に、
Cauchy-Schwarz + λ-optimization + score convolution で構成。

担当 file (合計 39 件 suspect / 2184 LoC、起動時 closure target):

| file | suspect | LoC |
|---|---|---|
| `EPIStamDischarge.lean` (Stam discharge 主) | 15 | 686 |
| `EPIStamToBridge.lean` (scaling + bridge) | 14 | 663 |
| `EPIStamInequalityBody.lean` (Cauchy-Schwarz + AM-GM) | 5 | 479 |
| `EPIStamStep12Body.lean` (score convolution + CS) | 5 | 356 |

Mathlib 壁分類 (b) 解析 / Tier 3 / 既存補助補題 `stam_lambda_min` /
`stam_inverse_form_of_harmonic_mean` を再利用。

**Closure**: 39 件 `@audit:suspect(epi-stam-discharge-plan)` → `@audit:ok`、
`IsStamInequalityHypothesis` placeholder を genuine `IsStamInequalityHyp` で置換。連鎖
`epi-stam-to-conclusion-plan` 23 件。

## Approach (executed)

Cover-Thomas Lemma 17.7.2 を 4 段で構成 (V2 keyed `fisherInfoOfDensity`):

1. Blachman score-of-convolution identity: `s_{X+Y}(z) = E[s_X(X) | X+Y=z]`
2. Cauchy-Schwarz: `J(X+Y) ≤ λ² J(X) + (1-λ)² J(Y)` (`condVar_ae_le_condExp_sq`)
3. λ-optimization: `λ_min = J(Y)/(J(X)+J(Y))` 閉形 (`stam_lambda_min` 既存)
4. inverse 形: `1/J(X+Y) ≥ 1/J(X) + 1/J(Y)` (`stam_inverse_form_of_harmonic_mean`)

Mathlib base: `IndepFun.pdf_add_eq_lconvolution_pdf` (`Density.lean:356`) /
`condExp_ae_eq_integral_condDistrib_id` (`Kernel/CondDistrib.lean`) /
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`。

## Phase 完了サマリ ✅ (commit `0fe2ad4`, 2026-05-25)

| Phase | 結果 |
|---|---|
| A V1→V2 張替 | noop — Wave 2 以前移行済 / 対応 decl 再構成済 |
| B Blachman score-of-convolution | Tier 0/1 完了。`EPIStamStep12Body.lean` 5 件 ok (line 214/253/273/295/309) |
| C λ-opt + CS | `EPIStamInequalityBody.lean` 7 件 ok。`stam_lambda_min` 閉形で L-Stam-C-β 不要 |
| D inverse-Fisher harmonic | `EPIStamDischarge.lean` 15 + `EPIStamToBridge.lean` 13/14 件 ok |
| V verify + 編入 | 5 file `lake env lean` clean、`InformationTheory.lean` 編入済 |

残 1 件 `IsStamToEPIScalingHyp` は sister `epi-stam-to-conclusion-plan` Phase 0 所管 📋

---

## 残 1 件 — `IsStamToEPIScalingHyp` 📋

- **location**: `InformationTheory/Shannon/EPIStamToBridge.lean:147` (`@audit:suspect(epi-stam-to-conclusion-plan)`)
- **defect 種別**: launder 疑い — predicate body は `g1 = 0` 固定で実は EPI 結論と同等、
  Csiszár scaling-monotonicity content 不在 (命名と内容の乖離)
- **所管**: sister `epi-stam-to-conclusion-plan` Phase 0 (real `g1` 導入 or premise 分割)
- **本 plan 影響なし**: 本 plan 配下 decl は本 predicate を consumer として参照しない

---

## 撤退ライン総覧 (履歴参照、全 Phase 完了で発火なし)

| slug | Phase | 内容 | 発火 |
|---|---|---|---|
| L-Stam-A-α | A | V1↔V2 bridge 経由保持 | no (Phase A noop) |
| L-Stam-B-α | B | 畳み込み smooth witness 仮定 | no (honest hyp 整理で ok) |
| L-Stam-C-α | C | score L² integrability 仮定 | no |
| L-Stam-C-β | C | λ-opt IVT 仮定 | no (`stam_lambda_min` 閉形) |
| L-Stam-D-α | D | partial discharge (B-α/C-α 連鎖) | no |

共通規律: `:= True` placeholder / 循環 `:= h` / load-bearing name laundering 禁止
(CLAUDE.md 検証の誠実性)。

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-24 Wave 2 planner Phase 起草**: stub plan (66 行、Phase 設計未起草) に Phase
   A-V を埋め込み。inventory `epi-stam-blachman-discharge-inventory.md` Part 1A の V1 keyed
   primitive 5 件を Phase A で V2 張替対象として確定、Part 1C 依存グラフから `IsStamTotalExpectation`
   と `IsStamScoreConvolution` を Phase B / C の主 deliverable として確定。V2 Fisher info
   経路 (4 sub-predicate `@audit:suspect(fisher-info-moonshot-plan)` 状態) は本 plan の
   **前提として明記**、並行可。3 sub-plan 依存関係は §Position に既存記述で十分整合。

2. **2026-05-25 Wave 3 second batch 38/39 ok 達成 + sister plan re-route** (commit `0fe2ad4`):
   Phase A は noop 確認 (V1→V2 張替は Wave 2 以前に完了済 or 対応 declaration が再構成済)、
   Phase B Tier 0/1 を完了 (`EPIStamStep12Body.lean` 5 件 ok)、Phase C/D は Wave 2 以前完了
   分を再確認 (`EPIStamInequalityBody.lean` 7 件 + `EPIStamDischarge.lean` 15 件 +
   `EPIStamToBridge.lean` 13 件、合計 35 件 ok)。**38/39 (97%)**。残 1 件は
   `IsStamToEPIScalingHyp` (`EPIStamToBridge.lean:147`、`g1 = 0` 固定で実は EPI 同等の
   launder 疑い)、本 session 内で `@audit:suspect(epi-stam-to-conclusion-plan)` タグ付与
   + sister plan `epi-stam-to-conclusion-plan` Phase 0 に cleanup re-route。本 plan の
   閉鎖判定は **38/39 ok + 残 1 は所管外** で確定 (closed-by-successor 風扱い、bridge は
   sister 担当)。`EPIStamDischarge.lean:144/187` の `@audit:defect(false-statement)` +
   `@audit:suspect(epi-debruijn-integration-plan)` 2 件はそもそも本 plan 所管外 (de Bruijn
   integration sister)、counted カウントには入らない。
