# AWGN Channel Capacity ムーンショット計画 🌙 (T2-A)

> **Status (2026-05-20)**: DONE-HONEST-HYPS。headline `awgn_channel_coding_theorem`
> (`AWGNMain.lean:59`) は F-1 (`IsAwgnTypicalityHypothesis`、`AWGNAchievability.lean:39`) +
> F-2 (MI bridge) + F-3 (`IsAwgnConverseHypothesis`、`AWGNConverse.lean:56`) を honest
> pass-through hyp で publish (0 sorry、非自明 Prop)。F-1 kernel measurability のみ
> `AWGNF1Discharge.lean:60` で完全 discharge 済。
>
> **注意**: `AWGNF2F3Discharge.lean` の `awgn_theorem_of_F2F3_hypotheses` は F-2/F-3 の
> 実 discharge **ではない** — alias (id-like reduction) + `IsAwgnF3PerLetterHypothesis`
> (line 229) は `:= ... True` placeholder。F-2/F-3 実体は未着手。
>
> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §T2-A /
> **Inventory**: [`awgn-mathlib-inventory.md`](awgn-mathlib-inventory.md)
>
> **Goal**: Cover-Thomas 9.1.1 + 9.1.2 (AWGN capacity `C = (1/2) log(1+P/N)`、closed form +
> achievability + converse) を hypothesis pass-through 形で publish。
> **撤退ライン**: F-1 (typicality) / F-2 (MI bridge) / F-3 (per-letter aux) — §撤退ライン。

## 進捗

- [x] Phase 0 — Mathlib + InformationTheory API 在庫 ✅ → [`awgn-mathlib-inventory.md`](awgn-mathlib-inventory.md)
- [x] Phase A — `awgnChannel` kernel + `AwgnCode` + `mutualInfo` closed-form bridge + `awgnCapacity` 定義 + 等号 ✅ (`AWGN.lean`, 275 行, F-2 + F-4 採用)
- [x] Phase B — Achievability (F-1 hypothesis pass-through 形) ✅ (`AWGNAchievability.lean`, 72 行)
- [x] Phase C — Converse (F-3 hypothesis pass-through 形) ✅ (`AWGNConverse.lean`, 94 行)
- [x] Phase D — 主定理 wrapper (`awgn_channel_coding_theorem`) ✅ (`AWGNMain.lean` 新規, 107 行) — 判断 #4 で `AWGN.lean` 末尾から `AWGNMain.lean` へ移動
- [x] Phase V — verify (4 ファイル `lake env lean` clean、0 sorry / 0 errors) ✅ (InformationTheory.lean 編入はオーケストレータが実施)

## ゴール / Approach

### Goal (最終定理 signature)

Code が SoT。`InformationTheory/Shannon/AWGNMain.lean` に `awgn_channel_coding_theorem` (3
hypothesis pass-through 形)、`AWGN.lean` に `awgnChannel` / `AwgnCode` / `awgnCapacity` /
`awgnCapacity_eq`、`AWGNAchievability.lean` / `AWGNConverse.lean` に主定理。

### Approach (overall strategy / shape of solution)

Cover-Thomas Ch.9 の AWGN 容量公式 = **(a) Gaussian 精密計算 (closed-form KL / conv /
entropy) + (b) discrete Shannon channel coding の continuous 化**。Mathlib 側で
Gaussian closed-form 100%、InformationTheory 側で `differentialEntropy_gaussianReal` +
`differentialEntropy_le_gaussian_of_variance_le` (4-hyp 形) が converse per-letter bound
そのまま使える。AWGN 専用 layer は本 plan 新規。

**4 ファイル分離** (実装中に `AWGNMain.lean` 追加へ拡張、判断ログ #2):

- `AWGN.lean` — `awgnChannel` + `AwgnCode` + `awgnCapacity` 定義 + 等号 (F-2 hyp 形)
- `AWGNAchievability.lean` — F-1 hyp pass-through achievability
- `AWGNConverse.lean` — F-3 hyp pass-through converse
- `AWGNMain.lean` — sandwich wrapper (循環依存回避のため新規分離)

**Mathlib-shape-driven 採用**: `awgnChannel x := gaussianReal x N` (textbook 形 PDF 直書きは
+50 行リスク回避)、`awgnCapacity := sSup` 直書き (`Fintype α` 想定の既存 `capacity W` 再利用不可)、
MI bridge `I = h(P+N) - h(N)` は F-2 hypothesis pass-through (Stein/Cramér/Chernoff と同型)。

### 段階的 ship + ファイル構成

- **Tier 0** (Phase A): 定義 + closed-form capacity。`InformationTheory.lean` 編入可
- **Tier 1** (+ B + C): achievability + converse hyp 形
- **Tier 2** (+ D): sandwich main theorem
- **Tier 3** (defer): F-1/F-2/F-3 discharge は別 plan (`awgn-*-plan.md` 3 本)

実績 4 ファイル: `AWGN.lean` (275) / `AWGNAchievability.lean` (72) /
`AWGNConverse.lean` (94) / `AWGNMain.lean` (107) = 548 行 (予測 1090-1850 行から 50% 縮小)。

## 依存関係

完了済 / 利用可 (inventory §A-§C SoT):

- **Mathlib Gaussian**: `gaussianReal_conv_gaussianReal`, `gaussianReal_add_gaussianReal_of_indepFun`,
  `variance_id_gaussianReal`, `rnDeriv_gaussianReal`, `instIsProbabilityMeasureGaussianReal`,
  `gaussianReal_map_add_const`, `isGaussian_gaussianReal`
- **Mathlib Kernel / Indep / Variance / Conv**: `Measure.compProd`, `IsMarkovKernel`,
  `IndepFun.map_add_eq_map_conv_map₀'`, `variance_eq_integral`, `Measure.conv`
- **InformationTheory Shannon**: `DifferentialEntropy.lean` (`differentialEntropy_gaussianReal`,
  `differentialEntropy_le_gaussian_of_variance_le` 4-hyp 形), `ChannelCoding.lean`
  (`Channel`/`Code`/`mutualInfoOfChannel`), `BlockwiseChannel.lean`, `MutualInfo.lean`,
  `CondMutualInfo.lean` + `MIChainRule.lean` (`condMutualInfo_chain_rule_X_2var`)
- **InformationTheory Fano**: `Fano/Measure.lean` `fano_inequality_measure_theoretic`
  (`X := Fin M`, `Y := Fin n → ℝ` で直接 reuse)

**参考のみ (Fintype 壁で reuse 不可)**: `ChannelCodingAchievability.lean` /
`ChannelCodingConverseGeneralComplete.lean` / `ChannelCodingShannonTheoremFullDischarge.lean`

---

## Phase 0 — Mathlib + InformationTheory API 在庫 ✅

完了 ([`awgn-mathlib-inventory.md`](awgn-mathlib-inventory.md), 643 行)。Gaussian 精密計算
100% Mathlib、continuous entropy + max-entropy は InformationTheory 既存、AWGN 専用 6 ピース
自作。撤退ライン F-1/F-2/F-3 + 判断 #1-#3 → 判断ログ #1-#3 / 確定済 #1-#5。

---

## Phase A-V — 実装 ✅

全 Phase 完了。code SoT (`AWGN.lean` / `AWGNAchievability.lean` / `AWGNConverse.lean` /
`AWGNMain.lean` の 4 ファイル、合計 548 行)。詳細 → 判断ログ #1-#5。

- **Phase A** (`AWGN.lean`, 275 行): `awgnChannel` + Markov inst + measurability (F-4 hyp
  pass-through、後続 `AWGNF1Discharge.lean` で完全 discharge) + `AwgnCode` (4 field) +
  `outputDistribution_gaussianInput` + F-2 hyp 形 closed form + `awgnCapacity_eq` sandwich
- **Phase B** (`AWGNAchievability.lean`, 72 行): F-1 `IsAwgnTypicalityHypothesis` pass-through
- **Phase C** (`AWGNConverse.lean`, 94 行): F-3 `IsAwgnConverseHypothesis` pass-through
  (Fano + chain rule per-letter + max-entropy)
- **Phase D** (`AWGNMain.lean`, 107 行 — 循環依存回避のため新規分離、判断 #2 改): sandwich

---

## 撤退ライン

全採用済 (slug は他 doc / code から参照されるので保持):

- **F-1** `IsAwgnTypicalityHypothesis` (Phase B): sphere packing / continuous AEP を hyp 外出し →
  別 plan `awgn-achievability-typicality-plan.md` に defer
- **F-2** `h_mi_bridge` (Phase A): `I = h(Y) - h(Y|X)` bridge を hyp 外出し → 別 plan
  `awgn-mi-bridge-plan.md` に defer (Mathlib-shape-driven レッドフラグ回避)
- **F-3** `IsAwgnConverseHypothesis` (Phase C): per-letter max-entropy `h_ent_int` を hyp
  外出し → 別 plan `awgn-converse-aux-plan.md` に defer
- **F-4** (実装中追加) `IsAwgnChannelMeasurable` (Phase A): `awgnChannel.measurable'` を
  hyp 外出し → 後続 plan `awgn-f1-discharge-moonshot-plan.md` で完全 discharge 済
  (`AWGNF1Discharge.lean:60` `isAwgnChannelMeasurable`)

自作 plumbing 肥大ライン **L-A1 / L-A2 / L-C1 / L-D1** は未発動 (4 撤退ライン全採用で 548 行
ship、予測 1000-1300 行を大幅下回り)。slug は将来参照のため保持。

---

## Risk table

実装完了済、全 risk は予測通り処理済 (F-1/F-2/F-3 hyp 化、F-4 後続 discharge、`AwgnCode`
新規 wrapper)。詳細は inventory §G 危険箇所トップ 5 + 判断ログ #1。

---

## オーケストレータ注記

完了済。後続 plan (F-1/F-2/F-3 discharge) では実装 agent は `InformationTheory.lean` 編集せず、
オーケストレータが最後にまとめて import 追加。

---

## 判断ログ

append-only。

### 後続 (2026-05-20)

6. **F-4 (kernel measurability) discharge 完了** → `awgn-f1-discharge-moonshot-plan.md` /
   `AWGNF1Discharge.lean` (148 行) で `Measurable (fun x => gaussianReal x N)` を
   `gaussianReal_map_const_add` + Giry monad + `measurable_measure_prodMk_left` で完全証明
   (`isAwgnChannelMeasurable`)。`awgn_theorem_F1_discharged` / `awgn_capacity_closed_form_F1_discharged`
   で h_meas 引数なし形再 publish。seed では「F-1 (kernel measurability)」と呼ぶ点に注意。

### 確定済 (2026-05-19, Phase A-D 一括実装)

1. **F-1 + F-2 + F-3 + F-4 全採用確定**: 実装中に **新規 F-4** 発見 (`gaussianReal` の
   `m`-measurability 直接 lemma が Mathlib 不在、loogle Found 0)。Tier 0 規模膨張回避のため
   `IsAwgnChannelMeasurable N` を hyp 外出し → 別 plan defer。
2. **3 → 4 ファイル拡張**: `awgn_channel_coding_theorem` sandwich を `AWGN.lean` 末尾に置くと
   `AWGN ↔ AWGNAchievability` 循環依存。**`AWGNMain.lean`** 新規分離 (107 行)。
3. **`AwgnCode` 4 field 確定**: encoder/decoder/decoder_meas/power_constraint。encoder
   measurability は `Fin M` finite で自動充足。
4. **規模 1090-1850 行予測 → 実績 548 行 (50% 縮小)**: 4 撤退ライン全採用で
   Achievability + Converse 本体が pass-through 1 行 proof に圧縮。Phase A の `awgnCapacity_eq`
   sandwich 周辺 (sSup `le_csSup`/`csSup_le`、variance bridge、MI 純算術) が実装の core。
5. **`mutualInfoOfChannel_gaussianInput_closed_form` 純算術 fill**: F-2 hyp で
   `I = h(P+N) - h(N)` まで来た上で `differentialEntropy_gaussianReal` 2 回引き →
   `(1/2) log((P+N)/N) = (1/2) log(1 + P/N)` (`AWGN.lean:119-170`、~40 行)。

---

## オーケストレータ向け Phase 着手順序サマリ

Phase A → B → C → D + V 順、4 ファイル全完了済 (実績 548 行、予測 1000-1500 行を大幅下回り)。
