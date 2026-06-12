# AWGN Channel Capacity ムーンショット計画 🌙 (T2-A)

> **Status (2026-06-12)**: **AWGN family 実 sorry 全閉鎖 — headline 含め genuine closure**。
> converse 経路 `awgn_converse` (`AWGN/Converse.lean`) は **完全 transitively genuine closed**
> (converse の 3 Mathlib 壁 mi-bridge / multivariate-mi / continuous-mi-chain-rule はすべて
> false-wall overturn で genuine closure 済)。**achievability 側の 3 shared sorry 補題
> (`AWGN/Walls.lean`) も全 deep atom 閉鎖で genuine** (`isAwgnTypicalityHypothesis` / 主要 wrapper まで
> genuine、[`awgn-achievability-walls-discharge-plan.md`](awgn-achievability-walls-discharge-plan.md)
> CLOSED、計 6 件の false-statement を honest 化)。**両 line の機械検証状態 (sorryAx 依存 +
> 再検証コマンド) は [`awgn-facts.md`](awgn-facts.md) 達成テーブルが SoT** (prose にキャッシュしない)。
> 残る AWGN 壁は kernel-measurability gap (`IsParallelGaussianKernelMeasurable`、X-input route 真の
> Mathlib gap、W-input で回避) のみ。
>
> headline `awgn_achievability` の最終 wiring も **閉鎖済** (import 反転 wiring、`c44be72`、
> 独立 honesty 監査 all OK `cb1af3c`): `AchievabilityDischarge` の上流 import 3 本を除去して
> `Achievability` が Discharge を import する向きに反転、body = `isAwgnTypicalityHypothesis`
> 直呼び。`awgn_channel_coding_theorem` (`AWGN/Main.lean`) も transitively sorryAx-free。
>
> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §T2-A /
> **Inventory**: [`awgn-mathlib-inventory.md`](awgn-mathlib-inventory.md) /
> **Facts ledger**: [`awgn-facts.md`](awgn-facts.md)
>
> **Goal**: Cover-Thomas 9.1.1 + 9.1.2 (AWGN capacity `C = (1/2) log(1+P/N)`、closed form +
> achievability + converse) を genuine publish。
> **残作業**: kernel-measurability gap のみ (X-input route 真の Mathlib gap、W-input で回避済、
> code `@residual` が SoT)。実 sorry は family 内 0。

## 進捗

- [x] Phase 0 — Mathlib + InformationTheory API 在庫 ✅ → [`awgn-mathlib-inventory.md`](awgn-mathlib-inventory.md)
- [x] Phase A — `awgnChannel` kernel + `AwgnCode` + `mutualInfo` closed-form bridge + `awgnCapacity` 定義 + 等号 ✅
- [x] Phase B — Achievability ✅ (`AWGN/Achievability.lean`) — headline `awgn_achievability` **discharge 済** (import 反転 wiring `c44be72`、旧 F-1 park の `sorry + @residual` 解消)。achievability 側 3 shared 壁の genuine discharge + statement-fix は → [`awgn-achievability-walls-discharge-plan.md`](awgn-achievability-walls-discharge-plan.md) ✅ **CLOSED** (全 deep atom 閉鎖、解析核 genuine、計 6 件 false-statement honest 化。機械検証状態 → [`awgn-facts.md`](awgn-facts.md))
- [x] Phase C — **Converse genuine closed** ✅ (`AWGN/Converse.lean`、`awgn_converse` transitively genuine)。converse 3 Mathlib 壁すべて false-wall overturn で genuine closure (mi-bridge / multivariate-mi / continuous-mi-chain-rule)。詳細 + 機械検証状態 → [`awgn-facts.md`](awgn-facts.md)
- [x] Phase D — 主定理 wrapper (`awgn_channel_coding_theorem`) ✅ (`AWGN/Main.lean`)
- [x] Phase V — verify ✅

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

- **F-1** `IsAwgnTypicalityHypothesis` (Phase B): sphere packing / continuous AEP。**閉鎖済** —
  `awgn_achievability` body の F-1 park は import 反転 wiring (`c44be72`) で discharge、
  `@residual(plan:awgn-achievability-typicality-plan)` 解消。achievability 側 3 shared 壁 (`AWGN/Walls.lean`)
  の genuine discharge + statement-fix は
  → [`awgn-achievability-walls-discharge-plan.md`](awgn-achievability-walls-discharge-plan.md) **CLOSED**:
  全 deep atom 閉鎖で 3 shared 補題 + union-bound lemma + consumer (`isAwgnTypicalityHypothesis`)
  まで genuine。計 6 件の false-statement (Wall1 (ii)/(iii) / D2 term2 #5 / degenerate corner #6)
  を honest 化 (詳細 + 機械検証状態 → [`awgn-facts.md`](awgn-facts.md))
- **F-2** `h_mi_bridge` (Phase A converse 側): per-letter MI bridge `I = h(Y) - h(Z)`。
  **closed (genuine、`awgn-mi-bridge-plan`)** — `awgn_per_letter_mi_bridge_genuine`
- **F-3** `IsAwgnConverseHypothesis` (Phase C): converse 全体 (Fano + DPI + chain + per-letter)。
  **closed (genuine、`awgn-converse-aux-plan`)** — converse 3 壁すべて closed、`awgn_converse` genuine
  (機械検証状態 → [`awgn-facts.md`](awgn-facts.md))
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
   `m`-measurability 直接 lemma が Mathlib 不在、loogle で再確認 — loogle-neg 状態は
   [`awgn-facts.md`](awgn-facts.md) 残存壁テーブルが SoT)。Tier 0 規模膨張回避のため
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
