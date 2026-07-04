# MAC: time-sharing converse half (CV + V) サブ計画

> **Parent**: [`mac-timesharing-plan.md`](mac-timesharing-plan.md) — 親の **CV**（converse half）+ **V**（full-region antisymmetry）を本サブ計画が担う。
> grandparent = [`mac-moonshot-plan.md`](mac-moonshot-plan.md) §撤退ライン **L-MAC5**（time-sharing 全凸包）。

**Status**: **CLOSED（L-MAC5 CV/V 完全 genuine closure、proof-done sorryAx-free）**。CV headline `mac_timesharing_converse` + V full-region headline `mac_timesharing_capacity_region`（`@[entry_point]`、intersection 形）ともに proof-done。両ファイル `TimeSharing.lean` / `TimeSharingConverse.lean` は **0 sorry / 0 @residual**。**L-MAC5 = Cover–Thomas Thm 15.3.1 の time-sharing 全凸包形が標準B（proof done）で完全達成**。再検証 → settled-facts。

frozen slug: 撤退口 `@residual(plan:mac-timesharing-converse-plan)` = 本ファイル stem 一致（同 slug 再帰、CLOSED ゆえ active 参照は code 側に 0 件）。

<!--
記法は moonshot-plan-template と同じ（状態絵文字 📋🚧✅🔄、取り消し線、append-only 判断ログ）。
Parent ヘッダは plan_lint の親子グラフ構築点。CLOSED 反映は親の CV/V 行 / DAG と同期済
（衝突時は子が SoT → CLAUDE.md「Plan / docs hygiene」親子整合）。プラン予算 ≤ 600 行 / active 判断ログ ≤ 10 entry。
-->

## 進捗

**全 gap / 全 dispatch 完了**（各 proof-done, sorryAx-free。状態はキャッシュせず `#print axioms <decl>` で都度再検証）:

- [x] Gap 0/A/B′/C — finite-n 材料（code→ambient bridge / Fano 付き rate extract / per-letter `condMI=macInfo` 同定 / 平均 pentagon→凸包）✅ commits `3377eba5`/`9c86884d`/`5a0419b0`/`302dbe03`、独立監査 PASS。
- [x] Dispatch B — CV-level 解析核（Fano `/n→0` 極限 + 点構成 uniform 乗法縮小 + interior tail）✅ `d920a15e`→`23f9db46`。CV interior + shrunk-point sorryAx-free。
- [x] Dispatch A — `hsub = mac_perletter_superadd`（無条件 `macInfoBoth ≤ macInfo₁+macInfo₂`、差分 = `I(X₁;X₂)+I(X₁;X₂|Y) ≥ 0`、既存 `macJoint_mutualInfo_X1_X2_eq_zero` 使用）✅ `315be033`。→ interior 全体 sorryAx-free。
- [x] **軸 casework** — `mac_timesharing_converse_axis1`/`_axis2`（single-user Fano corner `mac_converse_from_code_bound₁`/`_bound₂` を `hcard₁`/`hcard₂` のみ・M_other=1 で通す）✅ `c37333dc`、監査 PASS（all-OK 6/6）→ **CV headline `mac_timesharing_converse` proof-done sorryAx-free**。
- [x] Dispatch C — achievability full-support→all-prob upgrade `mac_achievability_region_allprob` + `mac_pentagon_subset_capacityRegion_allprob`（macMix smoothing + macInfo 連続性、gateway atom PASS = not-a-wall）✅ `2d45273c`。proof-done sorryAx-free。
- [x] Dispatch D — clamp-equivalence `mac_achievable_clamp_iff` + **V full-region headline `mac_timesharing_capacity_region`**（`@[entry_point]`、intersection 形 `macCapacityRegion W ∩ Q = closedConvexHull(all-prob pentagons)`）✅ `67283ec4`。proof-done sorryAx-free。

## ゴール / Approach（達成、記録）

**ファイル**: `InformationTheory/Shannon/MultipleAccess/TimeSharingConverse.lean`（`TimeSharing.lean` を import）。namespace `InformationTheory.Shannon.MAC`。

### 達成した headline signature（advisor 再精査で 3 軸訂正した最終形）

```lean
-- CV headline: converse half（(a) 0≤R guard、(b) union を IsProbabilityMeasure に限定）
theorem mac_timesharing_converse (W) [IsMarkovKernel W] :
    {p | MACAchievable W p.1 p.2 ∧ 0 ≤ p.1 ∧ 0 ≤ p.2}
      ⊆ closedConvexHull ℝ (⋃ (p₁) (p₂) (_ : IsProbabilityMeasure p₁)
          (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W)

-- V headline (@[entry_point]): full region = intersection 形（(c) ∩Q + hW threading）
theorem mac_timesharing_capacity_region (W) [IsMarkovKernel W]
    (hW : ∀ a b, 0 < (W a).real {b}) :
    macCapacityRegion W ∩ {p | 0 ≤ p.1 ∧ 0 ≤ p.2}
      = closedConvexHull ℝ (⋃ (p₁) (p₂) (_ : IsProbabilityMeasure p₁)
          (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W)
```

3 軸訂正の理由（settled、機械確認済）: (a) `MACAchievable`（`TimeSharing.lean:47`）は `⌈exp(n·R)⌉ ≤ M` が R<0 で `⌈exp(neg)⌉=1` vacuous ゆえ負 rate を含む down-set → `0≤p.1∧0≤p.2` guard 必須（旧 `{MACAchievable} ⊆ RHS` は反例 `(−1,−1)` で false）。(b) 非確率測度 `p` は `macInfo`（`macJointDistribution` entropy = 確率入力でのみ law）に junk → union は `IsProbabilityMeasure` scope（converse 出力 marginal は確率だが非 full-support）。(c) `macCapacityRegion = closure {MACAchievable}` は down-closure で負象限含む → **intersection 形 `∩Q`**（redefine 回避で blast radius 最小、`macCapacityRegion` consumer 0 本 touch）+ ⊇ 継承元 achievability の `hW` threading。

### Approach（達成した shape）

converse = 「達成 rate pair `(R₁,R₂)` は各時刻の周辺入力ペンタゴン点の**時間平均**として凸包に入る」を operational に構成。finite-n 材料（Gap 0/A/B′/C）→ CV-level 極限 + 点構成（Dispatch B）→ per-letter well-formedness `hsub`（Dispatch A、無条件 MI superadditivity ルート）→ 軸 casework（single-user Fano corner）で CV 完成。V は CV（⊆）+ achievability all-prob upgrade（Dispatch C、⊇）を clamp-equivalence（Dispatch D）で intersection 形 antisymmetry に組む。

### honesty（達成後も遵守された設計軸）

追加した `0≤R` / `IsProbabilityMeasure` / `hW` / `StandardBorelSpace` は全て honest な nonneg / regularity precondition（Proposal F、load-bearing bundle でない）。削除済 tier-5 scaffold `MACPerLetterChain₁₂`（「code ⟹ (`mac_converse` hyps ∧ pentagon 不等式)」の 1-hyp bundle）は再導入せず、各 obligation は genuine sub-lemma で貫通。独立 honesty 監査（軸 all-OK 6/6、Dispatch B/C/D）PASS。

---

## settled-facts（minimal、再導出可能なものは都度 `#print axioms` / `rg` / loogle）

- **L-MAC5 全体（CV + V）proof-done sorryAx-free**（confidence machine、再検証: `lake env lean InformationTheory/Shannon/MultipleAccess/TimeSharingConverse.lean` silent + `#print axioms mac_timesharing_capacity_region` = `[propext, Classical.choice, Quot.sound]`、commit `67283ec4`。両ファイル 0 sorry / 0 @residual）。
- **軸 corner は un-bundled `mac_converse_from_code_bound₁`/`_bound₂` が `hcard₁`/`hcard₂`（`2≤Mᵢ`）のみで通る**（confidence machine、commit `c37333dc`）。bundled wrapper `mac_converse` の「両ユーザ `2≤M`」要求が障害に見えたが、un-bundled 個別 bound は片側 card 前提だけで M_other=1 でも成立 → 軸 casework が genuine closure。
- **`MACAchievable`（`TimeSharing.lean:47`）は負 rate を含む down-set**（confidence machine、`⌈exp(n·R)⌉ ≤ M` が R<0 で `⌈exp(neg)⌉=1` vacuous）。→ CV の `0≤R` guard + V の `∩Q` の根拠。
- **`Real.continuous_negMulLog` は Mathlib 存在**（confidence machine、Dispatch C macInfo 連続性 gateway atom の building block、`InformationTheory/Fano/Measure.lean:333` 使用実績）→ full-support→all-prob upgrade は not-a-wall。

（これ以上のキャッシュはしない。`docs/shannon/mac-facts.md` は現時点で作らない。）

---

## 判断ログ

append-only。決着済 entry は削除（git が履歴）、active のみ残す。≤ 10 entry。CLOSED ゆえ active な判断は残さず、後続参照価値のある教訓 1 件のみ保持。

1. **軸 casework closure の教訓（settled、un-bundling が鍵）**: 軸点（`R₁=0` or `R₂=0`）は当初「route 未確立、single-user converse 要」と評価したが、bundled wrapper `mac_converse` の「両ユーザ `2≤M`」要求が障害に見えただけで、un-bundled 個別 bound `mac_converse_from_code_bound₁`/`_bound₂` は片側 `hcard`（`2≤Mᵢ`）のみで通り M_other=1 の corner を genuine に閉じた（commit `c37333dc`）。教訓 = 「bundle wrapper の合成前提が過大に見えるとき、un-bundled 部品の個別前提を確認する」。
