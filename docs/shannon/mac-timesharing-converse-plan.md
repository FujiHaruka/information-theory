# MAC: time-sharing converse half (CV + V) サブ計画

> **Parent**: [`mac-timesharing-plan.md`](mac-timesharing-plan.md) — 親の **CV**（converse half）+ **V**（full-region antisymmetry）を本サブ計画が担う。
> grandparent = [`mac-moonshot-plan.md`](mac-moonshot-plan.md) §撤退ライン **L-MAC5**（time-sharing 全凸包）。

**Status**: 🚧 4 gap（Gap 0/A/B′/C）**全て proof-done, sorryAx-free**（commits 下記）。残 = CV/V の assemble + advisor 再精査で判明した **6 obligation**（下記）。いずれも genuine Mathlib 壁ではない = **plan correction / Mathlib-shape-driven statement realignment**（CLAUDE.md）であって撤退ではない。唯一の壁候補 macInfo 連続性も building block `Real.continuous_negMulLog` を Mathlib に確認済（gateway-atom-first）。

frozen slug: 撤退口 `@residual(plan:mac-timesharing-converse-plan)` = 本ファイル stem 一致（同 slug 再帰）。

<!--
記法は moonshot-plan-template と同じ（状態絵文字 📋🚧✅🔄、取り消し線、append-only 判断ログ）。
Parent ヘッダは plan_lint の親子グラフ構築点。子の状態を変えたら親の CV/V 行 / 進捗も同期する
（衝突時は子が SoT → CLAUDE.md「Plan / docs hygiene」親子整合）。
プラン予算 ≤ 600 行 / active 判断ログ ≤ 10 entry。
-->

## 進捗

**4 gap 完了**（各 proof-done, sorryAx-free。`#print axioms <decl>` で都度再検証、prose にキャッシュしない）:

- [x] Gap 0 — code→ambient bridge（`macConverseAmbient` 構成 + `mac_converse` の全 hyp discharge、`mac_converse_from_code` end-to-end）✅ commit `3377eba5`、独立監査 PASS。
- [x] Gap C 🎯 — `mac_avgPentagon_mem_convexHull`（平均 pentagon → convexHull、down-closedness は `convexHull_mem_of_le` で genuine、壁でなかった）✅ commit `302dbe03`。**`hbc` 追加**（判断ログ #4）。
- [x] Gap A — finite-n rate extract `mac_converse_rate_extract`（`TimeSharingConverse.lean:863`、`InMACCapacityRegion (n·R₁)(n·R₂)` の Fano 付き 3-bound）+ `le_log_of_ceil_exp_le`（:850）+ ambient errorProb reconciliation 3 本（:912/:947/:963、~25 LOC で機械化、予測「50-100/壁」は悲観的だった）✅ commit `9c86884d`。**注**: **軸 casework は未実装で意図的に deferred** — finite-n の Gap A でなく CV-level（下記 Dispatch B）に属す。
- [x] Gap B′ — per-letter 同定 `mac_condMI_eq_macInfo₁_at`/`_macInfo₂_at`/`mac_mutualInfo_eq_macInfoBoth_at`（:1171/:1197/:1223）+ helper `macConverse_map_triple_eq`（:1118）+ 自作汎用合成 3 本 `mutualInfo_map_comp`/`condDistrib_map_comp`/`condMutualInfo_map_comp`（:1033/:1046/:1063）✅ commit `5a0419b0`。**plan-vs-reality**: 計画が挙げた `condMutualInfo_map_left/middle_measurableEquiv` は **適用不可**（測度を固定するため）→ implementer が full-joint-pushforward 合成補題を自作（"reindexing plumbing"、genuine 貫通、sorry なし）。bridge precondition `[IsProbabilityMeasure p₁ᵢ]` は内部 discharge、deliverable に追加 hyp なし。

**残 = CV/V assemble（6 obligation、Dispatch B→A→C→D で攻略）**:

- [ ] Dispatch B — CV-level 解析核（Fano `/n → 0` 極限 + 点構成 uniform 乗法縮小 + interior tail + 軸 casework）📋 **← 次**
- [ ] Dispatch A — `hsub`（MI superadditivity）+ CV assemble（+ Gap C set-reindexing plumbing）📋
- [ ] Dispatch C — achievability full-support→all-probability upgrade（独立、gateway-atom-first）📋
- [ ] Dispatch D — clamp-equivalence 補題 + V antisymmetry（intersection 形）📋

## ゴール / Approach

### Goal（最終定理 signature、**advisor 再精査で 3 軸訂正済**）

**ファイル**: `InformationTheory/Shannon/MultipleAccess/TimeSharingConverse.lean`（`TimeSharing.lean` を import）。namespace `InformationTheory.Shannon.MAC`。

```lean
-- CV headline: converse half（訂正: (a) 0≤R guard 追加、(b) union を IsProbabilityMeasure に限定）
theorem mac_timesharing_converse (W) [IsMarkovKernel W] :
    {p | MACAchievable W p.1 p.2 ∧ 0 ≤ p.1 ∧ 0 ≤ p.2}
      ⊆ closedConvexHull ℝ (⋃ (p₁) (p₂) (_ : IsProbabilityMeasure p₁)
          (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W)

-- V headline (@[entry_point]): full region = intersection 形（訂正: (c) ∩Q + hW threading）
theorem mac_timesharing_capacity_region (W) [IsMarkovKernel W]
    (hW : ∀ a b, 0 < (W a).real {b}) :
    macCapacityRegion W ∩ {p | 0 ≤ p.1 ∧ 0 ≤ p.2}
      = closedConvexHull ℝ (⋃ (p₁) (p₂) (_ : IsProbabilityMeasure p₁)
          (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W)
```

**旧 signature が false だった理由**（advisor 3 concern、機械確認済 → 判断ログ #2/#3）:

- **旧 CV `{p | MACAchievable W p.1 p.2} ⊆ RHS` は false**: `MACAchievable`（`TimeSharing.lean:47`）は `⌈exp(n·R)⌉ ≤ M` を条件とし **R<0 で `⌈exp(neg)⌉=1` が vacuous** → 負 rate も達成集合に入る down-set。一方 `macPentagon`/hull ⊆ 第一象限 `Q`。反例 `(−1,−1) ∈ {MACAchievable} \ RHS`。→ **`0 ≤ p.1 ∧ 0 ≤ p.2` guard 必須**。
- **union scope を `IsProbabilityMeasure` に限定**（無制限 `⋃ p₁ p₂` でない）: 非確率測度 `p` は `macInfo`（`macJointDistribution` の entropy = 確率入力でのみ law）に junk を流す。converse が露出する per-letter marginal `μ.map(encoder)` は確率だが **full-support でない** → all-prob union が正しい scope（full-support union より広く、converse 出力を包含）。
- **旧 V `macCapacityRegion = RHS` は false**: `macCapacityRegion = closure {MACAchievable}`（`:64`）は down-closure で **負象限を含む**。RHS ⊆ Q ゆえ等号不成立。→ **`∩ {0≤p.1 ∧ 0≤p.2}` の intersection 形**（advisor 推奨 = **blast radius 最小**: `macCapacityRegion` consumer 0 本を touch せず、redefine 案の `TimeSharing.lean` 4 decl 改変を回避。orchestrator 未検算なら `scripts/dep_consumers.sh InformationTheory.Shannon.MAC.macCapacityRegion` で確認）。
- **`hW` 明示追加**: V の ⊇ 方向は achievability `mac_achievability_region`（`TimeSharing.lean:887`）から継承するが、同 headline は `hW : ∀ a b, 0 < (W a).real {b}`（full-support channel）を要求。旧 V signature はこれを落としていた。

### Approach（overall strategy / shape of solution）

converse = 「達成 rate pair `(R₁,R₂)` は各時刻の周辺入力ペンタゴン点の**時間平均**として凸包に入る」を operational に組む。4 gap（Gap 0/A/B′/C）で **finite-n の材料は全て genuine に揃った**:

- Gap 0 が code→ambient を供給、Gap A が finite-n の Fano 付き rate bound、Gap B′ が per-letter `condMI = macInfo` 同定、Gap C が「平均 pentagon 点 ∈ convexHull（raw Fin n union）」。

残る CV/V assemble は **6 obligation に分解**（いずれも壁でなく plumbing / 解析 / statement 整合）:

1. **CV-level 極限 + 点構成**（Dispatch B）: finite-n rate bound の Fano 項 `/n → 0`（`ε'→0, n→∞`）+ 達成点 `(R₁,R₂)` を hull 内に落とす **uniform 乗法縮小 + interior tail** の点構成 + **軸 casework**。Gap A で deferred した軸分岐はここ（CV-level）に属す。
2. **`hsub` per-letter well-formedness**（Dispatch A）: Gap C の `mac_avgPentagon_mem_convexHull`（`TimeSharingConverse.lean:104`）は `hsub : ∀ i, c i ≤ a i + b i` を要求。CV instantiate 時 `c=macInfoBothᵢ, a=macInfo₁ᵢ, b=macInfo₂ᵢ` で `macInfoBoth ≤ macInfo₁ + macInfo₂`（**MI superadditivity** `I(X₁;Y)+I(X₂;Y) ≤ I(X₁X₂;Y)` under input independence）。既存の `hac/hbc`（`mac_macInfo₁/₂_le_macInfoBoth` `:241/:270`）とは **categorically 別物**（非負項落しでない、下記判断ログ #4）。
3. **CV assemble + Gap C set-reindexing**（Dispatch A）: Gap C の出力は raw `⋃ i:Fin n, {p | 0≤·∧·≤a i∧·≤b i∧·+·≤c i}`（**macPentagon でなく Fin n 上の生 union**）。各 per-letter 生集合 = `macPentagon (μ.map X₁ᵢ)(μ.map X₂ᵢ) W` の集合等式 + measure-indexed headline union への `⋃`-reindex が要る（Gap B′ は corner の **値**を与えるが、集合等式 + reindex は別 plumbing）。
4. **achievability full-support→all-prob upgrade**（Dispatch C、独立）: CV が non-full-support marginal を露出するため、V の ⊇ 側（achievability）は **all-prob union** を cover せねば V を閉じられない（`mac_achievability_region` は現状 full-support union のみ、`:890-891` の `0 < p.real {a}` witness）。
5. **clamp-equivalence + V antisymmetry**（Dispatch D）: V ⊆ 方向に `MACAchievable W R₁ R₂ ↔ MACAchievable W (max R₁ 0)(max R₂ 0)`（`MACAchievable` は `R` に `⌈exp(n·R)⌉` 経由でしか依存せず `R↦max R 0` 不変）+ intersection 形 antisymmetry。

計 ~475-800 LOC。**攻略順は下記「攻略順」**（B→A→C→D）。

### critical（honesty、判断ログ #1 で ACTIVE）

**「code ⟹ (`mac_converse` hyps ∧ pentagon 不等式)」を 1 hyp に bundle するのは禁止** = 削除済 tier-5 scaffold `MACPerLetterChain₁₂`（`mac-inventory.md:136`）の再導入。6 obligation は各々 genuine sub-lemma か（詰まれば）**per-obligation sorry**。**追加した `0≤R` / `IsProbabilityMeasure` / `hW` は honest な nonneg / regularity precondition（Proposal F）で load-bearing bundle でない** — Fano 項 / per-letter chain / rate 不等式を hyp に encode しない。

### 型クラス設定 / Proposal F（正則性追加、honest precondition）

converse file の `variable` ブロック: `[StandardBorelSpace α₁] [StandardBorelSpace α₂] [StandardBorelSpace β]`（`mac_converse` の disintegration/condDistrib が要求、Fintype から導けるが宣言必須）+ `[IsMarkovKernel W]`。いずれも precondition（load-bearing でない）。

---

## Phase 詳細（攻略順 B→A→C→D）

### Dispatch B — CV-level 解析核（Fano→0 極限 + 点構成 + 軸 casework）
**proof-log**: yes（極限論証 + 点構成 trap + 軸 casework、解析の重心、再開根拠必須）

**最初に dispatch**（自己完結の解析 bulk、CV を unblock）。~120-200 LOC。

- [ ] **Fano→0 極限**: `MACAchievable W R₁ R₂`（`∀ε'∃N∀n≥N∃code`）+ Gap 0 ambient + Gap A finite-n bound（`mac_converse_rate_extract`）から、Fano 項 `binEntropy(errorProb) + errorProb·log(M₁−1)` を `/n` して `→ 0`（`errorProb < ε'`）、`log Mᵢ ≥ n·Rᵢ`（`⌈exp(n·Rᵢ)⌉ ≤ Mᵢ` = `le_log_of_ceil_exp_le` 既存 `:850`）で `Rᵢ ≤ liminf (1/n)∑ᵢ`（per-letter 平均）を抽出。
- [ ] **点構成（TRAP 注意、下記）**: 達成点 `(R₁,R₂)` を hull 内へ落とす。**独立座標 `max 0 ·` clamp は禁止**（Gap C の sum 制約 `hs` を破る、反例: coord-shrink `x₁=−1,x₂=5`, `(∑c)/n=4`: `x₁+x₂=4≤4` だが `max0 x₁+max0 x₂=5>4`）。正解 = **uniform 乗法縮小** `(R₁(1−Pe)−log2/n, R₂(1−Pe)−log2/n)` + **interior tail**（`R₁,R₂>0`, large k で `Pe→0`, `log2/n→0` ⇒ 最終的に `≥0` かつ `→(R₁,R₂)`、`convexHull ⊆ closedConvexHull` に着地）。
- [ ] **軸 casework**（`R₁=0` or `R₂=0`）: `mac_converse` の `hcard = 2≤M` 適用域外。achievability `mac_axis1/2` + mono を mirror。**Gap A で deferred した軸分岐の実体はここ（CV-level、finite-n でない）**。
- **撤退ライン**: `liminf` 抽出 / interior tail / 軸のどれかで詰まったら **その sub-lemma のみ** `sorry` + `@residual(plan:mac-timesharing-converse-plan)`。「達成 → rate 不等式」を 1 hyp で受けない（under-hypothesized bundle 禁止）。

---

### Dispatch A — `hsub`（MI superadditivity）+ CV assemble
**proof-log**: yes（`hsub` は MI superadditivity で hac/hbc と別物、再開根拠必須）

Dispatch B の後。~40-80（`hsub`）+ ~60-100（assemble）LOC。

- [ ] **`hsub` per-letter well-formedness** `macInfoBoth p₁ p₂ W ≤ macInfo₁ p₁ p₂ W + macInfo₂ p₁ p₂ W`。
  - **hac/hbc とは categorically harder**（判断ログ #4）: hac/hbc は「非負項を落とす」だが hsub は **MI superadditivity** `I(X₁;Y)+I(X₂;Y) ≤ I(X₁X₂;Y)` under input independence。「同 bridge ⇒ 軽い」heuristic は **転用不可**。
  - **advisor 提案の再利用**（implementer が verbatim 検証）: `mutualInfo_superadditive_of_indep`（`InformationTheory/Shannon/RateDistortion/ConverseNLetter.lean:532`、`@audit:ok`、n-fold `∑I(Xᵢ;X̂ᵢ) ≤ I(Xⁿ;X̂ⁿ)` under `iIndepFun`）を **n=2 で instantiate**、OR direct chain-rule + cond-entropy subadditivity。
  - **唯一の genuine sub-obligation**: 入力独立 `X₁⊥X₂` under `macJointDistribution p₁ p₂ W`（product-input 構成で true）。
- [ ] **CV assemble** `mac_timesharing_converse`（上記 Goal signature）: Dispatch B の rate 不等式 → Gap 0 ambient → Gap B′ per-letter 点 → hac/hbc（既存 `:241/:270`）+ hsub（上）→ Gap C（`mac_avgPentagon_mem_convexHull`）→ `convexHull ⊆ closedConvexHull`。
- [ ] **Gap C set-reindexing plumbing**（CV brief で明示）: Gap C 出力の raw `⋃ i:Fin n, {p | 0≤p.1∧0≤p.2∧p.1≤a i∧p.2≤b i∧p.1+p.2≤c i}`（**macPentagon でなく Fin n 生 union**）について、各 per-letter 生集合 = `macPentagon (μ.map X₁ᵢ)(μ.map X₂ᵢ) W` の集合等式 + measure-indexed union への `⋃`-reindex。Gap B′ は corner の **値**、集合等式 + reindex は別。
- **撤退ライン**: `hsub` の入力独立で詰まったら **その 1 本のみ** sorry + `@residual`。assemble は各 gap の sorry を推移継承（独自 sorry 新設しない）。

---

### Dispatch C — achievability full-support→all-probability upgrade（独立）
**proof-log**: yes（gateway-atom-first、macInfo 連続性の壁候補、再開根拠必須）

**A/B に依存せず任意時点で slot 可**（achievability 側のみ touch）。~100-200 LOC。

- [ ] **必要性（REQUIRED, unavoidable）**: CV は non-full-support marginal を露出するため、V を閉じるには achievability ⊇ 側が **all-prob union** を cover せねばならない。現状 `mac_achievability_region`（`TimeSharing.lean:887`）は **full-support union のみ**（`:890-891` に `0 < p₁.real {a}` / `0 < p₂.real {a}` witness）。
- [ ] **gateway atom（最初に dispatch-check）**: `Continuous (fun p₁ ↦ macInfo₁ p₁ p₂ W)`（有限 simplex 上）。**NOT a wall**: `macInfo` = `macJointDistribution` mass の `Real.negMulLog` の有限和、`Real.continuous_negMulLog` は Mathlib 存在（advisor 確認済、`InformationTheory/Fano/Measure.lean:333` で使用実績）、境界 `0 log 0 = 0` は `Real.negMulLog_zero`。
- [ ] **route**: `closedConvexHull(full-support pentagons) = closedConvexHull(all-prob pentagons)`（full-support 測度の density + macInfo 連続性）、OR `(1−ε)p + ε·unif` perturbation。
- **撤退ライン**: gateway atom が 3+ turn stall なら **その 1 本のみ** sorry + `@residual`、壁判定は反証義務（loogle 0-hit → conclusion-shape 再検索 → template 自作行数見積り）。壁昇格は後続 PR 判断。

---

### Dispatch D — clamp-equivalence + V antisymmetry（intersection 形）
**proof-log**: no（clamp 補題 + antisymmetry plumbing）

A/B/C の後（V が全入力を要する）。~15-25（clamp）+ ~40-80（antisymmetry）LOC。

- [ ] **clamp-equivalence 補題** `MACAchievable W R₁ R₂ ↔ MACAchievable W (max R₁ 0)(max R₂ 0)`: `MACAchievable` は `R` に `⌈exp(n·R)⌉` 経由でしか依存せず、`R↦max R 0` で `⌈exp(n·R)⌉` 不変（R<0 でも R=0 でも `⌈exp(≤0)⌉` の下限は同じ vacuous、R≥0 は恒等）。V ⊆ 方向で負 rate を第一象限に折り返す。~15-25 LOC。
- [ ] `mac_timesharing_capacity_region`（`@[entry_point]`、intersection 形、上記 Goal）= `Set.Subset.antisymm`:
  - **⊆**: `macCapacityRegion W ∩ Q` → clamp-equivalence で第一象限化 → CV（`mac_timesharing_converse`）。
  - **⊇**: RHS = `closedConvexHull(all-prob pentagons)` → Dispatch C の upgrade で `⊆ macCapacityRegion W`、かつ RHS ⊆ Q（`macPentagon ⊆ Q`, Q closed convex）ゆえ `⊆ macCapacityRegion W ∩ Q`。`hW` を achievability から threading。
- [ ] `lake env lean InformationTheory/Shannon/MultipleAccess/TimeSharingConverse.lean` silent（type-check done）。
- [ ] proof done: `#print axioms mac_timesharing_converse` / `mac_timesharing_capacity_region` = `[propext, Classical.choice, Quot.sound]`。
- [ ] 新規 `sorry`+`@residual` 導入 commit があれば **独立 honesty 監査**（`honesty-auditor`）を session 内起動（orchestrator-mandatory）。特に Dispatch B の rate 抽出 / `hsub` 入力独立が load-bearing bundle でないことを検査対象に明示。
- [ ] `InformationTheory.lean` に import 追加（orchestrator が最後に）。
- [ ] **親 co-stage**: 親 `mac-timesharing-plan.md` の CV/V 進捗行 + DAG を本 sub-plan 完了状態に同期。

---

## 攻略順 / 推奨 leg 数

**B → A → C → D**（同時 1 体まで、CLAUDE.md「Max one parallel agent」）:

1. **Dispatch B**（Fano→0 極限 + 点構成 + 軸 casework、解析核、~120-200 LOC）— 自己完結の解析 bulk、CV を unblock。
2. **Dispatch A**（`hsub` MI superadditivity + CV assemble + Gap C set-reindexing、~100-180 LOC）— B の出力後の plumbing。
3. **Dispatch C**（achievability upgrade、~100-200 LOC）— A/B 非依存で独立、gateway-atom-first、任意時点で slot 可。
4. **Dispatch D**（clamp-equivalence + V antisymmetry、~55-105 LOC）— A/C の入力後の最終 plumbing。

Rationale（advisor）: B は自己完結の解析 bulk、C は achievability 側のみ touch（A/B 非依存）、A/D は入力後の plumbing。**推奨 3-4 leg**。

---

## 撤退ライン / honesty（最重要）

- 撤退口は **`sorry` + `@residual(plan:mac-timesharing-converse-plan)` のみ**（CLAUDE.md「検証の誠実性」、同 slug 再帰）。6 obligation は独立 sub-lemma で、**詰まった obligation の当該 sub-lemma のみ** sorry。他は genuine 維持。
- **honesty trap ACTIVE**: 「code ⟹ (`mac_converse` hyps ∧ pentagon 不等式)」を **1 hyp に bundle 禁止** = 削除済 tier-5 `MACPerLetterChain₁₂`（`mac-inventory.md:136`）の再導入禁止。per-letter chain / rate 不等式 / Fano bound を受ける load-bearing `*Hypothesis` predicate は禁止。
- **§2-§5 の signature 訂正は plan correction / Mathlib-shape-driven realignment であって撤退ではない**: 6 obligation いずれも genuine Mathlib 壁でない。追加した `0≤R` / `IsProbabilityMeasure` / `hW` は honest nonneg / regularity precondition（Proposal F、load-bearing でない）。
- **唯一の壁候補 = Dispatch C の macInfo 連続性**（gateway atom `Continuous (fun p₁ ↦ macInfo₁ p₁ p₂ W)`）だが building block `Real.continuous_negMulLog` は Mathlib 存在 → gateway-atom-first で最初に dispatch-check。壁判定は反証義務（loogle 0-hit → conclusion-shape 再検索 → template 自作行数）。

---

## settled-facts（minimal、再導出可能なものは都度 `rg` / `#print axioms` / loogle）

- **4 gap（Gap 0/A/B′/C）は proof-done sorryAx-free**（confidence machine、再検証: `lake env lean InformationTheory/Shannon/MultipleAccess/TimeSharingConverse.lean` silent + `#print axioms mac_converse_from_code` / `mac_converse_rate_extract` / `mac_condMI_eq_macInfo₁_at` / `mac_avgPentagon_mem_convexHull`、commits `3377eba5`/`9c86884d`/`5a0419b0`/`302dbe03`）。prose には commit + 再検証 command のみ、状態はキャッシュしない。
- **`MACAchievable`（`TimeSharing.lean:47`）は負 rate を含む down-set**（confidence machine、`⌈exp(n·R)⌉ ≤ M` が R<0 で `⌈exp(neg)⌉=1` vacuous）。→ CV の `0≤R` guard + V の `∩Q` の根拠。
- **`mac_achievability_region`（`TimeSharing.lean:887`, `@[entry_point]`）は `hW : ∀ a b, 0<(W a).real{b}` + ⊇ union が full-support 限定**（`:890-891` に `0<p.real{a}` witness、confidence machine、再検証: signature Read）。→ V の `hW` threading + Dispatch C の all-prob upgrade の根拠。
- **`mutualInfo_superadditive_of_indep`（`ConverseNLetter.lean:532`, `@audit:ok`）は n-fold `∑I(Xᵢ;X̂ᵢ) ≤ I(Xⁿ;X̂ⁿ)` under `iIndepFun`**（confidence machine）。`hsub`（n=2 instantiate）の再利用候補。
- **`Real.continuous_negMulLog` は Mathlib 存在**（confidence machine、`InformationTheory/Fano/Measure.lean:333` で使用実績）。Dispatch C macInfo 連続性の building block。
- **`IsLowerSet × convexHull` は Mathlib 直系 0-hit**（confidence loogle-neg、query `IsLowerSet, convexHull` = SimplicialComplex 系 2 件のみ）。Gap C で自作 closure 済ゆえ壁でない。

（これ以上のキャッシュはしない。`docs/shannon/mac-facts.md` は現時点で作らない。）

---

## 判断ログ

append-only。決着済 entry は削除（git が履歴）、active のみ残す。≤ 10 entry。

1. **honesty trap ACTIVE（設計軸）**: 「code ⟹ (`mac_converse` hyps ∧ pentagon 不等式)」の 1-hyp bundle = 削除済 tier-5 `MACPerLetterChain₁₂` の再導入 = 禁止。6 obligation は各々 genuine sub-lemma か per-obligation sorry。regularity/nonneg 追加（Proposal F: `0≤R` / `IsProbabilityMeasure` / `hW` / `StandardBorelSpace`）は precondition で OK。
2. **CV signature 訂正（advisor concern 1+2 CONFIRMED）**: 旧 `{MACAchievable} ⊆ RHS` は false（`(−1,−1) ∈ {MACAchievable}\RHS`、`MACAchievable` は `⌈exp(n·R)⌉` 経由で R<0 vacuous な down-set）→ `0≤p.1∧0≤p.2` guard 追加。union scope も無制限でなく **`IsProbabilityMeasure` 限定**（非確率 `p` は `macInfo`=`macJointDistribution` entropy に junk、converse 出力 marginal は確率だが non-full-support）。
3. **V signature 訂正（advisor concern 3 CONFIRMED + hW 欠落）**: 旧 `macCapacityRegion = RHS` は false（`macCapacityRegion=closure{MACAchievable}` が down-closure で負象限含む、RHS⊆Q）→ **intersection 形 `macCapacityRegion ∩ Q = RHS`**（advisor 推奨 = blast radius 最小、`macCapacityRegion` consumer 0 本 touch、redefine 案の 4 decl 改変回避）。⊇ 継承元 `mac_achievability_region` の `hW` を明示 threading。⊆ に clamp-equivalence 補題（`MACAchievable R ↔ MACAchievable (max R 0)`、~15-25 LOC）が要る。
4. **pentagon well-formedness ledger（hac/hbc done, hsub 残・categorically harder）**: `hac/hbc = macInfo₁/₂ ≤ macInfoBoth`（`:241/:270`、非負項落し、done）。`hsub = macInfoBoth ≤ macInfo₁+macInfo₂` は **MI superadditivity** `I(X₁;Y)+I(X₂;Y)≤I(X₁X₂;Y)` under input independence で **categorically 別物**（「同 bridge ⇒ 軽い」heuristic 転用不可、~40-80 LOC, NOT a wall）。再利用候補 `mutualInfo_superadditive_of_indep`（`:532`, `@audit:ok`）を n=2 instantiate、唯一の genuine sub-obligation = 入力独立 `X₁⊥X₂`。Gap C `hbc` 追加（signature-drops-constraint 修正、反例 `n=2,a=(0,4),b=(4,0),c=(0,4),(0,2)`）は done。
5. **achievability full-support→all-prob upgrade REQUIRED（unavoidable）**: CV が non-full-support marginal を露出するため V ⊇ 側は all-prob union を cover せねば V を閉じられない。現状 `mac_achievability_region` は full-support union のみ（`:890-891` witness）。~100-200 LOC、gateway atom = `Continuous (fun p₁ ↦ macInfo₁ p₁ p₂ W)`（building block `Real.continuous_negMulLog` Mathlib 存在、NOT a wall、gateway-atom-first で先に dispatch-check）。
6. **CV assembly 点構成 TRAP（uniform 乗法縮小、per-coord clamp 禁止）**: 達成点を hull へ落とすのに **独立座標 `max 0 ·` clamp は Gap C の sum 制約 `hs` を破る**（反例 coord-shrink `x₁=−1,x₂=5`,`(∑c)/n=4`: `x₁+x₂=4≤4` だが `max0 x₁+max0 x₂=5>4`）。正解 = **uniform 乗法縮小 `(R₁(1−Pe)−log2/n, R₂(1−Pe)−log2/n)` + interior tail**。軸点（`R₁=0` or `R₂=0`）は別 **軸 casework**（`mac_axis1/2` mirror + mono）= Gap A で deferred した軸分岐の実体（CV-level、finite-n でない）。Gap C 出力は raw Fin n union ゆえ per-letter 集合等式 + `⋃`-reindex plumbing も要る。
7. **攻略順 B→A→C→D（advisor 4-dispatch、同時 1 体）**: B（CV-level 解析核: Fano→0 + 点構成 + 軸 casework、~120-200 LOC、CV unblock）→ A（`hsub` + CV assemble + set-reindexing、~100-180）→ C（achievability upgrade、独立・gateway-atom-first、~100-200）→ D（clamp-equivalence + V antisymmetry intersection 形、~55-105）。B 自己完結、C は achievability 側のみ（A/B 非依存）、A/D は入力後 plumbing。
