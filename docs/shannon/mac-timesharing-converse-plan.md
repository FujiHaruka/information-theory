# MAC: time-sharing converse half (CV + V) サブ計画

> **Parent**: [`mac-timesharing-plan.md`](mac-timesharing-plan.md) — 親の **CV**（converse half）+ **V**（full-region antisymmetry）を本サブ計画が担う。
> grandparent = [`mac-moonshot-plan.md`](mac-moonshot-plan.md) §撤退ライン **L-MAC5**（time-sharing 全凸包）。

**Status**: 📋 未着手（分離起票）。親 L-MAC5 の achievability half（M0–P4）は **proof-done, sorryAx-free, 独立監査 PASS**（commit `b216fb04`）。残 = 本 CV + V。read-only advisor の converse 精査で、親 CV 骨格が **4 つの独立重量 gap を 1 節に圧縮し、真の起点ブロッカー（code→ambient bridge）をスキップしている**と判明したため分離した（親 CV 節の分離 trigger = LOC 予測が親閾値超過、判断ログ #1）。

frozen slug: 撤退口 `@residual(plan:mac-timesharing-converse-plan)` = 本ファイル stem 一致（同 slug 再帰）。

<!--
記法は moonshot-plan-template と同じ（状態絵文字 📋🚧✅🔄、取り消し線、append-only 判断ログ）。
Parent ヘッダは plan_lint の親子グラフ構築点。子の状態を変えたら親の CV/V 行 / 進捗も同期する
（衝突時は子が SoT → CLAUDE.md「Plan / docs hygiene」親子整合）。
プラン予算 ≤ 600 行 / active 判断ログ ≤ 10 entry。
-->

## 進捗

- [x] M0（Gap C 分）— 凸幾何 hull 資産確定: `Finset.centerMass_mem_convexHull` / `Finset.mem_convexHull` / `mem_convexHull_iff_exists_fintype`（`Mathlib.Analysis.Convex.Combination`）。`IsLowerSet × convexHull` は Mathlib 直系 0-hit（greenfield 確定）だが下記 Gap C で自作 closure 済。ambient / reconciliation 分の在庫は Gap 0/B′ 着手時。📋（Gap 0/B′ 分残）
- [x] Gap C 🎯 gateway — `mac_avgPentagon_mem_convexHull` ✅ **proof-done, sorryAx-free**（commit `302dbe03`、`TimeSharingConverse.lean` 211 行）。down-closedness は座標スケーリング private helper `convexHull_mem_of_le` で genuine closure（**壁でなかった** = refutation 的中）。**signature に `hbc : ∀ i, b i ≤ c i` 追加**（`hac` 対称、機械検証反例で必須と判明、判断ログ #4）。
- [ ] Gap 0 — code→ambient bridge（bare `MACCode` から `mac_converse` の hyp 群を discharge、最大 greenfield）📋
- [ ] Gap A — 弱 converse 極限抽出（ε'→0/n→∞、Fano/n→0、R₁=0 軸 casework）📋
- [ ] Gap B′ — per-letter 同定（condMutualInfo → macInfo、既存 reconciliation bridge 流用）📋
- [ ] CV — converse headline assemble（`{MACAchievable} ⊆ closedConvexHull`）📋
- [ ] V — full-region antisymmetry headline + verify 📋

## ゴール / Approach

### Goal（最終定理 signature）

**ファイル**: `InformationTheory/Shannon/MultipleAccess/TimeSharingConverse.lean`（`TimeSharing.lean` を import）。namespace `InformationTheory.Shannon.MAC`。

```lean
-- CV headline: converse half
theorem mac_timesharing_converse (W) [IsMarkovKernel W] :
    {p | MACAchievable W p.1 p.2}
      ⊆ closedConvexHull ℝ (⋃ (p₁) (p₂), macPentagon p₁ p₂ W)

-- V headline (@[entry_point]): full region = antisymmetry
theorem mac_timesharing_capacity_region (W) [IsMarkovKernel W] :
    macCapacityRegion W = closedConvexHull ℝ (⋃ (p₁) (p₂), macPentagon p₁ p₂ W)
--   = Set.Subset.antisymm (CV 経由の ⊆ + 親 P4 achievability `mac_achievability_region` の ⊇)
```

`macCapacityRegion W = closure {p | MACAchievable W p.1 p.2}`。RHS は closed ゆえ
`closure {MACAchievable} ⊆ closedConvexHull` は CV から自動で従う。

### 重要な root diagnosis（最初に明記）

親 CV 骨格は「既存 `mac_converse` の per-letter 和形から始める」と書いていたが、**そのままでは
`MACAchievable` から開始できない**。`mac_converse`（`Converse.lean:830`、`@audit:ok`）は
**`dep_consumers` 0**（本 planner が `scripts/dep_consumers.sh InformationTheory.Shannon.MAC.mac_converse`
で機械確認、settled-facts 参照）の **floating message-level 文**であり、ambient 測度 `μ` と
その正則性（uniform messages / memoryless / independence / Markov / hcard）を **仮説として取る**。
`MACCode` からは構成しない。ゆえに CV は達成述語 `MACAchievable`（bare `MACCode` + 誤り→0）から
**code→ambient bridge（Gap 0）を経由しないと開始できない** = 親骨格がスキップしていた真の起点
ブロッカー。

### `mac_converse` 結論形（verbatim、`Converse.lean:848-871`）

`InMACCapacityRegion (Real.log M₁) (Real.log M₂) [B₁] [B₂] [Bboth]`。3 つの bound は
（`B₁` を代表に、`B₂` は user 対称、`Bboth` は mutualInfo）:

```
B₁ = (∑ i, condMutualInfo μ (encoder₁ (Msg₁ ω) i) (Ys i) (encoder₂ (Msg₂ ω) i)).toReal
     + Real.binEntropy (errorProb …)
     + errorProb … * Real.log (M₁ - 1)
```

per-letter 和 `∑ᵢ I(X₁ᵢ;Yᵢ|X₂ᵢ)` は正しい量だが **Fano 項（`binEntropy(errorProb)` +
`errorProb·log(M₁−1)`）が付き**、fixed code per 文で operational でない。operational rate を出すには
`ε'→0 / n→∞` の極限（Fano 項 → 0）が要る = Gap A。前提 `hcard₁/hcard₂ = 2 ≤ M₁/M₂`（`M₁,M₂ ≥ 2`）に
注意 = 軸 `R₁=0`（`M₁=1` 許容）は `mac_converse` の適用域外ゆえ別扱い（Gap A の軸 casework）。

### Approach（overall strategy / shape of solution）

converse = 「達成 rate pair `(R₁,R₂)` は各時刻の周辺入力ペンタゴン点の**時間平均**として凸包に入る」を
operational に組む。核心を **4 つの独立 sub-lemma（Gap 0/A/B′/C）**に分解し、各 gap は
**単独で genuine に閉じるか、詰まればその 1 gap のみ sorry + `@residual`** とする（後述 honesty trap）。
達成 rate pair `(R₁,R₂)`（`MACAchievable`）から出発して:

1. **Gap 0 (ambient)**: 各 `n`・各 `MACCode c` から ambient 測度 `μ = uniform(Fin M₁ × Fin M₂) ⊗ per-letter channel W` を構成し、`mac_converse` の hyp 群（uniform / memoryless / indep / markov）を discharge。
2. **Gap A (弱 converse 極限)**: `MACAchievable` の `∀ε'∃N∀n≥N∃code` から、`mac_converse` の per-letter 和 bound に対し `ε'→0 / n→∞` を取り、Fano 項 `/n → 0`、`log M₁ ≥ n·R₁`（`⌈exp(nR₁)⌉ ≤ M₁`）で `R₁ ≤ liminf (1/n)∑ᵢ condMIᵢ` 等を抽出。
3. **Gap B′ (per-letter 同定)**: 各時刻の `condMutualInfo μ X₁ᵢ Yᵢ X₂ᵢ = macInfo₁ (law X₁ᵢ)(law X₂ᵢ) W` を、既存 reconciliation bridge で同定 → per-letter 点 `(macInfo₁ᵢ, macInfo₂ᵢ)` が product-input `p₁ᵢ⊗p₂ᵢ` のペンタゴン点。
4. **Gap C (平均 pentagon → 凸包)**: 「点 `(R₁,R₂)` ≤ per-letter 点の時間平均 ∈ hull」。平均 corner が凸包に入り、正象限の **down-closedness** で `(R₁,R₂)` を線分下に配置。**これが唯一の genuine Mathlib 壁候補**（lower-set 凸包の down-closedness、in-project に用例なし）。

計 ~520-880 LOC。**攻略順は下記「攻略順」参照**（純幾何・壁候補の Gap C を **gateway として最初に単独 dispatch**）。

### critical（honesty、判断ログ #2 で ACTIVE）

**「code ⟹ (`mac_converse` hyps ∧ pentagon 不等式)」を 1 hyp に bundle するのは禁止** = 削除済
tier-5 scaffold `MACPerLetterChain₁₂`（`mac-inventory.md:136`）の再導入。Gap 0/A/B′/C は各々
genuine sub-lemma か **per-gap sorry**。regularity 追加（`StandardBorelSpace` /
`IsMarkovKernel` = Proposal F）は precondition で OK。

### 型クラス設定 / Proposal F（正則性追加、honest precondition）

converse file の `variable` ブロックに以下を追加する（親 P0 の型クラス設定 = MAC moonshot
「事故注意ボックス」verbatim に加えて）:

- `[StandardBorelSpace α₁] [StandardBorelSpace α₂] [StandardBorelSpace β]` —
  `mac_converse` の SingleLetterization 節（disintegration / condDistrib）が要求。親
  `TimeSharing.lean` の variable ブロック（`:35` から始まる、`StandardBorelSpace` 不在を planner
  が機械確認）は欠く。Fintype から導けるが **宣言必須**。
- `[IsMarkovKernel W]` — channel 正則性（per-theorem 引数でも可）。

これらは **precondition（regularity）で load-bearing でない**。Fano 項や per-letter chain を hyp に
encode しない。

---

## Gap 分解（4 独立ブロック）

| Gap | 内容 | 新規? | LOC | 攻略順 |
|---|---|---|---|---|
| **Gap 0 ambient** | bare `MACCode` から `μ = uniform(Fin M₁ × Fin M₂) ⊗ per-letter channel W` を構成、`mac_converse` の hyp（uniform / memoryless / indep / markov / hcard）を discharge。`IIDAmbient.lean:64 macAmbientMeasure` は **product-input i.i.d. ambient**（固定 `p₁⊗p₂` の n 重）= **流用不可**（converse 入力は任意 code、`c.encoder` 経由の任意 joint input）。**greenfield、真の起点** | NEW | 200-300 | 2 |
| **Gap A 弱 converse 極限** | `∀ε'∃N∀n≥N∃code` → `ε'→0 / n→∞`、Fano `/n → 0`、`log M₁ ≥ n·R₁`（from `⌈exp(nR₁)⌉ ≤ M₁`）、`R₁ ≤ liminf (1/n)∑ᵢ condMIᵢ` 抽出。**R₁=0 軸は別扱い**（achievability の `mac_axis1/2` 軸 casework を mirror、`mac_converse` の `M₁≥2` 前提を暗黙にしない） | NEW | 120-200 | 3 |
| **Gap B′ per-letter 同定** | `condMutualInfo μ X₁ᵢ Yᵢ X₂ᵢ = macInfo₁ (law X₁ᵢ)(law X₂ᵢ) W`。**reconciliation bridge 既存・流用**: `macInfo₁_eq_condMutualInfo_toReal`（`Reconciliation.lean:222`, `@audit:ok`）/ `macInfo₂_eq_condMutualInfo_toReal`（`:237`）/ `macInfoBoth_eq_mutualInfo_toReal`（`:252`）+ `condMutualInfo_map_left_measurableEquiv`（`CondMutualInfo.lean:400`）/ `condMutualInfo_map_middle_measurableEquiv`（`:462`）。**新規は `μ.map (X₁ᵢ,X₂ᵢ,Yᵢ) = macJointDistribution p₁ᵢ p₂ᵢ W` の同定のみ** | HALF | 100-180 | 4 |
| **Gap C 平均 pentagon → 凸包** | 「点 ≤ 平均 ∈ hull」。`Finset.centerMass_mem_convexHull`（`Mathlib.Analysis.Convex.Combination`）で平均 corner ∈ hull の半分は出る。**`convexHull (⋃ macPentagon)` の down-closedness は greenfield**（in-project に `IsLowerSet` × convexHull 用例なし）= **唯一の genuine Mathlib 壁候補** | NEW | 100-200 | **1 (gateway)** |

計 **~520-880 LOC**。

---

## Phase 詳細（攻略順）

### M0 — 在庫（凸幾何 hull 資産 + ambient 構成資産 + reconciliation bridge verbatim）
**proof-log**: no

- [ ] **凸幾何 Mathlib 資産**（Gap C 用、signature verbatim + `[...]` 型クラス verbatim）:
  - `Finset.centerMass_mem_convexHull`（`Mathlib.Analysis.Convex.Combination`）— 平均 corner ∈ hull。
  - `convexHull_min` / `segment_subset_convexHull` / `closedConvexHull_eq_closure_convexHull`
    （親 M0 で確認済、再掲）。
  - `IsLowerSet` / down-closedness × `convexHull` の Mathlib 補題探索（loogle 0-hit 見込み → Gap C
    の壁根拠に。`|- _ ∈ convexHull _` の conclusion-shape 再検索 + template 補題 1 本の自作行数見積り
    を M0 で固定する = 壁判定必須メタデータ）。
- [ ] **ambient 構成資産**（Gap 0 用、verbatim）:
  - `macAmbientMeasure`（`IIDAmbient.lean:64`）+ `.instIsProbabilityMeasure`（`:69`）の**構成形を
    参照**（流用不可だが `Measure.pi` × uniform message の組み方の型 template）。
  - `Measure.count` / uniform `(card)⁻¹ • Measure.count`（`mac_converse` の `hMsg_uniform` 形）、
    `IsMemorylessChannel` / `IsMarkovChain`（`Converse.lean` の hyp 定義 `*_def` を Read）。
- [ ] **reconciliation bridge verbatim**（Gap B′ 用）: 上表の 5 補題の signature + 前提を verbatim 記録。
  `macJointDistribution` の定義（`Reconciliation.lean` / `Achievability.lean`）を Read し、
  `μ.map (X₁ᵢ,X₂ᵢ,Yᵢ)` との一致条件を固定。
- [ ] **`mac_converse` 前提 `*_def` verbatim**: `IsMemorylessChannel` / `IsMarkovChain` /
  `hMsg₁₂_uniform` の定義を Read（Gap 0 で discharge する対象の正確な形）。`hcard₁/hcard₂ = 2≤M`
  を確認（軸 casework の根拠）。
- **撤退**: 在庫 Phase、sorry 不要。`mathlib-inventory` サブエージェントに委任する場合は
  **per-lemma 構造化出力**（file:line + signature + `[...]` verbatim + conclusion 形）を要求。

---

### Gap C 🎯 gateway — `mac_avgPentagon_mem_convexHull`（純 ℝ 凸幾何）
**proof-log**: yes（lower-set 凸包の down-closedness = greenfield 壁候補、再開根拠必須）

**最初に単独 dispatch**（純 ℝ 凸幾何・measure theory 不要、gateway-atom-first）。gateway atom:

**✅ DONE**（`302dbe03`、sorryAx-free）。実装 signature（`hbc` 追加済、verbatim）:

```lean
theorem mac_avgPentagon_mem_convexHull {n : ℕ} (hn : 0 < n)
    (a b c : Fin n → ℝ) (h0a : ∀ i, 0 ≤ a i) (h0b : ∀ i, 0 ≤ b i)
    (hac : ∀ i, a i ≤ c i) (hbc : ∀ i, b i ≤ c i) (hsub : ∀ i, c i ≤ a i + b i)
    {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (h1 : R₁ ≤ (∑ i, a i) / n) (h2 : R₂ ≤ (∑ i, b i) / n) (hs : R₁ + R₂ ≤ (∑ i, c i) / n) :
    (R₁, R₂) ∈ convexHull ℝ
      (⋃ i, ({p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ a i ∧ p.2 ≤ b i ∧ p.1 + p.2 ≤ c i}
             : Set (ℝ × ℝ)))
```

**`hbc` は元 plan signature が欠いていた必須 precondition**（欠くと false: 機械検証反例 `n=2, a=(0,4),
b=(4,0), c=(0,4), (0,2)` — 両 pentagon が x 軸に潰れ `(0,2)∉hull`）。`hac` 対称ゆえ **genuine な
regularity precondition**（load-bearing bundling でない）。**下流 CV へのインパクト**: CV instantiate
時に `a=macInfo₁ᵢ, b=macInfo₂ᵢ, c=macInfoBothᵢ` で `hac : macInfo₁ᵢ ≤ macInfoBothᵢ` /
`hbc : macInfo₂ᵢ ≤ macInfoBothᵢ` を discharge する必要（product 入力下でチェーン則
`macInfoBoth − macInfo₁ = I(X₂;Y) ≥ 0` / `macInfoBoth − macInfo₂ = I(X₁;Y) ≥ 0`、MI 非負で成立）。
**既存補題なし**（`rg` 確認、orchestrator）→ CV 節に新規小 obligation として追加（下記 CV 節）。

- **mechanism**: 平均 dominant corner `(ā, c̄−ā)` と `(c̄−b̄, b̄)`（`ā=(∑a)/n` 等）が
  `Finset.centerMass_mem_convexHull` で hull に入る → 正象限での **down-closedness** + 初等 2D
  casework で `(R₁,R₂)` を線分下に配置。
- **まず lean-implementer に本 atom 1 本を dispatch**。通れば CV assemble の凸包側が確定。
- **予想規模**: ~100-200 行。
- **撤退ライン**: **最有力 stall = lower-set 凸包の down-closedness**（greenfield、in-project 用例なし）。
  3+ turn stall なら **その sub-lemma のみ** `sorry` + `@residual(plan:mac-timesharing-converse-plan)`、
  他（centerMass による平均 corner ∈ hull 半分 + 2D casework）は genuine 維持。**壁判定は必須
  メタデータ**（試したルート ≥2 + conclusion-shape 再検索 + template 自作行数）を判断ログに残す。

---

### Gap 0 — code→ambient bridge（`mac_converse` hyp 群 discharge）
**proof-log**: yes（本計画最大の greenfield、ambient 構成、再開根拠必須）

**M0 在庫（`mac_converse` signature verbatim、`Converse.lean:830-847`、orchestrator 確認済）**。
discharge する引数（10 個中の非型クラス分）:
```
[NeZero M₁] [NeZero M₂]
(μ : Measure Ω) [IsProbabilityMeasure μ]                                    -- ← 構成対象
(Msg₁ : Ω → Fin M₁) (Msg₂ : Ω → Fin M₂) (Ys : Fin n → Ω → β)                 -- ← 構成対象（射影）
(c : MACCode M₁ M₂ n α₁ α₂ β)
hMsg₁ hMsg₂ : Measurable ;  hYs : ∀ i, Measurable (Ys i)                     -- 可測性
hMsg₁_uniform : μ.map Msg₁ = (card (Fin M₁))⁻¹ • Measure.count               -- uniform 周辺
hMsg₂_uniform : μ.map Msg₂ = (card (Fin M₂))⁻¹ • Measure.count
hMsg₁₂_uniform : μ.map (Msg₁,Msg₂) = (card (Fin M₁ × Fin M₂))⁻¹ • Measure.count -- joint uniform
h_memo : IsMemorylessChannel μ (fun i ω ↦ (c.encoder₁ (Msg₁ ω) i, c.encoder₂ (Msg₂ ω) i)) Ys
h_indep : mutualInfo μ Msg₁ Msg₂ = 0                                          -- message 独立
hmarkov : IsMarkovChain μ (fun ω ↦ (Msg₁ ω, Msg₂ ω))
            (fun ω ↦ (fun j ↦ c.encoder₁ (Msg₁ ω) j, fun j ↦ c.encoder₂ (Msg₂ ω) j))
            (fun ω j ↦ Ys j ω)
hcard₁ : 2 ≤ M₁ ; hcard₂ : 2 ≤ M₂                                            -- ← Gap A の軸 casework へ
```
結論 = `InMACCapacityRegion (log M₁) (log M₂) [B₁] [B₂] [Bboth]`（各 `Bᵢ` に Fano 項 = Gap A で消去）。
自然な ambient: `Ω = Fin M₁ × Fin M₂ × (Fin n → β)`、`(m₁,m₂) ~ uniform ⊗ uniform`、
`(Yᵢ) | (m₁,m₂) ~ ∏ᵢ W(encoder₁ m₁ i, encoder₂ m₂ i)`（`Measure.compProd` + per-letter kernel）。
`Msg₁,Msg₂,Ys` は Ω の射影。**`IsMemorylessChannel` / `IsMarkovChain` の `*_def` を Read** して
discharge 形を掴む（M0 残）。

- [ ] **ambient 構成** `macConverseAmbient c := uniform(Fin M₁ × Fin M₂) ⊗ (per-letter channel W)`。
  message は uniform、input は `c.encoder₁ / c.encoder₂` 経由の deterministic map、output は W。
  `IIDAmbient.macAmbientMeasure`（`:64`）は **固定 product input `p₁⊗p₂` の i.i.d. ambient** ゆえ
  **流用不可**（converse は任意 code の任意 joint input）— 構成形のみ template として参照。
- [ ] **hyp discharge**（各々 genuine sub-lemma）:
  - `hMsg₁_uniform / hMsg₂_uniform / hMsg₁₂_uniform`（uniform message marginal）。
  - `h_memo : IsMemorylessChannel μ …`（per-letter channel の memoryless 性、構成から直）。
  - `h_indep : mutualInfo μ Msg₁ Msg₂ = 0`（message 独立、uniform product marginal から）。
  - `hmarkov : IsMarkovChain μ …`（Msg → encoder → Y の Markov 性）。
- **依存 in-project decl**: `MACCode` / `MACChannel` / `averageErrorProb`（`Basic.lean`）、
  `Measure.pi` / `Measure.count`、`mac_converse` の hyp 定義（`Converse.lean`）。
- **予想規模**: ~200-300 行（**本計画の重心 2 番手**、ambient 構成 + 4 hyp discharge）。
- **撤退ライン**: hyp のどれかで詰まったら **その 1 hyp discharge の sub-lemma のみ** `sorry` +
  `@residual(plan:mac-timesharing-converse-plan)`。ambient 構成全体を hyp で受ける
  （= `mac_converse` の前提を丸ごと外から渡す load-bearing bundle）は **禁止**。

---

### Gap A — 弱 converse 極限抽出（Fano 消去 + rate 抽出）
**proof-log**: yes（極限論証 + 軸 casework、再開根拠必須）

- [ ] **極限抽出** `mac_converse_rate_extract`: `MACAchievable W R₁ R₂` の `∀ε'∃N∀n≥N∃code` から、
  各 `n` の `mac_converse` bound（Gap 0 で ambient を供給）に対し `ε'→0 / n→∞`。
  - Fano 項 `binEntropy(errorProb) + errorProb·log(M₁−1)` を `/n` して `→ 0`（`errorProb < ε'`）。
  - `log M₁ ≥ n·R₁`（from `⌈exp(n·R₁)⌉ ≤ M₁`、`Nat.ceil` 単調 + `Real.exp_log`）。
  - `R₁ ≤ liminf (1/n)∑ᵢ condMIᵢ`、`R₂ ≤ liminf (1/n)∑ᵢ …`、`R₁+R₂ ≤ liminf (1/n)∑ᵢ mIᵢ` を抽出。
- [ ] **軸 casework**（`mac_converse` の `hcard = 2≤M₁/M₂` 前提の適用域外）:
  `R₁=0`（`M₁=1` 許容）は user-1 情報ゼロ = achievability の `mac_axis1/mac_axis2` 軸 casework を
  **mirror**。`M₁≥2` を暗黙前提にしない（`(0,R₂)` / `(R₁,0)` / `(0,0)` を明示分岐）。
- **予想規模**: ~120-200 行。
- **撤退ライン**: `liminf` 抽出 / 有限和の平均境界で詰まったら **その sub-lemma のみ** `sorry` +
  `@residual(plan:mac-timesharing-converse-plan)`。「達成 → rate 不等式」を 1 hyp で受けない
  （under-hypothesized bundle 禁止）。

---

### Gap B′ — per-letter 同定（condMutualInfo → macInfo）
**proof-log**: yes（`μ.map` 同定は新規、reconciliation bridge は流用、再開根拠必須）

- [ ] **per-letter 同定** `mac_condMI_eq_macInfo_at`:
  `condMutualInfo μ (X₁ᵢ) (Yᵢ) (X₂ᵢ) = macInfo₁ (μ.map X₁ᵢ) (μ.map X₂ᵢ) W`（user 1、対称に user 2 /
  Both）。**既存 bridge 流用**: `macInfo₁_eq_condMutualInfo_toReal`（`Reconciliation.lean:222`）/
  `macInfo₂_eq_condMutualInfo_toReal`（`:237`）/ `macInfoBoth_eq_mutualInfo_toReal`（`:252`）+
  `condMutualInfo_map_left_measurableEquiv`（`CondMutualInfo.lean:400`）/
  `condMutualInfo_map_middle_measurableEquiv`（`:462`）。
- [ ] **新規（唯一）**: `μ.map (fun ω ↦ (X₁ᵢ ω, X₂ᵢ ω, Yᵢ ω)) = macJointDistribution p₁ᵢ p₂ᵢ W`
  の同定（`p₁ᵢ = μ.map X₁ᵢ` 等、per-letter joint law が macJointDistribution 形に一致）。
- **予想規模**: ~100-180 行（HALF: bridge 流用で軽、`μ.map` 同定のみ新規）。
- **撤退ライン**: `μ.map` 同定で詰まったら **その 1 本のみ** `sorry` +
  `@residual(plan:mac-timesharing-converse-plan)`。bridge 側は `@audit:ok` 流用ゆえ独自 sorry 不要見込み。

---

### CV — converse headline assemble
**proof-log**: no（Gap 0/A/B′/C の組立 plumbing）

- [x] **（Gap C の `hac`/`hbc` 供給）pentagon well-formedness 補題** 2 本 ✅ **proof-done sorryAx-free**
  （commit `b7a7379f`、`TimeSharingConverse.lean`）: `mac_macInfo₁_le_macInfoBoth` /
  `mac_macInfo₂_le_macInfoBoth`。**reconciliation bridge 経由が entropy-direct より lea**: `@audit:ok` 橋
  `macInfo₁_eq_condMutualInfo_toReal` 等 + `mutualInfo_chain_rule`（`I((X₁,X₂);Y)=I(X₁;Y)+I(X₂;Y|X₁)`）
  + `self_le_add_left` + `ENNReal.toReal_mono`（各 3 行）。予測「40-80 行 ×2」は over-budget だった
  （bridge が既に condMutualInfo に押し込んでいた）→ **同 bridge に乗る Gap B′ も予測より軽い公算**。
  precondition に `[StandardBorelSpace α_i]`（Proposal F、bridge 要求、honest regularity）追加、`import
  Reconciliation` を追加（cycle なし）。
- [ ] `mac_timesharing_converse`（上記 Goal signature）:
  達成 `(R₁,R₂) ∈ {MACAchievable}` から、Gap A で rate 不等式 → Gap 0 で ambient → Gap B′ で
  per-letter 点 `(macInfo₁ᵢ, macInfo₂ᵢ)` が `p₁ᵢ⊗p₂ᵢ` のペンタゴン点 → 上 well-formedness で
  `hac`/`hbc` 供給 → Gap C（`mac_avgPentagon_mem_convexHull`）で
  `(R₁,R₂) ∈ convexHull (⋃ macPentagon)` → `convexHull ⊆ closedConvexHull`
  （`convexHull_subset_closedConvexHull`）。
- **予想規模**: ~60-100 行（wire）+ well-formedness ~80-160 行。
- **撤退ライン**: いずれかの Gap が sorry の場合、CV は推移的にその sorry を継承する
  （独自 sorry を新設しない）。

---

### V — full-region antisymmetry headline + verify
**proof-log**: no

- [ ] `mac_timesharing_capacity_region`（`@[entry_point]`、full region）=
  `Set.Subset.antisymm`（CV 経由 `macCapacityRegion ⊆ closedConvexHull` + 親 P4
  `mac_achievability_region` の `closedConvexHull ⊆ macCapacityRegion`）。
  `closure {MACAchievable} ⊆ closedConvexHull` は RHS closed + CV から従う。
- [ ] `lake env lean InformationTheory/Shannon/MultipleAccess/TimeSharingConverse.lean` silent
  （sorry warning のみ許容 = type-check done）。
- [ ] proof done 判定: `#print axioms mac_timesharing_converse` /
  `mac_timesharing_capacity_region` = `[propext, Classical.choice, Quot.sound]`（sorryAx-free）。
- [ ] 新規 `sorry` + `@residual` 導入 commit があれば **独立 honesty 監査**（`honesty-auditor`）を
  session 内で起動（orchestrator-mandatory）。特に Gap 0 の ambient hyp discharge / Gap A の
  rate 抽出が load-bearing bundle でないことを検査対象に明示。
- [ ] `InformationTheory.lean` に `TimeSharingConverse` の import を追加（orchestrator が最後に）。
- [ ] **親 co-stage**: 親 `mac-timesharing-plan.md` の CV/V 進捗行 + DAG を本 sub-plan 完了状態に同期。

---

## 攻略順 / 推奨 leg 数

1. **Gap C gateway**（純幾何、壁候補、単独 dispatch）→ 2. **Gap 0 ambient**（最大、greenfield）→
   3. **Gap A 極限** → 4. **Gap B′ 同定** → 5. **CV assemble + V antisymmetry**。
- **推奨 4-5 leg**（同時 1 体まで、CLAUDE.md「Max one parallel agent」）。
- 純幾何・壁候補の Gap C を先頭に置く理由: 通れば凸包側が確定し、残 3 gap は measure-theoretic な
  「ペンタゴン点を作って hull に入れる」plumbing に縮退する（gateway-atom-first）。

---

## 撤退ライン / honesty（最重要）

- 撤退口は **`sorry` + `@residual(plan:mac-timesharing-converse-plan)` のみ**（CLAUDE.md
  「検証の誠実性」、同 slug 再帰）。各 gap は独立 sub-lemma で、**詰まった gap の当該 sub-lemma のみ**
  sorry。他 gap は genuine 維持。
- **honesty trap ACTIVE**: 「code ⟹ (`mac_converse` hyps ∧ pentagon 不等式)」を **1 hyp に bundle
  するのは禁止** = 削除済 tier-5 `MACPerLetterChain₁₂`（`mac-inventory.md:136`）の再導入。Gap 0/A/B′/C
  は各々 genuine か per-gap sorry。**per-letter chain / rate 不等式 / Fano bound を受ける
  load-bearing `*Hypothesis` predicate は禁止**。
- **regularity 追加は precondition で OK**（load-bearing でない、Proposal F）: `StandardBorelSpace α₁/α₂/β`
  / `IsMarkovKernel W` / `IsProbabilityMeasure` / 可測性。
- **最有力壁候補 = Gap C の lower-set 凸包 down-closedness**（唯一の genuine Mathlib 壁候補）。
  ここで 3+ turn stall なら wall 化判定を検討するが、**壁判定は反証義務**（CLAUDE.md「Verification」）:
  loogle 0-hit（必要条件）→ conclusion-shape 再検索 + template 補題 1 本の自作行数見積り →
  それでも塞がれば `@residual(plan:mac-timesharing-converse-plan)` で park（wall 昇格は後続 PR 判断）。

---

## settled-facts（minimal、再導出可能なものは都度 `rg` / `#print axioms` / loogle）

- **`mac_converse`（`Converse.lean:830`）は `dep_consumers` 0**（confidence machine、再検証:
  `scripts/dep_consumers.sh InformationTheory.Shannon.MAC.mac_converse`）。= floating message-level
  文であり ambient μ + 正則性を仮説で取る。**Gap 0（code→ambient bridge）が必須**の根拠。
- **`mac_converse` 結論に Fano 項が付く**（`binEntropy(errorProb) + errorProb·log(M−1)`、verbatim
  `Converse.lean:848-871`）。operational rate には `ε'→0 / n→∞` 極限が要る = Gap A の根拠。
- **`mac_converse` の hcard = `2 ≤ M₁ / M₂`**（`Converse.lean:847`）。軸 `R₁=0`（`M₁=1`）は適用域外
  → Gap A の軸 casework が必要。
- **reconciliation bridge 5 本は `@audit:ok` 流用可**（`macInfo₁/₂_eq_condMutualInfo_toReal`
  `Reconciliation.lean:222/237`、`macInfoBoth_eq_mutualInfo_toReal` `:252`、
  `condMutualInfo_map_left/middle_measurableEquiv` `CondMutualInfo.lean:400/462`、planner 機械確認）。
  Gap B′ の新規は `μ.map (X₁ᵢ,X₂ᵢ,Yᵢ) = macJointDistribution` 同定のみ。
- **`macAmbientMeasure`（`IIDAmbient.lean:64`）は Gap 0 に流用不可**（固定 product input i.i.d.
  ambient、converse は任意 code の joint input）。構成形の型 template としてのみ参照。
- **`TimeSharing.lean` の variable ブロック（`:35`）に `StandardBorelSpace` 不在**（planner 機械確認）
  → Proposal F で converse file の variable ブロックに宣言追加が必要。

- **Gap C `mac_avgPentagon_mem_convexHull` は proof-done sorryAx-free**（confidence machine、再検証:
  `lake env lean InformationTheory/Shannon/MultipleAccess/TimeSharingConverse.lean` silent +
  `#print axioms mac_avgPentagon_mem_convexHull`、commit `302dbe03`）。down-closedness は自作 private
  helper `convexHull_mem_of_le`（座標スケーリング）で closure = **壁でなかった**。
- **`IsLowerSet × convexHull` は Mathlib 直系 0-hit**（confidence loogle-neg、query `IsLowerSet, convexHull`
  = SimplicialComplex 系 2 件のみ）。ただし down-closedness は自作で closure 済ゆえ壁でない。
- **`macInfo₁/₂ ≤ macInfoBoth` の well-formedness 補題は in-project 不在**（confidence loogle-neg 相当、
  再検証: `rg "le_macInfoBoth|macInfo.*_le_" InformationTheory/Shannon/MultipleAccess/*.lean`）→ CV で
  新規 ~40-80 行 × 2。product 入力下でチェーン則 + MI 非負で成立（human-judgment、既 verbatim 確認）。

（これ以上のキャッシュはしない。`docs/shannon/mac-facts.md` は現時点で作らない。）

---

## 判断ログ

append-only。決着済 entry は削除（git が履歴）、active のみ残す。≤ 10 entry。

1. **sub-plan 分離を親から実施（active、分離根拠）**: 親 CV 節が 4 独立重量 gap（Gap 0/A/B′/C）を
   1 節に圧縮し、真の起点ブロッカー（Gap 0 = code→ambient bridge）をスキップしていた。LOC 予測
   ~520-880 が親の分離 trigger（>300 LOC / 判断ログ >5）を超過 → 本 sub-plan に分離、親 CV/V 行は
   backlink + `@residual(plan:mac-timesharing-converse-plan)` に圧縮（child-is-SoT）。
2. **honesty trap ACTIVE（active、設計軸）**: 「code ⟹ (`mac_converse` hyps ∧ pentagon 不等式)」の
   1-hyp bundle = 削除済 tier-5 `MACPerLetterChain₁₂` の再導入 = 禁止。Gap 0/A/B′/C は各々 genuine
   sub-lemma か per-gap sorry。regularity 追加（Proposal F）は precondition で OK。
3. **root diagnosis = Gap 0 が真の起点（active）**: 親骨格の「`mac_converse` 和形から始める」は
   `mac_converse` が dep_consumers 0 の floating 文（ambient を仮説で取る）ゆえ `MACAchievable` から
   直接開始不能。Gap 0（ambient 構成 + hyp discharge）が起点。攻略順は純幾何・壁候補の Gap C を
   gateway に先行させ、残 3 gap を measure plumbing に縮退させる。
4. **Gap C signature-drops-constraint 修正（active、実装結果）**: 元 Gap C signature は
   `hbc : ∀ i, b i ≤ c i` を欠き **false**（機械検証反例 `n=2, a=(0,4),b=(4,0),c=(0,4),(0,2)`）。実装
   エージェントが `hac` 対称の genuine precondition として追加（load-bearing bundling でない、honest）。
   down-closedness 壁候補は refutation どおり座標スケーリングで genuine closure（`convexHull_mem_of_le`）。
   **CV への波及**: `hac`/`hbc` = `macInfo₁/₂ ≤ macInfoBoth` を CV で新規 discharge（well-formedness 2 本、
   既存なし）。新 sorry/@residual 導入なし（sorryAx-free）ゆえ独立 honesty 監査は非該当、signature 強化の
   honesty 疑義は macInfo 定義 verbatim 確認で解消済。
