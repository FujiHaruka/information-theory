# MAC: time-sharing 全凸包形 (L-MAC5) genuine-closure サブ計画

> **Parent**: [`mac-moonshot-plan.md`](mac-moonshot-plan.md) §撤退ライン **L-MAC5** (line 233) /
> [`textbook-roadmap.md`](../textbook-roadmap.md) §Ch.15 (Network IT / DSC mini-chapter)
>
> **Status**: **着手決定 (scope-out 解除)**。従来 L-MAC5 は「time-sharing 全凸包形は scope-out」
> だったが、read-only advisor の tractability 評価で「**Mathlib 壁ではない、operational な新規論証
> ~900-1200 LOC over ≥2 sessions**」と判定され着手。corner-point form (`mac_converse` +
> `mac_achievability`、両 genuine) は既達 = 本計画の入力資産。

<!--
記法は moonshot-plan-template と同じ（状態絵文字 📋🚧✅🔄、取り消し線、append-only 判断ログ）。
Parent ヘッダは plan_lint の親子グラフ構築点。子の状態を変えたら親の L-MAC5 行 / DAG も同期する
（衝突時は子が SoT → CLAUDE.md「Plan / docs hygiene」親子整合）。
プラン予算 ≤ 600 行 / active 判断ログ ≤ 10 entry。
ファイル名 stem `mac-timesharing-plan` は撤退口 `@residual(plan:mac-timesharing-plan)` の slug と一致。
-->

## 進捗

**achievability half (M0–P4) = proof-done, sorryAx-free, 独立監査 PASS** (commit `b216fb04`)。残 = CV + V。

- [x] M0 — inventory (Mathlib 凸包資産 + 流用 in-project decl 確認) ✅
- [x] P0 — `MACAchievable` def + `macPentagon` set def + strict-interior wrapper ✅
- [x] P1 🎯 gateway — `mac_timesharing_strict` (block 連結による凸性、exact→strict restate) ✅
- [x] P2 — `mac_capacityRegion_convex` / `_isClosed` (direct 構成) ✅
- [x] P3 — `mac_pentagon_subset_capacityRegion` (strict 内部 + 退化 3-way: (0,0)=`mac_achievable_zero_zero`, 軸=`mac_axis1/2_achievable` の M=1 engine 特殊化) ✅
- [x] P4 — achievability headline `mac_achievability_region` (`@[entry_point]`) ✅ `@audit:ok`
- [ ] CV — converse half (`{MACAchievable} ⊆ closedConvexHull`) 🚧 → [`mac-timesharing-converse-plan.md`](mac-timesharing-converse-plan.md)（凸包側 done: Gap C gateway `302dbe03` + pentagon well-formedness `b7a7379f`、いずれも proof-done sorryAx-free; 残 = measure 側 Gap 0/A/B′ + assemble）**← 次**
- [ ] V — full-region antisymmetry headline 📋 → [`mac-timesharing-converse-plan.md`](mac-timesharing-converse-plan.md)

## ゴール / Approach

### Goal (最終定理 signature)

**honest target = (α) operational full region** (Cover–Thomas Thm 15.3.1 time-sharing 版)。
namespace `InformationTheory.Shannon.MAC`、greenfield。既存 corner-point 層は signature 不変で
**流用のみ**ゆえ `dep_consumers` blast radius ゼロ (新規 decl 追加 + `mac_achievability` を
consume するだけ、既存共有補題の signature 改変なし → ripple 検証不要)。

```lean
-- 達成可能述語 (operational primitive、正直な定義)
def MACAchievable (W : MACChannel α₁ α₂ β) (R₁ R₂ : ℝ) : Prop :=
  ∀ ε' > 0, ∃ N, ∀ n ≥ N, ∃ M₁ M₂ (_ : ⌈exp (n·R₁)⌉ ≤ M₁) (_ : ⌈exp (n·R₂)⌉ ≤ M₂)
    (c : MACCode M₁ M₂ n α₁ α₂ β), (c.averageErrorProb W).toReal < ε'

-- 固定 product input のペンタゴン (既存 macInfo₁/₂/Both = Achievability.lean:218/225/232 を再利用)
def macPentagon (p₁ : Measure α₁) (p₂ : Measure α₂) (W) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ macInfo₁ p₁ p₂ W ∧ p.2 ≤ macInfo₂ p₁ p₂ W
       ∧ p.1 + p.2 ≤ macInfoBoth p₁ p₂ W}

-- 操作的容量領域 = 達成集合の閉包 (下記「headline RHS 訂正」参照)
def macCapacityRegion (W) : Set (ℝ × ℝ) := closure {p | MACAchievable W p.1 p.2}

-- achievability half (headline):
--   closedConvexHull ℝ (⋃ p₁ p₂, macPentagon p₁ p₂ W) ⊆ macCapacityRegion W
-- converse half:
--   {p | MACAchievable W p.1 p.2} ⊆ closedConvexHull ℝ (⋃ p₁ p₂, macPentagon p₁ p₂ W)
-- full region (antisymmetry):
--   macCapacityRegion W = closedConvexHull ℝ (⋃ p₁ p₂, macPentagon p₁ p₂ W)
```

`mac_achievability` (Achievability.lean:1992、`@audit:ok`) が inner `∃N…` block を verbatim 供給
(strict corner `R₁<macInfo₁ ∧ R₂<macInfo₂ ∧ R₁+R₂<macInfoBoth`、full-support `hp₁/hp₂/hW`、
`0<R₁`, `0<R₂` 前提)。

**headline RHS 訂正 (advisor 案からの逸脱、判断ログ #2)**: advisor 原案は RHS を生の
`{p | MACAchievable W p.1 p.2}` と置き P2 で「`IsClosed` (limiting/diagonal)」を証明する計画
だったが、これは **false-as-stated**。exact-rate + error→0 で定義した達成集合は **閉じない**
(単一ユーザ類比 = `[0, C)`: rate = capacity `C` ちょうどでは random-coding exponent `E(C)=0`
ゆえ誤りが消えず `R=C ∉ {MACAchievable}`、境界 Pareto 面は closure でのみ入る)。よって headline
RHS を `macCapacityRegion = closure {MACAchievable}` に置換する。副次効果: **P2 の重い
「生集合の IsClosed」は消滅** — closure は自動で closed、凸性は `Convex.closure` (Mathlib 確認済)
で P1 から自由に持ち上がる (advisor の ~120 LOC → ~40 LOC)。生集合 `{MACAchievable}` を閉包に
包むのは textbook 標準かつ honest (load-bearing predicate 不要)。

### Approach (overall strategy / shape of solution)

time-sharing 領域 = **異なる product input のペンタゴンを跨いだ凸結合を operational に達成する**
論証。難所は「凸包=達成」の凸包側を **符号連結 (block concatenation)** で operational に埋める 1 点
に局所化し、周辺 (閉包 plumbing / 単調性 / 単一ペンタゴン achievability = 既存 corner-point 層)
は再利用する。二段構え:

1. **achievability half (P0–P4)** = `closedConvexHull(⋃ pentagon) ⊆ macCapacityRegion`。
   - **P1 が gateway (唯一の重い operational 核)**: `MACAchievable` の凸性
     `mac_timesharing_concat_achievable`。長さ `n₁` 符号と `n₂` 符号を長さ `n₁+n₂` に連結し、
     各ブロックを独立 decode、誤り ≤ err₁+err₂ (union bound)、`n₁/(n₁+n₂) → lam` を有理近似
     (`MACAchievable` の `∀ε'` slack が近似誤差を吸収するため任意実 lam で成立)。真の template は
     **Mathlib convexHull 補題ではなく in-project の `Measure.pi` split over
     `Fin (n₁+n₂) ≃ Fin n₁ ⊕ Fin n₂`** (単一ユーザ版も存在せず自作)。
   - **P2** = P1 から `Convex {MACAchievable}` (segment 翻訳) → `macCapacityRegion` は
     `Convex.closure` + `isClosed_closure` で Convex かつ Closed (自由)。
   - **P3** = `macPentagon ⊆ macCapacityRegion`。strict 内部は `mac_achievability` 直接、
     境界 Pareto 面 / 軸 (R=0) / 退化ペンタゴン (I=0 で線分・点) は limiting で closure に載せる。
   - **P4** = Mathlib plumbing (`convexHull_min` + `closedConvexHull_eq_closure_convexHull`)。

2. **converse half (CV)** = `{MACAchievable} ⊆ closedConvexHull(⋃ pentagon)`。既存
   `mac_converse` の per-letter **和形** から、各時刻 `i` の周辺入力 `p₁ᵢ ⊗ p₂ᵢ` を露出し、
   達成 rate pair を per-letter ペンタゴン点の (時間平均 = 凸結合) として convex hull に入れる。
   **点 ≤ 平均 ∈ hull** + per-letter marginal `p₁ᵢ⊗p₂ᵢ` 露出 + time-sharing 補助変数
   (Q-augmentation) が核。より難 (~300-500 LOC)。

**critical (honesty、判断ログ #1)**: 「hull = 達成」は operational content を隠さない —
**異なる input のペンタゴン点の凸結合は単一 product input では達成不可** (`mac_achievability`
単独では出ない、load-bearing 確認済)。だから P1 の符号連結が本質で、削除済 tier-5 scaffold
`IsMACTimeSharingHyp` (pentagon の凸結合を hyp で受ける) の再導入は禁止。純凸幾何再定式化
(下記 (β)) を却下する理由もこれ。

### (β) 純凸幾何再定式化の却下 (判断ログ #1、mac-inventory.md:137)

「ペンタゴンの凸包の凸性を Mathlib `convexHull` + corner-point 結果だけから出す」案は不可:
異なる product input `p, p'` のペンタゴン点の凸結合は **単一 product-input ペンタゴンに属さない**
ので、達成領域の凸性が corner-point 層から出ず、必ず load-bearing predicate
(`IsMACTimeSharingHyp` = 削除済 tier-5 defect) を再導入する。→ (α) operational full region
のみが honest target。

### 型クラス設定 (MAC moonshot「事故注意ボックス」verbatim)

```lean
variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
  [Fintype β]  [DecidableEq β]  [Nonempty β]  [MeasurableSpace β]  [MeasurableSingletonClass β]
```

`mac_achievability` は `[IsProbabilityMeasure p₁] [IsProbabilityMeasure p₂] [IsMarkovKernel W]`
+ full-support `hp₁/hp₂/hW` を要求。凸性 P1 も `[IsMarkovKernel W]` を precondition とする
(regularity、load-bearing でない)。

---

## M0 — inventory (Mathlib 凸包資産 + 流用 in-project decl 確認)
**proof-log**: no

- [ ] **Mathlib 凸包資産** (outer assembly のみ、signature verbatim 確認):
  - `convexHull_min : s ⊆ t → Convex 𝕜 t → convexHull 𝕜 s ⊆ t` (`Mathlib/Analysis/Convex/Hull.lean:63`)
  - `segment_subset_convexHull (hx : x∈s)(hy : y∈s) : segment 𝕜 x y ⊆ convexHull 𝕜 s` (`Hull.lean:100`)
  - `closedConvexHull_eq_closure_convexHull : closedConvexHull 𝕜 s = closure (convexHull 𝕜 s)` (`Mathlib/Analysis/Convex/Topology.lean:332`)
  - `convexHull_subset_closedConvexHull` (`Topology.lean:313`)
  - `Convex.closure : Convex 𝕜 s → Convex 𝕜 (closure s)` (Mathlib.Analysis.Convex.Topology、loogle 確認済) + `isClosed_closure` / `IsClosed.closure_eq` / `closure_mono`
  - `convex_iff_segment_subset` / `convex_iff_forall_pos` (P2 で segment 翻訳に使う形を選ぶ)
  - **確認事項**: 直 `closedConvexHull_min` は loogle 0-hit (2026-07-04) → P4 は closure 経由
    (`closedConvexHull_eq_closure_convexHull` + `convexHull_min` + `IsClosed.closure_eq`) で組む。
- [ ] **流用 in-project decl** (signature 不変で consume): `macInfo₁/₂/Both`
  (`Achievability.lean:218/225/232`)、`mac_achievability` (`:1992`)、`MACChannel`/`MACCode`/
  `averageErrorProb` (`Basic.lean`)、`Measure.pi` (`Pi.lean:212`、`irreducible_def` — `pi_pi`
  API 経由)、単一ユーザ `RandomCodebook.lean` の block-law split パターン (P1 連結の参考)。
- [ ] **Mathlib-shape-driven 確認**: `macPentagon` は `macInfo₁/₂/Both` の値 (ℝ) をそのまま
  受ける (textbook `H(...)` 差分直書きを避ける)。凸性 P2 で `Convex ℝ (S : Set (ℝ×ℝ))` を
  出すため `S ⊆ ℝ×ℝ = EuclideanSpace` 相当の型で扱う (`Prod` の `Module ℝ` instance 確認)。
- **撤退**: 定義 Phase、sorry 不要。旧 scaffold `MACTimeSharingBody.lean` は pentagon 凸結合
  幾何のみ genuine (time-sharing 統合は hyp pass-through = 踏襲禁止) = 型の参考にとどめる。

---

## P0 — `MACAchievable` def + `macPentagon` set def + strict-interior wrapper
**proof-log**: no (def + 既存 `mac_achievability` の `∀ε'` 抽象化 plumbing)

**ファイル**: `InformationTheory/Shannon/MultipleAccess/TimeSharing.lean`

- [ ] `def MACAchievable` (上記 signature)。operational primitive、載せる sorry なし。
- [ ] `def macPentagon` (上記) + `def macCapacityRegion W := closure {p | MACAchievable W p.1 p.2}`。
- [ ] 単調性 `mac_achievable_mono : MACAchievable W R₁ R₂ → R₁'≤R₁ → R₂'≤R₂ → 0≤R₁'→0≤R₂'
      → MACAchievable W R₁' R₂'` (低 rate は `⌈exp(n·R₁')⌉ ≤ ⌈exp(n·R₁)⌉ ≤ M₁` で easier、
      down-set 性質。P3 の境界・軸 casework で使う)。
- [ ] **strict-interior wrapper** `mac_strict_interior_achievable`:
      full-support `hp₁ hp₂ hW` + `0<R₁ ∧ 0<R₂ ∧ R₁<macInfo₁ ∧ R₂<macInfo₂ ∧ R₁+R₂<macInfoBoth`
      → `MACAchievable W R₁ R₂`。`mac_achievability` を `ε'` について `∀` 抽象化するだけ (直呼び)。
- **撤退**: `mac_achievability` の hypothesis 形が `MACAchievable` inner block と型不一致なら
  Mathlib-shape-driven 再定義 (CLAUDE.md 第一選択)。`Prop := True` / load-bearing hyp 禁止。

---

## P1 🎯 gateway — `mac_timesharing_concat_achievable` (block 連結による凸性)
**proof-log**: yes (block-Markov 連結 + `Measure.pi` split が本計画の唯一の新規 operational 核、再開根拠必須)

**ファイル**: `TimeSharing.lean`

- [ ] **gateway atom** (最優先 dispatch、gateway-atom-first):
  ```lean
  theorem mac_timesharing_concat_achievable (W) [IsMarkovKernel W]
      {a₁ a₂ b₁ b₂ lam : ℝ} (ha : MACAchievable W a₁ a₂) (hb : MACAchievable W b₁ b₂)
      (hlam : lam ∈ Set.Icc (0:ℝ) 1) :
      MACAchievable W (lam·a₁ + (1-lam)·b₁) (lam·a₂ + (1-lam)·b₂)
  ```
  証明骨格 (operational): 目標 `ε'` に対し (i) `n₁/(n₁+n₂)` が `lam` に十分近い `n₁, n₂` を選ぶ
  (有理近似、`∀ε'` slack が近似誤差吸収)、(ii) `ha`/`hb` から長さ `n₁`/`n₂` 符号を取り、
  `Fin (n₁+n₂) ≃ Fin n₁ ⊕ Fin n₂` で連結符号を構成、(iii) per-block channel 測度を
  `Measure.pi` split で積に分解 (Sum-index measurable equiv)、(iv) 各ブロック独立 decode →
  誤り ≤ err₁ + err₂ < ε' (union bound)、rate は連結で `(n₁ a + n₂ b)/(n₁+n₂) ≈ lam·a+(1-lam)·b`。
  - **まず lean-implementer に本 atom 1 本を dispatch**。通れば achievability half の凸性が確定。
- [ ] 補助: `mac_concat_code` (連結符号構成 + rate 下界) / `measure_pi_sum_split`
  (`Measure.pi (Fin n₁ ⊕ Fin n₂) ≃ Measure.pi (Fin n₁) ×ₘ Measure.pi (Fin n₂)` の block 測度版、
  単一ユーザ `block_law_*_eq_pi` の Sum-index 一般化)。
- **依存 in-project decl**: `MACCode`/`averageErrorProb`/`errorProbAt` (`Basic.lean`)、`Measure.pi`
  (`pi_pi` API); Mathlib `Equiv.sumArrowEquivProdArrow` / `finSumFinEquiv` / `Measure.pi` の
  factorization、`MeasurableEquiv` 群。
- **予想規模**: ~150-300 行 (連結 + `Measure.pi` split + union bound + 有理近似)。**本計画の重心**。
- **撤退ライン (最重要)**: `Fin (n₁+n₂) ≃ Fin n₁ ⊕ Fin n₂` の measure factorization で **3+ turn
  stall したら、その 1 atom `mac_timesharing_concat_achievable` のみ `sorry` +
  `@residual(plan:mac-timesharing-plan)`** (同 slug 再帰)。**`IsMACTimeSharingHyp` /
  `Prop := True` / pentagon 凸結合を受ける load-bearing predicate は禁止** (削除済 tier-5 scaffold
  の再発防止)。regularity hyp (`IsMarkovKernel W` / `0≤lam≤1` / 可測性) は precondition で OK。

---

## P2 — `{MACAchievable}` 凸性 + 容量領域は Closed/Convex 自動
**proof-log**: no (P1 からの segment 翻訳 + closure plumbing、軽量)

**ファイル**: `TimeSharing.lean`

- [ ] `mac_achievable_convex : Convex ℝ {p : ℝ×ℝ | MACAchievable W p.1 p.2}` — P1 を
  `convex_iff_segment_subset` / `convex_iff_forall_pos` 形に翻訳 (`lam·x + (1-lam)·y` の
  成分別が `mac_timesharing_concat_achievable` の結論に一致)。
- [ ] `mac_capacityRegion_convex : Convex ℝ (macCapacityRegion W)` = `Convex.closure` を上に適用。
- [ ] `mac_capacityRegion_isClosed : IsClosed (macCapacityRegion W)` = `isClosed_closure`。
- **注記 (advisor 逸脱)**: advisor の「生 `{MACAchievable}` の `IsClosed` (limiting/diagonal)」は
  **証明不能 (false-as-stated、判断ログ #2)** ゆえ実装しない。closure に包むことで closed/convex が
  自由に出る。
- **撤退**: P1 が sorry の場合 `mac_achievable_convex` も推移的に sorry を継承する
  (`@residual(plan:mac-timesharing-plan)`)。ここ自体は plumbing で独自 sorry を作らない。

---

## P3 — `macPentagon ⊆ macCapacityRegion` (退化/軸/境界 limiting)
**proof-log**: yes (境界・退化・軸 casework の limiting は手数多、再開根拠必須)

**ファイル**: `TimeSharing.lean`

- [ ] `mac_pentagon_interior_achievable`: `macPentagon` の **strict 内部**
  (`0<R₁ ∧ 0<R₂ ∧ R₁<macInfo₁ ∧ R₂<macInfo₂ ∧ R₁+R₂<macInfoBoth`) は
  `mac_strict_interior_achievable` (P0) 直接 → `∈ {MACAchievable} ⊆ macCapacityRegion`。
- [ ] `mac_pentagon_subset_capacityRegion`: `macPentagon p₁ p₂ W ⊆ macCapacityRegion W`。
  境界 Pareto 面 (`R₁=macInfo₁` 等) は strict 内部点の列の極限 → closure。退化 casework:
  - **軸点** (`R₁=0`): `M₁=1 ⇒ ⌈exp(n·0)⌉=1≤M₁` ゆえ user-1 情報なし、`(0,R₂)` は user-2 単一
    ユーザ achievability + `mac_achievable_mono`。**concrete 確認済**: `⌈exp(n·0)⌉=⌈1⌉=1`。
  - **退化ペンタゴン** (`macInfo₁=0` 等で内部空、線分・点に collapse): 内部点列が空でも、
    軸/単一ユーザ achievability + closure で各点を極限として拾う。
  - **非 full-support 境界 input**: `mac_achievability` は full-support `hp₁/hp₂/hW` 要求ゆえ、
    退化 input のペンタゴンは full-support input 列 `pₖ → p` の極限 (`macInfo` 連続性) で closure
    に載せる。
- **依存 in-project decl**: `mac_achievability` (`:1992`)、`mac_strict_interior_achievable` (P0)、
  `mac_achievable_mono` (P0); 単一ユーザ channel achievability (軸点); `macInfo₁/₂/Both` の
  下半連続/連続性 (境界 input limiting、必要なら補題化)。
- **予想規模**: ~150 行。
- **撤退**: 詰まった sub-lemma のみ `sorry` + `@residual(plan:mac-timesharing-plan)`。境界 input
  limiting が `macInfo` 連続性で詰まる場合はその 1 本のみ sorry (壁ではなく plumbing 見込み)。

---

## P4 — achievability headline assemble
**proof-log**: no (Mathlib plumbing)

**ファイル**: `TimeSharing.lean`

- [ ] `mac_timesharing_achievability` (`@[entry_point]`):
  ```lean
  closedConvexHull ℝ (⋃ (p₁) (p₂), macPentagon p₁ p₂ W) ⊆ macCapacityRegion W
  ```
  組立: (i) `⋃ p₁ p₂, macPentagon ⊆ macCapacityRegion` (P3、各 pentagon を union で束ねる)、
  (ii) `convexHull_min` + `mac_capacityRegion_convex` (P2) で
  `convexHull(⋃ pentagon) ⊆ macCapacityRegion`、(iii)
  `closedConvexHull_eq_closure_convexHull` + `mac_capacityRegion_isClosed` (P2) +
  `IsClosed.closure_eq` / `closure_mono` で `closedConvexHull ⊆ macCapacityRegion`。
- **予想規模**: ~60 行。純 Mathlib plumbing、リスク低。
- **撤退**: `closedConvexHull` の API 形が想定と違えば M0 で確認した代替補題に差替。sorry 不要見込み。

---

## CV + V — converse half + full-region antisymmetry → 子サブ計画に委譲
**proof-log**: 子側

converse half `{MACAchievable} ⊆ closedConvexHull(⋃ pentagon)`（CV）+ full-region antisymmetry
headline `macCapacityRegion = closedConvexHull(⋃ pentagon)`（V）は、read-only advisor の精査で
**4 独立重量 gap（code→ambient bridge / 弱 converse 極限 / per-letter 同定 / 平均 pentagon→凸包）**
に分解され、LOC 予測 ~520-880 が親の分離 trigger を超過したため子サブプランに分離した
（判断ログ #4）:

**→ [`mac-timesharing-converse-plan.md`](mac-timesharing-converse-plan.md)**（撤退口
`@residual(plan:mac-timesharing-converse-plan)`）。

要点のみ（詳細は子）: (i) 既存 `mac_converse`（`Converse.lean:830`）は **`dep_consumers` 0** の
floating 文で ambient μ を仮説で取るため、`MACAchievable` から直接開始できず **code→ambient
bridge（Gap 0）が真の起点**。(ii) `mac_converse` 結論に Fano 項が付くため operational rate には
`ε'→0/n→∞` 極限（Gap A）が要る。(iii) 純 ℝ 凸幾何・壁候補の「平均 pentagon→凸包 down-closedness」
（Gap C）を gateway として最初に単独 dispatch。V の antisymmetry は CV + 本 plan の P4
`mac_achievability_region` で `Set.Subset.antisymm`。**honesty trap**: per-letter chain を
load-bearing hyp で受けない（削除済 tier-5 `MACPerLetterChain₁₂` 踏襲禁止）。

---

## ファイル配置

```
InformationTheory/Shannon/MultipleAccess/
  TimeSharing.lean          -- P0–P4: MACAchievable / macPentagon / macCapacityRegion /
                            --        P1 gateway 凸性 / P2 convex+closure / P3 pentagon⊆ / P4 headline
  TimeSharingConverse.lean  -- CV + V: converse half + full-region antisymmetry (TimeSharing import)
```

import 連鎖: 既存 `Achievability` (`mac_achievability`/`macInfo*`) + `Converse` (`mac_converse`)
← `TimeSharing` ← `TimeSharingConverse`。

## 規模見積り / 推奨 leg 数

- achievability half (M0+P0+P1+P2+P3+P4) ≈ **510-660 LOC** (P2 訂正で advisor 案より軽、**達成**)。
- converse half + V (CV + full region) ≈ **520-880 LOC over ≥2 sessions** → 子サブプラン
  [`mac-timesharing-converse-plan.md`](mac-timesharing-converse-plan.md)（4 独立 gap + 推奨 4-5 leg）。
- **本 plan の推奨 leg 数 = 4**（achievability half のみ、同時 1 体まで、CLAUDE.md「Max one parallel agent」）:
  1. M0 + P0 (def + wrapper skeleton)。
  2. **P1 gateway (block 連結凸性)** — 決定打。通れば achievability 凸性確定。
  3. P2 + P3 (凸性翻訳 + pentagon 閉包 limiting)。
  4. P4 + achievability half verify。

---

## 撤退ライン / honesty

撤退口は **`sorry` + `@residual(plan:mac-timesharing-plan)` のみ** (CLAUDE.md「検証の誠実性」)。
最有力撤退点 = **P1 の `Fin (n₁+n₂) ≃ Fin n₁ ⊕ Fin n₂` measure factorization** (3+ turn stall
時にこの 1 atom のみ sorry)。詰まっても gateway atom は analytic 壁ではなく **measure 代数の
plumbing** ゆえ headline は推移的にこの 1 本にのみ依存。

**禁止 (削除済 tier-5 scaffold の再発防止)**: `IsMACTimeSharingHyp` (pentagon 凸結合を hyp で
受ける、`mac-inventory.md:137`) / `Prop := True` slot / per-letter chain を受ける load-bearing
`*Hypothesis` predicate。**regularity hyp は precondition で OK**: `IsMarkovKernel W` /
`IsProbabilityMeasure p₁/p₂` / full-support `hp₁/hp₂/hW` / `0≤lam≤1` / 可測性。

frozen slug: **L-MAC5** (time-sharing 全凸包) = 本計画が genuine closure 対象。旧「scope-out
維持」から「着手・genuine closure 計画」へ (親の L-MAC5 行を本 plan link に同期する = orchestrator
アクション、本 planner は roadmap / 親本文の該当行更新を親 co-stage で反映)。

---

## settled-facts (minimal、再導出可能なものは都度 `rg` / `#print axioms` / loogle)

- **`{MACAchievable}` (exact-rate + error→0) は topologically 閉じない** (confidence
  human-judgment、単一ユーザ類比 `[0,C)` + `E(C)=0`)。境界 Pareto 面は closure でのみ入る →
  headline RHS は `macCapacityRegion = closure {MACAchievable}`。**独立 pivot 再確認推奨** (P2
  着手時に単一ユーザ `{achievable}` の閉性を code で 1 度検算)。
- **異 input pentagon の凸結合点は単一 product input で達成不可** (confidence human-judgment)。
  → P1 符号連結が本質、(β) 純凸幾何再定式化却下、load-bearing predicate 禁止の根拠。
- `Convex.closure` は Mathlib.Analysis.Convex.Topology に存在 (loogle 確認 2026-07-04)。
  直 `closedConvexHull_min` は loogle 0-hit → P4 は closure 経由で組む。
- `mac_achievability` (`:1992`) は full-support `hp₁/hp₂/hW` + `0<R₁,0<R₂` + strict corner を
  要求 (verbatim 確認済) → strict 内部のみ直接、軸/境界/退化は P3 limiting。

(これ以上のキャッシュはしない。`docs/shannon/mac-facts.md` は現時点で作らない。)

---

## 判断ログ

append-only。決着済 entry は削除 (git が履歴)、active のみ残す。≤ 10 entry。

1. **(β) 純凸幾何再定式化を却下 (active、設計軸)**: 異 input pentagon 点の凸結合は単一
   product-input pentagon に属さず、corner-point 層 + Mathlib `convexHull` だけからは達成領域の
   凸性が出ない → 必ず load-bearing predicate (`IsMACTimeSharingHyp` = 削除済 tier-5) を再導入。
   よって **(α) operational full region** のみが honest target、P1 符号連結が凸性を operational に
   埋める本質。`mac-inventory.md:137` 参照。
2. **headline RHS = `closure {MACAchievable}` に訂正 (active、advisor 逸脱)**: advisor 原案は生
   `{MACAchievable}` を RHS に置き P2 で `IsClosed` を証明する計画だったが、exact-rate + error→0 の
   達成集合は **閉じない** (単一ユーザ類比 `[0,C)`、`R=C` は `E(C)=0` で達成不可) ため
   false-as-stated。RHS を `macCapacityRegion = closure {MACAchievable}` (操作的容量領域) に置換。
   副次: P2 の「生集合 IsClosed (limiting/diagonal、~120 LOC)」は消滅、closure が自動 closed +
   `Convex.closure` で P1 から凸性自由 (~40 LOC)。honest かつ軽量化。
3. **achievability 攻略順序 (active)**: P1 gateway atom `mac_timesharing_concat_achievable` を
   **gateway-atom-first で dispatch** → 通れば P2 凸性 + P3 閉包 + P4 plumbing で achievability half
   確定、`Fin (n₁+n₂) ≃ Fin n₁ ⊕ Fin n₂` factorization で 3+ turn stall なら P1 のみ sorry に縮退。
4. **converse half + V を子サブプランに分離済 (active、child-is-SoT)**: advisor 精査で CV が
   4 独立重量 gap（code→ambient bridge / 弱 converse 極限 / per-letter 同定 / 平均 pentagon→凸包）に
   分解され LOC 予測 ~520-880 が分離 trigger 超過 → [`mac-timesharing-converse-plan.md`](mac-timesharing-converse-plan.md)
   に移動（撤退口 `@residual(plan:mac-timesharing-converse-plan)`）。真の起点は Gap 0（`mac_converse`
   が dep_consumers 0 の floating 文ゆえ ambient 構成が要る、親骨格がスキップしていた）。本 plan は
   achievability half（M0–P4）を保持。per-letter chain を load-bearing hyp で受けない
   (`MACPerLetterChain₁₂` = 削除済 bundle 踏襲禁止)。
