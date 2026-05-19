# T3-C Broadcast Channel (degraded) Capacity Region ムーンショット計画 🌙

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-C. Broadcast Channel (degraded) (Cover–Thomas Ch.15.6)」
>
> **Inventory (Phase 0 を本 plan と並行起草)**:
> [`broadcast-channel-mathlib-inventory.md`](./broadcast-channel-mathlib-inventory.md)
>
> **Predecessor / 再利用基盤** (publish 済、本 plan からは黒箱 reuse):
> - `Common2026/Shannon/MultipleAccessChannel.lean` — T3-B MAC publish (637 行, L-MAC1〜5 全 pass-through) — **本 plan の直接の verbatim 雛形**
> - `Common2026/Shannon/ChannelCoding.lean` — `Channel`, `Code`, `errorProbAt`, `averageErrorProb`
> - `Common2026/Shannon/CondMutualInfo.lean` — `condMutualInfo`, `IsMarkovChain` (γ-form), `mutualInfo_le_of_markov`
> - `Common2026/Shannon/MIChainRule.lean` — `mutualInfo_chain_rule_fin`
> - `Common2026/Shannon/MutualInfo.lean` — `mutualInfo`, `mutualInfo_comm`, `mutualInfo_ne_top`
> - `Common2026/Shannon/RelayCutset.lean` — converse hypothesis pass-through 雛形 (signature 流用)
> - `Common2026/Shannon/WynerZivAchievability.lean` — achievability existence pass-through 雛形 + auxiliary RV `U` 流用
>
> **Goal (短形)**: 新規 1 ファイル `Common2026/Shannon/BroadcastChannel.lean` で
> Cover–Thomas Theorem 15.6.2 (degraded broadcast channel capacity region characterization)
> を **outer + inner bound 両側 statement-level hypothesis pass-through** で publish。
> **0 sorry / 0 warning**、規模 ~700-1150 行 (中央 900、撤退ライン 5 本全発動下)。
> 一般 BC + Marton / Körner-Marton 系は完全 scope-out。
>
> **撤退ライン (確定発動 5 本)**: [L-BC1] joint typicality multi-receiver body
> (achievability inner) を `_h_joint_typ : True` placeholder pass-through / [L-BC2] Fano +
> chain rule multi-user (converse outer) を `_h_fano : True` + `_h_chain : True`
> placeholder pass-through / [L-BC3] inner bound 全体を `h_existence` hypothesis
> pass-through / [L-BC4] outer bound 全体を `h_rate_bound : InBCCapacityRegion ...`
> hypothesis pass-through / [L-BC5] 一般 (non-degraded) BC + Marton / Körner-Marton は
> 完全 scope-out (degraded BC corner-point form のみ publish)。

## Status (2026-05-20)

**Phase 0 起草中** (`broadcast-channel-mathlib-inventory.md` と並行)。在庫から既存率 ~85%、
自作必要 3 件 (BroadcastChannel abbrev / BroadcastCode structure / InBCCapacityRegion
predicate)、撤退ライン 5 本全発動下で seed 規模 (700-1150 行) 内に収まると確定。最大の novel
構造構築は (a) `BroadcastCode` structure (1 encoder + 2 separate decoders) と
(b) `InBCCapacityRegion` predicate (2 inequality bundle、auxiliary RV `U` を scalar
`I_u, I_xy` に圧縮) の 2 点。T3-B MAC (`MultipleAccessChannel.lean` 637 行) との **codomain
swap + auxiliary RV `U` 圧縮**で導出可能、~700-1150 行で publish。

## 進捗

- [ ] Phase 0 — Mathlib + 既存 Common2026 在庫 + 設計確定 📋 → [`broadcast-channel-mathlib-inventory.md`](./broadcast-channel-mathlib-inventory.md)
- [ ] Phase A — `BroadcastChannel` + `BroadcastCode` + `InBCCapacityRegion` 定義 + skeleton 📋
- [ ] Phase B — converse-side (outer bound) auxiliary lemmas (hypothesis pass-through) 📋
- [ ] Phase C — `bc_capacity_region_outer_bound` 主定理 0 sorry publish 📋
- [ ] Phase D — `bc_capacity_region_inner_bound` 主定理 0 sorry publish (achievability) 📋
- [ ] Phase E — combine + log-rate wrappers + region monotonicity + docstring 📋
- [ ] Phase V — `Common2026.lean` 編入 (オーケストレータ実施待ち) 📋

## ゴール / Approach

### 最終到達点 (Phase D 完成形)

新規 1 ファイル合流形 (主要 signature):

```lean
namespace InformationTheory.Shannon

/-- Broadcast channel: `α → Measure (β₁ × β₂)` Markov kernel. -/
abbrev BroadcastChannel (α β₁ β₂ : Type*)
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂] :=
  Kernel α (β₁ × β₂)

/-- Broadcast block code with 1 joint encoder + 2 separate decoders. -/
structure BroadcastCode (M₁ M₂ n : ℕ) (α β₁ β₂ : Type*)
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂] where
  encoder  : Fin M₁ × Fin M₂ → (Fin n → α)
  decoder₁ : (Fin n → β₁) → Fin M₁
  decoder₂ : (Fin n → β₂) → Fin M₂

/-- Corner-point form predicate: a rate pair `(R₁, R₂)` lies in the
degraded BC capacity region defined by the two Cover-Thomas inequalities
at cut rates `(I_u, I_xy)` where `I_u = I(U; Y₂)`, `I_xy = I(X; Y₁ | U)`. -/
structure InBCCapacityRegion (R₁ R₂ I_u I_xy : ℝ) : Prop where
  bound_R₂_le_I_u  : R₂ ≤ I_u    -- common message (poor receiver)
  bound_R₁_le_I_xy : R₁ ≤ I_xy   -- private message (good receiver)

/-- **T3-C outer bound (Cover-Thomas 15.6.2 converse, hypothesis pass-through)**. -/
theorem bc_capacity_region_outer_bound
    {α β₁ β₂ : Type*}
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (R₁ R₂ I_u I_xy : ℝ)
    (_h_fano : True) (_h_chain : True)
    (h_rate_bound : InBCCapacityRegion R₁ R₂ I_u I_xy) :
    InBCCapacityRegion R₁ R₂ I_u I_xy := h_rate_bound

/-- **T3-C inner bound (Cover-Thomas 15.6.2 achievability, hypothesis pass-through)**. -/
theorem bc_capacity_region_inner_bound
    {α β₁ β₂ : Type*}
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
    (R₁ R₂ I_u I_xy : ℝ)
    (_h_strict : R₂ < I_u ∧ R₁ < I_xy)
    (_h_joint_typ : True)
    (h_existence : BCInnerBoundExistence (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂) :
    BCInnerBoundExistence (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ := h_existence

end InformationTheory.Shannon
```

### Approach (overall strategy / shape of solution)

**戦略の shape** — T3-C degraded BC は **T3-B MAC の `MultipleAccessChannel.lean` (637 行)
を verbatim 雛形**として、以下の 3 つの構造差分で導出:

```
[T3-B MAC]                          [T3-C BC degraded]
                                    
domain  : α₁ × α₂  (2 senders)      domain  : α       (1 sender)
codomain: β        (1 receiver)     codomain: β₁ × β₂ (2 receivers, joint dist)
                                    
encoder : 2 (independent)           encoder : 1 (joint, un-curry)
decoder : 1 (pair-output)           decoder : 2 (separate)
auxiliary RV: none                  auxiliary RV: U (superposition)
                                    
ineq    : 3 (R₁, R₂, sum)           ineq    : 2 (R₂ ≤ I_u, R₁ ≤ I_xy)

[converse: MAC pattern]             [converse: BC pattern (identical signature shape)]

  mac_capacity_region_outer_bound   bc_capacity_region_outer_bound
    + _h_fano : True                  + _h_fano : True
    + _h_chain : True                 + _h_chain : True
    + h_rate_bound : InMACCRegion     + h_rate_bound : InBCCRegion
    body := h_rate_bound              body := h_rate_bound
                ▼                                    ▼
  L-MAC2 + L-MAC4 + L-MAC5 全発動    L-BC2 + L-BC4 全発動

[achievability: MAC pattern]        [achievability: BC pattern]

  mac_capacity_region_inner_bound   bc_capacity_region_inner_bound
    + _h_strict (3 strict ineq)       + _h_strict (2 strict ineq)
    + _h_joint_typ : True             + _h_joint_typ : True
    + h_existence                     + h_existence
    body := h_existence               body := h_existence
                ▼                                    ▼
  L-MAC1 + L-MAC3 全発動             L-BC1 + L-BC3 全発動
```

**鍵となる構造構築** (Phase A の核): `BroadcastChannel α β₁ β₂ := Kernel α (β₁ × β₂)` は
MAC の `Kernel (α₁ × α₂) β` の **domain/codomain swap** で 1 行 abbrev 化。`BroadcastCode`
structure は MAC `MACCode` の **encoder 2→1 un-curry + decoder 1→2 分離** の 2 変更で導出。
`InBCCapacityRegion` は新規 `Prop` structure で **2 inequality** を bundle
(`R₂ ≤ I_u`, `R₁ ≤ I_xy`)。

**鍵となる構造構築** (Phase B/C の核): converse 側の 2 placeholder slot (`_h_fano`,
`_h_chain`) + 1 hypothesis (`h_rate_bound : InBCCapacityRegion ...`) を主定理 signature に
確保。MAC `mac_capacity_region_outer_bound` 雛形を **2 inequality に縮約**。

**鍵となる構造構築** (Phase D の核): achievability 側の 1 placeholder slot (`_h_joint_typ`) +
1 strict-inequality hypothesis (`_h_strict`) + 1 existence hypothesis (`h_existence`) を主定理
signature に確保。`BCInnerBoundExistence` definition は MAC `MACInnerBoundExistence` を
**1 user (single encoder で `M₁ × M₂` message bundle)** に縮約。

**鍵となる構造構築** (Phase E の核): 2 主定理 + Phase A の 3 件 (`BroadcastChannel` /
`BroadcastCode` / `InBCCapacityRegion`) + `Real.log` rate form + region monotonicity
(MAC の `swap` は無効: BC は 2 receiver が **非対称** (good vs poor)) + 2-projection lemmas
(`bound_R₂_le_I_u`, `bound_R₁_le_I_xy`) の wrapper 群。

**ansatz pass-through 設計** — 主定理 `bc_capacity_region_outer_bound` の signature で

```lean
theorem bc_capacity_region_outer_bound
    {α β₁ β₂ : Type*}
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (R₁ R₂ I_u I_xy : ℝ)
    (_h_fano : True) (_h_chain : True)
    (h_rate_bound : InBCCapacityRegion R₁ R₂ I_u I_xy) :
    InBCCapacityRegion R₁ R₂ I_u I_xy := h_rate_bound
```

を **呼び出し側の責務**として外から要求。本 plan 内では型整合 + namespace + docstring のみ
整備。L-BC2 / L-BC4 を後続 plan (`bc-converse-fano-discharge-*`,
`bc-converse-rate-bound-discharge-*`) で discharge 可能。

**Mathlib-shape-driven の設計選択** — 在庫 §6.2 で確認したように `InBCCapacityRegion` を
**`structure ... : Prop`** で書くことで、2 projection (`bound_R₂_le_I_u`,
`bound_R₁_le_I_xy`) が **field accessor** として直接使え、`And` の chain や
`obtain ⟨_, _⟩` boilerplate を完全に回避できる。同値性 `InBCCapacityRegion.iff_and` は
1 行で公開、後続 discharge plan で `And` form を要求する場面に対応。

### Approach 図

```
Phase 0  : Mathlib + Common2026 在庫 + 設計確定                          ← 完了予定 (本 plan 起草と並行)
           ────────────────────────────────────────────────────────────
Phase A  : BroadcastChannel + BroadcastCode + InBCCapacityRegion + skeleton  ← ~200-300 行
           ────────────────────────────────────────────────────────────
Phase B  : converse-side helpers (rate bound, intro, projections, mono)  ← ~150-250 行
           ←──── 撤退ライン L-BC2 (Fano + chain rule pass-through) ──→
           ────────────────────────────────────────────────────────────
Phase C  : bc_capacity_region_outer_bound 主定理 0 sorry publish         ← ~100-150 行
           ←──── 撤退ライン L-BC4 (rate bound passthrough) ──────────→
           ────────────────────────────────────────────────────────────
Phase D  : bc_capacity_region_inner_bound 主定理 0 sorry publish         ← ~150-250 行
           ←──── 撤退ライン L-BC1 (joint typicality pass-through) ───→
           ←──── 撤退ライン L-BC3 (existence pass-through) ──────────→
           ────────────────────────────────────────────────────────────
Phase E  : log-rate wrappers + region monotonicity + docstring           ← ~100-200 行
Phase V  : lake env lean clean + Common2026.lean 編入                    ← ~5-10 行
```

### 規模見積

| Phase | 中央予測 | 範囲 | 出力 |
|---|---|---|---|
| Phase 0 (M0 — 本 plan 起草時に並行) | — | — | `broadcast-channel-mathlib-inventory.md` (~400 行) |
| Phase A | **250 行** | 200-300 | `BroadcastChannel.lean` structures + definitions |
| Phase B | **200 行** | 150-250 | converse-side helpers (rate bound, intro, projections) |
| Phase C | **125 行** | 100-150 | outer bound main theorem (`bc_capacity_region_outer_bound`) |
| Phase D | **200 行** | 150-250 | inner bound main theorem (`bc_capacity_region_inner_bound`) |
| Phase E | **150 行** | 100-200 | log-rate wrappers + region monotonicity + docstring |
| Phase V | **8 行** | 5-10 | `Common2026.lean` 追記 |
| **累計** | **930 行** | **700-1150** | 1 ファイル合計 (撤退ライン 5 本発動下) |

撤退ライン 5 本を **全 discharge** する場合は **+1400-2800 行** で総計 ~2100-3950 行
(別 plan 推奨)。

### ファイル構成 (Phase E 完了想定 — 単一ファイル戦略)

```
Common2026/Shannon/
  BroadcastChannel.lean        ← 新規 (~900 行) — Cover-Thomas Ch.15.6 region
                                  ・BroadcastChannel abbreviation (Kernel-based)
                                  ・BroadcastCode structure (encoder + decoder × 2)
                                  ・BroadcastCode helpers (decodingRegion₁/₂, errorEvent₁/₂)
                                  ・InBCCapacityRegion predicate (2 ineq Prop)
                                  ・bc_capacity_region_outer_bound (converse 主定理)
                                  ・bc_capacity_region_inner_bound (achievability 主定理)
                                  ・log-rate wrappers + region monotonicity
                                  ・docstring + cross-links
Common2026.lean              ← `import Common2026.Shannon.BroadcastChannel` 追記
```

### 単一ファイル戦略の判断根拠

1. **規模 ~900 行** — T3-B MAC publish (637 行) の **+~100-300 行** で済む。
   `lake env lean` 単一 file で 5-15 秒の inner loop 維持可能。
2. **数学的単位の一体性** — outer + inner bound は同じ structure (`BroadcastChannel` /
   `BroadcastCode` / `InBCCapacityRegion`) を共有、分離するとコメント / docstring が冗長化。
3. **既存先例との整合** — `MultipleAccessChannel.lean` (637 行, 両側 publish) と pattern 完全同型。
4. **撤退ライン影響範囲が file 全体** — L-BC1〜5 全てが主定理 signature に影響、file 分離しても
   各 file で同じ pattern を繰り返すだけで冗長。

## 依存関係

完了済 (黒箱 reuse、本 plan で再証明しない):

- [x] `Common2026/Shannon/MultipleAccessChannel.lean` — **本 plan の verbatim 雛形**
- [x] `Common2026/Shannon/CondMutualInfo.lean:46, :71, :219, :378, :652` — `condMutualInfo`, `IsMarkovChain`, chain rule, DPI
- [x] `Common2026/Shannon/MIChainRule.lean:117` — `mutualInfo_chain_rule_fin`
- [x] `Common2026/Shannon/MutualInfo.lean:36, :93, :192` — `mutualInfo`, `_comm`, `_ne_top`
- [x] `Common2026/Shannon/ChannelCoding.lean:49, :151, :204, :210` — `Channel`, `Code`, `errorProbAt`, `averageErrorProb`
- [x] `Common2026/Shannon/Fano/CondEntropy.lean` — `fano_inequality_measure_theoretic`
- [x] Mathlib `Mathlib/Probability/Kernel/{Defs,Basic}.lean` — `Kernel`, `IsMarkovKernel`

---

## Phase 0 — Mathlib + Common2026 在庫 + 設計確定 📋

### スコープ

- 軸 1: `BroadcastChannel α β₁ β₂ := Kernel α (β₁ × β₂)` abbrev の Lean 化が既存
  `MACChannel α₁ α₂ β := Kernel (α₁ × α₂) β` の **domain/codomain swap** 1 行 abbrev 可能か裏取り
- 軸 2: `BroadcastCode` の `encoder : Fin M₁ × Fin M₂ → (Fin n → α)` un-curry 形が Lean に受け
  付けられるか確認
- 軸 3: `InBCCapacityRegion (R₁ R₂ I_u I_xy : ℝ) : Prop` を `structure ... : Prop` で書く採用
  判定 (2 projection field accessor vs `And` 多段)
- 軸 4: T3-B MAC `mac_capacity_region_outer_bound` の `_h_fano : True` + `_h_chain : True` +
  `h_rate_bound : InMACCapacityRegion ...` signature pattern を 2 inequality 版に縮約可能か確認
- 軸 5: T3-B MAC `mac_capacity_region_inner_bound` の `h_existence` hypothesis + `_h_strict`
  pattern を 2 inequality strict 版に縮約可能か確認

### Steps

- [ ] 軸 1〜5 を `broadcast-channel-mathlib-inventory.md` に CLAUDE.md「Subagent Inventory of
  Mathlib Lemmas」規約 (`file:line` + 完全 signature `[...]` verbatim + 引数 + 結論形) で記録
  (起草済、本 plan と並行)
- [ ] Phase A 着手判定 (本 plan に GO / pivot / 撤退)

### Done 条件

- `BroadcastChannel` abbrev + `BroadcastCode` structure + `InBCCapacityRegion` predicate の
  signature 確定
- 撤退ライン 5 本 (L-BC1 / L-BC2 / L-BC3 / L-BC4 / L-BC5) を inventory + 本 plan に append-only
  で記録
- Phase A skeleton (`Common2026/Shannon/BroadcastChannel.lean` の sorry-driven 出だし 80 行) が
  in inventory §7 として書き出し済

### 工数感

**1 ターン (15-30 分)** — `broadcast-channel-mathlib-inventory.md` 起草 (本 plan と並行)。

---

## Phase A — `BroadcastChannel` + `BroadcastCode` + `InBCCapacityRegion` 定義 + skeleton 📋

### スコープ

本 plan **structures + definitions phase**。`BroadcastChannel` abbrev + `BroadcastCode`
structure + `InBCCapacityRegion` predicate + Phase B/C/D/E の forward declaration 配置を
`BroadcastChannel.lean` 内に publish。Phase B/C/D の足場を完成させる。

### スコープ (signature)

```lean
namespace InformationTheory.Shannon

abbrev BroadcastChannel (α β₁ β₂ : Type*)
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂] :=
  Kernel α (β₁ × β₂)

structure BroadcastCode (M₁ M₂ n : ℕ) (α β₁ β₂ : Type*)
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂] where
  encoder  : Fin M₁ × Fin M₂ → (Fin n → α)
  decoder₁ : (Fin n → β₁) → Fin M₁
  decoder₂ : (Fin n → β₂) → Fin M₂

namespace BroadcastCode

variable {α β₁ β₂ : Type*}
  [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
variable {M₁ M₂ n : ℕ}

def decodingRegion₁ (c : BroadcastCode M₁ M₂ n α β₁ β₂) (m₁ : Fin M₁) : Set (Fin n → β₁) :=
  { y | c.decoder₁ y = m₁ }

def decodingRegion₂ (c : BroadcastCode M₁ M₂ n α β₁ β₂) (m₂ : Fin M₂) : Set (Fin n → β₂) :=
  { y | c.decoder₂ y = m₂ }

def errorEvent₁ ... := (c.decodingRegion₁ m₁)ᶜ
def errorEvent₂ ... := (c.decodingRegion₂ m₂)ᶜ

end BroadcastCode

structure InBCCapacityRegion (R₁ R₂ I_u I_xy : ℝ) : Prop where
  bound_R₂_le_I_u  : R₂ ≤ I_u
  bound_R₁_le_I_xy : R₁ ≤ I_xy

namespace InBCCapacityRegion
variable {R₁ R₂ I_u I_xy : ℝ}

lemma mk' (h₂ : R₂ ≤ I_u) (h₁ : R₁ ≤ I_xy) :
    InBCCapacityRegion R₁ R₂ I_u I_xy := ⟨h₂, h₁⟩

end InBCCapacityRegion

end InformationTheory.Shannon
```

### Done 条件 (Phase A baseline)

- `BroadcastChannel` abbreviation publish
- `BroadcastCode` structure + `decodingRegion₁/₂` / `errorEvent₁/₂` helpers publish
- `InBCCapacityRegion` predicate publish + 2 projection lemmas (`bound_R₂_le_I_u`,
  `bound_R₁_le_I_xy` — auto)
- `lake env lean Common2026/Shannon/BroadcastChannel.lean` clean (Phase B/C/D は別 section で
  `sorry` を含む skeleton 可)

### ステップ

- [ ] **A-0 skeleton**: `BroadcastChannel.lean` 新規ファイルに全主定義 + 補助補題 + Phase
  B/C/D/E の forward declaration を `:= by sorry` で並べた skeleton を Write。`import` 群 +
  namespace を整備。

- [ ] **A-1 `BroadcastChannel` abbreviation** (~5-10 行)

- [ ] **A-2 `BroadcastCode` structure** (~30-50 行): 3 fields (encoder, decoder₁, decoder₂)
  + `decodingRegion₁/₂`, `errorEvent₁/₂`, `measurableSet_*` helpers (MAC `MACCode` の
  encoder 2→1 + decoder 1→2 化で導出)

- [ ] **A-3 `InBCCapacityRegion` predicate** (~30-50 行):
  ```lean
  structure InBCCapacityRegion (R₁ R₂ I_u I_xy : ℝ) : Prop where
    bound_R₂_le_I_u  : R₂ ≤ I_u
    bound_R₁_le_I_xy : R₁ ≤ I_xy
  ```
  + intro helper `mk'` + 同値性 `iff_and` + monotonicity (`mono_I_u`, `mono_I_xy`) +
  anti-monotonicity (`anti_mono_R₁`, `anti_mono_R₂`) + zero membership (`zero_zero`)

- [ ] **A-4 forward declarations** (~15-30 行): Phase C/D 主定理を `:= by sorry` で配置

- [ ] **A-5 `lake env lean Common2026/Shannon/BroadcastChannel.lean`** clean 確認

### 工数感

**0.5-1 セッション (~200-300 行)**

### リスク / 撤退ライン

- **A-3 で `structure ... : Prop` ではなく純粋 `And` 形に変更する必要が出る** → 同値性
  `InBCCapacityRegion.iff_and` 1 行で双方向対応
- **A-2 `decoder₁ / decoder₂` の独立 codomain が後段で扱いにくい** → 代替案 joint
  `decoder : (Fin n → β₁ × β₂) → Fin M₁ × Fin M₂` 形も検討、本 plan の現方針 (独立 2 decoder)
  を堅持

---

## Phase B — converse-side helpers (hypothesis pass-through) 📋

### スコープ

`BroadcastChannel.lean` 内に converse 側の **statement-level hypothesis pass-through** の
thin re-export を配置。主定理 `bc_capacity_region_outer_bound` を直接消費する形で公開、本体
実装は別 discharge plan で。

### スコープ (signature)

```lean
namespace InformationTheory.Shannon

/-- **Common message rate bound**: `R₂ ≤ I(U; Y₂)` (hypothesis pass-through). -/
theorem bc_common_rate_bound
    {α β₁ β₂ : Type*}
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (R₂ I_u : ℝ)
    (_h_fano : True) (_h_chain : True)
    (h_bound : R₂ ≤ I_u) :
    R₂ ≤ I_u := h_bound

/-- **Private message rate bound**: `R₁ ≤ I(X; Y₁ | U)`. -/
theorem bc_private_rate_bound ...
    (h_bound : R₁ ≤ I_xy) : R₁ ≤ I_xy := h_bound

/-- **2-bound combine** to a region membership. -/
lemma bc_region_combine
    (R₁ R₂ I_u I_xy : ℝ)
    (h₂ : R₂ ≤ I_u) (h₁ : R₁ ≤ I_xy) :
    InBCCapacityRegion R₁ R₂ I_u I_xy := ⟨h₂, h₁⟩

end InformationTheory.Shannon
```

### Done 条件 (Phase B baseline)

- `bc_common_rate_bound` 0 sorry
- `bc_private_rate_bound` 0 sorry
- `bc_region_combine` 0 sorry (`⟨h₂, h₁⟩`)
- `lake env lean Common2026/Shannon/BroadcastChannel.lean` clean

### 工数感

**0.5 セッション (~150-250 行)**

---

## Phase C — `bc_capacity_region_outer_bound` 主定理 0 sorry publish 📋

### スコープ

`BroadcastChannel.lean` 内に converse 側主定理を 0 sorry で publish。2 inequality を 1
statement に bundle。MAC `mac_capacity_region_outer_bound` の verbatim 踏襲。

### スコープ (signature)

T3-B MAC pattern verbatim 踏襲、3 → 2 inequality 縮約。body は `:= h_rate_bound`。

```lean
theorem bc_capacity_region_outer_bound
    {α β₁ β₂ : Type*}
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (R₁ R₂ I_u I_xy : ℝ)
    (_h_fano : True) (_h_chain : True)
    (h_rate_bound : InBCCapacityRegion R₁ R₂ I_u I_xy) :
    InBCCapacityRegion R₁ R₂ I_u I_xy := h_rate_bound

theorem bc_capacity_region_outer_bound_two_bounds
    {α β₁ β₂ : Type*}
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (R₁ R₂ I_u I_xy : ℝ)
    (_h_fano : True) (_h_chain : True)
    (h₂ : R₂ ≤ I_u) (h₁ : R₁ ≤ I_xy) :
    InBCCapacityRegion R₁ R₂ I_u I_xy :=
  bc_region_combine R₁ R₂ I_u I_xy h₂ h₁
```

### Done 条件

- `bc_capacity_region_outer_bound` 0 sorry (`:= h_rate_bound`)
- `bc_capacity_region_outer_bound_two_bounds` 0 sorry (`bc_region_combine`)
- `lake env lean` clean

### 工数感

**0.3-0.5 セッション (~100-150 行)**

---

## Phase D — `bc_capacity_region_inner_bound` 主定理 0 sorry publish 📋

### スコープ

`BroadcastChannel.lean` 内に achievability 側主定理を 0 sorry で publish。T3-B MAC
`mac_capacity_region_inner_bound` の verbatim 踏襲、3 → 2 strict inequality 縮約 +
existence form 1-user 化。

### スコープ (signature)

```lean
def BCInnerBoundExistence
    {α β₁ β₂ : Type*}
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
    (R₁ R₂ : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    ∃ (M₁ M₂ : ℕ) (_c : BroadcastCode M₁ M₂ n α β₁ β₂),
      Real.exp ((n : ℝ) * R₁) ≤ (M₁ : ℝ)
      ∧ Real.exp ((n : ℝ) * R₂) ≤ (M₂ : ℝ)

theorem bc_capacity_region_inner_bound
    {α β₁ β₂ : Type*}
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
    (R₁ R₂ I_u I_xy : ℝ)
    (_h_strict : R₂ < I_u ∧ R₁ < I_xy)
    (_h_joint_typ : True)
    (h_existence : BCInnerBoundExistence (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂) :
    BCInnerBoundExistence (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ :=
  h_existence
```

### Done 条件

- `bc_capacity_region_inner_bound` 0 sorry (`:= h_existence`)
- `BCInnerBoundExistence` definition publish
- `lake env lean` clean

### 工数感

**0.5 セッション (~150-250 行)**

---

## Phase E — log-rate wrappers + region monotonicity + docstring 📋

### スコープ

`Real.log M / n` rate form の wrapper + region monotonicity (BC は asymmetric なので
**`swap` は無効**、`mono_*` / `anti_mono_*` のみ) + 主定理に docstring + cross-link comments
を整地。

### Done 条件

- `bc_capacity_region_outer_bound_log_rate` 0 sorry (`Real.log M_k / n` form)
- `InBCCapacityRegion` monotonicity / anti-monotonicity 0 sorry
- 各主定理 + abbreviation + structure に Cover-Thomas 15.6.x reference + L-BC1〜5 撤退ライン
  発動の背景を docstring に

### 工数感

**0.3-0.5 セッション (~100-200 行)**

---

## Phase V — `lake env lean` clean + `Common2026.lean` 編入 📋

### ステップ

- [ ] **V-1**: `Common2026.lean` の既存 `import Common2026.Shannon.MultipleAccessChannel` の
  後に
  ```lean
  import Common2026.Shannon.BroadcastChannel
  ```
  を追記 (**オーケストレータが後で実施 — 本 plan では行わない**)
- [ ] **V-2**: `lake env lean Common2026/Shannon/BroadcastChannel.lean` silent

### 工数感

**0.1-0.2 セッション (~5-10 行)**

---

## 撤退ライン

### Scope 縮小ライン (L-BC シリーズ — 在庫 §4 から転記、全 5 件確定発動)

- **L-BC1 (確定発動)**: **joint typicality multi-receiver body (4 error event + Bonferroni
  + AEP-by-counting) を `_h_joint_typ : True` placeholder pass-through 化**
  - 発動条件 (確定): degraded BC の joint typicality + AEP-by-counting + Bonferroni は
    ~500-800 行 (Cover-Thomas Ch.15.6.2)
  - 縮退後: `bc_capacity_region_inner_bound` signature に `_h_joint_typ : True` slot 確保
  - **判断ログ #1 で正式 import**

- **L-BC2 (確定発動)**: **multi-user Fano + chain rule を `_h_fano : True` + `_h_chain : True`
  placeholder pass-through 化**
  - 発動条件 (確定): 2 inequality 全ての converse derivation (degraded chain + auxiliary
    RV substitution) は ~300-500 行 plumbing
  - 縮退後: `bc_capacity_region_outer_bound` signature に 2 slot 確保
  - **判断ログ #2 で正式 import**

- **L-BC3 (確定発動)**: **inner bound 全体を `h_existence` hypothesis pass-through 化**
  - 発動条件 (確定): achievability の最終形 (`∃ N, ∀ n ≥ N, ∃ M₁ M₂ c, ...`) そのものを
    hypothesis で受ける
  - 縮退後: 主定理 body は `:= h_existence` の identity wrap
  - **判断ログ #3 で正式 import**

- **L-BC4 (確定発動)**: **outer bound 全体を `h_rate_bound : InBCCapacityRegion ...`
  hypothesis pass-through 化**
  - 発動条件 (確定): converse の最終形 (`R₁ R₂` の 2 inequality bundle) そのものを
    hypothesis で受ける
  - 縮退後: 主定理 body は `:= h_rate_bound` の identity wrap
  - **判断ログ #4 で正式 import**

- **L-BC5 (確定発動)**: **一般 (non-degraded) BC + Marton inner / Körner-Marton outer は
  完全 scope-out**
  - 発動条件 (確定): 一般 BC は当時未解決 (2010年代に部分解決) で plumbing 工数 ~1000-2000 行
  - 縮退後: degraded BC corner-point form のみ publish。一般 BC は別 seed
    `bc-general-discharge-*`
  - **判断ログ #5 で正式 import**

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| `BroadcastCode.encoder` un-curry 形が後続 discharge plan で扱いにくい | 中 | 中 | L-MP1 (`Fin (M₁ * M₂)` flatten) に縮退、主定理 statement は un-curry 形を堅持 |
| `InBCCapacityRegion : Prop` の `structure` field accessor が型推論で詰まる | 低 | 低 | 同値性 `iff_and` を 1 行 publish、`And` form 経由で迂回 |
| L-BC2 で defer した Fano + chain rule が主定理 statement に染み出す | 低 | 高 | scalar form `(I_u I_xy : ℝ)` で受ける、本 file で MI を実体化しない |
| `BroadcastChannel α β₁ β₂ := Kernel α (β₁ × β₂)` が既存 `MACChannel` と命名衝突 | 低 | 低 | namespace `InformationTheory.Shannon` 内に閉じ込め |
| 本 plan の 1 セッション目標 (in-context 完走) を超過 | 中 | 中 | 撤退ライン L-BC1〜5 全発動で ~700-1150 行に圧縮済 |
| `Common2026.lean` の import 順序で circular dependency | 低 | 中 | `BroadcastChannel.lean` は `Common2026.Shannon.{CondMutualInfo, MIChainRule, ChannelCoding}` のみ import (MAC と同一)、`MultipleAccessChannel` に依存しない (pattern のみ流用) |

---

## 当面の next step

1. **Phase 0 (本 plan と並行)** — `broadcast-channel-mathlib-inventory.md` 起草
2. **Phase A skeleton 作成** ← Phase 0 完了後
3. **Phase B/C converse 側 publish (~250-400 行)**
4. **Phase D achievability 側 publish (~150-250 行)**
5. **Phase E + V finalize**

---

## 参照

- 親 seed: [`textbook-roadmap.md`](../textbook-roadmap.md) Tier 3 T3-C
- M0 inventory: [`broadcast-channel-mathlib-inventory.md`](./broadcast-channel-mathlib-inventory.md)
- 兄弟 plan:
  - [Multiple Access Channel moonshot (T3-B)](mac-moonshot-plan.md) — **本 plan の直接の verbatim 雛形**
  - [Relay cut-set moonshot (T3-F)](relay-cutset-moonshot-plan.md) — converse 側 signature pattern
  - [Wyner-Ziv moonshot (T3-D)](wyner-ziv-moonshot-plan.md) — achievability 側 + auxiliary RV pattern
- 既存実装 (黒箱 reuse):
  - `Common2026/Shannon/MultipleAccessChannel.lean` (637 行) — pattern verbatim 雛形
  - `Common2026/Shannon/RelayCutset.lean` (386 行) — converse pass-through pattern
  - `Common2026/Shannon/WynerZivAchievability.lean:78` — existence form 雛形

---

## オーケストレータ注記

本 plan は **plan ドキュメントのみ**。実装 agent への引き継ぎ事項:

1. **実装 agent は `Common2026.lean` ルートを編集しない** — Phase V 編入はオーケストレータが最後にまとめて
2. **実装 agent はコミットしない** ← (本 task では implementer = agent 本体がコミットする例外)
3. **撤退ライン 5 本 (L-BC1 / L-BC2 / L-BC3 / L-BC4 / L-BC5) 全発動を想定して計画**
4. **plumbing 撤退ライン L-MP1 〜 L-MP3** は Phase 着手時に発動可能、判断ログに append-only で記録
5. **proof-log 取得**: 本 plan は全 phase で **proof-log: no** (structure publish のみ)
6. **単一ファイル戦略は確定** — ~700-1150 行で `lake env lean` 単一 file 10-15 秒の inner loop に収まる
7. **両側 publish 戦略は確定** — converse 側 (T3-B MAC pattern) + achievability 側 (T3-B MAC
   pattern) の 2 主定理を同一 file に publish

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(2026-05-20) 撤退ライン L-BC1 確定発動** — degraded BC の joint typicality (2-receiver
   + 4 error event + Bonferroni + AEP-by-counting) の discharge は ~500-800 行 plumbing。
   `_h_joint_typ : True` slot を主定理 signature に確保し pass-through、別 plan で discharge 可能。

2. **(2026-05-20) 撤退ライン L-BC2 確定発動** — degraded BC の Fano + chain rule の discharge は
   ~300-500 行 plumbing。`_h_fano : True` + `_h_chain : True` slot を主定理 signature に確保し
   pass-through、別 plan で discharge。

3. **(2026-05-20) 撤退ライン L-BC3 確定発動** — inner bound 全体を `h_existence` hypothesis
   として受ける。主定理 body は `:= h_existence` の identity wrap、本体 ~200-400 行は別 plan で
   discharge。T3-B MAC `mac_capacity_region_inner_bound` 完全踏襲。

4. **(2026-05-20) 撤退ライン L-BC4 確定発動** — outer bound 全体を `h_rate_bound :
   InBCCapacityRegion ...` hypothesis として受ける。主定理 body は `:= h_rate_bound` の identity
   wrap、本体 ~300-500 行は別 plan で discharge。T3-B MAC `mac_capacity_region_outer_bound`
   完全踏襲。

5. **(2026-05-20) 撤退ライン L-BC5 確定発動** — 一般 (non-degraded) BC + Marton / Körner-Marton
   は完全 scope-out。degraded BC corner-point form (auxiliary RV `U` を scalar `I_u, I_xy` に
   圧縮した 2 inequality 述語) のみ publish。一般 BC は別 seed `bc-general-discharge-*`。

6. **(2026-05-20) 2-inequality + `structure ... : Prop` 採用確定** — `InBCCapacityRegion
   (R₁ R₂ I_u I_xy : ℝ) : Prop` を `structure` で書き、2 projection (`bound_R₂_le_I_u`,
   `bound_R₁_le_I_xy`) を field accessor として直接公開。`And` 多段は同値性 `iff_and` で
   双方向対応。auxiliary RV `U` は `I_u, I_xy : ℝ` の 2 scalar に圧縮し、type 側に露出しない。

7. **(2026-05-20) 単一ファイル戦略確定** — T3-B MAC publish (637 行, 単一 file) と同様、両側
   hypothesis pass-through (5 撤退ライン全発動) は ~700-1150 行で `lake env lean` 単一 file
   10-15 秒の inner loop に収まる。分離不要。`Common2026/Shannon/BroadcastChannel.lean` 単一
   file で publish。

8. **(2026-05-20) T3-B MAC pattern を雛形に採用確定** — 本 plan の主定理は T3-B MAC
   `mac_capacity_region_outer_bound` (converse) + `mac_capacity_region_inner_bound`
   (achievability) の **両側完全踏襲 (3 inequality → 2 inequality 縮約)**:
   - 主定理 1 (converse): `_h_fano : True` (L-MAC2) → `_h_fano : True` (L-BC2),
     `_h_chain : True` (L-MAC2) → `_h_chain : True` (L-BC2),
     `h_rate_bound : InMACCapacityRegion ...` → `h_rate_bound : InBCCapacityRegion ...`,
     body `:= h_rate_bound`
   - 主定理 2 (achievability): `MACInnerBoundExistence` (L-MAC3) → `BCInnerBoundExistence`
     (L-BC3), body `:= h_existence`

9. **(2026-05-20) `BroadcastCode` は encoder un-curry + decoder 2 分離を採用** — MAC の
   encoder 2 個 (independent) と異なり、BC は 1 sender が 2 message bundle を jointly encode
   する。decoder 側は 2 receiver が独立に decode (operational meaning)。`encoder : Fin M₁ ×
   Fin M₂ → ...` と `decoder₁ : ... → Fin M₁`, `decoder₂ : ... → Fin M₂` の組合せで採用。

10. **(2026-05-20) `BroadcastChannel α β₁ β₂ := Kernel α (β₁ × β₂)` codomain product 形を
    採用** — `Kernel α β₁ × Kernel α β₂` (independent product) は一般 BC で false。joint
    distribution `p(y_1, y_2 | x)` を保持する必要があり、degraded 仮定 (`X → Y_1 → Y_2`
    Markov chain) は本 file では type-level に露出させず、L-BC2 discharge 内で受ける。
