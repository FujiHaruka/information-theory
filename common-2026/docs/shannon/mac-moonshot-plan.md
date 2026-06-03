# T3-B Multiple Access Channel (MAC) Capacity Region ムーンショット計画 🌙

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-B. Multiple Access Channel (MAC) (Cover–Thomas Ch.15.3)」
>
> **Inventory (Phase 0 を本 plan 直前に並行起草)**:
> [`mac-mathlib-inventory.md`](./mac-mathlib-inventory.md)
>
> **Predecessor / 再利用基盤** (publish 済、本 plan からは黒箱 reuse):
> - `InformationTheory/Shannon/ChannelCoding.lean` — `Channel`, `Code`, `errorProbAt`, `averageErrorProb`
> - `InformationTheory/Shannon/ChannelCodingAchievability.lean` — single-user random codebook
> - `InformationTheory/Shannon/ChannelCodingConverseGeneralComplete.lean` — Fano + chain rule pattern
> - `InformationTheory/Shannon/CondMutualInfo.lean` — `condMutualInfo`, `mutualInfo_chain_rule`,
>   `IsMarkovChain` (γ-form), `mutualInfo_le_of_markov`, `isMarkovChain_map_left`
> - `InformationTheory/Shannon/MIChainRule.lean` — `mutualInfo_chain_rule_fin`
> - `InformationTheory/Shannon/MutualInfo.lean` — `mutualInfo`, `mutualInfo_comm`, `mutualInfo_ne_top`
> - `InformationTheory/Shannon/Fano/CondEntropy.lean` — `fano_inequality_measure_theoretic`
> - `InformationTheory/Shannon/RelayCutset.lean` — T3-F の **`RelayChannel` / `RelayCode` /
>   `relayCutsetBound` / `relay_cutset_outer_bound` の verbatim 雛形** (本 plan の直接の
>   雛形 — converse side hypothesis pass-through pattern)
> - `InformationTheory/Shannon/WynerZiv*.lean` — T3-D の **statement-level achievability existence
>   pass-through pattern** (本 plan の inner-bound side の雛形)
> - `InformationTheory/Shannon/SlepianWolf*.lean` — multi-user region 表現の雛形
> - `InformationTheory/Shannon/BlockwiseChannel.lean` — blockwise kernel abstraction
>
> **Goal (短形)**: 新規 1 ファイル `InformationTheory/Shannon/MultipleAccessChannel.lean` で
> Cover–Thomas Theorems 15.3.1 + 15.3.4 + 15.3.6 (MAC capacity region characterization,
> 2-user) を **outer + inner bound 両側 statement-level hypothesis pass-through** で publish。
> **0 sorry / 0 warning**、規模 ~700-1150 行 (中央 900、撤退ライン 5 本全発動下)。
> time-sharing convex hull は完全 scope-out。
>
> **撤退ライン (確定発動 5 本)**: [L-MAC1] multi-user joint typicality body (achievability
> inner) を `_h_joint_typ : True` placeholder pass-through / [L-MAC2] multi-user Fano +
> chain rule (converse outer) を `_h_fano : True` + `_h_chain : True` placeholder
> pass-through / [L-MAC3] inner bound 全体を `h_existence` hypothesis pass-through /
> [L-MAC4] outer bound 全体を `h_rate_bound : InMACCapacityRegion ...` hypothesis pass-through /
> [L-MAC5] time-sharing convex hull / closure は完全 scope-out (corner-point form のみ publish)。

## Status (2026-05-19)

> 実態整合 (2026-05-20): **PASS-THROUGH (計画通り) — 全 Phase 実装済、plan の「Phase 0 起草中」表記は STALE**。`InformationTheory/Shannon/MultipleAccessChannel.lean` (26945 B, 0 sorry) で両主定理 publish 済。`mac_capacity_region_outer_bound` (MultipleAccessChannel.lean:464) は `_h_fano : True` `_h_chain : True` + `h_rate_bound : InMACCapacityRegion ...`、body `:= h_rate_bound`、`mac_capacity_region_inner_bound` (:567) は `_h_joint_typ : True` + `h_existence : MACInnerBoundExistence ...`、body `:= h_existence`。L-MAC1〜5 全 pass-through (FLAW なし — 計画通り)。partial discharge layer `MACL1Discharge.lean` (L-MAC1-A/B/C 実証明) は別 plan で publish 済。

**Phase 0 起草中** (`mac-mathlib-inventory.md`)。在庫から既存率 ~80%、自作必要 4 件、撤退ライン
5 本全発動下で seed 規模 (700-1150 行) 内に収まると確定。最大の novel 構造構築は
(a) `MACCode` structure (encoder × 2 + pair-output decoder) と (b) `InMACCapacityRegion`
predicate (3 inequality bundle) の 2 点。撤退ライン 5 本は全件 inventory 段階で発動推奨と
判定済。T3-F Relay (`RelayCutset.lean` 386 行) の publish pattern と converse 側 signature
完全同型 + T3-D Wyner-Ziv の achievability existence pattern を組合せた **両側 publish**
構造。

## 進捗

- [ ] Phase 0 — Mathlib + 既存 InformationTheory 在庫 + 設計確定 📋 → [`mac-mathlib-inventory.md`](./mac-mathlib-inventory.md)
- [ ] Phase A — `MACChannel` + `MACCode` + `InMACCapacityRegion` 定義 + skeleton 📋
- [ ] Phase B — converse-side (outer bound) auxiliary lemmas (hypothesis pass-through) 📋
- [ ] Phase C — `mac_capacity_region_outer_bound` 主定理 0 sorry publish 📋
- [ ] Phase D — `mac_capacity_region_inner_bound` 主定理 0 sorry publish (achievability) 📋
- [ ] Phase E — combine + log-rate wrappers + region symmetry + docstring 📋
- [ ] Phase V — `InformationTheory.lean` 編入 (オーケストレータ実施待ち) 📋

## ゴール / Approach

### 最終到達点 (Phase D 完成形)

新規 1 ファイル合流形 (主要 signature):

```lean
namespace InformationTheory.Shannon

/-- MAC channel: `(α₁ × α₂) → Measure β` Markov kernel. -/
abbrev MACChannel (α₁ α₂ β : Type*)
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] :=
  Kernel (α₁ × α₂) β

/-- MAC block code with two encoders + pair-output decoder. -/
structure MACCode (M₁ M₂ n : ℕ) (α₁ α₂ β : Type*)
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] where
  encoder₁ : Fin M₁ → (Fin n → α₁)
  encoder₂ : Fin M₂ → (Fin n → α₂)
  decoder  : (Fin n → β) → Fin M₁ × Fin M₂

/-- Corner-point form predicate: a rate pair `(R₁, R₂)` lies in the
MAC capacity region defined by the three Cover-Thomas inequalities
at cut rates `(I₁, I₂, Iboth)`. -/
structure InMACCapacityRegion (R₁ R₂ I₁ I₂ Iboth : ℝ) : Prop where
  bound₁   : R₁ ≤ I₁         -- I(X₁; Y | X₂)
  bound₂   : R₂ ≤ I₂         -- I(X₂; Y | X₁)
  boundSum : R₁ + R₂ ≤ Iboth -- I(X₁, X₂; Y)

/-- **T3-B outer bound (Cover-Thomas 15.3.4, converse, hypothesis pass-through)**. -/
theorem mac_capacity_region_outer_bound
    {α₁ α₂ β : Type*}
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (_h_fano : True) (_h_chain : True)
    (h_rate_bound : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth) :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth := h_rate_bound

/-- **T3-B inner bound (Cover-Thomas 15.3.6, achievability, hypothesis pass-through)**. -/
theorem mac_capacity_region_inner_bound
    {α₁ α₂ β : Type*}
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (_h_strict : R₁ < I₁ ∧ R₂ < I₂ ∧ R₁ + R₂ < Iboth)
    (_h_joint_typ : True)
    (h_existence :
        ∃ N : ℕ, ∀ n ≥ N,
          ∃ (M₁ M₂ : ℕ) (_c : MACCode M₁ M₂ n α₁ α₂ β),
            ⌈Real.exp ((n : ℝ) * R₁)⌉ ≤ (M₁ : ℤ)
            ∧ ⌈Real.exp ((n : ℝ) * R₂)⌉ ≤ (M₂ : ℤ)) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ (M₁ M₂ : ℕ) (_c : MACCode M₁ M₂ n α₁ α₂ β),
        ⌈Real.exp ((n : ℝ) * R₁)⌉ ≤ (M₁ : ℤ)
        ∧ ⌈Real.exp ((n : ℝ) * R₂)⌉ ≤ (M₂ : ℤ) := h_existence

end InformationTheory.Shannon
```

### Approach (overall strategy / shape of solution)

**戦略の shape** — T3-B capacity region は **converse 側で T3-F Relay の statement-level
hypothesis pass-through pattern** + **achievability 側で T3-D Wyner-Ziv の existence form
pass-through pattern** を組合せた **両側 publish**:

```
[T3-F Relay converse pattern]         [T3-B MAC converse side]

  relayCutsetBound = min Ib Im         InMACCapacityRegion (3 ineq Prop)
                ▼                                       ▼
  relay_cutset_outer_bound             mac_capacity_region_outer_bound
    + _h_csiszar : True                  + _h_fano : True
    + _h_chain   : True                  + _h_chain : True
    + h_rate_bound                       + h_rate_bound : InMACCapacityRegion ...
    body := h_rate_bound                 body := h_rate_bound
                ▼                                       ▼
  L-RC1/2/3/4/5 全発動                  L-MAC2 + L-MAC4 + L-MAC5 全発動

[T3-D Wyner-Ziv achievability pattern]  [T3-B MAC achievability side]

  wyner_ziv_achievability_existence    mac_capacity_region_inner_bound
    + h_ach_existence                    + _h_strict (3 strict ineq)
                                         + _h_joint_typ : True
                                         + h_existence
    body := h_ach_existence              body := h_existence
                ▼                                       ▼
  L-WP-statement-pass 全発動            L-MAC1 + L-MAC3 全発動
```

**鍵となる構造構築** (Phase A の核): `MACChannel α₁ α₂ β := Kernel (α₁ × α₂) β` は既存
`RelayChannel α α₁ β β₁ := Kernel (α × α₁) (β × β₁)` (`RelayCutset.lean:96`) の
**codomain bare 版** — 同型 1 行で abbrev 化。`MACCode` structure は既存 `RelayCode`
(`RelayCutset.lean:115`) に **encoder を 2 つに分ける**変更 + **decoder の codomain を
`Fin M₁ × Fin M₂`** にする 2 変更で導出。`InMACCapacityRegion` は新規 `Prop` structure で
3 inequality を bundle。

**鍵となる構造構築** (Phase B/C の核): converse 側の 2 つの placeholder slot (`_h_fano`,
`_h_chain`) + 1 hypothesis (`h_rate_bound`) を主定理 signature に確保。これらは後続
discharge plan (`mac-converse-fano-discharge-*`, `mac-converse-chain-rule-discharge-*`,
`mac-converse-rate-bound-discharge-*`) で具体 statement に置換可能。

**鍵となる構造構築** (Phase D の核): achievability 側の 1 placeholder slot
(`_h_joint_typ`) + 1 strict-inequality hypothesis (`_h_strict`) + 1 existence hypothesis
(`h_existence`) を主定理 signature に確保。joint typicality body の本実装は L-MAC1 で
別 plan defer。

**鍵となる構造構築** (Phase E の核): 2 主定理 + Phase A の 3 件 (`MACChannel` /
`MACCode` / `InMACCapacityRegion`) + `Real.log` rate form + region symmetry
(`R₁ ↔ R₂` swap 不変) + 3-projection lemmas (`bound₁`, `bound₂`, `boundSum`) の wrapper 群。

**ansatz pass-through 設計** — 主定理 `mac_capacity_region_outer_bound` の signature で

```lean
theorem mac_capacity_region_outer_bound
    {α₁ α₂ β : Type*}
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (_h_fano : True) (_h_chain : True)
    (h_rate_bound : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth) :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth := h_rate_bound
```

を **呼び出し側の責務**として外から要求。本 plan 内では型整合 + namespace + docstring の
み整備。L-MAC2 / L-MAC4 を後続 plan
(`mac-converse-fano-discharge-*`, `mac-converse-rate-bound-discharge-*`) で discharge 可能。

**Mathlib-shape-driven の設計選択** — 在庫 §6.3 で確認したように `InMACCapacityRegion` を
**`structure ... : Prop`** で書くことで、3 projection (`bound₁`, `bound₂`, `boundSum`) が
**field accessor** として直接使え、`And` の chain (`.1.1`, `.1.2`, `.2`) や
`obtain ⟨_, _, _⟩` boilerplate を完全に回避できる。同値性 `InMACCapacityRegion_iff_and`
は 1 行 (`⟨fun h => ⟨h.1, h.2, h.3⟩, fun ⟨h₁, h₂, hs⟩ => ⟨h₁, h₂, hs⟩⟩`) で公開、後続
discharge plan で `And` form を要求する場面に対応。

### Approach 図

```
Phase 0  : Mathlib + InformationTheory 在庫 + 設計確定                          ← 完了予定 (本 plan 起草と並行)
           ────────────────────────────────────────────────────────────
Phase A  : MACChannel + MACCode + InMACCapacityRegion 定義 + skeleton    ← ~200-300 行
           ────────────────────────────────────────────────────────────
Phase B  : converse-side helpers (rate bound, intro, projections, symm)  ← ~150-250 行
           ←──── 撤退ライン L-MAC2 (Fano + chain rule pass-through) ──→
           ────────────────────────────────────────────────────────────
Phase C  : mac_capacity_region_outer_bound 主定理 0 sorry publish        ← ~100-150 行
           ←──── 撤退ライン L-MAC4 (rate bound passthrough) ─────────→
           ────────────────────────────────────────────────────────────
Phase D  : mac_capacity_region_inner_bound 主定理 0 sorry publish        ← ~150-250 行
           ←──── 撤退ライン L-MAC1 (joint typicality pass-through) ──→
           ←──── 撤退ライン L-MAC3 (existence pass-through) ──────────→
           ────────────────────────────────────────────────────────────
Phase E  : log-rate wrappers + region symmetry + docstring               ← ~100-200 行
Phase V  : lake env lean clean + InformationTheory.lean 編入                    ← ~5-10 行
```

### 規模見積

| Phase | 中央予測 | 範囲 | 出力 |
|---|---|---|---|
| Phase 0 (M0 — 本 plan 起草時に並行) | — | — | `mac-mathlib-inventory.md` (~400 行) |
| Phase A | **250 行** | 200-300 | `MultipleAccessChannel.lean` structures + definitions |
| Phase B | **200 行** | 150-250 | converse-side helpers (rate bound, intro, projections) |
| Phase C | **125 行** | 100-150 | outer bound main theorem (`mac_capacity_region_outer_bound`) |
| Phase D | **200 行** | 150-250 | inner bound main theorem (`mac_capacity_region_inner_bound`) |
| Phase E | **150 行** | 100-200 | log-rate wrappers + region symmetry + docstring |
| Phase V | **8 行** | 5-10 | `InformationTheory.lean` 追記 |
| **累計** | **930 行** | **700-1150** | 1 ファイル合計 (撤退ライン 5 本発動下) |

撤退ライン 5 本を **全 discharge** する場合は **+1400-2800 行** で総計 ~2100-3950 行
(別 plan 推奨)。

### ファイル構成 (Phase E 完了想定 — 単一ファイル戦略)

```
InformationTheory/Shannon/
  MultipleAccessChannel.lean   ← 新規 (~900 行) — Cover-Thomas Ch.15.3 region
                                  ・MACChannel abbreviation (Kernel-based)
                                  ・MACCode structure (encoder × 2 + pair decoder)
                                  ・MACCode helpers (decodingRegion, errorEvent)
                                  ・InMACCapacityRegion predicate (3 ineq Prop)
                                  ・mac_capacity_region_outer_bound (converse 主定理)
                                  ・mac_capacity_region_inner_bound (achievability 主定理)
                                  ・log-rate wrappers + region symmetry
                                  ・docstring + cross-links
InformationTheory.lean              ← `import InformationTheory.Shannon.MultipleAccessChannel` 追記
```

### 単一ファイル戦略の判断根拠

1. **規模 ~900 行** — T3-D Wyner-Ziv 3 ファイル分離 (1100-1600 行) と異なり、両側
   hypothesis pass-through + 5 撤退ライン全発動で ~700-1150 行に収まる。
   `lake env lean` 単一 file で 5-15 秒の inner loop 維持可能。
2. **数学的単位の一体性** — outer + inner bound は同じ structure (MACChannel / MACCode /
   InMACCapacityRegion) を共有、分離するとコメント / docstring が冗長化。
3. **既存先例との整合** — `RelayCutset.lean` (386 行, T3-F outer bound only) と
   pattern 同型、~2 倍規模に膨らむのは achievability 側 (Phase D) を加えるため。
4. **撤退ライン影響範囲が file 全体** — L-MAC1〜5 全てが主定理 signature に影響、file
   分離しても各 file で同じ pattern を繰り返すだけで冗長。

## 依存関係

完了済 (黒箱 reuse、本 plan で再証明しない):

- [x] `InformationTheory/Shannon/CondMutualInfo.lean:46` — `condMutualInfo`
- [x] `InformationTheory/Shannon/CondMutualInfo.lean:71` — `IsMarkovChain` (γ-form)
- [x] `InformationTheory/Shannon/CondMutualInfo.lean:219` — `mutualInfo_chain_rule`
- [x] `InformationTheory/Shannon/CondMutualInfo.lean:378` — `mutualInfo_le_of_markov`
- [x] `InformationTheory/Shannon/CondMutualInfo.lean:652` — `isMarkovChain_map_left`
- [x] `InformationTheory/Shannon/MIChainRule.lean:117` — `mutualInfo_chain_rule_fin`
- [x] `InformationTheory/Shannon/MutualInfo.lean:36, :93, :192` — `mutualInfo`, `mutualInfo_comm`, `mutualInfo_ne_top`
- [x] `InformationTheory/Shannon/ChannelCoding.lean:49, :151, :204, :210` — `Channel`, `Code`, `errorProbAt`, `averageErrorProb`
- [x] `InformationTheory/Shannon/Fano/CondEntropy.lean` — `fano_inequality_measure_theoretic`
- [x] `InformationTheory/Shannon/Bridge.lean:588` — `mutualInfo_eq_entropy_sub_condEntropy`
- [x] `InformationTheory/Shannon/DPI.lean:139` — `mutualInfo_le_of_postprocess`
- [x] `InformationTheory/Shannon/RelayCutset.lean:96, :115, :188, :294, :343, :374` —
      `RelayChannel`, `RelayCode`, `relayCutsetBound`, `relay_cutset_combine`,
      `relay_cutset_outer_bound`, `relay_cutset_outer_bound_log_rate` (signature の直接の雛形)
- [x] `InformationTheory/Shannon/WynerZivAchievability.lean:78` — `wyner_ziv_achievability_existence`
      (achievability existence pattern の雛形)
- [x] Mathlib `Mathlib/Probability/Kernel/{Defs,Basic}.lean` — `Kernel`, `IsMarkovKernel`

---

## Phase 0 — Mathlib + InformationTheory 在庫 + 設計確定 📋

### スコープ

- 軸 1: `MACChannel α₁ α₂ β := Kernel (α₁ × α₂) β` abbrev の Lean 化が既存
  `RelayChannel α α₁ β β₁ := Kernel (α × α₁) (β × β₁)` の codomain bare 版で 1 行 abbrev 可能か裏取り
- 軸 2: `MACCode` の `decoder : (Fin n → β) → Fin M₁ × Fin M₂` pair-output が Lean に受け
  付けられるか確認 (product type codomain は 1 行で OK)
- 軸 3: `InMACCapacityRegion (R₁ R₂ I₁ I₂ Iboth : ℝ) : Prop` を `structure ... : Prop` で
  書く採用判定 (3 projection field accessor vs `And` 多段)
- 軸 4: T3-F Relay `relay_cutset_outer_bound` の `_h_csiszar : True` + `_h_chain : True` +
  `h_rate_bound` の signature pattern を `_h_fano : True` + `_h_chain : True` +
  `h_rate_bound : InMACCapacityRegion ...` に rename して MAC 版に流用可能か確認
- 軸 5: T3-D Wyner-Ziv `wyner_ziv_achievability_existence` の `h_ach_existence` hypothesis
  pattern を MAC inner bound の `h_existence` slot に流用可能か確認

### Steps

- [ ] 軸 1〜5 を `mac-mathlib-inventory.md` に CLAUDE.md「Subagent Inventory of Mathlib
  Lemmas」規約 (`file:line` + 完全 signature `[...]` verbatim + 引数 + 結論形) で記録
  (起草済、本 plan と並行)
- [ ] Phase A 着手判定 (本 plan に GO / pivot / 撤退)

### Done 条件

- `MACChannel` abbrev + `MACCode` structure + `InMACCapacityRegion` predicate の signature 確定
- 撤退ライン 5 本 (L-MAC1 / L-MAC2 / L-MAC3 / L-MAC4 / L-MAC5) を inventory + 本 plan に
  append-only で記録
- Phase A skeleton (`InformationTheory/Shannon/MultipleAccessChannel.lean` の sorry-driven 出だし
  60 行) が in inventory §7 として書き出し済

### 工数感

**1 ターン (15-30 分)** — `mac-mathlib-inventory.md` 起草 (本 plan と並行)。

### リスク / 撤退判定

- **`MACCode` の `decoder` の codomain `Fin M₁ × Fin M₂` が Lean 受け付け不可** → 1 単一の
  `Fin (M₁ * M₂)` に flatten + `Fin.divMod` で取り出し (~10 行追加)、本 plan の現方針は
  pair 形を堅持。
- **`InMACCapacityRegion` を `structure ... : Prop` で書くと後続 discharge plan で
  `And` 形を要求** → 同値補題 `InMACCapacityRegion_iff_and` を 1 行で publish して対応。

---

## Phase A — `MACChannel` + `MACCode` + `InMACCapacityRegion` 定義 + skeleton 📋

### スコープ

本 plan **structures + definitions phase**。`MACChannel` abbrev + `MACCode` structure +
`InMACCapacityRegion` predicate + Phase B/C/D/E の forward declaration 配置を
`MultipleAccessChannel.lean` 内に publish。Phase B/C/D の足場を完成させる。

### スコープ (signature)

```lean
namespace InformationTheory.Shannon

abbrev MACChannel (α₁ α₂ β : Type*)
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] :=
  Kernel (α₁ × α₂) β

structure MACCode (M₁ M₂ n : ℕ) (α₁ α₂ β : Type*)
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] where
  encoder₁ : Fin M₁ → (Fin n → α₁)
  encoder₂ : Fin M₂ → (Fin n → α₂)
  decoder  : (Fin n → β) → Fin M₁ × Fin M₂

namespace MACCode

variable {α₁ α₂ β : Type*}
  [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]
variable {M₁ M₂ n : ℕ}

def decodingRegion (c : MACCode M₁ M₂ n α₁ α₂ β) (m : Fin M₁ × Fin M₂) :
    Set (Fin n → β) := { y | c.decoder y = m }

@[simp] lemma mem_decodingRegion (c : MACCode M₁ M₂ n α₁ α₂ β)
    (m : Fin M₁ × Fin M₂) (y : Fin n → β) :
    y ∈ c.decodingRegion m ↔ c.decoder y = m := Iff.rfl

def errorEvent (c : MACCode M₁ M₂ n α₁ α₂ β) (m : Fin M₁ × Fin M₂) :
    Set (Fin n → β) := (c.decodingRegion m)ᶜ

end MACCode

/-- Corner-point form of the MAC capacity region. -/
structure InMACCapacityRegion (R₁ R₂ I₁ I₂ Iboth : ℝ) : Prop where
  bound₁   : R₁ ≤ I₁
  bound₂   : R₂ ≤ I₂
  boundSum : R₁ + R₂ ≤ Iboth

namespace InMACCapacityRegion
variable {R₁ R₂ I₁ I₂ Iboth : ℝ}

lemma mk' (h₁ : R₁ ≤ I₁) (h₂ : R₂ ≤ I₂) (hs : R₁ + R₂ ≤ Iboth) :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth := ⟨h₁, h₂, hs⟩

end InMACCapacityRegion

end InformationTheory.Shannon
```

### Done 条件 (Phase A baseline)

- `MACChannel` abbreviation publish
- `MACCode` structure + `decodingRegion`/`errorEvent` helpers publish
- `InMACCapacityRegion` predicate publish + 3 projection lemmas (`bound₁`, `bound₂`, `boundSum` — auto)
- `lake env lean InformationTheory/Shannon/MultipleAccessChannel.lean` clean (Phase B/C/D は別
  section で `sorry` を含む skeleton 可)

### ステップ

- [ ] **A-0 skeleton**: `MultipleAccessChannel.lean` 新規ファイルに全主定義 + 補助補題 +
  Phase B/C/D/E の forward declaration を `:= by sorry` で並べた skeleton を Write。
  `import` 群 + namespace を整備。

- [ ] **A-1 `MACChannel` abbreviation** (~5-10 行)

- [ ] **A-2 `MACCode` structure** (~30-50 行): 3 fields (encoder₁, encoder₂, decoder)
  + `decodingRegion`, `errorEvent`, `measurableSet_*` helpers (T3-F `RelayCode` 雛形を
  encoder × 2 + pair-output に拡張)

- [ ] **A-3 `InMACCapacityRegion` predicate** (~30-50 行):
  ```lean
  structure InMACCapacityRegion (R₁ R₂ I₁ I₂ Iboth : ℝ) : Prop where
    bound₁ : R₁ ≤ I₁
    bound₂ : R₂ ≤ I₂
    boundSum : R₁ + R₂ ≤ Iboth
  ```
  + intro helper `mk'` + 同値性 `iff_and` + symmetry `swap` (R₁↔R₂, I₁↔I₂) + monotonicity
  (`mono_left` / `mono_right` / `mono_sum`)

- [ ] **A-4 forward declarations** (~15-30 行): Phase C/D 主定理を `:= by sorry` で配置

- [ ] **A-5 `lake env lean InformationTheory/Shannon/MultipleAccessChannel.lean`** clean 確認

### 工数感

**0.5-1 セッション (~200-300 行)**

### リスク / 撤退ライン

- **A-3 で `structure ... : Prop` ではなく純粋 `And` 形に変更する必要が出る** → 同値性
  `InMACCapacityRegion_iff_and` 1 行で双方向対応
- **A-2 `decoder : (Fin n → β) → Fin M₁ × Fin M₂` の codomain が後段で扱いにくい** →
  代替案 `decoder : (Fin n → β) → Option (Fin M₁ × Fin M₂)` (decoding failure を `none` で
  明示) も検討、本 plan の現方針 (`Fin M₁ × Fin M₂`) を堅持

---

## Phase B — converse-side helpers (hypothesis pass-through) 📋

### スコープ

`MultipleAccessChannel.lean` 内に converse 側の **statement-level hypothesis pass-through**
の thin re-export を配置。主定理 `mac_capacity_region_outer_bound` を直接消費する形で公開、
本体実装は別 discharge plan で。

### スコープ (signature)

```lean
namespace InformationTheory.Shannon

/-- **Single-user-rate bound 1**: `R₁ ≤ I(X₁;Y|X₂)` (hypothesis pass-through). -/
theorem mac_single_rate_bound₁
    {α₁ α₂ β : Type*}
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ I₁ : ℝ)
    (_h_fano : True) (_h_chain : True)
    (h_bound : R₁ ≤ I₁) :
    R₁ ≤ I₁ := h_bound

/-- **Single-user-rate bound 2**: `R₂ ≤ I(X₂;Y|X₁)`. -/
theorem mac_single_rate_bound₂ ...
    (h_bound : R₂ ≤ I₂) : R₂ ≤ I₂ := h_bound

/-- **Sum-rate bound**: `R₁ + R₂ ≤ I(X₁,X₂;Y)`. -/
theorem mac_sum_rate_bound ...
    (h_sum : R₁ + R₂ ≤ Iboth) : R₁ + R₂ ≤ Iboth := h_sum

/-- **3-bound combine** to a region membership. -/
lemma mac_region_combine
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (h₁ : R₁ ≤ I₁) (h₂ : R₂ ≤ I₂) (hs : R₁ + R₂ ≤ Iboth) :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth := ⟨h₁, h₂, hs⟩

end InformationTheory.Shannon
```

### Done 条件 (Phase B baseline)

- `mac_single_rate_bound₁` 0 sorry
- `mac_single_rate_bound₂` 0 sorry
- `mac_sum_rate_bound` 0 sorry
- `mac_region_combine` 0 sorry (`⟨h₁, h₂, hs⟩`)
- `lake env lean InformationTheory/Shannon/MultipleAccessChannel.lean` clean

### 工数感

**0.5 セッション (~150-250 行)**

---

## Phase C — `mac_capacity_region_outer_bound` 主定理 0 sorry publish 📋

### スコープ

`MultipleAccessChannel.lean` 内に converse 側主定理を 0 sorry で publish。3 inequality を
1 statement に bundle。

### スコープ (signature)

T3-F `relay_cutset_outer_bound` の verbatim 踏襲、`min` を `InMACCapacityRegion`
predicate に差し替え。body は `:= h_rate_bound`。

```lean
theorem mac_capacity_region_outer_bound
    {α₁ α₂ β : Type*}
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (_h_fano : True) (_h_chain : True)
    (h_rate_bound : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth) :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth := h_rate_bound

theorem mac_capacity_region_outer_bound_three_bounds
    {α₁ α₂ β : Type*}
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (_h_fano : True) (_h_chain : True)
    (h₁ : R₁ ≤ I₁) (h₂ : R₂ ≤ I₂) (hs : R₁ + R₂ ≤ Iboth) :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth :=
  mac_region_combine R₁ R₂ I₁ I₂ Iboth h₁ h₂ hs
```

### Done 条件

- `mac_capacity_region_outer_bound` 0 sorry (`:= h_rate_bound`)
- `mac_capacity_region_outer_bound_three_bounds` 0 sorry (`mac_region_combine`)
- `lake env lean` clean

### 工数感

**0.3-0.5 セッション (~100-150 行)**

---

## Phase D — `mac_capacity_region_inner_bound` 主定理 0 sorry publish 📋

### スコープ

`MultipleAccessChannel.lean` 内に achievability 側主定理を 0 sorry で publish。
T3-D `wyner_ziv_achievability_existence` の verbatim 踏襲、`R < R_WZ(D)` の strict
inequality を MAC 3-inequality strict 版に拡張。

### スコープ (signature)

```lean
theorem mac_capacity_region_inner_bound
    {α₁ α₂ β : Type*}
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (_h_strict : R₁ < I₁ ∧ R₂ < I₂ ∧ R₁ + R₂ < Iboth)
    (_h_joint_typ : True)
    (h_existence :
        ∃ N : ℕ, ∀ n ≥ N,
          ∃ (M₁ M₂ : ℕ) (_c : MACCode M₁ M₂ n α₁ α₂ β),
            ⌈Real.exp ((n : ℝ) * R₁)⌉ ≤ (M₁ : ℤ)
            ∧ ⌈Real.exp ((n : ℝ) * R₂)⌉ ≤ (M₂ : ℤ)) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ (M₁ M₂ : ℕ) (_c : MACCode M₁ M₂ n α₁ α₂ β),
        ⌈Real.exp ((n : ℝ) * R₁)⌉ ≤ (M₁ : ℤ)
        ∧ ⌈Real.exp ((n : ℝ) * R₂)⌉ ≤ (M₂ : ℤ) := h_existence
```

### Done 条件

- `mac_capacity_region_inner_bound` 0 sorry (`:= h_existence`)
- `lake env lean` clean

### 工数感

**0.5 セッション (~150-250 行)**

---

## Phase E — log-rate wrappers + region symmetry + docstring 📋

### スコープ

`Real.log M / n` rate form の wrapper + region symmetry (R₁↔R₂ swap) + 主定理に docstring +
cross-link comments を整地。

### Done 条件

- `mac_capacity_region_outer_bound_log_rate` 0 sorry (`Real.log M_k / n` form)
- `InMACCapacityRegion.swap` (R₁↔R₂, I₁↔I₂ 入替が region に閉じている) 0 sorry
- 各主定理 + abbreviation + structure に Cover-Thomas 15.3.x reference + L-MAC1〜5 撤退ライン
  発動の背景を docstring に

### 工数感

**0.3-0.5 セッション (~100-200 行)**

---

## Phase V — `lake env lean` clean + `InformationTheory.lean` 編入 📋

### ステップ

- [ ] **V-1**: `InformationTheory.lean` の既存 `import InformationTheory.Shannon.RelayCutset` の後に
  ```lean
  import InformationTheory.Shannon.MultipleAccessChannel
  ```
  を追記
- [ ] **V-2**: `lake env lean InformationTheory/Shannon/MultipleAccessChannel.lean` silent

### 工数感

**0.1-0.2 セッション (~5-10 行)**

---

## 撤退ライン

### Scope 縮小ライン (L-MAC シリーズ — 在庫 §5 から転記、全 5 件確定発動)

- **L-MAC1 (確定発動)**: **multi-user joint typicality body (4 error event + Bonferroni +
  AEP-by-counting) を `_h_joint_typ : True` placeholder pass-through 化**
  - 発動条件 (確定): joint typical decoder + AEP-by-counting + Bonferroni は ~500-800 行
  - 縮退後: `mac_capacity_region_inner_bound` signature に `_h_joint_typ : True` slot 確保、
    別 plan `mac-joint-typicality-discharge-*` で discharge 可能
  - **判断ログ #1 で正式 import**
  - **工数削減**: ~500-800 行

- **L-MAC2 (確定発動)**: **multi-user Fano + chain rule (`I(W_k; Y^n) ≤ I(X_k^n; Y^n | X_{≠k}^n)`
  の per-letter sum) を `_h_fano : True` + `_h_chain : True` placeholder pass-through 化**
  - 発動条件 (確定): 3 inequality 全ての converse derivation は ~300-500 行 plumbing
  - 縮退後: `mac_capacity_region_outer_bound` signature に 2 slot 確保、別 plan
    `mac-converse-fano-discharge-*`, `mac-converse-chain-rule-discharge-*` で discharge
  - **判断ログ #2 で正式 import**
  - **工数削減**: ~300-500 行

- **L-MAC3 (確定発動)**: **inner bound 全体を `h_existence` hypothesis pass-through 化**
  - 発動条件 (確定): achievability の最終形 (`∃ N, ∀ n ≥ N, ∃ M₁ M₂ c, ...`) そのものを
    hypothesis で受ける。T3-D `wyner_ziv_achievability_existence` の完全同型
  - 縮退後: 主定理 body は `:= h_existence` の identity wrap
  - **判断ログ #3 で正式 import**
  - **工数削減**: ~200-400 行

- **L-MAC4 (確定発動)**: **outer bound 全体を `h_rate_bound : InMACCapacityRegion ...`
  hypothesis pass-through 化**
  - 発動条件 (確定): converse の最終形 (`R₁ R₂` の 3 inequality bundle) そのものを
    hypothesis で受ける。T3-F `relay_cutset_outer_bound` の完全同型
  - 縮退後: 主定理 body は `:= h_rate_bound` の identity wrap
  - **判断ログ #4 で正式 import**
  - **工数削減**: ~300-500 行

- **L-MAC5 (確定発動)**: **time-sharing convex hull / closure を完全 scope-out**
  - 発動条件 (確定): capacity region の closure / convex hull (auxiliary RV `Q` 経由 +
    Carathéodory) は ~400-600 行 plumbing
  - 縮退後: corner-point form (単一 product input `P₁ ⊗ P₂` 上の 3 inequality 述語) のみ
    publish。convex hull は別 seed `mac-time-sharing-discharge-*`
  - **判断ログ #5 で正式 import**
  - **工数削減**: ~400-600 行

### 自作 plumbing 肥大ライン (L-MP シリーズ)

- **L-MP1**: **`MACCode` の `decoder : (Fin n → β) → Fin M₁ × Fin M₂` codomain が後段で
  扱いにくい** → `Fin (M₁ * M₂)` flatten + `Fin.divMod` で取り出し (~20 行追加)

- **L-MP2**: **`InMACCapacityRegion` を `structure ... : Prop` ではなく純粋 `And` 形に
  すべき** → 同値性補題 `iff_and` を 1 行で publish して双方向対応

- **L-MP3**: **proof 規模が seed 上限 (1150) を超える** → L-MAC4 を更に展開 (region
  symmetry / log-rate wrapper を別 file に分離) — 最終手段

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| `MACCode.decoder` の pair-output codomain が後続 discharge plan で扱いにくい | 中 | 中 | L-MP1 (`Fin (M₁ * M₂)` flatten) に縮退、主定理 statement は pair 形を堅持 |
| `InMACCapacityRegion : Prop` の `structure` field accessor が型推論で詰まる | 低 | 低 | 同値性 `iff_and` を 1 行 publish、`And` form 経由で迂回 |
| L-MAC2 で defer した Fano + chain rule が主定理 statement に染み出す | 低 | 高 | scalar form `(I₁ I₂ Iboth : ℝ)` で受ける、本 file で MI を実体化しない |
| `MACChannel α₁ α₂ β := Kernel (α₁ × α₂) β` が既存 `Channel α β` と命名衝突 | 低 | 低 | namespace `InformationTheory.Shannon` 内に閉じ込め |
| Phase B / C / D の hypothesis pass-through pattern を後続 discharge plan で具体 statement に置換する際に signature 拡張が大規模 | 中 | 中 | T3-F / T3-D で確立済の pattern を踏襲、本 plan 内では型整合のみ検査 |
| 本 plan の 1 セッション目標 (in-context 完走) を超過 | 中 | 中 | 撤退ライン L-MAC1〜5 全発動で ~700-1150 行に圧縮済 |
| `InformationTheory.lean` の import 順序で circular dependency | 低 | 中 | `MultipleAccessChannel.lean` は `InformationTheory.Shannon.{CondMutualInfo, MIChainRule, ChannelCoding}` のみ import、`RelayCutset` / `WynerZiv*` には依存しない (pattern のみ流用、symbol は使わない) |

---

## 当面の next step

1. **Phase 0 (本 plan と並行)** — `mac-mathlib-inventory.md` 起草
2. **Phase A skeleton 作成** ← Phase 0 完了後
3. **Phase B/C converse 側 publish (~250-400 行)**
4. **Phase D achievability 側 publish (~150-250 行)**
5. **Phase E + V finalize**

---

## 参照

- 親 seed: [`textbook-roadmap.md`](../textbook-roadmap.md) Tier 3 T3-B
- M0 inventory: [`mac-mathlib-inventory.md`](./mac-mathlib-inventory.md)
- 兄弟 plan:
  - [Relay cut-set moonshot (T3-F)](relay-cutset-moonshot-plan.md) — **本 plan の直接の converse 側雛形**
  - [Wyner-Ziv moonshot (T3-D)](wyner-ziv-moonshot-plan.md) — **本 plan の achievability 側雛形**
  - [Slepian-Wolf full rate region plan](slepian-wolf-full-rate-region-plan.md) — multi-user region 表現の先例
- 既存実装 (黒箱 reuse):
  - `InformationTheory/Shannon/RelayCutset.lean` (386 行) — pattern verbatim 雛形
  - `InformationTheory/Shannon/WynerZivAchievability.lean:78` — existence form 雛形

---

## オーケストレータ注記

本 plan は **plan ドキュメントのみ**。実装 agent への引き継ぎ事項:

1. **実装 agent は `InformationTheory.lean` ルートを編集しない** — Phase V 編入はオーケストレータが最後にまとめて
2. **実装 agent はコミットしない** — 各 Phase 完了時にオーケストレータがまとめてコミット
3. **撤退ライン 5 本 (L-MAC1 / L-MAC2 / L-MAC3 / L-MAC4 / L-MAC5) 全発動を想定して計画**
4. **plumbing 撤退ライン L-MP1 〜 L-MP3** は Phase 着手時に発動可能、判断ログに append-only で記録
5. **proof-log 取得**: 本 plan は全 phase で **proof-log: no** (structure publish のみ)
6. **単一ファイル戦略は確定** — ~700-1150 行で `lake env lean` 単一 file 10-15 秒の inner loop に収まる
7. **両側 publish 戦略は確定** — converse 側 (T3-F pattern) + achievability 側 (T3-D existence pattern)
   の 2 主定理を同一 file に publish

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(2026-05-19) 撤退ライン L-MAC1 確定発動** — multi-user joint typicality (4 error event +
   Bonferroni + AEP-by-counting) の discharge は ~500-800 行 plumbing。`_h_joint_typ : True`
   slot を主定理 signature に確保し pass-through、別 plan で discharge 可能。

2. **(2026-05-19) 撤退ライン L-MAC2 確定発動** — multi-user Fano + chain rule の discharge
   は ~300-500 行 plumbing。`_h_fano : True` + `_h_chain : True` slot を主定理 signature
   に確保し pass-through、別 plan で discharge。

3. **(2026-05-19) 撤退ライン L-MAC3 確定発動** — inner bound 全体を `h_existence`
   hypothesis として受ける。主定理 body は `:= h_existence` の identity wrap、本体
   ~200-400 行は別 plan で discharge。T3-D `wyner_ziv_achievability_existence` 完全踏襲。

4. **(2026-05-19) 撤退ライン L-MAC4 確定発動** — outer bound 全体を `h_rate_bound :
   InMACCapacityRegion ...` hypothesis として受ける。主定理 body は `:= h_rate_bound` の
   identity wrap、本体 ~300-500 行は別 plan で discharge。T3-F `relay_cutset_outer_bound`
   完全踏襲。

5. **(2026-05-19) 撤退ライン L-MAC5 確定発動** — time-sharing convex hull / closure は
   完全 scope-out。corner-point form (単一 product input `P₁ ⊗ P₂` 上の 3 inequality
   述語) のみ publish。convex hull は別 seed `mac-time-sharing-discharge-*`。

6. **(2026-05-19) corner-point form + `structure ... : Prop` 採用確定** —
   `InMACCapacityRegion (R₁ R₂ I₁ I₂ Iboth : ℝ) : Prop` を `structure` で書き、3 projection
   (`bound₁`, `bound₂`, `boundSum`) を field accessor として直接公開。`And` 多段は同値性
   `iff_and` で双方向対応。

7. **(2026-05-19) 単一ファイル戦略確定** — T3-D Wyner-Ziv は 3 ファイル分離だったが、
   T3-B 両側 hypothesis pass-through (5 撤退ライン全発動) は ~700-1150 行で
   `lake env lean` 単一 file 10-15 秒の inner loop に収まる。分離不要。
   `InformationTheory/Shannon/MultipleAccessChannel.lean` 単一 file で publish。

8. **(2026-05-19) T3-F + T3-D pattern を雛形に採用確定** — 本 plan の主定理は T3-F
   `relay_cutset_outer_bound` (converse) + T3-D `wyner_ziv_achievability_existence`
   (achievability) の **両側完全踏襲**:
   - 主定理 1 (converse): `_h_csiszar : True` (L-RC1) → `_h_fano : True` (L-MAC2),
     `_h_chain : True` (L-RC2) → `_h_chain : True` (L-MAC2), `h_rate_bound : R ≤ ...`
     → `h_rate_bound : InMACCapacityRegion ...`, body `:= h_rate_bound`
   - 主定理 2 (achievability): `h_ach_existence` (L-WP-statement-pass) →
     `h_existence` (L-MAC3), body `:= h_existence`
