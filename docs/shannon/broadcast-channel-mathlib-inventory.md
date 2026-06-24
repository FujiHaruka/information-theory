# T3-C Broadcast Channel (degraded) Mathlib + InformationTheory Inventory 📋

> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-C. Broadcast Channel (degraded) (Cover–Thomas Ch.15.6)」
>
> **Sibling plan**: [`broadcast-channel-moonshot-plan.md`](./broadcast-channel-moonshot-plan.md)
>
> **Predecessor / 直接の雛形**:
> - [`mac-mathlib-inventory.md`](./mac-mathlib-inventory.md) — T3-B MAC 在庫
> - [`InformationTheory/Shannon/MultipleAccessChannel.lean`](../../InformationTheory/Shannon/MultipleAccessChannel.lean) — T3-B MAC publish (637 行, L-MAC1〜5 pass-through)
> - [`wyner-ziv-mathlib-inventory.md`](./wyner-ziv-mathlib-inventory.md) — auxiliary RV `U` superposition pattern
> - [`relay-cutset-mathlib-inventory.md`](./relay-cutset-mathlib-inventory.md) — converse hypothesis pass-through pattern

## 結論

**全 5 撤退ライン (L-BC1 / L-BC2 / L-BC3 / L-BC4 / L-BC5) 発動下で seed 規模 ~700-1150 行で publish 可能**と判定。

- 構造体 3 件 (`BroadcastChannel` / `BroadcastCode` / `InBCCapacityRegion`) を新規定義 (~80 行)
- 主定理 2 件 (`bc_capacity_region_outer_bound` converse + `bc_capacity_region_inner_bound` achievability) を hypothesis pass-through 形で publish (~150 行)
- 雛形 T3-B MAC `MultipleAccessChannel.lean` (637 行) の **codomain `β` を `β₁ × β₂` に置換、auxiliary RV `U` を 1 つ追加** で導出可能 (~700-1150 行)
- 既存 publish 済 API ~85% カバー、自作必要は (a) `BroadcastChannel` abbreviation、(b) `BroadcastCode` structure (1 encoder + 2 decoders)、(c) `InBCCapacityRegion` predicate (2 inequality) の 3 件のみ

## §1. Mathlib 在庫 (直接利用候補)

### 1.1 Kernel basics

| file:line | 完全 signature (verbatim, `[...]` brackets) | 結論形 |
|---|---|---|
| `Mathlib/Probability/Kernel/Defs.lean:65` | `def ProbabilityTheory.Kernel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Type _` | type definition |
| `Mathlib/Probability/Kernel/Defs.lean:268` | `class ProbabilityTheory.IsMarkovKernel {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (κ : Kernel α β) : Prop` | type-class |
| `Mathlib/Probability/Kernel/Basic.lean` | `instance ProbabilityTheory.Kernel.instAdd : Add (Kernel α β)` | algebraic operations |

`BroadcastChannel α β₁ β₂ := Kernel α (β₁ × β₂)` で 1 行 abbrev。codomain が **`Prod` 型**になる点が MAC との唯一の構造差 (MAC は domain が `α₁ × α₂`, codomain は bare `β`).

### 1.2 Real-valued inequalities

| file:line | signature | 結論形 |
|---|---|---|
| `Mathlib/Order/Basic.lean` | `theorem LE.le.trans {α : Type*} [Preorder α] {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c` | `a ≤ c` |
| `Mathlib/Tactic/Linarith.lean` | `tactic linarith` | linear arithmetic decision |
| `Mathlib/Data/Real/Basic.lean` | `Real.add_lt_add` 系 strict ineq | `a + c < b + d` |

`InBCCapacityRegion` の 2 inequality + region symmetry 補題 (`mono_*`, `anti_mono_*`) で `linarith` を使用。

## §2. InformationTheory 既存 publish 在庫 (黒箱 reuse)

### 2.1 雛形 file (直接踏襲)

| file:line | 完全 signature | 役割 |
|---|---|---|
| `InformationTheory/Shannon/MultipleAccessChannel.lean:123` | `abbrev MACChannel (α₁ α₂ β : Type*) [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] := Kernel (α₁ × α₂) β` | `BroadcastChannel` の直接の雛形 (domain ↔ codomain swap) |
| `InformationTheory/Shannon/MultipleAccessChannel.lean:143` | `structure MACCode (M₁ M₂ n : ℕ) (α₁ α₂ β : Type*) [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] where encoder₁ ... encoder₂ ... decoder` | `BroadcastCode` の直接の雛形 (encoder 2→1 + decoder 1→2) |
| `InformationTheory/Shannon/MultipleAccessChannel.lean:248` | `structure InMACCapacityRegion (R₁ R₂ I₁ I₂ Iboth : ℝ) : Prop where bound₁ ... bound₂ ... boundSum` | `InBCCapacityRegion` の直接の雛形 (3 ineq → 2 ineq) |
| `InformationTheory/Shannon/MultipleAccessChannel.lean:464` | `theorem mac_capacity_region_outer_bound {M₁ M₂ n : ℕ} (_hn : 0 < n) (_c : MACCode M₁ M₂ n α₁ α₂ β) (R₁ R₂ I₁ I₂ Iboth : ℝ) (_h_fano : True) (_h_chain : True) (h_rate_bound : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth) : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth := h_rate_bound` | `bc_capacity_region_outer_bound` の直接の雛形 (converse) |
| `InformationTheory/Shannon/MultipleAccessChannel.lean:567` | `theorem mac_capacity_region_inner_bound (R₁ R₂ I₁ I₂ Iboth : ℝ) (_h_strict : ...) (_h_joint_typ : True) (h_existence : MACInnerBoundExistence ...) : MACInnerBoundExistence ... := h_existence` | `bc_capacity_region_inner_bound` の直接の雛形 (achievability) |

### 2.2 parent imports (本 file の import 群、MAC と同一)

| file:line | 公開 symbol | 用途 |
|---|---|---|
| `InformationTheory/Shannon/ChannelCoding.lean:49` | `abbrev Channel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] := Kernel α β` | single-user channel base |
| `InformationTheory/Shannon/CondMutualInfo.lean:46` | `noncomputable def condMutualInfo {Ω α β γ : Type*} [MeasurableSpace Ω] ...` | `I(X; Y | U)` の数学的実体 (本 file では type-level 参照のみ) |
| `InformationTheory/Shannon/MIChainRule.lean:117` | `mutualInfo_chain_rule_fin` | per-letter chain rule (本 file では参照のみ) |

### 2.3 兄弟 publish 在庫 (signature 雛形参照)

| file:line | 公開 symbol | 役割 |
|---|---|---|
| `InformationTheory/Shannon/RelayCutset.lean:96` | `abbrev RelayChannel (α α₁ β β₁ : Type*) [...] := Kernel (α × α₁) (β × β₁)` | **`BroadcastChannel` と最も近い類似形** — domain bare、codomain product。BC は逆向き (domain bare、codomain product) |
| `InformationTheory/Shannon/RelayCutset.lean:343` | `theorem relay_cutset_outer_bound` | converse hypothesis pass-through pattern (`_h_csiszar : True` + `_h_chain : True` + `h_rate_bound`) |
| `InformationTheory/Shannon/WynerZivAchievability.lean:78` | `theorem wyner_ziv_achievability_existence` | achievability existence-form pass-through pattern (auxiliary RV `U` 経由) |

## §3. 構造差: MAC ↔ BC ↔ Relay 比較表

| 構造 | domain | codomain | encoder | decoder | auxiliary RV |
|---|---|---|---|---|---|
| `Channel α β` | bare `α` | bare `β` | 1 (`Fin M → Fin n → α`) | 1 (`Fin n → β → Fin M`) | なし |
| `MACChannel α₁ α₂ β` | `α₁ × α₂` | bare `β` | 2 (`Fin M_k → Fin n → α_k`) | 1 pair-output (`Fin n → β → Fin M₁ × Fin M₂`) | なし |
| **`BroadcastChannel α β₁ β₂`** | bare `α` | **`β₁ × β₂`** | 1 (`Fin M₁ × Fin M₂ → Fin n → α`) | **2** (`Fin n → β_k → Fin M_k`) | **`U`** (superposition) |
| `RelayChannel α α₁ β β₁` | `α × α₁` | `β × β₁` | 1 + relay | 1 receiver | なし (cut-set) |

### 3.1 BC 特有: superposition coding

- 主定理は **degraded BC** `X → Y_1 → Y_2` (Markov chain) のみ。一般 BC は scope-out (L-BC5)
- achievability の核は **superposition coding**: `U ~ p(u)`、`X ~ p(x|u)` で `(U, X)` を生成、receiver 1 (Y_1) は `(U, X)` を decode、receiver 2 (Y_2) は `U` のみ decode
- capacity region 2 inequality:
  ```
  R_2 ≤ I(U; Y_2)        -- common info rate (poor receiver)
  R_1 ≤ I(X; Y_1 | U)    -- private info rate (good receiver)
  ```

### 3.2 `BroadcastCode` の field 構成

```lean
structure BroadcastCode (M₁ M₂ n : ℕ) (α β₁ β₂ : Type*)
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂] where
  encoder  : Fin M₁ × Fin M₂ → (Fin n → α)         -- 1 joint encoder
  decoder₁ : (Fin n → β₁) → Fin M₁                  -- good receiver decodes M₁
  decoder₂ : (Fin n → β₂) → Fin M₂                  -- poor receiver decodes M₂
```

MAC との比較: encoder 2 → 1 (1 sender + 2 messages bundled)、decoder 1 → 2 (2 separate receivers)。

## §4. 撤退ライン (5 本全発動見込み)

### L-BC1 (確定発動): joint typicality multi-receiver hypothesis

- 内容: **2-receiver joint typicality + 4 error event + Bonferroni** (achievability inner body)
- 規模: ~500-800 行 (Cover-Thomas Ch.15.6.2 §15.6.2 — common message + private message の 2 段 joint typicality decoder)
- 縮退: `_h_joint_typ : True` placeholder slot を `bc_capacity_region_inner_bound` signature に確保
- discharge plan: `bc-joint-typicality-discharge-*`

### L-BC2 (確定発動): Fano + chain rule multi-user hypothesis

- 内容: **degraded BC 用 Fano + chain rule** (`n·R_2 ≤ I(W_2; Y_2^n) + n·ε_n`, `n·R_1 ≤ I(W_1; Y_1^n | W_2) + n·ε_n`, per-letter chain rule)
- 規模: ~300-500 行
- 縮退: `_h_fano : True` + `_h_chain : True` placeholder slot 2 件
- discharge plan: `bc-converse-fano-discharge-*`, `bc-converse-chain-rule-discharge-*`

### L-BC3 (確定発動): superposition decoder existence

- 内容: **achievability 全体を `h_existence` hypothesis pass-through 化**
- 規模: ~200-400 行 (superposition decoder の存在証明本体)
- 縮退: `h_existence : BCInnerBoundExistence ...` slot を `bc_capacity_region_inner_bound` signature に確保
- 主定理 body は `:= h_existence` の identity wrap
- discharge plan: `bc-superposition-decoder-discharge-*`

### L-BC4 (確定発動): outer bound rate hypothesis

- 内容: **converse 全体を `h_rate_bound : InBCCapacityRegion ...` hypothesis pass-through 化**
- 規模: ~300-500 行
- 縮退: `h_rate_bound : InBCCapacityRegion R₁ R₂ I_u I_xy` slot 確保
- 主定理 body は `:= h_rate_bound` の identity wrap
- discharge plan: `bc-converse-rate-bound-discharge-*`

### L-BC5 (確定発動): general (non-degraded) BC scope-out

- 内容: **degraded BC のみ publish**、一般 BC (`Marton inner bound` / `Körner-Marton outer bound`) は完全 scope-out
- 規模: ~1000-2000 行 (一般 BC の inner / outer bound は当時未解決問題)
- 縮退: file 全体を degraded BC に限定、auxiliary RV `U` は 1 個のみ
- discharge plan: `bc-general-discharge-*` (将来 seed)

## §5. ファイル設計 (Phase A skeleton 出力先)

```
InformationTheory/Shannon/
  BroadcastChannel.lean       ← 新規 ~700-1150 行 (撤退ライン 5 本全発動下)
    ・file docstring: Cover-Thomas Ch.15.6 reference + 撤退ライン L-BC1〜5 列挙
    ・namespace InformationTheory.Shannon
    ・BroadcastChannel α β₁ β₂ := Kernel α (β₁ × β₂) abbrev
    ・BroadcastCode structure (encoder + decoder₁ + decoder₂)
    ・BroadcastCode helpers (decodingRegion₁/₂, errorEvent₁/₂)
    ・InBCCapacityRegion (R₁ R₂ I_u I_xy : ℝ) : Prop predicate
    ・InBCCapacityRegion 補題 (mk', iff_and, swap-like, mono, anti_mono, zero_zero)
    ・Single-rate cut bounds (statement-level pass-through)
    ・bc_capacity_region_outer_bound (converse 主定理, L-BC2 + L-BC4 engage)
    ・bc_capacity_region_outer_bound_two_bounds (3-bound combine 経由)
    ・bc_capacity_region_outer_bound_log_rate (Real.log M_k / n 形)
    ・BCInnerBoundExistence definition
    ・bc_capacity_region_inner_bound (achievability 主定理, L-BC1 + L-BC3 engage)
    ・bc_capacity_region_consistent (両側 combine)
```

## §6. 設計判断記録

### 6.1 `BroadcastChannel` を `Kernel α (β₁ × β₂)` で abbrev する (`Kernel α β₁ × Kernel α β₂` の積構造ではなく)

- **採用**: `Kernel α (β₁ × β₂)`
- **理由**: 一般 BC の数学定義は **joint distribution `p(y_1, y_2 | x)`** であり、独立 product `p(y_1|x) p(y_2|x)` ではない。degraded BC `X → Y_1 → Y_2` は joint distribution の特殊形 (Markov chain) で、構造体段階では joint distribution を持つことが必須。
- **degraded 仮定**: 主定理 signature では受け取らず、`InBCCapacityRegion` predicate で受け取ると **converse の Fano + chain rule の発動条件**としてのみ要求される。degraded 仮定の機械化 (Markov chain `IsMarkovChain X Y_1 Y_2`) は L-BC2 の中で扱う (本 file では type-level 参照のみ)。

### 6.2 `InBCCapacityRegion` を **2 inequality** で書く (`R_2 ≤ I_u` + `R_1 ≤ I_xy`)

- **採用**: 2 inequality structure
- **理由**: degraded BC の Cover-Thomas Theorem 15.6.2 は **2 inequality** のみ (MAC は 3 inequality)。一般 BC (non-degraded) は 3+ inequality + auxiliary RV を 2 個以上に拡張する必要があるが、これは scope-out (L-BC5)。
- **命名**: `bound_R₂_le_I_u : R₂ ≤ I_u`, `bound_R₁_le_I_xy : R₁ ≤ I_xy` (両 receiver の論理対称性を保つ)

### 6.3 `BroadcastCode` を **decoder × 2** で書く (`decoder : (Fin n → β₁ × β₂) → Fin M₁ × Fin M₂` ではなく)

- **採用**: 独立 `decoder₁ : (Fin n → β₁) → Fin M₁` + `decoder₂ : (Fin n → β₂) → Fin M₂`
- **理由**: BC の本質は **物理的に独立な 2 receiver** が独自の channel output `β_k` だけから自分宛 message を decode する。joint observation `(β₁, β₂)` を 1 decoder で見るのは数学的には許されるが、operational meaning と乖離する。
- **Mathlib-shape-driven**: `decodingRegion₁`, `errorEvent₁`, `decodingRegion₂`, `errorEvent₂` の 4 つの helper が自然に出る → 各 receiver のエラー解析を独立に進められる。

### 6.4 `BroadcastCode.encoder` を **`Fin M₁ × Fin M₂ → (Fin n → α)`** で書く (`Fin M₁ → Fin M₂ → ...` の curry 形ではなく)

- **採用**: `Fin M₁ × Fin M₂ → (Fin n → α)` (un-curry 形)
- **理由**: superposition coding は `(U, X) ~ p(u) p(x|u)` で **同時生成**、un-curry 形が encoder の operational shape と整合。curry 形は decoder 2 つに `m₁ m₂ ↦ encoder.snd m₁ m₂` のような nested λ を強制する。
- **`MACCode` との対称**: MAC は `encoder₁ : Fin M₁ → ...`, `encoder₂ : Fin M₂ → ...` (independent) なので un-curry 不要。BC は **bundled** なので un-curry 形が自然。

## §7. Phase A skeleton (~80 行 — 本 inventory 内 prelim)

```lean
import InformationTheory.Shannon.ChannelCoding
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.MIChainRule

namespace InformationTheory.Shannon
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

abbrev BroadcastChannel (α β₁ β₂ : Type*)
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂] :=
  Kernel α (β₁ × β₂)

structure BroadcastCode (M₁ M₂ n : ℕ) (α β₁ β₂ : Type*)
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂] where
  encoder  : Fin M₁ × Fin M₂ → (Fin n → α)
  decoder₁ : (Fin n → β₁) → Fin M₁
  decoder₂ : (Fin n → β₂) → Fin M₂

structure InBCCapacityRegion (R₁ R₂ I_u I_xy : ℝ) : Prop where
  bound_R₂_le_I_u  : R₂ ≤ I_u
  bound_R₁_le_I_xy : R₁ ≤ I_xy

end InformationTheory.Shannon
```

## §8. Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| `BroadcastCode.encoder` un-curry 形が後続 discharge plan で扱いにくい | 中 | 中 | `MultipleAccessChannel.lean` の `MACCode` (encoder × 2) との対比を明示し、un-curry の operational rationale を docstring に |
| `InBCCapacityRegion` 2 inequality が一般 BC への将来拡張で破れる | 低 | 低 | scope を degraded BC に限定 (L-BC5)、一般 BC は別 seed |
| `Kernel α (β₁ × β₂)` codomain product が degraded 仮定の自動 derive を妨げる | 低 | 低 | degraded 仮定は主定理 signature で受け取らず、L-BC2 discharge 内で発動 |
| MAC pattern を踏襲しすぎて BC 固有の auxiliary RV `U` 構造が表面化しない | 中 | 中 | `InBCCapacityRegion (R₁ R₂ I_u I_xy : ℝ)` の引数命名 (`I_u`, `I_xy`) で `U` 構造を type-level に露出、`U` 自体は scalar `I_u : ℝ` に圧縮 |
| 主定理 body 長さが seed 上限 (1150) を超過 | 低 | 低 | L-BC1〜5 全発動下で MAC (637 行) +50-100 行で収まる見込み |

---

## §9. 参照

- 親 seed: [`textbook-roadmap.md`](../textbook-roadmap.md) Tier 3 T3-C
- sibling plan: [`broadcast-channel-moonshot-plan.md`](./broadcast-channel-moonshot-plan.md)
- 直接の雛形:
  - [InformationTheory/Shannon/MultipleAccessChannel.lean](../../InformationTheory/Shannon/MultipleAccessChannel.lean) (637 行)
  - [mac-mathlib-inventory.md](./mac-mathlib-inventory.md)
  - [mac-moonshot-plan.md](./mac-moonshot-plan.md)
- pattern reference:
  - [relay-cutset-mathlib-inventory.md](./relay-cutset-mathlib-inventory.md) (converse 側)
  - [wyner-ziv-mathlib-inventory.md](./wyner-ziv-mathlib-inventory.md) (achievability 側 + auxiliary RV)
