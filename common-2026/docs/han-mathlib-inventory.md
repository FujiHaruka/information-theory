# Han 不等式 — Mathlib + 既存 Shannon API インベントリ (Phase 0 / M0)

> **Status (2026-05-10)**: Phase 0 (M0) 調査完了。次: Phase A skeleton (`Common2026/Shannon/Entropy.lean`) を sorry-driven で書き始める。
>
> 親計画: [`han-moonshot-plan.md`](han-moonshot-plan.md)

## 結論 (TL;DR)

1. **Mathlib に Han / Shearer / 一般化エントロピー不等式は存在しない** ─ 計画破棄ラインはクリア。
2. **既存 `Common2026/Shannon` API は n 変数化に耐える** ─ `Fin n → α` 上で必要な instance チェインはすべて Mathlib 既存 instance で自動発火する見込み。Phase B の最大想定リスクは消えた。
3. **Phase A 中間補題 `condMutualInfo_eq_condEntropy_sub_condEntropy` の所要量を 150〜200 行に再見積もり** ─ Bridge.lean の証明骨格を「fiber 上で呼ぶ」ことで写経不要。

---

## (1) Mathlib 探索 (Han / Shearer / 類縁)

### loogle 全クエリ結果

| クエリ | 結果 |
|--------|------|
| `Han` | Found 0 declarations (unknown identifier) |
| `Shearer` | Found 0 declarations (unknown identifier) |
| `entropy_pair_le` | Found 0 declarations |
| `entropy_sum_le` | Found 0 declarations |
| `\|- _ * entropy _ _ ≤ _` | Found 0 declarations |

### rg テキスト探索

| クエリ | hit |
|--------|-----|
| `rg -i 'han'` `Mathlib/InformationTheory/` | 0 |
| `rg -i 'shearer'` 全 Mathlib | 0 |
| `rg 'fractional.*cover\|fractional.*entropy'` | 0 |

### Mathlib InformationTheory 棚卸し (関連箇所)

- `Hamming.lean` ─ Hamming 距離 (符号理論、情報理論ではない)
- `KullbackLeibler/{Basic,ChainRule,...}` ─ KL 発散と chain rule (これは既に Common2026 が活用)
- `Coding/` ─ Kraft-McMillan 定理

**Shannon 熵フレームワーク自体が Mathlib に未実装** (joint / marginal / conditional いずれも `Common2026/Shannon` が自前)。Han 不等式は完全自前。

---

## (2) 既存 `Common2026/Shannon` API の n 変数耐性

### 主要 API インベントリ (Phase A / B から呼ぶもの)

| 定義 / 定理 | 場所 | signature 要件 (codomain X) | 備考 |
|-------------|------|------------------------------|------|
| `entropy μ Xs` | `Bridge.lean:42-44` | `[Fintype X] [DecidableEq X] [Nonempty X] [MS X] [MSC X]` | Phase 3 / 4-β、ℝ 値 |
| `condEntropy μ Xs Yo` | `Fano/Measure.lean` (`InformationTheory.MeasureFano.condEntropy`) | X 側に `[Fintype]` 系 / Y 側 `[MS]` のみ | ℝ 値 |
| `mutualInfo μ Xs Yo` | `MutualInfo.lean:36-39` | `[MS X] [MS Y]` のみ | ℝ≥0∞ 値 |
| `mutualInfo_eq_entropy_sub_condEntropy` (Bridge) | `Bridge.lean:579-587` | `[Fintype X] [DEq X] [Nonempty X] [MS X] [MSC X]`, Y は `[MS]` のみ | Phase 4-β 主橋渡し、ℝ 値で結ぶ |
| `condMutualInfo μ Xs Yo Zc` | `CondMutualInfo.lean:46-52` | **`[StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]`**, Z は `[MS]` のみ | ℝ≥0∞ 値、compProd 形定義 |
| `mutualInfo_chain_rule` | `CondMutualInfo.lean:219-227` | 上に同じ | `I((Z, X); Y) = I(Z; Y) + I(X; Y \| Z)` (mutualInfo 形) |

**注意**: `condMutualInfo` の codomain 要件が Bridge より厳しい (`[Fintype]`系 → `[StandardBorelSpace]`)。Phase A 中間補題で X / Y に `[Fintype + MSC]` を喰わせるとき、SBS が自動発火するか要確認 → 下記 (3) で確認済 (発火する)。

### `Fin n → α` への instance チェイン自動発火確認

調査クエリ:

```text
loogle "MeasurableSingletonClass (∀ _, _)" → Pi.instMeasurableSingletonClass
loogle "StandardBorelSpace (∀ _, _)" → StandardBorelSpace.pi_countable
loogle "MeasurableSingletonClass (Subtype _)" → Subtype.instMeasurableSingletonClass
```

各 instance の signature (verbatim):

```lean
-- Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:720
instance Pi.instMeasurableSingletonClass [Countable δ]
    [∀ a, MeasurableSingletonClass (X a)] :
    MeasurableSingletonClass (∀ a, X a)

-- Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:150
instance pi_countable {ι : Type*} [Countable ι] {α : ι → Type*}
    [∀ n, MeasurableSpace (α n)] [∀ n, StandardBorelSpace (α n)] :
    StandardBorelSpace (∀ n, α n)

-- Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:549
instance (priority := 100) MeasurableSingletonClass.toDiscreteMeasurableSpace
    [MeasurableSpace α] [MeasurableSingletonClass α] : DiscreteMeasurableSpace α
```

加えて、Fano/Measure.lean の冒頭コメント (`:25-27`) が confirm:

> `condDistrib` の `StandardBorelSpace` 要求は出力側の型に課されるが、
> 本定理での出力は `DiscreteMeasurableSpace → StandardBorelSpace` が自動で derive される。

つまり instance 発火の chain は次の通り:

```
[Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
   ↓ MeasurableSingletonClass.toDiscreteMeasurableSpace (priority 100)
[DiscreteMeasurableSpace α]
   ↓ Mathlib 経路 (DMS → SBS)
[StandardBorelSpace α]

Pi 側:
[Countable (Fin n)] (auto) + [∀ i, MeasurableSingletonClass α]
   ↓ Pi.instMeasurableSingletonClass
[MeasurableSingletonClass (Fin n → α)]
   ↓ ditto chain (DMS → SBS)
[StandardBorelSpace (Fin n → α)]

補集合 {j // j ≠ i}:
   ↓ Subtype.instMeasurableSingletonClass + Subtype.fintype + Subtype.countable
すべて自動
```

**結論**: Phase B で `entropy μ (fun ω => fun i => Xs i ω)` および `entropy μ (fun ω => fun (j : {j // j ≠ i}) => Xs j ω)` を書き下すとき、必要な instance チェインはすべて自動発火する見込み。手動 instance の追加は要らない。

ただし **`StandardBorelSpace` が「`[Fintype + MSC]` から `DiscreteMeasurableSpace` 経由で出る」具体経路は loogle で 0 件** (`StandardBorelSpace, Fintype` 直撃で Found 0)。Fano/Measure.lean が現に動いているので chain は通っているが、Phase A skeleton 着手時に念のため `lake env lean` で 1 回 type-check を走らせて instance 発火を確認する (skeleton-driven の常套)。

### `condMutualInfo` の Z 引数が `[MS]` のみで済む利点

Phase B で `condEntropy_le_condEntropy_of_pair` を `Fin n` の prefix に適用するとき、prefix `Fin i → α` を Z (条件付け側) に喰わせる経路が使える。Z 側に `[StandardBorelSpace]` が要らないので、たとえ pi_countable 経由の SBS 発火が引っかかっても Z 側だけは確実に通る。設計上の保険になる。

---

## (3) Phase A 中間補題 `condMutualInfo_eq_condEntropy_sub_condEntropy` 所要量

### 目標 signature

```lean
/-- I(X; Z | Y) = H(X | Y) - H(X | Y, Z). -/
theorem condMutualInfo_eq_condEntropy_sub_condEntropy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (Zo : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZo : Measurable Zo) :
    (condMutualInfo μ Xs Zo Yo).toReal
      = condEntropy μ Xs Yo - condEntropy μ Xs (fun ω => (Yo ω, Zo ω))
```

### 当初見積もり: 100〜200 行 → **再見積もり: 150〜200 行**

### 戦略 (Bridge fiber 再利用ルート)

`condMutualInfo` は compProd 形 (両 base が `μ.map Yo` 共通) で定義されているので、**fiber-wise klDiv chain rule (`klDiv_compProd_const_eq_lintegral_of_ac`、Bridge.lean の Helper 1)** を直接適用できる:

```
condMutualInfo μ Xs Zo Yo
  = klDiv ((μ.map Yo) ⊗ₘ K_joint) ((μ.map Yo) ⊗ₘ (K_X ×ₖ K_Z))
  = ∫⁻ y, klDiv (K_joint y) ((K_X y).prod (K_Z y)) ∂(μ.map Yo)        ← Bridge Helper 1
  = ∫⁻ y, mutualInfo (条件分布 K_joint y) (K_X y) (K_Z y)              ← per-fiber MI
```

**fiber 上で `mutualInfo_eq_entropy_sub_condEntropy` (Bridge 主定理) を呼べる**。Bridge 全体 (~190 行) の写経は不要。

### 内訳見立て

| 部品 | 行数 | 補足 |
|------|------|------|
| compProd 形 → fiber-wise klDiv 展開 (`klDiv_compProd_const_eq_lintegral_of_ac` 直接適用) | 30 | Bridge Helper 1 を再利用 |
| fiber 上で Bridge 主定理を呼ぶ + ENNReal/ℝ の往復整理 | 30 | `integral_toReal` + `lintegral_congr_ae` |
| `condEntropy` tower 補題: `H(X \| Y, Z) = ∫ z, H_z(X \| Y) d(μ.map Z)` | 50 | Tonelli + condEntropy 定義展開、新規 (要 derive) |
| `condEntropy μ Xs (fun ω => (Yo, Zo))` を tower 経由で書き直す | 30 | iterated integral plumbing |
| 最終合成 (linarith / ring) | 20 | |
| **計** | **150〜160** | |

### 別ルート (退路)

撤退ライン (han-moonshot-plan.md の失敗判定セクション参照):

> Phase A の `condMutualInfo_eq_condEntropy_sub_condEntropy` 中間補題で 1 週間溶ける場合
> → Phase A を `entropy_pair_eq_entropy_add_condEntropy` のみで打ち止めにし、
> Phase B 着手は条件付けでエントロピーが減る部分を「KL chain rule から直接 Han 用に局所証明」する経路に倒す

この退路では中間補題を諦め、Han 本体の証明内で「fiber 上 chain rule + DPI」を直接走らせる。コード重複は出るが Phase A 単独定理として publish はしない代わりに進む。

---

## (4) 計画書への反映 (han-moonshot-plan.md 更新点)

Phase 0 結果を踏まえた **calling-card 級の更新は不要**。当初の見立て (Phase A 100〜200 行 / Phase B Pi instance 自動発火期待) はおおむね正しかった。微修正のみ:

- **Phase A 「鍵となる作業」#2** に「**Bridge.lean Helper 1 を fiber 上で呼び、Bridge 主定理を fiber 上で再利用するルート**」を明記 (Bridge 写経しない判断を明文化)
- **Phase A 工数感**: `100〜200 行` → `150〜200 行 (Bridge fiber 再利用ルート想定)`
- **Phase B 最大リスク** に書いた「`Fin n` Pi-値 RV measurability で 1 週間溶ける」は instance チェイン裏取り済みのため **下方修正** (Phase 0 で発火経路 confirm 済 / 残るのは skeleton 書き起こし時の type-check 1 発のみ)

---

## (5) 次の一手 (Phase A 着手準備)

1. `Common2026/Shannon/Entropy.lean` の skeleton を sorry-driven で書く
   - 必要 import: `Common2026.Shannon.Bridge` + `Common2026.Shannon.CondMutualInfo` + 関連 Mathlib
   - 主定理 3 つ (chain rule / 中間補題 / `condEntropy_le_condEntropy_of_pair`) を `:= by sorry` で並べる
   - skeleton type-check (`lake env lean Common2026/Shannon/Entropy.lean`) で instance 発火を確認
2. sorry を 1 つずつ割る順序: `entropy_pair_eq_entropy_add_condEntropy` → `condMutualInfo_eq_condEntropy_sub_condEntropy` → `condEntropy_le_condEntropy_of_pair`
3. (中間補題に着手する直前に) `condEntropy` tower 補題の skeleton を別途追加
