# T3-F Relay Inner Bound (DF/CF) ムーンショット計画 🌙

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-F. Relay
>   Channel + Cut-set bound」(inner bound 半部)
>
> **Predecessor seed (publish 済 2026-05-19、本 plan の対称項)**:
> - `Common2026/Shannon/RelayCutset.lean` — T3-F outer bound (cut-set),
>   386 行 / 0 sorry / 0 warning, L-RC1〜5 全 pass-through。
> - `Common2026/Shannon/MultipleAccessChannel.lean` — T3-B, 637 行,
>   **`mac_capacity_region_inner_bound` (achievability existence-form
>   pass-through)** が本 plan 主定理 `relay_df_inner_bound` /
>   `relay_cf_inner_bound` の直接の雛形。
>
> **Inventory (Phase 0 を本 plan と並行起草)**:
> [`relay-inner-bound-mathlib-inventory.md`](./relay-inner-bound-mathlib-inventory.md)
>
> **Goal (短形)**: 新規 1 ファイル `Common2026/Shannon/RelayInnerBound.lean`
> で Cover-Thomas Theorem 15.10.2 (decode-and-forward inner bound) +
> Theorem 15.10.3 (compress-and-forward inner bound) を **両方 statement-level
> hypothesis pass-through** で publish。0 sorry / 0 warning、規模 ~350-500 行
> (中央 400、撤退ライン L-RI1〜L-RI4 全発動下)。
>
> **撤退ライン (確定発動 4 本)**: [L-RI1] block Markov encoding (DF) →
> `_h_block_markov : True` placeholder / [L-RI2] sliding-window decoder (DF)
> → `_h_sliding_window : True` placeholder / [L-RI3] Wyner-Ziv binning (CF)
> → `_h_wz_binning : True` placeholder / [L-RI4] side-information decoding
> (CF) → `_h_si_decode : True` placeholder。主定理 body は `:= h_existence`。

## Status (2026-05-20)

**Phase 0 完了予定 (起草中)** — outer bound (T3-F) + MAC inner bound (T3-B)
の publish pattern 流用で signature 完全確定。本 plan は MAC achievability
publish (`mac_capacity_region_inner_bound`) の **単一-rate 縮退 + relay
channel structure 流用** で signature 同型に書ける。新 Mathlib API
要求: ゼロ。

## 進捗

- [ ] Phase 0 — Mathlib + 既存 Common2026 在庫 + 設計確定 📋 → [`relay-inner-bound-mathlib-inventory.md`](./relay-inner-bound-mathlib-inventory.md)
- [ ] Phase A — `InRelayDFRate` + `InRelayCFRate` + Existence defs + skeleton 📋
- [ ] Phase B — DF inner bound 主定理 + helpers 📋
- [ ] Phase C — CF inner bound 主定理 + helpers 📋
- [ ] Phase D — docstring + cross-link comments 📋
- [ ] Phase V — `lake env lean` clean (`Common2026.lean` 編入はオーケストレータ判断) 📋

## ゴール / Approach

### 最終到達点 (Phase C 完成形)

新規 1 ファイル合流形:

```lean
import Common2026.Shannon.RelayCutset

namespace InformationTheory.Shannon

/-- DF rate region predicate (Cover-Thomas (15.232) form, 2 不等式 bundle). -/
structure InRelayDFRate (R Imrh Iry Ibroad : ℝ) : Prop where
  boundMAC   : R ≤ Imrh + Iry     -- I(X; Y_1 | X_1) + I(X_1; Y)
  boundBroad : R ≤ Ibroad          -- I(X, X_1; Y)

/-- CF rate region predicate (Cover-Thomas (15.243) + compression feasibility). -/
structure InRelayCFRate (R Idec Ix1y Iy1hy1 : ℝ) : Prop where
  rateBound       : R ≤ Idec       -- I(X; Ŷ_1, Y | X_1)
  compressionFeas : Iy1hy1 ≤ Ix1y  -- I(Y_1; Ŷ_1 | X_1, Y) ≤ I(X_1; Y)

/-- DF achievability existence form (single-rate analogue of `MACInnerBoundExistence`). -/
def RelayDFInnerBoundExistence {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (R : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    ∃ (M : ℕ) (_c : RelayCode M n α α₁ β β₁),
      Real.exp ((n : ℝ) * R) ≤ (M : ℝ)

/-- CF achievability existence form. -/
def RelayCFInnerBoundExistence {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (R : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    ∃ (M : ℕ) (_c : RelayCode M n α α₁ β β₁),
      Real.exp ((n : ℝ) * R) ≤ (M : ℝ)

/-- **T3-F DF inner bound (Cover-Thomas 15.10.2, hypothesis pass-through)**. -/
theorem relay_df_inner_bound
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (R Imrh Iry Ibroad : ℝ)
    (_h_in_df_region : InRelayDFRate R Imrh Iry Ibroad)
    (_h_block_markov : True) (_h_sliding_window : True)
    (h_existence :
        RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  h_existence

/-- **T3-F CF inner bound (Cover-Thomas 15.10.3, hypothesis pass-through)**. -/
theorem relay_cf_inner_bound
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (R Idec Ix1y Iy1hy1 : ℝ)
    (_h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1)
    (_h_wz_binning : True) (_h_si_decode : True)
    (h_existence :
        RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  h_existence

end InformationTheory.Shannon
```

### Approach (overall strategy / shape of solution)

**戦略の shape** — T3-F inner bound は T3-B MAC inner bound と同じ
**statement-level hypothesis pass-through pattern** の relay 版 (単一-rate
への縮退 + DF/CF それぞれの achievability 構造ごとに placeholder 2 本):

```
[T3-B MAC inner bound pattern]                  [T3-F Relay inner bound pattern]

 InMACCapacityRegion (3 不等式 bundle)            InRelayDFRate (2 不等式 bundle)
 MACInnerBoundExistence (R₁, R₂)                 RelayDFInnerBoundExistence (R)
              ▼                                                ▼
 mac_capacity_region_inner_bound                  relay_df_inner_bound
   + _h_strict triple                                + _h_in_df_region : InRelayDFRate
   + _h_joint_typ : True                             + _h_block_markov : True
   + h_existence                                     + _h_sliding_window : True
                                                     + h_existence
   body := h_existence                                body := h_existence
              ▼                                                ▼
 L-MAC1/2/3/5 (5本) 全発動で publish               L-RI1/2/3/4 (4本) 全発動で publish
```

**鍵となる構造構築** (Phase A の核): `RelayChannel` + `RelayCode` の構造定義は
既に `RelayCutset.lean` に publish 済 — 本 plan では **再宣言せず import 経由
reuse**。新規構造は `InRelayDFRate` (2 不等式 structure) + `InRelayCFRate`
(2 不等式 structure) + 2 つの existence form (MAC pattern の単一-rate 縮退)
のみ。命名衝突のリスクは 0 (DF/CF の predicate 名は relay namespace で未使用)。

**鍵となる設計選択** (DF rate の form): Cover-Thomas (15.232) 形

```
R ≤ min { I(X; Y₁ | X₁) + I(X₁; Y),  I(X, X₁; Y) }
```

を採用、3 scalar `Imrh` (`I(X; Y_1 | X_1)`) + `Iry` (`I(X_1; Y)`) + `Ibroad`
(`I(X, X_1; Y)`) を受ける形で `min { Imrh + Iry, Ibroad }` を構成。本 file 内
で足し算 `Imrh + Iry` を完結することで callers から見て **scalar pre-computed**
シナリオ + **MI raw** シナリオの両対応。

**鍵となる設計選択** (CF rate の form): Cover-Thomas (15.243) 形

```
R ≤ I(X; Ŷ₁, Y | X₁)   s.t.   I(X₁; Y) ≥ I(Y₁; Ŷ₁ | X₁, Y)
```

を採用、3 scalar `Idec` (`I(X; Ŷ_1, Y | X_1)`) + `Ix1y` (`I(X_1; Y)`) +
`Iy1hy1` (`I(Y_1; Ŷ_1 | X_1, Y)`) を受ける形で 2 不等式を bundle。auxiliary
`Ŷ_1` は本 file 内では構造に embed しない (scalar で外から受ける)。

**Mathlib-shape-driven の設計選択** — `InRelayDFRate` / `InRelayCFRate` を
`structure` (3 構成子+) で書くことで:
1. field projection (`.boundMAC`, `.boundBroad`, `.rateBound`,
   `.compressionFeas`) が namespace dot-notation で使える;
2. `mk'` / `iff_and` helper で unbundled `∧` 形と相互変換が直接書ける;
3. `mono_Imrh`, `mono_Iry`, `mono_Ibroad`, `anti_mono_R` 等の単調性
   ライブラリが MAC `InMACCapacityRegion.mono_I₁` の verbatim 雛形で書ける。

T3-B MAC で確立済の API 完全踏襲。

**ansatz pass-through 設計** — DF/CF 主定理の signature で

```lean
theorem relay_df_inner_bound (R Imrh Iry Ibroad : ℝ)
    (_h_in_df_region : InRelayDFRate R Imrh Iry Ibroad)
    (_h_block_markov : True) (_h_sliding_window : True)
    (h_existence : RelayDFInnerBoundExistence … R) :
    RelayDFInnerBoundExistence … R := h_existence
```

を **呼び出し側の責務**として外から要求。本 plan 内では型整合 + namespace +
docstring のみ整備。L-RI1 / L-RI2 / L-RI3 / L-RI4 を後続 plan
(`relay-df-block-markov-discharge-*`, `relay-df-sliding-window-discharge-*`,
`relay-cf-wz-binning-discharge-*`, `relay-cf-si-decode-discharge-*`) で
discharge 可能。

### Approach 図

```
Phase 0  : Mathlib + Common2026 在庫 + 設計確定                          ← 完了予定 (本 plan 起草と並行)
           ────────────────────────────────────────────────────────────
Phase A  : InRelayDFRate + InRelayCFRate + Existence defs + skeleton    ← ~100-150 行
           ────────────────────────────────────────────────────────────
Phase B  : DF inner bound 主定理 + helpers (mono / log-rate / two-side) ← ~100-150 行
           ←──── 撤退ライン L-RI1 (block Markov pass-through) ────────→
           ←──── 撤退ライン L-RI2 (sliding-window pass-through) ──────→
           ────────────────────────────────────────────────────────────
Phase C  : CF inner bound 主定理 + helpers                              ← ~100-150 行
           ←──── 撤退ライン L-RI3 (WZ binning pass-through) ──────────→
           ←──── 撤退ライン L-RI4 (SI decoding pass-through) ─────────→
           ────────────────────────────────────────────────────────────
Phase D  : two-side combine (outer + inner) + log-rate wrappers          ← ~50-80 行
Phase V  : lake env lean clean                                          ← ~5-10 行
```

### 規模見積

| Phase | 中央予測 | 範囲 | 出力 |
|---|---|---|---|
| Phase 0 | — | — | `relay-inner-bound-mathlib-inventory.md` (~250 行) |
| Phase A | **120 行** | 100-150 | structures + defs + skeleton |
| Phase B | **120 行** | 100-150 | DF inner bound + helpers |
| Phase C | **110 行** | 100-150 | CF inner bound + helpers |
| Phase D | **60 行** | 50-80 | log-rate wrappers + two-side (outer combine) |
| Phase V | **5 行** | 5-10 | verify only (Common2026.lean は外出し) |
| **累計** | **415 行** | **350-500** | 1 ファイル合計 |

### ファイル構成

```
Common2026/Shannon/
  RelayInnerBound.lean   ← 新規 (~400 行) — Cover-Thomas Ch.15.10.2 + 15.10.3
                            ・InRelayDFRate / InRelayCFRate (predicate structures)
                            ・RelayDFInnerBoundExistence / RelayCFInnerBoundExistence (defs)
                            ・relay_df_inner_bound / relay_cf_inner_bound (主定理)
                            ・rate region helpers (mk', iff_and, mono_*, anti_mono_*)
                            ・log-rate wrappers
                            ・two-side outer+inner combine (optional)
```

### 単一ファイル戦略の判断根拠

1. **規模 ~400 行** — DF + CF 両方 publish (撤退ライン 4 本全発動) で 350-500
   行に収まる。`lake env lean` 5-10 秒 inner loop。
2. **数学的単位の一体性** — DF と CF は inner bound の 2 つの構成法、互いに
   refer する docstring が多い。分離するとコメント冗長。
3. **既存先例との整合** — `MultipleAccessChannel.lean` (637 行) が outer + inner
   両方 publish 同一 file の前例。
4. **撤退ライン影響範囲が file 全体** — L-RI1〜4 全てが主定理 signature に影響、
   file 分離しても繰り返すだけで冗長。

## 依存関係

完了済 (黒箱 reuse):

- [x] `Common2026/Shannon/RelayCutset.lean:96` — `RelayChannel`
- [x] `Common2026/Shannon/RelayCutset.lean:115` — `RelayCode`
- [x] `Common2026/Shannon/MultipleAccessChannel.lean:531` — `MACInnerBoundExistence` (signature 直接の雛形)
- [x] `Common2026/Shannon/MultipleAccessChannel.lean:567` — `mac_capacity_region_inner_bound` (主定理直接の雛形)
- [x] Mathlib `Mathlib/Analysis/SpecialFunctions/Exp.lean` — `Real.exp`
- [x] Mathlib `Mathlib/Order/MinMax.lean` — `min_le_iff`, `le_min`

## 撤退ライン

### Scope 縮小ライン (L-RI シリーズ — 4 件全発動)

- **L-RI1 (確定発動)**: **block Markov encoding (DF achievability の構造的
  根幹) を `_h_block_markov : True` placeholder pass-through 化**
  - 発動条件 (確定): Cover-Thomas 15.10.2 の B blocks random codebook +
    段階的 cooperation の構成は ~600-1000 行
  - 縮退後: 主定理 signature に `_h_block_markov : True` slot を確保、別 plan
    `relay-df-block-markov-discharge-*` で discharge
  - **工数削減**: ~600-1000 行

- **L-RI2 (確定発動)**: **sliding-window joint typicality decoder (DF) を
  `_h_sliding_window : True` placeholder pass-through 化**
  - 発動条件 (確定): 各 block の段階的 decoding と error event collapse は
    ~400-600 行
  - 縮退後: `_h_sliding_window : True` slot、別 plan
    `relay-df-sliding-window-discharge-*` で discharge
  - **工数削減**: ~400-600 行

- **L-RI3 (確定発動)**: **Wyner-Ziv binning (CF) を `_h_wz_binning : True`
  placeholder pass-through 化**
  - 発動条件 (確定): compression with side info の random binning ~500-700 行
  - 縮退後: `_h_wz_binning : True` slot、別 plan
    `relay-cf-wz-binning-discharge-*` で discharge
  - **工数削減**: ~500-700 行

- **L-RI4 (確定発動)**: **side-information decoding (CF) を
  `_h_si_decode : True` placeholder pass-through 化**
  - 発動条件 (確定): Ŷ_1 reconstruction + final decoding ~300-500 行
  - 縮退後: `_h_si_decode : True` slot、別 plan
    `relay-cf-si-decode-discharge-*` で discharge
  - **工数削減**: ~300-500 行

### Risk table

| Risk | 確率 | 影響 | 緩和策 |
|---|---|---|---|
| `Real.exp` の型推論で詰まる (`(n : ℝ)`/`(M : ℝ)` cast) | 低 | 低 | MAC pattern verbatim で動いている、同形で動くはず |
| `InRelayDFRate` の `boundMAC : R ≤ Imrh + Iry` が field 名の `MAC` 文字列衝突 | 低 | 低 | field 名は局所、collision 危険 0 |
| `RelayDFInnerBoundExistence` の `RelayCode` の implicit instance 推論で詰まる | 中 | 中 | MAC でも同じ pattern で動いている、`(α := α) (α₁ := α₁)` 等の explicit instance argument 注入で確実 |
| 1 セッションで 400 行を書ききれない | 中 | 中 | DF / CF を別ターンに分割可、Phase B 完了で DF 単独 publish も有効 |

## 当面の next step

1. **Phase 0 (inventory)** — `relay-inner-bound-mathlib-inventory.md` 起草中
2. **Phase A skeleton** — Phase 0 完了後の次
3. **Phase B DF inner bound + helpers** — ~100-150 行
4. **Phase C CF inner bound + helpers** — ~100-150 行
5. **Phase D log-rate / two-side wrappers** — ~50-80 行
6. **Phase V lake env lean clean**

## 参照

- 親 seed: [`textbook-roadmap.md`](../textbook-roadmap.md) Tier 3 T3-F
- 兄弟 plan (本 plan の直接の雛形):
  - [Relay cutset moonshot (T3-F outer bound)](relay-cutset-moonshot-plan.md)
  - MAC publish (T3-B): `Common2026/Shannon/MultipleAccessChannel.lean`
- 既存実装 (黒箱 reuse):
  - `Common2026/Shannon/RelayCutset.lean:96, :115` — `RelayChannel`, `RelayCode`
  - `Common2026/Shannon/MultipleAccessChannel.lean:531, :567` — MAC inner bound pattern
