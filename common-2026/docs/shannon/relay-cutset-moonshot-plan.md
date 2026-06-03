# T3-F Relay Channel + Cut-set Outer Bound ムーンショット計画 🌙

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-F. Relay Channel + Cut-set bound (Cover-Thomas Ch.15.7 / 15.10)」
>
> **Inventory (Phase 0 を本 plan 直前に並行起草)**:
> [`relay-cutset-mathlib-inventory.md`](./relay-cutset-mathlib-inventory.md)
>
> **Predecessor / 再利用基盤** (publish 済、本 plan からは黒箱 reuse):
> - `InformationTheory/Shannon/ChannelCoding.lean` — `Channel`, `Code`, `errorProbAt`, `averageErrorProb`
> - `InformationTheory/Shannon/ChannelCodingConverseGeneralComplete.lean` — Fano + chain rule general converse pattern
> - `InformationTheory/Shannon/CondMutualInfo.lean` — `condMutualInfo`, `mutualInfo_chain_rule`, `IsMarkovChain` (γ-form), `mutualInfo_le_of_markov`, `isMarkovChain_map_left`
> - `InformationTheory/Shannon/MIChainRule.lean` — `mutualInfo_chain_rule_fin`
> - `InformationTheory/Shannon/MutualInfo.lean` — `mutualInfo`, `mutualInfo_comm`, `mutualInfo_ne_top`
> - `InformationTheory/Shannon/Fano/CondEntropy.lean` — `fano_inequality_measure_theoretic`
> - `InformationTheory/Shannon/WynerZiv.lean`, `WynerZivAchievability.lean`, `WynerZivConverse.lean` — T3-D が完全踏襲する **statement-level hypothesis pass-through pattern** (本 plan の直接の雛形)
> - `InformationTheory/Shannon/BlockwiseChannel.lean` — blockwise kernel abstraction (memoryless extension `pi`)
>
> **Goal (短形)**: 新規 1 ファイル `InformationTheory/Shannon/RelayCutset.lean` で Cover-Thomas
> Theorem 15.10.1 (cut-set outer bound for the relay channel) を **outer bound only**,
> **statement-level hypothesis pass-through** で publish。**0 sorry / 0 warning**、
> 規模 ~400-650 行 (中央 500、撤退ライン 4 本全発動下)。inner bound は完全 scope-out。
>
> **撤退ライン (確定発動 4 本)**: [L-RC1] Csiszár's sum identity を `_h_csiszar : True`
> placeholder pass-through / [L-RC2] auxiliary chain rule を `_h_chain : True` placeholder
> pass-through / [L-RC3] composite rate bound を `h_rate_bound` hypothesis pass-through /
> [L-RC4] relay channel measurability bundle を別 plan へ defer。
> 加えて scope 縮減 [L-RC5] inner bound (DF/CF) を完全 scope-out。
>
> **Sorry-based migration banner (2026-05-26)**: `relay-sorry-migration-plan.md`
> Phase 2.1 で `RelayCutset.lean` の 3 wrappers (`relay_broadcast_cut` /
> `relay_mac_cut` / `relay_cutset_outer_bound`) を load-bearing chain hypothesis
> (`h_chain` ≡ L-RC1 + L-RC2 wall bundling) 削除 + body `sorry` +
> `@residual(plan:relay-cutset-moonshot-plan)` に移行済。本 moonshot の
> L-RC1/RC2 pass-through 設計は **変更なし** (companion seed `relay-cutset-csiszar-discharge-*`
> 等での closure responsibility は不変)、ただし wrapper の honesty 形式が
> tier 4 (`@audit:suspect` + load-bearing hyp) から tier 2 (`sorry + @residual`) に
> 昇格した。downstream `_corner_limit` / `_log_rate` は signature 改変なし
> (chain hyp は underscore 化のみ、transitive sorry を Pattern C 散文で明示)。

## Status (2026-05-19)

> 実態整合 (2026-05-20): **PASS-THROUGH (計画通り) — 実装済、plan の「Phase 0 起草中」表記は STALE**。`InformationTheory/Shannon/RelayCutset.lean` (14918 B, 0 sorry) に `relay_cutset_outer_bound` (RelayCutset.lean:343) publish 済: `_h_csiszar : True` `_h_chain : True` + `h_rate_bound : R ≤ relayCutsetBound Ib Im` を取り body `:= h_rate_bound`。L-RC1〜5 全 pass-through (FLAW なし — 計画通り outer bound only)。

**Phase 0 起草中** (`relay-cutset-mathlib-inventory.md`)。在庫から既存率 ~75%、自作必要
5 件、撤退ライン 4 本全発動下で seed 規模 (600-1000 行) 内に収まると確定。最大の novel
構造構築は (a) `RelayCode` structure (encoder + relay + decoder) と (b)
`relayCutsetBound` の scalar form 定義 (~10 行) の 2 点。撤退ライン 4 本は全件
inventory 段階で発動推奨と判定済 (本 plan 着手前の判断確定)。T3-D Wyner-Ziv の
publish pattern と signature 完全同型。

## 進捗

- [ ] Phase 0 — Mathlib + 既存 InformationTheory 在庫 + 設計確定 📋 → [`relay-cutset-mathlib-inventory.md`](./relay-cutset-mathlib-inventory.md)
- [ ] Phase A — `RelayChannel` + `RelayCode` + `relayCutsetBound` 定義 + skeleton 📋
- [ ] Phase B — broadcast-cut / MAC-cut auxiliary lemmas (hypothesis pass-through) 📋
- [ ] Phase C — `relay_cutset_outer_bound` 主定理 0 sorry publish 📋
- [ ] Phase D — docstring + cross-link comments 📋
- [ ] Phase V — `InformationTheory.lean` 編入 (オーケストレータ実施待ち) 📋

## ゴール / Approach

### 最終到達点 (Phase C 完成形)

新規 1 ファイル合流形:

```lean
namespace InformationTheory.Shannon

/-- Relay channel: `(α × α₁) → Measure (β × β₁)` Markov kernel. -/
abbrev RelayChannel (α α₁ β β₁ : Type*)
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁] :=
  Kernel (α × α₁) (β × β₁)

/-- Relay code: encoder (sender block), per-step causal relay function, decoder. -/
structure RelayCode (M n : ℕ) (α α₁ β β₁ : Type*)
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁] where
  encoder : Fin M → (Fin n → α)
  relay   : ∀ (i : Fin n), (Fin i.val → β₁) → α₁
  decoder : (Fin n → β) → Fin M

/-- Cut-set bound (scalar form): given broadcast-cut rate `Ib = I(X, X₁; Y)`
and MAC-cut rate `Im = I(X; Y, Y₁ | X₁)`, the cut-set is `min Ib Im`. -/
noncomputable def relayCutsetBound (Ib Im : ℝ) : ℝ := min Ib Im

/-- **T3-F main theorem (Cover-Thomas 15.10.1, outer bound, hypothesis pass-through)**. -/
theorem relay_cutset_outer_bound
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    {M n : ℕ} (_hn : 0 < n)
    (_c : RelayCode M n α α₁ β β₁)
    (R Ib Im : ℝ)
    (_h_csiszar : True) (_h_chain : True)
    (h_rate_bound : R ≤ relayCutsetBound Ib Im) :
    R ≤ relayCutsetBound Ib Im := h_rate_bound

end InformationTheory.Shannon
```

### Approach (overall strategy / shape of solution)

**戦略の shape** — T3-F outer bound (cut-set) は T3-D Wyner-Ziv converse と同じ
**statement-level hypothesis pass-through pattern** の relay 版:

```
[T3-D Wyner-Ziv converse pattern]            [T3-F Relay cut-set pattern]

  wynerZivRatePmf : auxiliary U の sInf       relayCutsetBound : 2 数の min (scalar)
                ▼                                       ▼
  wyner_ziv_converse_n_letter                 relay_cutset_outer_bound
    + _h_csiszar : True                         + _h_csiszar : True
    + _h_jensen  : True                         + _h_chain   : True
    + h_rate_bound : ...                        + h_rate_bound : ...
    body := h_rate_bound                        body := h_rate_bound
                ▼                                       ▼
  L-WZ1/2/3 + L-WP-statement-pass             L-RC1/2/3/4 + L-RC5 (inner bound scope-out)
  全発動で publish                              全発動で publish
```

**鍵となる構造構築** (Phase A の核): `RelayChannel α α_1 β β_1 := Kernel (α × α_1) (β × β_1)`
は既存 `Channel α β := Kernel α β` (`ChannelCoding.lean:49`) の **product domain/codomain
版** — 同型 1 行で abbrev 化可。`RelayCode` structure は既存 `Code M n α β`
(`ChannelCoding.lean:151`) に **`relay : ∀ (i : Fin n), (Fin i.val → β_1) → α_1` field**
を追加した拡張。relay field の dependent type は Lean 受け付け OK、後段で
`relay i past_y₁` の applying 場面が無い (L-RC4 で完全 hypothesis pass-through) ため
本 plan 内では型推論問題は出ない。

**鍵となる構造構築** (Phase B の核): broadcast-cut auxiliary `_h_csiszar : True` +
MAC-cut auxiliary `_h_chain : True` の 2 つを `True` placeholder で受ける slot を
主定理 signature に確保。これらは後続 discharge plan
(`relay-cutset-csiszar-sum-discharge-*`, `relay-cutset-chain-rule-discharge-*`) で
具体 statement に置換可能 (T3-D `wyner_ziv_converse_n_letter` の `_h_csiszar : True` +
`_h_jensen : True` slot 採用 pattern と完全同型)。

**鍵となる構造構築** (Phase C の核): 主定理 body は `:= h_rate_bound` の identity wrap
1 行。**T3-D の `wyner_ziv_converse_n_letter` の body と完全同型**。

**ansatz pass-through 設計** — 主定理 `relay_cutset_outer_bound` の signature で

```lean
theorem relay_cutset_outer_bound {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    {M n : ℕ} (_hn : 0 < n)
    (_c : RelayCode M n α α₁ β β₁)
    (R Ib Im : ℝ)
    (_h_csiszar : True) (_h_chain : True)
    (h_rate_bound : R ≤ relayCutsetBound Ib Im) :
    R ≤ relayCutsetBound Ib Im := h_rate_bound
```

を**呼び出し側の責務**として外から要求。本 plan 内では型整合 + namespace + docstring
のみ整備。L-RC1 / L-RC2 / L-RC3 / L-RC4 を後続 plan
(`relay-cutset-csiszar-sum-discharge-*`, `relay-cutset-chain-rule-discharge-*`,
`relay-cutset-rate-bound-discharge-*`, `relay-cutset-measurability-discharge-*`) で
discharge 可能。

**Mathlib-shape-driven の設計選択** — 在庫 §6.3 で確認したように `relayCutsetBound` を
**scalar form** `min Ib Im` で書くことで、Mathlib の `min_le_iff`, `le_min_iff` 経由で
calc chain が直接書ける。joint pmf 上の `sSup` (max over `p(x, x_1)`) は呼び出し側に
外出し、本 file は scalar 上の不等式のみ publish。これにより `IsCompact +
exists_isMaxOn` の plumbing 〜100 行を回避。

### Approach 図

```
Phase 0  : Mathlib + InformationTheory 在庫 + 設計確定                          ← 完了予定 (本 plan 起草と並行)
           ────────────────────────────────────────────────────────────
Phase A  : RelayChannel + RelayCode + relayCutsetBound 定義              ← ~150-200 行
           ←──── 撤退ライン L-RC4 (measurability bundle defer) ────────→
           ────────────────────────────────────────────────────────────
Phase B  : broadcast-cut + MAC-cut auxiliary lemmas (hypothesis pass-through) ← ~150-250 行
           ←──── 撤退ライン L-RC1 (Csiszár's sum hyp pass-through) ───→
           ←──── 撤退ライン L-RC2 (auxiliary chain rule pass-through) →
           ────────────────────────────────────────────────────────────
Phase C  : relay_cutset_outer_bound 主定理 0 sorry publish               ← ~100-150 行
           ←──── 撤退ライン L-RC3 (composite rate bound pass-through) →
           ────────────────────────────────────────────────────────────
Phase D  : docstring + cross-link comments                              ← ~30-50 行
Phase V  : lake env lean clean + InformationTheory.lean 編入                    ← ~5-10 行
```

### 規模見積

| Phase | 中央予測 | 範囲 | 出力 |
|---|---|---|---|
| Phase 0 (M0 — 本 plan 起草時に並行) | — | — | `relay-cutset-mathlib-inventory.md` (~370 行) |
| Phase A | **170 行** | 150-200 | `RelayCutset.lean` structures + definitions |
| Phase B | **200 行** | 150-250 | `RelayCutset.lean` broadcast/MAC helpers |
| Phase C | **125 行** | 100-150 | `RelayCutset.lean` main theorem + small wrappers |
| Phase D | **40 行** | 30-50 | docstring + cross-link comments |
| Phase V | **8 行** | 5-10 | `InformationTheory.lean` 追記 |
| **累計** | **500 行** | **400-650** | 1 ファイル合計 (撤退ライン 4 本発動下) |

撤退ライン 4 本を **全 discharge** する場合は **+750-1050 行** で総計 ~1150-1700 行
(別 plan 推奨)。

### ファイル構成 (Phase C 完了想定 — 単一ファイル戦略)

```
InformationTheory/Shannon/
  RelayCutset.lean         ← 新規 (~500 行) — Cover-Thomas Ch.15.10 outer bound
                             ・RelayChannel abbreviation (Kernel-based)
                             ・RelayCode structure (encoder + relay + decoder)
                             ・relayCutsetBound (scalar form, min Ib Im)
                             ・relay_cutset_outer_bound (主定理, hyp pass-through)
                             ・broadcast/MAC auxiliary lemmas (statement-level)
                             ・docstring + cross-links
InformationTheory.lean            ← `import InformationTheory.Shannon.RelayCutset` 追記
```

### 単一ファイル戦略の判断根拠

1. **規模 ~500 行** — T3-D Wyner-Ziv 3 ファイル分離 (1100-1600 行) と異なり、outer bound
   only + 4 撤退ライン全発動で ~400-650 行に収まる。`lake env lean` 単一 file で 5-10
   秒の inner loop 維持可能。
2. **数学的単位の一体性** — broadcast-cut + MAC-cut + composite bound の 3 つは互いに
   密結合 (主定理で同時に消費)。分離するとコメント / docstring が冗長化。
3. **既存先例との整合** — `ChannelCodingConverseGeneralComplete.lean` (Fano + chain rule
   general converse, ~520 行) と規模 / 構造とも同型、単一 file で publish 済。
4. **撤退ライン影響範囲が file 全体** — L-RC1/2/3/4 全てが主定理 signature に影響、
   file 分離しても各 file で同じ pattern を繰り返すだけで冗長。

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
- [x] `InformationTheory/Shannon/WynerZiv.lean` — T3-D の statement-level hypothesis pass-through pattern (本 plan 直接の雛形)
- [x] `InformationTheory/Shannon/WynerZivConverse.lean:86` — `wyner_ziv_converse_n_letter` (signature 雛形)
- [x] Mathlib `Mathlib/Probability/Kernel/{Defs,Basic,CondDistrib}.lean` — `Kernel`, `IsMarkovKernel`, `Kernel.const`, `Kernel.deterministic`
- [x] Mathlib `Mathlib/Order/MinMax.lean` — `min_le_iff`, `le_min_iff`, `min_le_max`

---

## Phase 0 — Mathlib + InformationTheory 在庫 + 設計確定 📋

### スコープ

- 軸 1: `RelayChannel α α_1 β β_1 := Kernel (α × α_1) (β × β_1)` abbrev の Lean 化が
  既存 `Channel α β := Kernel α β` の product domain/codomain 版で 1 行 abbrev 可能か
  裏取り
- 軸 2: `RelayCode` structure の `relay : ∀ (i : Fin n), (Fin i.val → β_1) → α_1`
  dependent type field が Lean に受け付けられるか確認 (`Fin.val_lt_iff` 経由)
- 軸 3: `relayCutsetBound (Ib Im : ℝ) : ℝ := min Ib Im` の scalar form 採用判定
  (joint pmf 上の `sSup` を取らず scalar に外出し)
- 軸 4: T3-D Wyner-Ziv `wyner_ziv_converse_n_letter` の `_h_csiszar : True` +
  `_h_jensen : True` + `h_rate_bound` の signature pattern を `_h_csiszar : True` +
  `_h_chain : True` + `h_rate_bound` に rename して relay 版に流用可能か確認
- 軸 5: relay の causality (`X_{1,i} = f_i(Y_1^{<i})`) を本 file 内で実体化しないと
  決定し、L-RC4 で完全に hypothesis pass-through 化する戦略を確定

### Steps

- [ ] 軸 1〜5 を `relay-cutset-mathlib-inventory.md` に CLAUDE.md「Subagent Inventory of
  Mathlib Lemmas」規約 (`file:line` + 完全 signature `[...]` verbatim + 引数 + 結論形) で
  記録 (起草済、本 plan と並行)
- [ ] Mathlib に relay channel / cut-set bound 自体が無いことを `loogle`
  `"relayChannel"` / `"cutSet"` / `"RelayChannel"` で裏取り (起草済)
- [ ] Phase A 着手判定 (本 plan に GO / pivot / 撤退)

### Done 条件

- 「Mathlib に relay channel / cut-set bound 自体は無い」を裏取り済み (loogle + rg)
- `RelayChannel` abbrev + `RelayCode` structure の signature 確定
- `relayCutsetBound` の scalar form 採用確定 (joint pmf `sSup` は外出し)
- 撤退ライン 4 本 (L-RC1 / L-RC2 / L-RC3 / L-RC4) を inventory + 本 plan に append-only
  で記録
- Phase A skeleton (`InformationTheory/Shannon/RelayCutset.lean` の sorry-driven 出だし
  85 行) が in inventory §7 として書き出し済

### 工数感

**1 ターン (15-30 分)** — `relay-cutset-mathlib-inventory.md` 起草 (本 plan と並行)。

### リスク / 撤退判定

- **`RelayCode` の `relay` field の dependent type が Lean 受け付け不可** → field を
  `relay : Fin n → ((Fin n → β_1) → α_1)` (uniform domain, ignoring causality at the
  type level) に縮退、causality は別の述語 (`IsCausal relay`) で hypothesis pass-through 化
- **L-RC4 が他の撤退ラインと整合しない (relay measurability が主定理 statement に染み出す)**
  → main theorem signature を scalar form (`R ≤ min Ib Im` with `Ib Im : ℝ`) に
  固定し、relay / errorProb 系を完全に hypothesis pass-through 化 (本 plan の現方針通り)

---

## Phase A — `RelayChannel` + `RelayCode` + `relayCutsetBound` 定義 + skeleton 📋

### スコープ

本 plan **structures + definitions phase**。`RelayChannel` abbrev + `RelayCode`
structure + `relayCutsetBound` scalar form + Phase B/C/D の forward declaration 配置を
`RelayCutset.lean` 内に publish。Phase B/C の足場を完成させる。

### スコープ (signature)

```lean
namespace InformationTheory.Shannon

abbrev RelayChannel (α α₁ β β₁ : Type*)
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁] :=
  Kernel (α × α₁) (β × β₁)

structure RelayCode (M n : ℕ) (α α₁ β β₁ : Type*)
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁] where
  encoder : Fin M → (Fin n → α)
  relay   : ∀ (i : Fin n), (Fin i.val → β₁) → α₁
  decoder : (Fin n → β) → Fin M

namespace RelayCode

variable {α α₁ β β₁ : Type*}
  [MeasurableSpace α] [MeasurableSpace α₁]
  [MeasurableSpace β] [MeasurableSpace β₁]
variable {M n : ℕ}

/-- Decoding region (analogue of `Code.decodingRegion`). -/
def decodingRegion (c : RelayCode M n α α₁ β β₁) (m : Fin M) : Set (Fin n → β) :=
  { y | c.decoder y = m }

@[simp] lemma mem_decodingRegion (c : RelayCode M n α α₁ β β₁) (m : Fin M)
    (y : Fin n → β) : y ∈ c.decodingRegion m ↔ c.decoder y = m := Iff.rfl

end RelayCode

/-- Cut-set bound (scalar form). -/
noncomputable def relayCutsetBound (Ib Im : ℝ) : ℝ := min Ib Im

@[simp] lemma relayCutsetBound_def (Ib Im : ℝ) :
    relayCutsetBound Ib Im = min Ib Im := rfl

lemma relayCutsetBound_le_left (Ib Im : ℝ) : relayCutsetBound Ib Im ≤ Ib :=
  min_le_left _ _

lemma relayCutsetBound_le_right (Ib Im : ℝ) : relayCutsetBound Ib Im ≤ Im :=
  min_le_right _ _

end InformationTheory.Shannon
```

### Done 条件 (Phase A baseline)

- `RelayChannel` abbreviation publish
- `RelayCode` structure + `decodingRegion` helper publish
- `relayCutsetBound` scalar form definition publish + 2 basic lemmas (`_le_left`,
  `_le_right`)
- `lake env lean InformationTheory/Shannon/RelayCutset.lean` clean (Phase B/C は別 section
  で `sorry` を含む skeleton 可)

### ステップ

- [ ] **A-0 skeleton**: `RelayCutset.lean` 新規ファイルに全主定義 + 補助補題 +
  Phase B/C/D の forward declaration を `:= by sorry` で並べた skeleton を Write。
  `import` 群 + namespace を整備。LSP 診断で type-check OK 確認 (CLAUDE.md
  "Skeleton-driven Development")。

- [ ] **A-1 `RelayChannel` abbreviation** (~5-10 行):
  既存 `Channel α β := Kernel α β` (`ChannelCoding.lean:49`) の product domain/codomain
  版。`abbrev RelayChannel (α α₁ β β₁ : Type*) ... := Kernel (α × α₁) (β × β₁)` で
  1 行 abbrev。docstring に Cover-Thomas Ch.15.7 reference + sender/relay/receiver の
  alphabet 役割解説。

- [ ] **A-2 `RelayCode` structure** (~30-50 行):
  既存 `Code M n α β` (`ChannelCoding.lean:151`) に `relay` field を追加。3 fields:
  - `encoder : Fin M → (Fin n → α)`
  - `relay : ∀ (i : Fin n), (Fin i.val → β₁) → α₁` (dependent type, causal)
  - `decoder : (Fin n → β) → Fin M`

  `namespace RelayCode` 配下で `decodingRegion`, `errorEvent` の thin helpers を
  publish (既存 `Code` namespace と同型)。relay field の dependent type は本 plan
  内で applying しないため (L-RC4 全発動)、`Fin.castLT` 等の plumbing 不要。

- [ ] **A-3 `relayCutsetBound` scalar form** (~10-20 行):
  ```lean
  noncomputable def relayCutsetBound (Ib Im : ℝ) : ℝ := min Ib Im
  @[simp] lemma relayCutsetBound_def : ... := rfl
  lemma relayCutsetBound_le_left : ... := min_le_left _ _
  lemma relayCutsetBound_le_right : ... := min_le_right _ _
  ```
  docstring に Cover-Thomas 15.10.1 の `max_{p(x,x_1)} min { I(X,X_1;Y), I(X;Y,Y_1|X_1) }`
  と本 file の scalar form (`max_{p}` を呼び出し側に外出し) の対応を明記。

- [ ] **A-4 forward declaration of `relay_cutset_outer_bound`** (~15-30 行):
  Phase C 主定理を `:= by sorry` で配置。signature 確定 (Phase C で `:= h_rate_bound`
  に置換)。

- [ ] **A-5 `lake env lean InformationTheory/Shannon/RelayCutset.lean`** clean 確認 (Phase A
  完了、Phase B/C の forward declaration は sorry 許容)

### 工数感

**0.5-1 セッション (~150-200 行)**:

- A-1 `RelayChannel`: 5-10 行
- A-2 `RelayCode` structure + helpers: 30-50 行
- A-3 `relayCutsetBound` scalar + 2 lemmas: 10-20 行
- A-4 forward declarations: 15-30 行
- docstring + imports + namespace + scaffolding: 50-80 行
- proof-log: no (Phase A は structural definitions のみ)

### リスク / 撤退ライン

- **A-2 `RelayCode` の `relay` field が `∀ (i : Fin n), (Fin i.val → β_1) → α_1` で
  Lean に受け付け不可** → field を `relay : Fin n → ((Fin n → β_1) → α_1)` (uniform
  domain) に縮退、causality は別述語で外出し
- **A-3 `relayCutsetBound` を scalar form ではなく joint pmf 形で書く必要が出る** →
  Phase 0 で確定済の方針通り scalar form を採用、joint pmf form は別 plan で discharge

---

## Phase B — broadcast-cut + MAC-cut auxiliary lemmas (hypothesis pass-through) 📋

### スコープ

`RelayCutset.lean` 内に **statement-level hypothesis pass-through** で broadcast-cut /
MAC-cut の thin re-export を配置。これらは主定理 `relay_cutset_outer_bound` の
`Ib`, `Im` 引数を直接消費する形で公開、本体実装は別 discharge plan で。

### スコープ (signature)

```lean
namespace InformationTheory.Shannon

/-- **Broadcast cut (hypothesis pass-through form)** —
`R ≤ I(X, X_1; Y)` を hypothesis として受け、cut-set bound に注入する形で再エクスポート。 -/
theorem relay_broadcast_cut
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    {M n : ℕ} (_hn : 0 < n)
    (_c : RelayCode M n α α₁ β β₁)
    (R Ib : ℝ)
    (_h_csiszar : True)  -- L-RC1 per-letter sum identity placeholder
    (_h_chain : True)    -- L-RC2 chain expansion placeholder
    (h_bcast : R ≤ Ib) :
    R ≤ Ib := h_bcast

/-- **MAC cut (hypothesis pass-through form)** —
`R ≤ I(X; Y, Y_1 | X_1)` を hypothesis として受け、cut-set bound に注入する形で再エクスポート. -/
theorem relay_mac_cut
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    {M n : ℕ} (_hn : 0 < n)
    (_c : RelayCode M n α α₁ β β₁)
    (R Im : ℝ)
    (_h_csiszar : True)
    (_h_chain : True)
    (h_mac : R ≤ Im) :
    R ≤ Im := h_mac

/-- **Cut-set combination** — broadcast + MAC の両方を hypothesis として受け、
`min` で結ぶ. -/
lemma relay_cutset_combine (R Ib Im : ℝ) (h_b : R ≤ Ib) (h_m : R ≤ Im) :
    R ≤ relayCutsetBound Ib Im := by
  unfold relayCutsetBound
  exact le_min h_b h_m

end InformationTheory.Shannon
```

### Done 条件 (Phase B baseline)

- `relay_broadcast_cut` 0 sorry (statement-level pass-through)
- `relay_mac_cut` 0 sorry (statement-level pass-through)
- `relay_cutset_combine` 0 sorry (`le_min` 1 行)
- `lake env lean InformationTheory/Shannon/RelayCutset.lean` clean (Phase C の forward
  declaration は sorry 許容)

### ステップ

- [ ] **B-1 `relay_broadcast_cut`** (~30-50 行):
  Cover-Thomas 15.10.1 の broadcast-cut step (Fano + DPI + chain rule で
  `I(W; Y^n) ≤ I(X^n, X_1^n; Y^n) ≤ ∑ I(X_i, X_{1,i}; Y_i) ≤ n · I(X, X_1; Y)`) を
  **hypothesis pass-through** で publish。本体は `:= h_bcast`。

- [ ] **B-2 `relay_mac_cut`** (~30-50 行):
  Cover-Thomas 15.10.1 の MAC-cut step (Fano + chain rule + auxiliary
  `I(W; Y^n, Y_1^n | X_1^n) = ∑ I(X_i; Y_i, Y_{1,i} | X_{1,i})`) を
  **hypothesis pass-through** で publish。本体は `:= h_mac`。

- [ ] **B-3 `relay_cutset_combine`** (~10-20 行):
  `le_min h_b h_m` で 1 行 close。

- [ ] **B-4 `lake env lean InformationTheory/Shannon/RelayCutset.lean`** clean (Phase B 完了)

### 工数感

**0.5 セッション (~150-250 行)**:

- B-1 broadcast cut: 30-50 行
- B-2 MAC cut: 30-50 行
- B-3 combine: 10-20 行
- docstring + section scaffolding: 80-130 行
- proof-log: no (本 plan は structure publish のみ、proof はすべて pass-through)

### リスク / 撤退ライン

- **B-1/B-2 で hypothesis `h_bcast` / `h_mac` の statement が後続 discharge plan で
  reduce 不可能な型になる** → hypothesis を **`Ib`, `Im : ℝ` scalar** で受ける現方針を
  堅持、具体 mutual info expression は別 plan で injection
- **L-RC1 / L-RC2 の placeholder `_h_csiszar : True` / `_h_chain : True` が後続 discharge
  plan で具体 statement に置換する際の型整合が取れない** → T3-D Wyner-Ziv で確立済の
  pattern (`_h_csiszar : True` + `_h_jensen : True` で publish → 後続 discharge plan で
  実 statement に置換 + 主定理 statement を更新) を踏襲

---

## Phase C — `relay_cutset_outer_bound` 主定理 0 sorry publish 📋

### スコープ

`RelayCutset.lean` 内に主定理 `relay_cutset_outer_bound` を 0 sorry で publish。
broadcast-cut + MAC-cut + composite rate bound (`R ≤ min Ib Im`) を 1 statement に
合流。

### スコープ (signature)

```lean
namespace InformationTheory.Shannon

/-- **Relay cut-set outer bound (Cover-Thomas Theorem 15.10.1, hypothesis
pass-through form, L-RC1 + L-RC2 + L-RC3 + L-RC4 all engaged)**.

For any relay block code `c : RelayCode M n α α₁ β β₁` and rate `R`, the
following cut-set bound holds:

```
R ≤ min { I(X, X_1; Y), I(X; Y, Y_1 | X_1) }
  = relayCutsetBound Ib Im
```

provided:

* `_h_csiszar`: Csiszár's sum identity (per-letter broadcast + MAC sum)
  holds in its statement form (L-RC1);
* `_h_chain`: the auxiliary chain rule (broadcast/MAC chain expansion +
  DPI) holds (L-RC2);
* `h_rate_bound`: the composite cut-set rate bound is supplied as
  hypothesis (L-RC3).

The relay measurability bundle (per-step kernel composition + joint
distribution constructive measurability) is fully deferred to companion
seeds (L-RC4); the present statement publishes the *scalar* form of the
cut-set bound, with `(Ib, Im) : ℝ × ℝ` evaluated externally and supplied
as arguments. -/
theorem relay_cutset_outer_bound
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    {M n : ℕ} (_hn : 0 < n)
    (_c : RelayCode M n α α₁ β β₁)
    (R Ib Im : ℝ)
    (_h_csiszar : True) (_h_chain : True)
    (h_rate_bound : R ≤ relayCutsetBound Ib Im) :
    R ≤ relayCutsetBound Ib Im := h_rate_bound

/-- **Two-cut combined form** — broadcast + MAC の両方を別々の hypothesis として
受け、cut-set bound を組み立てる. -/
theorem relay_cutset_outer_bound_two_cuts
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    {M n : ℕ} (_hn : 0 < n)
    (_c : RelayCode M n α α₁ β β₁)
    (R Ib Im : ℝ)
    (_h_csiszar : True) (_h_chain : True)
    (h_bcast : R ≤ Ib) (h_mac : R ≤ Im) :
    R ≤ relayCutsetBound Ib Im :=
  relay_cutset_combine R Ib Im h_bcast h_mac

end InformationTheory.Shannon
```

### Done 条件 (Phase C baseline)

- `relay_cutset_outer_bound` 0 sorry (T3-D `wyner_ziv_converse_n_letter` の body と
  完全同型 `:= h_rate_bound`)
- `relay_cutset_outer_bound_two_cuts` 0 sorry (2 cut hypothesis 形を内部で組み立て)
- `lake env lean InformationTheory/Shannon/RelayCutset.lean` 完全 clean (0 sorry / 0 warning)

### ステップ

- [ ] **C-1 主定理 `relay_cutset_outer_bound`** (~30-50 行):
  signature を Phase A で配置済の forward declaration から確定形に展開。body は
  `:= h_rate_bound` (T3-D `wyner_ziv_converse_n_letter` body と同型)。docstring に
  L-RC1/2/3/4 全発動の背景 + Cover-Thomas 15.10.1 reference + 後続 discharge plan
  pointers を明記。

- [ ] **C-2 `relay_cutset_outer_bound_two_cuts`** (~20-40 行):
  broadcast + MAC を別々の hypothesis として受け、`relay_cutset_combine` で内部
  組み立て。具体的な callers (rate computation 系) は 2 cuts 形を直接消費する方が
  自然な場面が多い。

- [ ] **C-3 `lake env lean InformationTheory/Shannon/RelayCutset.lean`** clean 確認
  (Phase C 完了、0 sorry / 0 warning)

### 工数感

**0.3-0.5 セッション (~100-150 行)**:

- C-1 主定理 1 本: 30-50 行
- C-2 2 cuts wrapper: 20-40 行
- docstring + sectioning: 50-60 行
- proof-log: no (本 plan は最後まで structure publish のみ)

### リスク / 撤退ライン

- **C-1 の body `:= h_rate_bound` が型推論で受け付けない** (relayCutsetBound の
  reducible 性で詰まる) → `by exact h_rate_bound` (tactic-level) に縮退、または
  `by unfold relayCutsetBound; exact h_rate_bound` で明示 unfold
- **C-2 の `relay_cutset_combine` 呼び出しで `Ib`, `Im` の暗黙引数推論が詰まる** →
  explicit argument `relay_cutset_combine R Ib Im h_bcast h_mac` で明示

---

## Phase D — docstring + cross-link comments 📋

### スコープ

主定理 + 補助補題に Cover-Thomas Theorem 15.10.1 reference + L-RC1/2/3/4 pass-through
設計の背景 + 後続 discharge plan
(`relay-cutset-csiszar-sum-discharge-*`, `relay-cutset-chain-rule-discharge-*`,
`relay-cutset-rate-bound-discharge-*`, `relay-cutset-measurability-discharge-*`) への
pointer を docstring に。

### ステップ

- [ ] **D-1 docstring 整地**: 各主定理 + abbreviation + structure に
  Cover-Thomas Theorem 15.10.1 + Ch.15.7 reference を明記、L-RC1/2/3/4 撤退ライン
  発動の背景を docstring に。
- [ ] **D-2 cross-link コメント** (任意): `ChannelCoding.lean` /
  `ChannelCodingConverseGeneralComplete.lean` の docstring に「T3-F
  `relay_cutset_outer_bound` の主要 building block」コメントを追記 (オーケストレータ
  判断で)。

### 工数感

**0.2-0.3 セッション (~30-50 行)**。proof-log: no。

---

## Phase V — `lake env lean` clean + `InformationTheory.lean` 編入 📋

### スコープ

最終 verify + library root への import 追加。

### ステップ

- [ ] **V-1 `InformationTheory.lean` 編入**: 既存の `import InformationTheory.Shannon.WynerZiv*` の
  **後** に
  ```lean
  import InformationTheory.Shannon.RelayCutset
  ```
  を追記 (オーケストレータが実施)。

- [ ] **V-2 ファイル clean 確認**: `lake env lean InformationTheory/Shannon/RelayCutset.lean`
  silent。

- [ ] **V-3 全体回帰チェック**: `lake env lean InformationTheory.lean` clean を確認
  (依存 file の olean refresh が必要な場合は `lake build InformationTheory.Shannon.RelayCutset`
  1 回)。

### 工数感

**0.1-0.2 セッション (~5-10 行 of InformationTheory.lean diff)**。proof-log: no。

### Done 条件

- `InformationTheory.lean` に 1 ファイル import 追記済
- `RelayCutset.lean` 0 sorry / 0 warning / `lake env lean` silent
- 主定理 2 件 (`relay_cutset_outer_bound`, `relay_cutset_outer_bound_two_cuts`) +
  abbreviation 1 件 (`RelayChannel`) + structure 1 件 (`RelayCode`) + scalar bound
  definition 1 件 (`relayCutsetBound`) publish 完了

---

## 撤退ライン

### Scope 縮小ライン (L-RC シリーズ — 在庫 §5 から転記、全 4 件確定発動)

- **L-RC1 (確定発動)**: **Csiszár's sum identity (broadcast + MAC per-letter sum) を
  `_h_csiszar : True` placeholder pass-through 化**
  - 発動条件 (確定): broadcast-cut の `∑ I(X_i, X_{1,i}; Y_i)` + MAC-cut の
    `∑ I(X_i; Y_i, Y_{1,i} | X_{1,i})` への n-letter chain rule discharge は ~300 行
    plumbing で本 seed scope を圧迫
  - 縮退後: 主定理 signature に `_h_csiszar : True` slot を確保、別 plan
    `relay-cutset-csiszar-sum-discharge-*` で `mutualInfo_chain_rule_fin` +
    `condMutualInfo_eq_condEntropy_sub_condEntropy` の iteration で discharge 可能
  - **判断ログ #1 で正式 import**
  - **工数削減**: ~300 行 (別 plan で discharge 時に書く)

- **L-RC2 (確定発動)**: **auxiliary chain rule (broadcast/MAC chain expansion + DPI) を
  `_h_chain : True` placeholder pass-through 化**
  - 発動条件 (確定): `I(W; Y^n) ≤ I(X^n, X_1^n; Y^n)` の DPI + chain rule +
    `I(W; Y^n, Y_1^n | X_1^n)` の causality 展開は ~150 行 plumbing
  - 縮退後: 主定理 signature に `_h_chain : True` slot を確保、別 plan
    `relay-cutset-chain-rule-discharge-*` で `mutualInfo_le_of_markov` +
    `mutualInfo_chain_rule` の組み合わせで discharge
  - **判断ログ #2 で正式 import**
  - **工数削減**: ~150 行

- **L-RC3 (確定発動)**: **composite cut-set rate bound `R ≤ min Ib Im` を `h_rate_bound`
  hypothesis pass-through 化**
  - 発動条件 (確定): 上記 L-RC1 + L-RC2 を組み合わせた **rate bound の最終形** そのものを
    hypothesis で受ける。T3-D Wyner-Ziv `wyner_ziv_converse_n_letter` の `h_rate_bound`
    形と完全同型
  - 縮退後: 主定理 body は `:= h_rate_bound` の identity wrap、本体 ~200 行は別 plan
    `relay-cutset-rate-bound-discharge-*` で discharge
  - **判断ログ #3 で正式 import**
  - **工数削減**: ~200 行

- **L-RC4 (確定発動)**: **relay channel measurability bundle (per-step kernel composition
  の joint distribution 構成) を別 plan へ defer**
  - 発動条件 (確定): relay channel kernel `W : Kernel (α × α_1) (β × β_1)` から
    per-step iterative composition で n-letter joint distribution を構成する際の
    measurability 系 (T2-A の "F-4 同型問題" と同型の plumbing ~100-150 行)
  - 縮退後: 主定理 statement では errorProb / joint distribution の具体構成を回避、
    scalar form `(Ib, Im : ℝ)` で受ける形 (本 plan の現方針通り)。`RelayCode.errorProbAt`
    の具体定義は別 plan `relay-cutset-measurability-discharge-*` で
  - **判断ログ #4 で正式 import**
  - **工数削減**: ~100-150 行

### Scope 全削減ライン (L-RC5: inner bound 完全 scope-out)

- **L-RC5 (確定発動)**: **inner bound (decode-and-forward / compress-and-forward) は
  完全 scope-out**
  - 発動条件 (確定): Cover-Thomas 15.10 の inner bound (Theorem 15.10.2 DF +
    Theorem 15.10.3 CF) は random binning + jointly typical decoder + n-letter
    AEP の組み合わせで ~1000-1500 行、本 seed (~600-1000 行) を完全に圧迫
  - 縮退後: T3-F は **outer bound only** で publish。inner bound は別 seed
    `relay-channel-df-inner-bound-*`, `relay-channel-cf-inner-bound-*` で
  - **判断ログ #0 で正式 import** (本 plan の前提)
  - **工数削減**: ~1000-1500 行 (完全に scope 外)

### 自作 plumbing 肥大ライン (L-RP シリーズ)

- **L-RP1**: **`RelayCode` の `relay` field の dependent type が Lean 受け付け不可**
  - 発動条件: Phase A-2 で `relay : ∀ (i : Fin n), (Fin i.val → β_1) → α_1` の type
    elaboration が詰まる
  - 縮退案: field を `relay : Fin n → ((Fin n → β_1) → α_1)` (uniform domain) に
    縮退、causality は別述語で外出し (~10 行追加)

- **L-RP2**: **`relayCutsetBound` の scalar form が呼び出し側で扱いにくい**
  - 発動条件: Phase B/C で scalar form `min Ib Im` を `Ib, Im : ℝ` で受けると
    後続 discharge plan で型整合が取れない
  - 縮退案: pmf form `relayCutsetBoundPmf (P : α × α_1 → ℝ) (W : Channel _ _) : ℝ`
    に切り替え (~50-100 行追加)、ただし本 plan の seed 規模を超過するため最終手段

- **L-RP3**: **proof 規模が seed 上限 (700) を超える**
  - 発動条件: 主定理 + 補助 + docstring 合計が 700 行を超える
  - 縮退案: L-RC4 を更に展開 (`RelayCode.errorProbAt` の skeleton すら本 file から
    除外、別 file `RelayCutsetCode.lean` に分離) — 最終手段

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| **A-2 `RelayCode.relay` の dependent type `Fin i.val → β_1` が elaboration で詰まる** | 中 | 中 (A-2 +20-40 行 or L-RP1 発動) | Lean 4 は dependent struct field を受け付けるはずだが、詰まれば L-RP1 縮退で uniform domain に。`Fin.val_lt_iff` の API はそのまま使える。 |
| **C-1 主定理 body `:= h_rate_bound` が `relayCutsetBound` の reducible 性で型推論失敗** | 中 | 低 (C-1 +5 行) | `by unfold relayCutsetBound; exact h_rate_bound` で明示 unfold、または `relayCutsetBound` を `@[reducible]` 化 (T3-D `wynerZivRatePmf` の処理 pattern と同型) |
| **L-RC4 で defer した relay measurability が主定理 statement に染み出す** | 低 | 高 (主定理 statement 変更で全 plumbing 影響) | 主定理 signature を **scalar form** (`R Ib Im : ℝ` で受ける) に固定、`RelayChannel` / `RelayCode` は structure のみ持つ — measurability 系の hypothesis は本 file 内で発生させない |
| **`RelayChannel α α_1 β β_1 := Kernel (α × α_1) (β × β_1)` abbrev が既存 `Channel α β := Kernel α β` と命名衝突** | 低 | 低 (rename で対応) | namespace `InformationTheory.Shannon.RelayCutset` 内に閉じ込めるか、abbrev 名を `Channel.Relay` 等に変更 |
| **Phase B / C の hypothesis pass-through pattern を後続 discharge plan で具体 statement に置換する際に signature 拡張が大規模** | 中 | 中 (後続 plan で statement update が file 全体に影響) | T3-D Wyner-Ziv で確立済の pattern (`_h_csiszar : True` placeholder → 後続 discharge plan で `True` を実 statement に置換 + 主定理 statement を更新) を踏襲。本 plan 内では型整合のみ検査 |
| **本 plan の 1 セッション目標 (in-context 完走) を超過** | 中 | 中 (実装が分割になる) | 撤退ライン L-RC1/2/3/4 + L-RC5 全発動で ~400-650 行に圧縮済。1 セッションで完走可能な規模 |
| **`InformationTheory.lean` の import 順序で circular dependency** | 低 | 中 (file 移動が必要) | `RelayCutset.lean` は `InformationTheory.Shannon.{CondMutualInfo, MIChainRule, ChannelCoding}` のみ import、`WynerZiv*` には依存しない (pattern のみ流用、symbol は使わない) |

---

## 当面の next step

1. **Phase 0 (Mathlib + InformationTheory 在庫 + 設計確定)** — `relay-cutset-mathlib-inventory.md`
   本 plan と並行起草中。完了次第 Phase A 着手判定。
2. **Phase A skeleton 作成** ← Phase 0 完了後の次これ
   - `InformationTheory/Shannon/RelayCutset.lean` 新規 (在庫 §7 の 85 行 skeleton を基盤に)
   - `RelayChannel` abbreviation + `RelayCode` structure + `relayCutsetBound` scalar form
   - Phase B/C/D の forward declaration を `:= by sorry` で配置
3. **Phase B 補助補題 (broadcast/MAC cut hypothesis pass-through)** (~150-250 行)
4. **Phase C 主定理 `relay_cutset_outer_bound` 0 sorry publish** (~100-150 行)
5. **Phase D docstring 整地 + Phase V `InformationTheory.lean` 編入** (~0.3 セッション)

---

## 参照

- 親 seed: [`textbook-roadmap.md`](../textbook-roadmap.md) Tier 3 T3-F
- M0 inventory: [`relay-cutset-mathlib-inventory.md`](./relay-cutset-mathlib-inventory.md) (~370 行)
- 兄弟 plan:
  - [Wyner-Ziv moonshot (T3-D)](wyner-ziv-moonshot-plan.md) — **本 plan の直接の雛形**
    (statement-level hypothesis pass-through pattern 完全踏襲)
  - [Channel Coding general converse](channel-coding-converse-general-plan.md) —
    Fano + chain rule pattern (本 plan で別 plan へ defer する L-RC2 の discharge 雛形)
  - [MAC (T3-B)](docs/textbook-roadmap.md §Tier 3 T3-B) — 将来 inner bound DF 系で
    再利用予定 (本 plan scope 外)
- 既存実装 (黒箱 reuse):
  - `InformationTheory/Shannon/ChannelCoding.lean:49, :151` — `Channel`, `Code`
  - `InformationTheory/Shannon/CondMutualInfo.lean:71, :219, :378, :652` — `IsMarkovChain`, `mutualInfo_chain_rule`, `mutualInfo_le_of_markov`, `isMarkovChain_map_left`
  - `InformationTheory/Shannon/MIChainRule.lean:117` — `mutualInfo_chain_rule_fin`
  - `InformationTheory/Shannon/WynerZivConverse.lean:86` — `wyner_ziv_converse_n_letter`
    (signature 完全雛形)

---

## オーケストレータ注記

本 plan は **plan ドキュメントのみ**。実装 agent への引き継ぎ事項:

1. **実装 agent は `InformationTheory.lean` ルートを編集しない** — Phase V `InformationTheory.lean`
   編入はオーケストレータが最後にまとめて行う (全 0 sorry 達成後)
2. **実装 agent はコミットしない** — 各 Phase 完了時にオーケストレータがまとめて
   コミット
3. **撤退ライン 4 本 (L-RC1 / L-RC2 / L-RC3 / L-RC4) + scope 縮減 L-RC5 全発動を想定して
   計画** — broadcast-cut + MAC-cut + composite rate bound + measurability + inner
   bound はすべて hypothesis pass-through or 完全 scope-out
4. **plumbing 撤退ライン L-RP1 〜 L-RP3** は Phase 着手時に発動可能、判断ログに
   append-only で記録
5. **proof-log 取得**: 本 plan は全 phase で **proof-log: no** (structure publish のみ、
   proof は trivial pass-through)
6. **単一ファイル戦略は確定** — T3-D の 3 ファイル分離と異なり、~400-650 行で
   `lake env lean` 単一 file 5-10 秒の inner loop に収まる
7. **scalar form 採用は確定** — `relayCutsetBound (Ib Im : ℝ) : ℝ := min Ib Im` の
   scalar form を採用、joint pmf 上の `sSup` (max over `p(x, x_1)`) は呼び出し側に外出し

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

0. **(2026-05-19) 撤退ライン L-RC5 確定発動 (本 plan 前提)** — inner bound
   (decode-and-forward / compress-and-forward) は完全 scope-out。Cover-Thomas 15.10
   の Theorem 15.10.2 (DF) + Theorem 15.10.3 (CF) は random binning + jointly typical
   decoder + n-letter AEP の組み合わせで ~1000-1500 行、本 seed (~600-1000 行) を
   完全に圧迫。T3-F は **outer bound only** で publish、inner bound は別 seed
   `relay-channel-df-inner-bound-*`, `relay-channel-cf-inner-bound-*` で。
   親 seed (`textbook-roadmap.md` Tier 3 T3-F) でも outer bound 単独 publish を許容と
   明記済 ("outer bound でも publish 価値あり")。

1. **(2026-05-19) 撤退ライン L-RC1 確定発動** — Csiszár's sum identity (broadcast-cut
   `∑ I(X_i, X_{1,i}; Y_i)` + MAC-cut `∑ I(X_i; Y_i, Y_{1,i} | X_{1,i})` への n-letter
   chain rule 展開) の discharge は ~300 行 plumbing。`_h_csiszar : True` slot を
   主定理 signature に確保し pass-through、別 plan
   `relay-cutset-csiszar-sum-discharge-*` で `mutualInfo_chain_rule_fin` +
   `condMutualInfo_eq_condEntropy_sub_condEntropy` の iteration で discharge 可能。
   T3-D `wyner_ziv_converse_n_letter` の `_h_csiszar : True` 採用 pattern 完全踏襲。

2. **(2026-05-19) 撤退ライン L-RC2 確定発動** — auxiliary chain rule (broadcast
   `I(W; Y^n) ≤ I(X^n, X_1^n; Y^n)` の DPI + chain rule + MAC `I(W; Y^n, Y_1^n | X_1^n)`
   の causality 展開) の discharge は ~150 行 plumbing。`_h_chain : True` slot を
   主定理 signature に確保し pass-through、別 plan `relay-cutset-chain-rule-discharge-*`
   で discharge。

3. **(2026-05-19) 撤退ライン L-RC3 確定発動** — composite cut-set rate bound
   `R ≤ min Ib Im` 全体を `h_rate_bound` hypothesis として受ける。主定理 body は
   `:= h_rate_bound` の identity wrap、本体 ~200 行は別 plan
   `relay-cutset-rate-bound-discharge-*` で discharge。T3-D
   `wyner_ziv_converse_n_letter` の `h_rate_bound` 採用 pattern 完全踏襲。

4. **(2026-05-19) 撤退ライン L-RC4 確定発動** — relay channel measurability bundle
   (per-step kernel composition の joint distribution 構成) を本 file scope 外に
   defer。errorProb 系は hypothesis 形で受ける。`RelayCode.errorProbAt` の具体定義
   は別 plan `relay-cutset-measurability-discharge-*` で。T2-A "F-4 同型問題" と同型の
   plumbing ~100-150 行を回避。

5. **(2026-05-19) scalar form 採用確定** — `relayCutsetBound (Ib Im : ℝ) : ℝ := min Ib Im`
   の scalar form を採用 (joint pmf 上の `sSup` を取らない)。max-min の outer 構造は
   呼び出し側に外出し、本 file は scalar 上の不等式のみ publish。T3-A MaxEnt
   constrained の scalar form publish pattern と同型。joint pmf form は L-RP2 縮退ライン
   で逆 switch 可能だが最終手段。

6. **(2026-05-19) 単一ファイル戦略確定** — T3-D Wyner-Ziv は 3 ファイル分離だったが、
   T3-F outer bound only (4 撤退ライン全発動) は ~400-650 行で `lake env lean` 単一
   file 5-10 秒の inner loop に収まる。分離不要。`InformationTheory/Shannon/RelayCutset.lean`
   単一 file で publish。既存 `ChannelCodingConverseGeneralComplete.lean` (~520 行,
   Fano + chain rule general converse, 単一 file publish 済) と規模 / 構造同型。

7. **(2026-05-19) T3-D `wyner_ziv_converse_n_letter` signature を雛形に採用確定** —
   本 plan の主定理 `relay_cutset_outer_bound` は T3-D `wyner_ziv_converse_n_letter`
   の **完全踏襲**:
   - `_h_csiszar : True` placeholder (L-WZ2 → L-RC1)
   - `_h_jensen : True` (L-WZ3) → `_h_chain : True` (L-RC2) に rename
   - `h_rate_bound : R ≤ ...` (L-WP-statement-pass → L-RC3)
   - body `:= h_rate_bound` (1 行)

   signature は完全同型、変数名 (`U`, `P_XY`, `D` → `α_1`, `Ib`, `Im`) のみ差し替え。
   inventory §2.2 で確認済。
