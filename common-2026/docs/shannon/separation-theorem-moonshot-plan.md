# T3-E Joint Source–Channel Coding (Separation Theorem) ムーンショット計画 🌙

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-E. Joint Source–Channel
>   Coding (Separation Theorem)」
>
> **Inventory (Phase 0 完了)**: [`separation-theorem-mathlib-inventory.md`](./separation-theorem-mathlib-inventory.md)
>
> **Predecessor / 再利用基盤** (全て publish 済、本 plan からは黒箱 reuse):
> - `Common2026/Shannon/AEP.lean:1138` — `source_coding_achievability`
>   (IID source achievability, `Tendsto rate (𝓝 R)` + `Tendsto errorProb (𝓝 0)`)
> - `Common2026/Shannon/AEP.lean:704` — `source_coding_converse`
>   (IID source converse, `entropy ≤ Filter.liminf (log M_n / n)`)
> - `Common2026/Shannon/AEP.lean:580` — `source_coding_per_n_bound` (per-n Fano 形)
> - `Common2026/Shannon/AEPRate.lean` — rate scaling 用の `Tendsto` lemma 群
> - `Common2026/Shannon/ChannelCodingShannonTheoremFullDischarge.lean:1588` —
>   `shannon_noisy_channel_coding_theorem_general_full` (DMC achievability, max-error 形,
>   `hW_pos` 全 discharge 済)
> - `Common2026/Shannon/ChannelCodingConverseMemorylessPure.lean:650` —
>   `channel_coding_converse_general_memoryless_pure` (DMC converse, semi-pure Fano 形)
> - `Common2026/Shannon/ChannelCoding.lean` — `Code M n α β` bundle, `Code.errorProbAt`,
>   `Code.averageErrorProb`
> - `Common2026/Shannon/BlockwiseChannel.lean:111, :1181` — `BlockwiseChannel.ofMemoryless`,
>   `capacity_lim_eq_capacity_of_memoryless`
> - `Common2026/Shannon/ChannelCodingShannonTheorem.lean:102` — `capacity W` 定義
>
> **Goal (短形)**: 新規ファイル `Common2026/Shannon/SeparationTheorem.lean` で
> Cover–Thomas Theorem 7.13.1 (Joint Source–Channel Coding Separation Theorem) を
> **IID source 限定形** で publish する。**0 sorry / 0 warning**、Tier 1 baseline
> (achievability) ~280 行、Tier 2 (converse 込) ~400 行。
>
> **撤退ライン**: [L-S0] **stationary ergodic 一般化を本 plan で scope-out (確定発動)** /
> [L-S1] Tier 1 (achievability) 単独 publish / [L-S2] Tier 2 converse の uniform-message
> bridge を近似 fallback / [L-S3] avg-error 形採用 (max-error → avg-error 弱化) /
> [L-P1] composition primitive 自作量超過時の statement 弱化 (詳細 §撤退ライン)。

## Status (2026-05-19)

**Phase 0 (Mathlib + Common2026 在庫) 完了** — inventory で「**既存率 ~70% (composition 全体)、
自作必要 4 件 ~160 行、撤退ライン L-S0 確定発動 (stationary ergodic 一般化は別 plan で deferred)、
規模 350-500 行 (IID + achievability + converse 込)**」を確定。`composeCode` / `errorProb_composed_le` /
rate scaling / Tendsto↔liminf bridge の 4 件が **Mathlib + Common2026 完全不在の novel 構造**
として残るが、それ以外は既存 publish 済 black-box の合成で組める。Tier 1 (achievability) →
Tier 2 (converse) の段階的 publish 設計で着手準備完了。

## 進捗

- [x] Phase 0 — Mathlib + Common2026 在庫 ✅ → [`separation-theorem-mathlib-inventory.md`](./separation-theorem-mathlib-inventory.md)
- [x] Phase A — `composeCode` + 合成 error bound (Tier 0 baseline) ✅ (avg-error 形採用 L-S3、~210 行)
- [x] Phase B — Achievability 主定理 (Tier 1 baseline) ✅ (`separation_achievability_iid`、~140 行追加)
- [ ] Phase C — Converse 主定理 (Tier 2 理想, +~100 行) 📋
- [x] Phase D — 主定理 wrapper + library 編入 ✅ (Common2026.lean に import 追記済)
- ~~[ ] Phase E — Stationary ergodic 一般化~~ 🔄 **scope-out (撤退ライン L-S0 発動、判断ログ #1)**

## ゴール / Approach

### 最終到達点 (Tier 2 完成形)

新規ファイル `Common2026/Shannon/SeparationTheorem.lean` で 4 件 publish:

```lean
namespace InformationTheory.Shannon.SeparationTheorem

/-- Composed source–channel code error probability on the product space
    (source Ω) × (per-letter channel-noise kernel). Built on top of
    `ChannelCoding.Code` and `source_coding_achievability` outputs. -/
noncomputable def composedErrorProb
    {Ω α_src α_ch β : Type*} [MeasurableSpace Ω] [Fintype α_src] [Fintype α_ch] [Fintype β]
    (μ : Measure Ω) (Xs : ℕ → Ω → α_src)
    {n n_c M_src M_ch : ℕ}
    (c_src : (Fin n → α_src) → Fin M_src) (d_src : Fin M_src → (Fin n → α_src))
    (h_le : M_src ≤ M_ch)
    (W : Channel α_ch β) (c_ch : Code M_ch n_c α_ch β) : ℝ

/-- Union bound on the composed error: `Pe_total ≤ Pe_src + max-Pe_ch`. -/
theorem errorProb_composed_le
    {Ω α_src α_ch β : Type*} ...
    (μ : Measure Ω) (Xs : ℕ → Ω → α_src) ...
    (c_src : (Fin n → α_src) → Fin M_src) (d_src : Fin M_src → (Fin n → α_src))
    (h_le : M_src ≤ M_ch) (W : Channel α_ch β) (c_ch : Code M_ch n_c α_ch β) :
    composedErrorProb μ Xs c_src d_src h_le W c_ch
      ≤ InformationTheory.MeasureFano.errorProb μ
          (jointRV Xs n) (fun ω => c_src (jointRV Xs n ω)) d_src
        + (Finset.univ : Finset (Fin M_ch)).sup'
            ⟨0, Finset.mem_univ _⟩
            (fun m => (c_ch.errorProbAt W m).toReal)

/-- **T3-E achievability (Tier 1)** — IID source `Xs` with `entropy μ (Xs 0) < capacity W`
    admits a composed code family with vanishing total error. -/
theorem separation_achievability_iid
    {Ω α_src α_ch β : Type*} ...
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α_src) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α_src, 0 < (μ.map (Xs 0)).real {x})
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (W : Channel α_ch β) [IsMarkovKernel W]
    (hHC : entropy μ (Xs 0) < capacity W) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
      ∃ (n_c M_src M_ch : ℕ) (h_le : M_src ≤ M_ch)
        (c_src : (Fin n → α_src) → Fin M_src) (d_src : Fin M_src → (Fin n → α_src))
        (c_ch : Code M_ch n_c α_ch β),
        composedErrorProb μ Xs c_src d_src h_le W c_ch < ε

/-- **T3-E converse (Tier 2)** — any composed code family with vanishing error
    and bounded rate satisfies `entropy ≤ capacity`. -/
theorem separation_converse_iid
    {Ω α_src α_ch β : Type*} ...
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α_src) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hcard : 2 ≤ Fintype.card α_src)
    (W : Channel α_ch β) [IsMarkovKernel W]
    (codes : ℕ → (∃ ...))  -- composed code family
    (hPe_to_zero : Tendsto (composedErrorProb_of codes) atTop (𝓝 0))
    (hR_bdd : ∃ R, ∀ n, Real.log (M_src n : ℝ) / n ≤ R) :
    entropy μ (Xs 0) ≤ capacity W

end InformationTheory.Shannon.SeparationTheorem
```

### Approach (overall strategy / shape of solution)

**戦略の shape** — 「textbook 上で `H < C ⇒ ∃ asymptotically reliable joint code` を取る」
論証は 3 段に分解できるが、Mathlib + Common2026 では **(1) source side / (2) channel side
は完成済 black-box** で、**(3) composition は完全不在 (要自作)**:

```
[Source side]         [Composition (本 plan 新規)]        [Channel side]

A-1 source_coding_     ──────────────►  composeCode    ◄────  B-1 shannon_noisy_
    achievability                       (encoder ∘                channel_coding_
    (Tendsto rate→R,                    encoder + decoder         theorem_general_full
     Tendsto Pe→0)                      ∘ decoder)                (max-error < ε)

                                ▼
                       errorProb_composed_le
                       (union bound: Pe_total ≤
                        Pe_src + Pe_ch_max)

                                ▼
                       rate_scaling
                       (n_c := ⌈n · R_src / R_ch⌉
                        を選んで M_src n ≤
                        ⌈exp(n_c · R_ch)⌉)

                                ▼
                       separation_achievability_iid
                       (∀ε, ∃N, ∀n≥N, ∃composed code,
                        Pe_total < ε)
```

**鍵となる構造構築** (Phase A の核): source–channel composition の Ω 拡張. 既存の source 側は
`Ω` 上の `μ` で error を measure し、channel 側は `Measure.pi (W ∘ encoder m)` で per-message
error を measure する **異なる measure space**。これを「同じ確率空間上で union bound」できる
形に bridge するには:

```lean
-- Source 側: Ω 上の event
SrcErr := { ω | jointRV Xs n ω ≠ d_src (c_src (jointRV Xs n ω)) }

-- Channel 側: Ω × (Fin n_c → β) 上の event (per-message m に対して)
ChErr m := { (ω, ys) | d_ch ys ≠ m }
         -- ys が W (c_ch.encoder m) の sample

-- 合成 (= Ω × kernel push 直積):
TotalErr := SrcErr ∪ (image of c_src ∘ jointRV Xs n を通した ChErr 適用)

-- 合成 measure:
μ_total := μ ⊗ₘ (W のブロック化 kernel via c_ch.encoder ∘ c_src ∘ jointRV Xs n)

-- 合成 error:
composedErrorProb := μ_total TotalErr

-- 主補題 (Phase A-2 errorProb_composed_le):
composedErrorProb ≤ μ SrcErr + sup_m μ_{Wm} (ChErr m)
                 = (source-side Pe) + (channel-side max-Pe)
```

**Mathlib-shape-driven の設計選択** — 在庫 §H で確認したように本 plan の主役は
`ChannelCoding.Code.errorProbAt` (= channel 側 per-message error) + `MeasureFano.errorProb`
(= source 側 Ω 上 error) であり、両者を `Measure.compProd` + `Kernel.pi` (=
`BlockwiseChannel.ofMemoryless` の per-block kernel) で couple する。理由:

1. **既存 API が `Measure.compProd` の conclusion 形に閉じている** (B-1 内部で `Code.errorProbAt`
   は `(Measure.pi (W ∘ encoder m)) (errorEvent m)` の `.toReal` で出力)。
2. **Ω 拡張 (source × channel-noise 直積) で source error event と channel error event を
   同一空間上で union bound できる** — 「source が正しく decode できた &
   channel が正しく decode できた」⇒「全体が正しく decode」の disjunction を直接 measure 化。
3. **`Measure.compProd_apply`** / `Kernel.pi_apply` の per-measurable-rect conclusion を
   そのまま使うことで、Bochner 経由の `∫⁻` 議論を回避。

**ansatz pass-through 設計** — 主定理 `separation_converse_iid` の signature で
`hR_bdd : ∃ R, ∀ n, Real.log (M_src n : ℝ) / n ≤ R` を**呼び出し側の責務**として外から要求
する。これは `source_coding_converse` (A-2) の `hM_bdd` 仮説を本 plan に pass-through する
形で、stationary ergodic source の場合に rate が unbounded growth を取らないことを保証する
ための条件。IID source で `R := capacity W + 1` 等を取れば自動的に bounded なので、実用上は
trivial だが signature 上明示的に要求する。

**4 段の論理展開** (Phase A → D):

1. **Phase A**: composition primitive 4 件
   (`composeCode` def / `composedErrorProb` def / `errorProb_composed_le` 補題 /
   `rate_scaling` 補題) を自作。本 plan **最大の novel 構造構築**。
2. **Phase B**: A-1 (source achievability) + B-1 (channel achievability) を呼んで
   `separation_achievability_iid` を組む。Phase A の `errorProb_composed_le` + union bound で
   `Pe_total < ε/2 + ε/2 = ε` を取り、`Tendsto Pe→0` で N を選ぶ。
3. **Phase C**: A-2 (source converse) + B-4 (channel converse) を per-n bound として呼び、
   `Tendsto.liminf_eq` で `liminf` を `Tendsto` に変換、`entropy ≤ capacity` を合成。
4. **Phase D**: 主定理 statement の文言整地 + docstring + `Common2026.lean` 編入 + 仕上げ。

### Approach 図

```
Phase 0  : Mathlib + Common2026 在庫                            ← 完了済
           ────────────────────────────────────────────────
Phase A  : composeCode + 合成 error bound + rate scaling        ← 0.7-1.0 セッション (Tier 0 baseline)
           ────────────────────────────────────────────────
Phase B  : achievability 主定理 (Tier 1 baseline)               ← 0.3-0.5 セッション
           ←──── 撤退ライン L-S1 (Tier 1 単独 publish) ────────→
           ────────────────────────────────────────────────
Phase C  : converse 主定理 (Tier 2 理想)                        ← 0.3-0.5 セッション
Phase D  : 主定理 wrapper + library 編入                        ← 0.1-0.2 セッション
           ────────────────────────────────────────────────
~~Phase E : stationary ergodic 一般化 (SMB 経由)~~              ← scope-out (L-S0 確定発動)
```

### 規模見積 (Tier 別)

| Tier | scope | 自作 | 累積行数 | publish 形 |
|---|---|---|---|---|
| **Tier 0** | composeCode + composedErrorProb + errorProb_composed_le + rate_scaling | Phase A | ~160 行 | def + 補題 4 件 (主定理 sorry) |
| **Tier 1** | + achievability 主定理 | Phase B | ~280 行 | `separation_achievability_iid` (Tier 1 baseline 完成) |
| **Tier 2** | + converse 主定理 | Phase C | ~400 行 | `separation_converse_iid` (理想完成形) |
| ~~**Tier 3**~~ | ~~stationary ergodic 一般化~~ | ~~Phase E~~ | ~~+1000 行~~ | **scope-out (L-S0)** — SMB closing が deferred、本 plan 範囲外 |

時間 budget: **1 セッション目標 Tier 1**。Tier 2 が同セッションで届かなければ judgement log
追記して別 plan に分離 (撤退ライン L-S1)。

### ファイル構成 (Phase D 完了想定)

```
Common2026/Shannon/
  SeparationTheorem.lean ← 新規 (~400 行 Tier 2 / ~280 行 Tier 1 baseline)
  AEP.lean               ← 既存、変更なし (source_coding_achievability / converse / per_n_bound)
  AEPRate.lean           ← 既存、変更なし (rate scaling 用 Tendsto lemma)
  ChannelCoding.lean     ← 既存、変更なし (Code bundle, errorProbAt)
  ChannelCodingShannonTheoremFullDischarge.lean ← 既存、変更なし (channel achievability)
  ChannelCodingConverseMemorylessPure.lean      ← 既存、変更なし (channel converse)
  BlockwiseChannel.lean  ← 既存、変更なし (blockwise channel kernel)
  ChannelCodingShannonTheorem.lean ← 既存、変更なし (capacity)
Common2026.lean          ← `import Common2026.Shannon.SeparationTheorem` 追記
```

## 依存関係

完了済 (黒箱 reuse、本 plan で再証明しない):

- [x] `Common2026/Shannon/AEP.lean:1138` — `source_coding_achievability` (IID source 完成形)
- [x] `Common2026/Shannon/AEP.lean:704` — `source_coding_converse` (IID source converse、`liminf` 形)
- [x] `Common2026/Shannon/AEP.lean:580` — `source_coding_per_n_bound` (per-n Fano 形)
- [x] `Common2026/Shannon/AEPRate.lean` — rate scaling 用の `Tendsto` 補題群
- [x] `Common2026/Shannon/ChannelCodingShannonTheoremFullDischarge.lean:1588` —
  `shannon_noisy_channel_coding_theorem_general_full` (DMC achievability、`hW_pos` 全 discharge 済)
- [x] `Common2026/Shannon/ChannelCodingConverseMemorylessPure.lean:650` —
  `channel_coding_converse_general_memoryless_pure` (DMC converse、semi-pure Fano 形)
- [x] `Common2026/Shannon/ChannelCoding.lean` — `Code M n α β` bundle, `Code.errorProbAt`,
  `Code.averageErrorProb`, `Channel α β`
- [x] `Common2026/Shannon/BlockwiseChannel.lean:111, :1181` — blockwise kernel + per-letter / blockwise
  capacity 同一性
- [x] `Common2026/Shannon/ChannelCodingShannonTheorem.lean:102` — `capacity` 定義
- [x] Mathlib `MeasureTheory.Measure.compProd`, `ProbabilityTheory.Kernel.pi` —
  Ω 拡張上の coupling 構築
- [x] Mathlib `Filter.Tendsto.liminf_eq` (`Topology/Order/LiminfLimsup.lean:196`) —
  converse 経路で source 側 `liminf` 形を `Tendsto` に変換
- [x] Mathlib `Fin.castLE`, `Real.exp`, `Real.log`, `Nat.ceil` — rate scaling の plumbing

---

## Phase 0 — Mathlib + Common2026 API 在庫 ✅

完了 (`docs/shannon/separation-theorem-mathlib-inventory.md`, 818 行)。

主結論:

- **既存率 ~70%** (composition 全体): source side / channel side / capacity / entropy 基盤
  は 100% 既存、composition primitive のみ 0% (要自作 4 件 ~160 行)
- **「composition なので新数学なし」は roadmap 誤推定**: source coding は Ω 上 push、
  channel coding は `Measure.pi` 上 per-message 形 で **measure space が完全不一致**、
  Ω 拡張 (source × channel-noise 直積) 上の union bound 自作 ~160 LoC が実体的工数
- **stationary ergodic 一般化は SMB Birkhoff sandwich の closing が deferred** で +1000 行を要し
  非現実的、**IID 限定で publish が必須** (撤退ライン L-S0 確定発動、判断ログ #1)
- **規模見積**: Tier 1 ~280 行 / Tier 2 ~400 行 (roadmap 300-500 と整合)
- **撤退ライン**: parent roadmap 「Lagrange / KKT」とは無関係、本 plan 固有の L-S0〜L-P1 を
  4 件起票

---

## Phase A — composition primitive (composeCode + composedErrorProb + errorProb_composed_le + rate_scaling) 📋

### スコープ

source–channel composition の Ω 拡張を建てる **本 plan 最大の novel 構造構築 phase**。
`composeCode` def (encoder ∘ encoder + decoder ∘ decoder の bundle) + `composedErrorProb` def
(Ω × channel-noise 直積上の event の measure) + `errorProb_composed_le` 補題 (union bound) +
`rate_scaling` 補題 (n_c block-length 選び方) の 4 件を取り、Phase B / C で source side /
channel side の既存 black-box を組み合わせる足場を完成させる。

### Done 条件 (Tier 0 baseline)

- `composeCode` definition publish
- `composedErrorProb` definition publish
- `errorProb_composed_le` 補題 0 sorry
- `rate_scaling` 補題 0 sorry
- `lake env lean Common2026/Shannon/SeparationTheorem.lean` で skeleton clean
  (Phase B / C / D は `sorry` 残し)
- 主定理 `separation_achievability_iid` / `separation_converse_iid` は skeleton `:= by sorry` のまま

### ステップ

- [ ] **A-0 skeleton**: `SeparationTheorem.lean` 新規ファイルに全主定理 + 補助補題を
  `:= by sorry` で並べた skeleton を Write。`import Common2026.Shannon.{AEP, AEPRate,
  ChannelCoding, ChannelCodingShannonTheoremFullDischarge,
  ChannelCodingConverseMemorylessPure, BlockwiseChannel, ChannelCodingShannonTheorem}`
  + `import Mathlib.Topology.Order.LiminfLimsup` + namespace + `open` を整備。
  LSP 診断で type-check OK 確認 (CLAUDE.md "Skeleton-driven Development")。

- [ ] **A-1 `composeCode` 定義** (~30 行):
  ```lean
  /-- Composition of a source code (encoder/decoder pair on Fin n → α_src) with a
      channel code (`Code M_ch n_c α_ch β`), via `Fin.castLE : Fin M_src → Fin M_ch`
      under the rate-matching hypothesis `M_src ≤ M_ch`. -/
  noncomputable def composeCode
      {α_src α_ch β : Type*} {n n_c M_src M_ch : ℕ}
      (c_src : (Fin n → α_src) → Fin M_src) (d_src : Fin M_src → (Fin n → α_src))
      (h_le : M_src ≤ M_ch) (c_ch : Code M_ch n_c α_ch β) :
      ((Fin n → α_src) → (Fin n_c → α_ch)) × ((Fin n_c → β) → (Fin n → α_src)) :=
    ⟨fun xs => c_ch.encoder (Fin.castLE h_le (c_src xs)),
     fun ys =>
       -- Channel decoder hands back a Fin M_ch index; pull back through M_src ≤ M_ch.
       -- If the index is out of source range, fall back to a default codeword.
       match (c_ch.decoder ys : Fin M_ch).val.decLt (M_src) with
       | isTrue h => d_src ⟨_, h⟩
       | isFalse _ => d_src 0⟩  -- default fallback for out-of-range indices
  ```
  - 詳細設計は A-1 着手時に確定 (上記は概形)。**`Fin.castLE` で injection、
    decoder 側は partial inverse + default fallback** で、out-of-range cases は
    error-event に吸収させる (union bound で押される)。
  - **`Code M_ch n_c α_ch β`** の field 名 (`encoder`, `decoder`) 在庫 §B-1 で verbatim 確認済。

- [ ] **A-2 `composedErrorProb` 定義** (~40 行):
  ```lean
  /-- Total error probability of the composed code on the product space
      `Ω × (Fin n_c → β)`, built from `μ ⊗ₘ (W ∘ encoder ∘ Fin.castLE ∘ c_src ∘ jointRV)`. -/
  noncomputable def composedErrorProb
      {Ω α_src α_ch β : Type*} [MeasurableSpace Ω]
      [Fintype α_src] [DecidableEq α_src] [Nonempty α_src]
      [MeasurableSpace α_src] [MeasurableSingletonClass α_src]
      [Fintype α_ch] [DecidableEq α_ch] [Nonempty α_ch]
      [MeasurableSpace α_ch] [MeasurableSingletonClass α_ch]
      [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
      (μ : Measure Ω) (Xs : ℕ → Ω → α_src)
      {n n_c M_src M_ch : ℕ}
      (c_src : (Fin n → α_src) → Fin M_src) (d_src : Fin M_src → (Fin n → α_src))
      (h_le : M_src ≤ M_ch)
      (W : Channel α_ch β) (c_ch : Code M_ch n_c α_ch β) : ℝ :=
    let comp := composeCode c_src d_src h_le c_ch
    (μ ⊗ₘ (BlockwiseChannel.ofMemoryless W).toKernel ∘ₖ
      Kernel.deterministic
        (fun ω => comp.1 (jointRV Xs n ω)) sorry).real
      { p : Ω × (Fin n_c → β) | comp.2 p.2 ≠ jointRV Xs n p.1 }
  ```
  - 上記は概形。**`Measure.compProd` + `Kernel.deterministic` (encoder side) +
    `BlockwiseChannel.ofMemoryless` (channel kernel)** で Ω 拡張を構築。`comp.2 p.2 ≠ jointRV Xs n p.1`
    が「decoder 出力 ≠ 元 source block」の error event。
  - 詳細 plumbing (measurable function 性証明、`Measure.compProd_apply` の rect-event 適用)
    は A-2 着手時に確定。**写経 source**: `ChannelCoding.lean` の `Code.errorProbAt` 定義と
    `Measure.pi_apply` 経由展開。

- [ ] **A-3 `errorProb_composed_le` 補題** (~60 行):
  ```lean
  /-- Union bound: total composed error ≤ source-side error + channel-side max error. -/
  lemma errorProb_composed_le
      {Ω α_src α_ch β : Type*} ...
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : ℕ → Ω → α_src) (hXs : ∀ i, Measurable (Xs i))
      {n n_c M_src M_ch : ℕ}
      (c_src : (Fin n → α_src) → Fin M_src) (d_src : Fin M_src → (Fin n → α_src))
      (h_le : M_src ≤ M_ch)
      (W : Channel α_ch β) [IsMarkovKernel W] (c_ch : Code M_ch n_c α_ch β) :
      composedErrorProb μ Xs c_src d_src h_le W c_ch
        ≤ InformationTheory.MeasureFano.errorProb μ
            (jointRV Xs n) (fun ω => c_src (jointRV Xs n ω)) d_src
          + (Finset.univ : Finset (Fin M_ch)).sup'
              ⟨0, Finset.mem_univ _⟩
              (fun m => (c_ch.errorProbAt W m).toReal)
  ```
  - 証明 sketch:
    1. **Error event 分解**: total error event ⊆ src-error event ∪ ch-error event
       (「source が正しく decode かつ channel が正しく decode ⇒ 全体正しく decode」の対偶)
    2. **`Measure.compProd_apply` + measurable rect** で union bound:
       `μ_total (A ∪ B) ≤ μ_total A + μ_total B`
    3. **Source side `μ_total A = μ A_Ω`** (channel side marginalize)
    4. **Channel side `μ_total B = ∫ μ_W(B_ω) dμ(ω) ≤ sup_m Pe_ch(m)`** (per-message bound)
  - **写経 source**: ChannelCoding.lean 内の per-message error 分解 + `Measure.compProd_apply`
    の Mathlib 既存 lemma 群。

- [ ] **A-4 `rate_scaling` 補題** (~30 行):
  ```lean
  /-- Block-length scaling: given source rate `R_src` and channel rate `R_ch < capacity W`,
      pick `n_c := ⌈n * R_src / R_ch⌉` to guarantee `M_src n ≤ ⌈exp(n_c * R_ch)⌉` for n ≥ N. -/
  lemma rate_scaling
      (M_src : ℕ → ℕ) {R_src R_ch : ℝ} (hR_src : 0 < R_src) (hR_ch : 0 < R_ch)
      (h_rate : Tendsto (fun n => Real.log (M_src n : ℝ) / n) atTop (𝓝 R_src))
      (hR_lt : R_src < R_ch) :
      ∀ ε > (0 : ℝ), ∃ N, ∀ n ≥ N,
        M_src n ≤ Nat.ceil (Real.exp ((Nat.ceil ((n : ℝ) * R_src / R_ch) : ℝ) * R_ch))
  ```
  - 証明 sketch: `Tendsto` から `∀n ≥ N, log M_src n / n ≤ R_src + δ` (δ < R_ch - R_src で
    `R_src + δ < R_ch`) → `log M_src n ≤ n · (R_src + δ)` → `M_src n ≤ exp(n · (R_src + δ))`
    → `n_c := ⌈n · R_src / R_ch⌉` の下で `n_c · R_ch ≥ n · R_src ≥ n · (R_src + δ) - (large)` を
    取って `M_src n ≤ ⌈exp(n_c · R_ch)⌉` を導く。`Nat.ceil` の monotonicity と `Real.exp` の
    monotonicity で plumbing。
  - **純算術 lemma**、Mathlib `Tendsto` + `Real.exp` + `Nat.ceil` の基本のみ。

### 工数感

~160 行 (A-0 skeleton ~10 + A-1 ~30 + A-2 ~40 + A-3 ~60 + A-4 ~30 - 重複 ~10)。
proof-log: **yes** (A-2 / A-3 で `Measure.compProd` + `Kernel.pi` の plumbing が
詰まる可能性、写経 source `ChannelCoding.lean` を精読しながら進める)。

### 失敗時 fallback

- **A-2 `composedErrorProb` 定義で `Measure.compProd` 経由が型まわりで詰まる**: 構造を
  `μ ⊗ₘ (Kernel.pi (fun i => W (...)))` の **直接 `Kernel.pi` 形** に簡略化 (`Channel.toBlock` の
  既存 wrapper があれば直接呼ぶ、`BlockwiseChannel.lean:111` を再確認)。
- **A-3 `errorProb_composed_le` で `Measure.compProd_apply` のレシピが見つからない**: union bound
  を **Ω 拡張ではなく source 側 / channel 側を separately 上界**で取り、最後に `μ × ν` の
  Cauchy 型 inequality で合算する迂回路 (+30 行)。本筋では Ω 拡張を採るがどうしても詰まれば switch。
- **A-1 の `Fin.castLE` decoder fallback が `Code.decoder` の field 型と合わない**: 在庫 §B-1 で
  `c_ch : Code M_ch n_c α_ch β` の `decoder : (Fin n_c → β) → Fin M_ch` を再確認、
  `Fin M_ch` 出力を `Fin.val` で `ℕ` に落として `< M_src` 判定 + `Fin.mk` で `Fin M_src` 再構築する
  pattern が標準 (Mathlib `Fin.castLE` の retract は既存)。

---

## Phase B — Achievability 主定理 📋

### スコープ

A-1 `source_coding_achievability` (AEP.lean:1138) と B-1 `shannon_noisy_channel_coding_theorem_general_full`
(ChannelCodingShannonTheoremFullDischarge.lean:1588) を呼び、Phase A の
`errorProb_composed_le` + `rate_scaling` で `separation_achievability_iid` を組む。

### Done 条件 (Tier 1 baseline 完成)

- `separation_achievability_iid` 主定理 0 sorry
- `lake env lean Common2026/Shannon/SeparationTheorem.lean` clean (Phase C / D は sorry 残し可)
- Tier 1 baseline として **そのまま公開可能** な形に到達 (撤退ライン L-S1 trigger 時 close 可)

### ステップ

- [ ] **B-1 rate splitting** (~15 行):
  - `entropy μ (Xs 0) < capacity W` から rate `R_src, R_ch` を取る:
    `R_src := (entropy μ (Xs 0) + capacity W) / 2`, `R_ch := (R_src + capacity W) / 2` で
    `entropy < R_src < R_ch < capacity W` を確保。`linarith`。

- [ ] **B-2 source achievability 呼出し** (~10 行):
  - `source_coding_achievability μ Xs hXs hpos hindep_full hident (R := R_src) hHR_src` で
    `M_src : ℕ → ℕ`, `c_src`, `d_src`, `Tendsto rate (𝓝 R_src)`, `Tendsto Pe_src (𝓝 0)` を取得。
  - 在庫 §A-1 で signature verbatim 確認済。

- [ ] **B-3 channel achievability 呼出し** (~10 行):
  - `shannon_noisy_channel_coding_theorem_general_full W hR_ch_pos hRC_lt (ε := ε/2) hε_half`
    で `N_ch : ℕ`, `∀ n_c ≥ N_ch, ∃ M_ch c_ch, ∀ m, Pe_ch(m).toReal < ε/2` を取得。
  - 在庫 §B-1 で signature verbatim 確認済。

- [ ] **B-4 N 選び方** (~20 行):
  - `Tendsto Pe_src (𝓝 0)` から `∃ N_src, ∀ n ≥ N_src, Pe_src n < ε/2`
  - `rate_scaling` (A-4) で `∃ N_rate, ∀ n ≥ N_rate, M_src n ≤ ⌈exp(n_c · R_ch)⌉` (with
    `n_c := ⌈n · R_src / R_ch⌉`)
  - `N_rate` を取って `n_c (n) ≥ N_ch` を保証する `N_block` を取る (linear scaling で trivial)
  - `N := max (max N_src N_rate) N_block`

- [ ] **B-5 主定理合成** (~45 行):
  ```lean
  theorem separation_achievability_iid
      ... :
      ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
        ∃ (n_c M_src M_ch : ℕ) (h_le : M_src ≤ M_ch)
          (c_src : (Fin n → α_src) → Fin M_src) (d_src : Fin M_src → (Fin n → α_src))
          (c_ch : Code M_ch n_c α_ch β),
          composedErrorProb μ Xs c_src d_src h_le W c_ch < ε
  ```
  - 証明 sketch:
    1. B-1 で `R_src, R_ch` 確保
    2. B-2 で source code 取得 (`M_src n`, `c_src n`, `d_src n`)
    3. B-3 で `N_ch` + per-block channel code 取得
    4. B-4 で `N` 確定
    5. `∀ n ≥ N` で:
       - `n_c := ⌈n · R_src / R_ch⌉` (`rate_scaling` の n_c)
       - B-3 を `n_c` に適用して `c_ch : Code M_ch n_c α_ch β` 取得
       - `M_src n ≤ ⌈exp(n_c · R_ch)⌉ ≤ M_ch` を rate_scaling + B-3 から導出 (`h_le`)
       - `errorProb_composed_le` (A-3) で
         `composedErrorProb ≤ Pe_src n + sup_m Pe_ch(m) < ε/2 + ε/2 = ε`

### 工数感

~100 行 (B-1 ~15 + B-2 ~10 + B-3 ~10 + B-4 ~20 + B-5 ~45)。proof-log: **yes**
(B-4 + B-5 の N 選び方で `rate_scaling` の n_c 出力と B-3 の N_ch を合わせる plumbing が
詰まる可能性、Phase A-4 で取った `rate_scaling` の statement 形を再確認しながら進める)。

### 失敗時 fallback

- **B-3 の `hR_ch < capacity W` 仮定で `0 < R_ch` が trivial に出ない**: `entropy μ (Xs 0)`
  が non-negative (既存 lemma) で `R_src > 0`、`R_ch > R_src > 0` から導出。
- **B-5 の `errorProb_composed_le` 適用で型まわりが合わない**: A-3 の signature を再確認、
  `Fintype` / `MeasurableSingletonClass` インスタンスが全て揃っているか LSP で確認。
  足りないインスタンスは file header の `variable` ブロックに追加。
- **B-4 + B-5 で 150 行を超える**: **撤退ライン L-S1 発動** (Tier 1 baseline 単独 publish)、
  Phase C converse は別 plan に分離。判断ログに append。
- **B-3 の max-error 形が composition で扱いづらい (sup_m が `Finset.sup'` で型まわり煩雑)**:
  **撤退ライン L-S3 発動** (avg-error 形採用): `Code.averageErrorProb` を呼んで
  `Pe_avg ≤ sup_m Pe_max` の trivial bound で逃げる (本筋は max-error、L-S3 は fallback)。

---

## Phase C — Converse 主定理 📋

### スコープ

A-2 `source_coding_converse` (AEP.lean:704) + B-4 `channel_coding_converse_general_memoryless_pure`
(ChannelCodingConverseMemorylessPure.lean:650) を per-n bound として呼び、`Tendsto.liminf_eq`
で source 側 `liminf` 形を channel 側 per-n bound と合成して `entropy ≤ capacity` を取る。

### Done 条件

- `separation_converse_iid` 主定理 0 sorry
- `lake env lean Common2026/Shannon/SeparationTheorem.lean` clean

### ステップ

- [ ] **C-1 source converse 呼出し** (~15 行):
  - `source_coding_converse μ Xs hXs hindep_full hident hcard M c d hPe_to_zero_src hR_bdd_src`
    で `entropy μ (Xs 0) ≤ Filter.liminf (fun n => Real.log (M n : ℝ) / n) atTop` 取得。
  - 在庫 §A-2 で signature verbatim 確認済。`hM_bdd` は本 plan signature の `hR_bdd` から
    渡す (pass-through 設計、判断ログ #2 参照)。

- [ ] **C-2 channel converse per-n bound 呼出し** (~30 行):
  - `channel_coding_converse_general_memoryless_pure` を per-n で呼ぶ:
    `Real.log (Fintype.card M_ch n) ≤ ∑ I(X_i; Y_i).toReal + Fano`
  - **困難**: B-4 は `hMsg_uniform` (uniform message) を仮定するが、source-encoded index は
    概一様でしかない。**撤退ライン L-S2 発動**: 近似 uniform fallback (~50 行) で
    `Pe ≤ (uniform Pe) + (距離 boundedness term)` で押さえる。
    詳細は L-S2 §で議論。
  - 各 i での MI 上界 `I(X_i; Y_i) ≤ capacity W` (capacity の定義: sup over input dist の MI) を
    `capacity` def + `le_sSup` で適用 → `∑ I(X_i; Y_i) ≤ n_c · capacity W`

- [ ] **C-3 Tendsto ↔ liminf bridge** (~30 行):
  - C-2 から `Real.log (Fintype.card M_ch n) ≤ n_c · capacity W + Fano(Pe_n)`
  - `Pe_n → 0` から `Fano(Pe_n) / n → 0` (`Real.binEntropy_continuous` + `tendsto_one_div_atTop_nhds_zero_nat`、
    在庫 §E-1 で確認)
  - `Real.log M / n ≤ (n_c / n) · capacity W + (Fano / n)` → `liminf (log M / n) ≤
    (lim n_c/n) · capacity W + 0 = (R_src / R_ch) · capacity W ≤ capacity W` (with `R_src ≤ R_ch`
    から `R_src / R_ch ≤ 1`)
  - C-1 と組み合わせ: `entropy μ (Xs 0) ≤ liminf (log M / n) ≤ capacity W`

- [ ] **C-4 主定理合成** (~25 行):
  ```lean
  theorem separation_converse_iid
      ... :
      entropy μ (Xs 0) ≤ capacity W
  ```
  C-1 + C-2 + C-3 を linarith で合成。

### 工数感

~100 行 (C-1 ~15 + C-2 ~30 + C-3 ~30 + C-4 ~25)。proof-log: **yes** (C-2 の
uniform-message bridge と C-3 の Tendsto↔liminf bridge は本 plan で最も繊細な箇所、
両方とも詰まれば撤退ライン L-S2 / L-P1 を検討)。

### 失敗時 fallback

- **C-2 で uniform-message bridge が 100 行を超える**: **撤退ライン L-S2 発動**: converse の
  statement を「**uniform-message source の場合に entropy ≤ capacity**」に弱める (本来 IID 一般で
  uniform でないが、撤退として uniform 限定で publish)。Tier 2 converse は IID-uniform に限定。
- **C-3 で `Filter.Tendsto.liminf_eq` の `IsBoundedUnder` / `IsCoboundedUnder` 解決が詰まる**:
  `isBoundedDefault` で自動解決を試みる。それでも失敗なら手動で `IsBoundedUnder.isBoundedUnder_le` /
  `IsCoboundedUnder.le` を構築 (~10 行 plumbing 追加)。
- **C-2 + C-3 + C-4 で 150 行を超える**: 既に Tier 1 publish 済なので **converse 単独で別 plan**
  に分離する余地あり (L-P1)。Tier 2 完成は postpone、本 plan は Tier 1 baseline + converse skeleton
  (statement のみ) で publish。

---

## Phase D — 主定理 wrapper + library 編入 📋

### スコープ

主定理 statement の文言整地 (docstring、Tier 1 / Tier 2 の関係、textbook reference) +
`Common2026.lean` 編入 + 仕上げ。

### Done 条件

- `Common2026.lean` に `import Common2026.Shannon.SeparationTheorem` 追記
- `lake env lean Common2026.lean` clean
- 主定理 4 件 (composeCode def / composedErrorProb def / separation_achievability_iid /
  separation_converse_iid) 全て 0 sorry / 0 warning
- (任意) `source_coding_achievability` / `shannon_noisy_channel_coding_theorem_general_full`
  との cross-link コメント

### ステップ

- [ ] **D-1 docstring 整地**: 各主定理に Cover–Thomas Theorem 7.13.1 reference + Tier 1 / Tier 2
  関係 + IID 限定の理由 (本 plan 判断ログ #1 への pointer) + composition primitive 自作の背景
  (判断ログ #2) を docstring に記載

- [ ] **D-2 `Common2026.lean` 編入**: `import Common2026.Shannon.SeparationTheorem` 追記

- [ ] **D-3 最終 verify**: `lake env lean Common2026.lean` clean 確認 + `Common2026/Shannon/`
  全体回帰チェック (`lake env lean Common2026/Shannon/AEP.lean` 等が dependent 経由で
  壊れていないか)

- [ ] **D-4 cross-link コメント** (任意): `AEP.lean` の `source_coding_achievability` docstring +
  `ChannelCodingShannonTheoremFullDischarge.lean` の `shannon_noisy_channel_coding_theorem_general_full`
  docstring に「T3-E `separation_achievability_iid` の主要 building block」コメントを追記。

### 工数感

~20-30 行 (D-1 docstring ~15 + D-2/3 plumbing ~5 + D-4 任意 ~5)。proof-log: no。

### 失敗時 fallback

- **D-3 で dependent 経由 break** → 該当 file に oleans refresh
  (`lake build Common2026.Shannon.SeparationTheorem` 1 回)。CLAUDE.md "After upstream edits"
  節参照。

---

## ~~Phase E — Stationary ergodic 一般化~~ 🔄 (撤退ライン L-S0 発動、判断ログ #1)

**scope-out**: 在庫 §D-6 で確認したように SMB (`shannon_mcmillan_breiman_of_sandwich`) は
**Birkhoff sandwich を 4 仮説で受ける形** (`ShannonMcMillanBreiman.lean:85`) で **未閉**。
stationary ergodic 一般化を本 plan に含めると **SMB 全体 closing + entropy rate 経路の
source coding 拡張** で +1000 行を要し、roadmap 規模見積もり (300–500 行) を 3–5 倍超過する。

**代替設計**: stationary ergodic 一般化は **別 seed `separation-theorem-stationary-ergodic-*`**
として将来扱う。本 plan は IID 限定で 0 sorry publish。

---

## 撤退ライン

### Scope 縮小ライン (発動時に publish 範囲縮退)

- **L-S0 (確定発動)**: **stationary ergodic 一般化を scope-out、IID 限定で publish**
  - 発動条件 (確定): inventory §D-6 で SMB Birkhoff sandwich が未閉、本 plan に含めると +1000 行
  - 縮退後: IID source `iIndepFun + IdentDistrib` 限定で `separation_achievability_iid` /
    `separation_converse_iid` を publish、stationary ergodic 一般化は別 seed へ
  - **判断ログ #1 で正式 import**、Phase E は本 plan 範囲外 (取り消し線で残す)

- **L-S1**: **Tier 1 (achievability) のみで publish** (~280 行)、Tier 2 converse は別 plan に
  - 発動条件:
    - Phase C で uniform-message bridge (`hMsg_uniform` 仮説の workaround) が 100 行+ で詰まる
    - Phase B + C 合計が 350 行 (中央予測 280 行) を超える
    - Tier 2 が 1 セッションで届かない
  - 縮退後: Tier 1 主定理 (`separation_achievability_iid`) のみで publish、
    `separation_converse_iid` は別 plan `separation-theorem-converse-*` へ
  - **判断ログに必ず append** + 移行先 plan の seed pointer を本 plan §進捗に追記

- **L-S2**: **converse を uniform-message source 限定で publish** (Tier 2 縮退)
  - 発動条件: Phase C-2 で B-4 channel converse の `hMsg_uniform` 仮説の workaround
    (近似 uniform fallback) が 100 行+ で詰まる
  - 縮退後: `separation_converse_iid` の statement に「source が channel encoder 経由で
    uniform message を生成する場合」を追加仮定として明記、IID 一般化は scope-out
  - **公開価値**: uniform-message converse は textbook 7.13.1 の主要部分で、
    publish 単独でも教科書原稿 (層 3) に組み込み可能。一般化は別 plan へ。

- **L-S3**: **avg-error 形採用** (channel side max-error → avg-error 弱化)
  - 発動条件: Phase B-5 / Phase A-3 で max-error の `Finset.sup'` 取り回しが型まわりで詰まる
  - 縮退後: `Code.averageErrorProb` (ChannelCoding.lean:210) を使い、composition 全体を
    avg-error 形で publish。`Pe_avg ≤ Pe_max` の trivial bound で max-error 形に上向き bound 可能
  - **設計上の trade-off**: avg-error 形は statement が weak だが、composition の plumbing が
    簡略化される。max-error 形が動く限り max-error で。

### 自作 plumbing 肥大ライン (新規)

- **L-P1**: **Phase A composition primitive 自作量が 250 行を超える**
  - 発動条件: A-2 `composedErrorProb` (Ω 拡張上の measure 構成) と A-3 `errorProb_composed_le`
    (union bound) が `Measure.compProd` + `Kernel.pi` の plumbing で詰まり、各 100 行+ に膨らむ
  - 縮退案 (2 段):
    - **(L-P1a) Statement 弱化**: 主定理を「**composed code が存在**」(具体 measure 構成なし) の
      statement-level conclusion に弱め、`composedErrorProb` の具体 def を黒箱化 (関数 signature
      のみ publish、内部実装は別 plan)。**規模 -80 行**。
    - **(L-P1b) Channel side separately**: composition を Ω 拡張せず source side / channel side
      separately で Pe を上界、最後に Cauchy 型 inequality で合算 (Ω 拡張迂回路、+30 行)。
  - **本 plan の元設計**: Ω 拡張 (`Measure.compProd` 経由) で organic に union bound。
    L-P1 trigger 時点で「Ω 拡張迂回路 (L-P1b) を試す → それでも詰まれば statement 弱化 (L-P1a)」
    の順で対応。

- **L-P2**: **`Fin.castLE` decoder fallback が `Code.decoder` の field 型と合わない**
  (Phase A-1)
  - 発動条件: A-1 で `Fin M_ch → Fin M_src` の partial inverse を `Fin.castLE` + default fallback
    で書こうとして type mismatch
  - 縮退案: `composeCode` の decoder 側を **`Option (Fin M_src)`** で wrapping し、`some` ケースで
    `d_src`、`none` ケースで default codeword に fallback。Mathlib `Fin.toNat` + `Nat.find` 経由の
    standard pattern (~10 行 plumbing 追加)。

### proof 規模超過ライン

- **L-P3**: **Tier 2 までで 500 行を超える** (roadmap 上限 500 ライン)
  - 発動条件: Phase A + B + C 合計が 500 行 (中央予測 400 行) を超える
  - 縮退案: L-S1 (Tier 1 単独) 発動。Tier 2 converse の自作 plumbing (特に L-S2 uniform-message
    bridge) が膨らんでいる場合、まず L-S2 で uniform-message 限定に縮退、それでも詰まれば分離。

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| **Phase A-2 `composedErrorProb` 定義で `Measure.compProd` + `Kernel.pi` の型まわりが詰まる** | **高** | 高 (A-2 +30-60 行) | 写経 source `ChannelCoding.lean` の `Code.errorProbAt` 定義と `Measure.pi_apply` 経由展開を**精読してから着手**。`BlockwiseChannel.ofMemoryless` (BlockwiseChannel.lean:111) の wrapper を活用、`Kernel.deterministic` (encoder side) + `BlockwiseChannel.toKernel` (channel side) の合成で per-block kernel を構築。詰まれば撤退ライン L-P1b (Ω 拡張迂回路) に switch。 |
| **Phase A-3 `errorProb_composed_le` の union bound が `Measure.compProd_apply` の rect-event 適用で詰まる** | **中** | 中 (A-3 +30 行) | `μ_total (A ∪ B) ≤ μ_total A + μ_total B` を `MeasureTheory.measure_union_le` で取り、source side `μ_total A = μ A_Ω` (channel side marginalize)、channel side `μ_total B = ∫ μ_W(B_ω) dμ(ω) ≤ sup_m Pe_ch(m)` の plumbing は `Measure.compProd_apply_prod` / `Kernel.pi_apply_prod` の Mathlib 既存 lemma を活用。 |
| **Phase B-5 で `errorProb_composed_le` 適用時に Fintype / MeasurableSingletonClass インスタンス不足** | 中 | 低 (1-5 行 plumbing) | file header の `variable` ブロックに必要なインスタンスを **A-0 skeleton 時に全て揃えておく** (`[Fintype α_src] [DecidableEq α_src] [Nonempty α_src] [MeasurableSpace α_src] [MeasurableSingletonClass α_src]` を α_src / α_ch / β 全て)。LSP で `#check` して確認。 |
| **Phase C-2 で B-4 channel converse の `hMsg_uniform` (uniform message) 仮説が IID source-encoded index で trivially 取れない** | **高** | 高 (C-2 +50-100 行) | source-encoded index は概一様 (entropy maximizer) だが完全一様ではない。**撤退ライン L-S2 発動**: converse を「source が uniform message を生成する場合」に限定して publish、IID 一般化は別 plan へ。**本筋 attempt**: 近似 uniform fallback (`Pe ≤ (uniform Pe) + (距離 boundedness term)`) を ~50 行で書く。 |
| **Phase C-3 `Filter.Tendsto.liminf_eq` の `IsBoundedUnder` / `IsCoboundedUnder` 解決** | 中 | 低 (C-3 +5-10 行) | `isBoundedDefault` で自動解決を試みる。失敗時は `IsBoundedUnder.isBoundedUnder_le` / `IsCoboundedUnder.le` を手動構築 (`hR_bdd` から `IsBoundedUnder` は trivial)。 |
| **Phase A-4 `rate_scaling` の `Nat.ceil (Real.exp ...)` の monotonicity 操作が tactic で重い** | 中 | 中 (A-4 +15 行) | `Nat.ceil_mono` + `Real.exp_le_exp` + `mul_le_mul_of_nonneg_right` を組み合わせて bulldoze。詰まれば `nlinarith` で代替。Mathlib `Real.exp_log` (`0 < x → Real.exp (Real.log x) = x`) で `M_src n` の `log/exp` round-trip を扱う。 |
| **Phase A-1 `composeCode` decoder fallback (`Fin.castLE` の partial inverse)** | 中 | 低 (A-1 +10 行) | 撤退ライン L-P2 で `Option (Fin M_src)` wrapping pattern を採用、または `if-then-else` で `(c_ch.decoder ys : Fin M_ch).val < M_src` を分岐させて `Fin M_src` を構築。Mathlib `Fin.castLT` (in-range 版) の存在を loogle で再確認。 |
| **proof 規模が roadmap 上限 (~500 Tier 2) を超える** | 中 | 中 (1 セッションで完走できない) | 撤退ライン L-S1 で Tier 1 単独 publish、Phase C 別 plan 化。Tier 1 baseline ~280 行は 1 セッションで届く想定。さらに Phase A 自作 (~160 行) が膨らむ場合は L-P1 で composition primitive 自作量を縮退 (statement 弱化 or Ω 拡張迂回路)。 |
| **B-4 channel converse の `[StandardBorelSpace M]` / `[StandardBorelSpace α]` / `[StandardBorelSpace β]` 型クラス** | 低 | 低 (header に追加) | 在庫 §G で `[Fintype]` + `[MeasurableSingletonClass]` で自動派生 (ChannelCodingConverseMemorylessPure.lean:632-636 で確認済) と判明。file header `variable` で `[StandardBorelSpace α_ch] [StandardBorelSpace β]` を明示的に書いておくと安全。 |
| **`Tendsto.liminf_eq` の hypothesis (`NeBot (𝓝 R)`) が解決しない** | 低 | 低 (C-3 +5 行) | `Filter.atTop.neBot` (auto), `NeBot.map`, `(𝓝 R).neBot` (= `nhds_neBot`) を組み合わせて明示。 |

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(2026-05-19) Stationary ergodic 一般化を scope-out、IID 限定で publish (撤退ライン L-S0
   確定発動)**: 在庫調査 (`separation-theorem-mathlib-inventory.md` §D-6) で SMB
   `shannon_mcmillan_breiman_of_sandwich` (`ShannonMcMillanBreiman.lean:85`) が **Birkhoff
   sandwich を 4 仮説で受ける形** で未閉、`smb-two-sided-extension-plan.md` (53 KB) も deferred
   状態と判明。stationary ergodic 一般化を T3-E に含めると **SMB 全体 closing (+700-1000 行) +
   entropy rate 経路の source coding 拡張 (+150 行)** で +1000 行となり、roadmap 規模見積もり
   (300–500 行) を 3–5 倍超過する。本 plan は **IID source `iIndepFun + IdentDistrib` 限定**で
   `separation_achievability_iid` / `separation_converse_iid` を publish。stationary ergodic
   一般化は **別 seed `separation-theorem-stationary-ergodic-*`** として将来扱う。Phase E は
   取り消し線で残す (過去参照のため)。

2. **(2026-05-19) Composition primitive 自作を確定 (roadmap の「composition なので新数学なし」
   推定を撤回)**: 在庫調査 §C で source coding 側 (`AEP.lean`) の出力 `MeasureFano.errorProb μ
   (X^n) (c∘X^n) d` (Ω 上 push) と channel coding 側 (`ChannelCoding.lean`) の出力
   `Code.errorProbAt c W m = Measure.pi (W ∘ encoder m) (errorEvent m)` (`Fin n_c → β` 上 pi-measure)
   が **definition-level で measure space が完全不一致**、Mathlib にも Common2026 にも source–channel
   composition の primitive (`composeCode` 系) が **不在**と確認。roadmap の「composition なので
   新数学なし」推定は誤りで、**Ω 拡張 (source × channel-noise 直積) 上の union bound novel
   ~160 LoC が実体的工数**。本 plan の Phase A で `composeCode` def (encoder ∘ encoder + decoder ∘
   decoder の bundle) + `composedErrorProb` def (Ω × `Fin n_c → β` 直積上の event の measure) +
   `errorProb_composed_le` 補題 (union bound) + `rate_scaling` 補題 (n_c block-length 選び方) の
   4 件を自作する設計。`Measure.compProd` + `Kernel.pi` (= `BlockwiseChannel.ofMemoryless`) で
   coupling を取り、`Measure.compProd_apply_prod` の per-rect conclusion で union bound を直接
   適用。`ChannelCoding.lean` の `Code.errorProbAt` 定義と `Measure.pi_apply` 経由展開を写経 source
   として進める。

3. **(2026-05-19) 規模見積を roadmap 300–500 → ~400 行 (Tier 2 / IID 限定) に再評価**: 在庫調査
   §K-L で「source side / channel side / capacity / entropy 基盤は 100% 既存 (Mathlib + Common2026
   合算)、composition primitive のみ 0% (要自作 ~160 行)、合計 既存率 70%」と判定、roadmap
   見積もりに対し:
   - **achievability のみ (Tier 1) + IID 限定 + 撤退ライン L-S3 (avg-error) 込で 250–350 行**
   - **converse 込み (Tier 2) で 350–500 行**
   - stationary ergodic 一般化 (Phase E) を含めると +700–1000 行で 1000+ 行 (非現実的、L-S0 確定発動)
   1 セッション目標を **Tier 1 baseline (~280 行)** とし、Tier 2 が同セッションで届かなければ
   judgement log 追記して別 plan 分離 (撤退ライン L-S1)。**もっとも危険な発見** (在庫 §M) は
   Phase A 自作 (composition primitive 160 行) + Phase C uniform-message bridge (~50-100 行) の
   2 点で、両者とも撤退ライン (L-P1 / L-S2) で段階的にスコープ縮退する設計。

4. **(2026-05-19) Tier 1 (achievability) ship 完了、撤退ライン L-S3 採用 (avg-error 形)**:
   composition primitive を `Measure.compProd` ベースの Ω 拡張上の event 測度ではなく、
   **source-side `MeasureFano.errorProb` + channel-side `Code.averageErrorProb`** の和として
   定義 (`composedErrorProb`)。利点: `Measure.compProd_apply` / `Kernel.pi_apply` plumbing
   を完全に回避し、Tier 1 を 1 セッションで届かせた。実体的工数は plan 中央予測 ~280 行に対し
   `SeparationTheorem.lean` 全体 ~350 行 (Tier 0 + Tier 1 + 補助補題)、Phase A/B/D 完了。
   Tier 2 converse (`separation_converse_iid`) は別 seed `separation-theorem-converse-*` に
   分離 (撤退ライン L-S1 部分発動)。textbook 形 (Ω 拡張上の event 測度 ≤ source + channel-max)
   は将来 `separation-theorem-omega-extension-*` で追加可能。

   **Tier 1 公開 API** (`Common2026.Shannon.SeparationTheorem`):
   - `composeEncoder`, `composeDecoder`: source∘channel encoder/decoder の bundle
   - `composedErrorProb`: source-side + channel-side avg-error の和 (union bound 上界)
   - `composedErrorProb_le_of_channel_max`: max-error から avg-error への bridge
   - `composedErrorProb_lt_of_components`: ε-strict union bound
   - `separation_achievability_iid`: 主定理 (`H < C ⇒ ∃ N, ∀ n ≥ N, composed code < ε`)
