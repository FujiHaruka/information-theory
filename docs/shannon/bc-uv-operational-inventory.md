# BC UV 外界の操作的包含 (Phase 4b) — MAC 橋からの読み替え在庫

> **Parent**: [`bc-general-region-plan.md`](bc-general-region-plan.md) Phase 4b M0

## 一行サマリ

**Phase 4b で必要な 60 decl 相当のうち、MAC 側から `reuse` (de-privatize のみ) できるのが 9 本
238 行 / `mirror` (機械的書き直し) が 33 本 / `restructure` (設計判断が要る) が 5 本 /
`absent` (BC には不要) が 6 本。総行数見積りは推奨ルート (時間共有変数を補助変数に吸収) で
約 1330 行、MAC 実績 2191 行 (`Bridge.lean` 1238 + `Assembly.lean` 953) の約 6 割。**
結合 Markov の既定 (b)「操作的 wrapper 側で μ の構成から導く」は **実行可能** (根拠 → 表 2 §結論)。
撤退ライン **L-BCO4 は不発動見込み**。ただし plan の Phase 4b チェックリストに載っていない
新規難所が 2 つある (補助変数の型統一 / 退化レートの被覆)。

**最大の危険**: `uvAux W Y₁s Y₂s i` の**型が `i` に依存する**
(`Ω → ξ × ((Fin i.val → β₁) × ({j : Fin n // i.val < j.val} → β₂))`, `OuterBoundUV.lean:71-73`)。
単一文字分布の集合として `bcOuterRegionUV` を定義する以上、n 文字ぶんの補助変数を
**共通のアルファベットに載せ替える層**が必須で、MAC には対応物が一切ない (MAC の per-letter
オブジェクトは固定型 `α₁ / α₂` 上の入力分布だった)。

---

## 前提の確認 (plan 記載 line 番号の実測照合)

plan `docs/shannon/bc-general-region-plan.md` の在庫表に載る line 番号を全件実ファイル照合した。
**ズレはゼロ**。以下すべて一致:

| plan 記載 | 実測 | 判定 |
|---|---|---|
| `Operational.lean:53` `BCAchievable` / `:68` `bcCapacityRegion` | 53 / 68 | ✅ |
| `Operational.lean:102` / `:71` / `:86` (閉性・単調性・closure 回収) | 102 / 71 / 86 | ✅ |
| `Operational.lean:121` `martonRegion` / `:149` `marton_region_subset_capacity` | 121 / 149 | ✅ |
| `OuterBound.lean:380` `bcOuterRegionCoop` / `:408` `bc_capacity_subset_coop` | 380 / 408 | ✅ |
| `OuterBound.lean:50`–`:262` (`restrict₁` 50 / `restrict₂` 56 / `coop` 62 / `averageErrorProb_coop_le` 242) | 一致 | ✅ |
| `OuterBoundUV.lean:71` `uvAux` | 71 | ✅ |
| `OuterBoundUV.lean:113 / :174 / :684 / :637` 単一文字化 4 本 | 一致 | ✅ |
| `OuterBoundUV.lean:735` `InBCOuterRegionUV` / `:815` `bc_uv_converse` | 735 / 815 | ✅ |
| `Bridge.lean` 1238 行 / 48 decl、`macConverseAmbient:348` / `mac_converse_from_code:777` / `mac_converse_rate_extract:854` / per-letter `:1109`–`:1214` | 一致 | ✅ |
| `Bridge.lean:94` `mac_avgPentagon_mem_convexHull` | 94 | ✅ |
| `TimeSharing.lean:49 / :58 / :66` | 一致 | ✅ |
| `Reconciliation.lean:292` `mac_capacity_region_reconciliation` | 292 | ✅ |

**plan の在庫表が落としている資産が 1 本ある**:
`InformationTheory/Shannon/MultipleAccess/TimeSharingConverse/Assembly.lean` (**953 行 / 12 decl**)。
`Bridge.lean` は「符号 → ambient + レート抽出 + per-letter 同定」までで、
**集合化 (`⊆` の組み立て) と Fano slack → 0 の極限は全部 `Assembly.lean` にある**。
Phase 4b が到達目標にしている `bc_capacity_subset_uv` の対応物は
`mac_timesharing_converse` (`Assembly.lean:817`) と `mac_timesharing_capacity_region` (`:908`) なので、
**4b の雛形は `Bridge.lean` 単独ではなく `Bridge.lean` + `Assembly.lean` = 2191 行**。
plan の「MAC 実績 1238 行と同等以上」という外挿は分母を約半分に見積もっている。

**in-repo 事前探索 (結論形)**: `rg "Set \(ℝ × ℝ\)"` で region 型の def は 4 本のみ
(`bcCapacityRegion` / `macCapacityRegion` / `bcOuterRegionCoop` / `kernelBox`)。
`rg "Fin M₁ × Fin M₂\) × \(Fin n"` は `Bridge.lean` のみヒット。
`bcAmbientMeasure` (`Achievability/Setup.lean:71`) は達成側の i.i.d. ambient
(`Measure.infinitePi (fun _ ↦ bcJointDistribution pU K W)`) で**符号を引数に取らない**ため、
符号 → ambient の橋としては使えない。→ **BC 側の符号→ambient 橋は真に不在**を確認。

---

## 表 1 — MAC `Bridge.lean` → BC 読み替え対応表

行数は「その decl の開始行 → 次の decl の開始行」から docstring 行を引いた実測概算。
署名は `scripts/sig_view.ts` の出力 + `#check` 実測 (`lake env lean` で elaborate 済) から逐語。

### 1-A. 凸幾何ゲートウェイ (`Bridge.lean:25`–`:279`)

| MAC decl (`file:line`) | 逐語署名 (型クラス前提込み) | 行数 | BC 対応物 | 区分 | 新規行数 | 難所 |
|---|---|---|---|---|---|---|
| `convexHull_mem_of_le`<br>`Bridge.lean:25` | `private lemma convexHull_mem_of_le {s : Set (ℝ × ℝ)} (hpos : ∀ pt ∈ s, 0 ≤ pt.1 ∧ 0 ≤ pt.2) (hdown : ∀ pt ∈ s, ∀ x y : ℝ, 0 ≤ x → x ≤ pt.1 → 0 ≤ y → y ≤ pt.2 → (x, y) ∈ s) {q p : ℝ × ℝ} (hq : q ∈ convexHull ℝ s) (hp1 : 0 ≤ p.1) (hp2 : 0 ≤ p.2) (hle1 : p.1 ≤ q.1) (hle2 : p.2 ≤ q.2) : p ∈ convexHull ℝ s` | 63 | 凸包ルートを採る場合のみ | `absent` (推奨ルート) | 0 | `private` なので凸包ルートなら複製か de-privatize が要る |
| `mac_avgPentagon_mem_convexHull`<br>`Bridge.lean:94` | `theorem mac_avgPentagon_mem_convexHull {n : ℕ} (hn : 0 < n) (a b c : Fin n → ℝ) (h0a : ∀ i, 0 ≤ a i) (h0b : ∀ i, 0 ≤ b i) (hac : ∀ i, a i ≤ c i) (hbc : ∀ i, b i ≤ c i) (hsub : ∀ i, c i ≤ a i + b i) {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (h1 : R₁ ≤ (∑ i, a i) / n) (h2 : R₂ ≤ (∑ i, b i) / n) (hs : R₁ + R₂ ≤ (∑ i, c i) / n) : (R₁, R₂) ∈ convexHull ℝ (⋃ i, ({p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ a i ∧ p.2 ≤ b i ∧ p.1 + p.2 ≤ c i} : Set (ℝ × ℝ)))`<br>**型クラス前提は皆無** (純実解析) | 109 | 凸包ルートなら 4 制約版が要る | `restructure` | 0 (推奨) / 170 (凸包ルート) | 表 3 §リスク。`hac`/`hbc` に相当する **`I₁ᵢ ≤ J₂ᵢ` が一般 BC で成立しない** |
| `mac_macInfo₁_le_macInfoBoth`<br>`Bridge.lean:231` | `theorem mac_macInfo₁_le_macInfoBoth (p₁ : Measure α₁) [IsProbabilityMeasure p₁] (p₂ : Measure α₂) [IsProbabilityMeasure p₂] (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] : macInfo₁ p₁ p₂ W ≤ macInfoBoth p₁ p₂ W` | 29 | (同上) | `restructure` | 0 / 120 | UV では chain rule で出ない (表 3) |
| `mac_macInfo₂_le_macInfoBoth`<br>`Bridge.lean:260` | 上と同型 (`macInfo₂ ≤ macInfoBoth`) | 19 | (同上) | `restructure` | 0 / (上に込み) | 同上 |

### 1-B. CodeToAmbient (`Bridge.lean:294`–`:821`) — 4b の心臓

| MAC decl (`file:line`) | 逐語署名 (型クラス前提込み) | 行数 | BC 対応物 | 区分 | 新規行数 | 難所 |
|---|---|---|---|---|---|---|
| `uniformCount_isProbabilityMeasure`<br>`:310` | `instance uniformCount_isProbabilityMeasure {X : Type*} [Fintype X] [Nonempty X] [MeasurableSpace X] [MeasurableSingletonClass X] : IsProbabilityMeasure ((Fintype.card X : ℝ≥0∞)⁻¹ • Measure.count : Measure X)` | 10 | 同名 instance | `reuse`* | 0 (import) / 10 (複製) | *MAC namespace の instance。BC から使うには `MultipleAccess.TimeSharingConverse.Bridge` を import (MAC 家系全部が入る) → 共有モジュールへ移設を推奨 |
| `macConverseInput`<br>`:322` | `noncomputable def macConverseInput (M₁ M₂ : ℕ) : Measure (Fin M₁ × Fin M₂)` | 4 | `bcConverseInput` | `mirror` | 4 | BC も独立一様 2 メッセージなので完全同型 |
| `macConverseInput_isProbabilityMeasure`<br>`:326` | `instance … [NeZero M₁] [NeZero M₂] : IsProbabilityMeasure (macConverseInput M₁ M₂)` | 3 | `mirror` | `mirror` | 3 | — |
| `macConverseKernel`<br>`:333` | `noncomputable def macConverseKernel (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) : Kernel (Fin M₁ × Fin M₂) (Fin n → β)`<br>本体 `Kernel.ofFunOfCountable (fun m ↦ Measure.pi (fun i ↦ W (c.encoder₁ m.1 i, c.encoder₂ m.2 i)))` | 6 | `bcConverseKernel : Kernel (Fin M₁ × Fin M₂) (Fin n → β₁ × β₂)` | `mirror` | 6 | **BC の方が簡単** (encoder が 1 本)。`c.blockOutputLaw W m` (`Basic.lean:56`) が既に `Measure.pi (fun i ↦ W (c.encoder m i))` なので定義が一致 |
| `macConverseKernel_isMarkovKernel`<br>`:339` | `instance … (c) (W) [IsMarkovKernel W] : IsMarkovKernel (macConverseKernel c W)` | 7 | `mirror` | `mirror` | 7 | — |
| `macConverseAmbient`<br>`:348` | `noncomputable def macConverseAmbient (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) : Measure ((Fin M₁ × Fin M₂) × (Fin n → β))`<br>本体 `(macConverseInput M₁ M₂) ⊗ₘ (macConverseKernel c W)` | 5 | `bcConverseAmbient : Measure ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂))` | `mirror` | 5 | **出力空間が `Fin n → β₁ × β₂` (対の列) になるのが唯一の差**。この形にすることが表 2 の結合 Markov を導く鍵 |
| `macConverseAmbient_isProbabilityMeasure`<br>`:353` | `instance … [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] : IsProbabilityMeasure (macConverseAmbient c W)` | 5 | `mirror` | `mirror` | 5 | — |
| `macConverseMsg₁` / `Msg₂`<br>`:360` / `:363` | `def macConverseMsg₁ : ((Fin M₁ × Fin M₂) × (Fin n → β)) → Fin M₁ := fun ω ↦ ω.1.1` | 2+2 | `mirror` | `mirror` | 4 | — |
| `macConverseYs`<br>`:366` | `def macConverseYs : Fin n → ((Fin M₁ × Fin M₂) × (Fin n → β)) → β := fun i ω ↦ ω.2 i` | 2 | `bcConverseYs` (対) / `bcConverseY₁s` (`(ω.2 i).1`) / `bcConverseY₂s` (`(ω.2 i).2`) | `mirror` | 6 | 1 本 → 3 本 |
| `measurable_macConverseMsg₁/₂/Ys`<br>`:370`/`:376`/`:382` | `lemma measurable_macConverseMsg₁ : Measurable (macConverseMsg₁ (M₁ := M₁) (M₂ := M₂) (n := n) (β := β))` 他 | 6+6+4 | 5 本 (Msg 2 + Y 3) | `mirror` | 26 | — |
| `macConverseInput_map_fst` / `_map_snd`<br>`:386` / `:392` | `lemma macConverseInput_map_fst [NeZero M₁] [NeZero M₂] : (macConverseInput M₁ M₂).map Prod.fst = (Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ • Measure.count` | 6+6 | `mirror` | `mirror` | 12 | — |
| `macConverseInput_eq`<br>`:398` | `lemma macConverseInput_eq : macConverseInput M₁ M₂ = (Fintype.card (Fin M₁ × Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count` | 16 | — | `absent` | 0 | 合同メッセージ対の一様性は MAC の**合同復号器**のための資産。BC は受信機ごとに復号器が分かれるので不要 |
| `macConverse_msgPair_eq_fst`<br>`:416` | `lemma macConverse_msgPair_eq_fst : (fun ω : (Fin M₁ × Fin M₂) × (Fin n → β) ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) = Prod.fst` | 5 | `mirror` | `mirror` | 5 | 独立性の証明で使う |
| `macConverseMsg₁_uniform` / `₂_uniform`<br>`:421` / `:433` | `lemma macConverseMsg₁_uniform (c) (W) [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] : (macConverseAmbient c W).map macConverseMsg₁ = (Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ • Measure.count` | 12+12 | `bc_uv_converse` の `hW₁_uniform` / `hW₂_uniform` を供給 | `mirror` | 24 | — |
| `macConverseMsg₁₂_uniform`<br>`:445` | `lemma … : (macConverseAmbient c W).map (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) = (Fintype.card (Fin M₁ × Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count` | 10 | — | `absent` | 0 | 同上 (合同復号器用) |
| `macConverseCodeKernel` + instance<br>`:457` / `:461` | `noncomputable def macConverseCodeKernel (W : MACChannel α₁ α₂ β) : Kernel ((Fin n → α₁) × (Fin n → α₂)) (Fin n → β)` | 4+6 | `bcConverseCodeKernel : Kernel (Fin n → α) (Fin n → β₁ × β₂)` | `mirror` | 10 | BC は符号語が 1 本なので**より簡単** |
| `isMarkovChain_of_compProd_encoder`<br>`:473` | `private lemma isMarkovChain_of_compProd_encoder {M Z Y : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Z] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] (ν : Measure M) [IsProbabilityMeasure ν] (g : M → Z) (hg : Measurable g) (κ : Kernel M Y) [IsMarkovKernel κ] (Wcode : Kernel Z Y) [IsMarkovKernel Wcode] (hκ : ∀ m : M, κ m = Wcode (g m)) : IsMarkovChain (ν ⊗ₘ κ) (Prod.fst : M × Y → M) (fun ω : M × Y ↦ g ω.1) (Prod.snd : M × Y → Y)` | 94 | そのまま | **`reuse`** (要 de-privatize) | 0 | **MAC 固有の要素が署名にも本体にも一切無い**。`g m := (m.2, c.encoder m)` と取れば BC の `hmarkov₁` の conditioner `(W₂, Xⁿ)` がそのまま出る |
| `lintegral_pi_reRandomize`<br>`:572` | `private lemma lintegral_pi_reRandomize {γ : Type*} [MeasurableSpace γ] {k : ℕ} (ζ : Fin k → Measure γ) [∀ j, IsProbabilityMeasure (ζ j)] (i : Fin k) (F : (Fin k → γ) → ℝ≥0∞) (hF : Measurable F) : ∫⁻ y, F y ∂(Measure.pi ζ) = ∫⁻ y, (∫⁻ b, F (Function.update y i b) ∂(ζ i)) ∂(Measure.pi ζ)` | 19 | そのまま | **`reuse`** (要 de-privatize) | 0 | 汎用の `Measure.pi` 補題 |
| `lintegral_pi_eval`<br>`:593` | `private lemma lintegral_pi_eval {γ : Type*} [MeasurableSpace γ] {k : ℕ} (ζ : Fin k → Measure γ) [∀ j, IsProbabilityMeasure (ζ j)] (i : Fin k) (g : γ → ℝ≥0∞) (hg : Measurable g) : ∫⁻ y, g (y i) ∂(Measure.pi ζ) = ∫⁻ b, g b ∂(ζ i)` | 8 | そのまま | **`reuse`** (要 de-privatize) | 0 | 同上 |
| `isMemorylessChannel_of_compProd_pi`<br>`:606` | `private lemma isMemorylessChannel_of_compProd_pi {M A B : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M] [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B] {k : ℕ} (ν : Measure M) [IsProbabilityMeasure ν] (x : M → Fin k → A) (hx : Measurable x) (W : Kernel A B) [IsMarkovKernel W] (κ : Kernel M (Fin k → B)) [IsMarkovKernel κ] (hκ : ∀ m, κ m = Measure.pi (fun j ↦ W (x m j))) : IsMemorylessChannel (ν ⊗ₘ κ) (fun i ω ↦ x ω.1 i) (fun i ω ↦ ω.2 i)` | 118 | **一般化して再利用** | **`restructure`** | 25 (一般化) | **4b の最大の技術核**。conditioner にメッセージ成分を足す一般化が要る。表 2 §結論を参照 |
| `macConverse_memorylessChannel`<br>`:728` | `lemma macConverse_memorylessChannel (c) (W) [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] : IsMemorylessChannel (macConverseAmbient c W) (fun i ω ↦ (c.encoder₁ (macConverseMsg₁ ω) i, c.encoder₂ (macConverseMsg₂ ω) i)) macConverseYs` | 9 | `h_memo₁` / `h_memo₂` の供給 | `restructure` | 60 | 対出力 `(Y₁ᵢ,Y₂ᵢ)` から片方の座標へ落とす層 (swap + `isMarkovChain_map_left` + swap ×2) |
| `macConverse_mutualInfo_eq_zero`<br>`:741` | `lemma … : mutualInfo (macConverseAmbient c W) macConverseMsg₁ macConverseMsg₂ = 0` | 13 | `h_indep` の供給 | `mirror` | 13 | 完全同型 |
| `macConverse_isMarkovChain`<br>`:756` | `lemma macConverse_isMarkovChain (c) (W) [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] : IsMarkovChain (macConverseAmbient c W) (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) (fun ω ↦ ((fun j ↦ c.encoder₁ (macConverseMsg₁ ω) j), (fun j ↦ c.encoder₂ (macConverseMsg₂ ω) j))) (fun ω j ↦ macConverseYs j ω)` | 14 | `hmarkov₁` / `hmarkov₂` の供給 | `mirror` | 50 | 2 本必要 + 出力射影のため swap/map_left/swap。conditioner を `(W₂, Xⁿ)` にするのは `g` の取り方だけ |
| `mac_converse_from_code`<br>`:777` | `theorem mac_converse_from_code [NeZero M₁] [NeZero M₂] (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) : InMACCapacityRegion (Real.log (M₁ : ℝ)) (Real.log (M₂ : ℝ)) (…3 スロット…)` | 44 | `bc_uv_converse_from_code : InBCOuterRegionUV (log M₁) (log M₂) (…4 スロット…)` | `mirror` | 60 | スロットが 3 → 4 |

### 1-C. RateExtract (`Bridge.lean:823`–`:969`)

| MAC decl (`file:line`) | 逐語署名 (型クラス前提込み) | 行数 | BC 対応物 | 区分 | 新規行数 | 難所 |
|---|---|---|---|---|---|---|
| `le_log_of_ceil_exp_le`<br>`Bridge.lean:840` | `lemma le_log_of_ceil_exp_le {x : ℝ} {M : ℕ} (hM : Nat.ceil (Real.exp x) ≤ M) : x ≤ Real.log (M : ℝ)`<br>**型クラス前提ゼロ / public** | 14 | そのまま | **`reuse`** | 0 (移設) / 14 (複製) | 家系跨ぎ import を避けるなら `Shannon/` 直下へ移設が最善 |
| `mac_converse_rate_extract`<br>`Bridge.lean:854` | `lemma mac_converse_rate_extract [NeZero M₁] [NeZero M₂] (c) (W) [IsMarkovKernel W] (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) {R₁ R₂ : ℝ} (hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁) (hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂) : InMACCapacityRegion ((n : ℝ) * R₁) ((n : ℝ) * R₂) (…3 スロット…)` | 49 | `bc_uv_rate_extract` | `mirror` | 55 | スロット 4 本 |
| `mac_converse_ambient_errorProb_joint_eq`<br>`Bridge.lean:903` | `lemma mac_converse_ambient_errorProb_joint_eq (c) (W) [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] : MeasureFano.errorProb (macConverseAmbient c W) (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) (fun ω i ↦ macConverseYs i ω) c.decoder = (c.averageErrorProb W).toReal` | 35 | 受信機ごとに 2 本 (`= (c.averageErrorProb₁ W).toReal` / `₂`) | `mirror` | 70 | `errorProb μ Xs Yo dec = μ.real {ω \| Xs ω ≠ dec (Yo ω)}` (`Fano/Measure.lean:89`) と `averageErrorProb₁` (`BroadcastChannel/Basic.lean:87`) の突き合わせ。BC は `blockOutputLaw` が ambient の kernel と定義的に一致するので MAC と同難度 |
| `mac_converse_ambient_errorProb_user1_le`<br>`Bridge.lean:938` | `lemma … : MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₁ (fun ω ↦ (macConverseMsg₂ ω, fun i ↦ macConverseYs i ω)) (fun p ↦ (c.decoder p.2).1) ≤ MeasureFano.errorProb (macConverseAmbient c W) (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) (fun ω i ↦ macConverseYs i ω) c.decoder` | 16 | — | `absent` | 0 | **MAC 固有**。MAC は合同復号器 1 本なので「合同誤り ≥ ユーザ別誤り」の段が要る。BC は最初から受信機別復号器なのでこの段が消える |
| `mac_converse_ambient_errorProb_user2_le`<br>`Bridge.lean:954` | 上のミラー | 15 | — | `absent` | 0 | 同上 |

### 1-D. PerLetterInfo (`Bridge.lean:971`–`:1237`)

| MAC decl (`file:line`) | 逐語署名 (型クラス前提込み) | 行数 | BC 対応物 | 区分 | 新規行数 | 難所 |
|---|---|---|---|---|---|---|
| `compProd_pi_map_pair_eq`<br>`:992` | `private lemma compProd_pi_map_pair_eq {M A B : Type*} [MeasurableSpace M] [MeasurableSpace A] [MeasurableSpace B] {k : ℕ} (ν : Measure M) [IsProbabilityMeasure ν] (x : M → Fin k → A) (hx : Measurable x) (W : Kernel A B) [IsMarkovKernel W] (κ : Kernel M (Fin k → B)) [IsMarkovKernel κ] (hκ : ∀ m, κ m = Measure.pi (fun j ↦ W (x m j))) (i : Fin k) : (ν ⊗ₘ κ).map (fun ω ↦ (x ω.1 i, ω.2 i)) = (ν.map (fun m ↦ x m i)) ⊗ₘ W` | 32 | `B := β₁ × β₂` で**そのまま** | **`reuse`** (要 de-privatize) | 0 | BC でも `(Xᵢ, (Y₁ᵢ,Y₂ᵢ))` の同時分布が `pᵢ ⊗ₘ W` になる。文字通り同じ主張 |
| `mutualInfo_map_comp`<br>`:1024` | `private lemma mutualInfo_map_comp {Ω Ω' A B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace A] [MeasurableSpace B] (μ : Measure Ω) (T : Ω → Ω') (hT : Measurable T) (f : Ω' → A) (hf : Measurable f) (g : Ω' → B) (hg : Measurable g) : mutualInfo (μ.map T) f g = mutualInfo μ (fun ω ↦ f (T ω)) (fun ω ↦ g (T ω))` | 13 | そのまま | **`reuse`** (要 de-privatize) | 0 | 完全に汎用 |
| `condDistrib_map_comp`<br>`:1037` | `private lemma condDistrib_map_comp {Ω Ω' A C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] [MeasurableSpace C] (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω') (hT : Measurable T) (f : Ω' → A) (hf : Measurable f) (h : Ω' → C) (hh : Measurable h) : condDistrib f h (μ.map T) =ᵐ[(μ.map T).map h] condDistrib (fun ω ↦ f (T ω)) (fun ω ↦ h (T ω)) μ` | 17 | そのまま | **`reuse`** (要 de-privatize) | 0 | 同上 |
| `condMutualInfo_map_comp`<br>`:1054` | `private lemma condMutualInfo_map_comp {Ω Ω' A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B] [MeasurableSpace C] (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω') (hT : Measurable T) (f : Ω' → A) (hf : Measurable f) (g : Ω' → B) (hg : Measurable g) (h : Ω' → C) (hh : Measurable h) : condMutualInfo (μ.map T) f g h = condMutualInfo μ (fun ω ↦ f (T ω)) (fun ω ↦ g (T ω)) (fun ω ↦ h (T ω))` | 34 | そのまま | **`reuse`** (要 de-privatize) | 0 | 同上 |
| `condMutualInfo_map_comp'`<br>`:1088` | 上に `(ρ : Measure Ω') [IsFiniteMeasure ρ] (hρ : ρ = μ.map T)` を足した版 | 21 | そのまま | **`reuse`** (要 de-privatize) | 0 | 同上 |
| `macConverse_map_triple_eq`<br>`:1109` | `lemma macConverse_map_triple_eq (c) (W) [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] (i : Fin n) : (macConverseAmbient c W).map (fun ω ↦ (c.encoder₁ (macConverseMsg₁ ω) i, c.encoder₂ (macConverseMsg₂ ω) i, macConverseYs i ω)) = macJointDistribution ((macConverseAmbient c W).map (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i)) ((macConverseAmbient c W).map (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)) W` | 53 | `(Uᵢ, Vᵢ, Xᵢ, Y₁ᵢ, Y₂ᵢ)` の 5 つ組同定 | `mirror` | 70 | 3 つ組 → 5 つ組。`bcJointDistribution` (`Achievability/Setup.lean:54`, 補助変数 1 本) は形が違うので UV 用に `bcUVJointDistribution : Measure ((U × V) × α × β₁ × β₂)` を新設 |
| `mac_condMI_eq_macInfo₁_at`<br>`:1162` | `lemma mac_condMI_eq_macInfo₁_at (c) (W) [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] (i : Fin n) : (condMutualInfo (macConverseAmbient c W) (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i) (macConverseYs i) (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)).toReal = macInfo₁ (…) (…) W` | 26 | 4 スロットぶんの同定 | `mirror` | 110 (4 本) | 新設する `uvInfo₁ / uvInfo₂ / uvInfoSum₁ / uvInfoSum₂` の定義と揃える必要がある (→ Mathlib-shape-driven) |
| `mac_condMI_eq_macInfo₂_at`<br>`:1188` | 上のミラー | 26 | (上に込み) | `mirror` | — | — |
| `mac_mutualInfo_eq_macInfoBoth_at`<br>`:1214` | `lemma … (i : Fin n) : (mutualInfo (macConverseAmbient c W) (fun ω ↦ (c.encoder₁ (macConverseMsg₁ ω) i, c.encoder₂ (macConverseMsg₂ ω) i)) (macConverseYs i)).toReal = macInfoBoth (…) (…) W` | 23 | (上に込み) | `mirror` | — | — |

### 1-E. MAC には無い BC 固有の新規層 (`Bridge.lean` に対応 decl なし)

| BC で新設 | 内容 | 区分 | 新規行数 | 難所 |
|---|---|---|---|---|
| `uvAuxPad` + `uvAux_pad_mutualInfo_eq` | `uvAux … i` の**型が i に依存する** (`OuterBoundUV.lean:71-73`) ので、固定型 `A := Fin n × ξ × (Fin n → β₁) × (Fin n → β₂)` へ pad する再符号化と、その下での相互情報量の不変性 | **`restructure`** | 40 | `mutualInfo_le_of_postprocess` (`DPI.lean:123`) を**両向き**に当てて等式にする (pad と un-pad が互いに逆写像) |
| `uvAux_pad_condMutualInfo_eq` | 条件付き相互情報量の conditioner スロットについて同じ不変性 | **`restructure`** | 60 | 単調性が使えないので `mutualInfo_chain_rule` (`CondMutualInfo.lean:214`, `I((Z,X);Y) = I(Z;Y) + I(X;Y\|Z)`) で分解 → 2 本の mutualInfo に落とす → `ENNReal.add_right_inj` + `mutualInfo_ne_top` で消去 |

**表 1 集計**: `reuse` 9 本 (238 行を再利用) / `mirror` 33 本 / `restructure` 5 本 / `absent` 6 本。
新規行数合計 (推奨ルート) ≈ **810 行**。

---

## 表 2 — `bc_uv_converse` の仮説 → 導出義務表

`OuterBoundUV.lean:815`–`:843` の署名を逐語転記。ambient は
`μ := bcConverseAmbient c W : Measure ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂))`、
`ξ₁ := Fin M₁`, `ξ₂ := Fin M₂`, `Xs i ω := c.encoder ω.1 i`, `Y₁s i ω := (ω.2 i).1`,
`Y₂s i ω := (ω.2 i).2` を想定。

| 仮説名 | 逐語の型 | MAC 側の対応 (`file:line`) | 構成した μ からの難度 | 備考 |
|---|---|---|---|---|
| (暗黙) `[IsProbabilityMeasure μ]` | — | `macConverseAmbient_isProbabilityMeasure` `Bridge.lean:353` | easy | `⊗ₘ` の instance で自動 |
| `hW₁` / `hW₂` | `Measurable W₁` / `Measurable W₂` | `measurable_macConverseMsg₁/₂` `Bridge.lean:370` / `:376` | easy | `measurable_fst.fst` / `.snd` |
| `hXs` | `∀ (j : Fin n), Measurable (Xs j)` | (MAC は `measurable_of_countable _` で直接) | easy | `(measurable_pi_apply j).comp ((measurable_of_countable c.encoder).comp measurable_fst)` |
| `hY₁s` / `hY₂s` | `∀ (j : Fin n), Measurable (Y₁s j)` / `(Y₂s j)` | `measurable_macConverseYs` `Bridge.lean:382` | easy | `measurable_fst/snd ∘ (measurable_pi_apply j) ∘ measurable_snd` |
| `hW₁_uniform` | `μ.map W₁ = (Fintype.card ξ₁ : ℝ≥0∞)⁻¹ • Measure.count` | `macConverseMsg₁_uniform` `Bridge.lean:421` | easy | `Measure.fst_compProd` (`Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:171`) + `Measure.map_fst_prod` |
| `hW₂_uniform` | `μ.map W₂ = (Fintype.card ξ₂ : ℝ≥0∞)⁻¹ • Measure.count` | `macConverseMsg₂_uniform` `Bridge.lean:433` | easy | 同上 |
| `hcard₁` / `hcard₂` | `2 ≤ Fintype.card ξ₁` / `2 ≤ Fintype.card ξ₂` | `mac_converse_from_code` の `hcard₁ : 2 ≤ M₁` `Bridge.lean:777` | easy | `Fintype.card (Fin M₁) = M₁` で `2 ≤ M₁` に還元。**退化レートで壊れる箇所** (§難所 3) |
| `h_indep` | `mutualInfo μ W₁ W₂ = 0` | `macConverse_mutualInfo_eq_zero` `Bridge.lean:741` | easy | 入力が積測度 `macConverseInput` 相当なので `mutualInfo_eq_zero_iff_indep` 一発 |
| `h_memo₁` | `∀ i : Fin n, IsMarkovChain μ (fun ω ↦ (W₂ ω, ((fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω), ((fun (j : {j : Fin n // j ≠ i}) ↦ Y₁s j.val ω), (fun (j : {j : Fin n // j ≠ i}) ↦ Y₂s j.val ω))))) (Xs i) (Y₁s i)` | `macConverse_memorylessChannel` `Bridge.lean:728` (← `isMemorylessChannel_of_compProd_pi` `:606`) | **medium** | (i) conditioner の `W₂` 成分 (ii) 出力を対 `(Y₁ᵢ,Y₂ᵢ)` から第 1 座標へ落とす、の 2 つの差。§結論を参照 |
| `h_memo₂` | 上の `W₂ → W₁`、出力 `Y₁s i → Y₂s i` 版 | 同上 | **medium** | 同上 (第 2 座標へ落とす) |
| `hmarkov₁` | `IsMarkovChain μ (fun ω ↦ (W₂ ω, W₁ ω)) (fun ω ↦ (W₂ ω, fun j ↦ Xs j ω)) (fun ω j ↦ Y₁s j ω)` | `macConverse_isMarkovChain` `Bridge.lean:756` (← `isMarkovChain_of_compProd_encoder` `:473`) | **medium** | `g m := (m.2, c.encoder m)` と取れば conditioner がそのまま出る。始点 `(W₂,W₁)` は `Prod.swap` で `isMarkovChain_map_left`、終点 `Y₁ⁿ` は swap→map_left→swap |
| `hmarkov₂` | 上の `W₁ ↔ W₂` / `Y₁s → Y₂s` 版 | 同上 | **medium** | 同上 |

### 結論 — 結合 Markov について既定 (b) は実行可能

plan 判断ログ 3 の申し送り「座標ごと条件付き独立 ≠ 結合の条件付き独立」は正しく、
`h_memo₁` / `h_memo₂` は**同一文字の対 `(Y₁ᵢ, Y₂ᵢ)` を決して分離しない**
(`OuterBoundUV.lean:804-806` の docstring が明示)。集合定義の段では
`(Uᵢ,Vᵢ) → Xᵢ → (Y₁ᵢ,Y₂ᵢ)` の**結合形**が要る。

**MAC 側で結合形に相当するものがどう扱われているか (実測)**:
`isMemorylessChannel_of_compProd_pi` (`Bridge.lean:606`) は
`hκ : ∀ m, κ m = Measure.pi (fun j ↦ W (x m j))` から
`IsMarkovChain (ν ⊗ₘ κ) (X^{≠i}, Y^{≠i}) (Xᵢ) (Yᵢ)` を出す。ここで `Yᵢ = ω.2 i` は
**チャネル `W` の出力そのもの (対でも構わない)** であり、MAC では `B = β` だったに過ぎない。
本体の要は `:713`–`:723` の 3 行で、
`Function.update y i b` に対して conditioner が不変・出力がちょうど `b` になることしか使っていない。

したがって **(b) が実行可能である根拠は 3 点、すべて実ファイル照合済**:

1. **BC の符号は最初から対出力の直積で定義されている**。
   `BroadcastCode.blockOutputLaw c W m = Measure.pi (fun i ↦ W (c.encoder m i))`
   (`BroadcastChannel/Basic.lean:56-59`, `W : Kernel α (β₁ × β₂)`)。
   ambient を `bcConverseInput ⊗ₘ Kernel.ofFunOfCountable (fun m ↦ c.blockOutputLaw W m)` と組めば
   `hκ` が `rfl` で通り、`B := β₁ × β₂` として `isMemorylessChannel_of_compProd_pi` の
   仮説がそのまま満たされる → **結合形の Markov 連鎖が構成から直接出る**。
2. **conditioner にメッセージ成分を足す一般化はほぼ無コスト**。現行の `Full`
   (`Bridge.lean:624-625`) は `((fun j ↦ x ω.1 j.val), (fun j ↦ ω.2 j.val))`。
   証明が `Full` について使うのは可測性と「座標 `i` の update に対する不変性」だけ
   (`:721`–`:722`)。`Full ω := (g ω.1, X^{≠i}, Y^{≠i})` に差し替えても
   `g ω.1` は `y` に触らないので不変性がそのまま成立する。**+25 行程度の一般化**。
3. **対出力から片方の座標へ落とすのは既存資産だけで済む**。
   `isMarkovChain_swap` (`CondEntropyMemoryless.lean:330`,
   `(μ) (Xs) (Zc) (Yo) → IsMarkovChain μ Yo Zc Xs`, 両端が `[StandardBorelSpace] [Nonempty]`) と
   `isMarkovChain_map_left` (`CondMutualInfo.lean:570`,
   `{f : X → X'} (hf : Measurable f) (hmarkov : IsMarkovChain μ Xs Zc Yo) : IsMarkovChain μ (fun ω ↦ f (Xs ω)) Zc Yo`)
   の swap → map_left → swap で**出力側の後処理**が作れる。どちらも `@[entry_point]` の public。

→ **仮説を結合形に強める案 (a) は不要**。`OuterBoundUV.lean` の署名は 1 文字も触らない。
plan「(a) を選んだ場合の波及 6 decl」は発動しない。

**注意 (under-estimation ガード)**: 上の 1. は「ambient を `Fin n → β₁ × β₂` 上に組む」ことに
依存する。もし ambient を `(Fin n → β₁) × (Fin n → β₂)` (出力を 2 本の列に分離) で組むと
`Measure.pi` の構造が壊れ、結合形が出なくなる。**定義の形が結論の可否を決める**ので、
`bcConverseAmbient` の出力空間は `Fin n → β₁ × β₂` で固定すること (Mathlib-shape-driven)。

---

## 表 3 — 単一文字還元 (凸化) の選択肢

plan「設計上の未決事項 2」。**推奨は案 A (時間共有変数を補助変数に吸収)**。

| 観点 | **案 A: 時間共有変数を補助変数に吸収 (推奨)** | 案 B: MAC 式に凸包へ逃がす |
|---|---|---|
| `bcOuterRegionUV` の定義 | `closure (⋃ k : ℕ, ⋃ (p : Measure (Fin k × Fin k × α)) (_ : IsProbabilityMeasure p), {r \| InBCOuterRegionUV r.1 r.2 (uvInfo₁ p W) (uvInfo₂ p W) (uvInfoSum₂ p W) (uvInfoSum₁ p W)})` — **union 1 本、凸包演算なし** | `closedConvexHull ℝ (⋃ k, ⋃ p …, uvPentagon p W)` — MAC `Assembly.lean:817` と同型 |
| 型量化の回避 | 補助変数対 `(U,V)` を `Fin k × Fin k` に固定し `k` について union (plan Phase 2 の方針と一致) | 同じ |
| 幾何補題 | 不要 | **4 制約版の `mac_avgPentagon_mem_convexHull` が要る** (2 本の和制約 `J₁`, `J₂`)。`c i := min (J₁ i) (J₂ i)` で 3 制約に潰せるが、下の well-formedness が要る |
| well-formedness | 不要 | **`I₁ᵢ ≤ min(J₁ᵢ, J₂ᵢ)` と `I₂ᵢ ≤ min(J₁ᵢ,J₂ᵢ)` が要る。`I₁ᵢ ≤ J₂ᵢ` は一般 BC で成立しない見込み** (下記) |
| 第一象限問題 | **無害**。4 スロットはすべて非負 (`.toReal` of `ℝ≥0∞` + `binEntropy ≥ 0` + `Pe·log(card−1) ≥ 0`) なので、領域は下方閉で第三象限を含む → plan 判断ログ 1「外界に第一象限制約を入れない」を**満たす** | **満たせない**。凸包はつねに第一象限内なので `bcCapacityRegion ⊆ …` が偽になり、MAC と同じく `bcCapacityRegion W ∩ {0 ≤ p.1 ∧ 0 ≤ p.2} ⊆ …` に弱めざるを得ない (`mac_timesharing_capacity_region` `Assembly.lean:908` が実際にそうしている)。**plan の到達目標の形が変わる** |
| 型統一 (`uvAux` の i 依存型) | 必要 (表 1-E、~100 行) | 各文字 `i` が別々の `k` で union に入るだけなので**不要**。ここは案 B が有利 |
| 行数見積り | 幾何 0 + 型統一 100 + 吸収層 180 = **280** | 幾何 170 + well-formedness 120 (成立しない場合 `sorry`) + 型統一 0 + 凸包配線 200 = **490** |
| リスク | 型統一補題が想定より重い (mutualInfo は両向き DPI で確実、conditioner は chain rule 経由) | **well-formedness が偽なら詰む** |

### 案 B のリスク根拠 (`I₁ᵢ ≤ J₂ᵢ` が一般に出ない)

`mac_avgPentagon_mem_convexHull` (`Bridge.lean:94`) は `hac : a i ≤ c i` / `hbc : b i ≤ c i` /
`hsub : c i ≤ a i + b i` を必須で要求し、MAC ではこれを
`mac_macInfo₁_le_macInfoBoth` (`:231`) = chain rule + 相互情報量の非負性で供給していた。

これらの仮説が**飾りではない**ことは反例で確認できる: `n = 2`, `a = (2,0)`, `b = (2,2)`,
`c = (0,2)` (→ `hac` が `i=0` で破れる) を取ると `avg a = 1`, `avg b = 2`, `avg c = 1`、
`P₀ = {(0,0)}`, `P₁ = {0} × [0,2]` で凸包は線分 `{0} × [0,2]`。
`(R₁,R₂) = (1,0)` は 3 つの平均制約をすべて満たすが凸包に**入らない**。

UV 側の対応は `a i = I(Vᵢ;Y₁ᵢ)`, `b i = I(Uᵢ;Y₂ᵢ)`,
`c i = min(I(Uᵢ;Y₂ᵢ)+I(Xᵢ;Y₁ᵢ|Uᵢ), I(Vᵢ;Y₁ᵢ)+I(Xᵢ;Y₂ᵢ|Vᵢ))`。
`a i ≤ J₁ᵢ` と `b i ≤ J₂ᵢ` は自明 (条件付き相互情報量の非負性) だが、
`a i ≤ J₂ᵢ` は `Uᵢ → Xᵢ → Y₁ᵢ` の chain rule で
`J₂ᵢ = I(Xᵢ;Y₁ᵢ) − I(Uᵢ;Y₁ᵢ) + I(Uᵢ;Y₂ᵢ)` と書け、`a i ≤ I(Xᵢ;Y₁ᵢ)` (DPI) と合わせても
**`I(Uᵢ;Y₁ᵢ) ≤ I(Uᵢ;Y₂ᵢ)` が要る** — これは less noisy / degraded の仮定そのもので、
一般 BC では偽。**degradedness 前提なしという Phase 4a の成果を捨てることになる**ので、
案 B は採るべきでない。

---

## §行数と難所のまとめ

### Phase 4b 全体の行数見積り (推奨ルート = 案 A)

| 層 | 内訳 | 行数 |
|---|---|---|
| **L1 共有化 (de-privatize + 移設)** | `isMarkovChain_of_compProd_encoder` / `lintegral_pi_reRandomize` / `lintegral_pi_eval` / `isMemorylessChannel_of_compProd_pi` / `compProd_pi_map_pair_eq` / `mutualInfo_map_comp` / `condDistrib_map_comp` / `condMutualInfo_map_comp` / `condMutualInfo_map_comp'` / `le_log_of_ceil_exp_le` を `InformationTheory/Shannon/ChannelCoding/CodeToAmbient.lean` (新規) へ移設 | +60 (移設に伴う module doc / import 調整。**238 行は書かずに済む**) |
| **L2 memoryless の一般化** | conditioner にメッセージ成分を許す `isMemorylessChannel_of_compProd_pi'` | +25 |
| **L3 BC ambient 構成** | input / kernel / ambient / 射影 / 可測性 / 一様性 / 独立性 | +130 |
| **L4 構造前提の導出** | `h_memo₁/₂` (60) + `hmarkov₁/₂` (50) + `h_indep` (13) | +123 |
| **L5 符号レベル converse** | `bc_uv_converse_from_code` (60) + 誤り確率同定 ×2 (70) + `bc_uv_rate_extract` (55) | +185 |
| **L6 per-letter 同定** | `bcUVJointDistribution` + 5 つ組 map (70) + `uvInfo*` 4 本の定義 (40) + 同定 4 本 (110) | +220 |
| **L7 補助変数の型統一** | `uvAuxPad` + mutualInfo 不変 (40) + condMutualInfo 不変 (60) | +100 |
| **L8 集合化 + 吸収** | `bcOuterRegionUV` + 閉性 (70) + 時間共有吸収 (180) | +250 |
| **L9 極限と組み立て** | Fano slack → 0 (85) + 退化レート被覆 (150) + `bc_capacity_subset_uv` (40) | +275 |
| | **合計** | **≈ 1370 行** |

参考: MAC 実績は `Bridge.lean` 1238 + `Assembly.lean` 953 = **2191 行**。
6 割強に収まる主因は L1 の 238 行再利用 + 凸幾何 (172 行) の回避 + BC の受信機別復号器による
誤り確率の段の削減。逆に増える要因は情報スロットが 3 → 4 と L7 の新規層。

**ファイル構成の推奨**: `InformationTheory/Shannon/BroadcastChannel/OuterBoundUV/Bridge.lean`
(L2–L7、≈ 800 行) と `.../OuterBoundUV/Assembly.lean` (L8–L9、≈ 530 行) に分割。
`docs/rules/` の 1500 行ガイドに収まる。

### 難所ランキング (上位 3)

1. **L2+L4 — memoryless の一般化と結合 Markov の取り出し** (~85 行)。
   4b の成否を決める箇所だが、**表 2 §結論のとおり実行可能と判定**。
   `isMemorylessChannel_of_compProd_pi` の本体で `Full` について使っているのが
   可測性 + update 不変性だけであること (`Bridge.lean:713`–`:723`) が根拠。
   失敗するとすれば `bcConverseAmbient` の出力空間を `(Fin n → β₁) × (Fin n → β₂)` に
   取ってしまった場合なので、**定義を `Fin n → β₁ × β₂` で固定**することが唯一の防御。
2. **L7 — 補助変数の型統一** (~100 行、**plan 未記載**)。
   `uvAux W Y₁s Y₂s i : Ω → ξ × ((Fin i.val → β₁) × ({j : Fin n // i.val < j.val} → β₂))`
   の型が `i` に依存するため、単一文字分布の集合を作るには共通アルファベットへの
   載せ替えが要る。MAC には対応物ゼロ。攻略路は確定済:
   mutualInfo は `mutualInfo_le_of_postprocess` (`DPI.lean:123`) の両向き適用で等式、
   conditioner は `mutualInfo_chain_rule` (`CondMutualInfo.lean:214`) で 2 本の mutualInfo に
   分解してから `ENNReal.add_right_inj` で消去。
3. **L9 — 退化レートの被覆** (~150 行、**plan 未記載**)。
   `bc_uv_converse` は `hcard₁ : 2 ≤ Fintype.card ξ₁` を要求するが、`R₁ ≤ 0` では
   `BCAchievable` が `M₁ = 1` の符号しか保証しない。MAC はここに
   `mac_converse_from_code_bound₁/₂` + `mac_converse_shrunk_point_mem_axis1/2` +
   `mac_timesharing_converse_axis1/2` (`Assembly.lean:397`–`:817`) で**約 450 行**を費やしている。
   案 A では領域が下方閉で第三象限を含むため、非正レートは単調性で潰せる見込みで
   150 行程度に収まるはずだが、**plan の checklist には 1 行も現れていない**ので明示しておく。

### step の推奨分割 (1 dispatch = 1 step)

| step | 成果物 (decl 名) | 依存 | 行数 | 備考 |
|---|---|---|---|---|
| **4b-S1** | `InformationTheory/Shannon/ChannelCoding/CodeToAmbient.lean` 新設。`isMarkovChain_of_compProd_encoder` / `lintegral_pi_reRandomize` / `lintegral_pi_eval` / `isMemorylessChannel_of_compProd_pi` / `compProd_pi_map_pair_eq` / `mutualInfo_map_comp` / `condDistrib_map_comp` / `condMutualInfo_map_comp` / `condMutualInfo_map_comp'` / `le_log_of_ceil_exp_le` を移設し public 化。`Bridge.lean` はそれを import して再エクスポート | — | 移設 300 / 新規 60 | **MAC 側の既存証明を触るので `scripts/dep_consumers.sh` を先に回すこと**。`Bridge.lean` / `Assembly.lean` / `Converse.lean` / `TimeSharingConverse.lean` の 4 ファイルが consumer 候補 |
| **4b-S2** | `bcConverseInput` / `bcConverseKernel` / `bcConverseAmbient` / `bcConverseMsg₁/₂` / `bcConverseYs` / `bcConverseY₁s` / `bcConverseY₂s` + 可測性 5 本 + instance 4 本 + `bcConverseMsg₁/₂_uniform` + `bcConverse_mutualInfo_eq_zero` | S1 | 130 | `bcConverseAmbient` の出力空間は `Fin n → β₁ × β₂` で固定 (難所 1) |
| **4b-S3** | `isMemorylessChannel_of_compProd_pi'` (一般化) + `bcConverse_memoryless₁` / `_memoryless₂` (= `h_memo₁/₂`) + `bcConverse_isMarkovChain₁` / `₂` (= `hmarkov₁/₂`) | S2 | 148 | **難所 1**。swap/map_left/swap の組み方をここで確立 |
| **4b-S4** | `bc_uv_converse_from_code` + `bcConverse_errorProb₁_eq` / `₂_eq` + `bc_uv_rate_extract` | S3 | 185 | `bc_uv_converse` をここで初めて呼ぶ。`InBCOuterRegionUV (log M₁) (log M₂) …` が出る |
| **4b-S5** | `uvAuxPad` + `uvAux_pad_mutualInfo_eq` + `uvAux_pad_condMutualInfo_eq` | S1 (S2–S4 と独立に着手可) | 100 | **難所 2**。`OuterBoundUV.lean` の隣に置くのが自然 |
| **4b-S6** | `bcUVJointDistribution` + `uvInfo₁` / `uvInfo₂` / `uvInfoSum₁` / `uvInfoSum₂` + 5 つ組 map + 同定 4 本 | S4, S5 | 220 | 定義は `bc_uv_converse` の結論形に合わせて決める (Mathlib-shape-driven) |
| **4b-S7** | `bcOuterRegionUV` + `bcOuterRegionUV_isClosed` + 時間共有吸収 (`bc_uv_shrunk_point_mem` 相当) | S6 | 250 | 案 A。第一象限制約は入れない |
| **4b-S8** | Fano slack → 0 の極限 + 退化レート被覆 + `bc_capacity_subset_uv` | S7 | 275 | **難所 3**。ここだけ 2 dispatch に割れる可能性あり |

依存順序: `S1 → S2 → S3 → S4 → S6 → S7 → S8`、`S5` は `S1` の直後に並行着手可。
S1 のみ **MAC 側の既存ファイルを編集する** ので、honesty ゲートより先に
`lake build InformationTheory.Shannon.MultipleAccess.TimeSharingConverse` での回帰確認が要る。

---

## Mathlib 側 API 在庫 (BC 固有で新たに要るもの)

MAC が使った Mathlib 資産はすべて BC でもそのまま効く。追加で要るものだけ列挙する。

| 概念 | Mathlib API | file:line | 状態 | 4b での扱い |
|---|---|---|---|---|
| ブロック出力の直積 | `protected irreducible_def pi : Measure (∀ i, α i)` | `Mathlib/MeasureTheory/Constructions/Pi.lean:212` | ✅ 既存 | `bcConverseKernel` の本体 (`β₁ × β₂` 値) |
| 測度とカーネルの合成 | `def compProd (μ : Measure α) (κ : Kernel α β) : Measure (α × β)` (記法 `⊗ₘ`) | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:43` / 記法 `:47` | ✅ 既存 | ambient の骨格 |
| 第一周辺 | `@[simp] lemma fst_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsMarkovKernel κ] : (μ ⊗ₘ κ).fst = μ` | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:171` | ✅ 既存 | メッセージ一様性 |
| 可算型のカーネル構成 | `def ofFunOfCountable [MeasurableSpace α] {_ : MeasurableSpace β} [Countable α]` | `Mathlib/Probability/Kernel/Basic.lean:237` | ✅ 既存 | `bcConverseKernel` |
| 有限型の可測性 | `theorem measurable_of_countable [Countable α] [MeasurableSingletonClass α] (f : α → β) : Measurable f` | `Mathlib/MeasureTheory/MeasurableSpace/Basic.lean:276` | ✅ 既存 | encoder / decoder の可測性、`Equiv → MeasurableEquiv` の 2 行構成 |
| 条件付き分布の一意性 | `lemma condDistrib_ae_eq_of_measure_eq_compProd (X : α → β) (hY : AEMeasurable Y μ) {κ : Kernel β Ω} [IsFiniteKernel κ] (hκ : μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ κ) : condDistrib Y X μ =ᵐ[μ.map X] κ` | `Mathlib/Probability/Kernel/CondDistrib.lean:163` | ✅ 既存 | memoryless 一般化の Step 2 (MAC と同じ) |
| 分解等式 | `lemma compProd_map_condDistrib (hY : AEMeasurable Y μ) : (μ.map X) ⊗ₘ condDistrib Y X μ = μ.map fun a ↦ (X a, Y a)` | `Mathlib/Probability/Kernel/CondDistrib.lean:82` | ✅ 既存 | 同 Step 3 |
| 閉凸包 | `def closedConvexHull : ClosureOperator (Set E)` / `theorem isClosed_closedConvexHull` / `theorem closedConvexHull_eq_closure_convexHull` | `Mathlib/Analysis/Convex/Topology.lean:294` / `:300` / `:332` | ✅ 既存 | **案 B を採った場合のみ**。案 A では不使用 |

**自作が必要な Mathlib レベルの穴はゼロ**。`@residual(wall:…)` 候補も現時点でゼロ
(loogle 0 hit を根拠にする wall 宣言をこの在庫では行わない)。
4b で自作するものはすべて「既存 Mathlib 資産の配線 (plumbing)」または
「InformationTheory 内の既存補題の一般化」に分類される。

**型クラス前提の漏れチェック**: `bc_uv_converse` は 5 つのアルファベット
`α / ξ₁ / ξ₂ / β₁ / β₂` すべてに
`[Fintype _] [MeasurableSpace _] [MeasurableSingletonClass _] [StandardBorelSpace _] [Nonempty _]`
を要求する (`#check` 実測)。wrapper では `ξ₁ = Fin M₁` / `ξ₂ = Fin M₂` を代入するので
`[NeZero M₁] [NeZero M₂]` から `Nonempty` が、`Countable + MeasurableSingletonClass` の
instance 連鎖から `StandardBorelSpace` が自動導出される (MAC `mac_converse_from_code` が
同じ代入で通っている実績あり)。**ambient `Ω` 側に `StandardBorelSpace` は不要**
(`IsMarkovChain` が γ 形で定義されており、docstring `CondMutualInfo.lean:79-81` が
「`[StandardBorelSpace Ω]` を要求しないために γ 形を選んだ」と明記)。

---

## 撤退ラインとの距離

| slug | 発動条件 | 判定 |
|---|---|---|
| **L-BCO4** | Phase 4b の符号→ambient 橋または単一文字還元が閉じない | **不発動見込み**。橋は MAC の抽象補題 4 本 (`isMarkovChain_of_compProd_encoder` / `isMemorylessChannel_of_compProd_pi` / `lintegral_pi_*`) が BC 固有要素ゼロで再利用でき、結合 Markov も構成側から出る (表 2 §結論)。単一文字還元は案 A で凸幾何を回避できる |
| **L-BCO2** | Phase 2 の型量化 union が universe 問題で詰む | **4b でも同じ論点が出る**。案 A / 案 B のどちらでも `bcOuterRegionUV` は補助変数の型について union を取る。`Fin k` 固定 + `k` について union という Phase 2 の回避策をそのまま採るので、4b が新たに L-BCO2 を発動させることはない |
| **L-BCO3** | Phase 5 の等号が Phase 4 の外界の形と噛み合わない | 4b の範囲外。ただし案 B を採ると領域が第一象限に閉じ込められ、`martonRegion` (第一象限に閉じている、`Operational.lean:123`) との比較はむしろ易しくなる。案 A では両者の象限の扱いが違うので Phase 5 で交差を取る一手間が増える (影響は軽微) |
| **L-BCO1** | (Phase 4a で不発動確定) | 変化なし |

**新規の撤退ライン候補 (提案)**: 難所 2 / 難所 3 は plan に載っていないので、
以下を Phase 4b の撤退ラインに追加することを提案する (最終判断は plan 側)。

- **L-BCO5 (提案)**: 補助変数の型統一 (S5) が `mutualInfo_chain_rule` 経由でも閉じない場合
  → `bcOuterRegionUV` を「補助変数の型についての union」ではなく
  **`n` を露出した族 `bcOuterRegionUVAt W n`** として定義し、
  `bc_capacity_subset_uv` は `⋂ n` 版で述べる。退避出口は
  `sorry` + `@residual(plan:bc-general-region-plan)`。
- **L-BCO6 (提案)**: 退化レート被覆 (S8) が MAC 同様 450 行級に膨らむ場合
  → `bc_capacity_subset_uv` を第一象限交差版
  `bcCapacityRegion W ∩ {p | 0 ≤ p.1 ∧ 0 ≤ p.2} ⊆ bcOuterRegionUV W` で先に閉じ、
  全平面版を後続 leg に送る (MAC `mac_timesharing_capacity_region` `Assembly.lean:908` と同じ形)。

**禁止事項の再確認**: どの退避でも「結合 memoryless を仮説で受け取る」形は取らない。
表 2 §結論のとおり構成側から導けるので、`*Hypothesis` 述語への束ね (tier 5) を
選ぶ理由が実測上存在しない。

---

## 着手用スケルトン

`InformationTheory/Shannon/BroadcastChannel/OuterBoundUV/Bridge.lean` の出だし
(step 4b-S2 の成果物まで)。

```lean
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Basic
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV
import InformationTheory.Shannon.ChannelCoding.CodeToAmbient  -- step 4b-S1 で新設
import InformationTheory.Fano.Measure

/-!
# Broadcast channel — the code-to-ambient bridge for the UV outer bound

## Main definitions

* `bcConverseAmbient` — the canonical ambient law of a broadcast code.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCodingConverseGeneral
open scoped ENNReal BigOperators

variable {α β₁ β₂ : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [StandardBorelSpace α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁]
    [MeasurableSingletonClass β₁] [StandardBorelSpace β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂]
    [MeasurableSingletonClass β₂] [StandardBorelSpace β₂]
variable {M₁ M₂ n : ℕ}

/-- Uniform input law on the broadcast message pair. -/
noncomputable def bcConverseInput (M₁ M₂ : ℕ) : Measure (Fin M₁ × Fin M₂) :=
  ((Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ • Measure.count).prod
    ((Fintype.card (Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count)

/-- Per-letter product-channel kernel of a broadcast code: the block output law is the
product over the `n` letters of the channel applied to the encoded pair, with the **output
pair kept joint** at each letter. -/
noncomputable def bcConverseKernel
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) :
    Kernel (Fin M₁ × Fin M₂) (Fin n → β₁ × β₂) :=
  Kernel.ofFunOfCountable (fun m ↦ Measure.pi (fun i ↦ W (c.encoder m i)))

/-- Canonical ambient measure for the broadcast converse: a uniform message pair passed
through the per-letter product channel. -/
noncomputable def bcConverseAmbient
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) :
    Measure ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) :=
  (bcConverseInput M₁ M₂) ⊗ₘ (bcConverseKernel c W)

/-- Message-1 projection. -/
def bcConverseMsg₁ : ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) → Fin M₁ := fun ω ↦ ω.1.1

/-- Message-2 projection. -/
def bcConverseMsg₂ : ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) → Fin M₂ := fun ω ↦ ω.1.2

/-- Receiver-1 output coordinate. -/
def bcConverseY₁s : Fin n → ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) → β₁ :=
  fun i ω ↦ (ω.2 i).1

/-- Receiver-2 output coordinate. -/
def bcConverseY₂s : Fin n → ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) → β₂ :=
  fun i ω ↦ (ω.2 i).2

end InformationTheory.Shannon.BroadcastChannel
```

到達目標 (step 4b-S8) の署名:

```lean
@[entry_point]
theorem bc_capacity_subset_uv
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    bcCapacityRegion W ⊆ bcOuterRegionUV W := by
  sorry -- @residual(plan:bc-general-region-plan)
```
