# AEP Phase E — 源符号化定理 achievability ムーンショット計画 🌙

<!--
雛形メモ:
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 判断ログは append-only。Phase 中の方針変更・撤退・当初仮定の修正を記録
- `rg "^- \[ \]"` で残タスク横断 grep、`rg "🔄"` でピボット箇所だけ拾える
-->

> **Status (2026-05-11)**: 起草。AEP moonshot ([`aep-moonshot-plan.md`](aep-moonshot-plan.md))
> Phase E (achievability) の deferred 単独 plan。
> シードカード ([`moonshot-seeds.md` "次のシード候補 A. 直接 deferred"](../moonshot-seeds.md#a-直接-deferred))
> の見積 100〜300 行 / 低リスク / 0.5〜1 週間 を起点に膨らませた。
>
> Phase D (`source_coding_converse`) が完了済 ([`aep-source-coding-plan.md`](aep-source-coding-plan.md)、
> `Common2026/Shannon/AEP.lean` で 0 sorry)、本 plan はその自然な後続。
>
> **撤退ライン**: Phase A (encoder/decoder def + round-trip) 緑通過時点で **typical set ↔ Fin M_n bijection の構成補題** が独立に立つ。Phase B/C で詰まる場合は Phase A のみ publish して残りを次セッションへ。

## 進捗

- [x] Phase 0 — Mathlib + 既存 Common2026 API インベントリ ✅ → [`aep-achievability-mathlib-inventory.md`](aep-achievability-mathlib-inventory.md)
- [ ] Phase A — encoder / decoder 構成 + round-trip lemma (`d_n ∘ c_n = id` on typicalSet) 📋
- [ ] Phase B — error rate bound (`error ⊆ ∁ typicalSet` + Tendsto 0) 📋
- [ ] Phase C — rate Tendsto (`log M_n / n → R`) + 主定理組成 📋
- [ ] Phase D — verify (`lake env lean Common2026/Shannon/AEP.lean` silent + proof-log + metrics) 📋

## ゴール / Approach

**最終到達点**: 源符号化定理 achievability —
任意の `R > entropy μ (Xs 0)` に対し、ブロック符号 `(c_n, d_n) : (Fin n → α) ↔ Fin M_n` で
`P{d_n(c_n(X^n)) ≠ X^n} → 0` ∧ `log M_n / n → R` を満たすものが存在する。

**Approach の中核 (typical-set enumeration constructive scheme、3 段)**:

1. **(a) `M_n := Nat.ceil (Real.exp (n · R))` + encoder/decoder 構成 (Phase A)** ─
   `ε := (R - entropy μ (Xs 0)) / 2 > 0` を取り、`H + ε < R` を確保。
   encoder `c_n : (Fin n → α) → Fin M_n` を:
   - typical block `x ∈ (typicalSet μ Xs n ε).toFinite.toFinset` ⇒ `Finset.equivFin` で `Fin (toFinset.card)` index 取得 → `Fin.castLE h_card_le` で `Fin M_n` に埋め込み
   - 非 typical block ⇒ default index `0`

   decoder `d_n : Fin M_n → (Fin n → α)` を symmetric に:
   - `k.val < toFinset.card` ⇒ `Finset.equivFin.symm` で `↑toFinset` を取り、coercion で `Fin n → α` に
   - 範囲外 ⇒ default block (任意固定)

   **round-trip lemma**: `∀ x ∈ typicalSet, d_n (c_n x) = x` (typical 集合上で正逆対応、非 typical は外側で error 容認)
2. **(b) error rate Tendsto (Phase B)** ─
   error 事象 `{ω | d_n (c_n (jointRV Xs n ω)) ≠ jointRV Xs n ω} ⊆ {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε}` (round-trip lemma の対偶)。
   Phase C 既存 `typicalSet_prob_tendsto_one` の **補集合** `μ {ω | jointRV Xs n ω ∉ typicalSet ...} → 0` を subset monotonicity で error rate に伝播。
3. **(c) rate Tendsto + 主定理組成 (Phase C)** ─
   `log M_n / n = log (Nat.ceil (Real.exp (n · R))) / n`、`Nat.le_ceil` + `Nat.ceil_lt_add_one` で `exp(nR) ≤ M_n < exp(nR) + 1`、両辺 `log` + `/n` で `R ≤ log M_n / n < log(exp(nR) + 1) / n → R` (上下挟み込み squeeze)。
   主定理は `⟨M, c, d, h_rate, h_error⟩` の `⟨..⟩` 組成 1 行。

**Approach 図**:

```
Phase 0  : Mathlib + Common2026 API インベントリ              ← 完 (本 plan + inventory 起草)
           ──────────────────────────────────────────
Phase A  : encoder / decoder 構成 + round-trip lemma          ← 山場 1、60〜100 行、2〜3 日
           ──────────────────────────────────────────
Phase B  : error rate Tendsto (subset + 補集合)                ← 中盤、30〜60 行、1〜2 日
           ──────────────────────────────────────────
Phase C  : rate Tendsto + 主定理組成                           ← 終段 plumbing、30〜60 行、1〜2 日
           ──────────────────────────────────────────
Phase D  : lake env lean silent + proof-log + metrics           ← verify、半日
```

**ファイル構成**:

```
Common2026/Shannon/
  AEP.lean             ← Phase A〜D 既存 (800 行)
                       ← 本 plan は **末尾 append**
                          (Phase A〜C in achievability 部分、120〜220 行)
```

AEP.lean は現在 800 行。Phase E +120〜220 行 = 920〜1020 行。**判断**: 800 行 → 1000 行台は許容範囲、ファイル分割 (`SourceCoding.lean` 新規) は **見送り**。Phase D 完了時点で同様の分割判断 (Phase A 着手時) は「800 行を超えそうなら分割」だったが、Phase E は内容が直接 Phase C (typicalSet) + Phase D (source coding converse) の素材を組み合わせるため append が clean。

**統合形 (Phase D + Phase E unified statement) は別 plan に切り出し**:
`liminf log M_n / n = entropy μ (Xs 0)` (両側等号) や
`(achievable rates) = {R | R ≥ entropy μ (Xs 0)}` の形は本 plan のスコープ外、Phase E 完了後に Phase F として deferred 化判断。理由: 統合形は (a) `inf_{achievable codes}` の sInf 構成 + (b) Phase D の `liminf` 形と Phase E の `Tendsto` 形を squeeze、で +50〜100 行追加、本 plan の "achievability 単体" のスコープを超える。

---

## Phase 0 — Mathlib + 既存 Common2026 API インベントリ ✅

### スコープ

[`aep-achievability-mathlib-inventory.md`](aep-achievability-mathlib-inventory.md) を起草、4 軸 (typical set 3 性質 / `Finset.equivFin` / `Nat.ceil` / errorProb 再利用) を裏取り。

### 結論

- **typical set 3 性質は Phase A〜C で完備**、`measurableSet_typicalSet` / `typicalSet_card_le` / `typicalSet_prob_tendsto_one` を直接利用
- **`Finset.equivFin` (`Mathlib/Data/Fintype/EquivFin.lean:320`) + `Fin.castLE` で encoder/decoder bijection が組成可**
- **`M_n := Nat.ceil (Real.exp (n · R))`** で `Nat.le_ceil` + `Nat.ceil_lt_add_one` から rate 漸近が squeeze で取れる
- **errorProb は Phase D と同形で再利用**、新規 formalism ゼロ

### Done 条件 (Phase 0)

- [x] 4 軸調査完了 (inventory)
- [x] Phase A skeleton (encoder/decoder def + round-trip lemma) が書ける状態
- [x] Phase B skeleton (error subset + Tendsto) が書ける状態
- [x] Phase C skeleton (rate Tendsto + 主定理 ⟨..⟩ 組成) が書ける状態

### 工数感

1 ターン (本 plan 起草 = 完)。

---

## Phase A — encoder / decoder 構成 + round-trip lemma 📋

### スコープ

```lean
namespace InformationTheory.Shannon

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                    [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The codebook size used in the achievability proof: `M_n := ⌈exp(n · R)⌉`. -/
noncomputable def codebookSize (R : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (Real.exp ((n : ℝ) * R))

/-- `M_n ≥ 1` (so `Fin M_n` is `Nonempty`). -/
lemma codebookSize_pos (R : ℝ) (n : ℕ) : 0 < codebookSize R n

/-- Cardinality of typical set is ≤ `M_n` (provided `H + ε ≤ R` and `hpos`). -/
lemma typicalSet_card_le_codebookSize
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (n : ℕ) {ε R : ℝ} (hε : 0 < ε) (h_le : entropy μ (Xs 0) + ε ≤ R) :
    (typicalSet μ Xs n ε).toFinite.toFinset.card ≤ codebookSize R n

/-- The encoder: typical blocks → `Fin M_n` index, non-typical → 0. -/
noncomputable def aepEncoder
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (n : ℕ) (ε R : ℝ)
    (h_card_le : (typicalSet μ Xs n ε).toFinite.toFinset.card ≤ codebookSize R n) :
    (Fin n → α) → Fin (codebookSize R n)

/-- The decoder: `Fin M_n` index → typical block (out of range → default). -/
noncomputable def aepDecoder
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (n : ℕ) (ε R : ℝ) :
    Fin (codebookSize R n) → (Fin n → α)

/-- **Round-trip lemma**: `d_n ∘ c_n = id` on typical set. -/
lemma aepDecoder_aepEncoder_of_mem_typicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (n : ℕ) (ε R : ℝ)
    (h_card_le : (typicalSet μ Xs n ε).toFinite.toFinset.card ≤ codebookSize R n)
    (x : Fin n → α) (hx : x ∈ typicalSet μ Xs n ε) :
    aepDecoder μ Xs n ε R (aepEncoder μ Xs n ε R h_card_le x) = x

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(A.1) `codebookSize` 定義** + `codebookSize_pos` ─ `Nat.ceil_pos` (`0 < x` ⟹ `0 < Nat.ceil x`) + `Real.exp_pos`。5〜10 行
- [ ] **(A.2) `typicalSet_card_le_codebookSize`** ─ Phase C `typicalSet_card_le` で `card ≤ exp(n(H+ε))`、`H + ε ≤ R` の monotonicity で `exp(n(H+ε)) ≤ exp(nR)`、`Nat.le_ceil` で `exp(nR) ≤ Nat.ceil (exp(nR)) = codebookSize R n`。`Nat` ↔ `ℝ` cast plumbing。15〜25 行
- [ ] **(A.3) `aepEncoder` 定義** ─ 戦略: `if hx : x ∈ (typicalSet μ Xs n ε).toFinite.toFinset` の `Decidable` 分岐 (`Fin n → α` Fintype + `Set.toFinite` で `Decidable` auto-derive)、then 分岐は `Finset.equivFin ⟨x, hx⟩` で `Fin (toFinset.card)` index、`Fin.castLE h_card_le` で `Fin (codebookSize R n)` に埋め込み、else 分岐は `⟨0, codebookSize_pos R n⟩`。15〜25 行
- [ ] **(A.4) `aepDecoder` 定義** ─ 戦略: 引数 `k : Fin (codebookSize R n)` で `if hk : k.val < (typicalSet μ Xs n ε).toFinite.toFinset.card` の分岐、then 分岐は `(toFinset.equivFin).symm ⟨k.val, hk⟩` で `↑toFinset` の元 → coercion で `Fin n → α`、else 分岐は `Classical.arbitrary _` (Pi 型は `Nonempty` 自動 derive、`Fin n → α` で `α : Nonempty` 仮定済)。15〜25 行
- [ ] **(A.5) `aepDecoder_aepEncoder_of_mem_typicalSet` 主補題** ─ 戦略: `x ∈ typicalSet` で `aepEncoder` の then 分岐に入り、`Finset.equivFin` の left_inv (= `equivFin.symm (equivFin _) = _`) を使う。`Set.Finite.mem_toFinset` で `x ∈ toFinite.toFinset ↔ x ∈ typicalSet`。`Fin.castLE` の `val_castLE = val` で `aepDecoder` の then 分岐の hypothesis を満たす。20〜30 行 (細かい cast/coercion plumbing が主)

### Done 条件

- [ ] 上記 5 項目が `lake env lean Common2026/Shannon/AEP.lean` で silent
- [ ] skeleton-driven で A.1 → A.2 → A.3 → A.4 → A.5 の sorry を割る順序

### 工数感

2〜3 日 (60〜100 行)。**最大リスク**: A.5 の `Finset.equivFin` left_inv の plumbing で `↑toFinset` の coercion (subtype の `.val`) と `Fin.castLE` の `.val` 平坦化が `simp` で素直に通るか。前例として Han Phase D の `MeasurableEquiv` plumbing は若干重かったが、本 plan は `Equiv` (`MeasurableEquiv` ではなく) なので measurability plumbing 不要、Han より軽い見込み。

### 撤退ライン (Phase A 内)

- A.5 で `Finset.equivFin.symm.left_inv` 周りの `simp` が通らない → `Equiv.symm_apply_apply` を 1 段ずつ rewrite で割る (+10〜20 行)
- A.4 の `else` 分岐で `Classical.arbitrary` が Pi 型で素直に取れない → `fun _ => Classical.arbitrary α` に書き換える (Pi は pointwise nonempty で OK)

---

## Phase B — error rate Tendsto (`error ⊆ ∁ typicalSet` + Tendsto 0) 📋

### スコープ

```lean
namespace InformationTheory.Shannon

/-- error event ⊆ {jointRV Xs n ∉ typicalSet}. -/
lemma error_subset_compl_typicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (n : ℕ) (ε R : ℝ)
    (h_card_le : (typicalSet μ Xs n ε).toFinite.toFinset.card ≤ codebookSize R n) :
    {ω | aepDecoder μ Xs n ε R (aepEncoder μ Xs n ε R h_card_le (jointRV Xs n ω))
            ≠ jointRV Xs n ω}
      ⊆ {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε}

/-- error rate → 0. -/
lemma aep_errorProb_tendsto_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {ε R : ℝ} (hε : 0 < ε) (h_le : entropy μ (Xs 0) + ε ≤ R) :
    Tendsto
      (fun n => InformationTheory.MeasureFano.errorProb μ
                  (jointRV Xs n)
                  (fun ω => aepEncoder μ Xs n ε R
                              (typicalSet_card_le_codebookSize μ Xs hXs hpos n hε h_le)
                              (jointRV Xs n ω))
                  (aepDecoder μ Xs n ε R))
      atTop (𝓝 0)

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(B.1) `error_subset_compl_typicalSet`** ─ 戦略: 対偶 = "x ∈ typicalSet ⇒ d (c x) = x" は Phase A `aepDecoder_aepEncoder_of_mem_typicalSet` そのもの。`Set.subset_def` + 対偶。10〜20 行
- [ ] **(B.2) `aep_errorProb_tendsto_zero`** ─ 戦略: `errorProb μ X^n Yo_n d` を unfold して `(μ {ω | d (c (X^n ω)) ≠ X^n ω}).real`、subset monotonicity で `≤ (μ {ω | X^n ω ∉ typicalSet}).real = 1 - (μ {ω | X^n ω ∈ typicalSet}).real` (補集合)。Phase C `typicalSet_prob_tendsto_one` で `(μ {ω | X^n ω ∈ typicalSet}).real → 1`、`Tendsto.const_sub` で `1 - · → 0`、`Tendsto.le_of_le` (squeeze) で error rate → 0。**仮定 `hindep_full : iIndepFun` ではなく `hindep : Pairwise IndepFun` で十分** (Phase C 既存補題が Pairwise で受けるので)、Phase E 主定理側で `iIndepFun.indepFun` で派生する。20〜40 行

### Done 条件

- [ ] 上記 2 項目が silent
- [ ] subset 補題 + Tendsto 補題が独立に通る (skeleton で検証)

### 工数感

1〜2 日 (30〜60 行)。**最大リスク**: B.2 で `errorProb` の `.real` plumbing と `μ.real` ↔ `μ` ↔ `(μ ...).toReal` の cast 往復。Phase D `source_coding_per_n_bound` 末尾で同種の `errorProb` 操作が通っているので前例あり。

### 撤退ライン (Phase B 内)

- B.2 の Tendsto squeeze で `Tendsto.le_of_le` 系が直接使えない → `Tendsto.of_tendsto_of_tendsto_of_le_of_le` (squeeze theorem) に切り替え (+5〜10 行)
- subset → measure 不等式の plumbing で `MeasurableSet` の引き回しが重い → `μ.real_mono_of_measurableSet` 系を直接呼び (+5〜10 行)

---

## Phase C — rate Tendsto + 主定理組成 📋

### スコープ

```lean
namespace InformationTheory.Shannon

/-- `log M_n / n → R`. -/
lemma codebookSize_log_div_tendsto
    (R : ℝ) :
    Tendsto (fun n : ℕ => Real.log (codebookSize R n : ℝ) / n) atTop (𝓝 R)

/-- **Source coding theorem, achievability**:
For any rate `R > entropy μ (Xs 0)`, there exists a block code with rate `R` and
vanishing error. -/
theorem source_coding_achievability
    {Ω : Type*} [MeasurableSpace Ω]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {R : ℝ} (hR : entropy μ (Xs 0) < R) :
    ∃ M : ℕ → ℕ, ∃ _hM_pos : ∀ n, 0 < M n,
    ∃ c : ∀ n, (Fin n → α) → Fin (M n),
    ∃ d : ∀ n, Fin (M n) → (Fin n → α),
      Tendsto (fun n => Real.log (M n : ℝ) / n) atTop (𝓝 R) ∧
      Tendsto
        (fun n => InformationTheory.MeasureFano.errorProb μ
                    (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n))
        atTop (𝓝 0)

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(C.1) `codebookSize_log_div_tendsto`** ─ 戦略: squeeze.
  - 下界: `Real.exp (n · R) ≤ codebookSize R n` (Nat.le_ceil) ⟹ `n · R ≤ log (codebookSize R n)` ⟹ `R ≤ log (codebookSize R n) / n` (n ≥ 1)
  - 上界: `codebookSize R n < Real.exp (n · R) + 1` (`Nat.ceil_lt_add_one`) ⟹ `log (codebookSize R n) < log (exp (n · R) + 1)` ⟹ `log (codebookSize R n) / n < log (exp (n · R) + 1) / n`
  - 上界の `log (exp (n · R) + 1) / n → R` は `log (exp (n · R) + 1) = log (exp(nR) (1 + exp(-nR))) = n · R + log (1 + exp(-nR))`、`exp(-nR) → 0` (when `R > 0`) または bounded、`log (1 + ε) ≤ ε` で `/ n → 0`。`R ≤ 0` の場合 (`R = 0` で `M_n = 1`、`log 1 / n = 0 → 0 ≠ R` で statement 破綻するが、`hR : H < R` から `R > 0` (entropy ≥ 0、`hR` で strict) は **Phase E 全体で `R > 0` を内部 derive 可能** ─ entropy ≥ 0 + hR。要確認: `entropy_nonneg` は `Pi.lean` or `Bridge.lean` に存在するか)。25〜45 行
- [ ] **(C.2) 主定理 `source_coding_achievability`** ─ 戦略: `set ε := (R - entropy μ (Xs 0)) / 2 with hε_def`、`hε : 0 < ε` (`hR` から)、`h_le : entropy μ (Xs 0) + ε ≤ R` (algebra)、`set h_card := typicalSet_card_le_codebookSize μ Xs hXs hpos n hε h_le`、`refine ⟨codebookSize R, codebookSize_pos R, fun n => aepEncoder μ Xs n ε R h_card, fun n => aepDecoder μ Xs n ε R, ?, ?⟩`、第一: C.1 直接、第二: B.2 (`aep_errorProb_tendsto_zero` を `hindep_full.indepFun` 経由で Pairwise に lift して呼ぶ)。10〜20 行

### Done 条件

- [ ] 上記 2 項目が silent
- [ ] 主定理 `source_coding_achievability` の statement が Cover-Thomas (Theorem 5.4.2 系) と一致
- [ ] proof-log + metrics 取得済み

### 工数感

1〜2 日 (30〜60 行)。**最大リスク**: C.1 上界の `log (exp(nR) + 1) → n · R` 漸近 plumbing。`Tendsto.div_atTop` + `tendsto_const_div_atTop` 系の Mathlib API 完備性 (Phase D Phase C で類似 Tendsto algebra は通っているので前例あり)。

### 撤退ライン (Phase C 内)

- C.1 上界 squeeze で `log (exp(nR) + 1) - n · R → 0` の Mathlib 既存補題が薄い → `log (1 + x) ≤ x` (`Real.log_one_add_le_iff`?) を使う 自前 lemma で 5〜10 行追加
- C.1 で `R ≤ 0` の corner case が破綻 → `entropy_nonneg` (要既存確認、無ければ Common2026 内自前) で `R > 0` を確保、Phase E は `R > 0` 内部 derive で Cover-Thomas 教科書範囲を維持

---

## Phase D — verify 📋

### スコープ

- [ ] `lake env lean Common2026/Shannon/AEP.lean` silent
- [ ] `lake build Common2026.Shannon.AEP` 緑通過 (依存 module の olean refresh 確認)
- [ ] proof-log: `docs/proof-logs/proof-log-aep-achievability.md` 起票
- [ ] metrics: `scripts/session_metrics.ts` 実行 + `docs/metrics/aep-achievability.{manifest,metrics}.{json,md}` 出力
- [ ] `docs/moonshot-seeds.md` の "Seed 4 → A. AEP Phase E" 項目を ✅ 更新 (Phase F unified 形 deferred 化判断)
- [ ] `docs/shannon/aep-moonshot-plan.md` の進捗を `Phase E ✅` に更新

### Done 条件

- [ ] 全 5 項目完了

### 工数感

半日。

---

## 失敗判定 / 撤退ライン (全体)

| 撤退ポイント | 判定基準 | アクション |
|---|---|---|
| Phase 0 で typical set 3 性質に欠陥 | Phase A〜C で 0 sorry 確認済み | 不該当 |
| Phase A の A.5 (round-trip) で 2〜3 日溶ける | `Finset.equivFin.symm.left_inv` plumbing が `simp` で通らない | 1 段ずつ `Equiv.symm_apply_apply` で rewrite (+10〜20 行) |
| Phase B の B.2 (Tendsto squeeze) で詰まる | `errorProb` の `.real` cast 往復が plumbing-heavy | `Tendsto.of_tendsto_of_tendsto_of_le_of_le` 直接呼び (+5〜10 行) |
| Phase C の C.1 (上界 squeeze) で詰まる | `log (exp + 1) → ...` Mathlib 補題が薄い | 自前 `log_one_add_le` で +5〜10 行 |
| Phase C の C.1 で `R > 0` corner case 破綻 | `entropy_nonneg` 不在 | 既存 `negMulLog ≥ 0` から自前 5 行で `entropy_nonneg`、Common2026/Shannon/Bridge.lean に append |
| **Phase A 完了 (= encoder/decoder + round-trip)** | `aepDecoder_aepEncoder_of_mem_typicalSet` silent | **★ 撤退ライン: 「typical set ↔ Fin M_n bijection plumbing」が独立 publish 可能 ★**。Phase B/C を別 plan に切り出すかは Phase A 完了時点で判断 |
| Phase B 完了 (= error rate) | `aep_errorProb_tendsto_zero` silent | 撤退判断不要、Phase C へ |
| Phase C 完了 (= 主定理) | `source_coding_achievability` silent | 完成 |

どのケースも proof-log に **正直に**記録。

---

## 工数見積もり総括

| 経路 | 工数 | 行数 | リスク |
|---|---|---|---|
| Phase A 単独 (encoder/decoder + round-trip) | **2〜3 日** | **60〜100 行** | **低〜中** (A.5 `Equiv` plumbing) |
| Phase A〜B (error rate Tendsto 確定) | **3〜5 日** | **90〜160 行** | **低〜中** |
| Phase A〜C (主定理) | **4〜7 日** | **120〜220 行** | **低〜中** |
| Phase A〜D (verify 込み) | **5〜8 日** | **120〜220 行** | **低〜中** |

シード見積 **100〜300 行 / 低リスク / 0.5〜1 週間** とほぼ一致 (やや少なめ、Phase D の `entropy_jointRV_eq_n_smul` plumbing が既に立っているため Phase E は構成側 + Tendsto 側の plumbing のみ)。

撤退時 (Phase A) でも **「typical set ↔ Fin M_n bijection plumbing」** が独立 publish ライン。`Finset.equivFin` を `Set.toFinite.toFinset` 上で具体的に組み合わせるスニペットは Mathlib にも前例少なめで、AEP 以外でも再利用可能。

---

## 当面の next step

1. ✅ **Phase 0 (本 plan + inventory 起草)** — 完 (2026-05-11)
2. **Phase A skeleton** — `Common2026/Shannon/AEP.lean` 末尾に `codebookSize` / `aepEncoder` / `aepDecoder` / `aepDecoder_aepEncoder_of_mem_typicalSet` を `:= by sorry` で append、緑通過確認 ← **次これ**
3. **Phase A 完で Phase B 着手判定** — round-trip silent なら Phase B (error rate Tendsto)
4. **Phase B 完で Phase C 着手判定** — `aep_errorProb_tendsto_zero` silent なら Phase C (主定理 + rate Tendsto)
5. **Phase C 完 = 完成**: proof-log + metrics 取得、Phase F (unified `liminf = entropy` 統合形) を別 plan に切り出すかは本 plan 完了時に判断

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### 2026-05-11 — 起草

- **`M_n := Nat.ceil (Real.exp (n · R))` を採用 (`2^⌈nR⌉` ではなく)**: Phase C 既存 `Real.exp` plumbing と整合させ、`log 2` 換算 plumbing を回避。教科書 (Cover-Thomas Theorem 5.4.2) は `2^⌈nR⌉` で書くが、本 plan の statement は `log` 基底を Real (= ln) に統一しているので `Real.exp` 形が自然
- **standalone achievability statement (Phase D `liminf` 形 とは別) を採用**: 統合形 `liminf log M_n / n = entropy μ (Xs 0)` (両側等号) は **Phase F (deferred)** に切り出し。理由は (a) sInf / inf_{achievable codes} 構成 plumbing が +50〜100 行追加で本 plan のスコープ超過、(b) Phase D は forall code → liminf ≥、Phase E は exists code → Tendsto = R で statement 形が異なる (片や `liminf`、片や `Tendsto`) ので 1 statement に押し込めるには別途 sInf wrapper が要る
- **`hpos : ∀ x, P(x) > 0` 仮定を継承**: Phase C `typicalSet_card_le` で確定済み、Phase E でもそのまま使う。撤回路線 (= 一般 measure で書き直し) は Phase C 撤退ライン超過で本 plan のスコープ外
- **encoder/decoder の measurability は不要**: Phase E 主定理は `errorProb` の `.real` 値だけ要求、measurability は `errorProb` 内部で `MeasurableSet` チェックが入る。`aepEncoder` / `aepDecoder` は構成上 `Measurable` だが (Fintype の関数は自動 derive)、本 plan の statement では明示しない。Phase D の主定理 `source_coding_converse` も同じ流儀 (encoder/decoder の measurable 仮定を取らない、`measurable_of_countable` で内部 derive)
