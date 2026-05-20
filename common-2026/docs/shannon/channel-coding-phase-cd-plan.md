# Channel coding achievability — Phase C + D (B-3'') ムーンショット計画 🌙

> オーケストレータ指示: B-3 (`channel-coding-achievability-plan.md`,
> `Common2026/Shannon/ChannelCoding.lean`, 659 行, Phase A + Phase B-(a,b,c) 完了)
> を起点に、**Phase C (random codebook + averaging)** + **Phase D (主定理
> `R < I ⟹ ∃ code, P_err → 0`)** を **新規ファイル** に並立 publish。Phase B 3 つの
> joint AEP bound はそのまま黒箱として呼び、`ChannelCoding.lean` (659 行) は touch しない。
> B-1' / B-5' / B-8' / B-1'' / B-2'' と同じ「親プラン deferred → 子プランで完成」
> パターン。

## Status / 目標

**✅ `B-3''` 完全閉鎖 (2026-05-12、0 sorry)**。Phase C-(a)-(d) + Phase D-(a)-(b) 全段 publish 済。詳細は末尾「実装結果サマリ」。

> 実態整合 (2026-05-20): DONE-HONEST-HYPS — `channel_coding_achievability` (`Common2026/Shannon/ChannelCodingAchievability.lean:1607`、0 sorry) を確認。signature は std typeclass binders + 正直な positivity 仮説 `hp_pos : ∀ a, 0 < p.real {a}` / `hW_pos : ∀ a b, 0 < (W a).real {b}` (full-support、後段 D-1 で smoothing 除去) のみ。pass-through Prop 仮説なし。下記 signature 例は `hW_pos` 追加前の旧形 (実装結果サマリ参照で訂正済)。

主結果 (Cover-Thomas Theorem 7.7.1 achievability 半分):

```lean
theorem channel_coding_achievability
    [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]
    (W : Channel α β) [IsMarkovKernel W]
    (p : Measure α) [IsProbabilityMeasure p]
    (hp_pos : ∀ a : α, 0 < p.real {a})
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (mutualInfoOfChannel p W).toReal)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        (c.averageErrorProb W).toReal < ε'
```

備考:
- **Channel namespace**: 本 plan は既存 `InformationTheory.Shannon.ChannelCoding` namespace
  下で `Code`, `Channel`, `mutualInfoOfChannel`, `jointlyTypicalSet`,
  `jointlyTypicalSet_prob_tendsto_one` / `_card_le` / `_indep_prob_le`,
  `Code.averageErrorProb` をそのまま使う。
- **i.i.d. 入力**: `p` を固定し、Phase B-(c) の `iIndepFun` + `IdentDistrib` 仮定は
  `Measure.pi (fun _ : Fin n => p)` 上の coordinate projections (`Xs i ω := ω i`) で
  自動的に充足される。
- **Rate slack**: 主定理の `R < I` から `R + 3ε < I` となる正の `ε := (I - R)/6` (または
  類似) を取り、Phase C を呼ぶ。
- **Codebook size**: `M := Nat.ceil (Real.exp ((n : ℝ) * R))`。

副目標:
- (Phase C) `random_codebook_average_le`: ランダム codebook 全体上の平均誤り確率は
  `2 · ((n_{B-(a)} で eventually 1 から離れる量) + (M-1) · exp(-n(I - 3ε)))` で押さえる。
- (Phase C) `exists_codebook_with_low_error`: pigeonhole で `∃ codebook, P_err ≤ ...`。

## Approach

**Cover-Thomas 7.7.3-4 流の random coding + averaging (C2 pigeonhole)**:

1. **Codebook 全体集合**: `Codebook M n α := Fin M → (Fin n → α)`。alphabet 有限 + `n`,
   `M` 有限 ⟹ `Codebook M n α` は `Fintype`。**確率測度を立てない** (親 plan 判断 #2
   採用)。codebook 全体上の `∑` を有限 finset (`Finset.univ : Finset (Codebook M n α)`)
   で取る。
2. **Joint typical decoding rule**: 受信 `y : Fin n → β` で
   - **unique** な `m : Fin M` が `(codebook m, y) ∈ jointlyTypicalSet μ Xs Ys n ε`
     を満たすとき: `decode = m`.
   - そうでないとき (一意でない / 全くない): **任意の固定 message** (e.g., `0`、
     `M > 0` から取れる) を返す。
3. **誤り確率の分解** (固定 codebook `c`、送信 message `m`):
   - (E1) **true codeword が typical でない**: `(c m, Y^n) ∉ jointlyTypicalSet`.
   - (E2) **alias codeword が typical 集合に紛れ込む**: `∃ m' ≠ m, (c m', Y^n) ∈ jointlyTypicalSet`.
   - 誤り `decoder(Y^n) ≠ m ⟹ E1 ∨ E2` (decoder の定義から)。
4. **Random codebook 上の平均** (over `codebook ∈ Codebook M n α` uniformly):
   - **(E1) 部分**: codebook を marginalize して `P((X^n(m), Y^n) ∉ jointlyTypicalSet)`、
     これは Phase B-(a) で `n → ∞` で 0 に行く。`m` に依存しない。
   - **(E2) 部分**: 各 `m' ≠ m` で Phase B-(c) で `≤ exp(-n(I - 3ε))`。Union bound で
     `(M-1) · exp(-n(I - 3ε))`。
5. **平均 ≤ 2ε ⟹ ∃ codebook**: pigeonhole (`Finset.exists_le_of_sum_le`)。
6. **Phase D 主定理**: `ε := (I - R)/6 > 0` を取り、`R + 3ε = (R + I)/2 < I`。
   `M · exp(-n(I - 3ε)) = exp(nR + log M - n(I - 3ε))`、`log M ≈ nR` から
   `M · exp(-n(I - 3ε)) ≤ exp(-n(I-R-3ε)) · O(1) → 0`.

**Mathlib-shape-driven Definitions 節 (CLAUDE.md) の適用**:
- `Codebook M n α` は **`abbrev` (`= Fin M → (Fin n → α)`)** とすることで `Fintype`
  / `DecidableEq` / `MeasurableSpace` を自動継承。
- 「random codebook 上の sum」は **`Finset.sum (s := Finset.univ) (f := fun c => ...)`**
  形。
- Decoder は `Classical.dec` で「一意 m 」を判定し、`Classical.choose` で取る。

## Phase 0 — Inventory + ファイル配置

### ファイル配置の判断

**採用: (B) 新規 `Common2026/Shannon/ChannelCodingAchievability.lean` 並立 publish**。

理由:
- B-1' / B-5' / B-8' / B-2'' の「親 file 不変 + 子 file 並立 publish」パターン。
- `ChannelCoding.lean` 659 行 + Phase C+D 500-900 行を単一 file 化すると 1200-1500 行で
  可読性低下。
- import 方向: 子 → 親 の一方向、循環なし。

### 既存 ChannelCoding.lean の公開 API (verbatim)

`Common2026/Shannon/ChannelCoding.lean` 公開 API (Phase C/D で全部呼ぶ):

```lean
namespace InformationTheory.Shannon.ChannelCoding

abbrev Channel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] :=
  Kernel α β

noncomputable def jointDistribution (p : Measure α) (W : Channel α β) : Measure (α × β)
noncomputable def outputDistribution (p : Measure α) (W : Channel α β) : Measure β
noncomputable def mutualInfoOfChannel (p : Measure α) (W : Channel α β) : ℝ≥0∞

structure Code (M n : ℕ) (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  encoder : Fin M → (Fin n → α)
  decoder : (Fin n → β) → Fin M

namespace Code
  def decodingRegion (c : Code M n α β) (m : Fin M) : Set (Fin n → β)
  def errorEvent (c : Code M n α β) (m : Fin M) : Set (Fin n → β)
  noncomputable def errorProbAt
      (c : Code M n α β) (W : Channel α β) (m : Fin M) : ℝ≥0∞
  noncomputable def averageErrorProb
      (c : Code M n α β) (W : Channel α β) : ℝ≥0∞
end Code

noncomputable def jointSequence
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) : ℕ → Ω → α × β
noncomputable def jointlyTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (n : ℕ) (ε : ℝ) :
    Set ((Fin n → α) × (Fin n → β))

theorem jointlyTypicalSet_prob_tendsto_one
    [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY : Pairwise fun i j => Ys i ⟂ᵢ[μ] Ys j)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ : Pairwise fun i j =>
      jointSequence Xs Ys i ⟂ᵢ[μ] jointSequence Xs Ys j)
    (hidentZ : ∀ i,
      IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto (fun n : ℕ => μ {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈
        jointlyTypicalSet μ Xs Ys n ε}) Filter.atTop (𝓝 1)

theorem jointlyTypicalSet_card_le
    [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hpos : ∀ p : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((jointlyTypicalSet μ Xs Ys n ε).toFinite.toFinset.card : ℝ) ≤
      Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) + ε))

theorem jointlyTypicalSet_indep_prob_le
    [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX_full : iIndepFun (fun i => Xs i) μ)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY_full : iIndepFun (fun i => Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (((μ.map (jointRV Xs n)).prod (μ.map (jointRV Ys n))).real
        (jointlyTypicalSet μ Xs Ys n ε))
      ≤ Real.exp ((n : ℝ) *
          ((entropy μ (jointSequence Xs Ys 0)
            - entropy μ (Xs 0) - entropy μ (Ys 0)) + 3 * ε))
```

### Mathlib API 必要リスト

- `Finset.exists_le_of_sum_le` (`Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`):
  pigeonhole 本体。
- `Real.exp_neg`, `Real.exp_add`, `Real.exp_pos`, `Real.exp_le_exp`,
  `Real.tendsto_exp_neg_atTop_nhds_zero` (`Mathlib/Analysis/SpecialFunctions/Exp.lean`).
- `Nat.le_ceil`, `Nat.ceil_lt_add_one`, `Nat.one_le_ceil_iff`
  (`Mathlib/Algebra/Order/Floor.lean`).
- `Measure.pi` + `Measure.pi_singleton` (既存使用).
- `Filter.Tendsto.add`, `Filter.Tendsto.mul`,
  `tendsto_of_tendsto_of_tendsto_of_le_of_le` (squeeze).
- `iIndepFun_iff_map_fun_eq_pi_map` (既存 AEP 使用).

### TBD: i.i.d. 確率空間構築の plumbing

**TBD 1**: 「入力分布 `p : Measure α` と channel `W` の i.i.d. 拡張」を Phase D で
立てる際の Ω の選択:
- **候補 (i)**: `Ω := (Fin n → α) × (Fin n → β)`.
- **候補 (ii) 採用**: `Ω := Fin n → α × β`, `μ := Measure.pi (fun _ => jointDistribution p W)`、
  `Xs i ω := (ω i).1`, `Ys i ω := (ω i).2`。joint axis の coordinate projection が
  `jointSequence` と defeq。

実際に立てる lemmas (Phase C-(a) 冒頭):

```lean
section IIDInput

variable (W : Channel α β) [IsMarkovKernel W] (p : Measure α) [IsProbabilityMeasure p]

/-- 入力 + channel の i.i.d. 拡張. -/
noncomputable def iidJointMeasure (n : ℕ) : Measure (Fin n → α × β) :=
  Measure.pi (fun _ : Fin n => jointDistribution p W)

instance (n : ℕ) : IsProbabilityMeasure (iidJointMeasure W p n) := by
  unfold iidJointMeasure; infer_instance

end IIDInput
```

## Phase C — Random codebook + averaging argument (~310-460 行)

### Phase C-(a) — Codebook + decoder skeleton (~80-120 行)

定義:

```lean
abbrev Codebook (M n : ℕ) (α : Type*) [MeasurableSpace α] :=
  Fin M → (Fin n → α)

noncomputable def jointTypicalDecoder
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (codebook : Codebook M n α) :
    (Fin n → β) → Fin M := fun y =>
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  if h : ∃! m : Fin M, (codebook m, y) ∈ jointlyTypicalSet μ Xs Ys n ε
    then Classical.choose h.exists
    else ⟨0, hM⟩

noncomputable def codebookToCode
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (codebook : Codebook M n α) :
    Code M n α β where
  encoder := codebook
  decoder := jointTypicalDecoder μ Xs Ys hM ε codebook
```

ステップ:
- [ ] `Codebook` abbrev (~5 行)
- [ ] `jointTypicalDecoder` (Classical.dec + Classical.choose、~40 行)
- [ ] `codebookToCode` (bundling, ~15 行)
- [ ] (補題) `decode_eq_iff_unique` (~40 行)

### Phase C-(b) — 各 codeword の error prob bound (~110-160 行)

主補題:

```lean
theorem errorProbAt_le_E1_plus_E2
    (W : Channel α β) [IsMarkovKernel W]
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (codebook : Codebook M n α) {hM : 0 < M} {ε : ℝ}
    (m : Fin M) :
    let c := codebookToCode μ Xs Ys hM ε codebook
    (c.errorProbAt W m).toReal
      ≤ (Measure.pi (fun i => W (codebook m i))).real
          {y | (codebook m, y) ∉ jointlyTypicalSet μ Xs Ys n ε}
        + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m,
            (Measure.pi (fun i => W (codebook m i))).real
              {y | (codebook m', y) ∈ jointlyTypicalSet μ Xs Ys n ε}
```

ステップ:
- [ ] `errorEvent ⊆ E1 ∪ E2` (~50 行)
- [ ] `measure_union_le` (~10 行)
- [ ] `measure(E2) ≤ ∑ m' ≠ m, ...` (union bound, ~30 行)
- [ ] `.toReal` 変換 (~30 行)

### Phase C-(c) — Random codebook average bound (~110-160 行)

主補題:

```lean
theorem random_codebook_average_le
    (W : Channel α β) [IsMarkovKernel W]
    (p : Measure α) [IsProbabilityMeasure p]
    (hp_pos : ∀ a : α, 0 < p.real {a})
    {M n : ℕ} (hM : 0 < M) {ε : ℝ} (hε : 0 < ε)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX : iIndepFun (fun i => Xs i) μ)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY : iIndepFun (fun i => Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ : Pairwise fun i j =>
      jointSequence Xs Ys i ⟂ᵢ[μ] jointSequence Xs Ys j)
    (hidentZ : ∀ i,
      IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    (hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {p}) :
    (Fintype.card (Codebook M n α) : ℝ)⁻¹ *
      ∑ codebook : Codebook M n α,
        ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal
    ≤ μ.real
        {ω | (jointRV Xs n ω, jointRV Ys n ω) ∉ jointlyTypicalSet μ Xs Ys n ε}
      + ((M : ℝ) - 1) *
          Real.exp ((n : ℝ) *
            ((entropy μ (jointSequence Xs Ys 0)
              - entropy μ (Xs 0) - entropy μ (Ys 0)) + 3 * ε))
```

証明戦略:
1. **Fubini-like swap**: `(1/|Codebooks|) ∑_codebook (1/M) ∑_m P_err(codebook, m)` を
   外側 / 内側を入れ替え `(1/M) ∑_m E_codebook[P_err(codebook, m)]` に。
2. (E1) 部分: Phase B-(a) で `μ.real {(X^n, Y^n) ∉ A_ε^n}` に rewrite。
3. (E2) 部分: Phase B-(c) で `(M-1)` 倍 union bound。

ステップ:
- [ ] (補題) `average_over_codebook_eq_iid_expectation` (~30 行)
- [ ] (E1) 項を Phase B-(a) event に rewrite (~30 行)
- [ ] (E2) 項を Phase B-(c) で `(M-1)` 倍 union bound (~50 行)
- [ ] 結合 (~30 行)

### Phase C-(d) — Pigeonhole (~30-60 行)

主補題:

```lean
theorem exists_codebook_le_avg
    (W : Channel α β) [IsMarkovKernel W]
    {M n : ℕ} (hM : 0 < M) {ε : ℝ}
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (B : ℝ)
    (h_avg :
      (Fintype.card (Codebook M n α) : ℝ)⁻¹ *
        ∑ codebook : Codebook M n α,
          ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal ≤ B) :
    ∃ codebook : Codebook M n α,
      ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal ≤ B
```

ステップ:
- [ ] `Codebook M n α` の nonemptiness (~10 行)
- [ ] `Finset.exists_le_of_sum_le` (~10 行)
- [ ] `(1/N) ∑ ≤ B ⟹ ∑ ≤ N · B` plumbing (~10 行)

## Phase D — 主定理組立 (~130-230 行)

### Phase D-(a) — N の存在 (~80-150 行)

戦略:
1. `ε := (I - R)/6` を取り `R + 3ε < I`, `I - R - 3ε > 0`.
2. `M := Nat.ceil (Real.exp (n · R))` で `M ≤ exp(nR) + 1`.
3. (E1) Phase B-(a) → `eventually < ε'/2`.
4. (E2) `(M-1) exp(-n(I-3ε)) ≤ exp(-n(I-R-3ε)/2) → 0` → `eventually < ε'/2`.
5. `N := max(N_a, N_b)`.

ステップ:
- [ ] `I - R > 0` から `ε := (I - R)/6` (~10 行)
- [ ] (E1) `→ 0` from `jointlyTypicalSet_prob_tendsto_one` (~20 行)
- [ ] (E2) 指数 decay (~50 行)
- [ ] `N := max(N_a, N_b)` (~30 行)

### Phase D-(b) — 主定理 (~50-80 行)

```lean
theorem channel_coding_achievability
    (W : Channel α β) [IsMarkovKernel W]
    (p : Measure α) [IsProbabilityMeasure p]
    (hp_pos : ∀ a : α, 0 < p.real {a})
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (mutualInfoOfChannel p W).toReal)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        (c.averageErrorProb W).toReal < ε'
```

## 見積行数

| Phase | 内訳 | 行数見積 |
|---|---|---|
| Phase 0 (file 配置, IIDInput plumbing) | ~50-80 行 | |
| Phase C-(a) Codebook + decoder skeleton | 80-120 行 | |
| Phase C-(b) 各 codeword error bound | 110-160 行 | |
| Phase C-(c) Random codebook average | 110-160 行 | |
| Phase C-(d) Pigeonhole | 30-60 行 | |
| Phase D-(a) N の存在 | 80-150 行 | |
| Phase D-(b) 主定理 | 50-80 行 | |
| **合計** | | **~510-810 行** |

## 撤退ライン / 部分完了境界

- **Phase C-(a) + (b) 完了で commit**: decoder definition + per-codeword decomp publish。
- **Phase C 完了で commit**: random codebook averaging を独立 lemma として publish。
- **Phase D 完了で commit**: 主定理 publish。B-3 完成。

## 判断ログ

1. **ファイル配置 = 新規 `ChannelCodingAchievability.lean` (候補 B)** — B-1' / B-5' /
   B-8' / B-2'' の並立 publish 前例に整合。

2. **Decoder = 「unique m が joint typical」or fallback `⟨0, hM⟩`** — Cover-Thomas 7.7.4 流。
   確率測度を絡めず、純粋に `Classical.dec` + `Classical.choose`。

3. **Codebook 上の sum = `Finset.univ` 上の sum** (親 plan #2 踏襲):
   確率測度 (uniform on `Codebook M n α`) を立てずに `Finset` sum 不等式 +
   `Finset.exists_le_of_sum_le` で pigeonhole。

4. **i.i.d. 拡張 = `Ω := Fin n → α × β`, `μ := Measure.pi (jointDistribution p W)`** —
   joint axis の coordinate projection が `jointSequence` と defeq。

5. **Rate slack `ε := (I - R) / 6`** — `R + 3ε = (R + I)/2 < I`、`I - R - 3ε = (I-R)/2 > 0`。

6. **`M = Nat.ceil (Real.exp (nR))`** — 親 plan 主定理 statement にあわせる。

## 実装結果サマリ (2026-05-12 完全閉鎖時点)

- **行数**: 1890 行 (`Common2026/Shannon/ChannelCodingAchievability.lean`、初期 362 → +1528)。
- **`lake env lean`**: 0 error / 0 sorry / unused-variable 警告のみ。
- **完了範囲** (全段):
  - **Phase C-(a)** `Codebook` abbrev + `jointTypicalDecoder` + `codebookToCode` + `decode_eq_iff_unique`。
  - **Phase C-(b)** `errorProbAt_le_E1_plus_E2`: decoder error event ⊆ E1 ∪ ⋃ E2 を case analysis + `measureReal_biUnion_finset_le` で union bound。
  - **Phase C-(c)** `random_codebook_average_le` (probabilistic-method 形): `codebookMeasure p M n := Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => p))` を導入、LHS を `∑ codebook, (codebookMeasure p M n).real {codebook} * (averageErrorProb).toReal` 形に restate。仮説 `h_match_X` / `h_match_Z` / `hindepZ_full` で abstract ambient と codebook law を coupling。内部で 3 つの private 補題 (`block_law_X_eq_pi_p` / `block_law_Y_eq_pi` / `block_joint_law_eq_pi`) で `iIndepFun + IdentDistrib + h_match_*` → `Measure.pi` 化、Fubini-collapse 補題 `codebook_marginal_one` / `codebook_marginal_two` で per-row 平均、`random_codebook_E1_swap` / `_E2_swap` で E1 (true-codeword non-JTS) / E2 (alias-codeword JTS) の Fubini swap。E2 で `jointlyTypicalSet_indep_prob_le` 適用。
  - **Phase C-(d)** `exists_codebook_le_avg`: `codebookMeasure`-weighted Finset sum 上の pigeonhole (`sum_measureReal_singleton` + `Finset.sum_lt_sum` + classical contradiction)。
  - **Phase D-(a)** rate-slack 算術 (`ε := (I - R) / 6`、`R + 3ε < I`、`0 < I - R - 3ε`) + `N := max (max N₁ N₂) 1`。
  - **Phase D-(b)** `channel_coding_achievability` 主定理: `Common2026/Shannon/IIDProductInput.lean` の ready-made instance (`iidAmbientMeasure p W` + 全 `iIndepFun` / `IdentDistrib` / `μ.map = p` 等) を消費、`Common2026/Shannon/MIChainRule.lean` + `Common2026/Shannon/ChannelCoding.lean` 拡張の entropy-MI bridge (`mutualInfoOfChannel_eq_HX_add_HY_sub_HZ`) と `entropy_eq_of_identDistrib` を chain、E1 → 0 (`jointlyTypicalSet_prob_tendsto_one` + sandwich) + E2 → 0 (`Nat.ceil_lt_add_one` + `Real.tendsto_exp_neg_atTop_nhds_zero`)、最後に `random_codebook_average_le` + `exists_codebook_le_avg` で締め。channel positivity 仮説 `hW_pos : ∀ a y, 0 < (W a).real {y}` を signature に追加。
- **precursor (本 plan で新規追加)**:
  - `Common2026/Shannon/IIDProductInput.lean` (399 行、0 sorry): `Ω := ℕ → α × β` 上の `Measure.infinitePi (jointDistribution p W)` i.i.d. ambient bundle、`Function.eval i` の rfl-true 性質で `MeasurableEquiv` plumbing 不要、当初見積 ~150 行を 140 行で収まる。
  - `Common2026/Shannon/MIChainRule.lean` 拡張 (475 行、+57): joint-distribution 上の `mutualInfo_eq_entropy_add_entropy_sub_jointEntropy` を publish。
  - `Common2026/Shannon/ChannelCoding.lean` 拡張 (706 行、+47): channel-specialized `mutualInfoOfChannel_eq_mutualInfo_prod` + `mutualInfoOfChannel_eq_HX_add_HY_sub_HZ` を publish。
- **追加 signature 改変**:
  - 主定理 `channel_coding_achievability` に `hW_pos : ∀ a y, 0 < (W a).real {y}` 追加 (channel positivity)。
  - `random_codebook_E1_swap` / `random_codebook_average_le` に `hindepZ_full : iIndepFun (fun i : ℕ => jointSequence Xs Ys i) μ` 追加 (E1 swap が `block_joint_law_eq_pi` を消費するために mutual independence が必要)。
- **進行 (autonomous session 6 ラウンド)**:
  1. Phase C+D skeleton + C-(b) + C-(d) → 2 sorry。
  2. C-(c) probabilistic-method 形へ restate + C-(d) 再証明 + D-(b) 算術 → 2 sorry (statement 安定化)。
  3. precursor 2 本並列 (`MIChainRule.lean` 拡張 + `IIDProductInput.lean` 新規) → 主定理組立準備完了。
  4. D-(b) 主定理 close → 1 sorry (C-(c) Fubini body のみ)。
  5. C-(c) statement upgrade (`h_match_Z` 追加) + backbone proof + `block_law_*` × 3 + Fubini decomposition (E1 / E2 helpers) → 2 sorry (E1 / E2 isolated)。
  6. E2 swap close + E1 statement diagnosis (`hindepZ_full` 必要) → 1 sorry。
  7. E1 swap close via `hindepZ_full` mutation → **0 sorry**。

## Risk / Fallback

- **R1**: `Codebook` 上の sum と確率測度 (Phase C-(c) Fubini-like swap) の plumbing が
  想定より重くなる場合。Fallback: probabilistic method (cooperative measure-theoretic)
  に切り替え、`Measure.pi (fun _ : Fin M => p^n)` 上で期待値計算。
  **2026-05-12 実装中に発覚**: 当初 statement は uniform-on-codebook 形だったが、これは
  `p` が uniform でない限り不整合。R1 fallback (probabilistic method 形) が **本質的に必要**で、
  Phase C-(c) は restate 待ち。
- **R2**: `mutualInfoOfChannel` の reshape (`ℝ≥0∞` vs `ℝ`) plumbing。Fallback: 主定理を
  `entropy` 表示で書き直す。
- **R3**: `M = Nat.ceil (...)` の `Nat` ⊆ `ℝ` cast plumbing。Fallback (R4 と共通):
  `M := 2^{Nat.floor (n · R / Real.log 2)}` で `Nat.ceil` 回避。
- **R4**: scope 過大化時の縮小先。800 行超で `Nat.ceil` plumbing を簡略化。
- **R5**: i.i.d. plumbing が想定より厚い場合、別 file `IIDProductInput.lean` (~150 行)
  に分離 publish。
