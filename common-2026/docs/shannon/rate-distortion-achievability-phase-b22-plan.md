# E-3' Phase B.2.2 — `jointlyTypicalSet_indep_prob_ge` 実装計画

> Append site: end of `Common2026/Shannon/RateDistortionAchievabilityPhaseB.lean` (現状 479 行)

## Approach

`ChannelCoding.jointlyTypicalSet_indep_prob_le` (ChannelCoding.lean:573) の **anti-direction (lower bound)** mirror。

上界の証明戦略 (要約):
1. `(μX.prod μY).real JTS = ∑_{p∈JTS} μX{p.1}·μY{p.2}` (sum_measureReal_singleton)
2. 各 summand 上界: `typicalSet_prob_le` (X 軸, Y 軸) で `≤ exp(-n(HX-ε)) · exp(-n(HY-ε))`
3. `|JTS|` 上界: `jointlyTypicalSet_card_le` で `≤ exp(n(HZ+ε))`
4. 合成: `(μX.prod μY).real JTS ≤ |JTS|·C ≤ exp(n(HZ-HX-HY+3ε))`

Anti-direction (下界) では各 `≤` を `≥` に反転、point-wise lower (`typicalSet_prob_ge`)、size lower の **新規 helper** `jointlyTypicalSet_card_ge` が必要。

### 重要な signature 修正

Plan エージェント案の `hμJTS` は product-law の下界 `(μX.prod μY).real JTS ≥ 1-η` だったが、これでは circular。
正しい入力 hypothesis は **joint-law** 形:
`μ.real {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈ JTS} ≥ 1 - η`
これは `jointlyTypicalSet_prob_tendsto_one` (ChannelCoding.lean:402) が直接供給する形。

### `jointlyTypicalSet_card_ge` の証明 (正しい形)

1. `(1-η) ≤ μ.real {ω | (jX, jY) ∈ JTS}` (joint-law 仮説)
2. `= (μ.map (jointRV Zs n)).real (φ '' JTS)` where `φ : (x,y) ↦ fun i ↦ (x i, y i)` (injective)
3. `≤ Σ_{q∈φ''JTS} (μ.map jointRV Zs n).real {q}` (sum of singletons)
4. `≤ |φ''JTS| · exp(-n(HZ-ε))` via `typicalSet_prob_le` on Zs (φ(x,y) ∈ T_Z by JTS 3rd conjunct)
5. `= |JTS| · exp(-n(HZ-ε))` (φ injective)
→ `|JTS| ≥ (1-η) · exp(n(HZ-ε))`

### `jointlyTypicalSet_indep_prob_ge` の証明

1. `(μX.prod μY).real JTS = ∑_{p∈JTS} μX{p.1}·μY{p.2}` (sum_measureReal_singleton)
2. 各 summand 下界: `typicalSet_prob_ge` で `≥ exp(-n(HX+ε)) · exp(-n(HY+ε))` (JTS 1st/2nd conjuncts)
3. `|JTS|` 下界: 上の `_card_ge` で `≥ (1-η) · exp(n(HZ-ε))`
4. 合成: `≥ (1-η) · exp(n(HZ-HX-HY-3ε))`

## Phase 分解

| Step | LOC |
|------|-----|
| B.2.2.a-helper `jointlyTypicalSet_card_ge` (private) | ~40 |
| B.2.2.a `jointlyTypicalSet_indep_prob_ge` (publish) | ~60 |
| (B.2.2.b alias `single_codeword_typical_match_prob` — オプション) | ~10 |
| 合計 | **~110** |

## Skeleton

```lean
private lemma jointlyTypicalSet_card_ge
    [Nonempty α] [Nonempty β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepZ_full : iIndepFun (fun i => jointSequence Xs Ys i) μ)
    (hidentZ : ∀ i, IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    (hposZ : ∀ p : α × β, 0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    (n : ℕ) {ε η : ℝ} (hε : 0 < ε)
    (hμJTS : (1 - η) ≤ μ.real {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈
        jointlyTypicalSet μ Xs Ys n ε}) :
    (1 - η) * Real.exp ((n : ℝ) *
        (entropy μ (jointSequence Xs Ys 0) - ε))
      ≤ ((jointlyTypicalSet μ Xs Ys n ε).toFinite.toFinset.card : ℝ) := by
  sorry

theorem jointlyTypicalSet_indep_prob_ge
    [Nonempty α] [Nonempty β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX_full : iIndepFun (fun i => Xs i) μ)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY_full : iIndepFun (fun i => Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ_full : iIndepFun (fun i => jointSequence Xs Ys i) μ)
    (hidentZ : ∀ i, IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    (hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : α × β, 0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    (n : ℕ) {ε η : ℝ} (hε : 0 < ε)
    (hμJTS : (1 - η) ≤ μ.real {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈
        jointlyTypicalSet μ Xs Ys n ε}) :
    (1 - η) * Real.exp ((n : ℝ) *
        (entropy μ (jointSequence Xs Ys 0)
         - entropy μ (Xs 0) - entropy μ (Ys 0) - 3 * ε))
      ≤ ((μ.map (jointRV Xs n)).prod (μ.map (jointRV Ys n))).real
          (jointlyTypicalSet μ Xs Ys n ε) := by
  sorry
```

## リスク + 撤退ライン

- `_card_ge` の φ-image 化が複雑になる場合 → joint-law hypothesis を `(1-η)·exp(...) ≤ |JTS|` 形に **assumption pass-through** に変えて publish (consumer 側で派生)
- 行数 150 超 → 別ファイル `Common2026/Shannon/RateDistortionAchievabilityPhaseB22.lean` 切り出し
- 1 セッションで終わらなければ `_card_ge` のみ publish + `_indep_prob_ge` を次セッションへ

## Imports (追加不要)

既存の `RateDistortionAchievabilityPhaseB.lean` の imports で十分。

## Definition of Done

`lake env lean Common2026/Shannon/RateDistortionAchievabilityPhaseB.lean` clean、0 sorry、0 warning。
