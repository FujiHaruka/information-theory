# Slepian–Wolf Full Rate Region — Phase F inventory

> Scope: implement the missing final assembly headline
> `slepian_wolf_full_rate_region_achievability` in
> `Common2026/Shannon/SlepianWolfFullRateRegion.lean`.
> Parent plan: [`slepian-wolf-full-rate-region-plan.md`](slepian-wolf-full-rate-region-plan.md).
> Inventory only (2026-05-30).

## 一行サマリ

**Phase F の建材は ~95% 既存。真に未実装なのは E.5 (exp squeeze 集約) + F.3 (headline assembly) のみ。
新規 Mathlib 壁 0 件、撤退ライン発動 no。残実装 ~150–200 行。**

## 重大発見 0 — plan 状態表記が二重に stale

- plan `:25/:35/:500` は「`slepian_wolf_full_rate_region_achievability` (`:1956`) publish 済 / 127745 B / 0 sorry / 完全証明」と記載。
- **実コード**: file は **1902 行** (`:1956` 不在)。headline theorem は **どこにも declare されていない** (docstring `:1428` でロードマップ言及のみ)。
- 逆に plan が「これから書く」とする **F.1 / F.2 / bridge は既に実装済 (0 sorry)**:
  - F.1 `swErrorProb_total_expectation_le` (`:1455`)
  - F.2 `exists_pair_le_of_binning_integral_le` (`:1873`)
  - bridge `entropy_joint_sub_marginal_eq_condEntropy` (`:1442`)
- 残作業は plan 見積 (~230 行) より小、**E.5 squeeze + F.3 assembly + F.4 boundary(optional) のみ**。

## 既存 building-block の verbatim signature

namespace `InformationTheory.Shannon.ChannelCoding`、共通 variable block:
```
variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]
```

### `swErrorProb` (def) — `SlepianWolfAchievability.lean:57`, namespace `InformationTheory.Shannon`
```lean
noncomputable def swErrorProb
    (μ : Measure Ω) {n M_X M_Y : ℕ}
    (Xs : Ω → Fin n → α) (Ys : Ω → Fin n → β)
    (f_X : (Fin n → α) → Fin M_X) (f_Y : (Fin n → β) → Fin M_Y)
    (d : Fin M_X × Fin M_Y → (Fin n → α) × (Fin n → β)) : ℝ :=
  μ.real {ω | d (f_X (Xs ω), f_Y (Ys ω)) ≠ (Xs ω, Ys ω)}
```

### `swErrorProb_le_E0_plus_EX_plus_EY_plus_EXY` (Phase D) — `:140`
```lean
theorem swErrorProb_le_E0_plus_EX_plus_EY_plus_EXY
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    {n M_X M_Y : ℕ} (ε : ℝ)
    (f_X : (Fin n → α) → Fin M_X) (f_Y : (Fin n → β) → Fin M_Y) :
    swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
        (swJointTypicalDecoder μ Xs Ys ε f_X f_Y)
      ≤ μ.real (swError_E0 μ Xs Ys n ε) + μ.real (swError_EX μ Xs Ys n ε f_X)
        + μ.real (swError_EY μ Xs Ys n ε f_Y) + μ.real (swError_EXY μ Xs Ys n ε f_X f_Y)
```

### `swError_E0_prob_tendsto_zero` — `:293` (既に Tendsto 形、binning 非依存、pairwise indep)
```lean
theorem swError_E0_prob_tendsto_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j) (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY : Pairwise fun i j => Ys i ⟂ᵢ[μ] Ys j) (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ : Pairwise fun i j => jointSequence Xs Ys i ⟂ᵢ[μ] jointSequence Xs Ys j)
    (hidentZ : ∀ i, IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto (fun n : ℕ => μ.real (swError_E0 μ Xs Ys n ε)) Filter.atTop (𝓝 0)
```

### `swError_EX_expectation_le` — `:465` (RHS = `exp(n·(H(X,Y)−H(Y)+2ε))·M_X⁻¹`)
```lean
theorem swError_EX_expectation_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepY_full : iIndepFun (fun i => Ys i) μ) (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ_full : iIndepFun (fun i => jointSequence Xs Ys i) μ)
    (hidentZ : ∀ i, IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : α × β, 0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    {n M_X : ℕ} [NeZero M_X] {ε : ℝ} (hε : 0 < ε) :
    ∫ f_X, μ.real (swError_EX μ Xs Ys n ε f_X) ∂(binningMeasure α n M_X)
      ≤ Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) - entropy μ (Ys 0) + 2 * ε))
        * ((M_X : ℝ))⁻¹
```

### `swError_EY_expectation_le` — `:865` (RHS = `exp(n·(H(X,Y)−H(X)+2ε))·M_Y⁻¹`、対称、full iIndep X)

### `swError_EXY_strict_expectation_le` — `:1206` (RHS = `exp(n·(H(X,Y)+ε))·M_X⁻¹·M_Y⁻¹`、hposZ のみ)
```lean
theorem swError_EXY_strict_expectation_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hposZ : ∀ p : α × β, 0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    {n M_X M_Y : ℕ} [NeZero M_X] [NeZero M_Y] {ε : ℝ} (hε : 0 < ε) :
    ∫ f_X, ∫ f_Y, μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y)
          ∂(binningMeasure β n M_Y) ∂(binningMeasure α n M_X)
      ≤ Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) + ε)) * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹
```
注意: `swError_EXY` (loose) は `swError_EXY_subset_union:1044` で EX/EY に吸収。strict 版を使う。

### `binningMeasure` — `SlepianWolfBinning.lean:63` (Fintype 上 probability measure)
```lean
noncomputable def binningMeasure (α : Type*) [Fintype α] [MeasurableSpace α] (n M : ℕ) [NeZero M] :
    Measure ((Fin n → α) → Fin M) := Measure.pi (fun _ => uniformOn (Set.univ : Set (Fin M)))
instance binningMeasure.instIsProbabilityMeasure (n M : ℕ) [NeZero M] :
    IsProbabilityMeasure (binningMeasure α n M)
```

### F.1 total expectation (既存) — `:1455`
`swErrorProb_total_expectation_le` : decomposition + 4 bounds を 1 本にまとめた binning 上 total expectation bound (0 sorry)。

### F.2 pigeonhole (既存) — `:1873`
```lean
private lemma exists_pair_le_of_binning_integral_le
    {n M_X M_Y : ℕ} [NeZero M_X] [NeZero M_Y]
    (g : ((Fin n → α) → Fin M_X) → ((Fin n → β) → Fin M_Y) → ℝ)
    (hg_int_inner : ∀ f_X, Integrable (fun f_Y => g f_X f_Y) (binningMeasure β n M_Y))
    (hg_int_outer : Integrable (fun f_X => ∫ f_Y, g f_X f_Y ∂(binningMeasure β n M_Y))
        (binningMeasure α n M_X))
    {δ : ℝ}
    (hδ : ∫ f_X, ∫ f_Y, g f_X f_Y ∂(binningMeasure β n M_Y) ∂(binningMeasure α n M_X) ≤ δ) :
    ∃ f_X, ∃ f_Y, g f_X f_Y ≤ δ
```
(内部で `MeasureTheory.exists_le_integral` (`Mathlib/.../Average.lean:594`, `[IsProbabilityMeasure μ]` + `Integrable f μ`) を 2 回適用。)

## Phase F 用 Mathlib / Common2026 API

### 指数 squeeze
- `Real.tendsto_exp_neg_atTop_nhds_zero` (`Exp.lean:222`) : `Tendsto (fun x => exp (-x)) atTop (𝓝 0)`
- `squeeze_zero {f g : α → ℝ} (hf : ∀ t, 0 ≤ f t) (hft : ∀ t, f t ≤ g t) (g0 : Tendsto g t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 0)` (`Pseudo/Lemmas.lean:38`、ℝ 専用、`∀ t`)
- `tendsto_of_tendsto_of_tendsto_of_le_of_le'` (`Topology/Order/Basic.lean:219`、eventually 版 squeeze)

### rate parametrization (AEP.lean 既存)
```lean
noncomputable def codebookSize (R : ℝ) (n : ℕ) : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R))   -- :820
lemma codebookSize_pos (R : ℝ) (n : ℕ) : 0 < codebookSize R n                              -- :824
instance codebookSize_neZero (R : ℝ) (n : ℕ) : NeZero (codebookSize R n)                   -- :828
lemma codebookSize_log_div_tendsto {R : ℝ} (hR : 0 < R) :
    Tendsto (fun n : ℕ => Real.log (codebookSize R n : ℝ) / n) atTop (𝓝 R)                 -- :1023
```
`⌈exp(nR)⌉⁻¹ ≤ exp(−nR)` には `Nat.le_ceil` (= `exp(nR) ≤ ⌈·⌉`) + `inv_le_inv`。

### condEntropy chain rule / bridge / swap (Common2026 既存)
```lean
def MeasureFano.condEntropy (μ : Measure Ω) [IsFiniteMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) : ℝ  -- Fano/Measure.lean:69
theorem entropy_pair_eq_entropy_add_condEntropy (μ) [IsProbabilityMeasure μ] (Xs Yo) (hXs hYo) :
    entropy μ (fun ω => (Xs ω, Yo ω)) = entropy μ Xs + MeasureFano.condEntropy μ Yo Xs           -- Entropy.lean:43
private lemma entropy_joint_sub_marginal_eq_condEntropy (μ) [IsProbabilityMeasure μ] (X Y) (hX hY) :
    entropy μ (fun ω => (X ω, Y ω)) - entropy μ X = MeasureFano.condEntropy μ Y X                 -- SWFullRateRegion.lean:1442
theorem condEntropy_nonneg (μ) [IsProbabilityMeasure μ] (Ws Yo) : 0 ≤ MeasureFano.condEntropy μ Ws Yo  -- Pi.lean:108
lemma entropy_measurableEquiv_comp (μ) (Xs) (hXs) (e : β ≃ᵐ γ) :
    entropy μ (fun ω => e (Xs ω)) = entropy μ Xs                                                   -- Pi.lean:45
```
**swap 注意**: EY 指数 `H(X,Y)−H(X)` は bridge `X←Xs,Y←Ys` で直接 `= condEntropy μ (Ys 0)(Xs 0) = H(Y|X)`、swap 不要。
EX 指数 `H(X,Y)−H(Y)` を `condEntropy μ (Xs 0)(Ys 0) = H(X|Y)` に繋ぐには bridge を `X←Ys,Y←Xs` 適用後、
`entropy μ (fun ω => (Ys 0 ω, Xs 0 ω))` を `entropy μ (jointSequence Xs Ys 0)` に揃えるため
`entropy_measurableEquiv_comp` を `e := MeasurableEquiv.prodComm` で 1 回 (~5 行 plumbing、自作不要)。

### corner (boundary check, optional)
- plan の `slepian_wolf_achievability_corner_X/_corner_Y` は **不在**。実在は `slepian_wolf_achievability_via_Y_aep` (`SlepianWolfAchievability.lean:111`)。F.4 は core 非依存、名前修正 or 省略。

## 主要前提条件ボックス
- `exists_le_integral`: `[IsProbabilityMeasure μ]` + `Integrable f μ` (Fintype measure で自明だが F.3 で明示供給要)。`f : α → ℝ`。
- `codebookSize_log_div_tendsto`: **`0 < R`** 必須。`R_X > H(X|Y) ≥ 0` (`condEntropy_nonneg`) から 1 行。
- `entropy_pair_eq_entropy_add_condEntropy`: 結論 condEntropy は **`condEntropy μ Yo Xs`** (条件付け側 = 第 2 引数)。引数順取り違えで H(Y|X)↔H(X|Y) 反転。
- EX/EY/EXY: それぞれ `[NeZero M_X]`/`[NeZero M_Y]` (codebookSize_neZero で自動)。E0 は pairwise indep、EX/EY は full iIndep (`iIndepFun.indepFun` で pairwise derive)。

## 自作が必要な要素 (新 Mathlib 壁 0)
1. **E.5 squeeze 集約** (~50–80 行): expectation bound RHS に `M := codebookSize R` 代入 → `exp(−n·gap)` → `squeeze_zero` + `tendsto_exp_neg_atTop_nhds_zero`。EX 側 swap 込み。落とし穴: `⌈exp(nR)⌉⁻¹ ≤ exp(−nR)` の逆数化。
2. **F.3 headline assembly** (~80–100 行): `M_X := codebookSize R_X`、`M_Y := codebookSize R_Y`、`ε` を `min` で固定。`swErrorProb_total_expectation_le` → `exists_pair_le_of_binning_integral_le` で per-n 取り出し → E0-tendsto + 3 exp-squeeze の `Tendsto.add` で `Tendsto (swErrorProb → 0)`。落とし穴: F.2 の Integrable 供給、`∃ f_X f_Y` per-n の choice 関数化。
3. **F.4 boundary** (~30 行、optional): `via_Y_aep` 照合 or 省略。

## 撤退ライン
**発動 no** (pigeonhole/rate-param/bridge 全て既存、残りは pure 組立)。
新規撤退口 (縮退案): F.3 で `ε` の n-依存二重極限が必要と判明した場合のみ headline を `sorry + @residual(plan:slepian-wolf-phase-f)` で signature 保持して撤退、E.5 を先に genuine 完成。**headline の rate 仮説 `hRX/hRY/hRXY` は legitimate achievability hypothesis (達成可能性の前提)、load-bearing ではない。** 仮説束化禁止。

## 教訓
plan の状態表記 (DONE-UNCOND / `:1956` / 127745 B) が実コードと大きく乖離。CLAUDE.md「具体的数値・型予測の verbatim 確認」の実例 — orchestrator は F 着手前に実コードで headline 不在を確認すべき (確認済)。
