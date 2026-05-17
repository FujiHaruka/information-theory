# Rate-distortion achievability — E-3''' fully-discharged サブ計画

> **Parent**: [`rate-distortion-achievability-plan.md`](rate-distortion-achievability-plan.md) §Phase E (strong-typicality variant)
>
> **Status (起草 2026-05-18)**: Phase E (strong) は本体 `RateDistortionAchievabilityPhaseEStrong.lean` の Phases α–δ + ζ + η が完了 (980 LOC、1 sorry @ L890)。本サブ計画は **その 1 sorry — `codebookAvgFailure_tendsto_zero` — を閉じる** ことのみを目的とする。

## 進捗

- [ ] M0 在庫調査 — Cover-Thomas Lemma 10.6.1 用の strong-typical 条件 fiber-size 系の Mathlib gap 確定 📋
- [ ] Phase B' 経路選択 — `jointTypicalLossyEncoder` を strong-JTS 化するか並立か決定 📋
- [ ] Phase S1 — `conditionalStronglyTypicalSlice` 定義 + size lower bound 📋
- [ ] Phase S2 — `per_source_typical_match_prob_strong_ge` (Cover-Thomas 10.6.1 strong form) 📋
- [ ] Phase S3 — strong encoder + `jointlyTypicalSet_implies_distortionTypicalSet` ブリッジ 📋
- [ ] Phase S4 — `encoder_strong_failure_prob_le` (Phase C ミラー) 📋
- [ ] Phase S5 — `codebookAvgFailure_tendsto_zero` 最終組立 📋
- [ ] Phase S6 — `rate_distortion_achievability` の wrapper signature 整合 📋

## ゴール / Approach

### ゴール

`Common2026/Shannon/RateDistortionAchievabilityPhaseEStrong.lean:890` の単一 `sorry`:

```lean
lemma codebookAvgFailure_tendsto_zero
    (qStar : α × β → ℝ) (hqStar_simp : qStar ∈ stdSimplex ℝ (α × β))
    (d : DistortionFn α β)
    {R : ℝ} (_hI_lt_R : mutualInfoPmf qStar < R)
    (ε δ_typ : ℝ) (_hε_pos : 0 < ε) (_hδ_typ_nn : 0 ≤ δ_typ) :
    Filter.Tendsto
      (fun n : ℕ => codebookAvgFailure qStar d R n ε δ_typ)
      Filter.atTop (𝓝 0) := sorry
```

を閉じきり、E-3''' (Cover-Thomas Theorem 10.5 achievability、no-hypothesis form) を完成させる。

### Approach

**全体 shape**: Cover-Thomas 10.5 の random-coding 失敗確率分解を **strong-typicality 経路**で形式化する。`codebookAvgFailure n` を 2 つの bad events に分解し、それぞれ独立な極限定理に帰着させる:

1. **E1 (source X^n が strong-typical でない)**: `Pr[X^n ∉ A^*]`, `stronglyTypicalSet_prob_tendsto_one` の補集合で `→ 0`。
2. **E2 (source は strong-typical だが、どの codeword も jointly strong-typical でない)**: `Pr_C[∀ m, (x, c m) ∉ A^*_{XY}] ≤ (1 - p_typ_strong(x))^{M_n} ≤ exp(-M_n · exp(-n(I+δ)))`、`source_averaged_failure_tendsto_zero` (Phase D) で `→ 0`。
3. **E3 (E1∪E2 の外側では distortion-typical も保証される)**: strong-JTS encoder にすれば Phase γ (既存 `jointStronglyTypicalSet_implies_distortion_le`) で自動的に `(x, c(m)) ∈ distortionTypicalSet`。

**鍵となる中核**: per-source-typical-word の **strong-typical fiber match-probability lower bound** (Cover-Thomas Lemma 10.6.1 の strong form):

```
∀ x ∈ stronglyTypicalSet μ Xs n ε_X,
  Pr_Y[(x, Y) ∈ jointStronglyTypicalSet μ Xs Ys n ε]
    ≥ exp(-n · (mutualInfoPmf q* + δ(ε)))
```

これは `conditionalStronglyTypicalSlice` (新規) の **size lower bound** から導く。weak 版テンプレ `SlepianWolfConditionalTypicalSlice.lean` の size **upper** bound と双対 (mirror) 関係にあるが、**lower 側**は別物 (典型 fiber の確率質量を下から評価する必要)。本サブ計画は size lower bound + per-fiber 質量 lower bound の 2 段で組む。

**Encoder の Phase B' 決定**: 現行 `jointTypicalLossyEncoder` は weak JTS を targets するため、strong-JTS の per-x match probability bound (10.6.1 strong) と直接接続できない。**(b) 並立を採用** (詳細 §Phase B' で議論)。これにより既存 Phase B/C/D の weak chain を温存しつつ、Phase E (strong) 内に閉じた strong chain を新設できる。

### 経路の代替案と却下理由

1. **(却下) Phase B' = (a) in-place rewrite**: `jointTypicalLossyEncoder` 自身を strong-JTS 化。`distortionTypicalSet` の定義も連動して strong 版に置換する必要があり、`Phase B (RateDistortionAchievabilityPhaseB.lean 738 LOC)`, `Phase C (RateDistortionAchievabilityPhaseC.lean 422 LOC)`, `Phase D (RateDistortionAchievabilityPhaseD.lean 443 LOC)`, `Phase E discharge (RateDistortionAchievabilityPhaseEDischarge.lean ~340 LOC)` の全 consumer が連鎖破壊される。本サブ計画 1 ターンの予算 (500-800 LOC) に収まらず、E-3'' (weak 経路 partial-discharge 完了済み 764 LOC) の deliverable も壊す。
2. **(却下) Phase γ `jointStronglyTypicalSet_implies_distortion_le` を **weak** JTS から導く方向への弱化**: weak JTS は entropy 3 条件のみで empirical mean を含まないため不可。weak 経路では原理的に distortion bound が出ない (E-3'' の判断ログ #4 確認済)。
3. **(却下) Cover-Thomas 10.6.1 (strong) を skip し、`(1 - p_typ_weak)^M` を流用**: weak `p_typ` (jointly typical の indep probability) は `≥ exp(-n(I + 3ε))` (`jointlyTypicalSet_indep_prob_le` の dual) で取れるが、**`x` ごとの conditional bound** ではなく **(X, Y) joint distribution 上の bound**。これを `∫_x p_typ(x)^M ∂P_X` でなく `(P_X.prod p)(JTS)^M` に集約してしまうと Cover-Thomas 10.5 の (10.85) `M · (1 - p_typ)^M` 形が立たない (Jensen の向きで詰まる)。

### 規模見積

| Phase | 内訳 | 行数見積 |
|---|---|---|
| M0 | strong conditional fiber 関連 inventory | ~50 |
| Phase B' | strong encoder 並立 (`jointStronglyTypicalLossyEncoder`) | ~80 |
| Phase S1 | `conditionalStronglyTypicalSlice` 定義 + size lower bound | ~180 |
| Phase S2 | `per_source_typical_match_prob_strong_ge` (Cover-Thomas 10.6.1 strong) | ~150 |
| Phase S3 | strong encoder + `jointStronglyTypicalSet → distortionTypicalSet` bridge | ~80 |
| Phase S4 | `encoder_strong_failure_prob_le` (Phase C strong ミラー) | ~90 |
| Phase S5 | `codebookAvgFailure_tendsto_zero` 最終組立 | ~80 |
| Phase S6 | `rate_distortion_achievability` の wrapper 整合 (encoder swap) | ~30 |
| precursor (Mathlib gap が出た場合) | (整数 ↔ ℝ 変換、`Real.exp_neg` 系) | ~30 |
| **合計** | | **~770** |

予算 (500-800 LOC) の上限近辺。Phase S2 が予想以上に膨らんだ場合は Phase S1 を **upper bound のみ** に縮退させ、lower bound は `stronglyTypicalSet_card_ge_eventually` + per-fiber 質量 lower bound の直接組立で書く (size lower bound の精緻な統制を回避、+30 LOC ペナルティで)。

## Phase 詳細

### M0 — 在庫調査

- [ ] M0.1 loogle で **strong-conditional fiber size** 系の既存 lemma 探索:
  - クエリ: `MeasureTheory.Set.Finite.toFinset.card, stronglyTypicalSet`
  - クエリ: `conditionalStronglyTypicalSlice` (まず存在しない想定)
  - クエリ: `Real.exp (- _ * _) ≤ _.real _` (per-fiber 質量下界 prior)
- [ ] M0.2 `SlepianWolfConditionalTypicalSlice.lean` (411 LOC) の **upper bound** proof structure を読み、strong 版 lower bound の dual proof shape を計画 (X-axis prob lower bound (`typicalSet_prob_ge`) + Y-axis prob upper bound (`typicalSet_prob_le`) の符号反転)。
- [ ] M0.3 `jointStronglyTypicalSet_indep_prob_ge` (`RateDistortionAchievabilityPhaseEStrong.lean:552`) の signature と仮定セットを再確認: これは **(P_X, P_Y) 独立 product** 上の下界。**条件付き**版 (`x` 固定で `Y` だけ random) には流用できない (Phase S2 で別途構築)。

#### M0 で確認したい既存 API (構造化形式)

- `stronglyTypicalSet_card_ge_eventually` — `Common2026/Shannon/StrongTypicality.lean:503`:
  - sig: `(μ : Measure Ω) (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (hindep_full : iIndepFun (fun i => Xs i) μ) (hindep_pair : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j) (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (hpos : ∀ a : α, 0 < (μ.map (Xs 0)).real {a}) {ε δ η : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hη : 0 < η) : ∃ N : ℕ, ∀ n ≥ N, (1 - η) * Real.exp ((n : ℝ) * (entropy μ (Xs 0) - ε * logSumAbs μ Xs - δ)) ≤ ((stronglyTypicalSet μ Xs n ε).toFinite.toFinset.card : ℝ)`
  - 用途: Phase S1 で `α × β` 軸 (joint sequence) に instantiate して conditional slice の **lower envelope**
- `typicalSet_prob_ge` — `Common2026/Shannon/AEP.lean:1403`:
  - sig: `(μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (hindep_full : iIndepFun (fun i => Xs i) μ) (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (hpos : ∀ a : α, 0 < (μ.map (Xs 0)).real {a}) (n : ℕ) (x : Fin n → α) (hx : x ∈ typicalSet μ Xs n ε) : Real.exp (-(n : ℝ) * (entropy μ (Xs 0) + ε)) ≤ (μ.map (jointRV Xs n)).real {x}`
  - 用途: Phase S2 per-fiber 質量 lower bound (Y 側)
- `typicalSet_prob_le` — `Common2026/Shannon/AEP.lean:1279`:
  - sig: `(μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (hindep_full : iIndepFun (fun i => Xs i) μ) (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (hpos : ∀ a : α, 0 < (μ.map (Xs 0)).real {a}) (n : ℕ) (x : Fin n → α) (hx : x ∈ typicalSet μ Xs n ε) : (μ.map (jointRV Xs n)).real {x} ≤ Real.exp (-(n : ℝ) * (entropy μ (Xs 0) - ε))`
  - 用途: Phase S1 conditional slice の per-fiber 上界 (X 側、scaling factor 用)
- `jointStronglyTypicalSet_implies_distortion_le` — `Common2026/Shannon/RateDistortionAchievabilityPhaseEStrong.lean:282`:
  - sig: `(μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (d : DistortionFn α β) {n : ℕ} {ε δ : ℝ} (hε : 0 ≤ ε) (h_slack : ε * ∑ p : α × β, ((d p.1 p.2 : NNReal) : ℝ) ≤ δ) (x : Fin n → α) (y : Fin n → β) (hxy : (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε) : blockDistortion d n x y ≤ expectedDistortionPmf d (fun p => (μ.map (jointSequence Xs Ys 0)).real {p}) + δ`
  - 用途: Phase S3、strong encoder の choice が distortionTypicalSet に入ることを示す
- `stronglyTypicalSet_prob_tendsto_one` — `Common2026/Shannon/StrongTypicality.lean:212`:
  - sig: `(μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j) (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) {ε : ℝ} (hε : 0 < ε) : Tendsto (fun n : ℕ => μ {ω | jointRV Xs n ω ∈ stronglyTypicalSet μ Xs n ε}) atTop (𝓝 1)`
  - 用途: Phase S5 で `Pr[X^n ∉ A^*] → 0`
- `source_averaged_failure_tendsto_zero` — `Common2026/Shannon/RateDistortionAchievabilityPhaseD.lean:102`:
  - sig: `(θ R η : ℝ) (hRθ : θ < R) (hη_pos : 0 < η) (hη_lt : η < 1) (hθ_nn : 0 ≤ θ) (M : ℕ → ℕ) (hM_lb : ∀ n : ℕ, Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M n) (failure_seq : ℕ → ℝ) (h_failure_le : ∀ n : ℕ, failure_seq n ≤ Real.exp (-(M n : ℝ) * ((1 - η) * Real.exp (-(n : ℝ) * θ)))) (h_failure_nn : ∀ n : ℕ, 0 ≤ failure_seq n) : Filter.Tendsto failure_seq Filter.atTop (𝓝 0)`
  - 用途: Phase S5 主たる asymptotic 詰め。`θ := mutualInfoPmf qStar + δ`、`R := R` のまま、`M := M_n`、`failure_seq n := source-typical 上の E2 failure`
- `one_sub_pow_le_exp_neg_mul` — `Common2026/Shannon/RateDistortionAchievabilityPhaseC.lean:121`:
  - sig: `(M : ℕ) {t : ℝ} (_h0 : 0 ≤ t) (h1 : t ≤ 1) : (1 - t) ^ M ≤ Real.exp (-(M : ℝ) * t)`
  - 用途: Phase S4 で per-codeword failure prob → exp 形

### Phase B' — Encoder shape 決定 (採用: 並立 (b))

**判断**: `jointTypicalLossyEncoder` の **in-place 改修 (a)** ではなく **strong 版を並立 (b)** で追加する。

**理由**:
- (a) は Phase B (738 LOC), C (422 LOC), D (443 LOC), E discharge (~340 LOC) の **全 consumer** を連鎖破壊し、E-3'' で publish 済 partial-discharge 主定理を巻き戻す。本サブ計画予算 (500-800 LOC) を遥かに超える。
- (b) は **新 encoder `jointStronglyTypicalLossyEncoder` を `RateDistortionAchievabilityPhaseEStrong.lean` 内に追加**、既存 weak encoder は無改変。E discharge wrapper (`RateDistortionAchievabilityPhaseEDischarge.lean`) は元々 hypothesis 形 (`failure_seq + h_failure_le + h_codebook_avg_failure`) で書かれているので、Phase S6 で **strong encoder 版の hypothesis discharge** を別途差し込めばよい。
- 弊害: encoder の重複 ~80 LOC + `lossyCodeOfCodebook` の strong 版 ~10 LOC + 後段 wrapper の swap ~30 LOC = ~120 LOC のコード duplication。本サブ計画予算内。

**実装**: `RateDistortionAchievabilityPhaseEStrong.lean` 内に追加。

```lean
/-- **Strong-JTS lossy encoder** (Phase B' 並立 strong 版). 既存 weak `jointTypicalLossyEncoder`
と signature は同じ、ターゲットだけ `jointStronglyTypicalSet`。 -/
noncomputable def jointStronglyTypicalLossyEncoder
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (c : Codebook M n β) :
    (Fin n → α) → Fin M := fun x =>
  haveI : Decidable (∃ m : Fin M, (x, c m) ∈ jointStronglyTypicalSet μ Xs Ys n ε) :=
    Classical.propDecidable _
  if h : ∃ m : Fin M, (x, c m) ∈ jointStronglyTypicalSet μ Xs Ys n ε
    then Classical.choose h
    else ⟨0, hM⟩

noncomputable def stronglyJointTypicalLossyCode ... : LossyCode M n α β where
  encoder := jointStronglyTypicalLossyEncoder μ Xs Ys hM ε c
  decoder := c

theorem jointStronglyTypicalLossyEncoder_spec_of_exists ...
theorem jointStronglyTypicalLossyEncoder_spec_of_not_exists ...
```

ステップ:
- [ ] B'.1 `jointStronglyTypicalLossyEncoder` definition + 2 spec lemma (~50 LOC)
- [ ] B'.2 `stronglyJointTypicalLossyCode` bundle (~10 LOC)
- [ ] B'.3 spec lemma `jointStronglyTypicalLossyEncoder_image_mem_jointStronglyTypicalSet_of_exists`: `(x, c (jointStronglyTypicalLossyEncoder ... x)) ∈ jointStronglyTypicalSet` if exists branch (~20 LOC)

**注**: `codebookAvgFailure` (現行 L797、weak encoder を参照) は **そのまま残す** (E-3'' partial-discharge wrapper 整合)。S5 では新規 `codebookAvgFailure_strong` を定義し、現行 `codebookAvgFailure_tendsto_zero` は **strong 版を経由してから weak ≤ strong の domination で discharge** する (詳細 §Phase S5)。

### Phase S1 — Conditional strongly typical slice + size lower bound

**ゴール**: 与えられた source word `x ∈ stronglyTypicalSet μ Xs n ε_X` に対し、`x` を一方の軸に固定した joint strong-typical fiber

```
F_x := { y : Fin n → β | (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε }
```

の **size lower bound**:

```
|F_x| ≥ exp(n · (H(X, Y) - H(X) - ε · L_X - 2 · ε · L_Z - δ))
     ≈ exp(n · (H(Y|X) - δ'))  (chain rule、symbolic)
```

を確立する。`SlepianWolfConditionalTypicalSlice.lean` の upper bound と双対の lower-bound 版。

#### S1 設計上の決定

`SlepianWolfConditionalTypicalSlice` は upper bound のみで、proof shape は「per-fiber 質量 lower bound (`typicalSet_prob_ge` Z 側) + total 確率 upper bound (`typicalSet_prob_le` Y 側)」。本 Phase S1 は **逆向き**: per-fiber 質量 upper bound (`typicalSet_prob_le` Z 側) + total 確率 lower bound (`typicalSet_prob_ge` Y 側)。

ステップ:
- [ ] S1.1 `conditionalStronglyTypicalSlice` 定義 (~15 LOC):
  ```lean
  noncomputable def conditionalStronglyTypicalSlice
      (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (n : ℕ) (ε : ℝ)
      (x : Fin n → α) : Set (Fin n → β) :=
    { y | (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε }
  ```
- [ ] S1.2 basic structure: `_finite` / `MeasurableSet` (~10 LOC)
- [ ] S1.3 補題: `x ∉ stronglyTypicalSet (with widened slack) ⟹ conditionalStronglyTypicalSlice = ∅` (~20 LOC、`jointStronglyTypicalSet_implies_X_stronglyTypical` from L374 を縮約)
- [ ] S1.4 **per-fiber 質量 upper bound** (Z 軸): for `y ∈ conditionalStronglyTypicalSlice μ Xs Ys n ε x`, `(μ.map (jointRV (jointSequence Xs Ys) n)).real {(fun i => (x i, y i))} ≤ exp(-n · (H(Z) - ε · L_Z))` via `typicalSet_prob_le` (`stronglyTypicalSet ⊆ typicalSet` from `stronglyTypicalSet_subset_typicalSet` at L437) (~30 LOC)
- [ ] S1.5 **total 確率 lower bound** (X 軸固定で y を ranging): Pr_Y `[(x, Y^n) ∈ jointStronglyTypicalSet]` を `μ.map (jointRV Ys n)` 上 で `y` 範囲 sum、それを `typicalSet_prob_ge` 経由で下から評価 — ただし「X 軸固定で `y` だけ random」は (X, Y) 独立 product 上の積分の section、`Measure.prod_apply` で `∫ Pr[Y ∈ slice_x] dP_X` から逆向きに取り出す必要あり (~40 LOC)。Phase S2 main lemma のスコープにずらしても良い。
- [ ] S1.6 **size lower bound** (sum 形): `|F_x| ≥ Pr_Y[(x, Y) ∈ JTS^*] / max-per-fiber-mass`、上で取った upper bound と lower bound を組合せて (~65 LOC):
  ```lean
  theorem conditionalStronglyTypicalSlice_card_ge
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
      (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
      (hindepX_full : iIndepFun Xs μ) (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
      (hindepY_full : iIndepFun Ys μ) (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
      (hindepZ_full : iIndepFun (jointSequence Xs Ys) μ)
      (hidentZ : ∀ i, IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
      (hposX : ∀ a, 0 < (μ.map (Xs 0)).real {a})
      (hposY : ∀ b, 0 < (μ.map (Ys 0)).real {b})
      (hposZ : ∀ p, 0 < (μ.map (jointSequence Xs Ys 0)).real {p})
      (hmarg_X : (μ.map (jointSequence Xs Ys 0)).map Prod.fst = μ.map (Xs 0))
      (hmarg_Y : (μ.map (jointSequence Xs Ys 0)).map Prod.snd = μ.map (Ys 0))
      {ε δ η : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hη : 0 < η) :
      ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ stronglyTypicalSet μ Xs n ε,
        (1 - η) * Real.exp ((n : ℝ) *
          ((entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0))
           - (ε * logSumAbs μ Xs + ε * logSumAbs μ (jointSequence Xs Ys) + 2 * δ)))
          ≤ ((conditionalStronglyTypicalSlice μ Xs Ys n ε x).toFinite.toFinset.card : ℝ)
  ```

### Phase S2 — `per_source_typical_match_prob_strong_ge` (Cover-Thomas 10.6.1 strong)

**ゴール**: per-source-typical-word strong-JTS match probability lower bound:

```
∀ x ∈ stronglyTypicalSet μ Xs n ε_X,
  (Measure.pi (fun _ : Fin n => μ.map (Ys 0))).real
    { y | (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε }
  ≥ exp(-n · (mutualInfoPmf qStar + δ(ε)))
```

ここで `qStar := fun (a, b) => (μ.map (jointSequence Xs Ys 0)).real {(a, b)}` (joint pmf)。

#### 設計の核心

Cover-Thomas Lemma 10.6.1 (strong form): `Pr_Y[fiber] ≥ |F_x| · min-per-fiber-Y-mass`。
- `|F_x|`: Phase S1.6 で確立、`≥ (1-η) exp(n(H(Y|X) - δ_1))`
- `min-per-fiber-Y-mass`: `y` が `F_x` に入るなら `y ∈ stronglyTypicalSet μ Ys n (|α|·ε)` (Phase E δ.2 既存 `jointStronglyTypicalSet_implies_Y_stronglyTypical` L457)、よって `Pr[Y^n = y] ≥ exp(-n(H(Y) + |α|·ε·L_Y + δ_2))` (`typicalSet_prob_ge`)
- 積: `(1-η) exp(n(H(Y|X) - δ_1 - H(Y) - |α|·ε·L_Y - δ_2)) = (1-η) exp(-n · (H(Y) - H(Y|X) + δ_3)) = (1-η) exp(-n · (I(X;Y) + δ_3))`、chain rule の **textbook 形** `H(Y|X) := H(X,Y) - H(X)` を使えば指数部が `mutualInfoPmf qStar + δ_3` に書ける。
- ここで `mutualInfoPmf qStar = H(X) + H(Y) - H(X,Y)` の **entropy 形** (`RateDistortionAchievability.lean:261`) と `H(Y) - H(Y|X) = I(X;Y)` が一致することは pmf 形定義の即時帰結 (ring identity)。

ステップ:
- [ ] S2.1 補題: `y ∈ conditionalStronglyTypicalSlice μ Xs Ys n ε x ⟹ y ∈ stronglyTypicalSet μ Ys n (|α|·ε)` (Phase E δ.2 既存 L457 を縮約) (~20 LOC)
- [ ] S2.2 per-fiber Y-mass lower bound: `y ∈ slice ⟹ (Measure.pi (μ.map (Ys 0))).real {y} ≥ exp(-n(H(Y) + |α|·ε·L_Y + δ))` (`typicalSet_prob_ge` 経由) (~25 LOC)
- [ ] S2.3 sum lower bound (fiber size × per-fiber mass): (~40 LOC)
- [ ] S2.4 entropy ↔ mutualInfoPmf bridge: `H(Y) - (H(X,Y) - H(X)) = H(X) + H(Y) - H(X,Y) = mutualInfoPmf qStar` (ring + pmf 定義 unfold) (~20 LOC)
- [ ] S2.5 主補題 `per_source_typical_match_prob_strong_ge`:
  ```lean
  theorem per_source_typical_match_prob_strong_ge
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
      ... (hindep_*, hident_*, hpos_*, hmarg_*)
      {ε δ η : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hη : 0 < η) :
      ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ stronglyTypicalSet μ Xs n ε,
        (1 - η) * Real.exp (-(n : ℝ) *
          (mutualInfoPmf (fun p => (μ.map (jointSequence Xs Ys 0)).real {p})
           + δ_total ε δ))
          ≤ (Measure.pi (fun _ : Fin n => μ.map (Ys 0))).real
              { y | (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε }
  ```
  where `δ_total ε δ` は (a) `ε · L_X`、(b) `|α| · ε · L_Y`、(c) `ε · L_Z`、(d) `2 · δ` の和。最後の `δ → 0` 統合は Phase S5 で行う。 (~45 LOC)

### Phase S3 — Strong encoder + distortionTypicalSet ブリッジ

**ゴール**: strong encoder の出力が distortionTypicalSet に入ることを示す:

```
If ∃ m, (x, c m) ∈ jointStronglyTypicalSet μ Xs Ys n ε
  ∧ ε · Σ_{(a,b)} d(a,b) ≤ δ_typ
  ∧ μ.map (jointSequence Xs Ys 0) marginal が source の P_X と一致,
then (x, c (jointStronglyTypicalLossyEncoder ... x)) ∈ distortionTypicalSet μ Xs Ys d n ε δ_typ
```

ステップ:
- [ ] S3.1 補題: `(x, c m) ∈ jointStronglyTypicalSet ⟹ (x, c m) ∈ jointlyTypicalSet (with widened slack)` (`jointStronglyTypicalSet_joint_axis_subset` 既存 L111 を Lifted to weak JTS 経由 OR 直接 Phase α membership iff から) (~20 LOC)
- [ ] S3.2 主ブリッジ `jointStronglyTypicalSet_implies_mem_distortionTypicalSet`:
  ```lean
  theorem jointStronglyTypicalSet_implies_mem_distortionTypicalSet
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
      (d : DistortionFn α β) {n : ℕ} {ε δ_typ : ℝ}
      (hε_pos : 0 < ε)
      (h_slack : ε * ∑ p : α × β, ((d p.1 p.2 : NNReal) : ℝ) ≤ δ_typ)
      (h_bridge : expectedDistortionPmf d
          (fun p => (μ.map (jointSequence Xs Ys 0)).real {p})
        = expectedJointDistortion μ (Xs 0) (Ys 0) d)
      (x : Fin n → α) (y : Fin n → β)
      (hxy_strong : (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε)
      (hxy_weak : (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε) :
      (x, y) ∈ distortionTypicalSet μ Xs Ys d n ε δ_typ
  ```
  証明: `mem_distortionTypicalSet_iff` を分解、weak 側は `hxy_weak`、distortion side は `jointStronglyTypicalSet_implies_distortion_le` L282 から `blockDistortion ≤ expectedDistortionPmf + δ_typ` を取り、`h_bridge` で `expectedJointDistortion + δ_typ` に書き換え。 (~45 LOC)
- [ ] S3.3 spec for strong encoder の自動 `distortionTypicalSet` 達成: combine B'.3 + S3.2 (~15 LOC)

### Phase S4 — `encoder_strong_failure_prob_le` (Phase C strong ミラー)

**ゴール**: Phase C `encoder_failure_prob_le_exp_neg_M_avg` (weak 版) の strong-typical 上での per-x conditional 版:

```
∀ x ∈ stronglyTypicalSet, ∀ n ≥ N,
  (codebookMeasure (μ.map (Ys 0)) M_n n).real
    { c | ∀ m, (x, c m) ∉ jointStronglyTypicalSet μ Xs Ys n ε }
  ≤ exp(-M_n · (1 - η) · exp(-n · (mutualInfoPmf qStar + δ_total)))
```

ステップ:
- [ ] S4.1 per-source-typical match-no event の **per-codeword 独立性 + Fubini**: Phase C `codebook_indep_no_match_prob_eq` (~5 LOC を strong 版に simp で書き換え)
- [ ] S4.2 `(1 - p_typ_strong(x))^M ≤ exp(-M · p_typ_strong(x))` (`one_sub_pow_le_exp_neg_mul` 直流用) (~10 LOC)
- [ ] S4.3 per-source-typical x への lower bound 噛ませ (S2.5 + S4.1 + S4.2 + 単調性): (~35 LOC)
- [ ] S4.4 source-typical 集合上での integration:
  ```lean
  theorem encoder_strong_failure_prob_le
      ...
      ∃ N, ∀ n ≥ N,
        (Measure.pi (fun _ : Fin n => μ.map (Xs 0))).real
            ({ x | x ∈ stronglyTypicalSet μ Xs n ε } ∩
             { x | ... strong-JTS-no-match event ... })
        ≤ Real.exp (-(M_n n : ℝ) * ((1 - η) * Real.exp (-(n : ℝ) *
            (mutualInfoPmf qStar + δ_total))))
  ```
  証明: integrand を per-x pointwise bound (S4.3) で押さえ、`integral_mono` + `integral_const` で右辺 sup へ。`stronglyTypicalSet` 上以外を indicator 0 にする (~40 LOC)

### Phase S5 — `codebookAvgFailure_tendsto_zero` 最終組立

**ゴール**: 既存 sorry を閉じる。

#### 戦略

現行 `codebookAvgFailure` は **weak encoder** を参照しているため、直接 strong 版に乗せ替えはできない。代わりに:

(α) **domination**: weak encoder の failure ≤ strong encoder の failure (with appropriate slack) を示し、後者の `→ 0` を経由する。
    - **問題**: weak encoder の failure event は `(x, c (weak-encoder x)) ∉ distortionTypicalSet`。weak encoder は jointly-typical (weak) match を選ぶが、これは empirical distortion 制御を含まないため、たまたま選んだ weak-JTS の `(x, c m)` で `blockDistortion` がはみ出す可能性あり (= weak encoder の固有失敗)。
    - **解**: `codebookAvgFailure (weak encoder で定義) ≤ Pr[X ∉ A^*_typ_X] + Pr[X ∈ A^*_typ_X ∧ strong-encoder fails]` を示す。後者は **strong encoder が成功すれば weak encoder も distortion-typical を取れる** という structural な事実から、`weak encoder fails ⟹ strong encoder fails (with widened ε)` を obtain。

(β) **clean rewrite**: 新規 `codebookAvgFailure_strong` を定義し、現行 `codebookAvgFailure_tendsto_zero` proof は `codebookAvgFailure ≤ codebookAvgFailure_strong (with widened ε)` から conclude。

**採用: (β)** — domination proof のほうがクリーン。`codebookAvgFailure_strong` は Phase S4 出力を直接組合せれば bound できる。`codebookAvgFailure ≤ codebookAvgFailure_strong (with widened ε)` の証明は **encoder 選択の存在性ベース** (strong-JTS match があれば weak-JTS match もあり、weak encoder はその match を取る可能性も含めて少なくとも 1 つ選ぶ、その distortion は strong → distortionTypicalSet ⊆ weak-distortionTypicalSet) で 1 段。

ステップ:
- [ ] S5.1 `codebookAvgFailure_strong` 定義 (weak `codebookAvgFailure` の encoder 部分のみ swap、distortionTypicalSet 判定はそのまま再利用) (~15 LOC)
- [ ] S5.2 補題 `codebookAvgFailure_le_codebookAvgFailure_strong`: weak の failure event は strong の failure event を含む (encoder の choice が異なってもどちらかの match があれば成功する側、ない側、両方を 1 つの implication で繋ぐ) (~25 LOC)
- [ ] S5.3 `codebookAvgFailure_strong ≤ Pr[X ∉ A^*] + encoder_strong_failure_prob`: (~15 LOC、E1 + E2 decomp)
- [ ] S5.4 `Pr[X ∉ A^*] → 0`: `stronglyTypicalSet_prob_tendsto_one` の補集合化 + `IsProbabilityMeasure.complement` (~10 LOC)
- [ ] S5.5 `encoder_strong_failure_prob → 0`: `source_averaged_failure_tendsto_zero` 直適用、`θ := mutualInfoPmf qStar + δ_total`、`R` のまま、`M_n := Nat.ceil (Real.exp (n * R))`。仮定 `θ < R` は `δ_total` を `(R - mutualInfoPmf qStar) / 2` 以下に取れば成立。 (~15 LOC)
- [ ] S5.6 sum (`Filter.Tendsto.add` で 0 + 0 = 0) + domination で sorry を閉じる (~10 LOC)

```lean
-- Final closure shape:
lemma codebookAvgFailure_tendsto_zero ... : Tendsto (fun n => codebookAvgFailure ... n) atTop (𝓝 0) := by
  -- (1) Choose `ε_S := ε / (3 * (1 + L_X + |α|·L_Y + L_Z))` ≤ ε to ensure
  --     `δ_total ε_S δ_S < (R - mutualInfoPmf qStar) / 2`.
  -- (2) Apply `codebookAvgFailure_le_codebookAvgFailure_strong` (S5.2).
  -- (3) Apply `codebookAvgFailure_strong ≤ Pr[X ∉ A^*] + encoder_strong_failure_prob` (S5.3).
  -- (4) `Pr[X ∉ A^*] → 0` (S5.4) + `encoder_strong_failure_prob → 0` (S5.5).
  -- (5) `Filter.Tendsto.add` + squeeze.
```

### Phase S6 — Wrapper signature 整合

**ゴール**: `rate_distortion_achievability` (現行 L918) は `codebookAvgFailure_tendsto_zero` を呼ぶだけなので、signature 変更なし。S5 が closed なら自動完成。

ただし以下を verify:
- [ ] S6.1 `rate_distortion_achievability` の `_hε_pos` / `_hδ_typ_nn` 仮定が S5 で要求する仮定セット (`hindep_*`, `hident_*`, `hpos_*`, `hmarg_*`) と適合するかを再確認。**現行 `_hε_pos : 0 < ε` のみ**で、S5 が要求する大量の structural 仮定 (X/Y/Z の `iIndepFun`, `IdentDistrib`, full support, marginal match) は `codebookAvgFailure_tendsto_zero` の signature に追加する必要あり。**これは現行 sorry の signature 改修となる** (E-3'' の partial-discharge wrapper も追加 hypothesis を要求していたので、同型の改修が `rate_distortion_achievability_partial_discharge` 内に既にある可能性高 — Phase S6 で要 verify)。
- [ ] S6.2 `rate_distortion_achievability` 呼び出し側 (`RateDistortionAchievabilityPhaseEDischarge.lean` の `rate_distortion_achievability_partial_discharge`) で structural hypothesis を `rdAmbient` 上で discharge 済か再確認。済なら本サブ計画内で追加 instance/hypothesis bridge は不要。

## File layout

**全変更を `Common2026/Shannon/RateDistortionAchievabilityPhaseEStrong.lean` に追加** (現行 980 LOC → 推定 1750 LOC):

- 既存 Phase α-ζ-η はそのまま (980 LOC)
- Phase B' (~80 LOC) を Phase ε の直前に挿入
- Phase S1-S2 (~330 LOC) を Phase δ の後 (現行 L552-770 の `jointStronglyTypicalSet_indep_prob_ge` の直後) に挿入
- Phase S3 (~80 LOC) を Phase γ の後 / B' の前あたり
- Phase S4 (~90 LOC) を Phase ε `codebookAvgFailure` 定義の直後
- Phase S5 (~80 LOC) は現行 L879 の sorry 本体を置換
- Phase S6 (~30 LOC) は必要に応じて signature 改修
- 合計 +770 LOC、最終 ~1750 LOC

**新規ファイルを切らない理由**:
- (α) Phase B' 並立 encoder と Phase α-η の definitions が密結合 (`jointStronglyTypicalSet`, `expectedDistortionPmf`, `codebookAvgFailure` 全部同 file)。
- (β) `StrongTypicality.lean` を joint 化する一般化は本サブ計画スコープ外 (E-3''' 1 sorry にしか効かないため overhead 大、E-5 強形に汎化する場合は別 plan)。
- (γ) `SlepianWolfConditionalTypicalSlice.lean` (411 LOC) の dual file `SlepianWolfConditionalStronglyTypicalSlice.lean` を切る案は overkill — 単一 fiber size lower bound は ~180 LOC で本 file 内 inline で十分。
- (δ) ファイル単体 1750 LOC は ChannelCodingAchievability (1890) より小さく、`lake env lean` で許容範囲。

**`StrongTypicality.lean` への追加は最小限** (Phase S1.1 の `conditionalStronglyTypicalSlice` 定義は `RateDistortionAchievabilityPhaseEStrong.lean` 内に置く、後でリファクタが必要なら別 plan に切り出す)。

## Mathlib API needed

**既存 Common2026 (流用)**:
- `Common2026/Shannon/StrongTypicality.lean:212` `stronglyTypicalSet_prob_tendsto_one`
- `Common2026/Shannon/StrongTypicality.lean:437` `stronglyTypicalSet_subset_typicalSet`
- `Common2026/Shannon/StrongTypicality.lean:456` `stronglyTypicalSet_card_le`
- `Common2026/Shannon/StrongTypicality.lean:503` `stronglyTypicalSet_card_ge_eventually`
- `Common2026/Shannon/AEP.lean:1279` `typicalSet_prob_le`
- `Common2026/Shannon/AEP.lean:1403` `typicalSet_prob_ge`
- `Common2026/Shannon/RateDistortionAchievabilityPhaseEStrong.lean:111` `jointStronglyTypicalSet_joint_axis_subset`
- `Common2026/Shannon/RateDistortionAchievabilityPhaseEStrong.lean:132` `jointStronglyTypicalSet_prob_tendsto_one`
- `Common2026/Shannon/RateDistortionAchievabilityPhaseEStrong.lean:282` `jointStronglyTypicalSet_implies_distortion_le`
- `Common2026/Shannon/RateDistortionAchievabilityPhaseEStrong.lean:374` `jointStronglyTypicalSet_implies_X_stronglyTypical`
- `Common2026/Shannon/RateDistortionAchievabilityPhaseEStrong.lean:457` `jointStronglyTypicalSet_implies_Y_stronglyTypical`
- `Common2026/Shannon/RateDistortionAchievabilityPhaseB.lean:115` `distortionTypicalSet` (定義 + iff)
- `Common2026/Shannon/RateDistortionAchievabilityPhaseC.lean:121` `one_sub_pow_le_exp_neg_mul`
- `Common2026/Shannon/RateDistortionAchievabilityPhaseC.lean:42` `per_codeword_no_match_prob`
- `Common2026/Shannon/RateDistortionAchievabilityPhaseC.lean:59` `codebook_indep_no_match_prob_eq`
- `Common2026/Shannon/RateDistortionAchievabilityPhaseD.lean:102` `source_averaged_failure_tendsto_zero`

**Mathlib (流用、loogle で signature verify 推奨)**:
- `Mathlib.MeasureTheory.Measure.Prod.prod_apply` — Phase S1.5, S4 で section と product 化を行き来
- `Filter.Tendsto.add` — Phase S5.6
- `Real.exp_neg`, `Real.exp_add`, `Real.exp_log` — 指数 manipulation
- `MeasureTheory.measure_inter_le_left` / `measure_union_le` — Phase S5.3 の E1 ∪ E2 decomp

**loogle で要 verify** (新規補題で出てくる shape):
- 「conditional measure on stronglyTypicalSet」: `MeasureTheory.Measure.restrict, stronglyTypicalSet` — restrict 表現で書くか indicator 表現で書くか
- 「per-codeword Y-mass via product measure indexed by Fin n」: `Measure.pi, Set.preimage Prod.mk` — Phase S2.3 sum lower bound の sectioning
- 「`integral_mono` on indicator-multiplied」: 既に Phase C C-2 で使用済、再利用形式の verify

**期待される gap (≤ 30 LOC 内 precursor で吸収可)**:
- 整数 ↔ ℝ 変換の小さい補題 (`Nat.cast`, `Real.exp` 系)
- `entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0) = ?` の chain-rule 形 (本サブ計画 Phase S2.4 内 inline、external Mathlib lemma 不要)

## 撤退ライン / 部分完了境界

優先順位順:

1. **Phase B'-S3 で commit 可** (推定 +430 LOC): strong encoder + conditional fiber size lower bound + per-source-typical match prob lower bound (= Cover-Thomas 10.6.1 strong) の publish。本サブ計画の **理論的中核**だけで standalone な inventory contribution として E-3''' 部分達成。残: Phase S4-S5 の asymptotic 詰め (1 sorry 残置)。
2. **Phase S4 まで commit 可** (推定 +520 LOC): encoder failure exponential bound publish (per-source-typical x 上の `≤ exp(-M_n · exp(-n(I+δ)))` 形)。残: Phase S5 の組立 (1 sorry 残置)。
3. **Phase S5 完了で commit** (推定 +770 LOC): 主 sorry 閉鎖、E-3''' 完成。

**1 sorry が新たに発生する撤退ライン**:
- Phase S1.5 (total Y-probability lower bound) で `Measure.prod_apply` 周りの shape mismatch が深刻な場合: lower bound を「Pr_Y[F_x] ≥ |F_x| · min-per-fiber-mass」の form ではなく「∃ y ∈ F_x, Pr_Y[y] ≥ ...」の **single-witness form** に弱化 — Phase S2 の match probability bound は弱化形でも `1 - (1 - p_typ)^M_n ≥ 1 - (1 - exp(-n(I+δ)))^M_n` の M スケールで吸収可。-50 LOC 程度のシンプル化、ただし constant factor が tight でなくなる (E-3''' は asymptotic なので無問題)。

**原理的不可ライン (このまま行くと M0 で判明する)**:
- `iIndepFun (fun i => Ys i) μ` が `rdAmbient qStar` の i.i.d. ambient で導出済か要確認。`IIDProductInputJoint.lean` の `iidAmbientJoint_iIndepFun_iidYs` 系統が既に publish されているはずだが (E-3'' で構築済)、もし `jointSequence` 軸でしか取られていなければ Phase S1-S2 で `Ys` 軸独立性を `rdAmbient` で discharge する追加補題 ~50 LOC が必要。E-3'' の `IIDProductInputJoint.lean` (225 LOC) の `_iIndepFun_iidXs/iidYs` 補題が網羅していれば追加ゼロ。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 例 (起草時、未確定):
1. **Phase B' 並立 vs in-place の最終確定**: 起草時 (b) 並立採用。S1 着手後に encoder の重複が DRY 違反として大きく感じられた場合は (a) in-place に倒すが、その際 Phase B/C/D の reverify cost を別 plan で計上。
2. **`conditionalStronglyTypicalSlice` 定義の shape**: 起草時 set-builder 形 `{ y | (x, y) ∈ jointStronglyTypicalSet }` で計画。実装時に `jointStronglyTypicalSet.section x` の image 形のほうが proof が短ければ pivot。
3. **`mutualInfoPmf qStar` の entropy 形 ↔ `H(Y) - H(Y|X)` の bridge**: Phase S2.4 で ring identity 1 行で済むつもり。pmf 形 entropy の unfold が深い場合は別補題に切り出し ~20 LOC。
-->
