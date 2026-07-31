# Marton inner bound (一般 BC) — Mathlib / in-project 在庫調査

> 親 plan: [`docs/shannon/broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md)
> (撤退ライン **L-BC5** = 「一般 (non-degraded) BC + Marton / Körner–Marton は完全 scope-out」を
> ユーザー指示で解除して追う前提の在庫調査)
>
> 対象: El Gamal–Kim *Network Information Theory* Thm 8.3 (private message のみの Marton inner bound)
> + その中核 Lemma 8.1 (mutual covering lemma)。
>
> **本ファイルは在庫の事実のみを積む。壁の断定・実装・plan 執筆はしない。**

---

## 一行サマリ

**second moment method の部品 (分散・共分散・Chebyshev) は Mathlib に 100% 既存、joint typicality の
両側評価 (上下界・conditional slice の上下界) は in-project に 100% 既存**。自前構築が要るのは
**(1) 二重添字 indicator 和の共分散分解 (mutual covering lemma 本体)、(2) `P(A = 0) ≤ Var/E²` の
10 行 wrapper、(3) 3 本目の rate 制約を持つ region 述語、(4) 5-tuple ambient plumbing** の 4 種。
**Mathlib 壁は 0 件**。ただし **最大の構造的リスクは数学ではなく `hpos` (full support) 前提**:
決定的関数 `x = f(v₁,v₂)` を `Kernel.deterministic` で入れると、in-project の typicality mass bound
**全部が要求する `∀ a b, 0 < (K a).real {b}` が原理的に壊れる**（§4 / §6）。

---

## 1. 主定理の最終形 (目標) と証明戦略

### 1.1 到達目標 (EGK Thm 8.3, private messages only)

在庫調査時点での想定形。既存 `bc_achievability`
(`InformationTheory/Shannon/BroadcastChannel/Achievability/Assembly.lean:1087`) の署名を骨格に、
degradedness (`hdeg : IsBCDegraded W`) を外し、補助変数を 1 本 (`U`) から 2 本 (`V₁`, `V₂`) に増やす:

```lean
theorem marton_achievability
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]      -- ← 決定的 f の一般化 (§4)
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v})
    (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hmarton : InMartonRegion R₁ R₂
        (martonInfo₁ pV K W) (martonInfo₂ pV K W) (martonInfoV₁V₂ pV K W))
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M₁ M₂ : ℕ) (_hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
        (_hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂)
        (c : BroadcastCode M₁ M₂ n α β₁ β₂),
        (c.averageErrorProb₁ W).toReal < ε' ∧ (c.averageErrorProb₂ W).toReal < ε'
```

`InMartonRegion R₁ R₂ I₁ I₂ I₁₂` は **3 本** (`R₁ ≤ I₁` / `R₂ ≤ I₂` / `R₁ + R₂ ≤ I₁ + I₂ − I₁₂`)。
既存 `InBCCapacityRegion` (`BroadcastChannel/Basic.lean:133`) は **2 本しかない**ので別述語が要る (§5)。

### 1.2 中核: mutual covering lemma (EGK Lemma 8.1)

```
-- 独立に引いた 2 本の codebook から jointly typical な組が存在する確率 → 1
A(cV₁, cV₂) := #{ (m₁, m₂) | (cV₁ m₁, cV₂ m₂) ∈ jointlyTypicalSet }      -- ℝ 値の二重和
E[A]   = M₁ · M₂ · p                where p := (μ_{V₁}ⁿ × μ_{V₂}ⁿ)(JTS)   -- 既存下界 §3-B
Var[A] = ∑_{(m₁,m₂)} ∑_{(m₁',m₂')} cov[…]                                  -- Mathlib variance_sum
       ≤ E[A]                            (対角: m₁=m₁' ∧ m₂=m₂')
       + M₁ M₂ (M₂−1) · q̄ · p            (m₁ 共有: conditional slice 上界 §3-C)
       + M₁ (M₁−1) M₂ · q̄ · p            (m₂ 共有)
       + 0                               (全異: 独立 ⇒ cov = 0, IndepFun.covariance_eq_zero)
P(A = 0) ≤ Var[A] / E[A]²                                                  -- 自前 10 行 (§5-2)
        ≤ 1/(M₁M₂p) + q̄/(M₁ p) + q̄/(M₂ p) → 0   when R₁+R₂ > I(V₁;V₂)
```

Cover–Thomas 系の既存 achievability が使う first moment
(`(1−q)^M ≤ exp(−Mq)`, `RateDistortion/AchievabilityStrongTypicality/SupportingBounds.lean:160,182`)
では**足りない**。その理由も在庫として確定した: あの product 分解は
「1 本の codebook の M 語が i.i.d. だから失敗事象が積に分解する」に依存しており、
2 本 codebook では pair 事象が添字を共有して積に分解しないため。

---

## 2. API 在庫テーブル (A) — second moment method (Mathlib 側)

すべて **Mathlib 既存**。`variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X Y : Ω → ℝ} {μ : Measure Ω}`
(`Mathlib/Probability/Moments/Variance.lean:51`) が共通の暗黙変数。

| 概念 | Mathlib API (逐語) | file:line | 状態 | Marton での扱い |
|---|---|---|---|---|
| 分散 | `def variance : ℝ := (evariance X μ).toReal` (記法 `Var[X; μ]`) | `Mathlib/Probability/Moments/Variance.lean:64` | ✅ 既存 | `A` の分散 |
| 共分散 | `noncomputable def covariance (X Y : Ω → ℝ) (μ : Measure Ω) : ℝ := ∫ ω, (X ω - μ[X]) * (Y ω - μ[Y]) ∂μ` (記法 `cov[X, Y; μ]`) | `Mathlib/Probability/Moments/Covariance.lean:44` | ✅ 既存 | 交差項の受け皿 |
| **Chebyshev** | `theorem meas_ge_le_variance_div_sq [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) {c : ℝ} (hc : 0 < c) : μ {ω \| c ≤ \|X ω - μ[X]\|} ≤ ENNReal.ofReal (variance X μ / c ^ 2)` | `Mathlib/Probability/Moments/Variance.lean:399` | ✅ 既存 (in-project 4 箇所で実績) | `c := E[A]` を代入して `P(A=0)` を潰す |
| **分散 = 共分散二重和** | `lemma variance_sum [IsFiniteMeasure μ] [Fintype ι] (hX : ∀ i, MemLp (X i) 2 μ) : Var[∑ i, X i; μ] = ∑ i, ∑ j, cov[X i, X j; μ]` | `Mathlib/Probability/Moments/Variance.lean:295` | ✅ 既存 | **mutual covering の心臓部**。pairwise 独立を要求しないのが要点 |
| 同 Finset 版 | `lemma variance_sum' [IsFiniteMeasure μ] (hX : ∀ i ∈ s, MemLp (X i) 2 μ) : Var[∑ i ∈ s, X i; μ] = ∑ i ∈ s, ∑ j ∈ s, cov[X i, X j; μ]` | `Mathlib/Probability/Moments/Variance.lean:287` | ✅ 既存 | 添字を `Fin M₁ × Fin M₂` に取るときの一般形 |
| pairwise 独立版 | `nonrec theorem IndepFun.variance_sum {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι} (hs : ∀ i ∈ s, MemLp (X i) 2 μ) (h : Set.Pairwise ↑s fun i j => X i ⟂ᵢ[μ] X j) : variance (∑ i ∈ s, X i) μ = ∑ i ∈ s, variance (X i) μ` | `Mathlib/Probability/Moments/Variance.lean:424` | ✅ 既存 | **Marton では直接使えない** (indicator 族は pairwise 独立でない)。`variance_sum` の方を使う |
| pi 測度版 | `lemma variance_sum_pi [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)} {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)] {X : Π i, Ω i → ℝ} (h : ∀ i, MemLp (X i) 2 (μ i)) : Var[∑ i, fun ω ↦ X i (ω i); Measure.pi μ] = ∑ i, Var[X i; μ i]` | `Mathlib/Probability/Moments/Variance.lean:449` | ✅ 既存 | 座標独立の弱法則用。Marton の pair 和には非適用 |
| 独立 ⇒ 共分散 0 | `lemma IndepFun.covariance_eq_zero (h : X ⟂ᵢ[μ] Y) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) : cov[X, Y; μ] = 0` | `Mathlib/Probability/Moments/Covariance.lean:327` | ✅ 既存 | 「全添字が異なる」項を消す |
| `cov[X,X] = Var` | `lemma covariance_self {X : Ω → ℝ} (hX : AEMeasurable X μ) : cov[X, X; μ] = Var[X; μ]` | `Mathlib/Probability/Moments/Variance.lean:195` | ✅ 既存 | 対角項 |
| `cov = E[XY] − E[X]E[Y]` | `lemma covariance_eq_sub [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) : cov[X, Y; μ] = μ[X * Y] - μ[X] * μ[Y]` | `Mathlib/Probability/Moments/Covariance.lean:54` | ✅ 既存 | 添字共有項を「両方 typical の確率」に落とす |
| 二重和の共分散 | `lemma covariance_sum_sum [Fintype ι] {ι' : Type*} [Fintype ι'] {Y : ι' → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ) : cov[∑ i, X i, ∑ j, Y j; μ] = ∑ i, ∑ j, cov[X i, Y j; μ]` | `Mathlib/Probability/Moments/Covariance.lean:285` | ✅ 既存 | 添字を 2 段に割るときの整形 |
| 分散 ≥ 0 | `theorem variance_nonneg (X : Ω → ℝ) (μ : Measure Ω) : 0 ≤ variance X μ` | `Mathlib/Probability/Moments/Variance.lean:202` | ✅ 既存 | 定型 |
| indicator の `MemLp` | `theorem MemLp.of_bound [IsFiniteMeasure μ] {f : α → E} (hf : AEStronglyMeasurable f μ) (C : ℝ) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : MemLp f p μ` | `Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean:553` | ✅ 既存 (in-project `AEP/Rate.lean:53` で実績) | indicator は `‖·‖ ≤ 1` なので即 |

### in-project 実績 (Chebyshev + variance_sum の使用例 — 手法の教科書)

| 実績箇所 | file:line | 使っている補題 | 手法 |
|---|---|---|---|
| `aep_chebyshev_bound` | `InformationTheory/Shannon/AEP/Rate.lean:108` | `IndepFun.variance_sum` (`:149`) + `meas_ge_le_variance_div_sq` (`:185`) | **座標独立和の弱法則**。二重添字ではない |
| `wz_pi_nonuniform_mean_concentration` | `InformationTheory/Shannon/WynerZiv/Achievability/Concentration.lean:789` | `variance_sum_pi` (`:813`) + `meas_ge_le_variance_div_sq` (`:856`) | 同上 (非一様 pi 測度) |
| `StrongConverseAsymptotic` Phase B | `InformationTheory/Shannon/ChannelCoding/StrongConverseAsymptotic.lean:445,551,614` | `variance_sum_pi` + `meas_ge_le_variance_div_sq` | 同上 |
| `AWGN/AchievabilityAEP.lean:62,113` | 同上 | 同上 | 同上 |

> **重要な区別**: in-project の Chebyshev 実績は**すべて「独立座標の和の集中 (弱法則)」**であり、
> **「二重添字 indicator の個数計数に対する second moment method」は 1 件も存在しない**
> (`rg -n "second moment method\|Paley\|Zygmund" InformationTheory/` → 該当 0)。
> 手法として新規。ただし部品は全部そろっている。

---

## 3. API 在庫テーブル (B/C) — joint typicality の両側評価 (in-project)

### B. 独立ペア確率の**両側**評価 — `E[A]` を挟むのに必要

| 概念 | in-project API (逐語結論形) | file:line | 状態 |
|---|---|---|---|
| 弱 (entropy) typical set | `noncomputable def typicalSet (μ : Measure Ω) (Xs : ℕ → Ω → α) (n : ℕ) (ε : ℝ) : Set (Fin n → α) := { x \| \|(∑ i : Fin n, pmfLog μ Xs (x i)) / n - entropy μ (Xs 0)\| < ε }` | `InformationTheory/Shannon/AEP/Basic/Core.lean:214` | ✅ 既存 |
| joint typical set | `noncomputable def jointlyTypicalSet (μ) (Xs) (Ys) (n) (ε) : Set ((Fin n → α) × (Fin n → β))` — X 軸 / Y 軸 / joint 軸の 3 条件の交わり | `InformationTheory/Shannon/ChannelCoding/Basic.lean:281` | ✅ 既存 |
| 単語質量 **上界** | `theorem typicalSet_prob_le (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (hindep_full : iIndepFun (fun i ↦ Xs i) μ) (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x}) (n : ℕ) {ε : ℝ} (x : Fin n → α) (hx : x ∈ typicalSet μ Xs n ε) : (μ.map (jointRV Xs n)).real {x} ≤ Real.exp (- (n : ℝ) * (entropy μ (Xs 0) - ε))` | `InformationTheory/Shannon/AEP/Basic/Achievability.lean:507` | ✅ 既存 |
| 単語質量 **下界** | `theorem typicalSet_prob_ge (…同じ引数…) : Real.exp (- (n : ℝ) * (entropy μ (Xs 0) + ε)) ≤ (μ.map (jointRV Xs n)).real {x}` | `InformationTheory/Shannon/AEP/Basic/Achievability.lean:628` | ✅ 既存 |
| **独立ペア確率 上界** | `theorem jointlyTypicalSet_indep_prob_le [Nonempty α] [Nonempty β] (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs) (Ys) (hXs) (hYs) (hindepX_full : iIndepFun (fun i ↦ Xs i) μ) (hidentX) (hindepY_full) (hidentY) (hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x}) (hposY) (hposZ) (n : ℕ) {ε : ℝ} (hε : 0 < ε) : (((μ.map (jointRV Xs n)).prod (μ.map (jointRV Ys n))).real (jointlyTypicalSet μ Xs Ys n ε)) ≤ Real.exp ((n : ℝ) * ((entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0) - entropy μ (Ys 0)) + 3 * ε))` | `InformationTheory/Shannon/ChannelCoding/Basic.lean:540` (`@[entry_point]`) | ✅ 既存 |
| **独立ペア確率 下界** | `theorem jointlyTypicalSet_indep_prob_ge (μ) [IsProbabilityMeasure μ] (Xs) (Ys) (hXs) (hYs) (hindepX_full) (hidentX) (hindepY_full) (hidentY) (hindepZ_full) (hidentZ) (hposX) (hposY) (hposZ) (n : ℕ) {ε η : ℝ} (hμJTS : (1 - η) ≤ μ.real {ω \| (jointRV Xs n ω, jointRV Ys n ω) ∈ jointlyTypicalSet μ Xs Ys n ε}) : (1 - η) * Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0) - entropy μ (Ys 0) - 3 * ε)) ≤ ((μ.map (jointRV Xs n)).prod (μ.map (jointRV Ys n))).real (jointlyTypicalSet μ Xs Ys n ε)` | `InformationTheory/Shannon/RateDistortion/AchievabilityJointTypicalEncoder.lean:255` (`@[entry_point]`) | ✅ **既存 — これが `E[A]` の下界そのもの** |
| 入力仮定 `hμJTS` の供給元 | `theorem jointlyTypicalSet_prob_tendsto_one` | `InformationTheory/Shannon/ChannelCoding/Basic.lean:450` | ✅ 既存 |
| typical set 個数 上界 | `theorem typicalSet_card_le` | `InformationTheory/Shannon/AEP/Basic/Core.lean:247` (`@[entry_point]`) | ✅ 既存 |
| typical set 個数 下界 | `theorem typicalSet_card_ge` | `InformationTheory/Shannon/AEP/Basic/Achievability.lean:719` | ✅ 既存 |
| joint typical set 個数 上界 | `theorem jointlyTypicalSet_card_le` | `InformationTheory/Shannon/ChannelCoding/Basic.lean:320` | ✅ 既存 |

> **「mutual covering は分散評価のため joint typical set のサイズ両側評価が要る」という brief の前提は
> 完全に充足されている**。上下界とも `@[entry_point]` 付きの既存 sorry-free 資産。

### C. conditional slice の上界 — 添字共有 (交差) 項の評価に必要

second moment の交差項は
`E[1_{(m₁,m₂)} · 1_{(m₁,m₂')}] = E_{v₁}[ q(v₁)² ]`, `q(v₁) := P_{V₂}(slice at v₁)` の形。
`q(v₁) ≤ q̄` の一様上界が要る。**これも既存**:

| 概念 | in-project API (逐語) | file:line | 状態 |
|---|---|---|---|
| conditional slice の定義 | `noncomputable def conditionalTypicalSlice (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (n : ℕ) (ε : ℝ) (y : Fin n → β) : Set (Fin n → α) := { x \| (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε }` | `InformationTheory/Shannon/SlepianWolf/ConditionalTypicalSlice.lean:51` | ✅ 既存 |
| **slice の個数上界** | `theorem conditionalTypicalSlice_card_le (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs) (Ys) (hXs) (hYs) (hindepY_full : iIndepFun (fun i ↦ Ys i) μ) (hidentY) (hindepZ_full) (hidentZ) (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y}) (hposZ : ∀ p : α × β, 0 < (μ.map (jointSequence Xs Ys 0)).real {p}) (n : ℕ) {ε : ℝ} (y : Fin n → β) : ((conditionalTypicalSlice μ Xs Ys n ε y).toFinite.toFinset.card : ℝ) ≤ Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) - entropy μ (Ys 0) + 2 * ε))` | `InformationTheory/Shannon/SlepianWolf/ConditionalTypicalSlice.lean:140` (`@[entry_point]`) | ✅ 既存 |
| slice が空 (y 非 typical) | `lemma conditionalTypicalSlice_empty_of_y_not_typical` | `InformationTheory/Shannon/SlepianWolf/ConditionalTypicalSlice.lean:75` | ✅ 既存 |
| **「個数上界 × 単語質量上界 = slice 質量上界」のテンプレ実装** | `theorem bc_conditional_slice_prob_le … : (Measure.pi (fun l : Fin n ↦ K (u l))).real { x \| (u, x, y₁) ∈ macJointlyTypicalSet … } ≤ Real.exp (-(n : ℝ) * (bcInfo₁ pU K W - 4 * ε))` | `InformationTheory/Shannon/BroadcastChannel/Achievability/Setup.lean:549` (`@audit:ok`) | ✅ 既存 — **Marton の `q̄` はこの証明を 1:1 で写せば取れる (本体 ~90 行, `:604-639`)** |
| そのための per-sequence 質量上界 | `lemma bc_perseq_mass_le … : (Measure.pi (fun l : Fin n ↦ K (u l))).real {x} ≤ Real.exp (-(n : ℝ) * (entropy … (jointSequence bcUs bcXs 0) - entropy … (bcUs 0) - 2 * ε))` | `InformationTheory/Shannon/BroadcastChannel/Achievability/Setup.lean:350` | ✅ 既存 |
| そのための slice card 具体化 | `lemma bc_slice_card_le … ≤ Real.exp ((n : ℝ) * (entropy … (jointSequence bcXs (jointSequence bcUs bcY₁s) 0) - entropy … (jointSequence bcUs bcY₁s 0) + 2 * ε))` | `InformationTheory/Shannon/BroadcastChannel/Achievability/Setup.lean:438` | ✅ 既存 |

> `q̄ ≤ exp(−n (I(V₁;V₂) − 3ε))` は
> **`conditionalTypicalSlice_card_le` × `typicalSet_prob_le`** の 2 行合成で出る
> (`bc_conditional_slice_prob_le` の `calc` と同型)。**自前構築 ~60–90 行**。

### 強 (strong) typicality 系 — 代替ルート (現時点では非推奨)

| 概念 | API | file:line | 備考 |
|---|---|---|---|
| `stronglyTypicalSet` | `noncomputable def stronglyTypicalSet (μ) (Xs) (n) (ε) : Set (Fin n → α) := { x \| ∀ a : α, \|(typeCount x a : ℝ) / n - (μ.map (Xs 0)).real {a}\| ≤ ε }` | `InformationTheory/Shannon/StrongTypicality.lean:58` | ✅ |
| `jointStronglyTypicalSet` | `InformationTheory/Shannon/RateDistortion/AchievabilityJointStrongTypicality.lean:69` | ✅ | |
| 強版 独立ペア下界 | `theorem jointStronglyTypicalSet_indep_prob_ge … (hposX) (hposY) (hposZ) (hmarg_X) (hmarg_Y) {ε δ η : ℝ} …` | `InformationTheory/Shannon/RateDistortion/AchievabilityJointStrongTypicality.lean:474` (`@[entry_point]`) | ✅ |
| conditional slice 質量下界 (強版) | `theorem conditionalStronglyTypicalSlice_mass_ge` | `InformationTheory/Shannon/ConditionalMethodOfTypes/Mass/SliceMass.lean:36` (`@[entry_point]`) | ✅ |

> **強版も `hposX`/`hposY`/`hposZ` (full support) を等しく要求する** (`:487-491` を逐語確認)。
> したがって §4 の決定的 `f` 問題は強/弱いずれのルートでも回避できない。
> かつ強版の slack は `(card β · L_X + card α · L_Y + L_Z)·ε + 3δ` と複雑なので、
> **弱 (entropy) typicality を第一候補**とする。`jointlyTypicalSet` の弱版なら slack は `3ε` 固定。

---

## 4. 決定的関数 `x = f(v₁, v₂)` の扱い — 最大の構造的リスク

### 4.1 operational layer は無改修で通る

- `structure BroadcastCode (M₁ M₂ n : ℕ) (α β₁ β₂ : Type*) … where encoder : Fin M₁ × Fin M₂ → (Fin n → α); decoder₁ : (Fin n → β₁) → Fin M₁; decoder₂ : (Fin n → β₂) → Fin M₂`
  (`InformationTheory/Shannon/BroadcastChannel/Basic.lean:41`)
  — encoder が**メッセージ対から直接入力語**なので、`encoder (m₁,m₂) i := f (cV₁ m₁ i, cV₂ m₂ i)` が
  そのまま書ける。**構造体の改修は不要**。
- `abbrev BCChannel (α β₁ β₂) := Kernel α (β₁ × β₂)` (`Basic.lean:34`) も無改修。
- 逆依存実測 (`scripts/dep_consumers.sh`):
  - `InformationTheory.Shannon.BroadcastChannel.BroadcastCode` → **direct consumers 19 decl / 5 file**
    (Basic 10 / Converse 5 / ErrorAnalysis 2 / Setup 1 / Assembly 1)。→ 触らないので blast radius 0。
  - `InformationTheory.Shannon.BroadcastChannel.InBCCapacityRegion` → **direct consumers 3 decl / 2 file**
    (`Basic.lean:139 .mono`, `Converse.lean:179 bc_converse_message_level`, `Converse.lean:583 bc_degraded_converse`)。
    → **既存述語を 3 本制約に改修すると converse 2 本が壊れる**ので、`InMartonRegion` を**新規に足す**のが正解 (§5-3)。

### 4.2 ただし `hpos` (full support) が原理的に壊れる ← **最重要所見**

決定的 `f : V₁ × V₂ → α` を kernel 化するなら Mathlib の
`noncomputable def Kernel.deterministic (f : α → β) (hf : Measurable f) : Kernel α β where toFun a := Measure.dirac (f a)`
(`Mathlib/Probability/Kernel/Basic.lean:58`, Markov 性は `instance isMarkovKernel_deterministic` `:81`)。

その質量は
`theorem Measure.dirac_apply' (a : α) (hs : MeasurableSet s) : dirac a s = s.indicator 1 a`
(`Mathlib/MeasureTheory/Measure/Dirac.lean:44`) より
**`(Kernel.deterministic f hf v).real {b} = 0` (`b ≠ f v`)** — 逐語確認済。

一方 in-project の typicality 資産は例外なく full support を要求する (すべて逐語確認済):

- `typicalSet_prob_le` / `typicalSet_prob_ge` : `(hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})`
- `jointlyTypicalSet_indep_prob_le` / `_ge` : `(hposX)` `(hposY)` `(hposZ)`
- `conditionalTypicalSlice_card_le` : `(hposY)` `(hposZ)`
- `bc_perseq_mass_le` / `bc_slice_card_le` / `bc_conditional_slice_prob_le` :
  `(hpU : ∀ a : U, 0 < pU.real {a}) (hK : ∀ (a : U) (b : α), 0 < (K a).real {b}) (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})`
- 供給元 `bcAmbient_coord_marginal_pos` (`Setup.lean:247`) は `hpU`/`hK`/`hW` から座標周辺の正値性を作る。
  `hK` が偽なら座標周辺 `hposZ` が出せない。

⇒ **`card α ≥ 2` のとき `K := Kernel.deterministic f` は `hK` を満たさない**
(`b ≠ f v` で `0 < 0` になるため)。したがって
**「決定的 f を素直に書くと、既存の typicality 資産が 1 本も適用できない」**。

### 4.3 推奨する回避 (Mathlib-shape-driven の定石)

| 案 | 内容 | 評価 |
|---|---|---|
| **案 A (推奨)** | 主定理を **一般 Markov kernel `K : Kernel (V₁ × V₂) α`** で述べる (`hK` full support 可)。決定的 `f` は述べない | EGK の「`p(x\|v₁,v₂)` 形」に対応する標準形。in-project 資産が**そのまま**通る。`bc_achievability` の `K : Kernel U α` と完全に同じ形なので Setup plumbing も写せる |
| 案 B | full support を `hpos` から `μ.map` レベルの正値性 (`hposZ` だけ) に緩める改修 | `bcAmbient_coord_marginal_pos` から下流全部を触る。逆依存が広く、**別 leg** |
| 案 C | 決定的版を `Kernel.deterministic` で書き、mass bound を `f` の像上に制限した subtype 版へ書き換える | 型が subtype に汚染される。`Mathlib-shape-driven Definitions` の red flag (橋渡し補題を大量に書く形) |

> **案 A を採ると、決定的 `f` 版 (EGK Thm 8.3 の逐語形) は主定理の系として直ちには出ない**。
> ここは「scope の縮退」であって「壁」ではない。EGK 自身も一般 kernel 形と決定的形の等価性を
> 別命題として扱う (V を拡張して randomization を吸収する議論)。§7 の撤退ライン案に反映。

---

## 5. API 在庫テーブル (D/E/F) — codebook / plumbing / region (in-project)

### D. codebook アンサンブルと pigeonhole

| 概念 | in-project API (逐語) | file:line | 状態 | Marton での扱い |
|---|---|---|---|---|
| codebook 型 | `abbrev Codebook (M n : ℕ) (α : Type*) [MeasurableSpace α] := Fin M → (Fin n → α)` | `InformationTheory/Shannon/ChannelCoding/Achievability/Core.lean:50` | ✅ | `Fin M₁ → Fin n → V₁` を 2 本 |
| codebook 測度 | `noncomputable def codebookMeasure (p : Measure α) (M n : ℕ) : Measure (Codebook M n α) := Measure.pi (fun _ : Fin M ↦ Measure.pi (fun _ : Fin n ↦ p))` | `InformationTheory/Shannon/ChannelCoding/Achievability/Core.lean:216` | ✅ | 2 本を `Measure.prod` で独立に結合 |
| 同 確率測度 instance | `instance codebookMeasure.instIsProbabilityMeasure (p : Measure α) [IsProbabilityMeasure p] (M n : ℕ) : IsProbabilityMeasure (codebookMeasure p M n)` | `:220` | ✅ | |
| **抽象 2 段 pigeonhole** | `lemma bc_two_tier_pigeonhole {κU κX : Type*} [Fintype κU] [Fintype κX] (wU : κU → ℝ) (wX : κU → κX → ℝ) (val : κU → κX → ℝ) (hwU_nn) (hwX_nn) (hwU_sum : ∑ cU, wU cU = 1) (hwX_sum : ∀ cU, ∑ cX, wX cU cX = 1) (B : ℝ) (h_avg : ∑ cU, wU cU * ∑ cX, wX cU cX * val cU cX ≤ B) : ∃ (cU : κU) (cX : κX), val cU cX ≤ B` | `InformationTheory/Shannon/BroadcastChannel/Achievability/Assembly.lean:699` | ✅ | **完全に抽象。Marton の 2 本独立 codebook にそのまま適用可** (`wX cU cX` を `cU` 非依存に取る) |
| 具体 2 段 pigeonhole | `theorem bc_exists_codebook_le_avg …` | `InformationTheory/Shannon/BroadcastChannel/Achievability/Assembly.lean:744` | ✅ | 参考実装 (~50 行) |
| 単段 pigeonhole | `theorem exists_codebook_low_avg {M n : ℕ} (p : Measure β) [IsProbabilityMeasure p] (f : Codebook M n β → ℝ) {B : ℝ} (h_avg : ∑ c : Codebook M n β, (codebookMeasure p M n).real {c} * f c ≤ B) : ∃ c : Codebook M n β, f c ≤ B` | `InformationTheory/Shannon/RateDistortion/AchievabilityCodebookMatchProbability.lean:138` | ✅ | |
| 誤り分解 (E1+E2) | `theorem errorProbAt_le_E1_plus_E2 …` | `InformationTheory/Shannon/ChannelCoding/Achievability/Core.lean:83` | ✅ | 単一受信機の union bound 骨格 |
| 3 項 Bonferroni (受信機 1) | `theorem bc_errorProbAt₁_le_bonferroni3` | `InformationTheory/Shannon/BroadcastChannel/Achievability/ErrorAnalysis.lean:652` | ✅ | Marton も 3 項になる |
| 2 項 Bonferroni (受信機 2) | `theorem bc_errorProbAt₂_le_bonferroni` | `InformationTheory/Shannon/BroadcastChannel/Achievability/ErrorAnalysis.lean:28` | ✅ | |
| 平均誤り → 和形 | `theorem bc_averageErrorProb₁_toReal_le` / `bc_averageErrorProb₂_toReal_le` | `.../Assembly.lean:345` / `:312` | ✅ | |
| `(1−q)^M ≤ exp(−Mq)` | `lemma one_sub_pow_le_exp_neg_mul (M : ℕ) {t : ℝ} (_h0 : 0 ≤ t) (h1 : t ≤ 1) : …` | `InformationTheory/Shannon/RateDistortion/AchievabilityCodebookMatchProbability.lean:45` | ✅ | **単一 codebook covering 用。Marton の mutual covering には使えない** (§1.2) |

### E. i.i.d. ambient plumbing

| 概念 | in-project API (逐語) | file:line | 状態 |
|---|---|---|---|
| 座標ごとの joint 法則 | `noncomputable def bcJointDistribution (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂) : Measure (U × α × β₁ × β₂) := ((pU ⊗ₘ K) ⊗ₘ (W.comap Prod.snd measurable_snd)).map MeasurableEquiv.prodAssoc` | `InformationTheory/Shannon/BroadcastChannel/Achievability/Setup.lean:54` | ✅ 既存 |
| i.i.d. ambient | `noncomputable def bcAmbientMeasure (pU) (K) (W) : Measure (ℕ → U × α × β₁ × β₂) := Measure.infinitePi (fun _ : ℕ ↦ bcJointDistribution pU K W)` | `Setup.lean:71` | ✅ 既存 |
| 座標 map | `lemma bcAmbient_map_coord {γ} [MeasurableSpace γ] … (g : U × α × β₁ × β₂ → γ) (hg : Measurable g) (i : ℕ) : (bcAmbientMeasure pU K W).map (fun ω ↦ g (ω i)) = (bcJointDistribution pU K W).map g` | `Setup.lean:159` | ✅ 既存 |
| 座標 iIndepFun | `lemma bcAmbient_iIndepFun_coord … : iIndepFun (fun (i : ℕ) (ω : ℕ → U × α × β₁ × β₂) ↦ g (ω i)) (bcAmbientMeasure pU K W)` | `Setup.lean:172` | ✅ 既存 |
| 座標 IdentDistrib | `lemma bcAmbient_identDistrib_coord …` | `Setup.lean:182` | ✅ 既存 |
| 座標周辺の正値性 | `lemma bcAmbient_coord_marginal_pos … (hpU) (hK) (hW) (g) (hg) (i) (c : γ) (r : U × α × β₁ × β₂) (hr : g r = c) : 0 < ((bcAmbientMeasure pU K W).map (fun ω ↦ g (ω i))).real {c}` | `Setup.lean:247` | ✅ 既存 (§4.2 の分岐点) |
| 3 変数 joint typical set | `noncomputable def macJointlyTypicalSet (μ) (X1s) (X2s) (Ys) (n) (ε) : Set ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β))` — 7 連言 (3 単軸 + 3 ペア + 1 三重) | `InformationTheory/Shannon/MultipleAccess/JointTypicality.lean:79` | ✅ 既存 — **Marton の (V₁,V₂,Y₁) 三重にそのまま使える** |
| 3 変数 joint 列 | `noncomputable def macJointSequence (X1s) (X2s) (Ys) : ℕ → Ω → α₁ × α₂ × β := fun i ω ↦ (X1s i ω, X2s i ω, Ys i ω)` | `MultipleAccess/JointTypicality.lean:50` | ✅ 既存 |
| 3 変数 独立ペア上界 (X₁ 側) | `theorem macJTS_indep_prob_le_X1 … : ((μ.map (jointRV X1s n)).prod (μ.map (fun ω ↦ (jointRV X2s n ω, jointRV Ys n ω)))).real (macJointlyTypicalSet μ X1s X2s Ys n ε) ≤ Real.exp ((n : ℝ) * ((entropy μ (macJointSequence X1s X2s Ys 0) - entropy μ (X1s 0) - entropy μ (jointSequence X2s Ys 0)) + 3 * ε))` | `InformationTheory/Shannon/MultipleAccess/AchievabilityCore.lean:50` (`@[entry_point]`, `@audit:ok`) | ✅ 既存 — **Marton 復号側 alias 事象の受け皿** |
| 同 (X₂ 側 / 両方) | `macJTS_indep_prob_le_X2` `:271` / `macJTS_indep_prob_le_both` `:182` | `.../AchievabilityCore.lean` | ✅ 既存 |

### F. region / 情報量 (在庫と不足)

| 概念 | API | file:line | 状態 | Marton での扱い |
|---|---|---|---|---|
| エントロピー | `noncomputable def entropy (μ : Measure Ω) (Xs : Ω → X) : ℝ := ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})` | `InformationTheory/Shannon/Bridge.lean:40` | ✅ | **情報量はすべてこの差分形で書く** |
| 相互情報量 (KL 版) | `noncomputable def mutualInfo (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞ := klDiv (μ.map (fun ω ↦ (Xs ω, Yo ω))) ((μ.map Xs).prod (μ.map Yo))` | `InformationTheory/Shannon/MutualInfo.lean:36` | ✅ | **使わない** (`ℝ≥0∞` で typicality の出口形と噛み合わない) |
| BC 情報量 (雛形) | `noncomputable def bcInfo₁ (pU) (K) (W) : ℝ := entropy (bcJointDistribution pU K W) (fun q ↦ (q.1, q.2.1)) + entropy … (fun q ↦ (q.1, q.2.2.1)) - entropy … (fun q ↦ (q.1, q.2.1, q.2.2.1)) - entropy … Prod.fst` | `Setup.lean:111` | ✅ | `martonInfo₁ = I(V₁;Y₁)` などを同じ形で新規定義 |
| 同 `bcInfo₂` / `bcInfoJoint` | `Setup.lean:100` / `ErrorAnalysis.lean:927` | ✅ | | |
| 2 本制約 region | `structure InBCCapacityRegion (R₁ R₂ I₁ I₂ : ℝ) : Prop where bound₁ : R₁ ≤ I₁; bound₂ : R₂ ≤ I₂` | `InformationTheory/Shannon/BroadcastChannel/Basic.lean:133` | ✅ | **3 本目がないので流用不可** → 新規 `InMartonRegion` |
| region 単調性 | `theorem InBCCapacityRegion.mono {R₁ R₂ I₁ I₂ I₁' I₂' : ℝ} (h : InBCCapacityRegion R₁ R₂ I₁ I₂) (h₁ : I₁ ≤ I₁') (h₂ : I₂ ≤ I₂') : InBCCapacityRegion R₁ R₂ I₁' I₂'` | `Basic.lean:141` | ✅ | 3 本版を写経 (~8 行) |
| 平均誤り確率 | `noncomputable def BroadcastCode.averageErrorProb₁ … : ℝ≥0∞ := if M₁ * M₂ = 0 then 0 else ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ∑ m : Fin M₁ × Fin M₂, c.errorProbAt₁ W m` | `Basic.lean:87` (₂ は `:94`) | ✅ | 無改修 |

---

## 6. 重要な前提条件ボックス (事故が起きやすい順)

- **`hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a}` (full support)**
  → §4.2。決定的 `f` と**両立しない**。案 A (一般 kernel) を採るならこの前提は「正則性前提」であり
  load-bearing ではない (既存 `bc_achievability` も同じ前提を持つ)。
- **`hposZ : ∀ p, 0 < (μ.map (jointSequence …0)).real {p})`**
  → `jointlyTypicalSet_indep_prob_le`/`_ge`, `conditionalTypicalSlice_card_le` が要求。
  `bcAmbient_coord_marginal_pos` (`Setup.lean:247`) 経由で `hpV`/`hK`/`hW` から供給する。
- **`hindepZ_full : iIndepFun (fun i ↦ jointSequence Xs Ys i) μ` と
  `hindepZ_pair : Pairwise fun i j ↦ … ⟂ᵢ[μ] …` は別物**。
  `jointlyTypicalSet_indep_prob_ge` は `iIndepFun` (全体独立) を、
  `conditionalStronglyTypicalSlice_mass_ge` は `Pairwise` を要求する。取り違えると型が合わない。
- **`hμJTS : (1 - η) ≤ μ.real {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈ jointlyTypicalSet μ Xs Ys n ε}`**
  → `jointlyTypicalSet_indep_prob_ge` の入力。`jointlyTypicalSet_prob_tendsto_one`
  (`ChannelCoding/Basic.lean:450`) から `∃ N, ∀ n ≥ N` の形で取り出す。**`η` は自由パラメータ**なので
  `E[A]` の下界に `(1 − η)` が残る。second moment の分母に効くので `η ≤ 1/2` 等で固定する必要あり。
- **`MemLp (indicator) 2 μ`**: `meas_ge_le_variance_div_sq` / `variance_sum` が `MemLp … 2` を要求。
  `MemLp.of_bound` (`Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean:553`, `[IsFiniteMeasure μ]`)
  + indicator の `‖·‖ ≤ 1` で即。codebook 空間は `Fintype` なので `AEStronglyMeasurable` も自明。
- **`meas_ge_le_variance_div_sq` の結論は `ℝ≥0∞` (`ENNReal.ofReal (variance X μ / c ^ 2)`)**。
  in-project の慣習は `Measure.real` (`ℝ`) なので、`.toReal` / `measureReal_def` の橋渡しが
  各所で要る (既存 `aep_chebyshev_bound` `AEP/Rate.lean:185` の直後がその実例)。
- **`Fin M₁ × Fin M₂` 上の二重和と `variance_sum` の `[Fintype ι]`**: `ι := Fin M₁ × Fin M₂` は
  `Fintype` なので `variance_sum` (Fintype 版, `:295`) がそのまま使える。
  `Finset` 版 `variance_sum'` (`:287`) は使わなくてよい。
- **`[IsFiniteMeasure μ]` vs `[IsProbabilityMeasure μ]`**:
  `variance_sum` / `covariance_sum_sum` / `MemLp.of_bound` は `[IsFiniteMeasure μ]`、
  `covariance_eq_sub` は `[IsProbabilityMeasure μ]`。codebook 測度は
  `codebookMeasure.instIsProbabilityMeasure` (`Core.lean:220`) で確率測度なので両方満たす。

---

## 7. 自前構築が必要な要素 (優先度順)

| # | 内容 | 推奨実装 | 行数感 | 落とし穴 |
|---|---|---|---|---|
| 1 | **mutual covering lemma 本体** `∃ N, ∀ n ≥ N, (codebook 測度).real {A = 0} < η` | `variance_sum` (`Variance.lean:295`) で `Var[A] = ∑∑ cov`、4 ケース分割 (対角 / m₁ 共有 / m₂ 共有 / 全異)、全異は `IndepFun.covariance_eq_zero` (`Covariance.lean:327`)、共有項は `covariance_eq_sub` (`Covariance.lean:54`) → conditional slice 一様上界 (#3) | **500–800** | 4 ケースの `Finset` 分割 (`Finset.filter` × 4 の直和) の整形が重い。共有項で `E[1·1'] = E_{v₁}[q(v₁)²] ≤ q̄ · p` を出すには Fubini (codebook 測度の pi 分解) が要る |
| 2 | `P(A = 0) ≤ Var[A] / E[A]²` wrapper | `{A = 0} ⊆ {E[A] ≤ \|A − E[A]\|}` → `meas_ge_le_variance_div_sq` (`c := E[A]`, `hc : 0 < E[A]`) → `ENNReal.ofReal` の `.toReal` 化 | **10–25** | `E[A] > 0` を先に立てる (= `p > 0`, `jointlyTypicalSet_indep_prob_ge` から)。`ℝ≥0∞ → ℝ` の変換 |
| 3 | conditional slice 一様上界 `q(v₁) ≤ exp(−n(I(V₁;V₂) − 3ε))` | `conditionalTypicalSlice_card_le` (`ConditionalTypicalSlice.lean:140`) × `typicalSet_prob_le` (`AEP/Basic/Achievability.lean:507`) の `calc` 合成。テンプレは `bc_conditional_slice_prob_le` (`Setup.lean:604-639`) | **60–90** | `v₁` が非 typical なら slice は空 (`conditionalTypicalSlice_empty_of_y_not_typical`)。場合分けを忘れると `typicalSet_prob_le` の `hx` が立たない |
| 4 | `InMartonRegion` (3 本制約) + `.mono` | `InBCCapacityRegion` (`Basic.lean:133`) を 3 フィールドに拡張した**新規 structure**。既存は改修しない (逆依存 3 decl) | **40–60** | `R₁+R₂ ≤ I₁+I₂−I₁₂` の右辺は `I₁₂` に**単調減少**なので `.mono` の向きに注意 |
| 5 | `martonInfo₁ / ₂ / V₁V₂` (entropy 差分形の情報量) | `bcInfo₁` (`Setup.lean:111`) と同じ形で 5-tuple の座標セレクタ版を書く | **60–100** | `entropy` は `[Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X] [MeasurableSingletonClass X]` を要求 (`Bridge.lean:34`)。5-tuple の各射影に instance が要る |
| 6 | 5-tuple ambient plumbing (`martonJointDistribution` / `martonAmbientMeasure` / 座標補題 4 本) | `bcJointDistribution` (`Setup.lean:54`) / `bcAmbientMeasure` (`:71`) / `bcAmbient_*_coord` (`:159,172,182,247`) を `V₁ × V₂ × α × β₁ × β₂` に写経 | **300–450** | `MeasurableEquiv.prodAssoc` の入れ子が 1 段深くなる (4-tuple → 5-tuple)。`bcJointDistribution_singleton_pos` (`Setup.lean:212`) 相当も要る |
| 7 | 誤り解析 (受信機 1 / 2 の Bonferroni + swap + 平均) | `bc_errorProbAt₁_le_bonferroni3` (`ErrorAnalysis.lean:652`) / `bc_random_codebook_E0₁_swap` (`Assembly.lean:97`) を写経 | **800–1100** | private message のみなので cloud/satellite の 2 段構造がなくなり、代わりに **encoder が mutual covering の存在証明から来る非構成的な選択**になる。`Classical.choice` 経由の codebook 構成の型が既存と違う |
| 8 | 組み立て (rate slack + N の合成 + pigeonhole) | `bc_achievability` (`Assembly.lean:1087-1223`) を写経。pigeonhole は `bc_two_tier_pigeonhole` (`:699`) をそのまま呼ぶ | **250–400** | ε の配分が 4 系統 (E0₁/E0₂/alias₁/alias₂) + covering 失敗 の 5 系統になる |

**合計見積り: 約 2000–3000 行** (新規 `InformationTheory/Shannon/BroadcastChannel/Marton/` 配下 4–5 ファイル)。

### 既存 `bc_achievability` との相対比 (実測)

| 対象 | 実測行数 |
|---|---|
| `BroadcastChannel/Achievability/Setup.lean` | 690 |
| `BroadcastChannel/Achievability/ErrorAnalysis.lean` | 1351 |
| `BroadcastChannel/Achievability/Assembly.lean` | 1223 |
| **(小計) degraded BC achievability** | **3264** (+ `Achievability.lean` 45 / `Basic.lean` 147) |
| 参考: MAC achievability 一式 (`MultipleAccess/` 7 file) | 3230 |
| 参考: WZ covering + concentration | 1392 + 1351 |

⇒ Marton は **degraded BC achievability の 0.7–0.9 倍** 程度。
理由: cloud/satellite の 2 段 superposition が消える分は軽くなるが、
mutual covering (second moment) が丸ごと純増する。

---

## 8. Mathlib 壁の列挙

**現時点で `@residual(wall:…)` 相当の候補は 0 件。** 以下は「Mathlib に無い」が
「in-project で 10–800 行の自前構築で書ける」ものとして #7 に計上済み。

| 「無い」もの | loogle 確認 | in-project `rg` 確認 | 判定 |
|---|---|---|---|
| Paley–Zygmund 不等式 | `"Paley"` → `Found 0 declarations whose name contains "Paley".` | `rg -n "Paley\|Zygmund" InformationTheory/` → BC/covering 文脈のヒット 0 (`ShannonHartley/Operational.lean:26` の Paley-Wiener は無関係) | **不要**。Chebyshev で足りる |
| second moment method 命名の補題 | `"second_moment"` → `Found 0 declarations whose name contains "second_moment".` | `rg -n "second moment method" InformationTheory/` → 0 | **自前 #2** (10–25 行) |
| `P(X = 0) ≤ Var/E²` | 第 1 段 `ProbabilityTheory.variance, \|- _ ≤ _` → `Found 6 declarations mentioning LE.le and ProbabilityTheory.variance. Of these, 5 match` = `variance_nonneg` / `variance_le_expectation_sq` / `variance_le_sq_of_bounded` / `variance_le_sub_mul_sub` / `meas_ge_le_variance_div_sq` のみ (**網羅列挙**)。第 2 段 (結論形) `\|- MeasureTheory.Measure.real _ _ ≤ ProbabilityTheory.variance _ _ / _` → `Found 0 declarations` | — | **自前 #2**。`meas_ge_le_variance_div_sq` から 10 行 |
| covering lemma 一般形 | `"covering_lemma"` → `Found 0 declarations whose name contains "covering_lemma".` | `rg -n "Marton\|marton" InformationTheory/` → **0 件** (家系ごと新規) | **自前 #1** |
| 相互情報量 (Mathlib 側) | `"mutualInfo"` → `Found 0 declarations whose name contains "mutualInfo".` | `InformationTheory/Shannon/MutualInfo.lean:36` に自前あり | **在庫あり** (ただし `ℝ≥0∞` 形なので entropy 差分形を使う) |

> 「これは無い」と書いた 4 項目はいずれも **loogle 0-hit + in-project `rg` 0-hit の両方**を確認済み。
> かつ **各項目に対して「結論形が近い既存テンプレ補題」を名指しできている**
> (#1 → `variance_sum`、#2 → `meas_ge_le_variance_div_sq`、#3 → `bc_conditional_slice_prob_le`)。
> したがって**どれも壁ではなく plumbing / 自前構築**の側。
> 共有 sorry 補題への集約は現時点では不要 (壁が 0 件のため)。

---

## 9. 撤退ラインとの距離

親 plan (`broadcast-channel-moonshot-plan.md:12`) の frozen slug:

> **L-BC5** 一般 (non-degraded) BC + Marton / Körner-Marton は完全 scope-out

- **本調査は L-BC5 そのものの解除を前提とする**ので、L-BC5 は定義上「触れている」。
  ただし在庫調査の結果として **L-BC5 を再発動させる材料 (Mathlib 壁) は見つからなかった**。
- 未使用のまま残っている `L-BC1` (joint typicality multi-receiver body) / `L-BC3`
  (inner bound existence pass-through) は Marton でも再利用可能なスロット。
  特に **L-BC1 は mutual covering (#7-1) の撤退先として意味を持つ**
  (multi-receiver joint typicality 本体が重すぎた場合)。

### 新規に提案する撤退ライン (子 plan 起票時に採否を決める想定)

| slug 案 | 発動条件 | 縮退先 (退避口 = `sorry` + `@residual`、hypothesis bundling は禁止) |
|---|---|---|
| **L-MT1** | mutual covering lemma (#7-1) の 4 ケース共分散分解が 1 leg で閉じない | `mutual_covering_exists : … := by sorry` + `@residual(plan:marton-mutual-covering)` を置き、上位 (region / operational) を先に組む。**述語化して仮定に積むのは禁止** |
| **L-MT2** | 決定的 `x = f(v₁,v₂)` 版が `hpos` 前提と両立しない (§4.2、**既に確定した事実**) | **一般 kernel `K : Kernel (V₁ × V₂) α` 形で主定理を述べる (案 A)**。決定的版は別 leg。README / textbook-roadmap には「EGK Thm 8.3 の `p(x\|v₁,v₂)` 形」と明記する |
| **L-MT3** | 5-tuple ambient plumbing (#7-6) が 4-tuple の写経で済まず爆発 | 補助変数を `V := V₁ × V₂` と束ねた 4-tuple `V × α × β₁ × β₂` に落として `bcAmbientMeasure` の形をそのまま保つ (射影 `V → V₁` / `V → V₂` を後付けする) |
| **L-MT4** | 誤り解析 (#7-7) の非構成的 encoder 構成が既存 `codebookToCode` 系と型が合わない | sum-rate 制約なしの**退化版** (`R₁ ≤ I(V₁;Y₁)`, `R₂ ≤ I(V₂;Y₂)` のみ、`V₁ ⟂ V₂`) をまず閉じる。これは mutual covering 不要 (I(V₁;V₂) = 0) で、既存 MAC 型 union bound だけで通る |

> **L-MT4 の退化版は「gateway atom」として先に撃つ価値が高い**:
> `V₁ ⟂ V₂` を課すと mutual covering が自明化し、`macJTS_indep_prob_le_*`
> (`MultipleAccess/AchievabilityCore.lean:50,182,271`) の写経だけで一般 BC の
> (弱い) inner bound が閉じる。ここが通れば #7-6/#7-7 の plumbing 見積りが実測で取れる。

---

## 10. 着手のための skeleton

`InformationTheory/Shannon/BroadcastChannel/Marton/Basic.lean` の出だし想定 (region + 情報量のみ):

```lean
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Basic
import InformationTheory.Shannon.BroadcastChannel.Achievability.Setup

/-!
# Marton inner bound — region primitives

The three-constraint auxiliary-variable region for the general (non-degraded)
two-receiver broadcast channel (El Gamal–Kim Thm 8.3, private messages only).
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators

variable {V₁ V₂ α β₁ β₂ : Type*}
  [Fintype V₁] [DecidableEq V₁] [Nonempty V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [DecidableEq V₂] [Nonempty V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- The Marton inner-bound region: the two corner rate bounds plus the sum-rate
bound penalised by the auxiliary-variable dependence `I₁₂ = I(V₁; V₂)`.  Unlike
`InBCCapacityRegion` (two constraints, degraded BC) this carries a third field;
the two predicates are deliberately separate so the degraded converse consumers
of `InBCCapacityRegion` are untouched. -/
structure InMartonRegion (R₁ R₂ I₁ I₂ I₁₂ : ℝ) : Prop where
  /-- Receiver-1 rate bound. -/
  bound₁ : R₁ ≤ I₁
  /-- Receiver-2 rate bound. -/
  bound₂ : R₂ ≤ I₂
  /-- Sum-rate bound, penalised by the auxiliary dependence. -/
  boundSum : R₁ + R₂ ≤ I₁ + I₂ - I₁₂

theorem InMartonRegion.mono {R₁ R₂ I₁ I₂ I₁₂ I₁' I₂' I₁₂' : ℝ}
    (h : InMartonRegion R₁ R₂ I₁ I₂ I₁₂)
    (h₁ : I₁ ≤ I₁') (h₂ : I₂ ≤ I₂') (h₁₂ : I₁₂' ≤ I₁₂) :
    InMartonRegion R₁ R₂ I₁' I₂' I₁₂' :=
  ⟨h.bound₁.trans h₁, h.bound₂.trans h₂, by linarith [h.boundSum]⟩

end InformationTheory.Shannon.BroadcastChannel
```

`InformationTheory/Shannon/BroadcastChannel/Marton/MutualCovering.lean` の出だし想定:

```lean
import InformationTheory.Shannon.ChannelCoding.Achievability.Core
import InformationTheory.Shannon.RateDistortion.AchievabilityJointTypicalEncoder
import InformationTheory.Shannon.SlepianWolf.ConditionalTypicalSlice
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.Covariance

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators

/-- The number of jointly typical codeword pairs, as a real-valued random
variable on the product of the two independent codebook ensembles. -/
noncomputable def martonPairCount
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (V₁s : ℕ → Ω → V₁) (V₂s : ℕ → Ω → V₂) {M₁ M₂ n : ℕ} (ε : ℝ) :
    (Codebook M₁ n V₁ × Codebook M₂ n V₂) → ℝ := fun c ↦
  ∑ m : Fin M₁ × Fin M₂,
    if (c.1 m.1, c.2 m.2) ∈ jointlyTypicalSet μ V₁s V₂s n ε then (1 : ℝ) else 0

/-- Mutual covering lemma (El Gamal–Kim Lemma 8.1): if the sum rate exceeds
`I(V₁; V₂)` then the probability that no jointly typical codeword pair exists
tends to `0`.  Second-moment method: `P(A = 0) ≤ Var[A] / E[A]²`. -/
theorem marton_mutual_covering
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V₁s : ℕ → Ω → V₁) (V₂s : ℕ → Ω → V₂) : True := by
  sorry   -- skeleton placeholder; the real statement is fixed at plan time

end InformationTheory.Shannon.BroadcastChannel
```

> skeleton 2 本目の `True` は**在庫文書内の擬似コード**であり、実装時にそのまま書いてはいけない
> (`Prop := True` プレースホルダは tier 5 defect)。実装 leg では
> 主張を確定させたうえで `:= by sorry` + `@residual(plan:marton-mutual-covering)` を置く。

---

## 11. まとめ

- **既存率**: 本調査で数え上げた 38 項目のうち **34 項目が既存** (Mathlib 15 / in-project 19)、
  **自前構築 8 種**（うち 4 種は既存テンプレの写経）。→ **既存率 約 89%**。
- **Mathlib 壁 0 件**。loogle 0-hit 4 件はいずれも「近接テンプレ補題を名指しできる自前構築」。
- **最大の所見は §4.2**: 決定的 `x = f(v₁,v₂)` は `Kernel.deterministic` で書けるが、
  そのとき `(K v).real {b} = 0` (`b ≠ f v`) となり、in-project の typicality mass bound が
  **例外なく要求する `hK` full support 前提を原理的に壊す**。
  → 主定理は一般 kernel `K : Kernel (V₁ × V₂) α` 形で述べるのが唯一の低コスト経路 (L-MT2)。
- **推奨する先発 atom**: `V₁ ⟂ V₂` に退化させた inner bound (L-MT4)。
  mutual covering を迂回して既存 MAC atom だけで通るため、plumbing 見積りの実測が取れる。
