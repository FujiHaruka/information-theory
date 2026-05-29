# Slepian–Wolf full rate region achievability ムーンショット計画 🌙

E-5' シードカード (E-5 deferred 後継、`docs/moonshot-seeds.md`)。
Cover-Thomas Theorem 15.4.1 完全形:

```
R_X > H(X|Y),  R_Y > H(Y|X),  R_X + R_Y > H(X,Y)
```

の **3-bound rate region 全域** の達成可能性を、random binning + joint typicality
decoder 経路で publish する。E-5 退化点 MVP
([`slepian-wolf-achievability-plan.md`](slepian-wolf-achievability-plan.md)、310 行) で
publish 済の `swErrorProb` 定義 + 2 corner-point 結果を **boundary check** として
そのまま再利用。

> **オーケストレータ指示**: 本 plan は `Common2026/Shannon/SlepianWolfAchievability.lean`
> (310 行、E-5 corner MVP) を touch せず、新規 file
> `Common2026/Shannon/SlepianWolfFullRateRegion.lean` に **並立 publish**。
> `ChannelCodingAchievability.lean` (1890 行、`codebookMeasure` Phase C-(c)
> `random_codebook_average_le`) を **encoder-side 鏡像** として参照するか、共通
> plumbing を `Common2026/Shannon/UniformPiMeasure.lean` などへ切り出す
> (Phase 0 判断)。B-3'' で前例化した「親 file 不変 + 子 file 並立 publish」パターン
> の SW 版。

> ⚠️ **実態整合 (2026-05-30、上書き修正)**: 旧「DONE-UNCOND (headline `:1956` publish 済)」表記は **STALE / 誤り**。
> 実コード verbatim 確認で `Common2026/Shannon/SlepianWolfFullRateRegion.lean` は **1902 行 (`:1956` 不在)、
> headline `slepian_wolf_full_rate_region_achievability` は未 declare** (docstring `:1428` でロードマップ言及のみ)。
> **実装済 (0 sorry)** = Phase A–E の全 building block + F.1 total expectation (`swErrorProb_total_expectation_le:1455`)
> + F.2 pigeonhole (`exists_pair_le_of_binning_integral_le:1873`) + condEntropy bridge (`:1442`)。
> **未実装** = E.5 (rate→exp squeeze 集約) + F.3 (headline assembly) + F.4 (boundary, optional)。新規 Mathlib 壁 0、
> 残 ~150–200 行 (pure 組立)。詳細在庫: [`slepian-wolf-full-rate-region-phase-f-inventory.md`](slepian-wolf-full-rate-region-phase-f-inventory.md)。
> (旧表記は「具体的数値・型予測の verbatim 未確認」事例 — CLAUDE.md 該当節参照。)

## 進捗

- [x] Phase 0 — Codebook 機構の流用 vs 抽出判断 ✅ (2026-05-14、(B) 独立定義経路採用)
- [x] Phase A — Binning 機構 (`binningMeasure`) ✅ (2026-05-14、`SlepianWolfBinning.lean` 273 行、0 sorry)
- [x] Phase B — 期待値 collapse (`𝔼[1_{f(x)=f(x')}] = 1/M_X`) ✅ (2026-05-14、`binning_collision_prob` + `_eq_self`)
- [x] Phase C — Conditional typical slice size bound ✅ (2026-05-14、`SlepianWolfConditionalTypicalSlice.lean` 315 行、0 sorry)
- [x] Phase D — Error event decomposition `E ⊆ E_0 ∪ E_X ∪ E_Y ∪ E_{XY}` ✅ (`swErrorProb_le_E0_plus_EX_plus_EY_plus_EXY:140`)
- [x] Phase E — Per-term expectation bound ✅ (E0 tendsto `:293` + EX `:465` + EY `:865` + EXY `:1206`、全 0 sorry)
- [x] Phase F — **✅ 完了 (2026-05-30)**: E.5 squeeze (`tendsto_exp_mul_codebookSize_inv`/`_inv₂` + `codebookSize_inv_le_exp_neg`) + F.3 headline `slepian_wolf_full_rate_region_achievability` (`:1992`) genuine assembly。**proof done (0 sorry / 0 @residual、`#print axioms` sorryAx-free、honesty audit 全 `@audit:ok`、連結 gap 独立確認済)**。F.4 boundary は core 非依存で省略。在庫 → `slepian-wolf-full-rate-region-phase-f-inventory.md`

**MVP 完了サマリ (2026-05-14)**: `Common2026/Shannon/SlepianWolfBinning.lean` (273 行、0 sorry / 0 warning):
- `binningMeasure α n M := Measure.pi (fun _ => uniformOn (univ : Set (Fin M)))`
- `IsProbabilityMeasure` instance
- `binningMeasure_singleton_real`: `(1/M)^{|α|^n}` singleton mass
- `binning_collision_prob`: `x ≠ x' ⟹ Pr[f x = f x'] = 1/M` (主結果)
- `binning_collision_prob_eq_self`: self-collision = 1

A.4 marginal は Phase B 主結果が経由不要だったため skip。**後継 `E-5''` deferred**: Phase C-F (joint typicality decoder + 4-way error decomposition + per-term expectation + pigeonhole + 主定理) ~1700 行。

## ゴール / Approach

**最終的に証明したい定理**:

任意の i.i.d. 2-source `(X_i, Y_i) ∼ P_{XY}` で rate triple `(R_X, R_Y)` が
3-bound rate region (`R_X > H(X|Y)`, `R_Y > H(Y|X)`, `R_X + R_Y > H(X,Y)`) を満たすとき、
**separate encoder pair** `f_X^n, f_Y^n` + joint decoder `d^n` が存在し、

- (a) `log M_X^n / n → R_X`, `log M_Y^n / n → R_Y`
- (b) `swErrorProb μ (jointRV Xs n) (jointRV Ys n) (f_X^n) (f_Y^n) (d^n) → 0`

を達成する。

### Approach (random binning + joint typicality decoder)

1. **Encoder = random binning**: 各 `n` で 2 つの **uniform random hash function**
   `f_X^n : (Fin n → α) → Fin M_X` と `f_Y^n : (Fin n → β) → Fin M_Y` を独立に
   draw。具体的に `binningMeasure α n M_X := Measure.pi (fun _ : (Fin n → α) =>
   uniformOn (Fin M_X))` で encoder 関数空間上の確率測度を立てる。
   `Codebook M n α := Fin M → (Fin n → α)` の `ChannelCodingAchievability.codebookMeasure`
   と **encoder-side 鏡像**: あちらは「codeword index → 入力 sequence」、こちらは
   「入力 sequence → bin index」。
2. **Decoder = joint typicality**: 受信 bin `(i, j) ∈ Fin M_X × Fin M_Y` に対し、
   `(x, y) ∈ (Fin n → α) × (Fin n → β)` を `(f_X^n x, f_Y^n y) = (i, j)` かつ
   `(x, y) ∈ jointlyTypicalSet μ Xs Ys n ε` で **一意** に取れるなら return、
   そうでなければ任意固定値を fallback。`ChannelCodingAchievability.jointTypicalDecoder`
   と完全同形 (`∃! m, codebook m typ` → `∃! (x, y), bin match ∧ joint typical`)。
3. **誤り 4 分解** (`E ⊆ E_0 ∪ E_X ∪ E_Y ∪ E_{XY}`):
   - `E_0`: 真の `(X^n, Y^n) ∉ jointlyTypicalSet` → AEP (`jointlyTypicalSet_prob_tendsto_one`) で → 0。
   - `E_X`: ∃ `x' ≠ X^n`, `f_X(x') = f_X(X^n)` かつ `(x', Y^n) typical` → conditional typical slice size + bin collision 確率。
   - `E_Y`: 対称形。
   - `E_{XY}`: ∃ `(x', y') ≠ (X^n, Y^n)`, `f_X(x') = f_X(X^n)`, `f_Y(y') = f_Y(Y^n)`, `(x', y') typical` → joint typical set 全域。
4. **Per-term expectation** (over random binning):
   - `E_X`: `(M_X)^{-1} · |conditional fiber slice|` で `M_X · exp(-n(H(X|Y)-2ε)) · |y_fiber|`
     形、`R_X > H(X|Y)` から → 0。
   - `E_Y`: 対称。
   - `E_{XY}`: `(M_X M_Y)^{-1} · |jointlyTypicalSet|` で `M_X M_Y · exp(-n(H(X,Y)-ε))` 形、
     `R_X + R_Y > H(X,Y)` から → 0。
5. **Pigeonhole**: 期待値 → 0 ⟹ ∃ deterministic `(f_X, f_Y)` も → 0。

### E-5 退化点 MVP との境界

- 既存 `SlepianWolfAchievability.lean` (E-5 corner MVP, 310 行) は **`R_X = log|α|`** または
  **`R_Y = log|β|`** の縮退コーナーのみ publish。本 plan は **`R_X > H(X|Y)`** かつ
  **`R_Y > H(Y|X)`** の **非自明 interior** を埋める。
- `swErrorProb` 定義 (E-5 で publish 済) はそのまま流用。
- 退化点 corner-point 結果 (`slepian_wolf_achievability_corner_X/Y`) は本 plan の
  **boundary sanity check** として `R_X → log|α|` で本 plan 主結果と一致することを
  Phase F-(c) で確認。

### Approach の代替経路と却下理由

1. **Cover-Thomas 元来 (random binning)** = **採用**。
2. **「両 source を joint AEP encode → split」経路**: `Z := (X, Y)` を joint AEP encode
   して `Fin M_n` 1 本に圧縮、その後 `Fin M_n ≅ Fin M_X × Fin M_Y` で 2 分割。
   **却下**: そもそも separate encoder pair (X だけ見て encode, Y だけ見て encode)
   を要請する SW 設定と矛盾する (joint AEP encoder は X, Y 両方を見る)。E-5 でも
   同じ理由で deterministic 経路は退化点に限定された。
3. **Type-method based achievability** (Csiszár-Körner 流): strong typicality + multinomial
   bound で `|conditional fiber slice|` を取る。**却下**: 既存 `jointlyTypicalSet` は
   weak typicality 基底、E-7 strong typicality (`StrongTypicality.lean`, 614 行) との
   bridge plumbing が ~300 行追加。本 plan は weak typicality 内で完結させる。

## Phase 0 — Codebook 機構の流用 vs 抽出判断

### 判断ポイント

`ChannelCodingAchievability.codebookMeasure`:

```lean
noncomputable def codebookMeasure (p : Measure α) (M n : ℕ) : Measure (Codebook M n α) :=
  Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => p))
```

これは「`Fin M` 本の `n`-長 codeword を独立に `p^n` から draw」する確率測度。
SW で必要なのは:

```lean
noncomputable def binningMeasure (α : Type*) [Fintype α] (n M : ℕ) :
    Measure ((Fin n → α) → Fin M) :=
  Measure.pi (fun _ : (Fin n → α) => uniformOn (Fin M))
```

= 「各 `x ∈ (Fin n → α)` に対して独立に uniform random な bin index `Fin M` を draw」。

**鏡像対応** (Phase B 期待値 collapse の本質):

| ChannelCodingAchievability | SlepianWolfFullRateRegion |
|---|---|
| Codebook `Fin M → (Fin n → α)` | Hash `(Fin n → α) → Fin M` |
| `codebookMeasure p M n = Measure.pi (fun _ : Fin M => p^n)` | `binningMeasure α n M = Measure.pi (fun _ : (Fin n → α) => uniformOn (Fin M))` |
| `𝔼[1_{codebook m = ·}] = p^n(·)` (per-row marginal) | `𝔼[1_{f(x) = f(x')}] = 1/M` for `x ≠ x'` (cross-row marginal) |
| Fubini swap on `Fin M` index | Fubini swap on `(Fin n → α)` index |

### 判断選択肢

- **(A) 共通 plumbing 抽出**: `Common2026/Shannon/UniformPiMeasure.lean` に
  `uniformPiOnFun [Fintype I] [Fintype J] : Measure (I → J)` + Fubini-collapse 補題群を
  publish。`ChannelCodingAchievability` も refactor して呼び替え。
  **コスト**: refactor ~200 行 + 既存 oleans 強制再ビルド (`ChannelCodingAchievability` は
  1890 行)、リスク高。
- **(B) 重複定義 + reuse 観点はコメントのみ**: `binningMeasure` を新規 file 内に
  独立定義、Phase B の Fubini-collapse 補題も独立証明。`codebookMeasure` の構造を
  **証明テンプレート**として参照するがコードは共有しない。
  **コスト**: ~400 行重複だが既存 file 不変、リスク低。
- **(C) 部分流用**: `codebookMeasure` の `Measure.pi` plumbing 補題
  (`block_law_X_eq_pi_p` 等の private) を public 化し、`binningMeasure` 側で
  symbol-level に流用。
  **コスト**: 中間。private → public 化は upstream `ChannelCodingAchievability` の
  signature 改変を要する。

**判断方針 (Phase 0 で finalize)**: **(B) を default**、Phase B 進行中に
重複 plumbing が ~300 行を超える場合 (C) → (A) へ pivot。判断ログ #1 に記録。

### Phase 0 ステップ

- [ ] **0.1** `binningMeasure` の Mathlib API inventory (loogle):
  - `MeasureTheory.Measure.pi` + `Fintype` 上の `uniformOn`。
  - 既存 `ChannelCodingAchievability` `codebookMeasure` instances (`IsProbabilityMeasure`)。
- [ ] **0.2** ファイル配置決定: 新規 `Common2026/Shannon/SlepianWolfFullRateRegion.lean`
  vs 既存 `SlepianWolfAchievability.lean` に追記 (B-3'' precedent → 新規)。
- [ ] **0.3** 判断 (A/B/C) 仮 commit (judgmental, 後で revise 可)。

## Phase A — Binning 機構

### 主定義

```lean
/-- Uniform random hash on `(Fin n → α) → Fin M`: 各 `x` に対し独立に bin index を draw。 -/
noncomputable def binningMeasure
    (α : Type*) [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (n M : ℕ) [NeZero M] :
    Measure ((Fin n → α) → Fin M) :=
  Measure.pi (fun _ : (Fin n → α) =>
    (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ • Measure.count.restrict Set.univ)
```

(具体的な uniform 表現は loogle で確認、Mathlib `Fintype` 上の uniform discrete distribution
の最短 shape を採用。)

### Phase A ステップ

- [ ] **A.1** `binningMeasure` 定義 (~40 行) — Mathlib-shape-driven (Fintype 上 uniform pi の
  既存 conclusion form を verbatim 参照)。
- [ ] **A.2** `instance : IsProbabilityMeasure (binningMeasure α n M)` (~10 行) —
  `Measure.pi` の `IsProbabilityMeasure` instance + uniform pi singleton mass。
- [ ] **A.3** `binningMeasure_pi_singleton`: `binningMeasure α n M {f} = (1/M)^{|α|^n}` 形 (~30 行)。
- [ ] **A.4** 補助補題 `binningMeasure_marginal`:
  `(binningMeasure α n M).map (fun f => f x) = uniformOn (Fin M)` (~50 行)、
  Phase B の per-point collapse 入り口。

**規模**: ~130 行。

## Phase B — 期待値 collapse `𝔼[1_{f(x)=f(x')}] = 1/M_X` for `x ≠ x'`

### 主補題

```lean
theorem binning_collision_prob
    {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    {n M : ℕ} [NeZero M]
    {x x' : Fin n → α} (h : x ≠ x') :
    (binningMeasure α n M).real {f | f x = f x'} = (M : ℝ)⁻¹
```

```lean
theorem binning_collision_prob_eq_self
    {x : Fin n → α} :
    (binningMeasure α n M).real {f | f x = f x} = 1
```

### Phase B ステップ

- [ ] **B.1** `binningMeasure` を `Measure.pi` で展開 (~30 行)。
- [ ] **B.2** **Fubini swap**: `Measure.pi` を `x` と `x'` の 2-coordinate に restrict
  し、残りを marginal out (`Measure.pi_eval_eq` 系列)。`ChannelCodingAchievability`
  の `random_codebook_E2_swap` (~50 行) の鏡像 (~80 行)。
- [ ] **B.3** **2-coordinate joint**: `{f | f x = f x'}` を `Fin M × Fin M` 上の対角集合に
  pullback、`uniformOn × uniformOn` で対角 mass `M / M² = 1/M` (~80 行)。
- [ ] **B.4** Self-collision (`x = x`) 専用 short cut (~20 行)。
- [ ] **B.5** **3-event extension** (Phase E-{XY} で必要): 2 個の独立 binning `f_X, f_Y` で
  `(f_X(x), f_Y(y))` の同時 collision、`(binningMeasure α × binningMeasure β).prod` の
  Fubini で `1/(M_X M_Y)` (~80 行)。
- [ ] **B.6** **Symbolic 流用 vs 独立証明 判断**: Phase 0 判断 (A/B/C) に沿って。
  (B) なら独立証明、(C) なら `codebookMeasure_marginal_one` を再公開して symbol 借用。

**規模**: ~290-400 行。`ChannelCodingAchievability.random_codebook_E2_swap` (~50 行) +
`block_law_X_eq_pi_p` / `block_law_Y_eq_pi` (~30 行) の **encoder-side 鏡像** として
構造完全平行。

## Phase C — Conditional typical slice size bound

### 主補題 (Mathlib gap、本 plan の中核新規補題)

```lean
/-- For any `y ∈ Fin n → β`, the fiber of `jointlyTypicalSet` at `y` has size
    bounded by `exp(n(H(X|Y) + 2ε))`. -/
theorem jointlyTypicalSet_conditional_fiber_card_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hposZ : ∀ p : α × β, 0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (y : Fin n → β) :
    ((Set.image Prod.fst
        ((jointlyTypicalSet μ Xs Ys n ε) ∩ {p | p.2 = y})).toFinite.toFinset.card : ℝ)
      ≤ Real.exp ((n : ℝ) *
          ((entropy μ (jointSequence Xs Ys 0) - entropy μ (Ys 0)) + 2 * ε))
```

Conclusion 右辺の `H(X, Y) - H(Y) = H(X|Y)` で `H(X|Y) + 2ε` (chain rule)。

### 証明戦略

1. **Fiber 全体の確率上界**: 各 `(x, y) ∈ jointlyTypicalSet` で point-wise 確率は
   `≥ exp(-n(H(X,Y) + ε))` (`AEP.jointlyTypicalSet_prob_ge`、既存 Mathlib gap)。
2. **`Y^n = y` の確率下界**: `Y^n` 単独で typical なら `Pr[Y^n = y] ≥ exp(-n(H(Y) + ε))`。
3. **比 = fiber size**: `(条件付き fiber 内 mass) / Pr[Y^n = y] ≤ 1` から
   `fiber size · exp(-n(H(X,Y) + ε)) / exp(-n(H(Y) + ε)) ≤ 1` で
   `fiber size ≤ exp(n(H(X,Y) - H(Y) + 2ε)) = exp(n(H(X|Y) + 2ε))`。

### Phase C ステップ

- [ ] **C.1** `jointlyTypicalSet_prob_ge`: 点 mass 下界 (~80 行、`AEP.typicalSet_prob_le`
  の逆向き、Mathlib gap)。
- [ ] **C.2** `jointlyTypicalSet_fiber_at_y`: `{p | p.2 = y}` での切断、`Set.image Prod.fst`
  の Finite/Fintype plumbing (~60 行)。
- [ ] **C.3** `Y^n` 単独の typical set 確率下界 (`AEP.typicalSet_prob_ge` 既存) (~40 行)。
- [ ] **C.4** **主補題**: fiber size の指数 upper bound (~120 行)。
- [ ] **C.5** 対称形 `X^n = x` での fiber (Phase E-Y で使用) (~80 行)。

**規模**: ~380 行。**Mathlib gap (本 plan で新規 publish)**: `jointlyTypicalSet_prob_ge`
(点 mass 下界) は既存 `jointlyTypicalSet_card_le` の **point-wise dual**、AEP plumbing
を踏襲して証明可能。

### conditional entropy の表現選択

`H(X|Y) = H(X,Y) - H(Y)` 形で内部書く (Cover-Thomas chain rule)、最終 statement で
`InformationTheory.MeasureFano.condEntropy μ (Xs 0) (Ys 0)` への bridge は別補題
(Phase F の cleanup)。既存 `MIChainRule.lean` に
`mutualInfo_eq_entropy_add_entropy_sub_jointEntropy` 等の chain rule 補題あり、流用。

## Phase D — Error event decomposition `E ⊆ E_0 ∪ E_X ∪ E_Y ∪ E_{XY}`

### Joint typicality decoder の定義

```lean
noncomputable def swJointTypicalDecoder
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {n M_X M_Y : ℕ} (ε : ℝ)
    (f_X : (Fin n → α) → Fin M_X) (f_Y : (Fin n → β) → Fin M_Y) :
    Fin M_X × Fin M_Y → (Fin n → α) × (Fin n → β) := fun ij =>
  haveI : Nonempty ((Fin n → α) × (Fin n → β)) := ⟨default⟩
  if h : ∃! p : (Fin n → α) × (Fin n → β),
      f_X p.1 = ij.1 ∧ f_Y p.2 = ij.2 ∧ p ∈ jointlyTypicalSet μ Xs Ys n ε
    then Classical.choose h.exists
    else default
```

### 主補題: 誤り集合の 4 分解

```lean
theorem swErrorEvent_subset
    {μ : Measure Ω} {Xs : ℕ → Ω → α} {Ys : ℕ → Ω → β}
    {n M_X M_Y : ℕ} {ε : ℝ}
    (f_X : (Fin n → α) → Fin M_X) (f_Y : (Fin n → β) → Fin M_Y) :
    {ω | swJointTypicalDecoder μ Xs Ys ε f_X f_Y
            (f_X (jointRV Xs n ω), f_Y (jointRV Ys n ω))
            ≠ (jointRV Xs n ω, jointRV Ys n ω)}
      ⊆ E_0 ∪ E_X ∪ E_Y ∪ E_XY
```

ここで:

- `E_0 ω := (jointRV Xs n ω, jointRV Ys n ω) ∉ jointlyTypicalSet μ Xs Ys n ε`
- `E_X ω := ∃ x' ≠ jointRV Xs n ω, f_X x' = f_X (jointRV Xs n ω) ∧ (x', jointRV Ys n ω) ∈ jointlyTypicalSet`
- `E_Y ω := ∃ y' ≠ jointRV Ys n ω, f_Y y' = f_Y (jointRV Ys n ω) ∧ (jointRV Xs n ω, y') ∈ jointlyTypicalSet`
- `E_XY ω := ∃ (x', y') ≠ (jointRV Xs n ω, jointRV Ys n ω), f_X x' = f_X _ ∧ f_Y y' = f_Y _ ∧ (x', y') ∈ jointlyTypicalSet`

### Phase D ステップ

- [ ] **D.1** `swJointTypicalDecoder` 定義 (~30 行) — `jointTypicalDecoder` (ChannelCoding版)
  の SW shape 鏡像。
- [ ] **D.2** `decode_eq_iff_unique` 系の補題 (~50 行) — encoder/decoder の関係。
- [ ] **D.3** **主分解定理** `swErrorEvent_subset` の case analysis (~120 行) —
  `ChannelCodingAchievability.errorProbAt_le_E1_plus_E2` の SW 鏡像。
- [ ] **D.4** 4 集合の measurability (`Set.Finite` + Fintype 系) (~30 行)。

**規模**: ~230 行。

## Phase E — Per-term expectation bound

### 主補題

```lean
/-- E_0 の確率は random binning と独立に AEP で → 0. -/
theorem swError_E0_tendsto_zero : Tendsto E_0_prob atTop (𝓝 0)

/-- E_X の期待値 ≤ exp(-n(R_X - H(X|Y) - 3ε)) → 0 since R_X > H(X|Y). -/
theorem swError_E_X_expectation_le :
    𝔼[E_X_prob] ≤ Real.exp (- n · (R_X - H(X|Y) - 3 * ε))

/-- E_Y 対称. -/
theorem swError_E_Y_expectation_le :
    𝔼[E_Y_prob] ≤ Real.exp (- n · (R_Y - H(Y|X) - 3 * ε))

/-- E_{XY} の期待値 ≤ exp(-n(R_X + R_Y - H(X,Y) - 2ε)) → 0
    since R_X + R_Y > H(X,Y). -/
theorem swError_E_XY_expectation_le :
    𝔼[E_XY_prob] ≤ Real.exp (- n · (R_X + R_Y - H(X,Y) - 2 * ε))
```

### Phase E ステップ

- [ ] **E.1** `E_0`: `jointlyTypicalSet_prob_tendsto_one` 直接適用 (~30 行)。
- [ ] **E.2** `E_X`: Phase B (`binning_collision_prob`, 1/M_X) + Phase C-(C.5)
  (`|fiber slice| ≤ exp(n(H(X|Y) + 2ε))`) の積 (~150 行)。
- [ ] **E.3** `E_Y`: 対称 (~150 行)。
- [ ] **E.4** `E_{XY}`: Phase B-(B.5) (2 個 collision, `1/(M_X M_Y)`) + 既存
  `jointlyTypicalSet_card_le` (`|JTS| ≤ exp(n(H(X,Y) + ε))`) の積 (~150 行)。
- [ ] **E.5** rate condition から指数 → 0 の squeeze 集約 (~80 行)。

**規模**: ~560 行。各 term は **Fubini swap** (binning ⊗ ambient ⊗ AEP-fiber 上で
Tonelli) を要する。`ChannelCodingAchievability.random_codebook_E2_swap` (~120 行 in
existing file) の **encoder-side 鏡像** で構造平行。

## Phase F — Pigeonhole + finalize

### Phase F-(a) 期待値 → 存在

```lean
theorem exists_binning_pair_low_error
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs Ys ...) (R_X R_Y ε' ...) :
    ∃ N : ℕ, ∀ n, N ≤ n →
    ∃ (f_X : (Fin n → α) → Fin (M_X n)) (f_Y : (Fin n → β) → Fin (M_Y n)),
      swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
        (swJointTypicalDecoder μ Xs Ys ε f_X f_Y) < ε'
```

### Phase F-(b) 主定理

```lean
theorem slepian_wolf_full_rate_region_achievability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindep : ... full i.i.d. of joint sequence ...)
    (hpos : ∀ p : α × β, 0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    {R_X R_Y : ℝ}
    (hRX : InformationTheory.MeasureFano.condEntropy μ (Xs 0) (Ys 0) < R_X)
    (hRY : InformationTheory.MeasureFano.condEntropy μ (Ys 0) (Xs 0) < R_Y)
    (hRXY : entropy μ (jointSequence Xs Ys 0) < R_X + R_Y) :
    ∃ (M_X M_Y : ℕ → ℕ),
      (∀ n, 0 < M_X n) ∧ (∀ n, 0 < M_Y n) ∧
    ∃ (f_X : ∀ n, (Fin n → α) → Fin (M_X n)) (f_Y : ∀ n, (Fin n → β) → Fin (M_Y n))
      (d : ∀ n, Fin (M_X n) × Fin (M_Y n) → (Fin n → α) × (Fin n → β)),
      Tendsto (fun n => Real.log (M_X n : ℝ) / n) atTop (𝓝 R_X) ∧
      Tendsto (fun n => Real.log (M_Y n : ℝ) / n) atTop (𝓝 R_Y) ∧
      Tendsto (fun n => swErrorProb μ (jointRV Xs n) (jointRV Ys n)
                          (f_X n) (f_Y n) (d n)) atTop (𝓝 0)
```

### Phase F-(c) Boundary check

- [ ] `slepian_wolf_full_rate_region_achievability` を `R_X := log|α|` で specialize し、
  `R_Y > H(Y|X)` の `Y`-encoder 経路として既存
  `slepian_wolf_achievability_corner_Y` と consistency check (sanity)。
- [ ] 対称形 `R_Y := log|β|` で `slepian_wolf_achievability_corner_X` 一致。

### Phase F ステップ

- [ ] **F.1** Pigeonhole: 期待値 < ε' ⟹ ∃ `(f_X, f_Y)` ≤ ε' (~80 行) — `binningMeasure`
  上の `exists_le_of_sum_le` (B-3'' Phase C-(d) `exists_codebook_le_avg` 鏡像)。
- [ ] **F.2** rate parametrization (`M_X n := Nat.ceil (exp (n · R_X))`) (~40 行)。
- [ ] **F.3** 主定理組立 (`N := max N_0 N_X N_Y N_XY`) (~80 行)。
- [ ] **F.4** Boundary check (~30 行)。

**規模**: ~230 行。

## Mathlib API inventory (loogle 確認必須)

> **CLAUDE.md 規約**: 各 lemma の **`file:line` 位置 + 全シグネチャ + `[...]` 型クラス
> 前提 verbatim + 結論形 verbatim** で記録すること。Phase 0 で subagent に inventory を
> 委譲する場合も同じ。以下は調査リスト (skeleton)。

### Uniform Pi Measure 系 (Phase A)

- [ ] `MeasureTheory.Measure.pi` (既存使用) — `Mathlib/MeasureTheory/Constructions/Pi.lean`
- [ ] `MeasureTheory.Measure.count` — `Mathlib/MeasureTheory/Measure/Count.lean`
- [ ] `MeasureTheory.Measure.pi_pi` (singleton mass) — `Mathlib/MeasureTheory/Constructions/Pi.lean`
- [ ] Mathlib における `Fintype` 上 uniform discrete distribution の canonical shape (PMF/Measure)。
- [ ] 既存 `ChannelCodingAchievability.codebookMeasure.instIsProbabilityMeasure` (refer)。

### Fubini / Marginal 系 (Phase B)

- [ ] `MeasureTheory.Measure.pi_pi` 経由の per-coordinate evaluation。
- [ ] `MeasureTheory.lintegral_prod_swap` / `Measure.lintegral_pi_eval`。
- [ ] 既存 `ChannelCodingAchievability` Phase C-(c) `codebook_marginal_one`,
  `codebook_marginal_two`, `block_law_X_eq_pi_p` 等の **encoder-side 鏡像対応**。

### Typical Set Fiber 系 (Phase C、Mathlib gap 多数)

- [ ] `InformationTheory.Shannon.jointlyTypicalSet` (`Common2026/Shannon/ChannelCoding.lean:301`).
- [ ] `InformationTheory.Shannon.jointlyTypicalSet_card_le` (`ChannelCoding.lean:340`):
  ```
  ((jointlyTypicalSet μ Xs Ys n ε).toFinite.toFinset.card : ℝ) ≤
    Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) + ε))
  ```
- [ ] `InformationTheory.Shannon.typicalSet_prob_le` (`AEP.lean:1279`) —
  point-wise upper bound 鏡像で `typicalSet_prob_ge` を**本 plan で publish**。
- [ ] **Mathlib gap (本 plan で publish)**:
  - `jointlyTypicalSet_prob_ge` (point-wise 下界)
  - `jointlyTypicalSet_conditional_fiber_card_le` (Phase C 主補題)

### Pigeonhole + 指数 squeeze (Phase F)

- [ ] `Finset.exists_le_of_sum_le` — `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`
- [ ] `Real.tendsto_exp_neg_atTop_nhds_zero` — `Mathlib/Analysis/SpecialFunctions/Exp.lean`
- [ ] `Nat.ceil_lt_add_one`, `Nat.le_ceil`, `Nat.one_le_ceil_iff` — `Mathlib/Algebra/Order/Floor.lean`
- [ ] `tendsto_of_tendsto_of_tendsto_of_le_of_le'` (squeeze).

### Conditional entropy (Phase C-(C.5), Phase F)

- [ ] `InformationTheory.MeasureFano.condEntropy` (既存使用)。
- [ ] `mutualInfo_eq_entropy_sub_condEntropy` (`Common2026/Shannon/MIChainRule.lean`).
- [ ] **chain rule**: `H(X,Y) = H(Y) + H(X|Y)` の Lean 表現確認。

## 規模見積

| Phase | 行数見積 | 説明 |
|---|---|---|
| Phase 0 (file 配置, inventory, codebook 流用判断) | ~80 行 | plan ファイル + 判断ログ |
| Phase A (binningMeasure 機構) | ~130 行 | uniform pi measure 構築 |
| Phase B (期待値 collapse, 1/M, 1/(M_X M_Y)) | ~290-400 行 | Fubini swap |
| Phase C (conditional fiber size, Mathlib gap) | ~380 行 | jointlyTypicalSet_prob_ge + fiber bound |
| Phase D (error decomposition E ⊆ E_0 ∪ E_X ∪ E_Y ∪ E_{XY}) | ~230 行 | decoder + case analysis |
| Phase E (per-term expectation bounds × 4) | ~560 行 | binning × ambient × AEP の triple Fubini |
| Phase F (pigeonhole + 主定理 + boundary check) | ~230 行 | 親定理組立 |
| **合計** | **~1900-2010 行** | seed `~2000 行` と整合 |

precursor が必要になった場合 (~200 行 buffer): 共通 plumbing 抽出
(`UniformPiMeasure.lean`) や `jointlyTypicalSet_prob_ge` を別 file 切り出し。

## 撤退ライン / 部分完了境界

- **Phase A + B のみで commit**: `binningMeasure` 機構 + 期待値 collapse 単体を
  独立 utility として publish。Cover-Thomas 15.4 への接続は別 file。Mathlib 流の
  random hashing utility として再利用可能。
- **Phase A + B + C で commit**: `jointlyTypicalSet_conditional_fiber_card_le` までを
  publish。本 plan の Mathlib gap 単独補題として横展開可。
- **Phase A-E まで完了で commit**: 主定理を残し、4 個の per-term expectation bound を
  独立補題として publish。Phase F (pigeonhole + 主定理) は別セッションへ。
- **Phase F まで完了**: 主定理 `slepian_wolf_full_rate_region_achievability` 完成、
  Cover-Thomas 15.4.1 完全形 publish。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### #1 ChannelCodingAchievability `codebookMeasure` 流用観点 (Phase 0 起草時)

`ChannelCodingAchievability.codebookMeasure` (`Measure.pi (fun _ : Fin M => Measure.pi
(fun _ : Fin n => p))`) は「`Fin M` 本独立 codeword draw」、本 plan の
`binningMeasure` (`Measure.pi (fun _ : (Fin n → α) => uniformOn (Fin M))`) は
「`|α|^n` 個独立 hash bin draw」。両者は **`Measure.pi` の index 型を入れ替えた
鏡像**:

- ChannelCoding: index = `Fin M` (codeword 数), value = `Fin n → α` (codeword 内容)。
- SW Binning: index = `Fin n → α` (入力 sequence), value = `Fin M` (bin label)。

**期待値 collapse の証明構造は完全に対称** (Fubini swap で per-coordinate に restrict
し、残り coordinate を marginal out)。default 採用 (B): 重複定義で並立、Phase B
進行中に plumbing が 300 行を超えたら (C) → (A) へ pivot。判断 trigger は Phase B 完了時。

### #2 weak typicality 維持、E-7 (Strong Typicality) は呼ばない (Phase 0 起草時)

Cover-Thomas 15.4 は weak typicality で十分。`StrongTypicality.lean` (614 行) は
Sanov / channel coding 強形 (E-2 / E-1 上位) で使うが、本 plan の Phase C
(`jointlyTypicalSet_conditional_fiber_card_le`) は weak typicality + point-wise mass
評価で完結。strong typicality 経路は (a) より tight な bound を出すが (b) plumbing が
分厚く、本 plan の `~2000 行` budget では budget overrun。判断 trigger は Phase C
進行中、`jointlyTypicalSet_prob_ge` の証明難度が weak typicality で 300 行を超えた場合
strong typicality 経路へ pivot を検討。

### #3 (予約) conditional entropy `H(X|Y)` の表現

最終 statement は `InformationTheory.MeasureFano.condEntropy μ (Xs 0) (Ys 0) < R_X` 形を
採用、内部証明では `entropy μ (jointSequence Xs Ys 0) - entropy μ (Ys 0)` で書き、
chain rule (`MIChainRule.lean` 既存) で bridge。Phase C 起草時に re-confirm。

### #4 Phase C 実装後評価 (2026-05-14)

**結果**: `SlepianWolfConditionalTypicalSlice.lean` 315 行、0 sorry / 0 warning で
Phase C を完走。当初見積 ~380 行を下回り、Mathlib gap として新規補題
`jointlyTypicalSet_prob_ge` を separately publish せず、AEP 既存
`typicalSet_prob_ge` を `Zs := jointSequence Xs Ys` に直接適用する経路で迂回。

**採用経路**:
- `conditionalTypicalSlice μ Xs Ys n ε y := {x | (x, y) ∈ jointlyTypicalSet ...}` で
  Y-fiber を定義。
- `conditionalTypicalSlice_card_le` 主結果:
  `|slice| ≤ exp(n(H(X,Y) - H(Y) + 2ε))`。
- 証明戦略: y が Y-typical かで場合分け。
  - y not Y-typical: slice = ∅ (JTS 第 2 条件で y は Y-typical 強制)、自明。
  - y is Y-typical: `embed x i := (x i, y i) : (Fin n → α) → (Fin n → α × β)`
    で X-fiber を Z-typical set に injection。各 `embed x` に
    `typicalSet_prob_ge μ Zs` で `Pr ≥ exp(-n(H_Z + ε))`、合計 `|slice| · exp(-n(H_Z + ε))`。
    一方 `embed '' F ⊆ proj_Y ⁻¹' {y}` で `(μ.map (jointRV Zs n))(proj_Y ⁻¹' {y})`
    に押し上げ、preimage bridge `jointRV Zs n ⁻¹' (proj_Y ⁻¹' {y}) =
    jointRV Ys n ⁻¹' {y}` で `(μ.map (jointRV Ys n)) {y}` に変換、
    `typicalSet_prob_le μ Ys` で `≤ exp(-n(H_Y - ε))`。

**判断 ログ #1 への反映**: 判断 #1 で危惧した「point-wise mass 下界が典型集合外で
成立しない」(Risk R1) は、本 plan の Phase C は典型集合 **内** の点のみで
評価できるため不発。R1 の strong typicality pivot は不要だった。

**Phase D-F (後継カード) への引き継ぎ**:
- 主補題 signature は `hindepY_full`, `hidentY`, `hindepZ_full`, `hidentZ`,
  `hposY`, `hposZ` の 6 仮説。Phase E `swError_E_X_expectation_le` の証明で
  これらをそのまま渡せる shape。
- conditional entropy bridge (`H(X,Y) - H(Y) = H(X|Y)`) は本 file では
  exposed せず、最終 statement で内部式のまま。Phase F-(b) の主定理組立時に
  `MIChainRule.lean` の chain rule 補題で bridge する。

### #5 (予約) random binning **deterministic 化** の coupling 仮説

`ChannelCodingAchievability` Phase D-(b) で `hindepZ_full : iIndepFun (jointSequence Xs Ys) μ`
が追加されたのと同様、本 plan の Phase E でも binning 確率測度と ambient probability
measure の **product coupling** が必要。Phase E 起草時に `h_match_X`, `h_match_Y`,
`h_match_Z` 系の追加仮説判断を判断ログに記録。

## Risk / Fallback

- **R1 (Phase C)**: `jointlyTypicalSet_prob_ge` (point-wise 下界) が AEP の point-wise
  上界の単純 dual で書けない場合 (典型集合の point-wise mass 下界は **典型集合内** で
  しか成立しないが、本 plan は典型集合 *外* の `x` も込みで bound を取りたい局面が
  ありうる)。**Fallback**: strong typicality 経路に Phase C 部分のみ pivot、
  `StrongTypicality.lean` の `stronglyTypicalSet_prob_eq` (有値の場合) を流用。
- **R2 (Phase B)**: `Measure.pi` の index 型が `(Fin n → α)` (`Fintype` だが
  巨大カードナリティ) のとき、Mathlib `Measure.pi_pi` 系の補題の signature が
  `[Fintype I]` ではなく `[Finite I]` で書かれていて instance 衝突する可能性。
  **Fallback**: `(Fin n → α) ≃ Fin (|α|^n)` の `Fintype.equivFin` で indexer
  を `Fin (|α|^n)` に reindex、Mathlib API と整合。
- **R3 (Phase E)**: 4 個の Fubini swap (binning × ambient × AEP-fiber) で `Measure.pi`
  と `Measure.prod` の interplay が `ChannelCodingAchievability.random_codebook_E2_swap`
  以上に重くなる場合。**Fallback**: 共通 plumbing
  `Common2026/Shannon/UniformPiMeasure.lean` を切り出し、`codebookMeasure` も refactor
  して symbol 共有 (Phase 0 判断 (A) へ promotion)。
- **R4 (規模超過)**: 全体が 2500 行を超えた場合、Phase E-{XY} を deferred 後継
  カードへ切り出し、`R_X > H(X|Y) ∧ R_Y > H(Y|X)` だけ publish (sum bound は別)。
  **R_X + R_Y > H(X,Y)** 単独は E-5 corner-MVP の合成で取れるため、本 plan の
  「真の新規 contribution」は 2 つの individual conditional rate bound。

## 経路の honest 評価 (起草時)

E-5 退化点 MVP (310 行) との差分は **~1700 行**。内訳:

- Phase A + B (binning + 期待値 collapse, ~420 行): `codebookMeasure` 鏡像、
  既存 plumbing の **encoder-side 鏡像** として高再利用 (実装時間目安: 1-2 セッション)。
- Phase C (conditional fiber, ~380 行): **Mathlib gap**、本 plan で publish する
  新規補題が ~200 行、残りは plumbing。最大不確定要素 (実装時間目安: 2-3 セッション)。
- Phase D (decoder + 4-decomp, ~230 行): `ChannelCodingAchievability.jointTypicalDecoder`
  + `errorProbAt_le_E1_plus_E2` の SW 鏡像、構造既知 (実装時間目安: 1 セッション)。
- Phase E (per-term ×4, ~560 行): 既存 `random_codebook_average_le` の SW 4-term 版、
  Fubini machinery の量で律速 (実装時間目安: 2-3 セッション)。
- Phase F (pigeonhole + 主定理, ~230 行): `channel_coding_achievability` の SW 鏡像
  (実装時間目安: 1 セッション)。

**合計実装目安**: 7-10 セッション。CLAUDE.md「Skeleton-driven Development」に沿い、
Phase 0 で skeleton (全 lemma + theorem statement + `:= by sorry`) を立てた後、
**1 sorry / 1 ターン** で進める。
