# Channel coding achievability — Mathlib + Common2026 在庫 (B-3 Phase 0)

調査日 2026-05-12。Loogle index 経由 + `rg` 補助。

## Mathlib 不在 (新規定義が必要)

- **`channel` / `channelCapacity` / `dmcCapacity`**: loogle で `"channel"` 文字列 86 件、すべて `Std.Channel` (sync primitive) で IT 用は無し。`"capacity"` 211 件、すべて `Array.emptyWithCapacity` 系。**Mathlib 情報理論 namespace に DMC / Capacity 定義は無い**。
- **`jointlyTypical*`**: 文字列 hit 無し。Common2026 内も無し。

## Mathlib 利用予定 API

### Kernel (`ProbabilityTheory.Kernel`)

- `ProbabilityTheory.Kernel α β` (`Mathlib/Probability/Kernel/Defs.lean`): channel の本体型。`FunLike` で `α → Measure β` として使える。
- `ProbabilityTheory.IsMarkovKernel` (`Mathlib/Probability/Kernel/Defs.lean`): 各 fiber が probability measure であることを保証。
- `ProbabilityTheory.Kernel.const (α : Type*) (μ : Measure β) : Kernel α β` (`Mathlib/Probability/Kernel/Basic.lean`): 定数 kernel。
- `MeasureTheory.Measure.compProd (μ : Measure α) (κ : Kernel α β) : Measure (α × β)` (`Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean`): 入力分布 + channel から joint 構成。**`p ⊗ₘ W`** notation。
- `MeasureTheory.Measure.compProd_const`: `μ ⊗ₘ (Kernel.const _ ν) = μ.prod ν`.
- `ProbabilityTheory.Kernel.pi` (existence in Mathlib needs confirm): product kernel `(Fin n → α) → Measure (Fin n → β)`. Loogle で `Kernel.pi` 不在 → 自作必要かも。代替: `Kernel.prod` を畳む or `MeasureTheory.Measure.pi` を kernel化。

### KL divergence

- `klDiv (μ ν : Measure α) : ℝ≥0∞` (`Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57`)
- `klDiv_compProd_eq_add` (`Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:204`): joint KL 加法性。
- `klDiv_compProd_left` (`Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:182`): `klDiv (μ ⊗ κ) (ν ⊗ κ) = klDiv μ ν` (`@[simp]`).
- `klDiv_map_measurableEquiv` (自作, `MutualInfo.lean:52`).
- `klDiv_prod_const_left` (自作, `MutualInfo.lean:80`).

### 確率収束 + AEP

- 既存 `typicalSet_prob_tendsto_one` (`AEP.lean:375`): X 単独 AEP。**Joint AEP では `(X,Y)` を 1 つの RV に潰し再利用**。
- `tendstoInMeasure_of_tendsto_ae`: a.s. ⇒ in-probability.
- `strong_law_ae_real` (Mathlib): LLN.

## Common2026 内 利用予定 API

### `Common2026/Shannon/MIChainRule.lean` (B-7、本シードの直接前段)

- **`mutualInfo_iid_eq_nsmul`** (`MIChainRule.lean:387`) ★中核★

  ```lean
  theorem mutualInfo_iid_eq_nsmul
      {n : ℕ} (hn : 0 < n)
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
      (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
      (h_iid_joint : μ.map (fun ω (i : Fin n) => (Xs i ω, Ys i ω))
                        = Measure.pi (fun i => μ.map (fun ω => (Xs i ω, Ys i ω))))
      (h_iid_X : μ.map (fun ω (i : Fin n) => Xs i ω)
                    = Measure.pi (fun i => μ.map (Xs i)))
      (h_iid_Y : μ.map (fun ω (i : Fin n) => Ys i ω)
                    = Measure.pi (fun i => μ.map (Ys i)))
      (h_copy : ∀ i, μ.map (fun ω => (Xs i ω, Ys i ω))
                        = μ.map (fun ω => (Xs ⟨0, hn⟩ ω, Ys ⟨0, hn⟩ ω)))
      (h_copy_X : ∀ i, μ.map (Xs i) = μ.map (Xs ⟨0, hn⟩))
      (h_copy_Y : ∀ i, μ.map (Ys i) = μ.map (Ys ⟨0, hn⟩)) :
      mutualInfo μ (fun ω i => Xs i ω) (fun ω i => Ys i ω)
        = n • mutualInfo μ (Xs ⟨0, hn⟩) (Ys ⟨0, hn⟩)
  ```

  本シードの Phase D で `I(X^n; Y^n) = n · I(X; Y)` を 1 行 reduction。

- `mutualInfo_pi_eq_sum` (`MIChainRule.lean:336`): 一般 product joint での MI 加法性。i.i.d. 仮定なし版。
- `klDiv_pi_eq_sum` (`MIChainRule.lean:268`): KL の `Measure.pi` 上加法性。**Phase B-(b) で `K(p^n × q^n ‖ p×q^n) = …` を分解する際に有用**。
- `klDiv_prod_eq_add` (`MIChainRule.lean:249`): 2-product KL。
- `mutualInfo_map_left_measurableEquiv` / `mutualInfo_map_right_measurableEquiv` (`MIChainRule.lean:38, 70`): reshape 不変性。

### `Common2026/Shannon/AEP.lean`

- **`typicalSet`** (`AEP.lean:229`): 単独 typical set。Joint typical では `Fin n → (α × β)` を 1 軸に潰せばそのまま。
- **`typicalSet_card_le`** (`AEP.lean:257`): `|T_ε^n| ≤ exp(n(H+ε))`. 同上で joint typical の size bound に転用可。
- **`typicalSet_prob_tendsto_one`** (`AEP.lean:375`): `P(jointRV ∈ T_ε^n) → 1`. 同上で joint AEP に転用可。
- `jointRV` (`AEP.lean:55`): `(Xs 0 ω, Xs 1 ω, …, Xs (n-1) ω) : Fin n → α`.
- `pmfLog` / `logLikelihood` / `aep_ae` / `aep_inProbability`: 確率収束 plumbing。
- `entropy_jointRV_eq_n_smul` (`AEP.lean:527`): `H(X^n) = n · H(X_0)` for i.i.d.

### `Common2026/Shannon/MutualInfo.lean`

- `mutualInfo (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞` (`MutualInfo.lean:36`)
- `mutualInfo_nonneg`, `mutualInfo_comm`, `mutualInfo_eq_zero_iff_indep`, `mutualInfo_ne_top` (有限 alphabet)
- `klDiv_map_measurableEquiv`, `klDiv_prod_const_left`

### `Common2026/Shannon/Converse.lean` (双対参照)

- `errorProb` の単一形 (`InformationTheory.MeasureFano.errorProb`): block 版で再利用可。
- `shannon_converse_single_shot` (`Converse.lean:81`): 「`log|M| ≤ I + h(P_e) + P_e · log(|M|-1)`」converse。本シード achievability の **双対**: encoder 付き形 (`shannon_converse_single_shot_injective_encoder`, `shannon_converse_single_shot_markov_encoder`) を見ると、encoder/decoder の Lean 化形が分かる。

### `Common2026/Fano/Measure.lean` (errorProb)

- `MeasureFano.errorProb (μ : Measure Ω) (Msg : Ω → M) (Yo : Ω → Y) (decoder : Y → M) : ℝ` — `μ.real {ω | Msg ω ≠ decoder (Yo ω)}` 形。**Block code の `errorProb` も同型で書ける** (Msg = m ∈ Fin M, Yo = (Fin n → β)).

## 設計上の重要ポイント

### 1. Channel をどう表現するか

候補:
- (A) `Channel α β := ProbabilityTheory.Kernel α β`: Mathlib 既存。`klDiv_compProd_*` がそのまま使える。
- (B) ad-hoc `α → Measure β` + measurability hypothesis: Mathlib との互換性低下、補題を自前で書く。

**判断: (A) 採用**。channel = kernel と alias し、`[IsMarkovKernel W]` を type class で要請。

### 2. Memoryless extension `W^n` の構成

`W : Kernel α β` (1-symbol) から `W^n : Kernel (Fin n → α) (Fin n → β)` を作る。
候補:
- (A) `Kernel.pi` を Mathlib で探す → 不在の可能性 (要確認)
- (B) 自前で `(Kernel.const ... W)` の繰り返し畳み込み + `Kernel.prodMkLeft` で構成
- (C) Joint product measure 形 `Measure.pi (i ↦ W (x i))` を kernel に包む

**判断**: まず (C) を Phase A で試す。Joint distribution `joint : Measure ((Fin n → α) × (Fin n → β)) := (p^n).compProd W^n` を直接 `Measure.pi (i ↦ (p ⊗ W))` の reshape として書ければ Kernel.pi 不要。

### 3. Code structure 定義

```lean
structure Code (M n : ℕ) (α β : Type*) where
  encoder : Fin M → (Fin n → α)
  decoder : (Fin n → β) → Fin M
  encoder_meas : Measurable encoder  -- Fin M 有限なので自動
  decoder_meas : Measurable decoder  -- Fin n → β 上の決定論関数
```

`Fin M`, `Fin n → β` は両者 measurable space 自動 (Fintype × MeasurableSingletonClass)、`encoder_meas` / `decoder_meas` フィールドは省略可。

### 4. 主定理 statement の rate 表現

候補:
- (A) `M = ⌈2^{nR}⌉` を natural number で。`Nat.ceil` 経由。
- (B) Rate `R = (log M)/n` を結論側で書く。Code 定義を `M, n` パラメータのままにして、`Real.log M < n · I_p - n · ε` で制約。

**判断: (B) 採用**。`Nat.ceil` plumbing を避ける。statement は「`Real.log M / n < I_p` ⟹ ∃ code, P_err < ε for large n」.

### 5. Phase B (jointly typical) の組み立て

3 つの条件 (X-typical, Y-typical, (X,Y)-typical) の交叉。各 typical condition は `AEP.lean` の `typicalSet` で構築済。**Joint typical set = X軸 typical ∩ Y軸 typical ∩ (X,Y)軸 typical** という 3 つの集合の交叉と書くと、`typicalSet_prob_tendsto_one` を 3 回適用 + `Tendsto.mul` (3 確率の積が `(1-δ)^3 → 1`) または union bound (`P(¬A₁ ∪ ¬A₂ ∪ ¬A₃) ≤ ∑ P(¬Aᵢ)` で `1-3δ`) で (a) が出る。

### 6. Phase B-(c) 独立対の上界

Cover-Thomas 7.6.1 (e):
`P((X̃^n, Y^n) ∈ A_ε^n) ≤ |A_ε^n| · 2^{-n(H(X)-ε)} · 2^{-n(H(Y)-ε)}`
   `≤ 2^{n(H(X,Y)+ε)} · 2^{-n(H(X)+H(Y)-2ε)}`
   `= 2^{-n(I(X;Y)-3ε)}`

ここで `|A_ε^n| ≤ 2^{n(H(X,Y)+ε)}` (size bound (b)), `P(X̃^n = x^n) ≤ 2^{-n(H(X)-ε)}` (typical → low prob lower bound, AEP の **下界** 補題が要る) を組み合わせる。

**注意**: `typicalSet_prob_tendsto_one` の現状は上界 `|T| ≤ exp(n(H+ε))` のみ。下界 `P(x^n) ≤ exp(-n(H-ε))` (point-wise) は別補題が必要。**`AEP.lean` に既存？** 要確認。
