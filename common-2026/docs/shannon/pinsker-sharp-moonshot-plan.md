# シャープ Pinsker 不等式 ムーンショット計画 🌙 (B-5')

<!-- B-5' (deferred from B-5 弱形): docs/moonshot-seeds.md より B-5' 切り出し分を本格 plan 化 -->

> **Parent**: [`pinsker-moonshot-plan.md`](pinsker-moonshot-plan.md) — 弱形 (`TV ≤ √KL`, 定数 1, Bretagnolle-Huber 経路) を完了済。**本 plan は定数を `1/√2` まで強化** (Cover-Thomas 11.6 strict 形 `TV ≤ √(KL/2)`)。
>
> **実態整合 (2026-05-20): DONE-UNCOND** — Phase A〜B 完了。`InformationTheory/Shannon/PinskerSharp.lean:207` の `klFun_sharp_lower` (`∀ t ≥ 0, 3(t-1)² ≤ 2(t+2)·klFun t`) + `PinskerSharp.lean:306` の主定理 `tvNorm_le_sqrt_klDiv_div_two` (`Pinsker.tvNorm P Q ≤ Real.sqrt ((klDiv P Q).toReal / 2)`、定数 1/√2、std binders `hPQ : P ≪ Q`)。0 sorry / 0 `:=True`。実装結果サマリ (line 138 以降) も実態と一致。

## 進捗

- [x] Phase 0 — Mathlib API 在庫 (klFun, MeanValue, log/sqrt) ✅
- [x] Phase A — 点別 sharp Pinsker `2(t+2)·klFun(t) ≥ 3(t-1)²` (`t ≥ 0`) ✅
- [x] Phase B — 有限 alphabet 上 `tvNorm P Q ≤ √((klDiv P Q).toReal / 2)` ✅

## ゴール / Approach

**ゴール**: 有限アルファベット `α` 上の確率測度 `P, Q` (`P ≪ Q`) について
`tvNorm P Q ≤ Real.sqrt ((klDiv P Q).toReal / 2)` を Lean 化。
弱形 (`InformationTheory/Shannon/Pinsker.lean`、定数 1) はそのまま温存し、新規ファイル
`InformationTheory/Shannon/PinskerSharp.lean` で sharp 版を独立 publish。

**Approach** (Csiszár-Kullback-Topsøe 古典経路):

1. **Phase A — 点別不等式** `2(t+2)·klFun(t) ≥ 3(t-1)²` (for `t ≥ 0`):
   - `H(t) := 2(t+2)·klFun(t) - 3(t-1)²` の符号を 3 段で潰す:
   - `H''(t) = 4(log t + 1/t - 1) ≥ 0` for `t > 0`
     (Mathlib `Real.one_sub_inv_le_log_of_pos`: `1 - 1/t ≤ log t` で一行)
   - `H'(1) = 0` ⟹ `H'` は `(0, ∞)` 上 monotone で sign-change at `t = 1`
   - `H(1) = 0` ⟹ `H` は `t = 1` で minimum → `H(t) ≥ 0` for `t > 0`
   - `t = 0` 別途: `H(0) = 4·1 - 3 = 1 ≥ 0`
   - 連続性で `t ≥ 0` 全体に接続

2. **Phase B — 主定理** `tvNorm P Q ≤ √(KL/2)`:
   - 弱形 (`Pinsker.lean`) と同じ MaxEntropy パターン (`withDensity_rnDeriv_eq` + `withDensity_apply` + `lintegral_singleton`) で per-element rnDeriv 識別
   - per-element: `Q.real{x} · klFun(p_x/q_x) ≥ 3(p_x - q_x)² / (2(p_x + 2·q_x))`
     (Phase A を `t := p_x/q_x` に評価、`q_x` 倍で代数整理)
   - Σ: `(klDiv P Q).toReal ≥ Σ x, 3(p_x - q_x)² / (2(p_x + 2·q_x))`
   - Cauchy-Schwarz on `r_x := |p_x - q_x|`, `f_x := (p_x - q_x)²/(p_x + 2·q_x)`, `g_x := p_x + 2·q_x`
     (`Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul`): `(Σ|p-q|)² ≤ (Σ f) · (Σ g)`
   - `Σ g_x = Σ (p_x + 2·q_x) = 1 + 2 = 3` (IsProbabilityMeasure)
   - 統合: `(2 tvNorm)² ≤ 3 · Σ f ≤ 3 · (2/3) · (klDiv).toReal = 2 · KL.toReal`
   - `tvNorm² ≤ KL.toReal / 2` ⟹ `tvNorm ≤ √(KL.toReal/2)` (`Real.le_sqrt_of_sq_le`)

**設計選択**:
- 弱形 (`InformationTheory/Shannon/Pinsker.lean`) を **touch せず並列 publish**。`tvNorm` 定義は弱形と
  名前衝突を避けるため新ファイルでは弱形を **import + re-use** (`Pinsker.tvNorm`)。
- Mathlib に `klFun(t) ≥ 3(t-1)²/(2(t+2))` 形は存在せず (loogle 0 件、`klFun_ge` で始まる sharp
  bound 系がない)、本 plan で独立に証明 → 将来 Mathlib 上流 PR 候補。
- 「Mathlib-shape-driven 定義」の観点では、`klDiv_eq_lintegral_klFun` / `toReal_klDiv_eq_integral_klFun`
  の conclusion form を再利用、定義レベルの新規導入は不要。

## Phase 0 - Mathlib + 既存 API 在庫 ✅

検証済 API:

- `InformationTheory.klFun (x : ℝ) : ℝ := x * log x + 1 - x` (Mathlib `KullbackLeibler/KLFun.lean:53`)
- `InformationTheory.klFun_nonneg`, `klFun_zero`, `klFun_one`, `isMinOn_klFun`
- `InformationTheory.toReal_klDiv_eq_integral_klFun` (Mathlib `KullbackLeibler/Basic.lean`)
- `Real.one_sub_inv_le_log_of_pos`: `0 < x → 1 - x⁻¹ ≤ log x` (`Log/Basic.lean:311`)
  → `log t + 1/t ≥ 1` で `H''(t) ≥ 0` を 1 行
- `Real.hasDerivAt_mul_log`, `Real.deriv_mul_log` (`Log/NegMulLog.lean`)
- `monotoneOn_of_hasDerivWithinAt_nonneg` (`Calculus/Deriv/MeanValue.lean:426`)
- `Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul` (Cauchy-Schwarz 一般形)
- `Real.le_sqrt_of_sq_le`
- 既存 `InformationTheory/Shannon/Pinsker.lean` の `tvNorm` 定義 + 弱形証明

確認済 (loogle 0 件):

- `klFun_ge_sub_sub_one_sq_div`, `klFun_sharp`, `pinsker_sharp` — Mathlib に sharp bound API なし
- 独立に証明する必要あり

## Phase A - 点別 sharp Pinsker `2(t+2)·klFun(t) ≥ 3(t-1)²` ✅

シグネチャ:
```
lemma klFun_sharp_lower (t : ℝ) (ht : 0 ≤ t) :
    3 * (t - 1)^2 ≤ 2 * (t + 2) * klFun t
```

ステップ:

- [ ] **A-1**: `H : ℝ → ℝ := fun t => 2 * (t + 2) * klFun t - 3 * (t - 1)^2` を導入
- [ ] **A-2**: `H_deriv`: `∀ t > 0, HasDerivAt H (4 * ((t + 1) * log t - 2 * (t - 1))) t`
  (`hasDerivAt_mul_log` + 多項式 deriv + 連鎖律)
- [ ] **A-3**: `H'_deriv`: `∀ t > 0, HasDerivAt H' (4 * (log t + 1/t - 1)) t`
  (where `H' := fun t => 4 * ((t + 1) * log t - 2 * (t - 1))`)
- [ ] **A-4**: `H''_nonneg`: `∀ t > 0, 0 ≤ 4 * (log t + 1/t - 1)`
  (`one_sub_inv_le_log_of_pos` ⟹ `1 ≤ log t + 1/t`)
- [ ] **A-5**: `H'_monotoneOn`: `MonotoneOn H' (Set.Ioi 0)`
  (`monotoneOn_of_hasDerivWithinAt_nonneg`)
- [ ] **A-6**: `H'(1) = 0` → `H'(t) ≤ 0` on `(0, 1]`, `H'(t) ≥ 0` on `[1, ∞)`
- [ ] **A-7**: `H_monotoneOn`: `MonotoneOn H [1, ∞)`, `AntitoneOn H (0, 1]`
  (`monotoneOn_of_hasDerivWithinAt_nonneg` × 2)
- [ ] **A-8**: `H(1) = 0` → `H(t) ≥ 0` on `(0, ∞)`
- [ ] **A-9**: `t = 0` 別途: `H(0) = 4 · 1 - 3 = 1 ≥ 0`
- [ ] **A-10**: 結論: `H(t) ≥ 0` for `t ≥ 0`、unfold で `3(t-1)² ≤ 2(t+2)·klFun(t)`

**潜在ハマり**:
- `HasDerivAt` の連鎖律で `(t+2)·klFun(t)` の deriv を組むときに `klFun` の deriv を直接ではなく
  expand して `t·log t + 1 - t` の項別 deriv で組む方が早そう。
- `H'` の 1 次部分 `4*(t+1)*log t - 8*(t-1)` の derivative: `4·log t + 4·(t+1)/t - 8`
  `= 4·log t + 4 + 4/t - 8 = 4·log t + 4/t - 4 = 4·(log t + 1/t - 1)` ← 検算 OK

## Phase B - 主定理 `tvNorm P Q ≤ √(KL/2)` ✅

シグネチャ:
```
theorem tvNorm_le_sqrt_klDiv_div_two
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) :
    Pinsker.tvNorm P Q ≤ Real.sqrt ((klDiv P Q).toReal / 2)
```

ステップ (弱形 `Pinsker.lean` の Step 1-7 と並列):

- [ ] **B-1** rnDeriv 識別 (弱形と同一): `(P.rnDeriv Q x) * Q {x} = P {x}`
- [ ] **B-2** `KL.toReal = Σ x, Q.real{x} · klFun((P.rnDeriv Q x).toReal)` (弱形と同一)
- [ ] **B-3** per-element sharp:
  `Q.real{x} · klFun((P.rnDeriv Q x).toReal) ≥ 3·(p_x - q_x)² / (2·(p_x + 2·q_x))`
  - `Q.real{x} = 0` ⟹ `p_x = 0` (AC) で両辺 0
  - `Q.real{x} > 0`: `t := p_x/q_x` で Phase A 適用、`q_x` 倍で代数整理
  - 代数: `q · 3(p/q - 1)²/(2(p/q + 2)) = 3(p-q)²·q / (2q·(p/q + 2)) = 3(p-q)² / (2(p + 2q))`
    (注意: `q · 2(p/q + 2)·klFun(p/q) = 2(p + 2q)·q·klFun(p/q)`、整理: `q·(p/q - 1)² = (p-q)²/q` で `q · 3(p-q)²/(2q(p+2q)) = 3(p-q)²/(2(p+2q))`)
- [ ] **B-4** Σ: `(klDiv).toReal ≥ Σ x, 3·(p_x - q_x)² / (2·(p_x + 2·q_x))`
- [ ] **B-5** Cauchy-Schwarz (`Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul`):
  - `r_x := |p_x - q_x|`, `f_x := (p_x - q_x)²/(p_x + 2·q_x)`, `g_x := p_x + 2·q_x`
  - 検証 `r_x² = f_x · g_x`: `(p_x - q_x)² = (p_x - q_x)²/(p_x + 2·q_x) · (p_x + 2·q_x)` (定義域で `p_x + 2·q_x > 0` のとき、`= 0` のときも両辺 0)
  - 結論: `(Σ|p-q|)² ≤ (Σ f) · (Σ g)`
- [ ] **B-6** `Σ g_x = Σ (p_x + 2·q_x) = 1 + 2·1 = 3` (IsProbabilityMeasure)
- [ ] **B-7** 統合: `(2·tvNorm)² = (Σ|p-q|)² ≤ 3·Σ f`, `Σ f ≤ (2/3)·KL.toReal` (Step B-4)
  → `(2·tvNorm)² ≤ 3·(2/3)·KL = 2·KL`
  → `4·tvNorm² ≤ 2·KL` → `tvNorm² ≤ KL/2` → `tvNorm ≤ √(KL/2)`

**潜在ハマり**:
- `f_x · g_x = r_x²` の検証で `q_x + 2·p_x = 0` (i.e., `p_x = q_x = 0`) 場合の zero division を
  if-then-else で扱う必要あり。0 の場合 `f_x := 0` と定義する自然な split で進める。
- `Real.sqrt` の単調性 (`Real.sqrt_le_sqrt` / `Real.le_sqrt_of_sq_le`) を最後にかける。

## 実装結果サマリ (2026-05-12 完了)

- **ファイル**: `InformationTheory/Shannon/PinskerSharp.lean` (429 行、新規)。弱形 `Pinsker.lean` (310 行) は
  touch せず並立 publish。`tvNorm` 定義は弱形 namespace (`InformationTheory.Shannon.Pinsker.tvNorm`)
  からそのまま再利用。
- **公開した主補題**:
  - `klFun_sharp_lower : ∀ t ≥ 0, 3 * (t - 1)^2 ≤ 2 * (t + 2) * klFun t` (点別 sharp Pinsker)
  - `tvNorm_le_sqrt_klDiv_div_two : tvNorm P Q ≤ Real.sqrt ((klDiv P Q).toReal / 2)`
    (主定理、有限 alphabet 上で `P ≪ Q` 確率測度に対し)
- **検証**: `lake env lean InformationTheory/Shannon/PinskerSharp.lean` clean (0 error / 0 warning / 0 sorry)。
- **Phase A 実装ノート**:
  - 当初 plan 通り `H(t) := 2(t+2)·klFun(t) - 3(t-1)²` の 3 段微分サインチェインで完走。Mathlib
    `Real.one_sub_inv_le_log_of_pos` (`1 - 1/t ≤ log t` for `t > 0`) のおかげで `H''(t) ≥ 0` が
    実質 2 行で出る。
  - `HasDerivAt` の連鎖律は `hasDerivAt_klFun` (Mathlib `KLFun.lean:89`) を直接使い、
    `klFun` を unfold せずに済む経路を採用。微分の閉形式 `Hderiv`, `Hderiv2` を独立 private def 化。
  - `MonotoneOn`/`AntitoneOn` は `monotoneOn_of_hasDerivWithinAt_nonneg` /
    `antitoneOn_of_hasDerivWithinAt_nonpos` で `f' := Hderiv`/`Hderiv2` を明示指定し、
    interior の rewrite (`interior_Ici` / `interior_Ioc`) で plumbing。
- **Phase B 実装ノート**:
  - per-element 不等式の rnDeriv 識別 + `Q.real{x} = 0` ケース分岐は弱形 `Pinsker.lean` と
    同一パターンを再現。`field_simp` + `linarith` で代数を潰し、`q · (t-1) = p - q`,
    `q · (t+2) = p + 2q` 経由で sharp 不等式を `(p-q)²` / `(p+2q)` 形に整理。
  - Cauchy-Schwarz は `Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul` で `r := |p-q|`,
    `f := (p-q)²/(p+2q)`, `g := p+2q` のセットアップ。`p+2q = 0` 場合 (`p = q = 0`) の zero
    division は `by_cases` で両辺 0 に潰す。
  - `Σ g = ∑ x, (p_x + 2·q_x) = 1 + 2 = 3` は `IsProbabilityMeasure` の `sum_measureReal_singleton`
    + `measure_univ` で。
- **Mathlib 上流 PR 切り出し可能性**: `klFun_sharp_lower` は `Mathlib.InformationTheory.KullbackLeibler.KLFun`
  の純粋拡張 (定義 `klFun` のみに依存、他の InformationTheory シードへの依存なし)。`H` / `Hderiv` /
  `Hderiv2` を `private` 化して `klFun_sharp_lower` だけ public で出せば、独立 PR として
  Mathlib に提案可能。Phase B (`tvNorm_le_sqrt_klDiv_div_two`) は `tvNorm` 定義を Mathlib 風に
  整える (`MeasureTheory.tvDist` 等の既存 API があれば置換) 必要があるが、Phase A 部分のみで
  もアップストリーム価値あり。
- **不確定 / 妥協**: なし。当初 plan 通り定数 `1/√2` を達成、特殊ケース回避や仮定強化はなし。
