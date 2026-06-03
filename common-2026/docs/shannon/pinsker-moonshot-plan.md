# Pinsker 不等式 ムーンショット計画 🌙 (B-5)

<!-- B-5 シード: docs/moonshot-seeds.md より複製・膨らませ -->

> **実態整合 (2026-05-20): DONE-UNCOND (弱形に着地)** — Phase A〜B 完了。`InformationTheory/Shannon/Pinsker.lean:118` の `tvNorm_le_sqrt_klDiv` が **弱形** `tvNorm P Q ≤ Real.sqrt (klDiv P Q).toReal` (定数 1、Bretagnolle-Huber 経路) を std binders (`hPQ : P ≪ Q` のみ) で discharge、0 sorry / 0 `:=True`。**注**: 本 plan の「ゴール」見出し (line 13) と Phase B シグネチャ block (line 105) は sharp 形 `√(klDiv/2)` を記載しており stale; 実際の定理は判断ログ pivot 2 通り弱形。sharp 形は `pinsker-sharp-moonshot-plan.md` (`PinskerSharp.lean`) で別途達成済。

## 進捗

- [x] Phase 0 — Mathlib + 既存 InformationTheory API インベントリ ✅ → [pinsker-mathlib-inventory.md](pinsker-mathlib-inventory.md)
- [x] Phase A — 点別補題 (`Real` レベル, **Bretagnolle-Huber 形へ pivot**): `(√t - 1)^2 ≤ klFun t` for t ≥ 0 ✅
- [x] Phase B — 有限 alphabet 上の TV 定義 + Cauchy-Schwarz 経由の主定理 (**弱定数 `TV ≤ √KL`**) ✅

## ゴール / Approach

**ゴール**: 有限アルファベット `α` 上の確率測度 `P, Q` (`P ≪ Q`) について
`tvNorm P Q ≤ Real.sqrt (klDiv P Q).toReal` を Lean 化。
ここで `tvNorm P Q := (1/2) * ∑ x, |P.real {x} - Q.real {x}|`。

**Approach** (Csiszár-style elementary 形、Cover-Thomas 11.6 と同骨格・**定数 √2 ゆるい**):

シャープな `TV ≤ √(KL/2)` (Cover-Thomas 11.6 の strict 形) を目指す場合、点別不等式
`klFun(t) ≥ 3(t-1)^2 / (2(t+2))` が必要で、これは三階微分 `4(t-1)/t^2` を経由する
モノトニシティ階段が必要 (~150-200 行の calculus)。本シードでは時間最適化のため、
**点別不等式を `klFun(t) ≥ (t-1)^2 / (2(t+1))` に弱め**、`TV ≤ √(KL)` (定数 1) で commit。

ギャップ補正は B-5' (後続またはアップストリーム PR) で行う。Sanov / Strong Stein など下流の
qualitative 用途では定数の √2 違いは効かない (rate function の存在性自体は同等)。

1. **Phase A (Real-only)**: 点別不等式
   `2 (t + 1) * klFun(t) ≥ (t - 1)^2` for all `t ≥ 0`
   を `H(t) := 2(t+1)*klFun(t) - (t-1)^2` の二階微分の非負性で証明。
   - `H(1) = 0, H'(1) = 0`
   - `H''(t) = 4 log t + 2/t` ≥ 0 for `t > 0` (use `Real.log_le_sub_one_of_pos` 系)
   - `H'' ≥ 0` + 既知の `MeanValue` で `H ≥ 0` on `[0, ∞)`。

2. **Phase B**: discrete Pinsker (`TV ≤ √KL`)
   - 有限 alphabet 上で `tvNorm` を定義。
   - per-element: `Q.real{x} * klFun(P.real{x}/Q.real{x}) ≥ (P.real{x} - Q.real{x})^2 / (2 (P.real{x} + Q.real{x}))`
   - 和: `(klDiv P Q).toReal ≥ (1/2) * Σ (p_x - q_x)^2 / (p_x + q_x)` (rnDeriv 経由、`MaxEntropy.lean` 同型のパターン)
   - Cauchy-Schwarz (`Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul` with `r_x := |p-q|`, `f_x := (p-q)^2/(p+q)`, `g_x := p+q`):
     `(Σ|p-q|)^2 ≤ (Σ (p-q)^2/(p+q)) * (Σ (p+q)) = (Σ (p-q)^2/(p+q)) * 2`
   - よって `(2 tvNorm)^2 = (Σ|p-q|)^2 ≤ 2 * 2 (klDiv P Q).toReal = 4 (klDiv P Q).toReal`
   - `tvNorm^2 ≤ (klDiv P Q).toReal` ⟹ `tvNorm ≤ √(klDiv P Q).toReal` (`Real.le_sqrt_of_sq_le`)

`MaxEntropy.lean` で確立した「Bochner per-point rnDeriv identification」パターン (`withDensity_rnDeriv_eq` + `withDensity_apply` + `lintegral_singleton`) で per-element 展開、`(P.rnDeriv Q x).toReal = P.real{x} / Q.real{x}` を導出。`klDiv_discrete_toReal_eq_sum` は private なので inline で展開。

## Phase 0 - Mathlib + 既存 API Inventory 📋 → [pinsker-mathlib-inventory.md](pinsker-mathlib-inventory.md)

主な検証済 API:

- `InformationTheory.klFun (x : ℝ) : ℝ := x * log x + 1 - x` (KullbackLeibler/KLFun.lean:53)
- `InformationTheory.toReal_klDiv_of_measure_eq` (KullbackLeibler/Basic.lean:164)
- `MeasureTheory.Measure.withDensity_rnDeriv_eq` / `withDensity_apply` / `lintegral_singleton`
- `Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul` (Algebra/Order/BigOperators/Ring/Finset.lean:126) — Cauchy-Schwarz の一般形
- `Real.le_sqrt`, `Real.le_sqrt_of_sq_le`, `Real.sqrt_le_iff`
- 既存 `InformationTheory/Shannon/MaxEntropy.lean` の Bochner per-point rnDeriv パターン

確認済 (loogle 0 件):

- `Pinsker`, `tvNorm`, `hellinger`, `dataProcessing`, `logSum` — Mathlib に専用 API なし
- ⟹ TV norm は本ファイル内で `def tvNorm` を新規定義 (`(1/2) * Σ|p - q|` Finset 和形)。

## Phase A - 点別 Pinsker (Real-only) 📋

シグネチャ:
```
private lemma klFun_ge_quad_lower (t : ℝ) (ht : 0 ≤ t) :
    (t - 1)^2 / (2 * (t + 1)) ≤ klFun t
```

(`t = -1` のときの 0 除算は問題にならない — `t ≥ 0` で `t+1 ≥ 1`。)

ステップ (`H(t) := 2*(t+1)*klFun(t) - (t-1)^2 ≥ 0` ルート):
- [ ] `t = 0` 別途: `H(0) = 2*1*1 - 1 = 1 ≥ 0`
- [ ] `t > 0` 一般:
  - [ ] `H'(t) = 2*klFun(t) + 2*(t+1)*log(t) - 2*(t-1)` (微分計算)
  - [ ] `H''(t) = 4*log(t) + 2/t` (微分計算)
  - [ ] `H''(t) ≥ 0` on `(0, ∞)`: at `t = 1`: `0 + 2 = 2 > 0`; 
    - for `t ≥ 1`: `log t ≥ 0` ⟹ trivial
    - for `t ∈ (0, 1)`: 補題 `4 log t + 2/t ≥ 0` ⟺ `2/t ≥ -4 log t = 4 log(1/t)` ⟺ `1/(2t) ≥ log(1/t)`、置換 `u := 1/t ≥ 1`: `u/2 ≥ log u`、これは `Real.log_le_self` (`log u ≤ u`) と `u ≥ 1` から従う (もしくは `log_le_sub_one_of_pos` で `log u ≤ u - 1 ≤ u/2` when `u ≤ 2`、unfortunately for `u > 2` need separate; 別案 `Real.log_le_self` で `log u ≤ u`、欲しいのは `log u ≤ u/2` で **緩めの版**は不要、別ルート: `4 log t + 2/t ≥ 0 ⟺ 8 t log t + 4 ≥ 0` for `t > 0`; on `(0, 1)`: `8 t log t` → 0 as t → 0, ≥ -2 at minimum (t = 1/e), so `8 t log t + 4 ≥ -8/e + 4 ≈ 1.06 > 0` ✓. これを `Real.mul_log_ge_negTwoOver_e` 風で示すか、直接 `Real.log_le_self` で `t log t ≤ t · 0` for `t ∈ (0, 1]` の下界がない、別検討。
- [ ] **代替フォールバック**: `H''(t) ≥ 0` の直接 calculus を避けて、`klFun` の `convexOn_klFun` + 接線 `klFun(t) ≥ klFun(1) + klFun'(1)*(t-1) = 0` の二次補正版を使う ⟶ 既知 Mathlib API では不可。
- [ ] **採用ルート**: `H''(t) ≥ 0` を直接示し、`MeanValue.monotoneOn_of_deriv_nonneg` で `H' ≥ 0 on [1,∞)`, `H' ≤ 0 on (0, 1]`、再度同 lemma で `H ≥ 0 on [0, ∞)`。

実装オプション: 二階微分非負性 `H''(t) ≥ 0` で頻発するのは `t log t ≥ -1/e` 型の bound。最速ルートはたぶん `Real.log_le_self` (log u ≤ u) を `u = 1/t` で適用して `1/t * log(1/t) ≤ 1/t * 1/t = 1/t^2`... ハマるので、まず一階形:

**最終ルート**: `klFun_ge_quad_lower` を `H` 経由ではなく、もっと elementary な path で示す:
- `klFun(t) = t*log(t) + 1 - t`
- `(t-1)^2 / (2(t+1)) = (t-1)/2 * (t-1)/(t+1) = ...`
- 既存 `Real.self_sub_one_le_mul_log` (`x - 1 ≤ x * log x`) を `x = t` で適用 → `klFun(t) ≥ 0` (弱い)
- **強化**: `(t-1)/(t+1) ≤ log t / 2` ?? at t=2: log 2 / 2 ≈ 0.347, (1)/(3) ≈ 0.333. ✓ at t=4: log 4 / 2 ≈ 0.693, 3/5 = 0.6. ✓ Padé approximant: `log t ≥ 2(t-1)/(t+1)` for `t ≥ 1` (true, well-known). 検索: Mathlib?

**フォールバック**: もし Phase A の log 微分系が深くなりすぎる場合、defer 全体 (plan ファイルで切り出し方向記録 → 上流 PR or 後続 B-5' で再着手)。

## Phase B - 有限 alphabet TV + 主定理 📋

定義:
```
noncomputable def tvNorm (P Q : Measure α) : ℝ :=
  (1/2) * ∑ x : α, |P.real {x} - Q.real {x}|
```

シグネチャ:
```
theorem tvNorm_le_sqrt_klDiv_div_two
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) :
    tvNorm P Q ≤ Real.sqrt ((klDiv P Q).toReal / 2)
```

ステップ:
- [ ] 補題: `toReal_klDiv_per_element_lower`: `(klDiv P Q).toReal ≥ Σ x, 3*(p_x - q_x)^2 / (2*(p_x + 2*q_x))`
  (MaxEntropy パターン: `toReal_klDiv_of_measure_eq` + `integral_fintype` + per-point rnDeriv id + Phase A 適用)
- [ ] 補題: `Σ_x (p_x + 2*q_x) = 3` (有限和 + IsProbabilityMeasure)
- [ ] Cauchy-Schwarz step: `(2 * tvNorm P Q)^2 = (Σ|p-q|)^2 ≤ 3 * Σ (p-q)^2/(p+2q)`
  (`Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul` w/ f = (p-q)^2/(p+2q), g = (p+2q), r = |p-q|)
- [ ] 統合: `(2 * tvNorm)^2 ≤ 2 * (klDiv).toReal`
- [ ] sqrt 化: `tvNorm ≤ √((klDiv).toReal / 2)` (`Real.le_sqrt_of_sq_le` + 算術)

**エッジケース**: `q_x = 0` の場合 (P ≪ Q なので `p_x = 0` も automatic、両辺 0)。`p_x + 2*q_x = 0` も同時、Cauchy-Schwarz は `f_i = 0` の項を skip。

## 判断ログ

- **(計画時点 2026-05-11)** DPI / log-sum 不等式 Mathlib に**なし**を確認したため、binary Pinsker 経由は採らず、Csiszár 形の **点別 Cauchy-Schwarz** 経路で組む。Csiszár-Kullback の `3(t-1)^2/(2(t+2))` lower bound が右の点別不等式。等号は t = 1 (P = Q)。

- **(実装中 2026-05-11 pivot 1)**: 計画した `klFun(t) ≥ (t-1)^2/(2(t+1))` 形は二階微分 `H''(t) = 4 log t + 2/t ≥ 0` の non-trivial calculus を要する (特に `t ∈ (0, 1)` 側で `4 log t + 2/t ≥ 0 ⟺ 2 t log t ≥ -1` を経由、Mathlib に `t log t ≥ -1/e` 系の bound 無し)。tactical な calculus 経路は 100-150 行見積、線形でない labor。**Bretagnolle-Huber 経路に pivot**: 算術恒等式 `klFun(t) = (1-√t)^2 + 2√t·klFun(√t)` から `klFun(t) ≥ (√t - 1)^2` (Phase A 5 行)。

- **(実装中 2026-05-11 pivot 2)**: Bretagnolle-Huber 経路だと Cauchy-Schwarz は `|p-q| = |√p - √q| · (√p + √q)` で展開し、`Σ(√p + √q)^2 ≤ 4` (AM-GM 由来) を使う。結果は `TV ≤ √(KL)` (定数 1)、シャープな `TV ≤ √(KL/2)` (定数 1/√2) より √2 ゆるい。下流の Sanov / Strong Stein の qualitative 用途には影響なし。**シャープ版は B-5' (将来) の Mathlib 上流 PR で再着手**。

## 後続シードへの引き継ぎ

- **B-1 (Sanov)** で使う場合: 本シードの `tvNorm_le_sqrt_klDiv` で十分。Sanov の rate function は `klDiv` で書かれており、Pinsker の定数は qualitative 結果 (LDP の rate function 同一性) に効かない。
- **B-4 (Strong Stein)** で使う場合: シャープ Pinsker `TV ≤ √(KL/2)` を要する場合は B-5' で先取り強化が必要だが、`(1+o(1))` factor の議論には弱形でも十分のことが多い。
- **将来の B-5' (シャープ化)**: 鍵は `klFun(t) ≥ 3(t-1)^2/(2(t+2))` の calculus 形式化。`monotoneOn_of_deriv_nonneg` 三段または `t log t ≥ -1/e` の補助補題を Mathlib に PR する経路が見える。
