# AWGN converse: C-1c Jensen affine substitution mini-plan

> **Parent**: [`awgn-converse-aux-plan.md`](awgn-converse-aux-plan.md) §「Phase C 失敗時 fallback (line 905-908)」 / 判断ログ #6「後続セッション送り (2)」
>
> **Slug**: `awgn-converse-c1c-jensen`
>
> **対象 sorry**: `Common2026/Shannon/AWGNConverseDischarge.lean:624` `sum_log_one_add_le_n_log_one_add_avg`、現タグ `@residual(plan:awgn-converse-aux-plan)` (`wall:jensen-affine-subst` 想定での Phase C retreat)
>
> **Status (2026-05-27)**: 起草。Phase C dispatch (Wave 6) で `ConcaveOn.le_map_sum` の affine substitution 段 (`smul`/`mul` normalization friction) が実装中に発火、`sorry` retreat で commit。本 mini-plan は後続 1 session でその sorry を analytic body で discharge する。

## 進捗

- [ ] Phase 0 — Mathlib API verbatim 在庫 + 候補 (i/ii/iii) 確定 ✅ (本 mini-plan 内で完了済、§Mathlib 在庫確認)
- [ ] Phase 1 — `Real.log (1 + x/N)` 専用 concavity 補題追加 (option (ii) 採用、`DifferentialEntropy.lean` への ~20 行 helper) 📋
- [ ] Phase 2 — `sum_log_one_add_le_n_log_one_add_avg` body fill (Jensen 適用 + uniform weight 1/n 算術 ~30-50 行) 📋
- [ ] Phase V — verify + tag 解消 + handoff 📋

## ゴール / Approach

### Goal (target signature、verbatim)

`Common2026/Shannon/AWGNConverseDischarge.lean:624-637` の `sorry` を埋める:

```lean
theorem sum_log_one_add_le_n_log_one_add_avg
    {n : ℕ} (hn_pos : 0 < n)
    (N : ℝ) (hN_pos : 0 < N)
    (xs : Fin n → ℝ) (hxs_nn : ∀ i, 0 ≤ xs i) :
    ∑ i : Fin n, (1 / 2) * Real.log (1 + xs i / N)
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + ((1 / (n : ℝ)) * ∑ i : Fin n, xs i) / N)) := by
  …  -- 完成形では 0 sorry / 0 @residual
```

signature 改変なし (引数 5 件維持)。bundle predicate / load-bearing hypothesis 追加禁止 (本補題は **algebraic concavity** であり Mathlib 内 closure 可能、staged 化禁止)。

### Approach (overall strategy / shape of solution)

**採用候補: (ii) `Real.log (1 + x/N)` 専用 concavity 補題を `DifferentialEntropy.lean` に追加してから sum-form に適用**。

3 候補比較 (verbatim 確認後、§Mathlib 在庫確認参照):

| 候補 | 戦略 | composition friction | 採否 |
|---|---|---|---|
| (i) | `ConcaveOn.comp_affineMap` で `Real.log ∘ (x ↦ 1 + x/N)` を直接組み、`ConcaveOn.le_map_sum` を呼ぶ | `→ᵃ[ℝ]` affine map を構築 (`AffineMap.const + AffineMap.linear (1/N)`) → `(g ⁻¹' Ioi 0)` の membership unfold (`1 + x/N ∈ Ioi 0` ⇔ `0 ≤ x` 程度の inequality plumbing) — Phase C dispatch agent はここで `smul`/`mul` normalization friction に詰まった (proof-log 観察) | 不採用 (friction 既知) |
| (ii) | `Real.log (1 + x/N)` の `ConcaveOn ℝ (Ici 0) (fun x => Real.log (1 + x/N))` を別 helper 補題化 (`DifferentialEntropy.lean` に追加、~20 行)、本体は `ConcaveOn.le_map_sum` を uniform weight `wᵢ := 1/n` で呼ぶだけ | helper 1 件で friction を吸収、本体は mechanical (Phase 0 verbatim 確認で 1/n + Ici 0 + smul = mul の slot 整合 OK) | **採用** |
| (iii) | `Real.add_pow_le_pow_mul_pow_of_sq` 等 power-mean inequality 経由で affine substitution を回避 | log は AM ≥ GM 由来 (`Real.geom_mean_le_arith_mean*`) で組めるが、`log(1+x/N)` は単純 GM-AM 形に乗らない (`+1` のシフトで base が変わる)、特殊 transformation 必要 | 不採用 (本問題に直接 fit する Mathlib power-mean 補題が無い) |

**(ii) の構造** (Phase 1 + 2 の 2 段):

```
Phase 1: DifferentialEntropy.lean (or new file) に helper 追加 (~20 行)
─────────────────────────────────────────────────────────────────────
  theorem concaveOn_log_one_add_div {N : ℝ} (hN_pos : 0 < N) :
      ConcaveOn ℝ (Ici (0 : ℝ)) (fun x => Real.log (1 + x / N)) := by
    -- `f := Real.log ∘ g` where `g x := 1 + x / N` is affine (slope 1/N > 0)
    -- `strictConcaveOn_log_Ioi.concaveOn` ↦ `ConcaveOn ℝ (Ioi 0) Real.log`
    -- `g` maps `Ici 0` into `Ioi 0` since `1 + x/N ≥ 1 > 0`
    -- (a) build `g` as `AffineMap.const ℝ ℝ 1 + (1/N) • AffineMap.id` (or simpler:
    --     `LinearMap.toAffineMap (smul N⁻¹) + const 1`)
    -- (b) apply `ConcaveOn.comp_affineMap`
    -- (c) preimage `g ⁻¹' (Ioi 0) ⊇ Ici 0` (since `g(Ici 0) ⊆ Ici 1 ⊆ Ioi 0`)
    -- (d) widen to `Ici 0` via `ConcaveOn.subset` (Mathlib `ConcaveOn.subset` 既存)

Phase 2: AWGNConverseDischarge.lean:624 本体 (~30-50 行)
─────────────────────────────────────────────────────────────────────
  - `f := fun x => Real.log (1 + x / N)`、 `hf := concaveOn_log_one_add_div hN_pos`
  - weights `w : Fin n → ℝ := fun _ => (1 : ℝ) / n`、`points p := xs`
  - h₀ : `∀ i ∈ Finset.univ, 0 ≤ (1/n)` ← `by positivity` (`hn_pos` から `(n : ℝ) > 0`)
  - h₁ : `∑ i, (1/n) = 1` ← `by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin];
                                 field_simp` (`n ≠ 0` 経由)
  - hmem : `∀ i ∈ Finset.univ, xs i ∈ Ici 0` ← `hxs_nn i`
  - **apply** `hf.le_map_sum h₀ h₁ hmem` →
      `∑ i, (1/n) • f (xs i) ≤ f (∑ i, (1/n) • xs i)`
  - `smul = mul` 正規化 (`smul_eq_mul`、`Pi.smul_apply` 不要、`ℝ` scalar)
  - 両辺 `(n : ℝ)` 倍 + `(1/2)` 倍 (positivity) で目標式へ:
        ∑ (1/2) * log(1 + xᵢ/N)
      = (1/2) * ∑ log(1 + xᵢ/N)                    [Finset.mul_sum, 算術]
      = (1/2) * n * (1/n) * ∑ log(1 + xᵢ/N)        [field_simp, n ≠ 0]
      ≤ (1/2) * n * log(1 + ((1/n) * ∑ xᵢ) / N)    [Jensen 結論 × (1/2)·n]
      = n * ((1/2) * log(1 + avg/N))                [ring]
```

**friction 回避の鍵** (Phase C dispatch 失敗の原因仮説):

- `ConcaveOn.le_map_sum` の結論は `∑ i, w i • f (p i) ≤ f (∑ i, w i • p i)` (verbatim、`Jensen.lean:73-75`)。`ℝ` 上で `w i • p i = w i * p i` だが `smul_eq_mul` rewrite を忘れると `field_simp` / `ring` が `smul` を残して詰まる。
- `comp_affineMap` 経路 (候補 (i)) では `(g ⁻¹' Ioi 0)` の membership goal が `1 + x/N ∈ Ioi 0` の形で出てきて、 `Ici 0` への変換に余分な `Convex.subset` plumbing が必要 → 本体内で組むと friction 累積。**helper 補題に切り出すと friction が 1 箇所に集約**され、本体は mechanical chain で済む。
- `(1 / (n : ℝ))` と `Real.log` の domain 制約 (`Ici 0` vs `Ioi 0`) の境界処理: helper 内で `Ici 0 → Ioi 0` の domain widening (`1 + x/N ≥ 1 > 0`) を 1 回だけやれば本体は `xs i ∈ Ici 0` (= `hxs_nn i`) で済む。

### Mathlib-shape-driven 確認 (CLAUDE.md)

`ConcaveOn.le_map_sum` の結論形 `∑ i ∈ t, w i • f (p i) ≤ f (∑ i ∈ t, w i • p i)` と本補題目標形 `∑ (1/2) * log(1 + xᵢ/N) ≤ n · (1/2) · log(1 + avg/N)` の整合:

- `f := fun x => log(1+x/N)`、`p := xs`、`w := fun _ => 1/n`、`t := Finset.univ` で起動
- LHS の `(1/2) *` は Jensen 適用後に外で掛ければよい (constant factor)
- RHS の `(n : ℝ) * (1/2) *` は `n · (1/n) = 1` cancel + `(1/2) *` 外掛けで一致

⇒ Jensen 結論形 verbatim はそのまま流せる、bridge 不要 ✅ (CLAUDE.md「Mathlib-shape-driven Definitions」遵守)

### 規模見積もり (verbatim 在庫済)

| Phase | 内容 | 中央 |
|---|---|---:|
| Phase 1 | `concaveOn_log_one_add_div` helper (`DifferentialEntropy.lean` 追加) | ~20 行 |
| Phase 2 | 本体 `sum_log_one_add_le_n_log_one_add_avg` body fill | ~30-50 行 |
| Phase V | verify + tag 解消 (`@residual` 削除、`AWGNConverseDischarge.lean` 1 sorry 解消) | 0 行 |
| **合計** | | **~50-70 行** |

session 見込: **0.5-1 session** (1 helper + 1 本体、Mathlib API verbatim 確定済)

---

## Mathlib 在庫確認 (verbatim、Phase 0 で確認済)

### A. Jensen 主補題

`Mathlib/Analysis/Convex/Jensen.lean:73-76`:

```lean
/-- Concave **Jensen's inequality**, `Finset.sum` version. -/
theorem ConcaveOn.le_map_sum (hf : ConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    (∑ i ∈ t, w i • f (p i)) ≤ f (∑ i ∈ t, w i • p i) :=
  ConvexOn.map_sum_le (β := βᵒᵈ) hf h₀ h₁ hmem
```

型クラス前提 (file 冒頭 `Jensen.lean:47-49`、**verbatim**):

```lean
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [AddCommGroup β]
  [PartialOrder β] [IsOrderedAddMonoid β] [Module 𝕜 E] [Module 𝕜 β] [IsStrictOrderedModule 𝕜 β]
  {s : Set E} {f : E → β} {t : Finset ι} {w : ι → 𝕜} {p : ι → E} {v : 𝕜} {q : E}
```

本 mini-plan では `𝕜 = ℝ`, `E = β = ℝ` で起動 → 上記型クラス全件自動充足 (`ℝ` 上 `Field + LinearOrder + …` instance 完備)。

### B. `Real.log` concavity 基礎

`Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean:67`:

```lean
/-- `Real.log` is strictly concave on `(0, +∞)`. -/
theorem strictConcaveOn_log_Ioi : StrictConcaveOn ℝ (Ioi 0) log := by
  …
```

`StrictConcaveOn.concaveOn` で `ConcaveOn ℝ (Ioi 0) Real.log` を取れる (Mathlib 慣行)。

### C. Affine 合成 (concavity 保存)

`Mathlib/Analysis/Convex/Function.lean:946-948`:

```lean
/-- If a function is concave on `s`, it remains concave when precomposed by an affine map. -/
theorem ConcaveOn.comp_affineMap {f : F → β} (g : E →ᵃ[𝕜] F) {s : Set F} (hf : ConcaveOn 𝕜 s f) :
    ConcaveOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  hf.dual.comp_affineMap g
```

型クラス前提 (前後文脈、`Function.lean:926-934`、**verbatim**):

```lean
variable [Field 𝕜] [LinearOrder 𝕜] [AddCommGroup E] [AddCommGroup F]
…
variable [AddCommMonoid β] [PartialOrder β]
…
variable [Module 𝕜 E] [Module 𝕜 F] [SMul 𝕜 β]
```

### D. Translation / scalar (補助、Phase 1 で helper 内で使う場合)

`Function.lean:290-303`:

```lean
theorem ConcaveOn.translate_right (hf : ConcaveOn 𝕜 s f) (c : E) :
    ConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) := …

theorem ConcaveOn.translate_left (hf : ConcaveOn 𝕜 s f) (c : E) :
    ConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) := …
```

`Function.lean:914-916`:

```lean
theorem ConcaveOn.smul {c : 𝕜} (hc : 0 ≤ c) (hf : ConcaveOn 𝕜 s f) :
    ConcaveOn 𝕜 s fun x => c • f x := hf.dual.smul hc
```

(注: `ConcaveOn.smul` は image 側 scalar、domain 側 scaling は `comp_affineMap` 経由)

### E. Common2026 既存 concavity 補題在庫 (`DifferentialEntropy.lean`)

`rg -n "strictConcaveOn|concaveOn|ConcaveOn|le_map_sum"` で `DifferentialEntropy.lean` 内に該当補題は **0 件** (Phase 0 grep 結果)。Phase 1 helper は新規追加。

### F. Loogle で「Real.log composition concavity」を確認

`./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "Real.log, ConcaveOn"` — 既存 `Real.log(1 + ·)` / `Real.log(1 + ·/N)` 専用 concavity 補題は **不在** (Phase 0 確認、Mathlib + Common2026 双方)。Phase 1 helper 新規追加で重複なし ✅

---

## Phase 1 — `concaveOn_log_one_add_div` helper 追加 📋

### スコープ

`Common2026/Shannon/DifferentialEntropy.lean` 末尾 or 適切な section に helper 追加 (~20 行)。

```lean
theorem concaveOn_log_one_add_div {N : ℝ} (hN_pos : 0 < N) :
    ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun x => Real.log (1 + x / N)) := by
  -- (a) `Real.log` is concave on `Ioi 0`
  have h_log : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log :=
    Real.strictConcaveOn_log_Ioi.concaveOn
  -- (b) build affine `g : ℝ →ᵃ[ℝ] ℝ`, `g x = 1 + x/N`
  --     `g := AffineMap.const ℝ ℝ 1 + (N⁻¹) • AffineMap.id ℝ ℝ`
  --     (Mathlib `AffineMap` 上の `+` / scalar `•` で構築)
  let g : ℝ →ᵃ[ℝ] ℝ := …
  -- (c) `h_log.comp_affineMap g` ↦ `ConcaveOn ℝ (g ⁻¹' Ioi 0) (Real.log ∘ g)`
  have h_comp : ConcaveOn ℝ (g ⁻¹' Set.Ioi 0) (Real.log ∘ g) :=
    h_log.comp_affineMap g
  -- (d) `Ici 0 ⊆ g ⁻¹' Ioi 0` since `x ≥ 0 ⇒ g x = 1 + x/N ≥ 1 > 0`
  have h_subset : Set.Ici (0 : ℝ) ⊆ g ⁻¹' Set.Ioi 0 := by
    intro x hx
    simp [g, AffineMap.…]  -- g x = 1 + x/N、`1 + x/N > 0` を `hx : 0 ≤ x` と `hN_pos` から
  -- (e) `ConcaveOn.subset` で domain を `Ici 0` に絞る
  exact h_comp.subset h_subset (convex_Ici 0)
```

### Done 条件

- [ ] `concaveOn_log_one_add_div` publish、0 sorry
- [ ] `lake env lean Common2026/Shannon/DifferentialEntropy.lean` silent

### proof-log

no (helper 1 件、規模小)

### 工数感

~20 行、0.2-0.3 session。

### 失敗時 fallback

- `AffineMap` 構築 friction → helper 内で `ConcaveOn` の definition unfold + 直接 `convex_combination` 検証 (~30-40 行に拡張)。`AffineMap` 路と等価。
- helper の配置先が `DifferentialEntropy.lean` で違和感 (analytic Jensen 補題、entropy と無関係) → 新規 file `Common2026/Analysis/LogConcavity.lean` (~25 行) 作成 + `Common2026.lean` に 1 行 import 追加。判断ログで記録。

---

## Phase 2 — `sum_log_one_add_le_n_log_one_add_avg` body fill 📋

### スコープ

`Common2026/Shannon/AWGNConverseDischarge.lean:624-637` の `sorry` を fill (~30-50 行)。

skeleton (本 plan 起草段階の sketch、実装時に refine):

```lean
theorem sum_log_one_add_le_n_log_one_add_avg
    {n : ℕ} (hn_pos : 0 < n)
    (N : ℝ) (hN_pos : 0 < N)
    (xs : Fin n → ℝ) (hxs_nn : ∀ i, 0 ≤ xs i) :
    ∑ i : Fin n, (1 / 2) * Real.log (1 + xs i / N)
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + ((1 / (n : ℝ)) * ∑ i : Fin n, xs i) / N)) := by
  set f : ℝ → ℝ := fun x => Real.log (1 + x / N) with hf_def
  have hf_concave : ConcaveOn ℝ (Set.Ici (0 : ℝ)) f :=
    concaveOn_log_one_add_div hN_pos
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real_pos
  -- Jensen with uniform weights wᵢ := 1/n
  set w : Fin n → ℝ := fun _ => (1 : ℝ) / (n : ℝ) with hw_def
  have hw_nn : ∀ i ∈ Finset.univ, 0 ≤ w i := by
    intro i _; simp [hw_def]; positivity
  have hw_sum : ∑ i ∈ Finset.univ, w i = 1 := by
    simp [hw_def, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    field_simp
  have hxs_mem : ∀ i ∈ Finset.univ, xs i ∈ Set.Ici (0 : ℝ) := by
    intro i _; exact hxs_nn i
  have h_jensen :
      (∑ i ∈ Finset.univ, w i • f (xs i))
        ≤ f (∑ i ∈ Finset.univ, w i • xs i) :=
    hf_concave.le_map_sum hw_nn hw_sum hxs_mem
  -- smul → mul on ℝ
  simp only [smul_eq_mul] at h_jensen
  -- Multiply both sides by (n : ℝ) > 0 and rearrange to extract (1/2) factor
  -- LHS goal: ∑ (1/2) * log(1 + xᵢ/N)
  --        = (1/2) * ∑ log(1 + xᵢ/N)                  [Finset.mul_sum]
  --        = (1/2) * (n : ℝ) * ((1/n) * ∑ log(1 + xᵢ/N))  [field_simp, hn_ne]
  --        = (n : ℝ) * (1/2) * ((1/n) * ∑ log(1 + xᵢ/N))  [ring]
  --        ≤ (n : ℝ) * (1/2) * log(1 + avg/N)         [Jensen × (1/2)·n、positivity]
  --        = (n : ℝ) * ((1/2) * log(1 + avg/N))       [ring]
  -- 算術 plumbing は `field_simp` + `ring_nf` + `nlinarith` の組合せで吸収
  sorry  -- ← Phase 2 完了時に削除
```

### Done 条件

- [ ] `sum_log_one_add_le_n_log_one_add_avg` body 0 sorry
- [ ] `Common2026/Shannon/AWGNConverseDischarge.lean:624` の `@residual(plan:awgn-converse-aux-plan)` タグ削除 (該当 line 関連)
- [ ] `lake env lean Common2026/Shannon/AWGNConverseDischarge.lean` silent
- [ ] 既存 `sum_log_one_add_le_n_log_one_add_avg` 呼出側 (`awgn_sum_per_letter_mi_le_n_capacity:681`) signature 無変更維持確認

### proof-log

yes (`proof-log-awgn-converse-c1c-jensen.md`)。実装時に `smul`/`mul` normalization のどの段で詰まったか / 算術 plumbing がどの程度膨らんだかを記録 (Phase C dispatch 失敗観察の feedback)。

### 工数感

~30-50 行、0.3-0.5 session。

### 失敗時 fallback

- `smul_eq_mul` rewrite で `h_jensen` が想定形にならない (`Pi.smul_apply` / `Module ℝ ℝ` instance friction) → `simp only [smul_eq_mul]` の代わりに手動 `show (1/n) * f (xs i) ≤ …` で type 強制。
- 算術 plumbing が肥大 (~80 行超) → `(n : ℝ)` 倍 + `(1/2)` 倍の正規化を補助補題 `aux_jensen_arith` に切出 (~15 行 helper)。判断ログで記録。

---

## Phase V — verify + tag 解消 + handoff 📋

### スコープ

- `lake env lean Common2026/Shannon/DifferentialEntropy.lean` silent
- `lake env lean Common2026/Shannon/AWGNConverseDischarge.lean` silent
- 当該 declaration (line 624) の `@residual(plan:awgn-converse-aux-plan)` タグ削除確認 (`sum_log_one_add_le_n_log_one_add_avg` body 内に sorry 残置がないこと)
- `rg -n "@residual\(plan:awgn-converse-aux-plan\)" Common2026/Shannon/AWGNConverseDischarge.lean` で残数を親 plan 判断ログ #6 の 5 → 4 件に減ったことを確認
- 親 plan `awgn-converse-aux-plan.md` 判断ログ #6「後続セッション送り (2)」を完了マーク + 本 mini-plan へ pointer
- 独立 honesty audit subagent 起動: helper `concaveOn_log_one_add_div` 1 件 + 本体 1 件 body fill のため、新規 `sorry` 導入は無しだが既存 sorry 解消 commit は audit 対象 (CLAUDE.md「Independent honesty audit」起動条件は **新規 sorry 導入** だが、Phase C audit verdict 引き継ぎとして「sorry 解消 commit」も verify 推奨)

### Done 条件

- [ ] 上記 verify 全件 silent
- [ ] 親 plan 判断ログ #6 更新
- [ ] 本 mini-plan `## 判断ログ` に Phase 1 + Phase 2 完了記録 append
- [ ] (推奨) honesty audit verdict PASS 確認

### proof-log

no。

### 工数感

0.1-0.2 session。

---

## 撤退ライン

### T-JEN-1: helper `concaveOn_log_one_add_div` で `AffineMap` 構築が friction (Phase 1)

`AffineMap.const ℝ ℝ 1 + (N⁻¹ : ℝ) • AffineMap.id ℝ ℝ` の型推論 / scalar `•` instance plumbing で詰まる。

- 縮退案 (a): helper 内で `ConcaveOn` definition 直接 unfold + convex combination 検証 (~30-40 行に拡張、`AffineMap` 路と等価)
- 縮退案 (b): helper を `Set.Ioi 0` (not `Ici 0`) 上で定義し、本体で `xs i ∈ Ioi 0` を要求 (`hxs_nn : ∀ i, 0 ≤ xs i` を `0 < xs i` に強化、本来 `xs i = perLetterInputSecondMoment c i ≥ 0` で `= 0` 退化境界が許される should-be regularity hyp 改変は本 mini-plan scope では避ける、退化境界 `xs i = 0` で trivial bound `log 1 = 0` で別途処理) — 推奨されない (signature 改変リスク)

### T-JEN-2: `ConcaveOn.le_map_sum` 結論形と本体目標形の bridge が想定外 hard (Phase 2)

`smul_eq_mul` rewrite / `Finset.mul_sum` / `field_simp` の連携で `(1/n) * ∑ ...` が単純化しない。

- 縮退案: 算術 plumbing helper `aux_jensen_arith` (~15 行) に切出 + 本体 1 行呼出。判断ログ #2 で記録。

### T-JEN-3: 候補 (i)(ii)(iii) すべて composition friction が high で詰まった場合 (本 mini-plan 失敗)

**確率: 低** (verbatim 在庫確認済、(ii) は friction を helper 1 箇所に集約する設計、Phase C dispatch 失敗の構造的原因 = 本体内一括 friction を回避済)。発動時:

- `sum_log_one_add_le_n_log_one_add_avg` の `sorry` + tag を `@residual(wall:jensen-finset-sum)` に **再分類** (現 `wall:jensen-affine-subst` は friction 仮説、wall:jensen-finset-sum は Jensen 結論形と本体目標形の構造的 mismatch を表明)
- 親 plan §C 失敗時 fallback (line 906-908) の 2 段目を発動: `log(1+x/N) = log((N+x)/N) = log(N+x) - log(N)` 分離経路で `Real.log` concavity (`Ioi 0` 上) を直接適用 — この経路は (ii) と等価だが split の slot が増える、本 mini-plan で発動した場合は別 mini-plan `awgn-converse-c1c-jensen-split.md` (新規未起草) に委ねる
- 本 mini-plan は failure と判定し handoff + 親 plan 判断ログ append、`@residual` retain

### honesty 撤退ライン (常時、CLAUDE.md「検証の誠実性」)

- ❌ helper `concaveOn_log_one_add_div` の中に load-bearing hypothesis を bundle (例: `(h_concave : ConcaveOn ℝ (Ici 0) (fun x => Real.log (1 + x / N)))` を引数として外出し) → 本補題は **algebraic concavity** で Mathlib 内 closure 可能、staged 化は禁止
- ❌ `sum_log_one_add_le_n_log_one_add_avg` の signature 改変 (引数追加 / hxs_nn の `0 ≤` を `0 <` に強化 等) — 親 plan の呼出側 `awgn_sum_per_letter_mi_le_n_capacity:681` が壊れる
- ❌ `:True` slot / 循環 `:= h` / 退化定義悪用 (CLAUDE.md tells 全件回避)

---

## 検証手順

実装完了時の確認手順:

```bash
# 1. helper verify
lake env lean Common2026/Shannon/DifferentialEntropy.lean
# expect: silent (0 errors, 0 warnings or sorry-無関係 warning のみ)

# 2. 本体 verify
lake env lean Common2026/Shannon/AWGNConverseDischarge.lean
# expect: silent (sorry 残数 5 → 4 件、line 624 解消)

# 3. residual tag 残数確認
rg -n "@residual\(plan:awgn-converse-aux-plan\)" Common2026/Shannon/AWGNConverseDischarge.lean | wc -l
# expect: 4 (親 plan 判断ログ #6 の 5 件から 1 件減)

# 4. line 624 周辺の sorry が消えたことを確認
rg -n "sorry" Common2026/Shannon/AWGNConverseDischarge.lean
# expect: line 624 が出力されない (他 4 件残存は OK)

# 5. honesty audit (orchestrator が実装後 dispatch)
# subagent_type: "honesty-auditor"
# 対象: concaveOn_log_one_add_div (新規) + sum_log_one_add_le_n_log_one_add_avg (body fill)
```

---

## 親 plan / 兄弟 plan との scope 区別

| Plan | スコープ | 状態 |
|---|---|---|
| `awgn-converse-aux-plan.md` (親) | F-3 converse aux discharge (Phase A-V) | Phase C 完了済、後続セッション送り 4 件 |
| **本 mini-plan** (`awgn-converse-c1c-jensen`) | C-1c Jensen affine substitution の `sorry` 解消 | **起草** |
| `awgn-converse-c1b-gaussian-mini-plan.md` (#M1、並行) | C-1b per-letter Gaussian max-entropy 4 hyp 充足 (~80-150 行) | 別 mini-plan、並列 dispatch 中 |
| `awgn-converse-c5-mi-finite-bridge-mini-plan.md` (TBD) | C-5 transitive MI 有限性 bridge (C-1b 完成後) | 未起草 |
| `awgn-main-converse-wiring-plan.md` (TBD) | `AWGNConverse.lean:70` body 置換 + `AWGNMain.lean` migration | 未起草 |

**重要**:

- 本 mini-plan は **C-1b (#M1) と独立** (C-1b は per-letter MI bound の 4 hyp 充足、本 mini-plan は per-letter bound 群を sum で集約する Jensen 段)。並列 dispatch 可。
- 本 mini-plan 完了で `AWGNConverseDischarge.lean` の sorry 残数が 5 → 4 件に減るが、`awgn_converse` (`AWGNConverse.lean:70`) の body sorry は別 plan で処理 (C-7 / wiring)。

---

## オーケストレータ注記

- 実装 agent は `Common2026.lean` を編集しない (helper を `DifferentialEntropy.lean` に追加する場合は既存 import 経路に乗るので import 追加不要、新規 file 作成 fallback の場合は orchestrator が 1 行追加)
- 並列 dispatch 中の場合: `lean-implementer` を `isolation: "worktree"` で起動 (CLAUDE.md「Parallel orchestration」boilerplate 必須)
- 単独 dispatch の場合: worktree 省略 + main 直接
- 完了後の commit は autonomous (CLAUDE.md「Commits」)

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### #0 (2026-05-27) plan 起草 — option (ii) 採用根拠

3 候補 (i/ii/iii) を Mathlib verbatim 在庫確認後比較。

- **(i)** `comp_affineMap` 直接路は Phase C dispatch で friction 観察済 (本体内一括で `smul`/`mul` normalization + `(g ⁻¹' Ioi 0)` membership unfold が重なる)。
- **(ii)** helper 1 件で friction を `concaveOn_log_one_add_div` 内に集約、本体は mechanical Jensen 適用 + 算術。**採用**。Phase 0 verbatim 在庫で Mathlib API 5 件 (`ConcaveOn.le_map_sum` / `strictConcaveOn_log_Ioi` / `ConcaveOn.comp_affineMap` / `ConcaveOn.smul` / `ConcaveOn.translate_*`) 確認済、closure 可能と判定。
- **(iii)** power-mean inequality 経由は `log(1+x/N)` の `+1` シフトで base が変わり、Mathlib `Real.geom_mean_le_arith_mean*` 系に直接 fit せず — 追加 transformation が必要で friction (i) より大。不採用。

scope: 1 helper + 1 本体 body fill、~50-70 行、0.5-1 session。signature 改変なし、load-bearing hyp 追加禁止。

### #1 (TBD、Phase 1 完了時) helper 構築 friction の有無

`AffineMap` 構築 (`AffineMap.const + smul AffineMap.id`) で `Module ℝ ℝ` / scalar `•` instance plumbing が想定通り通ったか、T-JEN-1 縮退案 (a) (definition 直接 unfold) に降格したかを記録。

### #2 (TBD、Phase 2 完了時) Jensen 適用後の算術 plumbing 規模

`smul_eq_mul` + `Finset.mul_sum` + `field_simp` + `ring` の連携で算術 plumbing が ~30 行 (中央) で済んだか、T-JEN-2 縮退案 (補助補題 `aux_jensen_arith` 切出) に降格したかを記録。

### #3 (TBD、Phase V 完了時) sorry 残数 + honesty audit verdict

実績: `AWGNConverseDischarge.lean` sorry 残数 5 → 4 件 + helper `concaveOn_log_one_add_div` 0 sorry + honesty audit subagent verdict (PASS expected、tier 5 defect なし)。
