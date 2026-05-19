# Wyner–Ziv body discharge — moonshot plan

> **Status**: 着手中。target は **L-WZ3 partial discharge** + 関連 plumbing
> 補題群 (D-antitone / 上界 / Constraint set 構造)。撤退ラインは満たさず、
> 1 本完全 discharge は目指さず、**plumbing layer の独立 publish** で着地する。
>
> **撤退ライン (本 plan)**: L-WZ3 の凸性主定理は `Markov cross-product` 制約が
> non-affine なため凸結合不変性が成り立たず full discharge 不可。**D-antitone** に絞り
> + 凸性 statement の build block (stdSimplex 上の凸結合保存補題) を hypothesis
> pass-through 形ではなく **独立 publish 形** で出す。L-WZ2 (Csiszár's sum
> identity) と L-WZ1 (cardinality bound) は本 plan で扱わない。

## Context

Cover–Thomas Theorem 15.9.1 (Wyner–Ziv) の statement-level publish は
2026-05-19 完了 (`WynerZiv.lean` + `WynerZivAchievability.lean` +
`WynerZivConverse.lean`、計 597 行 / 0 sorry)。残るのは:

- **L-WZ1** (auxiliary cardinality bound `|U| ≤ |α|+1`) — `U` を引数 defer
- **L-WZ2** (Csiszár's sum identity) — `_h_csiszar : True` で pass-through
- **L-WZ3** (`R_WZ(D)` の `D` 凸性) — `_h_jensen : True` で pass-through

の 3 本の本体 discharge。本 plan は **L-WZ3 の最も計算可能な側面 (D-antitone)** を
完全 discharge、+ 凸性 statement の build block を独立 publish。

## Approach

`rateDistortionFunction_antitone` (RD の D-antitone discharge、~10 行) と
完全に同型の議論で `wynerZivRatePmf_antitone` を出す:

```
D ≤ D'  ⟹  WynerZivConstraint U P_XY d D ⊆ WynerZivConstraint U P_XY d D'
        ⟹  (image at D) ⊆ (image at D')
        ⟹  sInf (image at D') ≤ sInf (image at D)
```

凸性については **Markov constraint が cross-product 形 `q(x,y,u) * Σ q(x,y',u') =
q(x,y,u') * Σ q(x,y',u)` で non-affine** であることが致命的:
線形結合 `λq₁ + (1-λ)q₂` をこの等式に代入すると交差項
`λ(1-λ) · [q₁(x,y,u) · Σq₂(x,y',u') + q₂(x,y,u) · Σq₁(x,y',u')]` が出て、
一般に `q₁` と `q₂` の Markov constraint だけからは消えない。

したがって本 plan では:

1. **D-antitone を完全 discharge** (`wynerZivRatePmf_antitone`)
2. **`WynerZivConstraint` の D 単調性** を独立 publish (`WynerZivConstraint_mono_in_D`)
3. **`wzExpectedDistortion` の `q`-affinity** (固定 `f` で `q` に対し線形) を独立 publish
   — L-WZ3 凸性の build block の一つ。Markov constraint と独立に成立。
4. **`wzMarginalXY` の `q`-affinity** を独立 publish — もう一つの build block
5. **`stdSimplex` 凸性 を `Common2026` namespace に re-export wrap** (再使用便宜)
6. **`wynerZivRatePmf` の上界**: 任意の `R_WZ(D) ≤ log(Fintype.card U)`
   (`I(X;U) ≤ log|U|` + `I(Y;U) ≥ 0` を独立に出す。これは
   `RateDistortion` の `mutualInfo ≤ logCard` パターン踏襲)
   — achievability/converse の sandwich の片側として有用。
7. **`wzMutualInfoXU - wzMutualInfoYU` の image bddBelow** を **明示的下界
   `-Real.log (Fintype.card U)` で具体化** (`wynerZivRatePmf_image_bddBelow_explicit`)
   — `wynerZivRatePmf_le_of_feasible` の `h_bdd` 引数を消す方向。

これらは:
- 全て pmf-side で完結 (measure-theoretic side に降りない)
- 既存 `WynerZiv.lean` の predicate signature を一切変更しない
  (新規 `WynerZivDischarge.lean` で独立)
- 各補題 ~20-50 行で、合計 ~200-400 行を見込む

## File layout

新規ファイル `Common2026/Shannon/WynerZivDischarge.lean` のみ。
`Common2026.lean` は不変 (seed の制約)。本 file は CLI `lake build` target に
乗らないが、`lake env lean Common2026/Shannon/WynerZivDischarge.lean` で
file-level に clean 検証可能。downstream で本 file の補題を使う場合は
明示的に `import Common2026.Shannon.WynerZivDischarge` で取り込む。

## Lemma roadmap

### Section 1: Constraint set monotonicity

```lean
-- D ≤ D' ⇒ WynerZivConstraint U P_XY d D ⊆ WynerZivConstraint U P_XY d D'.
theorem WynerZivConstraint_mono_in_D
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) {D D' : ℝ} (hD : D ≤ D') :
    WynerZivConstraint U P_XY d D ⊆ WynerZivConstraint U P_XY d D'
```

### Section 2: Wyner-Ziv rate function antitone in D

```lean
-- D ≤ D' ⇒ wynerZivRatePmf U P_XY d D' ≤ wynerZivRatePmf U P_XY d D.
theorem wynerZivRatePmf_antitone
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) {D D' : ℝ} (hD : D ≤ D')
    (h_bdd : BddBelow ((fun qf : (α × β × U → ℝ) × (U × β → γ) =>
                wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
            '' WynerZivConstraint U P_XY d D')) :
    wynerZivRatePmf U P_XY d D' ≤ wynerZivRatePmf U P_XY d D
```

### Section 3: Affinity blocks for L-WZ3

```lean
-- wzMarginalXY is affine in q.
lemma wzMarginalXY_add (q₁ q₂ : α × β × U → ℝ) :
    wzMarginalXY U (q₁ + q₂) = wzMarginalXY U q₁ + wzMarginalXY U q₂
lemma wzMarginalXY_smul (c : ℝ) (q : α × β × U → ℝ) :
    wzMarginalXY U (c • q) = c • wzMarginalXY U q

-- wzExpectedDistortion is affine in q (fixed decoder f).
lemma wzExpectedDistortion_add (d : α → γ → ℝ) (q₁ q₂ : α × β × U → ℝ)
    (f : U × β → γ) :
    wzExpectedDistortion U d (q₁ + q₂) f
      = wzExpectedDistortion U d q₁ f + wzExpectedDistortion U d q₂ f
lemma wzExpectedDistortion_smul (d : α → γ → ℝ) (c : ℝ)
    (q : α × β × U → ℝ) (f : U × β → γ) :
    wzExpectedDistortion U d (c • q) f = c * wzExpectedDistortion U d q f
```

### Section 4: stdSimplex re-export wrapper

```lean
-- Convexity of stdSimplex on the product space, re-exported for convenience.
lemma convex_stdSimplex_wynerZiv :
    Convex ℝ (stdSimplex ℝ (α × β × U)) :=
  convex_stdSimplex ℝ _
```

### Section 5: Upper bound on Wyner-Ziv rate

```lean
-- mutualInfoPmf is bounded above by log |U| × log |α × U| 等の自明上界群
-- (Section 5 は当初計画。L-WZ3 凸性 build block には不要なので scope-out。
-- 5-7 はまとめて削除し、Section 1-4 + bddBelow specialization に集中する)
```

### Section 6: BddBelow specialization

```lean
-- The Wyner-Ziv objective image is bddBelow with the explicit lower bound
-- -Real.log (Fintype.card U) (since I(X;U) ≥ 0 and I(Y;U) ≤ log |U|).
-- 当初は具体的 lower bound (-log |U|) を出す予定だったが、
-- mutualInfoPmf ≤ log |U| の inventory が
-- Common2026 内に整っていない (mutualInfoPmf は entropy 形定義、
-- max entropy bound への bridge ~30 行が要)。代わりに **constraint set
-- が `stdSimplex ℝ (α × β × U)` という compact set の subset** であることを
-- 使い、`continuous_wzObjective` から自動的に bddBelow を導く形にする。
lemma wynerZivConstraint_subset_stdSimplex
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) :
    (fun qf : (α × β × U → ℝ) × (U × β → γ) => qf.1)
        '' WynerZivConstraint U P_XY d D ⊆ stdSimplex ℝ (α × β × U)

-- Compact image of continuous function on compact set ⊆ stdSimplex.
-- 凸性 statement 用 build block ではないが、Section 6 はもとの
-- `wynerZivRatePmf_image_bddBelow_of_objective` 仮定の自然な discharge。
```

## Approach (詳細)

1. **Section 1 + 2 を最初に書く** — RD の `rateDistortionFunction_antitone` を
   verbatim 移植するだけ。~20 行 + ~30 行。
2. **Section 3** — `Finset.sum_add` / `Finset.mul_sum` / `Finset.sum_const` 等の
   基本 simp lemma で discharge。各 ~10-15 行。
3. **Section 4** — `convex_stdSimplex` の re-export。~5 行。
4. **Section 6** — `WynerZivConstraint` の構造から `qf.1 ∈ stdSimplex` を抽出。
   ~10-15 行。

合計予測: **150-250 行 / 8-12 補題**。

## 撤退ライン (本 plan)

- **L-WZ3 凸性主定理本体** — Markov constraint non-affine 性で完全 discharge 不可。
  Section 3 (affinity build block) のみ独立 publish。
- **L-WZ1 / L-WZ2** — 本 plan で扱わない。
- **achievability / converse の主定理 signature 変更** — 禁止。`WynerZivDischarge.lean`
  は新規 file で、既存 file の signature は完全不変。

## 判断ログ

1. **2026-05-20 着手**: L-WZ3 完全 discharge を当初 target にしたが、Markov
   cross-product constraint の非線形性で凸結合不変性が破綻することを確認。
   D-antitone (`sInf` の包含モノトニシティ) のみ完全 discharge、凸性は
   affinity build block を独立 publish する方針に転換。L-WZ2 (Csiszár's
   sum identity, ~300-400 行 plumbing) と L-WZ1 (cardinality bound, ~500
   行 Carathéodory) は本 plan で扱わない。
