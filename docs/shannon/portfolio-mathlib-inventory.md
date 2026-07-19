# Ch.16 Portfolio (log-optimal) — Mathlib + in-project API inventory

> Cover–Thomas *Elements of Information Theory* 2nd ed, Ch.16 "Information Theory and
> Investment" の log-optimal portfolio。有限アウトカム版で定式化 (測度論を持ち込まず有限和で完結、
> 既存 gambling `doublingRate` の一般化)。
>
> 最寄り parent: [`gambling-moonshot-plan.md`](gambling-moonshot-plan.md) (Ch.6、DONE)。
> 本ファイルは「tractable な解析核 (concavity / KT / competitive optimality) を genuine 化できるか」の
> 探索調査 (在庫のみ、実装計画は含まない)。
>
> **状態: ✅ Ch.16 は 2026-07-19 に完遂** — 在庫の壁ゼロ判定どおり 4 中核定理すべて proof-done
> sorryAx-free + `@audit:ok` (`InformationTheory/Shannon/Portfolio/Basic.lean`)。roadmap Ch.16 は
> `✖ scope-out` から `✅` へ復帰。子プラン [`portfolio-moonshot-plan.md`](portfolio-moonshot-plan.md) が SoT。
> 以下の在庫テーブルは実装時の API 参照として保持 (歴史的記述中の「scope-out」は着手前の状態)。

## 一行サマリ

**3 中核定理で使う Mathlib API はすべて既存 — 既存率 100% (実体ベース)、Mathlib 壁ゼロ。** 自作するのは
新 def (`wealthRelative` / `growthRate` / `logOptimal`) と、それらを既存補題で組む糊コードのみ。唯一の
計算的重量は forward KT 方向 (log-optimal ⟹ KT) の Fréchet 微分構築だが、機構
(`IsLocalMaxOn.hasFDerivWithinAt_nonpos` + `mem_posTangentConeAt_of_segment_subset` +
`HasFDerivWithinAt.sum`/`.log`) は完備 = plumbing であり壁ではない。**最大の落とし穴は concavity の
定義域**: `log ∘ affine` は `Real.log` が `Ioi 0` 上でのみ凹なため、合成補題が返す凹性の定義域は
`{b | S_b(a) > 0}` の preimage であって simplex 全体ではない (下記 preconditions box)。

---

## 3 中核定理の最終形 (再掲) と証明戦略

有限型 `α` `[Fintype α]` (アウトカム)、`m : ℕ` (株数)、`p : α → ℝ` (真の pmf、`p ∈ stdSimplex ℝ α`)、
`X : α → (Fin m → ℝ)` (price-relative、各 `X a i ≥ 0`)、portfolio `b ∈ stdSimplex ℝ (Fin m)`。

```lean
/-- wealth relative S_b(a) = ∑ i, b i · X a i (Mathlib の dotProduct 形に合わせる) -/
noncomputable def wealthRelative (X : α → Fin m → ℝ) (b : Fin m → ℝ) (a : α) : ℝ :=
  ∑ i, b i * X a i

/-- growth (doubling) rate W(b) = ∑ a, p a · log (S_b(a)) -/
noncomputable def growthRate (p : α → ℝ) (X : α → Fin m → ℝ) (b : Fin m → ℝ) : ℝ :=
  ∑ a, p a * Real.log (wealthRelative X b a)

-- (1) CT 16.2.2  W concave on the simplex
theorem growthRate_concaveOn (p : α → ℝ) (X : α → Fin m → ℝ) (hp : p ∈ stdSimplex ℝ α)
    (hpos : ∀ a, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < wealthRelative X b a) :
    ConcaveOn ℝ (stdSimplex ℝ (Fin m)) (growthRate p X)

-- (2) CT 16.2.1  Kuhn–Tucker characterization of the log-optimal b*
--     b* log-optimal ⟺ ∀ i, ∑ a, p a · X a i / S_{b*}(a) ≤ 1  (= on supp b*)
theorem kuhnTucker_of_logOptimal (…) :
    IsMaxOn (growthRate p X) (stdSimplex ℝ (Fin m)) bs →
    ∀ i, (∑ a, p a * X a i / wealthRelative X bs a) ≤ 1        -- forward (calculus)
theorem logOptimal_of_kuhnTucker (…) :
    (∀ i, (∑ a, p a * X a i / wealthRelative X bs a) ≤ 1) →
    IsMaxOn (growthRate p X) (stdSimplex ℝ (Fin m)) bs          -- reverse (concavity+Jensen)

-- (3) CT 16.3.1  competitive optimality (gateway atom — pure algebra from KT)
theorem competitive_optimality (…) (bs b : Fin m → ℝ) (hKT : ∀ i, …≤ 1) (hb : b ∈ stdSimplex …) :
    (∑ a, p a * (wealthRelative X b a / wealthRelative X bs a)) ≤ 1
```

証明フロー (依存構造):

```
(1) concavity  = strictConcaveOn_log_Ioi ∘ (linear S_b) via ConcaveOn.comp_linearMap
                 → ConcaveOn.smul (p a ≥ 0) → ConcaveOn.add over a
(2a) forward KT  = IsMaxOn.localize → IsLocalMaxOn.hasFDerivWithinAt_nonpos に
                   direction (e_i − b*) を渡す (mem_posTangentConeAt_of_segment_subset で
                   segment ⊆ simplex から tangent cone 所属)。W' は HasFDerivWithinAt.sum/.log で構築。
                   W'(e_i − b*) = KT_i − 1 ≤ 0.   ← 唯一の calculus
(2b) reverse KT  = concavity(1) + finite log-Jensen (ConcaveOn.le_map_sum)。calculus 不要。
                   W(b*) − W(b) = −∑ p_a log(S_b/S_{b*}) ≥ −log(∑ p_a S_b/S_{b*})
                                = −log(∑ i b_i KT_i) ≥ −log 1 = 0.
(3) competitive  = KT から純代数 (Finset.sum_comm + Finset.mul_sum):
                   ∑ p_a S_b/S_{b*} = ∑ i b_i (∑ a p_a X_i/S_{b*}) = ∑ i b_i KT_i ≤ ∑ i b_i = 1.
```

**構造上の要点**: calculus は forward KT (2a) にのみ現れる。competitive optimality (3) と reverse KT (2b)
は微分ゼロ。したがって gateway atom = **(3) を KT 仮定下で** または **(2b)** から始めるのが最安。

---

## A. 凹性の合成・和 (定理 1 = W の concavity)

`variable {𝕜 E F α β : Type*}` 文脈。我々は `𝕜 = ℝ`, `E = (Fin m → ℝ)`, `F = ℝ`, `β = ℝ`。

| 概念 | Mathlib API | file:line | 状態 | 定理 1 での扱い |
|---|---|---|---|---|
| `Real.log` の狭義凹性 | `strictConcaveOn_log_Ioi : StrictConcaveOn ℝ (Ioi 0) log` | `Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean:67` | ✅ 既存 | **凹性の起点**。`.concaveOn` で `ConcaveOn ℝ (Ioi 0) log` に降格して合成。定義域が `Set.Ioi 0` (開、x>0) な点が preconditions box の核 |
| (負側) | `strictConcaveOn_log_Iio : StrictConcaveOn ℝ (Iio 0) log` | 同上 `:217` | ✅ 既存 | 不使用 (S_b ≥ 0 側のみ) |
| affine 前合成で凹性保存 | `theorem ConcaveOn.comp_affineMap {f : F → β} (g : E →ᵃ[𝕜] F) {s : Set F} (hf : ConcaveOn 𝕜 s f) : ConcaveOn 𝕜 (g ⁻¹' s) (f ∘ g)` | `Mathlib/Analysis/Convex/Function.lean:948` | ✅ 既存 | `b ↦ S_b(a)` を affine map で構成する場合。結論の定義域が `g ⁻¹' s` = `{b | S_b(a) ∈ Ioi 0}` に注意 |
| linear 前合成で凹性保存 | `theorem ConcaveOn.comp_linearMap {f : F → β} {s : Set F} (hf : ConcaveOn 𝕜 s f) (g : E →ₗ[𝕜] F) : ConcaveOn 𝕜 (g ⁻¹' s) (f ∘ g)` | `Mathlib/Analysis/Convex/Function.lean:464` | ✅ 既存 | **第一候補** (`S_b` は原点固定なので linear で足りる)。`g = ∑ i, X a i • LinearMap.proj i` |
| 非負係数倍で凹性保存 | `theorem ConcaveOn.smul {c : 𝕜} (hc : 0 ≤ c) (hf : ConcaveOn 𝕜 s f) : ConcaveOn 𝕜 s fun x => c • f x` | `Mathlib/Analysis/Convex/Function.lean:916` | ✅ 既存 | `p a ≥ 0` で各項 `p a · log(S_b(a))` の凹性 |
| 凹関数の和 | `theorem ConcaveOn.add (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConcaveOn 𝕜 s (f + g)` | `Mathlib/Analysis/Convex/Function.lean:201` | ✅ 既存 | 有限和 `∑ a` は `Finset.sum` induction で `.add` を畳む (直接の `ConcaveOn.sum` は不在、下記) |
| 有限和版 `ConcaveOn.sum` | — | — | ❌ **不在** (loogle `"ConcaveOn.sum"` Found 0) | `Finset.cons_induction` で `.add` + `concaveOn_const` を畳む糊 ~15 行。または `s.centerMass`/epigraph で自作 |
| 線形射影 | `LinearMap.proj (i : ι) : (Π i, φ i) →ₗ[R] φ i` | `Mathlib/LinearAlgebra/Pi.lean` | ✅ 既存 | `S_b(a) = ∑ i, X a i • (LinearMap.proj i) b` として linear form 構成 |

`ConcaveOn.comp_linearMap` / `.add` / `.smul` の型クラス文脈 (`𝕜 = ℝ` で全充足): `[Field 𝕜]`/`[Semiring 𝕜]`
`[LinearOrder 𝕜]`/`[PartialOrder 𝕜]` + `[AddCommGroup/Monoid E]` `[AddCommGroup/Monoid β]` `[Module 𝕜 E]`
`[Module 𝕜 β]` `[IsOrderedAddMonoid β]` 等 (`Mathlib/Analysis/Convex/Function.lean:35,39,43,47,189,208,453`
の section variable 積み上げ)。ℝ は全て instance 供給。

**定理 1 まとめ**: `strictConcaveOn_log_Ioi.concaveOn |>.comp_linearMap g |>.smul (hp.1 a) |> (Finset 畳み)` の
チェーンで閉じる。Mathlib gap は「有限和版 `ConcaveOn.sum`」のみで **~15 行の induction 糊**。ただし定義域は
`⋂ a, gₐ ⁻¹' (Ioi 0)` = `{b | ∀ a, S_b(a) > 0}` になり、simplex 全体で凹を主張するには `hpos` 前提
(preconditions box) が要る。

---

## B. 有限 Jensen (凹版) — 定理 2b (reverse KT) + 定理 3 の log 段

`variable {𝕜 E F β ι : Type*}`。我々は `𝕜 = ℝ`, `E = β = ℝ`, `f = Real.log`, `s = Ioi 0`,
`p i` = 比 `S_b(a)/S_{b*}(a)`, `w i` = `p a`。

| API | file:line | signature (verbatim) | 定理での扱い |
|---|---|---|---|
| **`ConcaveOn.le_map_sum`** | `Mathlib/Analysis/Convex/Jensen.lean:73` | `theorem ConcaveOn.le_map_sum (hf : ConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) : (∑ i ∈ t, w i • f (p i)) ≤ f (∑ i ∈ t, w i • p i)` | **reverse KT + 定理 3 の log-Jensen の第一候補**。`w = p` (pmf、`h₁` = `hp.2`)、`f = log`、`s = Ioi 0` |
| `ConcaveOn.le_map_centerMass` | `Mathlib/Analysis/Convex/Jensen.lean:61` | `(hf : ConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : 0 < ∑ i ∈ t, w i) (hmem : ∀ i ∈ t, p i ∈ s) : t.centerMass w (f ∘ p) ≤ f (t.centerMass w p)` | バックアップ (正規化前、`0 < ∑ w`)。`sum` 版で足りる |

`ConcaveOn.le_map_sum` の型クラス前提 **verbatim** (`Mathlib/Analysis/Convex/Jensen.lean:47-49`):
`[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [AddCommGroup β] [PartialOrder β]`
`[IsOrderedAddMonoid β] [Module 𝕜 E] [Module 𝕜 β] [IsStrictOrderedModule 𝕜 β]`。
引数: `{s : Set E} {f : E → β} {t : Finset ι} {w : ι → 𝕜} {p : ι → E}`。ℝ で全充足。
注: `w i • f (p i)` は `ℝ` では `w i * f (p i)` (`smul_eq_mul`)。

**注意**: これは **有限和 Jensen**。measure 版 (`ConcaveOn.le_map_integral`) は不要 (有限アウトカム定式化のため)。
`hmem : ∀ a, S_b(a)/S_{b*}(a) ∈ Ioi 0` は `S_b > 0`, `S_{b*} > 0` から従う (positivity 前提に依存)。

---

## C. log の単調性・微分 — 定理 2a (forward KT) の被微分部品

| API | file:line | signature (verbatim) | 扱い |
|---|---|---|---|
| log 単調 | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:150` | `lemma log_le_log (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y` | reverse KT / competitive の `−log ≥ −log` 段 |
| log 非負 | `.../Log/Basic.lean:212` | `theorem log_nonneg (hx : 1 ≤ x) : 0 ≤ log x` | `log 1 = 0` 境界 |
| log 非正 | `.../Log/Basic.lean:221` | `theorem log_nonpos (hx : 0 ≤ x) (h'x : x ≤ 1) : log x ≤ 0` | `∑ ≤ 1 ⟹ log ∑ ≤ 0` |
| 接線上界 | `.../Log/Basic.lean:306` | `theorem log_le_sub_one_of_pos {x : ℝ} (hx : 0 < x) : log x ≤ x - 1` | 代替ルート (Jensen を使わず接線で competitive を出す時) |
| log 微分 | `.../Log/Deriv.lean:52` | `theorem hasDerivAt_log (hx : x ≠ 0) : HasDerivAt log x⁻¹ x` | forward KT のスカラー route の核 |
| 合成 log 微分 (scalar) | `.../Log/Deriv.lean:112` | `theorem HasDerivAt.log (hf : HasDerivAt f f' x) (hx : f x ≠ 0) : HasDerivAt (fun y => log (f y)) (f' / f x) x` | `λ ↦ log(S_{(1-λ)b*+λe_i}(a))` の微分 |
| 有限和微分 (scalar) | `Mathlib/Analysis/Calculus/Deriv/Add.lean:222` | `theorem HasDerivAt.sum (h : ∀ i ∈ u, HasDerivAt (A i) (A' i) x) : HasDerivAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) x` | `∑ a` を微分 |
| 合成 log 微分 (Fréchet) | `.../Log/Deriv.lean:145` | `theorem HasFDerivWithinAt.log (hf : HasFDerivWithinAt f f' s x) (hx : f x ≠ 0) : HasFDerivWithinAt (fun x => log (f x)) ((f x)⁻¹ • f') s x` | **FDeriv route の核** (下 E と併用) |
| 有限和微分 (Fréchet) | `Mathlib/Analysis/Calculus/FDeriv/Add.lean:429` | `theorem HasFDerivWithinAt.sum (h : ∀ i ∈ u, HasFDerivWithinAt (A i) (A' i) s x) : HasFDerivWithinAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) s x` | `∑ a` の FDeriv 構築 |

---

## D. stdSimplex API (定理 1/2/3 共通)

`stdSimplex 𝕜 ι := { f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1 }` (`Mathlib/Analysis/Convex/StdSimplex.lean:35`)。
membership 分解に専用 iff 補題は無く **def 直接** (`hb.1 : ∀ i, 0 ≤ b i`、`hb.2 : ∑ i, b i = 1`) —
gambling `Basic.lean` と同一の使い方。

| API | file:line | signature (verbatim) | 扱い |
|---|---|---|---|
| membership 分解 | `.../StdSimplex.lean:35` | `def stdSimplex : Set (ι → 𝕜) := { f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1 }` | `.1`/`.2` で非負・和1を取り出す |
| 凸性 | `.../StdSimplex.lean:42` | `theorem convex_stdSimplex [IsOrderedRing 𝕜] : Convex 𝕜 (stdSimplex 𝕜 ι)` | forward KT で segment ⊆ simplex を出す (`Convex.segment_subset` 経由) |
| Icc 所属 | `.../StdSimplex.lean:68` | `theorem mem_Icc_of_mem_stdSimplex [IsOrderedAddMonoid 𝕜] {f : ι → 𝕜} (hf : f ∈ stdSimplex 𝕜 ι) (x) : f x ∈ Icc (0 : 𝕜) 1` | `b i ∈ [0,1]` の即出し |
| 頂点 e_i ∈ simplex | `.../StdSimplex.lean:81` | `theorem single_mem_stdSimplex (i : ι) : Pi.single i 1 ∈ stdSimplex 𝕜 ι` | **forward KT の direction `e_i = Pi.single i 1`**。前提 `[DecidableEq ι] [ZeroLEOneClass 𝕜]` |
| コンパクト | `.../StdSimplex.lean:189` | `theorem isCompact_stdSimplex [CompactIccSpace 𝕜] [IsOrderedAddMonoid 𝕜] : IsCompact (stdSimplex 𝕜 ι)` | log-optimal b* の **存在** (最大値の存在) を出す時のみ (定理 1-3 の主張自体には不要) |
| 頂点間 segment ⊆ simplex | `.../StdSimplex.lean:95` | `lemma segment_single_subset_stdSimplex (i j : ι) : ([Pi.single i 1 -[𝕜] Pi.single j 1]) ⊆ stdSimplex 𝕜 ι` | 参考 (b*→e_i の segment は `convex_stdSimplex.segment_subset` で足りる) |

`Fin m` は `[DecidableEq]` `[Fintype]` を持ち、ℝ は `[ZeroLEOneClass]` `[CompactIccSpace]`
`[IsOrderedRing]` を供給 = 全前提充足。

---

## E. 最大点の一階条件 (forward KT = 定理 2a、唯一の calculus)

`variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : StrongDual ℝ E}`
`{s : Set E} {a x y : E}` (`Mathlib/Analysis/Calculus/LocalExtr/Basic.lean:69-70`)。
我々は `E = (Fin m → ℝ)` (有限次元 normed space、instance 完備)。

| API | file:line | signature (verbatim) | 扱い |
|---|---|---|---|
| 大域最大 → 局所最大 | `Mathlib/Topology/Order/LocalExtr.lean:117` | `theorem IsMaxOn.localize (hf : IsMaxOn f s a) : IsLocalMaxOn f s a` | log-optimal (`IsMaxOn`) を局所化 |
| **max での方向微分 ≤ 0** | `Mathlib/Analysis/Calculus/LocalExtr/Basic.lean:104` | `theorem IsLocalMaxOn.hasFDerivWithinAt_nonpos (h : IsLocalMaxOn f s a) (hf : HasFDerivWithinAt f f' s a) (hy : y ∈ posTangentConeAt s a) : f' y ≤ 0` | **forward KT の心臓**。`y = e_i − b*` を渡すと `W'(e_i−b*) ≤ 0` |
| segment → tangent cone | `Mathlib/Analysis/Calculus/LocalExtr/Basic.lean:92` | `theorem mem_posTangentConeAt_of_segment_subset (h : [x -[ℝ] x + y] ⊆ s) : y ∈ posTangentConeAt s x` | `y = e_i − b*` が tangent cone に入る証拠 (segment b*→e_i ⊆ simplex は convex から) |
| (減算版) | `.../LocalExtr/Basic.lean:87` | `theorem sub_mem_posTangentConeAt_of_segment_subset (h : segment ℝ x y ⊆ s) : y - x ∈ posTangentConeAt s x` | `e_i − b* ∈ tangent cone` の別形 |

**W の FDeriv 構築** (self-build、下記): `growthRate` = `∑ a, (p a) • log ∘ (linear S_·(a))` の
`HasFDerivWithinAt` を `HasFDerivWithinAt.sum` + `HasFDerivWithinAt.log` + linear form の FDeriv
(`ContinuousLinearMap.hasFDerivWithinAt` / `LinearMap` の FDeriv は自明) で組む。得られる
`f' = ∑ a, (p a) • (S_{b*}(a))⁻¹ • (linear form dual)`、`f'(e_i − b*) = KT_i − 1`。

**forward KT まとめ**: 機構は完備 (壁ゼロ)。self-build は「W の `HasFDerivWithinAt` 構築 + `f'(e_i−b*) =
KT_i − 1` の代数簡約」で **~60–100 行**。`S_{b*}(a) ≠ 0` が `.log` の前提 (positivity)。

---

## F. 有限和 Fubini / 線形性 (定理 3 = competitive optimality、gateway atom)

すべて trivial・既存。competitive optimality は KT から純代数で従う (calculus ゼロ)。

| API | file:line | 用途 |
|---|---|---|
| `Finset.sum_comm` | `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean` | `∑ a ∑ i` ↔ `∑ i ∑ a` の swap |
| `Finset.mul_sum` | `Mathlib/Algebra/BigOperators/Ring/Finset.lean` | `b_i · ∑ a (…)` の分配 |
| `Finset.sum_div` | `Mathlib/Algebra/BigOperators/…` | `(∑) / c = ∑ (·/c)` |
| `Finset.sum_le_sum` | 標準 | `∑ i b_i KT_i ≤ ∑ i b_i · 1 = 1` (KT_i ≤ 1 + b_i ≥ 0) |

**定理 3 まとめ**: `∑ a p_a S_b(a)/S_{b*}(a) = ∑ a p_a (∑ i b_i X_{a,i})/S_{b*}(a)`
`= ∑ i b_i (∑ a p_a X_{a,i}/S_{b*}(a)) = ∑ i b_i · KT_i ≤ ∑ i b_i = 1`。`sum_comm` + `mul_sum` +
`sum_le_sum` + `hb.2` のみ、~20 行。**gateway atom** — KT さえ手元にあれば凹性も微分も不要。

---

## G. in-project 資産 (gambling — 一般化元)

`InformationTheory/Shannon/Gambling/Basic.lean` (`@audit:ok`、sorryAx-free) は horse-race 特殊形。

| in-project API | file:line | signature | portfolio への関係 |
|---|---|---|---|
| `doublingRate` | `Gambling/Basic.lean:72` | `noncomputable def doublingRate (b o p : α → ℝ) : ℝ := ∑ x, p x * Real.log (b x * o x)` | **`growthRate` の特殊形**: `X a i = o i · [a = i]` (diagonal price-relative) とすると `S_b(a) = b a · o a`、`growthRate p X b = doublingRate b o p`。def の一般化が自然に効く |
| `klDivPmf` | `CsiszarProjection.lean:61` | `noncomputable def klDivPmf (P Q : α → ℝ) : ℝ := ∑ a, Q a * klFun (P a / Q a)` | horse-race では gap = `klDivPmf p b`。portfolio は非対角なので **KL 還元は効かない** (一般 X で `log(b x o x) − log(p x o x)` が per-term 分離しない)。portfolio は凹性/Jensen ルートが本筋 |
| `klDivPmf_nonneg` | `CsiszarProjection.lean:67` | `lemma klDivPmf_nonneg (P Q : α → ℝ) (hP : ∀ a, 0 ≤ P a) (hQ : ∀ a, 0 ≤ Q a) : 0 ≤ klDivPmf P Q` | 参考 (portfolio では未使用見込み) |
| `doublingRate_le_proportional` | `Gambling/Basic.lean:124` | `@[entry_point]` CT 6.1.2 | portfolio の `logOptimal_of_kuhnTucker` を `X` diagonal に落とすと **これに一致** (整合性チェック用) |

**所見 (対応の効き方)**: def の一般化は自然 (`b x · o x` → `∑ i b i · X a i`)。しかし **証明ルートは分岐する**:
gambling は KL 還元 (対角なので per-term に log が分離) で閉じたが、portfolio の一般 X では per-term
分離しないため **凹性 + finite Jensen** が本筋。gambling の補題 (`klDivPmf_*`) はほぼ再利用できず、
portfolio は上 A/B/E の Mathlib 補題を新規に組む。`stdSimplex` の `.1`/`.2` 使い方と全体骨格
(`Finset.sum` + per-outcome 場合分け) のみ gambling から流用可。

---

## Key-preconditions box (事故が起きやすい前提)

- **[最重要] concavity の定義域**: `strictConcaveOn_log_Ioi` は `Set.Ioi 0` (**開**、x > 0) 上でのみ凹。
  `ConcaveOn.comp_linearMap` が返す凹性の定義域は `g ⁻¹' (Ioi 0)` = `{b | S_b(a) > 0}` であって
  **simplex 全体ではない**。定理 1 を simplex 全体で述べるには `∀ a, ∀ b ∈ simplex, S_b(a) > 0` を前提化
  (= 各アウトカムで全 portfolio が正の wealth、例えば `∀ a i, 0 < X a i` から従う)。これを落とすと
  頂点 `b = e_i` で `S_b(a) = X a i = 0` になりうる点で凹性が破れる (境界)。**regularity precondition**
  として明示するのが正道 (load-bearing ではない)。
- **`Real.log 0 = 0` 規約**: gambling と同じ落とし穴。`X a i = 0` を含む portfolio では真の growth は
  `−∞` (ruin) だが Lean は `0` に潰す。`S_b > 0` 前提はこの規約由来の必須前提 (gambling `hb_pos` と同性質)。
- **`ConcaveOn.le_map_sum` の `hmem`**: `∀ a, S_b(a)/S_{b*}(a) ∈ Ioi 0`。分母 `S_{b*}(a) > 0` と
  分子 `S_b(a) > 0` の両方が要る (positivity 前提に依存)。
- **forward KT の `.log` 前提**: `HasFDerivWithinAt.log` / `HasDerivAt.log` は `f x ≠ 0` = `S_{b*}(a) ≠ 0`。
  log-optimal b* が全アウトカムで正の wealth を出すこと (positivity) が必要。
- **`single_mem_stdSimplex` の型クラス**: `[DecidableEq ι] [ZeroLEOneClass 𝕜]` — `Fin m` + ℝ で自動充足。
- **KT の等号 (on support)**: forward 方向は `≤ 1` のみ機構で出る。support 上の等号 (`b*_i > 0 ⟹ = 1`)
  は `∑ i b*_i (KT_i − 1) = W'(b*−b*)... = 0` かつ各 `b*_i(KT_i−1) ≤ 0` から `b*_i > 0` の項で `KT_i = 1`。
  追加 ~15 行 (機構は同じ `hasFDerivWithinAt_nonpos` を `y = b* − b*` 近傍で)。

---

## 自作が必要な要素 (優先度順)

1. **新 def `wealthRelative` / `growthRate` / (`isLogOptimal := IsMaxOn growthRate simplex`)** — Mathlib
   shape 駆動で定義 (`∑ i, b i * X a i` は `Matrix.dotProduct`/`Finset.sum` 形、log-Jensen と comp_linearMap の
   結論形にそのまま乗る)。~20 行。落とし穴: `growthRate` を `Real.log (b · X_a)` で書くと linear form の
   FDeriv/comp_linearMap への持ち上げが素直 (textbook 形の丸写しでよい珍しいケース)。
2. **定理 3 competitive optimality (gateway atom)** — F の sum_comm/mul_sum で KT 仮定下に純代数。~20 行、
   壁ゼロ、**最初に着手すべき decisive atom** (KT の意味論が正しいか + def の形が Mathlib 補題に乗るかを最小コストで検証)。
3. **定理 1 concavity** — A のチェーン + `ConcaveOn.sum` 自作 induction 糊 ~15 行。計 ~40 行。
4. **定理 2b reverse KT** — 定理 1 + `ConcaveOn.le_map_sum`。~50 行。calculus 不要。
5. **定理 2a forward KT** — E の FDeriv-at-max。W の `HasFDerivWithinAt` 構築 (~60–100 行) が最大重量。
   support 等号 +~15 行。壁ではなく plumbing。
6. **`ConcaveOn.sum` (有限和版凹性)** — Mathlib 不在の唯一の汎用ギャップ。`Finset.cons_induction` +
   `ConcaveOn.add` + `concaveOn_const`。~15 行。Mathlib PR 余地あり (副次メリット)。

工数感: gambling (~150 行、壁ゼロ、1 ファイル) との比較で **portfolio は 2–3 倍** (~300–400 行)。
理由は (a) 多次元 simplex 上の FDeriv-at-max、(b) KL 還元が効かず凹性+Jensen を新規に組む、の 2 点。
壁が無い分、gambling 同様 proof-done 到達は現実的。

---

## Mathlib 壁の列挙

**genuine な Mathlib 壁はゼロ**。3 中核定理の全部品が既存。不在は以下の 2 種のみで、いずれも壁でなく
「自作糊 / モデリング選択」:

| 不在項目 | loogle 確認 | 分類 | 対処 |
|---|---|---|---|
| 有限和版 `ConcaveOn.sum` | `"ConcaveOn.sum"` → **Found 0 declarations** | 糊 (plumbing) | `.add` induction ~15 行。壁でない |
| packaged "log-optimal portfolio / KT" 定理 | `"logOptimal"` → **Found 0** / `"portfolio"` → **Found 0** | これは我々が建てる対象 | 該当なし (壁でない) |

`ConcaveOn.comp_linearMap` の結論定義域が simplex 全体でない点も **壁でなく precondition** (positivity 前提で解消)。
共有 sorry-lemma 集約の対象なし (壁が無いため)。

---

## 撤退ラインとの距離

parent [`gambling-moonshot-plan.md`](gambling-moonshot-plan.md) は Ch.6 DONE で portfolio 固有の撤退ラインを
持たず、Ch.16 は着手前 roadmap で章単位 scope-out だったため、本探索の撤退判断は新規に設定した
(結果: 撤退不発、4 定理とも完遂)。

- **撤退ライン (触れるか)**: forward KT (定理 2a) の FDeriv-at-max 構築が想定超過 (W の
  `HasFDerivWithinAt` が 100 行を超え詰まる) した場合。**発動リスクは低** (機構 E は完備、`.sum`/`.log`
  合成のみ) だが、多次元 FDeriv の未経験度から非ゼロ。
- **degenerate fallback (新撤退ライン提案)**: forward KT が詰まったら **定理 1 (concavity) + 定理 2b
  (reverse KT) + 定理 3 (competitive、KT を仮定した形)** の 3 本で着地し、forward KT (log-optimal ⟹ KT) は
  `sorry` + `@residual(plan:portfolio-forward-kt)` で残置する (retreat exit は sorry、hypothesis 束ねは
  しない)。この縮退でも CT 16.2.2 (凹性) / 16.2.1 逆向き / 16.3.1 (competitive) の 3/4 は genuine closure。
  forward KT のみ後続タスクへ。
- **gateway-atom-first 推奨**: 撤退判断の前に、**定理 3 (competitive optimality) を KT 仮定下で 1 本**
  `lean-implementer` に投げ、def の形が Mathlib 補題に乗るか + KT 意味論が正しいかを最小コストで確認する。

---

## 着手 skeleton (imports + namespace + 主定理 sorry)

`InformationTheory/Shannon/Gambling/Portfolio.lean` (または `Shannon/Portfolio/Basic.lean`) の出だし:

```lean
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import InformationTheory.Meta.EntryPoint

namespace InformationTheory.Shannon.Portfolio

open Real
open scoped BigOperators

variable {α : Type*} [Fintype α] {m : ℕ}

/-- Wealth relative `S_b(a) = ∑ i, b i · X a i` of portfolio `b` under price relatives `X`. -/
noncomputable def wealthRelative (X : α → Fin m → ℝ) (b : Fin m → ℝ) (a : α) : ℝ :=
  ∑ i, b i * X a i

/-- Growth (doubling) rate `W(b) = ∑ a, p a · log (S_b(a))`. -/
noncomputable def growthRate (p : α → ℝ) (X : α → Fin m → ℝ) (b : Fin m → ℝ) : ℝ :=
  ∑ a, p a * Real.log (wealthRelative X b a)

/-- CT 16.2.2: the growth rate is concave in the portfolio. -/
theorem growthRate_concaveOn (p : α → ℝ) (X : α → Fin m → ℝ) (hp : p ∈ stdSimplex ℝ α)
    (hpos : ∀ a, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < wealthRelative X b a) :
    ConcaveOn ℝ (stdSimplex ℝ (Fin m)) (growthRate p X) := by
  sorry

/-- CT 16.3.1: competitive optimality of a Kuhn–Tucker portfolio `bs` (gateway atom). -/
theorem competitive_optimality (p : α → ℝ) (X : α → Fin m → ℝ) (bs b : Fin m → ℝ)
    (hb : b ∈ stdSimplex ℝ (Fin m)) (hpos : ∀ a, 0 < wealthRelative X bs a) (hXnn : ∀ a i, 0 ≤ X a i)
    (hKT : ∀ i, (∑ a, p a * X a i / wealthRelative X bs a) ≤ 1) :
    (∑ a, p a * (wealthRelative X b a / wealthRelative X bs a)) ≤ 1 := by
  sorry

end InformationTheory.Shannon.Portfolio
```

最初に `competitive_optimality` (gateway atom、KT 仮定下・純代数) を割り、次に `growthRate_concaveOn`
→ reverse KT → forward KT の順で着地するのが最短・最安。
