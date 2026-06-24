# Cramér / Chernoff CLT-boundary closure ムーンショット計画 🌙

**Status**: CLOSED ✅ — done (Phase 1-6 full closure 2026-06-11、headline `cramer_lower_boundary_unconditional` + 上流両 root sorryAx-free、独立監査 PASS)。

> ✅ **CLOSED (2026-06-11)** — Phase 1-6 full closure 達成。`InformationTheory/Shannon/CramerCltBoundaryClosure.lean`
> (586 行, 0 sorry / 0 @residual, sorryAx-free, `InformationTheory.lean` import 済) に headline
> `cramer_lower_boundary_unconditional` (内部最適 tilt `a = deriv (cgf (Y∘eval 0) (infinitePi μ₀)) lam`
> で residual largeness hypothesis を除去した Cramér 下界) を含む 10 decl を publish。独立 honesty 監査
> (`@audit:ok` 全 10 件、`h_coboundedBelow` 非 vacuous 性まで機械検証) **PASS**。判断ログ #4 / commit `05ed225`。
> **未配線残件 = 配線完了 (2026-06-11)**: 子 plan [`cramer-root-wiring-plan.md`](cramer-root-wiring-plan.md) が
> root A (`cramer_lower_phaseC_partial_discharge`、`7e4f05a` cycle-break + `hVar` thread) と root B
> (`cramer_lower` / `cramer_lower_legendre` / `cramer_tendsto`、下流新モジュール `CramerGeneralLower.lean` 移設 +
> transport) を **両方 sorryAx-free で discharge 完了**。両 root とも `#print axioms` =
> `[propext, Classical.choice, Quot.sound]`。headline + consumer chain end-to-end で sorryAx-free。

> **sorry-based 移行完了 (2026-05-25、partial)** — `docs/shannon/cramer-sorry-migration-plan.md`
> に従い、本 plan に属する 1 件の `@audit:suspect(cramer-chernoff-clt-closure-moonshot-plan)`
> を `sorry + @residual(plan:cramer-chernoff-clt-closure-moonshot-plan)` に書換: 対象は
> `InformationTheory/Shannon/CramerCLTClosure.cramer_lower_at` (load-bearing `h_slice` 仮説を削除、
> body は `sorry` 1 行)。**unconditional headline `cramer_lower_at_cgfDeriv_unconditional`**
> (CramerCLTClosure.lean:523, suspect なし) は signature を維持しつつ body が
> `cramer_lower_at` を呼ぶ 1 行に縮退 — constructive 経路 (boundary CLT + Phase 5 + tiltedHalfLine
> change-of-measure) は **transitive `sorry` を経由する状態に降格** (上流 `cramer_lower_at` の
> `sorry` を継承)。signature 上は依然 `hVar + h_coboundedBelow` 以外の residual largeness 仮定なし。
> `hVar` は dead-code 由来の unused 警告状態 (旧 body の `tiltedHalfLine_chernoff_lower_at_boundary`
> 経由で消費されていたが、新 body では `cramer_lower_at` が `h_slice` を取らないため。判断ログ参照)。

> ⚠️ **上記 (2026-05-20「DONE」) banner は STALE / 虚偽だった (2026-06-10 機械検証で訂正)**:
> 主張された `InformationTheory/Shannon/CramerCLTClosure.lean` も decl
> `cramer_lower_at_cgfDeriv_unconditional` も **実在しない** (`find`/`grep` 0-hit)。Cramér CLT-boundary
> closure は **未達**。現存する Cramér コードは `Shannon/Cramer/Cramer.lean` +
> `Shannon/Cramer/LC2PhaseC.lean` の 2 file で、live `@[entry_point]`
> `cramer_tendsto_phaseC_partial_discharge` (CramerLC2PhaseC.lean:208) は **sorryAx 依存** (Phase C
> sorry `cramer_lower_phaseC_partial_discharge`, CramerLC2PhaseC.lean:167 にブロックされる)。
> **実態 (2026-06-10 独立壁再判定)**: Phase C sorry は壁ではなく配線。closure に必要な 0-sorry 資産
> (`isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge`, `tiltedWindow_eventually_large_of_cgfDeriv_interior`,
> `pi_tilted_sum_eq_pi_tilted`) は `InfinitePiTiltedChangeOfMeasure.lean` 等に既存。`...:167` は
> canonical i.i.d. 設定で ~30-50 行配線、`Cramer.lean:468 cramer_lower` は一般化で ~100-150 行。
> **進捗 Phase 0-6 の [ ] は実態どおり未完。**

> **Parent**: [`infinitepi-tilted-rn-discharge-moonshot-plan.md`](infinitepi-tilted-rn-discharge-moonshot-plan.md) §撤退ライン **W-3**
> (Phase 4 residual predicate `IsTiltedWindowEventuallyLarge` の **境界ケース** discharge)
>
> **在庫 (verdict GO)**: [`cramer-chernoff-clt-closure-mathlib-inventory.md`](cramer-chernoff-clt-closure-mathlib-inventory.md)
> (~120-210 行、piece 別難度・鍵 lemma・file:line 済)
>
> **Predecessors (publish 済、変更なしで再利用)** — ⚠️ 実パス (2026-06-11 `1a19915` で確認、`fdd68a3` 昇格後):
> - `InformationTheory/Shannon/Cramer/InfinitePiTiltedChangeOfMeasure.lean` (0 sorry):
>   `IsTiltedWindowEventuallyLarge`, `isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge`,
>   `tiltedMean_eq_deriv_cgf`, `tiltedWindow_eventually_large_of_interior`,
>   `tiltedWindow_eventually_large_of_cgfDeriv_interior`, `cramer_lower_phaseC_residual_discharge`
> - `InformationTheory/Shannon/Cramer/LC2Discharge.lean`: `iIndepFun_tilted_ambient`,
>   `identDistrib_tilted_ambient`, `bounded_eval_family` (full name `InformationTheory.Shannon.Cramer.Discharge.bounded_eval_family`)
> - `InformationTheory/Shannon/Cramer/LC2DischargeExt.lean`: `tilted_lln_in_probability_real`,
>   `isProbabilityMeasure_infinitePi_tilted_of_bounded`
>
> **Status (2026-05-20)**: 着手前。親 W-3 は **既に発動済** (現状コードは
> `IsTiltedWindowEventuallyLarge` residual + interior ケースのみ discharge で 0 sorry 着地)。
> 本 plan は residual の **境界ケース `a = tilted mean m`** を CLT で実証して predicate を
> 実際に証明可能にする **上振れ方向** (撤退から前進)。完成すれば Cramér 下界が内部点
> `a = deriv (cgf) lam` で unconditional 化する。

## 進捗

- [ ] Phase 0 — Mathlib + 既存足場 signature 再確認 (在庫転記の verbatim 固定) 📋 → [inventory](cramer-chernoff-clt-closure-mathlib-inventory.md)
- [x] Phase 1 — `gaussianReal_Ici_eq_half` (Gaussian median、唯一の「一から」) ✅ **CLOSED** (sorryAx-free, `1a19915`, `InformationTheory/Shannon/CramerCltBoundaryClosure.lean`, ~62 行)
- [x] Phase 2 — portmanteau half-line bridge (frontier null + 適用) ✅ `tilted_halfline_tendsto_half` (`05ed225`)
- [x] Phase 3 — CLT を tilted ambient へ適用 (witness 構築 + 既存 plumbing 注入) ✅ `tilted_halfline_tendsto_gaussian` + `gaussianReal_hasLaw_id` (`05ed225`)
- [x] Phase 4 — 窓質量 → 1/2 (集合書換 + LLN 引き算) + `tiltedWindow_eventually_large_of_boundary` ✅ (`05ed225`)
- [x] Phase 5 — residual predicate 緩和 (`1/2 → ∃C>0`) + boundary discharge ✅ `tilted_window_lower_to_halfline` + 緩和 reduction (`05ed225`)
- [x] Phase 6 — Cramér end-to-end ✅ `cramer_lower_boundary_unconditional` (`05ed225`)、独立監査 PASS

## Sub-plan 一覧

| 子 plan | 担当 | 状態 |
|---|---|---|
| [`cramer-root-wiring-plan.md`](cramer-root-wiring-plan.md) | 未配線残件 = headline で上流 root sorry 2 件 (`cramer_lower_phaseC_partial_discharge` / `cramer_lower`) を discharge。cycle-break (8 decl hoist) + `hVar` precondition thread + root B 下流移設 (`CramerGeneralLower.lean`) + transport | ✅ Phase A (`7e4f05a`) + Phase B 完了、両 root sorryAx-free |

## ゴール / Approach

### Goal (完成判定)

新ファイル `InformationTheory/Shannon/CramerCltBoundaryClosure.lean` で 0-sorry、`lake env lean` clean、
`InformationTheory.lean` に `import` 1 行追加。最終 publish:

1. `gaussianReal_Ici_eq_half` (Gaussian median): `(v ≠ 0) → gaussianReal 0 v {x | 0 ≤ x} = 1/2`。
2. `tiltedWindow_eventually_large_of_boundary` (境界 per-instance): `a = m`、tilted 分散
   非退化のとき窓質量 eventually `≥ 1/4`。
3. residual predicate 緩和形 (`IsTiltedWindowEventuallyLargeC` or `1/2 → C` 一般化) +
   `IsMeasureInfinitePiTiltedEq` の境界 discharge。
4. `cramer_lower_boundary_unconditional` (end-to-end): `a = deriv (cgf Y μ₀) lam` (内部点)
   で `cramer_lower_phaseC_residual_discharge` の residual hypothesis を除去した形。

### Approach (overall strategy / shape of solution)

**全体像** — 親 residual `IsTiltedWindowEventuallyLarge` の `1/2` largeness は interior
(`a < m < a+ε`) では両側 LLN-squeeze で取れる (既存 `tiltedWindow_eventually_large_of_interior`)。
境界 `a = m` では `a ≤` 側が等号になり LLN が片側でしか効かない。**CLT で「ちょうど境界での
窓質量は漸近的に 1/2 (Gaussian median)」を実証して埋める**。

```
P := infinitePi (μ₀.tilted (lam·Y))         -- tilted ambient (既存 IsProbabilityMeasure)
X i ω := Y (ω i)                            -- eval family (既存 plumbing の X)
m := P[X 0] = ∫ Y ∂(μ₀.tilted (lam·Y))      -- tilted mean = deriv (cgf Y μ₀) lam (既存 bridge)
v := Var[X 0; P]                            -- tilted variance (CLT の極限分散)

[Phase 3 CLT 適用]
  tendstoInDistribution_inv_sqrt_mul_sum_sub に
    hindep := iIndepFun_tilted_ambient            (既存、字面一致)
    hident := fun i => identDistrib_tilted_ambient i (既存、字面一致)
    hX     := memLp_of_bounded (bounded_eval_family)   (Mathlib + 既存 bound)
    hY     := HasLaw id (gaussianReal 0 v.toNNReal) (gaussianReal 0 v.toNNReal)  ← witness 自前
  を注入
  ⇒ S_n := (√n)⁻¹·(∑_{k<n} X k − n·m) →d gaussianReal 0 v.toNNReal
  .tendsto field ⇒ Tendsto (n ↦ ⟨P.map S_n, _⟩) atTop (𝓝 ⟨gaussianReal 0 v, _⟩) (ProbabilityMeasure ℝ)

[Phase 2 portmanteau half-line]
  E := {x | 0 ≤ x} = Set.Ici 0; frontier E = {0} (frontier_Ici)
  E_nullbdry := noAtoms_gaussianReal (v≠0) ⇒ gaussianReal 0 v {0} = 0
  tendsto_measure_of_null_frontier_of_tendsto' に CLT .tendsto を注入
  ⇒ Tendsto (n ↦ (P.map S_n)(Ici 0)) atTop (𝓝 (gaussianReal 0 v (Ici 0)))

[scaling 変形 — Approach の核心]
  {ω | m·n ≤ ∑_{i<n} Y(ω i)} = S_n ⁻¹' (Ici 0)        (n ≥ 1 で √n > 0)
    ∵ 0 ≤ (√n)⁻¹·(∑Y − n·m) ⟺ 0 ≤ ∑Y − n·m ⟺ m·n ≤ ∑Y
  Measure.map_apply (Measurable S_n, MeasurableSet (Ici 0))
  ⇒ (P.map S_n)(Ici 0) = P(S_n⁻¹'(Ici 0)) = P{m·n ≤ ∑Y}
  ⇒ Tendsto (n ↦ P{m·n ≤ ∑Y}) atTop (𝓝 (gaussianReal 0 v (Ici 0)))

[Phase 1 Gaussian median]
  gaussianReal 0 v (Ici 0) = 1/2       ← gaussianReal_Ici_eq_half (v≠0)
  ⇒ Tendsto (n ↦ P{m·n ≤ ∑Y}) atTop (𝓝 (1/2))

[Phase 4 窓質量 → 1/2]
  窓質量 = P{m·n ≤ ∑Y} − P{(m+ε)·n ≤ ∑Y}
  P{(m+ε)·n ≤ ∑Y} → 0  ← 既存 tilted_lln_in_probability_real ((m+ε) > m で右側脱落)
  ⇒ 窓質量 → 1/2 ≥ 1/4 eventually  ⇒ tiltedWindow_eventually_large_of_boundary

[Phase 5 緩和 + discharge]
  residual predicate を 1/2 → ∃C>0 (or C=1/4 固定) に一般化、reduction 補題の refine ⟨1/2,..⟩
  を ⟨C,..⟩ に置換 ⇒ IsMeasureInfinitePiTiltedEq を a=m で discharge

[Phase 6 Cramér end-to-end]
  a := deriv (cgf Y μ₀) lam = m (tiltedMean_eq_deriv_cgf) ⇒ cramer_lower_phaseC_residual_discharge
  の h_res を内部で供給 ⇒ residual hypothesis なしの Cramér 下界
```

**scaling 変形の明示**: CLT は `(√n)⁻¹·(∑(Yₖ−m))` を出すが、欲しいのは `{∑Y/n ≥ m}`
= `{m·n ≤ ∑Y}`。これらは `n ≥ 1` のとき `{(√n)⁻¹·(∑(Yₖ) − n·m) ≥ 0}` と **集合として等しい**
(正のスカラー `(√n)⁻¹` 倍は不等号の向きを保つ、`∑(Yₖ−m) = ∑Yₖ − n·m`)。`n = 0` は
eventually で捨てる。この preimage 同一視 `{m·n ≤ ∑Y} = S_n⁻¹'(Ici 0)` が CLT の出力を
窓質量に接続する蝶番。

**Mathlib-shape-driven note** (CLAUDE.md §): CLT 結論 `S_n := (√n)⁻¹·(∑X − n·P[X 0])` の
**形をそのまま** preimage 同一視に使う。窓質量の方を CLT 形に書き換える (逆ではない) ことで
「`(√n)⁻¹∑(Yₖ−m)` を `∑Y/n` に変換する bridge lemma」の自作を回避する。median も `cdf`
経由ではなく `gaussianReal_map_neg` symmetry-by-map で出す (cdf 1/2 lemma は Mathlib 不在で
逆に高コスト、在庫 §3 確認済)。

### 退化処理 (分散正値 v > 0)

- **v = 0 (Y が tilted ambient で a.e. 定数)** のとき: median 1/2 が崩れ (`{0≤·}` 質量が 0/1)、
  `noAtoms_gaussianReal` 前提 `v ≠ 0` も崩れる。窓質量も境界で 0/1 ジャンプし `1/4` 下界が
  成立しない。**この 1 ケースは仕様から除外** — `hVar : 0 < Var[X 0; P]` を hypothesis として
  要求する。
- **自然性の根拠** (在庫 §5): Cramér / Chernoff の非自明 rate function (`Λ* > 0` 領域) では
  `Λ'' = iteratedDeriv 2 (cgf) > 0` が常に成立し、`v = Var[Y; μ₀.tilted (lam·Y)]
  = iteratedDeriv 2 (cgf Y μ₀) lam` (`variance_tilted_mul`) なので **非退化前提は文脈で自動的に
  満たされる**。退化 Y (定数列) は Cramér が自明に成り立つ縮退ケースで除外して問題ない。
- `hVar` を `Λ'' > 0` 形に翻訳する corollary (`variance_tilted_mul` 経由) は **オプション**
  (Phase 6 で時間があれば、cgf 凸性の言葉で使いやすくする糖衣)。

### 鍵 lemma の verbatim signature (在庫より転記、Phase 着手時に再確認)

**CLT** (`Mathlib/Probability/CentralLimitTheorem.lean:123`):
```lean
theorem tendstoInDistribution_inv_sqrt_mul_sum_sub
    {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {P : Measure Ω} {P' : Measure Ω'} {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hY : HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * P[X 0]))
      atTop Y (fun _ ↦ P) P'
```
型クラス前提: `[IsProbabilityMeasure P] [IsProbabilityMeasure P']` のみ
(StandardBorelSpace / Countable 等 **無し**、codomain ℝ 固定)。

**portmanteau half-line** (`Mathlib/MeasureTheory/Measure/Portmanteau.lean:333`):
```lean
theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' {Ω ι : Type*}
    {L : Filter ι} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    [HasOuterApproxClosed Ω] {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω}
    (μs_lim : Tendsto μs L (𝓝 μ)) {E : Set Ω} (E_nullbdry : (μ : Measure Ω) (frontier E) = 0) :
    Tendsto (fun i ↦ (μs i : Measure Ω) E) L (𝓝 ((μ : Measure Ω) E))
```
型クラス前提: `[OpensMeasurableSpace ℝ] [HasOuterApproxClosed ℝ]` — **ℝ で自動充足**
(StandardBorelSpace / PolishSpace 不要)。

**Gaussian symmetry / no atoms** (`Mathlib/.../Distributions/Gaussian/Real.lean`):
```lean
lemma noAtoms_gaussianReal {μ : ℝ} {v : ℝ≥0} (h : v ≠ 0) : NoAtoms (gaussianReal μ v)       -- :213
lemma gaussianReal_map_neg : (gaussianReal μ v).map (fun x ↦ -x) = gaussianReal (-μ) v       -- :330
```

**MemLp from bounded** (`Mathlib/.../LpSeminorm/Basic.lean:557`): `memLp_of_bounded`
(要 `[IsFiniteMeasure P]`、確率測度で充足)。

**既存 plumbing** (字面一致で CLT 引数に注入可、`InformationTheory/Shannon/Cramer/LC2Discharge.lean`):
```lean
lemma iIndepFun_tilted_ambient (hY_meas) (h_bdd) (lam) :          -- :85
    iIndepFun (fun (i : ℕ) (ω : ℕ → Ω₀) => Y (ω i))
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)))
lemma identDistrib_tilted_ambient (hY_meas) (h_bdd) (lam) (i : ℕ) :  -- :98
    IdentDistrib (fun ω : ℕ → Ω₀ => Y (ω i)) (fun ω : ℕ → Ω₀ => Y (ω 0)) P P
```

**既存 tilted bridge / LLN** (`Shannon/Cramer/InfinitePiTiltedChangeOfMeasure.lean` / `Shannon/Cramer/LC2DischargeExt.lean`):
```lean
theorem tiltedMean_eq_deriv_cgf (hY) (h_bdd) (lam) :    -- :489
    ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)) = deriv (cgf Y μ₀) lam
theorem tilted_lln_in_probability_real ...              -- CramerLC2DischargeExt.lean:236
```

**変分曲率 link** (`Mathlib/Probability/Moments/Tilted.lean:159`、オプション):
```lean
lemma variance_tilted_mul (ht : t ∈ interior (integrableExpSet X μ)) :
    Var[X; μ.tilted (t * X ·)] = iteratedDeriv 2 (cgf X μ) t
```

### 規模見積もり (Phase 別、中央予測 ~120-210 行)

| Phase | 自作要素 | 難度 | 既存度 | 推定行数 |
|---|---|---|---|---|
| 0 | signature 再確認 (本 plan 転記の verbatim 固定) | — | — | 0 (調査) |
| 1 | `gaussianReal_Ici_eq_half` (median) | **(c) 一から** | **0%** | **40-70** |
| 2 | portmanteau half-line (frontier null + 適用) | (b) 組立 | lemma 既存 | 20-35 |
| 3 | CLT tilted 適用 (witness + plumbing 注入) | (b) 組立 | plumbing 100% | 30-50 |
| 4 | 窓質量 → 1/2 (集合書換 + LLN 引き算) + boundary 補題 | (b) 組立 | LLN 既存 | 30-50 |
| 5 | residual 緩和 (1/2 → ∃C) + discharge | (a) ほぼ直接 | reduction 既存 | 5-20 |
| 6 | Cramér end-to-end + verify + 親反映 | (a) 直結 | 全足場既存 | 10-25 |
| | **合計 (full closure)** | — | ≈80% | **~135-250** |

### 1 unit 完遂見込みか分割か

**判定: 1 unit で chain して full closure を狙う (~135-250 行、seed 制約 ~150-400 行内)。
ただし Phase 2-3 (CLT + portmanteau) を **boundary 補題内に inline** せず、独立 helper として
段組みする** (skeleton で各 helper を `:= by sorry` で立てて 1 つずつ埋める)。Phase 1 (median)
は他から完全に独立なので **最初に建てて単独で閉じる** (撤退時の単独 PR-target 化が容易)。
Phase 3 の CLT witness 構築 (`HasLaw id` の `.toNNReal` 変換) と Phase 1 median が二大難所
なので、両方が 1 セッションで割れない兆候が出たら下記撤退ラインへ。

## Phase 0 — Mathlib + 既存足場 signature 再確認 📋

proof-log: no (調査のみ)

### スコープ

着手前に在庫 §1-6 の鍵 lemma を `file:line` + 完全前提リスト verbatim で **本 plan に既に転記済**
(上記「鍵 lemma の verbatim signature」)。Phase 1 着手直前に以下を loogle / Read で **最終確認**:

- [ ] `tendstoInDistribution_inv_sqrt_mul_sum_sub` の `HasLaw` 引数の正確な形 (`gaussianReal 0 Var[X 0;P].toNNReal`) と `TendstoInDistribution` structure の `.tendsto` field 型
- [ ] `gaussianReal_map_neg` の暗黙引数 `{μ v}` 順 + `noAtoms_gaussianReal` の `v ≠ 0` 形 (`≠ 0` vs `0 < v`)
- [ ] `frontier_Ici` の正確な名前と結論 (`frontier (Set.Ici a) = {a}`)
- [ ] `Measure.map_apply` の可測前提 (`Measurable f`, `MeasurableSet s`)
- [ ] `gaussianReal 0 v (univ) = 1` (`instIsProbabilityMeasureGaussianReal`)、`{0≤·} ∪ {·≤0} = univ`、`{0≤·} ∩ {·≤0} = {0}` の集合計算ルート
- [ ] `tilted_lln_in_probability_real` の **正確な結論形** (`.real` 形、収束先、`(m+ε)` 側の符号) を再 Read

### Done 条件

- 上記 6 点の verbatim 形が確定し、Phase 1-4 skeleton の sorry statement が正確に書ける。

## Phase 1 — `gaussianReal_Ici_eq_half` (Gaussian median) 📋

proof-log: yes (唯一の「一から」、落とし穴記録のため)

### スコープ

```lean
theorem gaussianReal_Ici_eq_half {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal 0 v {x : ℝ | (0 : ℝ) ≤ x} = 1 / 2
```

実装ルート (在庫 §3 推奨、symmetry-by-map):

- [ ] `x ↦ -x` で `{0≤·}` の preimage は `{·≤0}`、`gaussianReal_map_neg` (μ=0 で固定点) ⇒
  `gaussianReal 0 v {0≤·} = gaussianReal 0 v {·≤0}` (要 `Measure.map_apply` + 可測 `{0≤·}`)
- [ ] `{0≤·} ∪ {·≤0} = univ` (= 1)、交わり `{0}` は `noAtoms_gaussianReal (hv)` で 0
- [ ] `measure_union_add_inter` 系で `2 · (half-line) = 1`、ℝ≥0∞ 算術 (`2 * x = 1 → x = 1/2`)

**落とし穴** (在庫 §3): (i) ℝ≥0∞ 算術 (`ENNReal.eq_div_of_...` / `2*x=1`)、(ii) `map` 下の
measure 値引き戻し (`Measure.map_apply` 可測前提)、(iii) 集合計算 `∪ = univ` / `∩ = {0}`。

### Done 条件

- `gaussianReal_Ici_eq_half` が `lake env lean` clean (0 sorry)。これ単独で閉じれば
  撤退ライン L-CLT1 の最悪ケースを回避済。

## Phase 2 — portmanteau half-line bridge 📋

proof-log: no

### スコープ

CLT `.tendsto` (Phase 3 で供給) を受けて `Tendsto (n ↦ (P.map S_n)(Ici 0)) atTop
(𝓝 (gaussianReal 0 v (Ici 0)))` を出す helper。

- [ ] `E := Set.Ici (0:ℝ)`、`frontier E = {0}` (`frontier_Ici`)
- [ ] `E_nullbdry : gaussianReal 0 v {0} = 0` ← `noAtoms_gaussianReal hv`
- [ ] `tendsto_measure_of_null_frontier_of_tendsto'` に CLT の `.tendsto`
  (`Tendsto (n ↦ ⟨P.map S_n, _⟩) atTop (𝓝 ⟨gaussianReal 0 v, _⟩)`) を `μs_lim` として注入

**注意**: Phase 3 の CLT 出力 (`ProbabilityMeasure` 値の `Tendsto`) を Phase 2 が受ける
依存があるので、skeleton では Phase 3 helper の結論を hypothesis に取る形で Phase 2 を先に
立て、Phase 3 で供給する。`HasOuterApproxClosed ℝ` instance は自動 (在庫 §2)。

### Done 条件

- portmanteau bridge helper が `lake env lean` clean。

## Phase 3 — CLT を tilted ambient へ適用 📋

proof-log: yes (CLT witness 構築の `.toNNReal` 変換が難所)

### スコープ

`tendstoInDistribution_inv_sqrt_mul_sum_sub` を tilted ambient に適用して
`TendstoInDistribution S_n atTop id (fun _ => P) (gaussianReal 0 v.toNNReal)` を得、
`.tendsto` を取り出す helper。

- [ ] `P := infinitePi (μ₀.tilted (lam·Y))`、`[IsProbabilityMeasure P]` ←
  `isProbabilityMeasure_infinitePi_tilted_of_bounded` (既存)
- [ ] `X i ω := Y (ω i)`、`hindep := iIndepFun_tilted_ambient` (既存、字面一致)
- [ ] `hident := fun i => identDistrib_tilted_ambient i` (既存、`∀ i, IdentDistrib (X i) (X 0) P P`)
- [ ] `hX := memLp_of_bounded (bounded_eval_family ...)` (Mathlib + 既存 bound、`[IsFiniteMeasure P]` 充足)
- [ ] **witness** `hY : HasLaw id (gaussianReal 0 v.toNNReal) (gaussianReal 0 v.toNNReal)`
  自前構築 — `(ℝ, gaussianReal 0 v, id)` で `map id = self` から `HasLaw id (gaussianReal ...) (gaussianReal ...)`
- [ ] `.tendsto` field を取り出して Phase 2 に渡す形に整形

**落とし穴** (在庫 §自作要素 2): (i) `HasLaw id` witness の `gaussianReal 0 v.toNNReal` の
`.toNNReal` / `ℝ≥0` 変換 (`v := Var[X 0;P]` は `ℝ`、CLT は `.toNNReal` を要求)、
(ii) `Var[X 0;P]` の `.toReal` / 正値 (`hVar`) の往復、(iii) `S_n` 可測性 (`eval ∘ sum` の `fun_prop`)。

### Done 条件

- CLT 適用 helper が `lake env lean` clean。Phase 2 と接続して
  `Tendsto (n ↦ (P.map S_n)(Ici 0)) atTop (𝓝 (gaussianReal 0 v (Ici 0)))` が得られる。

## Phase 4 — 窓質量 → 1/2 + `tiltedWindow_eventually_large_of_boundary` 📋

proof-log: yes (集合書換 + LLN 引き算)

### スコープ

scaling 集合書換 + Phase 1-3 合成 + LLN 引き算で boundary 補題を出す。

- [ ] **scaling 書換**: `{ω | m·n ≤ ∑_{i<n} Y(ω i)} = S_n ⁻¹' (Ici 0)` (`n ≥ 1`)、
  `Measure.map_apply` ⇒ `(P.map S_n)(Ici 0) = P{m·n ≤ ∑Y}`
- [ ] Phase 2-3 + Phase 1 (median) 合成 ⇒ `Tendsto (n ↦ P{m·n ≤ ∑Y}) atTop (𝓝 (1/2))`
- [ ] `(m+ε)` 側: `P{(m+ε)·n ≤ ∑Y} → 0` ← 既存 `tilted_lln_in_probability_real`
- [ ] 窓質量 = 半直線(m) − 半直線(m+ε) → 1/2、`eventually` で `≥ 1/4`

主定理:
```lean
theorem tiltedWindow_eventually_large_of_boundary
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω₀ => Y (ω 0);
        Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))]) :
    ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / 4 ≤ (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).real
          {ω : ℕ → Ω₀ |
            (∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)
            ∧ ∑ i ∈ Finset.range n, Y (ω i)
                < ((∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) + ε) * n}
```

**落とし穴**: (i) `n = 0` を eventually で捨てる、(ii) `(√n)⁻¹ > 0` の不等号保存、
(iii) 窓質量 = 差の `.real` 算術 (収束差は `Tendsto.sub`)、(iv) `m = ∫ Y ∂tilted` 表記の統一
(deriv cgf 形は Phase 6 で `tiltedMean_eq_deriv_cgf` で繋ぐ)。

### Done 条件

- `tiltedWindow_eventually_large_of_boundary` が `lake env lean` clean。

## Phase 5 — residual predicate 緩和 + boundary discharge 📋

proof-log: no

### スコープ

在庫 §6 の緩和判定: `isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge` の内部は
`refine ⟨1/2, ..., ...⟩` で C を流すだけで `1/2` 特定値依存なし。よって residual を `∃C>0` 形に
一般化しても reduction 補題が通る。

- [ ] 緩和 predicate (本 plan 新 file 内): `IsTiltedWindowEventuallyLargeC μ₀ Y lam`
  = `∀ a ε, 0 < ε → ∃ C > 0, ∀ᶠ n, C ≤ 窓質量` (or `C = 1/4` 固定)
- [ ] 緩和版 reduction `isMeasureInfinitePiTiltedEq_of_tiltedWindowLargeC`
  (既存 `isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge` の `⟨1/2,..⟩ → ⟨C,..⟩` 置換コピー)。
  **注意**: 既存定理は predecessor file にあり編集境界外 — 本 plan の新 file に **新規 reduction
  を書く** (既存を改変しない)
- [ ] `a = m` で `tiltedWindow_eventually_large_of_boundary` を流して緩和 predicate を充足、
  `IsMeasureInfinitePiTiltedEq` を境界で discharge

**設計判断**: 既存 `IsTiltedWindowEventuallyLarge` (1/2, predecessor file) は **触らない**。
本 file で `∃C>0` 緩和版を新規定義し、reduction も新規に書く (predecessor file への
breaking change を避ける)。境界補題の `1/4` を `C := 1/4` で吸収。

### Done 条件

- 緩和 predicate + 緩和 reduction が `lake env lean` clean、`a = m` で
  `IsMeasureInfinitePiTiltedEq` を実証。

## Phase 6 — Cramér end-to-end + verify + 親反映 📋

proof-log: no

### スコープ

- [ ] `a := deriv (cgf Y μ₀) lam` が tilted mean `m` (`tiltedMean_eq_deriv_cgf`) なので、
  Phase 5 の boundary discharge を `a = m` インスタンスとして
  `cramer_lower_phaseC_residual_discharge` の `h_res` 相当に供給
- [ ] `cramer_lower_boundary_unconditional` (end-to-end): 内部点 `a = deriv (cgf Y μ₀) lam` で
  residual hypothesis を除去した Cramér 下界
  (`h_coboundedBelow` は据え置きか、これも内部 discharge できるか着手時判断 — できなければ
  hypothesis として残す)
- [ ] (オプション) `hVar` を `Λ'' > 0` 形に翻訳する糖衣 corollary (`variance_tilted_mul`)
- [ ] `lake env lean InformationTheory/Shannon/CramerCltBoundaryClosure.lean` clean
- [ ] `InformationTheory.lean` に `import InformationTheory.Shannon.CramerCltBoundaryClosure` 追記
- [ ] 親 `infinitepi-tilted-rn-discharge-moonshot-plan.md` の W-3 を 🔄 → 部分達成 (境界 CLT closure
  済) に反映、本 plan §判断ログに着地形を追記

### Done 条件

- end-to-end 定理が clean、`InformationTheory.lean` import 済、親 plan W-3 状態更新済。

## ファイル構成

```
InformationTheory/Draft/Shannon/
  InfinitePiTiltedChangeOfMeasure.lean   ← 既存 (0 sorry, 変更なし)
InformationTheory/Shannon/Cramer/
  LC2Discharge.lean                      ← 既存 (変更なし、plumbing 利用)
  LC2DischargeExt.lean                   ← 既存 (変更なし、LLN + IsProbabilityMeasure 利用)
InformationTheory/Shannon/
  CramerCltBoundaryClosure.lean          ← Phase 1 で新規作成済 (62 行, 0 sorry); Phase 2-6 を追記
InformationTheory.lean                          ← import 1 行追記
docs/shannon/
  cramer-chernoff-clt-closure-mathlib-inventory.md  ← 既存 (predecessor、verdict GO)
  cramer-chernoff-clt-closure-moonshot-plan.md      ← 本ファイル (新規)
```

## 撤退ライン

> sorry 禁止。詰まったら最小 residual を predicate / hypothesis pass-through で抜く。
> proof-pivot-advisor トリガ: 下記いずれか発動の判断時。

**L-CLT1** (Gaussian median が ℝ≥0∞ 算術で 1 セッション詰まる): `gaussianReal_Ici_eq_half`
(Phase 1) を `(hMedian : gaussianReal 0 v {0≤·} = 1/2)` の **hypothesis pass-through** で
boundary 補題が受ける形に縮退 (median 自体は別 file の単独 PR-target 補題として切り出し、
本 file は足場のみ publish、sorry なし)。着地 ~90 行。

**L-CLT2** (CLT witness 構築 `HasLaw id (gaussianReal ...)` の `.toNNReal` 変換が詰まる):
Phase 3 を `(hCLT : Tendsto (n ↦ (P.map S_n)(Ici 0)) atTop (𝓝 (1/2)))` 形 hypothesis
pass-through で boundary 補題が受ける形に縮退 (CLT 適用は別 plan defer)。着地 ~70 行。

**L-CLT3** (Phase 4 集合書換 / LLN 引き算が詰まる): boundary 補題を緩和 predicate
`IsTiltedWindowEventuallyLargeC` のまま (sorry なし)、`a = m` での具体充足は **predicate 仮定**
として残す (現 W-3 state よりは緩和 predicate を新 publish した分だけ前進)。着地 ~50 行。

**最悪着地** (全 piece が割れない): Phase 1 median のみ単独 publish (~50-70 行)。これだけでも
Mathlib PR-candidate として価値があり、後退ゼロ。

**現時点判断**: **full closure を 1 unit で狙う** (Phase 1 median と Phase 3 CLT witness の二大
難所が両方割れる前提)。Phase 1 を最初に閉じて L-CLT1 を即回避、続いて Phase 3 で L-CLT2 判定。

## 判断ログ

> 書く頻度: Phase 終了時 / 設計変更 / 撤退判定。append-only。

1. **2026-05-20 起草**: 親 `infinitepi-tilted-rn-discharge` §W-3 (residual predicate 着地) からの
   **上振れ復帰 plan** として起草。在庫 `cramer-chernoff-clt-closure-mathlib-inventory.md`
   (verdict GO、既存率 ≈80%、自作 2 件 = Gaussian median + boundary 統合) を受け、CLT
   (`tendstoInDistribution_inv_sqrt_mul_sum_sub`) + portmanteau half-line + Gaussian median
   (symmetry-by-map 自作) で境界 `a = m` を埋める方針を採用。退化 `v = 0` は仕様除外
   (`hVar : 0 < Var` を hypothesis 要求、Cramér 非自明領域では `Λ'' > 0` で自動充足)。
   既存 predecessor 3 file (`InfinitePiTiltedChangeOfMeasure` / `CramerLC2Discharge` /
   `CramerLC2DischargeExt`) は **変更せず**、緩和 predicate と reduction は本 file に新規追加
   (predecessor への breaking change 回避)。median (Phase 1) を最初に閉じて撤退ライン L-CLT1 を
   即回避する着手順を採用。

2. **2026-06-11 consumer def-fix 完了 (前提整備、本 plan Phase 0-6 は未着手のまま)** (`f62be91`、判断ログ #24 / roadmap):
   本 plan が closure する **下流 consumer 2 root** (`cramer_lower` / `cramer_lower_phaseC_partial_discharge`) は
   #19 で false-statement (一般 `a` で偽) と判明していた。今回 `(h_deriv : deriv (cgf (X 0) μ) lam = a)` を
   signature に追加し true-as-stated 化 (`@audit:defect(false-statement)` → `@residual(plan:` 本 plan `)`、
   独立監査 PASS)。**効果**: 本 plan の closure target (Phase 6 `cramer_lower_boundary_unconditional`、
   内部点 `a = deriv (cgf Y μ₀) lam`) が consumer root の signature と **字面一致** — 以前の
   「plan が `a=deriv cgf lam` を狙うのに root は一般 `a` で over-promise」状態が解消。Phase 6 で
   `h_deriv` を `tiltedMean_eq_deriv_cgf` (`a = m = deriv cgf lam`) から供給する配線が直結になった。
   **本体 (Phase 1 median + Phase 3 CLT witness) は依然未着手**、規模見積 ~135-250 行・二大難所
   (median「一から」+ CLT witness `.toNNReal`) は変わらず。着手時は gateway-atom-first (Phase 1 median 単独閉じ)
   で tractability 確認してから full closure へ。

3. **2026-06-11 Phase 1 gateway CLOSED → 継続 GO** (`1a19915`):
   `gaussianReal_Ici_eq_half` を `InformationTheory/Shannon/CramerCltBoundaryClosure.lean` に
   symmetry-by-map (`gaussianReal_map_neg` μ=0 固定点 + `Measure.map_apply` → `μ(Ici 0)=μ(Iic 0)`、
   `measure_union_add_inter` で `1+0=2·μ(Ici 0)`、`ENNReal.eq_div_iff` で `=1/2`) で **0 sorry / sorryAx-free**
   閉じた (62 行、自作補題ゼロ、全て既存 Mathlib 組立)。落とし穴 3 点 (ℝ≥0∞ 算術 / map 引戻し / 集合計算) は
   `ENNReal.eq_div_iff` + `fun_prop` + `Set.Iic_union_Ici`/`Set.Ici_inter_Iic` で無痛。二大難所の片方が割れ
   **撤退ライン L-CLT1 (最悪ケース) 回避済**。
   **plumbing 実在 再確認 (継続判断の前提)**: 実装 agent が「predecessor 3 file 不在」と 気づき を上げたが
   **誤報** — `fdd68a3` の昇格 refactor で `Shannon/CramerLC2Discharge.lean` → `Shannon/Cramer/LC2Discharge.lean`
   等にパス移動しただけ。plan 依存 11 シンボル (`iIndepFun_tilted_ambient` … `cramer_lower_phaseC_residual_discharge`)
   を補題名 grep で全て実機確認 = **plumbing 健在**。stale パスは本 plan 上で訂正済 (上記 Predecessors / file 構成)。
   → 継続 GO。次 = Phase 2-6 full closure (CLT witness `.toNNReal` が残る二大難所、~70-180 行)。

4. **2026-06-11 Phase 2-6 full closure 達成 + 独立監査 PASS** (`05ed225`):
   Phase 2-6 を 1 セッションで全閉。`CramerCltBoundaryClosure.lean` (586 行, 0 sorry / 0 @residual, sorryAx-free)。
   - **Phase 3 (二大難所)**: `tilted_halfline_tendsto_gaussian` — Mathlib CLT を tilted ambient に適用、witness
     `gaussianReal_hasLaw_id` (`HasLaw id (gaussianReal 0 w) (gaussianReal 0 w)` を `Measure.map_id` で自作) +
     portmanteau (`frontier (Ici 0) = {0}` null by `noAtoms`) + scaling preimage 同一視
     `{m·n ≤ ∑Y} = S_n⁻¹'(Ici 0)` (`mul_nonneg_iff_of_pos_left`)。
   - **Phase 5 設計判断 (honesty)**: plan が想定した `∀a∀ε` 緩和 predicate `IsTiltedWindowEventuallyLargeC` は
     **false-as-framed** (a が tilted mean から遠いと窓質量消失、predecessor 自認)。これを「証明済」とせず
     **reduction tool (true implication、predicate を hypothesis に取る)** に留め、Phase 6 は `∀a` predicate を
     **bypass** して per-`(a,ε)` core `tilted_window_lower_to_halfline` を `a=m` で直接呼ぶ。headline の証明経路に
     false predicate は **乗らない** (監査 term 依存確認済)。
   - **Phase 6 headline `cramer_lower_boundary_unconditional`**: 仮説は全て precondition
     (`hY`/`h_bdd`/`hlam`/`h_deriv`(最適 tilt 位置, def-fix #24 と同型)/`hVar`(非退化)/`h_coboundedBelow`(liminf 正則性,
     `cramer_lower` 継承))。CLT 窓質量は内部供給 = load-bearing bundling なし。`ε→0⁺` collapse (`le_of_forall_sub_le`)
     で sharp exponent `-(λm − Λ)`。
   - **独立 honesty 監査 PASS** (honesty-auditor, `@audit:ok` 全 10): under-hyp / load-bearing / false-predicate 隔離 /
     degenerate 濫用 / consumer 字面一致 / sorryAx-free を機械裏取り。特に `h_coboundedBelow` の **非 vacuous 性**
     (`P≤1 ⇒ log≤0` で上有界 → `b=0` 充足) を別ファイルで検証。
   - **残件 (未達でなく配線制約)**: consumer root `cramer_lower_phaseC_partial_discharge`
     (`Shannon/Cramer/LC2PhaseC.lean:165`) は import cycle で in-place 書換不可。root の sorry は本 closure を指す
     live residual として残置 (冒頭バナー)。`InformationTheory.lean` import 済 (`lake build` 2972 jobs clean)。
   **moonshot CLOSED。** 後続候補: root residual の差し替え経路 (import cycle 解消 or 別 entry_point 化) は別 plan。

5. **2026-06-11 配線残件 (上記「後続候補」) も closure — 子 `cramer-root-wiring-plan.md` 完了** (roadmap 判断ログ #26、`7e4f05a`/`184affa`/`8a8a001`):
   #4 で「別 plan」とした closed-but-unwired 2 root を子 plan で解消。root A は 8 decl 上流 hoist の cycle-break で `exact headline`、root B (`cramer_lower`) は下流 `CramerGeneralLower.lean` へ移設し iid joint law transport で discharge。両 root sorryAx-free、独立監査 `@audit:ok` 12 件。project 実 sorry 17→15。**Cramér CLT-boundary は headline + 上流両 root とも完全 closure。**

6. **2026-06-13 orphan cleanup で Phase 5 reduction tool 2 件を削除** (orphan sweep):
   Phase 6 headline が bypass する緩和 predicate `IsTiltedWindowEventuallyLargeC` (def、false-as-framed) +
   それを唯一の consumer とする reduction `isMeasureInfinitePiTiltedEq_of_tiltedWindowLargeC` (consumer 0) は、
   closure 後 dead scaffolding 化していた (headline は live core `tilted_window_lower_to_halfline` を `a=m` で
   直接呼ぶ)。3点照合 (dep_consumers transitive 0 + 全ツリー textual grep = prose のみ) で削除、`#print axioms
   cramer_lower_boundary_unconditional` = `[propext, Classical.choice, Quot.sound]` 維持を確認。上記 #4 の
   「reduction tool に留め」記述は履歴 (削除前の状態)。false-as-framed の知見自体は roadmap 判断ログに残置。
