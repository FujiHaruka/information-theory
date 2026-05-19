# T2-B L-PG0 discharge: Parallel Gaussian kernel measurability

撤退ライン **L-PG0 (parallel kernel measurability)** — predicate

```
IsParallelGaussianKernelMeasurable N
  := Measurable (fun x : Fin n → ℝ =>
       Measure.pi (fun i => gaussianReal (x i) (N i)))
```

— の Mathlib 直接 discharge を与え、`parallel_gaussian_capacity_formula` と
`parallel_gaussian_capacity_active_form` を `h_parallel_meas` 引数なし形で
re-publish する。

## Context

* 親 `Common2026/Shannon/ParallelGaussian.lean` (381 行、2026-05-19 publish)
  は L-PG0 を `h_parallel_meas : IsParallelGaussianKernelMeasurable N`
  hypothesis として外出ししている。L-PG0 が消えれば `IsParallelAwgnChannelMeasurable N`
  (= per-coord `IsAwgnChannelMeasurable (N i)`) から parallel kernel
  measurability が自動で導かれる。
* T2-A 親 `awgn_channel_coding_theorem` の F-1 (= per-coord
  `IsAwgnChannelMeasurable`) は本セッションで `AWGNF1Discharge.lean`
  により `gaussianReal_map_const_add` 経由で discharge 済。
  本 plan はその拡張パターン。

## Approach

**核心の観察**: `gaussianReal (x i) (N i) = (gaussianReal 0 (N i)).map (x i + ·)`
を全 `i` について並べると、

```
Measure.pi (fun i => gaussianReal (x i) (N i))
  = Measure.pi (fun i => (gaussianReal 0 (N i)).map (x i + ·))
  = (Measure.pi (fun i => gaussianReal 0 (N i))).map (fun y i => x i + y i)
```

最後の等号は **`Measure.pi_map_pi`** (`Mathlib.MeasureTheory.Constructions.Pi:390`):

```
(Measure.pi μ).map (fun x i ↦ f i (x i)) = Measure.pi (fun i ↦ (μ i).map (f i))
```

を `μ = fun i => gaussianReal 0 (N i)`, `f i = (x i + ·)` で右辺→左辺向きに使う。

すなわち parameter-dependent 量 `Measure.pi (fun i => gaussianReal (x i) (N i))`
を、**固定の** product Gaussian `Measure.pi (fun i => gaussianReal 0 (N i))`
(これは IsProbabilityMeasure → SFinite) の "parameter-dependent shift map による
pushforward" として書き直す。

そうすると AWGN F-1 と全く同じ Giry monad 議論が使える:

* `Measure.measurable_of_measurable_coe` で「∀ s, MeasurableSet s →
  Measurable (fun x => RHS s)」に reduce。
* `RHS s = (Measure.pi (fun i => gaussianReal 0 (N i)))
            ((fun y i => x i + y i) ⁻¹' s)`
  (これは `Measure.map_apply` で `(shift x).map = ↦` の preimage に書き直す。
  ただし `(fun y i => x i + y i)` の measurability は `measurable_pi_iff` +
  `(measurable_const.add (measurable_pi_apply i))` で自動。)
* preimage は `Prod.mk x ⁻¹' {p : (Fin n → ℝ) × (Fin n → ℝ) | ...}` 形に
  rewrite (curried シフト → uncurried 加算)。
* `measurable_measure_prodMk_left` で finish (SFinite は IsProbabilityMeasure
  から自動)。

### AWGN F-1 pattern との比較

| AWGN F-1 (`AWGNF1Discharge.lean`) | T2-B L-PG0 (本 plan) |
| --- | --- |
| `gaussianReal x N = (gaussianReal 0 N).map (x + ·)` | `Measure.pi (fun i => gaussianReal (x i) (N i)) = (Measure.pi (fun i => gaussianReal 0 (N i))).map (fun y i => x i + y i)` |
| `gaussianReal_map_const_add` (`Mathlib:292`) | `gaussianReal_map_const_add` + `Measure.pi_map_pi` (`Mathlib:390`) |
| 1-arg `Measure.map` | n-arg `Measure.map ∘ Measure.pi` ↔ `Measure.pi ∘ ...map` |
| `measurable_fst.add measurable_snd` で uncurry | 各 coordinate `(measurable_fst.eval i).add (measurable_snd.eval i)` で uncurry (or `Measurable.add` on `Π i`) |
| `(x + ·) ⁻¹' s = Prod.mk x ⁻¹' {p | p.1+p.2 ∈ s}` | `(fun y i => x i + y i) ⁻¹' s = Prod.mk x ⁻¹' {p | (fun i => p.1 i + p.2 i) ∈ s}` |

→ 構造は完全に並行。`gaussianReal_map_const_add` を `pi_map_pi` で持ち上げる
ところが本 plan の唯一の non-trivial 拡張点。

## Per-file breakdown

新規 `Common2026/Shannon/ParallelGaussianL_PG0Discharge.lean` (~150-250 行):

1. **`gaussianReal_pi_eq_zero_map`** — 上の "核心の観察":
   `Measure.pi (fun i => gaussianReal (x i) (N i)) = (Measure.pi (fun i => gaussianReal 0 (N i))).map (fun y i => x i + y i)`。
   `funext + gaussianReal_map_const_add + Measure.pi_map_pi` ~10 行。
2. **`isParallelGaussianKernelMeasurable`** — L-PG0 述語の discharge:
   `Measure.measurable_of_measurable_coe` + curry uncurry + `measurable_measure_prodMk_left`
   〜 AWGN F-1 と並行で ~60-100 行。`h_meas` 引数 (= `IsParallelAwgnChannelMeasurable N`)
   は使わない (fixed base measure に reduce するので per-coord measurability 不要)。
3. **`parallel_gaussian_capacity_formula_PG0_discharged`** —
   `parallel_gaussian_capacity_formula` の `h_parallel_meas` を上で埋めて再 publish。
4. **`parallel_gaussian_capacity_active_form_PG0_discharged`** —
   `parallel_gaussian_capacity_active_form` の `h_parallel_meas` を埋めて再 publish。

## 撤退ライン (本 plan 内)

* 核心の `pi_map_pi` 適用が hypothesis 要件 (`SigmaFinite ((μ i).map (f i))`,
  `AEMeasurable (f i) (μ i)`) を満たせなければ:
  * shift map の `Measurable` は `measurable_const.add measurable_id` で自動。
  * `(gaussianReal 0 (N i)).map (x i + ·) = gaussianReal (x i) (N i)` は確率測度 →
    sigma-finite。
* それでも詰まれば、`pi_eq` (π-system 上での等価性) を直接使って手書きで
  `Measure.pi (fun i => gaussianReal (x i) (N i)) (Set.univ.pi t)
    = (Measure.pi (fun i => gaussianReal 0 (N i))).map (...) (Set.univ.pi t)`
  を rectangle で示す (~30 行追加)。
* 全ての手段が失敗したら、L-PG0 の partial discharge (例: per-coord
  measurability から `measurable_pi_iff` で **`fun x => (fun i => gaussianReal (x i) (N i))`
  が Π Measure 値関数として measurable** を示し、最後の `Measure.pi` 適用部分は
  外側 hypothesis として残す) で着地。
* Mathlib gap: `MeasureTheory.Measure.pi` の "parameter measurability" lemma
  (= まさに本 plan の目標) は 2026-05 時点 Mathlib 不在。Report に PR 候補
  として明記。

## 制約

* 既存 `ParallelGaussian.lean` の signature 変更禁止 (述語名・引数名・順序保持)。
* `Common2026.lean` / `docs/textbook-roadmap.md` 不変。
* `import Mathlib` 禁止 — 必要な module を pinpoint import。
