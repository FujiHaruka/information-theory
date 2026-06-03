# 最大エントロピー ムーンショット計画 🌙 (B-6)

> 実態整合 (2026-05-20): **DONE-UNCOND — 進捗ブロックの全 [x] が実態と一致 (この plan は正確)**。
> `InformationTheory/Shannon/MaxEntropy.lean` (0 sorry) に Phase A `klDiv_uniformOn_univ_toReal_eq` (:123)、
> Phase B `entropy_le_log_card` (:229)、Phase C `entropy_eq_log_card_iff` (:241) を honest に publish。
> いずれも vacuous/pass-through なし。

<!-- B-6 シード: docs/moonshot-seeds.md より複製・膨らませ -->

## 進捗

- [x] Phase 0 — Mathlib + 既存 InformationTheory API インベントリ ✅
- [x] Phase A — KL identity `klDiv P (uniformOn univ) = log |α| - entropy μ X` ✅
- [x] Phase B — 主定理 `entropy μ X ≤ log |α|` (Gibbs 帰結) ✅
- [x] Phase C — 等号条件 `entropy μ X = log |α| ↔ μ.map X = uniformOn univ` ✅

## ゴール / Approach

**ゴール**: 有限アルファベット `α` 上で `entropy μ X ≤ Real.log (Fintype.card α)` を Lean 化、等号は `μ.map X = uniformOn Set.univ`。Pinsker / Sanov の前段補題、LoomisWhitney の `entropy_le_log_image_card` の一般 measure 版。

**Approach**: 既存 `klDiv` 上に薄い 3 段で乗せる。

1. **identity** (Phase A): `(klDiv (μ.map X) (uniformOn univ)).toReal = log |α| - entropy μ X`。
   - `P := μ.map X` は有限 Fintype 上の確率測度、`U := uniformOn univ` も確率測度、`U {x} = 1/|α| > 0` なので `P ≪ U` が automatic。
   - `toReal_klDiv_of_measure_eq` (Mathlib) で `(klDiv P U).toReal = ∫ x, llr P U x ∂P`。
   - `llr P U x = log (P.rnDeriv U x).toReal` で、`withDensity_rnDeriv_eq` + `lintegral_singleton` から
     `(P.rnDeriv U x).toReal * U.real {x} = P.real {x}` ⟹ `(P.rnDeriv U x).toReal = N * P.real {x}` (where `N := |α|`)。
   - よって `llr P U x = log N + log P.real {x}` (各 `x` で `P.real {x} > 0` のとき; `P{x}=0` のときは Bochner の積分で `negMulLog` で潰せる)。
   - Bochner `integral_fintype` で `∫ x, (log N + log P{x}) ∂P = log N · 1 + ∑ x, P{x} · log P{x} = log N - entropy μ X`。
2. **主定理** (Phase B): `klDiv P U ≥ 0` (ENNReal なので automatic) + identity ⟹ `log N - entropy μ X ≥ 0`。
3. **等号** (Phase C): `entropy μ X = log N ↔ klDiv P U = 0 ↔ P = U` (`klDiv_eq_zero_iff`)。

`klDiv_discrete_toReal_eq_sum` (Bridge.lean) は `private` なのでそのままは使えないが、本シードでは `Q = uniformOn` 特化形なのでわざわざ呼ばずに上記直接ルートが最短。

## Phase 0 - Inventory ✅

### Mathlib

- `InformationTheory.klDiv (μ ν : Measure α) : ℝ≥0∞` — Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57
- `InformationTheory.toReal_klDiv_of_measure_eq` (`Mathlib.../KullbackLeibler/Basic.lean:164`):
  signature: `{α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ ≪ ν) (h_eq : μ univ = ν univ) : (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ`
- `InformationTheory.klDiv_eq_zero_iff` (`.../KullbackLeibler/Basic.lean:377`):
  `{α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] : klDiv μ ν = 0 ↔ μ = ν`
- `ProbabilityTheory.llr (μ ν : Measure α) (x : α) : ℝ := Real.log (μ.rnDeriv ν x).toReal` — log-likelihood ratio
- `MeasureTheory.Measure.withDensity_rnDeriv_eq` — `ν.withDensity (μ.rnDeriv ν) = μ` when `μ ≪ ν`
- `MeasureTheory.withDensity_apply` + `MeasureTheory.lintegral_singleton`
- `ProbabilityTheory.uniformOn` — `Mathlib/Probability/UniformOn.lean:60`
- `ProbabilityTheory.uniformOn_apply_finset` — `{Ω} [DecidableEq Ω] [MeasurableSingletonClass Ω] {s t : Finset Ω} : uniformOn (s : Set Ω) (t : Set Ω) = #(s ∩ t) / #s`
- `ProbabilityTheory.instIsProbabilityMeasure_uniformOn_univ : [Finite Ω] [Nonempty Ω] → IsProbabilityMeasure (uniformOn univ)`
- `MeasureTheory.integral_fintype`, `MeasureTheory.integral_add`
- `Real.log_mul`, `Real.negMulLog`

### InformationTheory 既存

- `InformationTheory/Shannon/Bridge.lean:43` — `noncomputable def entropy (μ : Measure Ω) (Xs : Ω → X) : ℝ := ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})`
- `InformationTheory/Shannon/Bridge.lean:47` — `entropy_nonneg`
- `InformationTheory/Shannon/Bridge.lean:216` — `private klDiv_discrete_toReal_eq_sum` (参考、本シードでは inline で別ルート)
- `InformationTheory/Shannon/LoomisWhitney.lean` — `entropy_uniformOn_eq_log_card` (uniformOn-specific 形)、本シードの汎用版で代替可能だが既存依存があるので併存

## Phase A - KL identity 📋

シグネチャ:
```
theorem klDiv_uniformOn_univ_toReal_eq
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (hX : Measurable X) :
    (klDiv (μ.map X) (uniformOn (Set.univ : Set α))).toReal
      = Real.log (Fintype.card α) - entropy μ X
```

ステップ:
- [ ] `P := μ.map X`、`U := uniformOn univ` を導入、各々 `IsProbabilityMeasure` を発火
- [ ] `P ≪ U`: 任意 `A` で `U A = 0 ⟹ A = ∅`、よって `P A = 0` (各 singleton mass `1/N`)
- [ ] `toReal_klDiv_of_measure_eq hPU h_univ`
- [ ] `llr P U x = log N + log (P.real {x})` 補題 — `(P.rnDeriv U x).toReal = N * P.real {x}` 経由
- [ ] `∫ x, llr P U x ∂P = log N - entropy μ X` — `integral_fintype` + Fintype 和の分配

## Phase B - 主定理 📋

シグネチャ:
```
theorem entropy_le_log_card
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (hX : Measurable X) :
    entropy μ X ≤ Real.log (Fintype.card α)
```

`klDiv P U ≥ 0` (ENNReal `bot_le`) + `.toReal ≥ 0` + identity ⟹ `log N - entropy ≥ 0`。

## Phase C - 等号条件 📋

シグネチャ:
```
theorem entropy_eq_log_card_iff
    ... :
    entropy μ X = Real.log (Fintype.card α)
      ↔ μ.map X = uniformOn (Set.univ : Set α)
```

`klDiv_eq_zero_iff` + identity の両方向。`(klDiv P U).toReal = 0 ↔ klDiv P U = 0` には finiteness が必要 (`klDiv P U < ⊤` を identity の存在から確保)。

## 判断ログ

書き出し時 (2026-05-11): なし。実装中に何か pivot したらここに append。
