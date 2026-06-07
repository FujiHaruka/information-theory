# EPI 無条件化 W-Y1 crux ② (EReal chain rule) — Mathlib + in-tree API 在庫

> **対象**: EPI 無条件化 方針 Y W-Y1 の crux ② = `differentialEntropyExt_eq_condEntExt_add_klDiv`
> (`InformationTheory/Shannon/EPIUncondCondEntropyExt.lean:191`、file 内唯一の sorry)。
> **親計画**: [`epi-uncond-deffix-monotone-plan.md`](epi-uncond-deffix-monotone-plan.md) §7-6 (道 A self-build) / §7-7。
> **本ファイルは在庫調査のみ** (実装・計画起草・判定なし)。§7-4 判断点 (`plan:` 据置 vs `wall:` 昇格) の独立材料。

## 一行サマリ

**② の self-build に要る API は配線材料 (Mathlib + in-tree) がほぼ揃う「known-shape self-build」。真の Mathlib 不在は 1 種だけ — 「条件付き KL = fibrewise lintegral 平均」の ℝ≥0∞ 版** (Mathlib `ChainRule.lean:74-77` の TODO、loogle conclusion-shape 二段で Found 0)。ただし in-tree `klDiv_compProd_const_toReal_integral` (`.toReal` 形、`@audit:ok`) が**同じ gap を埋めた既存資産**として在り、その `.toReal` を外した ℝ≥0∞ 版は self-build template が明確 (~30-50 行、`klDiv_eq_lintegral_klFun_of_ac` + `lintegral_compProd` の Tonelli)。**残り 3 step (per-fibre entropy↔KL の符号 lift / marginal collapse / EReal 算術) は配線中心**。よって ② は **真の Mathlib 壁を含まない self-build (multi-session 規模だが path 可視)** という独立評価 (詳細 → 総括)。**最危険発見**: 道 A の入口 `klDiv_eq_lintegral_klFun_of_ac` / in-tree `klDiv_compProd_*` 群が全て `[IsFiniteMeasure]` + `[IsMarkovKernel]` + `[MeasurableSpace.CountableOrCountablyGenerated 𝓧 𝓨]` を要求 — 最後の hidden type-class が ② の signature (現在 `α` に何の制約もなし) に leak しうる。

---

## ⚠ 戦略更新 (2026-06-07、step a' 着地 + pivot-advisor 独立検証後) — **本セクションが現行 SoT**

> 以下は step a' 着地 (`CondKLIntegral.lean:144`、commit `bb852da`、sorryAx-free) と proof-pivot-advisor 独立検証を経た方針修正。**下記「API 在庫テーブル」の step b'/c' 設計 (A/B/cross 別 lintegral 分配) は赤フラグと判明したので、本セクションが優先する**。

- **step a' 状態 = ✅ 着地済** (`klDiv_compProd_lintegral`、`CondKLIntegral.lean:144`、ℝ≥0∞・無 integrability・sorryAx-free)。在庫テーブル項目1 / 自作要素1 の「未着地」記述は drift (本セクションが訂正)。

- **❌ 棄却ルート (案 B')**: per-step で `klDiv(κz)(ν)` を A(κz)/B(κz)/Cpos/Cneg の **別々 lintegral に分配** する設計 (下記 項目2 「符号付き分解」の素朴解釈)。`ENNReal.ofReal(a+b) ≠ ofReal a + ofReal b` で pointwise 恒等式にならず、`klDiv` の integrand `ofReal(p log p − p log q + q − p)` (= 単一非負 `ofReal(q·klFun(p/q))`) は A/B/cross に割れない。`.toReal` 版がミラーできたのは Real 域で減算自由だからで、**負号/減算を含む step では ℝ≥0∞ ミラーは機械的に成り立たない** (advisor 教訓)。

- **✅ 採用ルート (案 A' = 単一量 all-nonneg ℝ≥0∞ 恒等式)**:
  1. **assemble の核**: ② を EReal 差の比較でなく **all-nonneg ℝ≥0∞ 恒等式 (★)** に落とす:
     `A(ν) + ∫⁻z B(κz) = ∫⁻z A(κz) + B(ν) + ∫⁻z klDiv(κz)(ν)` (全項 coe-from-ℝ≥0∞、減算なし)。
     これを EReal 補題 `(U−V = a−b) ⟸ (U+b = a+V)` (⊤ 場合分けは `hcond_ne_bot` scope) で目標 EReal 差形へ。`klDiv` は **単一非負量のまま** (分配しない)。
  2. **step c' (marginal collapse) = clean・finiteness-free** (私の追加分析、確信度高): cross 項 `ofReal(pz·log qν)` は **`pz` に線型** (`log qν(x)` の符号は z 非依存) ⇒ `ofReal(pz·c) = pz·c⁺` で `ofReal` が z-Tonelli を通過。marginal collapse `∫⁻z pz ∂μZ = qν` で `∫⁻z Cpos_z = B(ν)`、`∫⁻z Cneg_z = A(ν)`。元 `integral_condDistrib_marginal_eq` (`:150`) の lintegral ミラーで取れる。
  3. **step b' (per-fibre ☆) = 真のボトルネック・finiteness-free 性が不確実**:
     `∫⁻z [A(κz) + klDiv(κz)(ν) + Cpos_z] = ∫⁻z [Cneg_z + B(κz)]` を per-fibre 恒等式
     `A(κz) + klDiv(κz)(ν) + Cpos_z = Cneg_z + B(κz)` (☆) に落とす。**(☆) は pointwise 恒等式でない** — `+q−p` mass 項 (∫=0 だが pointwise≠0) が pointwise 等式を壊し、signed llr は ℝ≥0∞ に直接入らない。`.toReal` 版は `toReal_klDiv_of_measure_eq hPQ hmass` が mass 項を吸収するが、ℝ≥0∞ には対応物がない (`∫⁻ ofReal(llr) ≥ klDiv`、符号で不等)。**finiteness-free が成立するか、per-fibre 有限性 (fibre 微分エントロピー有限) regularity hyp が必要かは実機械検証で裏取り** (advisor=不要派、本調査追加分析=補強の可能性あり、判定分岐)。

- **撤退ライン**: step b' で finiteness-free が崩れ、honest な regularity 補強 (fibre 有限エントロピー) でも closure できない / 2-3 session 詰まれば §7-4 で `wall:` 昇格 + headline を `entropy_power_inequality_of_ac` (proof-done) に確定 (L-Uncond-Y-roi)。**case-split-to-Real-bridge (案 C') は選ばない** (advisor: 最悪コスト)。**signature 補強が genuine regularity でかつ EPI consumer (`differentialEntropyExt_indep_add_eq_add_klDiv`、`EPIUncondMonotone.lean:80`、fibre = `μ.map W` 有限エントロピー) で供給可能なら、補強は撤退でなく honest closure** (load-bearing でない)。

---

## 主定理の最終形 (crux ②、再掲)

`InformationTheory/Shannon/EPIUncondCondEntropyExt.lean:191-200` verbatim:

```lean
theorem differentialEntropyExt_eq_condEntExt_add_klDiv
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) (hX_ac : (μ.map X) ≪ volume)
    (hcond_ne_bot : condDifferentialEntropyExt X Z μ ≠ ⊥) :
    differentialEntropyExt (μ.map X)
      = condDifferentialEntropyExt X Z μ
        + (((InformationTheory.klDiv ((μ.map Z) ⊗ₘ condDistrib X Z μ)
              ((μ.map Z) ⊗ₘ Kernel.const α (μ.map X))) : ℝ≥0∞) : EReal) := by
  sorry
```

定義 (`EPIUncondCondEntropyExt.lean:52-58`):
- `condDifferentialEntropyExt X Z μ = ((∫⁻ z, A(κz) ∂μZ : ℝ≥0∞) : EReal) − ((∫⁻ z, B(κz) ∂μZ : ℝ≥0∞) : EReal)`、
  `κ = condDistrib X Z μ`、`μZ = μ.map Z`、`A(ν) := ∫⁻ x, ofReal(negMulLog (rnDeriv ν vol x).toReal) ∂vol`、`B(ν) := ∫⁻ x, ofReal(−(negMulLog ...))`。
- `differentialEntropyExt μ = (A(μ):EReal) − (B(μ):EReal)` (a.c. 枝、`EntropyPowerExt.lean:56` `differentialEntropyExt_of_ac`)。

証明戦略 (pseudo-Lean、道 A = Real bridge `differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv` の sum 形・finiteness-free 持ち上げ):

```
-- 元 Real bridge (差分形, 8 integrability): h(X) − h(X|Z) = (klDiv joint product).toReal
-- ② = sum 形 (⊤−⊤ 回避) + ℝ≥0∞/lintegral 持ち上げ (8 integrability 全落とし)
-- step (a'): klDiv joint product (ℝ≥0∞) = ∫⁻ z, klDiv (κz) ν ∂μZ        -- ★ self-build (ℝ≥0∞ 版 fibrewise)
-- step (b'): per-fibre  klDiv (κz) ν (ℝ≥0∞) を A(κz)/B(κz) + cross の符号付き形に           -- ★ self-build (符号)
-- step (c'): ∫⁻z cross_z = ∫⁻ qX log qX = B(ν)−... (marginal collapse, Tonelli)            -- ★ self-build
-- assemble: A(ν) − B(ν)  =  (∫⁻z A(κz) − ∫⁻z B(κz))  +  klDiv             -- EReal 算術 (sum 形)
--   ⊤ 項 (klDiv=⊤ or A=⊤) は EReal `add_top_of_ne_bot` で吸収 (hcond_ne_bot が ⊥ 枝を除外)
```

---

## API 在庫テーブル

凡例 (gap 判定): ① = Mathlib/in-tree に在る (配線のみ) / ② = 自作要 (見積行数 + template lemma 1 本) / ③ = 真の壁疑い。

### 項目1: finiteness-free fibrewise 条件付き KL 分解 (step a')

目標: `klDiv ((μZ) ⊗ₘ κ) ((μZ) ⊗ₘ Kernel.const α ν) = ∫⁻ z, klDiv (κ z) ν ∂μZ` (ℝ≥0∞ 値、無 `.toReal`、無 integrability)。

| 概念 | API | file:line | signature ([..] verbatim) / conclusion | 状態 |
|---|---|---|---|---|
| KL chain rule (無仮定 compProd 形) | `InformationTheory.klDiv_compProd_eq_add` | `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:204` | section vars `[IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η]` (`:90`)。**concl**: `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` | ✅ 既存 (ℝ≥0∞) |
| KL compProd-left simp | `InformationTheory.klDiv_compProd_left` | `…/ChainRule.lean:182` | 同 section vars。**concl**: `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν` | ✅ 既存 |
| **fibrewise lintegral 平均形 (ℝ≥0∞)** | — | — | `klDiv (μ⊗κ)(μ⊗η) = ∫⁻ z, klDiv (κ z)(η z) ∂μ` の **ℝ≥0∞ 版** | ❌ **Mathlib 不在** (ChainRule.lean:74-77 の TODO、本項末 gap 参照) |
| in-tree `.toReal` 版 fibrewise (★同 gap 既埋) | `InformationTheory.klDiv_compProd_toReal_integral` | `InformationTheory/Shannon/CondKLIntegral.lean:108` | section vars `[IsFiniteMeasure μ] [IsMarkovKernel κ] [IsMarkovKernel η] [MeasurableSpace.CountableOrCountablyGenerated 𝓧 𝓨]` (`:95-96`)。args: `(h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) (h_int : Integrable (llr (μ ⊗ₘ κ) (μ ⊗ₘ η)) (μ ⊗ₘ κ))`。**concl**: `(klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal = ∫ z, (klDiv (κ z) (η z)).toReal ∂μ` | ✅ 既存 (`@audit:ok`、`.toReal` 形・要 integrability) |
| in-tree const-kernel 特化 (`.toReal`) | `InformationTheory.klDiv_compProd_const_toReal_integral` | `CondKLIntegral.lean:146` | + `{ν : Measure 𝓨} [IsProbabilityMeasure ν]`。args: `(h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ (Kernel.const 𝓧 ν)) (h_int : …)`。**concl**: `(klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (Kernel.const 𝓧 ν))).toReal = ∫ z, (klDiv (κ z) ν).toReal ∂μ` | ✅ 既存 (`@audit:ok`、② が消費する step a の `.toReal` 元) |
| ℝ≥0∞ 値 KL ↔ lintegral (per-measure) | `InformationTheory.klDiv_eq_lintegral_klFun_of_ac` | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:138` | section vars `[IsFiniteMeasure μ] [IsFiniteMeasure ν]` (`:108`/`:146`)。args: `(h_ac : μ ≪ ν)`。**concl**: `klDiv μ ν = ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν` | ✅ 既存 (ℝ≥0∞、★ self-build の入口) |
| Tonelli (compProd の lintegral、無仮定で交換) | `MeasureTheory.Measure.lintegral_compProd` | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:183` | `[SFinite μ] [IsSFiniteKernel κ]`、`{f : α × β → ℝ≥0∞} (hf : Measurable f)`。**concl**: `∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂(κ a) ∂μ` | ✅ 既存 (ℝ≥0∞ Tonelli は無 integrability) |
| `klFun` 定義 | `InformationTheory.klFun` | `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean:53` | `noncomputable def klFun (x : ℝ) : ℝ := x * log x + 1 - x` | ✅ 既存 |
| `condDistrib` の `IsMarkovKernel` instance | `ProbabilityTheory.instIsMarkovKernelCondDistrib` | `Mathlib/Probability/Kernel/CondDistrib.lean` | (loogle 確認) `condDistrib` は Markov kernel | ✅ 既存 (compProd 系の `[IsMarkovKernel κ]` を満たす) |

**gap 判定 (項目1)**: **② 自作要 (ℝ≥0∞ 版 fibrewise)**。
- loogle conclusion-shape 二段 (反証試行): bare-identifier `InformationTheory.klDiv, MeasureTheory.lintegral` → 2 件のみ (`klDiv_eq_lintegral_klFun(_of_ac)`、per-measure)。compProd 同梱の `InformationTheory.klDiv, Measure.compProd, MeasureTheory.lintegral` → **Found 0**。conclusion-shape `klDiv (compProd _ _) _ = lintegral _ _` → **Found 0**。同 integral 形 → **Found 0**。`condDistrib, klDiv` → **Found 0**。⇒ Mathlib に fibrewise lintegral/integral 形の条件付き KL は不在 (ChainRule.lean:74-77 が「Add a version of the chain rule for the integral form … `μ[fun x ↦ klDiv (κ x) (η x)]`」と TODO 明記)。
- **template lemma が書ける** (壁判定保留の根拠): in-tree `klDiv_compProd_toReal_integral` (`CondKLIntegral.lean:108`) は **この gap を `.toReal` 形で既に埋めた genuine 資産**。本体は `toReal_klDiv_eq_integral_klFun` (joint) + `Measure.integral_compProd` (Fubini) + per-fibre slice の組み合わせ (line 126-138)。ℝ≥0∞ 版は `toReal_klDiv_eq_integral_klFun` を `klDiv_eq_lintegral_klFun_of_ac` (Basic.lean:138) に、`Measure.integral_compProd` を `Measure.lintegral_compProd` (Tonelli、無 integrability) に差し替えるミラー。ℝ≥0∞ では Tonelli が無条件なので **8 integrability の大半が落ちる**。⇒ **~30-50 行の known-shape self-build** (壁でない)。型クラス `[MeasurableSpace.CountableOrCountablyGenerated 𝓧 𝓨]` は `slice identity` (CondKLIntegral.lean:59) 由来で ℝ≥0∞ 版でも継承する見込み (下記「主要前提条件ボックス」)。

### 項目2: per-fibre entropy↔KL 関係の ℝ≥0∞/EReal 形 (step b')

目標: `klDiv (κz) ν` (ℝ≥0∞) を A(κz)/B(κz) (lintegral) + cross-entropy lintegral で表す符号付き finiteness-free 形。

| 概念 | API | file:line | signature ([..] verbatim) / conclusion | 状態 |
|---|---|---|---|---|
| in-tree per-fibre (`.toReal` 形、★元) | `klDiv_toReal_eq_neg_differentialEntropy_sub_cross` | `EPIG2BridgeDensityHelpers.lean:97` | args: `(P Q : Measure ℝ) [IsFiniteMeasure P] [IsFiniteMeasure Q] (hPv : P ≪ volume) (hQv : Q ≪ volume) (hPQ : P ≪ Q) (hmass : P univ = Q univ) (h_logp_int : Integrable (fun x => (P.rnDeriv volume x).toReal * Real.log ((P.rnDeriv volume x).toReal)) volume) (h_cross_int : Integrable (fun x => (P.rnDeriv volume x).toReal * Real.log ((Q.rnDeriv volume x).toReal)) volume)`。**concl**: `(klDiv P Q).toReal = - differentialEntropy P - ∫ x, (P.rnDeriv volume x).toReal * Real.log ((Q.rnDeriv volume x).toReal) ∂volume` | ✅ 既存 (`@audit:ok`、`.toReal` 形・2 integrability) |
| KL ↔ klFun integral (per-measure、有限版) | `klDiv_eq_lintegral_klFun_of_ac` | `Basic.lean:138` | (上掲、項目1) | ✅ 既存 |
| `Real.negMulLog` (= −x log x) | `Real.negMulLog` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:164` | `def negMulLog (x : ℝ) : ℝ := -x * log x` (定義は plan で利用済) | ✅ 既存 (A/B integrand) |
| **klFun ↔ negMulLog + cross の ℝ≥0∞/EReal 符号付き分解** | — | — | `klFun(r) = r·log r − r + 1`。fibre 値の ℝ≥0∞ lift で `−r+1` 項を mass 相殺し A/B/cross に分ける形 | ❌ 不在 (自作、符号 delicate) |
| EReal 差非負 / coe 比較 | `EReal.sub_nonneg` | `Mathlib/Data/EReal/Operations.lean:373` | `{x y : EReal} (h_top : x ≠ ⊤ ∨ y ≠ ⊤) (h_bot : x ≠ ⊥ ∨ y ≠ ⊥)`。**concl**: `0 ≤ x - y ↔ y ≤ x` | ✅ 既存 (符号処理用) |

**gap 判定 (項目2)**: **② 自作要 (符号 lift)**。
- 元 `klDiv_toReal_eq_neg_differentialEntropy_sub_cross` (`@audit:ok`) は **probability measure 両者で `hmass : P univ = Q univ` を `measure_univ` 等で discharge 済** (consumer `EPIG2ConvEntropyMonotone.lean:174-175`)。klFun の `−t+1` 項は `klFun(t) = t·log t + 1 − t`、両 prob measure (両 univ = 1) で `∫(1−t) dν` 部分が mass 相殺 → `t·log t` (= `−negMulLog`) のみ残る。これが ℝ≥0∞/EReal 化での「`−t+1` 項が消える」機構。
- **符号の壁の精査**: `klDiv (κz) ν ≥ 0` (ℝ≥0∞、type-trivial) だが、A(κz)/B(κz) は EReal 差 `(A:EReal)−(B:EReal)` で `−h(κz)` は符号自由。よって per-fibre 等式は **EReal 差で受ける**必要があり、`⊤` を含む算術 (`add_top_of_ne_bot` 等、項目4) で受ける。`hcond_ne_bot` が ⊥ fibre を除外する scope。
- template: 元 `.toReal` 版 (line 108-129) の `toReal_klDiv_of_measure_eq` + `llr_eq_log_density_sub_log_density` + `integral_toReal_rnDeriv_mul` を、それぞれ ℝ≥0∞/lintegral の対応物に差し替え。**~40-80 行**、符号場合分け (A 発散 / B 発散) を加味。**known-shape self-build (壁でない)**。

### 項目3: marginal collapse の lift (step c')

目標: `∫⁻z (∫⁻x pz·log qν) ∂μZ = ∫⁻x qν·log qν` (Fubini marginal) の lintegral/ℝ≥0∞ 版。

| 概念 | API | file:line | signature ([..] verbatim) / conclusion | 状態 |
|---|---|---|---|---|
| in-tree density-form marginal (`∫`, ★元) | `integral_condDistrib_density_marginal_eq` | `EPIG2BridgeDensityHelpers.lean:198` | args: `{Ω α} [MeasurableSpace Ω] [MeasurableSpace α] (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (hZ : Measurable Z) (hX_ac : (μ.map X) ≪ volume) (hκ_ac : ∀ᵐ z ∂(μ.map Z), condDistrib X Z μ z ≪ volume) (h_logq_int : Integrable (fun x => Real.log (((μ.map X).rnDeriv volume x).toReal)) (μ.map X))`。**concl**: `∫ z, (∫ x, ((condDistrib X Z μ z).rnDeriv volume x).toReal * Real.log (((μ.map X).rnDeriv volume x).toReal) ∂volume) ∂(μ.map Z) = ∫ x, ((μ.map X).rnDeriv volume x).toReal * Real.log (((μ.map X).rnDeriv volume x).toReal) ∂volume` | ✅ 既存 (`@audit:ok`、`∫`・3 integrability) |
| in-tree marginal core (`∫`、汎用) | `integral_condDistrib_marginal_eq` | `EPIG2BridgeDensityHelpers.lean:150` | args: 同上 + `{g : ℝ → ℝ} (hg_int : Integrable g (μ.map X))`。**concl**: `∫ z, (∫ x, g x ∂(condDistrib X Z μ z)) ∂(μ.map Z) = ∫ x, g x ∂(μ.map X)` | ✅ 既存 (`@audit:ok`、Fubini core) |
| compProd ↔ condDistrib joint 同定 | `ProbabilityTheory.compProd_map_condDistrib` | `Mathlib/Probability/Kernel/CondDistrib.lean` (in-tree consumer `BridgeDensityHelpers:157`) | **concl**: `(μ.map Z) ⊗ₘ condDistrib X Z μ = μ.map (fun ω => (Z ω, X ω))` | ✅ 既存 |
| Tonelli (compProd lintegral) | `MeasureTheory.Measure.lintegral_compProd` | `MeasureCompProd.lean:183` | (上掲、項目1) | ✅ 既存 (ℝ≥0∞ 無 integrability) |
| lintegral_map (marginal 射影) | `MeasureTheory.lintegral_map` | `Mathlib/MeasureTheory/Integral/Lebesgue/Basic` 系 | (in-tree `∫` 版は `integral_map` 使用、ℝ≥0∞ は `lintegral_map`) | ✅ 既存 |

**gap 判定 (項目3)**: **② 自作要 (ℝ≥0∞ ミラー)**。
- 元 `integral_condDistrib_marginal_eq` (`@audit:ok`) は `compProd_map_condDistrib` + `Measure.integral_compProd` (Fubini) + `integral_map` の組み (line 156-178)。ℝ≥0∞ 版は `Measure.integral_compProd` → `Measure.lintegral_compProd` (Tonelli、無 integrability)、`integral_map` → `lintegral_map` のミラー。**Tonelli が無 integrability なので `hg_int` (Integrable g (μ.map X)) が落ちる**のが ℝ≥0∞ 化の利得。ただし `(rnDeriv κz · log qν)` の符号が混在するので、`negMulLog` 正部・負部分離 (A/B) で各々を非負 lintegral として扱う設計が要る (signed log は ℝ≥0∞ に直接入らない)。
- template: 元 (line 150-178) の `∫`→`∫⁻` ミラー + 正部/負部分離。**~30-60 行、known-shape self-build (壁でない)**。`integral_toReal_rnDeriv_mul` (per-fibre 密度展開、line 217) の lintegral 対応物が要 (`lintegral_withDensity` / `setLIntegral` 系、要 verbatim 確認、本調査未踏)。

### 項目4: EReal/ℝ≥0∞ 算術の在庫 (sum 形 assemble + ⊤ 処理)

| 概念 | API | file:line | signature ([..] verbatim) / conclusion | 状態 |
|---|---|---|---|---|
| `⊤ + x = ⊤` (x≠⊥) | `EReal.top_add_of_ne_bot` | `Mathlib/Data/EReal/Operations.lean:74` | `{x : EReal} (h : x ≠ ⊥)`。**concl**: `⊤ + x = ⊤` | ✅ 既存 |
| `x + ⊤ = ⊤` (x≠⊥) | `EReal.add_top_of_ne_bot` | `…/Operations.lean:94` | `{x : EReal} (h : x ≠ ⊥)`。**concl**: `x + ⊤ = ⊤` | ✅ 既存 |
| ℝ≥0∞→EReal coe 加法準同型 | `EReal.coe_ennreal_add` | `Mathlib/Data/EReal/Basic.lean:670` | `(x y : ENNReal)`。**concl**: `((x + y : ℝ≥0∞) : EReal) = x + y` | ✅ 既存 |
| ℝ≥0∞→EReal coe `⊤` | `EReal.coe_ennreal_top` | `…/Basic.lean:594` | **concl**: `((⊤ : ℝ≥0∞) : EReal) = ⊤` | ✅ 既存 |
| ℝ≥0∞→EReal coe 比較 | `EReal.coe_ennreal_le_coe_ennreal_iff` | `…/Basic.lean:613` | `{x y : ℝ≥0∞}`。**concl**: `(x : EReal) ≤ (y : EReal) ↔ x ≤ y` | ✅ 既存 |
| ℝ≥0∞.toReal → EReal coe (有限時) | `EReal.coe_ennreal_toReal` | `…/Basic.lean:578` | `{x : ℝ≥0∞} (hx : x ≠ ∞)`。**concl**: `(x.toReal : EReal) = x` | ✅ 既存 (bridge 枝で利用) |
| EReal 差非負 ↔ ≤ | `EReal.sub_nonneg` | `…/Operations.lean:373` | (上掲、項目2) | ✅ 既存 |
| EReal mono `a ≤ a + (i:EReal)` (i≥0) | `add_le_add_right` (一般 OrderedAddCommMonoid) | (gateway atom 利用済、`EPIUncondMonotone.lean:61`) | consumer は `add_le_add_right hi _` で `bot_le` (ℝ≥0∞→EReal coe) を渡す。GREEN (probe §7-6 で 0 sorry) | ✅ 既存 (consumer 側で genuine 着地済) |

**gap 判定 (項目4)**: **① Mathlib 既存 (配線のみ)**。EReal sum 形 (`⊤−⊤` 回避) の assemble に要る ⊤-吸収・coe 準同型は全て Mathlib 完備。② が `condEntExt + klDiv` の sum 形を選んだのは正にこの在庫を使うため (差分 `differentialEntropyExt` 自体は `A−B` の EReal 差だが、② の RHS は `condEntExt(=∫A−∫B) + klDiv(≥0)` の sum で `⊤+klDiv=⊤` を `add_top_of_ne_bot` で吸収できる)。**gateway atom の GREEN 算術 (add_le_add_right) は既に genuine 着地済 (consumer 側)**。

### 項目5 (acyclic 確認): conditioning 単調性の依存方向メモ

> **判定はしない (在庫の依存方向メモのみ)**。監査 気づき: ② closure で conditioning 単調 `h(X|Z) ≤ h(X)` の EReal 版を使うと `hcond_ne_bot` 経由で循環しうる。

| lemma | file:line | ② への依存方向 | メモ |
|---|---|---|---|
| Real `condDifferentialEntropy_le` (h(X\|Z)≤h(X)) | `EPIG2ConvEntropyMonotone.lean:224` | **②に依存** (本体が `differentialEntropy_sub_…_eq_toReal_klDiv` を呼び `sub_nonneg`) | この Real 版は **bridge (= ② の Real 対応物 `:124`) の系**。EReal 版を作って ② 証明に使うと循環 |
| Real bridge `differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv` | `EPIG2ConvEntropyMonotone.lean:124` | ② の **Real 対応物** (= ② が EReal 持ち上げする元) | ② はこれを持ち上げる。`condDifferentialEntropy_le` はこれの consumer なので、② が単調性に依存すると逆向き |
| ② が単調性に依存せず組めるか | — | **依存不要 (組める見込み)** | ② = entropy 分解恒等式 (`h(X)=h(X\|Z)+I`)。step a'/b'/c' は KL chain rule + 符号 lift + marginal collapse で構成され、conditioning 単調性 (`h(X\|Z)≤h(X)`) を**使わない** (元 Real bridge `:124` 本体が `condDifferentialEntropy_le` を呼んでいない、line 153-209 で確認 — bridge は単調性に非依存、単調性が bridge に依存)。よって ② も単調性非依存で acyclic に組める |

**依存方向の結論 (メモ)**: 元 Real bridge (`:124`) は `condDifferentialEntropy_le` (`:224`) に**依存していない** (逆: 単調性が bridge に依存)。⇒ ② を bridge の EReal ミラーとして組めば、conditioning 単調性に依存せず acyclic。② 証明内で `h(X|Z)≤h(X)` を使う誘惑 (sufficiency の枝処理) が出たら、それは `hcond_ne_bot` の honest scope で代替する (audit docstring `:178-180` の枝処理がこの代替を既に記述)。**判定は orchestrator/planner**。

---

## 主要前提条件ボックス (前提事故が起きやすい lemma)

- **`klDiv_compProd_toReal_integral` / `_const_…` (項目1、step a の `.toReal` 元 & ℝ≥0∞ self-build の参照)**:
  `[IsFiniteMeasure μ] [IsMarkovKernel κ] [IsMarkovKernel η] [MeasurableSpace.CountableOrCountablyGenerated 𝓧 𝓨]` (`CondKLIntegral.lean:95-96`)。**`CountableOrCountablyGenerated 𝓧 𝓨` が hidden type-class**。② の設定では `𝓧 = α` (= Z の codomain)、`𝓨 = ℝ` (= X の codomain)。`ℝ` は countably generated (Borel)、`α` 側は ② が `[MeasurableSpace α]` のみで制約なし → **`CountableOrCountablyGenerated α ℝ` が ② の signature に leak する可能性大** (現 ② は `α` に何も課していない)。`condDistrib` の `IsMarkovKernel` instance (`instIsMarkovKernelCondDistrib`) は自動発火するが、`CountableOrCountablyGenerated` は別途要確認 (Z の codomain `α` が standardBorel / countablyGenerated なら充足、`ℝ` 片側でも `countableOrCountablyGenerated_left_of_prod_left_of_nonempty` 系の派生 instance あり、要 verbatim 確認)。
- **`klDiv_eq_lintegral_klFun_of_ac` (項目1、ℝ≥0∞ self-build の入口)**:
  section vars `[IsFiniteMeasure μ] [IsFiniteMeasure ν]` (`Basic.lean:108`/`:146`、`AlternativeFormulas` + `Real` セクション)。fibre `κz` / marginal `ν=μ.map X` は probability measure なので有限性は充足。`(h_ac : μ ≪ ν)` の絶対連続は ② の `hX_ac` + fibre a.c. (`hκ_ac` 相当) で供給。
- **`lintegral_compProd` (項目1/3、Tonelli)**:
  `[SFinite μ] [IsSFiniteKernel κ]` + `(hf : Measurable f)`。**ℝ≥0∞ Tonelli は integrability 不要** — これが 8 integrability の大半を落とせる核心。measurability (`hf`) のみ要 (negMulLog ∘ rnDeriv は可測)。
- **`klDiv_toReal_eq_neg_differentialEntropy_sub_cross` (項目2、step b の `.toReal` 元)**:
  `[IsFiniteMeasure P] [IsFiniteMeasure Q]` + 5 regularity (`hPv`/`hQv`/`hPQ`/`hmass`/2 integrability)。`hmass : P univ = Q univ` は両 prob measure で `measure_univ` discharge (consumer `:174`)。ℝ≥0∞ 版では 2 integrability を Tonelli/lintegral well-definedness で落とせる見込み (符号分離が条件)。
- **`integral_condDistrib_density_marginal_eq` (項目3、step c の `.toReal` 元)**:
  `[IsProbabilityMeasure μ]` + `hX`/`hZ`/`hX_ac`/`hκ_ac`/`h_logq_int`。ℝ≥0∞ 版では `h_logq_int` (Integrable log qX) が Tonelli で落ちる見込み (正部/負部分離が条件)。

---

## 自作が必要な要素 (優先度順)

1. **step a' = ℝ≥0∞ 版 fibrewise 条件付き KL** `klDiv_compProd_lintegral` (仮称)。
   - **推奨実装**: in-tree `klDiv_compProd_toReal_integral` (`CondKLIntegral.lean:108`) の `.toReal` を外したミラー。`toReal_klDiv_eq_integral_klFun` → `klDiv_eq_lintegral_klFun_of_ac` (Basic.lean:138)、`Measure.integral_compProd` → `Measure.lintegral_compProd` (Tonelli)。slice identity `rnDeriv_compProd_eq_kernel_rnDeriv` (`:69`、ℝ≥0∞ 共用) はそのまま。
   - **工数感**: ~30-50 行。**落とし穴**: `[MeasurableSpace.CountableOrCountablyGenerated 𝓧 𝓨]` の継承 (主要前提ボックス参照、② signature に α 制約が leak しうる)。`h_int` (llr integrability) が ℝ≥0∞ Tonelli で本当に落ちるか — `klDiv_eq_lintegral_klFun_of_ac` は `h_ac` のみ要求 (integrability 不要) なので落ちる見込みだが、`klFun` の符号 (klFun ≥ 0 は `klFun_nonneg`) で ℝ≥0∞ 値の well-definedness を確保する必要。
2. **step b' = per-fibre 符号付き ℝ≥0∞/EReal lift** `klDiv_eq_signed_negMulLog_lintegral_sub_cross` (仮称)。
   - **推奨実装**: `klDiv_toReal_eq_neg_differentialEntropy_sub_cross` (`:97`) の ℝ≥0∞/EReal ミラー。`klFun(t) = t log t + 1 − t`、両 prob measure の mass 相殺で `−h(κz)`(=A/B 差) + cross に。
   - **工数感**: ~40-80 行。**落とし穴**: 符号 (A=⊤ / B=⊤ の場合分け)、`negMulLog` 正部・負部の lintegral 分離 (signed log は ℝ≥0∞ に直接入らない、A/B の二本立て必須)。`hcond_ne_bot` 由来の ⊥ 除外を fibre レベルで a.e. 化する手間。
3. **step c' = marginal collapse の ℝ≥0∞ ミラー** `lintegral_condDistrib_density_marginal_eq` (仮称)。
   - **推奨実装**: `integral_condDistrib_marginal_eq` (`:150`、Fubini core) の `∫`→`∫⁻` ミラー + 正部/負部分離。`compProd_map_condDistrib` + `lintegral_compProd` (Tonelli) + `lintegral_map`。
   - **工数感**: ~30-60 行。**落とし穴**: `integral_toReal_rnDeriv_mul` (per-fibre 密度展開、`:217`) の lintegral 対応物 (`lintegral_withDensity` 系) の verbatim 確認が未踏。signed cross の正部/負部分離。
4. **assemble (EReal sum 形)** = ② 本体。step a'/b'/c' を `condEntExt + klDiv` の EReal sum に組み、⊤ 項を `add_top_of_ne_bot` で吸収。
   - **工数感**: ~30-50 行 (項目4 が全て既存なので配線中心)。**落とし穴**: `hcond_ne_bot` で ⊥ 枝を閉じる場合分け、`A=⊤`/`klDiv=⊤` の各ケースで sum が `⊤` になることの EReal 算術。

**総工数感**: 4 step 合計 ~130-240 行 + 型クラス継承の取り回し。**multi-session moonshot 規模だが path 可視 (plan §7-6 の probe verdict (B) と整合)**。最大不確実性 = step b'/c' の signed-log 正部負部分離の実装量と、step a' の `CountableOrCountablyGenerated` leak。

---

## Mathlib 壁の列挙 (真の Mathlib 不在)

| 壁候補 | loogle conclusion-shape 二段確認 | 評価 |
|---|---|---|
| 条件付き KL = fibrewise lintegral 平均 (ℝ≥0∞) | `klDiv, compProd, lintegral` → **Found 0**。`klDiv (compProd _ _) _ = lintegral _ _` (conclusion-shape) → **Found 0**。`klDiv (compProd _ _) _ = integral _ _` → **Found 0**。`condDistrib, klDiv` → **Found 0** | **Mathlib 不在だが真の壁ではない** — in-tree `klDiv_compProd_toReal_integral` (`CondKLIntegral.lean:108`、`@audit:ok`) が同 gap を `.toReal` で既埋。ℝ≥0∞ 版は self-build template 明確 (項目1)。Mathlib `ChainRule.lean:74-77` が TODO 明記 (= Mathlib 側も「未整備だが可能」と認識) |

**`@residual(wall:…)` 対象**: **現時点で無し**。① 配線 / ② self-build (template 書ける) のいずれかで、真に「命題が存在せず self-build template も書けない」項目は本調査で見つからなかった。3 step (a'/b'/c') は全て in-tree `@audit:ok` lemma の ℝ≥0∞ ミラーであり、conclusion-shape 反証義務 (template lemma 1 本) を全て充足する。

**shared sorry 補題化候補**: step a' (`klDiv_compProd_lintegral`、ℝ≥0∞ 版 fibrewise) は Mathlib `ChainRule.lean` TODO を埋める汎用補題。将来 EPI 以外 (条件付き相互情報量の他用途) でも再利用されうるので、in-tree の汎用 namespace (`CondKLIntegral.lean` 拡張) に置けば single-source。現状 `differentialEntropyExt_eq_condEntExt_add_klDiv` 1 本のみが consumer なので散在リスクは低い (詳細 → `docs/audit/audit-tags.md`「共有 Mathlib 壁」)。

---

## 撤退ラインへの距離

親計画 §7-5 (W-Y1 専用撤退ライン) + §7-4 判断点:

- **L-WY1-α (route α 型壁)**: 「EReal chain rule が ⊤ 項で `⊤−⊤=⊥` 等の退化に落ち、workhorse EReal 化が傘 plan の Real 温存制約と衝突」。
  - **本調査の距離**: **触れる可能性あり、ただし現時点で発動なし**。② は sum 形 (`condEntExt + klDiv`、差分 `⊤−⊤` を RHS に作らない) を採用済で、⊤ 項は `add_top_of_ne_bot` (項目4、既存) で吸収できる設計。`hcond_ne_bot` が ⊥ 枝を honest に除外。**workhorse (`differentialEntropy : Measure ℝ → ℝ`) は触らず、上位に EReal 層 (`condDifferentialEntropyExt` 等) を足す設計**なので Real 温存制約と衝突しない (def `EPIUncondCondEntropyExt.lean:52` は EReal Bochner を組まず ℝ≥0∞ lintegral で構成済、衝突回避済)。
- **§7-4 判断点 (`plan:` 据置 vs `wall:` 昇格)**: 「道 A chain rule (②) が型壁で 2-3 session 詰まれば `wall:` 昇格」。
  - **本調査の独立材料**: ② は **真の Mathlib 壁を含まない self-build** (壁候補 1 種が in-tree `.toReal` 既埋 + template 明確)。⇒ **現時点で `plan:` 据置が妥当**という材料を提供 (判定は orchestrator/planner)。型クラス leak (`CountableOrCountablyGenerated`) が実装で hell 化した場合のみ session 数が伸びる risk。
- **新規撤退ライン提案 (縮退案)**: 本調査からは新規撤退ラインの提案不要 (既存 §7-4/§7-5 が cover)。仮に step a' の `CountableOrCountablyGenerated α ℝ` が ② signature に leak し downstream (gateway atom) を破壊する場合は、② の `Z : Ω → α` を `[StandardBorelSpace α]` or `[Countable α]` 制限する honest regularity precondition 追加が縮退口 (load-bearing でない、sorry+@residual は不要なので撤退口というより signature 補強)。

**consumer 逆引きメモ (item 5 関連)**: crux ② `differentialEntropyExt_eq_condEntExt_add_klDiv` の direct consumer は `differentialEntropyExt_indep_add_eq_add_klDiv` (`EPIUncondMonotone.lean:80-103`、line 103 で呼出) **1 本のみ** (plan §7-7 の「集約点単一」と整合)。これが gateway atom `entropyPowerExt_mono_add` (`:176`) と +∞ 伝播 `differentialEntropyExt_top_of_indep_add` (`:153`) / mono を ② transitive で継承。⇒ ② signature 変更 (型クラス追加等) の ripple は (i-a) 1 本 → gateway atom 1 本の連鎖。`scripts/dep_consumers.sh` は root olean stale で未実行 (docs-only につき `lake build` 回避)、上記は plan §7-7 verbatim + rg 確認による (term レベル実値の機械確認は実装着手時に `lake build InformationTheory` 後 `dep_consumers.sh InformationTheory.Shannon.differentialEntropyExt_eq_condEntExt_add_klDiv` で取得推奨)。

---

## 着手 skeleton

> ② 本体は既存 file `InformationTheory/Shannon/EPIUncondCondEntropyExt.lean:191` の sorry を埋める形。step a'/b'/c' の helper は同 file or `CondKLIntegral.lean` 拡張に置く。以下は **step a' helper を新規 skeleton で立てる場合**の出だし (① の ℝ≥0∞ fibrewise を最初に landing する想定)。

```lean
import InformationTheory.Shannon.CondKLIntegral  -- klDiv_compProd_toReal_integral (.toReal 元)
import Mathlib.InformationTheory.KullbackLeibler.Basic  -- klDiv_eq_lintegral_klFun_of_ac
import Mathlib.InformationTheory.KullbackLeibler.ChainRule  -- klDiv_compProd_eq_add / _left
import Mathlib.Probability.Kernel.Composition.MeasureCompProd  -- lintegral_compProd (Tonelli)

namespace InformationTheory

open Real MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {μ : Measure 𝓧} {κ η : Kernel 𝓧 𝓨}

section LIntegral
-- 主要前提ボックス: 型クラスは .toReal 元 (CondKLIntegral.lean:95-96) を継承する見込み。
-- CountableOrCountablyGenerated 𝓧 𝓨 が leak するか着手時に verbatim 確認。
variable [IsFiniteMeasure μ] [IsMarkovKernel κ] [IsMarkovKernel η]
  [MeasurableSpace.CountableOrCountablyGenerated 𝓧 𝓨]

/-- **(step a') ℝ≥0∞ 版 fibrewise 条件付き KL** (Mathlib `ChainRule.lean:74-77` TODO の ℝ≥0∞ 形)。
`klDiv_compProd_toReal_integral` (`CondKLIntegral.lean:108`、`.toReal` 形) の Tonelli ミラー。
ℝ≥0∞ では Tonelli (`lintegral_compProd`) が無 integrability ゆえ `h_int` を落とせる。 -/
theorem klDiv_compProd_lintegral (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ z, klDiv (κ z) (η z) ∂μ := by
  sorry  -- @residual(plan:epi-uncond-deffix-monotone-plan) — step a' self-build (項目1)

end LIntegral

end InformationTheory
```

② 本体 (既存 `EPIUncondCondEntropyExt.lean:191` の sorry) は step a'/b'/c' landing 後に `rw [klDiv_compProd_lintegral, …]` + EReal sum assemble で埋める。最初の `sorry` を step a' (① の最も配線寄りで in-tree `.toReal` 元が明確な部分) から割っていくのが着手 1 手。

---

## 総括 (§7-4 判断点の独立材料)

**② `differentialEntropyExt_eq_condEntExt_add_klDiv` は「known-shape self-build (配線中心)」であり、真の Mathlib 壁を 0 本含む** という独立評価。

各 step の gap 判定集約:
- **項目1 (step a')**: ② 自作要。Mathlib 不在 (`ChainRule.lean:74-77` TODO、conclusion-shape 二段で Found 0) **だが** in-tree `klDiv_compProd_toReal_integral` (`@audit:ok`) が同 gap を `.toReal` で既埋、ℝ≥0∞ ミラーの template 明確 (~30-50 行)。
- **項目2 (step b')**: ② 自作要。in-tree `klDiv_toReal_eq_neg_differentialEntropy_sub_cross` (`@audit:ok`) の符号付き EReal lift (~40-80 行)、符号 (A/B 発散) が delicate だが template あり。
- **項目3 (step c')**: ② 自作要。in-tree `integral_condDistrib_marginal_eq` (`@audit:ok`) の ℝ≥0∞ ミラー (~30-60 行)、Tonelli で integrability 落とせる。
- **項目4 (assemble)**: ① Mathlib 既存 (配線のみ)。EReal ⊤-吸収・coe 準同型完備。
- **項目5 (acyclic)**: 依存方向メモ — 元 Real bridge (`:124`) は conditioning 単調性 (`:224`) に非依存ゆえ ② も acyclic に組める (判定は planner)。

結論として ② は **plan §7-6 probe verdict (B)「multi-session moonshot だが path 可視、Mathlib-不能 wall ではない」と整合**。現 classification `@residual(plan:epi-uncond-deffix-monotone-plan)` は本在庫から見て**妥当** (`wall:` 過大評価でない)。最大の実装 risk は (a) step a' の `[MeasurableSpace.CountableOrCountablyGenerated α ℝ]` が ② signature (現 `α` 制約なし) に leak する型壁、(b) step b'/c' の signed-log 正部負部分離の実装量。これらが 2-3 session 詰まれば §7-4 で `wall:` 昇格、というのが既存撤退ラインの想定通り。**判定は orchestrator/planner が行う (本ファイルは材料提供のみ)**。
