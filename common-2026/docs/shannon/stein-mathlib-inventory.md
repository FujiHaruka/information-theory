# Shannon: Stein の補題 Mathlib インベントリ サブ計画

> **Parent**: [`stein-moonshot-plan.md`](stein-moonshot-plan.md) §Phase 0

<!--
雛形メモ:
- 各候補補題は CLAUDE.md「Subagent Inventory of Mathlib Lemmas」規約に従う
  (file:line / 完全署名 / 引数型 / 結論形 verbatim、`[..]` プレリク鍵括弧厳守)
- "無し" でも探索した query を記録 (negative grep / loogle 結果は資産)
-->

## 進捗

- [x] 軸 1: `klDiv` 既存 API + chain rule (`klDiv_compProd_eq_add` / `klDiv_compProd_left`)
- [x] 軸 2: likelihood ratio (`MeasureTheory.llr` / `Measure.rnDeriv`) と log measurability
- [x] 軸 3: hypothesis testing formalism (Mathlib 不在の確認)
- [x] 軸 4: AEP 補題再利用候補 (本 project 既存)
- [x] 軸 5: `Filter.liminf` / `Filter.atTop` 漸近形 (上下界系)
- [x] 軸 6: Neyman-Pearson lemma (Mathlib 不在の確認 + 自前構築方針)

## ゴール / Approach

Stein の補題 (Phase A〜D) の着手前に **必要な Mathlib API がどれだけ揃っているか / 何を自前で書くか / AEP の何を再利用するか**
を 6 軸で固定し、本計画の skeleton を sorry-driven で書ける状態にする。**結論先取り**:

- **Mathlib `klDiv` + chain rule (`klDiv_compProd_eq_add` / `klDiv_compProd_left`) 完備**
  - ただし **`klDiv (Measure.pi μs) (Measure.pi νs) = ∑ i, klDiv (μs i) (νs i)` は不在**、`Fin n` 上 `MeasurableEquiv.piFinSuccAbove` 経由で induction を 1 本自作 (40〜80 行見積)
- **`MeasureTheory.llr μ ν x := log (μ.rnDeriv ν x).toReal` 既存** — Stein の中心量、`measurable_llr` も既存
- **`MeasureTheory.Measure.pi` + `iIndepFun_iff_map_fun_eq_pi_map` で i.i.d. 列の joint law を Pi 測度に翻訳可能** — AEP では本筋に乗らなかったが Stein では必要
- **検定 / 仮説検定 formalism (`HypothesisTest`, `Test`, `RejectionRegion`) は Mathlib 不在** — 自前でも 1〜2 本の def + α/β error 補題のみで足りる (検定 = 可測集合 + α-level バウンド)
- **Neyman-Pearson 補題は Mathlib 不在** — Stein の lower bound には Neyman-Pearson の最適性は **不要** (likelihood ratio test を自前構成 + 直接 typicality で attack)
- **`Filter.le_liminf_iff` / `Filter.Tendsto.liminf_eq` 既存** — `liminf` 形 statement に乗せる橋渡しは AEP Phase D で残された懸念と同じだが、Stein は `lim` (両側収束) 形で書けるため `liminf = limsup` の組み合わせで attack
- **AEP 補題は **`pmfLog` / `aep_inProbability` / `typicalSet` を Stein で 2 分布版に拡張** — 計画上 70〜80% は AEP 構造の type-parametric replay

---

## 軸 1: `klDiv` 既存 API + chain rule

### `InformationTheory.klDiv` (定義)

- **file:line**: `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57`
- **完全署名**:
  ```lean
  noncomputable def klDiv (μ ν : Measure α) : ℝ≥0∞ :=
    if μ ≪ ν ∧ Integrable (llr μ ν) μ
      then ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ)
      else ∞
  ```
- **`[..]` プレリク**: section variable `{α : Type*} [MeasurableSpace α]`
- **値域**: `ℝ≥0∞` (= `ENNReal`)。Stein の statement は `ENNReal` のまま `(klDiv P Q).toReal` で実数に下ろす
- **本 plan での要点**:
  - `klDiv P Q` は 2 つの `Measure α` (= P, Q) を取る — 自前 wrapper 不要
  - `[IsProbabilityMeasure P]` `[IsProbabilityMeasure Q]` (or `IsFiniteMeasure`) を仮定し、`Integrable (llr P Q) P` (= `Q ≪`-side integrability) は `α : Fintype` で自動

### `InformationTheory.klDiv_compProd_eq_add` (chain rule, 一般)

- **file:line**: `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:204`
- **完全署名 verbatim**:
  ```lean
  variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
    {μ ν : Measure 𝓧} {κ η : Kernel 𝓧 𝓨}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η]
  variable (μ ν κ η) in
  theorem klDiv_compProd_eq_add :
      klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)
  ```
- **`[..]` プレリク verbatim**: `[IsFiniteMeasure μ]` `[IsFiniteMeasure ν]` `[IsMarkovKernel κ]` `[IsMarkovKernel η]`
- **本 plan での要点**:
  - `μ` を P^{(n-1)}, `ν` を Q^{(n-1)}, `κ` を `Kernel.const _ P`, `η` を `Kernel.const _ Q` と置けば `klDiv (P^{(n-1)} ⊗ Kernel.const _ P) (Q^{(n-1)} ⊗ Kernel.const _ Q) = klDiv P^{(n-1)} Q^{(n-1)} + klDiv (P^{(n-1)} ⊗ Kernel.const _ P) (P^{(n-1)} ⊗ Kernel.const _ Q)`
  - 2 段目の右辺第 2 項は `klDiv_compProd_left` で `klDiv P Q` (= 単発分) に下りる
  - これを Pi 構築 + `MeasurableEquiv.piFinSuccAbove` で `Fin n` 上の i.i.d. に翻訳 → `klDiv (Pi P) (Pi Q) = n · klDiv P Q` (induction on n)

### `InformationTheory.klDiv_compProd_left`

- **file:line**: `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:182` (`@[simp]`)
- **完全署名 verbatim**:
  ```lean
  variable (μ ν κ) in
  @[simp]
  lemma klDiv_compProd_left :
      klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν
  ```
- **`[..]` プレリク verbatim**: 同上の `[IsFiniteMeasure μ]` `[IsFiniteMeasure ν]` `[IsMarkovKernel κ]` (`η` 不在)
- **本 plan での要点**: 上の chain rule から `μ = ν` 退化形を取ると `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` が出る。**i.i.d. への適用ではこれを 1 段目 (left compProd) で 0 にし、2 段目で `klDiv P Q` を取り出す**

### `InformationTheory.klDiv_eq_zero_iff`

- **file:line**: `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:377`
- **完全署名 verbatim**:
  ```lean
  lemma klDiv_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
      klDiv μ ν = 0 ↔ μ = ν
  ```
- **`[..]` プレリク verbatim**: `[IsFiniteMeasure μ]` `[IsFiniteMeasure ν]`
- **本 plan での要点**: Stein の statement は `klDiv P Q < ∞` 仮定 (= `P ≪ Q` + integrable LLR) のもと `klDiv P Q > 0` (P ≠ Q) で attack。退化 `klDiv P Q = 0` (= `P = Q`) では Stein の右辺が 0 で Stein は trivial に成立 (両側 0)

### `InformationTheory.klDiv_self`

- **file:line**: `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:78`
- **完全署名 verbatim**: `lemma klDiv_self (μ : Measure α) [SigmaFinite μ] : klDiv μ μ = 0`

### `InformationTheory.toReal_klDiv` (ENNReal → Real 翻訳)

- **file:line**: `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:157`
- **完全署名 verbatim**:
  ```lean
  lemma toReal_klDiv (h : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
      (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ + ν.real univ - μ.real univ
  ```
- **本 plan での要点**: 確率測度なら `μ.real univ = ν.real univ = 1` で `(klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ` (= 期待値 LLR)。**Stein の lower / upper bound は両方この `Real` 形で attack**

### Mathlib 不在 (要自前構築)

- **`klDiv (Measure.pi μs) (Measure.pi νs) = ∑ i, klDiv (μs i) (νs i)`** — loogle `Found 0 declarations mentioning MeasurableSpace.pi, MeasureTheory.Measure.pi, and InformationTheory.klDiv` で確認
  - **自前構築方針**: `Fin n` 上 induction、`MeasurableEquiv.piFinSuccAbove` で `Fin (n+1) → α ≃ᵐ α × (Fin n → α)`、`Measure.map_pi` 系で `Measure.pi` を `Measure.prod` に下げ、`Measure.compProd_const` (= `μ ⊗ₘ Kernel.const _ ν = μ.prod ν`) で compProd 形に乗せ、`klDiv_compProd_eq_add` + `klDiv_compProd_left` の連打。**40〜80 行見積**
- **`klDiv (μ.prod ν₁) (μ.prod ν₂) = klDiv ν₁ ν₂` (右因子)** — `Common2026/Shannon/MutualInfo.lean:80` `klDiv_prod_const_left` で**既存** (本 project 内、`[IsProbabilityMeasure μ]` 仮定付き)。Stein の i.i.d. 拡張で再利用予定
- **`klDiv (P.prod P) (Q.prod Q) = 2 · klDiv P Q`** (n = 2 退化形) — 上の自前 induction の base + step

---

## 軸 2: likelihood ratio (`MeasureTheory.llr` / `Measure.rnDeriv`)

### `MeasureTheory.llr` (= log-likelihood ratio)

- **file:line**: `Mathlib/MeasureTheory/Measure/LogLikelihoodRatio.lean:37`
- **完全署名 verbatim**:
  ```lean
  noncomputable def llr (μ ν : Measure α) (x : α) : ℝ :=
    log (μ.rnDeriv ν x).toReal
  ```
- **`[..]` プレリク**: section variable `{α : Type*} [MeasurableSpace α]`
- **本 plan での要点**:
  - **Stein の中心量**。`P^n / Q^n` の log を `(1/n) ∑_i llr (μ.map (Xs i)) (μ.map (Xs i に対応する Q-marg)) (Xs i ω)` の形で扱う
  - `α : Fintype` のもとでは `(P.rnDeriv Q x).toReal = P.real {x} / Q.real {x}` (`hQpos : Q.real{x} > 0` のとき) — `Common2026/Shannon/Bridge.lean` の `klDiv_discrete_toReal_eq_sum` 内で `h_rnD_div : (Q.rnDeriv P x).toReal = Q.real {x} / P.real {x}` として導出済み (再利用可)

### `MeasureTheory.measurable_llr`

- **file:line**: `Mathlib/MeasureTheory/Measure/LogLikelihoodRatio.lean:83`
- **完全署名 verbatim**: `lemma measurable_llr (μ ν : Measure α) : Measurable (llr μ ν)`
- **本 plan での要点**: 直接使用 (Phase A の log-likelihood plumbing で)

### `Real.measurable_log` / `Measurable.log`

- AEP inventory 軸 3 と同じ。再記載省略 (Phase A で再利用)

### `Measure.rnDeriv` (Radon–Nikodym)

- **file:line**: `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean` (定義) / `Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean` (主補題群)
- **本 plan で使う補題**:
  - `Measure.withDensity_rnDeriv_eq` — `Q ≪ P ⇒ P.withDensity (Q.rnDeriv P) = Q`、`Common2026/Shannon/Bridge.lean:248` で再利用前例あり
  - `Measure.rnDeriv_self` — `μ.rnDeriv μ = 1` (a.e.)
- **不在補題** (要自前): `(Measure.pi μs).rnDeriv (Measure.pi νs) x = ∏ i, (μs i).rnDeriv (νs i) (x i)` — Pi 値 RN 微分の積形。**Stein では本格的には経由しない** (compProd / klDiv 経由で済ませる)

### Pi 上の log-likelihood ratio 取り扱い

- **方針**: `Pi` 値の RN 微分を**直接**書かず、AEP の `pmfLog` 戦略を Stein 用に **2 分布化**して使う:
  ```lean
  -- AEP 既存:
  noncomputable def pmfLog (μ : Measure Ω) (Xs : ℕ → Ω → α) : α → ℝ :=
    fun x => -Real.log ((μ.map (Xs 0)).real {x})

  -- Stein 用 2 分布化 (Phase A で導入):
  noncomputable def llrPmf (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : α → ℝ :=
    fun x => Real.log (P.real {x} / Q.real {x})
  -- ↑ または等価に Real.log (P.rnDeriv Q x).toReal = (llr P Q x) を直接使う
  ```
- **理由**: AEP では `α : Fintype` のもとで `pmfLog` の point-wise 評価が log と log の差で済んだ。Stein でも同じ離散仮定 (P, Q 共に Fintype 上の確率測度 + Q full support) で **point-wise**に展開できる。`Pi` 値 RN 微分の汎用 plumbing を回避

---

## 軸 3: hypothesis testing formalism

### Mathlib に検定 (Test / RejectionRegion / TypeIError) は無い

- **negative grep 確認**:
  - `rg "neyman.pearson|hypothesis.test|nplemma|likelihood.ratio.test" .lake/packages/mathlib/Mathlib/` → 0 件
  - `rg "TypeIError|TypeIIError|RejectionRegion|HypothesisTest" .lake/packages/mathlib/Mathlib/` → 0 件 (要 Phase 0 着手時に再確認)
- **本 plan の方針**: 自前で薄く定義する。**`Test α := MeasurableSet (s : Set α)`** + α-level / β-error の definition を 2〜3 本書く形:
  ```lean
  /-- 検定 `s` (rejection region for H_0 = "X ~ P") の type-I error: P が s を出してしまう確率 -/
  noncomputable def typeIError (P : Measure α) (s : Set α) : ℝ≥0∞ := P s

  /-- type-II error: Q が s の補集合を出す確率 (i.e. accept H_0 when Q is true) -/
  noncomputable def typeIIError (Q : Measure α) (s : Set α) : ℝ≥0∞ := Q sᶜ
  ```
  上 2 本だけで Stein の statement に必要な vocabulary は揃う。`α-level test` は `typeIError P s ≤ ENNReal.ofReal ε` で書く。

### Stein statement への乗せ替え

```lean
theorem stein_lemma
    {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q)
    (hQpos : ∀ x : α, 0 < Q.real {x})  -- AEP Phase C と同じ仮定形
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto
      (fun n : ℕ => -(1 / n : ℝ) * Real.log
        (sInf { (Measure.pi (fun _ : Fin n => Q)) sᶜ
              | s : Set (Fin n → α),
                MeasurableSet s ∧
                (Measure.pi (fun _ : Fin n => P)) sᶜ ≤ ENNReal.ofReal ε }).toReal)
      Filter.atTop
      (𝓝 (klDiv P Q).toReal)
```

実装上は `sInf` 部分を直接扱わず、**lower bound `≥ klDiv - δ`** + **upper bound `≤ klDiv + δ`** の 2 主定理に分解、両方を `lim` で繋ぐ。

---

## 軸 4: AEP 補題再利用候補 (本 project 既存)

### 直接 2 分布版に拡張する補題

`Common2026/Shannon/AEP.lean` で確立済 (432 行、0 sorry) のうち、Stein で再利用するもの:

| AEP 補題 | Stein 用拡張 | 再利用度 |
|---|---|---|
| `pmfLog μ Xs : α → ℝ` (AEP.lean:67) | `llrPmf P Q : α → ℝ := log (P.real{x}) - log (Q.real{x})` または `MeasureTheory.llr (μ.map (Xs 0)) Q` 直接 | 構造同一、2 分布化のみ |
| `measurable_pmfLog` (AEP.lean:70) | `measurable_llrPmf` (or `measurable_llr` 直接) | `α : Fintype` から `measurable_of_finite` で同手 |
| `logLikelihood μ Xs i : Ω → ℝ` (AEP.lean:78) | `logLikelihoodRatio P Q Xs i : Ω → ℝ := llrPmf P Q ∘ Xs i` | 構造同一 |
| `integrable_logLikelihood` (AEP.lean:91) | `integrable_logLikelihoodRatio` (`α : Fintype` + Q 確率測度 ⇒ 自動) | 同手、`Integrable.of_finite` |
| `integral_logLikelihood_zero = entropy` (AEP.lean:104) | `integral_logLikelihoodRatio_under_P = klDiv P Q (Real 値)` | **最重要再利用ポイント**。教科書 LR の期待値 = KL の中核 |
| `identDistrib_logLikelihood` (AEP.lean:128) | `identDistrib_logLikelihoodRatio` | composition 補題、構造同一 |
| `indepFun_logLikelihood` (AEP.lean:135) | `indepFun_logLikelihoodRatio` | 同上 |
| `aep_ae` (AEP.lean:146) | **`stein_strong_law` (Stein 用)**: `(1/n) ∑ i, llrPmf P Q (Xs i ω) → (klDiv P Q).toReal` a.s. | **Stein lower / upper bound の中核**、`strong_law_ae_real` を Q-distribution と P-distribution の 2 回適用 |
| `aep_inProbability` (AEP.lean:174) | `stein_inProbability` | 同上、a.s. → 確率収束 lift |
| `typicalSet μ Xs n ε` (AEP.lean:222) | `steinTypicalSet P Q n ε := { x : Fin n → α | |(1/n) ∑ i, llrPmf P Q (x i) - (klDiv P Q).toReal| < ε }` | **Stein typicality 議論の主役**、Phase C で利用 |
| `measurableSet_typicalSet` (AEP.lean:232) | `measurableSet_steinTypicalSet` | 同手、`Set.toFinite` から自動 |
| `typicalSet_card_le` (AEP.lean:249) | `steinTypicalSet_Q_prob_le` (Stein-typical 上の Q 測度上界) | **構造同一**、`hQpos` 仮定 + `Real.exp_sum` ルートで attack |
| `typicalSet_prob_tendsto_one` (AEP.lean:367) | `steinTypicalSet_P_prob_tendsto_one` (P 測度で typical → 1) | 直接同手 |
| `jointRV Xs n` (AEP.lean:47) | 共有 (再利用、変更なし) | 完全再利用 |

**結論**: AEP の 13 補題のうち **12 補題が型 / 概念上 1〜2 行の 2 分布化で済む**。Stein 専用の **完全新規補題は 2〜3 本のみ** (likelihood ratio test の構成 + lower bound、upper bound)。

### AEP plumbing 再利用の戦略

1. **`Common2026/Shannon/Stein.lean`** に Stein 全体を書く (新規ファイル、`AEP.lean` を import)。AEP 補題は `open` で取り込み
2. **Stein 用補題は AEP 補題の名前を `_stein` 接尾語付きで複製しない** — 代わりに **AEP 補題を type-class generic / 多分布対応に generalize** すべきかは判断保留 (refactor は Stein 完了後)。第 1 セッションでは **Stein.lean 内で 2 分布版を local に書き、AEP 既存補題は差分のみ呼ぶ**
3. **Phase A の skeleton**: `pmfLog` を `llrPmf` に置き換え、`logLikelihood` を `logLikelihoodRatio` に置き換える step-by-step rename + 2 分布化

---

## 軸 5: `Filter.liminf` / `Filter.atTop` 漸近形

### `Filter.Tendsto.liminf_eq` (`Tendsto → liminf = lim`)

- **file:line**: `Mathlib/Topology/Order/LiminfLimsup.lean:196`
- **完全署名 verbatim**:
  ```lean
  theorem Filter.Tendsto.liminf_eq {f : Filter β} {u : β → α} {a : α} [NeBot f]
      (h : Tendsto u f (𝓝 a)) : liminf u f = a
  ```
- **`[..]` プレリク verbatim**: `[ConditionallyCompleteLinearOrder α]` (section variable)、`[NeBot f]`
- **本 plan での要点**: AEP Phase D で残された懸念がここで効く。Stein の statement を **`lim` (= `Tendsto`) 形** で書けば `liminf_eq` の橋渡しは不要 (lim 形 → Tendsto に直接乗る)。**Stein は lower bound と upper bound の両側を取って `Tendsto` で結ぶ路線で attack** → liminf API は補助的にしか使わない

### `Filter.le_liminf_iff`

- **file:line**: `Mathlib/Order/LiminfLimsup.lean:922`
- **完全署名 verbatim**:
  ```lean
  theorem le_liminf_iff {x : β}
      (h₁ : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
      (h₂ : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
      x ≤ liminf u f ↔ ∀ y < x, ∀ᶠ a in f, y < u a
  ```
- **本 plan での要点**: Stein の lower bound を `liminf` 形で書きたい場合 (Tendsto 不成立の途中段階) に使う。本 plan では **両側 bound → `Tendsto`** で完結するため、本補題は撤退ライン以降の保険

### Stein で必要な liminf / limsup 関連

- **基本路線 (lim 形)**:
  ```
  Tendsto (fun n => -(1/n) * log β_n^*) atTop (𝓝 (klDiv P Q).toReal)
  ```
  ここで `β_n^*` は最適 type-II error (= `inf { Q^n s^c | typeIError P^n s ≤ ε }`)
- **lower bound と upper bound の 2 段で挟む**:
  - Lower: `∀ ε > 0, ∀ᶠ n in atTop, -(1/n) * log β_n^* > klDiv - ε - δ` (= "Stein achievability"-side)
  - Upper: `∀ ε > 0, ∀ᶠ n in atTop, -(1/n) * log β_n^* < klDiv + ε + δ` (= "Stein converse"-side)
  - これらを `Filter.tendsto_atTop_of_eventually_le_and_ge` 系で結合

---

## 軸 6: Neyman-Pearson lemma (Mathlib 不在 + 自前構築方針)

### Mathlib 確認 (negative)

- `rg "neyman.pearson|np_lemma|likelihood_ratio_test|optimal.test" .lake/packages/mathlib/Mathlib/` → 0 件
- `rg "stein|chernoff|sanov|error.exponent" .lake/packages/mathlib/Mathlib/` → 0 件 (情報理論側)
- 結論: **Mathlib に Neyman-Pearson は無い**。Stein で必要な「最適性」は **Neyman-Pearson の full statement なし**で attack できるかが本 plan の判断ポイント

### Stein lower bound の attack 方針

教科書の Stein は通常以下の 2 段:

1. **lower bound (achievability)**: ある検定 (likelihood ratio test) を構成し、`α_n ≤ ε` で `β_n ≤ exp(-n · klDiv P Q + n · δ)` を示す
   - **手法**: `T_ε^n` (Stein-typical set) を rejection region とする検定を構成 → `α_n = P^n(T_ε^{n,c}) → 0` (AEP Phase C 再利用)、`β_n = Q^n(T_ε^n) ≤ exp(-n · (klDiv - ε))` (typicality 上の Q 測度評価)
   - **Neyman-Pearson 不要**: 具体的 LRT を構成 + その性能評価で完結
2. **upper bound (converse)**: 任意の検定で `α_n ≤ ε ⇒ β_n ≥ exp(-n · klDiv P Q - n · δ)` (= 逆向きの最適性)
   - **手法**: 任意の検定 `s` を取り、Stein-typical set との交わりで分解、KL 不等式 + chain rule (`klDiv P^n Q^n = n · klDiv P Q`) で評価
   - **Neyman-Pearson の代用**: KL 不等式 (`klDiv ≥ 0` + chain rule) と data processing inequality (本 project 既存) で代用可能 — **教科書 Cover-Thomas Theorem 11.8.3 の証明は Neyman-Pearson 不要**

### 結論

- **Neyman-Pearson 補題本体は本 plan 範囲では書かない**。Stein の lower / upper を **直接 typicality + chain rule** で attack
- **撤退ライン**: もし upper bound (converse) で「任意の検定」を扱う際に Neyman-Pearson の最適性が必要になった場合 → 別 sub-plan として Neyman-Pearson を切り出す (本 plan は lower bound のみで close)。本 plan の **判断ログ Phase 0 末尾**に「直接 KL 経路で行く」を明記

---

## 結論サマリ (各軸 1 行)

| 軸 | 結論 | Phase 影響 |
|---|---|---|
| 1 klDiv | `klDiv` + `klDiv_compProd_eq_add` + `klDiv_compProd_left` 完備、**Pi 化 (`klDiv_pi_eq_sum`) は不在 → 自前 induction 40〜80 行** | Phase A の山場 1 |
| 2 llr | `MeasureTheory.llr` + `measurable_llr` 既存、`α : Fintype` で point-wise 展開可 | Phase A `llrPmf` 設計に直接乗る |
| 3 hypothesis test | Mathlib 不在、自前 `typeIError` / `typeIIError` 2 本で十分 | Phase A の vocabulary 整備 1 ターン |
| 4 AEP 再利用 | **AEP の 13 補題のうち 12 が 1〜2 行の 2 分布化で再利用可**、新規は 2〜3 本のみ | Phase A〜C の 70〜80% は AEP 構造の type-parametric replay |
| 5 liminf | `Filter.le_liminf_iff` / `Tendsto.liminf_eq` 既存、Stein は両側 bound → `Tendsto` で完結する路線で liminf 依存最小化 | Phase D は `Tendsto` 形 statement で attack |
| 6 Neyman-Pearson | Mathlib 不在、**本 plan 範囲では書かない** (直接 typicality + chain rule で attack) | upper bound 路線判定、撤退時別 sub-plan |

---

## Phase A 着手判定

**GO**:

- `klDiv` 一式 + chain rule は Mathlib 完備、本 plan の skeleton はそのまま書ける
- AEP 既存補題で 70〜80% カバー、新規構築は 2〜3 本のみ
- Neyman-Pearson は迂回可能 (典型集合 + chain rule で attack)
- 唯一の不確実性は **`klDiv (Measure.pi P) (Measure.pi Q) = n · klDiv P Q` の自前 induction**、これは Phase A 内で副産物として書く方針

## Definition of Done (本 inventory)

- [x] 6 軸全て調査完了
- [x] `klDiv_compProd_eq_add` / `klDiv_compProd_left` の verbatim 署名 + `[..]` プレリク確定
- [x] `MeasureTheory.llr` 定義の verbatim 確認
- [x] hypothesis testing / Neyman-Pearson は Mathlib 不在を裏取り (`rg` 0 件確認)
- [x] AEP 既存補題の 2 分布化マッピング表作成
- [x] Phase A skeleton (`Common2026/Shannon/Stein.lean` の sorry-driven 出だし) が書ける状態

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 本 inventory はまだ起草段階。本体着手で発見があれば追記。 -->
