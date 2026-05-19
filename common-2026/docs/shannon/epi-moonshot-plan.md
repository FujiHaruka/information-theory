# Entropy Power Inequality (T2-D) ムーンショット計画 🌙

> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 2 — T2-D.
> Entropy Power Inequality」
>
> **Predecessor**:
> - T2-A `AWGN.lean` (F-1+F-2+F-3+F-4 pass-through publish)
> - T2-F `FisherInfo.lean` + `FisherInfoGaussian.lean` (L-F1+L-F2 hypothesis
>   pass-through、`fisherInfo` の representative-dependence flaw は既知)
> - E-9 `DifferentialEntropy.lean` (Gaussian entropy + max entropy 完成)
>
> **Inventory**: [`epi-mathlib-inventory.md`](epi-mathlib-inventory.md) (Mathlib
> + Common2026 在庫、自作要素 ~420-630 行、撤退ライン L-EPI1+L-EPI2+L-EPI3
> 採用)
>
> **Status (2026-05-19)**: 着手前。inventory 完了済、本 plan は Phase 1 の成果物。
> T2-A / T2-B / T2-C / T2-F の hypothesis pass-through pattern を流用 + EPI 専用
> L-EPI* 新規。**撤退ライン L-EPI1 + L-EPI2 + L-EPI3 全採用形で publish** (seed
> 規模 ~420-630 行内に着地、roadmap 中央 800-1200 行よりタイト)。
>
> **Goal**: 新規ファイル `Common2026/Shannon/EntropyPowerInequality.lean` で
> **Cover-Thomas Theorem 17.7.3** (`exp(2 h(X+Y)) ≥ exp(2 h(X)) + exp(2 h(Y))`)
> を **hypothesis pass-through 形 (L-EPI1 + L-EPI2 + L-EPI3 三本)** で publish。
>
> **撤退ライン**: [L-EPI1] Stam inequality を `IsStamInequalityHypothesis`
> predicate hypothesis 形に外出し / [L-EPI2] de Bruijn integration を
> `IsDeBruijnIntegrationHypothesis` predicate hypothesis 形に外出し / [L-EPI3]
> EPI 結論そのものを `IsEntropyPowerInequalityHypothesis` predicate hypothesis
> 形に外出し (詳細 §撤退ライン、inventory §D に対応)。
>
> **副成果**: Gaussian saturation case (X, Y それぞれ Gaussian なら等号成立) は
> **本 plan 内で full discharge** (撤退ラインに含めない、~50-80 行)。

## 進捗

- [x] Phase 0 — Mathlib + Common2026 API 在庫 ✅ → [`epi-mathlib-inventory.md`](epi-mathlib-inventory.md)
- [ ] Phase A — `entropyPower`, `entropyPowerMeasure` + 基本性質 📋
- [ ] Phase B — L-EPI1 + L-EPI2 + L-EPI3 predicate 定義 📋
- [ ] Phase C — 主定理 `entropy_power_inequality` (L-EPI3 適用) 📋
- [ ] Phase D — Gaussian saturation case (full discharge、補助 corollary) 📋
- [ ] Phase E — 補助 corollary 群 (multi-arg, monotonicity, scaling) 📋
- [ ] Phase V — verify (`lake env lean ...` clean) 📋

## ゴール / Approach

### Goal (最終定理 signature)

```lean
namespace InformationTheory.Shannon.EntropyPowerInequality

/-- **Entropy power** of a measure `μ` on `ℝ`. Cover-Thomas Ch.17.7 定義は
`N(μ) := (2πe)⁻¹ · exp (2 h(μ))` だが、本 file は EPI signature
`exp(2 h(X+Y)) ≥ exp(2 h(X)) + exp(2 h(Y))` と直結する `exp (2 h(μ))` 形を
採用 (Mathlib-shape-driven、係数 `(2πe)` は scaling corollary で吸収)。 -/
noncomputable def entropyPower (μ : Measure ℝ) : ℝ :=
  Real.exp (2 * differentialEntropy μ)

/-- L-EPI1: Stam inequality を hypothesis 化 (signature 露出のみ、本体未使用). -/
def IsStamInequalityHypothesis ... : Prop := True

/-- L-EPI2: de Bruijn integration を hypothesis 化 (signature 露出のみ). -/
def IsDeBruijnIntegrationHypothesis ... : Prop := True

/-- L-EPI3: EPI 結論を hypothesis 化 (本 plan の核心 retreat). -/
def IsEntropyPowerInequalityHypothesis (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  Real.exp (2 * differentialEntropy (P.map (fun ω => X ω + Y ω)))
    ≥ Real.exp (2 * differentialEntropy (P.map X))
      + Real.exp (2 * differentialEntropy (P.map Y))

/-- **Entropy Power Inequality** (Cover-Thomas Theorem 17.7.3).
独立 `X, Y` に対し
`exp(2 h(X+Y)) ≥ exp(2 h(X)) + exp(2 h(Y))`.

撤退ライン L-EPI1 + L-EPI2 + L-EPI3 全採用 (hypothesis pass-through 3 本)。 -/
theorem entropy_power_inequality {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (_h_stam : IsStamInequalityHypothesis X Y P)
    (_h_debruijn : IsDeBruijnIntegrationHypothesis X Y P)
    (h_epi : IsEntropyPowerInequalityHypothesis X Y P) :
    Real.exp (2 * differentialEntropy (P.map (fun ω => X ω + Y ω)))
      ≥ Real.exp (2 * differentialEntropy (P.map X))
        + Real.exp (2 * differentialEntropy (P.map Y)) :=
  h_epi

end InformationTheory.Shannon.EntropyPowerInequality
```

### Approach (overall strategy / shape of solution)

**戦略の shape**: Cover-Thomas Ch.17.7.3 EPI の証明は **2 つの主要経路**がある:

1. **de Bruijn 経路**: Stam inequality (`J(X+Y)⁻¹ ≥ J(X)⁻¹ + J(Y)⁻¹`、Fisher
   info inverse) → de Bruijn identity (`(d/dt) h(X+√t Z) = (1/2) J(X+√t Z)`) →
   integration along heat flow path → EPI.
2. **Brunn-Minkowski 経路**: Convex body Brunn-Minkowski (`|A+B|^{1/n} ≥
   |A|^{1/n} + |B|^{1/n}`) → entropy form (typical set 体積を Brunn-Minkowski
   に流す) → EPI.

**採用案: de Bruijn 経路** (judgement #1 inventory §H):

- T2-F `FisherInfo.lean` の `IsRegularDeBruijnHyp` + `deBruijn_identity` が既に
  publish 済 (statement-level pass-through 形)、上流接続が直接できる。
- Brunn-Minkowski 経路は T2-E seed として独立扱い (Mathlib `Convex` /
  `volume`-form の整備状況に依存)。

採用しても**証明本体は L-EPI3 hypothesis pass-through で 1 行**なので、上流経路の
discharge は別 plan に defer。本 plan は **EPI signature の publish と Gaussian
saturation case 等号性の full discharge** に集中。

```
[T2-F deBruijn_identity (re-use)]      [Stam inequality (Mathlib gap, defer)]

F.1 IsRegularDeBruijnHyp  ◄─────────  S.1 stamInequality {X, Y, P} (J inverse 形)
F.2 deBruijn_identity      ◄─────────  S.2 J_convolution_le
F.3 fisherInfoReal                     S.3 Fisher inverse triangle
F.4 IsRegularDensity

        ▲                                              ▲
        │ name/signature 露出のみ                       │ Mathlib 不在 → L-EPI1 で外出し
        │                                              │
        └────────────────────────────┬─────────────────┘
                                     ▼
                  T2-D EPI layer (本 plan 新規、~420-630 行)
                  ─────────────────────────────────────────
                  Phase A: entropyPower 定義 + Gaussian closed form
                  Phase B: L-EPI1/L-EPI2/L-EPI3 predicates
                  Phase C: 主定理 entropy_power_inequality (L-EPI3 適用)
                  Phase D: Gaussian saturation case (FULL DISCHARGE)
                  Phase E: 補助 corollary 群
```

**鍵となる構造選択** (CLAUDE.md Mathlib-shape-driven Definitions):

1. **`entropyPower μ : ℝ`** は `Real.exp (2 * differentialEntropy μ)` で
   **`Real.exp_pos` / `Real.exp_log` / `Real.exp_add` の結論形に直結**。
   Cover-Thomas の `(2πe)⁻¹ · e^{2h}` 形は係数のみの差なので別 corollary で扱う。

2. **L-EPI3 `IsEntropyPowerInequalityHypothesis X Y P`** は EPI 結論そのもの
   `exp(2 h(X+Y)) ≥ exp(2 h(X)) + exp(2 h(Y))` を `Prop` 化。**主定理本体は
   `:= h_epi` で着地** (T2-B L-PG1 / T2-C L-SH3 と同型流儀)。

3. **`gaussianReal_add_gaussianReal_of_indepFun`** が Mathlib にある (inventory
   §A.1) ので、X, Y それぞれ Gaussian な場合は **(`X+Y).law = gaussianReal
   (m₁+m₂) (v₁+v₂)`** が rigorous に取れ、`differentialEntropy_gaussianReal` と
   `Real.exp_log` で **Gaussian saturation case は撤退ラインなしで discharge** 可能。

4. **L-EPI1 + L-EPI2 は signature 露出のみ**。Cover-Thomas Theorem 17.7.3 の
   textbook 完全形 (Stam + de Bruijn + integration) を signature 露出するために
   主定理 signature に hypothesis 引数として残すが、本体では使わない (L-EPI3
   単独で着地)。将来 discharge plan で L-EPI1 + L-EPI2 → L-EPI3 を導出する想定。

### Approach 図

```
Phase 0 : Mathlib + Common2026 在庫                                ← 完了済 (inventory)
          ──────────────────────────────────────────────────
Phase A : entropyPower 定義 + Gaussian closed form                ← 0.5 session
                                                                   = Tier 0 (~80-120 行)
          ──────────────────────────────────────────────────
Phase B : L-EPI1/L-EPI2/L-EPI3 predicate 定義                     ← 0.25 session
                                                                   = Tier 0 (~80-100 行)
          ──────────────────────────────────────────────────
Phase C : 主定理 entropy_power_inequality (`:= h_epi`)            ← 0.1 session
                                                                   = Tier 1 (~30-50 行)
          ←──── 撤退ライン L-EPI1 + L-EPI2 + L-EPI3 三本適用 ────→
          ──────────────────────────────────────────────────
Phase D : Gaussian saturation case (FULL DISCHARGE)                ← 0.5 session
                                                                   = Tier 1 (~50-80 行)
          ──────────────────────────────────────────────────
Phase E : 補助 corollary 群 (multi-arg, scaling, monotonicity)    ← 0.5 session
                                                                   = Tier 2 (~100-200 行)
          ──────────────────────────────────────────────────
Phase V : verify (`lake env lean EntropyPowerInequality.lean`)    ← 0.25 session
```

### 段階的 ship 設計 (Tier 0 / 1 / 2)

- **Tier 0** (~160-220 行, Phase A + B): `entropyPower` + `entropyPowerMeasure` +
  Gaussian closed form + L-EPI1/L-EPI2/L-EPI3 predicate 定義。Phase A + B 完了で
  発生、`Common2026.lean` 編入 OK。partial publish 価値あり (定義 + predicate を
  hypothesis 形で公開、主定理は次フェーズ)。

- **Tier 1** (~240-350 行, Phase A + B + C + D): + `entropy_power_inequality` 主定理
  (L-EPI1+L-EPI2+L-EPI3 適用形) + Gaussian saturation case (full discharge)。**本
  plan の核心** (Cover-Thomas Theorem 17.7.3 を 3 hypothesis pass-through で
  publish + Gaussian saturating case を完全証明)。

- **Tier 2** (~420-630 行, Phase A + B + C + D + E): + 補助 corollary 群
  (multi-arg pass-through、monotonicity、scaling、log-form 等)。Phase E 完了。

- **Tier 3 (任意 stretch、本 plan の外)**: L-EPI1 + L-EPI2 + L-EPI3 を discharge する
  別 plan (`epi-stam-discharge-plan.md` + `epi-debruijn-integration-plan.md`
  + `epi-stam-to-conclusion-plan.md`)。本 plan のスコープ外、Tier 2 publish 後の
  派生 plan で。

### 規模見積もり (inventory §F より)

| 自作要素 | 想定行数 | Phase | ファイル |
|---|---|---|---|
| `entropyPower` / `entropyPowerMeasure` + positivity + unfold | ~30-50 | A | `EntropyPowerInequality.lean` |
| `entropyPower_gaussianReal` (closed form) | ~15-25 | A | `EntropyPowerInequality.lean` |
| L-EPI1/L-EPI2/L-EPI3 predicates + docstrings | ~80-100 | B | `EntropyPowerInequality.lean` |
| 主定理 `entropy_power_inequality` (L-EPI3 適用) | ~30-50 | C | `EntropyPowerInequality.lean` |
| Gaussian saturation case (full discharge) | ~50-80 | D | `EntropyPowerInequality.lean` |
| 補助 corollary (multi-arg, monotonicity, scaling) | ~100-200 | E | `EntropyPowerInequality.lean` |
| skeleton + imports + docstring + namespace | ~80-120 | A-E | `EntropyPowerInequality.lean` |
| **合計** | **~385-625** | | |

中央予測 **~500 行** (roadmap 「800-1200 行」より小さく着地、T2-F が独立 publish 済ゆえ)。

### ファイル構成 (Phase V 完了想定)

```
Common2026/Shannon/
  EntropyPowerInequality.lean  ← 新規 (~385-625 行 = Tier 0 + 1 + 2)
  DifferentialEntropy.lean     ← 既存 1010 行、変更なし (E-9 完成、再利用元)
  FisherInfo.lean              ← 既存 236 行、変更なし (T2-F 完成、name 露出のみ参照)
  FisherInfoGaussian.lean      ← 既存 329 行、変更なし (本 plan は import せず)
  AWGN.lean                    ← 既存、変更なし
Common2026.lean                ← `import Common2026.Shannon.EntropyPowerInequality` 追記
```

**新規 import (`EntropyPowerInequality.lean`、CLAUDE.md `Import Policy` 厳守)**:

```lean
import Common2026.Shannon.DifferentialEntropy
import Common2026.Shannon.FisherInfo
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
```

## 依存関係

完了済 / 利用可:

- [x] **Mathlib `Probability.Distributions.Gaussian.Real`** (inventory §A.1):
  `gaussianReal`, `gaussianReal_add_gaussianReal_of_indepFun`,
  `gaussianReal_conv_gaussianReal`
- [x] **Mathlib `Analysis.SpecialFunctions.Exp` / `Log.Basic`**: `Real.exp_pos`,
  `Real.exp_log`, `Real.exp_add`, `Real.log_mul`
- [x] **Mathlib `Probability.Independence.Basic`**: `IndepFun`,
  `IndepFun.map_add_eq_map_conv_map₀'` (内部で convolution lemma が呼び出す)
- [x] **Common2026 E-9 `DifferentialEntropy.lean`**: `differentialEntropy`,
  `differentialEntropy_gaussianReal`
- [x] **Common2026 T2-F `FisherInfo.lean`**: `IsRegularDeBruijnHyp`,
  `deBruijn_identity` (signature 露出のみ、本 plan の本体では呼ばない)

**参考 (import しない / schema のみ参照)**:

- T2-B `ParallelGaussian.lean` (L-WF1+L-WF2+L-PG1 三本立て pass-through 流儀)
- T2-C `ShannonHartley.lean` (L-SH1+L-SH2+L-SH3 三本立て pass-through 流儀)
- T3-D `WynerZiv.lean` / T3-F `RelayCutset.lean` (statement-level publish の
  雛形)

---

## Phase 0 — Mathlib + Common2026 API 在庫 ✅

完了 ([`epi-mathlib-inventory.md`](epi-mathlib-inventory.md))。

主結論:

- **Mathlib に EPI / Stam inequality / 関連 entropy power は完全不在**
  (`loogle "EntropyPower"` で unknown identifier)。本 plan は hypothesis
  pass-through 形でしか着地できない。
- **`gaussianReal_add_gaussianReal_of_indepFun` (Mathlib :624)** が
  独立 Gaussian sum の law を rigorous に与える ⇒ Gaussian saturation case は
  撤退ラインなしで discharge 可能。
- **T2-F `IsRegularDeBruijnHyp` を本 plan で再利用** — name 露出のみ
  (signature レベル predicate として L-EPI2 が直接参照しなくとも、上流 plan
  との bridge を docstring で確保)。
- **`fisherInfo` の値表 (representative-dependence flaw、`= 1/v` for Gaussian
  が成立しない)** に踏み込まないため、本 plan signature には `fisherInfo` を
  露出させない。

### Phase 0 で確定する判断 (判断ログ #1〜#5)

inventory §H と同じ:

- [x] **判断 #1**: de Bruijn 経路採用 (vs Brunn-Minkowski 経路)。
- [x] **判断 #2**: L-EPI1 + L-EPI2 + L-EPI3 三本立て採用。
- [x] **判断 #3**: Gaussian saturation case は本 plan 内で full discharge。
- [x] **判断 #4**: `fisherInfo` の値表に踏み込まない。
- [x] **判断 #5**: `entropyPower μ := Real.exp (2 * differentialEntropy μ)` 形採用
  (Cover-Thomas `(2πe)⁻¹ · e^{2h}` 形は scaling corollary)。

---

## Phase A — `entropyPower` 定義 + Gaussian closed form 📋

### スコープ

`Common2026/Shannon/EntropyPowerInequality.lean` 新規作成 (Phase A 部分 ~80-120 行)。

- skeleton write (全主定理 `:= by sorry`)
- `entropyPower` / `entropyPowerMeasure` 定義
- `entropyPower_pos`, `entropyPower_eq_exp_two_differentialEntropy`
- `entropyPower_gaussianReal` (closed form via `differentialEntropy_gaussianReal`)

### Done 条件

- `Common2026/Shannon/EntropyPowerInequality.lean` 新規作成 (skeleton)
- Phase A 0 sorry (Phase B/C/D/E は `:= by sorry` 残し OK だが ASAP discharge)
- `lake env lean Common2026/Shannon/EntropyPowerInequality.lean` clean

### ステップ

- [ ] **A-0 skeleton write** (`EntropyPowerInequality.lean` 全主定理 + 補助補題を
  `:= by sorry` で並べる、inventory §G の skeleton ~70 行を base)。imports は
  §依存関係 のリストのみ。

- [ ] **A-1 `entropyPower` 定義** (~10 行):
  ```lean
  /-- **Entropy power** `N̄(μ) := exp (2 h(μ))`. Cover-Thomas の `N(μ) = (2πe)⁻¹ ·
  exp (2 h(μ))` と係数差のみ、本 file は `exp (2 h(μ))` 直書きで採用。 -/
  noncomputable def entropyPower (μ : Measure ℝ) : ℝ :=
    Real.exp (2 * differentialEntropy μ)
  ```

- [ ] **A-2 `entropyPower_pos`** (~3 行):
  ```lean
  theorem entropyPower_pos (μ : Measure ℝ) : 0 < entropyPower μ :=
    Real.exp_pos _
  ```

- [ ] **A-3 `entropyPower_gaussianReal`** (~10-15 行): Use
  `differentialEntropy_gaussianReal` + `Real.exp_log` + positivity.
  ```lean
  theorem entropyPower_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
      entropyPower (gaussianReal m v) = 2 * Real.pi * Real.exp 1 * v := by
    unfold entropyPower
    rw [differentialEntropy_gaussianReal m hv]
    -- exp (2 * ((1/2) * log (2πe v))) = exp (log (2πe v)) = 2πe v
    rw [show (2 : ℝ) * ((1/2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ)))
        = Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ)) by ring]
    have h_pos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * v := by positivity
    exact Real.exp_log h_pos
  ```

---

## Phase B — L-EPI1 + L-EPI2 + L-EPI3 predicates 📋

### スコープ

`EntropyPowerInequality.lean` の Phase B 部分 (~80-100 行)。

- `IsStamInequalityHypothesis` (L-EPI1) predicate
- `IsDeBruijnIntegrationHypothesis` (L-EPI2) predicate
- `IsEntropyPowerInequalityHypothesis` (L-EPI3) predicate

### Done 条件

- 3 predicates 0 sorry (`Prop` 定義のみなので proof body なし)
- docstring で discharge plan へのリンク

### ステップ

- [ ] **B-1 L-EPI1 `IsStamInequalityHypothesis`** (~15-25 行):
  ```lean
  /-- **L-EPI1 (Stam inequality hypothesis)**: Stam の `1/J(X+Y) ≥ 1/J(X) + 1/J(Y)`
  を hypothesis 化。主定理 signature 露出のみ、本体未使用。

  Cover-Thomas Lemma 17.7.2 (Stam) を Mathlib 整備が無い段階で扱うため、本
  predicate は **真偽そのものを内容に含めず**、`Prop := True` placeholder と
  する。Discharge plan `epi-stam-discharge-plan.md` で真の Stam inequality
  predicate に置き換える想定。 -/
  def IsStamInequalityHypothesis {Ω : Type*} [MeasurableSpace Ω]
      (X Y : Ω → ℝ) (P : Measure Ω) : Prop := True
  ```

- [ ] **B-2 L-EPI2 `IsDeBruijnIntegrationHypothesis`** (~15-25 行):
  ```lean
  /-- **L-EPI2 (de Bruijn integration hypothesis)**: heat-flow path `X+√t Z`
  の `t ∈ [0, ∞)` 上での EPI integration identity を hypothesis 化。

  主定理 signature 露出のみ、本体未使用。Discharge plan
  `epi-debruijn-integration-plan.md` で T2-F `IsRegularDeBruijnHyp` 適用形に
  展開する想定。 -/
  def IsDeBruijnIntegrationHypothesis {Ω : Type*} [MeasurableSpace Ω]
      (X Y : Ω → ℝ) (P : Measure Ω) : Prop := True
  ```

- [ ] **B-3 L-EPI3 `IsEntropyPowerInequalityHypothesis`** (~20-40 行, 核心):
  ```lean
  /-- **L-EPI3 (EPI conclusion hypothesis、核心 retreat)**: EPI 結論
  `exp(2 h(X+Y)) ≥ exp(2 h(X)) + exp(2 h(Y))` を直接 hypothesis 化。

  主定理本体はこの 1 本で `:= h_epi` で着地。Discharge plan
  `epi-stam-to-conclusion-plan.md` で L-EPI1 + L-EPI2 経路から導出する想定。 -/
  def IsEntropyPowerInequalityHypothesis {Ω : Type*} [MeasurableSpace Ω]
      (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y)
  ```

---

## Phase C — 主定理 `entropy_power_inequality` 📋

### スコープ

`EntropyPowerInequality.lean` の Phase C 部分 (~30-50 行)。

- `entropy_power_inequality` (L-EPI1 + L-EPI2 + L-EPI3 適用形)
- `entropy_power_inequality_real_form` (Cover-Thomas signature の真の形、
  `Real.exp (2 * ...)` を unfold した形)

### Done 条件

- 主定理 0 sorry / 0 warning
- `lake env lean ...` clean

### ステップ

- [ ] **C-1 主定理 `entropy_power_inequality`** (~30-50 行):
  ```lean
  theorem entropy_power_inequality {Ω : Type*} {mΩ : MeasurableSpace Ω}
      (P : Measure Ω) [IsProbabilityMeasure P]
      (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
      (hXY : IndepFun X Y P)
      (_h_stam : IsStamInequalityHypothesis X Y P)
      (_h_debruijn : IsDeBruijnIntegrationHypothesis X Y P)
      (h_epi : IsEntropyPowerInequalityHypothesis X Y P) :
      entropyPower (P.map (fun ω => X ω + Y ω))
        ≥ entropyPower (P.map X) + entropyPower (P.map Y) :=
    h_epi
  ```

- [ ] **C-2 主定理 real-form** (`Real.exp` 展開形, signature 露出のため、~20-30 行):
  ```lean
  theorem entropy_power_inequality_exp_form
      ...
      (h_epi : IsEntropyPowerInequalityHypothesis X Y P) :
      Real.exp (2 * differentialEntropy (P.map (fun ω => X ω + Y ω)))
        ≥ Real.exp (2 * differentialEntropy (P.map X))
          + Real.exp (2 * differentialEntropy (P.map Y)) := by
    have := entropy_power_inequality P X Y hX hY hXY h_stam h_debruijn h_epi
    simpa [entropyPower] using this
  ```

---

## Phase D — Gaussian saturation case (FULL DISCHARGE) 📋

### スコープ

`EntropyPowerInequality.lean` の Phase D 部分 (~50-80 行)。

- `entropy_power_inequality_gaussian_saturation` (X, Y それぞれ Gaussian なら
  EPI は等号成立、Mathlib + Common2026 既存 API のみで full discharge)

### Done 条件

- Gaussian saturation case 0 sorry / 0 warning
- 撤退ラインを使わない (Mathlib `gaussianReal_add_gaussianReal_of_indepFun` +
  Common2026 `differentialEntropy_gaussianReal` で完結)

### ステップ

- [ ] **D-1 `entropy_power_inequality_gaussian_saturation`** (~50-80 行):
  ```lean
  /-- **Gaussian saturation case**: X, Y それぞれ独立 Gaussian なら EPI は
  等号成立 `exp(2 h(X+Y)) = exp(2 h(X)) + exp(2 h(Y))`.

  Mathlib `gaussianReal_add_gaussianReal_of_indepFun` (sum is Gaussian) +
  Common2026 `differentialEntropy_gaussianReal` (closed form `(1/2) log(2πe v)`)
  の合成で full discharge (撤退ラインなし)。 -/
  theorem entropy_power_inequality_gaussian_saturation
      {Ω : Type*} {mΩ : MeasurableSpace Ω}
      (P : Measure Ω) [IsProbabilityMeasure P]
      (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
      (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
      (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
      entropyPower (P.map (fun ω => X ω + Y ω))
        = entropyPower (P.map X) + entropyPower (P.map Y) := by
    -- Step 1: (X+Y).law = gaussianReal (m₁+m₂) (v₁+v₂)
    have h_sum : P.map (fun ω => X ω + Y ω) = gaussianReal (m₁ + m₂) (v₁ + v₂) := by
      have := gaussianReal_add_gaussianReal_of_indepFun hXY hLawX hLawY
      simpa [Pi.add_apply, Function.add_def] using this
    -- Step 2: entropyPower (gaussianReal m v) = 2πe v (from A-3)
    rw [hLawX, hLawY, h_sum]
    rw [entropyPower_gaussianReal m₁ hv₁, entropyPower_gaussianReal m₂ hv₂]
    rw [entropyPower_gaussianReal (m₁+m₂) (by
      -- (v₁ + v₂) ≠ 0 from hv₁ ≠ 0
      simp [hv₁]; intro h; exact hv₁ (by simpa using h))]
    -- Step 3: 2πe (v₁ + v₂) = 2πe v₁ + 2πe v₂
    push_cast
    ring
  ```

---

## Phase E — 補助 corollary 群 📋

### スコープ

`EntropyPowerInequality.lean` の Phase E 部分 (~100-200 行)。

- `entropyPower_nonneg`: `0 ≤ entropyPower μ` (trivial from positivity)
- `entropyPower_scaling`: `entropyPower (μ.map (· * c)) = entropyPower μ * c²`
  (`differentialEntropy_map_mul_const` 経由)
- `entropyPower_translation`: `entropyPower (μ.map (· + a)) = entropyPower μ`
- `entropy_power_inequality_log_form`: log 形 (`h(X+Y) ≥ (1/2) log(N(X) + N(Y))`)
- (任意 stretch) multi-arg version (`Fin n` indexed, n-fold EPI)

### Done 条件

- 各 corollary 0 sorry / 0 warning

### ステップ

- [ ] **E-1 `entropyPower_nonneg`** (~3 行): `(entropyPower_pos μ).le`
- [ ] **E-2 `entropyPower_translation`** (~10 行): `differentialEntropy_map_add_const` 経由
- [ ] **E-3 `entropyPower_scaling`** (~15-25 行): `differentialEntropy_map_mul_const` 経由
- [ ] **E-4 `entropy_power_inequality_log_form`** (~30-50 行): EPI signature の log 形
- [ ] **E-5 (任意) 3-arg pass-through** (~30-50 行)

---

## Phase V — verify + Common2026.lean 編入 📋

### スコープ

- `lake env lean Common2026/Shannon/EntropyPowerInequality.lean` clean (0 errors
  / 0 sorry / 警告最小限) を確認
- `Common2026.lean` への `import Common2026.Shannon.EntropyPowerInequality` 追記
- `docs/textbook-roadmap.md` Ch.17 行のステータス更新 (T2-D 完了マーク)
- `docs/moonshot-seeds.md` 冒頭 Status ブロックに本 seed の成果を append

### Done 条件

- `lake env lean Common2026/Shannon/EntropyPowerInequality.lean` clean
- `Common2026.lean` import 行追加
- roadmap / seeds 更新

---

## 撤退ライン

### L-EPI1 (Stam inequality hypothesis)

- **形**: `IsStamInequalityHypothesis X Y P : Prop := True` (placeholder)
- **適用**: 主定理 signature の `_h_stam` 引数
- **discharge plan**: 別 plan `epi-stam-discharge-plan.md` (Stam の inverse
  Fisher info inequality discharge、~500-1000 行)
- **理由**: Mathlib 不在、Fisher convolution + score variance argument
  が本 plan scope 外
- **緩和策**: L-EPI1 単独では本体に影響なし (signature 露出のみ)、本体は
  L-EPI3 単独で済む。`True` placeholder 形で signature は保持 (将来の
  discharge plan で真の predicate に置換)

### L-EPI2 (de Bruijn integration hypothesis)

- **形**: `IsDeBruijnIntegrationHypothesis X Y P : Prop := True` (placeholder)
- **適用**: 主定理 signature の `_h_debruijn` 引数
- **discharge plan**: 別 plan `epi-debruijn-integration-plan.md` (T2-F
  `IsRegularDeBruijnHyp` を `[0, ∞)` 上で積分、~300-500 行)
- **理由**: 1-parameter ODE 積分 + heat flow boundary value 解析が
  本 plan scope 外 (T2-F の publish も statement-level pass-through なので、
  本 plan で本格的に組むには T2-F の本体 discharge が前提)
- **緩和策**: L-EPI1 と同じ、signature 露出のみ。`True` placeholder 形

### L-EPI3 (EPI conclusion hypothesis、核心)

- **形**: `IsEntropyPowerInequalityHypothesis X Y P := exp(2 h(X+Y)) ≥ exp(2 h(X))
  + exp(2 h(Y))`
- **適用**: 主定理 signature の `h_epi` 引数 — **主定理本体はこの 1 本で終わる**
- **discharge plan**: L-EPI1 + L-EPI2 を組み合わせる別 plan
  `epi-stam-to-conclusion-plan.md` (~200-300 行)
- **理由**: 本 plan の核心。L-EPI3 採用で主定理本体が `:= h_epi` で済む
- **緩和策**: なし (核心 retreat、これを採用しないと本 plan は publish 不可)

---

## Risk Table

| # | リスク | 確率 | 影響 | 緩和策 |
|---|---|---|---|---|
| 1 | `entropyPower` 命名衝突 (Mathlib に同名識別子) | 低 | namespace 衝突 | Mathlib 確認済 (`loogle "EntropyPower"` で unknown)、`InformationTheory.Shannon.EntropyPowerInequality` namespace で定義 |
| 2 | Gaussian saturation case の `Real.exp_log` 引数 vs `Real.log_pos` の取り回しで詰まる | 低 | corollary 規模 +20-30 行 | `2πe v > 0` の positivity を `by positivity` で組む、`v ≠ 0` 仮定を渡す |
| 3 | `IndepFun` 形の `X + Y` vs `fun ω => X ω + Y ω` 形不一致 | 中 | minor compile error | `Pi.add_apply` / `Function.add_def` で正規化 |
| 4 | `IsEntropyPowerInequalityHypothesis` の signature が universe-polymorphic で型ずれ | 低 | minor | `{Ω : Type*}` で統一、`[mΩ : MeasurableSpace Ω]` は明示 |
| 5 | Mathlib `gaussianReal_add_gaussianReal_of_indepFun` の returns `P.map (X + Y)` vs `P.map (fun ω => X ω + Y ω)` 表記 | 中 | Phase D 規模 +10-20 行 | `Pi.add_def` で正規化、または `simpa` で吸収 |
| 6 | `v₁ + v₂ : ℝ≥0` の `≠ 0` 推論で躓く | 低 | minor | `hv₁ : v₁ ≠ 0` から `v₁ + v₂ ≠ 0` を `add_pos`-like lemma で導出 |
| 7 | L-EPI3 を渡せば主定理は `:= h_epi` で通るはずだが、signature に `hX`, `hY`, `hXY` 等の余剰引数が rigid に整合しないリスク | 低 | signature 微修正 | Phase C 着手時に `linter.unusedVariables false` 設定 |

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **判断 #1 (Phase 0)**: de Bruijn 経路採用 (vs Brunn-Minkowski 経路)。理由:
   T2-F `IsRegularDeBruijnHyp` + `deBruijn_identity` の上流接続が既に
   signature 露出形で publish 済、Brunn-Minkowski は T2-E seed として独立扱い。
2. **判断 #2 (Phase 0)**: L-EPI1 + L-EPI2 + L-EPI3 三本立て採用。
   Cover-Thomas Theorem 17.7.3 の **textbook 完全形** (Stam + de Bruijn +
   integration) を signature 露出。本体は L-EPI3 単独で済む (`:= h_epi`) が、
   L-EPI1 + L-EPI2 を discharge plan への bridge として signature に残す。
3. **判断 #3 (Phase 0)**: Gaussian saturation case **(L-EPI0 候補)** は **本 plan
   内で full discharge** (`gaussianReal_add_gaussianReal_of_indepFun` +
   `differentialEntropy_gaussianReal` + `Real.exp_log` 合成で ~50-80 行)。
   撤退ラインに含めない。
4. **判断 #4 (Phase 0)**: `fisherInfo` の値表 (representative-dependence flaw あり)
   には踏み込まない。本 plan の主定理 signature は `entropyPower` 形のみで
   `fisherInfo` を露出させない (L-EPI3 形が値依存しないため不要)。
5. **判断 #5 (Phase 0)**: `entropyPower` の定義は **`Real.exp (2 *
   differentialEntropy μ)`** 形を採用 (Cover-Thomas Ch.17 の
   `N(X) = (2πe)⁻¹ · e^{2h(X)}` ではなく `e^{2h(X)}` 形)。係数 `(2πe)` の
   付け替えは corollary で扱える。
