# EPI 無条件化 — entropyPower 再型付け Phase 0-A/0-C Mathlib API 在庫

> 親計画: [`docs/shannon/epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md)。本ファイルは **Phase 0-A (新定義 shape 確定) + 0-C (API 在庫指示)** の先行調査成果物。read-only 調査、コード未編集。
>
> 在庫日: 2026-06-05。全 lemma は loogle 完全 namespace 検索 → 実 Mathlib file Read で verbatim 確認済。

## 一行サマリ

**Phase 0-A/0-C で使う coercion / 分解 API は実体 100% 既存。最大不確実点だった「a.c. 判定の definitional 化」は GO — Mathlib `klDiv` 自身が `open Classical in` + `if μ ≪ ν then ... else ...` を採用しており、同じパターンで `entropyPower` を case-split 定義できる。さらに `EReal.exp : EReal → ℝ≥0∞` (`exp ⊥ = 0`、`exp ↑x = ENNReal.ofReal (Real.exp x)`、`exp_monotone` [gcongr]) が存在し、親計画が「`Real.exp` の ℝ≥0∞ 版は不在」としていた前提は半分覆る。自作必要は 0 個 (定義本体 + ~6 bridge lemma の plumbing のみ)。撤退ライン L-Uncond-0-α は発動しない。**

---

## 主定理の最終形 (親計画 §1 再掲)

```lean
-- 独立可測 X Y : Ω → ℝ に対し、新 entropyPower : Measure ℝ → ℝ≥0∞ 下で
theorem entropy_power_inequality_unconditional
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hindep : IndepFun X Y P) :
    entropyPower (P.map (X + Y))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y)
```

本 inventory が確定するのは **その下の 2 つの新定義** (`differentialEntropyExt` / 新 `entropyPower`) と coercion bridge。新定義 shape の pseudo-Lean:

```lean
-- (a) Real workhorse は温存 (DifferentialEntropy.lean:45、不変)
--     differentialEntropy (μ : Measure ℝ) : ℝ := ∫ x, negMulLog ((μ.rnDeriv volume x).toReal) ∂volume

-- (b1) EReal 上位レイヤ: 特異で ⊥、a.c. で coe(workhorse)
open Classical in
noncomputable def differentialEntropyExt (μ : Measure ℝ) : EReal :=
  if μ ≪ volume then (differentialEntropy μ : EReal) else ⊥

-- (b2) entropyPower: EReal.exp で coercion 不要に畳む (特異 ⊥ → exp ⊥ = 0、a.c. → ofReal(exp(2h)))
noncomputable def entropyPower (μ : Measure ℝ) : ℝ≥0∞ :=
  EReal.exp (2 * differentialEntropyExt μ)
```

---

## API 在庫テーブル

### A. Lebesgue 分解 / a.c. 判定の definitional 化

| 概念 | Mathlib API | file:line | 状態 | Phase 0 での扱い |
|---|---|---|---|---|
| 絶対連続 `≪` | `MeasureTheory.Measure.AbsolutelyContinuous` (`μ ≪ ν`) | `Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean` | ✅ | case-split の述語 |
| **`Decidable (μ ≪ ν)`** | — | — | ❌ **不在** (loogle: `Decidable, MeasureTheory.Measure.AbsolutelyContinuous` = **Found 0**) | `open Classical in` で `Classical.propDecidable` 供給 (下記precedent) |
| **case-split def precedent** | `klDiv` = `open Classical in` + `irreducible_def` + `if μ ≪ ν ∧ ... then ... else ∞` | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:55-59` | ✅ **既存パターン** | **L-Uncond-0-α を解消する決定的 precedent**。downstream は `klDiv_eq_*` 展開 lemma 経由で reasoning、`rfl`/`simp` on `if` を踏まない |
| 特異 ⟺ singularPart 自身 | `singularPart_eq_self : μ.singularPart ν = μ ↔ μ ⟂ₘ ν` | `Mathlib/.../Decomposition/Lebesgue.lean:325` | ✅ (HLD instance **不要**、body 内で `h.haveLebesgueDecomposition` derive) | 非分岐版の特異判定 |
| a.c. ⟺ singularPart=0 | `singularPart_eq_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] : μ.singularPart ν = 0 ↔ μ ≪ ν` | `Mathlib/.../Decomposition/Lebesgue.lean:266` | ✅ (要 `[μ.HaveLebesgueDecomposition ν]`) | a.c. 判定の代替表現 |
| 特異 ⟹ rnDeriv =ᵐ 0 | `rnDeriv_eq_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] : μ.rnDeriv ν =ᵐ[ν] 0 ↔ μ ⟂ₘ ν` | `Mathlib/.../Decomposition/Lebesgue.lean:288` | ✅ (要 `[μ.HaveLebesgueDecomposition ν]`) | workhorse が特異で 0 を返すことの根拠 (既に `differentialEntropy_dirac` で使用) |
| a.c. ⟹ singularPart=0 | `singularPart_eq_zero_of_ac (h : μ ≪ ν) : μ.singularPart ν = 0` | `Mathlib/.../Decomposition/Lebesgue.lean:252` | ✅ (HLD instance **不要**) | a.c. 枝の補助 |
| **HLD instance (自動発火)** | `haveLebesgueDecomposition_of_sigmaFinite [SFinite μ] [SigmaFinite ν] : HaveLebesgueDecomposition μ ν` (priority 100 instance) | `Mathlib/.../Decomposition/Lebesgue.lean:948-949` | ✅ **instance** | `μ : Measure ℝ` `[IsProbabilityMeasure μ]` ⟹ SFinite、`volume` は SigmaFinite ⟹ `μ.HaveLebesgueDecomposition volume` が **自動 resolve**。上記 `[μ.HaveLebesgueDecomposition ν]` 前提は確率測度 on ℝ で常に満たされる |
| Lebesgue 分解等式 | `haveLebesgueDecomposition_add μ ν` / `singularPart_add_rnDeriv` | `Mathlib/.../Decomposition/Lebesgue.lean` | ✅ | bridge lemma で a.c. 値一致を示すとき |
| `Measure.rnDeriv` / `singularPart` / `withDensity` | (総関数、Decidable 不要) | `Mathlib/.../Decomposition/Lebesgue.lean` | ✅ | 既存 workhorse が依存済 |

### B. exp の ℝ≥0∞ / EReal 在庫 (親計画前提の再確認 — 一部覆る)

| 概念 | Mathlib API | file:line | 状態 | Phase 0 での扱い |
|---|---|---|---|---|
| `Real.exp` の EReal 版 | — | — | ❌ 不在 (loogle: `Real.exp, EReal` = **Found 0 declarations mentioning EReal and Real.exp**) | 親計画通り |
| `ENNReal.exp` | — | — | ❌ 不在 (loogle: `ENNReal.exp` = **unknown identifier 'ENNReal.exp'**) | 親計画通り |
| `ENNReal.ofReal_exp` | — | — | ❌ 不在 (rg: ofReal_exp = 0 hits) | 専用 lemma なし。`EReal.exp_coe` で代替 |
| **`EReal.exp : EReal → ℝ≥0∞`** | `def exp (x : EReal) : ℝ≥0∞ := EReal.rec 0 (fun x => ENNReal.ofReal (Real.exp x)) ∞ x` | `Mathlib/Analysis/SpecialFunctions/Log/ERealExp.lean:39-40` | ✅ **既存 (親計画が見落とし)** | **新 entropyPower の正規ルート**。`exp ⊥ = 0`、`exp ↑x = ofReal(exp x)` を 1 関数で供給 |
| `EReal.exp_bot` | `@[simp] lemma exp_bot : exp ⊥ = 0 := rfl` | `ERealExp.lean:42` | ✅ | 特異 → entropyPower=0 (Dirac sanity) |
| `EReal.exp_zero` | `@[simp] lemma exp_zero : exp 0 = 1` | `ERealExp.lean:43` | ✅ | — |
| `EReal.exp_coe` | `@[simp] lemma exp_coe (x : ℝ) : exp x = ENNReal.ofReal (Real.exp x) := rfl` | `ERealExp.lean:45` | ✅ | a.c. 枝で `ofReal(exp(2h))` 形を取り出す bridge |
| `EReal.exp_monotone` | `@[gcongr] lemma exp_monotone : Monotone exp := exp_strictMono.monotone` | `ERealExp.lean:71-72` | ✅ | EPI 不等式を `gcongr` で持ち上げ |
| `EReal.exp_strictMono` | `@[gcongr] lemma exp_strictMono : StrictMono exp` | `ERealExp.lean:58-59` | ✅ | 厳密単調 (Gaussian saturation) |
| `EReal.exp_le_exp_iff` | `@[simp] lemma exp_le_exp_iff {a b : EReal} : exp a ≤ exp b ↔ a ≤ b` | `ERealExp.lean:84` | ✅ | 不等式の往復 |
| `EReal.exp_add` | `lemma exp_add (x y : EReal) : exp (x + y) = exp x * exp y` | `ERealExp.lean:109` | ✅ | (今回直接は不要、参考) |

### C. EReal ↔ ℝ ↔ ℝ≥0∞ coercion 在庫

| 概念 | Mathlib API | file:line | 状態 | Phase 0 での扱い |
|---|---|---|---|---|
| `EReal.toENNReal` (def) | `noncomputable def toENNReal (x : EReal) : ℝ≥0∞ := if x = ⊤ then ⊤ else ENNReal.ofReal x.toReal` | `Mathlib/Data/EReal/Basic.lean:695-697` | ✅ | (EReal.exp 採用なら toENNReal 経路は不要だが、`differentialEntropyExt` から直接畳む代替案で使用) |
| `EReal.toENNReal_bot` | `lemma toENNReal_bot : (⊥ : EReal).toENNReal = 0` | `Mathlib/Data/EReal/Basic.lean:719` | ✅ | 特異 ⊥ → 0 (代替案) |
| `EReal.toENNReal_of_ne_top` | `@[simp] lemma toENNReal_of_ne_top {x : EReal} (hx : x ≠ ⊤) : x.toENNReal = ENNReal.ofReal x.toReal` | `Mathlib/Data/EReal/Basic.lean:702` | ✅ | a.c. 枝 coerce |
| `EReal.toENNReal_coe` | `@[simp] lemma toENNReal_coe {x : ℝ≥0∞} : (x : EReal).toENNReal = x` | `Mathlib/Data/EReal/Basic.lean:748` | ✅ | round-trip |
| `EReal.real_coe_toENNReal` | `@[simp] lemma real_coe_toENNReal (x : ℝ) : (x : EReal).toENNReal = ENNReal.ofReal x := rfl` | `Mathlib/Data/EReal/Basic.lean:754` | ✅ | ℝ → ℝ≥0∞ 直結 |
| `EReal.toENNReal_le_toENNReal` | `lemma toENNReal_le_toENNReal {x y : EReal} (h : x ≤ y) : x.toENNReal ≤ y.toENNReal` | `Mathlib/Data/EReal/Basic.lean:766` | ✅ | 単調性 (代替案で不等式持ち上げ) |
| `EReal.toENNReal_lt_toENNReal` | `lemma toENNReal_lt_toENNReal {x y : EReal} (hx : 0 ≤ x) (hxy : x < y) : x.toENNReal < y.toENNReal` | `Mathlib/Data/EReal/Basic.lean:775` | ✅ | 厳密単調 |
| `EReal.coe_add` | `theorem coe_add (x y : ℝ) : (↑(x + y) : EReal) = x + y := rfl` | `Mathlib/Data/EReal/Basic.lean:301` | ✅ | a.c.+a.c. 和保存 |
| `EReal.add_bot` | `@[simp] theorem add_bot (x : EReal) : x + ⊥ = ⊥` | `Mathlib/Data/EReal/Operations.lean:47` | ✅ | ⚠ 和を取ると ⊥ が吸収 (下記 box 参照) |
| `EReal.bot_add` | `@[simp] theorem bot_add (x : EReal) : ⊥ + x = ⊥` | `Mathlib/Data/EReal/Operations.lean:51` | ✅ | 同上 |
| `ENNReal.ofReal_add` | `theorem ofReal_add {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) : ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q` | `Mathlib/Data/ENNReal/Real.lean:52` | ✅ (**両 nonneg 前提 verbatim**) | RHS `N(X)+N(Y)` を a.c.+a.c. で 1 つの ofReal に畳む |
| `ENNReal.ofReal_le_ofReal` | `theorem ofReal_le_ofReal {p q : ℝ} (h : p ≤ q) : ENNReal.ofReal p ≤ ENNReal.ofReal q` | `Mathlib/Data/ENNReal/Real.lean:137` | ✅ | a.c. EPI を Real から ℝ≥0∞ に coerce |

### D. 既存 InformationTheory 側 (温存 / 整合確認)

| 概念 | 定義/値 | file:line | 状態 | Phase 0 での扱い |
|---|---|---|---|---|
| Real workhorse | `differentialEntropy (μ : Measure ℝ) : ℝ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume` | `InformationTheory/Shannon/DifferentialEntropy.lean:45` | ✅ 温存 (不変) | (a) 層、a.c. 枝で coerce 元 |
| 旧 entropyPower (Real) | `entropyPower (μ : Measure ℝ) : ℝ := Real.exp (2 * differentialEntropy μ)` | `InformationTheory/Shannon/EntropyPowerInequality.lean:101` | ⚠ 衝突 | 新 ℝ≥0∞ 版に置換 or `entropyPowerReal` 退避 (L-Uncond-1-β) |
| Dirac workhorse値 | `differentialEntropy_dirac (m) : differentialEntropy (Measure.dirac m) = 0` | `InformationTheory/Shannon/DifferentialEntropy.lean:155` | ✅ verbatim 確認 | **退化トラップ源**: workhorse は Dirac で **0** (∵ rnDeriv=ᵐ0、negMulLog 0 = 0)。旧 entropyPower = exp 0 = 1 (誤)。新 `differentialEntropyExt (dirac m) = ⊥` ⟹ `entropyPower = exp ⊥ = 0` (正) |
| Gaussian saturation | `entropyPower_gaussianReal (m) {v} (hv : v ≠ 0) : entropyPower (gaussianReal m v) = 2πe·v` | `InformationTheory/Shannon/EntropyPowerInequality.lean` (§A) | ✅ | 新定義でも a.c. 枝 ⟹ 非ゼロ非自明値 (L-Uncond-0-γ sanity gate) |

---

## 主要前提条件ボックス

- **`singularPart_eq_zero` / `rnDeriv_eq_zero` / `withDensity_rnDeriv_eq_zero`** はいずれも `[μ.HaveLebesgueDecomposition ν]` を要求する。**EPI 設定では自動充足**: `μ : Measure ℝ`、`[IsProbabilityMeasure μ]` ⟹ `IsFiniteMeasure` ⟹ `SFinite`、`volume : Measure ℝ` は `SigmaFinite` (Haar)。よって `haveLebesgueDecomposition_of_sigmaFinite` (priority 100 instance, Lebesgue.lean:948) が `μ.HaveLebesgueDecomposition volume` を自動供給。**ただし `P.map (X+Y)` 等の pushforward 測度が `SFinite` であることは別途確認要** (probability measure の map は probability measure なので OK、`Measure.map` of IsProbabilityMeasure with measurable → IsProbabilityMeasure)。
- **`singularPart_eq_self` (Lebesgue.lean:325) は HLD instance を要求しない** — body 内で `h.haveLebesgueDecomposition` を derive する。非分岐の特異判定が要るときはこちらが軽い。
- **`ENNReal.ofReal_add` は両引数 nonneg を要求** (`hp : 0 ≤ p`、`hq : 0 ≤ q` verbatim)。`exp(2h)` は常に `> 0` なので a.c.+a.c. case では自動充足。`EReal.exp` 経路なら `ENNReal.mul`/`add` が直接効くので `ofReal_add` を経由しない選択も可。
- **`EReal.add_bot` / `bot_add` で ⊥ が和を吸収** (⚠ 設計上重要): `differentialEntropyExt` を「両方 ⊥ なら ⊥、片方 ⊥ なら ⊥」と素朴に EReal 上で足すと、混合 case (X a.c. ∧ Y 特異) で `h(X)+⊥ = ⊥ → entropyPower = 0` となり **RHS が `N(X)+0=N(X)` でなく 0 に潰れる**。これは差分形 RHS を **`entropyPower X + entropyPower Y` (ℝ≥0∞ 上の和)** で取れば回避できる (`exp ⊥ = 0` を先に各項で評価してから ℝ≥0∞ で足す)。**RHS は EReal 上で `h(X)+h(Y)` を足してから exp するのでなく、各 entropyPower を ℝ≥0∞ で足す** — 新 `entropyPower : Measure ℝ → ℝ≥0∞` 単項定義ならこの事故は自動回避 (主定理 RHS が `entropyPower (P.map X) + entropyPower (P.map Y)` で ℝ≥0∞ 加算)。

---

## 自作が必要な要素 (優先度順)

Mathlib 不在の primitive は **0 個**。自作は新定義本体 + bridge plumbing のみ:

1. **`differentialEntropyExt : Measure ℝ → EReal`** (def 本体) — `open Classical in` + `if μ ≪ volume then (differentialEntropy μ : EReal) else ⊥`。工数: ~3 行。落とし穴: `irreducible_def` にして downstream の意図しない unfold を防ぐ (`klDiv` 同様)。
2. **新 `entropyPower : Measure ℝ → ℝ≥0∞`** (def 本体) — `EReal.exp (2 * differentialEntropyExt μ)`。工数: ~2 行。`2 * ⊥ = ⊥` (EReal: `EReal.mul` の bot 挙動を verbatim 確認要 — 0 ≤ 2 なので `⊥` 保存のはずだが Phase 1 で `EReal.mul_bot`/`bot_mul` 系を確認すること)。
3. **`entropyPower_eq_ofReal_of_ac : μ ≪ volume → entropyPower μ = ENNReal.ofReal (Real.exp (2 * differentialEntropy μ))`** — bridge。`unfold` + `if_pos` + `EReal.exp_coe` + `EReal.coe_mul`/`coe_ofNat`。工数: ~6 行。
4. **`entropyPower_singular : ¬(μ ≪ volume) → entropyPower μ = 0`** — bridge。`unfold` + `if_neg` + `EReal.exp_bot` (`2 * ⊥ = ⊥` 経由)。工数: ~5 行。
5. **`entropyPower_dirac : entropyPower (Measure.dirac m) = 0`** (sanity) — `mutuallySingular_dirac` ⟹ `¬ dirac ≪ volume` ⟹ (4)。工数: ~4 行。
6. **`entropyPower_gaussianReal` 再証明** (新定義版、非自明値 sanity) — `gaussianReal m v ≪ volume` ⟹ (3) ⟹ 旧 `entropyPower_gaussianReal` の Real 値を `ENNReal.ofReal` でラップ。工数: ~8 行。

**工数感**: 定義 2 本 + bridge 4-6 本 = 計 ~30-40 行。Fano Phase 3 の `condEntropy` 自作 (~150 行) よりずっと軽い。最大の plumbing リスクは「`EReal.mul` の bot/coe 挙動」(`2 * ⊥`、`(2:EReal) * ↑x = ↑(2*x)`) の細部だが、これは Phase 1 着手時に `EReal.coe_mul` / `EReal.mul_bot` を 2 query 追加すれば潰せる。

---

## Mathlib 壁の列挙

**真の Mathlib 不在 (`@residual(wall:...)` 対象) は 0 個。** 親計画が壁と見ていた 3 点はいずれも回避可能:

- **(W-C) ⊥ → entropyPower=0 の coercion 整合** → 壁ではない。`EReal.exp` (`ERealExp.lean:39`) が `exp ⊥ = 0` を `rfl` で供給。`Real.exp` の ℝ≥0∞ 版不在 (loogle `Real.exp, EReal` = **Found 0**、`ENNReal.exp` = **unknown identifier**) は事実だが、`EReal.exp` が代替を完備するので壁にならない。
- **a.c. 判定の definitional 化** → 壁ではない。`Decidable (μ ≪ ν)` = **Found 0** だが、`klDiv` (Basic.lean:55-58) が `open Classical in` + `if μ ≪ ν then` で既に実運用しており、同パターンで GO。
- **(W-B) 混合 case `N(X+Y) ≥ N(X)`** → 本 inventory のスコープ外 (Phase 3/4 の数学的中身)。Phase 0-A/0-C の定義 shape には壁なし。

「Real.exp ℝ≥0∞ 版不在」は **wall ではなく単なる API 形の選択** (`EReal.exp` で迂回)。shared sorry 補題化は不要。

---

## 撤退ラインへの距離

親計画 Phase 0 の撤退ライン (§Phase 0 撤退ライン):

- **L-Uncond-0-α** (case-split に `Decidable (μ ≪ volume)` が要り classical instance で組むと downstream simp/rfl 全滅 → EReal 一本化に縮退):
  → **発動しない。** `klDiv` precedent (Basic.lean:55) が「`open Classical in` + `irreducible_def` + `if μ ≪ ν then`」で downstream を `klDiv_eq_*` 展開 lemma 経由 reasoning に閉じ込めており、`rfl`/`simp` on `if` を踏まない設計が確立済。同じ `irreducible_def` 化で `entropyPower` も保護できる。**縮退不要、case-split 定義で着地可。**
- **L-Uncond-0-γ** (退化定義悪用の自己監査 — 特異で ⊥/0 を返す設計が vacuous 達成に見えうる):
  → **設計として健全。** 特異測度のエントロピーパワーが真に 0 なのは正しい値。LHS が常に 0 に潰れる定義ミスは Gaussian sanity (`entropyPower (gaussianReal m v) = 2πe·v ≠ 0`、上記自作要素 6) で gate。退化定義悪用には**当たらない**。混合 case の ⊥ 吸収事故 (上記 box) だけ注意 — RHS を ℝ≥0∞ 加算で取れば自動回避。

**新規撤退ライン提案** (Phase 1 着手時の gate):

- **L-Uncond-0-δ (新規)**: `EReal.mul` の bot/coe 挙動 (`2 * ⊥ = ⊥`、`(2:EReal) * ↑x = ↑(2x)`) が想定外 (例: `0 * ⊥ = 0` 規約で `2 * ⊥` が `⊥` にならない等) で `entropyPower_singular` bridge が組めない場合 → `entropyPower := if μ ≪ volume then ENNReal.ofReal (Real.exp (2*differentialEntropy μ)) else 0` の **直接 case-split 定義** (EReal.exp を経由しない) に切替。これは EReal 算術を完全に回避し、`if_pos`/`if_neg` + `ENNReal.ofReal` のみで bridge が組める。撤退口は該当 bridge を `sorry` + `@residual(plan:epi-entropypower-retype-plan)` で抜く (仮説束化禁止)。

---

## 着手 skeleton (S1: epi-entropypower-retype-plan 向け)

`InformationTheory/Shannon/EntropyPowerExt.lean` (新規、~30 行 skeleton):

```lean
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Data.EReal.Basic

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal

/-- 拡張微分エントロピー: 特異測度で `⊥`、`μ ≪ volume` で Real workhorse を coerce。 -/
open Classical in
noncomputable irreducible_def differentialEntropyExt (μ : Measure ℝ) : EReal :=
  if μ ≪ volume then (differentialEntropy μ : EReal) else ⊥

/-- 拡張エントロピーパワー (ℝ≥0∞): 特異で `0`、a.c. で `ofReal (exp (2h))`。
`EReal.exp` が `exp ⊥ = 0` / `exp ↑x = ofReal (exp x)` を 1 関数で供給。 -/
noncomputable def entropyPowerExt (μ : Measure ℝ) : ℝ≥0∞ :=
  EReal.exp (2 * differentialEntropyExt μ)

theorem entropyPowerExt_eq_ofReal_of_ac {μ : Measure ℝ} (h : μ ≪ volume) :
    entropyPowerExt μ = ENNReal.ofReal (Real.exp (2 * differentialEntropy μ)) := by
  sorry -- @residual(plan:epi-entropypower-retype-plan)

theorem entropyPowerExt_singular {μ : Measure ℝ} (h : ¬ μ ≪ volume) :
    entropyPowerExt μ = 0 := by
  sorry -- @residual(plan:epi-entropypower-retype-plan)

theorem entropyPowerExt_dirac (m : ℝ) : entropyPowerExt (Measure.dirac m) = 0 := by
  sorry -- @residual(plan:epi-entropypower-retype-plan)

end InformationTheory.Shannon
```

---

## まとめ (Phase 0-A/0-C 結論)

- **新定義 shape 確定**: (b1) `differentialEntropyExt : Measure ℝ → EReal` = `open Classical in if μ ≪ volume then ↑(differentialEntropy μ) else ⊥`、(b2) `entropyPowerExt : Measure ℝ → ℝ≥0∞` = `EReal.exp (2 * differentialEntropyExt μ)`。**case-split 案で GO**、EReal 一本化への縮退は不要。
- **最大不確実点 (a.c. 判定の definitional 化) = 解決**: `klDiv` precedent で確立済。`Decidable (μ ≪ volume)` 不在は `open Classical in` で回避、`irreducible_def` で downstream simp/rfl 汚染を防ぐ。
- **親計画の前提誤り 1 件訂正**: 「`Real.exp` の ℝ≥0∞ 版は Mathlib 不在ゆえ素朴に exp で定義できない」→ `EReal.exp : EReal → ℝ≥0∞` (`ERealExp.lean:39`) が存在し、`exp ⊥ = 0` / `exp_coe` / `exp_monotone` [gcongr] を完備。素朴な `EReal.exp (2 * h)` で定義可能。
- **自作 0 wall / bridge ~6 本 (~30-40 行)** / **撤退ライン発動 no**。
- **要 Phase 1 追加確認 (本 inventory のスコープ外)**: `EReal.mul` の `2 * ⊥` / `(2:EReal) * ↑x` 挙動 (L-Uncond-0-δ gate)、`P.map (X+Y)` の SFinite instance 解決。
