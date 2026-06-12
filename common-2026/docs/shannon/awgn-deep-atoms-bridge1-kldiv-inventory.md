# AWGN deep-atoms bridge ① 在庫: `klDiv` n-fold 同一視 + RN-deriv change-of-measure

> 親 plan: [`awgn-achievability-walls-discharge-plan.md`](awgn-achievability-walls-discharge-plan.md)。
> settled-facts: [`awgn-facts.md`](awgn-facts.md)（M0 で `klDiv_pi_eq_sum` 等の前提クラスを確認済、本 inventory はその逐語再録 + 拡張）。
> 本ファイルは **API 在庫のみ**。コードは編集しない。inventory file の編集境界は `docs/shannon/*-inventory.md` のみ。

## 一行サマリ

**bridge ① 「`klDiv(J_n,Q_n) = n·klDiv(J₁,Q₁) = n·I`」と「RN-deriv tensorize + setLIntegral change-of-measure」で必要な API のうち、A 系（klDiv 分解・map 不変・per-letter 閉形式・積分表現）は ~90% が既存（Mathlib もしくは in-project に逐語確認済）、唯一 A4 の「`klDiv(J₁,Q₁).toReal → (1/2)log(1+P/N)` 橋」だけ achievability ⇄ converse 接続 lemma が不在（self-build ~40-70 行、plumbing）。B 系（RN-deriv tensorize）は 2-項 prod 版（`rnDeriv_compProd`）は既存だが n-fold `Measure.pi` 版が不在（self-build ~30-50 行、plumbing）、setLIntegral change-of-measure（B2）と AC（B3）は完全既存。** genuine Mathlib gap は **ゼロ**（全て plumbing / 配線）。

---

## 対象 deep atoms（再掲）

- **atom (b)** = `continuousAepGaussian_holds` の (iii) change-of-measure sorry（`Walls.lean:244`、`@residual(plan:awgn-achievability-walls-discharge-plan)`）。証明 sketch（`Walls.lean:235-243`）:
  ```
  -- A 上で ∑φ > n(J₁[φ] − δ)、tensorized dJ/dQ = exp(∑φ) から
  -- Q(A) = ∫_A exp(−∑φ) dJ ≤ exp(−n(J₁[φ]−δ))·J(A) ≤ exp(−(klDiv_n − n·3δ))
  -- J₁[φ] = (klDiv J₁ Q₁).toReal、klDiv_n = n·klDiv(J₁,Q₁)
  ```
- **atom (c)/(e)** = `awgn_random_coding_union_bound` の N₀ sorry（`AchievabilityDischarge.lean:540`）+ term2。`hslack : R + 3δ < (1/2)log(1+P/N)` から margin `g = I − R − 3δ > 0` を得るのに **`klDiv(J₁,Q₁).toReal = (1/2)log(1+P/N)` の閉形式（= A4）** が要る。

両 atom が共有する bridge ① = 「per-letter `klDiv(J₁,Q₁)` を (i) n-fold へ持ち上げ (A2/A3)、(ii) 閉形式 `(1/2)log(1+P/N)` に同定 (A4)、(iii) `J₁[φ] = klDiv.toReal` の積分表現 (A5)、(iv) RN-deriv tensorize + change-of-measure (B1/B2/B3)」。

### J₁ / Q₁ / φ の定義（`Walls.lean:146-153` 逐語）

```lean
set μX := gaussianReal 0 P.toNNReal       -- 入力 X
set μZ := gaussianReal 0 N                 -- noise Z
set μY := gaussianReal 0 (P.toNNReal + N)  -- 出力 Y = X+Z の周辺
set J₁ : Measure (ℝ × ℝ) := (μX.prod μZ).map (fun p => (p.1, p.1 + p.2))  -- joint (X, X+Z)
set Q₁ : Measure (ℝ × ℝ) := μX.prod μY                                    -- product of marginals
set φ  : ℝ × ℝ → ℝ := fun p => Real.log ((J₁.rnDeriv Q₁ p).toReal)       -- = llr J₁ Q₁
```

---

## A1. `klDiv` の特定 + 規約

`continuousAepGaussian_holds` の signature 中の `klDiv` は `open InformationTheory`（`Walls.lean:52`）で解決される **`InformationTheory.klDiv`**（`Mathlib.InformationTheory.KullbackLeibler.Basic`）。in-project ラッパでなく Mathlib 本体。

| 項目 | 内容（逐語） | file:line |
|---|---|---|
| 定義 | `noncomputable irreducible_def klDiv (μ ν : Measure α) : ℝ≥0∞ := if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ) else ∞` | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57` |
| 値域 | `ℝ≥0∞`（**not ℝ / EReal**）。`.toReal` で実数に落とす | — |
| **μ ⊀ ν の規約** | `klDiv μ ν = ∞`（`@[simp] lemma klDiv_of_not_ac (h : ¬ μ ≪ ν) : klDiv μ ν = ∞`） | `:68` |
| ¬Integrable の規約 | `klDiv μ ν = ∞`（`@[simp] lemma klDiv_of_not_integrable`） | `:73` |
| `Integrable (llr)` 条項 | **あり**（`if` の第 2 連言）。`klDiv_ne_top` は `(hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : klDiv μ ν ≠ ∞` | `:103` |
| `llr` 定義（逐語） | `noncomputable def llr (μ ν : Measure α) (x : α) : ℝ := log (μ.rnDeriv ν x).toReal` | `Mathlib/MeasureTheory/Measure/LogLikelihoodRatio.lean:37` |

**規約上の含意（退化境界）**: 退化 `J₁ ⊀ Q₁`（`P=0` で X が Dirac、density が破れる）のときは `klDiv = ∞`、`φ = log(rnDeriv) = 0` a.e.（sketch のコメント `Walls.lean:161` と整合）。本 line の precondition（`P > 0` / `hN`）で非退化が保証され `J₁ ≪ Q₁` が成立する（B3）。**`φ = llr J₁ Q₁`**（`hφ_def` と `llr` 定義が `Real.log ∘ toReal ∘ rnDeriv` で逐語一致）。

---

## A2. map-invariance（reshape を `klDiv` に通す）

| 概念 | API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| `klDiv` の `MeasurableEquiv` 不変性 | **in-project** `InformationTheory.Shannon.klDiv_map_measurableEquiv` | `InformationTheory/Shannon/MutualInfo.lean:54` | ✅ 既存（in-project、sorryAx-free） | J_n=(pi J₁).map e / Q_n=(pi Q₁).map e の reshape を klDiv に通す本命 |
| `Measure.pi` の map（reshape） | `MeasureTheory.Measure.pi_map_pi` | `Mathlib/MeasureTheory/Constructions/Pi.lean:390` | ✅ 既存 | `(pi μ).map (fun x i => f i (x i)) = pi (fun i => (μ i).map (f i))`。`Walls.lean:221` で既に使用 |
| reshape equiv | `MeasurableEquiv.arrowProdEquivProdArrow` + `measurePreserving_arrowProdEquivProdArrow` | （in-project、`Walls.lean:210` で使用済） | ✅ 既存 | `(Fin n → ℝ × ℝ) ≃ᵐ (Fin n → ℝ) × (Fin n → ℝ)` |

**`klDiv_map_measurableEquiv` 逐語 signature**（`[...]` 含む）:
```lean
theorem klDiv_map_measurableEquiv {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν
```
- 引数順: explicit `(e : α ≃ᵐ β) (μ ν : Measure α)`、instance `[MeasurableSpace α] [MeasurableSpace β] [IsFiniteMeasure μ] [IsFiniteMeasure ν]`。
- 結論形（逐語）: `klDiv (μ.map e) (ν.map e) = klDiv μ ν`。
- **前提クラス事故注意**: `[IsFiniteMeasure μ] [IsFiniteMeasure ν]`（probability measure ⊆ finite なので J₁/Q₁ で自動充足）。
- **`pi_map_pi` 逐語**: 引数 instance に **`[hμ : ∀ i, SigmaFinite ((μ i).map (f i))]`** + 引数 `(hf : ∀ i, AEMeasurable (f i) (μ i))`、結論 `(Measure.pi μ).map (fun x i ↦ (f i (x i))) = Measure.pi (fun i ↦ (μ i).map (f i))`。

> **判定（A2）**: 既存。`klDiv` reshape の bridge は self-build 不要。Mathlib 不在（`klDiv_map_*` は Mathlib に 0 件、loogle `MeasureTheory.Measure.map _ _ , InformationTheory.klDiv` → `Found 0`）だが、**in-project に既にある**ので新規不要。

---

## A3. n-fold 分解（`klDiv_n = ∑ᵢ klDiv(J₁,Q₁) = n·klDiv(J₁,Q₁)`）

| 概念 | API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| `Measure.pi` の klDiv 加法性 | `InformationTheory.Shannon.klDiv_pi_eq_sum` | `InformationTheory/Shannon/MIChainRule.lean:249` | ✅ 既存（sorryAx-free、`#print axioms` = std） | **n-fold 分解の本命**。M0 で前提クラス確認済 |
| `prod` の klDiv 加法性 | `InformationTheory.Shannon.klDiv_prod_eq_add` | `MIChainRule.lean:230` | ✅ 既存（sorryAx-free） | 2-項版。pi 版の induction step で内部利用 |
| `∑const → n·` 圧縮 | `Finset.sum_const` + `Finset.card_univ` / `Fin.sum_const` / `nsmul_eq_mul` | （Mathlib 標準） | ✅ 既存 | i.i.d. 特殊化 `∑ i : Fin n, c = n • c = (n:ℝ)·c` |

**`klDiv_pi_eq_sum` 逐語 signature**（M0 確定の逐語再録）:
```lean
theorem klDiv_pi_eq_sum
    {n : ℕ} {α' : Fin n → Type*} [∀ i, MeasurableSpace (α' i)]
    (μs νs : ∀ i, Measure (α' i))
    [∀ i, IsProbabilityMeasure (μs i)] [∀ i, IsProbabilityMeasure (νs i)] :
    klDiv (Measure.pi μs) (Measure.pi νs) = ∑ i : Fin n, klDiv (μs i) (νs i)
```
- 引数順: implicit `{n} {α'}`、instance `[∀ i, MeasurableSpace (α' i)]`、explicit `(μs νs : ∀ i, Measure (α' i))`、instance `[∀ i, IsProbabilityMeasure (μs i)] [∀ i, IsProbabilityMeasure (νs i)]`。
- 結論形（逐語）: `klDiv (Measure.pi μs) (Measure.pi νs) = ∑ i : Fin n, klDiv (μs i) (νs i)`。
- **前提クラス（M0 逐語確認、事故注意）**: **`IsProbabilityMeasure` のみ**（`SigmaFinite` / `IsFiniteMeasure` 不要）。J₁/Q₁ は `IsProbabilityMeasure`（`Walls.lean:154-158` で `haveI` 済）なので i.i.d. 特殊化で充足。

**`klDiv_prod_eq_add` 逐語 signature**:
```lean
theorem klDiv_prod_eq_add
    {α' β' : Type*} [MeasurableSpace α'] [MeasurableSpace β']
    (μ₁ μ₂ : Measure α') [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (ν₁ ν₂ : Measure β') [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    klDiv (μ₁.prod ν₁) (μ₂.prod ν₂) = klDiv μ₁ μ₂ + klDiv ν₁ ν₂
```
- **前提クラス**: 全 4 measure `[IsProbabilityMeasure]`（M0 確認、`SigmaFinite` 不要）。

**i.i.d. 特殊化 1 行**: J_n / Q_n は `arrowProdEquivProdArrow` reshape 後 `Measure.pi (fun _ : Fin n => J₁)` / `Measure.pi (fun _ => Q₁)`。よって
```lean
klDiv_pi_eq_sum (fun _ => J₁) (fun _ => Q₁)  -- = ∑ i : Fin n, klDiv J₁ Q₁
  |>.trans (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])
-- = (n:ℝ) • klDiv J₁ Q₁ (ENNReal smul) → toReal で n * (klDiv J₁ Q₁).toReal
```
（reshape `klDiv (pi J₁).map e = klDiv (pi J₁)` は A2 の `klDiv_map_measurableEquiv` で剥がす。これは `Walls.lean:206-225` の `hJ_eq` reshape と逆向きに対応。）

> **判定（A3）**: 既存（in-project）。n-fold 分解は self-build 不要。最短 chain = `klDiv_map_measurableEquiv`（reshape 剥がし）→ `klDiv_pi_eq_sum`（pi 加法）→ `Finset.sum_const`（i.i.d. 圧縮）。

---

## A4. per-letter 閉形式（`klDiv(J₁,Q₁).toReal = (1/2)log(1+P/N)`）— **最大の plumbing**

| 概念 | API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| AWGN per-letter MI 閉形式 | `InformationTheory.Shannon.AWGN.mutualInfoOfChannel_gaussianInput_closed_form'` | `InformationTheory/Shannon/AWGN/MIClosedForm.lean:46` | ✅ 既存（0 sorry、transitively genuine） | **閉形式の出口**。ただし `mutualInfoOfChannel` 形 |
| `mutualInfoOfChannel` 定義 | `noncomputable def mutualInfoOfChannel (p : Measure α) (W : Channel α β) : ℝ≥0∞ := klDiv (jointDistribution p W) (p.prod (outputDistribution p W))` | `InformationTheory/Shannon/ChannelCoding/Basic.lean:85` | ✅ 既存 | `klDiv(joint, product)` 形 ← bridge の繋ぎ先 |
| `mutualInfo` 定義 | `noncomputable def mutualInfo (μ) (Xs) (Yo) := klDiv (μ.map (fun ω => (Xs ω, Yo ω))) ((μ.map Xs).prod (μ.map Yo))` | `InformationTheory/Shannon/MutualInfo.lean:37` | ✅ 既存 | 同型の別表現 |

**`mutualInfoOfChannel_gaussianInput_closed_form'` 逐語 signature**:
```lean
theorem mutualInfoOfChannel_gaussianInput_closed_form'
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N) :
    (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
        (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal
      = (1/2) * Real.log (1 + P / (N : ℝ))
```
- **前提（事故注意）**: `(hP : 0 < P)`（退化 `P=0` を排除、Q₁ ≪ J₁ の AC を保つ）+ `(hN : (N : ℝ) ≠ 0)`（`N=0` を排除、klDiv 閉形式の `hv₂≠0`）+ `(h_meas : IsAwgnChannelMeasurable N)`。**`hslack` の `(1/2)log(1+P/N)` と RHS が逐語一致**（margin `g = I−R−3δ` の I）。

**gap（bridge の核）**: 閉形式は `mutualInfoOfChannel (gaussianReal 0 P') (awgnChannel N)` 形で、bridge ① が要るのは `klDiv(J₁, Q₁)`（J₁ = `(μX.prod μZ).map (p↦(p.1,p.1+p.2))`, Q₁ = `μX.prod μY`）。両者の同一視
```
klDiv J₁ Q₁ = mutualInfoOfChannel (gaussianReal 0 P') (awgnChannel N)
```
を示す in-project lemma は **不在**（rg で AWGN 配下に `J₁ = jointDistribution` 系のヒット 0）。必要なのは:
1. `jointDistribution (gaussianReal 0 P') (awgnChannel N) = J₁`（= `(μX.prod μZ).map (p↦(p.1,p.1+p.2))`）。`awgnChannel` が「`x ↦ gaussianReal x N` を `+x` で押す」kernel なら、`jointDistribution = p ⊗ₘ W` の reshape が J₁ に一致するはず（要 `awgnChannel` / `jointDistribution` の定義 Read）。
2. `outputDistribution (gaussianReal 0 P') (awgnChannel N) = μY`（= `gaussianReal 0 (P'+N)`）。これは AWGN output gaussian（`IsAwgnOutputGaussian`、converse 側で genuine 確立済、`MIClosedForm.lean:54`）。
3. `p.prod (outputDistribution …) = μX.prod μY = Q₁`。

**finiteness `klDiv(J₁,Q₁) ≠ ⊤` の取り方**: `mutualInfoOfChannel` 閉形式が `.toReal` 等式を与えており、RHS が有限 ⇒ `klDiv ≠ ⊤` は `klDiv_ne_top`（A1）で別取り、または `toReal` 等式の成立自体から（`toReal ⊤ = 0 ≠ (1/2)log(1+P/N)` の対偶で）`≠ ⊤` を導出。最も安全なのは `J₁ ≪ Q₁`（B3）+ `Integrable (llr J₁ Q₁) J₁`（= `hφ_memLp` から L²⊆L¹）で `klDiv_ne_top` を直接適用。

> **判定（A4）**: **閉形式の数値は既存（`(1/2)log(1+P/N)`、逐語一致）だが、achievability の `klDiv(J₁,Q₁)` ⇄ converse の `mutualInfoOfChannel` 同一視 lemma が不在**。self-build ~40-70 行（plumbing、genuine gap でない）。詳細 → gap 表 G-1。

---

## A5. 積分表現（`J₁[φ] = (klDiv J₁ Q₁).toReal`）

| 概念 | API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| `klDiv.toReal` の積分表現 | `InformationTheory.toReal_klDiv` | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:157` | ✅ 既存 | **本命**。`φ = llr J₁ Q₁` の積分 = klDiv.toReal |
| univ-合致版 | `InformationTheory.toReal_klDiv_of_measure_eq` | `:164` | ✅ 既存 | probability measure で `μ univ = ν univ = 1` なので補正項消去 |
| klFun 積分版 | `InformationTheory.toReal_klDiv_eq_integral_klFun` | `:170` | ✅ 既存 | 代替表現 |

**`toReal_klDiv` 逐語 signature**:
```lean
lemma toReal_klDiv (h : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ + ν.real univ - μ.real univ
```
- 引数順: explicit `(h : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)`。
- 結論形（逐語）: `(klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ + ν.real univ - μ.real univ`。
- **前提（事故注意）**: section variable `[IsFiniteMeasure μ] [IsFiniteMeasure ν]`（`:146`）+ `h : μ ≪ ν` + `h_int : Integrable (llr μ ν) μ`。

**補正項の消去**: J₁/Q₁ は probability measure なので `Q₁.real univ = 1 = J₁.real univ`、`ν.real univ - μ.real univ = 0`。よって
```
J₁[φ] = ∫ a, llr J₁ Q₁ a ∂J₁ = ∫ a, φ a ∂J₁ = (klDiv J₁ Q₁).toReal  -- 補正項消去後
```
（`φ = llr J₁ Q₁` は A1 で逐語一致確認済。）`toReal_klDiv_of_measure_eq (h) (h_eq : μ univ = ν univ)` を使うと補正項を自動消去できてより直接。

> **判定（A5）**: 既存（Mathlib）。`J₁[φ] = klDiv.toReal` は `toReal_klDiv` 1 本 + probability-measure 補正項消去で閉じる。前提 `J₁ ≪ Q₁`（B3）+ `Integrable (llr) J₁`（= `hφ_memLp` L²⊆L¹）が必要。

---

## B1. RN-deriv tensorization（`dJ/dQ = exp(∑φ)` の核）

| 概念 | API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| **prod (2-項) の rnDeriv** | `ProbabilityTheory.rnDeriv_compProd` | `Mathlib/Probability/Kernel/Composition/RadonNikodym.lean:107` | ✅ 既存 | prod = compProd const なので 2-項 J₁/Q₁ の per-letter rnDeriv に使える |
| compProd-left の rnDeriv | `ProbabilityTheory.rnDeriv_measure_compProd_left` | `:92` | ✅ 既存 | `(μ⊗ₘκ).rnDeriv(ν⊗ₘκ) =ᵐ μ.rnDeriv ν ∘ fst` |
| **n-fold `Measure.pi` の rnDeriv** | — | — | ❌ **不在** | loogle `rnDeriv (pi _) (pi _)` → `Found 0`。self-build 要（G-2） |

**`rnDeriv_compProd` 逐語 signature**:
```lean
lemma rnDeriv_compProd [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) (ν : Measure α) [IsFiniteMeasure ν] :
    (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η]
      (fun p ↦ μ.rnDeriv ν p.1 * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p)
```
- **前提（事故注意）**: `[IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure ν]` + `(h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η)`。

**`rnDeriv_measure_compProd_left` 逐語**:
```lean
lemma rnDeriv_measure_compProd_left (μ ν : Measure α) (κ : Kernel α β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] :
    (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ) =ᵐ[ν ⊗ₘ κ] fun p ↦ (μ.rnDeriv ν) p.1
```

**n-fold 不在の評価**: loogle `MeasureTheory.Measure.rnDeriv (Measure.pi _) (Measure.pi _)` → `Found 0`（必要条件）。結論形 2 段階: `rnDeriv (compProd _ _) (compProd _ _)` → 7 件ヒット（`rnDeriv_compProd` 系、prod は compProd const）だが **`Measure.pi` を直接 factorize する rnDeriv 補題はゼロ**。**ただし atom (b) の change-of-measure は J/Q が既に `(pi …).prod (pi …)` を `.map g` した 2-項 prod 構造**なので、n-fold pi の rnDeriv を陽に求める必要は薄い: `setLIntegral_rnDeriv`（B2）で `Q(A) = ∫_A (J.rnDeriv Q) dQ` でなく **`Q(A) = ∫_A exp(−φ_total) dJ`** を経由する。φ_total = ∑φ は `llr J Q`（n-fold）であり、`klDiv_pi_eq_sum` の積分版（`integral_rnDeriv` 系）で `∑ llr` に分解される。最短 self-build template → G-2。

> **判定（B1）**: 2-項版（`rnDeriv_compProd`）既存。n-fold `Measure.pi` 版は不在だが、**change-of-measure を `setLIntegral_rnDeriv`（B2）+ `lintegral_rnDeriv_mul` 経由で書けば n-fold rnDeriv の陽な tensorize は回避可能**（plumbing、G-2 参照）。genuine gap でない。

---

## B2. setLIntegral change-of-measure（`Q(A) = ∫_A (J.rnDeriv Q) dQ` / `∫_A exp(−φ) dJ`）

| 概念 | API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| **set-restricted rnDeriv 積分** | `MeasureTheory.Measure.setLIntegral_rnDeriv` | `Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean:333` | ✅ 既存 | **本命**。`∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s` |
| 全空間版 | `MeasureTheory.Measure.lintegral_rnDeriv` | `:338` | ✅ 既存 | `∫⁻ x, μ.rnDeriv ν x ∂ν = μ univ` |
| **rnDeriv 掛け算 change-of-measure** | `MeasureTheory.lintegral_rnDeriv_mul` | `:566` | ✅ 既存 | `∫⁻ x, μ.rnDeriv ν x * f x ∂ν = ∫⁻ x, f x ∂μ`。**逆向き（∂J→∂Q）の本命** |
| withDensity 経由 | `MeasureTheory.withDensity_apply` | `Mathlib/MeasureTheory/Measure/WithDensity.lean:45` | ✅ 既存 | `μ.withDensity f s = ∫⁻ a in s, f a ∂μ` |
| rnDeriv の withDensity 同定 | `MeasureTheory.Measure.withDensity_rnDeriv_eq` | `Decomposition/RadonNikodym.lean`（loogle 確認） | ✅ 既存 | `setLIntegral_rnDeriv` が内部利用 |

**`setLIntegral_rnDeriv` 逐語 signature**:
```lean
lemma setLIntegral_rnDeriv [HaveLebesgueDecomposition μ ν] [SFinite ν]
    (hμν : μ ≪ ν) (s : Set α) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s
```
- **前提（事故注意）**: `[HaveLebesgueDecomposition μ ν] [SFinite ν]` + `(hμν : μ ≪ ν)`。probability measure は `SFinite`、`HaveLebesgueDecomposition` は finite measure で自動。

**`lintegral_rnDeriv_mul` 逐語 signature**（atom (b) の `Q(A) = ∫_A exp(−φ) dJ` 向きに直結）:
```lean
theorem lintegral_rnDeriv_mul [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) : ∫⁻ x, μ.rnDeriv ν x * f x ∂ν = ∫⁻ x, f x ∂μ
```
- **前提**: `[HaveLebesgueDecomposition μ ν]` + `(hμν : μ ≪ ν)` + `(hf : AEMeasurable f ν)`。
- **使い方**: `μ := J`, `ν := Q`, `f := 𝟙_A`（or `exp(−φ)·𝟙_A`）で `∫⁻ x, (J.rnDeriv Q) * f ∂Q = ∫⁻ f ∂J`。`J.rnDeriv Q = exp(φ)` なので逆向き `Q(A) = ∫_A exp(−φ) dJ` を得る（`rnDeriv_inv` / `rnDeriv` 相互逆で）。

> **判定（B2）**: 完全既存。change-of-measure の核（`setLIntegral_rnDeriv` / `lintegral_rnDeriv_mul`）は Mathlib に揃う。self-build 不要。

---

## B3. 絶対連続性（`J₁ ≪ Q₁` / non-degeneracy）

| 概念 | API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| gaussianReal ≪ volume | `ProbabilityTheory.gaussianReal_absolutelyContinuous` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:228` | ✅ 既存 | 非退化 Gaussian の AC |
| volume ≪ gaussianReal | `ProbabilityTheory.gaussianReal_absolutelyContinuous'` | `:233` | ✅ 既存 | 逆向き（両側 AC） |
| **prod の AC 合成** | `MeasureTheory.Measure.AbsolutelyContinuous.prod` | `Mathlib/MeasureTheory/Measure/Prod.lean:415` | ✅ 既存 | `μ ≪ μ' → ν ≪ ν' → μ.prod ν ≪ μ'.prod ν'` |
| **map 経由の AC** | `MeasureTheory.Measure.AbsolutelyContinuous.map` | `Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean:88` | ✅ 既存 | `μ ≪ ν → μ.map f ≪ ν.map f` |
| pi の AC 合成 | — | — | ❌ 不在 | loogle `AC (pi _) (pi _)` → `Found 0`。ただし bridge は 2-項 prod 構造で pi-AC 不要 |

**`AbsolutelyContinuous.prod` 逐語 signature**:
```lean
theorem AbsolutelyContinuous.prod [SFinite ν'] (h1 : μ ≪ μ') (h2 : ν ≪ ν') :
    μ.prod ν ≪ μ'.prod ν'
```
- **前提（事故注意）**: `[SFinite ν']`（右第 2 因子のみ）+ `(h1 : μ ≪ μ') (h2 : ν ≪ ν')`。`omit [SFinite ν]` 注記あり（`:414`）。

**`AbsolutelyContinuous.map` 逐語 signature**:
```lean
protected theorem map (h : μ ≪ ν) {f : α → β} (hf : Measurable f) : μ.map f ≪ ν.map f
```
- **前提**: `(h : μ ≪ ν) (hf : Measurable f)`。`@[gcongr, mono]`。

**`gaussianReal_absolutelyContinuous` 逐語 signature**:
```lean
lemma gaussianReal_absolutelyContinuous (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal μ v ≪ volume
```
- **前提（事故注意）**: `(hv : v ≠ 0)`（**退化分散排除**）。`P=0`（μX のみ）で破れるが本 line では `P > 0`。`N=0` で μZ/μY が破れるが `hN` で排除。

**`J₁ ≪ Q₁` の取り方（chain）**: J₁ = `(μX.prod μZ).map h₁`、Q₁ = `μX.prod μY`。
1. 各 1-D の両側 AC（`gaussianReal_absolutelyContinuous` / `'`）で `μX.prod μZ ≪ volume.prod volume` 等を確立。
2. AWGN map `h₁ = (p ↦ (p.1, p.1+p.2))` は volume-preserving な線形変換（shear、det=1）なので `J₁ ≪ Q₁` は density 比 `f_Z(y−x)/f_Y(y)`（f_X 相殺、facts.md:92-94 の MemLp insight と同じ構造）が有限 ⇒ AC。**直接 self-build より、A4 の `klDiv_ne_top` 経由（閉形式が有限 ⇒ `J₁ ≪ Q₁ ∧ Integrable`、`klDiv_ne_top_iff` の mpr 逆）で取る方が安い**。

> **判定（B3）**: 完全既存（1-D Gaussian AC + prod/map AC 合成）。pi-AC は不在だが bridge では 2-項構造ゆえ不要。`J₁ ≪ Q₁` は A4 閉形式の有限性から `klDiv_ne_top_iff` 逆で間接取得が最安。

---

## 重要 precondition box（事故が起きやすい前提の集約）

- **`klDiv_pi_eq_sum` / `klDiv_prod_eq_add`（A3）**: 全 measure `[IsProbabilityMeasure]` 必須（`SigmaFinite`/`IsFiniteMeasure` では**ない**、M0 逐語確認）。J₁/Q₁ は `Walls.lean:154-158` で `haveI` 済。
- **`klDiv_map_measurableEquiv`（A2）**: `[IsFiniteMeasure μ] [IsFiniteMeasure ν]`（probability ⊆ finite で自動）。
- **`toReal_klDiv`（A5）**: section `[IsFiniteMeasure μ] [IsFiniteMeasure ν]` + `(μ ≪ ν)` + `Integrable (llr μ ν) μ`。後 2 つは `hφ_memLp`（L²⊆L¹）+ B3 から供給。
- **`mutualInfoOfChannel_gaussianInput_closed_form'`（A4）**: `(0 < P)` + `((N:ℝ) ≠ 0)` + `IsAwgnChannelMeasurable N`。退化 `P=0`/`N=0` を排除。本 line の `awgnPowerWitness_exists` の `0<P'<P` + `hN` で充足。
- **`setLIntegral_rnDeriv` / `lintegral_rnDeriv_mul`（B2）**: `[HaveLebesgueDecomposition μ ν]`（finite で自動）+ `[SFinite ν]`（probability で自動）+ `(μ ≪ ν)`。
- **`AbsolutelyContinuous.prod`（B3）**: `[SFinite ν']`（右第 2 因子のみ）。
- **`gaussianReal_absolutelyContinuous`（B3）**: `(v ≠ 0)`（退化分散排除）。

---

## gap 表（不在資産 + self-build template + blocker 種別）

| gap | 不在資産 | 最も近い既存 template（file:line） | 概算行数 | blocker 種別 | loogle 確認 |
|---|---|---|---|---|---|
| **G-1** | `klDiv(J₁,Q₁) = mutualInfoOfChannel (gaussianReal 0 P') (awgnChannel N)`（achievability ⇄ converse 同一視） | `mutualInfoOfChannel_def`（`ChannelCoding/Basic.lean:88`、`= klDiv (jointDistribution) (p.prod (outputDistribution))`）+ `IsAwgnOutputGaussian`（converse 側 genuine、`MIClosedForm.lean:54`）。`jointDistribution = p ⊗ₘ W` reshape を J₁ に一致させる | ~40-70 | **plumbing**（J₁/Q₁ ⇄ jointDistribution/outputDistribution の defeq 配線。`awgnChannel`/`jointDistribution` の定義 Read 要） | `rg "klDiv.*jointDistribution\|J₁.*jointDistribution" AWGN/` → 0 件（in-project 不在） |
| **G-2** | n-fold `Measure.pi` の rnDeriv tensorize `(pi μ).rnDeriv (pi ν) =ᵐ ∏ᵢ (μ i).rnDeriv (ν i) ∘ eval i` | `rnDeriv_compProd`（`Probability/Kernel/Composition/RadonNikodym.lean:107`、2-項 prod 版）+ `klDiv_pi_eq_sum` 内部 induction（`MIChainRule.lean:249-309`、`piFinSuccAbove` で帰納分解） | ~30-50（陽 tensorize 不要なら ~15、change-of-measure を B2 経由で書く場合） | **plumbing**（atom (b) は 2-項 prod 構造で陽な pi-rnDeriv 回避可能。`setLIntegral_rnDeriv`+`lintegral_rnDeriv_mul` で書けば G-2 自体不要化） | `loogle "MeasureTheory.Measure.rnDeriv (MeasureTheory.Measure.pi _) (MeasureTheory.Measure.pi _)"` → `Found 0`；結論形 `rnDeriv (compProd _ _) (compProd _ _)` → 7 件（pi 直接版なし） |

**genuine Mathlib wall（`@residual(wall:)` 対象）**: **なし**。両 gap は in-project / Mathlib 既存資産の配線（plumbing）であり、命題自体が Mathlib に欠落しているわけではない。**shared sorry 補題への集約は不要**（atom (b)/(c)/(e) は既存 `@residual(plan:awgn-achievability-walls-discharge-plan)` の傘下で、bridge ① の closure は plan 内の deep-atom 解消として進む）。

---

## 撤退ラインとの距離

親 plan `awgn-achievability-walls-discharge-plan.md` の deep-atom 撤退ライン（bridge ① が Mathlib gap で塞がる場合）に対して:

- **触れない / 発動しない**。bridge ① の全構成要素は **既存資産の配線**で、genuine Mathlib gap はゼロ（A1-A5・B1-B3 すべて既存または in-project、不在は G-1/G-2 の 2 plumbing のみ）。
- 最大リスクは **G-1（achievability ⇄ converse の `klDiv ⇄ mutualInfoOfChannel` 同一視）の plumbing 量**（~40-70 行、`awgnChannel`/`jointDistribution` 定義の Read が前提）。これが想定の 1.5 倍に膨れても plan の deep-atom 予算内。
- もし G-1 が `awgnChannel` の kernel 構造の都合で defeq に落ちず大きく膨らんだ場合の **新規 degenerate fallback**: bridge ① を「閉形式 `(1/2)log(1+P/N)` を直接 RHS に置く」のでなく、**`klDiv(J₁,Q₁).toReal > 0` の下界のみ**（`klDiv_eq_zero_iff` の対偶 + 非独立性）で margin `g` を確保する縮退路。これでも `hslack` の `R + 3δ < I` から `g > 0` は出ないため、closure には閉形式が要る → fallback の撤退口は **sorry + `@residual(plan:awgn-achievability-walls-discharge-plan)` 据え置き**（hypothesis bundling 禁止、閉形式を hyp に積まない）。

---

## 着手 skeleton（bridge ① closure の入口）

bridge ① は新規 file でなく既存 2 file の sorry 充填（`Walls.lean:244` / `AchievabilityDischarge.lean:540`）。着手は **共有補題 1 本を新設**して両 atom から呼ぶ形が最短（DRY、A4 の閉形式同一視を 1 箇所に集約）。配置先は両 consumer の共通上流（`Walls.lean` が `AchievabilityDischarge.lean` の上流なので `Walls.lean` 内、または新 file `AWGN/Bridge1KL.lean`）。

```lean
import InformationTheory.Shannon.AWGN.MIClosedForm     -- 閉形式 mutualInfoOfChannel_gaussianInput_closed_form'
import InformationTheory.Shannon.MIChainRule           -- klDiv_pi_eq_sum / klDiv_prod_eq_add
import InformationTheory.Shannon.MutualInfo            -- klDiv_map_measurableEquiv
import Mathlib.InformationTheory.KullbackLeibler.Basic -- toReal_klDiv / klDiv_ne_top
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym -- setLIntegral_rnDeriv / lintegral_rnDeriv_mul

namespace InformationTheory.Shannon.AWGN

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

/-- **bridge ① per-letter 閉形式**: per-letter joint `J₁` と product `Q₁` の KL は
AWGN 容量 `(1/2)log(1+P/N)` に一致。A4 の `mutualInfoOfChannel` 同一視 (G-1) を経由。
@residual(plan:awgn-achievability-walls-discharge-plan) -/
theorem klDiv_perLetter_eq_capacity
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N) :
    (klDiv
        (((gaussianReal 0 P.toNNReal).prod (gaussianReal 0 N)).map
            (fun p : ℝ × ℝ => (p.1, p.1 + p.2)))
        ((gaussianReal 0 P.toNNReal).prod (gaussianReal 0 (P.toNNReal + N)))).toReal
      = (1/2) * Real.log (1 + P / (N : ℝ)) := by
  -- G-1: klDiv J₁ Q₁ = mutualInfoOfChannel (gaussianReal 0 P') (awgnChannel N)
  --   経由で mutualInfoOfChannel_gaussianInput_closed_form' に委譲。
  sorry

/-- **bridge ① n-fold 同一視**: `klDiv_n = n · klDiv(J₁,Q₁) = n · I`。
A2 (reshape 剥がし) + A3 (klDiv_pi_eq_sum + i.i.d. 圧縮)。
@residual(plan:awgn-achievability-walls-discharge-plan) -/
theorem klDiv_nFold_eq_nsmul (P : ℝ) (N : ℝ≥0) {n : ℕ} :
    (klDiv
        (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
            (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
          (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1, fun i => p.1 i + p.2 i)))
        ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
          (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N))))).toReal
      = (n : ℝ) *
        (klDiv
            (((gaussianReal 0 P.toNNReal).prod (gaussianReal 0 N)).map
                (fun p : ℝ × ℝ => (p.1, p.1 + p.2)))
            ((gaussianReal 0 P.toNNReal).prod
              (gaussianReal 0 (P.toNNReal + N)))).toReal := by
  -- A2: arrowProdEquivProdArrow reshape を klDiv_map_measurableEquiv で剥がす
  -- A3: klDiv_pi_eq_sum (fun _ => J₁) (fun _ => Q₁) + Finset.sum_const
  sorry

end InformationTheory.Shannon.AWGN
```

`klDiv_perLetter_eq_capacity`（A4/G-1）→ `klDiv_nFold_eq_nsmul`（A2/A3）の順に割る。両 theorem を `Walls.lean:244` の (iii) と `AchievabilityDischarge.lean:540` の N₀/term2 から呼ぶ。change-of-measure（B1/B2）の `Q(A) = ∫_A exp(−∑φ) dJ` は `lintegral_rnDeriv_mul`（B2）+ A5（`J₁[φ] = klDiv.toReal`）で `Walls.lean:244` 内に直接展開（共有補題化は任意）。
