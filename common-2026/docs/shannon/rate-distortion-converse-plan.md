# Rate-distortion converse (single-shot) ムーンショット計画 🌙

> 実態整合 (2026-06-10): DONE-UNCOND (single-shot) — headline `rate_distortion_converse_single_shot`
> (`InformationTheory/Shannon/RateDistortion/Converse.lean:135`) は DPI + Fano + max-entropy 連鎖の実証明 (0 sorry) で publish、
> 副条件は `hMI_W_finite` (MI 有限性) のみで honest。E-4' `rate_distortion_converse_single_shot_specified`
> (`InformationTheory/Shannon/RateDistortion/ConverseMonotone.lean:68`) +
> `rateDistortionFunction_antitone` (`...ConverseMonotone.lean:39`) も完了。
> 後継 E-4'' (convexity + n-letter): 凸性 `rateDistortionFunction_convexOn`
> (`InformationTheory/Draft/Shannon/RateDistortionConvexity.lean:390`) は **genuine proof done**
> (`rate-distortion-convexity-plan.md`)。n-letter converse は本 plan E-4-C で attack 中
> (Stage 1 `_block` genuine、Stage 2 `_singleLetter` は true-as-framed 化済 + sorry 据置、下記)。

E-4 シードカード ([`docs/moonshot-seeds.md`](../moonshot-seeds.md))。
Cover-Thomas 10.4 — レート歪み関数 `R(D)` を達成可能 rate の下界として定式化する
**single-shot 形** の converse。`𝔼 d(X, X̂) ≤ D ⟹ log M ≥ R(D)` (M = encoder の像)。

E-3 (achievability) は plan-only で並走。R(D) 定義 + distortion 定義は本ファイル
(E-4) が own し、E-3 plan はここを参照する。

## 進捗

- [x] Phase A — definitions ✅
  - [x] **A.1** `expectedDistortion`: 期待歪み `∫ p, d p.1 p.2 ∂ν` (joint measure 上)
  - [x] **A.2** `rateDistortionFunction (P : Measure α) (D : ℝ) : ℝ≥0∞` —
        `iInf` over feasible joint measures of `klDiv ν (prod of marginals)`
- [x] Phase B — basic properties ✅
  - [x] **B.1** `rateDistortionFunction_le_of_feasible`
- [x] Phase C — 単発 converse (主定理) ✅
  - [x] **C.1** `rate_distortion_converse_single_shot`
- [x] **E-4' MVP**: R(D) antitone + specified-distortion form ✅ (2026-05-14、
      `InformationTheory/Shannon/RateDistortionConverseMonotone.lean` 151 行 0 sorry)
  - `rateDistortionFunction_antitone`: `D₁ ≤ D₂ ⟹ R(D₂) ≤ R(D₁)` (feasible set monotone)
  - `rate_distortion_converse_single_shot_specified`: `D̃ ≤ D ⟹ R(D).toReal ≤ log|M|`
    (親 single-shot 形 + monotonicity 合成)
- [x] 後継 `E-4''` 凸性 — R(D) convexity ✅ **genuine proof done** (`rate-distortion-convexity-plan.md`、
      `RateDistortionConvexity.lean:390`、DPI 経路、sorryAx 非依存)
- [🚧] `E-4-C` n-letter chain rule converse — `RateDistortionConverseNLetter.lean`。
      Stage 1 `_block` (`:72`) genuine、Stage 2 `_singleLetter` (`:305`) は true-as-framed 化済
      (hD+hindep 追加) + sorry 据置 (`:328`、`@residual(plan:rate-distortion-converse-plan)`)。
      **残壁 = MI superadditivity `∑I(Xᵢ;X̂ᵢ) ≤ I(X^n;X̂^n)` (独立 source)** (下記 E-4-C)

## 実装完了

**実装ファイル**: [`InformationTheory/Shannon/RateDistortion/Converse.lean`](../../InformationTheory/Shannon/RateDistortion/Converse.lean)

**主要 def + theorem**:
- `expectedDistortion d ν`: 期待歪み (joint 上の積分)
- `rateDistortionFunction d P D`: R(D) 関数 (`iInf` over feasible joints)
- `rateDistortionFunction_le_of_feasible`: feasible point の `iInf_le` 系
- `rate_distortion_converse_single_shot`:
  `(R(D̃)).toReal ≤ Real.log |M|` where `D̃ = ∫ d(X, decoder(encoder X)) ∂μ`

**Mathlib gap**: なし。既存 `InformationTheory/Shannon/` 資産で完結
(`MaxEntropy.entropy_le_log_card` + `Bridge.mutualInfo_eq_entropy_sub_condEntropy` +
`Pi.condEntropy_nonneg` + `DPI.mutualInfo_le_of_postprocess` + `MutualInfo.mutualInfo_comm`).

**0 sorry 達成**: `lake env lean InformationTheory/Shannon/RateDistortionConverse.lean` silent。

## ゴール / Approach

**最終的に証明したい定理** (本 plan scope、E-4 single-shot MVP):

任意の単発 lossy code `(f : α → Fin M, g : Fin M → β)` と確率変数 `X : Ω → α` で、
歪み `D̃ := 𝔼 d(X, g(f(X)))` のとき:
```
Real.log M ≥ (rateDistortionFunction (μ.map X) D̃).toReal
```
ここで `rateDistortionFunction P D := ⨅ ν ∈ feasibleSet P D, mutualInfoOf ν`、
`feasibleSet P D := {ν | ν.map Prod.fst = P ∧ expectedDistortion ν ≤ D}`、
`mutualInfoOf ν := klDiv ν ((ν.map Prod.fst).prod (ν.map Prod.snd))`。

### 全体戦略 (Approach)

**形 (shape)**: single-shot Shannon converse `InformationTheory/Shannon/Converse.lean` の
**rate-distortion 鏡像**。Fano (誤り確率) の代わりに R(D) (期待歪み) で MI を
下から押さえる。chain rule + Jensen 抜きで n=1 まで絞れば 0 sorry が現実的。

**証明 chain**:
```
Real.log M ≥ entropy μ W                    -- entropy_le_log_card (MaxEntropy.lean)
          ≥ (mutualInfo μ X W).toReal       -- I(X; W) = H(W) - H(W|X) ≤ H(W) (condEntropy nonneg)
          ≥ (mutualInfo μ X X̂).toReal       -- DPI: X̂ = decoder ∘ W (mutualInfo_le_of_postprocess)
          ≥ (rateDistortionFunction P_X D̃).toReal
                                            -- iInf ≤ value at the joint ν := μ.map (X, X̂)
```

第 4 ステップが本 plan の **新規部分**。R(D) を `iInf` で定義し、`iInf_le` を
`ν := μ.map (fun ω => (X ω, X̂ ω))` で適用する。**Mathlib-shape-driven**:
`mutualInfo` の定義は既に `klDiv (μ.map (X, Yo)) ((μ.map X).prod (μ.map Yo))` だから、
`mutualInfoOf ν` を `klDiv ν ((ν.map Prod.fst).prod (ν.map Prod.snd))` で定義すれば、
`μ.map (X, X̂)` を入れた瞬間に既存 `mutualInfo μ X X̂` と **書き換え rfl**。
(`μ.map (X, X̂).map Prod.fst = μ.map X` は `Measure.map_map` で簡約)。

**`.toReal` の扱い**: `R(D)` を `ℝ≥0∞` 値で定義 → `iInf_le ≤ mutualInfoOf ν` を ENNReal
レベルで取り、`mutualInfo μ X X̂ ≠ ∞` の前提下で `ENNReal.toReal_mono` で実数下界化。
**有限性は本 plan では仮定**。実 closure (entropy finite ⇒ MI finite) は deferred。

### 退化点 MVP scope (judgment log 1)

n-letter form (`rate ≥ R(D)` 形) は **R(D) convexity (Jensen)** を要し、`R(D)` が
joint distribution の上の凸関数であるという解析的事実は ~1000 行規模の Mathlib gap。
本 plan は **single-shot n=1**、かつ **R(D̃) (実際の期待歪み)** で press 抑え、
`D̃ ≤ D ⟹ R(D̃) ≥ R(D)` (単調性) は **deferred**。

## 既存資産の流用

`InformationTheory/Shannon/` 既存資産 (本 plan が完全流用):

| 資産 | 用途 |
|---|---|
| `MaxEntropy.entropy_le_log_card` | Step 1: `H(W) ≤ log M` |
| `Bridge.mutualInfo_eq_entropy_sub_condEntropy` | Step 2: `I(X; W) = H(W) - H(W|X)` |
| `Fano/Measure.condEntropy_nonneg` | Step 2 plumbing: `H(W|X) ≥ 0` |
| `MutualInfo.mutualInfo_comm` | Step 2: 必要なら左右入れ替え |
| `DPI.mutualInfo_le_of_postprocess` | Step 3: `I(X; X̂) ≤ I(X; W)` (X̂ = decoder ∘ W) |
| `MutualInfo.mutualInfo` (def) | Step 4: feasible joint への iInf-下界 |

**新規** (本 plan で書く):
- `expectedDistortion` (定義, ~5 行)
- `rateDistortionFunction` (定義, ~15 行)
- `rateDistortionFunction_le_of_feasible` (補題, ~30 行)
- `rate_distortion_converse_single_shot` (主定理, ~100 行)

総見積 ~250-400 行。

## Phase A — definitions 📋

### A.1 `expectedDistortion`

```lean
/-- Expected distortion of a joint distribution `ν : Measure (α × β)` under a
distortion measure `d : α → β → ℝ`. -/
noncomputable def expectedDistortion
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (d : α → β → ℝ) (ν : Measure (α × β)) : ℝ :=
  ∫ p, d p.1 p.2 ∂ν
```

### A.2 `rateDistortionFunction`

```lean
/-- Rate-distortion function. For a source distribution `P : Measure α` and
distortion threshold `D : ℝ`, R(D) is the infimum of `klDiv ν (marginals)`
(i.e. the MI of the joint `ν`) over feasible joint distributions:
- `ν.map Prod.fst = P` (marginal correct)
- `expectedDistortion d ν ≤ D` (avg distortion ≤ D)

Returns `ℝ≥0∞`. If no feasible `ν` exists, the iInf is `∞`. -/
noncomputable def rateDistortionFunction
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (d : α → β → ℝ) (P : Measure α) (D : ℝ) : ℝ≥0∞ :=
  ⨅ (ν : Measure (α × β)) (_ : ν.map Prod.fst = P)
    (_ : expectedDistortion d ν ≤ D),
      klDiv ν ((ν.map Prod.fst).prod (ν.map Prod.snd))
```

## Phase B — basic properties 📋

### B.1 `rateDistortionFunction_le_of_feasible`

```lean
theorem rateDistortionFunction_le_of_feasible
    (d : α → β → ℝ) (P : Measure α) (D : ℝ)
    (ν : Measure (α × β))
    (hν_marg : ν.map Prod.fst = P)
    (hν_dist : expectedDistortion d ν ≤ D) :
    rateDistortionFunction d P D
      ≤ klDiv ν ((ν.map Prod.fst).prod (ν.map Prod.snd)) := by
  unfold rateDistortionFunction
  exact iInf_le_of_le ν (iInf_le_of_le hν_marg (iInf_le _ hν_dist))
```

## Phase C — 単発 converse 主定理 📋

### C.1 `rate_distortion_converse_single_shot`

```lean
theorem rate_distortion_converse_single_shot
    {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    {M : Type*} [Fintype M] [MeasurableSpace M] [MeasurableSingletonClass M]
    [Nonempty M]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (encoder : α → M) (decoder : M → β)
    (hX : Measurable X)
    (d : α → β → ℝ)
    (hMI_finite :
      mutualInfo μ X ((decoder ∘ encoder) ∘ X) ≠ ∞) :
    (rateDistortionFunction d (μ.map X)
        (expectedDistortion d
          (μ.map (fun ω => (X ω, (decoder ∘ encoder) (X ω)))))).toReal
      ≤ Real.log (Fintype.card M) := by
  -- See Approach: 4-step chain.
  sorry
```

主定理の **fan in 順**:
1. `entropy μ W ≤ Real.log (Fintype.card M)` (`entropy_le_log_card`)
2. `(mutualInfo μ X W).toReal ≤ entropy μ W` (Bridge + `condEntropy_nonneg`)
3. `mutualInfo μ X X̂ ≤ mutualInfo μ X W` (DPI: X̂ = decoder ∘ W)
4. `rateDistortionFunction (μ.map X) D̃ ≤ klDiv (joint) (marg-prod) = mutualInfo μ X X̂`
   (`rateDistortionFunction_le_of_feasible` + 定義書き換え)

Step 4 詳細:
- `ν := μ.map (fun ω => (X ω, X̂ ω))` where `X̂ := (decoder ∘ encoder) ∘ X`
- `ν.map Prod.fst = μ.map X` (確認: `Measure.map_map` で `Prod.fst ∘ (X, X̂) = X`)
- `expectedDistortion d ν = ∫ ω, d (X ω) (X̂ ω) ∂μ = D̃` (定義通り、`integral_map` で μ-側へ翻訳)
- `ν.map Prod.snd = μ.map X̂`
- `klDiv ν ((ν.map Prod.fst).prod (ν.map Prod.snd)) = mutualInfo μ X X̂` (定義 unfold)

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **Single-shot scope に commit** (起草時): n-letter form `rate ≥ R(D)` は
   `R(D)` の convexity (Jensen) を要し、解析的 Mathlib gap が ~500-1000 行規模。
   本 plan は `n=1` MVP に絞り、**0 sorry 完走** を最優先する。
   n-letter form は **後継カード E-4'** へ。

2. **`R(D̃)` (実測歪み) vs `R(D)` (公称閾値)** (起草時): `D̃ ≤ D` を assume すれば
   R(D) の **antitone monotonicity** (`D₁ ≤ D₂ ⇒ R(D₁) ≥ R(D₂)`) で `R(D̃) ≥ R(D)` を
   出せるが、本 plan は **公称値依存を避け** `R(D̃)` 形で publish する。R(D) 単調性
   の証明は feasible set の包含関係から ~20 行で出るが、ENNReal の `iInf_le` 系の
   plumbing で意外と詰むため deferred。

3. **`.toReal` lift の有限性仮定** (起草時): MI が `∞` のとき `.toReal = 0` なので
   `R(D̃).toReal ≤ log M` は左辺が `0` で trivially 成立しうるが、その「成立」は
   `iInf` の値が `∞` になる病的ケースを含んでしまう。MI 有限を仮定して非自明な
   下界として publish する。

4. **distortion measure の non-negativity** (起草時): R(D) の解析的性質
   (単調性、`R(0)` 形) には `0 ≤ d a b` を要するが、**主定理 (本 plan)** は
   non-negativity 不要 (定義の iInf-下界として直接使う)。よって本 plan の
   signature には **`0 ≤ d` を assume しない**。

## Mathlib gap

- **single-shot (E-4)**: なし。既存 `InformationTheory/Shannon/` 資産で press 済 (0 sorry)。
- **n-letter (E-4-C)**: MI superadditivity `∑ I(Xᵢ; X̂ᵢ) ≤ I(X^n; X̂^n)` (独立 source) が
  project 内 wall。Stage 2 `_singleLetter` の唯一の残 sorry。額面の壁扱いは未確定 (gateway-atom
  で再判定、上記 E-4-C)。

## 後継

- **E-4-A** ✅ R(D) 単調性 `D₁ ≤ D₂ ⇒ R(D₁) ≥ R(D₂)` — `rateDistortionFunction_antitone`
  (`ConverseMonotone.lean:39`、genuine)。
- **E-4-B** ✅ R(D) 凸性 — `rateDistortionFunction_convexOn`
  (`RateDistortionConvexity.lean:390`、**genuine proof done**、DPI selector-forget 経路、
  sorryAx 非依存)。詳細 → `rate-distortion-convexity-plan.md`。
- **E-4-C** 🚧 n-letter chain rule converse — `RateDistortionConverseNLetter.lean`。下記。
- **E-4-D** R(D) 連続性 (continuity of `D ↦ R(D)` on `[0, D_max)`) — deferred。

## E-4-C — n-letter single-letterization converse 🚧

> 前提資産 (全て genuine / sorryAx 非依存):
> - Stage 1 `rate_distortion_converse_n_letter_block` (`RateDistortionConverseNLetter.lean:72`) —
>   block-level 形 `R_block(P_X^n, D).toReal ≤ log M`。single-shot specified を
>   `(α := Fin n → α, β := Fin n → β, M := Fin M)` で直接 instantiate。
> - 凸性 `rateDistortionFunction_convexOn` (`RateDistortionConvexity.lean:390`、E-4-B)。

**現状** (Stage 2 `rate_distortion_converse_n_letter_singleLetter`, `:305`、sorry 据置 `:328`、
`@residual(plan:rate-distortion-converse-plan)`):

- **true-as-framed 化済** (今セッション、commit `06b1435`)。migration が load-bearing
  `h_jensen_antitone` を除去した際に regularity precondition (`expectedBlockDistortion ≤ D` +
  独立性) を分離せず落とし、**under-hypothesized = 偽**になっていた。反例:
  - n=1, M=2, |α|=4, D=0 → `R = log4 > log2 = RHS` (operating-point 欠落)
  - n=2, X₁=X₂ (full dep), uniform `{0,1}`, M=2, D=0 → `log2 > (1/2)log2 = RHS` (独立性欠落)
- `hD : c.expectedBlockDistortion P_X d ≤ D` + `hindep : iIndepFun (fun i => Xs i) μ` を
  precondition 追加して **true-as-framed** 化。両者は regularity precondition (Stage 1 が同じ
  `hD` を既に持つ)、`*Hypothesis` predicate に bundle せず plain hyp。独立監査 honest_residual、
  0 consumer。

**残壁 = MI superadditivity / tensorization** `∑ I(Xᵢ; X̂ᵢ) ≤ I(X^n; X̂^n)` (独立 source)。
project 内 wall 扱い (`ParallelGaussianPerCoord.lean` の "n" family と同根、逆向き lemma
`mutualInfo_le_sum_per_letter_of_memoryless_strong` は閉じない)。これが genuine 化すれば
凸性 (E-4-B ✅) + Stage 1 (genuine) + tensorization で single-letterization が閉じる。

**次の一手**: MI superadditivity を **gateway-atom で判定** (壁を額面で受けず、atom 1 本を
着手して self-buildable か / 真の Mathlib 壁かを確認 — Cramér 前例で「not-a-wall verdict は
gateway-atom 確認後に記録」)。退化境界 verify (独立 source の縮退ケース) も併せて。
