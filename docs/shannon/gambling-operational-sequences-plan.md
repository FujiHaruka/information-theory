# Gambling: operational sequences (Cover–Thomas §6.3) サブ計画

> **Parent**: [`gambling-moonshot-plan.md`](gambling-moonshot-plan.md) §残課題 (operational gambling)

## 進捗

- [ ] M0 在庫 (SLLN 署名 + discrete-expectation bridge テンプレ + 親 Basic.lean 3 資産 verbatim) 📋
- [ ] Phase 1 — skeleton (def 3 本 + 補助補題 5 本 + headline/corollary 3 本を `sorry` 化、root 登録) 📋
- [ ] Phase 2 — discrete-expectation bridge `integral_comp_law` (中心計算) 📋
- [ ] Phase 3 — iid plumbing (Integrable / IdentDistrib / IndepFun の `.comp` 持ち上げ) 📋
- [ ] Phase 4 — headline `seqLogWealth_div_tendsto_doublingRate` (SLLN 組立) 📋
- [ ] Phase 5 — `lawPmf ∈ stdSimplex` + 比例賭け閉形式 corollary 📋
- [ ] Phase 6 — 最適性 corollary + 配線 (root / README / roadmap) + 独立 honesty 監査 📋

## Context

親計画 `gambling-moonshot-plan.md` は Cover–Thomas Ch.6 **Thm 6.1.2** (比例賭け倍加率最適性) を
`InformationTheory/Shannon/Gambling/Basic.lean` で proof-done (sorryAx-free, `@audit:ok`) 済み。
Thm 6.1.3 (副情報増分 = MI) も子プラン `gambling-side-information-plan.md` で closure 済み。

本サブ計画は roadmap `## scope-out` の **operational gambling (horse-race sequences)** = Cover–Thomas
**§6.3** を拾う: i.i.d. 競馬列 `Xs : ℕ → Ω → α` に対し固定賭け `b` / オッズ `o` で得る富の対数増分の
時間平均が **ほとんど確実に (a.s.) 倍加率 `doublingRate b o p` に収束する** という operational (列レベル)
定理。`p` は `Xs 0` の法 (law) の pmf。比例 (Kelly) 賭け `b = p` で極限は最適値 `W*(p)`。

**tractability の load-bearing な観測**: これは `InformationTheory/Shannon/AEP/Basic/Core.lean` の
`aep_ae` (L138–163) の **near-clone**。`aep_ae` は i.i.d. 列の実数値関数 `logLikelihood μ Xs i` に
プロジェクト補題 `strong_law_ae_real` を適用し、SLLN の極限 `μ[logLikelihood μ Xs 0]` を離散期待値
bridge `integral_logLikelihood_zero` で `entropy μ (Xs 0)` に書き換える。本結果は同一 shape で、
`logLikelihood μ Xs i` を `fun ω ↦ Real.log (b (Xs i ω) * o (Xs i ω))` に置き換え、極限を
`doublingRate b o p` に橋渡しするだけ。壁は想定されない。

既存共有補題の **署名変更は一切しない** (consume のみ): `doublingRate` / `doublingRate_proportional_eq`
/ `doublingRate_le_proportional` (親 Basic.lean) と `strong_law_ae_real` (Mathlib) を参照するのみで、
ripple 無し (`dep_consumers.sh` 不要 — 署名を変えないため)。

## ゴール / Approach

**ゴール** — 新規 file `InformationTheory/Shannon/Gambling/OperationalSequences.lean`、namespace
`InformationTheory.Shannon.Gambling`、`variable {Ω} [MeasurableSpace Ω] {α} [Fintype α]
[MeasurableSpace α] [MeasurableSingletonClass α]`。

```lean
-- alphabet-side per-race log return  g(x) = log(b x · o x)
noncomputable def betLogReturn (b o : α → ℝ) : α → ℝ := fun x ↦ Real.log (b x * o x)

-- log-wealth after n races (starting from 1):  log S_n = ∑_{i<n} log(b(Xs i)·o(Xs i))
noncomputable def seqLogWealth (b o : α → ℝ) (Xs : ℕ → Ω → α) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range n, betLogReturn b o (Xs i ω)

-- pmf (law) of a finite random variable
noncomputable def lawPmf (μ : Measure Ω) (X : Ω → α) : α → ℝ := fun x ↦ (μ.map X).real {x}

-- headline (§6.3, general bet): (1/n)·log S_n → W(b,o,p) a.s.
@[entry_point]
theorem seqLogWealth_div_tendsto_doublingRate
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b o : α → ℝ)
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ seqLogWealth b o Xs n ω / n) atTop
      (𝓝 (doublingRate b o (lawPmf μ (Xs 0))))
```

**Approach** — `aep_ae` の SLLN clone + 期待値→pmf bridge。証明の全体形:

```
X i := fun ω ↦ betLogReturn b o (Xs i ω)         -- = betLogReturn b o ∘ Xs i
strong_law_ae_real X hint hindep hident  ⟹  ∀ᵐ ω, (∑_{i<n} X i ω)/n → μ[X 0]
seqLogWealth b o Xs n ω / n  ≡  (∑_{i<n} X i ω)/n              -- defeq (seqLogWealth の展開)
μ[X 0] = ∫ ω, betLogReturn b o (Xs 0 ω) ∂μ
       = ∑ x, (μ.map (Xs 0)).real {x} · betLogReturn b o x      -- integral_map + integral_fintype
       = ∑ x, lawPmf μ (Xs 0) x · Real.log (b x · o x)
       = doublingRate b o (lawPmf μ (Xs 0))                      -- def 展開 + smul_eq_mul
```

3 つの部品しかない:

1. **SLLN 本体** = `strong_law_ae_real` を `X i = betLogReturn b o ∘ Xs i` に適用 (`aep_ae` L158 と同型)。
2. **iid plumbing** = `Integrable (X 0)` / `Pairwise (IndepFun on X)` / `∀ i, IdentDistrib (X i) (X 0)` を、
   親の `Xs` 側 hyp から可測関数 `betLogReturn b o` (`measurable_of_finite`) との `.comp` で持ち上げる
   (`integrable_logLikelihood` / `indepFun_logLikelihood` / `identDistrib_logLikelihood` L78–132 の 1:1 clone)。
3. **discrete-expectation bridge** = `∫ ω, g (X ω) ∂μ = ∑ x, (μ.map X).real {x} · g x`
   (`integral_logLikelihood_zero` L92–114 を一般 `g : α → ℝ` に脱特殊化した `integral_comp_law`)。
   `integral_map` (push-forward) → `integral_fintype` (有限和化) → `smul_eq_mul` の 3 手。

**極限の同定 `μ[X 0] = doublingRate b o (lawPmf μ (Xs 0))` は本 file の唯一の非自明部**。
`aep_ae` の `simpa [h_int_eq] using hω` パターン (`μ[X 0]` 記法は `∫ ω, X 0 ω ∂μ` に展開される) を踏襲する。

**pmf `p` は `Xs 0` の法**: `doublingRate` の第3引数 `p` を `lawPmf μ (Xs 0)` で束ねるのは
**genuine な定義的束縛** (命題の核を仮説に encode するのではなく、`Xs 0` の法という定義そのもの)。
iid + 可測性は regularity precondition。hypothesis bundling は無い (正直性メモ参照)。

**比例 (Kelly) 賭け**: `b := lawPmf μ (Xs 0)` を代入すると極限は `doublingRate p o p = W*(p)`。
`doublingRate_proportional_eq` で閉形式 `∑ p·log o − ∑ negMulLog p` に、`doublingRate_le_proportional`
で任意 full-support 賭けに対する最適性 `W(b) ≤ W*(p)` に接続する (corollary 2 本)。

**壁は無い**: 全補題は既存 sorryAx-free asset の再利用 + `aep_ae` の機械的 clone。proof-done 到達可能。

## M0 在庫 (verbatim 署名 — 実装前に Phase 0 で再 Read 確認)

### SLLN 本体 (Mathlib)

- `.lake/packages/mathlib/Mathlib/Probability/StrongLaw.lean:598`
  ```lean
  theorem strong_law_ae_real {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
      (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ)
      (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
      (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ i ∈ range n, X i ω) / n) atTop (𝓝 μ[X 0])
  ```
  — `[IsProbabilityMeasure μ]` は **明示引数でない** (退化 case を内部処理し、それ以外で内部 derive)。
  極限 `μ[X 0] = ∫ ω, X 0 ω ∂μ`。`hindep` は `((· ⟂ᵢ[μ] ·) on X)` 形 (`aep_ae` は `Pairwise fun i j ↦ …`
  形で渡しており defeq、`on` 展開で一致)。

### discrete-expectation bridge の部品 (Mathlib)

- `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1033`
  ```lean
  theorem integral_map {β} [MeasurableSpace β] {φ : α → β} (hφ : AEMeasurable φ μ) {f : β → G}
      (hfm : AEStronglyMeasurable f (Measure.map φ μ)) :
      ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ
  ```
- `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/SumMeasure.lean:209`
  ```lean
  theorem integral_fintype [Fintype X] (hf : Integrable f μ) :
      ∫ x, f x ∂μ = ∑ x, μ.real {x} • f x
  ```
  — `f : X → E`、`[MeasurableSpace X]` + `[MeasurableSingletonClass X]` は section 前提。`μ.real {x} • f x`
  の `•` は実数では `smul_eq_mul` で `*`。
- `.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Basic.lean:280`
  ```lean
  theorem measurable_of_finite [Finite α] [MeasurableSingletonClass α] (f : α → β) : Measurable f
  ```
  — `betLogReturn b o : α → ℝ` の可測性 (`[Fintype α]` ⊃ `[Finite α]`)。

### テンプレ元 (`aep_ae` chain、脱特殊化して clone)

`InformationTheory/Shannon/AEP/Basic/Core.lean`:

- `L78 integrable_logLikelihood` — `Integrable.of_finite` (μ.map 上) を `.comp_measurable (hXs i)` で pull-back。
  clone 元: `Integrable (X 0) μ`。`IsProbabilityMeasure (μ.map (Xs 0))` を
  `Measure.isProbabilityMeasure_map (hXs 0).aemeasurable` で供給。
- `L92 integral_logLikelihood_zero` — `∫ ω, pmfLog μ Xs (Xs 0 ω) ∂μ = entropy μ (Xs 0)`。手順:
  `integral_map (hXs 0).aemeasurable (measurable_pmfLog μ Xs).aestronglyMeasurable`
  → `integral_fintype Integrable.of_finite` → 各項 `smul_eq_mul` 書換。**bridge の 1:1 テンプレ**。
- `L117 identDistrib_logLikelihood` — `(hident i).comp (measurable_pmfLog μ Xs)`。
- `L124 indepFun_logLikelihood` — `(hindep hij).comp hpf hpf` (`hpf = measurable_pmfLog`)。
- `L140 aep_ae` — 上記 4 本 + `strong_law_ae_real` + `integral_*_zero` の `filter_upwards`/`simpa`。**headline の 1:1 テンプレ**。

### 親 Basic.lean 3 資産 (consume のみ、署名変更なし)

`InformationTheory/Shannon/Gambling/Basic.lean` (namespace `InformationTheory.Shannon.Gambling`,
`variable {α} [Fintype α]`):

1. `Basic.lean:72`
   `noncomputable def doublingRate (b o p : α → ℝ) : ℝ := ∑ x, p x * Real.log (b x * o x)`
   — 引数順 **(賭け, オッズ, 真の law)**。極限 = `doublingRate b o (lawPmf μ (Xs 0))`。
2. `Basic.lean:77`
   `theorem doublingRate_proportional_eq (p o : α → ℝ) (hp : p ∈ stdSimplex ℝ α) (ho : ∀ x, 0 < o x) : doublingRate p o p = (∑ x, p x * Real.log (o x)) - ∑ x, Real.negMulLog (p x)`
   — `p := lawPmf μ (Xs 0)` に適用 (比例賭け閉形式 corollary、`p` の positivity 不要)。
3. `Basic.lean:124` (`@[entry_point]`, `@audit:ok`)
   `theorem doublingRate_le_proportional (p b o : α → ℝ) (hp : p ∈ stdSimplex ℝ α) (hb : b ∈ stdSimplex ℝ α) (hb_pos : ∀ x, 0 < b x) (ho : ∀ x, 0 < o x) : doublingRate b o p ≤ doublingRate p o p`
   — `p := lawPmf μ (Xs 0)` に適用 (最適性 corollary、`b` full-support 前提)。

### Mathlib 側 (transitive、明示 import)

`Real.log_mul` / `Real.negMulLog` / `Finset.sum_range` / `smul_eq_mul` /
`Measure.isProbabilityMeasure_map` / `Integrable.of_finite` / `IdentDistrib.comp` / `IndepFun.comp` /
`stdSimplex`。imports: `Meta.EntryPoint` + `Shannon.Gambling.Basic` + `Mathlib.Probability.StrongLaw`
+ `Mathlib.Probability.IdentDistrib` + `Mathlib.Probability.Independence.Basic`
+ `Mathlib.MeasureTheory.Integral.Bochner.SumMeasure` (+ `…Bochner.Basic` は transitive 見込み、
不足なら追記)。

## 個別 decl 内訳 (新 file)

def 3 + 補助補題 5 + headline/corollary 3 ≈ 200–240 行。全て `aep_ae` chain の脱特殊化 clone +
親 Basic.lean の再利用。

| # | decl (提案名) | 種別 | 依拠 (file:line) |
|---|---|---|---|
| D1 | `betLogReturn (b o : α → ℝ) : α → ℝ` | def | 新規 (`Real.log (b x * o x)`) |
| D2 | `seqLogWealth (b o) (Xs) (n) : Ω → ℝ` | def | 新規 (`∑ i ∈ range n, betLogReturn b o (Xs i ω)`) |
| D3 | `lawPmf (μ) (X : Ω → α) : α → ℝ` | def | 新規 (`(μ.map X).real {x}`) |
| L1 | `measurable_betLogReturn (b o) : Measurable (betLogReturn b o)` | lemma | `measurable_of_finite` (Basic.lean:280) |
| L2 | `integral_comp_law (μ) [IsProbabilityMeasure μ] (X) (hX : Measurable X) (g : α → ℝ) : ∫ ω, g (X ω) ∂μ = ∑ x, (μ.map X).real {x} * g x` | lemma | `integral_map` + `integral_fintype` (= `integral_logLikelihood_zero` の一般化) |
| L3 | `integrable_betLogReturn_zero (μ) [IsProbabilityMeasure μ] (b o) (Xs) (hXs) : Integrable (fun ω ↦ betLogReturn b o (Xs 0 ω)) μ` | lemma | `integrable_logLikelihood` (Core.lean:78) clone |
| L4 | `identDistrib_betLogReturn (μ) (b o) (Xs) (hident) (i) : IdentDistrib (fun ω ↦ betLogReturn b o (Xs i ω)) (fun ω ↦ betLogReturn b o (Xs 0 ω)) μ μ` | lemma | `identDistrib_logLikelihood` (Core.lean:117) clone |
| L5 | `indepFun_betLogReturn (μ) (b o) (Xs) (hindep) : Pairwise fun i j ↦ (fun ω ↦ betLogReturn b o (Xs i ω)) ⟂ᵢ[μ] (fun ω ↦ betLogReturn b o (Xs j ω))` | lemma | `indepFun_logLikelihood` (Core.lean:124) clone |
| L6 | `lawPmf_mem_stdSimplex (μ) [IsProbabilityMeasure μ] (X) (hX) : lawPmf μ X ∈ stdSimplex ℝ α` | lemma | `measureReal_nonneg` + `sum_measureReal_singleton` / `probReal_univ` (Core.lean:265–273 `hsum_P`/`hP_pos` template) |
| H1 | `seqLogWealth_div_tendsto_doublingRate` | `@[entry_point]` theorem | headline、`aep_ae` (Core.lean:140) clone |
| C1 | `seqLogWealth_proportional_div_tendsto` | corollary (entry_point 候補) | H1(b:=lawPmf) + `doublingRate_proportional_eq` + L6 |
| C2 | `seqLogWealth_proportional_asymptotically_optimal` | `@[entry_point]` theorem | H1 ×2 + `doublingRate_le_proportional` + L6 |

**corollary の shape (提案)**:

```lean
-- C1: 比例 (Kelly) 賭けの列レベル growth = 閉形式 W*(p) = ∑ p·log o − H(p)
theorem seqLogWealth_proportional_div_tendsto
    (μ : Measure Ω) [IsProbabilityMeasure μ] (o : α → ℝ) (ho : ∀ x, 0 < o x)
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ seqLogWealth (lawPmf μ (Xs 0)) o Xs n ω / n) atTop
      (𝓝 ((∑ x, lawPmf μ (Xs 0) x * Real.log (o x)) - ∑ x, Real.negMulLog (lawPmf μ (Xs 0) x)))

-- C2: 比例賭けが任意 full-support 賭けに漸近的に劣らない (operational 最適性)
theorem seqLogWealth_proportional_asymptotically_optimal
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b o : α → ℝ)
    (hb : b ∈ stdSimplex ℝ α) (hb_pos : ∀ x, 0 < b x) (ho : ∀ x, 0 < o x)
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ ↦ seqLogWealth b o Xs n ω / n) atTop
        (𝓝 (doublingRate b o (lawPmf μ (Xs 0)))) ∧
      Tendsto (fun n : ℕ ↦ seqLogWealth (lawPmf μ (Xs 0)) o Xs n ω / n) atTop
        (𝓝 (doublingRate (lawPmf μ (Xs 0)) o (lawPmf μ (Xs 0)))) ∧
      doublingRate b o (lawPmf μ (Xs 0)) ≤ doublingRate (lawPmf μ (Xs 0)) o (lawPmf μ (Xs 0))
```

注: C2 の第3連言 (不等式) は ω 非依存の決定的事実 (`doublingRate_le_proportional` L6 経由)。`∀ᵐ` 内に
束ねると「a.e. で両富列の成長率が確定し Kelly が優越」という単一 operational 主張になる。`∀ᵐ` 外に
出す (2 収束 + 別の不等式定理) 形も可 — 実装時に読みやすい方を選ぶ (どちらも honest)。

## Phase 詳細

### M0 — 在庫確認 (proof-log: no)
- [ ] `strong_law_ae_real` の verbatim 署名 (極限 `μ[X 0]`、`hindep` の `on` 形) を再 Read 確認。
- [ ] `integral_map` / `integral_fintype` / `measurable_of_finite` の verbatim 署名を再 Read 確認。
- [ ] `aep_ae` chain (Core.lean:78/92/117/124/140) を Read し clone 対象を確定。
- [ ] 親 Basic.lean の 3 資産 (`doublingRate` 引数順 / `doublingRate_proportional_eq` は p positivity 不要 /
      `doublingRate_le_proportional` の full-support 前提) を verbatim 再確認。

### Phase 1 — skeleton (proof-log: no)
- [ ] 新 file 作成、imports (M0 の一覧) + namespace + `variable` (`{Ω} [MeasurableSpace Ω] {α}
      [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]`)。`[DecidableEq α]` / `[Nonempty α]`
      は tactic が要求した場合のみ追加 (`aep_ae` は付けているが本 file の bridge/plumbing では不要見込み)。
- [ ] def 3 本 (D1–D3) を書く。
- [ ] 補助補題 5 本 (L1–L6) + headline/corollary 3 本 (H1/C1/C2) を `:= by sorry` で state。
- [ ] `InformationTheory.lean` に `import InformationTheory.Shannon.Gambling.OperationalSequences` を
      追記 (既存 `Gambling.SideInformation` 行 = `InformationTheory.lean:277` の直後)。
- [ ] Write 後 LSP `<new-diagnostics>` で skeleton が型検査を通す (sorry 警告のみ) ことを確認。

### Phase 2 — discrete-expectation bridge `integral_comp_law` (proof-log: yes — 中心計算)
- [ ] L2 を `integral_logLikelihood_zero` (Core.lean:92–114) の一般化として証明:
      `integral_map hX.aemeasurable (measurable_of_finite g).aestronglyMeasurable` で push-forward →
      `integral_fintype (μ := μ.map X) Integrable.of_finite` で有限和化 →
      各項 `(μ.map X).real {x} • g x = (μ.map X).real {x} * g x` を `smul_eq_mul` で書換。
- [ ] `IsProbabilityMeasure (μ.map X)` を `Measure.isProbabilityMeasure_map hX.aemeasurable` で供給
      (`integral_fintype` の `Integrable.of_finite` に必要)。
- [ ] proof-log に「push-forward → 有限和 → smul」の 3 手と、`integral_logLikelihood_zero` との差分
      (一般 `g`、entropy 特殊化を外した) を記録。

### Phase 3 — iid plumbing (proof-log: no)
- [ ] L1 `measurable_betLogReturn` = `measurable_of_finite _`。
- [ ] L3 `integrable_betLogReturn_zero` = `(Integrable.of_finite : Integrable (betLogReturn b o) (μ.map (Xs 0))).comp_measurable (hXs 0)` (`IsProbabilityMeasure (μ.map (Xs 0))` 供給、L78 clone)。
- [ ] L4 `identDistrib_betLogReturn` = `(hident i).comp (measurable_betLogReturn b o)` (L117 clone)。
- [ ] L5 `indepFun_betLogReturn` = `(hindep hij).comp hmeas hmeas` (L124 clone)。
      `Pairwise (… on X)` と `Pairwise fun i j ↦ …` の defeq を確認 (SLLN 側は `on` 形)。

### Phase 4 — headline `seqLogWealth_div_tendsto_doublingRate` (proof-log: yes — SLLN 組立)
- [ ] `X i := fun ω ↦ betLogReturn b o (Xs i ω)`。`h_lln := strong_law_ae_real X (L3) (L5) (L4)`。
- [ ] `h_bridge := integral_comp_law μ (Xs 0) (hXs 0) (betLogReturn b o)` で
      `∫ ω, betLogReturn b o (Xs 0 ω) ∂μ = ∑ x, (μ.map (Xs 0)).real {x} * betLogReturn b o x`。
- [ ] 極限同定: RHS `= doublingRate b o (lawPmf μ (Xs 0))` を `unfold doublingRate betLogReturn lawPmf`
      で `∑ x, (μ.map (Xs 0)).real {x} * Real.log (b x * o x)` に一致させる (`Finset.sum_congr` / `rfl`)。
- [ ] `filter_upwards [h_lln] with ω hω`、`seqLogWealth b o Xs n ω / n ≡ (∑ i ∈ range n, X i ω)/n`
      (`seqLogWealth` 展開で defeq)、`μ[X 0] = ∫ ω, betLogReturn b o (Xs 0 ω) ∂μ` を bridge で書換し
      `simpa` (`aep_ae` L162–163 パターン)。
- [ ] proof-log に SLLN 適用 + bridge 書換 + `μ[X 0]` 記法展開の順序を記録。

### Phase 5 — `lawPmf ∈ stdSimplex` + 比例賭け閉形式 corollary (proof-log: no)
- [ ] L6 `lawPmf_mem_stdSimplex`: `.1` (非負) = `measureReal_nonneg`、`.2` (和 = 1) =
      `∑ x, (μ.map X).real {x} = (μ.map X).real univ = 1` (`sum_measureReal_singleton` +
      `Finset.coe_univ` + `probReal_univ`、`typicalSet_card_le` の `hsum_P` L265–273 template)。
      `IsProbabilityMeasure (μ.map X)` を供給。
- [ ] C1 `seqLogWealth_proportional_div_tendsto`: H1 を `b := lawPmf μ (Xs 0)` で呼び、極限
      `doublingRate (lawPmf μ (Xs 0)) o (lawPmf μ (Xs 0))` を
      `doublingRate_proportional_eq (lawPmf μ (Xs 0)) o (L6) ho` で閉形式に `Tendsto.congr` / 書換。

### Phase 6 — 最適性 corollary + 配線 + 独立 honesty 監査 (proof-log: no)
- [ ] C2 `seqLogWealth_proportional_asymptotically_optimal`: H1 を `b` と `b := lawPmf μ (Xs 0)` の 2 回、
      `filter_upwards` で 2 収束を束ね、決定的不等式を
      `doublingRate_le_proportional (lawPmf μ (Xs 0)) b o (L6) hb hb_pos ho` で供給。
- [ ] root import は Phase 1 で登録済 → `lake build InformationTheory.Shannon.Gambling.OperationalSequences`
      で clean 確認、H1/C2 (+ C1) を `#print axioms` で sorryAx-free (`[propext, Classical.choice, Quot.sound]`)
      確認。
- [ ] README 定理表: `docs/readme-theorems.txt` の Ch.6 節に headline (H1 + C2、C1 は任意) を追記 →
      `gen_readme_table.ts --write` (表本体は手編集不可)。
- [ ] roadmap: `## scope-out` の「operational gambling (horse-race sequences)」を closure 済に更新
      (§6.3 = a.s. 収束、注記に残 scope-out = 株式市場 Ch.6 stock-market を明記)。
- [ ] 親 `gambling-moonshot-plan.md` §残課題の sub-plan テーブルに本子プランの行を追加 (**orchestrator が親を同期**)。
- [ ] `docs/shannon/shannon-facts.md` に再検証コマンド追記 (family facts があれば)。
- [ ] **独立 honesty 監査必須**: 新 def (`betLogReturn` / `seqLogWealth` / `lawPmf`) + headline H1 を
      `honesty-auditor` に付す (`lawPmf μ (Xs 0)` が genuine 定義的束縛で hypothesis bundling でないこと・
      iid/可測性が regularity のみ・check 4 sufficiency を確認) → headline を `@audit:ok`。

## 正直性メモ (precondition の性質)

全 precondition は **regularity precondition**、load-bearing hypothesis bundling ではない:

- `[IsProbabilityMeasure μ]` — 確率測度 (SLLN + bridge の前提)。
- `hXs : ∀ i, Measurable (Xs i)` — 各競馬結果 RV の可測性。
- `hindep : Pairwise (Xs i ⟂ᵢ[μ] Xs j)` + `hident : ∀ i, IdentDistrib (Xs i) (Xs 0)` — i.i.d. 列
  (SLLN の必須前提、命題の核を encode するのではなく列の統計的構造)。
- C2 のみ追加 `b ∈ stdSimplex` + `∀ x, 0 < b x` + `∀ x, 0 < o x` — full-support 賭け + 正のオッズ
  (親 Basic.lean の `doublingRate_le_proportional` と同性質、`log 0 = 0` 規約由来の correctness precondition)。

**pmf `p = lawPmf μ (Xs 0)` の束縛は genuine な定義的束縛**: 極限を `doublingRate b o (lawPmf μ (Xs 0))`
と書くのは、`Xs 0` の法という **定義そのもの** を参照しているだけで、証明の核を仮説に抱えさせては
いない。`aep_ae` が極限を `entropy μ (Xs 0)` と書くのと同型。headline は「recognizable な倍加率への
a.s. 収束」であり trivial/circular でない (SLLN + 非自明 bridge を経由する)。

## 規模見積 / 想定壁

- **規模**: 新 file 1 本、def 3 + 補助補題 5 (うち 4 本は `aep_ae` chain の 1:1 clone) + headline/corollary 3
  ≈ 200–240 行 (task 上限 ~250 行内)。最重は Phase 2 bridge (~25 行、`integral_logLikelihood_zero` 相当) と
  Phase 4 headline (~25 行、`aep_ae` 相当)。
- **想定壁**: **無し** (公算大)。`aep_ae` (Core.lean、sorryAx-free、`@[entry_point]`) が同一 machinery で
  既に proof-done ゆえ、`logLikelihood` → `betLogReturn` の置換で機械的に閉じる。Mathlib gap は生じない。
  壁判定を loogle 0-hit だけで確定しない (CLAUDE.md「壁を宣言するとき」) が、そもそも壁 family でない
  (既存資産の脱特殊化 = plumbing)。
- **署名変更 ripple**: 無し。既存共有補題は consume のみ (`doublingRate` / `doublingRate_proportional_eq`
  / `doublingRate_le_proportional` / `strong_law_ae_real`)、本 file は Gambling.Basic の新規 consumer。
  `dep_consumers.sh` は署名変更時のみ必要 — 本計画では不要。

## 最大リスク + fallback

**単一の最も詰まりそうな箇所** = **極限の同定 `μ[X 0] = doublingRate b o (lawPmf μ (Xs 0))`**
(= bridge `integral_comp_law` + def 展開の噛み合わせ)。具体的な摩擦候補: (a) `integral_fintype` が返す
`μ.real {x} • g x` の `•` → `*` 変換 (`smul_eq_mul`)、(b) `doublingRate b o p` の引数順 (賭け, オッズ, 法)
と bridge RHS `∑ p x * Real.log (b x * o x)` の項ごとの一致 (`Finset.sum_congr`)、(c) `integral_map` の
`AEStronglyMeasurable f (μ.map (Xs 0))` 要求 (`measurable_of_finite _ |>.aestronglyMeasurable`)。
いずれも `integral_logLikelihood_zero` で実証済の手順ゆえ risk は低いが、噛み合わせがずれると
Phase 4 headline が組めない。

**fallback (honest 撤退)**: Phase 2 の bridge `integral_comp_law` (または極限同定ステップ) が詰まったら、
**当該補題の signature を target 形のまま保ち body を `sorry` + `@residual(plan:gambling-operational-sequences-plan)`**
で撤退する。headline H1 は `𝓝 (doublingRate b o (lawPmf μ (Xs 0)))` の form を保ったまま (bridge の
`sorry` を transitive に継承)、SLLN skeleton は残す。hypothesis bundling / `*Hypothesis` predicate 化は
**禁止** — 極限を仮説で渡す (`(h : μ[X 0] = doublingRate …) → …`) のは load-bearing bundling なので不可。
想定壁は無いので `wall:` は使わない。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除 (git が履歴)、active な判断のみ残す。

1. **極限 pmf = `lawPmf μ (Xs 0)` (local def) で束縛**: 既存 project に `(μ.map X).real {x}` を返す
   再利用可能な `law`/pmf def は不在 (`pmfLog` は `-log` を掛けた形で inline)。`lawPmf` を新規 def 化して
   readability を確保 (genuine 定義的束縛、honesty 監査で bundling でないことを確認)。inline `fun x ↦
   (μ.map (Xs 0)).real {x}` でも honest だが def 化を primary とする。
2. **`entropy` 参照を避けて `∑ negMulLog (lawPmf …)` を直接使う**: C1 の閉形式第2項 `H(p)` は
   `entropy μ (Xs 0)` (Bridge.lean) と定義一致だが、`entropy` 参照は `Shannon.Bridge` の重い import を
   引き込む。`∑ x, Real.negMulLog (lawPmf μ (Xs 0) x)` を直接書けば import を軽く保てる (両者 def 一致)。
   実装で import weight を確認し、`entropy` 参照が軽微なら recognizable 化のため切替可。
