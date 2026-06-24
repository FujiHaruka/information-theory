# Proof log — AEP (Phase A〜C 完了)

> **Parent plan**: [`docs/shannon/aep-moonshot-plan.md`](../shannon/aep-moonshot-plan.md)
> **File**: [`InformationTheory/Shannon/AEP.lean`](../../InformationTheory/Shannon/AEP.lean) (約 415 行)
> **Status**: Phase A ✅ / Phase B ✅ / Phase C ✅ (`measurableSet_typicalSet` ✅ / `typicalSet_prob_tendsto_one` ✅ / `typicalSet_card_le` ✅ — 第 2 セッションで `[∀ x, P(x) > 0]` 仮定追加で完了)
> **Verification**: `lake env lean InformationTheory/Shannon/AEP.lean` silent (0 sorry) / `lake build` 全体緑通過

## 質的観察

### 1. `IndepFun.comp` / `IdentDistrib.comp` で i.i.d. 性 lift は 1 行で済む

教科書の AEP 証明では「`Y i := −log P(X i)` という新しい列を作って強法則を適用」がもっとも泥臭い plumbing と思われていた。実際 Mathlib では:

- `IndepFun.comp (h : f ⟂ᵢ[μ] g) (hφ : Measurable φ) (hψ : Measurable ψ) : (φ ∘ f) ⟂ᵢ[μ] (ψ ∘ g)`
- `IdentDistrib.comp (h : IdentDistrib f g μ ν) (hu : Measurable u) : IdentDistrib (u ∘ f) (u ∘ g) μ ν`

の 2 補題で、それぞれ **1 行**で `Y i = pmfLog ∘ Xs i` への lift が完了 (`simpa [logLikelihood_eq_comp] using h.comp hpf hpf`)。Mathlib の IID-machinery が「真の Mathlib 流儀」(2 仮定を直接受ける + composition で lift) で **設計の sweet spot** を踏んでいることが確認できた。教訓: 自前 `IsIID` predicate を導入してから lift 補題を書くのは **明らかに余計な抽象化**。

### 2. `α : Fintype` 仮定下で `Real.log 0 = 0` 規約がサポート外点 plumbing をすべて吸収

最大の警戒ポイント (計画の Phase B-1 撤退ライン) だった「サポート外点 `P(x) = 0` で `−log 0 = +∞` になる handling」が **完全に不要**だった。理由:

- Mathlib `Real.log 0 := 0` (convention)
- 従って `pmfLog μ Xs x := −Real.log ((μ.map (Xs 0)).real {x}) = 0` for `x` outside support
- `Integrable.of_finite` は `[Finite α] [MeasurableSingletonClass α] [IsFiniteMeasure μ]` を要求し、有限離散空間上の **任意の関数** が integrable を返す (値が `+∞` になる心配なし)
- 期待値計算 `∫ ω, pmfLog μ Xs (Xs 0 ω) ∂μ = ∑ x, P(x) · pmfLog x = ∑ x, P(x) · (−log P(x))`、`P(x) = 0` の点で `0 · 0 = 0`、support 上で `Real.negMulLog P(x)` と一致 → `entropy` 定義に直結

教訓: Mathlib の `Real.log` / `negMulLog` の **convention は教科書 plumbing を素通りさせる方向に設計済み**。事前撤退ライン (`[∀ x, P(x) > 0]` 仮定追加) は不要だった。

### 3. `Pairwise ((· ⟂ᵢ[μ] ·) on Xs)` は parsing で詰まる、`Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j` で書く

Mathlib の `strong_law_ae_real` の **公式署名は `Pairwise ((· ⟂ᵢ[μ] ·) on X)`** で書かれているが、その表記をユーザコードで再現しようとすると `Function expected at … but this term has type Prop` エラーで詰まる。Lean 4 の anonymous lambda `(· ⟂ᵢ[μ] ·)` が `Function.onFun` の二項関数引数で再展開されないのが原因 (StrongLaw.lean の **`variable` scope 内での special elaboration** に依存している模様)。ユーザコード側は `Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j` の明示形で書く必要がある。`strong_law_ae_real` への引数渡しは elaborator が unify するので問題なし。

教訓: Mathlib 公式署名の verbatim 写経が必ずしも user code でそのまま通るとは限らない (`variable` scope の差で elaboration が変わる)。Subagent inventory で「verbatim 引数型を写す」要件は **Mathlib 内部 verbatim** であって、user code への落とし込みでは notation の現代化 (`fun i j => …` 形) を許容すべき。

### 4. `typicalSet_card_le` は `Real.exp_sum` 経由 (`Real.log_prod` 不使用) が plumbing 最小

第 2 セッション (`hpos : ∀ x, 0 < (μ.map (Xs 0)).real {x}` 仮定追加版) で `typicalSet_card_le` を埋めた際、当初想定の `Real.log_prod` 経路 (= `−log P^n(x) = −∑ log P(x_i)`、`P(x_i) ≠ 0` 仮定要) ではなく、**per-point の `Real.exp_log` + 全体の `Real.exp_sum`** で組み立てる方が短かった:

- `hexp_pmfLog : ∀ x, Real.exp (-pmfLog μ Xs x) = P x` ─ `pmfLog x := -log P(x)` の定義から `-pmfLog x = log P(x)` で `Real.exp_log (hpos x)` を 1 回。1 行
- `Real.exp (-(∑ i, pmfLog μ Xs (x i))) = ∏ i, P (x i)` ─ `Finset.sum_neg_distrib` で外側の `−` を inside に押し込んでから `Real.exp_sum`、最後に `Finset.prod_congr` + `hexp_pmfLog`。3 行

これで `Real.log_prod` の `≠ 0` 仮定との往復が不要。`hpos` 仮定は `Real.exp_log` の per-point 適用に 1 回しか触れず、log 側に出てこない。

**教訓: `log (∏ ...) = ∑ log ...` を解くより、 `exp (∑ ...) = ∏ exp(...)` を組むほうが Mathlib 流儀に合う**。前者は `≠ 0` per-point 仮定 + 結果が `log` 領域で扱いにくいが、後者は `Real.exp` が常に正なので不等式変形 (`Real.exp_lt_exp.mpr` / `Real.exp_pos`) も自然に閉じる。

### 5. `Real.log 0 = 0` 規約は **積分** には素通り、**card 上界** には追加仮定が必要

第 1 セッションで Phase B (probability AEP の期待値計算) はサポート外点を `Real.log 0 = 0` + `negMulLog 0 = 0` で素通りさせた。第 2 セッションで Phase C.3 (`typicalSet_card_le`) も同じ手で行けると当初仮説していたが、**実際は破綻**:

- Phase B (積分): サポート外点 `P(x)=0` で `pmfLog x = 0` ⇒ `pmfLog x · P(x) = 0`。期待値の和の項として **0 寄与** で自動的に消える。仮定不要
- Phase C.3 (card 下界): `x ∈ T` の各点で **下界量** $\prod P(x_i) \geq \exp(-n(H+\epsilon))$ が必要。サポート外点を含む $x \in T$ では $\prod P(x_i) = 0 < \exp(...)$ で **下界が成立しない**。Mathlib 規約で `pmfLog (\text{サポート外}) = 0` でも、$\exp(-\sum \text{pmfLog}) = \prod_{i: P(x_i)>0} P(x_i) > P^n(x) = 0$ となり、規約は逆向きの不等式を作り出す
- 別アプローチ: $f(x) := \exp(-\sum \text{pmfLog}\ x_i)$ をサポート外点込みで全和に使うと、$\sum_x f(x) = (1 + |\{x:P(x)=0\}|)^n$ となり $\neq 1$ で「下界量 × card ≤ 1」が閉じない

教訓: **Mathlib `Real.log 0 = 0` 規約の効力は方向性が強い**。期待値 / 積分のように **0 寄与で済む** 計算では追加仮定不要だが、card 上界のように **正の下界が必要**な計算では追加仮定 (`[∀ x, P(x) > 0]`) で潰すのが筋。Phase B での成功体験を Phase C.3 に流用しようとした第 1 セッションの所感は、 **計算の「寄与方向」が違う** ことを見落としていた。

## 撤退判断

### Phase C.3 (`typicalSet_card_le`) を本セッション撤退

**判断根拠**:

- Phase A〜C 緑通過 (= AEP 単体 publish ライン) のうち 5/6 主定理が緑通過 (Phase A: `jointRV` + `measurable_jointRV` / Phase B: `aep_ae` + `aep_inProbability` / Phase C: `measurableSet_typicalSet` + `typicalSet_prob_tendsto_one`)
- 残る `typicalSet_card_le` は:
  1. `pmfLog` の sum → `log (∏ P(x i))` 展開 (`Real.log_prod` + per-i `P(x i) ≠ 0` 仮定)
  2. `∑_{x : Fin n → α} ∏ P(x i) = 1` (Finset.prod_sum 経由 + `IsProbabilityMeasure (μ.map (Xs 0))` で `∑ P = 1`)
  3. `Real.exp` への往復 + 全 typical x の確率和 ≤ 1 から size bound
  の **3 段、見積もり 80〜120 行**
- **詰まりポイント**: サポート外点 `P(x) = 0` を含む block `x` の扱い。`Real.log_prod` の `∀ i, P(x i) ≠ 0` 仮定を満たすため `[∀ x : α, μ.map (Xs 0) {x} > 0]` 追加仮定が必要 → statement の弱体化 (= 仮定の追加) が必要だが、本セッションの「Phase A〜C 緑通過 = 完了」ラインを優先

**次セッションの方針**:

- option A: `[∀ x, μ.map (Xs 0) {x} > 0]` 仮定追加で `typicalSet_card_le` を埋める (+30〜50 行)
- option B: `typicalSet` 定義側で `pmfLog x = +∞` (= `P(x) = 0`) の点を typical 判定から排除する形に再設計 (+10〜20 行 / 教科書 statement との整合は要確認)
- option C: Phase D / E (源符号化定理) を先行、本 sorry を Phase D の中で必要になったタイミングで解消

**撤退ラインに到達したか?** ─ **到達**。Phase A〜C のうち主要 5/6 が緑通過、AEP 本体 (`aep_ae` + `aep_inProbability`) は完全に動く形で publishable。源符号化定理 weak converse の **block per-n 適用に必要な素材** (= AEP a.s. + 確率収束 + typical set measurability + typicality probability) はすべて揃っている。`typicalSet_card_le` は **encoder side achievability** (Phase E) で要となる補題なので、Phase D には影響しない。

## 完成補題一覧

| 補題 | Phase | 行 | 状態 |
|---|---|---|---|
| `jointRV` (def) | A | 47 | ✅ |
| `jointRV_apply` (simp) | A | 50 | ✅ |
| `measurable_jointRV` | A | 53 | ✅ |
| `pmfLog` (def) | B | 67 | ✅ |
| `measurable_pmfLog` | B | 70 | ✅ |
| `logLikelihood` (def) | B | 75 | ✅ |
| `logLikelihood_eq_comp` | B | 78 | ✅ |
| `measurable_logLikelihood` | B | 81 | ✅ |
| `integrable_logLikelihood` | B | 89 | ✅ |
| `integral_logLikelihood_zero` | B | 102 | ✅ |
| `identDistrib_logLikelihood` | B | 130 | ✅ |
| `indepFun_logLikelihood` | B | 137 | ✅ |
| `aep_ae` | B | 152 | ✅ |
| `aep_inProbability` | B | 184 | ✅ |
| `typicalSet` (def) | C | 222 | ✅ |
| `mem_typicalSet_iff` | C | 227 | ✅ |
| `measurableSet_typicalSet` | C | 233 | ✅ |
| `typicalSet_card_le` | C | 250 | ✅ (第 2 セッションで `hpos` 仮定追加で完了) |
| `typicalSet_prob_tendsto_one` | C | 264 | ✅ |
