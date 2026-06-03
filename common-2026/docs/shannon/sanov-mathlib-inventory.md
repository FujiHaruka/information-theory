# Sanov の定理 (B-1) Mathlib + 既存 plumbing インベントリ

> 作業: Phase 0 — 既存基盤の調査と Mathlib delta の特定。本シードカードは [`sanov-moonshot-plan.md`](sanov-moonshot-plan.md) の Phase 0 成果物。

## 結論

- Mathlib に **`Sanov`, `empiricalMeasure`, `LargeDeviation` 系は無い** (loogle で `Found 0 declarations`)。Method of types も独立 API なし。**全て自前構築**。
- ただし**主定理は既存 Stein converse `steinTypicalSet_Q_prob_le` のロジック特化で 60–100 行**。type class 定義 + point-wise ratio plumbing 80–150 行。合計 **~200–300 行で A 形完成見込み**。

## 既存基盤 (InformationTheory)

| ファイル | 識別子 | 役割 |
|---|---|---|
| `InformationTheory/Shannon/Stein.lean:53` | `llrPmf P Q : α → ℝ` | `log P{x} - log Q{x}` — Sanov の point-wise ratio 評価で使う原型 |
| `InformationTheory/Shannon/Stein.lean:341` | `steinTypicalSet_Q_prob_le` | **本テンプレ**: `Q^n(T) ≤ exp(-n(K-ε))` を「片側 inequality」で示す。Sanov A 形は **両側 equality** に特化 |
| `InformationTheory/Shannon/Stein.lean:368` | `h_pi_singleton_Q : (Pi Q).real {x} = ∏ Q.real {x i}` (inline) | Pi-measure singleton の積分解 (Mathlib `Measure.pi_singleton` + `ENNReal.toReal_prod`) |
| `InformationTheory/Shannon/Stein.lean:420` | `h_exp_neg_llr` (inline) | `exp(-llrPmf P Q x) = Q.real{x}/P.real{x}` |
| `InformationTheory/Shannon/Stein.lean:430` | `h_prod_ratio` (inline) | `∏ Q/P = exp(-∑ llrPmf)` |
| `InformationTheory/Shannon/MaxEntropy.lean:123` | `klDiv_uniformOn_univ_toReal_eq` | `(klDiv P U).toReal = ∫ llr P U ∂P` 経由で `klDiv.toReal` を finite alphabet sum に展開する **template** |
| `InformationTheory/Shannon/MIChainRule.lean:268` | `klDiv_pi_eq_sum` | i.i.d. でない `Q^n` には不使用、ただし `Measure.pi` 同型変形のテンプレ |
| `InformationTheory/Shannon/AEP.lean:229` | `typicalSet`, `typicalSet_card_le` | type class **size bound** との対比 (本 plan A 形は size bound を回避するが Phase D で必要になる場合の参照) |

## 既存 Mathlib API (使用候補)

### KL divergence — `Mathlib/InformationTheory/KullbackLeibler/Basic.lean`

| 行 | 識別子 | 用途 |
|---|---|---|
| 164 | `toReal_klDiv_of_measure_eq (h : μ ≪ ν) (h_eq : μ univ = ν univ) : (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ` | `klDivSumForm = (klDiv P̂ Q).toReal` の等値性証明 — 両方 prob measure ⇒ `univ` 一致 |
| (有り) | `klDiv_self`, `klDiv_eq_zero_iff` | 端 case |
| (Mathlib) | `llr_def`: `llr μ ν x = Real.log (μ.rnDeriv ν x).toReal` | Bochner integral 形 (MaxEntropy.lean:202 でテンプレ済) |

### Measure.pi — `Mathlib/MeasureTheory/Constructions/Pi.lean`

| 識別子 | 用途 |
|---|---|
| `Measure.pi_singleton` (Stein で使用済 line 372) | `(Measure.pi μs) {x} = ∏ i, μs i {x i}` |
| `Fintype.piFinset_univ` | `Fintype.piFinset (fun _ => Finset.univ) = Finset.univ` |
| `Finset.sum_prod_piFinset` | `∑ x ∈ piFinset, ∏ i, f i (x i) = ∏ i, ∑ a, f i a` |

### Big operators

| 識別子 | 用途 |
|---|---|
| `Real.exp_sum` | `exp(∑ i, f i) = ∏ i, exp(f i)` |
| `Real.exp_log` | `0 < x → exp(log x) = x` |
| `Real.log_prod` | `log(∏ i, f i) = ∑ i, log(f i)` (sign-positive |
| `Finset.prod_pow` | `∏ i, x ^ f i = x ^ ∑ i, f i` (constant base 形) |

## 設計判断

### 1. type class 定義の形

textbook では `T(P̂) = { x | empirical(x) = P̂ }` で `P̂ : 𝒫(α)` を **n の倍数なるパラメータ**から拾う。本実装では **measure-valued** `P̂ : Measure α` を直接受け、`x ∈ typeClass P̂ n ↔ ∀ a, #{i | x i = a} = n · P̂.real {a}`。`P̂` が「n に対し有効な type」でない場合 (例: `n · P̂.real {a}` が整数でない) は `typeClass P̂ n = ∅` となり、主定理は `0 ≤ exp(-n·D)` で trivially 成立。

### 2. `klDivSumForm` を主定理 LHS に使う

主定理 `typeClass_Qn_le` は `klDivSumForm P̂ Q := ∑ a, P̂.real{a} * (log P̂.real{a} - log Q.real{a})` の形で書き、`.toReal` 形は corollary。**理由**:
- 内側証明は `∑ a` の代数操作 (= `∑ i, log(Q/P̂)(x_i) = -n · ∑ a, P̂(a) · log(Q/P̂)(a)`) で完結
- `klDiv.toReal` の Bochner-integral 展開を毎回挟むと plumbing が増える
- 等値性 `klDivSumForm = (klDiv P̂ Q).toReal` (`klDivSumForm_eq_toReal_klDiv`) は MaxEntropy.lean:123 のテンプレで 50–80 行で立つ

### 3. ratio 評価の集約形

```
(∏ Q(x_i)) / (∏ P̂(x_i)) = ∏ (Q/P̂)(x_i) = exp(∑ i, log(Q/P̂)(x_i))
                       = exp(∑ a, typeCount(x,a) · log(Q/P̂)(a))   ← 集約
                       = exp(n · ∑ a, P̂(a) · log(Q/P̂)(a))         ← typeClass 仮定
                       = exp(-n · klDivSumForm P̂ Q)
```

集約の鍵: `∑ i : Fin n, f (x i) = ∑ a : α, (typeCount x a) * f a`。これは Mathlib の標準補題 `Finset.sum_comm`-変形 (実装時に inventory 拡張、見つからなければ ad-hoc 補題で 10–15 行)。

### 4. 撤退ライン

- Phase A.4 (ratio 補題) で 200 行超えたら deferred 候補
- Phase B (主定理) で `Q^n(T) = exp(-n·D) · P̂^n(T)` の等式変形が詰まったら、Stein の `steinTypicalSet_Q_prob_le` の `≤` 版に fallback (`exp(-n·D) · P̂^n(T) ≤ exp(-n·D) · 1`)

## Phase 0 終了時の判断

**進行可**: 既存 `steinTypicalSet_Q_prob_le` (140 行) のロジックがそのまま使え、ratio plumbing は 80–150 行で書けると見込み。**B 形 LDP は deferred** で本 plan では A 形 + (optional) Phase D corollary までを scope とする。
