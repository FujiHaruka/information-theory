# Stein の補題 ムーンショット計画 🌙

**Status**: CLOSED ✅ — done (Ch.11 Stein; `stein_lemma` sandwich form proof done, 0 sorry; Phase C/D implemented in child `stein-converse-plan.md`, strict form in `strong-stein-moonshot-plan.md`).

<!--
雛形メモ:
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 判断ログは append-only。Phase 中の方針変更・撤退・当初仮定の修正を記録
- `rg "^- \[ \]"` で残タスク横断 grep、`rg "🔄"` でピボット箇所だけ拾える
-->

> **Status (2026-05-11)**: 起草。シードカード [Seed 5](../moonshot-seeds.md#seed-5-stein-の補題仮説検定の最適-error-exponent) を膨らませた 3〜4 週間ムーンショット。AEP (Seed 4 Phase A〜C) 完了を起点に、漸近 plumbing の 70〜80% を AEP 既存補題の **2 分布化**で再利用する設計。
> **撤退ライン**: Phase A〜C 完了 (= Stein lower bound = achievability) で publish 価値あり。Phase D (upper bound = converse + 統合形) はそこから separable に切り出せる。
>
> **実態整合 (2026-05-20): DONE-UNCOND (sandwich 形)** — Phase A〜B (achievability) に加え、sandwich 形 (`K ≤ liminf ∧ limsup ≤ K/(1-ε)`、std binders のみ、pass-through なし) で **完了**。(module-restructure で `Stein.lean` は 3 分割され、当時の単一 `stein_lemma` は 2 本の bound `steinOptimalBeta_log_ge_of_achievability` / `steinOptimalBeta_log_le_of_converse` (`InformationTheory/Shannon/Stein/OptimalExponent.lean`) に分かれた。) Phase C/D は子 plan `stein-converse-plan.md` で実装済 (本 plan の Goal 部の strict `Tendsto` 形は子 plan で sandwich に着地、strict 形は `strong-stein-moonshot-plan.md` の `stein_strong_lemma` で別途達成)。Stein 系 0 sorry / 0 `:=True`。converse は `stein_converse_finite_n` (`InformationTheory/Shannon/Stein/Converse.lean`)。

## 進捗

- [x] Phase 0 — Mathlib + InformationTheory (AEP 含む) API インベントリ ✅ → [`stein-mathlib-inventory.md`](stein-mathlib-inventory.md)
- [x] Phase A — log-likelihood ratio plumbing (`llrPmf` / `logLikelihoodRatio` / Stein 強法則) + i.i.d. 化 ✅ (A.7 `klDiv_pi_eq_n_smul` は B.4 で迂回 → Phase C で実装予定)
- [x] Phase B — Stein lower bound (achievability): typicality 構成 → `-(1/n) log β_n ≥ klDiv - δ` ✅ (**publish ライン到達 2026-05-11**)
- [ ] Phase C — Stein upper bound (converse): 任意の検定 → `-(1/n) log β_n ≤ klDiv + δ` 📋 (撤退、別 plan に切り出し)
- [ ] Phase D — 統合形 `stein_lemma`: 両側 bound → `Tendsto` 形 lim 結論 📋 (撤退、Phase C 完了後)

## ゴール / Approach

**最終到達点**: `klDiv P Q < ∞` のもとで仮説検定の最適 type-II error が KL の指数で減衰:

```lean
theorem stein_lemma
    {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q)
    (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto
      (fun n : ℕ => -(1 / n : ℝ) * Real.log (steinOptimalBeta P Q n ε))
      Filter.atTop
      (𝓝 (klDiv P Q).toReal)
```

ここで `steinOptimalBeta P Q n ε := sInf { (Q^⊗n) sᶜ | s ⊆ (Fin n → α), MeasurableSet s ∧ (P^⊗n) sᶜ ≤ ε }` (= optimal type-II error subject to type-I ≤ ε)。

**Approach の中核 (4 段)**:

1. **(a) AEP plumbing の 2 分布化** ─ `pmfLog μ Xs` (1 分布) → `llrPmf P Q` (2 分布、`Real.log (P.real{x} / Q.real{x})`)、`logLikelihood` → `logLikelihoodRatio`、`aep_ae`/`aep_inProbability` → `stein_strong_law` (`(1/n) Σ llrPmf P Q (Xs i ω) → (klDiv P Q).toReal`)。**新規 plumbing は 2 本のみ**: (i) `integral_llrPmf_under_P = (klDiv P Q).toReal` (LR 期待値 = KL)、(ii) `klDiv_pi_eq_n_smul` (chain rule の Pi 形)
2. **(b) Stein-typical set を 2 分布で定義** ─ `T_ε^n := { x : Fin n → α | |(1/n) Σ llrPmf P Q (x i) - (klDiv P Q).toReal| < ε }`。AEP `typicalSet_card_le` の Q 測度版で `Q^n(T_ε^n) ≤ exp(-n · (klDiv - ε))`、`typicalSet_prob_tendsto_one` の P 版で `P^n(T_ε^n) → 1`
3. **(c) Lower bound (achievability)** ─ rejection region として **Stein-typical set を採用**、`α_n = P^n(T_ε^{n,c}) → 0` ≤ ε for large n、`β_n = Q^n(T_ε^n) ≤ exp(-n · (klDiv - ε))`。Neyman-Pearson 補題不要、具体的 LRT 構成で完結
4. **(d) Upper bound (converse)** ─ 任意の α-level 検定 `s` (`P^n(s^c) ≤ ε`) に対し `klDiv P^n Q^n = n · klDiv P Q` (chain rule の Pi 形) と data processing 不等式 (本 project 既存 DPI) で `Q^n(s) ≥ exp(-n · klDiv - δ_n)` を導出。**ここでも Neyman-Pearson 不要**

**撤退ライン**: Phase A〜C 緑通過時点で **Stein achievability 単体として publish OK** (= 「ある検定で `β_n ≤ exp(-n · klDiv)`」)。Phase D の converse で詰まる場合は次セッションに切り出し。本 plan は **lower bound 単体でも価値が残る**設計。

**Approach 図**:

```
Phase 0  : Mathlib + AEP インベントリ                          ← 1 ターン
           ──────────────────────────────────────────
Phase A  : log-likelihood ratio plumbing + Pi 化 KL chain rule  ← 山場 (1)、1〜1.5 週
           ──────────────────────────────────────────
Phase B  : Stein lower bound (achievability)                    ← 0.5〜1 週
           ←──── 撤退ライン (Stein achievability publish) ────→
           ──────────────────────────────────────────
Phase C  : Stein upper bound (converse)                         ← 山場 (2)、1〜1.5 週
           ──────────────────────────────────────────
Phase D  : 両側 bound → `Tendsto` 形 lim 結論                  ← 0.5 週
```

**ファイル構成 (Phase D 終了時想定)**:

```
InformationTheory/Shannon/
  Stein.lean           ← Phase A〜D 全体 (新規ファイル、AEP.lean を import)
  AEP.lean             ← 既存、変更なし (Stein で参照)
```

撤退時 (Phase A〜B) は `InformationTheory/Shannon/Stein.lean` の Phase C 以降に `sorry` を残して close、Phase C/D は別 plan に切り出し。

---

## Phase 0 — Mathlib + AEP API インベントリ

### スコープ

`docs/shannon/stein-mathlib-inventory.md` を起草、6 軸 (`klDiv` API / `llr` 可測性 / hypothesis testing formalism / AEP 補題再利用 / `Filter.liminf` / Neyman-Pearson) を裏取り。

### 進捗

- [x] サブ計画起草 (本ファイル + inventory file 同時、2026-05-11)
- [ ] Phase A 着手前の不確実性ランクが low (= inventory 結論で skeleton が書ける状態)

### Done 条件

- 「`klDiv_compProd_eq_add` の verbatim 署名」が inventory に記録 → ✅ 起草段階で確定
- 「Stein / Neyman-Pearson / hypothesis testing は Mathlib 不在」を裏取り → ✅ `rg` 0 件確認
- AEP 既存補題の 2 分布化マッピング表 → ✅ 13 補題分作成
- Phase A skeleton (`InformationTheory/Shannon/Stein.lean` の sorry-driven 出だし) が書ける状態 → 本 plan 起草時点で **GO**

### 工数感

1 ターン (10〜15 分)。本起草で完。

---

## Phase A — log-likelihood ratio plumbing + Pi 化 KL chain rule 📋

### スコープ

```lean
namespace InformationTheory.Shannon.Stein

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                    [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Alphabet-side log-likelihood ratio `log (P(x) / Q(x))`. AEP `pmfLog` の 2 分布化。 -/
noncomputable def llrPmf (P Q : Measure α) : α → ℝ :=
  fun x => Real.log (P.real {x}) - Real.log (Q.real {x})

/-- Per-symbol log-likelihood ratio `log P(Xs i ω) − log Q(Xs i ω)`. AEP `logLikelihood` の 2 分布版。 -/
noncomputable def logLikelihoodRatio
    (P Q : Measure α) (Xs : ℕ → Ω → α) (i : ℕ) : Ω → ℝ :=
  fun ω => llrPmf P Q (Xs i ω)

/-- LR 期待値 = KL: `∫ ω, logLikelihoodRatio P Q Xs 0 ω ∂μ = (klDiv P Q).toReal` ただし
  `μ.map (Xs 0) = P` を仮定。AEP `integral_logLikelihood_zero` の 2 分布化。 -/
theorem integral_logLikelihoodRatio_under_P
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hMap : μ.map (Xs 0) = P)
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x}) :
    ∫ ω, logLikelihoodRatio P Q Xs 0 ω ∂μ = (klDiv P Q).toReal

/-- Stein 強法則: `(1/n) Σ_{i<n} logLikelihoodRatio P Q Xs i ω → (klDiv P Q).toReal` a.s.
AEP `aep_ae` の 2 分布化。 -/
theorem stein_strong_law
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P)
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x}) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range n, logLikelihoodRatio P Q Xs i ω) / n)
      Filter.atTop
      (𝓝 (klDiv P Q).toReal)

/-- KL chain rule の Pi 形: `klDiv (Π P) (Π Q) = n · klDiv P Q`.
`klDiv_compProd_eq_add` + `klDiv_compProd_left` を induction で組み合わせ。 -/
theorem klDiv_pi_eq_n_smul
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) :
    klDiv (Measure.pi (fun _ : Fin n => P)) (Measure.pi (fun _ : Fin n => Q))
      = (n : ℝ≥0∞) * klDiv P Q

end InformationTheory.Shannon.Stein
```

### 鍵となる作業

- [ ] **(A.1) `llrPmf` 定義 + 基本 measurability** ─ AEP `pmfLog` の構造をそのまま 2 分布化、`measurable_of_finite` で measurability。10〜20 行
- [ ] **(A.2) `logLikelihoodRatio` 定義 + measurability + integrability** ─ AEP `logLikelihood` 系の 2 分布化、`Integrable.of_finite` で integrability、`hQpos` 仮定下で `−log 0` を回避 (= `llrPmf` がサポート外で finite ない問題は **`hPQ : P ≪ Q`** で支持外点が `P` 側で確率 0)。30〜50 行
- [ ] **(A.3) `integral_logLikelihoodRatio_under_P = (klDiv P Q).toReal`** ─ Phase A の中核 plumbing。AEP `integral_logLikelihood_zero` の証明骨格を 2 分布化、`integral_map` + `integral_fintype` + `Bridge.lean` の `klDiv_discrete_toReal_eq_sum` (`InformationTheory/Shannon/Bridge.lean:209`) **再利用**。**`klDiv_discrete_toReal_eq_sum` は Bridge.lean に既存** (有限アルファベット discrete KL の sum 形展開) → 直接 import 可。50〜80 行
- [ ] **(A.4) `IdentDistrib` / `IndepFun` lift** ─ AEP `identDistrib_logLikelihood` / `indepFun_logLikelihood` を 2 分布版に複製、`IdentDistrib.comp` / `IndepFun.comp` を `llrPmf P Q` で 1 回呼ぶだけ。20〜30 行
- [ ] **(A.5) `stein_strong_law`** ─ `strong_law_ae_real` を `Y i := logLikelihoodRatio P Q Xs i` で 1 回呼び、`integral_logLikelihoodRatio_under_P` で期待値書き換え。AEP `aep_ae` の構造そのまま。15〜20 行
- [ ] **(A.6) `stein_inProbability`** ─ a.s. → 確率収束 lift、AEP `aep_inProbability` の構造そのまま (`tendstoInMeasure_of_tendsto_ae`)。30〜50 行
- [ ] **(A.7) `klDiv_pi_eq_n_smul`** ─ Phase A の山場 1。`Fin n` 上 induction、`Measure.pi (Fin (n+1))` を `MeasurableEquiv.piFinSuccAbove` 経由で `α × Π_{Fin n} α` に reshape、`Measure.compProd_const` で compProd 形に乗せ、`klDiv_compProd_eq_add` (chain rule) と `klDiv_compProd_left` (左因子退化) で base + step を組む。**`InformationTheory/Shannon/MutualInfo.lean:80` `klDiv_prod_const_left` (本 project 既存) も再利用候補**。40〜80 行

### Done 条件

- 上記 7 項目が `lake env lean InformationTheory/Shannon/Stein.lean` で silent
- skeleton-driven で `llrPmf` → `logLikelihoodRatio` → `integral_logLikelihoodRatio_under_P` → `stein_strong_law` → `klDiv_pi_eq_n_smul` の sorry を割る順序

### 工数感

1〜1.5 週。**最大リスク**: (A.7) `klDiv_pi_eq_n_smul` の Pi 化 induction。Mathlib に直接補題は無い (`klDiv (Measure.pi P) (Measure.pi Q)` 形は loogle 0 件) が、`klDiv_compProd_eq_add` + `MeasurableEquiv.piFinSuccAbove` で組める見込み。ただし `Kernel.const _ ν` を仲介とする plumbing の往復が想定より多い可能性あり。

### 撤退ライン (Phase A 内)

- (A.7) で 5〜7 日溶ける場合 → **Phase B / C を `klDiv_pi_eq_n_smul` 不要なルートで attack**:
  - Phase B (lower bound) は typicality 構成だけで `klDiv_pi_eq_n_smul` 不要 (`Q^n(T_ε^n) ≤ exp(-n(klDiv - ε))` は typicality 定義から直接、KL chain rule は不要)
  - Phase C (upper bound) で `klDiv P^n Q^n = n · klDiv P Q` が必須なため、撤退ルートは Phase B のみ完了 → Stein achievability 単体で publish

---

## Phase B — Stein lower bound (achievability) 📋

### スコープ

```lean
namespace InformationTheory.Shannon.Stein

/-- Stein-typical set: blocks `x : Fin n → α` whose empirical LR is within `ε`
of the true KL divergence. AEP `typicalSet` の 2 分布版。 -/
noncomputable def steinTypicalSet
    (P Q : Measure α) (n : ℕ) (ε : ℝ) : Set (Fin n → α) :=
  { x | |(∑ i : Fin n, llrPmf P Q (x i)) / n - (klDiv P Q).toReal| < ε }

theorem measurableSet_steinTypicalSet
    (P Q : Measure α) (n : ℕ) (ε : ℝ) :
    MeasurableSet (steinTypicalSet P Q n ε)

/-- P-side typicality: `P^n(T_ε^n) → 1` as `n → ∞` (under i.i.d. with `μ.map (Xs 0) = P`). -/
theorem steinTypicalSet_P_prob_tendsto_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P)
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ => μ {ω | jointRV Xs n ω ∈ steinTypicalSet P Q n ε})
      Filter.atTop (𝓝 1)

/-- Q-side mass bound: `Q^n(T_ε^n) ≤ exp(-n · (klDiv - ε))`. -/
theorem steinTypicalSet_Q_prob_le
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQpos : ∀ x : α, 0 < Q.real {x})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((Measure.pi (fun _ : Fin n => Q)) (steinTypicalSet P Q n ε)).toReal
      ≤ Real.exp (-((n : ℝ) * ((klDiv P Q).toReal - ε)))

/-- Stein lower bound (achievability): the Stein-typical set provides an α-level
test whose type-II error decays as `exp(-n · (klDiv - ε))`. -/
theorem stein_achievability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P)
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ s : Set (Fin n → α), MeasurableSet s ∧
        ((Measure.pi (fun _ => P)) sᶜ).toReal ≤ ε ∧
        -((1 : ℝ) / n) * Real.log ((Measure.pi (fun _ => Q)) s).toReal
          ≥ (klDiv P Q).toReal - δ

end InformationTheory.Shannon.Stein
```

### 鍵となる作業

- [ ] **(B.1) `steinTypicalSet` 定義 + `measurableSet_steinTypicalSet`** ─ AEP `typicalSet` / `measurableSet_typicalSet` の 2 分布化。`Set.toFinite.measurableSet` で measurability 自動。10〜20 行
- [ ] **(B.2) `steinTypicalSet_P_prob_tendsto_one`** ─ AEP `typicalSet_prob_tendsto_one` の構造そのまま (`stein_inProbability` から余事象で導出)。30〜50 行
- [ ] **(B.3) `steinTypicalSet_Q_prob_le`** ─ Phase B の中核 plumbing。AEP `typicalSet_card_le` の **Q 測度版**: `x ∈ T_ε^n` から `(1/n) Σ llrPmf P Q (x i) > klDiv - ε` (= 上界側)、`Q^n({x}) = Π_i Q.real{x_i} ≤ Π_i P.real{x_i} · exp(-(klDiv - ε)) = P^n({x}) · exp(-n(klDiv - ε))`、`P^n` は確率測度なので `Q^n(T_ε^n) ≤ exp(-n(klDiv - ε))`。AEP `typicalSet_card_le` の Real.exp / Real.log 往復 (90 行) を **両側不等式で再演**。70〜120 行
- [ ] **(B.4) `stein_achievability`** ─ B.1〜B.3 の組み合わせ。`s := { ω | jointRV Xs n ω ∉ steinTypicalSet P Q n ε }` (= P-側の余事象を rejection region) ではなく、**`s := { x | x ∉ steinTypicalSet P Q n ε }`** を `Fin n → α` 側で取る (Pi 測度上で評価)。`α-level` は B.2 から、`β-bound` は B.3 から。30〜50 行

### Done 条件

- 上記 4 項目が silent
- proof-log + metrics 取得済み (`docs/proof-logs/proof-log-stein-A.md`, `docs/metrics/stein-A.{manifest,metrics}.{json,md}`)
- **★ 撤退ライン到達時点 (Phase B 完) で publish 価値あり ★**

### 工数感

0.5〜1 週。Phase A が片付けば組み合わせ + Pi 値 reshape のみ。**最大リスクは (B.3)** の `Real.exp / Real.log` 両側不等式。AEP `typicalSet_card_le` で先例があり (90 行)、Stein 版もほぼ同手で済む見込み。

### 撤退ライン (Phase B 内)

- (B.3) で AEP card_le の路線が破綻 → `Real.exp / Real.log` 経路を `llr` (Mathlib 既存) で書き直し、`Bridge.lean:209` `klDiv_discrete_toReal_eq_sum` の経路に乗せる

### **★★★ Phase A〜B 完了 = Stein achievability publish ライン ★★★**

ここで `InformationTheory/Shannon/Stein.lean` が `stein_achievability` (= 「ある検定で `β_n ≤ exp(-n · klDiv + n · δ)`」) を提供する状態。Cover-Thomas Theorem 11.8.3 の **半分**。**Phase C 不達でもムーンショット成立**。proof-log + metrics 取得 + Phase C 切り出し判断はここで実施。

---

## Phase C — Stein upper bound (converse) 📋

### スコープ

```lean
namespace InformationTheory.Shannon.Stein

/-- Stein upper bound (converse): for any α-level test, the type-II error is at
least `exp(-n · klDiv - n · δ)`. -/
theorem stein_converse
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ s : Set (Fin n → α), MeasurableSet s →
        ((Measure.pi (fun _ : Fin n => P)) sᶜ).toReal ≤ ε →
        -((1 : ℝ) / n) * Real.log ((Measure.pi (fun _ : Fin n => Q)) s).toReal
          ≤ (klDiv P Q).toReal + δ

end InformationTheory.Shannon.Stein
```

### 鍵となる作業

- [ ] **(C.1) 任意検定 `s` から `klDiv P^n|_s Q^n|_s` を取り出す** ─ data processing 不等式: 検定 `s` (= 二値分割) で得られる Bernoulli 分布のペア `(P^n(s), 1 - P^n(s))` vs `(Q^n(s), 1 - Q^n(s))` の KL は `klDiv P^n Q^n` 以下。**本 project の `InformationTheory/Shannon/DPI.lean` (DPI 既存) を再利用候補**。30〜60 行
- [ ] **(C.2) Bernoulli KL の評価**: `klDiv (Bernoulli p₁) (Bernoulli p₂) ≥ -h(p₁) + p₁ · log(1/p₂) + (1-p₁) · log(1/(1-p₂))` の形を直接展開、または `klDiv_compProd_eq_add` + `klDiv_eq_zero_iff` の組み合わせで **下から `(1-ε) · log((1-ε)/Q^n(s)) - h(ε)`** に押す。30〜60 行
- [ ] **(C.3) `klDiv P^n Q^n = n · klDiv P Q` の適用** (= Phase A の `klDiv_pi_eq_n_smul`) で `n · klDiv P Q ≥ (1-ε) · log((1-ε)/Q^n(s)) - h(ε)` → `Q^n(s) ≥ (1-ε) · exp(-(n · klDiv P Q + h(ε)) / (1-ε))` → `-(1/n) log Q^n(s) ≤ klDiv P Q + δ_n` で `δ_n → 0`。30〜60 行
- [ ] **(C.4) `∀ᶠ n in atTop` への乗せ替え**: 上の `δ_n → 0` から `δ_n ≤ δ` を `∀ᶠ n` の形で。20〜30 行

### Done 条件

- 上記 4 項目が silent
- proof-log + metrics 取得済み

### 工数感

1〜1.5 週。**最大リスク**: (C.1) data processing 不等式の Bernoulli reduction の plumbing 量。本 project DPI が `Fintype` 値 RV → `Fintype` 値 RV で書かれているため、Pi 値 → `Fin 2` 値 (= 検定の指示関数) で直接乗るか確認。乗らなければ Bernoulli KL を直接計算する別ルート。

### 撤退ライン (Phase C 内)

- (C.1) DPI 経由が plumbing-heavy → Bernoulli KL を直接 `klFun` 経由で計算する形 (`klDiv_eq_lintegral_klFun_of_ac`) に切り替え。AC は `(P^n s, P^n s^c) ≪ (Q^n s, Q^n s^c)` で済む
- (C.3) で `klDiv_pi_eq_n_smul` (Phase A.7) の plumbing が破綻していた場合 → Phase A.7 を Phase C 内で再実装、または **本 plan 全体を Phase B (lower bound) のみで close**

---

## Phase D — 統合形 `stein_lemma`: 両側 bound → `Tendsto` 形 lim 結論 📋

### スコープ

```lean
namespace InformationTheory.Shannon.Stein

/-- Optimal type-II error subject to type-I ≤ ε. -/
noncomputable def steinOptimalBeta
    (P Q : Measure α) (n : ℕ) (ε : ℝ) : ℝ :=
  sInf { ((Measure.pi (fun _ : Fin n => Q)) s).toReal
        | (s : Set (Fin n → α)) (_ : MeasurableSet s)
          (_ : ((Measure.pi (fun _ : Fin n => P)) sᶜ).toReal ≤ ε) }

/-- **Stein's lemma**: the optimal type-II error of an α-level test for `H_0 : P` vs
`H_1 : Q` decays exactly as `exp(-n · klDiv P Q)`. -/
theorem stein_lemma
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P)
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto
      (fun n : ℕ => -(1 / n : ℝ) * Real.log (steinOptimalBeta P Q n ε))
      Filter.atTop
      (𝓝 (klDiv P Q).toReal)

end InformationTheory.Shannon.Stein
```

### 鍵となる作業

- [ ] **(D.1) `steinOptimalBeta` 定義 + 基本性質 (well-defined / nonempty / 0 ≤ · ≤ 1)** ─ Pi 測度の値域から `0 ≤ steinOptimalBeta ≤ 1`。`s := Set.univ` で trivially `α-level` を満たすため inf は空集合でない。15〜30 行
- [ ] **(D.2) `stein_achievability` (Phase B) → `liminf` 形 lower bound for `steinOptimalBeta`** ─ achievability の `s` が inf 候補を 1 つ提供 ⇒ `steinOptimalBeta P Q n ε ≤ Q^n(s) ≤ exp(-n(klDiv - δ))`。20〜40 行
- [ ] **(D.3) `stein_converse` (Phase C) → `limsup` 形 upper bound for `steinOptimalBeta`** ─ converse の statement「任意の検定 ⇒ `Q^n(s) ≥ exp(-n(klDiv + δ))`」から `steinOptimalBeta P Q n ε ≥ exp(-n(klDiv + δ))`。20〜40 行
- [ ] **(D.4) 両側 bound → `Tendsto` 形に統合** ─ `Filter.tendsto_atTop_of_eventually_le_and_ge` 系 + (D.2) (D.3)。`-(1/n) log` の単調性 (decreasing) 取り扱いに注意。30〜50 行

### Done 条件

- 上記 4 項目が silent
- 教科書 Stein (Cover-Thomas Theorem 11.8.3) と一致する statement
- proof-log + metrics 取得済み

### 工数感

0.5 週。Phase B + Phase C の素材を組み合わせるだけ、新規 plumbing は最小限。

### 撤退ライン (Phase D 内)

- (D.4) の `Tendsto` 形統合で `Filter.tendsto_of_eventually_*` の使い方が想定外 → **`liminf = limsup = klDiv` の 2 段で結ぶ路線**に切り替え (`Tendsto.liminf_eq` の逆方向、`liminf_eq_limsup ↔ Tendsto`)

---

## 失敗判定 / 撤退ライン (全体)

| 撤退ポイント | 判定基準 | アクション |
|---|---|---|
| Phase 0 で Stein / Neyman-Pearson が Mathlib にあった | 0 件確認済み (本 inventory) | 不該当 |
| Phase A の `klDiv_pi_eq_n_smul` で 5〜7 日溶ける | (A.7) 進捗 0 | Phase B (achievability) のみで close、Phase C/D は別 plan |
| Phase B の `steinTypicalSet_Q_prob_le` で 4〜5 日溶ける | (B.3) Real.exp / Real.log 両側不等式が破綻 | `llr` (Mathlib 既存) + `Bridge.lean` `klDiv_discrete_toReal_eq_sum` 経路に切替 |
| **Phase A〜B 完了 (= Stein achievability)** | lower bound silent | **★ 撤退ライン: Phase C は次セッション ★** ─ 別 plan に切り出し、本 plan は close |
| Phase C の DPI reduction (C.1) で 5〜7 日溶ける | Bernoulli KL の自前計算経路へ | Bernoulli KL を `klDiv_eq_lintegral_klFun_of_ac` 直接展開で計算、別 sub-plan に切り出し |
| Phase D の `Tendsto` 形統合 (D.4) で詰まる | Mathlib `Filter.tendsto_*` API の不足 | `liminf = limsup` 2 段経路、または `lim` 形 statement に弱体化 (= `Tendsto` を `liminf` のみに弱める) |

どのケースも proof-log に **正直に**記録。Mathlib の薄い箇所を可視化したという結果自体がデモのデータポイント。

---

## 工数見積もり総括 (シードからの改訂)

シード見積: **3〜4 週間 / 600〜900 行 / 中〜高リスク**。AEP 完了 (= 12 補題が再利用可能) を取り込んだ改訂:

| 経路 | 工数 | 行数 | リスク |
|---|---|---|---|
| Phase A〜B (Stein achievability) | **1.5〜2.5 週** | **300〜500 行** | **中** (Phase A.7 の Pi 化 KL chain rule が唯一の実質新規 plumbing) |
| Phase A〜D (Stein 統合形まで) | **3〜4 週** | **600〜900 行** | **中〜高** (シード通り、Phase C の DPI reduction が山場) |
| Phase C 単独 (Stein achievability 後の追加分) | 1〜1.5 週 | 200〜400 行 | 中 (本 project DPI 流用度次第) |
| Phase D 単独 (Phase C 後の追加分) | 0.5 週 | 100〜200 行 | 低 (組み合わせのみ) |

**AEP 完了による短縮効果**: シードの「800〜1500 行 / 4〜6 週間」想定の **約半分**で Stein achievability が立つ見込み。AEP plumbing の 70〜80% 再利用が効く。

撤退時 (Phase A〜B) でも **シード「600〜900 行 / 3〜4 週間」の半分**で Stein achievability が立つので、本 plan は **撤退時にも価値が残る**設計。

---

## 当面の next step

1. ✅ **Phase 0 (本 plan + inventory 起草)** — 完 (2026-05-11)
2. **Phase A skeleton** — `InformationTheory/Shannon/Stein.lean` を sorry-driven で書き始め、`llrPmf` → `logLikelihoodRatio` → `integral_logLikelihoodRatio_under_P` → `stein_strong_law` の sorry を割る ← **次これ**
3. **Phase A 完で Phase B 着手判定** — `stein_strong_law` + `klDiv_pi_eq_n_smul` が silent なら Phase B (achievability)
4. **Phase B 完 = 撤退ライン到達**: proof-log + metrics 取得、Phase C を別 plan に切り出すか継続するかをここで判断
5. **Phase C 完で Phase D 着手判定** — converse が silent なら Phase D (統合形) で 0.5 週で close

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 本 plan はまだ起草段階。本体着手で発見があれば追記。 -->

### 2026-05-11 — Phase A〜B 完了 (publish ライン到達)

**結果**: `InformationTheory/Shannon/Stein.lean` (625 行) で Phase A〜B 完了、`lake env lean InformationTheory/Shannon/Stein.lean` 緑通過 (warning 0、error 0、sorry 0)、`lake build` 緑通過。**Stein achievability publish ラインに到達**。

**Phase A 完了**:
- `llrPmf P Q : α → ℝ` (alphabet-side LR、AEP `pmfLog` の 2 分布化)
- `logLikelihoodRatio P Q Xs i : Ω → ℝ` (per-symbol LR)
- `integral_logLikelihoodRatio_under_P = (klDiv P Q).toReal` (= LR の期待値 = KL)
- `stein_strong_law` (a.s. 収束、`strong_law_ae_real` を `logLikelihoodRatio` で 1 回呼ぶだけ)
- `stein_inProbability` (確率収束、`tendstoInMeasure_of_tendsto_ae` 経由)

**Phase B 完了**:
- `steinTypicalSet P Q n ε` + `measurableSet_steinTypicalSet`
- `steinTypicalSet_P_prob_tendsto_one` (P 側典型 → 1)
- `steinTypicalSet_Q_prob_le` (= `Q^n(T) ≤ exp(-n(klDiv-ε))`)
- `stein_achievability` (∃ test、α-level + β-bound)

**ピボット 1: A.7 `klDiv_pi_eq_n_smul` は迂回**
- 計画では Phase A.7 に `klDiv (Π P) (Π Q) = n · klDiv P Q` の Pi 化 chain rule を実装予定だったが、Phase B (achievability) では **typicality 経由で `Q^n(T) ≤ exp(-n·(klDiv-ε))` を直接導出**できるため不要と判明
- B.3 の証明では `Measure.pi_singleton` (`Measure.pi μ {f} = ∏ i, μ i {f i}`) で点ごとの product 形に下し、point-wise の対数比 `llrPmf P Q (x i) = log P{x_i} - log Q{x_i}` から直接 `Π Q{x_i} / Π P{x_i} = exp(-∑ llrPmf)` を得る
- **Phase A.7 は Phase C 着手時に必要**になる予定

**ピボット 2: `stein_achievability` の statement を pi 形 + RV 仮定併存に**
- 計画段階では statement に `Xs : ℕ → Ω → α` の i.i.d. RV を取る形を想定していたが、**結論部 (`P^n s, Q^n s` の bound)** は pi 形でないと自然に書けない
- 妥協: 両方の hypothesis を取る + 追加で `hMapJoint : ∀ n, μ.map (jointRV Xs n) = Measure.pi (fun _ => P)` を仮定
- `iIndepFun_iff_map_fun_eq_pi_map` (Mathlib) でこの仮定は `iIndepFun` から得られるが、AEP は `Pairwise IndepFun` (弱形) で書かれているため、ここで強形を要求する形にした
- 改善案 (Phase C 着手時): `iIndepFun` 仮定で書き直し、`hMapJoint` は内部で導出する

**ピボット 3: B.3 で `hPpos` 仮定を追加**
- 計画段階では `hQpos : ∀ x, 0 < Q.real{x}` のみ仮定していたが、B.3 の per-point bound (`Π Q ≤ Π P · exp(...)`) を導出する際 `Π P` で割る必要があり、`hPpos : ∀ x, 0 < P.real{x}` も要求
- これは Cover-Thomas 教科書の "regular case" に相当 (P, Q ともに full support)
- Stein achievability 自体は `hPpos` なしでも成立する (= P がサポート外で 0 になる点を typical set 定義で除外する)が、本実装では plumbing 簡素化のため両側 full support を要求

**残課題 (Phase C/D)**:
- A.7 `klDiv_pi_eq_n_smul` の Pi 化 chain rule (Phase C で必要)
- DPI reduction (Phase C.1)
- Bernoulli KL の評価 (Phase C.2)
- `Tendsto` 形統合 (Phase D)
- 撤退ライン到達のため、Phase C/D は別 plan に切り出すか次セッションへ繰越

### 2026-05-11 (再試行) — Phase C/D は別 moonshot plan として切り出し確定

**状況**: Phase A〜B 完了直後の同日、Phase C/D 試行を 5 ターン制限で attack するセッションを起動。`docs/shannon/stein-moonshot-plan.md` + `InformationTheory/Shannon/Stein.lean` を読み戦略を判断した結果、**5 ターン以内では Phase C/D の plumbing 量 (200〜400 行、3 段の新規補題) に届かない**ことが計画記述から明白だったため、計画推奨ルートの **「skeleton も追加せず、現状 (Phase A〜B のみ) で締めて Phase C/D を別 moonshot plan に切り出す」** に従い即時撤退。

**判断根拠 (再確認)**:
- Phase C は (i) Pi 化 KL chain rule (A.7、40〜80 行)、(ii) DPI reduction (C.1、30〜60 行)、(iii) Bernoulli KL 評価 (C.2、30〜60 行)、(iv) `∀ᶠ` 乗せ替え (C.3〜C.4、50〜90 行) の 4 段、合計 150〜290 行の plumbing
- skeleton (= statement に `:= by sorry`) を追加するだけでも 5 ターン中の 1〜2 ターンを消費、緑維持のため `omit` / `variable` 配置の調整が要るリスクあり
- 計画推奨ルート (skeleton も追加せず別 plan 切り出し) が **本シードの整合性が最も高い**: 撤退時 sorry 0 / warning 0 を維持

**確認した状態**:
- `lake env lean InformationTheory/Shannon/Stein.lean` silent (warning 0、error 0、sorry 0)
- `lake build` 緑通過 (2771 jobs)
- 本シードは Phase A〜B (= Stein achievability publish ライン) で **完了**として close

**次セッションへの引継ぎ**:
- 別 moonshot plan を起こす (例: `docs/shannon/stein-converse-moonshot-plan.md`) ─ Phase C (converse) + Phase D (統合形) を独立 plan としてリスタート
- A.7 `klDiv_pi_eq_n_smul` を Phase C の Phase 0 として独立に組む (Mathlib `klDiv_compProd_eq_add` + `MeasurableEquiv.piFinSuccAbove` で induction)
- 起点ファイルは `InformationTheory/Shannon/Stein.lean` (本シードの成果物) に append する形を想定
