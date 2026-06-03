# Sanov の定理 (B-1) ムーンショット計画 🌙

> **Status (2026-05-12)**: **A 形完了 (Phase A〜C すべて 0 sorry)**。`InformationTheory/Shannon/Sanov.lean` (319 行)。**B-1' (LDP upper bound) 完了** → [docs/shannon/sanov-ldp-b-plan.md](sanov-ldp-b-plan.md) で別 publish。**B-1'' deferred** = LDP equality 形 (`Tendsto` の双方向、`klDivIndex` 連続性 + achievable type sequence)。
> **撤退ライン**: A 形 (`typeClass_Qn_le` + `.toReal` 形 `typeClass_Qn_le_klDiv`、Cover-Thomas 11.1.4) を 0 sorry で publish ✅。
>
> **実態整合 (2026-05-20): DONE-UNCOND** — A 形主定理 `typeClass_Qn_le` は `InformationTheory/Shannon/Sanov.lean:172`、std binders (full-support `hPpos`/`hQpos` は honest)、0 sorry。なお **B-1'' (LDP equality) は既に完了済**: `InformationTheory/Shannon/SanovLDPEquality.lean:1243` の `sanov_ldp_equality` (deferred ではない、[sanov-ldp-equality-plan.md](sanov-ldp-equality-plan.md) 参照)。本 Status 行の「B-1'' deferred」は stale。

## 進捗

- [x] Phase 0 — Mathlib delta + 既存 plumbing インベントリ ✅ → [`sanov-mathlib-inventory.md`](sanov-mathlib-inventory.md)
- [x] Phase A — type class 定義 (`typeClass P n`) + 基本補題 (`typeCount`, `measurableSet_typeClass`, `sum_llrPmf_eq_of_mem_typeClass` aggregation, `typeClass_prod_ratio` per-point ratio) ✅
- [x] Phase B — Sanov A 形主定理 `typeClass_Qn_le`: `Q^n(T(P)) ≤ exp(-n · klDivSumForm P Q)` + `.toReal` 形 corollary `typeClass_Qn_le_klDiv` (経由補題 `klDivSumForm_eq_toReal_klDiv`) ✅
- [x] Phase C — verify (`lake env lean InformationTheory/Shannon/Sanov.lean` silent) ✅
- [ ] (Deferred B-1') Phase D — LDP B 形完全版 (`(1/n) log Q^n({ω | empirical_n ∈ E}) → -inf D(P‖Q)`): type 列挙 `𝒫_n` (多項係数) + `(n+1)^{|α|} = exp(o(n))` plumbing + `inf` の `Tendsto`。追加 ~600-1000 行見積。📋

## ゴール / Approach

**最終到達点** (Phase B の主定理):

```lean
theorem typeClass_Qn_le
    (P̂ Q : Measure α) [IsProbabilityMeasure P̂] [IsProbabilityMeasure Q]
    (hP̂Q : P̂ ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    (n : ℕ) :
    ((Measure.pi (fun _ : Fin n => Q)) (typeClass P̂ n)).toReal
      ≤ Real.exp (-((n : ℝ) * (klDiv P̂ Q).toReal))
```

ここで `typeClass P̂ n : Set (Fin n → α)` は「empirical 分布が `P̂` 完全一致」する系列集合。

### Approach (Stein converse 経路の特化、`|T(P̂)| ≤ exp(n·H(P̂))` を回避)

**核心アイデア (Stein の方が出るより簡単な経路)**: 古典的な Cover-Thomas 経路は

1. `|T(P̂)| ≤ exp(n·H(P̂))` (Theorem 11.1.3, 多項係数評価)
2. `∀ x ∈ T(P̂), Q^n({x}) = exp(-n(H(P̂) + D(P̂‖Q)))` (Theorem 11.1.2)
3. (1) × (2) で `Q^n(T(P̂)) ≤ exp(-n·D(P̂‖Q))`

の 2 段で証明するが、本実装は **(1) の多項係数評価を回避** して直接

```
Q^n(T(P̂)) = ∑_{x ∈ T(P̂)} Q^n({x})
          = ∑_{x ∈ T(P̂)} P̂^n({x}) · exp(-n · D(P̂‖Q))  (point-wise の比は T 上一定)
          = exp(-n · D(P̂‖Q)) · P̂^n(T(P̂))
          ≤ exp(-n · D(P̂‖Q)) · 1
```

で終わらせる。この経路は **Stein converse の `steinTypicalSet_Q_prob_le` (Stein.lean:341) と同じ** で、相違点は

- Stein: `steinTypicalSet` 上で `(∑ llrPmf(x_i))/n - K < ε` ⇒ 比は `≤ exp(-(K-ε))` (片側 inequality)
- Sanov: `typeClass P̂` 上で `empirical = P̂` ⇒ 比は **完全一致** `= exp(-D(P̂‖Q))` (両側 equality)

の片側を等号にした特殊形。よって Stein のロジックを **simplify** することで Sanov A 形が得られる。

**3 層構造**:

1. **(Phase A) 定義 + plumbing**:
   - `noncomputable def typeClass (P̂ : Measure α) (n : ℕ) : Set (Fin n → α) :=`
     `{x | ∀ a : α, ((Finset.filter (fun i => x i = a) Finset.univ).card : ℝ) = (n : ℝ) * P̂.real {a}}`
   - `measurableSet_typeClass`: 上記は有限集合の subset なので `Set.toFinite.measurableSet`
   - **point-wise 補題** `typeClass_pi_singleton_eq`: `x ∈ typeClass P̂ n` ⇒
     `Q^n({x}) = ∏ a : α, (Q.real {a})^{(typeCount x a)}` where `typeCount x a = #{i | x i = a}`
   - **比補題** `typeClass_ratio_eq`: `x ∈ typeClass P̂ n` ⇒
     `Q^n({x}) = P̂^n({x}) · exp(-n · (klDiv P̂ Q).toReal)`
     (Stein.lean:420 周辺の `h_exp_neg_llr` の集約形 — alphabet 上 sum `∑ a, n·P̂(a)·log(Q(a)/P̂(a)) = -n·D(P̂‖Q)`)
   - **80〜150 行**
2. **(Phase B) 主定理 `typeClass_Qn_le`**:
   - Stein.lean:341 の `steinTypicalSet_Q_prob_le` をテンプレに、`hxT : x ∈ T` の使い方だけ
     「片側 inequality `(K - ε) < S/n`」→「両側 equality `S/n = K`」に置換。
   - `Q^n(T) = ∑_{x ∈ T} Q^n({x}) ≤ ∑_{x ∈ T} P̂^n({x}) · exp(-n·D) = P̂^n(T) · exp(-n·D) ≤ exp(-n·D)`
   - **60〜100 行**
3. **(Phase C) verify + 配線**:
   - `InformationTheory.lean` に `import InformationTheory.Shannon.Sanov` 追記
   - `lake env lean InformationTheory/Shannon/Sanov.lean` silent
   - `docs/moonshot-seeds.md` B-1 にポインタ `→ docs/shannon/sanov-moonshot-plan.md`

**Approach 図**:

```
Phase 0  : インベントリ                                           ← ✅ 完
           ──────────────────────────────────────────
Phase A  : typeClass 定義 + point-wise ratio                     ← 山場 1、~150 行
           ──────────────────────────────────────────
Phase B  : Sanov A 主定理 `typeClass_Qn_le`                      ← 山場 2、~100 行
           ──────────────────────────────────────────
Phase C  : verify + 配線                                          ← 0.5 日
           ──────────────────────────────────────────
(Phase D : LDP A 形系)                                            ← deferred 候補
```

**ファイル構成 (Phase C 終了時想定)**:

- `InformationTheory/Shannon/Sanov.lean` (新規、 namespace `InformationTheory.Shannon`、想定 250〜400 行)
- `InformationTheory.lean` に 1 行 import 追記

## Phase 0 - Mathlib delta + 既存 plumbing インベントリ ✅

成果物: [`sanov-mathlib-inventory.md`](sanov-mathlib-inventory.md)

調査軸:
- **既存 Stein**: `steinTypicalSet_Q_prob_le` のロジック (Stein.lean:341–480)
- **既存 AEP**: `typicalSet` の構造 (AEP.lean:229–438)
- **既存 MIChainRule**: `klDiv_pi_eq_sum` (MIChainRule.lean:268) — i.i.d. でない `Q^n` には不要だが類似手法参考
- **Mathlib KL**: `klDiv_eq_integral_log` / `klDiv_eq_sum` 形があれば finite alphabet で `D = ∑ P(a)·log(P(a)/Q(a))` への展開で使える
- **Mathlib multinomial**: 不使用 (経路で回避)
- **Mathlib measure pi**: `Measure.pi_singleton`, `Measure.pi_apply` 等の基本。`Finset.prod_pow_eq_pow_sum` か?

## Phase A - typeClass 定義 + point-wise plumbing 📋

### A.1 typeClass 定義

```lean
noncomputable def typeCount (x : Fin n → α) (a : α) : ℕ :=
  (Finset.univ.filter (fun i => x i = a)).card

/-- **Type class** `T(P̂)`: sequences whose empirical distribution matches `P̂` exactly.
A sequence `x : Fin n → α` belongs iff `#{i | x i = a} = n · P̂(a)` for every `a : α`. -/
noncomputable def typeClass (P̂ : Measure α) (n : ℕ) : Set (Fin n → α) :=
  { x | ∀ a : α, ((typeCount x a : ℝ) = (n : ℝ) * P̂.real {a}) }
```

### A.2 measurability

`Set.toFinite.measurableSet` (alphabet 有限 ⇒ `Fin n → α` 有限 ⇒ `typeClass ⊆` 有限集合 ⇒ measurable)。

### A.3 point-wise probability `Q^n({x})`

```lean
lemma pi_singleton_eq_prod
    (Q : Measure α) [IsProbabilityMeasure Q] (n : ℕ) (x : Fin n → α) :
    ((Measure.pi (fun _ : Fin n => Q)).real {x}) = ∏ i : Fin n, Q.real {x i}
```

Stein.lean:368 `h_pi_singleton_Q` をそのまま reuse (`Measure.pi_singleton` + `ENNReal.toReal_prod`)。

### A.4 ratio 補題

```lean
lemma typeClass_ratio_eq
    (P̂ Q : Measure α) [IsProbabilityMeasure P̂] [IsProbabilityMeasure Q]
    (hP̂pos : ∀ x : α, 0 < P̂.real {x})
    (hQpos : ∀ x : α, 0 < Q.real {x})
    (n : ℕ) {x : Fin n → α} (hx : x ∈ typeClass P̂ n) :
    ∏ i : Fin n, Q.real {x i}
      = (∏ i : Fin n, P̂.real {x i}) * Real.exp (-((n : ℝ) * klDivSumForm P̂ Q))
```

ここで `klDivSumForm P̂ Q := ∑ a, P̂.real {a} * (Real.log (P̂.real {a}) - Real.log (Q.real {a}))` (=
`(klDiv P̂ Q).toReal` を finite alphabet で展開した形)。

**鍵 step** (Stein.lean:420–435 の集約):
- `∏ Q(x_i) / ∏ P̂(x_i) = ∏ (Q(x_i)/P̂(x_i)) = exp(∑_i log(Q(x_i)/P̂(x_i)))`
- `∑_i log(Q(x_i)/P̂(x_i)) = ∑_a typeCount(a) · log(Q(a)/P̂(a))` ← 集約
- `x ∈ typeClass` ⇒ `typeCount(a) = n · P̂(a)` ⇒ `= n · ∑_a P̂(a) · log(Q(a)/P̂(a)) = -n · D(P̂‖Q)`

### A.5 `klDivSumForm = (klDiv P̂ Q).toReal`

Mathlib `klDiv_eq_sum` 系 (finite alphabet 上 `klDiv P Q = ∑ P(a) · log (P(a)/Q(a))` の ENNReal 形) を呼ぶ補題。**inventory で API 確認後**、不要なら統合形のまま避ける (Phase B で
`klDivSumForm` で statement、別補題で textbook 形に等値性を取る)。

## Phase B - Sanov A 主定理 📋

```lean
theorem typeClass_Qn_le
    (P̂ Q : Measure α) [IsProbabilityMeasure P̂] [IsProbabilityMeasure Q]
    (hP̂pos : ∀ x : α, 0 < P̂.real {x})
    (hQpos : ∀ x : α, 0 < Q.real {x})
    (n : ℕ) :
    ((Measure.pi (fun _ : Fin n => Q)) (typeClass P̂ n)).toReal
      ≤ Real.exp (-((n : ℝ) * klDivSumForm P̂ Q))
```

Stein.lean:341 をテンプレに proof 構造:

```
Q^n(T)         = ∑_{x ∈ T} Q^n({x})                                          (h_pi_real_eq_sum)
               = ∑_{x ∈ T} (∏ P̂(x_i)) · exp(-n · klDivSumForm)              (typeClass_ratio_eq)
               = exp(-n · klDivSumForm) · ∑_{x ∈ T} ∏ P̂(x_i)
               ≤ exp(-n · klDivSumForm) · ∑_{x : Fin n → α} ∏ P̂(x_i)
               = exp(-n · klDivSumForm) · 1                                   (`Fintype.piFinset_univ`)
```

## Phase C - verify + 配線 📋

- `InformationTheory.lean` に `import InformationTheory.Shannon.Sanov` 追記
- `lake env lean InformationTheory/Shannon/Sanov.lean` silent
- `docs/moonshot-seeds.md` 冒頭 Status と B-1 セクションに pointer

## (Optional) Phase D - LDP A 形系 📋 deferred 候補

任意の **有限** measurable set `E ⊆ {P : Measure α | empirical 候補}` に対し:

```
Q^n({ω | empirical_n(ω) ∈ E}) = ∑_{P̂ ∈ E ∩ 𝒫_n} Q^n(T(P̂)) ≤ |E ∩ 𝒫_n| · exp(-n · inf_{P̂ ∈ E ∩ 𝒫_n} D(P̂‖Q))
                              ≤ (n+1)^{|α|} · exp(-n · inf …)
```

LDP 上界 `(1/n) log Q^n(...) → -inf D(P‖Q)` には `(n+1)^{|α|} = exp(o(n))` の plumbing が必要 — A 形を超える追加 100〜200 行。**本シードでは deferred、必要なら別 plan に切り出し**。

## 判断ログ

1. **2026-05-12 起草時**: 当初 Cover-Thomas 経路 (多項係数 + `|T(P)| ≤ exp(n·H(P))`) を想定したが、Stein の `steinTypicalSet_Q_prob_le` が **多項係数を一切経由せず** `x ∈ T` 上の比評価 + `∑ P^n({x}) ≤ 1` で完成しているのを再読し、これを Sanov の **両側 equality 形** に特化させる方が遥かに短いと判断。`|T(P)| ≤ exp(n·H(P))` の独立 publish (B-1' 系) は本 plan の **scope 外**。
2. **2026-05-12**: `klDivSumForm P Q := ∑ a, P(a) * (log P(a) - log Q(a))` を **finite alphabet 上の textbook 定義** として使い、`(klDiv P Q).toReal` との等値性は別補題に切り出す方針。Mathlib `klDiv_eq_sum` 系の直接 API は見つからなかったが、`toReal_klDiv_of_measure_eq` + `integral_fintype` + `llr` 展開で MaxEntropy.lean:123 のテンプレ通り `klDivSumForm_eq_toReal_klDiv` を約 60 行で導出。主定理は `klDivSumForm` 形を core にして `.toReal` 形は corollary。
3. **2026-05-12 実装中**: `P̂` (U+0050 + U+0302 combining circumflex) が Lean parser に「expected token」と認識されたため、変数名を全て plain `P` に rename。文書中の `P̂` 記号は採用せず。
4. **2026-05-12 実装中**: `prod_fiberwise_of_maps_to'` (Mathlib `Algebra.BigOperators.Group.Finset.Basic:263`) で **additive 版 `sum_fiberwise_of_maps_to'`** が自動生成され、`∑ a, ∑ i ∈ univ with x i = a, f a = ∑ i, f (x i)` の形で aggregation lemma に直結。fiberwise sum を `typeCount x a * f a` に簡約する `Finset.sum_const` + `nsmul_eq_mul` の組合せで Phase A.4 (aggregation) は約 25 行で着地。
