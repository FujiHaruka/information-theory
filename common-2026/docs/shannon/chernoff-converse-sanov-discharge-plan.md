# Chernoff converse 完全 discharge (Sanov 経由) サブ計画 🌙 (T1-B)

> **Parent**: [`chernoff-converse-moonshot-plan.md`](chernoff-converse-moonshot-plan.md)
> §「完全 discharge (Sanov LDP per-tilt 起動)」 + §撤退ライン L-CC2
>
> **Predecessor が defer したものを閉じる plan**。predecessor は per-tilt 形 hypothesis
> 縮減 (L-CC2) で着地し、`IsBayesErrorPerTiltLowerBound` / `IsChernoffNLetterRN` を
> Mathlib-gap predicate として残した。本 plan はその predicate を **genuine に証明**して
> 全 converse headline を **無条件 (標準B、regularity-only)** にする。

## 進捗

- [x] M0 — Sanov 支配補題の conclusion form 確定 + redefine 2 択の最終判断 ✅ (verbatim inventory 下記)
- [x] Phase 1 — skeleton (新規 file `ChernoffSanovDischarge.lean`、sorries 3 個) ✅
- [x] Phase 2 — step 1: tilted typical set 上の逆 Hölder per-point 下界 ✅ (`min_ge_exp_neg_mul_rpow_mul_rpow`)
- [x] Phase 3 — step 3: tilted typical set の確率→1 ✅ (実装は SLLN on `infinitePi Q` 経路、Stein 経路ではなく；下記判断ログ #3)
- [x] Phase 4 — step 1+2+3 合成: `exp(-n·ε)·Z^n ≤ 4·bayesErrorMinPmf` を genuine に構成 ✅ (`bayesErrorMinPmf_ge_exp_neg_mul_Z_pow`, `chernoff_converse_from_eps_relaxed`, `chernoff_converse_of_bandMass`)
- [ ] Phase 5 — name laundering 解消 + 既存 suspect tag (~20 件) の migration 📋 (下記 consumer 書換表)
- [ ] Phase 6 — verify (already passing) + InformationTheory 編入 (already 編入: 行 186 + 187) + roadmap 判断ログ 📋

proof-log: yes (Phase 2-4 の実装は完了済。proof-log は予定通り存在するなら参照、無ければ Phase 5 移行作業の中で記録)

> **2026-05-24 Wave 2 audit 再判定**: 本 plan を起草した時点 (2026-05-21) では「Phase 2-4 が本物の Mathlib 作業」と想定していたが、**実装は既に overshoot している**:
> - `ChernoffSanovDischarge.lean` (479 行、0 sorry) が step 1+2+4 を **無条件 genuine** で publish 済。
> - `ChernoffBandMassDischarge.lean` (575 行、0 sorry) が step 3 (band mass → 1) を **interior-optimality + Q-LLN 経路で genuine discharge**、regularity-only headline `chernoff_converse_holds` / `chernoff_lemma_tendsto_holds` を publish 済。
> - 実装中に **predicate `IsBayesErrorPerTiltLowerBound` 自体が一般に偽** (Cramér local-limit prefactor `Θ(1/√n)` のため定数 `C` は存在しない) という Plan-Level 重要発見 (ChernoffSanovDischarge.lean 冒頭 docstring "Plan-level finding (honesty alert)") → 本 plan の Phase 4 で当初目指していた「`IsBayesErrorPerTiltLowerBound` を genuine に構成」は **数学的に不可能**、ε-relaxed 版 (`exp(-n·ε)·Z^n ≤ 4·bayesErrorMinPmf`) に pivot して publish 済。
> - 残作業は実質 **Phase 5 のみ**: 旧 predicate 経由 publish された ~20 件の `@audit:suspect(chernoff-converse-sanov-discharge-plan)` / `@audit:suspect(chernoff-converse-moonshot-plan)` を `closed-by-successor(chernoff-converse-sanov-discharge)` へ migration + 旧 `chernoff_per_tilt_via_RN` (`:= h_RN` 循環) の docstring に defect 明示。
> - **想定規模 (積み上げ、実測)**: 新規 file 合計 **~1054 行** (ChernoffSanovDischarge 479 + ChernoffBandMassDischarge 575)。当初見積 ~150-300 行 / pessimistic ~310 行を大幅超過したが、これは「genuine discharge を最後まで通した結果」で gap な大量化ではない (judgement log #4)。

---

## Context / 現況

### いま load-bearing になっている述語 (起草時の認識)

Cover-Thomas Theorem 11.9.1 converse の headline:

```
limsup_n -(1/n) log bayesErrorMinPmf P₁ P₂ n ≤ chernoffInfo P₁ P₂   (＝ Tendsto / DotEq 形も)
```

これは `ChernoffPerTiltSanov.lean` / `ChernoffPerTiltDischarge.lean` で publish 済だが、
入力に **load-bearing predicate** を要求している:

```lean
-- ChernoffPerTiltDischarge.lean:136
def IsBayesErrorPerTiltLowerBound (P₁ P₂ : α → ℝ) (lam : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      C * (chernoffZSum P₁ P₂ lam) ^ n ≤ 2 * bayesErrorMinPmf P₁ P₂ n
```

これは「証明の核心」(= 残タスク)。「その仮説は前提条件か、それとも証明の核心か」の判定で
**核心**側 — converse の指数下界そのものを仮定が肩代わりしている。regularity hyp ではない。

### 実装で発覚した plan-level 重要発見 (2026-05-21、ChernoffSanovDischarge 起草時に inline で記録)

**`IsBayesErrorPerTiltLowerBound` は一般に偽**: 定数 `C > 0` で `∀ᶠ n, C·Z(λ*)^n ≤ 2·bayesErrorMinPmf` を満たす `C` は **存在しない**。理由は genuine method-of-types 漸近形が
`bayesErrorMinPmf ~ poly(n)·Z(λ*)^n` で **vanishing sub-exponential prefactor (`Θ(1/√n)` local-limit / lattice factor)** を伴うため、`bayesErrorMinPmf / Z(λ*)^n → 0`。
symmetric 2-point alphabet (`λ* = 1/2`) で具体的に検証可能。

→ predicate as stated は **証明不能ではなく false**。converse が実際に必要としているのは ε-relaxed 形:

```
∀ ε > 0, ∀ᶠ n, exp(-n·ε)·Z(λ*)^n ≤ 4·bayesErrorMinPmf P₁ P₂ n
```

vanishing prefactor を `exp(-n·ε)` で吸収する形。typical-set + 逆 Hölder で **これは genuine に出る**
(`bayesErrorMinPmf_ge_exp_neg_mul_Z_pow`、ChernoffSanovDischarge.lean:289)。

### honesty defect (発見済、本 plan で解消する)

`ChernoffPerTiltSanov.lean:165-169` の `chernoff_per_tilt_via_RN` は
`IsChernoffNLetterRN` ≡ `IsBayesErrorPerTiltLowerBound` (body 字面一致、`:140` vs `:136`) で
body `:= h_RN` の **循環 / name laundering** (CLAUDE.md「検証の誠実性」tells)。

```lean
-- ChernoffPerTiltSanov.lean:165-169
lemma chernoff_per_tilt_via_RN (P₁ P₂ : α → ℝ) (lam : ℝ)
    (h_RN : IsChernoffNLetterRN P₁ P₂ lam) :
    IsBayesErrorPerTiltLowerBound P₁ P₂ lam := h_RN          -- ← 循環 (型≡結論、:= h)
```

しかも上記 plan-level finding により **両 predicate とも一般に偽** で、誰も discharge できない (実装も
試みたら矛盾を導ける)。本 plan の Phase 5 で:

1. genuine な無条件 headline (`chernoff_converse_holds` / `chernoff_lemma_tendsto_holds`,
   `ChernoffBandMassDischarge.lean`) が **既に publish されている**ことを記録。
2. 旧 predicate 経由の publish (`chernoff_converse_via_RN_forall`, `chernoff_lemma_tendsto_via_RN`,
   `chernoff_dotEq_tendsto_via_RN`, ...) は **死コード**として「`@audit:closed-by-successor(chernoff-converse-sanov-discharge)`」へ migration。
3. 旧 `chernoff_per_tilt_via_RN` の docstring に「**両 predicate は一般に偽**, ε-relaxed 版が genuine、
   `ChernoffBandMassDischarge.chernoff_converse_holds` 参照」を明示。

---

## Approach (全体戦略 = Sanov 経由 step 1-4、実装ベース)

下界 `exp(-n·ε)·Z(λ*)^n ≤ 4·bayesErrorMinPmf` を、tilted mediator measure
`chernoffMediatorMeasure P₁ P₂ λ*` (= Q) を ambient に据えた **change-of-measure on a
log-ratio band** で構成する。Stein の typicality argument 同型のテンプレートを使うが、
**band 確率 → 1** の証明は Stein の `Ω` 上 RV 形ではなく **`Measure.infinitePi Q` 上の
`strong_law_ae_real` 直接適用 + `infinitePi_map_take` reindex** で `Measure.pi (Fin n) Q` 形に下ろす
(下記判断ログ #3)。

```
bayesErrorMinPmf P₁ P₂ n
  = (1/2) ∑_x min(∏P₁(x_i), ∏P₂(x_i))                          -- 定義 (Chernoff.lean:691)
  ≥ (1/2) ∑_{x ∈ B_n} min(...)                                  -- 非負項を band B_n に制限
  ≥ (1/2) ∑_{x ∈ B_n} exp(-n·ε)·(∏P₁)^{1-λ}·(∏P₂)^λ            -- step 1 逆 Hölder on B_n
  = (1/2) exp(-n·ε)·Z(λ)^n · ∑_{x∈B_n} ∏ mediator(x_i)         -- step 2 正規化 (mediator def 経由)
  ≥ (1/2) exp(-n·ε)·Z(λ)^n · (1/2)                              -- step 3 Q^n(B_n) ≥ 1/2 (SLLN tail)
  = (1/4) exp(-n·ε)·Z(λ)^n                                      -- ε-relaxed per-tilt lower bound 成立
```

ここで `B_n := chernoffLogRatioBand P₁ P₂ n ε` (ChernoffSanovDischarge.lean:169) は
**band 集合** `{x : Fin n → α | |∑ (log P₁(x_i) - log P₂(x_i))| ≤ n·ε}`。
`Stein.steinTypicalSet` (LR-based) と字面的に近いが
LR ではなく **log P₁ - log P₂** (sign 付き) を採るのが key (interior optimality で Q-mean = 0)。

4 step の役割 (実装後の確定形):

1. **step 1 (新規 core)**: 逆 Hölder per-point on the band。
   `min_ge_exp_neg_mul_rpow_mul_rpow` (ChernoffSanovDischarge.lean:106): `a, b > 0`,
   `λ ∈ [0,1]`, `|log a - log b| ≤ δ` ⇒ `exp(-δ)·a^{1-λ}·b^λ ≤ min a b`。
   κ explicit form: **κ(ε) := exp(-n·ε)** (n依存定数、δ = n·ε)。
   既存 `min_le_rpow_mul_rpow` (Chernoff.lean:699) の **正逆対** (上界版の逆向き、log-ratio band 上で成立)。
2. **step 2 (既存再利用、無変更)**: n-letter Z 正規化。
   `geomMean_eq_Z_pow_mul_prod_mediator` (ChernoffSanovDischarge.lean:260) で
   `(∏P₁)^{1-λ}·(∏P₂)^λ = Z(λ)^n · ∏ mediator(x_i)` per-block。
   既存 `prod_rpow_mul_rpow` + `chernoffZSum_pow_eq_sum_prod` の合成。
3. **step 3 (SLLN on infinitePi Q、新規 wiring)**: band の Q^n 確率 → 1。
   `isChernoffBandMassToOne_of_interior_optimal` (ChernoffBandMassDischarge.lean:395)。
   `Q := chernoffMediatorMeasure P₁ P₂ λ*` を `Measure.infinitePi` に持ち上げ、
   `Y a := log P₁ a - log P₂ a` の SLLN で `(∑ Y(ω i)) / n →ᵐ 0` (Q-mean は interior optimality
   `chernoffMediator_mean_logRatio_eq_zero` で 0)、`tendstoInMeasure_of_tendsto_ae` → band tail 0、
   `infinitePi_map_take` で `Measure.pi (Fin n) Q` 上の band へ reindex。
4. **step 4 (合成 + interior 引き出し)**: `chernoff_converse_of_bandMass`
   (ChernoffSanovDischarge.lean:463) → `chernoff_converse_holds`
   (ChernoffBandMassDischarge.lean:536)。
   `exists_interior_minimiser` (`:259`) で `λ* ∈ (0,1)` を strict Gibbs (`P₁ ≠ P₂`) で boundary 排除
   して取り出し、step 1-3 を起動。

`chernoff_lemma_tendsto_holds` (ChernoffBandMassDischarge.lean:560) が
`ChernoffInformation.chernoff_lemma_tendsto` を経由した **regularity-only headline** (full-support
`P₁, P₂`, `∑P₁ = ∑P₂ = 1`, `P₁ ≠ P₂` — すべて regularity hyp、core 仮定なし)。

---

## 設計判断 (Mathlib-shape-driven): `bayesErrorMinPmf` redefine するか

### 結論: **redefine しない。現 min-和 形のまま step 1-4 で通す。** (実装で確証)

#### 根拠 (支配補題の conclusion form を verbatim 読んだ上で、M0 確定)

支配補題は **`typeClassByCount_Qn_ge` (`SanovLDPEquality.lean:918`)** と
**`sanov_ldp_lower_bound_pointwise` (`:1071`)**。conclusion form (verbatim):

```lean
-- SanovLDPEquality.lean:918  typeClassByCount_Qn_ge
theorem typeClassByCount_Qn_ge
    (Q : Measure α) [IsProbabilityMeasure Q]
    (hQpos : ∀ a : α, 0 < Q.real {a})
    {n : ℕ} (hn : 0 < n) (c : α → ℕ) (hc_sum : (∑ a, c a) = n) :
    (((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹ * Real.exp (-((n : ℝ) * klDivIndex c n Q))
      ≤ ((Measure.pi (fun _ : Fin n => Q)) (typeClassByCount (α := α) c)).toReal
```

```lean
-- SanovLDPEquality.lean:1071  sanov_ldp_lower_bound_pointwise
theorem sanov_ldp_lower_bound_pointwise
    (Q : Measure α) [IsProbabilityMeasure Q] (hQpos : ∀ a : α, 0 < Q.real {a})
    (P : α → ℝ) (hP_prob : (∑ a, P a) = 1) (hP_full : ∀ a, 0 < P a)
    (E : ∀ n, Finset (TypeCountIndex α n))
    (h_in_E : ∀ᶠ n : ℕ in atTop, roundedTypeIndex P n ∈ E n) :
    -klDivSumForm_ofVec P (fun a => Q.real {a})
      ≤ Filter.liminf (fun n : ℕ => (1 / (n : ℝ)) * Real.log
          (((Measure.pi (fun _ : Fin n => Q))
            (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal)) atTop
```

両者とも **`Measure.pi (fun _ : Fin n => Q)` 上の集合測度** を出力する。Q として何を入れても
集合 (typeClassByCount / 任意の cylinder) の `.toReal` measure が結論。一方
`bayesErrorMinPmf` (現 min-和形) を step 1-3 で使う際に **必要なのは `∑_{x ∈ B_n}` の
finite-sum 評価**であって、Sanov 補題の出力 `Q^n(B_n).toReal` とは
`chernoffMediatorMeasure_pi_singleton_toReal` (`ChernoffPerTiltSanov.lean:224`, verbatim:
`((Measure.pi (fun _ : Fin n => chernoffMediatorMeasure P₁ P₂ lam)) {x}).toReal = ∏ i, chernoffMediator P₁ P₂ lam (x i)`)
+ `MeasureTheory.sum_measureReal_singleton` (Mathlib) で **既に bridge 済**。

→ redefine の動機 (「min-和 ↔ Measure.pi の bridge を探しているのが詰まりの根因」) は、
predecessor の Phase J/C plumbing (`ChernoffPerTiltDischarge.lean:425-498`,
`ChernoffPerTiltSanov.lean:188-251`) が **既に架けたことで消えている**。
実装でも `chernoffMediatorMeasure_pi_real_band` (ChernoffBandMassDischarge.lean:354) として
~25 行で確認済。redefine の純利益はなく、achievability チェーン (Chernoff.lean:779-1064、
`unfold bayesErrorMinPmf` 依存) を壊す損が確実。**L-SD2 不発動**。

---

## Phase 詳細 (実装ベース)

### M0 — Sanov 支配補題の conclusion form 確定 + redefine 最終判断 ✅

依存補題 verbatim inventory (`file:line`、`[...]` 型クラス前提、引数、conclusion):

- [x] **`typeClassByCount_Qn_ge`** — `InformationTheory/Shannon/SanovLDPEquality.lean:918`
  ```
  theorem typeClassByCount_Qn_ge
      (Q : Measure α) [IsProbabilityMeasure Q]
      (hQpos : ∀ a : α, 0 < Q.real {a})
      {n : ℕ} (hn : 0 < n) (c : α → ℕ) (hc_sum : (∑ a, c a) = n) :
      (((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹ * Real.exp (-((n : ℝ) * klDivIndex c n Q))
        ≤ ((Measure.pi (fun _ : Fin n => Q)) (typeClassByCount (α := α) c)).toReal
  ```
  ※ implicit binder: `[Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α]` (file 冒頭 `variable` 由来、`omit [Nonempty α]` 適用)
  conclusion: `((n+1)^|α|)⁻¹ · exp(-n·D) ≤ (Measure.pi Q (T_c)).toReal` — **`Measure.pi` 上の集合測度の `.toReal`**

- [x] **`sanov_ldp_lower_bound_pointwise`** — `InformationTheory/Shannon/SanovLDPEquality.lean:1071`
  ```
  theorem sanov_ldp_lower_bound_pointwise
      (Q : Measure α) [IsProbabilityMeasure Q] (hQpos : ∀ a : α, 0 < Q.real {a})
      (P : α → ℝ) (hP_prob : (∑ a, P a) = 1) (hP_full : ∀ a, 0 < P a)
      (E : ∀ n, Finset (TypeCountIndex α n))
      (h_in_E : ∀ᶠ n : ℕ in atTop, roundedTypeIndex P n ∈ E n) :
      -klDivSumForm_ofVec P (fun a => Q.real {a})
        ≤ Filter.liminf (fun n : ℕ => (1 / (n : ℝ)) * Real.log
            (((Measure.pi (fun _ : Fin n => Q))
              (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal)) atTop
  ```
  conclusion: `-D ≤ liminf (1/n) log (Measure.pi Q (⋃ T_c)).toReal` — **`Measure.pi` 上 union-of-typeclasses 集合の log-測度の liminf**

- [x] **`steinTypicalSet_P_prob_tendsto_one`** — `InformationTheory/Shannon/Stein.lean:275`
  ```
  theorem steinTypicalSet_P_prob_tendsto_one
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
      (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
      (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
      (hMap : μ.map (Xs 0) = P)
      (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
      {ε : ℝ} (hε : 0 < ε) :
      Tendsto (fun n : ℕ => μ {ω | jointRV Xs n ω ∈ steinTypicalSet P Q n ε})
        atTop (𝓝 1)
  ```
  ※ implicit: `[MeasurableSpace Ω] [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]` (file冒頭)
  conclusion: `Tendsto (n ↦ μ {ω | jointRV Xs n ω ∈ T_ε^n}) atTop (𝓝 1)` — **`Ω` 上 RV jointRV 形** (Measure.pi 直接形ではない)

- [x] **`steinTypicalSet_Q_prob_le`** — `InformationTheory/Shannon/Stein.lean:341`
  ```
  theorem steinTypicalSet_Q_prob_le
      (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (hPpos : ∀ x : α, 0 < P.real {x})
      (hQpos : ∀ x : α, 0 < Q.real {x})
      (n : ℕ) (ε : ℝ) :
      ((Measure.pi (fun _ : Fin n => Q)) (steinTypicalSet P Q n ε)).toReal
        ≤ Real.exp (-((n : ℝ) * ((klDiv P Q).toReal - ε)))
  ```
  conclusion: `(Measure.pi Q T_ε^n).toReal ≤ exp(-(n·(K - ε)))` — **`Measure.pi` 直接形** (本 plan の step 3 で起動を試したテンプレート、最終的に SLLN 直接で代替)

- [x] **`chernoffMediatorMeasure_isProbabilityMeasure`** — `InformationTheory/Shannon/ChernoffPerTiltDischarge.lean:464`
  ```
  lemma chernoffMediatorMeasure_isProbabilityMeasure
      [MeasurableSpace α] [MeasurableSingletonClass α]
      (P₁ P₂ : α → ℝ) [Nonempty α]
      (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
      (lam : ℝ) :
      MeasureTheory.IsProbabilityMeasure (chernoffMediatorMeasure P₁ P₂ lam)
  ```
  conclusion: `IsProbabilityMeasure (chernoffMediatorMeasure P₁ P₂ lam)` — instance 供給用

- [x] **`chernoffMediatorMeasure_real_singleton`** — `ChernoffPerTiltDischarge.lean:487`
  ```
  lemma chernoffMediatorMeasure_real_singleton
      [MeasurableSpace α] [MeasurableSingletonClass α]
      (P₁ P₂ : α → ℝ) [Nonempty α]
      (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
      (lam : ℝ) (a : α) :
      (chernoffMediatorMeasure P₁ P₂ lam).real ({a} : Set α)
        = ChernoffConverse.chernoffMediator P₁ P₂ lam a
  ```
  conclusion: `Q.real {a} = chernoffMediator P₁ P₂ lam a` — singleton real measure = pmf 値

- [x] **`chernoffMediatorMeasure_pi_singleton_toReal`** — `ChernoffPerTiltSanov.lean:224`
  ```
  lemma chernoffMediatorMeasure_pi_singleton_toReal
      [MeasurableSpace α] [MeasurableSingletonClass α]
      (P₁ P₂ : α → ℝ) [Nonempty α]
      (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
      (lam : ℝ) {n : ℕ} (x : Fin n → α) :
      ((Measure.pi (fun _ : Fin n => chernoffMediatorMeasure P₁ P₂ lam)) {x}).toReal
        = ∏ i : Fin n, ChernoffConverse.chernoffMediator P₁ P₂ lam (x i)
  ```
  conclusion: `(Measure.pi Q {x}).toReal = ∏ mediator(x i)` — n-letter singleton .toReal = pmf 積

- [x] **`chernoffMediatorMeasure_pi_isProbability`** (instance) — `ChernoffPerTiltSanov.lean:240`
  ```
  instance chernoffMediatorMeasure_pi_isProbability
      [MeasurableSpace α] [MeasurableSingletonClass α]
      {P₁ P₂ : α → ℝ} [Nonempty α]
      [Fact (∀ a, 0 < P₁ a)] [Fact (∀ a, 0 < P₂ a)]
      {lam : ℝ} {n : ℕ} :
      IsProbabilityMeasure
        (Measure.pi (fun _ : Fin n => chernoffMediatorMeasure P₁ P₂ lam))
  ```
  conclusion: `IsProbabilityMeasure (Measure.pi (fun _ : Fin n => Q))` — instance、要 `[Fact (∀ a, 0 < P_i a)]`

- [x] **`min_le_rpow_mul_rpow`** — `InformationTheory/Shannon/Chernoff.lean:699`
  ```
  lemma min_le_rpow_mul_rpow
      {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {lam : ℝ}
      (hlam_nn : 0 ≤ lam) (hlam_le : lam ≤ 1) :
      min a b ≤ a ^ (1 - lam) * b ^ lam
  ```
  conclusion: `min a b ≤ a^{1-λ}·b^λ` — Phase 2 の **構造参照**（逆向きを実装するのが本 plan の step 1）

- [x] **`sum_prod_rpow_eq_Z_pow`** — `InformationTheory/Shannon/Chernoff.lean:751`
  ```
  lemma sum_prod_rpow_eq_Z_pow
      (P₁ P₂ : α → ℝ) (hP₁_nn : ∀ a, 0 ≤ P₁ a) (hP₂_nn : ∀ a, 0 ≤ P₂ a)
      (lam : ℝ) (n : ℕ) :
      ∑ x : Fin n → α, (∏ i, P₁ (x i)) ^ (1 - lam) * (∏ i, P₂ (x i)) ^ lam
        = (chernoffZSum P₁ P₂ lam) ^ n
  ```
  conclusion: `∑_x geomMean(x) = Z(λ)^n` — Phase 4 step 2 (per-block 経由なので直接は使わず、`geomMean_eq_Z_pow_mul_prod_mediator` で代用)

- [x] **`chernoffZSum_pow_eq_sum_prod`** — `InformationTheory/Shannon/ChernoffNLetterZSum.lean:36`
  ```
  theorem chernoffZSum_pow_eq_sum_prod
      (P₁ P₂ : α → ℝ) (lam : ℝ) (n : ℕ) :
      (chernoffZSum P₁ P₂ lam) ^ n =
        ∑ x : Fin n → α, ∏ i : Fin n, (P₁ (x i)) ^ (1 - lam) * (P₂ (x i)) ^ lam
  ```
  conclusion: `Z^n = ∑_x ∏_i (P₁(x_i))^{1-λ}·(P₂(x_i))^λ` — 上の per-block 展開 (rpow を ∏ 内に押し込む)

- [x] **`IsBayesErrorPerTiltLowerBound`** (predicate) — `ChernoffPerTiltDischarge.lean:136`
  ```
  def IsBayesErrorPerTiltLowerBound
      (P₁ P₂ : α → ℝ) (lam : ℝ) : Prop :=
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        C * (chernoffZSum P₁ P₂ lam) ^ n ≤ 2 * bayesErrorMinPmf P₁ P₂ n
  ```
  predicate body: `∃ C > 0, ∀ᶠ n, C·Z^n ≤ 2·bayesError` — **本 plan の起草時には genuine 化対象、実装で false と判明** (Plan-Level Finding、ChernoffSanovDischarge.lean 冒頭 docstring)

**M0 結論**:

1. **Mathlib gap なし** — 12 補題すべて InformationTheory / Mathlib に存在 (Mathlib 側追加検証: `MeasureTheory.sum_measureReal_singleton`, `MeasureTheory.Measure.pi_singleton`, `MeasureTheory.Measure.infinitePi_map_eval`, `strong_law_ae_real`, `tendstoInMeasure_of_tendsto_ae`, `HasDerivAt.const_rpow`, `Real.log_lt_sub_one_of_pos` ほか、loogle で `Found` 確認済)。L-SD1 不発動。
2. **redefine 不要** — bridge は `chernoffMediatorMeasure_pi_singleton_toReal` + `sum_measureReal_singleton` で 1 行 (`chernoffMediatorMeasure_pi_real_band`、ChernoffBandMassDischarge.lean:354)、~25 行で閉じる。L-SD2 不発動。
3. **step 3 経路の選択** — 起草時 (a) Stein 移植 を第一候補としたが、実装で **(c) `strong_law_ae_real` を `Measure.infinitePi Q` 上直接適用** に pivot (下記 Phase 3、判断ログ #3)。

規模: 在庫確認のみ (0 行)。

### Phase 1 — skeleton ✅

- [x] 新規 file `InformationTheory/Shannon/ChernoffSanovDischarge.lean` 作成、pinpoint import:
      `ChernoffPerTiltSanov`, `Chernoff`, `ChernoffNLetterZSum`, `Mathlib.Analysis.SpecialFunctions.Pow.Real`,
      `Mathlib.Analysis.SpecialFunctions.Log.Basic`。
      ※ 当初 imports に追加された `Stein` / `SanovLDPEquality` は最終的に不要 (step 3 を SLLN 経路に pivot した結果)。
- [x] Phase 2-4 の補題を最初 `:= by sorry` で全 state、`linter.unusedSectionVars` + `linter.unusedVariables` を false に。
- [x] LSP `<new-diagnostics>` で skeleton type-check OK 確認。

実装ベースの最終 signature 一覧 (skeleton 段階で確定):

```lean
-- step 1 per-point
lemma min_ge_exp_neg_mul_rpow_mul_rpow
    {a b δ : ℝ} (ha : 0 < a) (hb : 0 < b)
    {lam : ℝ} (hlam_nn : 0 ≤ lam) (hlam_le : lam ≤ 1)
    (hband : |Real.log a - Real.log b| ≤ δ) :
    Real.exp (-δ) * (a ^ (1 - lam) * b ^ lam) ≤ min a b

-- band 集合 def
noncomputable def chernoffLogRatioBand (P₁ P₂ : α → ℝ) (n : ℕ) (ε : ℝ) :
    Set (Fin n → α) :=
  { x | |∑ i : Fin n, (Real.log (P₁ (x i)) - Real.log (P₂ (x i)))| ≤ (n : ℝ) * ε }

-- step 1 block
lemma bayesErrorBlock_ge_exp_neg_mul_geomMean
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    {n : ℕ} {ε : ℝ} {lam : ℝ} (hlam_nn : 0 ≤ lam) (hlam_le : lam ≤ 1)
    {x : Fin n → α} (hx : x ∈ chernoffLogRatioBand P₁ P₂ n ε) :
    Real.exp (-((n : ℝ) * ε)) *
        ((∏ i, P₁ (x i)) ^ (1 - lam) * (∏ i, P₂ (x i)) ^ lam)
      ≤ min (∏ i, P₁ (x i)) (∏ i, P₂ (x i))

-- step 3 honest load-bearing residual
def IsChernoffBandMassToOne (P₁ P₂ : α → ℝ) (lam : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (1 / 2 : ℝ) ≤ ∑ x ∈ (chernoffLogRatioBand P₁ P₂ n ε).toFinite.toFinset,
        ∏ i, ChernoffConverse.chernoffMediator P₁ P₂ lam (x i)

-- step 4 ε-relaxed (composite)
lemma bayesErrorMinPmf_ge_exp_neg_mul_Z_pow ...
theorem chernoff_converse_from_eps_relaxed ...
theorem chernoff_converse_of_bandMass ...
```

規模: ~40 行 (実測 ~80 行、docstring 多め)。

### Phase 2 — step 1: log-ratio band 上の逆 Hölder per-point 下界 ✅

#### κ explicit form

**κ(ε) := exp(-n·ε)** (band 上で `|∑ (log P₁(x_i) - log P₂(x_i))| ≤ n·ε` から
`|log a - log b| ≤ n·ε` (`a := ∏P₁`, `b := ∏P₂`)、これを per-point の `min ≥ exp(-δ)·a^{1-λ}b^λ` に
渡して `δ := n·ε` で起動)。

#### per-point 証明 sketch (実装通り、ChernoffSanovDischarge.lean:106-161)

```lean
lemma min_ge_exp_neg_mul_rpow_mul_rpow
    {a b δ : ℝ} (ha : 0 < a) (hb : 0 < b)
    {lam : ℝ} (hlam_nn : 0 ≤ lam) (hlam_le : lam ≤ 1)
    (hband : |Real.log a - Real.log b| ≤ δ) :
    Real.exp (-δ) * (a ^ (1 - lam) * b ^ lam) ≤ min a b := by
  -- (1) hband から両側評価
  have h_lo : -δ ≤ Real.log a - Real.log b := neg_le_of_abs_le hband
  have h_hi : Real.log a - Real.log b ≤ δ := le_of_abs_le hband
  -- (2) `a = a^{1-λ}·a^λ` と `b = b^{1-λ}·b^λ` を Real.rpow_add で
  have h_a_split : a ^ (1 - lam) * a ^ lam = a := ...  -- Real.rpow_add + rpow_one
  have h_b_split : b ^ (1 - lam) * b ^ lam = b := ...
  -- (3) le_min で a 側 / b 側に分割
  refine le_min ?_ ?_
  · -- a 側: exp(-δ)·a^{1-λ}·b^λ ≤ a (Real.exp_le_exp + Real.log_rpow + nlinarith)
    have h_key : Real.exp (-δ) * b ^ lam ≤ a ^ lam := by
      rw [← Real.exp_log (Real.rpow_pos_of_pos ha _),
          ← Real.exp_log (Real.rpow_pos_of_pos hb _), ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [Real.log_rpow ha, Real.log_rpow hb]
      -- ‐δ + λ·log b ≤ λ·log a ⇔ -δ ≤ λ·(log a - log b)
      have hmul : -δ ≤ lam * (Real.log a - Real.log b) := by
        rcases eq_or_lt_of_le hlam_nn with h | h
        · simp [← h, hδ_nn]
        · nlinarith [mul_le_mul_of_nonneg_left h_lo hlam_nn, mul_nonneg hlam_nn hδ_nn]
      nlinarith
    calc Real.exp (-δ) * (a ^ (1 - lam) * b ^ lam)
        = a ^ (1 - lam) * (Real.exp (-δ) * b ^ lam) := by ring
      _ ≤ a ^ (1 - lam) * a ^ lam := mul_le_mul_of_nonneg_left h_key ...
      _ = a := h_a_split
  · -- b 側: 対称 (h_hi で -δ ≤ (1-λ)·(log b - log a))
    ...
```

実装は **既存 `min_le_rpow_mul_rpow` の逆対**として綺麗にミラーされており、唯一の新規数学。
δ = n·ε を block 形 `bayesErrorBlock_ge_exp_neg_mul_geomMean` (`:181`) で起動するときの bridge は
`Real.log_prod` (log of product) + `Finset.sum_sub_distrib`。

依存補題:
- `Real.rpow_add (Pos.ofNat hb : 0 < a)` — Mathlib (rpow exponent 加法)
- `Real.exp_log (h : 0 < x)` — Mathlib
- `Real.log_rpow (h : 0 < a) (b : ℝ) : log (a^b) = b · log a` — Mathlib
- `Real.exp_le_exp : exp x ≤ exp y ↔ x ≤ y` — Mathlib
- `min_le_rpow_mul_rpow` — `Chernoff.lean:699` (構造の参照のみ)
- `Real.log_prod` — Mathlib (∏ → ∑ log)

規模 (実測): ~95 行 (per-point 56 行 + block 19 行 + band def + iff 補題)。
proof-log: yes — κ explicit (`exp(-δ)`) で nlinarith が ε = 0 corner で爆発する手前で `eq_or_lt_of_le hlam_nn` の場合分けが必要 (実装で実観測)。

### Phase 3 — step 3: band の Q^n 確率 → 1 ✅

#### 経路選択: SLLN on `Measure.infinitePi Q` 直接

起草時の M0 では **(a) Stein 移植**を第一候補としていたが、実装で以下の理由から **(c) SLLN 直接** に pivot:

- Stein `steinTypicalSet_P_prob_tendsto_one` の signature は **`(μ : Measure Ω)` + `Xs : ℕ → Ω → α`** 形 (file 冒頭 variable で `Ω`)。Chernoff 側は最初から **`Measure.pi (Fin n) Q`** 直接形を望むので、Ω-RV 形を経由するなら adaptation layer (Ω := ℕ → α, μ := infinitePi Q, Xs := eval) が必要 — つまり結局 `infinitePi Q` を介する。
- であれば Ω-RV を経由せず、**`Measure.infinitePi Q` 上の `strong_law_ae_real`** を直接適用するのが natural shape。Mathlib `strong_law_ae_real` の引数は `(X : ℕ → Ω → ℝ) (h_int : Integrable (X 0) μ) (h_indep : Pairwise (Function.onFun (· ⟂ᵢ[μ] ·) X)) (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)` — Ω 抽象でよく、`Ω := ℕ → α`, `μ := infinitePi Q`, `X i ω := Y (ω i)` で hit。
- Cramér 側の既存 `iIndepFun_eval_under_infinitePi` / `identDistrib_eval_under_infinitePi` (`InformationTheory/Shannon/Cramer/Discharge.lean`、ChernoffBandMassDischarge.lean:429-433 で reuse) が **adaptation infrastructure を 1 行で供給**。Stein 経路を新規移植する 80-120 行より圧倒的に短い。
- ただし Q-mean (= `∫ Y ∂Q`) **= 0** が必要 — これは **interior optimality** 要件で、`chernoffInfo_attained` だけでは取れない (boundary でも attain しうる)。`exists_interior_minimiser` (P₁ ≠ P₂ + 凸解析) で interior に格上げするのが (a)。

#### step 3 証明 sketch (`isChernoffBandMassToOne_of_interior_optimal`、ChernoffBandMassDischarge.lean:395-530)

```lean
theorem isChernoffBandMassToOne_of_interior_optimal
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (hlam_int : lam ∈ Set.Ioo (0:ℝ) 1)
    (hlam_min : IsMinOn (fun l => chernoffZSum P₁ P₂ l) (Set.Icc 0 1) lam) :
    IsChernoffBandMassToOne P₁ P₂ lam := by
  classical
  -- (1) Q, Y, infinitePi μ の setup
  set Q : Measure α := chernoffMediatorMeasure P₁ P₂ lam
  haveI hQ_prob : IsProbabilityMeasure Q := chernoffMediatorMeasure_isProbabilityMeasure ...
  set Y : α → ℝ := fun a => Real.log (P₁ a) - Real.log (P₂ a)
  set μ : Measure (ℕ → α) := Measure.infinitePi (fun _ : ℕ => Q)
  set X : ℕ → (ℕ → α) → ℝ := fun i ω => Y (ω i)
  -- (2) Q-mean of Y = 0  (interior optimality 経由)
  have h_mean0 : μ[X 0] = 0 := by
    rw [integral_map ..., Measure.infinitePi_map_eval _ 0]
    rw [chernoffMediator_integral_eq, chernoffMediator_mean_logRatio_eq_zero ...]
  -- (3) IID structure: pairwise IndepFun + IdentDistrib
  have h_indep := Cramer.Discharge.iIndepFun_eval_under_infinitePi ...
  have h_ident := Cramer.Discharge.identDistrib_eval_under_infinitePi ...
  -- (4) SLLN: (∑ X i ω) / n →ᵐ 0
  have h_slln := strong_law_ae_real X h_int h_indep h_ident
  -- (5) tendstoInMeasure_of_tendsto_ae
  have h_inm : TendstoInMeasure μ Sn atTop (fun _ => (0:ℝ))
    := MeasureTheory.tendstoInMeasure_of_tendsto_ae ...
  -- (6) tail → 0 (convergence in measure at ε)
  intro ε hε
  have h_tail : Tendsto (fun n => μ {ω | ε ≤ |Sn n ω|}) atTop (𝓝 0) := ...
  -- (7) band mass = (μ.real (T⁻¹ band))  reindex via infinitePi_map_take
  have h_band_eq : ∀ n, 0 < n →
      (∑ x ∈ band.toFinset, ∏ i, mediator (x i))
        = μ.real {ω | |Sn n ω| ≤ ε} := by
    intro n hn
    rw [chernoffMediatorMeasure_pi_real_band, ← infinitePi_map_take Q n,
        Measure.map_apply ...]
    congr 2; ext ω; simp [...]; rw [Fin.sum_univ_eq_sum_range, ...]
  -- (8) band mass = 1 - tail.real, tail.real → 0, so band mass → 1
  have h_band_tendsto : Tendsto (fun n => μ.real {|Sn| ≤ ε}) atTop (𝓝 1) := ...
  -- (9) eventually ≥ 1/2
  filter_upwards [h_band_tendsto.eventually_const_le ..., eventually_gt_atTop 0] with n hn_half hn_pos
  rw [h_band_eq n hn_pos]
  exact hn_half
```

依存補題 (実装通り):
- `strong_law_ae_real` — `Mathlib.Probability.StrongLaw`
- `MeasureTheory.tendstoInMeasure_of_tendsto_ae` — `Mathlib.MeasureTheory.Function.ConvergenceInMeasure`
- `MeasureTheory.Measure.infinitePi_map_eval` — `Mathlib.Probability.ProductMeasure`
- `infinitePi_map_take` (新規補題、ChernoffBandMassDischarge.lean:310、~40 行) — `infinitePi → Measure.pi` 経由
- `chernoffMediator_mean_logRatio_eq_zero` (`:89`) — Fermat + `HasDerivAt.const_rpow` で interior 0
- `exists_interior_minimiser` (`:259`) — strict Gibbs (`Real.log_lt_sub_one_of_pos`) で boundary 排除
- `iIndepFun_eval_under_infinitePi`, `identDistrib_eval_under_infinitePi` — `InformationTheory/Shannon/Cramer/Discharge.lean` (既存)

規模 (実測): ChernoffBandMassDischarge.lean 全 575 行 (うち SLLN core 段 `isChernoffBandMassToOne_of_interior_optimal` が ~135 行、`exists_interior_minimiser` + 補助 boundary 排除 ~85 行、`hasDerivAt_chernoffZSum` + mediator-mean ~70 行、infinitePi reindex ~80 行、Q-LLN bridge ~30 行)。
proof-log: yes — `infinitePi_map_take` の `Measure.pi_eq` 経由 box 計算 (preimage の if-分岐 + Fin↔range 翻訳) が実装上の最大の細部、interior 排除 lemma の `IsLocalMin.hasDerivAt_eq_zero` で `Set.Icc 0 1 ∈ 𝓝 lam` 経由 (`mem_interior_iff_mem_nhds`)。

### Phase 4 — step 1+2+3 合成: ε-relaxed per-tilt lower bound ✅

#### step 2 (per-block normalisation)

`geomMean_eq_Z_pow_mul_prod_mediator` (ChernoffSanovDischarge.lean:260):

```lean
lemma geomMean_eq_Z_pow_mul_prod_mediator
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) {n : ℕ} (x : Fin n → α) :
    (∏ i, P₁ (x i)) ^ (1 - lam) * (∏ i, P₂ (x i)) ^ lam
      = (chernoffZSum P₁ P₂ lam) ^ n *
          ∏ i, ChernoffConverse.chernoffMediator P₁ P₂ lam (x i) := by
  have hZ_pos := chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam
  -- (∏ mediator) = (∏ tilt factor) / Z^n  [unfold + Finset.prod_div_distrib + Finset.prod_const]
  -- (∏ tilt factor) = geomMean [prod_rpow_mul_rpow]
  -- geomMean = Z^n · (geomMean / Z^n) [mul_div_cancel₀]
  ...
```

#### 合成 sketch (`bayesErrorMinPmf_ge_exp_neg_mul_Z_pow`、ChernoffSanovDischarge.lean:289-353)

```lean
theorem bayesErrorMinPmf_ge_exp_neg_mul_Z_pow ... :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-((n : ℝ) * ε)) * (chernoffZSum P₁ P₂ lam) ^ n
        ≤ 4 * bayesErrorMinPmf P₁ P₂ n := by
  have hZ_pos := chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam
  filter_upwards [h_band ε hε] with n hmass
  -- step 1 (each block): apply bayesErrorBlock_ge_exp_neg_mul_geomMean
  have h_block : ∀ x ∈ T, exp(-nε)·geomMean ≤ min := ...
  -- sum over T, factor exp(-nε):
  have h_sum_block : exp(-nε) · ∑_{x∈T} geomMean ≤ ∑_{x∈T} min := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum h_block
  -- step 2: ∑ geomMean = Z^n · ∑ ∏ mediator
  have h_geom_sum : ∑_{x∈T} geomMean = Z^n · ∑_{x∈T} ∏ mediator := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun x _ => ?_)
    exact geomMean_eq_Z_pow_mul_prod_mediator ...
  -- step 3: ∑_{x∈T} ∏ mediator ≥ 1/2  (from hmass)
  have h_mass_ge : Z^n · ∑ ∏ mediator ≥ Z^n · (1/2 : ℝ) :=
    mul_le_mul_of_nonneg_left hmass hZn_nn
  -- restriction to T (Finset.sum_le_sum_of_subset_of_nonneg)
  have h_band_sum_le : (1/2) · ∑_{x∈T} min ≤ bayesError :=
    bayesErrorMinPmf_ge_half_band_sum P₁ P₂ hP₁_pos hP₂_pos
  -- chain: exp(-nε)·Z^n·(1/2) ≤ ∑_{x∈T} min ≤ 2·bayesError
  nlinarith [h_chain, h_band_sum_le, h_exp_nn, hZn_nn]
```

#### ε-aggregation (`chernoff_converse_from_eps_relaxed`、ChernoffSanovDischarge.lean:363-451)

```lean
theorem chernoff_converse_from_eps_relaxed ... :
    Filter.limsup (fun n => -(1/n) · log bayesError) atTop ≤ -log Z(lam) := by
  -- h_bdd_ge / h_bdd_le から limsup_le_iff で発火
  rw [Filter.limsup_le_iff h_bdd_ge.isCoboundedUnder_le h_bdd_le]
  intro b hb
  -- ε := (b - (-log Z))/2 > 0
  -- log 4 / n → 0 なので eventually < ε
  filter_upwards [h_eps ε hε_pos, eventually_gt_atTop 0, h_lt_eps] with n hn_lb hn_pos hn_lt
  -- bayesError ≥ (1/4)·exp(-nε)·Z^n
  -- log bayesError ≥ -log 4 - nε + n·log Z
  -- rate n ≤ log 4 / n + ε + (-log Z) < ε + ε + (-log Z) = b
```

#### 最終 headline (`chernoff_converse_of_bandMass`、ChernoffSanovDischarge.lean:463-477)

```lean
theorem chernoff_converse_of_bandMass ... :
    Filter.limsup (fun n => -(1/n) · log bayesError) atTop ≤ chernoffInfo P₁ P₂ := by
  obtain ⟨lam, hlam_mem, h_eq, h_mass⟩ := h_band
  rw [h_eq]
  refine chernoff_converse_from_eps_relaxed P₁ P₂ hP₁_pos hP₂_pos lam ?_
  intro ε hε
  exact bayesErrorMinPmf_ge_exp_neg_mul_Z_pow ...
```

依存補題:
- `Finset.sum_le_sum_of_subset_of_nonneg` — Mathlib (restrict to band)
- `Finset.mul_sum`, `Finset.sum_congr` — Mathlib
- `geomMean_eq_Z_pow_mul_prod_mediator` (step 2)
- `bayesErrorMinPmf_ge_half_band_sum` (ChernoffSanovDischarge.lean:205)
- `Filter.limsup_le_iff`, `Filter.IsBoundedUnder.isCoboundedUnder_le` — Mathlib
- `chernoff_rate_isBoundedUnder_le` (predecessor、ChernoffConverse.lean) / `chernoff_rate_isBoundedUnder_ge` (ChernoffInformation.lean)

規模 (実測): step 4 合成 ~65 行 + ε-aggregation ~89 行 + headline ~15 行 = ~170 行 (ChernoffSanovDischarge.lean 後半)。
proof-log: yes — `nlinarith` で `(1/2)·∑min ≤ bayesError` と `exp(-nε)·Z^n·(1/2) ≤ ∑min` を chain させる箇所、`h_chain` を内部 calc に分離した方が読めるが nlinarith でも通った。

### Phase 5 — name laundering 解消 + consumer 書換表 📋 (本 Wave 2 の残作業)

実装 (`chernoff_converse_holds` / `chernoff_lemma_tendsto_holds`) は **既に regularity-only headline を publish 済**。残るは:

1. 旧 predicate 経由 publish された ~20 件の `@audit:suspect(...)` を `closed-by-successor(chernoff-converse-sanov-discharge)` へ migration。
2. 旧 `chernoff_per_tilt_via_RN` (循環 `:= h_RN`) の docstring に **Plan-Level Finding** を明示 (両 predicate が一般に偽、ε-relaxed 版が genuine、`ChannelBandMassDischarge.chernoff_converse_holds` 参照)。
3. **`@audit:suspect(chernoff-converse-moonshot-plan)` 3 件** (predecessor plan slug) を本 plan slug へ rebind するか judgement (predecessor は L-CC2 で意図的着地、本 plan が完全 discharge なので **`closed-by-successor`** 適用が妥当)。

#### consumer 書換表 (20 件、Wave 3 並列割当用)

| file | line | symbol | 現タグ | 書換方針 | 規模 |
|---|---|---|---|---|---|
| ChernoffPerTiltSanov.lean | 164 | `IsChernoffNLetterRN` (def) | `suspect(...sanov-discharge-plan)` | `closed-by-successor(chernoff-converse-sanov-discharge)` + docstring: predicate FALSE in general, redirect to `chernoff_converse_holds` | (a) tag migration only |
| ChernoffPerTiltSanov.lean | 175 | `chernoff_per_tilt_via_RN` (`:= h_RN` 循環) | 〃 | (b) 循環 + Plan-Level Finding 明示。tag を `closed-by-successor` + docstring に "circular `:= h_RN`, both predicates false in general — see `ChernoffBandMassDischarge.chernoff_converse_holds`" | (b) docstring 拡充 |
| ChernoffPerTiltSanov.lean | 260 | `chernoff_lemma_tendsto_via_RN` | 〃 | (a) | (a) |
| ChernoffPerTiltSanov.lean | 278 | `isChernoffPerTiltDischargeable_of_RN` | 〃 | (a) | (a) |
| ChernoffPerTiltSanov.lean | 292 | `chernoff_converse_via_RN_forall` | 〃 | (a) | (a) |
| ChernoffPerTiltSanov.lean | 309 | `chernoff_lemma_tendsto_via_RN_forall` | 〃 | (a) | (a) |
| ChernoffPerTiltSanov.lean | 356 | `chernoff_dotEq_tendsto_via_RN` | 〃 | (a) | (a) |
| ChernoffPerTiltDischarge.lean | 162 | `chernoff_converse_from_predicate` | 〃 | (a) | (a) |
| ChernoffPerTiltDischarge.lean | 182 | `chernoff_converse_discharged_from_predicate` | 〃 | (a) | (a) |
| ChernoffPerTiltDischarge.lean | 212 | `chernoff_lemma_tendsto_from_predicate` | 〃 | (a) | (a) |
| ChernoffPerTiltDischarge.lean | 277 | `chernoff_lemma_tendsto_of_per_tilt` (🟢ʰ load-bearing 明示済) | 〃 | (a) + 既存 🟢ʰ docstring 維持 ("predicate FALSE in general" 補足追加) | (b) |
| ChernoffPerTiltDischarge.lean | 306 | `chernoff_dotEq_tendsto_of_per_tilt` (🟢ʰ load-bearing 明示済) | 〃 | (a) + 〃 | (b) |
| ChernoffSanovDischarge.lean | 288 | `bayesErrorMinPmf_ge_exp_neg_mul_Z_pow` (genuine ε-relaxed) | 〃 | **`closed-by-successor` ではなく そのまま suspect 維持 → `audit` agent 判定で `staged(chernoff-converse-bandmass-residual)` か別タグ**。`IsChernoffBandMassToOne` 残仮説経由なので **`staged(<slug>)`** が妥当 (本 plan が完全 discharge なら `closed-by-successor`、staged であれば residual) | **(c) audit agent 判定要** |
| ChernoffSanovDischarge.lean | 362 | `chernoff_converse_from_eps_relaxed` (genuine ε-aggregation) | 〃 | (a) `closed-by-successor` (本 plan slug、規律: 後継 file `ChernoffBandMassDischarge` で discharge 完了) | (a) |
| ChernoffSanovDischarge.lean | 462 | `chernoff_converse_of_bandMass` (genuine but band-mass hyp) | 〃 | (a) `closed-by-successor` (本 plan で `chernoff_converse_holds` が discharge) | (a) |
| ChernoffConverse.lean | 273 | `chernoff_converse_from_per_tilt` (predecessor) | `suspect(chernoff-converse-moonshot-plan)` | (a) `closed-by-successor(chernoff-converse-sanov-discharge)` (predecessor plan の load-bearing が本 plan で discharge) | (a) |
| ChernoffConverse.lean | 411 | `chernoff_converse_of_per_tilt_existential` | 〃 | (a) | (a) |
| ChernoffConverse.lean | 446 | `chernoff_lemma_tendsto_from_per_tilt` | 〃 | (a) | (a) |
| ChernoffInformation.lean | 125 | `chernoff_lemma_tendsto` (h_converse hyp 形) | `closed-by-successor(chernoff-converse-sanov-discharge)` **既設** | 既設のまま (本 plan が完成すれば validate)、docstring に `chernoff_lemma_tendsto_holds` 参照を追記 | (b) |
| ChernoffInformation.lean | 197 | `chernoff_dotEq_tendsto` | 〃 既設 | 〃 | (b) |

**集計**: 直接タグ書換 (a) 15 件 / docstring 拡充 (b) 4 件 / audit agent 判定要 (c) 1 件 (= ChernoffSanovDischarge.lean:288)。
※ Wave 1.5 で既に `closed-by-successor` を付与した ChernoffInformation.lean:125, 197 (2 件) は **再記録 (タグ維持 + docstring 改善)** で 1 commit。

#### 旧 predicate の運命

`IsBayesErrorPerTiltLowerBound` (`ChernoffPerTiltDischarge.lean:136`) / `IsChernoffNLetterRN` (`ChernoffPerTiltSanov.lean:140`) 自体は **削除しない** (predecessor file は過去参照として残置)。docstring に:

```
/-- ... predicate as stated is FALSE in general (constant `C` does not exist due to
the `Θ(1/√n)` Cramér local-limit prefactor; see
`ChernoffBandMassDischarge.lean` opening docstring). The ε-relaxed version
`bayesErrorMinPmf_ge_exp_neg_mul_Z_pow` is what the genuine proof produces.
This predicate is preserved for historical reference only; consumers should
route through `ChernoffBandMassDischarge.chernoff_converse_holds` or
`chernoff_lemma_tendsto_holds`.
`@audit:closed-by-successor(chernoff-converse-sanov-discharge)` -/
```

を追記する (Wave 3 lean-implementer の brief で「逐次 Edit」と指示)。

依存補題: なし (タグ migration + docstring 編集のみ)。

規模 (Wave 3 想定): 並列 5 (file 単位) で agent dispatch、各 agent 数十分。
~20 件タグ書換 + ~6 件 docstring 拡充 + 1 件 audit subagent 判定要。
InformationTheory.lean は変更不要 (既設 import 186/187)。

### Phase 6 — verify + InformationTheory 編入 + roadmap 📋

- [x] `lake env lean InformationTheory/Shannon/ChernoffSanovDischarge.lean` silent (実装完了済)。
- [x] `lake env lean InformationTheory/Shannon/ChernoffBandMassDischarge.lean` silent (実装完了済)。
- [x] `InformationTheory.lean` 行 186-187 に既に編入済:
  ```
  186:import InformationTheory.Shannon.ChernoffSanovDischarge
  187:import InformationTheory.Shannon.ChernoffBandMassDischarge
  ```
  (`ChernoffPerTiltSanov` は行 185。本 plan 起草時の目標「行 183 以降」と整合。)
- [ ] Phase 5 完了後、`docs/textbook-roadmap.md` の Chernoff converse 行を 🟢ʰ → 🟢 (regularity-only 完全 discharge) に更新、本 plan §判断ログ + roadmap 判断ログに「ε-relaxed 経路で per-tilt predicate を bypass、`IsBayesErrorPerTiltLowerBound` 自体が一般に偽と判明、`chernoff_converse_holds` が genuine headline」を記録。
- [ ] `#check chernoff_lemma_tendsto_holds` で hypothesis 一覧が `[Nonempty α]` + `hP₁_pos hP₂_pos hP₁_sum hP₂_sum hne` (すべて regularity hyp) のみであることを機械確認。

規模: ~10 行 (roadmap 行更新 + judgement log)。

---

## 撤退ライン (honest 限定)

step 1 か step 3 で本物の Mathlib gap に当たった場合のみ。`:True` / 結論同型述語への再逃避は禁止。
**実装後の判定**: L-SD1 / L-SD2 とも **不発動**。下記は元のまま (起草時の判断、record として保持)。

**L-SD1** (step 3 の Sanov LLN 移植が Mathlib gap): Stein
`steinTypicalSet_P_prob_tendsto_one` は `Ω` 上の独立確率変数列 (`Xs : ℕ → Ω → α` +
`Pairwise IndepFun` + `IdentDistrib`) で書かれており、`Measure.pi` 直接形への adaptation で
**独立性の供給** (`Measure.pi` の coordinate 独立を `IndepFun` 形に変換する Mathlib 補題) が
欠けていたら、step 3 を **honest な名前付き仮説**で抜く:

```lean
/-- NOT a discharge. load-bearing: tilted mediator の n-letter typical set 確率が
1 に収束する弱大数。Sanov LLN の Measure.pi 形 adaptation が Mathlib gap のとき退避。
型 ≠ 結論 (結論は per-tilt lower bound、これはその一構成要素)。 -/
def IsChernoffTiltedTypicalProbToOne (P₁ P₂ : α → ℝ) (lam : ℝ) : Prop := ...
```

**実装後の状況**: 実装で **`IsChernoffBandMassToOne` (`ChernoffSanovDischarge.lean:243`) という honest residual を経由したが、それも `ChernoffBandMassDischarge` で genuine discharge した**。最終的に L-SD1 不発動。`IsChernoffBandMassToOne` は honest 4 条件 (NOT a discharge, type ≠ conclusion, docstring で load-bearing 明示, `:True` でない) を満たしており、後続 file で完全に discharge されたので「中間 residual」として残置 (公開 API は `chernoff_converse_of_bandMass` だが consumer は `chernoff_converse_holds` 経由)。

ただし step 1 (逆 Hölder) は **必ず genuine に証明する** (これは pure な実解析で Mathlib gap
なし、退避不可)。L-SD1 採用時も step 1+2+4 は genuine、step 3 のみ仮説化。
**name laundering 禁止**: 退避した仮説を `*_discharged` と命名しない。

**L-SD2** (redefine が step 1/4 で不可避と判明): M0 または Phase 4 で「min-和 ↔ Q^n(T_n)
集合測度」の昇格が ~50 行を超え、`bayesErrorMinPmf` redefine が安いと判明した場合のみ。
**実装後の状況**: `chernoffMediatorMeasure_pi_real_band` (ChernoffBandMassDischarge.lean:354) で ~25 行で閉じた。L-SD2 不発動。

---

## 検証

- 各 Phase: `lake env lean InformationTheory/Shannon/ChernoffSanovDischarge.lean`,
  `lake env lean InformationTheory/Shannon/ChernoffBandMassDischarge.lean` が silent
  (0 sorry / 0 warning)。すでに実装完了で実測 silent (last commit 時点)。`lake build` は使わない。
- Phase 5 後、predecessor file (`ChernoffPerTiltSanov.lean`, `ChernoffPerTiltDischarge.lean`,
  `ChernoffConverse.lean`) の docstring 編集後は `lake build InformationTheory.Shannon.ChernoffPerTiltSanov`
  などで olean refresh。
- 最終: 無条件 headline `chernoff_lemma_tendsto_holds` が
  `IsBayesErrorPerTiltLowerBound` / `IsChernoffNLetterRN` を **一切 hypothesis に取らない**
  ことを `#check` で確認 (= 標準B 達成の機械チェック)。実装ベースで既に成立、`P₁ ≠ P₂` は regularity hyp。

---

## 判断ログ

> 書く頻度: Phase 終了時 / 設計変更 / 撤退判定。append-only。

1. **2026-05-21 起草** (本セッション): predecessor `chernoff-converse-moonshot-plan.md`
   (L-CC2 着地、per-tilt predicate を残置) の後継として本 plan を新規。独立 strategy 再評価の
   結論 (CLT-port 不可 / Sanov 経由が正) を採用。**設計判断: `bayesErrorMinPmf` redefine
   しない** — 支配補題 `typeClassByCount_Qn_ge` (`SanovLDPEquality.lean:918`) /
   `sanov_ldp_lower_bound_pointwise` (`:1071`) の conclusion (`Measure.pi Q` 上集合測度) と
   現 min-和形の bridge は predecessor の `chernoffMediatorMeasure_pi_singleton`
   (`ChernoffPerTiltSanov.lean:202`) で既に架かっており、redefine の純利益なし。むしろ
   achievability チェーン (`Chernoff.lean:779`-`:1064`) を壊す損が確実。残りは step 1
   (逆 Hölder on typical set、唯一の新規数学) + step 3 (Sanov LLN 移植、Stein
   `Stein.lean:275` がテンプレート)。規模 ~150-300 行。

2. **honesty defect 記録** (起草時に発見): `chernoff_per_tilt_via_RN`
   (`ChernoffPerTiltSanov.lean:165`) は `IsChernoffNLetterRN` ≡ `IsBayesErrorPerTiltLowerBound`
   (body 字面一致、`:140` vs `:136`) で body `:= h_RN` の **循環 / name laundering**。
   predecessor docstring は honest に「pass-through」と書くが標準B では残タスク。
   本 plan Phase 5 で genuine な無条件 headline を新規 publish して解消する
   (既存 `:= h_RN` lemma は過去参照で残置、docstring に defect 明示を追記指示)。

3. **2026-05-24 Wave 2 planner refine (本セッション)**: 実装ベースで plan を全面 update。
   主な refinements:
   - M0 inventory を **verbatim signature + `[...]` 型クラス前提 + conclusion** で 12 補題確定 (CLAUDE.md「Subagent Inventory of Mathlib Lemmas」遵守)。Mathlib 側 (`sum_measureReal_singleton`, `Measure.infinitePi_map_eval`, `strong_law_ae_real`) は loogle で実在確認。**M0 結論: Mathlib gap なし、L-SD1/L-SD2 不発動**。
   - Phase 2 の κ explicit は **κ(ε) = exp(-n·ε)** (per-point form `exp(-δ)` を block で `δ := n·ε` 起動)。実装 (`min_ge_exp_neg_mul_rpow_mul_rpow`、ChernoffSanovDischarge.lean:106-161) で確定。
   - Phase 3 経路は **(a) Stein 移植ではなく (c) SLLN on `Measure.infinitePi Q` 直接** に pivot。Stein は `(μ : Measure Ω) + Xs : ℕ → Ω → α` 形で、Chernoff の natural ambient `Measure.pi (Fin n) Q` への adaptation が逆方向に余分なので、`strong_law_ae_real` を `Measure.infinitePi Q` 上で直接適用 + `infinitePi_map_take` で `Measure.pi (Fin n) Q` へ reindex する方が短い (実装で確証、ChernoffBandMassDischarge.lean:395 ~135 行)。さらに Q-mean = 0 は **interior optimality** 要件で、`exists_interior_minimiser` (P₁ ≠ P₂ + strict Gibbs) で boundary 排除して取り出す。
   - Phase 4 合成 sketch を Lean-pseudocode 20-30 行で plan に書き下し (`chernoff_converse_of_bandMass` までの calc + tactics)。
   - **Phase 5 consumer 書換表 (20 件)** を Wave 3 並列割当用に file × line × tag migration 方針で表化。直接タグ書換 (a) 15 件 / docstring 拡充 (b) 4 件 / audit agent 判定要 (c) 1 件 (= `ChernoffSanovDischarge.lean:288` `bayesErrorMinPmf_ge_exp_neg_mul_Z_pow` 、本 plan slug の `closed-by-successor` か `staged(<別 slug>)` か独立監査要)。Wave 1.5 で既設の `closed-by-successor` 2 件 (ChernoffInformation.lean:125, 197) は再記録のみ。
   - Phase 6 import 行確認: 既に `InformationTheory.lean:186-187` に `ChernoffSanovDischarge` / `ChernoffBandMassDischarge` 編入済 (`ChernoffPerTiltSanov` 行 185 の直後)。
   - **規模見積り再校正 (実測)**: 当初 ~150-300 行 → 実測 **~1054 行** (ChernoffSanovDischarge 479 + ChernoffBandMassDischarge 575)。超過の主因は (i) `IsChernoffBandMassToOne` を honest residual として正式に置いて discharge したこと、(ii) interior optimality 補助補題群 (`hasDerivAt_chernoffZSum`, `gibbs_cross_sum_neg`, `not_isMinOn_*`, `exists_interior_minimiser`) ~200 行、(iii) infinitePi reindex 補助 (`infinitePi_map_take`, `chernoffMediatorMeasure_pi_real_band`) ~80 行。**gap な大量化ではなく完全 discharge を最後まで通した結果**。
   - **Plan-Level Finding** (実装中に発見、ChernoffSanovDischarge.lean 冒頭 docstring に記録): `IsBayesErrorPerTiltLowerBound` 述語は **一般に偽** (Cramér local-limit prefactor `Θ(1/√n)` のため定数 `C` 不存在)。ε-relaxed 形 (`exp(-n·ε)·Z^n ≤ 4·bayesErrorMinPmf`) が genuine な対象であり、本 plan Phase 4 を起草時 target (`IsBayesErrorPerTiltLowerBound` を genuine に構成) から **ε-relaxed pivot** に変更して着地。
