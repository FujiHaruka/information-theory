# AWGN converse: C-5 transitive MI 有限性 bridge mini-plan

> **Parent**: [`awgn-converse-aux-plan.md`](awgn-converse-aux-plan.md) §「Phase C 失敗時 fallback (line 905-921)」C-5 項 / 判断ログ #6「後続セッション送り (3)」
>
> **Slug**: `awgn-converse-c5-mi-finite-bridge`
>
> **対象 sorry 3 件 (同時 closure を期待、ENNReal 形 per-letter bound 経由)**:
>
> - `InformationTheory/Shannon/AWGNConverseDischarge.lean:395`
>   `awgnConverseJoint_mutualInfo_ne_top` body
>   (現タグ `@residual(plan:awgn-converse-aux-plan)`、wall 想定 `wall:multivariate-mi`)
> - `InformationTheory/Shannon/AWGNConverseDischarge.lean:502`
>   `awgn_dpi` body 内 inline `h_finite : (jointMIXnYn h_meas c) ≠ ∞`
>   (現タグ `@residual(plan:awgn-converse-aux-plan)`、wall 想定 `wall:multivariate-mi`)
> - `InformationTheory/Shannon/AWGNConverseDischarge.lean:1175`
>   `awgnConverseJoint_mutualInfo_ne_top_via_chain` body
>   (現タグ `@residual(plan:awgn-converse-aux-plan)`、wall 想定 `wall:multivariate-mi`)
>
> **Status (2026-05-27)**: 起草。M1 (`awgn-converse-c1b-gaussian-maxent`) が
> `awgn_per_letter_mi_le_log_var` (line 901) を 0 sorry / 0 @residual 化済 (commit
> `84e013c` 後の状態で confirmed via Read line 887-998)。本 mini-plan は M1 で publish
> された per-letter `.toReal ≤ (1/2) log(1 + S²/N)` 形を **ENNReal-lift** し、
> Finset sum / chain rule / Markov DPI の transitive 伝播で 3 sorry 同時 closure。

## 進捗

- [ ] M0 — Mathlib API verbatim 在庫 + ENNReal-lift 経路の存在確認 (本 plan 内で済、§Mathlib 在庫確認) ✅
- [ ] M1 — shared helper `awgn_per_letter_mi_ne_top` (ENNReal 形 per-letter bound、M1 結果から `ofReal_toReal` lift) 📋
- [ ] M2 — shared helper `awgnConverseJoint_jointMIXnYn_ne_top` (chain rule + Finset sum 経由、X^n 側 ne_top) 📋
- [ ] M3 — 3 sorry 同時 closure (`awgnConverseJoint_mutualInfo_ne_top` 経由 Markov DPI / `awgn_dpi` inline / `awgnConverseJoint_mutualInfo_ne_top_via_chain` の合成形) 📋
- [ ] M4 — verify + tag 解消 + `wall:multivariate-mi` reclassify 判断 📋

## ゴール / Approach

### Goal (target signatures、verbatim 維持、改変禁止)

3 declaration すべて **signature 改変なし** で body の `sorry` を埋める。

```lean
-- 1. AWGNConverseDischarge.lean:389
private lemma awgnConverseJoint_mutualInfo_ne_top
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    mutualInfo (awgnConverseJoint h_meas c)
        (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
        (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) ≠ ∞

-- 2. AWGNConverseDischarge.lean:468 (awgn_dpi body 内 inline)
have h_finite : (jointMIXnYn h_meas c) ≠ ∞

-- 3. AWGNConverseDischarge.lean:1159
theorem awgnConverseJoint_mutualInfo_ne_top_via_chain
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (hn_pos : 0 < n) (c : AwgnCode M n P)
    (h_per_letter : PerLetterIntegrabilityForConverse P N h_meas c)
    (h_chain : ContinuousMIChainRuleForConverse P N h_meas c)
    (h_markov : MarkovChainForConverse P N h_meas c)
    (h_mi_bridge_per_letter : ∀ i : Fin n, (perLetterMI h_meas c i).toReal = …) :
    mutualInfo (awgnConverseJoint h_meas c)
        (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
        (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) ≠ ∞
      ∧ jointMIXnYn h_meas c ≠ ∞
```

bundle predicate / load-bearing hypothesis の追加禁止 (3 declaration とも既存
hypothesis 群で closure 可能、本 mini-plan は wall:multivariate-mi の **plan-level
closure** であって新規 wall packaging ではない)。

### Approach (overall strategy / shape of solution — 必須 §)

**戦略**: M1 の per-letter `.toReal ≤ (1/2)log(1+S²/N)` を **ENNReal-lift** して
per-letter `(perLetterMI) ≠ ∞` を立てる → `Finset.sum` で `∑ᵢ (perLetterMI) ≠ ∞`
→ chain rule (`ContinuousMIChainRuleForConverse` の **ENNReal 形 wrapping**) で
`(jointMIXnYn) ≠ ∞` → Markov DPI (`mutualInfo_le_of_markov` の ENNReal 結論) で
`(jointMIWYn) ≠ ∞` (= Fano 側目的) → 3 sorry 同時 closure。

#### 退化境界 trap の回避 (M1 観察反映、CLAUDE.md「具体的数値・型予測の verbatim 確認」)

既存 `ContinuousMIChainRuleForConverse` (`AWGNConverseDischarge.lean:165-169`、
verbatim Read 済) は **Real 形 `(jointMIXnYn).toReal ≤ ∑ᵢ (perLetterMI).toReal`** で
定義されている — これは退化境界 `(jointMIXnYn) = ∞ → .toReal = 0` で trivially
true、ne_top を直接導けない (= CLAUDE.md「退化定義悪用」直撃 risk、親 plan 判断
ログ #6「現状は `.toReal ≤ R` で `∞.toReal = 0` 退化境界が引っかかる」と一致)。

3 経路で対応:

| 経路 | 内容 | 採否判定 |
|---|---|---|
| (α) bundle predicate を ENNReal 形に置換 (`(jointMIXnYn) ≤ ∑ᵢ (perLetterMI)`) | signature 改変 → Phase A bundle 再設計 + Phase B-chain 再 publish → scope creep (影響範囲大) | **不採用** (本 mini-plan scope 外) |
| (β) ENNReal 形 chain rule を `awgnConverseJoint_mutualInfo_ne_top_via_chain` の **追加 hypothesis** として外注供給 (`h_chain_ennreal : (jointMIXnYn) ≤ ∑ᵢ (perLetterMI)`) | signature 改変 = 1 hyp 追加、staged hyp T-FFC-3 の本質的 packaging (= regularity bundle 拡張)、本 mini-plan で closure 完了 | **採用 (case A)** |
| (γ) per-letter MI ENNReal 形 bound `(perLetterMI) ≤ ENNReal.ofReal((1/2)log(1+S²/N))` を本 mini-plan で立てる → Finset.sum で `∑ᵢ (perLetterMI) ≤ ENNReal.ofReal(∑ᵢ ...) < ∞` → ne_top 推論 → `ContinuousMIChainRuleForConverse` (Real 形) は **使わない**、ne_top の伝播のみ別経路 | per-letter ENNReal-lift 1 件 + `Finset.sum` ne_top 経路、chain rule の ENNReal 形は **不要** (sum_ne_top で済む)、bundle 改変なし | **採用 (case B、優先)** |

**case B 優先** (Approach 確定): bundle / signature 改変なしで `Finset.sum ne_top`
経路で chain rule を 1 度も使わず ne_top を立てる。chain rule 自体 (Real 形) は
`isAwgnConverseFeasible_discharger` body 内で別途使用済 (line 1213 `h_chain_le`)
だが、本 mini-plan の ne_top 伝播経路では **触らない**。

ただし最終 declaration 3 (= `awgnConverseJoint_mutualInfo_ne_top_via_chain`) の
**W → X^n DPI 経路** で `jointMIXnYn ≠ ∞` から `jointMIWYn ≠ ∞` を導く必要があり、
この 1 段で `mutualInfo_le_of_markov` (`CondMutualInfo.lean:385`、verbatim 確認済
ENNReal 形 `mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo`) + `ne_top_of_le_ne_top` で
直接 closure 可。

#### 流れ (case B、3 sorry 同時 closure)

```
M1 結果 (`awgn_per_letter_mi_le_log_var`、本 mini-plan の入力):
    ∀ i, (perLetterMI h_meas c i).toReal ≤ (1/2) log(1 + perLetterInputSecondMoment c i / N)

           ↓ (ENNReal-lift via `ENNReal.ofReal_le_iff_le_toReal` + per-letter ne_top)

shared helper M1 (`awgn_per_letter_mi_ne_top`):
    ∀ i, (perLetterMI h_meas c i) ≠ ∞
    
           ↓ (Finset.sum_ne_top)

shared helper M2 (`awgnConverseJoint_jointMIXnYn_ne_top`):
    jointMIXnYn h_meas c ≠ ∞   ←  ← sorry 2 (line 502 inline) 直接 closure

           ↓ (mutualInfo_le_of_markov ENNReal 形 + ne_top_of_le_ne_top)

target sorry 1 (line 395) + sorry 3 (line 1175, 左半分):
    mutualInfo (awgnConverseJoint h_meas c) Prod.fst Prod.snd ≠ ∞
    (= jointMIWYn h_meas c ≠ ∞、jointMIWYn def unfold で同型)
```

ne_top の伝播経路は **1 方向: per-letter → ∑ → X^n → W**。chain rule (Real 形) は
触らず、`mutualInfo_le_of_markov` (ENNReal 形) と `ENNReal.sum_ne_top` /
`ne_top_of_le_ne_top` の 2 primitives で完結。

#### M1 ENNReal-lift の詳細 (shared helper `awgn_per_letter_mi_ne_top`)

```lean
private lemma awgn_per_letter_mi_ne_top
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P)
    (h_per_letter : PerLetterIntegrabilityForConverse P N h_meas c)
    (h_mi_bridge_per_letter :
        ∀ i : Fin n, (perLetterMI h_meas c i).toReal = …) :
    ∀ i : Fin n, (perLetterMI h_meas c i) ≠ ∞ := by
  intro i
  -- 経路 (a): `(perLetterMI).toReal` が finite real value を取る ⇒ ne_top
  -- 直接 path: `(perLetterMI ≠ ∞ ↔ (perLetterMI).toReal が genuine な値)` の Mathlib lemma
  -- 探索 → `ENNReal.toReal_eq_toReal_iff` 等は ne_top 前提なので使えない、
  -- M1 結果が `.toReal ≤ R` 形なので ne_top を直接得る lemma が無い退化境界 trap が
  -- M1 段階で残っている。
  -- 採用経路: per-letter MI の ne_top を **independent route** で立てる:
  --   per-letter MI = klDiv (joint_i) (prod_i) (InformationTheory `mutualInfo` def 経由)
  --   joint_i の AbsolutelyContinuous prod_i + integrable llr ⇒ `klDiv_ne_top`
  -- これは M1 結果に依存しない genuine route で、`differentialEntropy_le_gaussian_*`
  -- の `h_var_int` / `h_ent_int` (= bundle 内 `h_per_letter`) と同型の analytic primitive。
  sorry  -- 詳細 → §「Mathlib 在庫確認」M1-route
```

**鍵: per-letter MI ne_top は M1 結果 `.toReal ≤ R` から直接出ない** (退化境界
trap)。本 mini-plan 内で **independent route** で立てる必要がある:

1. **route (i) — klDiv 経由 (推奨)**:
   `mutualInfo` def `:= klDiv (jointDistribution) (prod marginals)` を unfold し
   `klDiv_ne_top` (Mathlib `KullbackLeibler.lean`、AbsolutelyContinuous + Integrable
   llr 前提) で discharge。per-letter は AWGN 1-d なので Gaussian convolution
   absolute continuity + bundle 内 `h_per_letter i` integrability から 2 前提 OK。

2. **route (ii) — InformationTheory `mutualInfo_ne_top` 拡張**:
   `MutualInfo.lean:197` を見ると `[Fintype X] [Fintype Y]` 両側要求、AWGN
   Y_i ∼ ℝ で reuse 不可。継続 reuse は不可だが、片側 Fintype 緩和の variant
   (= Mathlib にあるかも) を Phase 0 で loogle で確認。在庫不在なら route (i)
   で進む。

3. **route (iii) — Mathlib 一般 MI ne_top**:
   `Mathlib/InformationTheory/MutualInfo.lean` 系の本家 mutualInfo ne_top
   lemma の存在を Phase 0 で確認。loogle `"ProbabilityTheory.mutualInfo, _ ≠ ⊤"`
   の結果 `Found 0` (本 plan 起草時の Bash 確認結果、§Mathlib 在庫確認) ⇒
   route (iii) は **不在確定**、route (i) または (ii) で進む。

#### Mathlib-shape-driven (CLAUDE.md)

`ENNReal.sum_ne_top` の結論形 `∑ a ∈ s, f a ≠ ∞ ↔ ∀ a ∈ s, f a ≠ ∞`
(`BigOperators.lean:88` verbatim) は本 mini-plan の M2 目標形と完全一致 ⇒
bridge 不要 ✅

`mutualInfo_le_of_markov` の結論形 `mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo`
(ENNReal、`CondMutualInfo.lean:385` verbatim) + `ne_top_of_le_ne_top` で
`mutualInfo μ Xs Yo ≠ ∞` 導出可。bridge 不要 ✅

`klDiv_ne_top` の前提 (AbsolutelyContinuous + Integrable llr) の AWGN 1-d
per-letter での充足は M0 で verbatim 確認 (`InformationTheory/Shannon/KullbackLeibler.lean`
等を Read)。route (i) で進む場合の必須前提。

### 規模見積もり

| Phase | 内容 | 楽観 | 中央 | 悲観 (壁発動) |
|---|---|---:|---:|---:|
| M0 | 在庫確認 (本 plan 起草時 verbatim 確認済、Phase 0 reset 不要) | 0 | 0 | 0 |
| M1 | `awgn_per_letter_mi_ne_top` (klDiv 経由 route (i)、AbsolutelyContinuous + integrable llr 構築) | 20 | 40 | 80 |
| M2 | `awgnConverseJoint_jointMIXnYn_ne_top` (Finset.sum_ne_top mechanical assembly) | 5 | 15 | 30 |
| M3 | 3 sorry 同時 closure (DPI ENNReal 経路 + per-decl wiring) | 15 | 30 | 50 |
| M4 | verify + tag 解消 | 0 | 0 | 0 |
| **合計** | | **~40** | **~85** | **~160** |

中央予測 **~85 行、0.5-1 session** (起案 ~50-100 行 から M1 route (i) klDiv 経路の
構築コスト ~40 行で上振れ補正)。中央 100 行を超えた場合は撤退ライン
T-MIF-1 / T-MIF-3 発動。

---

## Mathlib + InformationTheory 在庫 (M0、verbatim、本 mini で利用するもの全列挙)

CLAUDE.md「具体的数値・型予測の verbatim 確認」遵守。signature paraphrase 禁止、
`[...]` 型クラス前提含む verbatim。

### A. ENNReal sum / ne_top primitives (Mathlib)

**`Mathlib/Data/ENNReal/BigOperators.lean:88`** (verbatim、本 plan 起草時 Read 済):

```lean
/-- A sum is finite iff all summands are finite. -/
lemma sum_ne_top : ∑ a ∈ s, f a ≠ ∞ ↔ ∀ a ∈ s, f a ≠ ∞ := WithTop.sum_ne_top
```

namespace: `ENNReal.sum_ne_top`。型クラス前提なし (本 lemma 上の `s : Finset α`
`f : α → ℝ≥0∞` のみ、`Mathlib.Data.ENNReal.BigOperators` 冒頭の `variable`
ブロック)。

**`Mathlib/Data/ENNReal/BigOperators.lean:91`**:

```lean
@[simp] lemma sum_lt_top : ∑ a ∈ s, f a < ∞ ↔ ∀ a ∈ s, f a < ∞ := WithTop.sum_lt_top
```

**`Mathlib/Data/ENNReal/BigOperators.lean:93`**:

```lean
theorem lt_top_of_sum_ne_top {s : Finset α} {f : α → ℝ≥0∞}
    (h : ∑ x ∈ s, f x ≠ ∞) {a : α} (ha : a ∈ s) : f a < ∞ :=
  sum_lt_top.1 h.lt_top a ha
```

(本 mini-plan では逆向き — per-letter ne_top から sum ne_top — のみ必要、こちらは
`sum_ne_top.mpr` で 1 行)

### B. ENNReal toReal / ofReal / ne_top conversion (Mathlib)

**`Mathlib/Data/ENNReal/Real.lean:67`** (verbatim):

```lean
@[gcongr]
theorem toReal_mono (hb : b ≠ ∞) (h : a ≤ b) : a.toReal ≤ b.toReal :=
  (toReal_le_toReal (ne_top_of_le_ne_top hb h) hb).2 h
```

`ne_top_of_le_ne_top` (Mathlib `WithTop`、`a ≤ b → b ≠ ∞ → a ≠ ∞`) — 本 mini-plan
M3 で `(jointMIXnYn) ≠ ∞` から `(jointMIWYn) ≤ (jointMIXnYn)` 経由 `(jointMIWYn) ≠ ∞` を導く 1 行。

**`Mathlib/Data/ENNReal/Basic.lean:340`**:

```lean
@[simp] theorem ofReal_lt_top {r : ℝ} : ENNReal.ofReal r < ∞ := coe_lt_top
```

(本 mini-plan case B では `ENNReal.ofReal` route を最終的に使わない見込み、
Reserved fallback)

### C. mutualInfo / DPI primitives (InformationTheory)

**`InformationTheory/Shannon/CondMutualInfo.lean:385`** (verbatim Read 済):

```lean
@[entry_point]
theorem mutualInfo_le_of_markov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo
```

**結論は ENNReal 形 `≤`** (= `ℝ≥0∞` 上)。`ne_top_of_le_ne_top` (Mathlib) と組み合わせ
`(jointMIXnYn) ≠ ∞` から `(jointMIWYn) ≠ ∞` 1 行。

型クラス前提: `[StandardBorelSpace X]` `[Nonempty X]` `[StandardBorelSpace Y]`
`[Nonempty Y]`。本 mini-plan 起動形は `X := Fin M` (Finite ⇒ StandardBorelSpace
自動) + `Z := Fin n → ℝ` (`instStandardBorelSpacePi` 自動) + `Y := Fin n → ℝ`
(同上)。`Nonempty` も `[NeZero M]` から `Fin M` 自動、`Fin n → ℝ` は trivially
nonempty (関数空間)。

**`InformationTheory/Shannon/MutualInfo.lean:197`** (既存 `mutualInfo_ne_top`、AWGN
converse で reuse 不可):

```lean
@[entry_point]
theorem mutualInfo_ne_top
    [Fintype X] [MeasurableSingletonClass X]
    [Fintype Y] [MeasurableSingletonClass Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    mutualInfo μ Xs Yo ≠ ∞
```

**両側 `[Fintype]` 要求** ⇒ AWGN `Y := Fin n → ℝ` (continuous) で reuse 不可
(既存 inventory 判断 + plan §385 と一致)。本 mini-plan M1 で **route (i) klDiv
経由** に進む根拠。

### D. mutualInfo definition + klDiv ne_top (InformationTheory)

**`InformationTheory/Shannon/MutualInfo.lean`** (mutualInfo definition、本 plan 起草時に
Read で確認、verbatim):

```lean
noncomputable def mutualInfo (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞ :=
  klDiv (μ.map (fun ω => (Xs ω, Yo ω))) ((μ.map Xs).prod (μ.map Yo))
```

(line 番号は M0 で再確認、本 plan 起草時に approximate 形式は他箇所から推定)

**`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`** (klDiv ne_top の
verbatim signature は M0 で再確認、推定形):

```lean
theorem klDiv_ne_top
    {μ ν : Measure α} [IsFiniteMeasure μ] (hμν : μ ≪ ν)
    (h_integrable : Integrable (llr μ ν) μ) : klDiv μ ν ≠ ∞
```

(本 plan 起草時の loogle 検索: `klDiv_ne_top` Found 1 declaration、`Mathlib/InformationTheory/KullbackLeibler/Basic.lean` 系。M0 で正確 line 確認必須。
**重要前提**: `[IsFiniteMeasure μ]` + `μ ≪ ν` + `Integrable (llr μ ν) μ`)

M1 で per-letter MI = `klDiv (joint_i) (prod_i)` に unfold、AC + integrable llr
の 2 前提が AWGN 1-d でどう供給されるかは M0 で再 verbatim 確認:

- AC `joint_i ≪ prod_i`: AWGN per-letter joint は `(uniform W) ⊗ AWGN kernel` で
  prod marginals に AC、Gaussian convolution density 経由 (InformationTheory 既存
  `InformationTheory/Shannon/MutualInfo.lean` 内 `map_pair_absolutelyContinuous_prod_marginals`
  系の reuse 可否を M0 で確認)
- Integrable llr: bundle 内 `h_per_letter i : Integrable (negMulLog ∘ rnDeriv)
  volume` から `llr ∘ ...` への形 bridge を別途要する場合あり (= ~10-30 行
  plumbing)。M0 で `Integrable (llr (joint_i) (prod_i)) (joint_i)` を直接立てる
  Mathlib 在庫 / InformationTheory 既存補題を確認

### E. InformationTheory 既存 mutualInfo helper (本 mini-plan で reuse 候補)

- `InformationTheory/Shannon/MutualInfo.lean:165-191` 周辺の
  `map_pair_absolutelyContinuous_prod_marginals` / `integrable_llr_map_pair_prod_marginals`
  (本 plan 起草時 line 188-191 で `integrable_llr_*` 確認、Fintype 想定なので AWGN 1-d
  per-letter で reuse 可否は M0 で再 verbatim 確認、route (i) M1 規模を左右する)

### F. Loogle で M0 時に再確認すべき項目

(本起草時には index で軽く確認、M0 phase で再度回す)

- `loogle "ProbabilityTheory.klDiv, _ ≠ ⊤"` — `klDiv_ne_top` の正確 file:line +
  型クラス前提
- `loogle "ProbabilityTheory.mutualInfo, _ ≤ _"` の Y 側 Fintype 制約緩和 variant
  の在庫確認
- `loogle "Measure.AbsolutelyContinuous, gaussianReal"` — per-letter joint の AC
  経路 (AWGN kernel が Gaussian convolution density 経由で `volume` ⊗ 形に AC)
- `loogle "Integrable, llr"` — bundle 内 `Integrable (negMulLog ∘ rnDeriv) volume`
  から `Integrable (llr) μ` への bridge 在庫

## Sub-bound 引数表 (CLAUDE.md brief checklist 必須項目)

本 mini-plan は **3 sorry 同時 closure** で sub-bound 多数を扱うので、各 sorry の
hypothesis 供給元と shared helper への入出力を 1 表で明示:

| sorry (line) | declaration | 必要 hypothesis | shared helper 経由 | 直接呼ぶ Mathlib lemma |
|---|---|---|---|---|
| line 395 | `awgnConverseJoint_mutualInfo_ne_top` (private) | `[NeZero M]` + bundle 不在 (= per-letter integrability hyp は外から取れない、本 declaration は **bundle 外** で立てる必要) | → **M3 で signature 改変要否を再判定** (§撤退ライン T-MIF-2 参照) | `mutualInfo_le_of_markov` + `ne_top_of_le_ne_top` (要 X^n ne_top の上流伝播) |
| line 502 inline | `awgn_dpi` body 内 `h_finite : (jointMIXnYn) ≠ ∞` | `h_markov : MarkovChainForConverse` (既存)、bundle 不在 (per-letter hyp 不要) | → M3 で signature 改変要否を再判定 | (X^n ne_top を直接立てる必要、M2 shared helper を呼ぶ) |
| line 1175 | `awgnConverseJoint_mutualInfo_ne_top_via_chain` | `h_per_letter` / `h_chain` / `h_markov` / `h_mi_bridge_per_letter` (既存 4 引数完備) | → M2 shared helper 呼出 + Markov DPI 1 段 | `mutualInfo_le_of_markov` + `ne_top_of_le_ne_top` + `ENNReal.sum_ne_top` |

**重要 friction (signature 改変要否)** — line 395 / line 502 は **bundle hypothesis
を引数として受け取らない** (= private helper / inline have block で sorry 残置)。
本 mini-plan の M2 shared helper `awgnConverseJoint_jointMIXnYn_ne_top` が
`h_per_letter` 引数を要求する形になる場合、line 395 / line 502 では shared helper
を呼べない (= bundle hyp が無いから)。

→ §撤退ライン T-MIF-2 で対応:
- **case A (推奨)**: shared helper を **bundle 抜き** の signature (`h_per_letter`
  を引数として外出し) にして、line 395 / line 502 から **bundle 引数を新規追加**
  (= signature 改変)。3 sorry 同時 closure 達成。
- **case B (fallback)**: line 395 / line 502 は signature 維持で sorry のまま残し、
  `awgnConverseJoint_mutualInfo_ne_top_via_chain` (line 1175) のみ closure。
  1/3 closure。`@audit:retract-candidate` で line 395 / line 502 を撤回 marker
  (`isAwgnConverseFeasible_discharger` body 内で via_chain helper を直接使う形に
  refactor)。

M3 着手時に case A / case B を判定する。

## Phase 詳細

### M0 — Mathlib + InformationTheory verbatim 再確認 (~30 分、本 plan 起草時に主要確認済)

- [ ] `ENNReal.sum_ne_top` / `ENNReal.lt_top_of_sum_ne_top` (`BigOperators.lean:88-95`) 再確認 (起草時 verbatim 済)
- [ ] `ENNReal.toReal_mono` / `ne_top_of_le_ne_top` (Real.lean:67) 再確認 (起草時済)
- [ ] `mutualInfo_le_of_markov` ENNReal 形結論 (`CondMutualInfo.lean:385`) 型クラス前提再確認 (起草時済)
- [ ] **新規必要 — `klDiv_ne_top` verbatim** (`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`、本起草時には推定形): 完全 signature (`[IsFiniteMeasure μ]` / AC / integrable llr) verbatim 確認
- [ ] **新規必要 — `InformationTheory/Shannon/MutualInfo.lean` 内 `mutualInfo` definition + 既存 AC / integrable llr helpers** (line 165-207 周辺) を per-letter (Y_i : ℝ) で reuse 可能かを判定 — Fintype 想定なら reuse 不可、route (i) M1 規模が +20-40 行
- [ ] **境界 case 確認** (CLAUDE.md「具体的数値・型予測の verbatim 確認」):
  - `perLetterInputSecondMoment c i = 0` の case で `(1/2) log(1+0/N) = 0`、
    per-letter MI ne_top 経路でこの退化境界が `klDiv = 0 ≠ ∞` で trivially 通る
    こと再確認 (退化定義悪用にならない genuine route)
  - `M = 1` `[NeZero M]` 充足だが `2 ≤ M` 不在の case が現 declaration で問題に
    ならないこと再確認 (line 395 / line 502 は `2 ≤ M` 仮定なし、line 1175 も同様、
    全件 NeZero M のみ要求)

### M1 — `awgn_per_letter_mi_ne_top` (~20-80 行)

- [ ] private helper signature 配置 (M3 で shared 化する場合は `def` → `theorem`、
  本 mini-plan 着手段階では private):
  ```lean
  private lemma awgn_per_letter_mi_ne_top
      {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
      {M n : ℕ} [NeZero M] (c : AwgnCode M n P)
      (h_per_letter : PerLetterIntegrabilityForConverse P N h_meas c) :
      ∀ i : Fin n, (perLetterMI h_meas c i) ≠ ∞
  ```
  (起草段階の暫定。M0 で `klDiv_ne_top` の `[IsFiniteMeasure μ]` 仕様確認後に
  追加 hyp が必要なら signature 拡張、M3 で他 sorry から呼ぶ際 shared 化)
- [ ] route (i) M1 — `mutualInfo` def unfold + `klDiv_ne_top` 適用:
  ```lean
  intro i
  unfold perLetterMI mutualInfo  -- = klDiv (joint_i) (prod_i)
  apply klDiv_ne_top
  · -- AC: joint_i ≪ prod_i
    exact perLetterJoint_absolutelyContinuous_prod h_meas c i
  · -- integrable llr
    exact perLetterJoint_llr_integrable h_meas c i (h_per_letter i)
  ```
  + 2 private helper (`perLetterJoint_absolutelyContinuous_prod` / `perLetterJoint_llr_integrable`):
  - `perLetterJoint_absolutelyContinuous_prod` (~10-30 行): per-letter joint
    `(awgnConverseJoint).map (fun ω => (c.encoder ω.1 i, ω.2 i))` が prod marginals
    に AC、AWGN kernel の Gaussian density 経由 (InformationTheory 既存
    `gaussianReal_absolutelyContinuous` + mixture 集約)
  - `perLetterJoint_llr_integrable` (~10-30 行): bundle 内 `h_per_letter i` から
    `Integrable (llr ...) (joint_i)` への bridge (M0 で在庫確認後、Mathlib /
    InformationTheory 既存 helper で 1 行か手動展開 ~20 行)

### M2 — `awgnConverseJoint_jointMIXnYn_ne_top` (~5-30 行)

- [ ] shared helper signature 配置:
  ```lean
  private lemma awgnConverseJoint_jointMIXnYn_ne_top
      {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
      {M n : ℕ} [NeZero M] (c : AwgnCode M n P)
      (h_per_letter : PerLetterIntegrabilityForConverse P N h_meas c)
      (h_chain : ContinuousMIChainRuleForConverse P N h_meas c) :
      jointMIXnYn h_meas c ≠ ∞
  ```
- [ ] body skeleton:
  ```lean
  -- per-letter ne_top
  have h_pl_ne_top := awgn_per_letter_mi_ne_top h_meas c h_per_letter
  -- ⇒ Finset.sum_ne_top
  have h_sum_ne_top : ∑ i : Fin n, (perLetterMI h_meas c i) ≠ ∞ := by
    rw [ENNReal.sum_ne_top]
    intro i _
    exact h_pl_ne_top i
  -- Real 形 chain rule `(jointMIXnYn).toReal ≤ ∑ (perLetterMI).toReal` から
  -- ENNReal 形に lift する経路は 退化境界 trap で出ない (Approach §):
  -- → **case B 採用**: chain rule (`h_chain : Real 形`) は **使わない**、
  --    per-letter MI ne_top + ENNReal 形 chain rule wall は M0 で別 wall として
  --    立てる必要があるかを再判定
  sorry  -- M3 で signature 再判定 (case A / case B 分岐)
  ```

**重要分岐点 (M2 着手時、Approach 整合再確認)**:

- 起草時の Approach (case B) では `h_chain` (Real 形) を使わず ne_top の伝播のみ
  別経路で出すと書いたが、**実際には `(jointMIXnYn) ≤ ∑ᵢ (perLetterMI)` の
  ENNReal 形 bound が無いと `jointMIXnYn` 単体の ne_top が出ない** — per-letter
  ne_top + sum_ne_top ⇒ `∑ᵢ (perLetterMI) ≠ ∞` までは出るが、そこから
  `jointMIXnYn ≤ ∑ᵢ` (ENNReal 形) を 別途必要 = T-FFC-3 wall の **ENNReal 化** が
  必要。
- → M2 着手時に 2 つの sub-case を判定:
  - **case M2-α (chain rule 自体に ENNReal 形を追加 hyp として要求)**:
    M2 shared helper signature に `(h_chain_enn : jointMIXnYn h_meas c ≤ ∑ ᵢ, perLetterMI h_meas c i)` を追加 = bundle 外 1 hyp 追加。これは
    `wall:multivariate-mi` の **本質的 ENNReal packaging**、本 mini-plan の
    sub-wall (T-MIF-1) として残置する形。M3 sorry closure は 3 件中 1 件 (line 1175 のみ)
    達成、残 2 件は signature 改変必要 (case A) で別 mini-plan に委ねる。
  - **case M2-β (chain rule の bundle predicate を ENNReal 化、scope creep)**:
    親 plan §A bundle predicate `ContinuousMIChainRuleForConverse` を Real 形 →
    ENNReal 形に置換、Phase B-chain 再 publish、本 mini-plan scope を超える。
    撤退ライン T-MIF-3 で記録。

→ **M2 着手前に Approach を 1 度再 verify** (Real 形 chain rule の ENNReal-lift
が trivial に出るかどうか、`toReal_le_toReal` 経由で 退化境界除外できるか、
具体的に `(jointMIXnYn).toReal ≤ ∑ (perLetterMI).toReal` ∧ `∑ (perLetterMI) ≠ ∞`
⇒ `(jointMIXnYn) ≠ ∞` が出るかを 1 turn 確認)。出るなら case M2-α 不要、
出ないなら案 (α) の追加 hyp で fallback。

**観察**: `toReal_le_toReal (ha hb) : a.toReal ≤ b.toReal ↔ a ≤ b` (`Real.lean:61`、
verbatim 確認済) は **両側 ne_top 前提**。`(jointMIXnYn).toReal ≤ ∑ .toReal` から
`jointMIXnYn ≤ ∑` を導くには `jointMIXnYn ≠ ∞` が **既に必要** = 循環。
**Real 形 chain rule からの ENNReal-lift は構造的に不可能**、case M2-α (ENNReal
形を追加 hyp で外注) が必須。

### M3 — 3 sorry 同時 closure (~15-50 行)

case A (signature 改変、3 sorry 全件 closure) or case B (1 sorry のみ closure + 2 件
撤回 marker) を M2 結果 + M3 着手時に判定。

- [ ] **case A 採用時の M3-a (signature 改変による 3 sorry closure)**:
  - line 395 `awgnConverseJoint_mutualInfo_ne_top` の signature に `(h_per_letter :
    PerLetterIntegrabilityForConverse P N h_meas c)` + `(h_chain_enn : jointMIXnYn
    ≤ ∑ ᵢ, perLetterMI)` + `(h_markov : MarkovChainForConverse)` を追加引数
  - line 502 inline は `awgn_dpi` body の `h_finite` を `awgnConverseJoint_jointMIXnYn_ne_top
    h_meas c h_per_letter h_chain_enn` 呼出に置換 (要 `awgn_dpi` signature 拡張、
    bundle hyp 注入)
  - line 1175 `awgnConverseJoint_mutualInfo_ne_top_via_chain` は M2 shared helper +
    Markov DPI 1 段で genuine assembly
  - **問題**: signature 改変は `awgn_converse_single_shot_call` (line 405) + 
    `isAwgnConverseFeasible_discharger` (line 1190) など callers にも波及、影響
    範囲確認必須 ⇒ T-MIF-2 と並行で M3 着手前に caller 影響範囲を Read 確認
- [ ] **case B 採用時の M3-b (1 件 closure + 2 件撤回 marker)**:
  - line 1175 `awgnConverseJoint_mutualInfo_ne_top_via_chain` のみ closure
    (引数 `h_per_letter` / `h_chain` 既存、追加 1 hyp `h_chain_enn` で OK)
  - line 395 + line 502 は signature 維持で sorry 残し、`@residual` tag を
    `@audit:retract-candidate(awgn-converse-c5-mi-finite-bridge)` に昇格、
    `isAwgnConverseFeasible_discharger` (line 1190) body を line 1175 の via_chain
    helper を直接使う形に refactor (= line 395 / line 502 を dead code 化、
    別 commit で削除)

### M4 — verify + tag 解消 (~5 分)

- [ ] `lake env lean InformationTheory/Shannon/AWGNConverseDischarge.lean` silent
- [ ] case A 採用時: sorry 残数が 5 → 5 - 3 = 2 件 (`awgn_per_letter_mi_le_log_var`
      撤回後の他 sorry 件数は M1 完了時に 0 → 残 sorry は M2/M3 mini-plan の出口
      数件、`rg -n "sorry" InformationTheory/Shannon/AWGNConverseDischarge.lean | wc -l` で
      確認)
- [ ] case B 採用時: sorry 残数 5 → 4 件 (line 1175 のみ消える、line 395 / 502 は
      retract-candidate tag 維持)
- [ ] `wall:multivariate-mi` reclassify 判断:
  - case A: 完全 closure、`wall:multivariate-mi` は **wall list から削除**
    (親 plan judgement #6 + #7 で記録)
  - case B: partial closure、`wall:multivariate-mi` は **存続** + 縮退タグ
    `@residual(wall:multivariate-mi-residual)` 等にリネームの是非を判断ログで record
- [ ] 親 plan `awgn-converse-aux-plan.md` 判断ログ #6「後続セッション送り (3)」を
      完了マーク + 本 mini-plan へ pointer (orchestrator 側責務)

## 撤退ライン

### T-MIF-1: M1 route (i) `klDiv_ne_top` の前提 (`integrable_llr_*`) 構築が肥大 (M1)

`bundle h_per_letter i : Integrable (negMulLog ∘ rnDeriv) volume` から
`Integrable (llr (joint_i) (prod_i)) (joint_i)` への bridge が想定 ~10-30 行から
50+ 行に肥大 (joint vs marginal の measure 切り替え、Gaussian density vs llr の
形式の違い)。

- 縮退案 (a): bridge を独立 helper `perLetterJoint_llr_integrable_via_negMulLog`
  に切り出し (~30-50 行)、本体は 1 行呼出。判断ログ #1 で記録。
- 縮退案 (b): route (i) を **撤退** し M1 を新規 staged hyp として bundle 拡張
  (per-letter `klDiv_ne_top` の 2 前提を bundle 内 staged field 化) →
  `IsAwgnConverseFeasible` の 4 番目 sub-bound 追加 = Phase A 再 publish 相当 =
  scope creep、推奨されない。発動時は親 plan §A pivot として別 mini-plan に委ねる。

### T-MIF-2: signature 改変要否 (M3 着手前判定、case A vs case B)

line 395 / line 502 が bundle hypothesis を引数として受け取らない構造で、shared
helper を呼ぶ際 signature 拡張が必須 (case A) か、または 1/3 sorry のみ closure に
留めて 2/3 を撤回 marker (case B) かを判定する分岐点。

- 縮退案: case B 採用 (1/3 closure)、line 395 / line 502 は dead code 化 + `isAwgnConverseFeasible_discharger` body refactor で via_chain helper を直接使う。本 mini-plan は partial closure として終了、`wall:multivariate-mi-residual` を残す。

### T-MIF-3: ENNReal 形 chain rule の bundle predicate 化 (M2 case M2-β、scope creep)

M2 着手時に `(jointMIXnYn) ≤ ∑ᵢ (perLetterMI)` の ENNReal 形 bound を bundle
predicate `ContinuousMIChainRuleForConverse` に追加 / 置換することが避けられない
case。

- 縮退案 (a): 本 mini-plan で bundle predicate を **拡張せず**、shared helper
  (M2) の追加 hyp として ENNReal 形を外注 (= case M2-α、上記 M2 §)。bundle
  signature 維持、本 mini-plan で closure 可能。
- 縮退案 (b): bundle predicate signature 改変 (Real 形 → ENNReal 形) を本 mini-plan
  scope 外として別 mini-plan `awgn-converse-chain-rule-ennreal-pivot.md` (新規
  未起草) に委ねる。本 mini-plan は partial closure で終了。

### T-MIF-fallback (mini 全体)

M1-M3 のいずれかで規模が中央予測 ~85 行を **大幅超過** (≥ 200 行) または analytic
body が本質的に Mathlib 壁を 2 件以上 hit。

- **本 mini-plan 全体を撤退**: 3 sorry の body を `sorry +
  @residual(wall:multivariate-mi)` 維持 (現状から変化なし)、`wall:multivariate-mi`
  を **共有 sorry 補題化** (audit-tags.md「共有 Mathlib 壁」) で 1 declaration に
  集約。本 mini-plan は closure 失敗、後続 mini-plan に委ねる。

### honesty 撤退ライン (常時、CLAUDE.md「検証の誠実性」)

- ❌ shared helper `awgn_per_letter_mi_ne_top` の中に load-bearing hypothesis を
  bundle (例: `(h_ne_top : ∀ i, perLetterMI ≠ ∞)` を引数として外出し → 循環
  tier 5 defect)。本 helper は **analytic primitives** で Mathlib 内 closure 可能、
  staged 化禁止。
- ❌ M3 で 3 sorry を `sorry := h` 循環 (仮説型 ≡ 結論型) で消す。各 sorry は
  signature 改変 (case A) or 撤回 marker (case B) で対応、循環で潰さない。
- ❌ `:True` slot / 退化定義悪用 / name laundering (CLAUDE.md tells 全件回避)。
  特に Real 形 `(jointMIXnYn).toReal ≤ ∑ .toReal` から `(jointMIXnYn) ≠ ∞` を
  「退化境界 `∞.toReal = 0` で trivially `0 ≤ ∑ < ∞`」と読み替えて ENNReal-lift
  を skip する形は退化定義悪用 (Approach §の M2 重要分岐点で明示済)。

## 検証手順

実装完了時の確認手順:

```bash
# 1. file verify
lake env lean InformationTheory/Shannon/AWGNConverseDischarge.lean
# expect: silent

# 2. case A (3 sorry closure) 採用時
rg -n "sorry" InformationTheory/Shannon/AWGNConverseDischarge.lean | wc -l
# expect: 元 5 件 → M1 (`awgn-converse-c1b-gaussian-maxent` で 1 件解消) 後
# 4 件 → さらに M2 (`awgn-converse-c1c-jensen` で 1 件解消) 後 3 件 →
# 本 mini-plan で 3 件解消 → 0 件 (= `AWGNConverseDischarge.lean` 完全 0 sorry 達成)

# 3. case B (1 sorry closure) 採用時
rg -n "sorry" InformationTheory/Shannon/AWGNConverseDischarge.lean | wc -l
# expect: 本 mini-plan で 1 件解消 → 2 件残置 (line 395 / line 502、retract-candidate
# tag 付き)

# 4. residual tag 残数確認
rg -n "@residual\(plan:awgn-converse-aux-plan\)" InformationTheory/Shannon/AWGNConverseDischarge.lean | wc -l
# expect (case A): 0 件 (`wall:multivariate-mi` 完全 closure)
# expect (case B): 2 件 (line 395 / line 502 のみ残置、retract-candidate tag に昇格)

# 5. line 395 / line 502 / line 1175 周辺の sorry が消えたことを確認
rg -n "sorry" InformationTheory/Shannon/AWGNConverseDischarge.lean
# expect (case A): 3 line すべて出力されない
# expect (case B): line 1175 のみ出力されない、line 395 / line 502 は残存

# 6. honesty audit (orchestrator が実装後 dispatch)
# subagent_type: "honesty-auditor"
# 対象: case A 時は 3 declaration の signature 改変 + 2 shared helpers 新規追加、
# case B 時は via_chain helper 1 件の signature 改変 + retract-candidate tag 付与
```

## 完了判定 (本 mini-plan)

### Case A 完了判定 (3 sorry 全件 closure、推奨)

- [ ] `AWGNConverseDischarge.lean` の sorry 残数 0 件
- [ ] 3 declaration の body 0 sorry / 0 @residual
- [ ] `wall:multivariate-mi` を wall list から削除、親 plan judgement #6 + #7 で記録
- [ ] 親 plan 進捗 ✅ 反映 (orchestrator 側)
- [ ] proof-log: **no** (本 mini は親 plan §C-5 の 1 sub-item、規模超過時のみ判断ログ append)
- [ ] **独立 honesty audit subagent 必須** (新規 helper 2 件 + 3 declaration signature
      改変 + bundle hypothesis 引数注入のため、orchestrator 側責務)

### Case B 完了判定 (1/3 sorry closure、partial)

- [ ] line 1175 `awgnConverseJoint_mutualInfo_ne_top_via_chain` body 0 sorry / 0 @residual
- [ ] line 395 / line 502 の `@residual(plan:awgn-converse-aux-plan)` を
      `@audit:retract-candidate(awgn-converse-c5-mi-finite-bridge)` に昇格
- [ ] `isAwgnConverseFeasible_discharger` body refactor (via_chain helper 直接使用、
      line 395 / line 502 を dead code 化)
- [ ] `wall:multivariate-mi` を `wall:multivariate-mi-residual` に縮退タグ化、
      残存範囲を親 plan judgement #7 で記録
- [ ] proof-log: **yes** (`proof-log-awgn-converse-c5-mi-finite-bridge.md`、
      case B 採用理由 + 削除 declaration の影響範囲 + 後続 mini-plan の必要性を記録)
- [ ] **独立 honesty audit subagent 必須** (signature 改変なしで sorry 解消は 1 件、
      残 2 件の retract-candidate tag 付与の妥当性 + dead code 化の影響範囲 verify)

## 親 plan / 兄弟 mini との scope 区別

| Plan / mini | スコープ | 出力 | 状態 |
|---|---|---|---|
| `awgn-converse-aux-plan.md` (親) | F-3 converse aux discharge (Phase A-V) | `AWGNConverseDischarge.lean` (1250 行、Phase A-V 完走、commit 84e013c 時点で 3 sorry 残置) | Phase V 完走、後続 mini-plan 群で残置 sorry を回収 |
| `awgn-converse-c1b-gaussian-maxent-mini-plan.md` (#M1、完了済) | C-1b per-letter Gaussian max-entropy 4 hyp 充足 (~80-150 行) | `awgn_per_letter_mi_le_log_var` (line 901、commit 84e013c で 0 sorry 化) | **完了** (M1 ENNReal-lift の入力として参照) |
| `awgn-converse-c1c-jensen-mini-plan.md` (#M2) | C-1c Jensen affine substitution `sorry` 解消 | `sum_log_one_add_le_n_log_one_add_avg` (line 624) | 起草済、未実装 |
| **本 mini-plan** (#M3、`awgn-converse-c5-mi-finite-bridge`) | C-5 transitive MI 有限性 (3 sorry 同時 closure) | line 395 / line 502 / line 1175 の `sorry` 解消 (case A) or partial closure (case B) | **起草** |
| `awgn-main-converse-wiring-plan.md` (TBD) | `AWGNConverse.lean:70` body 置換 + `AWGNMain.lean` migration | 未起草 |

**重要**:

- 本 mini-plan は **#M1 (C-1b) 完了後にのみ着手可能** — M1 で publish された
  `awgn_per_letter_mi_le_log_var` body の `differentialEntropy_le_gaussian_*` +
  bundle `h_per_letter i` 経路を本 mini-plan M1 (ENNReal-lift) の入力として使う。
  M2 (C-1c Jensen) との dependency なし、並列可。
- 本 mini-plan 完了 (case A) で `AWGNConverseDischarge.lean` の `@residual(wall:multivariate-mi)` 系 sorry が完全消滅 → `awgn_converse` (`AWGNConverse.lean:70`) の body sorry を埋める後続 mini-plan (`awgn-main-converse-wiring-plan.md`) の前提条件が揃う。
- case B 採用時は `wall:multivariate-mi-residual` (縮退) を残し、後続 mini-plan
  `awgn-converse-chain-rule-ennreal-pivot.md` (新規未起草) で完全 closure を目指す。

## オーケストレータ注記

- 実装 agent は `InformationTheory.lean` を編集しない (本 file は既に編入済)
- 並列 dispatch 中の場合: `lean-implementer` を `isolation: "worktree"` で起動
  (CLAUDE.md「Parallel orchestration」boilerplate 必須)。本 mini-plan は M2
  (`awgn-converse-c1c-jensen`) と同一 file 内別 declaration 編集なので、**並列
  dispatch 時は worktree 隔離必須**、逐次 dispatch なら隔離不要
- M3 case A/B 判定は orchestrator 判断必要、実装 agent 単独で signature 改変させない
- 完了後の commit は autonomous (CLAUDE.md「Commits」)
- 完了時 orchestrator: (a) 親 plan §C-5 進捗反映、(b) `@residual` tag 残数確認、
  (c) 独立 honesty audit subagent 起動 (case A: 3 declaration signature 改変 +
  2 shared helpers のため必須、case B: retract-candidate tag 付与 + dead code 化
  の妥当性 verify)

## 判断ログ

書く頻度: M0-M4 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### #0 (2026-05-27) plan 起草 — 3 sorry 同時 closure (case B 優先) として本 mini-plan 確定

親 plan 判断ログ #6「後続セッション送り (3) C-5 transitive MI 有限性 bridge —
C-1b 完成後に ENNReal 形 per-letter bound 経由で可能」を受けて本 mini-plan 起草。

入力前提:
- `awgn-converse-c1b-gaussian-maxent` (M1、commit 84e013c) で
  `awgn_per_letter_mi_le_log_var` (line 901) が 0 sorry / 0 @residual 化、本 plan
  起草時に Read で verbatim 確認済 (line 887-998 確認)
- 3 sorry の現在 line 番号は line 395 / line 502 / line 1175 (起草時 Read 確認、
  M1 publish 後で起草時 brief の 389 / 468 / 1159 から +6 / +34 / +16 shift)

採用 Approach (case B 優先): per-letter MI ENNReal-lift → Finset.sum_ne_top →
ENNReal 形 chain rule (M2 で追加 hyp 外注、case M2-α) → Markov DPI (`mutualInfo_le_of_markov`
ENNReal 形、`CondMutualInfo.lean:385` 結論型 verbatim 確認済) で 3 sorry 同時 closure。

注意:
- Approach §で発見した **Real 形 chain rule からの ENNReal-lift 構造的不可能性**
  (`toReal_le_toReal` 両側 ne_top 前提 → 循環) により M2 で必ず追加 hyp `h_chain_enn`
  が必要 (case M2-α 必須)。これは親 plan §C-5 起草時の見積もり「~20-40 行 (共通
  helper 1 件)」を超える可能性あり (中央 ~85 行)、規模超過時は撤退ライン T-MIF-1
  / T-MIF-3 で対応
- M3 case A (signature 改変) vs case B (1/3 closure + retract marker) の判定は
  M2 完了時の caller 影響範囲確認後に行う、起草時には case B 優先と判断

scope: 1 shared helper (M1) + 1 shared helper (M2) + 3 sorry closure (M3)、~85 行
中央、0.5-1 session。signature 改変要否は M3 で再判定、bundle predicate signature
改変は禁止 (= T-MIF-3 fallback で別 mini-plan に委ねる)。

### #1 (TBD、M1 完了時) `klDiv_ne_top` 経路の前提充足コスト

route (i) M1 (`mutualInfo` def unfold + `klDiv_ne_top` 適用) の AC 経路 +
integrable llr 経路の構築コストが ~10-30 行 (中央) で済んだか、T-MIF-1 縮退案 (a)
(bridge を独立 helper 化) に降格したかを記録。

### #2 (TBD、M2 完了時) ENNReal 形 chain rule 追加 hyp の必要性

M2 着手時の重要分岐点 (Real 形 chain rule からの ENNReal-lift 可否) を再 verify し、
案 (α) (追加 hyp 外注) で進めたか、案 (β) (bundle predicate 改変、scope creep) を
判断して T-MIF-3 で別 mini-plan に委ねたかを記録。

### #3 (TBD、M3 完了時) case A / case B の最終判定と影響範囲

M3 着手時に caller (`awgn_converse_single_shot_call` / `awgn_dpi` /
`isAwgnConverseFeasible_discharger`) の影響範囲を Read で確認、case A (3 sorry
全件 closure + signature 改変) を採用したか、case B (1/3 closure + retract-candidate
+ dead code 化 refactor) に降格したかを記録。残置 sorry 数 + `wall:multivariate-mi`
reclassify 結果も併せて記録。

### #4 (TBD、M4 完了時) honesty audit verdict + wall reclassify 結果

実績: `AWGNConverseDischarge.lean` sorry 残数 + `wall:multivariate-mi` 完全
closure (case A) / 縮退 (case B) / 存続 (T-MIF-fallback) + honesty audit subagent
verdict (PASS expected、tier 5 defect なし、特に case B 採用時の retract-candidate
tag 付与の妥当性 + dead code 化の影響範囲 verify)。
