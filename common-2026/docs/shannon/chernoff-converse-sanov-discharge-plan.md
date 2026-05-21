# Chernoff converse 完全 discharge (Sanov 経由) サブ計画 🌙 (T1-B)

> **Parent**: [`chernoff-converse-moonshot-plan.md`](chernoff-converse-moonshot-plan.md)
> §「完全 discharge (Sanov LDP per-tilt 起動)」 + §撤退ライン L-CC2
>
> **Predecessor が defer したものを閉じる plan**。predecessor は per-tilt 形 hypothesis
> 縮減 (L-CC2) で着地し、`IsBayesErrorPerTiltLowerBound` / `IsChernoffNLetterRN` を
> Mathlib-gap predicate として残した。本 plan はその predicate を **genuine に証明**して
> 全 converse headline を **無条件 (標準B)** にする。

## 進捗

- [ ] M0 — Sanov 支配補題の conclusion form 確定 + redefine 2 択の最終判断 📋
- [ ] Phase 1 — skeleton (新規 file `ChernoffSanovDischarge.lean`、sorries 3 個) 📋
- [ ] Phase 2 — step 1: tilted typical set 上の逆 Hölder per-point 下界 📋 (新規 core)
- [ ] Phase 3 — step 3: tilted typical set の確率→1 (Sanov LLN 起動) 📋 (新規 core)
- [ ] Phase 4 — step 1+2+3 合成: `C·Z(λ)^n ≤ 2·bayesErrorMinPmf` を genuine に構成 📋
- [ ] Phase 5 — name laundering 解消: `chernoff_per_tilt_via_RN` の `:= h_RN` を genuine 証明で置換 📋
- [ ] Phase 6 — verify + Common2026 編入 + roadmap 判断ログ 📋

proof-log: yes (Phase 2-4 が本物の Mathlib 作業。step ごとに何が通った/詰まったを残す)

---

## Context / 現況

### いま load-bearing になっている述語

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

### honesty defect (発見済、本 plan で解消する)

`ChernoffPerTiltSanov.lean:139` の `IsChernoffNLetterRN` は `IsBayesErrorPerTiltLowerBound`
(`:136`) と **body 字面が完全一致** (どちらも `∃ C, 0<C ∧ ∀ᶠ n, C·Z^n ≤ 2·bayesErrorMinPmf`)。
その上で:

```lean
-- ChernoffPerTiltSanov.lean:162
lemma chernoff_per_tilt_via_RN (P₁ P₂ : α → ℝ) (lam : ℝ)
    (h_RN : IsChernoffNLetterRN P₁ P₂ lam) :
    IsBayesErrorPerTiltLowerBound P₁ P₂ lam := h_RN          -- ← 循環 (型≡結論、:= h)
```

これは CLAUDE.md「検証の誠実性」の **name laundering / 循環** tell に該当する
(`IsChernoffNLetterRN` という別名を付けただけで何も証明していない)。docstring は
「pass-through, future structural refinement で non-trivial になる」と honest に書いてはいるが、
標準B では **残タスク**。本 plan の Phase 5 でこれを解消する (下記)。

### なぜ未完か (strategy 再評価の結論)

- **CLT-port は不可**: Cramér closure 側の CLT route は `P{m·n ≤ ∑Y}` の半直線 tail を扱うが、
  `bayesErrorMinPmf = (1/2)∑_x min(∏P₁,∏P₂)` は **min-of-products の和**で、半直線 tail に
  preimage 同一視できない。CLT は対象不一致。
- **正しいルートは Sanov / method-of-types**。本プロジェクトは Sanov LDP の `Measure.pi`
  下界機構を完備で持つ (`SanovLDPEquality.lean`, `typeClassByCount_Qn_ge`)。CLT 不要。

---

## Approach (全体戦略 = Sanov 経由 step 1-4)

下界 `C·Z(λ*)^n ≤ 2·bayesErrorMinPmf` を、tilted mediator measure
`chernoffMediatorMeasure P₁ P₂ λ*` (= Q) を ambient に据えた **change-of-measure on a
typical set** で構成する。Stein の `steinTypicalSet_Q_prob_le` (`Stein.lean:341`) +
`steinTypicalSet_P_prob_tendsto_one` (`Stein.lean:275`) が **構造的に同型の既存テンプレート**
であり、これを tilted-mediator typicality に移植する。

```
bayesErrorMinPmf P₁ P₂ n
  = (1/2) ∑_x min(∏P₁(x_i), ∏P₂(x_i))                          -- 定義 (Chernoff.lean:691)
  ≥ (1/2) ∑_{x ∈ T_n} min(...)                                  -- 非負項を typical set T_n に制限
  ≥ (1/2) ∑_{x ∈ T_n} (∏P₁(x_i))^{1-λ}·(∏P₂(x_i))^λ · κ        -- step 1 逆 Hölder on T_n
  = (1/2) κ · Z(λ)^n · Q^n(T_n)                                 -- step 2 正規化 (∏ = Z^n·Q^n項)
  ≥ (1/2) κ · Z(λ)^n · (1/2)                                    -- step 3 Q^n(T_n) → 1, eventually ≥ 1/2
  = (κ/4) · Z(λ)^n                                              -- C := κ/2 で per-tilt lower bound 成立
```

ここで `T_n := chernoffTiltedTypicalSet P₁ P₂ λ n ε` は **tilted mediator Q = chernoffMediator
の typical set** (empirical "tilted log-likelihood" が期待値近傍にあるブロック)。κ は typical
set 上で「幾何平均と min の比」が下から押さえられる定数 (step 1)。

4 step の役割:

1. **step 1 (新規 core)**: tilted typical set 上の **逆 Hölder per-point 下界**。
   既存 `min_le_rpow_mul_rpow` (`Chernoff.lean:699`) は上界 `min ≤ a^{1-λ}b^λ`。本 plan で
   要るのはその **逆向き on typical set**: typical set 上では `∏P₁` と `∏P₂` の比が指数的に
   制御され、`min ≥ κ · a^{1-λ}b^λ`。これが本 plan の唯一の真に新規な不等式。
2. **step 2 (既存再利用、無変更)**: n-letter Z 正規化。
   `sum_prod_rpow_eq_Z_pow` (`Chernoff.lean:751`) + `chernoffZSum_pow_eq_sum_prod`
   (`ChernoffNLetterZSum.lean:36`) + `chernoffMediatorMeasure_pi_singleton`
   (`ChernoffPerTiltSanov.lean:197`)。`(∏P₁)^{1-λ}(∏P₂)^λ = Z(λ)^n · Q^n({x})` を per-block で。
3. **step 3 (Sanov LLN 起動、新規 wiring)**: tilted typical set の確率 → 1。
   Q := `chernoffMediatorMeasure` (prob measure 証明済 `:435`) を ambient に、Stein の
   `steinTypicalSet_P_prob_tendsto_one` (`Stein.lean:275`) と同型の strong-law / LLN で
   `Q^n(T_n) → 1`。`chernoffMediatorMeasure_pi_singleton` (`:197`) で n-letter singleton 評価済。
4. **step 4 (既存再利用、無変更)**: rate → limsup。
   step 1-3 が `IsBayesErrorPerTiltLowerBound` を genuine に与えると、
   `chernoff_converse_from_per_tilt` (`ChernoffConverse.lean:270`) +
   `chernoffInfo_attained` (`Chernoff.lean:163`) が headline を自動で出す (predecessor 完成済)。

**残りは step 1 と step 3 の 2 つ**。step 2/4 は既存で 0 行。規模 ~150-300 行。

---

## 設計判断 (Mathlib-shape-driven): `bayesErrorMinPmf` redefine するか

### 結論: **redefine しない。現 min-和 形のまま step 1-4 で通す。** (推奨)

#### 根拠 (支配補題の conclusion form を verbatim 読んだ上で)

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
`bayesErrorMinPmf` (現 min-和形) を step 1-3 で使う際に **必要なのは `∑_{x ∈ T_n}` の
finite-sum 評価**であって、Sanov 補題の出力 `Q^n(T_n).toReal` とは
`chernoffMediatorMeasure_pi_singleton` (`ChernoffPerTiltSanov.lean:197`, verbatim:
`(Measure.pi (fun _ : Fin n => chernoffMediatorMeasure P₁ P₂ lam)) {x} = ∏ i, ENNReal.ofReal
(chernoffMediator ... (x i))`) で **既に bridge 済**。つまり min-和 ↔ Measure.pi の橋は
predecessor が `chernoffMediatorMeasure_pi_singleton` の形で **もう架けている**。

→ redefine の動機 (「min-和 ↔ Measure.pi の bridge を探しているのが詰まりの根因」) は、
predecessor の Phase J/C plumbing (`ChernoffPerTiltDischarge.lean:407-468`,
`ChernoffPerTiltSanov.lean:197-246`) が **既に架けたことで消えている**。redefine の純利益はない。

#### redefine した場合のリスク (採らない理由の補強)

`bayesErrorMinPmf` を `(1/2)·(Measure.pi P₁ {LLR≥0} + Measure.pi P₂ {LLR<0})` 形へ redefine
すると、**achievability 側が壊れる**。achievability の core は:

- `bayesErrorMinPmf_le_half_Z_pow` (`Chernoff.lean:779`) — `unfold bayesErrorMinPmf` で
  min-和を開いて per-point `min_le_rpow_mul_rpow` を起動 (`:783-802`)。
- `chernoff_lemma_achievability` (`Chernoff.lean:1059`) → `chernoff_achievability` (`:1004`)
  → `chernoff_rate_ge_chernoffInfo_eventually` (`:883`)。

これらは全て min-和の `unfold` に依存。redefine すると **achievability 全チェーン (~200 行) の
書き直し**が発生し、さらに「min-和 = pushforward 形」の equivalence lemma を新規に書く羽目になる
(これこそ CLAUDE.md が警告する「self-written bridge lemma」)。redefine の損益は明確にマイナス。

#### Stein redefine 参考の評価

Stein は `llrPmf` / `steinTypicalSet` を `Measure.pi` 上 LLR-based で持つ
(`Stein.lean:257`, `:341`, `:275`)。これは「Stein の本体 statement が `Measure.pi` 測度
そのもの (`Q^n(T) ≤ exp(...)`)」だから自然。だが Chernoff の本体 statement は
`bayesErrorMinPmf` = min-和という **異なる量** (Bayes error)。Stein の form を真似て redefine
すると Chernoff の textbook 量から離れてしまう。Stein のテンプレートは **証明技法 (typical set
+ change-of-measure)** として借りるべきで、**定義の字面**は借りない。

#### 補足: redefine が必要になる唯一のケース

step 1 (逆 Hölder on typical set) を組む際、もし「min-和の各項を `Q^n({x})` 形に持ち上げる
per-block 補題」が `chernoffMediatorMeasure_pi_singleton_toReal`
(`ChernoffPerTiltSanov.lean:219`, verbatim: `((Measure.pi ...) {x}).toReal = ∏ i,
chernoffMediator ... (x i)`) **だけでは足りず**、`∑_{x ∈ T_n}` の Finset → Measure.pi の集合
測度への昇格に新規 ~50 行超を要すると判明したら、その時点で redefine を再評価する
(撤退ライン L-SD2 参照)。M0 でこの一点を先に確認する。

---

## Phase 詳細

### M0 — Sanov 支配補題の conclusion form 確定 + redefine 最終判断

- [ ] `typeClassByCount_Qn_ge` (`:918`) と `sanov_ldp_lower_bound_pointwise` (`:1071`) の
      conclusion form / type-class 前提を inventory subagent 形式で確定
      (`[IsProbabilityMeasure Q]`, `hQpos : ∀ a, 0 < Q.real {a}` は verbatim 必須)。
- [ ] step 3 で使う「typical set 確率 → 1」を **どの補題で出すか**確定:
      候補 (a) Stein `steinTypicalSet_P_prob_tendsto_one` (`Stein.lean:275`) の移植 (strong law)、
      候補 (b) `sanov_ldp_lower_bound_pointwise` の liminf 形を `Q = mediator`, `E = {全 type}`
      で起動して `Q^n(complement) → 0`。**(a) を第一候補**とする (Stein が完備テンプレート)。
- [ ] `∑_{x ∈ T_n} (min-和項)` を `Q^n(T_n).toReal` に持ち上げる per-block bridge が
      `chernoffMediatorMeasure_pi_singleton_toReal` (`:219`) +
      `MeasureTheory.sum_measureReal_singleton` (Stein.lean:340-360 が使っている同型) で
      ~50 行以内に閉じるか確認 → redefine 不要の最終確証。超えるなら L-SD2 へ。

依存補題 (verbatim 場所):
- `typeClassByCount_Qn_ge` — `Common2026/Shannon/SanovLDPEquality.lean:918`
- `sanov_ldp_lower_bound_pointwise` — `Common2026/Shannon/SanovLDPEquality.lean:1071`
- `steinTypicalSet_P_prob_tendsto_one` — `Common2026/Shannon/Stein.lean:275`
- `steinTypicalSet_Q_prob_le` — `Common2026/Shannon/Stein.lean:341` (技法テンプレート)
- `chernoffMediatorMeasure_isProbabilityMeasure` — `Common2026/Shannon/ChernoffPerTiltDischarge.lean:435`
- `chernoffMediatorMeasure_real_singleton` — `ChernoffPerTiltDischarge.lean:458`

規模: 在庫確認のみ (0 行)。

### Phase 1 — skeleton

- [ ] 新規 file `Common2026/Shannon/ChernoffSanovDischarge.lean` を作る
      (pinpoint import: `ChernoffPerTiltSanov`, `Chernoff`, `Stein`, `SanovLDPEquality`,
      `ChernoffNLetterZSum`, 必要な `Mathlib.MeasureTheory.Constructions.Pi`)。
- [ ] Phase 2-4 の補題を `:= by sorry` で全 state、namespace + docstring を置く。
- [ ] LSP `<new-diagnostics>` で skeleton type-check (sorry warning のみ期待)。

新規補題の target signature (skeleton):

```lean
-- step 1: tilted typical set 上の逆 Hölder per-point 下界
lemma min_ge_kappa_rpow_mul_rpow_on_typical
    (P₁ P₂ : α → ℝ) (lam : ℝ) {n : ℕ} {ε : ℝ} (x : Fin n → α)
    (hx : x ∈ chernoffTiltedTypicalSet P₁ P₂ lam n ε) ... :
    κ(ε) * ((∏ i, P₁ (x i)) ^ (1 - lam) * (∏ i, P₂ (x i)) ^ lam)
      ≤ min (∏ i, P₁ (x i)) (∏ i, P₂ (x i))

-- step 3: tilted typical set の確率 → 1 (eventually ≥ 1/2)
lemma chernoffTiltedTypicalSet_Q_prob_eventually_ge_half
    (P₁ P₂ : α → ℝ) (hP₁_pos ...) (lam : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1/2 : ℝ) ≤ ((Measure.pi (fun _ : Fin n => chernoffMediatorMeasure P₁ P₂ lam))
        (chernoffTiltedTypicalSet P₁ P₂ lam n ε)).toReal

-- step 4 合成: genuine per-tilt lower bound
theorem isBayesErrorPerTiltLowerBound_genuine
    (P₁ P₂ : α → ℝ) [Nonempty α] (hP₁_pos ...) (hP₂_pos ...)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1) (lam : ℝ)
    (hlam_mem : lam ∈ Set.Icc (0:ℝ) 1) :
    IsBayesErrorPerTiltLowerBound P₁ P₂ lam
```

`chernoffTiltedTypicalSet` は新規 def (Stein の `steinTypicalSet` 字面を移植):
empirical な「mediator 下での log-比率」が期待値近傍にあるブロック集合。

規模: ~40 行 (skeleton + def + imports + docstring)。

### Phase 2 — step 1: tilted typical set 上の逆 Hölder per-point 下界

- [ ] `chernoffTiltedTypicalSet` 上で `∏P₁(x_i)` と `∏P₂(x_i)` の **log-比率が `nε` 以内**
      であることを `mem_chernoffTiltedTypicalSet_iff` から取り出す。
- [ ] その上で per-point `min(a,b) ≥ κ·a^{1-λ}b^λ`: typical set 上では
      `a/b ∈ [exp(-Cε), exp(Cε)]` 的に制御され、min と幾何平均の比 κ が一様下界を持つ。
      `min_le_rpow_mul_rpow` (`Chernoff.lean:699`) の逆向き。
- [ ] κ(ε) を explicit に定める (例 κ = exp(-ε) 系)。`Real.rpow` の基本補題で。

依存補題:
- `min_le_rpow_mul_rpow` — `Common2026/Shannon/Chernoff.lean:699` (上界版、構造の参照)
- `Real.rpow_le_rpow`, `Real.rpow_add_of_nonneg`, `Real.rpow_natCast` (Mathlib)

規模: ~60-90 行 (本 plan で **真に新規な数学**はここ。κ の取り方が肝)。
proof-log: yes — κ の explicit 構成と、min vs 幾何平均の比評価で何が通ったか。

### Phase 3 — step 3: tilted typical set の確率 → 1 (Sanov LLN 起動)

- [ ] `chernoffTiltedTypicalSet` の補集合 `Q^n` 測度 → 0 を、Stein
      `steinTypicalSet_P_prob_tendsto_one` (`Stein.lean:275`) の証明構造を移植して示す
      (Q = `chernoffMediatorMeasure` を ambient、empirical mean が期待値に収束する弱大数)。
- [ ] `Q^n(T_n).toReal → 1` から `∀ᶠ n, Q^n(T_n).toReal ≥ 1/2` を取り出す
      (`Tendsto.eventually_ge_const` 系)。
- [ ] `chernoffMediatorMeasure_isProbabilityMeasure` (`ChernoffPerTiltDischarge.lean:435`) +
      `chernoffMediatorMeasure_pi_singleton_toReal` (`ChernoffPerTiltSanov.lean:219`) で
      n-letter singleton / prob measure instance を供給。

依存補題:
- `steinTypicalSet_P_prob_tendsto_one` — `Common2026/Shannon/Stein.lean:275` (移植元)
- `stein_inProbability` — `Common2026/Shannon/Stein.lean:213` (弱大数の本体、移植元)
- `chernoffMediatorMeasure_isProbabilityMeasure` — `ChernoffPerTiltDischarge.lean:435`
- `chernoffMediatorMeasure_pi_singleton_toReal` — `ChernoffPerTiltSanov.lean:219`
- `chernoffMediatorMeasure_pi_isProbability` (instance) — `ChernoffPerTiltSanov.lean:235`

規模: ~80-120 行 (移植が主。Stein は `Ω` 上の独立確率変数列で書かれているので、
`Measure.pi` 直接形への adaptation が要点)。
proof-log: yes — Stein 移植で型が合わない点 (Ω-RV 形 vs Measure.pi 形) の解消法。

### Phase 4 — step 1+2+3 合成: genuine per-tilt lower bound

- [ ] `bayesErrorMinPmf = (1/2)∑_x min` を `unfold` → 非負項を `T_n` に制限
      (`Finset.sum_le_sum_of_subset_of_nonneg`)。
- [ ] 各項に step 1 (Phase 2) を適用 → `∑_{x∈T_n} κ·(∏P₁)^{1-λ}(∏P₂)^λ`。
- [ ] step 2: `(∏P₁)^{1-λ}(∏P₂)^λ = Z(λ)^n · Q^n({x})` を per-block で
      (`chernoffMediatorMeasure_pi_singleton_toReal` + `chernoffMediator` 定義
      `= (P₁^{1-λ}P₂^λ)/Z` `ChernoffConverse.lean:101`)。
- [ ] `∑_{x∈T_n} Q^n({x}) = Q^n(T_n)` (`sum_measureReal_singleton` 系) → step 3 で `≥ 1/2`。
- [ ] 合成: `bayesErrorMinPmf ≥ (κ/4)·Z(λ)^n` eventually → `C := κ/2` で
      `C·Z(λ)^n ≤ 2·bayesErrorMinPmf`、`IsBayesErrorPerTiltLowerBound` を `⟨C, _, _⟩` で構成。

依存補題:
- `sum_prod_rpow_eq_Z_pow` — `Common2026/Shannon/Chernoff.lean:751`
- `chernoffZSum_pow_eq_sum_prod` — `Common2026/Shannon/ChernoffNLetterZSum.lean:36`
- `chernoffMediatorMeasure_pi_singleton_toReal` — `ChernoffPerTiltSanov.lean:219`
- `MeasureTheory.sum_measureReal_singleton` (Mathlib、Stein.lean が使用)
- `IsBayesErrorPerTiltLowerBound` 定義 — `ChernoffPerTiltDischarge.lean:136`

規模: ~50-70 行 (既存補題の合成が主、新規数学なし)。
proof-log: yes — Z 正規化の per-block 等式で `chernoffMediator` 定義を割る向きの符号。

### Phase 5 — name laundering 解消 (`chernoff_per_tilt_via_RN` の循環除去)

- [ ] Phase 4 の `isBayesErrorPerTiltLowerBound_genuine` を使い、
      `ChernoffPerTiltSanov.chernoff_per_tilt_via_RN` (`:162`, 現 `:= h_RN` 循環) を
      **genuine 経由に置換**。具体的には新 file で:
      `chernoff_lemma_tendsto_unconditional` 系を `isBayesErrorPerTiltLowerBound_genuine` +
      `chernoffInfo_attained` から組み、`IsChernoffNLetterRN` / `IsBayesErrorPerTiltLowerBound`
      hypothesis を **一切取らない** headline を新規 publish する。
- [ ] 既存の `chernoff_per_tilt_via_RN` 自体は predecessor file に残す (過去参照) が、
      その docstring に「genuine 版は `ChernoffSanovDischarge.lean` の
      `isBayesErrorPerTiltLowerBound_genuine` を参照。本 lemma の `:= h_RN` は循環で
      load-bearing predicate を運ぶだけ」と **defect 明示**を追記
      (※ predecessor file の編集は lean-implementer の領分。本 plan では「追記せよ」と指示するに留める)。
- [ ] 無条件 headline (target):

```lean
theorem chernoff_lemma_tendsto_unconditional
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1) :
    Tendsto (fun n : ℕ => -((1:ℝ)/n) * Real.log (bayesErrorMinPmf P₁ P₂ n))
      atTop (𝓝 (chernoffInfo P₁ P₂))
```

(`IsBayesErrorPerTiltLowerBound` / `IsChernoffNLetterRN` hypothesis なし = 標準B 達成。
`hP_sum` は regularity hyp なので OK。)

依存補題:
- `isBayesErrorPerTiltLowerBound_genuine` (Phase 4)
- `chernoffInfo_attained` — `Common2026/Shannon/Chernoff.lean:163`
- `chernoff_lemma_tendsto_from_predicate` — `ChernoffPerTiltDischarge.lean:204`
- `isChernoffPerTiltDischargeable_of_forall` — `ChernoffPerTiltDischarge.lean:346`

規模: ~30 行 (合成のみ)。

### Phase 6 — verify + Common2026 編入 + roadmap

- [ ] `lake env lean Common2026/Shannon/ChernoffSanovDischarge.lean` が silent (0 sorry)。
- [ ] `Common2026.lean` に `import Common2026.Shannon.ChernoffSanovDischarge` を追記
      (`ChernoffPerTiltSanov` の後、行 183 以降)。
- [ ] `lake build Common2026.Shannon.ChernoffSanovDischarge` で olean 確定。
- [ ] `docs/textbook-roadmap.md` の Chernoff converse 行を 🟢ʰ → 🟢 (無条件) に更新、
      本 plan §判断ログ + roadmap 判断ログに「per-tilt predicate を Sanov 経由で genuine 化、
      name laundering (`:= h_RN`) 解消」を記録。

規模: ~10 行。

---

## 撤退ライン (honest 限定)

step 1 か step 3 で本物の Mathlib gap に当たった場合のみ。`:True` / 結論同型述語への再逃避は禁止。

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

ただし step 1 (逆 Hölder) は **必ず genuine に証明する** (これは pure な実解析で Mathlib gap
なし、退避不可)。L-SD1 採用時も step 1+2+4 は genuine、step 3 のみ仮説化。
**name laundering 禁止**: 退避した仮説を `*_discharged` と命名しない。

**L-SD2** (redefine が step 1/4 で不可避と判明): M0 または Phase 4 で「min-和 ↔ Q^n(T_n)
集合測度」の昇格が ~50 行を超え、`bayesErrorMinPmf` redefine が安いと判明した場合のみ。
redefine する場合は **achievability チェーン (`bayesErrorMinPmf_le_half_Z_pow` →
`chernoff_lemma_achievability`, `Chernoff.lean:779`-`:1064`) の影響範囲を別 Phase 化**して
評価 (この plan には含めない、再起票)。**現判断: L-SD2 は採らない (設計判断 §参照)**。

撤退判定は M0 と Phase 2/3 の境界で。step 1 が通れば本 plan の核心は越えている。

---

## 検証

- 各 Phase: `lake env lean Common2026/Shannon/ChernoffSanovDischarge.lean` が silent
  (0 sorry / 0 warning) を fill 後に確認。`lake build` は使わない (inner loop 不適)。
- Phase 5 後、predecessor file の docstring 追記を lean-implementer がした場合は
  `lake build Common2026.Shannon.ChernoffPerTiltSanov` で olean refresh。
- 最終: 無条件 headline `chernoff_lemma_tendsto_unconditional` が
  `IsBayesErrorPerTiltLowerBound` / `IsChernoffNLetterRN` を **一切 hypothesis に取らない**
  ことを `#check` で確認 (= 標準B 達成の機械チェック)。

---

## 判断ログ

> 書く頻度: Phase 終了時 / 設計変更 / 撤退判定。append-only。

1. **2026-05-21 起草** (本セッション): predecessor `chernoff-converse-moonshot-plan.md`
   (L-CC2 着地、per-tilt predicate を残置) の後継として本 plan を新規。独立 strategy 再評価の
   結論 (CLT-port 不可 / Sanov 経由が正) を採用。**設計判断: `bayesErrorMinPmf` redefine
   しない** — 支配補題 `typeClassByCount_Qn_ge` (`SanovLDPEquality.lean:918`) /
   `sanov_ldp_lower_bound_pointwise` (`:1071`) の conclusion (`Measure.pi Q` 上集合測度) と
   現 min-和形の bridge は predecessor の `chernoffMediatorMeasure_pi_singleton`
   (`ChernoffPerTiltSanov.lean:197`) で既に架かっており、redefine の純利益なし。むしろ
   achievability チェーン (`Chernoff.lean:779`-`:1064`) を壊す損が確実。残りは step 1
   (逆 Hölder on typical set、唯一の新規数学) + step 3 (Sanov LLN 移植、Stein
   `Stein.lean:275` がテンプレート)。規模 ~150-300 行。
2. **honesty defect 記録** (起草時に発見): `chernoff_per_tilt_via_RN`
   (`ChernoffPerTiltSanov.lean:162`) は `IsChernoffNLetterRN` ≡ `IsBayesErrorPerTiltLowerBound`
   (body 字面一致、`:139` vs `:136`) で body `:= h_RN` の **循環 / name laundering**。
   predecessor docstring は honest に「pass-through」と書くが標準B では残タスク。
   本 plan Phase 5 で genuine な無条件 headline を新規 publish して解消する
   (既存 `:= h_RN` lemma は過去参照で残置、docstring に defect 明示を追記指示)。
