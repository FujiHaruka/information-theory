# BC (degraded) achievability — superposition inner bound 実装計画 🌙

**Status**: 進行中 — Phase 0/8 (relay)。skeleton 未着手。
**SoT**: [`docs/textbook-roadmap.md`](../textbook-roadmap.md) Ch.15。詳細履歴は git。

> **Parent**: [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md)
> 撤退スロット = 親の frozen slug **L-BC1** (joint typicality multi-receiver body) / **L-BC3** (inner-bound existence pass-through)。

Cover–Thomas *Elements of Information Theory* Thm 15.6.2 の **達成側** (superposition inner
bound)。目標 = headline `bc_achievability` を **genuine closure** (proof done = 0 sorry ∧ 0
@residual, sorryAx-free, 独立監査 `@audit:ok`)。

---

## Approach

全体戦略 = 直近 CLOSED の MAC achievability テンプレ (`MultipleAccess/Achievability.lean`
~2115 行 + `JointTypicality.lean` + `AchievabilityCore.lean`) を **~55-60% 再利用**しつつ、唯一の
net-new tier = **conditional (superposition) random coding** を新規建造する。

**MAC↔BC の差分は union bound でも typicality-LLN でもなく、`codebook measure の形` に 100% 局在**:
MAC は flat product `codebookMeasure p₁ × codebookMeasure p₂` で平均するが、superposition は
**衛星 codeword を conditional compProd `Πᵢ K(Uᵢ)` で平均**する (cloud center `U^n(w₂)` に条件付け)。
この 1 点が全 net-new work を局在させる。

**gateway-atom-first**: ★ atom (leg 5、下記 conditional-slice satellite typicality probability
bound) を可能な限り早く dispatch して**家系全体を gate**する。★ が通れば GO、詰まれば
L-BC1/L-BC3 sorry 退避。CLAUDE.md「Mathlib-shape-driven Definitions」を **in-project atom の
exponent と def を揃える**形で適用 (def が atom の結論形と out-of-box で一致するよう `bcInfo₁` を建てる)。

---

## Statement shape (verbatim 候補、`BroadcastChannel/Basic.lean` の型に整合)

`BroadcastCode` (Basic.lean:41) は joint encoder `Fin M₁ × Fin M₂ → (Fin n → α)` + 2 decoder。
combined error は無く `averageErrorProb₁/₂` (Basic.lean:87/94、各 `ℝ≥0∞`) の 2 本。よって結論は
2 本の `.toReal < ε'` の連言。対応雛形 = `mac_achievability` (Achievability.lean:1992)。

```lean
theorem bc_achievability
    {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
      [MeasurableSpace U] [MeasurableSingletonClass U]
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]                 -- conditional input pmf p(x|u), cloud→satellite
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ u, 0 < pU.real {u}) (hK : ∀ u a, 0 < (K u).real {a}) (hW : ∀ a b, 0 < (W a).real {b})
    -- degradedness fork (a): X → Y₁ → Y₂ precondition (詳細下記)
    {R₁ R₂ : ℝ} (_hR₁ : 0 < R₁) (_hR₂ : 0 < R₂)
    (hR₁lt : R₁ < bcInfo₁ pU K W)                        -- I(X;Y₁|U)
    (hR₂lt : R₂ < bcInfo₂ pU K W)                        -- I(U;Y₂)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N, ∀ n, N ≤ n → ∃ (M₁ M₂ : ℕ)
      (_hM₁ : Nat.ceil (Real.exp (n*R₁)) ≤ M₁) (_hM₂ : Nat.ceil (Real.exp (n*R₂)) ≤ M₂)
      (c : BroadcastCode M₁ M₂ n α β₁ β₂),
      (c.averageErrorProb₁ W).toReal < ε' ∧ (c.averageErrorProb₂ W).toReal < ε'
```

---

## 新規 def (Mathlib-shape-driven、macJointDistribution / macInfo と parity)

| def | 型 / 定義 | 備考 |
|---|---|---|
| `bcJointDistribution pU K W` | `Measure (U × α × β₁ × β₂)` = `pU`→`K`→`W` の compProd | `macJointDistribution` 相当 |
| `bcInfo₂ pU K W` | `H(U)+H(Y₂)−H(U,Y₂)` (= `I(U;Y₂)`) | `macInfo` parity |
| `bcInfo₁ pU K W` | `H(U,X)+H(U,Y₁)−H(U,X,Y₁)−H(U)` (= `I(X;Y₁\|U)`) | **4-entropy 式・conditional MI**。macInfo は unconditional なので純 relabel でない → **独立 def**。★ atom exponent と揃える |
| two-tier codebook | cloud `Fin M₂ → (Fin n → U)` iid `pU`; satellite `Fin M₁ × Fin M₂ → (Fin n → α)` を `K(U(w₂,i))` から draw | satellite measure は **compProd / dependent**、flat product ではない |

---

## Degradedness fork

- **(a) 推奨**: degradedness Markov precondition `X → Y₁ → Y₂` を hypothesis で足す。これで
  receiver-1 joint decoding が要求する `R₁+R₂ < I(X;Y₁)` が `R₂<I(U;Y₂)≤I(U;Y₁)` から**自動充足**、
  `bc_converse` (Converse.lean) の `h_deg_block` / `h_memo` world と parity。**regularity precondition
  であって load-bearing でない** (独立監査で確認する)。
- **(b) 代替**: general inner bound + explicit 第 3 hypothesis `hRsum : R₁+R₂ < bcInfoJoint pU K W`
  (= `I(X;Y₁)`)、degradedness なし。recommend は (a)。

---

## ★ gateway atom (leg 5、最初に gate)

**conditional-independence satellite typicality probability bound** (superposition covering step、
receiver-1 の "wrong satellite, correct cloud" 部分事象 (b)):

> typical cloud `u` と受信 `y₁` に対し、conditional-product measure `Πᵢ K(uᵢ)` での
> `{x : (u,x,y₁) ∈ jointlyTypical}` の質量が `≤ exp(−n(I(X;Y₁|U)−ε))`。

- seed infra (conclusion form 確認済、ただし drop-in ではない):
  - `conditionalTypicalSlice_card_le` (`SlepianWolf/ConditionalTypicalSlice.lean:140`) — card 版・
    unconditional draw なので slice の per-sequence mass を上乗せする必要あり。
  - `ConditionalMethodOfTypes/Core.lean` (`conditionalTypeClass_card_ge`, `productMass_eq_columnProd`)。
- 自作見積り **~120-200 行**。**Mathlib gap ではない** (in-project new-build)。
- **この atom で家系全体を gate**。通れば GO、詰まれば下記撤退。

---

## 再利用 MAC 資産 (plumbing = 純配線、file:line)

| 資産 | 場所 | 用途 |
|---|---|---|
| `macJointlyTypicalSet` + `_prob_tendsto_one` | JointTypicality.lean:79 / 195 | E0 (correct triple typical) vanishing |
| `macJTS_indep_prob_le_both` | AchievabilityCore.lean:182 | receiver-1 wrong-cloud `P ≤ exp(−n(I(X;Y₁)−·))` |
| `macJTS_indep_prob_le_X1` | AchievabilityCore.lean:50 | receiver-2 cloud error `P ≤ exp(−n(I(U;Y₂)−·))` |
| `mac_errorProbAt_le_bonferroni4` | Achievability.lean:91 | per-receiver 3-subevent Bonferroni に ~50% rework |

---

## Leg 分解 (relay cap 8)

| Phase | 内容 | risk |
|---|---|---|
| 1 | Skeleton (`Achievability.lean` 全 def + 全 theorem `:= by sorry` 型チェック通過) + `bcJointDistribution` + `bcInfo₁/₂` + region target | 低 |
| 2 | two-tier codebook 型 + conditional codebook/ambient (compProd) def | 中 |
| 3 | receiver-2 cloud decoder + error via `macJTS_indep_prob_le_X1` 再利用 | 中 |
| 4 | receiver-1 joint decoder + per-receiver 3-subevent Bonferroni 再構成 | 中 |
| **5** | **★ conditional-slice satellite prob atom (gate here)** | **高** |
| 6 | conditional random-coding swap (compProd marginalization) | 高 |
| 7 | wrong-cloud (c) `macJTS_indep_prob_le_both` 再利用 + assemble | 中 |
| 8 | `averageError₁∧₂ → 0` + headline `bc_achievability` + 独立監査 + root 配線 + README/roadmap 同期 | 中 |

8 leg 収束は **leg 5/6 (conditional tier) が validate すること**が条件。gateway-atom-first で leg 5 を早めに叩く。

---

## 撤退ライン (L-BC1 / L-BC3 frozen slot)

- leg 5/6 の conditional tier が in-session で閉じなければ `bc_achievability` body を
  `sorry` + `@residual(plan:bc-superposition-inner)` (tier 2、**full statement 維持**)。
- **covering bound を `*Hypothesis` predicate に bundle するのは禁止** (tier-5 load-bearing)。
- RD/SW と共有な conditional-covering 壁が出たら shared sorry-lemma (audit-tags.md「Shared Mathlib walls」)。

---

## Settled facts

| claim | confidence | 再検証 | notes |
|---|---|---|---|
| BC scaffolding (BroadcastCode/error/region) 既存・0 sorry | machine | `scripts/sig_view.ts Basic.lean` | Basic.lean 13 decl |
| Achievability.lean 未作成 | machine | `ls BroadcastChannel/` | leg 1 で新規 |
| ★ atom は Mathlib gap でなく in-project new-build | human-judgment | — | advisor 精査、要 gateway 再確認 |

## Decision log (active)

- degradedness fork = (a) 採用 (converse parity)。(b) は fallback。
- codebook measure = conditional compProd (flat product 不採用、marginalization 手法が MAC と異なる)。
