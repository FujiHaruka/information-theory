# Shannon: degraded BC achievability (superposition inner bound) サブ計画

> **Parent**: [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md)

**Status**: CLOSED ✅ — headline `bc_achievability` genuine closure (proof done = 0 sorry ∧ 0 @residual、sorryAx-free、独立監査 `@audit:ok`)。degraded broadcast-channel achievability / superposition-coding inner bound (Cover–Thomas Thm 15.6.2 の**達成側**)。`InformationTheory.lean` root 登録済 + README Ch.15 表登録済。撤退スロット L-BC1 / L-BC3 (親 frozen slug) は **未使用** — 全 leg が genuine で閉じたため sorry 退避せずに済んだ。
**SoT**: [`docs/textbook-roadmap.md`](../textbook-roadmap.md) Ch.15。詳細履歴は git。
**再検証** (prose にキャッシュしない): `#print axioms InformationTheory.Shannon.BroadcastChannel.bc_achievability` (= `[propext, Classical.choice, Quot.sound]`) / `scripts/sig_view.ts --sorry InformationTheory/Shannon/BroadcastChannel/Achievability.lean` (0 件)。

## 進捗 (全 leg 完了 — 1 行 + commit に圧縮)

- [x] M0 — inventory は advisor 精査で代替 (独立 phase skip)。
- [x] Leg 1 — skeleton + `bcJointDistribution` + `bcInfo₁/₂` + region target (cfd4a595)。
- [x] Leg 2 — two-tier codebook 型 + conditional codebook/ambient (compProd) def。BC-ambient iid infra は Leg 5、codebook averaging swap は Leg 6 で建造。
- [x] Leg 3 — receiver-2 cloud decoder + Bonferroni + indep bound (0a0221e2)。
- [x] Leg 4 — receiver-1 3-subevent Bonferroni `bc_errorProbAt₁_le_bonferroni3` (68efa06b)。
- [x] Leg 5 — ★ gateway atom `bc_conditional_slice_prob_le` (4f394dae、exponent 4ε、家系 GO、Mathlib gap なし)。
- [x] Leg 6 — random-coding swap 群 全 sorryAx-free + 独立監査 全 8 件 `@audit:ok` (5ec0063e)。新 def `bcInfoJoint` (= I((U,X);Y₁)) + E0₂ / E_b / E_c / wrong-cloud averaged swap。
- [x] Leg 7 — assembly ✅ — receiver-1/2 E0 vanishing (typicality-LLN) + averaged bound 組上げ + two-tier pigeonhole 存在抽出 + ε-selection。
- [x] Leg 8 — headline `bc_achievability` ✅ genuine closure + 独立監査 `@audit:ok` (`bc_achievability` / gate `bc_degraded_infoJoint_ge` / helper `bcMarkovChain_UX_Y₁_Y₂`) + root 配線 + README Ch.15 表。commits: e15f78cf (DPI closure + root wiring) / acd50a3e (@audit:ok) / 6f0c687d (README)。

## ゴール / Approach (達成、再利用しうる設計事実)

MAC achievability テンプレを ~55-60% 再利用 + 唯一の net-new tier = conditional (superposition) random coding を新規建造。**MAC↔BC 差分は codebook measure 形に 100% 局在**: satellite codeword を conditional compProd `Πᵢ K(Uᵢ)` で平均 (cloud center `U^n(w₂)` に条件付け)、flat product ではない。gateway-atom-first で Leg 5 ★ atom を最初に gate → GO。

**最終ゲート `bc_degraded_infoJoint_ge`** (degradedness superadditivity `bcInfo₁ + bcInfo₂ ≤ bcInfoJoint`、これで wrong-cloud を消す) は、`IsBCDegraded` から stochastic-degradation Markov chain `U→Y₁→Y₂` を自作 (reusable helper `isMarkovChain_of_append` = `isMarkovChain_comp_conditioner_right` の stochastic 版) + 既存 DPI `mutualInfo_le_of_markov` で genuine closure。

## 新規 def (Mathlib-shape-driven)

| def | 定義 | 備考 |
|---|---|---|
| `bcJointDistribution pU K W` | `pU`→`K`→`W` compProd | `macJointDistribution` を U 先頭に拡張 |
| `bcInfo₂ pU K W` | `I(U;Y₂)` (3-entropy) | `macInfo₂` parity |
| `bcInfo₁ pU K W` | `I(X;Y₁\|U)` (4-entropy conditional MI) | 独立 def、★ atom exponent (4ε) と結論形整合 |
| `bcInfoJoint pU K W` | `I((U,X);Y₁)` | receiver-1 wrong-cloud 用、degradedness superadditivity ゲートの対象 |
| two-tier codebook | cloud iid `pU` / satellite compProd `K(U(w₂,i))` | satellite measure は dependent (MAC との唯一の構造差) |

## Settled facts

| claim | confidence | 再検証 | notes |
|---|---|---|---|
| `bc_achievability` proof-done (0 sorry / 0 @residual、sorryAx-free) | machine | `#print axioms InformationTheory.Shannon.BroadcastChannel.bc_achievability` (= 標準 3 公理) | Leg 8 CLOSED、独立監査 `@audit:ok` |
| ★ atom (conditional-slice satellite prob) は Mathlib gap でなく in-project new-build | machine | `#print axioms ...bc_conditional_slice_prob_le` | Leg 5 CLOSED (4f394dae) |

## 判断ログ

1. **MAC↔BC 差分は codebook measure 形に局在 (設計軸)**: net-new は conditional (superposition) random coding 1 tier のみ、★ atom を gateway-atom-first で最初に gate → GO で家系全体を validate。
2. **Degradedness fork = (a) 採用**: `X → Y₁ → Y₂` Markov を precondition (regularity、非 load-bearing、独立監査確認)。closure では `bcInfoJoint ≥ bcInfo₁ + bcInfo₂` (superadditivity) を stochastic Markov `U→Y₁→Y₂` 自作 + DPI で genuine 化 = wrong-cloud を消す最終ゲート。
3. **撤退スロット未使用**: L-BC1 (joint typicality multi-receiver body) / L-BC3 (existence pass-through) は取らずに済んだ (全 genuine)。closure-plan-split (`bc-superposition-inner`) も不要。covering bound は `*Hypothesis` predicate に bundle せず (tier-5 禁止) genuine atom で供給。
