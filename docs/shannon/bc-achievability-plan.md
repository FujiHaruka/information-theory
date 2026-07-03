# Shannon: degraded BC achievability (superposition inner bound) サブ計画

> **Parent**: [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md)
> 撤退スロット = 親の frozen slug **L-BC1** (joint typicality multi-receiver body) / **L-BC3** (inner-bound existence pass-through)。

**Status**: 起草 — 未着手 (relay 無人多 leg 実装用)。
**SoT**: [`docs/textbook-roadmap.md`](../textbook-roadmap.md) Ch.15 (Cover–Thomas Thm 15.6.2 の **達成側** = superposition inner bound)。詳細履歴は git。
**再検証** (prose にキャッシュしない): `scripts/sig_view.ts --sorry InformationTheory/Shannon/BroadcastChannel/Achievability.lean` / `#print axioms InformationTheory.Shannon.BroadcastChannel.bc_achievability`。

目標 = headline `bc_achievability` を **genuine closure** (proof done = 0 sorry ∧ 0 @residual、sorryAx-free、独立監査 `@audit:ok`)。

## 進捗

- [~] M0 — inventory は advisor 精査が代替 (seed 3 本 file:line 確認済)。独立 inventory phase は skip。
- [x] Leg 1 — skeleton + `bcJointDistribution` + `bcInfo₁/₂` + region target ✅ (cfd4a595、type-check done、監査 PASS)
- [~] Leg 2 — two-tier codebook 型 + conditional codebook/ambient (compProd) def。**BC-ambient iid infra は Leg 5 で建造済** (bcAmbient_* coord lemmas / marginal factorization / positivity)。codebook averaging swap は残 (Leg 6)
- [x] Leg 3 — receiver-2 cloud decoder/code scaffold + Bonferroni + indep bound ✅ (0a0221e2、`bcCloudTypicalDecoder`/`bcJointTypicalDecoder`/`bcCodebookToCode` def + `bc_errorProbAt₂_le_bonferroni`/`bc_cloud_indep_prob_le` 2本 genuine sorryAx-free。単一ユーザ `jointlyTypicalSet_indep_prob_le` 直用、conditional tier 不要を実証)
- [ ] Leg 4 — receiver-1 joint decoder + per-receiver 3-subevent Bonferroni 再構成 📋
- [x] Leg 5 — ★ conditional-slice satellite prob atom ✅ **CLOSED** (`bc_conditional_slice_prob_le`、4f394dae、sorryAx-free、**家系 GO**。card×per-seq route、exponent 4ε、seed 3 本 as-advertised、Mathlib gap なし)
- [ ] Leg 6 — conditional random-coding swap (compProd marginalization、HIGH RISK) 📋
- [ ] Leg 7 — wrong-cloud (c) `macJTS_indep_prob_le_both` 再利用 + assemble 📋
- [ ] Leg 8 — `averageError₁∧₂ → 0` + headline `bc_achievability` + 独立監査 + root 配線 📋

## ゴール / Approach

全体戦略 = 直近 CLOSED の MAC achievability テンプレ (`MultipleAccess/Achievability.lean` ~2115 行 + `JointTypicality.lean` + `AchievabilityCore.lean`) を **~55-60% 再利用**しつつ、唯一の net-new tier = **conditional (superposition) random coding** を新規建造する。

**支配的な設計事実 — MAC↔BC の差分は `codebook measure の形` に 100% 局在**: union bound でも typicality-LLN でも SLLN でもない。MAC は flat product `codebookMeasure p₁ × codebookMeasure p₂` で平均するが、superposition は **衛星 codeword を conditional compProd `Πᵢ K(Uᵢ)` で平均**する (cloud center `U^n(w₂)` に条件付け)。この 1 点が全 net-new work を局在させ、典型集合 LLN / vanishing / Bonferroni / SLLN は MAC 資産の純配線 (plumbing) で流用できる。

**gateway-atom-first**: ★ atom (Leg 5、下記 conditional-slice satellite typicality probability bound) を可能な限り早く dispatch して**家系全体を gate**する。★ が通れば GO、詰まれば L-BC1/L-BC3 sorry 退避。CLAUDE.md「Mathlib-shape-driven Definitions」を **in-project atom の exponent と def を揃える**形で適用 (def が atom の結論形と out-of-box で一致するよう `bcInfo₁` を独立 def で建てる)。

## Statement shape (verbatim 候補、`BroadcastChannel/Basic.lean` の型に整合)

`BroadcastCode` (`Basic.lean:41`) は joint encoder `Fin M₁ × Fin M₂ → (Fin n → α)` + 2 分離 decoder。combined error は無く `averageErrorProb₁` (`Basic.lean:87`) / `averageErrorProb₂` (`Basic.lean:94`)、各 `ℝ≥0∞`。よって結論は 2 本の `.toReal < ε'` の連言。対応雛形 = `mac_achievability` (`Achievability.lean:1992`)。

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

## 新規 def (Mathlib-shape-driven、macJointDistribution / macInfo と parity)

`bcInfo`/`bcJointDistribution` は現状 `BroadcastChannel/` に不在 (`rg` 確認)、Leg 1 で net-new 建造。

| def | 型 / 定義 | 備考 |
|---|---|---|
| `bcJointDistribution pU K W` | `Measure (U × α × β₁ × β₂)` = `pU`→`K`→`W` の compProd | `macJointDistribution` (`IIDAmbient.lean:48`) を U 先頭に one-tier 拡張 |
| `bcInfo₂ pU K W` | `H(U)+H(Y₂)−H(U,Y₂)` (= `I(U;Y₂)`) | `macInfo₂` (`Achievability.lean:225`) と同じ 3-entropy 形 |
| `bcInfo₁ pU K W` | `H(U,X)+H(U,Y₁)−H(U,X,Y₁)−H(U)` (= `I(X;Y₁\|U)`) | **4-entropy 式・conditional MI**。macInfo は unconditional なので純 relabel でない → **独立 def**。★ atom exponent (`exp(−n(bcInfo₁−4ε))`、4ε = 4 typicality window slack) と型・結論形を揃える |
| two-tier codebook | cloud `Fin M₂ → (Fin n → U)` iid `pU`; satellite `Fin M₁ × Fin M₂ → (Fin n → α)` を `K(U(w₂,i))` から draw | satellite measure は **compProd / dependent**、flat product ではない ← MAC との唯一の構造差 |

## Degradedness fork

- **(a) 推奨**: degradedness Markov precondition `X → Y₁ → Y₂` を hypothesis で足す。これで receiver-1 joint decoding が要求する `R₁+R₂ < I(X;Y₁)` が `R₂<I(U;Y₂)≤I(U;Y₁)` から**自動充足**、`bc_converse` (`Converse.lean`) の `h_deg_block` / `h_memo` world (子 [`bc-degraded-converse-plan.md`](bc-degraded-converse-plan.md)) と parity。**regularity precondition であって load-bearing でない** (CI 構造仮説、独立監査で確認する)。
- **(b) 代替 (併記のみ)**: general inner bound + explicit 第 3 hypothesis `hRsum : R₁+R₂ < bcInfoJoint pU K W` (= `I(X;Y₁)`)、degradedness なし。recommend は (a)。実装で (a) が joint decoding の `R₁+R₂` 自動充足に効かない兆候が出たら (b) にピボット。

**honesty 注意**: degradedness / memoryless / full-support (`hpU`/`hK`/`hW`) は全て precondition。「レート対 ∈ 達成領域」や covering bound を仮説に bundle しない (tier-5 禁止、下記撤退ライン)。

## ★ gateway atom (Leg 5、最初に gate)

**conditional-independence satellite typicality probability bound** (superposition covering step、receiver-1 の "wrong satellite, correct cloud" 部分事象 (b)):

> typical cloud `u` と受信 `y₁` に対し、conditional-product measure `Πᵢ K(uᵢ)` での `{x : (u,x,y₁) ∈ jointlyTypical}` の質量が `≤ exp(−n(I(X;Y₁|U)−4ε))`。

**✅ CLOSED (4f394dae、sorryAx-free)**: card×per-seq route で closure。exponent は **4ε** (= 4 typicality window の slack、MAC atoms の 3ε と同型。plan 初稿の `−ε` は shorthand で AEP typicality からは証明不能 = likely false-as-framed だった)。full-support precondition `hpU`/`hK`/`hW` 追加 (regularity、監査確認予定)。`hy₁` は card×per-seq route では未使用 (benign warning)。`bc_achievability` が ε をスケールして吸収。

- seed infra (conclusion form 確認済、ただし drop-in ではない):
  - `conditionalTypicalSlice_card_le` (`SlepianWolf/ConditionalTypicalSlice.lean:140`) — **card 版・unconditional draw** なので slice の per-sequence mass を上乗せする必要あり。
  - `conditionalTypeClass_card_ge` (`ConditionalMethodOfTypes/Core.lean:776`) + `productMass_eq_columnProd` (`Core.lean:815`) — per-column 質量 = kernel 積の分解。
- 自作見積り **~120-200 行**。**Mathlib gap ではない** (in-project new-build、seed 3 本あり conclusion-shape 確認済) → `@residual(wall:...)` ではなく `@residual(plan:...)` 相当。
- **この atom で家系全体を gate**。通れば GO、詰まれば下記撤退。

## 再利用 MAC 資産 (plumbing = 純配線、read-only 呼出、file:line)

signature 改変なし (既存 lemma を呼ぶだけ) → 共有 lemma ripple なし、`dep_consumers` 対象外。

| 資産 | 場所 | 用途 |
|---|---|---|
| `macJointlyTypicalSet` + `_prob_tendsto_one` | `JointTypicality.lean:79` / `:195` | E0 (correct triple typical) vanishing |
| `macJTS_indep_prob_le_both` | `AchievabilityCore.lean:182` | receiver-1 wrong-cloud (c) `P ≤ exp(−n(I(X;Y₁)−·))` |
| `macJTS_indep_prob_le_X1` | `AchievabilityCore.lean:50` | receiver-2 cloud error `P ≤ exp(−n(I(U;Y₂)−·))` |
| `mac_errorProbAt_le_bonferroni4` | `Achievability.lean:91` | per-receiver 3-subevent Bonferroni に ~50% rework |

## Phase (Leg) 分解 (relay cap 8、各 leg は cold な次 leg が carryon で拾える粒度)

M0 は inventory 側 dispatch (docs-only、`mathlib-inventory`)、実装 leg cap 8 には数えない。`proof-log` = 当該 leg で proof-log を残すか。

| Phase | 内容 | risk | proof-log |
|---|---|---|---|
| **M0** | conditional random coding 側 API 在庫 (`bc-achievability-mathlib-inventory.md`)。対象: (i) `Kernel.pi`/`compProd`/`bind` の質量 lemma、(ii) `productMass_eq_columnProd` 質量版持ち上げに要る Kernel mass API、(iii) 4-entropy conditional MI の in-tree 補題 (converse family 資産の再利用可否)。per-lemma 構造化出力 (file:line + `[...]` verbatim) | 低 | no |
| 1 | Skeleton (`Achievability.lean` 全 def + 全 theorem `:= by sorry` 型チェック通過) + `bcJointDistribution` + `bcInfo₁/₂` + region target。数値/型予測 verbatim 確認 (`bcInfo` の `EReal`/`ℝ` 境界が exponent 結論形と整合するか) | 低 | no |
| 2 | two-tier codebook 型 + conditional codebook/ambient (compProd) def。satellite measure を **compProd / dependent** で構成 (flat product に潰さない)。`integral_compProd` が drop-in で効く shape に揃える | 中 | no |
| 3 | receiver-2 cloud decoder + error via `macJTS_indep_prob_le_X1` 再利用 (cloud は iid `pU` draw なので MAC 資産直流用、conditional tier 不関与) | 中 | no |
| 4 | receiver-1 joint decoder + per-receiver 3-subevent Bonferroni 再構成 (`mac_errorProbAt_le_bonferroni4` を 4→3 sub-event に ~50% rework)。error を (a) correct-pair miss / (b) wrong satellite・correct cloud / (c) wrong cloud に分解、(b)/(c) を Leg 5/7 注入 slot として穴あけ | 中 | **yes** |
| **5** | **★ conditional-slice satellite prob atom (gate here)**。上記 seed を質量版へ持ち上げ + per-column kernel 積分解。反証チェック (`K`=Dirac / `bcInfo₁=0` 退化境界で statement が生きるか 1 度置換) | **高** | **yes** |
| 6 | conditional random-coding swap (compProd marginalization)。satellite dependent measure `Πᵢ K(uᵢ)` を Leg 5 per-slice bound と接続、MAC の flat-product Fubini を compProd 版に差替え | 高 | **yes** |
| 7 | wrong-cloud (c) `macJTS_indep_prob_le_both` 再利用 + Leg 4 の 3-subevent slot に (a)=vanishing/(b)=Leg5/(c)=本leg 注入して receiver-1 per-message error を組上げ | 中 | no |
| 8 | `averageError₁∧₂ → 0` (rate slack から) + headline `bc_achievability` + 独立監査 (`honesty-auditor`、新 sorry/新 def 導入で orchestrator mandatory) + `InformationTheory.lean` root 配線 + README/roadmap Ch.15 同期 | 中 | no |

8 leg 収束は **leg 5/6 (conditional tier) が validate すること**が条件。gateway-atom-first で leg 5 を早めに叩く。

## 撤退ライン (L-BC1 / L-BC3 frozen slot)

- **skeleton / 未実装 sorry の slug**: 本 plan が owner なので `@residual(plan:bc-achievability-plan)` (filename stem、audit-tags.md 慣習 line 59)。
- **Leg 5/6 の conditional tier が in-session で閉じない (genuine wall) 場合のみ**: closure-plan-split 機構で `bc-superposition-inner-plan.md` を新規起草し、slug を `plan:bc-superposition-inner` に付替えて core を移管 (tier 2、**full statement 維持**)。それまでは本 plan が owner。
  - Leg 5 atom / Leg 6 swap の sorry = 親 **L-BC1「joint typicality multi-receiver body」**に対応。
  - headline 存在部の pass-through sorry = 親 **L-BC3「inner bound existence pass-through」**に対応。
- **禁止 (tier-5 load-bearing)**: covering bound (★ atom) を `IsBCSuperpositionCoveringHypothesis` 等の `*Hypothesis` predicate に bundle して仮説で渡し body を機械展開だけにするのは **禁止** (CLAUDE.md「検証の誠実性」)。詰まったら必ず `sorry` + `@residual` で抜ける。degradedness / memoryless / full-support は precondition なので OK。
- **shared 壁化の条件**: RD (`SlepianWolf`) / WynerZiv と共有な conditional-covering 壁が **真に** 現れたら (= 2+ family で shared sorry 補題として再利用が確定)、`audit-tags.md`「提案中 wall」の `relay-cf-wz-binning` / `csiszar-sum-conditional` の promote 判定に乗せて shared sorry-lemma 化。それまでは `plan:` slug で揃える (デフォルト方針)。**壁判定前に ★ atom を 1 本 dispatch** (gateway-atom-first)。

## 親へ追記すべき backlink 行 (orchestrator が反映 — 本 plan は親を編集しない)

親 `broadcast-channel-moonshot-plan.md` の「## Sub-plan 一覧」表に以下 1 行を追加:

```
| [`bc-achievability-plan.md`](bc-achievability-plan.md) | L-BC1/L-BC3 degraded BC achievability (superposition inner bound、`bc_achievability`、conditional random coding) | 起草 — 未着手 📋 |
```

併せて親 Status 行の「BC achievability (superposition inner bound) … は scope-out 継続」を「achievability は子 [`bc-achievability-plan.md`] で再開 (起草)」に更新すべき (親 Status は現状 achievability を scope-out と記載、本 plan 起草で drift。pre-commit が「子更新時に親 co-stage」を WARN するので同一 commit に親を含める)。

## Settled facts

| claim | confidence | 再検証 | notes |
|---|---|---|---|
| BC scaffolding (BroadcastCode/error/region) 既存・0 sorry | machine | `scripts/sig_view.ts InformationTheory/Shannon/BroadcastChannel/Basic.lean` | `Basic.lean` scaffolding |
| `Achievability.lean` 未作成 | machine | `ls InformationTheory/Shannon/BroadcastChannel/` | Leg 1 で新規 |
| ★ atom は Mathlib gap でなく in-project new-build | human-judgment | — | advisor 精査、要 gateway-atom 再確認 (低信頼、Leg 5 dispatch で機械裏取り) |

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除 (git が履歴)、active な判断のみ残す。

1. **MAC↔BC 差分は codebook measure 形に局在 (設計軸)**: union bound / typicality-LLN / SLLN は MAC 資産で純配線、net-new は conditional (superposition) random coding 1 tier のみ。★ atom (Leg 5) を gateway-atom-first で最初に gate。
2. **Degradedness fork = (a) 採用**: `X → Y₁ → Y₂` Markov を precondition で足し `bc_converse` の `h_deg_block` world と parity (regularity、非 load-bearing)。(b) general + `hRsum` は fallback。
3. **slug 方針**: 未実装 sorry は `plan:bc-achievability-plan` (本 plan が owner)。conditional tier が genuine wall 化したら `bc-superposition-inner-plan.md` split + slug 付替え (closure plan 機構)。shared 壁化 (RD/SW 共有) は 2+ family 再利用が確定したときのみ promote。
