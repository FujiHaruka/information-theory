# EPI G2: 層2 (エントロピー汎関数への持ち上げ) ムーンショットサブ計画 🌙

> **Parent**: [`epi-g2-continuity-plan.md`](epi-g2-continuity-plan.md) §「Route B — machinery 自前構築」
> **対象壁**: `wall:heatflow-continuity`
> (`InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean:137`
> `heatFlowEntropyPower_continuousWithinAt_zero`、body `sorry`)
> **一次根拠**: [`epi-g2-layer2-semicontinuity-inventory.md`](epi-g2-layer2-semicontinuity-inventory.md)
> (5 カテゴリ構造化在庫)

<!--
記法: 状態絵文字 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更(判断ログ参照)。
取り消し線 = 廃止 Phase (履歴のため残す)。判断ログ append-only。
-->

## 進捗

- [ ] Phase 0 — 列特徴付けブリッジの API 在庫確定 📋
- [ ] Phase 1 — 層1 L¹ mollifier 収束 (`wall:approx-identity-L1` 切出 + 先行 ship) 📋
- [ ] Phase 2 — `UnifIntegrable` / `UnifTight` witness 構成 📋
- [ ] Phase 3 — 層2 machinery genuine 化 (列化 + Vitali + L¹→積分 + exp 再合成) 📋
- [ ] Phase 4 — 壁補題 closure / proof-done 結線 📋

proof-log: Phase 1〜3 は yes (新規 analytic content、判断記録の価値大)。Phase 0/4 は no。

## ゴール / Approach

**ゴール**: 壁補題 `heatFlowEntropyPower_continuousWithinAt_zero` の `sorry` を genuine 0 にし、
EPI G2 端点連続性 (`wall:heatflow-continuity`) を閉じる。consumer
`csiszarLogRatioGap_continuousWithinAt_zero` / `_antitoneOn_Ici_zero` (R-5-c live) は own
`@residual` を持たず本壁経由の transitive のみなので、壁 closure で transitive に genuine 化する。

### 全体戦略 (ルートA、shape)

在庫の確定 positive 発見 = **層2 machinery (Vitali / L¹→積分) は無限測度 `volume` on ℝ で通る**
(`tendsto_Lp_of_tendsto_ae` / `tendsto_integral_of_L1'` が `[IsFiniteMeasure]` 非要求、orchestrator
verbatim 確認済)。壁は machinery でなく**入力側 (層1 L¹ 収束 + UI/UT witness)** に局在する。

```text
密度 f_t := convDensityAdd pX (gaussianPDFReal 0 ⟨t,_⟩)   (= P.map(X+√t·Z) の密度)

  [Phase 1] 層1: t→0⁺ で f_t → pX in L¹(volume)              ← 真壁 (自作、wall:approx-identity-L1)
       │   近似単位元の標準事実。Mathlib 未整備 (convolution_tendsto_right は
       │   pointwise/bump 限定、tendsto_convDensityAdd_gaussian_zero は z→±∞ で別物)
       ▼
  [Phase 2] UnifIntegrable {negMulLog f_t} 1 volume + UnifTight  ← 自作 (Vitali 2 仮説)
       │   UnifTight は pX_mom (有限2次モーメント) 由来 tail 評価で構成見込み
       ▼
  [Phase 3-a] 列化: 𝓝[Ioi 0] 0 を任意列に落とす                ← genuine machinery
       │   Filter.tendsto_iff_seq_tendsto (𝓝[Ioi 0] 0 は IsCountablyGenerated)
       ▼
  [Phase 3-b] Vitali (UnifTight 版): tendsto_Lp_of_tendsto_ae   ← Mathlib (genuine)
       │   → eLpNorm (negMulLog f_t − negMulLog pX) 1 volume → 0
       ▼
  [Phase 3-c] L¹→積分: tendsto_integral_of_L1'                  ← Mathlib (genuine、測度非依存)
       │   → ∫ negMulLog f_t → ∫ negMulLog pX = differentialEntropy(P.map X)
       ▼
  [Phase 3-d] exp 再合成 + ContinuousWithinAt 化                ← genuine
       │   Real.continuous_exp.comp
       ▼
  [Phase 4] entropyPower の ContinuousWithinAt (Set.Ioi 0) 0   ← 壁補題 closure
```

### shared sorry 補題切出による surface shrink 評価

在庫が示唆した通り、**層1 L¹ 収束を独立 shared sorry 補題
`convDensityAdd_tendsto_L1_zero` (`@residual(wall:approx-identity-L1)`) に切り出す**ことで、
層2 (Phase 3 全体) を genuine に閉じられる。その結果:

- 壁補題 `heatFlowEntropyPower_continuousWithinAt_zero` の `sorry` は **削除可能** (Phase 1〜3 が
  揃えば genuine、`@audit:ok` 候補)。残る `sorry` は層1 補題 1 本に集約。
- 壁の表面積が「entropyPower の端点連続性全体」から「近似単位元の L¹ 収束」へ縮小。後者は
  **より小さく・より標準的・上流 Mathlib PR 化しやすい**命題。これは honesty surface shrink の
  正規パターン (`docs/audit/audit-tags.md`「共有 Mathlib 壁」)。
- `wall:heatflow-continuity` register は本壁が閉じた段で「層1 残壁を `wall:approx-identity-L1`
  に移送、層2 は genuine」と reconcile する (Phase 4)。

**Phase 2 (UI/UT) も自作だが、これは load-bearing でなく Vitali への入力供給**。UI は
`unifIntegrable_of_tendsto_Lp` (`:553`) が層1 L¹ 収束から出るが循環気味 (在庫 §自作要素 2) なので、
直接構成 (Phase 2 で独立 sorry → 後続で genuine 化) を採るか、層1 補題に UI/UT を込めるかは
Phase 2 で判断 (判断ログ)。**UI/UT を `*Hypothesis` predicate に bundle するのは禁止** (load-bearing)。

### honesty 境界 (常時)

- 層1 L¹ 収束 / UI/UT を **`*Hypothesis` / `*Reduction` predicate に bundle して仮説で渡すのは
  禁止** (load-bearing、tier 5)。撤退は必ず `sorry` + `@residual(wall:approx-identity-L1)`。
- 壁補題の signature に「連続性結論を hyp に取る」変更を加えない (循環)。仮説強化が必要になった場合
  (撤退ライン)、追加してよいのは **precondition** (negMulLog 一様可積分性 / entropy 有限性 = regularity)
  のみ。判定軸 → 後述「落とし穴2」。

## Phase 0 — 列特徴付けブリッジの API 在庫確定 📋

- **入力**: 在庫カテゴリ1「ℕ-filter 注意」(`tendsto_Lp_of_tendsto_ae` が `f : ℕ → α → β` 列限定)。
- **出力結論型** (verbatim、orchestrator 確認済):
  ```lean
  -- Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean:97
  theorem Filter.tendsto_iff_seq_tendsto {f : α → β} {k : Filter α} {l : Filter β}
      [k.IsCountablyGenerated] :
      Tendsto f k l ↔ ∀ x : ℕ → α, Tendsto x atTop k → Tendsto (f ∘ x) atTop l
  ```
- **タスク**:
  - [ ] `𝓝[Set.Ioi 0] (0:ℝ)` が `IsCountablyGenerated` instance を持つか確認
    (ℝ 第一可算 → `nhdsWithin` の countably-generated instance、`rg`/loogle で 1 行確認)。
  - [ ] 列 `u : ℕ → ℝ`、`Tendsto u atTop (𝓝[Ioi 0] 0)` から `0 < u n` (eventually) と
    `u n → 0` を取り出す形を確認 (`tendsto_nhdsWithin_iff` / `eventually_mem_nhdsWithin`)。
  - [ ] 列ごとに `AEStronglyMeasurable (negMulLog (f_{u n}))` / `MemLp (negMulLog pX) 1` /
    UI / UT を供給する skeleton 形を確定 (Phase 3-b への引数表)。
- **依存**: なし (純 API 確認)。
- **工数感**: 15〜30 行 (在庫 §自作要素 4「sequential 化」相当)。
- **落とし穴**: 列ごとに UI/UT を供給する形に整える必要 (在庫 §自作要素 4 落とし穴)。
  「自明」で流さない (落とし穴1 = orchestrator 指摘)。`Filter.tendsto_iff_seq_tendsto` の
  `f ∘ x` は **積分値の列** `n ↦ ∫ negMulLog f_{u n}` に適用 (連続版を直接列化せず、Phase 3-c の
  L¹→積分の極限を `ContinuousWithinAt` に翻訳する段で噛ませる)。
- **撤退口**: ブリッジ自体は genuine (Mathlib 既存)。`IsCountablyGenerated` instance が見つからない
  場合のみ要追加調査だが、ℝ 第一可算なので存在する見込み。

## Phase 1 — 層1 L¹ mollifier 収束 📋 (先行 ship 候補)

- **入力**: `pX` の正則性 (`IsDeBruijnRegularityHyp` 経由の L¹ 非負可測 + 有限2次モーメント)。
  部品: `convDensityAdd` 系 (`EPIConvDensity.lean:42`)、`tendsto_convDensityAdd_gaussian_zero`
  (`EPIConvDensityRegular.lean:148`、ただし `z→±∞` で別物、参考のみ)。
- **出力結論型** (verbatim、在庫 skeleton 由来):
  ```lean
  /-- @residual(wall:approx-identity-L1) -/
  theorem convDensityAdd_tendsto_L1_zero
      {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
      (hpX_int : Integrable pX volume)
      (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) :
      Tendsto (fun t : ℝ =>
        eLpNorm (convDensityAdd pX (gaussianPDFReal 0 ⟨t, by positivity⟩) - pX) 1 volume)
        (𝓝[Set.Ioi 0] 0) (𝓝 0)
  ```
- **依存**: なし (crux と独立、再利用資産)。**B-crux の GO/NO-GO に依らず数学的に正しい**ので
  **先行 ship 候補** (親 Route B B-1 と一致)。
- **工数感**: 80〜150 行 (在庫 §自作要素 1、**支配項**)。
- **落とし穴**:
  - gaussianPDF は compact support でない (ContDiffBump 不可) → tail 評価が要る。
  - 一般 L¹ `pX` (可積分特異点あり) で成立する標準事実だが、Mathlib の近似単位元 L¹ 収束一般定理が
    不在。素材 (連続関数の L¹ 稠密 + L¹ translation continuity + Young 不等式) は散在するが組上げ未整備。
- **撤退口**: 1-session で組めない → `sorry` + `@residual(wall:approx-identity-L1)` のまま ship。
  これが**最小 ship 単位**: 層1 補題の signature を確定し sorry で park するだけでも、Phase 3 の
  genuine 化 (層2) が層1 補題呼出で閉じられる構造を先に作れる。**仮説束化禁止** (L¹ 収束を
  `*Hypothesis` predicate に bundle しない)。
- **honesty**: `wall:approx-identity-L1` は register 未登録。Phase 4 で promote 判断
  (loogle 0 件確認 + register 追記、`audit-tags.md` Wall name register 手順)。
  現状は Proposed wall 扱い、初出は本 plan。

## Phase 2 — `UnifIntegrable` / `UnifTight` witness 構成 📋

- **入力**: 層1 L¹ 収束 (Phase 1) + `pX_mom` (有限2次モーメント)。
- **出力結論型** (verbatim、在庫カテゴリ1):
  ```lean
  -- 列 u : ℕ → ℝ (Phase 0 で供給、0 < u n eventually) に対し
  UnifIntegrable (fun n => fun x => negMulLog (f_{u n} x)) 1 volume
  UnifTight     (fun n => fun x => negMulLog (f_{u n} x)) 1 volume
  -- UnifTight 定義 (UnifTight.lean:59):
  --   ∀ ε>0, ∃ s, μ s ≠ ∞ ∧ ∀ i, eLpNorm (sᶜ.indicator (f i)) p μ ≤ ε
  ```
- **依存**: Phase 1 (UI を `unifIntegrable_of_tendsto_Lp` 経由で出す場合)、Phase 0 (列形)。
- **工数感**: 40〜80 行 (在庫 §自作要素 2)。
- **落とし穴**:
  - **循環注意**: `unifIntegrable_of_tendsto_Lp` (`:553`) は `negMulLog f_t` の L¹ 収束から UI を
    出すが、それは Phase 1 (密度 `f_t` の L¹ 収束) とは別物 (`negMulLog` 適用後の L¹ 収束)。
    在庫 §自作要素 2 が「1 と循環気味」と指摘。**直接構成 (tail 評価) を第一候補**とし、
    `unifIntegrable_of_tendsto_Lp` 経由は補助に留める。
  - `negMulLog` の符号構造 (`x>1` で負・`x→∞` で `-∞`) が DCT 直接 majorant を塞ぐ根本原因
    (在庫カテゴリ3)。UnifTight は majorant 不要 (`sᶜ` 上 Lp ノルム小だけ) なので回避できるが、
    負部の tail 制御に `pX_mom` をどう効かせるか要設計。
  - `convDensityAdd_negMulLog_integrable` (`FisherInfoV2DeBruijnAssembly.lean:2529`) は `private`
    (在庫 §自作要素 3) → Phase 3-c の `Integrable (F i)` 供給に file 跨ぎ public 化 or 共有 sorry
    補題化が要る (5〜15 行 plumbing)。**この plumbing は Phase 3 の依存として明示**。
- **撤退口**: UnifTight が `volume` 上 `pX_mom` だけからは原理的に出ない (= 反例で偽) と判明
  → 撤退ライン (後述「撤退ライン」)。それまでは `sorry` + `@residual(wall:approx-identity-L1)`
  (層1 と同壁に集約) or 独立 `@residual(plan:epi-g2-layer2-moonshot-plan)`。

## Phase 3 — 層2 machinery genuine 化 📋

層1 補題 (Phase 1) + UI/UT (Phase 2) + 列化ブリッジ (Phase 0) を仮定すれば、**この Phase 全体は
Mathlib 既存 machinery で genuine に閉じる** (sorry なし目標)。

- **3-a 列化**: `Filter.tendsto_iff_seq_tendsto` (Phase 0) で `𝓝[Ioi 0] 0` を任意列 `u` に。
- **3-b Vitali (無限測度版)**:
  ```lean
  -- UnifTight.lean:329 (verbatim、[IsFiniteMeasure] 非要求、orchestrator 確認済)
  theorem tendsto_Lp_of_tendsto_ae (hp : 1 ≤ p) (hp' : p ≠ ∞)
      {f : ℕ → α → β} {g : α → β} (haef : ∀ n, AEStronglyMeasurable (f n) μ)
      (hg' : MemLp g p μ) (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
      (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
      Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)
  ```
  入力: `hg'` = **`MemLp (negMulLog pX) 1 volume`** (← 落とし穴2、後述)、`hui`/`hut` (Phase 2)、
  `hfg` = a.e. 各点収束 `negMulLog f_{u n} → negMulLog pX` (Phase 1 の L¹ 収束 → a.e. 部分列、または
  `convDensityAdd` の pointwise 収束 + `Real.continuous_negMulLog`)。
- **3-c L¹→積分**:
  ```lean
  -- Bochner/Basic.lean:409 (verbatim、測度・filter 非依存)
  lemma tendsto_integral_of_L1' (f : α → G) (hfi : Integrable f μ) {F : ι → α → G} {l : Filter ι}
      (hFi : ∀ᶠ i in l, Integrable (F i) μ) (hF : Tendsto (fun i ↦ eLpNorm (F i - f) 1 μ) l (𝓝 0)) :
      Tendsto (fun i ↦ ∫ x, F i x ∂μ) l (𝓝 (∫ x, f x ∂μ))
  ```
  入力: `hfi` = `Integrable (negMulLog pX) volume` (← 落とし穴2)、`hFi` = 各 t の可積分性
  (`convDensityAdd_negMulLog_integrable`、要 public 化 = Phase 2 plumbing)、`hF` = 3-b の出力。
- **3-d exp 再合成 + ContinuousWithinAt 化**: `Real.continuous_exp.comp` + 3-c の積分極限を
  `ContinuousWithinAt (fun t => entropyPower …) (Ioi 0) 0` に翻訳。
- **依存**: Phase 0, 1, 2 + Phase 2 の `convDensityAdd_negMulLog_integrable` public 化。
- **工数感**: 3-d で 20〜40 行 (在庫 §自作要素 5)、3-a〜3-c は machinery 結線 30〜50 行。
- **落とし穴**:
  - **落とし穴2 (orchestrator 指摘) = `hg'` / `hfi` の出所**: `MemLp (negMulLog pX) 1 volume`
    (= h(X) 有限) は L¹+2次モーメントからは出ない (集中密度で `∫ negMulLog pX = −∞` がありうる)。
    → 下記「落とし穴2 への対処」で 3 選択肢を評価。
  - a.e. 各点収束 (`hfg`) は L¹ 収束から直接でなく部分列経由 (Phase 3-a の列化と整合させる)。
- **撤退口**: machinery 部分は genuine 目標。落とし穴2 が precondition 追加で解けない場合のみ
  撤退ライン。

### 落とし穴2 への対処 — `MemLp (negMulLog pX) 1 volume` (= h(X) 有限) の出所

`tendsto_Lp_of_tendsto_ae` の `hg'` と `tendsto_integral_of_L1'` の `hfi` が両方
`negMulLog pX` の可積分性 (= 微分エントロピー h(X) 有限) を要求する。L¹+2次モーメントだけからは
**出ない** (集中密度 / 可積分特異点で `∫ negMulLog pX = −∞` 反例)。選択肢と honesty 評価:

| 選択肢 | 内容 | honesty 評価 | 採否判断軸 |
|---|---|---|---|
| **(a)** `IsDeBruijnRegularityHyp` に regularity field 1 つ追加 (`hX_entropy_finite : Integrable (negMulLog pX) volume` 等) | 構造に precondition フィールド追加 | **OK** (precondition、load-bearing でない — 連続性結論でなく入力密度の有限エントロピー regularity) | 既存 consumer が全て probability density 由来で h(X) 有限を満たすなら採用。signature 変更 → 独立 honesty audit 起動 (CLAUDE.md 条件「signature 変更で honesty 意味が変わる」) |
| **(b)** 既存フィールドから導出可能か再調査 | `pX_mom` 等から `Integrable (negMulLog pX)` を出せるか | 出せるなら最良 (追加なし)。だが反例 (集中密度) があるので **一般には不可能**と予測 | Phase 3 着手前に 1 度だけ verbatim 再調査 (loogle `Integrable, Real.negMulLog`)。出なければ (a)/(c) へ |
| **(c)** 壁補題 `heatFlowEntropyPower_continuousWithinAt_zero` の signature に端点専用 hyp 追加 | 補題引数に `(hX_ent : Integrable (negMulLog pX) volume)` | OK (precondition) だが (a) より局所的 (consumer が hyp を供給する義務) | (a) が構造変更で影響範囲大の場合の代替。consumer (R-5-c) が h(X) 有限を容易に供給できるなら (c) |

**判断軸 (まとめ)**: precondition 追加 (`Integrable (negMulLog pX)` = 入力密度の有限エントロピー
regularity) は honesty OK。**連続性結論を bundle するのは禁止** (load-bearing、tier 5)。
(b) を先に試し、不可なら (a) を第一候補 (consumer の probability density 性から自然)。(a) 採用時は
`IsDeBruijnRegularityHyp` の field 追加 = 全 consumer の供給義務が増えるので、既存 consumer が
全て satisfiable か Phase 3 着手前に確認 (判断ログ記録)。

## Phase 4 — 壁補題 closure / proof-done 結線 📋

- **入力**: Phase 1〜3 完了。
- **タスク**:
  - [ ] `heatFlowEntropyPower_continuousWithinAt_zero` の `sorry` を Phase 3-d の結果で置換、
    `@residual(wall:heatflow-continuity)` を削除 (genuine 0 sorry なら `@audit:ok` 候補)。
  - [ ] consumer `csiszarLogRatioGap_continuousWithinAt_zero` / `_antitoneOn_Ici_zero`
    (`EPIStamToBridge.lean`) の sorryAx が層1 補題 (`wall:approx-identity-L1`) 経由の transitive
    のみになることを `#print axioms` で機械確認。
  - [ ] `audit-tags.md` Wall name register を reconcile: `wall:heatflow-continuity` は
    「層2 genuine、残壁は `wall:approx-identity-L1` (近似単位元 L¹ 収束) に移送」と更新。
    `wall:approx-identity-L1` を Proposed → 正式 register に promote (loogle 0 件再確認)。
- **proof-done 判定**: 壁補題の `sorry` が genuine 0 になる条件 = Phase 1 (層1) が genuine 化
  されること。**Phase 1 が `sorry` のまま (`wall:approx-identity-L1`) でも、層2 (Phase 3) は
  genuine** なので、その状態では:
  - `heatFlowEntropyPower_continuousWithinAt_zero` の body 内 `sorry` は層1 補題呼出に置換され、
    own `@residual` は持たず、transitive sorry のみ (層1 補題が唯一の壁)。
  - consumer も transitive genuine 化 (own residual なし)。
  - **完全な proof-done (壁補題に `@audit:ok`)** は Phase 1 (層1 L¹ 収束) が genuine 化されて
    初めて成立。それまでは「壁 1 件 = `wall:approx-identity-L1` の sorry 1 本」に集約された
    surface-shrunk 状態 (= 中間 honest state、type-check done)。
- **依存**: Phase 1, 2, 3。
- **工数感**: 20〜30 行 (結線 + reconcile)。
- **撤退口**: Phase 1 が moonshot のまま残る場合、本 Phase は「surface shrink 完了
  (層2 genuine + 層1 壁集約)」で着地。完全 closure は層1 closure を待つ。

## 工数現実性 / 1-session 最小単位

在庫見積り 160〜315 行を Phase 別按分:

| Phase | 内容 | 工数 | genuine か | 1-session ship 可否 |
|---|---|---:|---|---|
| 0 | 列化ブリッジ API 確定 | 15〜30 | genuine | ✅ 単独可 |
| 1 | 層1 L¹ 収束 (支配項) | 80〜150 | sorry 候補 (moonshot) | △ signature park は可、本体は moonshot |
| 2 | UI/UT witness + plumbing | 45〜95 | 一部 sorry | △ |
| 3 | 層2 machinery | 50〜90 | **genuine** | ✅ Phase 0/1/2 の sorry park 後なら |
| 4 | closure / reconcile | 20〜30 | genuine | ✅ |

**先行 ship 可能な genuine 部分** (= 最小単位、優先順):

1. **Phase 0** (列化ブリッジ) — 完全 genuine、単独 ship 可。
2. **Phase 1 の signature park** — 層1 補題 `convDensityAdd_tendsto_L1_zero` を sorry +
   `@residual(wall:approx-identity-L1)` で立てるだけ (5〜10 行)。これで Phase 3 が呼べる構造になる。
3. **Phase 3 (層2 machinery) を genuine 化** — Phase 1 が park 済なら、層2 全体 (列化 + Vitali +
   L¹→積分 + exp) を **genuine に閉じ**、壁補題の sorry を層1 補題呼出に置換。
   → **この 3 つで surface shrink が完了** (層2 genuine、壁が `wall:approx-identity-L1` 1 本に縮小)。
   = 1-session で着地可能な最小有意単位 (落とし穴2 が (b) で解ければ。(a)/(c) なら signature 変更
   + audit 1 件追加で +1 turn)。

層1 本体 (Phase 1 の 80〜150 行) と UI/UT 直接構成 (Phase 2) は次セッション以降の moonshot。

## 撤退ライン (発火条件具体)

1. **層1 L¹ 収束が `volume` 上 L¹+2次モーメントだけから原理的に出ない (反例で偽) と判明**
   → ありえない (近似単位元 L¹ 収束は標準事実、正則性は十分)。仮に Phase 1 着手で
   `convDensityAdd` 特有の障害が判明したら、`@residual(wall:approx-identity-L1)` 維持で
   Mathlib PR ルート (真 moonshot)。**発火条件**: Phase 1 で連続関数 L¹ 稠密 + translation
   continuity の組上げが `gaussianPDF` の non-compact-support で破綻すると確認。

2. **UI/UT witness が `pX_mom` (有限2次モーメント) だけからは出ない (反例で偽)**
   → 仮説強化 (落とし穴2 (a)、precondition 追加)。**発火条件**: Phase 2 で `UnifTight` の tail
   評価が `pX_mom` で閉じず、`negMulLog f_t` の負部 (`x>1`) tail が一様制御できないと確認。
   この場合 `IsDeBruijnRegularityHyp` に regularity field 追加 (negMulLog 一様可積分性 or
   entropy 有限性、**precondition** — load-bearing 化禁止)。signature 変更 → 独立 honesty audit。

3. **落とし穴2 が precondition 追加でも解けない**
   → 真 moonshot (Mathlib PR で近似単位元 L¹ 収束 + Vitali 一般化)。**発火条件**: (a)(b)(c)
   全て不可 (consumer が h(X) 有限を供給できず、`pX_mom` から導出も不可)。現時点では (a) で
   解ける見込みが高い (consumer は全て probability density 由来)。

各撤退とも **仮説束化禁止** (連続性結論 / L¹ 収束 / UI を `*Hypothesis` predicate に bundle しない)。
撤退は `sorry` + `@residual` (wall or plan) のみ。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(起草時、2026-06-04) GATE NO-GO 想定の修正**: 親 file header GATE verdict (2026-06-03) は
   「無限測度 `volume` で Vitali 不可」を NO-GO 根拠の一部としていたが、orchestrator が
   `tendsto_Lp_of_tendsto_ae` (UnifTight.lean:329) の signature を verbatim 確認し
   `[IsFiniteMeasure]` 非要求と判明。**machinery は `volume` で通る**。壁は machinery でなく
   入力側 (層1 L¹ 収束 + UI/UT) に局在。本 plan はこの修正を前提に層2 を genuine 化する設計。

2. **(起草時) FTC ショートカット否定の継承**: 親 Route B B-crux で確定。
   `IsDeBruijnPathRegular.cont` (`FisherInfoV2DeBruijn.lean:340`) が `Icc 0 T` 端点込み連続性を
   内包するため、de Bruijn 積分恒等式で端点連続性を出すのは循環。本 plan は積分恒等式ルートを
   採らず、密度レベル L¹ 強収束 (ルートA) で attack する。

3. **(起草時) 列化ブリッジの API 確定**: 落とし穴1 (連続版 → 列版ブリッジ) は
   `Filter.tendsto_iff_seq_tendsto` (`CountablyGenerated.lean:97`、orchestrator verbatim 確認) で
   解決。`𝓝[Ioi 0] 0` の `IsCountablyGenerated` instance 確認を Phase 0 のタスクに明示
   (ℝ 第一可算で存在見込み)。「自明」で流さない。
