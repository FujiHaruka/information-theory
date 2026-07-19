# Portfolio: stationary market W_∞ AEP (CT 16.5.1 完全形) サブ計画

> **Parent**: [`portfolio-operational-plan.md`](portfolio-operational-plan.md) — Leg B 完全形 (deferral 分離)

Cover–Thomas *Elements of Information Theory* 2nd ed **§16.5 "Investment in Stationary Markets" Thm 16.5.1**
の完全形を standard B (0 sorry / 0 @residual / sorryAx-free / 独立 `@audit:ok`) まで形式化する。親 Leg B は
**fixed-b core** (固定 rebalance portfolio の成長率収束 + KT dominance) を proof-done 済。本計画は残る
**log-optimal `W_∞` AEP** = 因果 log-optimal 戦略の富の成長率が無限過去条件付き成長率 `W_∞` に収束する部分を負う。

**現状 = R1+R2 proof-done (sorryAx-free)、R3–R4 残** (`Portfolio/StationaryWinfty.lean` に
対応コードあり、捏造 statement 無し)。本計画は scope 境界・要件・進捗・壁リスクの記録。

## 進捗 — 🚧 R1+R2 proof-done、R3–R4 残

- [ ] M0 在庫 — real-valued 条件付き growth / 可測選択 / Algoet–Cover sandwich の Mathlib / in-project 資産確定 📋
- [x] R1 — 条件付き log-optimal portfolio の可測選択 ✅ proof-done — `exists_measurable_argmax_on_stdSimplex` (`@audit:ok` sorryAx-free)
- [x] R2 — 条件付き成長率の単調収束 `W*_k ↑ W_∞` ✅ proof-done — `condOptGrowth_monotone` / `condOptGrowth_bddAbove` + 選択補題 `exists_condLogOptimalSeq` + headline `exists_condOptGrowth_tendsto_condOptGrowthInfty` すべて `@audit:ok` sorryAx-free。選択補題は `condExpKernel` (正則条件付き分布 / disintegration) 経由で closure — R1 gateway を ambient=`ℱ k` に instantiate + crux self-build `condExpKernel_ae_const` (ℱk-可測関数は κ_ω 下 a.e. 定数) + pull-out `condExp_causalLogReturn_eq`
- [ ] R3 — real-valued SMB 級 AEP `(1/n) log S*_n → W_∞` 📋 **最リスク・別 gateway で早期壁判定**
- [ ] R4 — 組立 (CT 16.5.1 headline) + 配線 + 独立監査 📋

## ゴール / Approach

**ゴール** — 定常エルゴード市場 `{X_i}` (price-relative `X_i : Ω → Fin m → ℝ`、shift `T`) に対し、各時刻で
無限過去の条件付き log-optimal portfolio を使う因果戦略の富 `S*_n` が

- 条件付き成長率の増加極限 `W_∞ := lim_k W*(X_0 | X_{-1}, …, X_{-k})` に対し
- `(1/n) log S*_n → W_∞` a.s. (+ 望ましくは L¹)

を満たすことを headline とする (CT 16.5.1)。fixed-b 版 (`seqLogWealth_div_tendsto_stationary`) は親 Leg B が所有。

**Approach — finite-alphabet SMB は lift 不可、sandwich *構造* のみ再利用**。CT 16.5.1 の証明は SMB (§16.8) と
同じ **Algoet–Cover sandwich** — k 次 Markov 近似の富の block 平均が liminf/limsup で真の `W_∞` を挟み込む —
を採る。in-project SMB 機構はこの sandwich を実装済だが **有限アルファベット専用**:

- `shannon_mcmillan_breiman` (`SMB/AlgoetCover/Liminf.lean:497`) と `shannon_mcmillan_breiman_of_sandwich`
  (`SMB/McMillanBreiman.lean:88`) はいずれも `[Fintype α] [DecidableEq α]` 前提、`blockLogAvg` / `entropyRate`
  は **pmf ベースの block 確率**依存。連続 price-relative の general-measure 市場に **decl はそのまま lift 不可**。
- 一方 sandwich の **論理骨格** (Birkhoff を k 次条件付き量に適用 → 単調収束で 2 境界を close) は市場でも同型。

⟹ 本計画は「finite SMB decl を再利用」ではなく「sandwich *パターン*を real-valued log-wealth 用に再構築」する。
3 部品:

1. **R1 可測選択**: 各条件付き法 (無限過去 σ-代数で条件付け) について、simplex 上の凹成長率
   `growthRate` の最大点 `b*` を **可測に選ぶ**。凹性 (`growthRate_concaveOn`、親 Basic) + compact simplex 上の
   最大点存在 (`IsCompact.exists_isMaxOn`) は在庫。**核 = 条件付け (ω / 条件付き法) への可測依存** = 可測 argmax
   (Kuratowski–Ryll-Nardzewski / measurable selection)。ここが本 family 初の新規機構。
2. **R2 単調収束**: 条件付き成長率 `W*(X_0 | X_{-1..−k})` は k 増加で単調非減少 (条件付けを増やすと growth 増、
   data-processing 型) かつ上に有界 ⟹ 増加極限 `W_∞` に収束 (単調収束)。real-valued 条件付き期待
   (`condexp`、Mathlib `MeasureTheory.condExp`) で `W*(·|·)` を定義し、単調性を conditional Jensen / KT で得る。
3. **R3 real-valued AEP**: `(1/n) log S*_n = (1/n) ∑_i log(b*_i · X_i)` が `W_∞` に収束。sandwich —
   k 次近似の下界 (`birkhoff_ergodic_ae` を k 次条件付き log-return に適用 → `W*(X_0|past_k)`) と上界 (真の
   log-optimal ≤ 各 k 近似 + R2) で `W_∞` を挟む。`birkhoff_ergodic_ae` (`BirkhoffErgodic.lean`) は市場でも
   適用可 (親 Leg B fixed-b が実証)。

**着手順 (gateway-first)**: R1 (可測選択 = 最新規、gateway) → R2 (条件付き単調性) → R3 (sandwich) → R4 (組立)。
R1 の可測 argmax が通れば残りは Birkhoff + 単調収束の既存テンプレ再利用に落ちる。R3 は独立 gateway atom で
「real-valued sandwich が Birkhoff で閉じるか」を早期に壁判定 (finite SMB の Algoet–Cover 補題群のうち
alphabet 非依存な骨格がどれだけ救えるかを実機確認)。

## Phase 詳細

### M0 在庫 (proof-log: no)

- [ ] `MeasureTheory.condExp` の real-valued 条件付き期待 API + `Filtration` / tail σ-代数の in-project 使用例確認。
- [ ] measurable selection: `MeasurableSet.exists_measurable_...` / `IsCompact.exists_isMaxOn` /
      Kuratowski–Ryll-Nardzewski 系の Mathlib 在庫を verbatim 署名 (型クラス前提込み) で確定 (loogle)。
- [ ] `birkhoff_ergodic_ae` (`BirkhoffErgodic.lean`) + `AlgoetCover/` の sandwich 補題群のうち **alphabet 非依存**
      に切り出せる骨格を洗い出す (どの補題が `[Fintype α]` に本質依存かを機械確認)。
- [ ] 親 Leg B `stationaryLogReturn` / fixed-b headline の再利用面を確定。

### R1 — 条件付き log-optimal portfolio の可測選択 ✅ proof-done (proof-log: yes、gateway atom)

**目標 (sketch、実装で確定)**: 無限過去で条件付けた法 `ρ_ω` について、`b* : Ω → (Fin m → ℝ)` を可測に選び
`b* ω ∈ stdSimplex ℝ (Fin m)` かつ `growthRate ρ_ω X (b* ω)` を最大化する。凹性 + compact 最大点存在は在庫、
核は **可測依存**。gateway 判定: 可測 argmax が Mathlib 資産 (measurable selection) で閉じるか、self-build 要か。

**着地**: gateway atom `exists_measurable_argmax_on_stdSimplex` (`StationaryWinfty.lean:197`) が sorryAx-free +
独立 `@audit:ok` + style PASS で closure。Carathéodory (可測 × 連続) + 凹の `F : Ω → (Fin m → ℝ) → ℝ` の
simplex 上 argmax を可測選択する一般形。追加 regularity 仮説 `hF_conc : ∀ ω, ConcaveOn ℝ (stdSimplex ℝ (Fin m))
(F ω)` + `[Nonempty (Fin m)]` は genuine precondition (m=0 で simplex 空 ⟹ 選択不能、非 load-bearing)。ルート =
Tikhonov 狭義凹正則化 (判断ログ 2 参照)。

### R2 — 条件付き成長率の単調収束 ✅ proof-done (proof-log: yes)

`W*(X_0 | X_{-1..−k})` を real-valued `condExp` で定義 → k 単調非減少 (条件付け増 ⟹ growth 増) + 上界
(無条件 `W*(X_0)` 以下でなく、`E[log ‖X_0‖]` 級の可積分性上界) ⟹ 単調収束で `W_∞`。single-letter 上界の
向き・可積分性前提を M0 honesty guard で実機確認 (coarse/fine ミスマッチ排除)。

**着地 (commit `36482092`、両 gate PASS)**:

- **defs**: `causalLogReturn` / `condOptGrowth` (`= ∫ causalLogReturn dμ`、スカラー `W*_k`) /
  `condOptGrowthInfty := ⨆ k, condOptGrowth` (`= W_∞`)。
- **CORE proof-done + sorryAx-free + `@audit:ok`** (独立 honesty audit): `condOptGrowth_monotone`
  (data-processing 核: `W*_k` は k 単調) + `condOptGrowth_bddAbove`。
- **R2 headline `exists_condOptGrowth_tendsto_condOptGrowthInfty` = honest REDUCTION**: body は sorry-free、
  仮説は market-regularity のみ (`hX` / `hpos` / `hint` / `hUB`)。monotone + bddAbove から
  `Tendsto condOptGrowth atTop (𝓝 condOptGrowthInfty)` を導く。下記 selection 補題 1 本にのみ条件付き。
  honesty audit が **load-bearing bundling でない**旨 CONFIRMED。
- **選択補題 `exists_condLogOptimalSeq` = closure 済** (`@audit:ok` sorryAx-free): 段階的な条件付き
  log-optimal 選択の存在 (可測・simplex 値・任意の ℱ_k-可測 simplex 競合に対する pointwise-a.e. 条件付き優越)。
  R1 gateway `exists_measurable_argmax_on_stdSimplex` を ambient=`ℱ k` に instantiate し、目的関数
  `condGrowthObjective ω b = ∫ log(∑ b_j X_j) d(condExpKernel μ (ℱ k) ω)` を good-set patch (κ_ω 可積分な co-null
  集合外で `else 0`) で everywhere 凹/連続化。crux self-build = `condExpKernel_ae_const` (ℱk-可測関数は κ_ω 下
  a.e. 定数、Mathlib kernel-properness 補題不在ゆえ countable-basis exhaustion で ~35 行自作) + pull-out
  `condExp_causalLogReturn_eq`。追加型クラス `[StandardBorelSpace Ω] [Nonempty Ω]` は condExpKernel 用の
  regularity (非 load-bearing、honesty-auditor 確認)。
- **アーキテクチャ**: R2 は具体的な market-past filtration ではなく **抽象な増加フィルトレーション
  `ℱ : Filtration ℕ m0`** でパラメータ化 (判断ログ 3)。⟹ R3/R4 は `ℱ` の具体化を **新規 obligation** として負う。

### R3 — real-valued SMB 級 AEP (proof-log: yes、独立 gateway)

`(1/n) log S*_n → W_∞` を Algoet–Cover sandwich で。下界 = `birkhoff_ergodic_ae` を k 次条件付き log-return に
適用、上界 = 真の log-optimal 富 ≤ k 次近似富 + R2。sandwich close = Mathlib `tendsto_of_le_liminf_of_limsup_le`。

**R3 在庫 (詳細 → `portfolio-winfty-inventory.md` "R3 inventory")、wall-risk = (b) 中程度 self-build、genuine gap なし**:

- **増加 filtration は in-project 既存** (判断ログ 3 の「新規・balloon」を覆す): `TwoSidedExtension/Backward.lean:84`
  `pastFiltration : Filtration ℕ MeasurableSpace.pi` が増加 (`pastSigma_mono`、`Backward.lean:70`)、`⨆ k =
  negPastSigma`。構造は **Fintype-free** ⟹ `α = Fin m → ℝ` に ~5 行で再述 or 直接再利用。R2 の `[StandardBorelSpace Ω]`
  も具体空間 `∀ _ : ℤ, (Fin m → ℝ)` で `StandardBorelSpace.pi_countable` 発火。**deferral 分は real-alphabet の
  ambient measure/shift のみ** = 親 Leg B 同様 `(μ, T, hT, hT_erg)` を regularity 仮説で受ける (theorem の核でない)。
- **下界 = 親 Leg B `seqLogWealth_div_tendsto_stationary` (`StationaryMarket.lean:66`) が 2 行テンプレ**。fixed-b →
  `bstar k` に一般化した新規 decl で `condOptGrowth k = W*_k` を得る。
- **最大の未知 = pathwise 上界 (独立 gateway atom)**: R2 は stage-wise **条件付き (in-expectation) dominance** のみ提供
  (`exists_condLogOptimalSeq` 3rd conjunct)。`limsup (1/n) log S*_n ≤ W*_k` へ変換するには **新規 wealth-ratio
  supermartingale + Borel–Cantelli** (SMB `MRatioUp_le_sq_eventually` の portfolio 版、finite-alphabet 版は lift 不可)。
  ~150–300 行見積。**gateway atom = `causalLogWealth_limsup_le_condOptGrowth` を solo `lean-implementer` に dispatch し
  Ville/Doob + Borel–Cantelli で閉じるか壁判定** (loogle-0 単独で壁宣言しない、gateway-atom-first)。Barron/Breiman
  一般 log-ratio AEP が要ると判明した場合のみ genuine wall (`@residual(wall:<slug>)` + audit-tags register)。

### R4 — 組立 + 配線 + 独立監査 (proof-log: no)

R1–R3 を CT 16.5.1 headline に組み、root import 登録 / README / roadmap / facts / 独立 `honesty-auditor` +
`style-auditor`。headline を `@[entry_point]` + proof-done で `@audit:ok`。

## 壁リスク評価

- **R1 可測選択**: **CLOSED (not-a-wall)**。Mathlib の一般 measurable-selection (KRN) は不在
  (`Mathlib/Probability/Decision/BayesEstimator.lean:46` の TODO が裏付け) だが、Tikhonov 正則化 self-build
  ~290 行で closure (当初見積 ~数十–150 行を上振れ、実測値)。撤退ライン不発。
- **R2 単調収束**: **CLOSED (not-a-wall)、fully proof-done**。`condOptGrowth_monotone` /
  `condOptGrowth_bddAbove` + headline reduction + 選択補題 `exists_condLogOptimalSeq` すべて proof-done
  sorryAx-free (@audit:ok)。予告どおり Mathlib 壁ではなく、条件付き選択リフトは `condExpKernel` (正則条件付き分布 /
  disintegration) で closure。crux (ℱk-可測 a.e.-定数 pull-out) のみ Mathlib 補題不在で ~35 行自作、他はすべて
  既存資産 (`condExp_ae_eq_integral_condExpKernel` / `integral_concaveOn_of_integrand_ae` /
  `continuousOn_of_dominated`)。
- **R3 real-valued AEP**: **最リスク、但し在庫後 wall-risk = (b) 中程度 self-build (genuine gap なし)**。
  finite SMB decl は lift 不可 (機械確認済) だが sandwich close (`tendsto_of_le_liminf_of_limsup_le`) + 下界
  (Birkhoff テンプレ) + 増加 filtration (`TwoSidedExtension/Backward.lean:84` 既存) は wired。**残る唯一の
  human-judgment 未知 = pathwise 上界** (`limsup ≤ W*_k`): wealth-ratio supermartingale + Borel–Cantelli の
  ~150–300 行 self-build、gateway atom `causalLogWealth_limsup_le_condOptGrowth` で早期壁判定。Barron/Breiman
  一般 log-ratio AEP が要ると判明した場合のみ新 wall slug。
- **総評**: real-valued SMB 級 AEP が本計画の重心。fixed-b (親 Leg B) が Birkhoff だけで閉じたのに対し、
  W_∞ は可測選択 + 単調収束 + sandwich の 3 段を要し格段に重い。

## 撤退ライン

- **R1/R2/R3 のいずれか**: 詰まった補題は signature を target 形のまま body を `sorry` +
  `@residual(plan:portfolio-stationary-woo-plan)` (slug = 本ファイル stem、整合)。**W_∞ / 可測選択 / 成長率極限を
  仮説で渡す load-bearing bundling は禁止** — retreat exit は `sorry` のみ。
- **R3 が genuine Mathlib gap (real-valued SMB) と確定した場合**: analytic core を `sorry` +
  新規 `@residual(wall:<name>)` で分離 (`docs/audit/audit-tags.md` register に追記)、組立骨格 (sandwich の
  上下界を仮定した consumer) は救う。**積分核 / AEP 極限を `*Hypothesis` predicate に抱えさせる形は禁止**。

## 正直性メモ (regularity precondition の性質)

追加仮説は **regularity precondition** に限る (load-bearing bundling 禁止):

- 定常エルゴード性 (`MeasurePreserving` / `Ergodic`) / 可積分性 (`Integrable (log ‖X_0‖)` 級) / 可測性:
  Birkhoff / condExp / 単調収束の必須前提、命題の核 (W_∞ 収束) を encode しない。
- simplex 帰属 / positivity (`0 < b·X`): 成長率解釈 + `Real.log` 定義域の correctness precondition。
- **`W_∞` の値そのもの・可測選択の存在・AEP 極限を仮説で渡す形は取らない** (それらは本計画が証明すべき核心)。

## DoD / gate

- **各 phase**: type-check done (`lake env lean` 0 error) で commit/push 可。proof-done (0 sorry ∧ 0 @residual、
  file 内) が genuine 完成。
- **headline `@[entry_point]`**: CT 16.5.1 完全形 headline を proof-done + 独立 `honesty-auditor` PASS で
  `@audit:ok`。
- **honesty gate**: 新規 `sorry` + `@residual` 導入 commit は独立 `honesty-auditor` 必須 (regularity precondition が
  load-bearing でない旨、可測選択/単調収束/AEP が仮説から semantic follow する旨も検査)。
- **style gate**: 新規 file の decl/docstring 追加で `style-auditor` を touched file に適用。

## 完了時の配線

- **root**: 新規 file (`Portfolio/StationaryWinfty.lean` 等、R4 で命名確定) の import を `InformationTheory.lean` に登録。
- **README / roadmap / facts**: `docs/readme-theorems.txt` Ch.16 節 / `docs/textbook-roadmap.md` Ch.16 行 /
  `docs/shannon/portfolio-facts.md` に headline の sorryAx-free 再検証コマンドを追記。
- **parent 同期**: 状態変化時は親 [`portfolio-operational-plan.md`](portfolio-operational-plan.md) の Leg B 完全形
  行を同期 (子が SoT、衝突時は親を子に合わせる)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除 (git が履歴)、active のみ残す。

1. **finite-alphabet SMB は lift 不可 (active)**: `shannon_mcmillan_breiman` / `shannon_mcmillan_breiman_of_sandwich`
   は `[Fintype α]` + pmf ベース `blockLogAvg` 依存を機械確認 (2026-07-19)。real-valued 市場では decl 再利用不可、
   Algoet–Cover sandwich の **論理骨格のみ**を再構築する方針。M0 で alphabet 非依存に救える補題を洗い出す。
2. **R1 可測 argmax = concave-regularization (Tikhonov) ルート採用 (active、設計ピボット)**: 在庫の当初 2C
   「least-index + compact-limit」可測 argmax レシピは closure しない — argmax タイ下で value-convergent だが
   point-convergent でなく、一般 measurable selection (KRN) は Mathlib 不在
   (`Mathlib/Probability/Decision/BayesEstimator.lean:46` の TODO が裏付け)。⟹ R1 は狭義凹正則化 (Tikhonov)
   ルートを採用: `F ω` に `-ε·qReg` を足して一意最大点を可測に取り ε↓0 の極限で argmax へ。前提 `ConcaveOn (F ω)`
   を要すが downstream で `growthRate_concaveOn` (親 Basic) が充足する regularity。
   `exists_measurable_argmax_on_stdSimplex` proof-done で着地。
3. **R2 は抽象 `Filtration ℕ m0` でパラメータ化 (active、設計ピボット、`36482092`)**: R2 は具体的な `T`/`X` から
   構築した market-past filtration ではなく、**抽象な増加フィルトレーション `ℱ : Filtration ℕ m0`** 上で
   monotone-convergence を証明する。⟹ **R3/R4 が抽象 `ℱ` を具体的 market-past filtration で instantiate する
   obligation を負う**。**訂正 (R3 在庫、2026-07-20)**: 当初「増加 past filtration は genuine 新規で two-sided 構成が
   balloon する」と見たが誤り — `TwoSidedExtension/Backward.lean:84` `pastFiltration : Filtration ℕ MeasurableSpace.pi`
   が既に増加 filtration を Fintype-free に提供 (`pastSigma_mono`)。instantiate は cheap (real-alphabet の ambient
   measure/shift のみ regularity 仮説で deferral、親 Leg B と同型)。R4 は from-scratch filtration build を再見積しないこと。
