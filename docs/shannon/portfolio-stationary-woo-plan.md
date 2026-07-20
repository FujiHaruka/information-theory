# Portfolio: stationary market W_∞ AEP (CT 16.5.1 完全形) サブ計画

> **Parent**: [`portfolio-operational-plan.md`](portfolio-operational-plan.md) — Leg B 完全形 (deferral 分離)

Cover–Thomas *Elements of Information Theory* 2nd ed **§16.5 "Investment in Stationary Markets" Thm 16.5.1**
の完全形を standard B (0 sorry / 0 @residual / sorryAx-free / 独立 `@audit:ok`) まで形式化する。親 Leg B は
**fixed-b core** (固定 rebalance portfolio の成長率収束 + KT dominance) を proof-done 済。本計画は残る
**log-optimal `W_∞` AEP** = 因果 log-optimal 戦略の富の成長率が無限過去条件付き成長率 `W_∞` に収束する部分を負う。

**現状 = framing fork 解決 → (B) Route M (growing-memory `S*_n` 逐語) 採択。R3-M 全段 (upper / lower / sandwich)
proof-done — CT 16.5.1 本体 headline `growingMemory_logWealth_tendsto_condOptGrowthInfty` が着地
(再検証: `#print axioms growingMemory_logWealth_tendsto_condOptGrowthInfty` が sorryAx-free)。crux succ は (b)
hybrid coherence 仮説で closure、両 gate PASS。残る唯一の未完 = R3-a (coherence 仮説の具体
pastFiltration+shift discharge、壁でない plumbing) + R4 (配線)** (Route M 群は
`Portfolio/StationaryWinftyAEP.lean` に分離、現 1031 行 / 0 sorry、fixed-b core は `StationaryWinfty.lean`)。
本計画は scope 境界・要件・進捗・壁リスクの記録。

## 進捗 — 🚧 R3-M 全段 proof-done (CT 16.5.1 本体 headline 着地)。残 = R3-a coherence discharge + R4 配線

- [ ] M0 在庫 — real-valued 条件付き growth / 可測選択 / Algoet–Cover sandwich の Mathlib / in-project 資産確定 📋
- [x] R1 — 条件付き log-optimal portfolio の可測選択 ✅ proof-done — `exists_measurable_argmax_on_stdSimplex` (`@audit:ok` sorryAx-free)
- [x] R2 — 条件付き成長率の単調収束 `W*_k ↑ W_∞` ✅ proof-done — `condOptGrowth_monotone` / `condOptGrowth_bddAbove` + 選択補題 `exists_condLogOptimalSeq` + headline `exists_condOptGrowth_tendsto_condOptGrowthInfty` すべて `@audit:ok` sorryAx-free。選択補題は `condExpKernel` (正則条件付き分布 / disintegration) 経由で closure — R1 gateway を ambient=`ℱ k` に instantiate + crux self-build `condExpKernel_ae_const` (ℱk-可測関数は κ_ω 下 a.e. 定数) + pull-out `condExp_causalLogReturn_eq`
- [x] R3 (Route T 踏み台) — real-valued SMB 級 AEP: ✅ **fixed-stationary W_∞ AEP proof-done + 両 gate PASS** — 積分恒等式 `condOptGrowthInfty_eq_integral_infPast` (`:807`) + bstarInf 存在 `exists_infPast_condLogOptimal` (`:965`) + headline `stationaryInfPast_logOptimal_growth_tendsto_condOptGrowthInfty` (`:990`) すべて `@audit:ok` sorryAx-free。Route T は固定 bstarInf の漸近最適性 companion ⟹ **(B) 採択後は踏み台**として残置し Route M の下界/極限同定に再利用 (恒等式で W_∞ 同定)
- [x] R3-M gateway — 加法→乗法変換 crux `condKuhnTucker_infPast` (`:1089`) ✅ **非壁確定 proof-done sorryAx-free @audit:ok** — R2 加法 dominance を wealth-ratio supermartingale が要する乗法 one-step 上界 `μ[(∑c·X)/(∑bstarInf·X)|⨆ℱ] ≤ᵐ 1` に変換。凸摂動一次条件 + setIntegral DCT で closure (κ_ω 還元不要)。補助 3 本 (`log_slope_tendsto_nhdsWithin`:1021 / `log_slope_bounds`:1036 / `condExp_nonpos_of_forall_setIntegral_nonpos`:1057) とも @audit:ok
- [x] R3-M-upper — growing-memory 上界 ✅ **proof-done** (`growingMemory_eventually_le_condOptGrowthInfty` `:796`、eventual-bound 形)。crux `wealthRatioProcess_lintegral_le_one` (`:244`、`∫⁻ M_n ≤ 1`) を **(b) hybrid ルート** (coherence 仮説 `hcoh` = measurability-only precondition、σ-代数 `(⨆ℱ).comap T^{k+1}` 固定) で succ closure。Markov+BC 骨格は一般補題 `logAvg_eventually_le_of_lintegral_le_one` (`:424`) に抽出 (lower も consume)。両 gate PASS (commit `8d282d2d`/`3f89c71a`)
- [x] R3-M-lower — 固定K/growing wealth-ratio supermartingale 下界 ✅ **proof-done** (`growingMemory_eventually_ge_condOptGrowthInfty` `:867`、eventual-bound 形)。tail-from-K supermmartingale `N_n^{(K)} = ∏_{i=K}^{n} (bstar_K·X_i)/(bstar_i·X_i)` + stagewise KT (`stagewise_condKuhnTucker` `:599`) + crux `∫⁻ N ≤ 1` (`lowerRatioProcess_lintegral_le_one` `:635`) を tower で closure、sup_K は R2 `exists_condOptGrowth_tendsto_condOptGrowthInfty`。lower coherence `hcoh_inf` (`(ℱ(k+1)).comap T^{k+1}`、upper より強い・coarser) = measurability-only。両 gate PASS (commit `9b5c1d3f`/`fac84779`)
- [x] R3-M-sandwich — upper+lower を組んで直接 `Tendsto gMLA (𝓝 W_∞)` ✅ **proof-done = CT 16.5.1 本体** (`growingMemory_logWealth_tendsto_condOptGrowthInfty` `:982`、`Metric.tendsto_atTop`)。3 headline すべて honesty-auditor 機械確認で load-bearing hyp なし (再検証: `#print axioms growingMemory_logWealth_tendsto_condOptGrowthInfty`)
- [ ] R3-a — 抽象 ℱ を具体 `pastFiltration`+shift で instantiate 📋 **shared bottleneck** — upper `hcoh` (`(⨆ℱ).comap T^{k+1}`) と lower `hcoh_inf` (`(ℱ(k+1)).comap T^{k+1}`、coarser・より強い) の **両方**を discharge。lower の強い need に合わせて設計 (upper 専用に作って lower で再 open しない)。壁でない plumbing (pastFiltration/shiftZ 既存)
- [ ] R4 — growing-memory headline 命名 (`@[entry_point]`) + 配線 (README/roadmap/facts) + 独立監査 📋

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
Tikhonov 狭義凹正則化。

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
  `ℱ : Filtration ℕ m0`** でパラメータ化 (判断ログ 1)。⟹ R3/R4 は `ℱ` の具体化を **新規 obligation** として負う。

### R3 — real-valued SMB 級 AEP ✅ Route M (growing-memory) 全段 proof-done = CT 16.5.1 本体着地 (proof-log: yes)

`(1/n) log S*_n → W_∞`。**(B) Route M (growing-memory `S*_n` 逐語) 採択** (判断ログ 2)。Route T (固定 bstarInf の
fixed-stationary AEP) は sandwich を回避して proof-done 済 ⟹ **踏み台**として残置し、Route M の下界/極限同定に再利用。

**Route T 着地 (踏み台、両 gate PASS、commit `3312d1fb` / `9a95fd95` / `da7370c1`)** — 3 decl は proof-done のまま:

- **`condOptGrowthInfty_eq_integral_infPast` (`StationaryWinfty.lean:807`、@audit:ok sorryAx-free)** = 積分恒等式
  `∫ causalLogReturn X bstarInf dμ = condOptGrowthInfty μ X bstar` (Lévy upward `Integrable.tendsto_ae_condExp` +
  DCT)。**Route M で W_∞ を同定する道具**として再利用 (下記 R3-M-upper)。
- **`exists_infPast_condLogOptimal` (`:965`、@audit:ok sorryAx-free)** = bstarInf 存在 (R2 の
  `exists_condLogOptimalSeq` を定数 filtration `Filtration.const ℕ (⨆ j, ℱ j)` に instantiate)。
- **`stationaryInfPast_logOptimal_growth_tendsto_condOptGrowthInfty` (`:990`、@audit:ok sorryAx-free)** = 固定定常
  AEP (Birkhoff + 上記恒等式 rewrite、dominance を内部 discharge した無条件-modulo-regularity 形)。`@[entry_point]`
  未付与 = growing-memory headline (R4) が本命ゆえ。

#### (B) Route M (growing-memory `S*_n` 逐語) 採択 + gateway

ユーザーが (B) を選択 (判断ログ 2)。追う対象は CT 16.5.1 の literal な growing-memory 富 `S*_n` = 各時刻 i で
i-past 最適 `bstar_i` を使う因果戦略 (SMB `shannon_mcmillan_breiman_of_sandwich` の growing-block + Algoet–Cover
sandwich 前例と整合)。gateway `condKuhnTucker_infPast` (`StationaryWinfty.lean:1089`) が R2 の**加法的** dominance を
wealth-ratio supermartingale が要する**乗法的** one-step 上界 `μ[(∑ c·X)/(∑ bstarInf·X) | ⨆ℱ] ≤ᵐ 1` に変換
(凸摂動一次条件 + setIntegral DCT)、R3-M-upper/lower が consume。wealth 定義 `growingMemoryLogAvg` は **抽象
フィルトレーション ℱ + 保測 T + coherence 仮説**でパラメータ化 (具体 pastFiltration+shift instantiate = R3-a、
判断ログ 1 と同型)。

**R3-M 全段 proof-done** (`StationaryWinftyAEP.lean`、1031 行 / 0 sorry):

- **R3-M-upper ✅**: `condKuhnTucker_infPast` から wealth-ratio supermartingale `M_n = ∏ (bstarInf·X)/(bstar_i·X)`
  を組み、crux `∫⁻ M_n ≤ 1` (`wealthRatioProcess_lintegral_le_one` `:244`) を base=KT + n-induction tower で
  closure。Markov + Borel–Cantelli + majorant `2log(n+1)/(n+1)→0` で eventual-bound
  `∀ε>0 ∀ᶠ n, gMLA ≤ W_∞+ε` (`growingMemory_eventually_le_condOptGrowthInfty`、W_∞ 同定は Route T 恒等式
  `condOptGrowthInfty_eq_integral_infPast`)。**設計変更 (判断ログ 3)**: `Submartingale.ae_tendsto_limitProcess` 路は
  不採 (ℝ-limsup が `gMLA→−∞` 経路で junk `sInf ℝ = 0` を取り `W_∞<0` で `limsup ≤ W_∞` が false-as-stated)、
  eventual-bound 形は honest。**coherence**: crux succ の increment transport (KT の base=⨆ℱ 条件付けを時刻 k+1
  history に運ぶ) は **(b) hybrid** — coherence 仮説 `hcoh` (σ-代数 `(⨆ℱ).comap T^{k+1}` 上の adaptedness、
  measurability-only precondition・非 load-bearing) を crux/headline に持たせ R3-a で discharge。
- **R3-M-lower ✅ (旧設計 false → tail-from-K supermartingale に訂正)**: `birkhoff_ergodic_ae` を固定 K 戦略
  `bstar_K` に適用する **liminf 下界**。crux = **固定K/growing wealth-ratio supermartingale**
  `N_n^{(K)} = ∏_{i=K}^{n} (bstar_K·X_i)/(bstar_i·X_i)` (**tail は i=K から** — i<K は KT 不成立)。stagewise KT
  `condKuhnTucker_infPast` を `Filtration.const ℕ (ℱ i)` に instantiate (`hbstar_dom i` が dominance 供給、
  `stagewise_condKuhnTucker` `:599`)、crux `∫⁻ N ≤ 1` (`lowerRatioProcess_lintegral_le_one` `:635`) を tower で
  closure。分解 (固定K Birkhoff 平均 + head/(n+1) − logN/(n+1)) + sup_K (R2
  `exists_condOptGrowth_tendsto_condOptGrowthInfty`) で eventual-bound
  `∀ε>0 ∀ᶠ n, gMLA ≥ W_∞−ε` (`growingMemory_eventually_ge_condOptGrowthInfty`)。Markov+BC 骨格は upper と共有の
  一般補題 `logAvg_eventually_le_of_lintegral_le_one` (`:424`) に抽出。lower coherence `hcoh_inf` は upper の `hcoh`
  より **強い** (σ-代数 `(ℱ(k+1)).comap T^{k+1}` = coarser ⟹ measurability 主張が強い、honest)。
  **⚠️ 旧 plan の設計 (下記) は false-as-stated だった** — 「birkhoff を固定 k 戦略に適用 → liminf gMLA ≥ W*_k
  (growing ≥ 固定 k) → sup_k」の **「growing ≥ 固定 k」は pointwise 偽** (bstar_i は条件付き期待の log-optimal で
  pathwise return を最大化しない、proof-pivot-advisor + honesty-auditor 両指摘)。隠れた supermartingale 論法
  (tail-from-K) を要した (判断ログ参照)。
- **R3-M-sandwich ✅**: upper + lower の eventual 上下界を組んで **直接** `Tendsto gMLA (𝓝 W_∞)`
  (`growingMemory_logWealth_tendsto_condOptGrowthInfty`、`Metric.tendsto_atTop`) = **CT 16.5.1 本体**。ℝ-limsup
  coboundedness 経由不要。3 headline すべて sorryAx-free (再検証:
  `#print axioms growingMemory_logWealth_tendsto_condOptGrowthInfty`)、honesty-auditor が load-bearing hyp なし
  (`hcoh`/`hcoh_inf`/`hint_coord`/`hUB` はすべて regularity precondition) CONFIRMED、両 gate PASS。

### R3-a — 抽象 ℱ の具体化 = R3-M coherence 仮説の discharge (proof-log: no、shared bottleneck)

R3-M の唯一の未 discharge = coherence 仮説 2 本を具体 `pastFiltration`+shift で埋める plumbing:

- **upper `hcoh`** — `M_k` の `(⨆ℱ).comap T^{k+1}`-可測性 (成長史 adaptedness、finest)。
- **lower `hcoh_inf`** — `N_k^{(K)}` の `(ℱ(k+1)).comap T^{k+1}`-可測性 (**upper より強い** = σ-代数が coarser
  ⟹ measurability 主張が強い = **binding constraint**)。

⟹ **R3-a は lower の強い need に合わせて設計** — upper 専用に作って lower で再 open しない。手順:
`ℱ := pastFiltration` (`InformationTheory/Probability/TwoSidedExtension/Backward.lean:84`、`pastSigma_mono`:70) を
instantiate + `StandardBorelSpace.pi_countable` 発火 + `(μ, shiftZ, hT, hT_erg)` を仮説化 (`μZ` / `ergodic_shiftZ`
は Fintype 依存で再利用不可)。**着手前に**、growing shifted-stage 単調性
`(ℱ i).comap T^i ≤ (ℱ(n+1)).comap T^{n+1}` (i≤n) を `pastSigma_mono` (`Backward.lean:70`) に対し verify する
(coarser-σ 側の measurability が finer 版を含意することの根拠)。判断ログで「増加 past filtration は既存・cheap」と
確認済ゆえ from-scratch build しない (R4 で再見積しない)。両 coherence は measurability-only precondition で
`∫⁻ M_n ≤ 1` / `∫⁻ N ≤ 1` を含意せず (KT/transport 無しに bound 出ない) ⟹ 非 load-bearing、honest。

### R4 — growing-memory headline 命名 + 配線 + 独立監査 (proof-log: no)

R3-a discharge 後、CT 16.5.1 本体 headline `growingMemory_logWealth_tendsto_condOptGrowthInfty` を proof-done で
`@[entry_point]` 付与 + 配線。root import は既に登録済 (`InformationTheory.lean:312`) ⟹ **import 追加は不要**。残る
配線 = README (`docs/readme-theorems.txt` Ch.16) / roadmap (`docs/textbook-roadmap.md` Ch.16 行) / facts
(`portfolio-facts.md` に growing-memory 3 headline + Route M gateway の sorryAx-free 再検証コマンド)。独立
`honesty-auditor` + `style-auditor` は Route T 3 decl / Route M gateway / R3-M upper・lower・sandwich で既に PASS。

**style flag (R3-M leg で発生、R4 or 完了時に判断)**:

- **file split = DEFER**: Route M 群は既に `StationaryWinftyAEP.lean` (現 1031 行、1500 cap 余裕) に分離済。更なる
  split は不要 (`>1400` 行で再検討)。**初回 cut が自然な単位** = condLExp pull-out helper 群の抽出 (`CondLExpPullOut`
   等の別 file)、これが重複 helper flag も同時解消する。**制約**: 共有 private 補助 (`market_pos` /
  `causalLogReturn` / `stdSimplex_component_le_one` — R3-M-upper で de-private 済) は file-scoped ゆえ、分割時に
  de-private (public 化) または複製が要る (CLAUDE.md「`private` は file-scoped」)。
- **upper crux 過剰 docstring = orchestrator 確認事項**: `wealthRatioProcess_lintegral_le_one` の crux docstring が
  過剰 ⟹ bare 化候補 (ただし honesty-relevant な prose は verbatim 保持)。style-auditor の process-vocabulary ban を
  適用する際、orchestrator が「削るのは dated 過程叙述のみ・reasoning は残す」を確認。

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
- **R3 real-valued AEP — Route T (踏み台)**: **CLOSED (not-a-wall)、fixed-stationary AEP proof-done**。R3 在庫が
  「解析の心臓・壁公算」とした pathwise 上界は、固定 bstarInf ルートでは condExp-martingale + DCT で閉じた。
- **R3 Route M (採択、growing-memory) — 全段 非壁確定・proof-done**: upper (wealth-ratio supermartingale +
  Markov/BC) / lower (tail-from-K supermartingale + Birkhoff + sup_K) / sandwich (直接 Tendsto) すべて
  proof-done sorryAx-free (再検証: `#print axioms growingMemory_logWealth_tendsto_condOptGrowthInfty`)。martingale-difference
  SLLN の Mathlib 不在は eventual-bound + Markov/BC 骨格 (`logAvg_eventually_le_of_lintegral_le_one`) で回避、
  supermartingale 収束層に genuine Mathlib gap は無し (壁 slug 新設不要)。coherence (shift-past) は wall でなく
  measurability-only の R3-a plumbing に落ちた。
- **総評**: R3-M 全段 (upper + lower + sandwich) 非壁確定・proof-done で **CT 16.5.1 本体 headline が着地**。残る
  唯一の未完 = R3-a (coherence 仮説の具体 pastFiltration+shift discharge、壁でない・既存資産) + R4 配線。壁 slug は
  本計画では 1 件も新設していない (R1/R2/Route T/Route M すべて not-a-wall で closure)。

## 撤退ライン

- **R3-a coherence discharge (唯一の active 残課題)**: 具体 `pastFiltration`+shift の instantiate で coherence
  `hcoh` / `hcoh_inf` の discharge が詰まった場合、その補題は signature を target 形のまま body を `sorry` +
  `@residual(plan:portfolio-stationary-woo-plan)` (slug = 本ファイル stem、整合)。**adaptedness / 可測性 / W_∞ を
  `*Hypothesis` predicate に抱えさせる load-bearing bundling は禁止** — retreat exit は `sorry` のみ。coherence が
  想定外に genuine Mathlib gap (past-σ の shift 整合が既存資産で埋まらない) を露呈したら analytic core を
  `sorry` + 新規 `@residual(wall:<name>)` で分離 (`docs/audit/audit-tags.md` register に追記)。ただし
  `pastFiltration` / `pastSigma_mono` / `shiftZ` は既に in-project で cheap ⟹ 壁公算は低い。

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

- **root**: `Portfolio/StationaryWinfty.lean` の import は既に `InformationTheory.lean:312` に登録済 ⟹ **追加不要**。
- **README / roadmap / facts**: `docs/readme-theorems.txt` Ch.16 節 / `docs/textbook-roadmap.md` Ch.16 行 /
  `docs/shannon/portfolio-facts.md` に growing-memory headline (R4 命名) + Route T 3 decl + Route M gateway の
  sorryAx-free 再検証コマンドを追記 (facts ledger 更新は R4 配線担当 / orchestrator の所掌、本 plan では machine
  fact を prose に cache しない)。
- **parent 同期**: 状態変化時は親 [`portfolio-operational-plan.md`](portfolio-operational-plan.md) の Leg B 完全形
  行を同期 (子が SoT、衝突時は親を子に合わせる)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除 (git が履歴)、active のみ残す。

1. **R2 は抽象 `Filtration ℕ m0` でパラメータ化 → R3-a discharge obligation (active、R3-a が参照)**: R2 は具体的な
   `T`/`X` から構築した market-past filtration ではなく **抽象な増加フィルトレーション `ℱ : Filtration ℕ m0`** 上で
   証明され、R3-M も同哲学で coherence 仮説をパラメータ化する。⟹ **R3-a が抽象 `ℱ` を具体 market-past filtration で
   instantiate + coherence を discharge する obligation を負う**。`pastFiltration : Filtration ℕ MeasurableSpace.pi`
   (`InformationTheory/Probability/TwoSidedExtension/Backward.lean:84`、`pastSigma_mono`:70) が増加 filtration を
   Fintype-free に既提供 ⟹ instantiate は cheap (ambient measure/shift のみ regularity 仮説で deferral)。R4 は
   from-scratch filtration build を再見積しないこと。
2. **(B) Route M (growing-memory `S*_n` 逐語) 採択 + Route T 踏み台 (active、route 選択)**: ユーザーが (B) を選択。
   Route T (固定 bstarInf の fixed-stationary AEP、3 decl proof-done @audit:ok) は **踏み台**として残置し、Route M の
   W_∞ 同定に再利用 (恒等式 `condOptGrowthInfty_eq_integral_infPast`)。Route M gateway `condKuhnTucker_infPast`
   (加法 dominance → 乗法 one-step 上界) 非壁確定。
3. **R3-M-upper: (b) hybrid coherence 確定 + crux succ closure 完了 + eventual-bound reframe + 両 gate PASS (active、
   決着、`8d282d2d`/`3f89c71a`)**: crux succ の advisor 再諮問で **(b) hybrid** 確定 — coherence 仮説 `hcoh`
   (σ-代数 `(⨆ℱ).comap T^{k+1}` 上の adaptedness、measurability-only precondition・非 load-bearing) を crux/headline に
   持たせ R3-a で discharge (R2 の抽象-parameterization と同型)。crux succ (増分 transport) closure 完了。**設計軸 =
   eventual-bound 形**: headline は `Filter.limsup ≤ W_∞` でなく `∀ε>0 ∀ᶠ n, gMLA ≤ W_∞+ε` — ℝ の `Filter.limsup`
   は `gMLA→−∞` 経路で junk (`sInf ℝ = 0`) を取り `W_∞<0` で false-as-stated。eventual 形は lower `∀ε>0 ∀ᶠ n,
   gMLA ≥ W_∞−ε` と組めば **直接 `Tendsto`** (limsup coboundedness 不要)。honesty-auditor が HONEST REFRAME (under-claim
   でない) + `hcoh` 非 load-bearing CONFIRMED。実装は `Submartingale.ae_tendsto_limitProcess` を不採、Markov+BC で isolate。
4. **R3-M-lower + sandwich proof-done + 旧 lower design が false + R3-a = shared bottleneck (active、決着 + 訂正、
   `9b5c1d3f`/`fac84779`)**: lower + sandwich が proof-done し **CT 16.5.1 本体 headline
   `growingMemory_logWealth_tendsto_condOptGrowthInfty` が着地** (再検証: `#print axioms` sorryAx-free)。**訂正**: 旧 plan
   の lower design 「birkhoff を固定 k 戦略に適用 → liminf gMLA ≥ W*_k (growing ≥ 固定 k) → sup_k」は **false-as-stated**
   — 「growing ≥ 固定 k」は pointwise 偽 (bstar_i は条件付き期待の log-optimal で pathwise return を最大化しない、
   proof-pivot-advisor + honesty-auditor 両指摘)。**tail-from-K supermartingale** `N_n^{(K)} = ∏_{i=K}^{n}
   (bstar_K·X_i)/(bstar_i·X_i)` (i<K は KT 不成立ゆえ i=K から) + stagewise KT + `∫⁻ N ≤ 1` tower + sup_K に書き換え
   (隠れた supermartingale 論法を要した)。**R3-a = shared bottleneck**: lower coherence `hcoh_inf` (σ-代数
   `(ℱ(k+1)).comap T^{k+1}` = coarser) は upper `hcoh` より **強い** ⟹ R3-a は lower の強い need に合わせて設計
   (upper 専用に作って lower で再 open しない)。**次アクション = R3-a (両 coherence discharge) → R4 配線**。
