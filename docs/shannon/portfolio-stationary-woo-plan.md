# Portfolio: stationary market W_∞ AEP (CT 16.5.1 完全形) サブ計画

> **Parent**: [`portfolio-operational-plan.md`](portfolio-operational-plan.md) — Leg B 完全形 (deferral 分離)

Cover–Thomas *Elements of Information Theory* 2nd ed **§16.5 "Investment in Stationary Markets" Thm 16.5.1**
の完全形を standard B (0 sorry / 0 @residual / sorryAx-free / 独立 `@audit:ok`) まで形式化する。親 Leg B は
**fixed-b core** (固定 rebalance portfolio の成長率収束 + KT dominance) を proof-done 済。本計画は残る
**log-optimal `W_∞` AEP** = 因果 log-optimal 戦略の富の成長率が無限過去条件付き成長率 `W_∞` に収束する部分を負う。

**現状 = framing fork 解決 → (B) Route M (growing-memory `S*_n` 逐語) 採択。R1+R2+R3(Route T = fixed-stationary
W_∞ AEP、踏み台) proof-done sorryAx-free + Route M gateway `condKuhnTucker_infPast` 非壁確定 proof-done
sorryAx-free @audit:ok。残 = R3-M 組立 (supermartingale limsup 上界 / Birkhoff liminf 下界 / sandwich) + R3-a
具体化 + R4 配線** (`Portfolio/StationaryWinfty.lean`、現 1255 行、捏造 statement 無し)。本計画は scope 境界・
要件・進捗・壁リスクの記録。

## 進捗 — 🚧 (B) Route M 採択。R1/R2/R3(Route T 踏み台)+Route M gateway proof-done、R3-M 組立 + R3-a + R4 残

- [ ] M0 在庫 — real-valued 条件付き growth / 可測選択 / Algoet–Cover sandwich の Mathlib / in-project 資産確定 📋
- [x] R1 — 条件付き log-optimal portfolio の可測選択 ✅ proof-done — `exists_measurable_argmax_on_stdSimplex` (`@audit:ok` sorryAx-free)
- [x] R2 — 条件付き成長率の単調収束 `W*_k ↑ W_∞` ✅ proof-done — `condOptGrowth_monotone` / `condOptGrowth_bddAbove` + 選択補題 `exists_condLogOptimalSeq` + headline `exists_condOptGrowth_tendsto_condOptGrowthInfty` すべて `@audit:ok` sorryAx-free。選択補題は `condExpKernel` (正則条件付き分布 / disintegration) 経由で closure — R1 gateway を ambient=`ℱ k` に instantiate + crux self-build `condExpKernel_ae_const` (ℱk-可測関数は κ_ω 下 a.e. 定数) + pull-out `condExp_causalLogReturn_eq`
- [x] R3 (Route T 踏み台) — real-valued SMB 級 AEP: ✅ **fixed-stationary W_∞ AEP proof-done + 両 gate PASS** — 積分恒等式 `condOptGrowthInfty_eq_integral_infPast` (`:807`) + bstarInf 存在 `exists_infPast_condLogOptimal` (`:965`) + headline `stationaryInfPast_logOptimal_growth_tendsto_condOptGrowthInfty` (`:990`) すべて `@audit:ok` sorryAx-free。Route T は固定 bstarInf の漸近最適性 companion ⟹ **(B) 採択後は踏み台**として残置し Route M の下界/極限同定に再利用 (恒等式で W_∞ 同定)
- [x] R3-M gateway — 加法→乗法変換 crux `condKuhnTucker_infPast` (`:1089`) ✅ **非壁確定 proof-done sorryAx-free @audit:ok** — R2 加法 dominance を wealth-ratio supermartingale が要する乗法 one-step 上界 `μ[(∑c·X)/(∑bstarInf·X)|⨆ℱ] ≤ᵐ 1` に変換。凸摂動一次条件 + setIntegral DCT で closure (κ_ω 還元不要)。補助 3 本 (`log_slope_tendsto_nhdsWithin`:1021 / `log_slope_bounds`:1036 / `condExp_nonpos_of_forall_setIntegral_nonpos`:1057) とも @audit:ok
- [~] R3-M-upper — growing-memory 上界 🚧 **構造 landed + honesty gate PASS** (`growingMemory_eventually_le_condOptGrowthInfty`、eventual-bound 形、`StationaryWinftyAEP.lean` へ split 中)。crux `wealthRatioProcess_lintegral_le_one` (`∫⁻ M_n ≤ 1`) のみ honest sorry (`@residual(plan:...)`) 残 → closure は SMB テンプレ `integral_MRatioLowerZ_le_one` 手法 (n-induction + `condExp_comp_measurePreserving` tower)。**設計変更 (判断ログ 5)**: `Submartingale.ae_tendsto_limitProcess` 路は不採 (ℝ-limsup junk)、Markov+Borel–Cantelli で isolate
- [ ] R3-M-lower — Birkhoff liminf 下界 (固定 k 戦略 → sup_k) 📋 **eventual-bound 形推奨** (`∀ε>0 ∀ᶠ n, gMLA ≥ W_∞−ε`、upper と組んで直接 Tendsto)
- [ ] R3-M-sandwich — eventual 上下界を組んで直接 `Tendsto gMLA (𝓝 W_∞)` (limsup coboundedness 経由不要) 📋
- [ ] R3-a — 抽象 ℱ を具体 `pastFiltration`+shift で instantiate 📋 (R4 plumbing)
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

### R3 — real-valued SMB 級 AEP 🚧 Route T 踏み台 proof-done + Route M gateway 非壁 + Route M 組立残 (proof-log: yes)

`(1/n) log S*_n → W_∞`。**(B) Route M (growing-memory `S*_n` 逐語) 採択** (判断ログ 4)。Route T (固定 bstarInf の
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

#### framing fork 解決 → (B) Route M (growing-memory `S*_n` 逐語) 採択

ユーザーが (B) を選択 (判断ログ 4)。追う対象は CT 16.5.1 の literal な growing-memory 富 `S*_n` = 各時刻 i で
i-past 最適 `bstar_i` を使う因果戦略。SMB `shannon_mcmillan_breiman_of_sandwich` (CT 16.8.1、
`McMillanBreiman.lean:88`) の growing-block + Algoet–Cover sandwich 前例と整合。

**Route M gateway 非壁確定 (commit `337ed270` → gates `1895ead4`)**: `condKuhnTucker_infPast`
(`StationaryWinfty.lean:1089`、@audit:ok sorryAx-free) が R2 の**加法的** dominance を、wealth-ratio
supermartingale が要する**乗法的** one-step 上界 `μ[(∑ c·X)/(∑ bstarInf·X) | ⨆ℱ] ≤ᵐ 1` に変換する crux。凸摂動の
一次条件 + setIntegral DCT で closure (κ_ω 還元不要)。補助 3 本 (`log_slope_tendsto_nhdsWithin`:1021 /
`log_slope_bounds`:1036 / `condExp_nonpos_of_forall_setIntegral_nonpos`:1057) とも @audit:ok。独立
honesty-auditor が hInf_dom=genuine input・hint_coord=regularity (bundling 無し) CONFIRMED、style PASS。⟹
**加法→乗法変換 crux = 非壁**、残リスクは supermartingale 組立の coherence (shift-past、下記) に絞られた。

**Route M 設計 (proof-pivot-advisor 確定)**: martingale sub-route は **(iii) Algoet–Cover sandwich 外枠 +
(i) wealth-ratio supermartingale を limsup エンジン**とする。martingale-difference SLLN は **Mathlib 不在** (実測、
route (ii) 却下)。wealth 定義 `growingMemoryLogAvg` は **抽象フィルトレーション ℱ + 保測 T + coherence 仮説**で
パラメータ化 (具体 pastFiltration+shift instantiate = R3-a は R4 に deferral、判断ログ 3 と同型)。

**R3-M 残り構造 (gateway 後の道筋)**:

- **R3-M-upper (次の一手、~150–250 行)**: `condKuhnTucker_infPast` から wealth-ratio supermartingale を組み
  `Submartingale.ae_tendsto_limitProcess` (`Mathlib/Probability/Martingale/Convergence.lean:209`、
  `[IsFiniteMeasure μ]`) で a.s. 収束 → `log(ratio)/n → 0` → `limsup growingMemoryLogAvg ≤ ∫ log(bstarInf·X) =
  condOptGrowthInfty` (Route T 恒等式 `condOptGrowthInfty_eq_integral_infPast` で W_∞ 同定)。**coherence の勘所**:
  KT は base 点で ⨆ℱ 条件付きだが supermartingale increment は時刻 i で history 𝒢_{i-1} 条件付き ⟹ shift-past
  coherence (抽象 𝒢-adapted 仮説 or 具体 pastFiltration+shift) が要る。詰まれば (b)-抽象 → (a)-具体に martingale
  sub-file だけ切替 (advisor 助言)。
- **R3-M-lower (~80–150 行)**: `birkhoff_ergodic_ae` (`BirkhoffErgodic.lean`) を固定 k 戦略
  `causalLogReturn X (bstar k)` に適用 → W*_k、`liminf growingMemoryLogAvg ≥ W*_k` (growing ≥ 固定 k) → sup_k で
  `≥ W_∞`。
- **R3-M-sandwich (~30 行)**: `tendsto_of_le_liminf_of_limsup_le` (`Topology/Order/LiminfLimsup.lean:306`) で close。

### R3-a — 抽象 ℱ の具体化 (proof-log: no、R4 plumbing)

`ℱ := pastFiltration` (`TwoSidedExtension/Backward.lean:84`、`pastSigma_mono`:70) を instantiate +
`StandardBorelSpace.pi_countable` 発火 + `(μ, shiftZ, hT, hT_erg)` を仮説化 (`μZ` / `ergodic_shiftZ` は Fintype
依存で再利用不可)。判断ログ 3 で「増加 past filtration は既存・cheap」と確認済ゆえ from-scratch build しない。

### R4 — growing-memory headline 命名 + 配線 + 独立監査 (proof-log: no)

R3-M 組立後に growing-memory headline を proof-done で `@[entry_point]` 付与 + 配線。root import は既に登録済
(`InformationTheory.lean:312`) ⟹ **import 追加は不要**。残る配線 = README (`docs/readme-theorems.txt` Ch.16) /
roadmap (`docs/textbook-roadmap.md` Ch.16 行) / facts (`portfolio-facts.md` に growing-memory headline + Route M
gateway の sorryAx-free 再検証コマンド)。独立 `honesty-auditor` + `style-auditor` は Route T 3 decl + Route M
gateway で既に PASS (`da7370c1` / `1895ead4`)。

**file 肥大化 flag**: `StationaryWinfty.lean` は現 1255 行 (1500 cap の 84%)。Route M 群 (supermartingale +
Birkhoff lower + sandwich、~260–430 行見込み) 追加で 1500 接近 ⟹ R4 で `StationaryWinftyAEP.lean` 等への分割候補。
**制約**: 共有 private 補助 (`market_pos` / `causalLogReturn` / `stdSimplex_component_le_one`) は file-scoped ゆえ、
分割時に de-private (public 化) または複製が要る (CLAUDE.md「`private` は file-scoped」)。style-auditor は 1500 超で
分割を flag するので、超過前に R4 で判断する。

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
- **R3 Route M (採択、growing-memory) — 加法→乗法変換 crux = 非壁確定**: R2 の**加法的** dominance を、
  wealth-ratio supermartingale が要する**乗法的** one-step 上界に変換する `condKuhnTucker_infPast` が凸摂動一次条件
  + setIntegral DCT で closure (proof-done sorryAx-free @audit:ok、壁でない)。**残リスクは supermartingale 組立の
  coherence (shift-past) 1 点に絞られた** — KT の base-point ⨆ℱ 条件付けと increment の時刻 i history 𝒢_{i-1}
  条件付けの整合。martingale-difference SLLN は Mathlib 不在 (実測) だが sandwich 外枠 + `limitProcess` 収束で回避
  (route (ii) 却下、advisor 確定) ⟹ 現時点で壁公算低 (加法→乗法の主難所を gateway が消化済)。coherence が genuine
  Mathlib gap を露呈したら `@residual(wall:<slug>)` + register 追記。
- **総評**: (B) Route M 採択。Route T 3 段 (R1 可測選択 + R2 単調収束 + R3 condExp 恒等式) は完成し踏み台として残る。
  Route M は gateway (加法→乗法変換) 非壁確定 ⟹ 残る未知は supermartingale 組立の shift-past coherence 1 点。

## 撤退ライン

- **R1/R2/R3 のいずれか**: 詰まった補題は signature を target 形のまま body を `sorry` +
  `@residual(plan:portfolio-stationary-woo-plan)` (slug = 本ファイル stem、整合)。**W_∞ / 可測選択 / 成長率極限を
  仮説で渡す load-bearing bundling は禁止** — retreat exit は `sorry` のみ。
- **R3-M supermartingale 組立 (採択路の残課題)**: shift-past coherence が詰まった場合、まず (b)-抽象仮説 →
  (a)-具体 pastFiltration+shift に martingale sub-file だけ切替 (advisor 助言)。それでも supermartingale a.s.
  収束が genuine Mathlib gap (real-valued SMB / Barron–Breiman 一般 log-ratio AEP) と確定したら、analytic core を
  `sorry` + 新規 `@residual(wall:<name>)` で分離 (`docs/audit/audit-tags.md` register に追記)、組立骨格 (sandwich の
  上下界を仮定した consumer) は救う。**加法→乗法変換 crux は gateway `condKuhnTucker_infPast` で消化済ゆえ、この
  撤退が発火するのは supermartingale 収束層のみ**。**積分核 / AEP 極限 / W_∞ を `*Hypothesis` predicate に抱えさせる
  形は禁止** — retreat exit は `sorry` のみ。

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
4. **R3 framing fork 解決 → (B) Route M (growing-memory `S*_n` 逐語) 採択 (active、route 選択、`1895ead4`)**:
   ユーザーが (B) を選択。Route T (固定 bstarInf の fixed-stationary AEP、3 decl proof-done @audit:ok) は
   **踏み台**として残置し、Route M の下界/極限同定に再利用 (恒等式 `condOptGrowthInfty_eq_integral_infPast` で W_∞
   同定)。**Route M gateway `condKuhnTucker_infPast` 非壁確定** (proof-done sorryAx-free @audit:ok、
   `StationaryWinfty.lean:1089`) — R2 の**加法的** dominance を wealth-ratio supermartingale が要する**乗法的**
   one-step 上界に変換する crux が凸摂動一次条件 + setIntegral DCT で closure (κ_ω 還元不要)。独立 honesty-auditor が
   hInf_dom=genuine input・hint_coord=regularity (bundling 無し) CONFIRMED。**次アクション = R3-M-upper**
   (supermartingale を組み limsup 上界)。残リスクは組立の shift-past coherence 1 点に絞られた (壁公算低)。

5. **R3-M-upper = eventual-bound 形 + Markov/BC で isolate (active、設計変更 + coherence 非壁確定、`0412ef5c`)**:
   headline `growingMemory_eventually_le_condOptGrowthInfty` は `Filter.limsup ≤ W_∞` でなく **eventual-bound 形**
   `∀ε>0 ∀ᶠ n, gMLA ≤ W_∞+ε`。理由: ℝ の `Filter.limsup` は `gMLA→−∞` 経路 (M_n 超指数減衰) で junk 値
   (`sInf ℝ = 0`) を取り、`W_∞<0` かつその経路で `limsup ≤ W_∞` が **false-as-stated**。eventual 形はその経路でも真で
   R3-M-lower の下界 `∀ε>0 ∀ᶠ n, gMLA ≥ W_∞−ε` と組めば **直接 `Tendsto gMLA (𝓝 W_∞)`** (limsup coboundedness 不要)。
   独立 honesty-auditor が **under-claim でなく HONEST REFRAME** (16.5.1 の genuine 結果に必要十分な upper 半分) CONFIRMED。
   実装は `Submartingale.ae_tendsto_limitProcess` 路 (submartingale 収束) を不採、**integral bound `E[M_n]≤1` → Markov +
   Borel–Cantelli → majorant `2log(n+1)/(n+1)→0`** に簡略化 (upcrossing 機構回避)。**coherence 非壁確定**: crux
   `wealthRatioProcess_lintegral_le_one` (`∫⁻ M_n ≤ 1`) の increment transport は in-project `condExp_comp_measurePreserving`
   (`TwoSidedExtension/CondExpMeasurePreserving.lean:39`) + SMB 同型テンプレ `integral_MRatioLowerZ_le_one`
   (`SMB/AlgoetCover/TwoSidedRatio.lean:1261`、0 sorry) が供給 = **壁でなく plumbing** (honesty-auditor 両資産実在確認)。
   crux は base=KT + n-induction tower で closure 予定 (file split 後、`StationaryWinftyAEP.lean`)。**次アクション =
   split + crux closure → R3-M-lower (eventual 下界) → sandwich (直接 Tendsto)**。
