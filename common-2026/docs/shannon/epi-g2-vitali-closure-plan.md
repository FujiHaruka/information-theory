# EPI G2: 3 Vitali witness 閉鎖 (UI / UT / ae) サブ計画

> **Parent**: [`epi-g2-layer2-moonshot-plan.md`](epi-g2-layer2-moonshot-plan.md) §Phase 1/2
> **対象壁**: `wall:approx-identity-L1` 配下の **3 Vitali witness sorry**
> (`InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean`)
> - witness ae: `negMulLog_convDensity_tendsto_ae` (`:179`)
> - witness UI: `negMulLog_convDensity_unifIntegrable` (`:144`)
> - witness UT: `negMulLog_convDensity_unifTight` (`:161`)
> - 層1 本体: `convDensityAdd_tendsto_L1_zero` (`EPIApproxIdentityL1.lean:165`、本体 sorry)
> **一次根拠**: [`epi-g2-vitali-witness-inventory.md`](epi-g2-vitali-witness-inventory.md)
> (3 witness の Mathlib 部品 + maxent 上界 + ae gap、verbatim signature 込み)

<!--
記法: 状態絵文字 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更(判断ログ参照)。
取り消し線 = 廃止 Phase (履歴のため残す)。判断ログ append-only。
-->

## 進捗

- [x] Phase A — ae witness ✅ **CLOSED 2026-06-04 (genuine 除去)**。full列 ae witness は層2 を部分列ルート
  (`tendsto_of_subseq_tendsto`) に書換えて **genuine に除去**。代替 = `negMulLog_convDensity_tendsto_ae_subseq`
  (`EPIVitaliAE.lean`、`@audit:ok`、sorryAx-free)。壁から消滅、surface shrink。
- [ ] Phase B — UT witness (`negMulLog_convDensity_unifTight`、`EPIVitaliUnifTight.lean:345`) 🚧 honesty fix 済
  (`hu_bdd`)。`convDensityAdd_second_moment` + `_unif_bdd` (n-一様 2次モーメント上界) は **genuine closure ✅**
  (`@audit:ok`)。残壁 = negMulLog tail bridge (`@residual(wall:approx-identity-L1)`)。
  **finding (2026-06-04)**: 一般 L¹ pX (Gauss より薄い裾) で `|log f_n| ≲ 1+x²` 不成立 → 2次モーメント
  route で tail を n-一様駆動不可。UI の de la VP core と **本質同一の wall** (将来 shared sorry 集約候補)。
- [ ] Phase C — UI witness (`negMulLog_convDensity_unifIntegrable`、`EPIVitaliUI.lean`) 🚧 framing 全 genuine。
  **Step 1-3 + moment integrability 全 genuine ✅** (`withDensity` 確率測度 framing + `differentialEntropy μ_n =
  ∫negMulLog f_n` 同定 + maxent 上界 + `convDensityAdd_gaussian_sq/id_integrable` 全 `@audit:ok`、独立監査 PASS)。
  主witness own body 0 sorry (de la VP core へ genuine 還元)。**plan-residual 全除去**。
  **残 = de la Vallée-Poussin core 1 本のみ** (`negMulLog_convDensity_indicatorTail_uniform`、`@residual(wall:
  approx-identity-L1)` = 真 moonshot、判断ログ 9)。`hpX_mass` precondition 追加済 (layer-2 から threading)。
- [x] Phase S — signature threading + 独立 honesty audit ✅ **部分 PASS 2026-06-04**。`hu_bdd : BddAbove (Set.range u)`
  を UT/UI witness に追加 (under-hypothesized 修正、`u→∞` で UnifTight/UnifIntegrable は genuine に偽)、
  layer-2 で `hv_bdd` を genuine 供給。独立 honesty-auditor が precondition (regularity、非 load-bearing) と PASS。
  (UI の `hpX_mass` 追加が確定したら再 audit 要)
- [x] 層1 — `convDensityAdd_tendsto_L1_zero` 本体 ✅ **CLOSED 2026-06-04** (`EPIApproxIdentityL1.lean`、genuine、sorryAx-free、独立 audit PASS。ae の足場 = 密度 a.e. 収束部分列の供給源)

**現状**: 層2 machinery `differentialEntropy_convDensity_integral_tendsto`
(`EPIG2HeatFlowContinuity.lean:206`、own-sorry 0、verbatim 確認済) は **3 witness の
transitive sorry のみ**で閉じる (層1 密度 L¹ 収束は CLOSED)。3 witness が genuine 化されれば
壁 `wall:approx-identity-L1` は完全 closure (EPI G2 端点連続性 done)。撤退ライン発火 no
(Vitali machinery `tendsto_Lp_of_tendsto_ae` は `[IsFiniteMeasure]` 非要求で `volume` で通る)。

proof-log: Phase A/B/C は yes (各 witness の genuine 化 / signature 変更を記録)。Phase S は yes。

## ゴール / Approach

**ゴール**: 3 Vitali witness の `sorry` を genuine 0 にし、壁を層1 `convDensityAdd_tendsto_L1_zero`
1 本に集約する。各 witness は層2 Vitali (`tendsto_Lp_of_tendsto_ae`, `UnifTight.lean:329`) の
入力 `hfg` (ae) / `hut` (UT) / `hui` (UI) を供給する。3 witness は load-bearing でなく、
genuine machinery への入力供給 (honesty: `*Hypothesis` predicate に核を bundle しない)。

### 全体形状 (3 witness を Vitali に供給する図)

```text
密度 f_{u n} := convDensityAdd pX (gaussianPDFReal 0 ⟨u n,_⟩) = pX ∗ g_{u n}   (u : ℕ→ℝ, u n>0)

  層1: t→0⁺ で convDensityAdd pX g_t → pX in L¹(volume)        ← convDensityAdd_tendsto_L1_zero
       │   (`@residual(wall:approx-identity-L1)`、別 dispatch 進行中)            真壁本体
       │   ⚠ 密度 L¹ 収束は negMulLog 非Lipschitz ゆえ negMulLog 合成の L¹ 収束を
       │     自動では与えない (在庫が Vitali を選んだ真因)。ae の足場のみ供給。
       ▼
  [Phase A] ae: ∀ᵐ x, negMulLog f_{u n} x → negMulLog (pX x)   ← witness ae (genuine 可能)
       │   層1 L¹ → tendstoInMeasure_of_tendsto_eLpNorm → exists_seq_tendsto_ae (部分列 ae)
       │   → Real.continuous_negMulLog 合成。 ⚠ full列 vs 部分列 gap (下記)
       │
  [Phase B] UT: UnifTight {negMulLog f_{u n}} 1 volume         ← witness UT (genuine 可能)
       │   f_{u n} 二次モーメント = ∫x²pX + u n·v_g (一様有界) → mul_meas_ge_le_lintegral
       │   (測度非依存、volume 直適用可) で density-weighted tail mass 一様小
       │
  [Phase C] UI: UnifIntegrable {negMulLog f_{u n}} 1 volume    ← witness UI (maxent 橋、最難)
       │   maxent 上界 differentialEntropy_le_gaussian_of_variance_le で ∫|negMulLog f_{u n}|
       │   一様有界 → unifIntegrable_of indicator-tail 一様小への de la Vallée-Poussin 橋
       │   ⚠ maxent は [IsProbabilityMeasure] 要求 → witness signature に X,Z,P precondition 追加
       ▼
  [既存 genuine] Vitali (tendsto_Lp_of_tendsto_ae) + L¹→積分 (tendsto_integral_of_L1')
       │   → ∫ negMulLog f_{u n} → ∫ negMulLog pX
       ▼
  壁補題 heatFlowEntropyPower_continuousWithinAt_zero が transitive に genuine 化
       (own body は既に genuine、`@residual(wall:approx-identity-L1)` 単独)
```

### 密度 L¹ 収束 (層1) との関係

層1 `convDensityAdd_tendsto_L1_zero` は **密度の L¹ 収束** (`eLpNorm (conv − pX) 1 volume → 0`)。
これは:
- **ae witness の足場になる** (`exists_seq_tendsto_ae` で部分列 ae、`negMulLog` 合成)。
- **UI/UT witness の足場には直接ならない** — `negMulLog` は非 Lipschitz (`x→0⁺` で導関数発散、
  `x→∞` で `-∞`) ゆえ、密度 L¹ 収束は `negMulLog` 合成後の L¹ 収束を自動では与えない。これが
  在庫が UI/UT を Vitali (UnifIntegrable/UnifTight) ルートで攻める設計を選んだ真因。UI/UT は
  maxent 上界 (UI) / 二次モーメント tail (UT) を独立に組む。

### maxent 上界の確率測度 framing (UI 専用)

maxent 上界 `differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:520`、
verbatim 確認済) は `[IsProbabilityMeasure μ]` + `μ ≪ volume` を要求し、`volume` 自体には適用不可。
適用先は **確率測度** `μ_n := f_{u n}·volume = P.map(X + √(u n)·Z)`。これを確率測度と見るには
`X,Z,P,v_Z,hZ_law` が要り、`pPath_eq_convDensityAdd` (`PerTime.lean:215`、`@audit:ok`、v_Z 一般化済、
verbatim 確認済) で `(P.map(X+√s·Z)).rnDeriv volume =ᵐ ofReal∘(convDensityAdd pX g_{s·v_Z})` の同定を使う。
**現 witness signature は `pX` のみ保有 (X,Z,P を持たない) → UI witness signature に
`X,Z,P,v_Z,hZ_law` precondition 追加が必要** (Phase S)。供給元は `IsHeatFlowEndpointRegular`
(`EPIG2:455`、全 field を保有、caller から threading 可、honesty OK)。

### ae gap の解決方針 (full列 vs 部分列)

`exists_seq_tendsto_ae` (`ConvergenceInMeasure.lean:277`、verbatim) は **部分列** `f (ns i)` の
ae 収束しか出さない (StrictMono ns)。一方 ae witness の現 signature は **full列** `n ↦ negMulLog f_{u n}`
の ae 収束を要求 (Vitali `hfg` も full列要求)。解決の 2 候補 (Phase A で判断):
- **(a) Gauss 核の Lebesgue 点 ae 点ごと収束を直接証明** — full列 ae が直接出る。
  `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable` (`:107`、bump 限定) の Besicovitch
  average (Lebesgue 微分) 論証を gaussianPDF (非 compact-support) で再現。工数大 (60〜120 行)。
- **(b) 層2 machinery 側を `TendstoInMeasure` 入力に書換** — 部分列 ae で足りる形に層2 を差替
  (`tendsto_Lp_of_tendstoInMeasure`、要存在確認)。層2 改変 (20〜40 行)。
- **第一候補 = (a)** (witness signature を保ち層2 genuine を保全)。(b) は層2 machinery (現 own-sorry 0)
  への侵襲を避けるため次善。判断は Phase A の冒頭タスクで verbatim 確認後に確定 (判断ログ)。

### honesty 境界 (常時、全 Phase)

- 3 witness (ae / UT / UI) / 層1 L¹ 収束を **`*Hypothesis` / `*Reduction` predicate に bundle して
  仮説で渡すのは禁止** (load-bearing、tier 5)。撤退は必ず `sorry` + `@residual(wall:approx-identity-L1)`。
- witness signature に追加してよいのは **precondition** (`X,Z,P,v_Z,hZ_law` の入力分布の素性、
  確率測度性 = regularity) のみ。**連続性 / UI / UT 結論を hyp に取らない** (循環)。判定軸 → 課題5。
- maxent 上界を「呼ぶ」のは bundling でない (`@entry_point` genuine 補題を precondition から genuine
  適用)。同様に `pPath_eq_convDensityAdd` (`@audit:ok`) を呼ぶのも genuine。

## Phase A — ae witness (`negMulLog_convDensity_tendsto_ae`) 📋

> **対象 sorry**: `EPIG2HeatFlowContinuity.lean:179`、現タグ `@residual(wall:approx-identity-L1)`。
> 難易度ランク (advisor): **最 tractable** (ae ≪ UT < UI)。

- **入力前提** (現 signature、verbatim):
  `{pX : ℝ → ℝ} (hpX_nn) (hpX_meas) (hpX_int) (hpX_mom) (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n)`
  `(hu_lim : Tendsto u atTop (𝓝[Set.Ioi 0] 0))`
- **出力結論型** (verbatim):
  ```lean
  ∀ᵐ x ∂volume,
    Tendsto (fun n =>
      Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x))
      atTop (𝓝 (Real.negMulLog (pX x)))
  ```
- **鍵 Mathlib lemma**:
  - `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` (`ConvergenceInMeasure.lean:463`) — L¹→測度収束。
  - `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae` (`:277`、verbatim 確認済) — 測度収束→**部分列** ae。
  - `Real.continuous_negMulLog` (`NegMulLog.lean:186`、`@[fun_prop]`) — `f_{u n} x → pX x` を合成。
  - (足場) 層1 `convDensityAdd_tendsto_L1_zero` (`EPIApproxIdentityL1.lean:165`、別 dispatch 進行中)。
- **タスク**:
  - [ ] full列 vs 部分列 gap の解決方針確定 (Approach「ae gap」(a)/(b))。Phase A 冒頭で
    `tendsto_Lp_of_tendstoInMeasure` の存在を loogle/rg 確認 ((b) 可否) + Besicovitch average の
    gaussianPDF 適用余地 verbatim 確認 ((a) 工数感)。
  - [ ] 第一候補 (a) で gaussianPDF の ae 点ごと収束を直接構成、または (b) で層2 書換 + witness を
    部分列 ae 形に signature 変更 (変更時 Phase S audit)。
  - [ ] `Real.continuous_negMulLog` 合成で `negMulLog` に持上げ。
- **工数感**: (a) 60〜120 行 / (b) 20〜40 行 (層2 書換) + witness signature 整合。
- **1-session ship**: △ (gap 解決方針による)。層1 が park 済なら部分列 ae までは genuine 化可能。
- **撤退口**: gap が (a)(b) いずれも当該 session で組めない → `sorry` + `@residual(wall:approx-identity-L1)`
  維持 (層1 と同壁集約)。**仮説束化禁止** (ae 収束を `*Hypothesis` predicate に bundle しない)。
- **closure 見込み判定**: **genuine 可能**。層1 (`convDensityAdd_tendsto_L1_zero`) が genuine 化されれば
  L¹→測度→部分列 ae は完全 genuine。full列 gap は signature 整合 (設計) であって真壁でない。

## Phase B — UT witness (`negMulLog_convDensity_unifTight`) 📋

> **対象 sorry**: `EPIG2HeatFlowContinuity.lean:161`、現タグ `@residual(wall:approx-identity-L1)`。
> 難易度ランク (advisor): **中** (ae < UT < UI)。

- **入力前提** (現 signature、verbatim):
  `{pX} (hpX_nn) (hpX_meas) (hpX_int) (hpX_mom) (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n)`。
  注: UT は `hu_lim` を持たない (tightness は各 n の tail 評価のみで、極限不要)。
- **出力結論型** (verbatim):
  ```lean
  UnifTight
    (fun n => fun x =>
      Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x))
    1 volume
  -- UnifTight 定義 (UnifTight.lean:59):
  --   ∀ ε>0, ∃ s, μ s ≠ ∞ ∧ ∀ i, eLpNorm (sᶜ.indicator (f i)) p μ ≤ ε
  ```
- **鍵 Mathlib lemma**:
  - `MeasureTheory.mul_meas_ge_le_lintegral` (`Lebesgue/Markov.lean:57`、verbatim、**測度非依存・volume OK**)
    — `ε·μ{ε≤f} ≤ ∫⁻ f`。`[IsFiniteMeasure]`/`[SigmaFinite]` 不要。これが `volume` 上 Chebyshev 回避の核。
  - **回避対象**: `meas_ge_le_variance_div_sq` (`Variance.lean:397`) は `[IsFiniteMeasure μ]` 要求で
    `volume` 直適用不可 (verbatim 確認済)。密度測度 `f_{u n}·volume` 経由か、上記 lintegral 版を使う。
  - `unifTight_finite` (`UnifTight.lean:191`、`[Finite ι]`) — 有限 prefix 処理 (補助)。
- **要自作補助補題** (in-tree 不在、verbatim 確認: `rg moment.*convDensityAdd` = 0):
  - [ ] `convDensityAdd_second_moment`: `∫ x²·(convDensityAdd pX g_t) = ∫ x²·pX + t·v_g`
    (独立和の分散加法性、`variance_fun_id_gaussianReal` `Real.lean:518` + 畳込み分散加法)。工数 10〜25 行。
- **タスク**:
  - [ ] `convDensityAdd_second_moment` を genuine 証明 (二次モーメント一様有界 `≤ ∫x²pX + (sup u n)·v_g`)。
  - [ ] `s = [-R, R]` (volume `2R < ∞`) を取り、`{|x|>R}` 上で `negMulLog f_{u n}` の Lp ノルムを
    density-weighted tail moment (`mul_meas_ge_le_lintegral` 適用) で一様小。
  - [ ] `negMulLog` の符号構造 (`x→∞` で `-∞`) ゆえ tail 上 `|negMulLog f_{u n}|` を `f_{u n}` の
    二次モーメント tail に結びつける評価 (UI と同根の障害、ただし UT は `sᶜ` 上 Lp 小だけで majorant 不要)。
- **工数感**: 30〜60 行 (二次モーメント補助 10〜25 + tail tightness 20〜35)。
- **1-session ship**: △ (二次モーメント補助 + tail 評価を 1 session で組めれば genuine)。
- **撤退口**: `pX_mom` だけから tail tightness が出ない (反例で偽) と判明 → 撤退ライン (後述)。
  それまでは `sorry` + `@residual(wall:approx-identity-L1)`。**仮説束化禁止**。
- **closure 見込み判定**: **genuine 可能** (moonshot でない)。`mul_meas_ge_le_lintegral` (測度非依存) +
  二次モーメント補助で `volume` 上に直接組める。`[IsProbabilityMeasure]` framing 不要 (UI と異なる)。

## Phase C — UI witness (`negMulLog_convDensity_unifIntegrable`) 📋

> **対象 sorry**: `EPIG2HeatFlowContinuity.lean:144`、現タグ `@residual(wall:approx-identity-L1)`。
> 難易度ランク (advisor): **最難** (de la Vallée-Poussin 橋 + maxent framing)。

- **入力前提** (現 signature、verbatim):
  `{pX} (hpX_nn) (hpX_meas) (hpX_int) (hpX_mom) (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n)`。
  **→ Phase S で `X,Z,P,v_Z,hZ_law` precondition 追加が必要** (maxent ルート、下記)。
- **出力結論型** (verbatim):
  ```lean
  UnifIntegrable
    (fun n => fun x =>
      Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x))
    1 volume
  ```
- **鍵 Mathlib lemma**:
  - `MeasureTheory.unifIntegrable_of` (`UniformIntegrable.lean:653`、verbatim、`[IsFiniteMeasure]` 不要)
    — **第一候補構成**。`{C ≤ ‖f i‖} 上 indicator Lp ノルムを `C` 一様小 (i 非依存)`。
  - `differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:520`、`@entry_point`、
    verbatim 確認済) — `∫ negMulLog f_{u n}` を二次モーメント一様に**下界**。
    **要求 (verbatim)**: `[IsProbabilityMeasure μ]`, `(hμ : μ ≪ volume)`, `m : ℝ`, `{v : ℝ≥0} (hv : v ≠ 0)`,
    `(h_mean : ∫ x ∂μ = m)`, `(h_var : ∫ (x-m)² ∂μ ≤ v)`, `(h_var_int : Integrable (fun x => (x-m)²) μ)`,
    `(h_ent_int : Integrable (fun x => negMulLog ((μ.rnDeriv volume x).toReal)) volume)`。
    結論: `differentialEntropy μ ≤ (1/2)·log(2πe·v)`。
  - `Real.negMulLog_le_one_sub_self` (`NegMulLog.lean:234`) — 正部 (`x≤1`) 上界 `≤ 1 - x`。
  - `convDensityAdd_negMulLog_integrable_pub` (`EPIG2:124`、`@audit:ok`) — 各 n で `h_ent_int` 供給。
  - `pPath_eq_convDensityAdd` (`PerTime.lean:215`、`@audit:ok`) — `f_{u n}·volume` の確率測度同定。
- **要自作 (in-tree/Mathlib 不在、最重要)**:
  - [ ] **de la Vallée-Poussin 橋**: `∫|negMulLog f_{u n}|` 一様有界 → `unifIntegrable_of` の
    indicator-tail 一様小。maxent (積分値下界) + `negMulLog_le_one_sub_self` (正部上界) で
    `∫|negMulLog f_{u n}|` 一様有界を作り、それを `{C ≤ ‖·‖}` indicator Lp ノルム一様小に変換。
    Mathlib に直接補題なし (loogle 確認推奨)。工数 40〜80 行 (maxent 足場あっても橋が残る)。
  - [ ] `μ_n := f_{u n}·volume` の確率測度性 / `≪ volume` 構築 (maxent 前提)。
    `pPath_eq_convDensityAdd` + `P.map(X+√s·Z)` が確率測度 (pushforward of probability)。工数 15〜30 行。
- **タスク**:
  - [ ] Phase S で UI witness に `X,Z,P,v_Z,hZ_law` precondition 追加 (maxent framing 用、signature 変更)。
  - [ ] `pPath_eq_convDensityAdd` で `μ_n = f_{u n}·volume` を確率測度と同定 (分散 `u n·v_Z`)。
  - [ ] maxent 上界で `∫ negMulLog f_{u n} ≥ -(1/2)log(2πe·V_n)` (V_n = `∫x²pX + u n·v_g`、
    `u n→0` で一様有界) → `∫ negMulLog f_{u n}` 一様下界。`negMulLog_le_one_sub_self` で正部上界。
  - [ ] de la Vallée-Poussin 橋で `∫|negMulLog f_{u n}|` 一様有界を indicator-tail 一様小に。
- **工数感**: 55〜110 行 (de la Vallée-Poussin 橋 40〜80 が支配項 + 確率測度 framing 15〜30)。
- **1-session ship**: ✗ (最難、橋 + framing で複数 session 見込み)。
- **撤退口** (= 撤退ライン 2 の境界、後述): de la Vallée-Poussin 橋が組めない、かつ
  `unifIntegrable_of_tendsto_Lp` (`:553`) 経由も `negMulLog f_{u n}` の L¹ 収束 (層1 と別物) が出ず
  循環で塞がる場合 → `sorry` + `@residual(wall:approx-identity-L1)` 維持 (park 継続)。
  precondition 追加 (`X,Z,P` / `hpX_ent` 型) は OK だが、それでも橋が出ない場合のみ真 moonshot
  (`wall:` 新設 + loogle 0 件再確認)。**仮説束化禁止**。
- **closure 見込み判定**: **genuine 可能だが最難** (真 moonshot ではない、maxent 上界が in-tree 既存で
  足場あり)。撤退ライン 2 に触れるが maxent 上界 + precondition 補強で踏み抜かない見込み。

## Phase S — signature 変更の threading + 独立 honesty audit 📋

> **対象**: Phase C (UI、確定) / 場合により Phase B (UT、maxent ルートを採る場合) の witness に
> precondition `X,Z,P,v_Z,hZ_law` を追加する。CLAUDE.md 起動条件「既存 declaration の signature を
> 変更して honesty 関連の意味が変わる」に該当 → 実装 session で **`honesty-auditor` を 1 件起動必須**。

### precondition 追加 = regularity であって load-bearing でない (判定軸)

追加する hyp は **すべて precondition (入力分布の素性 / 確率測度性 = regularity)**:
- `X,Z : Ω → ℝ`, `Measurable X`, `Measurable Z`, `IndepFun X Z P`, `P.map Z = gaussianReal 0 v_Z`,
  `pX` 密度 witness (+ 既存の `hpX_nn/meas/int/mass/mom`)。
- これらは `pPath_eq_convDensityAdd` (`@audit:ok`) を呼ぶための前提条件で、de Bruijn / EPI の正当な
  standing assumption (`X ⊥ Z`, `Z` Gaussian、Cover-Thomas 17.7.2)。
- **連続性 / UI / UT / 密度同定の核を hyp に取らない** (tier 5 禁止)。maxent 上界 / `pPath_eq_convDensityAdd`
  を「呼ぶ」のは bundling でない (genuine 補題の genuine 適用)。判定の一言 (CLAUDE.md):
  「その仮説は前提条件 (regularity) か、証明の核心 (load-bearing) か」→ **前者なので OK**。

### threading map (precondition の供給元)

| 段 | declaration | 供給する precondition |
|---|---|---|
| UI witness (要追加) | `negMulLog_convDensity_unifIntegrable` | `X,Z,P,v_Z,hZ_law,pX` 追加 |
| 層2 machinery | `differentialEntropy_convDensity_integral_tendsto` (`:206`) | UI witness を呼ぶ箇所 (`:253-254`) で precondition を渡す |
| 供給元 bundle | `IsHeatFlowEndpointRegular` (`EPIG2:455`、全 field 保有) | 壁補題 `heatFlowEntropyPower_continuousWithinAt_zero` (`:531`) が `h_endpt` で受取り、層2 / witness に threading |

> **注意 (verbatim 確認課題)**: 層2 machinery `differentialEntropy_convDensity_integral_tendsto`
> (`:206`) は現状 UI/UT/ae witness を **`pX` のみで呼んでいる** (`:253-261`)。UI witness に
> precondition を追加すると、層2 machinery の signature にも `X,Z,P,v_Z,hZ_law` を追加 (witness へ
> 横流し) するか、あるいは層2 を呼ぶ壁補題 helper `heatFlowDifferentialEntropy_continuousWithinAt_zero`
> (`:315`、これらを既に保有) から渡す形に整える必要がある。**この threading 方向は実装着手前に
> 層2 / helper / 壁補題の呼出鎖を verbatim 再確認してから確定** (CLAUDE.md「依存方向 / wrapper 呼出方向の
> verbatim 確認」)。`IsHeatFlowEndpointRegular` は既に全 field を保有するので caller 側の供給は揃う。

### honesty audit 起動

- UI (確定) / UT (maxent ルート採用時) の signature 変更を伴う実装 session で **`honesty-auditor`** を
  1 件起動。verify 対象: (i) 追加 field が全て precondition (load-bearing でない)、
  (ii) `@residual(wall:approx-identity-L1)` 分類の正しさ (genuine 化後の transitive 状態)、
  (iii) maxent / `pPath` 呼出が genuine (bundling でない)。
- **`@residual` 帰結**: 3 witness が genuine 化されると壁は層1 `convDensityAdd_tendsto_L1_zero` 1 本に
  集約。各 witness の `@residual(wall:approx-identity-L1)` は `@audit:ok` に変わる (genuine 後)。
  層1 が park のままでも、3 witness が genuine なら壁 surface は層1 1 本 (= surface shrink 最終形)。

## 層1 — `convDensityAdd_tendsto_L1_zero` 本体 📋

> **対象**: `EPIApproxIdentityL1.lean:165`、本体 `sorry` + `@residual(wall:approx-identity-L1)`。
> helper 4 本 (`eLpNorm_integral_le_lintegral` `:145` 等) は `@audit:ok` genuine。本体のみ残り
> (Gauss 集中 DCT)、**別 dispatch で進行中**。本 closure plan の責務外だが ae witness の足場として依存。

- **状態**: 本体 `sorry`。平行移動連続 + 連続 Minkowski + Gauss 集中 (二次モーメント DCT) の組上げ。
  loogle 裏取り: `convolution + eLpNorm (+Tendsto)` = Found 0 (Mathlib 近似単位元 L¹ 収束一般定理不在、
  honest wall)。gaussianPDF は compact support でない (ContDiffBump 不可) ため tail 評価が要る。
- **本 plan との関係**: ae witness (Phase A) の足場。層1 が genuine 化されれば Phase A の部分列 ae が
  完全 genuine。UI/UT (Phase B/C) は層1 に直接依存しない (maxent / 二次モーメント独立ルート)。

## 撤退ライン (発火条件具体)

親 plan [`epi-g2-layer2-moonshot-plan.md`](epi-g2-layer2-moonshot-plan.md)「撤退ライン」を継承。
本 closure plan の witness 別具体化:

1. **UT (Phase B) が `pX_mom` (有限2次モーメント) だけからは出ない (反例で偽)**
   → 仮説強化 (precondition 追加)。**発火条件**: Phase B で `mul_meas_ge_le_lintegral` + 二次モーメント
   tail が `negMulLog` の負部 (`x>1`) tail を一様制御できないと確認。この場合 witness に
   regularity precondition 追加 (`X,Z,P` 経由の確率測度 framing、または `hpX_ent` 型、**precondition** —
   load-bearing 化禁止)。signature 変更 → Phase S audit。**現時点では発火 no** (二次モーメント tail で
   genuine に出る見込み、in-tree maxent / Markov lintegral 在)。

2. **UI (Phase C) の de la Vallée-Poussin 橋が precondition 追加でも組めない**
   → 真 moonshot。**発火条件**: maxent 上界 (`X,Z,P` precondition 追加で適用可能になった後) でも
   `∫|negMulLog f_{u n}|` 一様有界 → indicator-tail 一様小の橋が書けず、かつ `unifIntegrable_of_tendsto_Lp`
   経由も循環で塞がる。この場合 UI 単独を `sorry` + `@residual(wall:approx-identity-L1)` で park。

3. **縮退状態 (honest resting state)**: UI が真 moonshot と確定した場合の honest 着地点 =
   「**ae (Phase A) + UT (Phase B) は genuine 化し、UI (Phase C) 単独を `wall:approx-identity-L1` で park**」。
   層1 本体 (別 dispatch) も park のままなら、壁 surface は「層1 1 本 + UI 1 本」(同壁 `approx-identity-L1`)。
   これは中間 honest state (type-check done)、surface shrink は ae/UT 分だけ進む。

各撤退とも **仮説束化禁止** (ae / UT / UI / L¹ 収束を `*Hypothesis` predicate に bundle しない、
load-bearing tier 5)。撤退は `sorry` + `@residual(wall:approx-identity-L1)` のみ。
maxent / `pPath_eq_convDensityAdd` 呼出 (genuine 補題の適用) は bundling でない。

## 工数現実性 / 1-session 最小単位

在庫見積り 105〜290 行 (witness 2 = UI の橋が支配項) を witness 別按分:

| Phase | witness | 工数 | genuine か | 1-session ship |
|---|---|---:|---|---|
| A | ae | (a) 60〜120 / (b) 20〜40 | genuine 可能 | △ (gap 方針による) |
| B | UT | 30〜60 | genuine 可能 | △ (二次モーメント補助 + tail) |
| C | UI | 55〜110 | genuine 可能 (最難) | ✗ (複数 session) |
| S | signature threading | 20〜40 | genuine | ✅ (UI/UT 後の結線) |

**最小有意単位 (優先順)**:
1. **Phase B (UT)** — `[IsProbabilityMeasure]` framing 不要、`mul_meas_ge_le_lintegral` (測度非依存) +
   二次モーメント補助で `volume` 上に直接組める。signature 変更不要なら独立 ship 可。
2. **Phase A (ae)** — gap 方針 (a)/(b) 確定後。層1 park 済なら部分列 ae まで genuine。
3. **Phase C (UI)** — 最難、Phase S の signature 変更 + de la Vallée-Poussin 橋。複数 session。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(起草、2026-06-04) 親 plan Phase 1/2 から 3 witness 精密設計を分離**: 親 plan が Phase 0-5 完結構造
   (層2 machinery genuine + 壁補題 closure + 密度同定 bridge genuine) に達したため、残る 3 Vitali witness
   を本 closure plan に切り出した。inventory `epi-g2-vitali-witness-inventory.md` の確定 positive 発見
   (maxent 上界 in-tree、`mul_meas_ge_le_lintegral` 測度非依存、ae full列 gap) を反映。難易度ランク
   (advisor): ae ≪ UT < UI。撤退ライン発火 no (Vitali machinery `tendsto_Lp_of_tendsto_ae` は
   `[IsFiniteMeasure]` 非要求)。

2. **(起草) maxent 上界の確率測度 framing が UI の最大 leverage と判定**: 実コード verbatim 確認
   (`differentialEntropy_le_gaussian_of_variance_le` `DifferentialEntropy.lean:520` の `[IsProbabilityMeasure μ]`
   + `μ ≪ volume` + `h_ent_int : Integrable (negMulLog ((μ.rnDeriv volume x).toReal)) volume` 要求)。
   `volume` 直適用不可 → `μ_n := f_{u n}·volume = P.map(X+√(u n)·Z)` を確率測度と見る視点が必須。
   `pPath_eq_convDensityAdd` (`PerTime.lean:215`、`@audit:ok`、v_Z 一般化済) で同定。**現 witness signature は
   `pX` のみ → UI witness に `X,Z,P,v_Z,hZ_law` precondition 追加が必要** (Phase S、honesty OK = regularity)。
   供給元 `IsHeatFlowEndpointRegular` (`EPIG2:455`) は全 field 保有 (verbatim 確認済)。

3. **(起草) UT は `volume` 上 Chebyshev 回避が可能と判定**: `meas_ge_le_variance_div_sq` (`Variance.lean:397`)
   は `[IsFiniteMeasure μ]` 要求で `volume` 不可 (verbatim 確認済)。代わりに `mul_meas_ge_le_lintegral`
   (`Lebesgue/Markov.lean:57`、測度非依存・volume OK) を density-weighted moment に使う。UT は UI と異なり
   `[IsProbabilityMeasure]` framing 不要 (signature 変更を避けられる可能性、Phase B で確定)。

4. **(起草) ae witness の full列 vs 部分列 gap を設計課題として明示**: `exists_seq_tendsto_ae`
   (`ConvergenceInMeasure.lean:277`、verbatim) は部分列 ae のみ。witness 現 signature は full列要求。
   解決 (a) Gauss 核 Lebesgue 点直接証明 (full列、工数大) / (b) 層2 を `TendstoInMeasure` 入力に書換
   (部分列で足りる、層2 改変)。第一候補 (a) (witness signature + 層2 genuine 保全)。Phase A 冒頭で
   `tendsto_Lp_of_tendstoInMeasure` 存在確認後に確定。

5. **(起草) 密度 L¹ 収束は UI/UT の足場にならないことを明示**: `negMulLog` 非 Lipschitz ゆえ、層1 の
   密度 L¹ 収束は `negMulLog` 合成後の L¹ 収束を自動では与えない (在庫が Vitali ルートを選んだ真因)。
   層1 は ae witness の足場 (部分列 ae) のみ供給。UI は maxent 上界、UT は二次モーメント tail を独立に組む。

6. **(2026-06-04 実装) Phase A ae witness を full列要求でなく部分列ルートで genuine 除去**: 当初 Phase A は
   full列 ae witness を park し、(a) Gauss 核 Lebesgue 点直接証明 or (b) 層2 を `TendstoInMeasure` 入力に
   書換、で解決する設計だった。実装で **Mathlib `tendsto_of_subseq_tendsto` (`CountablyGenerated.lean:138`)
   を層2 で直接使う第三の道** が判明: 層2 `differentialEntropy_convDensity_integral_tendsto` の Vitali
   ブロックを「各部分列 `ns` に対し更なる部分列 `ms` で `tendsto_Lp_of_tendsto_ae` を適用」に書換え、
   genuine 部分列補題 `negMulLog_convDensity_tendsto_ae_subseq` (`EPIVitaliAE.lean`、層1 → tendstoInMeasure →
   exists_seq_tendsto_ae → negMulLog 合成、`@audit:ok`、sorryAx-free) を供給源にした。これで full列 ae の
   gap (Mathlib 不在) を **完全に迂回**、ae witness は壁から消滅。Mathlib 自身の `tendsto_Lp_of_tendstoInMeasure`
   (`:357`) が同じ device を使っているのが手掛かり。層2 の signature/結論型は不変、own-sorry 0 維持。
   surface = ae/UT/UI 3 本 → UT/UI 2 本 (+ second_moment plan-class) に縮小。

9. **(2026-06-04 advisor NO-GO) de la VP wall は precondition 追加では閉じない = 真 moonshot 確定**:
   独立 proof-pivot-advisor が「`hpX_ent : Integrable (negMulLog pX)` (h(X)<∞) を UI/UT witness に追加すれば
   de la VP wall closure」案を **NO-GO** と判定。理由: maxent は `∫negMulLog f_n` の**符号付き上界のみ**供給、
   hpX_ent で下界を足しても (そもそも下界 = entropy 単調性 `h(X+√tZ) ≥ h(X)` は in-tree 不在、de Bruijn 積分
   自作要)、`∫negMulLog f_n` を一様 band に挟むだけで de la VP が要求する **superlinear-moment 一様有界**
   (`∫G(|negMulLog f_n|) ≤ M`、G superlinear) には届かない。**`∫|f|≤M` と `∫G(|f|)≤M` の区別が本質 gap、
   precondition では埋まらない**。**撤退ライン 2 (precondition で吸収) は誤り → 撤退ライン 3 (真 moonshot) が
   正しい着地**。在庫 `epi-g2-ui-bridge-inventory.md` の「maxent + 撤退ライン 2 で吸収」楽観は訂正対象。
   Scheffé 迂回 (UI 不要で L¹ 収束) も Mathlib に純粋 Scheffé 不在 (`tendsto_Lp_of_tendsto_ae` は UI+UT 必須)、
   UI/UT 迂回不能。**唯一の将来 genuine ルート** = de Bruijn identity 積分で `differentialEntropy(P.map(X+√sZ))`
   monotone を in-tree 化 (素材 `deBruijn_deriv_nonneg` `EPIStamDeBruijnConclusion.lean:132`) → maxent と組んで
   `∫|negMulLog f_n|` 一様 → さらに superlinear moment 自作 (100-200 行 + monotone 化が別 wall 級)。本 session 対象外。
   **honest 着地 = UI/UT を `@residual(wall:approx-identity-L1)` で park 継続** (独立 audit 済、仮説束化禁止)。

10. **(2026-06-04 三重独立追認 + de Bruijn route 訂正)**: orchestrator が fresh `mathlib-inventory` +
    fresh `proof-pivot-advisor` を**別角度で並列起動**し、判断ログ 9 の真 moonshot 判定を独立に再検証。
    両 agent とも tractable route の有無に明確に **NO** を回答 (在庫 `epi-g2-delavp-recheck-inventory.md` に
    記録)。loogle authoritative: `UnifIntegrable, ConvexOn` = Found 0、`negMulLog, Integrable` = Found 0、
    Mathlib 全体で "Vallée-Poussin"/"Scheff" = 0 file。**重要訂正**: 判断ログ 9 が「唯一の将来 genuine ルート」と
    した `deBruijn_deriv_nonneg` (`EPIStamDeBruijnConclusion.lean:132`) 積分 route は本壁に対して**カテゴリ違い
    (dead end)**。`:132` の結論は `0 ≤ (1/2)·fisherInfoOfDensityReal f` という **pointwise 導関数符号のみ**で、
    s 積分しても得られるのは entropy **値**の単調性 (`h(X)≤h(X+√tZ)`、しかも積分済み形は in-tree **0 hits**で
    ftc-2 + 端点連続性 + Fisher info 経路可積分という別 moonshot 前置が要る)。entropy 値の単調性は UnifTight が
    要求する「tail eLpNorm の n-一様 smallness」には変換できない。**よって de Bruijn route で本壁は閉じない** —
    将来ルートは de la VP 機構そのもの (superlinear-moment → UnifIntegrable 構築) を **in-tree 自作 or Mathlib
    upstream PR** するしかなく、これは複数 session の真 moonshot。**honest 着地 = park 継続を三重独立で確定**。
    付随発見 (両 agent 一致): 2 witness を 1 本の shared sorry 補題に集約すれば surface 2→1 縮小可。ただし
    inventory agent の caution「bookkeeping 集約と数学的可解性は別問題、集約前に集約命題の closability 再判定要」
    + 2 witness の結論型が genuinely 異なる (UI = 値しきい値 tail、UT = 空間 tail) ため、機械的集約は
    false-statement defect (tier 5) リスクあり → 急がず park のまま据え置き、集約は将来 closure 設計時に同時実施。

11. **(2026-06-04 サンドイッチ・ルート否定 → de la VP 機構自作 moonshot 起草)**: de la VP wall を UnifIntegrable
    迂回で閉じる**サンドイッチ分解** (上界 = `∫f log f` の L¹-LSC / 下界 = `h(f_n)≥h(pX)` 畳み込み非減少) を
    fresh inventory + fresh advisor で評価 (`docs/shannon/epi-g2-sandwich-inventory.md`)。結論 = **採用見送り**。
    (α) 上界: advisor 案の envelope `f log f ≥ f-1` は **R 上で非可積分** (`∫1=∞`、tail で `f_n log f_n-f_n+1→1`)
    のため Fatou (`lintegral_liminf_le`) が vacuous。厳密には (α) は `negMulLog` 負部 `(f log f)₋` の n-一様
    可積分 = **de la VP wall と数学的に同型**を再要求 → 壁を回避しない。(β) 下界: EPI 経由は `stamToEPIBridge_holds`
    (`plan:epi-stam-to-conclusion-plan`、open) + Stam line を transitive 消費、条件付き differential entropy は
    in-tree/Mathlib 完全不在。**3 逃げ道 (precondition / de Bruijn積分 / サンドイッチ) 全否定 → de la VP wall は
    genuine・不可避と確定**。**方針転換**: 近道探しを終え、de la Vallée-Poussin 機構**自作 moonshot** を起草
    (`docs/shannon/epi-g2-delavp-moonshot-plan.md`)。Phase 1 = de la VP 判定法の汎用補題化 (superlinear-moment →
    UnifIntegrable、`unifIntegrable_of` の上、tractable・genuine・再利用可) で不透明 UI/UT 壁を 1 点の解析ターゲット
    (superlinear moment 構成 = Phase 2、本物の moonshot 核) に絞り込む。

8. **(2026-06-04 実装) UI を真 moonshot から「橋 1 本 + plumbing」に縮小、EPIG2 own-file sorry-free 達成**:
   UI witness を `EPIVitaliUI.lean` に集約。確率測度 framing は **option (b) `withDensity` 直構成** (X,Z,P 不要、
   `pPath_eq_convDensityAdd` 迂回) で genuine 化: `μ_n := volume.withDensity (ofReal∘f_n)` が確率測度
   (`∫f_n=1` は in-tree `integral_convDensityAdd_gaussian_eq_one`) + `≪volume` + `rnDeriv_withDensity` で
   `differentialEntropy μ_n = ∫negMulLog f_n`。maxent `differentialEntropy_le_gaussian_of_variance_le`
   (`@entry_point`) 適用で `∫negMulLog f_n` 一様上界 (variance `≤ ∫x²f_n = ∫x²pX+t` を `convDensityAdd_second_moment`
   から、`hu_bdd` で n-一様)。UI 主witness は `unifIntegrable_of` で de la VP core (`indicatorTail_uniform`、parked)
   へ genuine 還元、own body 0 sorry。**残壁は de la VP core 1 本 (UI) + negMulLog tail 1 本 (UT、本質同一)**。
   UT/UI 集約で EPIG2 layer-2 が両 witness を delegation 呼出、**EPIG2HeatFlowContinuity.lean は own-file
   sorry-free** に (全壁が Vitali ファイルに集約)。`hpX_mass` を UI に追加 (確率測度 framing、layer-2 threading)。
   独立 honesty-auditor PASS (9 decl)。

7. **(2026-06-04 honesty) UT/UI witness は `hu_bdd` 欠落で under-hypothesized (genuine に偽) と判明 → 修正**:
   UT/UI witness の元 signature は `u : ℕ → ℝ` (hu_pos のみ) で、`u n → ∞` のとき密度分散 `∫x²f_n = ∫x²pX +
   (∫pX)·u n` が n 非一様 → UnifTight/UnifIntegrable は **genuine に偽** (質量が遠方へ逃げ tail 一様性が
   崩れる)。これは CLAUDE.md「under-hypothesized / insufficient signature」defect。`hu_bdd : BddAbove
   (Set.range u)` precondition を追加して修正 (regularity、非 load-bearing)。唯一の consumer (layer-2、
   `u→0` 列) は収束列ゆえ `(hv_lim.mono_right nhdsWithin_le_nhds).bddAbove_range` で genuine 供給。
   独立 honesty-auditor PASS。**parked sorry でも signature が偽を主張していたら honesty defect** という
   教訓 (sorry は「未証明」を意味するが「statement が真」を保証しない)。
