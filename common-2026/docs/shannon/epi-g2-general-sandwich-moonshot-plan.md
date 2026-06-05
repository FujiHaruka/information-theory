# EPI G2 端点連続性 — 一般形 genuine サンドイッチ moonshot 計画 🌙

> **Parent**: [`epi-g2-layer2-moonshot-plan.md`](epi-g2-layer2-moonshot-plan.md) §Phase 1/2
> （兄弟ルート: [`epi-g2-vitali-closure-plan.md`](epi-g2-vitali-closure-plan.md) = 現行 UI/UT witness、
> [`epi-g2-delavp-moonshot-plan.md`](epi-g2-delavp-moonshot-plan.md) = de la VP 機構自作）
> **対象壁**: EPI G2 heat-flow 端点連続性 `wall:approx-identity-L1` 配下の層2 積分収束を、
> **スコープ犠牲なし（一般の有限 2 次モーメント分布のまま）** に閉じる **正攻法サンドイッチ**。
> **一次根拠 (verbatim signature 確定済、再調査不要、参照のみ)**:
> [`epi-g2-general-sandwich-inventory.md`](epi-g2-general-sandwich-inventory.md) +
> [`epi-g2-sandwich-inventory.md`](epi-g2-sandwich-inventory.md) +
> [`epi-g2-delavp-recheck-inventory.md`](epi-g2-delavp-recheck-inventory.md)

<!--
記法: 状態絵文字 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更(判断ログ参照)。
取り消し線 = 廃止 Phase (履歴のため残す)。判断ログ append-only。
rg "^- \[ \]" で残タスク横断 grep、rg "🔄" でピボット箇所だけ拾える。
-->

## 進捗

- [x] Phase 0 — 接続 lemma の verbatim 再確認（Read のみ） ✅
- [x] **Phase 1 — (β) 下界: 畳み込みでエントロピー非減少 ✅ DONE (genuine, sorryAx-free, 独立監査 PASS)**
- [x] **Phase 2 — (α) 上界: KL 下半連続性 ✅ DONE (genuine, sorryAx-free, 独立監査 PASS)** 🔄 — 2b DV 双対 hard direction を回避し **klFun-Fatou ルート**で genuine 化（判断ログ 7）。
- [x] **Phase 3 — 層2 載せ替え + UI/UT witness 削除 + 独立 honesty audit ✅ DONE** — `wall:approx-identity-L1` CLOSED、EPI G2 端点連続性 一般形 genuine 完成（判断ログ 7）。

> **🎉 MOONSHOT 達成 (2026-06-05 multi-round orchestrator session)**: EPI G2 heat-flow 端点連続性が
> **一般の有限 2 次モーメント分布 + `h(X)>−∞` のまま (スコープ犠牲なし) で完全 genuine 完成**。親計画・在庫・
> handoff が「research-level moonshot、park が honest」と判定していた **DV 双対 hard direction (2b) を回避**し、
> KL 下半連続性を **klFun 積分表現 (`klDiv_eq_lintegral_klFun_of_ac`) + klFun≥0 + Fatou (`lintegral_liminf_le`)**
> で出す klFun-Fatou ルートで closure（判断ログ 7）。`wall:approx-identity-L1` の最後の壁 (UI/UT witness 2 本) を
> 削除、`#print axioms` で層2 + 下流 sorryAx-free。新規 genuine 資産: `EPIG2KLFatouLSC.lean` (KL-LSC, W1-W4 +
> assembly)、`EPIG2ConvEntropyDensity.lean` (密度形 (β) 下界)。独立 honesty audit 3 回全 PASS。

> **進捗スナップショット (2026-06-04 multi-round session)**:
> - **Phase 2a ✅ genuine DONE**: `EPIG2KLVariationalLower.lean`、`klDiv_variational_lower_bound` +
>   `integral_exp_sub_llr_le`、sorryAx-free、独立監査 PASS。在庫の悲観評価 (tilted-measure KL chain
>   rule 不在) を Jensen-on-exp + RN change-of-measure で迂回し genuine close。一般 KL 変分下界として
>   再利用可能な独立資産 (Phase 2c の LSC 組立や他 family の KL 評価から呼べる)。
> - **Phase 1 (β) 補題2 ✅ genuine DONE**: `condDifferentialEntropy_indep_add_eq` (fibre 同定)、
>   sorryAx-free、独立監査 PASS。z 依存アフィン kernel `affineShiftKernel` +
>   `prod_map_affine_eq_compProd` + `condDistrib_ae_eq_of_measure_eq_compProd` 一意性で
>   在庫の「wall 誤分類」を解消。
> - **Phase 1 (β) ✅ 完全 DONE (genuine, sorryAx-free, 独立監査 14 宣言 PASS)**: bridge 補題
>   `differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv` を 3 sub-gap の並列実装 + assembly で
>   genuine close → `condDifferentialEntropy_le` (conditioning reduces) + device/密度形
>   `negMulLog_convDensity_entropy_ge` (= layer-2 (β) ターゲット) 全 sorryAx-free。**cond-diff-entropy
>   wall CLOSED** (active residual 0 件)。新規 reusable 資産 (EPI line / 教科書全体):
>   - `CondKLIntegral.lean` — **条件付き KL の積分形** `(klDiv (μ⊗ₘκ)(μ⊗ₘη)).toReal = ∫ z, (klDiv (κz)(ηz)).toReal ∂μ`
>     (一般版 + const 版)。Mathlib 明示 TODO (`ChainRule.lean:74-77`) を充足、`compProd_withDensity` slice
>     同定で plumbing 解決。**Mathlib upstream PR 候補**。
>   - `EPIG2BridgeDensityHelpers.lean` — per-fibre 密度展開 `(klDiv P Q).toReal = −h(P) − ∫ p log q` +
>     condDistrib marginal-Fubini 同定 (g-一般 core + density wrapper)。
>   - assembly が threading した precondition は全て regularity (独立監査が 1 つずつ load-bearing 判定 →
>     全 regularity、vacuous なし)。

## ゴール

層2 machinery `differentialEntropy_convDensity_integral_tendsto`
(`EPIG2HeatFlowContinuity.lean:193`、own-sorry 0、**結論型不変**) を、現行の Vitali (UnifIntegrable/
UnifTight) ルートから **(α) 上界 + (β) 下界のサンドイッチ**に載せ替え、UI/UT witness 2 本
(`wall:approx-identity-L1` park 中) を削除する。**一般の有限 2 次モーメント分布 `pX`（`∫pX=1`、
有限 2 次モーメント `hpX_mom`、`h(X)>-∞` = `hpX_ent`）のまま**閉じる（スコープ犠牲なし）。
honest 中間着地 = **Phase 1 (β) + Phase 2 の 2a/2c genuine 化 + 2b（DV 双対 hard direction）を
`@residual(wall:kl-lower-semicontinuous)` park**（壁を「DV 双対 1 本」に最大絞り込み）。

## Approach

### 全体形状図 — de la VP route と sandwich route が同一核心に収束する

```text
                 最終形 (層2 結論型、不変で載せ替え):
   differentialEntropy_convDensity_integral_tendsto (EPIG2HeatFlowContinuity.lean:193)
   Tendsto (fun t => ∫ negMulLog (convDensityAdd pX (gaussianPDFReal 0 t.toNNReal) ·))
           (𝓝[Ioi 0] 0)  (𝓝 (∫ negMulLog pX))
   h(f) := ∫ negMulLog f、 f_n = pX ∗ g_{u n} → pX in L¹ (層1 genuine closed)
                                   │
        ┌──────── (β) 下界 [Phase 1] ────────┐   ┌──────── (α) 上界 [Phase 2] ────────┐
        │ ∀n, h(f_n) ≥ h(pX)                  │   │ limsup h(f_n) ≤ h(pX)              │
        │ = 畳み込みでエントロピー非減少       │   │ = ∫ f log f / KL の弱/L¹-LSC      │
        │ ★壁なし buildable・再利用資産       │   │ ★本体 wall (最難)                 │
        └────────────────┬───────────────────┘   └────────────────┬──────────────────┘
                         │                                          │
                         └────────── tendsto_of_le_liminf_of_limsup_le ──────────┘
                                 (LiminfLimsup.lean:306、ℝ で型クラス充足、§C)

   ───────────────────────────────────────────────────────────────────────────────
   核心の同型性 (de la VP route との収束点):

     de la VP route の本体 wall          sandwich route (α) の本体 wall
     = negMulLog 負部の n-一様可積分    ≡  = 相対エントロピー (KL) の下半連続性
       (tail uniform integrability)         (= Donsker-Varadhan hard direction)
                       │                                  │
                       └────────── 数学的に同型 ──────────┘
              どちらも「tail の一様可積分性 = 質量が逃げない」を要求
              一般形を正攻法で攻める = この DV 双対の hard direction を自作すること
```

**骨子**: 層2 を「(β) 下界 = 畳み込みエントロピー非減少（Phase 1、壁なし buildable）」と
「(α) 上界 = KL 下半連続性（Phase 2、本体 wall）」のサンドイッチに分解し、`tendsto_of_le_liminf_
of_limsup_le`（§C、存在確認済）で `Tendsto` を組む。de la VP route（UnifIntegrable 直接）と
sandwich route（α = KL-LSC）は **同一の数学的核心**（tail の一様可積分性 = Donsker-Varadhan
hard direction）に収束する。一般形を正攻法で攻めるとは、この **DV 双対の hard direction を自作する**
ことに他ならない。

### 最重要の正直さ — どこが buildable でどこが還元不能 wall か

planner の核心責務は「片刃 buildable / 両刃の片方が wall」を誤魔化さず明記すること:

- **Phase 1 (β) 下界は壁なし buildable・再利用資産だが片刃**。連続版 conditioning-reduces-entropy
  `h(X+√tZ) ≥ h(X+√tZ|Z) = h(X)` は in-tree/Mathlib に組立済み定理が無い（§B、`condDifferentialEntropy`
  = Found 0、連続 conditioning = 不在、畳み込み単調 `h(X+Y)≥h(X)` = 不在）が、**genuine 自作可能**
  （`I(X;Z) = KL(joint‖product) ≥ 0` 経由 = 不在 ≠ 壁）。EPI line / 教科書全体で再利用可能な独立
  資産。**ただし片刃** — (α) が閉じねば G2 端点連続性は閉じない。
- **Phase 2 (α) 上界の 2a/2c は buildable、2b（DV 双対 hard direction）が還元不能の本体 wall**:
  - **2a (Gibbs/Jensen、easy 方向)**: `KL(μ‖ν) ≥ ∫g dμ − log∫e^g dν`（∀ bounded cts g）。在庫の
    Gibbs 素材（`mul_log_le_klDiv` `Basic.lean:360`、`le_integral_rnDeriv_of_ac` `IntegralRNDeriv.lean:49`、
    `convexOn_klFun`）から組める見込み = buildable。
  - **2c (LSC 組立)**: 各 bounded g で `F_g(μ) := ∫g dμ − log∫e^g dν` が弱収束で連続 → `KL = sup_g F_g`
    が sup-of-continuous で LSC = buildable（2a + 2b が揃えば plumbing）。
  - **2b (DV 双対、hard 方向 = 本体 moonshot)**: `KL(μ) = sup_{g bounded cts}(∫g dμ − log∫e^g dν)` の
    `≤`（sup が KL に到達）。Mathlib 完全不在（inventory §A: `"DonskerVaradhan"` = Found 0、
    `klDiv, iSup` = Found 0、`klDiv, Real.exp` = Found 0）。**これが還元不能 wall**で、de la VP wall と
    数学的に同型（どちらも tail 一様可積分を要求）。research-level・複数 session。
- **honest 中間着地** = **Phase 1 (β) + Phase 2 の 2a/2c genuine 化 + 2b を
  `@residual(wall:kl-lower-semicontinuous)` park**。壁が「DV 双対 hard direction 1 本」に最大絞り込み
  された surface shrink 状態（type-check done）。

### 未解決の subtle question（明記、closure 時に決着）

**定理が一般有限 2 次モーメント + `h(X)>-∞` で真かは未確定**。Barron 1986（"Entropy and the Central
Limit Theorem"）は `h(X+√tZ) → h(X)` の `t→0⁺` 連続性に **sub-Gaussian** を示唆するが、compact-support
分布では tail moment 有界の反証計算がある（`epi-g2-delavp-moonshot-plan.md` 判断ログ 7 末尾: compact-
support 裾でも tail moment は Gaussian 減衰が log 増大を凌ぎ有界）。**DV 双対（2b）が closure すれば
定理の真偽（true-but-hard か under-hypothesized か）も決着する** — KL-LSC は一般の有限 2 次モーメントで
成り立つ古典定理（Donsker-Varadhan 1975）であり、2b が閉じれば一般形が真と確定する。この subtle
question は de la VP route の判断ログ 7 の積み残しと同根で、本 route の closure が両方を決着させる。

### 撤退ライン（honest 中間着地、仮説束化禁止）

- **Phase 1 (β) が park（低確率）**: conditioning ルートの disintegration（条件付き密度存在等）で
  詰まったら `sorry` + `@residual(wall:cond-diff-entropy)`（新 wall slug、ただし不在 ≠ 壁で closeable
  見込み高、§Phase 1）。
- **Phase 2 で 2a/2c のみ genuine、2b park（最尤の honest 着地）**: 2b の DV 双対 hard direction が
  当該 session（複数含む）で組めない場合の中間着地。`sorry` + `@residual(wall:kl-lower-semicontinuous)`。
  壁が「DV 双対 1 本」に絞られた surface shrink。
- **Phase 1 / Phase 2 のいずれかが park 中は層2 据置**（Vitali ルートを維持、§Phase 3）。Phase 1 のみ
  genuine 化しても (α) が park なら層2 載せ替えはせず、(β) genuine 資産だけ独立 ship（再利用可）。
- **仮説束化は全 Phase で禁止**（tier 5、CLAUDE.md「検証の誠実性」）。KL-LSC / DV 双対 / 畳み込み
  単調 / conditioning 減少を `*Hypothesis` / `*Reduction` predicate に bundle して仮説で渡すのは禁止。
  撤退口は必ず `sorry` + `@residual(wall:...)` のみ。追加してよいのは precondition（regularity =
  `IsHeatFlowEndpointRegular` の field: measurability / `IndepFun X Z` / `Z` Gaussian / `IsFiniteMeasure`）
  だけで、**結論（LSC / 単調性）を hyp に取らない**（循環）。判定の一言: 「その仮説は前提条件
  （regularity）か、証明の核心（load-bearing）か」→ 前者のみ OK。

## Phase 0 — 接続 lemma の verbatim 再確認（Read のみ） 📋

> 在庫 3 本（general-sandwich / sandwich / delavp-recheck）は verbatim signature 確定済。Phase 0 は
> **新規 inventory ではなく**、Phase 1/2/3 が接続する lemma の signature を着手直前に再 Read するだけ
> （CLAUDE.md「依存方向 / wrapper 呼出方向の verbatim 確認」）。

- [ ] **層2 結論型** `differentialEntropy_convDensity_integral_tendsto`（`EPIG2HeatFlowContinuity.lean:193`）
  を Read し、`gaussianPDFReal 0 t.toNNReal` / `negMulLog` / `𝓝[Set.Ioi 0] 0` の形を確認。
  **verbatim（確定済、参照のみ）**: 入力 `{pX : ℝ → ℝ} (hpX_nn) (hpX_meas) (hpX_int)
  (hpX_mass : (∫ y, pX y ∂volume) = 1) (hpX_mom) (hpX_ent : Integrable (negMulLog ∘ pX) volume)`、
  結論 `Tendsto (fun t => ∫ negMulLog (convDensityAdd pX (gaussianPDFReal 0 t.toNNReal) ·)) (𝓝[Ioi 0] 0)
  (𝓝 (∫ negMulLog pX))`。
- [ ] **サンドイッチ組立 API** `tendsto_of_le_liminf_of_limsup_le`（`LiminfLimsup.lean:306`）の型クラス
  前提を確認（§C verbatim: `[ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]`、
  `ℝ` 全充足、`IsBoundedUnder (·≤·)/(·≥·)` 2 本は `isBoundedDefault` 自動）。
- [ ] **(β) 接続 lemma** verbatim（§B、確定済、参照のみ）:
  - `ProbabilityTheory.IndepFun.map_add_eq_map_conv_map`（`Mathlib/Probability/Independence/Basic.lean:1103`、
    `[IsFiniteMeasure μ] {f g : Ω → M} (hf : Measurable f) (hg : Measurable g) (hfg : f ⟂ᵢ[μ] g) :
    μ.map (f + g) = (μ.map f) ∗ₘ (μ.map g)`、`M` が `[MeasurableAdd₂ M]`）。
  - `InformationTheory.Shannon.differentialEntropy_map_add_const`（`DifferentialEntropy.lean:171`、
    `{μ : Measure ℝ} (hμ : μ ≪ volume) [SigmaFinite μ] (y : ℝ) :
    differentialEntropy (μ.map (· + y)) = differentialEntropy μ`、genuine body）。
  - `InformationTheory.Shannon.entropyPower_pos`（`EntropyPowerInequality.lean:109`、`@audit:ok`）+
    `entropyPower_le_of_differentialEntropy_le`（`EPIPlumbing.lean:86`、genuine、`h-不等式 ↔ entropyPower-不等式`）。
- [ ] **(α) 接続 lemma** verbatim（§A、確定済、参照のみ）:
  - `InformationTheory.mul_log_le_klDiv`（`KullbackLeibler/Basic.lean:360`、`[IsFiniteMeasure μ]
    [IsFiniteMeasure ν]`）。`mul_log_le_toReal_klDiv`（`Basic.lean:346`、`toReal` 版）。
  - `MeasureTheory.le_integral_rnDeriv_of_ac`（`IntegralRNDeriv.lean:49`、`[IsFiniteMeasure μ]
    [IsProbabilityMeasure ν] (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousWithinAt f
    (Set.Ici 0) 0) (hf_int) (hμν : μ ≪ ν) : f (μ.real univ) ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν`）。
  - `InformationTheory.convexOn_klFun`（`KLFun.lean`、`ConvexOn ℝ (Set.Ici 0) klFun`、klFun = `x*log x − x + 1`）。
- [ ] **caller の precondition bundle** `IsHeatFlowEndpointRegular`（`EPIG2HeatFlowContinuity.lean:474`）の
  field を Read（measurability / `IndepFun X Z` / `Z` Gaussian `gaussianReal 0 v_Z` / 密度 witness pX /
  `hpX_ent`）。Phase 1 の (β) が要求する `IndepFun X Z` / `Measurable X,Z` が field に揃っているか確認
  （`epi-g2-vitali-closure-plan.md` 判断ログ 2 で「`pX` のみ保有 → X,Z,P precondition 追加」が確認済の
  ため、(β) も同 bundle から threading 可能の見込み）。
- **工数**: 30-60 分（Read のみ、新規証明なし）。
- **proof-log**: no（Read のみ）。

## Phase 1 — (β) 下界: 畳み込みでエントロピー非減少（★壁なし buildable・最優先・再利用資産） 📋

> `h(f_n) ≥ h(pX)` を **非循環**（EPI 迂回、`stamToEPIBridge_holds` は G2-blocked で循環）に出す。
> ルート = 連続版 conditioning-reduces-entropy: `h(X+√tZ) ≥ h(X+√tZ|Z) = h(X)`。
> Mathlib 不在（= 未整備）だが genuine 自作可能。**EPI line / 教科書全体で再利用可能な独立資産。最初の
> 独立 ship 単位**。

- **目標（自作する補題の想定 signature、設計案 — Phase 1 着手時に確定）**:
  ```lean
  -- InformationTheory/Shannon/EPIG2ConvEntropyMonotone.lean (新 file 構想)
  -- (β) 畳み込みでエントロピー非減少: h(pX) ≤ h(f_n)。
  -- f_n := convDensityAdd pX (gaussianPDFReal 0 ⟨u n,_⟩)
  theorem negMulLog_convDensity_entropy_ge
      {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
      (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
      (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
      (hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume)
      (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (n : ℕ) :
      (∫ x, Real.negMulLog (pX x) ∂volume)
        ≤ ∫ x, Real.negMulLog
            (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x) ∂volume := by sorry
  -- 注: precondition として X,Z,P,v_Z,hZ_law (IsHeatFlowEndpointRegular の field) を追加する
  --     可能性が高い (condDistrib / IndepFun の standing assumption)。Phase 0 で threading 可否確認。
  ```
- **Mathlib-shape-driven 設計（CLAUDE.md「Mathlib-shape-driven Definitions」厳守）**:
  - 条件付け減少 `h(X|Z) ≤ h(X)` を出すなら、結論形を Mathlib の `klDiv` 非負形に噛む形に定義する。
    `I(X;Z) = h(X) − h(X|Z) = KL(joint‖product) ≥ 0` 経由。**結論形の verbatim 確認義務**: `klDiv` は
    `ℝ≥0∞`-値で `≥ 0` は型から自明（inventory §A: `klDiv_nonneg` 名 = Found 0、`klDiv, |- 0 ≤ _` =
    Found 0、`klDiv : ℝ≥0∞` で非負は型から自明、`toReal` 版の明示 lemma は無い）。よって `I(X;Z) ≥ 0` を
    `klDiv ... ≥ 0`（型自明）から出す形に条件付き differential entropy / 連続 MI を定義する。**textbook の
    `h(X|Z) := ∫ h(X|Z=z) dz` 形を直接 def 化しない** — Mathlib `condDistrib` の disintegration 結論形
    （`ProbabilityTheory.condDistrib`、Phase 0 で verbatim）に合わせる。
  - 条件付き differential entropy 定義自体に `sorry` を書けない箇所が出たら（def / Prop RHS）、CLAUDE.md
    「sorry を書けない箇所での対処順序」第一選択（定義書換で性質を別 theorem に逃がし body `sorry`）を適用。
- **部品（in-tree / Mathlib、§B verbatim）**:
  - `IndepFun.map_add_eq_map_conv_map`（`Basic.lean:1103`、genuine）で測度等式
    `P.map(X+√tZ) = (P.map X) ∗ₘ (P.map(√tZ))` を明示。**罠注意（§B、inventory §B 所見）**: これは
    **測度の畳み込み等式のみ**でエントロピー単調を含意しない。単調 core は条件付け減少（不在 → 自作）。
  - `differentialEntropy_map_add_const`（`DifferentialEntropy.lean:171`、genuine）で `h(X+√tZ|Z=z) = h(X)`
    の定数平行移動部分（条件付き fiber は `X` の `z` 平行移動）を genuine に処理。
  - `entropyPower_pos`（`@audit:ok`）+ `entropyPower_le_of_differentialEntropy_le`（`EPIPlumbing.lean:86`、
    genuine）で `h` 不等式 ↔ entropyPower 不等式の橋（結論型を `∫ negMulLog` 直接形に持ち込む際の plumbing）。
- **要自作補助（in-tree/Mathlib 不在、§B: 連続 condDifferentialEntropy / conditioning 減少 = Found 0）**:
  - [ ] 連続版条件付き differential entropy の定義（Mathlib `condDistrib` / disintegration ベース、
    Mathlib-shape-driven）。**離散版 `MeasureFano.condEntropy`（`∑ x`、Fano family）を流用しない**
    （differential 版でない、§B）。
  - [ ] conditioning-reduces-entropy `h(X|Z) ≤ h(X)`（`I(X;Z) = KL(joint‖product) ≥ 0` 経由）。
  - [ ] 独立和 fiber の同定 `h(X+√tZ|Z) = h(X)`（`IndepFun.map_add_eq_map_conv_map` +
    `differentialEntropy_map_add_const`）。
- **工数**: 100-200 行 + 新規定義 Mathlib-shape 設計。これ自体は壁でなく**不在**（genuine 自作可）。
- **1-session ship**: △〜✗（条件付きエントロピー基盤の新設を含むため複数 step、ただし独立 file で
  UI/UT witness を待たず着手可能。最初の独立 ship 単位）。
- **撤退口**: disintegration の条件付き密度存在 / `condDistrib` の rnDeriv 表現等で詰まったら
  `sorry` + `@residual(wall:cond-diff-entropy)`（新 wall slug = 連続版条件付き differential entropy +
  conditioning 減少。ただし不在 ≠ 真壁で closeable 見込み高）。**仮説束化禁止**（条件付け減少 / 単調性を
  `*Hypothesis` predicate に bundle しない、tier 5）。
- **closure 見込み判定**: **genuine 可能（壁なし buildable）**。conditioning-reduces-entropy は古典的で、
  Mathlib 不在は未整備（§B: loogle/rg Found 0 = honest gap）であって数学的障害でない。`condDistrib` 基盤は
  Mathlib に存在するため disintegration は組める。EPI line / 教科書全体で再利用可能な独立資産。
- **proof-log**: yes（条件付き differential entropy 定義の Mathlib-shape 確定 + conditioning 減少の証明）。

### 最初の独立 ship 単位 = Phase 1 (β)、skeleton 設計

Phase 1 を最優先・最初の独立 ship 単位とする理由: (a) **壁なし buildable**（不在 ≠ 壁）、(b) UI/UT
witness を待たず独立 file で着手可能、(c) EPI line / 教科書全体で **再利用可能な独立資産**（連続版
条件付き differential entropy + conditioning-reduces-entropy は Cover-Thomas 全章で使う基盤）。

**条件付き differential entropy 定義の Mathlib-shape（設計案、Phase 1 冒頭で `condDistrib` 結論形 verbatim
確認後に確定）**:

```lean
-- Mathlib-shape-driven: Mathlib condDistrib の disintegration 結論形に合わせる。
-- textbook h(X|Z) := ∫_z h(X|Z=z) dμ_Z(z) を直接 def 化しない。
-- 期待する dominant Mathlib lemma (Phase 0 で verbatim 確認):
--   ProbabilityTheory.condDistrib : (Ω → β) → (Ω → α) → Measure Ω → Kernel α β
--   その rnDeriv / disintegration 表現 (compProd_condDistrib 系)。
--   InformationTheory.klDiv (joint ‖ product) ≥ 0 (型自明、ℝ≥0∞-値)。

namespace InformationTheory.Shannon

/-- 連続版条件付き differential entropy。`condDistrib X Z μ` の fiber エントロピーを
`μ.map Z` で平均。定義は Mathlib `condDistrib` の結論形に合わせる (Mathlib-shape-driven)。
@residual(wall:cond-diff-entropy) -/  -- ← 定義に sorry を書けないため、性質補題を別 theorem に逃がす
noncomputable def condDifferentialEntropy
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) : ℝ :=
  ∫ z, differentialEntropy ((condDistrib X Z μ) z) ∂(μ.map Z)
  -- 注: condDistrib の verbatim 引数順 (X Z μ か Z X μ か) は Phase 0 で確認して確定。

/-- conditioning reduces (differential) entropy: `h(X|Z) ≤ h(X)`。
`I(X;Z) = h(X) − h(X|Z) = KL(joint ‖ product) ≥ 0` 経由。`klDiv ≥ 0` は型自明 (ℝ≥0∞-値)。
@residual(wall:cond-diff-entropy) -/
theorem condDifferentialEntropy_le
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) (hX_ac : (μ.map X) ≪ volume) :
    condDifferentialEntropy X Z μ ≤ differentialEntropy (μ.map X) := by
  sorry  -- @residual(wall:cond-diff-entropy) (closeable: condDistrib + klDiv 非負)

/-- 独立和 fiber の同定: `h(X+√tZ | Z) = h(X)` (条件付き fiber は X の z 平行移動、
`differentialEntropy_map_add_const` で genuine)。 -/
theorem condDifferentialEntropy_indep_add_eq
    {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z μ)
    (hX_ac : (μ.map X) ≪ volume) :
    condDifferentialEntropy (fun ω => X ω + Z ω) Z μ = differentialEntropy (μ.map X) := by
  sorry  -- @residual(wall:cond-diff-entropy) (closeable: differentialEntropy_map_add_const + condDistrib fiber)

end InformationTheory.Shannon
```

3 補題を組むと (β) `negMulLog_convDensity_entropy_ge` は `h(X) = h(X+√tZ|Z) ≤ h(X+√tZ)` の連鎖で出る
（`√tZ` は `gaussianReal 0 (t·v_Z)`、`IsHeatFlowEndpointRegular` の `Z` Gaussian field から供給）。
**この skeleton は壁ではなく不在の自作**（`condDistrib` は Mathlib 既存）であり、撤退口
`@residual(wall:cond-diff-entropy)` は park でなく「complex な自作の途中マーカー」として使う。

## Phase 2 — (α) 上界: KL/相対エントロピー下半連続性 = Donsker-Varadhan（★本体 wall、最難） 📋

> `liminf ∫ f_n log f_n ≥ ∫ pX log pX`（= `limsup h(f_n) ≤ h(pX)`）。**critical-path wall**。
> sub-Phase 2a/2b/2c に分解。2a/2c は buildable、**2b（DV 双対 hard direction）が還元不能の本体 moonshot**。

- **目標**:
  ```lean
  -- (α) 上界: limsup h(f_n) ≤ h(pX)。f_n := convDensityAdd pX (gaussianPDFReal 0 ⟨u n,_⟩)
  theorem negMulLog_convDensity_limsup_le
      {pX : ℝ → ℝ} (hpX_nn) (hpX_meas) (hpX_int) (hpX_mass) (hpX_mom) (hpX_ent)
      (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_lim : Tendsto u atTop (𝓝[Set.Ioi 0] 0)) :
      Filter.limsup
          (fun n => ∫ x, Real.negMulLog
            (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x) ∂volume) atTop
        ≤ (∫ x, Real.negMulLog (pX x) ∂volume) := by sorry
  -- ⟺ liminf (∫ f_n log f_n) ≥ ∫ pX log pX (negMulLog = −f log f、符号反転)
  -- ⟺ KL(μ_n ‖ gaussian-ref) の弱/L¹-LSC
  ```

### sub-Phase 2a — Gibbs/Jensen 下界（★buildable、easy 方向）

`KL(μ‖ν) ≥ ∫g dμ − log∫e^g dν`（∀ bounded cts g）= DV 双対の **easy direction**。

- **部品（§A verbatim）**: `mul_log_le_klDiv`（`Basic.lean:360`、`[IsFiniteMeasure μ] [IsFiniteMeasure ν]`、
  質量レベル Gibbs）/ `le_integral_rnDeriv_of_ac`（`IntegralRNDeriv.lean:49`、単一測度 Jensen 下界）/
  `convexOn_klFun`（`KLFun.lean`、Jensen の凸性供給）。
- **証明骨子**: bounded cts g に対し `e^g` で測度を tilt し、Jensen `le_integral_rnDeriv_of_ac` を凸関数
  `klFun` に適用して `∫g dμ − log∫e^g dν ≤ KL(μ‖ν)` を出す。質量レベル Gibbs `mul_log_le_klDiv` は集合質量
  形なので pointwise cross-entropy に持ち上げる際 bounded g の tilt を経由。
- **工数**: 40-80 行。**buildable**（在庫の Gibbs/Jensen 素材で組める）。
- **撤退口**: bounded g の tilt が `le_integral_rnDeriv_of_ac` の `μ ≪ ν` / 可積分前提と繋がらない場合のみ
  `sorry` + `@residual(wall:kl-lower-semicontinuous)`（低確率）。

### sub-Phase 2b — DV 双対 hard direction（★本体 moonshot、還元不能 wall）

`KL(μ) = sup_{g bounded cts}(∫g dμ − log∫e^g dν)` の `≤`（sup が KL に到達）。

- **状態**: **Mathlib 完全不在**（inventory §A authoritative: `"DonskerVaradhan"` = Found 0、
  `"onsker"` = Found 0、`klDiv, iSup` = Found 0、`klDiv, SupSet.sSup` = Found 0、`klDiv, Real.log,
  integral` = Found 0、`klDiv, LowerSemicontinuous` = Found 0、`klDiv, Filter.liminf` = Found 0）。
- **数学的内容（self-attaining の構成）**: optimal `g* = log(dμ/dν)`（rnDeriv の log）を bounded cts で
  近似し、sup がその近似列に沿って `KL` に収束することを示す。bounded cts への近似（truncation +
  mollification）+ 単調収束 / 優収束で sup ≥ KL を出す。**これが de la VP wall と同型** — どちらも
  「tail（大きい rnDeriv 値）の質量が逃げない一様可積分性」を要求する。
- **工数**: 大（DV 双対自作、moonshot、行数不定 — 100-300 行 + tail truncation の解析）。
- **1-session ship**: ✗（research-level・複数 session）。
- **撤退口**: 当該 session（複数含む）で組めなければ `sorry` + `@residual(wall:kl-lower-semicontinuous)`
  維持（新 wall slug = 一般形の本体 wall、de la VP wall と同型を docstring に明記）。**仮説束化禁止**
  （DV 双対 / sup 到達を `*Hypothesis` predicate に bundle しない、tier 5）。
- **closure 見込み判定**: **不確実（真の moonshot 核）**。Donsker-Varadhan 1975 は一般の有限 2 次モーメントで
  成り立つ古典定理だが Mathlib 完全不在で自作は research-level。Mathlib upstream PR 候補。

### sub-Phase 2c — LSC 組立（★buildable、2a + 2b 揃えば plumbing）

各 bounded g で `F_g(μ) := ∫g dμ − log∫e^g dν` が弱収束で連続 → `KL = sup_g F_g` が sup-of-continuous で
LSC → `liminf KL(μ_n) ≥ F_g(μ_n) → F_g(μ)`、sup で `≥ KL(μ)`。

- **証明骨子**: `μ_n → μ` 弱収束（層1 L¹ 収束から、`f_n → pX` in L¹ ⟹ `μ_n → μ` 弱収束）。各 bounded cts g で
  `∫g dμ_n → ∫g dμ`（弱収束の定義）+ `log∫e^g dμ_n → log∫e^g dμ`（`e^g` bounded cts）→ `F_g(μ_n) → F_g(μ)`。
  2a より `F_g(μ_n) ≤ KL(μ_n)`、よって `F_g(μ) = lim F_g(μ_n) ≤ liminf KL(μ_n)`。g で sup を取り 2b
  （`sup_g F_g(μ) = KL(μ)`）で `KL(μ) ≤ liminf KL(μ_n)` = LSC。
- **2a があれば各 `F_g ≤ KL` は出る。LSC に必要なのは 2a（各 g で下界）+ 2b（限界点 μ での sup 到達 = 等式）**。
- **工数**: 30-60 行。**buildable**（2a + 2b が揃えば plumbing。弱収束は層1 L¹ から genuine）。
- **撤退口**: 弱収束 `μ_n → μ` が層1 L¹ 収束から出ない場合のみ `sorry` + `@residual(wall:kl-lower-semicontinuous)`
  （低確率、L¹ → 弱収束は genuine）。

- **Phase 2 全体の closure 判定**: **2b 次第**。2a/2c は buildable、2b が真の wall。**2a + 2c だけ genuine 化
  すれば「壁が DV 双対 hard direction 1 本に絞られる」surface shrink**（honest 中間着地）。
- **proof-log**: yes（2a/2c の genuine 化 + 2b の構成試行 / park 判定を記録）。

## Phase 3 — 層2 載せ替え + UI/UT witness 削除 + 独立 honesty audit 📋

> Phase 1 (β) + Phase 2 (α) が揃えば層2 を Vitali からサンドイッチに書換、UI/UT witness 2 本を削除。

- **タスク**:
  - [ ] 層2 `differentialEntropy_convDensity_integral_tendsto`（`EPIG2HeatFlowContinuity.lean:193`）の
    body を Vitali ブロック（`tendsto_Lp_of_tendsto_ae` + UI/UT/ae witness）から **サンドイッチ**に書換:
    `tendsto_of_le_liminf_of_limsup_le`（`LiminfLimsup.lean:306`）に (β)（`a := h pX ≤ liminf`）+
    (α)（`limsup ≤ a`）を渡す。`IsBoundedUnder (·≤·)/(·≥·)` 2 本は (α)/(β) から派生（`isBoundedDefault`
    自動、有界性の実体は (α) limsup 有界 + (β) liminf 有界から）。**結論型不変**（§C: signature 不変、
    内部 body の置換のみ）。
  - [ ] UI/UT witness 2 本（`EPIVitaliUI.lean` / `EPIVitaliUnifTight.lean` の
    `negMulLog_convDensity_unifIntegrable` / `negMulLog_convDensity_unifTight`、`wall:approx-identity-L1`
    park 中）が層2 から不要になり**削除可能**になる。ae witness（`negMulLog_convDensity_tendsto_ae_subseq`、
    `@audit:ok`）も layer-2 のサンドイッチ書換で不要になれば削除（または他 consumer 確認後）。
  - [ ] `wall:approx-identity-L1` register 行（`docs/audit/audit-tags.md`）の active residual 更新は
    orchestrator 判断（サンドイッチ書換後の壁状態は `wall:cond-diff-entropy`（Phase 1 park 時）+
    `wall:kl-lower-semicontinuous`（Phase 2 2b park 時）に移行）。
- **独立 honesty audit 起動（CLAUDE.md 必須）**: 層2 body の書換 + UI/UT witness 削除 + 新 wall slug 2 つの
  `@residual` 導入は CLAUDE.md 起動条件「新規 `@residual` 導入」「既存 declaration の signature/依存変更」に
  該当 → 実装 session で **`honesty-auditor` を 1 件起動必須**。verify 対象:
  - (i) Phase 1 (β) `condDifferentialEntropy_le` / 関連が genuine（conditioning 減少 / 単調性を hyp に
    bundle していない、追加 field は precondition）。
  - (ii) Phase 2 (α) 2a/2c が genuine、2b の `@residual(wall:kl-lower-semicontinuous)` 分類の正しさ
    （DV 双対 hard direction の wall 主張が honest = Mathlib Found 0 裏取り済）。
  - (iii) `wall:cond-diff-entropy` / `wall:kl-lower-semicontinuous` の register 追加（loogle 0 件確認 +
    既存類似なし確認、`docs/audit/audit-tags.md`「新規 wall を追加する時」手順）。
- **層2 consumer への影響（verbatim 確認）**: 壁補題 `heatFlowEntropyPower_continuousWithinAt_zero`
  （`EPIG2HeatFlowContinuity.lean:550`）+ helper `heatFlowDifferentialEntropy_continuousWithinAt_zero`
  （`:334`）は層2 を呼ぶ側で、結論型不変なら影響なし。Phase 3 着手時に層2 → 壁補題の呼出鎖を verbatim 再確認
  （CLAUDE.md「wrapper 呼出方向の verbatim 確認」）。
- **撤退口**: Phase 1 / Phase 2 のいずれかが park 中は **層2 据置**（Vitali ルートを維持）。サンドイッチ
  載せ替えは (α)+(β) **両方** genuine になってから（片刃 genuine では層2 は閉じない）。
- **工数**: 20-40 行（載せ替え + witness 削除、Phase 1/2 が揃った後）。
- **1-session ship**: ✅（Phase 1/2 完了後の結線）。
- **proof-log**: yes（載せ替え + witness 削除 + audit 結果を記録）。

## 工数現実性 / 1-session 最小単位

| Phase | 内容 | 工数 | genuine か | 1-session ship |
|---|---|---:|---|---|
| 0 | 接続 lemma verbatim 再確認（Read のみ） | 30-60 分 | — | ✅ |
| 1 | (β) 畳み込みエントロピー非減少 | 100-200 行 + 新規定義 | **壁なし buildable（不在 ≠ 壁）** | △〜✗ |
| 2a | Gibbs/Jensen 下界 | 40-80 行 | **buildable** | ✅ |
| 2b | DV 双対 hard direction | 大（行数不定、100-300+） | **不確実（真 moonshot 核）** | ✗ |
| 2c | LSC 組立 | 30-60 行 | **buildable**（2a+2b 揃えば plumbing） | △ |
| 3 | 層2 載せ替え + witness 削除 + audit | 20-40 行 | Phase 1/2 依存 | ✅ |

**最小有意単位（優先順）**:
1. **Phase 1（(β) 畳み込みエントロピー非減少）** — UI/UT witness を待たず独立 file で genuine 化可能。
   壁なし buildable・**EPI line / 教科書全体で再利用可能な独立資産**（連続版条件付き differential entropy +
   conditioning-reduces-entropy 基盤）。**最初の独立 ship 単位**。
2. **Phase 2a（Gibbs/Jensen 下界）** — 在庫の Gibbs 素材で組める buildable。Phase 1 と独立に着手可。
3. **Phase 2c（LSC 組立）** — 2a 完了後、2b を park したまま部分的に攻められる（2a の `F_g ≤ KL` までは
   genuine、sup 到達 = 2b のみ park）。
4. **Phase 2b（DV 双対 hard direction）** — 最難、真 moonshot 核、複数 session / Mathlib upstream PR。

## 撤退ライン（発火条件具体）

親 plan [`epi-g2-layer2-moonshot-plan.md`](epi-g2-layer2-moonshot-plan.md)「撤退ライン」+ 兄弟 plan
[`epi-g2-vitali-closure-plan.md`](epi-g2-vitali-closure-plan.md) 撤退ライン 3 を継承・精密化:

1. **Phase 1 (β) のみ genuine、Phase 2 全 park**: (α) が当該 session で全く着手できない場合の最初の
   着地。Phase 1 の (β) + 連続版条件付き differential entropy + conditioning-reduces-entropy は genuine
   `@audit:ok` で **EPI line / 教科書全体で再利用可能**。層2 は Vitali ルート据置（載せ替えしない、片刃
   genuine では閉じない）。

2. **Phase 1 (β) + Phase 2 の 2a/2c genuine、2b park（最尤の honest 着地）**: 2b の DV 双対 hard direction
   が当該 session（複数含む）で組めない場合の中間着地。壁が「DV 双対 hard direction 1 本
   （`@residual(wall:kl-lower-semicontinuous)`）」に最大絞り込みされた surface shrink。層2 は Vitali 据置
   （(α) 完成まで載せ替えない）。

3. **Phase 1 (β) park（低確率）**: conditioning ルートの disintegration で詰まったら
   `sorry` + `@residual(wall:cond-diff-entropy)`（新 wall slug、closeable 見込み高、真壁でない）。

4. **(α)+(β) 両方 genuine → 層2 載せ替え + UI/UT witness 削除（完全 closure）**: Phase 3 で層2 を
   サンドイッチに書換、`wall:approx-identity-L1` の UI/UT 2 本を削除。EPI G2 端点連続性 done、一般形を
   スコープ犠牲なしで closure。未解決の subtle question（一般形が真か）も DV 双対 closure で決着。

各撤退とも **仮説束化禁止**（KL-LSC / DV 双対 / 畳み込み単調 / conditioning 減少を `*Hypothesis`
predicate に bundle しない、tier 5）。撤退は `sorry` + `@residual(wall:cond-diff-entropy)` または
`@residual(wall:kl-lower-semicontinuous)` のみ。`condDistrib` / `klDiv` / `differentialEntropy_map_add_const`
等の genuine 補題を「呼ぶ」のは bundling でない。precondition 追加（`IsHeatFlowEndpointRegular` の
regularity field）は OK。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

7. **(2026-06-05 multi-round orchestrator session) MOONSHOT 達成 = 2b DV 双対を klFun-Fatou で回避し
   (α)+(β)+層2 全 genuine、wall:approx-identity-L1 CLOSED**:
   オーケストレーター 11 ラウンド (pivot-advisor + 在庫精査 → W1-W4 実装 → assembly scaffolding → (β) wrapper
   3 段 → (α) assembly closure → 層2 swap、監査 4 回) を実行。
   (a) **核心 pivot — 在庫の DV 双対 moonshot 判定は単一ルート過大評価だった**: 在庫 §A は `klDiv,
   LowerSemicontinuous` / `DonskerVaradhan` を Found 0 で「(α) = DV 双対 hard direction = research-level
   moonshot、park が honest」と判定。しかし **`klDiv_eq_lintegral_klFun_of_ac` (KL を ∫⁻ klFun(rnDeriv) dγ に
   書換) + klFun≥0 + Fatou (`lintegral_liminf_le`)** の間接経路で **固定ガウス確率測度 γ 上の KL 下半連続性**が
   直接出る。在庫が negMulLog を無限測度 Lebesgue 上で Fatou に乗せようとして「負部一様可積分 majorant 必須 =
   既存 wall 同型」と結論したのは、γ 上に書き換える pivot を見落としたため。memory `feedback_independent_wall_recheck`
   の実例追加 (監査・在庫は単一ルート仮定で壁を過大評価する)。
   (b) **(α) klFun-Fatou ルート (`EPIG2KLFatouLSC.lean`)**: W1 KL-LSC 本体 + W2 rnDeriv 商 base 統一 + W3
   cross-term 収束 + W4 密度 a.e. 部分列 + assembly。全 genuine sorryAx-free `@audit:ok`。真の Mathlib 壁 0 件。
   (c) **(β) 密度形 wrapper (`EPIG2ConvEntropyDensity.lean`)**: Ω-level (β) 補題を canonical Ω=ℝ×ℝ
   (`(withDensity pX).prod (gaussianReal 0 v_Z)`、X=fst/Z=snd) に instantiate、per-n regularity 前提 8 本を
   全 discharge (shift-invariance + 多項式優関数 `convDensityAdd_logFactor_poly_majorant` public 化 +
   `integrable_compProd_iff`)。genuine sorryAx-free。(α) assembly の boundedness と Phase 3 下刃に必須。
   (d) **サンドイッチの 2 刃は boundedness で交わる**: (α) assembly の ℝ≥0∞→toReal 変換に `h(μ_n)` の上有界性
   = (β) 下界が本質的に要る (klDiv≥0 は下界のみ供給)。「独立 2 刃」framing より entangled。
   (e) **Phase 3 層2 swap**: Vitali ブロックをサンドイッチ + `tendsto_of_le_liminf_of_limsup_le` に置換、
   boundedness は genuine maxent 上界 (`negMulLog_convDensityAdd_gaussian_entropy_upper`、壁非経由) で供給。
   UI/UT witness 削除、`wall:approx-identity-L1` active residual 0 件。独立 honesty audit 3 回全 PASS
   (defect/vacuity/false-generalization なし、signature 不変・非循環・非バンドル機械確認)。
   **副産物**: `CondKLIntegral.lean` (条件付き KL 積分形、Mathlib `ChainRule.lean` TODO 充足) は Mathlib
   upstream PR 候補のまま。klFun-Fatou KL-LSC も連続版 MI/DPI で再利用可能な独立資産。

6. **(2026-06-04 multi-round session) 実装結果 = Phase 2a + 補題2 genuine、補題1 = bridge 1 本に shrink**:
   オーケストレーター 5 ラウンド (在庫 → Phase 2a → 補題2 → 監査 → 補題1 → 監査) を実行。
   (a) **Phase 2a (DV easy direction) genuine 化が在庫予測を上回った**: 在庫 §結論は「easy direction も
   採用見送り (tilted-measure KL chain rule 不在)」だったが、実装は **chain rule を迂回**し
   `ConvexOn.map_integral_le` (exp の Jensen) + `integral_toReal_rnDeriv_mul` (RN change-of-measure) で
   genuine close。**在庫の工数/可否評価は経路に依存し、別経路で覆りうる教訓**。
   (b) **補題2 fibre 同定の compProd 同定が在庫見積 (40-60 行) を大幅短縮 (実質 8 行)**: `g(z,x)=(z,x+cz)`
   と kernel preimage が Lean 上で**定義的に一致**し `congr 1` 一発。在庫は measure-theoretic plumbing を
   保守的に過大評価する傾向。
   (c) **補題1 conditioning 減少は完全 genuine に至らず、単一 bridge 補題に surface shrink**: 残壁 =
   条件付き KL 積分形 (Mathlib 明示 TODO `ChainRule.lean:74-77`、`klDiv_compProd_eq_add` は周辺共通の
   本件で collapse して効かない)。non-negativity ステップ (klDiv≥0 型自明) は genuine 隔離済。
   `wall:cond-diff-entropy` 維持、独立監査 PASS。**次手 = 条件付き KL 積分形を自作 (Mathlib upstream PR
   候補)、これが (β) 完全 genuine 化の単一残壁**。

1. **(起草、2026-06-04) Phase 1 (β) を最優先にする設計判断**: サンドイッチの 2 刃のうち (β) 下界
   （畳み込みエントロピー非減少）は **壁なし buildable・再利用資産** であり、(α) 上界（KL-LSC）が真の
   wall。(β) は連続版 conditioning-reduces-entropy `h(X+√tZ) ≥ h(X+√tZ|Z) = h(X)` で出るが、in-tree/
   Mathlib に組立済み定理が無い（inventory §B: `condDifferentialEntropy` = Found 0、連続 conditioning =
   不在、畳み込み単調 = 不在）— ただしこれは **不在（未整備）であって壁ではない**。`condDistrib` 基盤は
   Mathlib 既存で、`I(X;Z) = KL(joint‖product) ≥ 0`（型自明）経由で genuine 自作可能。Phase 1 で (β) を
   独立 genuine 化すれば、連続版条件付き differential entropy + conditioning-reduces-entropy 基盤が
   EPI line / 教科書全体で再利用可能な独立資産として ship できる。これが (α) の成否に依らない this-session
   利得。よって tractable な順で Phase 1 を最優先・最初の独立 ship 単位とする。

2. **(起草) 2b（DV 双対 hard direction）が還元不能 wall の根拠**: (α) 上界 = `∫ f log f` / KL の弱/L¹-LSC
   が必要で、genuine に出す唯一の道は Donsker-Varadhan 変分公式 `KL = sup_{g bounded cts}(∫g dμ −
   log∫e^g dν)` → sup-of-weakly-continuous → LSC。DV 双対の **easy direction（2a）** = `KL ≥ ∫g − log∫e^g`
   は在庫の Gibbs/Jensen 素材（`mul_log_le_klDiv` `Basic.lean:360`、`le_integral_rnDeriv_of_ac`
   `IntegralRNDeriv.lean:49`、`convexOn_klFun`）から buildable。**hard direction（2b）** = `KL ≤ sup_g(…)`
   （sup が KL に到達）は **Mathlib 完全不在**（inventory §A authoritative: `"DonskerVaradhan"` = Found 0、
   `klDiv, iSup` = Found 0、`klDiv, Real.exp`/`Real.log`/`integral` = Found 0、`klDiv, LowerSemicontinuous`
   = Found 0、計 8 query 全 Found 0）。optimal `g* = log(dμ/dν)` を bounded cts で近似し sup を KL に到達
   させる構成は research-level で、Donsker-Varadhan 1975 の古典定理だが Mathlib 自作は moonshot。

3. **(起草) de la VP wall との同型性**: sandwich route の本体 wall（2b = DV 双対 hard direction = KL-LSC）は
   de la VP route の本体 wall（`negMulLog` 負部の tail 一様可積分 = UnifIntegrable）と **数学的に同型**。
   どちらも「tail（大きい rnDeriv 値 / 大きい `f log f` 値）の質量が逃げない一様可積分性」を要求する
   （inventory §A 所見 + §結論: 「(α) の Fatou 適用は既存 heatflow/de la VP wall を別形で再要求」）。
   よって de la VP moonshot plan の Phase 2（superlinear-moment 構成）と本 plan の Phase 2b（DV 双対 hard
   direction）は **同一核心の 2 つの定式化**であり、片方が closure すればもう片方も解ける（または同じ
   research-level 困難を共有する）。一般形を正攻法で攻める = この同型核心を DV 双対の側から自作すること。
   **shared sorry 補題化の検討**: 将来両 plan の本体 wall を 1 本の shared sorry 補題に集約する余地が
   あるが、結論型が genuinely 異なる（UnifIntegrable vs LSC）ため機械的集約は false-statement defect
   リスク（vitali-closure 判断ログ 10 と同種の caution）→ 急がず、closure 設計時に同時実施。

4. **(起草) 一般形が真かは未解決の subtle question として明記**: 定理 `h(X+√tZ) → h(X)`（`t→0⁺`）が
   一般有限 2 次モーメント + `h(X)>-∞` で真かは未確定。Barron 1986 は sub-Gaussian を示唆するが、
   compact-support 分布では tail moment 有界の反証計算がある（de la VP moonshot plan 判断ログ 7 末尾:
   compact-support 裾でも tail moment は Gaussian 減衰が log 増大を凌ぎ有界 = statement は true-but-hard の
   可能性）。**DV 双対（2b）が closure すれば真偽も決着する** — KL-LSC は Donsker-Varadhan 1975 により
   一般の有限 2 次モーメントで成り立つ古典定理であり、2b の closure は一般形の真を確定させる。この subtle
   question は de la VP route 判断ログ 7 の積み残し（true-but-hard か under-hypothesized か未解決）と同根で、
   本 route の closure が両 route の積み残しを同時に決着させる。

5. **(起草) 兄弟 2 plan（vitali-closure / delavp-moonshot）との関係 = 第 3 のルート**: 本 plan は
   `epi-g2-vitali-closure-plan.md`（現行 UI/UT witness、`wall:approx-identity-L1` park）+
   `epi-g2-delavp-moonshot-plan.md`（de la VP 機構自作、Phase 2 で真 moonshot park 確定、判断ログ 7）の
   **第 3 のルート**。delavp route は UnifIntegrable を直接攻める（superlinear-moment 構成）が、本 route は
   サンドイッチ（(β) 下界 + (α) 上界）に分解して (α) を DV 双対で攻める。**両者の本体 wall は同型**（判断ログ
   3）だが、本 route の利得は **(β) 下界が壁なし buildable・再利用資産**として独立 ship できる点（delavp
   route には (β) 相当の独立資産が無い）+ (α) を 2a/2c/2b に分解して **2a/2c を genuine 化し壁を 2b 1 本に
   絞れる**点。delavp route の Phase 1（de la VP 汎用 criterion `unifIntegrable_of_superlinear_lintegral`、
   genuine 完成・再利用可）は本 route でも再利用可能（万一 (α) を Fatou ルートで攻める場合の素材）。
   どちらの route も本体 wall（同型核心）は research-level で park が honest だが、本 route は surface shrink
   の粒度が細かい（(β) 独立資産 + 2a/2c genuine + 2b park）。
