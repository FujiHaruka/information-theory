# EPI G2 de la Vallée-Poussin 機構自作 ムーンショット計画 🌙

> **Parent**: [`epi-g2-vitali-closure-plan.md`](epi-g2-vitali-closure-plan.md) Phase B/C
> （その親: [`epi-g2-layer2-moonshot-plan.md`](epi-g2-layer2-moonshot-plan.md)）
> **対象壁**: `@residual(wall:approx-identity-L1)` 配下の **2 Vitali witness sorry**
> — de la Vallée-Poussin 機構を **自作で閉じる** 唯一の道（3 逃げ道全否定後、判断ログ 9/10/11）。
> **一次根拠 (verbatim signature 確定済、再調査不要)**:
> [`epi-g2-delavp-recheck-inventory.md`](epi-g2-delavp-recheck-inventory.md) +
> [`epi-g2-sandwich-inventory.md`](epi-g2-sandwich-inventory.md)

<!--
記法: 状態絵文字 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更(判断ログ参照)。
取り消し線 = 廃止 Phase (履歴のため残す)。判断ログ append-only。
rg "^- \[ \]" で残タスク横断 grep、rg "🔄" でピボット箇所だけ拾える。
-->

## 進捗

- [x] Phase 0 — de la VP 在庫の確定確認 ✅ (Phase 1 内で `unifIntegrable_of` verbatim 確認済)
- [x] Phase 1 — de la Vallée-Poussin 判定法の汎用補題化 ✅ **DONE 2026-06-04 (genuine, 独立監査 PASS)**。
  `InformationTheory/Shannon/DeLaValleePoussin.lean`、`unifIntegrable_of_superlinear_lintegral`
  + `def Superlinear`、0 sorry / 0 residual、sorryAx-free (`[propext, Classical.choice, Quot.sound]`)、
  `@audit:ok` (honesty-auditor 独立 PASS、commit ebb960e)。**UI 壁が「`Superlinear G` を満たす `G` の構成 +
  `sup_n ∫⁻ G(‖negMulLog f_n‖ₑ) ≤ C` (= Phase 2)」1 点に絞られた surface shrink 達成**。
- [ ] Phase 2 — superlinear moment bound の構成 🔄 **PARK (撤退ライン 3 発火 2026-06-04、判断ログ 7)**。
  独立 advisor gating = (B) 真 moonshot。有界密度は peak のみ closure、tail は sub-Gaussian 裾を要求
  (boundedness と直交) → caller 供給不能 + EPI scope 縮小。`sorry + @residual(wall:approx-identity-L1)` 維持。
- [ ] Phase 3 — UnifTight (空間 tail、UT witness) 🔄 **PARK (Phase 2 依存)**
- [ ] Phase 4 — witness 結線 + 独立 honesty audit 🔄 **保留 (Phase 2/3 closure 待ち)**

## 閉じる対象 (2 witness、verbatim)

```lean
-- EPIVitaliUI.lean:536  (de la VP bridge core、unifIntegrable_of の indicator-tail 入力)
-- 主 witness negMulLog_convDensity_unifIntegrable は unifIntegrable_of 経由で
-- 既にこの補題への genuine 還元済 (own body 0 sorry)。残るのはこの核。
theorem negMulLog_convDensity_indicatorTail_uniform
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_bdd : BddAbove (Set.range u))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ n,
      eLpNorm
        ({ x | C ≤ ‖Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x)‖₊ }.indicator
          (fun x => Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x)))
        1 volume ≤ ENNReal.ofReal ε := by sorry

-- EPIVitaliUnifTight.lean:360  (UnifTight witness)
theorem negMulLog_convDensity_unifTight
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_bdd : BddAbove (Set.range u)) :
    UnifTight (fun n => fun x =>
        Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x)) 1 volume := by sorry
```

`f_n := convDensityAdd pX (gaussianPDFReal 0 ⟨u n,_⟩) = pX ∗ g_{u n}`、`u n>0`、`u` 有界
(`hu_bdd`)、`u n→0`、`pX` 一般 L¹ 確率密度（`∫pX=1`、有限 2 次モーメント `hpX_mom`）。

## ゴール

2 witness の `sorry` を genuine 0 にし、壁 `wall:approx-identity-L1` を完全 closure する。
**ただし honest な中間着地は「Phase 1 のみ genuine 化、Phase 2/3 を park」**（下記 Approach 撤退ライン）。

## Approach

### 全体形状

```text
                    ┌─────────────────────────────────────────────────────────┐
  現状: 不透明な     │ UI witness: negMulLog_convDensity_indicatorTail_uniform  │
  2 壁              │ UT witness: negMulLog_convDensity_unifTight              │  ← wall:approx-identity-L1
                    └─────────────────────────────────────────────────────────┘
                                          │
        ┌──────────────── Phase 1 (★genuine 確実) ────────────────┐
        │ 汎用 de la VP criterion を自作:                          │
        │  「G superlinear (G(t)/t→∞), sup_i ∫⁻ G(‖f_i‖₊) ≤ C<∞ │
        │   ⟹ UnifIntegrable f 1 μ」 (μ = volume、[IsFiniteMeasure]│
        │   不要)。unifIntegrable_of の indicator-tail 形に接続。  │
        └────────────────────────────────────────────────────────┘
                                          │
                       UI 壁が「superlinear-moment 1 点」に絞られる
                                          │
        ┌──────────── Phase 2 (★本物の moonshot 核、最難) ─────────┐
        │ ∃ G superlinear, sup_n ∫⁻ G(‖negMulLog f_n‖₊) ≤ M<∞   │
        │  を構成。一般 L¹ では追加 regularity hyp が               │
        │  数学的に必要な可能性 (下記「最重要の正直さ」)。           │
        └────────────────────────────────────────────────────────┘
                                          │
        ┌──────────── Phase 3 (UT、空間 tail) ─────────────────────┐
        │ UnifTight: {|x|>R} 上 tail eLpNorm の n-一様小。          │
        │  mul_meas_ge_le_lintegral (測度非依存) + Phase 2 の       │
        │  moment bound or 2 次モーメント (convDensityAdd_second_   │
        │  moment_unif_bdd、genuine)。                              │
        └────────────────────────────────────────────────────────┘
                                          │
        ┌──────────── Phase 4 (結線 + 独立 honesty audit) ─────────┐
        │ UI/UT witness の sorry を genuine 化、@residual→@audit:ok│
        │  signature 変更を伴うなら honesty-auditor 起動。          │
        │  層2 機構 (own-sorry 0、結論型不変) への影響なし。        │
        └────────────────────────────────────────────────────────┘
```

骨子: **不透明 UI/UT 2 壁 → Phase 1（汎用 de la VP criterion、確実 genuine）で UI を
superlinear-moment 1 点に絞る → Phase 2（moment 構成、本物の moonshot）→ Phase 3（UT）→
Phase 4 結線**。Phase 1 は壁の **surface shrink** を確実に達成する（不透明 witness →
明示的 superlinear-moment bound への絞り込み）一方、Phase 2 が真の難所。

### なぜこの順序か（Phase 1 を最優先にする理由）

3 逃げ道（precondition / de Bruijn 積分 / サンドイッチ）全否定後、残るのは de la VP 機構
自作のみ（判断ログ 9/10/11）。だが de la VP 機構は 2 つの独立部品に分解できる:

1. **判定法そのもの**（superlinear-moment 一様有界 ⟹ UnifIntegrable）— これは古典的・短い・
   `[IsFiniteMeasure]` 不要で `volume` に乗る。Mathlib に Found 0（in-tree register 確認、
   `UnifIntegrable, ConvexOn = Found 0`）だが **証明は tractable**（閾値 M 抽出 + tail 上の
   `∫‖f‖ ≤ (ε/C)∫G(‖f‖) ≤ ε`）。再利用可・Mathlib upstream PR 候補。
2. **入力の供給**（superlinear-moment 一様有界の構成）— これが真の moonshot 核。

Phase 1 を先に独立 genuine 化すると、**壁が「不透明 2 witness」から「明示的 superlinear-moment
bound 1 本」に縮小**する。Phase 2 が当該 plan で閉じなくても、壁 surface は明確に絞られ
（解析ターゲットが特定された honest state）、Phase 1 の汎用補題は他 family でも再利用可能。
これが「tractable な順」で Phase 1 を最優先にする本質。

### 最重要の正直さ — Phase 2 の文献的十分条件と honest な不確実性

**Phase 1 は this-session genuine 確実だが、Phase 2（superlinear moment）が真の難所で、
一般 L¹ では追加 regularity hyp が数学的に必要な可能性がある**。これを honest に明記する:

- **thin-tail counterexample（核心障害、`EPIVitaliUnifTight.lean:318-358` の in-file note）**:
  一般 L¹ `pX`（Gauss より薄い裾）で `f_n(x) ≳ exp(-c x²)` の下界が破れ、`-log f_n` が
  super-polynomial に発散する。よって `negMulLog f_n` を `1 + x²` 型 envelope で挟むことは
  **数学的に不可能**（heuristic `|log f_n| ≲ 1+x²` は false）。これが Phase 2 を阻む。
- **文献の標準十分条件（Approach に明記、planner 判断）**: Cover-Thomas の微分エントロピー連続性
  / Barron 1986（"Entropy and the Central Limit Theorem"）級の議論で、`h(X+√tZ) → h(X)` を
  `t→0⁺` で出す標準十分条件は **有限 2 次モーメント単独では足りず**、典型的には次のいずれか
  を要求する:
  - **(C-a) `h(X) > -∞`** = `Integrable (negMulLog pX) volume`（微分エントロピー有限性）。
    これは de la VP の入力 `sup_n ∫G(|negMulLog f_n|) < ∞` の `n → ∞`（= `t → 0`）極限値
    `∫G(|negMulLog pX|)` を有限に保つために自然。**ただし判断ログ 9 が警告**: maxent は
    `∫negMulLog f_n` の符号付き上界しか供給せず、`hpX_ent` で下界を足しても `∫|f|≤M` と
    `∫G(|f|)≤M` の gap は埋まらない。`hpX_ent` 単独では Phase 2 を閉じない可能性が高い。
  - **(C-b) `pX` 有界**（`pX ∈ L^∞`）あるいは **sub-Gaussian / sub-exponential tail**。
    bounded density なら `f_n = pX ∗ g_t` も bounded で `negMulLog f_n` の正部（`f_n > 1`
    側）が制御でき、Gaussian 平滑化（`f_n` は `g_t` の smoothness を継承）で大値部の
    superlinear moment が構成できる見込み。これが Phase 2 を実際に閉じる最有力候補。
- **honest な結論**: **Phase 2 が finite 2nd moment 単独で閉じるかは未確定**。Phase 2 冒頭で
  「(i) finite 2nd moment + `hpX_ent` だけで superlinear moment が出るか」を verbatim 解析で
  判定し、出ないと確定したら **(C-b) bounded density 等の precondition 追加を検討**する
  （precondition として honest なら追加可、ただし **load-bearing 化禁止** — Phase 2 の核心
  である superlinear-moment 構成を `*Hypothesis` predicate に bundle してはならない、tier 5）。

### Gaussian 畳み込みの平滑性から moment を出す解析の骨子 (Phase 2 (ii))

`f_n = pX ∗ g_{u n}` の構造を使う方向（Phase 2 の解析骨子、planner 仮説）:

- **大値部 `f_n(x) > 1`**: `negMulLog f_n = -f_n log f_n < 0`、`|negMulLog f_n| = f_n log f_n`。
  `f_n = pX ∗ g_t ≤ ‖g_t‖_∞ · ‖pX‖_1 = (2π t)^{-1/2}`（Young）で **上から bounded**。よって
  `log f_n ≤ -½log(2πt)` で `u` 有界（`hu_bdd`）なら大値部の superlinear moment は line-moment
  `∫ x² f_n`（`convDensityAdd_second_moment_unif_bdd`、genuine、n-一様）で支配できる **見込み**。
  ただし `t = u n → 0` で `(2πt)^{-1/2} → ∞` なので n-一様性は `hu_bdd` だけでは弱く、**ここが
  難所**（`t` 下限が無いと `‖g_t‖_∞` が爆発）。
- **小値部 `0 < f_n(x) < 1`（tail）**: `negMulLog f_n = -f_n log f_n > 0`。`-log f_n` が
  super-polynomial（thin-tail `pX`）。**ここが counterexample の発火点**。bounded density や
  sub-Gaussian tail（C-b）を入れて `f_n` の下界 `f_n(x) ≳ exp(-c(1+x²))` を回復しないと、
  superlinear `G` で支配する moment が構成できない。
- **superlinear `G` の候補**: `G(s) = s · log(1+s)` あるいは `G(s) = s^p`（`p>1`）。
  `G(t)/t = log(1+t) → ∞` を満たす。`G` を `negMulLog` の絶対値に適用した
  `∫⁻ G(|negMulLog f_n|)` の n-一様有界が Phase 2 の最終ターゲット。

### 撤退ライン（honest 中間着地、仮説束化禁止）

- **honest 着地点（中間状態、type-check done）**: **Phase 1 のみ genuine 化 + Phase 2/3 を
  `@residual(wall:approx-identity-L1)` park**。壁が「不透明 witness」から「明示的
  superlinear-moment bound」に絞られた **surface shrink** が達成された状態。Phase 1 の汎用
  de la VP 補題は genuine `@audit:ok` で、他 family 再利用可。
- **Phase 2 で precondition 追加 or park の分岐**: Phase 2 冒頭の解析判定で「finite 2nd moment
  + `hpX_ent` で閉じない」と確定したら、**(a) bounded density 等の precondition 追加**（honest
  なら可、load-bearing 化禁止）か **(b) park 継続**（真 moonshot 確定）を選ぶ。park の場合も
  Phase 1 の surface shrink は残る。
- **仮説束化は全 Phase で禁止**（tier 5）: UI/UT/superlinear-moment を `*Hypothesis` /
  `*Reduction` predicate に bundle して仮説で渡すのは禁止。撤退口は必ず `sorry` +
  `@residual(wall:approx-identity-L1)` のみ。追加してよいのは **precondition（入力分布の
  regularity = bounded / sub-Gaussian / `hpX_ent`）** だけで、**UnifIntegrable / superlinear-
  moment 結論を hyp に取らない**（循環）。判定の一言（CLAUDE.md）: 「その仮説は前提条件
  （regularity）か、証明の核心（load-bearing）か」→ 前者のみ OK。

## Phase 0 — de la VP 在庫の確定確認 📋

> 在庫 (`epi-g2-delavp-recheck-inventory.md` + `epi-g2-sandwich-inventory.md`) は verbatim
> signature 確定済。Phase 0 は **新規 inventory ではなく**、Phase 1 が接続する 2 lemma の
> signature を着手直前に再 Read するだけ（CLAUDE.md「依存方向 / wrapper 呼出方向の verbatim 確認」）。

- [ ] `MeasureTheory.unifIntegrable_of` (`Mathlib/MeasureTheory/Function/UniformIntegrable.lean:653`)
  を Read し、indicator-tail 入力 `h` の形が Phase 1 の結論型と一致することを verbatim 確認。
  **要点（inventory §B verbatim）**: `[IsFiniteMeasure μ]` を **要求しない**（変数 scope 外、
  `volume` 適用可）。`uniformIntegrable_of`（大文字、`:808`）と取り違えると `[IsFiniteMeasure]`
  が混入し volume で詰む。
  - 入力 `h` の形（verbatim）:
    `(h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε)`
- [ ] `MeasureTheory.mul_meas_ge_le_lintegral` (`Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean:57`)
  を Read（Phase 1 内 tail 評価 + Phase 3 で使用）。**測度非依存版**:
  `{f : α → ℝ≥0∞} (hf : Measurable f) (ε : ℝ≥0∞) : ε * μ { x | ε ≤ f x } ≤ ∫⁻ a, f a ∂μ`。
- [ ] `convDensityAdd_second_moment_unif_bdd` (`EPIVitaliUnifTight.lean:288`、`@audit:ok` genuine)
  の結論型を再確認（Phase 3 の入力）:
  `∃ V : ℝ, ∀ n, ∫ x, x ^ 2 * convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x ∂volume ≤ V`。
- **工数**: 15-30 分（Read のみ、新規証明なし）。
- **proof-log**: no（Read のみ）。

## Phase 1 — de la Vallée-Poussin 判定法の汎用補題化 (★tractable・最優先・genuine 確実) 📋

> 古典的 de la VP criterion を `volume` で使える汎用補題として自作する。Mathlib Found 0
> （register 確認）だが **証明は短く tractable**。これで UI 壁が Phase 2 の superlinear moment
> bound 1 本に絞られる。

- **目標（自作する汎用補題の想定 signature、設計案 — Phase 1 着手時に確定）**:
  ```lean
  -- InformationTheory/Shannon/DeLaValleePoussin.lean (新 file 構想)
  -- 「G superlinear + sup_i ∫⁻ G(‖f_i‖₊) ≤ C ⟹ UnifIntegrable f 1 μ」
  theorem unifIntegrable_of_superlinear_moment
      {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {ι : Type*}
      {f : ι → α → ℝ}
      (hf : ∀ i, AEStronglyMeasurable (f i) μ)
      (G : ℝ≥0∞ → ℝ≥0∞)
      (hG_superlinear : Tendsto (fun t => G t / t) atTop atTop)  -- G(t)/t → ∞
      (hG_mono : Monotone G)                                      -- (or ConvexOn 形)
      {C : ℝ≥0∞} (hC : C ≠ ∞)
      (hbound : ∀ i, ∫⁻ x, G (‖f i x‖₊ : ℝ≥0∞) ∂μ ≤ C) :
      UnifIntegrable f 1 μ := by sorry
  -- 注: [IsFiniteMeasure μ] を付けない (volume で使う)。
  --     G の signature (ℝ≥0∞→ℝ≥0∞ か ℝ→ℝ か) は unifIntegrable_of の eLpNorm 形に
  --     合わせて Phase 1 冒頭で確定。superlinear の Lean 化 (Tendsto (G t/t) atTop atTop)
  --     も hG の使い方が出揃ってから fix。
  ```
- **証明骨子（古典 de la VP、短い）**:
  - `unifIntegrable_of`（`:653`、`[IsFiniteMeasure]` 不要）に reduce。任意 `ε>0` に対し
    `C₀ : ℝ≥0` を `G(t)/t → ∞` から「`t ≥ M ⟹ G(t)/t ≥ C/ε`」を満たす閾値 `M` で取り、
    indicator-tail `{C₀ ≤ ‖f i‖₊}` 上で `∫‖f i‖ ≤ (ε/C) ∫G(‖f i‖) ≤ (ε/C)·C = ε`。
  - tail 上の `‖f i‖ ≤ (ε/C)·G(‖f i‖)` を `mul_meas_ge_le_lintegral`（Phase 0 で確認）
    あるいは直接 monotone な pointwise 評価で持ち上げる。`eLpNorm ... 1 volume` の `1` 指数で
    `∫‖·‖` と `eLpNorm` の同定（`eLpNorm_one_eq_lintegral_nnnorm` 系）を使う。
- **鍵 Mathlib lemma（verbatim、inventory §B/§C）**:
  - `MeasureTheory.unifIntegrable_of` (`UniformIntegrable.lean:653`)
    `(hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ι → α → β} (hf : ∀ i, AEStronglyMeasurable (f i) μ) (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε) : UnifIntegrable f p μ`
    — `[IsFiniteMeasure μ]` **無し**（volume 適用可）。indicator-tail 入力ゲートウェイ。
  - `MeasureTheory.mul_meas_ge_le_lintegral` (`Lebesgue/Markov.lean:57`)
    `{f : α → ℝ≥0∞} (hf : Measurable f) (ε : ℝ≥0∞) : ε * μ { x | ε ≤ f x } ≤ ∫⁻ a, f a ∂μ`
    — 測度非依存。
- **自作補助**: 上記 `unifIntegrable_of_superlinear_moment` 1 本。`G(t)/t → ∞` から閾値 `M` を
  取る部分が補助 `have`（`Tendsto.eventually_ge_atTop` 系）。
- **工数**: 推定 30-60 行、genuine、再利用可・Mathlib upstream PR 候補。
- **1-session ship**: ✅（独立 file で genuine 化可能、UI/UT witness を待たない）。
- **撤退口**: criterion の Lean 化が `unifIntegrable_of` の indicator 形と繋がらない場合のみ
  `sorry` + `@residual(wall:approx-identity-L1)`（低確率）。**仮説束化禁止**。
- **closure 見込み判定**: **genuine 確実**。古典 de la VP の forward 方向（superlinear-moment →
  UI）は標準的で、Mathlib 不在は単に未整備（loogle 0 件 = honest gap）であって数学的障害ではない。
- **proof-log**: yes（汎用補題の signature 確定 + 証明）。

## Phase 2 — superlinear moment bound の構成 (★本物の moonshot 核、最難) 📋

> `∃ G superlinear, sup_n ∫⁻ G(‖negMulLog f_n‖₊) ∂volume ≤ M < ∞` を構成。**これが壁の本体**。
> Phase 1 の汎用補題に食わせる入力を作る。正直に: **一般 L¹ では閉じない可能性が高い**。

- **目標**:
  ```lean
  -- Phase 1 の unifIntegrable_of_superlinear_moment に渡す入力
  -- f_n := convDensityAdd pX (gaussianPDFReal 0 ⟨u n,_⟩)
  ∃ (G : ℝ≥0∞ → ℝ≥0∞) (M : ℝ≥0∞), M ≠ ∞ ∧
    (Tendsto (fun t => G t / t) atTop atTop) ∧
    (∀ n, ∫⁻ x, G (‖Real.negMulLog (f_n x)‖₊ : ℝ≥0∞) ∂volume ≤ M)
  ```
- **検討すべき問い（planner 判断、Phase 2 冒頭で verbatim 確認）**:
  - **(i) 一般 L¹ + 有限 2 次モーメントだけで閉じるか**: **NO の見込み**。判断ログ 9 +
    thin-tail counterexample（`EPIVitaliUnifTight.lean:318-358`）。小値部 tail で `-log f_n` が
    super-polynomial、superlinear `G` で支配する moment が出ない。**追加 regularity hyp が
    数学的に必要な可能性が高い** — 文献標準十分条件は **(C-b) bounded density `pX ∈ L^∞` or
    sub-Gaussian tail**（Approach「最重要の正直さ」）。`hpX_ent`（`h(X)>-∞`）単独は判断ログ 9
    で「`∫|f|≤M` と `∫G(|f|)≤M` の gap を埋めない」と判定済 → **(C-b) が最有力**。
  - **(ii) Gaussian 畳み込みの平滑性ルート**: `f_n = pX ∗ g_t`。大値部は Young
    `f_n ≤ (2πt)^{-1/2}` で bounded（ただし `t→0` で発散、`hu_bdd` の下限欠如が難所）、小値部は
    bounded density / sub-Gaussian で下界 `f_n ≳ exp(-c(1+x²))` を回復（Approach 骨子）。
    superlinear `G(s) = s·log(1+s)` or `s^p` 候補。
  - **(iii) 当該 plan で閉じない場合の honest park**: `sorry` + `@residual(wall:approx-identity-L1)`
    維持。Phase 1 で壁が「superlinear-moment 1 本」に絞られた surface shrink 状態は残る。
- **鍵 Mathlib / in-tree lemma（verbatim）**:
  - `convDensityAdd_second_moment_unif_bdd` (`EPIVitaliUnifTight.lean:288`、`@audit:ok` genuine)
    — `∃ V, ∀ n, ∫ x, x²·f_n ∂volume ≤ V`（line-moment n-一様、大値部支配の足場）。
  - `Real.negMulLog_le_one_sub_self` (`NegMulLog.lean:234`)
    `{x : ℝ} (h0 : 0 ≤ x) : x.negMulLog ≤ 1 - x` — 正部上界（**1 次線形、superlinear majorant
    は出ない** ことに注意、inventory §C）。
  - `differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:520`、maxent)
    — **符号付き上界のみ**供給（判断ログ 9、de la VP gap の本質）。superlinear moment には
    直接届かない。
  - （bounded density ルート採用時）Young の不等式系 / `convolution` の `L^∞` 評価
    — Phase 2 着手時に loogle で in-tree/Mathlib 在庫を verbatim 確認（`Real.negMulLog,
    MeasureTheory.Integrable = Found 0` は既知、bounded conv は別途確認要）。
- **自作補助（最重要、in-tree/Mathlib 不在）**:
  - [ ] superlinear `G` の選定 + `G(t)/t → ∞` の証明（`G(s)=s·log(1+s)` 等）。
  - [ ] `∫⁻ G(‖negMulLog f_n‖₊)` の n-一様有界 — **本体 moonshot**。大値部（Young bounded）+
    小値部（bounded/sub-Gaussian 下界）の 2 領域分割。
  - [ ] （precondition 追加時）bounded density `pX ∈ L^∞` or sub-Gaussian の hyp threading。
- **工数**: 大（60-150 行 + 場合により signature 追加）。
- **1-session ship**: ✗ 見込み。
- **撤退口**: 上記 (iii)。bounded density precondition を入れても superlinear moment が組めない、
  あるいは bounded density が caller（`IsHeatFlowEndpointRegular`、一般 L¹ 密度のみ保有）から
  供給できないと判明 → `sorry` + `@residual(wall:approx-identity-L1)` park 確定（真 moonshot）。
  **仮説束化禁止**（superlinear-moment 構成を `*Hypothesis` predicate に bundle しない、tier 5）。
- **closure 見込み判定**: **不確実（真の moonshot 核）**。bounded density precondition なら閉じる
  見込みだが、(1) その precondition が caller から honest に供給できるか、(2) 一般 L¹ を諦める
  ことが EPI G2 の数学的 scope として許容か、を Phase 2 で判定。許容できなければ park。
- **proof-log**: yes（superlinear moment 構成の試行 + 閉じる/park の判定を記録）。

## Phase 3 — UnifTight (空間 tail、UT witness) 📋

> `negMulLog f_n` の `UnifTight` を `{|x|>R}` 上の tail eLpNorm n-一様小で出す。UI（値 tail）と
> UT（空間 tail）の関係を明示。

- **目標（UT witness、verbatim 再掲）**:
  ```lean
  UnifTight (fun n => fun x =>
      Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x)) 1 volume
  -- UnifTight 定義 (UnifTight.lean:59):
  --   ∀ ε>0, ∃ s, μ s ≠ ∞ ∧ ∀ i, eLpNorm (sᶜ.indicator (f i)) p μ ≤ ε
  ```
- **UI（値 tail）と UT（空間 tail）の関係**: UI は **値しきい値** `{C ≤ ‖f i‖}` 上の indicator
  eLpNorm（大きい値の寄与）を制御。UT は **空間集合** `sᶜ = {|x|>R}` 上の indicator eLpNorm
  （遠方の寄与）を制御。2 つは独立な条件（Vitali `tendsto_Lp_of_tendsto_ae` は両方を入力に要求、
  inventory §B）。UT は `[IsProbabilityMeasure]` framing 不要で `volume` 上に直接組める点が UI
  と異なる。
- **証明骨子**: `s = Icc (-R) R`（`volume s = 2R < ∞`）を取り、`{|x|>R}` 上で
  `negMulLog f_n` の Lp ノルムを density-weighted tail moment で n-一様小にする:
  `mul_meas_ge_le_lintegral`（測度非依存）+ Phase 2 の moment bound（あれば直接）or
  `convDensityAdd_second_moment_unif_bdd`（genuine、2 次モーメント n-一様）。`negMulLog` の
  符号構造（`x→∞` で `-∞`）ゆえ tail 上 `|negMulLog f_n|` を `f_n` の 2 次モーメント tail に
  結びつける（UI と同根の障害だが、UT は `sᶜ` 上 Lp 小だけで majorant 不要）。
- **鍵 Mathlib / in-tree lemma（verbatim）**:
  - `MeasureTheory.mul_meas_ge_le_lintegral` (`Lebesgue/Markov.lean:57`、Phase 0 で確認、測度非依存)。
  - `convDensityAdd_second_moment_unif_bdd` (`EPIVitaliUnifTight.lean:288`、`@audit:ok`)。
  - `MeasureTheory.unifTight_finite` (`UnifTight.lean:191`、`[Finite ι]`) — 有限 prefix 補助。
  - **回避対象**: `meas_ge_le_variance_div_sq` (`Variance.lean:397`) は `[IsFiniteMeasure μ]`
    要求で `volume` 不可（inventory §C verbatim 確認済）。`mul_meas_ge_le_lintegral` で代替。
- **自作補助**: tail tightness 評価（`{|x|>R}` 上 eLpNorm を 2 次モーメント tail で抑える）。
  Phase 2 の superlinear moment が出ていれば、より強い majorant が使えて短縮。
- **工数**: 30-60 行。
- **1-session ship**: △（2 次モーメント補助は genuine 在庫、tail 評価を 1 session で組めれば）。
- **撤退口**: `hpX_mom`（2 次モーメント）だけから tail tightness が `negMulLog` 負部
  （`x>1` の `-f_n log f_n` 発散）を n-一様制御できないと確定 → Phase 2 の moment bound に依存
  （Phase 2 park なら UT も park）か、bounded density precondition 追加。`sorry` +
  `@residual(wall:approx-identity-L1)`。**仮説束化禁止**。
- **closure 見込み判定**: **Phase 2 依存**。Phase 2 の superlinear moment が出れば UT は plumbing。
  Phase 2 park なら UT も park（同壁集約）。
- **proof-log**: yes（tail tightness の genuine 化 / Phase 2 依存度を記録）。

## Phase 4 — witness 結線 + 独立 honesty audit 📋

> Phase 1-3 が揃えば UI/UT witness の sorry を genuine 化、`@residual` → `@audit:ok`。
> signature 変更を伴うなら honesty-auditor 起動。

- **タスク**:
  - [ ] Phase 1 の `unifIntegrable_of_superlinear_moment` に Phase 2 の superlinear moment bound
    を渡し、UI witness `negMulLog_convDensity_indicatorTail_uniform`（`EPIVitaliUI.lean:536`）の
    sorry を genuine 化。主 witness `negMulLog_convDensity_unifIntegrable` は既に
    `unifIntegrable_of` 経由で genuine 還元済（own body 0 sorry）なので、core が埋まれば transitive
    に閉じる。
  - [ ] UT witness `negMulLog_convDensity_unifTight`（`EPIVitaliUnifTight.lean:360`）の sorry を
    Phase 3 で genuine 化。
  - [ ] 各 witness の `@residual(wall:approx-identity-L1)` を `@audit:ok` に変更。壁
    `wall:approx-identity-L1` の register 行（`docs/audit/audit-tags.md`）を CLOSED 更新は
    orchestrator 判断。
- **signature 変更時の honesty-auditor 起動**: Phase 2 で bounded density / sub-Gaussian 等の
  **precondition を witness signature に追加**した場合、CLAUDE.md 起動条件「既存 declaration の
  signature を変更して honesty 関連の意味が変わる」に該当 → 実装 session で **`honesty-auditor`
  を 1 件起動必須**。verify 対象:
  - (i) 追加 field が全て **precondition（regularity、load-bearing でない）**。
  - (ii) Phase 1 の汎用補題 `unifIntegrable_of_superlinear_moment` が genuine（superlinear-moment
    結論を hyp に bundle していない）。
  - (iii) `@residual(wall:approx-identity-L1)` 分類の正しさ（genuine 化後の transitive 状態）。
- **層2 機構への影響なし（verbatim 確認）**: 層2 `differentialEntropy_convDensity_integral_tendsto`
  （`EPIG2HeatFlowContinuity.lean:206`、own-sorry 0）+ 壁補題
  `heatFlowEntropyPower_continuousWithinAt_zero`（`EPIG2HeatFlowContinuity.lean:531` 近傍、
  結論型不変）は witness 内部の埋めのみで影響を受けない。Phase 4 着手時に層2 → witness の
  呼出鎖を verbatim 再確認（CLAUDE.md「wrapper 呼出方向の verbatim 確認」）。**ただし witness
  signature に precondition を追加した場合は層2 / 壁補題 helper への threading が必要**
  （`IsHeatFlowEndpointRegular`（`EPIG2:455`）が一般 L¹ 密度のみ保有 — bounded density を
  追加する場合 caller の supply 元から再設計が要るため、Phase 2 の precondition 選定時に
  threading 可否を verbatim 確認）。
- **工数**: 20-40 行（結線、UI/UT が揃った後）。
- **1-session ship**: ✅（Phase 1-3 完了後の結線）。
- **proof-log**: yes（結線 + audit 結果を記録）。

## 工数現実性 / 1-session 最小単位

| Phase | 内容 | 工数 | genuine か | 1-session ship |
|---|---|---:|---|---|
| 0 | 在庫確定確認（Read のみ） | 15-30 分 | — | ✅ |
| 1 | 汎用 de la VP criterion | 30-60 行 | **genuine 確実** | ✅ |
| 2 | superlinear moment 構成 | 60-150 行 + 場合により sig 追加 | **不確実（真 moonshot 核）** | ✗ |
| 3 | UnifTight（空間 tail） | 30-60 行 | Phase 2 依存 | △ |
| 4 | witness 結線 + audit | 20-40 行 | Phase 1-3 依存 | ✅ |

**最小有意単位（優先順）**:
1. **Phase 1（汎用 de la VP criterion）** — UI/UT witness を待たず独立 file で genuine 化可能。
   壁の surface shrink を確実に達成（不透明 witness → 明示 superlinear-moment bound）。Mathlib
   upstream PR 候補。**最優先の独立 ship 単位**。
2. **Phase 3（UT）** — Phase 2 の moment が出ていなくても 2 次モーメント在庫
   （`convDensityAdd_second_moment_unif_bdd`、genuine）で部分的に攻められる可能性。
3. **Phase 2（superlinear moment）** — 最難、precondition 判定 + 複数 session。

## 撤退ライン（発火条件具体）

親 plan [`epi-g2-vitali-closure-plan.md`](epi-g2-vitali-closure-plan.md) の撤退ライン 3
（縮退 honest resting state）を継承・精密化:

1. **Phase 1 のみ genuine 化、Phase 2/3 park（最尤の honest 着地）**: Phase 2 の superlinear
   moment が当該 session（複数含む）で構成できない場合の中間着地。壁が「不透明 2 witness」から
   「明示的 superlinear-moment bound 1 本（Phase 1 補題に食わせる入力）」に絞られた surface
   shrink。Phase 1 補題は genuine `@audit:ok`、他 family 再利用可。UI/UT witness は
   `sorry` + `@residual(wall:approx-identity-L1)` park 継続。

2. **Phase 2 で precondition 追加（bounded density / sub-Gaussian）が必要と確定**: finite 2nd
   moment + `hpX_ent` で閉じないと verbatim 解析で確定したら、(a) bounded density precondition を
   honest に追加（caller `IsHeatFlowEndpointRegular` からの supply 可否を verbatim 確認）か
   (b) park。precondition 追加は **regularity であって load-bearing でない**（Phase 4 で
   honesty-auditor 検証）。bounded density が EPI G2 の数学的 scope として許容できない、あるいは
   caller から供給不能なら (b) park。

3. **Phase 2 が precondition 追加でも閉じない**: 真 moonshot 確定（Mathlib upstream PR or
   in-tree 自作で複数 session）。UI/UT を `@residual(wall:approx-identity-L1)` park 確定、
   Phase 1 の surface shrink のみ残す。

各撤退とも **仮説束化禁止**（UI/UT/superlinear-moment を `*Hypothesis` predicate に bundle
しない、tier 5）。撤退は `sorry` + `@residual(wall:approx-identity-L1)` のみ。maxent /
`convDensityAdd_second_moment_unif_bdd` 等の genuine 補題を「呼ぶ」のは bundling でない。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(起草、2026-06-04) Phase 1 を最優先にする設計判断**: de la VP 機構は 2 部品に分解できる
   — (a) 判定法そのもの（superlinear-moment → UnifIntegrable）と (b) 入力の供給（superlinear-
   moment 構成）。(a) は古典的・短い・`[IsFiniteMeasure]` 不要で `volume` に乗り、Mathlib Found 0
   は単なる未整備（honest gap）であって数学的障害でない。Phase 1 で (a) を独立 genuine 化すると
   壁が「不透明 2 witness」から「明示的 superlinear-moment bound 1 本」に縮小する surface shrink
   を **確実に達成**できる。これが Phase 2（真 moonshot 核）の成否に依らない this-session 利得。
   よって tractable な順で Phase 1 を最優先。

2. **(起草) Phase 2 の文献的十分条件として bounded density / sub-Gaussian を最有力と仮定**:
   判断ログ 9（親 plan）が `hpX_ent`（`h(X)>-∞`）単独では「`∫|f|≤M` と `∫G(|f|)≤M` の gap を
   埋めない」と判定済のため、`hpX_ent` 単独では Phase 2 を閉じない見込み。文献（Cover-Thomas
   微分エントロピー連続性 / Barron 1986）の標準十分条件は有限 2 次モーメント単独では足りず、
   typically bounded density（`pX ∈ L^∞`）or sub-Gaussian tail を要求する。Gaussian 畳み込み
   `f_n = pX ∗ g_t` の構造（大値部 Young bounded、小値部 bounded/sub-Gaussian で下界回復）から
   superlinear moment を出す解析骨子は bounded density で成立する見込み。**ただし honest に
   未確定**: (1) bounded density precondition が caller `IsHeatFlowEndpointRegular`（一般 L¹
   密度のみ保有）から供給できるか、(2) 一般 L¹ を諦めることが EPI G2 の数学的 scope として
   許容か、を Phase 2 で判定する。許容/供給不能なら park（撤退ライン 3）。

3. **(起草) thin-tail counterexample を Phase 2 の核心障害として明示**: `EPIVitaliUnifTight.lean:
   318-358` の in-file note（genuine attempt が反例確定）— 一般 L¹ thin-tail `pX` で
   `f_n(x) ≳ exp(-c x²)` の下界が破れ、`-log f_n` が super-polynomial。`1+x²` 型 envelope は
   数学的に不在（heuristic `|log f_n| ≲ 1+x²` が false）。これが Phase 2 の小値部 tail を阻む
   発火点。bounded density / sub-Gaussian で下界 `f_n ≳ exp(-c(1+x²))` を回復しない限り
   superlinear `G` で支配する moment は構成できない。

4. **(起草) maxent 上界は Phase 2 に直接使えないことを明示**: `differentialEntropy_le_gaussian_
   of_variance_le`（`DifferentialEntropy.lean:520`、verbatim 確認済）は `∫negMulLog f_n` の
   **符号付き上界のみ**供給（判断ログ 9）。de la VP が要求する `∫G(|negMulLog f_n|) ≤ M`
   （superlinear-moment 一様有界）には届かない。maxent は UI witness の現 framing（`withDensity`
   確率測度 + `differentialEntropy μ_n = ∫negMulLog f_n` 同定、genuine）で `∫negMulLog f_n` の
   n-一様上界を出すのに使われているが、これは `∫|f|≤M` であって `∫G(|f|)≤M` ではない。Phase 2 は
   maxent と別ルート（Gaussian 畳み込み平滑性）で superlinear moment を組む。

5. **(起草) 3 逃げ道全否定後の唯一ルートとして起草**: precondition 追加（判断ログ 9 NO-GO）/
   de Bruijn 積分（判断ログ 10 カテゴリ違い dead end）/ サンドイッチ分解（判断ログ 11 採用見送り、
   α が de la VP 同型を再要求 + β が `stamToEPIBridge_holds` open + 条件付き differential entropy
   不在）が全否定済。本 plan は近道探しを終え、de la VP 機構そのものを自作する moonshot。
   Phase 1（汎用 criterion、tractable・genuine・再利用可）で不透明 UI/UT 壁を 1 点の解析ターゲット
   （superlinear moment 構成 = Phase 2、本物の moonshot 核）に絞り込むのが本 plan の戦略的価値。

6. **(2026-06-04 Phase 1 実装) `Superlinear` 述語を退化 Tendsto 形から閾値形に矯正 (Phase 2 接続点訂正)**:
   Phase 1 起草案の `hG_superlinear : Tendsto (fun t => G t / t) atTop atTop` (`t : ℝ≥0∞`) は **退化**と
   実装で判明 — `ℝ≥0∞` は `OrderTop` で `⊤ = ∞`、`Ici ∞ = {∞}` が `atTop` に属するため `Filter.atTop`
   が `{∞}` 主フィルタに潰れ、`Tendsto (G·/·) atTop atTop` は `∞` 1 点評価の空虚命題になる
   (CLAUDE.md「Mathlib-shape-driven Definitions」の退化定義罠を実コードで回避)。代わりに non-degenerate な
   **閾値形 `def Superlinear G := ∀ K:ℝ≥0∞, ∃ M:ℝ≥0, ∀ t:ℝ≥0∞, (M:ℝ≥0∞) ≤ t → K * t ≤ G t`** を採用
   (古典「G(t)/t→∞」の正しい ℝ≥0∞ 表現、`G(t)=t²` で satisfiable、独立監査が非循環・非空虚を PASS)。
   **Phase 2 への影響**: Phase 2 は `G` を構成して `Superlinear G` (閾値形) を満たす必要がある。plan 本文の
   Phase 2 が `Tendsto (G·/·) atTop atTop` 前提で書いた箇所は **この `Superlinear G` 述語に読み替える**。
   superlinear `G(s)=s·log(1+s)` or `s^p` 候補は閾値形でも素直に満たせる (`K*t ≤ s·log(1+s)` の M 抽出)。
   主定理の最終 signature: `unifIntegrable_of_superlinear_lintegral {f : ι→α→ℝ} (hf : ∀ i, AEStronglyMeasurable (f i) μ) (G : ℝ≥0∞→ℝ≥0∞) (hG_superlinear : Superlinear G) {C : ℝ≥0∞} (hC : C ≠ ∞) (hbound : ∀ i, ∫⁻ x, G (‖f i x‖ₑ) ∂μ ≤ C) : UnifIntegrable f 1 μ` (`[IsFiniteMeasure]` 非要求、volume 適用可)。

7. **(2026-06-04 Phase 2 gating) 真 moonshot 確定 (撤退ライン 3 発火) + 「(C-b) bounded density 最有力」訂正**:
   独立 advisor が Phase 2 仮説十分性を3問 (Q1 最小条件 / Q2 領域分解 / Q3 caller 供給) で解析、gating = **(B)
   真 moonshot → park**。**核心訂正**: 判断ログ 2 + Approach「最重要の正直さ」が「(C-b) bounded density 最有力」
   としたのは **誤り**。bounded density (`pX≤B`) は畳込み `f_n=pX∗g_t≤B` で **peak 領域 (`f_n≥1`) のみ一様 closure**
   するが、**tail 領域 (`f_n<1`) の thin-tail counterexample (`-log f_n` super-polynomial) は density の上限でなく
   tail の下限 (sub-Gaussian `f_n≳exp(-c(1+x²))`) に支配され、boundedness と直交**。最小十分条件は **sub-Gaussian
   (or compact-support) tail** であって bounded density ではない (Barron 1986 級)。Q3: `IsHeatFlowEndpointRegular`
   (`EPIG2HeatFlowContinuity.lean:474-489`、field verbatim 確認 = `hpX_nn/meas/law/int/mass/mom/ent`) に
   bounded/sub-Gaussian field 無し。sub-Gaussian を入れると EPI G2 が「sub-Gaussian 入力限定」に弱まり EPI 本体の
   一般性を犠牲 → honest precondition の範囲外 (load-bearing 寄り scope 改変)。bounded density は tail 非 closure で
   **無益** (scope 縮小だけ払う)。**honest 着地 = Phase 1 surface shrink で park**。再着手の唯一ルート = sub-Gaussian
   限定版を別定理で立てる (案 C、EPI 一般性犠牲、60-150 行) or de la VP + Gaussian 平滑化裾下界を Mathlib upstream PR。
   付随 honesty note: thin-tail in-file 記述は **proof route の反例**であって UI/UT statement の偽証明ではない
   (compact-support 裾でも tail moment は Gaussian 減衰が log 増大を凌ぎ有界)。statement の真偽 (true-but-hard か
   under-hypothesized か) は未解決の subtle question として残るが、現 park は過去の独立 honesty-auditor PASS
   (statement honest 判定済) に依拠して honest。将来 closure 時に sub-Gaussian precondition の要否で再判定。
