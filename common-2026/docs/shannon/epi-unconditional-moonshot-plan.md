# EPI 無条件化 — entropyPower 再型付け + 3-case 分岐 ムーンショット計画 🌙

> **目標**: 主定理 `entropy_power_inequality` を **全仮説除去した無条件形**にする。
> 現状 (`EntropyPowerInequality.lean:289`) は `(hX hY : Measurable) (hXY : IndepFun X Y P)
> (h_stam : IsStamInequalityResidual X Y P)` を取るが、`h_stam` も密度 regularity も無い、
> **独立性 + 可測性のみ**からの EPI を達成する。
> **slug**: `epi-unconditional-moonshot-plan` (本 plan は傘 umbrella。各 sub-plan の slug は §sub-plan 一覧)。

<!--
記法: 状態絵文字 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更(判断ログ参照)。
取り消し線 = 廃止 Phase (履歴のため残す)。判断ログ append-only。
rg "^- \[ \]" で残タスク横断 grep、rg "🔄" でピボット箇所だけ拾える。
-->

## 規模見積りサマリ (冒頭)

| 項目 | 値 |
|---|---|
| 新規行数オーダー | **~1500–2500 行** (定義二層 + coercion bridge ~300、downstream re-port ~800–1400、3-case assembly ~400–600) |
| touch file 数 | **~38–40 file** (`differentialEntropy` 36 file + `entropyPower` 11 file、重複あり実数 ~40)。ただし下層 (a) Real workhorse を温存する設計のため、大半は **statement 層だけの shim 経由 re-port** に圧縮可能 |
| 最大の wall 候補 | **(W-A) a.c. EPI core** (既存 `stamToEPIBridge_holds` 系の残 sorry。本 plan の責務外、既存 plan 群で進行)。先行調査で **有限分散+有限エントロピーの隠れ regularity が判明** (発見 3) → 射程縮小、要スコープ判断。**(W-B) 混合 case** — 先行調査で **GO/soft 確定** (発見 2、既存 2 補題 + convolution-a.c. 3 行)。**(W-C) coercion 整合** — 先行調査で **解決** (発見 1、`EReal.exp` 実在で非分岐定義可)。真の残 wall は方針 Y を取る場合の **entropy power 弱収束 半連続性** (Mathlib 完全不在、新規) のみ |

**致命的前提 (実コード verbatim 確認済、§Phase 0 の出発点)**: 現定義のままだと無条件 EPI は
**literally FALSE**。`differentialEntropy (Measure.dirac m) = 0` (`DifferentialEntropy.lean:155`
`differentialEntropy_dirac`)、`entropyPower μ := Real.exp (2 * differentialEntropy μ)`
(`EntropyPowerInequality.lean:102`) ⇒ Dirac で `entropyPower = exp 0 = 1`、かつ
`entropyPower_pos` (`:109`) で常に `> 0`。定数 X,Y (独立自明) で 3 項とも 1、左辺 1 ≥ 右辺 2 が
矛盾。根本原因: `differentialEntropy` が rnDeriv の a.c. 部のみ見て `negMulLog 0 = 0` のため
特異測度で `0` に退化 (`-∞` にならない)。現条件付き定理が `h_stam` を load-bearing に持つのは
この退化反例を除外するため。

## 先行調査の結論 (2026-06-05、wall 3 本 verbatim 裏取り済)

3 inventory で壁候補を先行調査。結論を計画に反映。

### 発見 1 (定義 shape, W-C) — GO、設計が簡素化
`docs/shannon/epi-uncond-entropypower-retype-inventory.md`。
- **`Real.exp` ℝ≥0∞ 版不在の前提は覆る**: `EReal.exp : EReal → ℝ≥0∞` が実在
  (`Mathlib/Analysis/SpecialFunctions/Log/ERealExp.lean`、loogle 48 宣言、orchestrator 裏取り済)。
  `EReal.exp_bot : exp ⊥ = 0`、`EReal.exp_coe : exp ↑x = ENNReal.ofReal (Real.exp x)`、
  `EReal.exp_monotone` [gcongr]、`EReal.exp_top`。
  ⇒ **`entropyPower μ := EReal.exp (2 * differentialEntropyExt μ)` の非分岐定義**が可能。
  case-split は `differentialEntropyExt : EReal` 側に一元化 (特異で `⊥`、a.c. で `↑(workhorse)`)。
- **a.c. 判定の definitional 化 GO**: `Decidable (μ ≪ volume)` は不在だが、Mathlib `klDiv`
  (`Mathlib/InformationTheory/KullbackLeibler/Basic.lean:55-58`) が `open Classical in` +
  `irreducible_def` + `if μ ≪ ν then ... else ...` を実運用する precedent。
  `haveLebesgueDecomposition_of_sigmaFinite` (priority 100 instance) が確率測度 on ℝ で自動発火。
- 新規 primitive 自作 0、bridge ~6 本 (~30-40 行)。新撤退ライン候補 L-Uncond-0-δ:
  `EReal.mul` の `2 * ⊥` / `(2:EReal) * ↑x` 挙動が想定外なら ℝ≥0∞ 直接 case-split 定義へ退避。

### 発見 2 (混合 case, W-B) — GO、soft、隠れ壁なし
`docs/shannon/epi-uncond-mixed-case-inventory.md`。
- 混合 case core `h(X) ≤ h(X+Y)` は既存 genuine 2 補題
  (`condDifferentialEntropy_le` `:224` + `condDifferentialEntropy_indep_add_eq` `:328`、両 `@audit:ok`)
  の `c=1` 合成で **そのまま typecheck**。残る穴は `μ.map(X+Y) ≪ volume` の 1 点のみ。
- その 1 点 (`X a.c. ⟹ X+Y a.c.`) は Mathlib に存在: `IndepFun.map_add_eq_map_conv_map` →
  `Measure.conv_comm` → `Measure.conv_absolutelyContinuous` の **3 行で 0 sorry** (撤退ライン不発)。
  注意: `conv_absolutelyContinuous` は a.c. 因子を右に要求する非対称形 → `conv_comm` を 1 段噛ます。
- ℝ≥0∞ lift は `Real.exp_le_exp` + `ENNReal.ofReal_le_ofReal` 標準。`[StandardBorelSpace]` 不要。
- blocker (壁でない): `condDifferentialEntropy_le` の integrability precondition 8 本の threading 量。
  Gaussian 版 `differentialEntropy_indep_gaussian_add_ge` `:378` が同型 threading の雛形。非 load-bearing。

### 発見 3 (a.c. core, W-A) — ⚠ 「無条件」の射程を縮める。要スコープ判断
`docs/shannon/epi-uncond-ac-density-witness-inventory.md`。
- **verdict: case-1 (両 a.c.) EPI は「真に一般 a.c.」では閉じない。有限分散 + 有限微分エントロピーを隠し持つ。**
- assembly `isStamToEPIScalingHyp_of_stam_debruijn` の density-witness は **生入力**
  `P.map X` / `P.map Y` / `P.map (X+Y)` に課される (`EPIStamToBridge.lean:1413/1419/1425`、
  heat-flow 平滑後ではない — wall lemma endpoint は t→0⁺ で平滑が消える生入力点)。
- `IsHeatFlowEndpointRegular` (`EPIG2HeatFlowContinuity.lean`) は **8 density field**
  (`pX`/`hpX_nn`/`hpX_meas`/`hpX_law`/`hpX_int`/`hpX_mass`/`hpX_mom`/`hpX_ent`)。
  assembly の density sorry は **8×3 = 24 個** が正 (旧記載「21」「7 field」は assembly docstring
  `:1307` の `hpX_ent` 脱落由来の誤り、本計画で訂正)。
  - `hpX_mom`: `Integrable (fun y => y^2 * pX y) volume` = **有限 2 次 moment (有限分散)**。a.c. から自動で出ない (Cauchy 反例)。
  - `hpX_ent`: `Integrable (fun x => Real.negMulLog (pX x)) volume` = **有限微分エントロピー**。a.c.+有限分散からも出ない。project が「L¹+2次moment ⟹ negMulLog 可積分」を **false-as-stated と判定して削除済** (`EPIG2HeatFlowContinuity.lean:485` 周辺 docstring) ⇒ honest な追加前提として持つしかない (`@residual(wall:...)` 不可)。
  - 残 6 field は a.c.+確率測度から R-N で自動。
- 余波: `fisherInfo`/`differentialEntropy` は project-local (Mathlib 不在、loogle unknown)。将来 upstream 時 scope 大。

### ⇒ 達成可能な「無条件」の honest な射程 (要ユーザー判断)
退化トラップ除去 (特異入力 → entropyPower 0) は cases 2/3 で**追加前提なし**に達成できる (発見 1+2)。
しかし a.c. ブランチの heat-flow/de Bruijn 証明路は **有限分散 + 有限微分エントロピー**を本質的に要求する (発見 3)。
これは証明技法由来 (Fisher info が heat path 上で有限である必要) で、ただ落とすことはできない。よって:

- **方針 X (regularity-scoped, 推奨)**: `h_stam` と密度 predicate 仮説束を除去するが、a.c. 入力に
  **有限分散 + 有限微分エントロピー**を honest な regularity precondition として残す。教科書 EPI の標準射程
  (densities + finite variance 前提) と一致。本計画の Phase 構造はこれを前提に組める = 達成可能。
- **方針 Y (truly hypothesis-free)**: さらに有限分散も除く。任意 a.c. を有限分散で近似し極限を取る
  truncation/approximation 論法が要る。だが entropy power の弱収束下半連続性は **Mathlib 完全不在**
  (発見 3 + epi-g2-main-closure-inventory「entropy/KL 半連続性 loogle Found 0」) で、これ自体が新規 wall。
  別 moonshot 規模、しかも genuine Mathlib 壁を含む。

→ Phase 3/5 の最終 signature をどちらに置くかをユーザーに確認後、確定する (下記 §スコープ判断)。

## スコープ判断 — **DECIDED: 方針 Y (真に仮説ゼロ)** (2026-06-05、ユーザー確定)

最終主定理は独立性 + 可測性のみ。a.c. ブランチの有限分散 + 有限微分エントロピーも除く。
撤退ライン **L-Uncond-3-scope** = 「方針 Y が semicontinuity wall で genuine に詰まったら、
有限分散+有限エントロピーを honest precondition として残す方針 X に縮退して着地」(honest 後退口、tier 2)。

### 方針 Y の機構 (新クリティカルパス) — § Phase Y / sub-plan S5

a.c. ブランチで生入力に regularity を課す根因は **heat-flow endpoint t→0⁺ の連続性**
(`heatFlowEntropyPower_continuousWithinAt_zero` が生入力の有限分散+有限エントロピー density-witness を要求、発見 3)。
方針 Y はこの endpoint 依存を **近似 + 極限** で迂回する:

1. **t > 0 (平滑側) で無前提 EPI**: heat-flow path 上 `t > 0` では入力が Gaussian と畳み込み済で
   自動的に regular (有限分散・滑らか・有限エントロピー)。よって EPI_t `N(X+√t Z_X + Y+√t Z_Y) ≥
   N(X+√t Z_X) + N(Y+√t Z_Y)` は **入力 regularity 無し**に既存 a.c. core で閉じる (要確認: 平滑後測度が
   density-witness を自動充足するか — 発見 3 は「生入力」と判定したが t>0 平滑後は別、Phase Y-0 で検算)。
2. **t→0⁺ 極限**: EPI_t の各項で `t→0` を取る。RHS は `N(X+√t Z) → N(X)` の収束、LHS は
   `liminf` を取る。不等式が極限で保たれるには **entropy power の下半連続性** (LHS)
   `N(X+Y) ≤ liminf N((X+Y)+√t Z)` と RHS の収束が要る。
3. **真の wall = entropy power 弱収束 半連続性**: `X_t → X` (weak / 法則収束) のとき
   `liminf N(X_t) ≥ N(X)` (or 適切な向き)。**Mathlib 完全不在** (entropy/KL の半連続性 loogle Found 0、
   epi-g2-main-closure-inventory)。これが方針 Y の新規 genuine Mathlib 壁。自作必要。
   - 関連在庫: KL の下半連続性 `MeasureTheory.??` / `lowerSemicontinuous` + portmanteau /
     Fatou 系 (EPIG2KLFatouLSC.lean に klFun-Fatou サンドイッチの genuine 実績あり — 流用候補)。
     **→ § Phase Y の先行調査 S5-inventory で確定 (起動済)**。

注: 退化トラップ除去 (特異 → entropy power 0) は方針 Y でも cases 2/3 の枠組みをそのまま使う。
方針 Y が追加するのは「a.c. だが有限分散でない入力」を平滑近似で救う層のみ。

## 進捗

- [ ] Phase 0 — feasibility gate: 新定義 shape 確定 + 無条件成立の数学的裏付け + Mathlib API 在庫指示 📋
- [ ] Phase 1 — 二層定義導入 + 既存 Real 資産の coercion bridge 📋 → [sub-plan: epi-entropypower-retype-plan]
- [ ] Phase 2 — downstream 36-file re-port (段階順序・依存) 📋 → [sub-plan: epi-downstream-report-plan]
- [ ] Phase 3 — a.c. EPI core 完成 (残 G3/richness/wiring) 📋 → 既存 plan 群流用
- [ ] Phase 4 — 特異・混合 case (soft 補題、conditioning-reduces-entropy) 📋 → [sub-plan: epi-singular-mixed-case-plan]
- [ ] Phase 5 — 無条件主定理 assembly + #print axioms sorryAx-free 検証 📋

proof-log: 各 Phase 完了時に別途 `docs/shannon/proof-log-epi-unconditional-phase-*.md` (Phase 0 のみ proof-log: no、調査のみ)。

---

## ゴール / Approach

**最終定理 (達成目標)**: 独立可測 `X Y : Ω → ℝ` に対し、新 `entropyPower : Measure ℝ → ℝ≥0∞` 下で

```
entropyPower (P.map (X+Y)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)
```

を **`h_stam` 無し・密度 regularity 無し**で証明する (`hX hY hXY` のみ)。

### Approach (解の全体形 — 3 つの柱)

#### 柱 1: 二層定義 (退化トラップ除去、解析中核を Real に温存)

退化トラップの除去は「特異測度を `0` でなく `-∞`(エントロピー) / `0`(エントロピーパワー) に
落とす」再型付けで達成する。ただし de Bruijn / Fisher / heat-flow / Stam の解析中核は **normed
field (ℝ) を要求** するため EReal/ℝ≥0∞ を載せられない (下記設計制約)。よって **二層構造**:

- **(a) Real 値 workhorse** — `differentialEntropy : Measure ℝ → ℝ` (現定義を**そのまま温存**、改名のみ検討)。a.c. 測度 / 密度の微分エントロピー。de Bruijn `HasDerivAt` / Stam / AWGN translation invariance が主役として使う。**触らない (= 既存 genuine 資産を保護)**。
- **(b) EReal / ℝ≥0∞ 上位レイヤ** — 任意測度に対する `differentialEntropyExt : Measure ℝ → EReal` (a.c. ブランチで (a) から coerce、特異ブランチで `⊥`) + `entropyPower : Measure ℝ → ℝ≥0∞` (a.c. ブランチで (a) から、特異で `0`)。**EPI 主定理の statement だけ (b)**。

**Mathlib-shape-driven** (先行調査 発見 1 で確定、2026-06-05):
- **`entropyPower μ := EReal.exp (2 * differentialEntropyExt μ)` の非分岐定義を採用** (第一候補)。
  `EReal.exp : EReal → ℝ≥0∞` 実在 (`Mathlib/Analysis/SpecialFunctions/Log/ERealExp.lean`)、
  `exp_bot : exp ⊥ = 0` (特異 → entropyPower 0 自動)、`exp_coe : exp ↑x = ENNReal.ofReal (Real.exp x)`
  (a.c. → Real workhorse と一致)、`exp_monotone` [gcongr] (EPI 不等式の lift に直結)。
  case-split は `differentialEntropyExt : EReal` 側のみ。
- `differentialEntropyExt μ := if μ ≪ volume then ↑(differentialEntropy μ) else (⊥ : EReal)`。
  a.c. 判定の definitional 化は `klDiv` precedent (`open Classical in` + `irreducible_def`) で GO。
- 退避 (L-Uncond-0-δ): `EReal.mul` の `2 * ⊥` 挙動が想定外なら ℝ≥0∞ 直接 case-split
  `if μ ≪ volume then ENNReal.ofReal (Real.exp (2 * differentialEntropy μ)) else 0` へ。

#### 柱 2: 3-case 分岐 (無条件成立の構造)

新 ℝ≥0∞ 定義下で EPI を case 分けで TRUE にする。`hXac := (P.map X) ≪ volume` 等で a.c./特異を判定:

1. **両方 a.c.** (密度あり): 既存 genuine 機械 (柱 3) を (a) 層で再配線。a.c. なら新 `entropyPower = ENNReal.ofReal (exp (2·h))` が Real workhorse の値と一致し、不等式は **既存 Real EPI を ℝ≥0∞ に coerce** すれば従う。**ここが hard core (= 既存 plan 群の残課題)**。
2. **片方のみ特異** (例 Y 特異、`N(Y)=0`): RHS = `N(X) + 0 = N(X)`。要するは `N(X+Y) ≥ N(X)`。これは full EPI より **soft**: `h(X+Y) ≥ h(X+Y | Y) = h(X | Y) = h(X)` (conditioning reduces entropy + 独立)。**既存 genuine 資産 2 本で組める** (柱 3 注記)。
3. **両方特異**: RHS = `0 + 0 = 0`。`N(X+Y) ≥ 0` は ℝ≥0∞ で **型自明** (`zero_le`)。

3-case を `Phase 4` (case 2/3) + `Phase 3` (case 1) + `Phase 5` (assembly) に割り振る。

#### 柱 3: a.c. 既存 genuine 資産の保存 + 再配線

既存 EPI bridge chain の genuine 部分は (a) Real 層の上で**不変**。`#print axioms` 実測済 genuine:
G1 log-ratio reframe / G2 heat-flow 端点連続 / scaling→bridge 組立 / richness lift B1 /
Gaussian saturation / L-EPI1 Stam / L-EPI2 de Bruijn。残 sorry (G3 rescale / assembly 22 sorry の
21 density-witness + 1 joint-indep / richness in-place B2 / W0/W1 wiring) は **case 1 (両 a.c.)
内部の前提**として残り、a.c. なので density-witness は充足可能。

**case 2 (混合) の鍵資産 (verbatim 確認済、既に genuine CLOSED)**:
- `condDifferentialEntropy_le` (`EPIG2ConvEntropyMonotone.lean:224`、genuine sorryAx-free): `h(X|Z) ≤ h(X)` (conditioning reduces entropy)。
- `condDifferentialEntropy_indep_add_eq` (`:328`、genuine `@audit:ok`): `X ⊥ Z` で `h(X + c·Z | Z) = h(X)` (独立和 fibre 同定)。

この 2 本の合成で混合 case の `h(X+Y) ≥ h(X)` の core が **既に in-tree に存在**。Phase 4 は
これを ℝ≥0∞ entropyPower の単調性 (`exp` 単調 → `ENNReal.ofReal` 単調) に持ち上げる plumbing。

### 設計制約 (Mathlib-shape-driven 必須、orchestrator 実測根拠)

- de Bruijn 恒等式は `HasDerivAt (fun t => differentialEntropy (P.map ...)) ((1/2)·fisherInfo) t` 形 (`FisherInfoV2DeBruijnAssembly.lean:3522`)。`HasDerivAt` は normed field を要求 → **EReal 不可**。
- AWGN 系 (`AWGNMIBridge.lean` 等) は translation invariance / Gaussian 値の等式・不等式で `differentialEntropy` を Real 算術の主役に使う。
- ⇒ **(a) を Real のまま温存**、(b) は a.c. 枝で (a) を coerce する薄いラッパに留める。これにより 36-file re-port の大半が「(a) を呼ぶ箇所はそのまま、(b) を要求する箇所だけ shim」に圧縮される。

---

## Sub-plan 一覧 (umbrella 配下、依存順)

本 plan を傘とし、実装は以下 sub-plan に分割する。slug は `@residual(plan:<slug>)` と一致させる。

| # | sub-plan slug | スコープ | 依存 | 状態 |
|---|---|---|---|---|
| S1 | `epi-entropypower-retype-plan` | 柱 1: (a)(b) 二層定義導入 (`differentialEntropyExt : Measure ℝ → EReal`、新 `entropyPower : Measure ℝ → ℝ≥0∞`) + (a)→(b) coercion bridge lemma 群。a.c./特異 判定述語。`EReal.toENNReal_bot` 整合。 | Phase 0 (在庫確定) | 📋 |
| S2 | `epi-downstream-report-plan` | 柱 1 cont.: 36-file の `differentialEntropy`/`entropyPower` 参照を (a)(b) いずれが必要か分類し re-port。statement-層 shim + import 順序の DAG。AWGN/Fisher/de Bruijn は (a) のまま不変であることを検証する re-port。 | S1 | 📋 |
| S3 | `epi-singular-mixed-case-plan` | 柱 2: case 2 (混合) + case 3 (両特異) の新規補題。`condDifferentialEntropy_le` + `condDifferentialEntropy_indep_add_eq` から ℝ≥0∞ `N(X+Y) ≥ N(X)` への lift。case 3 は `zero_le` 自明。3-case 判定 + dispatch。 | S1、S2 (statement 型) | 📋 |
| — | (case 1 a.c. core closure) | 柱 3: 既存 plan 群を**流用** (新規 sub-plan を作らない)。`epi-stam-to-conclusion-plan` / `epi-csiszar-ratio-reframe-plan` / `epi-richness-route-b-plan` / `epi-g2-*` が SoT。 | (進行中) | 既存 |
| S5 | `epi-uncond-truncation-lsc-plan` | **方針 Y クリティカルパス**: t>0 平滑側無前提 EPI + t→0⁺ 極限 + entropy power 弱収束 半連続性 (新規 Mathlib 壁、自作)。EPIG2KLFatouLSC の klFun-Fatou 実績流用候補。 | case1 (有限分散版 a.c. core) + S1 | 📋 先行調査中 |
| S4 | (assembly、本 plan Phase 5 で直接) | 柱 2+3 合流: 3-case dispatch → 無条件主定理。方針 Y では case1 を S5 経由の無前提版に差替。新 sub-plan 不要、本 plan §Phase 5。 | S1–S3 + S5 | 📋 |

**依存 DAG (方針 Y)**: `Phase 0 → S1 → S2 → {S3, case1(既存、有限分散版)} → S5(無前提化) → Phase 5(S4)`。
S5 が方針 Y の本体で、case1 の有限分散版 a.c. core を入力に「平滑側無前提 EPI + 半連続性極限」で
regularity を剥がす。S5 が semicontinuity wall で詰まれば L-Uncond-3-scope で方針 X (case1 をそのまま最終形) に縮退。

---

## Phase 0 — feasibility gate (新定義 shape 確定 + 数学的裏付け + Mathlib 在庫指示) 📋

proof-log: no (調査のみ。実装着手しない)。**この Phase が GO/NO-GO gate**。

### 0-A: 新定義 shape の確定 (要 inventory phase 委任項目を明示)

- [ ] `entropyPower : Measure ℝ → ℝ≥0∞` の定義形を確定。**設計分岐 (i) case-split 定義** を第一候補とする: a.c. case `ENNReal.ofReal (Real.exp (2 * differentialEntropy μ))`、特異 case `0`。判定述語は `μ ≪ volume` (Mathlib `Measure.AbsolutelyContinuous`)。**要在庫**: a.c./特異の **decidable でない** 判定をどう定義に組むか — `if μ ≪ volume then ... else 0` は `Decidable` instance を要する。代替: `differentialEntropyExt : Measure ℝ → EReal` を `(μ.rnDeriv volume の積分が finite かつ μ が a.c.) ? coe(h) : ⊥` 形で定義し、`entropyPower μ := (差分形).toENNReal`-経由で exp を**避ける**経路を再評価 (が、`exp` 不在ゆえ toENNReal だけでは entropyPower にならない)。**→ inventory に「a.c. 判定を definitional に組む Mathlib パターン (`Measure.rnDeriv` の `withDensity` 復元 `μ = volume.withDensity (rnDeriv) + singular`、`Measure.haveLebesgueDecomposition`)」を委任**。
- [ ] `differentialEntropyExt : Measure ℝ → EReal` の特異 case `⊥`、a.c. case `coe (differentialEntropy μ)` の coercion 形を確定。`EReal.coe_add` で和保存。
- [ ] **要在庫確認 (verbatim、予測禁止)**: `Real.exp` の ℝ≥0∞/EReal 持ち上げ不在 (loogle Found 0 を再確認)。`ENNReal.ofReal_exp` 系の有無。`EReal.toENNReal` の単調性 `EReal.toENNReal_le_toENNReal` (存在確認済)。`ENNReal.ofReal` の加法 `ENNReal.ofReal_add` (a.c.+a.c. の RHS 和を coerce で組むため)。

### 0-B: 無条件成立の数学的裏付け (3-case feasibility)

- [ ] **case 1 (両 a.c.)**: 既存 Real EPI `exp(2h(X+Y)) ≥ exp(2h(X))+exp(2h(Y))` が成立する前提下で、`ENNReal.ofReal` が和を保存する (`ENNReal.ofReal_add`、両 nonneg) ことを確認 → ℝ≥0∞ 不等式が従う。**裏付け OK の条件 = case1 で Real EPI が genuine に閉じること** (= 既存 plan 群の残課題、本 plan の責務外だが gate には記録)。
- [ ] **case 2 (混合)**: `condDifferentialEntropy_le` + `condDifferentialEntropy_indep_add_eq` の合成で `h(X+Y) ≥ h(X)` が出るか **verbatim signature で検算** (両者の前提 — measurability / `μ.map X ≪ volume` / KL 有限性系 integrability — が case 2 で充足可能か)。⚠ **要確認**: これらの前提は a.c. 側 X についての regularity であり、Y が特異でも X が a.c. なら満たせる見込み。ただし `condDifferentialEntropy_le` は多数の integrability precondition を持つ (`:229-245` verbatim) — これらが「特異 Y を条件付ける」設定で充足可能かを inventory で検算。**NO-GO 兆候**: X も特異な混合は case 2 でなく case 3 に落ちる (RHS の a.c. 項が消える) ので、case 2 は「X a.c. ∧ Y 特異」に限定して良いことを確認。
- [ ] **case 3 (両特異)**: RHS = 0、`N(X+Y) ≥ 0` は `zero_le` で自明。裏付け不要。

### 0-C: Mathlib / InformationTheory API 在庫指示 (inventory phase へ委任)

以下を `mathlib-inventory` サブエージェントに **structured per-lemma output** (file:line / 完全 signature / `[...]` 前提 verbatim / 結論形 verbatim) で委任する。**予測値は書かず、確認できないものは「要調査」マーク**:

1. **EReal/ℝ≥0∞ 算術**: `EReal.coe_add` / `EReal.toENNReal` 系 32 lemmas のうち単調性・⊥規約・`toENNReal_bot`、`ENNReal.ofReal_add` / `ENNReal.ofReal_le_ofReal`、`Real.exp` の ℝ≥0∞ 持ち上げ (不在確認)。
2. **a.c./特異 definitional 判定**: `Measure.haveLebesgueDecomposition` / `Measure.rnDeriv` / `Measure.singularPart` / `Measure.MutuallySingular`、a.c. を `Prop`/`Decidable` で定義に組むパターン。
3. **case 2 資産 verbatim**: `condDifferentialEntropy_le` (`:224`) + `condDifferentialEntropy_indep_add_eq` (`:328`) の全前提を verbatim 抽出 + 充足可能性。
4. **既存 entropyPower consumer 11 file の参照形** (どれが等式・不等式・Real 算術を要求するか) を grep ベースで列挙 (re-port 分類の素材、S2 の DAG 入力)。

### Phase 0 撤退ライン

- **L-Uncond-0-α** (NO-GO 条件): `entropyPower` の case-split 定義に `Decidable (μ ≪ volume)` が要り、かつ Mathlib に classical instance が無く `Classical.dec` で組むと downstream の `simp`/`rfl` が全滅する場合 → 定義を `differentialEntropyExt : EReal` 一本に寄せ、`entropyPower := (差分の toENNReal)` で `exp` を回避する代替設計を再評価。最悪、本 moonshot を「EReal 微分エントロピー版 EPI (entropyPower 版は corollary)」に縮退。
- **L-Uncond-0-β** (case 2 NO-GO): `condDifferentialEntropy_le` の integrability 前提が「特異 Y を条件付ける」設定で充足不能 (= 混合 case の core が組めない) と判明 → 混合 case を **honest precondition 付き partial** (`entropy_power_inequality_mixed_under_X_regular` 等) に留め、無条件性を「両 a.c. ∨ 両特異」に縮小。docstring に「NOT fully unconditional」明示。
- **L-Uncond-0-γ** (退化定義悪用の自己監査): 新定義が特異測度で `⊥`/`0` を返す設計は、case 3 で RHS=0 を突いた **vacuous 達成** に見えうる。これは退化 case の正しい値 (特異測度のエントロピーパワーは真に 0) なので OK だが、**LHS が常に 0 になるような定義ミス** (例: a.c. 判定が常に false に転ぶ) を Phase 1 着地時に `gaussianReal` で非自明値確認する (Gaussian は a.c. で `entropyPower (gaussianReal m v) = 2πe v ≠ 0`)。退化定義悪用 (CLAUDE.md tells) の自己 gate。

---

## Phase 1 — 二層定義導入 + 既存 Real 資産の coercion bridge 📋 → `epi-entropypower-retype-plan`

proof-log: yes (sub-plan 側)。

- [ ] (a) `differentialEntropy : Measure ℝ → ℝ` を温存 (改名するなら全 consumer 同期、しないのが第一候補)。
- [ ] (b) `differentialEntropyExt : Measure ℝ → EReal` + `entropyPower : Measure ℝ → ℝ≥0∞` を新規導入 (Phase 0 で確定した shape)。**`def` の RHS が詰まったら** CLAUDE.md「sorry を書けない箇所」第一選択 = 結論形に合わせた定義書換、第二選択 = `@audit:defect` マーク (本 plan を `@audit:closed-by-successor`)。`Prop := True`/退化定義悪用は禁止。
- [ ] coercion bridge: `entropyPower_eq_ofReal_of_ac : μ ≪ volume → entropyPower μ = ENNReal.ofReal (Real.exp (2 * differentialEntropy μ))`、`entropyPower_singular : ¬(μ ≪ volume) → entropyPower μ = 0` (or Lebesgue 分解の特異部判定形)。
- [ ] **非自明値 sanity** (L-Uncond-0-γ gate): `entropyPower (gaussianReal m v) = 2πe v` (a.c. 枝)、`entropyPower (dirac m) = 0` (特異枝)。Dirac が **新定義で 0 になる**ことを確認 (旧 1 → 新 0 の退化トラップ除去を verbatim 検証)。

### Phase 1 撤退ライン

- **L-Uncond-1-α**: coercion bridge で `ENNReal.ofReal` と `EReal.toENNReal` の経路が二重定義になり整合 lemma が hell 化 → 一方の経路に統一 (定義は 1 つ、もう一方は導出 lemma)。
- **L-Uncond-1-β**: 旧 `entropyPower` (Real) を消すと EPI 系 11 file が一斉に壊れる → 旧 Real `entropyPower` を `entropyPowerReal` に退避して残し、新 ℝ≥0∞ 版を `entropyPower` とする (S2 で consumer を順次移行)。

---

## Phase 2 — downstream 36-file re-port (段階順序・依存) 📋 → `epi-downstream-report-plan`

proof-log: yes (sub-plan 側)。

re-port は **(a) を呼ぶ箇所は不変、(b) を要求する箇所だけ shim** 原則。順序は import DAG の葉から根へ:

- [ ] **層 0 (不変確認)**: Fisher / de Bruijn / AWGN 系 (`FisherInfoV2DeBruijnAssembly` / `AWGNMIBridge` / `ParallelGaussianConverse` 等、計 ~25 file) は (a) `differentialEntropy : ℝ` を使う。**変更不要**を `lake env lean` で確認するだけ (改名しない限り no-op)。
- [ ] **層 1 (entropyPower consumer 11 file)**: EPI 系のみ。新 ℝ≥0∞ `entropyPower` への移行。等式形は coercion lemma で書換、不等式形は ℝ≥0∞ 不等式に。Gaussian saturation `entropyPower_gaussian_additivity` (`:331`) は a.c. なので bridge 経由。
- [ ] **層 2 (主定理 + corollary)**: `EntropyPowerInequality.lean` の statement を新型に。corollary (scaling / log-form / multi-arg) を新型 reshape。
- [ ] import 順序 DAG を sub-plan 冒頭に表で固定 (循環回避)。**verbatim 確認**: 改名する場合の olean refresh 順 (CLAUDE.md「upstream edits 後 olean refresh」)。

### Phase 2 撤退ライン

- **L-Uncond-2-α**: AWGN/Fisher 系が実は (b) 上位型を要求している箇所が見つかる (Real 不変の前提が崩れる) → 当該箇所だけ (a)→(b) coercion を挿入。広範なら S2 のスコープを再見積り。
- **L-Uncond-2-β**: 36-file re-port が 1 session で終わらない → file 群を family batch に分割し type-check done 単位で commit (各 batch `lake env lean` clean)。

---

## Phase 3 — a.c. EPI core 完成 (case 1) 📋 → 既存 plan 群流用

proof-log: 既存 plan 側 (新規起こさない)。

case 1 (両 a.c.) の hard core は **既存の bridge chain closure**。本 plan では新規 sorry を作らず、
既存 plan の残課題を消費する形で参照する:

- 残 G3 rescale (`csiszarGap_antitoneOn_Icc_zero_one`, `EPIStamToBridge.lean`) → `epi-stam-to-conclusion-plan` §Phase A-close G3。
- assembly `isStamToEPIScalingHyp_of_stam_debruijn` の 22 sorry (21 density-witness + 1 joint-indep) → **a.c. case 内部の前提として正当化**。a.c. なので density-witness は充足可能 (= 入力分布の Real 密度 regularity を a.c. case 仮定から供給)。本 plan の Approach 柱 3 がこの「density-witness を a.c. case 仮定として正当化する」流れを設計。
- richness in-place B2 → `epi-richness-route-b-plan` (G2 待ち保留中)。
- G1 ratio reframe / G2 端点連続性 → 既に genuine CLOSED (verbatim 確認済)。

**本 plan Phase 3 の唯一の新規作業**: a.c. case の `entropyPower` (新 ℝ≥0∞) が、既存 Real EPI
`entropy_power_inequality` (旧、Real 版) を coerce して得られることを示す bridge lemma
`entropy_power_inequality_ac : (P.map X ≪ volume) → (P.map Y ≪ volume) → (h_stam) → 新型 EPI`。
**注意**: ここで `h_stam` は **a.c. case 内部前提**として残ってよい (a.c. なので density から供給可能、無条件化の対象は最終 statement であり、case 1 内部での density 前提は柱 3 の設計上 honest)。最終的に case 1 の `h_stam` も既存 plan 群が closure すれば完全 sorryAx-free。

### Phase 3 撤退ライン

- **L-Uncond-3-α**: 既存 plan 群の case1 core が未完 (G3/B2 残 sorry) のまま → case1 を `@residual(plan:epi-stam-to-conclusion-plan)` で transitive park。本 plan の **無条件性は「3-case dispatch が genuine」で達成**し、case1 内部 sorry は既存 plan に委譲 (compound `@residual` で両方指す)。これは honest (sorry は被呼出 wall が保持、dispatch 自体は genuine)。

---

## Phase 4 — 特異・混合 case (soft 補題) 📋 → `epi-singular-mixed-case-plan`

proof-log: yes (sub-plan 側)。

- [ ] **case 3 (両特異)**: `entropyPower (P.map (X+Y)) ≥ 0` を `zero_le` で。RHS = `0 + 0 = 0` を特異判定から。**最も soft**、新規 ~20-40 行。
- [ ] **case 2 (X a.c. ∧ Y 特異)**: RHS = `N(X) + 0 = N(X)`。要 `N(X+Y) ≥ N(X)`。鍵: `condDifferentialEntropy_le` + `condDifferentialEntropy_indep_add_eq` (両 genuine、verbatim 確認済) の合成で `h(X+Y) ≥ h(X+Y | Y) = h(X)`、`exp` 単調 + `ENNReal.ofReal` 単調で `N(X+Y) ≥ N(X)`。**前提充足**: `condDifferentialEntropy_le` の integrability 群を「X a.c.、Y 特異」設定で供給 (Phase 0-B で feasibility 確認済が前提)。
- [ ] **case 対称性**: case 2 の X↔Y 対称版 (Y a.c. ∧ X 特異)。
- [ ] **3-case 判定 + dispatch** スケルトン (Phase 5 で本体 assembly)。`P.map X ≪ volume` 等の Lebesgue 分解判定。

### Phase 4 撤退ライン

- **L-Uncond-4-α** (case 2 前提不足): `condDifferentialEntropy_le` の integrability 前提が混合設定で組めない → case 2 を honest precondition 付き (`..._of_X_integrable`) に留め `sorry` + `@residual(plan:epi-singular-mixed-case-plan)`、無条件性は「両 a.c. ∨ case3」に縮小 (L-Uncond-0-β と整合)。
- **L-Uncond-4-β** (`X+Y` の a.c./特異判定): X a.c. ∧ Y 特異のとき `X+Y` が a.c. になる (convolution は a.c. を保つ) ことの Mathlib lemma が要る → 在庫不在なら `condDifferentialEntropy` 経由で a.c. 判定を迂回 (entropy 直接比較、`entropyPower` の a.c. 枝に依らない形)。**禁止**: 退化定義悪用 (特異判定を常に true に倒して case3 に流し vacuous 達成) — L-Uncond-0-γ gate で検出。

---

## Phase 5 — 無条件主定理 assembly + #print axioms 検証 📋

proof-log: yes。

- [ ] 3-case dispatch を `entropy_power_inequality_unconditional` (新名) に組む: `P.map X ≪ volume` / `P.map Y ≪ volume` の 4 通り (両 a.c. / X のみ / Y のみ / 両特異) を `by_cases` 分岐し、各々 Phase 3 (case1) / Phase 4 (case2 両向き / case3) を呼ぶ。
- [ ] 主定理 signature: `(hX hY : Measurable) (hXY : IndepFun X Y P)` **のみ** (h_stam 除去)。conclusion は新 ℝ≥0∞ EPI。
- [ ] **`#print axioms entropy_power_inequality_unconditional`** で sorryAx 依存を実測。case1 が既存 plan に transitive park 中なら sorryAx 残存は honest (compound `@residual(plan:epi-stam-to-conclusion-plan,...)` で明示)。case2/3 + dispatch が genuine なら、無条件性の **構造**は sorryAx-free に達成、残は case1 内部のみ。
- [ ] 旧条件付き `entropy_power_inequality` (`:289`、Real 版 + h_stam) は **取り消し線化せず corollary として残す** (a.c. 特殊形)。または無条件版から導出。
- [ ] **独立 honesty-auditor 起動** (新規 sorry + `@residual` を導入した場合、CLAUDE.md 必須)。dispatch の honesty (退化定義悪用していないか、case3 の vacuous 達成でないか、case2 の前提が load-bearing でなく regularity か) を独立検証。

### Phase 5 撤退ライン

- **L-Uncond-5-α**: dispatch の `by_cases (P.map X ≪ volume)` が `Decidable` を要し classical で組むと axioms に `Classical.choice` が増える → これは propext/Quot.sound と同列で許容範囲 (sorryAx ではない)、honest。問題なし。
- **L-Uncond-5-β**: 無条件主定理が case1 の残 sorry を transitive 消費し続ける場合 → **部分達成として honest 命名**で commit (`entropy_power_inequality_unconditional` の docstring に「case1 (両 a.c.) は `epi-stam-to-conclusion-plan` の closure 待ち、混合/特異 case は genuine」明示)。moonshot の「無条件構造」は達成、「完全 sorryAx-free」は case1 closure 後。

---

## 撤退ライン共通規律

全 Phase 共通禁止 (CLAUDE.md 検証の誠実性): `Prop := True` placeholder / 結論型≡仮説型 `:= h`
循環 / load-bearing `*Hypothesis` predicate に核を bundle / **退化定義悪用** (特に本 plan は新定義
が特異 case で `0`/`⊥` を返すため、case3 の vacuous 達成や a.c. 判定の常時 false 倒しが
退化定義悪用に該当しうる — L-Uncond-0-γ gate で常時自己監査)。撤退時 docstring に「NOT a
discharge / load-bearing on <...>」明示。新規 `sorry` + `@residual` 導入時は独立 honesty-auditor 起動。

**honest 撤退口**: 詰まったら `sorry` + `@residual(plan:<該当 sub-plan slug>)` (def RHS が詰まったら
CLAUDE.md「sorry を書けない箇所」第一選択 = 定義書換、第二選択 = `@audit:defect` + `@audit:closed-by-successor(epi-unconditional-moonshot-plan)`)。

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-06-05 起草 (Approach 1 採用、二層構造確定)**: project owner が「既存 def を作り直す
   (Approach 1)」を選択。orchestrator 実測の致命的事実 (`differentialEntropy_dirac = 0` →
   現定義で無条件 EPI literally FALSE) + 設計制約 (de Bruijn `HasDerivAt` が normed field 要求で
   EReal 不可) から **二層構造** (a) Real workhorse 温存 + (b) EReal/ℝ≥0∞ statement 層 を確定。
   3-case 分岐 (両 a.c. / 混合 / 両特異) を Phase 骨格に。
   - **verbatim 確認済 (予測でなく実コード)**: `differentialEntropy_dirac = 0`
     (`DifferentialEntropy.lean:155`)、`entropyPower := Real.exp (2 * differentialEntropy)`
     (`EntropyPowerInequality.lean:102`)、`entropyPower_pos` (`:109`)、主定理 +
     `IsStamInequalityResidual` shape (`:211/:289`)、case2 鍵資産 `condDifferentialEntropy_le`
     (`EPIG2ConvEntropyMonotone.lean:224`、genuine) + `condDifferentialEntropy_indep_add_eq`
     (`:328`、genuine `@audit:ok`)。
   - **loogle 在庫 (verbatim)**: `EReal.toENNReal` 系 32 lemmas + `EReal.toENNReal_bot` (⊥→0、
     特異→entropyPower=0 ルート) 存在。`EReal.coe_add` 存在。⚠ **`Real.exp` の EReal/ℝ≥0∞ 版は
     不在** (loogle `Real.exp, EReal` = Found 0、`ENNReal.exp` = unknown) → entropyPower を
     ℝ≥0∞ で素朴 exp 定義できない、case-split 定義 (a.c. 枝で Real exp + `ENNReal.ofReal`) を
     第一候補に。`negMulLog` EReal 版も不在。
   - **要在庫調査マーク (Phase 0-C で inventory 委任、予測値を書かない)**: a.c./特異の
     definitional 判定パターン (`Measure.haveLebesgueDecomposition` / `Decidable (μ ≪ volume)`)、
     `ENNReal.ofReal_add` / 単調性、`X a.c. ∧ Y 特異 ⇒ X+Y a.c.` (convolution 保存) の Mathlib
     lemma 有無、`condDifferentialEntropy_le` の integrability 前提が混合設定で充足可能か。
   - **既存 plan 統合方針**: case1 (a.c. core) は新 sub-plan を作らず既存
     `epi-stam-to-conclusion-plan` / `epi-csiszar-ratio-reframe-plan` (G1 CLOSED) /
     `epi-richness-route-b-plan` (B1 done) / `epi-g2-general-sandwich-moonshot-plan` (G2 CLOSED) を
     流用。新規 sub-plan は S1 retype / S2 downstream re-port / S3 singular-mixed の 3 本。
